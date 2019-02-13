/*
  Name: Yubaraj Bhatta
  ID: 1001544124
*/

#define _GNU_SOURCE

#include <errno.h>
#include <libgen.h>
#include <signal.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
//#include <sys/wait.h>
#include <termios.h>
#include <unistd.h>

#include <assert.h>
#include <ctype.h>
#include <stdbool.h>

// If ENABLE_LOGGING is non-zero and non-empty,
// a lot of logging staff comes into stderr,
// so it is not expected to be turned on when an ordinary msh user runs it.
#define ENABLE_LOGGING 0

// Main exit point from the program which should free all resources allocated with malloc.
static void free_and_exit( int retcode );

// There are three types of process msh spawns:
// - the shell itself (PROCESS_TYPE_SHELL);
// - liner, which takes care of running the whole line of input and
// it spawns workers, which should execute one concrete command.
// - worker, which executes an atomic command (which doesn't have any semicolons) with exec
// or executes it itself, if it is special (history, listpids, etc.)
typedef enum process_type_t
{
  PROCESS_TYPE_NONE = 0,
  PROCESS_TYPE_SHELL,
  PROCESS_TYPE_LINER,
  PROCESS_TYPE_WORKER
} process_type_t;

static process_type_t my_process_type = PROCESS_TYPE_NONE;

// Some reporting to console macros. If logging is enabled, LOG lets us see,
// what staff is going on inside msh execution.
#define ERROR( ... )                \
  {                                 \
    fprintf( stderr, __VA_ARGS__ ); \
    fprintf( stderr, "\n" );        \
    fflush( stderr );               \
  }

#if ENABLE_LOGGING

// Auxiliary function used in logging, mostly to identify our current process.
static const char * get_my_process_name()
{
  const char * process_name = NULL;
  switch ( my_process_type )
  {
    case PROCESS_TYPE_SHELL:
      process_name = "Shell:\t";
      break;
    case PROCESS_TYPE_LINER:
      process_name = "Liner:\t";
      break;
    case PROCESS_TYPE_WORKER:
      process_name = "Worker:\t";
      break;
    case PROCESS_TYPE_NONE:
      process_name = "None:\t";
      break;
  }
  return process_name;
}

#define LOG( ... )                                  \
  {                                                 \
    fprintf( stderr, "%s", get_my_process_name() ); \
    ERROR( __VA_ARGS__ );                           \
  }

#else
#define LOG( ... ) ;
#endif

// Prompt that is print, while we are running msh in interactive mode.
#define PROMPT "msh> "
static void print_prompt()
{
  printf( PROMPT );
  fflush( stdout );
}

// The maximum command-line size we support (taken from sample repository).
#define MAX_COMMAND_SIZE 255

// Mav shell only supports up to 10 command line parameters
// plus the command name is also a token, for simplicity.
#define MAX_NUM_ARGUMENTS 11

// Suffix we will to PATH environmental variable,
// to specify where to search for executable file
#define SEARCH_PATH_SUFFIX ":/usr/local/bin:/usr/bin:/bin"

// Structures for preserving current command lines history.
#define MAX_COMMANDS_HISTORY_SIZE 50
// It is a circular buffer, so command_history_finish index will point at
// the first free spot, or the spot which is next to be rewritten.
static char command_history[MAX_COMMANDS_HISTORY_SIZE][MAX_COMMAND_SIZE];
static size_t command_history_finish = 0;

// The same principle of circular buffer is applied here, as in command_history.
// Structures for saving pid of processes spawned with fork().
#define MAX_PIDS_HISTORY_SIZE 15
static pid_t pids_history[MAX_PIDS_HISTORY_SIZE];
static size_t pids_history_finish = 0;

static void add_pid_to_history( pid_t pid )
{
  assert( my_process_type == PROCESS_TYPE_SHELL );
  if ( pid < 0 )
  {
    LOG( "pid is invalid" );
  }

  // Saving our (liner's pid) into pids history.
  pids_history[pids_history_finish] = pid;
  LOG( "add_pid_to_history: pids_history_finish %lu, pid %d", pids_history_finish, pid );

  // Make pid_history_finish point at the next free element of pids_history or the earliest one.
  pids_history_finish = ( pids_history_finish + 1 ) % MAX_PIDS_HISTORY_SIZE;
}

// Special codes for a worker to exit.
// It worth noting that when any command from execvp returns with the same code,
// our worker returns with EXIT_FAILURE (=1),
// which should not be equal to the special codes below.
typedef enum worker_exit_code_t
{
  MSH_EXIT_ALL = 4,
  MSH_EXIT_BG = 5
} worker_exit_code_t;

// This flag will be set, if worker's job is finished - so that in the main flow
// (not signal handling) the liner will now if he still need to pause().
static bool last_worker_exited = true;

// The same flag for being sure we have to put shell into sleep.
static bool last_liner_exited = true;

// Some kind of limitation, but no idea how to surpass it in an easy way.
// In a nutshell, we have to share C-string of the current working directory
// between different processes of msh. We are doing it through file sharing.
#define MAX_CWD_SIZE 255

static pid_t msh_pgid = -1;

#define CWD_STORAGE_FILENAME_SIZE 30
static char cwd_storage_filename[CWD_STORAGE_FILENAME_SIZE] = "/tmp/msh_cwd_";

// Set new current working directory.
static void set_cwd( char * new_cwd )
{
  FILE * f = fopen( cwd_storage_filename, "w" );
  fprintf( f, "%s", new_cwd );
  fclose( f );
}

// Will try to change current working directory to new_dir,
// returning 0 on success, -1 on failure.
static int try_change_directory( char * new_dir )
{
  LOG( "Changing directory to %s", new_dir );
  int exit_code = chdir( new_dir );
  if ( exit_code != 0 )
  {
    ERROR( "cd: Error occured\n" );
    return -1;
  }

  char * cwd = get_current_dir_name();
  set_cwd( cwd );
  free( cwd );
  return 0;
}

// Update this process' current working directory,
// taken from file cwd_storage_filename.
static void update_cwd()
{
  FILE * f = fopen( cwd_storage_filename, "r" );
  char * cwd = (char *)malloc( MAX_CWD_SIZE );
  memset( cwd, 0, MAX_CWD_SIZE );
  int fscanf_result = fscanf( f, "%s", cwd );
  if ( fscanf_result <= 0 )
  {
    ERROR( "Bad format for current working directory" );
    if ( my_process_type != PROCESS_TYPE_SHELL )
    {
      free_and_exit( EXIT_FAILURE );
    }
  }
  fclose( f );

  int chdir_ret_code = chdir( cwd );
  if ( chdir_ret_code == -1 )
  {
    ERROR( "Error with chdir" );
    if ( my_process_type != PROCESS_TYPE_SHELL )
    {
      free_and_exit( EXIT_FAILURE );
    }
  }
  free( cwd );
}

// Another kind of dirty hack decision to use files for sharing info between
// liner and shell. With sockets the code would become much-much more complicated
// (and it is over 1k LOC already!)
#define PID_STORAGE_FILENAME_SIZE 40
static char pid_storage_suffix[PID_STORAGE_FILENAME_SIZE] = "/tmp/msh_pid_";

// Shared between liner and shell - C-string with command line tokens and semicolons,
// with a space character as a delimiter.
static char * cmd_line;

// Maximum number of tokens is MAX_NUM_ARGUMENTS,
// +1 for a NULL string for passing properly into exec().

// Should initialize by zero as they are in static memory.
static char * tokens[MAX_NUM_ARGUMENTS + 1];

// Free current set of tokens for current process.
static void free_tokens()
{
  char ** token;
  for ( token = tokens; *token; token++ )
  {
    free( *token );
    *token = NULL;
  }
}

// Free resources used in current command line input iteration.
// We only need to take of variables created with malloc().
static void free_current_input_resources()
{
  free_tokens();
  free( cmd_line );
  cmd_line = NULL;
}

// This enum tells us in which state worker process
// (the one that runs a single command) is in.
// There also could be some WORKER_STATE_FINISHED,
// but we are removing worker info as soon as it finishes,
// So, WORKER_STATE_FINISHED would not be used anywhere.
typedef enum worker_state_t
{
  WORKER_STATE_ACTIVE,
  WORKER_STATE_SUSPENDED,
  WORKER_STATE_BACKGROUND
} worker_state_t;

// We are saving our current liner child's pid to be able to resume it,
// when msh user asks for putting this liner's command into the background.
static pid_t liner_child_pid = -1;
typedef struct liner_job_t
{
  pid_t pid;
  pid_t pgid;
  worker_state_t state;
} liner_job_t;

typedef struct liner_list_item_t
{
  // next_liner_list_item points at the liner,
  // which was added before current liner_list.
  struct liner_list_item_t * next_liner_list_item;

  // Stored liner job's info.
  liner_job_t * liner_job;
} liner_list_item_t;

// Pointer to the first liner in the list to be traversed.
// By design, it is the last liner added.
static liner_list_item_t * liner;

// Create new liner job and put it into our liners list.
static liner_job_t * add_liner_list_item( pid_t liner_pid )
{
  LOG( "Adding new_liner_list_item, pid %d", liner_pid );
  assert( my_process_type == PROCESS_TYPE_SHELL );

  liner_job_t * new_liner_job = (liner_job_t *)malloc( sizeof( liner_job_t ) );
  new_liner_job->pid = liner_pid;
  new_liner_job->pgid = getpgrp();
  new_liner_job->state = WORKER_STATE_ACTIVE;

  liner_list_item_t * new_liner_list_item =
      (liner_list_item_t *)malloc( sizeof( liner_list_item_t ) );
  new_liner_list_item->next_liner_list_item = liner;
  new_liner_list_item->liner_job = new_liner_job;
  liner = new_liner_list_item;

  return new_liner_job;
}

// Remove a liner info from list when its process finished.
static void remove_liner_list_item( pid_t liner_pid )
{
  LOG( "Removing liner with pid %d", liner_pid );
  liner_list_item_t * current_item = liner;

  // previous_item preserves the liner_list_item which points at our
  // liner_list_item to be deleted. We have to update next element links,
  // when removing an item from a list.
  liner_list_item_t * previous_item = NULL;

  // Traversing the list, trying to find item with liner_job->pid = liner_pid.
  while ( current_item != NULL )
  {
    liner_job_t * liner_job = current_item->liner_job;
    if ( liner_job->pid == liner_pid )
    {
      if ( previous_item != NULL )
      {
        previous_item->next_liner_list_item = current_item->next_liner_list_item;
      }
      else
      {
        assert( current_item == liner );
        liner = current_item->next_liner_list_item;
      }

      free( liner_job );
      free( current_item );

      return;
    }

    previous_item = current_item;
    current_item = current_item->next_liner_list_item;
  }

  ERROR( "Not found liner with pid %d", liner_pid );
}

// Free the whole list of liners info structures.
// To be called on msh's exit.
static void free_liner_list()
{
  liner_list_item_t * current_item = liner;
  // Traversing the list, trying to find item with liner_job->pid = liner_pid.
  // No need in previous_item here, as we are not modifying the list.

  while ( current_item != NULL )
  {
    liner_list_item_t * next_item = current_item->next_liner_list_item;
    liner_job_t * liner_job = current_item->liner_job;

    // When the item found, send some stopping signal to him
    // and free resources associated with it.
    if ( my_process_type == PROCESS_TYPE_SHELL )
    {
      // Kill our liners - suspended and the ones put to the background.
      kill( liner_job->pid, SIGKILL );
    }

    free( liner_job );
    free( current_item );
    current_item = next_item;
  }

  liner = NULL;
}

// Find an item in liners list and return the liner job stored inside, or NULL on failure.
static liner_job_t * get_liner_job_with_pid( pid_t liner_pid )
{
  liner_list_item_t * current_item = liner;
  while ( current_item != NULL )
  {
    liner_job_t * liner_job = current_item->liner_job;
    if ( liner_job->pid == liner_pid )
    {
      return liner_job;
    }
    current_item = current_item->next_liner_list_item;
  }
  LOG( "Not found liner with pid %d", liner_pid );
  return NULL;
}

static liner_job_t * get_liner_job_with_state( worker_state_t state )
{
  liner_list_item_t * current_item = liner;
  while ( current_item != NULL )
  {
    liner_job_t * liner_job = current_item->liner_job;
    if ( liner_job->state == state )
    {
      return liner_job;
    }
    current_item = current_item->next_liner_list_item;
  }
  LOG( "Not found liner with state %d", (int)state );
  return NULL;
}

// Frees all resources that could be allocated anywhere by malloc and not freed for sure.
static void free_all_resources()
{
  free_liner_list();
  free_current_input_resources();
}

static void free_and_exit( int retcode )
{
  LOG( "Exiting with code: %d\n", retcode );
  free_all_resources();
  exit( retcode );
}

// Returns filename, where the liner with pid=liner_pid saves the list of the pids
// of the workers spawned with fork().
// returned string should be freed after usage with free().
static char * get_pid_storage_filename( pid_t liner_pid )
{
  char * pid_storage_filename = (char *)malloc( PID_STORAGE_FILENAME_SIZE );
  memset( pid_storage_filename, 0, PID_STORAGE_FILENAME_SIZE );
  snprintf( pid_storage_filename,
            PID_STORAGE_FILENAME_SIZE,
            "%s_%d",
            pid_storage_suffix,
            liner_pid );
  return pid_storage_filename;
}

// Save currently spawned worker's pid.
static void save_worker_pid_with_liner( pid_t child_pid )
{
  assert( my_process_type == PROCESS_TYPE_LINER );
  char * pid_storage_filename = get_pid_storage_filename( getpid() );

  LOG( "Saving pid of worker: %d to %s", child_pid, pid_storage_filename );
  FILE * f = fopen( pid_storage_filename, "a" );
  if ( f == NULL )
  {
    LOG( "Failed to open pid_storage_filename \"%s\" for writing", pid_storage_filename )
  }
  else
  {
    fprintf( f, "%d\n", child_pid );
    fclose( f );
  }
  free( pid_storage_filename );
}

static void save_liner_pids_with_shell( pid_t liner_pid )
{
  assert( my_process_type == PROCESS_TYPE_SHELL );
  char * pid_storage_filename = get_pid_storage_filename( liner_pid );

  LOG( "opening file with pids of liner %d and pid_storage_filename = %s",
       liner_pid,
       pid_storage_filename );
  FILE * f = fopen( pid_storage_filename, "r" );
  if ( f == NULL )
  {
    // Maybe there is no workers spawned.
    // There are some commands running without a need of workers.
    LOG( "Failed to open pid_storage_filename \"%s\" for reading", pid_storage_filename )
  }
  else
  {
    pid_t worker_pid = 0;
    while ( f != NULL && fscanf( f, "%d\n", &worker_pid ) != EOF )
    {
      LOG( "In the past liner %d spawned a worker with pid %d ", liner_pid, worker_pid );
      if ( worker_pid != 0 && worker_pid != 0 )
      {
        add_pid_to_history( worker_pid );
      }
    }
    fclose( f );
  }
  free( pid_storage_filename );
}

// All the operations we need to do in the shell,
// when the liner with pid=liner_pid is closing.
static void take_leave_of_liner( pid_t liner_pid )
{
  assert( my_process_type == PROCESS_TYPE_SHELL );

  if ( liner && liner->liner_job->pid == liner_pid )
  {
    last_liner_exited = true;
  }

  // Saving workers' pids which were spawned by the liner.
  save_liner_pids_with_shell( liner_pid );

  // Removing liner from liners list in order to keep memory usage low.
  remove_liner_list_item( liner_pid );
}

typedef void ( *sighandler_t )( int );

// Invariant here: at any moment we can only have one active child.
static void sigchld_handler( int signal_num )
{
  LOG( "handling SIGCHLD in Shell" );
  assert( signal_num == SIGCHLD );
  assert( my_process_type == PROCESS_TYPE_SHELL );

  int child_status;
  pid_t child_pid = waitpid( -1, &child_status, WUNTRACED | WCONTINUED );
  LOG( "child_status: %d, child_pid: %d", child_status, child_pid );
  update_cwd();
  if ( child_pid == -1 )
  {
    ERROR( "Some error when changing liner state %d, Resuming...", errno );
    return;
  }

  liner_job_t * liner_job = get_liner_job_with_pid( child_pid );
  if ( liner_job == NULL )
  {
    // It can happen if the liner fired a signal or ended
    // before we added a liner job for it.
    LOG( "Unstable state: liner with pid %d not found...", child_pid );
    liner_job = add_liner_list_item( child_pid );
  }

  if ( WIFCONTINUED( child_status ) )
  {
    LOG( "Child %d continued", child_pid );
    // Someone just continued our child through sending signal manually,
    // assuming it's us. In the assignment there is not
    // `put back to the foreground option, so we
    // should put our child into background right away.

    if ( liner_job->state != WORKER_STATE_SUSPENDED )
    {
      LOG( "Bad apriori status (%d) for child %d", (int)liner_job->state, child_pid );
    }
    liner_job->state = WORKER_STATE_BACKGROUND;
  }
  else if ( WIFEXITED( child_status ) )
  {
    // Child exited and we can react on that.
    int child_exit_code = WEXITSTATUS( child_status );
    LOG( "Child returned with exit code: %d", child_exit_code );

    take_leave_of_liner( child_pid );

    if ( child_exit_code == MSH_EXIT_ALL )
    {
      free_and_exit( EXIT_SUCCESS );
    }
    else if ( child_exit_code == MSH_EXIT_BG )
    {
      // Find first suspended job and put it to the background.
      liner_job_t * liner_job = get_liner_job_with_state( WORKER_STATE_SUSPENDED );
      if ( liner_job )
      {
        LOG( "Continuing job with pid %d", liner_job->pid );
        kill( liner_job->pid, SIGCONT );
      }
      else
      {
        ERROR( "Did not found any job to continue" );
      }
    }
    else if ( child_exit_code == EXIT_SUCCESS )
    {
      LOG( "Doing nothing, returning to the main loop after sleep() call" );
    }
    else
    {
      LOG( "Unexpected exit code from liner: %d", child_exit_code );
    }
  }
  else if ( WIFSIGNALED( child_status ) || WIFSTOPPED( child_status ) )
  {
    int child_signal =
        WIFSIGNALED( child_status ) ? WTERMSIG( child_status ) : WSTOPSIG( child_status );
    switch ( child_signal )
    {
      case SIGCONT:
        if ( liner_job->state != WORKER_STATE_SUSPENDED )
        {
          LOG( "Bad apriori status (%d) for child %d", (int)liner_job->state, child_pid );
        }
        liner_job->state = WORKER_STATE_BACKGROUND;
        break;
      case SIGTSTP:
        if ( liner_job->state != WORKER_STATE_ACTIVE )
        {
          LOG( "Bad apriori status (%d) for child %d", (int)liner_job->state, child_pid );
        }
        liner_job->state = WORKER_STATE_SUSPENDED;
        break;
      case SIGKILL:
      case SIGINT:
        // Removing the child from our liners list,
        // as it wont signal us anymore.
        take_leave_of_liner( child_pid );

        break;
      default:
        // We don't know how to react to that signal sent to liner,
        // let's just kill it.
        ERROR( "Unexpected signal %d to child, killing it... %d", child_signal, child_pid );
        kill( child_pid, SIGKILL );
        take_leave_of_liner( child_pid );
        break;
    }
  }
  else
  {
    LOG( "Unexpected liner's state change, resuming..." );
  }

  // Returning shell to the foreground - helps very well, if we run msh inside msh.
  tcsetpgrp( STDIN_FILENO, msh_pgid );
}

// Liner should react on signals coming from his worker.
// Unfortunately, there is a lot of code duplication,
// but that is for clarity and simplicity.
static void sigchld_handler_for_liner( int signal_num )
{
  LOG( "handling SIGCHLD in Liner" );
  assert( signal_num == SIGCHLD );
  assert( my_process_type == PROCESS_TYPE_LINER );

  int child_status;
  pid_t child_pid = wait( &child_status );
  LOG( "child_status: %d", child_status );
  update_cwd();
  if ( child_pid == -1 )
  {
    ERROR( "Some error when changing worker state %d, Exiting...", errno );
    free_and_exit( EXIT_FAILURE );
    return;
  }

  // Child exited and we can react on that.
  if ( WIFEXITED( child_status ) )
  {
    // Removing liner from liners list in order to keep memory usage low.
    int child_exit_code = WEXITSTATUS( child_status );
    LOG( "Child returned with exit code: %d", child_exit_code );

    last_worker_exited = true;

    switch ( child_exit_code )
    {
      case MSH_EXIT_BG:
      case MSH_EXIT_ALL:
        // Special exit codes should be passed over to the shell.
        free_and_exit( child_exit_code );
        break;
      case EXIT_SUCCESS:
        // Doing nothing, going to the next child
        break;
      default:
        // Should fail the whole line.
        free_and_exit( EXIT_FAILURE );
        break;
    }
  }
  else if ( WIFSIGNALED( child_status ) || WIFSTOPPED( child_status ) )
  {
    int child_signal =
        WIFSIGNALED( child_status ) ? WTERMSIG( child_status ) :
                                      WSTOPSIG( child_status );
    switch ( child_signal )
    {
      case SIGCONT:
        LOG( "Child received SIGCONT" );
        break;
      case SIGTSTP:
        LOG( "Child received SIGTSTP, doing nothing..." );
        break;
      default:
        // We don't know how to react to that signal sent to worker.
        ERROR( "Unexpected signal %d to child, killing it... %d", child_signal, child_pid );
        kill( child_pid, SIGKILL );
        free_and_exit( EXIT_FAILURE );
        break;
    }
  }
  else
  {
    LOG( "Unexpected worker's state change, exiting..." );
    free_and_exit( EXIT_FAILURE );
  }
}

// SIGCONT handler for liner.
static void sigcont_handler( int signal_num )
{
  assert( my_process_type == PROCESS_TYPE_LINER );
  LOG( "sigcont_handler for liner." );

  // Continue in background, putting ourselves into a separate group.
  int pgid = getpid();
  if ( setpgid( pgid, pgid ) == -1 )
  {
    ERROR( "Failed to create a separate process group" );
    free_and_exit( EXIT_FAILURE );
  }
  kill( liner_child_pid, SIGCONT );
}

// Run a single command from semicolon-delimited line.
void run_worker()
{
  assert( my_process_type == PROCESS_TYPE_WORKER );
  LOG( "Entering worker" );
  size_t tokens_count;
  for ( tokens_count = 0; tokens[tokens_count]; tokens_count++ )
    ;

  if ( tokens_count == 0 )
  {
    LOG( "Liner: command is empty, skipping..." );
    return;
  }

  char * command = tokens[0];
  if ( command == NULL )
  {
    ERROR( "Something bad happened while tokens processing" );
    free_and_exit( EXIT_FAILURE );
  }

  LOG( "Running worker, command %s", command );

  if ( strcmp( command, "cd" ) == 0 )
  {
    bool cd_succeded = true;
    if ( tokens_count == 1 )
    {
      char * home_value = getenv( "HOME" );
      if ( home_value == NULL )
      {
        ERROR( "cd: HOME variable not set\n" );
        cd_succeded = false;
      }
      else
      {
        cd_succeded = try_change_directory( home_value ) == 0;
      }
    }
    else if ( tokens_count > 2 )
    {
      ERROR( "cd: Too many arguments, must be one\n" );
      cd_succeded = false;
    }
    else
    {
      char * dest = tokens[1];
      cd_succeded = try_change_directory( dest ) == 0;
    }
    if ( !cd_succeded )
    {
      LOG( "cd failed!" );
      free_and_exit( EXIT_FAILURE );
    }
  }
  else if ( strcmp( command, "exit" ) == 0 || strcmp( command, "quit" ) == 0 )
  {
    free_and_exit( MSH_EXIT_ALL );
  }
  else if ( strcmp( command, "bg" ) == 0 )
  {
    free_and_exit( MSH_EXIT_BG );
  }
  else if ( strcmp( command, "history" ) == 0 )
  {
    // Traversing command history starting from the oldest element.
    // As we stated earlier, command_history_finish index is for the earliest element.
    // Then the first non-zero element found in the circular buffer will be indexed
    // "0: " in output for user.
    size_t icmd = command_history_finish;

    // Numbered index for current command output
    // is icmd_printed, icmd is index for command_history.
    size_t icmd_printed = MAX_COMMANDS_HISTORY_SIZE;

    do
    {
      if ( strlen( command_history[icmd] ) > 0 )
      {
        if ( icmd_printed == MAX_COMMANDS_HISTORY_SIZE )
        {
          icmd_printed = 0;
        }
        printf( "%lu: %s\n", icmd_printed + 1, command_history[icmd] );
        icmd_printed++;
      }
      icmd = ( icmd + 1 ) % MAX_COMMANDS_HISTORY_SIZE;
    } while ( icmd != command_history_finish );
  }
  else if ( strcmp( command, "listpids" ) == 0 || strcmp( command, "showpids" ) == 0 )
  {
    size_t ipid = pids_history_finish;
    // ipid_printed will set to the first valid pid.
    // So, currently it is set to invalid value, that it can never take,
    // while being needed to print.
    size_t ipid_printed = MAX_PIDS_HISTORY_SIZE;
    do
    {
      if ( pids_history[ipid] != 0 )
      {
        if ( ipid_printed == MAX_PIDS_HISTORY_SIZE )
        {
          ipid_printed = 0;
        }
        printf( "%lu: %d\n", ipid_printed, pids_history[ipid] );
        ipid_printed++;
      }
      LOG( "ipid %lu, ipid_printed %lu, pid %d", ipid, ipid_printed, pids_history[ipid] );
      ipid = ( ipid + 1 ) % MAX_PIDS_HISTORY_SIZE;
    } while ( ipid != pids_history_finish );
  }
  else
  {
    // Preparing to run external command with exec().
    char * cwd = get_current_dir_name();
    LOG( "Add current working directory \"%s\"to the PATH of command", cwd );
    char * env_path =
        (char *)malloc( strlen( "PATH=" ) + strlen( cwd ) + strlen( SEARCH_PATH_SUFFIX ) + 1 );
    strcpy( env_path, "PATH=" );
    strcat( env_path, cwd );
    free( cwd );
    strcat( env_path, SEARCH_PATH_SUFFIX );

    // I've tried to pass PATH environmental variable with execvpe,
    // but it didn't work - execvpe used PATH value from worker process,
    // even printing `env` output as we specify but underhood switching to
    if ( putenv( env_path ) )
    {
      ERROR( "Failed to put PATH variable into environment" );
    }
    else
    {
      int return_code = execvp( tokens[0], tokens );
      if ( return_code == -1 )
      {
        switch ( errno )
        {
          case ENOENT:
            ERROR( "%s: Command not found.", command );
            break;
          default:
            ERROR( "Error (%d) while trying to execute command: %s\n", errno, command );
            break;
        }
        free_and_exit( EXIT_FAILURE );
      }
    }
  }

  free_and_exit( EXIT_SUCCESS );
}

// Starts worker with current set of tokens.
void start_worker()
{
  assert( my_process_type == PROCESS_TYPE_LINER );

  last_worker_exited = false;
  liner_child_pid = fork();
  if ( liner_child_pid == 0 )
  {
    // Initializing worker.
    // Setting SIGCONT and SIGCHLD signals to default handlers,
    // as we are not going to follow the worker's children,
    // and default SIGCONT is fine with us.
    signal( SIGCONT, SIG_DFL );
    signal( SIGCHLD, SIG_DFL );
    my_process_type = PROCESS_TYPE_WORKER;
    run_worker();
  }
  else
  {
    LOG( "Forked a new child worker with pid %d", liner_child_pid );

    // Store pid, so the shell process will be able to read it afterwards.
    save_worker_pid_with_liner( liner_child_pid );

    // Pause, waiting for any change in the currently forked worker's state.
    // Flag last_worker_exited tells us if it is still alive.
    while ( !last_worker_exited )
    {
      pause();
    }
  }
}

/*
 * run_liner takes null-terminated cmd_line,
 * with only spaces and semicolons allowed between tokens
 * Tries to extract tokens sequences consisting one command to run.
 * All commands in the input sequence cmd_line are separated by ' ; '.
 */
void run_liner()
{
  assert( my_process_type == PROCESS_TYPE_LINER );
  size_t cmd_len = strlen( cmd_line );
  LOG( "Entering liner, cmd_line = \"%s\", cmd_len = %lu", cmd_line, cmd_len );

  size_t i;
  size_t tokens_count = 0;
  for ( i = 0; i < cmd_len; i++ )
  {
    if ( cmd_line[i] == ' ' )
    {
      continue;
    }

    if ( cmd_line[i] == ';' )
    {
      // The command currently parsed is finished.

      // That is for the format for passing arguments to exec().
      tokens[tokens_count++] = NULL;

      // It's time to send current tokens sequence to execution.
      start_worker();

      // Free tokens expecting the other command coming after ';'
      free_tokens();

      tokens_count = 0;

      // Increment, so the next value after cmd_line[i] is
      // definitely a token symbol or the end.
      i++;
    }
    else
    {
      assert( cmd_line[i] != ' ' && cmd_line[i] != ';' );
      size_t token_start = i;
      while ( i < cmd_len && cmd_line[i] != ' ' )
      {
        assert( cmd_line[i] != ';' );
        i++;
      }

      size_t token_len = i - token_start;

      // allocate space for new token, don't forget about null-terminating byte
      char * new_token = (char *)malloc( token_len + 1 );
      memcpy( new_token, cmd_line + token_start, token_len );
      new_token[token_len] = '\0';
      if ( tokens_count == MAX_NUM_ARGUMENTS )
      {
        ERROR( "liner: Too much tokens already" );
        free_and_exit( EXIT_FAILURE );
      }
      tokens[tokens_count++] = new_token;
    }
  }

  // We ended up traversing line, and there are still some tokens left ->
  // have to run one more command.
  if ( tokens_count > 0 )
  {
    tokens[tokens_count++] = NULL;
    start_worker();
    free_tokens();
  }

  free_and_exit( EXIT_SUCCESS );
}

// Initializing procedure for our shell,
// where it is going to take control over the whole terminal.
void start_shell()
{
  LOG( "Initializing shell" );
  msh_pgid = getpgrp();

  LOG( "start_shell: declaring signal handlers" );
  // Declare an interceptor for callback after child changes its state.
  sighandler_t previous_sigchld_handler = signal( SIGCHLD, sigchld_handler );
  assert( previous_sigchld_handler == SIG_DFL );

  // Ignore certain types of signals, as requested.
  signal( SIGINT, SIG_IGN );
  signal( SIGTSTP, SIG_IGN );

  // As we are going to make an interactive shell in its own process group.
  signal( SIGTTIN, SIG_IGN );
  signal( SIGTTOU, SIG_IGN );

  LOG( "Setting our process group" );
  // Putting ourselves in our own process group, so we can run
  // msh inside msh.
  // If not executed, msh still stops on Ctrl-Z
  msh_pgid = getpid();
  if ( setpgid( msh_pgid, msh_pgid ) == -1 )
  {
    ERROR( "Failed to create a separate process group" );
    free_and_exit( EXIT_FAILURE );
  }

  // After resetting process group -> taking control over the terminal.
  LOG( "Taking control over the terminal" );
  tcsetpgrp( STDIN_FILENO, msh_pgid );
  tcsetpgrp( STDOUT_FILENO, msh_pgid );
  tcsetpgrp( STDERR_FILENO, msh_pgid );

  // Setting auxiliary variables for msh.c's flow.
  my_process_type = PROCESS_TYPE_SHELL;

  // Initializing our file for storing current working directory -
  // as an easy way to transfer PWD between msh's processs.
  char * cwd = get_current_dir_name();

  // Store our working directory to the temporary file that has to be unique
  // for msh run with different pids (different instances).
  char pid_string_buf[10];
  memset( pid_string_buf, 0, sizeof( pid_string_buf ) );
  snprintf( pid_string_buf, sizeof( pid_string_buf ), "%d", getpid() );
  strcat( cwd_storage_filename, pid_string_buf );
  set_cwd( cwd );
  free( cwd );

  // Getting ready for a temporary file with will a buffer
  // for passing worker's pid between liner and shell.
  strcat( pid_storage_suffix, pid_string_buf );

  LOG( "Finished initializing shell" );
}

int main()
{
  size_t i;
  LOG( "Starting msh with pid %d", getpid() );

  start_shell();

  LOG( "Starting main loop" );
  // Main loop, each iteration - reading a new line (new command) from user.
  while ( 1 )
  {
    char cmd_str[MAX_COMMAND_SIZE];
    size_t cmd_str_len;
    // Print out the msh prompt
    print_prompt();

    // Read the command from the commandline.  The
    // maximum command that will be read is MAX_COMMAND_SIZE
    // This while command will wait here until the user
    // inputs something since fgets returns NULL when there
    // is no input
    while ( !fgets( cmd_str, MAX_COMMAND_SIZE, stdin ) )
    {
    }

    // in order to make a clean string cmd_line,
    // we have to reserve some place for spaces between tokens.
    // as we use single space to separate tokens,
    // it is maximum that 1 space will correspond to one symbol
    // (for some crazy shell when a lot of commands names have one symbol)
    // IMPORTANT Can't use continue for while (1) as we have to free cmd_line memory.
    cmd_str_len = strlen( cmd_str );
    cmd_line = (char *)malloc( 2 * cmd_str_len );
    memset( cmd_line, 0, 2 * cmd_str_len );
    size_t cmd_line_len = 0;

    bool is_first_token = true;
    for ( i = 0; i < cmd_str_len; i++ )
    {
      char c = cmd_str[i];

      if ( isspace( c ) )
      {
        continue;
      }

      if ( is_first_token )
      {
        is_first_token = false;
      }
      else
      {
        cmd_line[cmd_line_len++] = ' ';
      }

      LOG( "i = %lu, c = %c", i, c );

      if ( c == ';' )
      {
        cmd_line[cmd_line_len++] = ';';
      }
      else
      {
        while ( i < cmd_str_len && !isspace( cmd_str[i] ) && cmd_str[i] != ';' )
        {
          // put current token fully to cmd_line and wait for the next non-token symbol.
          cmd_line[cmd_line_len++] = cmd_str[i++];
        }

        if ( i < cmd_str_len && cmd_str[i] == ';' )
        {
          cmd_line[cmd_line_len++] = ' ';
          cmd_line[cmd_line_len++] = ';';
        }
      }

      cmd_line[cmd_line_len] = '\0';
    }

    LOG( "cmd_line = \"%s\"", cmd_line );

    // Check if cmd_line is !n and swap with command from history.
    // Checking for command !n, where is n is a number from 1 to 15 included.
    if ( cmd_line_len >= 2 && cmd_line_len <= 3 && cmd_line[0] == '!' )
    {
      size_t num = 0;
      if ( cmd_line_len == 2 && isdigit( cmd_line[1] ) )
      {
        num = ( size_t )( cmd_line[1] - '0' );
      }
      if ( cmd_line_len == 3 && isdigit( cmd_line[1] ) && isdigit( cmd_line[1] ) )
      {
        num = ( size_t )( ( cmd_line[1] - '0' ) * 10 + ( cmd_line[2] - '0' ) );
      }

      if ( num == 0 )
      {
        LOG( "!n: Failed to parse a number: %s", cmd_line + 1 );
      }
      else
      {
        // Find the earliest command in history.
        size_t icmd = command_history_finish;
        while ( strlen( command_history[icmd] ) == 0 )
        {
          icmd = ( icmd + 1 ) % MAX_COMMANDS_HISTORY_SIZE;
        }

        // Shift index to the index n of !n command.
        // Mind that the number from user can be from 1 to 15,
        // then we have to make it 0-based,
        // as we store history commands in a usual array.
        num--;

        icmd = ( icmd + num ) % MAX_COMMANDS_HISTORY_SIZE;
        free( cmd_line );
        cmd_line = strdup( command_history[icmd] );
        cmd_line_len = strlen( cmd_line );
        if ( cmd_line_len == 0 )
        {
          ERROR( "Command not in history" );
        }
      }
    }

    if ( cmd_line_len > 0 )
    {
      // Save current command line to history.
      memset( command_history[command_history_finish], 0, MAX_COMMAND_SIZE );
      strcpy( command_history[command_history_finish], cmd_line );
      command_history_finish = ( command_history_finish + 1 ) % MAX_COMMANDS_HISTORY_SIZE;

      last_liner_exited = false;
      int child_pid = fork();
      if ( child_pid == 0 )
      {
        // Initializing foreground liner job.
        my_process_type = PROCESS_TYPE_LINER;

        // We don't need shell's liners list, as we are liner,
        // and we don't controll our siblings.
        free_liner_list();
        signal( SIGINT, SIG_DFL );
        signal( SIGTSTP, SIG_DFL );
        signal( SIGCONT, sigcont_handler );
        signal( SIGCHLD, sigchld_handler_for_liner );
        signal( SIGTTIN, SIG_DFL );
        signal( SIGTTOU, SIG_DFL );
        run_liner();
        // Should exit from inside run_liner.
        assert( false );
      }
      else
      {
        LOG( "Forked a new liner with pid %d", child_pid );
        // Saving currently spawned liner's pid to history.
        add_pid_to_history( child_pid );

        // So, we are in the shell here, saving our liner job.
        assert( my_process_type == PROCESS_TYPE_SHELL );

        if ( liner != NULL && liner->liner_job->pid == child_pid )
        {
          LOG( "Already created liner with pid: %d", child_pid );
        }
        else
        {
          add_liner_list_item( child_pid );
        }

        if ( !last_liner_exited )
        {
          pause();
        }

        LOG( "Shell: Resuming main loop" );
      }
    }

    free_current_input_resources();
  }

  // No way we could get here.
  LOG( "We are out of input, Exiting..." );
  free_and_exit( EXIT_SUCCESS );
}
