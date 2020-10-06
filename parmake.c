#define DEBUG 0
#define ER stderr
#include "format.h"
#include "graph.h"
#include "parmake.h"
#include "parser.h"
#include "set.h"
#include "queue.h"

#include <stdio.h>
#include <unistd.h>
#include <stdlib.h>
#include "time.h"
#include <sys/stat.h>
#include <pthread.h>

int detect_cycles(graph* this, void* val);
static set* explored;
static set* task_list;

static pthread_t* tid_ref;
static size_t tid_count;
static queue* task_queue;


static char* curr_goal;
static graph* curr_graph;
static ssize_t num_tasks;

static dictionary* depths;

pthread_mutex_t mutex = PTHREAD_MUTEX_INITIALIZER;
void generate_queue(set* task_list);
void thread_create(pthread_t* tids);
void* execute_parallel(void* param);
void thread_join();
void topological_sort();
void depth_sort();




void vector_print(vector *this){
    fprintf(ER, "--------------------------Vector print has been called!--------------------------\n");
    for(size_t i = 0; i < vector_size(this); i++){
        fprintf(stderr, "Vector at %zd: %s\n",i, (char*) vector_get(this, i));
    }
    fprintf(ER, "------------------------------End Vector print!----------------------------------\n");
}


void set_print(set *this){
    if(DEBUG == 0) return;
    vector *temp = set_elements(this);
    fprintf(ER, "++++++++++++++++++++++++++set print has been called!+++++++++++++++++++++++++++++\n");
    for(size_t i = 0; i < vector_size(temp); i++){
        fprintf(stderr, "Set at %zd: %s\n",i, (char*) vector_get(temp, i));
    }
    fprintf(ER, "++++++++++++++++++++++++++++++++End Set Print!+++++++++++++++++++++++++++++++++++\n");
    vector_destroy(temp);
}

static int depth = 0;
static int max = 0;
int detect_cycles(graph* this, void* val){
    depth++;
    if(depth > max) max = depth;

    if(DEBUG > 0) fprintf(ER, "Proving  acyclic on: %s\n", (char*) val);
    if(set_contains(explored, (char*) val) ){
        if(DEBUG > 0) fprintf(ER, "Set contains val: %s\n", (char*) val);
        vector* neighbors = graph_neighbors(this, val);
        if(vector_size(neighbors) == 0) return 0;
        if(DEBUG > 0) fprintf(ER, "There was a failure as set contained: %s \n!", (char*) val);
        vector_destroy(neighbors);
        return 1;

    }else{
        set_add(explored, (char*) val);
        // Ask, will neighbors return the parent even if directed?
        if(DEBUG > 1) fprintf(ER, "We will search on value: %s\n", (char*) val);
        vector* temp = graph_neighbors(this, val);
        if(DEBUG > 1) vector_print(temp);
        if(DEBUG > 0 ) set_print(explored);

        for(size_t i = 0; i < vector_size(temp); i++){
            int ret = detect_cycles(this, vector_get(temp, i));
            if(ret == 1){
                if(DEBUG > 1) fprintf(ER, "Failure propagate up: %s on %s \n!", (char*) val, (char*) vector_get(temp, i));
                vector_destroy(temp);
                return 1; // ASK: Do we want to return the parent?
            }
        }

        //set_add(task_list, (char*) val);
        set_remove(explored, (char*) val);
        if(DEBUG > 0) fprintf(stderr, "Adding val to explored: %s\n", (char*) val);
        vector_destroy(temp);
    }
    dictionary_set(depths, (char*) val, &depth);
    depth--;
    set_add(task_list, (char*) val);
    return 0;
}

// Note: oldest file will the be at the back
int time_diff(set* this){
    vector* filenames = set_elements(this);
    ssize_t size = vector_size(filenames);
    if( size > 2){
        char* start = vector_get(filenames, 0);
        struct stat start_att;
        stat(start, &start_att);
        for(ssize_t i = 1; i < size; i++){
            struct stat curr_att;
            stat( vector_get(filenames, i) , &curr_att );
            double difference = difftime(curr_att.st_ctime, start_att.st_ctime);
            if(difference >= 1.0){
                vector_destroy(filenames);
                return 1;
            }
        }
    }
    vector_destroy(filenames);
    return 0;
}


int execute_command(char* command){
    int res = system(command);
    if(res != 0){
        //fprintf(ER, "Make failed on command: %s\n!", command);
        return 1;
    }
    return 0;
}


/**
 * This function is the core of this program.
 * It's purpose is to delegate tasks for running make commands
 * @param:
 *  char *makefile --> The file to parse for the graph
 *  ssize_t num_threads --> The number of threads (remember n+1) for multi time
 *  char** targets --> the goal targets that we want to build
 * @return:
 *  int result --> Resulf of if the program failed or not?
 * 
 */
//static vector* target_vec = NULL;
//static vector* all_vertices;

int parmake(char *makefile, size_t num_threads, char **targets) {
    // Step 1.1 Generate a dependency graph
    pthread_t tids[num_threads];
    tid_count = num_threads;
    tid_ref = tids;
    graph* dep_graph = parser_parse_makefile(makefile, targets);
    //vector* goals = string_vector_create();
    // Step 2.0 Generate a vector of goals to run and cyclic on.
    vector* goals = graph_neighbors(dep_graph, "");
    if(DEBUG > 1) vector_print(goals);

    // Step 2.1 detect cycles for each goal
    // If not cycles then run the goals
    if(DEBUG > 1) fprintf(ER, "We are now onto part 2!\n");
    ssize_t goal_size = vector_size(goals);
    explored = string_set_create();
    task_list = string_set_create();


    //TODO: Determine thread size split up based on goals!
    // IE: Assign half of the threads to one goal, assign half to another
    for(ssize_t i = 0; i < goal_size; i++){
        depths = string_to_int_dictionary_create();
        void* current = vector_get(goals, i);
        int cyclic = detect_cycles(dep_graph, current);
        if(cyclic == 1){
            print_cycle_failure(current);
        }else{
            // Generate the queue of task to be completed
            curr_goal = (char*) current;
            curr_graph = dep_graph;
            if(DEBUG == -22) fprintf(ER, "Here\n");
            generate_queue(task_list);

            thread_create(tids);
            thread_join(tids);

            set_clear(task_list);
            set_clear(explored);

        }
    }



    dictionary_destroy(depths);
    vector_destroy(goals);
    set_destroy(explored);
    set_destroy(task_list);
    graph_destroy(dep_graph);
    // I guess we are done at this point?
    return 0;
}


void thread_create(pthread_t* tids){
    if(DEBUG == -22) fprintf(ER, "Creating threads!\n");
    for(size_t i = 0; i < tid_count; i++){
        if(DEBUG == -22) fprintf(ER, "Creating thread number: %zu!\n", i);
        pthread_create(&tids[i], NULL, execute_parallel, (void*)i); // figure out what exactly we want for the structure of this
    }
}


void thread_join(pthread_t* tids){
    if(DEBUG == -22) fprintf(ER, "Joining threads!\n");
    for(size_t i = 0; i < tid_count; i++){
        pthread_join(tids[i], NULL);
        if(DEBUG == -22) fprintf(ER, "Joined thread: %zu!\n", i);
    }
}
// Generates a queue for the tasks
// TODO: Add check for children's dependencies
void generate_queue(set* task_list){
    if(DEBUG == -22) fprintf(ER, "Generating queue!\n");
    num_tasks = (ssize_t) set_cardinality(task_list);

    task_queue = queue_create(num_tasks);
    if(DEBUG == -22 || DEBUG == -21)set_print(task_list);
    depth_sort();
    if(DEBUG == -22 || DEBUG == -21)set_print(task_list);
    vector* temp_vec = set_elements(task_list);


    for(size_t i = 0; i < (size_t) num_tasks; i++){
        if(DEBUG == -22) fprintf(ER, "Pushing %s onto queue!\n", (char*) vector_get(temp_vec, i));
        queue_push(task_queue, (char*) vector_get(temp_vec, i)  );
    }
    vector_destroy(temp_vec);
    if(DEBUG == -22) fprintf(ER, "Done generating!\n");

}


void depth_sort(){
    if(DEBUG == -22 || DEBUG == -21) fprintf(ER, "\n\nStart Depth sort with max d = %d!\n", max);
    vector* rule_vec = set_elements(task_list);
    for(int i = 0; i <= max; i++){
        for(size_t j = 0; j < vector_size(rule_vec); j++){
            rule_t* rule = (rule_t *)graph_get_vertex_value(curr_graph, vector_get(rule_vec, j));
            char* task = strdup( rule->target );
            void* temp = dictionary_get(depths, task);
            int depth = *(int*)temp;
            if(depth == i){
                if(DEBUG == -22 || DEBUG == -21) fprintf(ER, "Depths for  %s is %d !\n", task, depth );
                set_remove(task_list, task);
                set_add(task_list, task);
            }
            free(task);
        }
    }

    vector_destroy(rule_vec);

}


void topological_sort(){
    if(DEBUG == -22 || DEBUG == -21) fprintf(ER, "\n\nStart top sort!\n");
    vector* rule_vec = set_elements(task_list);

    for(size_t i = 0; i < vector_size(rule_vec); i++){
        rule_t* rule = (rule_t *)graph_get_vertex_value(curr_graph, vector_get(rule_vec, i));
        char* task = strdup( rule->target );
        void* temp = dictionary_get(depths, task);
        int depth = *(int*)temp;
        if(DEBUG == -22 || DEBUG == -21) fprintf(ER, "Depths for  %s is %d !\n", task, depth );
        vector* neighbors = graph_neighbors(curr_graph, task);
        if(vector_size(neighbors) == 0){
            if(DEBUG == -22 || DEBUG == -21) fprintf(ER, "Removing %s for sort !\n", task);
            set_remove(task_list, task);
            if(DEBUG == -22 || DEBUG == -21) fprintf(ER, "Adding %s for sort !\n", task);
            set_add(task_list, task);
        }
        free(task);

    }
    vector_destroy(rule_vec);


    if(DEBUG == -22 || DEBUG == -21) fprintf(ER, "End top sort!\n\n");
}

void* execute_parallel(void* param){
    if(DEBUG == -22) fprintf(ER, "Thread is going!\n");
    // So clearly we want to make this task master ruler based
    // So we can mark the rule with a flag saying if it fails or not

    // 0.0 Take task from queue
    // -1.0 if queue is empty exit the thread
    //  1.0 if not take the task
    //  1.1 Check if task's dependents have been satisfied
    //      1.15 if not then... wait?
    //      1.15 or take another task??

    // 2.0 run that shit
    // if that shit fails... check condition..
    // mark the rule as such


    //graph *dep_graph = curr_graph;
    while(true){


        if( set_cardinality(task_list) == 0 ){
            if(DEBUG == -22) fprintf(ER, "Car of task list is: %zu on %zu!\n", set_cardinality(task_list), (size_t) param ) ;
            return NULL;
        }
        if(DEBUG == -22) fprintf(ER, "loop on tid: %zu!\n", (size_t) param);

        pthread_mutex_lock(&mutex);
        if(num_tasks <= 0){
            if(DEBUG == -22) fprintf(ER, "CRITICAL>>> we ran out on tid: %zu!\n", (size_t) param);
            pthread_mutex_unlock(&mutex);
            return NULL;
        }
        num_tasks--;
        
        pthread_mutex_unlock(&mutex);
       // set* file_dependencies = string_set_create();

        char* task = queue_pull(task_queue);
        if(DEBUG == -22) fprintf(ER, "Attemping run on task: %s, tid: %zu!\n", task, (size_t) param );
        rule_t* rule = (rule_t *)graph_get_vertex_value(curr_graph, task);
        if(rule->state == -1){
            if(!strcmp(curr_goal, rule->target)){
                if(DEBUG == -22) fprintf(ER, "Goal complete on tid: %zu!\n", (size_t) param);
                set_remove(task_list, rule->target);
                return NULL;
            }
            set_remove(task_list, rule->target);
            continue;
        }

        // Not sure that this is a critical section but I will treat it as such for the moment
        vector* neighbors = graph_neighbors(curr_graph, task);

        // We need to check to make sure that deps are ready
        ssize_t neighbors_size = vector_size(neighbors);
        if(DEBUG == -22) fprintf(ER, "I wonder if we are locking on mutext tid: %zu!\n", (size_t) param);
        pthread_mutex_lock(&mutex);

        int flag = 0;
        for(ssize_t j = 0; j < neighbors_size; j++){
            //pthread_mutex_lock(&mutex);
            rule_t* curr = (rule_t *)graph_get_vertex_value(curr_graph, vector_get(neighbors, j) );
            int state = curr->state;
            if(state != 9){
                flag = 1;
                //vector_destroy(neighbors);
                // Do something here

                // if( set_contains(task_list, curr->target) == 1 ){
                //     // Considering doing a wait on condition
                // }


            }

        }
        if(flag == 1){
            num_tasks++;
            queue_push(task_queue, task);
            pthread_mutex_unlock(&mutex);
            continue;
        }

        pthread_mutex_unlock(&mutex);
            
        if(rule->state == 9){
            if(DEBUG == -22) fprintf(ER, "PAR>>> Rule: %s has already been executed! %zu\n", rule->target, (size_t) param);
            return NULL;
        } else if(rule->state == 0) {

                int command_failure = 0;
                ssize_t command_size = vector_size(rule->commands);
                for(ssize_t j = 0; j < command_size; j++){
                        int res = execute_command((char*)vector_get(rule->commands, j));
                        if(res == 1) {
                            rule_t * parent = (rule_t *)graph_get_vertex_value(curr_graph, curr_goal);
                            parent->state = -1;
                            // Do something
                            set_remove(task_list, rule->target);
                            rule->state = -1;
                            command_failure = 1;
                            break;
                        }
                }

                // Consider using a different mutex lock to avoid dead lock with the guys who are waiting on this 
                if(DEBUG == -22) fprintf(ER, " I wonder if there is a fight for the mutext, tid: %zu?\n", (size_t) param);
                pthread_mutex_lock(&mutex);
                if(command_failure != 1)  rule->state = 9;
                if( set_contains(task_list, rule->target) == 0){
                    if(DEBUG == -22) fprintf(ER, "PAR>>> ERROR NOT IN SET!!!! Rule: %s has already been executed tid: %zu!\n", rule->target, (size_t) param);
                } else { 
                    set_remove(task_list, rule->target);
                }
                if(DEBUG == -22)fprintf(ER, " Are we even in the mutext tid: %zu?\n", (size_t) param);
                pthread_mutex_unlock(&mutex);
        }

            //vector_destroy(neighbors);
        if(DEBUG == -22)fprintf(ER, "Let's iterate on %zu?\n", (size_t) param);
    }

    return NULL;
}

