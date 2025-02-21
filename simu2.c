#include <stdio.h>
#include <time.h>
#include <stdlib.h>

#define NUM_THREADS 4
#define NUM_LOCKS 2
#define MAX_EXECUTION_TIME 8
//threads have multiple fields, running time, priority, total time it took to finish, and its blocked time on the current lock.
//once a task's time taken field has gone down to zero, it will be seen as finished, and no longer be scheduled.
int running_time[NUM_THREADS];
int prio[NUM_THREADS];
int elapsed_time[NUM_THREADS];
//blocked[i] = k means thread i is blocked by lock k
int blocked[NUM_THREADS];

int waiting_time[NUM_THREADS];

int mutex[NUM_LOCKS];

//thread starts sleeping at time sleeping[i][0], and sleeps for sleeping[i][1] amount of time
int sleeping[NUM_THREADS][2];

void __CPROVER_assert(int cond, char * msg) {
    if (!cond) {
        printf("%s", msg);
    }
}
int nondet_int() {
    return rand();
}



//if thread i will acquire mutex j at time x, and hold it for y units of time after sucessfully obtaining it; then will_acquire[i][j] = x and locking_time[i][j] = y.
int will_acquire[NUM_THREADS][NUM_LOCKS];
int locking_time[NUM_THREADS][NUM_LOCKS];

int sys_tick_count = 0;
int max_waiting_time[NUM_THREADS] = {0};
int main()
{
    srand(time(NULL));
    for (int j = 0; j < NUM_LOCKS; j++) {
        mutex[j] = -1;
    }
    for (int i = 0; i < NUM_THREADS; i++){
        prio[i] = i;
        running_time[i] = abs(nondet_int() % MAX_EXECUTION_TIME) + 1;
        
        blocked[i] = -1;
        waiting_time[i] = 0;
        sleeping[i][0] = abs(nondet_int() % (running_time[i]));//this value indicates thread i should try to sleep after time sleeping[i][0]
        sleeping[i][1] = abs(nondet_int() % (running_time[i] - sleeping[i][0]));//indicates thread i should in total sleep for sleeping[i][1]
        printf("thread %d will sleep from %d for %d time\n", i, sleeping[i][0], sleeping[i][1]);
        for (int j = 0; j < NUM_LOCKS; j++) {
            will_acquire[i][j] = abs(nondet_int() % running_time[i]);
            locking_time[i][j] = abs(nondet_int() % (running_time[i] - will_acquire[i][j]));

            printf("thread %d, running %d time, will acquire lock %d starting from %d for %d time\n",i, running_time[i], j, will_acquire[i][j], locking_time[i][j]);
        }
        
    }
    //compute the maximum blocking time of each thread: for the highest prio thread, the sum of all remaining threads' lock holding time (critical section length).
    //for lower prio threads, they will be blocked by the maximum blcking chain of their own, plus all higher priority threads' lock holding time
    //it seems that in our particular case, the blocking length is always the sum of all critical regions except for the thread itself
    for(int i = 0; i < NUM_THREADS; i++) {
        max_waiting_time[i] = 0;
        for (int j = 0; j < NUM_THREADS; j++) {
            if (j != i) {
                max_waiting_time[i] = max_waiting_time[i] + running_time[j];
            }
        }
        printf("max waiting time of %d is %d\n", i, max_waiting_time[i]);
    }
    
    while(1){//The idea is that each loop in my simulation consists of two parts: the selecting thread to run phase and the running it phase.


        //now that running_time have been initialised (with priorities and a randomly assingned running time), we schedule them. As with liteos_m, higher number corresponds to lower priority.
        int highest_priority = NUM_THREADS;
        int to_run = -1;
        for (int i = 0; i < NUM_THREADS; i++){
            if (running_time[i] == 0){//if thread has finished already, do nothing. Otherwise always increase elapsed_time of that thread
                printf("time: %d, thread %d has finished\n", sys_tick_count, i);
            }
            else if (sleeping[i][0] <= sys_tick_count && sleeping[i][1] > 0) {//if thread is supposed to sleep (current time means "already needs to sleep", and has not slept enough0), let it sleep, and reduce the sleep time
                printf("time: %d, thread %d is supposed to sleep, sleeping %d more units of time\n", sys_tick_count, i, sleeping[i][1]);
                sleeping[i][1]--;
                if (sleeping[i][1] == 0) {
                    sleeping[i][1] = -1;
                }
                elapsed_time[i]++;
            }
            else if (blocked[i] != -1) {//if thread is blocked, continue to block it, increment its blocked timer to record how long it waited, detecting priority inversion
                printf("time: %d, thread %d is blocked by mutex %d, owner of which is %d\n", sys_tick_count, i, blocked[i], mutex[blocked[i]]);
                elapsed_time[i]++;
                waiting_time[i]++;
                __CPROVER_assert(waiting_time[i] <= max_waiting_time[i] + 2, "priority inversion");
            }
            else if (prio[i] >= highest_priority) {//if priority is low (numeric value is high) compared to existing priority, then do not schedule
                printf("time :%d, priority of thread %d is %d, lower than current highest priority which is %d\n", sys_tick_count, i, prio[i], highest_priority);
                elapsed_time[i]++;
            }
            else {//priority is high, is not sleeping/blocked, try to determine if we can schedule it: if no mutex is blocking it, then we can schedule it in this tick.
                printf("task %d has priority %d, can be scheduled, now 'run it' until it hit a lock which blocks it, or choose to schedule it if not blocked.\t", i, prio[i]);
                elapsed_time[i]++;
                // int is_blocked = 0;
                for (int j = 0; j < NUM_LOCKS; j++) {
                    if (will_acquire[i][j] <= sys_tick_count && locking_time[i][j] > 0){
                        // if (mutex[j] == -1) {
                        //     mutex[j] = i;
                        // }
                        if (mutex[j] != -1 && mutex[j] != i) {//lock already taken by another thread, must be blocked
                            blocked[i] = j;
                            int owner = mutex[j];
                            if(prio[i] < prio[owner]) {
                                //promote the lock owner to blocked thread
                                prio[owner] = prio[i];
                            }
                            break;
                        }
                        else {
                            mutex[j] = i;
                        }
                    }
                }
                if (blocked[i] == -1){//is not blocked by any thread, can be scheduled
                    printf("%d is not blocked\n", i);
                    highest_priority = prio[i];
                    to_run = i;
                }
                else {
                    printf("%d is blocked by mutex %d\n", i, blocked[i]);
                }
            }
        }
        printf("torun: %d\n", to_run);

        int flag = 0;
        if(to_run == -1) {//nothing to schedule, either deadlocked or all sleeping/blocked. exit simulation //must improve this by detecting deadlocks, if not deadlocking, should "fast forward"
            for(int i = 0; i < NUM_THREADS; i++) {
                if (sleeping[i][1] == -1) {
                    sleeping[i][1] = 0;
                    flag = 1;
                }
                if (sleeping[i][1] > 0) {
                    flag = 1;
                }
            }
            if (flag) {
                continue;
            }
            else {
                break;
            }
        }



        for (int j = 0; j < NUM_LOCKS; j++) {//now check each lock, and try to release/acquire as necessary
            if (mutex[j] == to_run ){//if thread is holding the lock
                locking_time[to_run][j]--;
                if (locking_time[to_run][j] <= 0) {
                    //release the lock
                    mutex[j] = -1;
                    int highest_waiting_prio = NUM_THREADS;
                    int kmax = -1;
                    for(int k = 0; k < NUM_THREADS; k++) {
                        if (blocked[k] == j && highest_waiting_prio > prio[k]) {//if thread k is blocked by the released lock j, should wake it up
                            kmax = k;
                            highest_waiting_prio = prio[k];
                        }
                    }
                    if (kmax >= 0) {//choose the waiting thread with the highest priority
                        blocked[kmax] = -1;
                        waiting_time[kmax] = 0; //waiting time is cleared for the current lock
                    }
                    int remaining_highest_prio = to_run;
                    if (to_run != prio[to_run]){
                        for (int k = 0; k < NUM_THREADS; k++) {
                            if (k == to_run) {
                                continue;
                            }
                            else {
                                if (blocked[k] != -1 && mutex[blocked[k]] == to_run && remaining_highest_prio > prio[k]) {
                                    remaining_highest_prio = prio[k];
                                }
                            }
                        }
                    }
                    prio[to_run] = remaining_highest_prio;//back to original priority when releasing a lock (prio inheritance)
                }
            }
            else if (will_acquire[to_run][j] <= sys_tick_count && locking_time[to_run][j] > 0) {//if thread is supposed to acquire this lock
                if(mutex[j] == -1) {
                    mutex[j] = to_run;
                    running_time[to_run]--;
                }
                else{//if selected, must be in a non-blocking condition (currently an over-approximation--a thread can acquire some locks before it is being blocked in a tick)
                    __CPROVER_assert(0, "not allowed to run a thread if it is being blocked by a lock it is trying to acquire");
                    blocked[j] = to_run;
                    int owner = mutex[j];
                    if (prio[owner] > prio[to_run]) {
                        //promote owner (owner of lock j) temporarily
                        prio[owner] = prio[to_run];
                    }
                }
            }
            else {//no locks involved
                ;
            }
        }
        //thread has run its time slice
        running_time[to_run]--;//successfully ran this thread for this time slice
        sys_tick_count++;
    }
    for(int i = 0; i < NUM_THREADS; i++){
        printf("Thread %d waited %d in total\n",i, elapsed_time[i]);
    }
    return 0;
}