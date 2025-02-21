#include <assert.h>
#include <limits.h>

#define NUM_TASKS 3

// Task structure: priority and remaining time
typedef struct {
    int priority;
    int remaining_time;
} Task;

int total_time_waited[NUM_TASKS] = {0};

// Function to select the highest priority task
int select_task(Task tasks[NUM_TASKS]) {
    int highest_priority = INT_MAX;
    int selected_task = -1;
    for (int i = 0; i < NUM_TASKS; i++) {
        if (tasks[i].remaining_time >0) {
            total_time_waited[i]++;
        }
        if (tasks[i].remaining_time > 0 && tasks[i].priority < highest_priority) {
            highest_priority = tasks[i].priority;
            selected_task = i;
        }
    }
    return selected_task;
}

// Function to simulate one time slice
void time_slice(Task tasks[NUM_TASKS]) {
    int task_id = select_task(tasks);
    if (task_id != -1) {
        tasks[task_id].remaining_time--;
    }
}

int main() {
    // Initialize tasks with priorities and burst times
    Task tasks[NUM_TASKS] = {
        {1, 5}, // Task 0: priority 1, burst time 5
        {2, 3}, // Task 1: priority 2, burst time 3
        {3, 2}  // Task 2: priority 3, burst time 2
    };

    // Simulate scheduling for a number of time slices
    for (int i = 0; i < 10; i++) {
        time_slice(tasks);
    }

    // Assert that all tasks have completed
    for (int i = 0; i < NUM_TASKS; i++) {
        // __CPROVER_assert(tasks[i].remaining_time == 0, "all tasks should be completed");
        printf("Task %d: remaining time = %d, waited %d in total\n", i, tasks[i].remaining_time, total_time_waited[i]); // P
    }

    return 0;
}
