 #include "iCunit.h"
#include "los_compiler.h"
 #include "los_mux.h"
 #include "los_task.h"
 #include "los_tick.h"
 #include <string.h>
 
 UINT32 m;
 UINT32 n;
 
 UINT32 umret = LOS_OK;
 UINT32 unret = LOS_OK;
 
 int nondet_int();
 
 
 #include "it_los_atomic.h"
 
 
 static VOID L(void) {
     printf("L started\n ");
     LOS_MuxPend(m, 1000);
     LOS_MuxPend(n, 1000);
     printf("L got lock\n");
     LOS_TaskDelay(4);
     LOS_MuxPost(m);
     LOS_TaskDelay(2);
     LOS_MuxPost(n);
 }
 
 static void M(void){
    __CPROVER_assert(0, "smoke");
     LOS_TaskDelay(1);
     UINT64 osEndTime;
     UINT64 osStartTime;
     UINT32 tickNum = 0;
     osStartTime = LOS_TickCountGet();
     int j = 0;
     UINT32 numticks = nondet_int();// was a number higher than the cumulative sum of delays of all other threads (e.g. 20)
     UINT32 innerloop = nondet_int();//was 10000000
    //  __CPROVER_assume(innerloop < 100 && numticks < 1000);
     for (int i = 0 ; i < numticks; i++) {// 外层循环多少次，大致就会花掉多少ticks来运行, busy-wait set by numticks
         j += i;
         for (int k = 0; k < innerloop; k++) {
             j += k;
         }
     }
     osEndTime = LOS_TickCountGet();
     tickNum = osEndTime - osStartTime;
     PRINTF("M finished with j = %d, took %d ticks", j, tickNum);
     
 }
 
 static void Hp(void){
     UINT64 osEndTime;
     UINT64 osStartTime;
     UINT32 tickNum = 0;
     LosMuxCB * muxPended = NULL;
     printf("Hp started\n");
     LOS_TaskDelay(2);
     osStartTime = LOS_TickCountGet();
     LOS_MuxPend(n, 2000);
     LOS_TaskDelay(1);
     osEndTime = LOS_TickCountGet();
     
     tickNum = osEndTime - osStartTime;
     PRINTF("Hp got lock n in %d ticks\n", tickNum);
     muxPended = GET_MUX(n);
     printf("Hp %d\n", muxPended->owner->taskID);
     printf("Hp %s\n", muxPended->owner->taskName);
     LOS_MuxPost(n);
     if (osEndTime - osStartTime > 20){
	 __CPROVER_assert(0, "priority inversion occurred\n");
         PRINTF("Hp took too long to get its lock!!!!!!!! tickNum = %d\n", tickNum);
     }
     LOS_TaskDelay(5); // 100, set delay time.
     
 }
 
 static VOID H(void)
 {
     UINT64 osEndTime;
     UINT64 osStartTime;
     UINT32 tickNum = 0;
     LosMuxCB *  muxPended = NULL;
     
     LOS_TaskDelay(1);
     printf("H started\n");
     osStartTime = LOS_TickCountGet();
     LOS_MuxPend(m, 1000); // 1000, Timeout interval of sem.
     LOS_TaskDelay(1);// H task delay length
     osEndTime = LOS_TickCountGet();
     tickNum = (osEndTime - osStartTime);
     PRINTF("H got lock m in %d ticks\n", tickNum);
     muxPended = GET_MUX(m);
     printf("H %d\n", muxPended->owner->taskID);
     printf("H %s\n", muxPended->owner->taskName);
     LOS_MuxPost(m);
 
 
     UINT32 inversion_delay = nondet_int();
     if (tickNum > nondet_int()) { //for a concrete example, use a number higher than the cumulative sum of delays in all other threads (e.g. 20)
         PRINTF("H took too long to get its lock!!!!!!!! tickNum = %d\n", tickNum);
     }
 
 
     LOS_TaskDelay(5); // 100, set delay time.
 }
 
 static UINT32 TestCase(VOID)
 {
     umret = LOS_MuxCreate(&m);
     unret = LOS_MuxCreate(&n);
     
     if (umret != LOS_OK) {
	 __CPROVER_assert(0, "create of lock m failed\n");
         printf("create m failed\n");
     }
     
     if (unret != LOS_OK) {
	 __CPROVER_assert(0, "create of lock n failed\n");
         printf("create n failed\n");
     }
     //__CPROVER_assert(0, "TestCase smoke\n");
     UINT32 ret;
     ret = 0;
     TSK_INIT_PARAM_S task1 = { 0 };
     task1.pfnTaskEntry = (TSK_ENTRY_FUNC)H;
     task1.uwStackSize = TASK_STACK_SIZE_TEST;
     task1.pcName = "H";
     task1.usTaskPrio = 5;
     task1.uwResved = LOS_TASK_STATUS_DETACHED;
     g_testCount = 0;
 
     ICUNIT_ASSERT_EQUAL(ret, LOS_OK, ret);
 
     TSK_INIT_PARAM_S task2 = { 0 };
     task2.pfnTaskEntry = (TSK_ENTRY_FUNC)Hp;
     task2.uwStackSize = TASK_STACK_SIZE_TEST;
     task2.pcName = "Hp";
     task2.usTaskPrio = 6;
     task2.uwResved = LOS_TASK_STATUS_DETACHED;
     g_testCount = 0;
 
 
     ICUNIT_ASSERT_EQUAL(ret, LOS_OK, ret);
 
     TSK_INIT_PARAM_S task3 = { 0 };
     task3.pfnTaskEntry = (TSK_ENTRY_FUNC)M;
     task3.uwStackSize = TASK_STACK_SIZE_TEST;
     task3.pcName = "M";
     task3.usTaskPrio = 10;
     task3.uwResved = LOS_TASK_STATUS_DETACHED;
     g_testCount = 0;
 
     ICUNIT_ASSERT_EQUAL(ret, LOS_OK, ret);
 
     TSK_INIT_PARAM_S task4 = { 0 };
     task4.pfnTaskEntry = (TSK_ENTRY_FUNC)L;
     task4.uwStackSize = TASK_STACK_SIZE_TEST;
     task4.pcName = "L";
     task4.usTaskPrio = 15;
     task4.uwResved = LOS_TASK_STATUS_DETACHED;
     g_testCount = 0;

     LOS_TaskLock();

     ret = LOS_TaskCreate(&g_testTaskID04, &task4);
     __CPORVER_assert(ret == LOS_OK, "task1 created good");
     __CPROVER_assert(0, "reachable");
     ret = LOS_TaskCreate(&g_testTaskID03, &task3);
     ret = LOS_TaskCreate(&g_testTaskID02, &task2); 
     ret = LOS_TaskCreate(&g_testTaskID01, &task1);
     printf("task H, Hp, M, L created, their IDs are %d, %d, %d, %d\n",g_testTaskID01, g_testTaskID02, g_testTaskID03, g_testTaskID04);
     LOS_TaskUnlock();
 
     ICUNIT_ASSERT_EQUAL(ret, LOS_OK, ret);
 
 
     return LOS_OK;
 }
 
 
 VOID main(VOID)
 {
    LOS_KernelInit();
	  ICunitInit();
    // TEST_ADD_CASE("ItLosAtomic001",(CASE_FUNCTION) TestCase, TEST_LOS, TEST_ATO, TEST_LEVEL0, TEST_FUNCTION);
    // __CPROVER_assert(0, "smoke test early term");
    // TestCase();
    iUINT32 uwRet = 1;                                                                                    
    uwRet = ICunitAddCase("ItLosAtomic001", (CASE_FUNCTION) TestCase, TEST_LOS, TEST_ATO, TEST_LEVEL0, TEST_FUNCTION);                                                                      
    //__CPROVER_assert(0, "smoke");
    // ICUNIT_ASSERT_EQUAL_VOID(uwRet, ICUNIT_SUCCESS, uwRet);      
    //__CPROVER_assert(uwRet == ICUNIT_SUCCESS, "smoke test");
    //TestCase();
    //return 1;
 }
 
