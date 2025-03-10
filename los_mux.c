/*
 * Copyright (c) 2013-2019 Huawei Technologies Co., Ltd. All rights reserved.
 * Copyright (c) 2020-2021 Huawei Device Co., Ltd. All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without modification,
 * are permitted provided that the following conditions are met:
 *
 * 1. Redistributions of source code must retain the above copyright notice, this list of
 *    conditions and the following disclaimer.
 *
 * 2. Redistributions in binary form must reproduce the above copyright notice, this list
 *    of conditions and the following disclaimer in the documentation and/or other materials
 *    provided with the distribution.
 *
 * 3. Neither the name of the copyright holder nor the names of its contributors may be used
 *    to endorse or promote products derived from this software without specific prior written
 *    permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
 * "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO,
 * THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR
 * PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR
 * CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL,
 * EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO,
 * PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS;
 * OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY,
 * WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR
 * OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF
 * ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 */

#include "los_mux.h"
#include "los_compiler.h"
#include "los_config.h"
#include "los_debug.h"
#include "los_hook.h"
#include "los_interrupt.h"
#include "los_memory.h"
#include "los_sched.h"

#if (LOSCFG_BASE_IPC_MUX == 1)

LITE_OS_SEC_BSS       LosMuxCB*   g_allMux = NULL;
LITE_OS_SEC_DATA_INIT LOS_DL_LIST g_unusedMuxList;

/*****************************************************************************
 Function      : OsMuxInit
 Description  : Initializes the mutex
 Input        : None
 Output       : None
 Return       : LOS_OK on success, or error code on failure
 *****************************************************************************/
LITE_OS_SEC_TEXT_INIT UINT32 OsMuxInit(VOID)
{
    LosMuxCB *muxNode = NULL;
    UINT32 index;

    LOS_ListInit(&g_unusedMuxList);

    if (LOSCFG_BASE_IPC_MUX_LIMIT == 0) {
        return LOS_ERRNO_MUX_MAXNUM_ZERO;
    }

    g_allMux = (LosMuxCB *)LOS_MemAlloc(m_aucSysMem0, (LOSCFG_BASE_IPC_MUX_LIMIT * sizeof(LosMuxCB)));
    if (g_allMux == NULL) {
        return LOS_ERRNO_MUX_NO_MEMORY;
    }

    for (index = 0; index < LOSCFG_BASE_IPC_MUX_LIMIT; index++) {
        muxNode = ((LosMuxCB *)g_allMux) + index;
        muxNode->muxID = index;
        muxNode->owner = (LosTaskCB *)NULL;
        muxNode->muxStat = OS_MUX_UNUSED;
#if (LOSCFG_MUTEX_CREATE_TRACE == 1)
        muxNode->createInfo = 0;
#endif
        LOS_ListTailInsert(&g_unusedMuxList, &muxNode->muxList);
    }
    return LOS_OK;
}

/*****************************************************************************
 Function     : LOS_MuxCreate
 Description  : Create a mutex
 Input        : None
 Output       : muxHandle ------ Mutex operation handle
 Return       : LOS_OK on success, or error code on failure
 *****************************************************************************/
LITE_OS_SEC_TEXT_INIT UINT32 LOS_MuxCreate(UINT32 *muxHandle)
{
    UINT32 intSave;
    LosMuxCB *muxCreated = NULL;
    LOS_DL_LIST *unusedMux = NULL;
    UINT32 errNo;
    UINT32 errLine;

    if (muxHandle == NULL) {
        return LOS_ERRNO_MUX_PTR_NULL;
    }

    intSave = LOS_IntLock();
    if (LOS_ListEmpty(&g_unusedMuxList)) {
        LOS_IntRestore(intSave);
        OS_GOTO_ERR_HANDLER(LOS_ERRNO_MUX_ALL_BUSY);
    }

    unusedMux = LOS_DL_LIST_FIRST(&(g_unusedMuxList));
    LOS_ListDelete(unusedMux);
    muxCreated = (GET_MUX_LIST(unusedMux));
    muxCreated->muxCount = 0;
    muxCreated->muxStat = OS_MUX_USED;
    muxCreated->priority = 0;
    muxCreated->owner = (LosTaskCB *)NULL;
    LOS_ListInit(&muxCreated->muxList);
    *muxHandle = (UINT32)muxCreated->muxID;
    LOS_IntRestore(intSave);
    OsHookCall(LOS_HOOK_TYPE_MUX_CREATE, muxCreated);
    return LOS_OK;
ERR_HANDLER:
    OS_RETURN_ERROR_P2(errLine, errNo);
}

/*****************************************************************************
 Function     : LOS_MuxDelete
 Description  : Delete a mutex
 Input        : muxHandle ------Mutex operation handle
 Output       : None
 Return       : LOS_OK on success, or error code on failure
 *****************************************************************************/
LITE_OS_SEC_TEXT_INIT UINT32 LOS_MuxDelete(UINT32 muxHandle)
{
    UINT32 intSave;
    LosMuxCB *muxDeleted = NULL;
    UINT32 errNo;
    UINT32 errLine;

    if (muxHandle >= (UINT32)LOSCFG_BASE_IPC_MUX_LIMIT) {
        OS_GOTO_ERR_HANDLER(LOS_ERRNO_MUX_INVALID);
    }

    muxDeleted = GET_MUX(muxHandle);
    intSave = LOS_IntLock();
    if (muxDeleted->muxStat == OS_MUX_UNUSED) {
        LOS_IntRestore(intSave);
        OS_GOTO_ERR_HANDLER(LOS_ERRNO_MUX_INVALID);
    }

    if ((!LOS_ListEmpty(&muxDeleted->muxList)) || muxDeleted->muxCount) {
        LOS_IntRestore(intSave);
        OS_GOTO_ERR_HANDLER(LOS_ERRNO_MUX_PENDED);
    }

    LOS_ListAdd(&g_unusedMuxList, &muxDeleted->muxList);
    muxDeleted->muxStat = OS_MUX_UNUSED;
#if (LOSCFG_MUTEX_CREATE_TRACE == 1)
    muxDeleted->createInfo = 0;
#endif
    LOS_IntRestore(intSave);

    OsHookCall(LOS_HOOK_TYPE_MUX_DELETE, muxDeleted);
    return LOS_OK;
ERR_HANDLER:
    OS_RETURN_ERROR_P2(errLine, errNo);
}

STATIC_INLINE UINT32 OsMuxValidCheck(LosMuxCB *muxPended)
{
    if (muxPended->muxStat == OS_MUX_UNUSED) {
        return LOS_ERRNO_MUX_INVALID;
    }

    if (OS_INT_ACTIVE) {
        return LOS_ERRNO_MUX_IN_INTERR;
    }

    if (g_losTaskLock) {
        PRINT_ERR("!!!LOS_ERRNO_MUX_PEND_IN_LOCK!!!\n");
        return LOS_ERRNO_MUX_PEND_IN_LOCK;
    }

    if (g_losTask.runTask->taskStatus & OS_TASK_FLAG_SYSTEM_TASK) {
        return LOS_ERRNO_MUX_PEND_IN_SYSTEM_TASK;
    }

    return LOS_OK;
}

/*****************************************************************************
 Function     : LOS_MuxPend
 Description  : Specify the mutex P operation
 Input        : muxHandle ------ Mutex operation handleone
              : timeOut   ------- waiting time
 Output       : None
 Return       : LOS_OK on success, or error code on failure
 *****************************************************************************/
LITE_OS_SEC_TEXT UINT32 LOS_MuxPend(UINT32 muxHandle, UINT32 timeout)
{
    UINT32 intSave;
    LosMuxCB *muxPended = NULL;
    UINT32 retErr;
    LosTaskCB *runningTask = NULL;

    if (muxHandle >= (UINT32)LOSCFG_BASE_IPC_MUX_LIMIT) {
        OS_RETURN_ERROR(LOS_ERRNO_MUX_INVALID);
    }

    muxPended = GET_MUX(muxHandle);
    intSave = LOS_IntLock();
    retErr = OsMuxValidCheck(muxPended);
    if (retErr) {
        goto ERROR_MUX_PEND;
    }

    runningTask = (LosTaskCB *)g_losTask.runTask;
    // printf("%s is trying to obtain lock %d\n", runningTask->taskName, muxHandle);
    if (muxPended->muxCount == 0) {
        // printf("%s has indeed obtained %d\n", runningTask->taskName, muxHandle);
        muxPended->muxCount++;
        muxPended->owner = runningTask;
        muxPended->priority = runningTask->priority;
        LOS_IntRestore(intSave);
        goto HOOK;
    }

    if (muxPended->owner == runningTask) {
        muxPended->muxCount++;
        LOS_IntRestore(intSave);
        goto HOOK;
    }

    if (!timeout) {
        retErr = LOS_ERRNO_MUX_UNAVAILABLE;
        goto ERROR_MUX_PEND;
    }

    runningTask->taskMux = (VOID *)muxPended;

    if (muxPended->owner->priority > runningTask->priority) {
        printf("%s inherited priority %d from %s\n", muxPended->owner->taskName, runningTask->priority, runningTask->taskName);
        (VOID)OsSchedModifyTaskSchedParam(muxPended->owner, runningTask->priority);
    }

    OsSchedTaskWait(&muxPended->muxList, timeout);

    LOS_IntRestore(intSave);
    OsHookCall(LOS_HOOK_TYPE_MUX_PEND, muxPended, timeout);
    LOS_Schedule();

    intSave = LOS_IntLock();
    if (runningTask->taskStatus & OS_TASK_STATUS_TIMEOUT) {
        runningTask->taskStatus &= (~OS_TASK_STATUS_TIMEOUT);
        retErr = LOS_ERRNO_MUX_TIMEOUT;
        goto ERROR_MUX_PEND;
    }

    LOS_IntRestore(intSave);
    return LOS_OK;

HOOK:
    OsHookCall(LOS_HOOK_TYPE_MUX_PEND, muxPended, timeout);
    return LOS_OK;

ERROR_MUX_PEND:
    LOS_IntRestore(intSave);
    OS_RETURN_ERROR(retErr);
}

/*****************************************************************************
 Function     : LOS_MuxPost
 Description  : Specify the mutex V operation,
 Input        : muxHandle ------ Mutex operation handle
 Output       : None
 Return       : LOS_OK on success, or error code on failure
 *****************************************************************************/
LITE_OS_SEC_TEXT UINT32 LOS_MuxPost(UINT32 muxHandle)
{
    UINT32 intSave;
    LosMuxCB *muxPosted = GET_MUX(muxHandle);
    LosTaskCB *resumedTask = NULL;
    LosTaskCB *runningTask = NULL;

    intSave = LOS_IntLock();

    if ((muxHandle >= (UINT32)LOSCFG_BASE_IPC_MUX_LIMIT) ||
        (muxPosted->muxStat == OS_MUX_UNUSED)) {
        LOS_IntRestore(intSave);
        OS_RETURN_ERROR(LOS_ERRNO_MUX_INVALID);
    }

    if (OS_INT_ACTIVE) {
        LOS_IntRestore(intSave);
        OS_RETURN_ERROR(LOS_ERRNO_MUX_IN_INTERR);
    }

    runningTask = (LosTaskCB *)g_losTask.runTask;
    if ((muxPosted->muxCount == 0) || (muxPosted->owner != runningTask)) {
        LOS_IntRestore(intSave);
        OS_RETURN_ERROR(LOS_ERRNO_MUX_INVALID);
    }

    if (--(muxPosted->muxCount) != 0) {
        LOS_IntRestore(intSave);
        OsHookCall(LOS_HOOK_TYPE_MUX_POST, muxPosted);
        return LOS_OK;
    }



    //Also should assert(muxPosted->owner == runningTask)
    if ((muxPosted->owner->priority) != muxPosted->priority) {
        LosTaskCB *taskCB = NULL;
        UINT16 remaining_min_priority = muxPosted->priority;

        for (int loopNum = 0; loopNum < g_taskMaxNum; loopNum++) {
            taskCB = (((LosTaskCB *)g_taskCBArray) + loopNum);
            if (taskCB->taskStatus & OS_TASK_STATUS_UNUSED) {
                continue;
            }
            // printf("Iterating over task %s, priority %d\n", taskCB->taskName, taskCB->priority);
            if(taskCB->taskMux) {
                // printf("((LosMuxCB *)taskCB->taskMux)->owner is %s, running task is %s\n", ((LosMuxCB *)taskCB->taskMux)->owner->taskName, runningTask->taskName);
            }
            if ((taskCB->taskMux) && ((LosMuxCB *)taskCB->taskMux != muxPosted) && (((LosMuxCB *)taskCB->taskMux)->owner == runningTask) && taskCB->priority < remaining_min_priority) {
                remaining_min_priority = taskCB->priority;
            }
            
    
        }
        // printf("%s is releasing lock %d, its priority is now set to %d\n", runningTask->taskName, muxHandle, remaining_min_priority);
        
        
        (VOID)OsSchedModifyTaskSchedParam(muxPosted->owner, remaining_min_priority);
    }

    if (!LOS_ListEmpty(&muxPosted->muxList)) {
        resumedTask = OS_TCB_FROM_PENDLIST(LOS_DL_LIST_FIRST(&(muxPosted->muxList)));

        muxPosted->muxCount = 1;
        muxPosted->owner = resumedTask;
        muxPosted->priority = resumedTask->priority;
        resumedTask->taskMux = NULL;

        OsSchedTaskWake(resumedTask);

        LOS_IntRestore(intSave);
        OsHookCall(LOS_HOOK_TYPE_MUX_POST, muxPosted);
        LOS_Schedule();
    } else {
        muxPosted->owner = NULL;
        LOS_IntRestore(intSave);
    }

    return LOS_OK;
}

#endif /* (LOSCFG_BASE_IPC_MUX == 1) */

