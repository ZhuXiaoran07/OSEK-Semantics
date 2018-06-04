require "./osek-initialization.k" 
require "./osek-imp.k" 

// 38 rules

module OSEK-TASK
  imports OSEK-CONFIGURATION 
  imports OSEK-INITIALIZATION  
  imports IMP-SEMANTICS   
  /*@ \section{Tasks}
  This module defines some APIs about task management with the different task types and scheduling mechanisms.

  */   

   /*@ Define the semantics of \texttt{auto start}.  If a task is auto-started and the program is not in the TCG mode, 
       it is put into ready list and send a schedule signal to invoke the scheduler. The system calls is loaded and they 
       are going to be executed by the system. */

    rule <task> <auto> true => false </auto> <tid> I </tid> <state> suspend => ready </state>
   	<tPriority> N:Int </tPriority> 
	<apiData> S:OSEKStmt </apiData> <k> .K => S </k> ... </task> 
        <readyTasks> LTP:ListTaskPair => add(I,N,LTP) </readyTasks> 
	<signal> .Set => SetItem(schedule) </signal> 
	//<tcgMode> false </tcgMode> 
  [transition]

      rule <task> <tid> I </tid> <state> running </state>
    <tPriority> N:Int </tPriority> 
  <apiData> S:OSEKStmt </apiData> <k> .K => S </k> ... </task> 
       // <readyTasks> LTP:ListTaskPair => add(I,N,LTP) </readyTasks> 
  <signal> .Set  </signal> 
  //<tcgMode> false </tcgMode> 
  [transition]

   rule S:Stmt .K => S [structural] 

   syntax SysApi ::= "getApi" "(" APIStmt ")" [function]
   
   rule getApi(GetResource(R);) => GetResource 
   rule getApi(ReleaseResource(R);) => ReleaseResource
   rule getApi(ActivateTask(R);) => ActivateTask
   rule getApi(ChainTask(R);) => ChainTask
   rule getApi(TerminateTask();) => TerminateTask

   syntax OSEKStmt ::= "convert2apis" "(" List ")" [function]
   rule convert2apis(.List) => .  [structural]
   rule convert2apis(ListItem(A:APIStmt) L) => (A convert2apis(L))  [structural]
//DeclareTask
rule <task><state>running</state><k>DeclareTask(T);=>. ...</k>...</task>
<task><tid>T</tid>...</task>
<signal> .Set </signal>
<alarm> <aid> A </aid> <aSysCounter> C</aSysCounter> <alarmTime>AT</alarmTime> ...</alarm><br/>
<sysCounter> <cid> C </cid> <currentValue> RV=>(RV+Int 1)%Int (MAV +Int 1) </currentValue> <maxAllowedValue> MAV </maxAllowedValue> ...</sysCounter>

rule <task><state>running</state><k>DeclareTask(T);=>. ...</k>...</task>
<task><tid>T</tid>...</task>
<signal> .Set=>SetItem(stop) </signal>
<alarm> <aid> A </aid> <aSysCounter> C</aSysCounter> <alarmTime>AT</alarmTime> ...</alarm><br/>
<sysCounter> <cid> C </cid> <currentValue> RV=>(RV+Int 1)%Int (MAV +Int 1) </currentValue> <maxAllowedValue> MAV </maxAllowedValue> ...</sysCounter>

//GetTaskID
rule <task><tid>T</tid><state>running</state><k>GetTaskID(ID);=>T ...</k>...</task>
<return>_=>T</return>
<signal> .Set </signal>

//GetTaskState
rule <task><state>running</state><k>GetTaskState(T,S);=>. ...</k>...</task>
	<task><tid>T</tid><state>S'</state>...</task>
	<return>_=>S'</return>
	<signal> .Set </signal>


    /*@ \subsection{Multiple requesting of task activation}
      In this section, we take multiple requesting of task activation into account. The number of multiple requests is defined when
      the task is declared. This parameter is stored in cell activationTime. It is our understanding that
      if a running task is actived again, the change of this task's state is running to suspend, and then to ready.\\
      According to the OSEK specification, only system service TerminateTask and ChainTask can change a task's state to suspend.
      Here a problem comes. As introduced about schedule, if task A is terminated then scheduling is performed immediately.
      However, in case task A has been multiple activated, should scheduling perform first or chang A's state to ready first?
      \par We have analized this two conditions. If scheduling perform firstly, assume task B is scheduled and then state of task A 
      becomes to ready. In fact at this time, system needs to perform scheduling again. But there is no scheduling policy about this 
      case in the OSEK specification. It seems not that reasonable.\\
      \par Thus, in our model, we adopt the second condition which means two steps are include in system service TerminateTask if the running task has been multiple activated.
      One is changing task's state from running to suspend. If value of activatedTime is not zero, then the state of this task is turned to ready.
      After these, scheduling should to be performed. I have thougt change the state of task from suspend to ready directly when terminating a
      multiple activated task. Maybe this idea is too abstract to conforms with the OSEK specification.\\
      \par Ways to deal with ChainTask is the same with TerminateTask.
    */
	
 /* rule <task> <tid> I </tid> <state> suspend=>ready </state> <tPriority> N </tPriority> <activatedTime> N1=>N1-Int 1 </activatedTime> ... </task>
        //<task> <state> running </state> <tPriority> N' </tPriority> </task>
        <readyTasks> L:ListTaskPair => add(I,N,L) </readyTasks>
         <signal> .Set => SetItem(schedule) </signal> 
         <proId> I </proId>
        when (N1=/=Int 0) [transition]*/

    rule <task> <tid> I </tid> <state> suspend=>ready </state> <tPriority> N </tPriority> <activatedTime> N1=>N1-Int 1 </activatedTime> ... </task>
   <task> <state> running </state> <tPriority> N' </tPriority> </task>
        <readyTasks> L:ListTaskPair => add(I,N,L) </readyTasks>
         <signal> .Set => SetItem(schedule) </signal> 
         <proId> I </proId>
        when (N1=/=Int 0) [transition]

   /*@ API:       TerminateTask(TaskID)\\
       Parameter: TaskID\\
       Result:    Task<TaskID> suspends itself and sends a signal to schedule.\\
       Condition: Task<TaskID> to be terminated can not occupy any resources; TerminateTask() must be the
       last API of the running task.*/

/*@ 
  For the API TerminateTask(), two cases are introduced in our implementation except alarm expiration.
   One is to terminate a task which has been mutiple actived. Another is to terminate a task whose activedTime
   is 0. 

*/

   rule <task> <tid> I </tid> <state> running => suspend </state> 
           <k> TerminateTask(); => .</k> 
            
         //  <activatedTime> 0 </activatedTime>
<accRes> .List </accRes> ... 
</task> 
<sysCounter><cid> C </cid> <currentValue> RV=>(RV+Int 1)%Int (MAV +Int 1) </currentValue> <maxAllowedValue> MAV </maxAllowedValue> ... </sysCounter>
  <runningTask> I => . </runningTask>
        <signal> .Set => SetItem(schedule) </signal>
        <alarmList> .List </alarmList>
 [transition]


   rule <task> <tid> I </tid> <state> running => suspend </state>  <k> TerminateTask();=> . </k> 
           <activatedTime> 0 </activatedTime>
<accRes> .List </accRes> ... </task>	
<signal> .Set => SetItem(schedule) </signal>
<alarm><aid> A1 </aid> <aSysCounter> C1</aSysCounter> <alarmTime>AT1</alarmTime> ...</alarm>
  <alarm><aid> A2</aid> <aSysCounter> C2</aSysCounter> <alarmTime>AT2</alarmTime> ...</alarm>
  <alarm><aid> A3 </aid> <aSysCounter> C3</aSysCounter> <alarmTime>AT3</alarmTime> ...</alarm>
  <br/>
<sysCounter><cid> C </cid> <currentValue> RV=>(RV+Int 1)%Int (MAV +Int 1) </currentValue> <maxAllowedValue> MAV </maxAllowedValue> ...</sysCounter>
<runningTask> I => . </runningTask>
<alarmList> L1 </alarmList>
    when  ((RV +Int 1)<Int AT1) andBool ((RV +Int 1)<Int AT2)andBool ((RV +Int 1)<Int AT3)  [transition]
        
 //when ((RV +Int 1)<Int AT) andBool (A in L) [transition]


rule <task> <tid> I </tid> <state> running => suspend </state> 
           <k> TerminateTask(); => . </k> <activatedTime> 0 </activatedTime>
<accRes> .List </accRes> ... 
</task> 
<signal> .Set =>SetItem(alarmed) SetItem(schedule) </signal>
<alarm> <aid> A </aid> <aSysCounter> C</aSysCounter> <alarmTime>AT</alarmTime> ...</alarm><br/>
<sysCounter> <cid> C </cid> <currentValue> RV=>(RV+Int 1)%Int (MAV +Int 1) </currentValue> <maxAllowedValue> MAV </maxAllowedValue> ...</sysCounter>
  <runningTask> I => . </runningTask>
  <alarmList> L </alarmList>
 when ((RV +Int 1)==Int AT) andBool (A in L)[transition]


    rule <task> <tid> I </tid> <state> running => suspend </state> <tPriority> N </tPriority>
           <k> TerminateTask(); => . </k>  <activatedTime> N1 </activatedTime>
<accRes> .List </accRes> ... 
</task> 
<alarm><aid> A </aid> <aSysCounter> C</aSysCounter> <alarmTime>AT</alarmTime> ...</alarm><br/>
<sysCounter><cid> C </cid> <currentValue> RV=>(RV+Int 1)%Int (MAV +Int 1) </currentValue> <maxAllowedValue> MAV </maxAllowedValue> ...</sysCounter>
  <runningTask> I => . </runningTask>
        <signal> .Set </signal>
        <alarmList> L </alarmList>
        <proId> _=>I </proId> 
 when ((RV +Int 1)<Int AT) andBool (N1=/=Int 0) andBool (A in L)[transition]


    rule <task> <tid> I </tid> <state> running => suspend </state> <tPriority> N </tPriority>
           <k> TerminateTask(); => . </k>  <activatedTime> N1 </activatedTime>
<accRes> .List </accRes> ... 
</task> 
<alarm><aid> A </aid> <aSysCounter> C</aSysCounter> <alarmTime>AT</alarmTime> ...</alarm><br/>
<sysCounter><cid> C </cid> <currentValue> RV=>(RV+Int 1)%Int (MAV +Int 1) </currentValue> <maxAllowedValue> MAV </maxAllowedValue> ...</sysCounter>
  <runningTask> I => . </runningTask>
        <signal> .Set => SetItem(alarmed) </signal>
        <proId> _=>I </proId>
        <alarmList> L </alarmList>
  //<tcgMode> false </tcgMode> 
  //<readyTasks> RT:ListTaskPair => add(I, N, RT) </readyTasks> 
 when ((RV +Int 1) ==Int AT) andBool (N1=/=Int 0) andBool (A in L)[transition] 


 rule <task> <tid> I </tid> <state> running => suspend </state> <tPriority> N </tPriority>
           <k> TerminateTask(); => . </k>  <activatedTime> N1 </activatedTime>
<accRes> .List </accRes> ... 
</task> 
<runningTask> I => . </runningTask>
        <signal> .Set => SetItem(schedule) </signal>
 
 

   // if TerminateTask() is not the last API in the task 
   rule <task> <tid> I </tid> <state> running </state> 
   	       (<k> TerminateTask(); A:OSEKStmt  </k> )  ... </task>	
	<runningTask> I => . </runningTask>
        <signal> .Set => SetItem(stop) </signal> <br/>
	(.Bag => <errorCell> Error(E_OS_UNDEF, I, TerminateTask();,"TerminateTask() is not the last API in task " +String Id2String(I)) </errorCell> )
//	<tcgMode> false </tcgMode> 
  [transition]



   // if the last API is not  TerminateTask() or ChainTask in the task 
   rule <task> <tid> I </tid> <state> running </state> 
   	       (<k> A:APIStmt </k> )  ... </task>	
	<runningTask> I => . </runningTask>
        <signal> .Set => SetItem(stop) </signal> <br/>
	(.Bag => <errorCell> Error(E_OS_UNDEF, I, A, "The last API should be TerminateTask or ChainTask in task " +String Id2String(I)) </errorCell> )
//	<tcgMode> false </tcgMode>
	when getApi(A) =/=K TerminateTask andBool getApi(A) =/=K ChainTask [transition]


   
    /*@API:       ChainTask(TaskID) \\
       Parameter: TaskID\\
       Result:    The running task terminates itself and activates task<TaskID> \\
       Condition: The task to be terminated can not occupy any resources; ChainTask() must be the
       last API of the running task; task<TaskID> is not in the readyTask list.*/

    /*@ Three cases about ChainTask is considered in our implementation.\\
        1. Task to be activated is a suspend task. In this condition, its state changes from suspend to ready and scheduling is performed;
        2. Task to be activated is a ready task. If this task can be mutiple activated, we record this activation by add 1 to value of activatedTime;
        3. Task to be activated is the running task. This case is the same as system service TerminateTask which we has introduced before.

    */



      rule <task> <tid> I </tid> <state> running => suspend </state> 
           (<k> ChainTask(T); => . ...</k> ) 
         <accRes> .List </accRes> 
         <apiData> A:OSEKStmt ... </apiData> ... </task>  
        <task> <tid> T </tid> <tPriority> N </tPriority> 
         <state> suspend => ready </state> 
        ...  </task> 
      <runningTask> I => . </runningTask>
        <signal> .Set=> SetItem(schedule) </signal>
         <sysCounter> <currentValue> RV=>(RV+Int 1)%Int (MAV +Int 1) </currentValue> <maxAllowedValue> MAV </maxAllowedValue> ... </sysCounter>
         
  <readyTasks> RT:ListTaskPair => add(T, N, RT) </readyTasks> 
   [transition]
   

   rule <task> <tid> I </tid> <state> running => suspend </state> 
           <k> ChainTask(T); => . ...</k>
        <accRes> .List </accRes> ... 
       </task>  
        <task> <tid> T </tid> <tPriority> N </tPriority> 
         <state> suspend => ready </state>...
           </task> <br/>
  <runningTask> I => . </runningTask>
        <signal> . => SetItem(schedule)  </signal>
		<readyTasks> RT:ListTaskPair => add(T, N, RT) </readyTasks> 
   
   
      rule <task> <tid> I </tid> <state> running => suspend </state> 
           <k> ChainTask(T); => . ...</k>
        <accRes> .List </accRes> ... 
       </task>  
        <task> <tid> T </tid> <tPriority> N </tPriority> 
         <state> suspend => ready </state>...
           </task> <br/>
  <runningTask> I => . </runningTask>
        <signal> . => SetItem(schedule)  </signal>
        <sysCounter> <currentValue> RV=>(RV+Int 1)%Int (MAV +Int 1) </currentValue> <maxAllowedValue> MAV </maxAllowedValue> ...</sysCounter>
  //<tcgMode> false </tcgMode> <br/>
  <alarmList> .List </alarmList>
  <readyTasks> RT:ListTaskPair => add(T, N, RT) </readyTasks> 
 [transition]

    
   rule <task> <tid> I </tid> <state> running => suspend </state> 
   	       (<k> ChainTask(T); => . ...</k> ) <activatedTime> N1 </activatedTime>
	      <accRes> .List </accRes> ... 
       </task>	
        <task> <tid> T </tid> <tPriority> N </tPriority> 
	       <state> suspend => ready </state> <ext> false </ext>... 
	         </task> <br/>
	<runningTask> I => . </runningTask>
        <signal> .Set => SetItem(schedule) </signal>
        <alarm><aid> A </aid><aSysCounter> C</aSysCounter> <alarmTime>AT</alarmTime> ...</alarm><br/>
        <sysCounter><cid> C </cid> <currentValue> RV=>(RV+Int 1)%Int (MAV +Int 1) </currentValue> <maxAllowedValue> MAV </maxAllowedValue> ...</sysCounter>
	//<tcgMode> false </tcgMode> <br/>
  <alarmList> L </alarmList>
	<readyTasks> RT:ListTaskPair => add(T, N, RT) </readyTasks> 
 
	 when ((RV +Int 1)<Int AT) andBool (N1==Int 0) andBool (A in L)[transition]

  
     rule <task> <tid> I </tid> <state> running => suspend </state> 
           (<k> ChainTask(T); => . </k> ) <activatedTime> N1 </activatedTime>
         <accRes> .List </accRes> ... 
       </task>  
        <task> <tid> T </tid> <tPriority> N </tPriority> 
         <state> suspend => ready </state> <ext> false </ext> 
          ...  </task> <br/>
  <runningTask> I => . </runningTask>
        <signal> S:Set => SetItem(schedule) SetItem(alarmed) S </signal>
        <alarm><aid> A </aid><aSysCounter> C</aSysCounter> <alarmTime>AT</alarmTime> ...</alarm><br/>
        <sysCounter><cid> C </cid> <currentValue> RV=>(RV+Int 1)%Int (MAV +Int 1) </currentValue> <maxAllowedValue> MAV </maxAllowedValue>... </sysCounter>
 // <tcgMode> false </tcgMode> <br/>
   <alarmList> L </alarmList>
  <readyTasks> RT:ListTaskPair => add(T, N, RT) </readyTasks> 
   when ((RV +Int 1) ==Int AT) andBool (N1==Int 0)andBool (A in L)[transition]

     rule <task>  <state> running => suspend </state> 
           (<k> ChainTask(T); => . ...</k> ) <activatedTime> N1 </activatedTime>
         <accRes> .List </accRes> ... 
       </task>  
        <task> <tid> T </tid> <tPriority> N </tPriority> 
         <state> suspend => ready </state> <ext> true </ext> <taskEvents> M => clear(M) </taskEvents>...
           </task> <br/>
  <runningTask> I => . </runningTask>
        <signal> S:Set => SetItem(schedule) S </signal>
        <alarm><aid> A </aid><aSysCounter> C</aSysCounter> <alarmTime>AT</alarmTime>... </alarm><br/>
        <sysCounter><cid> C </cid> <currentValue> RV=>(RV+Int 1)%Int (MAV +Int 1) </currentValue> <maxAllowedValue> MAV </maxAllowedValue> ...</sysCounter>
 // <tcgMode> false </tcgMode> <br/>
   <alarmList> L </alarmList>
  <readyTasks> RT:ListTaskPair => add(T, N, RT) </readyTasks> 
   when ((RV +Int 1)<Int AT) andBool (N1==Int 0) andBool (A in L)[transition]


     rule <task> <tid> I </tid> <state> running => suspend </state>
           (<k> ChainTask(T); => . ...</k> ) <activatedTime> N1 </activatedTime>
         <accRes> .List </accRes> ... 
       </task>  
        <task> <tid> T </tid> <tPriority> N </tPriority> 
         <state> suspend => ready </state> <ext> true </ext> <taskEvents> M => clear(M) </taskEvents>
           </task> <br/>
  <runningTask> I => . </runningTask>
        <signal> .Set => SetItem(schedule) SetItem(alarmed) </signal>
        <alarm><aid> A </aid><aSysCounter> C</aSysCounter> <alarmTime>AT</alarmTime>... </alarm><br/>
        <sysCounter><cid> C </cid> <currentValue> RV=>(RV+Int 1)%Int (MAV +Int 1) </currentValue> <maxAllowedValue> MAV </maxAllowedValue>... </sysCounter>
 // <tcgMode> false </tcgMode> <br/>
   <alarmList> L </alarmList>
  <readyTasks> RT:ListTaskPair => add(T, N, RT) </readyTasks> 
   when ((RV +Int 1) ==Int AT) andBool (N1==Int 0) andBool (A in L)[transition]



        rule <task> <tid> I </tid> <state> running => suspend </state> 
           (<k> ChainTask(T); => . </k> ) 
         <accRes> .List </accRes> ... 
       </task>  
        <task> <tid> T </tid> 
         <state>  ready </state> <ext> false </ext>  <activationTime> N1 </activationTime> 
        <activatedTime> N2=>N2+Int 1 </activatedTime>...</task>
          <runningTask> I => . </runningTask>
        <signal> .Set => SetItem(schedule) </signal>
        <alarm> <aid> A </aid> <aSysCounter> C</aSysCounter> <alarmTime>AT</alarmTime> ...</alarm><br/>
        <sysCounter><cid> C </cid> <currentValue> RV=>(RV+Int 1)%Int (MAV +Int 1) </currentValue> <maxAllowedValue> MAV </maxAllowedValue> ...</sysCounter>
         <alarmList> L </alarmList>
  //<tcgMode> false </tcgMode> 
  
   when ((RV +Int 1)<Int AT) andBool (N2<=Int N1) andBool (A in L) [transition]



      rule <task> <tid> I </tid> <state> running => suspend </state> 
           (<k> ChainTask(T); => . </k> ) 
         <accRes> .List </accRes> ... 
       </task>  
        <task> <tid> T </tid> <tPriority> N </tPriority> 
         <state> ready </state> <activationTime> N1 </activationTime> 
        <activatedTime> N2=>N2+Int 1 </activatedTime> <ext> false </ext>  </task>
         
  <runningTask> I => . </runningTask>
        <signal> .Set => SetItem(alarmed) SetItem(schedule) </signal>
        <alarm> <aid> A </aid> <aSysCounter> C</aSysCounter> <alarmTime>AT</alarmTime> ...</alarm><br/>
        <sysCounter><cid> C </cid> <currentValue> RV=>(RV+Int 1)%Int (MAV +Int 1) </currentValue> <maxAllowedValue> MAV </maxAllowedValue>... </sysCounter>
 // <tcgMode> false </tcgMode> 
   <alarmList> L </alarmList>

   when ((RV +Int 1)==Int AT) andBool (N2<=Int N1) andBool (A in L)[transition]



  rule <task> <tid> I </tid> <state> running => suspend </state> <tPriority> N </tPriority> 
           (<k> ChainTask(I); => . </k> ) <activationTime> N1 </activationTime> 
        <activatedTime> N2=>N2+Int 1 </activatedTime> <ext> false </ext> 
         <accRes> .List </accRes> ... 
       </task>  
        
  <runningTask> I => . </runningTask>
        <signal> .Set </signal>
        <alarm> <aid> A </aid><aSysCounter> C</aSysCounter> <alarmTime>AT</alarmTime> </alarm><br/>
        <sysCounter><cid> C </cid> <currentValue> RV=>(RV+Int 1)%Int (MAV +Int 1) </currentValue> <maxAllowedValue> MAV </maxAllowedValue> </sysCounter>
  <br/>
   <alarmList> L </alarmList>
  //<readyTasks> RT:ListTaskPair => add(I, N, RT) </readyTasks> 
   when ((RV +Int 1)<Int AT) andBool (N2<=Int N1) andBool (A in L)[transition]



   rule <task> <tid> I </tid> <state> running => suspend </state> <tPriority> N </tPriority>
           (<k> ChainTask(I); => . </k> ) <activationTime> N1 </activationTime>
           <activatedTime> N2=>N2+Int 1 </activatedTime> <ext> false </ext> 
         <accRes> .List </accRes> ... 
       </task>  
        <runningTask> I => . </runningTask>
        <signal> .Set => SetItem(alarmed) </signal>
        <alarm><aid> A </aid> <aSysCounter> C</aSysCounter> <alarmTime>AT</alarmTime> </alarm><br/>
        <sysCounter><cid> C </cid> <currentValue> RV=>(RV+Int 1)%Int (MAV +Int 1) </currentValue> <maxAllowedValue> MAV </maxAllowedValue> </sysCounter>
         <alarmList> L </alarmList>
  <readyTasks> RT:ListTaskPair => add(I, N, RT) </readyTasks> 
   when ((RV +Int 1)==Int AT) andBool (N2<=Int N1) andBool (A in L)[transition]
 


   // if ChainTask() is not the last API in the task 
   rule <task> <tid> I </tid> <state> running </state> 
   	       (<k> ChainTask(T); A  </k> )  ... </task>	
	<runningTask> I => . </runningTask><br/>
        <signal> .Set => SetItem(stop) </signal> 
	(.Bag => <errorCell> Error(E_OS_UNDEF,I,ChainTask(T);,"ChainTask is not the last API!") </errorCell> )
	//<tcgMode> false </tcgMode> 
	when A =/=K . [transition]




   // invalid task id 
   rule <task> <tid> I </tid> <state> running </state> 
   	       <k> ChainTask(T); A </k> <apiData> ST </apiData> 
	     //  <historyK> (L => #if B andBool ST ==K . #then L ListItem(ChainTask(T);) #else L #fi) </historyK> 
   //	<accRes> ListItem(R) ... </accRes> ... 
   </task>	<br/>
        <signal> .Set => SetItem(stop) </signal> 
	//<tcgMode> B </tcgMode> 
	<types> M </types> 
        (.Bag => <errorCell> Error(E_OS_ID, I, ChainTask(T);, "Invalid task ID!") </errorCell> )
	when notBool (T in keys(M)) orBool (notBool((T |->task) in values(M))) [transition]

 


   /*@ Definition of the semantics of ActivateTask. 
   */     
     /*@API:       ActivateTask(TaskID) \\
       Parameter: TaskID\\
       Result:    The task<TaskID> is transferred from the suspend state into the ready state. \\
       Condition: Task<TaskID> is not the running task; task<TaskID> is not in the readyTask list.*/

    /*@ Similar with ChainTask, there are three conditions when activating a task. Besides, if the running task is non preemitived, scheduling 
    won't performed.

    */

   syntax Map ::= "clear" "(" Map ")" [function]
   rule clear(.Map) => .Map 
   rule clear((K |-> V) M) => (K |-> CLEAR) clear(M) 

   // activating a basic task 
   rule <task> <state> running </state> <schedule> FULL </schedule> <k> (ActivateTask(T);) => . ... </k> 
      
	       <tPriority> N' </tPriority> <apiData> ST </apiData> 
	       //<historyK> (L' =>  #if B andBool ST ==K . #then L' ListItem(ActivateTask(T);) #else L' #fi) </historyK> 
	       <accRes> .List </accRes> ... 

       </task>	<br/>
   	<task> <tid> T </tid> <state> suspend => ready </state> <tPriority> N </tPriority> 
	       <k> .K => AS </k> <apiData> AS </apiData> ... </task> 
        <signal> .Set => (#if N' <Int N #then SetItem(schedule) #else .Set #fi) </signal> 
        <sysCounter> <cid> C </cid> <currentValue> RV=>(RV+Int 1)%Int (MAV +Int 1) </currentValue> <maxAllowedValue> MAV </maxAllowedValue> ...</sysCounter>
        <alarmList> .List </alarmList>
	<readyTasks> L:ListTaskPair => add(T,N,L) </readyTasks> 
  [transition]

  
    rule <task> <state> running </state> <schedule> FULL </schedule> <k> (ActivateTask(T);) => . ... </k> 
	       <tPriority> N' </tPriority> <apiData> ST </apiData> ...
	     //  <accRes> .List </accRes> ... 
       </task>	<br/>
   	<task> <tid> T </tid> <state> suspend => ready </state> <tPriority> N </tPriority> 
	       <k> .K => AS </k> <apiData> AS </apiData> ... </task> 
        <signal> .Set => (#if N' <Int N #then SetItem(schedule) #else .Set #fi) </signal> 
	<readyTasks> L => add(T,N,L) </readyTasks> 
  [transition]
  
  
    rule <task> <state> running </state> <schedule> FULL </schedule> <k> (ActivateTask(T);) => . ... </k> 
	       <tPriority> N' </tPriority> <apiData> ST </apiData> 
	        ... 
       </task>	<br/>
   	<task> <tid> T </tid> <state> ready </state> <tPriority> N </tPriority> 
           <activationTime> N2 </activationTime> 
           <activatedTime> N1 => N1 +Int 1 </activatedTime>		   ... </task> 
      requires N2 >Int N1
  [transition]
  
  
  

    rule <task> <state> running </state> <schedule> FULL </schedule> <k> (ActivateTask(T);) => . ... </k> 
         <tPriority> N' </tPriority> <apiData> ST </apiData> 
         //<historyK> (L' =>  #if B andBool ST ==K . #then L' ListItem(ActivateTask(T);) #else L' #fi) </historyK> 
         <accRes> .List </accRes> ... 
       </task>  <br/>
    <task> <tid> T </tid> <state> suspend => ready </state> <tPriority> N </tPriority> 
         <k> .K => AS </k> <apiData> AS </apiData> ... </task> 
        <signal> .Set => (#if N' <Int N #then SetItem(schedule) #else .Set #fi) </signal> 
        <alarm> <aid> A </aid> <aSysCounter> C</aSysCounter> <alarmTime>AT</alarmTime>... </alarm><br/>
        <sysCounter> <cid> C </cid> <currentValue> RV=>(RV+Int 1)%Int (MAV +Int 1) </currentValue> <maxAllowedValue> MAV </maxAllowedValue> ...</sysCounter>
  <readyTasks> L:ListTaskPair => add(T,N,L) </readyTasks> 
  <alarmList> L' </alarmList> 
    when ((RV +Int 1)<Int AT) andBool (A in L')
  [transition]



     rule <task> <state> running </state> <schedule> FULL </schedule> <k> ActivateTask(T); => . ... </k> 
         <tPriority> N' </tPriority> <apiData> ST </apiData> 
        // <historyK> (L' =>  #if B andBool ST ==K . #then L' ListItem(ActivateTask(T);) #else L' #fi) </historyK> 
        <accRes> .List </accRes> ... 
       </task>  <br/>
    <task> <tid> T </tid> <state> suspend => ready </state> <tPriority> N </tPriority> 
         <k> .K => AS </k> <apiData> AS </apiData> <ext> false </ext> ... </task> 
        <signal> .Set => (#if N' <Int N #then SetItem(schedule) SetItem(alarmed) #else SetItem(alarmed) #fi) </signal> 
        <alarm><aid> A </aid> <aSysCounter> C</aSysCounter> <alarmTime>AT</alarmTime> </alarm><br/>
        <sysCounter> <cid> C </cid> <currentValue> RV=>(RV+Int 1)%Int (MAV +Int 1) </currentValue> <maxAllowedValue> MAV </maxAllowedValue> </sysCounter>
  <readyTasks> L:ListTaskPair => add(T,N,L) </readyTasks> 
  <alarmList> L' </alarmList>  
    when ((RV +Int 1)==Int AT) andBool (A in L')
  [transition]

     // activating an extended task, all events of that task must be cleared 
   rule  <task> <state> running </state> <k> ActivateTask(T); => . ... </k>  
         <tPriority> N' </tPriority> <apiData> ST </apiData> 
         <accRes> .List </accRes> ... 
       </task> 
    <task> <tid> T </tid> <state> suspend => ready </state> <tPriority> N </tPriority> 
         <k> .K => AS </k> <apiData> AS </apiData> <ext> true </ext>
         <taskEvents> M => clear(M) </taskEvents> ... </task> 
        <signal> .Set => (#if N' <Int N #then SetItem(schedule) #else .Set #fi) </signal> 
  //<readyTasks> L:ListTaskPair => add(T,N,L) </readyTasks>   
        <alarm> <aid> A </aid> <aSysCounter> C</aSysCounter> <alarmTime>AT</alarmTime> ...</alarm><br/>
        <sysCounter> <cid> C </cid> <currentValue> RV=>(RV+Int 1)%Int (MAV +Int 1) </currentValue> <maxAllowedValue> MAV </maxAllowedValue>... </sysCounter>
  <readyTasks> L:ListTaskPair => add(T,N,L) </readyTasks> 
  <alarmList> L' </alarmList>
    when ((RV +Int 1)<Int AT) andBool (A in L')[transition]

     rule <task> <state> running </state> <k> ActivateTask(T); => . ... </k>  
         <tPriority> N' </tPriority> <apiData> ST </apiData> 
         <accRes> .List </accRes> ... 
       </task> 
    <task> <tid> T </tid> <state> suspend => ready </state> <tPriority> N </tPriority> 
         <k> .K => AS </k> <apiData> AS </apiData> <ext> true </ext>
         <taskEvents> M => clear(M) </taskEvents> ... </task> 
        <signal> .Set => (#if N' <Int N #then SetItem(schedule) SetItem(alarmed) #else SetItem(alarmed) #fi) </signal> 

        <alarm> <aid> A </aid> <aSysCounter> C</aSysCounter> <alarmTime>AT</alarmTime>... </alarm><br/>
        <sysCounter> <cid> C </cid> <currentValue> RV=>(RV+Int 1)%Int (MAV +Int 1) </currentValue> <maxAllowedValue> MAV </maxAllowedValue> ...</sysCounter>
  <readyTasks> L:ListTaskPair => add(T,N,L) </readyTasks> 
  <alarmList> L' </alarmList> 
    when ((RV +Int 1) ==Int AT) andBool (A in L')[transition]

rule <task> <state> running </state> <k> ActivateTask(T); => . ... </k>  
         <tPriority> N' </tPriority> <apiData> ST </apiData> 
         <accRes> .List </accRes> ... 
       </task> 
    <task> <tid> T </tid> <state> suspend => ready </state> <tPriority> N </tPriority> 
         <k> .K => AS </k> <apiData> AS </apiData> <ext> true </ext>
         <taskEvents> M => clear(M) </taskEvents> ... </task> 
        <signal> .Set => SetItem(schedule)</signal>     
        <sysCounter> <cid> C </cid> <currentValue> RV=>(RV+Int 1)%Int (MAV +Int 1) </currentValue> <maxAllowedValue> MAV </maxAllowedValue> ...</sysCounter>
  <readyTasks> L:ListTaskPair => add(T,N,L) </readyTasks> 
   <alarmList> .List </alarmList>  
    [transition]

  /*@ The task active itsef.
  */
  rule <task> <tid> T </tid> <state> running </state> <k> ActivateTask(T); => . ... </k> 
           <activationTime> N1 </activationTime> 
          <activatedTime> N2=>N2+1 </activatedTime>
          <ext> false </ext>
        // <historyK> (L' =>  #if B andBool ST ==K . #then L' ListItem(ActivateTask(T);) #else L' #fi) </historyK> 
        <accRes> .List </accRes> ... 
       </task>  <br/>
       <signal> .Set </signal>
       // <signal> S:Set => (#if N' <Int N #then add(schedule, S) #else S #fi) </signal> 
        <alarm><aid> A </aid><aSysCounter> C</aSysCounter> <alarmTime>AT</alarmTime> </alarm><br/>
        <sysCounter> <cid> C </cid> <currentValue> RV=>(RV+Int 1)%Int (MAV +Int 1) </currentValue> <maxAllowedValue> MAV </maxAllowedValue> </sysCounter>
  //<readyTasks> L:ListTaskPair => add(T,N,L) </readyTasks> //<tcgMode> B </tcgMode> 
  <alarmList> L </alarmList>  
    when ((RV +Int 1)<Int AT) andBool (N2<=Int N1) andBool (A in L)
  [transition]


  rule <task> <tid> T </tid> <state> running </state> <k> ActivateTask(T); => . ... </k> 
        <activationTime> N1 </activationTime> 
          <activatedTime> N2=>N2+Int 1 </activatedTime> 
         <accRes> .List </accRes> ... 
       </task>  <br/>
    
       <signal> .Set => SetItem(alarmed) </signal> 
        <alarm><aid> A </aid> <aSysCounter> C</aSysCounter> <alarmTime>AT</alarmTime> </alarm><br/>
        <sysCounter> <cid> C </cid> <currentValue> RV=>(RV+Int 1)%Int (MAV +Int 1) </currentValue> <maxAllowedValue> MAV </maxAllowedValue> </sysCounter>
 // <tcgMode> B </tcgMode>   
  <alarmList> L </alarmList>
    when ((RV +Int 1) ==Int AT) andBool (N2<=Int N1) andBool (A in L)
  [transition]

  /*@ Active a ready task
  */
  rule <task> <state> running </state>  <k> ActivateTask(T); => . ... </k> 
         <tPriority> N' </tPriority> 
      
         <accRes> .List </accRes> ... 
       </task>  <br/>
    <task> <tid> T </tid> <state> ready </state> <ext> false </ext> 
         <activationTime> N1 </activationTime> 
          <activatedTime> N2=>N2+1 </activatedTime> ... </task> 
        <signal> .Set</signal> 
        <alarm><aid> A </aid> <aSysCounter> C</aSysCounter> <alarmTime>AT</alarmTime> ...</alarm><br/>
        <sysCounter> <cid> C </cid> <currentValue> RV=>(RV+Int 1)%Int (MAV +Int 1) </currentValue> <maxAllowedValue> MAV </maxAllowedValue> ...</sysCounter>
        <alarmList> L </alarmList>
    when ((RV +Int 1) <Int AT) andBool (N2<=Int N1) andBool (A in L)
  [transition]


   rule <task> <state> running </state>  <k> ActivateTask(T); => . ... </k> 
         <tPriority> N' </tPriority> 
      
         <accRes> .List </accRes> ... 
       </task>  <br/>
    <task> <tid> T </tid> <state> ready </state> <ext> false </ext>  <tPriority> N </tPriority> 
         <activationTime> N1 </activationTime> 
          <activatedTime> N2=>N2+Int 1 </activatedTime> ... </task> 
        <signal> .Set </signal> 
        <alarm><aid> A </aid> <aSysCounter> C</aSysCounter> <alarmTime>AT</alarmTime> ...</alarm><br/>
        <sysCounter> <cid> C </cid> <currentValue> RV=>(RV+Int 1)%Int (MAV +Int 1) </currentValue> <maxAllowedValue> MAV </maxAllowedValue> ...</sysCounter>
        <alarmList> L </alarmList>
    
    when ((RV +Int 1)==Int AT)&& N2<=Int N1
  [transition]

    /*@ The running task is non preemtived 
    */
       rule <task> <state> running </state> <schedule> NON </schedule> <k> ActivateTask(T); => . ... </k> 
       ...</task>  <br/>
        <signal> .Set</signal> 
        <task> <tid> T </tid> <state> suspend=>ready </state>  <accRes> .List </accRes> <tPriority> N </tPriority>  ... </task> 
        <alarm><aid> A </aid><aSysCounter> C</aSysCounter> <alarmTime>AT</alarmTime> ...</alarm><br/>
        <sysCounter> <cid> C </cid> <currentValue> RV=>(RV+Int 1)%Int (MAV +Int 1) </currentValue> <maxAllowedValue> MAV </maxAllowedValue>... </sysCounter>
        <readyTasks> L:ListTaskPair => add(T,N,L) </readyTasks>
        <alarmList> L' </alarmList>    
    when ((RV +Int 1)<Int AT) andBool (A in L')
  [transition]

          rule <task> <state> running </state> <schedule> NON </schedule> <k> ActivateTask(T); => . ... </k> 
       ...</task>  <br/>
        <signal> .Set=>SetItem(alarmed)</signal> 
        <task> <tid> T </tid> <state> suspend=>ready </state>  <accRes> .List </accRes> <tPriority> N </tPriority> ... </task> 
        <alarm><aid> A </aid><aSysCounter> C</aSysCounter> <alarmTime>AT</alarmTime>... </alarm><br/>
        <sysCounter> <cid> C </cid> <currentValue> RV=>(RV+Int 1)%Int (MAV +Int 1) </currentValue> <maxAllowedValue> MAV </maxAllowedValue>... </sysCounter>
        <alarmList> L' </alarmList>
        <readyTasks> L:ListTaskPair => add(T,N,L) </readyTasks>    
    when ((RV +Int 1) ==Int AT) andBool (A in L')
  [transition]



  /*@ Definition of the semantics of Schedule. 
   */     
    /*@API:       Schedule() \\
       Parameter: none\\
       Result:    If a task with higher-priority is ready, the current task is put into ready task and the internal resource of the task is released. The higher-priority task are executed in the order of priority.\\
       Condition: The running task is non preemptable.*/
      
	   rule <signal> .Set => SetItem(schedule) </signal> <schedule> NON </schedule>
       <task> <state> running  </state> 
              <accRes> .List </accRes>
              <k> Schedule();=> . ...</k>... </task>
			  
	      rule <signal> .Set  </signal> <schedule> FULL </schedule>
       <task> <state> running  </state> 
              <accRes> .List </accRes>
              <k> Schedule();=> . ...</k>... </task>

       rule <signal> .Set => SetItem(schedule) </signal> 
       <task> <schedule> NON </schedule>
              <state> running  </state> 
              <accRes> .List </accRes>
              <k> Schedule();=> . ...</k>... </task> <br/>
        <sysCounter> <cid> C </cid> <currentValue> RV=>(RV+Int 1)%Int (MAV +Int 1) </currentValue> <maxAllowedValue> MAV </maxAllowedValue> ...</sysCounter>
        <alarmList> .List </alarmList>[transition]

    rule <signal> .Set => SetItem(schedule) </signal> 
       <task> <schedule> NON </schedule>
              <state> running  </state> <accRes> .List </accRes>
              <k> Schedule();=> . </k>... </task> <br/>
       <alarm><aid> A </aid> <aSysCounter> C</aSysCounter> <alarmTime>N1</alarmTime> ...</alarm><br/>
        <sysCounter> <cid> C </cid> <currentValue> RV=>(RV+Int 1)%Int (MAV +Int 1) </currentValue> <maxAllowedValue> MAV </maxAllowedValue>... </sysCounter>
        <alarmList> L </alarmList>
       when((RV +Int 1) <Int (N1+Int RV)) andBool (A in L)[transition]

      rule <signal> .Set => SetItem(schedule) SetItem(alarmed) </signal> 
       <task> <schedule> NON </schedule>
              <state> running  </state> <accRes> .List </accRes>
              <k> Schedule();=> . </k>... </task> <br/>
       <alarm><aid> A </aid><aSysCounter> C</aSysCounter> <alarmTime>N1</alarmTime>... </alarm><br/>
        <sysCounter> <cid> C </cid> <currentValue> RV=>(RV+Int 1)%Int (MAV +Int 1) </currentValue> <maxAllowedValue> MAV </maxAllowedValue> ...</sysCounter>
        <alarmList> L </alarmList>
       when  ((RV +Int 1) ==Int (N1 +Int RV)) andBool (A in L)[transition]


   

endmodule 
