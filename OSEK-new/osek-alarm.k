require "./osek-initialization.k" 
//require "./osek-scheduler.k"
require "./osek-imp.k" 

module OSEK-ALARM
  imports OSEK-CONFIGURATION 
  imports OSEK-INITIALIZATION
  imports IMP-SEMANTICS
  //imports OSEK-SCHEDULING   

  /*@ \section{alarm}
  In this section, we give the K semantic of some APIs about alarm. Besides, when alarmed signal arrives, transition of some states are also defined in this section.
  \par It's well known that OSEK operating system offers alarm mechanism, which is to say an alarm will expire when a predefined counter value is reached. Some actions such as activate tasks, set events or call an alarm callback routine are taken place when alarm expires. 
  \par In our model, counter and alarm have been abstracted. According to the OSEK standard, an attribute TICKSPERBASE, which specifies the number of timer's ticks required to reach a counter unit, is defined. Different counters correspond to different TICKSPERBASE. A particular counter, called system counter acts as a global counter in the system. In order to describe the system more intuitively, we just take system counter into consideration. All of the alarms employ system sounter in our model, which are consistent with the applications offered by our cooperate company.
  \par For an application of OSEK OS, we assume that the excutions of basic statements don't cost time, while the excution time of each API is one unit, i.e. plus one to the value of counter. After each API having been excuted, the value of counter should be compared with alarmTime to check whether the alarm expires. */



    
   /*@ This rule describe the condition when an alarmed signal arrives. Since the action of this alarm is ACTIVE, a task is going to be actived here. The informations about this task have been stored in cell actionType.
   \par Considerring a special condition, assume that task A just has called API ActiveTask(B) and the schedule signal reaches. At the same time, its corresponding alarm expires. The alarm asks to active task C. How to deal with schedule and alarm in this case? And which task can be scheduled.
   \par We don't get any information about whether it can be interrupted during the excution of API ActiveTask() and schedule a task according to OSEK specification. However, the specification specifies that the priority of interrupt is the highest. when an interrupt signal arrives, the system needs to pause anything it is doing now and to deal with the interrupt signal. Alarm is a kind of interrupt. Thus, we infer that the excution of API ActiveTask() and schedule a task is not atomic. 
   \par For that special condition, if alarmed and schedule signal reach at the same time, we handle alarmed signal at first. Since alarm asks to active task C, this task will be scheduled and put into readyTask list. Then the alarm complishes its action. Task A continues to excute its statements and Task B is to be scheduled. */

   /*@ Since nested interrupt is not allowed according to OSEK specification, we assume that dealing with actions of an alarm spends time while checking whether alarm expires is not done in this process.*/

   //23 rules

//DeclareAlarm
rule <task><state>running</state><k>DeclareAlarm(T);=>. ...</k>...</task>
<alarm><aid>T</aid>...</alarm>
<signal> .Set </signal>
<alarm> <aid> A </aid> <aSysCounter> C</aSysCounter> <alarmTime>AT</alarmTime> ...</alarm><br/>
<sysCounter> <cid> C </cid> <currentValue> RV=>(RV+Int 1)%Int (MAV +Int 1) </currentValue> <maxAllowedValue> MAV </maxAllowedValue> ...</sysCounter>

rule <task><state>running</state><k>DeclareAlarm(T);=>. ...</k>...</task>
<alarm><aid>T</aid>...</alarm>
<signal> .Set=>SetItem(stop) </signal>
<alarm> <aid> A </aid> <aSysCounter> C</aSysCounter> <alarmTime>AT</alarmTime> ...</alarm><br/>
<sysCounter> <cid> C </cid> <currentValue> RV=>(RV+Int 1)%Int (MAV +Int 1) </currentValue> <maxAllowedValue> MAV </maxAllowedValue> ...</sysCounter>

//GetAlarmBase
rule <task> <state> running </state> <k> (GetAlarmBase(R,I);)  => . ...</k> ...</task>
<alarm><aid>R</aid>...</alarm>
<return>1</return>





   rule <k> (TimeInterval=TI;=> .)...</k>
   <signal> .Set </signal>
   <alarm><aid> A </aid><aSysCounter> C</aSysCounter> <alarmTime>AT</alarmTime> ...</alarm><br/>
        <sysCounter> <cid> C </cid> <currentValue> RV=>(RV+Int TI)%Int (MAV +Int 1) </currentValue> <maxAllowedValue> MAV </maxAllowedValue>... </sysCounter>
        <alarmList> .List </alarmList>
        [transition]


   rule <k> (TimeInterval=TI;=> .)...</k>
   <signal> .Set </signal>
   <alarm><aid> A </aid><aSysCounter> C</aSysCounter> <alarmTime>AT</alarmTime> ...</alarm><br/>
        <sysCounter> <cid> C </cid> <currentValue> RV=>(RV+Int TI)%Int (MAV +Int 1) </currentValue> <maxAllowedValue> MAV </maxAllowedValue> ... </sysCounter>
        <alarmList> L </alarmList>  
    when (A in L) andBool ((RV +Int TI) <Int AT) [transition]

       rule <k> (TimeInterval=TI;=> .)...</k>
   <signal> .Set=>SetItem(alarmed) </signal>
   <alarm><aid> A </aid><aSysCounter> C</aSysCounter> <alarmTime>AT</alarmTime> ...</alarm><br/>
        <sysCounter> <cid> C </cid> <currentValue> RV=>(RV+Int TI)%Int (MAV +Int 1) </currentValue> <maxAllowedValue> MAV </maxAllowedValue> ... </sysCounter>
        <alarmList> L </alarmList>  
       when (A in L) andBool ((RV +Int TI) ==Int AT) [transition]

         rule <k> (TimeInterval=TI;=> TimeInterval=((TI +Int RV) -Int AT);)...</k>
   <signal> .Set=>SetItem(alarmed) </signal>
   <alarm><aid> A </aid><aSysCounter> C</aSysCounter> <alarmTime>AT</alarmTime> ...</alarm><br/>
        <sysCounter> <cid> C </cid> <currentValue> RV=> AT %Int (MAV +Int 1) </currentValue> <maxAllowedValue> MAV </maxAllowedValue> ... </sysCounter>
        <alarmList> L </alarmList>  
       when (A in L) andBool ((RV +Int TI) >Int AT) [transition]

      // rule <k>(TimeInterval = 0;=>.K)...</k>

   

   rule <signal> SetItem(alarmed) SetItem(schedule)  => SetItem(schedule) </signal> 
   <alarmList> L' </alarmList>
    <task>  
      //  <state> running </state>
         <tPriority> N' </tPriority> 
         
          ... </task> 
    <task> <tid> T </tid> <state> suspend => ready </state> <tPriority> N </tPriority> ... </task>    
  <readyTasks> L:ListTaskPair => add(T,N,L) </readyTasks>  <br/>  
  <alarm> <aid> I </aid> 
<alarmTime> AT </alarmTime>
<cycleTime> 0 </cycleTime>
<cyclicity> false </cyclicity>
    <action> ACTIVATE </action>
    <actedTaskId> T </actedTaskId>
    <actedType> task </actedType>
    <aSysCounter> C </aSysCounter>...</alarm><br/>
       <sysCounter> <cid> C </cid> <currentValue> RV=>(RV+Int 1)%Int (MAV +Int 1) </currentValue> <maxAllowedValue> MAV </maxAllowedValue>... </sysCounter>
   when (AT==Int RV) andBool (I in L')  [transition] 


   rule <signal> SetItem(alarmed) SetItem(schedule)  => SetItem(schedule) </signal> 
   <alarmList> L' </alarmList>
   
    <task> <tid> T </tid> <state> suspend => ready </state> <tPriority> N </tPriority> ... </task>    
  <readyTasks> L:ListTaskPair => add(T,N,L) </readyTasks>  <br/>  
  <alarm> <aid> I </aid> 
<alarmTime> AT=>(AT+Int CT) </alarmTime>
<cycleTime> CT </cycleTime>
<cyclicity> true </cyclicity>
    <action> ACTIVATE </action>
    <actedTaskId> T </actedTaskId>
    <actedType> task </actedType>
    <aSysCounter> C </aSysCounter>...</alarm><br/>
       <sysCounter> <cid> C </cid> <currentValue> RV=>(RV+Int 1)%Int (MAV +Int 1) </currentValue> <maxAllowedValue> MAV </maxAllowedValue>... </sysCounter>
   when (AT==Int RV) andBool (I in L')  [transition] 

       rule <signal> SetItem(alarmed)  => SetItem(schedule) </signal> 
    <alarmList> L' </alarmList>
    <task> <state> running </state> 
         <tPriority> N' </tPriority> 
          ... </task> 
    <task> <tid> T </tid> <state> suspend => ready </state> <tPriority> N </tPriority> ... </task>    
  <readyTasks> L:ListTaskPair => add(T,N,L) </readyTasks>  <br/>  
  <alarm> <aid> I </aid> 
<alarmTime> AT </alarmTime>
<cycleTime> 0 </cycleTime>
<cyclicity> false </cyclicity>
    <action> ACTIVATE </action>
    <actedTaskId> T </actedTaskId>
    <actedType> task </actedType>
    <aSysCounter> C </aSysCounter>...</alarm><br/>
       <sysCounter> <cid> C </cid> <currentValue> RV=>(RV+Int 1)%Int (MAV +Int 1) </currentValue> <maxAllowedValue> MAV </maxAllowedValue>... </sysCounter>
   when (AT==Int RV ) andBool (I in L') [transition] 


    rule <signal> SetItem(alarmed)  => SetItem(schedule) </signal> 
    <alarmList> L' </alarmList>
    <task> <state> running </state> 
         <tPriority> N' </tPriority> 
          ... </task> 
    <task> <tid> T </tid> <state> suspend => ready </state> <tPriority> N </tPriority> ... </task>    
  <readyTasks> L:ListTaskPair => add(T,N,L) </readyTasks>  <br/>  
  <alarm> <aid> I </aid> 
<alarmTime> AT=>(AT+Int CT) </alarmTime>
<cycleTime> CT </cycleTime>
<cyclicity> true </cyclicity>
    <action> ACTIVATE </action>
    <actedTaskId> T </actedTaskId>
    <actedType> task </actedType>
    <aSysCounter> C </aSysCounter>...</alarm><br/>
       <sysCounter> <cid> C </cid> <currentValue> RV=>(RV+Int 1)%Int (MAV +Int 1) </currentValue> <maxAllowedValue> MAV </maxAllowedValue>... </sysCounter>
   when (AT==Int RV ) andBool (I in L') 
   [transition] 


    /*   rule <signal> SetItem(alarmed)  =>  .Set </signal> 
    <alarmList> L' </alarmList>
    <task> <state> running </state> 
         <tPriority> N' </tPriority> 
          ... </task> 
    <task> <tid> T </tid> <state> suspend => ready </state> <tPriority> N </tPriority> ... </task>    
  <readyTasks> L:ListTaskPair => add(T,N,L) </readyTasks>  <br/>  
  <alarm> <aid> I </aid> 
<alarmTime> AT=>(AT+Int CT) </alarmTime>
<cycleTime> CT </cycleTime>
<cyclicity> true </cyclicity>
    <action> ACTIVATE </action>
    <actedTaskId> T </actedTaskId>
    <actedType> task </actedType>
    <aSysCounter> C </aSysCounter>...</alarm><br/>
       <sysCounter> <cid> C </cid> <currentValue> RV=>(RV+Int 1)%Int (MAV +Int 1) </currentValue> <maxAllowedValue> MAV </maxAllowedValue>... </sysCounter>
   when (AT==Int RV ) andBool (I in L') andBool (N'>=Int N)
   [transition] */


     /* rule <signal> SetItem(alarmed) S => add(schedule, S)</signal> 
    <task> <state> running </state>  
         //<accRes> .List </accRes>
          ... </task> 
    <task> <tid> T </tid> <state> waiting => ready </state> <tPriority> N </tPriority> 
    <waitEvents> L => . </waitEvents>
         <taskEvents> ... (E |-> (CLEAR => SET)) ...  </taskEvents>   
        //  <k> .K => AS </k> <apiData> AS </apiData> <ext> false </ext> ... 
      ... </task>    
  <readyTasks> L':ListTaskPair => add(T,N,L') </readyTasks> <tcgMode> B </tcgMode> <br/>  
  <alarm> <aid> I </aid> <alarmTime> N1 </alarmTime> 
    <action> SETEVENT </action>
    <actedTaskId> T </actedTaskId>
    <actedType> E </actedType>
    <aSysCounter> C </aSysCounter>...</alarm><br/>
       <sysCounter> <cid> C </cid> <currentValue> RV=>(RV+Int 1)%Int (MAV +Int 1) </currentValue> <maxAllowedValue> MAV </maxAllowedValue>... </sysCounter>
    when (E in L) [transition] 

          rule <signal> SetItem(alarmed) S=> S</signal> 
    <task> <state> running </state>  
         //<accRes> .List </accRes>
          ... </task> 
    <task> <tid> T </tid> <waitEvents> L </waitEvents>
         <taskEvents> ... (E |-> (CLEAR => SET)) ...  </taskEvents>   ... </task>   
  <alarm> <aid> I </aid> <alarmTime> N1 </alarmTime> 
    <action> SETEVENT </action>
    <actedTaskId> T </actedTaskId>
    <actedType> E </actedType>
    <aSysCounter> C </aSysCounter>...</alarm><br/>
       <sysCounter> <cid> C </cid> <currentValue> RV=>(RV+Int 1)%Int (MAV +Int 1) </currentValue> <maxAllowedValue> MAV </maxAllowedValue>... </sysCounter>
    when notBool (E in L) [transition] */

    
 /* rule <sysCounter> <maxAllowedValue> MAV </maxAllowedValue> <currentValue> RV=>(RV+1)%(MAV+1) </currentValue> </sysCounter>
       <alarm> <alarmTime> AT=>(AT-RV) </alarmTime> </alarm>
       when (MAV==RV)*/

   

 

	// remaining three errors!!!!!

  //@ The following rules define four APIs about alarm.
   /*@ API:       SetRelAlarm(AlarmID, increment, cycle) \\
       Parameter: AlarmID, increment (Relative value in counter), cycle (Cycle value in case of cyclic alarm. In case of single alarms, cycle shall be zero)\\
       Result:    The system service occupies the alarm<AlarmID> element. \\
       Condition: The alarm<AlarmID> must not already be in use.*/

  rule <task> <state> running </state> <k> SetRelAlarm(I, N1, N2); => . ...</k> ...</task>
      <alarm> <aid> I </aid> <alarmTime> _=>(N1+Int RV) %Int (MAV+Int 1) </alarmTime> <cycleTime> _=>N2 </cycleTime> <br/>
       <cyclicity> _=>true </cyclicity><aSysCounter> C </aSysCounter>...</alarm>
       <alarm> <aid> I' </aid> <alarmTime> N</alarmTime>...</alarm>
       <sysCounter> <cid> C </cid> <currentValue> RV=>(RV+Int 1)%Int (MAV +Int 1) </currentValue> <maxAllowedValue> MAV </maxAllowedValue> ...</sysCounter>
       <signal> .Set </signal>
       <alarmList> .List=>ListItem(I) </alarmList>
 when (N2=/=Int 0) andBool (N1=/=Int 0)  [transition]

	rule <task> <state> running </state> <k> SetRelAlarm(I, N1, N2); => . ...</k> ...</task>
      <alarm> <aid> I </aid> <alarmTime> _=>(N1+Int RV) %Int (MAV+Int 1) </alarmTime> <cycleTime> _=>N2 </cycleTime> <br/>
       <cyclicity> _=>true </cyclicity><aSysCounter> C </aSysCounter>...</alarm>
       <alarm> <aid> I' </aid> <alarmTime> N</alarmTime>...</alarm>

       <sysCounter> <cid> C </cid> <currentValue> RV=>(RV+Int 1)%Int (MAV +Int 1) </currentValue> <maxAllowedValue> MAV </maxAllowedValue> ...</sysCounter>
       <signal> .Set </signal>
       <alarmList> (L=>L ListItem(I)) </alarmList>
  when (N2=/=Int 0) andBool ((N1=/=Int 0) andBool (RV=/=Int N)) andBool (I' in L) [transition]

 /*@ The OSEK specification doesn't specify the cases that value of N1 is 0, thus in our definition of OIL, the alarm expires immediately in this condition. Note that the currenValue represents for value of counter after excuting this API, hence the alarmTime is N1 plus currentTime. */

  rule <task> <state> running </state> <k> SetRelAlarm(I, N1, N2); => . ...</k>  ...</task>
       <alarm> <aid> I </aid> <alarmTime> _=>N1+Int RV %Int (MAV+Int 1) </alarmTime> <cycleTime> _=>N2 </cycleTime> 
       <cyclicity> _=>true </cyclicity><aSysCounter> C </aSysCounter>...</alarm><br/>
       <alarm> <aid> I' </aid> <alarmTime> N</alarmTime>...</alarm>
       <sysCounter><cid> C </cid> <currentValue> RV=>(RV+Int 1)%Int (MAV +Int 1) </currentValue> <maxAllowedValue> MAV </maxAllowedValue> ...</sysCounter>
       <alarmList> (L=>L ListItem(I)) </alarmList>
       <signal> .Set=> SetItem(alarmed) </signal>
  when (N2=/=Int 0) andBool ((N1==Int 0 ) orBool (RV==Int N)) andBool (I' in L)[transition]

  rule <task> <state> running </state> <k> SetRelAlarm(I, N1, N2);=>. </k>  ...</task>
       <alarm> <aid> I </aid> <alarmTime> _=>N1+Int RV %Int (MAV+Int 1) </alarmTime> <cycleTime> _=>N2 </cycleTime> 
       <cyclicity> _=>false </cyclicity><aSysCounter> C </aSysCounter>...</alarm><br/>
       <sysCounter> <cid> C </cid><currentValue> RV=>(RV+Int 1)%Int (MAV +Int 1) </currentValue> <maxAllowedValue> MAV </maxAllowedValue>...</sysCounter>
       <signal> .Set </signal>
       <alarmList> (L=>L ListItem(I)) </alarmList>

  when (N2==Int 0) andBool (N1 >Int 0) [transition]

    rule <task> <state> running </state> <k> SetRelAlarm(I, N1, N2);=>. </k> </task>
       <alarm> <aid> I </aid> <alarmTime> _=>(N1+Int RV) %Int (MAV+Int 1) </alarmTime> <cycleTime> _=>N2 </cycleTime> 
       <cyclicity> _=>false </cyclicity><aSysCounter> C </aSysCounter>...</alarm><br/>

       <sysCounter> <cid> C </cid><currentValue> RV=>(RV+Int 1)%Int (MAV +Int 1) </currentValue> <maxAllowedValue> MAV </maxAllowedValue>...</sysCounter>
       <signal> .Set=> SetItem(alarmed) </signal>
       <alarmList> (L=>L ListItem(I))</alarmList>
  when (N2==Int 0) andBool (RV ==Int N1+Int RV) [transition]

 
   /*@ API:       SetAbsAlarm(AlarmID, start, cycle) \\
       Parameter: AlarmID, start (Absolute value in counter), cycle (Cycle value in case of cyclic alarm. In case of single alarms, cycle shall be zero)\\
       Result:    The system service occupies the alarm<AlarmID> element. \\
       Condition: The alarm<AlarmID> must not already be in use.*/


   // The parameter N3 stands for absolute alarmTime while N2 represents cycleTime in setrelalarm().
  rule <task> <state> running </state>
   <k> (SetAbsAlarm(I, N3, N2);)=>. ...</k> 
   ...
  </task>
       <alarm> <aid> I </aid> <alarmTime> N3 </alarmTime> <cycleTime> _=>N2 </cycleTime> 
       <cyclicity> _=>true </cyclicity><aSysCounter> C:Id </aSysCounter>...</alarm><br/>
       
       <sysCounter> <cid> C:Id </cid>
       <currentValue> RV=>(RV+Int 1)%Int (MAV +Int 1) </currentValue> 
       <maxAllowedValue> MAV </maxAllowedValue> ...</sysCounter>
       <signal> .Set </signal>
       <alarmList> (L=>L ListItem(I))</alarmList>
       
   when (N2=/=Int 0) andBool (RV<Int N3) [transition]



   rule <task> <state> running </state> <k> (SetAbsAlarm(I, N3, N2);)=>. ...</k>... </task>
       <alarm> <aid> I </aid> <alarmTime> _=>N3 </alarmTime> <cycleTime> _=>N2 </cycleTime> 
       <cyclicity> _=>true </cyclicity><aSysCounter> C </aSysCounter>...</alarm><br/>
       <sysCounter> <cid> C </cid><currentValue> RV=>(RV+Int 1)%Int (MAV +Int 1) </currentValue> <maxAllowedValue> MAV </maxAllowedValue>...</sysCounter>
        <signal> .Set=> SetItem(alarmed) </signal>
        <alarmList> (L=>L ListItem(I)) </alarmList>
  when (N2 =/=Int 0) andBool (RV==Int N3) [transition]



  rule <task> <state> running </state> <k> (SetAbsAlarm(I, N3, N2);)=>. ...</k> ... </task>
       <alarm> <aid> I </aid> <alarmTime> _=>N3 </alarmTime> <cycleTime> _=>N2 </cycleTime> 
       <cyclicity> _=>false </cyclicity><aSysCounter> C </aSysCounter>...</alarm><br/>
       <sysCounter> <cid> C </cid><currentValue> RV=>(RV+Int 1)%Int (MAV +Int 1) </currentValue> <maxAllowedValue> MAV </maxAllowedValue>...</sysCounter>
       <signal> .Set </signal>
       <alarmList> (L=>L ListItem(I)) </alarmList>
       when (N2==Int 0) andBool (RV<Int N3) [transition]
  
   rule <task> <state> running </state> <k> (SetAbsAlarm(I, N3, N2);)=>. ...</k>... </task>
       <alarm> <aid> I </aid> <alarmTime> _=>N3 </alarmTime> <cycleTime> _=>N2 </cycleTime> 
       <cyclicity> _=>false </cyclicity> <aSysCounter> C </aSysCounter>...</alarm><br/>
       <sysCounter> <cid> C </cid> <currentValue> RV=>(RV+Int 1)%Int (MAV +Int 1) </currentValue> <maxAllowedValue> MAV </maxAllowedValue>...</sysCounter>
       <signal> .Set=> SetItem(alarmed) </signal>
       <alarmList> (L=>L ListItem(I)) </alarmList>
       when (N2==Int 0) andBool(RV ==Int N3) [transition] 

  /* syntax List ::= "remove" "(" K "," List ")" [function]
   rule remove(I,ListItem(I) L) => remove(I,L)
   rule remove(I,ListItem(I') L) => (ListItem(I') remove(I,L)) when I =/=K I' 
   rule remove(I,.) => . */

  /*@ This rule is about cancelling an alarm. We didn't find the exact describtion of API CancelAlarm ()in OESK specification. Therefore, there can be two understandings about CancelAlarm. One is to delete the relation between alarm and its corresponding counter. In this case, this alarm cannot be used again as users have no access to specify a counter to an alarm. Another understanding, which we think is more reasonable is setting the value of alarmTime and cycleTime to an unreachable number, such as MAV+1. Thus, users can set this alarm again by some APIs such as SetRelAlarm() and SetAbsAlarm(). */ 


   /*@ API:       CancelAlarm(AlarmID) \\
       Parameter: AlarmID\\
       Result:    The value of alarmTime and cycleTime are set to MAV+1. \\
       Condition: The alarm<AlarmID> must already be in use.*/

  rule <task> <state> running </state> <k> (CancelAlarm(I);) => . ...</k> ...</task>
       <alarm> <aid> I </aid> <aSysCounter> C</aSysCounter> <alarmTime> _=>MAV+Int 1 </alarmTime> <cycleTime> _=>MAV+Int 1 </cycleTime>... </alarm><br/>
       <sysCounter> <cid> C </cid>  <currentValue> RV=>(RV+Int 1)%Int (MAV +Int 1) </currentValue> <maxAllowedValue> MAV </maxAllowedValue>... </sysCounter>
       <signal> .Set </signal>
       <alarmList> ListItem(I) L'=>L' </alarmList>
      // when (I in L)  

  //还差cancel的错误处理

  /*@  API:       GetAlarm(AlarmID, CounterValue) \\
       Parameter: AlarmID, CounterValue\\
       Result:    CounterValue which represents the relative value in counter before alarm<AlarmID> expires . \\
       Condition: The alarm<AlarmID> must already be in use.*/

  
  rule <task> <state> running </state> <k> (GetAlarm(I, N4);) => . ...</k> </task>
      //N4=>N3-RV
      <alarm> <aid> I </aid> <aSysCounter> C </aSysCounter> 
      <RemainAlarmTime> (_=>N4) |-> N3-Int (RV+Int 1)%Int (MAV+Int 1) </RemainAlarmTime>
        <alarmTime> N3 </alarmTime>
        <cycleTime> N2 </cycleTime>...</alarm><br/>
        <sysCounter> <cid> C </cid>  <currentValue> RV=>(RV+Int 1)%Int (MAV +Int 1) </currentValue> <maxAllowedValue> MAV </maxAllowedValue> ... </sysCounter>
        <signal> .Set </signal>
         when (RV< N3) [transition]

  rule <task> <state> running </state> <k> (GetAlarm(I, N4);) => . ...</k> </task>
      //N4=>N3-RV
      <alarm> <aid> I </aid> <aSysCounter> C </aSysCounter> 
      <RemainAlarmTime> _=>(N4 |-> N3-Int (RV+Int 1)%Int (MAV+Int 1)) </RemainAlarmTime>
        <alarmTime> N3 </alarmTime>
        <cycleTime> N2 </cycleTime>...</alarm><br/>
        <sysCounter> <cid> C </cid>  <currentValue> RV=>(RV+Int 1)%Int (MAV +Int 1) </currentValue> <maxAllowedValue> MAV </maxAllowedValue>... </sysCounter>
        <signal> .Set=> SetItem(alarmed) </signal>
         when  (RV == N3) [transition]
        

       

  endmodule

