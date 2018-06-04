require "./osek-initialization.k" 
require "builtins/fol.k"

module OSEK-EVENT 
  imports OSEK-CONFIGURATION 
  imports OSEK-INITIALIZATION 
  imports FOL       



   syntax List ::= "remove" "(" K "," List ")" [function]
   rule remove(I,ListItem(I) L) => remove(I,L)
   rule remove(I,ListItem(I') L) => (ListItem(I') remove(I,L)) when I =/=K I' 
   rule remove(I,.) => . 


   /*@ Define the semantics of SetEvent(TaskId, Event)
       If the event is right the one which the task is waiting for, the task goes to ready state, and 
       sheduler is invoked. Otherwise, the event is just set, and the currently running state continue running. 
   */
   // 23 rules
   // waiting 
//DeclareEvent
rule <task><state>running</state><k>DeclareEvent(T);=>. ...</k>...</task>
<event><eid>T</eid>...</event>
<signal> .Set </signal>
<alarm> <aid> A </aid> <aSysCounter> C</aSysCounter> <alarmTime>AT</alarmTime> ...</alarm><br/>
<sysCounter> <cid> C </cid> <currentValue> RV=>(RV+Int 1)%Int (MAV +Int 1) </currentValue> <maxAllowedValue> MAV </maxAllowedValue> ...</sysCounter>


rule <task><state>running</state><k>DeclareEvent(T);=>. ...</k>...</task>
<event><eid>T</eid>...</event>
<signal> .Set=>SetItem(stop) </signal>
<alarm> <aid> A </aid> <aSysCounter> C</aSysCounter> <alarmTime>AT</alarmTime> ...</alarm><br/>
<sysCounter> <cid> C </cid> <currentValue> RV=>(RV+Int 1)%Int (MAV +Int 1) </currentValue> <maxAllowedValue> MAV </maxAllowedValue> ...</sysCounter>



  rule <task> <state> running </state> 
           <k> (SetEvent(I, E);)  => . ... </k> 
           <apiData> ST </apiData>... </task> <br/>
        <task> <tid> I </tid> <state> waiting => ready </state>
         <waitEvents> L => .List </waitEvents>
         <taskEvents> ... (E |-> (CLEAR => SET)) ...  </taskEvents>   
         <tPriority> N </tPriority> 
         ... 
         </task> <br/> 
   <readyTasks> L' => add(I,N,L') </readyTasks> 
   <signal> .Set => SetItem(schedule) </signal>
<sysCounter><cid> C </cid> <currentValue> RV=>(RV+Int 1)%Int (MAV +Int 1) </currentValue> <maxAllowedValue> MAV </maxAllowedValue> ...</sysCounter>
<alarmList> .List </alarmList>
    when (E in L)  [transition]


   rule <task> <state> running </state> 
   	       <k> (SetEvent(I, E);)  => . ... </k> 
           ...	</task> <br/>
        <task> <tid> I </tid> <state> waiting => ready </state>
	       <waitEvents> L => .List </waitEvents>
	       <taskEvents> ... (E |-> (CLEAR => SET)) ...  </taskEvents>   
	       <tPriority> N </tPriority> 
	       ... 
         </task> <br/> 
	 <readyTasks> L' => add(I,N,L') </readyTasks> 
	 <signal> .Set => SetItem(schedule) </signal>
  <alarm><aid> A1 </aid> <aSysCounter> C1</aSysCounter> <alarmTime>AT1</alarmTime> ...</alarm>
  <alarm><aid> A2</aid> <aSysCounter> C2</aSysCounter> <alarmTime>AT2</alarmTime> ...</alarm>
  <alarm><aid> A3 </aid> <aSysCounter> C3</aSysCounter> <alarmTime>AT3</alarmTime> ...</alarm>
  <br/>
<sysCounter><cid> C </cid> <currentValue> RV=>(RV+Int 1)%Int (MAV +Int 1) </currentValue> <maxAllowedValue> MAV </maxAllowedValue> ...</sysCounter>
<alarmList> L1 </alarmList>
    when (E in L) andBool ((RV +Int 1)<Int AT1) andBool ((RV +Int 1)<Int AT2)andBool ((RV +Int 1)<Int AT3)  [transition]


    rule <task> <state> running </state>
           <k> (SetEvent(I, E);)  => . ... </k>   ...
  </task> <br/>
        <task> <tid> I </tid> <state> waiting => ready </state>
         <waitEvents> L => .List </waitEvents>
         <taskEvents> ... (E |-> (CLEAR => SET)) ...  </taskEvents>   
         <tPriority> N </tPriority> 
         ... 
         </task> <br/> 
   <readyTasks> L' => add(I,N,L') </readyTasks> 
   <signal> .Set => SetItem(schedule) SetItem(alarmed) </signal>
  // <tcgMode> B </tcgMode> 
   <alarm><aid> A </aid> <aSysCounter> C</aSysCounter> <alarmTime>AT</alarmTime> ...</alarm><br/>
<sysCounter><cid> C </cid> <currentValue> RV=>(RV+Int 1)%Int (MAV +Int 1) </currentValue> <maxAllowedValue> MAV </maxAllowedValue> ...</sysCounter>
 <alarmList> L1 </alarmList>
    when (E in L) andBool ((RV +Int 1)==Int AT)  [transition]


   // not waiting 


  

rule <task> <state> running </state> 
           <k> (SetEvent(I, E);) => . ... </k> 
         ... 
  </task> <br/> 
        <task> <tid> I </tid> <waitEvents> L </waitEvents>
        <ext> true </ext>
         <taskEvents> ... (E |-> ( CLEAR=> SET)) ...  </taskEvents>   ... </task> 
         <signal> .Set </signal>
   <sysCounter><cid> C </cid> <currentValue> RV=>(RV+Int 1)%Int (MAV +Int 1) </currentValue> <maxAllowedValue> MAV </maxAllowedValue> ...</sysCounter>
 <alarmList> .List </alarmList>
   when notBool (E in L)  [transition]


   rule <task> <state> running </state> 
   	       <k> (SetEvent(I, E);) => . ... </k> 
      ... 
	</task> <br/> 
        <task> <tid> I </tid> <waitEvents> L </waitEvents>
        <ext> true </ext>
	       <taskEvents> ... (E |-> ( CLEAR=> SET)) ...  </taskEvents>   ... </task> 
	       <signal> .Set </signal>
      <alarm><aid> A1 </aid> <aSysCounter> C1</aSysCounter> <alarmTime>AT1</alarmTime> ...</alarm>
  <alarm><aid> A2</aid> <aSysCounter> C2</aSysCounter> <alarmTime>AT2</alarmTime> ...</alarm>
  <alarm><aid> A3 </aid> <aSysCounter> C3</aSysCounter> <alarmTime>AT3</alarmTime> ...</alarm>
  <br/>
<sysCounter><cid> C </cid> <currentValue> RV=>(RV+Int 1)%Int (MAV +Int 1) </currentValue> <maxAllowedValue> MAV </maxAllowedValue> ...</sysCounter>
<alarmList> L1 </alarmList>
    when notBool (E in L) andBool ((RV +Int 1)<Int AT1) andBool ((RV +Int 1)<Int AT2)andBool ((RV +Int 1)<Int AT3) [transition]


   rule <task> <state> running </state> 
           <k> (SetEvent(I, E);) => . ... </k> 
           //<apiData> ST </apiData> 
         //<historyK> (L1 => #if B andBool ST ==K . #then ListItem(SetEvent(I,E);) #else L1 #fi) </historyK> 
         ... 
  </task> <br/> 
        <task> <tid> I </tid> <waitEvents> L </waitEvents>
        <ext> true </ext>
         <taskEvents> ... (E |-> ( CLEAR=> SET)) ...  </taskEvents>   ... </task> 
         <signal> .Set=>SetItem(alarmed) </signal>
  // <tcgMode> B </tcgMode> 
    <alarm><aid> A </aid> <aSysCounter> C</aSysCounter> <alarmTime>AT</alarmTime>... </alarm><br/>
<sysCounter><cid> C </cid> <currentValue> RV=>(RV+Int 1)%Int (MAV +Int 1) </currentValue> <maxAllowedValue> MAV </maxAllowedValue> ...</sysCounter>
  <alarmList> L' </alarmList>
   when notBool (E in L) andBool ((RV +Int 1) ==Int AT) andBool (A in L') [transition]

    rule <task> <state> running </state> 
           <k> (SetEvent(I, E);) => . ... </k> 
         //  <apiData> ST </apiData> 
         //<historyK> (L1 => #if B andBool ST ==K . #then ListItem(SetEvent(I,E);) #else L1 #fi) </historyK> 
       ... 
  </task> <br/> 
        <task> <tid> I </tid> 
        <ext> true </ext>
        <waitEvents> L </waitEvents>
         <taskEvents> ... (E |-> SET) ...  </taskEvents>   ... </task> 
         <signal> .Set </signal>
    <alarm><aid> A </aid> <aSysCounter> C</aSysCounter> <alarmTime>AT</alarmTime> ...</alarm><br/>
<sysCounter><cid> C </cid> <currentValue> RV=>(RV+Int 1)%Int (MAV +Int 1) </currentValue> <maxAllowedValue> MAV </maxAllowedValue>... </sysCounter>
<alarmList> L' </alarmList>
   when notBool (E in L) andBool ((RV +Int 1)<Int AT) andBool (A in L') [transition]


   rule <task> <state> running </state> 
           <k> (SetEvent(I, E);) => . ... </k> 
           //<apiData> ST </apiData> 
        // <historyK> (L1 => #if B andBool ST ==K . #then ListItem(SetEvent(I,E);) #else L1 #fi) </historyK> 
          ... </task> <br/> 
        <task> <tid> I </tid> <ext> true </ext>
        <waitEvents> L </waitEvents>
         <taskEvents> ... (E |-> SET) ...  </taskEvents>   ... </task> 
         <signal> .Set=>SetItem(alarmed) </signal>
  // <tcgMode> B </tcgMode> 
    <alarm><aid> A </aid> <aSysCounter> C</aSysCounter> <alarmTime>AT</alarmTime>... </alarm><br/>
<sysCounter><cid> C </cid> <currentValue> RV=>(RV+Int 1)%Int (MAV +Int 1) </currentValue> <maxAllowedValue> MAV </maxAllowedValue> ...</sysCounter>
  <alarmList> L' </alarmList>
   when notBool (E in L) andBool ((RV +Int 1) ==Int AT) andBool (A in L') [transition] 

  rule <task> <state> running </state> 
           <k> (SetEvent(I, E);) => . ... </k> 
          ... </task> <br/> 
        <task> <tid> I </tid> <ext> true </ext>
        <waitEvents> L </waitEvents>
         <taskEvents> ... .Map=>(E |-> SET) ...  </taskEvents>   
	   ... </task>   
        when notBool (E in L)
		
rule <task> <state> running </state> 
           <k> (SetEvent(I, E);) => . ... </k> 
            <tid> I </tid> 
        <waitEvents> .List </waitEvents>
		<taskEvents> ... .Map=>(E |-> SET) ...  </taskEvents>  
          ... </task> 
        		  
      //  when notBool (E in L)
   
   rule <task> <state> running </state> 
           <k> (SetEvent(I, E);)  => . ... </k> 
           <apiData> ST </apiData>... </task> <br/>
        <task> <tid> I </tid> <state> waiting => ready </state>
         <waitEvents> L => .List </waitEvents>
         <taskEvents> ... (E |-> (CLEAR => SET)) ...  </taskEvents>   
         <tPriority> N </tPriority> 
         ... 
         </task> <br/> 
   <readyTasks> L' => add(I,N,L') </readyTasks> 
   <signal> .Set => SetItem(schedule) </signal>
    when (E in L)  [transition]
   
   rule <task> <state> running </state> 
   	       <k> (ClearEvent(E);)  => . ... </k>
	       <taskEvents> ... E |-> (_ => CLEAR) ...</taskEvents> ... </task> 
   
   rule <task> <state> running </state> <tid> T </tid> 
   	       <k> (SetEvent(I, E);) ... </k>  <apiData> ST </apiData> 
   	     //  <historyK> (L1 => #if B andBool ST ==K .  #then L1 ListItem(SetEvent(I,E);) #else L1 #fi) </historyK> ... 	       	       
	</task> <br/> 
	<task> <tid> I </tid> <ext> false </ext> ... </task> 
        <signal> .Set => SetItem(stop) </signal> <br/> 
	// <tcgMode> B </tcgMode> 
        (. => <errorCell> Error(E_OS_ACCESS, T, SetEvent(I,E);, "Task " +String Id2String(I) +String "is not an extended one") </errorCell>) [transition]

   rule <task> <state> running </state> <tid> T </tid> 
   	       <k> (SetEvent(I, E);) ... </k> <apiData> ST </apiData> 
   	      // <historyK> (L1 => #if B andBool ST ==K . #then L1 ListItem(SetEvent(I,E);) #else L1 #fi) </historyK> ...	       
	</task> <br/> 
	<task> <tid> I </tid> <ext> true </ext> <state> suspend </state> ... </task> 
        <signal> .Set => SetItem(stop) </signal> <br/> 
	// <tcgMode> B </tcgMode> 
        (. => <errorCell> Error(E_OS_STATE, T, SetEvent(I,E);,"Task " +String Id2String(I) +String " is suspended") </errorCell>)  [transition]

   /*@ Define the semantics of ClearEvent 
       If $I$ is an extended task, it can clear the events it owns. 
   */


 rule <task> <state> running </state> 
           <k> (ClearEvent(E);)  => . ... </k>  <apiData> ST </apiData> 
   //      <historyK> (L1 => #if B andBool ST ==K . #then L1 ListItem(ClearEvent(E);) #else L1 #fi) </historyK>          
         <taskEvents> ... E |-> (_ => CLEAR) ...</taskEvents> ... </task> 
          <signal> .Set </signal> 
<sysCounter><cid> C </cid> <currentValue> RV=>(RV+Int 1)%Int (MAV +Int 1) </currentValue> <maxAllowedValue> MAV </maxAllowedValue> ...</sysCounter>
<alarmList> .List </alarmList>
   [transition]

   rule <task> <state> running </state> 
   	       <k> (ClearEvent(E);)  => . ... </k>  <apiData> ST </apiData> 
	       //<historyK> (L1 => #if B andBool ST ==K . #then L1 ListItem(ClearEvent(E);) #else L1 #fi) </historyK> 	       
	       <taskEvents> ... E |-> (_ => CLEAR) ...</taskEvents> ... </task> 
	
        <signal> .Set </signal>  <alarm><aid> A1 </aid> <aSysCounter> C1</aSysCounter> <alarmTime>AT1</alarmTime> ...</alarm>
  <alarm><aid> A2</aid> <aSysCounter> C2</aSysCounter> <alarmTime>AT2</alarmTime> ...</alarm>
  <alarm><aid> A3 </aid> <aSysCounter> C3</aSysCounter> <alarmTime>AT3</alarmTime> ...</alarm>
  <br/>
<sysCounter><cid> C </cid> <currentValue> RV=>(RV+Int 1)%Int (MAV +Int 1) </currentValue> <maxAllowedValue> MAV </maxAllowedValue> ...</sysCounter>
<alarmList> L1 </alarmList>
    when  ((RV +Int 1)<Int AT1) andBool ((RV +Int 1)<Int AT2)andBool ((RV +Int 1)<Int AT3) [transition]

   rule <task> <state> running </state> 
           <k> (ClearEvent(E);)  => . ... </k>  <apiData> ST </apiData> 
        // <historyK> (L1 => #if B andBool ST ==K . #then L1 ListItem(ClearEvent(E);) #else L1 #fi) </historyK>  
          <taskEvents> ... E |-> (_ => CLEAR) ...</taskEvents> ... </task> 
  // <tcgMode> B </tcgMode> 
        <signal> .Set=>SetItem(alarmed) </signal> 
        <alarm><aid> A </aid> <aSysCounter> C</aSysCounter> <alarmTime>AT</alarmTime> ...</alarm><br/>
<sysCounter><cid> C </cid> <currentValue> RV=>(RV+Int 1)%Int (MAV +Int 1) </currentValue> <maxAllowedValue> MAV </maxAllowedValue>... </sysCounter>
<alarmList> L </alarmList>
   when ((RV +Int 1) ==Int AT) andBool (A in L)[transition]

   rule <task> <state> running </state> <ext> true </ext> 
   	       <k> (ClearEvent(E);) ...  </k> <apiData> ST </apiData> 
	      // <historyK> (L1 => #if B andBool ST ==K . #then L1 ListItem(ClearEvent(E);) #else L1 #fi) </historyK> 	       
	       <tid> I </tid> ... </task> <signal> .Set => SetItem(stop) </signal>
   	<event> <eid> E </eid> <eOwner> L:List </eOwner> ... </event>	
	(. => <errorCell>  Error(E_OS_UNDEF, I, ClearEvent(E);,"Event " +String Id2String(E) +String " is not owned by " +String Id2String(I)) </errorCell>)
	// <tcgMode> B </tcgMode> 
        when notBool (I in L) [transition]

//   rule (ClearEvent(.ListId);) K => K [structral]


   /*@ Define the semantics of GetEvent 

   */


   /*@ Define the semantics of WaitEvent 
       fix me
   */


   syntax APIStmt ::= "waitEvent" "(" ListId ")" [function]

   rule <task> <state> running </state>
   	       <k> WaitEvent(EL);  => waitEvent(EL) ... </k> <apiData> ST </apiData> 
	      // <historyK> (L1 => #if B andBool ST ==K . #then ListItem(WaitEvent(EL);) #else L1 #fi) </historyK> 	       
	 ... </task> 
	// <tcgMode> B </tcgMode> 
 	<signal> . </signal> [transition]

   rule <task> <k> waitEvent(E | EL) => waitEvent(EL) ...</k> 
   	       <taskEvents> ... (E |-> CLEAR) ... </taskEvents> 
	       <waitEvents> L => (ListItem(E) L) </waitEvents> 
         <accRes> .List </accRes>
	... </task>
  <signal> .Set </signal> [structral]       

   /*rule <task> //<state> running </state>  
   	       <k> waitEvent(E | EL) => . ... </k> 
   	       <taskEvents> ... (E |-> SET )... </taskEvents> 
	       <waitEvents> _ => . </waitEvents> 
         <accRes> .List </accRes>
	... </task> <signal> .Set </signal>  [structral]      */      

   // if E is cleared, move to waiting state, and invoke scheduler 

 rule <task> <k> waitEvent(E) => . ...</k> <state> running => waiting </state> 
           <taskEvents> ... (E |-> CLEAR) ... </taskEvents> 
         <waitEvents> L => (ListItem(E) L) </waitEvents> 
         <accRes> .List </accRes>... </task> 
         <signal> .Set => SetItem(schedule) </signal>
  <runningTask> _ => .K </runningTask>
  <alarmList>  .List </alarmList>
<sysCounter><cid> C </cid> <currentValue> RV=>(RV+Int 1)%Int (MAV +Int 1) </currentValue> <maxAllowedValue> MAV </maxAllowedValue> ...</sysCounter>
[transition]  

   rule <task> <k> waitEvent(E) => . ...</k> <state> running => waiting </state> 
   	       <taskEvents> ... (E |-> CLEAR) ... </taskEvents> 
	       <waitEvents> L => (ListItem(E) L) </waitEvents> 
         <accRes> .List </accRes>... </task> 
         <signal> .Set => SetItem(schedule) </signal>
	<runningTask> _ => .K </runningTask>
   <alarm><aid> A1 </aid> <aSysCounter> C1</aSysCounter> <alarmTime>AT1</alarmTime> ...</alarm>
  <alarm><aid> A2</aid> <aSysCounter> C2</aSysCounter> <alarmTime>AT2</alarmTime> ...</alarm>
  <alarm><aid> A3 </aid> <aSysCounter> C3</aSysCounter> <alarmTime>AT3</alarmTime> ...</alarm>
  <br/>
<sysCounter><cid> C </cid> <currentValue> RV=>(RV+Int 1)%Int (MAV +Int 1) </currentValue> <maxAllowedValue> MAV </maxAllowedValue> ...</sysCounter>
<alarmList> L1 </alarmList>
    when  ((RV +Int 1)<Int AT1) andBool ((RV +Int 1)<Int AT2)andBool ((RV +Int 1)<Int AT3) [transition]    

  rule <task> <k> (waitEvent(E) => .) ...</k> <state> running => waiting </state> 
           <taskEvents> ... (E |-> CLEAR) ... </taskEvents> 
         <waitEvents> L => (ListItem(E) L) </waitEvents> 
         <accRes> .List </accRes>
  ... </task> 
 <signal> .Set => SetItem(schedule) SetItem(alarmed) </signal>
  <runningTask> _ => .K </runningTask>
  <alarm><aid> A </aid>  <alarmTime>AT</alarmTime> ...</alarm><br/>
<sysCounter><cid> C </cid> <currentValue> RV=>(RV+Int 1)%Int (MAV +Int 1) </currentValue> 
<maxAllowedValue> MAV </maxAllowedValue> ...</sysCounter>
<alarmList> L' </alarmList>
when ((RV +Int 1) ==Int AT) andBool (A in L')[transition]    

   rule <task> <state> running </state> 
   	       <k> waitEvent(E) => . ... </k> 
   	       <taskEvents> ... (E |-> SET) ... </taskEvents> 
	       <waitEvents> _ => . </waitEvents> 
         <accRes> .List </accRes>
	... </task> <signal> .Set </signal>  
   <alarm><aid> A1 </aid> <aSysCounter> C1</aSysCounter> <alarmTime>AT1</alarmTime> ...</alarm>
  <alarm><aid> A2</aid> <aSysCounter> C2</aSysCounter> <alarmTime>AT2</alarmTime> ...</alarm>
  <alarm><aid> A3 </aid> <aSysCounter> C3</aSysCounter> <alarmTime>AT3</alarmTime> ...</alarm>
  <br/>
<sysCounter><cid> C </cid> <currentValue> RV=>(RV+Int 1)%Int (MAV +Int 1) </currentValue> <maxAllowedValue> MAV </maxAllowedValue> ...</sysCounter>
<alarmList> L1 </alarmList>
    when((RV +Int 1)<Int AT1) andBool ((RV +Int 1)<Int AT2)andBool ((RV +Int 1)<Int AT3)  [transition]               

   rule <task> <state> running </state> 
           <k> waitEvent(E) => . ... </k> 
           <taskEvents> ... (E |-> SET) ... </taskEvents> 
         <waitEvents> _ => . </waitEvents> 
         <accRes> .List </accRes>
  ... </task> <signal> .Set=>SetItem(alarmed) </signal>  
  <alarm><aid> A </aid> <aSysCounter> C</aSysCounter> <alarmTime>AT</alarmTime> ...</alarm><br/>
<sysCounter><cid> C </cid> <currentValue> RV=>(RV+Int 1)%Int (MAV +Int 1) </currentValue> <maxAllowedValue> MAV </maxAllowedValue> ...</sysCounter>
<alarmList> L' </alarmList>
when ((RV +Int 1) ==Int AT) andBool (A in L') [transition]  

  rule <task> <state> running => waiting </state> 
   	       <k> (waitEvent(.ListId)) => . ... </k> 
	... </task> <signal> .Set => SetItem(schedule) </signal> 
	<runningTask> _ => .K </runningTask>  
 <alarms>  <alarm><aid> A1 </aid> <aSysCounter> C1</aSysCounter> <alarmTime>AT1</alarmTime> ...</alarm>
  <alarm><aid> A2</aid> <aSysCounter> C2</aSysCounter> <alarmTime>AT2</alarmTime> ...</alarm>
  <alarm><aid> A3 </aid> <aSysCounter> C3</aSysCounter> <alarmTime>AT3</alarmTime> ...</alarm>
  </alarms><br/>
<sysCounter><cid> C </cid> <currentValue> RV=>(RV+Int 1)%Int (MAV +Int 1) </currentValue> <maxAllowedValue> MAV </maxAllowedValue> ...</sysCounter>
//<alarmList> L1 </alarmList>
    when  ((RV +Int 1)<Int AT1) andBool ((RV +Int 1)<Int AT2)andBool ((RV +Int 1)<Int AT3) [transition]

rule <task> <state> running => waiting </state> 
           <k> (waitEvent(.ListId)) => . ... </k> 
  ... </task> <signal> .Set => SetItem(schedule) SetItem(alarmed) </signal>
  <runningTask> _ => .K </runningTask>
  <alarm><aid> A </aid> <aSysCounter> C</aSysCounter> <alarmTime>AT</alarmTime> ...</alarm><br/>
<sysCounter><cid> C </cid> <currentValue> RV=>(RV+Int 1)%Int (MAV +Int 1) </currentValue> <maxAllowedValue> MAV </maxAllowedValue> ...</sysCounter>
<alarmList> L' </alarmList>
when ((RV +Int 1) ==Int AT) andBool (A in L') [transition]  

rule <task> <k> waitEvent(E) => . ...</k> <state> running => waiting </state> 
           <taskEvents> (E |-> CLEAR)_ </taskEvents> 
		 //  <accRes> .List </accRes>
         <waitEvents> .List=>ListItem(E)  </waitEvents> 
         ... </task> 
         <signal> .Set => SetItem(schedule) </signal>
  <runningTask> _ => .K </runningTask>


rule <task> <state> running => waiting </state> 
           <k> (waitEvent(.ListId)) => . ... </k> 
		   <accRes> .List </accRes>
  ... </task> <signal> .Set => SetItem(schedule) </signal>
  <runningTask> _ => .K </runningTask>

/*rule <k> GetEvent(T:Task, I:Id); => . ...</k>
     <event>...
	 <eid> E:Id </eid>
     <maskType> N </maskType>
	 <eOwner> ...ListItem(T)... </eOwner>
	 ...</event>
	 <env> ... I|-> (_=>N) ...</env>
*/
   // errors  if E is not owned by I 
   rule <task> <state> running </state> <tid> I </tid> 
   	       <k> waitEvent(E | EL)  ... </k> 
	       ... </task> <signal> .Set => SetItem(stop) </signal>
	<event> <eid> E </eid> <eOwner> L </eOwner> ... </event> 
	(. => <errorCell> Error(E_OS_UNDEF, I, WaitEvent(E|EL);,Id2String(E) +String "is not owned by " +String Id2String(I)) </errorCell>)
	when notBool (I in L)  [structral]

endmodule 

