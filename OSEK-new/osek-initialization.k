require "./osek-configuration.k" 
require "./osek-error.k" 

//40 rules


module OSEK-INITIALIZATION 


   imports OSEK-CONFIGURATION 
   imports OSEK-ERROR 

   syntax Type ::=  "task"
	             |    "int"
               |    "sysCounter"
               |    "alarm"
               |    "event"
               |    "resource"

   syntax String ::= "type2String" "(" Type ")" [function]

   rule type2String(resource) => "resource"
   rule type2String(event) => "event"
   rule type2String(task) => "task" 
   rule type2String(sysCounter) => "sysCounter"
   rule type2String(alarm) => "alarm"  

   //syntax Bool ::= K "in" List [function]
   rule K1:K in ListItem(K2:K) L:List => (K1 ==K K2) orBool (K1 in L) 
   rule K1:K in .List => false 


   syntax List ::= "#if" Bool "#then" List "#else" List "#fi" [function]

   rule #if true #then L:List #else _ #fi => L 
   rule #if false #then _ #else L:List #fi => L 

   /*@ Define a function add(), which can add a TaskPair to a list or add signals to a set. 
   Note that elements in a list are in order of priority. The situation of adding two signals at once is when an ActiveTask API is called, the alarm expires exactly. Since alarmed signal and schedule signal should be added.*/

   syntax ListTaskPair ::= "add" "(" Id "," Int "," ListTaskPair ")"  [function]

   rule add(I,N,.ListTaskPair) => (< I ; N > .ListTaskPair) [structural]
   rule add(I,N, (< I'; N' > L)) => ( < I; N >  < I'; N' > L) when N >Int N' [structural]
   rule add(I,N, (< I'; N' > L)) => (< I'; N' > add(I,N,L))  when (N <=Int N')  [structural] 
  
 
 /*  syntax Set ::= "add" "(" Signal "," Set ")" 
                 | "add" "(" Signal "," Signal "," Set ")" [function]*/
    
   
 /*  rule add(G:Signal, S:Set) => (SetItem(G:Signal) S:Set)  [structural]
   rule add(G:Signal, .Set) => (SetItem(G:Signal)) [structural]

   rule add(G:Signal, G1:Signal, S:Set) => (SetItem(G:Signal) SetItem(G1:Signal) S:Set)  [structural]
   rule add(G:Signal, G1:Signal, .Set) => (SetItem(G:Signal) SetItem(G1:Signal)) [structural]  */



  /*@ To process the declaration of resources. \\
      Result: A new resource is created in the configuration \\
      Condition: If Id I is not used/declared in the system, i.e., \$hasMapping(M,I) is false. If not, 
      an error occurs. 
   */ 

   rule S1:OSEKStmt S2:OSEKStmt => S1 ~> S2 [structural] 



    rule .K S:OSEKStmt => S [structural] 
    
   // added on Feb 19 



  


    rule <k> (RESOURCE I:Id { RESOURCEPROPERTY = RP; } ; => .) ...  </k> 
         <proId> _ => I </proId> 
         <types> M:Map => (I |-> resource) M  </types> 
         <signal> .Set </signal>
         <resources> RS (. => <resource> <rid> I </rid> 
                    <rPriority> 0 </rPriority>  
                    <rProperty> RP </rProperty> <rOwner> .List </rOwner>  </resource>
                    ) </resources>
         when notBool (I in keys(M))  [structural]


   // error when I already exists 
   /*rule <k> RESOURCE I:Id { RESOURCEPROPERTY = RP; } ; ...  </k> 
      <types> M:Map  </types> 
      <signal> .Set => SetItem(stop) </signal>
      (. => <errorCell> Error(E_OS_CONF, I, Id2String(I) +String " has been used as " +String type2String(M[I])) </errorCell>) 
      when (I in keys(M)) [structural] */

   syntax EventValue ::= "SET"
   	  	     | "CLEAR"   
   //syntax TaskValue ::="ACTIVE"

   /*@ The ACTION attribute defines which type of notification is used when the alarm expires. Three actions may be taken place. They are ACTIVE a task, SET an event and alarm CALLBACK.*/

   syntax Actions ::= "ACTIVATE"
                    |"SETEVENT"
                    |"CALLBACK"



   /*@
	To process the declaration of events. \\
	Result: a new event is created \\
	Condition: when I does not exist 
    */
   rule <k> (EVENT I:Id { MASK = MT ; } ;  => .) ...  </k> 
      <proId> _ => I </proId> 
      <events> EV (. =>  <event> <eid> I </eid> <eOwner> .List </eOwner> <maskType> MT </maskType> </event>)
      </events>  
      <types> M:Map => (I |-> event) M </types> 
      <signal> . </signal> 
      when notBool (I in keys(M)) [structural]

   // error when I already exists 
  /* rule <k> (EVENT I:Id { MASK = MT ; } ; => . ) ...  </k> 
      <types> M:Map  </types> 
      <signal> .Set => SetItem(stop) </signal>
      (. => <errorCell> Error(E_OS_CONF, I, Id2String(I) +String " has been used as " +String type2String(M[I])) </errorCell> )
       when (I in keys(M)) [structural]  */

   //@ Function \emph{wrap} is used to wrap the statements. The wrapped statements is of type \texttt{DeclStmt}, so that we can process each statement in the order how they are declared afterward. 

   syntax DeclStmt ::= "wrap" "(" TaskProStmts ")" 
                      | "wrap" "(" AlarmProStmts ")"
                      | "wrap" "(" AlarmProperties ")"  
                      | "wrap" "(" CounterProStmts ")" [function]


    rule wrap( .CounterProStmts) => .    [structural]

    /*@ \subsection{Configuration of counter defined in OSEK specification}
    The counter serves as a base for the ALARM mechanism. In OSEK specification, a counter contains three attributes which are MAXALLOWEDVALUE, TICKSPERBASE and MINICYCLE.\\
    
     \subsection{Configuration of counter in our implementation} 
    To process the declaration of counters. The MAXALLOWEDVALUE attribute defines the maximum allowed counter value. When the value of counter is the MAXALLOWEDVALUE at present, the counter value returns to 0 next time. The MINCYCLE attribute specifies the minimum allowed number of counter ticks for a cyclic alarm linked to the counter.\\
        Result: A sysCounter is created in the configuration.\\
        Conditon: If Id I is not used/declared in the system. */

  rule <k>(COUNTER I:Id {MAXALLOWEDVALUE=MAV;};=>.)...</k>
        <sysCounters> CT(.=><sysCounter><cid> I </cid><maxAllowedValue> MAV:Int </maxAllowedValue> <miniCycle> 0 </miniCycle> </sysCounter>)</sysCounters>
        <proId> I </proId>
        <types> M:Map (.Map=> I |-> sysCounter) </types>
        <signal> .Set </signal> 
        when notBool (I in keys(M))[structural] 
 
   rule <k> (COUNTER I:Id {S2:CounterProStmts};=>wrap(S2))...</k>
        (.=><sysCounter><cid> I </cid><maxAllowedValue> 0 </maxAllowedValue> <miniCycle> 0 </miniCycle><currentValue> 0 </currentValue>
        <cAlarm> .List </cAlarm> </sysCounter>)
        <proId> _=>I </proId>
        <types> M:Map (.Map => I |-> sysCounter) </types>
        <signal> . </signal> 
        when notBool (I in keys(M))
        [structural]

 /*  rule <k> (COUNTER I:Id {MAXALLOWEDVALUE=MAV;};)...</k>
        <types> M:Map </types>
        <signal> .Set=>SetItem(stop) </signal>
       // (. => <errorCell> Error(E_OS_CONF, I, Id2String(I) +String " already exists as " +String type2String(I)) </errorCell> )
    when (I in keys(M)) [structural]  */


    rule <k> wrap( MAXALLOWEDVALUE = MAV ;S2:CounterProStmts)=>wrap(S2:CounterProStmts)...</k>
         <proId> I:Id </proId>
         <sysCounters> <sysCounter> <cid> I </cid><maxAllowedValue> _=>MAV </maxAllowedValue> ... </sysCounter> </sysCounters>
         <signal> . </signal> 
         [structural]

    rule <k> wrap(MINICYCLE=MC;S2=>S2)...</k>
         <proId> I </proId>
          <miniCycle> MC:Int </miniCycle>

    /*@ \subsection{Configuration of alarm defined in OSEK specification}
    An ALARM may be used to asynchronously inform or activate a specific task. In OSEK specification, an alarm contains three attributes which are COUNTER, ACTION and AUTOSTART.\\
     \subsection{Configuration of alarm in implementation}
    To process the declaration of alarms. An ALARM may be used to asynchronously inform or activate a specific task. The COUNTER reference defines the counter assigned to this alarm. Only one counter has to be assigned to the alarm. Any alarm has to be assigned to a particular counter. The ACTION attribute has been introduced. The AUTOSTART attribute of type BOOLEAN defines if an alarm is started The SCHEDULE attribute defines the preemptability of the task. at system start-up or started by a task. If the alarm is autostarted, its alarmtime and cycletime are configured in its initial state. The value of cycletime depends on whether the alarm is cyclic. In case of single alarms, cycletime value shall be zero.\\
        Result: A new alarm is created in the configuration.\\
        Condition: If Id I is not used/declared in the system. */


    rule <k>(ALARM I:Id {P:AlarmProStmts};=>wrap(P))...</k>
         <types> M:Map (.Map=> I |-> alarm) </types>
         <proId> _=>I </proId>
        (.=><alarm><aid> I </aid>
        <aSysCounter> .K </aSysCounter>
        <alarmTime> 0 </alarmTime>
        <cycleTime> 0 </cycleTime>
        <autostart> false </autostart>
        <cyclicity> false </cyclicity>
        <action> .K </action>
    <actedTaskId> .K </actedTaskId>
    <actedEventId> .K </actedEventId>
    <actedAlarmId> .K </actedAlarmId>
    <actedType> .K </actedType>
       </alarm>)
     
    when notBool (I in keys (M)) [structural]


  /*  rule <k> (ALARM I:Id {P:AlarmProStmts};)...</k>
         //<proid> _ => I </proid>
         <types> M:Map </types>
         <signal> .Set=>SetItem(stop) </signal>
       //  (. => <errorCell> Error(E_OS_CONF, I, Id2String(I) +String " already exists as " +String type2String(I)) </errorCell> )
    when (I in keys(M)) [structural]*/

    rule wrap( .AlarmProStmts) => .    [structural]
    rule wrap( .AlarmProperties) => .    [structural]

    rule <k> wrap(COUNTER = N ; P:AlarmProStmts => P:AlarmProStmts) ... </k>
         <proId> I:Id </proId>
         <types> M </types>
         <alarm> <aid> I </aid> <aSysCounter> _ => N </aSysCounter>... </alarm>
         <sysCounter> <cid> N </cid> 
         <cAlarm> L:List (.List=>ListItem(I)) </cAlarm>
         ... </sysCounter>
          <signal> .Set </signal>
    when (N in keys(M)) [structural]

   /* rule <k> wrap(COUNTER = N ; P:AlarmProStmts )...</k>
         <signal> .Set => SetItem(stop) </signal>
         <types> M </types>
         (. => <errorCell> Error(E_OS_CONF,N,"sysCounter " +String Id2String(N) +String " does not exist!") </errorCell>)
         when notBool (N in keys(M)) orBool (N in keys(M)) andBool (notBool((N |->sysCounter) in values(M)))[structural] */

    /*@ When executing the ACTION statement, a new cell cotaining the information of ACTION statement is generated. */

    rule <k> wrap(ACTION = ACTIVATETASK {TASK=T:Id;}; P:AlarmProStmts)=>wrap(P:AlarmProStmts)...</k>
         <proId> I:Id </proId>      
          <aid> I:Id </aid>   
      <action> . =>ACTIVATE </action>
        <actedTaskId> .K=>T:Id </actedTaskId>
      <actedType> .K=>task </actedType>    
        <signal> . </signal>
    [structural]


   /* rule <k> wrap(ACTION = SETEVENT {TASK=T; EVENT=E;}; P:AlarmProStmts)=>wrap(P:AlarmProStmts)...</k>
         <proId> I </proId>
         <alarm> <aid> I </aid> <actionType><action> SETEVENT </action>
    <actedTaskId> T </actedTaskId>
    <actedEventId> E </actedEventId>
    <actedType> event </actedType> </actionType></alarm>*/
   

    /*@ Varible AUTOSTART is false means this alarm must be started by users through API setrelalarm or setabsalarm. */
         
    rule <k> wrap(AUTOSTART=false;)=>. ...</k>
        <proId> I </proId>

         <alarm> <aid> I </aid> <autostart> _=>false </autostart>... </alarm>
    /*@ Varible AUTOSTART is true means this alarm is started when starting the system. */

    rule <k> wrap(AUTOSTART=true {P1:AlarmProperties};)=> wrap(P1)...</k>
         <proId> I </proId>
         <alarm> 
          <aid> I </aid> 
         <autostart> _=>true </autostart> ...
          </alarm>
          <alarmList> L=>ListItem(I) L </alarmList>


    rule <k> wrap(ALARMTIME=AT;P1:AlarmProperties=>P1:AlarmProperties)... </k>
         <proId> I </proId>
         <alarm> <aid> I </aid> <autostart> true </autostart>
         <alarmTime> _=>AT:Int </alarmTime> ... </alarm>

    rule <k> wrap(CYCLETIME=CT;P1 => P1)... </k>
         <proId> I </proId>
       <alarm> <aid> I </aid> <cyclicity> _=>true </cyclicity>
         <cycleTime> _=>CT </cycleTime> ...
         </alarm>
      //   when CT!=0

    rule <k> wrap(CYCLETIME=CT;P1 => P1)... </k>
         <proId> I </proId>
         <alarm> <aid> I </aid>  <cyclicity> _=>false </cyclicity>
         <cycleTime> _=>CT:Int </cycleTime>...
         </alarm>
         when CT==0

  /*@ \subsection{Configuration of task defined in OSEK specification}
  Seven attributes are included in task. They are PRIORITY, SCHEDULE, ACTIVATION, AUTOSTART, RESOURCE, EVENT and MESSAGE. The MESSAGE reference is used to define a list of messages accessed by the task.\\
  \subsection{Configuration of task in implementation} 
  To process the task declaration. The priority of a task is defined by the value of the PRIORITY attribute. The larger the PRIORITY value is, the higher the priority is. The SCHEDULE attribute defines whether the task is preemptability. Same as alarm, the attribute AUTOSTART represents whether the task is started automatically when starting system or started by other tasks.\\
    Result: A new task is created when every property initialized according to the declarations \\
  Condition: when I does not exist in the current system 
   */

   rule  
      <proId> I' => I </proId> 
       <k> (TASK I:Id { S:TaskProStmts } ; => wrap(S)) ... </k>
       (. => <task> 
      	      		 <apiData> . </apiData> 
		       	 <state> suspend </state> <tid> I </tid> <br/> 
			 <tPriority> 0 </tPriority> <ext> false </ext> 
		       	 <auto> false </auto> <historyK> .List </historyK>  <br/> 
		       	 <accRes> .List </accRes> 
		       	 <k> . </k> 
              <activationTime> 0 </activationTime> 
                           <activatedTime> 0 </activatedTime>
                         <done> false </done> 
			 <waitEvents> .List </waitEvents> <br/> 
			 <taskEvents> .Map </taskEvents>	
			 <taskResources> .List </taskResources> 
			 <schedule> NON </schedule> 
		        </task>)
        
      <types> M:Map =>(I |-> task) M  </types> 
      <signal> .Set </signal> 
     when notBool (I in keys(M)) [structural]

   // error when I already exists
  /* rule <k> (TASK I:Id { A:TaskProStmts } ;) ... </k> 
      <types> M:Map</types> 
      <signal> .Set => add(stop, .Set) </signal> 
	//(. => <errorCell> Error(E_OS_CONF, I, Id2String(I) +String " already exists as " +String type2String(I)) </errorCell> )
    when (I in keys(M)) [structural]*/


   // to initialize apis of the task. Later it will support more complicated control statements 
 
    rule <task> <k> (TASK I:Id { ST:OSEKStmt } ; => .) ... </k> ...</task>
  	<task> <tid> I </tid> <apiData> _ => ST </apiData> ... </task> 
	<signal> .Set </signal> [structural] 

   // error when I is not a task 


    /*  rule <k> (TASK I:Id { ST:OSEKStmt } ; => .) ... </k> 
    <types> M:Map</types>
  <signal> .Set => SetItem(stop) </signal>
  (. => <errorCell> Error(E_OS_CONF, I, "Task " +String Id2String(I) +String " not exist!") </errorCell> )
      // when notBool (I in keys(M)) orBool ((I in keys(M)) andBool (notBool((I |->task) in values(M)) ))[structural]*/

   rule wrap(.TaskProStmts) => .    [structural]

   //@ The following rules are used to process each declaration statement for task 

   rule <task> <k> wrap(AUTOSTART = B ; A :TaskProStmts=> A:TaskProStmts) ... </k>... </task>
        <proId> I </proId> 
  <task> <tid> I </tid> <auto> _ => B </auto> ... </task> 
  <types> ... (I |-> task) ... </types> 
  <signal> .Set </signal> [structural]

   rule <task><k> wrap(PRIORITY = N ; A :TaskProStmts)=> wrap(A:TaskProStmts ) ... </k>...</task> 
        <proId> I </proId> 
  <task> <tid> I </tid> <tPriority> _ => N </tPriority> ... </task> 
  <types> ... (I |-> task) ... </types> 
        <signal> . </signal> [structural]

   /*@ Change the type of task from basic to exented when the first event declaration statement is processed. 
       The event is added to the taskEvents cell. It is mapped to a value SET in the cell. That is, the value 
       of this event owned by the task is unique to the task, as specified by the OSEK/VDX standard. 
       The task is added to the owner list of the event 
     */
   rule <task><k> wrap(EVENT = E ; A => A) ...  </k> ...</task>
        <proId> I:Id </proId> 
  <task> <tid> I </tid> <taskEvents> M1:Map => (E |-> CLEAR) M1 </taskEvents> 
  <ext> _=> true </ext> ... </task> 
  <event> <eid> E </eid> <eOwner> (L => L ListItem(I))  </eOwner> ... </event> 
  <types> ... (I |-> task) ... </types> 
  <signal> .Set </signal> [structural]

  /* rule <k> wrap(EVENT = E ; A :TaskProStmts=> A:TaskProStmts) ... </k> 
        <proId> I:Id </proId> 
  <task> <tid> I </tid> 
         <taskEvents> M => (E |-> CLEAR) M </taskEvents>  <ext> true </ext>  ... </task> 
  <event> <eid> E </eid> <eOwner> ( L => L ListItem(I) ) </eOwner> ... </event> 
  <signal> . </signal> [structural]*/

   // error when there is no such an event in the system 
  /* rule <k> wrap(EVENT = E ; A) ...  </k> 
  <signal> .Set => SetItem(stop) </signal>
  <types> M </types> 
  (. => <errorCell> Error(E_OS_CONF,E,"Event " +String Id2String(E) +String " does not exist!") </errorCell>)
  //when notBool $hasMapping(M,E) orBool ($hasMapping(M,E) andBool M(E) =/=K event) [structural]   */


   rule <task> <k> wrap(SCHEDULE = SCH ; A :TaskProStmts=> A:TaskProStmts) ...  </k> ...</task>
        <proId> I:Id </proId> 
  <task> <tid> I </tid> 
         <schedule> _ => SCH </schedule> ... </task> 
  <signal> .Set </signal> [structural]

  rule <task><k> wrap(ACTIVATION = N; A=>A)...</k>...</task>
       <proId> I </proId>
       <task> <tid> I </tid>
       <activationTime> _ => N </activationTime> ...</task>
      <signal> .Set </signal> [structural] 


   rule <task><k> int I; => . ... </k>...</task> 
    <env>  (.Map => I |-> 0) ... </env> 
  <types> (.Map => I |-> int) ... </types> [structrual]


   // the resource is added to the resource list of the task 
   // the task is added to the owner list of resource 

   rule <task><k> wrap(RESOURCE = R:Id ; A => A) ...  </k>...</task> 
        <proId> I </proId> 
  <task> <tid> I </tid> <taskResources> (L:List => L ListItem(R)) </taskResources>
         <tPriority> N </tPriority> ... </task> 
  <resource> <rid> R </rid> <rOwner> (L':List => L' ListItem(I)) </rOwner>
       <rPriority> N' => (#if N' <Int N #then N #else N' #fi)  </rPriority>  ... </resource> 
  <signal> .Set </signal> [structural]



   // error when there is no such a resource in the system 
   /*rule <k> wrap(RESOURCE = R ; A) ...  </k> 
  <signal> . => stop </signal>
  <types> M </types> 
  (. => <errorCell> Error(E_OS_CONF, R, "Resource " +String Id2String(R) +String " does not exist!") </errorCell>)
  requires notBool $hasMapping(M,R) orBool ($hasMapping(M,R) andBool M(R) =/=K resource) [structural]  */


   rule <task> <k> .K </k> <tid> initialTask </tid> ... </task> => . [structural]



endmodule 
