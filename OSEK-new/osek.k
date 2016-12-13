require "./osek-task.k" 
require "./osek-resource.k" 
require "./osek-event.k" 
require "./osek-scheduler.k" 
require "./osek-alarm.k"
require "./osek-imp.k" 

//require "./osek-counter.k"

// 161 rules


module OSEK 

  imports OSEK-INITIALIZATION 

 imports OSEK-SCHEDULING 
 imports OSEK-TASK 
 imports OSEK-RESOURCE
 imports OSEK-EVENT 
 imports OSEK-ALARM
 imports IMP-SEMANTICS 
  
 //rule val(<generatedTop>...<alarm>...<alarmTime> AT</alarmTime><actedTaskId>A </actedTaskId>...</alarm><sysCounter> ...<currentValue> RV </currentValue>...  </sysCounter> ...</generatedTop>, A) => RV when (AT==Int RV)



rule count(<generatedTop>...<OSEK>...<sysCounters><sysCounter>...<currentValue> C:Int </currentValue>...</sysCounter></sysCounters>...</OSEK>...</generatedTop>)
=>
 C:Int  

 rule states(<generatedTop>...<OSEK>...<tasks>...<task>...<tid>I</tid><state> S</state>...</task>...</tasks>...</OSEK>...</generatedTop>, I)
=>
 S
//rule API(<generatedTop>...<OSEK>...<tasks>...<task>...<tid>I</tid><k> WaitEvent(E);...</k>...</task>...</tasks>...</OSEK>...</generatedTop>, I)
//=>
 //E
//rule event(<generatedTop>...<OSEK>...<tasks>...<task>...<tid>I</tid><taskEvents> E|->SET</taskEvents>...</task>...</tasks>...</OSEK>...</generatedTop>, I)
//=>
 //E

 rule state(<generatedTop>...<OSEK>...<global>...<runningTask>I</runningTask> ...</global>...</OSEK>...</generatedTop>)=>I [structural]

/*rule <k> counterValue=> RV </k>
  <currentValue> RV </currentValue>*/

//rule B:Bag |=Ltl eq(A:Id, I:Int) => (val(B, A)%Int 10 ) ==Int I [ltl, anywhere]

rule B:Bag |=Ltl wait(E, T)=>true when (API(B, T)==K E) [ltl, anywhere]
 
rule B:Bag |=Ltl set(E, T)=>true when event(B, T)==K E [ltl, anywhere]
rule B:Bag |=Ltl countvalue(I)=>true  when (count(B) %Int 10 ==Int I) [ltl, anywhere]

rule B:Bag |=Ltl taskstate(I) =>true when state(B)==K I [ltl, anywhere]

rule B:Bag |=Ltl succession(S, I)=>true when states(B, I)==K S [ltl, anywhere]

//rule B:Bag |=Ltl eq(K1, I:Int) => true 
//when (val(B, K1)) ==Int I [anywhere]
  
//  imports OSEK-COUNTER



endmodule 
