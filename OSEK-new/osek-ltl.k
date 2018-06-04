require "osek.k"
require "builtins/model-checker.k" 
module OSEK-LTL
imports OSEK
imports LTL-HOOKS
imports MODEL-CHECKER-HOOKS


syntax Id::= "Adapt_Event" [token]
           | "EMS_Adapt_Task_10ms" [token]
syntax Prop ::= "eq" "(" Id "," Int ")"
              | "countvalue" "(" Int ")"
              | "taskstate" "(" Id ")"
              | "succession" "(" TaskState "," Id ")"
              | "wait" "(" Id "," Id ")"
              | "set" "(" Id "," Id ")"
			  | "countRunning""("TaskState "," Int")"
			 




//syntax Int ::= "val" "(" Bag "," Id ")"  [function]
 syntax Int ::= "count" "(" Bag ")"     [function]
 syntax Id ::= "state" "(" Bag ")" [function]
 syntax Id ::= "API" "(" Bag "," Id ")" [function]
 syntax Id ::= "event" "(" Bag "," Id ")" [function]
 syntax TaskState::="states" "(" Bag "," Id ")" [function]
 syntax Int ::=  "priority" "(" Bag "," TaskState ")" [function]
 
 rule count(<generatedTop>...<runningTask> .K </runningTask> ...</generatedTop>)=>0
  rule count(<generatedTop>...<runningTask> I:Id </runningTask> ...</generatedTop>)=>1
 //rule val(<generatedTop>...<alarm>...<alarmTime> AT</alarmTime><actedTaskId>A </actedTaskId>...</alarm><sysCounter> ...<currentValue> RV </currentValue>...  </sysCounter> ...</generatedTop>, A) => RV when (AT==Int RV)



//rule count(<generatedTop>...<OSEK>...<sysCounters><sysCounter>...<currentValue> C:Int </currentValue>...</sysCounter></sysCounters>...</OSEK>...</generatedTop>)
//=>
// C:Int  

 rule states(<generatedTop>...<OSEK>...<tasks>...<task>...<tid>I</tid><state> S</state>...</task>...</tasks>...</OSEK>...</generatedTop>, I)
=>
 S

rule API(<generatedTop>...<OSEK>...<tasks>...<task>...<tid>I</tid><k> WaitEvent(E);...</k>...</task>...</tasks>...</OSEK>...</generatedTop>, I)
=>
 E
rule event(<generatedTop>...<OSEK>...<tasks>...<task>...<tid>I</tid><taskEvents> E|->SET</taskEvents>...</task>...</tasks>...</OSEK>...</generatedTop>, I)
=>
 E

 rule state(<generatedTop>...<OSEK>...<global>...<runningTask>I</runningTask> ...</global>...</OSEK>...</generatedTop>)=>I [structural]

//rule  priority(<generatedTop>...<OSEK>...<global>...<runningTask>I</runningTask> ...<task> ... <tid>I</tid><tPriority> N </tPriority> </task></global>...</OSEK>...</generatedTop>, running)=>N

/*rule <k> counterValue=> RV </k>
  <currentValue> RV </currentValue>*/

//rule B:Bag |=Ltl eq(A:Id, I:Int) => (val(B, A)%Int 10 ) ==Int I [ltl, anywhere]

rule B:Bag |=Ltl wait(E, T)=>true when (API(B, T)==K E) [ltl, anywhere]
 
rule B:Bag |=Ltl set(E, T)=>true when event(B, T)==K E [ltl, anywhere]
//rule B:Bag |=Ltl countvalue(I)=>true  when (count(B) %Int 10 ==Int I) [ltl, anywhere]

rule B:Bag |=Ltl taskstate(I) =>true when state(B)==K I [ltl, anywhere]

rule B:Bag |=Ltl succession(S, I)=>true when states(B, I)==K S [ltl, anywhere]

rule B:Bag |=Ltl countRunning(running, I)=>true when count(B) ==Int I [ltl, anywhere]
//rule B:Bag |=Ltl eq(K1, I:Int) => true 
//when (val(B, K1)) ==Int I [anywhere]
  
//  imports OSEK-COUNTER


endmodule