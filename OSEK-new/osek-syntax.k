/*
 This file defines the syntax of our input language of OSEK/VDX. 
   Right now, it only contains basic information of resources, tasks. 
 */

/*@ \section{Basic Syntax of OIL}
 This module declares the syntax of a simple imperative programming language. 
   Part of the definition is from the K tutorial. 
   It also declares the syntax of OIL (OSEK Implementation language)
 */
require "builtins/model-checker.k" 

module OSEK-SYNTAX 
//imports LTL-HOOKS
imports MODEL-CHECKER-HOOKS
  
  // IMP 
  syntax AExp  ::= Int | Id
                 | "++"AExp "%" AExp
                 | AExp "/" AExp              [left, strict]
                 | AExp "*" AExp              [left, strict]
                 | AExp "%" AExp              [left, strict]
                 > AExp "+" AExp              [left, strict]
                 > AExp "-" AExp              [left, strict]                 
                 | "(" AExp ")"               [bracket]
  syntax BExp  ::= Bool
                 | AExp "<=" AExp             [seqstrict, latex({#1}\leq{#2})]
                 | "!" BExp                   [strict]
                 | AExp "<" AExp             [seqstrict, latex({#1}\leq{#2})]
		             | AExp "==" AExp             [seqstrict]
		             | AExp "!=" AExp             [seqstrict]
                 > BExp "&&" BExp             [left, strict(1)]
                 | "(" BExp ")"               [bracket]
   
   // API Statement 
   syntax ListId ::= List{Id, "|"}

  /* syntax APIStmt ::= "GetResource" "(" Id ")"  ";"
   	      	  | "ReleaseResource" "(" Id ")" ";"
            	  | "ActivateTask" "(" Id ")" ";"
              	  | "ClearEvent" "(" Id ")" ";"
              	  | "SetEvent" "(" Id "," Id ")" ";"
	      	  | "WaitEvent" "(" ListId ")" ";"
              	  | "ChainTask" "(" Id ")" ";"
              	  | "TerminateTask" "(" ")" ";" */

  syntax APIStmt ::=  "ActivateTask" "(" Id ")" ";"
                  | "ChainTask" "(" Id ")" ";"
                  | "TerminateTask" "(" ")" ";"
                  | "SetRelAlarm" "(" Id "," Int "," Int ")" ";"
                  |  "SetAbsAlarm" "(" Id "," Int "," Int ")" ";"
                  |  "GetAlarm" "(" Id "," Int ")" ";"
                  |  "CancelAlarm" "(" Id ")" ";"
                  |  "Schedule" "(" ")" ";"
                  | "ClearEvent" "(" Id ")" ";"
                  | "SetEvent" "(" Id "," Id ")" ";"
                  | "WaitEvent" "(" ListId ")" ";"
                  | "GetResource" "(" Id ")"  ";"
                  | "ReleaseResource" "(" Id ")" ";"
				  | "DeclareTask" "(" Id ")" ";"
				  | "DeclareEvent" "(" Id ")" ";"
				  | "DeclareResource" "(" Id ")" ";"
				  | "DeclareAlarm" "(" Id ")" ";"
				  | "GetTaskID" "("Id")"";"
				  | "GetTaskState""("Id","Id")"";"
				  | "GetAlarmBase" "(" Id "," Id ")" ";"

  syntax Stmt  ::= Block
                 | Id "=" AExp ";"            [strict(2)]
		 | "int" Id ";"
                 | "if" "(" BExp ")" Block "else" Block [strict(1)]
		 | "if" "(" BExp ")" Block
                 | "while" "(" BExp ")" Block
                 | "TimeInterval" "=" AExp ";"


    //syntax Ids ::= List{Id,","}

  syntax Block ::= "{" "}"
                 | "{" OSEKStmt "}"


   //@ The syntax of configuration of OSEK/VDX 
   //@ Two possible values can be assigned to varible SchedValue. The value FULL corresponds to a preemptable task, while the value NON to a non- preemptable task.

   syntax SchedValue ::= "NON"
   	  	     | "FULL"

   syntax ResProperty ::= "STANDARD"
   	  	      | "LINKEDRESOURCE"
		      | "INTERNAL"  


   //
   /*syntax DeclStmt ::= "RESOURCE" Id "{" ResProStmt "}" ";"
		   | "EVENT" Id "{" EventProStmt "}" ";" 
   	  	   | "TASK" Id "{" TaskProStmts "}" ";" 	*/

    syntax DeclStmt ::= "TASK" Id "{" TaskProStmts "}" ";"  	
                       |"ALARM" Id "{" AlarmProStmts "}" ";"
                       | "COUNTER" Id "{" CounterProStmts "}" ";"
                       | "EVENT" Id "{" EventProStmt "}" ";"
                       | "RESOURCE" Id "{" ResProStmt "}" ";"

    syntax AlarmProStmt ::="COUNTER" "=" Id ";" 
                          | "ACTION" "=" Action ";"
                          | "AUTOSTART" "=" "false" ";"
                          | "AUTOSTART" "=" "true" "{" AlarmProperties "}" ";"

    syntax AlarmProStmts ::= List{AlarmProStmt,""}


                          
    syntax Action ::= "ACTIVATETASK" "{" "TASK" "=" Id ";" "}"
                    | "SETEVENT" "{" "TASK" "=" Id ";" "EVENT" "=" Id ";" "}"

    syntax AlarmProperty ::= "ALARMTIME" "=" Int ";"
                            |"CYCLETIME" "=" Int ";"
    syntax AlarmProperties ::= List{AlarmProperty,""}

    syntax CounterProStmt ::= "MAXALLOWEDVALUE" "=" Int ";"
                              |"MINICYCLE" "=" Int ";"
    syntax CounterProStmts ::= List{CounterProStmt,""} 


  syntax TaskState ::= "running"
         | "suspend"
       | "ready"
       | "waiting"
    
   syntax ResProStmt ::=  "RESOURCEPROPERTY" "=" ResProperty ";"

   syntax TaskProStmt ::= "PRIORITY" "=" Int ";" 
   	  	       |   "AUTOSTART"  "=" Bool ";"
		       |   "SCHEDULE" "=" SchedValue ";" 
           |"EVENT"   "=" Id ";" 
           | "ACTIVATION" "=" Int ";"
           | "RESOURCE" "=" Id ";"

   syntax TaskProStmts ::= List{TaskProStmt,""} 

   syntax MaskType ::= "AUTO" 
   	  	   | Int 

   syntax EventProStmt ::=  "MASK" "=" MaskType ";" 

		  
//
	//    syntax BodyStmt ::= APIStmt 
//    	   	    | Stmt 
//		    | BodyStmt BodyStmt [right]

   //syntax APIs ::= List{APIStmt, ""}

   // Stmt is extend to support definition of tasks 

   syntax DefStmt ::= "TASK" Id "{" OSEKStmt "}" ";" 


   syntax OSEKStmt ::= DefStmt 
   	  	   | DeclStmt
		   | Stmt 
		   | APIStmt 
		   > OSEKStmt OSEKStmt [right]

   syntax OSEK ::= OSEKStmt | LtlFormula

  // syntax OSEK ::= LtlFormula
syntax Prop ::= "eq" "(" Id "," Int ")"
              | "countvalue" "(" Int ")"
              | "taskstate" "(" Id ")"
              | "succession" "(" TaskState "," Id ")"
              | "wait" "(" Id "," Id ")"
              | "set" "(" Id "," Id ")"




//syntax Int ::= "val" "(" Bag "," Id ")"  [function]
 syntax Int ::= "count" "(" Bag ")"     [function]
 syntax Id ::= "state" "(" Bag ")" [function]
 syntax Id ::= "API" "(" Bag "," Id ")" [function]
 syntax Id ::= "event" "(" Bag "," Id ")" [function]
 syntax TaskState::="states" "(" Bag "," Id ")" [function]
 //syntax KItem


//rule val(<sysCounters> <sysCounter> ...<currentValue> RV </currentValue>...  </sysCounter>  </sysCounters> , counterValue) => RV

//rule <k> counterValue=> RV </k>
  //<currentValue> RV </currentValue>

//rule B:Bag |=Ltl eq(counterValue, I:Int) => true when val(B, counterValue)==K I [anywhere]*/

endmodule 

