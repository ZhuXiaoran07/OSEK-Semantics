require "./osek-initialization.k" 
require "./osek-imp.k" 



module OSEK-TASK
  imports OSEK-CONFIGURATION 
  imports OSEK-INITIALIZATION  
  imports IMP-SEMANTICS   
  
  //DisableAllInterrupts

  rule <task> <state> running </state> 
           <k> (DisableAllInterrupts();)  => . ... </k> 
		   </task>
		  <sysCounter><cid> C </cid> <currentValue> RV=>(RV+Int 1)%Int (MAV +Int 1) </currentValue>  ...</sysCounter> 
		  <signal> .Set => SetItem(disableInterrupt) </signal>

    rule <task> <state> running </state> 
           <k> (EnableAllInterrupts();)  => . ... </k> 
		   <sysCounter><cid> C </cid> <currentValue> RV=>(RV+Int 1)%Int (MAV +Int 1) </currentValue>  ...</sysCounter> 
		    <signal> SetItem(disableInterrupt)=>.Set </signal>
		   
		   
	rule <task> <state> running </state> 
           <k> (ResumeAllInterrupts();)  => . ... </k> 
		   <sysCounter><cid> C </cid> <currentValue> RV=>(RV+Int 1)%Int (MAV +Int 1) </currentValue>  ...</sysCounter> 
		   <signal> SetItem(disableInterrupt)=>.Set </signal>
		   <susAllCount>N=>N-Int 1</susAllCount>
   
	rule <task> <state> running </state> 
           <k> (SuspendAllInterrupts();)  => . ... </k> 
		   <sysCounter><cid> C </cid> <currentValue> RV=>(RV+Int 1)%Int (MAV +Int 1) </currentValue>  ...</sysCounter> 
		    <signal> .Set => SetItem(disableInterrupt) </signal>
		     <susAllCount>N=>N+Int 1</susAllCount>
		
		
    rule <task> <state> running </state> 
           <k> (ResumeOSInterrupts();)  => . ... </k> 
		   <sysCounter><cid> C </cid> <currentValue> RV=>(RV+Int 1)%Int (MAV +Int 1) </currentValue>  ...</sysCounter> 
		    <susOSCount>N=>N-Int 1</susOSCount>
		   
    rule <task> <state> running </state> 
           <k> (SuspendOSInterrupts();)  => . ... </k> 
		   <sysCounter><cid> C </cid> <currentValue> RV=>(RV+Int 1)%Int (MAV +Int 1) </currentValue>  ...</sysCounter> 
		    <susOSCount>N=>N+Int 1</susOSCount>
