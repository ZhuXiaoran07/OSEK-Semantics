require "./osek-syntax.k" 


module OSEK-CONFIGURATION 
         imports OSEK-SYNTAX 
        



  /*@ \subsection{TaskState}
  A task has to change between several states. Extended tasks have four task states. Its state model can be seen as follows.

  The state model of basic tasks is nearly identical to the extended tasks state model. The only exception is that basic tasks do not have a waiting state.*/

 
 /*@ \subsection{Signal}
 Since rules in K Framework are excuted indeterminate, signal mechanism is introdued in our work. We add a condition which asks the special signal into every rule. Some rules can be excuted only when no signal arrives while some rules need signals such as rules about alarm and scheduling. Signal mechanism ensures the system manages signals first. We define a type Signal and three constants of it. The signal schedule indicates that a task should be scheduled. The signal alarmed means the counter is expired and the alarm begins to work. When signal arrives, system deals with alarm at once.  Priority of alarmed is higher than that of schedule. When any errors occurs in the system, the stop signal is given. A case　may happen that two schedule signals arrive at the same time. (This condition is introduced in section alarm.) In fact, the tasks just need to schedule once. Thus these signals are defined as elements of a set due to mutual differences of sets. */
 
 syntax Signal ::= "schedule" 
 	       | "stop"
 	       | "alarmed"
		   | "disableInterrupt"
 
 syntax SysApi ::= "ActivateTask"
 	       | "GetResource"
	       | "ReleaseResource"
	       | "TerminateTask"
	       | "ChainTask"
	       | "WaitEvent"
	       | "SetEvent" 
	       | "ClearEvent"
		   | "GetEvent"
	       | "SetrelAlarm"
	       | "SetabsAlarm"
	       | "GetAlarm"
	       | "CancelAlarm"
		   | "DisableAllInterrupts"
	       

 syntax Id ::= "initialTask"

  /*@ \section{configuration}
      The configuration consists of four parts
      \begin{enumerate}
	\item A set of \emph{global values} used to represent part of the state of the system 
	\item A set of tasks. They are first initialized accorrding to the input. Each task contains a list of APIs which can be executed by the system if it is not in the TCG mode. In the TCG mode, API is randomly generated. 
	\item A counter declared by OS system
	\item A set of alarms declared by users or autostarted when start the system
	\item A set of resources declared by users  
	\item A set of events declared by users 
      \end{enumerate}

  */

   /*@ constant \texttt{sysapis} represents a list of all system APIs.
    */
    // Right now, we only consider four of them. removed (obsolete) 
       
//   syntax List ::= "sysapis" 
//   rule sysapis => ListItem(ActivateTask) ListItem(TerminateTask) ListItem(ReleaseResource) 
//   		   ListItem(GetResource)  ListItem(ChainTask) 
//   		   ListItem(WaitEvent) ListItem(SetEvent) ListItem(ClearEvent) 
	/*@ A new type TaskPair, which used to store a task's ID (Id) and priority (Int), is defined here.*/
	
   syntax TaskPair ::= "<" Id ";" Int ">"
   syntax ListTaskPair ::= List{TaskPair, ""} 

  configuration 

  			<OSEK color="yellow"> 
  		 <global>
//		        <pgm> $PGM:OSEK </pgm> 
			<proId> .K </proId> 
			<readyTasks color="blue"> .ListTaskPair </readyTasks>
		   	<signal color="green"> .Set </signal> 
		   	<runningTask> .K </runningTask> <br/> 
		   	<errorCell multiplicity="*" color="black"> .K </errorCell> 
		   //	<tcgMode> $TCG:Bool </tcgMode> 
			<types> .Map </types> 
			<env> .Map </env> 
			<alarmList> .List </alarmList>
			<return>.K</return>
		   </global> 
		   <br/> 
  		   <tasks multiplicity="?" color="orange"> 
		     <task multiplicity="*" color="cyan">
		     	   <k color="green"> $PGM:OSEK </k> 
			   <ext> false </ext>			// is an extended task? 
			   <apiData> .K </apiData> 
                 <state color="red"> .K </state> <br/> 
                  <tid> initialTask </tid> 
                  <tPriority> 0 </tPriority> 
                           <activationTime> 0 </activationTime> 
                           <activatedTime> 0 </activatedTime>
			   <auto> false </auto> 
			   <historyK> .List </historyK> 
			  // <taskAlarm> .List </taskAlarm>
			   <accRes> .List </accRes> <br/> 
                           <done> false </done> 
			   <waitEvents> .List </waitEvents>
			   <taskEvents> .Map </taskEvents>  
			   <taskResources> .List </taskResources> 
			   <schedule> .K </schedule>
			   <tEnv> .Map </tEnv> 
                     </task>  
                   </tasks> 
		   <br/> 
		   <sysCounters  color="blue">
		   <sysCounter multiplicity="*">
		   	//<k color="green"> $PGM:OSEK </k>
		   	<cid> .K </cid>
		   	<maxAllowedValue> 0 </maxAllowedValue>
		   	<miniCycle> 0 </miniCycle>
		   	<currentValue> 0 </currentValue>
		   	<cAlarm> .List </cAlarm>
		   </sysCounter>
		</sysCounters>

		   <alarms>
		   <alarm multiplicity="*" color="green">
		   	<aid> .K </aid>
		   	<aSysCounter> .K </aSysCounter>
		   	<RemainAlarmTime> .Map </RemainAlarmTime> 
		   	<alarmTime> 0 </alarmTime>
		   	<cycleTime> 0 </cycleTime>
		   	<autostart> false </autostart>
		   	<cyclicity> false </cyclicity>
		   	
		<action> .K </action>
		<actedTaskId> .K </actedTaskId>
		<actedEventId> .K </actedEventId>
		<actedAlarmId> .K </actedAlarmId>
		<actedType> .K </actedType>
		
		   </alarm>
		</alarms>

	


		   <resources color="gray"> 
		     <resource  multiplicity="*" >
		     		<rid> .K </rid> 
				<rPriority> 0 </rPriority> 
			   	<rTid> .K </rTid> <br/>  // to record the task id (created during execution)
				<tPri> 0 </tPri> // to record the priority of the task before the resource is allocated
                                <rProperty> .K </rProperty> 
				<rOwner> .List </rOwner> 
		     </resource>  
		   </resources> 

		   <events color="blue"> 
		      <event multiplicity="*">  
			 <eid> 0 </eid> 
			 <eOwner> .List </eOwner> <br/> 
			  <maskType> .K </maskType> 
			  </event>    
		    </events> 
		    
		    <interrupt>
		    <susAllCount>0</susAllCount>
		    <susOSCount>0</susOSCount>
		    </interrupt>
			
  		</OSEK> 
  
endmodule 




