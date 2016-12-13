require "./osek-initialization.k" 

module OSEK-SCHEDULING 
   imports OSEK-INITIALIZATION 


   /*@ \section{Schedule}
   This module introduces some scheduling policies for our implementation. Also, ways to deal with signal schedule  are described in this part. 
   */

   //5 rules
   

   /*@ \subsection{scheduling policy defined in OSEK specification}
   For a full preemptive system, scheduling is performed in all of the following cases:
   \begin{itemize} 
   \item Successful termination of a task (API TerminateTask());
   \item Successful termination of a task with explicit activating of a successor task (API ChainTask());
   \item Activating a task at task level (API ActivateTask() or alarm expiration, if task activation is defined in this alarm);
   \item Explicit wait call if a transition into the waiting state takes place (extended tasks only, API WaitEvent());
   \item Setting an event to a waiting task at task level (API SetEvent() or alarm expiration, if event setting defined);
   \item Release of resource at task level (API ReleaseResource());
   \item Return from interrupt level to task level.
   \end{itemize}
   
   
   In the case of a non preemptable task, rescheduling will take place exactly in the following cases:
   \begin{itemize} 
   \item Successful termination of a task (API TerminateTask());
   \item Successful termination of a task with explicit activating of a successor task (API ChainTask());
   \item Explicit call of scheduler (API Schedule());
   \item A transition into the waiting state takes place (API WaitEvent()).
   \end{itemize}
   
   

    \subsection{scheduling policy in our implementation}
   If there is a task I' of lower priority running and it is preemptable, it is preempted and the ready task with the highest priority in the task is started to run. If there is no task running, the task at the head of the list goes to run. \\
   So far, we have implemented the following cases of schedule in a full preemptable task:\\
   
   1. Successful termination of a task (API TerminateTask());\\
   2. Successful termination of a task with explicit activating of a successor task (API ChainTask());\\
   3. Activating a task at task level (API ActivateTask() or active a task when alarm expires).\\
   

    The schedule signal is given in the following cases for a non preemptable task:\\
   
   1. Successful termination of a task (API TerminateTask());\\
   2. Successful termination of a task with explicit activating of a successor task (API ChainTask());\\
   3. Explicit call of scheduler (API Schedule()).\\
   */


  rule <signal> SetItem(schedule) => .Set </signal> 
       <readyTasks> (< I ; N >  L:ListTaskPair) => add(I',N',L) </readyTasks> <br/>
       <task> <tid> I' </tid> 
       <schedule> FULL </schedule>
       	      <state> running => ready </state> <tPriority> N' </tPriority> ... </task> <br/>
       <task> <tid> I </tid> <state> ready => running </state> ... </task> 
       <runningTask> I' => I </runningTask> <br/>
       when N >Int N' [transition]


        rule <signal> SetItem(schedule) => .Set </signal> 
       <readyTasks> < I ; N >  L:ListTaskPair </readyTasks> <br/>
       <task> <tid> I' </tid> 
       <schedule> FULL </schedule>
              <state> running  </state> <tPriority> N' </tPriority> ... </task> <br/>
      
       <runningTask> I' </runningTask> <br/>
       when N' >=Int N [transition]



      /* rule <signal> SetItem(schedule) => .Set </signal> 
       <readyTasks> (< I ; N >  L:ListTaskPair) => L </readyTasks> <br/>
       <task> <tid> I </tid> 
       //<schedule> FULL </schedule>
              <state> running  </state>  ... </task> <br/>*/
      
      

  // if no task is running 
  rule <signal> SetItem(schedule)  => .Set </signal> 
       <readyTasks> (< I ; N >  L:ListTaskPair) => L </readyTasks> 
       <task> <tid> I </tid> <state> ready => running </state> ... </task> 
       <runningTask> .K => I </runningTask>  [transition]

  rule <signal> SetItem(schedule) => .Set </signal> 
       <readyTasks> (< I ; N >) => < I' ; N' > </readyTasks> <br/> 
       <task> <tid> I' </tid> 
       //<schedule> FULL </schedule> 
       	      <state> running => ready </state> <tPriority> N' </tPriority> ... </task> <br/>
       <task> <tid> I </tid> <state> ready => running </state> ... </task> 
       <runningTask> I' => I </runningTask>
       when N >Int N' [transition]


 /* rule <signal> SetItem(schedule) => .Set </signal> 
       <readyTasks> < I ; N > L</readyTasks> <br/> 
       <task> <tid> I' </tid> 
       <schedule> FULL </schedule> 
              <state> running  </state> <tPriority> N' </tPriority> ... </task> <br/>
      // <task> <tid> I </tid> <state> ready => running </state> ... </task> 
      // <runningTask> I' => I </runningTask>
       when N <Int N' [transition]*/


    


  // if the head task in the ready task list has a lower priority than the running task 
 /* rule <signal> SetItem(schedule) => .Set </signal> 
       <readyTasks> < I ; N > ... </readyTasks> 
       <task> <state> running </state> <tPriority> N' </tPriority> ... </task>  
       when notBool N >Int N'  [transition] */

  //  if the running task cannot be preempted 
  rule <signal> SetItem(schedule) => .Set </signal> 
       <task>  
        <schedule> NON </schedule> 
        <state> running </state> ... </task> [transition]

endmodule 
