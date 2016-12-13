require "./osek-initialization.k" 

module OSEK-RESOURCE
  imports OSEK-CONFIGURATION 
  imports OSEK-INITIALIZATION 

  //11 rules


  /*@ Define the semantics of API GetResource. Accorrding to the Priority Ceiling Protocol of the system, 
      if the current priority of the task (in the cell \texttt{tPriority}) is lower than the ceiling 
      priority of the resource (in the cell \texttt{rPriority}), the priority of the task is raised to 
      the ceiling priority of the resource. The current priority of the task is saved when the task 
      releases the resource. 
   */
//DeclareResource
rule <task><state>running</state><k>DeclareResource(T);=>. ...</k>...</task>
<resource><rid>T</rid>...</resource>
<signal> .Set </signal>
<alarm> <aid> A </aid> <aSysCounter> C</aSysCounter> <alarmTime>AT</alarmTime> ...</alarm><br/>
<sysCounter> <cid> C </cid> <currentValue> RV=>(RV+Int 1)%Int (MAV +Int 1) </currentValue> <maxAllowedValue> MAV </maxAllowedValue> ...</sysCounter>

rule <task><state>running</state><k>DeclareResource(T);=>. ...</k>...</task>
<resource><rid>T</rid>...</resource>
<signal> .Set=>SetItem(stop) </signal>
<alarm> <aid> A </aid> <aSysCounter> C</aSysCounter> <alarmTime>AT</alarmTime> ...</alarm><br/>
<sysCounter> <cid> C </cid> <currentValue> RV=>(RV+Int 1)%Int (MAV +Int 1) </currentValue> <maxAllowedValue> MAV </maxAllowedValue> ...</sysCounter>


  rule <task> <tid> I </tid> <state> running </state> <k> (GetResource(R);)  => . ...</k> 
             <tPriority> N' => (#if N' <Int N2 #then N2 #else N' #fi) </tPriority>
       <accRes>  (.List => ListItem(R)) _ </accRes> <apiData> ST </apiData> 
         //<historyK> (L' => #if B andBool ST ==K . #then L' ListItem(GetResource(R);) #else L' #fi) </historyK> 
  ... </task> 
  //<proId> I </proId>
       <resource> <rid> R </rid>  
            <rPriority> N2 </rPriority>  
      <rOwner> L </rOwner> 
      (.Bag => <tPri> N' </tPri>)
      (.Bag => <rTid> I </rTid>) ...
       </resource> 
       <signal> . </signal>
        <sysCounter> <cid> C </cid> 
        <currentValue>  RV=>(RV+Int 1)%Int (MAV +Int 1)  </currentValue> 
        <maxAllowedValue> MAV </maxAllowedValue>... </sysCounter>
        <alarmList> .List </alarmList>
       //<tcgMode> B </tcgMode> 
       [transition]




  rule <task> <tid> I </tid> <state> running </state> <k> (GetResource(R);)  => . ...</k> 
       	     <tPriority> N' => (#if N' <Int N2 #then N2 #else N' #fi) </tPriority>
	     <accRes>  (.List => ListItem(R)) _ </accRes> <apiData> ST </apiData> 
	       //<historyK> (L' => #if B andBool ST ==K . #then L' ListItem(GetResource(R);) #else L' #fi) </historyK> 
	... </task> 
       <resource> <rid> R </rid>  
       		  <rPriority> N2 </rPriority>  
		  <rOwner> L </rOwner> 
		  (.Bag => <tPri> N' </tPri>)
		  (.Bag => <rTid> I </rTid>) ...
       </resource> 
       <signal> . </signal>
       <alarm><aid> A </aid><aSysCounter> C</aSysCounter> <alarmTime>AT</alarmTime>... </alarm><br/>
        <sysCounter> <cid> C </cid> <currentValue> RV=>(RV+Int 1)%Int (MAV +Int 1) </currentValue> <maxAllowedValue> MAV </maxAllowedValue>... </sysCounter>
      // <tcgMode> B </tcgMode> 
       <alarmList> L1 </alarmList>
   //  when (I in L) andBool ((RV +Int 1)<Int AT) andBool (A in L1)[transition]


    rule <task> <tid> I </tid> <state> running </state> <k> GetResource(R);  => . ...</k> 
              <tPriority> N' => (#if N' <Int N2 #then N2 #else N' #fi) </tPriority>
        <accRes> (L =>L ListItem(R))  </accRes> <apiData> ST </apiData> 
       //  <historyK> (L' => #if B andBool ST ==K . #then L' ListItem(GetResource(R);) #else L' #fi) </historyK> 
  ... </task> 
       <resource> <rid> R </rid>  
            <rPriority> N2 </rPriority>  
      <rOwner> L </rOwner> 
      (.Bag => <tPri> N' </tPri>)
      (.Bag => <rTid> I </rTid>) ...
       </resource> <signal> .Set=>SetItem(alarmed) </signal>
       <alarm><aid> A </aid><aSysCounter> C</aSysCounter> <alarmTime>AT</alarmTime> </alarm><br/>
        <sysCounter> <cid> C </cid> <currentValue> RV=>(RV+Int 1)%Int (MAV +Int 1) </currentValue> <maxAllowedValue> MAV </maxAllowedValue> </sysCounter>
        <alarmList> L1 </alarmList>
     //  <tcgMode> B </tcgMode> 
     when (I in L) andBool ((RV +Int 1) ==Int AT) andBool (A in L1) [transition]


  rule <task> <tid> I </tid> <state> running </state> <k> GetResource(R); ... </k> <apiData> ST </apiData> 
	      // <historyK> (L' => #if B andBool ST ==K . #then L' ListItem(GetResource(R);) #else L' #fi) </historyK> 
	... </task> 
       <resource> <rid> R </rid>  
		  <rOwner> L </rOwner>  ...
       </resource> <signal> .Set => SetItem(stop) </signal>
     //  <tcgMode> B </tcgMode> 
       (.Bag => <errorCell> Error(E_OS_UNDEF, I, GetResource(R);,"Resource " +String Id2String(R) +String " cannot be accessed by task " +String Id2String(I))  </errorCell>)

     when notBool (I in L) [transition]


  rule <task> <tid> I </tid> <state> running </state> <k> GetResource(R); ... </k> <apiData> ST </apiData> 
	      // <historyK> (L => #if B andBool ST ==K . #then L ListItem(GetResource(R);) #else L #fi) </historyK> 
       ... </task> 
       <resource> <rid> R </rid> <rTid> I' </rTid> ... </resource> 
      // <tcgMode> B </tcgMode> 
       (.Bag => <errorCell> Error(E_OS_ACCESS, I, GetResource(R);,"Resource " +String Id2String(R) +String  " has been accupied by other tasks!")  </errorCell>)
       <signal> .Set => SetItem(stop) </signal> [transition]


 /* rule <task> <tid> I </tid> <state> running </state> <k> GetResource(R:Id); ... </k> <apiData> ST </apiData> 
	       <historyK> (L => #if B andBool ST ==K . #then L ListItem(GetResource(R);) #else L #fi) </historyK> 
	... </task> 
       (.Bag => <errorCell> Error(E_OS_ID, I, GetResource(R);,"Resource " +String Id2String(R) +String " not exist!")  </errorCell>)
       <signal> .Set => SetItem(stop) </signal>
       <types> M </types>
     //  <tcgMode> B </tcgMode> 
      // when notBool $hasMapping(M,R) orBool ($hasMapping(M,R) andBool M(R) =/=K resource) [transition]*/


  /*@ Define the semantics of API ReleaseResource. When the API is called, the corresponding resource $R$ is 
      released by removing the \texttt{rTid} cell and the \texttt{tPri} cell from the resource cell. 
      The priority of the task is reset to the priority which was dynamically assigned before requiring the resource. 
   */
   rule <task> <tid> I </tid> <state> running </state> <k> ReleaseResource(R); => . ... </k> 
              <tPriority> N' => N </tPriority> <apiData> ST </apiData> 
       //  <historyK> (L => #if B andBool ST ==K . #then L ListItem(ReleaseResource(R);) #else L #fi) </historyK> 
        <accRes> (ListItem(R) => .List) L1 </accRes>   ... </task> 
       <resource> <rid> R </rid> ( <rTid> I </rTid> => .) (<tPri> N </tPri> => .)  ... </resource>
      // <tcgMode> B </tcgMode> 
        <sysCounter> <cid> C </cid> <currentValue> RV=>(RV+Int 1)%Int (MAV +Int 1) </currentValue> <maxAllowedValue> MAV </maxAllowedValue> ... </sysCounter>
        <alarmList> .List </alarmList>
       <signal> .Set=>SetItem(schedule) </signal> [transition]


  rule <task> <tid> I </tid> <state> running </state> <k> ReleaseResource(R); => . ... </k> 
       	      <tPriority> N' => N </tPriority> <apiData> ST </apiData> 
	     //  <historyK> (L => #if B andBool ST ==K . #then L ListItem(ReleaseResource(R);) #else L #fi) </historyK> 
	      <accRes> (ListItem(R) => .List) L1 </accRes>   ... </task> 
       <resource> <rid> R </rid> ( <rTid> I </rTid> => .) (<tPri> N </tPri> => .)  ... </resource>
     //  <tcgMode> B </tcgMode> 
       <alarm><aid> A </aid><aSysCounter> C</aSysCounter> <alarmTime>AT</alarmTime> ...</alarm><br/>
        <sysCounter> <cid> C </cid> <currentValue> RV=>(RV+Int 1)%Int (MAV +Int 1) </currentValue> <maxAllowedValue> MAV </maxAllowedValue> ... </sysCounter>
        <alarmList> L' </alarmList>
       <signal> .Set=>SetItem(schedule) </signal> 
       when ((RV +Int 1)<Int AT) andBool (A in L')[transition]

 /*rule <task> <tid> I </tid> <state> running </state> <k> ReleaseResource(R); => . ... </k> 
              <tPriority> N' => N </tPriority> <apiData> ST </apiData> 
        // <historyK> (L => #if B andBool ST ==K . #then L ListItem(ReleaseResource(R);) #else L #fi) </historyK> 
        <accRes> (ListItem(R) => .) L1 </accRes>   ... </task> 
       <resource> <rid> R </rid> ( <rTid> I </rTid> => .) (<tPri> N </tPri> => .)  ... </resource>
      // <tcgMode> B </tcgMode> 
       <alarm><aid> A </aid><aSysCounter> C</aSysCounter> <alarmTime>AT</alarmTime> ...</alarm><br/>
        <sysCounter> <cid> C </cid> <currentValue> RV=>(RV+Int 1)%Int (MAV +Int 1) </currentValue> <maxAllowedValue> MAV </maxAllowedValue> ...</sysCounter>
        <alarmList> L' </alarmList>
       <signal> .Set=>SetItem(alarmed) SetItem(schedule) </signal> 
       when ((RV +Int 1) ==Int AT) andBool (A in L') [transition]*/


  rule <task> <state> running </state> <k> ReleaseResource(R); ... </k> <tid> I </tid> 
	      <accRes> ListItem(R') L </accRes>  <apiData> ST </apiData> 
	     //  <historyK> (L' => #if B andBool ST ==K . #then L' ListItem(ReleaseResource(R);) #else L' #fi) </historyK> 	      
       ... </task> 
      // <tcgMode> B </tcgMode> 
       <signal> .Set => SetItem(stop) </signal>
       (.Bag => <errorCell> Error(E_OS_ACCESS, I, ReleaseResource(R);, "Task must first release the last resource " +String Id2String(R') +String  " it has request!") </errorCell> ) 
       when R' =/=K R [transition]

  rule <task> <tid> I:Id </tid> <state> running </state> 
       	      <k> ReleaseResource(R); ... </k> <apiData> ST </apiData> 
	     //  <historyK> (L => #if B andBool ST ==K . #then L ListItem(ReleaseResource(R);) #else L #fi) </historyK> 	      
       ...  </task> 
       <resource> <rid> R </rid> <rTid> I' </rTid> ...  </resource>
       <signal> .Set => SetItem(stop) </signal>
       (.Bag => <errorCell> Error(E_OS_NOFUNC, I, ReleaseResource(R);, "Resource " +String Id2String(R) +String  " cannot be released because it is not accupied by the task!") </errorCell> ) 
      // <tcgMode> B </tcgMode> 
      when I =/=K I' [transition]

  rule <task> <tid> I </tid> <state> running </state> <k> ReleaseResource(R); ... </k> <apiData> ST </apiData> 
	     //  <historyK> (L => #if B andBool ST ==K . #then L ListItem(ReleaseResource(R);) #else L #fi) </historyK> 	      
	 ... </task> 
       <resource> <rid> R </rid> <rPriority> N </rPriority>  </resource>
       (.Bag => <errorCell> Error(E_OS_ACCESS, I, ReleaseResource(R);,"Resource " +String Id2String(R) +String  " cannot be released because it is not accupied by any task!") </errorCell> )
       //<tcgMode> B </tcgMode> 
       <signal> .Set => SetItem(stop) </signal> [transition]

   /*@ Define the semantics of DeclareResource

   */



endmodule 


