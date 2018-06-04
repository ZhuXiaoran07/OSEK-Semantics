require "./osek-task.k" 
require "./osek-resource.k" 
require "./osek-event.k" 
require "./osek-scheduler.k" 
require "./osek-alarm.k"
require "./osek-imp.k" 
require "./osek-configuration.k"
//require "./osek-counter.k"

// 161 rules
//kompile time 7.82s
//krun time 10.47s
//verification time


module OSEK 

 // imports OSEK-INITIALIZATION 
 imports OSEK-CONFIGURATION
 imports OSEK-SCHEDULING 
 imports OSEK-TASK 
 imports OSEK-RESOURCE
 imports OSEK-EVENT 
 imports OSEK-ALARM
 imports IMP-SEMANTICS 
 
 



endmodule 
