require "./osek-syntax.k" 


module OSEK-ERROR 
	   imports OSEK-SYNTAX   

  syntax ErrorType ::= "E_OS_ACCESS"  // release a resource which has a lower priority than the task 
  	 	   | "E_OS_CALLEVEL"  // errors related to interruption 
		   | "E_OS_ID"        // task/resource/event invalid Id 
		   | "E_OS_LIMIT"     // to many activation 
		   | "E_OS_NOFUNC"     // release unoccupied resources, or not in FILO order 
		   | "E_OS_RESOURCE"  // terminate/activate tasks when occupying resources 
		   | "E_OS_STATE"   // errors related to alarm 
		   | "E_OS_VALUE"     // errors related to alarm 
		   | "E_OS_CONF"      // configuration error 
		   | "E_OS_UNDEF"     // undefined errors 
		   

   
   syntax String ::= "Error" "(" ErrorType "," Id "," OSEKStmt "," String ")" [function]
   	  	  | "Error" "(" ErrorType "," Id "," String ")" [function]

endmodule 


