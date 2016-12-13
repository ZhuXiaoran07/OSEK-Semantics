require "./osek-configuration.k" 

//21 rules

module IMP-SEMANTICS 
  imports OSEK-CONFIGURATION 

  syntax KResult ::= Int | Bool 

  rule I1:Int <= I2:Int => I1 <=Int I2
  rule I1:Int == I2:Int => I1 ==Int I2 
  rule I1:Int != I2:Int => I1 =/=Int I2
  rule I1:Int < I2:Int => I1 <Int I2
  rule I1:Int + I2:Int => I1 +Int I2
  rule I1:Int - I2:Int => I1 -Int I2
  rule I1:Int * I2:Int => I1 *Int I2
  rule I1:Int / I2:Int => I1 /Int I2 when I2 =/=Int 0 
  rule I1:Int % I2:Int => I1 %Int I2 when I2 =/=Int 0
 
  
 





  rule ! T:Bool => notBool T
  rule true && B => B
  rule false && _ => false

  rule if (B) S => if (B) S else {} [macro]


/*rule <k> int (X,Xs => Xs);_ </k> <env> Rho:Map (.Map => X|->0) </env>
    when notBool (X in keys(Rho))*/

  

  rule  <state> running </state> 
       	      <k> X = I:Int; => . ...</k> 
       <env>... X |-> (_ => I) ...</env> 
       <signal> .Set </signal> 

   rule  <state> running </state>
        <k> X:Id => V ... </k> 
        <signal> .Set </signal> 
   	<env>... X |-> V:Int ... </env> [lookup]

  rule <task> <state> running </state>
	<k> if (true)  S else _ => S ... </k> ... </task> 
      <signal> . </signal>  [structural]

  rule <task> <state> running </state>
	<k>  if (false) _ else S => S ... </k> ... </task> 
      <signal> . </signal>

  rule <task> <state> running </state>
	<k>  while (B) S => if (B) {S while (B) S} else {} ... </k> ...          </task> 
      <signal> . </signal>  [structural]

  rule <task> <state> running </state>
	<k> {} => .K ... </k> ... </task> 
      <signal> . </signal> 

  rule <task> <state> running </state>  
       	      <k> { S } => S ... </k> ...
      </task>  <signal> . </signal> 

endmodule 
