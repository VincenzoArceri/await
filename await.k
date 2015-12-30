/**
  * To compile kompile --transition "lookup,read,assignment,print,random, choice" await.k
  */

module AWAIT-SYN
	syntax Decl ::= "int" Ids ";"

	syntax AExp ::= Int | Id
                | "-" AExp                [strict]
                > "read" "(" ")"          
                | AExp "/" AExp           [strict, left]
                | AExp "*" AExp           [strict, left]
                | AExp "%" AExp           [strict, left]
                > AExp "+" AExp           [strict, left]
                | AExp "-" AExp           [strict, left]
                | "(" AExp ")"            [bracket]
  
  syntax BExp ::= Bool
                | "randomBool"            
                | AExp "<" AExp           [strict, non-assoc]
                | AExp "<=" AExp          [strict, non-assoc]
                | AExp ">" AExp           [strict, non-assoc]
                | AExp ">=" AExp          [strict, non-assoc]
                | AExp "==" AExp          [strict]
                | AExp "!=" AExp          [strict]
                | "!" BExp                [strict]
                > BExp "and" BExp         [strict(1), left]
                | BExp "or" BExp          [strict(1), left]
                | "(" BExp ")"            [bracket]

  syntax Exp ::= AExp | BExp
  syntax Ids  ::= List{Id,","}

  syntax Stmt ::= Decl | Block 
                | "spawn" Block
                | Exp ";"                                           [strict]
                | Id "=" AExp ";"             			                [strict(2)]
                | "if" "(" BExp ")" Block "else" Block              [avoid, strict(1)]
                | "if" "(" BExp ")" Block
                | "while" "(" BExp ")" Block
                | "print" "(" AExp ")" ";"              	          [strict]
                | "await" BExp "protected" Block
                | "exclusiveSpawn" "(" Block "," Block ")" ";"            

  syntax Block ::= "{" Stmts "}" | "{" "}" 
                  
                
  syntax Stmts ::= Stmt
                 | Stmts Stmts                                      [right]

  rule if (E) S => if (E) S else {}                                 [macro]

endmodule

/*
  Semantica di Competition
*/
module AWAIT
	imports AWAIT-SYN
	imports SUBSTITUTION
	imports BUILTIN-SYNTAX-HOOKS

  syntax Val ::= Int | Bool
  syntax KResult ::= Val

  configuration <T color="red">
                  <threads color="orange">
                    <thread multiplicity="*" color="yellow">
                      <k color="green"> $PGM:Stmts </k>
                      <env color="violet"> .Map </env>
                      <id color="pink"> 0 </id>
                    </thread>
                  </threads>

                  <store color="white"> .Map </store>
                  
                  <streams>
                 	<in color="magenta" stream="stdin"> .List </in>
                  	<out color="brown" stream="stdout"> .List </out>
                  </streams>

                  <barrier color="blue"> -1 </barrier>
                </T>

  rule  ! T:Bool => notBool(T)
  rule  true and E => E
  rule  false and _ => false
  rule  true  or _ => true
  rule  false or E => E

  rule randomBool => true                           [random]
  rule randomBool => false                          [random]

  rule  I1:Int + I2:Int => I1 +Int I2
  rule  I1:Int - I2:Int => I1 -Int I2
  rule  I1:Int * I2:Int => I1 *Int I2
  rule  I1:Int / I2:Int => I1 /Int I2 when I2 =/=Int 0
  rule  I1:Int % I2:Int => I1 %Int I2 when I2 =/=Int 0
  rule  - I:Int => 0 -Int I
  rule  I1:Int < I2:Int => I1 <Int I2
  rule  I1:Int <= I2:Int => I1 <=Int I2
  rule  I1:Int > I2:Int => I1 >Int I2
  rule  I1:Int >= I2:Int => I1 >=Int I2

  rule  I1:Int == I2:Int => I1 ==Int I2
  rule  I1:Int != I2:Int => I1 =/=Int I2

  rule  if (true) S else _ => S
  rule  if (false) _ else S => S

  rule  while (E) S => if (E) { S while(E) S }  	   [structural]

  rule 	<k> read() => I ...</k> 
  		  <in> ListItem(I:Int) => .List ...</in> 
  		  <id> T:Int </id>
  		  <barrier> B:Int </barrier> when ( B ==Int T orElseBool B ==Int -1) [read]

  rule 	<k> print(I:Int) ; => I ;... </k> 
  		  <out>... .List => ListItem(I) </out>  		  
  		  <id> T:Int </id>
        <barrier> B:Int </barrier> when ( B ==Int T orElseBool B ==Int -1) [print]

  rule  _:Int ; => .K

  rule  <k> X:Id => I:Int ...</k>
        <env>... X |-> L:Int ...</env>
        <store>... L |-> I:Int ...</store>  [lookup]

  rule  <thread>...
          <k> spawn { S:Stmts } => T:Int ; ...</k>
          <env> Env:Map </env>
       ...</thread>
       (. => <thread>...
               <k> S </k>
               <env> Env </env>
               <id> T </id>
         ... </thread>) when fresh(T:Int)

  rule <thread> ... <k> .K </k> <id> T:Int </id> ... </thread> => . when T =/=Int 0// Elimino le thread quando hanno terminato

  rule  <k> int (X:Id,X1:Ids => X1) ; ... </k>
		    <env> Rho:Map => Rho[L:Int/X] </env>
	     	<store> Delta:Map => Delta[0 / L] </store> when fresh(L:Int)  

  rule  int .Ids ; => .K      [structural]

	rule  <k> X:Id = I:Int ; => I; ... </k>
		    <env> ... X |-> N:Int ... </env>
		    <store> ... N |-> (_ => I) </store>
		    <id> T:Int </id>
        <barrier> B:Int </barrier> when (B ==Int -1) orElseBool (B ==Int T) [assignment]

  rule  S1:Stmts S2:Stmts => S1 ~> S2  [structural]

  syntax K ::= env(Map)

  rule { } =>.K

  rule <k> { S:Stmts } => S ~> env(Rho) ... </k>
       <env> Rho:Map </env>                 [structural]

  rule <k> env(Rho:Map) => . ... </k>
       <env> _ => Rho </env>

  rule await B:BExp protected Bl:Block =>  B ~> await B protected Bl

  rule false ~> await B:BExp protected Bl:Block => await B protected Bl

  rule 	<k> true ~> await B:BExp protected Bl:Block => Bl ~> remove T ;... </k>
  			<id> T:Int </id>
  			<barrier> _ => T </barrier>

  syntax UDF ::= "remove" Int ";"

  rule  <k> remove T:Int ; => .K ... </k>
        <barrier> _ => -1 </barrier>

  rule exclusiveSpawn ( Bl1:Block , Bl2:Block ) ; => spawn Bl1 [choice]
  rule exclusiveSpawn ( Bl1:Block , Bl2:Block ) ; => spawn Bl2 [choice]

endmodule