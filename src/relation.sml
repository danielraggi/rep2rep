import "type"

signature RELATION =
sig
  type T;
  type relationship = SGraph.vertex list * SGraph.vertex list * T;

  val goal : SGraph.vertex list * SGraph.vertex list * T -> relationship;

  val leftTypeOf : T -> Type.T;
  val rightTypeOf : T -> Type.T;

  val alwaysTrue : Type.T -> Type.T -> T;
  val same : T -> T -> bool;
end

structure Relation : RELATION =
struct
  type T = string * Type.T * Type.T;
  type relationship = SGraph.vertex list * SGraph.vertex list * T;

  fun goal x = x;

  fun leftTypeOf (_,t,_) = t;
  fun rightTypeOf (_,_,t) = t;

  fun alwaysTrue lt rt = ("alwaysTrue",lt,rt) ;

  fun same (n,t1,t2) (n',t1',t2') =
     n = n' andalso Type.same t1 t1' andalso Type.same t2 t2'

end
