import "cspace"

signature RELATION =
sig
  type T;
  type relationship = CSpace.token list * SGraph.token list * T;

  val make : SGraph.token list * SGraph.token list * T -> relationship;

  val leftTypeOf : T -> Type.typ;
  val rightTypeOf : T -> Type.typ;

  val alwaysTrue : Type.typ -> Type.typ -> T;
  val isAlwaysTrue R : T -> bool;
  val same : T -> T -> bool;
  val sameRelationship : relationship -> relationship -> bool;
end

structure Relation : RELATION =
struct
  type T = string * Type.typ * Type.typ;
  type relationship = SGraph.token list * SGraph.token list * T;

  fun make x = x;

  fun nameOf (s,_,_) = s;
  fun leftTypeOf (_,t,_) = t;
  fun rightTypeOf (_,_,t) = t;

  fun alwaysTrue lty rty = ("alwaysTrue",lty,rty) ;
  fun isAlwaysTrue R = (nameOf R = "alwaysTrue");

  fun same (n,t1,t2) (n',t1',t2') =
     n = n' andalso Type.same t1 t1' andalso Type.same t2 t2'

  fun sameRelationship (ts1,ts2,R) (ts1',ts2',R') =
    allZip CSpace.sameTokens ts1 ts1' andalso allZip CSpace.sameTokens ts2 ts2' andalso same R R'
end
