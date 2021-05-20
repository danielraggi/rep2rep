import "cspace";

signature RELATION =
sig
  type T;
  type relationship = CSpace.token list * CSpace.token list * T;

  val tupleOfRelationship : relationship -> CSpace.token list * CSpace.token list * T;
  val make : string -> T;
  val makeRelationship : CSpace.token list * CSpace.token list * T -> relationship;

  val alwaysTrue : T;
  val isAlwaysTrue : T -> bool;
  val same : T -> T -> bool;
  val sameRelationship : relationship -> relationship -> bool;
end;

structure Relation : RELATION =
struct
  type T = string;
  type relationship = CSpace.token list * CSpace.token list * T;

  fun tupleOfRelationship r = r;
  fun make r = r;
  fun makeRelationship (x,y,R) = (x,y,R);

  fun nameOf s = s;

  val alwaysTrue = "alwaysTrue";
  fun isAlwaysTrue R = (nameOf R = "alwaysTrue");

  fun same n n' = (n = n')

  fun sameRelationship (ts1,ts2,R) (ts1',ts2',R') =
    List.allZip CSpace.sameTokens ts1 ts1'
    andalso List.allZip CSpace.sameTokens ts2 ts2'
    andalso same R R'

end;
