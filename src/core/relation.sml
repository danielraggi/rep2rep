import "core.cspace";

signature RELATION =
sig
  type T;
  type relationship = CSpace.token list * CSpace.token list * T;

  val T_rpc : T Rpc.Datatype.t;
  val relationship_rpc : relationship Rpc.Datatype.t;

  val nameOf : T -> string;
  val tupleOfRelationship : relationship -> CSpace.token list * CSpace.token list * T;
  val make : string -> T;
  val makeRelationship : CSpace.token list * CSpace.token list * T -> relationship;

  val alwaysTrue : T;
  val isAlwaysTrue : T -> bool;
  val alwaysFalse : T;
  val isAlwaysFalse : T -> bool;
  val relationshipIsFalse : relationship -> bool;
  val same : T -> T -> bool;
  val sameRelationship : relationship -> relationship -> bool;
  val stronglyMatchingRelationships : relationship -> relationship -> bool;
  val stringOfRelationship : relationship -> string;
end;

structure Relation : RELATION =
struct
  type T = string;
  type relationship = CSpace.token list * CSpace.token list * T;

  val T_rpc = String.string_rpc;

  val relationship_rpc = Rpc.Datatype.tuple3
                             (List.list_rpc CSpace.token_rpc,
                              List.list_rpc CSpace.token_rpc,
                              T_rpc);

  fun tupleOfRelationship r = r;
  fun make r = r;
  fun makeRelationship (x,y,R) = (x,y,R);

  fun nameOf s = s;

  val alwaysTrue = "alwaysTrue"
  fun isAlwaysTrue R = (nameOf R = alwaysTrue)
  val alwaysFalse = "FALSE"
  fun isAlwaysFalse R =  (nameOf R = alwaysFalse)
  fun relationshipIsFalse (_,_,R) = isAlwaysFalse R

  fun same n n' = (n = n')

  fun sameRelationship (ts1,ts2,R) (ts1',ts2',R') =
    List.allZip CSpace.sameTokens ts1 ts1'
    andalso List.allZip CSpace.sameTokens ts2 ts2'
    andalso same R R'

  fun stronglyMatchingRelationships (ts1,ts2,R) (ts1',ts2',R') =
    List.allZip CSpace.tokensHaveSameType ts1 ts1'
    andalso List.allZip CSpace.tokensHaveSameType ts2 ts2'
    andalso same R R'

  fun stringOfRelationship (x,y,R) = "(" ^ List.toString CSpace.stringOfToken x ^ "," ^ List.toString CSpace.stringOfToken y ^ "," ^ nameOf R ^ ")"
end;
