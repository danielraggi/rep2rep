import "util.set"

signature RELATION =
sig
  type T;
  type relationship = SGraph.vertex list * SGraph.vertex list * T;

  val ofRelationship : relationship -> T;
  val relationshipOf : T -> relationship;

  val subrelation : T * T -> bool;

  val leftTypeOf : T -> Type.T;
  val rightTypeOf : T -> Type.T;
  val alwaysTrue : T;
end

structure Relation : RELATION =
struct

end
