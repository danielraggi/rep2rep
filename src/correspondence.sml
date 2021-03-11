import "pattern"
import "relation"

signature CORRESPONDENCE =
sig
  type corr = Pattern.T * Pattern.T * Relation.T * Relation.T
  val patternsOf : corr -> Pattern.T * Pattern.T
  val relationsOf : corr -> Relation.T * Relation.T
  val ofRelation : Relation.T -> corr
end

structure Correspondence : CORRESPONDENCE =
struct
  type corr = Pattern.T * Pattern.T * Relation.T * Relation.T

  fun patternsOf (sP,tP,Rf,Rc) = (sP,tP)
  fun relationsOf (sP,tP,Rf,Rc) = (Rf,Rc)

  (*the following turns a relation into a correspondence.*)
  fun ofRelation R = (Pattern.trivial (Relation.leftTypeOf R),
                      Pattern.trivial (Relation.rightTypeOf R),
                      Relation.alwaysTrue,
                      R)
end
