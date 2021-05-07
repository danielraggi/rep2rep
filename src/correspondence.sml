import "pattern"
import "relation"

signature CORRESPONDENCE =
sig
  type corr;
  val patternsOf : corr -> Pattern.T * Pattern.T;
  val relationsOf : corr -> Relation.T * Relation.T;
  val ofRelation : Relation.T -> corr;
  val declareCorrespondence : Pattern.construction -> Pattern.construction -> Relation.T -> Relation.T;
end

structure Correspondence : CORRESPONDENCE =
struct
  type corr = Pattern.T * Pattern.T * Relation.T * Relation.T;

  fun patternsOf (sP,tP,Rf,Rc) = (sP,tP);
  fun relationsOf (sP,tP,Rf,Rc) = (Rf,Rc);

  (*the following turns a relation between tokens into a correspondence, with Rf being the
    "always true" relation, and Rc being the relation we want.*)
  fun ofRelation R = (Pattern.trivial (Relation.leftTypeOf R),
                      Pattern.trivial (Relation.rightTypeOf R),
                      Relation.alwaysTrue,
                      R);

  fun declareCorrespondence sP tP Rf Rc = (sP,tP,Rf,Rc);
end
