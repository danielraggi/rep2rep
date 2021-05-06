import "knowledge"

signature STATE =
sig
  type T;
  type goal = Relation.relationship;
  val goalsOf : T -> goal Sequence.T;
  val patternCompOf : T -> Pattern.composition ;
  val constructionCompOf : T -> SGraph.constructionComposition;
  val knowledgeOf : T -> Knowledge.base;
  val make : Decomposition.decomposition -> SGraph.constructionComposition -> goal list -> Correspondence.set -> Relation.set -> T;
  val init : goal list -> Knowledge.base -> T;
  val noGoals : T -> bool ;
  val propagateablePattern : T -> bool;

end

structure State : STATE =
struct

end
