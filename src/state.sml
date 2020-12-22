import "knowledge"

signature STATE =
sig
  type T;
  type goal = Pattern.vertexIndex list * SGraph.vertexIndex list * Relation.T;
  val goalsOf : T -> goal Sequence.T;
  val patternCompOf : T -> Pattern.composition ;
  val constructionCompOf : T -> SGraph.constructionComposition;
  val knowledgeOf : T -> Knowledge.base;
  val make : Pattern.composition -> SGraph.constructionComposition -> goal list -> Correspondence.set -> Relation.set -> T;
  val init : goal list -> Knowledge.base -> T;
  val noGoals : T -> bool ;
  val propagateablePattern : T -> bool;

end

structure State : STATE =
struct

end
