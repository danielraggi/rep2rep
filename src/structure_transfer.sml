signature STATE =
sig
  type T;
  type goal = Pattern.vertexIndex list * SGraph.vertexIndex list * Relation.T;
  val goalsOf : T -> goal list;
  val patternCompOf : T -> pattern.composition ;
  val constructionCompOf : T -> SGraph.constructionComposition;
  val knowledgeOf ;
  val make : Pattern.composition -> SGraph.constructionComposition -> goal list -> Correspondence.set -> Relation.set -> T;
  val init : goal list -> Correspondence.set -> Relation.set -> T;
  val noGoals : T -> bool ;
  val propagateablePattern : T -> bool;

end

structure State : STATE =
struct

end

signature TRANSFER =
sig

val unfoldGoals : State.T -> State.T seq
val StructureTransfer : Correspondence.set -> Relation.set -> SGraph.T -> Relation.T -> State.T

end

structure Transfer : TRANSFER =
struct

fun unfoldGoals st =
let val goals = State.goalsOf st (*this list of goals is conjunctive; all must be satisfied*)
    val patternComp = State.patternCompOf st
    val KB = State.knowledgeOf st
    val
in State.make (pattern ) (*the reaturned sequence of lists of goals is disjunctive; one must be satisfied *)
end

(* every element of R should be of the form ([vi1,...,vin],[vj1,...,vjm],R)*)
fun StructureTransfer Corrs Rels graph Rs =
let
  val patternComp = Pattern.empty
  val goals = map Relation.decompose Rs
  val KB = Knowledge.make Corrs Rels
  val initialState = State.make patternComp goals KB
  fun heuristic st = 0
  fun sat st = State.noGoals st andalso State.propagateablePattern st
in
  Search.strategy unfoldGoals heuristic sat initialState
end


end
