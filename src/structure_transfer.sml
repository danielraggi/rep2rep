import "search"
import "state"

signature TRANSFER =
sig

val unfoldGoals : State.T -> State.T seq
val StructureTransfer : Correspondence.set -> Relation.set -> SGraph.T -> Relation.T -> State.T

end

structure Transfer : TRANSFER =
struct

fun unfoldGoalsGivenCorr graph corr goals patternComp constructionComp =
let val matchingGoals = Correspondence.TagMatchingGoals corr goals
    fun unfoldGoalsGivenCorr' matchingGoals' =
      case Sequence.pull matchingGoals' of
        SOME ((g,NONE),gs) => Sequence.map (fn (gs',pc,cc) => (Sequence.insert g gs',cc,pc)) (unfoldGoalsGivenCorr' graph corr gs patternComp constructionComp)
      | SOME ((g,SOME uR),gs) => (* uR should be the foundation relation of the correspondence, with pointers to the vertices of the matching sub-construction of graph*)
              let val (P1,P2) = Correspondence.patternsOf corr
                  val construction = Pattern.getMatchingConstructions graph P1
                  val patternComp' = Pattern.attach patternComp P2 vi
                  val constructionComp' = Construction.attach constructionComp construction vi
                  val newgoals = Relation.decompose uR
              in Sequence.map (fn (gs',pc,cc) => (Sequence.concat newgoals gs',constructionComp',patternComp')) (unfoldGoalsGivenCorr' graph corr gs patternComp constructionComp)
              end
      | NONE => Sequence.empty
in unfoldGoalsGivenCorr' matchingGoals
end

fun unfoldGoals st =
let val goals = State.goalsOf st (*this list of goals is conjunctive; all must be satisfied*)
    val patternComp = State.patternCompOf st
    val graph = State.sgraphOf st
    val KB = State.knowledgeOf st
    val corrs = Knowledge.correspondencesOf KB
    val options = Sequence.map (fn corr => unfoldGoalsGivenCorr graph corr goals patternComp) corrs
in options (*the reaturned sequence of lists of goals is disjunctive; one must be satisfied *)
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
