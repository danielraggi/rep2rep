import "search"
import "state"

signature TRANSFER =
sig

val unfoldState : State.T -> State.T seq
val StructureTransfer : Knowledge.base -> SGraph.T -> Relation.relationship list -> State.T

end

structure Transfer : TRANSFER =
struct

exception Mismatch
(* given corr, a goal which matches the construct-relation of corr,
   and a construction (g,v) which source-matches corr, the following
   function produces the state with updated goals and pattern composition *)
fun applyCorrespondenceGivenGoalAndMatch st corr goal (g,v) =
let val (_,[tv],_) = Relation.relationshipOf goal handle _ => raise Mismatch
    val (Rf,_) = Correspondence.relationsOf corr
    val (sourcePattern,targetPattern) = Correspondence.patternsOf corr
    val sourceFoundations = Construction.foundationsOf (g,v)
    val patternComp = State.patternCompOf st
    val targetPattern' = Construction.refreshNames targetPattern patternComp
    val targetConstruct = Construction.constructOf targetPattern'
    val targetFoundations = Construction.foundationsOf targetPattern'
    val resultingpComp = Construction.joinWithIdentifications (patternComp,targetPattern') [(tv,targetConstruct)]
    val newGoal = Relation.ofRelationship (sourceFoundations,targetFoundations,Rf)
in State.updatePatternComp (State.replaceGoals st goal newGoal) resultingpComp
end

fun applyCorrespondenceGivenGoal st corr goal =
let val ([sv],_,Rg) = Relation.relationshipOf goal handle _ => raise Mismatch
    val (_,Rc) = Correspondence.relationsOf corr
    val (lPattern,rPattern) = Correspondence.patternsOf corr
    val sgraph = State.sgraphOf st
    val matchingConstructions = Pattern.matchingConstructionsGivenConstruct lPattern sgraph sv
in Seq.map (applyCorrespondenceGivenGoalAndMatch st corr goal) matchingConstructions
end

fun applyCorrespondence st corr = Seq.maps (applyCorrespondenceGivenGoal st corr) (Seq.of_list (State.goalsOf st))

fun quickCorrFilter rships corrs =
let fun f [] corr = false
      | f ((_,_,R)::rships) corr =
    let val (_,Rc) = Correspondence.relationsOf corr
    in Relation.subrelation Rc R orelse f rships corr
    end
in Set.filter f corrs end

fun unfoldState st =
let val KB = State.knowledgeOf st
    val corrs = Knowledge.correspondencesOf KB
    val rels = Set.map Correspondence.ofRelation (Knowledge.relationsOf KB)
    val CR = quickCorrFilter (State.goalsOf st) (Set.union rels corrs)
in Seq.maps (applyCorrespondence st) CR (*the returned sequence states is disjunctive; one must be satisfied *)
end

(* every element of goals should be of the form ([vi1,...,vin],[vj1,...,vjm],R)*)
fun StructureTransfer KB graph goals =
let
  val initialState = State.init KB goals graph
  fun heuristic (st,st') = EQUAL
  val limit = 10
in
  Search.sort unfoldState heuristic limit initialState
end


end
