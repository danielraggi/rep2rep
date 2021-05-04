import "search"
import "state"

signature TRANSFER =
sig

  val applyCorrespondenceForGoalAndMatch : State.T -> Correspondence.T -> Relation.relationship -> acmt.construction -> State.T seq
  val applyCorrespondenceForGoal : State.T -> Correspondence.T -> Relation.relationship -> State.T seq
  val applyCorrespondence : State.T -> Correspondence.T -> State.T seq
  val unfoldState : State.T -> State.T seq
  val StructureTransfer : Knowledge.base -> SGraph.T -> Relation.relationship list -> State.T

end

structure Transfer : TRANSFER =
struct

  exception Mismatch
  (* given corr, a goal which matches the construct-relation of corr,
     and a construction ct which source-matches corr, the following
     function produces the state with updated goals and pattern composition *)
  fun applyCorrespondenceForGoalAndMatch st corr goal ct =
    let val (_,[tv],_) = Relation.goal goal handle _ => raise Mismatch
        val (Rf,_) = Correspondence.relationsOf corr
        val (sourcePattern,targetPattern) = Correspondence.patternsOf corr
        val sourceFoundations = ConstructionTerm.foundationSequence ct
        val patternComp = State.patternCompOf st
        val targetPattern' = ConstructionTerm.refreshNames targetPattern patternComp
        val targetConstruct = ConstructionTerm.constructOf targetPattern'
        val targetFoundations = ConstructionTerm.foundationSequence targetPattern'
        val resultingpComp = ConstructionTerm.joinWithIdentifications (patternComp,targetPattern') [(tv,targetConstruct)]
        val newGoal = Relation.goal (sourceFoundations,targetFoundations,Rf)
    in State.updatePatternComp (State.replaceGoals st goal newGoal) resultingpComp
    end

  exception NoMatchingGenerator
  fun applyCorrespondenceForGoal st corr goal =
    let val ([sv],[tv],Rg) = Relation.goal goal handle _ => raise Mismatch
        val (Rf,Rc) = Correspondence.relationsOf corr
        val (sourcePattern,targetPattern) = Correspondence.patternsOf corr
        val ct = State.constructionOf st
        val matchingGenerator = case Pattern.findGeneratorMatching ct sourcePattern of SOME x => x | NONE => raise NoMatchingGenerator
        val generatorFoundations = ConstructionTerm.foundationSequence matchingGenerator
        val patternComp = State.patternCompOf st
        val targetPattern' = ConstructionTerm.refreshNames targetPattern patternComp
        val targetConstruct = ConstructionTerm.constructOf targetPattern'
        val targetFoundations = ConstructionTerm.foundationSequence targetPattern'
        val resultingpComp = ConstructionTerm.joinWithIdentifications (patternComp,targetPattern') [(tv,targetConstruct)]
        val newGoal = Relation.goal (generatorFoundations,targetFoundations,Rf)
    in State.updatePatternComp (State.replaceGoals st goal newGoal) resultingpComp
    end

  fun applyCorrespondence st corr = Seq.map (applyCorrespondenceForGoal st corr) (Seq.of_list (State.goalsOf st))

  fun quickCorrFilter KB rships corrs =
    let fun f [] corr = false
          | f ((_,_,R)::rships) corr =
        let val (_,Rc) = Correspondence.relationsOf corr
        in Knowledge.subrelation KB Rc R orelse f rships corr
        end
    in Set.filter f corrs end

  fun unfoldState st =
    let val KB = State.knowledgeOf st
        val corrs = Knowledge.correspondencesOf KB
        val rels = Set.map Correspondence.ofRelation (Knowledge.relationshipsOf KB)
        val CR = quickCorrFilter KB (State.goalsOf st) (Set.union rels corrs)
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
