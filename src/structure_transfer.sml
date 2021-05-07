import "search"
import "state"
import "decomposition"

signature TRANSFER =
sig
  (*
  val applyCorrespondenceForGoalAndMatch : State.T -> Correspondence.T -> Relation.relationship -> acmt.construction -> State.T seq *)
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
  (*
  fun applyCorrespondenceForGoalAndMatch st corr goal ct =
    let val (_,[tv],_) = Relation.tupleOfRelationship goal handle _ => raise Mismatch
        val (Rf,_) = Correspondence.relationsOf corr
        val (sourcePattern,targetPattern) = Correspondence.patternsOf corr
        val sourceFoundations = ConstructionTerm.foundationSequence ct
        val patternDecomp = State.patternDecompOf st
        val targetPattern' = ConstructionTerm.refreshNames targetPattern patternDecomp
        val targetConstruct = ConstructionTerm.constructOf targetPattern'
        val targetFoundations = ConstructionTerm.foundationSequence targetPattern'
        val resultingpDecomp = ConstructionTerm.joinWithIdentifications (patternDecomp,targetPattern') [(tv,targetConstruct)]
        val newGoal = Relation.ship (sourceFoundations,targetFoundations,Rf)
    in State.updatePatternDecomp (State.replaceGoal st goal newGoal) resultingpDecomp
    end
    *)

  exception CorrespondenceNotApplicable
  fun applyCorrespondenceForGoal st corr goal =
    let val ([sourceToken],[targetToken],Rg) = Relation.tupleOfRelationship goal handle _ => raise Mismatch
        val (Rf,Rc) = Correspondence.relationsOf corr
        val _ = if Knowledge.subRelation KB Rc Rg then () else raise CorrespondenceNotApplicable
        val (sourcePattern,targetPattern) = Correspondence.patternsOf corr
        val ct = State.constructionOf st
        val T = State.typeSystemOf st
        val matchingGenerator = case Pattern.findGeneratorForTokenMatching T ct sourceToken sourcePattern of SOME x => x | NONE => raise CorrespondenceNotApplicable
        val generatorFoundations = ConstructionTerm.foundationSequence matchingGenerator
        val patternDecomp = State.patternDecompOf st
        val targetPattern' = Decomposition.refreshNames targetPattern patternDecomp
        val targetFoundations = ConstructionTerm.foundationSequence targetPattern'
        val newPatternDecomp = if Decomposition.isPlaceholder patternDecomp
                             then Decomposition.initFromConstruction targetPattern'
                             else Decomposition.attachConstructionAt patternDecomp targetPattern' targetToken
        val stateWithUpdatedGoals = if Relation.isAlwaysTrue Rf then State.removeGoal st goal
                                    else State.replaceGoal st goal (generatorFoundations,targetFoundations,Rf)
    in State.updatePatternDecomp stateWithUpdatedGoals newPatternDecomp
    end

  fun applyCorrespondence st corr =
    let fun applyCorrespondence' [] = []
          | applyCorrespondence' (g::gs) = ([applyCorrespondenceForGoal st corr g] handle CorrespondenceNotApplicable => []) @ applyCorrespondence' gs
    in Seq.of_list (applyCorrespondence' (State.goalsOf st))
    end

  (*
  fun quickCorrFilter KB rships corrs =
    let fun f [] corr = false
          | f ((_,_,R)::rships) corr =
        let val (_,Rc) = Correspondence.relationsOf corr
        in Knowledge.subRelation KB Rc R orelse f rships corr
        end
    in Set.filter f corrs end
  *)

  fun unfoldState st =
    let val KB = State.knowledgeOf st
        val corrs = Knowledge.correspondencesOf KB
        (*val CR = quickCorrFilter KB (State.goalsOf st) (Set.union rels corrs)*)
    in Seq.maps (applyCorrespondence st) corrs (*the returned sequence states is disjunctive; one must be satisfied *)
    end

  exception BadGoals
  (* every element of goals should be of the form ([vi1,...,vin],[vj1,...,vjm],R)*)
  fun structureTransfer T corrs rels ct goals =
    let
      val relsAsCorrs = Set.map Correspondence.ofRelation rels
      val KB = Knowledge.make (Set.union relsAsCorrs corrs)
      val typeOfTarget = case goals of [(_,_,R)] => Relation.rightTypeOf R
                                     | _ => raise BadGoals (* in the future I want to update this so that one can start with multiple goals *)
      val initialState = State.make {typeSystem = T,
                                      construction = ct,
                                      goals = goals,
                                      decomposition = Decomposition.Placeholder (CSpace.makeToken "dummy" ty),
                                      knowledge = KB}
      fun heuristic (st,st') = EQUAL
      val limit = 10
    in
      Search.sort unfoldState heuristic limit initialState
    end


end
