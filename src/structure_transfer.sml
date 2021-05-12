import "search"
import "state"
import "decomposition"

signature TRANSFER =
sig
  (*
  val applyCorrespondenceForGoalAndMatch : State.T -> Correspondence.corr -> Relation.relationship -> acmt.construction -> State.T seq *)
  val applyCorrespondenceForGoal : State.T -> Correspondence.corr -> Relation.relationship -> State.T seq
  val applyCorrespondence : State.T -> Correspondence.corr -> State.T seq
  val unfoldState : State.T -> State.T seq
  val structureTransfer : Knowledge.base -> SGraph.T -> Relation.relationship list -> State.T

end

structure Transfer : TRANSFER =
struct

  (*  *)
  fun refreshNamesUpToConstruct ct D t =
    let
      fun firstUnusedName Ns =
        let fun f n =
              let val vcandidate = "v"^(Int.toString n)
              in if List.exists (fn x => x = vcandidate) Ns then f (n+1) else "v"^(Int.toString n)
              end
        in f 0
        end
      val tokensInConstruction = List.filter (fn x => not (CSpace.sameToken t x)) (ConstructionTerm.tokensOfConstruction ct)
      val tokensInDecomposition = Decomposition.tokensOfDecomposition D
      val names = map CSpace.nameOfToken (tokensInDecomposition @ tokensInConstruction)
      fun mkRenameFunction _ [] = (fn _ => NONE)
        | mkRenameFunction Ns (y::ys) =
            let
              fun f x = if CSpace.sameTokens x y then SOME (CSpace.makeToken (firstUnusedName Ns) (CSpace.typeOfToken x))
                        else mkRenameFunction (CSpace.nameOfToken (Option.valOf (f y)) :: Ns) ys x
            in f
            end
      fun renameFunction x = if CSpace.sameToken x t then SOME t else mkRenameFunction names tokensInConstruction x
      val updatedConstruction = Pattern.applyPartialIsomorpism renameFunction ct
    in (Option.valOf o renameFunction, updatedConstruction)
    end

  exception CorrespondenceNotApplicable
  (* The following function takes a correspondence, corr, with construct relation Rc,
     and a goal assumed to have a superRelation Rg of Rc.
     The function will try to find a generator in the given source construction that matches
     the source pattern of corr. If found, it will use the isomorphic map (from pattern to generator)
     to rename the relationships between the vertices of the source specified by the correspondence.
     It will also rename the vertices of the target pattern so that they don't clash with the
     vertices in the decomposition.  *)
  fun instantiateCorrForStateAndGoal corr st goal =
    let
      val ([sourceToken],[targetToken],_) = Relation.tupleOfRelationship goal (* assumes Rc is subrelation of Rg*)
      val (rfs,rc) = Correspondence.relationshipsOf corr
      val (sc,tc,Rc) = rc
      val ct = State.constructionOf st
      val T = State.typeSystemOf st
      val patternDecomp = State.patternDecompOf st
      val (sourcePattern,targetPattern) = Correspondence.patternsOf corr
      val (targetRenamingFunction, updatedTargetPattern) = refreshNamesUpToConstruct targetPattern patternDecomp targetToken
      val (sourceRenamingFunction,matchingGenerator) = (case Pattern.findMapAndGeneratorForTokenMatching T ct sourceToken sourcePattern of (f,SOME x) => (Option.valOf o f,x) | (_,NONE) => raise CorrespondenceNotApplicable)
      fun updateRFs ((sfs,tfs,R)::rfs') = (map sourceRenamingFunction sfs, map targetRenamingFunction tfs, R) :: (updateRFs rfs')
        | updateRFs [] = []
      val updatedSourceRelationships = updateRFs rfs
      val updatedTargetRelationship = (sourceRenamingFunction sc, targetRenamingFunction tc, Rc)
    in Correspondence.declareCorrespondence matchingGenerator updatedTargetPattern updatedSourceRelationships updatedTargetRelationship
    end

  fun applyCorrespondenceForGoal st corr goal =
    let val ([sourceToken],[targetToken],Rg) = case Relation.tupleOfRelationship goal of
                                                  ([x],[y],R) => ([x],[y],R)
                                                | _ => raise CorrespondenceNotApplicable
        val (_,(_,_,Rc)) = Correspondence.relationshipsOf corr
        val _ = if Knowledge.subRelation (State.knowledgeOf st) (Rc,Rg) then () else raise CorrespondenceNotApplicable
        val instantiatedCorr = instantiateCorrForStateAndGoal corr st goal
        val (sourcePattern,targetPattern) = Correspondence.patternsOf instantiatedCorr
        val (rfs,rc) = Correspondence.relationshipsOf instantiatedCorr
        val patternDecomp = State.patternDecompOf st
        val updatedPatternDecomp = if Decomposition.isPlaceholder patternDecomp
                                   then Decomposition.initFromConstruction targetPattern
                                   else Decomposition.attachConstructionAt patternDecomp targetPattern targetToken
        val stateWithUpdatedGoals = State.replaceGoal st goal rfs
    in State.updatePatternDecomp stateWithUpdatedGoals updatedPatternDecomp
    end

  fun applyCorrespondence st corr =
    let fun applyCorrespondence' [] = []
          | applyCorrespondence' (g::gs) = (applyCorrespondenceForGoal st corr g handle CorrespondenceNotApplicable => st) :: applyCorrespondence' gs
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
