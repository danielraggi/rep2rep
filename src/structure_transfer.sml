import "search";
import "composition";

signature TRANSFER =
sig
  val applyCorrespondenceForGoal : State.T -> Correspondence.corr -> Relation.relationship -> State.T
  val applyCorrespondence : State.T -> Correspondence.corr -> State.T Seq.seq
  val unfoldState : State.T -> State.T Seq.seq
  val structureTransfer : Knowledge.base -> TypeSystem.typeSystem -> Construction.construction -> Relation.relationship list -> State.T Seq.seq

end;

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
      val tokensInConstruction = List.filter (fn x => not (CSpace.sameTokens t x)) (Construction.tokensOfConstruction ct)
      val tokensInComposition = Composition.tokensOfComposition D
      val names = map CSpace.nameOfToken (tokensInComposition @ tokensInConstruction)
      fun mkRenameFunction _ [] = (fn _ => NONE)
        | mkRenameFunction Ns (y::ys) =
            let
              fun f x = if CSpace.sameTokens x y then SOME (CSpace.makeToken (firstUnusedName Ns) (CSpace.typeOfToken x))
                        else mkRenameFunction (CSpace.nameOfToken (Option.valOf (f y)) :: Ns) ys x
            in f
            end
      fun renameFunction x = if CSpace.sameTokens x t then SOME t else mkRenameFunction names tokensInConstruction x
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
     vertices in the composition.  *)
  fun instantiateCorrForStateAndGoal corr st goal =
    let
      val (sourceToken,targetToken) = (case Relation.tupleOfRelationship goal of
                                          ([x],[y],_) => (x,y)
                                        | _ => raise CorrespondenceNotApplicable) (* assumes Rc is subrelation of Rg*)
      val (rfs,rc) = Correspondence.relationshipsOf corr
      val ct = State.constructionOf st
      val T = #typeSystem st
      val patternComp = State.patternCompOf st
      val (sourcePattern,targetPattern) = Correspondence.patternsOf corr
      val (targetRenamingFunction, updatedTargetPattern) = refreshNamesUpToConstruct targetPattern patternComp targetToken
      val (sourceRenamingFunction, matchingGenerator) =
            (case Pattern.findMapAndGeneratorMatchingForToken T ct sourcePattern sourceToken of
              (f,SOME x) => (Option.valOf o f,x)
            | (_,NONE) => raise CorrespondenceNotApplicable)
      fun updateRF (sfs,tfs,R) = (map sourceRenamingFunction sfs, map targetRenamingFunction tfs, R)
      val updatedSourceRelationships = map updateRF rfs
      val updatedTargetRelationship = updateRF rc
    in Correspondence.declareCorrespondence {sourcePattern=matchingGenerator,
                                              targetPattern=updatedTargetPattern,
                                              foundationRels=updatedSourceRelationships,
                                              constructRel=updatedTargetRelationship}
    end

  exception Error
  fun applyCorrespondenceForGoal st corr goal =
    let val (targetToken,Rg) = (case Relation.tupleOfRelationship goal of
                                  ([x],[y],R) => (y,R)
                                | _ => raise CorrespondenceNotApplicable)
        val (_,(_,_,Rc)) = Correspondence.relationshipsOf corr
        val instantiatedCorr = if Knowledge.subRelation (State.knowledgeOf st) Rc Rg
                               then instantiateCorrForStateAndGoal corr st goal
                               else raise CorrespondenceNotApplicable
        val (_,targetPattern) = Correspondence.patternsOf instantiatedCorr
        val (rfs,rc) = Correspondence.relationshipsOf instantiatedCorr
        val _ = if Relation.sameRelationship rc goal then () else raise Error
        val patternComp = State.patternCompOf st
        val updatedPatternComp = if Composition.isPlaceholder patternComp
                                   then Composition.initFromConstruction targetPattern
                                   else Composition.attachConstructionAt patternComp targetPattern targetToken
        val stateWithUpdatedGoals = State.replaceGoal st goal rfs
    in State.updatePatternComp stateWithUpdatedGoals updatedPatternComp
    end

  fun applyCorrespondence st corr =
    let fun ac [] = Seq.empty
          | ac (g::gs) = Seq.cons (applyCorrespondenceForGoal st corr g handle CorrespondenceNotApplicable => st) (ac gs)
    in ac (State.goalsOf st)
    end

  (*
  fun quickCorrFilter KB rships corrs =
    let fun f [] corr = false
          | f ((_,_,R)::rships) corr =
        let val (_,Rc) = Correspondence.relationsOf corr
        in Knowledge.subRelation KB Rc R orelse f rships corr
        end
    in FiniteSet.filter f corrs end
  *)

  fun unfoldState st =
    let val KB = State.knowledgeOf st
        val corrs = FiniteSet.toSeq (Knowledge.correspondencesOf KB)
        (*val CR = quickCorrFilter KB (State.goalsOf st) (Set.union rels corrs)*)
    in Seq.maps (applyCorrespondence st) corrs (*the returned sequence states is disjunctive; one must be satisfied *)
    end

  exception BadGoals
  (* every element of goals should be of the form ([vi1,...,vin],[vj1,...,vjm],R)*)
  fun structureTransfer KB T ct goals =
    let
      val initialState = State.make {typeSystem = T,
                                      construction = ct,
                                      goals = goals,
                                      composition = Composition.makePlaceholderComposition (CSpace.makeToken "dummy" TypeSystem.any),
                                      knowledge = KB}
      fun heuristic (st,st') = EQUAL
      val limit = 10
    in
      Search.sort unfoldState heuristic limit initialState
    end


end;
