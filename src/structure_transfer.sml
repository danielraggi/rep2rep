import "search";
import "state";

signature TRANSFER =
sig
  val applyCorrespondenceForGoal : State.T -> Correspondence.corr -> Relation.relationship -> State.T
  val applyCorrespondence : State.T -> Correspondence.corr -> State.T Seq.seq
  val unfoldState : State.T -> State.T Seq.seq
  val structureTransfer : Knowledge.base -> TypeSystem.typeSystem -> TypeSystem.typeSystem -> Construction.construction -> Relation.relationship -> int -> State.T Seq.seq

end;

structure Transfer : TRANSFER =
struct

  exception CorrespondenceNotApplicable
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
      val updatedConstruction = Pattern.applyMorpism renameFunction ct
    in (renameFunction, updatedConstruction)
    end

  exception Undefined
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
      val T = #sourceTypeSystem st
      val patternComp = State.patternCompOf st
      val (sourcePattern,targetPattern) = Correspondence.patternsOf corr
      val (targetRenamingFunction, updatedTargetPattern) = (refreshNamesUpToConstruct targetPattern patternComp targetToken
                                                            handle Undefined => raise CorrespondenceNotApplicable)
      val (sourceRenamingFunction, matchingGenerator) =
            (case Pattern.findMapAndGeneratorMatchingForToken T ct sourcePattern sourceToken of
                ((f,SOME x) :: _) => (f, x)
              | _ => raise CorrespondenceNotApplicable)
      fun updateConstructR (sfs,tfs,R) = (map (Option.valOf o sourceRenamingFunction) sfs,
                                          map (Option.valOf o targetRenamingFunction) tfs,
                                          R)
      fun funUnion (f::L) x = (* Here there's a check that the map is compatible on all the subconstructions *)
        (case (f x, funUnion L x) of
            (NONE,SOME y) => SOME y
          | (SOME y,NONE) => SOME y
          | (NONE,NONE) => NONE
          | (SOME y, SOME z) => if CSpace.sameTokens y z then SOME y else raise Undefined)
        | funUnion [] _ = NONE
      val f = Pattern.funUnion [sourceRenamingFunction,targetRenamingFunction]
      fun updateFoundationR (xfs,yfs,R) = (map (Option.valOf o f) xfs, map (Option.valOf o f) yfs, R)
      val updatedFoundationRelationships = map updateFoundationR rfs
      val updatedConstructRelationship = updateConstructR rc
    in Correspondence.declareCorrespondence {sourcePattern=matchingGenerator,
                                              targetPattern=updatedTargetPattern,
                                              foundationRels=updatedFoundationRelationships,
                                              constructRel=updatedConstructRelationship}
    end

  exception Error
  fun applyCorrespondenceForGoal st corr goal =
    let val (sourceToken,targetToken,Rg) = (case Relation.tupleOfRelationship goal of
                                              ([x],[y],R) => (x,y,R)
                                            | _ => raise CorrespondenceNotApplicable)
        val (stcs,ttcs,Rc) = (case Correspondence.relationshipsOf corr of (_,([x],[y],R)) => (x,y,R) | _ => raise Error)
        val sT = #sourceTypeSystem st
        val tT = #targetTypeSystem st
        val instantiatedCorr = if Knowledge.subRelation (State.knowledgeOf st) Rc Rg
                                  andalso Pattern.tokenMatches sT sourceToken stcs (* check order *)
                                  andalso Pattern.tokenMatches tT ttcs targetToken
                               then instantiateCorrForStateAndGoal corr st goal
                               else raise CorrespondenceNotApplicable
        val (_,targetPattern) = Correspondence.patternsOf instantiatedCorr
        val (rfs,rc) = Correspondence.relationshipsOf instantiatedCorr
        val patternComp = State.patternCompOf st
        val updatedPatternComp = if Composition.isPlaceholder patternComp
                                 then Composition.initFromConstruction targetPattern
                                 else Composition.attachConstructionAt patternComp targetPattern targetToken
        val stateWithUpdatedGoals = State.replaceGoal st goal rfs
    in State.updatePatternComp stateWithUpdatedGoals updatedPatternComp
    end

  fun applyCorrespondence st corr =
    let fun ac [] = Seq.empty
          | ac (g::gs) = (Seq.cons (applyCorrespondenceForGoal st corr g) (ac gs)
                            handle CorrespondenceNotApplicable => ac gs)
    in ac (State.goalsOf st)
    end

  exception RelationNotApplicable
  fun applyRelationshipForGoal st rel goal =
    let val (xgs,ygs,Rg) = Relation.tupleOfRelationship goal
        val (xs,ys,R) = Relation.tupleOfRelationship rel
        val sT = #sourceTypeSystem st
        val tT = #targetTypeSystem st
        val _ = if Knowledge.subRelation (State.knowledgeOf st) R Rg
                   andalso List.allZip (Pattern.tokenMatches sT) xgs xs (* check that this line makes sense semantically. I think it does if you interpret relations as being universally quantified on the source relative to the type. *)
                   andalso List.allZip (Pattern.tokenMatches tT) ys ygs
                then () else raise RelationNotApplicable
        val patternComp = State.patternCompOf st
        fun attachInstantiatedLeaves [y] [yg] =
              if Composition.isPlaceholder patternComp
              then Composition.initFromConstruction (Pattern.Source y)
              else Composition.attachConstructionAt patternComp (Pattern.Source y) yg
          | attachInstantiatedLeaves (y::Y) (yg::Yg) =
              Composition.attachConstructionAt (attachInstantiatedLeaves Y Yg) (Pattern.Source y) yg
          | attachInstantiatedLeaves _ _ = raise Error
        val updatedPatternComp = attachInstantiatedLeaves ys ygs
        val stateWithUpdatedGoals = State.replaceGoal st goal []
    in State.updatePatternComp stateWithUpdatedGoals updatedPatternComp
    end

  fun applyRelationship st rel =
    let fun ar [] = Seq.empty
          | ar (g::gs) = (Seq.cons (applyRelationshipForGoal st rel g) (ar gs)
                            handle RelationNotApplicable => ar gs)
    in ar (State.goalsOf st)
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
        val rels = FiniteSet.toSeq (Knowledge.relationshipsOf KB)
        (*val CR = quickCorrFilter KB (State.goalsOf st) (Set.union rels corrs)*)
    in Seq.append (Seq.maps (applyRelationship st) rels) (Seq.maps (applyCorrespondence st) corrs) (*the returned sequence states is disjunctive; one must be satisfied *)
    end

  exception BadGoal
  (* every element of goals should be of the form ([vi1,...,vin],[vj1,...,vjm],R)*)
  fun structureTransfer KB sourceT targetT ct goal limit =
    let
      val t = (case Relation.tupleOfRelationship goal of (_,[x],_) => x | _ => raise BadGoal)
      val initialState = State.make {sourceTypeSystem = sourceT,
                                      targetTypeSystem = targetT,
                                      construction = ct,
                                      goals = [goal],
                                      composition = Composition.makePlaceholderComposition t,
                                      knowledge = KB}
      fun heuristic (st,st') =
        let val gs = State.goalsOf st
            val gs' = State.goalsOf st'
            val D = State.patternCompOf st
            val D' = State.patternCompOf st'
        in Int.compare ((Composition.size D') * (length gs), (Composition.size D) * (length gs'))
        end
    in
      Search.sort unfoldState heuristic limit initialState
    end


end;
