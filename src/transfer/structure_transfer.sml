import "transfer.search";
import "transfer.heuristic";
import "util.logging";

signature TRANSFER =
sig
  type goal = Pattern.pattern
  val applyTransferSchemaForGoal : State.T -> InterCSpace.tSchemaData -> goal -> State.T
  val applyTransferSchema : State.T -> InterCSpace.tSchemaData -> State.T Seq.seq
  val singleStepTransfer : State.T -> State.T Seq.seq

  val structureTransfer : bool -> Pattern.pattern option -> State.T -> State.T Seq.seq
(*)
  val iterativeStructureTransfer : bool -> Pattern.pattern option
                                        -> State.T -> State.T Seq.seq*)
(*)
  val targetedTransfer : Pattern.pattern
                            -> State.T -> State.T Seq.seq*)

  val masterTransfer : bool -> bool
                            -> Pattern.pattern option
                            -> State.T -> State.T Seq.seq

  val applyTransfer:
      CSpace.conSpecData -> (* Source Constructor Specification *)
      CSpace.conSpecData -> (* Target Constructor Specification *)
      CSpace.conSpecData -> (* Inter-space Constructor Specification *)
      Knowledge.base -> (* Transfer and Inference schemas *)
      Construction.construction -> (* The construction to transform *)
      Construction.construction -> (* The goal to satisfy *)
      Construction.construction list (* Your new transformed structure graph :-) *)
end;

structure Transfer : TRANSFER =
struct

  type goal = Pattern.pattern
  exception TransferSchemaNotApplicable
  exception Error

  fun firstUnusedName Ns =
        let fun mkFun n =
              let val vcandidate = "v_{"^(Int.toString n)^"}"
              in if FiniteSet.exists (fn x => x = vcandidate) Ns
                 then mkFun (n+1)
                 else vcandidate
              end
        in mkFun 0
        end
  (*  *)
  fun applyMorphismRefreshingNONEs given avoid CTs =
      let fun mkRenameFunction Ns Tks =
            let val (y,ys) = FiniteSet.pull Tks
                fun f x =
                  if CSpace.sameTokens x y
                  then SOME (CSpace.makeToken (firstUnusedName Ns) (CSpace.typeOfToken x))
                  else mkRenameFunction (CSpace.nameOfToken (Option.valOf (f y)) :: Ns) ys x
            in f
            end handle Empty => (fn _ => NONE)
          fun joinToks (x,y) = FiniteSet.union (Construction.tokensOfConstruction x) y
          val tokensInConstructions = foldl joinToks FiniteSet.empty CTs
          val names = FiniteSet.map CSpace.nameOfToken avoid
          fun renameFunction x =
              (case given x of
                  SOME y => SOME y
                | NONE => mkRenameFunction names tokensInConstructions x)
          val updatedConstructions = map (Pattern.applyMorphism renameFunction) CTs
      in (renameFunction, updatedConstructions)
      end

  (*  *)
  fun refreshNamesOfConstruction ct avoid =
    (case applyMorphismRefreshingNONEs (fn _ => NONE) avoid [ct] of
        (f,[x]) => (f,x)
      | _ => raise Error)


  exception InferenceSchemaNotApplicable
  fun applyInferenceSchemaForGoal st T idT ct ischData goal =
  let val {name,contextConSpecN,idConSpecN,iSchema} = ischData
      val {antecedent,consequent,context} = iSchema
      fun referenced x =
        FiniteSet.elementOf x (Construction.tokensOfConstruction context) orelse
        FiniteSet.exists (fn y => FiniteSet.elementOf x (Construction.tokensOfConstruction y)) antecedent
      val givenTokens = FiniteSet.filter referenced (Construction.tokensOfConstruction consequent)

      val (consequentMap, updatedConsequent) =
          (case Pattern.findEmbeddingUpTo idT givenTokens consequent goal of
                (f,_,SOME x) => (f,x)
              | _ => raise InferenceSchemaNotApplicable)

      val (contextMap, matchingSubConstruction) =
            (case Seq.pull (Pattern.findEmbeddingsOfSubConstructionWithCompatibleInverse T ct context consequentMap) of
                SOME ((_,f,x),_) => (f,x)
              | _ => raise InferenceSchemaNotApplicable)

      val usedTokens = FiniteSet.union
                          (State.tokensInUse st)
                          (Pattern.tokensOfConstruction updatedConsequent)
      val ccMap = Pattern.funUnion CSpace.sameTokens [consequentMap, contextMap]
      val (_,updatedAntecedent) = applyMorphismRefreshingNONEs ccMap usedTokens antecedent

      val goals = State.goalsOf st
      val updatedGoals = updatedAntecedent @ List.filter (fn x => not (Pattern.same goal x)) goals

      val instantiatedISchema = {antecedent = updatedAntecedent,
                                 consequent = updatedConsequent,
                                 context = matchingSubConstruction}
      val instantiatedISchemaData = {name = name,
                                     contextConSpecN = contextConSpecN,
                                     idConSpecN = idConSpecN,
                                     iSchema = instantiatedISchema}
      val transferProof = State.transferProofOf st
      val updatedTransferProof = TransferProof.attachISchemaAt instantiatedISchemaData goal transferProof

      val updatedState = State.updateTransferProof updatedTransferProof (State.updateGoals updatedGoals st)
  in updatedState
  end handle Pattern.IllDefined => raise InferenceSchemaNotApplicable

  (* The following function takes a tSchema, tsch, and a goal assumed to be
     matched by the consequent of tsch (up to the tokens of the original construction).
     The function will try to find a generator in the given source construction that matches
     the source pattern of tsch. If found, it will use the isomorphic map (from pattern to generator)
     to rename the relationships between the vertices of the source specified by the tSchema.
     It will also rename the vertices of the target pattern so that they don't clash with the
     vertices in the composition.  *)
  fun instantiateTransferSchema st tsch goal =
    let
      val {antecedent,consequent,source,target} = tsch

      val patternComps = State.patternCompsOf st
      val targetTokens = FiniteSet.intersection (Pattern.tokensOfConstruction goal)
                                                (Composition.tokensOfCompositions patternComps)
      val tTSD = State.targetTypeSystemOf st
      val tT = #typeSystem tTSD

      val ct = State.constructionOf st
      val T = #typeSystem (State.sourceTypeSystemOf st)
      val interTSD = (State.interTypeSystemOf st)
      val sourceConSpecData = #sourceConSpecData st
      val targetConSpecData = #targetConSpecData st
      val interConSpecData = #interConSpecData st

      fun preferentialFunUnion f g x = (case g x of NONE => f x | SOME y => SOME y)
      fun partialFunComp1 f g x = (case g x of NONE => f x | SOME y => f y)
      fun partialFunComp2 f g x = (case g x of NONE => f x
                                             | SOME y => (case f y of NONE => SOME y
                                                                            | SOME z => SOME z))
      fun funComp f g x = (case g x of NONE => NONE | SOME y => f y)

      fun referenced x =
        FiniteSet.elementOf x (Construction.tokensOfConstruction source) orelse
        FiniteSet.elementOf x (Construction.tokensOfConstruction target) orelse
        FiniteSet.exists (fn y => FiniteSet.elementOf x (Construction.tokensOfConstruction y)) antecedent

      val givenTokens = FiniteSet.filter referenced (Construction.tokensOfConstruction consequent)

      (* val partiallyMappedConsequent = Pattern.applyPartialMorphism targetConstructMap consequent*)
      val (consequentMap,goalMap,typeVarMap,newgoal) =
            (case Pattern.findEmbeddingMinimisingTypeUpTo interTSD givenTokens consequent goal of
                (f,g,vf,SOME ng) => (f,g,vf,ng)
              | _ => raise TransferSchemaNotApplicable)
      val _ = if Pattern.wellFormed interConSpecData newgoal then () else raise TransferSchemaNotApplicable
      val source = Pattern.applyTypeVarInstantiation typeVarMap source
      val _ = if Pattern.wellFormed sourceConSpecData source then () else raise TransferSchemaNotApplicable
      val target = Pattern.applyTypeVarInstantiation typeVarMap target
      val _ = if Pattern.wellFormed targetConSpecData target then () else raise TransferSchemaNotApplicable
      val antecedent = map (Pattern.applyTypeVarInstantiation typeVarMap) antecedent
      val _ = if List.all (Pattern.wellFormed interConSpecData) antecedent then () else raise TransferSchemaNotApplicable
      val targetConstruct = Pattern.constructOf target
      val usedTokenNames = map CSpace.nameOfToken (State.tokensInUse st)

      val freshName = firstUnusedName usedTokenNames

      fun makeAttachmentToken tt =
          CSpace.makeToken freshName
                           (valOf (Type.greatestCommonSubType tTSD (CSpace.typeOfToken tt) (CSpace.typeOfToken targetConstruct)))
                           handle Option => raise TransferSchemaNotApplicable
      val newTargetConstruct =
          if FiniteSet.isEmpty targetTokens
          then CSpace.makeToken freshName (CSpace.typeOfToken targetConstruct)
          else (case FiniteSet.pull targetTokens of (tt,H) =>
                  if FiniteSet.isEmpty H
                  then makeAttachmentToken tt
                  else raise TransferSchemaNotApplicable
                )

      val usedTokens = FiniteSet.insert newTargetConstruct (State.tokensInUse st)
      fun targetConstructMap x =
        if CSpace.sameTokens x targetConstruct
        then SOME newTargetConstruct
        else NONE

      val (sourceMap, matchingSubConstruction) =
            (case Seq.pull (Pattern.findEmbeddingsOfSubConstructionWithCompatibleInverse T ct source consequentMap) of
                SOME ((_,f,x),_) => (f, x)
              | _ => raise TransferSchemaNotApplicable)

      val updatedConsequent = Pattern.applyMorphism consequentMap consequent
      val csMap = Pattern.funUnion CSpace.sameTokens [sourceMap, consequentMap]
      val usedTokensC = FiniteSet.union usedTokens (Pattern.tokensOfConstruction updatedConsequent)

      val (targetMap, updatedTarget) =
        let val (f,_) = applyMorphismRefreshingNONEs csMap usedTokensC [target]
            val tmap = preferentialFunUnion f targetConstructMap
        in (tmap, Pattern.applyMorphism tmap target)
        end

      fun compositionMap x = if FiniteSet.elementOf x targetTokens then SOME newTargetConstruct else NONE

      val cstMap = preferentialFunUnion csMap targetMap
      val usedTokensCT = FiniteSet.union usedTokensC (Construction.tokensOfConstruction updatedTarget)

      val (_,updatedAntecedent) = applyMorphismRefreshingNONEs cstMap usedTokensCT antecedent
    in
      (preferentialFunUnion goalMap compositionMap,
       InterCSpace.declareTransferSchema {source = matchingSubConstruction,
                                          target = updatedTarget,
                                          antecedent = updatedAntecedent,
                                          consequent = updatedConsequent})
    end

(*
  fun applyTransferSchemaAsInferenceSchemaForGoal st tsch goal =
    let val {antecedent,consequent,source,target,name} = tsch

        fun referenced x =
          FiniteSet.elementOf x (Construction.tokensOfConstruction source) orelse
          FiniteSet.elementOf x (Construction.tokensOfConstruction target) orelse
          FiniteSet.exists (fn y => FiniteSet.elementOf x (Construction.tokensOfConstruction y)) antecedent
        val givenTokens = FiniteSet.filter referenced (Construction.tokensOfConstruction consequent)

        val patternComps = State.patternCompsOf st
        val ct = State.constructionOf st
        val T = #typeSystem (State.sourceTypeSystemOf st)
        val tT = #typeSystem (State.targetTypeSystemOf st)
        val interT = #typeSystem (State.interTypeSystemOf st)

        val targetTokens = FiniteSet.intersection (Pattern.tokensOfConstruction goal)
                                                  (Composition.tokensOfCompositions patternComps)

        val (consequentMap,inverseConsequentMap) =
              (case Pattern.findEmbeddingUpTo interT givenTokens consequent goal of
                  (f,g,SOME x) => (f,g)
                | _ => raise TransferSchemaNotApplicable)

        val (sourceMap, matchingSubConstruction) =
              (case Seq.pull (Pattern.findEmbeddingsOfSubConstructionWithCompatibleInverse T ct source consequentMap) of
                  SOME ((_,f,x),_) => (f, x)
                | _ => raise TransferSchemaNotApplicable)

        val csMap = Pattern.funUnion [consequentMap,sourceMap]

        fun getTargetEmbedding [] = raise TransferSchemaNotApplicable
          | getTargetEmbedding (tct::L) =
            (case Seq.pull (Pattern.findEmbeddingsOfSubConstructionWithCompatibleInverse tT tct target csMap) of
                SOME ((_,f,x),_) => (f, x)
              | _ => getTargetEmbedding L)

        val targetConstructions = List.maps Composition.resultingConstructions patternComps
        val (targetMap, matchingTargetConstruction) =
              getTargetEmbedding targetConstructions

        val cstMap = Pattern.funUnion [csMap,targetMap]
        val usedTokens = State.tokensInUse st
        val (_,updatedAntecedent) = applyMorphismRefreshingNONEs cstMap usedTokens antecedent

        val goals = State.goalsOf st
        val updatedGoals = updatedAntecedent @ List.filter (fn x => not (Pattern.same goal x)) goals

        val updatedTSchema = {name = name ^ "_asISchema",
                              consequent = goal,
                              antecedent = updatedAntecedent,
                              source = matchingSubConstruction,
                              target = matchingTargetConstruction}
        val transferProof = State.transferProofOf st
        val updatedTransferProof = TransferProof.attachTSchemaAt updatedTSchema goal transferProof

        val updatedState = State.updateTransferProof updatedTransferProof
                                (State.updateGoals updatedGoals st)

    in updatedState
    end handle Pattern.IllDefined => raise TransferSchemaNotApplicable
*)

  fun applyTransferSchemaForGoal st tschData goal =
    let val {name,sourceConSpecN,targetConSpecN,interConSpecN,tSchema} = tschData
        val (stateRenaming,instantiatedTSchema) = instantiateTransferSchema st tSchema goal

        val patternComps = State.patternCompsOf st
        val renamedPatternComps = map (Composition.applyPartialMorphism stateRenaming) patternComps
        val updatedPatternComps =
            Composition.attachConstructions renamedPatternComps [#target instantiatedTSchema]

        val goals = State.goalsOf st
        val updatedGoals = #antecedent instantiatedTSchema @ map (Pattern.applyPartialMorphism stateRenaming) (List.filter (fn x => not (Pattern.same goal x)) goals)

        val instantiatedTSchemaData = {name = name,
                                        sourceConSpecN = sourceConSpecN,
                                        targetConSpecN = targetConSpecN,
                                        interConSpecN = interConSpecN,
                                        tSchema = instantiatedTSchema}
        val transferProof = State.transferProofOf st
        val updatedTransferProof = TransferProof.attachTSchemaAt instantiatedTSchemaData goal transferProof

        val updatedState = State.applyPartialMorphismToProof stateRenaming
                              (State.updateTransferProof updatedTransferProof
                                  (State.updateGoals updatedGoals
                                      (State.updatePatternComps updatedPatternComps st)))
    in updatedState
    end

  fun idempotencyOnGoals st =
    let fun rg (g::gs) =
            let val (keep,dump) = rg gs
            in if List.exists (Construction.same g) keep
               then (keep,g::dump)
               else (g::keep,dump)
            end
          | rg [] = ([],[])
        fun updateTransferProof (g::gs) = TransferProof.dump "idempotency" g (updateTransferProof gs)
          | updateTransferProof [] = State.transferProofOf st
        val (keep,dump) = rg (State.goalsOf st)
        val stateWithUpdatedGoals = State.updateGoals keep st
    in State.updateTransferProof (updateTransferProof dump) stateWithUpdatedGoals
    end

  fun applyTransferSchema st tschData =
    let val newSt = idempotencyOnGoals st
        val ct = State.constructionOf st
      (*)  fun tac1 g = (Seq.single (applyTransferSchemaAsInferenceSchemaForGoal newSt tschData g)) handle TransferSchemaNotApplicable => Seq.empty
        fun tac2 g = (Seq.single (applyTransferSchemaForGoal newSt tschData g)) handle TransferSchemaNotApplicable => Seq.empty*)
        fun tac3 g = (*)(applyTransferSchemaAsInferenceSchemaForGoal newSt tschData g)
                      handle TransferSchemaNotApplicable =>*) applyTransferSchemaForGoal newSt tschData g
        fun ac [] = Seq.empty
          | ac (g::gs) = Seq.cons (tac3 g) (ac gs) handle TransferSchemaNotApplicable => ac gs
        (*)  | ac (g::gs) = (Seq.append (Seq.append (tac1 g) (tac2 g)) (ac gs))*)
    in ac (State.goalsOf newSt)
    end

  fun applyInferenceSchema st ischData =
    let val newSt = idempotencyOnGoals st
        val ct = State.constructionOf newSt
        val T = #typeSystem (State.targetTypeSystemOf newSt)
        val idT = #typeSystem (State.interTypeSystemOf newSt)
        val pcts = List.maps Composition.resultingConstructions (State.patternCompsOf newSt)
        fun appToTargetConstructions [] _ = Seq.empty
          | appToTargetConstructions (h::L) g =
              (Seq.single (applyInferenceSchemaForGoal newSt T idT h ischData g))
                handle InferenceSchemaNotApplicable => appToTargetConstructions L g
        fun ac [] = Seq.empty
          | ac (g::gs) =
              (Seq.append (appToTargetConstructions pcts g) (ac gs))
                handle InferenceSchemaNotApplicable => (ac gs)
    in ac (State.goalsOf newSt)
    end

  fun singleStepTransfer st =
    let val tschs = Knowledge.transferSchemasOf (State.knowledgeOf st)
    in Seq.maps (applyTransferSchema st) tschs
    end

  fun singleStepInference st =
    let val ischs = Knowledge.inferenceSchemasOf (State.knowledgeOf st)
    in Seq.maps (applyInferenceSchema st) ischs
    end

  val transferElseInfer =  Seq.ORELSE (singleStepTransfer,singleStepInference)

  fun structureTransferTac h ign forget state =
      (*Search.breadthFirstSortAndIgnore transferElseInfer h ign forget state*)
      (*Search.breadthFirstSortIgnoreForget transferElseInfer h ign forget state*)
      (*Search.depthFirstSortAndIgnore transferElseInfer h ign forget state*)
      (*Search.depthFirstSortIgnoreForget transferElseInfer h ign forget state*)
      (*Search.bestFirstSortAndIgnore transferElseInfer h ign forget state*)
      Search.bestFirstSortIgnoreForget transferElseInfer h ign forget state


  exception Nope

  fun constructionOfComp st =
    (case List.maps Composition.resultingConstructions (State.patternCompsOf st) of
        [c] => c
      | _ => raise Nope)
  fun withinTarget targetTypeSystem targetPattern st =
    (Pattern.hasUnifiableGenerator targetTypeSystem targetPattern (constructionOfComp st))
      handle Nope => false
  fun matchesTarget targetTypeSystem targetPattern st =
    (Pattern.matches targetTypeSystem (constructionOfComp st) targetPattern)
      handle Nope => false


fun structureTransfer unistructured targetPattOption st =
  let val ignI = Heuristic.ignoreRelaxed 10 199
      val ignT = Heuristic.ignore 15 199 45 unistructured
      val targetTypeSystem = #typeSystem (State.targetTypeSystemOf st)
      fun ignPT (x,L) = case targetPattOption of
                      SOME tpt => not (withinTarget targetTypeSystem tpt x) orelse ignT (x,L)
                    | NONE => ignT (x,L)
      fun fgtPT (x,L) = case targetPattOption of
                      SOME tpt => not (matchesTarget targetTypeSystem tpt x) orelse Heuristic.forgetRelaxed (x,L)
                    | NONE => Heuristic.forgetRelaxed (x,L)
      val tac = structureTransferTac Heuristic.transferProofMain ignPT fgtPT
  in tac st
  end

  fun v2t t =
    let val tok = CSpace.nameOfToken t
        val typ = CSpace.typeOfToken t
        fun vt (x::xs) = if x = #"v" then #"t"::xs else x::xs
          | vt [] = []
    in SOME (CSpace.makeToken (String.implode (vt (String.explode tok))) typ)
    end

(*
  fun iterativeStructureTransfer unistructured targetPatternOption initialState =
    let
      fun updateState (C as {composition,goals,...}) =
        let val newConstruction = (case Composition.resultingConstructions composition of
                                      [c] => Pattern.applyMorphism v2t c
                                    | _ => raise Nope)
            val newConstruct = Construction.constructOf newConstruction
            val newGoal = Relation.makeRelationship ([newConstruct],y,R)
            val _ = if length goals > 0 then raise Nope else ()
        in State.make {sourceConSpecData = #sourceConSpecData initialState,
                      targetConSpecData = #targetConSpecData initialState,
                      interConSpecData = #interConSpecData initialState,
                      transferProof = TransferProof.ofPattern newGoal,
                      construction = newConstruction,
                      originalGoal = newGoal,
                      goals = [newGoal],
                      compositions = [Composition.makePlaceholderComposition newConstruct],
                      knowledge = KB} handle Nope => (print "nope!\n";C)
        end
      fun ign (st,L) = List.exists (fn x => Heuristic.similarGoalsAndComps (x, st)) L
      val ignST = Heuristic.ignore 15 1999 45 unistructured
      fun forget (st,L) = (case targetPatternOption of
                              SOME targetPattern => not (matchesTarget typeSystem targetPattern st)
                            | NONE => false)
      fun forgetST (st,L) = Heuristic.forgetStrict (st,L)
      fun orderResults s =
        case Seq.pull s of
          SOME (x,xq) => Seq.insertManyNoRepetition x (orderResults xq) Heuristic.transferProofMultStrengths Heuristic.similarGoalsAndComps
        | NONE => Seq.empty
      val ST = Seq.take 10 o (structureTransferTac Heuristic.transferProofMultStrengths ignST forgetST)
      val results = Seq.map (Search.bestFirstSortIgnoreForget (ST o updateState) Heuristic.transferProofMultStrengths ign forget) (ST initialState)
    in orderResults results
    end*)
(*
  fun targetedTransferTac h ign forget targetPattern state =
    let val targetTypeSystem = #typeSystem (State.targetTypeSystemOf state)
        fun forget' (st,L) = not (matchesTarget targetTypeSystem targetPattern st) orelse forget (st,L)
        fun ign' (st,L) = not (withinTarget targetTypeSystem targetPattern st) orelse ign (st,L)
    in Search.bestFirstSortIgnoreForget singleStepTransfer h ign' forget' state
    end

  fun targetedTransfer targetPattern st =
    let val ign = Heuristic.ignoreRelaxed 10 199
    in targetedTransferTac Heuristic.transferProofMultStrengths ign Heuristic.forgetStrict targetPattern st
    end*)

  fun masterTransfer iterative unistructured targetPattOption st =
    structureTransfer unistructured targetPattOption st
  (*  if iterative
    then iterativeStructureTransfer unistructured targetPattOption st
    else*) (*
          (case targetPattOption of
              NONE => structureTransfer unistructured st
            | SOME targetPattern => targetedTransfer targetPattern st)*)


  fun applyTransfer sCSD tCSD iCSD KB ct goal =
      let val tTS = #typeSystem (#typeSystemData tCSD)
          val targetTokens = FiniteSet.filter
                                 (fn x => Set.elementOf (CSpace.typeOfToken x) (#Ty tTS))
                                 (Construction.leavesOfConstruction goal);
          val st = State.make {sourceConSpecData = sCSD,
                               targetConSpecData = tCSD,
                               interConSpecData = iCSD,
                               transferProof = TransferProof.ofPattern goal,
                               construction = ct,
                               originalGoal = goal,
                               goals = [goal],
                               compositions = map Composition.makePlaceholderComposition targetTokens,
                               knowledge = Knowledge.filterForISpace (#name iCSD) KB}
          val stateSeq = structureTransfer false NONE st;
          fun getStructureGraph st =
              List.flatmap (Composition.resultingConstructions) (State.patternCompsOf st);
          val firstState = Seq.hd stateSeq;
          val _ = print("UNCLOSED GOALS: " ^ Int.toString(List.length(State.goalsOf firstState)) ^ "\n");
          val structureGraph = getStructureGraph firstState;
      in structureGraph end
end;
