import "transfer.search";
import "transfer.heuristic";
import "util.logging";

signature TRANSFER =
sig
  type goal = Pattern.pattern
  val applyTransferSchemaForGoal : State.T -> InterCSpace.tSchemaData -> goal -> State.T
  val applyTransferSchema : State.T -> InterCSpace.tSchemaData -> State.T Seq.seq
  val singleStepTransfer : State.T -> State.T Seq.seq

  val structureTransfer : int option * int option * int option -> bool -> bool -> Pattern.pattern option -> State.T -> State.T Seq.seq
  val quickTransfer : int option * int option * int option -> bool -> Pattern.pattern option -> State.T -> State.T Seq.seq
(*)
  val iterativeStructureTransfer : bool -> Pattern.pattern option
                                        -> State.T -> State.T Seq.seq*)
(*)
  val targetedTransfer : Pattern.pattern
                            -> State.T -> State.T Seq.seq*)

  val masterTransfer : int option * int option * int option
                          -> bool
                          -> bool
                          -> bool
                          -> Pattern.pattern option
                          -> State.T
                          -> State.T Seq.seq

  val initState : CSpace.conSpecData -> (* Source Constructor Specification *)
                  CSpace.conSpecData -> (* Target Constructor Specification *)
                  CSpace.conSpecData -> (* Inter-space Constructor Specification *)
                  bool -> (* use inverse transfer schemas *)
                  Knowledge.base -> (* Transfer and Inference schemas *)
                  Construction.construction -> (* The construction to transform *)
                  Construction.construction -> (* The goal to satisfy *)
                  State.T
  val applyTransfer:
      CSpace.conSpecData -> (* Source Constructor Specification *)
      CSpace.conSpecData -> (* Target Constructor Specification *)
      CSpace.conSpecData -> (* Inter-space Constructor Specification *)
      Knowledge.base -> (* Transfer and Inference schemas *)
      Construction.construction -> (* The construction to transform *)
      Construction.construction -> (* The goal to satisfy *)
      (Construction.construction list, Diagnostic.t list) Result.t (* Your new transformed structure graph :-) *)
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
  let val {name,contextConSpecN,idConSpecN,iSchema,strength} = ischData
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
                SOME ((_,f,_,x),_) => (f,x)
              | _ => raise InferenceSchemaNotApplicable)

      val usedTokens = FiniteSet.union
                          (State.tokensInUse st)
                          (Pattern.tokensOfConstruction updatedConsequent)
      val ccMap = Pattern.funUnion CSpace.sameTokens [consequentMap, contextMap]
      val (_,updatedAntecedent) = applyMorphismRefreshingNONEs ccMap usedTokens antecedent

      val goals = State.goalsOf st
      val updatedGoals = List.merge Pattern.compare
                                    updatedAntecedent
                                    (List.filter (fn x => not (Pattern.same goal x)) goals)

      val instantiatedISchema = {antecedent = updatedAntecedent,
                                 consequent = updatedConsequent,
                                 context = matchingSubConstruction}
      val instantiatedISchemaData = {name = name,
                                     contextConSpecN = contextConSpecN,
                                     idConSpecN = idConSpecN,
                                     iSchema = instantiatedISchema,
                                     strength = strength}
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
      val interTSD = State.interTypeSystemOf st
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
          not (Type.isTypeVar (CSpace.typeOfToken x)) andalso
          (FiniteSet.elementOf x (Construction.tokensOfConstruction source) orelse
           FiniteSet.elementOf x (Construction.tokensOfConstruction target) orelse
           FiniteSet.elementOf x (FiniteSet.maps Construction.tokensOfConstruction antecedent))

      val givenTokens = FiniteSet.filter referenced (Construction.tokensOfConstruction consequent)

      val (consequentMap,goalMap,typeVarMap,newgoal) =
            (case Pattern.findEmbeddingMinimisingTypeUpTo interTSD givenTokens consequent goal of
                (f,g,vf,SOME ng) => (f,g,vf,ng)
              | _ => raise TransferSchemaNotApplicable)
      (*val _ = if Pattern.wellFormed interConSpecData newgoal then () else raise TransferSchemaNotApplicable*)
      val source = Pattern.applyTypeVarInstantiation typeVarMap source
      (*val _ = if Pattern.wellFormed sourceConSpecData source then () else raise TransferSchemaNotApplicable*)
      val target = Pattern.applyTypeVarInstantiation typeVarMap target
      (*val _ = if Pattern.wellFormed targetConSpecData target then () else raise TransferSchemaNotApplicable*)
      val antecedent = map (Pattern.applyTypeVarInstantiation typeVarMap) antecedent
      (*val _ = if List.all (Pattern.wellFormed interConSpecData) antecedent then () else raise TransferSchemaNotApplicable*)
      fun updateCMap [] = consequentMap
        | updateCMap (tk::tks) =
        let val f' = updateCMap tks
        in fn x => (case (typeVarMap (CSpace.typeOfToken tk), consequentMap tk) of
                        (SOME ityp, mtk) => (if Type.equal (CSpace.typeOfToken x) ityp andalso CSpace.nameOfToken tk = CSpace.nameOfToken x then mtk else f' x)
                      | _ => f' x)
        end
      val consequentMap = updateCMap (Construction.tokensOfConstruction consequent)

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

      val (sourceMap, consVarMap, matchingSubConstruction) =
            (case Seq.pull (Pattern.findEmbeddingsOfSubConstructionWithCompatibleInverse T ct source consequentMap) of
                SOME ((_,f,cf,x),_) => (f,cf,x)
              | _ => raise TransferSchemaNotApplicable)

      val target = Pattern.applyConsVarInstantiation consVarMap target

      val updatedConsequent = Pattern.applyMorphism consequentMap consequent
      val csMap = Pattern.funUnion CSpace.sameTokens [sourceMap, consequentMap]
      val usedTokensC = FiniteSet.union usedTokens (Pattern.tokensOfConstruction updatedConsequent)

      fun getTargetEmbedding [] = NONE
        | getTargetEmbedding (tct::L) =
          (case Seq.pull (Pattern.findEmbeddingsOfSubConstructionWithCompatibleInverse tT tct target csMap) of
              SOME ((_,f,_,x),_) => SOME (f, x)
            | _ => getTargetEmbedding L)
      val targetConstructions = List.maps Composition.resultingConstructions patternComps
      val (targetReifiedByComposition,targetMap,updatedTarget) =
        (case getTargetEmbedding targetConstructions of
            SOME (f,_) =>
              let val tmap = preferentialFunUnion f targetConstructMap
              in (true,tmap,Pattern.applyMorphism tmap target)
              end
          | NONE =>
              let val (f,_) = applyMorphismRefreshingNONEs csMap usedTokensC [target]
                  val tmap = preferentialFunUnion f targetConstructMap
              in (false,tmap, Pattern.applyMorphism tmap target)
              end)

      fun compositionMap x = if FiniteSet.elementOf x targetTokens then SOME newTargetConstruct else NONE

      val cstMap = preferentialFunUnion csMap targetMap
      val usedTokensCT = FiniteSet.union usedTokensC (Construction.tokensOfConstruction updatedTarget)

      val (_,updatedAntecedent) = applyMorphismRefreshingNONEs cstMap usedTokensCT antecedent
    in
      (targetReifiedByComposition,
       preferentialFunUnion goalMap compositionMap,
       InterCSpace.declareTransferSchema {source = matchingSubConstruction,
                                          target = updatedTarget,
                                          antecedent = updatedAntecedent,
                                          consequent = updatedConsequent})
    end


  fun applyTransferSchemaForGoal st tschData goal =
    let val {name,sourceConSpecN,targetConSpecN,interConSpecN,tSchema,strength} = tschData
        val (targetReifiedByComposition,stateRenaming,instantiatedTSchema) = instantiateTransferSchema st tSchema goal

        val patternComps = State.patternCompsOf st
        val renamedPatternComps = map (Composition.applyPartialMorphism stateRenaming) patternComps
        val updatedPatternComps = if targetReifiedByComposition then renamedPatternComps else
            Composition.attachConstructions renamedPatternComps [#target instantiatedTSchema]

        val goals = State.goalsOf st
        val updatedGoals = List.merge Pattern.compare
                                      (#antecedent instantiatedTSchema)
                                      (map (Pattern.applyPartialMorphism stateRenaming) (List.filter (fn x => not (Pattern.same goal x)) goals))

        val instantiatedTSchemaData = {name = name,
                                        sourceConSpecN = sourceConSpecN,
                                        targetConSpecN = targetConSpecN,
                                        interConSpecN = interConSpecN,
                                        tSchema = instantiatedTSchema,
                                        strength = strength}
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
        fun ac [] = Seq.empty
          | ac (g::gs) = Seq.cons (applyTransferSchemaForGoal newSt tschData g) (ac gs)
                          handle TransferSchemaNotApplicable => ac gs
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

  fun structureTransferTac h ign forget stop state =
      (*Search.breadthFirstIgnore transferElseInfer ign state*)
      (*Search.breadthFirstIgnoreForget transferElseInfer ign forget state*)
      (*Search.depthFirstIgnore transferElseInfer ign state*)
      (*Search.depthFirstIgnoreForget transferElseInfer ign forget state*)
      (*Search.bestFirstIgnore transferElseInfer h ign state*)
      (*Search.bestFirstIgnoreForget transferElseInfer h ign forget state*)
      Search.bestFirstAll transferElseInfer h ign forget stop state

  fun quickTransferTac ign forget stop state =
      Search.depthFirstIgnore transferElseInfer ign stop state

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


fun structureTransfer (goalLimit,compositionLimit,searchLimit) eager unistructured targetPattOption st =
  let val maxNumGoals = case goalLimit of SOME x => x | NONE => 15
      val maxCompSize = case compositionLimit of SOME x => x | NONE => 400
      val maxNumResults = case searchLimit of SOME x => x | NONE => 2000
      val ignT = Heuristic.ignore maxNumGoals maxNumResults maxCompSize unistructured
      val targetTypeSystem = #typeSystem (State.targetTypeSystemOf st)
      fun ignPT (x,L) = case targetPattOption of
                      SOME tpt => not (withinTarget targetTypeSystem tpt x) orelse ignT (x,L)
                    | NONE => ignT (x,L)
      fun fgtPT (x,L) = case targetPattOption of
                      SOME tpt => not (matchesTarget targetTypeSystem tpt x) (*orelse
                                  Heuristic.forgetRelaxed (x,L)*)
                    | NONE => false (*Heuristic.forgetRelaxed (x,L)*)
      val stop = if eager then (fn x => null (State.goalsOf x)) else (fn _ => false)
      val tac = structureTransferTac Heuristic.transferProofMain ignPT fgtPT stop
  in tac st
  end

  fun quickTransfer (goalLimit,compositionLimit,searchLimit) unistructured targetPattOption st =
    let val maxNumGoals = case goalLimit of SOME x => x | NONE => 15
        val maxCompSize = case compositionLimit of SOME x => x | NONE => 200
        val maxNumResults = case searchLimit of SOME x => x | NONE => 1000
        val ignT = Heuristic.ignore maxNumGoals maxNumResults maxCompSize unistructured
        val targetTypeSystem = #typeSystem (State.targetTypeSystemOf st)
        fun ignPT (x,L) = case targetPattOption of
                        SOME tpt => not (withinTarget targetTypeSystem tpt x) orelse ignT (x,L)
                      | NONE => ignT (x,L)
        fun fgtPT (x,L) = case targetPattOption of
                        SOME tpt => not (matchesTarget targetTypeSystem tpt x) (*orelse
                                    Heuristic.forgetRelaxed (x,L)*)
                      | NONE => false (*Heuristic.forgetRelaxed (x,L)*)
        val stop = (fn x => null (State.goalsOf x))
        val tac = quickTransferTac ignPT fgtPT stop
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
   TODO : recoding an iterative structure transfer would be nice
*)

  fun masterTransfer limits eager iterative unistructured targetPattOption st =
    structureTransfer limits eager unistructured targetPattOption st

  fun initState sCSD tCSD iCSD inverse KB ct goal =
    let val tTS = #typeSystem (#typeSystemData tCSD)
        val targetTokens = FiniteSet.filter
                               (fn x => Set.elementOf (CSpace.typeOfToken x) (#Ty tTS) andalso
                                        not (FiniteSet.elementOf x (Construction.tokensOfConstruction ct)))
                               (Construction.leavesOfConstruction goal);
    in State.make {sourceConSpecData = sCSD,
                   targetConSpecData = tCSD,
                   interConSpecData = iCSD,
                   transferProof = TransferProof.ofPattern goal,
                   construction = ct,
                   originalGoal = goal,
                   goals = [goal],
                   compositions = map Composition.makePlaceholderComposition targetTokens,
                   knowledge = Knowledge.filterForISpace (#name iCSD) inverse KB}
    end

  fun applyTransfer sCSD tCSD iCSD KB ct goal =
      let val st = initState sCSD tCSD iCSD false KB ct goal
          val stateSeq = structureTransfer (SOME 6,NONE,NONE) true false NONE st;
          fun getStructureGraph st =
              List.flatmap Composition.resultingConstructions (State.patternCompsOf st);
          fun makeDiagnostic goal =
              let val str = Construction.toString goal;
                  val toks = FiniteSet.listOf
                                 (Construction.tokensOfConstruction goal);
                  fun hexDigit c = Char.contains "0123456789ABCDEFabcdef" c;
                  fun couldBeId [] = false
                    | couldBeId [c] = hexDigit c
                    | couldBeId (c::cs) = if c = #"-" orelse hexDigit c
                                          then List.all hexDigit cs
                                          else false;
                  fun asId s = if couldBeId (String.explode s) then SOME s else NONE;
                  val ids = List.mapPartial (asId o CSpace.nameOfToken) toks;
              in Diagnostic.create
                     Diagnostic.ERROR
                     ("Transfer failed due to open goal: " ^ str)
                     ids
              end;
          val firstState = Seq.hd stateSeq;
          val goals = State.goalsOf firstState;
      in case goals of
             [] => Result.ok (getStructureGraph firstState)
           | _ => Result.error (List.map makeDiagnostic goals)
      end
end;
