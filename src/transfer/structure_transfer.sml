import "transfer.search";
import "transfer.heuristic";
import "util.logging";

signature TRANSFER =
sig
  type goal = Pattern.pattern
  val applyTransferSchemaForGoal : State.T -> InterCSpace.tSchema -> goal -> State.T
  val applyTransferSchema : State.T -> InterCSpace.tSchema -> State.T Seq.seq
  val singleStepTransfer : State.T -> State.T Seq.seq

  val structureTransfer : bool -> State.T -> State.T Seq.seq
(*)
  val iterativeStructureTransfer : bool -> Pattern.pattern option
                                        -> State.T -> State.T Seq.seq*)

  val targetedTransfer : Pattern.pattern
                            -> State.T -> State.T Seq.seq

  val masterTransfer : bool -> bool
                            -> Pattern.pattern option
                            -> State.T -> State.T Seq.seq

end;

structure Transfer : TRANSFER =
struct

  type goal = Pattern.pattern
  exception TransferSchemaNotApplicable
  exception Error


  (*  *)
  fun applyMorphismRefreshingNONEs given avoid CTs =
      let fun firstUnusedName Ns =
            let fun mkFun n =
                  let val vcandidate = "v_{"^(Int.toString n)^"}"
                  in if FiniteSet.exists (fn x => x = vcandidate) Ns
                     then mkFun (n+1)
                     else vcandidate
                  end
            in mkFun 0
            end
          fun mkRenameFunction Ns Tks =
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
  fun refreshNamesOfConstructionAvoiding ct avoid =
    (case applyMorphismRefreshingNONEs (fn _ => NONE) avoid [ct] of
        (f,[x]) => (f,x)
      | _ => raise Error)


  exception InferenceSchemaNotApplicable
  fun applyInferenceSchemaForGoal st T idT ct isch goal =
  let val {antecedent,consequent,context,name} = isch
      val givenTokens = FiniteSet.intersection
                             (Construction.tokensOfConstruction goal)
                             (Construction.tokensOfConstruction ct)

      val (consequentMap, updatedConsequent) =
          (case Pattern.findEmbeddingUpTo idT consequent goal givenTokens of
                (f,SOME x) => (f,x)
              | _ => raise InferenceSchemaNotApplicable)

      val (contextMap, matchingSubConstruction) =
            (case Pattern.findConsistentMatchToSubConstruction T ct context consequentMap of
                (f,SOME x) => (f,x)
              | _ => raise InferenceSchemaNotApplicable)

      val usedTokens = FiniteSet.union
                          (State.tokensInUse st)
                          (Pattern.tokensOfConstruction updatedConsequent)
      val ccMap = Pattern.funUnion [consequentMap, contextMap]
      val (_,updatedAntecedent) = applyMorphismRefreshingNONEs ccMap usedTokens antecedent

      val goals = State.goalsOf st
      val updatedGoals = updatedAntecedent @ List.filter (fn x => not (Pattern.same goal x)) goals

      val instantiatedISchema = {antecedent = updatedAntecedent,
                                 consequent = updatedConsequent,
                                 context = matchingSubConstruction,
                                 name = name}
      val transferProof = State.transferProofOf st
      val updatedTransferProof = TransferProof.attachISchemaAt instantiatedISchema goal transferProof

      val updatedState = State.updateTransferProof updatedTransferProof (State.updateGoals updatedGoals st)
  in updatedState
  end

  (* The following function takes a tSchema, tsch, and a goal assumed to be
     matched by the consequent of tsch (up to the tokens of the original construction).
     The function will try to find a generator in the given source construction that matches
     the source pattern of tsch. If found, it will use the isomorphic map (from pattern to generator)
     to rename the relationships between the vertices of the source specified by the tSchema.
     It will also rename the vertices of the target pattern so that they don't clash with the
     vertices in the composition.  *)
  fun instantiateTransferSchema tsch st goal targetConstructMap =
    let
      val ct = State.constructionOf st
      val givenTokens = FiniteSet.intersection
                            (Construction.tokensOfConstruction goal)
                            (Construction.tokensOfConstruction ct)
    (*)  val (sourceToken,H) = FiniteSet.pull givenTokens
                              handle Empty => (Logging.write "WARNING : goal and source share no tokens\n";
                                                raise TransferSchemaNotApplicable)
      val _ = if FiniteSet.isEmpty H then ()
              else Logging.write "WARNING : goal and source share more than one token\n"*)
      val patternComps = State.patternCompsOf st
      val {antecedent,consequent,source,target,...} = tsch
      val T = #typeSystem (State.sourceTypeSystemOf st)
      val interT = #typeSystem (State.interTypeSystemOf st)
      val usedTokens = State.tokensInUse st
      fun partialFunComp f g x = (case g x of NONE => f x | SOME y => f y)
      fun funComp f g x = (case g x of NONE => NONE | SOME y => f y)

      val consequentMap =
            (case Pattern.findEmbeddingUpTo interT consequent goal givenTokens of
              (f,SOME _) => partialFunComp f targetConstructMap
            | _ => raise TransferSchemaNotApplicable)

      val (sourceMap, matchingSubConstruction) =
            (case Pattern.findConsistentMatchToSubConstruction T ct source consequentMap of
                (f,SOME x) => (f, x)
              | _ => raise TransferSchemaNotApplicable)

      val updatedConsequent = Pattern.applyPartialMorphism consequentMap consequent
      val csMap = Pattern.funUnion [consequentMap, sourceMap]
      val usedTokensC = FiniteSet.union usedTokens (Pattern.tokensOfConstruction updatedConsequent)

      val targetMap =
            (case applyMorphismRefreshingNONEs csMap usedTokensC [Pattern.applyPartialMorphism targetConstructMap target] of
              (f,_) => partialFunComp f targetConstructMap)

      val updatedTarget = Pattern.applyPartialMorphism targetMap target

      val cstMap = Pattern.funUnion [csMap,targetMap]
      val usedTokensCT = FiniteSet.union usedTokensC (Construction.tokensOfConstruction updatedTarget)

      val (_,updatedAntecedent) = applyMorphismRefreshingNONEs cstMap usedTokensCT antecedent
      val updatedPullList =
            map (fn (R,R',tL) => (Pattern.applyPartialMorphism cstMap R,Pattern.applyPartialMorphism cstMap R',map (valOf o cstMap) tL
                                    handle Option => (map (print o (fn x => "unkown token: " ^ CSpace.stringOfToken x ^ "\n")) tL; raise Option)))
                (#pullList tsch)
    in (funComp targetMap targetConstructMap,
        InterCSpace.declareTransferSchema {name = #name tsch,
                                           source = matchingSubConstruction,
                                           target = updatedTarget,
                                           antecedent = updatedAntecedent,
                                           consequent = updatedConsequent,
                                           pullList = updatedPullList})
    end

  fun applyPullItem [] _ _ = []
    | applyPullItem ((x,y,R)::gs) t (R',R'',tL) =
    if Relation.same R R'
    then map (fn t' => (x,map (fn s => if CSpace.sameTokens s t then t' else s) y,R'')) tL @
        applyPullItem gs t (R',R'',tL)
    else (x,y,R)::applyPullItem gs t (R',R'',tL)

  fun applyTransferSchemaForGoal st tsch goal =
    let val {target,...} = tsch

        val patternComps = State.patternCompsOf st
        val targetTokens = FiniteSet.intersection (Pattern.tokensOfConstruction goal)
                                                  (Composition.tokensOfCompositions patternComps)
        val tT = #typeSystem (State.targetTypeSystemOf st)
        val targetConstruct = Pattern.constructOf target
        fun minType (ty1,ty2) =
              if (#subType tT) (ty1,ty2) then ty1
              else if (#subType tT) (ty2,ty1) then ty2
              else raise TransferSchemaNotApplicable
        val newTargetConstruct =
              if FiniteSet.isEmpty targetTokens then targetConstruct
              else (case FiniteSet.pull targetTokens of (tt,H) =>
                      if FiniteSet.isEmpty H then
                         (CSpace.makeToken (CSpace.nameOfToken tt)
                                           (minType (CSpace.typeOfToken tt, CSpace.typeOfToken targetConstruct)))
                      else raise TransferSchemaNotApplicable
                    )
        fun targetConstructMap x =
              if CSpace.sameTokens x targetConstruct
              then SOME newTargetConstruct
              else NONE
        val (attachmentMap,instantiatedTSchema) =
              instantiateTransferSchema tsch st goal targetConstructMap
        fun renaming x = if FiniteSet.elementOf x targetTokens andalso FiniteSet.size targetTokens = 1
                         then attachmentMap targetConstruct
                         else NONE

        val renamedPatternComps = map (Composition.applyPartialMorphism renaming) patternComps
        val updatedPatternComps = Composition.attachConstructions renamedPatternComps [#target instantiatedTSchema]

        val goals = State.goalsOf st
        val updatedGoals = #antecedent instantiatedTSchema @ List.filter (fn x => not (Pattern.same goal x)) goals

        val transferProof = State.transferProofOf st
        val updatedTransferProof = TransferProof.attachTSchemaAt instantiatedTSchema goal transferProof

        val updatedState = State.applyPartialMorphismToProof renaming
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

  fun applyTransferSchema st tsch =
    let val newSt = idempotencyOnGoals st
        val ct = State.constructionOf st
        fun ac [] = Seq.empty
          | ac (g::gs) =
              (Seq.cons (applyTransferSchemaForGoal newSt tsch g) (ac gs))
                handle TransferSchemaNotApplicable => (ac gs)
    in ac (State.goalsOf newSt)
    end

  fun applyInferenceSchema st isch =
    let val ct = State.constructionOf st
        val T = #typeSystem (State.targetTypeSystemOf st)
        val idT = #typeSystem (State.interTypeSystemOf st)
        val pcts = List.maps Composition.resultingConstructions (State.patternCompsOf st)
        fun appToTargetConstructions [] _ = Seq.empty
          | appToTargetConstructions (h::L) g = Seq.single (applyInferenceSchemaForGoal st T idT h isch g)
                                                handle InferenceSchemaNotApplicable => appToTargetConstructions L g
        fun ac [] = Seq.empty
          | ac (g::gs) =
              (Seq.append (appToTargetConstructions pcts g) (ac gs))
                handle InferenceSchemaNotApplicable => (ac gs)
    in ac (State.goalsOf st)
    end

  fun singleStepTransfer st =
    let val tschs = Knowledge.transferSchemasOf (State.knowledgeOf st)
    in Seq.maps (applyTransferSchema st) tschs
    end

  fun singleStepInference st =
    let val ischs = Knowledge.inferenceSchemasOf (State.knowledgeOf st)
    in Seq.maps (applyInferenceSchema st) ischs
    end

  fun structureTransferTac h ign forget state =
      (*Search.breadthFirstSortAndIgnore singleStepTransfer h ign forget state*)
      (*Search.breadthFirstSortIgnoreForget singleStepTransfer h ign forget state*)
      (*Search.depthFirstSortAndIgnore singleStepTransfer h ign forget state*)
      (*Search.depthFirstSortIgnoreForget singleStepTransfer h ign forget state*)
      (*Search.bestFirstSortAndIgnore singleStepTransfer h ign forget state*)
      Search.bestFirstSortIgnoreForget singleStepTransfer h ign forget state

(* every element of goals should be of the form ([vi1,...,vin],[vj1,...,vjm],R)*)
fun structureTransfer unistructured st =
  let val ign = Heuristic.ignore 15 4999 45 unistructured
      val transferTac = structureTransferTac Heuristic.transferProofMultStrengths ign Heuristic.forgetRelaxed
      val inferenceTac = Search.depthFirst singleStepInference 10
      val rawResults = Seq.THEN (transferTac, inferenceTac) st
  in Seq.sort (Seq.take 100 rawResults) Heuristic.transferProofMultStrengths
  end

  fun v2t t =
    let val tok = CSpace.nameOfToken t
        val typ = CSpace.typeOfToken t
        fun vt (x::xs) = if x = #"v" then #"t"::xs else x::xs
          | vt [] = []
    in SOME (CSpace.makeToken (String.implode (vt (String.explode tok))) typ)
    end

  exception Nope

  fun constructionOfComp st =
    (case List.maps Composition.resultingConstructions (State.patternCompsOf st) of
        [c] => c
      | _ => raise Nope)
  fun withinTarget targetTypeSystem targetPattern st =
    Pattern.hasUnifiableGenerator targetTypeSystem targetPattern (constructionOfComp st) handle Nope => false
  fun matchesTarget targetTypeSystem targetPattern st =
    Pattern.matches targetTypeSystem (constructionOfComp st) targetPattern handle Nope => false

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

  fun targetedTransferTac h ign forget targetPattern state =
    let val targetTypeSystem = #typeSystem (State.targetTypeSystemOf state)
        fun forget' (st,L) = forget (st,L) orelse not (matchesTarget targetTypeSystem targetPattern st)
        fun ign' (st,L) = ign (st,L) orelse not (withinTarget targetTypeSystem targetPattern st)
    in Search.bestFirstSortIgnoreForget singleStepTransfer h ign' forget' state
    end

  fun targetedTransfer targetPattern st =
    let val ign = Heuristic.ignoreRelaxed 15 4999
    in targetedTransferTac Heuristic.transferProofMultStrengths ign Heuristic.forgetStrict targetPattern st
    end

  fun masterTransfer iterative unistructured targetPattOption st =
  (*)  if iterative
    then iterativeStructureTransfer unistructured targetPattOption st
    else*) (case targetPattOption of
              NONE => structureTransfer unistructured st
            | SOME targetPattern => targetedTransfer targetPattern st)

end;
