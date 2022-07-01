import "transfer.search";
import "transfer.heuristic";
import "util.logging";

signature TRANSFER =
sig
  type goal = Pattern.pattern
  val applyTransferSchemaForGoal : State.T -> InterCSpace.tSchema -> CSpace.token FiniteSet.set -> goal -> State.T
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
  fun refreshNamesOfConstructionAvoiding ct avoid =
    let
      fun firstUnusedName Ns =
        let fun f n =
              let val vcandidate = "v_{"^(Int.toString n)^"}"
              in if FiniteSet.exists (fn x => x = vcandidate) Ns then f (n+1) else "v_{"^(Int.toString n)^"}"
              end
        in f 0
        end
      val tokensInConstruction = Construction.tokensOfConstruction ct
      val names = FiniteSet.map CSpace.nameOfToken avoid
      fun mkRenameFunction _ [] = (fn _ => NONE)
        | mkRenameFunction Ns (y::ys) =
            let
              fun f x = if CSpace.sameTokens x y
                        then SOME (CSpace.makeToken (firstUnusedName Ns) (CSpace.typeOfToken x))
                        else mkRenameFunction (CSpace.nameOfToken (Option.valOf (f y)) :: Ns) ys x
            in f
            end
      val renameFunction = mkRenameFunction names tokensInConstruction
      val updatedConstruction = Pattern.applyMorphism renameFunction ct
    in (renameFunction, updatedConstruction)
    end

  (* The following function takes a tSchema, tsch, with construct relation Rc,
     and a goal assumed to have a superRelation Rg of Rc.
     The function will try to find a generator in the given source construction that matches
     the source pattern of tsch. If found, it will use the isomorphic map (from pattern to generator)
     to rename the relationships between the vertices of the source specified by the tSchema.
     It will also rename the vertices of the target pattern so that they don't clash with the
     vertices in the composition.  *)
  fun instantiateTransferSchema tsch st goal targetConstructMap =
    let
      val ct = State.constructionOf st
      val (sourceToken,H) = FiniteSet.pull (FiniteSet.intersection
                                              (Construction.tokensOfConstruction goal)
                                              (Construction.tokensOfConstruction ct))
                              handle Empty => (Logging.write "WARNING : goal and source share no tokens\n"; raise TransferSchemaNotApplicable)
      val _ = if FiniteSet.isEmpty H then () else Logging.write "WARNING : goal and source share more than one token\n"
      val patternComps = State.patternCompsOf st
      val {antecedent,consequent,source,target,...} = tsch
      val T = #typeSystem (State.sourceTypeSystemOf st)
      val usedTokens = State.tokensInUse st
      fun partialFunComp f g x = (case g x of NONE => f x | SOME y => f y)
      fun funComp f g x = (case g x of NONE => NONE | SOME y => f y)
      val (targetRenamingFunction, updatedTargetPattern) =
            refreshNamesOfConstructionAvoiding (Pattern.applyPartialMorphism targetConstructMap target) usedTokens
      val (sourceRenamingFunction, matchingGenerator) =
            (case Pattern.matchToSubConstructionWithConstruct T ct source sourceToken of
                (f,SOME x) => (f, x)
              | _ => raise TransferSchemaNotApplicable)

      fun srFun x = (Option.valOf o sourceRenamingFunction) x
          handle Option => (Logging.write ("\nERROR: source renaming function\n"); raise Option)
      fun trFun x = (Option.valOf o (partialFunComp targetRenamingFunction targetConstructMap)) x
          handle Option => (Logging.write ("\nERROR: target renaming function\n"); raise Option)
      (*****)
      fun f x =  (Pattern.funUnion [partialFunComp targetRenamingFunction targetConstructMap, sourceRenamingFunction]) x
      fun update x = Pattern.applyPartialMorphism f x
      (*****)
      val updatedAntecedent = map update antecedent
      val updatedConsequent = update consequent
      val updatedPullList =
            map (fn (R,R',tL) => (update R,update R',map (valOf o f) tL
                                      handle Option => (map (print o (fn x => CSpace.stringOfToken x ^ "\n")) tL; raise Option)))
                (#pullList tsch)
    in (funComp targetRenamingFunction targetConstructMap,
        InterCSpace.declareTransferSchema {name = #name tsch,
                                            source = matchingGenerator,
                                            target = updatedTargetPattern,
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

  fun applyTransferSchemaForGoal st tsch givenTokens goal =
    let val {consequent,source,target,...} = tsch
      (*)  val (sourceToken,targetToken,Rg) = (case Relation.tupleOfRelationship goal of
                                              ([x],[y],R) => (x,y,R)
                                            | _ => raise TransferSchemaNotApplicable)*)
        val patternComps = State.patternCompsOf st
        val targetTokens = FiniteSet.intersection (Pattern.tokensOfConstruction goal)
                                                  (Composition.tokensOfCompositions patternComps)
        val sT = #typeSystem (State.sourceTypeSystemOf st)
        val tT = #typeSystem (State.targetTypeSystemOf st)
        val interT = #typeSystem (State.interTypeSystemOf st)
        val constructOfTargetPattern = Pattern.constructOf target
        fun minType (ty1,ty2) =
              if (#subType tT) (ty1,ty2) then ty1
              else if (#subType tT) (ty2,ty1) then ty2
              else raise TransferSchemaNotApplicable
        val newTargetToken =
              if FiniteSet.isEmpty targetTokens then constructOfTargetPattern
              else (case FiniteSet.pull targetTokens of (tt,H) =>
                      if FiniteSet.isEmpty H then
                         (CSpace.makeToken (CSpace.nameOfToken tt)
                                           (minType (CSpace.typeOfToken tt, CSpace.typeOfToken constructOfTargetPattern)))
                      else (Logging.write "\n  sorry: mutiple target tokens not possible yet\n";
                            raise TransferSchemaNotApplicable)
                    )
        fun targetConstructMap x =
              if CSpace.sameTokens x constructOfTargetPattern
              then SOME newTargetToken
              else NONE
        val (ff,instantiatedTSchema) =
              (case Pattern.findMatchUpTo interT consequent goal givenTokens of
                   (f,SOME _) => instantiateTransferSchema tsch st goal targetConstructMap
                 | _ => raise TransferSchemaNotApplicable)
        fun renaming x = (if CSpace.sameTokens x (#1(FiniteSet.pull targetTokens)) then ff constructOfTargetPattern else NONE) handle Empty => NONE
      (*  val _ = print ((CSpace.nameOfToken targetToken) ^ CSpace.nameOfToken(Pattern.constructOf targetPattern) ^ "\n")*)
        val {antecedent,target,...} = instantiatedTSchema
        val updatedPatternComps = Composition.attachConstructions (map (Composition.applyPartialMorphismToComposition renaming) patternComps) [target]
        val transferProof = State.transferProofOf st
        val updatedTransferProof = TransferProof.attachTSchemaAt instantiatedTSchema goal transferProof
      (*)  val updatedTransferProof = TransferProof.attachTSchemaPulls instantiatedTSchema targetToken updatedTransferProof'*)
        (*fun applyPullList [] = updatedGoals'
          | applyPullList (pi::pL) = applyPullItem (applyPullList pL) targetToken pi
        val updatedGoals = applyPullList (#pullList instantiatedTSchema)*)
        (*
        val _ = if not (null (#pullList instantiatedTSchema)) andalso List.allZip Relation.sameRelationship gs' updatedGoals
                then raise TransferSchemaNotApplicable else ()
        *)
        val stateWithUpdatedGoals = State.replaceGoal st goal antecedent
        val stateWithUpdatedProof = State.updateTransferProof stateWithUpdatedGoals updatedTransferProof
    in State.applyPartialMorphismToCompAndGoals renaming (State.updatePatternComps stateWithUpdatedProof updatedPatternComps)
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
        val stateWithUpdatedGoals = State.updateGoals st keep
    in State.updateTransferProof stateWithUpdatedGoals (updateTransferProof dump)
    end

  fun applyTransferSchema st tsch =
    let val newSt = idempotencyOnGoals st
        val ct = State.constructionOf st
        fun ac [] = Seq.empty
          | ac (g::gs) =
              let val givenTokens = FiniteSet.intersection
                                      (Construction.tokensOfConstruction g)
                                      (Construction.tokensOfConstruction ct)
                  val X = (Seq.single (applyTransferSchemaForGoal newSt tsch givenTokens g)
                            handle TransferSchemaNotApplicable => Seq.empty)
              in Seq.append X (ac gs)
              end
    in ac (State.goalsOf newSt)
    end

  fun singleStepTransfer st =
    let val tschs = Knowledge.transferSchemasOf (State.knowledgeOf st)
    in Seq.maps (applyTransferSchema st) tschs
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
  in structureTransferTac Heuristic.transferProofMultStrengths ign Heuristic.forgetRelaxed st
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
