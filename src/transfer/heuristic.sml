import "transfer.state";
import "util.random";

signature HEURISTIC =
sig
  val similarGoalsAndComps : State.T * State.T -> bool
  val similarTransferProofs : State.T * State.T -> bool
  val ignore : int -> int -> int -> bool -> (State.T * State.T list) -> bool
  val ignoreRelaxed : int -> int -> (State.T * State.T list) -> bool
  val forgetStrict : (State.T * State.T list) -> bool
  val forgetRelaxed : (State.T * State.T list) -> bool

  val largerComposition : State.T * State.T -> order
  val fewerGoals : State.T * State.T -> order
  val zeroGoalsOtherwiseCompositionSize : State.T * State.T -> order
  val random : State.T * State.T -> order
  val zeroGoalsOtherwiseRandom : State.T * State.T -> order
  val multiplicativeScore : (string -> real option) -> State.T -> real
  val transferProofMultStrengths : State.T * State.T -> order
end

structure Heuristic:HEURISTIC =
struct

fun similarGoalsAndComps (st,st') =
  let val gs = State.goalsOf st
      val gs' = State.goalsOf st'
      val C = State.patternCompsOf st
      val C' = State.patternCompsOf st'
  in List.isPermutationOf (uncurry Pattern.similar) gs gs' andalso
    List.isPermutationOf (uncurry Composition.pseudoSimilar) C C'
  end

fun similarTransferProofs (st,st') = TransferProof.similar (State.transferProofOf st) (State.transferProofOf st')

fun ignore ngoals nresults csize unistructured (st,L) =
  List.length (State.goalsOf st) > ngoals orelse
  length L > nresults orelse
  List.sumMapInt Composition.size (State.patternCompsOf st) > csize orelse
  List.exists (fn x => similarTransferProofs (x,st)) L orelse
  (unistructured andalso
   List.exists (fn x => not (Composition.unistructurable (#typeSystem (State.targetTypeSystemOf st)) x)) (State.patternCompsOf st))

fun ignoreRelaxed ngoals nresults (st,L) =
  List.length (State.goalsOf st) > ngoals orelse
  length L > nresults orelse
  List.exists (fn x => similarTransferProofs (x,st)) L

fun forgetStrict (st,L) =
  List.length (State.goalsOf st) > 0 orelse
  List.exists (fn x => similarGoalsAndComps (x,st)) L

fun forgetRelaxed (st,L) =
  List.exists (fn x => similarGoalsAndComps (x,st)) L


fun largerComposition (st,st') =
  let val D = State.patternCompsOf st
      val D' = State.patternCompsOf st'
  in Int.compare (List.sumMapInt Composition.size D', List.sumMapInt Composition.size D)
  end

fun fewerGoals (st,st') =
  let val gs = State.goalsOf st
      val gs' = State.goalsOf st'
  in Int.compare (length gs,length gs')
  end

fun opposite LESS = GREATER | opposite EQUAL = EQUAL | opposite GREATER = LESS
fun zeroGoalsOtherwiseCompositionSize (st,st') =
  let val gs = State.goalsOf st
      val gs' = State.goalsOf st'
      val gsn = length gs
      val gsn' = length gs'
      val D = State.patternCompsOf st
      val D' = State.patternCompsOf st'
      val P = Int.compare (List.sumMapInt Composition.size D, List.sumMapInt Composition.size D')
  in if gsn = 0 andalso gsn' = 0 then P
     else if gsn > 0 andalso gsn' > 0 andalso P <> EQUAL then opposite P
     else Int.compare (gsn,gsn')
  end

fun random _ =
  let val x1 = MLtonRandom.rand ()
      val X2 = map MLtonRandom.rand [(),(),(),(),(),(),(),(),(),()]
      fun le x = List.all (fn y => x < y) X2
  in if le x1 then LESS else GREATER
  end

fun zeroGoalsOtherwiseRandom (st,st') =
  let val gsn = length (State.goalsOf st)
      val gsn' = length (State.goalsOf st')
  in if (gsn = 0 andalso gsn' = 0) orelse (gsn > 0 andalso gsn' > 0) then random (st,st')
     else Int.compare (gsn,gsn')
  end


fun multProp (x::L) = x * multProp L
  | multProp [] = 1.0


fun hasTokensInTypeSystem ct TS = FiniteSet.exists (fn x => Set.elementOf (CSpace.typeOfToken x) (#Ty TS)) (Construction.tokensOfConstruction ct)
fun multiplicativeScore' p CS (TransferProof.Closed (r,npp,L)) =
      (case p (#name npp) of
          SOME s => s
        | NONE => 1.0) * multProp (map (multiplicativeScore' p CS) L)
  | multiplicativeScore' p CS (TransferProof.Open r) =
      if hasTokensInTypeSystem r (#typeSystem (#typeSystemData CS))
      then 0.1
      else 0.9

fun multiplicativeScore p st = multiplicativeScore' p (State.sourceConSpecDataOf st) (State.transferProofOf st)

fun transferProofMultStrengths (st,st') =
  let val gsn = length (State.goalsOf st)
      val gsn' = length (State.goalsOf st')
      val strength = Knowledge.strengthOf (State.knowledgeOf st)
  in if (gsn = 0 andalso gsn' = 0) orelse (gsn > 0 andalso gsn' > 0)
     then Real.compare (multiplicativeScore strength st',multiplicativeScore strength st)
     else Int.compare (gsn,gsn')
  end

end
