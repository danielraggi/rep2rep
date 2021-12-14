import "transfer.state";
import "util.random";

signature HEURISTIC =
sig
  val largerComposition : State.T * State.T -> order
  val fewerGoals : State.T * State.T -> order
  val zeroGoalsOtherwiseCompositionSize : State.T * State.T -> order
  val random : State.T * State.T -> order
  val zeroGoalsOtherwiseRandom : State.T * State.T -> order
  val transferProofMultStrengths : State.T * State.T -> order
end

structure Heuristic:HEURISTIC =
struct

fun largerComposition (st,st') =
  let val D = State.patternCompOf st
      val D' = State.patternCompOf st'
  in Int.compare (Composition.size D', Composition.size D)
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
      val D = State.patternCompOf st
      val D' = State.patternCompOf st'
      val P = Int.compare (Composition.size D,Composition.size D')
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

fun transferProofMultStrengths (st,st') =
  let val gsn = length (State.goalsOf st)
      val gsn' = length (State.goalsOf st')
      val tproof = State.transferProofOf st
      val tproof' = State.transferProofOf st'
      val strength = Knowledge.strengthOf (State.knowledgeOf st)
  in if (gsn = 0 andalso gsn' = 0) orelse (gsn > 0 andalso gsn' > 0)
     then Real.compare (TransferProof.multiplicativeIS strength tproof',TransferProof.multiplicativeIS strength tproof)
     else Int.compare (gsn,gsn')
  end

end
