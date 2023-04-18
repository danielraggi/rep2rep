import "transfer.state";

signature COGNITIVECOSTS =
sig
  type userProfile
  type data
  val empty : data;
  val joinCognitiveData : data -> data -> data;
  val registration : data -> State.T -> userProfile -> real;
  val quantityScale : data -> State.T -> userProfile -> real;
  val expressionComplexity : data -> State.T -> userProfile -> real;
  val heterogeneity : data -> State.T -> userProfile -> real;
  val aggregate : data -> State.T -> userProfile -> real;
end

structure CognitiveCosts : COGNITIVECOSTS =
struct
  type userProfile = real
  type data = {tokenRegistration : string * CSpace.constructor -> string option,
               quantityScale : string * Type.typ -> string option}
  val empty = {tokenRegistration = fn _ => NONE, quantityScale = fn _ => NONE}

  exception IllDefined of string
  fun joinCognitiveData {tokenRegistration = tr, quantityScale = qs}
                        {tokenRegistration = tr', quantityScale = qs'} =
    let fun TR x = (case (tr x, tr' x) of (NONE, res) => res
                                        | (SOME y,SOME y') => if y = y' then SOME y else raise IllDefined ("inconsisten token reg " ^ y ^ " and " ^ y' ^ " for " ^ CSpace.nameOfConstructor (#2 x))
                                        | (res,_) => res)
        fun QS x = (case (qs x, qs' x) of (NONE, res) => res
                                        | (SOME y,SOME y') => if y = y' then SOME y else raise IllDefined ("inconsisten quantity scales " ^ y ^ " and " ^ y' ^ " for " ^ Type.nameOfType (#2 x))
                                        | (res,_) => res)
    in {tokenRegistration = TR, quantityScale = QS}
    end

  fun userDepWeight u = Math.pow(2.0,3.0*(1.0-u))
  fun logistic L k x0 x = L / (1.0 + Math.exp (~k * (x-x0)))

(* registration *)
  (* number of symbols *)
  fun numberOfSymbols st =
    let val cts = List.flatmap Composition.resultingConstructions (State.patternCompsOf st)
        val tokens = List.flatmap (Construction.tokensOfConstruction) cts
    in FiniteSet.size tokens
    end

  (* variety of symbols *)
  fun varietyOfSymbols cts =
    let val tokens = List.flatmap (Construction.tokensOfConstruction) cts
        val types = FiniteSet.ofList (List.map CSpace.typeOfToken tokens)
    in FiniteSet.size types
    end

  (* registration: there's a disount of (1.0-u/2.0) every step down the tree. Uncertain what this means if there's a loop *)
  fun registration cognitiveData st u =
    let val conSpecName = #name (State.targetConSpecDataOf st)
        fun tokenReg x = (#tokenRegistration cognitiveData) (conSpecName,x)
        fun tokenRegVal x =
          (case x of SOME "icon" => 0.2
                   | SOME "emergent" => 0.4
                   | SOME "spatial-index" => 0.6
                   | SOME "notational-index" => 0.8
                   | SOME "search" => 1.0
                   | NONE => 0.5
                   | SOME y => (print ("unknown token reg" ^ y ^ " ") ; raise Match))
        val cts = List.flatmap Composition.resultingConstructions (State.patternCompsOf st)
        fun reg w (Construction.TCPair ({constructor,...},cs)) =
            let val discount = 1.0 - u/3.0
                val updWeight = discount * w
            in w * (tokenRegVal (tokenReg constructor)) * real(length cs) + (List.sumMap (reg updWeight) cs)
            end
          | reg _ _ = 1.0
        val rawVal = List.sumMap (reg 1.0) cts
    in userDepWeight u * logistic 100.0 0.05 80.0 rawVal
    end

(* semantic encoding *)
  (* Concept-mapping (assumes transfer happend from Bayes into the target space) *)

  (* ER-semantic process *)
  (* IR-semantic process *)

(* quantity scale *)
fun quantityScale cognitiveData st u =
  let val conSpecName = #name (State.targetConSpecDataOf st)
      val cts = List.flatmap Composition.resultingConstructions (State.patternCompsOf st)
      val tokens = List.flatmap (Construction.tokensOfConstruction) cts
      val types = List.map CSpace.typeOfToken tokens
      fun qs x = (#quantityScale cognitiveData) (conSpecName,x)
      fun qsVal x =
        (case qs x of
           SOME "nominal" => 0.25
         | SOME "ordinal" => 0.5
         | SOME "interval" => 0.75
         | SOME "ratio" => 1.0
         | NONE => (qsVal (Type.parentOfDanglyType x) handle Type.badType => 0.25)
         | SOME s => (print ("unknown quantity scale " ^ s ^ " "); raise Match))
  in 200.0 * userDepWeight u * (List.avgIndexed qsVal types)
  end

(* expression complexity *)
fun expressionComplexity cognitiveData st u =
  let val cts = List.flatmap Composition.resultingConstructions (State.patternCompsOf st)
      val discount = 1.0 - u/2.0
      fun graphSize w (Construction.Source _) = 1.0
        | graphSize w (Construction.Reference _) = 0.0
        | graphSize w (Construction.TCPair (_,cs)) = 3.0 + real(length cs) + w * (List.sumMap (graphSize (w * discount)) cs)
      val rawVal = List.sumMap (graphSize 1.0) cts
  in userDepWeight u * logistic 400.0 0.075 60.0 rawVal
  end

(* Heterogeneity *)
  fun heterogeneity cognitiveData st u =
    let val tCS = State.targetConSpecDataOf st
        val cts = List.flatmap Composition.resultingConstructions (State.patternCompsOf st)
        val rawVal = real (varietyOfSymbols cts)
    in userDepWeight u * logistic 800.0 0.3 15.0 rawVal
    end

(* infernce type *)
(* solution stuff *)

fun aggregate cognitiveData st u =
  let val reg = registration cognitiveData st u (* lightest *)
      val qs = quantityScale cognitiveData st u (* 3rd heaviest *)
      val ec = expressionComplexity cognitiveData st u (* 2nd heaviest *)
      val het = heterogeneity cognitiveData st u (* heaviest *)
  in reg + qs + ec + het
  end

end
