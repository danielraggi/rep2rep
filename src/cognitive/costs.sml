import "transfer.structure_transfer";

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
        fun tokenRegVal x = if x = SOME "icon" then 0.2
                       else if x = SOME "emergent" then 0.4
                       else if x = SOME "spatial-index" then 0.6
                       else if x = SOME "notational-index" then 0.8
                       else if x = SOME "search" then 1.0
                       else (print "unknown token reg"; raise Match)
        val cts = List.flatmap Composition.resultingConstructions (State.patternCompsOf st)
        fun reg w (Construction.TCPair ({constructor,...},cs)) =
            let val discount = 1.0 - u/2.0
                val updWeight = discount * (w + 1.0) / 2.0
            in w * (tokenRegVal (tokenReg constructor)) * (List.sumMap (reg updWeight) cs)
            end
          | reg _ _ = 1.0
    in List.sumMap (reg 1.0) cts
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
         | _ => (print "unknown quantity scale"; raise Match))
  in List.avgIndexed qsVal types
  end

(* expression complexity *)
fun expressionComplexity cognitiveData st u =
  let val cts = List.flatmap Composition.resultingConstructions (State.patternCompsOf st)
      val discount = 1.0 - u/2.0
      fun graphSize w (Construction.Source _) = 1.0
        | graphSize w (Construction.Reference _) = 0.0
        | graphSize w (Construction.TCPair (_,cs)) = 3.0 + real(length cs) + List.sumMap (graphSize (w * discount)) cs
  in List.sumMap (graphSize 1.0) cts
  end

(* Heterogeneity *)
  fun heterogeneity cognitiveData st u =
    let val tCS = State.targetConSpecDataOf st
        val cts = List.flatmap Composition.resultingConstructions (State.patternCompsOf st)
    in real (varietyOfSymbols cts)
    end

(* infernce type *)
(* solution stuff *)

fun aggregate cognitiveData st u =
  let val reg = registration cognitiveData st u (* lightest *)
      val qs = quantityScale cognitiveData st u (* 3rd heaviest *)
      val ec = expressionComplexity cognitiveData st u (* 2nd heaviest *)
      val het = heterogeneity cognitiveData st u (* heaviest *)
      val userDepWeight = 8.0 / (7.0 * u + 1.0)
  in (1.0 * userDepWeight) * reg +
     (2.0 * userDepWeight) * qs +
     (4.0 * userDepWeight) * ec +
     (8.0 * userDepWeight) * het
  end

end
