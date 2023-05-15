import "transfer.state";

signature COGNITIVECOSTS =
sig
  type userProfile
  type data
  val empty : data;
  val joinCognitiveData : data -> data -> data;
  val registration : data -> CSpace.conSpecData -> Construction.construction list -> userProfile -> real;
  val quantityScale : data -> CSpace.conSpecData -> Construction.construction list -> userProfile -> real;
  val expressionComplexity : data -> CSpace.conSpecData -> Construction.construction list -> userProfile -> real;
  val heterogeneity : data -> CSpace.conSpecData -> Construction.construction list -> userProfile -> real;
  val aggregate : data -> CSpace.conSpecData -> Construction.construction list -> userProfile -> real;
end

structure CognitiveCosts : COGNITIVECOSTS =
struct
  type userProfile = real
  type data = {registration : string * CSpace.constructor -> string option,
               quantityScale : string * Type.typ -> string option,
               complexity : string * CSpace.constructor -> real option}
  val empty = {registration = fn _ => NONE,
               quantityScale = fn _ => NONE,
               complexity = fn _ => NONE}

  exception IllDefined of string
  fun joinCognitiveData {registration = tr, quantityScale = qs, complexity = cx}
                        {registration = tr', quantityScale = qs', complexity = cx'} =
    let fun CX x = (case (cx x, cx' x) of (NONE, res) => res
                                        | (SOME y,SOME y') => if Real.==(y, y') then SOME y else raise IllDefined ("inconsistent exp complexity " ^ Real.toString y ^ " and " ^ Real.toString y' ^ " for " ^ CSpace.nameOfConstructor (#2 x))
                                        | (res,_) => res)
        fun TR x = (case (tr x, tr' x) of (NONE, res) => res
                                        | (SOME y,SOME y') => if y = y' then SOME y else raise IllDefined ("inconsistent token reg " ^ y ^ " and " ^ y' ^ " for " ^ CSpace.nameOfConstructor (#2 x))
                                        | (res,_) => res)
        fun QS x = (case (qs x, qs' x) of (NONE, res) => res
                                        | (SOME y,SOME y') => if y = y' then SOME y else raise IllDefined ("inconsistent quantity scales " ^ y ^ " and " ^ y' ^ " for " ^ Type.nameOfType (#2 x))
                                        | (res,_) => res)
    in {registration = TR, quantityScale = QS, complexity = CX}
    end

  fun userWeight u = Math.pow(2.0,3.0*(1.0-u))
  fun propUserWeight s u =
    case s of
        "registration" => Math.pow(2.0-u, 2.0-u)
      | "quantityScale" => Math.pow(2.67-u, 2.0-u)
      | "complexity" => Math.pow(3.33-u, 2.0-u)
      | "heterogeneity" => Math.pow(4.0-u, 2.0-u)
      | _ => raise Match

  fun logisticNorm x0 x = 1.0 / (1.0 + Math.exp (~(4.0/x0) * (x-x0)))

(* registration *)
  (* number of symbols *)
  fun numberOfSymbols cts =
    let val tokens = List.flatmap (Construction.tokensOfConstruction) cts
    in FiniteSet.size tokens
    end

  (* variety of symbols *)
  fun varietyOfSymbols cts =
    let val tokens = List.flatmap (Construction.tokensOfConstruction) cts
        val types = FiniteSet.ofList (List.map CSpace.typeOfToken tokens)
    in FiniteSet.size types
    end

  (* variety of types *)
  fun types cts =
    let val tokens = List.flatmap (Construction.tokensOfConstruction) cts
    in FiniteSet.ofList (List.map CSpace.typeOfToken tokens)
    end
  (* variety of parent types *)
  fun parentTypes TSD tys =
    let fun parents ty = [Type.parentOfDanglyType ty] handle Type.badType => Type.immediateSuperTypes TSD ty
    in FiniteSet.ofList (List.flatmap parents (FiniteSet.listOf tys))
    end

  (* registration: there's a disount of (1.0-u/2.0) every step down the tree. Uncertain what this means if there's a loop *)
  fun registration cognitiveData conSpecData cts u =
    let val conSpecName = #name conSpecData
        fun tokenReg x = (#registration cognitiveData) (conSpecName,x)
        fun tokenRegVal x =
          (case x of SOME "icon" => 0.0625
                   | SOME "emergent" => 0.125
                   | SOME "spatial-index" => 0.25
                   | SOME "notational-index" => 0.5
                   | SOME "search" => 1.0
                   | NONE => 0.5
                   | SOME y => (print ("unknown token reg" ^ y ^ " ") ; raise Match))
        fun reg w (Construction.TCPair ({constructor,...},cs)) =
            let val discount = 1.0 - u/3.0
                val updWeight = discount * w
            in (w, w * tokenRegVal (tokenReg constructor)) (** real(length cs)*) :: List.flatmap (reg updWeight) cs
            end
          | reg w _ = [(0.0,0.0)]
        val rawVals = List.flatmap (reg 1.0) cts
        val rawVal = (List.sumMap #2 rawVals) (*)/ (List.sumMap #1 rawVals)*)
    in propUserWeight "registration" u * logisticNorm 4.0 rawVal
    end

(* semantic encoding *)
  (* Concept-mapping (assumes transfer happend from Bayes into the target space) *)

  (* ER-semantic process *)
  (* IR-semantic process *)

(* quantity scale *)
fun quantityScale cognitiveData conSpecData cts u =
  let val conSpecName = #name conSpecData
      val tokens = List.flatmap (Construction.tokensOfConstruction) cts
      val types = List.map CSpace.typeOfToken tokens
      fun qs x = (#quantityScale cognitiveData) (conSpecName,x)
      fun qsVal x =
        (case qs x of
           SOME "nominal" => 0.0
         | SOME "ordinal" => 1.0/3.0
         | SOME "interval" => 2.0/3.0
         | SOME "ratio" => 1.0
         | NONE => (qsVal (Type.parentOfDanglyType x) handle Type.badType => 0.25)
         | SOME s => (print ("unknown quantity scale " ^ s ^ " "); raise Match))
      val rawVal = List.avgIndexed qsVal types
  in propUserWeight "quantityScale" u * logisticNorm 0.5 rawVal
  end

(* expression complexity *)
fun expressionComplexity cognitiveData conSpecData cts u =
  let val conSpecName = #name conSpecData
      fun complexity x = case (#complexity cognitiveData) (conSpecName,x) of NONE => 0.0 | SOME r => r
      val discount = 1.0 - u/2.0
      fun weightedSize w (Construction.Source _) = 0.0
        | weightedSize w (Construction.Reference _) = 0.0
        | weightedSize w (Construction.TCPair ({constructor,...},cs)) = w * (complexity constructor + 1.0 + real(length cs)) + (List.sumMap (weightedSize (w * discount)) cs)
      val rawVal = List.sumMap (weightedSize 1.0) cts
  in propUserWeight "complexity" u * logisticNorm 45.0 rawVal
  end

(* Heterogeneity *)
  fun heterogeneity cognitiveData conSpecData cts u =
    let val TSD = #typeSystemData conSpecData
        val T = {typeSystem = #typeSystem TSD, principalTypes = #principalTypes TSD}
        val typs = types cts
        val parentTyps = parentTypes T typs
        val grandparentTyps = parentTypes T parentTyps
        val greatgrandparentTyps = parentTypes T grandparentTyps
        val l0 = greatgrandparentTyps
        val l1 = FiniteSet.minus grandparentTyps l0
        val l2 = FiniteSet.minus parentTyps (FiniteSet.union l1 l0)
        val l3 = FiniteSet.minus typs (FiniteSet.union l2 (FiniteSet.union l1 l0))
        fun discount n = Math.pow(1.0 - u/2.0,n)
        fun realLength L = real (length L)
        val rawVal = realLength l0 +
                      discount 1.0 * realLength l1 +
                      discount 2.0 * realLength l2 +
                      discount 3.0 * realLength l3
                      val _ = print ("\n\n" ^ Real.toString rawVal ^ "\n\n")
    in propUserWeight "heterogeneity" u * logisticNorm 8.0 rawVal
    end

(* infernce type *)
(* solution stuff *)

fun aggregate cognitiveData conSpecData cts u =
  let val reg = registration cognitiveData conSpecData cts u
      val qs = quantityScale cognitiveData conSpecData cts u
      val ec = expressionComplexity cognitiveData conSpecData cts u
      val het = heterogeneity cognitiveData conSpecData cts u
      (*val W = propUserWeight "registration" u +
              propUserWeight "quantityScale" u +
              propUserWeight "complexity" u +
              propUserWeight "heterogeneity" u*)
  in (*100.0 * logisticNorm (W / 2.0)*) (reg + qs + ec + het)
  end

end
