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

  fun userDepWeight u = Math.pow(2.0,3.0*(1.0-u))
  fun logistic L k x0 x = L / (1.0 + Math.exp (~k * (x-x0)))

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
        val rawVal = (List.sumMap #2 rawVals) / (List.sumMap #1 rawVals)
    in userDepWeight u * logistic 1.0 9.0 0.4 rawVal
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
           SOME "nominal" => 0.25
         | SOME "ordinal" => 0.5
         | SOME "interval" => 0.75
         | SOME "ratio" => 1.0
         | NONE => (qsVal (Type.parentOfDanglyType x) handle Type.badType => 0.25)
         | SOME s => (print ("unknown quantity scale " ^ s ^ " "); raise Match))
  in 2.0 * userDepWeight u * (List.avgIndexed qsVal types)
  end

(* expression complexity *)
fun expressionComplexity cognitiveData conSpecData cts u =
  let val conSpecName = #name conSpecData
      fun complexity x = case (#complexity cognitiveData) (conSpecName,x) of NONE => 0.0 | SOME r => r
      val discount = 1.0 - u/2.0
      fun graphSize w (Construction.Source _) = 1.0
        | graphSize w (Construction.Reference _) = 0.0
        | graphSize w (Construction.TCPair ({constructor,...},cs)) = w * (3.0 + complexity constructor + real(length cs)) + (List.sumMap (graphSize (w * discount)) cs)
      val rawVal = List.sumMap (graphSize 1.0) cts
  in userDepWeight u * logistic 4.0 0.07 70.0 rawVal
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
        val l1 = FiniteSet.union l0 grandparentTyps
        val l2 = FiniteSet.union l1 parentTyps
        val l3 = FiniteSet.union l2 typs
        val rawVal = real (length l0 + length l1 + length l2 + length l3)
    in userDepWeight u * logistic 8.0 0.1 30.0 rawVal
    end

(* infernce type *)
(* solution stuff *)

fun aggregate cognitiveData conSpecData cts u =
  let val reg = registration cognitiveData conSpecData cts u
      val qs = quantityScale cognitiveData conSpecData cts u
      val ec = expressionComplexity cognitiveData conSpecData cts u
      val het = heterogeneity cognitiveData conSpecData cts u
  in reg + qs + ec + het
  end

end
