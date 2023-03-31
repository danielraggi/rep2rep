import "oruga.document";

signature COGNITIVECOSTS =
sig
  type userProfile
  val heterogeneity : State.T * userProfile -> real;
  val registration : State.T * userProfile -> real;
  val quantityScale : State.T * userProfile -> real;
  val conceptMapping : State.T * userProfile -> real;
  val expressionComplexity : State.T * userProfile -> real;
  val semanticProcess : State.T * userProfile -> real;
  val aggregate : State.T * userProfile -> real;
end

structure CognitiveCosts : COGNITIVECOSTS =
struct
  type userProfile = real


(* registration *)
  (* number of symbols *)
  fun numberOfSymbols st =
    let val cts = List.flatmap Composition.resultingConstructions (State.patternCompsOf st)
        val tokens = List.flatmap (Construction.tokensOfConstruction) cts
    in FiniteSet.size tokens
    end

  (* variety of symbols *)
  fun varietyOfSymbols st =
    let val cts = List.flatmap Composition.resultingConstructions (State.patternCompsOf st)
        val tokens = List.flatmap (Construction.tokensOfConstruction) cts
        val types = FiniteSet.ofList (List.map CSpace.typeOfToken tokens)
    in FiniteSet.size types
    end

  (* registration: there's a disount of (1.0-u/2.0) every step down the tree. Uncertain what this means if there's a loop *)
  fun registration (st,u) =
    let val tCS = State.targetConSpecDataOf st
        val cognitiveData = #cognitiveData tCS
        val tokenReg = #tokenRegistration cognitiveData
        fun tokenRegVal x = if x = "icon" then 0.2
                      else if x = "emergent" then 0.4
                      else if x = "spatial-index" then 0.6
                      else if x = "notational-index" then 0.8
                      else if x = "search" then 1.0
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
fun quantityScale (st,u) =
  let
  in (1.0-u/2.0)
  end

(* expression complexity *)
fun expressionComplexity (st,u) =
  let val cts = List.flatmap Composition.resultingConstructions (State.patternCompsOf st)
      val discount = 1.0 - u/2.0
      fun graphSize w (Construction.Source _) = 1.0
        | graphSize w (Construction.Reference _) = 0.0
        | graphSize w (Construction.TCPair (_,cs)) = 3.0 + real(length cs) + List.sumMap (graphSize (w * discount)) cs
  in List.sumMap (graphSize 1.0) cts
  end

(* Heterogeneity: don't use modes. Exploit types *)
  fun heterogeneity (st,u) =
    let val tCS = State.targetConSpecDataOf st
        val cognitiveData = #cognitiveData tCS
    in real (FiniteSet.size (#modes cognitiveData))
    end

(* infernce type *)
(* solution stuff *)

fun aggregate (st,u) =
  let val r = registration (st,u) (* lightest *)
      val qs = quantityScale (st,u) (* 3rd heaviest *)
      val ec = expressionComplexity (st,u) (* 2nd heaviest *)
      val h = heterogeneity (st,u) (* heaviest *)
      val userDepWeight = 8.0 / (7.0 * u + 1.0)
  in (1.0 * userDepWeight) * r +
     (2.0 * userDepWeight) * qs +
     (4.0 * userDepWeight) * ec +
     (8.0 * userDepWeight) * h
  end

end
