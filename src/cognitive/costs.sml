
(* sub-RS variety *)

(* registration *)
  (* number of symbols *)
  fun numberOfSymbols st =
    let val cts = List.flatmap Composition.resultingConstructions (State.compositionsOf st)
        val tokens = List.flatmap (Construction.tokensOfConstruction) cts
    in FiniteSet.size tokens
    end

  (* variety of symbols *)
  fun varietyOfSymbols st =
    let val cts = List.flatmap Composition.resultingConstructions (State.compositionsOf st)
        val tokens = List.flatmap (Construction.tokensOfConstruction) cts
        val types = FiniteSet.ofList (List.map CSpace.typeOfToken tokens)
    in FiniteSet.size types
    end

  (* registration *)
  fun registration st =
    let val cts = List.flatmap Composition.resultingConstructions (State.compositionsOf st)
        fun reg (TCPair ({constructor,...},cs)) =
              (regProcessValue (regProcess constructor)) * (List.sumMap reg cs)
          | reg _ = 1.0
        val m = mode (State.targetConSpecDataOf st)
    in List.sumMap (fn x => modeValue m * reg x) cts
    end

(* semantic encoding *)
  (* Concept-mapping (assumes transfer happend from Bayes into the target space) *)
  fun conceptMapping st =
    let val cts = List.flatmap Composition.resultingConstructions (State.compositionsOf st)
        val ctBayes = State.constructionOf st
        val sCS = 
        val tCS =
        val iCS =
        val _ = List.map (Transfer.applyTransfer )
    in List.sumMap (fn x => modeValue m * reg x) cts
    end
  (* ER-semantic process *)
  (* IR-semantic process *)

(* quantity scale *)


(* expression complexity *)
fun expressionComplexity st =
  let val cts = List.flatmap Composition.resultingConstructions (State.compositionsOf st)
      fun graphSize (Source _) = 1
        | graphSize (Reference _) = 0
        | graphSize (TCPair (_,cs)) = 3 + length cs + List.sumMapInt graphSize cs
  in List.sumMapInt graphSize cts
  end



(* infernce type *)
(* solution stuff *)
