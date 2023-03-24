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

(* subRS-variety *)
  fun heterogeneity (st,u) =
    let val tCS = State.targetConSpecDataOf st
        val cognitiveData = #cognitiveData tCS
    in real (FiniteSet.size (#modes cognitiveData))
    end

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
        val modes = #modes cognitiveData
        fun modesVal x = if x = "grid" then 1.0
                     else if x = "containment" then 1.0
                     else if x = "axial" then 2.0
                     else if x = "sentential" then 2.0
                     else if x = "connection" then 3.0
                     else if x = "proportional" then 3.0
                     else (print "unknown mode"; raise Match)
        val modeVal = List.avgIndexed modesVal modes
        val tokenReg = #tokenRegistration cognitiveData
        fun tokenRegVal x = if x = "icon" then 1.0
                      else if x = "emergent" then 2.0
                      else if x = "spatial-index" then 3.0
                      else if x = "notational-index" then 4.0
                      else if x = "search" then 5.0
                      else (print "unknown token reg"; raise Match)
        val cts = List.flatmap Composition.resultingConstructions (State.patternCompsOf st)
        fun reg w (Construction.TCPair ({constructor,...},cs)) =
               (tokenRegVal (tokenReg constructor)) * (w + (1.0-u/2.0) * (List.sumMap (reg ((w + 1.0) / 2.0)) cs))
          | reg _ _ = 1.0
    in List.sumMap (fn x => reg modeVal x) cts
    end

(* semantic encoding *)
  (* Concept-mapping (assumes transfer happend from Bayes into the target space) *)
  fun conceptMapping (st,u) =
    let val cts = List.flatmap Composition.resultingConstructions (State.patternCompsOf st)
        val ctBayes = State.constructionOf st
        val sCS = State.sourceConSpecDataOf st
        val tCS = State.targetConSpecDataOf st
        val iCS = State.targetConSpecDataOf st
        (*val goal = Document.parseConstruction interBTreeBayesConSpecData (":metaTrue <- SYS[" ^ (CSpace.stringOfToken (hd cts)) ^ ",t':probSys]")*)
    in (1.0-u/2.0)
    end

  (* ER-semantic process *)
  (* IR-semantic process *)
  fun semanticProcess (st,u) =
    let
    in (1.0-u/2.0) * real (varietyOfSymbols st)
    end

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


(* infernce type *)
(* solution stuff *)

fun aggregate (st,u) =
  let val h = heterogeneity (st,u)
      val r = registration (st,u)
      val cm = conceptMapping (st,u)
      val sp = semanticProcess (st,u)
      val qs = quantityScale (st,u)
      val ec = expressionComplexity (st,u)
      val userDepWeight = 2.0 / (u + 1.0)
  in (2.0 + userDepWeight) * h +
     (1.0 + userDepWeight) * r +
     (2.0 + userDepWeight) * cm +
     (2.0 + userDepWeight) * sp +
     (1.0 + userDepWeight) * qs +
     (2.0 + userDepWeight) * ec
  end

end
