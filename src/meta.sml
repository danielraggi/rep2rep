import "oruga.document";
import "oruga.SMLCParsers";

 fun realToString z =
    let val zs = Real.fmt (StringCvt.FIX (SOME 2)) z
    in case (String.explode zs) of
          (#"~"::n) => ("-" ^ String.implode n)
        | n => zs
    end

fun nSpaces n = if n <= 0 then "" else " " ^ nSpaces (n-1)
fun matrixToString ([h1]::LL) = h1 ^ "\n" ^ matrixToString LL
  | matrixToString ((h1::L1)::LL) = h1 ^ nSpaces(6 - size h1) ^ " " ^ matrixToString (L1::LL)
  | matrixToString ([]::LL) = raise Match
  | matrixToString [] = ""

fun transferProbabilityMeta sCSD tCSD iCSD KB ct goal =
    let val probDoc = Document.read "probability"
        val cogData = #cognitiveData probDoc
        val st = Transfer.initState sCSD tCSD iCSD false KB ct goal
        val stateSeq = Transfer.structureTransfer (SOME 6,NONE,NONE) true false NONE st;
        fun getStructureGraph st =
            List.flatmap Composition.resultingConstructions (State.patternCompsOf st);
        fun makeDiagnostic goal =
            let val str = Construction.toString goal;
                val toks = FiniteSet.listOf
                                (Construction.tokensOfConstruction goal);
                fun hexDigit c = Char.contains "0123456789ABCDEFabcdef" c;
                fun couldBeId [] = false
                | couldBeId [c] = hexDigit c
                | couldBeId (c::cs) = if c = #"-" orelse hexDigit c
                                        then List.all hexDigit cs
                                        else false;
                fun asId s = if couldBeId (String.explode s) then SOME s else NONE;
                val ids = List.mapPartial (asId o CSpace.nameOfToken) toks;
            in Diagnostic.create
                    Diagnostic.ERROR
                    ("Transfer failed due to open goal: " ^ str)
                    ids
            end;
        val firstState = Seq.hd stateSeq;
        val cts = getStructureGraph firstState

        (* start cog costs *)
        val reg = CognitiveCosts.registration cogData tCSD cts
        val qs = CognitiveCosts.quantityScale cogData tCSD cts
        val ec = CognitiveCosts.expressionComplexity cogData tCSD cts
        val het = CognitiveCosts.heterogeneity cogData tCSD cts
        val agg = CognitiveCosts.aggregate cogData tCSD cts
        val users = [0.1,0.3,0.5,0.7,0.9]
        val usersS = ["user                ","nov  ","beg  ","inter","adv  ","expert"]
        val regS = "registration        " :: map (realToString o reg) users
        val qsS = "quantityScale       " :: map (realToString o qs) users
        val ecS = "expressionComplexity" :: map (realToString o ec) users
        val hetS = "heterogeneity       " :: map (realToString o het) users
        val aggS = "aggregate           " :: map (realToString o agg) users
        val goals = State.goalsOf firstState;
    in case goals of
            [] => (print ("\n" ^ matrixToString [usersS,regS,qsS,ecS,hetS,aggS]); Result.ok cts)
        | _ => Result.error (List.map makeDiagnostic goals)
    end


  fun makeCognitiveMatrix cogData tCSD cts =
    let val reg = CognitiveCosts.registration cogData tCSD cts
        val qs = CognitiveCosts.quantityScale cogData tCSD cts
        val ec = CognitiveCosts.expressionComplexity cogData tCSD cts
        val het = CognitiveCosts.heterogeneity cogData tCSD cts
        val agg = CognitiveCosts.aggregate cogData tCSD cts
        val users = [0.1,0.3,0.5,0.7,0.9]
        val usersS = ["user                ","nov  ","beg  ","inter","adv  ","expert"]
        val regS = "registration        " :: map (realToString o reg) users
        val qsS = "quantityScale       " :: map (realToString o qs) users
        val ecS = "expressionComplexity" :: map (realToString o ec) users
        val hetS = "heterogeneity       " :: map (realToString o het) users
        val aggS = "aggregate           " :: map (realToString o agg) users
    in [usersS,regS,qsS,ecS,hetS,aggS]
    end

  fun transfer sCSD tCSD iCSD KB ct goal =
      let val st = Transfer.initState sCSD tCSD iCSD false KB ct goal
          val stateSeq = Transfer.structureTransfer (SOME 6,NONE,NONE) true false NONE st;
          fun getStructureGraph st =
              List.flatmap Composition.resultingConstructions (State.patternCompsOf st);
          fun makeDiagnostic goal =
              let val str = Construction.toString goal;
                  val toks = FiniteSet.listOf
                                  (Construction.tokensOfConstruction goal);
                  fun hexDigit c = Char.contains "0123456789ABCDEFabcdef" c;
                  fun couldBeId [] = false
                  | couldBeId [c] = hexDigit c
                  | couldBeId (c::cs) = if c = #"-" orelse hexDigit c
                                          then List.all hexDigit cs
                                          else false;
                  fun asId s = if couldBeId (String.explode s) then SOME s else NONE;
                  val ids = List.mapPartial (asId o CSpace.nameOfToken) toks;
              in Diagnostic.create
                      Diagnostic.ERROR
                      ("Transfer failed due to open goal: " ^ str)
                      ids
              end;
          val firstState = Seq.hd stateSeq;
          val cts = getStructureGraph firstState
          val goals = State.goalsOf firstState;
      in case goals of
            [] => cts
          | _ => raise Match
      end

val probDoc = Document.read "probability";
val cogData = #cognitiveData probDoc
val KB = Document.knowledgeOf probDoc
val bayesConSpecData = Document.getConSpecWithName probDoc "bayesG";
val areaConSpecData = Document.getConSpecWithName probDoc "areaDiagramG";
val treeConSpecData = Document.getConSpecWithName probDoc "probTreeG";
val tableConSpecData = Document.getConSpecWithName probDoc "contTableG";
val interBayesArea = Document.getConSpecWithName probDoc "interBayesArea";
val interBayesTree = Document.getConSpecWithName probDoc "interBayesTree";
val interBayesTable = Document.getConSpecWithName probDoc "interBayesTable";

val ct = SMLCParsers.parseProbSys "Pr(A|B) = 0.95; Pr(B) = 0.1; Pr(-A|-B) = 0.9";
val goalArea = Document.parseConstruction interBayesArea "x:metaTrue <- encode[t_{0}:Pr(A|B)=0.95; Pr(B)=0.1; Pr(-A|-B)=0.9:probSys,t':area]";
val goalTable = Document.parseConstruction interBayesTable "x:metaTrue <- encode[t_{0}:Pr(A|B)=0.95; Pr(B)=0.1; Pr(-A|-B)=0.9:probSys,t':table]";
val goalTree = Document.parseConstruction interBayesTree "x:metaTrue <- encode[t_{0}:Pr(A|B)=0.95; Pr(B)=0.1; Pr(-A|-B)=0.9:probSys,t':tree]";

val areasResults = transfer bayesConSpecData areaConSpecData interBayesArea KB ct goalArea;
val tableResults = transfer bayesConSpecData tableConSpecData interBayesTable KB ct goalTable;
val treeResults = transfer bayesConSpecData treeConSpecData interBayesTree KB ct goalTree;

val bayesCogMatrix = makeCognitiveMatrix cogData bayesConSpecData [ct]
val areaCogMatrix = makeCognitiveMatrix cogData areaConSpecData areasResults
val tableCogMatrix = makeCognitiveMatrix cogData tableConSpecData tableResults
val treeCogMatrix = makeCognitiveMatrix cogData treeConSpecData treeResults

val m0 = "**** Bayes ****\n" ^ matrixToString bayesCogMatrix
val m1 = "**** Area ****\n" ^ matrixToString areaCogMatrix
val m2 = "**** Table ****\n" ^ matrixToString tableCogMatrix
val m3 = "**** Tree ****\n" ^ matrixToString treeCogMatrix;

print ("\n" ^ m0 ^ "\n" ^ m1 ^ "\n" ^ m2 ^ "\n" ^ m3 ^ "\n");
