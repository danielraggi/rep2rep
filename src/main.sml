import "util.logging";
import "IO.input";
import "IO.latex";

(* To see a full trace of the algorithm, we enable logging.
   If this seems too 'noisy', you can use `Logging.disable ()`.
   (Alternatively, because disabled is the default logging state,
   you can just comment out the following line.)
*)
Logging.enable ();

fun filesMatchingPrefix dir prefix =
    let
        fun getWholeDir direc out = case OS.FileSys.readDir (direc) of
                                      SOME f => getWholeDir direc (f::out)
                                    | NONE => List.rev out;
        val dirstream = OS.FileSys.openDir dir;
        val filenames = getWholeDir dirstream [];
        val filteredFiles = List.filter (String.isPrefix prefix) filenames;
        fun attachDir p = dir ^ p;
    in
        map (OS.FileSys.realPath o attachDir) filteredFiles
    end
    handle OS.SysErr (a, b) => (raise OS.SysErr (a, b));

exception BadArguments
fun parseArgs () =
  let
    val args = CommandLine.arguments ();
    val configuration =
        (case args of
            [sourceTypeSystemFilename,
             targetTypeSystemFilename,
             correspondencesFilename,
             relationsFilename,
             constructionFilename,
             goalFilename,
             limit,
             outputFilename] => (Input.loadTypeSystem sourceTypeSystemFilename,
                                 Input.loadTypeSystem targetTypeSystemFilename,
                                 Input.loadKnowledge correspondencesFilename relationsFilename,
                                 Input.loadConstruction constructionFilename,
                                 Input.loadGoal goalFilename,
                                 valOf (Int.fromString limit),
                                 "tests/latex/"^outputFilename^".tex")
          | _ => raise BadArguments)
  in configuration end

fun main () =
  let val today = Date.fmt "%Y-%m-%d" (Date.fromTimeLocal (Time.now()));
      val version = "rep2rep-" ^ REP2REP_VERSION;
      val _ = Logging.write ("BEGIN algorithm-trace-"
                               ^ today
                               ^ " with "
                               ^ version ^ "\n");
      val (sourceTypeSystem,
            targetTypeSystem,
            KB,
            construction,
            goal,
            limit,
            outputFile) = parseArgs ();
      val startTime = Time.now();
      val results = Transfer.structureTransfer KB sourceTypeSystem targetTypeSystem construction goal 100;
      val endTime = Time.now();
      val _ = Logging.write ("structure transfer runtime: "^(LargeInt.toString (Time.toMilliseconds endTime - Time.toMilliseconds startTime)) ^ "\n");
      val (listOfResults,_) = Seq.chop limit results;
      fun getCompsAndGoals [] = []
        | getCompsAndGoals (h::t) = (State.patternCompOf h, State.goalsOf h) :: getCompsAndGoals t
      val compsAndGoals = getCompsAndGoals listOfResults;
      fun mkLatexCompsAndGoals [] = []
        | mkLatexCompsAndGoals ((comp,goals)::L) =
            let val constructions = Composition.resultingConstructions comp
                val latexConstructions = map (Latex.construction (0.0,0.0)) constructions
                val goalsS = String.concatWith "\\\\ \n " (map Latex.relationship goals)
                val alignedGoals = "\n " ^ (Latex.environment "align*" "" ("\\mathbf{Goals}\\\\\n"^goalsS))
                val latexGoals = Latex.environment "minipage" "[t]{0.25\\textwidth}" alignedGoals
            in Latex.printWithHSpace 0.7 (latexConstructions @ [latexGoals]) :: mkLatexCompsAndGoals L
            end
      val latexCompsAndGoals = Latex.printSubSections 1 (mkLatexCompsAndGoals compsAndGoals)
      val compositions = map State.patternCompOf listOfResults;
      val goals = map State.goalsOf listOfResults;
      val nres = length (Seq.list_of results);
      val _ = Logging.write ("number of results: " ^ Int.toString nres ^ "\n");
      val rCons = map Composition.resultingConstructions compositions;
      val latexCT = Latex.construction (0.0,0.0) construction
      val x = map (map (Latex.construction (0.0,0.0))) rCons;
      val latexResults = Latex.printSubSections 1 (map (Latex.printWithHSpace 0.7) x)
      val outputFile = TextIO.openOut outputFile
      val opening = (Latex.sectionTitle false "Original construction") ^ "\n"
      val resultText = (Latex.sectionTitle false "Structure transfer results") ^ "\n"
      val _ = Latex.outputDocument outputFile (opening ^ latexCT ^ "\n\n " ^ resultText ^ latexCompsAndGoals);
      val _ = TextIO.closeOut outputFile
  in ()
  end
