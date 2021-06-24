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
            outputFilePath) = parseArgs ();
      val _ = Logging.write ("Applying structure transfer...");
      val startTime = Time.now();
      val results = Transfer.structureTransfer KB sourceTypeSystem targetTypeSystem construction goal 1000;
      val endTime = Time.now();
      val runtime = Time.toMilliseconds endTime - Time.toMilliseconds startTime;
      val _ = Logging.write ("done\n" ^ "  runtime: "^ LargeInt.toString runtime ^ " ms \n");
      fun getCompsAndGoals [] = []
        | getCompsAndGoals (h::t) = (State.patternCompOf h, State.originalGoalOf h, State.goalsOf h) :: getCompsAndGoals t
      fun mkLatexGoals (goal,goals) =
        let val goalsS = String.concatWith "\\\\ \n " (map Latex.relationship goals)
            val originalGoalS = Latex.relationship goal ^ "\\\\ \n"
            val alignedGoals = "\n " ^ (Latex.environment "align*" "" ("\\mathbf{Original\\ goal}\\\\\n"^originalGoalS^"\\\\ \\mathbf{Open\\ goals}\\\\\n"^goalsS))
        in Latex.environment "minipage" "[t]{0.25\\textwidth}" alignedGoals
        end
      fun mkLatexConstructions comp =
        let val constructions = Composition.resultingConstructions comp;
        in map (Latex.construction (0.0,0.0)) constructions
        end
      fun mkLatexConstructionsAndGoals (comp,goal,goals) =
        let val latexConstructions = mkLatexConstructions comp
            val latexGoals = mkLatexGoals (goal,goals)
        in Latex.environment "center" "" (Latex.printWithHSpace 0.5 (latexConstructions @ [latexGoals]))
        end
      val nres = length (Seq.list_of results);
      val _ = Logging.write ("  number of results: " ^ Int.toString nres ^ "\n");
      val (listOfResults,_) = Seq.chop limit results;
      val compsAndGoals = getCompsAndGoals listOfResults;
      val _ = Logging.write "Composing patterns and creating tikz figures...";
      val latexCompsAndGoals = Latex.printSubSections 1 (map mkLatexConstructionsAndGoals compsAndGoals);
      val latexCT = Latex.construction (0.0,0.0) construction;
      val _ = Logging.write "done\n";
      val _ = Logging.write "Generating LaTeX document...";
      val latexOriginalConsAndGoals = Latex.environment "center" "" (latexCT);
      val outputFile = TextIO.openOut outputFilePath
      val opening = (Latex.sectionTitle false "Original construction") ^ "\n"
      val resultText = (Latex.sectionTitle false "Structure transfer results") ^ "\n"
      val _ = Latex.outputDocument outputFile (opening ^ latexOriginalConsAndGoals ^ "\n\n " ^ resultText ^ latexCompsAndGoals);
      val _ = TextIO.closeOut outputFile;
      val _ = Logging.write ("done!\n" ^ "  output file: "^outputFilePath^"\n");
  in ()
  end
