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
      val endTime = Time.now()
      val _ = Logging.write ("structure transfer runtime: "^(LargeInt.toString (Time.toMilliseconds endTime - Time.toMilliseconds startTime)) ^ "\n")
      val comps = map State.patternCompOf (Seq.list_of results);
      val nres = length comps
      val _ = Logging.write ("number of results: " ^ Int.toString nres ^ "\n")
      val rCons = List.take (map Composition.resultingConstructions comps, Int.min(limit,nres));
      val latexCT = Latex.construction (0.0,0.0) construction
      val x = map (map (Latex.construction (0.0,0.0))) rCons;
        fun printableList [] = ""
          | printableList (h::t) = h ^ "\n \\hfill \n " ^ printableList t;
        fun subsectionedList _ [] = ""
          | subsectionedList i (h::t) = "\\subsection*{Result "^Int.toString i^"}\n" ^ h ^ subsectionedList (i+1) t;
      val latexResults = subsectionedList 1 (map printableList x)
      val outputFile = TextIO.openOut outputFile
      val opening = "\\section*{Original construction}\n"
      val resultText = "\\section*{Structure transfer results}\n"
      val _ = Latex.outputDocument outputFile (opening ^ latexCT ^ "\n\n " ^ resultText ^ latexResults);
      val _ = TextIO.closeOut outputFile
  in ()
  end
