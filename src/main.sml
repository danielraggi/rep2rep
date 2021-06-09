import "util.logging";
import "IO.input";
import "IO.latex";

(* To see a full trace of the algorithm, we enable logging.
   If this seems too 'noisy', you can use `Logging.disable ()`.
   (Alternatively, because disabled is the default logging state,
   you can just comment out the following line.)
*)
Logging.disable ();

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
             outputFileName] => (sourceTypeSystemFilename,
                                 targetTypeSystemFilename,
                                 correspondencesFilename,
                                 relationsFilename,
                                 constructionFilename,
                                 goalFilename,
                                 valOf (Int.fromString limit),
                                 outputFileName)
          | _ => raise BadArguments)
  in configuration end

  (* the following is just a test *)
  fun printableList [] = ""
    | printableList (h::t) = h ^ "\n" ^ printableList t;
    (*)
  val KB = Input.loadKnowledge "arithDotsCorrs" "arithDotsRels";
  val arithT = Input.loadTypeSystem "arithTypeSystem";
  val dotsT = Input.loadTypeSystem "dotsTypeSystem";
  val ct = Input.loadConstruction "1plus2plus3equalsn";
  val goal = Parser.relationship "([t:1plus2plus3equal3oB3plus1cBdiv2],[t':arrangement]) :: firstArgumentIsValid";
  val results = Transfer.structureTransfer KB arithT dotsT ct goal 100;
  val rL = Seq.list_of results;
  val comps = map State.patternCompOf rL;
  val rCons = List.take (map Composition.resultingConstructions comps,1);
  val xx = (Latex.construction (0.0,0.0) ct)
  val x = map (map (Latex.construction (0.0,0.0))) rCons;
  val p = printableList (map printableList x);*)
  (* test ends *)

fun main () =
  let val today = Date.fmt "%Y-%m-%d" (Date.fromTimeLocal (Time.now()));
      val version = "rep2rep-" ^ REP2REP_VERSION;
      val _ = Logging.write ("BEGIN algorithm-trace-"
                               ^ today
                               ^ " with "
                               ^ version ^ "\n");
      val (sourceTypeSystemFilename,
            targetTypeSystemFilename,
            correspondencesFilename,
            relationsFilename,
            constructionFilename,
            goalFilename,
            limit,
            outputFilename) = parseArgs ();
      val sourceTypeSystem = Input.loadTypeSystem sourceTypeSystemFilename
      val targetTypeSystem = Input.loadTypeSystem targetTypeSystemFilename
      val KB = Input.loadKnowledge correspondencesFilename relationsFilename
      val ct = Input.loadConstruction constructionFilename
      val goal = Input.loadGoal goalFilename
      val results = Transfer.structureTransfer KB sourceTypeSystem targetTypeSystem ct goal 100
      val comps = map State.patternCompOf (Seq.list_of results);
      val rCons = List.take (map Composition.resultingConstructions comps,limit);
      val latexCT = Latex.construction (0.0,0.0) ct
      val x = map (map (Latex.construction (0.0,0.0))) rCons;
      val latexResults = printableList (map printableList x)
      val outputFile = TextIO.openOut ("tests/latex/"^outputFilename^".tex")
      val _ = Latex.outputDocument outputFile (latexCT ^ "\n\n" ^ latexResults);
      val _ = TextIO.closeOut outputFile
  in ()
  end
