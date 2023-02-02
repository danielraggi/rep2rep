(*
To run these tests:
$ polyc test/prob_renderers.sml -o test/prob_renderers
$ ./test/prob_renderers --transfer-map transferMap bayes probTree contTable areaDiagram arith transferSchemas/bayesTable transferSchemas/bayesArea transferSchemas/bayesTree
*)
use "base.sml";
import "probability.prob_parser";
import "transfer.structure_transfer";
import "server.server";
import "server.prob_renderers";


fun test_inputs () =
    let val testfile = TextIO.openIn "test/prob_inputs.txt";
        val lines = TextIO.inputLines testfile;
        val test_lines = List.filter
                             (fn line => let val line = String.stripSpaces line;
                                         in String.isPrefix "\"" line
                                            andalso String.isSuffix "\";" line end)
                             lines;
        val dropTrailingSemicolon =
            String.implode o List.rev o (List.dropWhile (curry op= #";")) o List.rev o String.explode;
        val make_input = String.removeDoubleQuotes o dropTrailingSemicolon o String.stripSpaces;
    in List.map make_input test_lines end;


(* Huge hack, we assume it's "encode" *)
fun mkGoal constr (interSpace : CSpace.conSpecData) =
    let val construct = Construction.constructOf constr;
        val encodeConstructor = FiniteSet.find (fn c => "encode" = CSpace.nameOfConstructor c) (#constructors interSpace);
        val types = Option.map CSpace.csig encodeConstructor;
        val (inTypes, outType) = case types of
                                     SOME((ins, out)) => (SOME(ins),SOME(out))
                                   | NONE => (NONE, NONE)
        val tgt_type = case inTypes of
                           SOME([_, t]) => SOME(t)
                         | _ =>  NONE
        val trueTok = Option.map (CSpace.makeToken "true") outType;
        val dummy = Option.map (CSpace.makeToken "tok") tgt_type;
    in case (encodeConstructor, trueTok, dummy) of
           (SOME(encodeConstructor), SOME(trueTok), SOME(dummy)) =>
           SOME(Construction.TCPair(
                     {token = trueTok, constructor = encodeConstructor},
                     [Construction.Source(construct), Construction.Source(dummy)]))
         | _ => NONE
    end;


fun getInterSpaceName srcSpaceName tgtSpaceName transferMap =
    case List.find (fn (a, b, c) => a = srcSpaceName andalso b = tgtSpaceName) transferMap of
        SOME(_, _, inter) => SOME(inter)
      | NONE => NONE;


fun transfer constr srcSpaceName tgtSpaceName transferMap spaces knowledge =
    let fun getSpace name = List.find (fn space => (#name space) = name) spaces;
        val srcSpace = getSpace srcSpaceName;
        val tgtSpace = getSpace tgtSpaceName;
        val interSpaceName = getInterSpaceName srcSpaceName tgtSpaceName transferMap;
        val intSpace = Option.mapPartial getSpace interSpaceName;
        val goal = Option.mapPartial (mkGoal constr) intSpace;
        fun err s = Result.error [Diagnostic.create Diagnostic.ERROR s []];
    in case (srcSpace, tgtSpace, intSpace, goal) of
           (SOME(s), SOME(t), SOME(i), SOME(g)) => Transfer.applyTransfer s t i knowledge constr g
         | (NONE, _, _, _) => err "No srcSpace!"
         | (_, NONE, _, _) => err "No tgtSpace!"
         | (_, _, NONE, _) => err "No intSpace!"
         | (_, _, _, NONE) => err "No goal!"
    end;


fun run_test transferMap spaces knowledge (input, expected_output) =
    let val () = print (input ^ "\n");
        val t = ProbParser.produce_construction input;
        val transfer = fn tgt => transfer t "bayesG" tgt transferMap spaces knowledge;
        val () = print "Area...";
        val t_area = transfer "areaDiagramG";
        val area_diagram = Result.flatmap ProbRender.drawArea t_area;
        val _ = case area_diagram of
                    Result.OK toks => print "done.\n"
                  | Result.ERROR errs => print ("\n" ^ (List.toString Diagnostic.message errs) ^ "\n");
        val () = print "Table...";
        val t_tabl = transfer "contTableG";
        val tabl_diagram = Result.flatmap ProbRender.drawTable t_tabl;
        val _ = case tabl_diagram of
                    Result.OK toks => print "done.\n"
                  | Result.ERROR errs => print ("\n" ^ (List.toString Diagnostic.message errs )^ "\n");
        val () = print "Tree...";
        val t_tree = transfer "probTreeG";
        val tree_diagram = Result.flatmap ProbRender.drawTree t_tree;
        val _ = case tree_diagram of
                    Result.OK toks => print "done.\n"
                  | Result.ERROR errs => print ("\n" ^ (List.toString Diagnostic.message errs) ^ "\n");
    in () end
    handle _ => print ("FAIL: " ^ input ^ "\n");


fun main () =
    let val (files, transferMap) =
            case CommandLine.arguments () of
                ("--transfer-map"::transferMap::files) => (files, Server.readTransferMap transferMap)
              | files => (files, []);

        val docs = List.map Document.read files;
        val spaces = List.flatmap Document.conSpecsDataOf docs;
        val typeSystems = List.flatmap Document.typeSystemsDataOf docs;
        val knowledge = List.foldl (fn (doc, kb) => Knowledge.join kb (Document.knowledgeOf doc))
                                   Knowledge.empty docs;

        val test_inputs = test_inputs ();
        val test_outputs = [];

        val tests = List.map (fn t => (t, "")) test_inputs; (* TODO: Get correct outputs, zip.*)

        val () = List.app (run_test transferMap spaces knowledge) tests;
    in () end;
