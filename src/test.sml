import "oruga.CParsers";
import "server.prob_renderers";
(*)
val ss = CParsers.parseProbSys "Pr(-x | y) = 0.63; Pr(s) = 0.5";
val _ = print "\n";
val _ = print (Latex.construction (0.0, 0.0) ss);
val _ = print "\n";*)
exception TestError

val DC = Document.read "probability"
val KB = Document.knowledgeOf DC
val Bayes = Document.findConSpecWithName DC "bayesG"
val Area = Document.findConSpecWithName DC "areaDiagramG"
val Table = Document.findConSpecWithName DC "contTableG"
val Tree = Document.findConSpecWithName DC "probTreeG"

val interBayesArea = Document.findConSpecWithName DC "interBayesArea"
val interBayesTable = Document.findConSpecWithName DC "interBayesTable"
val interBayesTree = Document.findConSpecWithName DC "interBayesTree"

val ss1 = CParsers.parseProbSys "Pr(D) = 0.04; Pr(T | D) = 0.95; Pr(-T | -D) = 0.9";
val construct = Construction.constructOf ss1
val areaGoal = Document.parseConstruction interBayesArea (":metaTrue <- encode[" ^  CSpace.stringOfToken (construct) ^ ",t':area]")
val tableGoal = Document.parseConstruction interBayesTable (":metaTrue <- encode[" ^  CSpace.stringOfToken (construct) ^ ",t':table]")
val treeGoal = Document.parseConstruction interBayesTree (":metaTrue <- encode[" ^  CSpace.stringOfToken (construct) ^ ",t':tree]")


val startTime = Time.now();
val t1 = ProbRender.drawBayes [ss1]
val _ = print "1\n"
val areaResult = case Transfer.applyTransfer Bayes Area interBayesArea KB ss1 areaGoal of (Result.OK (h::_)) => h | _ => raise TestError
val _ = print "2\n"
val t2 = ProbRender.drawArea [areaResult]
val _ = print "3\n"
val tableResult = case Transfer.applyTransfer Bayes Table interBayesTable KB ss1 tableGoal of (Result.OK (h::_)) => h | _ => raise TestError
val _ = print "4\n"
val t3 = ProbRender.drawTable [tableResult]
val _ = print "5\n"
val treeResult = case Transfer.applyTransfer Bayes Tree interBayesTree KB ss1 treeGoal of (Result.OK (h::_)) => h | _ => raise TestError
val _ = print "6\n"
val t4 = ProbRender.drawTree [treeResult]
val _ = print "7\n"
val endTime = Time.now();
val _ = print "\n";
val runtime = Time.toMilliseconds endTime - Time.toMilliseconds startTime;
val _ = print "\n";
val _ = print (Latex.construction (0.0, 0.0) ss1);
val _ = print "\n";
val _ = print ("  runtime: "^ LargeInt.toString runtime ^ " ms \n...done\n  ");
val _= print "\n";

val _= print "\n\n";
val _= case t1 of Result.OK (h::_) => print (#1 (#2 h)) | _ => raise TestError;
val _= print "\n\n";
val _= case t2 of Result.OK (h::_) => print (#1 (#2 h)) | _ => raise TestError;
val _= print "\n\n";
val _= case t3 of Result.OK (h::_) => print (#1 (#2 h)) | _ => raise TestError;
val _= print "\n\n";
val _= case t4 of Result.OK (h::_) => print (#1 (#2 h)) | _ => raise TestError;
