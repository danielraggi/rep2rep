import "oruga.CParsers";
import "oruga.SMLCParsers";
import "server.prob_renderers";
(*)
val ss = CParsers.parseProbSys "Pr(-x | y) = 0.63; Pr(s) = 0.5";
val _ = print "\n";
val _ = print (Latex.construction (0.0, 0.0) ss);
val _ = print "\n";*)
exception TestError

val DC = Document.read "probability"
val KB = Document.knowledgeOf DC
val Bayes = Document.getConSpecWithName DC "bayesG"
val Area = Document.getConSpecWithName DC "areaDiagramG"
val Table = Document.getConSpecWithName DC "contTableG"
val Tree = Document.getConSpecWithName DC "probTreeG"

val interBayesArea = Document.getConSpecWithName DC "interBayesArea"
val interBayesTable = Document.getConSpecWithName DC "interBayesTable"
val interBayesTree = Document.getConSpecWithName DC "interBayesTree"

val startTime = Time.now();
val bayesConstruction = SMLCParsers.parseProbSys "Pr(disease) = 0.04; Pr(test | disease) = 0.95; Pr(-test | -disease) = 0.9";
(*val bayesConstruction = SMLCParsers.parseProbSys "Pr(A) = 0.2; Pr(A) = 0.5"*)
val construct = Construction.constructOf bayesConstruction
val areaGoal = Document.parseConstruction interBayesArea (":metaTrue <- encode[" ^ CSpace.stringOfToken (construct) ^ ",t':area]")
val tableGoal = Document.parseConstruction interBayesTable (":metaTrue <- encode[" ^ CSpace.stringOfToken (construct) ^ ",t':table]")
val treeGoal = Document.parseConstruction interBayesTree (":metaTrue <- encode[" ^ CSpace.stringOfToken (construct) ^ ",t':tree]")

val sLatex = (Latex.construction (0.0, 0.0) bayesConstruction);

val s1 = case ProbRender.drawBayes [bayesConstruction]
        of Result.OK (y::_) => ("Bayes:\n" ^ #1 (#2 y) ^ "\n")
         | _ => "\n   BAYES RENDERING: BAD\n"

val s2 =
  case Transfer.applyTransfer Bayes Area interBayesArea KB bayesConstruction areaGoal
  of (Result.OK (x::_)) => case (ProbRender.drawArea [x])
                           of (Result.OK (y::_)) => ("\nArea:\n" ^ #1 (#2 y) ^ "\n")
                            | _ => "\n   AREA TRANSFER: GOOD\n   AREA RENDERING: BAD\n"
   | _ => "\n   AREA TRANSFER: BAD\n  "

val s3 =
  case Transfer.applyTransfer Bayes Table interBayesTable KB bayesConstruction tableGoal
  of (Result.OK (x::_)) => case (ProbRender.drawTable [x])
                           of (Result.OK (y::_)) => ("\nTable:\n" ^ #1 (#2 y) ^ "\n")
                            | _ => "\n   TABLE TRANSFER: GOOD\n   TABLE RENDERING: BAD\n"
   | _ => "\n   TABLE TRANSFER: BAD\n  "

val s4 =
  case Transfer.applyTransfer Bayes Tree interBayesTree KB bayesConstruction treeGoal
  of (Result.OK (x::_)) => case (ProbRender.drawTree [x])
                           of (Result.OK (y::_)) => ("\nTree:\n" ^ #1 (#2 y) ^ "\n")
                            | _ => "\n   TREE TRANSFER: GOOD\n   TREE RENDERING: BAD\n"
   | _ => "\n   TREE TRANSFER: BAD\n  "

val endTime = Time.now();
val runtime = Time.toMilliseconds endTime - Time.toMilliseconds startTime;
print ("\n\nLaTeX:\n\n" ^ sLatex ^ "\n\n\nHTML:\n\n" ^ s1 ^ s2 ^ s3 ^ s4 ^ "\n\n  runtime: "^ LargeInt.toString runtime ^ " ms \n\n ");
