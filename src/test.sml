import "oruga.CParsers";

val ss1 = CParsers.parseProbSys "Pr(-x | y) = 0.63; Pr(s) = 0.5; Pr(z | s) = 1";
val _ = print "\n";
val _ = print (Latex.construction (0.0, 0.0) ss1);
val _ = print "\n";
