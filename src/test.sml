import "oruga.CParsers";
(*)
val ss = CParsers.parseProbSys "Pr(-x | y) = 0.63; Pr(s) = 0.5";
val _ = print "\n";
val _ = print (Latex.construction (0.0, 0.0) ss);
val _ = print "\n";*)

val startTime = Time.now();
val ss1 = CParsers.parseProbSys "Pr(-s | z) = 0.63; Pr(s) = 0.5; Pr(-z | -s) = 1";
val endTime = Time.now();
val _ = print "\n";
val runtime = Time.toMilliseconds endTime - Time.toMilliseconds startTime;
val _ = print "\n";
val _ = print (Latex.construction (0.0, 0.0) ss1);
val _ = print "\n";
val _ = print ("  runtime: "^ LargeInt.toString runtime ^ " ms \n...done\n  ");
