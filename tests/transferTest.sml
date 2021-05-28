import "input.input";
val goal = Parser.relationship "([t:1plus2plus3],[t':arrangement]) :: count";
val numT = Parser.finiteTypeSystem "({1,2,3,1plus2,1plus2plus3,numExp,plus},{(1,numExp),(2,numExp),(3,numExp),(1plus2,numExp),(1plus2plus3,numExp)})";
val dotsT = Parser.finiteTypeSystem "({dot,arrangement},{(dot,arrangement)})";
val KB = Input.loadKnowledge "corrTest" "relTest";
val ct = Input.loadConstruction "constructionTest";
val results = Transfer.structureTransfer KB numT dotsT ct goal 10;
