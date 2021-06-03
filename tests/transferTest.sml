import "input.input";
val KB = Input.loadKnowledge "arithDotsCorrs" "arithDotsRels";
val arithT = Input.loadTypeSystem "arithTypeSystem";
val dotsT = Input.loadTypeSystem "dotsTypeSystem";
val ct = Input.loadConstruction "1plus2plus3equalsn";
val goal = Parser.relationship "([t:1plus2plus3equal3oB3plus1cBdiv2],[t':arrangement]) :: firstArgumentIsValid";
val results = Transfer.structureTransfer KB arithT dotsT ct goal 100;
val rL = Seq.list_of results;

val ct' = Input.loadConstruction "1plus2plus3";
val goal' = Parser.relationship "([t:1plus2plus3],[t':arrangement]) :: count";
val results' = Transfer.structureTransfer KB arithT dotsT ct' goal' 10;
val rL' = Seq.list_of results';

val patt = Parser.pattern "t:formula <- u:infixRel:[formula,numExp,equal,numExp] <-[n:numExp,e:equal,m:numExp]";
Pattern.findMapAndGeneratorMatching arithT ct patt;

val cc = Parser.construction "t:numExp <- u:infixOp:[numExp,numExp,binOp,numExp]<-[n:numExp,p:plus,m:numExp]"
val c = Parser.construction "t':arrangement <- u':rotateX:[arrangement,arrangement] <-[t1':arrangement <- u1':remove:[arrangement,arrangement,arrangement]<-[t2':arrangement,t':arrangement]]"

val cc = Parser.construction "t312:oB3plus1cB <- u312:addParentheses:[numExp,oB,numExp,cB]<-[t3121:oB, t3122:3plus1 <- u3122:infixOp:[numExp,numExp,binOp,numExp]<-[t31221:3,t31222:plus,t31223:1],t3123::cB]";
val p = Parser.pattern "t:numExp <- u:addParentheses:[numExp,oB,numExp,cB] <-[toB:oB,x:numExp,tcB:cB]";
