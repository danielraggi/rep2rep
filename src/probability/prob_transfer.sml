import "oruga.document";
import "works.prob_parser";
import "works.prob_renderer";

exception Error;

fun mkGoal constr interConstructors tgt_type =
    let val construct = Construction.constructOf constr;
        val encodeConstructor = FiniteSet.find (fn c => "encode" = CSpace.nameOfConstructor c) interConstructors;
        val trueTok = CSpace.makeToken "" (Type.fromString "metaTrue");
        val dummy = CSpace.makeToken "t'" (Type.fromString tgt_type);
    in case encodeConstructor of
           SOME(encodeConstructor) =>
           Construction.TCPair({token = trueTok, constructor = encodeConstructor},
                                [Construction.Source(construct), Construction.Source(dummy)])
         | _ => raise Error
    end;

fun filterResults (Result.OK x) = List.hd x
  | filterResults (Result.ERROR _) = raise Error;

fun renderArea p = 
    let val DC = Document.read "transferSchemas/bayesArea";
        val KB = Document.knowledgeOf DC;
        val S = Document.findConSpecWithName DC "bayesG";
        val T = Document.findConSpecWithName DC "areaDiagramG";
        val I = Document.findConSpecWithName DC "interBayesArea";
        val x = ProbParser.produce_construction p;
        val goal = mkGoal x (#constructors I) "area";
        val results = Transfer.applyTransfer S T I KB x goal;
        val v = filterResults results;
        val _ = drawArea v 
    in () end;

fun renderTable p = 
    let val DC = Document.read "transferSchemas/bayesTable";
        val KB = Document.knowledgeOf DC;
        val S = Document.findConSpecWithName DC "bayesG";
        val T = Document.findConSpecWithName DC "contTableG";
        val I = Document.findConSpecWithName DC "interBayesTable";
        val x = ProbParser.produce_construction p;
        val goal = mkGoal x (#constructors I) "table";
        val results = Transfer.applyTransfer S T I KB x goal;
        val v = filterResults results;
        val _ = drawTable v; 
    in v end;

fun renderTree p = 
    let val DC = Document.read "transferSchemas/bayesTree";
        val KB = Document.knowledgeOf DC;
        val S = Document.findConSpecWithName DC "bayesG";
        val T = Document.findConSpecWithName DC "probTreeG";
        val I = Document.findConSpecWithName DC "interBayesTree";
        val x = ProbParser.produce_construction p;
        val goal = mkGoal x (#constructors I) "tree";
        val results = Transfer.applyTransfer S T I KB x goal;
        val v = filterResults results;
        val _ = drawTree v; 
    in () end;

fun renderBayes p = 
    let val v = ProbParser.produce_construction p;
        val _ = drawBayes v; 
    in () end;
    
