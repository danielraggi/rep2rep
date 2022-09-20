import "oruga.document";
import "works.prob_parser";
import "works.prob_renderer";

signature TRANSFERPROB = sig
    val renderArea: string -> unit
    val renderTable: string -> unit;
    val renderTree: string -> unit;
    val renderBayes: string -> unit;
end;

structure TransferProb : TRANSFERPROB = struct
fun renderArea p = 
    let val DC = Document.read "transferSchemas/bayesArea"
        val KB = Document.knowledgeOf DC
        val ST = #typeSystem (Document.findTypeSystemDataWithName DC "bayes")
        val TT = #typeSystem (Document.findTypeSystemDataWithName DC "areaDiagram")
        val x = ProbParser.produce_construction p
        val goal = Relation.makeRelationship ([(Construction.constructOf x)],[("t'","area")],"encode")
        val results = Transfer.masterTransfer false false NONE KB ST TT x goal
        val v = List.hd(Composition.resultingConstructions (State.patternCompOf (Seq.hd results)))
        val _ = ProbRender.drawArea v in
        ()
    end;

fun renderTable p = 
    let val DC = Document.read "transferSchemas/bayesTable"
        val KB = Document.knowledgeOf DC
        val ST = #typeSystem (Document.findTypeSystemDataWithName DC "bayes")
        val TT = #typeSystem (Document.findTypeSystemDataWithName DC "contTable")
        val x = ProbParser.produce_construction p
        val goal = Relation.makeRelationship ([(Construction.constructOf x)],[("t'","table")],"encode")
        val results = Transfer.masterTransfer false false NONE KB ST TT x goal
        val v = List.hd(Composition.resultingConstructions (State.patternCompOf (Seq.hd results)))
        val _ = ProbRender.drawTable v in
        ()
    end;

fun renderTree p = 
    let val DC = Document.read "transferSchemas/bayesTree"
        val KB = Document.knowledgeOf DC
        val ST = #typeSystem (Document.findTypeSystemDataWithName DC "bayes")
        val TT = #typeSystem (Document.findTypeSystemDataWithName DC "probTree")
        val x = ProbParser.produce_construction p
        val goal = Relation.makeRelationship ([(Construction.constructOf x)],[("t'","tree")],"encode")
        val results = Transfer.masterTransfer false false NONE KB ST TT x goal
        val v = List.hd(Composition.resultingConstructions (State.patternCompOf (Seq.hd results)))
        val _ = ProbRender.drawTree v in
        ()
    end;

fun renderBayes p = 
    let val v = ProbParser.produce_construction p
        val _ = ProbRender.drawBayes v in
        ()
    end;

end;
    