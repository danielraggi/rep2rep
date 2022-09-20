import "oruga.document";
import "works.pl_renderer";
import "works.pl_parser";

signature TRANSFERPL = sig
    val toBdd: string -> unit;
    val toVenn: string -> unit;
end;

structure TransferPL : TRANSFERPL = struct
fun toBdd p = 
    let val DC = Document.read "correspondences/plBdd"
        val KB = Document.knowledgeOf DC
        val ST = #typeSystem (Document.findTypeSystemDataWithName DC "pl")
        val TT = #typeSystem (Document.findTypeSystemDataWithName DC "bdd")
        val (x, _) = PLParser.produce_construction p
        val t = CSpace.typeOfToken (hd (Construction.fullTokenSequence x))
        val goal = Parser.relationship ("([t:"^t^"],[t':bddTree])::match")
        val results = Transfer.masterTransfer false false NONE KB ST TT x goal
        val v = Seq.hd results
        val _ = RenderPL.drawBdd (List.hd(Composition.resultingConstructions (State.patternCompOf v))) in
        ()
    end;

fun toVenn p = 
    let val DC = Document.read "correspondences/plVenn"
        val KB = Document.knowledgeOf DC
        val ST = #typeSystem (Document.findTypeSystemDataWithName DC "pl")
        val TT = #typeSystem (Document.findTypeSystemDataWithName DC "venn")
        val (x, _) = PLParser.produce_construction p
        val t = CSpace.typeOfToken (hd (Construction.fullTokenSequence x))
        val goal = Parser.relationship ("([t:"^t^"],[t':diagram])::match")
        val results = Transfer.masterTransfer false false NONE KB ST TT x goal
        val v = Seq.hd results
        val _ = RenderPL.drawVenn (List.hd(Composition.resultingConstructions (State.patternCompOf v))) in
        ()
    end;

end;