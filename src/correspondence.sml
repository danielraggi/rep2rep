import "pattern"
import "relation"

signature CORRESPONDENCE =
sig
  type corr;
  val patternsOf : corr -> Pattern.T * Pattern.T;
  val relationshipsOf : corr -> Relation.relationship list * Relation.relationship;
  val ofRelation : Relation.T -> corr;
  val declareCorrespondence : Pattern.construction -> Pattern.construction -> Relation.T -> Relation.T;
end

structure Correspondence : CORRESPONDENCE =
struct
  type corr = Pattern.construction * Pattern.construction * Relation.relationship list * Relation.relationship;

  exception badForm
  fun wellFormed (sP,tP,rf,rc) =
  let fun inFoundations (t::L) fseq = List.exists (CSpace.sameTokens t) fseq andalso inFoundations L fseq | inFoundations [] fseq = true
      fun okAtFoundations ((sfseq,tfseq,Rf)::rfs) = inFoundations sfseq (Pattern.foundationSequence sP) andalso inFoundations tfseq (Pattern.foundationSequence tP) andalso okAtFoundations rfs
        | okAtFoundations [] = true
      fun okAtConstructs ([t],[t'],Rc) = CSpace.sameTokens t (Pattern.constructOf sP) andalso CSpace.sameTokens t' (Pattern.constructOf tP)
        | okAtConstructs _ => false
  in okAtConstructs rc andalso okAtFoundations rF
  end

  fun patternsOf (sP,tP,Rf,Rc) = (sP,tP);
  fun relationshipsOf (sP,tP,rfs,rc) = (rfs,rc);

  fun declareCorrespondence sP tP rfs rc = (sP,tP,rfs,rc);
  (*the following turns a relation between tokens into a correspondence, with Rf being the
    "always true" relation, and Rc being the relation we want.*)
  fun ofRelation R =
    let val lP = (Pattern.trivial (Relation.leftTypeOf R))
        val rP = (Pattern.trivial (Relation.rightTypeOf R))
        val lPc = Pattern.constructOf lP
        val rPc = Pattern.constructOf rP
        val lPfs = Pattern.foundationSequence lP
        val rPfs = Pattern.foundationSequence rP
    in declareCorrespondence lP rP (lPfs,rPfs,Relation.alwaysTrue) (lPc,rPc,R)
    end;

end
