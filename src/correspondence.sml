import "pattern";
import "relation";

signature CORRESPONDENCE =
sig
  type corr;
  val wellFormed : TypeSystem.typeSystem -> TypeSystem.typeSystem -> corr -> bool;
  val patternsOf : corr -> Pattern.pattern * Pattern.pattern;
  val relationshipsOf : corr -> Relation.relationship list * Relation.relationship;
  val ofRelationship : Relation.relationship -> corr;
  val declareCorrespondence : {sourcePattern : Pattern.construction,
                               targetPattern : Pattern.construction,
                               foundationRels : Relation.relationship list,
                               constructRel : Relation.relationship} -> corr;
end;

structure Correspondence : CORRESPONDENCE =
struct
  type corr = {sourcePattern : Pattern.construction,
               targetPattern : Pattern.construction,
               foundationRels : Relation.relationship list,
               constructRel : Relation.relationship};

  exception badForm
  fun wellFormed sT tT {sourcePattern,targetPattern,foundationRels,constructRel} =
    let fun inFoundations (t::L) fseq = List.exists (CSpace.sameTokens t) fseq andalso inFoundations L fseq | inFoundations [] _ = true
        fun okAtFoundations ((sfseq,tfseq,_)::rfs) = inFoundations sfseq (Pattern.foundationSequence sourcePattern) andalso inFoundations tfseq (Pattern.foundationSequence targetPattern) andalso okAtFoundations rfs
          | okAtFoundations [] = true
       fun okAtConstructs ([t],[t'],_) = CSpace.sameTokens t (Pattern.constructOf sourcePattern) andalso CSpace.sameTokens t' (Pattern.constructOf targetPattern)
          | okAtConstructs _ = false
    in Pattern.wellFormed sT sourcePattern andalso Pattern.wellFormed tT targetPattern
        andalso okAtConstructs constructRel andalso okAtFoundations foundationRels
    end

  fun patternsOf {sourcePattern,targetPattern,...} = (sourcePattern,targetPattern);
  fun relationshipsOf {foundationRels,constructRel,...} = (foundationRels,constructRel);

  fun declareCorrespondence x = x;
  (*the following turns a relation between tokens into a correspondence, with Rf being the
    "always true" relation, and Rc being the relation we want.*)
  exception nonBinary
  fun ofRelationship (xs,ys,R) =
    let val (sPc,tPc) = case (xs,ys) of ([x],[y]) => (x,y) | _ => raise nonBinary
        val sP = Pattern.Source sPc
        val tP = Pattern.Source tPc
    in {sourcePattern = sP,
      targetPattern = tP,
      foundationRels = [],
      constructRel = Relation.makeRelationship ([sPc],[tPc],R)}
    end;

end;
