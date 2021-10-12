import "core.pattern";
import "core.relation";

signature CORRESPONDENCE =
sig
  type corr = {name : string,
               sourcePattern : Pattern.construction,
               targetPattern : Pattern.construction,
               tokenRels : Relation.relationship list,
               constructRel : Relation.relationship};
  val wellFormed : Type.typeSystem -> Type.typeSystem -> corr -> bool;
  val nameOf : corr -> string;
  val patternsOf : corr -> Pattern.pattern * Pattern.pattern;
  val relationshipsOf : corr -> Relation.relationship list * Relation.relationship;
  val ofRelationship : Relation.relationship -> string -> corr;
  val declareCorrespondence : {name : string,
                               sourcePattern : Pattern.construction,
                               targetPattern : Pattern.construction,
                               tokenRels : Relation.relationship list,
                               constructRel : Relation.relationship} -> corr;
end;

structure Correspondence : CORRESPONDENCE =
struct
  type corr = {name : string,
               sourcePattern : Pattern.construction,
               targetPattern : Pattern.construction,
               tokenRels : Relation.relationship list,
               constructRel : Relation.relationship};

  exception badForm
  fun wellFormed sT tT {name,sourcePattern,targetPattern,tokenRels,constructRel} =
    let fun inFoundations (t::L) fseq = List.exists (CSpace.sameTokens t) fseq andalso inFoundations L fseq
          | inFoundations [] _ = true
        fun okAtFoundations ((sfseq,tfseq,_)::rfs) = inFoundations (sfseq @ tfseq) ((Pattern.foundationSequence sourcePattern) @ (Pattern.foundationSequence targetPattern))
                                                      andalso okAtFoundations rfs
          | okAtFoundations [] = true
       fun okAtConstructs ([t],[t'],_) = CSpace.sameTokens t (Pattern.constructOf sourcePattern) andalso CSpace.sameTokens t' (Pattern.constructOf targetPattern)
          | okAtConstructs _ = false
    in Pattern.wellFormed sT sourcePattern andalso Pattern.wellFormed tT targetPattern
        andalso okAtConstructs constructRel andalso okAtFoundations tokenRels
    end

  fun nameOf {name,...} = name;

  fun patternsOf {sourcePattern,targetPattern,...} = (sourcePattern,targetPattern);
  fun relationshipsOf {tokenRels,constructRel,...} = (tokenRels,constructRel);

  fun declareCorrespondence x = x;
  (*the following turns a relation between tokens into a correspondence, with Rf being the
    "always true" relation, and Rc being the relation we want.*)
  exception nonBinary
  fun ofRelationship (xs,ys,R) name =
    let val (sPc,tPc) = case (xs,ys) of ([x],[y]) => (x,y) | _ => raise nonBinary
        val sP = Pattern.Source sPc
        val tP = Pattern.Source tPc
    in {name = name,
        sourcePattern = sP,
        targetPattern = tP,
        tokenRels = [],
        constructRel = Relation.makeRelationship ([sPc],[tPc],R)}
    end;

end;
