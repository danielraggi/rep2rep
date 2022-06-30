import "core.interCSpace";
import "core.composition";

signature KNOWLEDGE =
sig
  type base

  (* CSpace knowledge *)


  (* Relational knowledge *)
(*)  val relationshipsOf : base -> Relation.relationship FiniteSet.set;*)
  (*val related : base -> Relation.T -> CSpace.token list -> CSpace.token list -> bool;*)
(*)  val subRelation : base -> Relation.T -> Relation.T -> bool;*)

  (* TransferSchema knowledge *)
  val transferSchemasOf : base -> InterCSpace.tSchema Seq.seq;
  val strengthOf : base -> string -> real option

  (* Building a knowledge base *)
  val addTransferSchema : base -> InterCSpace.tSchema -> real -> (InterCSpace.tSchema * InterCSpace.tSchema -> order) -> base;

  (*val addRelationships : base -> Relation.relationship list -> base;*)
  val findTransferSchemaWithName : base -> string -> InterCSpace.tSchema option;

  val join : base -> base -> base;
  val empty : base;
end;

structure Knowledge : KNOWLEDGE =
struct
  type base = {(*relationships : Relation.relationship FiniteSet.set,*)
               (*subRelation : Relation.T * Relation.T -> bool,*)
               transferSchemas : InterCSpace.tSchema Seq.seq,
               strength : string -> real option};

  (* Relational knowledge *)
  (*fun subRelation KB R1 R2 = (#subRelation KB) (R1,R2);*)
(*)
  fun related KB R a b =
    let fun sat (X,Y,R') = List.allZip CSpace.sameTokens a X andalso List.allZip CSpace.sameTokens b Y andalso subRelation KB R' R
    in Relation.same R Relation.alwaysTrue orelse Option.isSome (FiniteSet.find sat (relationshipsOf KB))
    end;*)

  (* TransferSchema knowledge *)
  fun transferSchemasOf KB = #transferSchemas KB;
  fun strengthOf KB = #strength KB

  fun addTransferSchema KB tsch s f =
    {(*relationships= #relationships KB,*)
      (*subRelation = #subRelation KB,*)
      transferSchemas = Seq.insert tsch (#transferSchemas KB) f,
      strength = (fn cn => if #name tsch = cn then SOME s else (#strength KB) cn)}

(*fun addRelationships KB rels =
    {relationships= FiniteSet.union (#relationships KB) rels,
      subRelation = #subRelation KB,
      transferSchemas = #transferSchemas KB}*)

  fun findTransferSchemaWithName KB name =
    Seq.findFirst (fn x => InterCSpace.nameOf x = name) (#transferSchemas KB)

  fun subRelUnion subR1 subR2 (x,y) = subR1(x,y) orelse subR2(x,y)

  fun join k1 k2 =
    {(*subRelation = subRelUnion (#subRelation k1) (#subRelation k2),*)
     transferSchemas = Seq.append (#transferSchemas k1) (#transferSchemas k2),
     strength = (fn cn => case (#strength k2) cn of SOME r => SOME r | NONE => (#strength k1) cn)}

  val empty =
    let fun subrel (R1,R2) = Relation.same R1 R2
    in {(*relationships= FiniteSet.ofList rels,*)
        (*subRelation = subrel,*)
        transferSchemas = Seq.empty,
        strength = (fn _ => NONE)}
  end
end;
