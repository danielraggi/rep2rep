import "core.interCSpace";
import "core.composition";

signature KNOWLEDGE =
sig
  type iSchema = {name : string,
                  context : Pattern.construction,
                  antecedent : Pattern.construction list,
                  consequent : Pattern.construction}
  type base

  (* TransferSchema knowledge *)
  val inferenceSchemasOf : base -> iSchema Seq.seq;
  val transferSchemasOf : base -> InterCSpace.tSchema Seq.seq;
  val strengthOf : base -> string -> real option

  (* Building a knowledge base *)
  val addInferenceSchema : base -> iSchema -> real -> (iSchema * iSchema -> order) -> base;
  val addTransferSchema : base -> InterCSpace.tSchema -> real -> (InterCSpace.tSchema * InterCSpace.tSchema -> order) -> base;

  val findInferenceSchemaWithName : base -> string -> iSchema option;
  val findTransferSchemaWithName : base -> string -> InterCSpace.tSchema option;

  val join : base -> base -> base;
  val empty : base;
end;

structure Knowledge : KNOWLEDGE =
struct
  type iSchema = {name : string,
                  context : Pattern.pattern,
                  antecedent : Pattern.pattern list,
                  consequent : Pattern.pattern}
  type base = {transferSchemas : InterCSpace.tSchema Seq.seq,
               inferenceSchemas : iSchema Seq.seq,
               strength : string -> real option};

  (* TransferSchema knowledge *)
  fun inferenceSchemasOf KB = #inferenceSchemas KB;
  fun transferSchemasOf KB = #transferSchemas KB;
  fun strengthOf KB = #strength KB

  fun addInferenceSchema KB isch s f =
    {inferenceSchemas = Seq.insert isch (#inferenceSchemas KB) f,
     transferSchemas = #transferSchemas KB,
     strength = (fn cn => if #name isch = cn then SOME s else (#strength KB) cn)}

  fun addTransferSchema KB tsch s f =
    {inferenceSchemas = #inferenceSchemas KB,
     transferSchemas = Seq.insert tsch (#transferSchemas KB) f,
     strength = (fn cn => if #name tsch = cn then SOME s else (#strength KB) cn)}

  fun findInferenceSchemaWithName KB name =
    Seq.findFirst (fn x => #name x = name) (#inferenceSchemas KB)
  fun findTransferSchemaWithName KB name =
    Seq.findFirst (fn x => InterCSpace.nameOf x = name) (#transferSchemas KB)


  fun join k1 k2 =
    {inferenceSchemas = Seq.append (#inferenceSchemas k1) (#inferenceSchemas k2),
     transferSchemas = Seq.append (#transferSchemas k1) (#transferSchemas k2),
     strength = (fn cn => case (#strength k2) cn of SOME r => SOME r | NONE => (#strength k1) cn)}

  val empty =
    {inferenceSchemas = Seq.empty,
     transferSchemas = Seq.empty,
     strength = (fn _ => NONE)}

end;
