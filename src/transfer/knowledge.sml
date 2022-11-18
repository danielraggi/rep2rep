import "core.interCSpace";
import "core.composition";

signature KNOWLEDGE =
sig
  type iSchema = {context : Pattern.construction,
                  antecedent : Pattern.construction list,
                  consequent : Pattern.construction}
  type iSchemaData = {name : string,
                      contextConSpecN : string,
                      idConSpecN : string,
                      iSchema : iSchema}
  type base

  (* TransferSchema knowledge *)
  val inferenceSchemasOf : base -> iSchemaData Seq.seq;
  val transferSchemasOf : base -> InterCSpace.tSchemaData Seq.seq;
  val strengthOf : base -> string -> real option

  (* Building a knowledge base *)
  val addInferenceSchema : base -> iSchemaData -> real -> (iSchemaData * iSchemaData -> order) -> base;
  val addTransferSchema : base -> InterCSpace.tSchemaData -> real -> (InterCSpace.tSchemaData * InterCSpace.tSchemaData -> order) -> base;
  val filterForISpace : string -> base -> base;

  val findInferenceSchemaWithName : base -> string -> iSchemaData option;
  val findTransferSchemaWithName : base -> string -> InterCSpace.tSchemaData option;

  val join : base -> base -> base;
  val empty : base;
end;

structure Knowledge : KNOWLEDGE =
struct
  type iSchema = {context : Pattern.pattern,
                  antecedent : Pattern.pattern list,
                  consequent : Pattern.pattern}
  type iSchemaData = {name : string,
                      contextConSpecN : string,
                      idConSpecN : string,
                      iSchema : iSchema}
  type base = {transferSchemas : InterCSpace.tSchemaData Seq.seq,
               inferenceSchemas : iSchemaData Seq.seq,
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

  fun filterForISpace name KB =
    {inferenceSchemas = Seq.filter (fn x => #idConSpecN x = name) (#inferenceSchemas KB),
     transferSchemas = Seq.filter (fn x => #interConSpecN x = name) (#transferSchemas KB),
     strength = #strength KB}


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
