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
  val conSpecImportsOf : base -> (string * string list) list

  val conSpecIsImportedBy : (string * string list) list -> string -> string -> bool

  (* Building a knowledge base *)
  val addInferenceSchema : base -> iSchemaData -> real -> (iSchemaData * iSchemaData -> order) -> base;
  val addTransferSchema : base -> InterCSpace.tSchemaData -> real -> (InterCSpace.tSchemaData * InterCSpace.tSchemaData -> order) -> base;
  val addConSpecImports : base -> (string * string list) -> base
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
               strength : string -> real option,
               conSpecImports : (string * string list) list};

  (* TransferSchema knowledge *)
  fun inferenceSchemasOf KB = #inferenceSchemas KB
  fun transferSchemasOf KB = #transferSchemas KB
  fun strengthOf KB = #strength KB
  fun conSpecImportsOf KB = #conSpecImports KB

  fun addInferenceSchema KB isch s f =
    {inferenceSchemas = Seq.insert isch (#inferenceSchemas KB) f,
     transferSchemas = #transferSchemas KB,
     conSpecImports = #conSpecImports KB,
     strength = (fn cn => if #name isch = cn then SOME s else (#strength KB) cn)}

  fun addTransferSchema KB tsch s f =
    {inferenceSchemas = #inferenceSchemas KB,
     transferSchemas = Seq.insert tsch (#transferSchemas KB) f,
     conSpecImports = #conSpecImports KB,
     strength = (fn cn => if #name tsch = cn then SOME s else (#strength KB) cn)}

  fun addConSpecImports KB (n,L) =
    {inferenceSchemas = #inferenceSchemas KB,
     transferSchemas = #transferSchemas KB,
     conSpecImports = (n,L) :: #conSpecImports KB,
     strength = #strength KB}

  fun conSpecIsImportedBy conSpecImports n1 n2 =
    List.exists (fn (x,L) => x = n2 andalso
                             (List.exists (fn y => n1 = y) L orelse List.exists (fn y => conSpecIsImportedBy conSpecImports n1 y) L))
                conSpecImports

  fun filterForISpace name KB =
    let val {conSpecImports,...} = KB
        fun iSchemaInISpace x =
            #idConSpecN x = name orelse conSpecIsImportedBy conSpecImports (#idConSpecN x) name
        fun tSchemaInISpace x =
            #interConSpecN x = name orelse conSpecIsImportedBy conSpecImports (#interConSpecN x) name
    in
      {inferenceSchemas = Seq.filter iSchemaInISpace (#inferenceSchemas KB),
       transferSchemas = Seq.filter tSchemaInISpace (#transferSchemas KB),
       conSpecImports = conSpecImports,
       strength = #strength KB}
    end


  fun findInferenceSchemaWithName KB name =
    Seq.findFirst (fn x => #name x = name) (#inferenceSchemas KB)
  fun findTransferSchemaWithName KB name =
    Seq.findFirst (fn x => InterCSpace.nameOf x = name) (#transferSchemas KB)


  fun join k1 k2 =
    {inferenceSchemas = Seq.append (#inferenceSchemas k1) (#inferenceSchemas k2),
     transferSchemas = Seq.append (#transferSchemas k1) (#transferSchemas k2),
     conSpecImports = (#conSpecImports k1) @ (#conSpecImports k2),
     strength = (fn cn => case (#strength k2) cn of SOME r => SOME r | NONE => (#strength k1) cn)}

  val empty =
    {inferenceSchemas = Seq.empty,
     transferSchemas = Seq.empty,
     conSpecImports = [],
     strength = (fn _ => NONE)}

end;
