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
  val filterForISpace : string -> bool -> base -> base;


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

  fun filterForISpace name inverse KB =
    let val {conSpecImports,...} = KB
        fun iSchemaInISpace x =
            #idConSpecN x = name orelse conSpecIsImportedBy conSpecImports (#idConSpecN x) name
        fun tSchemaInISpace x =
            #interConSpecN x = name orelse conSpecIsImportedBy conSpecImports (#interConSpecN x) name
        val relevantTSchemas = Seq.filter tSchemaInISpace (#transferSchemas KB)
        val tSchemas = if inverse then Seq.map InterCSpace.inverseData relevantTSchemas else relevantTSchemas
    in
      {inferenceSchemas = Seq.filter iSchemaInISpace (#inferenceSchemas KB),
       transferSchemas = tSchemas,
       conSpecImports = conSpecImports,
       strength = #strength KB}
    end


  fun findInferenceSchemaWithName KB name =
    Seq.findFirst (fn x => #name x = name) (#inferenceSchemas KB)
  fun findTransferSchemaWithName KB name =
    Seq.findFirst (fn x => InterCSpace.nameOf x = name) (#transferSchemas KB)

  fun cmpI (t1,t2) = List.compare String.compare ([#name t1,#idConSpecN t1],[#name t2,#idConSpecN t2])
  fun cmpT (t1,t2) = List.compare String.compare ([#name t1,#interConSpecN t1],[#name t2,#interConSpecN t2])

  fun join k1 k2 =
    {inferenceSchemas = Seq.insertManyNoEQUAL (#inferenceSchemas k1) (#inferenceSchemas k2) cmpI,
     transferSchemas = Seq.insertManyNoEQUAL (#transferSchemas k1) (#transferSchemas k2) cmpT,
     conSpecImports = List.removeDuplicates ((#conSpecImports k1) @ (#conSpecImports k2)),
     strength = (fn cn => case (#strength k2) cn of SOME r => SOME r | NONE => (#strength k1) cn)}

  val empty =
    {inferenceSchemas = Seq.empty,
     transferSchemas = Seq.empty,
     conSpecImports = [],
     strength = (fn _ => NONE)}

end;
