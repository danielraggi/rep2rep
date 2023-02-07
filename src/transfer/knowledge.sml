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
                      strength : real,
                      iSchema : iSchema}
  type base

  (* TransferSchema knowledge *)
  val inferenceSchemasOf : base -> iSchemaData Seq.seq;
  val transferSchemasOf : base -> InterCSpace.tSchemaData Seq.seq;
  val conSpecImportsOf : base -> (string * string list) list

  val conSpecIsImportedBy : (string * string list) list -> string -> string -> bool

  (* Building a knowledge base *)
  val addInferenceSchema : base -> iSchemaData -> real -> base;
  val addTransferSchema : base -> InterCSpace.tSchemaData -> real -> base;
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
                      strength : real,
                      iSchema : iSchema}
  type base = {transferSchemas : InterCSpace.tSchemaData Seq.seq,
               inferenceSchemas : iSchemaData Seq.seq,
               conSpecImports : (string * string list) list};

  (* TransferSchema knowledge *)
  fun inferenceSchemasOf KB = #inferenceSchemas KB
  fun transferSchemasOf KB = #transferSchemas KB
  fun conSpecImportsOf KB = #conSpecImports KB

  exception Duplicate
  fun iCmp (i,i') = (case Real.compare (#strength i', #strength i) of EQUAL => (case String.compare (#name i,#name i') of EQUAL => raise Duplicate | y => y) | x => x)
  fun tCmp (t,t') = (case Real.compare (#strength t', #strength t) of EQUAL => (case String.compare (#name t,#name t') of EQUAL => raise Duplicate | y => y) | x => x)

  fun addInferenceSchema KB isch s =
    {inferenceSchemas = Seq.insert isch (#inferenceSchemas KB) iCmp,
     transferSchemas = #transferSchemas KB,
     conSpecImports = #conSpecImports KB}

  fun addTransferSchema KB tsch s =
    {inferenceSchemas = #inferenceSchemas KB,
     transferSchemas = Seq.insert tsch (#transferSchemas KB) tCmp,
     conSpecImports = #conSpecImports KB}

  fun addConSpecImports KB (n,L) =
    {inferenceSchemas = #inferenceSchemas KB,
     transferSchemas = #transferSchemas KB,
     conSpecImports = (n,L) :: #conSpecImports KB}

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
       conSpecImports = conSpecImports}
    end


  fun findInferenceSchemaWithName KB name =
    Seq.findFirst (fn x => #name x = name) (#inferenceSchemas KB)
  fun findTransferSchemaWithName KB name =
    Seq.findFirst (fn x => InterCSpace.nameOf x = name) (#transferSchemas KB)

  fun cmpI (t1,t2) = List.compare String.compare ([#name t1,#idConSpecN t1],[#name t2,#idConSpecN t2])
  fun cmpT (t1,t2) = List.compare String.compare ([#name t1,#interConSpecN t1],[#name t2,#interConSpecN t2])
  fun cmpCS ((s,L),(s',L')) = List.compare String.compare ((s::L),(s'::L'))

  fun join k1 k2 =
    {inferenceSchemas = Seq.insertManyNoEQUAL (#inferenceSchemas k1) (#inferenceSchemas k2) cmpI,
     transferSchemas = Seq.insertManyNoEQUAL (#transferSchemas k1) (#transferSchemas k2) cmpT,
     conSpecImports = List.mergeNoEQUAL cmpCS (#conSpecImports k1) (#conSpecImports k2)}

  val empty =
    {inferenceSchemas = Seq.empty,
     transferSchemas = Seq.empty,
     conSpecImports = []}

end;
