import "oruga.parser";
import "latex.latex";

signature DOCUMENT =
sig
  type documentContent

  val joinDocumentContents : documentContent list -> documentContent
  val read : string -> documentContent
  val knowledgeOf : documentContent -> Knowledge.base
  val typeSystemsDataOf : documentContent -> Type.typeSystemData list
  val conSpecsDataOf : documentContent -> CSpace.conSpecData list
  type constructionData = {name : string, conSpecN : string, construction : Construction.construction}
  val constructionsDataOf : documentContent -> constructionData FiniteSet.set
  val transferRequestsOf : documentContent ->  (string list) list
  val parseConstruction : CSpace.conSpecData -> string -> Construction.construction
  val findTypeSystemDataWithName : documentContent -> string -> Type.typeSystemData
  val findConSpecWithName : documentContent -> string -> CSpace.conSpecData
  val findConstructionWithName : documentContent -> string -> constructionData
  val findTransferSchemaWithName : documentContent -> string -> InterCSpace.tSchemaData

  val parseConstruction_rpc : (string -> CSpace.conSpecData option) -> Rpc.endpoint

end;

structure Document : DOCUMENT =
struct

  val ParseError = Parser.ParseError;
  type constructionData = {name : string,
                           conSpecN : string,
                           construction : Construction.construction}

  val importKW = "import"
  val typeSystemKW = "typeSystem"
  val conSpecKW = "conSpec"
  val iSchemaKW = "iSchema"
  val tSchemaKW = "tSchema"
  val constructionKW = "construction"
  val transferKW = "transfer"
  val commentKW = "comment"
  val bigKeywords = [importKW,typeSystemKW,conSpecKW,iSchemaKW,
                     tSchemaKW,constructionKW,transferKW,commentKW]

  val typesKW = "types"
  val subTypeKW = "order"
  val typeImportsKW = "imports"
  val typeKeywords = [typesKW,subTypeKW,typeImportsKW]

  val constructorsKW = "constructors"
  val conSpecImportsKW = "imports"
  val conSpecKeywords = [constructorsKW,conSpecImportsKW]

  val contextKW = "context"
  val antecedentKW = "antecedent"
  val consequentKW = "consequent"
  val strengthKW = "strength"
  val iSchemaKeywords = [contextKW,antecedentKW,consequentKW,strengthKW]

  val targetKW = "target"
  val sourceKW = "source"
  val antecedentKW = "antecedent"
  val consequentKW = "consequent"
  val strengthKW = "strength"
  val tSchemaKeywords = [targetKW,sourceKW,antecedentKW,consequentKW,strengthKW]

  val sourceConstructionKW = "sourceConstruction"
  val goalKW = "goal"
  val outputKW = "output"
  val limitKW = "limit"
  val iterativeKW = "iterative"
  val unistructuredKW = "unistructured"
  val matchTargetKW = "matchTarget"
  val sourceConSpecKW = "sourceConSpec"
  val targetConSpecKW = "targetConSpec"
  val interConSpecKW = "interConSpec"
  val transferKeywords = [sourceConstructionKW,goalKW,outputKW,limitKW,
                          iterativeKW,unistructuredKW,matchTargetKW,targetConSpecKW,
                          sourceConSpecKW,interConSpecKW]


  fun breakListOn s [] = ([],"",[])
    | breakListOn s (w::ws) =
        if w = s
        then ([],s,ws)
        else (case breakListOn s ws of (x,s',y) => (w::x,s',y))

  fun parseToken s = case String.breakOn ":" (String.stripSpaces s) of
                  (ts,_,tys) => CSpace.makeToken ts (Type.fromString tys)
  fun parseCTyp s = case Parser.list Type.fromString (String.stripSpaces s) of
                  (ty::tys) => (tys,ty)
                | _ => raise ParseError ("bad constructor sig: " ^ s)
  fun parseConstructor s = case String.breakOn ":" (String.stripSpaces s) of
                        (cs,_,ctys) => CSpace.makeConstructor (cs, parseCTyp ctys)
  fun parseConfigurator s = case String.breakOn ":" (String.stripSpaces s) of
                         (us,_,ccs) => CSpace.makeConfigurator (us, parseConstructor ccs)


   fun findConstructorInConSpec s cspec =
     valOf (CSpace.findConstructorWithName s cspec)
     handle Option => raise ParseError ("no constructor " ^ s ^ " in " ^ (#name cspec))

  fun parseTCPair s cspec =
    case String.breakOn "<-" (String.stripSpaces s) of
          (_,"",_) => raise ParseError (s ^ " is not a token-constructor pair")
       |  (ts,_,cfgs) => {token = parseToken ts, constructor = findConstructorInConSpec cfgs cspec}

  fun parseConstruction cspec s =
    let fun c s' =
         case String.breakOn "[" s' of
           (ts,"",_) => Construction.Source (parseToken ts)
         | (tcps,_,ss) =>
             let val tcp = parseTCPair tcps cspec
                 val tok = #token tcp
                 val (xs,ys) = Parser.breakOnClosingDelimiter (#"[",#"]") ss
                 val _ = if ys = [] then ()
                         else raise ParseError ("invalid input sequence to constructor: " ^ ss)
             in Construction.TCPair (tcp, Parser.splitLevelApply (c o String.removeParentheses) xs)
             end
    in Construction.fixReferences (c (String.stripSpaces s))
    end;

  val parseConstruction_rpc = fn findCSpec =>
                                 Rpc.provide ("oruga.document.parseConstruction",
                                              Rpc.Datatype.tuple2(String.string_rpc, String.string_rpc),
                                              Construction.construction_rpc)
                                             (fn (cspecName, s) => let val cspec = Option.valOf (findCSpec cspecName);
                                                                   in parseConstruction cspec s end)

  fun contentForKeywords _ [] = []
  | contentForKeywords ks (w::ws) =
    let fun getKeywordMatch (k::K) = if k = w then SOME k else getKeywordMatch K
          | getKeywordMatch [] = NONE
    in (case getKeywordMatch ks of
          SOME k => (case contentForKeywords ks ws of
                        (NONE,x) :: L => (SOME k,x) :: L
                      | L => (SOME k, []) :: L)
        | NONE => (case contentForKeywords ks ws of
                      (NONE,x) :: L => (NONE, w :: x) :: L
                    | L => (NONE,[w]) :: L))
    end

  type documentContent =
       {typeSystemsData : Type.typeSystemData list,
        conSpecsData : CSpace.conSpecData list,
        knowledge : Knowledge.base,
        constructionsData : constructionData list,
        transferRequests : (string list) list,
        strengths : string -> real option}

  val emptyDocContent =
      {typeSystemsData = [],
       conSpecsData = [],
       knowledge = Knowledge.empty,
       constructionsData = [],
       transferRequests = [],
       strengths = (fn _ => NONE)}

  val typeSystemsDataOf = #typeSystemsData
  val conSpecsDataOf = #conSpecsData
  val knowledgeOf = #knowledge
  val constructionsDataOf = #constructionsData
  val transferRequestsOf = #transferRequests
  val strengthsOf = #strengths

  fun findTypeSystemDataWithName DC n =
    valOf (List.find (fn x => #name x = n) (typeSystemsDataOf DC))
    handle Option => raise ParseError ("no type system with name " ^ n)

  fun findConSpecWithName DC n =
    valOf (List.find (fn x => #name x = n) (conSpecsDataOf DC))
    handle Option => raise ParseError ("no constructor specification with name " ^ n)

  fun findConstructionWithName DC n =
    valOf (FiniteSet.find (fn x => #name x = n) (constructionsDataOf DC))
    handle Option => raise ParseError ("no construction with name " ^ n)

  fun findTransferSchemaWithName DC n =
    valOf (Knowledge.findTransferSchemaWithName (knowledgeOf DC) n)
    handle Option => raise ParseError ("no tSchema with name " ^ n)

  fun inequality s =
    (case String.breakOn "<" s of
        (x,"<",y) => (x,y)
      | (x,">",y) => (y,x)
      | _ => raise ParseError s)

  (* The function below adds types and, if in notation _:t it
      adds everything with :t as suffix *)
  fun parseTyp s =
    case String.breakOn ":" s of
      ("_",":",superTyp) => (fn x => x = Type.fromString superTyp orelse String.isSuffix (":"^superTyp) (Type.nameOfType x),
                             {typ = Type.fromString superTyp, subTypeable = true})
    | _ => (fn x => x = Type.fromString s, {typ = Type.fromString s, subTypeable = false})

(*
  fun insertPrincipalTypes (pt::L) P =
      Type.insertPrincipalType pt (insertPrincipalTypes L P)
    | insertPrincipalTypes [] P = P*)

  fun joinTypeSystemsData name TSDs =
    let fun joinData [] = {typeSystem = {Ty = Set.empty, subType = fn (x,y) => Type.equal x y},
                           principalTypes = FiniteSet.empty}
          | joinData (tsd::L) =
              let val tsd_rec = joinData L
                  val TS_rec = #typeSystem tsd_rec
                  val TS = #typeSystem tsd
                  val jointTys = Set.union (#Ty TS) (#Ty TS_rec)
                  val jointPTys = foldl (uncurry Type.insertPrincipalType) (#principalTypes tsd_rec) (FiniteSet.listOf (#principalTypes tsd))
                  (*val jointPTys = insertPrincipalTypes (FiniteSet.listOf (#principalTypes tsd)) (#principalTypes tsd_rec)*)
                  val jointSubType = (fn (x,y) => #subType TS (x,y) orelse #subType TS_rec (x,y))
                  val jointTS = {Ty = jointTys, subType = jointSubType}
              in {typeSystem = jointTS, principalTypes = jointPTys}
              end
        val {typeSystem,principalTypes} = joinData TSDs
        val _ = print "\n";
        val strippedPrincipalTypes = map #typ principalTypes
        val _ = map (fn x => print ("  " ^ x)) strippedPrincipalTypes
        val _ = print "\n"
        val principalSubType = Type.closureOverFiniteSet strippedPrincipalTypes (#subType typeSystem)
        val subTypeableTypes = List.filterThenMap #subTypeable #typ principalTypes
        val subType = Type.fixForSubtypeable subTypeableTypes principalSubType
        val typeSystem = {Ty = #Ty typeSystem, subType = subType}
    in {name = name, typeSystem = typeSystem, principalTypes = principalTypes}
    end

  fun renameTypeInTypeSystemData (t1,t2) {name,typeSystem,principalTypes} =
    let val {Ty,subType} = typeSystem
        val _ = if Set.elementOf t2 Ty
                then raise ParseError ("cannot rename " ^ t1 ^ " to " ^ t2 ^ " in " ^ name ^ " as " ^ t2 ^ " already exists")
                else ()
        val _ = if Set.elementOf t1 Ty
                then ()
                else raise ParseError ("cannot rename " ^ t1 ^ " to " ^ t2 ^ " in " ^ name ^ " as " ^ t1 ^ " doesn't exist")
        val updatedTy = Set.union (Set.minus Ty (Set.singleton t1)) (Set.singleton t2)
        fun m x = if x = t2 then t1 else x
        fun updatedSubType (x,y) = if x = t1 orelse y = t1 then false else subType (m x, m y)
        val updatedTypeSystem = {Ty = updatedTy, subType = updatedSubType}
        val (pt,npt) = (case FiniteSet.find (fn x => #typ x = t1) principalTypes of
                      SOME {typ,subTypeable} => (FiniteSet.singleton {typ = t1, subTypeable = subTypeable},
                                                  FiniteSet.singleton {typ = t2, subTypeable = subTypeable})
                    | _ => (FiniteSet.empty,FiniteSet.empty))
        val updatedPrincipalTypes = FiniteSet.union (FiniteSet.minus principalTypes pt) npt
    in {name = name,typeSystem = updatedTypeSystem, principalTypes = updatedPrincipalTypes}
    end

  fun addTypeSystem (name, tss) dc =
  let val _ = print ("\nAdding type system " ^ name ^ "...");
      val _ = (findTypeSystemDataWithName dc name;Logging.write ("\nWARNING: type systems have same name. Overwriting!\n"))
                handle ParseError => ()
      val blocks = contentForKeywords typeKeywords tss
      fun getTyps [] = []
        | getTyps ((x,c)::L) =
            if x = SOME typesKW
            then map parseTyp (String.tokens (fn k => k = #",") (String.concat c))
            else getTyps L
      fun getOrder [] = []
        | getOrder ((x,c)::L) =
            if x = SOME subTypeKW
            then map inequality (String.tokens (fn k => k = #",") (String.concat c))
            else getOrder L
      fun parseImport s =
        (case String.breakOn " with " s of
            (tsName," with ",mapString) =>
              let fun getMap ss = (case String.breakOn " as " ss of
                                    (s1," as ",s2) => (String.stripSpaces s1,String.stripSpaces s2)
                                  | _ => raise ParseError ("no type mapping: expected syntax \"with t1 as t2\" in "^s))
                  val mapPairs = Parser.splitLevelWithSepFunApply getMap (fn x => x = #";") (String.explode mapString)
                  val TS = findTypeSystemDataWithName dc (String.stripSpaces tsName)
              in foldl (uncurry renameTypeInTypeSystemData) TS mapPairs
              end
          | (tsName,_,_) => findTypeSystemDataWithName dc (String.stripSpaces tsName))
      fun getImports [] = []
        | getImports ((x,c)::L) =
            if x = SOME typeImportsKW
            then map parseImport (String.tokens (fn k => k = #",") (Parser.deTokenise " " c))
            else getImports L

      fun processTys ((Ty,prtyp)::L) =
          (case processTys L of
            (Ty_rec,prTyps) => (fn x => Ty x orelse Ty_rec x,
                                Type.insertPrincipalType prtyp prTyps)
          )
        | processTys [] = (Set.empty, FiniteSet.empty)

      val (newTys,newPrincipalTyps) = processTys (getTyps blocks)
      val strippedPrincipalTypes = map #typ newPrincipalTyps

      val ordList = getOrder blocks
      fun eq (x,y) (x',y') = Type.equal x x' andalso Type.equal y y'
      fun subType_raw (x,y) = List.exists (eq (x,y)) ordList
      val typeSystemData_raw = {typeSystem = {Ty = newTys, subType = subType_raw},
                                principalTypes = newPrincipalTyps,
                                name = "__tmp"}

      val importsTSDs = getImports blocks
      val typeSystemData = joinTypeSystemsData name (importsTSDs @ [typeSystemData_raw])
      val _ = if Type.wellDefined typeSystemData
              then print ("...done\n")
              else print ("\n  WARNING: Type System " ^ name ^ " is not well defined (probably a cycle, unless the there's a bug in oruga!)\n")

  in {typeSystemsData = typeSystemData :: List.filter (fn x => #name x <> name) (#typeSystemsData dc),
      conSpecsData = #conSpecsData dc,
      knowledge = #knowledge dc,
      constructionsData = #constructionsData dc,
      transferRequests = #transferRequests dc,
      strengths = #strengths dc}
  end

  fun parseConstructor s =
    case String.breakOn ":" s of
      (cname,":",csig) =>
        (case String.breakOn "->" csig of
            (inTyps,"->",outTyp) => CSpace.makeConstructor (cname, CSpace.makeCTyp (Parser.list Type.fromString inTyps, Type.fromString outTyp))
          | _ => raise ParseError ("bad signature for constructor: " ^ s)
        )
    | _ => raise ParseError ("badly specified constructor: " ^ s)


  fun addConSpec (r, tss) dc =
  let val (name,x,typeSystemN) = String.breakOn ":" r
      (*val _ = if x = ":" then () else raise ParseError "no type system specified for conSpec"*)
      val _ = Logging.write ("\nAdding constructors for constructor specification " ^ name ^ " of type system " ^ typeSystemN ^ "...\n")

      val blocks = contentForKeywords conSpecKeywords tss
      fun getImports [] = []
        | getImports ((x,c)::L) =
            if x = SOME conSpecImportsKW
            then map (findConSpecWithName dc) (String.tokens (fn k => k = #",") (String.concat c))
            else getImports L
      fun getConstructors [] = []
        | getConstructors ((x,c)::L) =
            if x = SOME constructorsKW
            then map parseConstructor (Parser.splitLevelWithSepFunApply (fn x => x) (fn x => x = #",") (List.concat (map String.explode c)))
            else getConstructors L

      val newConstructors = FiniteSet.ofList (getConstructors blocks)
      val importBlocks = getImports blocks
      val importedConSpecNames = map #name importBlocks
      val importedConstructorSets = map #constructors importBlocks
      val allConstructors = foldl (uncurry FiniteSet.union) FiniteSet.empty (newConstructors :: importedConstructorSets)

      (*val chars = List.concat (map String.explode tss)
      val crs = map parseConstructor (Parser.splitLevelWithSepFunApply (fn x => x) (fn x => x = #",") chars)*)
      val _ = FiniteSet.map ((fn x => Logging.write ("  " ^ x ^ "\n")) o CSpace.stringOfConstructor) allConstructors
      val cspec = {name = name,
                   typeSystemData = findTypeSystemDataWithName dc typeSystemN,
                   constructors = allConstructors}
      val updatedConSpec =
        case CSpace.wellDefinedConSpec cspec of
          (true,true) => cspec
        | (true,false) => CSpace.fixClashesInConSpec cspec
        | (false,_) => (Logging.write "ERROR: some constructor is not well defined... cannot proceed\n";
                        raise CSpace.ImpossibleOverload)
      val updatedTSD = #typeSystemData updatedConSpec

      val _ = if List.exists (fn x => Knowledge.conSpecIsImportedBy (Knowledge.conSpecImportsOf (#knowledge dc)) name x) importedConSpecNames
              then raise ParseError ("conSpec " ^ name ^ " appears in a cycle of imports")
              else ()
      val _ = Logging.write "...done\n"

  in {typeSystemsData = updatedTSD :: List.filter (fn x => #name x <> #name updatedTSD) (#typeSystemsData dc),
      conSpecsData = updatedConSpec :: #conSpecsData dc,
      knowledge = Knowledge.addConSpecImports (#knowledge dc) (name,importedConSpecNames),
      constructionsData = #constructionsData dc,
      transferRequests = #transferRequests dc,
      strengths = #strengths dc}
  end

  fun addInferenceSchema (nn,cs) dc =
  let val (name,x,cspecNs) = String.breakOn ":" nn
      val _ = if x = ":" then () else raise ParseError ("construction " ^ nn ^ " needs source, target and inter cspecs")
      val (contextConSpecN,y,idConSpecN) = String.breakOn "," (String.removeParentheses cspecNs)
      val _ = if y = "," then () else raise ParseError ("construction " ^ nn ^ " needs source, target and inter cspecs")
      val contextConSpec = findConSpecWithName dc contextConSpecN
      val contextTySys = #typeSystem (#typeSystemData contextConSpec)
      val idConSpec = findConSpecWithName dc idConSpecN
      val idTySys = #typeSystem (#typeSystemData idConSpec)
      val _ = Logging.write ("\nAdding inference schema " ^ name ^ "...")
      fun getPattern k [] = (Logging.write ("  ERROR: " ^ k ^ " pattern not specified");
                              raise ParseError ("no " ^ k ^ " in iSchema " ^ String.concat cs))
        | getPattern k ((x,ps) :: L) =
            if x = SOME k
            then parseConstruction (if k = contextKW then contextConSpec else idConSpec) (String.concat ps)
            else getPattern k L
      fun getAntecedent [] = (Logging.write ("  ERROR: token relation not specified");
                              raise ParseError ("no token rels in iSchema " ^ String.concat cs))
        | getAntecedent ((x,trss) :: L) =
            if x = SOME antecedentKW
            then if trss = [] then [] else Parser.splitLevelApply (parseConstruction idConSpec) (List.maps explode trss)
            else getAntecedent L
      fun getConsequent [] = (Logging.write ("  ERROR: construct relation not specified");
                                raise ParseError ("no construct rel in iSchema " ^ String.concat cs))
        | getConsequent ((x,crs) :: L) =
            if x = SOME consequentKW
            then parseConstruction idConSpec (String.concat crs)
            else getConsequent L
      fun getStrength [] = (Logging.write ("  ERROR: strength not specified");
                            raise ParseError ("no strength in iSchema " ^ String.concat cs))
        | getStrength ((x,ss) :: L) =
            if x = SOME strengthKW
            then valOf (Real.fromString (String.concat ss)) handle Option => (Logging.write ("strength is not a real number in iSchema " ^ String.concat cs);raise Option)
            else getStrength L
      val blocks = contentForKeywords iSchemaKeywords cs
      val context = getPattern contextKW blocks
      val antecedent = getAntecedent blocks
      val consequent = getConsequent blocks
      val _ = if Construction.wellFormed idConSpec context
              then Logging.write "\n  context pattern is well formed"
              else Logging.write "\n  WARNING: context pattern is not well formed"
      val _ = if List.all (Construction.wellFormed idConSpec) antecedent
              then Logging.write "\n  antecedent patterns are well formed"
              else Logging.write "\n  WARNING: some antecedent pattern is not well formed"
      val _ = if Construction.wellFormed idConSpec consequent
              then Logging.write "\n  consequent pattern is well formed\n"
              else Logging.write "\n  WARNING: consequent pattern is not well formed\n"
      val isch = {context = context,
                  antecedent = antecedent,
                  consequent = consequent}
      val ischData = {name = name,
                      contextConSpecN = contextConSpecN,
                      idConSpecN = idConSpecN,
                      iSchema = isch}
      val strengthVal = getStrength blocks
      fun strengthsUpd c = if c = name then SOME strengthVal else (#strengths dc) c
      val _ = Logging.write ("done\n");
      fun ff (c,c') = Real.compare (valOf (strengthsUpd (#name c')), valOf (strengthsUpd (#name c)))
  in {typeSystemsData = #typeSystemsData dc,
      conSpecsData = #conSpecsData dc,
      knowledge = Knowledge.addInferenceSchema (#knowledge dc) ischData strengthVal ff,
      constructionsData = #constructionsData dc,
      transferRequests = #transferRequests dc,
      strengths = strengthsUpd}
  end

  fun addTransferSchema (nn,cs) dc =
  let val (name,x,cspecNs) = String.breakOn ":" nn
      val _ = if x = ":" then () else raise ParseError ("construction " ^ nn ^ " needs source, target and inter cspecs")
      val (sourceConSpecN,y,targetInterConSpecN) = String.breakOn "," (String.removeParentheses cspecNs)
      val _ = if y = "," then () else raise ParseError ("construction " ^ nn ^ " needs source, target and inter cspecs")
      val (targetConSpecN,y,interConSpecN) = String.breakOn "," (String.removeParentheses targetInterConSpecN)
      val _ = if y = "," then () else raise ParseError ("construction " ^ nn ^ " needs source, target and inter cspecs")
      val sourceConSpec = findConSpecWithName dc sourceConSpecN
      val sourceTySys = #typeSystem (#typeSystemData sourceConSpec)
      val targetConSpec = findConSpecWithName dc targetConSpecN
      val targetTySys = #typeSystem (#typeSystemData targetConSpec)
      val interConSpec = findConSpecWithName dc interConSpecN
      val interTySys = #typeSystem (#typeSystemData interConSpec)
      val _ = Logging.write ("\nAdding transfer schema " ^ name ^ "...")
      fun getPattern k [] = (Logging.write ("  ERROR: " ^ k ^ " pattern not specified");
                              raise ParseError ("no " ^ k ^ " in tSchema " ^ String.concat cs))
        | getPattern k ((x,ps) :: L) =
            if x = SOME k
            then parseConstruction (if k = sourceKW then sourceConSpec else targetConSpec) (String.concat ps)
            else getPattern k L
      fun getAntecedent [] = (Logging.write ("  ERROR: token relation not specified");
                              raise ParseError ("no token rels in tSchema " ^ String.concat cs))
        | getAntecedent ((x,trss) :: L) =
            if x = SOME antecedentKW
            then if trss = [] then [] else Parser.splitLevelApply (parseConstruction interConSpec) (List.maps explode trss)
            else getAntecedent L
      fun getConsequent [] = (Logging.write ("  ERROR: construct relation not specified");
                                raise ParseError ("no construct rel in tSchema " ^ String.concat cs))
        | getConsequent ((x,crs) :: L) =
            if x = SOME consequentKW
            then parseConstruction interConSpec (String.concat crs)
            else getConsequent L
      fun getStrength [] = (Logging.write ("  ERROR: strength not specified");
                            raise ParseError ("no strength in tSchema " ^ String.concat cs))
        | getStrength ((x,ss) :: L) =
            if x = SOME strengthKW
            then valOf (Real.fromString (String.concat ss))
                  handle Option => (Logging.write ("strength is not a real number in tSchema " ^ String.concat cs);
                                    raise Option)
            else getStrength L
      val blocks = contentForKeywords tSchemaKeywords cs
      val source = getPattern sourceKW blocks
      val target = getPattern targetKW blocks
      val antecedent = getAntecedent blocks
      val consequent = getConsequent blocks
      val _ = if Construction.wellFormed sourceConSpec source
              then Logging.write "\n  source pattern is well formed"
              else Logging.write "\n  WARNING: source pattern is not well formed"
      val _ = if Construction.wellFormed targetConSpec target
              then Logging.write "\n  target pattern is well formed"
              else Logging.write "\n  WARNING: target pattern is not well formed"
      val _ = if List.all (Construction.wellFormed interConSpec) antecedent
              then Logging.write "\n  antecedent patterns are well formed"
              else Logging.write "\n  WARNING: some antecedent pattern is not well formed"
      val _ = if Construction.wellFormed interConSpec consequent
              then Logging.write "\n  consequent pattern is well formed\n"
              else Logging.write "\n  WARNING: consequent pattern is not well formed\n"
      val tsch = {source = source,
                  target = target,
                  antecedent = antecedent,
                  consequent = consequent}
      val tschData = {name = name,
                      sourceConSpecN = sourceConSpecN,
                      targetConSpecN = targetConSpecN,
                      interConSpecN = interConSpecN,
                      tSchema = tsch}
      val strengthVal = getStrength blocks
      fun strengthsUpd c = if c = name then SOME strengthVal else (#strengths dc) c
      val _ = Logging.write ("done\n");
      fun ff (c,c') = Real.compare (valOf (strengthsUpd (InterCSpace.nameOf c')), valOf (strengthsUpd (InterCSpace.nameOf c)))
  in {typeSystemsData = #typeSystemsData dc,
      conSpecsData = #conSpecsData dc,
      knowledge = Knowledge.addTransferSchema (#knowledge dc) tschData strengthVal ff,
      constructionsData = #constructionsData dc,
      transferRequests = #transferRequests dc,
      strengths = strengthsUpd}
  end

  fun addConstruction (nn, cts) dc =
  let val (name,x,cspecN) = String.breakOn ":" nn
      val _ = if x = ":" then () else raise ParseError ("construction " ^ nn ^ " needs a cspec")
      val cspec = findConSpecWithName dc cspecN
      val ct = parseConstruction cspec cts

      val _ = print ("\nChecking well-formedness of construction " ^ name ^ "...");
      val startTime = Time.now();
      val _ = if Construction.wellFormed cspec ct then Logging.write ("\n  "^ name ^ " is well formed\n")
                else print ("\n  WARNING: "^ name ^" is not well formed\n")
      val endTime = Time.now();
      val runtime = Time.toMilliseconds endTime - Time.toMilliseconds startTime;
      val _ = print ("  well-formedness check runtime: "^ LargeInt.toString runtime ^ " ms \n...done\n  ");

      val ctRecord = {name = name, conSpecN = cspecN, construction = ct}
  in {typeSystemsData = #typeSystemsData dc,
      conSpecsData = #conSpecsData dc,
      knowledge = #knowledge dc,
      constructionsData = ctRecord :: (#constructionsData dc),
      transferRequests = #transferRequests dc,
      strengths = #strengths dc}
  end

  fun addTransferRequests ws dc =
     {typeSystemsData = #typeSystemsData dc,
      conSpecsData = #conSpecsData dc,
      knowledge = #knowledge dc,
      constructionsData = #constructionsData dc,
      transferRequests = #transferRequests dc @ [ws],
      strengths = #strengths dc}


  exception BadGoal
  fun parseTransferRequests DC ws =
  let fun stringifyC ((x,c)::L) = "("^(valOf x)^","^ (String.stringOfList (fn x => x) c)^") : "^(stringifyC L)
        | stringifyC [] = ""
      val C = contentForKeywords transferKeywords ws

      fun getConstruction [] = raise ParseError "no construction to transfer"
        | getConstruction ((x,c)::L) =
            if x = SOME sourceConstructionKW
            then findConstructionWithName DC (String.concat c)
            else getConstruction L
      val constructionRecord = getConstruction C
      val construction = #construction constructionRecord
      val sourceConSpecN = #conSpecN constructionRecord
      val sourceConSpecData = findConSpecWithName DC sourceConSpecN
      val sourceTypeSystem = #typeSystem (#typeSystemData sourceConSpecData)

      fun getTargetConSpec [] = sourceConSpecData
        | getTargetConSpec ((x,c)::L) =
            if x = SOME targetConSpecKW
            then findConSpecWithName DC (String.concat c)
            else getTargetConSpec L
      fun getInterConSpec [] = raise ParseError "no inter-space specified"
        | getInterConSpec ((x,c)::L) =
            if x = SOME interConSpecKW
            then findConSpecWithName DC (String.concat c)
            else getInterConSpec L
            (*)
      fun getTargetTySys [] = sourceTypeSystem
        | getTargetTySys ((x,c)::L) =
            if x = SOME targetTypeSystemKW
            then #typeSystem (findTypeSystemDataWithName DC (String.concat c))
            else getTargetTySys L
      val targetTypeSystem = getTargetTySys C*)
      val targetConSpecData = getTargetConSpec C
      val targetTypeSystem = #typeSystem (#typeSystemData targetConSpecData)
      val interConSpecData = getInterConSpec C
      val interTypeSystem = #typeSystem (#typeSystemData interConSpecData)

      fun getGoal [] = raise ParseError "no goal for transfer"
        | getGoal ((x,c)::L) =
            if x = SOME goalKW
            then parseConstruction interConSpecData (String.concat c)
            else getGoal L
      fun getOutput [] = raise ParseError "no output file name for transfer"
        | getOutput ((x,c)::L) =
            if x = SOME outputKW
            then "output/latex/"^(String.concat c)^".tex"
            else getOutput L
      fun getLimit [] = raise ParseError "no limit for transfer output file"
        | getLimit ((x,c)::L) =
            if x = SOME limitKW
            then valOf (Int.fromString (String.concat c)) handle Option => raise ParseError "limit needs an integer!"
            else getLimit L
      fun getMatchTarget [] = NONE
        | getMatchTarget ((x,c)::L) =
            if x = SOME matchTargetKW
            then (let val mtct = parseConstruction targetConSpecData (String.concat c)
                      val _ = if Construction.wellFormed targetConSpecData mtct
                              then Logging.write "\n  pattern for matching is well formed"
                              else Logging.write "\n  WARNING: pattern for matching is not well formed"
                  in SOME mtct
                  end)
            else getMatchTarget L
      fun getIterative [] = false
        | getIterative ((x,_)::L) =
            if x = SOME iterativeKW
            then (case getMatchTarget C of
                      NONE => true
                    | _ => raise ParseError "iterative and matchTarget are incompatible")
            else getIterative L
      fun getUnistructured [] = false
        | getUnistructured ((x,_)::L) =
            if x = SOME unistructuredKW
            then true
            else getUnistructured L
      val goal = getGoal C
      val outputFilePath = getOutput C
      val limit = getLimit C
      val iterative = getIterative C
      val KB = knowledgeOf DC
      val unistructured = getUnistructured C
      val targetPattern = getMatchTarget C
      fun mkLatexGoals res =
        let val goal = State.originalGoalOf res
            val goals = State.goalsOf res
            val goalsS = if List.null goals
                         then "NO\\ OPEN\\ GOALS!"
                         else String.concatWith "\n " (map (Latex.construction (0.0,0.0)) goals)
            val originalGoalS = Latex.construction (0.0,0.0) goal ^ "\\\\ \n"
            val IS = Heuristic.scoreMain (strengthsOf DC) res
            val alignedGoals = "\n " ^ ("\\textbf{Original\\ goal}\\\\\n"
                                                                      ^ originalGoalS
                                                                      ^ "\\\\ \\textbf{Open\\ goals}\\\\\n"
                                                                      ^ goalsS ^ "\\\\"
                                                                      ^ "\\\\ \\textbf{transfer\\ score}\\\\\n"
                                                                      ^ Real.toString IS)
        in alignedGoals
        end
      fun mkLatexProof tproof =
        let val ct = TransferProof.toConstruction tproof;
        in Latex.construction (0.0,0.0) ct
        end
      fun mkLatexConstructions comps =
        List.maps (fn x => map (Latex.construction (0.0,0.0)) (Composition.resultingConstructions x)) comps
      fun mkLatexConstructionsAndGoals res =
        let val comps = State.patternCompsOf res
            val tproof = State.transferProofOf res
            val goal = State.originalGoalOf res
            val goals = State.goalsOf res
            val latexConstructions = mkLatexConstructions comps
            val _ = if List.all (Composition.wellFormedComposition targetConSpecData) comps
                    then ()
                    else print ("\nWARNING! some composition at the target is not well formed!")
            val latexLeft = Latex.environment "minipage" "[t]{0.68\\linewidth}" (Latex.printWithHSpace 0.2 latexConstructions)
            val latexGoals = mkLatexGoals res
            val latexRight = Latex.environment "minipage" "[t]{0.3\\linewidth}" latexGoals
            val latexProof = ""(*mkLatexProof tproof*)
            (*val CSize = List.sumMapInt Composition.size comps*)
        in Latex.environment "center" "" (Latex.printWithHSpace 0.0 ([latexLeft,latexRight,(*Int.toString CSize,*)latexProof]))
        end
      val _ = print ("\nApplying structure transfer to "^ #name constructionRecord ^ "...");
      val startTime = Time.now();
      val targetTokens = FiniteSet.filter
                             (fn x => Set.elementOf (CSpace.typeOfToken x) (#Ty targetTypeSystem))
                             (Construction.leavesOfConstruction goal)
                          handle Empty => (Logging.write "WARNING : goal has no tokens in target construction space\n"; raise BadGoal)
      val state = Transfer.initState sourceConSpecData targetConSpecData interConSpecData KB construction goal
      val results = Transfer.masterTransfer iterative unistructured targetPattern state;
      val nres = length (Seq.list_of results);
      val (listOfResults,_) = Seq.chop limit results;
      val endTime = Time.now();
      val runtime = Time.toMilliseconds endTime - Time.toMilliseconds startTime;
      val _ = print ("\n" ^ "  runtime: "^ LargeInt.toString runtime ^ " ms \n");
      val _ = print ("  number of results: " ^ Int.toString nres ^ "\n");
      (*fun readTSchemaStrengths c = (strengthsOf DC) (CSpace.nameOfConstructor c)*)
      val score = Heuristic.scoreMain (strengthsOf DC) (hd listOfResults) handle Empty => (0.0)
      (*val tproofConstruction = map (TransferProof.toConstruction o State.transferProofOf) listOfResults
      val _ = print (Construction.toString  (hd tproofConstruction))*)
      val _ = print ("  transfer score: " ^ Real.toString score)
        val _ = print ("\n...done\n")
      val _ = print "\nComposing patterns and creating tikz figures...";
      val latexCompsAndGoals = Latex.printSubSections 1 (map mkLatexConstructionsAndGoals listOfResults);
      val latexCT = Latex.construction (0.0,0.0) construction;
      val _ = print "done\n";
      val _ = print "\nGenerating LaTeX document...";
      val latexOriginalConsAndGoals = Latex.environment "center" "" latexCT;
      val outputFile = TextIO.openOut outputFilePath
      val opening = (Latex.sectionTitle false "Original construction") ^ "\n"
      val resultText = (Latex.sectionTitle false "Structure transfer results") ^ "\n"
      val _ = Latex.outputDocument outputFile (opening ^ latexOriginalConsAndGoals ^ "\n\n " ^ resultText ^ latexCompsAndGoals);
      val _ = TextIO.closeOut outputFile;
      val _ = print ("done!\n" ^ "  output file: "^outputFilePath^"\n\n");
  in ()
  end

  fun joinDocumentContents ({typeSystemsData = ts,
                             conSpecsData = sp,
                             knowledge = kb,
                             constructionsData = cs,
                             transferRequests = tr,
                             strengths = st} :: L) =
    (case joinDocumentContents L of
      {typeSystemsData = ts',
       conSpecsData = sp',
       knowledge = kb',
       constructionsData = cs',
       transferRequests = tr',
       strengths = st'} =>
          {typeSystemsData = ts @ ts',
           conSpecsData = sp @ sp',
           knowledge = Knowledge.join kb kb',
           constructionsData = cs @ cs',
           transferRequests = tr @ tr',
           strengths = (fn c => case st c of SOME f => SOME f | NONE => st' c)})
  | joinDocumentContents [] = emptyDocContent

  fun read filename =
  let val file = TextIO.openIn ("input/"^filename)
      val s = TextIO.inputAll file
      val _ = TextIO.closeIn file
      val words = String.tokens (fn x => x = #"\n" orelse x = #" ") s
      val blocks = contentForKeywords bigKeywords words

      val importFilenames = List.filter (fn (x,_) => x = SOME importKW) blocks
      val importedContents = map (read o String.concat o #2) importFilenames
      val importedContent = joinDocumentContents importedContents

      fun distribute [] = importedContent
        | distribute ((x,c)::L) =
          let val dc = distribute L
              val (n,eq,ws) = breakListOn "=" c
              (*val _ = if eq = "=" then () else raise ParseError (String.concat n)*)
          in if x = SOME typeSystemKW then addTypeSystem (hd n,ws) dc else
             if x = SOME conSpecKW then addConSpec (hd n, ws) dc else
             if x = SOME iSchemaKW then addInferenceSchema (hd n,ws) dc else
             if x = SOME tSchemaKW then addTransferSchema (hd n,ws) dc else
             if x = SOME constructionKW then addConstruction (hd n,String.concat ws) dc else
             if x = SOME transferKW then addTransferRequests c dc else
             if x = SOME commentKW then dc else raise ParseError "error: this shouldn't have happened"
          end handle Bind => raise ParseError "expected name = content, found multiple words before ="

      val nonImported = List.filter (fn (x,_) => x <> SOME importKW) blocks
      val allContent = distribute (rev nonImported)
      val _ = map (parseTransferRequests allContent) (#transferRequests allContent)
  in allContent
  end

end
