import "oruga.parser";
import "latex.latex";
import "transfer.state";

signature DOCUMENT =
sig
  type documentContent

  val joinDocumentContents : documentContent list -> documentContent
  val read : string -> documentContent
  val knowledgeOf : documentContent -> Knowledge.base
  val typeSystemsDataOf : documentContent -> Type.typeSystemData list
  val conSpecsDataOf : documentContent -> CSpace.conSpecData list
  type graphData = {name : string, conSpecN : string, graph : Graph.graph, usedTokens : CSpace.token list}
  val graphsDataOf : documentContent -> graphData FiniteSet.set
  val transferRequestsOf : documentContent ->  (string list) list
  val tokenise : string -> string list
  val deTokenise : string list -> string
  val normaliseString : string -> string

  val findTypeSystemDataWithName : documentContent -> string -> Type.typeSystemData option
  val findConSpecWithName : documentContent -> string -> CSpace.conSpecData option
  val findGraphWithName : documentContent -> string -> graphData option
  val findSchemaWithName : documentContent -> string -> State.schemaData option

  val getTypeSystemDataWithName : documentContent -> string -> Type.typeSystemData
  val getConSpecWithName : documentContent -> string -> CSpace.conSpecData
  val getGraphWithName : documentContent -> string -> graphData
  val getTransferSchemaWithName : documentContent -> string -> State.schemaData

end;

structure Document : DOCUMENT =
struct

  val ParseError = Parser.ParseError;
  type graphData = {name : string, 
                    conSpecN : string, 
                    graph : Graph.graph, 
                    usedTokens : CSpace.token list}

  val importKW = "import"
  val typeSystemKW = "typeSystem"
  val conSpecKW = "conSpec"
  val iSchemaKW = "iSchema"
  val tSchemaKW = "tSchema"
  val graphKW = "graph"
  val transferKW = "transfer"
  val commentKW = "comment"
  val bigKeywords = [importKW,typeSystemKW,conSpecKW,iSchemaKW,
                     tSchemaKW,graphKW,transferKW,
                     commentKW]

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

  val sourceGraphKW = "sourceGraph"
  val goalKW = "goal"
  val outputKW = "output"
  val outputLimitKW = "outputLimit"
  val goalLimitKW = "goalLimit"
  val compositionLimitKW = "compositionLimit"
  val searchLimitKW = "searchLimit"
  val eagerKW = "eager"
  val iterativeKW = "iterative"
  val unistructuredKW = "unistructured"
  val inverseKW = "inverse"
  val matchTargetKW = "matchTarget"
  val sourceConSpecKW = "sourceConSpec"
  val targetConSpecKW = "targetConSpec"
  val interConSpecKW = "interConSpec"
  val saveKW = "save"
  val transferKeywords = [sourceGraphKW,goalKW,outputKW,outputLimitKW,searchLimitKW,goalLimitKW,compositionLimitKW,eagerKW,
                          iterativeKW,unistructuredKW,matchTargetKW,targetConSpecKW,
                          sourceConSpecKW,interConSpecKW,saveKW,inverseKW]


  fun breakListOn s [] = ([],"",[])
    | breakListOn s (w::ws) =
        if w = s
        then ([],s,ws)
        else (case breakListOn s ws of (x,s',y) => (w::x,s',y))

  fun ignoreUntil _ [] = []
    | ignoreUntil f (h::L) = if f h then L else ignoreUntil f L

  val standAloneChars = [#"(",#")",#"[",#"]",#"{",#"}",#"\"",#",",#";",#"="]

  fun tokenise s =
    let fun commentChar x = (x = #"#")
        fun lineBreak x = (x = #"\n")
        fun separator x = (x = #"\n" orelse x = #" " orelse x = #"\t")
        fun standAlone x = List.exists (fn y => y = x) standAloneChars
        fun t [] = (true,[])
          | t (x::xs) =
            if commentChar x then (true, #2(t (ignoreUntil lineBreak xs)))
            else if separator x then (true, #2(t xs))
            else if List.exists (fn y => y = x) standAloneChars then (true, str x :: #2(t xs))
            else (case t xs of
                    (true,L) => (false, str x :: L)
                  | (false,r::rs) => (false, str x ^ r :: rs)
                  | _ => raise ParseError "Completely unexpected error. Inform a developer!")
        val (_,ts) = t (String.explode s)
    in ts end;

  fun deTokenise [] = ""
    | deTokenise [s] = s
    | deTokenise (s1::s2::L) =
    if List.exists (fn y => str y = s1 orelse str y = s2) standAloneChars
    then s1 ^ deTokenise (s2::L)
    else s1 ^ " " ^ deTokenise (s2::L)

  fun normaliseString s =
    if List.all (fn x => x = #" ") (String.explode s) then " "
    else (deTokenise o tokenise) s

  fun parseTyp s =
      (case String.breakOn ":" s of
          (s1,":",s2) => Type.fromString (normaliseString s1 ^ ":" ^ normaliseString s2)
        | _ => Type.fromString (normaliseString s))

  fun parseToken s =
      (case String.breakOn ":" s of
          (ts,":",tys) => CSpace.makeToken (normaliseString ts) (parseTyp tys)
        | _ => raise ParseError ("no type for token: " ^ s))

  fun parseCTyp s = case Parser.list parseTyp s of
                      (ty::tys) => (tys,ty)
                    | _ => raise ParseError ("bad constructor sig: " ^ s)

   fun findConstructorInConSpec s cspec =
     valOf (CSpace.findConstructorWithName s cspec)
     handle Option => raise ParseError ("no constructor " ^ s ^ " in " ^ (#name cspec))

  fun parseTCPair s cspec =
    case String.breakOn "<-"  s of
          (_,"",_) => raise ParseError (s ^ " is not a token-constructor pair")
       |  (ts,_,cfgs) => {token = parseToken ts, constructor = findConstructorInConSpec (normaliseString cfgs) cspec}

  fun removeOuterBrackets wL =
    let fun removeOuterJunk (L,L') =
            (case (L,L') of
                ("("::xL,")"::xL') => removeOuterJunk (xL,xL')
              | ("{"::xL,"}"::xL') => removeOuterJunk (xL,xL')
              | ("["::xL,"]"::xL') => removeOuterJunk (xL,xL')
              | _ => (L,L'))
        val (wL1,wL2) = List.split (wL, (List.length wL) div 2)
        val (wL1',wL2') = removeOuterJunk (wL1, rev wL2)
    in wL1' @ rev wL2'
    end

  fun gatherMaterialByKeywords ks wL =
      let fun cfw (bL,q) [] = ((bL,q),[])
            | cfw (bL,q) (w::ws) =
              let val newbL =
                    if q then bL
                    else (case (bL,w) of
                              ("("::bL',")") => bL'
                            | ("["::bL',"]") => bL'
                            | ("{"::bL',"}") => bL'
                            | (_,"(")        => w::bL
                            | (_,"[")        => w::bL
                            | (_,"{")        => w::bL
                            | (_,")")        => raise ParseError ("no matching bracket for ) near " ^ (hd ws))
                            | (_,"]")        => raise ParseError ("no matching bracket for ] near " ^ (hd ws))
                            | (_,"}")        => raise ParseError ("no matching bracket for } near " ^ (hd ws))
                            | (_,_)          => bL)
                  val newq = (q andalso not (w = "\"")) orelse (not q andalso w = "\"")
                  val (X,cfwr) = cfw (newbL,newq) ws
                  val C = if (newbL,newq) = ([],false) andalso List.exists (fn x => x = w) ks
                          then (case cfwr of
                                  (NONE,x) :: L => (SOME w,x) :: L
                                | L             => (SOME w, []) :: L)
                          else (case cfwr of
                                  (NONE,x) :: L => (NONE, w :: x) :: L
                                | L             => (NONE,[w]) :: L)
              in (X,C)
              end
          val ((bL,q),result) = cfw ([],false) (removeOuterBrackets wL)
          val _ = if bL = [] then ()
                  else raise ParseError ("no closing bracket for " ^ hd bL)
          val _ = if not q then ()
                  else raise ParseError ("uneven quotation marks")
      in result
      end

  type documentContent =
       {typeSystemsData : Type.typeSystemData list,
        conSpecsData : CSpace.conSpecData list,
        knowledge : Knowledge.base,
        graphsData : graphData list,
        transferRequests : (string list) list}

  val emptyDocContent =
      {typeSystemsData = [],
       conSpecsData = [],
       knowledge = Knowledge.empty,
       graphsData = [],
       transferRequests = []}

  val typeSystemsDataOf = #typeSystemsData
  val conSpecsDataOf = #conSpecsData
  val knowledgeOf = #knowledge
  val graphsDataOf = #graphsData
  val transferRequestsOf = #transferRequests

  fun findTypeSystemDataWithName DC n =
    List.find (fn x => #name x = n) (typeSystemsDataOf DC)

  fun findConSpecWithName DC n =
    List.find (fn x => #name x = n) (conSpecsDataOf DC)

  fun findGraphWithName DC n =
    FiniteSet.find (fn x => #name x = n) (graphsDataOf DC)

  fun findSchemaWithName DC n =
    Knowledge.findSchemaWithName (knowledgeOf DC) n

  fun getTypeSystemDataWithName DC n =
    valOf (findTypeSystemDataWithName DC n)
    handle Option => raise ParseError ("no type system with name " ^ n)

  fun getConSpecWithName DC n =
    valOf (findConSpecWithName DC n)
    handle Option => raise ParseError ("no constructor specification with name " ^ n)

  fun getGraphWithName DC n =
    valOf (findGraphWithName DC n)
    handle Option => raise ParseError ("no graph with name " ^ n)

  fun getTransferSchemaWithName DC n =
    valOf (findSchemaWithName DC n)
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


  structure TSet = Type.TypeSet;
  structure TDict = Type.TypeDictionary;
  fun addTypeSystem (N, tss) dc =
  let val name = case N of [x] => x | _ => raise ParseError ("invalid name for type system : " ^ String.concat N)
      val _ = print ("\nAdding type system " ^ name ^ "...");
      val _ = case findTypeSystemDataWithName dc name of NONE => () | SOME _ => raise ParseError ("\nWARNING: type systems have same name!\n")
      val blocks = gatherMaterialByKeywords typeKeywords tss

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
            val principalSubType = Type.transitiveClosure strippedPrincipalTypes (#subType typeSystem)(*)
            val subTypeableTypes = List.filterThenMap #subTypeable #typ principalTypes
            val subType = Type.fixForSubtypeable subTypeableTypes principalSubType*)
            val typeSystem = {Ty = #Ty typeSystem, subType = principalSubType}
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

      fun getTyps [] = []
        | getTyps ((x,c)::L) =
            if x = SOME typesKW
            then map parseTyp (String.tokens (fn k => k = #",") (String.concat (removeOuterBrackets c)))
            else getTyps L
      fun getOrder [] = []
        | getOrder ((x,c)::L) =
            if x = SOME subTypeKW
            then map inequality (String.tokens (fn k => k = #",") (String.concat (removeOuterBrackets c)))
            else getOrder L
      fun parseImport s =
        (case String.breakOn " with " s of
            (tsName," with ",mapString) =>
              let fun getMap ss = (case String.breakOn " as " ss of
                                    (s1," as ",s2) => (String.stripSpaces s1,String.stripSpaces s2)
                                  | _ => raise ParseError ("no type mapping: expected syntax \"with t1 as t2\" in "^s))
                  val mapPairs = Parser.splitLevelWithSepFunApply getMap (fn x => x = #";") (String.explode mapString)
                  val TS = getTypeSystemDataWithName dc (String.stripSpaces tsName)
              in foldl (uncurry renameTypeInTypeSystemData) TS mapPairs
              end
          | (tsName,_,_) => getTypeSystemDataWithName dc (String.stripSpaces tsName))
      fun getImports [] = []
        | getImports ((x,c)::L) =
            if x = SOME typeImportsKW
            then map parseImport (String.tokens (fn k => k = #",") (Parser.deTokenise " " (removeOuterBrackets c)))
            else getImports L

      fun processTys ((Ty,prtyp)::L) =
          (case processTys L of
            (Ty_rec,prTyps) => (fn x => Ty x orelse Ty_rec x,
                                Type.insertPrincipalType prtyp prTyps)
          )
        | processTys [] = (Set.empty, FiniteSet.empty)


      val (newTys,newPrincipalTyps) = processTys (getTyps blocks)
      val strippedPrincipalTypes = map #typ newPrincipalTyps

      fun typeStoreFromPairList TySt [] = TySt
        | typeStoreFromPairList TySt ((x,y)::L) =
        let fun updateX {subTypes,superTypes} = {subTypes = subTypes, superTypes = TSet.fromList (y::TSet.toList superTypes)}
            fun updateY {subTypes,superTypes} = {subTypes = TSet.fromList (x::TSet.toList superTypes), superTypes = superTypes}
            val empty = TSet.empty ()
            val TyStX = if TDict.has TySt x
                        then TDict.update TySt x updateX
                        else TDict.fromPairList ((x,{subTypes = empty,superTypes = TSet.fromList [y]})::TDict.toPairList TySt)
            val TyStXY = if TDict.has TyStX y
                         then TDict.update TyStX y updateY
                         else TDict.fromPairList ((y,{subTypes = TSet.fromList [x],superTypes = empty})::TDict.toPairList TyStX)
        in typeStoreFromPairList TyStXY L
        end
      val ordList = getOrder blocks
      val ordStore = typeStoreFromPairList (TDict.empty ()) ordList

    fun superTypeStoreFromTSD TSD =
      let val {typeSystem,principalTypes,...} = TSD
          val TP = {typeSystem = typeSystem, principalTypes = principalTypes}
          fun makeTypeStore TySt [] = TySt
            | makeTypeStore TySt (pty::L) =
            let val superTypesOfPT = FiniteSet.listOf (Type.superTypes TP pty)
                val TySt_upd = TDict.fromPairList ((pty, TSet.fromList superTypesOfPT) :: TDict.toPairList TySt)
            in makeTypeStore TySt_upd L
            end
          val pTys = map #typ (FiniteSet.listOf principalTypes)
      in makeTypeStore (TDict.empty ()) pTys
      end

      fun subType_raw (x,y) = case TDict.get ordStore x of NONE => false | SOME {superTypes,...} => TSet.contains superTypes y

      val typeSystemData_raw = {typeSystem = {Ty = newTys, subType = subType_raw},
                                principalTypes = newPrincipalTyps,
                                name = "__tmp"}

      val importsTSDs = getImports blocks
      val typeSystemData' = joinTypeSystemsData name (importsTSDs @ [typeSystemData_raw])
      val ordStore = superTypeStoreFromTSD typeSystemData'

      fun tyDataToString superTypes = TSet.toString superTypes
      val _ = if name = "nat10T" then print ("\n type system "^name ^ ": " ^ TDict.toString tyDataToString ordStore ^ "\n") else ()

      val principalTypes = #principalTypes typeSystemData'
      val slowSubType = #subType (#typeSystem typeSystemData')
      val fastSubType = Type.reflexiveClosure
                            (Type.fixForSubtypeable (List.filterThenMap #subTypeable #typ principalTypes)
                                                    (fn (x,y) => (case TDict.get ordStore x of
                                                                    NONE => false
                                                                  | SOME superTypes => TSet.contains superTypes y)))
      val typeSystemData = {typeSystem = {Ty = #Ty (#typeSystem typeSystemData'), subType = fastSubType},
                            principalTypes = principalTypes,
                            name = name}
      val _ = if Type.wellDefined typeSystemData
              then print ("...done\n")
              else print ("\n  WARNING: Type System " ^ name ^ " is not well defined (probably a cycle, unless the there's a bug in oruga!)\n")

  in {typeSystemsData = typeSystemData :: #typeSystemsData dc,
      conSpecsData = #conSpecsData dc,
      knowledge = #knowledge dc,
      graphsData = #graphsData dc,
      transferRequests = #transferRequests dc}
  end

  fun parseConstructor s =
    (case String.breakOn ":" s of
          (cname,":",csig) =>
            (case String.breakOn "->" csig of
                (inTyps,"->",outTyp) => CSpace.makeConstructor (cname, CSpace.makeCTyp (Parser.list Type.fromString inTyps, Type.fromString outTyp))
              | _ => raise ParseError ("bad signature for constructor: " ^ s)
            )
        | _ => raise ParseError ("badly specified constructor: " ^ s))



  fun addConSpec (R, tss) dc =
  let val r = case R of [x] => x | _ => raise ParseError ("invalid name or type system for constructor specification : " ^ String.concat R)
      val (name,x,typeSystemN) = String.breakOn ":" r
      val _ = case findConSpecWithName dc name of NONE => () | SOME _ => raise ParseError ("duplicated constructor specification: " ^ name)
      (*val _ = if x = ":" then () else raise ParseError "no type system specified for conSpec"*)
      val _ = Logging.write ("\nAdding constructors for constructor specification " ^ name ^ " of type system " ^ typeSystemN ^ "...\n")

      val blocks = gatherMaterialByKeywords conSpecKeywords tss
      fun getImports [] = []
        | getImports ((x,c)::L) =
            if x = SOME conSpecImportsKW
            then map (getConSpecWithName dc) (String.tokens (fn k => k = #",") (String.concat (removeOuterBrackets c)))
            else getImports L
      fun getConstructors [] = []
        | getConstructors ((x,c)::L) =
            if x = SOME constructorsKW
            then let val cChars = String.explode (String.concat (removeOuterBrackets c))
                     val cL = Parser.splitLevelWithSepFunApply (fn x => x) (fn x => x = #",") cChars
                 in map parseConstructor cL
                 end
            else getConstructors L

      fun processConstructorData [] = ([], fn _ => "")
        | processConstructorData ((c,r)::cL) =
        let val (cs,f) = processConstructorData cL
            fun updf x = if CSpace.sameConstructors x c then r else f x
        in (c::cs,updf)
        end

      val newConstructors = FiniteSet.ofList (getConstructors blocks)
      val importBlocks = getImports blocks
      val importedConSpecNames = map #name importBlocks
      val importedConstructorSets = map #constructors importBlocks
      val allConstructors = foldl (uncurry FiniteSet.union) FiniteSet.empty (newConstructors :: importedConstructorSets)

      val _ = FiniteSet.map ((fn x => Logging.write ("  " ^ x ^ "\n")) o CSpace.stringOfConstructor) allConstructors
      val cspec = {name = name,
                   typeSystemData = getTypeSystemDataWithName dc typeSystemN,
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

  in {typeSystemsData = List.mergeNoEQUAL (fn (x,y) => String.compare (#name x, #name y)) [updatedTSD] (List.filter (fn x => #name x <> #name updatedTSD) (#typeSystemsData dc)),
      conSpecsData = List.mergeNoEQUAL (fn (x,y) => String.compare (#name x, #name y)) [updatedConSpec] (#conSpecsData dc),
      knowledge = Knowledge.addConSpecImports (#knowledge dc) (name,importedConSpecNames),
      graphsData = #graphsData dc,
      transferRequests = #transferRequests dc}
  end

  fun addInferenceSchema (N,cs) dc =
  let val nn = String.concat N
      val (name,x,cspecNs) = String.breakOn ":" nn
      val _ = if x = ":" then () else raise ParseError ("schema " ^ nn ^ " needs source, target and inter cspecs")
      val (contextConSpecN,y,idConSpecN) = String.breakOn "," (String.removeParentheses cspecNs)
      val _ = if y = "," then () else raise ParseError ("schema " ^ nn ^ " needs source, target and inter cspecs")
      val _ = case findSchemaWithName dc name of
                SOME knownSchema => if (#name knownSchema) = name andalso (List.last (#conSpecNames knownSchema)) = idConSpecN
                                    then raise ParseError ("duplciated name for tSchema " ^ name ^ " in space " ^ idConSpecN)
                                    else ()
              | NONE => ()
      val contextConSpec = getConSpecWithName dc contextConSpecN
      val contextTySys = #typeSystem (#typeSystemData contextConSpec)
      val idConSpec = getConSpecWithName dc idConSpecN
      val idTySys = #typeSystem (#typeSystemData idConSpec)
      val _ = Logging.write ("\nAdding inference schema " ^ name ^ "...")
      fun getPatternGraph k _ [] = (Logging.write ("  ERROR: " ^ k ^ " pattern not specified");
                              raise ParseError ("no " ^ k ^ " in tSchema " ^ String.concat cs))
        | getPatternGraph k tks ((x,ps) :: L) =
            if x = SOME k
            then Parser.parseGraph tks (String.concat ps)
            else getPatternGraph k tks L
      fun getStrength [] = (Logging.write ("  ERROR: strength not specified");
                            raise ParseError ("no strength in iSchema " ^ String.concat cs))
        | getStrength ((x,ss) :: L) =
            if x = SOME strengthKW
            then valOf (Real.fromString (String.concat ss)) handle Option => (Logging.write ("strength is not a real number in iSchema " ^ String.concat cs);raise Option)
            else getStrength L
      val blocks = gatherMaterialByKeywords iSchemaKeywords cs
      val (usedTokens1, context) = getPatternGraph contextKW [] blocks
      val (usedTokens2, antecedent) = getPatternGraph antecedentKW usedTokens1 blocks
      val (_,consequent) = getPatternGraph consequentKW usedTokens2 blocks
      val strengthVal = getStrength blocks
      val _ = if Graph.wellFormed idConSpec context
              then Logging.write "\n  context pattern graph is well formed"
              else Logging.write "\n  WARNING: context pattern graph is not well formed"
      val _ = if Graph.wellFormed idConSpec antecedent
              then Logging.write "\n  antecedent pattern graph is well formed"
              else Logging.write "\n  WARNING: antecedent pattern graph is not well formed"
      val _ = if Graph.wellFormed idConSpec consequent
              then Logging.write "\n  consequent pattern graph is well formed\n"
              else Logging.write "\n  WARNING: consequent pattern graph is not well formed\n"
      val isch = ([context,antecedent],[Graph.empty,consequent])
      val ischData = {name = name,
                      conSpecNames = [contextConSpecN,idConSpecN],
                      strength = strengthVal,
                      schema = isch}
      val _ = Logging.write ("done\n");
  in {typeSystemsData = #typeSystemsData dc,
      conSpecsData = #conSpecsData dc,
      knowledge = Knowledge.addSchema (#knowledge dc) ischData strengthVal,
      graphsData = #graphsData dc,
      transferRequests = #transferRequests dc}
  end

  fun addTransferSchema (N,cs) dc =
  let val nn = String.concat N
      val (name,x,cspecNs) = String.breakOn ":" nn
      val _ = if x = ":" then () else raise ParseError ("schema " ^ nn ^ " needs source, target and inter cspecs")
      val (sourceConSpecN,y,targetInterConSpecN) = String.breakOn "," (String.removeParentheses cspecNs)
      val _ = if y = "," then () else raise ParseError ("schema " ^ nn ^ " needs source, target and inter cspecs")
      val (targetConSpecN,y,interConSpecN) = String.breakOn "," (String.removeParentheses targetInterConSpecN)
      val _ = if y = "," then () else raise ParseError ("schema " ^ nn ^ " needs source, target and inter cspecs")
      val _ = case findSchemaWithName dc name of
                SOME knownSchema => if (#name knownSchema) = name andalso (List.last (#conSpecNames knownSchema)) = interConSpecN
                                    then raise ParseError ("duplciated name for tSchema " ^ name ^ " in space " ^ interConSpecN)
                                    else ()
              | NONE => ()
      val sourceConSpec = getConSpecWithName dc sourceConSpecN
      val sourceTySys = #typeSystem (#typeSystemData sourceConSpec)
      val targetConSpec = getConSpecWithName dc targetConSpecN
      val targetTySys = #typeSystem (#typeSystemData targetConSpec)
      val interConSpec = getConSpecWithName dc interConSpecN
      val interTySys = #typeSystem (#typeSystemData interConSpec)
      val _ = Logging.write ("\nAdding transfer schema " ^ name ^ "...")
      fun getPatternGraph k _ [] = (Logging.write ("  ERROR: " ^ k ^ " pattern not specified");
                              raise ParseError ("no " ^ k ^ " in tSchema " ^ String.concat cs))
        | getPatternGraph k tks ((x,ps) :: L) =
            if x = SOME k
            then Parser.parseGraph tks (String.concat ps)
            else getPatternGraph k tks L
      fun getStrength [] = (Logging.write ("  ERROR: strength not specified");
                            raise ParseError ("no strength in tSchema " ^ String.concat cs))
        | getStrength ((x,ss) :: L) =
            if x = SOME strengthKW
            then valOf (Real.fromString (String.concat ss))
                  handle Option => (Logging.write ("strength is not a real number in tSchema " ^ String.concat cs);
                                    raise Option)
            else getStrength L
      val blocks = gatherMaterialByKeywords tSchemaKeywords cs
      val (usedTokens1,source) = getPatternGraph sourceKW [] blocks
      val (usedTokens2,target) = getPatternGraph targetKW usedTokens1 blocks
      val (usedTokens3,antecedent) = getPatternGraph antecedentKW usedTokens2 blocks
      val (_,consequent) = getPatternGraph consequentKW usedTokens3 blocks
      val _ = if Graph.wellFormed sourceConSpec source
              then Logging.write "\n  source pattern is well formed"
              else Logging.write ("\n  WARNING: source pattern is not well formed: " ^ Graph.toString source)
      val _ = if Graph.wellFormed targetConSpec target
              then Logging.write "\n  target pattern is well formed"
              else Logging.write ("\n  WARNING: target pattern is not well formed: " ^ Graph.toString target)
      val _ = if Graph.wellFormed interConSpec antecedent
              then Logging.write "\n  antecedent patterns are well formed"
              else Logging.write ("\n  WARNING: antecedent pattern is not well formed: " ^ Graph.toString antecedent)
      val _ = if Graph.wellFormed interConSpec consequent
              then Logging.write "\n  consequent pattern is well formed\n"
              else Logging.write ("\n  WARNING: consequent pattern is not well formed: " ^ Graph.toString consequent ^ "\n")
      val tsch = ([source,target,antecedent],[Graph.empty,Graph.empty,consequent])
      val strengthVal = getStrength blocks
      val schData = {name = name,
                     conSpecNames = [sourceConSpecN,targetConSpecN,interConSpecN],
                      strength = strengthVal,
                      schema = tsch}
      val _ = Logging.write ("done\n");
  in {typeSystemsData = #typeSystemsData dc,
      conSpecsData = #conSpecsData dc,
      knowledge = Knowledge.addSchema (#knowledge dc) schData strengthVal,
      graphsData = #graphsData dc,
      transferRequests = #transferRequests dc}
  end

  fun insertGraph gRecord DC =
       {typeSystemsData = #typeSystemsData DC,
        conSpecsData = #conSpecsData DC,
        knowledge = #knowledge DC,
        graphsData = List.mergeNoEQUAL (fn (x,y) => String.compare (#name x, #name y)) [gRecord] (#graphsData DC),
        transferRequests = #transferRequests DC}

  fun addGraph (N, bs) dc =
  let val nn = case N of [x] => x | _ => raise ParseError ("invalid name for graph " ^ String.concat N)
      val (name,x,cspecN) = String.breakOn ":" nn
      val _ = if x = ":" then () else raise ParseError ("graph " ^ nn ^ " needs a cspec")
      val _ = case findGraphWithName dc name of
                SOME knownSchema => raise ParseError ("duplciated name for graph: " ^ name)
              | NONE => ()
      val cspec = getConSpecWithName dc cspecN
      val (u,g) = (*case removeOuterBrackets bs of
                      "liftString" :: gL => Lift.string (deTokenise gL)
                    | gL => Parser.parseGraph [] (deTokenise gL)*)
                  Parser.parseGraph [] (deTokenise (removeOuterBrackets bs))

      val _ = print ("\nChecking well-formedness of graph " ^ name ^ "...");
      val startTime = Time.now();
      val _ = if Graph.wellFormed cspec g then Logging.write ("\n  "^ name ^ " is well formed\n")
                else print ("\n  WARNING: "^ name ^" is not well formed\n")
      val endTime = Time.now();
      val runtime = Time.toMilliseconds endTime - Time.toMilliseconds startTime;
      val _ = print ("  well-formedness check runtime: "^ LargeInt.toString runtime ^ " ms \n...done\n  ");

      val gRecord = {name = name, conSpecN = cspecN, graph = g, usedTokens = u}
  in insertGraph gRecord dc
  end

  fun addTransferRequests ws dc =
     {typeSystemsData = #typeSystemsData dc,
      conSpecsData = #conSpecsData dc,
      knowledge = #knowledge dc,
      graphsData = #graphsData dc,
      transferRequests = #transferRequests dc @ [ws]}

  exception BadGoal
  fun processTransferRequests ws DC =
  let fun stringifyC ((x,c)::L) = "("^(valOf x)^","^ (String.stringOfList (fn x => x) c)^") : "^(stringifyC L)
        | stringifyC [] = ""
      val C = gatherMaterialByKeywords transferKeywords ws

      fun getGraph [] = raise ParseError "no graph to transfer"
        | getGraph ((x,c)::L) =
            if x = SOME sourceGraphKW
            then getGraphWithName DC (String.concat (removeOuterBrackets c))
            else getGraph L

      val graphRecord = getGraph C
      val graph = #graph graphRecord
      val sourceConSpecN = #conSpecN graphRecord
      val sourceConSpecData = getConSpecWithName DC sourceConSpecN
      val sourceTypeSystem = #typeSystem (#typeSystemData sourceConSpecData)

      fun getTargetConSpec [] = sourceConSpecData
        | getTargetConSpec ((x,c)::L) =
            if x = SOME targetConSpecKW
            then getConSpecWithName DC (String.concat (removeOuterBrackets c))
            else getTargetConSpec L
      fun getInterConSpec [] = raise ParseError "no inter-space specified"
        | getInterConSpec ((x,c)::L) =
            if x = SOME interConSpecKW
            then getConSpecWithName DC (String.concat (removeOuterBrackets c))
            else getInterConSpec L
            (*)
      fun getTargetTySys [] = sourceTypeSystem
        | getTargetTySys ((x,c)::L) =
            if x = SOME targetTypeSystemKW
            then #typeSystem (findTypeSystemDataWithName DC (String.concat c))
            else getTargetTySys L
      val targetTypeSystem = getTargetTySys C*)
      val targetConSpecData = getTargetConSpec C
      val targetConSpecN = #name targetConSpecData
      val targetTypeSystem = #typeSystem (#typeSystemData targetConSpecData)

      val interConSpecData = getInterConSpec C
      val interConSpecN = #name interConSpecData
      val interTypeSystem = #typeSystem (#typeSystemData interConSpecData)

      fun getGoal [] = raise ParseError "no goal for transfer"
        | getGoal ((x,c)::L) =
            if x = SOME goalKW
            then Parser.parseGraph (#usedTokens graphRecord) (deTokenise (removeOuterBrackets c))
            else getGoal L
      fun getOutput [] = NONE
        | getOutput ((x,c)::L) =
            if x = SOME outputKW
            then SOME ("output/latex/"^(String.concat (removeOuterBrackets c))^".tex")
            else getOutput L
      fun getOutputLimit [] = NONE
        | getOutputLimit ((x,c)::L) =
            if x = SOME outputLimitKW
            then SOME (valOf (Int.fromString (String.concat c)) handle Option => raise ParseError "outputLimit needs an integer!")
            else getOutputLimit L
      fun getSearchLimit [] = NONE
        | getSearchLimit ((x,c)::L) =
            if x = SOME searchLimitKW
            then Int.fromString (String.concat c)
            else getSearchLimit L
      fun getCompositionLimit [] = NONE
        | getCompositionLimit ((x,c)::L) =
            if x = SOME compositionLimitKW
            then Int.fromString (String.concat c)
            else getCompositionLimit L
      fun getGoalLimit [] = NONE
        | getGoalLimit ((x,c)::L) =
            if x = SOME goalLimitKW
            then Int.fromString (String.concat c)
            else getGoalLimit L
      fun getMatchTarget tks [] = NONE
        | getMatchTarget tks ((x,c)::L) =
            if x = SOME matchTargetKW
            then (let val (_,mtct) = Parser.parseGraph tks (deTokenise (removeOuterBrackets c))
                      val _ = if Graph.wellFormed targetConSpecData mtct
                              then Logging.write "\n  pattern for matching is well formed"
                              else Logging.write "\n  WARNING: pattern for matching is not well formed"
                  in SOME mtct
                  end)
            else getMatchTarget tks L
      fun getEager [] = false
        | getEager ((x,_)::L) =
            if x = SOME eagerKW
            then true
            else getEager L
      fun getIterative tks [] = false
        | getIterative tks ((x,_)::L) =
            if x = SOME iterativeKW
            then (case getMatchTarget tks C of
                      NONE => true
                    | _ => raise ParseError "iterative and matchTarget are incompatible")
            else getIterative tks L
      fun getInverse [] = false
        | getInverse ((x,_)::L) =
            if x = SOME inverseKW
            then true
            else getInverse L
      fun getUnistructured [] = false
        | getUnistructured ((x,_)::L) =
            if x = SOME unistructuredKW
            then true
            else getUnistructured L
      fun getSave [] = NONE
        | getSave ((x,c)::L) =
            if x = SOME saveKW
            then SOME (String.concat c)
            else getSave L
      val (usedTokens1,goal) = getGoal C
      val outputFilePath = getOutput C
      val outputLimit = getOutputLimit C
      val goalLimit = getGoalLimit C
      val compositionLimit = getCompositionLimit C
      val searchLimit = getSearchLimit C
      val eager = getEager C
      val iterative = getIterative usedTokens1 C
      val KB = knowledgeOf DC
      val inverse = getInverse C
      val unistructured = getUnistructured C
      val targetPattern = getMatchTarget usedTokens1 C
      val save = getSave C
      fun mkLatexGoals res =
        let val goalGraph = List.nth(#2(#sequent res),2)
            val goalsS = if Graph.isEmpty goalGraph
                         then "\\centerline{NO\\ OPEN\\ GOALS!}\n"
                         else Latex.propositionsOfGraph goalGraph handle Fail "x" => Latex.tikzOfGraph (0.0,0.0) goalGraph
            val alignedGoals = "\n " ^ "\\centerline{\\textbf{Open\\ goals}}\\smallskip\n"
                                    ^ goalsS ^ "\n\n\\bigskip"
                                    ^ "\\centerline{\\textbf{transfer\\ score}}\n"
                                    ^ "\\centerline{" ^ Latex.realToString (#score res) ^ "}"
        in alignedGoals
        end
      fun mkLatexConstructionsAndGoals res =
        let val dischargedGraph = List.nth(#discharged res,1)
            val targetGraph = List.nth(#2(#sequent res),1)
            val targetGraphFull = Graph.join targetGraph dischargedGraph
            val latexConstructions = Latex.tikzOfGraph (0.0,0.0) targetGraphFull
            val latexLeft = Latex.environment "minipage" "[t]{0.65\\linewidth}" (Latex.printWithHSpace 0.2 [latexConstructions])
            val latexGoals = mkLatexGoals res
            val latexRight = Latex.environment "minipage" "[t]{0.33\\linewidth}" latexGoals
        in Latex.environment "center" "" (Latex.printWithHSpace 0.0 ([latexLeft,latexRight]))
        end
      val _ = print ("\nApplying structure transfer to "^ #name graphRecord ^ "...");
      val startTime = Time.now();
      
      val state = State.initState sourceConSpecData targetConSpecData interConSpecData graph goal
      val TTT = [#typeSystem (#typeSystemData sourceConSpecData), #typeSystem (#typeSystemData targetConSpecData), #typeSystem (#typeSystemData interConSpecData)]
      val adaptedKB = Knowledge.adaptToMSpace [sourceConSpecN,targetConSpecN,interConSpecN] KB
      val SC = #schemas adaptedKB
      val results = State.transfer (goalLimit,compositionLimit,searchLimit) eager iterative unistructured TTT SC state;

      val nres = length (Seq.list_of results);
      val listOfResults = case outputLimit of SOME n => #1(Seq.chop n results) | NONE => Seq.list_of results;
      val endTime = Time.now();
      val runtime = Time.toMilliseconds endTime - Time.toMilliseconds startTime;
      val _ = print ("\n" ^ "  runtime: "^ LargeInt.toString runtime ^ " ms \n");
      val _ = print ("  number of results: " ^ Int.toString nres ^ "\n");
      val (score,ngoals) =
            case Seq.pull results of
              SOME (x,_) => (#score x,
                             Graph.numberOfConstructors (List.nth(#2(#sequent x),2)))
            | NONE => (0.0,~1)
      val _ = print ("  number of open goals (top result): " ^ Int.toString ngoals ^ "\n")
      val _ = print ("  transfer score (top result): " ^ Real.toString score)
        val _ = print ("\n...done\n")
      val _ = print "\nComposing patterns and creating tikz figures...";
      val latexCompsAndGoals = Latex.printSubSections 1 (map mkLatexConstructionsAndGoals listOfResults);
      val latexCT = Latex.tikzOfGraph (0.0,0.0) graph;
      val _ = print "done\n";
      val _ = print "\nGenerating LaTeX document...";
      val latexOriginalConsAndGoals = Latex.environment "center" "" (latexCT);
      val opening = (Latex.sectionTitle false "Original graph") ^ "\n"
      val resultText = (Latex.sectionTitle false "Structure transfer results") ^ "\n"
      val _ = case outputFilePath of
                SOME filePath => let val outputFile = TextIO.openOut filePath
                                     val _ = Latex.outputDocument outputFile (opening ^ latexOriginalConsAndGoals ^ "\n\n " ^ resultText ^ latexCompsAndGoals);
                                     val _ = TextIO.closeOut outputFile;
                                 in print ("done!\n" ^ "  output file: " ^ filePath ^ "\n\n")
                                 end
              | NONE => ()
  in DC
  end


  fun tsdCmp (T,T') = String.compare (#name T, #name T')
  fun csdCmp (C,C') = String.compare (#name C, #name C')
  fun ctCmp (c,c') = String.compare (#name c, #name c')

  fun joinDocumentContents ({typeSystemsData = ts,
                             conSpecsData = sp,
                             knowledge = kb,
                             graphsData = cs,
                             transferRequests = tr} :: L) =
    (case joinDocumentContents L of
      {typeSystemsData = ts',
       conSpecsData = sp',
       knowledge = kb',
       graphsData = cs',
       transferRequests = tr'} =>
          {typeSystemsData = List.mergeNoEQUAL tsdCmp ts ts',
           conSpecsData = List.mergeNoEQUAL csdCmp sp sp',
           knowledge = Knowledge.join kb kb',
           graphsData = List.mergeNoEQUAL ctCmp cs cs',
           transferRequests = tr @ tr'})
  | joinDocumentContents [] = emptyDocContent

  fun read filename =
  let val file_str =
          let
            val file = TextIO.openIn ("input/"^filename^".oruga") handle Io => TextIO.openIn ("input/"^filename);
            val contents = TextIO.inputAll file;
          in
            TextIO.closeIn file;
            contents
          end
      handle IO.Io _ =>
        (print("File NOT found: neither input/" ^ filename ^ ".oruga nor input/" ^ filename ^ " found\n");
        OS.Process.exit(OS.Process.failure));

      val words = tokenise file_str
      val blocks = gatherMaterialByKeywords bigKeywords words

      val importFilenames = List.filter (fn (x,_) => x = SOME importKW) blocks
      val importedContents = map (read o deTokenise o #2) importFilenames
      val importedContent = joinDocumentContents importedContents

      fun distribute [] = importedContent
        | distribute ((x,c)::L) =
          let val dc = distribute L
              val (n,eq,ws) = breakListOn "=" c
              (*val _ = if eq = "=" then () else raise ParseError (String.concat n)*)
          in if x = SOME typeSystemKW then addTypeSystem (n,ws) dc else
             if x = SOME conSpecKW then addConSpec (n, ws) dc else
             if x = SOME iSchemaKW then addInferenceSchema (n,ws) dc else
             if x = SOME tSchemaKW then addTransferSchema (n,ws) dc else
             if x = SOME graphKW then addGraph (n,ws) dc else
             if x = SOME transferKW then addTransferRequests c dc else
             if x = SOME commentKW then dc else raise ParseError "error: this shouldn't have happened"
          end handle Bind => raise ParseError "expected name = content, found multiple words before ="

      val nonImported = List.filter (fn (x,_) => x <> SOME importKW) blocks
      val contentBeforeTransfers = distribute (rev nonImported)
      val contentAfterTransfers = foldl (uncurry processTransferRequests)
                                        contentBeforeTransfers
                                        (#transferRequests contentBeforeTransfers)
  in contentAfterTransfers
  end

end
