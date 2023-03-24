import "oruga.parser";
import "oruga.lift";
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
  val tokenise : string -> string list
  val deTokenise : string list -> string
  val normaliseString : string -> string
  val parseConstruction : CSpace.conSpecData -> string -> Construction.construction

  val findTypeSystemDataWithName : documentContent -> string -> Type.typeSystemData option
  val findConSpecWithName : documentContent -> string -> CSpace.conSpecData option
  val findConstructionWithName : documentContent -> string -> constructionData option
  val findTransferSchemaWithName : documentContent -> string -> InterCSpace.tSchemaData option
  val findInferenceSchemaWithName : documentContent -> string -> Knowledge.iSchemaData option

  val getTypeSystemDataWithName : documentContent -> string -> Type.typeSystemData
  val getConSpecWithName : documentContent -> string -> CSpace.conSpecData
  val getConstructionWithName : documentContent -> string -> constructionData
  val getTransferSchemaWithName : documentContent -> string -> InterCSpace.tSchemaData

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
  val modeKW = "modes"
  val conSpecKeywords = [constructorsKW,conSpecImportsKW,modeKW]

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
  val transferKeywords = [sourceConstructionKW,goalKW,outputKW,limitKW,searchLimitKW,goalLimitKW,compositionLimitKW,eagerKW,
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

  fun parseConstruction cspec s =
    let fun pc s' =
         case String.breakOn "[" s' of
           (_,"",_) => (case String.breakOn "<-" s' of
                            (tt,"<-",ctvar) => if String.isPrefix "?" ctvar
                                               then Construction.TCPair ({constructor = CSpace.makeConstructor(ctvar,([],"")), token = parseToken tt},[])
                                               else raise ParseError ("unexpected construction variable in: " ^ s')
                          | _ => Construction.Source (parseToken s'))
         | (tcps,_,ss) =>
             let val tcp = parseTCPair tcps cspec
                 val tok = #token tcp
                 val (xs,ys) = Parser.breakOnClosingDelimiter (#"[",#"]") ss
                 val _ = if ys = [] then ()
                         else raise ParseError ("invalid input sequence to constructor: " ^ ss)
             in Construction.TCPair (tcp, Parser.splitLevelApply (pc o String.removeParentheses) xs)
             end
    in Construction.fixReferences (pc s)
    end;

  val parseConstruction_rpc =
   fn findCSpec =>
      Rpc.provide ("oruga.document.parseConstruction",
                   Rpc.Datatype.tuple2(String.string_rpc, String.string_rpc),
                   Option.option_rpc(Construction.construction_rpc))
                  (fn (cspecName, s) =>
                      Option.mapPartial
                          (fn cspec => SOME (parseConstruction cspec s)
                                       handle ParseError => NONE)
                          (findCSpec cspecName) );


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
        constructionsData : constructionData list,
        transferRequests : (string list) list}

  val emptyDocContent =
      {typeSystemsData = [],
       conSpecsData = [],
       knowledge = Knowledge.empty,
       constructionsData = [],
       transferRequests = []}

  val typeSystemsDataOf = #typeSystemsData
  val conSpecsDataOf = #conSpecsData
  val knowledgeOf = #knowledge
  val constructionsDataOf = #constructionsData
  val transferRequestsOf = #transferRequests

  fun findTypeSystemDataWithName DC n =
    List.find (fn x => #name x = n) (typeSystemsDataOf DC)

  fun findConSpecWithName DC n =
    List.find (fn x => #name x = n) (conSpecsDataOf DC)

  fun findConstructionWithName DC n =
    FiniteSet.find (fn x => #name x = n) (constructionsDataOf DC)

  fun findTransferSchemaWithName DC n =
    Knowledge.findTransferSchemaWithName (knowledgeOf DC) n

  fun findInferenceSchemaWithName DC n =
    Knowledge.findInferenceSchemaWithName (knowledgeOf DC) n

  fun getTypeSystemDataWithName DC n =
    valOf (findTypeSystemDataWithName DC n)
    handle Option => raise ParseError ("no type system with name " ^ n)

  fun getConSpecWithName DC n =
    valOf (findConSpecWithName DC n)
    handle Option => raise ParseError ("no constructor specification with name " ^ n)

  fun getConstructionWithName DC n =
    valOf (findConstructionWithName DC n)
    handle Option => raise ParseError ("no construction with name " ^ n)

  fun getTransferSchemaWithName DC n =
    valOf (findTransferSchemaWithName DC n)
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
      constructionsData = #constructionsData dc,
      transferRequests = #transferRequests dc}
  end

  fun parseConstructor s =
    case String.breakOn "--" s of
      (cstring,_,rstring) =>
          (case String.breakOn ":" cstring of
            (cname,":",csig) =>
              ((case String.breakOn "->" csig of
                  (inTyps,"->",outTyp) => CSpace.makeConstructor (cname, CSpace.makeCTyp (Parser.list Type.fromString inTyps, Type.fromString outTyp))
                | _ => raise ParseError ("bad signature for constructor: " ^ s)
              ),rstring)
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
      fun getModes [] = []
        | getModes ((x,c)::L) =
            if x = SOME modeKW
            then String.tokens (fn k => k = #",") (String.concat (removeOuterBrackets c))
            else getModes L

      fun processConstructorData [] = ([], fn _ => "")
        | processConstructorData ((c,r)::cL) =
        let val (cs,f) = processConstructorData cL
            fun updf x = if CSpace.sameConstructors x c then r else f x
        in (c::cs,updf)
        end

      val (newConstructors,newRegFun) = (case processConstructorData (getConstructors blocks) of (x,y) => (FiniteSet.ofList x,y))
      val importBlocks = getImports blocks
      val importedConSpecNames = map #name importBlocks
      val importedConstructorSets = map #constructors importBlocks
      val importedCognitiveData = map #cognitiveData importBlocks
      val allConstructors = foldl (uncurry FiniteSet.union) FiniteSet.empty (newConstructors :: importedConstructorSets)

      fun joinCognitiveData [] = {modes = getModes blocks, tokenRegistration = newRegFun}
        | joinCognitiveData ({modes,tokenRegistration}::L) =
          let val CDrec = joinCognitiveData L
              val updModes = FiniteSet.union (#modes CDrec) modes
              fun updTokReg x = (case tokenRegistration x of "" => (#tokenRegistration CDrec) x | y => y)
          in {modes = updModes, tokenRegistration = updTokReg}
          end

      val cognitiveData = joinCognitiveData importedCognitiveData

      val _ = FiniteSet.map ((fn x => Logging.write ("  " ^ x ^ "\n")) o CSpace.stringOfConstructor) allConstructors
      val cspec = {name = name,
                   typeSystemData = getTypeSystemDataWithName dc typeSystemN,
                   constructors = allConstructors,
                   cognitiveData = cognitiveData}
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
      constructionsData = #constructionsData dc,
      transferRequests = #transferRequests dc}
  end

  fun addInferenceSchema (N,cs) dc =
  let val nn = String.concat N
      val (name,x,cspecNs) = String.breakOn ":" nn
      val _ = if x = ":" then () else raise ParseError ("schema " ^ nn ^ " needs source, target and inter cspecs")
      val (contextConSpecN,y,idConSpecN) = String.breakOn "," (String.removeParentheses cspecNs)
      val _ = if y = "," then () else raise ParseError ("schema " ^ nn ^ " needs source, target and inter cspecs")
      val _ = case findInferenceSchemaWithName dc name of
                SOME knownSchema => if (#name knownSchema) = name andalso (#idConSpecN knownSchema) = idConSpecN
                                    then raise ParseError ("duplciated name for tSchema " ^ name ^ " in space " ^ idConSpecN)
                                    else ()
              | NONE => ()
      val contextConSpec = getConSpecWithName dc contextConSpecN
      val contextTySys = #typeSystem (#typeSystemData contextConSpec)
      val idConSpec = getConSpecWithName dc idConSpecN
      val idTySys = #typeSystem (#typeSystemData idConSpec)
      val _ = Logging.write ("\nAdding inference schema " ^ name ^ "...")
      fun getPattern k [] = (Logging.write ("  ERROR: " ^ k ^ " pattern not specified");
                              raise ParseError ("no " ^ k ^ " in iSchema " ^ String.concat cs))
        | getPattern k ((x,ps) :: L) =
            if x = SOME k
            then parseConstruction (if k = contextKW then contextConSpec else idConSpec) (deTokenise (removeOuterBrackets ps))
            else getPattern k L
      fun getAntecedent [] = (Logging.write ("  ERROR: token relation not specified");
                              raise ParseError ("no token rels in iSchema " ^ String.concat cs))
        | getAntecedent ((x,trss) :: L) =
            if x = SOME antecedentKW
            then if trss = [] then []
                 else Parser.splitLevelApply (parseConstruction idConSpec) (List.maps explode (removeOuterBrackets trss))
            else getAntecedent L
      fun getConsequent [] = (Logging.write ("  ERROR: construct relation not specified");
                                raise ParseError ("no construct rel in iSchema " ^ String.concat cs))
        | getConsequent ((x,crs) :: L) =
            if x = SOME consequentKW
            then parseConstruction idConSpec (String.concat (removeOuterBrackets crs))
            else getConsequent L
      fun getStrength [] = (Logging.write ("  ERROR: strength not specified");
                            raise ParseError ("no strength in iSchema " ^ String.concat cs))
        | getStrength ((x,ss) :: L) =
            if x = SOME strengthKW
            then valOf (Real.fromString (String.concat ss)) handle Option => (Logging.write ("strength is not a real number in iSchema " ^ String.concat cs);raise Option)
            else getStrength L
      val blocks = gatherMaterialByKeywords iSchemaKeywords cs
      val context = getPattern contextKW blocks
      val antecedent = getAntecedent blocks
      val consequent = getConsequent blocks
      val strengthVal = getStrength blocks
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
                      strength = strengthVal,
                      iSchema = isch}
      val _ = Logging.write ("done\n");
  in {typeSystemsData = #typeSystemsData dc,
      conSpecsData = #conSpecsData dc,
      knowledge = Knowledge.addInferenceSchema (#knowledge dc) ischData strengthVal,
      constructionsData = #constructionsData dc,
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
      val _ = case findTransferSchemaWithName dc name of
                SOME knownSchema => if (#name knownSchema) = name andalso (#interConSpecN knownSchema) = interConSpecN
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
      fun getPattern k [] = (Logging.write ("  ERROR: " ^ k ^ " pattern not specified");
                              raise ParseError ("no " ^ k ^ " in tSchema " ^ String.concat cs))
        | getPattern k ((x,ps) :: L) =
            if x = SOME k
            then parseConstruction (if k = sourceKW then sourceConSpec else targetConSpec) (String.concat (removeOuterBrackets ps))
            else getPattern k L
      fun getAntecedent [] = (Logging.write ("  ERROR: token relation not specified");
                              raise ParseError ("no token rels in tSchema " ^ String.concat cs))
        | getAntecedent ((x,trss) :: L) =
            if x = SOME antecedentKW
            then if trss = [] then []
                 else Parser.splitLevelApply (parseConstruction interConSpec) (List.maps explode (removeOuterBrackets trss))
            else getAntecedent L
      fun getConsequent [] = (Logging.write ("  ERROR: construct relation not specified");
                                raise ParseError ("no construct rel in tSchema " ^ String.concat cs))
        | getConsequent ((x,crs) :: L) =
            if x = SOME consequentKW
            then parseConstruction interConSpec (String.concat (removeOuterBrackets crs))
            else getConsequent L
      fun getStrength [] = (Logging.write ("  ERROR: strength not specified");
                            raise ParseError ("no strength in tSchema " ^ String.concat cs))
        | getStrength ((x,ss) :: L) =
            if x = SOME strengthKW
            then valOf (Real.fromString (String.concat ss))
                  handle Option => (Logging.write ("strength is not a real number in tSchema " ^ String.concat cs);
                                    raise Option)
            else getStrength L
      val blocks = gatherMaterialByKeywords tSchemaKeywords cs
      val source = getPattern sourceKW blocks
      val target = getPattern targetKW blocks
      val antecedent = getAntecedent blocks
      val consequent = getConsequent blocks
      val _ = if Construction.wellFormed sourceConSpec source
              then Logging.write "\n  source pattern is well formed"
              else Logging.write ("\n  WARNING: source pattern is not well formed: " ^ Construction.toString source)
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
      val strengthVal = getStrength blocks
      val tschData = {name = name,
                      sourceConSpecN = sourceConSpecN,
                      targetConSpecN = targetConSpecN,
                      interConSpecN = interConSpecN,
                      strength = strengthVal,
                      tSchema = tsch}
      val _ = Logging.write ("done\n");
  in {typeSystemsData = #typeSystemsData dc,
      conSpecsData = #conSpecsData dc,
      knowledge = Knowledge.addTransferSchema (#knowledge dc) tschData strengthVal,
      constructionsData = #constructionsData dc,
      transferRequests = #transferRequests dc}
  end

  fun insertConstruction ctRecord DC =
       {typeSystemsData = #typeSystemsData DC,
        conSpecsData = #conSpecsData DC,
        knowledge = #knowledge DC,
        constructionsData = List.mergeNoEQUAL (fn (x,y) => String.compare (#name x, #name y)) [ctRecord] (#constructionsData DC),
        transferRequests = #transferRequests DC}

  fun addConstruction (N, bs) dc =
  let val nn = case N of [x] => x | _ => raise ParseError ("invalid name for construction " ^ String.concat N)
      val (name,x,cspecN) = String.breakOn ":" nn
      val _ = if x = ":" then () else raise ParseError ("construction " ^ nn ^ " needs a cspec")
      val _ = case findConstructionWithName dc name of
                SOME knownSchema => raise ParseError ("duplciated name for construction: " ^ name)
              | NONE => ()
      val cspec = getConSpecWithName dc cspecN
      val ct = case removeOuterBrackets bs of
                  "liftString" :: ctL => Lift.string (deTokenise ctL)
                | ctL => parseConstruction cspec (deTokenise ctL)

      val _ = print ("\nChecking well-formedness of construction " ^ name ^ "...");
      val startTime = Time.now();
      val _ = if Construction.wellFormed cspec ct then Logging.write ("\n  "^ name ^ " is well formed\n")
                else print ("\n  WARNING: "^ name ^" is not well formed\n")
      val endTime = Time.now();
      val runtime = Time.toMilliseconds endTime - Time.toMilliseconds startTime;
      val _ = print ("  well-formedness check runtime: "^ LargeInt.toString runtime ^ " ms \n...done\n  ");

      val ctRecord = {name = name, conSpecN = cspecN, construction = ct}
  in insertConstruction ctRecord dc
  end

  fun addTransferRequests ws dc =
     {typeSystemsData = #typeSystemsData dc,
      conSpecsData = #conSpecsData dc,
      knowledge = #knowledge dc,
      constructionsData = #constructionsData dc,
      transferRequests = #transferRequests dc @ [ws]}

  exception BadGoal
  fun processTransferRequests ws DC =
  let fun stringifyC ((x,c)::L) = "("^(valOf x)^","^ (String.stringOfList (fn x => x) c)^") : "^(stringifyC L)
        | stringifyC [] = ""
      val C = gatherMaterialByKeywords transferKeywords ws

      fun getConstruction [] = raise ParseError "no construction to transfer"
        | getConstruction ((x,c)::L) =
            if x = SOME sourceConstructionKW
            then getConstructionWithName DC (String.concat (removeOuterBrackets c))
            else getConstruction L

      val constructionRecord = getConstruction C
      val construction = #construction constructionRecord
      val sourceConSpecN = #conSpecN constructionRecord
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
      val targetTypeSystem = #typeSystem (#typeSystemData targetConSpecData)

      val interConSpecData = getInterConSpec C
      val interTypeSystem = #typeSystem (#typeSystemData interConSpecData)

      fun getGoal [] = raise ParseError "no goal for transfer"
        | getGoal ((x,c)::L) =
            if x = SOME goalKW
            then parseConstruction interConSpecData (deTokenise (removeOuterBrackets c))
            else getGoal L
      fun getOutput [] = NONE
        | getOutput ((x,c)::L) =
            if x = SOME outputKW
            then SOME ("output/latex/"^(String.concat (removeOuterBrackets c))^".tex")
            else getOutput L
      fun getLimit [] = NONE
        | getLimit ((x,c)::L) =
            if x = SOME limitKW
            then SOME (valOf (Int.fromString (String.concat c)) handle Option => raise ParseError "limit needs an integer!")
            else getLimit L
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
      fun getMatchTarget [] = NONE
        | getMatchTarget ((x,c)::L) =
            if x = SOME matchTargetKW
            then (let val mtct = parseConstruction targetConSpecData (deTokenise (removeOuterBrackets c))
                      val _ = if Construction.wellFormed targetConSpecData mtct
                              then Logging.write "\n  pattern for matching is well formed"
                              else Logging.write "\n  WARNING: pattern for matching is not well formed"
                  in SOME mtct
                  end)
            else getMatchTarget L
      fun getEager [] = false
        | getEager ((x,_)::L) =
            if x = SOME eagerKW
            then true
            else getEager L
      fun getIterative [] = false
        | getIterative ((x,_)::L) =
            if x = SOME iterativeKW
            then (case getMatchTarget C of
                      NONE => true
                    | _ => raise ParseError "iterative and matchTarget are incompatible")
            else getIterative L
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
      val goal = getGoal C
      val outputFilePath = getOutput C
      val limit = getLimit C
      val goalLimit = getGoalLimit C
      val compositionLimit = getCompositionLimit C
      val searchLimit = getSearchLimit C
      val eager = getEager C
      val iterative = getIterative C
      val KB = knowledgeOf DC
      val inverse = getInverse C
      val unistructured = getUnistructured C
      val targetPattern = getMatchTarget C
      val save = getSave C
      fun mkLatexGoals res =
        let val goal = State.originalGoalOf res
            val goals = State.goalsOf res
            val goalsS = if List.null goals
                         then "NO\\ OPEN\\ GOALS!"
                         else String.concatWith "\n " (map (Latex.construction (0.0,0.0)) goals)
            val originalGoalS = Latex.construction (0.0,0.0) goal ^ "\\\\ \n"
            val IS = Heuristic.scoreMain res
            val alignedGoals = "\n " ^ ("\\textbf{Original\\ goal}\\\\\n"
                                                                      ^ originalGoalS
                                                                      ^ "\\\\ \\textbf{Open\\ goals}\\\\\n"
                                                                      ^ goalsS ^ "\\\\"
                                                                      ^ "\\\\ \\textbf{transfer\\ score}\\\\\n"
                                                                      ^ Latex.realToString IS)
        in alignedGoals
        end
      fun mkLatexProof tproof =
        let val ct = TransferProof.toConstruction tproof;
        in (*Latex.construction (0.0,0.0) ct*) Latex.environment "alltt" "" (Construction.toString ct)
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
            val latexProof = mkLatexProof tproof
            (*val CSize = List.sumMapInt Composition.size comps*)
        in Latex.environment "center" "" (Latex.printWithHSpace 0.0 ([latexLeft,latexRight(*Int.toString CSize,*)]))
        end
      val _ = print ("\nApplying structure transfer to "^ #name constructionRecord ^ "...");
      val startTime = Time.now();
      val targetTokens = FiniteSet.filter
                             (fn x => Set.elementOf (CSpace.typeOfToken x) (#Ty targetTypeSystem))
                             (Construction.leavesOfConstruction goal)
                          handle Empty => (Logging.write "ERROR : goal has no tokens in target construction space\n"; raise BadGoal)
      val state = Transfer.initState sourceConSpecData targetConSpecData interConSpecData inverse KB construction goal
      val results = Transfer.masterTransfer (goalLimit,compositionLimit,searchLimit) eager iterative unistructured targetPattern state;
      val nres = length (Seq.list_of results);
      val listOfResults = case limit of SOME n => #1(Seq.chop n results) | NONE => Seq.list_of results;
      val endTime = Time.now();
      val runtime = Time.toMilliseconds endTime - Time.toMilliseconds startTime;
      val _ = print ("\n" ^ "  runtime: "^ LargeInt.toString runtime ^ " ms \n");
      val _ = print ("  number of results: " ^ Int.toString nres ^ "\n");
      val (score,ngoals,constructionsToSave) =
            case Seq.pull results of
              SOME (x,_) => (Heuristic.scoreMain x,
                             length (#goals x),
                             List.maps Composition.resultingConstructions (State.patternCompsOf x))
            | NONE => (0.0,~1,[])
      fun resultingConstructionData _ [] = raise ParseError ""
        | resultingConstructionData s [rct] = [{name = s, conSpecN = #name targetConSpecData, construction = rct}]
        | resultingConstructionData s L = let fun assignNames n (rct::rctL) = {name = s ^ "_" ^ Int.toString n, conSpecN = #name targetConSpecData, construction = rct} :: assignNames (n+1) rctL
                                                | assignNames _ [] = []
                                          in assignNames 0 L end
      val updDC = case save of SOME s => foldl (uncurry insertConstruction) DC (resultingConstructionData s constructionsToSave) | NONE => DC
      (*val tproofConstruction = map (TransferProof.toConstruction o State.transferProofOf) listOfResults
      val _ = print (Construction.toString  (hd tproofConstruction))*)
      val _ = print ("  number of open goals (top result): " ^ Int.toString ngoals ^ "\n")
      val _ = print ("  transfer score (top result): " ^ Real.toString score)
        val _ = print ("\n...done\n")
      val _ = print "\nComposing patterns and creating tikz figures...";
      val latexCompsAndGoals = Latex.printSubSections 1 (map mkLatexConstructionsAndGoals listOfResults);
      val latexCT = Latex.construction (0.0,0.0) construction;
      val _ = print "done\n";
      val _ = print "\nGenerating LaTeX document...";
      val latexOriginalConsAndGoals = Latex.environment "center" "" latexCT;
      val opening = (Latex.sectionTitle false "Original construction") ^ "\n"
      val resultText = (Latex.sectionTitle false "Structure transfer results") ^ "\n"
      val _ = case outputFilePath of
                SOME filePath => let val outputFile = TextIO.openOut filePath
                                     val _ = Latex.outputDocument outputFile (opening ^ latexOriginalConsAndGoals ^ "\n\n " ^ resultText ^ latexCompsAndGoals);
                                     val _ = TextIO.closeOut outputFile;
                                 in print ("done!\n" ^ "  output file: " ^ filePath ^ "\n\n")
                                 end
              | NONE => ()
  in updDC
  end

  fun tsdCmp (T,T') = String.compare (#name T, #name T')
  fun csdCmp (C,C') = String.compare (#name C, #name C')
  fun ctCmp (c,c') = String.compare (#name c, #name c')

  fun joinDocumentContents ({typeSystemsData = ts,
                             conSpecsData = sp,
                             knowledge = kb,
                             constructionsData = cs,
                             transferRequests = tr} :: L) =
    (case joinDocumentContents L of
      {typeSystemsData = ts',
       conSpecsData = sp',
       knowledge = kb',
       constructionsData = cs',
       transferRequests = tr'} =>
          {typeSystemsData = List.mergeNoEQUAL tsdCmp ts ts',
           conSpecsData = List.mergeNoEQUAL csdCmp sp sp',
           knowledge = Knowledge.join kb kb',
           constructionsData = List.mergeNoEQUAL ctCmp cs cs',
           transferRequests = tr @ tr'})
  | joinDocumentContents [] = emptyDocContent



  fun read filename =
  let val file_str =
          let
            val file = TextIO.openIn ("input/"^filename);
            val contents = TextIO.inputAll file;
          in
            TextIO.closeIn file;
            contents
          end
      handle IO.Io _ =>
        (print("File NOT found: input/" ^ filename ^ "\n");
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
             if x = SOME constructionKW then addConstruction (n,ws) dc else
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
