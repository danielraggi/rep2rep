import "oruga.parser";
import "latex.latex";

signature DOCUMENT =
sig
  type documentContent

  val joinDocumentContents : documentContent list -> documentContent
  val read : string -> documentContent
  val knowledgeOf : documentContent -> Knowledge.base
  val typeSystemsDataOf : documentContent -> Type.typeSystemData list
  val conSpecsOf : documentContent -> CSpace.conSpec list
  val constructionsOf : documentContent -> {name : string, conSpec : string, construction : Construction.construction} FiniteSet.set
  val transferRequestsOf : documentContent ->  (string list) list
  val findTypeSystemDataWithName : documentContent -> string -> Type.typeSystemData
  val findConSpecWithName : documentContent -> string -> CSpace.conSpec
  val findConstructionWithName : documentContent -> string -> {name : string, conSpec : string, construction : Construction.construction}
  val findTransferSchemaWithName : documentContent -> string -> TransferSchema.tSch

end;

structure Document : DOCUMENT =
struct

  val ParseError = Parser.ParseError;

  val importKW = "import"
  val typeSystemKW = "typeSystem"
  val conSpecKW = "conSpec"
  val tSchemaKW = "tSchema"
  val constructionKW = "construction"
  val transferKW = "transfer"
  val commentKW = "comment"
  val bigKeywords = [importKW,typeSystemKW,conSpecKW,tSchemaKW,constructionKW,transferKW,commentKW]

  val typesKW = "types"
  val subTypeKW = "order"
  val typeImportsKW = "imports"
  val typeKeywords = [typesKW,subTypeKW,typeImportsKW]

  val targetKW = "target"
  val sourceKW = "source"
  val antecedentKW = "antecedent"
  val consequentKW = "consequent"
  val pullListKW = "pull"
  val strengthKW = "strength"
  val tSchemaKeywords = [targetKW,sourceKW,antecedentKW,consequentKW,pullListKW,strengthKW]

  val sourceTypeSystemKW = "sourceTypeSystem"
  val targetTypeSystemKW = "targetTypeSystem"
  val sourceConstructionKW = "sourceConstruction"
  val goalKW = "goal"
  val outputKW = "output"
  val limitKW = "limit"
  val iterativeKW = "iterative"
  val unistructuredKW = "unistructured"
  val matchTargetKW = "matchTarget"
  val targetConSpecKW = "targetConSpec"
  val transferKeywords = [targetTypeSystemKW,sourceConstructionKW,goalKW,outputKW,limitKW,iterativeKW,unistructuredKW,matchTargetKW,targetConSpecKW]


  fun breakOn s [] = ([],"",[])
  | breakOn s (w::ws) = if w = s then ([],s,ws) else (case breakOn s ws of (x,s',y) => (w::x,s',y))

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

  type documentContent = {typeSystemsData : Type.typeSystemData list,
                          conSpecs : CSpace.conSpec list,
                          knowledge : Knowledge.base,
                          constructions : {name : string, conSpec : string, construction : Construction.construction} list,
                          transferRequests : (string list) list,
                          strengths : string -> real option}

  val emptyDocContent = {typeSystemsData = [],
                         conSpecs = [],
                         knowledge = Knowledge.empty,
                         constructions = [],
                         transferRequests = [],
                         strengths = (fn _ => NONE)}

  val typeSystemsDataOf = #typeSystemsData
  val conSpecsOf = #conSpecs
  val knowledgeOf = #knowledge
  val constructionsOf = #constructions
  val transferRequestsOf = #transferRequests
  val strengthsOf = #strengths

  fun findTypeSystemDataWithName DC n =
    valOf (List.find (fn x => #name x = n) (typeSystemsDataOf DC))
    handle Option => raise ParseError ("no type system with name " ^ n)

  fun findConSpecWithName DC n =
    valOf (List.find (fn x => #name x = n) (conSpecsOf DC))
    handle Option => raise ParseError ("no constructor specification with name " ^ n)

  fun findConstructionWithName DC n =
    valOf (FiniteSet.find (fn x => #name x = n) (constructionsOf DC))
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
      ("_",":",superTyp) => (fn x => x = Type.typeOfString superTyp orelse String.isSuffix (":"^superTyp) (Type.nameOfType x),
                             {typ = Type.typeOfString superTyp, subTypeable = true})
    | _ => (fn x => x = Type.typeOfString s, {typ = Type.typeOfString s, subTypeable = false})

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
        val strippedPrincipalTypes = map #typ principalTypes
        val subTypeableTypes = map #typ (FiniteSet.filter #subTypeable principalTypes)
        val principalSubType = Type.closureOverFiniteSet strippedPrincipalTypes (#subType typeSystem)
        val subType = Type.fixForSubtypeable subTypeableTypes principalSubType
        val typeSystem = {Ty = #Ty typeSystem, subType = subType}
    in {name = name, typeSystem = typeSystem, principalTypes = principalTypes}
    end

  fun addTypeSystem (name, tss) dc =
  let val _ = print ("\nAdding type system " ^ name ^ "...");
      val blocks = contentForKeywords typeKeywords tss
      fun getTyps [] = []
        | getTyps ((x,c)::L) =
            if x = SOME typesKW
            then map parseTyp (String.tokens (fn x => x = #",") (String.concat c))
            else getTyps L
      fun getOrder [] = []
        | getOrder ((x,c)::L) =
            if x = SOME subTypeKW
            then map inequality (String.tokens (fn x => x = #",") (String.concat c))
            else getOrder L
      fun getImports [] = []
        | getImports ((x,c)::L) =
            if x = SOME typeImportsKW
            then map (findTypeSystemDataWithName dc) (String.tokens (fn x => x = #",") (String.concat c))
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
              then print ("done\n")
              else print ("\n  WARNING: Type System " ^ name ^ " is not well defined and it's probably not your fault!\n")

  in {typeSystemsData = typeSystemData :: (#typeSystemsData dc),
      conSpecs = #conSpecs dc,
      knowledge = #knowledge dc,
      constructions = #constructions dc,
      transferRequests = #transferRequests dc,
      strengths = #strengths dc}
  end

  fun parseConstructor s =
    case String.breakOn ":" s of
      (cname,":",csig) =>
          (case String.breakOn "->" csig of
            (inTyps,"->",outTyp) => CSpace.makeConstructor (cname, CSpace.makeCTyp (Parser.list Type.typeOfString inTyps, Type.typeOfString outTyp))
          | _ => raise ParseError ("bad signature for constructor: " ^ s)
          )
    | _ => raise ParseError ("badly specified constructor: " ^ s)


  fun addConSpec (r, tss) dc =
  let val (name,x,typeSystemN) = String.breakOn ":" r
      (*val _ = if x = ":" then () else raise ParseError "no type system specified for conSpec"*)
      val chars = List.concat (map String.explode tss)
      val crs = map parseConstructor (Parser.splitLevelWithSeparatorApply' (fn x => x) (fn x => x = #",") chars)
      val _ = Logging.write ("\nAdding constructors for constructor specification " ^ name ^ " of type system " ^ typeSystemN ^ "...\n")
      val _ = map ((fn x => Logging.write ("  " ^ x ^ "\n")) o CSpace.stringOfConstructor) crs
      val _ = Logging.write "...done\n"
      val cspec = {name = name, typeSystem = typeSystemN, constructors = FiniteSet.ofList crs}
  in {typeSystemsData = #typeSystemsData dc,
      conSpecs = cspec :: #conSpecs dc,
      knowledge = #knowledge dc,
      constructions = #constructions dc,
      transferRequests = #transferRequests dc,
      strengths = #strengths dc}
  end

  fun findConstructorInConSpec s cspec =
    valOf (CSpace.findConstructorWithName s cspec)
      handle Option => raise ParseError ("no constructor " ^ s ^ " in " ^ (#name cspec))

  fun tcpair s cspec =
    case String.breakOn "<-" (String.stripSpaces s) of
          (ts,_,cfgs) => {token = Parser.token ts, constructor = findConstructorInConSpec cfgs cspec}

  fun parseConstruction s cspec =
    let
      fun c tacc s' =
        case String.breakOn "[" s' of
          (ts,"",_) =>
            let val tok = Parser.token ts
            in if List.exists (CSpace.sameTokens tok) tacc
               then Construction.Reference tok
               else Construction.Source tok
            end
        | (tcps,_,ss) =>
            let val tcp = tcpair tcps cspec
                val tok = #token tcp
                val (xs,ys) = Parser.breakOnClosingDelimiter (#"[",#"]") ss
                val _ = if ys = [] then ()
                        else raise ParseError ("invalid input sequence to constructor: " ^ ss)
            in Construction.TCPair (tcp, Parser.splitLevelApply ((c (tok::tacc)) o String.removeParentheses) xs)
            end
    in Construction.fixReferences (c [] (String.stripSpaces s))
    end;

  fun addTransferSchema (nn,cs) dc =
  let val (name,x,cspecNs) = String.breakOn ":" nn
      val _ = if x = ":" then () else raise ParseError ("construction " ^ nn ^ " needs source and target cspecs")
      val (sourceCSpecN,y,targetCSpecN) = String.breakOn "," (String.removeParentheses cspecNs)
      val _ = if y = "," then () else raise ParseError ("construction " ^ nn ^ " needs source and target cspecs")
      val sourceCSpec = findConSpecWithName dc sourceCSpecN
      val sourceTySys = #typeSystem (findTypeSystemDataWithName dc (#typeSystem sourceCSpec))
      val targetCSpec = findConSpecWithName dc targetCSpecN
      val targetTySys = #typeSystem (findTypeSystemDataWithName dc (#typeSystem targetCSpec))
      val _ = Logging.write ("\nAdding tSchema " ^ name ^ "...")
      fun getPattern k [] = (Logging.write ("  ERROR: " ^ k ^ " pattern not specified");
                              raise ParseError ("no " ^ k ^ " in tSchema " ^ String.concat cs))
        | getPattern k ((x,ps) :: L) =
            if x = SOME k
            then parseConstruction (String.concat ps) (if k = sourceKW then sourceCSpec else targetCSpec)
            else getPattern k L
      fun getTokenRels [] = (Logging.write ("  ERROR: token relation not specified");
                              raise ParseError ("no token rels in tSchema " ^ String.concat cs))
        | getTokenRels ((x,trss) :: L) =
            if x = SOME antecedentKW
            then Parser.relaxedList Parser.relationship (String.concat trss)
            else getTokenRels L
      fun getConstructRel [] = (Logging.write ("  ERROR: construct relation not specified");
                                raise ParseError ("no construct rel in tSchema " ^ String.concat cs))
        | getConstructRel ((x,crs) :: L) =
            if x = SOME consequentKW
            then Parser.relationship (String.concat crs)
            else getConstructRel L
      fun parsePull s =
        (case String.breakOn " to " s of
          (Rs," to ",S) => (case String.breakOn " as " S of
                              (tks," as ",Rs') => (Parser.relation (String.stripSpaces Rs), Parser.relation (String.stripSpaces Rs'), Parser.list Parser.token (String.stripSpaces tks))
                            | _ => (Parser.relation (String.stripSpaces Rs), Parser.relation (String.stripSpaces Rs), Parser.list Parser.token (String.stripSpaces S)))
        | _ => raise ParseError ("badly specified pull list in tSchema " ^ s))
      fun getPullList [] = []
        | getPullList ((x,pl) :: L) =
            if x = SOME pullListKW
            then Parser.relaxedList parsePull (Parser.deTokenise " " pl)
            else getPullList L
      fun getStrength [] = (Logging.write ("  ERROR: strength not specified");
                            raise ParseError ("no strength in tSchema " ^ String.concat cs))
        | getStrength ((x,ss) :: L) =
            if x = SOME strengthKW
            then valOf (Real.fromString (String.concat ss)) handle Option => (Logging.write ("strength is not a real number in tSchema " ^ String.concat cs);raise Option)
            else getStrength L
      val blocks = contentForKeywords tSchemaKeywords cs
      val sPatt = getPattern sourceKW blocks
      val tPatt = getPattern targetKW blocks
      val _ = if Construction.wellFormed sourceTySys sPatt
              then Logging.write "\n  source pattern is well formed"
              else Logging.write "\n  WARNING: source pattern is not well formed"
      val _ = if Construction.wellFormed targetTySys tPatt
              then Logging.write "\n  target pattern is well formed\n"
              else Logging.write "\n  WARNING: target pattern is not well formed\n"
      val tsch = {name = name,
                  sourcePattern = sPatt,
                  targetPattern = tPatt,
                  antecedent = getTokenRels blocks,
                  consequent = getConstructRel blocks,
                  pullList = getPullList blocks}
      val strengthVal = getStrength blocks
      fun strengthsUpd c = if c = name then SOME strengthVal else (#strengths dc) c
      val _ = Logging.write ("done\n");
      fun ff (c,c') = Real.compare (valOf (strengthsUpd (TransferSchema.nameOf c')), valOf (strengthsUpd (TransferSchema.nameOf c)))
  in {typeSystemsData = #typeSystemsData dc,
      conSpecs = #conSpecs dc,
      knowledge = Knowledge.addTransferSchema (#knowledge dc) tsch strengthVal ff,
      constructions = #constructions dc,
      transferRequests = #transferRequests dc,
      strengths = strengthsUpd}
  end

  fun addConstruction (nn, cts) dc =
  let val (name,x,cspecN) = String.breakOn ":" nn
      val _ = if x = ":" then () else raise ParseError ("construction " ^ nn ^ " needs a cspec")
      val cspec = findConSpecWithName dc cspecN
      val ct = parseConstruction cts cspec
      val T = #typeSystem (findTypeSystemDataWithName dc (#typeSystem cspec))

      val _ = print ("\nChecking well-formedness of construction " ^ name ^ "...");
      val startTime = Time.now();
      val _ = if Construction.wellFormed  T ct then Logging.write ("\n  "^ name ^ " is well formed\n")
                else print ("\n  WARNING: "^ name ^" is not well formed\n")
      val endTime = Time.now();
      val runtime = Time.toMilliseconds endTime - Time.toMilliseconds startTime;
      val _ = print ("  well-formedness check runtime: "^ LargeInt.toString runtime ^ " ms \n...done\n  ");

      val ctRecord = {name = name, conSpec = cspecN, construction = ct}
  in {typeSystemsData = #typeSystemsData dc,
      conSpecs = #conSpecs dc,
      knowledge = #knowledge dc,
      constructions = ctRecord :: (#constructions dc),
      transferRequests = #transferRequests dc,
      strengths = #strengths dc}
  end

  fun addTransferRequests ws dc =
     {typeSystemsData = #typeSystemsData dc,
      conSpecs = #conSpecs dc,
      knowledge = #knowledge dc,
      constructions = #constructions dc,
      transferRequests = #transferRequests dc @ [ws],
      strengths = #strengths dc}

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
      val sourceConSpecN = #conSpec constructionRecord
      val sourceConSpec = findConSpecWithName DC sourceConSpecN
      val sourceTypeSystem = #typeSystem (findTypeSystemDataWithName DC (#typeSystem sourceConSpec))

      fun getTargetConSpec [] = sourceConSpec
        | getTargetConSpec ((x,c)::L) =
            if x = SOME targetConSpecKW
            then findConSpecWithName DC (String.concat c)
            else getTargetConSpec L
      fun getTargetTySys [] = sourceTypeSystem
        | getTargetTySys ((x,c)::L) =
            if x = SOME targetTypeSystemKW
            then #typeSystem (findTypeSystemDataWithName DC (String.concat c))
            else getTargetTySys L
      val targetTypeSystem = getTargetTySys C
      fun getGoal [] = raise ParseError "no goal for transfer"
        | getGoal ((x,c)::L) =
            if x = SOME goalKW
            then Parser.relationship (String.concat c)
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
            then (let val mtct = parseConstruction (String.concat c) (getTargetConSpec C)
                      (*val _ = if Construction.wellFormed targetTypeSystem mtct
                              then Logging.write "\n  pattern for matching is well formed"
                              else Logging.write "\n  WARNING: pattern for matching is not well formed"*)
                  in SOME mtct
                  end)
            else getMatchTarget L
      fun getIterative [] = false
        | getIterative ((x,_)::L) =
            if x = SOME iterativeKW
            then (case getMatchTarget C of NONE => true | _ => raise ParseError "iterative and matchTarget are incompatible")
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
      fun getCompsAndGoals [] = []
        | getCompsAndGoals (h::t) = (State.patternCompOf h, State.transferProofOf h, State.originalGoalOf h, State.goalsOf h) :: getCompsAndGoals t
      fun mkLatexGoals (goal,goals,tproof) =
        let val goalsS = if List.null goals then "NO\\ OPEN\\ GOALS!" else String.concatWith "\\\\ \n " (map Latex.relationship goals)
            val originalGoalS = Latex.relationship goal ^ "\\\\ \n"
            val IS = Heuristic.multiplicativeScore (strengthsOf DC) tproof
            val alignedGoals = "\n " ^ (Latex.environment "align*" "" ("\\mathbf{Original\\ goal}\\\\\n"
                                                                      ^ originalGoalS
                                                                      ^ "\\\\ \\mathbf{Open\\ goals}\\\\\n"
                                                                      ^ goalsS ^ "\\\\"
                                                                      ^ "\\\\ \\mathbf{transfer\\ score}\\\\\n"
                                                                      ^ Real.toString IS))
        in alignedGoals
        end
      fun mkLatexProof tproof =
        let val ct = TransferProof.toConstruction tproof;
        in Latex.construction (0.0,0.0) ct
        end
      fun mkLatexConstructions comp =
        let val constructions = Composition.resultingConstructions comp;
        in map (Latex.construction (0.0,0.0)) constructions
        end
      fun mkLatexConstructionsAndGoals (comp,tproof,goal,goals) =
        let val latexConstructions = mkLatexConstructions comp
            val _ = if Composition.wellFormedComposition targetTypeSystem comp
                    then ()
                    else print ("\nWARNING! some decomposition is not well formed!")
            val latexLeft = Latex.environment "minipage" "[t]{0.45\\linewidth}" (Latex.printWithHSpace 0.2 latexConstructions)
            val latexGoals = mkLatexGoals (goal,goals,tproof)
            val latexRight = Latex.environment "minipage" "[t]{0.35\\linewidth}" (latexGoals)
            val latexProof = ""(*mkLatexProof tproof*)
            val CSize = Composition.size comp
        in Latex.environment "center" "" (Latex.printWithHSpace 0.0 ([latexLeft,latexRight,Int.toString CSize, latexProof]))
        end
      val _ = print ("\nApplying structure transfer to "^ #name constructionRecord ^ "...");
      val startTime = Time.now();
      val results = Transfer.masterTransfer iterative unistructured targetPattern KB sourceTypeSystem targetTypeSystem construction goal;
      val nres = length (Seq.list_of results);
      val (listOfResults,_) = Seq.chop limit results;
      val endTime = Time.now();
      val runtime = Time.toMilliseconds endTime - Time.toMilliseconds startTime;
      val _ = print ("done\n" ^ "  runtime: "^ LargeInt.toString runtime ^ " ms \n");
      val _ = print ("  number of results: " ^ Int.toString nres ^ "\n");
      val compsAndGoals = getCompsAndGoals listOfResults;
      val transferProofs = map State.transferProofOf listOfResults
      val tproofConstruction = map (TransferProof.toConstruction o #2) compsAndGoals
      fun readTSchemaStrengths c = (strengthsOf DC) (CSpace.nameOfConstructor c)
      val E = Propagation.mkMultiplicativeISEvaluator readTSchemaStrengths
      val is = (Propagation.evaluate E) (hd tproofConstruction) handle Empty => (SOME 0.0)
      val is' = SOME (Heuristic.multiplicativeScore (strengthsOf DC) (hd transferProofs)) handle Empty => (SOME 0.0)
    (*  val _ = print (Construction.toString  (hd tproofConstruction))*)
      val _ = print ("  transfer score: " ^ Real.toString (valOf is') ^ "\n")
      val _ = print "\nComposing patterns and creating tikz figures...";
      val latexCompsAndGoals = Latex.printSubSections 1 (map mkLatexConstructionsAndGoals compsAndGoals);
      val latexCT = Latex.construction (0.0,0.0) construction;
      val _ = print "done\n";
      val _ = print "\nGenerating LaTeX document...";
      val latexOriginalConsAndGoals = Latex.environment "center" "" (latexCT);
      val outputFile = TextIO.openOut outputFilePath
      val opening = (Latex.sectionTitle false "Original construction") ^ "\n"
      val resultText = (Latex.sectionTitle false "Structure transfer results") ^ "\n"
      val _ = Latex.outputDocument outputFile (opening ^ latexOriginalConsAndGoals ^ "\n\n " ^ resultText ^ latexCompsAndGoals);
      val _ = TextIO.closeOut outputFile;
      val _ = print ("done!\n" ^ "  output file: "^outputFilePath^"\n\n");
  in ()
  end

  fun joinDocumentContents ({typeSystemsData = ts, conSpecs = sp, knowledge = kb, constructions = cs, transferRequests = tr, strengths = st} :: L) =
  (case joinDocumentContents L of {typeSystemsData = ts', conSpecs = sp', knowledge = kb', constructions = cs', transferRequests = tr', strengths = st'} =>
      {typeSystemsData = ts @ ts',
       conSpecs = sp @ sp',
       knowledge = Knowledge.join kb kb',
       constructions = cs @ cs',
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
              val (n,eq,ws) = breakOn "=" c
              (*val _ = if eq = "=" then () else raise ParseError (String.concat n)*)
          in if x = SOME typeSystemKW then addTypeSystem (hd n,ws) dc else
             if x = SOME conSpecKW then addConSpec (hd n, ws) dc else
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


(* TODO: a parser for propagator functions! figure out if you can export ML code from string! *)
end
