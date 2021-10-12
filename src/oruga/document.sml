import "oruga.parser";

signature DOCUMENT =
sig
  type documentContent
  val joinDocumentContents : documentContent list -> documentContent
  val read : string -> documentContent
  val knowledgeOf : documentContent -> Knowledge.base
  val typeSystemsOf : documentContent -> Type.typeSystem list
  val constructionsOf : documentContent -> (string * Construction.construction) FiniteSet.set
  val transferRequestsOf : documentContent ->  (string list) list
  val findTypeSystemWithName : documentContent -> string -> Type.typeSystem
  val findConstructionWithName : documentContent -> string -> Construction.construction
  val findCorrespondenceWithName : documentContent -> string -> Correspondence.corr

end

structure Document : DOCUMENT =
struct

  val ParseError = Parser.ParseError;

  val bigKeywords = ["import","typeSystem","correspondence","construction","transfer","comment"]
  val typeKeywords = ["types","order"]
  val corrKeywords = ["target","source","tokenRels","constructRel","strength"]
  val transferKeywords = ["sourceTypeSystem","targetTypeSystem","sourceConstruction","goal","output","limit","IS"]


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

  type documentContent = {typeSystems : Type.typeSystem list,
                        knowledge : Knowledge.base,
                        constructions : (string * Construction.construction) FiniteSet.set,
                        transferRequests : (string list) list,
                        strengths : string -> real option}
  val emptyDocContent = {typeSystems = [],
                       knowledge = Knowledge.empty,
                       constructions = FiniteSet.empty,
                       transferRequests = [],
                       strengths = (fn _ => NONE)}

  val typeSystemsOf = #typeSystems
  val knowledgeOf = #knowledge
  val constructionsOf = #constructions
  val transferRequestsOf = #transferRequests
  val strengthsOf = #strengths

  fun findTypeSystemWithName DC n =
  valOf (List.find (fn x => #name x = n) (typeSystemsOf DC))
  fun findConstructionWithName DC n =
  (#2 o valOf) (FiniteSet.find (fn x => #1 x = n) (constructionsOf DC))
  fun findCorrespondenceWithName DC n =
  valOf (Knowledge.findCorrespondenceWithName (knowledgeOf DC) n)

  fun parseTransfer DC ws =
  let fun stringifyC ((x,c)::L) = "("^(valOf x)^","^ (String.stringOfList (fn x => x) c)^") : "^(stringifyC L)
        | stringifyC [] = ""
      val C = contentForKeywords transferKeywords ws
      fun getSourceTySys [] = raise ParseError "no source type system for transfer"
        | getSourceTySys ((x,c)::L) =
            if x = SOME "sourceTypeSystem"
            then findTypeSystemWithName DC (String.concat c)
            else getSourceTySys L
      fun getTargetTySys [] = raise ParseError "no target type system for transfer"
        | getTargetTySys ((x,c)::L) =
            if x = SOME "targetTypeSystem"
            then findTypeSystemWithName DC (String.concat c)
            else getTargetTySys L
      fun getConstruction [] = raise ParseError "no construction to transfer"
        | getConstruction ((x,c)::L) =
            if x = SOME "sourceConstruction"
            then findConstructionWithName DC (String.concat c)
            else getConstruction L
      fun getGoal [] = raise ParseError "no goal for transfer"
        | getGoal ((x,c)::L) =
            if x = SOME "goal"
            then Parser.relationship (String.concat c)
            else getGoal L
      fun getOutput [] = raise ParseError "no output file name for transfer"
        | getOutput ((x,c)::L) =
            if x = SOME "output"
            then "output/latex/"^(String.concat c)^".tex"
            else getOutput L
      fun getLimit [] = raise ParseError "no limit for transfer output file"
        | getLimit ((x,c)::L) =
            if x = SOME "limit"
            then valOf (Int.fromString (String.concat c)) handle Option => raise ParseError "limit needs an integer!"
            else getLimit L
      val sourceTypeSystem = getSourceTySys C  handle Match => (print "sourceTS!";raise Match)
      val targetTypeSystem = getTargetTySys C  handle Match => (print ("targetTS! " ^ (stringifyC C));raise Match)
      val construction = getConstruction C  handle Match => (print "sourceConstruction!";raise Match)
      val goal = getGoal C
      val outputFilePath = getOutput C  handle Match => (print ("output!" ^ (stringifyC C)) ;raise Match)
      val limit = getLimit C  handle Match => (print "limit!";raise Match)
      val KB = knowledgeOf DC
      val _ = Logging.write ("\nApplying structure transfer...");
      val startTime = Time.now();
      val results = Transfer.structureTransfer KB sourceTypeSystem targetTypeSystem construction goal 1000;
      val endTime = Time.now();
      val runtime = Time.toMilliseconds endTime - Time.toMilliseconds startTime;
      val _ = Logging.write ("done\n" ^ "  runtime: "^ LargeInt.toString runtime ^ " ms \n");
      fun getCompsAndGoals [] = []
        | getCompsAndGoals (h::t) = (State.patternCompOf h, State.transferProofOf h, State.originalGoalOf h, State.goalsOf h) :: getCompsAndGoals t
      fun mkLatexGoals (goal,goals) =
        let val goalsS = if List.null goals then "NO\\ OPEN\\ GOALS!" else String.concatWith "\\\\ \n " (map Latex.relationship goals)
            val originalGoalS = Latex.relationship goal ^ "\\\\ \n"
            val alignedGoals = "\n " ^ (Latex.environment "align*" "" ("\\mathbf{Original\\ goal}\\\\\n"^originalGoalS^"\\\\ \\mathbf{Open\\ goals}\\\\\n"^goalsS))
        in Latex.environment "minipage" "[t]{0.25\\textwidth}" alignedGoals
        end
      fun mkLatexProof tproof =
        let val construction = TransferProof.toConstruction tproof;
        in Latex.construction (0.0,0.0) construction
        end
      fun mkLatexConstructions comp =
        let val constructions = Composition.resultingConstructions comp;
        in map (Latex.construction (0.0,0.0)) constructions
        end
      fun mkLatexConstructionsAndGoals (comp,tproof,goal,goals) =
        let val latexConstructions = mkLatexConstructions comp
          (*)  val latexProof = mkLatexProof tproof*)
            val latexGoals = mkLatexGoals (goal,goals)
        in Latex.environment "center" "" (Latex.printWithHSpace 0.5 (latexConstructions @ [(*latexProof,*)latexGoals]))
        end
      val nres = length (Seq.list_of results);
      val _ = Logging.write ("  number of results: " ^ Int.toString nres ^ "\n");
      val (listOfResults,_) = Seq.chop limit results;
      val compsAndGoals = getCompsAndGoals listOfResults;
      val transferProofs = map State.transferProofOf listOfResults
      val tproofConstruction = map (TransferProof.toConstruction o #2) compsAndGoals
      fun readCorrStrengths c = (strengthsOf DC) (CSpace.nameOfConstructor c)
      val E = Propagation.mkMultiplicativeISEvaluator readCorrStrengths
      val is = (Propagation.evaluate E) (hd tproofConstruction)
      val is' = SOME (TransferProof.multiplicativeIS (strengthsOf DC) (hd transferProofs))
    (*  val _ = Logging.write (Construction.toString  (hd tproofConstruction))*)
      val _ = Logging.write ("  informational suitability score: " ^ Real.toString (valOf is') ^ "\n")
      val _ = Logging.write "\nComposing patterns and creating tikz figures...";
      val latexCompsAndGoals = Latex.printSubSections 1 (map mkLatexConstructionsAndGoals compsAndGoals);
      val latexCT = Latex.construction (0.0,0.0) construction;
      val _ = Logging.write "done\n";
      val _ = Logging.write "\nGenerating LaTeX document...";
      val latexOriginalConsAndGoals = Latex.environment "center" "" (latexCT);
      val outputFile = TextIO.openOut outputFilePath
      val opening = (Latex.sectionTitle false "Original construction") ^ "\n"
      val resultText = (Latex.sectionTitle false "Structure transfer results") ^ "\n"
      val _ = Latex.outputDocument outputFile (opening ^ latexOriginalConsAndGoals ^ "\n\n " ^ resultText ^ latexCompsAndGoals);
      val _ = TextIO.closeOut outputFile;
      val _ = Logging.write ("done!\n" ^ "  output file: "^outputFilePath^"\n\n");
  in ()
  end

  fun inequality s =
    (case String.breakOn "<" s of
        (x,"<",y) => (x,y)
      | (x,">",y) => (y,x)
      | _ => raise ParseError s)

  fun addTypeSystem (name, tss) dc =
  let val blocks = contentForKeywords typeKeywords tss
      fun getTyps [] = []
        | getTyps ((x,c)::L) =
            if x = SOME "types"
            then map Parser.typ (String.tokens (fn x => x = #"\n" orelse x = #",") (String.concat c))
            else getTyps L
      fun getOrder [] = []
        | getOrder ((x,c)::L) =
            if x = SOME "order"
            then map inequality (String.tokens (fn x => x = #"\n" orelse x = #",") (String.concat c))
            else getOrder L
      val ordList = getOrder blocks
      val TyList = getTyps blocks
      val finTy = FiniteSet.ofList TyList
      val Ty = Set.ofList TyList
      fun eq (x,y) (x',y') = Type.equal x x' andalso Type.equal y y'
      fun subType' x = List.exists (eq x) ordList
      val {subType,...} = Type.fixFiniteSubTypeFunction {name = name, Ty = finTy, subType = subType'}
      val typSys = {name = name, Ty = Ty, subType = subType}
  in {typeSystems = typSys :: (#typeSystems dc),
      knowledge = #knowledge dc,
      constructions = #constructions dc,
      transferRequests = #transferRequests dc,
      strengths = #strengths dc}
  end

  fun addCorrespondence (name,cs) dc =
  let val blocks = contentForKeywords corrKeywords cs
      fun getPattern k [] = raise ParseError ("no " ^ k ^ " in correspondence " ^ String.concat cs)
        | getPattern k ((x,ps) :: L) =
            if x = SOME k
            then Parser.pattern (String.concat ps)
            else getPattern k L
      fun getTokenRels [] = raise ParseError ("no token rels in correspondence " ^ String.concat cs)
        | getTokenRels ((x,trss) :: L) =
            if x = SOME "tokenRels"
            then Parser.relaxedList Parser.relationship (String.concat trss)
            else getTokenRels L
      fun getConstructRel [] = raise ParseError ("no construct rel in correspondence " ^ String.concat cs)
        | getConstructRel ((x,crs) :: L) =
            if x = SOME "constructRel"
            then Parser.relationship (String.concat crs)
            else getConstructRel L
      fun getStrength [] = raise ParseError ("no construct rel in correspondence " ^ String.concat cs)
        | getStrength ((x,ss) :: L) =
            if x = SOME "strength"
            then Real.fromString (String.concat ss)
            else getStrength L
      val corr = {name = name,
                  sourcePattern = getPattern "source" blocks,
                  targetPattern = getPattern "target" blocks,
                  tokenRels = getTokenRels blocks,
                  constructRel = getConstructRel blocks}
      fun strengthsUpd c = if c = name then getStrength blocks else (#strengths dc) c
  in {typeSystems = #typeSystems dc,
      knowledge = Knowledge.addCorrespondence (#knowledge dc) corr,
      constructions = #constructions dc,
      transferRequests = #transferRequests dc,
      strengths = strengthsUpd}
  end

  fun addConstruction (name, cts) dc =
  let val ct = Parser.construction cts
  in {typeSystems = #typeSystems dc,
      knowledge = #knowledge dc,
      constructions = FiniteSet.insert (name,ct) (#constructions dc),
      transferRequests = #transferRequests dc,
      strengths = #strengths dc}
  end

  fun joinDocumentContents ({typeSystems = ts, knowledge = kb, constructions = cs, transferRequests = tr, strengths = st} :: L) =
  (case joinDocumentContents L of {typeSystems = ts', knowledge = kb', constructions = cs', transferRequests = tr', strengths = st'} =>
      {typeSystems = ts @ ts',
       knowledge = Knowledge.join kb kb',
       constructions = FiniteSet.union cs cs',
       transferRequests = tr @ tr',
       strengths = (fn c => case st c of SOME f => SOME f | NONE => st' c)})
  | joinDocumentContents [] = emptyDocContent

  fun addTransferRequests ws dc =
   {typeSystems = #typeSystems dc,
    knowledge = #knowledge dc,
    constructions = #constructions dc,
    transferRequests = ws :: #transferRequests dc,
    strengths = #strengths dc}

  fun read filename =
  let val file = TextIO.openIn ("descriptions/"^filename)
      val s = TextIO.inputAll file
      val _ = TextIO.closeIn file
      val words = String.tokens (fn x => x = #"\n" orelse x = #" ") s
      val blocks = contentForKeywords bigKeywords words
      val nonImported = List.filter (fn (x,_) => x <> SOME "import") blocks
      fun distribute [] = emptyDocContent
        | distribute ((x,c)::L) =
          let val dc = distribute L
              val (n,eq,ws) = breakOn "=" c
              (*val _ = if eq = "=" then () else raise ParseError (String.concat n)*)
          in (case x of
                SOME "typeSystem" => addTypeSystem (hd n,ws) dc
              | SOME "correspondence" => addCorrespondence (hd n,ws) dc
              | SOME "construction" => addConstruction (hd n,String.concat ws) dc
              | SOME "transfer" => addTransferRequests c dc
              | SOME "comment" => dc
              | _ => dc)
          end handle Bind => raise ParseError "expected name = content, found multiple words before ="

      val C = distribute nonImported
      val importFilenames = List.filter (fn (x,_) => x = SOME "import") blocks
      val importedContents = map (read o String.concat o #2) importFilenames
      val allContent = joinDocumentContents (C::importedContents)
      val _ = map (parseTransfer allContent) (#transferRequests allContent)
  in allContent
  end


(* TODO: a parser for propagator functions! figure out if you can export ML code from string! *)
end
