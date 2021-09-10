import "structure_transfer";
import "util.logging";
import "IO.latex";

Logging.enable ();

signature PARSER =
sig
  val list : (string -> 'a) -> string -> 'a list
  val finiteSet : (string -> ''a) -> string -> ''a FiniteSet.set
  val set : (string -> ''a) -> string -> ''a Set.set
  val typ : string -> Type.typ
  val token : string -> CSpace.token
  val ctyp : string -> (Type.typ list * Type.typ)
  val constructor : string -> CSpace.constructor
  val configurator : string -> CSpace.configurator
  val tcpair : string -> {token : CSpace.token, constructor : CSpace.constructor}
  val splitLevelWithSeparatorApply : (string -> 'a) -> char -> char list -> 'a list
  val splitLevelWithSeparatorApply' : (string -> 'a) -> (char -> bool) -> char list -> 'a list
  val splitLevel : char list -> string list
  val construction : string -> Construction.construction
  val finiteTypeSystem : string -> Type.typeSystem
  val pattern : string -> Pattern.construction
  val relation : string -> Relation.T
  val relationship : string -> Relation.relationship
  val correspondence : string -> Correspondence.corr
  type documentContent
  val joinDocumentContents : documentContent list -> documentContent
  val document : string -> documentContent
  val knowledgeOf : documentContent -> Knowledge.base
  val typeSystemsOf : documentContent -> Type.typeSystem list
  val constructionsOf : documentContent -> (string * Construction.construction) FiniteSet.set
  val transferRequestsOf : documentContent ->  (string list) list
  val findTypeSystemWithName : documentContent -> string -> Type.typeSystem
  val findConstructionWithName : documentContent -> string -> Construction.construction
  val findCorrespondenceWithName : documentContent -> string -> Correspondence.corr
  (*
  val knowledge : string -> Knowledge.base
  val state : string -> State.T*)
end;

structure Parser : PARSER =
struct
  exception ParseError of string;
  exception CodeError;

  fun breakOnClosingDelimiter (lD,rD) s =
    let
      fun bcb _ [] = raise ParseError s
        | bcb (p,s,c) (x::xs) =
            let val p' = if x = #"(" then p+1 else (if x = #")" then p-1 else p)
                val s' = if x = #"[" then s+1 else (if x = #"]" then s-1 else s)
                val c' = if x = #"{" then c+1 else (if x = #"}" then c-1 else c)
            in if (p',s',c') = (0,0,0)
               then ([],xs)
               else (case bcb (p',s',c') xs of (l1,l2) => (x::l1,l2))
            end
      val triple = if rD = #")" then (1,0,0)
                    else if rD = #"]" then (0,1,0)
                    else if rD = #"}" then (0,0,1)
                    else raise CodeError
    in bcb triple (String.explode s)
    end;
(*)
  fun breakOnClosingDelimiter (lD,rD) s =
    let
      fun bcb _ [] = raise ParseError
        | bcb n (x::xs) =
            let val m = if x = lD then n+1 else (if x = rD then n-1 else n)
            in if m = ~1 then ([],xs) else (case bcb m xs of (l1,l2) => (x::l1,l2))
            end
    in bcb 0 (String.explode s)
    end;*)

  fun splitLevel L =
    let
      fun sl _ [] = [[]]
        | sl (p,s,c) (x::xs) =
            let val p' = if x = #"(" then p+1 else (if x = #")" then p-1 else p)
                val s' = if x = #"[" then s+1 else (if x = #"]" then s-1 else s)
                val c' = if x = #"{" then c+1 else (if x = #"}" then c-1 else c)
                val slr = sl (p',s',c') xs
            in
              if (p',s',c') = (0,0,0) then if x = #"," then []::slr
                                            else (case slr of (L::LL) =>
                                                    (x::L) :: LL
                                                  | _ => raise CodeError)
              else (case slr of (L::LL) => (x::L) :: LL | _ => raise CodeError)
            end
    in List.map String.implode (sl (0,0,0) L)
    end;


  fun splitLevelWithSeparatorApply' f sep L =
    let
      fun sl _ [] = [[]]
        | sl (p,s,c) (x::xs) =
            let val p' = if x = #"(" then p+1 else (if x = #")" then p-1 else p)
                val s' = if x = #"[" then s+1 else (if x = #"]" then s-1 else s)
                val c' = if x = #"{" then c+1 else (if x = #"}" then c-1 else c)
                val slr = sl (p',s',c') xs
            in
              if (p',s',c') = (0,0,0) then if sep x then []::slr
                                            else (case slr of
                                                    (L::LL) => (x::L) :: LL
                                                  | _ => raise CodeError)
              else (case slr of (L::LL) => (x::L) :: LL | _ => raise CodeError)
            end
    in List.map (f o String.implode) (sl (0,0,0) L)
    end;

  fun splitLevelWithSeparatorApply f sep L =
    let
      fun sl _ [] = [[]]
        | sl (p,s,c) (x::xs) =
            let val p' = if x = #"(" then p+1 else (if x = #")" then p-1 else p)
                val s' = if x = #"[" then s+1 else (if x = #"]" then s-1 else s)
                val c' = if x = #"{" then c+1 else (if x = #"}" then c-1 else c)
                val slr = sl (p',s',c') xs
            in
              if (p',s',c') = (0,0,0) then if x = sep then []::slr
                                            else (case slr of
                                                    (L::LL) => (x::L) :: LL
                                                  | _ => raise CodeError)
              else (case slr of (L::LL) => (x::L) :: LL | _ => raise CodeError)
            end
    in List.map (f o String.implode) (sl (0,0,0) L)
    end;

  fun splitLevelApply f L = splitLevelWithSeparatorApply f #"," L;

  fun relaxedList f x = if x = "" then [] else (splitLevelApply f o String.explode) x
  fun list f x = if x = "[]" then [] else (splitLevelApply f o String.explode o String.removeSquareBrackets) x
  fun finiteSet f x = if x= "{}" then FiniteSet.empty else (FiniteSet.ofList o splitLevelApply f o String.explode o String.removeBraces) x
  fun set f x = if x= "{}" then Set.empty else (Set.ofList o splitLevelApply f o String.explode o String.removeBraces) x
  val typ = Type.typeOfString
  fun token s = case String.breakOn ":" (String.stripSpaces s) of
                  (ts,_,tys) => CSpace.makeToken ts (typ tys)
  fun ctyp s = case list typ (String.stripSpaces s) of
                  (ty::tys) => (tys,ty)
                | _ => raise ParseError ("bad constructor spec: " ^ s)
  fun constructor s = case String.breakOn ":" (String.stripSpaces s) of
                        (cs,_,ctys) => CSpace.makeConstructor (cs, ctyp ctys)
  fun configurator s = case String.breakOn ":" (String.stripSpaces s) of
                         (us,_,ccs) => CSpace.makeConfigurator (us, constructor ccs)
  fun tcpair s = case String.breakOn "<-" (String.stripSpaces s) of
                    (ts,_,cfgs) => {token = token ts, constructor = constructor cfgs}

  fun pair (f,g) s =
    case splitLevel (String.explode (String.removeParentheses s)) of
      [x,y] => (f x, g y)
    | _ => raise ParseError (s ^ " not a pair")

  fun boolean s = if s = "true" then true
                  else if s = "false" then false
                       else raise ParseError (s ^ " not boolean")

  exception undefined
  fun functionFromPairs (f,g) eq (s::ss) x =
        (case pair (f,g) s of (a,b) => if eq x a then b else functionFromPairs (f,g) eq ss x)
    | functionFromPairs (f,g) eq [] x = raise undefined

  fun boolfun eq f s x = (List.exists (eq x) o splitLevelApply f o String.explode o String.removeBraces) s
  fun finiteTypeSystem s =
    let val s' = String.stripSpaces s
        val L = if String.isPrefix "(" s'
                then String.explode (String.removeParentheses s')
                else raise ParseError (s ^ " not a type system")
        val (name,Tys,subTys) = (case splitLevel L of
                                  [w,x,y] => (w,x,y)
                                | _ => raise ParseError (s ^ " not a type system"))
        val finTy = finiteSet typ Tys
        val Ty = set typ Tys
        fun eq (x,y) (x',y') = Type.equal x x' andalso Type.equal y y'
        val subType' = boolfun eq (pair (typ,typ)) subTys
        val {subType,...} = Type.fixFiniteSubTypeFunction {name = name, Ty = finTy, subType = subType'}
    in {name = name, Ty = Ty, subType = subType}
    end;

  fun construction s =
    let
      fun c tacc s' =
        case String.breakOn "<-[" (String.removeParentheses s') of
          (ts,"",_) =>
            let val tok = token ts
            in if List.exists (CSpace.sameTokens tok) tacc
               then Construction.Loop tok
               else Construction.Source tok
            end
        | (tcps,_,ss) =>
            let val tcp = tcpair tcps
                val tok = #token tcp
                val (xs,ys) = breakOnClosingDelimiter (#"[",#"]") ss
                val _ = if ys = [] then ()
                        else raise ParseError ("invalid input sequence to constructor: " ^ ss)
            in Construction.TCPair (tcp, splitLevelApply ((c (tok::tacc)) o String.removeParentheses) xs)
            end
    in c [] (String.stripSpaces s)
    end;
  fun pattern s = construction s;

  fun relation s = Relation.make s
  fun relationship s =
    let val (ss,sep,Rs) = String.breakOn "::" (String.stripSpaces s)
        val _ = if sep = "::" then () else raise ParseError ("missing :: in relation expression: " ^ s)
        val (xs,ys) = (case splitLevel (String.explode (String.removeParentheses ss)) of
                          [x,y] => (x,y)
                        | _ => raise ParseError ("non-binary relation expression: " ^ s))
    in Relation.makeRelationship (list token xs,list token ys,relation Rs)
    end

  fun correspondence s =
    let val ss = String.removeParentheses (String.stripSpaces s)
        val (n,sPs,tPs,fRss,cRs) =
              (case splitLevel (String.explode ss) of
                  [v,w,x,y,z] => (v,w,x,y,z)
                  | _ => raise ParseError ("invalid correspondence expression: " ^ s))
        val sP = pattern sPs
        val tP = pattern tPs
        val fRs = list relationship fRss
        val cR = relationship cRs
        val corr = {name = n,
                    sourcePattern = sP,
                    targetPattern = tP,
                    tokenRels = fRs,
                    constructRel = cR}
    in Correspondence.declareCorrespondence corr
    end

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

  val bigKeywords = ["import","typeSystem","correspondence","construction","transfer","comment"]
  val typeKeywords = ["types","order"]
  val corrKeywords = ["target","source","tokenRels","constructRel"]
  val transferKeywords = ["sourceTypeSystem","targetTypeSystem","sourceConstruction","goal","output","limit"]

  type documentContent = {typeSystems : Type.typeSystem list,
                          knowledge : Knowledge.base,
                          constructions : (string * Construction.construction) FiniteSet.set,
                          transferRequests : (string list) list}
  val emptyDocContent = {typeSystems = [],
                         knowledge = Knowledge.empty,
                         constructions = FiniteSet.empty,
                         transferRequests = []}

  val typeSystemsOf = #typeSystems
  val knowledgeOf = #knowledge
  val constructionsOf = #constructions
  val transferRequestsOf = #transferRequests

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
              then relationship (String.concat c)
              else getGoal L
        fun getOutput [] = raise ParseError "no output file name for transfer"
          | getOutput ((x,c)::L) =
              if x = SOME "output"
              then "tests/latex/"^(String.concat c)^".tex"
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
        val _ = Logging.write ("Applying structure transfer...");
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
              val latexProof = mkLatexProof tproof
              val latexGoals = mkLatexGoals (goal,goals)
          in Latex.environment "center" "" (Latex.printWithHSpace 0.5 (latexConstructions @ [latexProof,latexGoals]))
          end
        val nres = length (Seq.list_of results);
        val _ = Logging.write ("  number of results: " ^ Int.toString nres ^ "\n");
        val (listOfResults,_) = Seq.chop limit results;
        val compsAndGoals = getCompsAndGoals listOfResults;
        val _ = Logging.write "Composing patterns and creating tikz figures...";
        val latexCompsAndGoals = Latex.printSubSections 1 (map mkLatexConstructionsAndGoals compsAndGoals);
        val latexCT = Latex.construction (0.0,0.0) construction;
        val _ = Logging.write "done\n";
        val _ = Logging.write "Generating LaTeX document...";
        val latexOriginalConsAndGoals = Latex.environment "center" "" (latexCT);
        val outputFile = TextIO.openOut outputFilePath
        val opening = (Latex.sectionTitle false "Original construction") ^ "\n"
        val resultText = (Latex.sectionTitle false "Structure transfer results") ^ "\n"
        val _ = Latex.outputDocument outputFile (opening ^ latexOriginalConsAndGoals ^ "\n\n " ^ resultText ^ latexCompsAndGoals);
        val _ = TextIO.closeOut outputFile;
        val _ = Logging.write ("done!\n" ^ "  output file: "^outputFilePath^"\n");
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
              then map typ (String.tokens (fn x => x = #"\n" orelse x = #",") (String.concat c))
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
        transferRequests = #transferRequests dc}
    end

  fun addCorrespondence (name,cs) dc =
    let val blocks = contentForKeywords corrKeywords cs
        fun getPattern k [] = raise ParseError ("no " ^ k ^ " in correspondence " ^ String.concat cs)
          | getPattern k ((x,ps) :: L) =
              if x = SOME k
              then pattern (String.concat ps)
              else getPattern k L
        fun getTokenRels [] = raise ParseError ("no token rels in correspondence " ^ String.concat cs)
          | getTokenRels ((x,trss) :: L) =
              if x = SOME "tokenRels"
              then relaxedList relationship (String.concat trss)
              else getTokenRels L
        fun getConstructRel [] = raise ParseError ("no construct rel in correspondence " ^ String.concat cs)
          | getConstructRel ((x,crs) :: L) =
              if x = SOME "constructRel"
              then relationship (String.concat crs)
              else getConstructRel L
        val corr = {name = name,
                    sourcePattern = getPattern "source" blocks,
                    targetPattern = getPattern "target" blocks,
                    tokenRels = getTokenRels blocks,
                    constructRel = getConstructRel blocks}
    in {typeSystems = #typeSystems dc,
        knowledge = Knowledge.addCorrespondence (#knowledge dc) corr,
        constructions = #constructions dc,
        transferRequests = #transferRequests dc}
    end

  fun addConstruction (name, cts) dc =
    let val ct = construction cts
    in {typeSystems = #typeSystems dc,
        knowledge = #knowledge dc,
        constructions = FiniteSet.insert (name,ct) (#constructions dc),
        transferRequests = #transferRequests dc}
    end

  fun joinDocumentContents ({typeSystems = ts, knowledge = kb, constructions = cs, transferRequests = tr} :: L) =
    (case joinDocumentContents L of {typeSystems = ts', knowledge = kb', constructions = cs', transferRequests = tr'} =>
        {typeSystems = ts @ ts',
         knowledge = Knowledge.join kb kb',
         constructions = FiniteSet.union cs cs',
         transferRequests = tr @ tr'})
    | joinDocumentContents [] =
        {typeSystems = [],
         knowledge = Knowledge.empty,
         constructions = FiniteSet.empty,
         transferRequests = []}

  fun addTransferRequests ws dc =
     {typeSystems = #typeSystems dc,
      knowledge = #knowledge dc,
      constructions = #constructions dc,
      transferRequests = ws :: #transferRequests dc}

  fun document filename =
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
        val importedContents = map (document o String.concat o #2) importFilenames
        val allContent = joinDocumentContents (C::importedContents)
        val _ = map (parseTransfer allContent) (#transferRequests allContent)
    in allContent
    end


  (* TODO: a parser for propagator functions! figure out if you can export ML code from string! *)
end;
