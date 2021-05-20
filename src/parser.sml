import "structure_transfer";

signature PARSER =
sig
  val list : (string -> 'a) -> string -> 'a list
  val finiteSet : (string -> ''a) -> string -> ''a FiniteSet.set
  val set : (string -> ''a) -> string -> ''a Set.set
  val typ : string -> TypeSystem.typ
  val token : string -> CSpace.token
  val ctyp : string -> (TypeSystem.typ list * TypeSystem.typ)
  val constructor : string -> CSpace.constructor
  val configurator : string -> CSpace.configurator
  val tcpair : string -> {token : CSpace.token, configurator : CSpace.configurator}
  val splitLevel : char list -> string list
  val construction : string -> Construction.construction
  val finiteTypeSystem : string -> TypeSystem.typeSystem
  val pattern : string -> Pattern.construction
  val relation : string -> Relation.T
  val relationship : string -> Relation.relationship
  val correspondence : string -> Correspondence.corr
  (*
  val knowledge : string -> Knowledge.base
  val state : string -> State.T*)
end;

structure Parser : PARSER =
struct
  exception ParseError;

  fun breakOnClosingDelimiter (lD,rD) s =
    let
      fun bcb _ [] = raise ParseError
        | bcb (p,s,c) (x::xs) =
            let val p' = if x = #"(" then p+1 else (if x = #")" then p-1 else p)
                val s' = if x = #"[" then s+1 else (if x = #"]" then s-1 else s)
                val c' = if x = #"{" then c+1 else (if x = #"}" then c-1 else c)
            in if (p',s',c') = (0,0,0) then ([],xs) else (case bcb (p',s',c') xs of (l1,l2) => (x::l1,l2))
            end
      val triple = if rD = #")" then (1,0,0)
                    else if rD = #"]" then (0,1,0)
                    else if rD = #"}" then (0,0,1)
                    else raise ParseError
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
                                            else (case slr of (L::LL) => (x::L) :: LL)
              else (case slr of (L::LL) => (x::L) :: LL)
            end
    in List.map String.implode (sl (0,0,0) L)
    end;


  fun splitLevelApply f L =
    let
      fun sl _ [] = [[]]
        | sl (p,s,c) (x::xs) =
            let val p' = if x = #"(" then p+1 else (if x = #")" then p-1 else p)
                val s' = if x = #"[" then s+1 else (if x = #"]" then s-1 else s)
                val c' = if x = #"{" then c+1 else (if x = #"}" then c-1 else c)
                val slr = sl (p',s',c') xs
            in
              if (p',s',c') = (0,0,0) then if x = #"," then []::slr
                                            else (case slr of (L::LL) => (x::L) :: LL)
              else (case slr of (L::LL) => (x::L) :: LL)
            end
    in List.map (f o String.implode) (sl (0,0,0) L)
    end;

  fun list f s = (splitLevelApply f (String.explode (String.removeSquareBrackets s)))
  fun finiteSet f s = FiniteSet.ofList (splitLevelApply f (String.explode (String.removeBraces s)))
  fun set f s = Set.ofList (String.splitStripApply f "," ( String.removeBraces s))
  fun boolfun eq f s x = List.exists (eq x) (List.map f (splitLevel (String.explode (String.removeBraces s))))
  fun typ s = TypeSystem.typeOfString s
  fun token s = case String.breakOn ":" (String.stripSpaces s) of (ts,_,tys) => CSpace.makeToken ts (typ tys)
  fun ctyp s = let val (ty::tys) = rev (list typ (String.stripSpaces s)) in (rev tys,ty) end (*case String.breakOn "->" (String.stripSpaces s) of (tyss,_,tys) => (list typ tyss, typ tys)*)
  fun constructor s = case String.breakOn ":" (String.stripSpaces s) of (cs,_,ctys) => CSpace.makeConstructor (cs, ctyp ctys)
  fun configurator s = case String.breakOn ":" (String.stripSpaces s) of (us,_,ccs) => CSpace.makeConfigurator (us, constructor ccs)
  fun tcpair s = case String.breakOn "<-" (String.stripSpaces s) of (ts,_,cfgs) => {token = token ts, configurator = configurator cfgs}

  fun pair (f,g) s =
    let val [x,y] = splitLevel (String.explode (String.removeParens s))
    in (f x, g y)
    end

  fun boolean s = if s = "true" then true else if s = "false" then false else raise ParseError

  exception undefined
  fun functionFromPairs (f,g) eq (s::ss) x =
        (case pair (f,g) s of (a,b) => if eq x a then b else functionFromPairs (f,g) eq ss x)
    | functionFromPairs (f,g) eq [] x = raise undefined

  fun finiteTypeSystem s =
    let val s' = String.stripSpaces s
        val L = if String.isPrefix "(" s' then String.explode (String.removeParens s') else raise ParseError
        val [Tys,subTys] = splitLevel L
        val finTy = finiteSet typ Tys
        val Ty = set typ Tys
        fun eq (x,y) (x',y') = TypeSystem.equal x x' andalso TypeSystem.equal y y'
        val subType' = boolfun eq (pair (typ,typ)) subTys
        val {subType,...} = TypeSystem.fixFiniteSubTypeFunction {Ty = finTy, subType = subType'}
    in {Ty = Ty, subType = subType} handle Bind => raise ParseError
    end;

  fun construction s =
    let
      fun c tacc s' =
        case String.breakOn "<-[" (String.removeParens s') of
          (ts,"",_) =>
            let val tok = token ts
            in if List.exists (CSpace.sameTokens tok) tacc then Construction.Loop tok
               else Construction.Source tok
            end
        | (tcps,_,ss) =>
            let val tcp = tcpair tcps
                val tok = #token tcp
                val (xs,[]) = breakOnClosingDelimiter (#"[",#"]") ss
            in Construction.TCPair (tcp, map ((c (tok::tacc)) o String.removeParens) (splitLevel xs))
            end
    in c [] (String.stripSpaces s) handle Bind => raise ParseError
    end;
  fun pattern s = construction s;

  fun relation s = Relation.make s
  fun relationship s =
    let val (ss,_,Rs) = String.breakOn "::" (String.stripSpaces s)
        val [xs,ys] = splitLevel (String.explode (String.removeParens ss))
    in Relation.makeRelationship (list token xs,list token ys,relation Rs)
        handle Bind => raise ParseError
    end

  fun correspondence s =
    let val ss = String.removeParens (String.stripSpaces s)
        val [sPs,tPs,fRss,cRs] = splitLevel (String.explode ss)
        val sP = pattern sPs
        val tP = pattern tPs
        val fRs = list relationship fRss
        val cR = relationship cRs
        val corr = {sourcePattern = sP,
                    targetPattern = tP,
                    foundationRels = fRs,
                    constructRel = cR}
    in Correspondence.declareCorrespondence corr
    end
end;
