import "structure_transfer";

signature PARSE =
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
  val construction : string -> Construction.construction
  (*val pattern : string -> Pattern.construction
  val relation : string -> Relation.T
  val relationship : string -> Relation.relationship
  val correspondence : string -> Correspondence.corr
  val knowledge : string -> Knowledge.base
  val state : string -> State.T*)
end;

structure Parse : PARSE =
struct
  fun list f s = String.splitStripApply f "," (String.removeSquareBrackets s)
  fun finiteSet f s = FiniteSet.ofList (String.splitStripApply f "," (String.removeBraces s))
  fun set f s = Set.ofList (String.splitStripApply f "," ( String.removeBraces s))
  fun typ s = TypeSystem.typeOfString s
  fun token s = case String.breakOn ":" (String.stripSpaces s) of (ts,_,tys) => CSpace.makeToken ts (typ tys)
  fun ctyp s = let val (ty::tys) = rev (list typ (String.stripSpaces s)) in (rev tys,ty) end (*case String.breakOn "->" (String.stripSpaces s) of (tyss,_,tys) => (list typ tyss, typ tys)*)
  fun constructor s = case String.breakOn ":" (String.stripSpaces s) of (cs,_,ctys) => CSpace.makeConstructor (cs, ctyp ctys)
  fun configurator s = case String.breakOn ":" (String.stripSpaces s) of (us,_,ccs) => CSpace.makeConfigurator (us, constructor ccs)
  fun tcpair s = case String.breakOn "<-" (String.stripSpaces s) of (ts,_,cfgs) => {token = token ts, configurator = configurator cfgs}


  datatype parsetree = Node of string * parsetree list | Leaf of string

  exception ParseError;

  fun breakOnClosingBracket L =
    let
      fun bcb _ [] = raise ParseError
        | bcb n (x::xs) =
            let val m = if x = #"(" then n+1 else (if x = #")" then n-1 else n)
            in if m = ~1 then ([],xs) else (case bcb m xs of (l1,l2) => (x::l1,l2))
            end
    in bcb 0 L
    end;

  fun splitLevel L =
    let
      fun sl _ [] = [[]]
        | sl n (x::xs) =
        let val m = if x = #"(" then n+1 else (if x = #")" then n-1 else n)
        in
          if n = 0 then if x = #"," then []::sl m xs
                        else (case sl m xs of (L::LL) => (x::L) :: LL)
          else (case sl m xs of (L::LL) => (x::L) :: LL)
        end
    in List.map String.implode (sl 0 L)
    end;


  fun construction s =
    let
      fun c tacc s' =
        case String.breakOn "<-(" (String.stripSpaces s') of
          (ts,"",_) => let val tok = token ts in if List.exists (CSpace.sameTokens tok) tacc then Construction.Loop tok else Construction.Source tok end
        | (tcps,_,ss) => let val tcp = tcpair tcps val tok = #token tcp val (xs,ys) = breakOnClosingBracket (String.explode ss) in Construction.TCPair (tcp, map (c (tok::tacc)) (splitLevel xs)) end
    in c [] s
    end;

end;
