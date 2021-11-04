import "transfer.structure_transfer";
import "util.logging";
import "transfer.propagation";

Logging.enable ();

signature PARSER =
sig
  val ParseError : string -> exn;
  val breakOnClosingDelimiter : (char * char) -> string -> (char list * char list)
  val list : (string -> 'a) -> string -> 'a list
  val relaxedList : (string -> 'a) -> string -> 'a list
  val finiteSet : (string -> ''a) -> string -> ''a FiniteSet.set
  val set : (string -> ''a) -> string -> ''a Set.set
  val typ : string -> Type.typ
  val token : string -> CSpace.token
  val ctyp : string -> (Type.typ list * Type.typ)
  val constructor : string -> CSpace.constructor
  val configurator : string -> CSpace.configurator
  val tcpair : string -> {token : CSpace.token, constructor : CSpace.constructor}
  val splitLevelApply : (string -> 'a) -> char list -> 'a list
  val splitLevelWithSeparatorApply : (string -> 'a) -> char -> char list -> 'a list
  val splitLevelWithSeparatorApply' : (string -> 'a) -> (char -> bool) -> char list -> 'a list
  val splitLevel : char list -> string list
  val construction : string -> Construction.construction
(*)  val finiteTypeSystem : string -> Type.typeSystem*)
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
  (*
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
    end;*)

  fun construction s =
    let
      fun c tacc s' =
        case String.breakOn "<-[" (String.removeParentheses s') of
          (ts,"",_) =>
            let val tok = token ts
            in if List.exists (CSpace.sameTokens tok) tacc
               then Construction.Reference tok
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
    in Construction.fixReferences (c [] (String.stripSpaces s))
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
end;
