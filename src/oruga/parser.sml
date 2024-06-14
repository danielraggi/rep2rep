import "core.graph";
import "util.logging";

Logging.enable ();

signature PARSER =
sig
  val ParseError : string -> exn;
  val breakOnClosingDelimiter : (char * char) -> string -> (char list * char list)
  val list : (string -> 'a) -> string -> 'a list
  val relaxedList : (string -> 'a) -> string -> 'a list
  val finiteSet : (string -> ''a) -> string -> ''a FiniteSet.set
  val set : (string -> ''a) -> string -> ''a Set.set
  val splitLevelApply : (string -> 'a) -> char list -> 'a list
  val splitLevelWithSepApply : (string -> 'a) -> char -> char list -> 'a list
  val splitLevelWithSepFunApply : (string -> 'a) -> (char -> bool) -> char list -> 'a list
  val splitLevel : char list -> string list
  val splitListWhen : ('a -> bool) -> 'a list -> ('a list * 'a list)
  val deTokenise : string -> string list -> string
  val removeOuterBrackets : string list -> string list
  val parseGraph : CSpace.token list -> string -> CSpace.token list * Graph.graph
end;

structure Parser : PARSER =
struct
  exception ParseError of string;
  exception CodeError;

  fun deTokenise sep (s::L) = s ^ sep ^ deTokenise sep L
    | deTokenise sep [] = ""

  fun splitListWhen f [] = (print "splitListWhen";raise Match)
    | splitListWhen f (s::L) =
        if f s then ([],L)
        else (case splitListWhen f L of (L1,L2) => (s::L1,L2))

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


  fun splitLevelWithSepFunApply f sep L =
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

  fun splitLevelWithSepApply f sep L =
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

  fun splitLevelApply f L = splitLevelWithSepApply f #"," L;

  fun relaxedList f x = if x = "" then [] else (splitLevelApply f o String.explode) x
  fun list f x = if x = "[]" then [] else (splitLevelApply f o String.explode o String.removeSquareBrackets) x
  fun finiteSet f x = if x= "{}" then FiniteSet.empty else (FiniteSet.ofList o splitLevelApply f o String.explode o String.removeBraces) x
  fun set f x = if x= "{}" then Set.empty else (Set.ofList o splitLevelApply f o String.explode o String.removeBraces) x


  fun pair (f,g) s =
    case splitLevel (String.explode (String.removeParentheses s)) of
      [x,y] => (f x, g y)
    | _ => raise ParseError (s ^ " not a pair")

  fun boolean s = if s = "true" then true
                  else if s = "false" then false
                       else raise ParseError (s ^ " not boolean")

  fun boolfun eq f s x = (List.exists (eq x) o splitLevelApply f o String.explode o String.removeBraces) s

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

  fun removeOuterJunk s =
    let fun roj (L,L') =
            (case (L,L') of
                (#"("::xL,#")"::xL') => roj (xL,xL')
              | (#"{"::xL,#"}"::xL') => roj (xL,xL')
              | (#"["::xL,#"]"::xL') => roj (xL,xL')
              | (#" "::xL,xL') => roj (xL,xL')
              | (xL,#" "::xL') => roj (xL,xL')
              | _ => (L,L'))
        val wL = String.explode s
        val (wL1,wL2) = List.split (wL, (List.length wL) div 2)
        val (wL1',wL2') = roj (wL1, rev wL2)
    in String.implode (wL1' @ rev wL2')
    end

  fun parseTyp s =
      (case String.breakOn ":" s of
          (s1,":",s2) => Type.fromString (removeOuterJunk s1 ^ ":" ^ removeOuterJunk s2)
        | _ => Type.fromString (removeOuterJunk s))

  fun parseToken tks s =
      (case String.breakOn ":" s of
          (ts,":",tys) => CSpace.makeToken (removeOuterJunk ts) (parseTyp tys)
        | _ => (case removeOuterJunk s of s' => 
                  (case List.find (fn x => CSpace.nameOfToken x = s') tks of 
                      SOME tok => tok 
                    | NONE => raise ParseError ("unidentified token: " ^ s))))

  fun parseCTyp s = case list parseTyp s of
                      (ty::tys) => (tys,ty)
                    | _ => raise ParseError ("bad constructor sig: " ^ s)
       

fun insert tk tks = if List.exists (fn x => CSpace.sameTokens x tk) tks then tks else tk :: tks
fun insertMany [] tks' = tks'
  | insertMany (tk::tks) tks' = insertMany tks (insert tk tks')

fun parseGraph TKS gs = 
  let
    fun parseTokenList tks [] = (tks,[],[])
      | parseTokenList tks [""] = (tks,[],[])
      | parseTokenList tks (s::ss) =
        (case String.breakOn "<-" s of
            (tt,"<-",_) => 
              (case parseToken tks tt of 
                tk => case parseTokenList (insert tk tks) ss of
                      (usedTokens, tokenList, restList) => (usedTokens, tk :: tokenList, s :: restList))
          | _ =>
            (case parseToken tks s of 
              tk => case parseTokenList (insert tk tks) ss of
                      (usedTokens, tokenList, restList) => (usedTokens, tk :: tokenList, restList)))
    fun parseInput tks ctinps =
      case String.breakOn "[" ctinps of
        (c,"[",ss) =>
          let 
            val (xs,ys) = breakOnClosingDelimiter (#"[",#"]") ss
            val _ = if ys = [] then ()
                    else raise ParseError ("invalid input sequence to constructor: " ^ ss)
            val (usedTokens, tokenList, restList) = parseTokenList tks (splitLevel xs)
          in (usedTokens,{constructor = removeOuterJunk c, inputTokens = tokenList},restList)
          end
      | _ => raise ParseError ("fail to parse constructor with inputs: " ^ ctinps)
    fun parseTIN tks s =
      case String.breakOn "<-" s of
          (tt,"<-",ctinps) => (case parseToken tks tt of 
                                tk => case parseInput (insert tk tks) ctinps of 
                                        (usedTokens,inp,restList) => (usedTokens,{token = tk, inputs = [inp]},restList))
        | _ => (case parseToken tks s of 
                  tk => (insert tk tks,{token = tk, inputs = []},[]))
    fun pg tks [] = (tks,[])
      | pg tks (s::ss) =
        let 
          val (usedTokens,tin,restList) = parseTIN tks s
          val (usedTokens',rest) = pg (insertMany usedTokens tks) (restList @ ss)
        in 
          (usedTokens',Graph.insertTIN tin rest)
        end
    
    val (usedTokens,result) = 
      case String.explode (String.removeBraces gs) of s => 
        if List.all (fn x => x = #" ") s then 
          ([],Graph.empty) 
        else 
          pg TKS (splitLevel s)
  in 
    (usedTokens, Graph.normalise result)
  end

end;
