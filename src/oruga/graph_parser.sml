import "oruga.parser";
import "core.graph";


exception ParseError of string

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

  fun parseToken tks s =
      (case String.breakOn ":" s of
          (ts,":",tys) => CSpace.makeToken (normaliseString ts) (parseTyp tys)
        | _ => (case normaliseString s of s' => 
                  (case List.find (fn x => CSpace.nameOfToken x = s') tks of 
                      SOME tok => tok 
                    | NONE => raise ParseError ("unidentified token: " ^ s))))

  fun parseCTyp s = case Parser.list parseTyp s of
                      (ty::tys) => (tys,ty)
                    | _ => raise ParseError ("bad constructor sig: " ^ s)

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

fun insert tk tks = if List.exists (fn x => CSpace.sameTokens x tk) tks then tks else tk :: tks
fun insertMany [] tks' = tks'
  | insertMany (tk::tks) tks' = insertMany tks (insert tk tks')

fun parseGraph TKS gs = 
  let
    fun parseTokenList tks [] = (tks,[],[])
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
            val (xs,ys) = Parser.breakOnClosingDelimiter (#"[",#"]") ss
            val _ = if ys = [] then ()
                    else raise ParseError ("invalid input sequence to constructor: " ^ ss)
            val (usedTokens, tokenList, restList) = parseTokenList tks (Parser.splitLevel xs)
          in (usedTokens,{constructor = normaliseString c, inputTokens = tokenList},restList)
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
    val (usedTokens,result) = pg TKS (Parser.splitLevel (String.explode (String.removeBraces gs)))
  in 
    (usedTokens, Graph.normalise result)
  end
