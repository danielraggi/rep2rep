import "transfer.knowledge";

signature LATEX =
sig
  val realToString : Real.real -> string;
  val typ : Type.typ -> string;
  val token : CSpace.token -> string;
  val sectionTitle : bool -> string -> string;
  val tikzOfGraph : real * real -> Graph.graph -> string;
  val propositionsOfGraph : Graph.graph -> string;
  val mkDocument : string -> string;
  val outputDocument : TextIO.outstream -> string -> unit;
  val printWithHSpace : real -> string list -> string;
  val printSubSections : int -> string list -> string;
  val environment : string -> string -> string -> string;
end;

structure Latex : LATEX =
struct

  fun latexifyForbidden s =
    let fun lus [] = []
          | lus (c::C) = if c = (#"_") orelse c = (#"&") then #"\\" :: c :: lus C
                        else c :: lus C
    in String.implode (lus (String.explode s))
    end 

    fun mathsf s = "\\mathsf{" ^ latexifyForbidden s ^ "}"
    fun mathtt s = "\\mathtt{" ^ latexifyForbidden s ^ "}"
    fun texttt s = "\\texttt{" ^ latexifyForbidden s ^ "}"
    fun typ ty = mathtt (Type.nameOfType ty)
    fun token t =
      let val tok = CSpace.nameOfToken t
          val ty = typ (CSpace.typeOfToken t)
      in tok ^ " : " ^ ty
      end


  fun mapMany [] [] = []
    | mapMany (f::fs) (x::xs) = f x :: mapMany fs xs
    | mapMany _ _ = raise Match
  fun unzip [] = ([],[])
    | unzip ((x,y)::XY) = let val (X,Y) = unzip XY in (x::X,y::Y) end

  fun lines [h] = h
    | lines (h::t) = h ^ "\n " ^ lines t
    | lines _ = raise Empty
  
  fun nodeNameCharFilter x = x <> #"&" andalso x <> #"\\" andalso x <> #"|" andalso x <> #"(" andalso x <> #")" andalso x <> #"[" andalso x <> #"]" andalso x <> #":" andalso x <> #"," andalso x <> #"."

  fun nodeNameOfToken t =
    let val nt = CSpace.nameOfToken t
        val tt = CSpace.typeOfToken t
        val charL = case List.filter nodeNameCharFilter (String.explode (nt ^ "" ^ Type.nameOfType tt)) of #" " :: L => #"Q" :: #" " :: L | L => L
    in String.addParentheses (String.implode charL)
    end

  fun nodeNameOfConstructor c t x =
    let val tn = (CSpace.nameOfToken t ^ "" ^ Type.nameOfType (CSpace.typeOfToken t) ^ x)
        val nn = String.implode (List.filter nodeNameCharFilter (String.explode (c ^ "_" ^ tn)))
    in String.addParentheses nn
    end  

  fun firstN 0 _ = []
    | firstN n [] = []
    | firstN n (x::xs) = x :: firstN (n-1) xs

  fun realToString z =
    let val zs = Real.fmt (StringCvt.FIX (SOME 2)) z
    in case (String.explode zs) of
          (#"~"::n) => ("-" ^ String.implode n)
        | n => zs
    end
  fun intToString z =
    let val zs = Int.toString z
    in case (String.explode zs) of
          (#"~"::n) => ("-" ^ String.implode (firstN 6 n))
        | n => String.implode (firstN 6 n)
    end

  fun coordinates (x,y) = String.addParentheses (realToString x ^ "," ^ realToString y)
  fun coordinatesN (x,y) = String.implode (List.filter nodeNameCharFilter (String.explode ((realToString x ^ "," ^ realToString y)))) 

  fun constructorNode coor c t x =
    let val nc = "$\\mathsf{"^c^"}$"
        val nodeString = ""
    in "\\node[constructor = " ^ String.addBraces nc ^ "] " ^ nodeNameOfConstructor c t x ^ " at " ^ coordinates coor ^ " " ^ String.addBraces nodeString ^ ";"
    end

  fun tokenNode isSource coor t =
    let val typn = "$\\mathsf{"^latexifyForbidden(Type.nameOfType (CSpace.typeOfToken t))^"}$"
        val tokn = "$"^CSpace.nameOfToken t^"$"
        val att = if isSource then "termS" else "termE"
    in "\\node["^att^" = " ^ String.addBraces typn ^ "] " ^ nodeNameOfToken t ^ " at " ^ coordinates coor ^ " " ^ String.addBraces tokn ^ ";"
    end

  fun arrow nodeName parentName =
    "\\path[->] " ^ nodeName ^ " edge " ^ parentName ^ ";"

  fun angles 1 = ([90],[~90])
    | angles 2 = ([75, 105],[~150, ~30])
    | angles 3 = ([60, 90, 120],[~165, ~90, ~15])
    | angles 4 = ([30, 60, 120, 150],[~180, ~120, ~60, ~0])
    | angles 5 = ([15, 60, 90, 120, 165],[~180, ~120, ~90, ~60, ~0])
    | angles n = 
      let 
        val u = 180 div (n - 1)
        fun mkL 0 = ([],[]) 
          | mkL i = case mkL (i-1) of (X,Y) => ((n-i) * u :: X, ~i * u :: Y)
      in mkL n
      end

  fun arrowLabelled tokenPos conPos tokenName conName i n =
    let val (x,y) = conPos
        val (x',y') = tokenPos
        val angle = 180.0 * (Math.atan ((x-x')/(y-y'))) / Math.pi
        val outAngle = if y > y' then 90.0 - angle * 0.5 else (if Real.abs(angle) > 30.0 then ~90.0 - angle * 0.5 else (if i <= n div 2 then ~165.0 else ~15.0))
        val inAngle = if y > y' then ~90.0 - angle  else if Real.abs(angle) > 30.0 then 90.0 - angle else if i <= n div 2 then ~165.0 else ~15.0
        val actualInAngle = if n > 2 then List.avg[Real.fromInt(List.nth(#2(angles n),i-1)),inAngle] else inAngle
    in
      "\\path[->] " ^ tokenName ^ " edge[out = " ^ realToString outAngle ^ ", in = " ^ realToString actualInAngle ^ 
      ", looseness = 0.8] node[index label] " ^ String.addBraces (intToString i) ^ " " ^ conName ^ ";"
    end
    
  val normalScale = 0.215
  val scriptScale = normalScale * 0.68

  fun displaySize (#"_"::(#"{"::S')) = (9.0/10.0) * displaySize S'
    | displaySize (#"}"::S') = (10.0/9.0) * displaySize S'
    | displaySize (#"m"::S') = 1.2 + displaySize S'
    | displaySize (#":"::S') = 2.0 + displaySize S'
    | displaySize (#">"::S') = 2.5 + displaySize S'
    | displaySize (#"<"::S') = 2.5 + displaySize S'
    | displaySize (#"+"::S') = 2.5 + displaySize S'
    | displaySize (#"-"::S') = 2.5 + displaySize S'
    | displaySize (#"="::S') = 2.5 + displaySize S'
    | displaySize (char::S') = (if Char.isUpper char orelse Char.isDigit char then 1.2 else 1.0) + displaySize S'
    | displaySize [] = 0.0

  fun displaySizeOfString s = displaySize (String.explode s)

  val nodeConstant = 0.2 * normalScale
  fun sizeOfType t = scriptScale * (displaySizeOfString (Type.nameOfType (CSpace.typeOfToken t)))
  fun sizeOfToken t = normalScale * (displaySizeOfString (CSpace.nameOfToken t))
  fun sizeOfConstructorLabel c = scriptScale * (displaySizeOfString c)
    
  fun findPosOfToken [] t = raise Fail "no token"
    | findPosOfToken (posTIN::posG) t = if CSpace.sameTokens (#token (#tin posTIN)) t then #pos posTIN else findPosOfToken posG t

  fun mapArrows _ _ _ _ _ [] = []
    | mapArrows g i n conPos cn (tn::tns) = 
        arrowLabelled (findPosOfToken g tn) conPos (nodeNameOfToken tn) cn i n :: mapArrows g (i+1) n conPos cn tns

  fun tikzOfInput g t {input = {constructor,inputTokens}, pos} = 
    let val constructorNodeName = nodeNameOfConstructor constructor t (coordinatesN pos)
    in (constructorNode pos constructor t (coordinatesN pos), 
        lines (arrow constructorNodeName (nodeNameOfToken t) :: mapArrows g 1 (length inputTokens) pos constructorNodeName inputTokens))
    end
  fun tikzOfTIN g {tin={token,inputsWithPosition},pos} = 
    let val (nodes,arrows) = unzip (map (tikzOfInput g token) inputsWithPosition)
    in (tokenNode (null inputsWithPosition) pos token :: nodes,arrows)
    end

  fun range [] = (0.0,0.0,0.0,0.0)
    | range ({tin={token,inputsWithPosition},pos= (x,y)}::g) = let val (left,right,bottom,top) = range g in (Real.min(left,x),Real.max(right,x),Real.min(bottom,y),Real.max(top,y)) end

  fun tikzOfGraph (x,y) (g:Graph.graph) =
    let
      fun dropLast [] = []
        | dropLast [x] = []
        | dropLast (x::xs) = x :: dropLast xs
      fun dropFirstAndLast L = dropLast (List.tl L)
      fun xcv right0 [] = [right0]
        | xcv right0 (spaces::L) = 
          let val left1 = List.hd spaces 
              val right1 = List.last spaces 
              val inner = dropFirstAndLast spaces
              val i = List.sum inner / 2.0 
          in (right0 + left1 + i) :: (xcv (right1 + i) L) 
          end 
      val removeNodeConstant = map (fn x => x - nodeConstant)
      fun marginsForInput inp g' = 
        let 
          fun marginsPerInputToken t = 
              let val (tin,g'') = Graph.pullTINOfToken g' t 
              in marginsForTIN (valOf tin) g''
              end handle Option => ([0.0,0.0],g')
          fun getMarginsForInputTokens [] g'' = ([],g'')
            | getMarginsForInputTokens (inptk::inptks) g'' =
              let val (margins,g''') = marginsPerInputToken inptk
                  val (marginss,g'''') = getMarginsForInputTokens inptks g'''
              in (margins :: marginss, g'''')
              end
          val (marginsForInputTokens,g'') = getMarginsForInputTokens (#inputTokens inp) g'
          val margs = removeNodeConstant (xcv 0.0 marginsForInputTokens)
          val res = Real.max(List.hd margs,sizeOfConstructorLabel (#constructor inp)) :: List.tl margs handle Empty => margs (* assumes constructor label is on left *)
        in (res,g'') 
        end
      and marginsForTIN tin g' =
        let 
          fun getMarginsForInputs [] g'' = ([],g'')
            | getMarginsForInputs (inp::inps) g'' = 
              let val (margins,g''') = marginsForInput inp g''
                  val (marginss,g'''') = getMarginsForInputs inps g'''
              in (margins :: marginss, g'''')
              end
          val stk = sizeOfToken (#token tin)
          val sty = sizeOfType (#token tin)
          val hstk = Real.max(stk,sty) / 2.0 
          val (marginsForInputs,g'') = 
                if null (#inputs tin) then 
                  ([[hstk,hstk]],g') 
                else 
                  getMarginsForInputs (#inputs tin) g'
          val margs = if null (#inputs tin) then 
                        xcv 0.0 marginsForInputs 
                      else 
                        xcv 0.0 (map removeNodeConstant marginsForInputs)
          val res = if null (#inputs tin) then 
                      margs 
                    else 
                      let val rmargs = List.rev margs 
                      in List.rev (Real.max(List.hd rmargs,sty+stk/2.0) :: List.tl rmargs)
                      end handle Empty => margs (* assumes token label (type) is on left *)
        in (res,g'')
        end
      fun assignPositionsForTIN g' (x,y) NONE = ([],g') 
        | assignPositionsForTIN g' (x,y) (SOME tin) = 
        let
          val token = #token tin
          val inputs = #inputs tin
          val (margins,_) = marginsForTIN tin g'
          val inner = dropFirstAndLast margins
          val newY = y - 0.8
          fun makePositionsForChildren _ [] = []
            | makePositionsForChildren xj (s::ss) = (xj+s,newY) :: makePositionsForChildren (xj+s) ss
          val chPositions = makePositionsForChildren 0.0 (x - (List.sum inner / 2.0) :: inner)
          fun processMany g'' [] [] = ([],[], g'')
            | processMany g'' (pos::poss) (inp::inps) = 
              let 
                val (inputWithPosition,assignedTINs,unassignedTINs) = assignPositionsForInput g'' pos inp
                val (inputsWithPosition,moreAssignedTINs,g''') = processMany unassignedTINs poss inps
              in (inputWithPosition::inputsWithPosition,assignedTINs @ moreAssignedTINs,g''')
              end
            | processMany g'' (pos::poss) [] = ([],[], g'')
            | processMany _ [] (inp::inps) = raise Fail "mismatched inputs and positions"
          val (inputsWithPosition,assignedTINs,unassignedTINs) = processMany g' chPositions inputs
        in
          ({tin = {token = token, inputsWithPosition = inputsWithPosition}, pos = (x,y)} :: assignedTINs, unassignedTINs)
        end 
      and assignPositionsForInput g' (x,y) inp =
        let 
          val (_,g'') = Graph.pullTINsOfTokens g' (#inputTokens inp)
          val (TINs,_) = unzip (map (Graph.pullTINOfToken g') (#inputTokens inp))
          val (margins,_) = marginsForInput inp g'
          val inner = dropFirstAndLast margins
          val newY = y - 1.0
          fun makePositionsForChildren _ [] = []
            | makePositionsForChildren xj (s::ss) = (xj+s,newY) :: makePositionsForChildren (xj+s) ss
          val chPositions = makePositionsForChildren 0.0 (x - (List.sum inner / 2.0) :: inner)
          
          fun processMany g'' [] [] = ([], g'')
            | processMany g'' (pos::poss) (tin::tins) = 
              let 
                val (assignedTINs,unassignedTINs) = assignPositionsForTIN g'' pos tin
                val (moreAssignedTINs,g''') = processMany unassignedTINs poss tins
              in (assignedTINs @ moreAssignedTINs,g''')
              end
            | processMany g'' (pos::poss) [] = ([],g'')
            | processMany _ [] (tin::tins) = raise Fail "mismatched tins and positions"
          val (assignedTINs,unassignedTINs) = processMany g'' chPositions TINs
        in ({input = inp, pos = (x,y)}, assignedTINs, unassignedTINs)
        end
      fun processGraph _ [] = []
        | processGraph (x,y) (tin::g') = 
        let 
          val (margins,_) = marginsForTIN tin (tin::g')
          val inner = dropFirstAndLast margins
          val innerSpaceHalved = List.sum inner / 2.0
          val leftSpace = (List.hd margins) + innerSpaceHalved 
          val rightSpace = (List.last margins) + innerSpaceHalved 
          val (assigned,unassigned) = assignPositionsForTIN g' (x + leftSpace,y) (SOME tin)
        in assigned @ processGraph (x + leftSpace + rightSpace,y) unassigned
        end
      val graphWithPositions = processGraph (x,y) (Graph.orderByHierarchy (Graph.normalise g))
      val (left,right,bottom,top) = range graphWithPositions
      val (nodes,arrows) = unzip (map (tikzOfTIN graphWithPositions) graphWithPositions)
      val xscale = let val width = right - left in if width > 100.0 then ", xscale = " ^ realToString (30.0 / width) else if width > 60.0 then ", xscale = " ^ realToString (55.0 / width) else "" end
      val yscale =  let val height = top - bottom in if height > 120.0 then ", yscale = " ^ realToString (110.0 / height) else "" end
      val opening = "\\begin{tikzpicture}[construction,align at top" ^ xscale ^ yscale ^ "]"
      val closing = "\\end{tikzpicture}"
    in lines [opening, lines (List.concat (nodes @ arrows)), closing]
    end handle Empty => ""

  fun reduceGraph g = 
    let
      fun removeLeaves _ [] = []
        | removeLeaves tks (tin'::g) = 
          if List.exists (fn x => CSpace.sameTokens x (#token tin')) tks andalso null (#inputs tin') then 
            removeLeaves tks g 
          else 
            tin' :: removeLeaves (List.flatmap #inputTokens (#inputs tin') @ tks) g
    in removeLeaves [] (Graph.orderByHierarchy g)
    end

  fun propositionsOfGraph g =
    let
      fun pog [] = []
        | pog (tin::g') =
        let 
          fun makeNegStatements [] = []
            | makeNegStatements (inp::inps) = 
              "\\neg" ^ mathtt(#constructor inp) ^ List.toString token (#inputTokens inp) :: makeNegStatements inps
          fun makePosStatements [] = []
            | makePosStatements (inp::inps) = 
            mathtt(#constructor inp) ^ List.toString token (#inputTokens inp) :: makePosStatements inps
          val P = if CSpace.typeOfToken (#token tin) = "metaTrue" then 
                    makePosStatements (#inputs tin) 
                  else if CSpace.typeOfToken (#token tin) = "metaFalse" then 
                    makeNegStatements (#inputs tin)
                  else if null (#inputs tin) then [token (#token tin)] 
                  else raise Fail "x"
        in P @ pog g'
        end
    in 
      "\\begin{align*} &" ^ String.concatWith "\\\\ &" (pog (reduceGraph g)) ^ "\\end{align*}"
    end

  fun mkDocument content =
    let val opening = "\\documentclass[a3paper,10pt]{article}\n "^
                      "\\usepackage[margin=2cm]{geometry}\n "^
                      "\\input{commands}\n"^
                      "\\tikzset{align at top/.style={baseline=(current bounding box.north)}}\n\n"^
                      "\\begin{document}"
        val closing = "\\end{document}"
    in lines [opening, content, closing]
    end

  fun outputDocument file content =
    let val _ = TextIO.output(file, mkDocument content)
    in () end

  fun sectionTitle b s = "\\section" ^ (if b then "" else "*") ^ "{" ^ s ^ "}"
  fun subSectionTitle b s = "\\subsection" ^ (if b then "" else "*") ^ "{" ^ s ^ "}"

  fun printWithHSpace _ [] = ""
    | printWithHSpace r (h::t) = h ^ "\n \\hspace{" ^ Real.toString r ^ "cm} \n " ^ printWithHSpace r t;

  fun printSubSections _ [] = ""
    | printSubSections i (h::t) = "\\subsection*{Result "^Int.toString i^"}\n" ^ h ^ printSubSections (i+1) t;

  fun environment name parameters content =
    "\\begin{"^name^"}"^parameters^"\n"^content^"\n \\end{"^name^"}"

end;
