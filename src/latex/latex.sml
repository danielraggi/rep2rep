import "transfer.knowledge";

signature LATEX =
sig
  val realToString : Real.real -> string;
  val typ : Type.typ -> string;
  val token : CSpace.token -> string;
  val sectionTitle : bool -> string -> string;
  val tikzOfGraph : real * real -> Graph.graph -> string;
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
          | lus (c::C) = if c = (#"_") orelse c = (#"&") then (#"\\"(* " *))  :: c :: lus C
                        else c :: lus C
    in String.implode (lus (String.explode s))
    end 

    fun mathsf s = "\\mathsf{" ^ latexifyForbidden s ^ "}"
    fun typ ty = mathsf (Type.nameOfType ty)
    fun token t =
      let val tok = CSpace.nameOfToken t
          val ty = typ (CSpace.typeOfToken t)
      in tok ^ " : " ^ ty
      end

  fun findTINForToken _ [] = NONE
    | findTINForToken t (tin::g) = if CSpace.sameTokens t (#token tin) then SOME tin else findTINForToken t g
  fun getMissingOneStepDescendants tks g t = 
    let val oneStepDescendants = List.flatmap #inputTokens (#inputs (valOf (findTINForToken t g)))
    in List.filter (fn x => not (List.exists (fn y => CSpace.sameTokens x y) tks)) oneStepDescendants
    end
  fun assessTokenHierarchy tks (g:Graph.graph) t = 
    1 + (List.max (fn (x,y) => Int.compare (x,y)) (map (assessTokenHierarchy (t::tks) g) (getMissingOneStepDescendants (t::tks) g t))) handle Empty => 1 | Option => 0

  fun assignTokenHierarchy [] _ = []
    | assignTokenHierarchy (tin::g:Graph.graph) g' =
    {h = assessTokenHierarchy [] g' (#token tin), tin = tin} :: assignTokenHierarchy g g'

  fun orderByHierarchy (g:Graph.graph) = map #tin (List.mergesort (fn (x,y) => Int.compare(#h y,#h x)) (assignTokenHierarchy g g))

  fun descendantTokens tks g t = 
    let val oneStepDescendants = getMissingOneStepDescendants tks g t
        fun dts _ [] = []
          | dts tks' (d::ds) = (case descendantTokens tks' g d of dd => dd @ dts (tks' @ dd) ds)
    in oneStepDescendants @ dts (tks @ oneStepDescendants) oneStepDescendants
    end

  fun descendantTokens' tks g [] = []
    | descendantTokens' tks g (t::ts) = (case descendantTokens tks g t of dtks => dtks @ descendantTokens' (dtks @ tks) g ts)

  fun pullTINOfToken (g:Graph.graph) t = (case List.partition (fn tin => CSpace.sameTokens t (#token tin)) g of ([tin],g') => (SOME tin,g') | _ => (NONE,g))
  fun pullTINsOfTokens (g:Graph.graph) tks = List.partition (fn tin => List.exists (fn x => CSpace.sameTokens x (#token tin)) tks) g

  fun mapMany [] [] = []
    | mapMany (f::fs) (x::xs) = f x :: mapMany fs xs
    | mapMany _ _ = raise Match
  fun unzip [] = ([],[])
    | unzip ((x,y)::XY) = let val (X,Y) = unzip XY in (x::X,y::Y) end


  exception Fail
  fun lines [h] = h
    | lines (h::t) = h ^ "\n " ^ lines t
    | lines _ = raise Empty
  
  fun nodeNameCharFilter x = x <> #"&" andalso x <> #"\\"(* " *) andalso x <> #"|" andalso x <> #"("(* " *) andalso x <> #")" andalso x <> #"[" andalso x <> #"]" andalso x <> #":" andalso x <> #"," andalso x <> #"."

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
    let val nc = "$\\mathit{"^c^"}$"
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

  fun arrowLabelled nodeName parentName i =
    "\\path[->] " ^ nodeName ^ " edge node[index label] " ^ String.addBraces (intToString i) ^ " " ^ parentName ^ ";"

  val normalScale = 0.2
  val scriptScale = normalScale * 0.75
  val nodeConstant = 1.0 * normalScale

  fun displaySize (#"_"::(#"{"::S')) = (9.0/10.0) * displaySize S'
    | displaySize (#"}"::S') = (10.0/9.0) * displaySize S'
    | displaySize (#":"::S') = 2.0 + displaySize S'
    | displaySize (#"+"::S') = 3.0 + displaySize S'
    | displaySize (#"-"::S') = 3.0 + displaySize S'
    | displaySize (#"="::S') = 3.0 + displaySize S'
    | displaySize (_::S') = 1.0 + displaySize S'
    | displaySize [] = 0.0

  fun displaySizeOfString s = displaySize (String.explode s)

  fun sizeOfType t = scriptScale * (displaySizeOfString (Type.nameOfType (CSpace.typeOfToken t)))
  fun sizeOfToken t = Real.max(normalScale * (displaySizeOfString (CSpace.nameOfToken t)) + nodeConstant, sizeOfType t)

  fun mapArrows _ [] _ = []
    | mapArrows i (tn::tns) cn = arrowLabelled (nodeNameOfToken tn) cn i :: mapArrows (i+1) tns cn
    
  fun tikzOfInput t {input = {constructor,inputTokens}, pos} = 
    let val constructorNodeName = nodeNameOfConstructor constructor t (coordinatesN pos)
    in (constructorNode pos constructor t (coordinatesN pos), 
        lines (arrow constructorNodeName (nodeNameOfToken t) :: mapArrows 1 inputTokens constructorNodeName))
    end
  fun tikzOfTIN {tin={token,inputsWithPosition},pos} = 
    let val (nodes,arrows) = unzip (map (tikzOfInput token) inputsWithPosition)
    in (tokenNode (null inputsWithPosition) pos token :: nodes,arrows)
    end

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
          in right0+left1+i :: (xcv (right1+i) L) 
          end
      fun marginsForInput inp g' = 
        let 
          fun marginsPerInputToken t = 
              let val (tin,g'') = pullTINOfToken g' t 
              in marginsForTIN (valOf tin) g''
              end handle Option => ([0.0],g')
          fun getMarginsForInputTokens [] g'' = ([],g'')
            | getMarginsForInputTokens (inptk::inptks) g'' =
              let val (margins,g''') = marginsPerInputToken inptk
                  val (marginss,g'''') = getMarginsForInputTokens inptks g'''
              in (margins :: marginss, g'''')
              end
          val (marginsForInputTokens,g'') = getMarginsForInputTokens (#inputTokens inp) g'
        in (xcv 0.0 marginsForInputTokens,g'')
        end
      and marginsForTIN tin g' =
        let 
          fun getMarginsForInputs [] g'' = ([],g'')
            | getMarginsForInputs (inp::inps) g'' = 
              let val (margins,g''') = marginsForInput inp g''
                  val (marginss,g'''') = getMarginsForInputs inps g'''
              in (margins :: marginss, g'''')
              end
          val (marginsForInputs,g'') = if null (#inputs tin) then ([[sizeOfToken (#token tin) / 2.0,sizeOfToken (#token tin)/ 2.0]],g') else getMarginsForInputs (#inputs tin) g'
        (* val L = xcv 0.0 marginsForInputs
          val _ = print (CSpace.stringOfToken (#token tin) ^ "\n") 
          val _ = print (List.toString (List.toString Real.toString) (marginsForInputs) ^ "\n") 
          val _ = print (List.toString (Real.toString) L  ^ "\n\n") *)
        in (xcv 0.0 marginsForInputs,g'')
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
            | processMany _ [] (inp::inps) = (raise Fail)
          val (inputsWithPosition,assignedTINs,unassignedTINs) = processMany g' chPositions inputs
        in
          ({tin = {token = token, inputsWithPosition = inputsWithPosition}, pos = (x,y)} :: assignedTINs, unassignedTINs)
        end 
      and assignPositionsForInput g' (x,y) inp =
        let 
          val (_,g'') = pullTINsOfTokens g' (#inputTokens inp)
          val (TINs,_) = unzip (map (pullTINOfToken g') (#inputTokens inp))
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
            | processMany _ [] (tin::tins) = (raise Fail)
          val (assignedTINs,unassignedTINs) = processMany g'' chPositions TINs
        in ({input = inp, pos = (x,y)}, assignedTINs, unassignedTINs)
        end
      fun processGraph _ [] = []
        | processGraph (x,y) (tin::g') = 
        let 
          val (margins,_) = marginsForTIN tin g'
          val inner = dropFirstAndLast margins
          val innerSpaceHalved = List.sum inner / 2.0
          val leftSpace = (List.hd margins) + innerSpaceHalved
          val rightSpace = (List.last margins) + innerSpaceHalved
          val (assigned,unassigned) = assignPositionsForTIN g' (x + leftSpace,y) (SOME tin)
        in assigned @ processGraph (x + rightSpace,y) unassigned
        end
      val graphWithPositions = processGraph (x,y) (orderByHierarchy (Graph.normalise g))
      val (nodes,arrows) = unzip (map tikzOfTIN graphWithPositions)
      val opening = "\\begin{tikzpicture}[construction,align at top]"
      val closing = "\\end{tikzpicture}"
    in lines [opening, lines (List.concat (nodes @ arrows)), closing]
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
