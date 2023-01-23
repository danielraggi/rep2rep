import "transfer.knowledge";

signature LATEX =
sig
  val realToString : Real.real -> string;
  val typ : Type.typ -> string;
  val token : CSpace.token -> string;
  val sectionTitle : bool -> string -> string;
  val construction : real * real -> Construction.construction -> string;
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
        | lus (c::C) = if c = #"_" orelse c = #"&" then #"\\" :: c :: lus C
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

  fun lines [h] = h
    | lines (h::t) = h ^ "\n " ^ lines t
    | lines _ = raise Empty


  fun nodeNameCharFilter x = x <> #"&" andalso x <> #"\\" andalso x <> #"|" andalso x <> #"("andalso x <> #")" andalso x <> #"[" andalso x <> #"]" andalso x <> #":" andalso x <> #"," andalso x <> #"."
  fun nodeNameOfToken t = String.addParentheses (String.implode (List.filter nodeNameCharFilter (String.explode (CSpace.nameOfToken t ^ "" ^ Type.nameOfType (CSpace.typeOfToken t)))))

  fun nodeNameOfConstructor c t =
    let val nc = CSpace.nameOfConstructor c
        val tn = (CSpace.nameOfToken t ^ "" ^ Type.nameOfType (CSpace.typeOfToken t))
        val nn = String.implode (List.filter nodeNameCharFilter (String.explode (nc ^ "_" ^ tn)))
    in String.addParentheses nn
    end

  fun coordinates (x,y) = String.addParentheses (realToString x ^ "," ^ realToString y)

  fun constructorNode coor c t =
    let val nc = "$\\mathit{"^CSpace.nameOfConstructor c^"}$"
        val nodeString = ""
    in "\\node[constructor = " ^ String.addBraces nc ^ "] " ^ nodeNameOfConstructor c t ^ " at " ^ coordinates coor ^ " " ^ String.addBraces nodeString ^ ";"
    end


  fun tokenNode isSource coor t =
    let val typn = "$\\mathsf{"^latexifyForbidden(Type.nameOfType (CSpace.typeOfToken t))^"}$"
        val tokn = "$"^CSpace.nameOfToken t^"$"
        val att = if isSource then "termS" else "term"
    in "\\node["^att^" = " ^ String.addBraces typn ^ "] " ^ nodeNameOfToken t ^ " at " ^ coordinates coor ^ " " ^ String.addBraces tokn ^ ";"
    end

  fun arrowBent nodeName parentName (ix,ox) =
    "\\path[->,in=" ^intToString ix^",out="^intToString ox ^"] " ^ nodeName ^ " edge " ^ parentName ^ ";"

  fun arrow nodeName parentName =
    "\\path[->] " ^ nodeName ^ " edge " ^ parentName ^ ";"

  fun arrowLabelled nodeName parentName i =
    "\\path[->] " ^ nodeName ^ " edge node[index label] " ^ String.addBraces (intToString i) ^ " " ^ parentName ^ ";"
  fun arrowLabelledBent nodeName parentName i (ix,ox)=
    String.concat ["\\path[->,in=", intToString ix, ",out="^intToString ox ^ "] ",
                   nodeName,
                   " edge node[index label] ", String.addBraces (intToString i), " ",
                   parentName,
                   ";"]


  val normalScale = 0.17
  val scriptScale = normalScale * 0.7
  val nodeConstant = 1.0 * normalScale

  fun displaySize (#"_"::S') = 0.8 * displaySize S'
    | displaySize (#"{"::S') = displaySize S'
    | displaySize (#"}"::S') = 1.25 * displaySize S'
    | displaySize (#":"::S') = 2.0 + displaySize S'
    | displaySize (#"+"::S') = 3.0 + displaySize S'
    | displaySize (#"-"::S') = 3.0 + displaySize S'
    | displaySize (#"="::S') = 3.0 + displaySize S'
    | displaySize (_::S') = 1.0 + displaySize S'
    | displaySize [] = 0.0

  fun displaySizeOfString s = displaySize (String.explode s)

  fun sizeOfType t = scriptScale * (displaySizeOfString (Type.nameOfType (CSpace.typeOfToken t)))
  fun sizeOfToken t = normalScale * (displaySizeOfString (CSpace.nameOfToken t)) + nodeConstant
  fun sizeOfConstructor c = scriptScale * (displaySizeOfString (CSpace.nameOfConstructor c)) + nodeConstant

  fun quickWidthEstimate (Construction.Source t) =
        Real.max(sizeOfToken t, sizeOfType t)
    | quickWidthEstimate (Construction.Reference _) = 0.0
    | quickWidthEstimate (Construction.TCPair ({token,constructor},cs)) =
        List.max Real.compare [sizeOfConstructor constructor,
                               0.9 * sizeOfToken token + sizeOfType token,
                               List.sumMap quickWidthEstimate cs]

  fun pullFirstRow ((x11::X1)::M) = (case pullFirstRow M of (fr,m) => (x11::fr,X1::m))
    | pullFirstRow ([]::M) = pullFirstRow M
    | pullFirstRow [] = ([],[])

  fun getWidthPerRow M =
    if null M then [] else
      (case pullFirstRow M of
         (fr,m) => (List.sum fr) :: getWidthPerRow m)

  fun rowWidthEstimates (Construction.Source t) =
        [Real.max(sizeOfToken t, sizeOfType t)]
    | rowWidthEstimates (Construction.Reference _) = []
    | rowWidthEstimates (Construction.TCPair ({token,constructor},cs)) =
      let val widthMatrix = map rowWidthEstimates cs
          val halfTokenSize = sizeOfToken token / 2.0
          val tNodeSize = halfTokenSize + Real.max (halfTokenSize, sizeOfType token) + 2.0*nodeConstant
      in tNodeSize :: sizeOfConstructor constructor :: getWidthPerRow widthMatrix
      end

  fun stringOfMatrix ((x11::X1)::M) = realToString x11 ^ " " ^ stringOfMatrix (X1::M)
    | stringOfMatrix ([]::M) = "\n" ^ stringOfMatrix M
    | stringOfMatrix [] = ""

  fun mkIntervals M =
    let val redC = ~1.0*nodeConstant
        fun intervalNeeded [x1] [x2] _ = (x1 + x2,0.0)
          | intervalNeeded [x1] (x2::L2) [] = (x1 + 4.0*nodeConstant,0.0)
          | intervalNeeded (x1::L1) (x2::L2) LL = (case intervalNeeded L1 L2 (#2 (pullFirstRow LL)) of (x,excess) => (Real.max(x1+x2,x),excess))
          | intervalNeeded (x1::L1) [] (L3::LL) = (case intervalNeeded (x1::L1) L3 LL of (x,_) => (x / 2.0, x / 2.0))
          | intervalNeeded (x1::L1) [] [] = (0.0,0.0)
          | intervalNeeded [] (x2::L2) _ = (0.0,0.0)
          | intervalNeeded [] [] _ = (0.0,0.0)
        fun positionsPerRow _ [] = []
          | positionsPerRow _ [_] = []
          | positionsPerRow p (L1::(L2::LL)) =
            (case intervalNeeded L1 L2 LL of
              (x,excess) => p + x + redC :: positionsPerRow (p + x + redC + excess) (L2::LL))
    in 0.0 :: positionsPerRow redC M
    end

  fun unzip [] = ([],[])
    | unzip ((x,y)::L) = (case unzip L of (L1,L2) => (x::L1,y::L2))
  fun construction' coor parentName (i,n) (ct as Construction.Source t) =
        (case parentName of
          NONE => lines [tokenNode true coor t]
        | SOME pn => lines [tokenNode true coor t, arrowLabelled (nodeNameOfToken t) pn i],
        (Real.max(sizeOfToken t, sizeOfType t),1.0))
    | construction' _ parentName (i,n) (ct as Construction.Reference t) =
        (case parentName of
          NONE => "% BAD CONSTRUCTION"
        | SOME pn => if real i <= real n / real 2
                     then lines [arrowLabelledBent (nodeNameOfToken t) pn i (180,180)]
                     else lines [arrowLabelledBent (nodeNameOfToken t) pn i (0,0)],
        (0.0,0.0))
    | construction' (x,y) parentName (i,n) (ct as Construction.TCPair ({constructor,token},cs)) =
        let val tn = tokenNode false (x,y) token
            val cn = constructorNode (x,y-0.9) constructor token
            val constructorNodeName = nodeNameOfConstructor constructor token
            val cn2tn = arrow constructorNodeName (nodeNameOfToken token)
            val widthEstimates = map rowWidthEstimates cs
            val intervals = mkIntervals widthEstimates
            val cwidth = List.last intervals
            val nchildren = length cs
            fun calcX j = ~cwidth/2.0 + List.nth(intervals,j)
            fun crec _ [] = []
              | crec j (ct::cts) = construction' (x + (calcX j), y-1.8) (SOME constructorNodeName) (j+1,nchildren) ct :: crec (j+1) cts
            val (lcts, xysizes) = unzip (crec 0 cs)
            val width = List.sumMap #1 xysizes
            val depth = List.max Real.compare (map #2 xysizes)
        in (case parentName of
              NONE => lines ([tn,cn,cn2tn] @ lcts)
            | SOME pn =>
                let val tn2parent = arrowLabelled (nodeNameOfToken token) pn i
                in lines ([tn,tn2parent,cn,cn2tn] @ lcts)
                end,
            (width,depth))
        end

  fun construction coor ct =
    let val (ctLatex,(width,depth)) = construction' coor NONE (0,1) ct
        val (oscale,cscale) = if width > 18.0 orelse depth > 18.0 then ("\\scalebox{0.75}{","}") else ("","")
        val opening = oscale ^ "\\begin{tikzpicture}[construction,align at top]"
        val closing = "\\end{tikzpicture}" ^ cscale
    in lines [opening, ctLatex, closing]
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
