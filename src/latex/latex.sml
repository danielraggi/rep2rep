import "transfer.knowledge";

signature LATEX =
sig
  val typ : Type.typ -> string;
  val token : CSpace.token -> string;
  val relationship : Relation.relationship -> string;
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

  fun mathsf s = "\\mathsf{" ^ s ^ "}"
  fun typ ty = mathsf (Type.nameOfType ty)
  fun token t =
    let val tok = CSpace.nameOfToken t
        val ty = typ (CSpace.typeOfToken t)
    in tok ^ " : " ^ ty
    end
  fun relationship (x,y,R) =
    "(" ^ List.toString token x ^ "," ^
          List.toString token y ^ ")" ^
        "\\in " ^ mathsf (Relation.nameOf R)

  fun realToString z =
    let val zs = Real.toString z
    in case String.explode zs of (#"~"::n) => ("-" ^ String.implode n) | _ => zs
    end

  fun intToString z =
    let val zs = Int.toString z
    in case String.explode zs of (#"~"::n) => ("-" ^ String.implode n) | _ => zs
    end

  fun lines [h] = h
    | lines (h::t) = h ^ "\n " ^ lines t
    | lines _ = raise Empty


  fun nodeNameCharFilter x = x <> #"\\" andalso x <> #"|" andalso x <> #"("andalso x <> #")" andalso x <> #"[" andalso x <> #"]" andalso x <> #":" andalso x <> #","
  fun nodeNameOfToken t = String.addParentheses (String.implode (List.filter nodeNameCharFilter (String.explode (CSpace.nameOfToken t ^ "" ^ Type.nameOfType (CSpace.typeOfToken t)))))
  fun nodeNameOfConfigurator u t =
    let val nu = CSpace.nameOfConfigurator u
        val c = CSpace.constructorOfConfigurator u
        val nc = CSpace.nameOfConstructor c
        val tn = (CSpace.nameOfToken t ^ "" ^ Type.nameOfType (CSpace.typeOfToken t))
        val tn' = String.implode (List.filter nodeNameCharFilter (String.explode tn))
    in String.addParentheses (nu ^ "_" ^ nc ^ "_" ^ tn')
    end

  fun nodeNameOfConstructor c t =
    let val nc = CSpace.nameOfConstructor c
        val tn = (CSpace.nameOfToken t ^ "" ^ Type.nameOfType (CSpace.typeOfToken t))
        val nn = String.implode (List.filter nodeNameCharFilter (String.explode (nc ^ "_" ^ tn)))
    in String.addParentheses nn
    end

  fun coordinates (x,y) = String.addParentheses (realToString x ^ "," ^ realToString y)

  fun configuratorNode coor u t =
    let val nu = CSpace.nameOfConfigurator u
        val c = CSpace.constructorOfConfigurator u
        val nc = "$\\mathit{"^CSpace.nameOfConstructor c^"}$"
        val nodeString = ""
    in "\\node[constructor = " ^ String.addBraces nc ^ "] " ^ nodeNameOfConfigurator u t ^ " at " ^ coordinates coor ^ " " ^ String.addBraces nodeString ^ ";"
    end

  fun constructorNode coor c t =
    let val nc = "$\\mathit{"^CSpace.nameOfConstructor c^"}$"
        val nodeString = ""
    in "\\node[constructor = " ^ String.addBraces nc ^ "] " ^ nodeNameOfConstructor c t ^ " at " ^ coordinates coor ^ " " ^ String.addBraces nodeString ^ ";"
    end

  fun tokenNode isSource coor t =
    let val typn = "$\\mathsf{"^Type.nameOfType (CSpace.typeOfToken t)^"}$"
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

  fun quickWidthEstimate (Construction.Source t) =
        let val sizeOfToken = real (String.size (CSpace.nameOfToken t))
            val sizeOfType = 0.8 * real (String.size (Type.nameOfType (CSpace.typeOfToken t)))
        (*in Real.max(0.75,0.1*real (Int.max(sizeOfToken,sizeOfType)))*)
        in Real.max(0.7,0.11* (Real.max(sizeOfToken, sizeOfType)))
        end
    | quickWidthEstimate (Construction.Loop _) = 0.0
    | quickWidthEstimate (Construction.TCPair (_,cs)) = List.sumMap quickWidthEstimate cs

  fun construction' coor parentName i (Construction.Source t) =
        (case parentName of
          NONE => lines [tokenNode true coor t]
        | SOME pn => lines [tokenNode true coor t, arrowLabelled (nodeNameOfToken t) pn i])
    | construction' _ parentName i (Construction.Loop t) =
        (case parentName of
          NONE => "% BAD CONSTRUCTION"
        | SOME pn => if i = 1
                     then lines [arrowLabelledBent (nodeNameOfToken t) pn i (180,195)]
                     else lines [arrowLabelledBent (nodeNameOfToken t) pn i (0,~15)])
    | construction' (x,y) parentName i (Construction.TCPair ({constructor,token},cs)) =
        let val tn = tokenNode false (x,y) token
            val cn = constructorNode (x,y-1.0) constructor token
            val constructorNodeName = nodeNameOfConstructor constructor token
            val cn2tn = arrow constructorNodeName (nodeNameOfToken token)
            val widthEstimates = map (fn x => (Math.pow(quickWidthEstimate x,0.9))) cs
            fun mkIntervals _ [] = []
              | mkIntervals _ [h] = []
              | mkIntervals p (h1::(h2::t)) = (case p + (h1 + h2) of p' => p' :: mkIntervals p' (h2::t))
            val intervals = 0.0 :: mkIntervals 0.0 widthEstimates
            val cssize = List.last intervals
            fun calcX j = ~cssize/2.0 + List.nth(intervals,j)
            fun crec _ [] = []
              | crec j (ct::cts) = construction' (x + (calcX j), y-2.0) (SOME constructorNodeName) (j+1) ct :: crec (j+1) cts
        in (case parentName of
              NONE => lines ([tn,cn,cn2tn] @ (crec 0 cs))
            | SOME pn =>
                let val tn2parent = arrowLabelled (nodeNameOfToken token) pn i
                in lines ([tn,tn2parent,cn,cn2tn] @ (crec 0 cs))
                end)
        end

  fun construction coor ct =
    let val opening = "\\begin{tikzpicture}[construction,align at top]"
        val closing = "\\end{tikzpicture}"
    in lines [opening, construction' coor NONE 0 ct, closing]
    end

  fun mkDocument content =
    let val opening = "\\documentclass[a3paper,10pt]{article}\n "^
                      "\\usepackage[margin=2.5cm]{geometry}\n "^
                      "\\input{commands.sty}\n"^
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
