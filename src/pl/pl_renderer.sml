import "core.construction";
import "latex.latex";

signature RENDERPL = sig
    val drawBdd: Construction.construction -> unit;
    val drawVenn: Construction.construction -> unit;
    val drawPl: Construction.construction -> string;
end;

structure RenderPL : RENDERPL = struct

datatype bddExpr = FLIP of bddExpr 
                  |ZERO of bddExpr * bddExpr
                  |ONE of bddExpr * bddExpr
                  |VAR of string
                  |REMOVE of bddExpr
                  |BTRUE 
                  |BFALSE
exception BddError;

datatype tree = NODE of string * tree * tree
               |LF of bool

datatype vennExpr = CONT of vennExpr 
                    |ADD of string * vennExpr
                    |OR of vennExpr * vennExpr 
                    |AND of vennExpr * vennExpr
                    |IMPLY of vennExpr * vennExpr 
                    |IFF of vennExpr * vennExpr 
                    |ID of string 
                    |VTRUE 
                    |VFALSE
exception VennError;

fun drawBdd x =
  let fun parseBdd x =
        let fun tempParse xs (Construction.Source(x)) = 
                    let val t = #1 x in 
                    if String.substring(#2 x, 0, 1)="1" then ([(t, BTRUE)], BTRUE)
                    else if String.substring(#2 x, 0, 1)="0" then ([(t, BFALSE)], BFALSE)
                    else ([(t, VAR(String.substring(#2 x, 0, 1)))], VAR(String.substring(#2 x, 0, 1)))
                    end
                |tempParse xs (Construction.TCPair(x,y)) = 
                    let val t = (#1 (#token x)) in 
                    if (#1 (#constructor x)) = "flip" then 
                        let val (t1, c1) = tempParse xs (hd(y)) in
                        ((t, FLIP(c1))::t1, FLIP(c1))
                        end
                    else if (#1 (#constructor x)) = "replace0" then 
                        let val (t1, c1) = tempParse xs (hd(y))
                            val (t2, c2) = tempParse (xs@t1) (List.last(y)) in
                        ((t, ZERO(c1, c2))::t1@t2, ZERO(c1, c2))
                        end
                    else if (#1 (#constructor x)) = "replace1" then 
                        let val (t1, c1) = tempParse xs (hd(y))
                            val (t2, c2) = tempParse (xs@t1) (List.last(y)) in
                        ((t, ONE(c1, c2))::t1@t2, ONE(c1, c2))
                        end
                    else if (#1 (#constructor x)) = "removeDup" then
                        let val (t1, c1) = tempParse xs (hd(y)) in
                        ((t, REMOVE(c1))::t1, REMOVE(c1))
                        end
                    else if (#1 (#constructor x)) = "addNodes" then 
                        let val (t1, c1) = tempParse xs (hd(y)) in
                        ((t, c1)::t1, c1)
                        end
                    else raise BddError
                    end
                |tempParse xs (Construction.Reference(x)) = 
                    let fun findToken xs tok =
                            case xs of
                            [] => raise BddError
                            |(t,x)::xs => if t=tok then x else findToken xs tok
                        val t = #1 x 
                        val c = findToken xs t in 
                        ([(t, c)], c)
                    end
            val (_, y) = tempParse [] x 
            in
            y
        end
      fun replace b xs ys =
        case xs of
        NODE(s,l,r) => NODE(s, replace b l ys, replace b r ys)
        |LF(x) => if x = b then ys else LF(x)
      fun remove xs ss =
        let fun f x ys = 
          case ys of
            [] => ("",true)
            |y::ys => let val (a,b) = y in 
                        if a = x then (a, b) else (f x ys) end in
          case xs of
            LF(x) => LF(x)
            |NODE(x, l, r) => 
              let val (a,b) = f x ss in
                if a = "" then let val m = remove l ((x,false)::ss)
                                  val n = remove r ((x,true)::ss) in
                                if m = n then m else NODE(x, m, n)
                                end
                else if b then remove r ss 
                else remove l ss
              end
        end
      fun addVar t xs ys =
        if xs = [] then t else 
        case ys of
        [] => t
        |y::ys => case t of
                  NODE(s,l,r) => if List.hd xs = y then NODE(s,addVar l (List.tl xs) ys, addVar r (List.tl xs) ys)
                              else if List.hd xs < y then NODE(s,addVar l (List.tl xs) (y::ys), addVar r (List.tl xs) (y::ys))
                              else let val t2 = addVar t xs ys in NODE(y, t2, t2) end
                  |_ => t
      fun merge xs ys :string list =
        case (xs, ys) of
        ([], _) => ys
        |(_, []) => xs
        |(x::xs, y::ys) => if x = y then x::merge xs ys
                        else if x < y then x::merge xs (y::ys)
                        else y::merge (x::xs) ys
      fun convertBdd BTRUE = (LF(true), [])
          |convertBdd BFALSE = (LF(false), [])
          |convertBdd (VAR(x)) = (NODE(String.map Char.toUpper x, LF(false), LF(true)), [String.map Char.toUpper x])
          |convertBdd (FLIP(x)) = 
            let fun calculateNOT xs = 
                  case xs of 
                  NODE(s,l,r) => NODE(s, calculateNOT l, calculateNOT r)
                  |LF(x) => LF(not x)
                val (x2, y2) = convertBdd x in
              (calculateNOT x2, y2)
            end
          |convertBdd (ZERO(x,y)) =
            let val (x2, y2) = convertBdd x 
                val (x3, y3) = convertBdd y in
              (replace false (addVar x2 y2 y3) x3, merge y2 y3)
            end
          |convertBdd (ONE(x,y)) =
            let val (x2, y2) = convertBdd x
                val (x3, y3) = convertBdd y in
              (replace true (addVar x2 y2 y3) x3, merge y2 y3)
            end
          |convertBdd (REMOVE(x)) =
            let val (x2, y2) = convertBdd x in
              (remove x2 [], y2)
            end
      fun toDocBdd x =
        case x of
        LF(x) => if x then "[1]" else "[0]"
        |NODE(s,l,r) => 
          let val x2 = toDocBdd l 
              val x3 = toDocBdd r in
          "["^s^x2^x3^"]"
          end
      val header = "\\documentclass[12pt,a4paper]{article}\n"^
                   "\\usepackage[margin=20mm]{geometry}\n"^
                   "\\usepackage{tikz}\n"^
                   "\\usepackage{forest}\n"^
                   "\\usetikzlibrary{arrows.meta}\n"^
                   "\\tikzset{0 my edge/.style={densely dashed, my edge}, my edge/.style={-{Stealth[]}}}\n"^
                   "\\forestset{BDT/.style={for tree={if n children=0{}{circle},draw,edge={my edge,},if n=1{edge+={0 my edge},}{},font=\\sffamily}}}\n"^
                   "\\begin{document}\n"^
                   "\\begin{forest}\n"^
                   "  BDT\n" 
      val footer = "\\end{forest}\n"^
                   "\\end{document}"
      val (x2, y2) = convertBdd (parseBdd x)
      val content = toDocBdd x2 
      val outputFile = TextIO.openOut "output/latex/bdd.tex";
      val _ = TextIO.output(outputFile, (header^content^"\n"^footer));
      val _ = TextIO.closeOut outputFile;
      in 
      ()
  end

fun drawVenn x =
  let fun parseVenn (Construction.Source(x)) = 
              if String.substring(#2 x, 0, 1)="1" then VTRUE
              else if String.substring(#2 x, 0, 1)="0" then VFALSE
              else ID(String.map Char.toUpper (String.substring(#2 x, 0, 1)))
          |parseVenn (Construction.TCPair(x,y)) =
            if (#1 (#constructor x)) = "contrast" then CONT(parseVenn (hd(y))) 
            else if (#1 (#constructor x)) = "addCircle" then 
              let val Construction.Source(x2) = hd(y) in         
                ADD((String.map Char.toUpper (String.substring(#2 x2, 0, 1))), parseVenn (List.last(y)))
              end
            else if (#1 (#constructor x)) = "addCircles" then parseVenn (hd(y))
            else if (#1 (#constructor x)) = "fillAnd" then AND(parseVenn (hd(y)), parseVenn (List.last(y)))
            else if (#1 (#constructor x)) = "fillOr" then OR(parseVenn (hd(y)), parseVenn (List.last(y)))
            else if (#1 (#constructor x)) = "fillImply" then IMPLY(parseVenn (hd(y)), parseVenn (List.last(y)))
            else if (#1 (#constructor x)) = "fillIff" then IFF(parseVenn (hd(y)), parseVenn (List.last(y)))
            else raise VennError
          |parseVenn _ = raise VennError
      fun union xs ys a b c=
        case (xs, ys) of
        (_,[]) => (a, b@xs, c@xs)
        |([],_) => (a@ys, b, c@ys)
        |(x::xs, y::ys) => if x=y then union xs ys a b (c@[x])
                          else if x<y then union xs (y::ys) a (b@[x]) (c@[x])
                          else union (x::xs) ys (a@[y]) b (c@[y])
      fun addCircles xs ys cs =
        let fun addVarP xs = 
                    case xs of
                    [] => []
                    |y::ys => y::y::(addVarP ys)
                fun addVarQ xs =
                    case xs of
                    [] => []
                    |x::y::ys => x::y::x::y::(addVarQ ys)
                    |_ => raise VennError in
          case cs of
          [] => ys
          |c::cs => if (xs = [] orelse c < (List.hd xs)) then addCircles xs (addVarP ys) cs
                    else if c > (List.last xs) then addCircles xs (ys@ys) cs
                    else addCircles xs (addVarQ ys) cs
        end
      fun convertVenn VTRUE = ([], [true])
          |convertVenn VFALSE = ([], [false])
          |convertVenn (ID(x)) = ([String.map Char.toUpper x], [false, true])
          |convertVenn (OR(x,y)) = 
            let fun calculateOR xs ys =   
                  case (xs, ys) of
                    ([], []) => []
                    |(x::xs, y::ys)  => (x orelse y) :: calculateOR xs ys
                    | _ => raise VennError
                val (x2, y2) = convertVenn x
                val (x3, y3) = convertVenn y 
                val (a,b,c) = union x2 x3 [] [] [] 
                val y2 = addCircles x2 y2 a 
                val y3 = addCircles x3 y3 b in
                (c, (calculateOR y2 y3))
            end
          |convertVenn (AND(x,y)) = 
            let fun calculateAND xs ys =
                    case (xs, ys) of
                    ([], []) => []
                    |(x::xs, y::ys)  => (x andalso y) :: calculateAND xs ys
                    | _ => raise VennError
                val (x2, y2) = convertVenn x
                val (x3, y3) = convertVenn y
                val (a,b,c) = union x2 x3 [] [] [] 
                val y2 = addCircles x2 y2 a 
                val y3 = addCircles x3 y3 b in
                (c, (calculateAND y2 y3))
            end
          |convertVenn (IMPLY(x,y)) = 
            let fun calculateIMPLY xs ys =
                    case (xs, ys) of
                    ([], []) => []
                    |(x::xs, y::ys)  => ((not x) orelse (x andalso y)) :: calculateIMPLY xs ys
                    | _ => raise VennError
                val (x2, y2) = convertVenn x
                val (x3, y3) = convertVenn y
                val (a,b,c) = union x2 x3 [] [] [] 
                val y2 = addCircles x2 y2 a 
                val y3 = addCircles x3 y3 b in
                (c, (calculateIMPLY y2 y3))
            end
          |convertVenn (IFF(x,y)) = 
            let fun calculateIFF xs ys =
                    case (xs, ys) of
                    ([], []) => []
                    |(x::xs, y::ys)  => ((x andalso y) orelse (not x andalso not y)) :: calculateIFF xs ys
                    | _ => raise VennError
                val (x2, y2) = convertVenn x
                val (x3, y3) = convertVenn y 
                val (a,b,c) = union x2 x3 [] [] [] 
                val y2 = addCircles x2 y2 a 
                val y3 = addCircles x3 y3 b in
                (c, (calculateIFF y2 y3))
            end
          |convertVenn (CONT(x)) = 
            let fun calculateNOT xs = 
                    case xs of
                    [] => []
                    |x::xs => (not x) :: (calculateNOT xs)
                val (x2, y2) = convertVenn x in
              (x2, (calculateNOT y2))
            end
          |convertVenn (ADD(x,y)) =
            let fun addVarP xs = 
                    case xs of
                    [] => []
                    |y::ys => y::y::(addVarP ys)
                fun addVarQ xs =
                    case xs of
                    [] => []
                    |x::y::ys => x::y::x::y::(addVarQ ys)
                    |_ => raise VennError
                val (x2,y2) = convertVenn y in
              if x < hd(x2) then (x::x2, (addVarP y2))
              else if x > List.last(x2) then (x2@[x], (y2@y2))
              else (hd(x2)::x::tl(x2), (addVarQ y2))
            end
      fun toDocVenn x y =
        let fun toColor ys = 
              case ys of
              [] => []
              |x::xs => if x then "white"::(toColor xs)
                        else "gray"::(toColor xs)
            val ys = toColor y in
              case length(x) of
              0 => "\\filldraw[fill="^hd(ys)^"] (-1.5,-1.2) rectangle (1.5,1.2);\n"
              |1 => "\\filldraw[fill="^List.nth(ys, 0)^"] (-1.5,-1.2) rectangle (1.5,1.2);\n"^
                    "\\node[set,label={135:$"^List.nth(x, 0)^"$},fill="^List.nth(ys, 1)^"] at (0,0) {};\n"^
                    "\\draw (0,0) circle(0.8cm);\n"
              |2=>  "\\filldraw[fill="^List.nth(ys, 0)^"] (-1.5,-1.5) rectangle (2.5,1.5);\n"^
                    "\\node[set,label={135:$"^List.nth(x, 0)^"$},fill="^List.nth(ys, 1)^"] at (0,0) {};\n"^
                    "\\node[set,label={45:$"^List.nth(x, 1)^"$},fill="^List.nth(ys, 2)^"] at (1.0,0) {};\n"^
                    "\\begin{scope}\n"^
                    "\\clip (0,0) circle(0.8cm);\n"^
                    "\\clip (1.0,0) circle(0.8cm);\n"^
                    "\\fill["^List.nth(ys, 3)^"](0,0) circle(0.8cm);\n"^
                    "\\end{scope}\n"^
                    "\\draw (0,0) circle(0.8cm);\n"^
                    "\\draw (1.0,0) circle(0.8cm);\n"
              |3 => "\\filldraw[fill="^List.nth(ys, 0)^"] (-2,-1.5) rectangle (3,2.8);\n"^
                    "\\node[set,label={135:$"^List.nth(x, 1)^"$},fill="^List.nth(ys, 2)^"] at (0,0) {};\n"^
                    "\\node[set,label={45:$"^List.nth(x, 2)^"$},fill="^List.nth(ys, 4)^"] at (1.0,0) {};\n"^
                    "\\node[set,label=$"^List.nth(x, 0)^"$,fill="^List.nth(ys, 1)^"] at (0.5,1.0) {};\n"^
                    "\\begin{scope}\n"^
                    "\\clip (0,0) circle(0.8cm);\n"^
                    "\\clip (0.5,1.0) circle(0.8cm);\n"^
                    "\\fill["^List.nth(ys, 3)^"](0,0) circle(0.8cm);\n"^
                    "\\end{scope}\n"^
                    "\\begin{scope}\n"^
                    "\\clip (1.0,0) circle(0.8cm);\n"^
                    "\\clip (0.5,1.0) circle(0.8cm);\n"^
                    "\\fill["^List.nth(ys, 5)^"](1.0,0) circle(0.8cm);\n"^
                    "\\end{scope}\n"^
                    "\\begin{scope}\n"^
                    "\\clip (0,0) circle(0.8cm);\n"^
                    "\\clip (1.0,0) circle(0.8cm);\n"^
                    "\\fill["^List.nth(ys, 6)^"](0,0) circle(0.8cm);\n"^
                    "\\end{scope}\n"^
                    "\\begin{scope}\n"^
                    "\\clip (0,0) circle(0.8cm);\n"^
                    "\\clip (1.0,0) circle(0.8cm);\n"^
                    "\\clip (0.5,1.0) circle(0.8cm);\n"^
                    "\\fill["^List.nth(ys, 7)^"](0,0) circle(0.8cm);\n"^
                    "\\end{scope}\n"^
                    "\\draw (0,0) circle(0.8cm);\n"^
                    "\\draw (1.0,0) circle(0.8cm);\n"^
                    "\\draw (0.5,1.0) circle(0.8cm);\n"
              |_ => raise VennError
            end
      val header = "\\documentclass[12pt,a4paper]{article}\n"^
                   "\\usepackage[margin=20mm]{geometry}\n"^
                   "\\usepackage{tikz}\n"^
                   "\\begin{document}\n"^
                   "\\begin{tikzpicture}[thick, set/.style = {circle, minimum size = 1.6cm, fill=gray}]\n" 
      val footer = "\\end{tikzpicture}\n"^
                  "\\end{document}"
      val (x2, y2) = convertVenn (parseVenn x)
      val content = toDocVenn x2 y2
      val outputFile = TextIO.openOut "output/latex/venn.tex";
      val _ = TextIO.output(outputFile, (header^content^footer));
      val _ = TextIO.closeOut outputFile;
      in 
      ()
  end

fun drawPl x =
    let fun parsePl (Construction.Source(x)) =
                if String.substring(#2 x, 0, 4)="true" then TRUE
                else if String.substring(#2 x, 0, 5)="false" then FALSE
                else ID(String.substring(#2 x, 0, 1))
            |parsePl (Construction.TCPair(x,y)) =
                if (#1 (#constructor x)) = "unaryOp" then NOT(parsePl (List.last (y))) 
                else if (#1 (#constructor x)) = "infixOp" then
                    let val x = parsePl (List.nth (y,0)) 
                        val Construction.Source(z) = List.nth (y,1)
                        val y = parsePl (List.nth (y,2)) in
                    case (#2 z) of
                    "or" => OR(x,y)
                    |"and" => AND(x,y)
                    |"imply" => IMPLY(x,y)
                    |"iff" => IFF(x,y)
                    |_ => raise PLError
                    end
                else if (#1 (#constructor x)) = "addParentheses" then 
                    let val x = parsePl (List.nth (y,1)) in
                    PAREN(x) 
                    end
                else raise PLError
            |parsePl _ = raise PLError
        fun convertPl TRUE = "true"
            |convertPl FALSE = "false"
            |convertPl (ID(x)) = x
            |convertPl (NOT(x)) = let val x2 = convertPl x in "!"^x2 end
            |convertPl (PAREN(x)) = let val x2 = convertPl x in "("^x2^")" end
            |convertPl (OR(x,y)) = 
                let val x2 = convertPl x
                    val y2 = convertPl y in
                x2^"+"^y2
                end
            |convertPl (AND(x,y)) = 
                let val x2 = convertPl x
                    val y2 = convertPl y in
                x2^"*"^y2
                end
            |convertPl (IMPLY(x,y)) = 
                let val x2 = convertPl x
                    val y2 = convertPl y in
                x2^">"^y2
                end
            |convertPl (IFF(x,y)) = 
                let val x2 = convertPl x
                    val y2 = convertPl y in
                x2^"<>"^y2
                end
        val y = convertPl (parsePl x) in
      y
    end;

end;