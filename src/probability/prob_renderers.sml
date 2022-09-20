import "core.construction";
import "works.prob_num";

signature PROBRENDER = sig
    val drawArea: Construction.construction -> (string * (string*real*real)) list; 
    val drawTable: Construction.construction -> (string * (string*real*real)) list;
    val drawTree: Construction.construction -> (string * (string*real*real)) list;
    val drawBayes: Construction.construction -> (string * (string*real*real)) list;
end;

structure ProbRender : PROBRENDER = struct

datatype shading = BLUE
                  |WHITE
                  |RED
                  |GREEN
                  |PATTERN
exception ShadeError;

datatype eventExp = SEVENT of string
                    |NEVENT of string

type shadeList = eventExp list * shading list;
type shadeInt = eventExp list * int;

datatype areaExp = EMPTY
                  |LABEL of string
                  |NLABEL of string
                  |POINT of ProbNum.numExp * ProbNum.numExp
                  |RECT of areaExp * areaExp
                  |OVERLAY of string * areaExp * areaExp * areaExp * shading
                  |ADDAREA of string * areaExp * shadeList
                  |COMBAREA of string * areaExp * areaExp
exception AreaError;

datatype tableExp = NAME of string
                    |NNAME of string
                    |ONEWAY of string * tableExp * ProbNum.numExp
                    |TWOWAY of string * tableExp * tableExp * ProbNum.numExp
                    |COMB of string * tableExp * tableExp
                    |CTABLE of string * tableExp * shadeList
exception TableError;

datatype treeExp = BRANCH of string
                  |NBRANCH of string
                  |TREE of string * treeExp * ProbNum.numExp
                  |ADD of string * treeExp * treeExp * ProbNum.numExp
                  |RESOLVE of string * treeExp * treeExp
                  |CTREE of string * treeExp * shadeInt
exception TreeError;

exception BayesError;

fun eventToString (SEVENT(x)) = x
    |eventToString (NEVENT(x)) = x

fun parseShading (Construction.Source(x)) =
    let val a = #2 x 
        val b = #1 x in
        if String.substring(a,0,3) = "red" then (RED,[(b,"RED",3.0)])
        else if String.substring(a,0,4) = "blue" then (BLUE,[(b,"BLUE",4.0)])
        else if String.substring(a,0,5) = "white" then (WHITE,[(b,"WHITE",5.0)])
        else if String.substring(a,0,5) = "green" then (GREEN,[(b,"GREEN",5.0)])
        else if String.substring(a,0,7) = "pattern" then (PATTERN,[(b,"PATTERN",6.0)])
        else (WHITE,[(b,"WHITE",5.0)])
    end
    |parseShading _ = raise ShadeError;

fun concatAll xs =
    case xs of
        [] => ""
        |(x,(y,_,_))::xs => "<p>"^x^"</p>\n"^y^"\n"^(concatAll xs)

fun stringToHTML xs =
    case xs of
    [] => []
    |(a,b,c)::xs => if b = "EMPTY" then (a,("<div>\n"^
                                            "<svg width=\"200\" height=\"200\">\n"^
                                            "<rect width=\"200\" height=\"200\" style=\"fill:white;stroke-width:1;stroke:black\"/>\n"^
                                            "</svg>\n"^
                                            "</div>",
                                            200.0,200.0))::stringToHTML xs
                    else let val mid = c*5.0
                             val len = c*10.0 in 
                                (a,("<div>\n"^
                                    "<svg width=\""^(Real.toString len)^"\" height=\"18\" font-size=\"12px\">\n"^
                                    "<rect width=\""^(Real.toString len)^"\" height=\"18\" fill=\"#d9d9d9\"/>\n"^
                                    "<text text-anchor=\"middle\" transform=\"translate("^(Real.toString mid)^",13)\">"^b^"</text>\n"^
                                    "</svg>\n"^
                                    "</div>",
                                    len,18.0))::stringToHTML xs
                         end

fun drawArea x =
    let fun parseAreaShading (Construction.Source(x)) =
                if String.substring((#2 x), 0, 5) = "empty" then ([],[])
                else raise AreaError
            |parseAreaShading (Construction.TCPair(x,y)) =
                if (#1 (#constructor x)) = "colour" then
                    let val (x1, y1) = parseAreaShading (hd(y))
                        val (x2,_) = parseArea (List.nth(y, 1))
                        val (x3,_) = parseShading (List.last(y)) in
                        if x1 = [] then
                            (case x2 of
                            LABEL(a)     => ([SEVENT(a)],[x3,WHITE])
                            |NLABEL(a)   => ([NEVENT(a)],[WHITE,x3])
                            |_ => raise AreaError)
                        else (case (hd(x1), x2) of
                            (SEVENT(a), LABEL(b))   => (x1@[SEVENT(b)], y1@[x3,WHITE,WHITE,WHITE])
                            |(SEVENT(a), NLABEL(b)) => (x1@[NEVENT(b)], y1@[WHITE,x3,WHITE,WHITE])
                            |(NEVENT(a), LABEL(b))  => (x1@[SEVENT(b)], y1@[WHITE,WHITE,x3,WHITE])
                            |(NEVENT(a), NLABEL(b)) => (x1@[NEVENT(b)], y1@[WHITE,WHITE,WHITE,x3])
                            |_ => raise AreaError)
                    end
                else raise AreaError
            |parseAreaShading _ = raise AreaError
        and parseArea (Construction.Source(x)) =
                if String.isSubstring "empty" (#2 x) then (EMPTY,[(#1 x,"EMPTY",0.0)])
                else (case String.breakOn ":" (#2 x) of
                        (a,":",_) => (LABEL(a),[(#1 x,a,Real.fromInt(String.size a)+0.5)])
                        |_ => raise AreaError)
            |parseArea (Construction.TCPair(x,y)) =
                if (#1 (#constructor x)) = "reverseTag" then 
                    (case (parseArea (hd(y))) of
                        (LABEL(a),b) => (NLABEL(a),[((#1 (hd(b))),"<tspan text-decoration=\"overline\">"^(#2 (hd(b)))^"</tspan>",(#3 (hd(b))))])
                        |_ => raise AreaError)
                else if (#1 (#constructor x)) = "cPoint" then 
                    let val (x1,z1) = ProbNum.parseNum (hd(y))
                        val (x2,z2) = ProbNum.parseNum (List.last(y)) in
                        (POINT(x1,x2),(#1 (#token x),"("^(#2 (hd(z1)))^","^(#2 (hd(z2)))^")",(#3 (hd(z1)))+(#3 (hd(z2))))::z1@z2)
                    end
                else if (#1 (#constructor x)) = "cRect" then 
                    let val (x1,y1) = parseArea (hd(y))
                        val (x2,y2) = parseArea (List.last(y)) in
                        (RECT(x1,x2),(#1 (#token x),(#2 (hd(y1)))^" - "^(#2 (hd(y2))),(#3 (hd(y1)))+(#3 (hd(y2)))+0.5)::y1@y2)
                    end
                else if (#1 (#constructor x)) = "overlayRect" then 
                    let val (x1,y1) = parseArea (hd(y))
                        val (x2,y2) = parseArea (List.nth(y,1))
                        val (x3,y3) = parseArea (List.nth(y,2))
                        val (x4,y4) = parseShading (List.last(y)) in
                        (OVERLAY((#1 (#token x)),x1,x2,x3,x4),y1@y2@y3@y4)
                    end
                else if (#1 (#constructor x)) = "combine" then 
                    let val (x1,y1) = parseArea (hd(y))
                        val (x2,y2) = parseArea (List.last(y)) in
                        (COMBAREA((#1 (#token x)),x1,x2),y1@y2)
                    end
                else if (#1 (#constructor x)) = "addColour" then 
                    let val (x1,y1) = parseArea (hd(y))
                        val x2 = parseAreaShading (List.last(y)) in
                        (ADDAREA((#1 (#token x)),x1,x2),y1)
                    end
                else raise AreaError
            |parseArea (Construction.Reference(x)) = raise AreaError
        fun convertArea EMPTY = (([],[],[],[],[]),[])
            |convertArea (LABEL(x)) = (([SEVENT(x)],[],[],[],[]),[])
            |convertArea (NLABEL(x)) = (([NEVENT(x)],[],[],[],[]),[])
            |convertArea (POINT(x,y)) = (([],[x,y],[],[],[]),[])
            |convertArea (RECT(x,y)) = 
                let val ((_,y2,_,_,_),_) = convertArea x
                    val ((_,y3,_,_,_),_) = convertArea y in 
                    (([],y2@y3,[],[],[]),[])
                end
            |convertArea (OVERLAY(m,x,y,z,w)) = 
                let fun flipShading x =
                        case x of 
                        BLUE => RED
                        |RED => BLUE
                        |_ => x
                    val ((x1,y1,z1,w1,_),n) = convertArea x
                    val ((_,y2,_,_,_),_) = convertArea y
                    val ((x3,_,_,_,_),_) = convertArea z in
                    if w1 = [] then 
                        case (hd(x3)) of
                        SEVENT(a) => ((x3,y2,[w],[List.nth(y2,2),ProbNum.MINUS(ProbNum.NUM(1),List.nth(y2,2))],[]),(m,x3,y2,[w],[List.nth(y2,2),ProbNum.MINUS(ProbNum.NUM(1),List.nth(y2,2))],[])::n)
                        |NEVENT(a) => ((x3,[ProbNum.MINUS(ProbNum.NUM(1),List.nth(y2,2)),ProbNum.NUM(0),ProbNum.NUM(1),ProbNum.NUM(1)],[(flipShading w)],[ProbNum.MINUS(ProbNum.NUM(1),List.nth(y2,2)),List.nth(y2,2)],[]),(m,x3,[ProbNum.MINUS(ProbNum.NUM(1),List.nth(y2,2)),ProbNum.NUM(0),ProbNum.NUM(1),ProbNum.NUM(1)],[(flipShading w)],[ProbNum.MINUS(ProbNum.NUM(1),List.nth(y2,2)),List.nth(y2,2)],[])::n)
                    else case (hd(x1),hd(x3)) of
                        (SEVENT(_),SEVENT(_)) => ((x1@x3,y1@y2,z1@[w],w1@[List.nth(y2,3),ProbNum.MINUS(ProbNum.NUM(1),List.nth(y2,3))],[]),(m,x1@x3,y1@y2,z1@[w],w1@[List.nth(y2,3),ProbNum.MINUS(ProbNum.NUM(1),List.nth(y2,3))],[])::n)
                        |(SEVENT(_),NEVENT(_)) => ((x1@x3,y1@[List.nth(y2,0),ProbNum.MINUS(ProbNum.NUM(1),List.nth(y2,3)),List.nth(y2,2),ProbNum.NUM(1)],z1@[(flipShading w)],w1@[ProbNum.MINUS(ProbNum.NUM(1),List.nth(y2,3)),List.nth(y2,3)],[]),(m,x1@x3,y1@[List.nth(y2,0),ProbNum.MINUS(ProbNum.NUM(1),List.nth(y2,3)),List.nth(y2,2),ProbNum.NUM(1)],z1@[(flipShading w)],w1@[ProbNum.MINUS(ProbNum.NUM(1),List.nth(y2,3)),List.nth(y2,3)],[])::n)
                        |(NEVENT(_),SEVENT(_)) => ((x1@x3,y1@[List.nth(y1,0),List.nth(y2,1),List.nth(y1,2),List.nth(y2,3)],z1@[w],w1@[List.nth(y2,3),ProbNum.MINUS(ProbNum.NUM(1),List.nth(y2,3))],[]),(m,x1@x3,y1@[List.nth(y1,0),List.nth(y2,1),List.nth(y1,2),List.nth(y2,3)],z1@[w],w1@[List.nth(y2,3),ProbNum.MINUS(ProbNum.NUM(1),List.nth(y2,3))],[])::n)
                        |(NEVENT(_),NEVENT(_)) => ((x1@x3,y1@[List.nth(y1,0),ProbNum.MINUS(ProbNum.NUM(1),List.nth(y2,3)),List.nth(y1,2),ProbNum.NUM(1)],z1@[(flipShading w)],w1@[ProbNum.MINUS(ProbNum.NUM(1),List.nth(y2,3)),List.nth(y2,3)],[]),(m,x1@x3,y1@[List.nth(y1,0),ProbNum.MINUS(ProbNum.NUM(1),List.nth(y2,3)),List.nth(y1,2),ProbNum.NUM(1)],z1@[(flipShading w)],w1@[ProbNum.MINUS(ProbNum.NUM(1),List.nth(y2,3)),List.nth(y2,3)],[])::n)
                end
            |convertArea (COMBAREA(m,x,y)) =
                let fun toRects ws = [ProbNum.NUM(0),ProbNum.NUM(0),(hd(ws)),ProbNum.NUM(1),ProbNum.NUM(0),ProbNum.NUM(0),(hd(ws)),(List.nth(ws,2)),(hd(ws)),ProbNum.NUM(0),ProbNum.NUM(1),(List.nth(ws,4))]
                    fun mergeShading x y = 
                        if x = PATTERN then y
                        else if y = PATTERN then x
                        else if x = WHITE then y
                        else x
                    fun extractNum x y w =
                        if List.length x = 1 then w@[ProbNum.U,ProbNum.U,ProbNum.U,ProbNum.U]
                        else if List.length w = 6 then w
                        else case (hd(x)) of
                            SEVENT(a) => w@[ProbNum.U,ProbNum.U]
                            |NEVENT(a) => List.take(w,2)@[ProbNum.U,ProbNum.U]@List.drop(w,2)
                    fun areaMerge x2 y2 a x3 y3 b =
                        let fun ff b =
                                if List.nth(b,2) = ProbNum.U then 
                                let val xs = [ProbNum.VAR("z"),ProbNum.MINUS(ProbNum.NUM(1),ProbNum.VAR("z")),
                                            ProbNum.MINUS(ProbNum.NUM(1),ProbNum.FRAC(ProbNum.MULT(List.nth(b,4),List.nth(b,1)),ProbNum.VAR("z"))), ProbNum.FRAC(ProbNum.MULT(List.nth(b,4),List.nth(b,1)),ProbNum.VAR("z")), 
                                            ProbNum.MINUS(ProbNum.NUM(1),ProbNum.FRAC(ProbNum.MULT(List.nth(b,5),List.nth(b,1)),ProbNum.MINUS(ProbNum.NUM(1),ProbNum.VAR("z")))),ProbNum.FRAC(ProbNum.MULT(List.nth(b,5),List.nth(b,1)),ProbNum.MINUS(ProbNum.NUM(1),ProbNum.VAR("z")))]
                                    val xss = List.map ProbNum.simplify xs in 
                                    (xss, (toRects xss))
                                end
                                else if List.nth(b,4) = ProbNum.U then 
                                let val xs = [ProbNum.VAR("z"), ProbNum.MINUS(ProbNum.NUM(1),ProbNum.VAR("z")),
                                              ProbNum.FRAC(ProbNum.MULT(List.nth(b,2),List.nth(b,0)),ProbNum.VAR("z")), ProbNum.MINUS(ProbNum.NUM(1),ProbNum.FRAC(ProbNum.MULT(List.nth(b,2),List.nth(b,0)),ProbNum.VAR("z"))),
                                              ProbNum.FRAC(ProbNum.MULT(List.nth(b,3),List.nth(b,0)),ProbNum.MINUS(ProbNum.NUM(1),ProbNum.VAR("z"))), ProbNum.MINUS(ProbNum.NUM(1),ProbNum.FRAC(ProbNum.MULT(List.nth(b,3),List.nth(b,0)),ProbNum.MINUS(ProbNum.NUM(1),ProbNum.VAR("z"))))]
                                    val xss = List.map ProbNum.simplify xs in 
                                    (xss, (toRects xss))
                                end
                                else let val xs = [ProbNum.PLUS(ProbNum.MULT(List.nth(b,2),List.nth(b,0)),ProbNum.MULT(List.nth(b,4),List.nth(b,1))), ProbNum.PLUS(ProbNum.MULT(List.nth(b,3),List.nth(b,0)),ProbNum.MULT(List.nth(b,5),List.nth(b,1))), 
                                                   ProbNum.FRAC(ProbNum.MULT(List.nth(b,2), List.nth(b,0)),ProbNum.PLUS(ProbNum.MULT(List.nth(b,2),List.nth(b,0)),ProbNum.MULT(List.nth(b,4),List.nth(b,1)))), ProbNum.FRAC(ProbNum.MULT(List.nth(b,4), List.nth(b,1)),ProbNum.PLUS(ProbNum.MULT(List.nth(b,2),List.nth(b,0)),ProbNum.MULT(List.nth(b,4),List.nth(b,1)))), 
                                                   ProbNum.FRAC(ProbNum.MULT(List.nth(b,3),List.nth(b,0)),ProbNum.PLUS(ProbNum.MULT(List.nth(b,3),List.nth(b,0)),ProbNum.MULT(List.nth(b,5),List.nth(b,1)))),  ProbNum.FRAC(ProbNum.MULT(List.nth(b,5),List.nth(b,1)),ProbNum.PLUS(ProbNum.MULT(List.nth(b,3),List.nth(b,0)),ProbNum.MULT(List.nth(b,5),List.nth(b,1))))] 
                                        val xss = List.map ProbNum.simplify xs in 
                                    (xss, (toRects xss))
                                end 
                            in
                            if eventToString (hd(x2)) = eventToString (hd(x3)) then 
                                let fun merger a b y2 y3 c d e f =
                                        case (a,b) of
                                        ([],[]) => ((List.rev c),(List.rev d),e,f)
                                        |(x::xxs::xs,y::yys::ys) => if x = ProbNum.U andalso y = ProbNum.U then merger xs ys y2 y3 c d e f
                                                                    else if x = ProbNum.U then merger xs ys y2 (List.drop(y3,4)) (xxs::x::c) (yys::y::d) (e@[ProbNum.U,ProbNum.U,ProbNum.U,ProbNum.U]) (f@(List.take(y3,4)))
                                                                    else if y = ProbNum.U then merger xs ys (List.drop(y2,4)) y3 (xxs::x::c) (yys::y::d) (e@(List.take(y2,4))) (f@[ProbNum.U,ProbNum.U,ProbNum.U,ProbNum.U])
                                                                    else merger xs ys (List.drop(y2,4)) (List.drop(y3,4)) (xxs::x::c) (yys::y::d) (e@(List.take(y2,4))) (f@(List.take(y3,4)))
                                        |_ => raise AreaError
                                    val (c,d,e,f) = merger a b y2 y3 [] [] [] [] in
                                    if List.length x2 > List.length x3 then (x2, c, d, e, f)
                                    else (x3, c, d, e, f)
                                end
                            else if List.length x2 = List.length x3 andalso List.length x2 = 1 then 
                                let val xss = [ProbNum.VAR("z"),ProbNum.MINUS(ProbNum.NUM(1),ProbNum.VAR("z")), ProbNum.VAR("x"), ProbNum.MINUS(ProbNum.NUM(1),ProbNum.VAR("x")), ProbNum.FRAC(ProbNum.MINUS(hd(b),ProbNum.MULT(ProbNum.VAR("z"),ProbNum.VAR("x"))),ProbNum.MINUS(ProbNum.NUM(1),ProbNum.VAR("z"))), ProbNum.MINUS(ProbNum.NUM(1),ProbNum.FRAC(ProbNum.MINUS(hd(b),ProbNum.MULT(ProbNum.VAR("z"),ProbNum.VAR("x"))),ProbNum.MINUS(ProbNum.NUM(1),ProbNum.VAR("z"))))] in 
                                    (x2@x3, a, xss, y2@[ProbNum.U,ProbNum.U,ProbNum.U,ProbNum.U,ProbNum.U,ProbNum.U,ProbNum.U,ProbNum.U], (toRects xss))
                                end 
                            else if List.length x2 = List.length x3 andalso List.length y2 = 8 then 
                                let val (xss,yss) = ff b in (x2, a, xss, (y2@[ProbNum.U,ProbNum.U,ProbNum.U,ProbNum.U]), yss) end
                            else if List.length x2 = List.length x3 then
                                let val (xss,yss) = ff b in (x2, a, xss, y2, yss) end
                            else if List.length x3 > List.length x2 then
                                let val (xss,yss) = ff b in ((List.rev x3), a, xss, (y2@[ProbNum.U,ProbNum.U,ProbNum.U,ProbNum.U,ProbNum.U,ProbNum.U,ProbNum.U,ProbNum.U]), yss) end
                            else let val (xss,yss) = ff a in ((List.rev x2), xss, b, yss, (y3@[ProbNum.U,ProbNum.U,ProbNum.U,ProbNum.U,ProbNum.U,ProbNum.U,ProbNum.U,ProbNum.U])) end
                        end
                    val ((x2,y2,z2,w2,_),n1) = convertArea x
                    val ((x3,y3,z3,w3,_),n2) = convertArea y 
                    val (x, c, d, e, f) = areaMerge x2 y2 (extractNum x2 y2 w2) x3 y3 (extractNum x3 y3 w3)
                    val g = ProbNum.resolve (c@e) (d@f) (List.length c) in
                    if List.length g = 12 then ((x,(List.drop(g,4)),[(mergeShading (hd(z2)) (hd(z3))),PATTERN],List.take(g,4),[]),(m,x,(List.drop(g,4)), [(mergeShading (hd(z2)) (hd(z3))),PATTERN],List.take(g,4),[])::n1@n2)
                    else ((x,(toRects (List.take(g,6))),[WHITE,BLUE,RED],List.take(g,6),[]),(m,x,(toRects (List.take(g,6))),[WHITE,BLUE,RED],List.take(g,6),[])::n1@n2)
                end
            |convertArea (ADDAREA(m,x,y)) =
                let fun toWhite xs =
                        case xs of 
                        [] => []
                        |x::xs => WHITE::(toWhite xs)
                    fun changeShade l n new =
                        if n = 0 then new::(tl(l))
                        else (hd(l))::changeShade (tl(l)) (n-1) new
                    fun addRect xs ws n =
                        case xs of
                        [] => []
                        |x::xs => if x = WHITE then addRect xs ws (n+1)
                                else case n of
                                        0 => ([ProbNum.NUM(0),ProbNum.NUM(0),(hd(ws)),ProbNum.NUM(1)], x)::addRect xs ws (n+1)
                                        |1 => ([(hd(ws)),ProbNum.NUM(0),ProbNum.NUM(1),ProbNum.NUM(1)], x)::addRect xs ws (n+1)
                                        |2 => ([ProbNum.NUM(0),ProbNum.NUM(0),(hd(ws)),(List.nth(ws,2))], x)::addRect xs ws (n+1)
                                        |3 => ([ProbNum.NUM(0),(List.nth(ws,2)),(hd(ws)),ProbNum.NUM(1)], x)::addRect xs ws (n+1)
                                        |4 => ([(hd(ws)),ProbNum.NUM(0),ProbNum.NUM(1),(List.nth(ws,4))], x)::addRect xs ws (n+1)
                                        |5 => ([(hd(ws)),(List.nth(ws,4)),ProbNum.NUM(1),ProbNum.NUM(1)], x)::addRect xs ws (n+1)
                                        |_ => addRect xs ws (n+1)
                    fun revert xs l ws n =
                        case xs of
                        [] => []
                        |x::xs => if x = WHITE then revert xs l ws (n+1)
                                else case n of
                                        0 => (addRect (changeShade (changeShade (toWhite l) 4 x) 2 x) ws 0)@(revert xs l ws (n+1))
                                        |1 => (addRect (changeShade (changeShade (toWhite l) 5 x) 3 x) ws 0)@(revert xs l ws (n+1))
                                        |2 => (addRect (changeShade (toWhite l) 2 x) ws 0)@(revert xs l ws (n+1))
                                        |3 => (addRect (changeShade (toWhite l) 4 x) ws 0)@(revert xs l ws (n+1))
                                        |4 => (addRect (changeShade (toWhite l) 3 x) ws 0)@(revert xs l ws (n+1))
                                        |5 => (addRect (changeShade (toWhite l) 5 x) ws 0)@(revert xs l ws (n+1))
                                        |_ => revert xs l ws (n+1)
                    val ((x2,y2,z2,w2,_),n) = convertArea x
                    val (x3,y3) = y in
                    if List.length x2 = List.length x3 andalso eventToString (hd(x2)) = eventToString (hd(x3)) then ((x2,y2,(toWhite z2),w2,addRect y3 w2 0),(m,x2,y2,(toWhite z2),w2,addRect y3 w2 0)::n)
                    else if List.length x2 = List.length x3 andalso List.length x2 = 2 then ((x2,y2,(toWhite z2),w2, (revert y3 y3 w2 0)),(m,x2,y2,(toWhite z2),w2, (revert y3 y3 w2 0))::n)
                    else if List.length x2 = List.length x3 then ((x2@x3,y2,(toWhite z2),w2, (revert y3 y3 w2 0)),(m,x2@x3,y2,(toWhite z2),w2, (revert y3 y3 w2 0))::n)
                    else if List.length x2 > List.length x3 andalso eventToString (hd(x2)) = eventToString (hd(x3)) then ((x2,y2,(toWhite z2),w2,addRect y3 w2 0),(m,x2,y2,(toWhite z2),w2,addRect y3 w2 0)::n)
                    else if List.length x2 > List.length x3 then ((x2,y2,(toWhite z2),w2,(revert y3 (y3@[WHITE,WHITE,WHITE,WHITE]) w2 0)),(m,x2,y2,(toWhite z2),w2,(revert y3 (y3@[WHITE,WHITE,WHITE,WHITE]) w2 0))::n)
                    else if List.length x2 < List.length x3 andalso eventToString (hd(x2)) = eventToString (hd(x3)) then ((x3,y2,(toWhite z2),w2,addRect y3 w2 0),(m,x3,y2,(toWhite z2),w2,addRect y3 w2 0)::n)
                    else ((List.rev x3,y2,(toWhite z2),w2,(revert y3 y3 w2 0)),(m,List.rev x3,y2,(toWhite z2),w2,(revert y3 y3 w2 0))::n)
                end
        fun areaToHTML (m,a,b,c,d,e) =
            let fun toNum x =
                    if ProbNum.onlyNum x then ProbNum.numToString (ProbNum.PLUS(ProbNum.NUM(30),ProbNum.MULT(ProbNum.NUM(200),x)))
                    else ProbNum.numToString (ProbNum.NUM(80))
                fun calcLen x y k n = 
                    if ProbNum.onlyNum x andalso ProbNum.onlyNum y then ProbNum.numToString (ProbNum.MULT(ProbNum.NUM(200),ProbNum.MINUS(x,y)))
                    else if ProbNum.numToString k = ProbNum.numToString (ProbNum.NUM(0)) then ProbNum.numToString (ProbNum.NUM(50))
                    else ProbNum.numToString (ProbNum.MULT(n,ProbNum.NUM(50)))
                fun calcMid x n =
                    if ProbNum.onlyNum x then ProbNum.numToString (ProbNum.PLUS(n,ProbNum.MULT(ProbNum.NUM(100),x)))
                    else ProbNum.numToString (ProbNum.PLUS(ProbNum.NUM(25),n))
                fun calcLab n =
                    if ProbNum.numToString n = ProbNum.numToString (ProbNum.NUM(0)) then ProbNum.numToString (ProbNum.NUM(15))
                    else ProbNum.numToString (ProbNum.NUM(245))
                fun shadeToString x =
                    case x of
                    BLUE => "#4d79ff"
                    |RED => "#ff4d4d"
                    |GREEN => "#39ac73"
                    |WHITE => "white"
                    |PATTERN => "url(#diagonalHatch)"
                fun rectToString xs =
                    case xs of
                    [] => ""
                    |(ns,c)::xs => "<rect width=\""^(calcLen (List.nth(ns,2)) (List.nth(ns,0)) (List.nth(ns,0)) (ProbNum.NUM(1)))^"\" height=\""^(calcLen (List.nth(ns,3)) (List.nth(ns,1)) (List.nth(ns,3)) (ProbNum.NUM(1)))^"\" transform=\"translate("^(toNum (List.nth(ns,0)))^","^(toNum (List.nth(ns,1)))^")\" style=\"fill:"^(shadeToString c)^";stroke-width:1;stroke:black\" />\n"^(rectToString xs)
                fun toDocArea (x,y,z,w,m) =
                    if List.length x = 1 then   "<rect width=\"200\" height=\"200\" transform=\"translate(30,30)\" style=\"fill:white;stroke-width:1;stroke:black\" />\n"^
                                                "<rect width=\""^(calcLen (List.nth(y,2)) (List.nth(y,0)) (List.nth(y,0)) (ProbNum.NUM(3)))^"\" height=\""^(calcLen (List.nth(y,3)) (List.nth(y,1)) (List.nth(y,3)) (ProbNum.NUM(1)))^"\" transform=\"translate("^(toNum (List.nth(y,0)))^","^(toNum (List.nth(y,1)))^")\" style=\"fill-opacity:50%;fill:"^(List.nth(z,0))^";stroke-width:1;stroke:black\" />\n"^m^
                                                "<text text-anchor=\"middle\" transform=\"translate("^(calcMid (List.nth(w,0)) (ProbNum.NUM(30)))^",10)\">"^(List.nth(x,0))^"</text>\n"^
                                                "<text text-anchor=\"middle\" transform=\"translate("^(calcMid (List.nth(w,0)) (ProbNum.NUM(30)))^",25)\">"^(ProbNum.numToString (List.nth(w,0)))^"</text>\n"
                    else if List.length w = 4 then
                        "<rect width=\"200\" height=\"200\" transform=\"translate(30,30)\" style=\"fill:white;stroke-width:1;stroke:black\" />\n"^
                        "<rect width=\""^(calcLen (List.nth(y,2)) (List.nth(y,0)) (List.nth(y,0)) (ProbNum.NUM(3)))^"\" height=\""^(calcLen (List.nth(y,3)) (List.nth(y,1)) (List.nth(y,3)) (ProbNum.NUM(3)))^"\" transform=\"translate("^(toNum (List.nth(y,0)))^","^(toNum (List.nth(y,1)))^")\" style=\"fill-opacity:50%;fill:"^(List.nth(z,0))^";stroke-width:1;stroke:black\" />\n"^
                        "<rect width=\""^(calcLen (List.nth(y,6)) (List.nth(y,4)) (List.nth(y,4)) (ProbNum.NUM(3)))^"\" height=\""^(calcLen (List.nth(y,7)) (List.nth(y,5)) (List.nth(y,7)) (ProbNum.NUM(3)))^"\" transform=\"translate("^(toNum (List.nth(y,4)))^","^(toNum (List.nth(y,5)))^")\" style=\"fill-opacity:50%;fill:"^(List.nth(z,1))^";stroke-width:1;stroke:black\"/>\n"^m^
                        "<text text-anchor=\"middle\" transform=\"translate("^(calcMid (List.nth(w,0)) (ProbNum.NUM(30)))^",10)\">"^(List.nth(x,0))^"</text>\n"^
                        "<text text-anchor=\"middle\" transform=\"translate("^(calcMid (List.nth(w,0)) (ProbNum.NUM(30)))^",25)\">"^(ProbNum.numToString (List.nth(w,0)))^"</text>\n"^
                        "<text text-anchor=\"middle\" transform=\"translate("^(calcLab (List.nth(y,4)))^","^(calcMid (List.nth(w,2)) (ProbNum.NUM(22)))^")\">"^(List.nth(x,1))^"</text>\n"^
                        "<text text-anchor=\"middle\" transform=\"translate("^(calcLab (List.nth(y,4)))^","^(calcMid (List.nth(w,2)) (ProbNum.NUM(38)))^")\">"^(ProbNum.numToString (List.nth(w,2)))^"</text>\n"   
                    else    "<rect width=\"200\" height=\"200\" transform=\"translate(30,30)\" style=\"fill:white;stroke-width:1;stroke:black\" />\n"^
                            "<rect width=\""^(calcLen (List.nth(y,2)) (List.nth(y,0)) (List.nth(y,0)) (ProbNum.NUM(1)))^"\" height=\""^(calcLen (List.nth(y,3)) (List.nth(y,1)) (List.nth(y,3)) (ProbNum.NUM(1)))^"\" transform=\"translate("^(toNum (List.nth(y,0)))^","^(toNum (List.nth(y,1)))^")\" style=\"fill-opacity:50%;fill:"^(List.nth(z,0))^";stroke-width:1;stroke:black\" />\n"^
                            "<rect width=\""^(calcLen (List.nth(y,6)) (List.nth(y,4)) (List.nth(y,4)) (ProbNum.NUM(1)))^"\" height=\""^(calcLen (List.nth(y,7)) (List.nth(y,5)) (List.nth(y,7)) (ProbNum.NUM(1)))^"\" transform=\"translate("^(toNum (List.nth(y,4)))^","^(toNum (List.nth(y,5)))^")\" style=\"fill-opacity:50%;fill:"^(List.nth(z,1))^";stroke-width:1;stroke:black\"/>\n"^
                            "<rect width=\""^(calcLen (List.nth(y,10)) (List.nth(y,8)) (List.nth(y,8)) (ProbNum.NUM(3)))^"\" height=\""^(calcLen (List.nth(y,11)) (List.nth(y,9)) (List.nth(y,11))  (ProbNum.NUM(2)))^"\" transform=\"translate("^(toNum (List.nth(y,8)))^","^(toNum (List.nth(y,9)))^")\" style=\"fill-opacity:50%;fill:"^(List.nth(z,2))^";stroke-width:1;stroke:black\" />\n"^m^
                            "<text text-anchor=\"middle\" transform=\"translate("^(calcMid (List.nth(w,0)) (ProbNum.NUM(30)))^",10)\">"^(List.nth(x,0))^"</text>\n"^
                            "<text text-anchor=\"middle\" transform=\"translate("^(calcMid (List.nth(w,0)) (ProbNum.NUM(30)))^",25)\">"^(ProbNum.numToString (List.nth(w,0)))^"</text>\n"^
                            "<text text-anchor=\"middle\" transform=\"translate(15,"^(calcMid (List.nth(w,2)) (ProbNum.NUM(22)))^")\">"^(List.nth(x,1))^"</text>\n"^
                            "<text text-anchor=\"middle\" transform=\"translate(15,"^(calcMid (List.nth(w,2)) (ProbNum.NUM(38)))^")\">"^(ProbNum.numToString (List.nth(w,2)))^"</text>\n"^
                            "<text text-anchor=\"middle\" transform=\"translate(245,"^(calcMid (List.nth(w,4)) (ProbNum.NUM(22)))^")\">"^(List.nth(x,1))^"</text>\n"^
                            "<text text-anchor=\"middle\" transform=\"translate(245,"^(calcMid (List.nth(w,4)) (ProbNum.NUM(38)))^")\">"^(ProbNum.numToString (List.nth(w,4)))^"</text>\n"
                val header = "<div>\n"^
                            "<svg width=\"300\" height=\"240\" background-color=\"white\" font-size=\"12px\">\n"^
                            "<pattern id=\"diagonalHatch\" patternUnits=\"userSpaceOnUse\" width=\"4\" height=\"4\">\n"^
                            "<path d=\"M-1,1 l2,-2 M0,4 l4,-4 M3,5 l2,-2\" style=\"stroke:#222; stroke-width:1\"/>\n"^
                            "</pattern>\n"
                val footer = "</svg>\n"^
                            "</div>\n"
                val content = toDocArea ((List.map eventToString a), b, (List.map shadeToString c), d, (rectToString e))
                in 
                (m,((header^content^footer),300.0,240.0))
            end
        val (a,b) = parseArea x
        val (_,n) = convertArea a
        val ns = List.map areaToHTML n 
        val outputFile = TextIO.openOut "output/area.html";
        val _ = TextIO.output(outputFile, (concatAll (ns@(stringToHTML b))));
        val _ = TextIO.closeOut outputFile in
        ns@(stringToHTML b)
    end

fun drawTable x =
    let fun parseTableShading (Construction.Source(x)) =
            if String.substring((#2 x), 0, 5) = "blank" then ([],[])
            else raise TableError
            |parseTableShading (Construction.TCPair(x,y)) =
                if (#1 (#constructor x)) = "highlight" then
                    let val (x1, y1) = parseTableShading (hd(y))
                        val (x2,_) = parseTable (List.nth(y, 1))
                        val (x3,_) = parseShading (List.last(y)) in
                        if x1 = [] then
                            (case x2 of
                            NAME(a)     => ([SEVENT(a)],[x3,WHITE])
                            |NNAME(a)   => ([NEVENT(a)],[WHITE,x3])
                            |_ => raise TableError)
                        else (case (hd(x1), x2) of
                            (SEVENT(a), NAME(b))    => (x1@[SEVENT(b)], y1@[WHITE,WHITE,x3,WHITE,WHITE,WHITE])
                            |(SEVENT(a), NNAME(b))  => (x1@[NEVENT(b)], y1@[WHITE,WHITE,WHITE,x3,WHITE,WHITE])
                            |(NEVENT(a), NAME(b))   => (x1@[SEVENT(b)], y1@[WHITE,WHITE,WHITE,WHITE,x3,WHITE])
                            |(NEVENT(a), NNAME(b))  => (x1@[NEVENT(b)], y1@[WHITE,WHITE,WHITE,WHITE,WHITE,x3])
                            |_ => raise TableError)
                    end
                else raise TableError
            |parseTableShading _ = raise TableError 
        and parseTable (Construction.Source(x)) =
                (case String.breakOn ":" (#2 x) of
                    (a,":",_) => (NAME(a),[(#1 x,a,Real.fromInt(String.size a)+0.5)])
                    |_ => raise TableError)
            |parseTable (Construction.TCPair(x,y)) =
                if (#1 (#constructor x)) = "notName" then 
                    (case (parseTable (hd(y))) of 
                        (NAME(a),b) => (NNAME(a),[(#1 (hd(b)),"<tspan text-decoration=\"overline\">"^(#2 (hd(b)))^"</tspan>",(#3 (hd(b))))]) 
                        |_ => raise TableError)
                else if (#1 (#constructor x)) = "constructOne" then 
                    let val (x1,y1) = parseTable (hd(y))
                        val (x2,y2) = ProbNum.parseNum (List.last(y)) in 
                        (ONEWAY((#1 (#token x)),x1,x2),y1@y2)
                    end
                else if (#1 (#constructor x)) = "constructTwo" then 
                    let val (x1,y1) = parseTable (hd(y))
                        val (x2,y2) = parseTable (List.nth(y, 1))
                        val (x3,y3) = ProbNum.parseNum (List.last(y)) in 
                        (TWOWAY((#1 (#token x)),x1,x2,x3),y1@y2@y3)
                    end
                else if (#1 (#constructor x)) = "combine" then 
                    let val (x1,y1) = parseTable (hd(y))
                        val (x2,y2) = parseTable (List.last(y)) in 
                        (COMB((#1 (#token x)),x1,x2),y1@y2)
                    end
                else if (#1 (#constructor x)) = "colourTable" then 
                    let val (x1,y1) = parseTable (hd(y))
                        val x2 = parseTableShading (List.last(y)) in 
                        (CTABLE((#1 (#token x)),x1,x2),y1)
                    end
                else raise TableError
            |parseTable _ = raise TableError
        fun convertTable (NAME(x)) = (([SEVENT(x)],[],[]),[])
            |convertTable (NNAME(x)) = (([NEVENT(x)],[],[]),[])
            |convertTable (ONEWAY(m,x,y)) = 
                let val ((x2,_,_),_) = convertTable x in
                    case (hd(x2)) of 
                    SEVENT(a) => ((x2,[y,ProbNum.MINUS(ProbNum.NUM(1),y)],[]),[(m,x2,[y,ProbNum.MINUS(ProbNum.NUM(1),y)],[])])
                    |NEVENT(a) => ((x2,[ProbNum.MINUS(ProbNum.NUM(1),y),y],[]),[(m,x2,[ProbNum.MINUS(ProbNum.NUM(1),y),y],[])])
                end
            |convertTable (TWOWAY(m,x,y,z)) = 
                let val ((x2,y2,_),n1) = convertTable x
                    val ((x3,y3,_),n2) = convertTable y in
                        case ((hd(x2)),(hd(x3))) of 
                        (SEVENT(a),SEVENT(b)) => ((x2@x3,y2@y3@[z,ProbNum.MINUS((hd(y2)),z),ProbNum.MINUS((hd(y3)),z),ProbNum.MINUS(ProbNum.PLUS(ProbNum.NUM(1),ProbNum.MINUS(z,(hd(y3)))),(hd(y2)))],[]),(m,x2@x3,y2@y3@[z,ProbNum.MINUS((hd(y2)),z),ProbNum.MINUS((hd(y3)),z),ProbNum.MINUS(ProbNum.PLUS(ProbNum.NUM(1),ProbNum.MINUS(z,(hd(y3)))),(hd(y2)))],[])::n1@n2)
                        |(SEVENT(a),NEVENT(b)) => ((x2@x3,y2@y3@[ProbNum.MINUS(List.nth(y2,0), z), z, ProbNum.MINUS(ProbNum.PLUS(ProbNum.NUM(1), ProbNum.MINUS(z,(List.nth(y3,1)))),(List.nth(y2,0))), ProbNum.MINUS((List.nth(y3,1)),z)],[]), (m,x2@x3,y2@y3@[ProbNum.MINUS(List.nth(y2,0), z), z, ProbNum.MINUS(ProbNum.PLUS(ProbNum.NUM(1),ProbNum.MINUS(z,(List.nth(y3,1)))),(List.nth(y2,0))),ProbNum.MINUS((List.nth(y3,1)),z)],[])::n1@n2)
                        |(NEVENT(a),SEVENT(b)) => ((x2@x3,y2@y3@[ProbNum.MINUS((List.nth(y3,0)),z), ProbNum.MINUS(ProbNum.PLUS(ProbNum.NUM(1),ProbNum.MINUS(z,(List.nth(y3,0)))),(List.nth(y2,1))), z, ProbNum.MINUS((List.nth(y2,1)),z)],[]), (m,x2@x3,y2@y3@[ProbNum.MINUS((List.nth(y3,0)),z), ProbNum.MINUS(ProbNum.PLUS(ProbNum.NUM(1),ProbNum.MINUS(z,(List.nth(y3,0)))),(List.nth(y2,1))),z,ProbNum.MINUS((List.nth(y2,1)),z)],[])::n1@n2)
                        |(NEVENT(a),NEVENT(b)) => ((x2@x3,y2@y3@[ProbNum.MINUS(ProbNum.PLUS(ProbNum.NUM(1),ProbNum.MINUS(z,(List.nth(y3,1)))),(List.nth(y2,1))), ProbNum.MINUS((List.nth(y3,1)),z), ProbNum.MINUS((List.nth(y2,1)),z), z],[]), (m,x2@x3,y2@y3@[ProbNum.MINUS(ProbNum.PLUS(ProbNum.NUM(1),ProbNum.MINUS(z,(List.nth(y3,1)))),(List.nth(y2,1))),ProbNum.MINUS((List.nth(y3,1)),z),ProbNum.MINUS((List.nth(y2,1)),z),z],[])::n1@n2)
                end
            |convertTable (COMB(m,x,y)) =
                let fun tableMerge x2 y2 x3 y3 =
                        let fun rotate y2 = [List.nth(y2,2),List.nth(y2,3),List.nth(y2,0),List.nth(y2,1),List.nth(y2,4),List.nth(y2,6),List.nth(y2,5),List.nth(y2,7)] in 
                            if List.length x2 = List.length x3 andalso eventToString (hd(x2)) = eventToString (hd(x3)) then (x2, y2, y3)
                            else if List.length x2 = List.length x3 andalso List.length x2 = 1 then ((x2@x3),(y2@[ProbNum.U,ProbNum.U,ProbNum.U,ProbNum.U,ProbNum.U,ProbNum.U]),([ProbNum.U,ProbNum.U]@y3@[ProbNum.U,ProbNum.U,ProbNum.U,ProbNum.U]))
                            else if List.length x2 = List.length x3 then (x2, y2, rotate y3)
                            else if List.length x2 > List.length x3 andalso eventToString (hd(x2)) = eventToString (hd(x3)) then (x2,y2,(y3@[ProbNum.U,ProbNum.U,ProbNum.U,ProbNum.U,ProbNum.U,ProbNum.U]))
                            else if List.length x2 > List.length x3 then (x2,y2,([ProbNum.U,ProbNum.U]@y3@[ProbNum.U,ProbNum.U,ProbNum.U,ProbNum.U]))
                            else if eventToString (hd(x2)) = eventToString (hd(x3)) then (x3,(y2@[ProbNum.U,ProbNum.U,ProbNum.U,ProbNum.U,ProbNum.U,ProbNum.U]),y3)
                            else (x3,([ProbNum.U,ProbNum.U]@y2@[ProbNum.U,ProbNum.U,ProbNum.U,ProbNum.U]),y3)
                        end
                    val ((x2,y2,_),n1) = convertTable y
                    val ((x3,y3,_),n2) = convertTable x 
                    val (a,b,c) = tableMerge x2 y2 x3 y3 in
                    if List.length a = 1 then ((a, ProbNum.resolve b c (List.length b), []),(m, a, ProbNum.resolve b c (List.length b), [])::n1@n2)
                    else ((a, ProbNum.resolve b c (List.length b), []),(m, a, ProbNum.resolve b c (List.length b), [])::n1@n2)
                end
            |convertTable (CTABLE(m,x,y)) =
                let fun rotate y2 = List.nth(y2,2)::List.nth(y2,3)::List.nth(y2,0)::List.nth(y2,1)::List.nth(y2,4)::List.nth(y2,6)::List.nth(y2,5)::[List.nth(y2,7)]
                    val ((x2,y2,_),n) = convertTable x 
                    val (x3,y3) = y in
                    if List.length x2 = List.length x3 andalso eventToString (hd(x2)) = eventToString (hd(x3)) then ((x2,y2,y3),(m,x2,y2,y3)::n)
                    else if List.length x2 = List.length x3 andalso List.length x2 = 2 then ((x2,y2,rotate y3),(m,x2,y2,rotate y3)::n)
                    else if List.length x2 = List.length x3 then ((x2@x3, y2@[ProbNum.U,ProbNum.U,ProbNum.U,ProbNum.U,ProbNum.U,ProbNum.U], [WHITE, WHITE]@y3@[WHITE, WHITE, WHITE, WHITE]),(m, x2@x3, y2@[ProbNum.U,ProbNum.U,ProbNum.U,ProbNum.U,ProbNum.U,ProbNum.U], [WHITE, WHITE]@y3@[WHITE, WHITE, WHITE, WHITE])::n)
                    else if List.length x2 > List.length x3 andalso eventToString (hd(x2)) = eventToString (hd(x3)) then ((x2, y2, y3@[WHITE, WHITE, WHITE, WHITE, WHITE, WHITE]),(m, x2, y2, y3@[WHITE, WHITE, WHITE, WHITE, WHITE, WHITE])::n)
                    else if List.length x2 > List.length x3 then ((x2, y2, [WHITE, WHITE]@y3@[WHITE, WHITE, WHITE, WHITE]),(m, x2, y2, [WHITE, WHITE]@y3@[WHITE, WHITE, WHITE, WHITE])::n)
                    else if List.length x2 < List.length x3 andalso eventToString (hd(x2)) = eventToString (hd(x3)) then ((x3, y2@[ProbNum.U,ProbNum.U,ProbNum.U,ProbNum.U,ProbNum.U,ProbNum.U], y3),(m, x3, y2@[ProbNum.U,ProbNum.U,ProbNum.U,ProbNum.U,ProbNum.U,ProbNum.U], y3)::n)
                    else ((List.rev x3, y2@[ProbNum.U,ProbNum.U,ProbNum.U,ProbNum.U,ProbNum.U,ProbNum.U], rotate y3),(m, List.rev x3, y2@[ProbNum.U,ProbNum.U,ProbNum.U,ProbNum.U,ProbNum.U,ProbNum.U], rotate y3)::n)
                end
        fun tableToHTML (m,a,b,c) =
            let fun convertShade x n =
                    let fun shadeToString x =
                            case x of
                            BLUE => "background-color:lightblue;"
                            |RED => "background-color:lightyellow;"
                            |WHITE => ""
                            |GREEN => "background-color:lightcoral;"
                            |PATTERN => "background-color:lightSeaGreen;"
                        fun emptyList n =
                            if n = 0 then []
                            else ""::(emptyList (n-1))
                    in
                        if x = [] then emptyList n
                        else List.map shadeToString x
                    end
                fun toDocTable (x,y,z) =
                    if List.length x = 1 then  ("<th style=\"background-color:lightgrey; border:1px solid; height:25px; width:70px;\"></th>\n"^
                                                "<th style=\"background-color:lightgrey; border:1px solid; width:70px;\">Total</th>\n"^
                                                "</tr>\n"^
                                                "<tr>\n"^
                                                "<th style=\"background-color:lightgrey; border:1px solid; height:25px;\">"^(List.nth(x,0))^"</th>\n"^
                                                "<td style=\"border: 1px solid;"^(List.nth(z,0))^"\">"^(List.nth(y,0))^"</td>\n"^
                                                "</tr>\n"^
                                                "<tr>\n"^
                                                "<th style=\"background-color:lightgrey; border:1px solid; height:25px;\"><span style=\"text-decoration:overline\">"^(List.nth(x,0))^"</span></th>\n"^
                                                "<td style=\"border: 1px solid"^(List.nth(z,1))^"\">"^(List.nth(y,1))^"</td>\n"^
                                                "</tr>\n"^
                                                "<tr>\n"^
                                                "<th style=\"background-color:lightgrey; border:1px solid; height:25px;\">Total</th>\n"^
                                                "<td style=\"border: 1px solid;\">1</td>\n",
                                                140.0)
                    else   ("<th style=\"background-color:lightgrey; border:1px solid; height:25px; width:70px;\"></th>\n"^
                            "<th style=\"background-color:lightgrey; border:1px solid; width:70px;\">"^(List.nth(x,1))^"</th>\n"^
                            "<th style=\"background-color:lightgrey; border:1px solid; width:70px;\"><span style=\"text-decoration:overline\">"^(List.nth(x,1))^"</span></th>\n"^
                            "<th style=\"background-color:lightgrey; border:1px solid; width:70px;\">Total</th>\n"^
                            "</tr>\n"^
                            "<tr>\n"^
                            "<th style=\"background-color:lightgrey; border:1px solid; height:25px;\">"^(List.nth(x,0))^"</th>\n"^
                            "<td style=\"border: 1px solid;"^(List.nth(z,4))^"\">"^(List.nth(y,4))^"</td>\n"^
                            "<td style=\"border: 1px solid;"^(List.nth(z,5))^"\">"^(List.nth(y,5))^"</td>\n"^
                            "<td style=\"border: 1px solid;"^(List.nth(z,0))^"\">"^(List.nth(y,0))^"</td>\n"^
                            "</tr>\n"^
                            "<tr>\n"^
                            "<th style=\"background-color:lightgrey; border:1px solid; height:25px;\"><span style=\"text-decoration:overline\">"^(List.nth(x,0))^"</span></th>\n"^
                            "<td style=\"border: 1px solid;"^(List.nth(z,6))^"\">"^(List.nth(y,6))^"</td>\n"^
                            "<td style=\"border: 1px solid;"^(List.nth(z,7))^"\">"^(List.nth(y,7))^"</td>\n"^
                            "<td style=\"border: 1px solid;"^(List.nth(z,1))^"\">"^(List.nth(y,1))^"</td>\n"^
                            "</tr>\n"^
                            "<tr>\n"^
                            "<th style=\"background-color:lightgrey; border:1px solid; height:25px;\">Total</th>\n"^
                            "<td style=\"border: 1px solid;"^(List.nth(z,2))^"\">"^(List.nth(y,2))^"</td>\n"^
                            "<td style=\"border: 1px solid;"^(List.nth(z,3))^"\">"^(List.nth(y,3))^"</td>\n"^
                            "<td style=\"border: 1px solid;\">1</td>\n",
                            280.0)
                val header =    "<div>\n"^
                                "<table style=\"text-align:center; border-collapse:collapse; background-color:white; font-size:12px;\">\n"^
                                "<tr>\n"
                val footer =    "</tr>\n"^
                                "</table>\n"^
                                "</div>\n"
                val (content,w) = toDocTable ((List.map eventToString a),(List.map ProbNum.numToString b),(convertShade c (List.length b)))
                in
                (m, ((header^content^footer),w,100.0))
            end
        val (a,b) = parseTable x
        val (_,n) = convertTable a
        val ns = List.map tableToHTML n
        val outputFile = TextIO.openOut "output/table.html";
        val _ = TextIO.output(outputFile, (concatAll (ns@(stringToHTML b))))
        val _ = TextIO.closeOut outputFile
        in
        ns@(stringToHTML b)
    end

fun drawTree x =
    let fun parseTreeShading (Construction.Source(x)) =
            if String.substring((#2 x), 0, 5) = "empty" then ([],10)
            else raise TableError
            |parseTreeShading (Construction.TCPair(x,y)) =
                if (#1 (#constructor x)) = "colour" then
                    let val (x1, _) = parseTreeShading (hd(y))
                        val (x2,_) = parseTree (List.nth(y, 1))
                        val (x3,_) = parseShading (List.last(y)) in
                    if x1 = [] then
                        (case x2 of
                        BRANCH(a) => ([SEVENT(a)],0)
                        |NBRANCH(a) => ([NEVENT(a)],1)
                        |_ => raise TableError)
                    else (case (hd(x1), x2, x3) of
                        (SEVENT(a), BRANCH(b),  BLUE)   => (x1@[SEVENT(b)], 2)
                        |(SEVENT(a), NBRANCH(b), BLUE)   => (x1@[NEVENT(b)], 3)
                        |(NEVENT(a), BRANCH(b),  BLUE)   => (x1@[SEVENT(b)], 4)
                        |(NEVENT(a), NBRANCH(b), BLUE)   => (x1@[NEVENT(b)], 5)
                        |(SEVENT(a), BRANCH(b),  RED)    => (x1@[SEVENT(b)], 6)
                        |(SEVENT(a), NBRANCH(b), RED)    => (x1@[NEVENT(b)], 7)
                        |(NEVENT(a), BRANCH(b),  RED)    => (x1@[SEVENT(b)], 8)
                        |(NEVENT(a), NBRANCH(b), RED)    => (x1@[NEVENT(b)], 9)
                        |_ => raise TableError)
                    end
                else raise TableError
            |parseTreeShading _ = raise TableError 
        and parseTree (Construction.Source(x)) = 
                (case String.breakOn ":" (#2 x) of
                    (a,":",_) => (BRANCH(a),[(#1 x,a,Real.fromInt(String.size a)+0.5)])
                    |_ => raise TreeError)
            |parseTree (Construction.TCPair(x,y)) =
                if (#1 (#constructor x)) = "notLabel" then 
                    (case (parseTree (hd(y))) of
                        (BRANCH(a),b) => (NBRANCH(a),[((#1 (hd(b))),"<tspan text-decoration=\"overline\">"^(#2 (hd(b)))^"</tspan>",(#3 (hd(b))))])
                        |_ => raise TreeError)
                else if (#1 (#constructor x)) = "construct" then 
                    let val (x1,y1) = parseTree (hd(y))
                        val (x2,y2) = ProbNum.parseNum (List.last(y)) in
                        (TREE((#1 (#token x)),x1,x2), y1@y2)
                    end
                else if (#1 (#constructor x)) = "addBranch" then 
                    let val (x1,y1) = parseTree (hd(y))
                        val (x2,y2) = parseTree (List.nth(y,1)) 
                        val (x3,y3) = ProbNum.parseNum (List.last(y)) in
                        (ADD((#1 (#token x)),x1,x2,x3),y1@y2@y3)
                    end
                else if (#1 (#constructor x)) = "resolve" then 
                    let val (x1,y1) = parseTree (hd(y))
                        val (x2,y2) = parseTree (List.last(y)) in
                        (RESOLVE((#1 (#token x)),x1,x2),y1@y2)
                    end   
                else if (#1 (#constructor x)) = "colourTree" then 
                    let val (x1,y1) = parseTree (hd(y))
                        val x2 = parseTreeShading (List.last(y)) in
                        (CTREE((#1 (#token x)),x1,x2), y1)
                    end 
                    
                else raise TreeError
            |parseTree (Construction.Reference(x)) = raise TreeError
        fun convertTree (BRANCH(x)) = (([SEVENT(x)],[],[]),[])
            |convertTree (NBRANCH(x)) = (([NEVENT(x)],[],[]),[])
            |convertTree (TREE(m,x,y)) =
                let val ((x2,_,_),_) = convertTree x in
                    case (hd(x2)) of
                    NEVENT(a) => ((x2,[ProbNum.MINUS(ProbNum.NUM(1),y),y],[]),[(m,x2,[ProbNum.MINUS(ProbNum.NUM(1),y),y],[])])
                    |SEVENT(a) => ((x2,[y,ProbNum.MINUS(ProbNum.NUM(1),y)],[]),[(m,x2,[y,ProbNum.MINUS(ProbNum.NUM(1),y)],[])])
                end
            |convertTree (ADD(m,x,y,z)) =
                let val ((x2,y2,_),n) = convertTree x
                    val ((x3,_,_),_) = convertTree y in
                    case ((hd(x2)), (hd(x3))) of
                        (SEVENT(a),SEVENT(b)) => ((x2@x3,y2@[z,ProbNum.MINUS(ProbNum.NUM(1),z),ProbNum.U,ProbNum.U],[]),(m,x2@x3,y2@[z,ProbNum.MINUS(ProbNum.NUM(1),z),ProbNum.U,ProbNum.U],[])::n)
                        |(SEVENT(a),NEVENT(b)) => ((x2@x3,y2@[ProbNum.MINUS(ProbNum.NUM(1),z),z,ProbNum.U,ProbNum.U],[]),(m,x2@x3,y2@[ProbNum.MINUS(ProbNum.NUM(1),z),z,ProbNum.U,ProbNum.U],[])::n)
                        |(NEVENT(a),SEVENT(b)) => ((x2@x3,y2@[ProbNum.U,ProbNum.U,z,ProbNum.MINUS(ProbNum.NUM(1),z)],[]),(m,x2@x3,y2@[ProbNum.U,ProbNum.U,z,ProbNum.MINUS(ProbNum.NUM(1),z)],[])::n)
                        |(NEVENT(a),NEVENT(b)) => ((x2@x3,y2@[ProbNum.U,ProbNum.U,ProbNum.MINUS(ProbNum.NUM(1),z),z],[]),(m,x2@x3,y2@[ProbNum.U,ProbNum.U,ProbNum.MINUS(ProbNum.NUM(1),z),z],[])::n)
                end 
            |convertTree ((RESOLVE(m,x,y))) =
                let fun treeMerge x2 y2 x3 y3 =
                        let fun f b = 
                                if List.nth(b,2) = ProbNum.U then List.map ProbNum.simplify [ProbNum.VAR("z"),ProbNum.MINUS(ProbNum.NUM(1),ProbNum.VAR("z")),
                                                                                             ProbNum.MINUS(ProbNum.NUM(1),ProbNum.FRAC(ProbNum.MULT(List.nth(b,4),List.nth(b,1)), ProbNum.VAR("z"))),ProbNum.FRAC(ProbNum.MULT(List.nth(b,4), List.nth(b,1)),ProbNum.VAR("z")), 
                                                                                             ProbNum.MINUS(ProbNum.NUM(1),ProbNum.FRAC(ProbNum.MULT(List.nth(b,5),List.nth(b,1)), ProbNum.MINUS(ProbNum.NUM(1),ProbNum.VAR("z")))),ProbNum.FRAC(ProbNum.MULT(List.nth(b,5),List.nth(b,1)),ProbNum.MINUS(ProbNum.NUM(1),ProbNum.VAR("z")))]
                                else if List.nth(b,4) = ProbNum.U then List.map ProbNum.simplify [ProbNum.VAR("z"), ProbNum.MINUS(ProbNum.NUM(1),ProbNum.VAR("z")),
                                                                                ProbNum.FRAC(ProbNum.MULT(List.nth(b,2),List.nth(b,0)),ProbNum.VAR("z")), ProbNum.MINUS(ProbNum.NUM(1),ProbNum.FRAC(ProbNum.MULT(List.nth(b,2),List.nth(b,0)),ProbNum.VAR("z"))),
                                                                                ProbNum.FRAC(ProbNum.MULT(List.nth(b,3),List.nth(b,0)),ProbNum.MINUS(ProbNum.NUM(1),ProbNum.VAR("z"))), ProbNum.MINUS(ProbNum.NUM(1),ProbNum.FRAC(ProbNum.MULT(List.nth(b,3),List.nth(b,0)),ProbNum.MINUS(ProbNum.NUM(1),ProbNum.VAR("z"))))]
                                else List.map ProbNum.simplify 
                                    [ProbNum.PLUS(ProbNum.MULT(List.nth(b,2),List.nth(b,0)),ProbNum.MULT(List.nth(b,4),List.nth(b,1))), ProbNum.PLUS(ProbNum.MULT(List.nth(b,3),List.nth(b,0)),ProbNum.MULT(List.nth(b,5),List.nth(b,1))), 
                                     ProbNum.FRAC(ProbNum.MULT(List.nth(b,2), List.nth(b,0)),ProbNum.PLUS(ProbNum.MULT(List.nth(b,2),List.nth(b,0)),ProbNum.MULT(List.nth(b,4),List.nth(b,1)))), ProbNum.FRAC(ProbNum.MULT(List.nth(b,4), List.nth(b,1)),ProbNum.PLUS(ProbNum.MULT(List.nth(b,2),List.nth(b,0)),ProbNum.MULT(List.nth(b,4),List.nth(b,1)))), 
                                     ProbNum.FRAC(ProbNum.MULT(List.nth(b,3),List.nth(b,0)),ProbNum.PLUS(ProbNum.MULT(List.nth(b,3),List.nth(b,0)),ProbNum.MULT(List.nth(b,5),List.nth(b,1)))),  ProbNum.FRAC(ProbNum.MULT(List.nth(b,5),List.nth(b,1)),ProbNum.PLUS(ProbNum.MULT(List.nth(b,3),List.nth(b,0)),ProbNum.MULT(List.nth(b,5),List.nth(b,1))))] 
                            fun countNum xs = 
                                case xs of
                                [] => 0
                                |(x::xs) => if (ProbNum.onlyNum x) then (countNum xs) + 1 else countNum xs
                        in
                            if List.length x2 = List.length x3 andalso eventToString (hd(x2)) = eventToString (hd(x3)) then (x2, y2, y3)
                            else if List.length x2 = 1 andalso List.length x2 = List.length x3 then ((x2@x3), (y2@[ProbNum.U,ProbNum.U,ProbNum.U,ProbNum.U]),  [ProbNum.VAR("z"), ProbNum.MINUS(ProbNum.NUM(1),ProbNum.VAR("z")), ProbNum.VAR("y"), ProbNum.MINUS(ProbNum.NUM(1),ProbNum.VAR("y")), ProbNum.FRAC(ProbNum.MINUS((hd(y3)),ProbNum.MULT(ProbNum.VAR("z"),ProbNum.VAR("y"))),ProbNum.MINUS(ProbNum.NUM(1),ProbNum.VAR("z"))), ProbNum.MINUS(ProbNum.NUM(1),ProbNum.FRAC(ProbNum.MINUS((hd(y3)),ProbNum.MULT(ProbNum.VAR("z"),ProbNum.VAR("y"))),ProbNum.MINUS(ProbNum.NUM(1),ProbNum.VAR("z"))))])
                            else if List.length x2 = List.length x3 then 
                                if (countNum y2) > (countNum y3) then (x2, y2, (f y3)) else (x3, (f y2), y3) 
                            else if List.length x2 > List.length x3 andalso eventToString (hd(x2)) = eventToString (hd(x3)) then (x2, y2, (y3@[ProbNum.U,ProbNum.U,ProbNum.U,ProbNum.U])) 
                            else if List.length x2 > List.length x3 then (List.rev x2, f y2, y3@[ProbNum.U,ProbNum.U,ProbNum.U,ProbNum.U])
                            else if eventToString (hd(x2)) = eventToString (hd(x3)) then (x3, (y2@[ProbNum.U,ProbNum.U,ProbNum.U,ProbNum.U]), y3)
                            else (List.rev x3, y2@[ProbNum.U,ProbNum.U,ProbNum.U,ProbNum.U], f y3)
                        end
                    val ((x2,y2,_),n1) = convertTree y
                    val ((x3,y3,_),n2) = convertTree x 
                    val (a,b,c) = treeMerge x2 y2 x3 y3 
                    in 
                    if List.length a = 1 then ((a, ProbNum.resolve b c (List.length b), []),(m, a, ProbNum.resolve b c (List.length b), [])::n1@n2)
                    else ((a, ProbNum.resolve b c (List.length b), []),(m, a, ProbNum.resolve b c (List.length b), [])::n1@n2)
                end 
            |convertTree (CTREE(m,x,y)) =
                let fun changeShade l n new =
                        if n = 0 then new::(tl(l))
                        else (hd(l))::changeShade (tl(l)) (n-1) new
                    fun numToList n len = 
                        if len = 1 then changeShade [WHITE,WHITE] n RED
                        else changeShade [WHITE,WHITE,WHITE,WHITE,WHITE,WHITE,WHITE,WHITE,WHITE,WHITE] n RED
                    fun revert n =
                        let val l = [WHITE,WHITE,WHITE,WHITE,WHITE,WHITE,WHITE,WHITE,WHITE,WHITE] in
                            case n of
                                0 => changeShade (changeShade l 8 RED) 6 RED
                                |1 => changeShade (changeShade l 9 RED) 7 RED
                                |2 => changeShade (changeShade l 8 RED) 6 PATTERN
                                |3 => changeShade (changeShade l 6 RED) 8 PATTERN
                                |4 => changeShade (changeShade l 9 RED) 7 PATTERN
                                |5 => changeShade (changeShade l 7 RED) 9 PATTERN
                                |6 => changeShade l 6 RED
                                |7 => changeShade l 8 RED
                                |8 => changeShade l 7 RED
                                |9 => changeShade l 9 RED
                                |_ => raise TreeError
                        end
                    val ((x2,y2,_),n) = convertTree x
                    val (x3,y3) = y 
                    in
                    if List.length x2 = List.length x3 andalso eventToString (hd(x2)) = eventToString (hd(x3)) then ((x2,y2,numToList y3 (List.length x2)),(m,x2,y2,numToList y3 (List.length x2))::n)
                    else if List.length x2 = List.length x3 andalso List.length x2 = 2 then ((x2,y2,revert y3),(m,x2,y2,revert y3)::n)
                    else if List.length x2 = List.length x3 then ((x2@x3, y2@[ProbNum.U,ProbNum.U,ProbNum.U,ProbNum.U], revert y3),(m, x2@x3, y2@[ProbNum.U,ProbNum.U,ProbNum.U,ProbNum.U], revert y3)::n)
                    else if List.length x2 > List.length x3 andalso eventToString (hd(x2)) = eventToString (hd(x3)) then ((x2, y2, numToList y3 (List.length x2)),(m, x2, y2, numToList y3 (List.length x2))::n)
                    else if List.length x2 > List.length x3 then ((x2, y2, revert y3),(m, x2, y2, revert y3)::n)
                    else if List.length x2 < List.length x3 andalso eventToString (hd(x2)) = eventToString (hd(x3)) then ((x3, y2@[ProbNum.U,ProbNum.U,ProbNum.U,ProbNum.U], numToList y3 (List.length x3)),(m, x3, y2@[ProbNum.U,ProbNum.U,ProbNum.U,ProbNum.U], numToList y3 (List.length x3))::n)
                    else ((List.rev x3, y2@[ProbNum.U,ProbNum.U,ProbNum.U,ProbNum.U], revert y3),(m, List.rev x3, y2@[ProbNum.U,ProbNum.U,ProbNum.U,ProbNum.U], revert y3)::n)
                end
        fun treeToHTML (m,a,b,c) =
            let fun convertShade x n =
                    let fun shadeToString x =
                            case x of
                            BLUE => " fill=\"lightblue\""
                            |RED => " fill=\"lightcoral\""
                            |WHITE => ""
                            |GREEN => " fill=\"lightsalmon\""
                            |PATTERN => " fill=\"lightseagreen\""
                        fun emptyList n =
                            if n = 0 then []
                            else ""::(emptyList (n-1))
                    in
                        if x = [] then emptyList n
                        else List.map shadeToString x
                    end
                fun addJoint y =
                    if List.length y = 2 then []
                    else if List.nth(y,2) = ProbNum.U andalso List.nth(y,4) = ProbNum.U then [ProbNum.U,ProbNum.U,ProbNum.U,ProbNum.U]
                    else if List.nth(y,2) = ProbNum.U then [ProbNum.U,ProbNum.U,ProbNum.MULT(List.nth(y,4),List.nth(y,1)),ProbNum.MULT(List.nth(y,5),List.nth(y,1))]
                    else if List.nth(y,4) = ProbNum.U then [ProbNum.MULT(List.nth(y,2),List.nth(y,0)),ProbNum.MULT(List.nth(y,3),List.nth(y,0)),ProbNum.U,ProbNum.U]
                    else [ProbNum.MULT(List.nth(y,2),List.nth(y,0)),ProbNum.MULT(List.nth(y,3),List.nth(y,0)),ProbNum.MULT(List.nth(y,4),List.nth(y,1)),ProbNum.MULT(List.nth(y,5),List.nth(y,1))]
                fun toDocTree (x,y,z) =
                    if List.length x = 1 then  ("<svg height=\"90\" width=\"120\" style=\"background-color:white\" font-size=\"12px\">\n"^
                                                "<text transform=\"translate(85,27)\">P("^(List.nth(x,0))^")</text>\n"^
                                                "<text transform=\"translate(85,83)\">P(<tspan text-decoration=\"overline\">"^(List.nth(x,0))^"</tspan>)</text>\n"^
                                                "<text text-anchor=\"middle\" transform=\"translate(40,35) rotate(-17)\""^(List.nth(z,0))^">"^(List.nth(y,0))^"</text>\n"^
                                                "<text text-anchor=\"middle\" transform=\"translate(40,74) rotate(17)\""^(List.nth(z,1))^">"^(List.nth(y,1))^"</text>\n"^
                                                "<line x1=\"0\" y1=\"50\" x2=\"80\" y2=\"25\" style=\"stroke:black;stroke-width:1\"/>\n"^
                                                "<line x1=\"0\" y1=\"50\" x2=\"80\" y2=\"75\" style=\"stroke:black;stroke-width:1\"/>\n",
                                                90.0, 120.0)
                    else   ("<svg height=\"110\" width=\"350\" style=\"background-color:white\" font-size=\"12px\">\n"^
                            "<text transform=\"translate(85,27)\">P("^(List.nth(x,0))^")</text>\n"^
                            "<text transform=\"translate(85,83)\">P(<tspan text-decoration=\"overline\">"^(List.nth(x,0))^"</tspan>)</text>\n"^
                            "<text transform=\"translate(225,10)\""^(List.nth(z,6))^">P("^(List.nth(x,0))^"&cap;"^(List.nth(x,1))^") "^(List.nth(y,6))^"</text>\n"^
                            "<text transform=\"translate(225,38)\""^(List.nth(z,7))^">P("^(List.nth(x,0))^"&cap;<tspan text-decoration=\"overline\">"^(List.nth(x,1))^"</tspan>) "^(List.nth(y,7))^"</text>\n"^
                            "<text transform=\"translate(225,70)\""^(List.nth(z,8))^">P(<tspan text-decoration=\"overline\">"^(List.nth(x,0))^"</tspan>&cap;"^(List.nth(x,1))^") "^(List.nth(y,8))^"</text>\n"^
                            "<text transform=\"translate(225,98)\""^(List.nth(z,9))^">P(<tspan text-decoration=\"overline\">"^(List.nth(x,0))^"</tspan>&cap;<tspan text-decoration=\"overline\">"^(List.nth(x,1))^"</tspan>) "^(List.nth(y,9))^"</text>\n"^
                            "<text text-anchor=\"middle\" transform=\"translate(40,35) rotate(-17)\""^(List.nth(z,0))^">"^(List.nth(y,0))^"</text>\n"^
                            "<text text-anchor=\"middle\" transform=\"translate(40,74) rotate(17)\""^(List.nth(z,1))^">"^(List.nth(y,1))^"</text>\n"^
                            "<text text-anchor=\"middle\" transform=\"translate(170,11) rotate(-7)\""^(List.nth(z,2))^">"^(List.nth(y,2))^"</text>\n"^
                            "<text text-anchor=\"middle\" transform=\"translate(170,37) rotate(7)\""^(List.nth(z,3))^">"^(List.nth(y,3))^"</text>\n"^
                            "<text text-anchor=\"middle\" transform=\"translate(170,71) rotate(-7)\""^(List.nth(z,4))^">"^(List.nth(y,4))^"</text>\n"^
                            "<text text-anchor=\"middle\" transform=\"translate(170,97) rotate(7)\""^(List.nth(z,5))^">"^(List.nth(y,5))^"</text>\n"^
                            "<line x1=\"0\" y1=\"50\" x2=\"80\" y2=\"25\" style=\"stroke:black;stroke-width:1\"/>\n"^
                            "<line x1=\"0\" y1=\"50\" x2=\"80\" y2=\"75\" style=\"stroke:black;stroke-width:1\"/>\n"^
                            "<line x1=\"120\" y1=\"20\" x2=\"220\" y2=\"7\" style=\"stroke:black;stroke-width:1\"/>\n"^
                            "<line x1=\"120\" y1=\"20\" x2=\"220\" y2=\"33\" style=\"stroke:black;stroke-width:1\"/>\n"^
                            "<line x1=\"120\" y1=\"80\" x2=\"220\" y2=\"67\" style=\"stroke:black;stroke-width:1\"/>\n"^
                            "<line x1=\"120\" y1=\"80\" x2=\"220\" y2=\"93\" style=\"stroke:black;stroke-width:1\"/>\n",
                            110.0, 350.0)
                val header = "<div>\n"
                val footer = "</svg>\n"^
                             "</div>"
                val b = b@(addJoint b)
                val (content,h,w) = toDocTree ((List.map eventToString a),(List.map ProbNum.numToString b),(convertShade c (List.length b)))
                in
                (m, ((header^content^footer),w,h))
            end
        val (a,b) = parseTree x
        val (_,n) = convertTree a
        val ns = List.map treeToHTML n
        val outputFile = TextIO.openOut "output/tree.html";
        val _ = TextIO.output(outputFile, (concatAll (ns@(stringToHTML b))));
        val _ = TextIO.closeOut outputFile
        in
        ns@(stringToHTML b)
    end

fun drawBayes x =
    let fun parseEvent (Construction.Source(x)) = 
                (case String.breakOn ":" (#2 x) of
                (a,":",_) => [(#1 x,a,Real.fromInt(String.size a)+0.5)]
                | _ => raise BayesError)
            |parseEvent (Construction.TCPair(x,y)) =
                let val t = (#1 (#token x)) in
                    if (#1 (#constructor x)) = "complement" then 
                        let val y1 = parseEvent (List.last y) in 
                            (case (List.nth (y,0)) of
                            Construction.Source(z) => (t,"<tspan text-decoration=\"overline\">"^(#2 (hd(y1)))^"</tspan>",(#3 (hd(y1))))::((#1 z,"-",1.5))::y1
                            |_ => raise BayesError)
                        end
                    else let val y1 = parseEvent (hd(y))
                             val y2 = parseEvent (List.last(y)) in
                                if (#1 (#constructor x)) = "condition" then 
                                    (case (List.nth (y,1)) of
                                    Construction.Source(z) => (t,(#2 (hd(y1)))^"|"^(#2 (hd(y2))),(#3 (hd(y1)))+(#3 (hd(y2))))::y1@[(#1 z,"|",1.5)]@y2
                                    |_ => raise BayesError)
                                else case (List.nth (y,1)) of
                                        Construction.Source(z) => 
                                            (case (#2 z) of
                                            "inter" => (t,(#2 (hd(y1)))^"&cap;"^(#2 (hd(y2))),(#3 (hd(y1)))+(#3 (hd(y2)))+0.5)::y1@[(#1 z,"&cap;",1.5)]@y2
                                            |"union" => (t,(#2 (hd(y1)))^"&cup;"^(#2 (hd(y2))),(#3 (hd(y1)))+(#3 (hd(y2)))+0.5)::y1@[(#1 z,"&cup;",1.5)]@y2
                                            |_ => raise BayesError)
                                        |_ => raise BayesError
                         end
                end
            |parseEvent (Construction.Reference(x)) = raise BayesError
        fun parseBayes (Construction.TCPair(x,y)) = 
                if (#1 (#constructor x)) = "prob" then
                    let val y1 = parseEvent (hd(y)) 
                        val (_,y2) = ProbNum.parseNum (List.last y) 
                        in  
                        (#1 (#token x),"Pr("^(#2 (hd(y1)))^") = "^(#2 (hd(y2))),(#3 (hd(y1)))+(#3 (hd(y2)))+3.0)::y1@y2
                    end
                else if (#1 (#constructor x)) = "addEqn" then
                    let val y1 = parseBayes (hd(y))
                        val y2 = parseBayes (List.last y) in
                        (#1 (#token x),(#2 (hd(y1)))^", "^(#2 (hd(y2))),(#3 (hd(y1)))+(#3 (hd(y2)))-1.0)::y1@y2   
                    end
                else raise BayesError
            |parseBayes _ = raise BayesError
        val a = (parseBayes x)
        val outputFile = TextIO.openOut "output/bayes.html";
        val _ = TextIO.output(outputFile, (concatAll (stringToHTML a)));
        val _ = TextIO.closeOut outputFile
        in
        stringToHTML a
    end;

end;

