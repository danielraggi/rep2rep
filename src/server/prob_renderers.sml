import "core.construction";

signature PROBRENDER = sig
    val drawArea: Construction.construction -> (string * (string*real*real)) list;
    val drawTable: Construction.construction -> (string * (string*real*real)) list;
    val drawTree: Construction.construction -> (string * (string*real*real)) list;
end;

structure ProbRender : PROBRENDER = struct

datatype numExp = U
                 |NUM of int
                 |DEC of string
                 |VAR of string
                 |PLUS of numExp * numExp
                 |MINUS of numExp * numExp
                 |MULT of numExp * numExp
                 |FRAC of numExp * numExp
datatype num =  R of real
               |V of string
exception NumError;

datatype shading = BLUE
                  |WHITE
                  |RED
                  |GREEN
                  |PATTERN
exception ShadeError;

datatype eventExp = SEVENT of string
                    |NEVENT of string

datatype areaExp = EMPTY
                  |LABEL of string
                  |NLABEL of string
                  |POINT of numExp * numExp
                  |RECT of areaExp * areaExp
                  |OVERLAY of string * areaExp * areaExp * areaExp * shading
                  |COMBAREA of string * areaExp * areaExp
exception AreaError;

datatype tableExp = NAME of string
                    |NNAME of string
                    |ONEWAY of string * tableExp * numExp
                    |TWOWAY of string * tableExp * tableExp * numExp
                    |COMB of string * tableExp * tableExp
exception TableError;

datatype treeExp = BRANCH of string
                  |NBRANCH of string
                  |TREE of string * treeExp * numExp
                  |ADD of string * treeExp * treeExp * numExp
                  |RESOLVE of string * treeExp * treeExp
exception TreeError;

fun eventToString (SEVENT(x)) = x
    |eventToString (NEVENT(x)) = x

fun parseShading (Construction.Source(x)) =
    let val a = #2 x 
        val b = #1 x in
        if String.substring(a, 0, 3) = "red" then (RED, [(b, "RED")])
        else if String.substring(a, 0, 4) = "blue" then (BLUE, [(b, "BLUE")])
        else if String.substring(a, 0, 5) = "white" then (WHITE, [(b, "WHITE")])
        else if String.substring(a, 0, 5) = "green" then (GREEN, [(b, "GREEN")])
        else if String.substring(a, 0, 7) = "pattern" then (PATTERN, [(b, "PATTERN")])
        else (WHITE, [(b, "WHITE")])
    end
    |parseShading _ = raise ShadeError;

fun parseNum (Construction.Source(x)) =
        if (Char.isAlpha(String.sub(#2 x, 0)) andalso (not (String.substring(#2 x, 0, 2) = "fp"))) then (VAR(String.substring(#2 x, 0, 1)), [(#1 x, String.substring(#2 x, 0, 1))])
        else let fun range_num x s = 
                    if(Char.isDigit(String.sub(x, s))) then range_num x (s+1)
                    else s
                 fun f x k =
                    let val m = range_num (#2 x) k
                        val n = Int.fromString (String.substring(#2 x, k, m)) in 
                        case n of
                        NONE => raise NumError
                        |SOME x => x
                    end
            in
            if(String.substring(#2 x, 0, 2) = "fp") then 
                let val m = range_num (#2 x) 2 in
                    (DEC(String.substring(#2 x, 2, m-2)), [(#1 x, "0."^String.substring(#2 x, 2, m-2))])
                end
            else (NUM(f x 0), [(#1 x, Int.toString (f x 0))])
        end
    |parseNum (Construction.TCPair(x,y)) =
        if (#1 (#constructor x)) = "infixOp" then
            let val (a,y1) = parseNum (List.nth (y,0)) 
                val (b,y2) = parseNum (List.nth (y,2)) in
                case (List.nth (y,1)) of
                    Construction.Source(z) => (case (#2 z) of
                                                "plus" => (PLUS(a,b), (#1 z, "+")::y1@y2)
                                                |"minus" => (MINUS(a,b), (#1 z, "-")::y1@y2)
                                                |_ => raise NumError)
                    |_ => raise NumError
            end
        else if (#1 (#constructor x)) = "frac" then 
            let val (a,y1) = parseNum (List.nth (y,0)) 
                val (b,y2) = parseNum (List.last(y)) in
                case (List.nth (y,1)) of
                    Construction.Source(z) => (FRAC(a,b), (#1 z, "/")::y1@y2)
                    |_ => raise NumError
            end
        else if (#1 (#constructor x)) = "implicitMult" then 
            let val (a,y1) = parseNum (List.nth (y,0)) 
                val (b,y2) = parseNum (List.last(y)) in
                (MULT(a,b), y1@y2)
            end
        else raise NumError
    |parseNum (Construction.Reference(x)) = (VAR(String.substring(#2 x, 0, 1)), [])

fun onlyNum U = false
    |onlyNum (NUM(x)) = true
    |onlyNum (DEC(x)) = true
    |onlyNum (VAR(x)) = false
    |onlyNum (PLUS(x,y)) = (onlyNum x) andalso (onlyNum y)
    |onlyNum (MINUS(x,y)) = (onlyNum x) andalso (onlyNum y)
    |onlyNum (MULT(x,y)) = (onlyNum x) andalso (onlyNum y)
    |onlyNum (FRAC(x,y)) = (onlyNum x) andalso (onlyNum y)

fun numToString x =
    let fun round n =
            let fun temp f n =
                    case f n of
                    NONE => raise NumError
                    |SOME x => x
                val s = Real.toString n in
                if(String.size s > 6) then
                    let val z = temp (Real.fromString) (String.substring(s, 0, 6)) in
                         if (temp (Int.fromString) (String.substring(s, 6, 1)) > 4) then z + 0.0001
                        else z
                    end 
                else n
            end
        fun convertNum (PLUS(x,y)) =
                (case (convertNum x, convertNum y) of
                (R a, R b) => if b < 0.0 then R(a-(b*(~1.0))) 
                              else R (a+b)
                |(R a, V b) => if String.substring(b,0,1) = "~" then V ((Real.toString (round a))^"-"^(String.substring(b,1,(String.size b)-1))) 
                               else if Real.== (a,0.0) then (V b)
                               else V ((Real.toString (round a))^"+"^b)
                |(V a, R b) => if b < 0.0 then V (a^"-"^(Real.toString (round (b*(~1.0)))))
                               else if Real.== (b,0.0) then (V a)
                               else V (a^"+"^(Real.toString (round b)))
                |(V a, V b) => if String.substring(b,0,1) = "~" then V (a^"-"^(String.substring(b,1,(String.size b)-1))) else V (a^"+"^b))
            |convertNum (MINUS(x,y)) =
                (case (convertNum x, convertNum y) of
                (R a, R b) => if b < 0.0 then R(a+(b*(~1.0))) else R (a-b)
                |(R a, V b) => if Real.== (a,0.0) andalso String.substring(b,0,1) = "~" then V (String.substring(b,1,(String.size b)-1))
                               else if Real.== (a,0.0) then V ("~"^b)
                               else if String.substring(b,0,1) = "~" then V ((Real.toString (round a))^"+"^(String.substring(b,1,(String.size b)-1))) 
                               else V ((Real.toString (round a))^"-"^b)
                |(V a, R b) => if b < 0.0 then V (a^"+"^(Real.toString (round (b*(~1.0))))) 
                               else if Real.== (b,0.0) then (V a)
                               else V (a^"-"^(Real.toString (round b)))
                |(V a, V b) => if String.substring(b,0,1) = "~" then V (a^"+"^(String.substring(b,1,(String.size b)-1))) else V (a^"-"^b))
            |convertNum (MULT(x,y)) =
                (case (convertNum x, convertNum y) of
                (R a, R b) => R (a*b)
                |(R a, V b) => if Real.== (a,1.0) then V b 
                               else if Real.== (a,~1.0) then V ("~"^b)
                               else V ((Real.toString (round a))^"*"^b)
                |(V a, R b) => V (a^"*"^(Real.toString (round b)))
                |(V a, V b) => V (a^"*"^b))
            |convertNum (FRAC(x,y)) =
                (case (convertNum x, convertNum y) of
                (R a, R b) => R (a/b)
                |(R a, V b) => V ((Real.toString (round a))^"/"^b)
                |(V a, R b) => if Real.== (b,1.0) then V a else V (a^"/"^(Real.toString (round b)))
                |(V a, V b) => V (a^"/"^b))
            |convertNum (VAR(x)) = V x
            |convertNum (U) = V " "
            |convertNum (DEC(x)) = 
                let val x2 = Real.fromString ("0."^x) in
                (case x2 of
                    NONE => raise NumError
                    |SOME x => R x)
                end
            |convertNum (NUM(x)) = R (Real.fromInt x)
        fun f (V(x)) = x
            |f (R(x)) = Real.toString (round x) 
        val str = f (convertNum (simplify x))
        in
        if String.size str > 40 then " " else str
    end
and simplify (PLUS(x,y)) =
        let val a = simplify x 
            val b = simplify y in
            if numToString a = numToString (NUM(0)) then b
            else if numToString b = numToString (NUM(0)) then a
            else case (a,b) of
            (VAR(k),MULT(c,VAR(l)))                     => if k = l then simplify (MULT(PLUS(NUM(1),c),VAR(k))) else PLUS(a,b)
            |(MULT(n,VAR(m)),VAR(l))                    => if m = l then simplify (MULT(PLUS(NUM(1),n),VAR(m))) else PLUS(a,b) 
            |(MULT(n,VAR(m)),MULT(k,VAR(l)))            => if m = l then simplify (MULT(PLUS(n,k),VAR(m))) else PLUS(a,b) 
            |(MULT(m,VAR(k)),PLUS(n,VAR(l)))            => if k = l then simplify (PLUS(n,MULT(PLUS(NUM(1),m),VAR(k)))) else PLUS(a,b)
            |(MULT(m,VAR(k)),PLUS(n,MULT(c,VAR(l))))    => if k = l then simplify (PLUS(n,MULT(PLUS(m,c),VAR(k)))) else PLUS(a,b)
            |(MULT(m,VAR(k)),MINUS(n,VAR(l)))           => if k = l then simplify (PLUS(n,MULT(MINUS(m,NUM(1)),VAR(k)))) else PLUS(a,b)
            |(MULT(m,VAR(k)),MINUS(VAR(l),n))           => if k = l then simplify (PLUS(MINUS(NUM(0),n),MULT(PLUS(NUM(1),m),VAR(k)))) else PLUS(a,b)
            |(MULT(m,VAR(k)),MINUS(n,MULT(c,VAR(l))))   => if k = l then simplify (PLUS(n,MULT(MINUS(m,c),VAR(k)))) else PLUS(a,b)
            |(MULT(m,VAR(k)),MINUS(MULT(c,VAR(l)),n))   => if k = l then simplify (PLUS(MINUS(NUM(0),n),MULT(PLUS(c,m),VAR(k)))) else PLUS(a,b)
            |(PLUS(m,VAR(k)),VAR(l))                    => if k = l then simplify (PLUS(m,MULT(NUM(2),VAR(k)))) else PLUS(a,b)
            |(PLUS(m,VAR(k)),MULT(n,VAR(l)))            => if k = l then simplify (PLUS(m,MULT(PLUS(NUM(1),n),VAR(k)))) else PLUS(a,b)
            |(PLUS(m,VAR(k)),PLUS(n,VAR(l)))            => if k = l then simplify (PLUS(PLUS(m,n),MULT(NUM(2),VAR(k)))) else PLUS(a,b)
            |(PLUS(m,VAR(k)),PLUS(c,MULT(n,VAR(l))))    => if k = l then simplify (PLUS(PLUS(m,c),MULT(PLUS(NUM(1),n),VAR(k)))) else PLUS(a,b)
            |(PLUS(m,VAR(k)),MINUS(n,VAR(l)))           => if k = l then simplify (PLUS(m,n)) else PLUS(a,b)
            |(PLUS(m,VAR(k)),MINUS(VAR(l),n))           => if k = l then simplify (PLUS(MINUS(m,n),MULT(NUM(2),VAR(k)))) else PLUS(a,b)
            |(PLUS(m,VAR(k)),MINUS(n,MULT(c,VAR(l))))   => if k = l then simplify (PLUS(PLUS(m,n),MULT(MINUS(NUM(1),c),VAR(k)))) else PLUS(a,b)
            |(PLUS(m,VAR(k)),MINUS(MULT(c,VAR(l)),n))   => if k = l then simplify (PLUS(MINUS(m,n),MULT(PLUS(NUM(1),c),VAR(k)))) else PLUS(a,b)
            |(PLUS(n,MULT(c,VAR(l))),VAR(k))                    => if k = l then simplify (PLUS(n,MULT(PLUS(NUM(1),c),VAR(k)))) else PLUS(a,b)
            |(PLUS(n,MULT(c,VAR(l))),MULT(m,VAR(k)))            => if k = l then simplify (PLUS(n,MULT(PLUS(m,c),VAR(k)))) else PLUS(a,b)
            |(PLUS(m,MULT(n,VAR(k))),PLUS(c,VAR(l)))            => if k = l then simplify (PLUS(PLUS(m,c),MULT(PLUS(NUM(1),n),VAR(k)))) else PLUS(a,b)
            |(PLUS(n,MULT(c,VAR(l))),PLUS(d,MULT(m,VAR(k))))    => if k = l then simplify (PLUS(PLUS(n,d),MULT(PLUS(c,m),VAR(k)))) else PLUS(a,b)
            |(PLUS(n,MULT(c,VAR(l))),MINUS(d,VAR(k)))           => if k = l then simplify (PLUS(PLUS(n,d),MULT(MINUS(c,NUM(1)),VAR(k)))) else simplify (MINUS(PLUS(PLUS(n,d),MULT(c,VAR(l))),VAR(k)))
            |(PLUS(n,MULT(c,VAR(l))),MINUS(VAR(k),d))           => if k = l then simplify (PLUS(MINUS(n,d),MULT(PLUS(NUM(1),c),VAR(k)))) else PLUS(a,b)
            |(PLUS(n,MULT(c,VAR(l))),MINUS(d,MULT(m,VAR(k))))   => if k = l then simplify (PLUS(PLUS(n,d),MULT(MINUS(c,m),VAR(k)))) else PLUS(a,b)
            |(PLUS(n,MULT(c,VAR(l))),MINUS(MULT(m,VAR(k)),d))   => if k = l then simplify (PLUS(MINUS(n,d),MULT(PLUS(c,m),VAR(k)))) else PLUS(a,b)
            |(MINUS(m,VAR(k)),VAR(l))                           => if k = l then m else PLUS(a,b)
            |(MINUS(m,MULT(n,VAR(k))),VAR(l))                   => if k = l then simplify (MINUS(m,MULT(PLUS(NUM(1),n),VAR(k)))) else PLUS(a,b)
            |(MINUS(m,MULT(n,VAR(k))),MULT(c,VAR(l)))           => if k = l then simplify (PLUS(m,MULT(MINUS(c,n),VAR(k)))) else PLUS(a,b)
            |(MINUS(n,MULT(c,VAR(l))),PLUS(d,MULT(m,VAR(k))))   => if k = l then simplify (PLUS(PLUS(n,d),MULT(MINUS(m,c),VAR(k)))) else PLUS(a,b)
            |(MINUS(n,MULT(c,VAR(l))),PLUS(d,VAR(k)))           => if k = l then simplify (PLUS(PLUS(n,d),MULT(MINUS(NUM(1),c),VAR(k)))) else PLUS(a,b)
            |(MINUS(n,MULT(c,VAR(l))),MINUS(d,MULT(m,VAR(k))))  => if k = l then simplify (MINUS(PLUS(n,d),MULT(PLUS(m,c),VAR(k)))) else PLUS(a,b)
            |(MINUS(MULT(c,VAR(l)),n),MINUS(d,MULT(m,VAR(k))))  => if k = l then simplify (PLUS(MINUS(d,n),MULT(MINUS(c,m),VAR(k)))) else PLUS(a,b)
            |(MINUS(VAR(k),c),MINUS(m,VAR(l)))                  => if k = l then simplify (MINUS(m,c)) else simplify (MINUS(PLUS(MINUS(m,c),VAR(k)),VAR(l))) 
            |(MINUS(VAR(k),n),MINUS(c,MINUS(VAR(l),m)))         => if k = l andalso n = m then c else PLUS(a,b)
            |(a,MINUS(VAR(k),c))            => if onlyNum a andalso onlyNum c then simplify (PLUS(MINUS(a,c),VAR(k))) else PLUS(a,b) 
            |(a,MINUS(c,VAR(k)))            => if onlyNum a andalso onlyNum c then simplify (MINUS(PLUS(a,c),VAR(k))) else PLUS(a,b)
            |(a,MINUS(c,MULT(d,VAR(k))))    => if onlyNum a andalso onlyNum c then simplify (MINUS(PLUS(a,c),MULT(d,VAR(k)))) else PLUS(a,b)
            |(a,MINUS(MULT(d,VAR(k)),c))    => if onlyNum a andalso onlyNum c then simplify (PLUS(MINUS(a,c),MULT(d,VAR(k)))) else PLUS(a,b)
            |(a,PLUS(c,VAR(k)))             => if onlyNum a andalso onlyNum c then simplify (PLUS(PLUS(a,c),VAR(k))) else PLUS(a,b)
            |(a,PLUS(c,MULT(n,VAR(k))))     => if onlyNum a andalso onlyNum c then simplify (PLUS(PLUS(a,c),MULT(n,VAR(k)))) else PLUS(a,b)
            |(MINUS(VAR(k),c),b)            => if onlyNum b andalso onlyNum c then simplify (PLUS(MINUS(b,c),VAR(k))) else PLUS(a,b)
            |(MINUS(c,VAR(k)),b)            => if onlyNum b andalso onlyNum c then simplify (MINUS(PLUS(b,c),VAR(k))) else PLUS(a,b)
            |(MINUS(MULT(n,VAR(k)),c),b)    => if onlyNum b andalso onlyNum c then simplify (PLUS(MINUS(b,c),MULT(n,VAR(k)))) else PLUS(a,b)
            |(MINUS(c,MULT(n,VAR(k))),b)    => if onlyNum b andalso onlyNum c then simplify (MINUS(PLUS(b,c),MULT(n,VAR(k)))) else PLUS(a,b)
            |(PLUS(c,VAR(k)),b)             => if onlyNum b andalso onlyNum c then simplify (PLUS(PLUS(b,c),VAR(k))) else PLUS(a,b)
            |(PLUS(c,MULT(n,VAR(k))),b)     => if onlyNum b andalso onlyNum c then simplify (PLUS(PLUS(b,c),MULT(n,VAR(k)))) else PLUS(a,b)
            |(a,MINUS(c,k))     => if a = k then c else PLUS(a,b)
            |(MINUS(c,k),b)     => if b = k then c else PLUS(a,b)
            |(VAR(l),b)         => if onlyNum b then PLUS(b,VAR(l)) else PLUS(a,b)
            |(MULT(c,VAR(k)),b) => if onlyNum b then simplify (PLUS(b,MULT(c,VAR(k)))) else PLUS(a,b)
            |_ => PLUS(a,b) 
        end
    |simplify (MINUS(x,y)) =
        let val a = simplify x 
            val b = simplify y in
            if numToString b = numToString (NUM(0)) then a
            else if numToString a = numToString b then NUM(0)
            else case (a,b) of
                (VAR(n),MULT(m,VAR(k)))             => if k = n then simplify (MULT(MINUS(NUM(1),m),VAR(n))) else MINUS(a,b)
                |(VAR(n),MINUS(k,MULT(d,VAR(l))))   => if n = l then simplify (MINUS(MULT(PLUS(NUM(1),d),VAR(n)),k)) else simplify (PLUS(PLUS(MINUS(NUM(0),k),MULT(d,VAR(l))),VAR(n)))
                |(VAR(n),PLUS(k,MULT(d,VAR(l))))    => if n = l then simplify (PLUS(MINUS(NUM(0),k),MULT(MINUS(NUM(1),d),VAR(n)))) else MINUS(a,b)
                |(MULT(m,VAR(k)),VAR(n))            => if k = n then simplify (MULT(MINUS(m,NUM(1)),VAR(n))) else MINUS(a,b)
                |(MULT(n,VAR(m)),MULT(k,VAR(l)))    => if m = l then simplify (MULT(MINUS(n,k),VAR(m))) else MINUS(a,b) 
                |(MULT(n,VAR(m)),MINUS(k,MULT(d,VAR(l))))           => if m = l then simplify (MINUS(MULT(PLUS(n,d),VAR(m)),k)) else simplify (PLUS(PLUS(MINUS(NUM(0),k),MULT(n,VAR(m))),MULT(d,VAR(l))))
                |(MULT(n,VAR(m)),PLUS(k,VAR(l)))                    => if m = l then simplify (PLUS(MINUS(NUM(0),k),MULT(MINUS(n,NUM(1)),VAR(m)))) else MINUS(a,b) 
                |(MULT(n,VAR(m)),PLUS(k,MULT(d,VAR(l))))            => if m = l then simplify (PLUS(MINUS(NUM(0),k),MULT(MINUS(n,d),VAR(m)))) else MINUS(a,b) 
                |(MINUS(VAR(n),m),PLUS(k,MULT(d,VAR(l))))           => if n = l then simplify (PLUS(MINUS(NUM(0),PLUS(m,k)),MULT(MINUS(NUM(1),d),VAR(n)))) else MINUS(a,b) 
                |(MINUS(m,VAR(n)),MULT(d,VAR(l)))                   => if n = l then simplify (MINUS(m,MULT(PLUS(NUM(1),d),VAR(n)))) else MINUS(a,b)
                |(MINUS(m,VAR(n)),MINUS(d,VAR(l)))                  => if n = l then simplify (MINUS(m,d)) else simplify (PLUS(MINUS(MINUS(m,d),VAR(n)),VAR(l)))
                |(MINUS(m,VAR(n)),MINUS(k,MULT(d,VAR(l))))          => if n = l then simplify (MINUS(MINUS(m,k),MULT(MINUS(NUM(1),d),VAR(n)))) else simplify (MINUS(PLUS(MINUS(m,k),MULT(d,VAR(l))),VAR(n)))
                |(MINUS(m,MULT(c,VAR(n))),VAR(l))                   => if n = l then simplify (MINUS(m,MULT(PLUS(NUM(1),c),VAR(n)))) else MINUS(a,b)
                |(MINUS(m,MULT(c,VAR(n))),MINUS(k,MULT(d,VAR(l))))  => if n = l then simplify (MINUS(MINUS(m,k),MULT(MINUS(c,d),VAR(n)))) else simplify (PLUS(MINUS(MINUS(m,k),MULT(c,VAR(n))),MULT(d,VAR(l))))
                |(MINUS(m,MULT(c,VAR(n))),MINUS(d,VAR(l)))          => if n = l then simplify (MINUS(MINUS(m,d),MULT(MINUS(c,NUM(1)),VAR(n)))) else simplify (PLUS(MINUS(MINUS(m,d),MULT(c,VAR(n))),VAR(l)))
                |(MINUS(m,MULT(c,VAR(n))),MINUS(VAR(l),d))          => if n = l then simplify (MINUS(PLUS(m,d),MULT(PLUS(NUM(1),c),VAR(n)))) else MINUS(a,b) 
                |(MINUS(m,MULT(c,VAR(n))),PLUS(k,MULT(d,VAR(l))))   => if n = l then simplify (MINUS(MINUS(m,k),MULT(PLUS(c,d),VAR(n)))) else MINUS(a,b) 
                |(PLUS(c,MULT(n,VAR(l))),VAR(k))                    => if k = l then simplify (PLUS(c,MULT(MINUS(n,NUM(1)),VAR(k)))) else MINUS(a,b)
                |(PLUS(c,MULT(n,VAR(l))),MULT(m,VAR(k)))            => if k = l then simplify (PLUS(c,MULT(MINUS(n,m),VAR(k)))) else MINUS(a,b)
                |(PLUS(c,MULT(n,VAR(l))),MINUS(d,VAR(k)))           => if k = l then simplify (PLUS(MINUS(c,d),MULT(PLUS(NUM(1),n),VAR(l)))) else simplify (PLUS(PLUS(MINUS(c,d),MULT(n,VAR(l))),VAR(k)))
                |(PLUS(m,MULT(c,VAR(n))),MINUS(k,MULT(d,VAR(l))))   => if n = l then simplify (PLUS(MINUS(m,k),MULT(PLUS(c,d),VAR(n)))) else MINUS(a,b) 
                |(PLUS(m,MULT(d,VAR(k))),PLUS(c,MULT(n,VAR(l))))    => if k = l then simplify (PLUS(MINUS(m,c),MULT(MINUS(d,n),VAR(k)))) else MINUS(a,b)
                |(PLUS(m,VAR(k)),PLUS(c,MULT(n,VAR(l))))            => if k = l then simplify (PLUS(MINUS(m,c),MULT(MINUS(NUM(1),n),VAR(k)))) else MINUS(a,b)
                |(PLUS(m,VAR(k)),MULT(n,VAR(l)))                    => if k = l then simplify (PLUS(m,MULT(MINUS(NUM(1),n),VAR(k)))) else MINUS(a,b)
                |(PLUS(m,VAR(k)),MINUS(c,VAR(l)))                   => if k = l then simplify (PLUS(MINUS(m,c),MULT(NUM(2),VAR(k)))) else simplify (PLUS(PLUS(MINUS(m,c),VAR(k)),VAR(l)))
                |(PLUS(m,VAR(n)),b) => if m = b then VAR(n)
                                       else if onlyNum m andalso onlyNum b then simplify (PLUS(MINUS(m,b),VAR(n)))
                                       else MINUS(a,b)
                |(a,PLUS(c,VAR(k)))                         => if onlyNum a andalso onlyNum c then simplify (MINUS(MINUS(a,c),VAR(k))) else MINUS(a,b)
                |(a,PLUS(c,MULT(m,VAR(k))))                 => if onlyNum a andalso onlyNum c then simplify (MINUS(MINUS(a,c),MULT(m,VAR(k)))) else MINUS(a,b)
                |(a,MINUS(c,VAR(k)))                        => if onlyNum a andalso onlyNum c then simplify (PLUS(MINUS(a,c),VAR(k))) else MINUS(a,b)
                |(a,MINUS(VAR(k),c))                        => if onlyNum a andalso onlyNum c then simplify (MINUS(PLUS(a,c),VAR(k))) else MINUS(a,b)
                |(a,MINUS(c,MULT(m,VAR(k))))                => if onlyNum a andalso onlyNum c then simplify (PLUS(MINUS(a,c),MULT(m,VAR(k)))) else MINUS(a,b)
                |(a,MINUS(MULT(m,VAR(k)),c))                => if onlyNum a andalso onlyNum c then simplify (MINUS(PLUS(a,c),MULT(m,VAR(k)))) else MINUS(a,b)
                |(a,PLUS(c,FRAC(m,VAR(k))))                 => if onlyNum a andalso onlyNum c then simplify (MINUS(MINUS(a,c),FRAC(m,VAR(k)))) else MINUS(a,b)
                |(a,MINUS(c,FRAC(m,VAR(k))))                => if onlyNum a andalso onlyNum c then simplify (PLUS(MINUS(a,c),FRAC(m,VAR(k)))) else MINUS(a,b)
                |(MINUS(c,VAR(k)),b)                        => if onlyNum b andalso onlyNum c then simplify (MINUS(MINUS(c,b),VAR(k))) else MINUS(a,b)
                |(MINUS(c,MULT(d,VAR(k))),MULT(e,VAR(l)))   => if onlyNum c andalso k = l then simplify (MINUS(c,MULT(PLUS(d,e),VAR(k)))) else MINUS(a,b)
                |(MINUS(c,MULT(d,VAR(k))),b)                => if onlyNum c andalso onlyNum b then simplify (MINUS(MINUS(c,b),MULT(d,VAR(k)))) else MINUS(a,b)
                |(PLUS(c,MULT(d,VAR(k))),b)                 => if onlyNum c andalso onlyNum b then simplify (PLUS(MINUS(c,b),MULT(d,VAR(k)))) else MINUS(a,b)
                |(a, MINUS(k,m)) => if a = k then m 
                                    else if onlyNum a andalso onlyNum k then simplify (PLUS(MINUS(a,k),m))
                                    else MINUS(a,b)
                |(PLUS(c,d),b) => if c = b then d else if d = b then c else MINUS(a,b)
                |(a,PLUS(c,d)) => if a = c then simplify (MINUS(NUM(0),d)) else if a = d then simplify (MINUS(NUM(0),c)) else MINUS(a,b)
                |_ => MINUS(a,b)
        end
    |simplify (MULT(x,y)) =
        let val a = simplify x 
            val b = simplify y in
            if numToString a = numToString (NUM(0)) orelse numToString b = numToString (NUM(0)) then NUM(0)
            else if numToString a = numToString (NUM(1)) then b
            else if numToString b = numToString (NUM(1)) then a
            else if numToString a = numToString (NUM(~1)) then MINUS(NUM(0),b)
            else if numToString b = numToString (NUM(~1)) then MINUS(NUM(0),a)
            else case (a,b) of
            (VAR(k),MINUS(c,FRAC(n,VAR(l))))    => if k = l then simplify (MINUS(MULT(c,VAR(k)),n)) else MULT(a,b)
            |(MINUS(c,FRAC(n,VAR(l))),VAR(k))   => if k = l then simplify (MINUS(MULT(c,VAR(k)),n)) else MULT(a,b)
            |(VAR(k),PLUS(c,FRAC(n,VAR(l))))    => if k = l then simplify (PLUS(n,MULT(c,VAR(k)))) else MULT(a,b)
            |(PLUS(c,FRAC(n,VAR(l))),VAR(k))    => if k = l then simplify (PLUS(n,MULT(c,VAR(k)))) else MULT(a,b)
            |(a,MULT(FRAC(c,k),l))  => if a = k then simplify (MULT(c,l)) 
                                       else if onlyNum a andalso onlyNum c andalso onlyNum k then simplify (MULT(MULT(a,FRAC(c,k)),l))
                                       else MULT(a,b)
            |(MULT(FRAC(c,k),l),b)  => if b = k then simplify (MULT(c,l)) 
                                       else if onlyNum b andalso onlyNum c andalso onlyNum k then simplify (MULT(MULT(b,FRAC(c,k)),l))
                                       else MULT(a,b)        
            |(FRAC(n,m),MINUS(d,MULT(c,VAR(k))))            => if m = b then n else if onlyNum a andalso onlyNum d then simplify (MINUS(MULT(a,d),MULT(MULT(a,c),VAR(k)))) else MULT(a,b)
            |(MINUS(d,MULT(c,VAR(k))),FRAC(n,m))            => if m = a then n else if onlyNum b andalso onlyNum d then simplify (MINUS(MULT(b,d),MULT(MULT(b,c),VAR(k)))) else MULT(a,b)
            |(MINUS(n,FRAC(m,l)),MINUS(d,MULT(c,VAR(k))))   => if l = b then simplify (MINUS(MULT(n,b),m)) else if onlyNum a andalso onlyNum d then simplify (MINUS(MULT(a,d),MULT(MULT(a,c),VAR(k)))) else MULT(a,b)
            |(MINUS(d,MULT(c,VAR(k))),MINUS(n,FRAC(m,l)))   => if a = l then simplify (MINUS(MULT(n,a),m)) else if onlyNum b andalso onlyNum d then simplify (MINUS(MULT(b,d),MULT(MULT(b,c),VAR(k)))) else MULT(a,b)
            |(a,MINUS(MULT(c,VAR(k)),d))            => if onlyNum a andalso onlyNum d then simplify (MINUS(MULT(MULT(a,c),VAR(k)),MULT(a,d))) else MULT(a,b)
            |(MINUS(MULT(c,VAR(k)),d),b)            => if onlyNum b andalso onlyNum d then simplify (MINUS(MULT(MULT(b,c),VAR(k)),MULT(b,d))) else MULT(a,b)
            |(a,MINUS(d,MULT(c,VAR(k))))            => if onlyNum a andalso onlyNum d then simplify (MINUS(MULT(a,d),MULT(MULT(a,c),VAR(k)))) else MULT(a,b)
            |(MINUS(d,MULT(c,VAR(k))),b)            => if onlyNum b andalso onlyNum d then simplify (MINUS(MULT(b,d),MULT(MULT(b,c),VAR(k)))) else MULT(a,b)
            |(a,PLUS(d,MULT(c,VAR(k))))             => if onlyNum a then simplify (PLUS(MULT(a,d),MULT(MULT(a,c),VAR(k)))) else MULT(a,b)
            |(PLUS(d,MULT(c,VAR(k))),b)             => if onlyNum b then simplify (PLUS(MULT(b,d),MULT(MULT(b,c),VAR(k)))) else MULT(a,b)
            |(MINUS(c,FRAC(k,l)),MINUS(d,VAR(n)))   => if l = b then simplify (PLUS(MINUS(NUM(0),k),MULT(c,l))) else MULT(a,b)
            |(FRAC(c,k),MINUS(m,VAR(n)))            => if k = b then c else MULT(a,b)
            |(a,MINUS(c,VAR(k)))    => if onlyNum a andalso onlyNum c then simplify (MINUS(MULT(a,c),MULT(a,VAR(k)))) else MULT(a,b)
            |(a,MINUS(c,FRAC(k,l))) => if a = l then simplify (MINUS(MULT(c,a),k)) else MULT(a,b)
            |(MINUS(c,FRAC(k,l)),b) => if b = l then simplify (MINUS(MULT(c,b),k)) else MULT(a,b)           
            |(a,MULT(c,VAR(k)))     => if onlyNum a andalso onlyNum c then simplify (MULT(MULT(a,c),VAR(k))) else MULT(a,b)
            |(a,FRAC(c,k))  => if a = k then c else MULT(a,b)
            |(FRAC(c,k),b)  => if b = k then c else MULT(a,b)
            |(a,MINUS(c,k)) => if onlyNum a andalso onlyNum c then simplify (MINUS(MULT(a,c),MULT(a,k))) else MULT(a,b)
            |(MINUS(c,k),b) => if onlyNum b andalso onlyNum c then simplify (MINUS(MULT(b,c),MULT(b,k))) else MULT(a,b)
            |(a,PLUS(c,k))  => if onlyNum a andalso onlyNum c then simplify (PLUS(MULT(a,c),MULT(a,k))) else MULT(a,b)
            |(PLUS(c,k),b)  => if onlyNum b andalso onlyNum c then simplify (PLUS(MULT(b,c),MULT(b,k))) else MULT(a,b)
            |(a,MULT(c,k))  => if onlyNum a andalso onlyNum c then simplify (MULT(MULT(a,c),k)) else MULT(a,b)
            |(MULT(c,k),b)  => if onlyNum b andalso onlyNum c then simplify (MULT(MULT(b,c),k)) else MULT(a,b)
            |(VAR(k),b) => if onlyNum b then MULT(b,VAR(k)) else MULT(a,b)
            |_ => MULT(a,b)
        end
    |simplify (FRAC(x,y)) =
        let val a = simplify x 
            val b = simplify y in
            if numToString a = numToString (NUM(0)) then NUM(0)
            else if numToString a = numToString b then NUM(1)
            else if numToString b = numToString (NUM(0)) then raise NumError
            else case (a,b) of
            (a,NUM(1)) => a
            |(MULT(c,VAR(k)),b) => if c = b then VAR(k)
                                   else if b = (VAR(k)) then c
                                   else if onlyNum b andalso onlyNum c then simplify (MULT(FRAC(c,b),VAR(k))) else FRAC(a,b)
            |(MULT(VAR(k),c),b) => if c = b then VAR(k)
                                   else if b = (VAR(k)) then c
                                   else if onlyNum b andalso onlyNum c then simplify (MULT(FRAC(c,b),VAR(k))) else FRAC(a,b)
            |(MULT(c,k),b)      => if b = c then k else if b = k then c else FRAC(a,b)
            |(PLUS(c,VAR(k)),VAR(l))            => if k = l then simplify (PLUS(NUM(1),FRAC(c,VAR(l)))) else FRAC(a,b)
            |(MINUS(c,MULT(d,VAR(k))),VAR(l))   => if k = l then simplify (PLUS(MINUS(NUM(0),d),FRAC(c,VAR(k)))) else FRAC(a,b)
            |(MINUS(MULT(d,VAR(k)),c),VAR(l))   => if k = l then simplify (MINUS(d,FRAC(c,VAR(k)))) else FRAC(a,b)
            |(PLUS(c,MULT(d,VAR(k))),VAR(l))    => if k = l then simplify (PLUS(d,FRAC(c,VAR(k)))) else FRAC(a,b)
            |(MINUS(VAR(k),c),b)    => if onlyNum b andalso onlyNum c then simplify (MINUS(MULT(FRAC(NUM(1),b),VAR(k)),FRAC(c,b))) else FRAC(a,b)
            |(MINUS(c,VAR(k)),b)    => if onlyNum b andalso onlyNum c then simplify (MINUS(FRAC(c,b),MULT(FRAC(NUM(1),b),VAR(k)))) else FRAC(a,b)
            |(PLUS(c,VAR(k)),b)     => if onlyNum b andalso onlyNum c then simplify (PLUS(FRAC(c,b),MULT(FRAC(NUM(1),b),VAR(k)))) else FRAC(a,b)
            |(MINUS(c,MULT(d,VAR(k))),b)    => if onlyNum b andalso onlyNum c andalso onlyNum d then simplify (MINUS(FRAC(c,b),MULT(FRAC(d,b),VAR(k)))) else FRAC(a,b)
            |(MINUS(MULT(d,VAR(k)),c),b)    => if onlyNum b andalso onlyNum c then simplify (MINUS(MULT(FRAC(d,b),VAR(k)),FRAC(c,b))) else FRAC(a,b)
            |(PLUS(c,MULT(d,VAR(k))),b)     => if onlyNum b andalso onlyNum c andalso onlyNum d then simplify (PLUS(FRAC(c,b),MULT(FRAC(d,b),VAR(k)))) else FRAC(a,b)
            |_ => FRAC(a,b)
        end
    |simplify x = x;

fun resolve a b (n:int) =
    let fun countU [] = 0
            |countU (x::xs) = if x = U then (countU xs) + 1 else (countU xs)
        fun contains n (PLUS(a,b)) = contains n a orelse contains n b
            |contains n (MINUS(a,b)) = contains n a orelse contains n b
            |contains n (MULT(a,b)) = contains n a orelse contains n b
            |contains n (FRAC(a,b)) = contains n a orelse contains n b
            |contains n x = n = x 
        fun replace x y (PLUS(a,b)) =   let val c = replace x y a 
                                            val d = replace x y b in
                                            PLUS(c,d)
                                        end
            |replace x y (MINUS(a,b)) = let val c = replace x y a 
                                            val d = replace x y b in
                                            MINUS(c,d)
                                        end
            |replace x y (MULT(a,b)) =  let val c = replace x y a 
                                            val d = replace x y b in
                                            MULT(c,d)
                                        end
            |replace x y (FRAC(a,b)) =  let val c = replace x y a 
                                            val d = replace x y b in
                                            FRAC(c,d)
                                        end
            |replace x y z = if y = z then simplify x else z
        fun solveVar x y =
            case (simplify x, simplify y) of
            (VAR(n),y) => SOME (VAR(n),y)
            |(x,VAR(n)) => SOME (VAR(n),x)
            |(MINUS(n,MULT(m,VAR(w))),MULT(k,VAR(l))) => if w = l then SOME (VAR(w), FRAC(n,PLUS(m,k))) else NONE
            |(MULT(k,VAR(l)),MINUS(n,MULT(m,VAR(w)))) => if w = l then SOME (VAR(w), FRAC(n,PLUS(m,k))) else NONE
            |(FRAC(MINUS(n,MULT(m,VAR(k))),VAR(l)),y) => if k = l then SOME (VAR(k), FRAC(n,PLUS(m,y))) else NONE
            |(x,FRAC(MINUS(n,MULT(m,VAR(k))),VAR(l))) => if k = l then SOME (VAR(k), FRAC(n,PLUS(m,x))) else NONE
            |(FRAC(MINUS(n,MULT(m,MINUS(s,VAR(k)))),VAR(l)),y) => if k = l then SOME (VAR(k), FRAC(MINUS(n,MULT(m,s)),MINUS(y,m))) else NONE
            |(x,FRAC(MINUS(n,MULT(m,MINUS(s,VAR(k)))),VAR(l))) => if k = l then SOME (VAR(k), FRAC(MINUS(n,MULT(m,s)),MINUS(x,m))) else NONE
            |(FRAC(MINUS(n,MULT(MINUS(s,VAR(k)),m)),VAR(l)),y) => if k = l then SOME (VAR(k), FRAC(MINUS(n,MULT(m,s)),MINUS(y,m))) else NONE
            |(x,FRAC(MINUS(n,MULT(MINUS(s,VAR(k)),m)),VAR(l))) => if k = l then SOME (VAR(k), FRAC(MINUS(n,MULT(m,s)),MINUS(x,m))) else NONE
            |(FRAC(PLUS(n,MULT(m,VAR(k))),VAR(l)),y) => if k = l then SOME (VAR(k), FRAC(n,MINUS(y,m))) else NONE
            |(x,FRAC(PLUS(n,MULT(m,VAR(k))),VAR(l))) => if k = l then SOME (VAR(k), FRAC(n,MINUS(x,m))) else NONE
            |(x,PLUS(n,MULT(m,VAR(k)))) => SOME (VAR(k),FRAC(MINUS(x,n),m))
            |(PLUS(n,MULT(m,VAR(k))),y) => SOME (VAR(k),FRAC(MINUS(y,n),m))
            |(x,MINUS(MULT(m,VAR(k)),n)) => SOME (VAR(k),FRAC(PLUS(x,n),m))
            |(MINUS(MULT(m,VAR(k)),n),y) => SOME (VAR(k),FRAC(PLUS(y,n),m))
            |(x,MINUS(n,MULT(m,VAR(k)))) => SOME (VAR(k),FRAC(MINUS(n,x),m))
            |(MINUS(n,MULT(m,VAR(k))),y) => SOME (VAR(k),FRAC(MINUS(n,y),m))
            |(MULT(m,VAR(n)),y) => SOME (VAR(n),FRAC(y,m))
            |(x,MULT(m,VAR(n))) => SOME (VAR(n),FRAC(x,m))
            |(MINUS(c,VAR(n)),y) => SOME (VAR(n),MINUS(c,y))
            |(x,MINUS(c,VAR(n))) => SOME (VAR(n),MINUS(c,x))
            |(MINUS(VAR(n),c),y) => SOME (VAR(n),PLUS(c,y))
            |(x,MINUS(VAR(n),c)) => SOME (VAR(n),PLUS(c,x))
            |_ => NONE
        fun filterNum x y nx ny =
            case (x,y) of
            ([],[]) => []
            |(x::xs,y::ys) =>   if onlyNum x then x::(filterNum xs ys nx ny)
                                else if onlyNum y then y::(filterNum xs ys nx ny)
                                else if x = U then y::(filterNum xs ys nx ny)
                                else if y = U then x::(filterNum xs ys nx ny)
                                else if nx > ny then y::(filterNum xs ys nx ny)
                                else x::(filterNum xs ys nx ny)
            |_ => raise NumError
        fun tResolve a b c d (e:int) =
            if e = 0 then ((List.rev c)@a, (List.rev d)@b)
            else
            (case (a, b) of
            ([],[]) => (List.rev c, List.rev d)
            |(a::aas,b::bbs) => 
            let val x = simplify a
                val y = simplify b 
                val xs = List.map simplify aas
                val ys = List.map simplify bbs in             
                    if x = U then tResolve xs ys (y::c) (y::d) (e-1)
                    else if y = U then tResolve xs ys (x::c) (x::d) (e-1)
                    else if (x = y orelse (numToString x) = (numToString y)) andalso String.size (numToString x) > 1 then tResolve xs ys (x::c) (y::d) (e-1)
                    else if onlyNum y then 
                        (case (x,y) of
                            (VAR(n),y) => let fun f z = replace y x z 
                                                val zs = List.map f xs 
                                                val ws = List.map f c in
                                                tResolve zs ys (y::ws) (y::d) (e-1)
                                            end
                            |(FRAC(k,VAR(n)),y) => if contains (VAR(n)) k then 
                                                     case (solveVar x y) of
                                                         NONE => tResolve xs ys (y::c) (y::d) (e-1)
                                                        |SOME(a,b) =>   let fun f z = replace b a z
                                                                            val zx = List.map f xs
                                                                            val wx = List.map f c in 
                                                                            tResolve zx ys (y::wx) (y::d) (e-1)
                                                                        end
                                                   else if String.size n > 1 then 
                                                        let fun f z = replace (FRAC(k,y)) (VAR(n)) z
                                                            val zx = List.map f xs 
                                                            val wx = List.map f c
                                                            val zy = List.map f ys 
                                                            val wy = List.map f d in
                                                            tResolve zx zy (y::wx) (y::wy) (e-1)
                                                        end
                                                   else let fun f z = replace (FRAC(k,y)) (VAR(n)) z
                                                            val zs = List.map f xs 
                                                            val ws = List.map f c in
                                                            tResolve zs ys (y::ws) (y::d) (e-1)
                                                        end
                            |(FRAC(VAR(n),k),y) =>  let fun f z = replace (MULT(y,k)) (VAR(n)) z
                                                        val zs = List.map f xs 
                                                        val ws = List.map f c in
                                                        tResolve zs ys (y::ws) (y::d) (e-1)
                                                    end 
                            |(FRAC(MINUS(VAR(n),m),k),y) => let fun f z = replace (PLUS(MULT(y,k),m)) (VAR(n)) z
                                                                val zs = List.map f xs 
                                                                val ws = List.map f c in
                                                                tResolve zs ys (y::ws) (y::d) (e-1)
                                                            end
                            |(FRAC(MULT(m,VAR(n)),MINUS(k,MULT(q,VAR(l)))),y) => if n = l then 
                                                                                let fun f z = replace (FRAC(MULT(y,k),PLUS(m,MULT(y,q)))) (VAR(n)) z
                                                                                    val zs = List.map f xs 
                                                                                    val ws = List.map f c in
                                                                                    tResolve zs ys (y::ws) (y::d) (e-1)
                                                                                end
                                                                               else let fun f z = replace (FRAC(MULT(y,MINUS(k,MULT(q,VAR(l)))),m)) (VAR(n)) z
                                                                                        val zs = List.map f xs 
                                                                                        val ws = List.map f c in
                                                                                        tResolve zs ys (y::ws) (y::d) (e-1)
                                                                                    end
                            |(FRAC(MULT(m,VAR(n)),MINUS(k,VAR(l))),y) => if n = l then  let fun f z = replace (FRAC(MULT(y,k),PLUS(y,m))) (VAR(n)) z
                                                                                            val zs = List.map f xs 
                                                                                            val ws = List.map f c in
                                                                                            tResolve zs ys (y::ws) (y::d) (e-1)
                                                                                        end
                                                                        else let fun f z = replace (FRAC(MULT(y,MINUS(k,VAR(l))),m)) (VAR(n)) z
                                                                                 val zs = List.map f xs 
                                                                                 val ws = List.map f c in
                                                                                 tResolve zs ys (y::ws) (y::d) (e-1)
                                                                             end
                            |(FRAC(k,MULT(m,VAR(n))),y) => let fun f z = replace (FRAC(k,MULT(y,m))) (VAR(n)) z
                                                                val zx = List.map f xs 
                                                                val zy = List.map f ys 
                                                                val wx = List.map f c
                                                                val wy = List.map f d in
                                                                tResolve zx zy (y::wx) (y::wy) (e-1)
                                                            end
                            |(FRAC(MULT(m,VAR(n)),k),y) => let fun f z = replace (FRAC(MULT(y,k),m)) (VAR(n)) z
                                                                val zs = List.map f xs 
                                                                val ws = List.map f c in
                                                                tResolve zs ys (y::ws) (y::d) (e-1)
                                                            end
                            |(FRAC(k,MINUS(m,VAR(n))),y) => let fun f z = replace (FRAC(MINUS(MULT(y,m),k),y)) (VAR(n)) z
                                                                val zs = List.map f xs 
                                                                val ws = List.map f c in
                                                                tResolve zs ys (y::ws) (y::d) (e-1)
                                                            end
                            |(FRAC(k,MINUS(m,MULT(l,VAR(n)))),y) => let fun f z = replace (FRAC(MINUS(MULT(y,m),k),MULT(y,l))) (VAR(n)) z
                                                                        val zs = List.map f xs 
                                                                        val ws = List.map f c in
                                                                        tResolve zs ys (y::ws) (y::d) (e-1)
                                                                    end
                            |(FRAC(MINUS(MULT(m,VAR(n)),k),PLUS(q,MULT(p,VAR(l)))),y) => if n = l then
                                                                                            let fun f z = replace (FRAC(PLUS(MULT(y,q),k),MINUS(m,MULT(y,p)))) (VAR(n)) z
                                                                                                val zs = List.map f xs 
                                                                                                val ws = List.map f c in
                                                                                                tResolve zs ys (y::ws) (y::d) (e-1)
                                                                                            end
                                                                                          else tResolve xs ys (y::c) (y::d) (e-1)
                            |(MULT(k,VAR(n)),y) =>  let fun f z = replace (FRAC(y,k)) (VAR(n)) z
                                                        val zs = List.map f xs 
                                                        val ws = List.map f c in
                                                        tResolve zs ys (y::ws) (y::d) (e-1)
                                                    end
                            |(MULT(VAR(n),k),y) =>  let fun f z = replace (FRAC(y,k)) (VAR(n)) z
                                                        val zs = List.map f xs 
                                                        val ws = List.map f c in
                                                        tResolve zs ys (y::ws) (y::d) (e-1)
                                                    end
                            |(MULT(PLUS(l,VAR(n)),k),y) =>  let fun f z = replace (MINUS(FRAC(y,k),l)) (VAR(n)) z
                                                                val zs = List.map f xs 
                                                                val ws = List.map f c in
                                                                tResolve zs ys (y::ws) (y::d) (e-1)
                                                            end
                            |(MULT(k,PLUS(l,VAR(n))),y) =>  let fun f z = replace (MINUS(FRAC(y,k),l)) (VAR(n)) z
                                                                val zs = List.map f xs 
                                                                val ws = List.map f c in
                                                                tResolve zs ys (y::ws) (y::d) (e-1)
                                                            end
                            |(MINUS(k,VAR(n)),y) => let fun f z = replace (MINUS(k,y)) (VAR(n)) z
                                                        val zs = List.map f xs 
                                                        val ws = List.map f c in
                                                        tResolve zs ys (y::ws) (y::d) (e-1)
                                                    end
                            |(MINUS(VAR(n),k),y) => let fun f z = replace (PLUS(y,k)) (VAR(n)) z
                                                        val zs = List.map f xs 
                                                        val ws = List.map f c in
                                                        tResolve zs ys (y::ws) (y::d) (e-1)
                                                    end
                            |(MINUS(k,MULT(VAR(n),m)),y) => let fun f z = replace (FRAC(MINUS(k,y),m)) (VAR(n)) z
                                                                val zs = List.map f xs 
                                                                val ws = List.map f c in
                                                                tResolve zs ys (y::ws) (y::d) (e-1)
                                                            end
                            |(MINUS(k,MULT(m,VAR(n))),y) => let fun f z = replace (FRAC(MINUS(k,y),m)) (VAR(n)) z
                                                                val zs = List.map f xs 
                                                                val ws = List.map f c in
                                                                tResolve zs ys (y::ws) (y::d) (e-1)
                                                            end
                            |(MINUS(FRAC(VAR(n),m),k),y) => let fun f z = replace (MULT(PLUS(y,k),m)) (VAR(n)) z
                                                                val zs = List.map f xs 
                                                                val ws = List.map f c in
                                                                tResolve zs ys (y::ws) (y::d) (e-1)
                                                            end
                            |(PLUS(k,VAR(n)),y) =>  let fun f z = replace (MINUS(y,k)) (VAR(n)) z
                                                        val zs = List.map f xs 
                                                        val ws = List.map f c in
                                                        tResolve zs ys (y::ws) (y::d) (e-1)
                                                    end
                            |(PLUS(k,MULT(m,VAR(n))),y) => let fun f z = replace (FRAC(MINUS(y,k),m)) (VAR(n)) z
                                                               val zs = List.map f xs 
                                                               val ws = List.map f c in
                                                               tResolve zs ys (y::ws) (y::d) (e-1)
                                                            end
                            |(PLUS(k,MULT(VAR(n),m)),y) =>  let fun f z = replace (FRAC(MINUS(y,k),m)) (VAR(n)) z
                                                               val zs = List.map f xs 
                                                               val ws = List.map f c in
                                                               tResolve zs ys (y::ws) (y::d) (e-1)
                                                            end
                            |(PLUS(k,FRAC(m,VAR(n))),y) => let fun f z = replace (FRAC(m,MINUS(y,k))) (VAR(n)) z
                                                               val zs = List.map f xs 
                                                               val ws = List.map f c in
                                                               tResolve zs ys (y::ws) (y::d) (e-1)
                                                            end
                            |_ => tResolve xs ys (y::c) (y::d) (e-1))
                    else if onlyNum x then
                        (case (x,y) of
                            (x,VAR(n)) =>  let fun f z = replace x y z 
                                                val zs = List.map f ys 
                                                val ws = List.map f d in
                                                tResolve xs zs (x::c) (x::ws) (e-1)
                                            end
                            |(x,FRAC(VAR(n),k)) => let fun f z = replace (MULT(x,k)) (VAR(n)) z
                                                        val zs = List.map f ys 
                                                        val ws = List.map f d in
                                                        tResolve xs zs (x::c) (x::ws) (e-1)
                                                    end 
                            |(x,FRAC(k,VAR(n))) => if contains (VAR(n)) k then 
                                                     case (solveVar x y) of
                                                         NONE => tResolve xs ys (x::c) (x::d) (e-1)
                                                        |SOME(a,b) =>   let fun f z = replace b a z
                                                                            val zy = List.map f ys
                                                                            val wy = List.map f d in 
                                                                            tResolve xs zy (x::c) (y::wy) (e-1)
                                                                        end
                                                   else if String.size n > 1 then
                                                        let fun f z = replace (FRAC(k,x)) (VAR(n)) z
                                                            val zx = List.map f xs 
                                                            val wx = List.map f c
                                                            val zy = List.map f ys 
                                                            val wy = List.map f d in
                                                            tResolve zx zy (x::wx) (x::wy) (e-1)
                                                        end 
                                                    else let fun f z = replace (FRAC(k,x)) (VAR(n)) z
                                                             val zs = List.map f ys 
                                                             val ws = List.map f d in
                                                             tResolve xs zs (x::c) (x::ws) (e-1)
                                                         end 
                            |(x,FRAC(MINUS(VAR(n),m),k)) => let fun f z = replace (PLUS(MULT(x,k),m)) (VAR(n)) z
                                                                val zs = List.map f ys 
                                                                val ws = List.map f d in
                                                                tResolve xs zs (x::c) (x::ws) (e-1)
                                                            end                         
                            |(x,FRAC(MULT(m,VAR(n)),MINUS(k,MULT(q,VAR(l))))) => if n = l then 
                                                                                let fun f z = replace (FRAC(MULT(x,k),PLUS(m,MULT(x,q)))) (VAR(n)) z
                                                                                    val zs = List.map f ys 
                                                                                    val ws = List.map f d in
                                                                                    tResolve xs zs (x::c) (x::ws) (e-1)
                                                                                end 
                                                                               else let fun f z = replace (FRAC(MULT(x,MINUS(k,MULT(q,VAR(l)))),m)) (VAR(n)) z
                                                                                        val zs = List.map f ys 
                                                                                        val ws = List.map f d in
                                                                                        tResolve xs zs (x::c) (x::ws) (e-1)
                                                                                    end 
                            |(x,FRAC(MULT(m,VAR(n)),MINUS(k,VAR(l)))) => if n = l then  let fun f z = replace (FRAC(MULT(x,k),PLUS(x,m))) (VAR(n)) z
                                                                                            val zs = List.map f ys 
                                                                                            val ws = List.map f d in
                                                                                            tResolve xs zs (x::c) (x::ws) (e-1)
                                                                                        end 
                                                                         else let fun f z = replace (FRAC(MULT(x,MINUS(k,VAR(l))),m)) (VAR(n)) z
                                                                                  val zs = List.map f ys 
                                                                                  val ws = List.map f d in
                                                                                  tResolve xs zs (x::c) (x::ws) (e-1)
                                                                              end 
                            |(x,FRAC(MULT(m,VAR(n)),k)) =>  let fun f z = replace (FRAC(MULT(x,k),m)) (VAR(n)) z
                                                                val zs = List.map f ys 
                                                                val ws = List.map f d in
                                                                tResolve xs zs (x::c) (x::ws) (e-1)
                                                            end   
                            |(x,FRAC(k,MULT(m,VAR(n)))) =>  let fun f z = replace (FRAC(k,MULT(x,m))) (VAR(n)) z
                                                                val zx = List.map f xs 
                                                                val zy = List.map f ys 
                                                                val wx = List.map f c
                                                                val wy = List.map f d in
                                                                tResolve zx zy (x::wx) (x::wy) (e-1)
                                                            end   
                            |(x,FRAC(k,MINUS(m,VAR(n)))) => let fun f z = replace (FRAC(MINUS(MULT(x,m),k),x)) (VAR(n)) z
                                                                val zs = List.map f ys 
                                                                val ws = List.map f d in
                                                                tResolve xs zs (x::c) (x::ws) (e-1)
                                                            end 
                            |(x,FRAC(k,MINUS(m,MULT(l,VAR(n))))) => let fun f z = replace (FRAC(MINUS(MULT(x,m),k),MULT(x,l))) (VAR(n)) z
                                                                        val zs = List.map f ys 
                                                                        val ws = List.map f d in
                                                                        tResolve xs zs (x::c) (x::ws) (e-1)
                                                                    end 
                            |(x,FRAC(MINUS(MULT(m,VAR(n)),k),PLUS(q,MULT(p,VAR(l))))) => if n = l then
                                                                                        let fun f z = replace (FRAC(PLUS(MULT(x,q),k),MINUS(m,MULT(x,p)))) (VAR(n)) z
                                                                                            val zs = List.map f ys 
                                                                                            val ws = List.map f d in
                                                                                            tResolve xs zs (x::c) (x::ws) (e-1)
                                                                                        end 
                                                                                        else tResolve xs ys (x::c) (x::d) (e-1)
                            |(x,MULT(k,VAR(n))) => let fun f z = replace (FRAC(x,k)) (VAR(n)) z
                                                        val zs = List.map f ys 
                                                        val ws = List.map f d in
                                                        tResolve xs zs (x::c) (x::ws) (e-1)
                                                    end
                            |(x,MULT(VAR(n),k)) => let fun f z = replace (FRAC(x,k)) (VAR(n)) z
                                                        val zs = List.map f ys 
                                                        val ws = List.map f d in
                                                        tResolve xs zs (x::c) (x::ws) (e-1)
                                                    end
                            |(x,MULT(PLUS(l,VAR(n)),k)) =>  let fun f z = replace (MINUS(FRAC(x,k),l)) (VAR(n)) z
                                                                val zs = List.map f ys 
                                                                val ws = List.map f d in
                                                                tResolve xs zs (x::c) (x::ws) (e-1)
                                                            end
                            |(x,MULT(k,PLUS(l,VAR(n)))) =>  let fun f z = replace (MINUS(FRAC(x,k),l)) (VAR(n)) z
                                                                val zs = List.map f ys 
                                                                val ws = List.map f d in
                                                                tResolve xs zs (x::c) (x::ws) (e-1)
                                                            end
                            |(x,MINUS(k,VAR(n))) => let fun f z = replace (MINUS(k,x)) (VAR(n)) z
                                                        val zs = List.map f ys 
                                                        val ws = List.map f d in
                                                        tResolve xs zs (x::c) (x::ws) (e-1)
                                                    end
                            |(x,MINUS(VAR(n),k)) => let fun f z = replace (PLUS(x,k)) (VAR(n)) z
                                                        val zs = List.map f ys 
                                                        val ws = List.map f d in
                                                        tResolve xs zs (x::c) (x::ws) (e-1)
                                                    end
                            |(x,MINUS(k,MULT(m,VAR(n)))) => let fun f z = replace (FRAC(MINUS(k,x),m)) (VAR(n)) z
                                                                val zs = List.map f ys 
                                                                val ws = List.map f d in
                                                                tResolve xs zs (x::c) (x::ws) (e-1)
                                                            end
                            |(x,MINUS(k,MULT(VAR(n),m))) => let fun f z = replace (FRAC(MINUS(k,x),m)) (VAR(n)) z
                                                                val zs = List.map f ys 
                                                                val ws = List.map f d in
                                                                tResolve xs zs (x::c) (x::ws) (e-1)
                                                            end
                            |(x,MINUS(FRAC(VAR(n),m),k)) => let fun f z = replace (MULT(PLUS(y,k),m)) (VAR(n)) z
                                                                val zs = List.map f ys 
                                                                val ws = List.map f d in
                                                                tResolve xs zs (x::c) (x::ws) (e-1)
                                                            end
                            |(x,PLUS(k,VAR(n))) =>  let fun f z = replace (MINUS(x,k)) (VAR(n)) z
                                                        val zs = List.map f ys 
                                                        val ws = List.map f d in
                                                        tResolve xs zs (x::c) (x::ws) (e-1)
                                                    end
                            |(x,PLUS(k,MULT(m,VAR(n)))) => let fun f z = replace (FRAC(MINUS(x,k),m)) (VAR(n)) z
                                                                val zs = List.map f ys 
                                                                val ws = List.map f d in
                                                                tResolve xs zs (x::c) (x::ws) (e-1)
                                                            end
                            |(x,PLUS(k,MULT(VAR(n),m))) => let fun f z = replace (FRAC(MINUS(x,k),m)) (VAR(n)) z
                                                                val zs = List.map f ys 
                                                                val ws = List.map f d in
                                                                tResolve xs zs (x::c) (x::ws) (e-1)
                                                            end
                            |(x,PLUS(k,FRAC(m,VAR(n)))) => let fun f z = replace (FRAC(m,MINUS(x,k))) (VAR(n)) z
                                                                val zs = List.map f ys 
                                                                val ws = List.map f d in
                                                                tResolve xs zs (x::c) (x::ws) (e-1)
                                                            end
                            |_ => tResolve xs ys (x::c) (x::d) (e-1))
                    else (case (x,y) of
                            (VAR(n),VAR(m)) => let fun fx z = replace (VAR(n^m)) (VAR(n)) z
                                                        fun fy z = replace (VAR(n^m)) (VAR(m)) z
                                                        val zx = List.map fx xs
                                                        val wx = List.map fx c
                                                        val zy = List.map fy ys
                                                        val wy = List.map fy d in
                                                        tResolve zx zy ((VAR(n^m))::wx) ((VAR(n^m))::wy) (e-1)
                                                end
                            |(VAR(n),MINUS(NUM(1),VAR(m))) =>   let fun fx z = replace (VAR(n^m)) (VAR(n)) z
                                                                    fun fy z = replace (MINUS(NUM(1),VAR(n^m))) (VAR(m)) z
                                                                    val zx = List.map fx xs
                                                                    val wx = List.map fx c
                                                                    val zy = List.map fy ys
                                                                    val wy = List.map fy d in
                                                                    tResolve zx zy ((VAR(n^m))::wx) ((VAR(n^m))::wy) (e-1)
                                                                end
                            |(MINUS(NUM(1),VAR(n)),VAR(m)) =>   let fun fx z = replace (MINUS(NUM(1),VAR(n^m))) (VAR(n)) z
                                                                    fun fy z = replace (VAR(n^m)) (VAR(m)) z
                                                                    val zx = List.map fx xs
                                                                    val wx = List.map fx c
                                                                    val zy = List.map fy ys
                                                                    val wy = List.map fy d in
                                                                    tResolve zx zy ((VAR(n^m))::wx) ((VAR(n^m))::wy) (e-1)
                                                                end
                            |(MINUS(NUM(1),VAR(n)),MINUS(NUM(1),VAR(m))) => let fun fx z = replace (VAR(n^m)) (VAR(n)) z
                                                                                fun fy z = replace (VAR(n^m)) (VAR(m)) z
                                                                                val zx = List.map fx xs
                                                                                val wx = List.map fx c
                                                                                val zy = List.map fy ys
                                                                                val wy = List.map fy d in
                                                                                tResolve zx zy ((MINUS(NUM(1),VAR(n^m)))::wx) ((MINUS(NUM(1),VAR(n^m)))::wy) (e-1)
                                                                            end
                            |(PLUS(PLUS(k,MULT(m,VAR(n))),VAR(l)),y) =>  if not (contains (VAR(n)) y) then 
                                                                            let fun f z = replace (FRAC(MINUS(PLUS(MINUS(NUM(0),k),y),VAR(l)),m)) (VAR(n)) z 
                                                                                val zs = List.map f xs 
                                                                                val ws = List.map f c in
                                                                                tResolve zs ys (y::ws) (y::d) (e-1)
                                                                            end
                                                                        else if not (contains (VAR(l)) y) then 
                                                                            let fun f z = replace (MINUS(y,PLUS(k,MULT(m,VAR(n))))) (VAR(l)) z 
                                                                                val zs = List.map f xs 
                                                                                val ws = List.map f c in
                                                                                tResolve zs ys (y::ws) (y::d) (e-1)
                                                                            end
                                                                        else tResolve xs ys (x::c) (y::d) (e-1)
                            |(x,PLUS(PLUS(k,MULT(m,VAR(n))),VAR(l))) => if not (contains (VAR(n)) x) then 
                                                                            let fun f z = replace (FRAC(MINUS(PLUS(MINUS(NUM(0),k),x),VAR(l)),m)) (VAR(n)) z 
                                                                                val zs = List.map f ys 
                                                                                val ws = List.map f d in
                                                                                tResolve xs zs (x::c) (x::ws) (e-1)
                                                                            end
                                                                        else if not (contains (VAR(l)) x) then 
                                                                            let fun f z = replace (MINUS(x,PLUS(k,MULT(m,VAR(n))))) (VAR(l)) z 
                                                                                val zs = List.map f ys 
                                                                                val ws = List.map f d in
                                                                                tResolve xs zs (x::c) (x::ws) (e-1)
                                                                            end
                                                                        else tResolve xs ys (x::c) (y::d) (e-1)
                            |(MINUS(MINUS(k,MULT(m,VAR(n))),VAR(l)),y) =>  if not (contains (VAR(n)) y) then 
                                                                            let fun f z = replace (FRAC(MINUS(MINUS(k,y),VAR(l)),m)) (VAR(n)) z 
                                                                                val zs = List.map f xs 
                                                                                val ws = List.map f c in
                                                                                tResolve zs ys (y::ws) (y::d) (e-1)
                                                                            end
                                                                        else if not (contains (VAR(l)) y) then 
                                                                            let fun f z = replace (MINUS(MINUS(k,MULT(m,VAR(n))),y)) (VAR(l)) z 
                                                                                val zs = List.map f xs 
                                                                                val ws = List.map f c in
                                                                                tResolve zs ys (y::ws) (y::d) (e-1)
                                                                            end
                                                                        else tResolve xs ys (x::c) (y::d) (e-1)
                            |(x,MINUS(MINUS(k,MULT(m,VAR(n))),VAR(l))) => if not (contains (VAR(n)) x) then 
                                                                            let fun f z = replace (FRAC(MINUS(MINUS(k,x),VAR(l)),m)) (VAR(n)) z 
                                                                                val zs = List.map f ys 
                                                                                val ws = List.map f d in
                                                                                tResolve xs zs (x::c) (x::ws) (e-1)
                                                                            end
                                                                        else if not (contains (VAR(l)) x) then 
                                                                            let fun f z = replace (MINUS(MINUS(k,MULT(m,VAR(n))),x)) (VAR(l)) z 
                                                                                val zs = List.map f ys 
                                                                                val ws = List.map f d in
                                                                                tResolve xs zs (x::c) (x::ws) (e-1)
                                                                            end
                                                                        else tResolve xs ys (x::c) (y::d) (e-1)
                            |(PLUS(MINUS(k,MULT(m,VAR(n))),VAR(l)),y) =>  if not (contains (VAR(n)) y) then 
                                                                            let fun f z = replace (FRAC(PLUS(MINUS(k,y),VAR(l)),m)) (VAR(n)) z 
                                                                                val zs = List.map f xs 
                                                                                val ws = List.map f c in
                                                                                tResolve zs ys (y::ws) (y::d) (e-1)
                                                                            end
                                                                        else if not (contains (VAR(l)) y) then 
                                                                            let fun f z = replace (MINUS(y,MINUS(k,MULT(m,VAR(n))))) (VAR(l)) z 
                                                                                val zs = List.map f xs 
                                                                                val ws = List.map f c in
                                                                                tResolve zs ys (y::ws) (y::d) (e-1)
                                                                            end
                                                                        else tResolve xs ys (x::c) (y::d) (e-1)
                            |(x,PLUS(MINUS(k,MULT(m,VAR(n))),VAR(l))) => if not (contains (VAR(n)) x) then 
                                                                            let fun f z = replace (FRAC(PLUS(MINUS(k,x),VAR(l)),m)) (VAR(n)) z 
                                                                                val zs = List.map f ys 
                                                                                val ws = List.map f d in
                                                                                tResolve xs zs (x::c) (x::ws) (e-1)
                                                                            end
                                                                        else if not (contains (VAR(l)) x) then 
                                                                            let fun f z = replace (MINUS(x,MINUS(k,MULT(m,VAR(n)))))(VAR(l)) z 
                                                                                val zs = List.map f ys 
                                                                                val ws = List.map f d in
                                                                                tResolve xs zs (x::c) (x::ws) (e-1)
                                                                            end
                                                                        else tResolve xs ys (x::c) (y::d) (e-1)
                            |(MINUS(PLUS(k,MULT(m,VAR(n))),VAR(l)),y) =>  if not (contains (VAR(n)) y) then 
                                                                            let fun f z = replace (FRAC(PLUS(MINUS(y,k),VAR(l)),m)) (VAR(n)) z 
                                                                                val zs = List.map f xs 
                                                                                val ws = List.map f c in
                                                                                tResolve zs ys (y::ws) (y::d) (e-1)
                                                                            end
                                                                        else if not (contains (VAR(l)) y) then 
                                                                            let fun f z = replace (MINUS(PLUS(k,MULT(m,VAR(n))),y)) (VAR(l)) z 
                                                                                val zs = List.map f xs 
                                                                                val ws = List.map f c in
                                                                                tResolve zs ys (y::ws) (y::d) (e-1)
                                                                            end
                                                                        else tResolve xs ys (x::c) (y::d) (e-1)
                            |(x,MINUS(PLUS(k,MULT(m,VAR(n))),VAR(l))) => if not (contains (VAR(n)) x) then 
                                                                            let fun f z = replace (FRAC(PLUS(MINUS(x,k),VAR(l)),m)) (VAR(n)) z 
                                                                                val zs = List.map f ys 
                                                                                val ws = List.map f d in
                                                                                tResolve xs zs (x::c) (x::ws) (e-1)
                                                                            end
                                                                        else if not (contains (VAR(l)) x) then 
                                                                            let fun f z = replace (MINUS(PLUS(k,MULT(m,VAR(n))),x)) (VAR(l)) z 
                                                                                val zs = List.map f ys 
                                                                                val ws = List.map f d in
                                                                                tResolve xs zs (x::c) (x::ws) (e-1)
                                                                            end
                                                                        else tResolve xs ys (x::c) (y::d) (e-1)
                            |(PLUS(PLUS(k,VAR(n)),VAR(l)),y) =>  if not (contains (VAR(n)) y) then 
                                                                            let fun f z = replace (MINUS(PLUS(MINUS(NUM(0),k),y),VAR(l))) (VAR(n)) z 
                                                                                val zs = List.map f xs 
                                                                                val ws = List.map f c in
                                                                                tResolve zs ys (y::ws) (y::d) (e-1)
                                                                            end
                                                                        else if not (contains (VAR(l)) y) then 
                                                                            let fun f z = replace (MINUS(y,PLUS(k,VAR(n)))) (VAR(l)) z 
                                                                                val zs = List.map f xs 
                                                                                val ws = List.map f c in
                                                                                tResolve zs ys (y::ws) (y::d) (e-1)
                                                                            end
                                                                        else tResolve xs ys (x::c) (y::d) (e-1)
                            |(x,PLUS(PLUS(k,VAR(n)),VAR(l))) => if not (contains (VAR(n)) x) then 
                                                                            let fun f z = replace (MINUS(PLUS(MINUS(NUM(0),k),x),VAR(l))) (VAR(n)) z 
                                                                                val zs = List.map f ys 
                                                                                val ws = List.map f d in
                                                                                tResolve xs zs (x::c) (x::ws) (e-1)
                                                                            end
                                                                        else if not (contains (VAR(l)) x) then 
                                                                            let fun f z = replace (MINUS(x,PLUS(k,VAR(n)))) (VAR(l)) z 
                                                                                val zs = List.map f ys 
                                                                                val ws = List.map f d in
                                                                                tResolve xs zs (x::c) (x::ws) (e-1)
                                                                            end
                                                                        else tResolve xs ys (x::c) (y::d) (e-1)
                            |(MINUS(MINUS(k,VAR(n)),VAR(l)),y) =>  if not (contains (VAR(n)) y) then 
                                                                            let fun f z = replace (MINUS(MINUS(k,y),VAR(l))) (VAR(n)) z 
                                                                                val zs = List.map f xs 
                                                                                val ws = List.map f c in
                                                                                tResolve zs ys (y::ws) (y::d) (e-1)
                                                                            end
                                                                        else if not (contains (VAR(l)) y) then 
                                                                            let fun f z = replace (MINUS(MINUS(k,VAR(n)),y)) (VAR(l)) z 
                                                                                val zs = List.map f xs 
                                                                                val ws = List.map f c in
                                                                                tResolve zs ys (y::ws) (y::d) (e-1)
                                                                            end
                                                                        else tResolve xs ys (x::c) (y::d) (e-1)
                            |(x,MINUS(MINUS(k,VAR(n)),VAR(l))) => if not (contains (VAR(n)) x) then 
                                                                            let fun f z = replace (MINUS(MINUS(k,x),VAR(l))) (VAR(n)) z 
                                                                                val zs = List.map f ys 
                                                                                val ws = List.map f d in
                                                                                tResolve xs zs (x::c) (x::ws) (e-1)
                                                                            end
                                                                        else if not (contains (VAR(l)) x) then 
                                                                            let fun f z = replace (MINUS(MINUS(k,VAR(n)),x)) (VAR(l)) z 
                                                                                val zs = List.map f ys 
                                                                                val ws = List.map f d in
                                                                                tResolve xs zs (x::c) (x::ws) (e-1)
                                                                            end
                                                                        else tResolve xs ys (x::c) (y::d) (e-1)
                            |(PLUS(MINUS(k,VAR(n)),VAR(l)),y) =>  if not (contains (VAR(n)) y) then 
                                                                            let fun f z = replace (PLUS(MINUS(k,y),VAR(l))) (VAR(n)) z 
                                                                                val zs = List.map f xs 
                                                                                val ws = List.map f c in
                                                                                tResolve zs ys (y::ws) (y::d) (e-1)
                                                                            end
                                                                        else if not (contains (VAR(l)) y) then 
                                                                            let fun f z = replace (MINUS(y,MINUS(k,VAR(n)))) (VAR(l)) z 
                                                                                val zs = List.map f xs 
                                                                                val ws = List.map f c in
                                                                                tResolve zs ys (y::ws) (y::d) (e-1)
                                                                            end
                                                                        else tResolve xs ys (x::c) (y::d) (e-1)
                            |(x,PLUS(MINUS(k,VAR(n)),VAR(l))) => if not (contains (VAR(n)) x) then 
                                                                            let fun f z = replace (PLUS(MINUS(k,x),VAR(l))) (VAR(n)) z 
                                                                                val zs = List.map f ys 
                                                                                val ws = List.map f d in
                                                                                tResolve xs zs (x::c) (x::ws) (e-1)
                                                                            end
                                                                        else if not (contains (VAR(l)) x) then 
                                                                            let fun f z = replace (MINUS(x,MINUS(k,VAR(n))))(VAR(l)) z 
                                                                                val zs = List.map f ys 
                                                                                val ws = List.map f d in
                                                                                tResolve xs zs (x::c) (x::ws) (e-1)
                                                                            end
                                                                        else tResolve xs ys (x::c) (y::d) (e-1)
                            |(MINUS(PLUS(k,VAR(n)),VAR(l)),y) =>  if not (contains (VAR(n)) y) then 
                                                                            let fun f z = replace (PLUS(MINUS(y,k),VAR(l))) (VAR(n)) z 
                                                                                val zs = List.map f xs 
                                                                                val ws = List.map f c in
                                                                                tResolve zs ys (y::ws) (y::d) (e-1)
                                                                            end
                                                                        else if not (contains (VAR(l)) y) then 
                                                                            let fun f z = replace (MINUS(PLUS(k,VAR(n)),y)) (VAR(l)) z 
                                                                                val zs = List.map f xs 
                                                                                val ws = List.map f c in
                                                                                tResolve zs ys (y::ws) (y::d) (e-1)
                                                                            end
                                                                        else tResolve xs ys (x::c) (y::d) (e-1)
                            |(x,MINUS(PLUS(k,VAR(n)),VAR(l))) => if not (contains (VAR(n)) x) then 
                                                                            let fun f z = replace (PLUS(MINUS(x,k),VAR(l))) (VAR(n)) z 
                                                                                val zs = List.map f ys 
                                                                                val ws = List.map f d in
                                                                                tResolve xs zs (x::c) (x::ws) (e-1)
                                                                            end
                                                                        else if not (contains (VAR(l)) x) then 
                                                                            let fun f z = replace (MINUS(PLUS(k,VAR(n)),x)) (VAR(l)) z 
                                                                                val zs = List.map f ys 
                                                                                val ws = List.map f d in
                                                                                tResolve xs zs (x::c) (x::ws) (e-1)
                                                                            end
                                                                        else tResolve xs ys (x::c) (y::d) (e-1)
                            |(MINUS(VAR(n),m),MINUS(k,VAR(l))) =>  if contains (VAR(l)) m orelse contains (VAR(n)) k then tResolve xs ys (x::c) (y::d) (e-1)
                                                                   else let fun f z = replace (PLUS(m,y)) (VAR(n)) z 
                                                                            fun fy z = replace (MINUS(k,x)) (VAR(l)) z 
                                                                            val zs = List.map f xs 
                                                                            val zy = List.map fy ys 
                                                                            val ws = List.map f c
                                                                            val wy = List.map fy d in
                                                                            tResolve zs zy (y::ws) (x::wy) (e-1)
                                                                        end
                            |(MINUS(k,VAR(l)),MINUS(VAR(n),m)) =>  if contains (VAR(l)) m orelse contains (VAR(n)) k then tResolve xs ys (x::c) (y::d) (e-1)  
                                                                   else let fun f z = replace (MINUS(k,y)) (VAR(l)) z 
                                                                            fun fy z = replace (PLUS(m,x)) (VAR(n)) z 
                                                                            val zs = List.map f xs 
                                                                            val zy = List.map fy ys 
                                                                            val ws = List.map f c
                                                                            val wy = List.map fy d in
                                                                            tResolve zs zy (y::ws) (x::wy) (e-1)
                                                                        end
                            |(MINUS(VAR(n),m),MULT(l,VAR(k))) => if n = k then 
                                                                    let fun f z = replace (FRAC(m,MINUS(NUM(1),l))) (VAR(n)) z 
                                                                        val zs = List.map f xs 
                                                                        val zy = List.map f ys 
                                                                        val ws = List.map f (x::c)
                                                                        val wy = List.map f (y::d) in
                                                                        tResolve zs zy ws wy (e-1)
                                                                    end
                                                                else let fun f z = replace (PLUS(y,m)) (VAR(n)) z 
                                                                         val zs = List.map f xs 
                                                                         val ws = List.map f c in
                                                                            tResolve zs ys (y::ws) (y::d) (e-1)
                                                                     end
                            |(MULT(l,VAR(k)),MINUS(VAR(n),m)) => if n = k then 
                                                                    let fun f z = replace (FRAC(m,MINUS(NUM(1),l))) (VAR(n)) z 
                                                                        val zs = List.map f xs 
                                                                        val zy = List.map f ys 
                                                                        val ws = List.map f (x::c)
                                                                        val wy = List.map f (y::d) in
                                                                        tResolve zs zy ws wy (e-1)
                                                                    end
                                                                else let fun f z = replace (PLUS(x,m)) (VAR(n)) z 
                                                                         val zs = List.map f ys 
                                                                         val ws = List.map f d in
                                                                            tResolve xs zs (x::c) (x::ws) (e-1)
                                                                     end
                            |(MINUS(VAR(n),m),k) => if contains (VAR(n)) k then tResolve xs ys (x::c) (y::d) (e-1)
                                                    else let fun f z = replace (PLUS(k,m)) (VAR(n)) z 
                                                             val zs = List.map f xs 
                                                             val ws = List.map f c in
                                                                tResolve zs ys (y::ws) (y::d) (e-1)
                                                         end
                            |(k,MINUS(VAR(n),m)) => if contains (VAR(n)) k then tResolve xs ys (x::c) (y::d) (e-1) 
                                                   else let fun f z = replace (PLUS(k,m)) (VAR(n)) z 
                                                            val zs = List.map f ys 
                                                            val ws = List.map f d in
                                                                tResolve xs zs (x::c) (x::ws) (e-1)
                                                        end
                            |(k,MINUS(m,VAR(n))) => let fun f z = replace (MINUS(m,k)) (VAR(n)) z 
                                                        val zs = List.map f ys 
                                                        val ws = List.map f d in
                                                            tResolve xs zs (x::c) (x::ws) (e-1)
                                                    end
                            |(MINUS(m,VAR(n)),k) => let fun f z = replace (MINUS(m,k)) (VAR(n)) z 
                                                        val zs = List.map f xs 
                                                        val ws = List.map f c in
                                                            tResolve zs ys (y::ws) (y::d) (e-1)
                                                    end
                            |(k,PLUS(m,VAR(n))) =>  let fun f z = replace (MINUS(k,m)) (VAR(n)) z 
                                                        val zs = List.map f ys 
                                                        val ws = List.map f d in
                                                            tResolve xs zs (x::c) (x::ws) (e-1)
                                                    end
                            |(PLUS(m,VAR(n)),k) =>  let fun f z = replace (MINUS(k,m)) (VAR(n)) z 
                                                        val zs = List.map f xs 
                                                        val ws = List.map f c in
                                                            tResolve zs ys (y::ws) (y::d) (e-1)
                                                    end
                            |(VAR(n),y) =>  let fun f z = replace y x z 
                                                val zs = List.map f xs 
                                                val ws = List.map f c in
                                                tResolve zs ys (y::ws) (y::d) (e-1)
                                            end
                            |(x,VAR(n)) => let fun f z = replace x y z 
                                                val zs = List.map f ys 
                                                val ws = List.map f d in
                                                tResolve xs zs (x::c) (x::ws) (e-1)
                                            end
                            |(MULT(q,VAR(l)),PLUS(m,MULT(n,VAR(k)))) => if l = k then
                                                                        let fun f z = replace (FRAC(m,MINUS(q,n))) (VAR(l)) z 
                                                                            val zx = List.map f xs 
                                                                            val zs = List.map f ys 
                                                                            val wx = List.map f (x::c) 
                                                                            val ws = List.map f (y::d) in
                                                                            tResolve zx zs wx ws (e-1)
                                                                        end
                                                                        else tResolve xs ys (x::c) (y::d) (e-1)
                            |(PLUS(m,MULT(n,VAR(k))),MULT(q,VAR(l))) => if l = k then
                                                                        let fun f z = replace (FRAC(m,MINUS(q,n))) (VAR(l)) z 
                                                                            val zx = List.map f xs 
                                                                            val zs = List.map f ys 
                                                                            val wx = List.map f (x::c) 
                                                                            val ws = List.map f (y::d) in
                                                                            tResolve zx zs wx ws (e-1)
                                                                        end
                                                                        else tResolve xs ys (x::c) (y::d) (e-1)
                            |(l,MINUS(MINUS(m,VAR(n)),k)) => let fun f z = replace (MINUS(MINUS(m,k),l)) (VAR(n)) z 
                                                                 val zs = List.map f ys 
                                                                 val ws = List.map f d in
                                                                 tResolve xs zs (x::c) (x::ws) (e-1)
                                                             end
                            |(MINUS(MINUS(m,VAR(n)),k),l) => let fun f z = replace (MINUS(MINUS(m,k),l)) (VAR(n)) z 
                                                                 val zs = List.map f xs 
                                                                 val ws = List.map f c in
                                                                tResolve zs ys (y::ws) (y::d) (e-1)
                                                             end
                            |(k,PLUS(m,MULT(l,VAR(n)))) =>  let fun f z = replace (FRAC(MINUS(k,m),l)) (VAR(n)) z 
                                                                val zs = List.map f ys 
                                                                val ws = List.map f d in
                                                                tResolve xs zs (x::c) (x::ws) (e-1)
                                                            end
                            |(PLUS(m,MULT(l,VAR(n))),k) =>  let fun f z = replace (FRAC(MINUS(k,m),l)) (VAR(n)) z 
                                                                val zs = List.map f xs 
                                                                val ws = List.map f c in
                                                                tResolve zs ys (y::ws) (y::d) (e-1)
                                                            end
                            |(MINUS(MULT(l,VAR(n)),m),k) => let fun f z = replace (FRAC(PLUS(k,m),l)) (VAR(n)) z 
                                                                val zs = List.map f xs 
                                                                val ws = List.map f c in
                                                                    tResolve zs ys (y::ws) (y::d) (e-1)
                                                            end
                            |(k,MINUS(MULT(l,VAR(n)),m)) => let fun f z = replace (FRAC(PLUS(k,m),l)) (VAR(n)) z 
                                                                val zs = List.map f ys 
                                                                val ws = List.map f d in
                                                                    tResolve xs zs (x::c) (x::ws) (e-1)
                                                            end
                            |(k,MINUS(m,MULT(l,VAR(n)))) => let fun f z = replace (FRAC(MINUS(m,k),l)) (VAR(n)) z 
                                                                val zs = List.map f ys 
                                                                val ws = List.map f d in
                                                                    tResolve xs zs (x::c) (x::ws) (e-1)
                                                            end
                            |(MINUS(m,MULT(l,VAR(n))),k) => let fun f z = replace (FRAC(MINUS(m,k),l)) (VAR(n)) z 
                                                                val zs = List.map f xs 
                                                                val ws = List.map f c in
                                                                    tResolve zs ys (y::ws) (y::d) (e-1)
                                                            end
                            |(MULT(n,VAR(m)),MULT(k,VAR(l))) => let fun fx z = replace (MULT(FRAC(k,n),VAR(l))) (VAR(m)) z
                                                                    val zx = List.map fx xs
                                                                    val wx = List.map fx c in
                                                                    tResolve zx ys (y::wx) (y::d) (e-1)
                                                                end
                            |(FRAC(n,m),FRAC(k,l)) => if l = m then 
                                                        case (solveVar n k) of
                                                        NONE => tResolve xs ys (x::c) (y::d) (e-1)
                                                        |SOME(a,b) => let fun f z = replace b a z
                                                                          val zx = List.map f xs
                                                                          val wx = List.map f (x::c)
                                                                          val zy = List.map f ys
                                                                          val wy = List.map f (y::d) in 
                                                                          tResolve zx zy wx wy (e-1)
                                                                      end
                                                      else tResolve xs ys (x::c) (y::d) (e-1)
                            |(MINUS(q,FRAC(n,m)),FRAC(k,l)) => if l = m then 
                                                               case (solveVar k (MINUS(MULT(q,m),n))) of
                                                               NONE => tResolve xs ys (x::c) (y::d) (e-1)
                                                               |SOME(a,b) => let fun f z = replace b a z
                                                                                 val zx = List.map f xs
                                                                                 val wx = List.map f (x::c)
                                                                                 val zy = List.map f ys
                                                                                 val wy = List.map f (y::d) in 
                                                                                 tResolve zx zy wx wy (e-1)
                                                                             end
                                                                else tResolve xs ys (x::c) (y::d) (e-1)
                            |(FRAC(k,l),MINUS(q,FRAC(n,m))) => if l = m then 
                                                               case (solveVar k (MINUS(MULT(q,m),n))) of
                                                               NONE => tResolve xs ys (x::c) (y::d) (e-1)
                                                               |SOME(a,b) => let fun f z = replace b a z
                                                                                 val zx = List.map f xs
                                                                                 val wx = List.map f (x::c)
                                                                                 val zy = List.map f ys
                                                                                 val wy = List.map f (y::d) in 
                                                                                 tResolve zx zy wx wy (e-1)
                                                                             end
                                                                else tResolve xs ys (x::c) (y::d) (e-1)
                            |(PLUS(q,FRAC(n,m)),FRAC(k,l)) => if l = m then 
                                                               case (solveVar k (PLUS(n,MULT(q,m)))) of
                                                               NONE => tResolve xs ys (x::c) (y::d) (e-1)
                                                               |SOME(a,b) => let fun f z = replace b a z
                                                                                 val zx = List.map f xs
                                                                                 val wx = List.map f (x::c)
                                                                                 val zy = List.map f ys
                                                                                 val wy = List.map f (y::d) in 
                                                                                 tResolve zx zy wx wy (e-1)
                                                                             end
                                                                else tResolve xs ys (x::c) (y::d) (e-1)
                            |(FRAC(k,l),PLUS(q,FRAC(n,m))) => if l = m then 
                                                               case (solveVar k (PLUS(n,MULT(q,m)))) of
                                                               NONE => tResolve xs ys (x::c) (y::d) (e-1)
                                                               |SOME(a,b) => let fun f z = replace b a z
                                                                                 val zx = List.map f xs
                                                                                 val wx = List.map f (x::c)
                                                                                 val zy = List.map f ys
                                                                                 val wy = List.map f (y::d) in 
                                                                                 tResolve zx zy wx wy (e-1)
                                                                             end
                                                                else tResolve xs ys (x::c) (y::d) (e-1)
                            |_ => case (solveVar x y) of
                                   NONE => tResolve xs ys (x::c) (y::d) (e-1)
                                  |SOME(a,b) => let fun f z = replace b a z
                                                    val zx = List.map f xs
                                                    val wx = List.map f (x::c)
                                                    val zy = List.map f ys
                                                    val wy = List.map f (y::d) in 
                                                    tResolve zx zy wx wy (e-1)
                                                end)
            end
        |_ => raise NumError)
    val (x,y) = tResolve a b [] [] n
    in        
        filterNum x y (countU a) (countU b)
    end

fun stringToHTML xs =
    case xs of
    [] => []
    |(a,b)::xs => if b = "empty" then (a,  ("<div>\n"^
                                            "<svg width=\"200\" height=\"200\">\n"^
                                            "<rect width=\"200\" height=\"200\" style=\"fill:white;stroke-width:1;stroke:black\"/>\n"^
                                            "</svg>\n"^
                                            "</div>",
                                            200.0,200.0))::stringToHTML xs
                  else if String.substring(b,0,1) = "!" then 
                    (a,("<div>\n"^
                        "<svg width=\"60\" height=\"18\" font-size=\"12px\">\n"^
                        "<rect width=\"60\" height=\"18\" fill=\"#d9d9d9\"/>\n"^
                        "<text text-anchor=\"middle\" transform=\"translate(30,14)\"><tspan text-decoration=\"overline\">"^(String.substring(b,1,(String.size b)-1))^"</tspan></text>"^
                        "</svg>\n"^
                        "</div>",
                        60.0,18.0))::stringToHTML xs
                  else  (a,("<div>\n"^
                            "<svg width=\"60\" height=\"18\" font-size=\"12px\">\n"^
                            "<rect width=\"60\" height=\"18\" fill=\"#d9d9d9\"/>\n"^
                            "<text text-anchor=\"middle\" transform=\"translate(30,14)\">"^b^"</text>\n"^
                            "</svg>\n"^
                            "</div>",
                            60.0,18.0))::stringToHTML xs

fun drawArea x =
    let fun parseArea (Construction.Source(x)) =
                if String.substring(#2 x, 0, 5) = "empty" then (EMPTY, [(#1 x, "empty")])
                else if Char.isAlpha(String.sub(#2 x, 0)) then (LABEL(String.substring(#2 x, 0, 1)), [(#1 x, String.substring(#2 x, 0, 1))])
                else raise AreaError
            |parseArea (Construction.TCPair(x,y)) =
                if (#1 (#constructor x)) = "notLabel" then 
                    (case (parseArea (hd(y))) of
                        (LABEL(a),b) => (NLABEL(a),[((#1 (hd(b))), "!"^(#2 (hd(b))))])
                        |_ => raise AreaError)
                else if (#1 (#constructor x)) = "cPoint" then 
                    let val (x1,z1) = parseNum (hd(y))
                        val (x2,z2) = parseNum (List.last(y)) in
                        (POINT(x1,x2),z1@z2)
                    end
                else if (#1 (#constructor x)) = "cRect" then 
                    let val (x1,y1) = parseArea (hd(y))
                        val (x2,y2) = parseArea (List.last(y)) in
                        (RECT(x1,x2),y1@y2)
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
                else raise AreaError
            |parseArea (Construction.Reference(x)) = raise AreaError 
        fun convertArea EMPTY = (([],[],[],[]),[])
            |convertArea (LABEL(x)) = (([SEVENT(x)],[],[],[]),[])
            |convertArea (NLABEL(x)) = (([NEVENT(x)],[],[],[]),[])
            |convertArea (POINT(x,y)) = (([],[x,y],[],[]),[])
            |convertArea (RECT(x,y)) = 
                let val ((_,y2,_,_),_) = convertArea x
                    val ((_,y3,_,_),_) = convertArea y in 
                    (([],y2@y3,[],[]),[])
                end
            |convertArea (OVERLAY(m,x,y,z,w)) = 
                let fun flipShading x =
                        case x of 
                        BLUE => RED
                        |RED => BLUE
                        |_ => x
                    val ((x1,y1,z1,w1),n) = convertArea x
                    val ((_,y2,_,_),_) = convertArea y
                    val ((x3,_,_,_),_) = convertArea z in
                    if w1 = [] then 
                        case (hd(x3)) of
                        SEVENT(a) => ((x3,y2,[w],[List.nth(y2,2),MINUS(NUM(1), List.nth(y2,2))]),(m,x3,y2,[w],[List.nth(y2,2),MINUS(NUM(1), List.nth(y2,2))])::n)
                        |NEVENT(a) => ((x3,[MINUS(NUM(1), List.nth(y2,2)), NUM(0), NUM(1), NUM(1)],[(flipShading w)],[MINUS(NUM(1), List.nth(y2,2)),List.nth(y2,2)]),(m,x3,[MINUS(NUM(1), List.nth(y2,2)), NUM(0), NUM(1), NUM(1)],[(flipShading w)],[MINUS(NUM(1), List.nth(y2,2)),List.nth(y2,2)])::n)
                    else case (hd(x3)) of
                        SEVENT(a) => ((x1@x3,y1@[List.nth(y1,0), List.nth(y2,1), List.nth(y1,2), List.nth(y2,3)],z1@[w],w1@[List.nth(y2,3), MINUS(NUM(1),List.nth(y2,3))]),(m,x1@x3,y1@[List.nth(y1,0), List.nth(y2,1), List.nth(y1,2), List.nth(y2,3)],z1@[w],w1@[List.nth(y2,3), MINUS(NUM(1),List.nth(y2,3))])::n)
                        |NEVENT(a) => ((x1@x3,y1@[List.nth(y1,0), MINUS(NUM(1), List.nth(y2,3)), List.nth(y1,2), NUM(1)],z1@[(flipShading w)],w1@[MINUS(NUM(1),List.nth(y2,3)), List.nth(y2,3)]),(m,x1@x3,y1@[List.nth(y1,0), MINUS(NUM(1), List.nth(y2,3)), List.nth(y1,2), NUM(1)],z1@[(flipShading w)],w1@[MINUS(NUM(1),List.nth(y2,3)), List.nth(y2,3)])::n)
                end
            |convertArea (COMBAREA(m,x,y)) =
                let fun toRects ws = [NUM(0),NUM(0),(hd(ws)),NUM(1),NUM(0),NUM(0),(hd(ws)),(List.nth(ws,2)),(hd(ws)),NUM(0),NUM(1),(List.nth(ws,4))]
                    fun mergeShading x y = 
                        if x = PATTERN then y
                        else if y = PATTERN then x
                        else if x = WHITE then y
                        else x
                    fun extractNum x y w =
                        if List.length x = 1 then w@[U, U, U, U]
                        else if List.length w = 6 then w
                        else case (hd(x)) of
                            SEVENT(a) => w@[U,U]
                            |NEVENT(a) => List.take(w,2)@[U,U]@List.drop(w,2)
                    fun areaMerge x2 y2 a x3 y3 b =
                        let fun createNums xs = [NUM(0),NUM(0),List.nth(xs,0),NUM(1),NUM(0),NUM(0),List.nth(xs,0),List.nth(xs,2),List.nth(xs,0),NUM(0),NUM(1),List.nth(xs,4)]
                            fun ff b =
                                if List.nth(b,2) = U then 
                                let val xs = [VAR("z"),MINUS(NUM(1),VAR("z")),
                                            MINUS(NUM(1),FRAC(MULT(List.nth(b,4), List.nth(b,1)), VAR("z"))), FRAC(MULT(List.nth(b,4), List.nth(b,1)), VAR("z")), 
                                            MINUS(NUM(1),FRAC(MULT(List.nth(b,5),List.nth(b,1)), MINUS(NUM(1), VAR("z")))), FRAC(MULT(List.nth(b,5),List.nth(b,1)), MINUS(NUM(1), VAR("z")))]
                                    val xss = List.map simplify xs in 
                                    (xss, (createNums xss))
                                end
                                else if List.nth(b,4) = U then 
                                let val xs = [VAR("z"), MINUS(NUM(1),VAR("z")),
                                            FRAC(MULT(List.nth(b,2),List.nth(b,0)),VAR("z")), MINUS(NUM(1),FRAC(MULT(List.nth(b,2),List.nth(b,0)),VAR("z"))),
                                            FRAC(MULT(List.nth(b,3),List.nth(b,0)),MINUS(NUM(1),VAR("z"))), MINUS(NUM(1),FRAC(MULT(List.nth(b,3),List.nth(b,0)),MINUS(NUM(1),VAR("z"))))]
                                    val xss = List.map simplify xs in 
                                    (xss, (createNums xss))
                                end
                                else let val xs = [PLUS(MULT(List.nth(b,2),List.nth(b,0)),MULT(List.nth(b,4),List.nth(b,1))), PLUS(MULT(List.nth(b,3),List.nth(b,0)),MULT(List.nth(b,5),List.nth(b,1))), 
                                                FRAC(MULT(List.nth(b,2), List.nth(b,0)),PLUS(MULT(List.nth(b,2),List.nth(b,0)),MULT(List.nth(b,4),List.nth(b,1)))), FRAC(MULT(List.nth(b,4), List.nth(b,1)),PLUS(MULT(List.nth(b,2),List.nth(b,0)),MULT(List.nth(b,4),List.nth(b,1)))), 
                                                FRAC(MULT(List.nth(b,3),List.nth(b,0)),PLUS(MULT(List.nth(b,3),List.nth(b,0)),MULT(List.nth(b,5),List.nth(b,1)))),  FRAC(MULT(List.nth(b,5),List.nth(b,1)),PLUS(MULT(List.nth(b,3),List.nth(b,0)),MULT(List.nth(b,5),List.nth(b,1))))] 
                                        val xss = List.map simplify xs in 
                                    (xss, (createNums xss))
                                end 
                            in
                            if eventToString (hd(x2)) = eventToString (hd(x3)) then 
                                let fun merger a b y2 y3 c d e f =
                                        case (a,b) of
                                        ([],[]) => ((List.rev c), (List.rev d), e, f)
                                        |(x::xxs::xs,y::yys::ys) => if x = U andalso y = U then merger xs ys y2 y3 c d e f
                                                                else if x = U then merger xs ys y2 (List.drop(y3,4)) (xxs::x::c) (yys::y::d) (e@[U,U,U,U]) (f@(List.take(y3,4)))
                                                                else if y = U then merger xs ys (List.drop(y2,4)) y3 (xxs::x::c) (yys::y::d) (e@(List.take(y2,4))) (f@[U,U,U,U])
                                                                else merger xs ys (List.drop(y2,4)) (List.drop(y3,4)) (xxs::x::c) (yys::y::d) (e@(List.take(y2,4))) (f@(List.take(y3,4)))
                                        |_ => raise AreaError
                                    val (c,d,e,f) = merger a b y2 y3 [] [] [] [] in
                                    if List.length x2 > List.length x3 then (x2, c, d, e, f)
                                    else (x3, c, d, e, f)
                                end
                            else if List.length x2 = List.length x3 andalso List.length x2 = 1 then 
                                let val xss = [VAR("z"),MINUS(NUM(1),VAR("z")), VAR("x"), MINUS(NUM(1),VAR("x")), FRAC(MINUS(hd(b),MULT(VAR("z"),VAR("x"))),MINUS(NUM(1),VAR("z"))), MINUS(NUM(1),FRAC(MINUS(hd(b),MULT(VAR("z"),VAR("x"))),MINUS(NUM(1),VAR("z"))))] in 
                                    (x2@x3, a, xss, y2@[U,U,U,U,U,U,U,U], (createNums xss))
                                end 
                            else if List.length x2 = List.length x3 andalso List.length y2 = 8 then 
                                let val (xss,yss) = ff b in (x2, a, xss, (y2@[U,U,U,U]), yss) end
                            else if List.length x2 = List.length x3 then
                                let val (xss,yss) = ff b in (x2, a, xss, y2, yss) end
                            else if List.length x3 > List.length x2 then
                                let val (xss,yss) = ff b in ((List.rev x3), a, xss, (y2@[U,U,U,U,U,U,U,U]), yss) end
                            else let val (xss,yss) = ff a in ((List.rev x2), xss, b, yss, (y3@[U,U,U,U,U,U,U,U])) end
                        end
                    val ((x2,y2,z2,w2),n1) = convertArea x
                    val ((x3,y3,z3,w3),n2) = convertArea y 
                    val (x, c, d, e, f) = areaMerge x2 y2 (extractNum x2 y2 w2) x3 y3 (extractNum x3 y3 w3)
                    val g = resolve (c@e) (d@f) (List.length c) in
                    if List.length g = 12 then ((x, (List.drop(g,4)), [(mergeShading (hd(z2)) (hd(z3))),PATTERN], List.take(g,4)),(m, x, (List.drop(g,4)), [(mergeShading (hd(z2)) (hd(z3))),PATTERN], List.take(g,4))::n1@n2)
                    else ((x, (toRects (List.take(g,6))), [WHITE,BLUE,RED], List.take(g,6)),(m, x, (toRects (List.take(g,6))), [WHITE,BLUE,RED], List.take(g,6))::n1@n2)
                end
        fun areaToHTML (m,a,b,c,d) =
            let fun toNum x =
                    if onlyNum x then numToString (PLUS(NUM(30),MULT(NUM(200),x)))
                    else numToString (NUM(80))
                fun calcLen x y k n = 
                    if onlyNum x andalso onlyNum y then numToString (MULT(NUM(200),MINUS(x,y)))
                    else if numToString k = numToString (NUM(0)) then numToString (NUM(50))
                    else numToString (MULT(n,NUM(50)))
                fun calcMid x n =
                    if onlyNum x then numToString (PLUS(n,MULT(NUM(100),x)))
                    else numToString (PLUS(NUM(25),n))
                fun calcLab n =
                    if numToString n = numToString (NUM(0)) then numToString (NUM(15))
                    else numToString (NUM(245))
                fun shadeToString x =
                    case x of
                    BLUE => "#99b3ff"
                    |RED => "#f08080"
                    |GREEN => "#8cd98c"
                    |WHITE => "white"
                    |PATTERN => "url(#diagonalHatch)"
                fun toDocArea (x,y,z,w) =
                    if List.length x = 1 then   "<rect width=\"200\" height=\"200\" transform=\"translate(30,30)\" style=\"fill:white;stroke-width:1;stroke:black\" />\n"^
                                                "<rect width=\""^(calcLen (List.nth(y,2)) (List.nth(y,0)) (List.nth(y,0)) (NUM(3)))^"\" height=\""^(calcLen (List.nth(y,3)) (List.nth(y,1)) (List.nth(y,3)) (NUM(1)))^"\" transform=\"translate("^(toNum (List.nth(y,0)))^","^(toNum (List.nth(y,1)))^")\" style=\"fill:"^(List.nth(z,0))^";stroke-width:1;stroke:black\" />\n"^m^
                                                "<text text-anchor=\"middle\" transform=\"translate("^(calcMid (List.nth(w,0)) (NUM(30)))^",10)\">"^(List.nth(x,0))^"</text>\n"^
                                                "<text text-anchor=\"middle\" transform=\"translate("^(calcMid (List.nth(w,0)) (NUM(30)))^",25)\">"^(numToString (List.nth(w,0)))^"</text>\n"
                    else if List.length w = 4 then
                        "<rect width=\"200\" height=\"200\" transform=\"translate(30,30)\" style=\"fill:white;stroke-width:1;stroke:black\" />\n"^
                        "<rect width=\""^(calcLen (List.nth(y,2)) (List.nth(y,0)) (List.nth(y,0)) (NUM(3)))^"\" height=\""^(calcLen (List.nth(y,3)) (List.nth(y,1)) (List.nth(y,3)) (NUM(3)))^"\" transform=\"translate("^(toNum (List.nth(y,0)))^","^(toNum (List.nth(y,1)))^")\" style=\"fill:"^(List.nth(z,0))^";stroke-width:1;stroke:black\" />\n"^
                        "<rect width=\""^(calcLen (List.nth(y,6)) (List.nth(y,4)) (List.nth(y,4)) (NUM(3)))^"\" height=\""^(calcLen (List.nth(y,7)) (List.nth(y,5)) (List.nth(y,7)) (NUM(3)))^"\" transform=\"translate("^(toNum (List.nth(y,4)))^","^(toNum (List.nth(y,5)))^")\" style=\"fill:"^(List.nth(z,1))^";stroke-width:1;stroke:black\"/>\n"^m^
                        "<text text-anchor=\"middle\" transform=\"translate("^(calcMid (List.nth(w,0)) (NUM(30)))^",10)\">"^(List.nth(x,0))^"</text>\n"^
                        "<text text-anchor=\"middle\" transform=\"translate("^(calcMid (List.nth(w,0)) (NUM(30)))^",25)\">"^(numToString (List.nth(w,0)))^"</text>\n"^
                        "<text text-anchor=\"middle\" transform=\"translate("^(calcLab (List.nth(y,4)))^","^(calcMid (List.nth(w,2)) (NUM(22)))^")\">"^(List.nth(x,1))^"</text>\n"^
                        "<text text-anchor=\"middle\" transform=\"translate("^(calcLab (List.nth(y,4)))^","^(calcMid (List.nth(w,2)) (NUM(38)))^")\">"^(numToString (List.nth(w,2)))^"</text>\n"   
                    else    "<rect width=\"200\" height=\"200\" transform=\"translate(30,30)\" style=\"fill:white;stroke-width:1;stroke:black\" />\n"^
                            "<rect width=\""^(calcLen (List.nth(y,2)) (List.nth(y,0)) (List.nth(y,0)) (NUM(1)))^"\" height=\""^(calcLen (List.nth(y,3)) (List.nth(y,1)) (List.nth(y,3)) (NUM(1)))^"\" transform=\"translate("^(toNum (List.nth(y,0)))^","^(toNum (List.nth(y,1)))^")\" style=\"fill:"^(List.nth(z,0))^";stroke-width:1;stroke:black\" />\n"^
                            "<rect width=\""^(calcLen (List.nth(y,6)) (List.nth(y,4)) (List.nth(y,4)) (NUM(1)))^"\" height=\""^(calcLen (List.nth(y,7)) (List.nth(y,5)) (List.nth(y,7)) (NUM(1)))^"\" transform=\"translate("^(toNum (List.nth(y,4)))^","^(toNum (List.nth(y,5)))^")\" style=\"fill:"^(List.nth(z,1))^";stroke-width:1;stroke:black\"/>\n"^
                            "<rect width=\""^(calcLen (List.nth(y,10)) (List.nth(y,8)) (List.nth(y,8)) (NUM(3)))^"\" height=\""^(calcLen (List.nth(y,11)) (List.nth(y,9)) (List.nth(y,11))  (NUM(2)))^"\" transform=\"translate("^(toNum (List.nth(y,8)))^","^(toNum (List.nth(y,9)))^")\" style=\"fill:"^(List.nth(z,2))^";stroke-width:1;stroke:black\" />\n"^m^
                            "<text text-anchor=\"middle\" transform=\"translate("^(calcMid (List.nth(w,0)) (NUM(30)))^",10)\">"^(List.nth(x,0))^"</text>\n"^
                            "<text text-anchor=\"middle\" transform=\"translate("^(calcMid (List.nth(w,0)) (NUM(30)))^",25)\">"^(numToString (List.nth(w,0)))^"</text>\n"^
                            "<text text-anchor=\"middle\" transform=\"translate(15,"^(calcMid (List.nth(w,2)) (NUM(22)))^")\">"^(List.nth(x,1))^"</text>\n"^
                            "<text text-anchor=\"middle\" transform=\"translate(15,"^(calcMid (List.nth(w,2)) (NUM(38)))^")\">"^(numToString (List.nth(w,2)))^"</text>\n"^
                            "<text text-anchor=\"middle\" transform=\"translate(245,"^(calcMid (List.nth(w,4)) (NUM(22)))^")\">"^(List.nth(x,1))^"</text>\n"^
                            "<text text-anchor=\"middle\" transform=\"translate(245,"^(calcMid (List.nth(w,4)) (NUM(38)))^")\">"^(numToString (List.nth(w,4)))^"</text>\n"
                val header = "<div>\n"^
                            "<svg width=\"300\" height=\"240\" background-color=\"white\" font-size=\"12px\">\n"^
                            "<pattern id=\"diagonalHatch\" patternUnits=\"userSpaceOnUse\" width=\"4\" height=\"4\">\n"^
                            "<path d=\"M-1,1 l2,-2 M0,4 l4,-4 M3,5 l2,-2\" style=\"stroke:#222; stroke-width:1\"/>\n"^
                            "</pattern>\n"
                val footer = "</svg>\n"^
                            "</div>\n"
                val content = toDocArea ((List.map eventToString a), b, (List.map shadeToString c), d)
                in (m,((header^content^footer),300.0,240.0))
            end
        val (a,b) = parseArea x
        val (_,n) = convertArea a
        val ns = List.map areaToHTML n in
        ns@(stringToHTML b)
    end

fun drawTable x =
    let fun parseTable (Construction.Source(x)) =
                if Char.isAlpha(String.sub(#2 x, 0)) then (NAME(String.substring(#2 x, 0, 1)), [(#1 x, String.substring(#2 x, 0, 1))])
                else raise TableError
            |parseTable (Construction.TCPair(x,y)) =
                if (#1 (#constructor x)) = "constructOne" then 
                    let val (x1,y1) = parseTable (hd(y))
                        val (x2,y2) = parseNum (List.last(y)) in 
                        (ONEWAY((#1 (#token x)), x1, x2), y1@y2)
                    end
                else if (#1 (#constructor x)) = "constructTwo" then 
                    let val (x1,y1) = parseTable (hd(y))
                        val (x2,y2) = parseTable (List.nth(y, 1))
                        val (x3,y3) = parseNum (List.last(y)) in 
                        (TWOWAY((#1 (#token x)), x1, x2, x3), y1@y2@y3)
                    end
                else if (#1 (#constructor x)) = "combine" then 
                    let val (x1,y1) = parseTable (hd(y))
                        val (x2,y2) = parseTable (List.last(y)) in 
                        (COMB((#1 (#token x)), x1, x2), y1@y2)
                    end
                else if (#1 (#constructor x)) = "notName" then 
                    (case (parseTable (hd(y))) of 
                        (NAME(a),b) => (NNAME(a),[(#1 (hd(b)), "!"^(#2 (hd(b))))]) 
                        |_ => raise TableError)
                else raise TableError
            |parseTable _ = raise TableError
        fun convertTable (NAME(x)) = (([SEVENT(x)], []),[])
            |convertTable (NNAME(x)) = (([NEVENT(x)], []),[])
            |convertTable (ONEWAY(m,x,y)) = 
                let val ((x2,_),_) = convertTable x in
                    case (hd(x2)) of 
                    SEVENT(a) => ((x2, [y, MINUS(NUM(1),y)]),[(m, x2, [y, MINUS(NUM(1),y)])])
                    |NEVENT(a) => ((x2, [MINUS(NUM(1),y), y]),[(m, x2, [MINUS(NUM(1),y), y])])
                end
            |convertTable (TWOWAY(m,x,y,z)) = 
                let val ((x2,y2),n1) = convertTable x
                    val ((x3,y3),n2) = convertTable y in
                        case ((hd(x2)),(hd(x3))) of 
                        (SEVENT(a),SEVENT(b)) => ((x2@x3, y2@y3@[z, MINUS((hd(y2)),z), MINUS((hd(y3)),z), MINUS(PLUS(NUM(1),MINUS(z,(hd(y3)))),(hd(y2)))]),(m, x2@x3, y2@y3@[z, MINUS((hd(y2)),z), MINUS((hd(y3)),z), MINUS(PLUS(NUM(1),MINUS(z,(hd(y3)))),(hd(y2)))])::n1@n2)
                        |(SEVENT(a),NEVENT(b)) => ((x2@x3, y2@y3@[MINUS(List.nth(y2,0), z), z, MINUS(PLUS(NUM(1), MINUS(z,(List.nth(y3,1)))),(List.nth(y2,0))), MINUS((List.nth(y3,1)),z)]), (m, x2@x3, y2@y3@[MINUS(List.nth(y2,0), z), z, MINUS(PLUS(NUM(1), MINUS(z,(List.nth(y3,1)))),(List.nth(y2,0))), MINUS((List.nth(y3,1)),z)])::n1@n2)
                        |(NEVENT(a),SEVENT(b)) => ((x2@x3, y2@y3@[MINUS((List.nth(y3,0)),z), MINUS(PLUS(NUM(1),MINUS(z,(List.nth(y3,0)))),(List.nth(y2,1))), z, MINUS((List.nth(y2,1)),z)]), (m, x2@x3, y2@y3@[MINUS((List.nth(y3,0)),z), MINUS(PLUS(NUM(1),MINUS(z,(List.nth(y3,0)))),(List.nth(y2,1))), z, MINUS((List.nth(y2,1)),z)])::n1@n2)
                        |(NEVENT(a),NEVENT(b)) => ((x2@x3, y2@y3@[MINUS(PLUS(NUM(1),MINUS(z,(List.nth(y3,1)))),(List.nth(y2,1))), MINUS((List.nth(y3,1)),z), MINUS((List.nth(y2,1)),z), z]), (m, x2@x3, y2@y3@[MINUS(PLUS(NUM(1),MINUS(z,(List.nth(y3,1)))),(List.nth(y2,1))), MINUS((List.nth(y3,1)),z), MINUS((List.nth(y2,1)),z), z])::n1@n2)
                end
            |convertTable (COMB(m,x,y)) =
                let fun tableMerge x2 y2 x3 y3 =
                        let fun rotate y2 = [List.nth(y2,2),List.nth(y2,3),List.nth(y2,0),List.nth(y2,1),List.nth(y2,4),List.nth(y2,6),List.nth(y2,5),List.nth(y2,7)] in 
                            if List.length x2 = List.length x3 andalso eventToString (hd(x2)) = eventToString (hd(x3)) then (x2, y2, y3)
                            else if List.length x2 = List.length x3 andalso List.length x2 = 1 then ((x2@x3),(y2@[U,U,U,U,U,U]),([U,U]@y3@[U,U,U,U]))
                            else if List.length x2 = List.length x3 then (x2, y2, rotate y3)
                            else if List.length x2 > List.length x3 andalso eventToString (hd(x2)) = eventToString (hd(x3)) then (x2, y2, (y3@[U,U,U,U,U,U]))
                            else if List.length x2 > List.length x3 then (x2, y2, ([U,U]@y3@[U,U,U,U]))
                            else if eventToString (hd(x2)) = eventToString (hd(x3)) then (x3, (y2@[U,U,U,U,U,U]), y3)
                            else (x3, ([U,U]@y2@[U,U,U,U]), y3)
                        end
                    val ((x2,y2),n1) = convertTable y
                    val ((x3,y3),n2) = convertTable x 
                    val (a,b,c) = tableMerge x2 y2 x3 y3 in
                    if List.length a = 1 then ((a, resolve b c (List.length b)),(m, a, resolve b c (List.length b))::n1@n2)
                    else ((a, resolve b c (List.length b)),(m, a, resolve b c (List.length b))::n1@n2)
                end
        fun tableToHTML (m,a,b) =
            let fun toDocTable (x,y) =
                    if List.length x = 1 then  ("<th style=\"background-color:lightgrey; border:1px solid; height:25px; width:70px;\"></th>\n"^
                                                "<th style=\"background-color:lightgrey; border:1px solid; width:70px;\">Total</th>\n"^
                                                "</tr>\n"^
                                                "<tr>\n"^
                                                "<th style=\"background-color:lightgrey; border:1px solid; height:25px;\">"^(List.nth(x,0))^"</th>\n"^
                                                "<td style=\"border: 1px solid;\">"^(List.nth(y,0))^"</td>\n"^
                                                "</tr>\n"^
                                                "<tr>\n"^
                                                "<th style=\"background-color:lightgrey; border:1px solid; height:25px;\"><span style=\"text-decoration:overline\">"^(List.nth(x,0))^"</span></th>\n"^
                                                "<td style=\"border: 1px solid\">"^(List.nth(y,1))^"</td>\n"^
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
                            "<td style=\"border: 1px solid;\">"^(List.nth(y,4))^"</td>\n"^
                            "<td style=\"border: 1px solid;\">"^(List.nth(y,5))^"</td>\n"^
                            "<td style=\"border: 1px solid;\">"^(List.nth(y,0))^"</td>\n"^
                            "</tr>\n"^
                            "<tr>\n"^
                            "<th style=\"background-color:lightgrey; border:1px solid; height:25px;\"><span style=\"text-decoration:overline\">"^(List.nth(x,0))^"</span></th>\n"^
                            "<td style=\"border: 1px solid;\">"^(List.nth(y,6))^"</td>\n"^
                            "<td style=\"border: 1px solid;\">"^(List.nth(y,7))^"</td>\n"^
                            "<td style=\"border: 1px solid;\">"^(List.nth(y,1))^"</td>\n"^
                            "</tr>\n"^
                            "<tr>\n"^
                            "<th style=\"background-color:lightgrey; border:1px solid; height:25px;\">Total</th>\n"^
                            "<td style=\"border: 1px solid;\">"^(List.nth(y,2))^"</td>\n"^
                            "<td style=\"border: 1px solid;\">"^(List.nth(y,3))^"</td>\n"^
                            "<td style=\"border: 1px solid;\">1</td>\n",
                            280.0)
                val header =    "<div>\n"^
                                "<table style=\"text-align:center; border-collapse:collapse; background-color:white; font-size:12px;\">\n"^
                                "<tr>\n"
                val footer =    "</tr>\n"^
                                "</table>\n"^
                                "</div>\n"
                val (content,w) = toDocTable ((List.map eventToString a),(List.map numToString b))
                in
                (m, ((header^content^footer),w,100.0))
            end
        val (a,b) = parseTable x
        val (_,n) = convertTable a
        val ns = List.map tableToHTML n
        in
        ns@(stringToHTML b)
    end

fun drawTree x =
    let fun parseTree (Construction.Source(x)) = (BRANCH(String.substring(#2 x, 0, 1)), [(#1 x, String.substring(#2 x, 0, 1))])
            |parseTree (Construction.TCPair(x,y)) =
                if (#1 (#constructor x)) = "construct" then 
                    let val (x1,y1) = parseTree (hd(y))
                        val (x2,y2) = parseNum (List.last(y)) in
                        (TREE((#1 (#token x)),x1,x2), y1@y2)
                    end
                else if (#1 (#constructor x)) = "addBranch" then 
                    let val (x1,y1) = parseTree (hd(y))
                        val (x2,y2) = parseTree (List.nth(y, 1)) 
                        val (x3,y3) = parseNum (List.last(y)) in
                        (ADD((#1 (#token x)), x1, x2, x3), y1@y2@y3)
                    end
                else if (#1 (#constructor x)) = "resolve" then 
                    let val (x1,y1) = parseTree (hd(y))
                        val (x2,y2) = parseTree (List.last(y)) in
                        (RESOLVE((#1 (#token x)),x1,x2), y1@y2)
                    end   
                else if (#1 (#constructor x)) = "notLabel" then 
                    (case (parseTree (hd(y))) of
                        (BRANCH(a),b) => (NBRANCH(a),[((#1 (hd(b))), "!"^(#2 (hd(b))))])
                        |_ => raise TreeError)
                else raise TreeError
            |parseTree (Construction.Reference(x)) = raise TreeError
        fun convertTree (BRANCH(x)) = (([SEVENT(x)],[]), [])
            |convertTree (NBRANCH(x)) = (([NEVENT(x)],[]), [])
            |convertTree (TREE(m,x,y)) =
                let val ((x2,_),_) = convertTree x in
                    case (hd(x2)) of
                    NEVENT(a) => ((x2, [MINUS(NUM(1), y), y]),[(m, x2, [MINUS(NUM(1), y), y])])
                    |SEVENT(a) => ((x2, [y, MINUS(NUM(1), y)]),[(m, x2, [y, MINUS(NUM(1), y)])])
                end
            |convertTree (ADD(m,x,y,z)) =
                let val ((x2,y2),n) = convertTree x
                    val ((x3,_),_) = convertTree y in
                    case ((hd(x2)), (hd(x3))) of
                        (SEVENT(a),SEVENT(b)) => ((x2@x3, y2@[z, MINUS(NUM(1),z), U, U]),(m,x2@x3, y2@[z, MINUS(NUM(1),z), U, U])::n)
                        |(SEVENT(a),NEVENT(b)) => ((x2@x3, y2@[MINUS(NUM(1),z), z, U, U]),(m,x2@x3, y2@[MINUS(NUM(1),z), z, U, U])::n)
                        |(NEVENT(a),SEVENT(b)) => ((x2@x3, y2@[U, U, z, MINUS(NUM(1),z)]),(m,x2@x3, y2@[U, U, z, MINUS(NUM(1),z)])::n)
                        |(NEVENT(a),NEVENT(b)) => ((x2@x3, y2@[U, U, MINUS(NUM(1),z), z]),(m,x2@x3, y2@[U, U, MINUS(NUM(1),z), z])::n)
                end 
            |convertTree ((RESOLVE(m,x,y))) =
                let fun treeMerge x2 y2 x3 y3 =
                        let fun f b = 
                                if List.nth(b,2) = U then List.map simplify [VAR("z"),MINUS(NUM(1),VAR("z")),
                                                                            MINUS(NUM(1),FRAC(MULT(List.nth(b,4), List.nth(b,1)), VAR("z"))), FRAC(MULT(List.nth(b,4), List.nth(b,1)), VAR("z")), 
                                                                            MINUS(NUM(1),FRAC(MULT(List.nth(b,5),List.nth(b,1)), MINUS(NUM(1), VAR("z")))), FRAC(MULT(List.nth(b,5),List.nth(b,1)), MINUS(NUM(1), VAR("z")))]
                                else if List.nth(b,4) = U then List.map simplify [VAR("z"), MINUS(NUM(1),VAR("z")),
                                                                                FRAC(MULT(List.nth(b,2),List.nth(b,0)),VAR("z")), MINUS(NUM(1),FRAC(MULT(List.nth(b,2),List.nth(b,0)),VAR("z"))),
                                                                                FRAC(MULT(List.nth(b,3),List.nth(b,0)),MINUS(NUM(1),VAR("z"))), MINUS(NUM(1),FRAC(MULT(List.nth(b,3),List.nth(b,0)),MINUS(NUM(1),VAR("z"))))]
                                else List.map simplify 
                                    [PLUS(MULT(List.nth(b,2),List.nth(b,0)),MULT(List.nth(b,4),List.nth(b,1))), PLUS(MULT(List.nth(b,3),List.nth(b,0)),MULT(List.nth(b,5),List.nth(b,1))), 
                                    FRAC(MULT(List.nth(b,2), List.nth(b,0)),PLUS(MULT(List.nth(b,2),List.nth(b,0)),MULT(List.nth(b,4),List.nth(b,1)))), FRAC(MULT(List.nth(b,4), List.nth(b,1)),PLUS(MULT(List.nth(b,2),List.nth(b,0)),MULT(List.nth(b,4),List.nth(b,1)))), 
                                    FRAC(MULT(List.nth(b,3),List.nth(b,0)),PLUS(MULT(List.nth(b,3),List.nth(b,0)),MULT(List.nth(b,5),List.nth(b,1)))),  FRAC(MULT(List.nth(b,5),List.nth(b,1)),PLUS(MULT(List.nth(b,3),List.nth(b,0)),MULT(List.nth(b,5),List.nth(b,1))))] 
                            fun countNum xs = 
                                case xs of
                                [] => 0
                                |(x::xs) => if (onlyNum x) then (countNum xs) + 1 else countNum xs
                        in
                            if List.length x2 = List.length x3 andalso eventToString (hd(x2)) = eventToString (hd(x3)) then (x2, y2, y3)
                            else if List.length x2 = 1 andalso List.length x2 = List.length x3 then ((x2@x3), (y2@[U,U,U,U]),  [VAR("z"), MINUS(NUM(1),VAR("z")), VAR("y"), MINUS(NUM(1),VAR("y")), FRAC(MINUS((hd(y3)),MULT(VAR("z"),VAR("y"))),MINUS(NUM(1),VAR("z"))), MINUS(NUM(1),FRAC(MINUS((hd(y3)),MULT(VAR("z"),VAR("y"))),MINUS(NUM(1),VAR("z"))))])
                            else if List.length x2 = List.length x3 then 
                                if (countNum y2) > (countNum y3) then (x2, y2, (f y3)) else (x3, (f y2), y3) 
                            else if List.length x2 > List.length x3 andalso eventToString (hd(x2)) = eventToString (hd(x3)) then (x2, y2, (y3@[U,U,U,U])) 
                            else if List.length x2 > List.length x3 then (List.rev x2, f y2, y3@[U,U,U,U])
                            else if eventToString (hd(x2)) = eventToString (hd(x3)) then (x3, (y2@[U,U,U,U]), y3)
                            else (List.rev x3, y2@[U,U,U,U], f y3)
                        end
                    val ((x2,y2),n1) = convertTree y
                    val ((x3,y3),n2) = convertTree x 
                    val (a,b,c) = treeMerge x2 y2 x3 y3 
                    in 
                    if List.length a = 1 then ((a, resolve b c (List.length b)),(m, a, resolve b c (List.length b))::n1@n2)
                    else ((a, resolve b c (List.length b)),(m, a, resolve b c (List.length b))::n1@n2)
                end
        fun treeToHTML (m,a,b) =
            let fun addJoint y =
                    if List.length y = 2 then []
                    else if List.nth(y,2) = U andalso List.nth(y,4) = U then [U,U,U,U]
                    else if List.nth(y,2) = U then [U,U,MULT(List.nth(y,4),List.nth(y,1)),MULT(List.nth(y,5),List.nth(y,1))]
                    else if List.nth(y,4) = U then [MULT(List.nth(y,2),List.nth(y,0)),MULT(List.nth(y,3),List.nth(y,0)),U,U]
                    else [MULT(List.nth(y,2),List.nth(y,0)),MULT(List.nth(y,3),List.nth(y,0)),MULT(List.nth(y,4),List.nth(y,1)),MULT(List.nth(y,5),List.nth(y,1))]
                fun toDocTree (x,y) =
                    if List.length x = 1 then  ("<svg height=\"90\" width=\"120\" style=\"background-color:white\" font-size=\"12px\">\n"^
                                                "<text transform=\"translate(85,27)\">P("^(List.nth(x,0))^")</text>\n"^
                                                "<text transform=\"translate(85,83)\">P(<tspan text-decoration=\"overline\">"^(List.nth(x,0))^"</tspan>)</text>\n"^
                                                "<text text-anchor=\"middle\" transform=\"translate(40,35) rotate(-17)\">"^(List.nth(y,0))^"</text>\n"^
                                                "<text text-anchor=\"middle\" transform=\"translate(40,74) rotate(17)\">"^(List.nth(y,1))^"</text>\n"^
                                                "<line x1=\"0\" y1=\"50\" x2=\"80\" y2=\"25\" style=\"stroke:black;stroke-width:1\"/>\n"^
                                                "<line x1=\"0\" y1=\"50\" x2=\"80\" y2=\"75\" style=\"stroke:black;stroke-width:1\"/>\n",
                                                90.0, 120.0)
                    else   ("<svg height=\"110\" width=\"350\" style=\"background-color:white\" font-size=\"12px\">\n"^
                            "<text transform=\"translate(85,27)\">P("^(List.nth(x,0))^")</text>\n"^
                            "<text transform=\"translate(85,83)\">P(<tspan text-decoration=\"overline\">"^(List.nth(x,0))^"</tspan>)</text>\n"^
                            "<text transform=\"translate(225,10)\">P("^(List.nth(x,0))^"&cap;"^(List.nth(x,1))^") "^(List.nth(y,6))^"</text>\n"^
                            "<text transform=\"translate(225,38)\">P("^(List.nth(x,0))^"&cap;<tspan text-decoration=\"overline\">"^(List.nth(x,1))^"</tspan>) "^(List.nth(y,7))^"</text>\n"^
                            "<text transform=\"translate(225,70)\">P(<tspan text-decoration=\"overline\">"^(List.nth(x,0))^"</tspan>&cap;"^(List.nth(x,1))^") "^(List.nth(y,8))^"</text>\n"^
                            "<text transform=\"translate(225,98)\">P(<tspan text-decoration=\"overline\">"^(List.nth(x,0))^"</tspan>&cap;<tspan text-decoration=\"overline\">"^(List.nth(x,1))^"</tspan>) "^(List.nth(y,9))^"</text>\n"^
                            "<text text-anchor=\"middle\" transform=\"translate(40,35) rotate(-17)\">"^(List.nth(y,0))^"</text>\n"^
                            "<text text-anchor=\"middle\" transform=\"translate(40,74) rotate(17)\">"^(List.nth(y,1))^"</text>\n"^
                            "<text text-anchor=\"middle\" transform=\"translate(170,11) rotate(-7)\">"^(List.nth(y,2))^"</text>\n"^
                            "<text text-anchor=\"middle\" transform=\"translate(170,37) rotate(7)\">"^(List.nth(y,3))^"</text>\n"^
                            "<text text-anchor=\"middle\" transform=\"translate(170,71) rotate(-7)\">"^(List.nth(y,4))^"</text>\n"^
                            "<text text-anchor=\"middle\" transform=\"translate(170,97) rotate(7)\">"^(List.nth(y,5))^"</text>\n"^
                            "<line x1=\"0\" y1=\"50\" x2=\"80\" y2=\"25\" style=\"stroke:black;stroke-width:1\"/>\n"^
                            "<line x1=\"0\" y1=\"50\" x2=\"80\" y2=\"75\" style=\"stroke:black;stroke-width:1\"/>\n"^
                            "<line x1=\"120\" y1=\"20\" x2=\"220\" y2=\"7\" style=\"stroke:black;stroke-width:1\"/>\n"^
                            "<line x1=\"120\" y1=\"20\" x2=\"220\" y2=\"33\" style=\"stroke:black;stroke-width:1\"/>\n"^
                            "<line x1=\"120\" y1=\"80\" x2=\"220\" y2=\"67\" style=\"stroke:black;stroke-width:1\"/>\n"^
                            "<line x1=\"120\" y1=\"80\" x2=\"220\" y2=\"93\" style=\"stroke:black;stroke-width:1\"/>\n",
                             110.0, 350.0)
                val b = b@(addJoint b)
                val header = "<div>\n"
                val footer = "</svg>\n"^
                             "</div>"
                val (content, h, w) = toDocTree ((List.map eventToString a),(List.map numToString b))
                in
                (m, ((header^content^footer),w,h))
            end
        val (a,b) = parseTree x
        val (_,n) = convertTree a
        val ns = List.map treeToHTML n
        in
        ns@(stringToHTML b)
    end

end;

