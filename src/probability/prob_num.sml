

import "core.construction";
import "latex.latex";

signature PROBNUM = sig
    datatype numExp = U
                 |NUM of int
                 |DEC of string
                 |VAR of string
                 |PLUS of numExp * numExp
                 |MINUS of numExp * numExp
                 |MULT of numExp * numExp
                 |FRAC of numExp * numExp;
    val parseNum: Construction.construction -> numExp * ((string*string*real) list);
    val onlyNum: numExp -> bool;
    val numToString: numExp -> string;
    val simplify: numExp -> numExp;
    val resolve: numExp list -> numExp list -> int -> numExp list
end;

structure ProbNum : PROBNUM = struct 
datatype numExp = U
                 |NUM of int
                 |DEC of string
                 |VAR of string
                 |PLUS of numExp * numExp
                 |MINUS of numExp * numExp
                 |MULT of numExp * numExp
                 |FRAC of numExp * numExp
exception NumError;

datatype num =  R of real
               |V of string

fun parseNum (Construction.Source(x)) =
        (case String.breakOn ":" (#2 x) of
            (a,":",_) => if Char.isAlpha(String.sub(a,0)) then (VAR(a),[(#1 x,a,Real.fromInt(String.size a)+0.5)])
                         else if String.isSubstring "0." a then (DEC(a), [(#1 x,a,Real.fromInt(String.size a)-0.5)])
                         else (case Int.fromString a of 
                                SOME b => (NUM(b), [(#1 x,a,Real.fromInt(String.size a)+0.5)])
                                |NONE => raise NumError)
            |_ => raise NumError)
    |parseNum (Construction.TCPair(x,y)) =
        if (#1 (#constructor x)) = "infixOp" then
            let val (a,y1) = parseNum (List.nth (y,0)) 
                val (b,y2) = parseNum (List.nth (y,2)) in
                case (List.nth (y,1)) of
                    Construction.Source(z) => (case (#2 z) of
                                                "plus" => (PLUS(a,b),(#1 (#token x),(#2 (hd(y1)))^" + "^(#2 (hd(y2))),(#3 (hd(y1)))+(#3 (hd(y2)))+0.5)::y1@[(#1 z,"+",1.5)]@y2)
                                                |"minus" => (MINUS(a,b),(#1 (#token x),(#2 (hd(y1)))^" - "^(#2 (hd(y2))),(#3 (hd(y1)))+(#3 (hd(y2)))+0.5)::y1@[((#1 z,"-",1.5))]@y2)
                                                |_ => raise NumError)
                    |_ => raise NumError
            end
        else if (#1 (#constructor x)) = "frac" then 
            let val (a,y1) = parseNum (List.nth (y,0)) 
                val (b,y2) = parseNum (List.last(y)) in
                case (List.nth (y,1)) of
                    Construction.Source(z) => (FRAC(a,b),(#1 (#token x),(#2 (hd(y1)))^"/"^(#2 (hd(y2))),(#3 (hd(y1)))+(#3 (hd(y2))))::y1@[(#1 z,"/",1.5)]@y2)
                    |_ => raise NumError
            end
        else if (#1 (#constructor x)) = "implicitMult" then 
            let val (a,y1) = parseNum (List.nth (y,0)) 
                val (b,y2) = parseNum (List.last(y)) in
                (MULT(a,b),(#1 (#token x),(#2 (hd(y1)))^"*"^(#2 (hd(y2))),(#3 (hd(y1)))+(#3 (hd(y2))))::y1@y2)
            end
        else raise NumError
    |parseNum (Construction.Reference(x)) = 
        (case String.breakOn ":" (#2 x) of
            (a,":",_) => if Char.isAlpha(String.sub(a,0)) then (VAR(a),[(#1 x,a,Real.fromInt(String.size a)+0.5)])
                         else if String.isSubstring "0." a then (DEC(a), [(#1 x,a,Real.fromInt(String.size a)-0.5)])
                         else (case Int.fromString a of 
                                SOME b => (NUM(b), [(#1 x,a,Real.fromInt(String.size a)+0.5)])
                                |NONE => raise NumError)
            |_ => raise NumError)

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
                (case (Real.fromString x) of
                NONE => raise NumError
                |SOME z => R z)
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

end;