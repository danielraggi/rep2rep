import "core.construction";

signature PROBRENDER = sig
    type renderer = Construction.construction list
                    -> ((string * (string * real * real)) list, Diagnostic.t list) Result.t;

    val drawArea: renderer;
    val drawTable: renderer;
    val drawTree: renderer;
    val drawBayes: renderer;
end;

structure ProbRender : PROBRENDER = struct

type renderer = Construction.construction list
                -> ((string * (string * real * real)) list, Diagnostic.t list) Result.t;

datatype numExp =
           U
         | NUM of int
         | DEC of string  (* String, to be converted to real later; makes numExp eqtype *)
         | VAR of string
         | PLUS of numExp * numExp
         | MINUS of numExp * numExp
         | MULT of numExp * numExp
         | FRAC of numExp * numExp;
datatype num = R of real | V of string;
exception NumError;

datatype shading = BLUE | WHITE | RED | GREEN | PATTERN;
exception ShadeError;

datatype eventExp = SEVENT of string | NEVENT of string;

datatype areaExp =
           EMPTY
         | LABEL of string
         | NLABEL of string
         | POINT of numExp * numExp
         | RECT of areaExp * areaExp
         | OVERLAY of string * areaExp * areaExp * areaExp * shading
         | COMBAREA of string * areaExp * areaExp;
exception AreaError;

datatype tableExp =
           NAME of string
         | NNAME of string
         | ONEWAY of string * tableExp * numExp
         | TWOWAY of string * tableExp * tableExp * numExp
         | COMB of string * tableExp * tableExp;
exception TableError;

datatype treeExp =
           BRANCH of string
         | NBRANCH of string
         | TREE of string * treeExp * numExp
         | ADD of string * treeExp * treeExp * numExp
         | RESOLVE of string * treeExp * treeExp;
exception TreeError;

exception BayesError;

val inter = "<tspan style=\"font-size:1.4em;\">&cap;</tspan>";
val union = "<tspan style=\"font-size:1.4em;\">&cup;</tspan>";

fun eventToString (SEVENT(x)) = x
    |eventToString (NEVENT(x)) = x

fun parseShading (Construction.Source((id, typ))) =
    let val (subType, _, _) = String.breakOn ":" typ;
    in case subType of
           "red" => (RED, [(id, "RED", 3.0)])
         | "blue" => (BLUE, [(id, "BLUE", 4.0)])
         | "white" => (WHITE, [(id, "WHITE", 5.0)])
         | "green" => (GREEN, [(id, "GREEN", 5.0)])
         | "pattern" => (PATTERN, [(id, "PATTERN", 6.0)])
         | _ => (WHITE, [(id, "WHITE", 5.0)])
    end
  | parseShading _ = raise ShadeError;

local
    fun parseSource (id, typ) =
        let val (subType, _, _) = String.breakOn ":" typ;
            val subTypeLen = Real.fromInt (String.size subType);
        in if Char.isAlpha (String.sub(subType, 0))
           then (VAR(subType), [(id, subType, subTypeLen + 0.5)])
           else
               if String.isPrefix "0." subType
               then (DEC(subType), [(id, subType, subTypeLen - 0.5)])
               else case Int.fromString subType of
                        SOME x => (NUM(x), [(id, subType, subTypeLen + 0.5)])
                      | NONE => raise NumError
        end;
        fun parseWithValAndLength parse c =
            case parse c of
                (_, []) => raise NumError
              | (a, y as (_, value, length)::_) => (a, y, value, length);
in
fun parseNum (Construction.Source(tok)) = parseSource tok
  | parseNum (Construction.Reference(tok)) = parseSource tok (* WARNING - ASSUMES REF IS SOURCE *)
  | parseNum (Construction.TCPair({token=tok, constructor=con}, inputs)) =
    let val (id, typ) = tok;
        val (cname, ctyp) = con;
        val parseWithValAndLength = parseWithValAndLength parseNum;
    in case (cname, inputs) of
           ("infixOp", [a, Construction.Source((id', op_)), b]) =>
           let val (a', y1, leftVal, leftLen) = parseWithValAndLength a;
               val (b', y2, rightVal, rightLen) = parseWithValAndLength b;
           in case op_ of
                  "plus" =>
                  let val sum = (id, String.concat [leftVal, " + ", rightVal], leftLen + rightLen + 0.5);
                      val plus = (id', "+", 1.5);
                  in (PLUS(a', b'), sum::y1@(plus::y2)) end
                | "minus" =>
                  let val diff = (id, String.concat [leftVal, " - ", rightVal], leftLen + rightLen + 0.5);
                      val minus = (id', "-", 1.5);
                  in (MINUS(a', b'), diff::y1@(minus::y2)) end
                | "div" =>
                  let val (a', y1, leftVal, leftLen) = parseWithValAndLength a;
                      val (b', y2, rightVal, rightLen) = parseWithValAndLength b;
                      val frac = (id, String.concat [leftVal, "/", rightVal], leftLen + rightLen);
                      val divd = (id', "/", 1.5);
                  in (FRAC(a', b'), frac::y1@(divd::y2)) end
                | _ => raise NumError
           end
         | ("multiply", [a, b]) =>
           let val (a', y1, leftVal, leftLen) = parseWithValAndLength a;
               val (b', y2, rightVal, rightLen) = parseWithValAndLength b;
               val prod = (id, String.concat [leftVal, "*", rightVal], leftLen + rightLen);
           in (MULT(a', b'), prod::y1@y2) end
         | (_, _) => raise NumError
    end
end;

fun onlyNum U = false
  | onlyNum (NUM(x)) = true
  | onlyNum (DEC(x)) = true
  | onlyNum (VAR(x)) = false
  | onlyNum (PLUS(x,y)) = (onlyNum x) andalso (onlyNum y)
  | onlyNum (MINUS(x,y)) = (onlyNum x) andalso (onlyNum y)
  | onlyNum (MULT(x,y)) = (onlyNum x) andalso (onlyNum y)
  | onlyNum (FRAC(x,y)) = (onlyNum x) andalso (onlyNum y)

fun allNum [] = true
  | allNum (x::xs) = onlyNum x andalso allNum xs

fun numToString x =
    let fun round n = Real.roundDecimal n 4;
        fun convertNum (PLUS(x,y)) =
            (case (convertNum x, convertNum y) of
                 (R a, R b) => R (a + b)
               | (R a, V b) => if Real.== (a, 0.0) then V b
                               else
                                   if String.sub(b, 0) = #"~"
                                   then V ((Real.toString (round a)) ^ "-" ^ (String.extract (b, 1, NONE)))
                                   else V ((Real.toString (round a)) ^ "+" ^ b)
               | (V a, R b) => if Real.== (b, 0.0) then V a
                               else
                                   if b < 0.0
                                   then V (a ^ "-" ^ Real.toString (round (~b)))
                                   else V (a ^ "+" ^ Real.toString (round b))
               | (V a, V b) => if String.sub (b, 0) = #"~"
                               then V (a ^ "-" ^ (String.extract (b, 1, NONE)))
                               else V (a ^ "+" ^ b))
          | convertNum (MINUS(x,y)) =
            (case (convertNum x, convertNum y) of
                 (R a, R b) => R (a - b)
               | (R a, V b) => if Real.== (a,0.0) andalso String.sub(b,0) = #"~"
                               then V (String.extract (b, 1, NONE))
                               else
                                   if Real.== (a, 0.0) then V ("~" ^ b)
                                   else
                                       if String.sub(b,0) = #"~"
                                       then V ((Real.toString (round a)) ^ "+" ^ (String.extract (b, 1, NONE)))
                                       else V ((Real.toString (round a)) ^ "-" ^ b)
               | (V a, R b) => if b < 0.0 then V (a ^ "+" ^ (Real.toString (round (~b))))
                               else
                                   if Real.== (b, 0.0) then (V a)
                                   else V (a ^ "-" ^ (Real.toString (round b)))
               | (V a, V b) => if String.sub(b,0) = #"~"
                               then V (a ^ "+" ^ (String.extract (b, 1, NONE)))
                               else V (a ^ "-" ^ b))
          | convertNum (MULT(x,y)) =
             (case (convertNum x, convertNum y) of
                  (R a, R b) => R (a * b)
                | (R a, V b) => if Real.== (a, 1.0) then V b
                                else if Real.== (a, ~1.0) then V ("~" ^ b)
                                else V ((Real.toString (round a)) ^ "*" ^ b)
                |(V a, R b) => V (a ^ "*" ^ (Real.toString (round b)))
                |(V a, V b) => V (a ^ "*" ^ b))
          | convertNum (FRAC(x,y)) =
            (case (convertNum x, convertNum y) of
                 (R a, R b) => R (a / b)
               | (R a, V b) => V ((Real.toString (round a)) ^ "/" ^ b)
               | (V a, R b) => if Real.== (b,1.0) then V a else V (a ^ "/" ^ (Real.toString (round b)))
               | (V a, V b) => V (a ^ "/" ^ b))
          | convertNum (VAR(x)) = V x
          | convertNum (U) = V " "
          | convertNum (DEC(x)) = (case (Real.fromString x) of
                                       NONE => raise NumError
                                     | SOME z => R z)
          | convertNum (NUM(x)) = R (Real.fromInt x)
        val str = case convertNum (simplify x) of
                      V x => x
                    | R x => Real.toString (round x);
        in if String.size str > 40 then " " else str end
and simplify (PLUS(x,y)) =
    (* NOTE FROM AARON: This looks like it could be simplified by
       changing the internal representation. If we had a NEG variant
       rather than a MINUS variant, the PLUS stuff would be reused
       and we could add in a few simplifiers such as NEG(NEG(x)) => x,
       then change the stringifier to look for PLUS(a,NEG(b)).
       This would probably also require that we convert to a normal
       form, which is probably a good thing! I also suggest collapsing
       NUM and DEC into a single NUM variant (containing a numerical string?).
     *)
    let val a = simplify x;
        val b = simplify y;
    in case (a,b) of
           (NUM(0), b) => b (* 0 + b = b *)
         | (a, NUM(0)) => a (* a + 0 = a *)
         | (VAR(k), MULT(c, VAR(l))) (* k + ck = (c+1)k *)
           => if k = l then simplify (MULT(PLUS(NUM(1), c), VAR(k)))
              else PLUS(a,b)
         | (MULT(n, VAR(m)), VAR(l)) (* nm + m = (n+1)m *)
           => if m = l then simplify (MULT(PLUS(NUM(1), n), VAR(m)))
              else PLUS(a,b)
         | (MULT(n,VAR(m)),MULT(k,VAR(l))) (* nm + km = (n+k)m *)
           => if m = l then simplify (MULT(PLUS(n,k),VAR(m)))
              else PLUS(a,b)
         | (MULT(m, VAR(k)), PLUS(n, VAR(l))) (* mk + n + k = n + (m+1)k *)
           => if k = l then simplify (PLUS(n, MULT(PLUS(NUM(1), m), VAR(k))))
              else PLUS(a,b)
         | (MULT(m, VAR(k)), PLUS(n, MULT(c, VAR(l)))) (* mk + n + ck = n + (m+c)k *)
           => if k = l then simplify (PLUS(n, MULT(PLUS(m, c),VAR(k))))
              else PLUS(a,b)
         | (MULT(m, VAR(k)), MINUS(n, VAR(l))) (* mk + (n-k) = n + (m-1)*k *)
           => if k = l then simplify (PLUS(n, MULT(MINUS(m, NUM(1)), VAR(k))))
              else PLUS(a,b)
         | (MULT(m, VAR(k)), MINUS(VAR(l), n)) (* mk + (k-n) = (0-n) + (m+1)k *)
           => if k = l then simplify (PLUS(MINUS(NUM(0), n), MULT(PLUS(NUM(1), m), VAR(k))))
              else PLUS(a,b)
         | (MULT(m, VAR(k)), MINUS(n, MULT(c, VAR(l)))) (* mk + (n-ck) = n + (m-c)k *)
           => if k = l then simplify (PLUS(n, MULT(MINUS(m, c), VAR(k))))
              else PLUS(a,b)
         | (MULT(m, VAR(k)), MINUS(MULT(c, VAR(l)), n)) (* mk + (ck - n) = (0-n) + (c+m)k *)
           => if k = l then simplify (PLUS(MINUS(NUM(0), n), MULT(PLUS(c, m), VAR(k))))
              else PLUS(a,b)
         | (PLUS(m, VAR(k)), VAR(l)) (* (m+k) + k = m + 2k *)
           => if k = l then simplify (PLUS(m, MULT(NUM(2), VAR(k))))
              else PLUS(a,b)
         | (PLUS(m, VAR(k)), MULT(n, VAR(l))) (* (m+k) + nk = m + (1+n)k *)
           => if k = l then simplify (PLUS(m, MULT(PLUS(NUM(1), n), VAR(k))))
              else PLUS(a,b)
         | (PLUS(m, VAR(k)), PLUS(n, VAR(l))) (* (m+k) + (n+k) = (m+n) + 2k *)
           => if k = l then simplify (PLUS(PLUS(m, n), MULT(NUM(2), VAR(k))))
              else PLUS(a,b)
         | (PLUS(m, VAR(k)), PLUS(c, MULT(n, VAR(l)))) (* (m+k) + (c+nk) = (m+c)+((n+1)*k) *)
           => if k = l then simplify (PLUS(PLUS(m, c), MULT(PLUS(NUM(1), n), VAR(k))))
              else PLUS(a,b)
         | (PLUS(m, VAR(k)), MINUS(n, VAR(l))) (* (m+k) + (n-k) = m + n *)
           => if k = l then simplify (PLUS(m, n))
              else PLUS(a,b)
         | (PLUS(m, VAR(k)), MINUS(VAR(l), n)) (* (m+k) + (k-n) = (m-n) + 2k *)
           => if k = l then simplify (PLUS(MINUS(m, n), MULT(NUM(2), VAR(k))))
              else PLUS(a,b)
         | (PLUS(m, VAR(k)), MINUS(n, MULT(c, VAR(l)))) (* (m+k) + (n-ck) = (m+n) + (1-c)k *)
           => if k = l then simplify (PLUS(PLUS(m, n), MULT(MINUS(NUM(1), c), VAR(k))))
              else PLUS(a, b)
         | (PLUS(m, VAR(k)), MINUS(MULT(c, VAR(l)), n)) (* (m+k) + (ck-n) = (m-n) + (c+1)k *)
           => if k = l then simplify (PLUS(MINUS(m, n), MULT(PLUS(NUM(1), c), VAR(k))))
              else PLUS(a,b)
         (* FROM HERE WE HAVE THE COMMUTED VERSIONS OF THE ABOVE RULES... mostly?
                E.g., if above we simplified (x + y) + z, now we simplify z + (x + y)
          *)
         | (PLUS(n, MULT(c, VAR(l))), VAR(k)) (* (n+ck) + k = n + (c+1)k *)
           => if k = l then simplify (PLUS(n, MULT(PLUS(NUM(1), c), VAR(k))))
              else PLUS(a,b)
         | (PLUS(n, MULT(c, VAR(l))), MULT(m, VAR(k))) (* (n+ck) + mk = n + (m+c)k *)
           => if k = l then simplify (PLUS(n, MULT(PLUS(m, c), VAR(k))))
              else PLUS(a,b)
         | (PLUS(m, MULT(n, VAR(k))), PLUS(c, VAR(l))) (* (m+nk) + (c+k) = (m+c) + (1+n)k *)
           => if k = l then simplify (PLUS(PLUS(m, c), MULT(PLUS(NUM(1), n), VAR(k))))
              else PLUS(a,b)
         | (PLUS(n, MULT(c, VAR(l))), PLUS(d, MULT(m, VAR(k)))) (* (n+ck) + (d+mk) = (n+d) + (c+m)k *)
           => if k = l then simplify (PLUS(PLUS(n, d), MULT(PLUS(c, m), VAR(k))))
              else PLUS(a,b)
         | (PLUS(n, MULT(c, VAR(l))), MINUS(d, VAR(k))) (* (n+ck) + (d-k) = (n+d) + (c-1)k *)
           => if k = l then simplify (PLUS(PLUS(n, d), MULT(MINUS(c, NUM(1)), VAR(k))))
                                     (* (n-cl) + (d-k) = ((n+d)-cl) - k *)
                                     (* WHY IS THIS DIFFERENT? EVERYTHING ELSE ENDS WITH PLUS(a,b) *)
              else simplify (MINUS(PLUS(PLUS(n, d),MULT(c, VAR(l))), VAR(k)))
         | (PLUS(n, MULT(c, VAR(l))), MINUS(VAR(k), d)) (* (n+ck) + (k-d) = (n-d) + (1+c)k *)
           => if k = l then simplify (PLUS(MINUS(n, d), MULT(PLUS(NUM(1), c), VAR(k))))
              else PLUS(a,b)
         | (PLUS(n, MULT(c, VAR(l))), MINUS(d, MULT(m, VAR(k)))) (* (n+ck) + (d-mk) = (n+d) + (c-m)k *)
           => if k = l then simplify (PLUS(PLUS(n, d), MULT(MINUS(c, m), VAR(k))))
              else PLUS(a,b)
         | (PLUS(n, MULT(c, VAR(l))), MINUS(MULT(m, VAR(k)), d)) (* (n+ck) + (mk-d) = (n-d) + (c+m)k *)
           => if k = l then simplify (PLUS(MINUS(n, d), MULT(PLUS(c, m), VAR(k))))
              else PLUS(a,b)
         | (MINUS(m, VAR(k)), VAR(l)) (* (m-k) + k = m *)
           => if k = l then m
              else PLUS(a,b)
         | (MINUS(m, MULT(n, VAR(k))), VAR(l)) (* (m-nk) + k = m - (1+n)k *)
           => if k = l then simplify (MINUS(m, MULT(PLUS(NUM(1), n), VAR(k))))
              else PLUS(a,b)
         | (MINUS(m, MULT(n, VAR(k))), MULT(c, VAR(l))) (* (m-nk) + ck = m + (c-n)k *)
           => if k = l then simplify (PLUS(m, MULT(MINUS(c, n), VAR(k))))
              else PLUS(a,b)
         | (MINUS(n, MULT(c, VAR(l))), PLUS(d, MULT(m, VAR(k)))) (* (n-ck) + (d+mk) = (n+d) + (m-c)k *)
           => if k = l then simplify (PLUS(PLUS(n, d), MULT(MINUS(m, c), VAR(k))))
              else PLUS(a,b)
         | (MINUS(n, MULT(c, VAR(l))), PLUS(d, VAR(k))) (* (n-ck) + (d+k) = (n+d) + (1-c)k *)
           => if k = l then simplify (PLUS(PLUS(n, d), MULT(MINUS(NUM(1), c), VAR(k))))
              else PLUS(a,b)
         | (MINUS(n, MULT(c, VAR(l))), MINUS(d, MULT(m, VAR(k)))) (* (n-ck) + (d-mk) = (n+d) - (m+c)k *)
           => if k = l then simplify (MINUS(PLUS(n, d), MULT(PLUS(m, c), VAR(k))))
              else PLUS(a,b)
         | (MINUS(MULT(c, VAR(l)), n), MINUS(d, MULT(m, VAR(k)))) (* (ck-n) + (d-mk) = (d-n) + (c-m)k *)
           => if k = l then simplify (PLUS(MINUS(d, n), MULT(MINUS(c, m), VAR(k))))
              else PLUS(a,b)
         | (MINUS(VAR(k), c), MINUS(m, VAR(l))) (* (k-c) + (m-k) = m - c *)
           => if k = l then simplify (MINUS(m, c))
                                     (* (k-c) + (m-l) = ((m-c)+k)-l *)
                                     (* WHY IS THIS DIFFERENT? EVERYTHING ELSE ENDS WITH PLUS(a,b) *)
              else simplify (MINUS(PLUS(MINUS(m, c), VAR(k)), VAR(l)))
         | (MINUS(VAR(k), n), MINUS(c, MINUS(VAR(l), m))) (* (k-n) + (c-(k-n)) = c *)
           => if k = l andalso n = m then c
              else PLUS(a,b)
         | (a, MINUS(VAR(k), c)) (* a + (k-c) = (a-c) + k *)
           => if onlyNum a andalso onlyNum c then simplify (PLUS(MINUS(a, c), VAR(k)))
              else PLUS(a,b)
         | (a, MINUS(c, VAR(k))) (* a + (c-k) = (a+c) - k *)
           => if onlyNum a andalso onlyNum c then simplify (MINUS(PLUS(a, c), VAR(k)))
              else PLUS(a,b)
         | (a, MINUS(c, MULT(d, VAR(k)))) (* a + (c-dk) = (a+c) - dk *)
           => if onlyNum a andalso onlyNum c then simplify (MINUS(PLUS(a, c), MULT(d, VAR(k))))
              else PLUS(a,b)
         | (a, MINUS(MULT(d, VAR(k)), c)) (* a + (dk-c) = (a-c) + dk *)
           => if onlyNum a andalso onlyNum c then simplify (PLUS(MINUS(a, c), MULT(d, VAR(k))))
              else PLUS(a,b)
         | (a, PLUS(c, VAR(k))) (* a + (c+k) = (a+c) + k *)
           => if onlyNum a andalso onlyNum c then simplify (PLUS(PLUS(a, c), VAR(k)))
              else PLUS(a,b)
         | (a, PLUS(c, MULT(n, VAR(k)))) (* a + (c+nk) = (a+c) + nk *)
           => if onlyNum a andalso onlyNum c then simplify (PLUS(PLUS(a, c), MULT(n, VAR(k))))
              else PLUS(a,b)
         | (MINUS(VAR(k), c), b) (* (k-c) + b = (b-c) + k *)
           => if onlyNum b andalso onlyNum c then simplify (PLUS(MINUS(b, c), VAR(k)))
              else PLUS(a,b)
         | (MINUS(c, VAR(k)), b) (* (c-k) + b = (b+c) - k *)
           => if onlyNum b andalso onlyNum c then simplify (MINUS(PLUS(b, c), VAR(k)))
              else PLUS(a,b)
         | (MINUS(MULT(n, VAR(k)), c), b) (* (nk-c) + b = (b-c) + nk *)
           => if onlyNum b andalso onlyNum c then simplify (PLUS(MINUS(b, c), MULT(n, VAR(k))))
              else PLUS(a,b)
         | (MINUS(c, MULT(n, VAR(k))), b) (* (c-nk) + b = (b+c) - nk *)
           => if onlyNum b andalso onlyNum c then simplify (MINUS(PLUS(b, c), MULT(n, VAR(k))))
              else PLUS(a,b)
         | (PLUS(c, VAR(k)), b) (* (c+k) + b = (b+c) + k *)
           => if onlyNum b andalso onlyNum c then simplify (PLUS(PLUS(b, c), VAR(k)))
              else PLUS(a,b)
         | (PLUS(c, MULT(n, VAR(k))), b) (* (c+nk) + b = (b+c) + nk *)
           => if onlyNum b andalso onlyNum c then simplify (PLUS(PLUS(b, c), MULT(n, VAR(k))))
              else PLUS(a,b)
         | (a, MINUS(c, k)) (* k + (c-k) = c *)
           => if a = k then c
              else PLUS(a,b)
         | (MINUS(c, k), b) (* (c-k) + k = c *)
           => if b = k then c
              else PLUS(a,b)
         | (VAR(l), b) (* l + b = b + l *)
               (* simplify IS NOT CALLED RECURSIVELY HERE, WHY?? *)
           => if onlyNum b then PLUS(b,VAR(l))
              else PLUS(a,b)
         | (MULT(c, VAR(k)), b) (* ck + b = b + ck *)
           => if onlyNum b then simplify (PLUS(b, MULT(c, VAR(k))))
              else PLUS(a,b)
         | _ => PLUS(a,b)
    end
  | simplify (MINUS(x,y)) =
    let val a = simplify x
        val b = simplify y
    in case (a,b) of
           (a, NUM(0)) => a
         | (VAR(n), MULT(m, VAR(k))) (* n - mn = (1-m)n *)
           => if k = n then simplify (MULT(MINUS(NUM(1), m), VAR(n)))
              else MINUS(a,b)
         | (VAR(n), MINUS(k, MULT(d, VAR(l)))) (* n - (k - dn) = (1+d)n - k *)
           => if n = l then simplify (MINUS(MULT(PLUS(NUM(1), d), VAR(n)), k))
                                     (* n - (k - dl) = ((0-k) + dl) + n *)
                                     (* WHY IS THIS DIFFERENT? EVERYTHING ELSE ENDS WITH MINUS(a,b) *)
              else simplify (PLUS(PLUS(MINUS(NUM(0), k), MULT(d, VAR(l))), VAR(n)))
         | (VAR(n), PLUS(k, MULT(d, VAR(l)))) (* n - (k+dn) = (0-k) + (1-d)n *)
           => if n = l then simplify (PLUS(MINUS(NUM(0), k), MULT(MINUS(NUM(1), d), VAR(n))))
              else MINUS(a,b)
         | (MULT(m, VAR(k)), VAR(n)) (* mn - n = (m-1)n *)
           => if k = n then simplify (MULT(MINUS(m, NUM(1)), VAR(n)))
              else MINUS(a,b)
         | (MULT(n, VAR(m)), MULT(k, VAR(l))) (* nm - km = (n-k)m *)
           => if m = l then simplify (MULT(MINUS(n, k), VAR(m)))
              else MINUS(a,b)
         | (MULT(n, VAR(m)), MINUS(k, MULT(d, VAR(l)))) (* nm - (k-dm) = (n+d)m - k *)
           => if m = l then simplify (MINUS(MULT(PLUS(n, d),VAR(m)), k))
                                     (* nm - (k-dl) = ((0-k)+nm) + dl *)
                                     (* WHY IS THIS DIFFERENT? EVERYTHING ELSE ENDS WITH MINUS(a,b) *)
              else simplify (PLUS(PLUS(MINUS(NUM(0),k),MULT(n,VAR(m))),MULT(d,VAR(l))))
         | (MULT(n, VAR(m)), PLUS(k, VAR(l))) (* nm - (k+m) = (0-k) + (n-1)m *)
           => if m = l then simplify (PLUS(MINUS(NUM(0), k), MULT(MINUS(n, NUM(1)), VAR(m))))
              else MINUS(a,b)
         | (MULT(n, VAR(m)), PLUS(k, MULT(d, VAR(l)))) (* nm - (k +dm) = (0-k) + (n-d)m *)
           => if m = l then simplify (PLUS(MINUS(NUM(0), k), MULT(MINUS(n, d), VAR(m))))
              else MINUS(a,b)
         | (MINUS(VAR(n), m), PLUS(k, MULT(d, VAR(l)))) (* (n-m) - (k-dn) = (0-(m+k)) + (1-d)n *)
           => if n = l then simplify (PLUS(MINUS(NUM(0), PLUS(m, k)), MULT(MINUS(NUM(1), d), VAR(n))))
              else MINUS(a,b)
         | (MINUS(m, VAR(n)), MULT(d, VAR(l))) (* (m-n) - dn = m - (1+d)n *)
           => if n = l then simplify (MINUS(m, MULT(PLUS(NUM(1), d), VAR(n))))
              else MINUS(a,b)
         | (MINUS(m, VAR(n)), MINUS(d, VAR(l))) (* (m-n) - (d-n) = m - d *)
           => if n = l then simplify (MINUS(m, d))
                                     (* (m-n) - (d-l) = ((m-d)-n) + l *)
                                     (* WHY IS THIS DIFFERENT? EVERYTHING ELSE ENDS WITH MINUS(a,b) *)
              else simplify (PLUS(MINUS(MINUS(m, d), VAR(n)), VAR(l)))
         | (MINUS(m, VAR(n)), MINUS(k, MULT(d, VAR(l)))) (* (m-n) - (k-dn) = (m-k) - (1-d)n *)
           => if n = l then simplify (MINUS(MINUS(m, k), MULT(MINUS(NUM(1), d), VAR(n))))
                                     (* (m-n) - (k - dl) = ((m-k) + dl) - n *)
                                     (* WHY IS THIS DIFFERENT? EVERYTHING ELSE ENDS WITH MINUS(a,b) *)
              else simplify (MINUS(PLUS(MINUS(m, k), MULT(d, VAR(l))), VAR(n)))
         | (MINUS(m, MULT(c, VAR(n))), VAR(l)) (* (m-cn) - n = m - (1+c)n *)
           => if n = l then simplify (MINUS(m, MULT(PLUS(NUM(1), c), VAR(n))))
              else MINUS(a,b)
         | (MINUS(m, MULT(c, VAR(n))), MINUS(k, MULT(d, VAR(l)))) (* (m-cn) - (k-dn) = (m-k) - (c-d)n *)
           => if n = l then simplify (MINUS(MINUS(m, k), MULT(MINUS(c, d), VAR(n))))
                                     (* (m-cn) - (k-dl) = ((m-k) - cn) + dl *)
                                     (* WHY IS THIS DIFFERENT? EVERYTHING ELSE ENDS WITH MINUS(a,b) *)
              else simplify (PLUS(MINUS(MINUS(m, k), MULT(c, VAR(n))), MULT(d, VAR(l))))
         | (MINUS(m, MULT(c, VAR(n))), MINUS(d, VAR(l))) (* (m-cn) - (d-n) = (m-d) - (c-1)n *)
           => if n = l then simplify (MINUS(MINUS(m, d), MULT(MINUS(c, NUM(1)), VAR(n))))
                                     (* (m-cn) - (d-l) = ((m-d)-cn) + l *)
                                     (* WHY IS THIS DIFFERENT? EVERYTHING ELSE ENDS WITH MINUS(a,b) *)
              else simplify (PLUS(MINUS(MINUS(m, d), MULT(c, VAR(n))), VAR(l)))
         | (MINUS(m, MULT(c, VAR(n))), MINUS(VAR(l), d)) (* (m-cn) - (n-d) = (m+d) - (1+c)n *)
           => if n = l then simplify (MINUS(PLUS(m, d), MULT(PLUS(NUM(1), c), VAR(n))))
              else MINUS(a,b)
         | (MINUS(m, MULT(c, VAR(n))), PLUS(k, MULT(d, VAR(l)))) (* (m-cn) - (k+dn) = (m-k) - (c+d)n *)
           => if n = l then simplify (MINUS(MINUS(m, k), MULT(PLUS(c, d), VAR(n))))
              else MINUS(a,b)
         | (PLUS(c, MULT(n, VAR(l))), VAR(k)) (* (c+nk) - k = c + (n-1)k *)
           => if k = l then simplify (PLUS(c, MULT(MINUS(n, NUM(1)), VAR(k))))
              else MINUS(a,b)
         | (PLUS(c, MULT(n, VAR(l))), MULT(m, VAR(k))) (* (c+nk) - mk = c + (n-m)k *)
           => if k = l then simplify (PLUS(c, MULT(MINUS(n, m), VAR(k))))
              else MINUS(a,b)
         | (PLUS(c, MULT(n, VAR(l))), MINUS(d, VAR(k))) (* (c+nl) - (d-l) = (c-d) + (1+n)l *)
           => if k = l then simplify (PLUS(MINUS(c, d), MULT(PLUS(NUM(1), n), VAR(l))))
                                     (* (c+nl) - (d-k) = ((c-d) + nl) + k *)
                                     (* WHY IS THIS DIFFERENT? EVERYTHING ELSE ENDS WITH MINUS(a,b) *)
              else simplify (PLUS(PLUS(MINUS(c, d), MULT(n, VAR(l))), VAR(k)))
         | (PLUS(m, MULT(c, VAR(n))), MINUS(k, MULT(d, VAR(l)))) (* (m+cn) - (k-dn) = (m-k) + (c+d)n *)
           => if n = l then simplify (PLUS(MINUS(m, k), MULT(PLUS(c, d), VAR(n))))
              else MINUS(a,b)
         | (PLUS(m, MULT(d, VAR(k))), PLUS(c, MULT(n, VAR(l)))) (* (m+dk) - (c+nk) = (m-c) + (d-n)k *)
           => if k = l then simplify (PLUS(MINUS(m, c), MULT(MINUS(d, n), VAR(k))))
              else MINUS(a,b)
         | (PLUS(m, VAR(k)), PLUS(c, MULT(n, VAR(l)))) (* (m+k) - (c + nk) = (m-c) + (1-n)k *)
           => if k = l then simplify (PLUS(MINUS(m, c), MULT(MINUS(NUM(1), n), VAR(k))))
              else MINUS(a,b)
         | (PLUS(m, VAR(k)), MULT(n, VAR(l))) (* (m+k) - nk = m + (1-n)k *)
           => if k = l then simplify (PLUS(m, MULT(MINUS(NUM(1), n), VAR(k))))
              else MINUS(a,b)
         | (PLUS(m, VAR(k)), MINUS(c, VAR(l))) (* (m+k) - (c-k) = (m-c) + 2k *)
           => if k = l then simplify (PLUS(MINUS(m,c),MULT(NUM(2),VAR(k))))
                                     (* (m+k) - (c-l) = ((m-c) + k) + l *)
                                     (* WHY IS THIS DIFFERENT? EVERYTHING ELSE ENDS WITH MINUS(a,b) *)
              else simplify (PLUS(PLUS(MINUS(m,c),VAR(k)),VAR(l)))
         | (PLUS(m, VAR(n)), b)
           => if m = b then VAR(n) (* (b+n) - b = n *)
              else if onlyNum m andalso onlyNum b
              then simplify (PLUS(MINUS(m, b), VAR(n))) (* (m+n) - b = (m-b) + n *)
              else MINUS(a,b)
         | (a, PLUS(c, VAR(k))) (* a - (c+k) = (a-c) - k *)
           => if onlyNum a andalso onlyNum c then simplify (MINUS(MINUS(a, c), VAR(k)))
              else MINUS(a,b)
         | (a, PLUS(c, MULT(m, VAR(k)))) (* a - (c+mk) = (a-c) - mk *)
           => if onlyNum a andalso onlyNum c then simplify (MINUS(MINUS(a, c), MULT(m, VAR(k))))
              else MINUS(a,b)
         | (a, MINUS(c, VAR(k))) (* a - (c-k) = (a-c) + k *)
           => if onlyNum a andalso onlyNum c then simplify (PLUS(MINUS(a, c), VAR(k)))
              else MINUS(a,b)
         | (a, MINUS(VAR(k), c)) (* a - (k - c) = (a + c) - k *)
           => if onlyNum a andalso onlyNum c then simplify (MINUS(PLUS(a, c), VAR(k)))
              else MINUS(a,b)
         | (a, MINUS(c, MULT(m, VAR(k)))) (* a - (c - mk) = (a-c) + mk *)
           => if onlyNum a andalso onlyNum c then simplify (PLUS(MINUS(a, c), MULT(m, VAR(k))))
              else MINUS(a,b)
         | (a, MINUS(MULT(m, VAR(k)), c)) (* a - (mk - c) = (a+c) - mk *)
           => if onlyNum a andalso onlyNum c then simplify (MINUS(PLUS(a, c), MULT(m, VAR(k))))
              else MINUS(a,b)
         | (a, PLUS(c, FRAC(m, VAR(k)))) (* a - (c + m/k) = (a - c) - m/k *)
           => if onlyNum a andalso onlyNum c then simplify (MINUS(MINUS(a, c), FRAC(m, VAR(k))))
              else MINUS(a,b)
         | (a, MINUS(c, FRAC(m, VAR(k)))) (* a - (c - mk) = (a-c) + m/k *)
           => if onlyNum a andalso onlyNum c then simplify (PLUS(MINUS(a, c), FRAC(m, VAR(k))))
              else MINUS(a,b)
         | (MINUS(c, VAR(k)), b) (* (c-k) - b = (c-b) - k *)
           => if onlyNum b andalso onlyNum c then simplify (MINUS(MINUS(c, b), VAR(k)))
              else MINUS(a,b)
         | (MINUS(c, MULT(d, VAR(k))), MULT(e, VAR(l))) (* (c - dk) - ek = c - (d + e)k *)
           => if onlyNum c andalso k = l then simplify (MINUS(c, MULT(PLUS(d, e), VAR(k))))
              else MINUS(a,b)
         | (MINUS(c, MULT(d, VAR(k))), b) (* (c-dk) - b = (c-b) - dk *)
           => if onlyNum c andalso onlyNum b then simplify (MINUS(MINUS(c, b), MULT(d, VAR(k))))
              else MINUS(a,b)
         | (PLUS(c, MULT(d, VAR(k))), b) (* (c+dk) - b = (c-b) + dk *)
           => if onlyNum c andalso onlyNum b then simplify (PLUS(MINUS(c, b), MULT(d, VAR(k))))
              else MINUS(a,b)
         | (a, MINUS(k, m))
           => if a = k then m (* a - (a - m) = m *)
              else if onlyNum a andalso onlyNum k
              then simplify (PLUS(MINUS(a,k),m)) (* a - (k-m) = (a-k) + m *)
              else MINUS(a,b)
         | (PLUS(c, d), b)
           => if c = b then d (* (c+d) - c = d *)
              else if d = b then c (* (c+d) - d = c *)
              else MINUS(a,b)
         | (a, PLUS(c, d))
           => if a = c then simplify (MINUS(NUM(0),d)) (* a - (a+d) = 0 - d *)
              else if a = d then simplify (MINUS(NUM(0),c)) (* a - (c+a) = 0 - c *)
              else MINUS(a,b)
         | (a, b)
           => if a = b then NUM(0) (* a - a = 0 *)
              else MINUS(a,b)
    end
  | simplify (MULT(x,y)) =
    let val a = simplify x;
        val b = simplify y;
    in case (a, b) of
           (NUM(0), b) => NUM(0)
         | (a, NUM(0)) => NUM(0)
         | (NUM(1), b) => b
         | (a, NUM(1)) => a
         | (NUM(~1), b) => MINUS(NUM(0), b)
         | (a, NUM(~1)) => MINUS(NUM(0), a)
         | (VAR(k), MINUS(c, FRAC(n, VAR(l)))) (* k(c - n/k) = ck - n *)
           => if k = l then simplify (MINUS(MULT(c, VAR(k)), n))
              else MULT(a,b)
         | (MINUS(c, FRAC(n, VAR(l))), VAR(k)) (* (c - n/k)k = ck - n *)
           => if k = l then simplify (MINUS(MULT(c, VAR(k)), n))
              else MULT(a,b)
         | (VAR(k), PLUS(c, FRAC(n, VAR(l)))) (* k(c + n/k) = n + ck *)
           => if k = l then simplify (PLUS(n, MULT(c, VAR(k))))
              else MULT(a,b)
         | (PLUS(c, FRAC(n, VAR(l))), VAR(k)) (* (c + n/k)k = n + ck *)
           => if k = l then simplify (PLUS(n, MULT(c, VAR(k))))
              else MULT(a,b)
         | (a, MULT(FRAC(c, k), l))
           => if a = k then simplify (MULT(c,l)) (* a(c/a * l) = cl *)
              else if onlyNum a andalso onlyNum c andalso onlyNum k
              then simplify (MULT(MULT(a, FRAC(c, k)), l)) (* a(c/k * l) = (a*c/k)l *)
              else MULT(a,b)
         | (MULT(FRAC(c, k), l), b)
           => if b = k then simplify (MULT(c,l)) (* (c/k * l)k = cl *)
              else if onlyNum b andalso onlyNum c andalso onlyNum k
              then simplify (MULT(MULT(b, FRAC(c, k)), l)) (* (c/k * l)b = (b * c/k) * l *)
              else MULT(a,b)
         | (FRAC(n, m), MINUS(d, MULT(c, VAR(k))))
           => if m = b then n (* n/(d - ck) * (d - ck) = n *)
              else if onlyNum a andalso onlyNum d
              then simplify (MINUS(MULT(a,d),MULT(MULT(a,c),VAR(k)))) (* n/m * (d - ck) = (n/m)d - (n/m)ck *)
              else MULT(a,b)
         | (MINUS(d, MULT(c, VAR(k))), FRAC(n,m))
           => if m = a then n (* (d - ck)(n/(d - ck)) = n *)
              else if onlyNum b andalso onlyNum d
                                                (* (d - ck)(n/m) = (n/m * d) - (nm * c * k) *)
              then simplify (MINUS(MULT(b, d), MULT(MULT(b, c), VAR(k))))
              else MULT(a,b)
         | (MINUS(n, FRAC(m, l)), MINUS(d, MULT(c, VAR(k))))
           => if l = b then simplify (MINUS(MULT(n, b), m)) (* (n - m/(d - ck))(d - ck) = n(d - ck) - m *)
              else if onlyNum a andalso onlyNum d
                                                (* (n - m/l)(d - ck) = (n - m/l)d - (n - m/l)ck *)
              then simplify (MINUS(MULT(a, d), MULT(MULT(a, c), VAR(k))))
              else MULT(a,b)
         | (MINUS(d, MULT(c, VAR(k))), MINUS(n, FRAC(m, l)))
           => if a = l then simplify (MINUS(MULT(n, a), m)) (* (d-ck)(n-m/(d-ck)) = n(d-ck) - m *)
              else if onlyNum b andalso onlyNum d (* (d-ck)(n-m/l) = (n-m/l)d - (n-m/l)ck *)
              then simplify (MINUS(MULT(b,d),MULT(MULT(b,c),VAR(k))))
              else MULT(a,b)
         | (a, MINUS(MULT(c, VAR(k)), d))
           => if onlyNum a andalso onlyNum d (* a(ck - d) = ack - ad *)
              then simplify (MINUS(MULT(MULT(a, c), VAR(k)), MULT(a, d)))
              else MULT(a,b)
         | (MINUS(MULT(c, VAR(k)), d), b)
           => if onlyNum b andalso onlyNum d (* (ck - d)b = bck - bd *)
              then simplify (MINUS(MULT(MULT(b, c), VAR(k)), MULT(b, d)))
              else MULT(a,b)
         | (a, MINUS(d, MULT(c, VAR(k))))
           => if onlyNum a andalso onlyNum d (* a(d - ck) = ad - ack *)
              then simplify (MINUS(MULT(a, d), MULT(MULT(a, c), VAR(k))))
              else MULT(a,b)
         | (MINUS(d, MULT(c, VAR(k))), b)
           => if onlyNum b andalso onlyNum d (* (d - ck)b = bd - bck *)
              then simplify (MINUS(MULT(b, d), MULT(MULT(b, c), VAR(k))))
              else MULT(a,b)
         | (a, PLUS(d, MULT(c, VAR(k))))
           => if onlyNum a (* a(d + ck) = ad + ck *)
              then simplify (PLUS(MULT(a, d), MULT(MULT(a, c), VAR(k))))
              else MULT(a,b)
         | (PLUS(d, MULT(c, VAR(k))), b)
           => if onlyNum b (* (d + ck)b = bd + bck *)
              then simplify (PLUS(MULT(b, d), MULT(MULT(b, c), VAR(k))))
              else MULT(a,b)
         | (MINUS(c, FRAC(k, l)), MINUS(d, VAR(n)))
           => if l = b (* (c - k/(d-n))(d - n) = (0-k) + c(d-n) *)
              then simplify (PLUS(MINUS(NUM(0), k), MULT(c, l)))
              else MULT(a,b)
         | (FRAC(c, k), MINUS(m, VAR(n))) (* c/(m-n) * (m-n) = c *)
           => if k = b orelse numToString k = numToString b then c else MULT(a,b)
         | (a, MINUS(c, VAR(k)))
           => if onlyNum a andalso onlyNum c (* a(c - k) = ac - ak *)
              then simplify (MINUS(MULT(a, c), MULT(a, VAR(k))))
              else MULT(a,b)
         | (a, MINUS(c, FRAC(k, l))) (* a(c - k/a) = ac - k *)
           => if a = l then simplify (MINUS(MULT(c, a), k))
              else MULT(a,b)
         | (MINUS(c, FRAC(k, l)), b) (* (c - k/b)b = cb - k *)
           => if b = l then simplify (MINUS(MULT(c, b), k))
              else MULT(a,b)
         | (a, MULT(c, VAR(k)))
           => if onlyNum a andalso onlyNum c (* a(ck) = (ac)k *)
              then simplify (MULT(MULT(a, c), VAR(k)))
              else MULT(a,b)
         | (a, FRAC(c, k)) (* ac/a = c *)
           => if a = k then c else MULT(a,b)
         | (FRAC(c, k), b) (* (c/b)b = c *)
           => if b = k then c else MULT(a,b)
         | (a, MINUS(c, k))
           => if onlyNum a andalso onlyNum c (* a(c - k) = ac - ak *)
              then simplify (MINUS(MULT(a, c), MULT(a, k)))
              else MULT(a,b)
         | (MINUS(c, k), b)
           => if onlyNum b andalso onlyNum c (* (c - k)b = bc - bk *)
              then simplify (MINUS(MULT(b, c), MULT(b, k)))
              else MULT(a,b)
         | (a, PLUS(c, k))
           => if onlyNum a andalso onlyNum c (* a(c + k) = ac + ak *)
              then simplify (PLUS(MULT(a, c), MULT(a, k)))
              else MULT(a,b)
         | (PLUS(c, k), b)
           => if onlyNum b andalso onlyNum c (* (c + k)b = bc + bk *)
              then simplify (PLUS(MULT(b, c), MULT(b, k)))
              else MULT(a,b)
         | (a, MULT(c, k))
           => if onlyNum a andalso onlyNum c (* a(ck) = (ac)k *)
              then simplify (MULT(MULT(a, c), k))
              else MULT(a,b)
         | (MULT(c, k), b)
           => if onlyNum b andalso onlyNum c (* (ck)b = (bc)k *)
              then simplify (MULT(MULT(b, c), k))
              else MULT(a,b)
         | (VAR(k), b) (* kb = bk *)
           => if onlyNum b then MULT(b,VAR(k)) else MULT(a,b)
         | _ => MULT(a,b)
        end
  | simplify (FRAC(x,y)) =
    let val a = simplify x;
        val b = simplify y;
    in if numToString a = numToString b then NUM(1)
       else if numToString b = numToString (NUM(0)) then raise NumError
       else if numToString a = numToString (NUM(0)) then NUM(0)
       else case (a, b) of
                (NUM(0), _) => NUM(0)
              | (a, NUM(1)) => a
              | (MULT(c, VAR(k)), b)
                => if c = b then VAR(k) (* ck/c = k *)
                   else if b = (VAR(k)) then c (* ck/k = c *)
                   else if onlyNum b andalso onlyNum c (* ck/b = (c/b)k *)
                   then simplify (MULT(FRAC(c,b),VAR(k)))
                   else FRAC(a,b)
              | (MULT(VAR(k), c), b)
                => if c = b then VAR(k) (* kc/c = k *)
                   else if b = (VAR(k)) then c (* kc/k = c *)
                   else if onlyNum b andalso onlyNum c (* kc/b = (c/b)k *)
                   then simplify (MULT(FRAC(c, b), VAR(k)))
                   else FRAC(a,b)
              | (MULT(c, k), b)
                => if b = c then k (* ck/c = k *)
                   else if b = k then c (* ck/k = c *)
                   else FRAC(a,b)
              | (PLUS(c, VAR(k)), VAR(l)) (* (c+l)/l = 1 + c/l *)
                => if k = l then simplify (PLUS(NUM(1), FRAC(c, VAR(l))))
                   else FRAC(a,b)
              | (MINUS(c, MULT(d, VAR(k))), VAR(l)) (* (c - dk)/k = (0-d) + c/k *)
                => if k = l then simplify (PLUS(MINUS(NUM(0), d), FRAC(c, VAR(k))))
                   else FRAC(a,b)
              | (MINUS(MULT(d, VAR(k)), c), VAR(l)) (* (dk - c)/k = d - c/k *)
                => if k = l then simplify (MINUS(d, FRAC(c, VAR(k))))
                   else FRAC(a,b)
              | (PLUS(c, MULT(d, VAR(k))), VAR(l)) (* (c + dk)/k = d + c/k *)
                => if k = l then simplify (PLUS(d, FRAC(c, VAR(k))))
                   else FRAC(a,b)
              | (MINUS(VAR(k), c), b)
                => if onlyNum b andalso onlyNum c (* (k - c)/b = (1/b)k - c/b *)
                   then simplify (MINUS(MULT(FRAC(NUM(1), b), VAR(k)), FRAC(c, b)))
                   else FRAC(a,b)
              | (MINUS(c, VAR(k)), b)
                => if onlyNum b andalso onlyNum c (* (c-k)/b = c/b - (1/b)k *)
                   then simplify (MINUS(FRAC(c, b), MULT(FRAC(NUM(1), b), VAR(k))))
                   else FRAC(a,b)
              | (PLUS(c, VAR(k)), b)
                => if onlyNum b andalso onlyNum c (* (c+k)/b = c/b + (1/b)k *)
                   then simplify (PLUS(FRAC(c, b), MULT(FRAC(NUM(1), b), VAR(k))))
                   else FRAC(a,b)
              | (MINUS(c, MULT(d, VAR(k))), b)
                => if onlyNum b andalso onlyNum c andalso onlyNum d (* (c - dk)/b = (c/b) - (d/b)k *)
                   then simplify (MINUS(FRAC(c, b), MULT(FRAC(d, b), VAR(k))))
                   else FRAC(a,b)
              | (MINUS(MULT(d, VAR(k)), c), b)
                => if onlyNum b andalso onlyNum c (* (dk - c)/b = (d/b)k - c/b *)
                   then simplify (MINUS(MULT(FRAC(d, b), VAR(k)), FRAC(c, b)))
                   else FRAC(a,b)
              | (PLUS(c, MULT(d, VAR(k))), b)
                => if onlyNum b andalso onlyNum c andalso onlyNum d (* (c+dk)/b = (c/b) + (d/b)k *)
                   then simplify (PLUS(FRAC(c, b), MULT(FRAC(d, b), VAR(k))))
                   else FRAC(a,b)
              | _ => FRAC(a,b)
    end
  | simplify x = x;

fun resolve a b (n:int) =
    let fun countU lst =
            let fun countU' res [] = res
                  | countU' res (x::xs) = if x = U then countU' (res + 1) xs
                                          else countU' res xs;
            in countU' 0 lst end;
        fun contains n (PLUS(a,b)) = contains n a orelse contains n b
          | contains n (MINUS(a,b)) = contains n a orelse contains n b
          | contains n (MULT(a,b)) = contains n a orelse contains n b
          | contains n (FRAC(a,b)) = contains n a orelse contains n b
          | contains n x = n = x;
        fun replace x y (PLUS(a,b)) = let val c = replace x y a;
                                          val d = replace x y b;
                                      in PLUS(c,d) end
          | replace x y (MINUS(a,b)) = let val c = replace x y a;
                                           val d = replace x y b;
                                       in MINUS(c,d) end
          | replace x y (MULT(a,b)) = let val c = replace x y a;
                                          val d = replace x y b;
                                      in MULT(c,d) end
          | replace x y (FRAC(a,b)) = let val c = replace x y a;
                                          val d = replace x y b;
                                      in FRAC(c,d) end
          | replace x y z = if y = z then simplify x else z;
        fun solveVar x y =
            case (simplify x, simplify y) of
                (VAR(n), y) => SOME (VAR(n), y) (* N = y => N = y *)
              | (x, VAR(n)) => SOME (VAR(n), x) (* x = N => N = x *)
              | (MINUS(n, MULT(m, VAR(w))), MULT(k, VAR(l))) (* n - mW = kW => W = n/(m+k) *)
                => if w = l then SOME (VAR(w), FRAC(n, PLUS(m, k)))
                   else NONE
              | (MULT(k, VAR(l)), MINUS(n, MULT(m, VAR(w)))) (* kW = n - mW => W = n/(m+k) *)
                => if w = l then SOME (VAR(w), FRAC(n, PLUS(m, k)))
                   else NONE
              | (FRAC(MINUS(n, MULT(m, VAR(k))), VAR(l)), y) (* (n-mK)/K = y => K = n/(m+y) *)
                => if k = l then SOME (VAR(k), FRAC(n, PLUS(m, y)))
                   else NONE
              | (x, FRAC(MINUS(n, MULT(m, VAR(k))), VAR(l))) (* x = (n - mK)/K => K = n/(m+x) *)
                => if k = l then SOME (VAR(k), FRAC(n, PLUS(m, x)))
                   else NONE
              | (FRAC(MINUS(n, MULT(m, MINUS(s, VAR(k)))), VAR(l)), y)
                    (* (n-m(s-K))/K = y => K = (n-ms)/(y-m) *)
                => if k = l then SOME (VAR(k), FRAC(MINUS(n, MULT(m, s)), MINUS(y, m)))
                   else NONE
              | (x, FRAC(MINUS(n, MULT(m, MINUS(s, VAR(k)))), VAR(l)))
                    (* x = (n-m(s-K))/K => K = (n-ms)/(x-m) *)
                => if k = l then SOME (VAR(k), FRAC(MINUS(n, MULT(m, s)), MINUS(x, m)))
                   else NONE
              | (FRAC(MINUS(n, MULT(MINUS(s, VAR(k)), m)), VAR(l)), y)
                    (* (n - (s - K)m)/K = y => K = (n-ms)/(y-m) *)
                => if k = l then SOME (VAR(k), FRAC(MINUS(n, MULT(m, s)), MINUS(y, m)))
                   else NONE
              | (x, FRAC(MINUS(n, MULT(MINUS(s, VAR(k)), m)), VAR(l)))
                    (* x = (n - (s-K)m)/K => K = (n-ms)/(x-m) *)
                => if k = l then SOME (VAR(k), FRAC(MINUS(n, MULT(m, s)), MINUS(x, m)))
                   else NONE
              | (FRAC(PLUS(n, MULT(m, VAR(k))), VAR(l)), y)
                    (* (n + mK)/K = y => K = n/(y-m) *)
                => if k = l then SOME (VAR(k), FRAC(n, MINUS(y, m)))
                   else NONE
              | (x, FRAC(PLUS(n, MULT(m, VAR(k))), VAR(l)))
                    (* x = (n + mK)/K => K = n/(x-m) *)
                => if k = l then SOME (VAR(k), FRAC(n,MINUS(x,m)))
                   else NONE
              | (x, PLUS(n, MULT(m, VAR(k)))) => SOME (VAR(k), FRAC(MINUS(x, n), m))
              | (PLUS(n, MULT(m, VAR(k))), y) => SOME (VAR(k), FRAC(MINUS(y, n), m))
              | (x, MINUS(MULT(m, VAR(k)), n)) => SOME (VAR(k), FRAC(PLUS(x, n), m))
              | (MINUS(MULT(m, VAR(k)), n), y) => SOME (VAR(k), FRAC(PLUS(y, n), m))
              | (x, MINUS(n, MULT(m, VAR(k)))) => SOME (VAR(k), FRAC(MINUS(n, x), m))
              | (MINUS(n, MULT(m, VAR(k))), y) => SOME (VAR(k), FRAC(MINUS(n, y), m))
              | (MULT(m, VAR(n)), y) => if contains (VAR(n)) y 
                                        then NONE 
                                        else SOME (VAR(n), FRAC(y, m))
              | (x, MULT(m, VAR(n))) => if contains (VAR(n)) x
                                        then NONE
                                        else SOME (VAR(n), FRAC(x, m))
              | (MINUS(c, VAR(n)), y) => SOME (VAR(n), MINUS(c, y))
              | (x, MINUS(c, VAR(n))) => SOME (VAR(n), MINUS(c, x))
              | (MINUS(VAR(n), c), y) => SOME (VAR(n), PLUS(c, y))
              | (x, MINUS(VAR(n), c)) => SOME (VAR(n), PLUS(c, x))
              | _ => NONE;
        fun filterNum xs ys nx ny =
            let fun filterNum' ans [] [] = List.rev ans
                  | filterNum' ans [] ys = (List.rev ans)@ys
                  | filterNum' ans xs [] = (List.rev ans)@xs
                  | filterNum' ans (x::xs) (y::ys) =
                    if onlyNum x then filterNum' (x::ans) xs ys
                    else if onlyNum y then filterNum' (y::ans) xs ys
                    else if x = U then filterNum' (y::ans) xs ys
                    else if y = U then filterNum' (x::ans) xs ys
                    else if nx > ny then filterNum' (y::ans) xs ys
                    else filterNum' (x::ans) xs ys
            in filterNum' [] xs ys end;
        fun tResolve a b c d 0 = (List.revAppend (c, a), List.revAppend (d, b))
          | tResolve [] [] c d _ = (List.rev c, List.rev d)
          | tResolve (a::aas) (b::bbs) c d e =
            if allNum (a::aas@c) orelse allNum (b::bbs@d)
            then (List.revAppend (c, (a::aas)), List.revAppend (d, (b::bbs)))
            else 
              let val x = simplify a;
                  val y = simplify b;
                  val xs = List.map simplify aas;
                  val ys = List.map simplify bbs;
              in if x = U
                 then tResolve xs ys (y::c) (y::d) (e-1)
                 else if y = U
                 then tResolve xs ys (x::c) (x::d) (e-1)
                 else if (x = y orelse (numToString x) = (numToString y)) andalso String.size (numToString x) > 1
                 then tResolve xs ys (x::c) (y::d) (e-1)
                 else if onlyNum y
                 then (case (x,y) of
                         (VAR(n), y) => let val zs = List.map (replace y x) xs;
                                            val ws = List.map (replace y x) c;
                                        in tResolve zs ys (y::ws) (y::d) (e-1) end
                       | (FRAC(k, VAR(n)), y) =>
                         if contains (VAR(n)) k
                         then case (solveVar x y) of
                                  NONE => tResolve xs ys (y::c) (y::d) (e-1)
                                | SOME(a,b) =>   let val zx = List.map (replace b a) xs;
                                                     val wx = List.map (replace b a) c;
                                                 in tResolve zx ys (y::wx) (y::d) (e-1) end
                         else if String.size n > 1
                         then let val f = replace (FRAC(k,y)) (VAR(n));
                                  val zx = List.map f xs;
                                  val zy = List.map f ys;
                                  val wx = List.map f c;
                                  val wy = List.map f d;
                              in tResolve zx zy (y::wx) (y::wy) (e-1) end
                         else let val f = replace (FRAC(k,y)) (VAR(n));
                                  val zs = List.map f xs;
                                  val ws = List.map f c;
                              in tResolve zs ys (y::ws) (y::d) (e-1) end
                       | (FRAC(VAR(n), k), y) =>
                         let val f = replace (MULT(y,k)) (VAR(n));
                             val zs = List.map f xs;
                             val ws = List.map f c;
                         in tResolve zs ys (y::ws) (y::d) (e-1) end
                       | (FRAC(MINUS(VAR(n), m), k), y) =>
                         let val f = replace (PLUS(MULT(y,k),m)) (VAR(n));
                             val zs = List.map f xs;
                             val ws = List.map f c;
                         in tResolve zs ys (y::ws) (y::d) (e-1) end
                       | (FRAC(MULT(m, VAR(n)), MINUS(k, MULT(q, VAR(l)))), y) =>
                         if n = l
                         then let val f = replace (FRAC(MULT(y,k),PLUS(m,MULT(y,q)))) (VAR(n));
                                  val zs = List.map f xs;
                                  val ws = List.map f c;
                              in tResolve zs ys (y::ws) (y::d) (e-1) end
                         else let val f = replace (FRAC(MULT(y,MINUS(k,MULT(q,VAR(l)))),m)) (VAR(n));
                                  val zs = List.map f xs;
                                  val ws = List.map f c;
                              in tResolve zs ys (y::ws) (y::d) (e-1) end
                       | (FRAC(MULT(m, VAR(n)), MINUS(k, VAR(l))), y) =>
                         if n = l
                         then let val f = replace (FRAC(MULT(y,k),PLUS(y,m))) (VAR(n));
                                  val zs = List.map f xs;
                                  val ws = List.map f c;
                              in tResolve zs ys (y::ws) (y::d) (e-1) end
                         else let val f = replace (FRAC(MULT(y,MINUS(k,VAR(l))),m)) (VAR(n));
                                  val zs = List.map f xs;
                                  val ws = List.map f c;
                              in tResolve zs ys (y::ws) (y::d) (e-1) end
                       | (FRAC(k, MULT(m, VAR(n))), y) =>
                         let val f = replace (FRAC(k,MULT(y,m))) (VAR(n));
                             val zx = List.map f xs;
                             val zy = List.map f ys;
                             val wx = List.map f c;
                             val wy = List.map f d;
                         in tResolve zx zy (y::wx) (y::wy) (e-1) end
                       | (FRAC(MULT(m, VAR(n)), k), y) =>
                         let val f = replace (FRAC(MULT(y,k),m)) (VAR(n));
                             val zs = List.map f xs;
                             val ws = List.map f c;
                         in tResolve zs ys (y::ws) (y::d) (e-1) end
                       | (FRAC(k, MINUS(m, VAR(n))), y) =>
                         let val f = replace (FRAC(MINUS(MULT(y,m),k),y)) (VAR(n));
                             val zs = List.map f xs;
                             val ws = List.map f c;
                         in tResolve zs ys (y::ws) (y::d) (e-1) end
                       | (FRAC(k, MINUS(m, MULT(l, VAR(n)))), y) =>
                         let val f = replace (FRAC(MINUS(MULT(y,m),k),MULT(y,l))) (VAR(n));
                             val zs = List.map f xs;
                             val ws = List.map f c;
                         in tResolve zs ys (y::ws) (y::d) (e-1) end
                       | (FRAC(MINUS(MULT(m, VAR(n)), k), PLUS(q, MULT(p, VAR(l)))), y) =>
                         if n = l
                         then let val f = replace (FRAC(PLUS(MULT(y,q),k),MINUS(m,MULT(y,p)))) (VAR(n));
                                  val zs = List.map f xs;
                                  val ws = List.map f c;
                              in tResolve zs ys (y::ws) (y::d) (e-1) end
                         else tResolve xs ys (y::c) (y::d) (e-1)
                       | (MULT(k, VAR(n)), y) =>
                         let val f = replace (FRAC(y,k)) (VAR(n));
                             val zs = List.map f xs;
                             val ws = List.map f c;
                         in tResolve zs ys (y::ws) (y::d) (e-1) end
                       | (MULT(VAR(n), k), y) =>
                         let val f = replace (FRAC(y,k)) (VAR(n));
                             val zs = List.map f xs;
                             val ws = List.map f c;
                         in tResolve zs ys (y::ws) (y::d) (e-1) end
                       | (MULT(PLUS(l, VAR(n)), k), y) =>
                         let val f = replace (MINUS(FRAC(y,k),l)) (VAR(n));
                             val zs = List.map f xs;
                             val ws = List.map f c;
                         in tResolve zs ys (y::ws) (y::d) (e-1) end
                       | (MULT(k, PLUS(l, VAR(n))), y) =>
                         let val f = replace (MINUS(FRAC(y,k),l)) (VAR(n));
                             val zs = List.map f xs;
                             val ws = List.map f c;
                         in tResolve zs ys (y::ws) (y::d) (e-1) end
                       | (MINUS(k, VAR(n)), y) =>
                         let val f = replace (MINUS(k,y)) (VAR(n));
                             val zs = List.map f xs;
                             val ws = List.map f c;
                         in tResolve zs ys (y::ws) (y::d) (e-1) end
                       | (MINUS(VAR(n), k), y) =>
                         let val f = replace (PLUS(y,k)) (VAR(n));
                             val zs = List.map f xs;
                             val ws = List.map f c;
                         in tResolve zs ys (y::ws) (y::d) (e-1) end
                       | (MINUS(k, MULT(VAR(n), m)), y) =>
                         let val f = replace (FRAC(MINUS(k,y),m)) (VAR(n));
                             val zs = List.map f xs;
                             val ws = List.map f c;
                         in tResolve zs ys (y::ws) (y::d) (e-1) end
                       | (MINUS(k, MULT(m, VAR(n))), y) =>
                         let val f = replace (FRAC(MINUS(k,y),m)) (VAR(n));
                             val zs = List.map f xs;
                             val ws = List.map f c;
                         in tResolve zs ys (y::ws) (y::d) (e-1) end
                       | (MINUS(FRAC(VAR(n), m), k), y) =>
                         let val f = replace (MULT(PLUS(y,k),m)) (VAR(n));
                             val zs = List.map f xs;
                             val ws = List.map f c;
                         in tResolve zs ys (y::ws) (y::d) (e-1) end
                       | (PLUS(k, VAR(n)), y) =>
                         let val f = replace (MINUS(y,k)) (VAR(n));
                             val zs = List.map f xs;
                             val ws = List.map f c;
                         in tResolve zs ys (y::ws) (y::d) (e-1) end
                       | (PLUS(k, MULT(m, VAR(n))), y) =>
                         let val f = replace (FRAC(MINUS(y,k),m)) (VAR(n));
                             val zs = List.map f xs;
                             val ws = List.map f c;
                         in tResolve zs ys (y::ws) (y::d) (e-1) end
                       | (PLUS(k, MULT(VAR(n), m)), y) =>
                         let val f = replace (FRAC(MINUS(y,k),m)) (VAR(n));
                             val zs = List.map f xs;
                             val ws = List.map f c;
                         in tResolve zs ys (y::ws) (y::d) (e-1) end
                       | (PLUS(k, FRAC(m, VAR(n))), y) =>
                         let val f = replace (FRAC(m,MINUS(y,k))) (VAR(n));
                             val zs = List.map f xs;
                             val ws = List.map f c;
                         in tResolve zs ys (y::ws) (y::d) (e-1) end
                       | _ => tResolve xs ys (y::c) (y::d) (e-1))
               else if onlyNum x (* NOTE: I BET THESE ARE A SYMMETRIC COPY OF ABOVE! *)
               then (case (x,y) of
                         (x, VAR(n)) => let val zs = List.map (replace x y) ys;
                                            val ws = List.map (replace x y) d;
                                        in tResolve xs zs (x::c) (x::ws) (e-1)end
                       | (x, FRAC(VAR(n), k)) =>
                         let val f = replace (MULT(x,k)) (VAR(n));
                             val zs = List.map f ys;
                             val ws = List.map f d;
                         in tResolve xs zs (x::c) (x::ws) (e-1) end
                       | (x, FRAC(k, VAR(n))) =>
                         if contains (VAR(n)) k
                         then case (solveVar x y) of
                                  NONE => tResolve xs ys (x::c) (x::d) (e-1)
                                | SOME(a,b) =>
                                  let val zy = List.map (replace b a) ys;
                                      val wy = List.map (replace b a) d;
                                  in tResolve xs zy (x::c) (y::wy) (e-1) end
                         else if String.size n > 1
                         then let val f = replace (FRAC(k,x)) (VAR(n));
                                  val zx = List.map f xs;
                                  val wx = List.map f c;
                                  val zy = List.map f ys;
                                  val wy = List.map f d;
                              in tResolve zx zy (x::wx) (x::wy) (e-1) end
                         else let val f = replace (FRAC(k,x)) (VAR(n));
                                  val zs = List.map f ys;
                                  val ws = List.map f d;
                              in tResolve xs zs (x::c) (x::ws) (e-1) end
                       | (x, FRAC(MINUS(VAR(n), m), k)) =>
                         let val f = replace (PLUS(MULT(x,k),m)) (VAR(n));
                             val zs = List.map f ys;
                             val ws = List.map f d;
                         in tResolve xs zs (x::c) (x::ws) (e-1) end
                       | (x, FRAC(MULT(m, VAR(n)), MINUS(k, MULT(q, VAR(l))))) =>
                         if n = l
                         then let val f = replace (FRAC(MULT(x,k),PLUS(m,MULT(x,q)))) (VAR(n));
                                  val zs = List.map f ys;
                                  val ws = List.map f d;
                              in tResolve xs zs (x::c) (x::ws) (e-1) end
                         else let val f = replace (FRAC(MULT(x,MINUS(k,MULT(q,VAR(l)))),m)) (VAR(n));
                                  val zs = List.map f ys;
                                  val ws = List.map f d;
                              in tResolve xs zs (x::c) (x::ws) (e-1) end
                       | (x, FRAC(MULT(m, VAR(n)), MINUS(k, VAR(l)))) =>
                         if n = l
                         then let val f = replace (FRAC(MULT(x,k),PLUS(x,m))) (VAR(n));
                                  val zs = List.map f ys;
                                  val ws = List.map f d;
                              in tResolve xs zs (x::c) (x::ws) (e-1) end
                         else let val f = replace (FRAC(MULT(x,MINUS(k,VAR(l))),m)) (VAR(n));
                                  val zs = List.map f ys;
                                  val ws = List.map f d;
                              in tResolve xs zs (x::c) (x::ws) (e-1) end
                       | (x, FRAC(MULT(m, VAR(n)), k)) =>
                         let val f = replace (FRAC(MULT(x,k),m)) (VAR(n));
                             val zs = List.map f ys;
                             val ws = List.map f d;
                         in tResolve xs zs (x::c) (x::ws) (e-1) end
                       | (x, FRAC(k, MULT(m, VAR(n)))) =>
                         let val f = replace (FRAC(k,MULT(x,m))) (VAR(n));
                             val zx = List.map f xs;
                             val zy = List.map f ys;
                             val wx = List.map f c;
                             val wy = List.map f d;
                         in tResolve zx zy (x::wx) (x::wy) (e-1) end
                       | (x, FRAC(k, MINUS(m, VAR(n)))) =>
                         let val f = replace (FRAC(MINUS(MULT(x,m),k),x)) (VAR(n));
                             val zs = List.map f ys;
                             val ws = List.map f d;
                         in tResolve xs zs (x::c) (x::ws) (e-1) end
                       | (x, FRAC(k, MINUS(m, MULT(l, VAR(n))))) =>
                         let val f = replace (FRAC(MINUS(MULT(x,m),k),MULT(x,l))) (VAR(n));
                             val zs = List.map f ys;
                             val ws = List.map f d;
                         in tResolve xs zs (x::c) (x::ws) (e-1) end
                       | (x, FRAC(MINUS(MULT(m, VAR(n)), k), PLUS(q, MULT(p, VAR(l))))) =>
                         if n = l
                         then let val f = replace (FRAC(PLUS(MULT(x,q),k),MINUS(m,MULT(x,p)))) (VAR(n));
                                  val zs = List.map f ys;
                                  val ws = List.map f d;
                              in tResolve xs zs (x::c) (x::ws) (e-1) end
                         else tResolve xs ys (x::c) (x::d) (e-1)
                       | (x, MULT(k, VAR(n))) =>
                         let val f = replace (FRAC(x,k)) (VAR(n));
                             val zs = List.map f ys;
                             val ws = List.map f d;
                         in tResolve xs zs (x::c) (x::ws) (e-1) end
                       | (x, MULT(VAR(n), k)) =>
                         let val f = replace (FRAC(x,k)) (VAR(n));
                             val zs = List.map f ys;
                             val ws = List.map f d;
                         in tResolve xs zs (x::c) (x::ws) (e-1) end
                       | (x, MULT(PLUS(l, VAR(n)), k)) =>
                         let val f = replace (MINUS(FRAC(x,k),l)) (VAR(n));
                             val zs = List.map f ys;
                             val ws = List.map f d;
                         in tResolve xs zs (x::c) (x::ws) (e-1) end
                       | (x, MULT(k, PLUS(l, VAR(n)))) =>
                         let val f = replace (MINUS(FRAC(x,k),l)) (VAR(n));
                             val zs = List.map f ys;
                             val ws = List.map f d;
                         in tResolve xs zs (x::c) (x::ws) (e-1) end
                       | (x, MINUS(k, VAR(n))) =>
                         let val f = replace (MINUS(k,x)) (VAR(n));
                             val zs = List.map f ys;
                             val ws = List.map f d;
                         in tResolve xs zs (x::c) (x::ws) (e-1) end
                       | (x, MINUS(VAR(n), k)) =>
                         let val f = replace (PLUS(x,k)) (VAR(n));
                             val zs = List.map f ys;
                             val ws = List.map f d;
                         in tResolve xs zs (x::c) (x::ws) (e-1) end
                       | (x, MINUS(k, MULT(m, VAR(n)))) =>
                         let val f = replace (FRAC(MINUS(k,x),m)) (VAR(n));
                             val zs = List.map f ys;
                             val ws = List.map f d;
                         in tResolve xs zs (x::c) (x::ws) (e-1) end
                       | (x, MINUS(k, MULT(VAR(n), m))) =>
                         let val f = replace (FRAC(MINUS(k,x),m)) (VAR(n));
                             val zs = List.map f ys;
                             val ws = List.map f d;
                         in tResolve xs zs (x::c) (x::ws) (e-1) end
                       | (x, MINUS(FRAC(VAR(n), m), k)) =>
                         let val f = replace (MULT(PLUS(y,k),m)) (VAR(n));
                             val zs = List.map f ys;
                             val ws = List.map f d;
                         in tResolve xs zs (x::c) (x::ws) (e-1) end
                       | (x, PLUS(k, VAR(n))) =>
                         let val f = replace (MINUS(x,k)) (VAR(n));
                             val zs = List.map f ys;
                             val ws = List.map f d;
                         in tResolve xs zs (x::c) (x::ws) (e-1) end
                       | (x, PLUS(k, MULT(m, VAR(n)))) =>
                         let val f = replace (FRAC(MINUS(x,k),m)) (VAR(n));
                             val zs = List.map f ys;
                             val ws = List.map f d;
                         in tResolve xs zs (x::c) (x::ws) (e-1) end
                       | (x, PLUS(k, MULT(VAR(n), m))) =>
                         let val f = replace (FRAC(MINUS(x,k),m)) (VAR(n));
                             val zs = List.map f ys;
                             val ws = List.map f d;
                         in tResolve xs zs (x::c) (x::ws) (e-1) end
                       | (x, PLUS(k, FRAC(m, VAR(n)))) =>
                         let val f = replace (FRAC(m,MINUS(x,k))) (VAR(n));
                             val zs = List.map f ys;
                             val ws = List.map f d;
                         in tResolve xs zs (x::c) (x::ws) (e-1) end
                       | _ => tResolve xs ys (x::c) (x::d) (e-1))
               else (case (x,y) of
                         (VAR(n), VAR(m)) =>
                         let val fx = replace (VAR(n^m)) (VAR(n));
                             val fy = replace (VAR(n^m)) (VAR(m));
                             val zx = List.map fx xs;
                             val wx = List.map fx c;
                             val zy = List.map fy ys;
                             val wy = List.map fy d;
                         in tResolve zx zy ((VAR(n^m))::wx) ((VAR(n^m))::wy) (e-1) end
                       | (VAR(n), MINUS(NUM(1), VAR(m))) =>
                         let val fx = replace (VAR(n^m)) (VAR(n));
                             val fy = replace (MINUS(NUM(1),VAR(n^m))) (VAR(m));
                             val zx = List.map fx xs;
                             val wx = List.map fx c;
                             val zy = List.map fy ys;
                             val wy = List.map fy d;
                         in tResolve zx zy ((VAR(n^m))::wx) ((VAR(n^m))::wy) (e-1) end
                       | (MINUS(NUM(1), VAR(n)), VAR(m)) =>
                         let val fx = replace (MINUS(NUM(1),VAR(n^m))) (VAR(n));
                             val fy = replace (VAR(n^m)) (VAR(m));
                             val zx = List.map fx xs;
                             val wx = List.map fx c;
                             val zy = List.map fy ys;
                             val wy = List.map fy d;
                         in tResolve zx zy ((VAR(n^m))::wx) ((VAR(n^m))::wy) (e-1) end
                       | (MINUS(NUM(1), VAR(n)), MINUS(NUM(1), VAR(m))) =>
                         let val fx = replace (VAR(n^m)) (VAR(n));
                             val fy = replace (VAR(n^m)) (VAR(m));
                             val zx = List.map fx xs;
                             val wx = List.map fx c;
                             val zy = List.map fy ys;
                             val wy = List.map fy d;
                         in tResolve zx zy ((MINUS(NUM(1),VAR(n^m)))::wx) ((MINUS(NUM(1),VAR(n^m)))::wy) (e-1) end
                       | (PLUS(PLUS(k ,MULT(m, VAR(n))), VAR(l)), y) =>
                         if not (contains (VAR(n)) y)
                         then let val f = replace (FRAC(MINUS(PLUS(MINUS(NUM(0),k),y),VAR(l)),m)) (VAR(n));
                                  val zs = List.map f xs;
                                  val ws = List.map f c;
                              in tResolve zs ys (y::ws) (y::d) (e-1) end
                         else if not (contains (VAR(l)) y)
                         then let val f = replace (MINUS(y,PLUS(k,MULT(m,VAR(n))))) (VAR(l));
                                  val zs = List.map f xs;
                                  val ws = List.map f c;
                              in tResolve zs ys (y::ws) (y::d) (e-1) end
                         else tResolve xs ys (x::c) (y::d) (e-1)
                       | (x, PLUS(PLUS(k, MULT(m, VAR(n))), VAR(l))) =>
                         if not (contains (VAR(n)) x)
                         then let val f = replace (FRAC(MINUS(PLUS(MINUS(NUM(0),k),x),VAR(l)),m)) (VAR(n));
                                  val zs = List.map f ys;
                                  val ws = List.map f d;
                              in tResolve xs zs (x::c) (x::ws) (e-1) end
                         else if not (contains (VAR(l)) x)
                         then let val f = replace (MINUS(x,PLUS(k,MULT(m,VAR(n))))) (VAR(l));
                                  val zs = List.map f ys;
                                  val ws = List.map f d;
                              in tResolve xs zs (x::c) (x::ws) (e-1) end
                         else tResolve xs ys (x::c) (y::d) (e-1)
                       | (MINUS(MINUS(k, MULT(m, VAR(n))), VAR(l)), y) =>
                         if not (contains (VAR(n)) y)
                         then let val f = replace (FRAC(MINUS(MINUS(k,y),VAR(l)),m)) (VAR(n));
                                  val zs = List.map f xs;
                                  val ws = List.map f c;
                              in tResolve zs ys (y::ws) (y::d) (e-1) end
                         else if not (contains (VAR(l)) y)
                         then let val f = replace (MINUS(MINUS(k,MULT(m,VAR(n))),y)) (VAR(l));
                                  val zs = List.map f xs;
                                  val ws = List.map f c;
                              in tResolve zs ys (y::ws) (y::d) (e-1) end
                         else tResolve xs ys (x::c) (y::d) (e-1)
                       | (x, MINUS(MINUS(k, MULT(m, VAR(n))), VAR(l))) =>
                         if not (contains (VAR(n)) x)
                         then let val f = replace (FRAC(MINUS(MINUS(k,x),VAR(l)),m)) (VAR(n));
                                  val zs = List.map f ys;
                                  val ws = List.map f d;
                              in tResolve xs zs (x::c) (x::ws) (e-1) end
                         else if not (contains (VAR(l)) x)
                         then let val f = replace (MINUS(MINUS(k,MULT(m,VAR(n))),x)) (VAR(l));
                                  val zs = List.map f ys;
                                  val ws = List.map f d;
                              in tResolve xs zs (x::c) (x::ws) (e-1) end
                         else tResolve xs ys (x::c) (y::d) (e-1)
                       | (PLUS(MINUS(k, MULT(m, VAR(n))), VAR(l)), y) =>
                         if not (contains (VAR(n)) y)
                         then let val f = replace (FRAC(PLUS(MINUS(k,y),VAR(l)),m)) (VAR(n));
                                  val zs = List.map f xs;
                                  val ws = List.map f c;
                              in tResolve zs ys (y::ws) (y::d) (e-1) end
                         else if not (contains (VAR(l)) y)
                         then let val f = replace (MINUS(y,MINUS(k,MULT(m,VAR(n))))) (VAR(l));
                                  val zs = List.map f xs;
                                  val ws = List.map f c;
                              in tResolve zs ys (y::ws) (y::d) (e-1) end
                         else tResolve xs ys (x::c) (y::d) (e-1)
                       | (x, PLUS(MINUS(k, MULT(m, VAR(n))), VAR(l))) =>
                         if not (contains (VAR(n)) x)
                         then let val f = replace (FRAC(PLUS(MINUS(k,x),VAR(l)),m)) (VAR(n));
                                  val zs = List.map f ys;
                                  val ws = List.map f d;
                              in tResolve xs zs (x::c) (x::ws) (e-1) end
                         else if not (contains (VAR(l)) x)
                         then let val f = replace (MINUS(x,MINUS(k,MULT(m,VAR(n)))))(VAR(l));
                                  val zs = List.map f ys;
                                  val ws = List.map f d;
                              in tResolve xs zs (x::c) (x::ws) (e-1) end
                         else tResolve xs ys (x::c) (y::d) (e-1)
                       | (MINUS(PLUS(k, MULT(m, VAR(n))), VAR(l)), y) =>
                         if not (contains (VAR(n)) y)
                         then let val f = replace (FRAC(PLUS(MINUS(y,k),VAR(l)),m)) (VAR(n));
                                  val zs = List.map f xs;
                                  val ws = List.map f c;
                              in tResolve zs ys (y::ws) (y::d) (e-1) end
                         else if not (contains (VAR(l)) y)
                         then let val f = replace (MINUS(PLUS(k,MULT(m,VAR(n))),y)) (VAR(l));
                                  val zs = List.map f xs;
                                  val ws = List.map f c;
                              in tResolve zs ys (y::ws) (y::d) (e-1) end
                         else tResolve xs ys (x::c) (y::d) (e-1)
                       | (x, MINUS(PLUS(k, MULT(m, VAR(n))), VAR(l))) =>
                         if not (contains (VAR(n)) x)
                         then let val f = replace (FRAC(PLUS(MINUS(x,k),VAR(l)),m)) (VAR(n));
                                  val zs = List.map f ys;
                                  val ws = List.map f d;
                              in tResolve xs zs (x::c) (x::ws) (e-1) end
                         else if not (contains (VAR(l)) x)
                         then let val f = replace (MINUS(PLUS(k,MULT(m,VAR(n))),x)) (VAR(l));
                                  val zs = List.map f ys;
                                  val ws = List.map f d;
                              in tResolve xs zs (x::c) (x::ws) (e-1) end
                         else tResolve xs ys (x::c) (y::d) (e-1)
                       | (PLUS(PLUS(k, VAR(n)), VAR(l)), y) =>
                         if not (contains (VAR(n)) y)
                         then let val f = replace (MINUS(PLUS(MINUS(NUM(0),k),y),VAR(l))) (VAR(n));
                                  val zs = List.map f xs;
                                  val ws = List.map f c;
                              in tResolve zs ys (y::ws) (y::d) (e-1) end
                         else if not (contains (VAR(l)) y)
                         then let val f = replace (MINUS(y,PLUS(k,VAR(n)))) (VAR(l));
                                  val zs = List.map f xs;
                                  val ws = List.map f c;
                              in tResolve zs ys (y::ws) (y::d) (e-1) end
                         else tResolve xs ys (x::c) (y::d) (e-1)
                       | (x, PLUS(PLUS(k, VAR(n)), VAR(l))) =>
                         if not (contains (VAR(n)) x)
                         then let val f = replace (MINUS(PLUS(MINUS(NUM(0),k),x),VAR(l))) (VAR(n));
                                  val zs = List.map f ys;
                                  val ws = List.map f d;
                              in tResolve xs zs (x::c) (x::ws) (e-1) end
                         else if not (contains (VAR(l)) x)
                         then let val f = replace (MINUS(x,PLUS(k,VAR(n)))) (VAR(l));
                                  val zs = List.map f ys;
                                  val ws = List.map f d;
                              in tResolve xs zs (x::c) (x::ws) (e-1) end
                         else tResolve xs ys (x::c) (y::d) (e-1)
                       | (MINUS(MINUS(k, VAR(n)), VAR(l)), y) =>
                         if not (contains (VAR(n)) y)
                         then let val f = replace (MINUS(MINUS(k,y),VAR(l))) (VAR(n));
                                  val zs = List.map f xs;
                                  val ws = List.map f c;
                              in tResolve zs ys (y::ws) (y::d) (e-1) end
                         else if not (contains (VAR(l)) y)
                         then let val f = replace (MINUS(MINUS(k,VAR(n)),y)) (VAR(l));
                                  val zs = List.map f xs;
                                  val ws = List.map f c;
                              in tResolve zs ys (y::ws) (y::d) (e-1) end
                         else tResolve xs ys (x::c) (y::d) (e-1)
                       | (x, MINUS(MINUS(k, VAR(n)), VAR(l))) =>
                         if not (contains (VAR(n)) x)
                         then let val f = replace (MINUS(MINUS(k,x),VAR(l))) (VAR(n));
                                  val zs = List.map f ys;
                                  val ws = List.map f d;
                              in tResolve xs zs (x::c) (x::ws) (e-1) end
                         else if not (contains (VAR(l)) x)
                         then let val f = replace (MINUS(MINUS(k,VAR(n)),x)) (VAR(l));
                                  val zs = List.map f ys;
                                  val ws = List.map f d;
                              in tResolve xs zs (x::c) (x::ws) (e-1) end
                         else tResolve xs ys (x::c) (y::d) (e-1)
                       | (PLUS(MINUS(k, VAR(n)), VAR(l)), y) =>
                         if not (contains (VAR(n)) y)
                         then let val f = replace (PLUS(MINUS(k,y),VAR(l))) (VAR(n));
                                  val zs = List.map f xs;
                                  val ws = List.map f c;
                              in tResolve zs ys (y::ws) (y::d) (e-1) end
                         else if not (contains (VAR(l)) y)
                         then let val f = replace (MINUS(y,MINUS(k,VAR(n)))) (VAR(l));
                                  val zs = List.map f xs;
                                  val ws = List.map f c;
                              in tResolve zs ys (y::ws) (y::d) (e-1) end
                         else tResolve xs ys (x::c) (y::d) (e-1)
                       | (x, PLUS(MINUS(k, VAR(n)), VAR(l))) =>
                         if not (contains (VAR(n)) x)
                         then let val f = replace (PLUS(MINUS(k,x),VAR(l))) (VAR(n));
                                  val zs = List.map f ys;
                                  val ws = List.map f d;
                              in tResolve xs zs (x::c) (x::ws) (e-1) end
                         else if not (contains (VAR(l)) x)
                         then let val f = replace (MINUS(x,MINUS(k,VAR(n))))(VAR(l));
                                  val zs = List.map f ys;
                                  val ws = List.map f d;
                              in tResolve xs zs (x::c) (x::ws) (e-1) end
                         else tResolve xs ys (x::c) (y::d) (e-1)
                       | (MINUS(PLUS(k, VAR(n)), VAR(l)), y) =>
                         if not (contains (VAR(n)) y)
                         then let val f = replace (PLUS(MINUS(y,k),VAR(l))) (VAR(n));
                                  val zs = List.map f xs;
                                  val ws = List.map f c;
                              in tResolve zs ys (y::ws) (y::d) (e-1) end
                         else if not (contains (VAR(l)) y)
                         then let val f = replace (MINUS(PLUS(k,VAR(n)),y)) (VAR(l));
                                  val zs = List.map f xs;
                                  val ws = List.map f c;
                              in tResolve zs ys (y::ws) (y::d) (e-1) end
                         else tResolve xs ys (x::c) (y::d) (e-1)
                       | (x, MINUS(PLUS(k, VAR(n)), VAR(l))) =>
                         if not (contains (VAR(n)) x)
                         then let val f = replace (PLUS(MINUS(x,k),VAR(l))) (VAR(n));
                                  val zs = List.map f ys;
                                  val ws = List.map f d;
                              in tResolve xs zs (x::c) (x::ws) (e-1) end
                         else if not (contains (VAR(l)) x)
                         then let val f = replace (MINUS(PLUS(k,VAR(n)),x)) (VAR(l));
                                  val zs = List.map f ys;
                                  val ws = List.map f d;
                              in tResolve xs zs (x::c) (x::ws) (e-1) end
                         else tResolve xs ys (x::c) (y::d) (e-1)
                       | (MINUS(VAR(n), m), MINUS(k, VAR(l))) =>
                         if contains (VAR(l)) m orelse contains (VAR(n)) k
                         then tResolve xs ys (x::c) (y::d) (e-1)
                         else let val f = replace (PLUS(m,y)) (VAR(n));
                                  val fy = replace (MINUS(k,x)) (VAR(l));
                                  val zs = List.map f xs;
                                  val zy = List.map fy ys;
                                  val ws = List.map f c;
                                  val wy = List.map fy d;
                              in tResolve zs zy (y::ws) (x::wy) (e-1) end
                       | (MINUS(k, VAR(l)), MINUS(VAR(n), m)) =>
                         if contains (VAR(l)) m orelse contains (VAR(n)) k
                         then tResolve xs ys (x::c) (y::d) (e-1)
                         else let val f = replace (MINUS(k,y)) (VAR(l));
                                  val fy = replace (PLUS(m,x)) (VAR(n));
                                  val zs = List.map f xs;
                                  val zy = List.map fy ys;
                                  val ws = List.map f c;
                                  val wy = List.map fy d;
                              in tResolve zs zy (y::ws) (x::wy) (e-1) end
                       | (MINUS(VAR(n), m), MULT(l, VAR(k))) =>
                         if n = k
                         then let val f = replace (FRAC(m,MINUS(NUM(1),l))) (VAR(n));
                                  val zs = List.map f xs;
                                  val zy = List.map f ys;
                                  val ws = List.map f (x::c);
                                  val wy = List.map f (y::d);
                              in tResolve zs zy ws wy (e-1) end
                         else let val f = replace (PLUS(y,m)) (VAR(n));
                                  val zs = List.map f xs;
                                  val ws = List.map f c;
                              in tResolve zs ys (y::ws) (y::d) (e-1) end
                       | (MULT(l, VAR(k)), MINUS(VAR(n), m)) =>
                         if n = k
                         then let val f = replace (FRAC(m,MINUS(NUM(1),l))) (VAR(n));
                                  val zs = List.map f xs;
                                  val zy = List.map f ys;
                                  val ws = List.map f (x::c);
                                  val wy = List.map f (y::d);
                              in tResolve zs zy ws wy (e-1) end
                         else let val f = replace (PLUS(x,m)) (VAR(n));
                                  val zs = List.map f ys;
                                  val ws = List.map f d;
                              in tResolve xs zs (x::c) (x::ws) (e-1) end
                       | (VAR(n), y) =>
                         let val zs = List.map (replace y x) xs;
                             val ws = List.map (replace y x) c;
                         in tResolve zs ys (y::ws) (y::d) (e-1) end
                       | (x, VAR(n)) =>
                         let val zs = List.map (replace x y) ys;
                             val ws = List.map (replace x y) d;
                         in tResolve xs zs (x::c) (x::ws) (e-1) end
                       | (MINUS(VAR(n), m), k) =>
                         if contains (VAR(n)) k
                         then tResolve xs ys (x::c) (y::d) (e-1)
                         else let val f = replace (PLUS(k,m)) (VAR(n));
                                  val zs = List.map f xs;
                                  val ws = List.map f c;
                              in tResolve zs ys (y::ws) (y::d) (e-1) end
                       | (k, MINUS(VAR(n), m)) =>
                         if contains (VAR(n)) k
                         then tResolve xs ys (x::c) (y::d) (e-1)
                         else let val f = replace (PLUS(k,m)) (VAR(n));
                                  val zs = List.map f ys;
                                  val ws = List.map f d;
                              in tResolve xs zs (x::c) (x::ws) (e-1) end
                       | (k, MINUS(m, VAR(n))) =>
                         let val f = replace (MINUS(m,k)) (VAR(n));
                             val zs = List.map f ys;
                             val ws = List.map f d;
                         in tResolve xs zs (x::c) (x::ws) (e-1) end
                       | (MINUS(m, VAR(n)), k) =>
                         let val f = replace (MINUS(m,k)) (VAR(n));
                             val zs = List.map f xs;
                             val ws = List.map f c;
                         in tResolve zs ys (y::ws) (y::d) (e-1) end
                       | (k, PLUS(m, VAR(n))) =>
                         let val f = replace (MINUS(k,m)) (VAR(n));
                             val zs = List.map f ys;
                             val ws = List.map f d;
                         in tResolve xs zs (x::c) (x::ws) (e-1) end
                       | (PLUS(m, VAR(n)), k) =>
                         let val f = replace (MINUS(k,m)) (VAR(n));
                             val zs = List.map f xs;
                             val ws = List.map f c;
                         in tResolve zs ys (y::ws) (y::d) (e-1) end
                       | (MULT(q, VAR(l)), PLUS(m, MULT(n, VAR(k)))) =>
                         if l = k
                         then let val f = replace (FRAC(m,MINUS(q,n))) (VAR(l));
                                  val zx = List.map f xs;
                                  val zs = List.map f ys;
                                  val wx = List.map f (x::c);
                                  val ws = List.map f (y::d);
                              in tResolve zx zs wx ws (e-1) end
                         else tResolve xs ys (x::c) (y::d) (e-1)
                       | (PLUS(m, MULT(n, VAR(k))), MULT(q, VAR(l))) =>
                         if l = k
                         then let val f = replace (FRAC(m,MINUS(q,n))) (VAR(l));
                                  val zx = List.map f xs;
                                  val zs = List.map f ys;
                                  val wx = List.map f (x::c);
                                  val ws = List.map f (y::d);
                              in tResolve zx zs wx ws (e-1) end
                         else tResolve xs ys (x::c) (y::d) (e-1)
                       | (l, MINUS(MINUS(m, VAR(n)), k)) =>
                         let val f = replace (MINUS(MINUS(m,k),l)) (VAR(n));
                             val zs = List.map f ys;
                             val ws = List.map f d;
                         in tResolve xs zs (x::c) (x::ws) (e-1) end
                       | (MINUS(MINUS(m, VAR(n)), k), l) =>
                         let val f = replace (MINUS(MINUS(m,k),l)) (VAR(n));
                             val zs = List.map f xs;
                             val ws = List.map f c;
                         in tResolve zs ys (y::ws) (y::d) (e-1) end
                       | (k, PLUS(m, MULT(l, VAR(n)))) =>
                         let val f = replace (FRAC(MINUS(k,m),l)) (VAR(n));
                             val zs = List.map f ys;
                             val ws = List.map f d;
                         in tResolve xs zs (x::c) (x::ws) (e-1) end
                       | (PLUS(m, MULT(l, VAR(n))), k) =>
                         let val f = replace (FRAC(MINUS(k,m),l)) (VAR(n));
                             val zs = List.map f xs;
                             val ws = List.map f c;
                         in tResolve zs ys (y::ws) (y::d) (e-1) end
                       | (MINUS(MULT(l, VAR(n)), m), k) =>
                         let val f = replace (FRAC(PLUS(k,m),l)) (VAR(n));
                             val zs = List.map f xs;
                             val ws = List.map f c;
                         in tResolve zs ys (y::ws) (y::d) (e-1) end
                       | (k, MINUS(MULT(l, VAR(n)), m)) =>
                         let val f = replace (FRAC(PLUS(k,m),l)) (VAR(n));
                             val zs = List.map f ys;
                             val ws = List.map f d;
                         in tResolve xs zs (x::c) (x::ws) (e-1) end
                       | (k, MINUS(m, MULT(l, VAR(n)))) =>
                         let val f = replace (FRAC(MINUS(m,k),l)) (VAR(n));
                             val zs = List.map f ys;
                             val ws = List.map f d;
                         in tResolve xs zs (x::c) (x::ws) (e-1) end
                       | (MINUS(m, MULT(l, VAR(n))), k) =>
                         let val f = replace (FRAC(MINUS(m,k),l)) (VAR(n));
                             val zs = List.map f xs;
                             val ws = List.map f c;
                         in tResolve zs ys (y::ws) (y::d) (e-1) end
                       | (MULT(n, VAR(m)), MULT(k, VAR(l))) =>
                         let val f = replace (MULT(FRAC(k,n),VAR(l))) (VAR(m));
                             val zx = List.map f xs;
                             val wx = List.map f c;
                         in tResolve zx ys (y::wx) (y::d) (e-1) end
                       | (FRAC(n, m), FRAC(k, l)) =>
                         if l = m
                         then case (solveVar n k) of
                                  NONE => tResolve xs ys (x::c) (y::d) (e-1)
                                | SOME(a, b) => let val zx = List.map (replace b a) xs;
                                                    val wx = List.map (replace b a) (x::c);
                                                    val zy = List.map (replace b a) ys;
                                                    val wy = List.map (replace b a) (y::d);
                                                in tResolve zx zy wx wy (e-1) end
                         else tResolve xs ys (x::c) (y::d) (e-1)
                       | (MINUS(q, FRAC(n, m)), FRAC(k, l)) =>
                         if l = m
                         then case (solveVar k (MINUS(MULT(q,m),n))) of
                                  NONE => tResolve xs ys (x::c) (y::d) (e-1)
                                | SOME(a, b) => let val zx = List.map (replace b a) xs;
                                                    val wx = List.map (replace b a) (x::c);
                                                    val zy = List.map (replace b a) ys;
                                                    val wy = List.map (replace b a) (y::d);
                                                in tResolve zx zy wx wy (e-1) end
                         else tResolve xs ys (x::c) (y::d) (e-1)
                       | (FRAC(k, l), MINUS(q, FRAC(n, m))) =>
                         if l = m
                         then case (solveVar k (MINUS(MULT(q,m),n))) of
                                  NONE => tResolve xs ys (x::c) (y::d) (e-1)
                                | SOME(a, b) => let val zx = List.map (replace b a) xs;
                                                    val wx = List.map (replace b a) (x::c);
                                                    val zy = List.map (replace b a) ys;
                                                    val wy = List.map (replace b a) (y::d);
                                                in tResolve zx zy wx wy (e-1) end
                         else tResolve xs ys (x::c) (y::d) (e-1)
                       | (PLUS(q, FRAC(n, m)), FRAC(k, l)) =>
                         if l = m
                         then case (solveVar k (PLUS(n,MULT(q,m)))) of
                                  NONE => tResolve xs ys (x::c) (y::d) (e-1)
                                | SOME(a, b) => let val zx = List.map (replace b a) xs;
                                                    val wx = List.map (replace b a) (x::c);
                                                    val zy = List.map (replace b a) ys;
                                                    val wy = List.map (replace b a) (y::d);
                                                in tResolve zx zy wx wy (e-1) end
                         else tResolve xs ys (x::c) (y::d) (e-1)
                       | (FRAC(k, l), PLUS(q, FRAC(n, m))) =>
                         if l = m
                         then case (solveVar k (PLUS(n,MULT(q,m)))) of
                                  NONE => tResolve xs ys (x::c) (y::d) (e-1)
                                | SOME(a, b) => let val zx = List.map (replace b a) xs;
                                                    val wx = List.map (replace b a) (x::c);
                                                    val zy = List.map (replace b a) ys;
                                                    val wy = List.map (replace b a) (y::d);
                                                in tResolve zx zy wx wy (e-1) end
                         else tResolve xs ys (x::c) (y::d) (e-1)
                       | _ => case (solveVar x y) of
                                  NONE => tResolve xs ys (x::c) (y::d) (e-1)
                                | SOME(a, b) => let val zx = List.map (replace b a) xs;
                                                    val wx = List.map (replace b a) (x::c);
                                                    val zy = List.map (replace b a) ys;
                                                    val wy = List.map (replace b a) (y::d);
                                                in tResolve zx zy wx wy (e-1) end)
            end
          | tResolve _ _ _ _ _ = raise NumError;
        val (x, y) = tResolve a b [] [] n;
    in filterNum x y (countU a) (countU b) end

fun stringToHTML (id, "EMPTY", _) = (* NOT A STRING: This is an EMPTY area Diagram! *)
    (id, ("<div>\n"^
         "<svg width=\"220\" height=\"220\">\n"^
         "<rect x=\"10\" y=\"10\" width=\"200\" height=\"200\" style=\"fill:white;stroke-width:1;stroke:black\"/>\n"^
         "</svg>\n"^
         "</div>",
         220.0, 220.0))
  | stringToHTML (id, text, width) =
    let val mid = width * 5.0;
        val len = width * 10.0;
    in
        (id, ("<div>\n"^
              "<svg width=\""^(Real.toString len)^"\" height=\"18\" font-size=\"12px\">\n"^
              "<text text-anchor=\"middle\" transform=\"translate("^(Real.toString mid)^",13)\">"^text^"</text>\n"^
              "</svg>\n"^
              "</div>",
              len, 18.0))
    end;

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
    
fun wrap renderer c = Result.ok (List.flatmap renderer c)
                      handle e => Result.error [
                                     Diagnostic.create
                                         Diagnostic.ERROR
                                         ("Failed to render structure graph: "
                                          ^ (exnMessage e) ^ ".")
                                         []];

val drawArea = wrap drawArea;
val drawTable = wrap drawTable;
val drawTree = wrap drawTree;
val drawBayes = wrap drawBayes;

end;

