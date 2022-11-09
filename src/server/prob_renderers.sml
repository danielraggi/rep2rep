import "core.construction";

signature PROBRENDER = sig
    val drawArea: Construction.construction -> (string * (string*real*real)) list;
    val drawTable: Construction.construction -> (string * (string*real*real)) list;
    val drawTree: Construction.construction -> (string * (string*real*real)) list;
    val drawBayes: Construction.construction -> (string * (string*real*real)) list;
end;

structure ProbRender : PROBRENDER = struct

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

fun eventToString (SEVENT(x)) = x
  | eventToString (NEVENT(x)) = x

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
                | _ => raise NumError
           end
         | ("frac", [a, Construction.Source((id', "div")), b]) =>
           let val (a', y1, leftVal, leftLen) = parseWithValAndLength a;
               val (b', y2, rightVal, rightLen) = parseWithValAndLength b;
               val frac = (id, String.concat [leftVal, "/", rightVal], leftLen + rightLen);
               val divd = (id', "/", 1.5);
           in (FRAC(a', b'), frac::y1@(divd::y2)) end
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

fun numToString x =
    let fun round n = Real.roundDecimal n 6;
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
           => if k = b then c else MULT(a,b)
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
              | (MULT(m, VAR(n)), y) => SOME (VAR(n), FRAC(y, m))
              | (x, MULT(m, VAR(n))) => SOME (VAR(n), FRAC(x, m))
              | (MINUS(c, VAR(n)), y) => SOME (VAR(n), MINUS(c, y))
              | (x, MINUS(c, VAR(n))) => SOME (VAR(n), MINUS(c, x))
              | (MINUS(VAR(n), c), y) => SOME (VAR(n), PLUS(c, y))
              | (x, MINUS(VAR(n), c)) => SOME (VAR(n), PLUS(c, x))
              | _ => NONE;
        fun filterNum xs ys nx ny =
            let fun filterNum' ans [] [] = List.rev ans
                  | filterNum' ans (x::xs) (y::ys) =
                    if onlyNum x then filterNum' (x::ans) xs ys
                    else if onlyNum y then filterNum' (y::ans) xs ys
                    else if x = U then filterNum' (y::ans) xs ys
                    else if y = U then filterNum' (x::ans) xs ys
                    else if nx > ny then filterNum' (y::ans) xs ys
                    else filterNum' (x::ans) xs ys
                  | filterNum' _ _ _ = raise NumError;
            in filterNum' [] xs ys end;
        fun tResolve a b c d 0 = (List.revAppend (c, a), List.revAppend (d, b))
          | tResolve [] [] c d _ = (List.rev c, List.rev d)
          | tResolve (a::aas) (b::bbs) c d e =
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
                       | (VAR(n), y) =>
                         let val zs = List.map (replace y x) xs;
                             val ws = List.map (replace y x) c;
                         in tResolve zs ys (y::ws) (y::d) (e-1) end
                       | (x, VAR(n)) =>
                         let val zs = List.map (replace x y) ys;
                             val ws = List.map (replace x y) d;
                         in tResolve xs zs (x::c) (x::ws) (e-1) end
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

fun drawArea c =
    let fun parseArea (Construction.Source((id, typ))) =
            if String.isSubstring "empty" typ then (EMPTY, [(id, "EMPTY", 0.0)])
            else (case String.breakOn ":" typ of
                      (a, ":" ,_) => (LABEL(a), [(id, a, Real.fromInt (String.size a) + 0.5)])
                    | _ => raise AreaError)
          | parseArea (Construction.TCPair({token=(id, typ), constructor=(cname, ctyp)}, cons)) =
            (case (cname, cons) of
                 ("reverseTag", [tag]) =>
                 let fun overline x = "<tspan text-decoration=\"overline\">"^x^"</tspan>";
                 in case parseArea tag of
                        (LABEL(a), (id', l, s)::_) => (NLABEL(a), [(id', overline l, s)])
                      | _ => raise AreaError
                 end
               | ("cPoint", [x, y]) =>
                 let val (x', xHTML) = parseNum x;
                     val (y', yHTML) = parseNum y;
                 in case (xHTML, yHTML) of
                        ((_, s1, w1)::_, (_, s2, w2)::_) => (POINT(x', y'),
                                                             (id, "("^s1^","^s2^")", w1+w2) :: xHTML @ yHTML)
                      | _ => raise AreaError
                 end
               | ("cRect", [pt1, pt2]) =>
                 let val (p1, p1HTML) = parseArea pt1;
                     val (p2, p2HTML) = parseArea pt2;
                 in case (p1HTML, p2HTML) of
                        ((_, s1, w1)::_, (_, s2, w2)::_) => (RECT(p1, p2),
                                                             (id, s1^" - "^s2, w1+w2+0.5) :: p1HTML @ p2HTML)
                      | _ => raise AreaError
                 end
               | ("overlayRect", [area, rect, tag, shading]) =>
                 let val (a, areaHTML) = parseArea area;
                     val (r, rectHTML) = parseArea rect;
                     val (t, tagHTML) = parseArea tag;
                     val (s, shadingHTML) = parseShading shading;
                 in (OVERLAY(id, a, r, t, s), areaHTML @ rectHTML @ tagHTML @ shadingHTML) end
               | ("combine", [area1, area2]) =>
                 let val (a1, a1HTML) = parseArea area1;
                     val (a2, a2HTML) = parseArea area2;
                 in (COMBAREA(id, a1, a2), a1HTML @ a2HTML) end
               | _ => raise AreaError)
          | parseArea (Construction.Reference(_)) = raise AreaError
        fun convertArea EMPTY = (([],[],[],[]),[]) (* ((Events, points, shading, probs), HTML) *)
          | convertArea (LABEL(x)) = (([SEVENT(x)],[],[],[]),[])
          | convertArea (NLABEL(x)) = (([NEVENT(x)],[],[],[]),[])
          | convertArea (POINT(x,y)) = (([],[x,y],[],[]),[])
          | convertArea (RECT(p1, p2)) =
            let val ((_,pts1,_,_),_) = convertArea p1;
                val ((_,pts2,_,_),_) = convertArea p2;
            in (([], pts1 @ pts2, [], []), []) end
          | convertArea (OVERLAY(id, area, rect, tag, shading)) =
                let fun flipShading x = case x of
                                            BLUE => RED
                                          | RED => BLUE
                                          | _ => x;
                    val ((v1, p1, s1, w1), html) = convertArea area;
                    val (( _, p2,  _,  _),    _) = convertArea rect;
                    val ((v3,  _,  _,  _),    _) = convertArea tag;
                in if w1 = []
                   then case (hd v3) of
                            SEVENT _ => let val shading = [shading];
                                            val probs = case p2 of
                                                            (_::_::p::_) => [p, MINUS(NUM 1, p)]
                                                          | _ => raise AreaError;
                                        in ((    v3, p2, shading, probs),
                                            (id, v3, p2, shading, probs) :: html)
                                        end
                          | NEVENT _ => let val (points, probs) =
                                                case p2 of
                                                    (_::_::p::_) => ([MINUS(NUM 1, p), NUM 0, NUM 1, NUM 1],
                                                                     [MINUS(NUM 1, p), p])
                                                  | _ => raise AreaError;
                                          val shading = [flipShading shading];
                                      in ((    v3, points, shading, probs),
                                          (id, v3, points, shading, probs) :: html)
                                      end
                   else case (hd v1, hd v3) of
                            (SEVENT _, SEVENT _) =>
                            let val events = v1 @ v3;
                                val points = p1 @ p2;
                                val shading = s1 @ [shading];
                                val probs = case p2 of
                                                (_::_::_::p::_) => w1 @ [p, MINUS(NUM 1, p)]
                                              | _ => raise AreaError;
                            in ((    events, points, shading, probs),
                                (id, events, points, shading, probs) :: html)
                            end
                          | (SEVENT _, NEVENT _) =>
                            let val events = v1 @ v3;
                                val (points, probs) =
                                    case p2 of
                                        (p::_::_::q::_) => (p1 @ [p, MINUS(NUM 1, q), q, NUM 1],
                                                            w1 @ [MINUS(NUM 1, q), q])
                                     | _ => raise AreaError;
                                val shading = s1 @ [flipShading shading];
                            in ((    events, points, shading, probs),
                                (id, events, points, shading, probs) :: html)
                            end
                          | (NEVENT _, SEVENT _) =>
                            let val events = v1 @ v3;
                                val points = p1 @ [List.nth(p1,0),List.nth(p2,1),List.nth(p1,2),List.nth(p2,3)];
                                val shading = s1 @ [shading];
                                val probs = w1 @ [List.nth(p2,3),MINUS(NUM(1),List.nth(p2,3))];
                            in ((    events, points, shading, probs),
                                (id, events, points, shading, probs) :: html)
                            end
                          | (NEVENT _, NEVENT _) =>
                            let val events = v1 @ v3;
                                val points = p1 @ [List.nth(p1,0),MINUS(NUM(1),List.nth(p2,3)),List.nth(p1,2),NUM(1)];
                                val shading = s1 @ [flipShading shading];
                                val probs = w1 @ [MINUS(NUM(1),List.nth(p2,3)), List.nth(p2,3)];
                            in ((    events, points, shading, probs),
                                (id, events, points, shading, probs) :: html)
                            end
                end
            | convertArea (COMBAREA(id, x, y)) =
              let fun toRects [w0, _, w2, _, w4, _] =
                      let val z = NUM 0;
                          val i = NUM 1;
                      in [z, z, w0, i,
                          z, z, w0, w2,
                          w0, z, i, w4] end
                    | toRects _ = raise AreaError;
                  fun mergeShading PATTERN y = y
                    | mergeShading x PATTERN = x
                    | mergeShading WHITE y = y
                    | mergeShading x _ = x
                  fun extractNum [] y w = if List.length w = 6 then w else raise AreaError
                    | extractNum (x::xs) y w =
                      if xs = [] then w@[U, U, U, U]
                      else if List.length w = 6 then w
                      else case x of
                               SEVENT(a) => w@[U,U]
                             | NEVENT(a) => let val (pre, post) = List.split (w, 2);
                                            in pre @ [U, U] @ post end;
                  fun areaMerge x2 y2 a x3 y3 b =
                      let fun ff (b0::b1::b2::b3::b4::b5::_) =
                              let val z = VAR("z");
                                  val z' = MINUS(NUM(1), z);
                                  fun mktree xs = let val xs' = List.map simplify xs;
                                                  in (xs, (toRects xs)) end;
                              in case (b2, b4) of
                                     (U, _) => mktree [z, z',
                                                       MINUS(NUM(1), FRAC(MULT(b4, b1), z)),
                                                       FRAC(MULT(b4, b1), z),
                                                       MINUS(NUM(1), FRAC(MULT(b5, b1), z')),
                                                       FRAC(MULT(b5, b1), z')]
                                   | (_, U) => mktree [z, z',
                                                       FRAC(MULT(b2, b0), z),
                                                       MINUS(NUM(1), FRAC(MULT(b2, b0), z)),
                                                       FRAC(MULT(b3, b0), z'),
                                                       MINUS(NUM(1), FRAC(MULT(b3, b0), z'))]
                                   | (_, _) => let val y1 = PLUS(MULT(b2, b0), MULT(b4, b1));
                                                   val y2 = PLUS(MULT(b3, b0), MULT(b5, b1));
                                               in mktree [y1, y2,
                                                          FRAC(MULT(b2, b0), y1), FRAC(MULT(b4, b1), y1),
                                                          FRAC(MULT(b3, b0), y2), FRAC(MULT(b5, b1), y2)]
                                               end
                              end
                            | ff _ = raise AreaError;
                          fun merger [] [] _ _ c d e f = (List.rev c, List.rev d, e, f)
                            | merger (x::xxs::xs) (y::yys::ys) y2 y3 c d e f =
                              (case (x, y) of
                                   (U, U) => merger xs ys y2 y3 c d e f
                                 | (U, _) => let val (pre, post) = List.split (y3, 4);
                                             in merger xs ys
                                                       y2 post
                                                       (xxs::x::c) (yys::y::d)
                                                       (e@[U,U,U,U]) (f@pre) end
                                 | (_, U) => let val (pre, post) = List.split(y2, 4);
                                             in merger xs ys
                                                       post y3
                                                       (xxs::x::c) (yys::y::d)
                                                       (e@pre) (f@[U,U,U,U]) end
                                 | _ => let val (pre2, post2) = List.split(y2, 4);
                                            val (pre3, post3) = List.split(y3, 4);
                                        in merger xs ys
                                                  post2 post3
                                                  (xxs::x::c) (yys::y::d)
                                                  (e@pre2) (f@pre3) end)
                            | merger _ _ _ _ _ _ _ _ = raise AreaError;
                      in if eventToString (hd(x2)) = eventToString (hd(x3)) then
                             let val (c, d, e, f) = merger a b y2 y3 [] [] [] [];
                                 val x = if List.length x2 > List.length x3 then x2 else x3;
                             in (x, c, d, e, f) end
                         else if List.length x2 = List.length x3 andalso List.length x2 = 1
                         then let val z = VAR("z");
                                  val z' = MINUS(NUM(1), z);
                                  val x = VAR("x");
                                  val x' = MINUS(NUM(1), x);
                                  val xss = [z, z', x, x',
                                             FRAC(MINUS(hd(b),MULT(z, x)), z'),
                                             MINUS(NUM(1), FRAC(MINUS(hd(b), MULT(z, x)), z'))];
                              in (x2@x3, a, xss, y2@[U,U,U,U,U,U,U,U], (toRects xss)) end
                         else if List.length x2 = List.length x3 andalso List.length y2 = 8 then
                             let val (xss,yss) = ff b in (x2, a, xss, (y2@[U,U,U,U]), yss) end
                         else if List.length x2 = List.length x3 then
                             let val (xss,yss) = ff b in (x2, a, xss, y2, yss) end
                         else if List.length x3 > List.length x2 then
                             let val (xss,yss) = ff b in ((List.rev x3), a, xss, (y2@[U,U,U,U,U,U,U,U]), yss) end
                         else let val (xss,yss) = ff a in ((List.rev x2), xss, b, yss, (y3@[U,U,U,U,U,U,U,U])) end
                      end;
                  val ((x2,y2,z2,w2),n1) = convertArea x;
                  val ((x3,y3,z3,w3),n2) = convertArea y;
                  val (x, c, d, e, f) = areaMerge x2 y2 (extractNum x2 y2 w2) x3 y3 (extractNum x3 y3 w3);
                  val g = resolve (c@e) (d@f) (List.length c);
              in if List.length g = 12
                 then let val (pre, post) = List.split (g, 4);
                          val shading = mergeShading (hd z2) (hd z3);
                      in ((    x, post, [shading, PATTERN], pre),
                          (id, x, post, [shading, PATTERN], pre) :: n1 @ n2)
                      end
                 else let val pre = List.take (g, 6);
                          val rects = toRects pre;
                          val shading = [WHITE, BLUE, RED];
                      in ((    x, rects, shading, pre),
                          (id, x, rects, shading, pre) :: n1 @ n2)
                      end
              end;
        fun areaToHTML (id, events, b, fills, d) =
            let fun toNum x = if onlyNum x
                              then numToString (PLUS(NUM(30),MULT(NUM(200),x)))
                              else numToString (NUM(80));
                fun calcLen x y k n = if onlyNum x andalso onlyNum y
                                      then numToString (MULT(NUM(200),MINUS(x,y)))
                                      else if numToString k = numToString (NUM(0))
                                      then numToString (NUM(50))
                                      else numToString (MULT(n,NUM(50)));
                fun calcMid x n = if onlyNum x
                                  then numToString (PLUS(n,MULT(NUM(100),x)))
                                  else numToString (PLUS(NUM(25),n));
                fun calcLab n = if numToString n = numToString (NUM(0))
                                then numToString (NUM(15))
                                else numToString (NUM(245));
                fun shadeToString x = case x of
                                          BLUE => "#4d79ff"
                                        | RED => "#ff4d4d"
                                        | GREEN => "#39ac73"
                                        | WHITE => "white"
                                        | PATTERN => "url(#diagonalHatch)";
                fun toDocArea (events, y, fills, w) =
                    let fun rect (width, height) (trX, trY) fill =
                            String.concat ["<rect ",
                                           "width=\"", width, "\" ",
                                           "height=\"", height, "\" ",
                                           "transform=\"translate(", trX, ",", trY, ")\" ",
                                           "style=\"fill:", fill, ";stroke-width:1;stroke:black\" />"];
                        fun text (trX, trY) s =
                            String.concat ["<text ",
                                           "text-anchor=\"middle\" ",
                                           "transform=\"translate(", trX, ",", trY, ")\">",
                                           s,
                                           "</text>"];
                        val bg = rect ("200", "200") ("30", "30") "white";
                    in case (events, y, fills, w) of
                           ([event1], y0::y1::y2::y3::_, fill::_, w0::_) =>
                           let val width = calcLen y2 y0 y0 (NUM 3);
                               val height = calcLen y3 y1 y3 (NUM 1);
                               val translate = (toNum y0, toNum y1);
                               val mid = calcMid w0 (NUM 30);
                           in String.concat [
                                   bg, "\n",
                                   (rect (width, height) translate fill), "\n",
                                   id, (* We emit the token ID, not sure why... *)
                                   (text (mid, "10") event1), "\n",
                                   (text (mid, "25") (numToString w0)), "\n"
                               ] end
                         | ([event1, event2],
                            y0::y1::y2::y3::y4::y5::y6::y7::_,
                            fill1::fill2::_,
                            [w0, w1, w2, w3]) =>
                           let val width1 = calcLen y2 y0 y0 (NUM 3);
                               val height1 = calcLen y3 y1 y2 (NUM 3);
                               val translate1 = (toNum y0, toNum y1);
                               val width2 = calcLen y6 y4 y4 (NUM 3);
                               val height2 = calcLen y7 y5 y7 (NUM 3);
                               val translate2 = (toNum y4, toNum y5);
                               val mid = calcMid w0 (NUM 30);
                               val lab = calcLab y4;
                               fun mid2 v = calcMid w2 (NUM v);
                           in String.concat [
                                   bg, "\n",
                                   (rect (width1, height1) translate1 fill1), "\n",
                                   (rect (width2, height2) translate2 fill2), "\n",
                                   id,
                                   (text (mid, "10") event1), "\n",
                                   (text (mid, "25") (numToString w0)), "\n",
                                   (text (lab, (mid2 22)) event2), "\n",
                                   (text (lab, (mid2 38)) (numToString w2)), "\n"
                               ] end
                         | ([event1, event2],
                            y0::y1::y2::y3::y4::y5::y6::y7::y8::y9::y10::y11::_,
                            fill1::fill2::fill3::_,
                            w0::w1::w2::w3::w4::_) =>
                           let val width1 = calcLen y2 y0 y0 (NUM 1);
                               val height1 = calcLen y3 y1 y3 (NUM 1);
                               val translate1 = (toNum y4, toNum y5);
                               val width2 = calcLen y6 y4 y4 (NUM 1);
                               val height2 = calcLen y7 y5 y7 (NUM 1);
                               val translate2 = (toNum y4, toNum y5);
                               val width3 = calcLen y10 y8 y8 (NUM 3);
                               val height3 = calcLen y11 y9 y11 (NUM 2);
                               val translate3 = (toNum y8, toNum y9);
                               fun mid wi v = calcMid wi (NUM v);
                           in String.concat [
                                   bg, "\n",
                                   (rect (width1, height1) translate1 fill1), "\n",
                                   (rect (width2, height2) translate2 fill2), "\n",
                                   (rect (width3, height3) translate3 fill3), "\n",
                                   id,
                                   (text (mid w0 30, "10") event1), "\n",
                                   (text (mid w0 30, "25") (numToString w0)), "\n",
                                   (text ("15", mid w2 22) event2), "\n",
                                   (text ("15", mid w2 22) (numToString w2)), "\n",
                                   (text ("245", mid w4 22) event2), "\n",
                                   (text ("245", mid w4 38) (numToString w4)), "\n"
                               ] end
                         | _ => raise Match
                    end;
                val header = "<div>\n"^
                            "<svg width=\"300\" height=\"240\" background-color=\"white\" font-size=\"12px\">\n"^
                            "<pattern id=\"diagonalHatch\" patternUnits=\"userSpaceOnUse\" width=\"4\" height=\"4\">\n"^
                            "<path d=\"M-1,1 l2,-2 M0,4 l4,-4 M3,5 l2,-2\" style=\"stroke:#222; stroke-width:1\"/>\n"^
                            "</pattern>\n"
                val footer = "</svg>\n"^
                            "</div>\n"
                val content = toDocArea ((List.map eventToString events), b, (List.map shadeToString fills), d)
                in
                (id, ((header ^ content ^ footer), 300.0, 240.0))
            end;
        val (rects, strings) = parseArea c;
        val (_, areas) = convertArea rects;
    in (List.map areaToHTML areas) @ (List.map stringToHTML strings) end;

fun drawTable c =
    let fun parseTable (Construction.Source((id, typ))) =
            (case String.breakOn ":" typ of
                 (a,":",_) => (NAME(a),[(id, a, Real.fromInt (String.size a) + 0.5)])
               | _ => raise TableError)
          | parseTable (Construction.TCPair({token=(id, typ), constructor=(cname, ctyp)}, cons)) =
            (case (cname, cons) of
                 ("buildOne", [name, numExp]) =>
                 let val (var, varHTML) = parseTable name;
                     val (prob, probHTML) = parseNum numExp;
                 in (ONEWAY(id, var, prob), varHTML @ probHTML) end
               | ("buildTwo", [oneDim, twoDim, numExp]) =>
                 let val (t1, t1HTML) = parseTable oneDim;
                     val (t2, t2HTML) = parseTable twoDim;
                     val (conj, conjHTML) = parseNum numExp;
                 in (TWOWAY(id, t1, t2, conj), t1HTML @ t2HTML @ conjHTML) end
               | ("combine", [table1, table2]) =>
                 let val (x1,y1) = parseTable table1;
                     val (x2,y2) = parseTable table2;
                 in (COMB(id, x1, x2), y1@y2) end
               | ("notName", [name]) =>
                 let fun overline x = "<tspan text-decoration=\"overline\">"^x^"</tspan>";
                 in case parseTable name of
                        (NAME a, [(id, label, size)]) => (NNAME(a), [(id, overline label, size)])
                      | _ => raise TableError
                 end
               | _ => raise TableError)
          | parseTable _ = raise TableError;
        fun convertTable (NAME(x)) = (([SEVENT(x)],[]), [])
          | convertTable (NNAME(x)) = (([NEVENT(x)],[]), [])
          | convertTable (ONEWAY(id, var, prob)) =
            let val ((v, _), _) = convertTable var;
                val probs = case v of
                            [SEVENT(_)] => [prob, MINUS(NUM(1), prob)]
                          | [NEVENT(_)] => [MINUS(NUM(1), prob), prob]
                          | _ => raise TableError;
            in ((v, probs), [(id, v, probs)]) end
          | convertTable (TWOWAY(id, t1, t2, conj)) =
            let val ((v1, probs1), tabs1) = convertTable t1;
                val ((v2, probs2), tabs2) = convertTable t2;
                val vs = v1 @ v2;
                val conjs = case (v1, v2, probs1, probs2) of
                            ([SEVENT _], [SEVENT _], [p1, _], [p2, _])
                            => [conj, MINUS(p1, conj), MINUS(p2, conj),
                                MINUS(PLUS(NUM(1), MINUS(conj, p2)), p1)]
                          | ([SEVENT _], [NEVENT _], [p1, _], [_, p2])
                            => [MINUS(p1, conj), conj,
                                MINUS(PLUS(NUM(1), MINUS(conj, p2)), p1), MINUS(p2, conj)]
                          | ([NEVENT _], [SEVENT _], [_, p1], [p2, _])
                            => [MINUS(p2, conj), MINUS(PLUS(NUM(1), MINUS(conj, p2)), p1),
                                conj, MINUS(p1, conj)]
                          | ([NEVENT _], [NEVENT _], [_, p1], [_, p2])
                            => [MINUS(PLUS(NUM(1), MINUS(conj, p2)), p1), MINUS(p2, conj),
                                MINUS(p1, conj), conj]
                          | _ => raise TableError;
                val probs = probs1 @ probs2 @ conjs;
            in ((vs, probs), (id, vs, probs)::(tabs1 @ tabs2)) end
          | convertTable (COMB(id, t1, t2)) =
            let fun tableMerge [] _ _ _ = raise TableError
                  | tableMerge _ _ [] _ = raise TableError
                  | tableMerge (v1 as var1::_) probs1 (v2 as var2::_) probs2 =
                    let
                        (* Transpose:
                                 c   d      =>       a   b
                               ---------          ---------
                            a |  e   f         c |   e   g
                            b |  g   h         d |   f   h
                         *)
                        fun transpose [a, b, c, d, e, f, g, h] = [c, d, a, b, e, g, f, h]
                          | transpose _ = raise TableError;
                        val l1 = List.length v1;
                        val l2 = List.length v2;
                        val s1 = eventToString var1;
                        val s2 = eventToString var2;
                    in if l1 = l2 then (if s1 = s2 then (v1, probs1, probs2)
                                        else if l1 = 1 then ((v1 @ v2),
                                                             (probs1 @ [U,U,U,U,U,U]),
                                                             ([U,U] @ probs2 @ [U,U,U,U]))
                                        else (v1, probs1, transpose probs2))
                       else if l1 > l2 then (if s1 = s2 then (v1, probs2, (probs2 @ [U,U,U,U,U,U]))
                                             else (v1, probs1, ([U,U] @ probs2 @ [U,U,U,U])))
                       else if s1 = s2 then (v2, (probs1 @ [U,U,U,U,U,U]), probs2)
                       else (v2, ([U,U] @ probs1 @ [U,U,U,U]), probs2)
                    end;
                val ((v1, probs1), tabs1) = convertTable t2;
                val ((v2, probs2), tabs2) = convertTable t1;
                val (vs, b, c) = tableMerge v1 probs1 v2 probs2;
                val probs = resolve b c (List.length b);
            in ((vs, probs), (id, vs, probs)::tabs1 @ tabs2) end;
        fun tableToHTML (id, events, probabilities) =
            let fun toDocTable (events, probabilities) =
                    let fun th s = "<th style=\"background-color:lightgrey; "
                                   ^ "border:1px solid; height:25px; width:70px;\">"
                                   ^ s ^ "</th>";
                        fun td s = "<td style=\"border: 1px solid;\">" ^ s ^ "</td>";
                        fun tr cells = "<tr>" ^ (String.concat cells) ^ "</tr>";
                        fun overline x = "<span style=\"text-decoration:overline\">" ^ x ^ "</span>";
                    in case (events, probabilities) of
                           ([v], [p, p']) =>
                           (String.concatWith "\n" [
                                 tr [th "", th "Total"],
                                 tr [th v, td p],
                                 tr [th (overline v), td p'],
                                 tr [th "Total", td "1"]
                             ], 140.0)
                         | ([v1, v2], [p1, p1', p2, p2', p12, p12', p1'2, p1'2']) =>
                           (String.concatWith "\n" [
                                 tr [th "", th v2, th (overline v2), th "Total"],
                                 tr [th v1, td p12, td p12', td p1],
                                 tr [th (overline v1), td p1'2, td p1'2', td p1'],
                                 tr [th "Total", td p2, td p2', td "1"]
                           ], 280.0)
                         | _ => raise TableError
                    end;
                val header = "<div style=\"padding: 10px;\">\n"
                             ^ "<table style=\"text-align:center; "
                             ^ "border-collapse:collapse; "
                             ^ "background-color:white; "
                             ^ "font-size:12px;\">\n";
                val footer = "\n</table>\n</div>\n";
                val (content, width) = toDocTable ((List.map eventToString events),
                                                   (List.map numToString probabilities));
            in (id, ((header ^ content ^ footer), width + 20.0, 120.0)) end;
        val (tabs, strings) = parseTable c;
        val (_, tables) = convertTable tabs;
    in (List.map tableToHTML tables) @ (List.map stringToHTML strings) end;

fun drawTree x =
    let fun parseTree (Construction.Source((id, typ))) =
                (case String.breakOn ":" typ of
                    (subtype, ":", _) => (BRANCH(subtype), [(id, subtype, Real.fromInt (String.size subtype) + 0.5)])
                  | _ => raise TreeError)
          | parseTree (Construction.TCPair({token=(id, typ), constructor=(cname, ctyp)}, cons)) =
            (case (cname, cons) of
                ("construct", [label, value]) =>
                let val (l, lHTML) = parseTree label;
                    val (v, vHTML) = parseNum value;
                in (TREE(id, l, v), lHTML @ vHTML) end
              | ("addBranch", [tree, label, value]) =>
                let val (t, tHTML) = parseTree tree;
                    val (l, lHTML) = parseTree label;
                    val (v, vHTML) = parseNum value;
                in (ADD(id, t, l, v), tHTML @ lHTML @ vHTML) end
              | ("resolve", [tree1, tree2]) =>
                let val (t1, t1HTML) = parseTree tree1;
                    val (t2, t2HTML) = parseTree tree2;
                in (RESOLVE(id, t1, t2), t1HTML @ t2HTML) end
              | ("notLabel", [label]) =>
                let fun overline x = "<tspan text-decoration=\"overline\">"^x^"</tspan>";
                in case (parseTree label) of
                       (BRANCH(l), (id', lab, size)::_) => (NBRANCH(l), [(id', overline lab, size)])
                     | _ => raise TreeError
                end
              | _ =>  raise TreeError)
          | parseTree (Construction.Reference(_)) = raise TreeError
        fun convertTree (BRANCH(x)) = (([SEVENT(x)], []), [])
          | convertTree (NBRANCH(x)) = (([NEVENT(x)], []), [])
          | convertTree (TREE(id, label, prob)) =
            let val ((vars, _), _) = convertTree label;
                val prob' = MINUS(NUM 1, prob);
            in case vars of
                   [NEVENT _] => ((vars, [prob', prob]), [(id, vars, [prob', prob])])
                 | [SEVENT _] => ((vars, [prob, prob']), [(id, vars, [prob, prob'])])
                 | _ => raise TreeError
            end
          | convertTree (ADD(id, tree, label, prob)) =
            let val ((v1, ps), tHTML) = convertTree tree;
                val ((v2, _), _) = convertTree label;
                val vars = v1 @ v2;
                val prob' = MINUS(NUM 1, prob);
            in case (v1, v2) of
                   ([SEVENT _], [SEVENT _]) => let val ps = ps @ [prob, prob', U, U];
                                               in ((vars, ps), (id, vars, ps)::tHTML) end
                 | ([SEVENT _], [NEVENT _]) => let val ps = ps @ [prob', prob, U, U];
                                               in ((vars, ps), (id, vars, ps)::tHTML) end
                 | ([NEVENT _], [SEVENT _]) => let val ps = ps @ [U, U, prob, prob'];
                                               in ((vars, ps), (id, vars, ps)::tHTML) end
                 | ([NEVENT _], [NEVENT _]) => let val ps = ps @ [U, U, prob', prob];
                                               in ((vars, ps), (id, vars, ps)::tHTML) end
                 | _ => raise TreeError
            end
          | convertTree (RESOLVE(id, tree1, tree2)) =
            let fun treeMerge x2 y2 x3 y3 =
                    let fun f (b0::b1::b2::b3::b4::b5::_) =
                            let val z = VAR "z";
                                val z' = MINUS(NUM 1, z);
                            in case (b2, b4) of
                                   (U, _) => List.map simplify [
                                                z, z', MINUS(NUM(1), FRAC(MULT(b4, b1), z)),
                                                FRAC(MULT(b4, b1), z),
                                                MINUS(NUM(1), FRAC(MULT(b5, b1), z')),
                                                FRAC(MULT(b5, b1), z')]
                                 | (_, U) => List.map simplify [
                                                z, z', FRAC(MULT(b2, b0), z),
                                                MINUS(NUM(1), FRAC(MULT(b2, b0), z)),
                                                FRAC(MULT(b3, b0), z'),
                                                MINUS(NUM(1), FRAC(MULT(b3, b0), z'))]
                                 | (_, _) => List.map simplify [
                                                PLUS(MULT(b2, b0), MULT(b4, b1)),
                                                PLUS(MULT(b3, b0), MULT(b5, b1)),
                                                FRAC(MULT(b2, b0), PLUS(MULT(b2, b0), MULT(b4, b1))),
                                                FRAC(MULT(b4, b1), PLUS(MULT(b2, b0), MULT(b4, b1))),
                                                FRAC(MULT(b3, b0), PLUS(MULT(b3, b0), MULT(b5, b1))),
                                                FRAC(MULT(b5, b1), PLUS(MULT(b3, b0), MULT(b5, b1)))]
                            end
                          | f _ = raise TreeError;
                        fun countNum xs =
                            let fun f ans [] = ans
                                  | f ans (x::xs) = if onlyNum x then f (ans + 1) xs else f ans xs;
                            in f 0 xs end;
                        val l1 = List.length x2;
                        val l2 = List.length x3;
                        val s1 = eventToString (hd x2);
                        val s2 = eventToString (hd x3);
                        val (z, z') = (VAR  "z", MINUS(NUM 1, VAR "z"));
                        val (y, y') = (VAR  "y", MINUS(NUM 1, VAR "y"));
                    in if l1 = l2
                       then (if s1 = s2
                             then (x2, y2, y3)
                             else (if l1 = 1
                                   then let val probs = [z, z', y, y',
                                                         FRAC(MINUS(hd y3, MULT(z, y)), z'),
                                                         MINUS(NUM 1, FRAC(MINUS(hd y3, MULT(z, y)), z'))];
                                        in (x2 @ x3, y2 @ [U, U, U, U], probs) end
                                   else (if (countNum y2) > (countNum y3)
                                         then (x2, y2, f y3)
                                         else (x3, f y2, y3))))
                       else (if l1 > l2
                             then (if s1 = s2
                                   then (x2, y2, y3 @ [U, U, U, U])
                                   else (List.rev x2, f y2, y3 @ [U, U, U, U]))
                             else (if s1 = s2
                                   then (x3, y2 @ [U, U, U, U], y3)
                                   else (List.rev x3, y2 @ [U, U, U, U], f y3)))
                    end;
                val ((v1, p1), html1) = convertTree tree2;
                val ((v2, p2), html2) = convertTree tree1;
                val (vars, b, c) = treeMerge v1 p1 v2 p2;
                val probs = resolve b c (List.length b);
            in ((vars, probs), (id, vars, probs) :: html1 @ html2) end;
        fun treeToHTML (id, a, b) =
            let fun addJoint (y0::y1::y2::y3::y4::y5::_) =
                    (case (y2, y4) of
                         (U, U) => [U, U, U, U]
                       | (U, _) => [U, U, MULT(y4, y1), MULT(y5, y1)]
                       | (_, U) => [MULT(y2, y0), MULT(y3, y0), U, U]
                       | (_, _) => [MULT(y2, y0), MULT(y3, y0), MULT(y4, y1), MULT(y5, y1)])
                  | addJoint [p, p'] = []
                  | addJoint _ = raise TreeError;
                fun overline x = "<tspan text-decoration=\"overline\">" ^ x ^ "</tspan>";
                fun svg (height, width) = String.concat [
                        "<svg height=\"", height, "\" width=\"", width, "\" font-size=\"12px\">\n"
                    ];
                fun text s (x, y) mid rotate = String.concat [
                        "<text ",
                        (if mid then "text-anchor=\"middle\" " else ""),
                        "transform=\"translate(", x, ",", y, ")",
                        (case rotate of
                             NONE => ""
                          | SOME rot => " rotate(" ^ rot ^ ")"),
                        "\">",
                        "P(", s, ")",
                        "</text>\n"
                    ];
                fun line (x1, y1) (x2, y2) = String.concat [
                        "<line ",
                        "x1=\"", x1, "\" y1=\"", y1, "\" ",
                        "x2=\"", x2, "\" y2=\"", y2, "\" ",
                        "style=\"stroke:black;stroke-width:1\"/>\n"
                    ];
                fun toDocTree ([x], [p, p']) =
                    (String.concat [
                          svg ("90", "120"),
                          text x ("85", "27") false NONE,
                          text (overline x) ("85", "83") false NONE,
                          text p ("40", "35") true (SOME "-17"),
                          text p' ("40", "74") true (SOME "17"),
                          line ("0", "50") ("80", "25"),
                          line ("0", "50") ("80", "75")
                      ], 90.0, 120.0)
                  | toDocTree ([x1, x2], [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9]) =
                    (String.concat [
                          svg ("110", "350"),
                          text x1 ("85", "27") false NONE,
                          text (overline x1) ("85", "83") false NONE,
                          text (x1 ^ "&cap;" ^ x2 ^ " = " ^ y6) ("225", "10") false NONE,
                          text (x1 ^ "&cap;" ^ (overline x2) ^ " = " ^ y7) ("225", "38") false NONE,
                          text ((overline x1) ^ "&cap;" ^ x2 ^ " = " ^ y8) ("225", "70") false NONE,
                          text ((overline x1) ^ "&cap;" ^ (overline x2) ^ " = " ^ y9) ("225", "98") false NONE,
                          text y0 ("40", "35") true (SOME "-17"),
                          text y1 ("40", "74") true (SOME "17"),
                          text y2 ("170", "11") true (SOME "-7"),
                          text y3 ("170", "37") true (SOME "7"),
                          text y4 ("170", "71") true (SOME "-7"),
                          text y5 ("170", "97") true (SOME "7"),
                          line ("0", "50") ("80", "25"),
                          line ("0", "50") ("80", "75"),
                          line ("120", "20") ("220", "7"),
                          line ("120", "20") ("220", "33"),
                          line ("120", "80") ("220", "67"),
                          line ("120", "80") ("220", "93")
                      ], 110.0, 350.0)
                  | toDocTree _ = raise TreeError;
                val b = b @ (addJoint b);
                val header = "<div style=\"padding:5px;\">\n";
                val footer = "</svg>\n</div>";
                val (content, h, w) = toDocTree ((List.map eventToString a), (List.map numToString b))
            in (id, ((header ^ content ^ footer), w + 10.0, h + 10.0)) end;
        val (tr, strings) = parseTree x;
        val (_, trees) = convertTree tr;
    in (List.map treeToHTML trees) @ (List.map stringToHTML strings) end

fun drawBayes c =
    let fun parseOp (Construction.Source((id, "inter"))) = [(id, "&cap;", 1.5)]
          | parseOp (Construction.Source((id, "union"))) = [(id, "&cup;", 1.5)]
          | parseOp _ = raise BayesError;
        fun parseEvent (Construction.Source((id, typ))) =
            (case String.breakOn ":" typ of
                 (label, ":", _) => [(id, label, Real.fromInt (String.size label) + 0.5)]
               | _ => raise NumError)
          | parseEvent (Construction.TCPair({token=(id, typ), constructor=(cname, ctyp)}, cons)) =
            (case (cname, cons) of
                 ("complement", [bar, event]) =>
                 let val html = parseEvent event;
                     fun overline x = "<tspan text-decoration=\"overline\">"^x^"</tspan>"
                 in case bar of
                        Construction.Source((barId, "overline")) =>
                        (case html of
                             ((_, evt, width)::_) => (id, overline evt, width)::(barId, "-", 1.5)::html
                           | _ => raise BayesError)
                      | _ => raise BayesError
                 end
               | ("makeCond", [event1, event2]) =>
                 let val html1 = parseEvent event1;
                     val html2 = parseEvent event2;
                 in case (html1, html2) of
                        ((_, e1, w1)::_, (_, e2, w2)::_) => (id, e1 ^ "|" ^ e2, w1+w2) :: html1 @ html2
                      | _ => raise BayesError
                 end
               | ("infix", [event1, setop, event2]) =>
                 let val html1 = parseEvent event1;
                     val html2 = parseEvent event2;
                     val htmlOp = parseOp setop;
                 in case (html1, htmlOp, html2) of
                        ((_, e1, w1)::_, (_, ops, w3)::_, (_, e2, w2)::_) =>
                        (id, e1 ^ ops ^ e2, w1 + w2 + w3 - 1.0):: html1 @ html2 @ htmlOp
                      | _ => raise BayesError
                 end
               | _ => raise BayesError)
          | parseEvent (Construction.Reference(_)) = raise BayesError
        fun parseBayes (c as Construction.TCPair({token=(id, typ), constructor=(cname, ctyp)}, cons)) =
            (case (cname, cons) of
                 ("makeEqn", [events, value]) =>
                 let val html1 = parseEvent events;
                     val (_, html2) = parseNum value;
                 in case (html1, html2) of
                        ((_, ev, w1)::_, (_, pr, w2)::_) =>
                        let val eqn = "Pr(" ^ ev ^ ") = " ^ pr;
                            val width = w1 + w2 + 3.0;
                        in (id, eqn, width) :: html1 @ html2 end
                      | _ => raise BayesError
                 end
               | ("addEqn", [eqn, system]) =>
                 let val html1 = parseBayes eqn;
                     val html2 = parseBayes system;
                 in case (html1, html2) of
                        ((_, eq1, w1)::_, (_, eq2, w2)::_) =>
                        let val eqns = eq1 ^ ", " ^ eq2;
                            val width = w1 + w2 - 1.0;
                        in (id, eqns, width) :: html1 @ html2 end
                      | _ => raise BayesError
                 end
               | _ => parseEvent c)
          | parseBayes c = parseEvent c;
    in List.map stringToHTML (parseBayes c) end;

end;
