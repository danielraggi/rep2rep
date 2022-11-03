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
    in case cname of
           "infixOp" =>
           (case inputs of
                [a, Construction.Source((id', op_)), b] =>
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
              | _ => raise NumError)
         | "frac" =>
           (case inputs of
                [a, Construction.Source((id', "div")), b] =>
                let val (a', y1, leftVal, leftLen) = parseWithValAndLength a;
                    val (b', y2, rightVal, rightLen) = parseWithValAndLength b;
                    val frac = (id, String.concat [leftVal, "/", rightVal], leftLen + rightLen);
                    val divd = (id', "/", 1.5);
                in (FRAC(a', b'), frac::y1@(divd::y2)) end
              | _ => raise NumError)
         | "multiply" =>
           (case inputs of
                [a, b] =>
                let val (a', y1, leftVal, leftLen) = parseWithValAndLength a;
                    val (b', y2, rightVal, rightLen) = parseWithValAndLength b;
                    val prod = (id, String.concat [leftVal, "*", rightVal], leftLen + rightLen);
                in (MULT(a', b'), prod::y1@y2) end
              | _ => raise NumError)
         | _ => raise NumError
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
               | (R a, V b) => if Real.== (a,0.0) andalso String.substring(b,0,1) = "~"
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
                    | R x => Real.toString (round x)
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
    let val a = simplify x
        val b = simplify y
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
        val (x,y) = tResolve a b [] [] n;
    in filterNum x y (countU a) (countU b) end

fun stringToHTML (id, "EMPTY", _) = (* NOT A STRING: This is an EMPTY area Diagram! *)
    (id, ("<div>\n"^
         "<svg width=\"200\" height=\"200\">\n"^
         "<rect width=\"200\" height=\"200\" style=\"fill:white;stroke-width:1;stroke:black\"/>\n"^
         "</svg>\n"^
         "</div>",
         200.0, 200.0))
  | stringToHTML (id, text, width) =
    let val mid = width * 5.0;
        val len = width * 10.0;
    in
        (id, ("<div>\n"^
              "<svg width=\""^(Real.toString len)^"\" height=\"18\" font-size=\"12px\">\n"^
              "<rect width=\""^(Real.toString len)^"\" height=\"18\" fill=\"#d9d9d9\"/>\n"^
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
               | ("cPoint", [c1, c2]) =>
                 let val (x1, z1) = parseNum c1;
                     val (x2, z2) = parseNum c2;
                 in case (z1, z2) of
                        ((_, l1, s1)::_, (_, l2, s2)::_) => (POINT(x1,x2), (id, "("^l1^","^l2^")", s1+s2)::z1@z2)
                      | _ => raise AreaError
                 end
               | ("cRect", [p1, p2]) =>
                 let val (x1,y1) = parseArea p1;
                     val (x2,y2) = parseArea p2;
                 in case (y1, y2) of
                        ((_, l1, s1)::_, (_, l2, s2)::_) => (RECT(x1,x2), (id, l1^" - "^l2, s1+s2+0.5)::y1@y2)
                      | _ => raise AreaError
                 end
               | ("overlayRect", [a, r, t, s]) =>
                 let val (x1,y1) = parseArea a;
                     val (x2,y2) = parseArea r;
                     val (x3,y3) = parseArea t;
                     val (x4,y4) = parseShading s;
                 in (OVERLAY(id, x1, x2, x3, x4), y1@y2@y3@y4) end
               | ("combine", [a1, a2]) =>
                 let val (x1,y1) = parseArea a1;
                     val (x2,y2) = parseArea a2;
                 in (COMBAREA(id, x1, x2), y1@y2) end
               | _ => raise AreaError)
          | parseArea (Construction.Reference(_)) = raise AreaError
        fun convertArea EMPTY = (([],[],[],[]),[])
          | convertArea (LABEL(x)) = (([SEVENT(x)],[],[],[]),[])
          | convertArea (NLABEL(x)) = (([NEVENT(x)],[],[],[]),[])
          | convertArea (POINT(x,y)) = (([],[x,y],[],[]),[])
          | convertArea (RECT(x,y)) =
            let val ((_,y2,_,_),_) = convertArea x;
                val ((_,y3,_,_),_) = convertArea y;
            in (([], y2@y3, [], []), []) end
          | convertArea (OVERLAY(m,x,y,z,w)) =
                let fun flipShading x = case x of
                                            BLUE => RED
                                          | RED => BLUE
                                          | _ => x;
                    val ((x1,y1,z1,w1),n) = convertArea x;
                    val ((_,y2,_,_),_) = convertArea y;
                    val ((x3,_,_,_),_) = convertArea z;
                in if w1 = []
                   then case (hd(x3)) of
                            SEVENT(a) => ((x3,y2,[w],[List.nth(y2,2),MINUS(NUM(1),List.nth(y2,2))]),(m,x3,y2,[w],[List.nth(y2,2),MINUS(NUM(1),List.nth(y2,2))])::n)
                          | NEVENT(a) => ((x3,[MINUS(NUM(1),List.nth(y2,2)),NUM(0),NUM(1),NUM(1)],[(flipShading w)],[MINUS(NUM(1),List.nth(y2,2)),List.nth(y2,2)]),(m,x3,[MINUS(NUM(1),List.nth(y2,2)),NUM(0),NUM(1),NUM(1)],[(flipShading w)],[MINUS(NUM(1),List.nth(y2,2)),List.nth(y2,2)])::n)
                   else case (hd(x1),hd(x3)) of
                            (SEVENT(a),SEVENT(b)) => ((x1@x3,y1@y2,z1@[w],w1@[List.nth(y2,3),MINUS(NUM(1),List.nth(y2,3))]),(m,x1@x3,y1@y2,z1@[w],w1@[List.nth(y2,3),MINUS(NUM(1),List.nth(y2,3))])::n)
                          | (SEVENT(a),NEVENT(b)) => ((x1@x3,y1@[List.nth(y2,0),MINUS(NUM(1),List.nth(y2,3)),List.nth(y2,2),NUM(1)],z1@[(flipShading w)],w1@[MINUS(NUM(1),List.nth(y2,3)), List.nth(y2,3)]),(m,x1@x3,y1@[List.nth(y2,0),MINUS(NUM(1),List.nth(y2,3)),List.nth(y2,2),NUM(1)],z1@[(flipShading w)],w1@[MINUS(NUM(1),List.nth(y2,3)),List.nth(y2,3)])::n)
                          | (NEVENT(a),SEVENT(b)) => ((x1@x3,y1@[List.nth(y1,0),List.nth(y2,1),List.nth(y1,2),List.nth(y2,3)],z1@[w],w1@[List.nth(y2,3),MINUS(NUM(1),List.nth(y2,3))]),(m,x1@x3,y1@[List.nth(y1,0),List.nth(y2,1),List.nth(y1,2),List.nth(y2,3)],z1@[w],w1@[List.nth(y2,3),MINUS(NUM(1),List.nth(y2,3))])::n)
                          | (NEVENT(a),NEVENT(b)) => ((x1@x3,y1@[List.nth(y1,0),MINUS(NUM(1),List.nth(y2,3)),List.nth(y1,2),NUM(1)],z1@[(flipShading w)],w1@[MINUS(NUM(1),List.nth(y2,3)), List.nth(y2,3)]),(m,x1@x3,y1@[List.nth(y1,0),MINUS(NUM(1),List.nth(y2,3)),List.nth(y1,2),NUM(1)],z1@[(flipShading w)],w1@[MINUS(NUM(1),List.nth(y2,3)),List.nth(y2,3)])::n)
                end
            | convertArea (COMBAREA(m,x,y)) =
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
                      let fun ff b =
                              if List.nth(b,2) = U
                              then let val xs = [
                                           VAR("z"),MINUS(NUM(1),VAR("z")),
                                           MINUS(NUM(1),FRAC(MULT(List.nth(b,4), List.nth(b,1)), VAR("z"))),
                                           FRAC(MULT(List.nth(b,4), List.nth(b,1)), VAR("z")),
                                           MINUS(NUM(1),FRAC(MULT(List.nth(b,5),List.nth(b,1)), MINUS(NUM(1), VAR("z")))),
                                           FRAC(MULT(List.nth(b,5),List.nth(b,1)), MINUS(NUM(1), VAR("z")))];
                                       val xss = List.map simplify xs;
                                   in (xss, (toRects xss)) end
                              else if List.nth(b,4) = U
                              then let val xs = [VAR("z"), MINUS(NUM(1),VAR("z")),
                                                 FRAC(MULT(List.nth(b,2),List.nth(b,0)),VAR("z")),
                                                 MINUS(NUM(1),FRAC(MULT(List.nth(b,2),List.nth(b,0)),VAR("z"))),
                                                 FRAC(MULT(List.nth(b,3),List.nth(b,0)),MINUS(NUM(1),VAR("z"))),
                                                 MINUS(NUM(1),FRAC(MULT(List.nth(b,3),List.nth(b,0)),
                                                                   MINUS(NUM(1),VAR("z"))))];
                                       val xss = List.map simplify xs;
                                   in (xss, (toRects xss)) end
                              else let val xs = [
                                           PLUS(MULT(List.nth(b,2),List.nth(b,0)),
                                                MULT(List.nth(b,4),List.nth(b,1))),
                                           PLUS(MULT(List.nth(b,3),List.nth(b,0)),
                                                MULT(List.nth(b,5),List.nth(b,1))),
                                           FRAC(MULT(List.nth(b,2), List.nth(b,0)),
                                                PLUS(MULT(List.nth(b,2),List.nth(b,0)),
                                                     MULT(List.nth(b,4),List.nth(b,1)))),
                                           FRAC(MULT(List.nth(b,4), List.nth(b,1)),
                                                PLUS(MULT(List.nth(b,2),List.nth(b,0)),
                                                     MULT(List.nth(b,4),List.nth(b,1)))),
                                           FRAC(MULT(List.nth(b,3),List.nth(b,0)),
                                                PLUS(MULT(List.nth(b,3),List.nth(b,0)),
                                                     MULT(List.nth(b,5),List.nth(b,1)))),
                                           FRAC(MULT(List.nth(b,5),List.nth(b,1)),
                                                PLUS(MULT(List.nth(b,3),List.nth(b,0)),
                                                     MULT(List.nth(b,5),List.nth(b,1))))];
                                       val xss = List.map simplify xs;
                                   in (xss, (toRects xss)) end
                      in if eventToString (hd(x2)) = eventToString (hd(x3)) then
                             let fun merger [] [] _ _ c d e f = (List.rev c, List.rev d, e, f)
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
                                 val (c,d,e,f) = merger a b y2 y3 [] [] [] [];
                             in if List.length x2 > List.length x3 then (x2, c, d, e, f)
                                else (x3, c, d, e, f)
                             end
                         else if List.length x2 = List.length x3 andalso List.length x2 = 1
                         then let val xss = [VAR("z"),MINUS(NUM(1),VAR("z")),
                                             VAR("x"), MINUS(NUM(1),VAR("x")),
                                             FRAC(MINUS(hd(b),MULT(VAR("z"),VAR("x"))),
                                                  MINUS(NUM(1),VAR("z"))),
                                             MINUS(NUM(1),FRAC(MINUS(hd(b), MULT(VAR("z"),VAR("x"))),
                                                               MINUS(NUM(1),VAR("z"))))];
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
                 then ((x, (List.drop(g,4)),
                        [(mergeShading (hd(z2)) (hd(z3))),PATTERN],
                        List.take(g,4)),
                       (m, x, (List.drop(g,4)),
                        [(mergeShading (hd(z2)) (hd(z3))),PATTERN],
                        List.take(g,4))::n1@n2)
                 else ((x, (toRects (List.take(g,6))),
                        [WHITE,BLUE,RED],
                        List.take(g,6)),
                       (m, x, (toRects (List.take(g,6))),
                        [WHITE,BLUE,RED],
                        List.take(g,6))::n1@n2)
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
                 let val (x1,y1) = parseTable name;
                     val (x2,y2) = parseNum numExp;
                 in (ONEWAY(id, x1, x2), y1@y2) end
               | ("buildTwo", [oneDim, twoDim, numExp]) =>
                 let val (x1,y1) = parseTable oneDim;
                     val (x2,y2) = parseTable twoDim;
                     val (x3,y3) = parseNum numExp;
                 in (TWOWAY(id, x1, x2, x3), y1@y2@y3) end
               | ("combine", [table1, table2]) =>
                 let val (x1,y1) = parseTable table1;
                     val (x2,y2) = parseTable table2;
                 in (COMB(id, x1, x2), y1@y2) end
               | ("notName", [name]) =>
                 let fun overline x = "<tspan text-decoration=\"overline\">"^x^"</tspan>";
                 in case parseTable name of
                        (NAME a, (id, label, size)::_) => (NNAME(a), [(id, overline label, size)])
                      | _ => raise TableError
                 end
               | _ => raise TableError)
          | parseTable _ = raise TableError;
        fun convertTable (NAME(x)) = (([SEVENT(x)],[]), [])
          | convertTable (NNAME(x)) = (([NEVENT(x)],[]), [])
          | convertTable (ONEWAY(id, x, y)) =
            let val ((x2, _), _) = convertTable x;
                val w = case x2 of
                            SEVENT(a)::_ => [y,MINUS(NUM(1),y)]
                          | NEVENT(a)::_ => [MINUS(NUM(1),y), y]
                          | _ => raise TableError;
            in ((x2, w), [(id, x2, w)]) end
          | convertTable (TWOWAY(id, x, y, z)) =
            let val ((x2, y2), n1) = convertTable x;
                val ((x3, y3), n2) = convertTable y;
                val x23 = x2 @ x3;
                val w = case (x2, x3, y2, y3) of
                            ((SEVENT a)::_, (SEVENT b)::_, y2_0::_, y3_0::_)
                            => [z, MINUS(y2_0, z), MINUS(y3_0, z),
                                MINUS(PLUS(NUM(1), MINUS(z, y3_0)), y2_0)]
                          | ((SEVENT a)::_, (NEVENT b)::_, y2_0::_, _::y3_1::_)
                            => [MINUS(y2_0, z), z, MINUS(PLUS(NUM(1), MINUS(z, y3_1)), y2_0),
                                MINUS(y3_1, z)]
                          | ((NEVENT a)::_, (SEVENT b)::_, _::y2_1::_, y3_0::_)
                            => [MINUS(y3_0, z), MINUS(PLUS(NUM(1), MINUS(z, y3_0)), y2_1),
                                z, MINUS(y2_1, z)]
                          | ((NEVENT a)::_, (NEVENT b)::_, _::y2_1::_, _::y3_1::_)
                            => [MINUS(PLUS(NUM(1), MINUS(z, y3_1)), y2_1),
                                MINUS(y3_1, z), MINUS(y2_1, z), z]
                          | _ => raise TableError;
                val y23w = y2 @ y3 @ w;
            in ((x23, y23w), (id, x23, y23w)::(n1 @ n2)) end
          | convertTable (COMB(id, t1, t2)) =
            let fun tableMerge [] _ _ _ = raise TableError
                  | tableMerge _ _ [] _ = raise TableError
                  | tableMerge (x2 as x2_0::_) y2 (x3 as x3_0::_) y3 =
                    let
                        (* Transpose:
                                 c   d      =>       a   b
                               ---------          ---------
                            a |  e   f         c |   e   g
                            b |  g   h         d |   f   h
                         *)
                        fun transpose [a, b, c, d, e, f, g, h] = [c, d, a, b, e, g, f, h]
                          | transpose _ = raise TableError;
                        val l2 = List.length x2;
                        val l3 = List.length x3;
                        val s2 = eventToString x2_0;
                        val s3 = eventToString x3_0;
                    in if l2 = l3 then (if s2 = s3 then (x2, y2, y3)
                                        else if l2 = 1 then ((x2@x3),
                                                             (y2@[U,U,U,U,U,U]),
                                                             ([U,U]@y3@[U,U,U,U]))
                                        else (x2, y2, transpose y3))
                       else if l2 > l3 then (if s2 = s3 then (x2, y2, (y3@[U,U,U,U,U,U]))
                                             else (x2, y2, ([U,U]@y3@[U,U,U,U])))
                       else if s2 = s3 then (x3, (y2@[U,U,U,U,U,U]), y3)
                       else (x3, ([U,U]@y2@[U,U,U,U]), y3)
                    end;
                val ((x2, y2), n1) = convertTable t2;
                val ((x3, y3), n2) = convertTable t1;
                val (a, b, c) = tableMerge x2 y2 x3 y3;
                val t = resolve b c (List.length b);
            in ((a, t), (id, a, t)::n1@n2) end;
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
                val header = "<div>\n"
                             ^ "<table style=\"text-align:center; "
                             ^ "border-collapse:collapse; "
                             ^ "background-color:white; "
                             ^ "font-size:12px;\">\n";
                val footer = "\n</table>\n</div>\n";
                val (content, width) = toDocTable ((List.map eventToString events),
                                                   (List.map numToString probabilities));
            in (id, ((header ^ content ^ footer), width, 100.0)) end;
        val (tabs, strings) = parseTable c;
        val (_, tables) = convertTable tabs;
    in (List.map tableToHTML tables) @ (List.map stringToHTML strings) end;

fun drawTree x =
    let fun parseTree (Construction.Source(x)) =
                (case String.breakOn ":" (#2 x) of
                    (a,":",_) => (BRANCH(a),[(#1 x,a,Real.fromInt(String.size a)+0.5)])
                    |_ => raise TreeError)
            |parseTree (Construction.TCPair(x,y)) =
                if (#1 (#constructor x)) = "construct" then
                    let val (x1,y1) = parseTree (hd(y))
                        val (x2,y2) = parseNum (List.last(y)) in
                        (TREE((#1 (#token x)),x1,x2), y1@y2)
                    end
                else if (#1 (#constructor x)) = "addBranch" then
                    let val (x1,y1) = parseTree (hd(y))
                        val (x2,y2) = parseTree (List.nth(y,1))
                        val (x3,y3) = parseNum (List.last(y)) in
                        (ADD((#1 (#token x)),x1,x2,x3),y1@y2@y3)
                    end
                else if (#1 (#constructor x)) = "resolve" then
                    let val (x1,y1) = parseTree (hd(y))
                        val (x2,y2) = parseTree (List.last(y)) in
                        (RESOLVE((#1 (#token x)),x1,x2),y1@y2)
                    end
                else if (#1 (#constructor x)) = "notLabel" then
                    (case (parseTree (hd(y))) of
                        (BRANCH(a),b) => (NBRANCH(a),[((#1 (hd(b))),"<tspan text-decoration=\"overline\">"^(#2 (hd(b)))^"</tspan>",(#3 (hd(b))))])
                        |_ => raise TreeError)
                else raise TreeError
            |parseTree (Construction.Reference(x)) = raise TreeError
        fun convertTree (BRANCH(x)) = (([SEVENT(x)],[]), [])
            |convertTree (NBRANCH(x)) = (([NEVENT(x)],[]), [])
            |convertTree (TREE(m,x,y)) =
                let val ((x2,_),_) = convertTree x in
                    case (hd(x2)) of
                    NEVENT(a) => ((x2,[MINUS(NUM(1),y),y]),[(m,x2,[MINUS(NUM(1),y),y])])
                    |SEVENT(a) => ((x2,[y,MINUS(NUM(1),y)]),[(m,x2,[y,MINUS(NUM(1),y)])])
                end
            |convertTree (ADD(m,x,y,z)) =
                let val ((x2,y2),n) = convertTree x
                    val ((x3,_),_) = convertTree y in
                    case ((hd(x2)), (hd(x3))) of
                        (SEVENT(a),SEVENT(b)) => ((x2@x3, y2@[z,MINUS(NUM(1),z),U,U]),(m,x2@x3,y2@[z,MINUS(NUM(1),z),U,U])::n)
                        |(SEVENT(a),NEVENT(b)) => ((x2@x3, y2@[MINUS(NUM(1),z),z,U,U]),(m,x2@x3,y2@[MINUS(NUM(1),z),z,U,U])::n)
                        |(NEVENT(a),SEVENT(b)) => ((x2@x3, y2@[U,U,z,MINUS(NUM(1),z)]),(m,x2@x3,y2@[U,U,z,MINUS(NUM(1),z)])::n)
                        |(NEVENT(a),NEVENT(b)) => ((x2@x3, y2@[U,U,MINUS(NUM(1),z),z]),(m,x2@x3,y2@[U,U,MINUS(NUM(1),z),z])::n)
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
                val (content,h,w) = toDocTree ((List.map eventToString a),(List.map numToString b))
                in
                (m, ((header^content^footer),w,h))
            end
        val (a,strings) = parseTree x
        val (_,trees) = convertTree a
    in (List.map treeToHTML trees) @ (List.map stringToHTML strings) end

fun drawBayes x =
    let fun parseEvent (Construction.Source(x)) =
                (case String.breakOn ":" (#2 x) of
                (a,":",_) => [(#1 x,a,Real.fromInt(String.size a)+0.5)]
                | _ => raise NumError)
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
                                if (#1 (#constructor x)) = "makeCond" then
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
                if (#1 (#constructor x)) = "makeEqn" then
                    let val y1 = parseEvent (hd(y))
                        val (_,y2) = parseNum (List.last y)
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
        val a = parseBayes x
        in
        List.map stringToHTML a
    end;

end;
