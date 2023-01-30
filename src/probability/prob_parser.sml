import "core.construction";
(* Require numExp constructs *)
import "server.prob_renderers";

signature PROBPARSER = sig
  datatype probEvent = EVENT of string
                      |NOT of probEvent
                      |INTER of probEvent * probEvent
                      |UNION of probEvent * probEvent
                      |COND of probEvent * probEvent
                      |E
  val produce_construction: string -> Construction.construction
end;

structure ProbParser : PROBPARSER = struct

datatype probEvent = EVENT of string
                    |NOT of probEvent
                    |INTER of probEvent * probEvent
                    |UNION of probEvent * probEvent
                    |COND of probEvent * probEvent
                    |E

datatype probSys = EQN of probEvent * ProbNum.numExp
                  |SYS of probSys * probSys

datatype probQ =  PROBS of probSys
                  |PROOF of probSys * probEvent
exception ParseError;

fun parse x =
  let fun parse_event x n =
        if(Char.isAlpha(String.sub(x,n))) then (n+1, EVENT(String.substring(x,n,1)))
        else raise ParseError
      and parse_not x n =
        if(String.substring(x,n,1) = "!") then
          let val (j,e) = parse_event x (n+1) in (j, NOT(e)) end
        else parse_event x n
      and parse_infix x n =
        let val (j,e) = parse_not x n in
          if(String.size(x) >= 1+j andalso String.substring(x,j,1) = "*") then let val (j2,e2) = parse_infix x (j+1) in (j2,INTER(e,e2)) end
        else if(String.size(x) >= 1+j andalso String.substring(x,j,1) = "+") then let val (j2,e2) = parse_infix x (j+1) in (j2,UNION(e,e2)) end
        else (j,e)
        end
      and parse_cond x n =
        let val (j,e) = parse_infix x n in
            if(String.size(x) >= 1+j andalso String.substring(x,j,1) = "|") then let val (j2,e2) = parse_cond x (j+1) in (j2,COND(e,e2)) end
          else (j,e)
        end
      fun parse_var x n =
        (case String.breakOn ")" (String.substring(x,n,(String.size x) - n)) of
          (a,")",_) => if Char.isAlpha(String.sub(a,0)) then (n+(String.size a),ProbNum.VAR(a))
                       else if String.substring(a,0,2) = "0." then (n+(String.size a),ProbNum.DEC(a))
                       else (case Int.fromString a of
                              NONE => raise ParseError
                              |SOME x => (n+(String.size a),ProbNum.NUM x))
          |_ => raise ParseError)
      and parse_plus x n =
        let val (j,e) = parse_var x n in
          if(String.size(x) >= 1+j andalso String.substring(x,j,1) = "+") then let val (j2,e2) = parse_plus x (j+1) in (j2,ProbNum.PLUS(e,e2)) end
          else if(String.size(x) >= 1+j andalso String.substring(x,j,1) = "-") then let val (j2,e2) = parse_plus x (j+1) in (j2,ProbNum.MINUS(e,e2)) end
          else (j,e)
        end
      and parse_mult x n =
        let val (j,e) = parse_plus x n in
            if(String.size(x) >= 1+j andalso String.substring(x,j,1) = "*") then let val (j2,e2) = parse_mult x (j+1) in (j2,ProbNum.MULT(e,e2)) end
            else if(String.size(x) >= 1+j andalso String.substring(x,j,1) = "/") then let val (j2,e2) = parse_mult x (j+1) in (j2,ProbNum.FRAC(e,e2)) end
            else (j,e)
        end
      fun parse_eqn_num x n s =
          if(String.substring(x,(n+s),1) = ")" orelse String.substring(x,(n+s),1) = "]") then parse_mult (String.substring(x,n,s+1)) 0
          else parse_eqn_num x n (s+1)
      and parse_eqn_event x n s =
        if(String.substring(x,s,1) = ",") then
          let val (j,e) = parse_cond (String.substring(x,n,(s-n))) 0
              val (j2,e2) = parse_eqn_num x (s+1) 0 in
              (s+2+j2, EQN(e, e2))
          end
        else parse_eqn_event x n (s+1)
      and parse_sys x n =
        if(String.substring(x,n,1) = "(") then
          let val (j,e) = parse_eqn_event x (n+1) (n+1) in
            if(String.size(x) > j andalso String.substring(x,j,1) = ";") then
              let val (j2,e2) = parse_sys x (j+1) in (j2, SYS(e, e2)) end
            else (j,e)
          end
        else raise ParseError
      and parse_proof x n =
        if String.substring(x,0,1) = "(" then
          let val (j,e) = parse_sys x n in
              (j,PROBS(e))
          end
        else let val (j,e) = parse_cond x (n+1)
                 val (j2,e2) = parse_sys x (j+2) in
                  (j2, PROOF(e2, e))
             end
    val (j,e) = parse_proof x 0 in
      e
    end;

fun produce_construction e =
  let fun constructEvent n (EVENT(x)) = (Construction.Source("t"^n, x^":event"), x)
          |constructEvent n (NOT(x)) =
            let val (x2, x3) = constructEvent (n^"2") x in
                (Construction.TCPair({constructor = ("complement", (["event"], "event")), token = ("t"^n, "not-"^x3^":event")}, [x2]), "not-"^x3)
            end
          |constructEvent n (INTER(x,y)) =
            let val (x2, x3) = constructEvent (n^"1") x
                val (y2, y3) = constructEvent (n^"3") y in
                (Construction.TCPair({constructor=("infix", (["event","bin","event"],"event")), token=("t"^n,x3^"-inter-"^y3^":event")}, x2::Construction.Source("t"^n^"2", "inter")::[y2]), x3^"-inter-"^y3)
            end
          |constructEvent n (UNION(x,y)) =
            let val (x2, x3) = constructEvent (n^"1") x
                val (y2, y3) = constructEvent (n^"3") y in
                (Construction.TCPair({constructor=("infix", (["event","bin","event"],"event")), token=("t"^n,x3^"-union-"^y3^":event")}, x2::Construction.Source("t"^n^"2", "union")::[y2]), x3^"-union-"^y3)
            end
          |constructEvent n (COND(x,y)) =
            let val (x2, x3) = constructEvent (n^"1") x
                val (y2, y3) = constructEvent (n^"3") y in
                (Construction.TCPair({constructor=("makeCond", (["event","event"],"condEvent")), token=("t"^n,x3^"-cond-"^y3^":condEvent")}, x2::[y2]), x3^"-cond-"^y3)
            end
          |constructEvent n E = raise ParseError
      fun constructNum n (ProbNum.U) = (Construction.Source("t"^n, "numExp"), "")
          |constructNum n (ProbNum.NUM(x)) = (Construction.Source("t"^n, (Int.toString x)^":numeral"), (Int.toString x))
          |constructNum n (ProbNum.DEC(x)) = (Construction.Source("t"^n, x^":numeral"), x)
          |constructNum n (ProbNum.VAR(x)) = (Construction.Source("t"^n, x^":var"), x)
          |constructNum n (ProbNum.PLUS(x,y)) =
            let val (x2, x3) = constructNum (n^"1") x
                val (y2, y3) = constructNum (n^"3") y in
                (Construction.TCPair({constructor=("infixOp", (["numExp","binOp","numExp"],"numExp")), token=("t"^n,x3^"-plus-"^y3^":numExp")}, x2::Construction.Source("t"^n^"2", "plus")::[y2]), x3^"-plus-"^y3)
            end
          |constructNum n (ProbNum.MINUS(x,y)) =
            let val (x2, x3) = constructNum (n^"1") x
                val (y2, y3) = constructNum (n^"3") y in
                (Construction.TCPair({constructor=("infixOp", (["numExp","binOp","numExp"],"numExp")), token=("t"^n,x3^"-minus-"^y3^":numExp")}, x2::Construction.Source("t"^n^"2", "minus")::[y2]), x3^"-minus-"^y3)
            end
          |constructNum n (ProbNum.FRAC(x,y)) =
            let val (x2, x3) = constructNum (n^"1") x
                val (y2, y3) = constructNum (n^"3") y in
                (Construction.TCPair({constructor=("infixOp", (["numExp","binOp","numExp"],"numExp")), token=("t"^n,x3^"-div-"^y3^":numExp")}, x2::Construction.Source("t"^n^"2", "div")::[y2]), x3^"-div-"^y3)
            end
          |constructNum n (ProbNum.MULT(x,y)) =
            let val (x2, x3) = constructNum (n^"1") x
                val (y2, y3) = constructNum (n^"2") y in
                (Construction.TCPair({constructor=("implicitMult", (["numExp","numExp"],"numExp")), token=("t"^n,x3^"-mult-"^y3^":numExp")}, x2::[y2]), x3^"-mult-"^y3)
            end
      fun construct n (SYS(x,y)) =
            let val (x2, x3) = construct (n^"1") x
                val (y2, y3) = construct (n^"2") y in
                (Construction.TCPair({constructor=("addEqn", (["probEqn","probSys"],"probSys")), token=("t"^n,x3^"-and-"^y3^":probSys")}, x2::[y2]), x3^"-and-"^y3)
            end
          |construct n (EQN(x,y)) =
            let val (x2, x3) = constructEvent (n^"1") x
                val (y2, y3) = constructNum (n^"2") y in
                (Construction.TCPair({constructor=("makeEqn", (["events","numExp"],"probEqn")), token=("t"^n,x3^"-is-"^y3^":probEqn")}, x2::[y2]), x3^"-is-"^y3)
            end
      fun constructQ n (PROOF(x,y)) =
            let val (x2, x3) = construct (n^"1") x
                val (y2, y3) = constructEvent (n^"2") y in
                (Construction.TCPair({constructor=("calculate", (["probSys","events"],"probSys")), token=("t"^n,x3^"-calc-"^y3^":probSys")}, [x2,y2]), x3^"-calc-"^y3)
            end
          |constructQ n (PROBS(x)) = construct ("") x
      val (x,y) = constructQ "" (parse e) in
      x
  end

end;
