import "capullo.construction";

signature PROPAGATION =
sig
  type 'a evaluator =
      {name : string,
       seedFun : CSpace.token -> 'a option,
       propagator : CSpace.constructor -> (('a option) list -> 'a option) option};

  val evaluate : 'a evaluator -> Construction.construction -> 'a option;
  val mkISEvaluator : (CSpace.constructor -> real option) -> real evaluator;
end;

structure Propagation : PROPAGATION =
struct
  type 'a evaluator =
      {name : string,
       seedFun : CSpace.token -> 'a option,
       propagator : CSpace.constructor -> (('a option) list -> 'a option) option};


  fun evaluate E (Construction.Source t) = #seedFun E t
    | evaluate E (Construction.Loop t) = #seedFun E t
    | evaluate E (Construction.TCPair (tc,cs)) =
        (case (#seedFun E) (#token tc) of
            SOME a => (SOME a)
          | NONE => (case (#propagator E) (#constructor tc) of
                      NONE => NONE
                    | SOME f => f (map ((evaluate E)) cs)) handle Option => NONE)

  val trueT = CSpace.makeToken "" (Type.typeOfString "true")
  fun optionSum [] = 0.0
    | optionSum (NONE::t) = optionSum t - 1.0
    | optionSum (SOME x :: t) = x + optionSum t
  fun mkISEvaluator cf =
      {name = "IS",
       seedFun = fn x => if x = trueT then SOME 1.0 else NONE,
       propagator = fn c => case cf c of NONE => NONE
                                       | SOME s => SOME (fn L => SOME (optionSum L + s))}

end;
