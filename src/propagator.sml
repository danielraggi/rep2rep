import "construction";

signature PROPAGATOR =
sig
  val getPropagator : CSpace.constructor -> (string * ('a list -> 'a option)) list -> ('a list -> 'a option) option

  type propagator = CSpace.constructor -> ('a list -> 'a) option
end;

structure Propagator : PROPAGATOR =
struct

  fun nameOfPropagator (n,_) = n
  fun funOfPropagator (_,p) = p

  fun applyOption f (SOME x) = SOME (f x)
    | applyOption _ NONE = NONE

  fun getPropagator c P =
    applyOption funOfPropagator (List.find (fn x => CSpace.nameOfConstructor c = nameOfPropagator x) P)

  fun propagateTokens

end;
