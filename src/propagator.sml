import "cspace";

signature PROPAGATOR =
sig
  type 'a tokenAttribute = CSpace.token -> 'a
  type 'a typeAttribute = CSpace.typ -> 'a
  type 'a tokenPropagator = 'a tokenAttribute -> CSpace.constructor -> ('a list -> 'a)
  type 'a typePropagator = 'a typeAttribute -> CSpace.constructor -> ('a list -> 'a)
  val propagateFromTypeSequence : 'a typePropagator -> 'a typeAttribute -> CSpace.constructor -> (CSpace.typ list) -> 'a
  val propagateFromTokenSequence : 'a typePropagator -> 'a tokeneAttribute -> CSpace.constructor -> (CSpace.token list) -> 'a
end;

structure Propagator : PROPAGATOR =
struct
  type 'a tokenAttribute = CSpace.token -> 'a
  type 'a typeAttribute = CSpace.type -> 'a
  type 'a tokenPropagator = 'a tokenAttribute -> CSpace.constructor -> ('a list -> 'a)
  type 'a typePropagator = 'a typeAttribute -> CSpace.constructor -> ('a list -> 'a)
  fun propagateFromTypeSequence ppg att c T = ppg att c (map att T)
  fun propagateFromTokenSequence ppg att c T = ppg att c (map att T)
end;
