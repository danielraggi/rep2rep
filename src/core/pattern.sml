import "core.construction";

signature PATTERN =
sig
  include CONSTRUCTION
  type pattern;

  val configuratorMatches : CSpace.configurator -> CSpace.configurator -> bool
  val tokenMatches : Type.typeSystem -> CSpace.token -> CSpace.token -> bool
  val matches : Type.typeSystem -> construction -> pattern -> bool;
  val unifiable : Type.typeSystem -> pattern -> pattern -> bool;
  val hasUnifiableGenerator : Type.typeSystem -> pattern -> pattern -> bool;
  val funUnion : ('a -> CSpace.token option) list -> ('a -> CSpace.token option)
  val applyMorphism : (CSpace.token -> CSpace.token option) -> pattern -> pattern;
  val applyPartialMorphism : (CSpace.token -> CSpace.token option) -> pattern -> pattern;
  val findMapFromPatternToGenerator : Type.typeSystem -> construction -> pattern -> (CSpace.token -> CSpace.token option);
  val findMapAndGeneratorMatching : Type.typeSystem -> construction -> pattern -> (CSpace.token -> CSpace.token option) * construction option;
  val findMapAndGeneratorMatchingForToken : Type.typeSystem
                                         -> construction
                                         -> pattern
                                         -> CSpace.token
                                         -> ((CSpace.token -> CSpace.token option) * construction option) ;

end;

structure Pattern : PATTERN =
struct
  open Construction
  type pattern = construction;

  fun configuratorMatches u u' =
      CSpace.sameConstructors (CSpace.constructorOfConfigurator u) (CSpace.constructorOfConfigurator u')

  fun tokenMatches T t t' = (#subType T) (CSpace.typeOfToken t,CSpace.typeOfToken t')

  exception NoMatchingGenerator

  exception Undefined
  fun applyMorphism f (Source t) = (case f t of NONE => raise Undefined | SOME x => Source x)
    | applyMorphism f (Reference t) = (case f t of NONE => raise Undefined | SOME x => Reference x)
    | applyMorphism f (TCPair ({token = t, constructor = c},cs)) =
        (case f t of NONE => raise Undefined
                   | SOME x => TCPair ({token = x, constructor = c}, map (applyMorphism f) cs))
  fun applyPartialMorphism f (Source t) = (case f t of NONE => Source t | SOME x => Source x)
    | applyPartialMorphism f (Reference t) = (case f t of NONE => Reference t | SOME x => Reference x)
    | applyPartialMorphism f (TCPair ({token = t, constructor = c},cs)) =
        (case f t of NONE => TCPair ({token = t, constructor = c}, map (applyPartialMorphism f) cs)
                   | SOME x => TCPair ({token = x, constructor = c}, map (applyPartialMorphism f) cs))

  fun funUnion (f::L) x = (* Here there's a check that the map is compatible on all the subconstructions *)
    (case (f x, funUnion L x) of
        (NONE,SOME y) => SOME y
      | (SOME y,NONE) => SOME y
      | (NONE,NONE) => NONE
      | (SOME y, SOME z) => if CSpace.sameTokens y z then SOME y else raise Undefined)
    | funUnion [] _ = NONE

  (* Assumes well-formedness *)
  fun matches T ct pt =
    let fun m (Source t) (Source t') = tokenMatches T t t'
          | m (Reference t) (Reference t') = tokenMatches T t t'
          | m (TCPair ({token = t, constructor = c},cs)) (TCPair ({token = t', constructor = c'},cs')) =
                CSpace.sameConstructors c c' andalso tokenMatches T t t' andalso
                List.allZip (matches T) cs cs'
          | m _ _ = false
    in m ct pt
    end

  fun unifiable T ct1 ct2 =
    let fun u (Source t) (Source t') = tokenMatches T t t' orelse tokenMatches T t' t
          | u (Reference t) (Reference t') = tokenMatches T t t' orelse tokenMatches T t' t
          | u (TCPair ({token = t, constructor = c},cs)) (TCPair ({token = t', constructor = c'},cs')) =
                CSpace.sameConstructors c c' andalso (tokenMatches T t t' orelse tokenMatches T t' t) andalso
                List.allZip (unifiable T) cs cs'
          | u _ _ = false
    in u ct1 ct2
    end

  fun hasUnifiableGenerator T ct1 ct2 =
    let fun hu (Source t) (Source t') = tokenMatches T t t' orelse tokenMatches T t' t
          | hu (Reference t) (Reference t') = tokenMatches T t t' orelse tokenMatches T t' t
          | hu (TCPair ({token = t, constructor = c},cs)) (TCPair ({token = t', constructor = c'},cs')) =
                CSpace.sameConstructors c c' andalso
                (tokenMatches T t t' orelse tokenMatches T t' t) andalso
                List.allZip (hasUnifiableGenerator T) cs cs'
          | hu (TCPair ({token = t,...},_)) (Source t') = tokenMatches T t t' orelse tokenMatches T t' t
          | hu _ _ = false
    in hu ct1 ct2
    end

  (* *)
  fun findMapFromPatternToGenerator T ct ct' =
  let
    fun findMapFromPatternToGenerator' (Source t) (Source t') =
          if tokenMatches T t t'
          then (fn x => if CSpace.sameTokens x t' then SOME t else NONE)
          else (fn _ => NONE)
      | findMapFromPatternToGenerator' (Reference t) (Reference t') =
          if tokenMatches T t t'
          then (fn x => if CSpace.sameTokens x t' then SOME t else NONE)
          else (fn _ => NONE)
      | findMapFromPatternToGenerator' (TCPair ({token = t, constructor = c},cs))
                                        (TCPair ({token = t', constructor = c'},cs')) =
          if CSpace.sameConstructors c c' andalso tokenMatches T t t'
          then
            let val CHfunctions = List.funZip (findMapFromPatternToGenerator') cs cs'
                fun nodeFunction x = if CSpace.sameTokens x t' then SOME t else NONE
            in funUnion (nodeFunction :: CHfunctions)
            end
          else (fn _ => NONE)
      | findMapFromPatternToGenerator' (TCPair ({token = t, ...},_)) (Source t') =
          if tokenMatches T t t'
          then (fn x => if CSpace.sameTokens x t' then SOME t else NONE)
          else (fn _ => NONE)
      | findMapFromPatternToGenerator' (Reference t) ctx =
          if tokenMatches T t (constructOf ctx)
          then findMapFromPatternToGenerator' (findAndExpandSubConstruction ct t) ctx
          else (fn _ => NONE)
      | findMapFromPatternToGenerator' _ _ = (fn _ => NONE)
  in findMapFromPatternToGenerator' ct ct'
  end

  fun findMapAndGeneratorMatching T ct ct' =
    let val f = findMapFromPatternToGenerator T ct ct'
        val g = applyMorphism f ct'
    in (f, SOME g)
    end handle Undefined => (fn _ => NONE,NONE)

  fun filterSomes [] = []
    | filterSomes (NONE :: L) = filterSomes L
    | filterSomes (SOME x :: L) = x :: filterSomes L
  fun filterSomes' [] = []
    | filterSomes' ((_,NONE) :: L) = filterSomes' L
    | filterSomes' ((f,SOME x) :: L) = (f,SOME x) :: filterSomes' L
  fun firstSome [] = (fn _ => NONE,NONE)
    | firstSome ((_,NONE) :: L) = firstSome L
    | firstSome ((f,SOME x) :: L) = (f,SOME x)

  fun findMapAndGeneratorMatchingForToken T ct p t =
      if CSpace.sameTokens t (constructOf ct)
      then (findMapAndGeneratorMatching T (fixReferences ct) p)
      else (case ct of
              TCPair (_, cs) =>
                let fun fmg (x::xs) = (case findMapAndGeneratorMatchingForToken T x p t of
                                        (_,NONE) => fmg xs
                                      | P => P)
                      | fmg [] = (fn _ => NONE,NONE)
                in fmg cs
                end
            | _ => (fn _ => NONE,NONE))

      (*firstSome (List.map (fn x => findMapAndGeneratorMatchingForToken T x p t) cs)
                                  | _ => (fn _ => NONE,NONE))*)

end;
