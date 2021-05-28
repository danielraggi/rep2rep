import "construction";

signature PATTERN =
sig
  include CONSTRUCTION
  type pattern;

  val tokenMatches : TypeSystem.typeSystem -> CSpace.token -> CSpace.token -> bool
  (*val matches : TypeSystem.typeSystem -> construction -> pattern -> bool;*)
  (*val generatorMatches : TypeSystem.typeSystem -> construction -> pattern -> bool;*)
  (*val findGeneratorMatching : TypeSystem.typeSystem -> construction -> pattern -> construction option;*)
  val findMapFromPatternToGenerator : TypeSystem.typeSystem -> construction -> pattern -> (CSpace.token -> CSpace.token option);
  val findMapAndGeneratorMatchingForToken : TypeSystem.typeSystem -> construction -> pattern -> CSpace.token -> ((CSpace.token -> CSpace.token option) * construction option) list;

  val funUnion : ('a -> CSpace.token option) list -> ('a -> CSpace.token option)
  val applyMorpism : (CSpace.token -> CSpace.token option) -> pattern -> pattern;
(*)  val trivial : TypeSystem.typ -> construction;*)
end;

structure Pattern : PATTERN =
struct
  open Construction
  type pattern = construction;

  fun matchingConfigurators u u' =
      CSpace.sameConstructors (CSpace.constructorOfConfigurator u) (CSpace.constructorOfConfigurator u')

  fun tokenMatches T t t' = (#subType T) (CSpace.typeOfToken t,CSpace.typeOfToken t')

  exception NoMatchingGenerator

  (*
  fun matches T (Source t) (Source t') = tokenMatches T t t'
    | matches _ (Loop _) (Loop _) = true (* assumes this has been checked before *)
    | matches T (TCPair ({token = t, configurator = u},cs)) (TCPair ({token = t', configurator = u'},cs')) =
        matchingConfigurators u u'
        andalso tokenMatches T t t'
        andalso List.allZip (matches T) cs cs'
    | matches _ _ _ = false

  (* genertorMatches T c c' checks whether a generator of c matches the pattern c' exists*)
  fun generatorMatches T (Source t) (Source t') = tokenMatches T t t'
    | generatorMatches _ (Loop _) (Loop _) = true (* assumes this has been checked before *)
    | generatorMatches T (TCPair ({token = t, configurator = u},cs)) (TCPair ({token = t', configurator = u'},cs')) =
        matchingConfigurators u u'
        andalso tokenMatches T t t'
        andalso List.allZip (generatorMatches T) cs cs'
    | generatorMatches T (TCPair ({token = t, ...},_)) (Source t') =
        tokenMatches T t t'
    | generatorMatches _ _ _ = false
*)

  (*)
  (* genertorMatches T c c' checks whether a generator of c matches the pattern c' exists*)
  fun findGeneratorMatching T (Source t) (Source t') = if tokenMatches T t t' then SOME (Source t) else NONE
    | findGeneratorMatching _ (Loop t) (Loop _) = SOME (Loop t) (* assumes this has been checked before *)
    | findGeneratorMatching T (TCPair ({token = t, configurator = u},cs)) (TCPair ({token = t', configurator = u'},cs')) =
      if matchingConfigurators u u' andalso tokenMatches T t t'
      then
        let val CH = List.funZip (findGeneratorMatching T) cs cs'
            fun ss (SOME x ::t) = x :: ss t
              | ss (NONE :: _) = raise NoMatchingGenerator
              | ss [] = []
        in SOME (TCPair ({token = t, configurator = u},ss CH)) handle NoMatchingGenerator => NONE
        end
      else NONE
    | findGeneratorMatching T (TCPair ({token = t, ...},_)) (Source t') =
        if tokenMatches T t t' then SOME (Source t) else NONE
    | findGeneratorMatching _ _ _ = NONE*)


  exception Undefined
  fun applyMorpism f (Source t) = (case f t of NONE => raise Undefined | SOME x => Source x)
    | applyMorpism f (Loop t) = (case f t of NONE => raise Undefined | SOME x => Loop x)
    | applyMorpism f (TCPair ({token = t, configurator = u},cs)) =
        (case f t of NONE => raise Undefined
                   | SOME x => TCPair ({token = x, configurator = u}, map (applyMorpism f) cs))

  fun funUnion (f::L) x = (* Here there's a check that the map is compatible on all the subconstructions *)
    (case (f x, funUnion L x) of
        (NONE,SOME y) => SOME y
      | (SOME y,NONE) => SOME y
      | (NONE,NONE) => NONE
      | (SOME y, SOME z) => if CSpace.sameTokens y z then SOME y else raise Undefined)
    | funUnion [] _ = NONE

  (* *)
  fun findMapFromPatternToGenerator T (Source t) (Source t') =
        if tokenMatches T t t'
        then (fn x => if CSpace.sameTokens x t' then SOME t else NONE)
        else (fn _ => NONE)
    | findMapFromPatternToGenerator T (Loop t) (Loop t') =
        if tokenMatches T t t'
        then (fn x => if CSpace.sameTokens x t' then SOME t else NONE)
        else (fn _ => NONE)
    | findMapFromPatternToGenerator T (TCPair ({token = t, configurator = u},cs)) (TCPair ({token = t', configurator = u'},cs')) =
        if matchingConfigurators u u' andalso tokenMatches T t t'
        then
          let val CHfunctions = List.funZip (findMapFromPatternToGenerator T) cs cs'

              fun nodeFunction x = if CSpace.sameTokens x t' then SOME t else NONE
          in funUnion (nodeFunction :: CHfunctions)
          end
        else (fn _ => NONE)
    | findMapFromPatternToGenerator T (TCPair ({token = t, ...},_)) (Source t') =
        if tokenMatches T t t' then (fn x => if CSpace.sameTokens x t' then SOME t else NONE) else (fn _ => NONE)
    | findMapFromPatternToGenerator _ _ _ = (fn _ => NONE)

  fun findMapAndGeneratorMatching T ct ct' =
    let val f = findMapFromPatternToGenerator T ct ct'
        val g = applyMorpism f ct'
    in (f, SOME g)
    end handle Undefined => (fn _ => NONE,NONE)

(*)
  (* *)
  fun findMapAndGeneratorMatching T (Source t) (Source t') =
        if tokenMatches T t t'
        then (fn x => if CSpace.sameTokens x t' then SOME t else NONE, SOME (Source t))
        else (fn _ => NONE, NONE)
    | findMapAndGeneratorMatching _ (Loop t) (Loop _) = (fn _ => NONE, SOME (Loop t)) (* assumes this has been checked before *)
    | findMapAndGeneratorMatching T (TCPair ({token = t, configurator = u},cs)) (TCPair ({token = t', configurator = u'},cs')) =
        if matchingConfigurators u u' andalso tokenMatches T t t'
        then
          let val CH = List.funZip (findMapAndGeneratorMatching T) cs cs'
              fun ss (SOME x ::t) = x :: ss t
                | ss (NONE :: _) = raise NoMatchingGenerator
                | ss [] = []
              fun sf (f::L) x =
                    (case f x of NONE => sf L x
                               | SOME y => case sf L x of SOME z => if CSpace.sameTokens y z then SOME y else NONE else (* Here there's a check that the map is compatible on all the subconstructions *)
                                                        | NONE => SOME y)
                | sf [] _ = NONE
              fun f x = if CSpace.sameTokens x t' then SOME t else sf (map #1 CH) x
              val ch = ss (map #2 CH)
          in (f, SOME (TCPair ({token = t, configurator = u}, ch))) handle NoMatchingGenerator => (fn _ => NONE,NONE)
          end
        else (fn _ => NONE, NONE)
    | findMapAndGeneratorMatching T (TCPair ({token = t, ...},_)) (Source t') =
        if tokenMatches T t t' then (fn x => if CSpace.sameTokens x t' then SOME t else NONE, SOME (Source t)) else (fn _ => NONE,NONE)
    | findMapAndGeneratorMatching _ _ _ = (fn _ => NONE,NONE)
    *)

  (* Belongs in LISTS (?) *)(*)
  fun findFirstSome [] = NONE
    | findFirstSome (NONE :: L) = findFirstSome L
    | findFirstSome (SOME x :: _) = SOME x
  fun findFirstSome' [] = (fn _ => NONE,NONE)
    | findFirstSome' ((_,NONE) :: L) = findFirstSome' L
    | findFirstSome' ((f,SOME x) :: _) = (f,SOME x)*)

  fun filterSomes [] = []
    | filterSomes (NONE :: L) = filterSomes L
    | filterSomes (SOME x :: L) = x :: filterSomes L
  fun filterSomes' [] = []
    | filterSomes' ((_,NONE) :: L) = filterSomes' L
    | filterSomes' ((f,SOME x) :: L) = (f,SOME x) :: filterSomes' L

(*)
  fun findGeneratorMatchingForToken T ct p t =
      if CSpace.sameTokens t (Construction.constructOf ct) then findGeneratorMatching T (Construction.fixInducedConstruction ct) p
      else (case ct of TCPair (_, cs) => findFirstSome (map (fn c => findGeneratorMatchingForToken T c p t) cs)
                                      | _ => NONE)*)

  fun findMapAndGeneratorMatchingForToken T ct p t =
      if CSpace.sameTokens t (Construction.constructOf ct)
      then [findMapAndGeneratorMatching T (Construction.fixInducedConstruction ct) p]
      else (case ct of TCPair (_, cs) => filterSomes' (List.maps (fn x => findMapAndGeneratorMatchingForToken T x p t) cs)
                                  | _ => [])

(*
  fun trivial ty = Source (CSpace.makeToken "dummy" ty)*)

end;
