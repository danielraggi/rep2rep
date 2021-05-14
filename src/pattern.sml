import "construction"

signature PATTERN =
sig
  include CONSTRUCTION
  type pattern;

  val matches : TypeSystem.typeSystem -> construction -> pattern -> bool;
  val generatorMatches : TypeSystem.typeSystem -> construction -> pattern -> bool;
  val findGeneratorMatching : TypeSystem.typeSystem -> construction -> pattern -> construction option;
  val findMapAndGeneratorMatchingForToken : TypeSystem.typeSystem -> construction -> pattern -> CSpace.token -> ((CSpace.token -> CSpace.token option) * construction option);
  val applyPartialIsomorpism : (CSpace.token -> CSpace.token option) -> pattern -> pattern;

  val trivial : TypeSystem.typ -> construction;
end

structure Pattern : PATTERN =
struct
  open Construction
  type pattern = construction;

  fun tokenMatches T t t' = (#subType T) (CSpace.typeOfToken t,CSpace.typeOfToken t')

  fun matches T (Source t) (Source t') = tokenMatches T t t'
    | matches _ (Loop _) (Loop _) = true (* assumes this has been checked before *)
    | matches T (Construct ({token = t, configurator = u},cs)) (Construct ({token = t', configurator = u'},cs')) =
        CSpace.sameConfigurators u u'
        andalso tokenMatches T t t'
        andalso allZip (matches T) cs cs'
    | matches _ _ _ = false

  (* genertorMatches T c c' checks whether a generator of c matches the pattern c' exists*)
  fun generatorMatches T (Source t) (Source t') = tokenMatches T t t'
    | generatorMatches _ (Loop _) (Loop _) = true (* assumes this has been checked before *)
    | generatorMatches T (Construct ({token = t, configurator = u},cs)) (Construct ({token = t', configurator = u'},cs')) =
        CSpace.sameConfigurators u u'
        andalso tokenMatches T t t'
        andalso allZip (generatorMatches T) cs cs'
    | generatorMatches T (Construct ({token = t, ...},_)) (Source t') =
        tokenMatches T t t'
    | generatorMatches _ _ _ = false

  exception NoMatchingGenerator
  (* genertorMatches T c c' checks whether a generator of c matches the pattern c' exists*)
  fun findGeneratorMatching T (Source t) (Source t') = if tokenMatches T t t' then SOME (Source t) else NONE
    | findGeneratorMatching _ (Loop t) (Loop _) = SOME (Loop t) (* assumes this has been checked before *)
    | findGeneratorMatching T (Construct ({token = t, configurator = u},cs)) (Construct ({token = t', configurator = u'},cs')) =
      if CSpace.sameConfigurators u u' andalso tokenMatches T t t'
      then
        let val CH = funZip (findGeneratorMatching T) cs cs'
            fun ss (SOME x ::t) = x :: ss t
              | ss (NONE :: _) = raise NoMatchingGenerator
              | ss [] = []
        in SOME (Construct ({token = t, configurator = u},ss CH)) handle NoMatchingGenerator => NONE
        end
      else NONE
    | findGeneratorMatching T (Construct ({token = t, ...},_)) (Source t') =
        if tokenMatches T t t' then SOME (Source t) else NONE
    | findGeneratorMatching _ _ _ = NONE

  (* *)
  fun findMapAndGeneratorMatching T (Source t) (Source t') =
        if tokenMatches T t t'
        then (fn x => if CSpace.sameTokens x t' then SOME t else NONE, SOME (Source t))
        else (fn _ => NONE, NONE)
    | findMapAndGeneratorMatching _ (Loop t) (Loop _) = (fn _ => NONE, SOME (Loop t)) (* assumes this has been checked before *)
    | findMapAndGeneratorMatching T (Construct ({token = t, configurator = u},cs)) (Construct ({token = t', configurator = u'},cs')) =
        if CSpace.sameConfigurators u u' andalso tokenMatches T t t'
        then
          let val CH = funZip (findMapAndGeneratorMatching T) cs cs'
              fun ss (SOME x ::t) = x :: ss t
                | ss (NONE :: _) = raise NoMatchingGenerator
                | ss [] = []
              fun sf (f::L) x = (case f x of NONE => sf L x | SOME y => SOME y)
                | sf [] _ = NONE
              fun f x = if CSpace.sameTokens x t' then SOME t else sf (map #1 CH) x
              val ch = ss (map #2 CH)
          in (f, SOME (Construct ({token = t, configurator = u}, ch))) handle NoMatchingGenerator => (fn _ => NONE,NONE)
          end
        else (fn _ => NONE, NONE)
    | findMapAndGeneratorMatching T (Construct ({token = t, ...},_)) (Source t') =
        if tokenMatches T t t' then (fn x => if CSpace.sameTokens x t' then SOME t else NONE, SOME (Source t)) else (fn _ => NONE,NONE)
    | findMapAndGeneratorMatching _ _ _ = (fn _ => NONE,NONE)

  (* Belongs in LISTS (?) *)
  fun findFirstSome [] = NONE
    | findFirstSome (NONE :: L) = findFirstSome L
    | findFirstSome (SOME x :: _) = SOME x
  fun findFirstSome' [] = (fn _ => NONE,NONE)
    | findFirstSome' ((_,NONE) :: L) = findFirstSome' L
    | findFirstSome' ((f,SOME x) :: _) = (f,SOME x)

  fun findGeneratorMatchingForToken T ct p t =
      if CSpace.sameTokens t (Construction.constructOf ct) then findGeneratorMatching T (Construction.fixInducedConstruction ct) p
      else (case ct of Construct (_, cs) => findFirstSome (map (fn c => findGeneratorMatchingForToken T c p t) cs)
                                      | _ => NONE)

  fun findMapAndGeneratorMatchingForToken T ct p t =
      if CSpace.sameTokens t (Construction.constructOf ct) then findMapAndGeneratorMatching T (Construction.fixInducedConstruction ct) p
      else (case ct of Construct (_, cs) => findFirstSome' (map (fn x => findMapAndGeneratorMatchingForToken T x p t) cs)
                                      | _ => (fn _ => NONE,NONE))

  fun trivial ty = Source (CSpace.makeToken "dummy" ty)

  fun applyPartialIsomorpism f (Source t) = (case f t of NONE => Source t | SOME x => Source x)
    | applyPartialIsomorpism f (Loop t) = (case f t of NONE => Loop t | SOME x => Loop x)
    | applyPartialIsomorpism f (Construct ({token = t, configurator = u},cs)) =
        (case f t of NONE => Construct ({token = t, configurator = u}, map (applyPartialIsomorpism f) cs)
                  | SOME x => Construct ({token = x, configurator = u}, map (applyPartialIsomorpism f) cs))

end
