import "core.construction";

signature PATTERN =
sig
  include CONSTRUCTION
  type pattern;
  exception Undefined
  val pattern_rpc : pattern Rpc.Datatype.t;

  val configuratorMatches : CSpace.configurator -> CSpace.configurator -> bool
  val tokenMatches : Type.typeSystem -> CSpace.token -> CSpace.token -> bool
  val mapUnder : pattern -> pattern
                         -> (CSpace.token -> CSpace.token -> bool)
                         -> (CSpace.constructor -> CSpace.constructor -> bool)
                         -> (bool * (CSpace.token -> CSpace.token option))
  val similar : pattern -> pattern -> bool
  val matches : Type.typeSystem -> pattern -> pattern -> bool;
  (*val unifiable : Type.typeSystem -> pattern -> pattern -> bool;*)
  val hasUnifiableGenerator : Type.typeSystem -> pattern -> pattern -> bool;
  val funUnion : ('a -> CSpace.token option) list -> ('a -> CSpace.token option)
  val applyMorphism : (CSpace.token -> CSpace.token option) -> pattern -> pattern;
  val applyPartialMorphism : (CSpace.token -> CSpace.token option) -> pattern -> pattern;
  val findEmbedding : Type.typeSystem -> pattern -> pattern -> (CSpace.token -> CSpace.token option) * construction option
  val findMatch : Type.typeSystem -> pattern -> pattern -> (CSpace.token -> CSpace.token option) * construction option
  val findMatchUpTo : Type.typeSystem -> pattern -> pattern -> CSpace.token FiniteSet.set -> (CSpace.token -> CSpace.token option) * construction option
  val findEmbeddingUpTo : Type.typeSystem -> pattern -> pattern -> CSpace.token FiniteSet.set -> (CSpace.token -> CSpace.token option) * construction option
  val findMapFromPatternToGenerator : Type.typeSystem -> pattern -> pattern -> (CSpace.token -> CSpace.token option);
  val findMapAndGeneratorMatching : Type.typeSystem -> pattern -> pattern -> (CSpace.token -> CSpace.token option) * construction option;
  val matchToSubConstructionWithConstruct : Type.typeSystem
                                         -> construction
                                         -> pattern
                                         -> CSpace.token
                                         -> ((CSpace.token -> CSpace.token option) * construction option) ;

end;

structure Pattern : PATTERN =
struct
  open Construction
  type pattern = construction;

  val pattern_rpc = Rpc.Datatype.alias "Pattern.pattern" construction_rpc;

  fun configuratorMatches u u' =
      CSpace.sameConstructors (CSpace.constructorOfConfigurator u) (CSpace.constructorOfConfigurator u')

  fun tokenMatches T t t' = (#subType T) (CSpace.typeOfToken t,CSpace.typeOfToken t')

  (*TODO: in some future version, unifiable should check whether there's a common super-type,
          but this is hard to know in general because the set of types might be infinite *)
  (*fun unifiableTokens T t t' = tokenMatches T t t' orelse tokenMatches T t' t*)

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

  fun funUnion (f::L) x =
    (case (f x, funUnion L x) of
        (NONE,SOME y) => SOME y
      | (SOME y,NONE) => SOME y
      | (NONE,NONE) => NONE
      | (SOME y, SOME z) => if CSpace.sameTokens y z then SOME y else (Logging.write "funUnion undefined!\n"; raise Undefined))
    | funUnion [] _ = NONE

    (* Assumes well-formedness *)
    fun mapUnder ct1 ct2 relTok relCons =
    let fun u (Source t) (Source t') f = (relTok t t', fn x => if CSpace.sameTokens x t then SOME t' else f x)
          | u (Reference t) (Reference t') f = (f t = SOME t',f)
          | u (TCPair ({token = t, constructor = c}, cs)) (TCPair ({token = t', constructor = c'}, cs')) f =
            let fun uu (x::xq) (y::yq) g =
                    (case u x y g of (b,g') => if b then uu xq yq g' else (false, g'))
                  | uu [] [] g = (true, g)
                  | uu _ _ g = (false, g)
            in if relCons c c' andalso relTok t t'
               then uu cs cs' (fn z => if CSpace.sameTokens z t then SOME t' else f z)
               else (false, f)
            end
          | u _ _ f = (false, f)
    in u ct1 ct2 (fn _ => NONE)
    end

  fun similar pt pt' = #1 (mapUnder pt pt' CSpace.tokensHaveSameType CSpace.sameConstructors)
  (* Assumes well-formedness *)
  fun matches T ct pt = #1 (mapUnder ct pt (tokenMatches T) CSpace.sameConstructors)

  (* Assumes well-formedness *)
(*  fun unifiable T ct1 ct2 = #1 (mapUnder ct1 ct2 (unifiableTokens T) CSpace.sameConstructors)*)

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
  fun findMatch T ct ct' =
  let
    fun fm (Source t) (Source t') =
          if tokenMatches T t t'
          then (fn x => if CSpace.sameTokens x t' then SOME t else NONE)
          else (fn _ => NONE)
      | fm (Reference t) (Reference t') =
          if tokenMatches T t t'
          then (fn x => if CSpace.sameTokens x t' then SOME t else NONE)
          else (fn _ => NONE)
      | fm (TCPair ({token = t, constructor = c},cs))
            (TCPair ({token = t', constructor = c'},cs')) =
          if CSpace.sameConstructors c c' andalso tokenMatches T t t'
          then
            let val CHfunctions = List.funZip fm cs cs'
                fun nodeFunction x = if CSpace.sameTokens x t' then SOME t else NONE
            in funUnion (nodeFunction :: CHfunctions)
            end
          else (fn _ => NONE)
      | fm _ _ = (fn _ => NONE)
    val f = fm ct ct'
    val g = applyMorphism f ct'
  in (f, SOME g)
  end handle Undefined => (fn _ => NONE,NONE)

  (* *)
  fun findMatchUpTo T ct ct' tokens =
  let
    fun fm (Source t) (Source t') =
          if tokenMatches T t t'
          then (fn x => if CSpace.sameTokens x t' then SOME t else NONE)
          else if FiniteSet.elementOf t' tokens andalso tokenMatches T t' t
               then (fn x => if CSpace.sameTokens x t' then SOME t' else NONE)
               else (fn _ => NONE)
      | fm (Reference t) (Reference t') =
          if tokenMatches T t t'
          then (fn x => if CSpace.sameTokens x t' then SOME t else NONE)
          else if (FiniteSet.elementOf t' tokens andalso tokenMatches T t' t)
               then (fn x => if CSpace.sameTokens x t' then SOME t' else NONE)
               else (fn _ => NONE)
      | fm (TCPair ({token = t, constructor = c},cs))
           (TCPair ({token = t', constructor = c'},cs')) =
          if CSpace.sameConstructors c c'
          then if tokenMatches T t t'
               then let val CHfunctions = List.funZip fm cs cs'
                        fun nodeFunction x = if CSpace.sameTokens x t' then SOME t else NONE
                    in funUnion (nodeFunction :: CHfunctions)
                    end
               else if FiniteSet.elementOf t' tokens andalso tokenMatches T t' t
                    then (fn x => if CSpace.sameTokens x t' then SOME t' else NONE)
                    else (fn _ => NONE)
          else (fn _ => NONE)
      | fm _ _ = (fn _ => NONE)
    fun f x = (fm ct ct') x
    val g = applyMorphism f ct'
  in (f, SOME g)
  end handle Undefined => (fn _ => NONE,NONE)

  (* *)
  fun findEmbeddingUpTo T ct ct' tokens =
  let
    fun fm (Source t) (Source t') =
          if tokenMatches T t t' orelse (FiniteSet.elementOf t' tokens andalso tokenMatches T t' t)
          then (fn x => if CSpace.sameTokens x t then SOME t' else NONE)
          else (fn _ => NONE)
      | fm (Reference t) (Reference t') =
          if tokenMatches T t t' orelse (FiniteSet.elementOf t' tokens andalso tokenMatches T t' t)
          then (fn x => if CSpace.sameTokens x t then SOME t' else NONE)
          else (fn _ => NONE)
      | fm (TCPair ({token = t, constructor = c},cs))
           (TCPair ({token = t', constructor = c'},cs')) =
          if CSpace.sameConstructors c c' andalso (tokenMatches T t t' orelse (FiniteSet.elementOf t' tokens andalso tokenMatches T t' t))
          then
            let val CHfunctions = List.funZip fm cs cs'
                fun nodeFunction x = if CSpace.sameTokens x t then SOME t' else NONE
            in funUnion (nodeFunction :: CHfunctions)
            end
          else (fn _ => NONE)
      | fm _ _ = (fn _ => NONE)
    val f = fm ct ct'
    val g = applyMorphism f ct
  in (f, SOME g)
  end handle Undefined => (fn _ => NONE,NONE)

  (* *)
  fun findEmbedding T ct ct' =
  let
    fun fm (Source t) (Source t') =
          if tokenMatches T t t'
          then (fn x => if CSpace.sameTokens x t then SOME t' else NONE)
          else (fn _ => NONE)
      | fm (Reference t) (Reference t') =
          if tokenMatches T t t'
          then (fn x => if CSpace.sameTokens x t then SOME t' else NONE)
          else (fn _ => NONE)
      | fm (TCPair ({token = t, constructor = c},cs))
            (TCPair ({token = t', constructor = c'},cs')) =
          if CSpace.sameConstructors c c' andalso tokenMatches T t t'
          then
            let val CHfunctions = List.funZip fm cs cs'
                fun nodeFunction x = if CSpace.sameTokens x t then SOME t' else NONE
            in funUnion (nodeFunction :: CHfunctions)
            end
          else (fn _ => NONE)
      | fm _ _ = (fn _ => NONE)
    val f = fm ct ct'
    val g = applyMorphism f ct
  in (f, SOME g)
  end handle Undefined => (fn _ => NONE,NONE)

  (* *)
  fun findMapFromPatternToGenerator T ct ct' =
  let
    fun mpg (Source t) (Source t') =
          if tokenMatches T t t'
          then (fn x => if CSpace.sameTokens x t' then SOME t else NONE)
          else (fn _ => NONE)
      | mpg (Reference t) (Reference t') =
          if tokenMatches T t t'
          then (fn x => if CSpace.sameTokens x t' then SOME t else NONE)
          else (fn _ => NONE)
      | mpg (TCPair ({token = t, constructor = c},cs))
            (TCPair ({token = t', constructor = c'},cs')) =
          if CSpace.sameConstructors c c' andalso tokenMatches T t t'
          then
            let val CHfunctions = List.funZip (mpg) cs cs'
                fun nodeFunction x = if CSpace.sameTokens x t' then SOME t else NONE
            in funUnion (nodeFunction :: CHfunctions)
            end
          else (fn _ => NONE)
      | mpg (TCPair ({token = t, ...},_)) (Source t') =
          if tokenMatches T t t'
          then (fn x => if CSpace.sameTokens x t' then SOME t else NONE)
          else (fn _ => NONE)
      | mpg (Reference t) ctx =
          if tokenMatches T t (constructOf ctx)
          then mpg (largestSubConstructionWithConstruct ct t) ctx
          else (fn _ => NONE)
      | mpg _ _ = (fn _ => NONE)
  in mpg ct ct'
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

(* finds a subconstruction, sct, of ct with construct t that matches pattern p
    under type system T, and returns the map from p to sct as the first argument
    and sct as the second argument *)
  fun matchToSubConstructionWithConstruct T ct p t =
    if CSpace.sameTokens t (constructOf ct)
    then findMapAndGeneratorMatching T (fixReferences ct) p
    else (case ct of
            TCPair (_, cs) =>
              let fun fmg (x::xs) =
                        (case matchToSubConstructionWithConstruct T x p t of
                            (_,NONE) => fmg xs
                          | P => P)
                    | fmg [] = (fn _ => NONE,NONE)
              in fmg cs
              end
          | _ => (fn _ => NONE,NONE))

      (*firstSome (List.map (fn x => matchToSubConstructionWithConstruct T x p t) cs)
                                  | _ => (fn _ => NONE,NONE))*)


end;
