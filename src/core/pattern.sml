import "core.construction";

signature PATTERN =
sig
  include CONSTRUCTION
  type pattern;
  exception IllDefined
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
  val funUnion : ('a -> 'a -> bool) -> ('a -> 'a option) list -> ('a -> 'a option)
  val applyMorphism : (CSpace.token -> CSpace.token option) -> pattern -> pattern;
  val applyPartialMorphism : (CSpace.token -> CSpace.token option) -> pattern -> pattern;
  val applyTypeVarInstantiation : (Type.typ -> Type.typ option) -> pattern -> pattern;
  val findEmbedding : Type.typeSystem
                        -> pattern
                        -> pattern
                        -> (CSpace.token -> CSpace.token option) * (CSpace.token -> CSpace.token option) * construction option
  val findEmbeddingUpTo : Type.typeSystem
                            -> CSpace.token FiniteSet.set
                            -> pattern
                            -> pattern
                            -> (CSpace.token -> CSpace.token option) * (CSpace.token -> CSpace.token option) * construction option
  val findEmbeddingMinimisingTypeUpTo : Type.typeSystemData
                                        -> CSpace.token FiniteSet.set
                                        -> pattern
                                        -> pattern
                                        -> (CSpace.token -> CSpace.token option) * (CSpace.token -> CSpace.token option) * (Type.typ -> Type.typ option) * construction option
  val findEmbeddingUpToConditionally : Type.typeSystem
                                        -> CSpace.token FiniteSet.set
                                        -> (pattern -> pattern -> bool)
                                        -> pattern
                                        -> pattern
                                        -> (CSpace.token -> CSpace.token option) * (CSpace.token -> CSpace.token option) * construction option
  val matchToSubConstructionWithConstruct : Type.typeSystem
                                              -> pattern
                                              -> pattern
                                              -> CSpace.token
                                              -> (CSpace.token -> CSpace.token option) * (CSpace.token -> CSpace.token option) * construction option ;
  val findEmbeddingsOfSubConstructionWithCompatibleInverse : Type.typeSystem
                                                               -> pattern
                                                               -> pattern
                                                               -> (CSpace.token -> CSpace.token option)
                                                               -> ((CSpace.token -> CSpace.token option) * (CSpace.token -> CSpace.token option) * construction) Seq.seq;
  val findUnificationOfSubConstructionConditionally : Type.typeSystemData
                                                       -> (pattern -> pattern -> bool)
                                                       -> pattern
                                                       -> pattern
                                                       -> ((CSpace.token -> CSpace.token option) * (CSpace.token -> CSpace.token option) * construction) Seq.seq;

end;

structure Pattern : PATTERN =
struct
  open Construction
  type pattern = construction;

  val pattern_rpc = Rpc.Datatype.alias "Pattern.pattern" construction_rpc;

  fun configuratorMatches u u' =
      CSpace.sameConstructors (CSpace.constructorOfConfigurator u) (CSpace.constructorOfConfigurator u')

  fun tokenMatches T t t' =
    let val ty = CSpace.typeOfToken t
        val ty' = CSpace.typeOfToken t'
    in #subType T (ty,ty') orelse
        (Type.isTypeVar ty andalso Type.equal (Type.parentTypeOfSubtypeable ty) (Type.parentTypeOfSubtypeable ty'))
    end handle Type.badType => false

  (*TODO: in some future version, unifiable should check whether there's a common super-type,
          but this is hard to know in general because the set of types might be infinite *)
  fun unifyTokens TSD t t' = Type.greatestCommonSubType TSD (CSpace.typeOfToken t) (CSpace.typeOfToken t')

  exception NoMatchingGenerator
  exception IllDefined

  fun applyMorphism f (Source t) = (case f t of NONE => raise IllDefined | SOME x => Source x)
    | applyMorphism f (Reference t) = (case f t of NONE => raise IllDefined | SOME x => Reference x)
    | applyMorphism f (TCPair ({token = t, constructor = c},cs)) =
        (case f t of NONE => raise IllDefined
                   | SOME x => TCPair ({token = x, constructor = c}, map (applyMorphism f) cs))
  fun applyPartialMorphism f (Source t) = (case f t of NONE => Source t | SOME x => Source x)
    | applyPartialMorphism f (Reference t) = (case f t of NONE => Reference t | SOME x => Reference x)
    | applyPartialMorphism f (TCPair ({token = t, constructor = c},cs)) =
        (case f t of NONE => TCPair ({token = t, constructor = c}, map (applyPartialMorphism f) cs)
                   | SOME x => TCPair ({token = x, constructor = c}, map (applyPartialMorphism f) cs))

  fun applyTypeVarInstantiation f (Source t) =
        (case f (CSpace.typeOfToken t) of
            NONE => Source t
          | SOME ty => Source (CSpace.makeToken (CSpace.nameOfToken t) ty))
    | applyTypeVarInstantiation f (Reference t) =
        (case f (CSpace.typeOfToken t) of
            NONE => Reference t
          | SOME ty => Reference (CSpace.makeToken (CSpace.nameOfToken t) ty))
    | applyTypeVarInstantiation f (TCPair ({token = t, constructor = c},cs)) =
        (case f (CSpace.typeOfToken t) of
            NONE => TCPair ({token = t, constructor = c}, map (applyTypeVarInstantiation f) cs)
          | SOME ty => TCPair ({token = CSpace.makeToken (CSpace.nameOfToken t) ty, constructor = c}, map (applyTypeVarInstantiation f) cs))

  fun funUnion eq (f::L) x =
    (case (f x, funUnion eq L x) of
        (NONE,SOME y) => SOME y
      | (SOME y,NONE) => SOME y
      | (NONE,NONE) => NONE
      | (SOME y, SOME z) => if eq y z
                            then SOME y
                            else raise IllDefined)
    | funUnion _ [] _ = NONE

    (* Assumes well-formedness *)
    fun mapUnder ct1 ct2 relTok relCons =
      let fun u (Source t) (Source t') f = (relTok t t', fn x => if CSpace.sameTokens x t then SOME t' else f x)
            | u (Reference t) (Reference t') f = (f t = SOME t',f)
            | u (TCPair ({token = t, constructor = c}, cs))
                (TCPair ({token = t', constructor = c'}, cs')) f =
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
    let fun hu (Source t) (Source t') =
                  tokenMatches T t t' orelse tokenMatches T t' t
          | hu (Reference t) (Reference t') =
                  tokenMatches T t t' orelse tokenMatches T t' t
          | hu (TCPair ({token = t, constructor = c},cs))
               (TCPair ({token = t', constructor = c'},cs')) =
                  CSpace.sameConstructors c c' andalso
                  (tokenMatches T t t' orelse tokenMatches T t' t) andalso
                  List.allZip (hasUnifiableGenerator T) cs cs'
          | hu (TCPair ({token = t,...},_)) (Source t') =
                  tokenMatches T t t' orelse tokenMatches T t' t
          | hu _ _ = false
    in hu ct1 ct2
    end

  fun unzip [] = ([],[])
    | unzip ((x,y)::L) = (case unzip L of (L1,L2) => (x::L1,y::L2))

  fun unzip3 [] = ([],[],[])
    | unzip3 ((x,y,z)::L) = (case unzip3 L of (L1,L2,L3) => (x::L1,y::L2,z::L3))
  (* *)
  fun findEmbeddingUpTo T tokens ct ct'  =
  let fun fm (Source t) (Source t') =
            if tokenMatches T t t' orelse FiniteSet.elementOf t tokens
            then (fn x => if CSpace.sameTokens x t then SOME t' else NONE,
                  fn x => if CSpace.sameTokens x t' then SOME t else NONE)
            else (fn _ => NONE,fn _ => NONE)
        | fm (Reference t) (Reference t') =
            if tokenMatches T t t' orelse FiniteSet.elementOf t tokens
            then (fn x => if CSpace.sameTokens x t then SOME t' else NONE,
                  fn x => if CSpace.sameTokens x t' then SOME t else NONE)
            else (fn _ => NONE,fn _ => NONE)
        | fm (TCPair ({token = t, constructor = c},cs))
             (TCPair ({token = t', constructor = c'},cs')) =
            if CSpace.sameConstructors c c' andalso
               (tokenMatches T t t' orelse FiniteSet.elementOf t tokens)
            then let val (CHfunctions1,CHfunctions2) = unzip (List.funZip fm cs cs')
                     fun nodeFunction1 x = if CSpace.sameTokens x t then SOME t' else NONE
                     fun nodeFunction2 x = if CSpace.sameTokens x t' then SOME t else NONE
                  in (funUnion CSpace.sameTokens (nodeFunction1 :: CHfunctions1), funUnion CSpace.sameTokens (nodeFunction2 :: CHfunctions2))
                  end
            else (fn _ => NONE,fn _ => NONE)
        | fm _ _ = (fn _ => NONE,fn _ => NONE)
    val (f1,f2) = fm ct ct'
    val g = applyMorphism f1 ct
  in (f1, f2, SOME g)
  end handle IllDefined => (fn _ => NONE,fn _ => NONE,NONE)

  (* NONE means nothing to say.
     IllDefined means there's an unresolvable clash, i.e., the variable gets
     instantiated to two different types which have no common subtype. *)
  fun resolveInstantiationFunctions TSD [] ty = NONE
    | resolveInstantiationFunctions TSD (f::fL) ty =
      (case resolveInstantiationFunctions TSD fL ty of
          NONE => f ty
        | SOME rty => (case f ty of
                          NONE => SOME rty
                        | SOME fty => (case Type.greatestCommonSubType TSD fty rty of
                                          NONE => raise IllDefined
                                        | SOME sty => (print (Type.nameOfType ty ^ " maps to " ^ Type.nameOfType sty ^ "\n");SOME sty))
                      )
      )

  (* if there exists an embedding ct -> ct' up to a set of tokens tks of ct,
     findEmbeddingMinimisingTypeUpTo yields maps f1, f2 and pattern g where:
        1. f: ct -> g
        2. f': ct' -> g
        3. g is isomorphic to ct and ct', with the token names of ct' but the
            smaller type of either ct or ct' in pair of corresponding tokens.
            (The smaller types will come from ct, except when they live in tks,
            in which case they may come from either ct or ct'.)
     otherwise it yields NONEs *)
  fun findEmbeddingMinimisingTypeUpTo TSD tks ct ct'  =
  let val T = #typeSystem TSD
      fun tMaps t t' =
        let val ty = CSpace.typeOfToken t
            val ty' = CSpace.typeOfToken t'
            val varInst = if Type.isTypeVar ty then ty' else ty
            val nt = CSpace.makeToken (CSpace.nameOfToken t') varInst
        in if tokenMatches T t t' then
             (fn x => if CSpace.sameTokens x t then SOME nt else NONE,
              fn x => if CSpace.sameTokens x t' then SOME nt else NONE,
              fn x => if Type.isTypeVar ty andalso Type.equal x ty then SOME ty' else NONE)
           else if FiniteSet.elementOf t tks then
              (fn x => if CSpace.sameTokens x t then SOME t' else NONE,
               fn x => if CSpace.sameTokens x t' then SOME t' else NONE,
               fn x => if Type.isTypeVar ty andalso Type.equal x ty then SOME ty' else NONE)
           else raise IllDefined
        end
      fun fm (Source t) (Source t') = tMaps t t'
        | fm (Reference t) (Reference t') = tMaps t t'
        | fm (TCPair ({token = t, constructor = c},cs))
             (TCPair ({token = t', constructor = c'},cs')) =
            if CSpace.sameConstructors c c' then
                let val (tMap, tMap', vMap) = tMaps t t'
                    val (CHMaps,CHMaps',vCHMaps) = unzip3 (List.funZip fm cs cs')
                in (funUnion CSpace.sameTokens (tMap :: CHMaps),
                    funUnion CSpace.sameTokens (tMap' :: CHMaps'),
                    resolveInstantiationFunctions TSD (vMap :: vCHMaps))
                end
            else raise IllDefined
        | fm _ _ = raise IllDefined
      val (f,f',vf) = fm ct ct'
      val _ = map (vf o CSpace.typeOfToken) (tokensOfConstruction ct)
      val g = applyMorphism f ct
  in (f, f', vf, SOME g)
  end handle IllDefined => (fn _ => NONE,fn _ => NONE,fn _ => NONE,NONE)

(*)
  (* if there exists an embedding ct -> ct' up to a set of tokens tks of ct,
     findEmbeddingMinimisingTypeUpTo yields maps f1, f2 and pattern g where:
        1. f: ct -> g
        2. f': ct' -> g
        3. g is isomorphic to ct and ct', with the token names of ct' but the
            smaller type of either ct or ct' in pair of corresponding tokens.
            (The smaller types will come from ct, except when they live in tks,
            in which case they may come from either ct or ct'.)
     otherwise it yields NONEs *)
  fun findEmbeddingMinimisingTypeUpTo T tks ct ct'  =
  let fun tMaps t t' =
        if tokenMatches T t t' then
            let val nt = CSpace.makeToken (CSpace.nameOfToken t') (CSpace.typeOfToken t)
            in (fn x => if CSpace.sameTokens x t then SOME nt else NONE,
                fn x => if CSpace.sameTokens x t' then SOME nt else NONE)
            end
        else if FiniteSet.elementOf t tks then
            (fn x => if CSpace.sameTokens x t then SOME t' else NONE,
             fn x => if CSpace.sameTokens x t' then SOME t' else NONE)
        else raise IllDefined
      fun fm (Source t) (Source t') = tMaps t t'
        | fm (Reference t) (Reference t') = tMaps t t'
        | fm (TCPair ({token = t, constructor = c},cs))
             (TCPair ({token = t', constructor = c'},cs')) =
            if CSpace.sameConstructors c c' then
                let val (tMap, tMap') = tMaps t t'
                    val (CHMaps,CHMaps',v) = unzip3 (List.funZip fm cs cs')
                in (funUnion (tMap :: CHMaps),funUnion (tMap' :: CHMaps'))
                end
            else raise IllDefined
        | fm _ _ = raise IllDefined
    val (f,f') = fm ct ct'
    val g = applyMorphism f ct
  in (f, f', SOME g)
  end handle IllDefined => (fn _ => NONE,fn _ => NONE,NONE)*)

  (* *)
  fun findEmbeddingUpToConditionally T tokens cond ct ct' =
  let fun fm (Source t) (Source t') =
            if cond (Source t) (Source t') andalso (tokenMatches T t t' orelse FiniteSet.elementOf t tokens)
            then (fn x => if CSpace.sameTokens x t then SOME t' else NONE,
                  fn x => if CSpace.sameTokens x t' then SOME t else NONE)
            else (fn _ => NONE,fn _ => NONE)
        | fm (Reference t) (Reference t') =
            if cond (Reference t) (Reference t') andalso (tokenMatches T t t' orelse FiniteSet.elementOf t tokens)
            then (fn x => if CSpace.sameTokens x t then SOME t' else NONE,
                  fn x => if CSpace.sameTokens x t' then SOME t else NONE)
            else (fn _ => NONE,fn _ => NONE)
        | fm (TCPair ({token = t, constructor = c},cs))
             (TCPair ({token = t', constructor = c'},cs')) =
            if CSpace.sameConstructors c c' andalso cond (TCPair ({token = t, constructor = c},cs))
                                                         (TCPair ({token = t', constructor = c'},cs')) andalso
               (tokenMatches T t t' orelse FiniteSet.elementOf t tokens)
            then let val (CHfunctions1,CHfunctions2) = unzip (List.funZip fm cs cs')
                     fun nodeFunction1 x = if CSpace.sameTokens x t then SOME t' else NONE
                     fun nodeFunction2 x = if CSpace.sameTokens x t' then SOME t else NONE
                  in (funUnion CSpace.sameTokens (nodeFunction1 :: CHfunctions1),funUnion CSpace.sameTokens (nodeFunction2 :: CHfunctions2))
                  end
            else (fn _ => NONE,fn _ => NONE)
        | fm _ _ = (fn _ => NONE,fn _ => NONE)
    val (f1,f2) = fm ct ct'
    val g = applyMorphism f1 ct
  in (f1, f2, SOME g)
  end handle IllDefined => (fn _ => NONE,fn _ => NONE,NONE)

  (* *)
  fun findEmbedding T ct ct' = findEmbeddingUpTo T FiniteSet.empty ct ct'

  (* returns the maps between ct' and a generator of ct that matches ct' (if it exists) *)
  fun findEmbeddingOfGenerator T contextCT ct ct' =
  let fun mpg (Source t) (Source t') =
            if tokenMatches T t t'
            then (fn x => if CSpace.sameTokens x t then SOME t' else NONE,
                  fn x => if CSpace.sameTokens x t' then SOME t else NONE)
            else (fn _ => NONE,fn _ => NONE)
        | mpg (Reference t) (Reference t') =
            if tokenMatches T t t'
            then (fn x => if CSpace.sameTokens x t then SOME t' else NONE,
                  fn x => if CSpace.sameTokens x t' then SOME t else NONE)
            else (fn _ => NONE,fn _ => NONE)
        | mpg (TCPair ({token = t, constructor = c},cs))
              (TCPair ({token = t', constructor = c'},cs')) =
            if CSpace.sameConstructors c c' andalso tokenMatches T t t'
            then
              let val (CHfunctions1,CHfunctions2) = unzip (List.funZip mpg cs cs')
                       fun nodeFunction1 x = if CSpace.sameTokens x t then SOME t' else NONE
                       fun nodeFunction2 x = if CSpace.sameTokens x t' then SOME t else NONE
              in (funUnion CSpace.sameTokens (nodeFunction1 :: CHfunctions1),funUnion CSpace.sameTokens (nodeFunction2 :: CHfunctions2))
              end
            else (fn _ => NONE,fn _ => NONE)
        | mpg (TCPair ({token = t, ...},_)) (Source t') =
            if tokenMatches T t t'
            then (fn x => if CSpace.sameTokens x t then SOME t' else NONE,
                  fn x => if CSpace.sameTokens x t' then SOME t else NONE)
            else (fn _ => NONE,fn _ => NONE)
        | mpg (Reference t) xct' =
            if tokenMatches T t (constructOf xct')
            then mpg (largestSubConstructionWithConstruct contextCT t) xct'
            else (fn _ => NONE,fn _ => NONE)
        | mpg _ _ = (fn _ => NONE,fn _ => NONE)
      val (f1,f2) = mpg ct ct'
      val gt = applyMorphism f2 ct'
  in (f1, f2, SOME gt)
  end handle IllDefined => (fn _ => NONE,fn _ => NONE,NONE)

  (* returns the maps between ct' and a generator of ct that matches ct' (if it exists) *)
  fun unifyGeneratorWithPattern TSD cond contextCT ct ct' =
  let fun uToken t t' ty = CSpace.makeToken ((CSpace.nameOfToken t) ^ "__" ^ (CSpace.nameOfToken t')) ty
      fun uTokenFun t t' ty x = if CSpace.sameTokens x t then SOME (uToken t t' ty) else NONE
      fun uTokenFun' t t' ty x = if CSpace.sameTokens x t' then SOME (uToken t t' ty) else NONE
      val noneFunPair = (fn _ => NONE,fn _ => NONE)
      fun mpg (Source t) (Source t') =
          if cond (Source t) (Source t') then
            (case unifyTokens TSD t t' of
              SOME gcsty => (uTokenFun t t' gcsty, uTokenFun' t t' gcsty)
            | NONE => noneFunPair)
          else noneFunPair
        | mpg (Reference t) (Reference t') =
          if cond (Reference t) (Reference t') then
            (case unifyTokens TSD t t' of
              SOME gcsty => (uTokenFun t t' gcsty, uTokenFun' t t' gcsty)
            | NONE => noneFunPair)
          else noneFunPair
        | mpg (TCPair ({token = t, constructor = c},cs))
              (TCPair ({token = t', constructor = c'},cs')) =
              if cond (TCPair ({token = t, constructor = c},cs))
                    (TCPair ({token = t', constructor = c'},cs')) andalso CSpace.sameConstructors c c'
              then (case unifyTokens TSD t t' of
                      SOME gcsty =>
                        let val (CHfunctions,CHfunctions') = unzip (List.funZip mpg cs cs')
                                 val nodeFunction = uTokenFun t t' gcsty
                                 val nodeFunction' = uTokenFun' t t' gcsty
                        in (funUnion CSpace.sameTokens (nodeFunction :: CHfunctions), funUnion CSpace.sameTokens (nodeFunction' :: CHfunctions'))
                        end
                    | NONE => noneFunPair)
              else noneFunPair
        | mpg (TCPair ({token = t, constructor},cs)) (Source t') =
          if cond (TCPair ({token = t, constructor=constructor},cs)) (Source t') then
            (case unifyTokens TSD t t' of
              SOME gcsty => (uTokenFun t t' gcsty, uTokenFun' t t' gcsty)
            | NONE => noneFunPair)
          else noneFunPair
        | mpg (Reference t) xct' =
          if cond (Reference t) xct' then
            (case unifyTokens TSD t (constructOf xct') of
                SOME _ => mpg (largestSubConstructionWithConstruct contextCT t) xct'
              | NONE => noneFunPair)
          else noneFunPair
        | mpg _ _ = noneFunPair
      val (f1,f2) = mpg ct ct'
      val gt = applyMorphism f2 ct'
      val gt' = applyMorphism f1 ct
      val _ = print "\nLet's see: \n"
      val _ = print (toString ct ^ "\n")
      val _ = print (toString gt ^ "\n")
  in (f1, f2, SOME gt)
  end handle IllDefined => (fn _ => NONE,fn _ => NONE,NONE)

  fun filterSomes [] = []
    | filterSomes (NONE :: L) = filterSomes L
    | filterSomes (SOME x :: L) = x :: filterSomes L
  fun filterSomes' [] = []
    | filterSomes' ((_,_,NONE) :: L) = filterSomes' L
    | filterSomes' ((f1,f2,SOME x) :: L) = (f1,f2,SOME x) :: filterSomes' L
  fun firstSome [] = (fn _ => NONE,fn _ => NONE,NONE)
    | firstSome ((_,_,NONE) :: L) = firstSome L
    | firstSome ((f1,f2,SOME x) :: L) = (f1,f2,SOME x)

(* finds a subconstruction, sct, of ct with construct t that matches pattern pt
    under type system T, and returns the map from pt to sct as the first argument
    and sct as the second argument *)
  fun matchToSubConstructionWithConstruct T ct pt t =
    let
      fun matchToSubConstructionWithConstruct' ctx ct =
        if CSpace.sameTokens t (constructOf ct)
        then findEmbeddingOfGenerator T ctx ct pt
        else (case ct of
                TCPair (_, cs) =>
                  let fun fmg (x::xs) =
                            (case matchToSubConstructionWithConstruct' ctx x of
                                (_,_,NONE) => fmg xs
                              | P => P)
                        | fmg [] = (fn _ => NONE,fn _ => NONE,NONE)
                  in fmg cs
                  end
              | _ => (fn _ => NONE,fn _ => NONE,NONE))
    in matchToSubConstructionWithConstruct' ct ct
    end

  (* finds all subconstructions, sct, of ct that match pattern pt
      under type system T, compatible with a given f (with domain pt),
      and returns a sequence of triples (f1,f2,sct) where
      f1 is the map from sct to pt,
      f2 is the inverse of f1*)
  fun findEmbeddingsOfSubConstructionWithCompatibleInverse T ct pt f =
    let fun fescci ctx seq =
        Seq.make (fn () =>
            (case Seq.pull seq of
                NONE => NONE
              | SOME (sct,seqL) =>
                (case findEmbeddingOfGenerator T ctx sct pt of
                    (f1,f2,SOME x) => (applyMorphism (funUnion CSpace.sameTokens [f,f2]) pt;
                                       SOME ((f1,f2,x), fescci ctx seqL))
                  | _ => Seq.pull (fescci ctx seqL))
                 handle IllDefined => Seq.pull (fescci ctx seqL))
        )
    in fescci ct (subConstructionsRaw ct)
    end

  fun findUnificationOfSubConstructionConditionally TSD cond ct pt =
    let fun fuscci ctx seq =
        Seq.make (fn () =>
            (case Seq.pull seq of
                NONE => NONE
              | SOME (sct,seqL) =>
                (case unifyGeneratorWithPattern TSD cond ctx sct pt of
                    (f1,f2,SOME x) => SOME ((f1,f2,x), fuscci ctx seqL)
                  | _ => Seq.pull (fuscci ctx seqL)))
        )
    in fuscci ct (subConstructionsRaw ct)
    end
(*)
    fun findEmbeddingsOfSubConstructionWithCompatibleInverse T ct pt f =
      let fun fescci T ctx ct pt f =
            let val (f1,f2,x) = findEmbeddingOfGenerator T ctx ct pt
                fun w () =
                  (case ct of
                      TCPair (_, cs) =>
                        let fun fmg [] = []
                              | fmg (x::xs) =
                                  (List.filterThenMap (fn (_,_,x) => isSome x) (fn (f1,f2,x) => (f1,f2,valOf x)) (fescci T ctx x pt f)) @ fmg xs
                        in fmg cs
                        end
                    | _ => [])
            in if isSome x
               then (applyMorphism (funUnion [f,f2]) pt; (f1,f2,valOf x) :: w ()) handle IllDefined => w ()
               else w ()
            end
      in fescci T ct ct pt f
      end*)
(*)
    case findMatchToGenerator T (fixReferences ct) pt of
      (h,SOME _) => (case applyMorphism (funUnion [f,h]) pt of
                        y => (h,SOME y)) handle IllDefined =>
    | _ => (case ct of
              TCPair (_, cs) =>
                let fun fmg (x::xs) =
                          (case findEmbeddingsOfSubConstructionWithCompatibleInverse T x pt f of
                              (_,NONE) => fmg xs
                            | P => P)
                      | fmg [] = (fn _ => NONE,NONE)
                in fmg cs
                end
            | _ => (fn _ => NONE,NONE))*)

      (*firstSome (List.map (fn x => matchToSubConstructionWithConstruct T x p t) cs)
                                  | _ => (fn _ => NONE,NONE))*)


end;
