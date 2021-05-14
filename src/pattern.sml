import "construction"

signature PATTERN =
sig
  include CONSTRUCTION
  type pattern;

  val matches : TypeSystem.typeSystem -> construction -> pattern -> bool;
  val generatorMatches : TypeSystem.typeSystem -> construction -> pattern -> bool;
  val findGeneratorMatching : TypeSystem.typeSystem -> construction -> pattern -> construction option;
  val findMapAndGeneratorMatchingForToken : TypeSystem.typeSystem -> construction -> pattern -> CSpace.token -> ((CSpace.token -> CSpace.token option) * construction option);
  val applyPartialIsomorpism : (CSpace.token -> CSpace.token) -> pattern -> pattern;

  val trivial : TypeSystem.typ -> construction;
end

structure Pattern : PATTERN =
struct
  open Construction
  type pattern = construction;

  fun tokenMatches T t t' = (#subType T) (CSpace.typeOfToken t,CSpace.typeOfToken t')

  fun matches T (Source t) (Source t') = tokenMatches T t t'
    | matches T (Loop _) (Loop _) = true (* assumes this has been checked before *)
    | matches T (Construct ({token = t, configurator = u},cs)) (Construct ({token = t', configurator = u'},cs')) =
        CSpace.sameConfigurators u u'
        andalso tokenMatches T t t'
        andalso allZip (matches T) cs cs'

  (* genertorMatches T c c' checks whether a generator of c matches the pattern c' exists*)
  fun generatorMatches T (Source t) (Source t') = tokenMatches T t t'
    | generatorMatches T (Loop _) (Loop _) = true (* assumes this has been checked before *)
    | generatorMatches T (Construct ({token = t, configurator = u},cs)) (Construct ({token = t', configurator = u'},cs')) =
        CSpace.sameConfigurators u u'
        andalso tokenMatches T t t'
        andalso allZip (generatorMatches T) cs cs'
    | generatorMatches T (Construct ({token = t, configurator = u},cs)) (Source t') =
        tokenMatches T t t'

  exception NoMatchingGenerator
  (* genertorMatches T c c' checks whether a generator of c matches the pattern c' exists*)
  fun findGeneratorMatching T (Source t) (Source t') = if tokenMatches T t t' then SOME (Source t) else NONE
    | findGeneratorMatching T (Loop t) (Loop _) = SOME (Loop t) (* assumes this has been checked before *)
    | findGeneratorMatching T (Construct ({token = t, configurator = u},cs)) (Construct ({token = t', configurator = u'},cs')) =
      if CSpace.sameConfigurators u u' andalso tokenMatches T t t'
      then
        let val CH = funZip (findGeneratorMatching T) cs cs'
            fun ss (SOME x ::t) = x :: ss t
              | ss (NONE :: t) = raise NoMatchingGenerator
              | ss [] = []
        in SOME (Construct ({token = t, configurator = u},ss CH)) handle NoMatchingGenerator => NONE
        end
      else NONE
    | findGeneratorMatching T (Construct ({token = t, configurator = u},cs)) (Source t') =
        if tokenMatches T t t' then SOME (Source t) else NONE

  (* *)
  fun findMapAndGeneratorMatching T (Source t) (Source t') =
        if tokenMatches T t t'
        then (fn x => if CSpace.sameTokens x t' then SOME t else NONE, SOME (Source t))
        else (fn x => NONE, NONE)
    | findMapAndGeneratorMatching T (Loop t) (Loop _) = (fn x => NONE, SOME (Loop t)) (* assumes this has been checked before *)
    | findMapAndGeneratorMatching T (Construct ({token = t, configurator = u},cs)) (Construct ({token = t', configurator = u'},cs')) =
        if CSpace.sameConfigurators u u' andalso tokenMatches T t t'
        then
          let val CH = funZip (findMapAndGeneratorMatching T) cs cs'
              fun ss (SOME x ::t) = x :: ss t
                | ss (NONE :: t) = raise NoMatchingGenerator
                | ss [] = []
              fun sf (f::L) x = (case f x of NONE => sf L x | SOME y => SOME y)
                | sf [] x = NONE
              fun f x = if CSpace.sameTokens x t' then SOME t else sf (map #1 CH) x
              val ch = ss (map #2 CH)
          in (f, SOME (Construct ({token = t, configurator = u}, ch))) handle NoMatchingGenerator => (fn x => NONE,NONE)
          end
        else (fn x => NONE, NONE)
    | findMapAndGeneratorMatching T (Construct ({token = t, configurator = u},cs)) (Source t') =
        if tokenMatches T t t' then (fn x => if CSpace.sameTokens x t' then SOME t else NONE, SOME (Source t)) else (fn x => NONE,NONE)

  (* Belongs in LISTS (?) *)
  fun findFirstSome [] = NONE
    | findFirstSome (NONE :: L) = findFirstSome L
    | findFirstSome (SOME x :: L) = SOME x
  fun findFirstSome' [] = (fn x => NONE,NONE)
    | findFirstSome' ((_,NONE) :: L) = findFirstSome' L
    | findFirstSome' ((f,SOME x) :: L) = (f,SOME x)

  fun findGeneratorForTokenMatching T ct t p =
      if CSpace.sameTokens t (Construction.constructOf ct) then findGeneratorMatching T (Construction.fixInducedConstruction ct) p
      else (case ct of Construct (tu, cs) => findFirstSome (map (fn c => findGeneratorForTokenMatching T c t p) cs)
                                      | _ => NONE)

  fun findMapAndGeneratorMatchingForToken T ct p t =
      if CSpace.sameTokens t (Construction.constructOf ct) then findMapAndGeneratorMatching T (Construction.fixInducedConstruction ct) p
      else (case ct of Construct (tu, cs) => findFirstSome' (map (fn x => findMapAndGeneratorMatchingForToken T x p t) cs)
                                      | _ => (fn x => NONE,NONE))

  fun trivial ty = Source (CSpace.makeToken "dummy" ty)

  fun applyPartialIsomorpism f (Source t) = (case f t of NONE => Source t | SOME x => Source x)
    | applyPartialIsomorpism f (Loop t) = (case f t of NONE => Loop t | SOME x => Loop x)
    | applyPartialIsomorpism f (Construct ({token = t, configurator = u},cs)) =
        (case f t of NONE => Construct ({token = t, configurator = u}, map (applyPartialIsomorpism f) cs)
                  | SOME x => Construct ({token = x, configurator = u}, map (applyPartialIsomorpism f) cs))

  (* The following was a failure when trying to incorporate variables function.
    Maybe it should be revisited*)
    (*
  fun vertexMatch T (Token t, ty) (Token t', ty') = (equalTokens t t' andalso TypeSystem.equal ty ty')
    | vertexMatch T (_, ty) (Var _, ty') = ((#subType T) ty ty')
    | vertexMatch _ _ _ = false;

  fun vertexMatchWhich T (Token t, ty) (Token t', ty') = (equalTokens t t' andalso TypeSystem.equal ty ty', NONE)
    | vertexMatchWhich T (t, ty) (Var v, ty') = case (#subType T) ty ty' of true => (true,SOME ((Var v,ty'),(t,ty)))
                                                                          | false => (false,NONE)
    | vertexMatchWhich _ _ _ = (false, NONE);


  fun specialises T c c' =
  let
    fun specialises_acc M T (Source t) (Source t') =
          case vertexMatchWhich T t t' of (match,NONE) => (match,M)
                                        | (match,SOME pair) => (match,pair::M)
      | specialises_acc M T (Loop t) (Loop t') = true (* this is true by default simply because the node also checked higher in the tree *)
      | specialises_acc M T (Construct {token = t, configurator = u}, []) (Construct {token = t', configurator = u'}, []) =
          case vertexMatchWhich T t t' of (false,_) => (false,M)
                                        | (true,NONE) => (true,M)
                                        | (true,SOME pair) => (true,pair::M)
      | specialises_acc M T (Construct {token = t, configurator = u}, (h::cs)) (Construct {token = t', configurator = u'}, (h'::cs')) =
          case specialises_acc M T h h' of (false,M') => (false,M')
                                         | (true,M') => specialises_acc M' T (Construct {token = t, configurator = u}, cs) (Construct {token = t', configurator = u'}, cs') end
      | specialises_acc _ _ = false

      (* The following function is incomplete. I'm sure I can do a better job from scratch. *)
    fun propagate ((Var v1,ty1),(Var v2,ty2)) ((x,y)::M) =
          if CSpace.metaEqual (Var v1,ty1) (Var v2,ty2) then ((x,y)::M)
          else case (CSpace.metaEqual (Var v1,ty1) x, CSpace.metaEqual (Var v1,ty1) y) of
                  (false,false) => (x,y)::propagate ((Var v1,ty1),(Var v2,ty2)) M
                | (true,false) => ((Var v2,ty2),y)::propagate ((Var v1,ty1),(Var v2,ty2)) M
                | (false,true) => ((Var v2,ty2),x)::propagate ((Var v1,ty1),(Var v2,ty2)) M
                | (true,true) => propagate ((Var v1,ty1),(Var v2,ty2)) M
      | propagate ((Var v1,ty1),(Token v2,ty2)) ((x,y)::M) =
          case (CSpace.metaEqual (Var v1,ty1) x, CSpace.metaEqual (Var v1,ty1) y) of
              (false,false) => (x,y)::propagate ((Var v1,ty1),(Token v2,ty2)) M
            | (true,false) => case y of (Var vy,_) => (y,(Token v2,ty2))::propagate ((Var v1,ty1),(Var v2,ty2)) M | (Token ty,tyy) =>
            | (false,true) => (x,(Token v2,ty2))::propagate ((Var v1,ty1),(Var v2,ty2)) M
            | (true,true) => propagate ((Var v1,ty1),(Var v2,ty2)) M
      | propagate ((Var v1,ty1),(Var v2,ty2)) ((x,y)::M) =
      | propagate ((Var v1,ty1),(Var v2,ty2)) ((x,y)::M) =
      | propagate _ [] = true
  in case specialises_acc [] T c c' of (false, _) => false
                                     | (true, M) => consistent M
  end*)


end
