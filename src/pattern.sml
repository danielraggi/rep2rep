import "construction"

signature PATTERN =
sig
  include CONSTRUCTIONTERM

  val matches : Type.typeSystem -> construction -> construction -> bool;
  val generatorMatches : Type.typeSystem -> construction -> construction -> bool;
  val findGeneratorMatching : Type.typeSystem -> construction -> construction -> construction option;

  val trivial : Type.typ -> construction;
end

structure Pattern : PATTERN =
struct
  open ConstructionTerm

  fun tokenMatches T t t' = (#subtype T) (CSpace.typeOfToken t,CSpace.typeOfToken t')

  fun matches T (Source t) (Source t') = tokenMatches T t t'
    | matches T (Loop _) (Loop _) = true (* assumes this has been checked before *)
    | matches T (Construct ({token = t, configurator = u},cs)) (Construct ({token = t', configurator = u'},cs')) =
        CSpace.sameConfigurator u u'
        andalso tokenMatches T t t'
        andalso allZip (matches T) cs cs'

  (* genertorMatches T c c' checks whether a generator of c matches the pattern c' exists*)
  fun generatorMatches T (Source t) (Source t') = tokenMatches T t t'
    | generatorMatches T (Loop _) (Loop _) = true (* assumes this has been checked before *)
    | generatorMatches T (Construct ({token = t, configurator = u},cs)) (Construct ({token = t', configurator = u'},cs')) =
        CSpace.sameConfigurator u u'
        andalso tokenMatches T t t'
        andalso allZip (generatorMatches T) cs cs'
    | generatorMatches T (Construct ({token = t, configurator = u},cs)) (Source t') =
        tokenMatches T t t'

  exception NoMatchingGenerator
  (* genertorMatches T c c' checks whether a generator of c matches the pattern c' exists*)
  fun findGeneratorMatching T (Source t) (Source t') = if tokenMatches T t t' then SOME (Source t)
    | findGeneratorMatching T (Loop t) (Loop _) = SOME (Loop t) (* assumes this has been checked before *)
    | findGeneratorMatching T (Construct ({token = t, configurator = u},cs)) (Construct ({token = t', configurator = u'},cs')) =
      if CSpace.sameConfigurator u u' andalso tokenMatches T t t'
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

  (* Belongs in LISTS (?) *)
  fun findFirstSome [] = NONE
    | findFirstSome (NONE :: L) = findFirstSome L
    | findFirstSome (SOME x :: L) = SOME x

  fun findGeneratorForTokenMatching T ct t p =
      if CSpace.sameTokens t (ConstructionTerm.constructOf ct) then findGeneratorMatching T ct p
      else case ct of Construct (tu, cs) => findFirstSome (map (fn c => findGeneratorForTokenMatching T c t p) cs) | _ => NONE

  fun trivial ty = Source (CSpace.makeToken "dummy" ty)

  (* The following was a failure when trying to incorporate variables function.
    Maybe it should be revisited*)
    (*
  fun vertexMatch T (Token t, ty) (Token t', ty') = (equalTokens t t' andalso Type.equal ty ty')
    | vertexMatch T (_, ty) (Var _, ty') = ((#subtype T) ty ty')
    | vertexMatch _ _ _ = false;

  fun vertexMatchWhich T (Token t, ty) (Token t', ty') = (equalTokens t t' andalso Type.equal ty ty', NONE)
    | vertexMatchWhich T (t, ty) (Var v, ty') = case (#subtype T) ty ty' of true => (true,SOME ((Var v,ty'),(t,ty)))
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
