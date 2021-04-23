import "construction"

signature PATTERN =
sig
  include CONSTRUCTIONTERM
end

structure Pattern : PATTERN =
struct
  open ConstructionTerm

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
  end


end
