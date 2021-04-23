imports "type"

signature CSPACE =
sig
  type constructor;
  type spec;
  datatype atom = Token of string | Variable of string;
  type vertex = atom * Type.typ;
  type cspec = (constructor Set.set, spec)

  val sameVertices : vertex -> vertex -> bool;
  val vertexMatch : Type.typeSystem -> vertex -> vertex -> bool

end

structure CSpace : CSPACE =
struct
  type constructor;
  type spec = constructor -> Type.T list * Type.T ;
  datatype atom = Token of string | Variable of string;
  type vertex = atom * Type.typ;

  fun tsystemOf (T,_,_) = T

  fun equalTokens t t' = (t = t')
  fun equalVars v v' = (v = v')

  exception Variable
  fun sameVertices (Token t,ty) (Token t',ty') = (equalTokens t t' andalso Type.equal ty ty')
    | sameVertices _ _ = raise Variable;

  fun metaEqual (Token t,ty) (Token t',ty') = (equalTokens t t' andalso Type.equal ty ty')
    | metaEqual (Var v,ty) (Var v',ty') = (equalVars v v' andalso Type.equal ty ty');

end
