imports "type"


(* An underlying assumption of having token = string * type is that two tokens in a
  cspace are different if and only if their string type pairs are different.*)
signature CSPACE =
sig
  type constructor;
  (*datatype atom = Token of string | Variable of string;*)
  type token;(* = string * Type.typ;*)
  type configurator;

  val sameVertices : token -> token -> bool;
  val typeOfToken : token -> Type.typ;

end

structure CSpace : CSPACE =
struct
  type constructor = string * (Type.typ list * Type.typ);
  (*datatype atom = Token of string | Variable of string;*)
  type token = string * Type.typ;
  type configurator = string * constructor;

  fun sameConstructors (n,(tyL,ty)) (n',(tyL',ty')) = (n = n' andalso Type.equal ty ty' andalso allZip Type.equal tyL tyL');
  fun sameConfigurators (u,c) (u',c') = (u = u' andalso sameConstructor c c');
  fun sameTokens (t,ty) (t',ty') = (t = t' andalso Type.equal ty ty');
  fun typeOfToken (t,ty) = ty;
  (*
  fun tsystemOf (T,_,_) = T

  fun equalTokens t t' = (t = t')
  fun equalVars v v' = (v = v')



  exception Variable
  fun sameVertices (Token t,ty) (Token t',ty') = (equalTokens t t' andalso Type.equal ty ty')
    | sameVertices _ _ = raise Variable;

  fun metaEqual (Token t,ty) (Token t',ty') = (equalTokens t t' andalso Type.equal ty ty')
    | metaEqual (Var v,ty) (Var v',ty') = (equalVars v v' andalso Type.equal ty ty');
*)

end
