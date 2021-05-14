imports "type"


(* An underlying assumption of having token = string * type is that two tokens in a
  cspace are different if and only if their string type pairs are different.*)
signature CSPACE =
sig
  type constructor;
  (*datatype atom = Token of string | Variable of string;*)
  type token;(* = string * TypeSystem.typ;*)
  type configurator;

  val makeToken : string -> TypeSystem.typ -> token;
  val sameConstructors : constructor -> constructor -> bool;
  val sameConfigurators : configurator -> configurator -> bool;
  val sameTokens : token -> token -> bool;
  val nameOfToken : token -> string;
  val typeOfToken : token -> TypeSystem.typ;

end

structure CSpace : CSPACE =
struct
  type constructor = string * (TypeSystem.typ list * TypeSystem.typ);
  (*datatype atom = Token of string | Variable of string;*)
  type token = string * TypeSystem.typ;
  type configurator = string * constructor;

  fun makeToken s ty = (s,ty)

  fun sameConstructors (n,(tyL,ty)) (n',(tyL',ty')) = (n = n' andalso TypeSystem.equal ty ty' andalso allZip TypeSystem.equal tyL tyL');
  fun sameConfigurators (u,c) (u',c') = (u = u' andalso sameConstructors c c');
  fun sameTokens (t,ty) (t',ty') = (t = t' andalso TypeSystem.equal ty ty');
  fun nameOfToken (t,_) = t;
  fun typeOfToken (_,ty) = ty;
  (*
  fun tsystemOf (T,_,_) = T

  fun equalTokens t t' = (t = t')
  fun equalVars v v' = (v = v')



  exception Variable
  fun sameVertices (Token t,ty) (Token t',ty') = (equalTokens t t' andalso TypeSystem.equal ty ty')
    | sameVertices _ _ = raise Variable;

  fun metaEqual (Token t,ty) (Token t',ty') = (equalTokens t t' andalso TypeSystem.equal ty ty')
    | metaEqual (Var v,ty) (Var v',ty') = (equalVars v v' andalso TypeSystem.equal ty ty');
*)

end
