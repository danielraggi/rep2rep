import "type";


(* An underlying assumption of having token = string * type is that two tokens in a
  cspace are different if and only if their string type pairs are different.*)
signature CSPACE =
sig
  type ctyp
  type constructor
  (*datatype atom = Token of string | Variable of string;*)
  type token(* = string * Type.typ;*)
  type configurator

  val makeCTyp : Type.typ list * Type.typ -> ctyp
  val makeConstructor : string * ctyp -> constructor
  val makeConfigurator : string * constructor -> configurator
  val makeToken : string -> Type.typ -> token

  val spec : constructor -> ctyp
  val nameOfConfigurator : configurator -> string;
  val nameOfConstructor : constructor -> string;
  val constructorOfConfigurator : configurator -> constructor;
  val typesOfConfigurator : configurator -> ctyp
  val sameConstructors : constructor -> constructor -> bool
  val sameConfigurators : configurator -> configurator -> bool
  val sameTokens : token -> token -> bool
  val tokensHaveSameType : token -> token -> bool
  val nameOfToken : token -> string
  val typeOfToken : token -> Type.typ
  val stringOfToken : token -> string
  val stringOfConstructor : constructor -> string
  val stringOfConfigurator : configurator -> string

end;

structure CSpace : CSPACE =
struct
  type ctyp = Type.typ list * Type.typ
  type constructor = string * ctyp
  (*datatype atom = Token of string | Variable of string;*)
  type token = string * Type.typ
  type configurator = string * constructor

  fun makeCTyp x = x
  fun makeConstructor x = x
  fun makeConfigurator x = x
  fun makeToken s ty = (s,ty)

  fun spec (s,ctyp) = ctyp
  fun nameOfConfigurator (u,_) = u
  fun nameOfConstructor (cn,_) = cn
  fun constructorOfConfigurator (_,c) = c
  fun typesOfConfigurator (u,c) = spec c

  fun sameConstructors (n,(tyL,ty)) (n',(tyL',ty')) =
    (n = n' andalso Type.equal ty ty' andalso List.allZip Type.equal tyL tyL');
  fun sameConfigurators (u,c) (u',c') = (u = u' andalso sameConstructors c c');
  fun sameTokens (t,ty) (t',ty') = (t = t' andalso Type.equal ty ty');
  fun nameOfToken (t,_) = t;
  fun typeOfToken (_,ty) = ty;
  fun tokensHaveSameType (_,ty) (_,ty') = Type.equal ty ty';

  fun stringOfToken (t,ty) = t ^ ":" ^ (Type.nameOfType ty)
  fun stringOfConstructor (c,(tys,ty)) = c ^ ":" ^ (String.stringOfList Type.nameOfType (ty::tys))
  fun stringOfConfigurator (u,cc) = u ^ ":" ^ stringOfConstructor cc
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

end;
