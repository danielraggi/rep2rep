import "core.type";


(* An underlying assumption of having token = string * type is that two tokens in a
  cspace are different if and only if their string type pairs are different.*)
signature CSPACE =
sig
  type ctyp = Type.typ list * Type.typ
  type constructor
  (*datatype atom = Token of string | Variable of string;*)
  type token(* = string * Type.typ;*)
  type configurator
  type conSpec = {name : string, typeSystem : string, constructors : constructor FiniteSet.set}

  val ctyp_rpc : ctyp Rpc.Datatype.t;
  val constructor_rpc : constructor Rpc.Datatype.t;
  val token_rpc : token Rpc.Datatype.t;
  val configurator_rpc : configurator Rpc.Datatype.t;
  val conSpec_rpc : conSpec Rpc.Datatype.t;

  val makeCTyp : Type.typ list * Type.typ -> ctyp
  val makeConstructor : string * ctyp -> constructor
  val makeConfigurator : string * constructor -> configurator
  val makeToken : string -> Type.typ -> token

  val csig : constructor -> ctyp
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
  val findConstructorWithName : string -> conSpec -> constructor option
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
  type conSpec = {name : string, typeSystem : string, constructors : constructor FiniteSet.set}

  val ctyp_rpc = Rpc.Datatype.tuple2 (List.list_rpc Type.typ_rpc, Type.typ_rpc);

  val constructor_rpc = Rpc.Datatype.tuple2 (String.string_rpc, ctyp_rpc);

  val token_rpc = Rpc.Datatype.tuple2 (String.string_rpc, Type.typ_rpc);

  val configurator_rpc = Rpc.Datatype.tuple2 (String.string_rpc, constructor_rpc);

  val conSpec_rpc = Rpc.Datatype.convert
                        (Rpc.Datatype.tuple3
                             (String.string_rpc,
                              String.string_rpc,
                              FiniteSet.set_rpc constructor_rpc))
                        (fn (n, ts, cs) => {name = n, typeSystem = ts, constructors = cs})
                        (fn {name = n, typeSystem = ts, constructors = cs} => (n, ts, cs));


  fun makeCTyp x = x
  fun makeConstructor x = x
  fun makeConfigurator x = x
  fun makeToken s ty = (s,ty)

  fun csig (s,ctyp) = ctyp
  fun nameOfConfigurator (u,_) = u
  fun nameOfConstructor (cn,_) = cn
  fun constructorOfConfigurator (_,c) = c
  fun typesOfConfigurator (u,c) = csig c

  fun sameConstructors (n,(tyL,ty)) (n',(tyL',ty')) =
    (n = n' andalso Type.equal ty ty' andalso List.allZip Type.equal tyL tyL');
  fun sameConfigurators (u,c) (u',c') = (u = u' andalso sameConstructors c c');
  fun sameTokens (t,ty) (t',ty') = (t = t' andalso Type.equal ty ty');
  fun nameOfToken (t,_) = t;
  fun typeOfToken (_,ty) = ty;
  fun tokensHaveSameType (_,ty) (_,ty') = Type.equal ty ty';

  fun findConstructorWithName s cspec =
    List.find (fn c => nameOfConstructor c = s) (#constructors cspec)
  fun stringOfToken (t,ty) = t ^ ":" ^ (Type.nameOfType ty)
  fun stringOfConstructor (c,(tys,ty)) = c ^ " : " ^ (String.stringOfList Type.nameOfType tys) ^ " -> " ^ ty
  fun stringOfConfigurator (u,cc) = u ^ ":" ^ stringOfConstructor cc

end;
