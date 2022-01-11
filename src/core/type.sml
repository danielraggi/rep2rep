import "util.set";

signature TYPE =
sig
  type typ
  type typeSystem = {name : string, Ty : typ Set.set, subType : typ * typ -> bool}
  exception undefined

  val typ_rpc : typ Rpc.Datatype.t;
  (* val typeSystem_rpc : typeSystem Rpc.Datatype.t; *)

  val typeOfString : string -> typ
  val any : typ
  val equal : typ -> typ -> bool

  val nameOfType : typ -> string;

  val reflexiveClosure : (typ * typ -> bool) -> (typ * typ -> bool);
  val respectAnyClosure : (typ * typ -> bool) -> (typ * typ -> bool);
  val fixSubTypeFunction : (typ * typ -> bool) -> (typ * typ -> bool);

  (* finiteType is only a bridge for checking things about finite type systems.
    The type used as a representation of type systems in the rest of the code is typeSystem *)
  type finiteTypeSystem = {name : string, Ty : typ FiniteSet.set, subType : typ * typ -> bool}

  val reflexive : finiteTypeSystem -> bool;
  val transitive : finiteTypeSystem -> bool;
  val antisymmetric : finiteTypeSystem -> bool;
  val respectsAny : finiteTypeSystem -> bool;

  val wellDefined : finiteTypeSystem -> bool;

  val transitiveClosure : typ FiniteSet.set -> (typ * typ -> bool) -> (typ * typ -> bool);
  val fixFiniteSubTypeFunction : typ FiniteSet.set -> (typ * typ -> bool) -> (typ * typ -> bool);

end;

structure Type : TYPE =
struct
  type typ = string;
  type typeSystem = {name : string, Ty : typ Set.set, subType : typ * typ -> bool};
  type finiteTypeSystem = {name : string, Ty : typ FiniteSet.set, subType : typ * typ -> bool};
  exception undefined;

  val typ_rpc = String.string_rpc;
  (* val typeSystem_rpc =  *)

  fun typeOfString x = x
  val any = "" (* emtpy string *)
  fun equal x y = (x = y)


  fun reflexive {Ty,subType,...} = FiniteSet.all (fn x => subType (x,x)) Ty;
  fun transitive {Ty,subType,...} = FiniteSet.all (fn x => FiniteSet.all (fn y => FiniteSet.all (fn z => not (subType (x,y) andalso subType (y,z)) orelse subType (x,z)) Ty) Ty) Ty;
  fun antisymmetric {Ty,subType,...} = FiniteSet.all (fn x => FiniteSet.all (fn y => not (subType (x,y) andalso subType (y,x)) orelse x = y) Ty) Ty;
  fun respectsAny {Ty,subType,...} = FiniteSet.all (fn x => subType (x,any)) Ty

  fun wellDefined T =
    reflexive T andalso transitive T andalso antisymmetric T;

  fun reflexiveClosure subType = fn (x,y) => equal x y orelse subType (x,y)

  fun transitiveClosure Ty subType =
    let fun subType' (x,y) = (subType (x,y) orelse FiniteSet.exists (fn z => subType (x,z) andalso subType (z,y)) Ty)
    in if FiniteSet.all (fn x => FiniteSet.all (fn y => subType (x,y) = subType' (x,y)) Ty) Ty then subType else transitiveClosure Ty subType'
    end

  fun respectAnyClosure subType = (fn (x,y) => (y = any orelse subType(x,y)))

  val fixSubTypeFunction = respectAnyClosure o reflexiveClosure;
  fun fixFiniteSubTypeFunction Ty = respectAnyClosure o reflexiveClosure o (transitiveClosure Ty);
  fun nameOfType x = x
end;
