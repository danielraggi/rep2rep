import "util.set";

signature TYPESYSTEM =
sig
  type typ
  type typeSystem = {Ty : typ Set.set, subType : typ * typ -> bool}
  exception undefined

  val typeOfString : string -> typ
  val any : typ
  val equal : typ -> typ -> bool

  val stringOfType : typ -> string;

  val reflexiveClosure : typeSystem -> typeSystem;
  val respectAnyClosure : typeSystem -> typeSystem;
  val fixSubTypeFunction : typeSystem -> typeSystem;

  (* finiteTypeSystem is only a bridge for checking things about finite type systems.
    The type used as a representation of type systems in the rest of the code is typeSystem *)
  type finiteTypeSystem = {Ty : typ FiniteSet.set, subType : typ * typ -> bool}

  val reflexive : finiteTypeSystem -> bool;
  val transitive : finiteTypeSystem -> bool;
  val antisymmetric : finiteTypeSystem -> bool;
  val respectsAny : finiteTypeSystem -> bool;

  val wellDefined : finiteTypeSystem -> bool;

  val finiteReflexiveClosure : finiteTypeSystem -> finiteTypeSystem;
  val transitiveClosure : finiteTypeSystem -> finiteTypeSystem;
  val finiteRespectAnyClosure : finiteTypeSystem -> finiteTypeSystem;
  val fixFiniteSubTypeFunction : finiteTypeSystem -> finiteTypeSystem;

end;

structure TypeSystem : TYPESYSTEM =
struct
  type typ = string;
  type typeSystem = {Ty : typ Set.set, subType : typ * typ -> bool};
  type finiteTypeSystem = {Ty : typ FiniteSet.set, subType : typ * typ -> bool};
  exception undefined;

  fun typeOfString x = x
  val any = "" (* emtpy string *)
  fun equal x y = (x = y)


  fun reflexive {Ty,subType} = FiniteSet.all (fn x => subType (x,x)) Ty;
  fun transitive {Ty,subType} = FiniteSet.all (fn x => FiniteSet.all (fn y => FiniteSet.all (fn z => not (subType (x,y) andalso subType (y,z)) orelse subType (x,z)) Ty) Ty) Ty;
  fun antisymmetric {Ty,subType} = FiniteSet.all (fn x => FiniteSet.all (fn y => not (subType (x,y) andalso subType (y,x)) orelse x = y) Ty) Ty;
  fun respectsAny {Ty,subType} = FiniteSet.all (fn x => subType (x,any)) Ty

  fun wellDefined T =
    reflexive T andalso transitive T andalso antisymmetric T;

  fun reflexiveClosure T = {Ty = #Ty T, subType = (fn (x,y) => equal x y orelse (#subType T) (x,y))}
  fun finiteReflexiveClosure T = {Ty = #Ty T, subType = (fn (x,y) => equal x y orelse (#subType T) (x,y))}

  fun transitiveClosure {Ty,subType} =
    let fun subType' (x,y) = (subType (x,y) orelse FiniteSet.exists (fn z => subType (x,z) andalso subType (z,y)) Ty)
    in if FiniteSet.all (fn x => FiniteSet.all (fn y => subType (x,y) = subType' (x,y)) Ty) Ty then {Ty = Ty, subType = subType} else transitiveClosure {Ty=Ty,subType=subType'}
    end

  fun respectAnyClosure {Ty,subType} = {Ty = Ty,subType = (fn (x,y) => (y = any orelse subType(x,y)))}
  fun finiteRespectAnyClosure {Ty,subType} = {Ty = Ty,subType = (fn (x,y) => (y = any orelse subType(x,y)))}

  val fixSubTypeFunction = respectAnyClosure o reflexiveClosure;
  val fixFiniteSubTypeFunction = finiteRespectAnyClosure o finiteReflexiveClosure o transitiveClosure;
  fun stringOfType x = x
end;
