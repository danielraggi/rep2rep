import "util.set";

signature TYPESYSTEM =
sig
  type typ
  type typeSystem = {Ty : typ Set.set, subType : typ * typ -> bool}

  val typeOfString : string -> typ
  val any : typ
  val equal : typ -> typ -> bool

(*
  val reflexive : typeSystem -> bool;
  val transitive : typeSystem -> bool;
  val antisymmetric : typeSystem -> bool;
  val respectsAny : typeSystem -> bool;
  val wellDefined : typeSystem -> bool;

  *)
  val reflexiveClosure : typeSystem -> typeSystem;
  (*
  val transitiveClosure : typeSystem -> typeSystem;*)
  val respectAnyClosure : typeSystem -> typeSystem;
  val fixSubTypeFunction : typeSystem -> typeSystem;

  val stringOfType : typ -> string;

end;

structure TypeSystem : TYPESYSTEM =
struct
  type typ = string;
  type typeSystem = {Ty : typ Set.set, subType : typ * typ -> bool};

  fun typeOfString x = x
  val any = "" (* emtpy string *)
  fun equal x y = (x = y)

(*
  fun reflexive {Ty,subType} = Set.all (fn x => subType (x,x)) Ty;
  fun transitive {Ty,subType} = Set.all (fn x => Set.all (fn y => Set.all (fn z => not (subType (x,y) andalso subType (y,z)) orelse subType (x,z)) Ty) Ty) Ty;
  fun antisymmetric {Ty,subType} = Set.all (fn x => Set.all (fn y => not (subType (x,y) andalso subType (y,x)) orelse x = y) Ty) Ty;
  fun respectsAny {Ty,subType} = Set.all (fn x => subType x any) Ty

  fun wellDefined T =
    reflexive T andalso transitive T andalso antisymmetric T;

  fun almostWellDefined T =
    reflexive T andalso transitive T andalso antisymmetric T;
    *)

  fun reflexiveClosure T = {Ty = #Ty T, subType = (fn (x,y) => equal x y orelse (#subType T) (x,y))}
  (*)
  fun transitiveClosure {Ty,subType} =
    let fun subType' (x,y) = (subType (x,y) orelse Set.exists (fn z => subType (x,z) andalso subType (z,y)) Ty)
    in if Set.all (fn x => Set.all (fn y => subType (x,y) = subType' (x,y)) Ty) Ty then {Ty = Ty, subType = subType} else transitiveClosure {Ty=Ty,subType=subType'}
    end
    *)
  fun respectAnyClosure {Ty,subType} = {Ty = Ty,subType = (fn (x,y) => (y = any orelse subType(x,y)))}

  val fixSubTypeFunction = respectAnyClosure o reflexiveClosure;
  fun stringOfType x = x
end;
