signature typeSystem =
sig
  type typ
  type subType = typ * typ -> bool;
  type typeSystem = {Ty : typ Set.set, subtype : subType};

  val equal : typ -> typ -> bool;

  val reflexive : typeSystem -> bool;
  val transitive : typeSystem -> bool;
  val antisymmetric : typeSystem -> bool;

  val wellDefined : typeSystem -> bool;

  val reflexiveClosure : typeSystem -> typeSystem;
  val transitiveClosure : typeSystem -> typeSystem;
end

structure typeSystem : typeSystem =
struct
  type typ = string;
  type subType = typ * typ -> bool;
  type typeSystem = {Ty : typ Set.set, subtype : subType};

  fun equal x y = (x = y)

  fun reflexive {Ty,subtype} = Set.all (fn x => subtype (x,x)) Ty;
  fun transitive {Ty,subtype} = Set.all (fn x => Set.all (fn y => Set.all (fn z => not (subtype (x,y) andalso subtype (y,z)) orelse subtype (x,z)) Ty) Ty) Ty;
  fun antisymmetric {Ty,subtype} = Set.all (fn x => Set.all (fn y => not (subtype (x,y) andalso subtype (y,x)) orelse x = y) Ty) Ty;

  fun wellDefined T =
    reflexive T andalso transitive T andalso antisymmetric T;

  fun reflexiveClosure T = {Ty = #Ty T, subtype = (fn (x,y) => x = y orelse (#subtype T) (x,y))}
  fun transitiveClosure {Ty,subtype} =
    let fun subtype' (x,y) = (subtype (x,y) orelse Set.exists (fn z => subtype (x,z) andalso subtype (z,y)) Ty)
    in if Set.all (fn x => Set.all (fn y => subtype (x,y) = subtype' (x,y)) Ty) Ty then {Ty = Ty, subtype = subtype} else transitiveClosure {Ty=Ty,subtype=subtype'}
    end

end
