signature TYPESYSTEM =
sig
  type typ
  type Ty = typ Set.set;
  type subType = typ * typ -> bool;
  type TypeSystem = Ty * subType;
  val reflexive : TypeSystem -> bool;
  val transitive : TypeSystem -> bool;
  val antisymmetric : TypeSystem -> bool;
  val wellDefined : TypeSystem -> bool;
  val reflexiveClosure : TypeSystem -> TypeSystem;
  val transitiveClosure : TypeSystem -> TypeSystem;
end

structure TypeSystem : TYPESYSTEM =
struct
  type typ = string;
  type Ty = typ set;
  type subType = typ * typ -> bool;
  type TypeSystem = Ty * subType;

  fun reflexive (types,leq) = Set.all (fn x => leq (x,x)) types;
  fun transitive (types,leq) = Set.all (fn x => Set.all (fn y => Set.all (fn z => not (leq (x,y) andalso leq (y,z)) orelse leq (x,z)) types) types) types;
  fun antisymmetric (types,leq) = Set.all (fn x => Set.all (fn y => not (leq (x,y) andalso leq (y,x)) orelse x = y) types) types;

  fun wellDefined (types,leq) =
    reflexive (types,leq) andalso transitive (types,leq) andalso antisymmetric (types,leq);

  fun reflexiveClosure (types,leq) = (types, fn (x,y) => x = y orelse leq (x,y))
  fun transitiveClosure (types,leq) =
    let fun leq' (x,y) = (leq (x,y) orelse Set.exists (fn z => leq (x,z) andalso leq (z,y)) types)
    in if Set.all (fn x => Set.all (fn y => leq (x,y) = leq' (x,y)) types) types then (types,leq) else transitiveClosure (types,leq')
    end

end
