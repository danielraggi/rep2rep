import "util.set";

signature TYPE =
sig
  type typ
  type principalType = {typ : typ, subTypeable : bool}
  type typeSystem = {Ty : typ Set.set, subType : typ * typ -> bool}
  type typeSystemData = {name : string,
                         typeSystem : typeSystem,
                         principalTypes : principalType FiniteSet.set}
  exception undefined

  val typ_rpc : typ Rpc.Datatype.t;
  val principalType_rpc : principalType Rpc.Datatype.t
  (* val typeSystem_rpc : typeSystem Rpc.Datatype.t; *)

  val fromString : string -> typ
  val any : typ
  val equal : typ -> typ -> bool

  val nameOfType : typ -> string;

  val reflexiveClosure : (typ * typ -> bool) -> (typ * typ -> bool);
  val respectAnyClosure : (typ * typ -> bool) -> (typ * typ -> bool);

  (* finiteType is only a bridge for checking things about finite type systems.
    The type used as a representation of type systems in the rest of the code is typeSystem *)
  type finiteTypeSystem = {name : string, Ty : typ FiniteSet.set, subType : typ * typ -> bool}

  val reflexive : typ FiniteSet.set -> (typ * typ -> bool) -> bool;
  val transitive : typ FiniteSet.set -> (typ * typ -> bool) -> bool;
  val antisymmetric : typ FiniteSet.set -> (typ * typ -> bool) -> bool;
  val respectsAny : typ FiniteSet.set -> (typ * typ -> bool) -> bool;

  val wellDefined : typeSystemData -> bool;

  val transitiveClosure : typ FiniteSet.set -> (typ * typ -> bool) -> (typ * typ -> bool);
  val closureOverFiniteSet : typ FiniteSet.set -> (typ * typ -> bool) -> (typ * typ -> bool);

  val fixForSubtypeable : typ FiniteSet.set -> (typ * typ -> bool) -> (typ * typ -> bool)
  val insertPrincipalType : principalType -> principalType FiniteSet.set -> principalType FiniteSet.set

  val addLeastCommonSuperType : {typeSystem : typeSystem, principalTypes : principalType FiniteSet.set}
                                -> typ
                                -> typ
                                -> typ * {typeSystem : typeSystem, principalTypes : principalType FiniteSet.set}
end;

structure Type : TYPE =
struct
  type typ = string;
  type principalType = {typ : typ, subTypeable : bool}
  type typeSystem = {Ty : typ Set.set, subType : typ * typ -> bool};
  type finiteTypeSystem = {name : string, Ty : typ FiniteSet.set, subType : typ * typ -> bool};
  type typeSystemData = {name : string,
                         typeSystem : typeSystem,
                         principalTypes : principalType FiniteSet.set}
  exception undefined;

  val typ_rpc = Rpc.Datatype.alias "Type.typ" String.string_rpc;
  val principalType_rpc = Rpc.Datatype.convert
                              "Type.principalType"
                              (Rpc.Datatype.tuple2 (typ_rpc, Bool.bool_rpc))
                              (fn (typ, subTypeable) => {typ=typ, subTypeable=subTypeable})
                              (fn {typ, subTypeable} => (typ, subTypeable));
  (* val typeSystem_rpc =  *)

  fun fromString x = x
  val any = "" (* emtpy string *)
  fun equal x y = (x = y)


  fun reflexive Ty R = FiniteSet.all (fn x => R (x,x)) Ty;
  fun transitive Ty R = FiniteSet.all (fn x => FiniteSet.all (fn y => FiniteSet.all (fn z => not (R (x,y) andalso R (y,z)) orelse R (x,z)) Ty) Ty) Ty;
  fun antisymmetric Ty R = FiniteSet.all (fn x => FiniteSet.all (fn y => not (R (x,y) andalso R (y,x)) orelse x = y) Ty) Ty;
  fun respectsAny Ty R = FiniteSet.all (fn x => R (x,any)) Ty

  fun wellDefined {typeSystem,principalTypes,...} =
    let val Tys = FiniteSet.map #typ principalTypes
        val R = #subType typeSystem
    in reflexive Tys R andalso transitive Tys R andalso antisymmetric Tys R
    end

  fun reflexiveClosure R = fn (x,y) => equal x y orelse R (x,y)

  fun transitiveClosure Ty R =
    let fun R' (x,y) = R (x,y) orelse
                      FiniteSet.exists (fn z => R (x,z) andalso R (z,y)) Ty
    in if FiniteSet.all (fn x => FiniteSet.all (fn y => R (x,y) = R' (x,y)) Ty) Ty
       then R
       else transitiveClosure Ty R'
    end

  fun respectAnyClosure R = (fn (x,y) => (equal y any orelse R (x,y)))

  fun closureOverFiniteSet Ty = respectAnyClosure o reflexiveClosure o (transitiveClosure Ty);
  fun nameOfType x = x

  (* assumes subType is an order for the principal types and extends it to
    the ones hanging from subtypeable *)
  fun fixForSubtypeable Tys subType (x,y) =
  let
    fun subTypeOf_y_FromWhich_x_Hangs w =
      subType (w, y) andalso
      String.isSuffix (":" ^ w) x
  in
    subType (x,y) orelse
    FiniteSet.exists subTypeOf_y_FromWhich_x_Hangs Tys
  end

  fun insertPrincipalType pt P =
    if #subTypeable pt then
      FiniteSet.insert pt (FiniteSet.filter (fn x => #typ x <> #typ pt) P)
    else
      if FiniteSet.exists (fn x => #typ x = #typ pt) P then P
      else FiniteSet.insert pt P


  fun superTypes {typeSystem,principalTypes} ty =
    let val {Ty,subType} = typeSystem
        val pTys = map #typ principalTypes
    in FiniteSet.filter (fn typ => subType (ty,typ)) pTys
    end

  fun addLeastCommonSuperType (TP as {typeSystem,principalTypes}) ty ty' =
    let val {Ty,subType} = typeSystem
        val spTys = superTypes TP ty
        val spTys' = superTypes TP ty'
        val commonSuperTypes = FiniteSet.intersection spTys spTys'
        val (new,lcspt) =
              if FiniteSet.elementOf ty commonSuperTypes then (false, ty)
              else if FiniteSet.elementOf ty' commonSuperTypes then (false, ty')
              else (true, fromString ("leastCommonSuperType(" ^ (nameOfType ty) ^ "," ^ (nameOfType ty') ^ ")"))
        val updatedTy = if new then Set.insert lcspt Ty else Ty
        fun updatedSubType (x,y) =
              if new
              then if y = lcspt
                   then subType (x,ty) orelse subType (x,ty')
                   else if x = lcspt
                        then FiniteSet.elementOf y commonSuperTypes
                        else subType (x,y)
              else subType (x,y)
        val updatedTypeSystem = {Ty = updatedTy, subType = updatedSubType}
        val updatedPrincipalTypes =
              if new
              then insertPrincipalType {typ = lcspt,subTypeable = false} principalTypes
              else principalTypes
    in (lcspt,{typeSystem = updatedTypeSystem, principalTypes = updatedPrincipalTypes})
    end
end;
