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
  val emptySystem : typeSystem

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

  datatype typeDAG = Node of typ * typeDAG FiniteSet.set | Leaf of typ | Ref of typ
  val subTypeDAG : typeSystemData -> typ -> typeDAG
  val superTypeDAG : typeSystemData -> typ -> typeDAG

  val greatestCommonSubType : typeSystemData
                                -> typ
                                -> typ
                                -> typ option

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

  val emptySystem = {Ty = Set.empty, subType = (fn x => false)}

  fun reflexive Ty R = FiniteSet.all (fn x => R (x,x)) Ty;

  fun transitive Ty R =
    let fun f1 x =
          let val Ty' = FiniteSet.minus Ty (FiniteSet.singleton x)
              fun f2 y =
                let fun f3 z = not (R (y,z)) orelse R (x,z)
                in not (R (x,y)) orelse FiniteSet.all f3 (FiniteSet.minus Ty' (FiniteSet.singleton y))
                end
          in FiniteSet.all f2 Ty'
          end
    in FiniteSet.all f1 Ty
    end;
  fun antisymmetric Ty R = FiniteSet.all (fn x => FiniteSet.all (fn y => x = y orelse not (R (x,y)) orelse not (R (y,x))) Ty) Ty;
  fun respectsAny Ty R = FiniteSet.all (fn x => R (x,any)) Ty

  fun wellDefined {typeSystem,principalTypes,...} =
    let val PTys = FiniteSet.map #typ principalTypes
        val {Ty,subType} = typeSystem
        fun correctPrincipalType {typ,subTypeable} =
          Set.elementOf typ Ty andalso
          (not subTypeable orelse
           (Set.elementOf ("swwedfjaetubcRANDOM:" ^ typ) Ty andalso
            FiniteSet.all (fn x => not (subType(typ,x)) orelse subType("sqkedfjatubcRANDOM:" ^ typ,x)) PTys))
    in reflexive PTys subType andalso
       transitive PTys subType andalso
       antisymmetric PTys subType andalso
       FiniteSet.all correctPrincipalType principalTypes
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

  fun closureOverFiniteSet Ty = reflexiveClosure o (transitiveClosure Ty);
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

  fun superTypes {typeSystem,principalTypes,...} ty =
    let val {Ty,subType} = typeSystem
        val pTys = FiniteSet.map #typ principalTypes
    in FiniteSet.filter (fn x => subType (ty,x)) pTys
    end

  fun subTypes {typeSystem,principalTypes,...} ty =
    let val {Ty,subType} = typeSystem
        val pTys = FiniteSet.map #typ principalTypes
    in FiniteSet.filter (fn x => subType (x,ty)) pTys
    end

  fun maximal typeSystem tys =
    let val subType = #subType typeSystem
        fun noGreaterType x = FiniteSet.all (fn y => not (subType (x,y))) tys
    in FiniteSet.filter noGreaterType tys
    end

  fun minimal typeSystem tys =
    let val subType = #subType typeSystem
        fun noLesserType x = FiniteSet.all (fn y => not (subType (y,x))) tys
    in FiniteSet.filter noLesserType tys
    end

  fun immediateSuperTypes TSD ty =
    minimal (#typeSystem TSD) (FiniteSet.filter (fn x => not (equal x ty)) (superTypes TSD ty))

  fun immediateSubTypes TSD ty =
    maximal (#typeSystem TSD) (FiniteSet.filter (fn x => not (equal x ty)) (subTypes TSD ty))

  fun superTypesIn TSD ty tys =
    let val {subType,...} = #typeSystem TSD
    in FiniteSet.filter (fn x => subType (ty,x)) tys
    end

  fun subTypesIn TSD ty tys =
    let val {subType,...} = #typeSystem TSD
    in FiniteSet.filter (fn x => subType (x,ty)) tys
    end

  fun immediateSuperTypesIn TSD ty tys =
    minimal (#typeSystem TSD) (FiniteSet.filter (fn x => not (equal x ty)) (superTypesIn TSD ty tys))

  fun immediateSubTypesIn TSD ty tys =
    maximal (#typeSystem TSD) (FiniteSet.filter (fn x => not (equal x ty)) (subTypesIn TSD ty tys))

  datatype typeDAG = Node of typ * typeDAG FiniteSet.set | Leaf of typ | Ref of typ
  fun inTypeDAG ty (Node (ty',tTs)) = equal ty ty' orelse FiniteSet.exists (inTypeDAG ty) tTs
    | inTypeDAG ty (Leaf ty') = equal ty ty'
    | inTypeDAG ty (Ref ty') = equal ty ty'

  fun superTypeDAG TSD ty =
    let fun makeDAG rtys rty =
          let val strictSuperTys = superTypesIn TSD rty (FiniteSet.filter (fn x => not (equal x rty)) rtys)
          in if FiniteSet.isEmpty strictSuperTys
             then Leaf rty
             else let val immediateSuperTys = minimal (#typeSystem TSD) strictSuperTys
                      fun mapUnless prevDAGs (isty::istys) =
                          if FiniteSet.exists (inTypeDAG isty) prevDAGs
                          then mapUnless (FiniteSet.insert (Ref isty) prevDAGs) istys
                          else mapUnless (FiniteSet.insert (makeDAG strictSuperTys isty) prevDAGs) istys
                        | mapUnless prevDAGs [] = prevDAGs
                  in Node (rty, mapUnless [] immediateSuperTys)
                  end
          end
    in makeDAG (map #typ (#principalTypes TSD)) ty
    end

  fun subTypeDAG TSD ty =
    let fun makeDAG rtys rty =
          let val strictSubTys = subTypesIn TSD rty (FiniteSet.filter (fn x => not (equal x rty)) rtys)
          in if FiniteSet.isEmpty strictSubTys
             then Leaf rty
             else let val immediateSubTys = minimal (#typeSystem TSD) strictSubTys
                      fun mapUnless prevDAGs (isty::istys) =
                          if FiniteSet.exists (inTypeDAG isty) prevDAGs
                          then mapUnless (FiniteSet.insert (Ref isty) prevDAGs) istys
                          else mapUnless (FiniteSet.insert (makeDAG strictSubTys isty) prevDAGs) istys
                        | mapUnless prevDAGs [] = prevDAGs
                  in Node (rty, mapUnless [] immediateSubTys)
                  end
          end
    in makeDAG (map #typ (#principalTypes TSD)) ty
    end

  fun supremum R s =
    FiniteSet.find (fn x => FiniteSet.all (fn y => R (y,x)) s) s

  fun greatestCommonSubType TSD ty ty' =
    let val subType = #subType (#typeSystem TSD)
    in  if subType (ty,ty') then SOME ty
        else if subType (ty',ty) then SOME ty'
        else let val stys = subTypes TSD ty
                 val stys' = subTypes TSD ty'
                 val cstys = FiniteSet.intersection stys stys'
             in supremum subType cstys
             end
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
