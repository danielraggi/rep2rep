import "structure_transfer";

signature PARSE =
sig
  val list : (string -> 'a) -> string -> 'a list
  val finiteSet : (string -> ''a) -> string -> ''a FiniteSet.set
  val set : (string -> ''a) -> string -> ''a Set.set
  val typ : string -> TypeSystem.typ
  val token : string -> CSpace.token
  (*val constructor : string -> CSpace.constructor
  val configurator : string -> CSpace.configurator
  val construction : string -> Construction.construction
  val pattern : string -> Pattern.construction
  val relation : string -> Relation.T
  val relationship : string -> Relation.relationship
  val correspondence : string -> Correspondence.corr
  val knowledge : string -> Knowledge.base
  val state : string -> State.T*)
end;

structure Parse : PARSE =
struct
  fun list f s = String.splitStripApply f "," ( String.removeSquareBrackets s)
  fun finiteSet f s = FiniteSet.ofList (String.splitStripApply f "," (String.removeBraces s))
  fun set f s = Set.ofList (String.splitStripApply f "," ( String.removeBraces s))
  fun typ s = TypeSystem.typeOfString s
  fun token s = case String.breakOn ":" (String.stripSpaces s) of (ts,_,tys) => CSpace.makeToken ts (typ tys)

end;
