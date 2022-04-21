import "util.rpc";
import "core.type";
import "core.cspace";
import "core.construction";
import "oruga.document";

fun forAaron () =
  #construction (Document.findConstructionWithName (Document.read "aarons") "aarons");

fun demoSpaces () =
    [
      {name="monoid",
       typeSystem="trivial",
       constructors=FiniteSet.ofList [
           CSpace.makeConstructor ("app", ([Type.typeOfString "t", Type.typeOfString "t"], Type.typeOfString "t"))
      ]}
    ]

val forAaron_rpc = Rpc.provide ("aarons.forAaron", unit_rpc, Construction.construction_rpc) forAaron;
val demoSpaces_rpc = Rpc.provide("aarons.demoSpaces", unit_rpc, List.list_rpc(CSpace.conSpec_rpc)) demoSpaces;
