import "core.construction";
import "oruga.document";

fun forAaron () =
  #construction (Document.findConstructionWithName (Document.read "aarons") "aarons");

val forAaron_rpc = Rpc.provide ("aarons.forAaron", unit_rpc, Construction.construction_rpc) forAaron;
