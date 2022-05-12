import "util.rpc";
import "core.type";
import "core.cspace";
import "core.construction";
import "oruga.document";

signature SERVER = sig
    val make: string list -> Rpc.endpoint list;
end;

structure Server: SERVER = struct

fun makeTSDescription {typeSystem=typeSystem, principalTypes=principalTypes} = {name=(#name typeSystem), principalTypes=principalTypes};

(* They're the same, but the type system can't quite manage it... *)
fun getSpace spaces name = List.find (fn space => (#name space) = name) spaces;
fun getTypesystem systems name = List.find (fn system => (#name system) = name) systems;

fun make files =
    let
        val docs = List.map Document.read files;
        val spaces = List.flatmap Document.conSpecsOf docs;
        val typesystems = List.flatmap ((List.map makeTSDescription) o Document.typeSystemsDataOf) docs;
    in [
        Rpc.provide ("server.spaces", unit_rpc, List.list_rpc(CSpace.conSpec_rpc)) (fn () => spaces),
        Rpc.provide ("server.getSpace", String.string_rpc, Option.option_rpc(CSpace.conSpec_rpc)) (fn name => getSpace spaces name),
        Rpc.provide ("server.typesystems", unit_rpc, List.list_rpc(Document.typeSystemDescription_rpc)) (fn () => typesystems),
        Rpc.provide ("server.getTypesystem", String.string_rpc, Option.option_rpc(Document.typeSystemDescription_rpc)) (fn name => getTypesystem typesystems name)
    ] end;

end;
