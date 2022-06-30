import "util.rpc";
import "core.type";
import "core.cspace";
import "core.construction";
import "oruga.document";

signature SERVER = sig
    val make: string list -> Rpc.endpoint list;
end;

structure Server: SERVER = struct

fun makeTSDescription {name=name, typeSystem=_, principalTypes=principalTypes} = (name, principalTypes);

(* They're the same, but the type system can't quite manage it... *)
fun getSpace spaces name = List.find (fn space => (#name space) = name) spaces;
fun getPrincipalTypes systems name = List.find (fn (sname, ptyps) => sname = name) systems;

val spaces_sig = ("server.spaces", unit_rpc, List.list_rpc(CSpace.conSpecData_rpc));
val getSpace_sig = ("server.getSpace", String.string_rpc, Option.option_rpc(CSpace.conSpecData_rpc));
val typeSystems_sig = ("server.typeSystems",
                       unit_rpc,
                       List.list_rpc(Rpc.Datatype.tuple2(String.string_rpc, FiniteSet.set_rpc(Type.principalType_rpc))));
val getPrincipalTypes_sig = ("server.getPrincipalTypes",
                             String.string_rpc,
                             Option.option_rpc(FiniteSet.set_rpc(Type.principalType_rpc)))

fun make files =
    let
        val docs = List.map Document.read files;
        val spaces = List.flatmap Document.conSpecsDataOf docs;
        val typeSystems = List.flatmap ((List.map makeTSDescription) o Document.typeSystemsDataOf) docs;
    in [
        Rpc.provide spaces_sig (fn () => spaces),
        Rpc.provide getSpace_sig (fn name => getSpace spaces name),
        Rpc.provide typeSystems_sig (fn () => typeSystems),
        Rpc.provide getPrincipalTypes_sig (fn name => Option.map #2 (getPrincipalTypes typeSystems name))
    ] end;

end;
