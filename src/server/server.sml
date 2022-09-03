import "util.rpc";
import "core.type";
import "core.cspace";
import "core.construction";
import "transfer.structure_transfer";
import "oruga.document";
import "server.renderers";

signature SERVER = sig
    val make: string list -> Rpc.endpoint list;
end;

structure Server: SERVER = struct

fun makeTSDescription {name=name, typeSystem=_, principalTypes=principalTypes} = (name, principalTypes);

fun getSpace spaces name = List.find (fn space => (#name space) = name) spaces;

fun getPrincipalTypes systems name =
    Option.map #principalTypes
               (List.find (fn {name=sname, principalTypes=_, ...} => sname = name) systems);

fun getTypeContext systems name typ =
    let fun makeEdges (Type.Ref _) = []
          | makeEdges (Type.Leaf _) = []
          | makeEdges (Type.Node (t, cs)) =
            let val cs = FiniteSet.listOf cs;
                fun mkedge (Type.Ref u) = [(t, u)]
                  | mkedge (Type.Leaf u) = [(t, u)]
                  | mkedge (Type.Node (u, cs')) = (t, u)::(List.flatmap makeEdges cs');
            in List.flatmap mkedge cs end;
        val system = List.find (fn {name=sname, ...} => sname = name) systems;
        val above = Option.map (fn s => Type.superTypeDAG s typ) system;
        val below = Option.map (fn s => Type.subTypeDAG s typ) system;
        val edgesAbove = Option.map makeEdges above;
        val edgesBelow = Option.map ((map flip) o makeEdges) below;
    in case (edgesAbove, edgesBelow) of
           (SOME a, SOME b) => List.revAppend (a, b)
         | _ =>  []
    end;

fun guessInterSpaceName srcSpaceName tgtSpaceName =
    let val dropGAndCapitalize = String.implode
                                 o (fn x::xs => (Char.toUpper x)::xs | ys => ys)
                                 o List.rev
                                 o (fn (#"G"::xs) => xs | ys => ys)
                                 o List.rev
                                 o String.explode;
        val s = dropGAndCapitalize srcSpaceName;
        val t = dropGAndCapitalize tgtSpaceName;
    in "inter" ^ s ^ t end;

(* Huge hack, we assume it's "encode" *)
fun mkGoal constr interSpace =
    let val construct = Construction.constructOf constr;
        val encodeConstructor = FiniteSet.find (fn c => "encode" = CSpace.nameOfConstructor c) (#constructors interSpace);
        val types = Option.map CSpace.csig encodeConstructor;
        val (inTypes, outType) = case types of
                                     SOME((ins, out)) => (SOME(ins),SOME(out))
                                   | NONE => (NONE, NONE)
        val tgt_type = case inTypes of
                           SOME([_, t]) => SOME(t)
                         | _ =>  NONE
        val trueTok = Option.map (CSpace.makeToken "true") outType;
        val dummy = Option.map (CSpace.makeToken "tok") tgt_type;
    in case (encodeConstructor, trueTok, dummy) of
           (SOME(encodeConstructor), SOME(trueTok), SOME(dummy)) =>
           SOME(Construction.TCPair(
                     {token = trueTok, constructor = encodeConstructor},
                     [Construction.Source(construct), Construction.Source(dummy)]))
         | _ => NONE
    end;

fun transfer constr srcSpaceName tgtSpaceName spaces knowledge =
    let val srcSpace = getSpace spaces srcSpaceName;
        val tgtSpace = getSpace spaces tgtSpaceName;
        val intSpace = getSpace spaces (guessInterSpaceName srcSpaceName tgtSpaceName);
        val goal = Option.mapPartial (mkGoal constr) intSpace;
    in case (srcSpace, tgtSpace, intSpace, goal) of
           (SOME(s), SOME(t), SOME(i), SOME(g)) => Transfer.applyTransfer s t i knowledge constr g
        | _ => [] end;

val spaces_sig = ("server.spaces", unit_rpc, List.list_rpc(CSpace.conSpecData_rpc));
val getSpace_sig = ("server.getSpace", String.string_rpc, Option.option_rpc(CSpace.conSpecData_rpc));
val typeSystems_sig = ("server.typeSystems",
                       unit_rpc,
                       List.list_rpc(Rpc.Datatype.tuple2(String.string_rpc, FiniteSet.set_rpc(Type.principalType_rpc))));
val getPrincipalTypes_sig = ("server.getPrincipalTypes",
                             String.string_rpc,
                             Option.option_rpc(FiniteSet.set_rpc(Type.principalType_rpc)));
val getTypeContext_sig = ("server.getTypeContext",
                          Rpc.Datatype.tuple2 (String.string_rpc, Type.typ_rpc),
                          List.list_rpc (Rpc.Datatype.tuple2 (Type.typ_rpc, Type.typ_rpc)));
val renderers_sig = ("server.renderers",
                     unit_rpc,
                     List.list_rpc(Rpc.Datatype.tuple2 (String.string_rpc, String.string_rpc)));
val transfer_sig = ("server.transfer",
                    Rpc.Datatype.tuple3 (Construction.construction_rpc, String.string_rpc, String.string_rpc),
                    List.list_rpc Construction.construction_rpc);

fun make files =
    let
        val docs = List.map Document.read files;
        val spaces = List.flatmap Document.conSpecsDataOf docs;
        val typeSystems = List.flatmap Document.typeSystemsDataOf docs;
        val knowledge = List.foldl (fn (doc, kb) => Knowledge.join kb (Document.knowledgeOf doc)) Knowledge.empty docs;
    in [
        Rpc.provide spaces_sig (fn () => spaces),
        Rpc.provide getSpace_sig (fn name => getSpace spaces name),
        Rpc.provide typeSystems_sig (fn () => map makeTSDescription typeSystems),
        Rpc.provide renderers_sig (fn () => map (mapsnd Rpc.endpointName) Renderers.all),
        Rpc.provide getPrincipalTypes_sig (fn name => getPrincipalTypes typeSystems name),
        Rpc.provide getTypeContext_sig (fn (systemName, typ) => getTypeContext typeSystems systemName typ),
        Rpc.provide transfer_sig (fn (constr, srcSpace, tgtSpace) => transfer constr srcSpace tgtSpace spaces knowledge),
        Construction.R.toString
    ] @ map #2 Renderers.all end;

end;
