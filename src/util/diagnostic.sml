signature DIAGNOSTIC =
sig

    datatype kind = ERROR | INFORMATION;
    type token_id = string;
    type t;

    val t_rpc: t Rpc.Datatype.t;

    val create: kind -> string -> token_id list -> t;

    val kind: t -> kind;
    val affectedTokens: t -> token_id list;
    val message: t -> string;
end;

structure Diagnostic: DIAGNOSTIC =
struct

datatype kind = ERROR | INFORMATION;
type token_id = string;
type t = {
    kind: kind,
    message: string,
    affectedTokens: token_id list
};

val kind_rpc = Rpc.Datatype.convert
                   "Diagnostic.kind"
                   (Rpc.Datatype.either2 (unit_rpc, unit_rpc))
                   (fn (Rpc.Datatype.Either2.FST ()) => ERROR
                   |(Rpc.Datatype.Either2.SND ()) => INFORMATION)
                   (fn ERROR => Rpc.Datatype.Either2.FST ()
                   | INFORMATION => Rpc.Datatype.Either2.SND ());

val t_rpc = Rpc.Datatype.convert
                "Diagnostic.t"
                (Rpc.Datatype.tuple3 (kind_rpc,
                                      String.string_rpc,
                                      List.list_rpc String.string_rpc))
                (fn (k, m, t) => {kind=k, message=m, affectedTokens=t})
                (fn {kind=k, message=m, affectedTokens=t} => (k, m, t));

fun create kind message affectedTokens = {
    kind=kind,
    message=message,
    affectedTokens=affectedTokens
};

val kind = #kind;
val affectedTokens = #affectedTokens;
val message = #message;

end;
