
signature LOGGING =
sig

    val write : string -> unit;
    val error : string -> unit;

    val enable : unit -> unit;
    val disable : unit -> unit;

    val close : unit -> unit;

    val logStream : TextIO.outstream -> unit;
    val errStream : TextIO.outstream -> unit;

    val indent : unit -> unit;
    val indentBy : int -> unit;
    val dedent : unit -> unit;
    val dedentBy : int -> unit;

end;

structure Logging : LOGGING =
struct

val logStream_ = ref TextIO.stdOut;
val errStream_ = ref TextIO.stdErr;
val enabled = ref false;
val indentDepth = ref 0;

fun put stream s =
    let
        val indent = String.implode (List.tabulate (4 * !indentDepth, fn _ => #" "));
    in
        if (!enabled)
        then TextIO.output (stream, indent ^ s)
        else ()
    end;

fun write s = put (!logStream_) s;
fun error s = put (!errStream_) s;


fun enable () = enabled := true;
fun disable () = enabled := false;

fun close () = (
    TextIO.closeOut (!logStream_);
    TextIO.closeOut (!errStream_)
)

fun logStream s = logStream_ := s;
fun errStream s = errStream_ := s;

fun indentBy i = indentDepth := !indentDepth + i;
fun indent () = indentBy 1;

fun dedentBy i = indentBy (~i);
fun dedent () = dedentBy 1;

end;
