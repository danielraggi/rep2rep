(*
taken from Robin's robinlib.sml - created by Aaron Stockdill

rep2replib.sml

Define some useful things for the whole rep2rep system.
Names that contain trailing double underscores are provided only for convenience,
and are in no way guaranteed to be available or consistent.

*)

signature REP2REPLIB =
sig
    val import : string -> unit;
    val imported__ : unit -> string list;
    val imported__asFilenames__ : unit -> string list;
    val spread : ('a -> 'b) -> ('a * 'a) -> ('b * 'b);
    val flip : ('a * 'b) -> ('b * 'a);
    val allZip : ('a * 'b -> bool) -> 'a list -> 'b list -> bool
    val funZip : ('a * 'b -> 'c) -> 'a list -> 'b list -> 'c list
end;


structure Rep2RepLib : REP2REPLIB =
struct

val IMPORTING_STACK_ : string list ref = ref [];

val IMPORTED_ : string list ref = ref ["util.rep2replib"];

fun makeFilename str =
    let
        fun subDots s = String.implode
                            (map (fn c => if c = #"." then #"/" else c)
                                 (String.explode s));
    in
        BASE ^ (subDots str) ^ ".sml"
    end;


fun imported__ () = List.rev (!IMPORTED_);
fun imported__asFilenames__ () =
    map makeFilename (imported__ ());

fun import filename =
    if (List.exists (fn s => s = filename) ((!IMPORTING_STACK_) @ (!IMPORTED_)))
    then ()(* filename has already been imported *)
    else (
        IMPORTING_STACK_ := filename :: (!IMPORTING_STACK_);
        use (makeFilename filename);
        IMPORTED_ := (List.hd (!IMPORTING_STACK_))::(!IMPORTED_);
        IMPORTING_STACK_ := List.tl (!IMPORTING_STACK_)
    ) handle e => (IMPORTING_STACK_ := List.tl (!IMPORTING_STACK_); raise e);


fun spread f (a, b) = (f a, f b);

fun flip (a, b) = (b, a);


fun allZip _ [] [] = true
  | allZip f (h::t) (h'::t') = f h h' andalso allZip f t t'
  | allZip _ _ _ = false

fun funZip _ [] [] = []
  | funZip f (h::t) (h'::t') = f h h' :: funZip f t t'
  | funZip _ _ _ = raise Match
end;
