signature CONFIGURATION =
sig

    exception ArgumentError of string;

    type argspec = (string * string list * int);
    type configuration = (string * int * string option);

    (* Group given arguments according to specifications *)
    val readCommandLineArguments : argspec list -> string list -> (string * string) list;
    val getArgument : (string * string) list -> string -> string;
    val getArguments : (string * string) list -> string -> string list;
    val getArgBool : (string * string) list -> string -> bool;

    (* Load the config one way or another *)
    val configFromCommandLine : string list -> configuration;
    val configFromFile : string -> configuration;

end;


structure Configuration : CONFIGURATION =
struct

exception ArgumentError of string;

type argspec = (string * string list * int)
type configuration = (string * int * string option);

(*
argspec : label, switches, argcount
argument specs : argspec list
argument args : argument list
return : (label, argument) list
label is a string naming the argument, which is used to key the output.
switches is the list of valid switches (e.g., ["--version", "-v"]).
    Empty switches means positional (in the order given in the argspec list).
argcount is 0 for boolean, 1 for single-value, and >1 for repeated values
    Values >1 are only allowed for switches; every value needs to have a switch.
    If argcount is 0 and the argument has switches, then their presence is taken
    as truth, and their absence as false. If argcount is 0 and the argument is
    positional (has no switches) then the position must have either "true" or
    "false" exactly.
*)
fun readCommandLineArguments specs args =
    let
        val (positionalArgs, switchArgs) =
            List.partition (fn (_, x, _) => List.null x) specs;

        fun boolean name a = case (Bool.fromString a) of
                                 SOME b => (name, Bool.toString b)
                               | NONE => raise ArgumentError name;
        fun positional (name, [], count) a = (case count of
                                                  0 => boolean name a
                                                | 1 => (name, a)
                                                | _ => raise ArgumentError name)
          | positional (name, x::xs, count) a = raise ArgumentError name;
        fun switch (name, (s::ss), 0) args = (boolean name "true", args)
          | switch (name, (s::ss), _) (a::args) = ((name, a), args)
          | switch (name, _, _) _ = raise ArgumentError name;
        fun switchCase [] _ = NONE
          | switchCase ((name, s, i)::ss) a =
            let
                fun valid r y = List.exists (equals y) r
            in
                if valid s a then SOME (name, s, i) else switchCase ss a
            end;
        fun countOf (_, _, i) = i;
        val preBools =
            let
                fun switchesFalse (name, x::xs, 0) = SOME (name, "false")
                  | switchesFalse _ = NONE;
            in
                List.mapPartial switchesFalse specs
            end;

        fun parse ans _ _ [] = List.rev ans
          | parse ans [] ss (a::args) = (
            case switchCase ss a of
                NONE => raise ArgumentError ("unknown " ^ a)
              | SOME s =>
                let
                    val (v, rest) = switch s args;
                    val ss' = if countOf s < 2 then (List.remove s ss) else ss;
                in parse (v::ans) [] ss rest end)
          | parse ans (p::ps) ss (a::args) =
            case switchCase ss a of
                NONE => parse ((positional p a)::ans) ps ss args
              | SOME s =>
                let
                    val (v, rest) = switch s args;
                    val ss' = if countOf s < 2 then (List.remove s ss) else ss;
                in parse (v::ans) (p::ps) ss' rest end;
    in
        parse preBools positionalArgs switchArgs args
    end;


fun getArguments [] _ = []
  | getArguments ((k, v)::args) x = if x = k
                                    then v::(getArguments args x)
                                    else getArguments args x;

fun getArgument args x =
    case getArguments args x of
        [v] => v
      | _ => raise ArgumentError x;

fun getArgBool args x =
    case getArguments args x of
        [v] => (case Bool.fromString v of
                    SOME b => b
                  | NONE => raise ArgumentError x)
      | _ => raise ArgumentError x;

fun readConstruction cts = cts

fun readLimit l = case (Int.fromString l) of
                      SOME k => if (k >= ~1) then k else raise ArgumentError l
                    | NONE => raise ArgumentError l;

fun configFromCommandLine rawArgs =
    let
        val argspec = [("construction", [], 1),
                       ("corr directory", ["--corrs"], 2)];
        val args = readCommandLineArguments argspec rawArgs;
        val ct = readConstruction (getArgument args "construction");
        val limit = readLimit (getArgument args "transfer limit");
        val corrDir = SOME (getArgument args "corr directory")
                       handle ArgumentError _ => NONE;
    in
        (ct, limit, corrDir)
    end;

fun configFromFile filename = raise ArgumentError "File reading unavailable";

end;
