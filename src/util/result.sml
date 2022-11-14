signature RESULT =
sig

    datatype ('ok, 'err) t = OK of 'ok | ERROR of 'err;
    val t_rpc: ('ok Rpc.Datatype.t) * ('err Rpc.Datatype.t) -> ('ok, 'err) t Rpc.Datatype.t;

    val ok: 'ok -> ('ok, 'err) t;
    val error: 'err -> ('ok, 'err) t;

    val isOk: ('ok, 'err) t -> bool;
    val isError: ('ok, 'err) t -> bool;

    val toOption: ('ok, 'err) t -> 'ok option;
    val fromOption: 'ok option -> (unit -> 'err) -> ('ok, 'err) t;

    val get: ('ok, 'err) t -> 'ok option;
    val getWithDefault: ('ok, 'err) t -> (unit -> 'ok) -> 'ok;

    val map: ('a -> 'b) -> ('a, 'err) t -> ('b, 'err) t;
    val flatmap: ('a -> ('b, 'err) t) -> ('a, 'err) t -> ('b, 'err) t;
    val app: ('ok -> unit) -> ('ok, 'err) t -> unit;
    val all: ('err list -> 'err) -> ('ok, 'err) t list -> ('ok list, 'err) t;
    val allUnit: ('err list -> 'err) -> (unit, 'err) t list -> (unit, 'err) t;

    val mapError: ('e -> 'f) -> ('ok, 'e) t -> ('ok, 'f) t;
    val thenError: ('err list -> 'err) -> ('ok, 'err) t -> (unit -> 'err) -> ('ok, 'err) t;

    val both: ('err list -> 'err) -> ('a, 'err) t * ('b, 'err) t -> ('a * 'b, 'err) t;
    val both3: ('err list -> 'err)
               -> ('a, 'err) t * ('b, 'err) t * ('c, 'err) t
               -> ('a * 'b * 'c, 'err) t;
    val both4: ('err list -> 'err)
               -> ('a, 'err) t * ('b, 'err) t * ('c, 'err) t * ('d, 'err) t
               -> ('a * 'b * 'c * 'd, 'err) t;
    val both5: ('err list -> 'err)
               -> ('a, 'err) t * ('b, 'err) t * ('c, 'err) t * ('d, 'err) t * ('e, 'err) t
               -> ('a * 'b * 'c * 'd * 'e, 'err) t;
    val both6: ('err list -> 'err)
               -> ('a, 'err) t * ('b, 'err) t * ('c, 'err) t * ('d, 'err) t * ('e, 'err) t * ('f, 'err) t
               -> ('a * 'b * 'c * 'd * 'e * 'f, 'err) t;

end;

structure Result : RESULT =
struct

datatype ('ok, 'err) t = OK of 'ok | ERROR of 'err;
fun t_rpc (ok_rpc, err_rpc) =
    Rpc.Datatype.convert
        ("(" ^ (Rpc.Datatype.name ok_rpc) ^ ", " ^ (Rpc.Datatype.name err_rpc) ^ ") Result.t")
        (Rpc.Datatype.either2 (ok_rpc, err_rpc))
        (fn (Rpc.Datatype.Either2.FST ok) => OK ok
        | (Rpc.Datatype.Either2.SND err) => ERROR err)
        (fn (OK ok) => Rpc.Datatype.Either2.FST ok
        | (ERROR err) => Rpc.Datatype.Either2.SND err);

fun ok a = OK a;
fun error e = ERROR e;

fun isOk (OK _) = true
  | isOk _ = false;
fun isError (ERROR _) = true
  | isError _ = false;

fun toOption (OK a) = SOME a
  | toOption _ = NONE;
fun fromOption (SOME a) _ = OK a
  | fromOption NONE ef = ERROR (ef());

val get = toOption;
fun getWithDefault (OK a) _ = a
  | getWithDefault _ f = f();

fun map f (OK a) = OK (f a)
  | map _ (ERROR e) = ERROR e;

fun flatmap f (OK a) = f a
  | flatmap _ (ERROR e) = ERROR e;

fun app f (OK a) = f a
  | app _ _ = ();

fun all combErr ts =
    let val result = ref [];
        val errors = ref [];
        fun f (OK a) = result := (a::(!result))
          | f (ERROR e) = errors := (e::(!errors));
        val () = List.app f ts;
    in if List.null (!errors)
       then OK (List.rev (!result))
       else ERROR ((combErr o List.rev) (!errors))
    end;

fun allUnit combErr ts = map (fn _ => ()) (all combErr ts);

fun mapError _ (OK a) = OK a
  | mapError f (ERROR e) = ERROR (f e);

fun thenError _ (OK a) ef = ERROR (ef())
  | thenError combErr (ERROR e) ef = ERROR (combErr [e, ef()]);

fun both _ (OK a, OK b) = OK (a, b)
  | both _ (OK _, ERROR e) = ERROR e
  | both _ (ERROR e, OK _) = ERROR e
  | both combErr (ERROR e, ERROR f) = ERROR (combErr [e, f]);

fun both3 _ (OK a, OK b, OK c) = OK (a, b, c)
  | both3 _ (OK _, OK _, ERROR e) = ERROR e
  | both3 _ (OK _, ERROR e, OK _) = ERROR e
  | both3 _ (ERROR e, OK _, OK _) = ERROR e
  | both3 combErr (OK _, ERROR e, ERROR f) = ERROR (combErr [e, f])
  | both3 combErr (ERROR e, OK _, ERROR f) = ERROR (combErr [e, f])
  | both3 combErr (ERROR e, ERROR f, OK _) = ERROR (combErr [e, f])
  | both3 combErr (ERROR e, ERROR f, ERROR g) = ERROR (combErr [e, f, g]);

fun both4 combErr (a, b, c, d) =
    let val r1 = both combErr (a, b);
        val r2 = both combErr (c, d);
        val r = both combErr (r1, r2);
    in map (fn ((a, b), (c, d)) => (a, b, c, d)) r end;

fun both5 combErr (a, b, c, d, e) =
    let val r1 = both3 combErr (a, b, c);
        val r2 = both combErr (d, e);
        val r = both combErr (r1, r2);
    in map (fn ((a, b, c), (d, e)) => (a, b, c, d, e)) r end;

fun both6 combErr (a, b, c, d, e, f) =
    let val r1 = both3 combErr (a, b, c);
        val r2 = both3 combErr (d, e, f);
        val r = both combErr (r1, r2);
    in map (fn ((a, b, c), (d, e, f)) => (a, b, c, d, e, f)) r end;

end;
