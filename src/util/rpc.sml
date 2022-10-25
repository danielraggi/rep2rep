(*
rpc.sml

Provide a common serialisation format and means of communicating between processes.
The Rpc.Datatype structure gives the primitive building blocks of the serialisation format,
on which more elaborate datatypes can be built. The main method of doing so is composing
tuple and either types, then using "convert".
The Rpc structure also provides a way to create and start an RPC server, as well as provide
the endpoints that consumers might like to connect to.

While this structure allows for providing and calling RPC endpoints, it is primarily targetted
at providing endpoints. The "calling" end is from JavaScript/ReScript, located elsewhere.
The serialisation format must be kept in sync between the two languages.
*)

import "util.http";

signature RPC = sig

    exception RpcError;
    type data

    structure Datatype : sig
                  type 'a t

                  structure Either2 : sig
                                datatype ('a, 'b) t = FST of 'a
                                                    | SND of 'b

                            end;
                  structure Either3: sig
                                datatype ('a, 'b, 'c) t = FST of 'a
                                                        | SND of 'b
                                                        | THD of 'c
                            end;
                  structure Either4: sig
                                datatype ('a, 'b, 'c, 'd) t = FST of 'a
                                                            | SND of 'b
                                                            | THD of 'c
                                                            | FOR of 'd
                            end;
                  structure Either5: sig
                                datatype ('a, 'b, 'c, 'd, 'e) t = FST of 'a
                                                                | SND of 'b
                                                                | THD of 'c
                                                                | FOR of 'd
                                                                | FIF of 'e
                            end;
                  structure Either6: sig
                                datatype ('a, 'b, 'c, 'd, 'e, 'f) t = FST of 'a
                                                                    | SND of 'b
                                                                    | THD of 'c
                                                                    | FOR of 'd
                                                                    | FIF of 'e
                                                                    | SIX of 'f
                            end;

                  val read: 'a t -> data -> 'a
                  val write: 'a t -> 'a -> data
                  val name: 'a t -> string

                  (* convert: new_name -> old -> old_to_new -> new_to_old -> new *)
                  val convert: string -> 'a t -> ('a -> 'b) -> ('b -> 'a) -> 'b t
                  val alias: string -> 'a t -> 'a t

                  (* If the datatype is recursive, guard the recursion inside `recur`
                     and a unit function. *)
                  val recur: (unit -> 'a t) -> 'a t

                  val unit: unit t
                  val bool: bool t
                  val int: int t
                  val real: real t
                  val string: string t
                  val option: 'a t -> 'a option t
                  val list: 'a t -> 'a list t

                  val tuple2: ('a t * 'b t) -> ('a * 'b) t
                  val tuple3: ('a t * 'b t * 'c t) -> ('a * 'b * 'c) t
                  val tuple4: ('a t * 'b t * 'c t * 'd t) -> ('a * 'b * 'c * 'd) t
                  val tuple5: ('a t * 'b t * 'c t * 'd t * 'e t) -> ('a * 'b * 'c * 'd * 'e) t
                  val tuple6: ('a t * 'b t * 'c t * 'd t * 'e t * 'f t) -> ('a * 'b * 'c * 'd * 'e * 'f) t
                  val tupleN: int -> data list t

                  val either2: ('a t * 'b t) -> ('a, 'b) Either2.t t
                  val either3: ('a t * 'b t * 'c t) -> ('a, 'b, 'c) Either3.t t
                  val either4: ('a t * 'b t * 'c t * 'd t) -> ('a, 'b, 'c, 'd) Either4.t t
                  val either5: ('a t * 'b t * 'c t * 'd t * 'e t) -> ('a, 'b, 'c, 'd, 'e) Either5.t t
                  val either6: ('a t * 'b t * 'c t * 'd t * 'e t * 'f t) -> ('a, 'b, 'c, 'd, 'e, 'f) Either6.t t
                  val eitherN: (int * data) t
              end

    type ('a, 'b) functype = string * 'a Datatype.t * 'b Datatype.t
    type endpoint
    type service

    val endpointName: endpoint -> string;

    (* create: address * port -> service *)
    val create: (string * int) -> service

    (* provide: signature * function -> endpoint *)
    val provide: ('a, 'b) functype -> ('a -> 'b) -> endpoint
    (* require: service -> signature -> function *)
    val require: service -> ('a, 'b) functype -> ('a -> 'b)

    val serve: service -> endpoint list -> unit
end;


structure Rpc : RPC = struct

exception RpcError;

type data = Word8Vector.vector

structure Datatype = struct
type 'a t = {
    reader: data -> 'a,
    writer: 'a -> data,
    name: string
}

structure Either2 = struct
datatype ('a, 'b) t = FST of 'a
                    | SND of 'b
end
structure Either3 = struct
datatype ('a, 'b, 'c) t = FST of 'a
                        | SND of 'b
                        | THD of 'c
end;
structure Either4 = struct
datatype ('a, 'b, 'c, 'd) t = FST of 'a
                            | SND of 'b
                            | THD of 'c
                            | FOR of 'd
end;
structure Either5 = struct
datatype ('a, 'b, 'c, 'd, 'e) t = FST of 'a
                                | SND of 'b
                                | THD of 'c
                                | FOR of 'd
                                | FIF of 'e
end;
structure Either6 = struct
datatype ('a, 'b, 'c, 'd, 'e, 'f) t = FST of 'a
                                    | SND of 'b
                                    | THD of 'c
                                    | FOR of 'd
                                    | FIF of 'e
                                    | SIX of 'f
end;



fun read t d = (#reader t) d;
fun write t d = (#writer t) d;
fun name t = #name t

fun convert new_name t read_conv write_conv = {
    reader = fn bytes => read_conv (read t bytes),
    writer = fn x => write t (write_conv x),
    name = new_name
}

fun alias new_name {reader, writer, name} = {reader = reader,
                                             writer = writer,
                                             name = new_name}

fun recur f = {
    reader = fn bytes => (#reader (f ())) bytes,
    writer = fn value => (#writer (f ())) value,
    name = "<rec>"
}

val empty = Word8Vector.fromList [];

val unit = {
    reader = fn _ => (),
    writer = fn _ => empty,
    name = "unit"
};

val bool = {
    reader = fn w => case Word8.toInt (Word8Vector.sub (w, 0)) of
                         1 => true
                       | 0 => false
                       | _ => raise RpcError,
    writer = fn b => case b of
                         true => Word8Vector.fromList [Word8.fromInt 1]
                       | false => Word8Vector.fromList [Word8.fromInt 0],
    name = "bool"
}

val int =
    let (* Assuming 64-bit / 8-byte ints *)
        fun packInt i =
            let fun shift (i, s) = IntInf.toInt (IntInf.~>> (IntInf.fromInt i, Word.fromInt s))
                val b1 = Word8.fromInt i;
                val b2 = Word8.fromInt (shift (i, 8));
                val b3 = Word8.fromInt (shift (i, 16));
                val b4 = Word8.fromInt (shift (i, 24));
                val b5 = Word8.fromInt (shift (i, 32));
                val b6 = Word8.fromInt (shift (i, 40));
                val b7 = Word8.fromInt (shift (i, 48));
                val b8 = Word8.fromInt (shift (i, 56));
            in Word8Vector.fromList [b8, b7, b8, b5, b4, b3, b2, b1] end;
        fun unpackInt v =
            let val b1 = (Word8.toInt o Word8Vector.sub) (v, 7);
                val b2 = (Word8.toInt o Word8Vector.sub) (v, 6);
                val b3 = (Word8.toInt o Word8Vector.sub) (v, 5);
                val b4 = (Word8.toInt o Word8Vector.sub) (v, 4);
                val b5 = (Word8.toInt o Word8Vector.sub) (v, 3);
                val b6 = (Word8.toInt o Word8Vector.sub) (v, 2);
                val b7 = (Word8.toInt o Word8Vector.sub) (v, 1);
                val b8 = (Word8.toInt o Word8Vector.sub) (v, 0);
                fun unshift (i, s) = IntInf.toInt (IntInf.<< (IntInf.fromInt i, Word.fromInt s));
            in b1 +
               (unshift (b2, 8)) +
               (unshift (b3, 16)) +
               (unshift (b4, 24)) +
               (unshift (b5, 32)) +
               (unshift (b6, 40)) +
               (unshift (b7, 48)) +
               (unshift (b8, 56))
            end;
    in {
        reader = unpackInt,
        writer = packInt,
        name = "int"
    } end;

val real = {
    reader = PackRealBig.fromBytes,
    writer = PackRealBig.toBytes,
    name = "real"
};

val string = {
    reader = Byte.bytesToString,
    writer = Byte.stringToBytes,
    name = "string"
};

fun getBytes vect start len =
    Word8Vector.tabulate (len, (fn i => Word8Vector.sub (vect, i + start)));

fun tupleN n =
    let fun readTuple bytes =
            let fun readLens 0 _ ans = List.rev ans
                  | readLens n offset ans =
                    let val len = read int (getBytes bytes offset 8);
                    in readLens (n - 1) (offset + 8) (len::ans) end;
                fun readVals [] _ ans = List.rev ans
                  | readVals (len::lens) offset ans =
                    let val bytes = getBytes bytes offset len;
                    in readVals lens (offset + len) (bytes::ans) end;
                val lens = readLens n 0 [];
                val bytes = readVals lens (8 * n) [];
            in bytes end;
        fun writeTuple bytelist =
            let val lens = List.map ((write int) o Word8Vector.length) bytelist;
            in Word8Vector.concat (lens @ bytelist) end;
    in {
        reader = readTuple,
        writer = writeTuple,
        name = "tuple"
    } end;

fun tuple2 (at, bt) =
    convert (String.concat ["(", name at, " * ", name bt, ")"])
            (tupleN 2)
            (fn [a, b] => (read at a, read bt b)
            | _ => raise RpcError)
            (fn (a, b) => [write at a, write bt b]);

fun tuple3 (at, bt, ct) =
    convert (String.concat ["(", name at, " * ", name bt, " * ", name ct, ")"])
            (tupleN 3)
            (fn [a, b, c] => (read at a, read bt b, read ct c)
            | _ => raise RpcError)
            (fn (a, b, c) => [write at a, write bt b, write ct c]);

fun tuple4 (at, bt, ct, dt) =
    convert (String.concat ["(", name at,
                            " * ", name bt,
                            " * ", name ct,
                            " * ", name dt, ")"])
            (tupleN 4)
            (fn [a, b, c, d] => (read at a, read bt b, read ct c, read dt d)
            | _ => raise RpcError)
            (fn (a, b, c, d) => [write at a, write bt b, write ct c, write dt d]);

fun tuple5 (at, bt, ct, dt, et) =
    convert (String.concat ["(", name at,
                            " * ", name ct,
                            " * ", name dt,
                            " * ", name bt,
                            " * ", name et, ")"])
            (tupleN 5)
            (fn [a, b, c, d, e] => (read at a, read bt b, read ct c, read dt d, read et e)
            | _ => raise RpcError)
            (fn (a, b, c, d, e) => [write at a, write bt b, write ct c, write dt d, write et e]);

fun tuple6 (at, bt, ct, dt, et, ft) =
    convert (String.concat ["(", name at,
                            " * ", name bt,
                            " * ", name ct,
                            " * ", name dt,
                            " * ", name et,
                            " * ", name ft, ")"])
            (tupleN 6)
            (fn [a, b, c, d, e, f] => (read at a, read bt b, read ct c, read dt d, read et e, read ft f)
            | _ => raise RpcError)
            (fn (a, b, c, d, e, f) => [write at a, write bt b, write ct c, write dt d, write et e, write ft f]);


val eitherN =
    let fun readEither bytes =
            let val len = Word8Vector.length bytes - 1;
            in (Word8.toInt (Word8Vector.sub (bytes, 0)), getBytes bytes 1 len) end;
        fun writeEither (idx, data) =
            Word8Vector.concat [Word8Vector.fromList [Word8.fromInt idx], data];
    in {
        reader = readEither,
        writer = writeEither,
        name = "EitherN"
    } end;

fun either2 (at, bt) =
    convert(String.concat ["(", name at,
                            ", ", name bt,
                            ") Rpc.Datatype.Either2.t"])
           eitherN
            (fn (0, a) => Either2.FST (read at a)
            | (1, b) => Either2.SND (read bt b)
            | _ => raise RpcError)
            (fn (Either2.FST a) => (0, write at a)
            | (Either2.SND b) => (1, write bt b));

fun either3 (at, bt, ct) =
    convert (String.concat ["(", name at,
                            ", ", name bt,
                            ", ", name ct,
                            ") Rpc.Datatype.Either3.t"])
        eitherN
            (fn (0, a) => Either3.FST (read at a)
            | (1, b) => Either3.SND (read bt b)
            | (2, c) => Either3.THD (read ct c)
            | _ => raise RpcError)
            (fn (Either3.FST a) => (0, write at a)
            | (Either3.SND b) => (1, write bt b)
            | (Either3.THD c) => (2, write ct c));

fun either4 (at, bt, ct, dt) =
    convert (String.concat ["(", name at,
                            ", ", name bt,
                            ", ", name ct,
                            ", ", name dt,
                            ") Rpc.Datatype.Either4.t"])
        eitherN
            (fn (0, a) => Either4.FST (read at a)
            | (1, b) => Either4.SND (read bt b)
            | (2, c) => Either4.THD (read ct c)
            | (3, d) => Either4.FOR (read dt d)
            | _ => raise RpcError)
            (fn (Either4.FST a) => (0, write at a)
            | (Either4.SND b) => (1, write bt b)
            | (Either4.THD c) => (2, write ct c)
            | (Either4.FOR d) => (3, write dt d));

fun either5 (at, bt, ct, dt, et) =
    convert (String.concat ["(", name at,
                            ", ", name bt,
                            ", ", name ct,
                            ", ", name dt,
                            ", ", name et,
                            ") Rpc.Datatype.Either5.t"])
        eitherN
            (fn (0, a) => Either5.FST (read at a)
            | (1, b) => Either5.SND (read bt b)
            | (2, c) => Either5.THD (read ct c)
            | (3, d) => Either5.FOR (read dt d)
            | (4, e) => Either5.FIF (read et e)
            | _ => raise RpcError)
            (fn (Either5.FST a) => (0, write at a)
            | (Either5.SND b) => (1, write bt b)
            | (Either5.THD c) => (2, write ct c)
            | (Either5.FOR d) => (3, write dt d)
            | (Either5.FIF e) => (4, write et e));

fun either6 (at, bt, ct, dt, et, ft) =
    convert (String.concat ["(", name at,
                            ", ", name bt,
                            ", ", name ct,
                            ", ", name dt,
                            ", ", name et,
                            ", ", name ft,
                            ") Rpc.Datatype.Either6.t"])
        eitherN
            (fn (0, a) => Either6.FST (read at a)
            | (1, b) => Either6.SND (read bt b)
            | (2, c) => Either6.THD (read ct c)
            | (3, d) => Either6.FOR (read dt d)
            | (4, e) => Either6.FIF (read et e)
            | (5, f) => Either6.SIX (read ft f)
            | _ => raise RpcError)
            (fn (Either6.FST a) => (0, write at a)
            | (Either6.SND b) => (1, write bt b)
            | (Either6.THD c) => (2, write ct c)
            | (Either6.FOR d) => (3, write dt d)
            | (Either6.FIF e) => (4, write et e)
            | (Either6.SIX f) => (5, write ft f));

fun option at =
    convert ((name at) ^ " option")
            (either2 (at, unit))
            (fn Either2.FST v => SOME v
            | Either2.SND () => NONE)
            (fn SOME v => Either2.FST v
            | NONE => Either2.SND ())

fun list at =
    (* format is:
       leading int for list length,
       then for each element we include an int for the byte-length of the element,
       then the element itself.
     *)
    let fun listReader bytes =
            let val length = read int (getBytes bytes 0 8);
                fun f 0 _ ans = List.rev ans
                  | f remaining offset ans =
                    let val el_len = read int (getBytes bytes offset 8);
                        val x = read at (getBytes bytes (offset + 8) el_len);
                    in f (remaining - 1) (offset + 8 + el_len) (x::ans) end;
            in f length 8 [] end;
        fun listWriter xs =
            let val len_bytes = write int (List.length xs);
                val encoded_elements = List.map (fn x => let val b = write at x;
                                                             val len_b = write int (Word8Vector.length b)
                                                         in Word8Vector.concat [len_b, b] end)
                                                xs;
            in Word8Vector.concat (len_bytes::encoded_elements) end;
    in {
        reader = listReader,
        writer = listWriter,
        name = (name at) ^ " list"
    } end;

end;

type ('a, 'b) functype = string * 'a Datatype.t * 'b Datatype.t

type endpoint = {
    identifier: string,
    specification: string,
    callback: data -> data
}

type service = {
    address: INetSock.sock_addr
}

fun endpointName {identifier: string, ...} = identifier;

fun create (host, port) = {
    address = INetSock.toAddr (Option.valOf (NetHostDB.fromString host), port)
};

fun provide (name, param, return) callback = {
    identifier = name,
    specification = String.concat [Datatype.name param,
                                   " -> ",
                                   Datatype.name return],
    callback = fn data => let val input = Datatype.read param data;
                              val output = callback input;
                          in Datatype.write return output end
};

fun require {address = addr} (name, param, return) =
    fn input =>
       let val data = Datatype.write param input;
           val request = Http.Client.makeRequest
                             (Http.POST, "/" ^ name)
                             ("application/octet-stream", data);
           val response = Http.Client.fetch addr request;
           val (status, _, output) = Http.Client.readResponse response;
       in if status <> Http.OK then raise RpcError
          else Datatype.read return output
       end;

fun serve {address = addr} endpoints =
    let fun findEndpoint req =
            if req = "/"
            then SOME (fn _ =>
                          let fun fmt ep = String.concat
                                               [#identifier ep, " : ",
                                                #specification ep, ";\n"];
                              val lines = List.map fmt endpoints;
                              val msg = String.concat lines;
                          in Byte.stringToBytes msg end)
            else Option.map #callback
                            (List.find (fn ep => "/" ^ (#identifier ep) = req)
                                       endpoints);
        fun handler request =
            let val (_, endpoint, _, input) = Http.Server.readRequest request;
            in case findEndpoint endpoint of
                   NONE => Http.Server.makeResponse
                               Http.NOT_FOUND
                               ("text/plain", Datatype.empty)
                 | SOME callback => Http.Server.makeResponse
                                        Http.OK
                                        ("application/octet-stream",
                                         callback input)
            end handle RpcError => Http.Server.makeResponse
                                       Http.BAD_REQUEST
                                       ("text/plain", Datatype.empty);
    in Http.Server.listen addr handler end;

end;


(*
For convenience, we redefine some modules to include a `t_rpc` value.
This means we don't need to keep digging into the RPC module, or remember where
we defined the RPC "type" for any given type -- they always live in their module.
*)

val unit_rpc = Rpc.Datatype.unit;

structure Bool : sig
              include BOOL
              val bool_rpc: bool Rpc.Datatype.t
          end = struct
open Bool;
val bool_rpc = Rpc.Datatype.bool;
end;

structure Int : sig
              include INTEGER
              val int_rpc: int Rpc.Datatype.t
          end = struct
open Int;
val int_rpc = Rpc.Datatype.int;
end;

structure Real : sig
              include REAL
              val real_rpc: real Rpc.Datatype.t
          end = struct
open Real;
val real_rpc = Rpc.Datatype.real;
end;

structure String : sig
              include STRING
              val string_rpc: string Rpc.Datatype.t
          end = struct
open String;
val string_rpc = Rpc.Datatype.string;
end;

structure Option : sig
              include OPTION
              val option_rpc: 'a Rpc.Datatype.t -> 'a option Rpc.Datatype.t
          end = struct
open Option;
val option_rpc = Rpc.Datatype.option;
end;

structure List : sig
              include LIST
              val list_rpc: 'a Rpc.Datatype.t -> 'a list Rpc.Datatype.t
          end = struct
open List;
val list_rpc = Rpc.Datatype.list;
end;
