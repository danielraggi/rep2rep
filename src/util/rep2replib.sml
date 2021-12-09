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
    val mappair : ('a -> 'b) -> ('a * 'a) -> ('b * 'b);
    val mapfst : ('a -> 'b) -> ('a * 'c) -> ('b * 'c);
    val mapsnd : ('b -> 'c) -> ('a * 'b) -> ('a * 'c);
    val equals : ''a -> ''a -> bool;
    val flip : ('a * 'b) -> ('b * 'a);
    val curry: ('a * 'b -> 'c) -> 'a -> 'b -> 'c
    val uncurry: ('a -> 'b -> 'c) -> 'a * 'b -> 'c
end;


structure Rep2RepLib : REP2REPLIB =
struct

val IMPORTING_STACK_ : string list ref = ref [];

val IMPORTED_ : string list ref = ref ["util.robinlib"];

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


fun mappair f (a, b) = (f a, f b);

fun mapfst f (a, b) = (f a, b);

fun mapsnd f (a, b) = (a, f b);

fun equals a b = a = b;

fun flip (a, b) = (b, a);

fun curry f a b = f (a, b);

fun uncurry f (a, b) = f a b;

end;

open Rep2RepLib

signature LIST =
sig
    include LIST
    val remove : ''a -> ''a list -> ''a list;
    val removeDuplicates : ''a list -> ''a list;
    val removeRepetition : ('a -> 'a -> bool) -> 'a list -> 'a list;
    val inout : 'a list -> ('a * 'a list) list;

    val mergesort : ('a * 'a -> order) -> 'a list -> 'a list;

    val intersperse : 'a -> 'a list -> 'a list;

    val enumerate : 'a list -> (int * 'a) list;
    val enumerateFrom : int -> 'a list -> (int * 'a) list;

    val filterOption : ('a option) list -> 'a list;

    val isPermutationOf : ('a * 'a -> bool) -> 'a list -> 'a list -> bool;

    val mapArgs : ('a -> 'b) -> 'a list -> ('a * 'b) list;
    val flatmap : ('a -> 'b list) -> 'a list -> 'b list;

    val product : ('a list * 'b list) -> ('a * 'b) list;
    val listProduct : 'a list list -> 'a list list;

    val toString : ('a -> string) -> 'a list -> string;

    val unfold : ('a -> ('b * 'a) option) -> 'a -> 'b list;
    val replicate : int -> 'a -> 'a list;

    val max : (('a * 'a) -> order) -> 'a list -> 'a;
    val min : (('a * 'a) -> order) -> 'a list -> 'a;

    val argmax : ('a -> real) -> 'a list -> ('a * real);
    val argmin : ('a -> real) -> 'a list -> ('a * real);

    val takeWhile : ('a -> bool) -> 'a list -> 'a list;
    val dropWhile : ('a -> bool) -> 'a list -> 'a list;

    val split : ('a list * int) -> ('a list * 'a list);

    val rotate : int -> 'a list -> 'a list;

    val weightedSumMap : ('a -> real) -> ('a -> real) -> 'a list -> real;
    val sumMap : ('a -> real) -> 'a list -> real;
    val weightedSum : (real -> real) -> real list -> real;
    val sum : real list -> real;

    val weightedAvgIndexed : ('a -> real) -> ('a -> real) -> 'a list -> real;
    val avgIndexed : ('a -> real) -> 'a list -> real;
    val weightedAvg : (real -> real) -> real list -> real;
    val avg : real list -> real;

    val allZip : ('a -> 'b -> bool) -> 'a list -> 'b list -> bool;
    val funZip : ('a -> 'b -> 'c) -> 'a list -> 'b list -> 'c list;
    val maps : ('a -> 'b list) -> 'a list -> 'b list;
end;

structure List : LIST =
struct
open List;
fun remove needle haystack = List.filter (fn x => x <> needle) haystack;

fun removeDuplicates [] = []
  | removeDuplicates (h::t) = h :: removeDuplicates (remove h t);

(* belongs in lists *)
fun removeRepetition eq (n::ns) = n :: removeRepetition eq (List.filter (fn x => not (eq x n)) ns)
  | removeRepetition _ [] = []

fun split (xs, i) =
    let
        fun split' fst xs 0 = (List.rev fst, xs)
          | split' fst [] _ = raise Subscript
          | split' fst (x::xs) i = split' (x::fst) xs (i-1);
    in
        split' [] xs i
    end;

fun inout lst =
    let fun loop ans _ [] = List.rev ans
          | loop ans ys (x::xs) = loop ((x, (List.rev ys)@xs)::ans) (x::ys) xs;
    in loop [] [] lst end;

fun mergesort cmp [] = []
  | mergesort cmp [x] = [x]
  | mergesort cmp items =
    let fun merge [] xs = xs
          | merge xs [] = xs
          | merge (x::xs) (y::ys) =
            if cmp(x, y) = GREATER then
                y::(merge (x::xs) ys)
            else
                x::(merge xs (y::ys));

        val (left, right) = split (items, Int.div (length items, 2));
        val (sortedLeft, sortedRight) = (mergesort cmp left, mergesort cmp right);
        val result = merge sortedLeft sortedRight;
    in result
    end;

fun intersperse s [] = []
  | intersperse s (y::ys) =
    let fun intersperse' [] ans = List.rev ans
          | intersperse' (x::xs) ans = intersperse' xs (x::s::ans)
    in
        intersperse' ys [y]
    end;

fun enumerateFrom start list =
    let
        fun enumerateFrom' _ [] ans = List.rev ans
          | enumerateFrom' i (x::xs) ans = enumerateFrom' (i+1) xs ((i, x)::ans)
    in
        enumerateFrom' start list []
    end;

fun enumerate xs = enumerateFrom 0 xs;

fun filterOption xs = mapPartial (fn x => x) xs;

fun findAndRemoveOnce _ _ [] = (false,[])
  | findAndRemoveOnce f x (a::L) =
    if f (x, a) then (true,L)
    else let val (found,L') = findAndRemoveOnce f x L
         in (found,a::L')
         end;
fun isPermutationOf _ [] [] = true
  | isPermutationOf f (a::A) B = let val (found,B') = findAndRemoveOnce f a B
                                 in if found then isPermutationOf f A B'
                                    else false
                                 end
  | isPermutationOf _ _ _ = false;


fun mapArgs f xs = map (fn x => (x, f x)) xs;

fun flatmap f xs = concat (map f xs);

fun product (xs, ys) =
    let
        fun joinall ans x [] = ans
          | joinall ans x (y::ys) = joinall ((x, y)::ans) x ys
        fun cartprod ans [] _ = List.rev(ans)
          | cartprod ans _ [] = List.rev(ans)
          | cartprod ans (x::xs) ys = cartprod (joinall ans x ys) xs ys;
    in
        cartprod [] xs ys
    end;

fun listProduct ((h::t)::T) = (map (fn x => h :: x) (listProduct T)) @ (listProduct (t::T))
  | listProduct ([]::T) = []
  | listProduct [] = [[]];

fun toString fmt items = "[" ^ String.concatWith ", " (map fmt items) ^ "]";

fun unfold f seed =
    let
        fun unfold' f seed ans =
            case f seed of
                NONE => ans
              | SOME (x, next) => (unfold' f next (x::ans));
    in
        List.rev (unfold' f seed [])
    end;

fun replicate n x =
    if n < 0 then raise Size else
    let fun gen 0 = NONE
          | gen n = SOME (x, n-1)
    in
        unfold gen n
    end;

fun max _ [] = raise Empty
  | max cmp (x::xs) = foldl (fn (a, b) => if cmp(a, b) = GREATER
                                          then a
                                          else b)
                            x xs;

fun min _ [] = raise Empty
  | min cmp (x::xs) = foldl (fn (a, b) => if cmp(a, b) = LESS
                                          then a
                                          else b)
                            x xs;

fun dropWhile pred [] = []
  | dropWhile pred (x::xs) = if pred x then (dropWhile pred xs)
                             else x::xs;

fun takeWhile pred list =
    let fun takeWhile' [] ans = rev ans
          | takeWhile' (x::xs) ans = if pred x then takeWhile' xs (x::ans)
                                     else List.rev ans;
    in takeWhile' list []
    end;

fun rotate 0 xs = xs
  | rotate _ [] = []
  | rotate n xs = (op@ o flip o split) (xs, Int.mod (n, length xs));

fun weightedSumMap w f L =
    List.foldr (fn (x, s) => ((w x) * (f x)) + s) 0.0 L;

fun weightedSum w L = weightedSumMap w (fn x => x) L;

fun sumMap f L = weightedSumMap (fn _ => 1.0) f L;
fun sum L = weightedSumMap (fn _ => 1.0) (fn x => x) L;

fun weightedAvgIndexed w f L = if null L then raise Empty else (weightedSumMap w f L) / (sumMap w L)

fun weightedAvg w L = weightedAvgIndexed w (fn x => x) L;

fun avgIndexed f L = weightedAvgIndexed (fn _ => 1.0) f L;
fun avg L = weightedAvgIndexed (fn _ => 1.0) (fn x => x) L;

fun argmax _ [] = raise Empty
  | argmax f [x] = (x, f x)
  | argmax f (x::L) = let val r = argmax f L
                          val v = f x
                      in if v > #2 r then (x,v) else r
                      end;

fun argmin _ [] = raise Empty
  | argmin f [x] = (x, f x)
  | argmin f (x::L) = let val r = argmin f L
                          val v = f x
                      in if v < #2 r then (x,v) else r
                      end;

fun allZip _ [] [] = true
  | allZip f (h::t) (h'::t') = f h h' andalso allZip f t t'
  | allZip _ _ _ = false

fun funZip _ [] [] = []
  | funZip f (h::t) (h'::t') = f h h' :: funZip f t t'
  | funZip _ _ _ = raise Match

fun maps f [] = []
  | maps f (x :: xs) = f x @ maps f xs;
end;


signature STRING =
sig
    include STRING;

    val stripSpaces : string -> string;
    val splitOn : string -> string -> string list;
    val splitStrip : string -> string -> string list;
    val splitStripApply : (string -> 'a) -> string -> string -> 'a list;
    val breakOn : string -> string -> (string * string * string);
    val removeDelimiters : (string * string) -> string -> string;
    val removeParentheses : string -> string;
    val removeBraces : string -> string;
    val removeSquareBrackets : string -> string;
    val removeDoubleQuotes : string -> string;
    val removeSingleQuotes : string -> string;

    val addDelimiters : (string * string) -> string -> string
    val addParentheses : string -> string
    val addSquareBrackets : string -> string
    val addBraces : string -> string
    val addDoubleQuotes : string -> string
    val addSingleQuotes : string -> string

    val stringOfList : ('a -> string) -> 'a list -> string
    val listOfString : (string -> 'a) -> string -> 'a list
end;

structure String : STRING =
struct
open String;

fun splitOn sep s =
    if (String.size sep) = 1
    then let val char = List.hd (String.explode sep);
             val match = equals char;
         in String.tokens match s end
    else let
        val chars = String.explode s;
        val sepChars = String.explode sep;
        fun startsWithSep' [] r = (true, r)
          | startsWithSep' _ [] = (false, [])
          | startsWithSep' (s::sep) (t::rest) =
            if s = t then startsWithSep' sep rest
            else (false, []);
        fun startsWithSep chars = startsWithSep' sepChars chars;
        fun group ans collected [] =
            let val finalWord = String.implode(List.rev collected)
            in List.rev (finalWord :: ans) end
          | group ans collected (t::tokens) =
            let val (isSep, rest') = startsWithSep (t::tokens);
                val rest = if isSep then rest' else tokens;
            in
                if isSep
                then group ((String.implode (List.rev collected))::ans) [] rest
                else group ans (t::collected) rest
            end;
    in group [] [] (String.explode s) end;

fun stripSpaces str = implode (List.filter (not o Char.isSpace) (explode str))
(*)
    let val chars = explode str;
        val revDrop = List.rev o (List.dropWhile Char.isSpace);
        val remainingChars = (revDrop o revDrop) chars;
    in implode remainingChars end;*)

fun splitStrip sep s = List.map stripSpaces (splitOn sep s);

fun splitStripApply f sep s = List.map (f o stripSpaces) (splitOn sep s);

fun breakOn sep s =
    let val sepChars = String.explode sep;
        val sChars = String.explode s;
        fun fwJoin cs = String.implode cs;
        fun bwJoin cs = String.implode (List.rev cs);
        fun break front [] after _ = (bwJoin front, sep, fwJoin after)
          | break front (c::cs) [] _ = (s, "", "")
          | break front (x::xs) (c::cs) accum =
            if x = c then break front xs cs (x::accum)
            else break (c::(accum@front)) sepChars cs [];
    in break [] sepChars sChars [] end;

fun removeDelimiters (left, right) s =
    let val leftChars = String.explode left;
        val rightChars = List.rev (String.explode right);
        val sChars = String.explode s;
        fun dropMatching [] s _ = SOME (List.rev s)
          | dropMatching x [] dropped = NONE
          | dropMatching (x::xs) (c::cs) dropped =
            if x = c then dropMatching xs cs (c::dropped)
            else NONE;
    in
        case dropMatching leftChars sChars [] of
            NONE => s
          | SOME chars => case dropMatching rightChars chars [] of
                              NONE => s
                            | SOME chars' => String.implode chars'
    end;

val removeParentheses = removeDelimiters ("(", ")");
val removeBraces = removeDelimiters ("{", "}");
val removeSquareBrackets = removeDelimiters ("[", "]");
val removeDoubleQuotes = removeDelimiters ("\"", "\"");
val removeSingleQuotes = removeDelimiters ("'", "'");

fun addDelimiters (l,r) s = l ^ s ^ r
fun addParentheses s = addDelimiters ("(",")") s
fun addSquareBrackets s = addDelimiters ("[","]") s
fun addBraces s = addDelimiters ("{","}") s
fun addDoubleQuotes s = addDelimiters ("\"", "\"") s
fun addSingleQuotes s = addDelimiters ("'", "'") s

fun stringOfList f L = addSquareBrackets (String.concatWith ", " (List.map f L))
fun listOfString f s = splitStripApply f "," s

end;


signature TEXT_IO =
sig

    include TEXT_IO;

    val lookaheadN : (instream *  int) -> string;

end;

structure TextIO :> TEXT_IO =
struct

open TextIO;

fun lookaheadN (istr, count) =
    let
        val oldstream = getInstream istr;
        val (lookahead, newstream) = StreamIO.inputN(oldstream, count);
        val _ = setInstream (istr, oldstream);
    in
        lookahead
    end;

end;
