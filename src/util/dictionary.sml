(*

dictionary.sml

Provide a dictionary structure for associative look-ups.
A dictionary is backed by a splay tree, which is a self-balancing binary search
tree. This means dictionaries have an order, while also having amortized O(log n)
look-up, insert, and deletion times.

*)

(* An abstract signature for dictionaries *)
signature DICTIONARY =
sig
    type k;
    type ('k, 'v) dict;

    exception KeyError;

    val empty : unit -> (k, 'v) dict;
    val fromPairList : (k * 'v) list -> (k, 'v) dict;
    val toPairList : (k, 'v) dict -> (k * 'v) list;

    val insert : (k, 'v) dict -> (k * 'v) ->  unit;
    val remove : (k, 'v) dict -> k -> unit;

    val get : (k, 'v) dict -> k -> 'v;
    val update : (k, 'v) dict -> k -> ('v -> 'v) -> 'v;

    val keys : (k, 'v) dict -> k list;
    val values : (k, 'v) dict -> 'v list;
    val items : (k, 'v) dict -> (k * 'v) list;

    val size : (k, 'v) dict -> int;

    val union : (k, 'v) dict -> (k, 'v) dict -> (k, 'v) dict;
    val unionWith : ((k * 'v * 'v) -> 'v) -> (k, 'v) dict -> (k, 'v) dict -> (k, 'v) dict;
    val unionAll : (k, 'v) dict list -> (k, 'v) dict;
    val unionAllWith : ((k * 'v * 'v) -> 'v) -> (k, 'v) dict list -> (k, 'v) dict;

    val intersectionWith : ((k * 'v * 'v) -> 'v) -> (k, 'v) dict -> (k, 'v) dict -> (k, 'v) dict;
    val intersectionAllWith : ((k * 'v * 'v) -> 'v) -> (k, 'v) dict list -> (k, 'v) dict;

    val map : ((k * 'v) -> 'a) -> (k, 'v) dict -> 'a list; (* It would be nice to have this work to dictionaries *)
    val filter : ((k * 'v) -> bool) -> (k, 'v) dict -> (k, 'v) dict;
    val foldl : (((k * 'v) * 'a) -> 'a) -> 'a -> (k, 'v) dict -> 'a;
    val foldr : (((k * 'v) * 'a) -> 'a) -> 'a -> (k, 'v) dict -> 'a;
    val find : (k * 'v -> bool) -> (k, 'v) dict -> (k * 'v) option;

    val equalKeys : (k, 'v) dict * (k, 'v) dict -> bool;
    val equal : (k, ''v) dict * (k, ''v) dict -> bool;
    val isEmpty : (k, 'v) dict -> bool;

    val getFirst : (k, 'v) dict -> (k * 'v);
end;


(* A functor to produce dictionaries keyed with Ks.
   While we can be polymorphic in the values (i.e., so long as the type
   of the values are all the same, we don't care what they are), we
   impose a restriction upon the keys: in this case, the keys must be
   orderable through a compare function.
*)
functor Dictionary(K :
                   sig
                       type k;
                       val compare : k * k -> order;
                       val fmt : k -> string;
                   end
                  ) :> DICTIONARY where type k = K.k =
struct

datatype 'a tree = LEAF
                 | BRANCH of ('a * 'a tree * 'a tree);
type k = K.k;
type ('k, 'v) dict = ('k * 'v) tree ref;

exception KeyError;

fun keyFor (k, _) = k;

fun splayFor k LEAF = raise KeyError
  | splayFor k (BRANCH(v, l, r)) =
    case K.compare(k, keyFor(v)) of
        EQUAL => BRANCH(v, l, r)
      (* Potential zig-* *)
      | LESS => (
          case l of
              LEAF => BRANCH(v, l, r)
            | BRANCH(lv, ll, lr) =>
              case K.compare(k, keyFor(lv)) of
                  (* single-zig *)
                  EQUAL => BRANCH(lv,
                                  ll,
                                  BRANCH(v,
                                         lr,
                                         r))
                (* potential zig-zig *)
                | LESS => (
                    case ll of
                        LEAF => BRANCH(lv,
                                       LEAF,
                                       BRANCH(v,
                                              lr,
                                              r))
                      | llt =>
                        case (splayFor k llt) of
                            LEAF => BRANCH(lv,
                                           LEAF,
                                           BRANCH(v,
                                                  lr,
                                                  r))
                          | BRANCH(llv, lll, llr) => BRANCH(llv,
                                                            lll,
                                                            BRANCH(lv,
                                                                   llr,
                                                                   BRANCH(v,
                                                                          lr,
                                                                          r)))
                )
                (* potential zig-zag *)
                | GREATER => (
                    case lr of
                        LEAF => BRANCH(lv,
                                       ll,
                                       BRANCH(v,
                                              LEAF,
                                              r))
                      | lrt =>
                        case (splayFor k lrt) of
                            LEAF => BRANCH(lv,
                                           ll,
                                           BRANCH(v,
                                                  LEAF,
                                                  r))
                         | BRANCH(lrv, lrl, lrr) => BRANCH(lrv,
                                                           BRANCH(lv,
                                                                  ll,
                                                                  lrl),
                                                           BRANCH(v,
                                                                  lrr,
                                                                  r))
                )
      )
      (* potential zag-* *)
      | GREATER => (
          case r of
              LEAF => BRANCH(v, l, r)
            | BRANCH(rv, rl, rr) =>
              case K.compare(k, keyFor(rv)) of
                  (* single zag *)
                  EQUAL => BRANCH(rv,
                                  BRANCH(v,
                                         l,
                                         rl),
                                  rr)
                (* potential zag-zag *)
                | GREATER => (
                    case rr of
                        LEAF => BRANCH(rv,
                                       BRANCH(v,
                                              l,
                                              rl),
                                       rr)
                      | rrt =>
                        case (splayFor k rrt) of
                            LEAF => BRANCH(rv,
                                           BRANCH(v,
                                                  l,rl),
                                           rr)
                          | BRANCH(rrv, rrl, rrr) => BRANCH(rrv,
                                                            BRANCH(rv,
                                                                   BRANCH(v,
                                                                          l,
                                                                          rl),
                                                                   rrl),
                                                            rrr)
                )
                (* potential zag-zig *)
                | LESS => (
                    case rl of
                        LEAF => BRANCH(rv,
                                       BRANCH(v,
                                              l,
                                              rl),
                                      rr)
                      | rlt =>
                        case (splayFor k rlt) of
                            LEAF => BRANCH(rv,
                                           BRANCH(v,
                                                  l,
                                                  rl),
                                           rr)
                         | BRANCH(rlv, rll, rlr) => BRANCH(rlv,
                                                           BRANCH(v,
                                                                  l,
                                                                  rll),
                                                           BRANCH(rv,
                                                                  rlr,
                                                                  rr))
                )
      )

val empty = fn () => (ref LEAF);

fun insert' LEAF (x,y) = BRANCH ((x,y), LEAF, LEAF)
  | insert' (BRANCH ((k,v), l, r)) (x, y) =
    if K.compare(x, k) = EQUAL then BRANCH((x,y), l, r)
    else
        let
            val cmp = K.compare (x, k)
            val l' =  if cmp = GREATER then l else (insert' l (x, y));
            val r' = if cmp = GREATER then insert' r (x, y) else r;
        in
            BRANCH ((k, v), l', r')
        end;
fun insert d (x,y) =
    let
        val d' = !d;
        val updated_d' = insert' d' (x, y);
        val _ = (d := updated_d')
    in () end;

(*
We can exploit the structure of a sorted list to build a balanced tree faster.
We build half the tree the tree from the first half of the list,
the we build the other half of the tree from the second half of the list.
This will run in O(n) time, rather than the naïve O(n log n) time.
Proof:
    T(1) = 1
    T(n) = 2 * T(n/2) + 1
Solution with T(n) = 2n - 1.
*)
fun fromSortedPairList xs =
    let
        val len = List.length xs;
        fun helper xs 0 = (LEAF, xs)
          | helper xs n =
            let
                val (left, new_xs) = helper xs (n div 2);
                val (root, rightl) = case new_xs of
                                         [] => raise List.Empty
                                       | (h::t) => (h, t);
                val (right, nextl) = helper rightl (n - (n div 2) - 1);
                val result = BRANCH (root, left, right);
            in
               (result, nextl)
            end;
        val (result, _) = helper xs len;
    in
        ref result
    end;

(*
From an arbitrary list we cannot built the tree in O(n) time,
as if we could we would have an O(n) comparison-based sorting algorithm.
This method sorts the values (O(n log n)), removes duplicates (O(n)),
and uses the fast tree-ify from above (O(n)) to build the tree in
O(n log n) time with maximal code reuse.
*)
fun fromPairList xs =
    let
        fun dedup [] = []
          | dedup [x] = [x]
          | dedup ((x,a)::(y,b)::zs) = if K.compare(x,y) = EQUAL
                                       then dedup((y,b)::zs) (* Favour second *)
                                       else (x,a)::(dedup ((y,b)::zs))
    in
        fromSortedPairList (dedup (List.mergesort
                                       (fn ((a, _), (b, _)) => K.compare (a, b))
                                       xs))
    end;

(*
We avoid the naïve version of toPairList in the case of severely unbalanced
trees. This should be rare, but the version below is O(n) just in case.
*)
fun toPairList' (LEAF, pairs) = pairs
  | toPairList' (BRANCH (a, l, r), pairs) = toPairList' (l, a::(toPairList' (r, pairs)));
fun toPairList d = toPairList' ((!d), []);

(*
Unioning arbitrary BSTs is hard because they may overlap; we cannot just
pick an element to be the root and glue them together, we would break the
tree invariant. Instead, we resort to a simple but surprisingly fast algorithm
based on functions from above. We convert the trees into lists (O(m) + O(n)),
merge the lists (which we know will be sorted, O(m + n)), then build the
final tree (from the list which must also be sorted, O(m+n)). Overall complexity
is O(m+n), which is about as good as you can hope for!
*)
fun unionWith' _ LEAF t = t
  | unionWith' _ t LEAF = t
  | unionWith' f t t' =
    let
        val tl = toPairList' (t, []);
        val tl' = toPairList' (t', []);
        fun merge [] xs = xs
          | merge xs [] = xs
          | merge ((x, v)::xs) ((y, v')::ys) =
            case K.compare(x, y) of
                EQUAL => (x, f(x, v, v'))::(merge xs ys)
              | LESS => (x, v)::(merge xs ((y, v')::ys))
              | GREATER => (y, v')::(merge ((x, v)::xs) ys);
        val merged = merge tl tl';
        val newdict = fromSortedPairList merged;
    in
        ! newdict
    end;
fun unionWith f t u = ref (unionWith' f (!t) (!u));

fun union' a b = unionWith' (fn (k, v1, v2) => raise KeyError) a b;
fun union a b = ref (union' (!a) (!b));

fun unionAllWith f xs =
    let
        val xs' = map (fn x => !x) xs;
    in
        ref (List.foldr (fn (a, b) => unionWith' f a b) LEAF xs')
    end;
fun unionAll xs = unionAllWith (fn (k, v1, v2) => raise KeyError) xs;

(*
Much like unioning BSTs, intersecting them kind of sucks. And as with unioning,
we can use a surprisingly simple algorithm to get around this grossness:
listify (O(m) + O(n)), intersect (O(m + n)), treeify (O(min(m, n)))
for a total complexity of O(m+n).
*)
fun intersectionWith' _ LEAF _ = LEAF
  | intersectionWith' _ _ LEAF = LEAF
  | intersectionWith' f t t' =
    let
        val tl = toPairList' (t, []);
        val tl' = toPairList' (t', []);
        fun intsct [] _ = []
          | intsct _ [] = []
          | intsct ((x,v)::xs) ((y,v')::ys) =
            if K.compare(x,y) = EQUAL then (x, f(x,v,v'))::(intsct xs ys)
            else if K.compare(x,y) = LESS then (intsct xs ((y,v')::ys))
            else (intsct ((x,v)::xs) ys);
    in
        ! (fromSortedPairList (intsct tl tl'))
    end;
fun intersectionWith f t u = ref (intersectionWith' f (!t) (!u));

fun intersectionAllWith f xs =
    let
        val xs' = map (fn x => !x) xs;
    in
        ref (List.foldr (fn (a, b) => intersectionWith' f a b) LEAF xs')
    end;

(*
While we could use union, a custom joinDisjoint function is faster (O(log n))
because we are operating on values known to be strictly less
(from the left) and strictly greater (from the right) than a particular
value. They are mutually recursive because once we find the least element,
we need to remove it from the tree. Note that this second remove MUST trigger
a base case of joinDisjoint, because we selected the element based on it
being a half-branch.
*)
fun joinDisjoint LEAF t = t
  | joinDisjoint t LEAF = t
  | joinDisjoint t t' =
    let
        fun least (BRANCH(x, LEAF, _)) = x
          | least (BRANCH(x, l, r)) = least l
          | least LEAF = raise KeyError;
        fun fst (k, _) = k;
        val lt = least t'
    in
        BRANCH(lt, t, remove' t' (fst lt))
    end
and remove' LEAF _ = LEAF
  | remove' (BRANCH ((k,v), l, r)) x =
    if K.compare(x, k) = EQUAL then joinDisjoint l r
    else if K.compare(x, k) = GREATER then BRANCH((k,v), l, (remove' r x))
    else BRANCH((k,v), (remove' l x), r);
fun remove t k =
    let
        val _ = t := (remove' (!t) k);
    in () end;

fun get t k =
    let
        val t' = splayFor k (!t);
        val v = case (t') of
                    BRANCH ((a, b), _, _) => if K.compare(a, k) = EQUAL then b
                                             else raise KeyError
                  | _ => raise KeyError;
        val _ = (t := t');
    in
        v
    end;

fun update t k f =
    let
        val t' = splayFor k (!t);
        val (t'', v) = case (t') of
                    BRANCH ((a, b), l, r) =>
                    if K.compare(a, k) = EQUAL
                    then let val v = f b in (BRANCH ((a, v), l, r), v) end
                    else raise KeyError
                  | _ => raise KeyError;
        val _ = (t := t'');
    in v end;

fun keys t = map (fn (k, v) => k) (toPairList t);

fun values t = map (fn (k, v) => v) (toPairList t);

fun items d = toPairList d;

fun size' LEAF = 0
  | size' (BRANCH (_, l, r)) = 1 + size' l + size' r;
fun size t = size' (!t);

fun map f t = List.map f (toPairList t);

fun filter' f LEAF = LEAF
  | filter' f (BRANCH (a, l, r)) =
    let
        val l' = filter' f l;
        val r' = filter' f r;
    in
        if (f a)
        then BRANCH (a, l', r')
        else joinDisjoint l' r'
    end;
fun filter f t = ref (filter' f (!t));

fun foldl f z t = List.foldl f z (toPairList t);

fun foldr f z t = List.foldr f z (toPairList t);

fun find' p LEAF = NONE
  | find' p (BRANCH(kv, l, r)) = if (p kv) then SOME kv
                                else case (find' p l) of
                                         SOME x => SOME x
                                       | NONE => find' p r;
fun find p t = find' p (!t);

fun equalKeys (x, y) =
    let
        val xl = keys x;
        val yl = keys y;
        fun cmpList [] [] = true
          | cmpList (kx::xs) (ky::ys) =
            K.compare(kx, ky) = EQUAL andalso cmpList xs ys
          | cmpList _ _ = false;
    in
        cmpList xl yl
    end;
fun equal (x, y) =
    let
        val xl = toPairList x;
        val yl = toPairList y;
        fun cmpList [] [] = true
          | cmpList ((kx, vx)::xs) ((ky, vy)::ys) =
            K.compare(kx, ky) = EQUAL
            andalso vx = vy
            andalso cmpList xs ys
          | cmpList _ _ = false;
    in
        cmpList xl yl
    end;

fun isEmpty (ref LEAF) = true
  | isEmpty _ = false;

fun getFirst' LEAF = raise KeyError
  | getFirst' (BRANCH(x,_,_)) = x;
fun getFirst t = (getFirst' (!t));

end;
