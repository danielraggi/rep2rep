import "core.cspace";

signature TOKEN_MAP =
sig
  type token;
  type map; (* these maps are one-to-one relations between tokens. Useful as we use monomorphisms a lot. *)

  exception Fail
  val emptyMap : map;
  val identityMap : map;
  val addPair : token * token -> map -> map;
  val updatePair : token * token -> map -> map;
  
  val applyMap : map -> token -> token option;
  val applyInvMap : map -> token -> token option;

  val invertMap : map -> map; (* inverse *)
  
  val oo : map * map -> map; (* composition *)
  val restrictDomain : map -> token list -> map; (* restriction of domain *)
  val extendDomain : map -> token list -> string list -> map * string list; (* extention of domain *)
end

structure TokenMap : TOKEN_MAP =
struct
  type token = CSpace.token
  type map = (token -> token option) * (token -> token option)

  val emptyMap = (fn _ => NONE, fn _ => NONE)
  val identityMap = (fn t => SOME t, fn t => SOME t)

  infix 6 oo
  fun (f1,f2) oo (f1',f2') = (fn t => case f1' t of SOME x => f1 x | NONE => NONE, fn t => case f2 t of SOME x => f2' x | NONE => NONE)
 
  exception Fail
  (* updates a monomorphism so that fl(x) = y and fr(y) = x. 
     Fails if map is already defined on that pair with different value. *)
  fun addPair (x,y) (fl,fr) = 
      (case fl x of 
          SOME z => if CSpace.sameTokens y z then fl else raise Fail
        | NONE => (fn t => if CSpace.sameTokens t x then SOME y else fl t),
       case fr y of 
          SOME z => if CSpace.sameTokens x z then fr else raise Fail
        | NONE => (fn t => if CSpace.sameTokens t y then SOME x else fr t))

  (* updates a monomorphism so that fl(x) = y and fr(y) = x. 
     Forces new value. *)
  fun updatePair (x,y) (fl,fr) =
      (fn t => if CSpace.sameTokens t x then SOME y else fl t,
       fn t => if CSpace.sameTokens t y then SOME x else fr t)

  (*
    functions for building and operating with maps
  *)
  fun applyMap (f1,_) = f1
  fun applyInvMap (_,f2) = f2

  fun invertMap (f1,f2) = (f2,f1)
  fun restrictDomain (f1,f2) tks =
    (fn t => if List.exists (fn x => CSpace.sameTokens x t) tks then NONE else f1 t,
     fn t => (case f2 t of NONE => NONE | SOME y => if List.exists (fn x => CSpace.sameTokens x y) tks then NONE else f2 t))

  fun firstUnusedName Ns =
    let fun mkFun n =
          let val vcandidate = "v_{"^(Int.toString n)^"}"
          in if List.exists (fn x => x = vcandidate) Ns
              then mkFun (n+1)
              else vcandidate
          end
    in mkFun 0
    end

  (* 
    assuming f : g -> h is a monomorphism, it extends f to another monomorphism f', so that
    the domain of f' contains tokensToExtend and f' preserves their labels, 
    taking care that f(x) avoids tokens in tokenNamesToAvoid 
  *)
  fun extendDomain f [] tokenNamesToAvoid = (f,tokenNamesToAvoid)
    | extendDomain f (t::tokensToExtend) tokenNamesToAvoid = 
    let 
      val (updatedMap,updatedTks) = 
        case applyMap f t of 
            SOME t' => (f, tokenNamesToAvoid)
          | NONE => 
              let val newTokenName = firstUnusedName tokenNamesToAvoid
              in (addPair (t,CSpace.makeToken newTokenName (CSpace.typeOfToken t)) f, newTokenName :: tokenNamesToAvoid)
              end
    in 
      extendDomain updatedMap tokensToExtend updatedTks
    end

end

(* Graphs in a multi-space *)
signature GRAPH =
sig 
  include TOKEN_MAP

  type constructor;

  type TIN; (* token's incoming neighbourhood *)

  (* the graph type encodes structure graphs (directed bipartite graphs with tokens and constructor vertices). 
    Tokens are differenciated but constructor vertices are not. This restrictrs us to token-functional graphs. *)
  type graph; 

  val image : map -> graph -> graph;
  val preImage : map -> graph -> graph;

  val wellTyped : CSpace.conSpecData -> graph -> bool;
  val wellFormed : CSpace.conSpecData -> graph -> bool;
  val tokenInGraphQuick : token -> graph -> bool;
  val insertTokens : token list -> token list -> token list;
  val insertStrings : string list -> string list -> string list;
  val tokensOfGraphFull : graph -> token list;
  (* the quick version assumes the graph representation is already in normal form *)
  val tokensOfGraphQuick : graph -> token list;
  val tokenNamesOfGraphQuick : graph -> string list;

  val empty : graph;

  (* a graph with only tokens *)
  val makeFromTokens : token list -> graph;

  val join : graph -> graph -> graph;
  val remove : graph -> graph -> graph;

  (* factorising makes exactly one tin (token's incoming neighbourhood) for every token *)
  val factorise : graph -> graph;
  
  (* expanding separates the configurations of each token into individual tins. 
    Also adds a tin for each token without inputs. factorise(expand(g)) = g *)
  val expand : graph -> graph;

  (* normalising adds all tokens that appear in the graph and factorises their 
  configurations into a tin for each token *)
  val normalise : graph -> graph;

  val subgraphs : graph -> graph Seq.seq;

  (* 
  findMonomorphisms p f g1 g2 finds every extension of f that is a monomorphism 
  m from g1 to g2 where p(t,m(t)) is satisfied for every token t.
  It assumes the g1 and g2 are in normal form.
  *)
  val findMonomorphisms : (token * token -> bool) -> map -> graph -> graph -> map Seq.seq;

  (*
    A reification is a monomorphism f : g -> g' where f[g] is a specialisation of g
  *)
  val findReificationsUpTo : Type.typeSystem -> token list * token list -> map -> graph -> graph -> map Seq.seq;
  val findReifications : Type.typeSystem -> map -> graph -> graph -> map Seq.seq;

  (*
    A loosening is a partial function f : g -> g' where f^{-1} is a reification
  *)
  val findLooseningsUpTo : Type.typeSystem -> token list * token list -> map -> graph -> graph -> map Seq.seq;
  val findLoosenings : Type.typeSystem -> map -> graph -> graph -> map Seq.seq;

  (*
    An embedding is a is a monomorphism f : g -> g' where f[g] is a generalisation of g
  *)
  val findEmbeddingsUpTo : Type.typeSystem -> token list * token list -> map -> graph -> graph -> map Seq.seq;
  val findEmbeddings : Type.typeSystem -> map -> graph -> graph -> map Seq.seq;

end

structure Graph:GRAPH =
struct

  type token = CSpace.token
  type constructor = CSpace.constructor
  type 'a set = 'a list

  type TIN = {token : token, inputs : {constructor : string, inputTokens : token list} set}
  type graph = TIN set
  
  open TokenMap
  infix 6 oo

  exception Malformed of string;

  fun tokensMatchTypes T (t::ts) (ty::tys) = 
    (#subType T) (CSpace.typeOfToken t, ty) andalso tokensMatchTypes T ts tys
    | tokensMatchTypes T [] [] = true
    | tokensMatchTypes _ _ _ = raise Malformed "mismatched number of arguments"

  fun wellTyped CSD [] = true
    | wellTyped CSD (tin::g) =
    let val TSD = #typeSystemData CSD
        val T = #typeSystem TSD
        val t = #token tin
        fun checkInputs [] = true
          | checkInputs (inp::IN) = 
            (case CSpace.findConstructorWithName (#constructor inp) CSD of 
                SOME c => 
                  let val (tys,ty) = CSpace.csig c
                      val ts = #inputTokens inp
                  in tokensMatchTypes T (t::ts) (ty::tys) andalso checkInputs IN
                  end 
              | NONE => raise Malformed "unkown constructor")
    in checkInputs (#inputs tin) andalso wellTyped CSD g
    end

  fun noDuplicatedTokens g =
    let fun ndt _ [] = true
          | ndt tks (tin::g') = 
            (case CSpace.nameOfToken (#token tin) of s => 
              not (List.exists (fn x => x = s) tks) andalso ndt (s::tks) g')
    in ndt [] g
    end

  fun wellFormed CSD g = 
    noDuplicatedTokens g andalso 
    wellTyped CSD g handle Malformed _ => false

  fun tokenInGraphQuick _ [] = false
    | tokenInGraphQuick t (tin::g) = CSpace.sameTokens t (#token tin) orelse tokenInGraphQuick t g

  exception Mismatch

  fun allPairs f [] [] = true
    | allPairs f (x::X) (y::Y) = f x y andalso allPairs f X Y
    | allPairs _ _ _ = raise Mismatch

  fun sameINPs inp inp' = 
    (#constructor inp) = (#constructor inp') andalso 
    allPairs CSpace.sameTokens (#inputTokens inp) (#inputTokens inp')

  fun insertINP inp [] = [inp]
    | insertINP inp (inp'::INP') = if sameINPs inp inp' then inp'::INP' else inp' :: insertINP inp INP' 

  fun removeINP inp [] = []
    | removeINP inp (inp'::INP') = if sameINPs inp inp' then INP' else inp' :: removeINP inp INP' 

  fun joinInputs [] INP' = INP'
    | joinInputs (inp::INP) INP' = insertINP inp (joinInputs INP INP')

  fun removeInputs [] INP' = INP'
    | removeInputs (inp::INP) INP' = removeINP inp (removeInputs INP INP')

  fun insertTIN tin [] = [tin]
    | insertTIN tin (tin'::g) =
      if CSpace.sameTokens (#token tin) (#token tin') then
        {token = #token tin, inputs = joinInputs (#inputs tin) (#inputs tin')} :: g
      else
        tin' :: insertTIN tin g

  fun removeTIN tin [] = []
    | removeTIN tin (tin'::g) =
      if CSpace.sameTokens (#token tin) (#token tin') then
        case removeInputs (#inputs tin) (#inputs tin') of 
            [] => g 
          | inps => {token = #token tin, inputs = inps} :: g
      else
        tin' :: removeTIN tin g

  fun join [] g = g
    | join (tin::g) g' = join g (insertTIN tin g')

  val empty = [];

  fun makeFromTokens [] = []
    | makeFromTokens (t::ts) = insertTIN {token = t, inputs = []} (makeFromTokens ts)

  fun insertToken t [] = [t]
    | insertToken t (t'::tks) = if CSpace.sameTokens t t' then t' :: tks else t' :: insertToken t tks
  fun insertString x [] = [x]
    | insertString x (y::L) = 
      case String.compare (x,y) of 
          LESS => y :: insertString x L
        | EQUAL => y :: L
        | GREATER => x :: (y::L)
  fun insertTokens tks tks' = List.foldl (fn (t,L) => insertToken t L) tks' tks
  fun insertStrings tks tks' = List.foldl (fn (t,L) => insertString t L) tks' tks
  val tokensOfGraphFull = List.foldl (fn (tin,L) => insertTokens (#token tin :: List.maps #inputTokens (#inputs tin)) L) []
  val tokensOfGraphQuick = List.foldl (fn (tin,L) => insertToken (#token tin) L) []
  val tokenNamesOfGraphQuick = List.foldl (fn (tin,L) => insertString (CSpace.nameOfToken (#token tin)) L) []

  fun factorise g = join g []
  fun normalise g = join g (makeFromTokens (tokensOfGraphFull g))

  fun isTotalOver f g = List.all (fn x => isSome (f x)) (tokensOfGraphQuick g)

  (* removes g from g'. This is not a trivially intuitive operation: after removing parts of g', 
    it re-adds any tokens that are still attached to existing arrows (the normalisation step does this). *)
  fun remove g g' =
    let 
      fun rem [] g = g
        | rem (tin::g) g' = rem g (removeTIN tin g')
    in 
      normalise (rem g g')
    end

  fun expand [] = []
    | expand (tin::g) = 
      (case #inputs tin of 
          [] => tin :: expand g 
        | (inp::INP) => {token = #token tin, inputs = [inp]} :: (expand ({token = #token tin, inputs = INP}::g)))

  (* larger subgraphs appear first *)
  fun subgraphs g =
    let 
      fun fsg [] = Seq.single empty
        | fsg (tin::g') = 
          let val S = fsg g' 
          in Seq.append (Seq.map (fn g'' => insertTIN tin g'') S) S 
          end
    in 
      fsg (expand g)
    end


  fun image (f1,_) g =
    let
      fun im (tin::gx) = 
        let 
          val mappedToken = valOf (f1 (#token tin))
          val inputs = #inputs tin
          fun inputImage inp = {constructor = #constructor inp, inputTokens = List.map (valOf o f1) (#inputTokens inp)}
          val mappedInputs = List.map inputImage inputs
        in 
          {token = mappedToken, inputs = mappedInputs} :: im gx
        end
    in 
      im g
    end

  fun preImage f g = image (invertMap f) g

  fun matchAllPairs p f (x::X) (y::Y) = if p(x,y) then matchAllPairs p (addPair (x,y) f) X Y else raise Fail
    | matchAllPairs _ f [] [] = f
    | matchAllPairs _ _ _ _ = raise Fail

  fun findInputMatches p f in1 [] = Seq.empty
    | findInputMatches p f in1 (in2::IN2') =
      let 
        val rest = findInputMatches p f in1 IN2'
      in
        if #constructor in1 = #constructor in2 then 
          Seq.cons (matchAllPairs p f (#inputTokens in1) (#inputTokens in2), in2) rest handle Fail => rest
        else
          rest
      end

  fun findINMonomorphisms p f [] IN2 = Seq.single f
    | findINMonomorphisms p f (in1::IN1') IN2 =
      let 
        fun monomorphismsPerResult (f',in2) = findINMonomorphisms p f' IN1' (List.remove in2 IN2)
        val inputMatches = findInputMatches p f in1 IN2
      in 
        Seq.maps monomorphismsPerResult inputMatches
      end

  fun findTINMonomorphisms p f tin1 tin2 =
      let 
        val (t1,t2) = (#token tin1,#token tin2)
      in
        if p(t1,t2) then 
          findINMonomorphisms p (addPair (t1,t2) f) (#inputs tin1) (#inputs tin2) handle Fail => Seq.empty
        else
          Seq.empty
      end

  fun findTINMatches p f tin1 [] = Seq.empty
    | findTINMatches p f tin1 (tin2::g2') =
      let 
        val this = findTINMonomorphisms p f tin1 tin2
        val rest = findTINMatches p f tin1 g2'
      in
        Seq.cons (this, tin2) rest handle Fail => rest
      end

  fun findMonomorphisms p f [] g2 = Seq.single f
    | findMonomorphisms p f (tin1::g1') g2 =
      let 
        fun monomorphismsPerResult (F,tin2) = 
            let val g2' = List.remove tin2 g2 
            in Seq.maps (fn f' => findMonomorphisms p f' g1' g2') F 
            end
        val TINMatches = findTINMatches p f tin1 g2
      in 
        Seq.maps monomorphismsPerResult TINMatches
      end

  fun tokenSpecialises T t1 t2 = (#subType T) (CSpace.typeOfToken t1,CSpace.typeOfToken t2)
  fun equivalentTokens t1 t2 = CSpace.tokensHaveSameType t1 t2

  fun tokenInSet t tks = List.exists (fn x => CSpace.sameTokens t x) tks

  fun findReificationsUpTo T (tks1,tks2) f g1 g2 =
    findMonomorphisms (fn (t1,t2) => tokenSpecialises T t2 t1 orelse tokenInSet t1 tks1 orelse tokenInSet t2 tks2) f g1 g2
  fun findReifications T f g1 g2 =
    findMonomorphisms (fn (t1,t2) => tokenSpecialises T t2 t1) f g1 g2

  fun findEmbeddingsUpTo T (tks1,tks2) f g1 g2 =
    findMonomorphisms (fn (t1,t2) => tokenSpecialises T t1 t2 orelse tokenInSet t1 tks1 orelse tokenInSet t2 tks2) f g1 g2
  fun findEmbeddings T f g1 g2 =
    findMonomorphisms (fn (t1,t2) => tokenSpecialises T t1 t2) f g1 g2

  fun findLooseningsUpTo T (tks1,tks2) f g1 g2 = Seq.map invertMap (findReificationsUpTo T (tks2,tks1) f g2 g1)
  fun findLoosenings T f g1 g2 = Seq.map invertMap (findReifications T f g2 g1)

  fun findLPMonomorphismsUpTo T (tks1,tks2) f g1 g2 = 
    findMonomorphisms (fn (t1,t2) => equivalentTokens t1 t2 orelse tokenInSet t1 tks1 orelse tokenInSet t2 tks2) f g1 g2

  (* The following actually allows extra constructor vertices to exist on g2 as long as we can inject g1 into g2 and tokens are in bijection *)
  fun findLPIsomorphismsUpTo T tks f g1 g2 = 
    Seq.filter (fn (_,f2) => isTotalOver f2 g2) (findLPMonomorphismsUpTo T tks f g1 g2)

end

signature MGRAPH =
sig
  type mTypeSystem = Type.typeSystem list
  type mgraph = Graph.graph list
  include TOKEN_MAP
  type constructor

  val image : map -> mgraph -> mgraph;
  val preImage : map -> mgraph -> mgraph;

  val wellTyped : CSpace.conSpecData list -> mgraph -> bool;
  val wellFormed : CSpace.conSpecData list -> mgraph -> bool;
  val tokenInGraphQuick : token -> mgraph -> bool;

  val empty : int -> mgraph;
  val tokensOfGraphFull : mgraph -> token list;
  val tokensOfGraphQuick : mgraph -> token list;
  val tokenNamesOfGraphQuick : mgraph -> string list;
  
  val join : mgraph -> mgraph -> mgraph;
  val remove : mgraph -> mgraph -> mgraph;

  val subgraphs : mgraph -> mgraph Seq.seq;
  val subgraphsRestricted : (int -> bool) -> mgraph -> mgraph Seq.seq;
  
  val findMonomorphisms : (int -> token * token -> bool) -> map -> mgraph -> mgraph -> map Seq.seq;

  val findReificationsUpTo : mTypeSystem -> token list * token list -> map -> mgraph -> mgraph-> map Seq.seq;
  val findReifications : mTypeSystem -> map -> mgraph -> mgraph-> map Seq.seq;
  val findEmbeddingsUpTo : mTypeSystem -> token list * token list -> map -> mgraph -> mgraph-> map Seq.seq;
  val findEmbeddings : mTypeSystem -> map -> mgraph -> mgraph-> map Seq.seq;
  val findLooseningsUpTo : mTypeSystem -> token list * token list -> map -> mgraph -> mgraph -> map Seq.seq;
  val findLoosenings : mTypeSystem -> map -> mgraph -> mgraph -> map Seq.seq;
end

structure MGraph : MGRAPH =
struct
  type mTypeSystem = Type.typeSystem list
  type mgraph = Graph.graph list
  open TokenMap
  infix 6 oo
  type constructor = Graph.constructor

  fun image f g = List.map (Graph.image f) g
  fun preImage f g = List.map (Graph.preImage f) g

  exception Mismatch;

  fun allPairs f [] [] = true
    | allPairs f (x::X) (y::Y) = f x y andalso allPairs f X Y
    | allPairs _ _ _ = raise Mismatch

  fun wellTyped CSDs g = allPairs Graph.wellTyped CSDs g
  fun wellFormed CSDs g = allPairs Graph.wellFormed CSDs g

  fun tokenInGraphQuick _ [] = false
    | tokenInGraphQuick t (x::X) = Graph.tokenInGraphQuick t x orelse tokenInGraphQuick t X

  fun empty 0 = []
    | empty i = Graph.empty :: empty (i-1)

  val tokensOfGraphFull = List.foldl (fn (gx,tks) => Graph.insertTokens (Graph.tokensOfGraphFull gx) tks) []
  val tokensOfGraphQuick = List.foldl (fn (gx,tks) => Graph.insertTokens (Graph.tokensOfGraphQuick gx) tks) []
  val tokenNamesOfGraphQuick = List.foldl (fn (gx,tks) => Graph.insertStrings (Graph.tokenNamesOfGraphQuick gx) tks) []

  fun mapPairs f [] [] = []
    | mapPairs f (x::X) (y::Y) = f x y :: mapPairs f X Y
    | mapPairs _ _ _ = raise Mismatch

  fun join g g' = mapPairs Graph.join g g'
  fun remove g g' = mapPairs Graph.remove g g'

  fun mapProduct _ [] = Seq.single []
    | mapProduct f (g::gs) = Seq.maps (fn h => (Seq.map (fn x => h :: x) (mapProduct f gs))) (f g)

  fun subgraphs g = mapProduct Graph.subgraphs g
  
  fun subgraphsRestricted I g = 
    let
      fun sgod _ [] = Seq.single []
        | sgod i (x::X) = 
            Seq.maps (fn h => (Seq.map (fn x => h :: x) (sgod (i+1) X)))
                     (if I i then Seq.single x else Graph.subgraphs x)
    in
      sgod 1 g
    end

 
  fun foldMaps h i f [] [] = Seq.single f
    | foldMaps h i f (x::X) (y::Y) = Seq.maps (fn f' => foldMaps h (i+1) f' X Y) (h i f x y)
    | foldMaps _ _ _ _ _ = raise Mismatch

  fun findMonomorphisms p f g1 g2 = foldMaps (fn i => Graph.findMonomorphisms (p i)) 0 f g1 g2 

  fun findReificationsUpTo T tks f g1 g2 = foldMaps (fn i => Graph.findReificationsUpTo (List.nth(T,i)) tks) 0 f g1 g2 
  fun findReifications T f g1 g2 = foldMaps (fn i => Graph.findReifications (List.nth(T,i))) 0 f g1 g2 
  fun findEmbeddingsUpTo T tks f g1 g2 = foldMaps (fn i => Graph.findEmbeddingsUpTo (List.nth(T,i)) tks) 0 f g1 g2 
  fun findEmbeddings T f g1 g2 = foldMaps (fn i => Graph.findEmbeddings (List.nth(T,i))) 0 f g1 g2 
  fun findLooseningsUpTo T tks f g1 g2 = foldMaps (fn i => Graph.findLooseningsUpTo (List.nth(T,i)) tks) 0 f g1 g2 
  fun findLoosenings T f g1 g2 = foldMaps (fn i => Graph.findLoosenings (List.nth(T,i))) 0 f g1 g2 
end