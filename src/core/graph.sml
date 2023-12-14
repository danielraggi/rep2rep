import "core.cspace";

(* Graphs in a multi-space *)
signature GRAPH =
sig 
  type token;
  type constructor;

  type TIN; (* token's incoming neighbourhood *)
  type graph;
  type map;
  
  val image : map -> graph -> graph;
  val preImage : map -> graph -> graph;
  val extendMap : map -> graph -> string list -> map * string list;

  val wellTyped : CSpace.conSpecData -> graph -> bool;
  val wellFormed : CSpace.conSpecData -> graph -> bool;
  val tokensOfTIN : TIN -> token list;
  val tokensOfGraph : graph -> token list;

  (*
  val normal : graph -> bool;
  *)
  val empty : graph;
  val makeFromTokens : token list -> graph;
  val join : graph -> graph -> graph;
  val remove : graph -> graph -> graph;
  val normalise : graph -> graph;

  val subgraphs : graph -> graph Seq.seq;

  (* 
  findMonomorphisms f p g1 g2 finds every extension of f that is a monomorphism 
  m from g1 to g2 provided it satisfies p(t,m(t)) for every token t.
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
  (*type typ = Type.typ*)
  (*type sig = {input : typ list, output : typ}*)
  type token = CSpace.token (*{id : string, type : typ}*)
  type constructor = CSpace.constructor (*{id : string, sig : sig}*)
  type 'a set = 'a list

  type TIN = {token : token, inputs : {constructor : string, inputTokens : token list} set}
  type graph = TIN set
  type map = (token -> token option) * (token -> token option)


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
        tin' :: insertTIN tin g

  fun join [] g = g
    | join (tin::g) g' = insertTIN tin (join g g')

  val empty = [];

  fun makeFromTokens [] = []
    | makeFromTokens (t::ts) = insertTIN {token = t, inputs = []} (makeFromTokens ts)

  fun tokensOfTIN tin = #token tin :: List.flatmap #inputTokens (#inputs tin)
  fun tokensOfGraph g = List.flatmap tokensOfTIN g
  fun isTotalOver f g = List.all (fn x => isSome (f x)) (tokensOfGraph g)

  fun normalise g = join g (makeFromTokens (tokensOfGraph g))

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

  fun subgraphs g =
    let fun fsg [] = Seq.single empty
          | fsg (tin::g') = 
          let val S = fsg g' 
          in Seq.append (Seq.map (fn g'' => tin :: g'') S) S 
          end
    in Seq.map normalise (fsg (expand g))
    end

  exception Fail


  (*
    functions for building and operating with maps
  *)
  fun invertMap (f1,f2) = (f2,f1)

  exception Undefined

  fun image (f1,_) g =
    let
      fun im (tin::gx) = 
        let 
          val mappedToken = case f1 (#token tin) of SOME t' => t' | _ => raise Undefined
          val inputs = #inputs tin
          fun inputImage inp = {constructor = #constructor inp, inputTokens = List.map (valOf o f1) (#inputTokens inp)}
          val mappedInputs = List.map inputImage inputs
        in 
          {token = mappedToken, inputs = mappedInputs} :: im gx
        end
    in normalise (im g)
    end

  fun preImage f g = image (invertMap f) g

  (* updates a monomorphism so that fl(x) = y and fr(y) = x. 
     Fails if map is already defined on that pair with different value. *)
  fun addPair (x,y) (fl,fr) = 
      (case fl x of 
          SOME z => if CSpace.sameTokens y z then fl else raise Fail
        | NONE => (fn t => if CSpace.sameTokens t x then SOME y else fl t),
      case fr y of 
          SOME z => if CSpace.sameTokens x z then fr else raise Fail
        | NONE => (fn t => if CSpace.sameTokens t y then SOME x else fr t))

  fun firstUnusedName Ns =
    let fun mkFun n =
          let val vcandidate = "v_{"^(Int.toString n)^"}"
          in if FiniteSet.exists (fn x => x = vcandidate) Ns
              then mkFun (n+1)
              else vcandidate
          end
    in mkFun 0
    end

  (* assuming f : g' -> h' is a label-preserving monomorphism where g' is a subgraph of g, 
     it returns a label-preserving monomorphism f' such that f' : g -> h is a monomorphism that extends f, 
     and f(x) is not in tks (e.g., it avoids clashes) *)
  fun extendMap f [] tks = (f,tks)
    | extendMap f (tin::g) tokenIDs = 
    let 
      val tokenOfTIN = #token tin
      val mappedToken = CSpace.makeToken (firstUnusedName tokenIDs) (CSpace.typeOfToken tokenOfTIN)
      val updatedMap = addPair (tokenOfTIN,mappedToken) f
    in 
      extendMap updatedMap g (CSpace.nameOfToken tokenOfTIN :: tokenIDs)
    end

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
  type mgraph = Graph.graph list
  type token
  type constructor
  type map

  val image : map -> mgraph -> mgraph;
  val preImage : map -> mgraph -> mgraph;
  val extendMap : map -> mgraph -> string list -> map * string list;

  val wellTyped : CSpace.conSpecData list -> mgraph -> bool;
  val wellFormed : CSpace.conSpecData list -> mgraph -> bool;

  val empty : int -> mgraph;
  val tokensOfGraph : mgraph -> token list;
  
  val join : mgraph -> mgraph -> mgraph;
  val remove : mgraph -> mgraph -> mgraph;

  val subgraphs : mgraph -> mgraph Seq.seq;
  
  val findMonomorphisms : (token * token -> bool) -> map -> mgraph -> mgraph -> map Seq.seq;

  val findReificationsUpTo : Type.typeSystem -> token list * token list -> map -> mgraph -> mgraph-> map Seq.seq;
  val findReifications : Type.typeSystem -> map -> mgraph -> mgraph-> map Seq.seq;
  val findEmbeddingsUpTo : Type.typeSystem -> token list * token list -> map -> mgraph -> mgraph-> map Seq.seq;
  val findEmbeddings : Type.typeSystem -> map -> mgraph -> mgraph-> map Seq.seq;
  val findLooseningsUpTo : Type.typeSystem -> token list * token list -> map -> mgraph -> mgraph -> map Seq.seq;
  val findLoosenings : Type.typeSystem -> map -> mgraph -> mgraph -> map Seq.seq;
end

structure MGraph : MGRAPH =
struct
  type mgraph = Graph.graph list
  type token = Graph.token
  type constructor = Graph.constructor
  type map = Graph.map

  fun image f g = List.map (Graph.image f) g
  fun preImage f g = List.map (Graph.preImage f) g
  fun extendMap f [] tks = (f,tks)
    | extendMap f (x::X) tks = 
      let 
        val (updatedMap,updatedTks) = Graph.extendMap f x tks
      in
        extendMap updatedMap X updatedTks
      end

  exception Mismatch;

  fun allPairs f [] [] = true
    | allPairs f (x::X) (y::Y) = f x y andalso allPairs f X Y
    | allPairs _ _ _ = raise Mismatch

  fun wellTyped CSDs g = allPairs Graph.wellTyped CSDs g
  fun wellFormed CSDs g = allPairs Graph.wellFormed CSDs g

  fun empty 0 = []
    | empty i = Graph.empty :: empty (i-1)

  val tokensOfGraph = List.foldl (fn (gx,tks) => Graph.tokensOfGraph gx @ tks) []

  fun mapPairs f [] [] = []
    | mapPairs f (x::X) (y::Y) = f x y :: mapPairs f X Y
    | mapPairs _ _ _ = raise Mismatch

  fun join g g' = mapPairs Graph.join g g'
  fun remove g g' = mapPairs Graph.remove g g'

  fun mapProduct f [] = Seq.single []
    | mapProduct f (g::gs) = Seq.maps (fn h => (Seq.map (fn x => h :: x) (mapProduct f gs))) (f g)

  fun subgraphs g = mapProduct Graph.subgraphs g
 
  fun foldMaps h f [] [] = Seq.single f
    | foldMaps h f (x::X) (y::Y) = Seq.maps (fn f' => foldMaps h f' X Y) (h f x y)
    | foldMaps _ _ _ _ = raise Mismatch

  fun findMonomorphisms p f g1 g2 = foldMaps (Graph.findMonomorphisms p) f g1 g2 

  fun findReificationsUpTo T tks f g1 g2 = foldMaps (Graph.findReificationsUpTo T tks) f g1 g2 
  fun findReifications T f g1 g2 = foldMaps (Graph.findReifications T) f g1 g2 
  fun findEmbeddingsUpTo T tks f g1 g2 = foldMaps (Graph.findEmbeddingsUpTo T tks) f g1 g2 
  fun findEmbeddings T f g1 g2 = foldMaps (Graph.findEmbeddings T) f g1 g2 
  fun findLooseningsUpTo T tks f g1 g2 = foldMaps (Graph.findLooseningsUpTo T tks) f g1 g2 
  fun findLoosenings T f g1 g2 = foldMaps (Graph.findLoosenings T) f g1 g2 
end