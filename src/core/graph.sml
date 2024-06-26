import "core.cspace";
import "util.rpc";

signature TOKEN_MAP =
sig
  type token;
  type map; (* these maps are one-to-one relations between tokens. Useful as we use monomorphisms a lot. *)

  val emptyMap : map;
  val identityMap : map;
  val addPair : token * token -> map -> map;
  val updateMap : token * token -> map -> map;
  
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
 
  (* updates a one-to-one map so that fl(x) = y and fr(y) = x. 
     Fails if x or y are already mapped to a different element. *)
  fun addPair (x,y) (fl,fr) = 
      (case fl x of 
          SOME z => if CSpace.sameTokens y z then fl else raise Fail "not functional"
        | NONE => (fn t => if CSpace.sameTokens t x then SOME y else fl t),
       case fr y of 
          SOME z => if CSpace.sameTokens x z then fr else raise Fail "not injective"
        | NONE => (fn t => if CSpace.sameTokens t y then SOME x else fr t))

  fun updateMap (x,y) (fl,fr) = 
    (fn t => if CSpace.sameTokens x t then SOME y else (case fl x of SOME y' => (case fr y' of SOME x' => if CSpace.sameTokens x' t then NONE else fl t | _ => fl t) | _ => fl t), 
     fn t => if CSpace.sameTokens y t then SOME x else (case fr x of SOME x' => (case fl x' of SOME y' => if CSpace.sameTokens y' t then NONE else fr t | _ => fr t) | _ => fr t))

  (*
    functions for building and operating with maps
  *)
  fun applyMap (fl,_) = fl
  fun applyInvMap (_,fr) = fr

  fun invertMap (fl,fr) = (fr,fl)

  fun restrictDomain (fl,fr) tks =
    (fn t => if List.exists (fn x => CSpace.sameTokens x t) tks then NONE else fl t,
     fn t => (case fr t of NONE => NONE | SOME y => if List.exists (fn x => CSpace.sameTokens x y) tks then NONE else fr t))

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
  val TIN_rpc : TIN Rpc.Datatype.t;
  val graph_rpc : graph Rpc.Datatype.t;

  val toString : graph -> string;

  val image : map -> graph -> graph;
  val preImage : map -> graph -> graph;
  val imageWeak : map -> graph -> graph;
  val imageWeakTypeGeneralising : Type.typeSystem -> map -> graph -> graph;

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
  val intersection : graph -> graph -> graph;

  val insertTIN : TIN -> graph -> graph;

  (* factorising makes no more than one tin (token's incoming neighbourhood) for every token *)
  val factorise : graph -> graph;
  
  (* expanding separates the configurations of each token into individual tins. 
    Also adds a tin for each token without inputs. factorise(expand(g)) = g *)
  val expand : graph -> graph;

  (* normalising adds all tokens that appear in the graph and factorises their 
  configurations into a tin for each token *)
  val normalise : graph -> graph;
  val normal : graph -> bool;

  val isEmpty : graph -> bool;
  val size : graph -> int;
  val numberOfTokens : graph -> int;
  val numberOfConstructors : graph -> int;
  val contained : graph -> graph -> bool;
  val equal : graph -> graph -> bool;

  val subgraphs : graph -> graph Seq.seq;
  val pullTINOfToken : graph -> token -> TIN option * graph;
  val pullTINsOfTokens : graph -> token list -> graph * graph;
  val orderByHierarchy : graph -> graph;
  val largestConstructionOfToken : graph -> token -> graph;
  val largestConstructionsInGraph : graph -> graph list;
  val isConstructionOfToken : graph -> token -> bool;
  val isConstruction : graph -> bool;

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

  type input = {constructor : string, inputTokens : token list}
  type TIN = {token : token, inputs : input set}
  type graph = TIN set

  val input_rpc = Rpc.Datatype.convert
                      "Graph.input"
                      (Rpc.Datatype.tuple2 (String.string_rpc, List.list_rpc CSpace.token_rpc))
                      (fn (c,i) => {constructor = c, inputTokens = i})
                      (fn {constructor,inputTokens} => (constructor,inputTokens))

  val TIN_rpc = Rpc.Datatype.convert
                      "Graph.TIN"
                      (Rpc.Datatype.tuple2 (CSpace.token_rpc, List.list_rpc input_rpc))
                      (fn (t,i) => {token = t, inputs = i})
                      (fn {token,inputs} => (token,inputs))
                      
  val graph_rpc = Rpc.Datatype.alias
                        "Graph.graph"
                        (List.list_rpc TIN_rpc)

  fun stringOfInputs [] = ""
    | stringOfInputs [{constructor,inputTokens}] = constructor ^  List.toString CSpace.stringOfToken inputTokens
    | stringOfInputs ({constructor,inputTokens}::inps) = constructor ^  List.toString CSpace.stringOfToken inputTokens ^ "|" ^ stringOfInputs inps
  fun stringOfTIN {token,inputs = []} = CSpace.stringOfToken token
    | stringOfTIN {token,inputs} = CSpace.stringOfToken token ^ "<-" ^ stringOfInputs inputs
  fun toString' [] = "EMPTY"
    | toString' [tin] = stringOfTIN tin
    | toString' (tin::g) = stringOfTIN tin ^ ", " ^ toString' g
  
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
  val isEmpty = null;

  val numberOfTokens = length
  fun numberOfConstructors [] = 0
    | numberOfConstructors (tin::g) = length (#inputs tin) + numberOfConstructors g
  fun size g = numberOfTokens g + numberOfConstructors g

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
  val tokensOfGraphFull = List.foldl (fn (tin,L) => insertTokens (#token tin :: List.flatmap #inputTokens (#inputs tin)) L) []
  val tokensOfGraphQuick = List.foldl (fn (tin,L) => insertToken (#token tin) L) []
  val tokenNamesOfGraphQuick = List.foldl (fn (tin,L) => insertString (CSpace.nameOfToken (#token tin)) L) []

  fun factorise g = join g []
  fun normalise g = join g (makeFromTokens (tokensOfGraphFull g))

  fun isTotalOver f g = List.all (fn x => isSome (f x)) (tokensOfGraphQuick g)

  (* removes g from g'. This is not a trivially intuitive operation: after removing parts of g', 
    it re-adds any tokens that are still attached to existing arrows (the normalisation step does this). *)
  fun remove g g' =
    let 
      fun rem [] g' = g'
        | rem (tin::g) g' = rem g (removeTIN tin g')
    in 
      normalise (rem g g')
    end

  fun inputContained inp [] = false
    | inputContained inp (inp'::inps') = 
    (#constructor inp = #constructor inp' andalso allPairs CSpace.sameTokens (#inputTokens inp) (#inputTokens inp')) orelse 
    inputContained inp inps'

  fun inputsContained [] inps' = true
    | inputsContained (inp::inps) inps' = inputContained inp inps' andalso inputsContained inps inps'

  fun tinContained _ [] = false
    | tinContained tin (tin'::g') =
      (CSpace.sameTokens (#token tin) (#token tin') andalso inputsContained (#inputs tin) (#inputs tin')) orelse tinContained tin g'

  fun contained [] g' = true
    | contained (tin::g) g' = tinContained tin g' andalso contained g g'

  fun equal g g' = contained g g' andalso contained g' g

  fun normal g = equal g (normalise g)

  fun expand [] = []
    | expand (tin::g) = 
      (case #inputs tin of 
          [] => tin :: expand g 
        | [inp] => tin :: expand g 
        | (inp::INP) => {token = #token tin, inputs = [inp]} :: (expand ({token = #token tin, inputs = INP}::g)))

  fun findInputsIntersection [] _ = []
    | findInputsIntersection (inp::inps) inps' =
    if inputContained inp inps' then 
      inp :: findInputsIntersection inps inps' 
    else 
      findInputsIntersection inps inps'

  fun findTinIntersection _ [] = NONE
    | findTinIntersection tin (tin'::g') =
      if CSpace.sameTokens (#token tin) (#token tin') then
        SOME ({token = #token tin, inputs = findInputsIntersection (#inputs tin) (#inputs tin')})
      else
        findTinIntersection tin g'

  fun intersection g g' =
    let 
      fun inter [] g' = []
        | inter (tin::g) g' = case findTinIntersection tin g' of SOME x => x :: inter g g' | NONE => inter g g'
    in
      normalise (inter g g')
    end
  
  fun toString g = toString' (expand g)

  (* larger subgraphs appear first *)
  fun subgraphs g =
    let 
      fun fsg [] = Seq.single empty
        | fsg (tin::g') = 
          let val S = fsg g' 
          in Seq.insertManyNoRepetition S (Seq.map (fn g'' => insertTIN tin g'') S) (fn _ => EQUAL) (fn (x,y) => equal x y)
          end
    in 
      fsg (expand g)
    end

  fun findTINForToken _ [] = NONE
    | findTINForToken t (tin::g) = if CSpace.sameTokens t (#token tin) then SOME tin else findTINForToken t g
    
  fun getMissingOneStepDescendants tks g t = 
    let val oneStepDescendants = List.flatmap #inputTokens (#inputs (valOf (findTINForToken t g)))
    in List.filter (fn x => not (List.exists (fn y => CSpace.sameTokens x y) tks)) oneStepDescendants
    end
  fun assessTokenHierarchy tks (g:graph) t = 
    1 + (List.max (fn (x,y) => Int.compare (x,y)) (map (assessTokenHierarchy (t::tks) g) (getMissingOneStepDescendants (t::tks) g t))) handle Empty => 1 | Option => 0

  fun assignTokenHierarchy [] _ = []
    | assignTokenHierarchy (tin::g:graph) g' =
    {h = assessTokenHierarchy [] g' (#token tin), tin = tin} :: assignTokenHierarchy g g'

  fun orderByHierarchy (g:graph) = map #tin (List.mergesort (fn (x,y) => Int.compare(#h y,#h x)) (assignTokenHierarchy g g))

  fun descendantTokens tks g t = 
    let val oneStepDescendants = getMissingOneStepDescendants tks g t
        fun dts _ [] = []
          | dts tks' (d::ds) = (case descendantTokens tks' g d of dd => dd @ dts (tks' @ dd) ds)
    in oneStepDescendants @ dts (tks @ oneStepDescendants) oneStepDescendants
    end

  fun descendantTokens' tks g [] = []
    | descendantTokens' tks g (t::ts) = (case descendantTokens tks g t of dtks => dtks @ descendantTokens' (dtks @ tks) g ts)

  fun pullTINOfToken (g:graph) t = (case List.partition (fn tin => CSpace.sameTokens t (#token tin)) g of ([tin],g') => (SOME tin,g') | _ => (NONE,g))
  fun pullTINsOfTokens (g:graph) tks = List.partition (fn tin => List.exists (fn x => CSpace.sameTokens x (#token tin)) tks) g

  fun largestConstructionOfToken (g:graph) t =
    let
      fun lcot seenTks tk = 
        let 
          val firstTIN = valOf (findTINForToken tk g)
          val newSeenTokens = tk::seenTks
          val oneStepDescendants = getMissingOneStepDescendants newSeenTokens g tk
        in 
          firstTIN :: List.flatmap (lcot newSeenTokens) oneStepDescendants
        end
    in 
      normalise (lcot [] t)
    end

  fun largestConstructionsInGraph g =
    let 
      val g' = orderByHierarchy g
      val t = #token (hd g')
      val ct = largestConstructionOfToken g' t
    in ct :: (if equal g' ct then [] else largestConstructionsInGraph (remove ct g'))
    end handle Empty => empty

  fun isConstructionOfToken g t = equal g (largestConstructionOfToken g t)
  fun isConstruction g = List.exists (fn t => isConstructionOfToken g t) (tokensOfGraphQuick g)

  fun mymap f [] = []
    | mymap f (h::t) = (f h handle Option => (print ("\n\n token: " ^ CSpace.stringOfToken h ^ "\n\n"); raise Option)) :: mymap f t

  fun image (f1,_) g =
    let
      fun im [] = []
        | im (tin::gx) = 
        let 
          val mappedToken = valOf (f1 (#token tin))
          val inputs = #inputs tin
          fun inputImage inp = {constructor = #constructor inp, inputTokens = mymap (valOf o f1) (#inputTokens inp)} 
          val mappedInputs = List.map inputImage inputs handle Option => (print ("\n\n graph: "^ toString g ^"\n\n"); raise Option)
        in 
          {token = mappedToken, inputs = mappedInputs} :: im gx
        end
    in 
      im g handle Option => raise Fail "undefined image"
    end

  fun imageWeak (f1,_) g =
    let
      fun mapWeak t = 
        case f1 t of NONE => t 
                   | SOME t' => ((*if (CSpace.typeOfToken t) <> (CSpace.typeOfToken t') 
                                 then print ("\n" ^ CSpace.stringOfToken t ^ " " ^ CSpace.stringOfToken t' ^ "\n")
                                 else (); *)
                                 t')
      fun im [] = []
        | im (tin::gx) = 
        let 
          val mappedToken = mapWeak (#token tin)
          val inputs = #inputs tin
          fun inputImage inp = {constructor = #constructor inp, inputTokens = List.map mapWeak (#inputTokens inp)}
          val mappedInputs = List.map inputImage inputs
        in 
          {token = mappedToken, inputs = mappedInputs} :: im gx
        end
    in 
      im g
    end

  fun imageWeakTypeGeneralising T (f1,_) g =
    let
      fun mapWeak t = case f1 t of NONE => t | SOME t' => if #subType T (CSpace.typeOfToken t, CSpace.typeOfToken t') then t' else raise Fail "type generalising"
      fun im [] = []
        | im (tin::gx) = 
        let 
          val mappedToken = mapWeak (#token tin)
          val inputs = #inputs tin
          fun inputImage inp = {constructor = #constructor inp, inputTokens = List.map mapWeak (#inputTokens inp)}
          val mappedInputs = List.map inputImage inputs
        in 
          {token = mappedToken, inputs = mappedInputs} :: im gx
        end
    in 
      im g
    end

  fun preImage f g = image (invertMap f) g

  fun matchAllPairs p f (x::X) (y::Y) = if p(x,y) then matchAllPairs p (addPair (x,y) f) X Y else raise Fail "property"
    | matchAllPairs _ f [] [] = f
    | matchAllPairs _ _ _ _ = raise Fail "mismatch"

  fun findInputMatches p f in1 [] = Seq.empty
    | findInputMatches p f in1 (in2::IN2') =
      let 
        val rest = findInputMatches p f in1 IN2'
      in
        if #constructor in1 = #constructor in2 then 
          Seq.cons (matchAllPairs p f (#inputTokens in1) (#inputTokens in2), in2) rest handle Fail _ => rest
        else
          rest
      end

  fun findINMonomorphisms p f [] IN2 = Seq.single f
    | findINMonomorphisms p f (in1::IN1) IN2 =
      let 
        fun monomorphismsPerResult (f',in2) = findINMonomorphisms p f' IN1 (List.remove in2 IN2)
        val inputMatches = findInputMatches p f in1 IN2
      in 
        Seq.maps monomorphismsPerResult inputMatches
      end

  fun findTINMonomorphisms p f tin1 tin2 =
      let 
        val (t1,t2) = (#token tin1,#token tin2)
      in
        if p(t1,t2) then 
          findINMonomorphisms p (addPair (t1,t2) f) (#inputs tin1) (#inputs tin2) handle Fail _ => Seq.empty
        else
          Seq.empty
      end

  fun findTINMatches p f tin1 [] = Seq.empty
    | findTINMatches p f tin1 (tin2::g2') =
      let 
        val this = findTINMonomorphisms p f tin1 tin2
        val rest = findTINMatches p f tin1 g2'
      in
        Seq.cons (this, tin2) rest handle Fail _ => rest
      end

  fun findMonomorphisms p f [] g2 = Seq.single f
    | findMonomorphisms p f (tin1::g1') g2 =
      let 
        fun monomorphismsPerResult (F,tin2) = 
            let val g2' = removeTIN tin2 g2 
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
    findMonomorphisms (fn (t1,t2) => tokenSpecialises T t1 t2 orelse (tokenSpecialises T t2 t1 andalso (tokenInSet t1 tks1 orelse tokenInSet t2 tks2))) f g1 g2
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

  val toString : mgraph -> string;

  val image : map -> mgraph -> mgraph;
  val preImage : map -> mgraph -> mgraph;
  val imageWeak : map -> mgraph -> mgraph;
  val imageWeakTypeGeneralising : mTypeSystem -> map -> mgraph -> mgraph;

  val size : mgraph -> int;

  val wellTyped : CSpace.conSpecData list -> mgraph -> bool;
  val wellFormed : CSpace.conSpecData list -> mgraph -> bool;
  val tokenInGraphQuick : token -> mgraph -> bool;

  val empty : int -> mgraph;
  val isEmpty : mgraph -> bool;
  val tokensOfGraphFull : mgraph -> token list;
  val tokensOfGraphQuick : mgraph -> token list;
  val tokenNamesOfGraphQuick : mgraph -> string list;

  val normalise : mgraph -> mgraph;
  val normal : mgraph -> bool;
  
  val join : mgraph -> mgraph -> mgraph;
  val remove : mgraph -> mgraph -> mgraph;
  val intersection : mgraph -> mgraph -> mgraph;

  val contained : mgraph -> mgraph -> bool;
  val equal : mgraph -> mgraph -> bool;

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

  fun toString [] = ""
    | toString [g] = Graph.toString g
    | toString (g::gs) = Graph.toString g  ^ " ;; " ^ toString gs 

  fun image f g = List.map (Graph.image f) g
  fun preImage f g = List.map (Graph.preImage f) g
  fun imageWeak f g = List.map (Graph.imageWeak f) g
  fun imageWeakTypeGeneralising [] _ [] = []
    | imageWeakTypeGeneralising (T::Ts) f (g::gs) = Graph.imageWeakTypeGeneralising T f g :: imageWeakTypeGeneralising Ts f gs
    | imageWeakTypeGeneralising _ _ _ = (print "horror"; raise Match)

  fun size g = List.sumMapInt (Graph.size) g

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
  val isEmpty = List.all Graph.isEmpty

  val tokensOfGraphFull = List.foldl (fn (gx,tks) => Graph.insertTokens (Graph.tokensOfGraphFull gx) tks) []
  val tokensOfGraphQuick = List.foldl (fn (gx,tks) => Graph.insertTokens (Graph.tokensOfGraphQuick gx) tks) []
  val tokenNamesOfGraphQuick = List.foldl (fn (gx,tks) => Graph.insertStrings (Graph.tokenNamesOfGraphQuick gx) tks) []

  fun mapPairs f [] [] = []
    | mapPairs f (x::X) (y::Y) = f x y :: mapPairs f X Y
    | mapPairs _ _ _ = raise Mismatch

  fun normalise g = map Graph.normalise g
  fun join g g' = mapPairs Graph.join g g'
  fun remove g g' = mapPairs Graph.remove g g'
  fun intersection g g' = mapPairs Graph.intersection g g'

  fun contained g g' = allPairs Graph.contained g g'
  fun equal g g' = allPairs Graph.equal g g'
  fun normal g = List.all Graph.normal g

  fun mapProduct _ [] = Seq.single []
    | mapProduct f (g::gs) = Seq.maps (fn h => (Seq.map (fn x => h :: x) (mapProduct f gs))) (f g)

  fun subgraphs g = mapProduct Graph.subgraphs g
  
  fun subgraphsRestricted I g = 
    let
      fun sgod _ [] = Seq.single []
        | sgod i (x::X) = 
            Seq.maps (fn h => (Seq.map (fn x => h :: x) (sgod (i+1) X)))
                     (if I i then Seq.single x else Seq.cons x (Seq.single Graph.empty))
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