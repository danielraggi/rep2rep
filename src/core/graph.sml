import "core.cspace";

(* Graphs in a multi-space *)
signature GRAPH =
sig 
  type token;
  type constructor;

  type TIN; (* token's incoming neighbourhood *)
  type graph;
  type map;

  val wellTyped : CSpace.conSpecData -> graph -> bool;
  val wellFormed : CSpace.conSpecData -> graph -> bool;
  val tokensOfTIN : TIN -> token list;
  val tokensOfGraph : graph -> token list;

  (*
  val normal : graph -> bool;
  *)
  val makeFromTokens : token list -> graph;
  val join : graph -> graph -> graph;
  val normalise : graph -> graph;

  (* 
  findMonomorphisms f p g1 g2 finds every extension of f that is a monomorphism 
  m from g1 to g2 provided it satisfies p(t,m(t)) for every token t.
  It assumes the g1 and g2 are in normal form.
  *)
  val findMonomorphisms : (token * token -> bool) -> map -> graph -> graph -> map Seq.seq;

  val findReificationsUpTo : Type.typeSystem -> token list -> map -> graph -> graph -> map Seq.seq;
  val findLooseningsUpTo : Type.typeSystem -> token list -> map -> graph -> graph -> map Seq.seq;

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

  fun invertMap (f1,f2) = (f2,f1)

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

  fun insertTIN tin [] = [tin]
    | insertTIN tin (tin'::g) =
      if CSpace.sameTokens (#token tin) (#token tin') then
        {token = #token tin, inputs = (#inputs tin) @ (#inputs tin')} :: g
      else
        tin' :: insertTIN tin g

  fun join [] g = g
    | join (tin::g) g' = insertTIN tin (join g g')

  fun makeFromTokens [] = []
    | makeFromTokens (t::ts) = insertTIN {token = t, inputs = []} (makeFromTokens ts)

  fun tokensOfTIN tin = #token tin :: List.flatmap #inputTokens (#inputs tin)
  fun tokensOfGraph g = List.flatmap tokensOfTIN g
  fun isTotalOver f g = List.all (fn x => isSome (f x)) (tokensOfGraph g)

  fun normalise g = join g (makeFromTokens (tokensOfGraph g))


  exception Fail

  fun addPair (x,y) (fl,fr) = 
      (case fl x of 
          SOME z => if CSpace.sameTokens y z then fl else raise Fail
        | NONE => (fn t => if CSpace.sameTokens t x then SOME y else fl t),
      case fr y of 
          SOME z => if CSpace.sameTokens x z then fr else raise Fail
        | NONE => (fn t => if CSpace.sameTokens t y then SOME x else fr t))

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

  fun findReificationsUpTo T tks f g1 g2 =
    findMonomorphisms (fn (t1,t2) => tokenSpecialises T t2 t1 orelse tokenInSet t1 tks) f g1 g2

  fun findLooseningsUpTo T tks f g1 g2 = Seq.map invertMap (findReificationsUpTo T tks f g2 g1)

  fun findLPMonomorphismsUpTo T tks f g1 g2 = 
    findMonomorphisms (fn (t1,t2) => equivalentTokens t1 t2 orelse tokenInSet t1 tks) f g1 g2

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

  val wellTyped : CSpace.conSpecData list -> mgraph -> bool;
  val wellFormed : CSpace.conSpecData list -> mgraph -> bool;
  
  val findMonomorphisms : (token * token -> bool) -> map -> mgraph -> mgraph -> map Seq.seq;

  val findReificationsUpTo : Type.typeSystem -> token list -> map -> mgraph -> mgraph-> map Seq.seq;
  val findLooseningsUpTo : Type.typeSystem -> token list -> map -> mgraph -> mgraph -> map Seq.seq;
end

structure MGraph : MGRAPH =
struct
  type mgraph = Graph.graph list
  type token = Graph.token
  type constructor = Graph.constructor
  type map = Graph.map

  exception Mismatch;

  fun allPairs f [] [] = true
    | allPairs f (x::X) (y::Y) = f x y andalso allPairs f X Y
    | allPairs _ _ _ = raise Mismatch

  fun wellTyped CSDs g = allPairs Graph.wellTyped CSDs g
  fun wellFormed CSDs g = allPairs Graph.wellFormed CSDs g

  fun foldUpdateMap h f [] [] = Seq.single f
    | foldUpdateMap h f (x::X) (y::Y) = Seq.maps (fn f' => foldUpdateMap h f' X Y) (h f x y)
    | foldUpdateMap _ _ _ _ = raise Mismatch

  fun findMonomorphisms p f g1 g2 = foldUpdateMap (Graph.findMonomorphisms p) f g1 g2 
  fun findReificationsUpTo T tks f g1 g2 = foldUpdateMap (Graph.findReificationsUpTo T tks) f g1 g2 
  fun findLooseningsUpTo T tks f g1 g2 = foldUpdateMap (Graph.findLooseningsUpTo T tks) f g1 g2 
end