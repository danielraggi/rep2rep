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
  val normalise : graph -> graph;
  *)

  (* findMonomorphisms f p g1 g2 finds every monomorphism m of g1 to g2 that satisfies p(t,m(t)) and is compatible with f *)
  val findMonomorphisms : map -> (token * token -> bool) -> graph -> graph -> map Seq.seq;

  val findReificationsUpTo : Type.typeSystem -> map -> graph -> graph -> token list -> map Seq.seq;
  val findLooseningsUpTo : Type.typeSystem -> map -> graph -> graph -> token list -> map Seq.seq;

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

  exception Fail

  fun addPair (x,y) (fl,fr) = 
      (case fl x of 
          SOME z => if CSpace.sameTokens y z then fl else raise Fail
        | NONE => (fn t => if CSpace.sameTokens t x then SOME y else fl t),
      case fr y of 
          SOME z => if CSpace.sameTokens x z then fr else raise Fail
        | NONE => (fn t => if CSpace.sameTokens t y then SOME x else fr t))

  fun matchAllPairs f p (x::X) (y::Y) = if p(x,y) then matchAllPairs (addPair (x,y) f) p X Y else raise Fail
    | matchAllPairs f _ [] [] = f
    | matchAllPairs _ _ _ _ = raise Fail

  fun findInputMatches f p in1 [] = Seq.empty
    | findInputMatches f p in1 (in2::IN2') =
      let 
        val rest = findInputMatches f p in1 IN2'
      in
        if #constructor in1 = #constructor in2 then 
          Seq.cons (matchAllPairs f p (#inputTokens in1) (#inputTokens in2), in2) rest handle Fail => rest
        else
          rest
      end

  fun findINMonomorphisms f p [] IN2 = Seq.single f
    | findINMonomorphisms f p (in1::IN1') IN2 =
      let 
        fun MonomorphismsPerResult (f',in2) = findINMonomorphisms f' p IN1' (List.remove in2 IN2)
        val inputMatches = findInputMatches f p in1 IN2
      in 
        Seq.maps MonomorphismsPerResult inputMatches
      end

  fun findTINMonomorphisms f p tin1 tin2 =
    let 
      val (t1,t2) = (#token tin1,#token tin2)
    in
      if p(t1,t2) then 
        findINMonomorphisms (addPair (t1,t2) f) p (#inputs tin1) (#inputs tin2) handle Fail => Seq.empty
      else
        Seq.empty
    end

  fun findTINMatches f p tin1 [] = Seq.empty
    | findTINMatches f p tin1 (tin2::g2') =
        let 
          val rest = findTINMatches f p tin1 g2'
        in
            Seq.cons (findTINMonomorphisms f p tin1 tin2, tin2) rest handle Fail => rest
        end

  fun findMonomorphisms f p [] g2 = Seq.single f
    | findMonomorphisms f p (tin1::g1') g2 =
          let 
            fun MonomorphismsPerResult (F,tin2) = let val g2' = List.remove tin2 g2 in Seq.maps (fn f' => findMonomorphisms f' p g1' g2') F end
            val TINMatches = findTINMatches f p tin1 g2
          in 
            Seq.maps MonomorphismsPerResult TINMatches
          end

  fun tokenSpecialises T t1 t2 = (#subType T) (CSpace.typeOfToken t1,CSpace.typeOfToken t2)
  fun equivalentTokens t1 t2 = CSpace.tokensHaveSameType t1 t2

  fun tokenInSet t tks = List.exists (fn x => CSpace.sameTokens t x) tks

  fun findReificationsUpTo T f g1 g2 tks =
    findMonomorphisms f (fn (t1,t2) => tokenSpecialises T t2 t1 orelse tokenInSet t1 tks) g1 g2

  fun findLPMonomorphismsUpTo T f g1 g2 tks = 
    findMonomorphisms f (fn (t1,t2) => equivalentTokens t1 t2 orelse tokenInSet t1 tks) g1 g2

  fun tokensOfTIN tin = #token tin :: List.flatmap #inputTokens (#inputs tin)
  fun tokensOfGraph g = List.flatmap tokensOfTIN g
  fun isTotalOver f g = List.all (fn x => isSome (f x)) (tokensOfGraph g)

  (* The following actually allows extra constructor vertices to exist on g2 as long as we can inject g1 into g2 and tokens are in bijection *)
  fun findLPIsomorphismsUpTo T f g1 g2 tks = 
    Seq.filter (fn (_,f2) => isTotalOver f2 g2) (findLPMonomorphismsUpTo T f g1 g2 tks)

  fun findLooseningsUpTo T f g1 g2 tks = Seq.map invertMap (findReificationsUpTo T f g2 g1 tks)

end