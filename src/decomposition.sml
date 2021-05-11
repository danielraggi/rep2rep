import "pattern"

signature DECOMPOSITION =
sig
  include Pattern;
  datatype decomposition = Genuine of (construction * decomposition list) list
                         | Placeholder of CSpace.token;

  val isPlaceholder : decomposition -> bool;
  val constructOfDecomposition : decomposition -> CSpace.token;
  val wellFormedDecomposition : decomposition -> bool;

  val initFromConstruction : construction -> (construction * decomposition list) list;
  val attachConstructionAt : decomposition -> construction -> CSpace.token -> decomposition;

  val isExactDecompositionOf : decomposition -> construction -> bool;
  val isPatternDecompositionOf : decomposition -> construction -> bool;

end

structure Decomposition =
struct
  open Pattern
  datatype decomposition = Genuine of (construction * decomposition list) list
                         | Placeholder of CSpace.token;

  fun isPlaceholder (Placeholder _) = true | isPlaceholder _ => false
  fun constructsOfDecomposition (Genuine ((ct,_)::L)) = constructOf ct :: constructsOfDecomposition (Genuine L)
    | constructsOfDecomposition (Placeholder t) = [t]
  fun quickConstructOfDecomposition (Genuine ((ct,_)::L)) = constructOf ct
    | quickConstructOfDecomposition (Placeholder t) = [t]

  (* Note that the following function does not check that the constructions themselves
     are well formed. *)
  fun wellFormedDecomposition (Genuine L) =
        let
          fun wfds ((ct,Ds)::L') =
                andalso allZip sameTokens (foundationSequence ct) (maps constructsOfDecomposition Ds)
                andalso List.all wellFormedDecomposition Ds
                andalso wfds L'
            | wfds [] =  true
          fun allSameTokens (t1::t2::L) = CSpace.sameTokens t1 t2 andalso allSameTokens (t2::L)
            | allSameTokens _ = true
        in
          if null L then false
          else allSameTokens (constructsOfDecomposition (Genuine L)) andalso wfd L
        end
    | wellFormedDecomposition (Placeholder _) = true

  exception BadConstruction
  fun renameConstruct ct t' =
    let fun rc originalConstruct (Source t)  = Source t
          | rc originalConstruct (Loop t) = if CSpace.sameTokens t originalConstruct then Loop t' else Loop t
          | rc originalConstruct (Construct (ut, cs)) = Construct (ut, map (rc originalConstruct) cs)
    in case ct of Source _ => Source t'
                | Loop _ => raise BadConstruction
                | Construct ({token = t,configurator = u}, cs) => Construct ({token = t',configurator = u}, map (rc t) cs)
    end

  fun initFromConstruction ct = [(ct, map Placeholder (foundationSequence ct))]

  (* the following function doesn't assume anything about the names of vertices in
  the construction relative to the decomposition, except for the construct of the
  thing being attached, which will be renamed to the token to which it is attached *)
  fun attachConstructionAt (Placeholder t') ct t =
        if CSpace.sameTokens t t'
        then Genuine (initFromConstruction (renameConstruct ct t))
        else Placeholder t'
    | attachConstructionAt (Genuine L) ct t =
        if CSpace.sameTokens (quickConstructOfDecomposition (Genuine L)) t
        then Genuine ((initFromConstruction (renameConstruct ct t)) @ L)
        else let fun aca (ct',Ds) = (ct',map (fn x => attachConstructionAt x ct t) Ds)
             in Genuine (map aca L)
             end

end
