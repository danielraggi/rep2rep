import "pattern"

signature DECOMPOSITION =
sig
  include Pattern;
  datatype decomposition = Genuine of (construction * decomposition list)
                         | Placeholder of CSpace.token;

  val isPlaceholder : decomposition -> bool;
  val constructOfDecomposition : decomposition -> CSpace.token;
  val wellFormedDecomposition : decomposition -> bool;

  val initFromConstruction : construction -> decomposition;
  val attachConstructionAt : decomposition -> construction -> CSpace.token -> decomposition;

  val isExactDecompositionOf : decomposition -> construction -> bool;
  val isPatternDecompositionOf : decomposition -> construction -> bool;

end

structure Decomposition =
struct
  open Pattern
  datatype decomposition = Genuine of construction * decomposition list
                         | Placeholder of CSpace.token;

  fun isPlaceholder (Placeholder _) = true | isPlaceholder _ => false
  fun constructOfDecomposition (Genuine (ct,_)) = constructOf ct | constructOfDecomposition (Placeholder t) = t

  (* Note that the following function does not check that the constructions themselves
     are well formed. *)
  fun wellFormedDecomposition (Genuine (ct,Ds)) =
        allZip sameTokens (foundationSequence ct) (map constructOfDecomposition Ds)
        andalso List.all wellFormedDecomposition Ds
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

  fun initFromConstruction ct = Genuine (ct, map Placeholder (foundationSequence ct))
  fun attachConstructionAt (Placeholder t') ct t = if CSpace.sameTokens t t' then initFromConstruction (renameConstruct ct t') else Placeholder t'
    | attachConstructionAt (Genuine (ct,Ds)) ct t = Genuine (ct, map (fn x => attachConstructionAt x ct t) Ds)

end
