import "pattern";

signature COMPOSITION =
sig
  include PATTERN;
  type composition;

  val dataOfComposition : composition -> {construct : CSpace.token, attachments : (construction * composition list) list};

  val size : composition -> int;

  val isPlaceholder : composition -> bool;
  val constructOfComposition : composition -> CSpace.token;
  val wellFormedComposition : TypeSystem.typeSystem -> composition -> bool;

  val initFromConstruction : construction -> composition;
  val attachConstructionAt : composition -> construction -> CSpace.token -> composition;

  val makePlaceholderComposition : CSpace.token -> composition;
(*
  val isExactDecompositionOf : composition -> construction -> bool;
  val isPatternDecompositionOf : composition -> construction -> bool;
*)
  val constructionsInComposition : composition -> construction list;
  val tokensOfComposition : composition -> CSpace.token list;
  val resultingConstructions : composition -> construction list;
  val firstResultingConstruction : composition -> construction;

end;

structure Composition : COMPOSITION =
struct
  open Pattern
  datatype composition = Composition of {construct : CSpace.token, attachments : (construction * composition list) list};

  fun dataOfComposition (Composition {construct, attachments}) = {construct = construct, attachments = attachments}
  fun size (Composition {attachments = (c,D::DL)::L, construct}) = size D + size (Composition {attachments = (c,DL)::L, construct=construct})
    | size (Composition {attachments = (_,[])::L, construct}) = 1+size (Composition {attachments = L, construct=construct})
    | size (Composition {attachments = [], ...}) = 1

  fun isPlaceholder (Composition {attachments,...}) = null attachments
  fun constructOfComposition (Composition {construct,...}) = construct

  fun wellFormedComposition T (Composition {construct,attachments}) =
    let
      fun wfds ((ct,Ds)::L) =
            Construction.wellFormed T ct
            andalso List.allZip CSpace.sameTokens (foundationSequence ct) (map constructOfComposition Ds)
            andalso List.all (wellFormedComposition T) Ds
            andalso wfds L
        | wfds [] =  true
      val constructsOfAttachments = map (constructOf o #1) attachments
    in
      List.all (CSpace.sameTokens construct) constructsOfAttachments andalso wfds attachments
    end

  fun makePlaceholderComposition t = Composition {construct = t, attachments = []}

  fun initFromConstruction ct =
    Composition {construct = constructOf ct,
                   attachments = [(ct,map makePlaceholderComposition (foundationSequence ct))]}

  (* the following function doesn't assume anything about the names of vertices in
  the construction relative to the composition. *)
  fun attachConstructionAt (Composition {construct,attachments}) ct t =
    let fun aca (ct',Ds) = (ct',map (fn x => attachConstructionAt x ct t) Ds)
    in if CSpace.sameTokens t construct
       then Composition {construct = t, attachments = (ct,map makePlaceholderComposition (foundationSequence ct)) :: attachments}
       else Composition {construct = construct, attachments = map aca attachments}
    end

  fun tokensOfComposition (Composition {attachments,...}) =
    let fun tokensOfAttachments ((ct,DS)::L) = tokensOfConstruction ct @ (List.maps tokensOfComposition DS) @ tokensOfAttachments L
          | tokensOfAttachments [] = []
    in tokensOfAttachments attachments
    end

  fun constructionsInComposition (Composition {attachments,...}) =
    let fun coc ((ct,comps)::A) = ct :: (List.maps constructionsInComposition comps) @ coc A
          | coc [] = []
    in coc attachments
    end

  fun resultingConstructions (Composition {construct,attachments}) =
    let fun rc ((ct,comps)::A) = let val rr = List.listProduct (map resultingConstructions comps)
                                     fun f x = Construction.unsplit(ct,x)
                                 in map f rr @ rc A
                                 end
          | rc [] = []
    in if null attachments then [Source construct] else rc attachments
    end

  fun firstResultingConstruction (Composition {construct,attachments}) =
    case attachments of
      [] => Source construct
    | ((ct,comps)::_) => Construction.unsplit (ct, map firstResultingConstruction comps)

end;
