import "pattern"

signature COMPOSITION =
sig
  include PATTERN;
  type composition;

  val isPlaceholder : composition -> bool;
  val constructOfComposition : composition -> CSpace.token;
  val wellFormedComposition : composition -> bool;

  val initFromConstruction : construction -> composition;
  val attachConstructionAt : composition -> construction -> CSpace.token -> composition;
  val makePlaceholderComposition : CSpace.token -> composition;
(*
  val isExactDecompositionOf : composition -> construction -> bool;
  val isPatternDecompositionOf : composition -> construction -> bool;
*)
  val tokensOfComposition : composition -> CSpace.token list;

end

structure Composition : COMPOSITION =
struct
  open Pattern
  datatype composition = Composition of {construct : CSpace.token, attachments : (construction * composition list) list};

  fun dataOfComposition (Composition {construct, attachments}) = {construct = construct, attachments = attachments}

  fun isPlaceholder (Composition {attachments,...}) = null attachments
  fun constructOfComposition (Composition {construct,...}) = construct

  fun wellFormedComposition (Composition {construct,attachments}) =
    let
      fun wfds ((ct,Ds)::L) =
            Construction.wellFormed ct
            andalso allZip CSpace.sameTokens (foundationSequence ct) (map constructOfComposition Ds)
            andalso List.all wellFormedComposition Ds
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
    let fun tokensOfAttachments ((ct,DS)::L) = tokensOfConstruction ct @ (maps tokensOfComposition DS) @ tokensOfAttachments L
          | tokensOfAttachments [] = []
    in tokensOfAttachments attachments
    end

end