import "pattern"

signature DECOMPOSITION =
sig
  include Pattern;
  type decomposition;

  val isPlaceholder : decomposition -> bool;
  val constructOfDecomposition : decomposition -> CSpace.token;
  val wellFormedDecomposition : decomposition -> bool;

  val initFromConstruction : construction -> (construction * decomposition list) list;
  val attachConstructionAt : decomposition -> construction -> CSpace.token -> decomposition;

  val isExactDecompositionOf : decomposition -> construction -> bool;
  val isPatternDecompositionOf : decomposition -> construction -> bool;

  val tokensOfDecomposition : decomposition -> CSpace.token list;

end

structure Decomposition =
struct
  open Pattern
  datatype decomposition = Decomposition of {construct : CSpace.token, attachments : (construction * decomposition list) list};

  fun dataOfDecomposition (Decomposition {construct, attachments}) = {construct = construct, attachments = attachments}

  fun isPlaceholder (Decomposition {attachments,...}) = null attachments
  fun constructOfDecomposition (Decomposition {construct,...}) = construct

  fun wellFormedDecomposition (Decomposition {construct,attachments}) =
    let
      fun wfds ((ct,Ds)::L) =
            ConstructionTerm.wellFormed ct
            andalso allZip sameTokens (foundationSequence ct) (map constructOfDecomposition Ds)
            andalso List.all wellFormedDecomposition Ds
            andalso wfds L
        | wfds [] =  true
      val constructsOfAttachments = map (constructOf o #1) attachments
    in
      List.all (CSpace.sameTokens construct) constructsOfAttachments andalso wfd attachments
    end

  fun makePlaceholderDecomposition t = Decomposition {construct = t, attachments = []}

  fun initFromConstruction ct =
    Decomposition {construct = constructOf ct,
                   attachments = [(ct,map makePlaceholderDecomposition (foundationSequence ct))]}

  (* the following function doesn't assume anything about the names of vertices in
  the construction relative to the decomposition. *)
  fun attachConstructionAt (Decomposition {construct,attachments}) ct t =
    let fun aca (ct',Ds) = (ct',map (fn x => attachConstructionAt x ct t) Ds)
    in if CSpace.sameTokens t construct
       then Decomposition {construct = t, attachments = (ct,map makePlaceholderDecomposition (foundationSequence ct)) :: attachments}
       else Decomposition {construct = construct, attachments = map aca attachments}
    end

  fun tokensOfDecomposition (Decomposition {attachments,...}) =
    let fun tokensOfAttachments ((ct,DS)::L) = tokensOfConstruction ct @ (maps tokensOfDecomposition DS) @ tokensOfAttachments L
          | tokensOfAttachments [] = []
    in tokensOfAttachments attachments
    end

end
