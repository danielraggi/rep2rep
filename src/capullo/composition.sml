import "capullo.pattern";

signature COMPOSITION =
sig
  include PATTERN;
  type composition;

  val dataOfComposition : composition -> {construct : CSpace.token, attachments : (construction * composition list) list};

  val size : composition -> int;

  val isPlaceholder : composition -> bool;
  val constructOfComposition : composition -> CSpace.token;
  val wellFormedComposition : Type.typeSystem -> composition -> bool;

  val initFromConstruction : construction -> composition;
  val attachConstructionAt : composition -> construction -> CSpace.token -> composition;

  val makePlaceholderComposition : CSpace.token -> composition;

  val constructionsInComposition : composition -> construction list;
  val tokensOfComposition : composition -> CSpace.token list;
  val resultingConstructions : composition -> construction list;
  val pickICSfromAttachments : construction -> construction list -> construction list;

  val applyPartialMorphismToComposition : (CSpace.token -> CSpace.token option) -> composition -> composition;
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


  fun pickICSfromAttachments (Source _) [ct] = [ct]
    | pickICSfromAttachments (Loop _) [] = []
    | pickICSfromAttachments (TCPair (_,cs)) (_::cts) =
        let fun picsfa (c::L) icts = (case List.split(icts,length (fullTokenSequence c)) of
                                          (cLx,cly) => pickICSfromAttachments c cLx @ picsfa L cly)
              | picsfa [] _ = []
        in picsfa cs cts
        end
    | pickICSfromAttachments _ _ = raise Match

  fun initFromConstruction ct =
    let val placeholders = map makePlaceholderComposition (fullTokenSequence ct)
    in Composition {construct = constructOf ct,
                    attachments = [(ct,placeholders)]}
    end

  (* the following function doesn't assume anything about the names of vertices in
  the construction relative to the composition. *)
  fun attachConstructionAt (Composition {construct,attachments}) ct t =
    let fun aca (ct',Ds) = (ct',map (fn x => attachConstructionAt x ct t) Ds)
    in if CSpace.sameTokens t construct
       then Composition {construct = t, attachments = (ct,map makePlaceholderComposition (fullTokenSequence ct)) :: attachments}
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

  exception BadComposition

  fun resultingConstructions (Composition {construct,attachments}) =
    let fun rc ((ct,comps)::A) = let val rr = List.listProduct (map resultingConstructions comps)
                                     val VS = fullTokenSequence ct
                                     fun f [] [] = [ct]
                                       | f (t::tL) (c::cL) =
                                            if Construction.same (Source t) c then (f tL cL) else
                                              (List.maps (fn x => attachConstructionAtToken x t c) (f tL cL))
                                       | f _ _ = raise (print "Bad composition!\n";BadComposition)
                                     fun g L = f VS L
                                 in ((List.maps g rr)) @ rc A
                                 end
          | rc [] = []
        fun removeRedundant (ct::cts) =
              if List.exists (fn x => subConstruction ct x) cts then removeRedundant cts
              else ct :: removeRedundant (List.filter (fn x => not (subConstruction x ct)) cts)
          | removeRedundant [] = []
    in if null attachments then [Source construct] else removeRedundant (rc attachments)
    end

  fun applyPartialMorphismToComposition f (Composition {construct,attachments}) =
    let fun applyToAttachment (ct,C) = ((applyPartialMorphism f ct, map (applyPartialMorphismToComposition f) C))
    in case f construct of
          SOME t => Composition {construct = t, attachments = map applyToAttachment attachments}
        | NONE => Composition {construct = construct, attachments = map applyToAttachment attachments}
    end
end;
