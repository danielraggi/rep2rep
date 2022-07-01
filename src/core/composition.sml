import "core.pattern";

signature COMPOSITION =
sig
  type composition;

  val composition_rpc : composition Rpc.Datatype.t;

  val dataOfComposition : composition -> {construct : CSpace.token, attachments : (Construction.construction * composition list) list};

  val size : composition -> int;

  val isPlaceholder : composition -> bool;
  val constructOfComposition : composition -> CSpace.token;
  val wellFormedComposition : CSpace.conSpecData -> composition -> bool;

  val unistructured : composition -> bool;
  val unistructurable : Type.typeSystem -> composition -> bool;
  val similar : composition -> composition -> bool;

  val initFromConstruction : Construction.construction -> composition;
  val attachConstructions : composition list -> Construction.construction list -> composition list;
  val attachConstructionAt : Construction.construction -> CSpace.token -> composition -> (bool * composition);

  val makePlaceholderComposition : CSpace.token -> composition;

  val constructionsInComposition : composition -> Construction.construction list;

  val pseudoSimilar : composition -> composition -> bool;

  val tokensOfComposition : composition -> CSpace.token FiniteSet.set;
  val tokensOfCompositions : composition list -> CSpace.token FiniteSet.set;
  val resultingConstructions : composition -> Construction.construction list;
  val pickICSfromAttachments : Construction.construction -> Construction.construction list -> Construction.construction list;

  val applyPartialMorphismToComposition : (CSpace.token -> CSpace.token option) -> composition -> composition;
end;

structure Composition : COMPOSITION =
struct

  datatype composition = Composition of {construct : CSpace.token, attachments : (Construction.construction * composition list) list};

  fun composition_rpc_ () =
      Rpc.Datatype.convert
          "Composition.composition"
          (Rpc.Datatype.tuple2
               (CSpace.token_rpc,
                List.list_rpc
                    (Rpc.Datatype.tuple2
                         (Construction.construction_rpc,
                          List.list_rpc
                              (Rpc.Datatype.recur composition_rpc_)))))
          (fn (c, a) => Composition {construct = c, attachments = a})
          (fn (Composition {construct = c, attachments = a}) => (c, a));

  val composition_rpc = composition_rpc_ ();

  fun dataOfComposition (Composition {construct, attachments}) = {construct = construct, attachments = attachments}
  fun size (Composition {attachments = (c,D::DL)::L, construct}) = size D + size (Composition {attachments = (c,DL)::L, construct=construct})
    | size (Composition {attachments = (c,[])::L, construct}) = Construction.size c + size (Composition {attachments = L, construct=construct})
    | size (Composition {attachments = [], ...}) = 0

  fun isPlaceholder (Composition {attachments,...}) = null attachments
  fun constructOfComposition (Composition {construct,...}) = construct

  fun wellFormedComposition CS (Composition {construct,attachments}) =
    let
      fun wfds [] =  true
        | wfds ((ct,Ds)::L) =
            Construction.wellFormed CS ct
            andalso CSpace.sameTokens construct (Construction.constructOf ct)
            andalso List.all (fn x => FiniteSet.exists (fn y => CSpace.sameTokens (constructOfComposition x) y) (Construction.tokensOfConstruction ct)) Ds
            andalso List.all (wellFormedComposition CS) Ds
            andalso wfds L
      val result = wfds attachments
    in result
    end

  fun subsumingAttachments T (ct,DL) (ct',DL') =
    (case (ct,ct') of
        (Construction.Source t,ct') =>
          #subType T ((CSpace.typeOfToken (Construction.constructOf ct')), (CSpace.typeOfToken t))
          (*andalso List.all (subsumingAttachments T (ct',DL')) (List.concat (map (#attachments o dataOfComposition) DL)) *)
      | (ct,Construction.Source t') =>
          #subType T ((CSpace.typeOfToken (Construction.constructOf ct)), (CSpace.typeOfToken t'))
          (*andalso List.all (subsumingAttachments T (ct,DL)) (List.concat (map (#attachments o dataOfComposition) DL'))*)
      | _ => false)

  fun unistructured (Composition {attachments = [(_,DL)], ...}) = List.all unistructured DL
    | unistructured (Composition {attachments = [], ...}) = true
    | unistructured _ = false

  fun unistructurable T (Composition {attachments = (ct,DL)::L, construct}) =
        List.all (unistructurable T) DL andalso
        List.all (subsumingAttachments T (ct,DL)) L andalso
        unistructurable T (Composition {attachments = L, construct = construct})
    | unistructurable T (Composition {attachments = [], ...}) = true

  fun similar (Composition {construct = c, attachments = A}) (Composition {construct = c', attachments = A'}) =
    let fun SA (ct,compL) (ct',compL') =
          let val (similarCts,f) = Pattern.mapUnder ct ct' CSpace.tokensHaveSameType CSpace.sameConstructors
              fun mapAndSimilar (x,y) =
                  CSpace.sameTokens (valOf (f (constructOfComposition x))) (constructOfComposition y)
                  andalso similar x y
          in similarCts andalso List.isPermutationOf mapAndSimilar compL compL' handle Option => (print "hm";false)
          end
        fun similarAttachments L L' = List.isPermutationOf (uncurry SA) L L'
    in CSpace.tokensHaveSameType c c' andalso similarAttachments A A'
    end

  fun makePlaceholderComposition t = Composition {construct = t, attachments = []}

  fun pickICSfromAttachments (Construction.Source _) [ct] = [ct]
    | pickICSfromAttachments (Construction.Reference _) [] = []
    | pickICSfromAttachments (Construction.TCPair (_,cs)) (_::cts) =
        let fun picsfa (c::L) icts = (case List.split(icts,FiniteSet.size (Construction.tokensOfConstruction c)) of
                                          (cLx,cly) => pickICSfromAttachments c cLx @ picsfa L cly)
              | picsfa [] _ = []
        in picsfa cs cts
        end
    | pickICSfromAttachments _ _ = (print"hey";raise Match)

  fun initFromConstruction ct =
    let val placeholders = map makePlaceholderComposition (FiniteSet.listOf (Construction.tokensOfConstruction ct))
    in Composition {construct = Construction.constructOf ct,
                    attachments = [(ct,placeholders)]}
    end

  (* the following function doesn't assume anything about the names of vertices in
  the construction relative to the composition. *)
  fun attachConstructionAt ct t (Composition {construct,attachments}) =
    let fun aca (ct',Ds) = (case map (attachConstructionAt ct t) Ds of L =>
                              if List.exists (fn (b,_) => b) L
                              then (true,(ct',map #2 L))
                              else (false,(ct',Ds)))
        val (b,atts) = if CSpace.sameTokens t construct
                       then (true,(ct,map makePlaceholderComposition (FiniteSet.listOf (Construction.tokensOfConstruction ct))) :: attachments)
                       else (case map aca attachments of L =>
                              if List.exists (fn (b,_) => b) L
                              then (true,map #2 L)
                              else (false,map #2 L))
    in (b,Composition {construct = construct, attachments = atts})
    end

  fun attachConstructions CC [] = CC
    | attachConstructions CC (ct::L) =
      (case map (attachConstructionAt ct (Construction.constructOf ct)) (attachConstructions CC L) of
        CCC => if List.exists (fn (b,_) => b) CCC
                then (print " \n\n attaching \n\n"; map #2 CCC)
                else (print " \n\n creating \n\n"; initFromConstruction ct :: CC))



  (* assumes composition is well formed *)
  fun tokensOfComposition (Composition {attachments,construct}) =
    let fun tokensOfAttachments ((ct,DS)::L) = FiniteSet.union (Construction.tokensOfConstruction ct)
                                                               (FiniteSet.union (tokensOfCompositions DS)
                                                                                (tokensOfAttachments L))
          | tokensOfAttachments [] = FiniteSet.empty
    in if FiniteSet.isEmpty attachments then FiniteSet.ofList [construct] else tokensOfAttachments attachments
    end
  and tokensOfCompositions [] = FiniteSet.empty
    | tokensOfCompositions (c::L) = FiniteSet.union (tokensOfComposition c) (tokensOfCompositions L)

  fun constructionsInComposition (Composition {attachments,...}) =
    let fun coc ((ct,comps)::A) = ct :: (List.maps constructionsInComposition comps) @ coc A
          | coc [] = []
    in coc attachments
    end

  exception BadComposition

  fun resultingConstructions (Composition {construct,attachments}) =
    let fun rc ((ct,comps)::A) = let val rr = List.listProduct (map resultingConstructions comps)
                                     val VS = Construction.tokensOfConstruction ct
                                     fun f [] [] = [ct]
                                       | f (t::tL) (c::cL) =
                                            if Construction.same (Construction.Source t) c then (f tL cL) else
                                              (List.maps (fn x => Construction.attachConstructionAtToken x t c) (f tL cL))
                                       | f _ _ = raise (print "Bad composition!\n";BadComposition)
                                     fun g L = f VS L
                                 in ((List.maps g rr)) @ rc A
                                 end
          | rc [] = []
        fun removeRedundant (ct::cts) =
              if List.exists (fn x => Construction.isGenerator ct x) cts then removeRedundant cts
              else ct :: removeRedundant (List.filter (fn x => not (Construction.isGenerator x ct)) cts)
          | removeRedundant [] = []
    in if null attachments then [Construction.Source construct] else removeRedundant (rc attachments)
    end

  fun pseudoSimilar C C' =
    List.isPermutationOf (uncurry Pattern.similar) (resultingConstructions C) (resultingConstructions C')

  fun leavesOfComposition (Composition {attachments = (ct,C::CL)::L, construct}) =
        Construction.leavesOfConstruction ct :: ((leavesOfComposition C)
          @ (leavesOfComposition (Composition {attachments = L, construct = construct})))
    | leavesOfComposition (Composition {attachments = (ct,[])::L, construct}) =
        Construction.leavesOfConstruction ct :: (leavesOfComposition (Composition {attachments = L, construct = construct}))
    | leavesOfComposition (Composition {attachments = [], ...}) = []

  fun applyPartialMorphismToComposition f (Composition {construct,attachments}) =
    let fun applyToAttachment (ct,C) = ((Pattern.applyPartialMorphism f ct, map (applyPartialMorphismToComposition f) C))
    in case f construct of
          SOME t => Composition {construct = t, attachments = map applyToAttachment attachments}
        | NONE => Composition {construct = construct, attachments = map applyToAttachment attachments}
    end
end;
