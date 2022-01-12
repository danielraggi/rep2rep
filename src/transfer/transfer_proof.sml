import "core.correspondence";

signature TRANSFER_PROOF =
sig
  type corr = {name : string, sourcePattern : Pattern.pattern, targetPattern : Pattern.pattern}
  datatype tproof = Closed of Relation.relationship * corr * tproof list
                  | Open of Relation.relationship;
  val ofRelationship : Relation.relationship -> tproof;
  val dataOfCorrespondence : Correspondence.corr -> {name : string, sourcePattern : Pattern.pattern, targetPattern : Pattern.pattern}
  val ofCorrespondence : Correspondence.corr -> tproof;
  val similar : tproof -> tproof -> bool
  val applyTokenMorph : (CSpace.token -> CSpace.token option) -> tproof -> tproof
  val attachCorr : Correspondence.corr -> tproof -> tproof;
  val attachCorrAt : Correspondence.corr -> Relation.relationship -> tproof -> tproof;
  val attachCorrPulls : Correspondence.corr -> CSpace.token -> tproof -> tproof
  val dump : string -> Relation.relationship -> tproof -> tproof

  val mapRelsAndAttachCorr : (Relation.relationship -> Relation.relationship)
                              -> Correspondence.corr -> tproof -> tproof;

  val toConstruction : tproof -> Construction.construction;
end;

structure TransferProof : TRANSFER_PROOF =
struct

  type corr = {name : string, sourcePattern : Pattern.pattern, targetPattern : Pattern.pattern}
  datatype tproof = Closed of Relation.relationship * corr * tproof list
                  | Open of Relation.relationship;

  fun ofRelationship r = Open r;


  fun dataOfCorrespondence corr = {name = #name corr, sourcePattern = #sourcePattern corr,targetPattern = #targetPattern corr}

  fun ofCorrespondence corr =
    Closed (#constructRel corr, dataOfCorrespondence corr, map Open (#tokenRels corr))

  fun sameSimilarCorrs c c' = #name c = #name c' andalso
                          Pattern.same (#sourcePattern c) (#sourcePattern c') andalso
                          Pattern.similar (#targetPattern c) (#targetPattern c')

  fun similar (Closed (r,c,L)) (Closed (r',c',L')) = Relation.stronglyMatchingRelationships r r' andalso
                                                     sameSimilarCorrs c c' andalso
                                                     List.allZip similar L L'
    | similar (Open r) (Open r') = Relation.stronglyMatchingRelationships r r'
    | similar _ _ = false

  fun attachCorr corr (Closed (r,npp,L)) = Closed (r,npp, map (attachCorr corr) L)
    | attachCorr corr (Open r) =
        if Relation.sameRelationship (#constructRel corr) r
        then ofCorrespondence corr
        else Open r

  fun attachCorrAt corr r' (Closed (r,npp,L)) = Closed (r,npp, map (attachCorrAt corr r') L)
    | attachCorrAt corr r' (Open r) =
        if Relation.sameRelationship r' r
        then ofCorrespondence corr
        else Open r

  fun attachCorrPulls corr t (Closed (r,npp,L)) = Closed (r,npp, map (attachCorrPulls corr t) L)
    | attachCorrPulls corr t (Open (x,y,R)) =
      let val pullList = Correspondence.pullListOf corr
          (*val t = Pattern.constructOf (#targetPattern corr)*)
          fun applyPullItems ((R',R'',tL) :: L) =
                if Relation.same R R' andalso List.exists (CSpace.sameTokens t) y
                then map (fn t' => (x,map (fn s => if CSpace.sameTokens s t then t' else s) y,R'')) tL
                else applyPullItems L
            | applyPullItems [] = []
      in case applyPullItems pullList of
            [] => Open (x,y,R)
          | rL => Closed ((x,y,R),
                          {name = #name corr ^ "\\_pull",
                           sourcePattern = #sourcePattern corr,
                           targetPattern = #targetPattern corr},
                           map Open rL)
      end

  fun dump s g (Closed (r,npp,L)) = Closed (r,npp, map (dump s g) L)
    | dump s (x,y,R) (Open r) =
      if Relation.sameRelationship (x,y,R) r
      then Closed ((x,y,R),
                   {name = s,
                    sourcePattern = Pattern.Source (CSpace.makeToken "" ""),
                    targetPattern = Pattern.Source (CSpace.makeToken "" "")},
                   [])
      else Open r

  fun applyTokenMorph f (Closed (r,npp,L)) =
        let fun applyPartialF t = (case f t of SOME t' => t' | NONE => t)
            fun applyToRelationship (ss,ts,R) = (map applyPartialF ss, map applyPartialF ts, R)
        in Closed (applyToRelationship r, npp, map (applyTokenMorph f) L)
        end
    | applyTokenMorph f (Open r) =
        let fun applyPartialF t = (case f t of SOME t' => t' | NONE => t)
            fun applyToRelationship (ss,ts,R) = (map applyPartialF ss, map applyPartialF ts, R)
        in Open (applyToRelationship r)
        end

  fun mapRels f (Closed (r,npp,L)) = Closed (f r, npp, map (mapRels f) L)
    | mapRels f (Open r) = Open (f r)

  fun mapRelsAndAttachCorr f corr (Closed (r,npp,L)) =
        Closed (f r, npp, map (mapRelsAndAttachCorr f corr) L)
    | mapRelsAndAttachCorr f corr (Open r) =
      let val r' = f r
      in if Relation.sameRelationship r' (#constructRel corr)
         then ofCorrespondence corr
         else Open r'
      end

  fun topRel (Closed ((_,_,R),_,_)) = R
    | topRel (Open (_,_,R)) = R
  fun stringOfPair f (x,y) = "(" ^ f x ^ "," ^ f y ^ ")"
  fun stringOfTokenListPair (x,y) = stringOfPair (fn z => List.toString CSpace.stringOfToken z) (x,y)
  fun toConstruction (Closed ((x,y,R),npp,L)) =
      let fun relType X =Type.typeOfString (Relation.nameOf X)
          val Rtyp = relType R
          val t = CSpace.makeToken (stringOfTokenListPair (x,y)) Rtyp
          val ctyp = CSpace.makeCTyp (map (relType o topRel) L, Rtyp)
          val c = CSpace.makeConstructor (#name npp,ctyp)
          val cs = if null L
                   then [Construction.Source (CSpace.makeToken "" (Type.typeOfString "true"))]
                   else map toConstruction L
      in Construction.TCPair ({token = t,constructor = c}, cs)
      end
    | toConstruction (Open (x,y,R)) =
      let fun relType X =Type.typeOfString (Relation.nameOf X)
          val Rtyp = relType R
          val t = CSpace.makeToken (stringOfTokenListPair (x,y)) Rtyp
      in Construction.Source t
      end

end
