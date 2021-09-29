import "capullo.correspondence";

signature TRANSFER_PROOF =
sig
  datatype tproof = Closed of Relation.relationship * string * tproof list
                  | Open of Relation.relationship;
  val ofRelationship : Relation.relationship -> tproof;
  val ofCorrespondence : Correspondence.corr -> tproof;
  val applyTokenMorph : (CSpace.token -> CSpace.token option) -> tproof -> tproof
  val attachCorr : Correspondence.corr -> tproof -> tproof;
  val attachCorrAt : Correspondence.corr -> Relation.relationship -> tproof -> tproof;
  val mapRelsAndAttachCorr : (Relation.relationship -> Relation.relationship)
                              -> Correspondence.corr -> tproof -> tproof;

  val toConstruction : tproof -> Construction.construction;
end;

structure TransferProof : TRANSFER_PROOF =
struct

  datatype tproof = Closed of Relation.relationship * string * tproof list
                  | Open of Relation.relationship;

  fun ofRelationship r = Open r;

  fun ofCorrespondence corr =
    Closed (#constructRel corr, #name corr, map Open (#tokenRels corr))

  fun attachCorr corr (Closed (r,n,L)) = Closed (r,n, map (attachCorr corr) L)
    | attachCorr corr (Open r) =
        if Relation.sameRelationship (#constructRel corr) r
        then ofCorrespondence corr
        else Open r

  fun attachCorrAt corr r' (Closed (r,n,L)) = Closed (r,n, map (attachCorrAt corr r') L)
    | attachCorrAt corr r' (Open r) =
        if Relation.sameRelationship r' r
        then ofCorrespondence corr
        else Open r


  fun applyTokenMorph f (Closed (r,n,L)) =
        let fun applyPartialF t = (case f t of SOME t' => t' | NONE => t)
            fun applyToRelationship (ss,ts,R) = (map applyPartialF ss, map applyPartialF ts, R)
        in Closed (applyToRelationship r, n, map (applyTokenMorph f) L)
        end
    | applyTokenMorph f (Open r) =
        let fun applyPartialF t = (case f t of SOME t' => t' | NONE => t)
            fun applyToRelationship (ss,ts,R) = (map applyPartialF ss, map applyPartialF ts, R)
        in Open (applyToRelationship r)
        end

  fun mapRels f (Closed (r,n,L)) = Closed (f r, n, map (mapRels f) L)
    | mapRels f (Open r) = Open (f r)

  fun mapRelsAndAttachCorr f corr (Closed (r,n,L)) =
        Closed (f r, n, map (mapRelsAndAttachCorr f corr) L)
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
  fun toConstruction (Closed ((x,y,R),n,L)) =
      let fun relType X =Type.typeOfString (Relation.nameOf X)
          val Rtyp = relType R
          val t = CSpace.makeToken (stringOfTokenListPair (x,y)) Rtyp
          val ctyp = CSpace.makeCTyp (map (relType o topRel) L, Rtyp)
          val c = CSpace.makeConstructor (n,ctyp)
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
