import "core.transferSchema";

signature TRANSFER_PROOF =
sig
  type tApp = {name : string, sourcePattern : Pattern.pattern, targetPattern : Pattern.pattern}
  datatype tproof = Closed of Relation.relationship * tApp * tproof list
                  | Open of Relation.relationship;
  val ofRelationship : Relation.relationship -> tproof;
  val dataOfTransferSchema : TransferSchema.tSch -> {name : string, sourcePattern : Pattern.pattern, targetPattern : Pattern.pattern}
  val ofTransferSchema : TransferSchema.tSch -> tproof;
  val similar : tproof -> tproof -> bool
  val applyTokenMorph : (CSpace.token -> CSpace.token option) -> tproof -> tproof
  val attachTSchema : TransferSchema.tSch -> tproof -> tproof;
  val attachTSchemaAt : TransferSchema.tSch -> Relation.relationship -> tproof -> tproof;
  val attachTSchemaPulls : TransferSchema.tSch -> CSpace.token -> tproof -> tproof
  val dump : string -> Relation.relationship -> tproof -> tproof

  val mapRelsAndAttachTSchema : (Relation.relationship -> Relation.relationship)
                              -> TransferSchema.tSch -> tproof -> tproof;

  val toConstruction : tproof -> Construction.construction;
end;

structure TransferProof : TRANSFER_PROOF =
struct

  type tApp = {name : string, sourcePattern : Pattern.pattern, targetPattern : Pattern.pattern}
  datatype tproof = Closed of Relation.relationship * tApp * tproof list
                  | Open of Relation.relationship;

  fun ofRelationship r = Open r;


  fun dataOfTransferSchema tApp = {name = #name tApp, sourcePattern = #sourcePattern tApp,targetPattern = #targetPattern tApp}

  fun ofTransferSchema tApp =
    Closed (#consequent tApp, dataOfTransferSchema tApp, map Open (#antecedent tApp))

  fun sameSimilarTSchemas c c' = #name c = #name c' andalso
                          Pattern.same (#sourcePattern c) (#sourcePattern c') andalso
                          Pattern.similar (#targetPattern c) (#targetPattern c')

  fun similar (Closed (r,c,L)) (Closed (r',c',L')) = Relation.stronglyMatchingRelationships r r' andalso
                                                     sameSimilarTSchemas c c' andalso
                                                     List.allZip similar L L'
    | similar (Open r) (Open r') = Relation.stronglyMatchingRelationships r r'
    | similar _ _ = false

  fun attachTSchema tApp (Closed (r,npp,L)) = Closed (r,npp, map (attachTSchema tApp) L)
    | attachTSchema tApp (Open r) =
        if Relation.sameRelationship (#consequent tApp) r
        then ofTransferSchema tApp
        else Open r

  fun attachTSchemaAt tApp r' (Closed (r,npp,L)) = Closed (r,npp, map (attachTSchemaAt tApp r') L)
    | attachTSchemaAt tApp r' (Open r) =
        if Relation.sameRelationship r' r
        then ofTransferSchema tApp
        else Open r

  fun attachTSchemaPulls tApp t (Closed (r,npp,L)) = Closed (r,npp, map (attachTSchemaPulls tApp t) L)
    | attachTSchemaPulls tApp t (Open (x,y,R)) =
      let val pullList = TransferSchema.pullListOf tApp
          (*val t = Pattern.constructOf (#targetPattern tApp)*)
          fun applyPullItems ((R',R'',tL) :: L) =
                if Relation.same R R' andalso List.exists (CSpace.sameTokens t) y
                then map (fn t' => (x,map (fn s => if CSpace.sameTokens s t then t' else s) y,R'')) tL
                else applyPullItems L
            | applyPullItems [] = []
      in case applyPullItems pullList of
            [] => Open (x,y,R)
          | rL => Closed ((x,y,R),
                          {name = #name tApp ^ "\\_pull",
                           sourcePattern = #sourcePattern tApp,
                           targetPattern = #targetPattern tApp},
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

  fun mapRelsAndAttachTSchema f tApp (Closed (r,npp,L)) =
        Closed (f r, npp, map (mapRelsAndAttachTSchema f tApp) L)
    | mapRelsAndAttachTSchema f tApp (Open r) =
      let val r' = f r
      in if Relation.sameRelationship r' (#consequent tApp)
         then ofTransferSchema tApp
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
