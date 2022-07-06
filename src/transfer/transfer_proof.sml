import "core.interCSpace";

signature TRANSFER_PROOF =
sig
  type tApp = {name : string, source : Pattern.pattern, target : Pattern.pattern}
  datatype tproof = Closed of Pattern.pattern * tApp * tproof list
                  | Open of Pattern.pattern;
  val ofPattern : Pattern.pattern -> tproof;
  val dataOfTransferSchema : InterCSpace.tSchema -> {name : string, source : Pattern.pattern, target : Pattern.pattern}
  val ofTransferSchema : InterCSpace.tSchema -> tproof;
  val similar : tproof -> tproof -> bool
  val applyPartialMorphism : (CSpace.token -> CSpace.token option) -> tproof -> tproof
  val attachTSchema : InterCSpace.tSchema -> tproof -> tproof;
  val attachTSchemaAt : InterCSpace.tSchema -> Pattern.pattern -> tproof -> tproof;
  val attachISchemaAt : Knowledge.iSchema -> Pattern.pattern -> tproof -> tproof;
  (*val attachTSchemaPulls : InterCSpace.tSchema -> CSpace.token -> tproof -> tproof*)
  val dump : string -> Pattern.pattern -> tproof -> tproof

(*)
  val mapRelsAndAttachTSchema : (Relation.relationship -> Relation.relationship)
                              -> InterCSpace.tSchema -> tproof -> tproof;*)

  val toConstruction : tproof -> Construction.construction;
end;

structure TransferProof : TRANSFER_PROOF =
struct

  type tApp = {name : string, source : Pattern.pattern, target : Pattern.pattern}
  datatype tproof = Closed of Pattern.pattern * tApp * tproof list
                  | Open of Pattern.pattern;

  fun ofPattern r = Open r;


  fun dataOfTransferSchema tApp = {name = #name tApp, source = #source tApp,target = #target tApp}

  fun ofTransferSchema tApp =
    Closed (#consequent tApp, dataOfTransferSchema tApp, map Open (#antecedent tApp))
  fun ofInferenceSchema tApp =
    Closed (#consequent tApp, {name = #name tApp,source = #context tApp,target = #context tApp}, map Open (#antecedent tApp))

  fun sameSimilarTSchemas c c' = #name c = #name c' andalso
                          Pattern.same (#source c) (#source c') andalso
                          Pattern.similar (#target c) (#target c')

  fun similar (Closed (r,c,L)) (Closed (r',c',L')) = Pattern.similar r r' andalso
                                                     sameSimilarTSchemas c c' andalso
                                                     List.allZip similar L L'
    | similar (Open r) (Open r') = Pattern.similar r r'
    | similar _ _ = false

  fun attachTSchema tApp (Closed (r,npp,L)) = Closed (r,npp, map (attachTSchema tApp) L)
    | attachTSchema tApp (Open r) =
        if Construction.same (#consequent tApp) r
        then ofTransferSchema tApp
        else Open r

  fun attachTSchemaAt tApp r' (Closed (r,npp,L)) = Closed (r,npp, map (attachTSchemaAt tApp r') L)
    | attachTSchemaAt tApp r' (Open r) =
        if Construction.same r' r
        then ofTransferSchema tApp
        else Open r

  fun attachISchemaAt tApp r' (Closed (r,npp,L)) = Closed (r,npp, map (attachISchemaAt tApp r') L)
    | attachISchemaAt tApp r' (Open r) =
        if Construction.same r' r
        then ofInferenceSchema tApp
        else Open r

(*)
  fun attachTSchemaPulls tApp t (Closed (r,npp,L)) = Closed (r,npp, map (attachTSchemaPulls tApp t) L)
    | attachTSchemaPulls tApp t (Open (x,y,R)) =
      let val pullList = InterCSpace.pullListOf tApp
          (*val t = Pattern.constructOf (#target tApp)*)
          fun applyPullItems ((R',R'',tL) :: L) =
                if Relation.same R R' andalso List.exists (CSpace.sameTokens t) y
                then map (fn t' => (x,map (fn s => if CSpace.sameTokens s t then t' else s) y,R'')) tL
                else applyPullItems L
            | applyPullItems [] = []
      in case applyPullItems pullList of
            [] => Open (x,y,R)
          | rL => Closed ((x,y,R),
                          {name = #name tApp ^ "\\_pull",
                           source = #source tApp,
                           target = #target tApp},
                           map Open rL)
      end
*)
  fun dump s g (Closed (r,npp,L)) = Closed (r,npp, map (dump s g) L)
    | dump s r' (Open r) =
      if Pattern.similar r' r
      then Closed (r',
                   {name = s,
                    source = Pattern.Source (CSpace.makeToken "" ""),
                    target = Pattern.Source (CSpace.makeToken "" "")},
                   [])
      else Open r

  fun applyPartialMorphism f (Closed (r,npp,L)) =
        Closed (Pattern.applyPartialMorphism f r, npp, map (applyPartialMorphism f) L)
    | applyPartialMorphism f (Open r) =
        Open (Pattern.applyPartialMorphism f r)

  fun mapRels f (Closed (r,npp,L)) = Closed (f r, npp, map (mapRels f) L)
    | mapRels f (Open r) = Open (f r)

(*)
  fun mapRelsAndAttachTSchema f tApp (Closed (r,npp,L)) =
        Closed (f r, npp, map (mapRelsAndAttachTSchema f tApp) L)
    | mapRelsAndAttachTSchema f tApp (Open r) =
      let val r' = f r
      in if Relation.sameRelationship r' (#consequent tApp)
         then ofTransferSchema tApp
         else Open r'
      end*)

  fun nodeName (Closed (r,_,_)) = Construction.toString r
    | nodeName (Open r) = Construction.toString r

  fun toConstruction (Closed (r,npp,L)) =
      let val Rtyp = Construction.toString r
          val t = CSpace.makeToken "" Rtyp
          val ctyp = CSpace.makeCTyp (map nodeName L, Rtyp)
          val c = CSpace.makeConstructor (#name npp,ctyp)
          val cs = if null L
                   then [Construction.Source (CSpace.makeToken "" (Type.fromString "true"))]
                   else map toConstruction L
      in Construction.TCPair ({token = t,constructor = c}, cs)
      end
    | toConstruction (Open r) =
      let val Rtyp = Construction.toString r
          val t = CSpace.makeToken "" Rtyp
      in Construction.Source t
      end

end
