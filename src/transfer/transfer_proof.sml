import "core.interCSpace";

signature TRANSFER_PROOF =
sig
  type tApp = {name : string, source : Pattern.pattern, target : Pattern.pattern}
  datatype tproof = Closed of Pattern.pattern * tApp * tproof list
                  | Open of Pattern.pattern;
  val ofPattern : Pattern.pattern -> tproof;
  val dataOfTransferSchema : InterCSpace.tSchemaData -> {name : string, source : Pattern.pattern, target : Pattern.pattern}
  val ofTransferSchema : InterCSpace.tSchemaData -> tproof;
  val similar : tproof -> tproof -> bool
  val applyPartialMorphism : (CSpace.token -> CSpace.token option) -> tproof -> tproof
  val attachTSchema : InterCSpace.tSchemaData -> tproof -> tproof;
  val attachTSchemaAt : InterCSpace.tSchemaData -> Pattern.pattern -> tproof -> tproof;
  val attachISchemaAt : Knowledge.iSchemaData -> Pattern.pattern -> tproof -> tproof;
  val dump : string -> Pattern.pattern -> tproof -> tproof

  val toConstruction : tproof -> Construction.construction;
end;

structure TransferProof : TRANSFER_PROOF =
struct

  type tApp = {name : string, source : Pattern.pattern, target : Pattern.pattern}
  datatype tproof = Closed of Pattern.pattern * tApp * tproof list
                  | Open of Pattern.pattern;

  fun ofPattern r = Open r;


  fun dataOfTransferSchema tSchemaData =
    {name = #name tSchemaData,
     source = #source (#tSchema tSchemaData),
     target = #target (#tSchema tSchemaData)}

  fun ofTransferSchema tSchemaData =
    let val {tSchema,...} = tSchemaData
    in Closed (#consequent tSchema, dataOfTransferSchema tSchemaData, map Open (#antecedent tSchema))
    end

  fun ofInferenceSchema iSchemaData =
    let val {name,iSchema,...} = iSchemaData
        val data = {name = name, source = #context iSchema, target = #context iSchema}
    in Closed (#consequent iSchema, data, map Open (#antecedent iSchema))
    end

  fun sameSimilarTSchemas c c' = #name c = #name c' andalso
                          Pattern.same (#source c) (#source c') andalso
                          #3 (Pattern.similar (#target c) (#target c'))

  fun similar (Closed (r,c,L)) (Closed (r',c',L')) = #3 (Pattern.similar r r') andalso
                                                     sameSimilarTSchemas c c' andalso
                                                     List.allZip similar L L'
    | similar (Open r) (Open r') = #3 (Pattern.similar r r')
    | similar _ _ = false

  fun attachTSchema tApp (Closed (r,npp,L)) = Closed (r,npp, map (attachTSchema tApp) L)
    | attachTSchema tApp (Open r) =
        if Construction.same (#consequent (#tSchema tApp)) r
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

  fun dump s g (Closed (r,npp,L)) = Closed (r,npp, map (dump s g) L)
    | dump s r' (Open r) =
      if #3 (Pattern.similar r' r)
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
