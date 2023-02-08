import "core.pattern";

signature INTERCSPACE =
sig
  type interConSpec = {source : CSpace.conSpecData, target : CSpace.conSpecData, inter : CSpace.conSpecData}
  type tSchema = {source : Pattern.construction,
                  target : Pattern.construction,
                  antecedent : Pattern.construction list,
                  consequent : Pattern.construction};
  type tSchemaData = {name : string,
                      sourceConSpecN : string,
                      targetConSpecN : string,
                      interConSpecN : string,
                      strength : real,
                      tSchema : tSchema}


  val tSchema_rpc : tSchema Rpc.Datatype.t;
  val tSchemaData_rpc: tSchemaData Rpc.Datatype.t;

  val wellFormedTransferSchema : interConSpec -> tSchema -> bool;
  val nameOf : tSchemaData -> string;

  val declareTransferSchema : {source : Pattern.construction,
                               target : Pattern.construction,
                               antecedent : Pattern.construction list,
                               consequent : Pattern.construction} -> tSchema;

  val inverse : tSchema -> tSchema;
  val inverseData : tSchemaData -> tSchemaData;
end;

structure InterCSpace : INTERCSPACE =
struct
  type interConSpec = {source : CSpace.conSpecData, target : CSpace.conSpecData, inter : CSpace.conSpecData}
  type tSchema = {source : Pattern.construction,
                   target : Pattern.construction,
                   antecedent : Pattern.construction list,
                   consequent : Pattern.construction};
  type tSchemaData = {name : string,
                      sourceConSpecN : string,
                      targetConSpecN : string,
                      interConSpecN : string,
                      strength : real,
                      tSchema : tSchema}

  val tSchema_rpc = Rpc.Datatype.convert
                     "TransferSchema.tSchema"
                     (Rpc.Datatype.tuple4
                          (Pattern.construction_rpc,
                           Pattern.construction_rpc,
                           List.list_rpc Pattern.construction_rpc,
                           Pattern.construction_rpc))
                     (fn (s, t, rs, r) => {source = s,
                                            target = t,
                                            antecedent = rs,
                                            consequent = r})
                     (fn {source = s,
                          target = t,
                          antecedent = rs,
                          consequent = r} => (s, t, rs, r));

  val tSchemaData_rpc = Rpc.Datatype.convert
                            "TransferSchema.tSchemaData"
                            (Rpc.Datatype.tuple6
                                 (String.string_rpc,
                                  String.string_rpc,
                                  String.string_rpc,
                                  String.string_rpc,
                                  Real.real_rpc,
                                  tSchema_rpc))
                            (fn (n, s, t, i, r, x) => {name = n,
                                                      sourceConSpecN = s,
                                                      targetConSpecN = t,
                                                      interConSpecN = i,
                                                      strength = r,
                                                      tSchema = x})
                            (fn {name = n,
                                 sourceConSpecN = s,
                                 targetConSpecN = t,
                                 interConSpecN = i,
                                 strength = r,
                                 tSchema = x} => (n, s, t, i, r, x));

  exception badForm
  fun wellFormedTransferSchema iCS {source,target,antecedent,consequent} =
    Pattern.wellFormed (#source iCS) source andalso Pattern.wellFormed (#target iCS) target andalso
    Pattern.wellFormed (#inter iCS) consequent andalso List.all (Pattern.wellFormed (#inter iCS)) antecedent

  fun nameOf {name,...} = name;

  fun declareTransferSchema x = x;

  fun inverse {source,target,antecedent,consequent} =
    {source = target, target = source, antecedent = antecedent, consequent = consequent}
  fun inverseData {name,sourceConSpecN,targetConSpecN,interConSpecN,strength,tSchema} =
    {name = name, sourceConSpecN = targetConSpecN, targetConSpecN = sourceConSpecN, interConSpecN = interConSpecN, strength = strength, tSchema = inverse tSchema}


end;
