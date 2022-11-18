import "core.pattern";
import "core.relation";

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
                      tSchema : tSchema}


  val tSchema_rpc : tSchema Rpc.Datatype.t;

  val wellFormedTransferSchema : interConSpec -> tSchema -> bool;
  val nameOf : tSchemaData -> string;

  val declareTransferSchema : {source : Pattern.construction,
                               target : Pattern.construction,
                               antecedent : Pattern.construction list,
                               consequent : Pattern.construction} -> tSchema;
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

  exception badForm
  fun wellFormedTransferSchema iCS {source,target,antecedent,consequent} =
    Pattern.wellFormed (#source iCS) source andalso Pattern.wellFormed (#target iCS) target andalso
    Pattern.wellFormed (#inter iCS) consequent andalso List.all (Pattern.wellFormed (#inter iCS)) antecedent

  fun nameOf {name,...} = name;

  fun declareTransferSchema x = x;

end;
