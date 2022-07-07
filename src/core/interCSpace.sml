import "core.pattern";
import "core.relation";

signature INTERCSPACE =
sig
  type interConSpec = {source : CSpace.conSpecData, target : CSpace.conSpecData, inter : CSpace.conSpecData}
  type tSchema = {name : string,
                  source : Pattern.construction,
                  target : Pattern.construction,
                  antecedent : Pattern.construction list,
                  consequent : Pattern.construction};

  val tSchema_rpc : tSchema Rpc.Datatype.t;

  val wellFormedTransferSchema : interConSpec -> tSchema -> bool;
  val nameOf : tSchema -> string;

  val declareTransferSchema : {name : string,
                               source : Pattern.construction,
                               target : Pattern.construction,
                               antecedent : Pattern.construction list,
                               consequent : Pattern.construction} -> tSchema;
end;

structure InterCSpace : INTERCSPACE =
struct
  type interConSpec = {source : CSpace.conSpecData, target : CSpace.conSpecData, inter : CSpace.conSpecData}
  type tSchema = {name : string,
                   source : Pattern.construction,
                   target : Pattern.construction,
                   antecedent : Pattern.construction list,
                   consequent : Pattern.construction};

  val tSchema_rpc = Rpc.Datatype.convert
                     "TransferSchemma.tSchema"
                     (Rpc.Datatype.tuple5
                          (String.string_rpc,
                           Pattern.construction_rpc,
                           Pattern.construction_rpc,
                           List.list_rpc Pattern.construction_rpc,
                           Pattern.construction_rpc))
                     (fn (n, s, t, rs, r) => {name = n,
                                              source = s,
                                              target = t,
                                              antecedent = rs,
                                              consequent = r})
                     (fn {name = n,
                          source = s,
                          target = t,
                          antecedent = rs,
                          consequent = r} => (n, s, t, rs, r));

  exception badForm
  fun wellFormedTransferSchema iCS {name,source,target,antecedent,consequent} =
    Pattern.wellFormed (#source iCS) source andalso Pattern.wellFormed (#target iCS) target andalso
    Pattern.wellFormed (#inter iCS) consequent andalso List.all (Pattern.wellFormed (#inter iCS)) antecedent

  fun nameOf {name,...} = name;

  fun declareTransferSchema x = x;

end;
