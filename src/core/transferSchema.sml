import "core.pattern";
import "core.relation";

signature TRANSFERSCHEMA =
sig
  type tSch = {name : string,
               sourcePattern : Pattern.construction,
               targetPattern : Pattern.construction,
               antecedent : Relation.relationship list,
               consequent : Relation.relationship,
               pullList : (Relation.T * Relation.T * CSpace.token list) list};

  val corr_rpc : tSch Rpc.Datatype.t;

  val wellFormed : (*CSpace.conSpec ->*) Type.typeSystem -> (*CSpace.conSpec ->*) Type.typeSystem -> tSch -> bool;
  val nameOf : tSch -> string;
  val patternsOf : tSch -> Pattern.pattern * Pattern.pattern;
  val relationshipsOf : tSch -> Relation.relationship list * Relation.relationship;
  val pullListOf : tSch -> (Relation.T * Relation.T * CSpace.token list) list
  val ofRelationship : Relation.relationship -> string -> tSch;
  val declareCorrespondence : {name : string,
                               sourcePattern : Pattern.construction,
                               targetPattern : Pattern.construction,
                               antecedent : Relation.relationship list,
                               consequent : Relation.relationship,
                               pullList : (Relation.T * Relation.T * CSpace.token list) list} -> tSch;
end;

structure TransferSchema : TRANSFERSCHEMA =
struct
  type tSch = {name : string,
               sourcePattern : Pattern.construction,
               targetPattern : Pattern.construction,
               antecedent : Relation.relationship list,
               consequent : Relation.relationship,
               pullList : (Relation.T * Relation.T * CSpace.token list) list};

  val corr_rpc = Rpc.Datatype.convert
                     "Correspondence.corr"
                     (Rpc.Datatype.tuple6
                          (String.string_rpc,
                           Pattern.construction_rpc,
                           Pattern.construction_rpc,
                           List.list_rpc Relation.relationship_rpc,
                           Relation.relationship_rpc,
                           List.list_rpc
                               (Rpc.Datatype.tuple3
                                    (Relation.T_rpc,
                                     Relation.T_rpc,
                                     List.list_rpc CSpace.token_rpc))))
                     (fn (n, s, t, rs, r, p) => {name = n,
                                              sourcePattern = s,
                                              targetPattern = t,
                                              tokenRels = rs,
                                              constructRel = r,
                                              pullList = p})
                     (fn {name = n,
                          sourcePattern = s,
                          targetPattern = t,
                          tokenRels = rs,
                          constructRel = r,
                          pullList = p} => (n, s, t, rs, r, p));

  exception badForm
  fun wellFormed sT tT {name,sourcePattern,targetPattern,antecedent,consequent,pullList} =
    let fun inTokens (t::L) tseq = List.exists (CSpace.sameTokens t) tseq andalso inTokens L tseq
          | inTokens [] _ = true
        val sourceTokens = Pattern.fullTokenSequence sourcePattern
        val targetTokens = Pattern.fullTokenSequence targetPattern
        fun okAtTokens ((sfseq,tfseq,_)::rfs) = inTokens sfseq sourceTokens
                                         andalso inTokens tfseq targetTokens
                                         andalso okAtTokens rfs
          | okAtTokens [] = true
       fun okAtConstructs ([t],[t'],_) = CSpace.sameTokens t (Pattern.constructOf sourcePattern)
                                 andalso CSpace.sameTokens t' (Pattern.constructOf targetPattern)
          | okAtConstructs _ = false
       fun okAtPullList [] = true
         | okAtPullList ((_,_,tL)::pL) = List.all (fn t => List.exists (CSpace.sameTokens t) targetTokens) tL
                                      andalso List.all (fn t => not (CSpace.sameTokens t (Pattern.constructOf targetPattern))) tL
                                      andalso okAtPullList pL
    in Pattern.wellFormed sT sourcePattern andalso Pattern.wellFormed tT targetPattern
        andalso okAtConstructs consequent andalso okAtTokens antecedent
        andalso okAtPullList pullList
    end

  fun nameOf {name,...} = name;

  fun patternsOf {sourcePattern,targetPattern,...} = (sourcePattern,targetPattern);
  fun relationshipsOf {antecedent,consequent,...} = (antecedent,consequent);
  fun pullListOf {pullList,...} = pullList

  fun declareTransferSchema x = x;
  (*the following turns a relation between tokens into a tSchema, with Rf being the
    "always true" relation, and Rc being the relation we want.*)
  exception nonBinary
  fun ofRelationship (xs,ys,R) name =
    let val (sPc,tPc) = case (xs,ys) of ([x],[y]) => (x,y) | _ => raise nonBinary
        val sP = Pattern.Source sPc
        val tP = Pattern.Source tPc
    in {name = name,
        sourcePattern = sP,
        targetPattern = tP,
        antecedent = [],
        consequent = Relation.makeRelationship ([sPc],[tPc],R),
        pullList = []}
    end;

end;
