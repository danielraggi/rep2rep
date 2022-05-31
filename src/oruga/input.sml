import "util.logging";
import "util.sequence";

import "oruga.parser";

signature INPUT =
sig
  val loadTypeSystem : string -> Type.typeSystem
  val loadTransferSchemas : string -> TransferSchema.tSch Seq.seq
  val loadRelations : string -> Relation.relationship FiniteSet.set
  val loadKnowledge : string -> Knowledge.base
  val loadConstruction : string -> Construction.construction
  val loadGoal : string -> Relation.relationship
  val loadDocument : string -> Parser.documentContent
  val structureTransfer : string -> string -> string -> string -> string -> int -> State.T Seq.seq
end;

structure Input : INPUT =
struct
  fun removeLineBreaks s =
    let fun rlb [] = []
          | rlb (x::X) = if x = #"\n" then rlb X else x :: rlb X
    in String.implode (rlb (String.explode s))
    end

  fun normaliseLineBreaks L =
    let fun nlb _ [] = []
          | nlb _ [#"\n"] = []
          | nlb (p,s,c) (#"\n"::(#"\n"::L)) = nlb (p,s,c) (#"\n"::L)
          | nlb (p,s,c) (x::xs) =
            let val p' = if x = #"(" then p+1 else (if x = #")" then p-1 else p)
                val s' = if x = #"[" then s+1 else (if x = #"]" then s-1 else s)
                val c' = if x = #"{" then c+1 else (if x = #"}" then c-1 else c)
                val nlbr = nlb (p',s',c') xs
            in if (p',s',c') = (0,0,0) orelse (x <> #"\n")
               then x :: nlbr
               else nlbr
            end
    in nlb (0,0,0) L
    end

  fun loadTypeSystem filename =
    let
      val file = TextIO.openIn ("input/typeSystems/"^filename)
      val TBulk = TextIO.inputAll file
      val _ = TextIO.closeIn file
      val TChars = normaliseLineBreaks (String.explode TBulk)
      val T = Parser.finiteTypeSystem (String.implode TChars)
    in T
    end

  fun loadTransferSchemas filename =
    let
      val file = TextIO.openIn ("input/transferSchemas/"^filename)
      val tschBulk = TextIO.inputAll file
      val _ = TextIO.closeIn file
      val tschChars = normaliseLineBreaks (String.explode tschBulk)
      val tschList = if tschChars = [] then []
                     else Parser.splitLevelWithSeparatorApply Parser.tSchema #"\n" tschChars
    in Seq.of_list tschList
    end

  fun loadRelations filename =
    let
      val file = TextIO.openIn ("input/transferSchemas/"^filename)
      val relBulk = TextIO.inputAll file
      val _ = TextIO.closeIn file
      val relChars = normaliseLineBreaks (String.explode relBulk)
      val relList = if relChars = [] then []
                    else Parser.splitLevelWithSeparatorApply Parser.relationship #"\n" relChars
    in FiniteSet.ofList relList
    end;

  fun loadKnowledge tschfilename (*relfilename*) =
    let (*val rels = loadRelations relfilename*)
        val tschs = loadTransferSchemas tschfilename
    in Knowledge.make tschs
    end

  fun loadConstruction filename =
    let val file = TextIO.openIn ("input/constructions/"^filename)
        val ctBulk = TextIO.inputAll file
        val _ = TextIO.closeIn file
        val ctString = removeLineBreaks ctBulk
    in Parser.construction ctString
    end

  fun loadGoal filename =
    let val file = TextIO.openIn ("input/"^filename)
        val rBulk = TextIO.inputAll file
        val _ = TextIO.closeIn file
        val rString = removeLineBreaks rBulk
    in Parser.relationship rString
    end

  fun loadDocument filename =
    let (*val file = TextIO.openIn ("descriptions/"^filename)
        val s = TextIO.inputAll file
        val _ = TextIO.closeIn file*)
    in Parser.document filename
    end

  fun structureTransfer docName sourceTySysName targetTySysName constructionName goalString i =
    let val DC = loadDocument docName
        val KB = Parser.knowledgeOf DC
        val sourceTySys = Parser.findTypeSystemWithName DC sourceTySysName
        val targetTySys = Parser.findTypeSystemWithName DC targetTySysName
        val ct = Parser.findConstructionWithName DC constructionName
        val goal = Parser.relationship goalString
    in Transfer.structureTransfer KB sourceTySys targetTySys ct goal i
    end

end;
