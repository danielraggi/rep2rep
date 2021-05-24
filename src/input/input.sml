import "util.logging";
import "util.sequence";

import "parser";

signature INPUT =
sig
  val loadCorrespondences : string -> Correspondence.corr FiniteSet.set
  val loadRelations : string -> Relation.relationship FiniteSet.set
  val loadKnowledge : string -> string -> Knowledge.base
end;

structure Input : INPUT =
struct
  fun loadCorrespondences filename =
    let
      val file = TextIO.openIn ("descriptions/"^filename)
      val corrBulk = TextIO.inputAll file
      val _ = TextIO.closeIn file
      val corrChars = case rev (String.explode corrBulk) of #"\n"::L => rev L | L => rev L
      val corrList = Parser.splitLevelWithSeparatorApply Parser.correspondence #"\n" corrChars
    in FiniteSet.ofList corrList
    end
  fun loadRelations filename =
    let
      val file = TextIO.openIn ("descriptions/"^filename)
      val relBulk = TextIO.inputAll file
      val _ = TextIO.closeIn file
      val relChars = case rev (String.explode relBulk) of #"\n"::L => rev L | L => rev L
      val relList = Parser.splitLevelWithSeparatorApply Parser.relationship #"\n" relChars
    in FiniteSet.ofList relList
    end;

  fun loadKnowledge corrfilename relfilename =
    let val rels = loadRelations relfilename
        val corrs = loadCorrespondences corrfilename
    in Knowledge.make rels corrs
    end
end;
