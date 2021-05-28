import "util.logging";
import "util.sequence";

import "parser";

signature INPUT =
sig
  val loadCorrespondences : string -> Correspondence.corr FiniteSet.set
  val loadRelations : string -> Relation.relationship FiniteSet.set
  val loadKnowledge : string -> string -> Knowledge.base
  val loadConstruction : string -> Construction.construction
end;

structure Input : INPUT =
struct
  fun removeLineBreaks s =
    let fun rlb [] = []
          | rlb (x::X) = if x = #"\n" then rlb X else x :: rlb X
    in String.implode (rlb (String.explode s))
    end

  fun loadCorrespondences filename =
    let
      val file = TextIO.openIn ("descriptions/"^filename)
      val corrBulk = TextIO.inputAll file
      val _ = TextIO.closeIn file
      val corrChars = case rev (String.explode corrBulk) of #"\n"::L => rev L | L => rev L
      val corrList = Parser.splitLevelWithSeparatorApply (Parser.correspondence o removeLineBreaks) #"\n" corrChars
    in FiniteSet.ofList corrList
    end

  fun loadRelations filename =
    let
      val file = TextIO.openIn ("descriptions/"^filename)
      val relBulk = TextIO.inputAll file
      val _ = TextIO.closeIn file
      val relChars = case rev (String.explode relBulk) of #"\n"::L => rev L | L => rev L
      val relList = Parser.splitLevelWithSeparatorApply (Parser.relationship o removeLineBreaks) #"\n" relChars
    in FiniteSet.ofList relList
    end;

  fun loadKnowledge corrfilename relfilename =
    let val rels = loadRelations relfilename
        val corrs = loadCorrespondences corrfilename
    in Knowledge.make rels corrs
    end

  fun loadConstruction filename =
    let val file = TextIO.openIn ("descriptions/"^filename)
        val ctBulk = TextIO.inputAll file
        val _ = TextIO.closeIn file
        val ctString = removeLineBreaks ctBulk
    in Parser.construction ctString
    end
end;
