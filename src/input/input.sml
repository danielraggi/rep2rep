import "util.logging";
import "util.sequence";

import "parser";

signature INPUT =
sig
  val loadTypeSystem : string -> TypeSystem.typeSystem
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
      val file = TextIO.openIn ("descriptions/"^filename)
      val TBulk = TextIO.inputAll file
      val _ = TextIO.closeIn file
      val TChars = normaliseLineBreaks (String.explode TBulk)
      val T = Parser.finiteTypeSystem (String.implode TChars)
    in T
    end

  fun loadCorrespondences filename =
    let
      val file = TextIO.openIn ("descriptions/"^filename)
      val corrBulk = TextIO.inputAll file
      val _ = TextIO.closeIn file
      val corrChars = normaliseLineBreaks (String.explode corrBulk)
      val corrList = Parser.splitLevelWithSeparatorApply Parser.correspondence #"\n" corrChars
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
