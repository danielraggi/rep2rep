import "core.pattern";

signature LIFT =
sig
  val string : string -> Construction.construction
  val dropString : Construction.construction -> string
end

structure Lift : LIFT =
struct

(* assumes alignment with input/stringBTree oruga document.
  It converts an ML string into a construction *)
fun string s =
  let val emptyTyp = Type.fromString "empty"
      val charTyp = Type.fromString "char"
      val stringTyp = Type.fromString "string"
      val consSig = ([charTyp, stringTyp], stringTyp)
      val consCons = CSpace.makeConstructor ("cons", consSig)
      fun cl n [] = Construction.Source (CSpace.makeToken ("t" ^ n) emptyTyp)
        | cl n (x::xs) =
          let val thisTok = CSpace.makeToken ("t" ^ n) (String.implode (x::xs) ^ ":string")
              val charTy = case x of #"(" => "oB"
                                   | #")" => "cB"
                                   | #" " => "space"
                                   | #";" => "semicolon"
                                   | #"|" => "mid"
                                   | _ => str x ^ ":char"
              val charT = Construction.Source (CSpace.makeToken ("t" ^ n ^ "0") charTy)
              val stringT = cl (n ^ "1") xs
          in Construction.TCPair ({token = thisTok, constructor = consCons}, [charT,stringT])
          end
  in cl "" (String.explode s)
  end;

exception UnkownStringType of string
fun dropString ct =
  let fun atFnd t =
        (case String.breakOn ":" (CSpace.typeOfToken t) of
            (s,":","char") => s
          | ("oB","",_) => "("
          | ("cB","",_) => ")"
          | ("space","",_) => " "
          | ("semicolon","",_) => ";"
          | ("mid","",_) => "|"
          | ("empty","",_) => ""
          | (s1,s2,s3) => raise UnkownStringType (s1 ^ s2 ^ s3))
  in case ct of
        Construction.Source t => atFnd t
      | Construction.Reference t => atFnd t
      | Construction.TCPair (_,cs) => String.concat (map dropString cs)
  end


end
