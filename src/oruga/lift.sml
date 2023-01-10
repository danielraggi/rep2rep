import "core.pattern";

signature LIFT =
sig
  val string : string -> Construction.construction
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
                val charTy = case x of #"(" => "oB" | #")" => "cB" | _ => str x ^ ":nonBChar"
                val charT = Construction.Source (CSpace.makeToken ("t" ^ n ^ "0") charTy)
                val stringT = cl (n ^ "1") xs
            in Construction.TCPair ({token = thisTok, constructor = consCons}, [charT,stringT])
            end
    in cl "" (String.explode s)
    end;



end
