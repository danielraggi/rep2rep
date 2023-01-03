import "core.pattern";

signature FLAT_PARSER =
sig
  val constructionOfString : string -> Construction.construction
end

structure FlatParser : FLAT_PARSER =
struct

(* assumes alignment with input/listBTree oruga document.
  It converts an ML string into a construction *)
fun constructionOfString s =
    let val emptyTyp = Type.fromString "empty"
        val itemTyp = Type.fromString "item"
        val listTyp = Type.fromString "list"
        val insertSig = ([itemTyp, listTyp], listTyp)
        val insertCons = CSpace.makeConstructor ("insert", insertSig)
        fun cl n [] = Construction.Source (CSpace.makeToken ("t" ^ n) emptyTyp)
          | cl n (x::xs) =
            let val thisTok = CSpace.makeToken ("t" ^ n) (String.implode (x::xs) ^ ":list")
                val itemT = Construction.Source (CSpace.makeToken ("t" ^ n ^ "0") (str x ^ ":item"))
                val listT = cl (n ^ "1") xs
            in Construction.TCPair ({token = thisTok, constructor = insertCons}, [itemT,listT])
            end
    in cl "" (String.explode s)
    end;

end
