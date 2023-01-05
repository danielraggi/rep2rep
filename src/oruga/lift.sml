import "core.pattern";

signature LIFT =
sig
  val string : string -> Construction.construction
end

structure Lift : LIFT =
struct

(* assumes alignment with input/listBTree oruga document.
  It converts an ML string into a construction *)
fun string s =
    let val emptyTyp = Type.fromString "empty"
        val itemTyp = Type.fromString "item"
        val listTyp = Type.fromString "list"
        val insertSig = ([itemTyp, listTyp], listTyp)
        val insertCons = CSpace.makeConstructor ("insert", insertSig)
        fun cl n [] = Construction.Source (CSpace.makeToken ("t" ^ n) emptyTyp)
          | cl n (x::xs) =
            let val thisTok = CSpace.makeToken ("t" ^ n) (String.implode (x::xs) ^ ":list")
                val itemTy = case x of #"(" => "oB" | #")" => "cB" | _ => str x ^ ":nbItem"
                val itemT = Construction.Source (CSpace.makeToken ("t" ^ n ^ "0") itemTy)
                val listT = cl (n ^ "1") xs
            in Construction.TCPair ({token = thisTok, constructor = insertCons}, [itemT,listT])
            end
    in cl "" (String.explode s)
    end;



end
