import "core.sequent";

signature KNOWLEDGE =
sig
  type base

  (* schema knowledge *)
  val schemasOf : base -> Sequent.schemaData Seq.seq;
  val conSpecImportsOf : base -> (string * string list) list

  val conSpecIsImportedBy : (string * string list) list -> string -> string -> bool

  (* Building a knowledge base *)
  val addSchema : base -> Sequent.schemaData -> real -> base;
  val addConSpecImports : base -> (string * string list) -> base
  val adaptToMSpace : string list -> base -> base;

  val findSchemaWithName : base -> string -> Sequent.schemaData option;

  val join : base -> base -> base;
  val empty : base;
end;

structure Knowledge : KNOWLEDGE =
struct
  type base = {schemas : Sequent.schemaData Seq.seq,
               conSpecImports : (string * string list) list};

  (* Schema knowledge *)
  fun schemasOf KB = #schemas KB
  fun conSpecImportsOf KB = #conSpecImports KB

  exception Duplicate
  fun iCmp (i,i') = (case Real.compare (#strength i', #strength i) of EQUAL => (case String.compare (#name i,#name i') of EQUAL => raise Duplicate | y => y) | x => x)

  fun addSchema KB sch s =
    {schemas = Seq.insert sch (#schemas KB) iCmp,
     conSpecImports = #conSpecImports KB}

  fun addConSpecImports KB (n,L) =
    {schemas = #schemas KB,
     conSpecImports = (n,L) :: #conSpecImports KB}

  fun conSpecIsImportedBy conSpecImports n1 n2 =
    List.exists (fn (x,L) => x = n2 andalso
                             (List.exists (fn y => n1 = y) L orelse List.exists (fn y => conSpecIsImportedBy conSpecImports n1 y) L))
                conSpecImports

(* functions for finding an injection of one list into another *)
fun findArg _ _ [] = NONE
  | findArg i q (y::ys) = if q y then SOME (i,y) else findArg (i+1) q ys
fun reserve 0 (x::xs) = NONE :: xs
  | reserve i (x::xs) = x :: reserve (i-1) xs
  | reserve _ [] = []
fun findListInjection p _ [] L = SOME (fn _ => NONE,fn _ => NONE)
  | findListInjection p i (x::xs) L = 
    case findArg 0 (fn y => case y of NONE => false | SOME y' => p x y') L of 
        NONE => NONE
      | SOME (j, SOME y) => (case findListInjection p (i+1) xs (reserve j L) of 
                                SOME R => SOME ((fn n => if n = i then SOME j else #1 R n, fn m => if m = j then SOME i else #2 R m))
                              | NONE => NONE)
      | SOME (j, NONE) => raise Match


  fun adaptSchema conSpecImports CSN {schema = (A,C), strength, name, conSpecNames} =
    let 
      val (fx,fy) = valOf (findListInjection (fn x => fn y => x = y orelse conSpecIsImportedBy conSpecImports x y) 0 conSpecNames (map SOME CSN))
      val empty = Graph.empty
      fun makeNewSchema _ [] = ([],[])
        | makeNewSchema i (_::xs) = 
          let val (A',C') = makeNewSchema (i+1) xs 
          in case fy i of 
                SOME j => (List.nth(A,j) :: A', List.nth(C,j) :: C')
              | NONE => (empty :: A', empty :: C')
          end
    in 
      Seq.single {schema = makeNewSchema 0 CSN, strength = strength, name = name, conSpecNames = CSN}
    end handle Option => Seq.empty
(*)
  fun adaptSchema conSpecImports CSN {schema = (A,C), strength, name, conSpecNames} =
    let
      val empty = Graph.empty
      (*)
      val conSpecNames = [0,2,5]
      val CSN = [1,2,3,4,5]
      val empty = ""
      val (A,C) = (["a","b","c"],["a'","b'","c'"])*)
      fun whichItem' _ _ [] = NONE
        | whichItem' i s (x::xs) = 
          if conSpecIsImportedBy conSpecImports s x then SOME i
          else whichItem' (i+1) s xs
      fun whichItem _ s [] Y = whichItem' 0 s Y
        | whichItem i s (x::xs) Y = 
          if s = x then SOME i else whichItem (i+1) s xs Y
      fun makeFun _ [] _ = (fn _ => NONE)
        | makeFun i (x::xs) Y = (fn j => if i = j then whichItem 0 x Y Y else makeFun (i+1) xs Y j)
      val fx = makeFun 0 CSN conSpecNames
      val fy = makeFun 0 conSpecNames CSN 
      fun makeNewSchema _ [] = ([],[])
        | makeNewSchema i (_::xs) = 
          let val (A',C') = makeNewSchema (i+1) xs 
          in case fx i of 
                SOME j => (List.nth(A,j) :: A', List.nth(C,j) :: C')
              | NONE => (empty :: A', empty :: C')
          end
      fun isInjection i [] = true
        | isInjection i (_::xs) = isSome (fy i) andalso isInjection (i+1) xs
      (*val s = makeNewSchema 0 CSN;*)
      val iSpecName = List.last CSN
      fun schemaInISpace () =
        (case List.last conSpecNames of iSpecNameOfSchema =>
          iSpecNameOfSchema = iSpecName orelse conSpecIsImportedBy conSpecImports iSpecNameOfSchema iSpecName)
      (*val _ = if schemaInISpace () then map (fn x => print (x ^ ",")) conSpecNames else []
      val _ = print "\n"*)
    in 
      if isInjection 0 conSpecNames andalso schemaInISpace () then 
        ((*print (List.toString (fn x => x) conSpecNames ^" "^ name ^ " iScha adapted to " ^ List.toString (fn x => x) CSN ^ "\n");*)
        Seq.single {schema = makeNewSchema 0 CSN, strength = strength, name = name, conSpecNames = CSN} )
      else 
        Seq.empty
    end*)

  fun adaptToMSpace CSN KB =
    let val {conSpecImports,schemas,...} = KB
        val adaptedSchemas = Seq.maps (adaptSchema conSpecImports CSN) schemas
        val _ = map (fn x => print ("schema: \n" ^ Sequent.stringOfSchemaData x ^ "\n\n\n")) (Seq.list_of adaptedSchemas)
    in {schemas = adaptedSchemas,
        conSpecImports = conSpecImports}
    end


  fun findSchemaWithName KB name =
    Seq.findFirst (fn x => #name x = name) (#schemas KB)

  fun cmpI (t1,t2) = List.compare String.compare ([#name t1,List.last (#conSpecNames t1)],[#name t2,List.last (#conSpecNames t2)])
  (*fun cmpT (t1,t2) = List.compare String.compare ([#name t1,#interConSpecN t1],[#name t2,#interConSpecN t2])*)
  fun cmpCS ((s,L),(s',L')) = List.compare String.compare ((s::L),(s'::L'))

  fun join k1 k2 =
    {schemas = Seq.insertManyNoEQUAL (#schemas k1) (#schemas k2) cmpI,
     conSpecImports = List.mergeNoEQUAL cmpCS (#conSpecImports k1) (#conSpecImports k2)}

  val empty =
    {schemas = Seq.empty,
     conSpecImports = []}

end;
