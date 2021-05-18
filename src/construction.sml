import "cspace";

signature CONSTRUCTION =
sig
  type ut = {token : CSpace.token, configurator : CSpace.configurator}
  datatype construction = TCPair of ut * construction list
                        | Loop of CSpace.token
                        | Source of CSpace.token ;
  type trail;

  val same : construction -> construction -> bool;
  val constructOf : construction -> CSpace.token;
  val wellFormed : TypeSystem.typeSystem -> construction -> bool;
  val almostWellFormed : construction -> bool;
  val grounded : construction -> bool;

  val CTS : construction -> trail list;
  val inducedConstruction : construction -> trail -> construction;
  val foundationSequence : construction -> CSpace.token list;
  val isGenerator : construction -> construction -> bool;
  val split : construction -> construction -> construction list;
  val fixInducedConstruction : construction -> construction;

  val renameConstruct : construction -> CSpace.token -> construction;

  val tokensOfConstruction : construction -> CSpace.token list;

  val toString : construction -> string;

  exception MalformedConstructionTerm
end;

structure Construction : CONSTRUCTION =
struct

  type ut = {token : CSpace.token, configurator : CSpace.configurator}
  datatype construction =
      TCPair of ut * construction list
    | Loop of CSpace.token
    | Source of CSpace.token ;
  datatype vertex = Token of CSpace.token | Configurator of CSpace.configurator
  type trail = vertex list;


  fun same (Source t) (Source t') = CSpace.sameTokens t t'
    | same (Loop t) (Loop t') = CSpace.sameTokens t t'
    | same (TCPair ({token = t, configurator = u}, cs)) (TCPair ({token = t', configurator = u'}, cs')) =
        CSpace.sameTokens t t' andalso CSpace.sameConfigurators u u'
        andalso List.allZip same cs cs'
    | same _ _ = false
    (* TO DO: implment a sameConstruction function which actually checks that constructions are the same, not only their construction terms *)

  fun constructOf (Source t) = t
    | constructOf (Loop t) = t
    | constructOf (TCPair ({token, ...}, _)) = token

  fun grounded (Source _) = false
    | grounded (Loop _) = false
    | grounded (TCPair (_, cs)) = List.all grounded cs

  fun CTS (Source t) = [[Token t]]
    | CTS (Loop t) = [[Token t]]
    | CTS (TCPair ({token, configurator}, cs)) =
        if null cs then [[Token token, Configurator configurator]]
        else
          let fun addToAll S = List.map (fn s => [Token token, Configurator configurator] @ s) S
          in List.maps (addToAll o CTS) cs
          end

  fun CTS_lossless (Source t) = [[Source t]]
    | CTS_lossless (Loop t) = [[Loop t]]
    | CTS_lossless (TCPair ({token, configurator}, cs)) =
        if null cs then [[(TCPair ({token = token, configurator = configurator}, []))]]
        else
          let fun addToAll S = List.map (fn s => TCPair ({token = token, configurator = configurator}, cs) :: s) S
          in List.maps (addToAll o CTS_lossless) cs
          end

  exception EmptyInputSequence
  fun pseudoCTS (Source t) = [[Source t]]
    | pseudoCTS (Loop t) = [[Loop t]]
    | pseudoCTS (TCPair (ut,cs)) =
        let fun addToFirst (s::S) = (TCPair (ut,cs) :: s) :: S | addToFirst [] = raise EmptyInputSequence (*[[(TCPair (ut,cs))]]*)
        in List.maps (addToFirst o pseudoCTS) cs
        end

  (* coherent checks that, if a token appears in two parts of term, there are no
  inconsistencies on which arrows target them, etc. This is very costly because it
  needs to compare every pair of subterms. *)
  fun coherent c =
    let
      fun strongCoh (Source t) (Source t') = CSpace.sameTokens t t'
        | strongCoh (Loop t) (Loop t') = CSpace.sameTokens t t'
        | strongCoh (TCPair ({token = t, configurator = u}, q)) (TCPair ({token = t', configurator = u'}, q')) =
            CSpace.sameTokens t t' andalso CSpace.sameConfigurators u u' andalso List.allZip strongCoh q q'
        | strongCoh (TCPair ({token = t, ...}, _)) (Loop t') = CSpace.sameTokens t t'
        | strongCoh (Loop t') (TCPair ({token = t, ...}, _)) = CSpace.sameTokens t t'
        | strongCoh _ _ = false
      fun weakCoh (c as TCPair ({token = t, ...}, _)) (c' as TCPair ({token = t', ...}, _)) =
            not (CSpace.sameTokens t t') orelse strongCoh c c'
            (*else List.all (weakCoh c) q' andalso List.all (weakCoh c') q*)
        (* the following 4 cases just make sure that there's no source somewhere that appears as a non-source somewhere else*)
        | weakCoh (TCPair ({token = t, ...}, _)) (Source t') = not (CSpace.sameTokens t t')
        | weakCoh (Source t') (TCPair ({token = t, ...}, _)) = not (CSpace.sameTokens t t')
        | weakCoh (Loop t) (Source t') = not (CSpace.sameTokens t t')
        | weakCoh (Source t') (Loop t) = not (CSpace.sameTokens t t')
        | weakCoh _ _ = true
      fun compareFromCTS ((x::C)::(h::t)) =
            List.all (weakCoh x) h andalso compareFromCTS (C::(h::t)) andalso compareFromCTS ((x::C)::t)
        | compareFromCTS ([]::(h::t)) = compareFromCTS (h::t)
        | compareFromCTS (_::[]) = true
        | compareFromCTS [] = true
    in compareFromCTS (pseudoCTS c) handle EmptyInputSequence => false
    end

  fun specialises T [] [] = true
    | specialises T (ty::tys) (ty'::tys') = (#subType T) (ty, ty') andalso specialises T tys tys'
    | specialises _ _ _ = false
  (* the datatype construction itself is not a perfect representation of constructions.
     The following function makes sure that they are well formed, by checking that Loops
     are actually loops and that non-Loops are not forming loops.*)
  fun wellFormed T c =
    let fun correctLoopsAndTypes tr (Source t) = not (List.exists (fn x => #token x = t) tr)
          | correctLoopsAndTypes tr (Loop t) = List.exists (fn x => #token x = t) tr
          | correctLoopsAndTypes tr (TCPair (ut, cs)) =
            let val typesOfInducedConstructs = map (CSpace.typeOfToken o constructOf) cs
                val (typesOfConfigurator,ty) = CSpace.typesOfConfigurator (#configurator ut)
                val typeOfConstruct = CSpace.typeOfToken (#token ut)
            in (#subType T) (typeOfConstruct, ty)
                andalso specialises T (typesOfInducedConstructs) typesOfConfigurator
                andalso List.all (fn x => not (CSpace.sameTokens (#token x) (#token ut))
                                  andalso not (CSpace.sameConfigurators (#configurator x) (#configurator ut))) tr
                andalso List.all (correctLoopsAndTypes (ut :: tr)) cs
            end
    in correctLoopsAndTypes [] c andalso coherent c
    end;
  exception MalformedConstructionTerm;

  (* this function simply ensures that induced constructions in a split are almost
    well formed, in the sense that there may be potential references to loops where
    the loop is not within the induced construction, but otherwise it's fine. *)
  fun almostWellFormed c =
    let fun correctLoops tr (Source t) = not (List.exists (fn x => #token x = t) tr)
          | correctLoops _ (Loop _) = true
          | correctLoops tr (TCPair (ut, cs)) =
              List.all (fn x => not (CSpace.sameTokens (#token x) (#token ut))
                        andalso not (CSpace.sameConfigurators (#configurator x) (#configurator ut))) tr
              andalso List.all (correctLoops (ut :: tr)) cs
    in correctLoops [] c andalso coherent c
    end;

  fun tokenOfVertex (Token t) = t
    | tokenOfVertex _ = raise MalformedConstructionTerm;

  fun foundationSequence c = map (tokenOfVertex o hd o rev) (CTS c);

  fun isGenerator (Source t) (Source t') = CSpace.sameTokens t t'
    | isGenerator (Loop t) (Loop t') = CSpace.sameTokens t t'
    | isGenerator (TCPair ({token = t, configurator = u}, cs)) (TCPair ({token = t', configurator = u'}, cs')) =
        CSpace.sameTokens t t' andalso CSpace.sameConfigurators u u'
        andalso List.allZip isGenerator cs cs'
    | isGenerator (Source t) (TCPair ({token, ...}, _)) =
        CSpace.sameTokens t token
    | isGenerator (Source t) (Loop t') =
        CSpace.sameTokens t t'
    | isGenerator _ _ = false

  exception badTrail
  fun inducedConstruction (Source t) [Token t'] =
        if CSpace.sameTokens t t'
        then Source t
        else raise badTrail
    | inducedConstruction (Loop t) [Token t'] =
        if CSpace.sameTokens t t'
        then Source t
        else raise badTrail
    | inducedConstruction (TCPair ({token = token, configurator = configurator}, cs)) (Token token'::Configurator configurator'::tr) =
        if CSpace.sameTokens token token' andalso CSpace.sameConfigurators configurator configurator'
        then let fun ic (c::C) = (inducedConstruction c tr handle badTrail => ic C)
                   | ic [] = raise badTrail
             in if null tr then TCPair ({token = token, configurator = configurator}, cs) else ic cs
             end
        else raise badTrail
    | inducedConstruction (TCPair ({token = token, configurator = configurator}, cs)) [Token t'] =
        if CSpace.sameTokens token t'
        then TCPair ({token = token, configurator = configurator}, cs)
        else raise badTrail
    | inducedConstruction _ _ = raise badTrail

  exception Match
  fun split c c' = map (inducedConstruction c) (CTS c')

  fun fixInducedConstruction c =
    let
      fun fic _ (Source t) = (Source t)
        | fic tr (Loop t) = if List.exists (fn x => #token x = t) tr then Loop t else Source t
        | fic tr (TCPair (ut, cs)) =
            TCPair (ut, map (fic (ut::tr)) cs)
    in fic [] c
    end


  exception BadConstruction
  fun renameConstruct ct t' =
    let fun rc _ (Source t)  = Source t
          | rc originalConstruct (Loop t) = if CSpace.sameTokens t originalConstruct then Loop t' else Loop t
          | rc originalConstruct (TCPair (ut, cs)) = TCPair (ut, map (rc originalConstruct) cs)
    in case ct of Source _ => Source t'
                | Loop _ => raise BadConstruction
                | TCPair ({token = t,configurator = u}, cs) => TCPair ({token = t',configurator = u}, map (rc t) cs)
    end


  (* belongs in lists *)
  fun removeRepetition eq (n::ns) = n :: removeRepetition eq (List.filter (fn x => not (eq x n)) ns)
    | removeRepetition _ [] = []

  fun tokensOfConstruction ct =
    let fun toc (Source t) = [t]
          | toc (Loop _) = []
          | toc (TCPair ({token, ...}, cs)) = token :: List.maps toc cs
    in removeRepetition CSpace.sameTokens (toc ct)
    end

  fun toString (Source t) = CSpace.stringOfToken t
    | toString (Loop t) = "Loop " ^ (CSpace.stringOfToken t)
    | toString (TCPair ({token,configurator}, cs)) =
       CSpace.stringOfToken token ^ "_" ^ CSpace.stringOfConfigurator configurator ^ "(" ^ String.concat (map toString cs) ^ ")"
end;
