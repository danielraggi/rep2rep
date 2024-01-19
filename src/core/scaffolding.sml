import "core.pattern";
import "core.graph";

signature SCAFOLDING =
sig 
  val graphOfOldConstruction : Pattern.construction -> Graph.graph
  val oldConstructionsOfGraph : CSpace.conSpecData -> Graph.graph -> Pattern.construction list
end

structure Scaffolding : SCAFOLDING =
struct

  fun graphOfOldConstruction ct =
    let
      fun gooc (Pattern.Source t) = [{token = t, inputs = []}]
        | gooc (Pattern.Reference t) = [{token = t, inputs = []}]
        | gooc (Pattern.TCPair (tc,ch)) = {token = #token tc, inputs = [{constructor = CSpace.nameOfConstructor (#constructor tc), inputTokens = map Pattern.constructOf ch}]} :: List.flatmap gooc ch
    in Graph.factorise (gooc ct)
    end

  fun unzip [] = ([],[])
    | unzip ((x,y)::L) = case unzip L of (Lx,Ly) => (x::Lx,y::Ly)

  fun oldConstructionsOfGraph CS g =
    let
      fun getConstructor cn = case CSpace.findConstructorWithName cn CS of SOME c => c | NONE => (print ("constructor " ^cn ^ " not found"); raise Option)
      fun tokensMatchConstructs [] [] = true
        | tokensMatchConstructs (tk::tks) (ct::cts) = CSpace.sameTokens tk (Pattern.constructOf ct) andalso tokensMatchConstructs tks cts
        | tokensMatchConstructs _ _ = false
      fun attachDownwards {token,inputs = []} (Pattern.Source t) = (CSpace.sameTokens token t, Pattern.Source t)
        | attachDownwards {token,inputs = [{constructor,inputTokens}]} (Pattern.Source t) = 
            if CSpace.sameTokens token t then 
              (true, Pattern.TCPair ({token = token, constructor = getConstructor constructor}, map Pattern.Source inputTokens))
            else 
              (false, Pattern.Source t)
        | attachDownwards {token,inputs = []} (Pattern.TCPair (tc,ch)) = (CSpace.sameTokens token (#token tc), Pattern.TCPair (tc,ch))
        | attachDownwards (tin as {token,inputs = [{constructor,inputTokens}]}) (Pattern.TCPair (tc,ch)) = 
            if CSpace.sameTokens token (#token tc) andalso constructor = CSpace.nameOfConstructor (#constructor tc) andalso tokensMatchConstructs inputTokens ch then
              (true,Pattern.TCPair (tc,ch))
            else
              (case unzip (map (attachDownwards tin) ch) of (X,CH) =>
                (List.exists (fn x => x) X, Pattern.TCPair (tc,CH)))
        | attachDownwards {token,inputs = []} (Pattern.Reference t) = (CSpace.sameTokens token t,Pattern.Reference t)
        | attachDownwards tin (Pattern.Reference t) = (false,Pattern.Reference t)
        | attachDownwards _ _ = raise Match

      fun makeFromTokenListAndAttach [] ct = (false, [])
        | makeFromTokenListAndAttach (tk::tks) ct = 
            if CSpace.sameTokens tk (Pattern.constructOf ct) then 
              (true,ct :: map Pattern.Source tks)
            else 
              let val (x,cts) = makeFromTokenListAndAttach tks ct 
              in (x, Pattern.Source tk :: cts) 
              end
      fun attach (tin as {token,inputs = []}) ct = attachDownwards tin ct
        | attach (tin as {token,inputs = [{constructor,inputTokens}]}) ct = 
          let val (x,ch) = makeFromTokenListAndAttach inputTokens ct 
          in if x then (x,Pattern.TCPair ({token = token, constructor = getConstructor constructor}, ch)) else attachDownwards tin ct
          end
      fun ocotinSingle ({token,inputs = []}) = Pattern.Source token
        | ocotinSingle ({token,inputs = [{constructor,inputTokens}]}) = Pattern.TCPair ({token = token, constructor = getConstructor constructor}, map Pattern.Source inputTokens)
      fun ocotin tin [] = [ocotinSingle tin]
        | ocotin tin (ct::cts) = 
          let val (x,ct') = attach tin ct 
          in if x then (ct'::cts) else ct :: ocotin tin cts
          end
      fun ocog [] cts = cts
        | ocog (tin::g') cts = ocog g' (ocotin tin cts)
    in ocog (Graph.expand g) []
    end

end