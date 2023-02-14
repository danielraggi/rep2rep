import "oruga.document";

signature SMLCPARSERS =
sig
  val parseProbSys : string -> Construction.construction;
end;

structure SMLCParsers : SMLCPARSERS =
struct
  val makeRealConstructor = CSpace.makeConstructor ("makeReal",(["nat10","nat10"],"real10"))
  val addEqnConstructor = CSpace.makeConstructor ("addEqn",(["probEqn","probSys"],"probSys"))
  val makeEqnConstructor = CSpace.makeConstructor ("makeEqn",(["events","numExp"],"probEqn"))
  val makeCondConstructor = CSpace.makeConstructor ("makeCond",(["event","event"],"condEvent"))
  val infixConstructor = CSpace.makeConstructor ("infix",(["event","bin","event"],"event"))
  val complementConstructor = CSpace.makeConstructor ("complement",(["event"],"event"))
  val makeEventConstructor = CSpace.makeConstructor ("makeEvent",(["string"],"event"))

  val dummyName = "dummy"
  val interToken = CSpace.makeToken dummyName "inter"
  val unionToken = CSpace.makeToken dummyName "union"

  fun parseEvent s =
    let val chL = List.maps String.explode (Parser.removeOuterBrackets (Document.tokenise s))
    in case Parser.splitLevelWithSepFunApply (fn x => x) (fn x => x = #"U") chL of
          (s1::s2::L) => Construction.TCPair ({token = CSpace.makeToken dummyName ((String.implode chL) ^ ":" ^ "event"), constructor = infixConstructor},
                                [parseEvent s1, Construction.Source unionToken, parseEvent (String.concatWith "U" (s2::L))])
        | _ => case Parser.splitLevelWithSepFunApply (fn x => x) (fn x => x = #"&") chL of
                  (s1::s2::L) => Construction.TCPair ({token = CSpace.makeToken dummyName ((String.implode chL) ^ ":" ^ "event"), constructor = infixConstructor},
                                        [parseEvent s1, Construction.Source interToken, parseEvent (String.concatWith "&" (s2::L))])
                | _ => case chL of
                          (#"-"::L) => Construction.TCPair ({token = CSpace.makeToken dummyName ((String.implode chL) ^ ":" ^ "event"), constructor = complementConstructor},
                                              [parseEvent (String.implode L)])
                        | _ => Construction.Source (CSpace.makeToken dummyName ((String.implode chL) ^ ":" ^ "event"))
    end

    fun parseEvents s =
      let val s = Document.deTokenise (Parser.removeOuterBrackets (Document.tokenise s))
      in case String.breakOn "|" s of
            (s1, "|", s2) => Construction.TCPair ({token = CSpace.makeToken dummyName (s ^ ":" ^ "condEvent"), constructor = makeCondConstructor},
                                    [parseEvent s1,parseEvent s2])
          | _ => parseEvent s
      end

  fun parsePrExpr s = (case String.explode s of ((#"P")::(#"r")::evs) => parseEvents (String.implode evs) | _ => (print s; raise Match))

  fun parseNum s = (case String.breakOn "." s of
                        (_,".",_) => Construction.Source (CSpace.makeToken dummyName (s ^ ":real10"))
                      | ("1",_,_) => Construction.Source (CSpace.makeToken dummyName "1")
                      | ("0",_,_) => Construction.Source (CSpace.makeToken dummyName "0")
                    | _ => (print "oops1"; raise Match))

  fun parseEquation s = (case String.breakOn "=" s of
                            (s1,"=",s2) => Construction.TCPair ({token = CSpace.makeToken dummyName (s ^ ":probEqn"), constructor = makeEqnConstructor},[parsePrExpr s1, parseNum s2])
                          | _ => (print "oops2"; raise Match))


  fun parseProbSys s =
    let val ns = Document.normaliseString s
        fun differentiateTokenNames ct =
          let fun dtnL _ _ [] = []
                | dtnL s i (x::L) = dtn s i x :: dtnL s (i+1) L
              and dtn s i (Construction.Source t) = Construction.Source (CSpace.makeToken ("t_{"^ s ^ Int.toString i^"}") ( (CSpace.typeOfToken t)))
                | dtn s i (Construction.Reference t) = Construction.Reference (CSpace.makeToken ("t_{"^ s ^Int.toString i^"}") ( (CSpace.typeOfToken t)))
                | dtn s i (Construction.TCPair ({token = t,constructor = c},cs)) = Construction.TCPair ({token = CSpace.makeToken ("t_{"^ s ^Int.toString i^"}") ((CSpace.typeOfToken t)), constructor = c}, dtnL (s ^Int.toString i) 0 cs)
          in dtn "" 0 ct
          end
    in differentiateTokenNames
          (case Parser.splitLevelWithSepFunApply (fn x => x) (fn x => x = #";") (String.explode ns) of
              (s1::s2::L) => Construction.TCPair ({token = CSpace.makeToken dummyName (ns ^ ":probSys"), constructor = addEqnConstructor},
                                                  [parseEquation s1, parseProbSys (String.concatWith ";" (s2::L))])
            | _ => (case Parser.splitLevelWithSepFunApply (fn x => x) (fn x => x = #",") (String.explode ns) of
                        (s1::s2::L) => Construction.TCPair ({token = CSpace.makeToken dummyName (ns ^ ":probSys"), constructor = addEqnConstructor},
                                                            [parseEquation s1, parseProbSys (String.concatWith "," (s2::L))])
                      | _ => parseEquation s))
    end
end
