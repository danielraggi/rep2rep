import "oruga.lift";
import "oruga.document";

val makeRealConstructor = CSpace.makeConstructor ("makeReal",(["nat10","nat10"],"real10"))
val addEqnConstructor = CSpace.makeConstructor ("addEqn",(["probEqn","probSys"],"probSys"))
val makeEqnConstructor = CSpace.makeConstructor ("makeEqn",(["events","numExp"],"probEqn"))
val makeCondConstructor = CSpace.makeConstructor ("makeCond",(["event","event"],"condEvent"))
val infixConstructor = CSpace.makeConstructor ("makeCond",(["event","bin","event"],"event"))
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

fun parseSystem s = case Parser.splitLevelWithSepFunApply (fn x => x) (fn x => x = #";") (String.explode (Document.normaliseString s)) of
                        (s1::s2::L) => Construction.TCPair ({token = CSpace.makeToken dummyName (s ^ ":probSys"), constructor = addEqnConstructor},[parseEquation s1,parseSystem (String.concatWith ";" (s2::L))])
                      | _ => parseEquation s
