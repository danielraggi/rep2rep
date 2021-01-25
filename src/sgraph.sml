import "term"
import "constructor"
import "set"

signature SGRAPH =
sig
  type trep = string;
  type crep = string;
  type arrow = string;
  type trepLabel = trep -> Term.T;
  type crepLabel = crep -> Constructor.T;
  type vertLabel = trepLabel * crepLabel;
  type T = (trep set * crep set * arrow set * incidentVertices * vertexLabel);
end

structure SGraph : SGRAPH =
struct
  type trep = string;
  type crep = string;
  type arrow = string;
  type trepLabel = trep -> CSpace.term;
  type crepLabel = crep -> CSpace.constructor;
  type vertLabel = trepLabel * crepLabel;
  type T = (trep set * crep set * arrow set * incidentVertices * vertexLabel);
end
