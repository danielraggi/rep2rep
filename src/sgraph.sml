import "type"
import "constructor"
import "util.set"

signature SGRAPH =
sig
  type vertex = string;
  type arrow = string;
  type tokenLabelling = vertex -> Type.T;
  type crepLabelling = vertex -> Constructor.T;
  type vertLabelling = tokenLabelling * crepLabelling;
  type T = (token set * crep set * arrow set * incidentVertices * vertexLabelling);
end

structure SGraph : SGRAPH =
struct
  type vertex = string;
  type arrow = string;
  type tokenLabelling = vertex -> Type.T;
  type crepLabelling = vertex -> Constructor.T;
  type vertLabelling = tokenLabelling * crepLabelling;
  type T = (token set * crep set * arrow set * incidentVertices * vertexLabelling);
end
