import "sgraph"

signature CSPACE =
sig
  type constructor;
  type spec;
  type vertex;
  type arrow;
end

structure CSpace : CSPACE =
struct
  type constructor;
  type spec = constructor -> Type.T list * Type.T ;
  type vertex = SGraph.vertex;
  type arrow = SGraph.arrow;

  fun sameVertices = SGraph.sameVertices;
end
