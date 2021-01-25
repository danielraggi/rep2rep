import "cspace"

signature CONSTRUCTION =
sig
  type T = (SGraph.T * trep);
  datatype CMT = Leaf of trep | Node of crep * cmt list;
  val validCMT : CMT -> bool;
  val CMTtoConstruction : CMT -> T;
end

structure Construction : CONSTRUCTION =
struct
  type construction = (SGraph.T * vertex);
  datatype CMT = Leaf of trep | Node of crep * cmt list;

end
