import "core.construction";
import "util.rpc";

signature RENDERERS = sig
    val all: (string * Rpc.endpoint) list;
end;

structure Renderers : RENDERERS = struct
(* Renderers take a construction, and produces a list of (id, (html, width, height)) tuples.
   The ids are taken from the tokens in the construction. The width and height are the size
   of the rendering if it were to be inserted into a webpage.
 *)
type renderer = Construction.construction -> (string * (string * real * real)) list;

fun mkEndpoint (cspace:string) (renderer:renderer) : Rpc.endpoint =
    Rpc.provide
        ("server.renderer." ^ cspace,
         Construction.construction_rpc,
         List.list_rpc(Rpc.Datatype.tuple2(String.string_rpc,
                                           Rpc.Datatype.tuple3(String.string_rpc,
                                                               Real.real_rpc,
                                                               Real.real_rpc))))
        renderer;

(* To provide a new renderer, update all to have a new entry, such as
        ("arithG", mkEndpoint("arithG", my_arithg_renderer))
   where my_arithg_renderer is your renderer for the construction space.
 *)
val all = [];

end;