(*
http.sml

A very simple HTTP server.
*)

signature HTTP = sig

    exception HttpError of string

    datatype method = GET
                    | POST
                    | OPTIONS

    datatype status = OK
                    | NO_CONTENT
                    | BAD_REQUEST
                    | NOT_FOUND
           | INTERNAL_SERVER_ERROR;

    type addr
    type endpoint = string

    type request
    type response

    type contentType = string
    type content = Word8Vector.vector

    val addr: (string * int) -> addr

    structure Client :
        sig
            val makeRequest: (method * endpoint) -> (contentType * content) -> request
            val readResponse: response -> (status * contentType * content)

            val send: addr -> request -> unit;
            val fetch: addr -> request -> response;
        end;

    structure Server :
        sig
            val makeResponse: status -> (contentType * content) -> response;
            val readRequest: request -> (method * endpoint * contentType * content);

            val listen: addr -> (request -> response) -> unit;
        end;

end;

structure Http : HTTP = struct

exception HttpError of string
exception TooShort

datatype method = GET | POST | OPTIONS
datatype status = OK | NO_CONTENT | BAD_REQUEST | NOT_FOUND | INTERNAL_SERVER_ERROR

type addr = INetSock.sock_addr
type endpoint = string
type contentType = string
type content = Word8Vector.vector

type request = {
    method: method,
    endpoint: endpoint,
    headers: (string * string) list,
    content: content
}

type response = {
    status: status,
    headers: (string * string) list,
    content: content
}

fun addr (host, port) =
    INetSock.toAddr (Option.valOf (NetHostDB.fromString host),
                     port);

fun methodToString GET = "GET"
  | methodToString POST = "POST"
  | methodToString OPTIONS = "OPTIONS";

fun stringToMethod "GET" = GET
  | stringToMethod "POST" = POST
  | stringToMethod "OPTIONS" = OPTIONS
  | stringToMethod m = raise (HttpError ("Unknown method " ^ m));

fun statusToString OK = "200 OK"
  | statusToString NO_CONTENT = "204 No Content"
  | statusToString BAD_REQUEST = "400 Bad Request"
  | statusToString NOT_FOUND = "404 Not Found"
  | statusToString INTERNAL_SERVER_ERROR = "500 Internal Server Error";

fun stringToStatus status =
    let val (status, _, _) = String.breakOn " " status
    in case status of
           "200" => OK
         | "204" => NO_CONTENT
         | "400" => BAD_REQUEST
         | "404" => NOT_FOUND
         | "500" => INTERNAL_SERVER_ERROR
         | s => raise (HttpError ("Unknown status " ^ s))
    end;

fun getBytes vect start len =
    Word8Vector.tabulate (len, (fn i => Word8Vector.sub (vect, i + start)));

fun splitHeader bytes =
    let fun chopHeader i =
            if i + 3 >= Word8Vector.length bytes
            then (bytes, Byte.stringToBytes "")
            else let
                val slice = Word8VectorSlice.slice (bytes, i, SOME(4));
                val s = Byte.unpackStringVec slice;
                 in
                     if s = "\r\n\r\n"
                     then (getBytes bytes 0 i,
                           getBytes bytes (i+4) ((Word8Vector.length bytes)-(i+4)))
                     else chopHeader (i+1)
                 end;
        val (header_bytes, content) = chopHeader 0;
        val header_string = Byte.bytesToString header_bytes;
        val headers = String.splitOn "\r\n" header_string;
    in case headers of
           [] => raise (HttpError "Empty headers!")
         | (protocol::headers) =>
           (protocol,
            List.map
                (fn h =>
                    case String.breakOn ": " h of
                        (k, ": ", v) => (k, v)
                      | _ => raise (HttpError ("Malformed header '" ^ h ^ "'")))
                headers,
            content)
    end;

fun getHeader header headers =
    case List.find (fn (k, v) => k = header) headers of
        NONE => NONE
      | SOME (header, value) => SOME value;

fun addRequestHeader (k, v) {method, endpoint, headers, content} =
    {method = method,
     endpoint = endpoint,
     headers = (k, v)::headers,
     content = content};

fun addResponseHeader (k, v) {status, headers, content} =
    {status = status,
     headers = (k, v)::headers,
     content = content};

fun readRequestProtocol line =
    if String.isSuffix " HTTP/1.1" line
    then let val (method_s, _, endpoint) =
                 String.breakOn
                     " "
                     (String.substring
                          (line, 0,
                           (String.size line) - (String.size " HTTP/1.1")))
         in (stringToMethod method_s, endpoint) end
    else raise (HttpError ("Bad request protocol '" ^ line ^ "'"));

fun readResponseProtocol line =
    if String.isPrefix "HTTP/1.1 " line
    then stringToStatus (String.extract
                             (line,
                              (String.size line) - (String.size "HTTP/1.1 "),
                              NONE))
    else raise (HttpError ("Bad response protocol '" ^ line ^ "'"));

fun requestToBytes {method, endpoint, headers, content} =
    let val headers = String.concatWith "\r\n" (
                ((methodToString method) ^ " " ^ endpoint ^ " HTTP/1.1") ::
                (List.map (fn (k, v) => k ^ ": " ^ v) headers)
            ) ^ "\r\n";
    in Word8Vector.concat [Byte.stringToBytes headers, content] end;

fun bytesToRequest bytes =
    let val (protocol, headers, content) = splitHeader bytes;
        val (method, endpoint) = readRequestProtocol protocol;
        val contentLength =
            case getHeader "Content-Length" headers of
                NONE => 0
              | SOME l_s =>
                case Int.fromString l_s of
                    NONE => raise (HttpError
                                       "Content length not a number.")
                  | SOME(l) => l;
        val () = if contentLength = Word8Vector.length content
                 then ()
                 else raise TooShort;
    in {method = method,
        endpoint = endpoint,
        headers = headers,
        content = content} end;

fun responseToBytes {status, headers, content} =
    let val headers = String.concatWith "\r\n" (
                ("HTTP/1.1 " ^ (statusToString status)) ::
                (List.map (fn (k, v) => k ^ ": " ^ v) headers)
            ) ^ "\r\n\r\n";
    in Word8Vector.concat [Byte.stringToBytes headers, content] end;

fun bytesToResponse bytes =
    let val (protocol, headers, content) = splitHeader bytes;
        val status = readResponseProtocol protocol;
        val contentLength =
            case getHeader "Content-Length" headers of
                NONE => 0
              | SOME l_s =>
                case Int.fromString l_s of
                    NONE => raise (HttpError "Content length not an integer")
                  | SOME(l) => l;
        val () = if contentLength = Word8Vector.length content
                 then ()
                 else raise TooShort;
    in {status = status,
        headers = headers,
        content = content}
    end;

fun send_bytes sock vec =
    let fun f offset remaining =
            let val sent = Socket.sendVec
                               (sock,
                                Word8VectorSlice.slice (vec, offset, NONE));
            in if sent = remaining
               then offset + remaining
               else f (offset + sent) (remaining - sent)
            end;
    in f 0 (Word8Vector.length vec) end;

fun send_http sock vec =
    let val sent = send_bytes sock vec in
    if sent = Word8Vector.length vec then ()
    else raise (HttpError "Failed to send all bytes.")
    end;

fun recv_bytes sock =
    let fun f ans =
            let val chunk_size = 65536;
                val inv = Socket.recvVecNB (sock, chunk_size); in
                case inv of
                    NONE => Word8Vector.concat (List.rev ans)
                  | SOME inv => f (inv::ans)
            end
        val invec = f [];
    in if Word8Vector.length invec = 0
        then recv_bytes sock
        else invec
    end;

fun recv_http sock reader =
    let fun loop old_bytes =
            let val new_bytes = recv_bytes sock;
                val in_bytes = Word8Vector.concat [old_bytes, new_bytes];
                val response = reader in_bytes
                               handle TooShort => loop in_bytes;
            in response end;
    in loop (Byte.stringToBytes "") end;

fun send_request sock req = send_http sock (requestToBytes req);
fun send_response sock req = send_http sock (responseToBytes req);
fun recv_request sock = recv_http sock bytesToRequest;
fun recv_response sock = recv_http sock bytesToResponse;


structure Client = struct

fun makeRequest (method, endpoint) (contentType, content) =
    {method = method,
     endpoint = endpoint,
     headers = [("Content-Type", contentType),
                ("Content-Length", Int.toString (Word8Vector.length content))],
     content = content};

fun readResponse {status, headers, content} =
    (status,
     case getHeader "Content-Type" headers of
         NONE => raise (HttpError "Missing content type in response")
       | SOME t => t,
     content);

fun send (addr:addr) (request:request) : unit =
    let val request = addRequestHeader ("Connection", "close")
                                       request;
        val sock = INetSock.TCP.socket ();
        val () = Socket.connect (sock, addr);
        val () = send_request sock request;
        val () = Socket.close sock;
    in () end;

fun fetch addr request =
    let val sock = INetSock.TCP.socket ();
        val () = Socket.connect (sock, addr);
        val () = send_request sock request;
        val response = recv_response sock;
        val () = Socket.close sock;
    in response end;

end;

structure Server = struct

fun makeResponse status (contentType, content) =
    {status = status,
     headers = [("Access-Control-Allow-Origin", "*"),
                ("Content-Length", Int.toString (Word8Vector.length content)),
                ("Content-Type", contentType),
                ("Connection", "close")],
     content = content};

fun readRequest {method, endpoint, headers, content} =
    (method,
     endpoint,
     case getHeader "Content-Type" headers of
         SOME t => t
       | NONE => case getHeader "Content-Length" headers of
                     SOME "0" => "text/plain"
                   | _ => raise (HttpError "Missing content type in request"),
     content);

val preflight = {status = NO_CONTENT,
                 headers = [
                     ("Access-Control-Allow-Origin", "*"),
                     ("Access-Control-Allow-Methods", "POST, OPTIONS"),
                     ("Access-Control-Allow-Headers",
                      "X-PINGOTHER, Content-Type"),
                     ("Access-Control-Max-Age", "86400"),
                     ("Connection", "close")
                 ],
                 content = Byte.stringToBytes ""
                }
val internalError = makeResponse INTERNAL_SERVER_ERROR
                                 ("text/plain", Byte.stringToBytes "");

fun listen addr callback =
    let fun printDiagnostics e =
            print ((exnName e)
                   ^ " - "
                   ^ (exnMessage e)
                   ^ " - "
                   ^ (PolyML.makestring
                          (PolyML.Exception.exceptionLocation e))
                   ^ "\n");
        fun forever f = (f() handle e => (); forever f);
        val sock = INetSock.TCP.socket ();
        val () = Socket.bind (sock, addr);
        val () = Socket.listen (sock, 512);
    in
        forever
            (fn () =>
                let val (sock', remote_addr) = Socket.accept sock;
                    fun handler () = let
                        val response =
                            let val request = recv_request sock' in
                                case #method request of
                                    OPTIONS => preflight
                                  | _ =>  callback request
                            end handle (HttpError reason) => (
                                print ("HTTP Error: " ^ reason ^ "\n");
                                internalError
                            )
                                     | e => (printDiagnostics e;
                                             internalError);
                        val () = send_response sock' response;
                        val () = Socket.close sock';
                    in () end handle e => printDiagnostics e;
                    val _ = Thread.Thread.fork (handler, []);
                in () end)
    end;

end;

end;
