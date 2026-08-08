(* Source positions, diagnostics, and the error exception.
   Every token carries a position; every diagnostic quotes one. *)

type pos = { file : string; line : int; col : int }

let nowhere = { file = "<none>"; line = 0; col = 0 }

exception Kerr of pos * string

let fail pos fmt = Printf.ksprintf (fun s -> raise (Kerr (pos, s))) fmt

(* source text of every file we lexed, for the caret line in diagnostics *)
let sources : (string, string array) Hashtbl.t = Hashtbl.create 8

let register_source file lines = Hashtbl.replace sources file (Array.of_list lines)

let show p = Printf.sprintf "%s:%d:%d" p.file p.line p.col

(* "file:line:col: error [K4]: msg" + the offending source line + a caret *)
let render (p : pos) (msg : string) : string =
  let b = Buffer.create 256 in
  Buffer.add_string b (Printf.sprintf "%s: error: %s\n" (show p) msg);
  (match Hashtbl.find_opt sources p.file with
   | Some ls when p.line >= 1 && p.line <= Array.length ls ->
     let src = ls.(p.line - 1) in
     let gutter = Printf.sprintf "%5d | " p.line in
     Buffer.add_string b (gutter ^ src ^ "\n");
     let pad = String.make (String.length gutter) ' ' in
     let caret = String.make (max 0 (p.col - 1)) ' ' ^ "^" in
     Buffer.add_string b (pad ^ caret ^ "\n")
   | _ -> ());
  Buffer.contents b
