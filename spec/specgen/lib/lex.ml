(* Line-oriented tokenizer for .kspec.

   The format is line-structured (header lines and table rows), so the lexer
   returns a list of logical lines, each with its raw text and its tokens.
   Blank and comment-only lines are dropped; line numbers are preserved. *)

open Kpos

type tk =
  | ID of string
  | INT of int
  | STR of string
  | SYM of string

type tok = { tk : tk; pos : pos }

type line = { lno : int; raw : string; toks : tok list }

let tk_str = function
  | ID s -> s
  | INT n -> string_of_int n
  | STR s -> "\"" ^ s ^ "\""
  | SYM s -> s

let is_digit c = c >= '0' && c <= '9'
let is_alpha c = (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || c = '_'
let is_ident c = is_alpha c || is_digit c

let hex_val c =
  if is_digit c then Char.code c - 48
  else if c >= 'a' && c <= 'f' then Char.code c - 87
  else if c >= 'A' && c <= 'F' then Char.code c - 55
  else -1

let two_char = [ "<>"; "<="; ">="; "&&"; "||" ]
let one_char = "{}()|,;:=<>+-*/%@"

(* strip a trailing `# ...` comment (no strings contain '#' in this format) *)
let strip_comment (s : string) : string =
  match String.index_opt s '#' with
  | Some i -> String.sub s 0 i
  | None -> s

(* `cite` lines are free text (provenance): lex the keyword only *)
let cite_line (s : string) : bool =
  let t = String.trim s in
  let n = String.length t in
  n >= 4 && String.sub t 0 4 = "cite" && (n = 4 || t.[4] = ' ' || t.[4] = '\t')

let lex_line (file : string) (lno : int) (raw : string) : tok list =
  let s = strip_comment raw in
  if cite_line s then begin
    let i = ref 0 in
    while !i < String.length s && (s.[!i] = ' ' || s.[!i] = '\t') do incr i done;
    [ { tk = ID "cite"; pos = { file; line = lno; col = !i + 1 } } ]
  end else
  let n = String.length s in
  let out = ref [] in
  let i = ref 0 in
  while !i < n do
    let c = s.[!i] in
    let at = { file; line = lno; col = !i + 1 } in
    if c = ' ' || c = '\t' || c = '\r' then incr i
    else if is_alpha c then begin
      let j = ref !i in
      while !j < n && is_ident s.[!j] do incr j done;
      out := { tk = ID (String.sub s !i (!j - !i)); pos = at } :: !out;
      i := !j
    end
    else if is_digit c then begin
      if c = '0' && !i + 1 < n && (s.[!i + 1] = 'x' || s.[!i + 1] = 'X') then begin
        let j = ref (!i + 2) in
        let v = ref 0 in
        if !j >= n || hex_val s.[!j] < 0 then fail at "malformed hexadecimal literal";
        while !j < n && hex_val s.[!j] >= 0 do
          v := (!v * 16) + hex_val s.[!j];
          incr j
        done;
        out := { tk = INT !v; pos = at } :: !out;
        i := !j
      end else begin
        let j = ref !i in
        let v = ref 0 in
        while !j < n && is_digit s.[!j] do
          v := (!v * 10) + (Char.code s.[!j] - 48);
          incr j
        done;
        out := { tk = INT !v; pos = at } :: !out;
        i := !j
      end
    end
    else if c = '"' then begin
      let j = ref (!i + 1) in
      while !j < n && s.[!j] <> '"' do incr j done;
      if !j >= n then fail at "unterminated string literal";
      out := { tk = STR (String.sub s (!i + 1) (!j - !i - 1)); pos = at } :: !out;
      i := !j + 1
    end
    else begin
      let two = if !i + 1 < n then String.sub s !i 2 else "" in
      if List.mem two two_char then begin
        out := { tk = SYM two; pos = at } :: !out;
        i := !i + 2
      end else if String.contains one_char c then begin
        out := { tk = SYM (String.make 1 c); pos = at } :: !out;
        incr i
      end else fail at "unexpected character %C" c
    end
  done;
  List.rev !out

let read_lines (file : string) : string list =
  let ic = open_in_bin file in
  let out = ref [] in
  (try
     while true do
       out := input_line ic :: !out
     done
   with End_of_file -> ());
  close_in ic;
  List.rev !out

let lex_file (file : string) : line list =
  let raws = read_lines file in
  register_source file raws;
  let lines = ref [] in
  List.iteri
    (fun idx raw ->
      let lno = idx + 1 in
      let toks = lex_line file lno raw in
      if toks <> [] then lines := { lno; raw; toks } :: !lines)
    raws;
  List.rev !lines
