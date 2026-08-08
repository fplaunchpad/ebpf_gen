(* Hand-rolled recursive-descent parser for .kspec -> surface syntax tree.

   The file is line-structured: `spec`/`family` open a brace block, `enum` is
   a single line, and inside a family every line is either a header line
   (first token is a family keyword) or a pipe-separated table row. *)

open Kpos
open Lex

(* ---------------- surface syntax tree ---------------- *)

type sexpr =
  | SLit of int * pos
  | SVar of string * pos
  | SArith of string * sexpr * sexpr * pos
  | SApp of string * sexpr list * pos
  | SIf of scond * sexpr * sexpr * pos

and scond =
  | SCTrue of pos
  | SCCmp of string * sexpr * sexpr * pos
  | SCAnd of scond * scond * pos
  | SCOr of scond * scond * pos
  | SCNot of scond * pos

type sty = STBits of sexpr * pos | STInt of pos

type sctorarg =
  | SCAxis of string * pos            (* an axis variable *)
  | SCRole of string * string * pos   (* name : reg | operand *)

type ssemsig = {
  ss_widths : (string * pos) list;
  ss_vals : (string * string * sexpr * pos) list;  (* var, role, read width *)
  ss_res : sty;
  ss_pos : pos;
}

type sdefsig = {
  ds_widths : (string * pos) list;
  ds_vals : (string * pos) list;
  ds_pos : pos;
}

type sfield = SFInt of int * pos | SFRef of string * pos | SFAny of pos

type srow = {
  rw_name : string;
  rw_pos : pos;
  rw_cells : (tok list * pos) list;   (* one per column after `name` *)
}

type sfamily = {
  fs_name : string;
  fs_pos : pos;
  mutable fs_ctor : (string * sctorarg list * pos) option;
  mutable fs_key : (string * string * pos) option;
  mutable fs_axes : (string * string * pos) list;
  mutable fs_widths : (string * string * pos) list;   (* wvar, axis *)
  mutable fs_sem : ssemsig option;
  mutable fs_def : sdefsig option;
  mutable fs_valid : (scond * pos) option;
  mutable fs_excl : ((string * string * pos) list * string * pos) list;
  mutable fs_enc : (string * sfield * pos) list;
  mutable fs_cites : string list;
  mutable fs_cols : (string * pos) list option;
  mutable fs_cols_pos : pos;
  mutable fs_rows : srow list;
}

type senum = {
  se_name : string;
  se_pos : pos;
  se_cases : (string * (string * int) list * pos) list;
}

type sspec = {
  sp_name : string;
  sp_version : int;
  sp_isa : string;
  sp_host : string;
  sp_pos : pos;
}

type sfile = {
  sf_spec : sspec option;
  sf_enums : senum list;
  sf_families : sfamily list;
}

(* ---------------- token cursor ---------------- *)

type cur = { mutable ts : tok list; mutable last : pos }

let mk_cur toks p = { ts = toks; last = p }
let cpos c = match c.ts with [] -> c.last | t :: _ -> t.pos
let peek c = match c.ts with [] -> None | t :: _ -> Some t
let advance c = match c.ts with [] -> () | t :: r -> c.ts <- r; c.last <- t.pos
let next c =
  match c.ts with
  | [] -> fail c.last "unexpected end of line"
  | t :: r -> c.ts <- r; c.last <- t.pos; t
let at_sym c s = match peek c with Some { tk = SYM x; _ } -> x = s | _ -> false
let at_id c s = match peek c with Some { tk = ID x; _ } -> x = s | _ -> false
let eof c = c.ts = []

let eat_sym c s =
  if at_sym c s then advance c else fail (cpos c) "expected `%s`" s

let eat_id c s =
  if at_id c s then advance c else fail (cpos c) "expected `%s`" s

let want_id c =
  match next c with
  | { tk = ID x; pos } -> (x, pos)
  | t -> fail t.pos "expected an identifier, found `%s`" (tk_str t.tk)

let want_int c =
  match next c with
  | { tk = INT n; pos } -> (n, pos)
  | t -> fail t.pos "expected an integer, found `%s`" (tk_str t.tk)

let want_str c =
  match next c with
  | { tk = STR s; pos } -> (s, pos)
  | t -> fail t.pos "expected a quoted string, found `%s`" (tk_str t.tk)

let done_or_fail c what =
  if not (eof c) then
    fail (cpos c) "unexpected `%s` after %s" (tk_str (List.hd c.ts).tk) what

(* split a token list on a top-level symbol (parenthesis-aware) *)
let split_on (sym : string) (toks : tok list) : tok list list =
  let out = ref [] and cur = ref [] and depth = ref 0 in
  List.iter
    (fun t ->
      match t.tk with
      | SYM "(" -> incr depth; cur := t :: !cur
      | SYM ")" -> decr depth; cur := t :: !cur
      | SYM s when s = sym && !depth = 0 ->
        out := List.rev !cur :: !out; cur := []
      | _ -> cur := t :: !cur)
    toks;
  out := List.rev !cur :: !out;
  List.rev !out

let has_sym (sym : string) (toks : tok list) =
  List.exists (fun t -> match t.tk with SYM s -> s = sym | _ -> false) toks

(* ---------------- expressions ---------------- *)

let is_comb name = Il.comb_of_string name <> None

let known_combs =
  String.concat ", "
    [ "wrap"; "low"; "sval"; "sext"; "bswap"; "pow2"; "trunc_div"; "trunc_mod";
      "logand"; "logor"; "logxor" ]

let rec p_expr (c : cur) : sexpr =
  match peek c with
  | Some { tk = ID "if"; pos } ->
    advance c;
    let cnd = p_cond c in
    eat_id c "then";
    let a = p_expr c in
    eat_id c "else";
    let b = p_expr c in
    SIf (cnd, a, b, pos)
  | _ -> p_add c

and p_add c =
  let l = ref (p_mul c) in
  let rec loop () =
    match peek c with
    | Some { tk = SYM (("+" | "-") as o); pos } ->
      advance c;
      let r = p_mul c in
      l := SArith (o, !l, r, pos);
      loop ()
    | _ -> ()
  in
  loop (); !l

and p_mul c =
  let l = ref (p_app c) in
  let rec loop () =
    match peek c with
    | Some { tk = SYM (("*" | "/" | "%") as o); pos } ->
      advance c;
      let r = p_app c in
      l := SArith (o, !l, r, pos);
      loop ()
    | _ -> ()
  in
  loop (); !l

and p_app c =
  match peek c with
  | Some { tk = ID name; pos } when is_comb name ->
    advance c;
    let nw, nv = Il.comb_arity (Option.get (Il.comb_of_string name)) in
    let args = List.init (nw + nv) (fun _ -> p_atom c) in
    SApp (name, args, pos)
  | Some { tk = ID name; pos } when applied c ->
    (* an identifier followed by an argument: an application of something
       that is not in the combinator table (K3) *)
    fail pos
      "[K3] unknown combinator `%s`; the semantics language has exactly: %s"
      name known_combs
  | _ -> p_atom c

(* does an argument-looking token follow the head identifier? *)
and applied c =
  match c.ts with
  | _ :: { tk = INT _; _ } :: _ -> true
  | _ :: { tk = SYM "("; _ } :: _ -> true
  | _ :: { tk = ID x; _ } :: _ ->
    not (List.mem x [ "then"; "else"; "true"; "not" ])
  | _ -> false

and p_atom c =
  match next c with
  | { tk = INT n; pos } -> SLit (n, pos)
  | { tk = ID x; pos } ->
    if is_comb x then fail pos "combinator `%s` used without its arguments" x
    else SVar (x, pos)
  | { tk = SYM "("; pos } ->
    let e = p_expr c in
    eat_sym c ")";
    e
  | t -> fail t.pos "expected an expression, found `%s`" (tk_str t.tk)

and p_cond c : scond = p_or c

and p_or c =
  let l = ref (p_and c) in
  let rec loop () =
    match peek c with
    | Some { tk = SYM "||"; pos } ->
      advance c;
      let r = p_and c in
      l := SCOr (!l, r, pos);
      loop ()
    | _ -> ()
  in
  loop (); !l

and p_and c =
  let l = ref (p_not c) in
  let rec loop () =
    match peek c with
    | Some { tk = SYM "&&"; pos } ->
      advance c;
      let r = p_not c in
      l := SCAnd (!l, r, pos);
      loop ()
    | _ -> ()
  in
  loop (); !l

and p_not c =
  match peek c with
  | Some { tk = ID "not"; pos } -> advance c; SCNot (p_not c, pos)
  | Some { tk = ID "true"; pos } when List.length c.ts = 1 -> advance c; SCTrue pos
  | Some { tk = SYM "("; _ } ->
    (* a parenthesised condition, if it parses as one; otherwise a comparison *)
    let save = c.ts and saved_last = c.last in
    (try
       advance c;
       let inner = p_cond c in
       eat_sym c ")";
       inner
     with Kerr _ -> c.ts <- save; c.last <- saved_last; p_cmp c)
  | _ -> p_cmp c

and p_cmp c =
  let a = p_expr c in
  match peek c with
  | Some { tk = SYM (("=" | "<>" | "<" | "<=" | ">" | ">=") as o); pos } ->
    advance c;
    let b = p_expr c in
    SCCmp (o, a, b, pos)
  | _ ->
    (match a with
     | SVar ("true", pos) -> SCTrue pos
     | _ -> fail (cpos c) "expected a comparison operator (=, <>, <, <=, >, >=)")

let parse_expr_toks (toks : tok list) (p : pos) : sexpr =
  let c = mk_cur toks p in
  if eof c then fail p "empty expression";
  let e = p_expr c in
  done_or_fail c "the expression";
  e

let parse_cond_toks (toks : tok list) (p : pos) : scond =
  let c = mk_cur toks p in
  if eof c then fail p "empty condition";
  let e = p_cond c in
  done_or_fail c "the condition";
  e

(* ---------------- header lines ---------------- *)

let keywords =
  ["ctor"; "key"; "axis"; "width"; "sem"; "defined"; "valid"; "exclude";
   "enc"; "cite"; "cols"]

let p_ty (c : cur) : sty =
  match peek c with
  | Some { tk = ID "int"; pos } -> advance c; STInt pos
  | Some { tk = ID "bits"; pos } -> advance c; STBits (p_atom c, pos)
  | _ -> fail (cpos c) "expected a type (`bits <width>` or `int`)"

(* `( n ; d = dst @ n , s = src @ n ) : bits n` *)
let p_semsig (c : cur) (kw : pos) : ssemsig =
  eat_sym c "(";
  (* collect up to the matching ')' *)
  let inner = ref [] and depth = ref 0 and fin = ref false in
  while not !fin do
    let t = next c in
    (match t.tk with
     | SYM "(" -> incr depth; inner := t :: !inner
     | SYM ")" when !depth = 0 -> fin := true
     | SYM ")" -> decr depth; inner := t :: !inner
     | _ -> inner := t :: !inner)
  done;
  let inner = List.rev !inner in
  let ws, vs =
    match split_on ";" inner with
    | [ only ] -> (only, [])
    | [ a; b ] -> (a, b)
    | _ -> fail kw "a signature has at most one `;` (width params ; value params)"
  in
  let widths =
    List.filter_map
      (fun g ->
        if g = [] then None
        else
          let cc = mk_cur g kw in
          let n, p = want_id cc in
          done_or_fail cc "a width parameter";
          Some (n, p))
      (split_on "," ws)
  in
  let vals =
    List.filter_map
      (fun g ->
        if g = [] then None
        else
          let cc = mk_cur g kw in
          let v, p = want_id cc in
          eat_sym cc "=";
          let role, _ = want_id cc in
          eat_sym cc "@";
          let w = p_atom cc in
          done_or_fail cc "a value parameter";
          Some (v, role, w, p))
      (split_on "," vs)
  in
  eat_sym c ":";
  let res = p_ty c in
  done_or_fail c "the `sem` signature";
  { ss_widths = widths; ss_vals = vals; ss_res = res; ss_pos = kw }

let p_defsig (c : cur) (kw : pos) : sdefsig =
  eat_sym c "(";
  let inner = ref [] and fin = ref false in
  while not !fin do
    let t = next c in
    match t.tk with SYM ")" -> fin := true | _ -> inner := t :: !inner
  done;
  let inner = List.rev !inner in
  let ws, vs =
    match split_on ";" inner with
    | [ only ] -> (only, [])
    | [ a; b ] -> (a, b)
    | _ -> fail kw "a signature has at most one `;`"
  in
  let idents g =
    List.filter_map
      (fun grp ->
        if grp = [] then None
        else
          let cc = mk_cur grp kw in
          let n, p = want_id cc in
          done_or_fail cc "a parameter";
          Some (n, p))
      (split_on "," g)
  in
  done_or_fail c "the `defined` signature";
  { ds_widths = idents ws; ds_vals = idents vs; ds_pos = kw }

let p_field (c : cur) : sfield =
  match next c with
  | { tk = INT n; pos } -> SFInt (n, pos)
  | { tk = ID x; pos } -> SFRef (x, pos)
  | { tk = SYM "*"; pos } -> SFAny pos
  | t -> fail t.pos "expected an encoding value (integer, axis/width name, or `*`)"

let cite_text (raw : string) : string =
  let s = Lex.strip_comment raw in
  let s = String.trim s in
  (* drop the leading "cite" keyword *)
  let s = String.sub s 4 (String.length s - 4) in
  String.trim s

let p_family_line (fam : sfamily) (ln : line) : unit =
  let first = List.hd ln.toks in
  let kw = match first.tk with ID x -> x | _ -> "" in
  if List.mem kw keywords then begin
    let c = mk_cur (List.tl ln.toks) first.pos in
    match kw with
    | "ctor" ->
      let name, p = want_id c in
      eat_sym c "(";
      let args = ref [] in
      if not (at_sym c ")") then begin
        let fin = ref false in
        while not !fin do
          let a, ap = want_id c in
          if at_sym c ":" then begin
            advance c;
            let k, _ = want_id c in
            args := SCRole (a, k, ap) :: !args
          end else args := SCAxis (a, ap) :: !args;
          if at_sym c "," then advance c else fin := true
        done
      end;
      eat_sym c ")";
      done_or_fail c "the `ctor` declaration";
      if fam.fs_ctor <> None then fail p "duplicate `ctor` declaration";
      fam.fs_ctor <- Some (name, List.rev !args, p)
    | "key" ->
      let v, p = want_id c in
      eat_sym c ":";
      let e, _ = want_id c in
      done_or_fail c "the `key` declaration";
      if fam.fs_key <> None then fail p "duplicate `key` declaration";
      fam.fs_key <- Some (v, e, p)
    | "axis" ->
      List.iter
        (fun g ->
          let cc = mk_cur g first.pos in
          let v, p = want_id cc in
          eat_sym cc ":";
          let e, _ = want_id cc in
          done_or_fail cc "an `axis` declaration";
          fam.fs_axes <- fam.fs_axes @ [ (v, e, p) ])
        (split_on "," c.ts)
    | "width" ->
      List.iter
        (fun g ->
          let cc = mk_cur g first.pos in
          let v, p = want_id cc in
          eat_sym cc "=";
          eat_id cc "bits";
          let ax, _ = want_id cc in
          done_or_fail cc "a `width` binding";
          fam.fs_widths <- fam.fs_widths @ [ (v, ax, p) ])
        (split_on "," c.ts)
    | "sem" ->
      if fam.fs_sem <> None then fail first.pos "duplicate `sem` signature";
      fam.fs_sem <- Some (p_semsig c first.pos)
    | "defined" ->
      if fam.fs_def <> None then fail first.pos "duplicate `defined` signature";
      fam.fs_def <- Some (p_defsig c first.pos)
    | "valid" ->
      if fam.fs_valid <> None then fail first.pos "duplicate `valid` clause";
      fam.fs_valid <- Some (parse_cond_toks c.ts first.pos, first.pos)
    | "exclude" ->
      let binds = ref [] and reason = ref "" in
      let fin = ref false in
      while not !fin do
        let a, ap = want_id c in
        eat_sym c "=";
        let v, _ = want_id c in
        binds := (a, v, ap) :: !binds;
        if at_sym c "," then advance c else fin := true
      done;
      (match peek c with
       | Some { tk = STR s; _ } -> advance c; reason := s
       | _ -> fail (cpos c) "an `exclude` needs a quoted reason");
      done_or_fail c "the `exclude` declaration";
      fam.fs_excl <- fam.fs_excl @ [ (List.rev !binds, !reason, first.pos) ]
    | "enc" ->
      List.iter
        (fun g ->
          let cc = mk_cur g first.pos in
          let f, p = want_id cc in
          eat_sym cc "=";
          let v = p_field cc in
          done_or_fail cc "an `enc` assignment";
          fam.fs_enc <- fam.fs_enc @ [ (f, v, p) ])
        (split_on "," c.ts)
    | "cite" -> fam.fs_cites <- fam.fs_cites @ [ cite_text ln.raw ]
    | "cols" ->
      if fam.fs_cols <> None then fail first.pos "duplicate `cols` declaration";
      let cols =
        List.map
          (fun g ->
            let cc = mk_cur g first.pos in
            let n, p = want_id cc in
            done_or_fail cc "a column name";
            (n, p))
          (split_on "|" c.ts)
      in
      fam.fs_cols <- Some cols;
      fam.fs_cols_pos <- first.pos
    | _ -> assert false
  end
  else if has_sym "|" ln.toks then begin
    let groups = split_on "|" ln.toks in
    match groups with
    | [] -> fail first.pos "malformed table row"
    | name_g :: cells ->
      let cc = mk_cur name_g first.pos in
      let nm, p = want_id cc in
      done_or_fail cc "the entry name";
      let cells =
        List.map
          (fun g ->
            let cp = match g with t :: _ -> t.pos | [] -> first.pos in
            (g, cp))
          cells
      in
      fam.fs_rows <- fam.fs_rows @ [ { rw_name = nm; rw_pos = p; rw_cells = cells } ]
  end
  else
    fail first.pos
      "not a family header keyword and not a table row (rows contain `|`); \
       keywords are: %s"
      (String.concat ", " keywords)

let p_enum (ln : line) : senum =
  let c = mk_cur (List.tl ln.toks) (List.hd ln.toks).pos in
  let name, p = want_id c in
  eat_sym c "{";
  let body = ref [] and fin = ref false in
  while not !fin do
    let t = next c in
    match t.tk with SYM "}" -> fin := true | _ -> body := t :: !body
  done;
  done_or_fail c "the enum declaration";
  let cases =
    List.filter_map
      (fun g ->
        if g = [] then None
        else
          let cc = mk_cur g p in
          let cn, cp = want_id cc in
          let attrs = ref [] in
          if at_sym cc ":" then begin
            advance cc;
            while not (eof cc) do
              let a, ap = want_id cc in
              eat_sym cc "=";
              let v, _ = want_int cc in
              if List.mem_assoc a !attrs then fail ap "duplicate attribute `%s`" a;
              attrs := (a, v) :: !attrs
            done
          end;
          done_or_fail cc "an enum case";
          Some (cn, List.rev !attrs, cp))
      (split_on ";" (List.rev !body))
  in
  { se_name = name; se_pos = p; se_cases = cases }

let p_spec (lines : line list) (p : pos) : sspec =
  let name = ref "" and version = ref (-1) and isa = ref "" and host = ref "" in
  List.iter
    (fun ln ->
      let first = List.hd ln.toks in
      let c = mk_cur (List.tl ln.toks) first.pos in
      match first.tk with
      | ID "version" -> let v, _ = want_int c in version := v; done_or_fail c "`version`"
      | ID "isa" -> let s, _ = want_str c in isa := s; done_or_fail c "`isa`"
      | ID "host" ->
        let h, hp = want_id c in
        let h = if at_sym c "-" then (advance c; let h2, _ = want_id c in h ^ "-" ^ h2) else h in
        if h <> "little-endian" && h <> "big-endian" then
          fail hp "`host` must be little-endian or big-endian";
        host := h;
        done_or_fail c "`host`"
      | ID k -> fail first.pos "unknown `spec` key `%s`" k
      | _ -> fail first.pos "malformed `spec` entry")
    lines;
  if !version < 0 then fail p "`spec` block is missing `version`";
  if !isa = "" then fail p "`spec` block is missing `isa`";
  if !host = "" then fail p "`spec` block is missing `host`";
  { sp_name = !name; sp_version = !version; sp_isa = !isa; sp_host = !host; sp_pos = p }

(* ---------------- file ---------------- *)

let parse_file (file : string) : sfile =
  let lines = lex_file file in
  let enums = ref [] and fams = ref [] and spec = ref None in
  let rec go = function
    | [] -> ()
    | ln :: rest ->
      let first = List.hd ln.toks in
      let last = List.nth ln.toks (List.length ln.toks - 1) in
      let opens_block = match last.tk with SYM "{" -> true | _ -> false in
      (match first.tk with
       | ID "enum" -> enums := p_enum ln :: !enums; go rest
       | ID "spec" when opens_block ->
         let c = mk_cur (List.tl ln.toks) first.pos in
         let name, _ = want_id c in
         let body, rest' = take_block rest in
         let s = p_spec body first.pos in
         if !spec <> None then fail first.pos "duplicate `spec` block";
         spec := Some { s with sp_name = name };
         go rest'
       | ID "family" when opens_block ->
         let c = mk_cur (List.tl ln.toks) first.pos in
         let name, np = want_id c in
         let body, rest' = take_block rest in
         let fam =
           { fs_name = name; fs_pos = np; fs_ctor = None; fs_key = None;
             fs_axes = []; fs_widths = []; fs_sem = None; fs_def = None;
             fs_valid = None; fs_excl = []; fs_enc = []; fs_cites = [];
             fs_cols = None; fs_cols_pos = np; fs_rows = [] }
         in
         List.iter (p_family_line fam) body;
         fams := fam :: !fams;
         go rest'
       | ID k -> fail first.pos "unexpected `%s` at top level (expected spec, enum or family)" k
       | _ -> fail first.pos "unexpected token at top level")
  and take_block lines =
    let rec loop acc = function
      | [] -> fail nowhere "unterminated block: missing `}`"
      | ln :: rest ->
        (match ln.toks with
         | [ { tk = SYM "}"; _ } ] -> (List.rev acc, rest)
         | _ -> loop (ln :: acc) rest)
    in
    loop [] lines
  in
  go lines;
  { sf_spec = !spec; sf_enums = List.rev !enums; sf_families = List.rev !fams }
