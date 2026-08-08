(* The Ebpf.Ast reference table.

   This is the one place specgen's own knowledge of the AST is load-bearing
   (DESIGN.md section 7): meta-checks K1 and K9 validate the spec against it.
   It is transcribed from fstar/Ebpf.Ast.fst and kept honest by `specgen
   astcheck`, which re-extracts the constructor names from that file and
   diffs them against this table (see spec/DESIGN.md section 4, K1). *)

type argkind =
  | KEnum of string        (* an enum-typed argument: generates form axes *)
  | KDst                   (* dst:reg  - the written register *)
  | KSrcReg                (* src:reg  *)
  | KSrcOperand            (* src:operand = OpReg reg | OpImm i32 *)

type ctor = { ct_name : string; ct_args : argkind list }

type refenum = {
  re_name : string;
  re_spec_cases : string list;   (* the names the .kspec must declare *)
  re_ast_cases : string list;    (* the constructor names in Ebpf.Ast.fst *)
  re_ast_type : string;          (* the F* type they belong to *)
}

(* fstar/Ebpf.Ast.fst:15-49 *)
let enums = [
  { re_name = "width";     re_ast_type = "width";
    re_spec_cases = ["W32"; "W64"];
    re_ast_cases  = ["W32"; "W64"] };
  { re_name = "alu_op";    re_ast_type = "alu_op";
    re_spec_cases = ["ADD";"SUB";"MUL";"DIV";"SDIV";"MOD";"SMOD";
                     "AND";"OR";"XOR";"LSH";"RSH";"ARSH"];
    re_ast_cases  = ["ADD";"SUB";"MUL";"DIV";"SDIV";"MOD";"SMOD";
                     "AND";"OR";"XOR";"LSH";"RSH";"ARSH"] };
  (* the two cases of Ebpf.Ast.operand; the .kspec names them by their
     form ("reg"/"imm") because they are a form axis, not a value *)
  { re_name = "operand";   re_ast_type = "operand";
    re_spec_cases = ["reg"; "imm"];
    re_ast_cases  = ["OpReg"; "OpImm"] };
  { re_name = "movsx_sz";  re_ast_type = "movsx_sz";
    re_spec_cases = ["SX8"; "SX16"; "SX32"];
    re_ast_cases  = ["SX8"; "SX16"; "SX32"] };
  { re_name = "swap_kind"; re_ast_type = "swap_kind";
    re_spec_cases = ["ToLE"; "ToBE"; "Bswap"];
    re_ast_cases  = ["ToLE"; "ToBE"; "Bswap"] };
  { re_name = "swap_sz";   re_ast_type = "swap_sz";
    re_spec_cases = ["SW16"; "SW32"; "SW64"];
    re_ast_cases  = ["SW16"; "SW32"; "SW64"] };
]

(* the real instructions - every one of these must be claimed by exactly one
   family, and covered exhaustively (K9) *)
let ctors = [
  { ct_name = "Alu";   ct_args = [KEnum "width"; KEnum "alu_op"; KDst; KSrcOperand] };
  { ct_name = "Neg";   ct_args = [KEnum "width"; KDst] };
  { ct_name = "Mov";   ct_args = [KEnum "width"; KDst; KSrcOperand] };
  { ct_name = "MovSX"; ct_args = [KEnum "width"; KEnum "movsx_sz"; KDst; KSrcReg] };
  { ct_name = "Swap";  ct_args = [KEnum "swap_kind"; KEnum "swap_sz"; KDst] };
]

(* pseudo / terminal: NOT machine arithmetic, must not appear in a spec *)
let pseudo = ["Assert_"; "Exit"]

let find_enum n = List.find_opt (fun e -> e.re_name = n) enums
let find_ctor n = List.find_opt (fun c -> c.ct_name = n) ctors

let enum_of_argkind = function KEnum n -> Some n | _ -> None

(* Enums whose Ebpf.Ast constructors CARRY A VALUE, so a match pattern needs
   an argument: `OpReg _`, not `OpReg`.  (fstar/Ebpf.Ast.fst:28-30 - the
   `operand` axis is the only one in this fragment.) *)
let valued = [ "operand" ]

(* The F* match pattern for a spec case name: its Ebpf.Ast constructor
   (the .kspec spells the `operand` axis `reg`/`imm` because it is a form
   axis, but F* matches on `OpReg`/`OpImm`), plus `_` when that constructor
   carries a value.  The F* backend prints patterns through here so the
   spec-vs-AST spelling correspondence stays in this one file. *)
let ast_pattern (en : string) (case : string) : string =
  let ctor =
    match find_enum en with
    | None -> case
    | Some e ->
      let rec go spec ast =
        match (spec, ast) with
        | s :: _, a :: _ when s = case -> a
        | _ :: st, _ :: at -> go st at
        | _ -> case
      in
      go e.re_spec_cases e.re_ast_cases
  in
  if List.mem en valued then ctor ^ " _" else ctor

let ctor_list_str () =
  "[" ^ String.concat "; " (List.map (fun c -> c.ct_name) ctors) ^ "]"

let pseudo_list_str () = String.concat ", " pseudo

(* ------------------------------------------------------------------ *)
(* drift check: re-extract the constructors from fstar/Ebpf.Ast.fst     *)
(* ------------------------------------------------------------------ *)

(* Deliberately NOT an F* parser: we scan for `type <name>` and collect the
   identifier following each `|` until the type declaration ends. *)

let strip_line_comments (s : string) : string =
  (* drop (* ... *) occurring entirely within the line *)
  let b = Buffer.create (String.length s) in
  let n = String.length s in
  let depth = ref 0 in
  let i = ref 0 in
  while !i < n do
    if !i + 1 < n && s.[!i] = '(' && s.[!i + 1] = '*' then (incr depth; i := !i + 2)
    else if !i + 1 < n && s.[!i] = '*' && s.[!i + 1] = ')' && !depth > 0 then
      (decr depth; i := !i + 2)
    else begin
      if !depth = 0 then Buffer.add_char b s.[!i];
      incr i
    end
  done;
  Buffer.contents b

let trim = String.trim

let starts_with p s =
  String.length s >= String.length p && String.sub s 0 (String.length p) = p

let ident_at (s : string) (i : int) : string =
  let n = String.length s in
  let j = ref i in
  while !j < n && (Lex.is_ident s.[!j]) do incr j done;
  String.sub s i (!j - i)

(* all identifiers that immediately follow a '|' in the line *)
let cases_of_line (s : string) : string list =
  let n = String.length s in
  let out = ref [] in
  let i = ref 0 in
  while !i < n do
    if s.[!i] = '|' then begin
      let j = ref (!i + 1) in
      while !j < n && (s.[!j] = ' ' || s.[!j] = '\t') do incr j done;
      if !j < n && Lex.is_alpha s.[!j] then out := ident_at s !j :: !out;
      i := !j
    end else incr i
  done;
  List.rev !out

(* type name -> constructor names, for every `type` declaration in the file *)
let scan_ast_file (file : string) : (string * string list) list =
  let lines = Lex.read_lines file in
  let acc = ref [] in
  let cur = ref None in
  let flush () =
    match !cur with
    | Some (name, cases) -> acc := (name, List.rev cases) :: !acc; cur := None
    | None -> ()
  in
  List.iter
    (fun raw ->
      let s = strip_line_comments raw in
      let t = trim s in
      if starts_with "type " t then begin
        flush ();
        let rest = String.sub t 5 (String.length t - 5) in
        let name = ident_at rest 0 in
        cur := Some (name, List.rev (cases_of_line t))
      end
      else if t = "" then flush ()
      else
        match !cur with
        | Some (name, cases) ->
          let cs = cases_of_line t in
          if cs <> [] then cur := Some (name, List.rev_append cs cases)
          else if starts_with "let " t || starts_with "module " t then flush ()
        | None -> ())
    lines;
  flush ();
  List.rev !acc

type drift = { d_type : string; d_only_spec : string list; d_only_ast : string list;
               d_order : bool }

(* directional, itemized (DESIGN.md section 4 / MS5 drift replay) *)
let drift_check (file : string) : drift list =
  let scanned = scan_ast_file file in
  let get t = try Some (List.assoc t scanned) with Not_found -> None in
  let diff want got =
    let only_a = List.filter (fun x -> not (List.mem x got)) want in
    let only_b = List.filter (fun x -> not (List.mem x want)) got in
    (only_a, only_b)
  in
  let checks =
    List.map (fun e -> (e.re_ast_type, e.re_ast_cases)) enums
    @ [ ("insn", List.map (fun c -> c.ct_name) ctors @ pseudo) ]
  in
  List.filter_map
    (fun (tname, want) ->
      match get tname with
      | None ->
        Some { d_type = tname; d_only_spec = want; d_only_ast = []; d_order = false }
      | Some got ->
        let only_spec, only_ast = diff want got in
        let order = only_spec = [] && only_ast = [] && want <> got in
        if only_spec = [] && only_ast = [] && not order then None
        else Some { d_type = tname; d_only_spec = only_spec; d_only_ast = only_ast;
                    d_order = order })
    checks
