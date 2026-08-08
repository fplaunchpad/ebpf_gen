(* emit_prose.ml — the PROSE backend.  Consumes `Il.spec` (`s_instances` +
   `s_families` + the `cite` provenance) and renders an RFC-9669-style
   English reference for the fragment.

   The rule this file obeys, and the reason the artifact is worth having:

     NO SENTENCE ABOUT A PARTICULAR INSTRUCTION IS WRITTEN HERE.

   Every instruction-specific statement is a structural rendering of that
   instruction's `sem` / `defined` AST, its `enc` record, its `i_obligs` and
   its `cite` lines.  The only English in this file is (a) one template per
   AST *node kind* (the two rendering tables below, which §1.2 of the output
   prints by running them on sample terms, so the documented table cannot
   drift from the renderer), and (b) fixed scaffolding that says nothing
   instruction-specific.  Two deliberate exceptions are marked EXCEPTION and
   listed in spec/PROSE-CHECK.md.

   See spec/DESIGN.md §5 ("prose backend") for the contract. *)

open Kpos
open Il

let sprintf = Printf.sprintf
let bp = Printf.bprintf

(* ------------------------------------------------------------------ *)
(* rendering context                                                    *)
(* ------------------------------------------------------------------ *)

type ctx = {
  c_w : (string * int) list;      (* width valuation; [] = width-generic *)
  c_ps : (string * string) list;  (* sem var -> pseudocode operand name *)
  c_en : (string * string) list;  (* sem var -> English noun phrase *)
}

let ctx0 = { c_w = []; c_ps = []; c_en = [] }

let rec w_val ctx = function
  | WLit n -> Some n
  | WVar v -> List.assoc_opt v ctx.c_w
  | WBin (o, a, b) -> (
    match (w_val ctx a, w_val ctx b) with
    | Some x, Some y -> (
      match o with
      | Add -> Some (x + y)
      | Sub -> Some (x - y)
      | Mul -> Some (x * y)
      | Div -> if y = 0 then None else Some (x / y)
      | Mod -> if y = 0 then None else Some (x mod y))
    | _ -> None)

(* a width renders as its number when the instance fixes it, and as the
   width variable itself in the width-generic (per-entry) view *)
let w_str ctx w = match w_val ctx w with Some n -> string_of_int n | None -> wexp_str w

let ps_var ctx v = match List.assoc_opt v ctx.c_ps with Some s -> s | None -> v
let en_var ctx v = match List.assoc_opt v ctx.c_en with Some s -> s | None -> v

(* "a 64-bit" / "an 8-bit" / "an n-bit" — English article, not semantics *)
let art (s : string) =
  if s = "" then "a"
  else
    match s.[0] with
    | '8' -> "an"
    | '1' when String.length s >= 2 && (s.[1] = '1' || s.[1] = '8') -> "an"
    | 'a' | 'e' | 'f' | 'h' | 'i' | 'l' | 'm' | 'n' | 'o' | 'r' | 's' | 'x' | 'A' | 'E' | 'F'
    | 'H' | 'I' | 'L' | 'M' | 'N' | 'O' | 'R' | 'S' | 'X' ->
      "an"
    | _ -> "a"

(* a rendered phrase that already contains a comma is bracketed when it
   becomes the argument of another phrase, so the modifiers do not run on *)
let group (s : string) = if String.contains s ',' then "(" ^ s ^ ")" else s

(* The same syntactic sign analysis K5 uses to discharge `pow2`'s
   non-negativity (DESIGN.md §4): everything is a bit pattern, a width, or a
   sum/product/quotient of those — hence non-negative — unless a subtraction,
   a signed reading, or a truncated division put a sign on it.  It selects
   between the two renderings of `/`, `%` and `wrap`. *)
let rec may_neg = function
  | ELit (n, _) -> n < 0
  | EVar _ -> false
  | EWidth _ -> false
  | EArith (Sub, _, _, _) -> true
  | EArith (_, a, b, _) -> may_neg a || may_neg b
  | EComb (Sval, _, _, _) | EComb (TruncDiv, _, _, _) | EComb (TruncMod, _, _, _) -> true
  | EComb _ -> false
  | EIf (_, a, b, _) -> may_neg a || may_neg b

(* ------------------------------------------------------------------ *)
(* RENDERING TABLE 1 — pseudocode (the RFC "description column" style)  *)
(*                                                                      *)
(*   INT             k                    a decimal numeral             *)
(*   var             dst / src / imm      the operand it reads          *)
(*   width var       64                   its value at this instance    *)
(*   a OP b          (a OP b)             always parenthesised          *)
(*   wrap W e        (e mod 2^W)          truncation is never implicit  *)
(*   low W e         (e mod 2^W)          same function (Ebpf.Int)      *)
(*   sval W e        signedW(e)                                         *)
(*   sext F N e      sext(F, N, e)                                      *)
(*   bswap NB e      bswap(NB, e)                                       *)
(*   pow2 e          2^e                                                *)
(*   trunc_div a b   trunc_div(a, b)                                    *)
(*   trunc_mod a b   trunc_mod(a, b)                                    *)
(*   logand W a b    (a & b)              (logor -> |, logxor -> ^)     *)
(*   if c then a     (c) ? a : b                                        *)
(*     else b                                                           *)
(*   if a = b then   (a != b) ? y : x     NORMALISATION: the RFC states  *)
(*     x else y                            the interesting branch first *)
(* ------------------------------------------------------------------ *)

let rec ps ctx e =
  match e with
  | ELit (n, _) -> string_of_int n
  | EVar (v, _) -> ps_var ctx v
  | EWidth (w, _) -> w_str ctx w
  | EArith (o, a, b, _) -> sprintf "(%s %s %s)" (ps ctx a) (aop_str o) (ps ctx b)
  | EComb (c, ws, es, _) -> ps_comb ctx e c ws es
  | EIf (CCmp (Eq, a, b, _), x, y, _) ->
    sprintf "(%s != %s) ? %s : %s" (ps ctx a) (ps ctx b) (ps ctx y) (ps ctx x)
  | EIf (c, x, y, _) -> sprintf "(%s) ? %s : %s" (ps_cond ctx c) (ps ctx x) (ps ctx y)

and ps_comb ctx e c ws es =
  let w i = w_str ctx (List.nth ws i) and a i = ps ctx (List.nth es i) in
  match (c, List.length ws, List.length es) with
  | (Wrap | Low), 1, 1 -> sprintf "(%s mod 2^%s)" (a 0) (w 0)
  | Sval, 1, 1 -> sprintf "signed%s(%s)" (w 0) (a 0)
  | Sext, 2, 1 -> sprintf "sext(%s, %s, %s)" (w 0) (w 1) (a 0)
  | Bswap, 1, 1 -> sprintf "bswap(%s, %s)" (w 0) (a 0)
  | Pow2, 0, 1 -> sprintf "2^%s" (a 0)
  | TruncDiv, 0, 2 -> sprintf "trunc_div(%s, %s)" (a 0) (a 1)
  | TruncMod, 0, 2 -> sprintf "trunc_mod(%s, %s)" (a 0) (a 1)
  | Logand, 1, 2 -> sprintf "(%s & %s)" (a 0) (a 1)
  | Logor, 1, 2 -> sprintf "(%s | %s)" (a 0) (a 1)
  | Logxor, 1, 2 -> sprintf "(%s ^ %s)" (a 0) (a 1)
  | _ -> expr_str e (* unreachable: K3 fixes every combinator's arity *)

and ps_cond ctx = function
  | CTrue -> "true"
  | CCmp (o, a, b, _) ->
    let op = match o with Eq -> "==" | Ne -> "!=" | _ -> cmp_str o in
    sprintf "%s %s %s" (ps ctx a) op (ps ctx b)
  | CAnd (a, b) -> sprintf "%s && %s" (ps_cond ctx a) (ps_cond ctx b)
  | COr (a, b) -> sprintf "%s || %s" (ps_cond ctx a) (ps_cond ctx b)
  | CNot a -> sprintf "!(%s)" (ps_cond ctx a)

(* ------------------------------------------------------------------ *)
(* RENDERING TABLE 2 — English                                          *)
(*                                                                      *)
(*   a + b           the sum of A and B                                 *)
(*   a - b           A minus B                                          *)
(*   a * b           the product of A and B                             *)
(*   a / b           the unsigned quotient of A divided by B            *)
(*                   ... or, when A may be negative:                    *)
(*                   the quotient of A divided by B, rounded toward     *)
(*                   negative infinity                                  *)
(*   a % b           the unsigned remainder of A divided by B           *)
(*                   ... or: the Euclidean remainder of A divided by B  *)
(*   wrap W e        E, truncated to W bits                             *)
(*                   ... or, when E may be negative:                    *)
(*                   E, reduced modulo 2^W (two's-complement wrap)      *)
(*   low W e         the low W bits of E                                *)
(*   sval W e        the signed (two's-complement) interpretation of E   *)
(*                   as a W-bit value                                   *)
(*   sext F N e      the low F bits of E, sign-extended to N bits       *)
(*   bswap NB e      the low NB bytes of E in reverse order             *)
(*   pow2 e          2 raised to the power (E)                          *)
(*   trunc_div a b   A divided by B, truncated toward zero              *)
(*   trunc_mod a b   the remainder of A divided by B with the quotient   *)
(*                   truncated toward zero (the remainder takes the      *)
(*                   sign of the dividend)                              *)
(*   logand W a b    the W-bit bitwise AND of A and B  (OR, XOR)        *)
(*   if c then a     if C, A; otherwise B                               *)
(*     else b                                                           *)
(*                                                                      *)
(*   The `/`, `%` and `wrap` rows are sign-sensitive because F*'s `/`    *)
(*   and `%` on `int` are Euclidean (Ebpf.Int.fst header); on bit        *)
(*   patterns that is unsigned division, on a `sval` it rounds toward    *)
(*   negative infinity — which is what makes ARSH an arithmetic shift.  *)
(* ------------------------------------------------------------------ *)

let rec en ctx e =
  match e with
  | ELit (n, _) -> string_of_int n
  | EVar (v, _) -> en_var ctx v
  | EWidth (w, _) -> w_str ctx w
  | EArith (Add, a, b, _) -> sprintf "the sum of %s and %s" (en ctx a) (en ctx b)
  | EArith (Sub, a, b, _) -> sprintf "%s minus %s" (en ctx a) (en ctx b)
  | EArith (Mul, a, b, _) -> sprintf "the product of %s and %s" (en ctx a) (en ctx b)
  | EArith (Div, a, b, _) ->
    if may_neg a then
      sprintf "the quotient of %s divided by %s, rounded toward negative infinity"
        (en ctx a) (en ctx b)
    else sprintf "the unsigned quotient of %s divided by %s" (en ctx a) (en ctx b)
  | EArith (Mod, a, b, _) ->
    if may_neg a then
      sprintf "the Euclidean remainder of %s divided by %s" (en ctx a) (en ctx b)
    else sprintf "the unsigned remainder of %s divided by %s" (en ctx a) (en ctx b)
  | EComb (c, ws, es, _) -> en_comb ctx e c ws es
  | EIf (c, x, y, _) ->
    sprintf "(if %s, %s; otherwise %s)" (en_cond ctx c) (en ctx x) (en ctx y)

and en_comb ctx e c ws es =
  let w i = w_str ctx (List.nth ws i) and a i = en ctx (List.nth es i) in
  match (c, List.length ws, List.length es) with
  | Wrap, 1, 1 ->
    if may_neg (List.nth es 0) then
      sprintf "%s, reduced modulo 2^%s (two's-complement wrap-around)" (group (a 0)) (w 0)
    else sprintf "%s, truncated to %s bits" (group (a 0)) (w 0)
  | Low, 1, 1 -> sprintf "the low %s bits of %s" (w 0) (a 0)
  | Sval, 1, 1 ->
    sprintf "the signed (two's-complement) interpretation of %s as %s %s-bit value" (a 0)
      (art (w 0)) (w 0)
  | Sext, 2, 1 -> sprintf "the low %s bits of %s, sign-extended to %s bits" (w 0) (a 0) (w 1)
  | Bswap, 1, 1 -> sprintf "the low %s bytes of %s in reverse order" (w 0) (a 0)
  | Pow2, 0, 1 -> sprintf "2 raised to the power (%s)" (a 0)
  | TruncDiv, 0, 2 -> sprintf "%s divided by %s, truncated toward zero" (a 0) (a 1)
  | TruncMod, 0, 2 ->
    sprintf
      "the remainder of %s divided by %s with the quotient truncated toward zero (the \
       remainder takes the sign of the dividend)"
      (a 0) (a 1)
  | Logand, 1, 2 -> sprintf "the %s-bit bitwise AND of %s and %s" (w 0) (a 0) (a 1)
  | Logor, 1, 2 -> sprintf "the %s-bit bitwise OR of %s and %s" (w 0) (a 0) (a 1)
  | Logxor, 1, 2 -> sprintf "the %s-bit bitwise exclusive OR of %s and %s" (w 0) (a 0) (a 1)
  | _ -> expr_str e (* unreachable: K3 fixes every combinator's arity *)

and en_cond ctx = function
  | CTrue -> "always"
  | CCmp (Eq, a, ELit (0, _), _) -> sprintf "%s is zero" (en ctx a)
  | CCmp (Ne, a, ELit (0, _), _) -> sprintf "%s is nonzero" (en ctx a)
  | CCmp (o, a, b, _) ->
    let op =
      match o with
      | Eq -> "is equal to"
      | Ne -> "is not equal to"
      | Lt -> "is less than"
      | Le -> "is at most"
      | Gt -> "is greater than"
      | Ge -> "is at least"
    in
    sprintf "%s %s %s" (en ctx a) op (en ctx b)
  | CAnd (a, b) -> sprintf "%s and %s" (en_cond ctx a) (en_cond ctx b)
  | COr (a, b) -> sprintf "%s or %s" (en_cond ctx a) (en_cond ctx b)
  | CNot a -> sprintf "it is not the case that %s" (en_cond ctx a)

(* the whole-instruction sentence: the only place the write target is named *)
let en_top ctx (target : string) e =
  match e with
  | EIf (c, x, y, _) ->
    sprintf "If %s, `%s` is set to %s; otherwise `%s` is set to %s." (en_cond ctx c) target
      (en ctx x) target (en ctx y)
  | _ -> sprintf "`%s` is set to %s." target (en ctx e)

(* ------------------------------------------------------------------ *)
(* operands, forms, encodings                                           *)
(* ------------------------------------------------------------------ *)

(* which `operand` case (reg/imm) this instance is, if it has one *)
let src_case (i : instance) =
  match List.assoc_opt "src" i.i_args with Some (AEnum (_, c)) -> Some c | _ -> None

let op_name (i : instance) = function
  | RDst -> "dst"
  | RSrcReg -> "src"
  | RSrcOperand -> ( match src_case i with Some "imm" -> "imm" | _ -> "src")

let op_phrase (i : instance) = function
  | RDst -> "the destination value"
  | RSrcReg -> "the source register value"
  | RSrcOperand -> (
    match src_case i with
    | Some "imm" -> "the immediate value"
    | _ -> "the source register value")

let inst_ctx (i : instance) =
  {
    c_w = i.i_widths;
    c_ps = List.map (fun r -> (r.r_var, op_name i r.r_role)) i.i_reads;
    c_en = List.map (fun r -> (r.r_var, op_phrase i r.r_role)) i.i_reads;
  }

(* width-generic context for the per-entry view: widths stay symbolic *)
let entry_ctx (f : family) =
  {
    c_w = [];
    c_ps = List.map (fun r -> (r.r_var, role_str r.r_role)) f.f_sem.sg_vals;
    c_en =
      List.map
        (fun r ->
          ( r.r_var,
            match r.r_role with
            | RDst -> "the destination value"
            | RSrcReg -> "the source register value"
            | RSrcOperand -> "the source operand value" ))
        f.f_sem.sg_vals;
  }

(* ASSEMBLY MNEMONICS.  EXCEPTION 1 (see the header): the IL carries an
   Ebpf.Ast case name (`ToLE`), not an assembly stem (`le`).  The three
   stems below are the ones that differ, taken from ir/SPEC.md §3; every
   other entry lowercases its name.  The width suffix and the operand list
   are derived.  `tests/run.sh` anchors all eight non-trivial mnemonics
   against ir/SPEC.md so a silent rename is a test failure. *)
let stem (fam : string) (ent : string) =
  match (fam, ent) with
  | "swap", "ToLE" -> "le"
  | "swap", "ToBE" -> "be"
  | "swap", "Bswap" -> "bswap"
  | _ -> String.lowercase_ascii ent

(* the width suffix: this instance's width valuation, innermost width first
   (`n = 64, f = 8` -> `8_64`, i.e. movsx8_64), joined by `_` *)
let width_suffix (i : instance) =
  String.concat "_" (List.rev_map (fun (_, v) -> string_of_int v) i.i_widths)

let entry_of_id (i : instance) =
  match String.split_on_char '/' i.i_id with _ :: e :: _ -> e | _ -> i.i_id

let mnemonic (f : family) (i : instance) =
  let ops =
    List.filter_map
      (fun (ca, (_, _)) -> match ca with CARole r -> Some (op_name i r) | CAAxis _ -> None)
      (List.combine f.f_ctor_args i.i_args)
  in
  (stem i.i_family (entry_of_id i) ^ width_suffix i, String.concat ", " ops)

let ast_form (i : instance) =
  sprintf "%s(%s)" i.i_ctor
    (String.concat ", "
       (List.map
          (fun (_, v) ->
            match v with
            | AEnum (_, c) -> c
            | ARole RDst -> "dst"
            | ARole RSrcReg -> "src"
            | ARole RSrcOperand -> "src")
          i.i_args))

let fld = function FLit n -> sprintf "0x%02x" n | FAny -> "*"
let fld_dec = function FLit n -> string_of_int n | FAny -> "*"

let enc_line (i : instance) =
  sprintf "opcode byte `%s` = `cls %s` + `opc %s` + `sbit %s`; `off = %s`; `imm = %s`"
    (if i.i_opcode >= 0 then sprintf "0x%02x" i.i_opcode else "?")
    (fld i.i_enc.cls) (fld i.i_enc.opc) (fld i.i_enc.sbit) (fld_dec i.i_enc.off)
    (fld_dec i.i_enc.imm)

let read_line (i : instance) (r : read) =
  let ctx = inst_ctx i in
  let wv = match w_val ctx r.r_width with Some n -> n | None -> 64 in
  let ws = string_of_int wv in
  let reg =
    if wv >= 64 then "a 64-bit value"
    else sprintf "%s %d-bit value (its low %d bits)" (art ws) wv wv
  in
  match r.r_role with
  | RDst -> sprintf "`dst` — the destination register, read as %s" reg
  | RSrcReg -> sprintf "`src` — the source register, read as %s" reg
  | RSrcOperand -> (
    match src_case i with
    | Some "imm" ->
      sprintf "`imm` — the 32-bit immediate field, read as %s %d-bit operand value (see §1.4)"
        (art ws) wv
    | _ -> sprintf "`src` — the source register, read as %s" reg)

let oblig_en ctx = function
  | ONonZero (e, _) -> sprintf "%s is nonzero (it is used as a divisor)" (en ctx e)
  | ONonNeg (e, _) -> sprintf "%s is non-negative (it is a `pow2` exponent)" (en ctx e)
  | OLe (a, b, _) ->
    sprintf "the source width %s is at most the target width %s (`sext`)" (w_str ctx a)
      (w_str ctx b)
  | ODivides (k, w, _) ->
    sprintf "%d divides the result width %s (`bswap` produces whole bytes)" k (w_str ctx w)

(* ------------------------------------------------------------------ *)
(* markdown helpers                                                     *)
(* ------------------------------------------------------------------ *)

let cell s = String.concat "\\|" (String.split_on_char '|' s)
let code s = "`" ^ s ^ "`"

let has_comb (pred : comb -> bool) (e : expr) =
  let rec go = function
    | ELit _ | EVar _ | EWidth _ -> false
    | EArith (_, a, b, _) -> go a || go b
    | EComb (c, _, es, _) -> pred c || List.exists go es
    | EIf (c, a, b, _) -> goc c || go a || go b
  and goc = function
    | CTrue -> false
    | CCmp (_, a, b, _) -> go a || go b
    | CAnd (a, b) | COr (a, b) -> goc a || goc b
    | CNot a -> goc a
  in
  go e

(* ------------------------------------------------------------------ *)
(* §1.2 — the rendering tables, printed by RUNNING the renderer on       *)
(*        sample terms, so the documented table cannot drift from it     *)
(* ------------------------------------------------------------------ *)

let p = nowhere
let x = EVar ("x", p)
let y = EVar ("y", p)
let wn = WVar "N"
let sample_ctx = { c_w = []; c_ps = [ ("x", "x"); ("y", "y") ]; c_en = [ ("x", "x"); ("y", "y") ] }

let expr_samples : expr list =
  [
    ELit (0, p);
    x;
    EWidth (wn, p);
    EArith (Add, x, y, p);
    EArith (Sub, x, y, p);
    EArith (Mul, x, y, p);
    EArith (Div, x, y, p);
    EArith (Div, EComb (Sval, [ wn ], [ x ], p), y, p);
    EArith (Mod, x, y, p);
    EComb (Wrap, [ wn ], [ x ], p);
    EComb (Wrap, [ wn ], [ EComb (Sval, [ wn ], [ x ], p) ], p);
    EComb (Low, [ wn ], [ x ], p);
    EComb (Sval, [ wn ], [ x ], p);
    EComb (Sext, [ WVar "F"; wn ], [ x ], p);
    EComb (Bswap, [ WVar "NB" ], [ x ], p);
    EComb (Pow2, [], [ x ], p);
    EComb (TruncDiv, [], [ x; y ], p);
    EComb (TruncMod, [], [ x; y ], p);
    EComb (Logand, [ wn ], [ x; y ], p);
    EComb (Logor, [ wn ], [ x; y ], p);
    EComb (Logxor, [ wn ], [ x; y ], p);
    EIf (CCmp (Lt, x, y, p), x, y, p);
    EIf (CCmp (Eq, x, ELit (0, p), p), ELit (0, p), y, p);
  ]

let cond_samples : cond list =
  [
    CTrue;
    CCmp (Eq, x, ELit (0, p), p);
    CCmp (Ne, x, ELit (0, p), p);
    CCmp (Lt, x, EWidth (wn, p), p);
    CCmp (Le, x, y, p);
    CAnd (CCmp (Ne, x, ELit (0, p), p), CCmp (Lt, y, EWidth (wn, p), p));
    CNot (CCmp (Eq, x, y, p));
  ]

let notation_tables b =
  bp b "### 1.2 Rendering table — expressions\n\n";
  bp b
    "Each row is produced by running the generator on the sample term in the first\n\
     column, so this table *is* the renderer; it cannot describe it wrongly.\n\
     `x`, `y` stand for operand values, `N`, `F`, `NB` for widths.\n\n";
  bp b "| `sem` term | pseudocode | English |\n|---|---|---|\n";
  List.iter
    (fun e ->
      bp b "| %s | %s | %s |\n"
        (cell (code (expr_str e)))
        (cell (code (ps sample_ctx e)))
        (cell (en sample_ctx e)))
    expr_samples;
  bp b "\n### 1.3 Rendering table — conditions\n\n";
  bp b "| `defined` term | pseudocode | English |\n|---|---|---|\n";
  List.iter
    (fun c ->
      bp b "| %s | %s | %s |\n"
        (cell (code (cond_str c)))
        (cell (code (ps_cond sample_ctx c)))
        (cell (en_cond sample_ctx c)))
    cond_samples;
  bp b "\n"

(* ------------------------------------------------------------------ *)
(* the document                                                         *)
(* ------------------------------------------------------------------ *)

let semsig_str (f : family) =
  sprintf "(%s; %s) : %s"
    (String.concat ", " f.f_sem.sg_widths)
    (String.concat ", "
       (List.map
          (fun (r : read) -> sprintf "%s = %s@%s" r.r_var (role_str r.r_role) (wexp_str r.r_width))
          f.f_sem.sg_vals))
    (ty_str f.f_sem.sg_result)

let family_intro b (sp : spec) (f : family) (insts : instance list) =
  bp b "### family `%s` — `Ebpf.Ast.%s`\n\n" f.f_name f.f_ctor;
  bp b "- **AST constructor** — `%s(%s)`\n" f.f_ctor
    (String.concat ", "
       (List.map (function CAAxis v -> v | CARole r -> role_str r) f.f_ctor_args));
  (match f.f_key with
   | Some (v, e) -> bp b "- **Key** — `%s : %s` (one table row per case)\n" v e
   | None -> ());
  if f.f_axes <> [] then
    bp b "- **Form axes** — %s\n"
      (String.concat ", " (List.map (fun (v, e) -> sprintf "`%s : %s`" v e) f.f_axes));
  if f.f_widths <> [] then
    bp b "- **Widths** — %s\n"
      (String.concat ", "
         (List.map (fun (w, a) -> sprintf "`%s = bits %s`" w a) f.f_widths));
  bp b "- **Semantics signature** — `sem %s`\n" (semsig_str f);
  bp b "- **Definedness signature** — %s\n"
    (if f.f_def_vals = [] && f.f_def_widths = [] then "(none — always defined)"
     else
       code
         (sprintf "defined (%s%s)"
            (String.concat ", " f.f_def_widths)
            (if f.f_def_vals = [] then "" else "; " ^ String.concat ", " f.f_def_vals)));
  bp b "- **Instances** — %d\n" (List.length insts);
  if f.f_valid <> CTrue then
    bp b "- **Validity** — `%s`: %s. Axis points that fail it are not instructions.\n"
      (cond_str f.f_valid)
      (en_cond (entry_ctx f) f.f_valid);
  List.iter
    (fun (binds, reason) ->
      bp b "- **Excluded form** — %s — %s\n"
        (code (String.concat ", " (List.map (fun (a, c) -> a ^ " = " ^ c) binds)))
        reason)
    f.f_excludes;
  if List.exists (fun (e : entry) -> has_comb (fun c -> c = Bswap || c = Low) e.e_sem) f.f_entries
  then
    bp b
      "- **Host endianness** — the semantics below is stated for a %s host (`host` in the \
       spec source); on this host the `low` form is a truncation rather than a byte \
       reversal.\n"
      (match sp.s_host with Little -> "**little-endian**" | Big -> "**big-endian**");
  List.iter (fun c -> bp b "- **Cite** — %s\n" c) f.f_cites;
  bp b "\nWidth-generic behaviour, one row per table entry (this is what the F* backend\n\
        emits as a single `match`):\n\n";
  bp b "| entry | `sem` | `defined` | width-generic reading |\n|---|---|---|---|\n";
  let ectx = entry_ctx f in
  List.iter
    (fun (e : entry) ->
      bp b "| %s | %s | %s | %s |\n"
        (code (sprintf "%s/%s" f.f_name e.e_name))
        (cell (code (expr_str e.e_sem)))
        (cell (code (cond_str e.e_defined)))
        (cell (en_top ectx "dst" e.e_sem)))
    f.f_entries;
  bp b "\n"

let instance_section b (f : family) (i : instance) =
  let ctx = inst_ctx i in
  let mn, ops = mnemonic f i in
  bp b "#### `%s%s` — `%s`\n\n" mn (if ops = "" then "" else " " ^ ops) i.i_id;
  bp b "- **Form** — `%s%s`, i.e. `%s`\n" mn
    (if ops = "" then "" else " " ^ ops)
    (ast_form i);
  bp b "- **Encoding** — %s\n" (enc_line i);
  bp b "- **Reads** — %s\n"
    (if i.i_reads = [] then "(none)"
     else String.concat "; " (List.map (read_line i) i.i_reads));
  let rw = match i.i_result with TBits w -> w_val ctx w | TInt -> None in
  bp b "- **Writes** — `dst`%s\n"
    (match rw with
     | Some n when n < 64 ->
       sprintf
         ", a %d-bit result; writing a %d-bit value into the 64-bit destination register \
          clears bits %d..63 (zero extension)"
         n n n
     | Some n -> sprintf ", a %d-bit result" n
     | None -> "");
  bp b "\n**Operation** — `dst = %s`\n\n" (ps ctx i.i_sem);
  bp b "%s\n\n" (en_top ctx "dst" i.i_sem);
  (match i.i_defined with
   | CTrue ->
     bp b
       "**Definedness** — `defined: true`. No precondition: the operation above is total \
        over all operand values, in both checker modes.\n\n"
   | c ->
     bp b
       "**Definedness** — `defined: %s`. Strict mode requires a proof that %s; kernel mode \
        accepts the instruction without one, and the operation above gives the result in \
        every case.\n\n"
       (cond_str c) (en_cond ctx c));
  if i.i_obligs <> [] then begin
    bp b "**Side conditions** (recorded in the IL, discharged on the generated F*):\n\n";
    List.iter
      (fun o -> bp b "- `%s` — %s\n" (oblig_str o) (oblig_en ctx o))
      i.i_obligs;
    bp b "\n"
  end;
  bp b "**Spec source** — `sem: %s`, `defined: %s` (`%s:%d:%d`)\n\n" (expr_str i.i_sem)
    (cond_str i.i_defined) (Filename.basename i.i_pos.file) i.i_pos.line i.i_pos.col;
  if i.i_cites <> [] then
    bp b "**Provenance** — %s\n\n" (String.concat "; " i.i_cites)

let encoding_summary b (sp : spec) =
  bp b "## 3. Encoding summary\n\n";
  bp b
    "Every instance of the fragment, in generation order. `opcode` is the first byte \
     (`cls + opc + sbit`); `*` marks a field carried by the instruction's operands. K8 \
     (encoding disjointness) has checked that no two rows below can decode to the same \
     bytes.\n\n";
  bp b "| id | mnemonic | opcode | cls | opc | sbit | off | imm |\n|---|---|---|---|---|---|---|---|\n";
  List.iter
    (fun (i : instance) ->
      let f = List.find (fun f -> f.f_name = i.i_family) sp.s_families in
      let mn, ops = mnemonic f i in
      bp b "| `%s` | `%s%s` | `%s` | `%s` | `%s` | `%s` | `%s` | `%s` |\n" i.i_id mn
        (if ops = "" then "" else " " ^ ops)
        (if i.i_opcode >= 0 then sprintf "0x%02x" i.i_opcode else "?")
        (field_str i.i_enc.cls) (field_str i.i_enc.opc) (field_str i.i_enc.sbit)
        (field_str i.i_enc.off) (field_str i.i_enc.imm))
    sp.s_instances;
  bp b "\n"

let excluded_section b (sp : spec) =
  bp b "## 4. Forms that are not instructions\n\n";
  let any = List.exists (fun f -> f.f_excludes <> []) sp.s_families in
  if not any then bp b "(none)\n\n"
  else begin
    bp b
      "Axis points that the spec claims are *not* instructions. Each one is a load-bearing \
       claim: it costs a `valid` predicate that agrees with it (checked by K6) and a \
       mandatory reason.\n\n";
    bp b "| family | excluded point | `valid` predicate | reason |\n|---|---|---|---|\n";
    List.iter
      (fun (f : family) ->
        List.iter
          (fun (binds, reason) ->
            bp b "| `%s` | `%s` | `%s` | %s |\n" f.f_name
              (String.concat ", " (List.map (fun (a, c) -> a ^ " = " ^ c) binds))
              (cond_str f.f_valid) (cell reason))
          f.f_excludes)
      sp.s_families;
    bp b "\n"
  end

let header b (file : string) (sp : spec) =
  bp b "<!-- GENERATED by `specgen prose` from %s — DO NOT EDIT.\n\
       \     Regenerate with `make -C spec prose`; `make -C spec test` fails if this\n\
       \     file is stale. -->\n\n" (Filename.basename file);
  bp b "# The eBPF ALU fragment — generated instruction reference\n\n";
  bp b
    "This document is **generated**, not written. Every statement about an individual \
     instruction below is a structural rendering of that instruction's `sem` / `defined` \
     expression, its encoding record, its recorded side conditions and its `cite` lines, \
     as they appear in the KeelSpec source `%s`. No instruction prose is authored \
     anywhere: the generator (`spec/specgen/lib/emit_prose.ml`) contains one English \
     template per AST *node kind* (§1.2, §1.3) and nothing else. A by-eye comparison of \
     this document against RFC 9669 and `fstar/CONSTRAINTS.md`, including an honest list \
     of the places where this rendering is weaker or noisier than the RFC's own wording, \
     is in `spec/PROSE-CHECK.md`.\n\n"
    (Filename.basename file);
  bp b "| | |\n|---|---|\n";
  bp b "| spec | `%s`, version %d |\n" sp.s_name sp.s_version;
  bp b "| ISA | %s |\n" sp.s_isa;
  bp b "| host | %s |\n"
    (match sp.s_host with Little -> "little-endian" | Big -> "big-endian");
  bp b "| families | %d (%s) |\n" (List.length sp.s_families)
    (String.concat ", " (List.map (fun f -> code f.f_name) sp.s_families));
  bp b "| table entries | %d |\n"
    (List.fold_left (fun a f -> a + List.length f.f_entries) 0 sp.s_families);
  bp b "| instructions | %d |\n" (List.length sp.s_instances);
  bp b "| excluded forms | %d |\n"
    (List.fold_left (fun a f -> a + List.length f.f_excludes) 0 sp.s_families);
  bp b "\n"

let how_to_read b (sp : spec) =
  bp b "## 1. How to read this document\n\n";
  bp b "### 1.1 What is derived, and what is not\n\n";
  bp b
    "Derived from the spec source: every mnemonic form, encoding, operand read, \
     operation, definedness condition, side condition, exclusion and citation.\n\n\
     Not derived, and therefore the part a reviewer must read critically:\n\n\
     - the **English templates** for the AST node kinds, tabulated in §1.2 and §1.3 — \
       one template per node kind, applied uniformly;\n\
     - the **assembly stems** `le` / `be` / `bswap`, which the IL does not carry (its \
       entry names are the `Ebpf.Ast` case names `ToLE` / `ToBE` / `Bswap`); every other \
       mnemonic lowercases its entry name and appends the instance's widths;\n\
     - this section, §1.4, and the fixed section headings, which say nothing about any \
       individual instruction.\n\n";
  notation_tables b;
  bp b "### 1.4 Operand reads, immediates and write-back\n\n";
  bp b
    "KeelSpec deliberately does not specify how an operand is *read*; it names the read \
     (`d = dst@n`, `s = src@n`) and leaves the reading functions in the hand-written \
     frame (`Ebpf.Semantics.regbits` / `opbits`, `spec/DESIGN.md` §1). Two consequences \
     for this document:\n\n\
     - a register read at width *n* < 64 is the low *n* bits of the register;\n\
     - **the immediate rule is not visible below**: a 32-bit immediate is sign-extended \
       to 64 bits for 64-bit forms and used as a 32-bit pattern for 32-bit forms \
       (`Ebpf.Int.imm64` / `imm32`; `CONSTRAINTS.md` C11). Wherever a section says \
       \"`imm` — the 32-bit immediate field, read as a 64-bit operand value\", that read \
       is where the sign extension happens.\n\n\
     The write-back direction *is* visible: a result declared `bits n` stored into a \
     64-bit register is exactly the zero-extension rule, so every section whose result is \
     narrower than 64 bits states it.\n\n";
  bp b "### 1.5 Definedness and the two checker modes\n\n";
  bp b
    "Each instruction carries a `defined` condition — the **strict-mode** precondition. \
     In **kernel mode** the verifier accepts the instruction without proving it, and the \
     `Operation` line is the behaviour in every case (this is why division by zero has a \
     defined result). In strict mode the checker must prove the condition; programs that \
     pass are safe under the defensive semantics, where the excluded cases are stuck \
     states. See `fstar/CONSTRAINTS.md` (modes, C5–C9).\n\n";
  bp b "### 1.6 Encoding fields written `*`\n\n";
  bp b
    "The spec fixes each of the five encoding fields (`cls`, `opc`, `sbit`, `off`, `imm`) \
     to a byte, or writes `*` for \"not fixed by this form — supplied by the \
     instruction's operands\". `*` is what makes the disjointness check (K8) \
     conservative: two forms overlap if they *could* decode to the same bytes. Note that \
     the IL does not distinguish \"carried by an immediate operand\" from \"unused by \
     this form\": a register-source ALU instruction shows `imm = *` even though it has no \
     immediate operand at all, and the kernel requires such unused fields to be zero. See \
     `spec/PROSE-CHECK.md` (finding P7).\n\n";
  ignore sp

let render (file : string) (sp : spec) : string =
  let b = Buffer.create (1 lsl 18) in
  header b file sp;
  how_to_read b sp;
  bp b "## 2. Instructions\n\n";
  List.iter
    (fun (f : family) ->
      let insts = List.filter (fun i -> i.i_family = f.f_name) sp.s_instances in
      family_intro b sp f insts;
      List.iter (fun i -> instance_section b f i) insts)
    sp.s_families;
  encoding_summary b sp;
  excluded_section b sp;
  bp b "## 5. Coverage\n\n";
  let nx = List.fold_left (fun a f -> a + List.length f.f_excludes) 0 sp.s_families in
  bp b
    "One section per instruction of the fragment: %d sections for %d instances, from %d \
     table entries in %d families, plus %d excluded form%s listed in §4. \
     `spec/tests/run.sh` re-generates this file and fails if it differs from the \
     committed copy, and separately asserts that every entry id and every instance id in \
     the IL occurs here — a silently omitted instruction is a test failure.\n\n"
    (List.length sp.s_instances) (List.length sp.s_instances)
    (List.fold_left (fun a f -> a + List.length f.f_entries) 0 sp.s_families)
    (List.length sp.s_families) nx
    (if nx = 1 then "" else "s");
  Buffer.contents b
