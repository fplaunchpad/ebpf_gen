(* The checked intermediate form.  This is the whole backend API: MS2 (F*
   semantics), MS3 (encoding) and MS4 (prose) consume these types and nothing
   else.  See spec/DESIGN.md sections 3 and 5. *)

open Kpos

type aop = Add | Sub | Mul | Div | Mod
type cmp = Eq | Ne | Lt | Le | Gt | Ge

(* width expressions stay SYMBOLIC in the width variables: `wrap n (d + s)`
   is stored with `n` unresolved so the F* backend can print a width-generic
   function.  Each instance additionally carries a concrete valuation. *)
type wexp = WLit of int | WVar of string | WBin of aop * wexp * wexp

type ty = TInt | TBits of wexp

(* exactly the Ebpf.Int + FStar.UInt combinator set - nothing else exists *)
type comb =
  | Wrap | Low | Sval | Sext | Bswap | Pow2
  | TruncDiv | TruncMod | Logand | Logor | Logxor

type expr =
  | ELit of int * pos
  | EVar of string * pos                          (* a sem value parameter *)
  | EWidth of wexp * pos                          (* a width var in value position *)
  | EArith of aop * expr * expr * pos
  | EComb of comb * wexp list * expr list * pos   (* width args, value args *)
  | EIf of cond * expr * expr * pos

and cond =
  | CTrue
  | CCmp of cmp * expr * expr * pos
  | CAnd of cond * cond
  | COr of cond * cond
  | CNot of cond

type role = RDst | RSrcReg | RSrcOperand

type read = { r_var : string; r_role : role; r_width : wexp }

(* an encoding field: a literal byte, or `*` = supplied by an operand *)
type field = FLit of int | FAny

(* how a family/entry SPELLS an encoding field before instantiation: a
   literal, `*`, or derived from an axis case / a width variable *)
type fieldsrc = FSLit of int | FSAny | FSAxis of string | FSWidth of string

type enc = { cls : field; opc : field; sbit : field; off : field; imm : field }

(* side conditions the generated F* must satisfy; K5 discharges what it can
   syntactically and records all of them for the F* backend *)
type oblig =
  | ONonZero of expr * pos      (* a divisor is non-zero *)
  | ONonNeg of expr * pos       (* a pow2 argument is non-negative *)
  | OLe of wexp * wexp * pos    (* sext: source width <= target width *)
  | ODivides of int * wexp * pos(* bswap: 8 divides the result width *)

type argval =
  | AEnum of string * string    (* enum name, case name *)
  | ARole of role

(* one Ebpf.Ast constructor argument: an axis variable, or an operand role *)
type ctorarg = CAAxis of string | CARole of role

type instance = {
  i_id : string;                        (* "alu/ADD/W32/reg" *)
  i_family : string;
  i_ctor : string;                      (* "Alu" *)
  i_args : (string * argval) list;      (* ctor argument order *)
  i_enc : enc;
  i_opcode : int;                       (* cls + opc + sbit, when all literal *)
  i_widths : (string * int) list;       (* concrete valuation of width vars *)
  i_reads : read list;
  i_result : ty;
  i_sem : expr;
  i_defined : cond;
  i_obligs : oblig list;
  i_cites : string list;
  i_pos : pos;
}

type entry = {
  e_name : string;                      (* row name = key case, or free ident *)
  e_key : string option;
  e_sem : expr;
  e_defined : cond;
  e_enc_row : (string * fieldsrc) list;
  e_pos : pos;
}

type semsig = {
  sg_widths : string list;
  sg_vals : read list;                  (* value params, with role and read width *)
  sg_result : ty;
}

type family = {
  f_name : string;
  f_ctor : string;
  f_ctor_args : ctorarg list;
  f_key : (string * string) option;             (* var, enum *)
  f_axes : (string * string) list;              (* var, enum *)
  f_widths : (string * string) list;            (* width var <- axis *)
  f_sem : semsig;
  f_def_widths : string list;
  f_def_vals : string list;
  f_valid : cond;
  f_excludes : ((string * string) list * string) list;
  f_enc_family : (string * fieldsrc) list;
  f_cols : string list;
  f_entries : entry list;
  f_cites : string list;
  f_pos : pos;
}

type enum_case = { c_name : string; c_bits : int option; c_enc : int option }
type enum = { en_name : string; en_cases : enum_case list; en_pos : pos }

type endianness = Little | Big

type spec = {
  s_name : string;
  s_version : int;
  s_isa : string;
  s_host : endianness;
  s_enums : enum list;
  s_families : family list;
  s_instances : instance list;
}

(* ------------------------------------------------------------------ *)
(* printing (diagnostics, `specgen list`, and a head start for MS4)     *)
(* ------------------------------------------------------------------ *)

let aop_str = function Add -> "+" | Sub -> "-" | Mul -> "*" | Div -> "/" | Mod -> "%"
let cmp_str = function
  | Eq -> "=" | Ne -> "<>" | Lt -> "<" | Le -> "<=" | Gt -> ">" | Ge -> ">="

let comb_str = function
  | Wrap -> "wrap" | Low -> "low" | Sval -> "sval" | Sext -> "sext"
  | Bswap -> "bswap" | Pow2 -> "pow2" | TruncDiv -> "trunc_div"
  | TruncMod -> "trunc_mod" | Logand -> "logand" | Logor -> "logor"
  | Logxor -> "logxor"

(* width args / value args, per combinator *)
let comb_arity = function
  | Wrap | Low | Sval -> (1, 1)
  | Sext -> (2, 1)
  | Bswap -> (1, 1)
  | Pow2 -> (0, 1)
  | TruncDiv | TruncMod -> (0, 2)
  | Logand | Logor | Logxor -> (1, 2)

let comb_of_string = function
  | "wrap" -> Some Wrap | "low" -> Some Low | "sval" -> Some Sval
  | "sext" -> Some Sext | "bswap" -> Some Bswap | "pow2" -> Some Pow2
  | "trunc_div" -> Some TruncDiv | "trunc_mod" -> Some TruncMod
  | "logand" -> Some Logand | "logor" -> Some Logor | "logxor" -> Some Logxor
  | _ -> None

let rec wexp_str = function
  | WLit n -> string_of_int n
  | WVar v -> v
  | WBin (o, a, b) -> "(" ^ wexp_str a ^ " " ^ aop_str o ^ " " ^ wexp_str b ^ ")"

let ty_str = function TInt -> "int" | TBits w -> "bits " ^ wexp_str w

let rec expr_str = function
  | ELit (n, _) -> string_of_int n
  | EVar (v, _) -> v
  | EWidth (w, _) -> wexp_str w
  | EArith (o, a, b, _) -> "(" ^ expr_str a ^ " " ^ aop_str o ^ " " ^ expr_str b ^ ")"
  | EComb (c, ws, es, _) ->
    String.concat " "
      (comb_str c :: List.map wexp_str ws @ List.map (fun e -> "(" ^ expr_str e ^ ")") es)
  | EIf (c, a, b, _) ->
    "if " ^ cond_str c ^ " then " ^ expr_str a ^ " else " ^ expr_str b

and cond_str = function
  | CTrue -> "true"
  | CCmp (o, a, b, _) -> expr_str a ^ " " ^ cmp_str o ^ " " ^ expr_str b
  | CAnd (a, b) -> cond_str a ^ " && " ^ cond_str b
  | COr (a, b) -> cond_str a ^ " || " ^ cond_str b
  | CNot a -> "not " ^ cond_str a

let field_str = function FLit n -> Printf.sprintf "0x%02x" n | FAny -> "*"

let fieldsrc_str = function
  | FSLit n -> Printf.sprintf "0x%02x" n
  | FSAny -> "*"
  | FSAxis a -> "axis " ^ a
  | FSWidth w -> "width " ^ w

let role_str = function RDst -> "dst" | RSrcReg -> "src:reg" | RSrcOperand -> "src:operand"

let expr_pos = function
  | ELit (_, p) | EVar (_, p) | EWidth (_, p) | EArith (_, _, _, p)
  | EComb (_, _, _, p) | EIf (_, _, _, p) -> p

let oblig_str = function
  | ONonZero (e, _) -> "nonzero(" ^ expr_str e ^ ")"
  | ONonNeg (e, _) -> "nonneg(" ^ expr_str e ^ ")"
  | OLe (a, b, _) -> wexp_str a ^ " <= " ^ wexp_str b
  | ODivides (k, w, _) -> string_of_int k ^ " | " ^ wexp_str w
