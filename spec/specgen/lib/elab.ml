(* Elaboration: surface syntax -> checked IL, running meta-checks K1-K9.
   See spec/DESIGN.md section 4 for what each check rejects. *)

open Kpos
open Il

let sprintf = Printf.sprintf

(* position used by whole-file diagnostics (K1/K9); set to the spec block *)
let dpos = ref nowhere

(* ------------------------------------------------------------------ *)
(* small helpers                                                        *)
(* ------------------------------------------------------------------ *)

let fits_bits n k = k >= 0 && (n >= 62 || k < 1 lsl n)

let aop_of = function
  | "+" -> Add | "-" -> Sub | "*" -> Mul | "/" -> Div | "%" -> Mod
  | s -> failwith ("bad arith op " ^ s)

let cmp_of = function
  | "=" -> Eq | "<>" -> Ne | "<" -> Lt | "<=" -> Le | ">" -> Gt | ">=" -> Ge
  | s -> failwith ("bad cmp " ^ s)

let neg_cmp = function
  | Eq -> Ne | Ne -> Eq | Lt -> Ge | Ge -> Lt | Le -> Gt | Gt -> Le

let rec negate = function
  | CTrue -> CNot CTrue
  | CCmp (o, a, b, p) -> CCmp (neg_cmp o, a, b, p)
  | CAnd (a, b) -> COr (negate a, negate b)
  | COr (a, b) -> CAnd (negate a, negate b)
  | CNot a -> a

let dedup l = List.fold_left (fun acc x -> if List.mem x acc then acc else x :: acc) [] l |> List.rev

let itemize = function [] -> "(none)" | l -> String.concat ", " l

(* ------------------------------------------------------------------ *)
(* enums                                                                *)
(* ------------------------------------------------------------------ *)

let elab_enum (se : Parse.senum) : enum =
  let seen = Hashtbl.create 8 in
  let cases =
    List.map
      (fun (nm, attrs, p) ->
        if Hashtbl.mem seen nm then fail p "duplicate case `%s` in enum `%s`" nm se.se_name;
        Hashtbl.add seen nm ();
        List.iter
          (fun (a, _) ->
            if a <> "bits" && a <> "enc" then
              fail p "unknown enum attribute `%s` (known: bits, enc)" a)
          attrs;
        { c_name = nm;
          c_bits = List.assoc_opt "bits" attrs;
          c_enc = List.assoc_opt "enc" attrs })
      se.se_cases
  in
  if cases = [] then fail se.se_pos "enum `%s` has no cases" se.se_name;
  { en_name = se.se_name; en_cases = cases; en_pos = se.se_pos }

(* K1a: declared enums vs the Ebpf.Ast reference table, directionally *)
let check_enums_vs_ast (enums : enum list) (log : string list ref) =
  List.iter
    (fun (e : enum) ->
      match Astref.find_enum e.en_name with
      | None ->
        fail e.en_pos
          "[K1] enum `%s` is not an Ebpf.Ast argument domain (known: %s)"
          e.en_name
          (itemize (List.map (fun (r : Astref.refenum) -> r.re_name) Astref.enums))
      | Some r ->
        let spec = List.map (fun c -> c.c_name) e.en_cases in
        let only_spec = List.filter (fun x -> not (List.mem x r.re_spec_cases)) spec in
        let only_ast = List.filter (fun x -> not (List.mem x spec)) r.re_spec_cases in
        if only_spec <> [] || only_ast <> [] then
          fail e.en_pos
            "[K1] enum `%s` disagrees with Ebpf.Ast type `%s`:\n\
            \       in spec, not in AST: %s\n\
            \       in AST, not in spec: %s"
            e.en_name r.re_ast_type (itemize only_spec) (itemize only_ast);
        if spec <> r.re_spec_cases then
          fail e.en_pos
            "[K1] enum `%s` lists the right cases in the wrong order:\n\
            \       spec: %s\n\
            \       AST : %s"
            e.en_name (itemize spec) (itemize r.re_spec_cases))
    enums;
  List.iter
    (fun (r : Astref.refenum) ->
      if not (List.exists (fun (e : enum) -> e.en_name = r.re_name) enums) then
        fail !dpos
          "[K1] Ebpf.Ast argument domain `%s` is not declared:\n\
          \       in AST, not in spec: %s"
          r.re_name (itemize r.re_spec_cases))
    Astref.enums;
  log := !log @ [ sprintf "K1 ast-conformance   ok   enums: %d, constructors: %s"
                    (List.length enums) (Astref.ctor_list_str ()) ]

(* ------------------------------------------------------------------ *)
(* expression elaboration (K2 scope, K3 combinators)                    *)
(* ------------------------------------------------------------------ *)

type scope = { sc_widths : string list; sc_vals : string list; sc_what : string }

let rec resolve (sc : scope) (e : Parse.sexpr) : expr =
  match e with
  | Parse.SLit (n, p) -> ELit (n, p)
  | Parse.SVar (x, p) ->
    if List.mem x sc.sc_widths then EWidth (WVar x, p)
    else if List.mem x sc.sc_vals then EVar (x, p)
    else
      fail p
        "[K2] unknown variable `%s` in %s; in scope here: %s"
        x sc.sc_what
        (itemize (sc.sc_widths @ sc.sc_vals))
  | Parse.SArith (o, a, b, p) -> EArith (aop_of o, resolve sc a, resolve sc b, p)
  | Parse.SIf (c, a, b, p) -> EIf (resolve_cond sc c, resolve sc a, resolve sc b, p)
  | Parse.SApp (name, args, p) ->
    let c = Option.get (Il.comb_of_string name) in
    let nw, nv = Il.comb_arity c in
    let ws = List.filteri (fun i _ -> i < nw) args in
    let vs = List.filteri (fun i _ -> i >= nw) args in
    let ws = List.map (fun a -> to_wexp sc (resolve sc a)) ws in
    EComb (c, ws, List.map (resolve sc) vs, p)

and resolve_cond sc = function
  | Parse.SCTrue _ -> CTrue
  | Parse.SCCmp (o, a, b, p) -> CCmp (cmp_of o, resolve sc a, resolve sc b, p)
  | Parse.SCAnd (a, b, _) -> CAnd (resolve_cond sc a, resolve_cond sc b)
  | Parse.SCOr (a, b, _) -> COr (resolve_cond sc a, resolve_cond sc b)
  | Parse.SCNot (a, _) -> CNot (resolve_cond sc a)

and to_wexp sc (e : expr) : wexp =
  match e with
  | ELit (n, _) -> WLit n
  | EWidth (w, _) -> w
  | EArith (o, a, b, _) -> WBin (o, to_wexp sc a, to_wexp sc b)
  | EVar (v, p) ->
    fail p "[K4] `%s` is an operand, but a width is required here" v
  | e -> fail (expr_pos e) "[K4] a width argument must be a width expression"

let rec eval_w (env : (string * int) list) (p : pos) (w : wexp) : int =
  match w with
  | WLit n -> n
  | WVar v ->
    (match List.assoc_opt v env with
     | Some n -> n
     | None -> fail p "[K2] unknown width variable `%s`" v)
  | WBin (o, a, b) ->
    let x = eval_w env p a and y = eval_w env p b in
    (match o with
     | Add -> x + y | Sub -> x - y | Mul -> x * y
     | Div -> if y = 0 then fail p "division by zero in a width expression" else x / y
     | Mod -> if y = 0 then fail p "modulo zero in a width expression" else x mod y)

(* ------------------------------------------------------------------ *)
(* the width/type checker (K4) and the side conditions (K5)             *)
(* ------------------------------------------------------------------ *)

type cty = CInt | CBits of int

let cty_str = function CInt -> "int" | CBits n -> sprintf "bits %d" n

type tstate = {
  t_widths : (string * int) list;
  t_vals : (string * int) list;      (* value param -> its bit width *)
  mutable t_obl : oblig list;
}

let rec nonzero (st : tstate) (pc : cond list) (e : expr) : bool =
  match e with
  | ELit (k, _) -> k <> 0
  | EWidth (w, p) -> eval_w st.t_widths p w <> 0
  | EComb (Pow2, _, _, _) -> true
  | EComb (Sval, _, [ x ], _) -> nonzero st pc x
  | EVar (v, _) ->
    List.exists
      (fun c ->
        match c with
        | CCmp (Ne, EVar (v', _), ELit (0, _), _) -> v' = v
        | CCmp (Ne, ELit (0, _), EVar (v', _), _) -> v' = v
        | _ -> false)
      pc
  | _ -> false

let rec nonneg (st : tstate) (e : expr) : bool =
  match e with
  | ELit (k, _) -> k >= 0
  | EVar _ -> true                       (* value params are bit patterns *)
  | EWidth (w, p) -> eval_w st.t_widths p w >= 0
  | EComb ((Wrap | Low | Sext | Bswap | Pow2 | Logand | Logor | Logxor), _, _, _) -> true
  | EComb ((Sval | TruncDiv | TruncMod), _, _, _) -> false
  | EArith ((Add | Mul | Div | Mod), a, b, _) -> nonneg st a && nonneg st b
  | EArith (Sub, _, _, _) -> false
  | EIf (_, a, b, _) -> nonneg st a && nonneg st b

let rec infer (st : tstate) (pc : cond list) (e : expr) : cty =
  match e with
  | ELit _ -> CInt
  | EWidth _ -> CInt
  | EVar (v, p) ->
    (match List.assoc_opt v st.t_vals with
     | Some n -> CBits n
     | None -> fail p "[K2] unbound operand `%s`" v)
  | EArith (o, a, b, p) ->
    check st pc a CInt;
    check st pc b CInt;
    (match o with
     | Div | Mod -> require_nonzero st pc b p (Il.aop_str o)
     | _ -> ());
    CInt
  | EIf (c, a, b, p) ->
    check_cond st pc c;
    let t = infer st (pc @ [ c ]) a in
    check st (pc @ [ negate c ]) b t;
    t
  | EComb (c, ws, vs, p) ->
    let w i = eval_w st.t_widths p (List.nth ws i) in
    (match c, vs with
     | (Wrap | Low), [ x ] ->
       check st pc x CInt;
       let n = w 0 in
       if n < 1 then fail p "[K4] `%s` needs a positive width, got %d" (comb_str c) n;
       CBits n
     | Sval, [ x ] ->
       let n = w 0 in
       check st pc x (CBits n);
       CInt
     | Sext, [ x ] ->
       check st pc x CInt;
       let f = w 0 and n = w 1 in
       if f > n then
         fail p "[K4] `sext %d %d`: source width exceeds target width" f n;
       st.t_obl <- st.t_obl @ [ OLe (List.nth ws 0, List.nth ws 1, p) ];
       CBits n
     | Bswap, [ x ] ->
       check st pc x CInt;
       let nb = w 0 in
       if nb < 1 then fail p "[K4] `bswap` needs a positive byte count, got %d" nb;
       (match List.nth ws 0 with
        | WBin (Div, inner, WLit 8) -> st.t_obl <- st.t_obl @ [ ODivides (8, inner, p) ]
        | _ -> ());
       CBits (8 * nb)
     | Pow2, [ x ] ->
       check st pc x CInt;
       st.t_obl <- st.t_obl @ [ ONonNeg (x, p) ];
       if not (nonneg st x) then
         fail p "[K5] `pow2` argument may be negative: %s" (expr_str x);
       CInt
     | (TruncDiv | TruncMod), [ a; b ] ->
       check st pc a CInt;
       check st pc b CInt;
       require_nonzero st pc b p (comb_str c);
       CInt
     | (Logand | Logor | Logxor), [ a; b ] ->
       let n = w 0 in
       check st pc a (CBits n);
       check st pc b (CBits n);
       CBits n
     | _ -> fail p "[K3] `%s` applied to the wrong number of arguments" (comb_str c))

and check (st : tstate) (pc : cond list) (e : expr) (t : cty) : unit =
  match e, t with
  | EIf (c, a, b, _), _ ->
    check_cond st pc c;
    check st (pc @ [ c ]) a t;
    check st (pc @ [ negate c ]) b t
  | ELit (k, p), CBits n ->
    if not (fits_bits n k) then
      fail p "[K4] literal %d does not fit in `bits %d`" k n
  | ELit _, CInt -> ()
  | _ ->
    let t' = infer st pc e in
    (match t', t with
     | CBits n, CBits m when n <> m ->
       fail (expr_pos e)
         "[K4] this expression has type `bits %d` but `bits %d` is required"
         n m
     | CInt, CBits m ->
       fail (expr_pos e)
         "[K4] this expression has type `int` but `bits %d` is required \
          (a `wrap`/`low` is missing)" m
     | _ -> ())

and check_cond (st : tstate) (pc : cond list) (c : cond) : unit =
  match c with
  | CTrue -> ()
  | CCmp (_, a, b, _) -> check st pc a CInt; check st pc b CInt
  | CAnd (a, b) | COr (a, b) -> check_cond st pc a; check_cond st pc b
  | CNot a -> check_cond st pc a

and require_nonzero st pc b p what =
  st.t_obl <- st.t_obl @ [ ONonZero (b, p) ];
  if not (nonzero st pc b) then
    fail p
      "[K5] `%s` needs a non-zero divisor, but `%s` may be zero here \
       (guard it with `if <divisor> = 0 then ... else ...`)"
      what (expr_str b)

(* ------------------------------------------------------------------ *)
(* families                                                             *)
(* ------------------------------------------------------------------ *)

let enc_fields = [ "cls"; "opc"; "sbit"; "off"; "imm" ]

type fctx = {
  fx : Parse.sfamily;
  enums : enum list;
  axes : (string * string) list;          (* axis var -> enum name, key first *)
  key : (string * string) option;
  widths : (string * string) list;        (* width var -> axis var *)
  roles : (string * role) list;           (* role name -> role *)
}

let find_enum ctx n p =
  match List.find_opt (fun (e : enum) -> e.en_name = n) ctx.enums with
  | Some e -> e
  | None -> fail p "undeclared enum `%s`" n

let enum_case (e : enum) (c : string) p =
  match List.find_opt (fun x -> x.c_name = c) e.en_cases with
  | Some x -> x
  | None ->
    fail p "`%s` is not a case of enum `%s` (cases: %s)" c e.en_name
      (itemize (List.map (fun x -> x.c_name) e.en_cases))

(* K1b: the ctor line against the Ebpf.Ast reference table *)
let check_ctor (ctx : fctx) : string * ctorarg list =
  let fx = ctx.fx in
  let name, args, p =
    match fx.fs_ctor with
    | Some x -> x
    | None -> fail fx.fs_pos "[K7] family `%s` has no `ctor` declaration" fx.fs_name
  in
  if List.mem name Astref.pseudo then
    fail p
      "[K1] `%s` is a pseudo/terminal instruction, not machine arithmetic; \
       it must not be specified (pseudo: %s)"
      name (Astref.pseudo_list_str ());
  let r =
    match Astref.find_ctor name with
    | Some r -> r
    | None ->
      fail p "[K1] `%s` is not an Ebpf.Ast constructor; known: %s" name
        (Astref.ctor_list_str ())
  in
  if List.length args <> List.length r.ct_args then
    fail p "[K1] `%s` takes %d arguments in Ebpf.Ast, %d given" name
      (List.length r.ct_args) (List.length args);
  let out =
    List.map2
      (fun (k : Astref.argkind) (a : Parse.sctorarg) ->
        match k, a with
        | Astref.KEnum en, Parse.SCAxis (v, ap) ->
          (match List.assoc_opt v ctx.axes with
           | None -> fail ap "[K1] `%s` is not a declared axis" v
           | Some en' when en' <> en ->
             fail ap "[K1] `%s` has type `%s` at this argument of `%s`, but axis `%s` ranges over `%s`"
               v en name v en'
           | Some _ -> CAAxis v)
        | Astref.KDst, Parse.SCRole (nm, "reg", ap) ->
          if nm <> "dst" then fail ap "[K1] the written register role must be named `dst`";
          CARole RDst
        | Astref.KSrcReg, Parse.SCRole (nm, "reg", ap) ->
          if nm <> "src" then fail ap "[K1] the source register role must be named `src`";
          CARole RSrcReg
        | Astref.KSrcOperand, Parse.SCRole (nm, "operand", ap) ->
          if nm <> "src" then fail ap "[K1] the source operand role must be named `src`";
          (match List.assoc_opt nm ctx.axes with
           | Some "operand" -> ()
           | _ ->
             fail ap
               "[K1] `src:operand` needs an axis `src : operand` (it selects OpReg vs OpImm)");
          CARole RSrcOperand
        | Astref.KEnum en, Parse.SCRole (nm, _, ap) ->
          fail ap "[K1] argument `%s` of `%s` is `%s`-typed in Ebpf.Ast, not a role" nm name en
        | (Astref.KDst | Astref.KSrcReg | Astref.KSrcOperand), Parse.SCAxis (v, ap) ->
          fail ap "[K1] argument `%s` of `%s` is a register/operand role in Ebpf.Ast, not an axis" v name
        | _, Parse.SCRole (nm, k', ap) ->
          fail ap "[K1] argument `%s` of `%s` has the wrong role kind `%s`" nm name k')
      r.ct_args args
  in
  (name, out)

let field_of_sfield (ctx : fctx) (cases : (string * string) list)
    (wvals : (string * int) list) (f : Parse.sfield) : field =
  match f with
  | Parse.SFInt (n, _) -> FLit n
  | Parse.SFAny _ -> FAny
  | Parse.SFRef (x, p) ->
    (match List.assoc_opt x ctx.axes with
     | Some en ->
       let e = find_enum ctx en p in
       let c = enum_case e (List.assoc x cases) p in
       (match c.c_enc with
        | Some v -> FLit v
        | None ->
          fail p "[K7] case `%s` of enum `%s` has no `enc=` attribute" c.c_name en)
     | None ->
       (match List.assoc_opt x wvals with
        | Some v -> FLit v
        | None ->
          fail p
            "[K7] `%s` is neither an axis nor a width variable of this family" x))

(* how a field is spelled, before instantiation (kept in the IL for MS3) *)
let fieldsrc_of (ctx : fctx) (f : Parse.sfield) : fieldsrc =
  match f with
  | Parse.SFInt (n, _) -> FSLit n
  | Parse.SFAny _ -> FSAny
  | Parse.SFRef (x, p) ->
    if List.mem_assoc x ctx.axes then FSAxis x
    else if List.mem_assoc x ctx.widths then FSWidth x
    else fail p "[K7] `%s` is neither an axis nor a width variable of this family" x

(* the cartesian product of the NON-KEY axis domains, in declaration order.
   Instances are entries x this product: a key case with no entry is not an
   instance, it is a coverage hole, and K9 reports it as one. *)
let axis_product (ctx : fctx) : (string * string) list list =
  let non_key =
    List.filter (fun (v, _) -> Some v <> Option.map fst ctx.key) ctx.axes
  in
  List.fold_left
    (fun acc (v, en) ->
      let e = find_enum ctx en ctx.fx.fs_pos in
      List.concat_map
        (fun combo -> List.map (fun c -> combo @ [ (v, c.c_name) ]) e.en_cases)
        acc)
    [ [] ] non_key

let elab_family (enums : enum list) (fx : Parse.sfamily) : family * instance list =
  let axes0 =
    (match fx.fs_key with Some (v, en, _) -> [ (v, en) ] | None -> [])
    @ List.map (fun (v, en, _) -> (v, en)) fx.fs_axes
  in
  let ctx =
    { fx; enums; axes = axes0;
      key = (match fx.fs_key with Some (v, en, _) -> Some (v, en) | None -> None);
      widths = List.map (fun (v, a, _) -> (v, a)) fx.fs_widths;
      roles = [] }
  in
  (* duplicate axis names *)
  List.iter
    (fun (v, _) ->
      if List.length (List.filter (fun (v', _) -> v' = v) ctx.axes) > 1 then
        fail fx.fs_pos "duplicate axis `%s`" v)
    ctx.axes;
  List.iter (fun (_, en) -> ignore (find_enum ctx en fx.fs_pos)) ctx.axes;
  let ctor_name, ctor_args = check_ctor ctx in
  let role_name = function RDst -> "dst" | RSrcReg -> "src" | RSrcOperand -> "src" in
  let roles =
    List.filter_map (function CARole r -> Some (role_name r, r) | _ -> None) ctor_args
  in
  (* width bindings *)
  List.iter
    (fun (wv, ax, p) ->
      match List.assoc_opt ax ctx.axes with
      | None -> fail p "[K2] `bits %s`: `%s` is not an axis of this family" ax ax
      | Some en ->
        let e = find_enum ctx en p in
        List.iter
          (fun c ->
            if c.c_bits = None then
              fail p "[K1] case `%s` of enum `%s` has no `bits=` attribute, so \
                      `bits %s` is undefined" c.c_name en ax)
          e.en_cases)
    fx.fs_widths;
  (* sem signature *)
  let ss =
    match fx.fs_sem with
    | Some s -> s
    | None -> fail fx.fs_pos "[K7] family `%s` has no `sem` signature" fx.fs_name
  in
  let decl_widths = List.map (fun (v, _, _) -> v) fx.fs_widths in
  let sem_widths = List.map fst ss.ss_widths in
  List.iter
    (fun (v, p) ->
      if not (List.mem v decl_widths) then
        fail p "[K2] `%s` is not a declared width variable (declared: %s)" v
          (itemize decl_widths))
    ss.ss_widths;
  List.iter
    (fun v ->
      if not (List.mem v sem_widths) then
        fail fx.fs_pos "[K2] width variable `%s` is declared but not a `sem` parameter" v)
    decl_widths;
  let wsc = { sc_widths = sem_widths; sc_vals = []; sc_what = "a width expression" } in
  let reads =
    List.map
      (fun (v, role, w, p) ->
        match List.assoc_opt role roles with
        | None ->
          fail p "[K2] `%s` is not an operand role of `%s` (roles: %s)" role ctor_name
            (itemize (List.map fst roles))
        | Some r -> { r_var = v; r_role = r; r_width = to_wexp wsc (resolve wsc w) })
      ss.ss_vals
  in
  let sem_vals = List.map (fun r -> r.r_var) reads in
  let result =
    match ss.ss_res with
    | Parse.STInt _ -> TInt
    | Parse.STBits (w, _) -> TBits (to_wexp wsc (resolve wsc w))
  in
  (* defined signature (K2: a subset of sem's parameters) *)
  let def_widths, def_vals =
    match fx.fs_def with
    | None -> (sem_widths, [])
    | Some d ->
      List.iter
        (fun (v, p) ->
          if not (List.mem v sem_widths) then
            fail p "[K2] `%s` is not a `sem` width parameter" v)
        d.ds_widths;
      List.iter
        (fun (v, p) ->
          if not (List.mem v sem_vals) then
            fail p
              "[K2] `%s` is not a `sem` value parameter; `defined` may only \
               mention operands the semantics reads (in scope: %s)"
              v (itemize sem_vals))
        d.ds_vals;
      (List.map fst d.ds_widths, List.map fst d.ds_vals)
  in
  let valid =
    match fx.fs_valid with
    | None -> CTrue
    | Some (c, _) ->
      resolve_cond { sc_widths = sem_widths; sc_vals = []; sc_what = "a `valid` clause" } c
  in
  (* columns and encoding fields (K7) *)
  let cols =
    match fx.fs_cols with
    | Some c -> c
    | None -> fail fx.fs_pos "[K7] family `%s` has no `cols` declaration" fx.fs_name
  in
  (match cols with
   | ("name", _) :: _ -> ()
   | (c, p) :: _ -> fail p "[K7] the first column must be `name`, not `%s`" c
   | [] -> fail fx.fs_cols_pos "[K7] empty `cols` declaration");
  let col_names = List.map fst cols in
  List.iter
    (fun (c, p) ->
      if not (List.mem c ("name" :: "defined" :: "sem" :: enc_fields)) then
        fail p "[K7] unknown column `%s` (columns are: name, defined, sem, %s)" c
          (itemize enc_fields))
    cols;
  List.iter
    (fun c ->
      if List.length (List.filter (fun x -> x = c) col_names) > 1 then
        fail fx.fs_cols_pos "[K7] duplicate column `%s`" c)
    col_names;
  if not (List.mem "sem" col_names) then
    fail fx.fs_cols_pos "[K7] every entry needs a `sem` column";
  if not (List.mem "defined" col_names) then
    fail fx.fs_cols_pos "[K7] every entry needs a `defined` column";
  List.iter
    (fun (f, _, p) ->
      if not (List.mem f enc_fields) then
        fail p "[K7] unknown encoding field `%s` (fields: %s)" f (itemize enc_fields);
      if List.length (List.filter (fun (f', _, _) -> f' = f) fx.fs_enc) > 1 then
        fail p "[K7] encoding field `%s` is assigned twice" f;
      if List.mem f col_names then
        fail p "[K7] encoding field `%s` is given both in `enc` and as a column" f)
    fx.fs_enc;
  List.iter
    (fun f ->
      let in_enc = List.exists (fun (f', _, _) -> f' = f) fx.fs_enc in
      let in_col = List.mem f col_names in
      if (not in_enc) && (not in_col) && f <> "imm" then
        fail fx.fs_pos
          "[K7] family `%s` never gives encoding field `%s` (put it in `enc` or in `cols`)"
          fx.fs_name f)
    enc_fields;
  (* rows *)
  if fx.fs_rows = [] then fail fx.fs_pos "[K7] family `%s` has no entries" fx.fs_name;
  (match ctx.key with
   | None ->
     if List.length fx.fs_rows <> 1 then
       fail fx.fs_pos
         "family `%s` has no `key`, so it must have exactly one entry (found %d)"
         fx.fs_name (List.length fx.fs_rows)
   | Some (_, en) ->
     let e = find_enum ctx en fx.fs_pos in
     List.iter (fun (r : Parse.srow) -> ignore (enum_case e r.rw_name r.rw_pos)) fx.fs_rows;
     List.iter
       (fun (r : Parse.srow) ->
         if List.length (List.filter (fun (r' : Parse.srow) -> r'.rw_name = r.rw_name) fx.fs_rows) > 1
         then fail r.rw_pos "duplicate entry `%s`" r.rw_name)
       fx.fs_rows);
  let semsc = { sc_widths = sem_widths; sc_vals = sem_vals; sc_what = "a `sem` expression" } in
  let defsc = { sc_widths = def_widths; sc_vals = def_vals; sc_what = "a `defined` clause" } in
  let is_dash toks =
    match toks with [ { Lex.tk = Lex.SYM "-"; _ } ] -> true | _ -> false
  in
  let entries =
    List.map
      (fun (r : Parse.srow) ->
        if List.length r.rw_cells <> List.length cols - 1 then
          fail r.rw_pos "[K7] entry `%s` has %d cells, but `cols` declares %d" r.rw_name
            (List.length r.rw_cells) (List.length cols - 1);
        let cells = List.combine (List.tl col_names) r.rw_cells in
        let get c = List.assoc c cells in
        let sem_toks, sem_p = get "sem" in
        if is_dash sem_toks || sem_toks = [] then
          fail sem_p "[K7] entry `%s` has no semantics" r.rw_name;
        let sem = resolve semsc (Parse.parse_expr_toks sem_toks sem_p) in
        let dtoks, dp = get "defined" in
        let dfn =
          if dtoks = [] then fail dp "[K7] entry `%s` has no definedness cell" r.rw_name
          else if is_dash dtoks then CTrue
          else resolve_cond defsc (Parse.parse_cond_toks dtoks dp)
        in
        let enc_row =
          List.filter_map
            (fun (c, (toks, p)) ->
              if List.mem c enc_fields then begin
                if toks = [] || is_dash toks then
                  fail p "[K7] entry `%s` has no `%s` value" r.rw_name c;
                let cc = Parse.mk_cur toks p in
                let f = Parse.p_field cc in
                Parse.done_or_fail cc "an encoding value";
                Some (c, f)
              end else None)
            cells
        in
        { e_name = r.rw_name; e_key = (match ctx.key with Some _ -> Some r.rw_name | None -> None);
          e_sem = sem; e_defined = dfn;
          e_enc_row = List.map (fun (c, f) -> (c, fieldsrc_of ctx f)) enc_row;
          e_pos = r.rw_pos },
        enc_row)
      fx.fs_rows
  in
  (* instances *)
  let excl_expanded =
    List.concat_map
      (fun (binds, reason, p) ->
        List.iter
          (fun (ax, cs, bp) ->
            match List.assoc_opt ax ctx.axes with
            | None -> fail bp "[K6] `%s` is not an axis of this family" ax
            | Some en -> ignore (enum_case (find_enum ctx en bp) cs bp))
          binds;
        [ (List.map (fun (a, c, _) -> (a, c)) binds, reason, p) ])
      fx.fs_excl
  in
  let matches_excl (cases : (string * string) list) (binds, _, _) =
    List.for_all (fun (a, c) -> List.assoc a cases = c) binds
  in
  let instances = ref [] and invalid = ref [] and excluded = ref [] in
  let combos =
    List.concat_map
      (fun ((ent : entry), enc_row) ->
        List.map
          (fun rest ->
            let key_bind =
              match ctx.key with Some (kv, _) -> [ (kv, ent.e_name) ] | None -> []
            in
            (ent, enc_row, key_bind @ rest))
          (axis_product ctx))
      entries
  in
  List.iter
    (fun (ent, enc_row, combo) ->
      let row_name = ent.e_name in
      let wvals =
        List.map
          (fun (wv, ax) ->
            let en = List.assoc ax ctx.axes in
            let c = enum_case (find_enum ctx en fx.fs_pos) (List.assoc ax combo) fx.fs_pos in
            (wv, Option.get c.c_bits))
          ctx.widths
      in
      let ok =
        let rec ev = function
          | CTrue -> true
          | CNot a -> not (ev a)
          | CAnd (a, b) -> ev a && ev b
          | COr (a, b) -> ev a || ev b
          | CCmp (o, a, b, p) ->
            let num = function
              | ELit (n, _) -> n
              | EWidth (w, _) -> eval_w wvals p w
              | e -> fail (expr_pos e) "[K2] a `valid` clause may only mention widths"
            in
            let x = num a and y = num b in
            (match o with
             | Eq -> x = y | Ne -> x <> y | Lt -> x < y
             | Le -> x <= y | Gt -> x > y | Ge -> x >= y)
        in
        ev valid
      in
      let combo_str =
        String.concat "," (List.map (fun (a, c) -> a ^ "=" ^ c) combo)
      in
      let is_excl = List.exists (matches_excl combo) excl_expanded in
      if is_excl then excluded := combo_str :: !excluded;
      if not ok then invalid := combo_str :: !invalid;
      if ok && not is_excl then begin
        let suffix =
          List.filter_map
            (fun (a, c) ->
              match ctx.key with Some (kv, _) when kv = a -> None | _ -> Some c)
            combo
        in
        let id = String.concat "/" ((fx.fs_name :: row_name :: suffix)) in
        let st = { t_widths = wvals;
                   t_vals = List.map (fun r -> (r.r_var, eval_w wvals ent.e_pos r.r_width)) reads;
                   t_obl = [] } in
        let want =
          match result with
          | TInt -> CInt
          | TBits w -> CBits (eval_w wvals ent.e_pos w)
        in
        check st [] ent.e_sem want;
        check_cond st [] ent.e_defined;
        let enc =
          let getf f =
            match List.assoc_opt f enc_row with
            | Some sf -> field_of_sfield ctx combo wvals sf
            | None ->
              (match List.find_opt (fun (f', _, _) -> f' = f) fx.fs_enc with
               | Some (_, sf, _) -> field_of_sfield ctx combo wvals sf
               | None -> FAny)
          in
          { cls = getf "cls"; opc = getf "opc"; sbit = getf "sbit";
            off = getf "off"; imm = getf "imm" }
        in
        let opcode =
          match enc.cls, enc.opc, enc.sbit with
          | FLit a, FLit b, FLit c -> a + b + c
          | _ -> -1
        in
        let args =
          List.map
            (function
              | CAAxis v -> (v, AEnum (List.assoc v ctx.axes, List.assoc v combo))
              | CARole r ->
                let nm = role_name r in
                (* an `operand` role is chosen by a same-named axis: record
                   which case (OpReg/OpImm) this instance is *)
                (match List.assoc_opt nm combo with
                 | Some case -> (nm, AEnum (List.assoc nm ctx.axes, case))
                 | None -> (nm, ARole r)))
            ctor_args
        in
        instances :=
          { i_id = id; i_family = fx.fs_name; i_ctor = ctor_name; i_args = args;
            i_enc = enc; i_opcode = opcode; i_widths = wvals; i_reads = reads;
            i_result = result; i_sem = ent.e_sem; i_defined = ent.e_defined;
            i_obligs = st.t_obl; i_cites = fx.fs_cites; i_pos = ent.e_pos }
          :: !instances
      end)
    combos;
  (* K6: `valid` and `exclude` must describe the same set *)
  let inv = List.sort compare (dedup !invalid) in
  let exc = List.sort compare (dedup !excluded) in
  if inv <> exc then begin
    let only_valid = List.filter (fun x -> not (List.mem x exc)) inv in
    let only_excl = List.filter (fun x -> not (List.mem x inv)) exc in
    fail fx.fs_pos
      "[K6] family `%s`: `valid` and `exclude` disagree:\n\
      \       rejected by `valid` but not excluded: %s\n\
      \       excluded but accepted by `valid`:     %s"
      fx.fs_name (itemize only_valid) (itemize only_excl)
  end;
  let fam =
    { f_name = fx.fs_name; f_ctor = ctor_name; f_ctor_args = ctor_args;
      f_key = ctx.key; f_axes = List.filter (fun (v, _) -> Some v <> Option.map fst ctx.key) ctx.axes;
      f_widths = ctx.widths;
      f_sem = { sg_widths = sem_widths; sg_vals = reads; sg_result = result };
      f_def_widths = def_widths; f_def_vals = def_vals;
      f_valid = valid;
      f_excludes = List.map (fun (b, r, _) -> (b, r)) excl_expanded;
      f_enc_family = List.map (fun (f, sf, _) -> (f, fieldsrc_of ctx sf)) fx.fs_enc;
      f_cols = col_names;
      f_entries = List.map fst entries;
      f_cites = fx.fs_cites; f_pos = fx.fs_pos }
  in
  (fam, List.rev !instances)

(* ------------------------------------------------------------------ *)
(* cross-family checks                                                  *)
(* ------------------------------------------------------------------ *)

let compat a b =
  match a, b with FAny, _ | _, FAny -> true | FLit x, FLit y -> x = y

let enc_compat (a : enc) (b : enc) =
  compat a.cls b.cls && compat a.opc b.opc && compat a.sbit b.sbit
  && compat a.off b.off && compat a.imm b.imm

let enc_str (e : enc) =
  sprintf "cls=%s opc=%s sbit=%s off=%s imm=%s" (field_str e.cls) (field_str e.opc)
    (field_str e.sbit) (field_str e.off) (field_str e.imm)

(* K8 *)
let check_disjoint (insts : instance list) (log : string list ref) =
  let arr = Array.of_list insts in
  for i = 0 to Array.length arr - 1 do
    for j = i + 1 to Array.length arr - 1 do
      if enc_compat arr.(i).i_enc arr.(j).i_enc then
        fail arr.(j).i_pos
          "[K8] `%s` and `%s` claim overlapping encodings:\n\
          \       %s : %s\n\
          \       %s : %s"
          arr.(i).i_id arr.(j).i_id arr.(i).i_id (enc_str arr.(i).i_enc) arr.(j).i_id
          (enc_str arr.(j).i_enc)
    done
  done;
  log := !log @ [ sprintf "K8 enc-disjointness  ok   %d instances, %d pairs compared"
                    (Array.length arr)
                    (Array.length arr * (Array.length arr - 1) / 2) ]

(* K9 *)
let check_exhaustive (fams : family list) (insts : instance list) (log : string list ref) =
  List.iter
    (fun (c : Astref.ctor) ->
      match List.filter (fun f -> f.f_ctor = c.ct_name) fams with
      | [] ->
        fail !dpos
          "[K9] no family specifies Ebpf.Ast constructor `%s`:\n\
          \       in AST, not in spec: %s"
          c.ct_name c.ct_name
      | _ :: _ :: _ ->
        fail !dpos "[K9] constructor `%s` is claimed by more than one family" c.ct_name
      | [ f ] ->
        (* the argument domains of the constructor: its enum-typed arguments,
           plus the OpReg/OpImm choice of an `operand` argument *)
        let doms =
          List.filter_map
            (function
              | Astref.KEnum en ->
                Some (en, (Option.get (Astref.find_enum en)).Astref.re_spec_cases)
              | Astref.KSrcOperand ->
                Some ("operand", (Option.get (Astref.find_enum "operand")).Astref.re_spec_cases)
              | _ -> None)
            c.ct_args
        in
        let full =
          List.fold_left
            (fun acc (en, cases) ->
              List.concat_map (fun combo -> List.map (fun cs -> combo @ [ cs ]) cases) acc)
            [ [] ] doms
        in
        let point (i : instance) =
          List.filter_map
            (fun (_, v) -> match v with AEnum (_, c) -> Some c | ARole _ -> None)
            i.i_args
        in
        let covered = List.map point (List.filter (fun i -> i.i_family = f.f_name) insts) in
        (* the axis variables, in the order their domains appear in the ctor *)
        let axis_order =
          List.filter_map
            (function
              | CAAxis v -> Some v
              | CARole RSrcOperand -> Some "src"
              | CARole _ -> None)
            f.f_ctor_args
        in
        let idx a =
          let rec go i = function
            | [] -> -1
            | x :: r -> if x = a then i else go (i + 1) r
          in
          go 0 axis_order
        in
        let excl_points =
          List.filter
            (fun pt ->
              List.exists
                (fun (binds, _) ->
                  List.for_all
                    (fun (a, cs) ->
                      let i = idx a in
                      i >= 0 && i < List.length pt && List.nth pt i = cs)
                    binds)
                f.f_excludes)
            full
        in
        let missing =
          List.filter (fun pt -> not (List.mem pt covered) && not (List.mem pt excl_points)) full
        in
        let extra = List.filter (fun pt -> not (List.mem pt full)) covered in
        let str pt = c.ct_name ^ "(" ^ String.concat "," pt ^ ")" in
        if missing <> [] || extra <> [] then
          fail f.f_pos
            "[K9] family `%s` does not cover Ebpf.Ast constructor `%s` exhaustively:\n\
            \       in AST, not in spec: %s\n\
            \       in spec, not in AST: %s"
            f.f_name c.ct_name
            (itemize (List.map str missing))
            (itemize (List.map str extra)))
    Astref.ctors;
  List.iter
    (fun f ->
      if not (List.exists (fun (c : Astref.ctor) -> c.ct_name = f.f_ctor) Astref.ctors) then
        fail f.f_pos "[K9] family `%s` specifies unknown constructor `%s`" f.f_name f.f_ctor)
    fams;
  log := !log
         @ [ sprintf "K9 exhaustiveness    ok   %s covered; pseudo/terminal not spec'd: %s"
               (Astref.ctor_list_str ()) (Astref.pseudo_list_str ()) ]

(* ------------------------------------------------------------------ *)
(* entry point                                                          *)
(* ------------------------------------------------------------------ *)

let elab (sf : Parse.sfile) : spec * string list =
  let log = ref [] in
  let sp =
    match sf.sf_spec with
    | Some s -> s
    | None -> fail nowhere "the file has no `spec` block"
  in
  dpos := sp.Parse.sp_pos;
  let enums = List.map elab_enum sf.sf_enums in
  List.iter
    (fun (e : enum) ->
      if List.length (List.filter (fun (e' : enum) -> e'.en_name = e.en_name) enums) > 1 then
        fail e.en_pos "duplicate enum `%s`" e.en_name)
    enums;
  check_enums_vs_ast enums log;
  if sf.sf_families = [] then fail !dpos "the file declares no families";
  let pairs = List.map (elab_family enums) sf.sf_families in
  let fams = List.map fst pairs in
  let insts = List.concat_map snd pairs in
  List.iter
    (fun f ->
      if List.length (List.filter (fun f' -> f'.f_name = f.f_name) fams) > 1 then
        fail f.f_pos "duplicate family `%s`" f.f_name)
    fams;
  log := !log @ [ sprintf "K2 scope             ok   every `sem`/`defined`/`valid` \
                           variable resolved" ];
  log := !log @ [ sprintf "K3 combinators       ok   only Ebpf.Int + FStar.UInt combinators used" ];
  log := !log @ [ sprintf "K4 well-widthedness  ok   %d instances type-checked at concrete widths"
                    (List.length insts) ];
  let nobl = List.fold_left (fun a i -> a + List.length i.i_obligs) 0 insts in
  log := !log @ [ sprintf "K5 side conditions   ok   %d obligations discharged and recorded" nobl ];
  log := !log @ [ sprintf "K6 valid==exclude    ok   %d excluded instance(s)"
                    (List.fold_left (fun a f -> a + List.length f.f_excludes) 0 fams) ];
  log := !log @ [ sprintf "K7 completeness      ok   every entry has encoding + semantics + definedness" ];
  check_disjoint insts log;
  check_exhaustive fams insts log;
  ({ s_name = sp.Parse.sp_name; s_version = sp.Parse.sp_version; s_isa = sp.Parse.sp_isa;
     s_host = (if sp.Parse.sp_host = "little-endian" then Little else Big);
     s_enums = enums; s_families = fams; s_instances = insts },
   !log)
