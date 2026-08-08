(* emit_fstar.ml - the F* backend (MS2).  Consumes the IL (`Il.spec`) and
   prints the generated regions of `fstar/Ebpf.Semantics.fst` and
   `fstar/Ebpf.Serialize.fst`.  See spec/DESIGN.md section 5.

   The backend is a PRETTY-PRINTER: every IL node maps to exactly one F*
   term (DESIGN section 2.6), so nothing here decides anything semantic.  It is
   untrusted (DESIGN section 7): its output is re-verified by F*.

   Splicing.  The two F* files carry hand-written frame code that the spec
   deliberately does not describe (regfile, regbits/opbits/res64, stepx,
   encode_insn, ...).  Rather than generate them, `emit` reads the committed
   file, replaces the text between BEGIN/END GENERATED markers, and writes
   the result to spec/out/.  `make -C spec promote` then copies it back.
   Generation is therefore idempotent, and `make -C spec test` diffs the two
   to catch spec/F* drift mechanically. *)

open Il

let sprintf = Printf.sprintf

(* ================================================================== *)
(* 0. Names                                                            *)
(* ================================================================== *)

(* The F* names below are the ones the hand-written frame and the EXISTING
   PROOFS already use (`Ebpf.Interval`, `Ebpf.Sound`, `Ebpf.Annot`,
   `Ebpf.CertClaim` all mention `alu_semn` / `alu_defined` / `swap_bits` by
   name).  The generator reproduces them; it does not invent a naming
   scheme.  Each table is also an ALLOW-LIST: an enum or a family/field with
   no entry here is NOT emitted, because the hand-written frame covers it. *)

(* width tables generated from an enum's `bits=` attributes.
   `width` is absent ON PURPOSE: its table is `Ebpf.Semantics.bits`, which
   the hand-written frame (regbits / opbits / res64) consumes, so it stays
   in the frame (DESIGN section 1). *)
let width_table_name : (string * (string * string)) list =
  [ ("movsx_sz", ("movsx_bits", "sz"));
    ("swap_sz", ("swap_bits", "sz")) ]

(* encoding tables generated from an enum's `enc=` attributes.
   `operand` is absent: its table is `Ebpf.Serialize.src_bit` (MS3). *)
let enc_enum_name : (string * (string * string)) list =
  [ ("width", ("cls", "w")) ]

(* encoding tables indexed by a family's KEY enum: one value per table row *)
let enc_key_name : ((string * string) * string) list =
  [ (("alu", "opc"), "op_bits");
    (("alu", "off"), "op_off") ]

(* encoding tables indexed by an AXIS enum, carrying that case's `bits=`
   (a field spelled `off = width f` / `imm = width m`) *)
let enc_width_name : ((string * string) * string) list =
  [ (("movsx", "off"), "movsx_off");
    (("swap", "imm"), "swap_imm") ]

(* The three fields that add up to the opcode byte (DESIGN section 2.5:
   `opcode = cls + opc + sbit`).  Their tables carry a `n <= max` refinement,
   which is what discharges `Ebpf.Serialize.fields`' `opcode < 256`
   precondition, and they print in hex.  `off`/`imm` are plain `nat` and
   print in decimal. *)
let opcode_field f = f = "cls" || f = "opc" || f = "sbit"

(* ================================================================== *)
(* 1. Expression printer                                               *)
(* ================================================================== *)

(* precedence: 0 if | 1 cmp | 2 + - | 3 * / % | 4 application | 5 atom *)
let aop_prec = function Add | Sub -> 2 | Mul | Div | Mod -> 3

let paren (ctx : int) (lvl : int) (s : string) =
  if ctx > lvl then "(" ^ s ^ ")" else s

(* the F* spelling of each combinator (DESIGN section 2.6).  `Ebpf.Int` is
   opened by both target modules; `FStar.UInt` is aliased to `UInt`. *)
let comb_fstar = function
  | Wrap -> "wrap"
  | Low -> "low"
  | Sval -> "sval"
  | Sext -> "sext"
  | Bswap -> "bswap"
  | Pow2 -> "pow2"
  | TruncDiv -> "trunc_div"
  | TruncMod -> "trunc_mod"
  | Logand -> "UInt.logand"
  | Logor -> "UInt.logor"
  | Logxor -> "UInt.logxor"

(* logand/logor/logxor take their width IMPLICITLY in F*; KeelSpec makes it
   explicit (DESIGN section 8 deviation 9), so it prints back as `#n`. *)
let implicit_width = function Logand | Logor | Logxor -> true | _ -> false

(* `sub` maps a width variable to its F* text: either the variable itself
   (abstract emission, `alu_semn (n: pos)`) or its axis table application
   (`swap_bits sz`).  See DESIGN section 5, contract point 3. *)
let rec pp_wexp (sub : (string * string) list) (ctx : int) (w : wexp) : string =
  match w with
  | WLit n -> string_of_int n
  | WVar v -> (
    match List.assoc_opt v sub with
    | None -> v
    | Some txt ->
      (* an axis table application binds like an application, not an atom *)
      if String.contains txt ' ' then paren ctx 4 txt else txt)
  | WBin (o, a, b) ->
    let p = aop_prec o in
    paren ctx p (pp_wexp sub p a ^ " " ^ aop_str o ^ " " ^ pp_wexp sub (p + 1) b)

let rec pp_expr (sub : (string * string) list) (ctx : int) (e : expr) : string =
  match e with
  | ELit (n, _) -> string_of_int n
  | EVar (v, _) -> v
  | EWidth (w, _) -> pp_wexp sub ctx w
  | EArith (o, a, b, _) ->
    let p = aop_prec o in
    paren ctx p (pp_expr sub p a ^ " " ^ aop_str o ^ " " ^ pp_expr sub (p + 1) b)
  | EComb (c, ws, es, _) ->
    let wargs =
      List.map
        (fun w ->
          let t = pp_wexp sub 5 w in
          if implicit_width c then "#" ^ t else t)
        ws
    in
    let vargs = List.map (fun e -> pp_expr sub 5 e) es in
    paren ctx 4 (String.concat " " ((comb_fstar c :: wargs) @ vargs))
  | EIf (c, a, b, _) ->
    paren ctx 0
      ("if " ^ pp_cond sub 1 c ^ " then " ^ pp_expr sub 0 a ^ " else "
     ^ pp_expr sub 0 b)

and pp_cond (sub : (string * string) list) (ctx : int) (c : cond) : string =
  match c with
  | CTrue -> "true"
  | CCmp (o, a, b, _) ->
    paren ctx 1 (pp_expr sub 2 a ^ " " ^ cmp_str o ^ " " ^ pp_expr sub 2 b)
  | CAnd (a, b) -> paren ctx 1 (pp_cond sub 2 a ^ " && " ^ pp_cond sub 2 b)
  | COr (a, b) -> paren ctx 1 (pp_cond sub 2 a ^ " || " ^ pp_cond sub 2 b)
  | CNot a -> paren ctx 3 ("not " ^ pp_cond sub 4 a)

(* `let f (a) (b) : t =` on one line when it fits, wrapped otherwise - which
   is how the hand-written definitions are laid out *)
let pp_sig (head : string) (res : string) =
  let one = sprintf "%s : %s =" head res in
  if String.length one <= 80 then one else sprintf "%s\n  : %s =" head res

(* a value of declared type `bits w`, named `x`, as an F* refinement type *)
let pp_ty (sub : (string * string) list) (name : string) (t : ty) =
  match t with
  | TInt -> "int"
  | TBits w -> sprintf "int{fits %s %s}" (pp_wexp sub 5 w) name

(* ================================================================== *)
(* 2. `match` layout                                                   *)
(* ================================================================== *)

(* One arm per line.  When every arm has a single constructor pattern the
   patterns are padded so the `->` line up, which is how the hand-written
   `alu_semn` / `swap_sem` are laid out. *)
let pp_match (scrutinee : string) (arms : (string list * string) list) : string =
  let single = List.for_all (fun (pats, _) -> List.length pats = 1) arms in
  let width =
    if not single then 0
    else List.fold_left (fun a (p, _) -> max a (String.length (List.hd p))) 0 arms
  in
  let b = Buffer.create 256 in
  Buffer.add_string b ("  match " ^ scrutinee ^ " with\n");
  List.iter
    (fun (pats, rhs) ->
      let pat = String.concat " | " pats in
      let pat = if single then Printf.sprintf "%-*s" width pat else pat in
      Buffer.add_string b (sprintf "  | %s -> %s\n" pat rhs))
    arms;
  Buffer.contents b

(* group table rows that share a right-hand side, in first-occurrence order *)
let group_rows (rows : (string * string) list) : (string list * string) list =
  let order = ref [] in
  List.iter (fun (_, v) -> if not (List.mem v !order) then order := v :: !order) rows;
  List.map
    (fun v -> (List.filter_map (fun (k, v') -> if v' = v then Some k else None) rows, v))
    (List.rev !order)

(* ================================================================== *)
(* 3. IL helpers                                                       *)
(* ================================================================== *)

let find_enum (sp : spec) (n : string) =
  match List.find_opt (fun (e : enum) -> e.en_name = n) sp.s_enums with
  | Some e -> e
  | None -> failwith ("emit: no enum " ^ n)

let case_bits (e : enum) (c : enum_case) =
  match c.c_bits with
  | Some b -> b
  | None -> failwith (sprintf "emit: case %s of enum %s has no bits=" c.c_name e.en_name)

let case_enc (e : enum) (c : enum_case) =
  match c.c_enc with
  | Some b -> b
  | None -> failwith (sprintf "emit: case %s of enum %s has no enc=" c.c_name e.en_name)

let fam_instances (sp : spec) (f : family) =
  List.filter (fun i -> i.i_family = f.f_name) sp.s_instances

let fam_obligs sp f = List.concat_map (fun i -> i.i_obligs) (fam_instances sp f)

(* the enum a width variable ranges over, via its axis *)
let width_axis_enum (f : family) (v : string) =
  match List.assoc_opt v f.f_widths with
  | None -> None
  | Some ax -> (
    match List.assoc_opt ax f.f_axes with
    | Some en -> Some (ax, en)
    | None -> ( match f.f_key with Some (k, en) when k = ax -> Some (ax, en) | _ -> None))

(* DESIGN section 5, contract point 3: a width parameter may be emitted
   abstractly (`n: pos`) only when the semantics type-checks for EVERY n.
   `bswap (m / 8)` does not - it needs `8 | m` - and that is exactly the
   `ODivides` obligation the checker recorded, so the IL decides this. *)
let via_axis sp f v =
  List.exists
    (function
      | ODivides (_, w, _) ->
        let rec has = function
          | WVar x -> x = v
          | WBin (_, a, b) -> has a || has b
          | WLit _ -> false
        in
        has w
      | _ -> false)
    (fam_obligs sp f)

(* ================================================================== *)
(* 4. Ebpf.Semantics                                                   *)
(* ================================================================== *)

(* the width substitution for a family, plus the extra enum-typed axis
   parameters that a via-axis width emission introduces *)
let width_env sp (f : family) =
  List.filter_map
    (fun (v, _ax) ->
      if not (via_axis sp f v) then None
      else
        match width_axis_enum f v with
        | None -> None
        | Some (_ax, en) -> (
          match List.assoc_opt en width_table_name with
          | None -> failwith (sprintf "emit: no width table for enum %s" en)
          | Some (fn, param) -> Some (v, sprintf "%s %s" fn param)))
    f.f_widths

(* refinements a width parameter carries, from the recorded obligations.
   `OLe (a, b)` (sext's source <= target) lands on whichever of the two is
   declared LAST, so it can mention the other. *)
let width_refinements sp (f : family) (order : string list) (v : string) =
  let idx x =
    let rec go i = function [] -> -1 | y :: t -> if y = x then i else go (i + 1) t in
    go 0 order
  in
  let seen = ref [] in
  List.filter_map
    (function
      | OLe (a, b, _) -> (
        match (a, b) with
        | WVar x, WVar y when (x = v && idx x > idx y) || (y = v && idx y > idx x) ->
          let s = sprintf "%s <= %s" x y in
          if List.mem s !seen then None
          else (
            seen := s :: !seen;
            Some s)
        | _ -> None)
      | _ -> None)
    (fam_obligs sp f)

(* Parameter order = the order of the originating arguments in the AST
   constructor (`f_ctor_args`): `Alu(w, op, ..)` gives `alu_semn (n) (op)`,
   `Swap(k, z, ..)` gives `swap_sem (k) (sz)`.  Operand roles are not
   parameters here - they are the `sem` value params, which follow. *)
let head_params sp (f : family) (env : (string * string) list)
    (want_width : string -> bool) =
  let worder = f.f_sem.sg_widths in
  List.filter_map
    (function
      | CARole _ -> None
      | CAAxis ax -> (
        match f.f_key with
        | Some (k, en) when k = ax -> Some (sprintf "(%s: %s)" k en)
        | _ -> (
          (* the width variable this axis binds, if any *)
          match List.find_opt (fun (_, a) -> a = ax) f.f_widths with
          | None -> None (* e.g. alu's `src : operand`: not a sem parameter *)
          | Some (v, _) ->
            if not (want_width v) then None
            else if List.mem_assoc v env then
              let en = match List.assoc_opt ax f.f_axes with Some e -> e | None -> ax in
              let param =
                match List.assoc_opt en width_table_name with
                | Some (_, p) -> p
                | None -> ax
              in
              Some (sprintf "(%s: %s)" param en)
            else
              let refs = width_refinements sp f worder v in
              Some
                (if refs = [] then sprintf "(%s: pos)" v
                 else sprintf "(%s: pos{%s})" v (String.concat " /\\ " refs)))))
    f.f_ctor_args

let sem_fun sp (f : family) : string option =
  let env = width_env sp f in
  let abstract = env = [] in
  (* `_semn` = width-generic (an abstract `n`); `_sem` = over the axis enum *)
  let name = f.f_name ^ if abstract then "_semn" else "_sem" in
  (* DESIGN section 5: a keyless family is ONE term, so inlining it is free and
     keeps every downstream proof term textually identical; a keyed family
     would inline its whole match into every VC that mentions it. *)
  let kw = if f.f_key = None then "unfold let" else "let" in
  let heads = head_params sp f env (fun _ -> true) in
  let vals =
    List.map
      (fun (r : read) ->
        sprintf "(%s: %s)" r.r_var (pp_ty env r.r_var (TBits r.r_width)))
      f.f_sem.sg_vals
  in
  let res = sprintf "r:%s" (pp_ty env "r" f.f_sem.sg_result) in
  let sigline = String.concat " " ((kw ^ " " ^ name) :: (heads @ vals)) in
  let body =
    match f.f_key with
    | None -> (
      match f.f_entries with
      | [ e ] -> "  " ^ pp_expr env 0 e.e_sem ^ "\n"
      | _ -> failwith (sprintf "emit: family %s has no key but %d entries" f.f_name
                         (List.length f.f_entries)))
    | Some (k, _) ->
      pp_match k
        (List.map (fun (e : entry) -> ([ e.e_name ], pp_expr env 0 e.e_sem)) f.f_entries)
  in
  Some (sprintf "%s\n%s" (pp_sig sigline res) body)

let defined_fun sp (f : family) : string option =
  if List.for_all (fun (e : entry) -> e.e_defined = CTrue) f.f_entries then None
  else
    let env = width_env sp f in
    let name = f.f_name ^ "_defined" in
    let heads = head_params sp f env (fun v -> List.mem v f.f_def_widths) in
    let vals =
      List.filter_map
        (fun (r : read) ->
          if not (List.mem r.r_var f.f_def_vals) then None
          else Some (sprintf "(%s: %s)" r.r_var (pp_ty env r.r_var (TBits r.r_width))))
        f.f_sem.sg_vals
    in
    let sigline = String.concat " " ((("let " ^ name) :: heads) @ vals) in
    let rows =
      List.map (fun (e : entry) -> (e.e_name, pp_cond env 0 e.e_defined)) f.f_entries
    in
    (* DESIGN section 2.5: a `-` cell elaborates to `true`; those rows become the
       `| _ -> true` default, which is how `alu_defined` is written today. *)
    let groups = group_rows rows in
    let dflt, rest = List.partition (fun (_, rhs) -> rhs = "true") groups in
    let arms =
      List.map (fun (pats, rhs) -> (pats, rhs)) rest
      @ List.map (fun (_, rhs) -> ([ "_" ], rhs)) dflt
    in
    let body =
      match f.f_key with
      | Some (k, _) -> pp_match k arms
      | None -> "  " ^ snd (List.hd rows) ^ "\n"
    in
    Some (sprintf "%s\n%s" (pp_sig sigline "bool") body)

(* a width table generated from an enum's `bits=` attributes.  The result
   refinement is `n <= max` unless some family needs divisibility from it
   (`bswap (m / 8)`, recorded as `ODivides`), in which case the exact value
   set is what discharges it - DESIGN section 5, contract point 3. *)
let width_table sp (en : enum) (fn : string) (param : string) =
  let vals = List.map (fun c -> case_bits en c) en.en_cases in
  let needs_exact =
    List.exists
      (fun (f : family) ->
        List.exists
          (fun (v, _) ->
            via_axis sp f v
            && match width_axis_enum f v with Some (_, e) -> e = en.en_name | None -> false)
          f.f_widths)
      sp.s_families
  in
  let refn =
    if needs_exact then
      String.concat " \\/ " (List.map (fun v -> sprintf "n = %d" v) vals)
    else sprintf "n <= %d" (List.fold_left max 0 vals)
  in
  sprintf "%s\n%s"
    (pp_sig (sprintf "let %s (%s: %s)" fn param en.en_name) (sprintf "n:pos{%s}" refn))
    (pp_match param
       (List.map (fun c -> ([ c.c_name ], string_of_int (case_bits en c))) en.en_cases))

(* ================================================================== *)
(* 5. Ebpf.Serialize                                                   *)
(* ================================================================== *)

let byte_lit n = sprintf "0x%02x" n

let enc_result field vals =
  if opcode_field field then
    sprintf "n:nat{n <= %s}" (byte_lit (List.fold_left max 0 vals))
  else "nat"

let enc_show field n = if opcode_field field then byte_lit n else string_of_int n

(* a table over an enum's `enc=` attributes (`cls`) *)
let enc_enum_table sp (en : enum) (fn : string) (param : string) =
  let rows = List.map (fun c -> (c.c_name, case_enc en c)) en.en_cases in
  sprintf "%s\n%s"
    (pp_sig
       (sprintf "let %s (%s: %s)" fn param en.en_name)
       (enc_result "cls" (List.map snd rows)))
    (pp_match param
       (List.map (fun (k, v) -> ([ k ], enc_show "cls" v)) rows))

(* a table over a family's KEY enum: the per-row value of one encoding
   field (`op_bits` = the `opc` column, `op_off` = the `off` column) *)
let enc_key_table (f : family) (field : string) (fn : string) =
  match f.f_key with
  | None -> None
  | Some (k, en) ->
    let rows =
      List.filter_map
        (fun (e : entry) ->
          match List.assoc_opt field e.e_enc_row with
          | Some (FSLit n) -> Some (e.e_name, n)
          | _ -> None)
        f.f_entries
    in
    if List.length rows <> List.length f.f_entries then None
    else
      let groups = group_rows (List.map (fun (n, v) -> (n, enc_show field v)) rows) in
      (* a strict-majority value becomes the `_` default, which is how
         `op_off` (0 for every row but SDIV/SMOD) is written today *)
      let n = List.length rows in
      let big =
        List.find_opt (fun (pats, _) -> 2 * List.length pats > n) groups
      in
      let arms =
        match big with
        | None -> groups
        | Some (_, rhs) ->
          List.filter (fun (_, r) -> r <> rhs) groups @ [ ([ "_" ], rhs) ]
      in
      Some
        (sprintf "%s\n%s"
           (pp_sig
              (sprintf "let %s (%s: %s)" fn k en)
              (enc_result field (List.map snd rows)))
           (pp_match k arms))

(* a table over an AXIS enum: the field is spelled `off = width f`, so each
   case contributes its own `bits=` value *)
let enc_width_table sp (f : family) (field : string) (fn : string) =
  let spelling =
    match List.assoc_opt field f.f_enc_family with
    | Some s -> Some s
    | None -> (
      match f.f_entries with
      | e :: _ -> List.assoc_opt field e.e_enc_row
      | [] -> None)
  in
  match spelling with
  | Some (FSWidth v) -> (
    match width_axis_enum f v with
    | None -> None
    | Some (ax, enm) ->
      let en = find_enum sp enm in
      let param =
        match List.assoc_opt enm width_table_name with Some (_, p) -> p | None -> ax
      in
      Some
        (sprintf "%s\n%s"
           (pp_sig
              (sprintf "let %s (%s: %s)" fn param enm)
              (enc_result field (List.map (fun c -> case_bits en c) en.en_cases)))
           (pp_match param
              (List.map
                 (fun c -> ([ c.c_name ], enc_show field (case_bits en c)))
                 en.en_cases))))
  | _ -> None

(* ================================================================== *)
(* 6. Regions                                                          *)
(* ================================================================== *)

(* Every generated region opens with this.  The spec name/version/host are
   IL data (DESIGN section 2.2: the little-endian host pin is load-bearing -
   it is what makes `ToLE` a truncation), so stamping them makes a generated
   region self-identifying, which is what the MS5 drift experiment reads. *)
let hdr (sp : spec) src =
  sprintf
    "(* GENERATED from %s by specgen \xe2\x80\x94 do not edit *)\n\
     (* spec %s v%d, host %s *)" src sp.s_name sp.s_version
    (match sp.s_host with Little -> "little-endian" | Big -> "big-endian")

let join parts = String.concat "\n" parts

let fam sp n =
  match List.find_opt (fun (f : family) -> f.f_name = n) sp.s_families with
  | Some f -> f
  | None -> failwith ("emit: no family " ^ n)

let get_opt = function Some x -> x | None -> failwith "emit: expected a definition"

(* the generated body of each region, keyed by region id *)
let regions (sp : spec) (src : string) : (string * string) list =
  let h = hdr sp src in
  let width_tables =
    List.filter_map
      (fun (en : enum) ->
        match List.assoc_opt en.en_name width_table_name with
        | None -> None
        | Some (fn, param) -> Some (width_table sp en fn param))
      sp.s_enums
  in
  (* the keyless (unfold) families, in spec order *)
  let inline_sems =
    List.filter_map
      (fun (f : family) -> if f.f_key = None then sem_fun sp f else None)
      sp.s_families
  in
  (* keyed families other than alu (swap_sem) *)
  let keyed_sems =
    List.filter_map
      (fun (f : family) ->
        if f.f_key <> None && f.f_name <> "alu" then sem_fun sp f else None)
      sp.s_families
  in
  let enc_enum_tables =
    List.filter_map
      (fun (en : enum) ->
        match List.assoc_opt en.en_name enc_enum_name with
        | None -> None
        | Some (fn, param) -> Some (enc_enum_table sp en fn param))
      sp.s_enums
  in
  let enc_key_tables =
    List.filter_map
      (fun ((famn, field), fn) -> enc_key_table (fam sp famn) field fn)
      enc_key_name
  in
  let enc_width_tables =
    List.filter_map
      (fun ((famn, field), fn) -> enc_width_table sp (fam sp famn) field fn)
      enc_width_name
  in
  [ ("semantics-alu", join (h :: "" :: [ get_opt (sem_fun sp (fam sp "alu")) ]));
    ( "semantics-tables",
      join ((h :: "" :: width_tables) @ keyed_sems @ inline_sems) );
    ( "semantics-defined",
      join (h :: "" :: [ get_opt (defined_fun sp (fam sp "alu")) ]) );
    ("serialize-opcode", join ((h :: "" :: enc_enum_tables) @ enc_key_tables));
    ("serialize-fields", join (h :: "" :: enc_width_tables)) ]

(* ================================================================== *)
(* 7. Splicing                                                         *)
(* ================================================================== *)

exception Splice of string

let begin_pfx = "(* BEGIN GENERATED "
let end_pfx = "(* END GENERATED "

let marker_id line pfx =
  let l = String.trim line in
  if String.length l < String.length pfx then None
  else if String.sub l 0 (String.length pfx) <> pfx then None
  else
    let rest = String.sub l (String.length pfx) (String.length l - String.length pfx) in
    match String.index_opt rest ' ' with
    | Some i -> Some (String.sub rest 0 i)
    | None -> Some rest

let split_lines s =
  let n = String.length s in
  let out = ref [] and start = ref 0 in
  for i = 0 to n - 1 do
    if s.[i] = '\n' then (
      out := String.sub s !start (i - !start) :: !out;
      start := i + 1)
  done;
  if !start < n then out := String.sub s !start (n - !start) :: !out;
  List.rev !out

let read_file p =
  let ic = open_in_bin p in
  let n = in_channel_length ic in
  let s = really_input_string ic n in
  close_in ic;
  s

let write_file p s =
  let oc = open_out_bin p in
  output_string oc s;
  close_out oc

(* Replace the text between each BEGIN/END marker pair with the generated
   body for that region id.  Missing, duplicated, unbalanced or unknown
   markers are FATAL: otherwise a deleted marker would make a region vanish
   from both the generated and the committed file, and the drift check
   (`make -C spec test`) would pass green on a spec that is no longer
   connected to the F* source. *)
let splice (file : string) (text : string) (bodies : (string * string) list) : string =
  let b = Buffer.create (String.length text + 4096) in
  let seen = ref [] in
  let rec go = function
    | [] -> ()
    | line :: rest -> (
      Buffer.add_string b (line ^ "\n");
      match marker_id line begin_pfx with
      | None ->
        (match marker_id line end_pfx with
         | Some id ->
           raise (Splice (sprintf "%s: END GENERATED %s without a matching BEGIN" file id))
         | None -> ());
        go rest
      | Some id ->
        if List.mem id !seen then
          raise (Splice (sprintf "%s: duplicate generated region `%s'" file id));
        seen := id :: !seen;
        let body =
          match List.assoc_opt id bodies with
          | Some x -> x
          | None ->
            raise
              (Splice
                 (sprintf "%s: unknown generated region `%s' (known: %s)" file id
                    (String.concat ", " (List.map fst bodies))))
        in
        Buffer.add_string b (body ^ "\n");
        (* skip the old body, keep the END marker *)
        let rec skip = function
          | [] -> raise (Splice (sprintf "%s: region `%s' has no END marker" file id))
          | l :: t -> (
            match marker_id l end_pfx with
            | Some id' when id' = id ->
              Buffer.add_string b (l ^ "\n");
              go t
            | Some id' ->
              raise (Splice (sprintf "%s: region `%s' closed by END %s" file id id'))
            | None -> (
              match marker_id l begin_pfx with
              | Some id' ->
                raise (Splice (sprintf "%s: region `%s' contains BEGIN %s" file id id'))
              | None -> skip t))
        in
        skip rest)
  in
  go (split_lines text);
  (!seen, Buffer.contents b) |> fun (s, out) ->
  let want = List.map fst bodies in
  let missing = List.filter (fun id -> not (List.mem id s)) want in
  if missing <> [] then
    raise
      (Splice
         (sprintf "%s: no BEGIN GENERATED marker for region(s) %s" file
            (String.concat ", " missing)));
  out

(* which regions belong to which file *)
let file_regions =
  [ ("Ebpf.Semantics.fst", [ "semantics-alu"; "semantics-tables"; "semantics-defined" ]);
    ("Ebpf.Serialize.fst", [ "serialize-opcode"; "serialize-fields" ]) ]

let emit (sp : spec) (src : string) (indir : string) (outdir : string) : string list =
  let all = regions sp src in
  List.map
    (fun (f, ids) ->
      let bodies = List.filter (fun (id, _) -> List.mem id ids) all in
      let inp = Filename.concat indir f in
      let out = splice inp (read_file inp) bodies in
      let dst = Filename.concat outdir f in
      write_file dst out;
      dst)
    file_regions
