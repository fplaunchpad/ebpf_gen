(* bpfc — Keel DSL front-end + corpus generator (M2.3.4).
   For each high-level Ebpf.Dsl program it uses the extracted verified
   lowering (Ebpf_Lower) + emitter (Ebpf_Emit) + serializer (Ebpf_Serialize)
   to produce: a `.kir` file, the eBPF bytecode (hex), and the EXPECTED
   result (the reference evaluator Ebpf_Dsl.run, truncated to u32 like the
   kernel's BPF_PROG_TEST_RUN retval). It writes a manifest the kernel-side
   harness uses to check that each program (a) certifies (via irc), (b) loads,
   and (c) actually computes the predicted value. *)

module D = Ebpf_Dsl
module L = Ebpf_Lower
module E = Ebpf_Emit
module S = Ebpf_Serialize

let u = Stdint.Uint64.of_int
let c (n: int) : D.expr = D.Const (u n)
let two32 = Stdint.Uint64.of_string "4294967296"
let vi = Z.of_int                       (* var ids are Prims.nat = Z.t *)
let var (i: int) : D.expr = D.Var (vi i)
let letv (i: int) (e: D.expr) : D.stmt = D.Let (vi i, e)
let assrt (i: int) (b: int) : D.stmt = D.Assert (var i, u b)
let bin op a b = D.Bin (op, a, b)

(* --- corpus: varied straight-line ALU programs --- *)
(* each ends in `Assert (Var vf) bound; Ret (Var vf)` with a true bound. *)
let corpus : (string * D.prog) list = [
  "mul",      [ letv 0 (c 6); letv 1 (c 7); letv 2 (bin D.Mul (var 0) (var 1));
                assrt 2 42; D.Ret (var 2) ];
  "add",      [ letv 0 (c 100); letv 1 (c 50); letv 2 (bin D.Add (var 0) (var 1));
                assrt 2 150; D.Ret (var 2) ];
  "sub",      [ letv 0 (c 100); letv 1 (c 30); letv 2 (bin D.Sub (var 0) (var 1));
                assrt 2 70; D.Ret (var 2) ];
  "and",      [ letv 0 (c 255); letv 1 (c 60); letv 2 (bin D.And (var 0) (var 1));
                assrt 2 60; D.Ret (var 2) ];
  "or",       [ letv 0 (c 12); letv 1 (c 3); letv 2 (bin D.Or (var 0) (var 1));
                assrt 2 15; D.Ret (var 2) ];
  "xor",      [ letv 0 (c 15); letv 1 (c 6); letv 2 (bin D.Xor (var 0) (var 1));
                assrt 2 9; D.Ret (var 2) ];
  "div",      [ letv 0 (c 100); letv 1 (c 4); letv 2 (bin D.Div (var 0) (var 1));
                assrt 2 25; D.Ret (var 2) ];
  "mod",      [ letv 0 (c 100); letv 1 (c 7); letv 2 (bin D.Mod (var 0) (var 1));
                assrt 2 2; D.Ret (var 2) ];
  "lsh",      [ letv 0 (c 3); letv 1 (c 4); letv 2 (bin D.Lsh (var 0) (var 1));
                assrt 2 48; D.Ret (var 2) ];
  "rsh",      [ letv 0 (c 200); letv 1 (c 2); letv 2 (bin D.Rsh (var 0) (var 1));
                assrt 2 50; D.Ret (var 2) ];
  "chain",    [ letv 0 (c 10); letv 1 (c 20);
                letv 2 (bin D.And (bin D.Mul (var 0) (var 1)) (c 255));
                assrt 2 200; D.Ret (var 2) ];
  "poly",     [ letv 0 (bin D.Div (bin D.Add (bin D.Mul (c 6) (c 7)) (c 8)) (c 5));
                assrt 0 10; D.Ret (var 0) ];
  "mask_add", [ letv 0 (bin D.Add (bin D.And (c 255) (c 100)) (c 1));
                assrt 0 101; D.Ret (var 0) ];
  "big",      [ letv 0 (bin D.Mul (c 50000) (c 50000));
                D.Assert (var 0, u 2500000000); D.Ret (var 0) ];
  (* deeply-nested "comprehensive" expressions (single Let, one assert) *)
  (* nest_arith = ((2*3 + 4*5) * ((10-3) + 20/4)) = 26*12 = 312 *)
  "nest_arith", [ letv 0 (bin D.Mul
                    (bin D.Add (bin D.Mul (c 2) (c 3)) (bin D.Mul (c 4) (c 5)))
                    (bin D.Add (bin D.Sub (c 10) (c 3)) (bin D.Div (c 20) (c 4))));
                  assrt 0 312; D.Ret (var 0) ];
  (* nest_chain = ((((((1+2)*3)+4)*5)+6)*7) = 497 (left-heavy) *)
  "nest_chain", [ letv 0 (bin D.Mul (bin D.Add (bin D.Mul (bin D.Add
                    (bin D.Mul (bin D.Add (c 1) (c 2)) (c 3)) (c 4)) (c 5)) (c 6)) (c 7));
                  assrt 0 497; D.Ret (var 0) ];
  (* nest_mask = ((6*7 + 8) * (100/4 - 5)) & 0xff = (50 * 20) & 255 = 1000 & 255 = 232 *)
  "nest_mask",  [ letv 0 (bin D.And
                    (bin D.Mul (bin D.Add (bin D.Mul (c 6) (c 7)) (c 8))
                               (bin D.Sub (bin D.Div (c 100) (c 4)) (c 5)))
                    (c 255));
                  assrt 0 232; D.Ret (var 0) ];
  (* nest_bits = ((0xf0 | 0x0f) ^ 0xaa) & 0xff = (255 ^ 170) & 255 = 85 *)
  "nest_bits",  [ letv 0 (bin D.And (bin D.Xor (bin D.Or (c 240) (c 15)) (c 170)) (c 255));
                  assrt 0 85; D.Ret (var 0) ];
]

let expected (p: D.prog) : string =
  match D.run p with
  | FStar_Pervasives_Native.Some v -> Stdint.Uint64.to_string (Stdint.Uint64.rem v two32)
  | FStar_Pervasives_Native.None -> "novalue"

let hex (p: D.prog) : string option =
  match L.lower p with
  | FStar_Pervasives_Native.Some prog -> Some (S.serialize_hex prog)
  | FStar_Pervasives_Native.None -> None

let () =
  let dir = "../examples/corpus" in
  (try Unix.mkdir dir 0o755 with _ -> ());
  let man = open_out (dir ^ "/manifest.tsv") in
  List.iter (fun (name, p) ->
    match E.emit_dsl p, hex p with
    | FStar_Pervasives_Native.Some kir, Some hx ->
      let oc = open_out (dir ^ "/" ^ name ^ ".kir") in
      output_string oc kir; close_out oc;
      Printf.fprintf man "%s\t%s\t%s\n" name hx (expected p);
      Printf.printf "generated %-10s expected=%s\n" name (expected p)
    | _ -> Printf.printf "%-10s: lowering failed (skipped)\n" name) corpus;
  close_out man;
  Printf.printf "wrote %s/manifest.tsv (%d programs)\n" dir (List.length corpus)
