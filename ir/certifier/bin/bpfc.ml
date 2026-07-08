(* bpfc — the Keel DSL front-end driver (M2.3.3/M2.3.4 scaffold).
   Emits .kir text from high-level Ebpf.Dsl programs via the extracted
   verified lowering (Ebpf_Lower) + emitter (Ebpf_Emit). The generated .kir
   is then certified by `irc` (which runs the verified checker). *)

module E = Ebpf_Emit
module D = Ebpf_Dsl

let write (name: string) (prog: D.prog) : unit =
  match E.emit_dsl prog with
  | FStar_Pervasives_Native.Some s ->
    let f = "../examples/dsl_" ^ name ^ ".kir" in
    let oc = open_out f in
    output_string oc s;
    close_out oc;
    Printf.printf "wrote %s (%d bytes)\n" f (String.length s)
  | FStar_Pervasives_Native.None ->
    Printf.printf "%s: lowering failed (register/constant cap)\n" name

let () =
  write "mul" D.ex_mul;
  write "chain" D.ex_chain;
  write "div" D.ex_div;
  write "nested" D.ex_nested
