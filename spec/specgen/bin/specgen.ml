(* specgen - the (untrusted) KeelSpec checker.

   specgen check    <file.kspec>       parse, elaborate, run meta-checks K1-K9
   specgen list     <file.kspec>       print the flattened instance table
   specgen astcheck <Ebpf.Ast.fst>     diff the built-in AST table vs the real one
   specgen emit     <file.kspec> <fstar-dir> <out-dir>
                                       splice the generated F* regions of
                                       Ebpf.Semantics.fst / Ebpf.Serialize.fst *)

open Keelspec

let usage () =
  prerr_endline
    "usage:\n\
    \  specgen check    <file.kspec>\n\
    \  specgen list     <file.kspec>\n\
    \  specgen astcheck <path/to/Ebpf.Ast.fst>\n\
    \  specgen emit     <file.kspec> <fstar-dir> <out-dir>";
  exit 2

let names l = String.concat ", " l

let summary (file : string) (sp : Il.spec) (log : string list) =
  let fams = sp.Il.s_families in
  let nent = List.fold_left (fun a f -> a + List.length f.Il.f_entries) 0 fams in
  let per_fam =
    List.map
      (fun f ->
        let n =
          List.length (List.filter (fun i -> i.Il.i_family = f.Il.f_name) sp.Il.s_instances)
        in
        let x = List.length f.Il.f_excludes in
        if x = 0 then Printf.sprintf "%s %d" f.Il.f_name n
        else Printf.sprintf "%s %d (+%d excluded)" f.Il.f_name n x)
      fams
  in
  Printf.printf "spec %s v%d\n" sp.Il.s_name sp.Il.s_version;
  Printf.printf "  isa        %s\n" sp.Il.s_isa;
  Printf.printf "  host       %s\n"
    (match sp.Il.s_host with Il.Little -> "little-endian" | Il.Big -> "big-endian");
  Printf.printf "  enums      %d   (%s)\n" (List.length sp.Il.s_enums)
    (names (List.map (fun (e : Il.enum) -> e.Il.en_name) sp.Il.s_enums));
  Printf.printf "  families   %d   (%s)\n" (List.length fams)
    (names (List.map (fun f -> f.Il.f_name) fams));
  Printf.printf "  entries    %d\n" nent;
  Printf.printf "  instances  %d   %s\n" (List.length sp.Il.s_instances) (names per_fam);
  print_endline "checks:";
  List.iter (fun l -> Printf.printf "  %s\n" l) log;
  Printf.printf "OK: %s - %d entries, %d instances, %d checks passed.\n" file nent
    (List.length sp.Il.s_instances) (List.length log)

(* the structured view: what the F* backend prints from, and how each family
   SPELLS its encoding fields before instantiation (what MS3 reads) *)
let list_families (sp : Il.spec) =
  List.iter
    (fun (f : Il.family) ->
      Printf.printf "family %s  ctor %s%s%s\n" f.Il.f_name f.Il.f_ctor
        (match f.Il.f_key with Some (v, e) -> Printf.sprintf "  key %s:%s" v e | None -> "")
        (if f.Il.f_axes = [] then ""
         else
           "  axes "
           ^ names (List.map (fun (v, e) -> v ^ ":" ^ e) f.Il.f_axes));
      Printf.printf "  widths:     %s\n"
        (names (List.map (fun (w, a) -> Printf.sprintf "%s = bits %s" w a) f.Il.f_widths));
      Printf.printf "  enc family: %s\n"
        (names
           (List.map (fun (k, v) -> k ^ " = " ^ Il.fieldsrc_str v) f.Il.f_enc_family));
      List.iter
        (fun (e : Il.entry) ->
          Printf.printf "  entry %-6s enc row: %-28s defined: %s\n" e.Il.e_name
            (if e.Il.e_enc_row = [] then "(none)"
             else
               names (List.map (fun (k, v) -> k ^ " = " ^ Il.fieldsrc_str v) e.Il.e_enc_row))
            (Il.cond_str e.Il.e_defined))
        f.Il.f_entries;
      List.iter
        (fun (binds, reason) ->
          Printf.printf "  excluded:   %s  (%s)\n"
            (names (List.map (fun (a, c) -> a ^ "=" ^ c) binds))
            reason)
        f.Il.f_excludes)
    sp.Il.s_families

let list_instances (sp : Il.spec) =
  List.iter
    (fun (i : Il.instance) ->
      let args =
        String.concat ","
          (List.map
             (fun (n, v) ->
               match v with
               | Il.AEnum (_, c) -> c
               | Il.ARole Il.RDst -> "dst"
               | Il.ARole Il.RSrcReg -> "src"
               | Il.ARole Il.RSrcOperand -> "src")
             i.Il.i_args)
      in
      Printf.printf "%-22s %s(%s)\n" i.Il.i_id i.Il.i_ctor args;
      Printf.printf "  opcode=%s  %s\n"
        (if i.Il.i_opcode >= 0 then Printf.sprintf "0x%02x" i.Il.i_opcode else "?")
        (Elab.enc_str i.Il.i_enc);
      Printf.printf "  widths: %s\n"
        (names (List.map (fun (v, n) -> Printf.sprintf "%s=%d" v n) i.Il.i_widths));
      Printf.printf "  reads:  %s\n"
        (names
           (List.map
              (fun (r : Il.read) ->
                Printf.sprintf "%s = %s@%s" r.Il.r_var (Il.role_str r.Il.r_role)
                  (Il.wexp_str r.Il.r_width))
              i.Il.i_reads));
      Printf.printf "  sem:    %s : %s\n" (Il.expr_str i.Il.i_sem) (Il.ty_str i.Il.i_result);
      Printf.printf "  defined: %s\n" (Il.cond_str i.Il.i_defined);
      if i.Il.i_obligs <> [] then
        Printf.printf "  obligations: %s\n" (names (List.map Il.oblig_str i.Il.i_obligs)))
    sp.Il.s_instances

let astcheck (file : string) =
  let drift = Astref.drift_check file in
  if drift = [] then begin
    Printf.printf
      "OK: specgen's Ebpf.Ast reference table matches %s\n  constructors %s (pseudo/terminal: %s)\n"
      file (Astref.ctor_list_str ()) (Astref.pseudo_list_str ());
    exit 0
  end
  else begin
    Printf.eprintf "%s: specgen's Ebpf.Ast reference table has DRIFTED\n" file;
    List.iter
      (fun (d : Astref.drift) ->
        Printf.eprintf "  type %s:\n" d.Astref.d_type;
        if d.Astref.d_only_spec <> [] then
          Printf.eprintf "    in spec, not in AST: %s\n"
            (String.concat ", " d.Astref.d_only_spec);
        if d.Astref.d_only_ast <> [] then
          Printf.eprintf "    in AST, not in spec: %s\n"
            (String.concat ", " d.Astref.d_only_ast);
        if d.Astref.d_order then
          Printf.eprintf "    same cases, different order\n")
      drift;
    prerr_endline "  fix spec/specgen/lib/astref.ml (DESIGN.md section 7)";
    exit 1
  end

let () =
  match Array.to_list Sys.argv with
  | _ :: "check" :: file :: [] ->
    (try
       let sf = Parse.parse_file file in
       let sp, log = Elab.elab sf in
       summary file sp log
     with
     | Kpos.Kerr (p, m) -> prerr_string (Kpos.render p m); exit 1
     | Sys_error m -> prerr_endline m; exit 1
     | e -> Printf.eprintf "specgen internal error: %s\n" (Printexc.to_string e); exit 3)
  | _ :: "list" :: file :: [] ->
    (try
       let sf = Parse.parse_file file in
       let sp, _ = Elab.elab sf in
       list_families sp;
       print_newline ();
       list_instances sp
     with
     | Kpos.Kerr (p, m) -> prerr_string (Kpos.render p m); exit 1
     | Sys_error m -> prerr_endline m; exit 1
     | e -> Printf.eprintf "specgen internal error: %s\n" (Printexc.to_string e); exit 3)
  | _ :: "astcheck" :: file :: [] ->
    (try astcheck file with Sys_error m -> prerr_endline m; exit 1)
  | _ :: "emit" :: file :: indir :: outdir :: [] ->
    (try
       let sf = Parse.parse_file file in
       let sp, _ = Elab.elab sf in
       let src = "spec/" ^ Filename.basename file in
       let written = Emit_fstar.emit sp src indir outdir in
       List.iter (fun p -> Printf.printf "emitted %s\n" p) written
     with
     | Kpos.Kerr (p, m) -> prerr_string (Kpos.render p m); exit 1
     | Emit_fstar.Splice m -> Printf.eprintf "specgen emit: %s\n" m; exit 1
     | Failure m -> Printf.eprintf "specgen emit: %s\n" m; exit 1
     | Sys_error m -> prerr_endline m; exit 1
     | e -> Printf.eprintf "specgen internal error: %s\n" (Printexc.to_string e); exit 3)
  | _ -> usage ()
