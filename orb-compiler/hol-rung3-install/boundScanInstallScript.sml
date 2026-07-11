(* ===========================================================================
   CN Rung-3 INSTALL — discharge the runtime-install antecedent of the
   boundscan Rung-3 backbone (`boundScan_rung3_native`) for the CONCRETE x64
   machine config, against the REAL x64_configProof well-formedness lemmas.

   Ground: boundScanRung3Theory.boundScan_rung3_native
     (machine_sem mc ffi ms ⊆ … {semantics_decls s «main» boundScanProg};
      31 antecedent conjuncts = G1 [native-bytes compile_prog_max] + the
      runtime install package + non-failure; [oracles: DISK_THM] [axioms:]).

   This theory INSTANTIATES the backbone at the concrete x64 backend config
   (c := x64_backend_config) under `is_x64_machine_config mc`, and DISCHARGES
   the config-well-formedness core of the install package using the real
   CakeML x64 lemmas (x64_configProofTheory):
     - backend_config_ok mc.target.config c   (x64_backend_config_ok)
     - mc_conf_ok mc                          (x64_machine_config_ok)
     - mc_init_ok mc.target.config c mc        (x64_init_ok)
     - mc.target.config.ISA ≠ Ag32            (EVAL x64_config)
     - OPTION_ALL … c.lab_conf.ffi_names      (EVAL x64_backend_config)
   and simplifies the endianness conjunct to the little-endian constraint
   `¬s.be`, and folds `start := «main»`.

   The RESIDUAL is named precisely (§ the dump): G1 (the native-bytes
   compile_prog_max equation — separately discharged by
   boundScanPkgTheory.boundScan_G1_native, oracle cake_native_bootstrap), the
   placed-image geometry (`pan_installed …` + the register/heap/globals/bitmap
   layout + alignment), the initial-state boilerplate (s.code/locals/globals =
   FEMPTY, eshapes, ffi, ¬s.be), and non-failure.  The geometry + pan_installed
   is the irreducible loader / target-config contract — exactly what CakeML's
   own end-to-end examples leave as the `installed` hypothesis (helloProof
   DISCH_ALLs it against a concrete placed image); it cannot be discharged
   in-logic while `ms`/`s` stay symbolic, and is NOT faked here.
   =========================================================================== *)

open HolKernel boolLib bossLib Parse;
open panLangTheory panSemTheory;
open pan_to_targetProofTheory;
open x64_configProofTheory x64_configTheory x64_targetTheory;
open boundScanRung3Theory;

val _ = new_theory "boundScanInstall";

(* --- mc.target.config = x64_config from the x64 machine-config predicate --- *)
Theorem mc_target_config_x64:
  is_x64_machine_config mc ⇒ mc.target.config = x64_config
Proof
  rw [x64_configProofTheory.is_x64_machine_config_def]
  \\ rw [x64_targetTheory.x64_target_def]
QED

(* --- the config-level well-formedness facts (over x64_config after rewrite) --- *)
Theorem bs_isa_not_ag32:
  x64_config.ISA ≠ Ag32
Proof
  EVAL_TAC
QED

Theorem bs_ffi_names_extcall:
  OPTION_ALL (EVERY (λx. ∃s. x = ExtCall s)) x64_backend_config.lab_conf.ffi_names
Proof
  EVAL_TAC
QED

Theorem bs_big_endian_F:
  x64_config.big_endian = F
Proof
  EVAL_TAC
QED

(* --- the reduced backbone: install well-formedness core discharged --------- *)
val mc_conf_ok_uh  = UNDISCH x64_configProofTheory.x64_machine_config_ok;
val mc_init_ok_uh  = UNDISCH x64_configProofTheory.x64_init_ok;
val backend_ok_th  = x64_configProofTheory.x64_backend_config_ok;

(* The backbone's mc is (64,β,γ) machine_config (polymorphic target-state β);
   is_x64_machine_config mc forces mc to the concrete x64 target-state type.
   Fix β := that type BEFORE rewriting/discharging, else the rewrite silently
   no-ops on a type mismatch. *)
val mctc_uh = UNDISCH mc_target_config_x64;
val x64_mc_ty = type_of (rand (hd (hyp mctc_uh)));   (* mc @ x64 target-state *)
val bb_inst   = boundScanRung3Theory.boundScan_rung3_native
                |> Q.INST [`c` |-> `x64_backend_config`, `start` |-> `«main»`];
(* the backbone's own mc (from its mc_conf_ok conjunct) *)
val bb_mc =
  let val (ante,_) = dest_imp (concl bb_inst)
      val conjs = strip_conj ante
      val t = valOf (List.find
        (fn t => (fst (dest_const (fst (strip_comb t))) = "mc_conf_ok")
                 handle _ => false) conjs)
  in rand t end;
val tyinst = match_type (type_of bb_mc) x64_mc_ty;

val reduced =
  bb_inst
  |> INST_TYPE tyinst
  |> REWRITE_RULE [mctc_uh]
  |> SIMP_RULE bool_ss
       (bs_big_endian_F ::
        map EQT_INTRO
          [backend_ok_th, mc_conf_ok_uh, mc_init_ok_uh,
           bs_isa_not_ag32, bs_ffi_names_extcall]);

val boundScan_rung3_installed =
  save_thm ("boundScan_rung3_installed", reduced |> DISCH_ALL);

(* --- verification dump ----------------------------------------------------- *)
val _ =
  let val os = TextIO.openOut "install.out"
      fun p s = TextIO.output (os, s)
      fun tagstr th =
        let val (orc, ax) = Tag.dest_tag (Thm.tag th)
        in "[oracles: " ^ String.concatWith "," orc ^ "] [axioms: "
           ^ String.concatWith "," ax ^ "]" end
      fun countante th =
        let val c = concl th
        in if is_imp c
           then length (strip_conj (#1 (dest_imp c)))
           else 0 end
  in
    p ("=== mc_target_config_x64 ===\n"
       ^ thm_to_string mc_target_config_x64 ^ "\n" ^ tagstr mc_target_config_x64 ^ "\n\n");
    p ("=== boundScan_rung3_native (ground backbone) ===\n"
       ^ tagstr boundScanRung3Theory.boundScan_rung3_native ^ "\n"
       ^ "antecedent conjuncts = "
       ^ Int.toString (countante boundScanRung3Theory.boundScan_rung3_native) ^ "\n\n");
    p ("=== boundScan_rung3_installed (this lane) ===\n"
       ^ tagstr boundScan_rung3_installed ^ "\n");
    p ("hyps = " ^ Int.toString (length (hyp reduced)) ^ "\n");
    List.app (fn h => p ("  hyp: " ^ term_to_string h ^ "\n")) (hyp reduced);
    let val c = concl reduced
    in if is_imp c then
         let val (ante, conc) = dest_imp c
             val conjs = strip_conj ante
         in
           p ("reduced antecedent conjuncts = " ^ Int.toString (length conjs) ^ "\n");
           p ("--- residual antecedents (the install geometry + G1 + boilerplate) ---\n");
           List.app (fn t => p ("  * " ^ term_to_string t ^ "\n")) conjs;
           p ("\nconclusion:\n" ^ term_to_string conc ^ "\n")
         end
       else p ("NON-IMP concl:\n" ^ term_to_string c ^ "\n")
    end;
    p ("\ntheory axioms (boundScanInstall) = "
       ^ Int.toString (length (axioms "boundScanInstall")) ^ "\n");
    TextIO.closeOut os
  end;

val _ = export_theory ();
