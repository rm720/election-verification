(*print the command commitment
 start output window meta h H
 *)
 
open preamble basis;
open instancePlayTheory;
open groupInstancesTheory;

val _ = new_theory "cryptoProg";

val _ = translation_extends"basisProg";


val _ = translate z_code_def;
val _ = translate z_code_string_def;

val crypto = process_topdecs
             ‘fun crypto u = TextIO.print(z_code_string 11 2 3 4 5)’
             
val () = append_prog crypto;
val st = get_ml_prog_state();


Theorem crypto_spec: 
   app (p:'ffi ffi_proj) ^(fetch_v "crypto" st) [Conv NONE []]
   (STDIO fs * COMMANDLINE cl)
   (POSTv uv. &UNIT_TYPE () uv *
      STDIO (add_stdout fs (num_to_str( z_code 11 2 3 4 5) ^ strlit"\n")) *
      COMMANDLINE cl)
Proof
   xcf "crypto" st >>
   xlet_auto >-
    xsimpl >>
   gs[z_code_string_def] >>
   xapp >> xsimpl >>  first_assum $ irule_at Any >> qexists_tac‘fs’ >> qexists_tac‘COMMANDLINE cl’ >> xsimpl
QED
            
Theorem crypto_spec' = SIMP_RULE (srw_ss())[crypto_math_spec, ASSUME“prime 11”] crypto_spec 
   
Theorem crypto_whole_prog_spec:
   whole_prog_spec ^(fetch_v "crypto" st) cl fs NONE
    ((=) (add_stdout fs (toString (z_commit 11 2 3 4 5) ^ «\n» )))
Proof
  rw[whole_prog_spec_def]
  \\ qmatch_goalsub_abbrev_tac`fs1 = _ with numchars := _`
  \\ qexists_tac`fs1`
  \\ simp[Abbr`fs1`,GSYM add_stdo_with_numchars,with_same_numchars]
  \\ ‘prime 11’ by cheat
  \\ match_mp_tac (MP_CANON (MATCH_MP app_wgframe crypto_spec'))
  \\ xsimpl
QED

val spec = crypto_whole_prog_spec;
val name = "crypto";

val (call_thm_crypto, crypto_prog_tm) = whole_prog_thm st name spec;
val crypto_prog_def = Define`crypto_prog = ^crypto_prog_tm`;

val crypto_semantics = save_thm("crypto_semantics",
  call_thm_crypto |> ONCE_REWRITE_RULE[GSYM crypto_prog_def]
  |> DISCH_ALL
  |> SIMP_RULE std_ss [AND_IMP_INTRO,GSYM CONJ_ASSOC]);

val _ = export_theory();

