(* ******************* *)
(* Author: Yuting Wang *)
(* Date:   Feb 7, 2018 *)
(* ******************* *)

(** Correctness proof for the FlatAsm generation **)

Require Import Coqlib Integers Values Maps AST.
Require Import Memtype Memory.
Require Import Asm RawAsmgen.
Require Import FlatAsm FlatAsmgen.
Require Import Sect.
Require Import Events.
Require Import StackADT.
Require Import Linking Errors.
Require Import Globalenvs FlatAsmGlobenv.
Require Import RawAsmgen.
Require Import AsmFacts.

Section WITHMEMORYMODEL.
  
Context `{memory_model: Mem.MemoryModel }.
Existing Instance inject_perm_upto_writable.

Definition match_prog (p: Asm.program) (tp: FlatAsm.program) :=
  transf_program p = OK tp.


Section PRESERVATION.

Variable prog: Asm.program.
Variable tprog: FlatAsm.program.
Hypothesis TRANSF: match_prog prog tprog.

Let ge := Genv.globalenv prog.
Let tge := globalenv tprog.

Definition regset_inject (j:meminj) (rs rs' : regset) : Prop :=
  forall r, Val.inject j (rs r) (rs' r).

(** Agreement between a memory injection from Asm to the flat memory and 
    the mappings for sections, global id and labels *)    
Record match_sminj (gm: GID_MAP_TYPE) (lm: LABEL_MAP_TYPE) (sm: section_map) (mj: meminj) : Type :=
  mk_match_sminj {
      (* agree_sminj : forall b id sid ofs ofs',  *)
      (*   Genv.find_symbol ge id = Some b -> *)
      (*   gm id = Some (sid,ofs) -> PTree.get sid sm = Some ofs' ->  *)
      (*   mj b = Some (mem_block, Ptrofs.unsigned (Ptrofs.add ofs ofs')); *)
 
      agree_sminj_instr :  forall b b' f ofs ofs' i,
          Genv.find_funct_ptr ge b = Some (Internal f) -> 
          Asm.find_instr (Ptrofs.unsigned ofs) (Asm.fn_code f) = Some i ->
          mj b = Some (b', ofs') -> 
          exists id i' ofs1, 
            Genv.find_instr tge (Ptrofs.add ofs (Ptrofs.repr ofs')) = Some i' /\
            Genv.find_symbol ge id = Some b /\
            transl_instr gm lm ofs1 id i = OK i';
    }.

Definition globs_inj_into_flatmem (mj:meminj) := 
  forall b g b' ofs',
    Genv.find_def ge b = Some g -> 
    mj b = Some (b', ofs') -> b' = mem_block.

Definition funs_inj_into_flatmem (mj:meminj) := 
  forall b f b' ofs',
    Genv.find_funct_ptr ge b = Some (Internal f) -> 
    mj b = Some (b', ofs') -> b' = mem_block.

Lemma globs_to_funs_inj_into_flatmem : forall (j:meminj),
    globs_inj_into_flatmem j -> funs_inj_into_flatmem j.
Proof.
  unfold globs_inj_into_flatmem, funs_inj_into_flatmem. 
  unfold Genv.find_funct_ptr. intros.
  destruct (Genv.find_def ge b) eqn: FDEF; try congruence.
  destruct g; try congruence. 
  inv H0. eapply H; eauto.
Qed.


Definition valid_instr_offset_is_internal (mj:meminj) :=
  forall b f ofs i ofs',
    Genv.find_funct_ptr ge b = Some (Internal f) ->
    find_instr (Ptrofs.unsigned ofs) (Asm.fn_code f) = Some i ->
    mj b = Some (mem_block, ofs') ->
    Genv.genv_is_instr_internal tge (Ptrofs.add ofs (Ptrofs.repr ofs')) = true.


Definition def_frame_inj m := (fun n => if lt_dec n (length (Mem.stack_adt m)) then Some O else None).

Inductive match_states: Asm.state -> FlatAsm.state -> Prop :=
| match_states_intro: forall (j:meminj) (rs: regset) (m: mem) (rs': regset) (m':mem)
                        (gm: GID_MAP_TYPE) (lm: LABEL_MAP_TYPE) (sm: section_map)
                        (MINJ: Mem.inject j (def_frame_inj m) m m')
                        (MATCHSMINJ: match_sminj gm lm sm j)
                        (GINJFLATMEM: globs_inj_into_flatmem j)
                        (INSTRINTERNAL: valid_instr_offset_is_internal j)
                        (RSINJ: regset_inject j rs rs'),
    match_states (State rs m) (State rs' m').


Context `{external_calls_ops : !ExternalCallsOps mem }.
Context `{!EnableBuiltins mem}.
Existing Instance Asm.mem_accessors_default.
Existing Instance FlatAsm.mem_accessors_default.

Lemma exec_instr_step : forall j rs1 rs2 m1 m2 rs1' m1' gm lm sm i i' id ofs f,
    regset_inject j rs1 rs2 ->
    Mem.inject j (def_frame_inj m1) m1 m2 ->
    match_sminj gm lm sm j ->
    RawAsmgen.exec_instr ge f i rs1 m1 = Next rs1' m1' ->
    transl_instr gm lm ofs id i = OK i' ->
    exists rs2' m2',
      FlatAsm.exec_instr tge i' rs2 m2 = Next rs2' m2' /\
      match_states (State rs1' m1') (State rs2' m2').
Admitted.

Lemma eval_builtin_arg_inject : forall gm lm sm j m m' rs rs' sp sp' arg varg arg',
    match_sminj gm lm sm j ->
    Mem.inject j (def_frame_inj m) m m' ->
    regset_inject j rs rs' ->
    Val.inject j sp sp' ->
    transl_builtin_arg gm arg = OK arg' ->
    eval_builtin_arg ge rs sp m arg varg ->
    exists varg', FlatAsmBuiltin.eval_builtin_arg _ _ preg tge rs' sp' m' arg' varg' /\
             Val.inject j varg varg'.
Admitted.

Lemma eval_builtin_args_inject : forall gm lm sm j m m' rs rs' sp sp' args vargs args',
    match_sminj gm lm sm j ->
    Mem.inject j (def_frame_inj m) m m' ->
    regset_inject j rs rs' ->
    Val.inject j sp sp' ->
    transl_builtin_args gm args = OK args' ->
    eval_builtin_args ge rs sp m args vargs ->
    exists vargs', FlatAsmBuiltin.eval_builtin_args _ _ preg tge rs' sp' m' args' vargs' /\
             Val.inject_list j vargs vargs'.
Admitted.


Lemma external_call_inject : forall j vargs1 vargs2 m1 m2 m1' vres1 t ef,
    Val.inject_list j vargs1 vargs2 ->
    Mem.inject j (def_frame_inj m1) m1 m2 ->
    external_call ef ge vargs1 m1 t vres1 m1' ->
    exists j' vres2 m2',
      external_call ef dummy_senv vargs2 m2 t vres2 m2' /\ 
      Val.inject j' vres1 vres2 /\ Mem.inject j' (def_frame_inj m1') m1' m2' /\
      inject_incr j j'.
Admitted.

Lemma regset_inject_incr : forall j j' rs rs',
    regset_inject j rs rs' ->
    inject_incr j j' ->
    regset_inject j' rs rs'.
Proof.
  unfold inject_incr, regset_inject. intros.
  specialize (H r).
  destruct (rs r); inversion H; subst; auto.
  eapply Val.inject_ptr. apply H0. eauto. auto.
Qed.

Lemma undef_regs_pres_inject : forall j rs rs' regs,
  regset_inject j rs rs' ->
  regset_inject j (undef_regs regs rs) (undef_regs regs rs').
Proof.
  unfold regset_inject. intros. apply val_inject_undef_regs.
  auto.
Qed.    

Lemma Pregmap_gsspec_alt : forall (A : Type) (i j : Pregmap.elt) (x : A) (m : Pregmap.t A),
    (m # j <- x) i  = (if Pregmap.elt_eq i j then x else m i).
Proof.
  intros. apply Pregmap.gsspec.
Qed.

Lemma set_res_pres_inject : forall res j rs1 rs2,
    regset_inject j rs1 rs2 ->
    forall vres1 vres2,
    Val.inject j vres1 vres2 ->
    regset_inject j (set_res res vres1 rs1) (set_res res vres2 rs2).
Proof.
  induction res; auto; simpl; unfold regset_inject; intros.
  - rewrite Pregmap_gsspec_alt. destruct (Pregmap.elt_eq r x); subst.
    + rewrite Pregmap.gss. auto.
    + rewrite Pregmap.gso; auto.
  - exploit (Val.hiword_inject j vres1 vres2); eauto. intros. 
    exploit (Val.loword_inject j vres1 vres2); eauto. intros.
    apply IHres2; auto.
Qed.


Lemma nextinstr_pres_inject : forall j rs1 rs2 sz,
    regset_inject j rs1 rs2 ->
    regset_inject j (nextinstr rs1 sz) (nextinstr rs2 sz).
Proof.
  unfold nextinstr, regset_inject. intros.
  repeat rewrite Pregmap_gsspec_alt.
  destruct (Pregmap.elt_eq r PC); subst; simpl.
  - unfold Val.offset_ptr. specialize (H PC). 
    destruct (rs1 PC); inversion H; subst; auto.
    rewrite <- H2 in *. 
    exploit Val.offset_ptr_inject; eauto.
  - auto.
Qed.


Theorem step_simulation:
  forall S1 t S2,
    RawAsmgen.step ge S1 t S2 ->
    forall S1' (MS: match_states S1 S1'),
    exists S2',
      FlatAsm.step tge S1' t S2' /\
      match_states S2 S2'.
Proof.
  destruct 1; intros; inv MS.

  - (* Internal step *)
    unfold regset_inject in RSINJ. generalize (RSINJ Asm.PC). rewrite H. 
    inversion 1; subst.
    exploit (agree_sminj_instr gm lm sm j MATCHSMINJ b b2 f ofs delta i); auto.
    intros (id & i' & ofs1 & FITARG & FSYMB & TRANSL).
    exploit (globs_to_funs_inj_into_flatmem j); eauto. inversion 1; subst.
    exploit (exec_instr_step j rs rs'0 m m'0 rs' m' gm lm sm i i' id ofs1 f); auto.
    intros (rs2' & m2' & FEXEC & MS1).
    exists (State rs2' m2'). split; auto.
    apply FlatAsm.exec_step_internal with (Ptrofs.add ofs (Ptrofs.repr delta)) i'; auto.
    unfold valid_instr_offset_is_internal in INSTRINTERNAL.
    apply INSTRINTERNAL with b f i; auto.
        
  - (* Builtin *)
    unfold regset_inject in RSINJ. generalize (RSINJ Asm.PC). rewrite H.
    inversion 1; subst.
    exploit (agree_sminj_instr gm lm sm j MATCHSMINJ b b2 f ofs delta (Asm.Pbuiltin ef args res, sz)); auto.
    intros (id & i' & ofs1 & FITARG & FSYMB & TRANSL).
    exploit (globs_to_funs_inj_into_flatmem j); eauto. inversion 1; subst.
    monadInv TRANSL. monadInv EQ.
    set (pbsect := {| sect_block_id := code_sect_id; sect_block_start := Ptrofs.repr ofs1; sect_block_size := Ptrofs.repr (si_size sz) |}).
    fold pbsect in FITARG.
    exploit (eval_builtin_args_inject gm lm sm j m m'0 rs rs'0 (rs Asm.RSP) (rs'0 Asm.RSP) args vargs x0); auto.
    intros (vargs' & EBARGS & ARGSINJ).
    generalize (external_call_inject j vargs vargs' m m'0 m' vres t ef ARGSINJ MINJ H3).
    intros (j' & vres2 & m2' & EXTCALL & RESINJ & MINJ' & INJINCR).
    set (rs' := nextinstr_nf (set_res res vres2 (undef_regs (map preg_of (Machregs.destroyed_by_builtin ef)) rs'0)) (sect_block_size pbsect)).
    exploit (FlatAsm.exec_step_builtin tge (Ptrofs.add ofs (Ptrofs.repr delta))
                                       ef x0 res rs'0  m'0 vargs' t vres2 rs' m2' pbsect); auto.
    unfold valid_instr_offset_is_internal in INSTRINTERNAL.
    eapply INSTRINTERNAL; eauto.
    intros FSTEP. eexists; split; eauto.
    eapply match_states_intro with (j:=j'); eauto.
    (* Supposely the following propreties can proved by separation property of injections *)
    + admit.
    + admit.
    + admit.
    + subst rs'. unfold regset_inject. intros. subst pbsect; simpl.
      unfold nextinstr_nf, Asm.nextinstr_nf.
      assert (regset_inject j' rs rs'0) by 
          (eapply regset_inject_incr; eauto).
      set (dregs := (map Asm.preg_of (Machregs.destroyed_by_builtin ef))) in *.
      unfold preg_of. fold dregs.
      generalize (undef_regs_pres_inject j' rs rs'0 dregs H5). intros.
      unfold undef_regs. unfold set_res.

      
      set (rs1 := (Asm.undef_regs dregs rs)) in *.
      set (rs2 := (Asm.undef_regs dregs rs'0)) in *.
      generalize (set_res_pres_inject res j' 
                  rs1 rs2 H9 vres vres2 RESINJ).
      set (rs3 := (Asm.set_res res vres rs1)) in *.
      set (rs4 := (Asm.set_res res vres2 rs2)) in *.
      intros.
      fold ZF CF PF SF OF.
      set (fregs := (CR ZF :: CR CF :: CR PF :: CR SF :: CR OF :: nil)) in *.
      generalize (undef_regs_pres_inject j' rs3 rs4 fregs H10).
      intros.         
      generalize (nextinstr_pres_inject j'  
                    (undef_regs fregs rs3) (undef_regs fregs rs4) 
                    (Ptrofs.repr (si_size sz)) H11).
      intros. unfold regset_inject in H12.
      apply H12.

  - (* External call *)
    admit.

Admitted.

End PRESERVATION.

End WITHMEMORYMODEL.