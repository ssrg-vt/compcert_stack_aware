Require Import Smallstep.
Require Import Machregs.
Require Import Asm.
Require Import Integers.
Require Import List.
Require Import ZArith.
Require Import Memtype.
Require Import Memory.
Require Import Archi.
Require Import Coqlib.
Require Import AST.
Require Import Globalenvs.
Require Import Events.
Require Import Values.
Require Import Conventions1.
Require Import AsmFacts.
Require Import AsmDummyFrame.

Section WITHEXTERNALCALLS.
Context `{external_calls_prf: ExternalCalls}.

Variable init_sp: val.
Existing Instance mem_accessors_default.

Context `{injperm: InjectPerm}.

Inductive match_states: state -> state -> Prop :=
| match_states_intro:
    forall rs1 rs2 m1 m2
      (MEXT: Mem.extends m1 m2)
      (REGS: forall r, Val.lessdef (rs1 r) (rs2 r) ),
      match_states (State rs1 m1) (State rs2 m2).

Variable prog: Asm.program.

Let ge := Genv.globalenv prog.

Lemma mull_lessdef:
  forall v1 v2 v3 v4,
    Val.lessdef v1 v3 -> Val.lessdef v2 v4 ->
    Val.lessdef (Val.mull v1 v2) (Val.mull v3 v4).
Proof.
  inversion 1; inversion 1; subst; auto. unfold Val.mull.
  destr; auto.
Qed.

Lemma mul_lessdef:
  forall v1 v2 v3 v4,
    Val.lessdef v1 v3 -> Val.lessdef v2 v4 ->
    Val.lessdef (Val.mul v1 v2) (Val.mul v3 v4).
Proof.
  inversion 1; inversion 1; subst; auto. unfold Val.mul.
  destr; auto.
Qed.

Lemma eval_addrmode_extends:
  forall rs1 rs2 a,
    (forall r, Val.lessdef (rs1 r) (rs2 r)) ->
    Val.lessdef (eval_addrmode ge a rs1) (eval_addrmode ge a rs2).
Proof.
  unfold eval_addrmode. intros.
  destr.
  unfold eval_addrmode64.
  destr. apply Val.addl_lessdef. destr; auto.
  apply Val.addl_lessdef. repeat destr; auto.
  apply mull_lessdef; auto. auto.
  unfold eval_addrmode32.
  destr. apply Val.add_lessdef. destr; auto.
  apply Val.add_lessdef. repeat destr; auto.
  apply mul_lessdef; auto. auto.
Qed.

Lemma exec_load_extends:
  forall m1 m2 chunk a rs1 rs2 r rs1' m1',
    match_states (State rs1 m1) (State rs2 m2) ->
    exec_load ge chunk m1 a rs1 r = Next rs1' m1' ->
    exists rs2' m2',
      exec_load ge chunk m2 a rs2 r = Next rs2' m2'
      /\ match_states (State rs1' m1') (State rs2' m2').
Proof.
  intros m1 m2 chunk a rs1 rs2 r rs1' m1' MS EL.
  unfold exec_load in EL. destr_in EL. inv EL. inv MS.
  generalize (eval_addrmode_extends _ _ a REGS). intro ADDR.
  edestruct Mem.loadv_extends as (v2 & LOADV & LD). eauto. eauto. apply ADDR.
  unfold exec_load. rewrite LOADV. do 2 eexists; split; eauto.
  constructor; auto.
  unfold nextinstr_nf. simpl.
  intros. setoid_rewrite Pregmap.gsspec. destr.
  apply Val.offset_ptr_lessdef.
  setoid_rewrite Pregmap.gsspec. destr; eauto.
  intros. setoid_rewrite Pregmap.gsspec. destr. auto.
  repeat (setoid_rewrite Pregmap.gsspec; destr; eauto).
Qed.

Lemma is_freeframe i : {exists sz ora, i = Pfreeframe sz ora} + {forall sz ora, i <> Pfreeframe sz ora}.
Proof.
  destruct i; try (right; inversion 1; fail).
  left; eauto.
Qed.

Lemma exec_instr_step:
  forall rs1 m1 rs2 m2,
    match_states (State rs1 m1) (State rs2 m2) ->
    forall f i rs1' m1',
      Asm.exec_instr init_sp ge f i rs1 m1 = Next rs1' m1' ->
      exists rs2' m2',
        AsmDummyFrame.exec_instr init_sp ge f i rs2 m2 = Next rs2' m2' /\
        match_states (State rs1' m1') (State rs2' m2').
Proof.
  intros rs1 m1 rs2 m2 MS f i rs1' m1' EI.
  destruct (is_freeframe i).
  destruct e as (sz & ora & EQ). subst.
  - simpl in *. repeat (destr_in EI; [idtac]). inv EI.
    inv MS.
    edestruct Mem.loadv_extends as (v' & LOAD & LD); eauto.
    generalize (REGS RSP). rewrite Heqv0. inversion 1; subst.
    rewrite LOAD.

    edestruct (exec_load_extends) as (rs2' & m2' & LOADV & MS'); eauto.
    inv MS.

  destruct i; simpl in *; inv EI; inv MS; try (do 2 eexists; split; eauto; [idtac]); try (constructor; auto).
  


  - constructor; auto. intros. rewrite H4. unfold nextinstr.
    repeat (setoid_rewrite Pregmap.gsspec; try destr; try setoid_rewrite H4); auto.
  - constructor; auto. intros. unfold nextinstr_nf.
    repeat (setoid_rewrite Pregmap.gsspec; try destr; try setoid_rewrite H4); auto.
  - 
Qed.

  Inductive step (ge: genv) : state -> trace -> state -> Prop :=
  | exec_step_internal:
      forall b ofs f i rs m rs' m',
        rs PC = Vptr b ofs ->
        Genv.find_funct_ptr ge b = Some (Internal f) ->
        find_instr (Ptrofs.unsigned ofs) (fn_code f) = Some i ->
        exec_instr ge f i rs m = Next rs' m' ->
        step ge (State rs m) E0 (State rs' m')
  | exec_step_builtin:
      forall b ofs f ef args res rs m vargs t vres rs' m' m'',
        rs PC = Vptr b ofs ->
        Genv.find_funct_ptr ge b = Some (Internal f) ->
        find_instr (Ptrofs.unsigned ofs) f.(fn_code) = Some (Pbuiltin ef args res) ->
        eval_builtin_args ge rs (rs RSP) m args vargs ->
        external_call ef ge vargs (Mem.push_new_stage m) t vres m' ->
        Mem.unrecord_stack_block m' = Some m'' ->
        forall BUILTIN_ENABLED: builtin_enabled ef,
          no_rsp_builtin_preg res ->
          rs' = nextinstr_nf
                  (set_res res vres
                           (undef_regs (map preg_of (destroyed_by_builtin ef)) rs)) ->
          step ge (State rs m) t (State rs' m'')
  | exec_step_external:
      forall b ef args res rs m t rs' m' m'',
        rs PC = Vptr b Ptrofs.zero ->
        Genv.find_funct_ptr ge b = Some (External ef) ->
        extcall_arguments rs m (ef_sig ef) args ->
        forall (SP_TYPE: Val.has_type (rs RSP) Tptr)
          (RA_TYPE: Val.has_type (rs RA) Tptr)
          (SP_NOT_VUNDEF: rs RSP <> Vundef)
          (RA_NOT_VUNDEF: rs RA <> Vundef),
          external_call ef ge args m t res m' ->
          Mem.unrecord_stack_block m' = Some m'' ->
          no_rsp_pair (loc_external_result (ef_sig ef)) ->
          rs' = (set_pair (loc_external_result (ef_sig ef)) res (undef_regs (CR ZF :: CR CF :: CR PF :: CR SF :: CR OF :: nil) (undef_regs (map preg_of destroyed_at_call) rs))) #PC <- (rs RA) #RA <- Vundef ->
          step ge (State rs m) t (State rs' m'').

End RELSEM.

Definition semantics (p: Asm.program) :=
  Semantics step (initial_state p) final_state (Genv.globalenv p).

