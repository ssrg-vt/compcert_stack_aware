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
Require Import RawAsm.

Section WITHMEMORYMODEL.
  
  Context `{memory_model: Mem.MemoryModel }.
  Existing Instance inject_perm_upto_writable.

  Context `{external_calls_ops : !ExternalCallsOps mem }.
  Context `{!EnableBuiltins mem}.

  Existing Instance mem_accessors_default.
  Existing Instance symbols_inject_instance.
  Context `{external_calls_props : !ExternalCallsProps mem
                                    (memory_model_ops := memory_model_ops)
                                    }.

  Variable prog: Asm.program.
  Let ge := Genv.globalenv prog.
  Definition bstack := Genv.genv_next ge.
  Section PRESERVATION.

  Variable init_stk: stack_adt.
  Definition init_sp: val := current_sp init_stk.
  Variable binit_sp: block.
  Hypothesis init_sp_ptr: init_sp = Vptr binit_sp Ptrofs.zero.

  Lemma type_init_sp:
    Val.has_type init_sp Tptr.
  Proof.
    unfold init_sp, current_sp, current_frame_sp.
    repeat destr; eauto using Val.Vnullptr_has_type, Val.Vptr_has_type.
  Qed.

  Lemma init_sp_zero:
    forall b o,
      init_sp = Vptr b o -> o = Ptrofs.zero.
  Proof.
    intros. rewrite init_sp_ptr in H. inv H; auto.
  Qed.

  Definition is_unchanged (i:instr_with_info) :=
    let '(i,_) := i in
    match i with
      Pallocframe _ _
    | Pfreeframe _ _
    | Pload_parent_pointer _ _
    | Pcall_s _ _
    | Pcall_r _ _
    | Pret => false
    | _ => true
    end.

  Lemma is_unchanged_exec:
    forall (ge: Genv.t Asm.fundef unit) f rs m i istk,
      is_unchanged i = true ->
      exec_instr ge f i rs m = Asm.exec_instr istk ge f i rs m.
  Proof.
    destruct i. destruct i; simpl; intros; try reflexivity; try congruence.
  Qed.
 
  Definition no_inject_below j m thr:=
    forall b delta o k p,
      j b = Some (bstack, delta) ->
      Mem.perm m b o k p ->
      thr <= o + delta /\ in_stack (Mem.stack_adt m) b.

  Definition agree_sp m1 rs2:=
    forall ostack,
      rs2 # RSP = Vptr bstack ostack ->
      Ptrofs.unsigned ostack = Mem.stack_limit - StackADT.size_stack (Mem.stack_adt m1).

  Definition perm_bstack m2:=
    forall (ofs : Z) (k : perm_kind) (p : permission),
       Mem.perm m2 bstack ofs k p -> 0 <= ofs < Ptrofs.max_unsigned /\ perm_order Writable p.

  Definition perm_bstack_stack_limit m2:=
    forall (ofs : Z) (k : perm_kind),
      0 <= ofs < Mem.stack_limit ->
      Mem.perm m2 bstack ofs k Writable.

  Definition sp_aligned rs2:=
    forall ostack,
      rs2 # RSP = Vptr bstack ostack ->
      (8 | Ptrofs.unsigned ostack).

  Definition no_stack m2 :=
    exists fr fi r,
      Mem.stack_adt m2 = (fr::nil) :: r /\
      (bstack,fi)::nil = frame_adt_blocks fr /\
      0 = frame_adt_size fr /\
      (forall o, frame_perm fi o = Public) /\
      frame_size fi = Mem.stack_limit.

  Lemma no_stack_no_nil m:
    no_stack m ->
    Mem.stack_adt m <> nil.
  Proof.
    intros (frstack & fstack & r & EQstk & BLOCKS & ZERO & PUB & SZ).
    rewrite EQstk. congruence.
  Qed.

  Inductive inject_perm_stack (j: meminj) (P: perm_type): stack_adt -> Prop :=
  | inject_perm_stack_nil:
      inject_perm_stack j P nil
  | inject_perm_stack_cons_nil l (IPS_REC: inject_perm_stack j P l):
      inject_perm_stack j P (nil::l)
  | inject_perm_stack_cons
      l fr b fi (IPS_REC: inject_perm_stack j P l)
      (JB: j b = Some (bstack, Mem.stack_limit - size_stack l - align (frame_size fi) 8))
      (BLOCKS: frame_adt_blocks fr = (b,fi)::nil)
      (SIZE: frame_adt_size fr = frame_size fi)
      (PERM: forall o k p, 0 <= o < frame_size fi -> P b o k p):
      inject_perm_stack j P ((fr::nil)::l).

  Definition inject_padding (j: meminj) (m: mem) : Prop :=
    forall b fi delta,
      in_stack' (Mem.stack_adt m) (b,fi) ->
      j b = Some (bstack, delta) ->
      forall b' o delta' k p,
        j b' = Some (bstack, delta') ->
        Mem.perm m b' o k p ->
        ~ ( delta + frame_size fi <= o + delta' < delta + align (frame_size fi) 8).
  
  Inductive match_states: meminj -> Z -> state -> state -> Prop :=
  | match_states_intro:
      forall j (rs: regset) (m: mem) (rs': regset) m' g
        (MINJ: Mem.inject j g m m')
        lprog
        (STK: Mem.stack_adt m = lprog ++ init_stk)
        (GSPEC: forall i, g i =
                     if lt_dec i (length lprog)
                     then Some O
                     else if lt_dec i (length (Mem.stack_adt m))
                          then Some (i - (length lprog))%nat
                          else None)
        (RSPzero: exists b, rs # RSP = Vptr b Ptrofs.zero )
        (RINJ: forall r, Val.inject j (rs # r) (rs' # r))
        (VB: Mem.valid_block m' bstack)
        (AGSP: agree_sp m rs')
        (SPAL: sp_aligned rs')
        (PBS: perm_bstack m')
        (PBSL: perm_bstack_stack_limit m')
        (NS: no_stack m')
        ostack
        (RSPEQ: rs' RSP = Vptr bstack ostack)
        (NIB: no_inject_below j m (Ptrofs.unsigned ostack))
        (IS: inject_perm_stack j (Mem.perm m) (Mem.stack_adt m))
        (IP: inject_padding j m)
        (GLOBFUN_INJ: forall b f, Genv.find_funct_ptr ge b = Some f -> j b = Some (b,0))
        (GLOBDEF_INJ: forall b f, Genv.find_def ge b = Some f -> j b = Some (b,0))
        (GLOBSYMB_INJ: meminj_preserves_globals' ge j)
        (GlobLe: (Genv.genv_next ge <= Mem.nextblock m)%positive)
        (GlobLeT: (Genv.genv_next ge <= Mem.nextblock m')%positive)
        (SPinstack: in_stack' (Mem.stack_adt m) (binit_sp, public_frame_info 0)),
        match_states j (Ptrofs.unsigned ostack) (State rs m) (State rs' m').

  Lemma inject_stack_incr:
    forall j j' P (INCR: inject_incr j j')
      l (IS: inject_perm_stack j P l),
      inject_perm_stack j' P l.
  Proof.
    induction 2; econstructor; eauto.
  Qed.

  Lemma inject_stack_more_perm:
    forall j (P P': perm_type) (INCR: forall b o k p, P b o k p -> P' b o k p)
      l (IS: inject_perm_stack j P l),
      inject_perm_stack j P' l.
  Proof.
    induction 2; econstructor; eauto.
  Qed.

  Lemma perm_stack_inv:
    forall j (P P': perm_type) 
      l (IS: inject_perm_stack j P l)
      (INCR: forall b o k p, in_stack l b -> P b o k p -> P' b o k p),
      inject_perm_stack j P' l.
  Proof.
    induction 1; econstructor; eauto.
    - eapply IHIS; eauto. intros; eapply INCR; eauto. rewrite in_stack_cons; auto.
    - intros; eapply INCR; eauto. rewrite in_stack_cons. left; rewrite in_frames_cons. left.
      eapply in_frame'_in_frame. red. rewrite BLOCKS. left. reflexivity.
  Qed.

  Axiom exec_instr_inject:
    forall j g m1 m2 rs1 rs2 f i rs1' m1'
      (MINJ: Mem.inject j g m1 m2)
      (RINJ: forall r, Val.inject j (rs1 # r) (rs2 # r))
      (IU: is_unchanged i = true)
      istk1 istk2
      (EXEC: Asm.exec_instr istk1 ge f i rs1 m1 = Next rs1' m1'),      
      exists rs2' m2',
        Asm.exec_instr istk2 ge f i rs2 m2 = Next rs2' m2'
        /\ Mem.inject j g m1' m2'
        /\ (forall r, Val.inject j (rs1' # r) (rs2' # r)).
  (* should be proved already somewhere *)
  
  Lemma ZEQ: forall a b,
      proj_sumbool (zeq a b) = true -> a = b.
  Proof.
    intros; destruct zeq; auto. discriminate.
  Qed.

  Lemma ZLE: forall a b c d,
      zle a b || zle c d = true ->
      a <= b \/ c <= d.
  Proof.
    intros; destruct (zle a b), (zle c d); try congruence; try omega.
    simpl in H; congruence.
  Qed.

  Lemma perm_stack_eq':
    forall l m b fi j
      (SAP: stack_agree_perms (Mem.perm m) l)
      (WF: wf_stack (Mem.perm m) inject_id l)
      (PS: inject_perm_stack j (Mem.perm m) l)
      (INBLOCKS: in_stack' l (b, fi))
      o k p,
      Mem.perm m b o k p <-> 0 <= o < frame_size fi.
  Proof.
    induction 3; simpl; intros; eauto.
    - easy.
    - destruct INBLOCKS as [EQ | INSTK]. easy. 
      eapply IHPS; eauto. red; intros; eapply SAP; eauto. right; eauto. inv WF; auto.
    - inv WF.
      destruct INBLOCKS as [EQ | INSTK].
      + destruct EQ. 2: easy. generalize H. red in H; rewrite BLOCKS in H. destruct H as [EQ|[]]. inv EQ.
        split. 2: apply PERM. eapply SAP. left. reflexivity. left; reflexivity. auto.
      + eapply IHPS; eauto. red; intros; eapply SAP; eauto. right; eauto.
  Qed.

  Lemma perm_stack_eq:
    forall m b fi j
      (PS: inject_perm_stack j (Mem.perm m) (Mem.stack_adt m))
      (INBLOCKS: in_stack' (Mem.stack_adt m) (b, fi))
      o k p,
      Mem.perm m b o k p <-> 0 <= o < frame_size fi.
  Proof.
    intros; eapply perm_stack_eq'; eauto.
    apply Mem.agree_perms_mem.
    apply Mem.wf_stack_mem.
  Qed.
  
  Lemma size_stack_app:
    forall l1 l2,
      StackADT.size_stack (l1 ++ l2) = StackADT.size_stack l1 + StackADT.size_stack l2.
  Proof.
    induction l1; simpl; intros; eauto.
    rewrite IHl1. omega.
  Qed.

  Lemma val_inject_set:
    forall j rs1 rs2 r0 r1
      (RINJ: r0 <> r1 -> Val.inject j (rs1 r0) (rs2 r0))
      v v' (VINJ: Val.inject j v v'),
      Val.inject j ((rs1 # r1 <- v) r0) ((rs2 # r1 <- v') r0).
  Proof.
    intros.
    destruct (PregEq.eq r1 r0); subst; auto.
    rewrite ! Pregmap.gss; auto.
    rewrite ! Pregmap.gso by auto. auto.
  Qed.

  Lemma val_inject_undef_regs:
    forall l j rs1 rs2
      (RINJ: forall r, Val.inject j (rs1 r) (rs2 r))
      r,
      Val.inject j (undef_regs l rs1 r) (undef_regs l rs2 r).
  Proof.
    induction l; simpl; intros; eauto.
    apply IHl.
    intros; apply val_inject_set; auto.
  Qed.

  Lemma val_inject_nextinstr:
    forall j rs1 rs2 r sz
      (RINJ: forall r0, r0 = r \/ r0 = PC -> Val.inject j (rs1 r0) (rs2 r0)),
      Val.inject j (nextinstr rs1 sz r) (nextinstr rs2 sz r).
  Proof.
    unfold nextinstr.
    intros.
    apply val_inject_set; auto. 
    apply Val.offset_ptr_inject; auto.
  Qed.

  Lemma find_var_info_none_ge:
    forall b,
      (Genv.genv_next ge <= b)%positive ->
      Genv.find_var_info ge b = None.
  Proof.
    unfold Genv.find_var_info. intros.
    destr.
    apply Genv.genv_defs_range in Heqo. xomega.
  Qed.

  Lemma load_record_stack_blocks:
    forall m fi m',
      Mem.record_stack_blocks m fi = Some m' ->
      forall chunk b ofs,
        Mem.load chunk m' b ofs = Mem.load chunk m b ofs.
  Proof.
    intros.
    destruct (plt b (Mem.nextblock m)).
    eapply Mem.load_unchanged_on_1.
    eapply Mem.strong_unchanged_on_weak.
    eapply Mem.record_stack_block_unchanged_on; eauto.
    apply p.
    instantiate (1 := fun _ _ => True); simpl; auto.
    destruct (Mem.load chunk m b ofs) eqn:LOAD.
    apply Mem.load_valid_access in LOAD. destruct LOAD.
    exfalso; apply n.
    eapply Mem.perm_valid_block. apply H0.
    instantiate (1:= ofs). generalize (size_chunk_pos chunk); omega.
    clear LOAD.
    destruct (Mem.load chunk m' b ofs) eqn:LOAD; auto.
    apply Mem.load_valid_access in LOAD. destruct LOAD.
    exfalso; apply n.
    eapply Mem.perm_valid_block.
    specialize (H0 ofs). trim H0. generalize (size_chunk_pos chunk); omega.
    rewrite_perms_bw H0.
    apply H0.
  Qed.
  
  Lemma size_frames_nil: size_frames nil = 0.
  Proof.
    reflexivity.
  Qed.

  Lemma size_frames_one:
    forall f,
      size_frames (f :: nil) = align (frame_adt_size f) 8.
  Proof.
    intros. rewrite size_frames_cons, size_frames_nil.
    apply Z.max_l. etransitivity.
    2: apply align_le.
    apply frame_adt_size_pos. omega.
  Qed.
  
 Lemma alloc_inject:
    forall j ostack m1 (rs1 rs1': regset) fi b m1' m5 ofs_ra m2 m4 sz,
      match_states j (Ptrofs.unsigned ostack) (State rs1 m1) (State rs1' m1') ->
      Mem.top_is_new m1 ->
      Mem.alloc m1 0 (frame_size fi) = (m2, b) ->
      Mem.store Mptr m2 b ofs_ra rs1#RA = Some m4 ->
      Mem.record_stack_blocks m4 (make_singleton_frame_adt' b  fi (frame_size fi)) = Some m5 ->
      0 <= ofs_ra <= Ptrofs.max_unsigned ->
      0 < frame_size fi ->
      let sp := Val.offset_ptr (rs1' RSP) (Ptrofs.neg (Ptrofs.repr (align (frame_size fi) 8))) in
      let newostack := Ptrofs.unsigned ostack - align (frame_size fi) 8 in
      let rs2 := nextinstr ( rs1 #RAX <- (rs1#RSP)  #RSP <- (Vptr b Ptrofs.zero)) sz in
      let rs2' := nextinstr (rs1' #RAX <- (rs1'#RSP) #RSP <- sp) sz in
      exists j',
        (forall bb, j' bb = if peq bb b then Some (bstack, newostack) else j bb)
        /\ inject_incr j j'
        /\
        exists m4',
          Mem.storev Mptr m1' (Val.offset_ptr sp (Ptrofs.repr ofs_ra)) rs1'#RA = Some m4'
          /\ match_states j' newostack (State rs2 m5) (State rs2' m4').
  Proof.
    intros j ostack m1 rs1 rs1' fi b m1' m5 ofs_ra m2 m4 sz
           MS TIN ALLOC STORE RSB REPRretaddr sizepos
           sp newostack rs2 rs2'.
    inv MS.
    assert (RNGframe: 0 <= align (frame_size fi) 8 <= Ptrofs.max_unsigned).
    {
      generalize (Mem.size_stack_below m5).
      repeat rewrite_stack_blocks. revert EQ1; repeat rewrite_stack_blocks. inv TIN. intro A; inv A.
      simpl. rewrite size_frames_one. simpl. rewrite Z.max_r by apply frame_size_pos.
      generalize (align_le (frame_size fi) 8) (frame_size_pos fi) (size_stack_pos r).
      generalize Mem.stack_limit_range. omega.
    }
    assert (SP: sp = Vptr bstack (Ptrofs.repr newostack)).
    {
      unfold sp. rewrite RSPEQ. simpl. f_equal.
      rewrite <- Ptrofs.sub_add_opp. unfold newostack.
      unfold Ptrofs.sub. rewrite H1. rewrite Ptrofs.unsigned_repr; auto.
    }
    assert (REPRcur: align (frame_size fi) 8 <= Ptrofs.unsigned ostack0 <= Ptrofs.max_unsigned).
    {
      split.
      red in AGSP. specialize (AGSP _ RSPEQ). rewrite AGSP.
      generalize (Mem.size_stack_below m5).
      repeat rewrite_stack_blocks. revert EQ1; repeat rewrite_stack_blocks. inv TIN. intro A; inv A.
      simpl. rewrite size_frames_one, size_frames_nil. simpl. rewrite Z.max_r by apply frame_size_pos. omega.
      apply Ptrofs.unsigned_range_2.
    }
    assert (REPR: 0 <= newostack <= Ptrofs.max_unsigned).
    {
      unfold newostack.
      generalize (align_le (frame_size fi) 8) (frame_size_pos fi).
      omega.
    }
    generalize (Mem.alloc_left_mapped_inject _ _ _ _ _ _ _ _ _ newostack MINJ ALLOC VB).
    intro A.
    trim A. now omega.
    trim A. intros; right; eapply PBS; now eauto.
    trim A.
    {
      intros; eapply Mem.perm_implies. eapply PBSL; eauto.
      split. omega.
      unfold newostack.
      eapply Z.lt_le_trans with (Ptrofs.unsigned ostack).
      generalize (align_le ((frame_size fi)) 8) ((frame_size_pos fi)). omega.
      erewrite <- H1, (AGSP _ RSPEQ); eauto.
      generalize (size_stack_pos (Mem.stack_adt m1)); intros. omega.
      simpl in H0. auto.
    }
    trim A.
    {
      red.
      intros.
      unfold newostack.
      eapply Zdivides_trans with 8.
      destruct chunk; try (exists 8; reflexivity);
        try (exists 4; reflexivity);
        try (exists 2; reflexivity);
        try (exists 1; reflexivity).
      apply Z.divide_sub_r.
      rewrite <- H1. apply SPAL; auto.
      apply align_divides. omega.
    }
    trim A.
    {
      intros b0 delta' ofs k p JB PERM RNG.
      generalize (NIB _ _ _ _ _ JB PERM).
      generalize (align_le (frame_size fi) 8).
      unfold newostack in RNG. simpl in RNG. omega.
    }
    trim A.
    {
      revert NS. unfold no_stack. intros (fr & fi0 & rr & EQS & BLOCKS & ZERO & PUBLIC & SIZE). rewrite EQS.
      simpl. intros fi1 [[|[]]|INS]; subst.
      - revert H. unfold in_frame'. rewrite <- BLOCKS.
        intros [|[]]. inv H.
        intros; apply PUBLIC.
      - exploit Mem.stack_norepet. rewrite EQS.
        intro ND; inv ND.
        exfalso; eapply H3. 2: eapply in_stack'_in_stack; apply INS.
        rewrite in_frames_cons; left; simpl. red. unfold get_frame_blocks. rewrite <- BLOCKS. left; reflexivity.
    }
    destruct A as (f' & MINJ' & INCR & EQ1 & EQ2).
    exists f'.
    split.
    {
      intros.
      destruct peq; subst; eauto.
    }
    split; auto.
    (* store return address *)
    exploit Mem.store_mapped_inject. apply MINJ'. simpl in *; eauto. eauto. 
    eapply val_inject_incr; eauto. intros (m4' & STORE' & MINJ3).
    assert (Ptrofs.unsigned (Ptrofs.add (Ptrofs.repr newostack) (Ptrofs.repr ofs_ra)) =
            ofs_ra + newostack) as EQ'.
    2: simpl. 
    rewrite Ptrofs.add_commut.
    erewrite Mem.address_inject; eauto.
    rewrite Ptrofs.unsigned_repr; omega.
    exploit Mem.store_valid_access_3. exact STORE.
    intro VA; eapply Mem.store_valid_access_1 in VA; eauto. destruct VA.
    eapply H. 
    rewrite Ptrofs.unsigned_repr; generalize (size_chunk_pos Mptr); omega.
    rewrite SP. simpl. unfold Ptrofs.add.
    rewrite (Ptrofs.unsigned_repr _ REPR).
    rewrite (Ptrofs.unsigned_repr _ REPRretaddr) in *.
    rewrite Ptrofs.unsigned_repr. rewrite Z.add_comm. rewrite STORE'.
    eexists; split; eauto.
    (* record the stack block *)
    destruct NS as (frstack & fstack & rr & EQstk & BLOCKS & ZERO & PUB & SZ).
    exploit Mem.record_stack_block_inject_left_zero. apply MINJ3. 5: eauto.
    {
      red. repeat rewrite_stack_blocks. auto.
    }
    repeat rewrite_stack_blocks. rewrite EQstk. constructor; reflexivity.
    {
      red. simpl.
      intros ? [EQ|[]] HPF.
      exists frstack; split; auto.
      red. subst. simpl.
      constructor; auto. simpl. rewrite EQ1.
      intros b2 delta A; inversion A. subst b2 delta.
      rewrite <- BLOCKS. simpl.
      eexists; split. eauto.
      constructor.
      intros; eapply stack_perm_le_public. intros; apply PUB.
      intros; rewrite SZ.
      unfold newostack.
      rewrite <- H1.
      red in AGSP. apply AGSP in RSPEQ.  rewrite RSPEQ.
        cut (o - size_stack (Mem.stack_adt m1) - align ((frame_size fi)) 8 < 0). omega.
        generalize (size_stack_pos (Mem.stack_adt m1)).
        cut (o - align ((frame_size fi)) 8 < 0). omega.
        cut (o < align ((frame_size fi)) 8). omega.
        eapply Z.lt_le_trans.
        2: apply align_le. 2: omega. omega.
    }
    {
      red. unfold in_frame. simpl. exists b, 0, Cur, Writable.
      split. congruence.
      split. auto. split.
      repeat rewrite_perms. rewrite peq_true. omega.
      constructor.
    }
    rewrite GSPEC.
    inv TIN. simpl. destr.
    intro MINJ4.
    (* proving the final match_states *)
    rewrite <- (Ptrofs.unsigned_repr newostack) by omega.
    destruct lprog. simpl in STK.
    revert init_sp_ptr; unfold init_sp; rewrite <- STK. clear STK. inv TIN. inversion 1. simpl in STK.
    econstructor; eauto.
    - repeat rewrite_stack_blocks. revert EQ0; repeat rewrite_stack_blocks.
      intro EQ0; rewrite EQ0 in STK. inv STK.
      instantiate (1 := (make_singleton_frame_adt' b fi (frame_size fi)::nil) :: lprog).
      inversion TIN. rewrite EQ0 in H; inversion H. subst tf t. reflexivity.
    - rewrite_stack_blocks. revert EQ0; repeat rewrite_stack_blocks. intro.
      rewrite EQ0 in GSPEC. simpl in GSPEC; simpl; auto.
    - unfold rs2. rewrite nextinstr_rsp, Pregmap.gss. eauto.
    - intros r.
      unfold rs2, rs2'.
      apply val_inject_nextinstr. intros.
      apply val_inject_set; eauto. intro. apply val_inject_set. intros; eauto.
      eapply val_inject_incr; eauto.
      subst sp. simpl. rewrite RSPEQ. econstructor; eauto. rewrite Ptrofs.add_zero_l; auto.
      unfold newostack. rewrite <- Ptrofs.sub_add_opp. unfold Ptrofs.sub. rewrite <- H1. rewrite Ptrofs.unsigned_repr; auto.
    - red. rewnb. eauto.
    - red. unfold rs2'. rewrite nextinstr_rsp. rewrite Pregmap.gss. rewrite SP. inversion 1. subst.
      repeat rewrite_stack_blocks.
      rewrite Ptrofs.unsigned_repr by auto.
      unfold newostack in *.
      rewrite <- H1. rewrite (AGSP _ RSPEQ).
      revert EQ0; repeat rewrite_stack_blocks.
      clear EQstk. inv TIN. inversion 1; subst.
      simpl. rewrite size_frames_one, size_frames_nil. simpl.
      rewrite Z.max_r by omega. omega.
    - red. intros ostack1 A. unfold rs2' in A. rewrite nextinstr_rsp in A. rewrite Pregmap.gss in A.
      rewrite SP in A. inversion A. subst.
      rewrite Ptrofs.unsigned_repr by omega.
      unfold newostack.
      apply Z.divide_sub_r. rewrite <- H1. apply SPAL. auto.
      apply align_divides. omega.
    - red. intros ofs k p PERM.
      repeat rewrite_perms_bw PERM. eauto.
    - red; intros.
      repeat rewrite_perms_fw. eauto.
    - red. repeat rewrite_stack_blocks. exists frstack, fstack, rr; rewrite EQstk, <- BLOCKS, <- ZERO. eauto.
    (* - unfold rs2'. rewrite nextinstr_rsp, Pregmap.gss. inversion 1. eauto. *)
    - rewrite Ptrofs.unsigned_repr by omega.
      red. intros b0 delta o k p JB PERM.
      repeat rewrite_perms_bw PERM.
      destruct peq.
      * subst. rewrite EQ1 in JB. clear EQstk. inv JB. split. omega.
        rewrite_stack_blocks. rewrite in_stack_cons. rewrite in_frames_cons.
        revert EQ0. repeat rewrite_stack_blocks.
        inv TIN. inversion 1; subst.
        left. left; unfold in_frame; simpl; auto.
      * split. unfold newostack.
        transitivity (Ptrofs.unsigned ostack).
        -- generalize (align_le ((frame_size fi)) 8). omega.
        -- rewrite <- H1.
          rewrite EQ2 in JB; auto. 
          exploit NIB; eauto. tauto.
        -- repeat rewrite_stack_blocks.
           revert EQ0; repeat rewrite_stack_blocks. intro EQ0.
           rewrite in_stack_cons.
           right.
           edestruct NIB; eauto. rewrite <- EQ2; eauto.
           rewrite EQ0 in H0. rewrite in_stack_cons in H0. destruct H0; auto.
           exfalso.
           inv TIN. clear EQstk. rewrite EQ0 in H2; inv H2. easy.
    - repeat rewrite_stack_blocks.
      revert EQ0; repeat rewrite_stack_blocks. inv TIN. clear EQstk. inversion 1; subst.
      rewrite <- H in IS. inv IS. 
      econstructor; try reflexivity; eauto.
      eapply inject_stack_incr; eauto.
      eapply inject_stack_more_perm with (P:=Mem.perm m1).
      intros; repeat rewrite_perms.
      exploit Mem.perm_valid_block; eauto. intro VB'.
      generalize (Mem.fresh_block_alloc _ _ _ _ _ ALLOC). destr. auto.
      rewrite EQ1. f_equal. f_equal.
      unfold newostack.
      rewrite <- H1.
      rewrite AGSP. rewrite <- H. simpl. change (size_frames nil) with 0. omega. auto.
      + simpl. rewrite Z.max_r; auto. omega.
      + intros.
        repeat rewrite_perms. destr.
    - intros b0 fi0 delta INSTK FB0 b' o delta' k p FB1 P1.
      revert INSTK. repeat rewrite_stack_blocks. intro INSTK.
      revert EQ0; repeat rewrite_stack_blocks. inv TIN. clear EQstk. inversion 1; subst. clear EQ0.
      simpl in INSTK.
      repeat rewrite_perms_bw P1.
      destruct INSTK as [[IFR|[]]|INSTK].
      + destruct IFR as [EQ|[]]. inv EQ. rewrite FB0 in EQ1; inv EQ1.
        destr_in P1.
        * subst. rewrite FB0 in FB1; inv FB1. omega.
        * rewrite EQ2 in FB1 by auto.
          eapply NIB in P1; eauto.
          destruct P1 as (LE & IN).
          unfold newostack.
          rewrite <- H1.
          omega.
      + assert (b0 <> b). intro; subst.
        exploit Mem.stack_norepet. rewrite EQ3. intro ND; inv ND.
        eapply in_stack'_in_stack in INSTK; eauto. eapply H4 in INSTK; eauto.
        left. reflexivity.
        rewrite EQ2 in FB0 by auto.
        intro RNG.
        assert (0 < frame_size fi0).
        destruct (zlt 0 (frame_size fi0)); auto.
        assert (frame_size fi0 = 0). generalize (frame_size_pos fi0); omega. rewrite H2 in RNG.
        change (align 0 8) with 0 in RNG. omega.
        (* rewrite Z.max_r in RNG by omega. *)
        destr_in P1. 
        * subst. rewrite EQ1 in FB1; inv FB1.
          cut (newostack + (frame_size fi)  <= delta). omega.
          unfold newostack. rewrite <- H1.
          rewrite AGSP; auto.
          rewrite <- H in IS. inv IS.

          Lemma in_stack_inj_below:
            forall j P l
              (IS: inject_perm_stack j P l)
              b fi
              (INFRAMES: in_stack' l (b,fi)),
            exists l1 l2,
              l = l1 ++ l2 /\
              j b = Some (bstack, Mem.stack_limit - StackADT.size_stack l2).
          Proof.
            induction 1; simpl; intros; eauto. easy.
            - destruct INFRAMES as [[]|INFRAMES].
              edestruct IHIS as (l1 & l2 & EQ & JB); eauto. exists (nil::l1),l2; split; auto. simpl. subst. reflexivity.
            - destruct INFRAMES as [[INFRAME|[]]|INSTACK].
              + generalize INFRAME. red in INFRAME; rewrite BLOCKS in INFRAME. destruct INFRAME as [EQ|[]]; inv EQ.
                intro.
                exists nil,((fr::nil)::l). simpl; split. auto. rewrite size_frames_cons.
                rewrite Z.max_comm. rewrite SIZE. rewrite Z.sub_add_distr. rewrite JB. f_equal. f_equal. f_equal.
                rewrite ! Z.max_r. auto. etransitivity. 2: apply align_le.
                apply frame_size_pos. omega.
              + edestruct IHIS as (l1 & l2 & EQ & JB'); eauto. exists ((fr::nil)::l1),l2; split; auto. simpl. subst. reflexivity.
          Qed.

          eapply in_stack_inj_below in INSTK; eauto.
          destruct INSTK as (l1 & l2 & EQADT & JB0). rewrite FB0 in JB0. inv JB0.
          rewrite <- H. simpl. rewrite size_frames_nil.
          cut (size_stack (Mem.stack_adt m1) >= size_stack l2). rewrite <- H.
          generalize (align_le (frame_size fi) 8). simpl. rewrite size_frames_nil. omega.
          rewrite <- H.
          simpl. rewrite size_stack_app.
          generalize (size_stack_pos l1) (size_frames_pos nil); omega. 
        * eapply IP. rewrite <- H. right. eauto. eauto.
          rewrite <- EQ2. apply FB1. auto. eauto. omega.
    - destruct GLOBSYMB_INJ; split.
      + intros. eapply INCR. eauto.
      + intros. destruct (peq b1 b).
        subst; rewrite EQ1 in H2. clear EQstk. inv H2.
        simpl.
        unfold Genv.block_is_volatile.
        unfold Genv.find_var_info.
        replace (Genv.find_def ge bstack) with (None (A:=globdef Asm.fundef unit)).
        replace (Genv.find_def ge b) with (None (A:=globdef Asm.fundef unit)).
        auto.
        unfold Genv.find_def.
        destruct (Maps.PTree.get b (Genv.genv_defs ge)) eqn:EQdef; auto.
        apply Genv.genv_defs_range in EQdef.
        exploit Mem.fresh_block_alloc. eauto. red. xomega. easy.
        unfold Genv.find_def.
        destruct (Maps.PTree.get bstack (Genv.genv_defs ge)) eqn:EQdef; auto.
        apply Genv.genv_defs_range in EQdef.
        unfold bstack in EQdef. xomega.
        rewrite EQ2 in H2.
        eauto.
        auto.
    - erewrite Mem.record_stack_block_nextblock. 2: eauto.
      erewrite Mem.nextblock_store. 2 : eauto.
      erewrite Mem.nextblock_alloc. 2: eauto. xomega.
    - erewrite Mem.nextblock_store. 2 : eauto. xomega.
    - repeat rewrite_stack_blocks. revert EQ0; repeat rewrite_stack_blocks.
      inv TIN. clear EQstk. inversion 1; subst.
      rewrite <- H in SPinstack. simpl in SPinstack.
      simpl. right. destruct SPinstack; auto. easy.
    - rewrite Z.add_comm, <- EQ'. apply Ptrofs.unsigned_range_2.
  Qed.

  Lemma size_frames_divides f:
    (8 | size_frames f).
  Proof.
    unfold size_frames. induction f; simpl; eauto.
    exists 0; omega.
    rewrite Zmax_spec.
    destr.
    apply align_divides. omega.
  Qed.

  Lemma size_stack_divides l:
    (8 | StackADT.size_stack l).
  Proof.
    induction l; simpl; intros; eauto.
    exists 0; omega.
    apply Z.divide_add_r. auto. apply size_frames_divides; auto.
  Qed.

  Lemma inject_stack_init_sp:
    forall j P l,
      inject_perm_stack j P l ->
      forall b,
        in_stack l b ->
        exists o,
          j b = Some (bstack, o).
  Proof.
    induction 1; simpl; intros bb INS. easy.
    rewrite in_stack_cons in INS. destruct INS as [INF|INS]. easy. eauto.
    rewrite in_stack_cons in INS. destruct INS as [INF|INS].
    rewrite in_frames_cons in INF. destruct INF as [IFR|INF]. 2: easy.
    - edestruct in_frame_info as (ffi & IFRR). eauto.
      rewrite BLOCKS in IFRR. destruct IFRR as [IFRR|[]]. inv IFRR. eauto.
    - eauto.
  Qed.

  Lemma init_sp_inj:
    forall j P l,
      inject_perm_stack j P l ->
      in_stack l binit_sp ->
      exists o,
        Val.inject j init_sp (Vptr bstack o).
  Proof.
    intros. edestruct inject_stack_init_sp; eauto.
    rewrite init_sp_ptr. exists (Ptrofs.repr x).
    econstructor; eauto. rewrite Ptrofs.add_zero_l. auto.
  Qed.

  Ltac use_ains :=
    repeat match goal with
           | AINS: asm_instr_no_stack ?i,
                   UNC: stack_invar ?i = true,
                        EI: Asm.exec_instr ?init_stk _ _ ?i _ ?m1 = Next _ ?m2 |-
             context [Mem.stack_adt ?m2] =>
             let AINS_stack := fresh "AINS_stack" in
             edestruct (AINS UNC _ _ _ _ _ _ _ _ _ EI) as (AINS_stack & _); rewrite ! AINS_stack;
             clear AINS_stack
           | AINS: asm_instr_no_stack ?i,
                   UNC: stack_invar ?i = true,
                        EI: Asm.exec_instr ?init_stk _ _ ?i _ ?m1 = Next _ ?m2,
                            H: context [Mem.stack_adt ?m2] |- _ =>
             let AINS_stack := fresh "AINS_stack" in
             edestruct (AINS UNC _ _ _ _ _ _ _ _ _ EI) as (AINS_stack & _); rewrite ! AINS_stack in H;
             clear AINS_stack

           | AINS: asm_instr_no_stack ?i,
                   UNC: stack_invar ?i = true,
                        EI: Asm.exec_instr ?init_stk _ _ ?i _ ?m1 = Next _ ?m2 |-
             context [Mem.perm ?m2 _ _ _ _] =>
             let AINS_perm := fresh "AINS_perm" in
             edestruct (AINS UNC _ _ _ _ _ _ _ _ _ EI) as (_ & AINS_perm); rewrite ! AINS_perm;
             clear AINS_perm
           | AINS: asm_instr_no_stack ?i,
                   UNC: stack_invar ?i = true,
                        EI: Asm.exec_instr ?init_stk _ _ ?i _ ?m1 = Next _ ?m2,
                            H : context [Mem.perm ?m2 _ _ _ _] |- _ =>
             let AINS_perm := fresh "AINS_perm" in
             edestruct (AINS UNC _ _ _ _ _ _ _ _ _ EI) as (_ & AINS_perm); rewrite ! AINS_perm in H;
             clear AINS_perm
           | AINR: asm_instr_no_rsp ?i,
                   UNC: stack_invar ?i = true,
                        EI: Asm.exec_instr ?init_stk _ _ ?i ?rs1 _ = Next ?rs2 _ |-
             context [?rs2 (IR RSP)] =>
             rewrite (AINR UNC _ _ _ _ _ _ _ _ _ EI)
           | AINR: asm_instr_no_rsp ?i,
                   UNC: stack_invar ?i = true,
                        EI: Asm.exec_instr ?init_stk _ _ ?i ?rs1 _ = Next ?rs2 _,
                            H: context [?rs2 (IR RSP)] |- _ =>
             rewrite (AINR UNC _ _ _ _ _ _ _ _ _ EI) in H
                                                          
           end.

  Lemma is_unchanged_stack_invar:
    forall i,
      is_unchanged i = true ->
      stack_invar i = true.
  Proof.
    intros. destruct i. destruct i eqn:?; simpl in *; try congruence.
  Qed.
  
  Lemma exec_instr_inject':
    forall j ostack m1 m2 rs1 rs2 f i rs1' m1'
      (MS: match_states j ostack (State rs1 m1) (State rs2 m2))
      (AINR: asm_instr_no_rsp i)
      (AINS: asm_instr_no_stack i)
      (EI: Asm.exec_instr init_stk ge f i rs1 m1 = Next rs1' m1'),
      exists j' ostack' rs2' m2',
        exec_instr ge f i rs2 m2 = Next rs2' m2'
        /\ match_states j' ostack' (State rs1' m1') (State rs2' m2')
        /\ inject_incr j j'.
  Proof.
    intros. 
    destruct (is_unchanged i) eqn:ISUNCH.
    - inversion MS.
      edestruct exec_instr_inject as (rs2' & m2' & EXEC' & MINJ' & RINJ'); eauto.
      exists j, ostack, rs2', m2'; split; [|split]; eauto.
      destruct i as (i & szinfo); destruct i; simpl in *; eauto; try congruence.
      generalize (is_unchanged_stack_invar _ ISUNCH) as SINVAR. intro.
      subst. eapply match_states_intro with (g:=g); eauto; try now ((intros; use_ains; eauto) || (red; intros; use_ains; eauto)).
      + eapply asmgen_nextblock_forward in EXEC'.
        red in VB |- *. xomega.
      + use_ains. 
        eapply perm_stack_inv. eauto.
        intros; use_ains. tauto.
      + etransitivity. apply GlobLe.
        eapply asmgen_nextblock_forward; eauto.
      + etransitivity. apply GlobLeT.
        eapply asmgen_nextblock_forward; eauto.

    - destruct i as (i & szinfo).
      destruct i; simpl in *; try congruence.
      + (* call_s *)
        inv EI. inv MS. do 4 eexists. split. eauto. split. econstructor; eauto.
        * eapply Mem.inject_push_new_stage_left; eauto.
          apply no_stack_no_nil; auto.
        * rewrite_stack_blocks.
          instantiate (1 := nil::lprog); simpl; rewrite STK; auto. 
        * Opaque minus.
          unfold upstar. intros. rewrite_stack_blocks. simpl. rewrite GSPEC.
          rewrite STK. rewrite app_length.
          intros; repeat destr; try omega. f_equal. omega.
        * intros; apply val_inject_set; auto.
          intros; apply val_inject_set; auto.
          apply Val.offset_ptr_inject; auto.
          unfold Genv.symbol_address. destr; auto.
          destruct GLOBSYMB_INJ. apply H in Heqo.
          econstructor; eauto.
        * red. rewrite_stack_blocks. simpl. change (size_frames nil) with 0. rewrite Z.add_0_r. eauto.
        * red. intros b delta o k p. rewrite_perms. rewrite_stack_blocks. rewrite in_stack_cons.
          intros. exploit NIB; eauto. tauto.
        * rewrite_stack_blocks. constructor.
          eapply inject_stack_more_perm. 2: eauto. intros. rewrite_perms. auto.
        * red. rewrite_stack_blocks. simpl. intros b fi delta H H0 b' o delta' k p. rewrite_perms. eapply IP; eauto. tauto.
        * rewnb. auto.
        * rewrite_stack_blocks. simpl; auto.
        * red. auto.
      + (* call_r *)
        inv EI. inv MS. do 4 eexists. split. eauto. split. econstructor; eauto.
        * eapply Mem.inject_push_new_stage_left; eauto.
          apply no_stack_no_nil; auto.
        * rewrite_stack_blocks.
          instantiate (1 := nil::lprog); simpl; rewrite STK; auto. 
        * Opaque minus.
          unfold upstar. intros. rewrite_stack_blocks. simpl. rewrite GSPEC.
          rewrite STK. rewrite app_length.
          intros; repeat destr; try omega. f_equal. omega.
        * intros; apply val_inject_set; auto.
          intros; apply val_inject_set; auto.
          apply Val.offset_ptr_inject; auto.
        * red. rewrite_stack_blocks. simpl. change (size_frames nil) with 0. rewrite Z.add_0_r. eauto.
        * red. intros b delta o k p. rewrite_perms. rewrite_stack_blocks. rewrite in_stack_cons.
          intros. exploit NIB; eauto. tauto.
        * rewrite_stack_blocks. constructor. eapply inject_stack_more_perm. 2: eauto. intros; rewrite_perms; auto.
        * red. rewrite_stack_blocks. simpl. intros b fi delta H H0 b' o delta' k p. rewrite_perms. eapply IP; eauto. tauto.
        * rewnb. auto.
        * rewrite_stack_blocks. simpl; auto.
        * red. auto.
      + (* ret *)
        unfold Asm.exec_instr in EI. simpl in EI.
        repeat destr_in EI.
        eexists j,ostack, _, _; split; eauto. split; auto.
        inv MS; econstructor; eauto.
        * eapply Mem.unrecord_stack_block_inject_left_zero; eauto.
          inv t. rewrite <- H in IS. unfold is_stack_top. simpl. easy.
          rewrite GSPEC. inv t. rewrite <- H in *.
          destruct lprog. exfalso. revert init_sp_ptr; unfold init_sp; simpl in STK; rewrite <- STK. inversion 1.
          simpl. simpl in STK. inv STK.
          destr. rewrite app_length. destr.
          exfalso. revert init_sp_ptr; unfold init_sp, current_sp.
          destr. inversion 1.  contradict n0. simpl. omega.
        * instantiate (1:= tl lprog).
          rewrite_stack_blocks.
          rewrite STK.
          destruct lprog; simpl; auto. exfalso.
          simpl in *.
          revert init_sp_ptr; unfold init_sp; simpl in STK; rewrite <- STK.
          rewrite EQ. simpl. red in t. rewrite EQ in t. inversion t. subst f0. inversion 1.
        * simpl. intros; rewrite GSPEC.
          Require Import StackInj.
          repeat rewrite_stack_blocks.
          assert (f0 = nil).
          inv t. congruence. subst.
          destruct lprog. simpl in *.
          revert init_sp_ptr; unfold init_sp; simpl in STK; rewrite <- STK. rewrite EQ. simpl. inversion 1.
          simpl in STK. rewrite STK in EQ. inv EQ. rewrite STK. simpl. rewrite app_length. simpl.
          repeat destr; try omega.
        * simpl; intros. apply val_inject_set; auto.
          intros; apply val_inject_set; auto.
        * red. repeat rewrite Pregmap.gso by congruence.
          rewrite_stack_blocks. inv t. rewrite EQ in H; inv H. simpl.
          intros; erewrite AGSP; eauto.
          rewrite EQ. simpl. change (size_frames nil) with 0. omega.
        * red; intros. rewrite_stack_blocks. revert EQ. inv t. inversion 1; subst. simpl.
          red in NIB. rewrite <- H1 in NIB.
          revert H0. rewrite_perms. intro.
          exploit NIB; eauto.
        * rewrite_stack_blocks. revert EQ. inv t. inversion 1; subst. simpl.
          rewrite <- H in IS. inv IS.
          eapply inject_stack_more_perm. 2: eauto. intros; rewrite_perms. auto.
        * red. rewrite_stack_blocks. revert EQ. inv t. inversion 1; subst. simpl.
          red in IP. rewrite <- H in IP.
          intros. revert H3; rewrite_perms. eapply IP; eauto.
          right. auto.
        * rewnb. auto.
        * rewrite_stack_blocks. revert EQ. inv t. inversion 1; subst. rewrite <- H in SPinstack. simpl.
          simpl in SPinstack. destruct SPinstack. easy. auto.

     + (* allocframe *)
       clear ISUNCH.
       unfold Asm.exec_instr in EI; simpl in EI.
       repeat destr_in EI.
       inversion MS; subst.
       edestruct alloc_inject as (j' & JSPEC & INCR & m4' & STORE2 & MS') ; eauto.
       apply Ptrofs.unsigned_range_2.
       simpl in *.
       rewrite Ptrofs.repr_unsigned in STORE2. setoid_rewrite STORE2.
       eexists j', _, _, _; split; eauto.

     + (* freeframe *)
       unfold Asm.exec_instr in EI; simpl in EI.
       repeat (destr_in EI; [idtac]).
       clear ISUNCH.
       rename Heqv0 into RS1RSP.
       rename Heqo into LOADRA.
       rename Heqb0 into CHECKFRAME.
       rename Heqo0 into FREE.
       rename Heqo1 into UNRECORD.
       rename Heqo2 into ISDEF.
       inv MS. rewrite RS1RSP in RSPzero. destruct RSPzero as [bb EQ]; inv EQ.
       exploit Mem.loadv_inject. eauto. apply LOADRA.
       apply Val.offset_ptr_inject. rewrite <- RS1RSP; auto.
       intros (ra' & LOADRA' & INJra).
       rewrite LOADRA'.
       unfold check_top_frame in CHECKFRAME.
       repeat destr_in CHECKFRAME.
       (* repeat destr_in AGSP1. *)
       repeat rewrite andb_true_iff in H0.
       destruct H0 as (A & B).
       destruct Forall_dec; simpl in A; try congruence. clear A.
       apply ZEQ in B.
       set (newostack := Ptrofs.unsigned ostack0 + align ((frame_adt_size f0)) 8).

       assert (RNGframe: 0 <= align (frame_adt_size f0) 8 < Ptrofs.max_unsigned).
       {
         generalize (Mem.size_stack_below m1).
         generalize (size_stack_pos (Mem.stack_adt m1)). rewrite Heqs.
         generalize (Mem.stack_limit_range).
         simpl. rewrite size_frames_cons.
         generalize (frame_adt_size_pos f0) (align_le (frame_adt_size f0) 8) (size_stack_pos s).
         split. omega.
         eapply Z.le_lt_trans. apply (Z.le_max_l _ (size_frames t0)). omega.
       }

       Lemma clear_stage_inject_left:
         forall j g m1 m2 m1',
           Mem.inject j g m1 m2 ->
           Mem.clear_stage m1 = Some m1' ->
           g O = Some O -> g 1%nat = Some O ->
           (forall b : block, is_stack_top (Mem.stack_adt m1) b -> forall (o : Z) (k : perm_kind) (p : permission), ~ Mem.perm m1 b o k p) ->
           Mem.stack_adt m2 <> nil ->
           Mem.inject j g m1' m2.
       Proof.
         intros. unfold Mem.clear_stage in H0; repeat destr_in H0.
         eapply Mem.mem_inject_ext. apply Mem.inject_push_new_stage_left.
         eapply Mem.unrecord_stack_block_inject_left; eauto. auto.
         unfold upstar; simpl. intros. destr.
         auto.
         rewrite Nat.succ_pred; auto.
       Qed.

       exploit Mem.free_left_inject. apply MINJ. eauto. intro MINJ'.
       exploit clear_stage_inject_left; eauto.
       {
         rewrite GSPEC. simpl. destr.
       }
       {
         rewrite GSPEC. simpl.
         red in c. unfold init_sp in init_sp_ptr. unfold Asm.init_sp in c. rewrite init_sp_ptr in c.
         revert c. repeat rewrite_stack_blocks. rewrite Heqs. simpl. destruct s. simpl. easy. simpl.
         destruct lprog. simpl in *.
         revert init_sp_ptr; unfold init_sp; simpl in STK; rewrite <- STK. simpl. repeat destr.
         inversion 1. subst b.
         intros. exfalso.
         exploit Mem.stack_norepet. rewrite Heqs. intro ND; inversion ND. subst f3 s0 p l.
         apply (H2 binit_sp).
         rewrite in_frames_cons; left. eapply in_frame'_in_frame. red; rewrite Heql. left; reflexivity.
         rewrite in_stack_cons in c. destruct c. easy. auto.
         simpl. destr.
       }
       {
         erewrite Mem.free_stack_blocks; eauto. rewrite Heqs.
         unfold is_stack_top. simpl. unfold get_frames_blocks. simpl. setoid_rewrite in_app.
         inv IS.
         intros ? [?|[]].
         intros. rewrite_perms. unfold get_frame_blocks in H. rewrite BLOCKS in H. simpl in H. destruct H; try easy. subst.
         destr. intro P.
         rewrite BLOCKS in f1. inv f1. red in H1. simpl in H1. destruct H1; subst.
         exploit Mem.agree_perms_mem. rewrite Heqs. left; reflexivity. left; reflexivity. rewrite BLOCKS. left; reflexivity. eauto.
         rewrite <- SIZE. intros.
         Lemma zle_zlt:
           forall lo hi o,
             zle lo o && zlt o hi = true <-> lo <= o < hi.
         Proof.
           intros.
           destruct (zle lo o), (zlt o hi); intuition; try congruence; try omega.
         Qed.
         apply zle_zlt in H. rewrite <- andb_assoc in Heqb. rewrite H in Heqb.
         rewrite andb_true_r in Heqb. destruct peq; simpl in Heqb. congruence. congruence.
       }
       apply no_stack_no_nil; auto.
       intros INJ. 
       exists j, newostack; eexists; eexists; split; [|split]; eauto.
       generalize (RINJ RSP). rewrite RS1RSP.
       inversion 1 as [ff|ff|ff|ff|? ? ? ? ? INJB ? x EQRSP|ff]; subst.
       symmetry in EQRSP.
       rewrite Ptrofs.add_zero_l in *.
       inversion IS. subst. rewrite BLOCKS in f1. inv f1. red in H2; simpl in H2; destruct H2 as [? _]; subst. clear H3. rewrite JB in INJB; inv INJB.
       specialize (AGSP _ EQRSP).
       specialize (SPAL _ EQRSP).
       rewrite EQRSP in RSPEQ. inv RSPEQ.
       assert (0 <= Mem.stack_limit - StackADT.size_stack (Mem.stack_adt m1') <= Ptrofs.max_unsigned) as RNGnewofs. 
       {
         generalize (Mem.size_stack_below m1').
         generalize (size_stack_pos (Mem.stack_adt m1')).
         generalize (Mem.stack_limit_range).
         omega.
       }
       assert (0 <= newostack <= Ptrofs.max_unsigned) as RNGnew.
       {
         unfold newostack.
         rewrite AGSP. rewrite Heqs. simpl.
         revert RNGnewofs. repeat rewrite_stack_blocks. simpl. rewrite Heqs. simpl.
         rewrite size_frames_one, size_frames_nil. intros; omega.
       }
       rewrite <- (Ptrofs.unsigned_repr newostack) by omega.
       destruct lprog. simpl in STK.
       revert init_sp_ptr; unfold init_sp; simpl in STK; rewrite <- STK. simpl. repeat destr. inv BLOCKS.
       red in c. simpl in c. rewrite Heql in c.
       revert c; repeat rewrite_stack_blocks. rewrite Heqs. simpl. inversion 2. subst b.
       exploit Mem.stack_norepet; rewrite Heqs. clear STK. intro ND; inv ND.
       edestruct (H3 binit_sp). rewrite in_frames_cons; left. eapply in_frame'_in_frame. red; rewrite Heql. left; reflexivity.
       rewrite in_stack_cons in c. destruct c; easy.
       econstructor; eauto.
       * repeat rewrite_stack_blocks. rewrite Heqs. simpl.
         instantiate (1 := nil :: lprog). inv STK. reflexivity.
       * simpl. intros. rewrite GSPEC. repeat rewrite_stack_blocks. rewrite Heqs. simpl. auto.
       * rewrite nextinstr_rsp. rewrite Pregmap.gso by congruence.
         rewrite Pregmap.gss.
         simpl in ISDEF. unfold is_ptr in ISDEF.
         destr_in ISDEF. inv ISDEF. unfold current_sp, current_frame_sp in Heqv1.
         revert Heqv1.
         repeat destr; inversion 1. eauto.
       * intros; apply val_inject_nextinstr.
         intros; apply val_inject_set; auto.
         intros; apply val_inject_set; auto.
         assert (v0 = parent_sp (Mem.stack_adt m1)).
         revert ISDEF. rewrite Heqs.  simpl. unfold is_ptr. destr. 
         simpl.
         revert ISDEF. simpl. unfold is_ptr. destr. inversion 1; subst. inv ISDEF.
         inv IPS_REC.
         -- simpl in Heqv1. inv Heqv1.
         -- simpl in Heqv1. inv Heqv1.
         -- simpl in Heqv1. rewrite BLOCKS0 in Heqv1. inv Heqv1.
            econstructor. eauto.
            rewrite Ptrofs.add_zero_l.
            rewrite Ptrofs.add_unsigned.
            f_equal. setoid_rewrite Ptrofs.unsigned_repr. simpl.
            rewrite size_frames_one.
            rewrite SIZE0.
            rewrite SIZE. rewrite Z.max_r by (apply frame_size_pos). omega.
            Lemma max_align:
              forall x, 0 <= x ->
                   Z.max 0 (align x 8) = align (Z.max 0 x) 8.
            Proof.
              intros.
              rewrite ! Z.max_r; auto.
              etransitivity. 2: apply align_le. auto. omega.
            Qed.
            generalize (Mem.size_stack_below m1).
            generalize (size_stack_pos (Mem.stack_adt m1)).
            rewrite Heqs. simpl.
            rewrite ! size_frames_one. rewrite SIZE, SIZE0.
            generalize Mem.stack_limit_range. omega.
            rewrite Z.max_r by apply frame_adt_size_pos. omega.
         
       * red. rewrite nextinstr_rsp.
         rewrite ! Pregmap.gso by congruence.
         rewrite Pregmap.gss. simpl. inversion 1; subst.
         repeat rewrite_stack_blocks. rewrite Ptrofs.add_unsigned. rewrite AGSP. rewrite Heqs. simpl.
         rewrite size_frames_one.
         rewrite Ptrofs.unsigned_repr. rewrite size_frames_nil. rewrite Z.max_r by apply frame_adt_size_pos.
         rewrite Ptrofs.unsigned_repr by omega.
         omega.
         rewrite Z.max_r by apply frame_adt_size_pos.
         rewrite Ptrofs.unsigned_repr by omega. 
         generalize (Mem.size_stack_below m1). rewrite Heqs. simpl. rewrite size_frames_one.
         generalize (size_stack_pos s). 
         generalize (frame_adt_size_pos f0) (align_le (frame_adt_size f0) 8).
         generalize Mem.stack_limit_range. omega.
       * red. rewrite nextinstr_rsp.
         rewrite ! Pregmap.gso by congruence.
         rewrite Pregmap.gss. simpl. inversion 1. subst. clear H0.
         rewrite Ptrofs.add_unsigned.
         rewrite Ptrofs.unsigned_repr_eq. rewrite AGSP.
         rewrite Z.max_r by apply frame_adt_size_pos.
         rewrite Ptrofs.unsigned_repr by omega.

         Lemma mod_divides:
           forall a b c,
             c <> 0 ->
             (a | c) ->
             (a | b) ->
             (a | b mod c).
         Proof.
           intros.
           rewrite Zmod_eq_full.
           apply Z.divide_sub_r. auto.
           apply Z.divide_mul_r. auto. auto.
         Qed.
         apply mod_divides. vm_compute. congruence. rewrite Ptrofs.modulus_power.
         exists (two_p (Ptrofs.zwordsize - 3)). change 8 with (two_p 3). rewrite <- two_p_is_exp. f_equal. vm_compute. congruence. omega.
         apply Z.divide_add_r.
         apply Z.divide_sub_r.
         apply Mem.stack_limit_aligned.
         apply size_stack_divides.
         apply align_divides. omega.
       * rewrite nextinstr_rsp.
         rewrite ! Pregmap.gso by congruence.
         rewrite Pregmap.gss.
         f_equal. unfold newostack.
         simpl. rewrite Z.max_r. rewrite Ptrofs.add_unsigned.
         rewrite AGSP.
         rewrite Ptrofs.unsigned_repr by omega.
         reflexivity.
         apply frame_adt_size_pos.
       * red. intros b' delta0 o k p JB0.
         repeat rewrite_perms. destr. intro PERMS.
         generalize (NIB b' delta0 o k p JB0 PERMS).
         intros (LE & INS).
         destruct (peq b b').
         -- subst.
            rewrite perm_stack_eq in PERMS; eauto.
            2: rewrite Heqs; econstructor; eauto.
            2: rewrite Heqs. 2: left. 2: left. 2: red; rewrite BLOCKS; left; reflexivity.
            rewrite <- SIZE in PERMS.
            apply zle_zlt in PERMS. rewrite <- andb_assoc in Heqb0. rewrite PERMS in Heqb0. inv Heqb0.
         -- repeat rewrite_stack_blocks. rewrite Heqs. simpl. 
            rewrite Heqs in INS.
            rewrite in_stack_cons in INS. destruct INS.
            rewrite in_frames_cons in H0; destruct H0. 2: easy.
            red in H0. unfold get_frame_blocks in H0. rewrite BLOCKS in H0. simpl in H0. clear - H0 n; intuition.
            rewrite in_stack_cons. split; auto.
            rewrite Ptrofs.unsigned_repr by omega.
            unfold newostack.
            rewrite SIZE.
            destruct (zle (Ptrofs.unsigned (Ptrofs.repr (Mem.stack_limit - size_stack s - align ((frame_size fi)) 8)) + align ((frame_size fi)) 8) (o + delta0)); auto.
            exfalso.
            apply Z.gt_lt in g0.

            rewrite AGSP in LE, g0.
            
            assert (max_perm: forall m b o k p, Mem.perm m b o k p -> Mem.perm m b o Max Nonempty).
            {
              intros.
              eapply Mem.perm_implies.
              eapply Mem.perm_max. eauto. constructor.
            }
            generalize (Mem.free_range_perm _ _ _ _ _ FREE). intro FP.
            assert (LT: 0 < frame_size fi).
            {
              destruct (zlt 0 (frame_size fi)); auto.
              assert (frame_size fi = 0). generalize (frame_size_pos fi); omega.
              rewrite H1 in g0.
              change (align 0 8) with 0 in g0. omega.
            }
            revert LE g0. rewrite Heqs.

            simpl. rewrite size_frames_one.
            rewrite SIZE. rewrite Z.sub_add_distr. intros.
            set (delta := Mem.stack_limit - size_stack s - align ((frame_size fi)) 8) in *.
            destruct (zlt (o + delta0) (delta + frame_size fi)).
            ++
              assert (DISJ: forall ofs , Mem.perm m1 b ofs Cur Freeable -> bstack <> bstack \/ o + delta0 <> ofs + delta).
              intros; eapply Mem.mi_no_overlap. apply MINJ. apply not_eq_sym. apply n. auto. auto. eapply max_perm; eauto.
              eapply max_perm; eauto.
              assert (exists o2, 0 <= o2 < frame_size fi /\ o + delta0 = o2 + delta) as EX.
              {
                exists (o + delta0 - delta). omega.
              }
              destruct EX as (o2 & RNG & EQ').
              edestruct DISJ; eauto.
            ++ assert (delta + frame_size fi <= o + delta0 < delta + align (frame_size fi) 8).
               omega.
               assert (exists o2, frame_size fi <= o2 < align (frame_size fi) 8 /\ o + delta0 = o2 + delta) as EX.
               {
                 exists (o + delta0 - delta).
                 omega.
               }
               destruct EX as (o2 & RNG & EQ').
               eapply IP. 4: apply PERMS.  3: eauto. 2: apply JB.
               rewrite Heqs. left. left. red; rewrite BLOCKS. left; reflexivity. omega.
       * repeat rewrite_stack_blocks. rewrite Heqs. simpl. constructor.
         eapply perm_stack_inv. eauto.
         intros. repeat rewrite_perms. destr.
         repeat rewrite andb_true_iff in Heqb1. destruct Heqb1 as ((A & B) & C).
         destruct (peq b b0); simpl in *; try congruence. subst.
         exploit Mem.stack_norepet. rewrite Heqs. intro ND; inv ND.
         eapply H5 in H0; eauto.
         rewrite in_frames_cons; left.
         red. unfold get_frame_blocks. rewrite BLOCKS. left. reflexivity.
       * red. intros b0 fi0 delta' INSTK JB0 b2 o delta2 k p JB2 PERMS.
         revert INSTK. repeat rewrite_stack_blocks. rewrite Heqs. simpl. intros [[]|INSTK].
         eapply IP with (k:= k) (p:=p); eauto. rewrite Heqs. simpl. right; eauto. 
         revert PERMS. repeat rewrite_perms. destr.
       * rewnb. xomega.
       * repeat rewrite_stack_blocks. rewrite Heqs. simpl. auto. simpl in SPinstack. destruct SPinstack; auto.
         destruct H0 as [IFR|[]]. red in c.
         revert c. repeat rewrite_stack_blocks. rewrite Heqs. simpl.
         unfold init_sp in init_sp_ptr. setoid_rewrite init_sp_ptr.
         intro INS.
         exploit Mem.stack_norepet. rewrite Heqs. intro ND; exfalso; inv ND.
         apply (H3 binit_sp).
         rewrite in_frames_cons; left; eapply in_frame'_in_frame; eauto.
         rewrite in_stack_cons in INS; destruct INS; auto; easy.

     + (* load parent pointer *)
       unfold Asm.exec_instr in EI; simpl in EI.
       unfold check_top_frame in EI.
       destruct (Mem.stack_adt m1) eqn:S1; try congruence.
       repeat destr_in EI.
       repeat destr_in Heqb.
       apply andb_true_iff in H0; destruct H0 as (A & B).
       apply ZEQ in B. subst.
       destruct Forall_dec; simpl in A; try congruence. clear A.
       assert (RNGframe: 0 <= align (frame_adt_size f0) 8 < Ptrofs.max_unsigned).
       {
         generalize (Mem.size_stack_below m1').
         generalize (size_stack_pos (Mem.stack_adt m1')). rewrite S1.
         generalize (Mem.stack_limit_range).
         simpl. rewrite size_frames_cons.
         generalize (frame_adt_size_pos f0) (align_le (frame_adt_size f0) 8) (size_stack_pos s).
         split. omega.
         eapply Z.le_lt_trans. apply (Z.le_max_l _ (size_frames t0)). omega.
       }
       exists j, ostack; eexists; eexists; split. eauto.
       split; auto.
       inversion MS; subst; econstructor; eauto.
       * rewrite nextinstr_rsp.
         destruct (preg_eq RSP rd).
         rewrite e. rewrite Pregmap.gss. congruence.
         rewrite Pregmap.gso. eauto. auto.
       * intros; apply val_inject_nextinstr.
         intros; apply val_inject_set; auto. rewrite S1 in *.
         simpl in Heqo.
         unfold is_ptr in Heqo; destr_in Heqo. inv Heqo.
         inv IS. 
         rewrite <- Heqv0. unfold current_sp. destr. inv Heqv0.
         inv IPS_REC. inv Heqv0. simpl in *.
         repeat destr_in Heqv0. inv BLOCKS0.
         rewrite RSPEQ. simpl.
         econstructor; eauto. rewrite Ptrofs.add_zero_l.
         rewrite Ptrofs.add_unsigned. 
         rewrite AGSP. rewrite S1.
         simpl. rewrite ! size_frames_one.
         rewrite <- SIZE0.
         repeat rewrite Z.max_r by (apply frame_adt_size_pos). f_equal.
         rewrite Ptrofs.unsigned_repr.
         omega. omega.
         auto.
       * red. rewrite nextinstr_rsp.
         rewrite Pregmap.gso; eauto.
       * red. rewrite nextinstr_rsp.
         rewrite Pregmap.gso; eauto.
       * rewrite nextinstr_rsp.
         rewrite Pregmap.gso; eauto.
  Qed.

  Definition asm_prog_no_rsp (ge: Genv.t Asm.fundef unit):=
    forall b f,
      Genv.find_funct_ptr ge b = Some (Internal f) ->
      asm_code_no_rsp (fn_code f).

  Hypothesis prog_no_rsp: asm_prog_no_rsp ge.

  Context `{ecprops: !ExternalCallsProps mem}.

  Lemma inj_incr_sep_same:
    forall j j' m1 m2 b1 b2 delta,
      inject_incr j j' ->
      inject_separated j j' m1 m2 ->
      j' b1 = Some (b2, delta) ->
      Mem.valid_block m2 b2 ->
      j b1 = Some (b2, delta).
  Proof.
    intros.
    destruct (j b1) eqn:JB.
    destruct p. eapply H in JB; eauto.
    congruence.
    exploit H0; eauto. intuition congruence.
  Qed.

  Lemma set_res_no_rsp:
    forall res vres rs,
      no_rsp_builtin_preg res ->
      set_res res vres rs RSP = rs RSP.
  Proof.
    induction res; simpl.
    - intros. eapply Pregmap.gso. auto.
    - auto.
    - intros vres rs (NR1 & NR2).
      rewrite IHres2; auto.
  Qed.

  Lemma val_inject_set_res:
    forall r rs1 rs2 v1 v2 j,
      Val.inject j v1 v2 ->
      (forall r0, Val.inject j (rs1 r0) (rs2 r0)) ->
      forall r0, Val.inject j (set_res r v1 rs1 r0) (set_res r v2 rs2 r0).
  Proof.
    induction r; simpl; intros; auto.
    apply val_inject_set; auto.
    eapply IHr2; eauto.
    apply Val.loword_inject. auto.
    intros; eapply IHr1; eauto.
    apply Val.hiword_inject. auto.
  Qed.

  Definition init_data_diff (id: init_data) (i: ident) :=
    match id with
      Init_addrof ii _ => ii <> i
    | _ => True
    end.

  Lemma store_init_data_eq:
    forall F V m (ge: _ F V) id gv b o i,
      init_data_diff i id ->
      Genv.store_init_data (Genv.add_global ge (id,gv)) m b o i =
      Genv.store_init_data ge m b o i.
  Proof.
    destruct i; simpl; intros; auto.
    unfold Genv.find_symbol; simpl. 
    rewrite Maps.PTree.gso; auto.
  Qed.

  Lemma store_init_data_list_eq:
    forall F V id i, 
      Forall (fun x => init_data_diff x id) i ->
      forall m (ge: _ F V) gv b o,
        Genv.store_init_data_list (Genv.add_global ge (id,gv)) m b o i =
        Genv.store_init_data_list ge m b o i.
  Proof.
    induction 1; simpl; intros; auto.
    rewrite store_init_data_eq; auto.
    destr. 
  Qed.

  Lemma alloc_global_eq:
    forall F V (l: (ident * option (globdef F V))) m (ge: _ F V) id gv,
      (forall v, snd l = Some (Gvar v) -> Forall (fun x => init_data_diff x id) (gvar_init v)) ->
      Genv.alloc_global (Genv.add_global ge (id,gv)) m l =
      Genv.alloc_global ge m l .
  Proof.
    destruct l; simpl; intros.
    repeat (destr; [idtac]).
    rewrite store_init_data_list_eq. auto.
    apply H; auto.
  Qed.

  Lemma alloc_globals_eq:
    forall F V (l: list (ident * option (globdef F V))) m (ge: _ F V) id gv,
      (forall x v, In x l -> snd x = Some (Gvar v) -> Forall (fun x => init_data_diff x id) (gvar_init v)) ->
      Genv.alloc_globals (Genv.add_global ge (id,gv)) m l =
      Genv.alloc_globals ge m l .
  Proof.
    induction l; simpl; intros; eauto.
    rewrite alloc_global_eq. destr.
    apply IHl. intros; eauto.
    eauto.
  Qed.

  Lemma find_symbol_add_globals_other:
    forall F V l (ge: _ F V) s,
      ~ In s (map fst l) ->
      Genv.find_symbol (Genv.add_globals ge l) s =
      Genv.find_symbol ge s.
  Proof.
    induction l; simpl; intros; eauto.
    rewrite IHl.
    unfold Genv.find_symbol; simpl.
    apply Maps.PTree.gso. intuition. intuition.
  Qed.


  Lemma find_symbol_add_global_other:
    forall F V l (ge: _ F V) s,
      s <> fst l ->
      Genv.find_symbol (Genv.add_global ge l) s =
      Genv.find_symbol ge s.
  Proof.
    destruct l; simpl; intros; eauto.
    unfold Genv.find_symbol; simpl.
    apply Maps.PTree.gso. intuition. 
  Qed.

  Lemma find_symbol_none_add_global:
    forall F V (ge: Genv.t F V) a i,
      Genv.find_symbol (Genv.add_global ge a) i = None ->
      i <> fst a /\ Genv.find_symbol ge i = None.
  Proof.
    unfold Genv.find_symbol; simpl.
    intros F V ge0 a i.
    rewrite Maps.PTree.gsspec.
    destr.
  Qed.

  Lemma find_symbol_none_add_globals:
    forall F V a (ge: Genv.t F V) i,
      Genv.find_symbol (Genv.add_globals ge a) i = None ->
      ~ In i (map fst a) /\ Genv.find_symbol ge i = None.
  Proof.
    induction a; simpl; intros; eauto.
    apply IHa in H.
    destruct H as (H1 & H).
    apply find_symbol_none_add_global in H; auto.
    intuition.
  Qed.

  Lemma find_symbol_none_not_in_defs:
    forall F V (p: program F V) i,
      Genv.find_symbol (Genv.globalenv p) i = None ->
      ~ In i (map fst (prog_defs p)).
  Proof.
    unfold Genv.globalenv.
    intros F V p.
    generalize (Genv.empty_genv F V (prog_public p)).
    generalize (prog_defs p).
    induction l; simpl; intros; eauto.
    apply find_symbol_none_add_globals in H.
    destruct H as (A & B).
    apply find_symbol_none_add_global in B.
    destruct B as (B & C).
    intuition.    
  Qed.

  Lemma extcall_arg_inject:
    forall j g rs1 m1 arg1 loc rs2 m2,
      extcall_arg rs1 m1 loc arg1 ->
      (forall r, Val.inject j (rs1 r) (rs2 r)) ->
      Mem.inject j g m1 m2 ->
      exists arg2,
        extcall_arg rs2 m2 loc arg2 /\
        Val.inject j arg1 arg2.
  Proof.
    destruct 1; simpl; intros.
    eexists; split; try econstructor; eauto.
    exploit Mem.loadv_inject; eauto.
    apply Val.offset_ptr_inject; eauto.
    intros (v2 & LOAD & INJ).
    eexists; split; try econstructor; eauto.
  Qed.

  Lemma extcall_arg_pair_inject:
    forall j g rs1 m1 arg1 ty rs2 m2,
      extcall_arg_pair rs1 m1 ty arg1 ->
      (forall r, Val.inject j (rs1 r) (rs2 r)) ->
      Mem.inject j g m1 m2 ->
      exists arg2,
        extcall_arg_pair rs2 m2 ty arg2 /\
        Val.inject j arg1 arg2.
  Proof.
    destruct 1; simpl; intros.
    eapply extcall_arg_inject in H; eauto.
    destruct H as (arg2 & EA & INJ);
      eexists; split; try econstructor; eauto.
    eapply extcall_arg_inject in H; eauto.
    destruct H as (arg2 & EA & INJ).
    eapply extcall_arg_inject in H0; eauto.
    destruct H0 as (arg3 & EA1 & INJ1).
    eexists; split; try econstructor; eauto.
    apply Val.longofwords_inject; eauto.
  Qed.

  Lemma extcall_arguments_inject:
    forall j g rs1 m1 args1 sg rs2 m2,
      extcall_arguments rs1 m1 sg args1 ->
      (forall r, Val.inject j (rs1 r) (rs2 r)) ->
      Mem.inject j g m1 m2 ->
      exists args2,
        extcall_arguments rs2 m2 sg args2 /\
        Val.inject_list j args1 args2.
  Proof.
    unfold extcall_arguments.
    intros j g rs1 m1 args1 sg rs2 m2.
    revert args1. generalize (loc_arguments sg).
    induction 1; simpl; intros; eauto.
    exists nil; split; try econstructor.
    eapply extcall_arg_pair_inject in H; eauto.
    decompose [ex and] H.
    edestruct IHlist_forall2 as (a2 & EA & INJ); eauto.
    eexists; split; econstructor; eauto.
  Qed.

  Lemma set_pair_no_rsp:
    forall p res rs,
      no_rsp_pair p ->
      set_pair p res rs RSP = rs RSP.
  Proof.
    destruct p; simpl; intros; rewrite ! Pregmap.gso; intuition. 
  Qed.

  Lemma val_inject_set_pair:
    forall j p res1 res2 rs1 rs2,
      (forall r, Val.inject j (rs1 r) (rs2 r)) ->
      Val.inject j res1 res2 ->
      forall r,
        Val.inject j (set_pair p res1 rs1 r) (set_pair p res2 rs2 r).
  Proof.
    destruct p; simpl; intros; eauto.
    apply val_inject_set; auto.
    repeat (intros; apply val_inject_set; auto).
    apply Val.hiword_inject; auto.
    apply Val.loword_inject; auto.
  Qed.

  Theorem step_simulation:
    forall S1 t S2,
      Asm.step init_stk ge S1 t S2 ->
      forall j ostack S1' (MS: match_states j ostack S1 S1'),
      exists j' ostack' S2',
        step ge S1' t S2' /\
        match_states j' ostack' S2 S2'.
  Proof.
    destruct 1; intros; inversion MS; subst.
    - (* internal step *)
      generalize (RINJ PC); rewrite H. inversion 1; subst.
      assert (j b = Some (b,0)) as JB.
      {
        eapply GLOBFUN_INJ. eauto.
      }
      rewrite JB in H7; inv H7. 
      assert (asm_instr_no_rsp i).
      {
        eapply prog_no_rsp. eauto.
        eapply Asmgenproof0.find_instr_in; eauto.
      }
      destruct (exec_instr_inject' _ _ _ _ _ _ _ _ _ _ MS H4 (asmgen_no_change_stack i) H2)
        as ( j' & ostack' & rs2' & m2' & EI' & MS' & INCR).
      do 3 eexists; split.
      eapply exec_step_internal; eauto.
      rewrite Ptrofs.add_zero. eauto.
      eauto.
    - (* builtin step *)
      edestruct (eval_builtin_args_inject) as (vargs' & Hargs & Hargsinj).
      6: eauto.
      eauto. eauto. eauto.
      eauto. 
      eapply GLOBSYMB_INJ.
      edestruct (external_call_mem_inject_gen ef ge ge)
        as (j' & vres' & m2' & EC & RESinj & MemInj & Unch1 & Unch2 & INCR & SEP).
      apply meminj_preserves_globals'_symbols_inject.
      eauto.
      eauto.
      eapply Mem.inject_push_new_stage_left. eauto.
      apply no_stack_no_nil; auto.
      eauto.
      assert (j b = Some (b,0)) as JB.
      {
        eapply GLOBFUN_INJ. eauto.
      }
      generalize (RINJ PC); rewrite H. inversion 1; subst.
      rewrite JB in H10; inv H10.
      exploit Mem.unrecord_stack_block_inject_left. apply MemInj. eauto.
      unfold upstar. simpl.
      rewrite GSPEC.
      destr. destr.
      destruct (Mem.stack_adt m) eqn:STK2. simpl in *; easy. simpl in n0. omega. 
      repeat rewrite_stack_blocks. unfold is_stack_top. simpl. easy.
      intro MemInj'.
      do 3 eexists; split.
      eapply exec_step_builtin.
      eauto.
      eauto. 
      rewrite Ptrofs.add_zero; eauto.
      eauto.
      eauto.
      auto.
      reflexivity.
      econstructor.
      + eauto.
      + repeat rewrite_stack_blocks. simpl; eauto.
      + simpl; intros. unfold upstar. simpl.
        repeat rewrite_stack_blocks. simpl. apply GSPEC.
      + rewrite nextinstr_nf_rsp.
        rewrite set_res_no_rsp.
        rewrite Asmgenproof0.undef_regs_other.
        eauto.
        intros; intro; subst. rewrite in_map_iff in H7.
        destruct H7 as (x & EQ & IN).
        apply preg_of_not_rsp in EQ. congruence.
        auto.
      + intros. apply val_inject_nextinstr_nf.
        apply val_inject_set_res; auto.
        apply val_inject_undef_regs; auto.
        intros; eapply val_inject_incr; eauto.
      + red; rewnb. auto.
      + red. rewrite nextinstr_nf_rsp.
        rewrite set_res_no_rsp; auto.
        rewrite Asmgenproof0.undef_regs_other.
        repeat rewrite_stack_blocks. simpl; auto.
        intros r INR EQ; subst.
        rewrite in_map_iff in INR.
        destruct INR as (x & EQ & IN).
        apply preg_of_not_rsp in EQ. congruence.
      (* + red. erewrite <- external_call_stack_blocks. 2: eauto. *)
      (*   rewrite nextinstr_nf_rsp. *)
      (*   rewrite set_res_no_rsp; auto. *)
      (*   rewrite Asmgenproof0.undef_regs_other. eauto. *)
      (*   intros; intro; subst. *)
      (*   rewrite in_map_iff in H6. *)
      (*   destruct H6 as (x & EQ & IN). *)
      (*   apply preg_of_not_rsp in EQ. congruence. *)
      (* + erewrite <- external_call_stack_blocks; eauto. *)
      + red. 
        rewrite nextinstr_nf_rsp.
        rewrite set_res_no_rsp; auto.
        rewrite Asmgenproof0.undef_regs_other. eauto.
        intros r' INR; intro; subst.
        rewrite in_map_iff in INR.
        destruct INR as (x & EQ & IN).
        apply preg_of_not_rsp in EQ. congruence.
      + red. intros ofs0 k p PERM.
        revert PERM; rewrite_perms. eauto.
        destruct NS as (fr & fi & r & STK' & BLK & ZERO & PUB).
        rewrite STK'.
        rewrite in_stack_cons; left. 
        rewrite in_frames_cons; left. red; unfold get_frame_blocks; rewrite <- BLK. simpl. auto.
      + red.
        intros.
        eapply ec_perm_unchanged. eapply external_call_spec. eauto.
        eauto.
        intros. eapply PBS in H8. destruct H8.  intro A; inv A; inv H10. 
        eauto.
      + red.
        erewrite <- external_call_stack_blocks. 2: eauto.
        eauto.
      + rewrite nextinstr_nf_rsp.
        rewrite set_res_no_rsp; auto.
        rewrite Asmgenproof0.undef_regs_other. eauto.
        intros ? INR; intro; subst.
        rewrite in_map_iff in INR.
        destruct INR as (x & EQ & IN).
        apply preg_of_not_rsp in EQ. congruence.
      + red. intros b delta o k p JB1 PERM.
        repeat rewrite_stack_blocks. simpl.
        destruct (j b) eqn:A. destruct p0.
        exploit INCR. eauto. eauto. intro JB2. rewrite JB1 in JB2; inv JB2.
        eapply NIB; eauto.
        eapply Mem.perm_max in PERM. eapply Mem.push_new_stage_perm.
        eapply external_call_max_perm. eauto. red; rewnb.
        eapply Mem.valid_block_inject_1; eauto.
        eapply Mem.unrecord_stack_block_perm. eauto. eauto.
        exploit SEP. eauto. eauto.
        unfold Mem.valid_block.  rewnb. intuition congruence. 
      + eapply inject_stack_incr. apply INCR.
        repeat rewrite_stack_blocks. simpl.
        eapply perm_stack_inv. eauto. intros.
        repeat rewrite_perms; auto. rewrite_stack_blocks. rewrite in_stack_cons; auto.
      + red.
        repeat rewrite_stack_blocks. simpl.
        intros b fi delta INS J'B b' o delta' k p J'B' PERM.
        exploit inj_incr_sep_same. eauto. eauto. apply J'B. auto.
        exploit inj_incr_sep_same. eauto. eauto. apply J'B'. auto.
        intros NJB' NJB.
        eapply IP; eauto.
        eapply Mem.perm_max in PERM. eapply Mem.push_new_stage_perm.
        eapply external_call_max_perm. eauto. red; rewnb.
        eapply Mem.valid_block_inject_1; eauto.
        eapply Mem.unrecord_stack_block_perm. eauto. eauto.
      + intros.
        eapply INCR; eauto.
      + intros.
        eapply INCR; eauto.
      + destruct GLOBSYMB_INJ.
        split. intros.
        eapply INCR; eauto.
        intros.
        destruct (j b1) eqn:JB1.
        destruct p.
        exploit INCR; eauto. rewrite H10; intro X; inv X.
        eauto.
        exploit SEP; eauto. unfold Mem.valid_block; rewnb. intros (NV1 & NV2).
        simpl; unfold Genv.block_is_volatile.
        rewrite ! find_var_info_none_ge.
        auto.
        unfold Mem.valid_block in NV1. xomega.
        unfold Mem.valid_block in NV2. xomega.
      + etransitivity. apply GlobLe. fold Ple. rewnb. xomega.
      + etransitivity. apply GlobLeT. fold Ple. rewnb. xomega.
      + repeat rewrite_stack_blocks. simpl; eauto.
    - (* external step *)
      edestruct (extcall_arguments_inject) as (vargs' & Hargs & Hargsinj).
      eauto.
      eauto. eauto. 
      edestruct (external_call_mem_inject_gen ef ge ge)
        as (j' & vres' & m2' & EC & RESinj & MemInj & Unch1 & Unch2 & INCR & SEP).
      apply meminj_preserves_globals'_symbols_inject. eauto.
      eauto.
      eauto.
      eauto. 
      generalize (RINJ PC); rewrite H. inversion 1; subst.
      assert (j b = Some (b,0)) as JB.
      {
        eapply GLOBFUN_INJ. eauto.
      }
      rewrite JB in H9; inv H9.
      exploit (Mem.unrecord_stack_block_inject_left _ _ _ _ _ MemInj H3).
      destruct (Mem.stack_adt m) eqn:STK2. simpl in *; easy.
      rewrite ! GSPEC. simpl.
      inv TIN. rewrite STK2 in H6; inv H6.
      destruct lprog. simpl in STK. revert init_sp_ptr. unfold init_sp. rewrite <- STK. simpl; inversion 1.
      simpl in STK. inv STK. simpl. left. destr. rewrite app_length. simpl.
      revert init_sp_ptr; unfold init_sp.
      destruct init_stk; simpl; auto. inversion 1. intros _.
      destr. omega.
      repeat rewrite_stack_blocks. inv TIN. unfold is_stack_top. simpl. easy.
      intro MemInj'.
      do 3 eexists; split.
      eapply exec_step_external.
      eauto.
      eauto.
      eauto.
      generalize (RINJ RSP). destruct (rs RSP); simpl in *; inversion 1; subst; try congruence.
      generalize (RINJ RA). destruct (rs RA); simpl in *; inversion 1; subst; try congruence.
      destruct Tptr; try easy.
      destruct Tptr; try easy.
      destruct Tptr; try easy.
      destruct Tptr; try easy.
      generalize (RINJ RSP). destruct (rs RSP); simpl in *; inversion 1; subst; try congruence.
      generalize (RINJ RA). destruct (rs RA); simpl in *; inversion 1; subst; try congruence.
      eauto.
      reflexivity.

      econstructor.
      + eauto.
      + repeat rewrite_stack_blocks.
        instantiate (1 := tl lprog).
        destruct lprog. inv TIN. exfalso.
        revert init_sp_ptr; unfold init_sp; simpl in STK; rewrite <- STK. rewrite <- H6. inversion 1.
        revert EQ; rewrite_stack_blocks. intro A; rewrite A. simpl.
        rewrite STK in A. simpl in A ; inv A. auto.
      + simpl. repeat rewrite_stack_blocks. inv TIN. simpl. intros.
        rewrite GSPEC. rewrite <- H6. simpl.
        rewrite ! length_tl.
        repeat destr; try omega. f_equal.
        cut (O < length lprog)%nat. omega.
        destruct lprog; simpl; try omega.
        revert init_sp_ptr; unfold init_sp; simpl in STK; rewrite <- STK. rewrite <- H6. inversion 1.        
      + repeat rewrite Pregmap.gso by (congruence). 
        rewrite set_pair_no_rsp.
        rewrite Asmgenproof0.undef_regs_other.
        rewrite Asmgenproof0.undef_regs_other.
        eauto.
        intros ? INR; intro; subst. rewrite in_map_iff in INR.
        destruct INR as (x & EQ & IN).
        apply preg_of_not_rsp in EQ. congruence.
        intros; intro; subst. clear - H6; simpl in *; intuition congruence.
        auto.
      + intros; apply val_inject_set.
        intros; apply val_inject_set.
        intros; apply val_inject_set_pair; auto.
        apply val_inject_undef_regs; auto.
        apply val_inject_undef_regs; auto.
        intros; eapply val_inject_incr; eauto.
        intros; eapply val_inject_incr; eauto.
        auto.
      + red; rewnb; eauto.
      + red. repeat rewrite Pregmap.gso by (congruence). 
        rewrite set_pair_no_rsp.
        rewrite Asmgenproof0.undef_regs_other.
        rewrite Asmgenproof0.undef_regs_other.
        repeat rewrite_stack_blocks. inv TIN. simpl.
        intros ostack RRSP. apply AGSP in RRSP. rewrite <- H6 in RRSP. simpl in RRSP. change (size_frames nil) with 0 in RRSP. omega.
        intros ? INR; intro; subst. rewrite in_map_iff in INR.
        destruct INR as (x & EQ & IN).
        apply preg_of_not_rsp in EQ. congruence.
        intros; intro; subst. clear - H6; simpl in *; intuition congruence.
        auto.
      + red.
        repeat rewrite Pregmap.gso by (congruence). 
        rewrite set_pair_no_rsp.
        rewrite Asmgenproof0.undef_regs_other.
        rewrite Asmgenproof0.undef_regs_other.
        eauto.
        intros ? INR; intro; subst. rewrite in_map_iff in INR.
        destruct INR as (x & EQ & IN).
        apply preg_of_not_rsp in EQ. congruence.
        intros; intro; subst. clear - H6; simpl in *; intuition congruence.
        auto.
      + red.
        intros.
        eapply Mem.perm_max in H6.
        eapply external_call_max_perm in H6.
        2: eauto.
        eauto. eauto.
      + red.
        intros.
        eapply ec_perm_unchanged. eapply external_call_spec. eauto.
        eauto.
        intros. eapply PBS in H7. destruct H7.  intro A; inv A; inv H9.
        eauto.
      + red.
        erewrite <- external_call_stack_blocks. 2: eauto.
        eauto.
      + repeat rewrite Pregmap.gso by (congruence). 
        rewrite set_pair_no_rsp.
        rewrite Asmgenproof0.undef_regs_other.
        rewrite Asmgenproof0.undef_regs_other.
        eauto.
        intros ? INR; intro; subst. rewrite in_map_iff in INR.
        destruct INR as (x & EQ & IN).
        apply preg_of_not_rsp in EQ. congruence.
        intros; intro; subst. clear - H6; simpl in *; intuition congruence.
        auto. 
      + red. intros b delta o k p JB1 PERM.
        repeat rewrite_stack_blocks. inv TIN. simpl.
        destruct (j b) eqn:A. destruct p0.
        exploit INCR. eauto. eauto. intro JB2. rewrite JB1 in JB2; inv JB2.
        exploit NIB; eauto.
        eapply Mem.perm_max in PERM.
        eapply external_call_max_perm. eauto.
        eapply Mem.valid_block_inject_1; eauto.
        eapply Mem.unrecord_stack_block_perm; eauto. rewrite <- H6. rewrite in_stack_cons. intuition.
        exploit SEP. eauto. eauto. intuition congruence.
      + eapply inject_stack_incr; eauto.
        repeat rewrite_stack_blocks. inv IS. constructor. simpl.
        eapply perm_stack_inv. eauto.
        intros; repeat rewrite_perms; auto.
        rewrite <- H7. rewrite in_stack_cons; auto.
        simpl.
        eapply perm_stack_inv. eauto.
        intros; repeat rewrite_perms; auto.
        rewrite <- H7. rewrite in_stack_cons; auto.
      + red.
        repeat rewrite_stack_blocks.
        intros b fi delta INS J'B b' o delta' k p J'B' PERM.
        exploit inj_incr_sep_same. eauto. eauto. apply J'B. auto.
        exploit inj_incr_sep_same. eauto. eauto. apply J'B'. auto.
        intros.
        eapply IP; eauto.
        revert INS. inv TIN. simpl. auto.
        eapply Mem.perm_max in PERM.
        eapply external_call_max_perm. eauto.
        eapply Mem.valid_block_inject_1; eauto.
        eapply Mem.unrecord_stack_block_perm; eauto.
      + intros.
        eapply INCR; eauto.
      + intros.
        eapply INCR; eauto.
      + destruct GLOBSYMB_INJ.
        split. intros.
        eapply INCR; eauto.
        intros.
        destruct (j b1) eqn:JB1.
        destruct p.
        exploit INCR; eauto. rewrite H9; intro X; inv X.
        eauto.
        exploit SEP; eauto. intros (NV1 & NV2).
        simpl; unfold Genv.block_is_volatile.
        rewrite ! find_var_info_none_ge.
        auto.
        unfold Mem.valid_block in NV1. xomega.
        unfold Mem.valid_block in NV2.
        xomega. 
      + etransitivity. apply GlobLe. fold Ple; rewnb; xomega.
      + etransitivity. apply GlobLeT. fold Ple; rewnb; xomega.
      + repeat rewrite_stack_blocks. revert SPinstack. inv TIN. simpl. tauto.
  Qed.

End PRESERVATION.


  Lemma repr_stack_limit:
    Ptrofs.unsigned (Ptrofs.repr (Mem.stack_limit)) = Mem.stack_limit.
  Proof.
    apply Ptrofs.unsigned_repr.
    generalize (Mem.stack_limit_range); omega.
  Qed.
  
  Lemma match_initial_states s m0:
    Asm.initial_state prog s ->
    Genv.init_mem prog = Some m0 ->
    exists s' j ostack, match_states ((make_singleton_frame_adt (Genv.genv_next ge) 0 0 :: nil) :: nil) (Genv.genv_next ge) j ostack s s' /\
                   RawAsm.initial_state prog (Pregmap.init Vundef) m0 s'.
  Proof.
    inversion 1. subst.
    rename H into INIT.
    rename H0 into INITMEM.
    rename H1 into ALLOC.
    rename H2 into RSB.
    rewrite INITMEM. intro A; inv A.
    exploit Genv.initmem_inject; eauto. intro FLATINJ.
    assert  (ALLOCINJ:
               exists (f' : meminj) (m2' : mem) (b2 : block),
                 Mem.alloc m0 0 Mem.stack_limit = (m2', b2) /\
                 Mem.inject f' (flat_frameinj (length (Mem.stack_adt m0))) m2 m2' /\
                 inject_incr (Mem.flat_inj (Mem.nextblock m0)) f' /\
                 f' b = Some (b2, Mem.stack_limit) /\ (forall b0 : block, b0 <> b -> f' b0 = Mem.flat_inj (Mem.nextblock m2) b0)).
    {
      destruct (Mem.alloc m0 0 Mem.stack_limit) as (m2' & b2) eqn: ALLOC'.
      eapply Mem.alloc_right_inject in FLATINJ; eauto.
      exploit (Mem.alloc_left_mapped_inject _ _ _ _ _ _ _ _ b2 Mem.stack_limit FLATINJ ALLOC).
      - exploit Mem.alloc_result; eauto. intro; subst. red; rewnb. xomega.
      - apply Mem.stack_limit_range.
      - intros ofs k p. rewrite_perms. rewrite pred_dec_true; auto.
        generalize (Mem.stack_limit_range). intros; omega.
      - intros ofs k p. omega.
      - red. intro. generalize (size_chunk_pos chunk); omega.
      - unfold Mem.flat_inj. intros b0 delta' ofs k p. destr. inversion 1; subst.
        exploit Mem.alloc_result; eauto. intro; subst. xomega.
      - repeat rewrite_stack_blocks. easy.
      - intros (f' & INJ & INCR & FB & FOTHER).
        do 3 eexists. split; eauto. split; eauto. split; eauto. split; eauto.
        intros; rewrite FOTHER; auto.
        unfold Mem.flat_inj. exploit Mem.alloc_result; eauto. intro; subst.
        revert FB FOTHER. rewnb. repeat destr. intros; xomega.
        apply Plt_succ_inv in p. intuition. subst. contradict H. exploit Mem.alloc_result. apply ALLOC. intro; subst.
        rewnb. auto.
    }
    destruct ALLOCINJ as (f' & m2' & b2 & ALLOC' & ALLOCINJ & INCR & F'B & F'O).
    assert (b = b2).
    {
      exploit Mem.alloc_result. apply ALLOC.
      exploit Mem.alloc_result. apply ALLOC'. intros; subst. rewnb. congruence.
    }
    subst.
    assert (b2 = bstack).
    {
      unfold bstack.
      exploit Mem.alloc_result; eauto. intro; subst.
      erewrite <- Genv.init_mem_genv_next; eauto. fold ge; reflexivity.
    } subst.
    edestruct (Mem.range_perm_drop_2) with (p := Writable) as (m3' & DROP).
    red; intros; eapply Mem.perm_alloc_2; eauto.
    assert (DROPINJ: Mem.inject f' (flat_frameinj (length (Mem.stack_adt m0))) m2 m3').
    {
      eapply Mem.drop_outside_inject. apply ALLOCINJ. eauto.
      intros b' delta ofs k p FB1 PERM RNG.
      revert PERM; repeat rewrite_perms. destr. omega. intros.
      revert FB1; unfold Mem.flat_inj. rewrite F'O. unfold Mem.flat_inj. destr. auto.
    }
    assert (RSB': exists m4',
               Mem.record_stack_blocks (Mem.push_new_stage m3') (make_singleton_frame_adt' bstack frame_info_mono 0) = Some m4' /\
               Mem.inject f'
                          (flat_frameinj (length (Mem.stack_adt (Mem.push_new_stage m3')))) m3 m4').
    {
      edestruct Mem.record_stack_blocks_inject_parallel as (m4' & RSB' & RSBinj).
      apply Mem.push_new_stage_inject. apply DROPINJ. 7: eauto.
      instantiate (1 := make_singleton_frame_adt' bstack frame_info_mono 0).
      - red; red; intros.
        constructor; auto.
        simpl. rewrite F'B. inversion 1.
        eexists; split; eauto.
        split; simpl; intros; rewrite Z.max_r in H0; omega.
      - repeat rewrite_stack_blocks. easy.
      - red. intros b [A|[]].
        subst. unfold bstack; simpl.
        red. rewnb. fold ge. xomega.
      - intros b fi [A|[]]; inv A. intros o k p.
        rewrite_perms. intro PERM.
        eapply Mem.perm_drop_4 in PERM; eauto. revert PERM. repeat rewrite_perms.
        rewrite peq_true. simpl. auto.
      - unfold Mem.flat_inj. intros b1 b0 delta FB.
        destruct (peq b1 bstack); subst. rewrite F'B in FB; inv FB. tauto.
        rewrite F'O in FB; auto. unfold Mem.flat_inj in FB. destr_in FB. inv FB.
        tauto.
      - reflexivity.
      - repeat rewrite_stack_blocks. constructor. red; easy.
      - simpl. auto.
      - repeat rewrite_stack_blocks. simpl. omega.
      - eexists; split; eauto.
        eapply Mem.mem_inject_ext. eauto.
        simpl. intros.
        repeat rewrite_stack_blocks. simpl. unfold flat_frameinj.
        repeat destr; simpl; try omega; auto.
    }
    destruct RSB' as (m4' & RSB' & RSBINJ).
    eexists _, f', _; split.
    2: now (econstructor; eauto).
    econstructor; eauto.
    - apply Mem.inject_push_new_stage_left. apply RSBINJ.
      repeat rewrite_stack_blocks. congruence.
    - repeat rewrite_stack_blocks. instantiate (1:= nil::nil). reflexivity.
    - repeat rewrite_stack_blocks.
      unfold upstar, flat_frameinj.
      simpl. intros. repeat destr; try omega.
      f_equal. omega.
    - unfold rs0. rewrite Pregmap.gss. eauto.
    - intros. unfold rs0.
      repeat (intros; apply val_inject_set; auto).
      + unfold ge0. unfold Genv.symbol_address. destr; auto.
        eapply Genv.genv_symb_range in Heqo.
        econstructor; eauto.
        rewrite F'O.
        unfold Mem.flat_inj. rewrite pred_dec_true. eauto. rewnb. xomega.
        exploit Mem.alloc_result; eauto. intro; subst. rewrite H1. rewnb. apply Plt_ne. auto.
        reflexivity.
      + unfold Vnullptr; constructor.
      + econstructor. eauto. rewrite Ptrofs.add_zero_l. auto.
    - red; unfold bstack; rewnb. fold ge. xomega.
    - red. rewrite Pregmap.gss. inversion 1; subst.
      repeat rewrite_stack_blocks. simpl. rewrite repr_stack_limit. change (size_frames nil) with 0; omega.
    - red. rewrite Pregmap.gss. inversion 1; subst.
      rewrite repr_stack_limit. apply Mem.stack_limit_aligned.
    - red. intros o k p.
      repeat rewrite_perms. rewrite peq_true. intros (A & B).
      generalize (Mem.stack_limit_range). trim B; auto. trim B ; auto. split; auto. omega.
    - red; intros.
      repeat rewrite_perms. rewrite peq_true. split; auto. intros; constructor.
    - red.
      repeat rewrite_stack_blocks.
      repeat econstructor.
    - rewrite Pregmap.gss. eauto.
    - red.
      intros b delta o k p INJ. repeat rewrite_perms. destr. omega. intro P.
      rewrite F'O in INJ by auto. unfold Mem.flat_inj in INJ.
      revert INJ.
      apply Mem.perm_valid_block in P. red in P; revert P.
      rewnb. destr.
    - repeat rewrite_stack_blocks.
      repeat econstructor; eauto.
      + rewrite F'B. f_equal. f_equal.
        simpl. change (align (Z.max 0 0) 8) with 0. omega.
      + simpl. rewrite Z.max_r by omega. intros; omega.
    - red. repeat rewrite_stack_blocks. simpl.
      intros. destruct H as [[]|[[A|[]]|[]]]. destruct A as [A|[]]; inv A.
      simpl. rewrite Z.max_r by omega. change (align 0 8) with 0. omega.
    - intros.
      assert (Plt b (Genv.genv_next ge)).
      {
        unfold Genv.find_funct_ptr in H. repeat destr_in H.
        eapply Genv.genv_defs_range in Heqo; eauto.
      }
      rewrite F'O. unfold Mem.flat_inj. rewnb. fold ge. destr. xomega.
      apply Plt_ne; auto.
    - intros.
      assert (Plt b (Genv.genv_next ge)).
      {
        eapply Genv.genv_defs_range in H; eauto.
      }
      rewrite F'O. unfold Mem.flat_inj. rewnb. fold ge. destr. xomega.
      apply Plt_ne; auto.
    - split.
      simpl; intros.
      assert (Plt b (Genv.genv_next ge)).
      {
        eapply Genv.genv_symb_range in H; eauto.
      }
      rewrite F'O. unfold Mem.flat_inj. rewnb. fold ge. destr. xomega.
      apply Plt_ne; auto.
      intros b1 b2 delta FB. destruct (peq b1 bstack); subst.
      rewrite F'B in FB; inv FB; auto.
      rewrite F'O in FB; auto.
      unfold Mem.flat_inj in FB; repeat destr_in FB; auto.
    - rewnb. fold ge. xomega.
    - rewnb. fold ge. xomega.
    - repeat rewrite_stack_blocks. simpl. right; left; left. simpl. left. reflexivity.
  Qed.

  Lemma transf_final_states:
    forall istk isp j o st1 st2 r,
      match_states istk isp j o st1 st2 -> Asm.final_state st1 r -> final_state st2 r.
  Proof.
    inversion 1; subst.
    inversion 1; subst.
    econstructor.
    generalize (RINJ PC). rewrite H3. unfold Vnullptr. destruct ptr64; inversion 1; auto.
    generalize (RINJ RAX). rewrite H5. unfold Vnullptr. destruct ptr64; inversion 1; auto.
  Qed.
  
  Theorem transf_program_correct m:
    asm_prog_no_rsp ge ->
    Genv.init_mem prog = Some m ->
    forward_simulation (Asm.semantics prog
                                      ((make_singleton_frame_adt (Genv.genv_next ge) 0 0 :: nil) :: nil))
                       (RawAsm.semantics prog (Pregmap.init Vundef) m).
  Proof.
    intros APNR IM.
    eapply forward_simulation_step with (fun s1 s2 => exists j o, match_states ((make_singleton_frame_adt (Genv.genv_next ge) 0 0 :: nil) :: nil)  (Genv.genv_next ge) j o s1 s2).
    - simpl. reflexivity. 
    - simpl. intros s1 IS; inversion IS. rewrite IM in H; inv H.
      exploit match_initial_states. eauto. eauto.
      intros (s' & j & ostack & MS & MIS); eexists; split; eauto.
    - simpl. intros s1 s2 r (j & o & MS) FS. eapply transf_final_states; eauto.
    - simpl. intros s1 t s1' STEP s2 (j & o & MS). 
      edestruct step_simulation as (isp' & j' & o' & STEP' & MS'); eauto.
      reflexivity.
  Qed.
  
End WITHMEMORYMODEL.

