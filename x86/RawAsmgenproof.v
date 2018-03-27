Require Import Smallstep.
Require Import Machregs.
Require Import Asm.
Require Import Integers.
Require Import List.
Require Import ZArith.
(* Require Memimpl. *)
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
Require Import RawAsmgen.

Section WITHMEMORYMODEL.
  
  Context `{memory_model: Mem.MemoryModel }.
  Existing Instance inject_perm_upto_writable.


  Existing Instance mem_accessors_default.

  Context `{external_calls_ops : !ExternalCallsOps mem }.
  Context `{!EnableBuiltins mem}.
  Existing Instance symbols_inject_instance.
  Context `{external_calls_props : !ExternalCallsProps mem
                                    (memory_model_ops := memory_model_ops)
                                    }.

  Variable prog: Asm.program.
  Let ge := Genv.globalenv prog.
  Definition bstack: block := Genv.genv_next ge.
  Section PRESERVATION.

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
       Mem.perm m2 bstack ofs k p -> 0 <= ofs < Ptrofs.max_unsigned /\  perm_order Writable p.

  Definition perm_bstack_stack_limit m2:=
    forall (ofs : Z) (k : perm_kind),
      0 <= ofs < Mem.stack_limit ->
      Mem.perm m2 bstack ofs k Writable.

  Definition sp_aligned rs2:=
    forall ostack,
      rs2 # RSP = Vptr bstack ostack ->
      (8 | Ptrofs.unsigned ostack).

  Definition no_stack m2 :=
    exists fr fi,
      Mem.stack_adt m2 = (fr::nil)::nil /\
      (bstack,fi)::nil = frame_adt_blocks fr /\
      0 = frame_adt_size fr /\
      (forall o, frame_perm fi o = Public) /\
      frame_size fi = Mem.stack_limit.

  Inductive inject_perm_stack (j: meminj) (P: perm_type): stack_adt -> Prop :=
  | inject_perm_stack_nil:
      inject_perm_stack j P nil
  | inject_perm_stack_cons_nil l (IPS_REC: inject_perm_stack j P l):
      inject_perm_stack j P (nil::l)
  | inject_perm_stack_cons
      l fr b fi (IPS_REC: inject_perm_stack j P l)
      (JB: j b = Some (bstack, Mem.stack_limit - size_stack l - align (Z.max 0 (frame_size fi)) 8))
      (BLOCKS: frame_adt_blocks fr = (b,fi)::nil)
      (SIZE: frame_adt_size fr = frame_size fi)
      (PERM: forall o k p, 0 <= o < frame_size fi -> P b o k p)
      (* (ORDER: forall b', in_stack l b' -> Plt b' b) *):
      inject_perm_stack j P ((fr::nil)::l).

  Definition inject_padding (j: meminj) (m: mem) : Prop :=
    forall b fi delta,
      in_stack' (Mem.stack_adt m) (b,fi) ->
      j b = Some (bstack, delta) ->
      forall b' o delta' k p,
        j b' = Some (bstack, delta') ->
        Mem.perm m b' o k p ->
        ~ ( delta + Z.max 0 (frame_size fi) <= o + delta' < delta + align (Z.max 0 (frame_size fi)) 8).

  (* Fixpoint agree_sp_source rs (s: stack_adt) := *)
  (*   match s with *)
  (*     nil => rs # RSP = init_sp *)
  (*   | (fr::_)::r => *)
  (*     match frame_adt_blocks fr with *)
  (*     | (b,fi)::nil => rs # RSP = Vptr b Ptrofs.zero *)
  (*     | _ => False *)
  (*     end *)
  (*   | nil::r => agree_sp_source rs r *)
  (*   end. *)
  
  Inductive match_states: meminj -> Z -> state -> state -> Prop :=
  | match_states_intro:
      forall j (rs: regset) (m: mem) (rs': regset) m'
        (MINJ: Mem.inject j (fun n => if lt_dec n (length (Mem.stack_adt m)) then Some O else None) m m')
        (RSPzero: exists b, rs # RSP = Vptr b Ptrofs.zero )
        (RINJ: forall r, Val.inject j (rs # r) (rs' # r))
        (VB: Mem.valid_block m' bstack)
        (AGSP: agree_sp m rs')
        (* (AGSP1: agree_sp_source rs (Mem.stack_adt m)) *)
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
        (SPinstack: in_stack' (Mem.stack_adt m) (binit_sp,{| frame_size := 0; frame_perm := fun _ => Public |})),
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

  Definition is_ptr v :=
    match v with
      Vptr _ _ => True
    | _ => False
    end.

  Lemma is_ptr_dec v: {is_ptr v} + {~ is_ptr v}.
  Proof.
    destruct v; simpl; auto.
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
      (EXEC: Asm.exec_instr init_sp ge f i rs1 m1 = Next rs1' m1')
      init_sp'
      (init_sp_inject: Val.inject j init_sp init_sp'),
      exists rs2' m2',
        Asm.exec_instr init_sp' ge f i rs2 m2 = Next rs2' m2'
        /\ Mem.inject j g m1' m2'
        /\ (forall r, Val.inject j (rs1' # r) (rs2' # r)).
  (* should be proved already somewhere *)

  (* Lemma free_inject: *)
  (*   forall j g m1 b lo hi m2 m3 m1', *)
  (*     Mem.inject j g m1 m1' -> *)
  (*     Mem.free m1 b lo hi = Some m2 -> *)
  (*     (forall o k p, Mem.perm m1 b o k p -> lo <= o < hi) -> *)
  (*     (forall b0, is_stack_top (Mem.stack_adt m2) b0 -> b0 = b) -> *)
  (*     Mem.unrecord_stack_block m2 = Some m3 -> *)
  (*     g 1%nat = Some O -> *)
  (*     length (Mem.stack_adt m1') = 1%nat -> *)
  (*     no_stack m1' -> *)
  (*     Mem.inject j (fun n => g (S n)) m3 m1'. *)
  (* Proof. *)
  (*   intros j g m1 b lo hi m2 m3 m1' INJ FREE PERMRNG IST USB G1 LST NS. *)
  (*   eapply Mem.unrecord_stack_block_inject_left_zero. *)
  (*   eapply Mem.free_left_inject. eauto. eauto. eauto. *)
  (*   intros. eapply stack_inject_range in H. 2: eapply Mem.inject_stack_adt; eauto. *)
  (*   rewrite LST in H. omega. *)
  (*   intros. *)
  (*   apply IST in H. subst. intros PERM. *)
  (*   eapply Mem.perm_free in PERM. 2: eauto. destruct PERM. apply H. split; eauto. *)
  (*   auto. *)
  (* Qed. *)
  
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
        rewrite <- SIZE; apply frame_adt_size_pos. omega.
        rewrite <- SIZE; apply frame_adt_size_pos.
      + edestruct IHIS as (l1 & l2 & EQ & JB'); eauto. exists ((fr::nil)::l1),l2; split; auto. simpl. subst. reflexivity.
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
    forall j rs1 rs2 r
      (RINJ: forall r0, r0 = r \/ r0 = PC -> Val.inject j (rs1 r0) (rs2 r0)),
      Val.inject j (nextinstr rs1 r) (nextinstr rs2 r).
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

 Lemma alloc_inject:
    forall j ostack m1 (rs1 rs1': regset) fi b m1' m5 ofs_ra m2 m4,
      match_states j (Ptrofs.unsigned ostack) (State rs1 m1) (State rs1' m1') ->
      Mem.top_is_new m1 ->
      Mem.alloc m1 0 (frame_size fi) = (m2, b) ->
      Mem.store Mptr m2 b ofs_ra rs1#RA = Some m4 ->
      Mem.record_stack_blocks m4 (make_singleton_frame_adt' b  fi (frame_size fi)) = Some m5 ->
      0 <= ofs_ra <= Ptrofs.max_unsigned ->
      0 < frame_size fi ->
      let curofs := current_offset (rs1' # RSP) in
      let newostack := offset_after_alloc curofs fi in
      let rs2 := nextinstr ( rs1 #RAX <- (rs1#RSP)  #RSP <- (Vptr b Ptrofs.zero)) in
      let rs2' := nextinstr (rs1' #RAX <- (rs1'#RSP) #RSP <- (Vptr bstack (Ptrofs.repr newostack))) in
      exists j',
        (forall bb, j' bb = if peq bb b then Some (bstack, newostack) else j bb) 
        /\ inject_incr j j'
        /\
        exists m4',
          Mem.storev Mptr m1' (Val.offset_ptr (Vptr bstack (Ptrofs.repr newostack)) (Ptrofs.repr ofs_ra)) rs1'#RA = Some m4'
          /\ match_states j' newostack (State rs2 m5) (State rs2' m4').
  Proof.
    intros j ostack m1 rs1 rs1' fi b m1' m5 ofs_ra m2 m4
           MS TIN ALLOC STORE RSB REPRretaddr sizepos
           curofs newostack rs2 rs2'.
    inv MS.
    assert (RSPDEC: curofs = Ptrofs.unsigned ostack0).
    {
      unfold curofs. rewrite RSPEQ. simpl. auto.
    }
    assert (REPRcur: align (Z.max 0 (frame_size fi)) 8 <= curofs <= Ptrofs.max_unsigned).
    {
      split. rewrite RSPDEC.
      red in AGSP. specialize (AGSP _ RSPEQ). rewrite AGSP.
      generalize (Mem.size_stack_below m5).
      repeat rewrite_stack_blocks. revert EQ1; repeat rewrite_stack_blocks. inv TIN. intro A; inv A.
      simpl. rewrite size_frames_cons.
      change (size_frames nil) with 0. rewrite Z.max_l. simpl. omega.
      generalize (align_le (Z.max 0 (frame_size fi)) 8) (Z.le_max_l 0 (frame_size fi)). simpl. omega.
      rewrite RSPDEC. apply Ptrofs.unsigned_range_2.
    }
    assert (REPR: 0 <= newostack <= Ptrofs.max_unsigned).
    {
      unfold newostack.
      unfold offset_after_alloc.
      generalize (align_le (Z.max 0 (frame_size fi)) 8) (Z.le_max_l 0 (frame_size fi)).
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
      unfold newostack, offset_after_alloc.
      eapply Z.lt_le_trans with curofs.
      generalize (align_le (Z.max 0 (frame_size fi)) 8) (Z.le_max_l 0 (frame_size fi)).
      rewrite Z.max_r by omega. omega.
      rewrite RSPDEC. erewrite (AGSP _ RSPEQ); eauto.
      generalize (size_stack_pos (Mem.stack_adt m1)); intros. omega.
      simpl in H0. auto.
    }
    trim A.
    {
      red.
      intros.
      unfold newostack, offset_after_alloc.
      eapply Zdivides_trans with 8.
      destruct chunk; try (exists 8; reflexivity);
        try (exists 4; reflexivity);
        try (exists 2; reflexivity);
        try (exists 1; reflexivity).
      apply Z.divide_sub_r.
      rewrite RSPDEC. apply SPAL; auto.
      apply align_divides. omega.
    }
    trim A.
    {
      intros b0 delta' ofs k p JB PERM RNG.
      generalize (NIB _ _ _ _ _ JB PERM).
      generalize (align_le (frame_size fi) 8).
      unfold newostack, offset_after_alloc in RNG.
      rewrite Z.max_r in RNG by omega. simpl in RNG. omega.
    }
    trim A.
    {
      revert NS. unfold no_stack. intros (fr & fi0 & EQS & BLOCKS & ZERO & PUBLIC & SIZE). rewrite EQS.
      simpl. intros fi1 [[|[]]|[]]; subst. revert H. unfold in_frame'. rewrite <- BLOCKS.
      intros [|[]]. inv H.
      intros; apply PUBLIC.
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
    unfold Ptrofs.add.
    rewrite (Ptrofs.unsigned_repr _ REPR).
    rewrite (Ptrofs.unsigned_repr _ REPRretaddr) in *.
    rewrite Ptrofs.unsigned_repr. rewrite Z.add_comm. rewrite STORE'.
    eexists; split; eauto.
    (* record the stack block *)
    destruct NS as (frstack & fstack & EQstk & BLOCKS & ZERO & PUB & SZ).
    exploit Mem.record_stack_block_inject_left_zero. apply MINJ3. 6: eauto.
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
      intros b2 delta A; inv A.
      rewrite <- BLOCKS. simpl.
      eexists; split. eauto.
      constructor.
      intros; eapply stack_perm_le_public. intros; apply PUB.
      intros; rewrite SZ.
      unfold newostack, offset_after_alloc.
      rewrite RSPDEC. 
      red in AGSP. apply AGSP in RSPEQ.  rewrite RSPEQ.
        cut (o - size_stack (Mem.stack_adt m1) - align (Z.max 0 (frame_size fi)) 8 < 0). omega.
        generalize (size_stack_pos (Mem.stack_adt m1)).
        cut (o - align (Z.max 0 (frame_size fi)) 8 < 0). omega.
        cut (o < align (Z.max 0 (frame_size fi)) 8). omega.
        eapply Z.lt_le_trans.
        2: apply align_le. 2: omega. rewrite Z.max_r. omega. omega.
    }
    {
      red. unfold in_frame. simpl. exists b, 0, Cur, Writable.
      split. congruence.
      split. auto. split.
      repeat rewrite_perms. rewrite peq_true. omega.
      constructor.
    }
    {
      repeat rewrite_stack_blocks. rewrite EQstk. constructor; auto.
    } 
    simpl; auto.
    inv TIN. reflexivity.
    intro MINJ4.
    (* proving the final match_states *)
    rewrite <- (Ptrofs.unsigned_repr newostack) by omega.
    econstructor; eauto.
    - eapply Mem.mem_inject_ext. eauto. simpl; intros.
      repeat rewrite_stack_blocks. simpl.
      revert EQ0; repeat rewrite_stack_blocks. intro. rewrite EQ0. simpl. auto.
    - unfold rs2. rewrite nextinstr_rsp, Pregmap.gss. eauto.
    - intros r.
      unfold rs2, rs2'.
      apply val_inject_nextinstr. intros.
      apply val_inject_set; eauto. intro. apply val_inject_set. intros; eauto.
      eapply val_inject_incr; eauto.
      econstructor; eauto. rewrite Ptrofs.add_zero_l; auto.
    - red. rewnb. eauto.
    - red. unfold rs2'. rewrite nextinstr_rsp. rewrite Pregmap.gss. inversion 1. subst.
      repeat rewrite_stack_blocks.
      rewrite Ptrofs.unsigned_repr by auto.
      unfold newostack, offset_after_alloc in *.
      rewrite RSPDEC. rewrite (AGSP _ RSPEQ).
      revert EQ0; repeat rewrite_stack_blocks.
      inv TIN. inversion 1; subst.
      simpl. rewrite size_frames_cons.
      change (size_frames nil ) with 0. 
      rewrite (Z.max_l _ 0). simpl. omega. simpl.
      eapply Z.le_trans.
      2: apply align_le. 2: omega. apply Z.le_max_l.
    - red. intros ostack1 A. unfold rs2' in A. rewrite nextinstr_rsp in A. rewrite Pregmap.gss in A.
      inversion A. subst.
      rewrite Ptrofs.unsigned_repr by omega.
      unfold newostack.
      apply Z.divide_sub_r. rewrite RSPDEC. apply SPAL. auto.
      apply align_divides. omega.
    - red. intros ofs k p PERM.
      repeat rewrite_perms_bw PERM. eauto.
    - red; intros.
      repeat rewrite_perms_fw. eauto.
    - red. repeat rewrite_stack_blocks. exists frstack, fstack; rewrite EQstk, <- BLOCKS, <- ZERO. eauto.
    (* - unfold rs2'. rewrite nextinstr_rsp, Pregmap.gss. inversion 1. eauto. *)
    - rewrite Ptrofs.unsigned_repr by omega.
      red. intros b0 delta o k p JB PERM.
      repeat rewrite_perms_bw PERM.
      destruct peq.
      * subst. rewrite EQ1 in JB. inv JB. split. omega.
        rewrite_stack_blocks. rewrite in_stack_cons. rewrite in_frames_cons.
        revert EQ0. repeat rewrite_stack_blocks.
        inv TIN. inversion 1; subst.
        left. left; unfold in_frame; simpl; auto.
      * split. unfold newostack, offset_after_alloc.
        transitivity curofs.
        -- generalize (Z.le_max_l 0 (frame_size fi)); intro MAX.
           generalize (align_le (Z.max 0 (frame_size fi)) 8). omega.
        -- rewrite RSPDEC.
          rewrite EQ2 in JB; auto. 
          exploit NIB; eauto. tauto.
        -- repeat rewrite_stack_blocks.
           revert EQ0; repeat rewrite_stack_blocks. intro EQ0.
           rewrite in_stack_cons.
           right.
           edestruct NIB; eauto. rewrite <- EQ2; eauto.
           rewrite EQ0 in H0. rewrite in_stack_cons in H0. destruct H0; auto.
           exfalso.
           inv TIN. rewrite EQ0 in H2; inv H2. easy.
    - repeat rewrite_stack_blocks.
      revert EQ0; repeat rewrite_stack_blocks. inv TIN. inversion 1; subst.
      econstructor; eauto.
      + eapply inject_stack_incr; eauto.
        rewrite <- H in IS. inv IS.
        eapply inject_stack_more_perm. 2: eauto.
        intros.
        repeat rewrite_perms.
        exploit Mem.perm_valid_block; eauto. intro VB'.
        generalize (Mem.fresh_block_alloc _ _ _ _ _ ALLOC). destr.
      + rewrite EQ1. f_equal. f_equal.
        unfold newostack, offset_after_alloc.
        rewrite RSPDEC.
        instantiate (1:=fi).
        rewrite AGSP. rewrite <- H. simpl. change (size_frames nil) with 0. omega. auto.
      + reflexivity.
      + simpl. rewrite Z.max_r; auto. omega.
      + intros.
        repeat rewrite_perms. destr.
    - intros b0 fi0 delta INSTK FB0 b' o delta' k p FB1 P1.
      revert INSTK. repeat rewrite_stack_blocks. intro INSTK.
      revert EQ0; repeat rewrite_stack_blocks. inv TIN. inversion 1; subst. clear EQ0.
      simpl in INSTK.
      repeat rewrite_perms_bw P1.
      destruct INSTK as [[IFR|[]]|INSTK].
      + destruct IFR as [EQ|[]]. inv EQ. rewrite FB0 in EQ1; inv EQ1.
        destr_in P1.
        * subst. rewrite FB0 in FB1; inv FB1.
          rewrite Z.max_r by omega.  omega.
        * rewrite EQ2 in FB1 by auto.
          eapply NIB in P1; eauto.
          destruct P1 as (LE & IN).
          unfold newostack, offset_after_alloc.
          rewrite RSPDEC.
          omega.
      + assert (b0 <> b). intro; subst.
        exploit Mem.stack_norepet. rewrite EQ3. intro ND; inv ND.
        eapply in_stack'_in_stack in INSTK; eauto. eapply H4 in INSTK; eauto.
        left. reflexivity.
        rewrite EQ2 in FB0 by auto.
        intro RNG.
        assert (0 < frame_size fi0).
        destruct (zlt 0 (frame_size fi0)); auto.
        rewrite Z.max_l in RNG by omega. change (align 0 8) with 0 in RNG. omega.
        rewrite Z.max_r in RNG by omega.
        rewrite RSPDEC in *.
        destr_in P1. 
        * subst. rewrite EQ1 in FB1; inv FB1.
          cut (newostack + (frame_size fi)  <= delta). omega.
          unfold newostack. rewrite RSPDEC.
          rewrite AGSP; auto.
          rewrite <- H in IS. inv IS.
          eapply in_stack_inj_below in INSTK; eauto.
          destruct INSTK as (l1 & l2 & EQADT & JB0). rewrite FB0 in JB0. inv JB0.
          rewrite Z.max_r in * by omega.
          unfold offset_after_alloc.
          rewrite Z.max_r by omega. rewrite <- H. simpl. 
          cut (StackADT.size_stack (Mem.stack_adt m1) >= StackADT.size_stack l2). rewrite <- H.
          generalize (align_le (frame_size fi) 8). simpl. omega.
          rewrite <- H.
          simpl. rewrite size_stack_app.
          generalize (size_stack_pos l1) (size_frames_pos nil); omega. 
        * eapply IP.  rewrite <- H. right. eauto. eauto.
          rewrite <- EQ2. apply FB1. auto. eauto.
          rewrite Z.max_r by omega. omega.
    (* - repeat rewrite_stack_blocks.  *)
    (*   econstructor; eauto. *)
    (*   + eapply perm_stack_inv. eauto. apply Mem.in_frames_valid. *)
    (*     split; intros. *)
    (*     * repeat rewrite_perms_bw H2. *)
    (*       destr_in H2. *)
    (*       subst. *)
    (*       eapply Mem.in_frames_valid in H0. *)
    (*       eapply Mem.fresh_block_alloc in H0. easy. *)
    (*       eauto. *)
    (*     * repeat rewrite_perms_fw. auto. *)
    (*   + split; intros. *)
    (*     * repeat rewrite_perms_bw H0. *)
    (*       rewrite pred_dec_true in H0; eauto. *)
    (*     * do 2 rewrite_perms_fw. eapply Mem.perm_implies. eapply Mem.perm_alloc_2. eauto. eauto. *)
    (*       constructor. *)
    (*   + inv PS. simpl. easy. *)
    (*     intros b' [A|A]. *)
    (*     * eapply Plt_Ple_trans. apply Mem.in_frames_valid. rewrite <- H0. left; auto.  *)
    (*       erewrite Mem.alloc_result. 2: eauto. xomega. *)
    (*     * eapply H4 in A; eauto. eapply Plt_trans. eauto. *)
    (*       eapply Plt_Ple_trans. apply Mem.in_frames_valid. rewrite <- H0. left. *)
    (*       red. rewrite H5. left; auto.  *)
    (*       erewrite Mem.alloc_result. 2: eauto. xomega. *)
    (*   + reflexivity. *)
    - destruct GLOBSYMB_INJ; split.
      + intros. eapply INCR. eauto.
      + intros. destruct (peq b1 b).
        subst; rewrite EQ1 in H2. inv H2.
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
      inv TIN. inversion 1; subst.
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

  (* Lemma inject_stack_all_below: *)
  (*   forall l m, *)
  (*     perm_stack l m -> *)
  (*     forall b b' d, *)
  (*       in_frames ((hd d l)) b -> *)
  (*       in_stack (tl l) b' -> *)
  (*       Plt b' b. *)
  (* Proof. *)
  (*   induction 1; simpl; intros. easy. *)
  (*   rewrite in_frames_cons in H3. *)
  (*   destruct H3. unfold in_frame, get_frame_blocks in H3; rewrite H2 in H3. *)
  (*   simpl in H3. destruct H3 as [|[]]. *)
  (*   subst. eauto. *)
    
  (*   simpl in *; subst. eauto. *)
  (* Qed. *)

  (* Lemma inject_stack_only_once: *)
  (*   forall l m a b, *)
  (*     perm_stack (a::l) m -> *)
  (*     in_frames a b -> *)
  (*     get_assoc_stack l b = None. *)
  (* Proof. *)
  (*   inversion 1; subst. *)
  (*   rewrite in_frames_cons. *)
  (*   unfold in_frame, get_frame_blocks. rewrite H6. simpl. intros [[|[]]|]; subst. *)
  (*   rewrite not_in_stack_get_assoc; auto. *)
  (*   intro INF. *)
  (*   apply H4 in INF. xomega. *)
    
  (* Qed. *)

  (* Lemma inject_stack_norepeat: *)
  (*   forall l m a b, *)
  (*     perm_stack (a::l) m -> *)
  (*     in_frame (a) b -> *)
  (*     ~ in_frames l b. *)
  (* Proof. *)
  (*   inversion 1; subst. *)
  (*   unfold in_frame. rewrite H6. simpl. intros [?|[]]. *)
  (*   subst. intro INF; apply H4 in INF.  xomega.  *)
  (* Qed. *)

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
    unfold init_sp. exists (Ptrofs.repr x).
    econstructor; eauto. rewrite Ptrofs.add_zero_l. auto.
  Qed.

  Ltac use_ains :=
    repeat match goal with
           | AINS: asm_instr_no_stack ?i,
                   UNC: stack_invar ?i = true,
                        EI: Asm.exec_instr ?isp _ _ ?i _ ?m1 = Next _ ?m2 |-
             context [Mem.stack_adt ?m2] =>
             let AINS_stack := fresh "AINS_stack" in
             edestruct (AINS UNC _ _ _ _ _ _ _ _ _ EI) as (AINS_stack & _); rewrite ! AINS_stack;
             clear AINS_stack
           | AINS: asm_instr_no_stack ?i,
                   UNC: stack_invar ?i = true,
                        EI: Asm.exec_instr ?isp _ _ ?i _ ?m1 = Next _ ?m2,
                            H: context [Mem.stack_adt ?m2] |- _ =>
             let AINS_stack := fresh "AINS_stack" in
             edestruct (AINS UNC _ _ _ _ _ _ _ _ _ EI) as (AINS_stack & _); rewrite ! AINS_stack in H;
             clear AINS_stack

           | AINS: asm_instr_no_stack ?i,
                   UNC: stack_invar ?i = true,
                        EI: Asm.exec_instr _ _ _ ?i _ ?m1 = Next _ ?m2 |-
             context [Mem.perm ?m2 _ _ _ _] =>
             let AINS_perm := fresh "AINS_perm" in
             edestruct (AINS UNC _ _ _ _ _ _ _ _ _ EI) as (_ & AINS_perm); rewrite ! AINS_perm;
             clear AINS_perm
           | AINS: asm_instr_no_stack ?i,
                   UNC: stack_invar ?i = true,
                        EI: Asm.exec_instr _ _ _ ?i _ ?m1 = Next _ ?m2,
                            H : context [Mem.perm ?m2 _ _ _ _] |- _ =>
             let AINS_perm := fresh "AINS_perm" in
             edestruct (AINS UNC _ _ _ _ _ _ _ _ _ EI) as (_ & AINS_perm); rewrite ! AINS_perm in H;
             clear AINS_perm
           | AINR: asm_instr_no_rsp ?i,
                   UNC: stack_invar ?i = true,
                        EI: Asm.exec_instr ?isp _ _ ?i ?rs1 _ = Next ?rs2 _ |-
             context [?rs2 (IR RSP)] =>
             rewrite (AINR UNC _ _ _ _ _ _ _ _ _ EI)
           | AINR: asm_instr_no_rsp ?i,
                   UNC: stack_invar ?i = true,
                        EI: Asm.exec_instr ?isp _ _ ?i ?rs1 _ = Next ?rs2 _,
                            H: context [?rs2 (IR RSP)] |- _ =>
             rewrite (AINR UNC _ _ _ _ _ _ _ _ _ EI) in H
                                                          
           end.

  Lemma is_unchanged_stack_invar:
    forall i,
      is_unchanged i = true ->
      stack_invar i = true.
  Proof.
    destruct i eqn:?; simpl; try congruence.
  Qed.

  (* Lemma agree_sp_source_change_rs: *)
  (*   forall (rs1 rs2: regset) (EQ: rs1 # RSP = rs2 # RSP) s, *)
  (*     agree_sp_source rs1 s -> *)
  (*     agree_sp_source rs2 s. *)
  (* Proof. *)
  (*   induction s; simpl; rewrite EQ; auto. destr. *)
  (* Qed. *)
  
  Lemma exec_instr_inject':
    forall j ostack m1 m2 rs1 rs2 f i rs1' m1'
      (MS: match_states j ostack (State rs1 m1) (State rs2 m2))
      (AINR: asm_instr_no_rsp i)
      (AINS: asm_instr_no_stack i)
      (EI: Asm.exec_instr init_sp ge f i rs1 m1 = Next rs1' m1'),
      exists j' ostack' rs2' m2',
        exec_instr ge f i rs2 m2 = Next rs2' m2'
        /\ match_states j' ostack' (State rs1' m1') (State rs2' m2')
        /\ inject_incr j j'.
  Proof.
    intros. 
    destruct (is_unchanged i) eqn:ISUNCH.
    - edestruct init_sp_inj as (oinit & INJinit); eauto.
        inv MS; eauto.
        inv MS; eapply in_stack'_in_stack; eauto.
      edestruct exec_instr_inject as (rs2' & m2' & EXEC' & MINJ' & RINJ'); eauto.
        inv MS; eauto.
        inv MS; eauto.
      exists j, ostack, rs2', m2'; split; [|split]; eauto.
      destruct i; simpl in *; eauto; try congruence.
      generalize (is_unchanged_stack_invar _ ISUNCH) as SINVAR. intro.
      inv MS; econstructor; eauto; try now ((intros; use_ains; eauto) || (red; intros; use_ains; eauto)).
      + eapply asmgen_nextblock_forward in EXEC'.
        red in VB |- *. xomega.
      + use_ains. 
        eapply perm_stack_inv. eauto.
        intros; use_ains. tauto.
      + etransitivity. apply GlobLe.
        eapply asmgen_nextblock_forward; eauto.
      + etransitivity. apply GlobLeT.
        eapply asmgen_nextblock_forward; eauto.

    - destruct i; simpl in *; try congruence.
      + (* call_s *)
        inv EI. inv MS. do 4 eexists. split. eauto. split. econstructor; eauto.
        * eapply Mem.mem_inject_ext.
          eapply Mem.inject_push_new_stage_left. eauto. destruct NS as (fr & fi & EQ & ?). rewrite EQ. congruence.
          unfold upstar. rewrite_stack_blocks. simpl. intros; repeat destr; try omega.
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
        * eapply Mem.mem_inject_ext.
          eapply Mem.inject_push_new_stage_left. eauto. destruct NS as (fr & fi & EQ & ?). rewrite EQ. congruence.
          unfold upstar. rewrite_stack_blocks. simpl. intros; repeat destr; try omega.
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
        repeat destr_in EI.
        eexists j,ostack, _, _; split; eauto. split; auto.
        inv MS; constructor; auto.
        * eapply Mem.mem_inject_ext.
          eapply Mem.unrecord_stack_block_inject_left_zero. 2: eauto. eauto.
          simpl. intros. destr_in H.
          inv t. easy. simpl.
          inv t. rewrite <- H in IS. inv IS. simpl. inv IPS_REC; simpl; auto. rewrite <- H in SPinstack.
          simpl in SPinstack. destruct SPinstack as [[]|[]].
          simpl. repeat rewrite_stack_blocks. rewrite EQ. simpl.
          intros; repeat destr; try omega.
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
       repeat destr_in EI.
       inversion MS; subst.
       edestruct alloc_inject as (j' & JSPEC & INCR & m4' & STORE2 & MS') ; eauto.
       apply Ptrofs.unsigned_range_2.
       simpl in *.
       rewrite Ptrofs.repr_unsigned in STORE2. rewrite STORE2.
       set (newostack := offset_after_alloc (current_offset (rs2 RSP)) frame).
       fold newostack in STORE2, JSPEC, MS'.
       exists j',  newostack; eexists; eexists; split; eauto.
     + (* freeframe *)
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
       set (newostack := Ptrofs.unsigned ostack0 + align (Z.max 0 (frame_adt_size f0)) 8).

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
       simpl. destr. inv IS. simpl in SPinstack.
       destruct SPinstack as [[SPinstack|[]] | SPinstack].
       red in SPinstack. rewrite BLOCKS in SPinstack. destruct SPinstack as [H|[]]; inv H.
       destruct s; simpl in n; try omega. inv IPS_REC.
       revert Heqb1. repeat rewrite_stack_blocks. destruct in_stack_dec; simpl; try congruence.
       rewrite in_stack_cons in i. destruct i. easy. rewrite Heqs in H. simpl in H. easy.
       inv IPS_REC; simpl in *; try omega; try easy.
       {
         erewrite Mem.free_stack_blocks; eauto. rewrite Heqs. inv IS.
         unfold is_stack_top. simpl. unfold get_frames_blocks. simpl. setoid_rewrite in_app.
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
       {
         destruct NS as (f0' & fr & EQ & ?). simpl. rewrite EQ. congruence.
       }
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
       (* generalize (Mem.unrecord_stack_adt _ _ UNRECORD). *)
       (* erewrite Mem.free_stack_blocks. 2: eauto. rewrite Heql. intros (bb0 & EQ). *)
       (* inv EQ. *)
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
         rewrite size_frames_cons.
         change (size_frames nil) with 0. rewrite Z.max_l. rewrite Z.max_r. intros; omega.
         apply frame_adt_size_pos.
         etransitivity. 2: apply align_le. apply frame_adt_size_pos. omega.
       }
       rewrite <- (Ptrofs.unsigned_repr newostack) by omega.
       econstructor; eauto.
       * eapply Mem.mem_inject_ext. eauto.
         simpl. intros. repeat rewrite_stack_blocks. rewrite Heqs. simpl. auto.
       * rewrite nextinstr_rsp. rewrite Pregmap.gso by congruence.
         rewrite Pregmap.gss.
         revert ISDEF.
         unfold parent_pointer. unfold init_sp. repeat destr; inversion 1; eauto.
       * intros; apply val_inject_nextinstr.
         intros; apply val_inject_set; auto.
         intros; apply val_inject_set; auto.
         assert (v0 = parent_pointer init_sp m1).
         revert ISDEF. unfold is_def. destr. subst. unfold parent_pointer. rewrite Heqs.
         inv IPS_REC.
         -- simpl in SPinstack. destruct SPinstack as [[A|[]]|[]].
            red in A. unfold get_frame_blocks in A.
            rewrite BLOCKS in A. simpl in A.
            destruct A as [A|[]]; inv A.
            econstructor. eauto.
            unfold offset_after_free. rewrite Ptrofs.add_zero_l.
            f_equal. setoid_rewrite Ptrofs.unsigned_repr. simpl.
            rewrite SIZE. simpl. change (align (Z.max 0 0) 8) with 0. omega.
            simpl. change (align (Z.max 0 0) 8) with 0.
            generalize (Mem.stack_limit_range); omega.
         -- revert ISDEF. unfold parent_pointer at 1. rewrite Heqs. inversion 1.
         -- rewrite BLOCKS0.
            econstructor. eauto.
            unfold offset_after_free. rewrite Ptrofs.add_zero_l.
            f_equal. setoid_rewrite Ptrofs.unsigned_repr. simpl.
            rewrite size_frames_cons.
            change (size_frames nil) with 0. rewrite SIZE0.
            rewrite SIZE. rewrite Z.max_comm.
            Lemma max_align:
              forall x, 0 <= x ->
                   Z.max 0 (align x 8) = align (Z.max 0 x) 8.
            Proof.
              intros.
              rewrite ! Z.max_r; auto.
              etransitivity. 2: apply align_le. auto. omega.
            Qed.

            rewrite max_align. omega.
            rewrite <- SIZE0; apply frame_adt_size_pos.

            generalize (Mem.size_stack_below m1). rewrite Heqs. simpl.
            replace (size_frames (f0 :: nil)) with (align (Z.max 0 (frame_size fi)) 8). split. omega.
            generalize (size_stack_pos l)
                       (size_frames_pos (fr :: nil)).
            rewrite <- max_align.
            generalize (Z.le_max_l 0 (align (frame_size fi) 8)).
            generalize (Mem.stack_limit_range). omega.
            rewrite <- SIZE; apply frame_adt_size_pos.
            rewrite size_frames_cons.
            rewrite <- max_align. rewrite Z.max_comm. f_equal. rewrite SIZE. reflexivity.
            rewrite <- SIZE; apply frame_adt_size_pos.
         
       * red. rewrite nextinstr_rsp.
         rewrite ! Pregmap.gso by congruence.
         rewrite Pregmap.gss. intros; subst.
         inv H0. repeat rewrite_stack_blocks. rewrite AGSP. rewrite Heqs. simpl.
         cut (size_frames (f0 :: nil) = align (Z.max 0 (frame_adt_size f0)) 8). intro.
         unfold offset_after_free.
         rewrite Ptrofs.unsigned_repr. rewrite H0. change (size_frames nil) with 0. omega.
         rewrite <- H0. generalize (size_frames_pos (f0::nil)).
         generalize (Mem.size_stack_below m1). rewrite Heqs. simpl.
         generalize (size_stack_pos s). intros.
         cut (0 <= Mem.stack_limit - size_stack s <= Ptrofs.max_unsigned). omega.
         split. omega. generalize Mem.stack_limit_range. omega.
         rewrite size_frames_cons. rewrite <- max_align, Z.max_comm.  reflexivity.
         apply frame_adt_size_pos.
       * (* unfold parent_pointer. rewrite Heql. *)
       (*   inv PS.  *)
       (*   rewrite nextinstr_rsp. rewrite Pregmap.gso by congruence. *)
       (*   inv H4; auto. *)
       (*   rewrite H10. auto. *)
       (* * inv SZpos.  auto. *)
         (* *  *)
         red. rewrite nextinstr_rsp.
         rewrite ! Pregmap.gso by congruence.
         rewrite Pregmap.gss. inversion 1. subst. clear H0.
         (* inv LRSP. rewrite <- H4 in *. destr_in Heqb0; inv INJ3. *)
         (* rewrite <- H4 in *. inv INJ3. *)
         unfold offset_after_free.
         rewrite Ptrofs.unsigned_repr_eq. rewrite AGSP.

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
       (* *  *)
         (* * red. *)
         (*   intros ofs k p PERM. *)
         (*   eapply Mem.unrecord_stack_block_perm in PERM. 2: eauto. eauto. *)
         (* * red. *)
         (*   intros ofs k RNG. *)
         (*   eapply Mem.unrecord_stack_block_perm'. 2: eauto. eauto.                  *)
         (* * red. *)
         (*   edestruct Mem.unrecord_stack_adt. apply USB. red in NS. rewrite H0 in NS. *)
         (*   inv NS; auto. *)
         (* *  *)
         (* rewrite nextinstr_rsp. *)
         (* rewrite ! Pregmap.gso by congruence. *)
         (* rewrite Pregmap.gss.  *)
         (* inversion 1. subst. clear H0. split; auto. *)
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
            destruct (zle (Ptrofs.unsigned (Ptrofs.repr (Mem.stack_limit - size_stack s - align (Z.max 0 (frame_size fi)) 8)) + align (Z.max 0 (frame_size fi)) 8) (o + delta0)); auto.
            exfalso.
            apply Z.gt_lt in g.

            rewrite AGSP in LE, g.
            
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
              apply Z.ge_le in g0.
              rewrite Z.max_l in g by omega.
              change (align 0 8) with 0 in g. omega.
            }
            (* generalize (fun pf => Mem.address_inject _ _ _ _ _ Ptrofs.zero _ _ Freeable MINJ (FP _ pf) JB). *)
            (* rewrite Ptrofs.unsigned_zero. rewrite Ptrofs.add_zero_l.  simpl. *)
            (* intro UR. trim UR. omega. *)
            revert LE g. rewrite Heqs.

            Lemma size_frames_one:
              forall f,
                size_frames (f :: nil) = align (frame_adt_size f) 8.
            Proof.
              intros. rewrite size_frames_cons.
              change (size_frames nil) with 0.
              apply Z.max_l. etransitivity.
              2: apply align_le.
              apply frame_adt_size_pos. omega.
            Qed.
            simpl. rewrite size_frames_one.
            rewrite SIZE. rewrite Z.max_r by omega. rewrite Z.sub_add_distr. intros.
            rewrite (Z.max_r 0 (frame_size fi)) in * by omega.
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
               rewrite Heqs. left. left. red; rewrite BLOCKS. left; reflexivity. rewrite Z.max_r by omega. omega.
       * repeat rewrite_stack_blocks. rewrite Heqs. simpl. constructor.
         eapply perm_stack_inv. eauto.
         intros. repeat rewrite_perms. destr.
         repeat rewrite andb_true_iff in Heqb0. destruct Heqb0 as ((A & B) & C).
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
         destruct H0 as [IFR|[]].
         exploit Mem.stack_norepet. rewrite Heqs. intro ND; exfalso; inv ND.
         destruct (in_stack_dec (Mem.stack_adt m1') binit_sp); simpl in *; try congruence.
         revert i. repeat rewrite_stack_blocks. rewrite Heqs; simpl. revert H3 IFR. clear.
         intros.
         apply (H3 binit_sp).
         rewrite in_frames_cons; left; eapply in_frame'_in_frame; eauto.
         rewrite in_stack_cons in i; destruct i; auto; easy.
     + unfold check_top_frame in EI.
       destruct (Mem.stack_adt m1) eqn:S1; try congruence.
       repeat destr_in EI.
       repeat destr_in Heqb.
       apply andb_true_iff in H0; destruct H0 as (A & B).
       apply ZEQ in B. subst.
       destruct Forall_dec; simpl in A; try congruence. clear A.
       exists j, ostack; eexists; eexists; split. eauto.
       split; auto.
       inversion MS; subst; constructor; eauto.
       * rewrite nextinstr_rsp.
         destruct (preg_eq RSP rd).
         rewrite e. rewrite Pregmap.gss. congruence.
         rewrite Pregmap.gso. eauto. auto.
       * intros; apply val_inject_nextinstr.
         intros; apply val_inject_set; auto. rewrite S1 in *.
         inv IS. unfold parent_pointer. rewrite S1.
         repeat destr; auto.
         -- rewrite BLOCKS in f1. inv f1. red in H2. simpl in H2. destruct H2. clear H0 H1 H3.
            simpl in SPinstack.
            destruct SPinstack as [[IFR|[]]|[]]. red in IFR. rewrite BLOCKS in IFR.
            destruct IFR as [EQ|[]]; inv EQ. simpl in *.
            econstructor. eauto. unfold offset_after_free.
            rewrite RSPEQ. simpl. rewrite Ptrofs.add_zero_l.
            erewrite AGSP; eauto. rewrite S1. simpl. rewrite size_frames_one.
            rewrite SIZE.
            rewrite Z.max_r by omega. change (align 0 8) with 0. f_equal; omega.
         -- subst. inv IPS_REC. rewrite BLOCKS0 in Heql0; inv Heql0.
            econstructor; eauto.
            rewrite Ptrofs.add_zero_l. f_equal.
            unfold current_offset.
            rewrite RSPEQ.
            rewrite AGSP. rewrite S1.
            unfold offset_after_free. simpl. rewrite ! size_frames_one.
            rewrite <- SIZE0.
            repeat rewrite Z.max_r by (apply frame_adt_size_pos). omega.
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
      Asm.step init_sp ge S1 t S2 ->
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
      destruct NS as (fr & fi & STK & O); rewrite STK; congruence.
      eauto.
      assert (j b = Some (b,0)) as JB.
      {
        eapply GLOBFUN_INJ. eauto.
      }
      generalize (RINJ PC); rewrite H. inversion 1; subst.
      rewrite JB in H10; inv H10.
      exploit Mem.unrecord_stack_block_inject_left. apply MemInj. eauto.
      unfold upstar. simpl. destruct (Mem.stack_adt m) eqn:STK. simpl in *; easy. simpl; left; reflexivity.
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
      + eapply Mem.mem_inject_ext. eauto.
        simpl; intros. unfold upstar. simpl.
        repeat rewrite_stack_blocks. simpl. reflexivity.
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
        destruct NS as (fr & fi & STK & BLK & ZERO & PUB).
        rewrite STK. rewrite in_stack_cons; left.
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
      destruct (Mem.stack_adt m) eqn:STK. simpl in *; easy. simpl. left. destruct s; try reflexivity. simpl.
      inv TIN. rewrite STK in H6; inv H6. simpl in SPinstack. clear - SPinstack; intuition.
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
      + eapply Mem.mem_inject_ext. eauto.
        simpl. repeat rewrite_stack_blocks. inv TIN. simpl. intros. repeat destr; omega.
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


  Inductive mono_initial_state {F V} (prog: program F V) (rs: regset) m: state -> Prop :=
  |mis_intro:
     forall m1 bstack m2 m3
       (MALLOC: Mem.alloc m 0 (Mem.stack_limit) = (m1,bstack))
       (MDROP: Mem.drop_perm m1 bstack 0 (Mem.stack_limit) Writable = Some m2)
       (MRSB: Mem.record_stack_blocks (Mem.push_new_stage m2) (make_singleton_frame_adt' bstack frame_info_mono 0) = Some m3),
       let ge := Genv.globalenv prog in
       let rs0 :=
           rs # PC <- (Genv.symbol_address ge prog.(prog_main) Ptrofs.zero)
              #RA <- Vnullptr
              #RSP <- (Vptr bstack (Ptrofs.repr Mem.stack_limit)) in
         mono_initial_state prog rs m (State rs0 m3).

  Lemma repr_stack_limit:
    Ptrofs.unsigned (Ptrofs.repr (Mem.stack_limit)) = Mem.stack_limit.
  Proof.
    apply Ptrofs.unsigned_repr.
    generalize (Mem.stack_limit_range); omega.
  Qed.
  
  Lemma match_initial_states s m0:
    Asm.initial_state prog s ->
    Genv.init_mem prog = Some m0 ->
    exists s' j ostack, match_states (Genv.genv_next ge) j ostack s s' /\
                   mono_initial_state prog (Pregmap.init Vundef) m0 s'.
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
        split; simpl; intros; omega.
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
    constructor; auto.
    - eapply Mem.mem_inject_ext. apply Mem.inject_push_new_stage_left. apply RSBINJ.
      repeat rewrite_stack_blocks. congruence.
      repeat rewrite_stack_blocks.
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
      + simpl. intros; omega.
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
    forall isp j o st1 st2 r,
      match_states isp j o st1 st2 -> Asm.final_state st1 r -> final_state st2 r.
  Proof.
    inversion 1; subst.
    inversion 1; subst.
    econstructor.
    generalize (RINJ PC). rewrite H3. unfold Vnullptr. destruct ptr64; inversion 1; auto.
    generalize (RINJ RAX). rewrite H5. unfold Vnullptr. destruct ptr64; inversion 1; auto.
  Qed.
>>>>>>> origin/newstackadt2

  Definition mono_semantics (p: Asm.program) rs m :=
    Semantics step (mono_initial_state p rs m) final_state (Genv.globalenv p).
  
<<<<<<< HEAD
=======
  Theorem transf_program_correct m:
    asm_prog_no_rsp ge ->
    Genv.init_mem prog = Some m ->
    forward_simulation (Asm.semantics (Vptr (Genv.genv_next ge) Ptrofs.zero) prog) (mono_semantics prog (Pregmap.init Vundef) m).
  Proof.
    intros APNR IM.
    eapply forward_simulation_step with (fun s1 s2 => exists j o, match_states (Genv.genv_next ge) j o s1 s2).
    - simpl. reflexivity. 
    - simpl. intros s1 IS; inversion IS. rewrite IM in H; inv H.
      exploit match_initial_states. eauto. eauto.
      intros (s' & j & ostack & MS & MIS); eexists; split; eauto.
    - simpl. intros s1 s2 r (j & o & MS) FS. eapply transf_final_states; eauto.
    - simpl. intros s1 t s1' STEP s2 (j & o & MS). 
      edestruct step_simulation as (isp' & j' & o' & STEP' & MS'); eauto.
  Qed.
>>>>>>> origin/newstackadt2
  Definition no_inject_below j m thr:=
    forall b delta o k p,
      j b = Some (bstack, delta) ->
      Mem.perm m b o k p ->
      thr <= o + delta /\ in_frames (Mem.stack_adt m) b.

  Definition agree_sp m1 rs2:=
    forall ostack,
      rs2 # RSP = Vptr bstack ostack ->
      Ptrofs.unsigned ostack = Mem.stack_limit - StackADT.size_stack (Mem.stack_adt m1).

  Definition perm_bstack m2:=
    forall (ofs : Z) (k : perm_kind) (p : permission),
       Mem.perm m2 bstack ofs k p -> 0 <= ofs < Ptrofs.max_unsigned /\  perm_order Writable p.

  Definition perm_bstack_stack_limit m2:=
    forall (ofs : Z) (k : perm_kind),
      0 <= ofs < Mem.stack_limit ->
      Mem.perm m2 bstack ofs k Writable.

  Definition sp_aligned rs2:=
    forall ostack,
      rs2 # RSP = Vptr bstack ostack ->
      (8 | Ptrofs.unsigned ostack).

  Definition no_stack m2 :=
    exists fi, Mem.stack_adt m2 = (bstack::nil, Some fi, 0)::nil /\ (forall o, frame_perm fi o = Public) /\ frame_size fi = Mem.stack_limit.

  Inductive inject_stack: meminj -> list (frame_adt) -> Prop :=
  | inject_stack_nil j :
      inject_stack j nil
  | inject_stack_cons j l b fi:
      inject_stack j l ->
      j b = Some (bstack, Mem.stack_limit - size_stack l - align (Z.max 0 (frame_size fi)) 8) ->
      inject_stack j ( (b::nil,Some fi,frame_size fi)::l).

  Variable init_sp: val.
  
  Inductive load_rsp: list (frame_adt) -> mem -> Prop :=
  | load_rsp_nil m:
      load_rsp nil m
  | load_rsp_one m b fi sz:
      Forall (fun fl => Mem.load Mptr m b (seg_ofs fl) = Some init_sp) (frame_link fi) ->
      load_rsp ((b::nil,Some fi,sz)::nil) m
  | load_rsp_cons m b fi sz b' fi' sz' l:
      Forall (fun fl => Mem.load Mptr m b (seg_ofs fl) = Some (Vptr b' Ptrofs.zero)) (frame_link fi) ->
      load_rsp ((b'::nil,Some fi', sz')::l) m ->
      Plt b' b ->
      load_rsp ((b::nil, Some fi,sz)::(b'::nil, Some fi', sz')::l) m.

  Inductive perm_stack: list (frame_adt) -> mem -> Prop :=
  | ps_nil m:
      perm_stack nil m
  | ps_cons l m b fi sz:
      perm_stack l m ->
      (forall o k p, Mem.perm m b o k p <-> 0 <= o < frame_size fi) ->
      perm_stack ((b::nil,Some fi, sz)::l) m.

  Definition inject_padding (j: meminj) (m: mem) : Prop :=
    forall b fi delta,
      get_frame_info (Mem.stack_adt m) b = Some fi ->
      j b = Some (bstack, delta) ->
      forall b' o delta' k p,
        j b' = Some (bstack, delta') ->
        Mem.perm m b' o k p ->
        ~ ( delta + Z.max 0 (frame_size fi) <= o + delta' < delta + align (Z.max 0 (frame_size fi)) 8).

  Inductive match_states: meminj -> Z -> state -> state -> Prop :=
  | match_states_intro:
      forall j (rs: regset) (m: mem) (rs': regset) m'
        (MINJ: Mem.inject j (fun n => if lt_dec n (length (Mem.stack_adt m)) then Some O else None) m m')
        (RSPzero: forall b o, rs # RSP = Vptr b o -> o = Ptrofs.zero )
        (RINJ: forall r, Val.inject j (rs # r) (rs' # r))
        (VB: Mem.valid_block m' bstack)
        (AGSP: agree_sp m rs')
        (AGSP1: match Mem.stack_adt m with
                  nil => rs # RSP = init_sp
                | (b::nil, Some fi,n)::r => rs # RSP = Vptr b Ptrofs.zero
                | _ => False
                end)
        (SZpos: Forall (fun f : frame_adt => 0 <= frame_adt_size f) (Mem.stack_adt m))
        (OneLink: Forall (fun f : frame_adt => option_map (fun f => length (frame_link f)) (frame_adt_info f) = Some 1%nat) (Mem.stack_adt m))
        (SPAL: sp_aligned rs')
        (PBS: perm_bstack m')
        (PBSL: perm_bstack_stack_limit m')
        (NS: no_stack m')
        ostack
        (RSPEQ: forall b o, rs' RSP = Vptr b o -> b = bstack /\ o = ostack)
        (NIB: no_inject_below j m (Ptrofs.unsigned ostack))
        (IS: inject_stack j (Mem.stack_adt m))
        (IP: inject_padding j m)
        (PS: perm_stack (Mem.stack_adt m) m)
        (LRSP: load_rsp (Mem.stack_adt m) m)
        (GLOBFUN_INJ: forall b f, Genv.find_funct_ptr ge b = Some f -> j b = Some (b,0))
        (GLOBDEF_INJ: forall b f, Genv.find_def ge b = Some f -> j b = Some (b,0))
        (GLOBSYMB_INJ: meminj_preserves_globals' ge j)
        (GlobLe: (Genv.genv_next ge <= Mem.nextblock m)%positive)
        (GlobLeT: (Genv.genv_next ge <= Mem.nextblock m')%positive)
      ,
        match_states j (Ptrofs.unsigned ostack) (State rs m) (State rs' m').

  Lemma inject_stack_incr:
    forall j j' (INCR: inject_incr j j')
      l (IS: inject_stack j l),
      inject_stack j' l.
  Proof.
    induction 2; constructor; eauto.
  Qed.
  
  Definition is_ptr v :=
    match v with
      Vptr _ _ => True
    | _ => False
    end.

  Lemma is_ptr_dec v: {is_ptr v} + {~ is_ptr v}.
  Proof.
    destruct v; simpl; auto.
  Qed.

  Lemma perm_stack_inv:
    forall l m (PS: perm_stack l m) m'
      (V: forall b, in_frames l b -> Mem.valid_block m b)
      (U: forall b o k p, in_frames l b -> Mem.perm m' b o k p <-> Mem.perm m b o k p),
      perm_stack l m'.
  Proof.
    induction 1; simpl; intros; constructor; auto.
    intros. 
    split; intros.
    - eapply U in H0; eauto.
      eapply H; eauto. unfold in_frame; simpl. eauto.
    - eapply U; eauto; unfold in_frame; simpl; eauto.
      apply H. auto.
  Qed.

  Axiom exec_instr_inject:
    forall j g m1 m2 rs1 rs2 f i rs1' m1'
      (MINJ: Mem.inject j g m1 m2)
      (RINJ: forall r, Val.inject j (rs1 # r) (rs2 # r))
      (IU: is_unchanged i = true)
      (EXEC: Asm.exec_instr ge f i rs1 m1 = Next rs1' m1'),
      exists rs2' m2',
        Asm.exec_instr ge f i rs2 m2 = Next rs2' m2'
        /\ Mem.inject j g m1' m2'
        /\ (forall r, Val.inject j (rs1' # r) (rs2' # r))
        (* /\ (forall b b' delta, j b = None -> j' b = Some (b', delta) -> Ple (Genv.genv_next ge) b /\ b' <> bstack) *). 
  (* should be proved already somewhere *)

  Lemma free_inject:
    forall j g m1 b lo hi m2 m3 m1',
      Mem.inject j g m1 m1' ->
      Mem.free m1 b lo hi = Some m2 ->
      (forall o k p, Mem.perm m1 b o k p -> lo <= o < hi) ->
      (forall b0, is_stack_top (Mem.stack_adt m2) b0 -> b0 = b) ->
      Mem.unrecord_stack_block m2 = Some m3 ->
      (* g 1%nat = Some O -> *)
      length (Mem.stack_adt m1') = 1%nat ->
      Mem.inject j (fun n => g (S n)) m3 m1'.
  Proof.
    intros j g m1 b lo hi m2 m3 m1' INJ FREE PERMRNG IST USB LST.
    eapply Mem.unrecord_stack_block_inject_left_zero.
    eapply Mem.free_left_inject. eauto. eauto. eauto.
    intros. eapply stack_inject_range in H. 2: eapply Mem.inject_stack_adt; eauto.
    rewrite LST in H. omega.
    intros.
    apply IST in H. subst. intros PERM.
    eapply Mem.perm_free in PERM. 2: eauto. destruct PERM. apply H. split; eauto.
  Qed.

  Hypothesis type_init_sp:
    Val.has_type init_sp Tptr.

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

  Definition link_offsets l b o :=
    match get_assoc l b with
      Some fi => in_segments o (frame_link fi)
    | _ => False
    end.
  
  Lemma get_assoc_app:
    forall l2 l1 b,
      (forall b, in_frames l2 b -> in_frames l1 b -> False) ->
      in_frames l1 b ->
      get_assoc (l2 ++ l1) b = get_assoc l1 b.
  Proof.
    induction l2; simpl; intros; auto.
    destruct a, p.
    destr. eapply H in H0; eauto. easy. 
    eapply IHl2; eauto.
  Qed.

  Lemma in_frames_app:
    forall l1 l2 b,
      in_frames (l1 ++ l2) b <->
      in_frames l1 b \/ in_frames l2 b.
  Proof.
    clear.
    induction l1; simpl; intros; eauto. tauto.
    destruct a, p.
    split; intros; destruct H; auto.
    apply IHl1 in H. destruct H; auto. rewrite IHl1.
    destruct H; auto.
    rewrite IHl1. auto.
  Qed.

  Lemma load_rsp_plt:
    forall l a m,
      load_rsp (a :: l) m ->
      forall b b',
        in_frame a b ->
        in_frames l b' ->
        Plt b' b.
  Proof.
    clear.
    induction l; simpl; intros; eauto. easy.
    destruct a0, p. destruct a, p.
    inv H.
    unfold in_frame in *. simpl in *.
    destruct H0; try easy; subst.
    destruct H1. destruct H; try easy; subst. auto.
    eapply IHl in H. 2: simpl; eauto. 2: simpl; left; auto. xomega.
  Qed.

  Lemma load_rsp_plt_app:
    forall l1 l2 m,
      load_rsp (l1 ++ l2) m ->
      forall b b',
        in_frames l1 b ->
        in_frames l2 b' ->
        Plt b' b.
  Proof.
    clear.
    induction l1; simpl; intros. easy.
    destruct a.
    destruct H0.
    eapply load_rsp_plt in H. 2: simpl; eauto. 2: rewrite in_frames_app. 2: right; eauto. auto.
    eapply IHl1; eauto. inv H; eauto.
    constructor.
  Qed.

  Lemma in_segment_in_segments:
    forall l x i,
      In x l ->
      in_segment i x ->
      in_segments i l.
  Proof.
    induction l; simpl; intros; eauto.
    destruct H; subst; eauto.
  Qed.

  Lemma load_rsp_inv:
    forall l m ,
      load_rsp l m ->
      forall m' l1 l2,
        l1 = l2 ++ l ->
        (forall b, in_frames l2 b -> in_frames l b -> False) ->
        Mem.unchanged_on (link_offsets l1) m m' ->
        load_rsp l m'.
  Proof.
    induction 1; simpl; intros m' l1 l2 EQ DISJ UNCH.
    - constructor.
    - constructor.
      rewrite Forall_forall; intros.
      eapply Mem.load_unchanged_on. eauto. unfold link_offsets.
      intros. rewrite EQ. rewrite get_assoc_app; auto. simpl.
      rewrite pred_dec_true; eauto. unfold in_segment. eapply in_segment_in_segments; eauto.
      red; simpl. generalize (frame_link_size fi); rewrite Forall_forall; intro F. rewrite F; auto.
      simpl; unfold in_frame; simpl; auto.
      revert x H0; rewrite <- Forall_forall. auto.
    - constructor.
      + rewrite Forall_forall. intros x IN.
        eapply Mem.load_unchanged_on; eauto.
        unfold link_offsets. erewrite EQ. rewrite get_assoc_app; auto. simpl. rewrite pred_dec_true; auto. 
        intros.
        generalize (frame_link_size fi); rewrite Forall_forall; intro F. erewrite <- F in H2; eauto.
        eapply in_segment_in_segments; eauto.
        simpl. unfold in_frame; simpl; auto.
        revert x IN; rewrite <- Forall_forall. auto.
      + eapply IHload_rsp; auto. 
        * instantiate (1 := l2 ++ (b::nil, Some fi,sz) :: nil). subst. simpl.
          intros. apply in_frames_app in H2. simpl in *.
          unfold in_frame in H2, H3. simpl in *. destruct H2.
          apply DISJ in H2. auto. auto.
          destruct H2; try congruence.
          destruct H2; try congruence. subst.
          destruct H3. destruct H2; try congruence. subst; xomega.
          eapply load_rsp_plt in H0. 2: red; simpl; eauto. 2: apply H2. xomega.
        * subst. rewrite app_ass. simpl. auto. 
      + auto.
  Qed.

  Lemma load_rsp_inv':
    forall l m m',
      load_rsp l m ->
      Mem.unchanged_on (link_offsets l) m m' ->
      load_rsp l m'.
  Proof.
    intros.
    eapply (load_rsp_inv l m H m' l nil). reflexivity. simpl; easy. auto.
  Qed.

  Lemma load_rsp_add:
    forall l m b frame,
      load_rsp l m ->
      Forall (fun fl =>
      Mem.load Mptr m b (seg_ofs fl) = Some (match l with
                                               nil => init_sp
                                             | (b'::nil,_,_)::r => Vptr b' Ptrofs.zero
                                             | _ => Vundef
                                             end)) (frame_link frame) ->
      (forall bs, in_frames l bs -> Plt bs b) ->
      load_rsp ((b::nil, Some frame, frame_size frame) :: l) m.
  Proof.
    induction 1; simpl; intros; repeat constructor; auto.
    unfold in_frame in H1. simpl in H1. eauto.
    unfold in_frame in H3. simpl in H3. eauto.
  Qed.

  Lemma exec_load_unchanged_on:
    forall rs1 m1 rs1' m1' p am chunk P sz,
      exec_load ge chunk m1 am rs1 p sz = Next rs1' m1' ->
      Mem.unchanged_on P m1 m1'.
  Proof.
    unfold exec_load.
    intros. destr_in H. inv H.
    apply Mem.unchanged_on_refl.
  Qed.

  Lemma goto_label_unchanged_on:
    forall rs1 m1 rs1' m1' f l P,
      goto_label ge f l rs1 m1 = Next rs1' m1' ->
      Mem.unchanged_on P m1 m1'.
  Proof.
    unfold goto_label.
    intros. repeat destr_in H. 
    apply Mem.unchanged_on_refl.
  Qed.

  Lemma in_segments_in_segment:
    forall i l,
      in_segments i l ->
      exists x,
        In x l /\ in_segment i x.
  Proof.
    induction l; simpl; intros; eauto.
    easy.
    destruct H.
    eexists; split; eauto.
    destruct IHl as (x & IN & INS); eauto.
  Qed.

  Lemma exec_store_unchanged_on:
    forall rs1 m1 rs1' m1' p am rl chunk sz,
      exec_store ge chunk m1 am rs1 p rl sz = Next rs1' m1' ->
      Mem.unchanged_on (link_offsets (Mem.stack_adt m1)) m1 m1'.
  Proof.
    unfold exec_store.
    intros rs1 m1 rs1' m1' p am rl chunk sz ES.
    destr_in ES. inv ES.
    unfold Mem.storev in Heqo. destr_in Heqo.
    eapply Mem.store_unchanged_on. eauto.
    eapply Mem.store_valid_access_3 in Heqo.
    destruct Heqo as (RP & AL & SA).
    trim SA. constructor.
    intros i0 RNG LO.
    red in LO. destr_in LO.
    destruct SA as [[IST NONLINK]|[NIST DATA]].
    - apply NONLINK in RNG.
      red in RNG.
      unfold get_frame_info in RNG. rewrite Heqo in RNG.
      apply RNG.
      generalize (frame_link_readonly f); rewrite Forall_forall; intro RO.
      edestruct in_segments_in_segment as (x & IN & INS); eauto.
      eapply RO; eauto.
    - red in DATA.
      unfold get_frame_info in DATA. rewrite Heqo in DATA.
      generalize (frame_link_readonly f); rewrite Forall_forall; intro RO.
      edestruct in_segments_in_segment as (x & IN & INS); eauto.
      eapply RO in INS; eauto.
      apply DATA in RNG. red in RNG. congruence.
  Qed.

  Lemma exec_instr_unchanged_on:
    forall f i rs1 m1 rs1' m1',
      is_unchanged i = true ->
      Asm.exec_instr ge f i rs1 m1 = Next rs1' m1' ->
      Mem.unchanged_on (fun b o => match get_frame_info (Mem.stack_adt m1) b with
                                  Some fi => in_segments o (frame_link fi)
                                | _ => False
                                end) m1 m1'.
  Proof.
    intros f i.
    assert (forall P, (forall x, P x) -> P i). intros. auto.
    destruct i as (i & info).
    destruct i; unfold Asm.exec_instr; simpl; intros rs1 m1 rs1' m1' IU EI;
      simpl in IU; try discriminate;
      repeat match goal with
               H: Next _ _ = Next _ _ |- _ => inv H
             | H: exec_load _ _ _ _ _ _ _ = _ |- _ => eapply exec_load_unchanged_on; eauto
             | H: exec_store _ _ _ _ _ _ _ _ = _ |- _ => eapply exec_store_unchanged_on; eauto
             | H: goto_label _ _ _ _ _ = _ |- _ => eapply goto_label_unchanged_on; eauto
             | |- Mem.unchanged_on _ ?m ?m => apply Mem.unchanged_on_refl
             | |- _ => repeat destr_in EI
             end.
  Qed.


  Lemma perm_stack_eq:
    forall l m b fi,
      perm_stack l m ->
      get_assoc l b = Some fi ->
      forall o k p,
        Mem.perm m b o k p <-> 0 <= o < frame_size fi.
  Proof.
    induction 1; simpl; intros; eauto. congruence.
    destruct (eq_block b0 b).
    - inv H1. eauto.
    - eauto.
  Qed.

  Lemma in_stack_inj_below:
    forall j l,
      inject_stack j l ->
      forall b fi,
        get_assoc l b = Some fi ->
        exists l1 l2,
          l = l1 ++ l2 /\
          j b = Some (bstack, Mem.stack_limit - StackADT.size_stack l2).
  Proof.
    induction 1; simpl; intros; eauto.
    congruence.
    destruct (eq_block).
    - subst.
      inv H1.
      rewrite H0.
      exists nil. 
      repeat eexists.
      f_equal. f_equal. simpl. omega. 
    - specialize (IHinject_stack _ _ H1).
      destruct IHinject_stack as (l1 & l2 & EQl & JB).
      subst.
      rewrite JB.
      repeat eexists.
      rewrite app_comm_cons. eauto.
  Qed.

  Lemma size_stack_app:
    forall l1 l2,
      StackADT.size_stack (l1 ++ l2) = StackADT.size_stack l1 + StackADT.size_stack l2.
  Proof.
    induction l1; simpl; intros; eauto.
    destruct a.
    rewrite IHl1. destruct p; omega.
  Qed.

  Ltac rewrite_perms_fw :=
    match goal with
    | H1: Mem.record_stack_blocks _ _ ?m |- Mem.perm ?m _ _ _ _ =>
      eapply (Mem.record_stack_block_perm' _ _ _ H1)
    | H1: Mem.alloc _ _ _ = (?m,_) |- Mem.perm ?m _ _ _ _ =>
      first [
          apply Mem.perm_implies; [apply (Mem.perm_alloc_2 _ _ _ _ _ H1) | try constructor]
        |  apply (Mem.perm_alloc_1 _ _ _ _ _ H1)
        ]
    | H1: Mem.store _ _ _ _ _ = Some ?m |- Mem.perm ?m _ _ _ _ =>
      apply (Mem.perm_store_1 _ _ _ _ _ _ H1)
    | H1: Mem.storev _ _ _ _ = Some ?m |- Mem.perm ?m _ _ _ _ =>
      apply (Mem.perm_store_1 _ _ _ _ _ _ H1)
    end.

  Ltac rewrite_stack_blocks :=
    match goal with
    | H: Mem.record_stack_blocks _ _  ?m |- context [Mem.stack_adt ?m] =>
      rewrite (Mem.record_stack_blocks_stack_adt _ _ _ H)
    | H: Mem.alloc _ _ _ = (?m,_) |- context [Mem.stack_adt ?m] =>
      rewrite (Mem.alloc_stack_blocks _ _ _ _ _ H)
    | H: Mem.store _ _ _ _ _ = Some ?m |- context [Mem.stack_adt ?m] =>
      rewrite (Mem.store_stack_blocks _ _ _ _ _ _ H)
    | H: Mem.storev _ _ _ _ = Some ?m |- context [Mem.stack_adt ?m] =>
      rewrite (Mem.store_stack_blocks _ _ _ _ _ _ H)
    end.

  Ltac rewrite_perms_bw H :=
    match type of H with
      Mem.perm ?m2 _ _ _ _ =>
      match goal with
      | H1: Mem.record_stack_blocks _ _  ?m |- _ =>
        apply (Mem.record_stack_block_perm _ _ _ H1) in H
      | H1: Mem.alloc _ _ _ = (?m,_) |- _ =>
        apply (Mem.perm_alloc_inv _ _ _ _ _ H1) in H
      | H1: Mem.store _ _ _ _ _ = Some ?m |- _ =>
        apply (Mem.perm_store_2 _ _ _ _ _ _ H1) in H
      | H1: Mem.storev _ _ _ _ = Some ?m |- _ =>
        apply (Mem.perm_store_2 _ _ _ _ _ _ H1) in H
      end
    end.

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
      Mem.record_stack_blocks m fi m' ->
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


  Lemma alloc_inject:
    forall j ostack m1 (rs1 rs1': regset) fi b m1' m2 m3 m4 m5 ofs_ra fl sz,
      (frame_link fi = fl::nil) ->
      match_states j (Ptrofs.unsigned ostack) (State rs1 m1) (State rs1' m1') ->
      Mem.alloc m1 0 (frame_size fi) = (m2, b) ->
      Mem.store Mptr m2 b (seg_ofs fl) rs1#RSP = Some m3 ->
      Mem.store Mptr m3 b ofs_ra rs1#RA = Some m4 ->
      Mem.record_stack_blocks m4 (b::nil, Some fi, frame_size fi) m5 ->
      0 <= seg_ofs fl <= Ptrofs.max_unsigned ->
      0 <= ofs_ra <= Ptrofs.max_unsigned ->
      0 <= frame_size fi ->
      (forall o, seg_ofs fl <= o < seg_ofs fl + size_chunk Mptr ->
            ofs_ra <= o < ofs_ra + size_chunk Mptr -> False) ->
      let curofs := current_offset (rs1' # RSP) in
      let newostack := offset_after_alloc curofs fi in
      let rs2 := nextinstr ( rs1 #RAX <- (rs1#RSP)  #RSP <- (Vptr b Ptrofs.zero)) sz in
      let rs2' := nextinstr (rs1' #RAX <- (rs1'#RSP) #RSP <- (Vptr bstack (Ptrofs.repr newostack))) sz in
      exists j',
        (forall bb, j' bb = if peq bb b then Some (bstack, newostack) else j bb) 
        /\ inject_incr j j'
        /\ exists m3',
            Mem.storev Mptr m1' (Val.offset_ptr (Vptr bstack (Ptrofs.repr newostack)) (Ptrofs.repr (seg_ofs fl))) rs1'#RSP = Some m3'
            /\
            exists m4',
              Mem.storev Mptr m3' (Val.offset_ptr (Vptr bstack (Ptrofs.repr newostack)) (Ptrofs.repr ofs_ra)) rs1'#RA = Some m4'
              /\ match_states j' newostack (State rs2 m5) (State rs2' m4').
  Proof.
    intros j ostack m1 rs1 rs1' fi b m1' m2 m3 m4 m5 ofs_ra fl sz INFL
           MS ALLOC STORE_PARENT STORE_RETADDR RSB REPRlink REPRretaddr sizepos
           DISJ curofs newostack rs2 rs2'.
    inv MS.
    assert (RSPDEC: (rs1' RSP = Vptr bstack ostack0 /\ curofs = Ptrofs.unsigned ostack0)
                    \/ (~ is_ptr (rs1' RSP) /\ curofs = Mem.stack_limit /\ Mem.stack_adt m1 = nil)).
    {
      destruct (is_ptr_dec (rs1' RSP)).
      left; destruct (rs1' RSP) eqn:?; simpl in *; try easy.
      specialize (RSPEQ _ _ eq_refl).
      intuition subst. auto. reflexivity.
      right. split; auto.
      split; auto.
      destruct (rs1' RSP) eqn:?; simpl in *; try easy.
      generalize (RINJ RSP).
      repeat destr_in AGSP1.
      rewrite H0. inversion 1. rewrite <- H4 in n. simpl in n; easy.
    }
    assert (REPRcur: align (Z.max 0 (frame_size fi)) 8 <= curofs <= Ptrofs.max_unsigned).
    {
      generalize (align_le (Z.max 0 (frame_size fi)) 8) (Z.le_max_l 0 (frame_size fi)).
      generalize (Mem.size_stack_below m5).
      erewrite Mem.record_stack_blocks_stack_adt. 2: eauto.
      simpl.
      erewrite Mem.store_stack_blocks. 2: simpl in *; eauto.
      erewrite Mem.store_stack_blocks. 2: simpl in *; eauto.
      erewrite Mem.alloc_stack_blocks. 2: eauto.
      destruct (RSPDEC) as [[EQRSP ?]|[NOPTR [EQ NIL]]]; subst.
      unfold curofs, current_offset. rewrite EQRSP. erewrite AGSP; eauto.
      generalize (size_stack_pos (Mem.stack_adt m1)); intros.
      generalize (Mem.stack_limit_range).
      omega.
      rewrite EQ, NIL. simpl.
      generalize (Mem.stack_limit_range).
      omega.
    }
    assert (REPR: 0 <= newostack <= Ptrofs.max_unsigned).
    {
      unfold newostack.
      unfold offset_after_alloc.
      generalize (align_le (Z.max 0 (frame_size fi)) 8) (Z.le_max_l 0 (frame_size fi)).
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
      unfold newostack, offset_after_alloc.
      eapply Z.lt_le_trans with curofs.
      generalize (align_le (Z.max 0 (frame_size fi)) 8) (Z.le_max_l 0 (frame_size fi)).
      rewrite Z.max_r by omega. omega.
      destruct (RSPDEC) as [[EQRSP ?]|[NOPTR [EQ NIL]]]; subst.
      rewrite H2. erewrite (AGSP _ EQRSP); eauto.
      generalize (size_stack_pos (Mem.stack_adt m1)); intros. omega. omega.
      simpl in H0.
      auto.
    }
    trim A.
    {
      red.
      intros.
      unfold newostack, offset_after_alloc.
      eapply Zdivides_trans with 8.
      destruct chunk; try (exists 8; reflexivity);
        try (exists 4; reflexivity);
        try (exists 2; reflexivity);
        try (exists 1; reflexivity).
      apply Z.divide_sub_r.
      destruct (RSPDEC) as [[EQRSP ?]|[NOPTR [EQ NIL]]]; subst.
      rewrite H0. apply SPAL; auto.
      rewrite EQ. apply Mem.stack_limit_aligned.
      apply align_divides. omega.
    }
    trim A.
    {
      intros b0 delta' ofs k p JB PERM RNG.
      generalize (NIB _ _ _ _ _ JB PERM).
      destruct (RSPDEC) as [[EQRSP ?]|[NOPTR [EQ NIL]]]; subst.
      rewrite EQRSP in RSPEQ. specialize (RSPEQ _ _ eq_refl). inv RSPEQ.
      generalize (align_le (frame_size fi) 8).
      unfold newostack, offset_after_alloc in RNG.
      rewrite Z.max_r in RNG by omega. simpl in RNG. omega.
      rewrite NIL in *. simpl. tauto.
    }
    trim A.
    {
      revert NS. unfold no_stack. intros (fi0 & EQS & PUBLIC). rewrite EQS.
      simpl. intros f2 fi1 [?|[]]; subst. unfold in_frame. simpl. intros _. inversion 1; subst.
      intros; apply PUBLIC.
    }
    destruct A as (f' & MINJ' & INCR & EQ1 & EQ2).
    exists f'.
    split.
    {
      intros.
      destruct peq; subst; eauto.
    }
    split; auto.
    (* store parent *)
    exploit Mem.store_mapped_inject. apply MINJ'. simpl in *; eauto. eauto.
    eapply val_inject_incr; eauto. intros (m3' & STORE & MINJ2).
    simpl.
    assert (Ptrofs.unsigned (Ptrofs.add (Ptrofs.repr newostack) (Ptrofs.repr (seg_ofs fl))) =
            seg_ofs fl + newostack) as EQ.
    2: rewrite EQ, STORE.
    rewrite Ptrofs.add_commut. erewrite Mem.address_inject; eauto. rewrite Ptrofs.unsigned_repr. omega. omega.
    exploit Mem.store_valid_access_3. exact STORE_PARENT.
    intro VA; eapply Mem.store_valid_access_1 in VA; eauto. destruct VA.
    eapply H. rewrite Ptrofs.unsigned_repr; generalize (size_chunk_pos Mptr); omega.
    eexists; split; eauto.
    (* store return address *)
    exploit Mem.store_mapped_inject. apply MINJ2. simpl in *; eauto. eauto.
    eapply val_inject_incr; eauto. intros (m4' & STORE' & MINJ3).
    assert (Ptrofs.unsigned (Ptrofs.add (Ptrofs.repr newostack) (Ptrofs.repr ofs_ra)) =
            ofs_ra + newostack) as EQ'.
    2: rewrite EQ', STORE'.
    rewrite Ptrofs.add_commut.
    erewrite Mem.address_inject; eauto.
    rewrite Ptrofs.unsigned_repr; omega.
    exploit Mem.store_valid_access_3. exact STORE_RETADDR.
    intro VA; eapply Mem.store_valid_access_1 in VA; eauto. destruct VA.
    eapply H.
    rewrite Ptrofs.unsigned_repr; generalize (size_chunk_pos Mptr); omega.
    eexists; split; eauto.
    (* record the stack block *)
    destruct NS as (fstack & EQstk & PUB & SZ).
    exploit Mem.record_stack_block_inject_left_zero. apply MINJ3. 6: eauto.
    repeat rewrite_stack_blocks. rewrite EQstk. constructor; reflexivity.
    {
      constructor.
      - simpl. constructor; auto. intros. left; congruence.
      - red. simpl.
        constructor; auto.
        intros.
        rewrite EQ1 in H; inv H.
        split.
        + intros; eapply stack_perm_le_public. intros; apply PUB.
        + intros; rewrite SZ.
          unfold newostack, offset_after_alloc.
          destruct (RSPDEC) as [[EQRSP ?]|[NOPTR [EQ3 NIL]]]; subst.
          rewrite EQRSP in RSPEQ. specialize (RSPEQ _ _ eq_refl). inv RSPEQ.
          rewrite H0.
          * red in AGSP. apply AGSP in EQRSP.  rewrite EQRSP.
            cut (o - size_stack (Mem.stack_adt m1) - align (Z.max 0 (frame_size fi)) 8 < 0). omega.
            generalize (size_stack_pos (Mem.stack_adt m1)).
            cut (o - align (Z.max 0 (frame_size fi)) 8 < 0). omega.
            cut (o < align (Z.max 0 (frame_size fi)) 8). omega.
            eapply Z.lt_le_trans.
            2: apply align_le. 2: omega. rewrite Z.max_r. omega. omega.
          * rewrite EQ3.
            cut (o < align (Z.max 0 (frame_size fi)) 8). omega.
            eapply Z.lt_le_trans.
            2: apply align_le. 2: omega. rewrite Z.max_r. omega. omega.
    }
    {
      repeat rewrite_stack_blocks.
      auto.
    }
    { repeat rewrite_stack_blocks. rewrite EQstk. constructor; auto.
    }
    simpl; auto.
    intro H.
    (* proving the final match_states *)
    rewrite <- (Ptrofs.unsigned_repr newostack) by omega.
    econstructor; eauto.
    - eapply Mem.mem_inject_ext. eauto. simpl; intros.
      repeat rewrite_stack_blocks. simpl. destr. subst. simpl. auto.
      destr. destr.  omega. destr. omega.
    - intros b0 o A. unfold rs2 in A.
      rewrite nextinstr_rsp in A.
      rewrite Pregmap.gss in A. inv A; auto.
    - intros r.
      unfold rs2, rs2'.
      destruct (PregEq.eq r RSP).
      + subst. rewrite ! nextinstr_rsp. rewrite ! Pregmap.gss.
        econstructor; eauto. rewrite Ptrofs.add_zero_l; auto.
      + apply val_inject_nextinstr. intros.
        assert (r0 <> RSP) by intuition congruence.
        rewrite ! (Pregmap.gso _ _ H2) by auto.
        eapply val_inject_set; eauto.
    - eapply Mem.store_valid_block_1. eauto.
      eapply Mem.store_valid_block_1. eauto.
      eauto.
    - red. unfold rs2'. rewrite nextinstr_rsp. rewrite Pregmap.gss. inversion 1. subst.
      repeat rewrite_stack_blocks.
      rewrite Ptrofs.unsigned_repr by auto.
      unfold newostack, offset_after_alloc in *.
      destruct (RSPDEC) as [[EQRSP ?]|[NOPTR [EQRSP NIL]]]; subst.
      rewrite EQRSP in RSPEQ. specialize (RSPEQ _ _ eq_refl). inv RSPEQ.
      rewrite H2. rewrite (AGSP _ EQRSP).
      simpl. omega.
      rewrite EQRSP, NIL in *. simpl. omega.
    - rewrite_stack_blocks.
      unfold rs2. rewrite nextinstr_rsp. apply Pregmap.gss.
    - repeat rewrite_stack_blocks. constructor; auto.
    - repeat rewrite_stack_blocks. constructor; auto.
      simpl. rewrite INFL. reflexivity.
    - red. intros ostack1 A. unfold rs2' in A. rewrite nextinstr_rsp in A. rewrite Pregmap.gss in A.
      inversion A. subst.
      rewrite Ptrofs.unsigned_repr by omega.
      unfold newostack.
      apply Z.divide_sub_r.
      destruct (RSPDEC) as [[EQRSP ?]|[NOPTR [EQRSP NIL]]]; subst.
      rewrite H0; apply SPAL; auto.
      rewrite EQRSP. apply Mem.stack_limit_aligned.
      apply align_divides. omega.
    - red. intros ofs k p PERM.
      repeat rewrite_perms_bw PERM. eauto.
    - red; intros.
      repeat rewrite_perms_fw. eauto.
    - red. repeat rewrite_stack_blocks. eauto.
    - unfold rs2'. rewrite nextinstr_rsp, Pregmap.gss. inversion 1. eauto.
    - rewrite Ptrofs.unsigned_repr by omega.
      red. intros b0 delta o k p JB PERM.
      repeat rewrite_perms_bw PERM.
      destruct peq.
      * subst. rewrite EQ1 in JB. inv JB. split. omega.
        rewrite_stack_blocks. simpl. unfold in_frame; simpl; auto.
      * split. unfold newostack, offset_after_alloc.
        transitivity curofs.
        -- generalize (Z.le_max_l 0 (frame_size fi)); intro MAX.
           generalize (align_le (Z.max 0 (frame_size fi)) 8). omega.
        --
          destruct (RSPDEC) as [[EQRSP ?]|[NOPTR [EQRSP NIL]]]; subst.
          rewrite H0.
          rewrite EQ2 in JB; auto.
          exploit NIB; eauto. tauto.
          exploit NIB; eauto. rewrite <- EQ2. eauto. auto.
          rewrite NIL. simpl; tauto.
        -- repeat rewrite_stack_blocks. simpl; auto.
           right.
           eapply NIB; eauto. rewrite <- EQ2; eauto.
    - repeat rewrite_stack_blocks.
      constructor; auto.
      eapply inject_stack_incr; eauto.
      rewrite EQ1. f_equal. f_equal.
      unfold newostack, offset_after_alloc.
      destruct (RSPDEC) as [[EQRSP ?]|[NOPTR [EQRSP NIL]]]; subst.
      rewrite H0.
      rewrite AGSP. omega. auto. rewrite EQRSP, NIL. simpl; omega.
    - intros b0 fi0 delta GFI FB0 b' o delta' k p FB1 P1.
      unfold get_frame_info in GFI.
      revert GFI. repeat rewrite_stack_blocks. intro GFI.
      simpl in GFI.
      repeat rewrite_perms_bw P1.
      destr_in GFI.
      + destruct o0; try easy. subst. inv GFI. rewrite FB0 in EQ1; inv EQ1.
        destr_in P1.
        * subst. rewrite FB0 in FB1; inv FB1.
          rewrite Z.max_r by omega.  omega.
        * rewrite EQ2 in FB1 by auto.
          eapply NIB in P1; eauto.
          destruct P1 as (LE & IN).
          unfold newostack, offset_after_alloc.
          destruct (RSPDEC) as [[EQRSP EQA]|[NOPTR [EQA NIL]]]; subst; rewrite EQA.
          omega. rewrite NIL in IN; easy.
      + rewrite EQ2 in FB0 by auto.
        intro RNG.
        assert (0 < frame_size fi0).
        destruct (zlt 0 (frame_size fi0)); auto.
        rewrite Z.max_l in RNG by omega. change (align 0 8) with 0 in RNG. omega.
        rewrite Z.max_r in RNG by omega.
        destruct (RSPDEC) as [[EQRSP EQA]|[NOPTR [EQA NIL]]]; subst; rewrite EQA, ?NIL in *; try easy.
        generalize (perm_stack_eq _ _ _ _ PS GFI). intro PF0.
        destr_in P1.
        * subst. rewrite EQ1 in FB1; inv FB1.
          cut (newostack + (frame_size fi)  <= delta). omega.
          unfold newostack. rewrite EQA.
          rewrite AGSP; auto.
          eapply in_stack_inj_below in GFI; eauto.
          destruct GFI as (l1 & l2 & EQADT & JB0). rewrite FB0 in JB0. inv JB0.
          rewrite Z.max_r in * by omega.
          unfold offset_after_alloc.
          rewrite Z.max_r by omega.
          cut (StackADT.size_stack (Mem.stack_adt m1)
               >= StackADT.size_stack l2).
          generalize (align_le (frame_size fi) 8). omega.
          rewrite EQADT.
          rewrite size_stack_app.
          generalize (size_stack_pos l1); omega.
        * eapply IP.  apply GFI. eauto.
          rewrite <- EQ2. apply FB1. auto. eauto.
          rewrite Z.max_r by omega. omega.
    - repeat rewrite_stack_blocks.
      constructor; auto.
      eapply perm_stack_inv. eauto. apply Mem.in_frames_valid.
      split; intros.
      repeat rewrite_perms_bw H2.
      destr_in H2.
      subst.
      eapply Mem.in_frames_valid in H0.
      eapply Mem.fresh_block_alloc in H0. easy.
      eauto.
      repeat rewrite_perms_fw. auto.
      split; intros.
      repeat rewrite_perms_bw H0.
      rewrite pred_dec_true in H0; auto.
      do 3 rewrite_perms_fw. eapply Mem.perm_implies. eapply Mem.perm_alloc_2. eauto. eauto. constructor.
    - repeat rewrite_stack_blocks.
      assert (Mem.unchanged_on (fun b o => in_frames (Mem.stack_adt m1) b) m1 m5).
      {
        eapply Mem.unchanged_on_trans.
        eapply Mem.alloc_unchanged_on. eauto.
        eapply Mem.unchanged_on_trans.
        eapply Mem.store_unchanged_on; simpl in *; eauto.
        intros. intro INF; eapply Mem.in_frames_valid in INF; eapply Mem.fresh_block_alloc; eauto.
        eapply Mem.unchanged_on_trans.
        eapply Mem.store_unchanged_on; simpl in *; eauto.
        intros. intro INF; eapply Mem.in_frames_valid in INF; eapply Mem.fresh_block_alloc; eauto.
        eapply Mem.strong_unchanged_on_weak.
        eapply Mem.record_stack_block_unchanged_on; eauto.
      }
      eapply load_rsp_inv' in LRSP.
      eapply load_rsp_add. eauto.
      rewrite Forall_forall; intros.
      erewrite load_record_stack_blocks. 2: eauto.
      erewrite Mem.load_store_other.
      erewrite Mem.load_store_same.
      2: rewrite <- STORE_PARENT. 2: simpl; f_equal.
      destr_in AGSP1.
      rewrite AGSP1.
      change (Mptr) with (chunk_of_type Tptr).
      rewrite Val.load_result_same. auto. auto.
      destr_in AGSP1.
      destr_in AGSP1.
      destr_in AGSP1.
      destr_in AGSP1.
      destruct o; try easy.
      rewrite AGSP1.
      change (Mptr) with (chunk_of_type Tptr).
      rewrite Val.load_result_same. auto. simpl. unfold Tptr.
      destruct ptr64; auto.
      f_equal. rewrite INFL in H2. simpl in H2. intuition.
      eauto.
      right.
      unfold in_segment in DISJ.
      destruct (zle (seg_ofs x  + size_chunk Mptr) ofs_ra); auto.
      destruct (zle (ofs_ra + size_chunk Mptr) (seg_ofs x)); auto.
      exfalso.
      assert (x = fl). rewrite INFL in H2; simpl in H2; intuition. subst.
      specialize (DISJ (Z.max (seg_ofs fl) ofs_ra)).
      trim DISJ. split. apply Z.le_max_l.
      rewrite Zmax_spec. destr. omega. omega.
      trim DISJ. split. apply Z.le_max_r.
      rewrite Zmax_spec. destr. omega. omega. auto.
      intros bs INF. apply Mem.in_frames_valid in INF.
      eapply Plt_Ple_trans. apply INF.
      erewrite Mem.alloc_result. apply Ple_refl. eauto.
      eapply Mem.unchanged_on_implies. apply H0.
      simpl; intros.
      red in H2.
      destr_in H2.
      destruct (in_frames_dec (Mem.stack_adt m1) b0); auto.
      rewrite not_in_frames_get_assoc in Heqo; eauto; congruence.
    - destruct GLOBSYMB_INJ; split.
      + intros. eapply INCR. eauto.
      + intros. destruct (peq b1 b).
        subst; rewrite EQ1 in H3. inv H3.
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
        rewrite EQ2 in H3.
        eauto.
        auto.
    - erewrite Mem.record_stack_block_nextblock. 2: eauto.
      erewrite Mem.nextblock_store. 2 : eauto.
      erewrite Mem.nextblock_store. 2 : eauto.
      erewrite Mem.nextblock_alloc. 2: eauto. xomega.
    - erewrite Mem.nextblock_store. 2 : eauto.
      erewrite Mem.nextblock_store. 2 : eauto. xomega.
  Qed.
  
  Lemma size_stack_divides l:
    (8 | StackADT.size_stack l).
  Proof.
    induction l; simpl; intros; eauto.
    exists 0; omega.
    destruct a, p.
    apply Z.divide_add_r. auto. apply align_divides. omega.
  Qed.

  Lemma inject_stack_all_below:
    forall l m,
      load_rsp l m ->
      forall b b',
        in_frame ((hd (nil,None,0) l)) b ->
        in_frames (tl l) b' ->
        Plt b' b. 
  Proof.
    induction 1; simpl; intros. easy.
    easy.
    unfold in_frame in *. simpl in *.
    destruct H2; inv H2.
    destruct H3. destruct H2; inv H2. auto.
    eapply Plt_trans.
    eapply IHload_rsp. eauto. auto. eauto. 
  Qed.

  Lemma inject_stack_only_once:
    forall l m a b,
      load_rsp (a::l) m ->
      in_frame a b ->
      get_assoc l b = None.
  Proof.
    inversion 1; subst. simpl. auto.
    simpl. intro; subst.
    rewrite pred_dec_false.
    - rewrite not_in_frames_get_assoc; auto.
      intro INF.
      cut (Plt b0 b'). xomega.
      eapply inject_stack_all_below; eauto.
      unfold in_frame; simpl. auto.
      unfold in_frame; simpl. red in H0; simpl in H0. destruct H0; subst; easy. 
    - intros [?|[]]; subst. red in H0; simpl in H0. destruct H0 as [?|[]]. subst. xomega. 
  Qed.

  Lemma inject_stack_norepeat:
    forall l m a b,
      load_rsp (a::l) m ->
      in_frame (a) b ->
      ~ in_frames l b.
  Proof.
    inversion 1; subst. simpl. auto.
    simpl. unfold in_frame. simpl. intros [?|[]].
    subst. intros [[?|[]]|?]. subst; xomega.
    eapply inject_stack_all_below in H3; eauto.
    2: unfold in_frame; simpl; eauto. xomega.
  Qed.

  Lemma exec_instr_inject':
    forall j ostack m1 m2 rs1 rs2 f i rs1' m1',
      match_states j ostack (State rs1 m1) (State rs2 m2) ->
      asm_instr_no_rsp i ->
      asm_instr_no_stack i ->
      Asm.exec_instr ge f i rs1 m1 = Next rs1' m1' ->
      exists j' ostack' rs2' m2',
        exec_instr ge f i rs2 m2 = Next rs2' m2'
        /\ match_states j' ostack' (State rs1' m1') (State rs2' m2')
        /\ inject_incr j j'.
  Proof.
    intros j ostack m1 m2 rs1 rs2 f i rs1' m1' MS AINR AINS EI.
    destruct (is_unchanged i) eqn:?.
    - edestruct exec_instr_inject as (rs2' & m2' & EXEC' & MINJ' & RINJ'); eauto.
      inv MS; eauto. inv MS; eauto.
      exists j, ostack, rs2', m2'; split; [|split]; eauto.
      destruct i as (i & info).
      destruct i; simpl in *; eauto; try congruence.
      inv MS; econstructor; eauto.
      + eapply Mem.mem_inject_ext; eauto. simpl.
        edestruct AINS. eauto. apply EI. rewrite H. tauto.
      + erewrite AINR; eauto.
      + eapply asmgen_nextblock_forward in EXEC'.
        red in VB |- *. xomega.
      + red. intros. erewrite AINR in H; eauto.
        edestruct AINS. eauto. apply EI. rewrite H0. auto.
      + edestruct AINS. eauto. apply EI. rewrite H.
        erewrite AINR; eauto.
      + edestruct AINS. eauto. apply EI. rewrite H. auto.
      + edestruct AINS. eauto. apply EI. rewrite H. auto.
      + red. intros.
        erewrite AINR in H; eauto.
      + red; intros.
        edestruct AINS. eauto. apply EXEC'.
        rewrite H1 in H; eauto.
      + red; intros.
        edestruct AINS. eauto. apply EXEC'.
        rewrite H1; eauto.
      + red; intros.
        edestruct AINS. eauto. apply EXEC'. rewrite H. auto.
      + erewrite AINR; eauto.
      + edestruct AINS. eauto. apply EI.
        red; intros.
        edestruct AINS. eauto. apply EI. rewrite H3.
        eapply NIB. auto. rewrite <- H4. eauto.
      + edestruct AINS. eauto. apply EI. rewrite H. eapply inject_stack_incr; eauto.
      + edestruct AINS. eauto. apply EI.
        red. unfold get_frame_info.
        rewrite H.
        intros b fi delta GFI JB b' o delta' k p JB' PERM RNG.
        eapply IP. eauto. eauto. eauto. rewrite <- H0; eauto.
        apply RNG.
      + edestruct AINS. eauto. apply EI. rewrite H.
        eapply perm_stack_inv. eauto. apply Mem.in_frames_valid.
        intros; apply H0.
      + edestruct AINS. eauto. apply EI. rewrite H.
        intros; eapply load_rsp_inv'. eauto.
        eapply exec_instr_unchanged_on; eauto.
      + etransitivity. apply GlobLe.
        eapply asmgen_nextblock_forward; eauto.
      + etransitivity. apply GlobLeT.
        eapply asmgen_nextblock_forward; eauto.

    - destruct i as (i & info).
      destruct i; simpl in *; try congruence.
      + (* allocframe *)
        unfold Asm.exec_instr in EI. simpl in EI.
        repeat destr_in EI.
        unfold check_alloc_frame in Heqb0.
        rewrite andb_true_iff in Heqb0.
        rewrite ! andb_true_iff in Heqb0.
        destruct Heqb0 as (((numlinks & EQofslink) & DISJ) & SZpos).
        assert (length (frame_link frame) = 1%nat). destruct Nat.eq_dec; auto. simpl in numlinks. discriminate.
        destruct (frame_link frame) eqn:FL. simpl in H; inv H.
        destruct l; simpl in H. 2: inv H. clear H. clear numlinks.
        assert (Forall (fun fl => Ptrofs.unsigned ofs_link = seg_ofs fl) (s::nil)).
        edestruct Forall_dec; eauto. simpl in EQofslink; discriminate.
        clear EQofslink Heqb.
        inversion MS; subst.
        inv H. inv H3.
        edestruct Mem.push_frame_alloc_record as (malloc & ALLOC & mstores & STORES & RSB). eauto.
        simpl in STORES. destr_in STORES. destr_in STORES. inv STORES.
        edestruct alloc_inject as (j' & JSPEC & INCR & m3' & STORE1 & m4' & STORE2 & MS') ; eauto.
        rewrite H2 in Heqo0. eauto.
        rewrite <- H2. apply Ptrofs.unsigned_range_2.
        apply Ptrofs.unsigned_range_2.
        destruct zle; auto. discriminate.
        apply disjointb_disjoint. rewrite <- H2. auto.
        simpl in *.
        set (newostack := offset_after_alloc (current_offset (rs2 RSP)) frame).
        fold newostack in STORE1, STORE2, JSPEC, MS'.
        rewrite <- H2 in STORE1. rewrite Ptrofs.repr_unsigned in STORE1.
        rewrite Ptrofs.repr_unsigned in STORE2.
        setoid_rewrite STORE1. setoid_rewrite STORE2.
        exists j',  newostack; eexists; eexists; split; eauto.

      +
        unfold Asm.exec_instr in EI. simpl in EI.
        repeat destr_in EI.
        inv MS.
        specialize (RSPzero _ _ Heqv1). subst.
        exploit Mem.loadv_inject. eauto. apply Heqo.
        apply Val.offset_ptr_inject. rewrite <- Heqv1; auto. intros (v2 & LOAD2 & INJ2).
        exploit Mem.loadv_inject. eauto. apply Heqo0.
        apply Val.offset_ptr_inject. rewrite <- Heqv1; auto. intros (v3 & LOAD3 & INJ3).
        rewrite LOAD2, LOAD3.
        unfold check_top_frame in Heqb0.
        repeat (destr_in Heqb0; [idtac]).
        repeat rewrite andb_true_iff in Heqb1.
        destruct Heqb1 as ((((((A & B) & C) & D) & E) & F) & G).
        destruct (in_dec peq b l0); try congruence.
        apply ZEQ in B. apply ZEQ in C.
        subst.
        set (newostack := Ptrofs.unsigned ostack0 + align (Z.max 0 (frame_size f1)) 8).
        destr_in AGSP1. destr_in AGSP1.
        simpl in i. destruct i; try easy. subst.
        exploit free_inject; eauto.
        {
          inversion PS as [|? ? ? ? ? PS' PERMeq]; subst.
          intros o k p PERM. rewrite <- PERMeq; eauto.
        }
        {
          erewrite Mem.free_stack_blocks; eauto. rewrite Heql.
          unfold is_stack_top. simpl. intros ? [?|[]]. auto.
        }
        {
          destruct NS as (f0 & EQ & ?). rewrite EQ. reflexivity.
        }
        intros INJ.
        exists j, newostack; eexists; eexists; split; [|split]; eauto.
        generalize (RINJ RSP). rewrite Heqv1. inversion 1 as [ff|ff|ff|ff|? ? ? ? ? INJB ? x EQRSP|ff]; subst.
        symmetry in EQRSP.
        rewrite Ptrofs.add_zero_l in *.
        exploit RSPEQ. eauto. intros (AA & B). subst.
        specialize (AGSP _ EQRSP).
        assert (VoEQ: v0 = (match l with
                        nil => init_sp
                      | (b'::nil,_,_)::r => Vptr b' Ptrofs.zero
                      | _ => Vundef
                      end)).
        {
          assert (FF: Forall (fun fl => Ptrofs.unsigned ofs_link = seg_ofs fl) (frame_link f1)).
          edestruct Forall_dec; eauto. discriminate.
          inv OneLink. simpl in H2. inv H2.
          destruct (frame_link f1) eqn:EQ. inv H1.
          destruct l0. 2: inv H1. clear H1.
          inv FF.
          move Heqo0 at bottom.
          simpl in Heqo0. rewrite Ptrofs.add_zero_l in Heqo0.
          rewrite H2 in Heqo0.
          inv LRSP.
          rewrite Forall_forall in H8. rewrite H8 in Heqo0. congruence.
          rewrite EQ. simpl; auto.
          rewrite Forall_forall in H8. rewrite H8 in Heqo0. congruence.
          rewrite EQ. simpl; auto.
        }
        subst.
        specialize (SPAL _ EQRSP).
        generalize (Mem.unrecord_stack_adt _ _ Heqo2).
        erewrite Mem.free_stack_blocks. 2: eauto. rewrite Heql. intros (bb0 & EQ).
        inv EQ.
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
          rewrite AGSP. rewrite Heql. simpl. omega.
        }
        rewrite <- (Ptrofs.unsigned_repr newostack) by omega.
        econstructor; eauto.
        * eapply Mem.mem_inject_ext. eauto.
          simpl. intros. repeat destr; omega.
        * intros b0 o NI. rewrite nextinstr_rsp in NI. rewrite Pregmap.gso in NI by congruence.
          rewrite Pregmap.gss in NI. subst.
          destr_in NI. destr_in Heqb0. destruct f0, p. repeat destr_in NI.
        * intros; apply val_inject_nextinstr.
          intros; apply val_inject_set; auto.
          intros; apply val_inject_set; auto.
        (* * red. rewrite nextinstr_rsp. rewrite ; edestruct Mem.unrecord_stack_block_mem_unchanged. simpl ; apply USB. *)
        (*   rewrite H0; eauto. *)
        * red. rewrite nextinstr_rsp.
          rewrite ! Pregmap.gso by congruence.
          rewrite Pregmap.gss. intros; subst.
          inv INJ3.
          repeat destr_in H0. discriminate.
          rewrite Ptrofs.add_zero_l.
          inv IS. inv H4. rewrite H3 in H10; inv H10. simpl.
          rewrite Ptrofs.unsigned_repr. omega. simpl in RNGnewofs; omega.
          repeat destr_in H1. discriminate.
        * repeat destr_in INJ3.
          rewrite EQRSP in H. inv H. rewrite INJB in H4. inv H4.
          rewrite nextinstr_rsp. rewrite Pregmap.gso by congruence.
          rewrite Pregmap.gss.
          inv LRSP. auto.
        * inv SZpos.  auto.
        * inv OneLink.  auto.
        * red. rewrite nextinstr_rsp.
          rewrite ! Pregmap.gso by congruence.
          rewrite Pregmap.gss. intros; subst.
          inv LRSP. rewrite <- H4 in *. destr_in Heqb0; inv INJ3.
          rewrite <- H4 in *. inv INJ3.
          inv IS. inv H8. rewrite H3 in H14; inv H14.
          rewrite Ptrofs.add_zero_l.
          rewrite Ptrofs.unsigned_repr. rewrite Heql in AGSP. simpl in AGSP.
          apply Z.divide_sub_r.
          apply Z.divide_sub_r.
          apply Mem.stack_limit_aligned.
          apply size_stack_divides.
          apply align_divides; omega.
          simpl in RNGnewofs. omega.
        *
        (* * red. *)
        (*   intros ofs k p PERM. *)
        (*   eapply Mem.unrecord_stack_block_perm in PERM. 2: eauto. eauto. *)
        (* * red. *)
        (*   intros ofs k RNG. *)
        (*   eapply Mem.unrecord_stack_block_perm'. 2: eauto. eauto.                  *)
        (* * red. *)
        (*   edestruct Mem.unrecord_stack_adt. apply USB. red in NS. rewrite H0 in NS. *)
        (*   inv NS; auto. *)
          (* *  *)
          unfold nextinstr.
          rewrite ! Pregmap.gso by congruence.
          rewrite Pregmap.gss.
          intros. subst.
          inv LRSP;
          match goal with
            H: _ = Mem.stack_adt ?m |- _ => rewrite <- H in *; destr_in Heqb0; inv INJ3
          end.
          repeat match goal with
                   IS: inject_stack _ (_::_) |- _ => inv IS
                 end.
          repeat match goal with
                   A: ?a = ?b, B: ?a = ?c |- _ => rewrite A in B; inv B
                 end.
          split; auto. rewrite Ptrofs.add_zero_l.
          unfold newostack. rewrite AGSP. rewrite Heql. simpl. f_equal. omega.
        * red. intros b0 delta0 o k p JB0 PERM.
          eapply Mem.unrecord_stack_block_perm in PERM. 2: eauto.
          erewrite Mem.perm_free in PERM. 2: eauto.
          destruct PERM as (NOTSAME & PERM).
          generalize (NIB b0 delta0 o k p JB0 PERM).
          destruct (peq b0 b).
          -- subst.
             inv PS. clear H5. rename H6 into PERM_in_range.
             apply PERM_in_range in PERM. intuition.
          -- clear NOTSAME.
             rewrite Heql. simpl.
             intros (LE & OR). destruct OR; try congruence.
             red in H0; simpl in H0. destruct H0 as [?|[]]; subst.
             congruence.
             split; auto.
             rewrite Ptrofs.unsigned_repr by omega.
             unfold newostack.
             destruct (zle (Ptrofs.unsigned (Ptrofs.repr delta) + align (Z.max 0 (frame_size f1)) 8) (o + delta0)); auto.
             exfalso.
             apply Z.gt_lt in g.
             assert (max_perm: forall m b o k p, Mem.perm m b o k p -> Mem.perm m b o Max Nonempty).
             {
               intros.
               eapply Mem.perm_implies.
               eapply Mem.perm_max. eauto. constructor.
             }
             generalize (Mem.free_range_perm _ _ _ _ _ Heqo1). intro FP.
             assert (0 < frame_size f1).
             destruct (zlt 0 (frame_size f1)); auto.
             apply Z.ge_le in g0.
             rewrite Z.max_l in g by omega.
             change (align 0 8) with 0 in g. omega.
             generalize (fun pf => Mem.address_inject _ _ _ _ b Ptrofs.zero _ _ Freeable MINJ (FP _ pf) INJB).
             rewrite Ptrofs.unsigned_zero. rewrite Ptrofs.add_zero_l.  simpl.
             intro UR. trim UR. omega.
             destruct (zlt (o + delta0) (delta + frame_size f1)).
             ++ generalize (fun o2 RNG => Mem.mi_no_overlap _ _ _ _ MINJ b0 _ _ _ _ _ o o2 n JB0 INJB (max_perm _ _ _ _ _ PERM) (max_perm _ _ _ _ _ (FP _ RNG))).
                assert (exists o2, 0 <= o2 < frame_size f1 /\ o + delta0 = o2 + delta) as EX.
                {
                  exists (o + delta0 - delta).
                  omega.
                }
                destruct EX as (o2 & RNG & EQ').
                intro CONTRA; edestruct CONTRA; eauto.
             ++ assert (delta + frame_size f1 <= o + delta0 < delta + align (frame_size f1) 8).
                rewrite Z.max_r in g by omega. omega.
                assert (exists o2, frame_size f1 <= o2 < align (frame_size f1) 8 /\ o + delta0 = o2 + delta) as EX.
                {
                  exists (o + delta0 - delta).
                  omega.
                }
                destruct EX as (o2 & RNG & EQ').
                eapply IP. 4: apply PERM.  3: eauto. 2: apply INJB.
                unfold get_frame_info; rewrite Heql.
                simpl. rewrite pred_dec_true; auto.
                rewrite Z.max_r. omega. omega.
        *
          inv IS. auto.
        * red; intros.
          destruct (peq b' b).
          subst.
          eapply Mem.unrecord_stack_block_perm in H3. 2: eauto.
          eapply Mem.perm_free_2 in H3.
          easy. eauto.
          eapply perm_stack_eq. eauto. simpl. rewrite pred_dec_true. auto. left; reflexivity.
          eapply Mem.perm_free_3. eauto. eauto.
          eapply Mem.unrecord_stack_block_perm in H3. 2: eauto.
          eapply Mem.perm_free_3 in H3. 2: eauto.
          eapply IP; eauto.
          unfold get_frame_info. rewrite Heql.
          simpl.
          destruct peq; auto.
          subst.
          unfold get_frame_info in H0.
          erewrite inject_stack_only_once in H0.
          congruence.
          eauto. red; simpl; auto.
        * inv PS. eapply perm_stack_inv; eauto.
          intros; eapply Mem.in_frames_valid.
          rewrite Heql; simpl; auto.
          intros.
          cut (b0 <> b).
          intro DIFF.
          split; intros P.
          eapply Mem.unrecord_stack_block_perm in P. 2: eauto.
          eapply Mem.perm_free_3; eauto.
          eapply Mem.unrecord_stack_block_perm'. eauto.
          eapply Mem.perm_free_1; eauto.
          intro; subst.
          eapply inject_stack_norepeat in H0; eauto.
          red; simpl; auto.
        * inversion LRSP. constructor.
          rewrite <- H4 in *.
          eapply load_rsp_inv'. eauto.
          eapply Mem.unchanged_on_trans.
          eapply Mem.unchanged_on_implies.
          eapply Mem.free_unchanged_on. eauto.
          instantiate (1:= fun b0 o => b0 <> b). simpl. congruence.
          simpl.
          intros.
          intro; subst.
          red in H8. destr_in H8. simpl in Heqo3. rewrite pred_dec_false in Heqo3.
          exploit inject_stack_norepeat. apply LRSP. red; simpl. eauto.
          simpl.
          destruct (in_frames_dec l b); auto.
          erewrite not_in_frames_get_assoc in Heqo3; eauto; congruence. auto.
          intros [?|[]]; subst. xomega.
          eapply Mem.strong_unchanged_on_weak.
          eapply Mem.unrecord_stack_block_unchanged_on.
          eauto.
        * etransitivity. apply GlobLe.
          erewrite <- Mem.nextblock_free. 2: eauto.
          erewrite <- Mem.unrecord_stack_block_nextblock.
          2: eauto. xomega.
        * discriminate.
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

  Lemma link_offsets_not_public_stack_range:
    forall b ofs0 l m ,
      link_offsets l b ofs0 ->
      Mem.valid_block m b -> ~ match get_assoc l b with
                              | Some fi => public_stack_range ofs0 (ofs0 + 1) fi
                              | None => True
                              end.
  Proof.
    unfold public_stack_access.
    unfold get_frame_info.
    induction l; simpl; intros; eauto.
    destruct a.
    simpl in *.
    red in H.
    simpl in H.
    destr_in H. destr_in Heqo.
    intro PSR. red in PSR. specialize (PSR ofs0). trim PSR. omega.
    generalize (frame_link_readonly f). rewrite Forall_forall.
    edestruct in_segments_in_segment as (x & INX & INS); eauto.
    intro F; eapply F in INX; eauto. setoid_rewrite PSR in INX. congruence.
  Qed.


  Theorem step_simulation:
    forall S1 t S2,
      Asm.step ge S1 t S2 ->
      forall j ostack S1' (MS: match_states j ostack S1 S1'),
      exists j' ostack' S2',
        step ge S1' t S2' /\
        match_states j' ostack' S2 S2'.
  Proof.
    destruct 1; intros; inversion MS; subst.
    -
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
    -
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
      eauto.
      eauto.
      generalize (RINJ PC); rewrite H. inversion 1; subst.
      assert (j b = Some (b,0)) as JB.
      {
        eapply GLOBFUN_INJ. eauto.
      }
      rewrite JB in H9; inv H9.
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
      + eapply Mem.mem_inject_ext. eauto.
        erewrite external_call_stack_blocks; eauto.
      + rewrite nextinstr_nf_rsp.
        intros b o.
        rewrite set_res_no_rsp.
        rewrite Asmgenproof0.undef_regs_other.
        eauto.
        intros; intro; subst. rewrite in_map_iff in H6.
        destruct H6 as (x & EQ & IN).
        apply preg_of_not_rsp in EQ. congruence.
        auto.
      + intros. apply val_inject_nextinstr_nf.
        apply val_inject_set_res; auto.
        apply val_inject_undef_regs; auto.
        intros; eapply val_inject_incr; eauto.
      + eapply external_call_valid_block; eauto.
      + red. rewrite nextinstr_nf_rsp.
        rewrite set_res_no_rsp; auto.
        rewrite Asmgenproof0.undef_regs_other.
        erewrite <- external_call_stack_blocks. eauto. eauto.
        intros; intro; subst.
        rewrite in_map_iff in H6.
        destruct H6 as (x & EQ & IN).
        apply preg_of_not_rsp in EQ. congruence.
      + erewrite <- external_call_stack_blocks. 2: eauto.
        rewrite nextinstr_nf_rsp.
        rewrite set_res_no_rsp; auto.
        rewrite Asmgenproof0.undef_regs_other. eauto.
        intros; intro; subst.
        rewrite in_map_iff in H6.
        destruct H6 as (x & EQ & IN).
        apply preg_of_not_rsp in EQ. congruence.
      + erewrite <- external_call_stack_blocks; eauto.
      + erewrite <- external_call_stack_blocks; eauto.
      + red.
        rewrite nextinstr_nf_rsp.
        rewrite set_res_no_rsp; auto.
        rewrite Asmgenproof0.undef_regs_other. eauto.
        intros; intro; subst.
        rewrite in_map_iff in H6.
        destruct H6 as (x & EQ & IN).
        apply preg_of_not_rsp in EQ. congruence.
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
      + rewrite nextinstr_nf_rsp.
        rewrite set_res_no_rsp; auto.
        rewrite Asmgenproof0.undef_regs_other. eauto.
        intros; intro; subst.
        rewrite in_map_iff in H6.
        destruct H6 as (x & EQ & IN).
        apply preg_of_not_rsp in EQ. congruence.
      + red. intros b delta o k p JB1 PERM.
        erewrite <- external_call_stack_blocks. 2: eauto.
        destruct (j b) eqn:A. destruct p0.
        exploit INCR. eauto. eauto. intro JB2. rewrite JB1 in JB2; inv JB2.
        eapply NIB; eauto.
        eapply Mem.perm_max in PERM.
        eapply external_call_max_perm in PERM.
        2: eauto.
        eauto.
        eapply Mem.valid_block_inject_1; eauto.
        exploit SEP. eauto. eauto. intuition congruence.
      + erewrite <- external_call_stack_blocks. 2: eauto.
        eapply inject_stack_incr; eauto.
      +
        red.
        unfold get_frame_info.
        erewrite <- external_call_stack_blocks. 2: eauto.
        intros.
        exploit inj_incr_sep_same. eauto. eauto. apply H7. auto.
        exploit inj_incr_sep_same. eauto. eauto. apply H9. auto.
        intros.
        eapply IP; eauto.
        eapply Mem.perm_max in H10.
        eapply external_call_max_perm; eauto.
        eapply Mem.valid_block_inject_1 in H11; eauto.
      + erewrite <- external_call_stack_blocks. 2: eauto.
        eapply perm_stack_inv. eauto.
        apply Mem.in_frames_valid.
        eapply ec_perm_frames; eauto.
        apply external_call_spec.
      + erewrite <- external_call_stack_blocks. 2: eauto.
        eapply load_rsp_inv'. eauto.
        eapply Mem.unchanged_on_implies.
        eapply external_call_unchanged_on. eauto.
        intros; eapply link_offsets_not_public_stack_range; eauto.
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
        unfold Mem.valid_block in NV2. xomega.
      + etransitivity. apply GlobLe. eapply external_call_nextblock; eauto.
      + etransitivity. apply GlobLeT. eapply external_call_nextblock; eauto.
    -
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
      rewrite JB in H8; inv H8.
      do 3 eexists; split.
      eapply exec_step_external.
      eauto.
      eauto.
      eauto.
      generalize (RINJ RSP). destruct (rs RSP); simpl in *; inversion 1; subst; try congruence.
      destruct Tptr; try easy.
      destruct Tptr; try easy.
      destruct Tptr; try easy.
      destruct Tptr; try easy.
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
      + eapply Mem.mem_inject_ext; eauto.
        erewrite external_call_stack_blocks; eauto.
      +
        repeat rewrite Pregmap.gso by (congruence).
        rewrite set_pair_no_rsp.
        rewrite Asmgenproof0.undef_regs_other.
        rewrite Asmgenproof0.undef_regs_other.
        eauto.
        intros; intro; subst. rewrite in_map_iff in H5.
        destruct H5 as (x & EQ & IN).
        apply preg_of_not_rsp in EQ. congruence.
        intros; intro; subst. clear - H5; simpl in *; intuition congruence.
        auto.
      + intros; apply val_inject_set.
        intros; apply val_inject_set.
        intros; apply val_inject_set_pair; auto.
        apply val_inject_undef_regs; auto.
        apply val_inject_undef_regs; auto.
        intros; eapply val_inject_incr; eauto.
        intros; eapply val_inject_incr; eauto.
        auto.
      + eapply external_call_valid_block; eauto.
      + red. repeat rewrite Pregmap.gso by (congruence).
        rewrite set_pair_no_rsp.
        rewrite Asmgenproof0.undef_regs_other.
        rewrite Asmgenproof0.undef_regs_other.
        erewrite <- external_call_stack_blocks. eauto. eauto.
        intros; intro; subst. rewrite in_map_iff in H5.
        destruct H5 as (x & EQ & IN).
        apply preg_of_not_rsp in EQ. congruence.
        intros; intro; subst. clear - H5; simpl in *; intuition congruence.
        auto.
      + erewrite <- external_call_stack_blocks. 2: eauto.
        repeat rewrite Pregmap.gso by (congruence).
        rewrite set_pair_no_rsp.
        rewrite Asmgenproof0.undef_regs_other.
        rewrite Asmgenproof0.undef_regs_other.
        eauto.
        intros; intro; subst. rewrite in_map_iff in H5.
        destruct H5 as (x & EQ & IN).
        apply preg_of_not_rsp in EQ. congruence.
        intros; intro; subst. clear - H5; simpl in *; intuition congruence.
        auto.
      + erewrite <- external_call_stack_blocks; eauto.
      + erewrite <- external_call_stack_blocks; eauto.
      + red.
        repeat rewrite Pregmap.gso by (congruence).
        rewrite set_pair_no_rsp.
        rewrite Asmgenproof0.undef_regs_other.
        rewrite Asmgenproof0.undef_regs_other.
        eauto.
        intros; intro; subst. rewrite in_map_iff in H5.
        destruct H5 as (x & EQ & IN).
        apply preg_of_not_rsp in EQ. congruence.
        intros; intro; subst. clear - H5; simpl in *; intuition congruence.
        auto.
      + red.
        intros.
        eapply Mem.perm_max in H5.
        eapply external_call_max_perm in H5.
        2: eauto.
        eauto. eauto.
      + red.
        intros.
        eapply ec_perm_unchanged. eapply external_call_spec. eauto.
        eauto.
        intros. eapply PBS in H6. destruct H6.  intro A; inv A; inv H8.
        eauto.
      + red.
        erewrite <- external_call_stack_blocks. 2: eauto.
        eauto.
      + repeat rewrite Pregmap.gso by (congruence).
        rewrite set_pair_no_rsp.
        rewrite Asmgenproof0.undef_regs_other.
        rewrite Asmgenproof0.undef_regs_other.
        eauto.
        intros; intro; subst. rewrite in_map_iff in H5.
        destruct H5 as (x & EQ & IN).
        apply preg_of_not_rsp in EQ. congruence.
        intros; intro; subst. clear - H5; simpl in *; intuition congruence.
        auto.
      + red. intros b delta o k p JB1 PERM.
        erewrite <- external_call_stack_blocks. 2: eauto.
        destruct (j b) eqn:A. destruct p0.
        exploit INCR. eauto. eauto. intro JB2. rewrite JB1 in JB2; inv JB2.
        eapply NIB; eauto.
        eapply Mem.perm_max in PERM.
        eapply external_call_max_perm in PERM.
        2: eauto.
        eauto.
        eapply Mem.valid_block_inject_1; eauto.
        exploit SEP. eauto. eauto. intuition congruence.
      + erewrite <- external_call_stack_blocks. 2: eauto.
        eapply inject_stack_incr; eauto.
      +
        red.
        unfold get_frame_info.
        erewrite <- external_call_stack_blocks. 2: eauto.
        intros.
        exploit inj_incr_sep_same. eauto. eauto. apply H6. auto.
        exploit inj_incr_sep_same. eauto. eauto. apply H8. auto.
        intros.
        eapply IP; eauto.
        eapply Mem.perm_max in H9.
        eapply external_call_max_perm; eauto.
        eapply Mem.valid_block_inject_1 in H10; eauto.
      + erewrite <- external_call_stack_blocks. 2: eauto.
        eapply perm_stack_inv. eauto.
        apply Mem.in_frames_valid.
        eapply ec_perm_frames; eauto. apply external_call_spec.
      + erewrite <- external_call_stack_blocks. 2: eauto.
        eapply load_rsp_inv'. eauto.
        eapply Mem.unchanged_on_implies.
        eapply external_call_unchanged_on. eauto.
        intros; eapply link_offsets_not_public_stack_range; eauto.
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
        exploit INCR; eauto. rewrite H8; intro X; inv X.
        eauto.
        exploit SEP; eauto. intros (NV1 & NV2).
        simpl; unfold Genv.block_is_volatile.
        rewrite ! find_var_info_none_ge.
        auto.
        unfold Mem.valid_block in NV1. xomega.
        unfold Mem.valid_block in NV2.
        xomega.
      + etransitivity. apply GlobLe. eapply external_call_nextblock; eauto.
      + etransitivity. apply GlobLeT. eapply external_call_nextblock; eauto.
  Qed.

End PRESERVATION.


  Lemma match_initial_states s:
    Asm.initial_state prog s ->
    exists s' j ostack, match_states Vnullptr j ostack s s' /\
                        mono_initial_state prog s'.
  Proof.
    inversion 1. subst.
    destruct (Mem.alloc m0 0 Mem.stack_limit) as [m1 bstack0] eqn:ALLOC.
    assert (bstack = bstack0).
    {
      unfold bstack.
      unfold ge.
      exploit Mem.alloc_result; eauto.
      erewrite <- Genv.init_mem_genv_next; eauto.
    }
    subst.
    assert (ge = ge0).
    {
      unfold ge, ge0. auto.
    }
    subst ge0. clear H1.
    assert (bstack = Mem.nextblock m0) as stackeq.
    {
      exploit Mem.alloc_result; eauto.
    }
    edestruct (Mem.range_perm_drop_2).
    red; intros; eapply Mem.perm_alloc_2; eauto.
    exploit Mem.record_stack_blocks_intro. instantiate (1:= x).
    instantiate (1 := (bstack::nil,Some frame_info_mono, 0)).
    {
      red; simpl. unfold in_frame; simpl. intros. destruct H1 as [?|[]]; subst.
      eapply Mem.drop_perm_valid_block_1. eauto.
      eapply Mem.valid_new_block; eauto.
    }
    {
      constructor; auto.
      erewrite Mem.drop_perm_stack_adt; eauto.
      erewrite Mem.alloc_stack_blocks; eauto.
      erewrite Genv.init_mem_stack_adt; eauto.
    }
    {
      constructor; auto. simpl. intros. inv H2.
      eapply Mem.perm_drop_4 in H1. 2: eauto.
      simpl.
      eapply Mem.perm_alloc_3; eauto.
    }
    {
      simpl.
      erewrite Mem.drop_perm_stack_adt; eauto.
      erewrite Mem.alloc_stack_blocks; eauto.
      change (align (Z.max 0 0) 8) with 0.
      generalize (Mem.size_stack_below m0); omega.      
    }
    intros (m2 & RSB).
    do 2 eexists; exists (Ptrofs.unsigned Ptrofs.zero); split.
    2: econstructor; eauto.
    exploit Genv.initmem_inject; eauto.
    intro FLATINJ.
    exploit Mem.alloc_right_inject. apply FLATINJ.
    eauto. intro STACKINJ.
    exploit Mem.drop_outside_inject. apply STACKINJ. eauto.
    unfold Mem.flat_inj. intros b' delta ofs k p FB1 PERM RNG. destr_in FB1. inv FB1.
    exploit Mem.alloc_result; eauto. intro A; clear Heqs. rewrite A in p0.  xomega.
    intro STACKINJ'.
    exploit Mem.record_stack_block_right. 2: eauto. eauto.
    {
      erewrite Genv.init_mem_stack_adt; eauto. 
    }
    eauto.
    intro STACKINJ_FINAL.
    econstructor; eauto.
    - eapply Mem.mem_inject_ext. eauto.
      unfold flat_frameinj.
      intros.
      erewrite Genv.init_mem_stack_adt; eauto.
    - unfold rs0.
      rewrite Pregmap.gss. inversion 1.
    - unfold rs0.
      intros; apply val_inject_set; auto.
      intros; apply val_inject_set; auto.
      intros; apply val_inject_set; auto.
      + unfold Genv.symbol_address. destr; auto.
        econstructor. unfold Mem.flat_inj. rewrite pred_dec_true. eauto.
        erewrite <- Genv.init_mem_genv_next.
        eapply Genv.genv_symb_range; eauto. eauto. 
        reflexivity.
      + constructor.
      + constructor.
    - red.         
      rewrite stackeq. exploit Mem.nextblock_alloc; eauto.
      exploit Mem.nextblock_drop. eauto.
      exploit Mem.record_stack_block_nextblock; eauto.
      intros A B C; rewrite A, B, C; xomega.
    - red.
      unfold rs0.
      rewrite Pregmap.gss. inversion 1.
    - erewrite Genv.init_mem_stack_adt; eauto.
    - erewrite Genv.init_mem_stack_adt; eauto.
    - erewrite Genv.init_mem_stack_adt; eauto.
    - red. 
      unfold rs0.
      rewrite Pregmap.gss. inversion 1.
    - red. intros.
      assert (0 <= ofs < Mem.stack_limit).
      {
        eapply Mem.record_stack_block_perm in H1. 2: eauto.
        eapply Mem.perm_drop_4 in H1; eauto.
        eapply Mem.perm_alloc_3 in H1. 2: eauto. auto.
      }
      eapply Mem.record_stack_block_perm in H1. 2: eauto.
      exploit Mem.perm_drop_2; eauto. intros.
      split; auto. split. omega. eapply Z.lt_le_trans. apply H2. apply Mem.stack_limit_range.
    - red; intros.
      eapply Mem.record_stack_block_perm'. eauto.
      eapply Mem.perm_drop_1; eauto.
    - red.
      erewrite Mem.record_stack_blocks_stack_adt; eauto.
      erewrite Mem.drop_perm_stack_adt; eauto.
      erewrite Mem.alloc_stack_blocks; eauto.
      erewrite Genv.init_mem_stack_adt; eauto.
    - unfold rs0.
      rewrite Pregmap.gss. inversion 1.
    - red.
      unfold Mem.flat_inj.
      intros b delta o k p INJ PERM.
      destr_in INJ. inv INJ.
      exploit Mem.alloc_result; eauto. intro; subst. exfalso; clear - H1 p0. rewrite H1 in p0. xomega.
    -
      erewrite Genv.init_mem_stack_adt; eauto.
      constructor.
    - red. 
      erewrite Genv.init_mem_stack_adt; eauto.
      simpl. congruence.
    - erewrite Genv.init_mem_stack_adt; eauto. constructor.
    - erewrite Genv.init_mem_stack_adt; eauto. constructor.
    - intros. unfold Mem.flat_inj. rewrite pred_dec_true; auto.
      eapply Genv.find_funct_ptr_not_fresh; eauto.
    - intros. unfold Mem.flat_inj. rewrite pred_dec_true; auto.
      eapply Genv.find_def_not_fresh; eauto.
    - split.
      simpl; intros; unfold Mem.flat_inj.
      rewrite pred_dec_true; auto.
      eapply Genv.find_symbol_not_fresh; eauto.
      simpl; intros b1 b2 delta; unfold Mem.flat_inj.
      intro A; destr_in A.
    - erewrite <- Genv.init_mem_genv_next; eauto. unfold ge; apply Ple_refl.
    -
      erewrite Mem.record_stack_block_nextblock. 2: eauto.
      erewrite Mem.nextblock_drop; eauto. erewrite Mem.nextblock_alloc.
      erewrite <- Genv.init_mem_genv_next; eauto. unfold ge; xomega.
      eauto.
  Qed.

  Lemma transf_final_states:
    forall isp j o st1 st2 r,
      match_states isp j o st1 st2 -> Asm.final_state st1 r -> final_state st2 r.
  Proof.
    inversion 1; subst.
    inversion 1; subst.
    econstructor.
    generalize (RINJ PC). rewrite H3. unfold Vnullptr. destruct ptr64; inversion 1; auto.
    generalize (RINJ RAX). rewrite H5. unfold Vnullptr. destruct ptr64; inversion 1; auto.
  Qed.

  Theorem transf_program_correct:
    asm_prog_no_rsp ge ->
    forward_simulation (Asm.semantics prog) (mono_semantics prog).
  Proof.
    intro APNR.
    eapply forward_simulation_step.
    - simpl. reflexivity. 
    - instantiate (1:= fun s1 s2 => exists j o, match_states Vnullptr j o s1 s2).
      simpl. intros; exploit match_initial_states. eauto. intros (s' & j & ostack & MS & MIS); eexists; split; eauto.
    - simpl. intros s1 s2 r (j & o & MS) FS. eapply transf_final_states; eauto.
    - simpl. intros s1 t s1' STEP s2 (j & o & MS). 
      edestruct step_simulation as (isp' & j' & o' & STEP' & MS'); eauto.
      apply Val.Vnullptr_has_type.
  Qed.

End WITHMEMORYMODEL.