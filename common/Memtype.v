(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the GNU General Public License as published by  *)
(*  the Free Software Foundation, either version 2 of the License, or  *)
(*  (at your option) any later version.  This file is also distributed *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(** This file defines the interface for the memory model that
  is used in the dynamic semantics of all the languages used in the compiler.
  It defines a type [mem] of memory states, the following 4 basic
  operations over memory states, and their properties:
- [load]: read a memory chunk at a given address;
- [store]: store a memory chunk at a given address;
- [alloc]: allocate a fresh memory block;
- [free]: invalidate a memory block.
*)

Require Import Coqlib.
Require Intv.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import Memdata.
Require Import MemPerm.
Require Import StackADT.

Module Mem.

Definition locset := block -> Z -> Prop.

Close Scope nat_scope.

Parameter stack_limit': Z.
Definition stack_limit: Z := Z.max 8 ((align stack_limit' 8) mod (Ptrofs.modulus - align (size_chunk Mptr) 8)).

Lemma stack_limit_range: 0 <= stack_limit <= Ptrofs.max_unsigned.
Proof.
  unfold stack_limit.
  rewrite Zmax_spec. destr. vm_compute. intuition congruence.
  split. omega.
  eapply Z.lt_le_incl, Z.lt_le_trans. apply Z_mod_lt. unfold Mptr; destr; vm_compute; auto.
  unfold Ptrofs.max_unsigned. apply Z.sub_le_mono_l. unfold Mptr; destr; simpl; vm_compute; congruence.
Qed.

Lemma stack_limit_range': stack_limit + align (size_chunk Mptr) 8 <= Ptrofs.max_unsigned.
Proof.
  unfold stack_limit.
  rewrite Zmax_spec. destr. vm_compute. intuition congruence.
  generalize (Z_mod_lt (align stack_limit' 8) (Ptrofs.modulus - align (size_chunk Mptr) 8)).
  intro A; trim A. vm_compute. auto. unfold Ptrofs.max_unsigned. omega.
Qed.

Lemma stack_limit_pos: 0 < stack_limit.
Proof.
  unfold stack_limit.
  rewrite Zmax_spec. destr. omega. omega.
Qed.

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

Lemma stack_limit_aligned: (8 | stack_limit).
Proof.
  unfold stack_limit.
  rewrite Zmax_spec. destr. exists 1; omega.
  apply mod_divides. vm_compute. congruence.
  apply Z.divide_sub_r.
  rewrite Ptrofs.modulus_power.
  exists (two_p (Ptrofs.zwordsize - 3)). change 8 with (two_p 3). rewrite <- two_p_is_exp. f_equal. vm_compute. congruence. omega.
  apply align_divides. omega.
  apply align_divides. omega.
Qed.

Global Opaque stack_limit.

Class MemoryModelOps
      (** The abstract type of memory states. *)
 (mem: Type)

: Type
 :=
{

(** * Operations on memory states *)

(** [empty] is the initial memory state. *)
  empty: mem;

(** [alloc m lo hi] allocates a fresh block of size [hi - lo] bytes.
  Valid offsets in this block are between [lo] included and [hi] excluded.
  These offsets are writable in the returned memory state.
  This block is not initialized: its contents are initially undefined.
  Returns a pair [(m', b)] of the updated memory state [m'] and
  the identifier [b] of the newly-allocated block.
  Note that [alloc] never fails: we are modeling an infinite memory. *)
 alloc: forall (m: mem) (lo hi: Z), mem * block;

(** [free m b lo hi] frees (deallocates) the range of offsets from [lo]
  included to [hi] excluded in block [b].  Returns the updated memory
  state, or [None] if the freed addresses are not writable. *)
 free: forall (m: mem) (b: block) (lo hi: Z), option mem;

(** [load chunk m b ofs] reads a memory quantity [chunk] from
  addresses [b, ofs] to [b, ofs + size_chunk chunk - 1] in memory state
  [m].  Returns the value read, or [None] if the accessed addresses
  are not readable. *)
 load: forall (chunk: memory_chunk) (m: mem) (b: block) (ofs: Z), option val;

(** [store chunk m b ofs v] writes value [v] as memory quantity [chunk]
  from addresses [b, ofs] to [b, ofs + size_chunk chunk - 1] in memory state
  [m].  Returns the updated memory state, or [None] if the accessed addresses
  are not writable. *)
 store: forall (chunk: memory_chunk) (m: mem) (b: block) (ofs: Z) (v: val), option mem;

(** [loadbytes m b ofs n] reads and returns the byte-level representation of
  the values contained at offsets [ofs] to [ofs + n - 1] within block [b]
  in memory state [m].
  [None] is returned if the accessed addresses are not readable. *)
 loadbytes: forall (m: mem) (b: block) (ofs n: Z), option (list memval);

(** [storebytes m b ofs bytes] stores the given list of bytes [bytes]
  starting at location [(b, ofs)].  Returns updated memory state
  or [None] if the accessed locations are not writable. *)
 storebytes: forall (m: mem) (b: block) (ofs: Z) (bytes: list memval), option mem;

(** [drop_perm m b lo hi p] sets the permissions of the byte range
    [(b, lo) ... (b, hi - 1)] to [p].  These bytes must have [Freeable] permissions
    in the initial memory state [m].
    Returns updated memory state, or [None] if insufficient permissions. *)

 drop_perm: forall (m: mem) (b: block) (lo hi: Z) (p: permission), option mem;

(** * Permissions, block validity, access validity, and bounds *)

(** The next block of a memory state is the block identifier for the
  next allocation.  It increases by one at each allocation.
  Block identifiers below [nextblock] are said to be valid, meaning
  that they have been allocated previously.  Block identifiers above
  [nextblock] are fresh or invalid, i.e. not yet allocated.  Note that
  a block identifier remains valid after a [free] operation over this
  block. *)

 nextblock: mem -> block;

(** [perm m b ofs k p] holds if the address [b, ofs] in memory state [m]
  has permission [p]: one of freeable, writable, readable, and nonempty.
  If the address is empty, [perm m b ofs p] is false for all values of [p].
  [k] is the kind of permission we are interested in: either the current
  permissions or the maximal permissions. *)
 perm: forall (m: mem) (b: block) (ofs: Z) (k: perm_kind) (p: permission), Prop;

(** [range_perm m b lo hi p] holds iff the addresses [b, lo] to [b, hi-1]
  all have permission [p] of kind [k]. *)
 range_perm (m: mem) (b: block) (lo hi: Z) (k: perm_kind) (p: permission) : Prop :=
  forall ofs, lo <= ofs < hi -> perm m b ofs k p;

(** [valid_pointer m b ofs] returns [true] if the address [b, ofs]
  is nonempty in [m] and [false] if it is empty. *)

 valid_pointer: forall (m: mem) (b: block) (ofs: Z), bool;

(** * Relating two memory states. *)

(** ** Memory extensions *)

(**  A store [m2] extends a store [m1] if [m2] can be obtained from [m1]
  by relaxing the permissions of [m1] (for instance, allocating larger
  blocks) and replacing some of the [Vundef] values stored in [m1] by
  more defined values stored in [m2] at the same addresses. *)

 extends: forall {injperm: InjectPerm}, mem -> mem -> Prop;

(** The [magree] predicate is a variant of [extends] where we
  allow the contents of the two memory states to differ arbitrarily
  on some locations.  The predicate [P] is true on the locations whose
  contents must be in the [lessdef] relation.
  Needed by Deadcodeproof. *)

 magree: forall {injperm: InjectPerm} (m1 m2: mem) (P: locset), Prop;

(** ** Memory injections *)

(** A memory injection [f] is a function from addresses to either [None]
  or [Some] of an address and an offset.  It defines a correspondence
  between the blocks of two memory states [m1] and [m2]:
- if [f b = None], the block [b] of [m1] has no equivalent in [m2];
- if [f b = Some(b', ofs)], the block [b] of [m2] corresponds to
  a sub-block at offset [ofs] of the block [b'] in [m2].

A memory injection [f] defines a relation [Val.inject] between values
that is the identity for integer and float values, and relocates pointer
values as prescribed by [f].  (See module [Values].)

Likewise, a memory injection [f] defines a relation between memory states
that we now axiomatize. *)

 inject: forall {injperm: InjectPerm}, meminj -> frameinj -> mem -> mem -> Prop;

(** ** Weak Memory injections *)

 weak_inject: forall {injperm: InjectPerm}, meminj -> frameinj -> mem -> mem -> Prop;


(** Memory states that inject into themselves. *)

 inject_neutral: forall {injperm: InjectPerm} (thr: block) (m: mem), Prop;

(** ** Invariance properties between two memory states *)

 unchanged_on: forall (P: block -> Z -> Prop) (m_before m_after: mem), Prop
 ;

 (** Necessary to distinguish from [unchanged_on], used as
 postconditions to external function calls, whereas
 [strong_unchanged_on] will be used for ordinary memory operations. *)

 strong_unchanged_on: forall (P: block -> Z -> Prop) (m_before m_after: mem), Prop
 ;

 (* Stack ADT and methods *)
 stack: mem -> StackADT.stack;
 (* Pushes a new stage on the stack, with no frames in it. *)
 push_new_stage: mem -> mem;
 (* Marks the current active frame in the top stage as tailcalled. *)
 tailcall_stage: mem -> option mem;
 (* Records a [frame_adt] on the current top stage. *)
 record_stack_blocks: mem -> frame_adt -> option mem;
 (* Pops the topmost stage of the stack, if any. *)
 unrecord_stack_block: mem -> option mem;
}.


Section WITHMEMORYMODELOPS.
Context `{memory_model_ops: MemoryModelOps}.
Context {injperm: InjectPerm}.

(** [loadv] and [storev] are variants of [load] and [store] where
  the address being accessed is passed as a value (of the [Vptr] kind). *)

Definition loadv (chunk: memory_chunk) (m: mem) (addr: val) : option val :=
  match addr with
  | Vptr b ofs => load chunk m b (Ptrofs.unsigned ofs)
  | _ => None
  end.

Definition storev (chunk: memory_chunk) (m: mem) (addr v: val) : option mem :=
  match addr with
  | Vptr b ofs => store chunk m b (Ptrofs.unsigned ofs) v
  | _ => None
  end.

(** [free_list] frees all the given (block, lo, hi) triples. *)
Fixpoint free_list (m: mem) (l: list (block * Z * Z)) {struct l}: option mem :=
  match l with
  | nil => Some m
  | (b, lo, hi) :: l' =>
      match free m b lo hi with
      | None => None
      | Some m' => free_list m' l'
      end
  end.

Definition valid_block (m: mem) (b: block) := Plt b (nextblock m).

Definition valid_frame f m :=
  forall b, in_frame f b -> valid_block m b.

(** An access to a memory quantity [chunk] at address [b, ofs] with
  permission [p] is valid in [m] if the accessed addresses all have
  current permission [p] and moreover the offset is properly aligned. *)
Definition valid_access (m: mem) (chunk: memory_chunk) (b: block) (ofs: Z) (p: permission): Prop :=
  range_perm m b ofs (ofs + size_chunk chunk) Cur p
  /\ (align_chunk chunk | ofs)
  /\ (perm_order p Writable -> stack_access (stack m) b ofs (ofs + size_chunk chunk)).

(** C allows pointers one past the last element of an array.  These are not
  valid according to the previously defined [valid_pointer]. The property
  [weak_valid_pointer m b ofs] holds if address [b, ofs] is a valid pointer
  in [m], or a pointer one past a valid block in [m].  *)

Definition weak_valid_pointer (m: mem) (b: block) (ofs: Z) :=
  valid_pointer m b ofs || valid_pointer m b (ofs - 1).

(** Integrity of pointer values. *)

Definition compat_pointer_chunks (chunk1 chunk2: memory_chunk) : Prop :=
  match chunk1, chunk2 with
  | (Mint32 | Many32), (Mint32 | Many32) => True
  | (Mint64 | Many64), (Mint64 | Many64) => True
  | _, _ => False
  end.

Definition inj_offset_aligned (delta: Z) (size: Z) : Prop :=
  forall chunk, size_chunk chunk <= size -> (align_chunk chunk | delta).

Definition flat_inj (thr: block) : meminj :=
  fun (b: block) => if plt b thr then Some(b, 0) else None.

Definition meminj_no_overlap (f: meminj) (m: mem) : Prop :=
  forall b1 b1' delta1 b2 b2' delta2 ofs1 ofs2,
  b1 <> b2 ->
  f b1 = Some (b1', delta1) ->
  f b2 = Some (b2', delta2) ->
  perm m b1 ofs1 Max Nonempty ->
  perm m b2 ofs2 Max Nonempty ->
  b1' <> b2' \/ ofs1 + delta1 <> ofs2 + delta2.

Definition stack_unchanged (T: mem -> mem -> Prop) :=
  forall m1 m2, T m1 m2 -> stack m2 = stack m1.

Definition mem_unchanged (T: mem -> mem -> Prop) :=
  forall m1 m2, T m1 m2 ->
           nextblock m2 = nextblock m1
           /\ (forall b o k p, perm m2 b o k p <-> perm m1 b o k p)
           /\ (forall P, strong_unchanged_on P m1 m2)
           /\ (forall b o chunk, load chunk m2 b o = load chunk m1 b o).

(* Definition top_is_new (m:mem) := *)
(*   top_tframe_prop (fun tf => tf = (None,nil)) (stack m). *)

Lemma check_top_tc m : { top_tframe_tc (stack m) } + { ~ top_tframe_tc (stack m) }.
Proof.
  unfold top_tframe_tc.
  destruct (stack m) eqn:STK. right; intro A; inv A.
  destruct t.
  destruct o.
  right. intro A. inv A. inv H0.
  left; constructor. auto.
Defined.

Definition top_frame_no_perm m :=
  top_tframe_prop
    (fun tf : tframe_adt =>
     forall b : block,
     in_frames tf b -> forall (o : Z) (k : perm_kind) (p : permission), ~ Mem.perm m b o k p)
    (Mem.stack m).

Definition record_init_sp m :=
  let (m1, b1) := Mem.alloc (Mem.push_new_stage m) 0 0 in
  Mem.record_stack_blocks m1 (make_singleton_frame_adt b1 0 0).


End WITHMEMORYMODELOPS.

Class MemoryModel mem `{memory_model_ops: MemoryModelOps mem} 
  : Prop :=
{

 valid_not_valid_diff:
  forall m b b', valid_block m b -> ~(valid_block m b') -> b <> b';

(** Logical implications between permissions *)

 perm_implies:
  forall m b ofs k p1 p2, perm m b ofs k p1 -> perm_order p1 p2 -> perm m b ofs k p2;

(** The current permission is always less than or equal to the maximal permission. *)

 perm_cur_max:
  forall m b ofs p, perm m b ofs Cur p -> perm m b ofs Max p;
 perm_cur:
  forall m b ofs k p, perm m b ofs Cur p -> perm m b ofs k p;
 perm_max:
  forall m b ofs k p, perm m b ofs k p -> perm m b ofs Max p;

(** Having a (nonempty) permission implies that the block is valid.
  In other words, invalid blocks, not yet allocated, are all empty. *)
 perm_valid_block:
  forall m b ofs k p, perm m b ofs k p -> valid_block m b;

 range_perm_implies:
  forall m b lo hi k p1 p2,
  range_perm m b lo hi k p1 -> perm_order p1 p2 -> range_perm m b lo hi k p2;

 range_perm_cur:
  forall m b lo hi k p,
  range_perm m b lo hi Cur p -> range_perm m b lo hi k p;

 range_perm_max:
  forall m b lo hi k p,
  range_perm m b lo hi k p -> range_perm m b lo hi Max p;

 valid_access_implies:
  forall m chunk b ofs p1 p2,
  valid_access m chunk b ofs p1 -> perm_order p1 p2 ->
  valid_access m chunk b ofs p2;

 valid_access_valid_block:
  forall m chunk b ofs,
  valid_access m chunk b ofs Nonempty ->
  valid_block m b;

 valid_access_perm:
  forall m chunk b ofs k p,
  valid_access m chunk b ofs p ->
  perm m b ofs k p;

 valid_pointer_nonempty_perm:
  forall m b ofs,
  valid_pointer m b ofs = true <-> perm m b ofs Cur Nonempty;
 valid_pointer_valid_access:
  forall m b ofs,
  valid_pointer m b ofs = true <-> valid_access m Mint8unsigned b ofs Nonempty;

 weak_valid_pointer_spec:
  forall m b ofs,
  weak_valid_pointer m b ofs = true <->
    valid_pointer m b ofs = true \/ valid_pointer m b (ofs - 1) = true;
 valid_pointer_implies:
  forall m b ofs,
  valid_pointer m b ofs = true -> weak_valid_pointer m b ofs = true;

(** * Properties of the memory operations *)

(** ** Properties of the initial memory state. *)

 nextblock_empty: nextblock empty = 1%positive;
 perm_empty: forall b ofs k p, ~perm empty b ofs k p;
 valid_access_empty:
  forall chunk b ofs p, ~valid_access empty chunk b ofs p;

(** ** Properties of [load]. *)

(** A load succeeds if and only if the access is valid for reading *)
 valid_access_load:
  forall m chunk b ofs,
  valid_access m chunk b ofs Readable ->
  exists v, load chunk m b ofs = Some v;
 load_valid_access:
  forall m chunk b ofs v,
  load chunk m b ofs = Some v ->
  valid_access m chunk b ofs Readable;

(** The value returned by [load] belongs to the type of the memory quantity
  accessed: [Vundef], [Vint] or [Vptr] for an integer quantity,
  [Vundef] or [Vfloat] for a float quantity. *)
 load_type:
  forall m chunk b ofs v,
  load chunk m b ofs = Some v ->
  Val.has_type v (type_of_chunk chunk);

(** For a small integer or float type, the value returned by [load]
  is invariant under the corresponding cast. *)
 load_cast:
  forall m chunk b ofs v,
  load chunk m b ofs = Some v ->
  match chunk with
  | Mint8signed => v = Val.sign_ext 8 v
  | Mint8unsigned => v = Val.zero_ext 8 v
  | Mint16signed => v = Val.sign_ext 16 v
  | Mint16unsigned => v = Val.zero_ext 16 v
  | _ => True
  end;

 load_int8_signed_unsigned:
  forall m b ofs,
  load Mint8signed m b ofs = option_map (Val.sign_ext 8) (load Mint8unsigned m b ofs);

 load_int16_signed_unsigned:
  forall m b ofs,
  load Mint16signed m b ofs = option_map (Val.sign_ext 16) (load Mint16unsigned m b ofs);

 loadv_int64_split:
  forall m a v,
  loadv Mint64 m a = Some v -> Archi.ptr64 = false ->
  exists v1 v2,
     loadv Mint32 m a = Some (if Archi.big_endian then v1 else v2)
  /\ loadv  Mint32 m (Val.add a (Vint (Int.repr 4))) = Some (if Archi.big_endian then v2 else v1)
  /\ Val.lessdef v (Val.longofwords v1 v2);

(** ** Properties of [loadbytes]. *)

(** [loadbytes] succeeds if and only if we have read permissions on the accessed
    memory area. *)

 range_perm_loadbytes:
  forall m b ofs len,
  range_perm m b ofs (ofs + len) Cur Readable ->
  exists bytes, loadbytes m b ofs len = Some bytes;
 loadbytes_range_perm:
  forall m b ofs len bytes,
  loadbytes m b ofs len = Some bytes ->
  range_perm m b ofs (ofs + len) Cur Readable;

(** If [loadbytes] succeeds, the corresponding [load] succeeds and
  returns a value that is determined by the
  bytes read by [loadbytes]. *)
 loadbytes_load:
  forall chunk m b ofs bytes,
  loadbytes m b ofs (size_chunk chunk) = Some bytes ->
  (align_chunk chunk | ofs) ->
  load chunk m b ofs = Some(decode_val chunk bytes);

(** Conversely, if [load] returns a value, the corresponding
  [loadbytes] succeeds and returns a list of bytes which decodes into the
  result of [load]. *)
 load_loadbytes:
  forall chunk m b ofs v,
  load chunk m b ofs = Some v ->
  exists bytes, loadbytes m b ofs (size_chunk chunk) = Some bytes
             /\ v = decode_val chunk bytes;

(** [loadbytes] returns a list of length [n] (the number of bytes read). *)
 loadbytes_length:
  forall m b ofs n bytes,
  loadbytes m b ofs n = Some bytes ->
  length bytes = nat_of_Z n;

 loadbytes_empty:
  forall m b ofs n,
  n <= 0 -> loadbytes m b ofs n = Some nil;

(** Composing or decomposing [loadbytes] operations at adjacent addresses. *)
 loadbytes_concat:
  forall m b ofs n1 n2 bytes1 bytes2,
  loadbytes m b ofs n1 = Some bytes1 ->
  loadbytes m b (ofs + n1) n2 = Some bytes2 ->
  n1 >= 0 -> n2 >= 0 ->
  loadbytes m b ofs (n1 + n2) = Some(bytes1 ++ bytes2);
 loadbytes_split:
  forall m b ofs n1 n2 bytes,
  loadbytes m b ofs (n1 + n2) = Some bytes ->
  n1 >= 0 -> n2 >= 0 ->
  exists bytes1, exists bytes2,
     loadbytes m b ofs n1 = Some bytes1
  /\ loadbytes m b (ofs + n1) n2 = Some bytes2
  /\ bytes = bytes1 ++ bytes2;

(** ** Properties of [store]. *)

(** [store] preserves block validity, permissions, access validity, and bounds.
  Moreover, a [store] succeeds if and only if the corresponding access
  is valid for writing. *)

 nextblock_store:
  forall chunk m1 b ofs v m2, store chunk m1 b ofs v = Some m2 ->
  nextblock m2 = nextblock m1;
 store_valid_block_1:
  forall chunk m1 b ofs v m2, store chunk m1 b ofs v = Some m2 ->
  forall b', valid_block m1 b' -> valid_block m2 b';
 store_valid_block_2:
  forall chunk m1 b ofs v m2, store chunk m1 b ofs v = Some m2 ->
  forall b', valid_block m2 b' -> valid_block m1 b';

 perm_store_1:
  forall chunk m1 b ofs v m2, store chunk m1 b ofs v = Some m2 ->
  forall b' ofs' k p, perm m1 b' ofs' k p -> perm m2 b' ofs' k p;
 perm_store_2:
  forall chunk m1 b ofs v m2, store chunk m1 b ofs v = Some m2 ->
  forall b' ofs' k p, perm m2 b' ofs' k p -> perm m1 b' ofs' k p;

 valid_access_store':
  forall m1 chunk b ofs v,
  valid_access m1 chunk b ofs Writable ->
  exists m2: mem, store chunk m1 b ofs v = Some m2;
 store_valid_access_1:
  forall chunk m1 b ofs v m2, store chunk m1 b ofs v = Some m2 ->
  forall chunk' b' ofs' p,
  valid_access m1 chunk' b' ofs' p -> valid_access m2 chunk' b' ofs' p;
 store_valid_access_2:
  forall chunk m1 b ofs v m2, store chunk m1 b ofs v = Some m2 ->
  forall chunk' b' ofs' p,
  valid_access m2 chunk' b' ofs' p -> valid_access m1 chunk' b' ofs' p;
 store_valid_access_3:
  forall chunk m1 b ofs v m2, store chunk m1 b ofs v = Some m2 ->
  valid_access m1 chunk b ofs Writable;

(** Load-store properties. *)

 load_store_similar:
  forall chunk m1 b ofs v m2, store chunk m1 b ofs v = Some m2 ->
  forall chunk',
  size_chunk chunk' = size_chunk chunk ->
  align_chunk chunk' <= align_chunk chunk ->
  exists v', load chunk' m2 b ofs = Some v' /\ decode_encode_val v chunk chunk' v';
 load_store_similar_2:
  forall chunk m1 b ofs v m2, store chunk m1 b ofs v = Some m2 ->
  forall chunk',
  size_chunk chunk' = size_chunk chunk ->
  align_chunk chunk' <= align_chunk chunk ->
  type_of_chunk chunk' = type_of_chunk chunk ->
  load chunk' m2 b ofs = Some (Val.load_result chunk' v);

 load_store_same:
  forall chunk m1 b ofs v m2, store chunk m1 b ofs v = Some m2 ->
  load chunk m2 b ofs = Some (Val.load_result chunk v);

 load_store_other:
  forall chunk m1 b ofs v m2, store chunk m1 b ofs v = Some m2 ->
  forall chunk' b' ofs',
  b' <> b
  \/ ofs' + size_chunk chunk' <= ofs
  \/ ofs + size_chunk chunk <= ofs' ->
  load chunk' m2 b' ofs' = load chunk' m1 b' ofs';

 load_store_pointer_overlap:
  forall chunk m1 b ofs v_b v_o m2 chunk' ofs' v,
  store chunk m1 b ofs (Vptr v_b v_o) = Some m2 ->
  load chunk' m2 b ofs' = Some v ->
  ofs' <> ofs ->
  ofs' + size_chunk chunk' > ofs ->
  ofs + size_chunk chunk > ofs' ->
  v = Vundef;
 load_store_pointer_mismatch:
  forall chunk m1 b ofs v_b v_o m2 chunk' v,
  store chunk m1 b ofs (Vptr v_b v_o) = Some m2 ->
  load chunk' m2 b ofs = Some v ->
  ~compat_pointer_chunks chunk chunk' ->
  v = Vundef;
 load_pointer_store:
  forall chunk m1 b ofs v m2 chunk' b' ofs' v_b v_o,
  store chunk m1 b ofs v = Some m2 ->
  load chunk' m2 b' ofs' = Some(Vptr v_b v_o) ->
  (v = Vptr v_b v_o /\ compat_pointer_chunks chunk chunk' /\ b' = b /\ ofs' = ofs)
  \/ (b' <> b \/ ofs' + size_chunk chunk' <= ofs \/ ofs + size_chunk chunk <= ofs');

 store_same_ptr:
   forall m1 b o v m2,
     v <> Vundef ->
     Val.has_type v Tptr ->
     loadbytes m1 b o (size_chunk Mptr) = Some (encode_val Mptr v) ->
     store Mptr m1 b o v = Some m2 -> m1 = m2;

 
(** Load-store properties for [loadbytes]. *)

 loadbytes_store_same:
  forall chunk m1 b ofs v m2, store chunk m1 b ofs v = Some m2 ->
  loadbytes m2 b ofs (size_chunk chunk) = Some(encode_val chunk v);
 loadbytes_store_other:
  forall chunk m1 b ofs v m2, store chunk m1 b ofs v = Some m2 ->
  forall b' ofs' n,
  b' <> b \/ n <= 0 \/ ofs' + n <= ofs \/ ofs + size_chunk chunk <= ofs' ->
  loadbytes m2 b' ofs' n = loadbytes m1 b' ofs' n;

(** [store] is insensitive to the signedness or the high bits of
  small integer quantities. *)

 store_signed_unsigned_8:
  forall m b ofs v,
  store Mint8signed m b ofs v = store Mint8unsigned m b ofs v;
 store_signed_unsigned_16:
  forall m b ofs v,
  store Mint16signed m b ofs v = store Mint16unsigned m b ofs v;
 store_int8_zero_ext:
  forall m b ofs n,
  store Mint8unsigned m b ofs (Vint (Int.zero_ext 8 n)) =
  store Mint8unsigned m b ofs (Vint n);
 store_int8_sign_ext:
  forall m b ofs n,
  store Mint8signed m b ofs (Vint (Int.sign_ext 8 n)) =
  store Mint8signed m b ofs (Vint n);
 store_int16_zero_ext:
  forall m b ofs n,
  store Mint16unsigned m b ofs (Vint (Int.zero_ext 16 n)) =
  store Mint16unsigned m b ofs (Vint n);
 store_int16_sign_ext:
  forall m b ofs n,
  store Mint16signed m b ofs (Vint (Int.sign_ext 16 n)) =
  store Mint16signed m b ofs (Vint n);
 storev_int64_split:
  forall m a v m',
  storev Mint64 m a v = Some m' -> Archi.ptr64 = false ->
  exists m1,
     storev Mint32 m a (if Archi.big_endian then Val.hiword v else Val.loword v) = Some m1
  /\ storev Mint32 m1 (Val.add a (Vint (Int.repr 4))) (if Archi.big_endian then Val.loword v else Val.hiword v) = Some m';

(** ** Properties of [storebytes]. *)

(** [storebytes] preserves block validity, permissions, access validity, and bounds.
  Moreover, a [storebytes] succeeds if and only if we have write permissions
  on the addressed memory area. *)

 range_perm_storebytes' :
  forall m1 b ofs bytes,
    range_perm m1 b ofs (ofs + Z_of_nat (length bytes)) Cur Writable ->
    stack_access ( (stack m1)) b ofs (ofs + Z_of_nat (length bytes)) ->
  exists m2 : mem, storebytes m1 b ofs bytes = Some m2;
 storebytes_range_perm:
  forall m1 b ofs bytes m2, storebytes m1 b ofs bytes = Some m2 ->
                       range_perm m1 b ofs (ofs + Z_of_nat (length bytes)) Cur Writable;
 storebytes_stack_access:
  forall m1 b ofs bytes m2, storebytes m1 b ofs bytes = Some m2 ->
     stack_access ( (stack m1)) b ofs (ofs + Z_of_nat (length bytes)) ;
 perm_storebytes_1:
  forall m1 b ofs bytes m2, storebytes m1 b ofs bytes = Some m2 ->
  forall b' ofs' k p, perm m1 b' ofs' k p -> perm m2 b' ofs' k p;
 perm_storebytes_2:
  forall m1 b ofs bytes m2, storebytes m1 b ofs bytes = Some m2 ->
  forall b' ofs' k p, perm m2 b' ofs' k p -> perm m1 b' ofs' k p;
 storebytes_valid_access_1:
  forall m1 b ofs bytes m2, storebytes m1 b ofs bytes = Some m2 ->
  forall chunk' b' ofs' p,
  valid_access m1 chunk' b' ofs' p -> valid_access m2 chunk' b' ofs' p;
 storebytes_valid_access_2:
  forall m1 b ofs bytes m2, storebytes m1 b ofs bytes = Some m2 ->
  forall chunk' b' ofs' p,
  valid_access m2 chunk' b' ofs' p -> valid_access m1 chunk' b' ofs' p;
 nextblock_storebytes:
  forall m1 b ofs bytes m2, storebytes m1 b ofs bytes = Some m2 ->
  nextblock m2 = nextblock m1;
 storebytes_valid_block_1:
  forall m1 b ofs bytes m2, storebytes m1 b ofs bytes = Some m2 ->
  forall b', valid_block m1 b' -> valid_block m2 b';
 storebytes_valid_block_2:
  forall m1 b ofs bytes m2, storebytes m1 b ofs bytes = Some m2 ->
  forall b', valid_block m2 b' -> valid_block m1 b';

(** Connections between [store] and [storebytes]. *)

 storebytes_store:
  forall m1 b ofs chunk v m2,
  storebytes m1 b ofs (encode_val chunk v) = Some m2 ->
  (align_chunk chunk | ofs) ->
  store chunk m1 b ofs v = Some m2;

 store_storebytes:
  forall m1 b ofs chunk v m2,
  store chunk m1 b ofs v = Some m2 ->
  storebytes m1 b ofs (encode_val chunk v) = Some m2;

(** Load-store properties. *)

 loadbytes_storebytes_same:
  forall m1 b ofs bytes m2, storebytes m1 b ofs bytes = Some m2 ->
  loadbytes m2 b ofs (Z_of_nat (length bytes)) = Some bytes;
 loadbytes_storebytes_disjoint:
  forall m1 b ofs bytes m2, storebytes m1 b ofs bytes = Some m2 ->
  forall b' ofs' len,
  len >= 0 ->
  b' <> b \/ Intv.disjoint (ofs', ofs' + len) (ofs, ofs + Z_of_nat (length bytes)) ->
  loadbytes m2 b' ofs' len = loadbytes m1 b' ofs' len;
 loadbytes_storebytes_other:
  forall m1 b ofs bytes m2, storebytes m1 b ofs bytes = Some m2 ->
  forall b' ofs' len,
  len >= 0 ->
  b' <> b
  \/ ofs' + len <= ofs
  \/ ofs + Z_of_nat (length bytes) <= ofs' ->
  loadbytes m2 b' ofs' len = loadbytes m1 b' ofs' len;
 load_storebytes_other:
  forall m1 b ofs bytes m2, storebytes m1 b ofs bytes = Some m2 ->
  forall chunk b' ofs',
  b' <> b
  \/ ofs' + size_chunk chunk <= ofs
  \/ ofs + Z_of_nat (length bytes) <= ofs' ->
  load chunk m2 b' ofs' = load chunk m1 b' ofs';

(** Composing or decomposing [storebytes] operations at adjacent addresses. *)

 storebytes_concat:
  forall m b ofs bytes1 m1 bytes2 m2,
  storebytes m b ofs bytes1 = Some m1 ->
  storebytes m1 b (ofs + Z_of_nat(length bytes1)) bytes2 = Some m2 ->
  storebytes m b ofs (bytes1 ++ bytes2) = Some m2;
 storebytes_split:
  forall m b ofs bytes1 bytes2 m2,
  storebytes m b ofs (bytes1 ++ bytes2) = Some m2 ->
  exists m1,
     storebytes m b ofs bytes1 = Some m1
  /\ storebytes m1 b (ofs + Z_of_nat(length bytes1)) bytes2 = Some m2;

(** ** Properties of [alloc]. *)

(** The identifier of the freshly allocated block is the next block
  of the initial memory state. *)

 alloc_result:
  forall m1 lo hi m2 b, alloc m1 lo hi = (m2, b) ->
  b = nextblock m1;

(** Effect of [alloc] on block validity. *)

 nextblock_alloc:
  forall m1 lo hi m2 b, alloc m1 lo hi = (m2, b) ->
  nextblock m2 = Psucc (nextblock m1);

 valid_block_alloc:
  forall m1 lo hi m2 b, alloc m1 lo hi = (m2, b) ->
  forall b', valid_block m1 b' -> valid_block m2 b';
 fresh_block_alloc:
  forall m1 lo hi m2 b, alloc m1 lo hi = (m2, b) ->
  ~(valid_block m1 b);
 valid_new_block:
  forall m1 lo hi m2 b, alloc m1 lo hi = (m2, b) ->
  valid_block m2 b;
 valid_block_alloc_inv:
  forall m1 lo hi m2 b, alloc m1 lo hi = (m2, b) ->
  forall b', valid_block m2 b' -> b' = b \/ valid_block m1 b';

(** Effect of [alloc] on permissions. *)

 perm_alloc_1:
  forall m1 lo hi m2 b, alloc m1 lo hi = (m2, b) ->
  forall b' ofs k p, perm m1 b' ofs k p -> perm m2 b' ofs k p;
 perm_alloc_2:
  forall m1 lo hi m2 b, alloc m1 lo hi = (m2, b) ->
  forall ofs k, lo <= ofs < hi -> perm m2 b ofs k Freeable;
 perm_alloc_3:
  forall m1 lo hi m2 b, alloc m1 lo hi = (m2, b) ->
  forall ofs k p, perm m2 b ofs k p -> lo <= ofs < hi;
 perm_alloc_4:
  forall m1 lo hi m2 b, alloc m1 lo hi = (m2, b) ->
  forall b' ofs k p, perm m2 b' ofs k p -> b' <> b -> perm m1 b' ofs k p;
 perm_alloc_inv:
  forall m1 lo hi m2 b, alloc m1 lo hi = (m2, b) ->
  forall b' ofs k p,
  perm m2 b' ofs k p ->
  if eq_block b' b then lo <= ofs < hi else perm m1 b' ofs k p;

(** Effect of [alloc] on access validity. *)

 valid_access_alloc_other:
  forall m1 lo hi m2 b, alloc m1 lo hi = (m2, b) ->
  forall chunk b' ofs p,
  valid_access m1 chunk b' ofs p ->
  valid_access m2 chunk b' ofs p;
 valid_access_alloc_same:
  forall m1 lo hi m2 b, alloc m1 lo hi = (m2, b) ->
  forall chunk ofs,
  lo <= ofs -> ofs + size_chunk chunk <= hi -> (align_chunk chunk | ofs) ->
  valid_access m2 chunk b ofs Freeable;
 valid_access_alloc_inv:
  forall m1 lo hi m2 b, alloc m1 lo hi = (m2, b) ->
  forall chunk b' ofs p,
  valid_access m2 chunk b' ofs p ->
  if eq_block b' b
  then lo <= ofs /\ ofs + size_chunk chunk <= hi /\ (align_chunk chunk | ofs)
  else valid_access m1 chunk b' ofs p;

(** Load-alloc properties. *)

 load_alloc_unchanged:
  forall m1 lo hi m2 b, alloc m1 lo hi = (m2, b) ->
  forall chunk b' ofs,
  valid_block m1 b' ->
  load chunk m2 b' ofs = load chunk m1 b' ofs;
 load_alloc_other:
  forall m1 lo hi m2 b, alloc m1 lo hi = (m2, b) ->
  forall chunk b' ofs v,
  load chunk m1 b' ofs = Some v ->
  load chunk m2 b' ofs = Some v;
 load_alloc_same:
  forall m1 lo hi m2 b, alloc m1 lo hi = (m2, b) ->
  forall chunk ofs v,
  load chunk m2 b ofs = Some v ->
  v = Vundef;
 load_alloc_same':
  forall m1 lo hi m2 b, alloc m1 lo hi = (m2, b) ->
  forall chunk ofs,
  lo <= ofs -> ofs + size_chunk chunk <= hi -> (align_chunk chunk | ofs) ->
  load chunk m2 b ofs = Some Vundef;
 loadbytes_alloc_unchanged:
  forall m1 lo hi m2 b, alloc m1 lo hi = (m2, b) ->
  forall b' ofs n,
  valid_block m1 b' ->
  loadbytes m2 b' ofs n = loadbytes m1 b' ofs n;
 loadbytes_alloc_same:
  forall m1 lo hi m2 b, alloc m1 lo hi = (m2, b) ->
  forall n ofs bytes byte,
  loadbytes m2 b ofs n = Some bytes ->
  In byte bytes -> byte = Undef;

(** ** Properties of [free]. *)

(** [free] succeeds if and only if the correspond range of addresses
  has [Freeable] current permission. *)

 range_perm_free' :
  forall m1 b lo hi,
  range_perm m1 b lo hi Cur Freeable ->
  exists m2: mem, free m1 b lo hi = Some m2;
 free_range_perm:
  forall m1 bf lo hi m2, free m1 bf lo hi = Some m2 ->
                    range_perm m1 bf lo hi Cur Freeable;

(** Block validity is preserved by [free]. *)

 nextblock_free:
  forall m1 bf lo hi m2, free m1 bf lo hi = Some m2 ->
  nextblock m2 = nextblock m1;
 valid_block_free_1:
  forall m1 bf lo hi m2, free m1 bf lo hi = Some m2 ->
  forall b, valid_block m1 b -> valid_block m2 b;
 valid_block_free_2:
  forall m1 bf lo hi m2, free m1 bf lo hi = Some m2 ->
  forall b, valid_block m2 b -> valid_block m1 b;

(** Effect of [free] on permissions. *)

 perm_free_1:
  forall m1 bf lo hi m2, free m1 bf lo hi = Some m2 ->
  forall b ofs k p,
  b <> bf \/ ofs < lo \/ hi <= ofs ->
  perm m1 b ofs k p ->
  perm m2 b ofs k p;
 perm_free_2:
  forall m1 bf lo hi m2, free m1 bf lo hi = Some m2 ->
  forall ofs k p, lo <= ofs < hi -> ~ perm m2 bf ofs k p;
 perm_free_3:
  forall m1 bf lo hi m2, free m1 bf lo hi = Some m2 ->
  forall b ofs k p,
  perm m2 b ofs k p -> perm m1 b ofs k p;

(** Effect of [free] on access validity. *)

 valid_access_free_1:
  forall m1 bf lo hi m2, free m1 bf lo hi = Some m2 ->
  forall chunk b ofs p,
  valid_access m1 chunk b ofs p ->
  b <> bf \/ lo >= hi \/ ofs + size_chunk chunk <= lo \/ hi <= ofs ->
  valid_access m2 chunk b ofs p;
 valid_access_free_2:
  forall m1 bf lo hi m2, free m1 bf lo hi = Some m2 ->
  forall chunk ofs p,
  lo < hi -> ofs + size_chunk chunk > lo -> ofs < hi ->
  ~(valid_access m2 chunk bf ofs p);
 valid_access_free_inv_1:
  forall m1 bf lo hi m2, free m1 bf lo hi = Some m2 ->
  forall chunk b ofs p,
  valid_access m2 chunk b ofs p ->
  valid_access m1 chunk b ofs p;
 valid_access_free_inv_2:
  forall m1 bf lo hi m2, free m1 bf lo hi = Some m2 ->
  forall chunk ofs p,
  valid_access m2 chunk bf ofs p ->
  lo >= hi \/ ofs + size_chunk chunk <= lo \/ hi <= ofs;

(** Load-free properties *)

 load_free:
  forall m1 bf lo hi m2, free m1 bf lo hi = Some m2 ->
  forall chunk b ofs,
  b <> bf \/ lo >= hi \/ ofs + size_chunk chunk <= lo \/ hi <= ofs ->
  load chunk m2 b ofs = load chunk m1 b ofs;
 loadbytes_free_2:
  forall m1 bf lo hi m2, free m1 bf lo hi = Some m2 ->
  forall b ofs n bytes,
  loadbytes m2 b ofs n = Some bytes -> loadbytes m1 b ofs n = Some bytes;

(** ** Properties of [drop_perm]. *)

 nextblock_drop:
  forall m b lo hi p m', drop_perm m b lo hi p = Some m' ->
  nextblock m' = nextblock m;
 drop_perm_valid_block_1:
  forall m b lo hi p m', drop_perm m b lo hi p = Some m' ->
  forall b', valid_block m b' -> valid_block m' b';
 drop_perm_valid_block_2:
  forall m b lo hi p m', drop_perm m b lo hi p = Some m' ->
  forall b', valid_block m' b' -> valid_block m b';

 range_perm_drop_1:
  forall m b lo hi p m', drop_perm m b lo hi p = Some m' ->
  range_perm m b lo hi Cur Freeable;
 range_perm_drop_2' :
  forall m b lo hi p,
  range_perm m b lo hi Cur Freeable -> exists m', drop_perm m b lo hi p = Some m';

 perm_drop_1:
  forall m b lo hi p m', drop_perm m b lo hi p = Some m' ->
  forall ofs k, lo <= ofs < hi -> perm m' b ofs k p;
 perm_drop_2:
  forall m b lo hi p m', drop_perm m b lo hi p = Some m' ->
  forall ofs k p', lo <= ofs < hi -> perm m' b ofs k p' -> perm_order p p';
 perm_drop_3:
  forall m b lo hi p m', drop_perm m b lo hi p = Some m' ->
  forall b' ofs k p', b' <> b \/ ofs < lo \/ hi <= ofs -> perm m b' ofs k p' -> perm m' b' ofs k p';
 perm_drop_4:
  forall m b lo hi p m', drop_perm m b lo hi p = Some m' ->
  forall b' ofs k p', perm m' b' ofs k p' -> perm m b' ofs k p';

 loadbytes_drop:
  forall m b lo hi p m', drop_perm m b lo hi p = Some m' ->
  forall b' ofs n,
  b' <> b \/ ofs + n <= lo \/ hi <= ofs \/ perm_order p Readable ->
  loadbytes m' b' ofs n = loadbytes m b' ofs n;
 load_drop:
  forall m b lo hi p m', drop_perm m b lo hi p = Some m' ->
  forall chunk b' ofs,
  b' <> b \/ ofs + size_chunk chunk <= lo \/ hi <= ofs \/ perm_order p Readable ->
  load chunk m' b' ofs = load chunk m b' ofs;

(** ** Properties of [weak_inject]. *)
 empty_weak_inject {injperm: InjectPerm}: forall f m, 
  stack m = nil ->
  (forall b b' delta, f b = Some(b', delta) -> delta >= 0) ->
  (forall b b' delta, f b = Some(b', delta) -> valid_block m b') ->
  weak_inject f nil Mem.empty m;

 weak_inject_to_inject {injperm: InjectPerm}: forall f g m1 m2,
  weak_inject f g m1 m2 -> 
  (forall b p, f b = Some p -> valid_block m1 b) ->
  inject f g m1 m2;

 store_mapped_weak_inject {injperm: InjectPerm}:
  forall f g chunk m1 b1 ofs v1 n1 m2 b2 delta v2,
  weak_inject f g m1 m2 ->
  store chunk m1 b1 ofs v1 = Some n1 ->
  f b1 = Some (b2, delta) ->
  Val.inject f v1 v2 ->
  exists n2,
    store chunk m2 b2 (ofs + delta) v2 = Some n2
    /\ weak_inject f g n1 n2;

 alloc_left_mapped_weak_inject {injperm: InjectPerm}:
  forall f g m1 m2 lo hi m1' b1 b2 delta,
  f b1 = Some(b2, delta) ->
  weak_inject f g m1 m2 ->
  alloc m1 lo hi = (m1', b1) ->
  valid_block m2 b2 ->
  0 <= delta <= Ptrofs.max_unsigned ->
  (forall ofs k p, perm m2 b2 ofs k p -> delta = 0 \/ 0 <= ofs < Ptrofs.max_unsigned) ->
  (forall ofs k p, lo <= ofs < hi -> inject_perm_condition p -> perm m2 b2 (ofs + delta) k p) ->
  inj_offset_aligned delta (hi-lo) ->
  (forall b delta' ofs k p,
   f b = Some (b2, delta') ->
   perm m1 b ofs k p ->
   lo + delta <= ofs + delta' < hi + delta -> False) ->
  (forall fi,
      in_stack' (stack m2) (b2,fi) ->
      forall o k pp,
        perm m1' b1 o k pp ->
        inject_perm_condition pp ->
        frame_public fi (o + delta)) ->
  weak_inject f g m1' m2;

 alloc_left_unmapped_weak_inject {injperm: InjectPerm}:
  forall f g m1 m2 lo hi m1' b1,
  f b1 = None ->
  weak_inject f g m1 m2 ->
  alloc m1 lo hi = (m1', b1) ->
  weak_inject f g m1' m2;

 drop_parallel_weak_inject {InjectPerm: InjectPerm}:
  forall f g m1 m2 b1 b2 delta lo hi p m1',
  weak_inject f g m1 m2 ->
  inject_perm_condition Freeable ->
  drop_perm m1 b1 lo hi p = Some m1' ->
  f b1 = Some(b2, delta) ->
  exists m2',
      drop_perm m2 b2 (lo + delta) (hi + delta) p = Some m2'
   /\ weak_inject f g m1' m2';

 drop_extended_parallel_weak_inject {injperm: InjectPerm}:
  forall f g m1 m2 b1 b2 delta lo1 hi1 lo2 hi2 p m1',
  weak_inject f g m1 m2 ->
  inject_perm_condition Freeable ->
  drop_perm m1 b1 lo1 hi1 p = Some m1' ->
  f b1 = Some(b2, delta) ->
  lo2 <= lo1 -> hi1 <= hi2 ->
  range_perm m2 b2 (lo2 + delta) (hi2 + delta) Cur Freeable ->
  (* no source memory location with non-empty permision 
     injects into the following region in b2 in the target memory: 
     [lo2, lo1)
     and
     [hi1, hi2)
  *)
  (forall b' delta' ofs' k p,
    f b' = Some(b2, delta') ->
    perm m1 b' ofs' k p ->
    ((lo2 + delta <= ofs' + delta' < lo1 + delta )
     \/ (hi1 + delta <= ofs' + delta' < hi2 + delta)) -> False) ->
  exists m2',
      drop_perm m2 b2 (lo2 + delta) (hi2 + delta) p = Some m2'
   /\ weak_inject f g m1' m2';

(** ** Properties of [extends]. *)

 extends_refl {injperm: InjectPerm}:
  forall m, extends m m;

 load_extends {injperm: InjectPerm}:
  forall chunk m1 m2 b ofs v1,
  extends m1 m2 ->
  load chunk m1 b ofs = Some v1 ->
  exists v2, load chunk m2 b ofs = Some v2 /\ Val.lessdef v1 v2;

 loadv_extends {injperm: InjectPerm}:
  forall chunk m1 m2 addr1 addr2 v1,
  extends m1 m2 ->
  loadv chunk m1 addr1 = Some v1 ->
  Val.lessdef addr1 addr2 ->
  exists v2, loadv chunk m2 addr2 = Some v2 /\ Val.lessdef v1 v2;

 loadbytes_extends {injperm: InjectPerm}:
  forall m1 m2 b ofs len bytes1,
  extends m1 m2 ->
  loadbytes m1 b ofs len = Some bytes1 ->
  exists bytes2, loadbytes m2 b ofs len = Some bytes2
              /\ list_forall2 memval_lessdef bytes1 bytes2;

 store_within_extends {injperm: InjectPerm}:
  forall chunk m1 m2 b ofs v1 m1' v2,
  extends m1 m2 ->
  store chunk m1 b ofs v1 = Some m1' ->
  Val.lessdef v1 v2 ->
  exists m2',
     store chunk m2 b ofs v2 = Some m2'
  /\ extends m1' m2';

 store_outside_extends {injperm: InjectPerm}:
  forall chunk m1 m2 b ofs v m2',
  extends m1 m2 ->
  store chunk m2 b ofs v = Some m2' ->
  (forall ofs', perm m1 b ofs' Cur Readable -> ofs <= ofs' < ofs + size_chunk chunk -> False) ->
  extends m1 m2';

 storev_extends {injperm: InjectPerm}:
  forall chunk m1 m2 addr1 v1 m1' addr2 v2,
  extends m1 m2 ->
  storev chunk m1 addr1 v1 = Some m1' ->
  Val.lessdef addr1 addr2 ->
  Val.lessdef v1 v2 ->
  exists m2',
     storev chunk m2 addr2 v2 = Some m2'
  /\ extends m1' m2';

 storebytes_within_extends {injperm: InjectPerm}:
  forall m1 m2 b ofs bytes1 m1' bytes2,
  extends m1 m2 ->
  storebytes m1 b ofs bytes1 = Some m1' ->
  list_forall2 memval_lessdef bytes1 bytes2 ->
  exists m2',
     storebytes m2 b ofs bytes2 = Some m2'
  /\ extends m1' m2';

 storebytes_outside_extends {injperm: InjectPerm}:
  forall m1 m2 b ofs bytes2 m2',
  extends m1 m2 ->
  storebytes m2 b ofs bytes2 = Some m2' ->
  (forall ofs', perm m1 b ofs' Cur Readable -> ofs <= ofs' < ofs + Z_of_nat (length bytes2) -> False) ->
  extends m1 m2';

 alloc_extends {injperm: InjectPerm}:
  forall m1 m2 lo1 hi1 b m1' lo2 hi2,
  extends m1 m2 ->
  alloc m1 lo1 hi1 = (m1', b) ->
  lo2 <= lo1 -> hi1 <= hi2 ->
  exists m2',
     alloc m2 lo2 hi2 = (m2', b)
  /\ extends m1' m2';

 free_left_extends {injperm: InjectPerm}:
  forall m1 m2 b lo hi m1',
  extends m1 m2 ->
  free m1 b lo hi = Some m1' ->
  extends m1' m2;

 free_right_extends {injperm: InjectPerm}:
  forall m1 m2 b lo hi m2',
  extends m1 m2 ->
  free m2 b lo hi = Some m2' ->
  (forall ofs k p, perm m1 b ofs k p -> lo <= ofs < hi -> False) ->
  extends m1 m2';

 free_parallel_extends {injperm: InjectPerm}:
  forall m1 m2 b lo hi m1',
    extends m1 m2 ->
    inject_perm_condition Freeable ->
  free m1 b lo hi = Some m1' ->
  exists m2',
     free m2 b lo hi = Some m2'
  /\ extends m1' m2';

 valid_block_extends {injperm: InjectPerm}:
  forall m1 m2 b,
  extends m1 m2 ->
  (valid_block m1 b <-> valid_block m2 b);
 perm_extends {injperm: InjectPerm}:
  forall m1 m2 b ofs k p,
  extends m1 m2 -> perm m1 b ofs k p -> inject_perm_condition p -> perm m2 b ofs k p;
 valid_access_extends {injperm: InjectPerm}:
  forall m1 m2 chunk b ofs p,
    extends m1 m2 -> valid_access m1 chunk b ofs p -> inject_perm_condition p ->
    valid_access m2 chunk b ofs p;
 valid_pointer_extends {injperm: InjectPerm}:
  forall m1 m2 b ofs,
  extends m1 m2 -> valid_pointer m1 b ofs = true -> valid_pointer m2 b ofs = true;
 weak_valid_pointer_extends {injperm: InjectPerm}:
  forall m1 m2 b ofs,
  extends m1 m2 ->
  weak_valid_pointer m1 b ofs = true -> weak_valid_pointer m2 b ofs = true;

  
(** ** Properties of [magree]. *)
 ma_perm {injperm: InjectPerm}:
   forall m1 m2 (P: locset),
     magree m1 m2 P ->
     forall b ofs k p,
       perm m1 b ofs k p ->
       inject_perm_condition p ->
       perm m2 b ofs k p;

 magree_monotone {injperm: InjectPerm}:
  forall m1 m2 (P Q: locset),
  magree m1 m2 P ->
  (forall b ofs, Q b ofs -> P b ofs) ->
  magree m1 m2 Q;

 mextends_agree {injperm: InjectPerm}:
  forall m1 m2 P, extends m1 m2 -> magree m1 m2 P;

 magree_extends {injperm: InjectPerm}:
  forall m1 m2 (P: locset),
  (forall b ofs, P b ofs) ->
  magree m1 m2 P -> extends m1 m2;

 magree_loadbytes {injperm: InjectPerm}:
  forall m1 m2 P b ofs n bytes,
  magree m1 m2 P ->
  loadbytes m1 b ofs n = Some bytes ->
  (forall i, ofs <= i < ofs + n -> P b i) ->
  exists bytes', loadbytes m2 b ofs n = Some bytes' /\ list_forall2 memval_lessdef bytes bytes';

 magree_load {injperm: InjectPerm}:
  forall m1 m2 P chunk b ofs v,
  magree m1 m2 P ->
  load chunk m1 b ofs = Some v ->
  (forall i, ofs <= i < ofs + size_chunk chunk -> P b i) ->
  exists v', load chunk m2 b ofs = Some v' /\ Val.lessdef v v';

 magree_storebytes_parallel {injperm: InjectPerm}:
  forall m1 m2 (P Q: locset) b ofs bytes1 m1' bytes2,
  magree m1 m2 P ->
  storebytes m1 b ofs bytes1 = Some m1' ->
  (forall b' i, Q b' i ->
                b' <> b \/ i < ofs \/ ofs + Z_of_nat (length bytes1) <= i ->
                P b' i) ->
  list_forall2 memval_lessdef bytes1 bytes2 ->
  exists m2', storebytes m2 b ofs bytes2 = Some m2' /\ magree m1' m2' Q;

 magree_storebytes_left {injperm: InjectPerm}:
  forall m1 m2 P b ofs bytes1 m1',
  magree m1 m2 P ->
  storebytes m1 b ofs bytes1 = Some m1' ->
  (forall i, ofs <= i < ofs + Z_of_nat (length bytes1) -> ~(P b i)) ->
  magree m1' m2 P;

 magree_store_left {injperm: InjectPerm}:
  forall m1 m2 P chunk b ofs v1 m1',
  magree m1 m2 P ->
  store chunk m1 b ofs v1 = Some m1' ->
  (forall i, ofs <= i < ofs + size_chunk chunk -> ~(P b i)) ->
  magree m1' m2 P;

 magree_free {injperm: InjectPerm}:
  forall m1 m2 (P Q: locset) b lo hi m1',
    magree m1 m2 P ->
    inject_perm_condition Freeable ->
    free m1 b lo hi = Some m1' ->
    (forall b' i, Q b' i ->
             b' <> b \/ ~(lo <= i < hi) ->
             P b' i) ->
    exists m2', free m2 b lo hi = Some m2' /\ magree m1' m2' Q;

 magree_valid_access {injperm: InjectPerm}:
  forall m1 m2 (P: locset) chunk b ofs p,
  magree m1 m2 P ->
  valid_access m1 chunk b ofs p ->
  inject_perm_condition p ->
  valid_access m2 chunk b ofs p;

(** ** Properties of [inject]. *)
 mi_no_overlap {injperm: InjectPerm}:
   forall f g m1 m2,
   inject f g m1 m2 ->
   meminj_no_overlap f m1;

 mi_delta_pos {injperm: InjectPerm}:
   forall f g m1 m2 b1 b2 delta,
     inject f g m1 m2 ->
     f b1 = Some (b2, delta) ->
     delta >= 0;

 valid_block_inject_1 {injperm: InjectPerm}:
  forall f g m1 m2 b1 b2 delta,
  f b1 = Some(b2, delta) ->
  inject f g m1 m2 ->
  valid_block m1 b1;

 valid_block_inject_2 {injperm: InjectPerm}:
  forall f g m1 m2 b1 b2 delta,
  f b1 = Some(b2, delta) ->
  inject f g m1 m2 ->
  valid_block m2 b2;

 perm_inject {injperm: InjectPerm}:
  forall f g m1 m2 b1 b2 delta ofs k p,
  f b1 = Some(b2, delta) ->
  inject f g m1 m2 ->
  perm m1 b1 ofs k p ->
  inject_perm_condition p ->
  perm m2 b2 (ofs + delta) k p;

 range_perm_inject {injperm: InjectPerm}:
  forall f g m1 m2 b1 b2 delta lo hi k p,
  f b1 = Some(b2, delta) ->
  inject f g m1 m2 ->
  range_perm m1 b1 lo hi k p ->
  inject_perm_condition p ->
  range_perm m2 b2 (lo + delta) (hi + delta) k p;

 valid_access_inject {injperm: InjectPerm}:
  forall f g m1 m2 chunk b1 ofs b2 delta p,
  f b1 = Some(b2, delta) ->
  inject f g m1 m2 ->
  valid_access m1 chunk b1 ofs p ->
  inject_perm_condition p ->
  valid_access m2 chunk b2 (ofs + delta) p;

 valid_pointer_inject {injperm: InjectPerm}:
  forall f g m1 m2 b1 ofs b2 delta,
  f b1 = Some(b2, delta) ->
  inject f g m1 m2 ->
  valid_pointer m1 b1 ofs = true ->
  valid_pointer m2 b2 (ofs + delta) = true;

 valid_pointer_inject' {injperm: InjectPerm}: 
  forall f g m1 m2 b1 ofs b2 delta,
    f b1 = Some(b2, delta) ->
    inject f g m1 m2 ->
    valid_pointer m1 b1 (Ptrofs.unsigned ofs) = true ->
    valid_pointer m2 b2 (Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.repr delta))) = true;

 weak_valid_pointer_inject {injperm: InjectPerm}:
  forall f g m1 m2 b1 ofs b2 delta,
  f b1 = Some(b2, delta) ->
  inject f g m1 m2 ->
  weak_valid_pointer m1 b1 ofs = true ->
  weak_valid_pointer m2 b2 (ofs + delta) = true;

 weak_valid_pointer_inject' {injperm: InjectPerm}: 
  forall f g m1 m2 b1 ofs b2 delta,
  f b1 = Some(b2, delta) ->
  inject f g m1 m2 ->
  weak_valid_pointer m1 b1 (Ptrofs.unsigned ofs) = true ->
  weak_valid_pointer m2 b2 (Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.repr delta))) = true;

 address_inject {injperm: InjectPerm}:
  forall f g m1 m2 b1 ofs1 b2 delta p,
  inject f g m1 m2 ->
  perm m1 b1 (Ptrofs.unsigned ofs1) Cur p ->
  f b1 = Some (b2, delta) ->
  Ptrofs.unsigned (Ptrofs.add ofs1 (Ptrofs.repr delta)) = Ptrofs.unsigned ofs1 + delta;

 (** The following is needed by Separation, to prove storev_parallel_rule *)
 address_inject' {injperm: InjectPerm}:
  forall f g m1 m2 chunk b1 ofs1 b2 delta,
  inject f g m1 m2 ->
  valid_access m1 chunk b1 (Ptrofs.unsigned ofs1) Nonempty ->
  f b1 = Some (b2, delta) ->
  Ptrofs.unsigned (Ptrofs.add ofs1 (Ptrofs.repr delta)) = Ptrofs.unsigned ofs1 + delta;

 valid_pointer_inject_no_overflow {injperm: InjectPerm}:
  forall f g m1 m2 b ofs b' delta,
  inject f g m1 m2 ->
  valid_pointer m1 b (Ptrofs.unsigned ofs) = true ->
  f b = Some(b', delta) ->
  0 <= Ptrofs.unsigned ofs + Ptrofs.unsigned (Ptrofs.repr delta) <= Ptrofs.max_unsigned;

 weak_valid_pointer_inject_no_overflow {injperm: InjectPerm}:
  forall f g m1 m2 b ofs b' delta,
  inject f g m1 m2 ->
  weak_valid_pointer m1 b (Ptrofs.unsigned ofs) = true ->
  f b = Some(b', delta) ->
  0 <= Ptrofs.unsigned ofs + Ptrofs.unsigned (Ptrofs.repr delta) <= Ptrofs.max_unsigned;

 valid_pointer_inject_val {injperm: InjectPerm}:
  forall f g m1 m2 b ofs b' ofs',
  inject f g m1 m2 ->
  valid_pointer m1 b (Ptrofs.unsigned ofs) = true ->
  Val.inject f (Vptr b ofs) (Vptr b' ofs') ->
  valid_pointer m2 b' (Ptrofs.unsigned ofs') = true;

 weak_valid_pointer_inject_val {injperm: InjectPerm}:
  forall f g m1 m2 b ofs b' ofs',
  inject f g m1 m2 ->
  weak_valid_pointer m1 b (Ptrofs.unsigned ofs) = true ->
  Val.inject f (Vptr b ofs) (Vptr b' ofs') ->
  weak_valid_pointer m2 b' (Ptrofs.unsigned ofs') = true;

 inject_no_overlap {injperm: InjectPerm}:
  forall f g m1 m2 b1 b2 b1' b2' delta1 delta2 ofs1 ofs2,
  inject f g m1 m2 ->
  b1 <> b2 ->
  f b1 = Some (b1', delta1) ->
  f b2 = Some (b2', delta2) ->
  perm m1 b1 ofs1 Max Nonempty ->
  perm m1 b2 ofs2 Max Nonempty ->
  b1' <> b2' \/ ofs1 + delta1 <> ofs2 + delta2;

 different_pointers_inject {injperm: InjectPerm}:
  forall f g m m' b1 ofs1 b2 ofs2 b1' delta1 b2' delta2,
  inject f g m m' ->
  b1 <> b2 ->
  valid_pointer m b1 (Ptrofs.unsigned ofs1) = true ->
  valid_pointer m b2 (Ptrofs.unsigned ofs2) = true ->
  f b1 = Some (b1', delta1) ->
  f b2 = Some (b2', delta2) ->
  b1' <> b2' \/
  Ptrofs.unsigned (Ptrofs.add ofs1 (Ptrofs.repr delta1)) <>
  Ptrofs.unsigned (Ptrofs.add ofs2 (Ptrofs.repr delta2));

 disjoint_or_equal_inject {injperm: InjectPerm}:
  forall f g m m' b1 b1' delta1 b2 b2' delta2 ofs1 ofs2 sz,
  inject f g m m' ->
  f b1 = Some(b1', delta1) ->
  f b2 = Some(b2', delta2) ->
  range_perm m b1 ofs1 (ofs1 + sz) Max Nonempty ->
  range_perm m b2 ofs2 (ofs2 + sz) Max Nonempty ->
  sz > 0 ->
  b1 <> b2 \/ ofs1 = ofs2 \/ ofs1 + sz <= ofs2 \/ ofs2 + sz <= ofs1 ->
  b1' <> b2' \/ ofs1 + delta1 = ofs2 + delta2
             \/ ofs1 + delta1 + sz <= ofs2 + delta2
             \/ ofs2 + delta2 + sz <= ofs1 + delta1;

 aligned_area_inject {injperm: InjectPerm}:
  forall f g m m' b ofs al sz b' delta,
  inject f g m m' ->
  al = 1 \/ al = 2 \/ al = 4 \/ al = 8 -> sz > 0 ->
  (al | sz) ->
  range_perm m b ofs (ofs + sz) Cur Nonempty ->
  (al | ofs) ->
  f b = Some(b', delta) ->
  (al | ofs + delta);

 load_inject {injperm: InjectPerm}:
  forall f g m1 m2 chunk b1 ofs b2 delta v1,
  inject f g m1 m2 ->
  load chunk m1 b1 ofs = Some v1 ->
  f b1 = Some (b2, delta) ->
  exists v2, load chunk m2 b2 (ofs + delta) = Some v2 /\ Val.inject f v1 v2;

 loadv_inject {injperm: InjectPerm}:
  forall f g m1 m2 chunk a1 a2 v1,
  inject f g m1 m2 ->
  loadv chunk m1 a1 = Some v1 ->
  Val.inject f a1 a2 ->
  exists v2, loadv chunk m2 a2 = Some v2 /\ Val.inject f v1 v2;

 loadbytes_inject {injperm: InjectPerm}:
  forall f g m1 m2 b1 ofs len b2 delta bytes1,
  inject f g m1 m2 ->
  loadbytes m1 b1 ofs len = Some bytes1 ->
  f b1 = Some (b2, delta) ->
  exists bytes2, loadbytes m2 b2 (ofs + delta) len = Some bytes2
              /\ list_forall2 (memval_inject f) bytes1 bytes2;

 store_mapped_inject {injperm: InjectPerm}:
  forall f g chunk m1 b1 ofs v1 n1 m2 b2 delta v2,
  inject f g m1 m2 ->
  store chunk m1 b1 ofs v1 = Some n1 ->
  f b1 = Some (b2, delta) ->
  Val.inject f v1 v2 ->
  exists n2,
    store chunk m2 b2 (ofs + delta) v2 = Some n2
    /\ inject f g n1 n2;

 store_unmapped_inject {injperm: InjectPerm}:
  forall f g chunk m1 b1 ofs v1 n1 m2,
  inject f g m1 m2 ->
  store chunk m1 b1 ofs v1 = Some n1 ->
  f b1 = None ->
  inject f g n1 m2;

 store_outside_inject {injperm: InjectPerm}:
  forall f g m1 m2 chunk b ofs v m2',
  inject f g m1 m2 ->
  (forall b' delta ofs',
    f b' = Some(b, delta) ->
    perm m1 b' ofs' Cur Readable ->
    ofs <= ofs' + delta < ofs + size_chunk chunk -> False) ->
  store chunk m2 b ofs v = Some m2' ->
  inject f g m1 m2';

 store_right_inject {injperm: InjectPerm}:
  forall f g m1 m2 chunk b ofs v m2',
    inject f g m1 m2 ->
    (forall b' delta ofs',
        f b' = Some(b, delta) ->
        ofs' + delta = ofs ->
        exists vl, loadbytes m1 b' ofs' (size_chunk chunk) = Some vl /\
              list_forall2 (memval_inject f) vl (encode_val chunk v)) ->
    store chunk m2 b ofs v = Some m2' ->
    inject f g m1 m2';

 (* store_right_inject {injperm: InjectPerm}: *)
 (*  forall f g m1 m2 chunk b ofs v m2', *)
 (*    inject f g m1 m2 -> *)
 (*    (forall b' delta ofs', *)
 (*        f b' = Some(b, delta) -> *)
 (*        ofs' + delta = ofs -> *)
 (*        list_forall2 (memval_inject f) (getN (size_chunk_nat chunk) ofs' (PMap.get b' (m1.(mem_contents)))) (encode_val chunk v)) -> *)
 (*    store chunk m2 b ofs v = Some m2' -> *)
 (*    inject f g m1 m2'; *)

 storev_mapped_inject {injperm: InjectPerm}:
  forall f g chunk m1 a1 v1 n1 m2 a2 v2,
  inject f g m1 m2 ->
  storev chunk m1 a1 v1 = Some n1 ->
  Val.inject f a1 a2 ->
  Val.inject f v1 v2 ->
  exists n2,
    storev chunk m2 a2 v2 = Some n2 /\ inject f g n1 n2;

 storebytes_mapped_inject {injperm: InjectPerm}:
  forall f g m1 b1 ofs bytes1 n1 m2 b2 delta bytes2,
  inject f g m1 m2 ->
  storebytes m1 b1 ofs bytes1 = Some n1 ->
  f b1 = Some (b2, delta) ->
  list_forall2 (memval_inject f) bytes1 bytes2 ->
  exists n2,
    storebytes m2 b2 (ofs + delta) bytes2 = Some n2
    /\ inject f g n1 n2;

 storebytes_unmapped_inject {injperm: InjectPerm}:
  forall f g m1 b1 ofs bytes1 n1 m2,
  inject f g m1 m2 ->
  storebytes m1 b1 ofs bytes1 = Some n1 ->
  f b1 = None ->
  inject f g n1 m2;

 storebytes_outside_inject {injperm: InjectPerm}:
  forall f g m1 m2 b ofs bytes2 m2',
  inject f g m1 m2 ->
  (forall b' delta ofs',
    f b' = Some(b, delta) ->
    perm m1 b' ofs' Cur Readable ->
    ofs <= ofs' + delta < ofs + Z_of_nat (length bytes2) -> False) ->
  storebytes m2 b ofs bytes2 = Some m2' ->
  inject f g m1 m2';

 storebytes_empty_inject {injperm: InjectPerm}:
  forall f g m1 b1 ofs1 m1' m2 b2 ofs2 m2',
  inject f g m1 m2 ->
  storebytes m1 b1 ofs1 nil = Some m1' ->
  storebytes m2 b2 ofs2 nil = Some m2' ->
  inject f g m1' m2';

 alloc_right_inject {injperm: InjectPerm}:
  forall f g m1 m2 lo hi b2 m2',
  inject f g m1 m2 ->
  alloc m2 lo hi = (m2', b2) ->
  inject f g m1 m2';

 alloc_left_unmapped_inject {injperm: InjectPerm}:
  forall f g m1 m2 lo hi m1' b1,
  inject f g m1 m2 ->
  alloc m1 lo hi = (m1', b1) ->
  exists f',
     inject f' g m1' m2
  /\ inject_incr f f'
  /\ f' b1 = None
  /\ (forall b, b <> b1 -> f' b = f b);

 alloc_left_mapped_inject {injperm: InjectPerm}:
  forall f g m1 m2 lo hi m1' b1 b2 delta,
  inject f g m1 m2 ->
  alloc m1 lo hi = (m1', b1) ->
  valid_block m2 b2 ->
  0 <= delta <= Ptrofs.max_unsigned ->
  (forall ofs k p, perm m2 b2 ofs k p -> delta = 0 \/ 0 <= ofs < Ptrofs.max_unsigned) ->
  (forall ofs k p, lo <= ofs < hi -> inject_perm_condition p -> perm m2 b2 (ofs + delta) k p) ->
  inj_offset_aligned delta (hi-lo) ->
  (forall b delta' ofs k p,
   f b = Some (b2, delta') ->
   perm m1 b ofs k p ->
   lo + delta <= ofs + delta' < hi + delta -> False) ->
  (forall (fi : frame_info),
      in_stack' (stack m2) (b2,fi) ->
      forall (o : Z) (k : perm_kind) (pp : permission), perm m1' b1 o k pp -> inject_perm_condition pp -> frame_public fi (o + delta)) ->
  exists f',
     inject f' g m1' m2
  /\ inject_incr f f'
  /\ f' b1 = Some(b2, delta)
  /\ (forall b, b <> b1 -> f' b = f b);

 alloc_parallel_inject {injperm: InjectPerm}:
  forall f g m1 m2 lo1 hi1 m1' b1 lo2 hi2,
  inject f g m1 m2 ->
  alloc m1 lo1 hi1 = (m1', b1) ->
  lo2 <= lo1 -> hi1 <= hi2 ->
  exists f', exists m2', exists b2,
  alloc m2 lo2 hi2 = (m2', b2)
  /\ inject f' g m1' m2'
  /\ inject_incr f f'
  /\ f' b1 = Some(b2, 0)
  /\ (forall b, b <> b1 -> f' b = f b);

 free_inject {injperm: InjectPerm}:
  forall f g m1 l m1' m2 b lo hi m2',
  inject f g m1 m2 ->
  free_list m1 l = Some m1' ->
  free m2 b lo hi = Some m2' ->
  (forall b1 delta ofs k p,
    f b1 = Some(b, delta) -> perm m1 b1 ofs k p -> lo <= ofs + delta < hi ->
    exists lo1, exists hi1, In (b1, lo1, hi1) l /\ lo1 <= ofs < hi1) ->
  inject f g m1' m2';

 free_left_inject {injperm: InjectPerm}:
  forall f g m1 m2 b lo hi m1',
  inject f g m1 m2 ->
  free m1 b lo hi = Some m1' ->
  inject f g m1' m2;
 free_list_left_inject {injperm: InjectPerm}:
  forall f g m2 l m1 m1',
  inject f g m1 m2 ->
  free_list m1 l = Some m1' ->
  inject f g m1' m2;

 free_right_inject {injperm: InjectPerm}:
  forall f g m1 m2 b lo hi m2',
  inject f g m1 m2 ->
  free m2 b lo hi = Some m2' ->
  (forall b1 delta ofs k p,
    f b1 = Some(b, delta) -> perm m1 b1 ofs k p ->
    lo <= ofs + delta < hi -> False) ->
  inject f g m1 m2';

 free_parallel_inject {injperm: InjectPerm}:
  forall f g m1 m2 b lo hi m1' b' delta,
  inject f g m1 m2 ->
  free m1 b lo hi = Some m1' ->
  f b = Some(b', delta) ->
  inject_perm_condition Freeable ->
  exists m2',
     free m2 b' (lo + delta) (hi + delta) = Some m2'
  /\ inject f g m1' m2';

 drop_parallel_inject {InjectPerm: InjectPerm}:
  forall f g m1 m2 b1 b2 delta lo hi p m1',
  inject f g m1 m2 ->
  inject_perm_condition Freeable ->
  drop_perm m1 b1 lo hi p = Some m1' ->
  f b1 = Some(b2, delta) ->
  exists m2',
      drop_perm m2 b2 (lo + delta) (hi + delta) p = Some m2'
   /\ inject f g m1' m2';


 drop_extended_parallel_inject {InjectPerm: InjectPerm}:
  forall f g m1 m2 b1 b2 delta lo1 hi1 lo2 hi2 p m1',
  inject f g m1 m2 ->
  inject_perm_condition Freeable ->
  drop_perm m1 b1 lo1 hi1 p = Some m1' ->
  f b1 = Some(b2, delta) ->
  lo2 <= lo1 -> hi1 <= hi2 ->
  range_perm m2 b2 (lo2 + delta) (hi2 + delta) Cur Freeable ->
  (* no source memory location with non-empty permision 
     injects into the following region in b2 in the target memory: 
     [lo2, lo1)
     and
     [hi1, hi2)
  *)
  (forall b' delta' ofs' k p,
    f b' = Some(b2, delta') ->
    perm m1 b' ofs' k p ->
    ((lo2 + delta <= ofs' + delta' < lo1 + delta )
     \/ (hi1 + delta <= ofs' + delta' < hi2 + delta)) -> False) ->
  exists m2',
      drop_perm m2 b2 (lo2 + delta) (hi2 + delta) p = Some m2'
   /\ inject f g m1' m2';

 drop_outside_inject {injperm: InjectPerm}:
  forall f g m1 m2 b lo hi p m2',
    inject f g m1 m2 ->
    drop_perm m2 b lo hi p = Some m2' ->
  (forall b' delta ofs k p,
    f b' = Some(b, delta) ->
    perm m1 b' ofs k p -> lo <= ofs + delta < hi -> False) ->
  inject f g m1 m2';

 drop_right_inject {injperm: InjectPerm}: 
   forall f g m1 m2 b lo hi p m2',
     inject f g m1 m2 ->
     drop_perm m2 b lo hi p = Some m2' ->
     (forall b' delta ofs' k p',
         f b' = Some(b, delta) ->
         perm m1 b' ofs' k p' ->
         lo <= ofs' + delta < hi -> p' = p) ->
     inject f g m1 m2';


(** The following property is needed by ValueDomain, to prove mmatch_inj. *)

 self_inject f m {injperm: InjectPerm}:
  (forall b, f b = None \/ f b = Some (b, 0)) ->
  (forall b, f b <> None -> valid_block m b) ->
  (forall b,
     f b <> None ->
     forall o b' o' q n,
       loadbytes m b o 1 = Some (Fragment (Vptr b' o') q n :: nil) ->
       f b' <> None) ->
  inject f (flat_frameinj (length (stack m))) m m;

 inject_stack_inj_wf {injperm: InjectPerm}:
   forall f g m1 m2,
     inject f g m1 m2 ->
     sum_list g = length (stack m1) /\ length g = length (stack m2);

 (* Needed by Stackingproof, with Linear2 to Mach,
   to compose extends (in Linear2) and inject. *)
 extends_inject_compose {injperm: InjectPerm}:
   forall f g m1 m2 m3,
     extends m1 m2 -> inject f g m2 m3 -> inject f g m1 m3;

 extends_extends_compose {injperm: InjectPerm}:
   forall m1 m2 m3,
     extends m1 m2 -> extends m2 m3 -> extends m1 m3;


(** ** Properties of [inject_neutral] *)

 neutral_inject {injperm: InjectPerm}:
  forall m, inject_neutral (nextblock m) m ->
  inject (flat_inj (nextblock m)) (flat_frameinj (length (stack m))) m m;

 empty_inject_neutral {injperm: InjectPerm}:
  forall thr, inject_neutral thr empty;

 empty_stack {injperm: InjectPerm}:
   stack empty = nil;

 alloc_inject_neutral {injperm: InjectPerm}:
  forall thr m lo hi b m',
  alloc m lo hi = (m', b) ->
  inject_neutral thr m ->
  Plt (nextblock m) thr ->
  inject_neutral thr m';

 store_inject_neutral {injperm: InjectPerm}:
  forall chunk m b ofs v m' thr,
  store chunk m b ofs v = Some m' ->
  inject_neutral thr m ->
  Plt b thr ->
  Val.inject (flat_inj thr) v v ->
  inject_neutral thr m';

 drop_inject_neutral {injperm: InjectPerm}:
  forall m b lo hi p m' thr,
  drop_perm m b lo hi p = Some m' ->
  inject_neutral thr m ->
  Plt b thr ->
  inject_neutral thr m';
drop_perm_stack {injperm: InjectPerm}:
  forall m1 b lo hi p m1',
    drop_perm m1 b lo hi p = Some m1' ->
    stack m1' = stack m1;

(** ** Properties of [unchanged_on] and [strong_unchanged_on] *)

 strong_unchanged_on_weak P m1 m2:
  strong_unchanged_on P m1 m2 ->
  unchanged_on P m1 m2;
 unchanged_on_nextblock P m1 m2:
  unchanged_on P m1 m2 ->
  Ple (nextblock m1) (nextblock m2);
 strong_unchanged_on_refl:
  forall P m, strong_unchanged_on P m m;
 unchanged_on_trans:
  forall P m1 m2 m3, unchanged_on P m1 m2 -> unchanged_on P m2 m3 -> unchanged_on P m1 m3;
 strong_unchanged_on_trans:
  forall P m1 m2 m3, strong_unchanged_on P m1 m2 -> strong_unchanged_on P m2 m3 -> strong_unchanged_on P m1 m3;
 perm_unchanged_on:
  forall P m m' b ofs k p,
  unchanged_on P m m' -> P b ofs ->
  perm m b ofs k p -> perm m' b ofs k p;
 perm_unchanged_on_2:
  forall P m m' b ofs k p,
  unchanged_on P m m' -> P b ofs -> valid_block m b ->
  perm m' b ofs k p -> perm m b ofs k p;
 loadbytes_unchanged_on_1:
  forall P m m' b ofs n,
  unchanged_on P m m' ->
  valid_block m b ->
  (forall i, ofs <= i < ofs + n -> P b i) ->
  loadbytes m' b ofs n = loadbytes m b ofs n;
 loadbytes_unchanged_on:
   forall P m m' b ofs n bytes,
     unchanged_on P m m' ->
     (forall i, ofs <= i < ofs + n -> P b i) ->
     loadbytes m b ofs n = Some bytes ->
     loadbytes m' b ofs n = Some bytes;
 load_unchanged_on_1:
  forall P m m' chunk b ofs,
  unchanged_on P m m' ->
  valid_block m b ->
  (forall i, ofs <= i < ofs + size_chunk chunk -> P b i) ->
  load chunk m' b ofs = load chunk m b ofs;
 load_unchanged_on:
   forall P m m' chunk b ofs v,
     unchanged_on P m m' ->
     (forall i, ofs <= i < ofs + size_chunk chunk -> P b i) ->
     load chunk m b ofs = Some v ->
     load chunk m' b ofs = Some v;
 store_strong_unchanged_on:
  forall P chunk m b ofs v m',
    store chunk m b ofs v = Some m' ->
    (forall i, ofs <= i < ofs + size_chunk chunk -> ~ P b i) ->
    strong_unchanged_on P m m';
 storebytes_strong_unchanged_on:
  forall P m b ofs bytes m',
  storebytes m b ofs bytes = Some m' ->
  (forall i, ofs <= i < ofs + Z_of_nat (length bytes) -> ~ P b i) ->
  strong_unchanged_on P m m';
 alloc_strong_unchanged_on:
   forall P m lo hi m' b,
     alloc m lo hi = (m', b) ->
     strong_unchanged_on P m m';
 free_strong_unchanged_on:
  forall P m b lo hi m',
  free m b lo hi = Some m' ->
  (forall i, lo <= i < hi -> ~ P b i) ->
  strong_unchanged_on P m m';
 drop_perm_strong_unchanged_on:
   forall P m b lo hi p m',
     drop_perm m b lo hi p = Some m' ->
     (forall i, lo <= i < hi -> ~ P b i) ->
     strong_unchanged_on P m m';
 unchanged_on_implies:
   forall (P Q: block -> Z -> Prop) m m',
     unchanged_on P m m' ->
     (forall b ofs, Q b ofs -> valid_block m b -> P b ofs) ->
     unchanged_on Q m m'
 ;
 strong_unchanged_on_implies:
   forall (P Q: block -> Z -> Prop) m m',
     strong_unchanged_on P m m' ->
     (forall b ofs, Q b ofs -> valid_block m b -> P b ofs) ->
     strong_unchanged_on Q m m'
 ;

(** The following property is needed by Separation, to prove
minjection. HINT: it can be used only for [strong_unchanged_on], not
for [unchanged_on]. *)

 inject_strong_unchanged_on j g m0 m m'  {injperm: InjectPerm}:
   inject j g m0 m ->
   strong_unchanged_on
     (fun (b : block) (ofs : Z) =>
        exists (b0 : block) (delta : Z),
          j b0 = Some (b, delta) /\
          perm m0 b0 (ofs - delta) Max Nonempty) m m' ->
   stack m' = stack m ->
   inject j g m0 m';

 (* Original operations don't modify the stack. *)
 store_no_abstract:
   forall chunk b o v, stack_unchanged (fun m1 m2 => store chunk m1 b o v = Some m2);

 storebytes_no_abstract:
   forall b o bytes, stack_unchanged (fun m1 m2 => storebytes m1 b o bytes = Some m2);

 alloc_no_abstract:
   forall lo hi b, stack_unchanged (fun m1 m2 => alloc m1 lo hi = (m2, b));

 free_no_abstract:
   forall lo hi b, stack_unchanged (fun m1 m2 => free m1 b lo hi = Some m2);

 freelist_no_abstract:
   forall bl, stack_unchanged (fun m1 m2 => free_list m1 bl = Some m2);

 drop_perm_no_abstract:
   forall b lo hi p, stack_unchanged (fun m1 m2 => drop_perm m1 b lo hi p = Some m2);

 (* Properties of [record_stack_block] *)

 record_stack_blocks_inject_left' {injperm: InjectPerm}:
   forall m1 m1' m2 j g f1 f2
     (INJ: inject j g m1 m2)
     (FAP2: frame_at_pos (stack m2) 0 f2)
     (FI: tframe_inject j (perm m1) (Some f1, nil) f2)
     (RSB: record_stack_blocks m1 f1 = Some m1'),
     inject j g m1' m2;

 record_stack_blocks_inject_parallel {injperm: InjectPerm}:
   forall m1 m1' m2 j g fi1 fi2,
     inject j g m1 m2 ->
     frame_inject j fi1 fi2 ->
     (forall b : block, in_stack (stack m2) b -> ~ in_frame fi2 b) ->
     (valid_frame fi2 m2) ->
     frame_agree_perms (perm m2) fi2 ->
     (forall (b1 b2 : block) (delta : Z), j b1 = Some (b2, delta) -> in_frame fi1 b1 <-> in_frame fi2 b2) ->
     frame_adt_size fi1 = frame_adt_size fi2 ->
     record_stack_blocks m1 fi1 = Some m1' ->
     top_tframe_tc (stack m2) ->
     size_stack (tl (stack m2)) <= size_stack (tl (stack m1)) ->
     exists m2',
       record_stack_blocks m2 fi2 = Some m2' /\
       inject j g m1' m2';

 record_stack_blocks_extends {injperm: InjectPerm}:
    forall m1 m2 m1' fi,
      extends m1 m2 ->
      record_stack_blocks m1 fi = Some m1' ->
      (forall b, in_frame fi b -> ~ in_stack ( (stack m2)) b ) ->
      frame_agree_perms (perm m2) fi ->
      top_tframe_tc (stack m2) ->
      size_stack (tl (stack m2)) <= size_stack (tl (stack m1)) ->
      exists m2',
        record_stack_blocks m2 fi = Some m2' /\
        extends m1' m2';

 record_stack_blocks_mem_unchanged:
   forall bfi,
     mem_unchanged (fun m1 m2 => record_stack_blocks m1 bfi = Some m2);

 record_stack_blocks_stack:
   forall m fi m' f s,
     record_stack_blocks m fi = Some m' ->
     stack m = f::s ->
     stack m' = (Some fi , snd f) :: s;

 record_stack_blocks_inject_neutral {injperm: InjectPerm}:
   forall thr m fi m',
     inject_neutral thr m ->
     record_stack_blocks m fi = Some m' ->
     Forall (fun b => Plt b thr) (map fst (frame_adt_blocks fi)) ->
     inject_neutral thr m';

 (* Properties of unrecord_stack_block *)

 unrecord_stack_block_inject_parallel {injperm: InjectPerm}:
   forall (m1 m1' m2 : mem) (j : meminj) g,
     inject j (1%nat :: g) m1 m2 ->
     unrecord_stack_block m1 = Some m1' ->
     exists m2',
       unrecord_stack_block m2 = Some m2' /\ inject j g m1' m2';

 unrecord_stack_block_inject_left {injperm: InjectPerm}:
   forall (m1 m1' m2 : mem) (j : meminj) n g,
     inject j (S n :: g) m1 m2 ->
     unrecord_stack_block m1 = Some m1' ->
     (1 <= n)%nat ->
     top_frame_no_perm m1 ->
     inject j (n :: g) m1' m2;

 unrecord_stack_block_extends {injperm: InjectPerm}:
   forall m1 m2 m1',
     extends m1 m2 ->
     unrecord_stack_block m1 = Some m1' ->
     exists m2',
       unrecord_stack_block m2 = Some m2' /\
       extends m1' m2';

 unrecord_stack_block_mem_unchanged:
   mem_unchanged (fun m1 m2 => unrecord_stack_block m1 = Some m2);

 unrecord_stack:
   forall m m',
     unrecord_stack_block m = Some m' ->
     exists b,
       stack m = b :: stack m';

 unrecord_stack_block_succeeds:
   forall m b r,
     stack m = b :: r ->
     exists m',
       unrecord_stack_block m = Some m'
       /\ stack m' = r;

 unrecord_stack_block_inject_neutral {injperm: InjectPerm}:
   forall thr m m',
     inject_neutral thr m ->
     unrecord_stack_block m = Some m' ->
     inject_neutral thr m';


 (* Other properties *)

 public_stack_access_extends {injperm: InjectPerm}:
   forall m1 m2 b lo hi p,
     extends m1 m2 ->
     range_perm m1 b lo hi Cur p ->
     inject_perm_condition p ->
     public_stack_access ( (stack m1)) b lo hi ->
     public_stack_access ( (stack m2)) b lo hi;

 public_stack_access_inject {injperm: InjectPerm}:
   forall f g m1 m2 b b' delta lo hi p,
     f b = Some (b', delta) ->
     inject f g m1 m2 ->
     range_perm m1 b lo hi Cur p ->
     inject_perm_condition p ->
     public_stack_access ( (stack m1)) b lo hi ->
     public_stack_access ( (stack m2)) b' (lo + delta) (hi + delta);

 public_stack_access_magree {injperm: InjectPerm}: forall P (m1 m2 : mem) (b : block) (lo hi : Z) p,
     magree m1 m2 P ->
     range_perm m1 b lo hi Cur p ->
     inject_perm_condition p ->
     public_stack_access ( (stack m1)) b lo hi ->
     public_stack_access ( (stack m2)) b lo hi;

 in_frames_valid:
   forall m b,
     in_stack ( (stack m)) b -> valid_block m b;

 is_stack_top_extends {injperm: InjectPerm}:
   forall m1 m2 b
     (MINJ: extends m1 m2)
     (PERM: exists (o : Z) (k : perm_kind) (p : permission),
         perm m1 b o k p /\ inject_perm_condition p)
     (IST: is_stack_top ( (stack m1)) b),
     is_stack_top ( (stack m2)) b ;

 is_stack_top_inject {injperm: InjectPerm}:
   forall f g m1 m2 b1 b2 delta
     (MINJ: inject f g m1 m2)
     (FB: f b1 = Some (b2, delta))
     (PERM: exists (o : Z) (k : perm_kind) (p : permission),
         perm m1 b1 o k p /\ inject_perm_condition p)
     (IST: is_stack_top ( (stack m1)) b1),
     is_stack_top ( (stack m2)) b2 ;

 size_stack_below:
   forall m, size_stack (stack m) < stack_limit;
 
 record_stack_block_inject_left_zero {injperm: InjectPerm}:
    forall m1 m1' m2 j g f1 f2
      (INJ: inject j g m1 m2)
      (FAP2: frame_at_pos (stack m2) O f2)
      (FI: tframe_inject j (perm m1) (Some f1,nil) f2)
      (RSB: record_stack_blocks m1 f1 = Some m1'),
      inject j g m1' m2;

 unrecord_stack_block_inject_left_zero {injperm: InjectPerm}:
    forall (m1 m1' m2 : mem) (j : meminj) n g,
      inject j (S n :: g) m1 m2 ->
      unrecord_stack_block m1 = Some m1' ->
      top_frame_no_perm m1 ->
      (1 <= n)%nat ->
      inject j (n :: g) m1' m2;

 stack_norepet:
   forall m, nodup (stack m);
 
 inject_ext {injperm: InjectPerm}:
    forall j1 j2 g m1 m2,
      inject j1 g m1 m2 ->
      (forall x, j1 x = j2 x) ->
      inject j2 g m1 m2;

record_stack_block_inject_flat {injperm: InjectPerm}:
   forall m1 m1' m2 j  f1 f2
     (INJ: inject j (flat_frameinj (length (stack m1))) m1 m2)
     (FI: frame_inject j f1 f2)
     (NOIN: forall b, in_stack (stack m2) b -> ~ in_frame f2 b)
     (VF: valid_frame f2 m2)
     (BOUNDS: frame_agree_perms (perm m2) f2)
     (EQINF: forall (b1 b2 : block) (delta : Z), j b1 = Some (b2, delta) -> in_frame f1 b1 <-> in_frame f2 b2)
     (EQsz: frame_adt_size f1 = frame_adt_size f2)
     (RSB: record_stack_blocks m1 f1 = Some m1')
     (TNF: top_tframe_tc (stack m2))
     (SZ: size_stack (tl (stack m2)) <= size_stack (tl (stack m1))),
     exists m2',
       record_stack_blocks m2 f2 = Some m2' /\
       inject j (flat_frameinj (length (stack m1'))) m1' m2';

unrecord_stack_block_inject_parallel_flat {injperm: InjectPerm}:
  forall (m1 m1' m2 : mem) (j : meminj),
    inject j (flat_frameinj (length (stack m1))) m1 m2 ->
    unrecord_stack_block m1 = Some m1' ->
    exists m2',
      unrecord_stack_block m2 = Some m2' /\
      inject j (flat_frameinj (length (stack m1'))) m1' m2';

record_stack_blocks_tailcall_original_stack:
  forall m1 f1 m2,
    record_stack_blocks m1 f1 = Some m2 ->
    exists f r,
      stack m1 = (None,f)::r;

push_new_stage_nextblock: forall m, nextblock (push_new_stage m) = nextblock m;
 push_new_stage_load: forall chunk m b o, load chunk (push_new_stage m) b o = load chunk m b o;

 push_new_stage_inject  {injperm: InjectPerm}:
   forall j g m1 m2,
        inject j g m1 m2 ->
        inject j (1%nat :: g) (push_new_stage m1) (push_new_stage m2);

 inject_push_new_stage_left {injperm: InjectPerm}:
   forall j n g m1 m2,
     inject j (n::g) m1 m2 ->
     inject j (S n :: g) (push_new_stage m1) m2;

 inject_push_new_stage_right {injperm: InjectPerm}:
   forall j n g m1 m2,
     inject j (S n :: g) m1 m2 ->
     top_tframe_tc (stack m1) ->
     (O < n)%nat ->
     inject j (1%nat :: n :: g) m1 (push_new_stage m2);

 push_new_stage_length_stack:
      forall m,
        length (stack (push_new_stage m)) = S (length (stack m));

 push_new_stage_stack:
      forall m,
        stack (push_new_stage m) = (None, nil) :: stack m;

 push_new_stage_perm:
      forall m b o k p,
        perm (push_new_stage m) b o k p <-> perm m b o k p;

 wf_stack_mem:
   forall m,
     wf_stack (Mem.perm m) (Mem.stack m);

 agree_perms_mem:
  forall m,
    stack_agree_perms (Mem.perm m) (Mem.stack m);

 record_stack_blocks_top_tframe_no_perm:
   forall m1 f m2,
     Mem.record_stack_blocks m1 f = Some m2 ->
    top_tframe_tc (Mem.stack m1);

 extends_push {injperm: InjectPerm}:
   forall m1 m2,
     Mem.extends m1 m2 ->
     Mem.extends (Mem.push_new_stage m1) (Mem.push_new_stage m2);
 
 push_new_stage_unchanged_on:
   forall P m,
     Mem.strong_unchanged_on P m (Mem.push_new_stage m);

 tailcall_stage_unchanged_on:
   forall P m1 m2,
     Mem.tailcall_stage m1 = Some m2 ->
     Mem.strong_unchanged_on P m1 m2;
 
 unrecord_push:
   forall m, Mem.unrecord_stack_block (Mem.push_new_stage m) = Some m;

 push_storebytes_unrecord:
   forall m b o bytes m1 m2,
     storebytes m b o bytes = Some m1 ->
     storebytes (push_new_stage m) b o bytes = Some m2 ->
     unrecord_stack_block m2 = Some m1;

 push_store_unrecord:
   forall m b o chunk v m1 m2,
     store chunk m b o v = Some m1 ->
     store chunk (push_new_stage m) b o v = Some m2 ->
     unrecord_stack_block m2 = Some m1;
 
 magree_push {injperm:InjectPerm}:
      forall P m1 m2,
        magree m1 m2 P ->
        magree (Mem.push_new_stage m1) (Mem.push_new_stage m2) P;
 magree_unrecord {injperm:InjectPerm}:
    forall m1 m2 P,
      magree m1 m2 P ->
      forall m1',
        Mem.unrecord_stack_block m1 = Some m1' ->
        exists m2',
          Mem.unrecord_stack_block m2 = Some m2' /\ magree m1' m2' P;

 magree_tailcall_stage {injperm:InjectPerm}:
      forall P m1 m2 m1',
        magree m1 m2 P ->
        tailcall_stage m1 = Some m1' ->
        top_frame_no_perm m2 ->
        exists m2', tailcall_stage m2 = Some m2' /\ magree m1' m2' P;

 
 loadbytes_push:
   forall m b o n,
     Mem.loadbytes (Mem.push_new_stage m) b o n = Mem.loadbytes m b o n;

 (* store_unchanged_on_1: *)
 (*    forall chunk m m' b ofs v m1 *)
 (*      (UNCH: Mem.unchanged_on (fun _ _ => True) m m') *)
 (*      (SH: same_head (perm m) (Mem.stack m) (Mem.stack m') \/ ~ in_stack (Mem.stack m') b) *)
 (*      (STORE: Mem.store chunk m b ofs v = Some m1), *)
 (*    exists m1', *)
 (*      Mem.store chunk m' b ofs v = Some m1' /\ Mem.unchanged_on (fun _ _ => True) m1 m1'; *)

 (* storebytes_unchanged_on_1: *)
 (*    forall m m' b ofs v m1 *)
 (*      (UNCH: Mem.unchanged_on (fun _ _ => True) m m') *)
 (*      (SH: same_head (perm m) (Mem.stack m) (Mem.stack m') \/ ~ in_stack (Mem.stack m') b) *)
 (*      (STORE: Mem.storebytes m b ofs v = Some m1), *)
 (*    exists m1', *)
 (*      Mem.storebytes m' b ofs v = Some m1' /\ Mem.unchanged_on (fun _ _ => True) m1 m1'; *)
 
 (* valid_pointer_unchanged: *)
 (*  forall m1 m2, *)
 (*    Mem.unchanged_on (fun _ _ => True) m1 m2 -> *)
 (*    Mem.nextblock m1 = Mem.nextblock m2 -> *)
 (*    Mem.valid_pointer m1 = Mem.valid_pointer m2; *)

 (* push_new_stage_strong_unchanged_on: *)
 (*    forall m1 m2 P, *)
 (*      Mem.unchanged_on P m1 m2 -> *)
 (*      Mem.unchanged_on P (Mem.push_new_stage m1) (Mem.push_new_stage m2); *)

 (* unchanged_on_free: *)
 (*    forall m1 m2, *)
 (*      Mem.unchanged_on (fun _ _ => True) m1 m2 -> *)
 (*      forall b lo hi m1', *)
 (*        Mem.free m1 b lo hi = Some m1' -> *)
 (*        exists m2', *)
 (*          Mem.free m2 b lo hi = Some m2' /\ Mem.unchanged_on (fun _ _ => True) m1' m2'; *)

 (* unchanged_on_unrecord: *)
 (*    forall m1 m2, *)
 (*      Mem.unchanged_on (fun _ _ => True) m1 m2 -> *)
 (*      length (stack m1) = length (stack m2) -> *)
 (*      forall m1', *)
 (*        Mem.unrecord_stack_block m1 = Some m1' -> *)
 (*        exists m2', *)
 (*          Mem.unrecord_stack_block m2 = Some m2' /\ Mem.unchanged_on (fun _ _ => True) m1' m2'; *)

 (* unchanged_on_record: *)
 (*    forall m1 m2, *)
 (*      Mem.unchanged_on (fun _ _ => True) m1 m2 -> *)
 (*      nextblock m1 = nextblock m2 -> *)
 (*      same_head (perm m1) ((stack m1)) ((stack m2)) -> *)
 (*      forall m1' fi, *)
 (*        Mem.record_stack_blocks m1 fi = Some m1' -> *)
 (*        exists m2', *)
 (*          Mem.record_stack_blocks m2 fi = Some m2' /\ Mem.unchanged_on (fun _ _ => True) m1' m2'; *)

 (* unrecord_push_unchanged: *)
 (*    forall m1 m2 m2', *)
 (*      Mem.unchanged_on (fun _ _ => True) m1 m2 -> *)
 (*      Mem.unrecord_stack_block m2 = Some m2' -> *)
 (*      Mem.unchanged_on (fun _ _ => True) m1 (Mem.push_new_stage m2'); *)

 (* unchanged_on_alloc: *)
 (*   forall m1 m2 (UNCH: Mem.unchanged_on (fun _ _ => True) m1 m2) *)
 (*     lo hi m1' b (ALLOC1: Mem.alloc m1 lo hi = (m1', b)) *)
 (*     m2' (ALLOC2: Mem.alloc m2 lo hi = (m2', b)), *)
 (*     Mem.unchanged_on (fun _ _ => True) m1' m2'; *)

 (* inject_unchanged_compose {injperm: InjectPerm}: *)
 (*   forall f g m1 m2 m3, *)
 (*     inject f g m1 m2 -> *)
 (*     unchanged_on (fun _ _ => True) m2 m3 -> *)
 (*     same_head (perm m2) (Mem.stack m2) (Mem.stack m3) -> *)
 (*     inject f g m1 m3; *)

 (* extends_unchanged_compose {injperm: InjectPerm}: forall (m1 m2 m3 : mem), *)
 (*       Mem.extends m1 m2 -> *)
 (*       Mem.unchanged_on (fun (_ : Values.block) (_ : Z) => True) m2 m3 -> *)
 (*       Mem.nextblock m2 = Mem.nextblock m3 -> *)
 (*       same_head (Mem.perm m2) (Mem.stack m2) (Mem.stack m3) -> Mem.extends m1 m3; *)

 tailcall_stage_tc:
  forall m1 m2,
    Mem.tailcall_stage m1 = Some m2 ->
    top_tframe_tc (Mem.stack m2);

 tailcall_stage_perm:
   forall m1 m2,
     Mem.tailcall_stage m1 = Some m2 ->
     forall b o k p,
       Mem.perm m2 b o k p <-> Mem.perm m1 b o k p;
 
 tailcall_stage_tl_stack:
  forall m1 m2,
    Mem.tailcall_stage m1 = Some m2 ->
    tl (Mem.stack m2) = tl (Mem.stack m1);

 tailcall_stage_extends {injperm: InjectPerm}:
   forall m1 m2 m1',
     Mem.extends m1 m2 ->
     Mem.tailcall_stage m1 = Some m1' ->
     Mem.top_frame_no_perm m2 ->
     exists m2',
       Mem.tailcall_stage m2 = Some m2' /\ Mem.extends m1' m2';


 tailcall_stage_inject {injperm: InjectPerm}:
  forall j g m1 m2 m1',
    Mem.inject j g m1 m2 ->
    Mem.tailcall_stage m1 = Some m1' ->
    top_frame_no_perm m2 ->
    exists m2',
      Mem.tailcall_stage m2 = Some m2' /\ Mem.inject j g m1' m2';

 tailcall_stage_stack_equiv:
  forall m1 m2 m1' m2',
    Mem.tailcall_stage m1 = Some m1' ->
    Mem.tailcall_stage m2 = Some m2' ->
    stack_equiv (Mem.stack m1) (Mem.stack m2) ->
    stack_equiv (Mem.stack m1') (Mem.stack m2');

 tailcall_stage_same_length_pos:
    forall m1 m2,
      Mem.tailcall_stage m1 = Some m2 ->
      length (Mem.stack m2) = length (Mem.stack m1) /\ lt O (length (Mem.stack m1));


 tailcall_stage_nextblock:
    forall m1 m2,
      Mem.tailcall_stage m1 = Some m2 ->
      Mem.nextblock m2 = Mem.nextblock m1;


 inject_new_stage_left_tailcall_right {injperm: InjectPerm}:
    forall j n g m1 m2,
      Mem.inject j (n :: g) m1 m2 ->
      (forall l, take ( n) (stack m1) = Some l ->
          Forall (fun tf => forall b, in_frames tf b -> forall o k p, ~ perm m1 b o k p) l) ->
      top_frame_no_perm m2 ->
      exists m2',
        Mem.tailcall_stage m2 = Some m2' /\
        Mem.inject j (S n :: g) (Mem.push_new_stage m1) m2';

 inject_tailcall_left_new_stage_right {injperm:InjectPerm}:
   forall (j : meminj) (n : nat) (g : list nat) (m1 m2 m1' : mem),
     Mem.inject j (S n :: g) m1 m2 ->
     lt O n ->
     tailcall_stage m1 = Some m1' ->
     Mem.inject j (1%nat:: n :: g) m1' (Mem.push_new_stage m2);

 tailcall_stage_inject_left {injperm: InjectPerm}:
  forall j n g m1 m2 m1',
    Mem.inject j (n :: g) m1 m2 ->
    Mem.tailcall_stage m1 = Some m1' ->
    Mem.inject j (n::g) m1' m2;

 tailcall_stage_right_extends {injperm: InjectPerm}:
        forall m1 m2 (EXT: Mem.extends m1 m2)
          (TFNP1: Mem.top_frame_no_perm m1)
          (TFNP2: Mem.top_frame_no_perm m2),
        exists m2', Mem.tailcall_stage m2 = Some m2' /\ Mem.extends m1 m2';
      
 
 tailcall_stage_stack:
    forall m1 m2,
      Mem.tailcall_stage m1 = Some m2 ->
      exists f r,
        Mem.stack m1 = f :: r /\ Mem.stack m2 = (None, opt_cons (fst f) (snd f))::r;

}.

Section WITHMEMORYMODEL.

Context `{memory_model_prf: MemoryModel}.

Lemma stack_top_valid:
  forall m b, is_stack_top (stack m) b -> valid_block m b.
Proof.
  intros. rewrite is_stack_top_stack_blocks in H.
  decompose [ex and] H.
  eapply in_frames_valid. rewrite H2, in_stack_cons; auto.
Qed.

Lemma get_frame_info_valid:
  forall m b f, get_frame_info (stack m) b = Some f -> valid_block m b.
Proof.
  intros. eapply in_frames_valid. eapply get_frame_info_in_stack; eauto.
Qed.

Lemma invalid_block_stack_access:
  forall m b lo hi,
    ~ valid_block m b ->
    stack_access (stack m) b lo hi.
Proof.
  right.
  red.
  rewrite not_in_stack_get_assoc. auto.
  intro IN; apply in_frames_valid in IN; congruence.
Qed.

Lemma store_get_frame_info:
  forall chunk m1 b o v m2 (STORE: store chunk m1 b o v = Some m2),
  forall b', get_frame_info (stack m2) b' = get_frame_info (stack m1) b'.
Proof.
  intros. 
  erewrite store_no_abstract; eauto.
Qed.

Lemma store_stack_blocks:
  forall m1 sp chunk o v m2,
    store chunk m1 sp o v = Some m2 ->
    stack m2 = stack m1.
Proof.
  intros. 
  eapply store_no_abstract; eauto.
Qed.

Lemma store_is_stack_top:
   forall chunk m1 b o v m2 (STORE: store chunk m1 b o v = Some m2),
   forall b', is_stack_top (stack m2) b' <-> is_stack_top (stack m1) b'.
Proof.
  intros; erewrite store_no_abstract; eauto. tauto.
Qed.

Lemma storebytes_get_frame_info:
   forall m1 b o v m2 (STOREBYTES: storebytes m1 b o v = Some m2),
   forall b', get_frame_info (stack m2) b' = get_frame_info (stack m1) b'.
Proof.
  intros; erewrite storebytes_no_abstract; eauto.
Qed.

Lemma storebytes_is_stack_top:
  forall m1 b o v m2 (STOREBYTES: storebytes m1 b o v = Some m2),
  forall b', is_stack_top (stack m2) b' <-> is_stack_top (stack m1) b'.
Proof.
  intros; erewrite storebytes_no_abstract; eauto. tauto.
Qed.

Lemma alloc_get_frame_info:
  forall m1 lo hi m2 b (ALLOC: alloc m1 lo hi = (m2, b)),
  forall b', get_frame_info (stack m2) b' = get_frame_info (stack m1) b'.
Proof.
  intros; erewrite alloc_no_abstract; eauto.
Qed.

Lemma alloc_is_stack_top:
  forall m1 lo hi m2 b (ALLOC: alloc m1 lo hi = (m2, b)),
  forall b', is_stack_top (stack m2) b' <-> is_stack_top (stack m1) b'.
Proof.
  intros; erewrite alloc_no_abstract; eauto. tauto.
Qed.

Lemma alloc_get_frame_info_fresh:
  forall m1 lo hi m2 b (ALLOC: alloc m1 lo hi = (m2, b)),
    get_frame_info (stack m2) b = None.
Proof.
  intros; eapply not_in_stack_get_assoc; auto.
  rewrite alloc_no_abstract; eauto.
  intro IN; apply in_frames_valid in IN.
  eapply fresh_block_alloc in IN; eauto.
Qed.

Lemma alloc_stack_blocks:
  forall m1 lo hi m2 b,
    alloc m1 lo hi = (m2, b) ->
    stack m2 = stack m1.
Proof. intros; eapply alloc_no_abstract; eauto. Qed.

Lemma free_stack_blocks:
  forall m1 b lo hi m2,
    free m1 b lo hi = Some m2 ->
    stack m2 = stack m1.
Proof. intros; eapply free_no_abstract; eauto. Qed.

Lemma free_get_frame_info:
  forall m1 b lo hi m2 b',
    free m1 b lo hi = Some m2 ->
    get_frame_info (stack m2) b' = get_frame_info (stack m1) b'.
Proof.
  intros; erewrite free_no_abstract; eauto.
Qed.

Lemma storebytes_stack_blocks:
  forall m1 b o bytes m2,
    storebytes m1 b o bytes = Some m2 ->
    stack m2 = stack m1.
Proof.
  intros; eapply storebytes_no_abstract; eauto.
Qed.

Lemma free_list_stack_blocks:
  forall m bl m',
    free_list m bl = Some m' ->
    stack m' = stack m.
Proof.
  intros; eapply freelist_no_abstract; eauto.
Qed.

Lemma record_stack_block_unchanged_on:
  forall m bfi m' (P: block -> Z -> Prop),
    record_stack_blocks m bfi = Some m' ->
    strong_unchanged_on P m m'.
Proof.
  intros; eapply record_stack_blocks_mem_unchanged; eauto.
Qed.

Lemma record_stack_block_perm:
  forall m bfi m',
    record_stack_blocks m bfi = Some m' ->
    forall b' o k p,
      perm m' b' o k p ->
      perm m b' o k p.
Proof.
  intros. eapply record_stack_blocks_mem_unchanged in H; eauto.
  apply H; eauto.
Qed.

Lemma record_stack_block_perm'
  : forall m m' bofi,
    record_stack_blocks m bofi = Some m' ->
    forall (b' : block) (o : Z) (k : perm_kind) (p : permission),
      perm m b' o k p -> perm m' b' o k p.
Proof.
  intros. eapply record_stack_blocks_mem_unchanged in H; eauto.
  apply H; eauto.
Qed.

Lemma record_stack_block_valid:
  forall m bf m',
    record_stack_blocks m bf = Some m' ->
    forall b', valid_block m b' -> valid_block m' b'.
Proof.
  unfold valid_block; intros.
  eapply record_stack_blocks_mem_unchanged in H; eauto.
  destruct H. rewrite H. auto.
Qed.

Lemma record_stack_block_nextblock:
  forall m bf m',
    record_stack_blocks m bf = Some m' ->
    nextblock m' = nextblock m.
Proof.
  intros.
  eapply record_stack_blocks_mem_unchanged in H; eauto.
  intuition.
Qed.

Lemma record_stack_block_is_stack_top:
  forall m b fi m',
    record_stack_blocks m fi = Some m' ->
    in_frame fi b ->
    is_stack_top (stack m') b.
Proof.
  unfold is_stack_top, get_stack_top_blocks.
  intros.
  edestruct (record_stack_blocks_tailcall_original_stack _ _ _ H) as (f & r & EQ).
  erewrite record_stack_blocks_stack; eauto.
  unfold get_frames_blocks. simpl. auto.
Qed.

Lemma unrecord_stack_block_unchanged_on:
  forall m m' P,
    unrecord_stack_block m = Some m' ->
    strong_unchanged_on P m m'.
Proof.
  intros. eapply unrecord_stack_block_mem_unchanged in H; eauto.
  intuition.
Qed.

Lemma unrecord_stack_block_perm:
   forall m m',
     unrecord_stack_block m = Some m' ->
     forall b' o k p,
       perm m' b' o k p ->
       perm m b' o k p.
Proof.
  intros. eapply unrecord_stack_block_mem_unchanged in H; eauto.
  intuition. apply H; auto.
Qed.

Lemma unrecord_stack_block_perm'
     : forall m m' : mem,
       unrecord_stack_block m = Some m' ->
       forall (b' : block) (o : Z) (k : perm_kind) (p : permission),
       perm m b' o k p -> perm m' b' o k p.
Proof.
  intros. eapply unrecord_stack_block_mem_unchanged in H; eauto.
  intuition. apply H; auto.
Qed.

Lemma unrecord_stack_block_nextblock:
  forall m m',
    unrecord_stack_block m = Some m' ->
    nextblock m' = nextblock m.
Proof.
  intros. eapply unrecord_stack_block_mem_unchanged in H; eauto.
  intuition.
Qed.

Lemma unrecord_stack_block_get_frame_info:
   forall m m' b,
     unrecord_stack_block m = Some m' ->
     ~ is_stack_top (stack m) b ->
     get_frame_info (stack m') b = get_frame_info (stack m) b.
Proof.
  unfold is_stack_top, get_stack_top_blocks, get_frame_info. intros.
  exploit unrecord_stack. eauto. intros (b0 & EQ).
  rewrite EQ in *. simpl.
  destr.
Qed.

Lemma valid_access_store:
  forall m1 chunk b ofs v,
  valid_access m1 chunk b ofs Writable ->
  { m2: mem | store chunk m1 b ofs v = Some m2 }.
Proof.
  intros m1 chunk b ofs v H.
  destruct (store _ _ _ _ _) eqn:STORE; eauto.
  exfalso.
  eapply @valid_access_store' with (v := v) in H; eauto.
  destruct H.
  congruence.
Defined.

Lemma range_perm_storebytes:
  forall m1 b ofs bytes,
    range_perm m1 b ofs (ofs + Z_of_nat (length bytes)) Cur Writable ->
    stack_access (stack m1) b ofs (ofs + Z_of_nat (length bytes)) ->
  { m2 : mem | storebytes m1 b ofs bytes = Some m2 }.
Proof.
  intros m1 b ofs bytes H NPSA.
  destruct (storebytes _ _ _ _) eqn:STOREBYTES; eauto.
  exfalso.
  apply range_perm_storebytes' in H.
  destruct H.
  congruence.
  apply NPSA.
Defined.

Lemma range_perm_free:
  forall m1 b lo hi,
  range_perm m1 b lo hi Cur Freeable ->
  { m2: mem | free m1 b lo hi = Some m2 }.
Proof.
  intros m1 b lo hi H.
  destruct (free _ _ _ _) eqn:FREE; eauto.
  exfalso.
  apply range_perm_free' in H.
  destruct H.
  congruence.
Defined.

Lemma range_perm_drop_2:
  forall m b lo hi p,
  range_perm m b lo hi Cur Freeable -> { m' | drop_perm m b lo hi p = Some m' }.
Proof.
  intros m b lo hi p H.
  destruct (drop_perm _ _ _ _ _) eqn:DROP; eauto.
  exfalso.
  eapply @range_perm_drop_2' with (p := p) in H; eauto.
  destruct H.
  congruence.
Defined.

Lemma perm_free_list:
  forall l m m' b ofs k p,
  free_list m l = Some m' ->
  perm m' b ofs k p ->
  perm m b ofs k p /\
  (forall lo hi, In (b, lo, hi) l -> lo <= ofs < hi -> False).
Proof.
  induction l; simpl; intros.
  inv H. auto.
  destruct a as [[b1 lo1] hi1].
  destruct (free m b1 lo1 hi1) as [m1|] eqn:E; try discriminate.
  exploit IHl; eauto. intros [A B].
  split. eapply perm_free_3; eauto.
  intros. destruct H1. inv H1.
  elim (perm_free_2 _ _ _ _ _ E ofs k p). auto. auto.
  eauto.
Qed.

Lemma unchanged_on_refl:
  forall P m, unchanged_on P m m.
Proof.
  intros. apply strong_unchanged_on_weak. apply strong_unchanged_on_refl.
Qed.

Lemma store_unchanged_on:
  forall P chunk m b ofs v m',
    store chunk m b ofs v = Some m' ->
    (forall i, ofs <= i < ofs + size_chunk chunk -> ~ P b i) ->
    unchanged_on P m m'.
Proof.
  intros. apply strong_unchanged_on_weak. eapply store_strong_unchanged_on; eauto.
Qed.

Lemma storebytes_unchanged_on:
  forall P m b ofs bytes m',
  storebytes m b ofs bytes = Some m' ->
  (forall i, ofs <= i < ofs + Z_of_nat (length bytes) -> ~ P b i) ->
  unchanged_on P m m'.
Proof.
  intros. apply strong_unchanged_on_weak. eapply storebytes_strong_unchanged_on; eauto.
Qed.

Lemma alloc_unchanged_on:
   forall P m lo hi m' b,
     alloc m lo hi = (m', b) ->
     unchanged_on P m m'.
Proof.
  intros. apply strong_unchanged_on_weak. eapply alloc_strong_unchanged_on; eauto.
Qed.

Lemma free_unchanged_on:
  forall P m b lo hi m',
  free m b lo hi = Some m' ->
  (forall i, lo <= i < hi -> ~ P b i) ->
  unchanged_on P m m'.
Proof.
  intros. apply strong_unchanged_on_weak. eapply free_strong_unchanged_on; eauto.
Qed.

Lemma drop_perm_unchanged_on:
   forall P m b lo hi p m',
     drop_perm m b lo hi p = Some m' ->
     (forall i, lo <= i < hi -> ~ P b i) ->
     unchanged_on P m m'.
Proof.
  intros. apply strong_unchanged_on_weak. eapply drop_perm_strong_unchanged_on; eauto.
Qed.

Lemma perm_free m b lo hi m':
  free m b lo hi = Some m' ->
  forall b' o' k p,
    perm m' b' o' k p <->
    ((~ (b' = b /\ lo <= o' < hi)) /\ perm m b' o' k p).
Proof.
  intros H b' o' k p.
  assert (~ (b' = b /\ lo <= o' < hi) -> perm m b' o' k p -> perm m' b' o' k p) as H0.
  {
    intro H0.
    eapply perm_free_1; eauto.
    destruct (peq b' b); try tauto.
    subst.
    intuition xomega.
  }
  assert (b' = b /\ lo <= o' < hi -> ~ perm m' b' o' k p) as H1.
  destruct 1; subst; eapply perm_free_2; eauto.
  generalize (perm_free_3 _ _ _ _ _ H b' o' k p).
  tauto.
Qed.

Lemma store_stack_access:
  forall chunk m b o v m1 ,
    store chunk m b o v = Some m1 ->
    forall b' lo hi,
      stack_access (stack m1) b' lo hi <-> stack_access (stack m) b' lo hi.
Proof.
  intros; erewrite store_no_abstract; eauto. tauto.
Qed.


Context {injperm: InjectPerm}.

Lemma storev_nextblock :
  forall m chunk addr v m',
    storev chunk m addr v = Some m' ->
    nextblock m' = nextblock m.
Proof.
  intros; destruct addr; simpl in *; try congruence.
  eapply nextblock_store; eauto.
Qed.

Lemma storev_stack :
  forall m chunk addr v m',
    storev chunk m addr v = Some m' ->
    stack m' = stack m.
Proof.
  intros; destruct addr; simpl in *; try congruence.
  eapply store_stack_blocks; eauto.
Qed.

Lemma storev_perm_inv:
  forall m chunk addr v m',
    storev chunk m addr v = Some m' ->
    forall b o k p,
      perm m' b o k p ->
      perm m b o k p.
Proof.
  intros; destruct addr; simpl in *; try congruence.
  eapply perm_store_2; eauto.
Qed.

Lemma frame_inject_flat:
  forall thr f,
    Forall (fun bfi => Plt (fst bfi) thr) (frame_adt_blocks f) ->
    frame_inject (flat_inj thr) f f.
Proof.
  red; intros thr f PLT.
  eapply Forall_impl. 2: eauto. simpl; intros a IN PLTa b2 delta FI.
  unfold flat_inj in FI. destr_in FI. inv FI.
  eexists; split; eauto.
  rewrite <- surjective_pairing. auto.
Qed.

Lemma record_push_inject:
  forall j n g m1 m2 (MINJ: Mem.inject j (n :: g) m1 m2)
    fi1 fi2 (FI: frame_inject j fi1 fi2)
    (NINSTACK: forall b, in_stack (Mem.stack m2) b -> in_frame fi2 b -> False)
    (VALID: Mem.valid_frame fi2 m2)
    (FAP2: frame_agree_perms (Mem.perm m2) fi2)
    (INF: forall b1 b2 delta, j b1 = Some (b2, delta) -> in_frame fi1 b1 <-> in_frame fi2 b2)
    (SZ: frame_adt_size fi1 = frame_adt_size fi2)
    m1'
    (RSB: Mem.record_stack_blocks m1 fi1 = Some m1')
    (TTNP: top_tframe_tc (Mem.stack m2))
    (SZ: size_stack (tl (stack m2)) <= size_stack (tl (stack m1))),
  exists m2', Mem.record_stack_blocks m2 fi2 = Some m2' /\ Mem.inject j (n::g) m1' m2'.
Proof.
  intros.
  eapply Mem.record_stack_blocks_inject_parallel; eauto.
Qed.

Lemma record_stack_blocks_length_stack:
  forall m1 f m2,
    Mem.record_stack_blocks m1 f = Some m2 ->
    length (Mem.stack m2) = length (Mem.stack m1).
Proof.
  intros.
  edestruct Mem.record_stack_blocks_tailcall_original_stack as (ff & r & eq); eauto. rewrite eq.
  eapply Mem.record_stack_blocks_stack in eq; eauto. rewrite eq. reflexivity.
Qed.

Lemma record_stack_blocks_stack_eq:
  forall m1 f m2,
    Mem.record_stack_blocks m1 f = Some m2 ->
    exists tf r,
      Mem.stack m1 = (None,tf)::r /\ Mem.stack m2 = (Some f,tf)::r.
Proof.
  intros.
  edestruct Mem.record_stack_blocks_tailcall_original_stack as (ff & r & eq); eauto. rewrite eq.
  eapply Mem.record_stack_blocks_stack in eq; eauto.
Qed.

Lemma record_push_inject_flat:
  forall j m1 m2 (MINJ: Mem.inject j (flat_frameinj (length (Mem.stack m1))) m1 m2)
    fi1 fi2 (FI: frame_inject j fi1 fi2)
    (NINSTACK: forall b, in_stack (Mem.stack m2) b -> in_frame fi2 b -> False)
    (VALID: Mem.valid_frame fi2 m2)
    (FAP2: frame_agree_perms (Mem.perm m2) fi2)
    (INF: forall b1 b2 delta, j b1 = Some (b2, delta) -> in_frame fi1 b1 <-> in_frame fi2 b2)
    (SZ: frame_adt_size fi1 = frame_adt_size fi2)
    m1'
    (RSB: Mem.record_stack_blocks m1 fi1 = Some m1')
    (TTNP: top_tframe_tc (Mem.stack m2))
    (SZ: size_stack (tl (stack m2)) <= size_stack (tl (stack m1))),
  exists m2', Mem.record_stack_blocks m2 fi2 = Some m2' /\
         Mem.inject j (flat_frameinj (length (Mem.stack m1'))) m1' m2'.
Proof.
  intros.
  destruct (record_stack_blocks_tailcall_original_stack _ _ _ RSB) as (f & r & EQ).
  rewrite (record_stack_blocks_length_stack _ _ _ RSB).
  rewrite EQ in MINJ |- *.
  eapply record_push_inject; eauto.
Qed.

Lemma push_new_stage_loadv:
  forall chunk m v,
    Mem.loadv chunk (Mem.push_new_stage m) v = Mem.loadv chunk m v.
Proof.
  intros; destruct v; simpl; auto. apply Mem.push_new_stage_load.
Qed.
    
Lemma storebytes_push:
  forall m b o bytes m'
    (SB: Mem.storebytes (Mem.push_new_stage m) b o bytes = Some m'),
  exists m2,
    Mem.storebytes m b o bytes = Some m2.
Proof.
  intros.
  eapply Mem.range_perm_storebytes'.
  eapply Mem.storebytes_range_perm in SB.
  red; intros; rewrite <- Mem.push_new_stage_perm; eapply SB; eauto.
  eapply Mem.storebytes_stack_access in SB.
  red in SB |- *.
  destruct SB as [IST|PSA].
  revert IST; rewrite push_new_stage_stack. unfold is_stack_top. simpl. easy.
  right; red in PSA |- *.
  revert PSA. rewrite push_new_stage_stack. simpl; auto.
Qed.

(* Definition clear_stage (m: mem): option mem := *)
(*   match Mem.unrecord_stack_block m with *)
(*   | Some m' => Some (Mem.push_new_stage m') *)
(*   | None => None *)
(*   end. *)

(* Lemma clear_stage_perm: *)
(*   forall m m' *)
(*     (CS: clear_stage m = Some m') *)
(*     b o k p, *)
(*     perm m' b o k p <-> perm m b o k p. *)
(* Proof. *)
(*   unfold clear_stage; intros. repeat destr_in CS. *)
(*   rewrite push_new_stage_perm. *)
(*   split. eapply unrecord_stack_block_perm; eauto. *)
(*   eapply unrecord_stack_block_perm'; eauto. *)
(* Qed. *)

(* Lemma clear_stage_nextblock: *)
(*   forall m m' *)
(*     (CS: clear_stage m = Some m'), *)
(*     nextblock m' = nextblock m. *)
(* Proof. *)
(*   unfold clear_stage; intros. repeat destr_in CS. *)
(*   rewrite push_new_stage_nextblock. *)
(*   eapply unrecord_stack_block_nextblock; eauto. *)
(* Qed. *)

(* Lemma clear_stage_stack: *)
(*   forall m m' *)
(*     (CS: clear_stage m = Some m'), *)
(*     stack m' = nil :: tl (stack m). *)
(* Proof. *)
(*   unfold clear_stage; intros. repeat destr_in CS. *)
(*   rewrite push_new_stage_stack. *)
(*   edestruct unrecord_stack; eauto. rewrite H. simpl. auto. *)
(* Qed. *)

Lemma push_new_stage_inject_flat:
   forall j m1 m2,
        inject j (flat_frameinj (length (stack m1))) m1 m2 ->
        inject j (flat_frameinj (length (stack (push_new_stage m1))))
               (push_new_stage m1) (push_new_stage m2).
Proof.
  intros j m1 m2 INJ.
  apply push_new_stage_inject in INJ.
  rewrite push_new_stage_length_stack.
  unfold flat_frameinj in *. simpl in *; auto.
Qed.

Lemma record_stack_blocks_inject_parallel_flat:
   forall m1 m1' m2 j fi1 fi2,
     inject j (flat_frameinj (length (stack m1))) m1 m2 ->
     frame_inject j fi1 fi2 ->
     (forall b : block, in_stack (stack m2) b -> ~ in_frame fi2 b) ->
     (valid_frame fi2 m2) ->
     frame_agree_perms (perm m2) fi2 ->
     (forall (b1 b2 : block) (delta : Z), j b1 = Some (b2, delta) -> in_frame fi1 b1 <-> in_frame fi2 b2) ->
     frame_adt_size fi1 = frame_adt_size fi2 ->
     record_stack_blocks m1 fi1 = Some m1' ->
     top_tframe_tc (stack m2) ->
     size_stack (tl (stack m2)) <= size_stack (tl (stack m1)) ->
     exists m2',
       record_stack_blocks m2 fi2 = Some m2' /\
       inject j (flat_frameinj (length (stack m1'))) m1' m2'.
Proof.
  intros.
  edestruct record_stack_blocks_inject_parallel as (m2' & RSB & INJ'); eauto.
  eexists; split; eauto.
  erewrite record_stack_blocks_length_stack; eauto.
Qed.


Lemma stack_inject_aux_tailcall_stage:
  forall j g m f1 l1 s1 f2 l2 s2,
    stack_inject_aux j m (1%nat::g) ((Some f1,l1)::s1) ((Some f2, l2)::s2) ->
    stack_inject_aux j m (1%nat::g) ((None, f1::l1)::s1) ((None, f2::l2)::s2).
Proof.
  intros j g m f1 l1 s1 f2 l2 s2 SI. inv SI; econstructor.
  reflexivity. reflexivity. simpl in *; auto.
  constructor; auto.
  simpl in *. inv TAKE.
  red. simpl. congruence.
Qed.

Lemma stack_inject_tailcall_stage:
  forall j g m f1 l1 s1 f2 l2 s2,
    top_tframe_prop (fun tf => forall b, in_frames tf b -> forall o k p, ~ m b o k p) ((Some f1,l1)::s1) ->
    stack_inject j (1%nat::g) m ((Some f1,l1)::s1) ((Some f2, l2)::s2) ->
    stack_inject j (1%nat::g) m ((None, f1::l1)::s1) ((None, f2::l2)::s2).
Proof.
  intros j g m f1 l1 s1 f2 l2 s2 NOPERM SI. inv SI; constructor.
  eapply stack_inject_aux_tailcall_stage; eauto.
  simpl. setoid_rewrite in_stack_cons. intros b1 b2 delta bi2 H H0 FI o k p0 PERM IPC.
  destruct FI as [FI | FI]. easy.
  eapply stack_inject_not_in_source; eauto. 
  2: right; auto.
  rewrite in_stack_cons. intros [A|A].
  red in A. simpl in A.
  inv NOPERM. eapply H2 in PERM; eauto.
  apply H0; right. auto.
Qed.

  Lemma tailcall_stage_inject_flat:
  forall j m1 m2 m1',
    Mem.inject j (flat_frameinj (length (Mem.stack m1))) m1 m2 ->
    Mem.tailcall_stage m1 = Some m1' ->
    top_frame_no_perm m2 ->
     exists m2',
      Mem.tailcall_stage m2 = Some m2' /\ Mem.inject j (flat_frameinj (length (Mem.stack m1'))) m1' m2'.
  Proof.
    intros j m1 m2 m1' INJ TS TOPNOPERM.
    destruct (tailcall_stage_same_length_pos _ _ TS) as (LENEQ & LENPOS).
    rewrite LENEQ.
    destruct (length (Mem.stack m1)); simpl in *. omega.
    rewrite frameinj_push_flat in *.
    eapply tailcall_stage_inject; eauto.
  Qed.

  Lemma free_no_perm_stack:
    forall m b sz m',
      Mem.free m b 0 sz = Some m' ->
      forall bi,
        in_stack' (Mem.stack m) (b, bi) ->
        frame_size bi = Z.max 0 sz ->
        forall o k p,
          ~ Mem.perm m' b o k p.
  Proof.
    intros. rewrite perm_free. 2: eauto.
    intros (NORANGE & P).
    apply NORANGE. split; auto.
    rewrite in_stack'_rew in H0. destruct H0 as (tf & IFR & INS).
    rewrite in_frames'_rew in IFR. destruct IFR as (fr & IFR & EQfr).
    exploit Mem.agree_perms_mem. apply INS. eauto. apply IFR. eauto. rewrite H1.
    rewrite Zmax_spec. destr. omega.
  Qed.

  Lemma free_no_perm_stack':
    forall m b sz m',
      Mem.free m b 0 sz = Some m' ->
      forall bi f0 r s0 l,
        Mem.stack m = (Some f0, r) :: s0 ->
        frame_adt_blocks f0 = (b, bi) :: l ->
        frame_size bi = Z.max 0 sz ->
        forall o k p,
          ~ Mem.perm m' b o k p.
  Proof.
    intros; eapply free_no_perm_stack; eauto.
    rewrite H0; left. red; simpl; red. rewrite H1. left; reflexivity.
  Qed.

  Lemma free_top_tframe_no_perm:
    forall m b sz m'
      (FREE: Mem.free m b 0 sz = Some m')
      bi f0 r s0
      (STKeq: Mem.stack m = (Some f0, r) :: s0)
      (BLOCKS: frame_adt_blocks f0 = (b, bi) :: nil)
      (SZ: frame_size bi = Z.max 0 sz),
      top_frame_no_perm m'.
  Proof.
    intros.
    red. erewrite free_stack_blocks; eauto.
    rewrite STKeq.
    constructor.
    generalize (Mem.wf_stack_mem m). rewrite STKeq. intro A; inv A.
    unfold in_frames. simpl. unfold get_frame_blocks. rewrite BLOCKS.
    simpl. intros bb [EQ|[]].
    subst. simpl in *.
    intros; eapply free_no_perm_stack'; eauto.
  Qed.

  Lemma free_top_tframe_no_perm':
    forall m b sz m'
      (FREE: Mem.free m b 0 sz = Some m')
      bi f0 r s0
      (STKeq: Mem.stack m = (Some f0, r) :: s0)
      (BLOCKS: frame_adt_blocks f0 = (b, bi) :: nil)
      (SZ: frame_size bi = sz),
      top_frame_no_perm m'.
  Proof.
    intros.
    eapply free_top_tframe_no_perm; eauto.
    rewrite Z.max_r. auto. subst; apply frame_size_pos.
  Qed.

  
  Lemma record_push_inject_alloc
    : forall m01 m02 m1 m2 j0 j g fsz b1 b2 sz
        (MINJ0: Mem.inject j0 g m01 m02)
        (ALLOC1: Mem.alloc m01 0 fsz = (m1, b1))
        (ALLOC2: Mem.alloc m02 0 fsz = (m2, b2))
        (MINJ: Mem.inject j g m1 m2)
        (OLD: forall b : block, b <> b1 -> j b = j0 b)
        (NEW: j b1 = Some (b2, 0))
        m1'
        (RSB: Mem.record_stack_blocks m1 (make_singleton_frame_adt b1 fsz sz) = Some m1') 
        (TTT: top_tframe_tc (Mem.stack m02))
        (SZ: size_stack (tl (Mem.stack m02)) <= size_stack (tl (Mem.stack m01))),
      exists m2' : mem,
        Mem.record_stack_blocks m2 (make_singleton_frame_adt b2 fsz sz) = Some m2' /\
        Mem.inject j g m1' m2'.
  Proof.
    intros m01 m02 m1 m2 j0 j g fsz b1 b2 sz MINJ0 ALLOC1 ALLOC2 MINJ OLD NEW m1' RSB TTT SZ.
    eapply Mem.record_stack_blocks_inject_parallel. eauto. 7: eauto. all: eauto.
    - red; simpl. constructor; auto.
      simpl. rewrite NEW. inversion 1; subst. eauto.
    - unfold in_frame; simpl.
      erewrite alloc_stack_blocks by eauto.
      intros b H. eapply Mem.in_frames_valid in H. red in H.
      intros [A|[]]; subst.
      eapply Mem.fresh_block_alloc; eauto.
    - red; unfold in_frame; simpl. intros b [[]|[]].
      eapply Mem.valid_new_block; eauto.
    - simpl.
      intros ? ? ? ? ? [A|[]]. inv A.
      intro P; eapply Mem.perm_alloc_inv in P; eauto. destr_in P.
      simpl. rewrite Z.max_r; omega.
    - unfold in_frame; simpl.
      intros b0 b3 delta JB.
      split; intros [A|[]]; inv A; left. congruence.
      destruct (peq b1 b0); auto.
      rewrite OLD in JB by auto.
      eapply Mem.valid_block_inject_2 in JB; eauto.
      eapply Mem.fresh_block_alloc in JB. easy. eauto.
    - erewrite alloc_stack_blocks by eauto. auto.
    - erewrite (alloc_stack_blocks _ _ _ _ _ ALLOC1), (alloc_stack_blocks _ _ _ _ _ ALLOC2); auto.
  Qed.

    Lemma record_push_inject_flat_alloc
    : forall m01 m02 m1 m2 j0 j fsz b1 b2 sz
        (MINJ0: Mem.inject j0 (flat_frameinj (length (Mem.stack m01))) m01 m02)
        (ALLOC1: Mem.alloc m01 0 fsz = (m1, b1))
        (ALLOC2: Mem.alloc m02 0 fsz = (m2, b2))
        (MINJ: Mem.inject j (flat_frameinj (length (Mem.stack m01))) m1 m2)
        (OLD: forall b : block, b <> b1 -> j b = j0 b)
        (NEW: j b1 = Some (b2, 0))
        m1'
        (RSB: Mem.record_stack_blocks m1 (make_singleton_frame_adt b1 fsz sz) = Some m1') 
        (TTT: top_tframe_tc (Mem.stack m02))
        (SZ: size_stack (tl (Mem.stack m02)) <= size_stack (tl (Mem.stack m01))),
      exists m2' : mem,
         Mem.record_stack_blocks m2 (make_singleton_frame_adt b2 fsz sz) = Some m2' /\
         Mem.inject j (flat_frameinj (length (Mem.stack m1'))) m1' m2'.
  Proof.
    intros m01 m02 m1 m2 j0 j fsz b1 b2 sz MINJ0 ALLOC1 ALLOC2 MINJ OLD NEW m1' RSB TTT SZ.
    eapply record_push_inject_alloc. 7: eauto. 2: eauto. all: eauto.
    erewrite record_stack_blocks_length_stack, alloc_stack_blocks; eauto.
    erewrite record_stack_blocks_length_stack, alloc_stack_blocks; eauto.
  Qed.

  Lemma record_push_extends_flat_alloc
    : forall m01 m02 m1 m2 fsz b sz
        (ALLOC1: Mem.alloc m01 0 fsz = (m1, b))
        (ALLOC2: Mem.alloc m02 0 fsz = (m2, b))
        (MINJ: Mem.extends m1 m2)
        m1'
        (RSB: Mem.record_stack_blocks m1 (make_singleton_frame_adt b fsz sz) = Some m1') 
        (TTT: top_tframe_tc (Mem.stack m02))
        (SZ: size_stack (tl (Mem.stack m02)) <= size_stack (tl (Mem.stack m01))),
      exists m2' : mem,
        Mem.record_stack_blocks m2 (make_singleton_frame_adt b fsz sz) = Some m2' /\
        Mem.extends m1' m2'.
  Proof.
    intros m01 m02 m1 m2 fsz b sz ALLOC1 ALLOC2 MINJ m1' RSB TTT SZ.
    eapply record_stack_blocks_extends; eauto.
    + unfold in_frame. simpl. intros ? [?|[]]; subst.
      intro IFF.
      erewrite alloc_stack_blocks in IFF; eauto.
      eapply Mem.in_frames_valid in IFF. eapply Mem.fresh_block_alloc in ALLOC2. congruence.
    + intros bb fi o k0 p [AA|[]] P; inv AA. simpl.
      eapply perm_alloc_inv in P; eauto. destr_in P. rewrite Z.max_r; omega.
    + erewrite alloc_stack_blocks; eauto.
    + erewrite (alloc_stack_blocks _ _ _ _ _ ALLOC1), (alloc_stack_blocks _ _ _ _ _ ALLOC2); auto.
  Qed.

  Lemma record_init_sp_inject:
    forall j g m1 m1' m2,
      Mem.inject j g m1 m1' ->
      size_stack (stack m1') <= size_stack (stack m1) ->
      record_init_sp m1 = Some m2 ->
      exists m2', record_init_sp m1' = Some m2' /\ inject (fun b => if peq b (nextblock (push_new_stage m1))
                                                           then Some (nextblock (push_new_stage m1'), 0)
                                                           else j b) (1%nat::g) m2 m2'.
  Proof.
    intros j g m1 m1' m2 INJ SZ RIS.
    unfold record_init_sp in *; destr_in RIS.
    exploit Mem.push_new_stage_inject. apply INJ. intro INJ0.
    edestruct Mem.alloc_parallel_inject as (f' & m2' & b2 & ALLOC & INJ1 & INCR & JNEW & JOLD).
    apply INJ0. eauto. reflexivity. reflexivity.
    rewrite ALLOC.
    edestruct record_push_inject_alloc as (m2'' & RSB & INJ'). 7: apply RIS.
    2: apply Heqp. 2: apply ALLOC. all: eauto.
    rewrite push_new_stage_stack. constructor; reflexivity.
    rewrite ! push_new_stage_stack. simpl. auto.
    eexists; split. eauto.
    eapply inject_ext. eauto.
    intros. erewrite <- ! alloc_result by eauto.
    destr. eauto.
  Qed.

  Lemma record_init_sp_extends:
    forall m1 m1' m2,
      Mem.extends m1 m1' ->
      size_stack (stack m1') <= size_stack (stack m1) ->
      record_init_sp m1 = Some m2 ->
      exists m2', record_init_sp m1' = Some m2' /\ extends m2 m2'.
  Proof.
    intros m1 m1' m2 INJ SZ RIS.
    unfold record_init_sp in *; destr_in RIS.
    apply extends_push in INJ.
    edestruct alloc_extends as (m2' & ALLOC & INJ1).
    apply INJ. eauto. reflexivity. reflexivity.
    rewrite ALLOC.
    edestruct record_push_extends_flat_alloc as (m2'' & RSB & INJ'). 4: apply RIS.
    apply Heqp. apply ALLOC. all: eauto.
    rewrite push_new_stage_stack. constructor; reflexivity.
    rewrite ! push_new_stage_stack. simpl. auto.
  Qed.

  Lemma record_init_sp_flat_inject
    : forall (m1 m1' m2 : mem),
      Mem.inject (Mem.flat_inj (Mem.nextblock m1)) (flat_frameinj (length (Mem.stack m1))) m1 m1' ->
      size_stack (Mem.stack m1') <= size_stack (Mem.stack m1) ->
      Mem.record_init_sp m1 = Some m2 ->
      Mem.nextblock m1 = Mem.nextblock m1' ->
      exists m2' : mem,
        Mem.record_init_sp m1' = Some m2' /\
        Mem.inject
          (Mem.flat_inj (Mem.nextblock m2))
          (flat_frameinj (length (Mem.stack m2))) m2 m2'.
  Proof.
    intros m1 m1' m2 INJ SZ RIS EQNB.
    edestruct record_init_sp_inject as (m2' & RIS' & INJ'); eauto.
    eexists; split; eauto.
    unfold record_init_sp in RIS; destr_in RIS.
    erewrite (record_stack_block_nextblock _ _ _ RIS).
    erewrite (nextblock_alloc _ _ _ _ _ Heqp).
    rewrite push_new_stage_nextblock.
    destruct (record_stack_blocks_stack_eq _ _ _ RIS) as (tf & r & EQ1 & EQ2).
    rewrite EQ2. 
    erewrite (alloc_stack_blocks _ _ _ _ _ Heqp) in EQ1.
    rewrite push_new_stage_stack in EQ1. inv EQ1.
    simpl. rewrite frameinj_push_flat.
    eapply inject_ext; eauto.
    simpl; intros. unfold flat_inj.
    rewrite ! push_new_stage_nextblock. rewrite EQNB.
    repeat (destr; subst); xomega.
  Qed.

  Lemma record_init_sp_nextblock:
    forall m1 m2,
      record_init_sp m1 = Some m2 ->
      Ple (nextblock m1) (nextblock m2).
  Proof.
    intros m1 m2 RIS.
    unfold record_init_sp in RIS. destr_in RIS.
    erewrite (record_stack_block_nextblock _ _ _ RIS).
    erewrite (nextblock_alloc _ _ _ _ _ Heqp).
    rewrite push_new_stage_nextblock. xomega.
  Qed.

  Lemma record_init_sp_nextblock_eq:
    forall m1 m2,
      record_init_sp m1 = Some m2 ->
      (nextblock m2) = Pos.succ (nextblock m1).
  Proof.
    intros m1 m2 RIS.
    unfold record_init_sp in RIS. destr_in RIS.
    erewrite (record_stack_block_nextblock _ _ _ RIS).
    erewrite (nextblock_alloc _ _ _ _ _ Heqp).
    rewrite push_new_stage_nextblock. reflexivity.
  Qed.
  
  Lemma record_init_sp_stack:
    forall m1 m2,
      Mem.record_init_sp m1 = Some m2 ->
      Mem.stack m2 = (Some (make_singleton_frame_adt (Mem.nextblock (Mem.push_new_stage m1)) 0 0),nil)::Mem.stack m1.
  Proof.
    unfold Mem.record_init_sp. intros m1 m2 RIS; destr_in RIS.
    destruct (record_stack_blocks_stack_eq _ _ _ RIS) as (tf & r & EQ1 & EQ2).
    rewrite EQ2. 
    erewrite (alloc_stack_blocks _ _ _ _ _ Heqp) in EQ1.
    rewrite push_new_stage_stack in EQ1. inv EQ1.
    exploit Mem.alloc_result; eauto. intros; subst. reflexivity.
  Qed.
  
  Lemma record_init_sp_perm:
    forall m1 m2,
      Mem.record_init_sp m1 = Some m2 ->
      forall b o k p,
        perm m2 b o k p <-> perm m1 b o k p.
  Proof.
    unfold Mem.record_init_sp. intros m1 m2 RIS; destr_in RIS.
    intros.
    split; intro P.
    - eapply push_new_stage_perm.
      eapply record_stack_block_perm in P. 2: eauto.
      eapply perm_alloc_inv in P; eauto.
      destr_in P. omega.
    - eapply record_stack_block_perm'. eauto.
      eapply perm_alloc_1. eauto.
      eapply push_new_stage_perm. auto.
  Qed.
  
  Definition is_ptr (v: val) :=
    match v with Vptr _ _ => Some v | _ => None end.
  
  Definition encoded_ra (l: list memval) : option val :=
    match proj_bytes l with
    | Some bl => Some (Vptrofs (Ptrofs.repr (decode_int bl)))
    | None => is_ptr (Val.load_result Mptr (proj_value (quantity_chunk Mptr) l))
    end.

  Definition loadbytesv chunk m addr :=
    match addr with
      Vptr b o =>
      match Mem.loadbytes m b (Ptrofs.unsigned o) (size_chunk chunk) with
      | Some bytes => encoded_ra bytes
      | None => None
      end
    | _ => None
    end.

  Lemma loadbytesv_inject:
    forall j g chunk m m' v v' ra,
      Mem.inject j g m m' ->
      Val.inject j v v' ->
      loadbytesv chunk m v = Some ra ->
      exists ra', loadbytesv chunk m' v' = Some ra' /\ Val.inject j ra ra'.
  Proof.
    intros j g chunk m m' v v' ra MINJ VINJ L.
    unfold loadbytesv in *.
    destr_in L. inv VINJ.
    destr_in L.
    edestruct Mem.loadbytes_inject as (l' & L' & INJ); eauto.
    erewrite Mem.address_inject; eauto.
    rewrite L'.
    - unfold encoded_ra in L |- *.
      repeat destr_in L.
      erewrite proj_bytes_inject; eauto.
      destr. eapply proj_bytes_not_inject in Heqo0; eauto. 2: congruence.
      erewrite proj_value_undef in H0; eauto.
      contradict H0. unfold Mptr. destr; simpl; congruence.
      generalize (proj_value_inject _ (quantity_chunk Mptr) _ _ INJ). intro VINJ.
      generalize (Val.load_result_inject _ Mptr _ _ VINJ). intro VINJ'.
      unfold is_ptr in H0. destr_in H0. inv H0. inv VINJ'.
      eexists; split. simpl. eauto.
      econstructor; eauto.
    - eapply Mem.loadbytes_range_perm; eauto. generalize (size_chunk_pos chunk); omega.
  Qed.

  Lemma loadbytesv_extends:
    forall chunk m m' v v' ra,
      Mem.extends m m' ->
      Val.lessdef v v' ->
      loadbytesv chunk m v = Some ra ->
      exists ra', loadbytesv chunk m' v' = Some ra' /\ Val.lessdef ra ra'.
  Proof.
    intros chunk m m' v v' ra MEXT VLD L.
    unfold loadbytesv in *.
    destr_in L. inv VLD.
    destr_in L.
    edestruct Mem.loadbytes_extends as (l' & L' & EXT); eauto.
    rewrite L'.
    - unfold encoded_ra in L |- *.
      repeat destr_in L.
      erewrite proj_bytes_inject; eauto.
      destr. eapply proj_bytes_not_inject in Heqo0; eauto. 2: congruence.
      erewrite proj_value_undef in H0; eauto.
      contradict H0. unfold Mptr. destr; simpl; congruence.
      generalize (proj_value_inject _ (quantity_chunk Mptr) _ _ EXT). intro VEXT.
      generalize (Val.load_result_inject _ Mptr _ _ VEXT). intro VEXT'.
      unfold is_ptr in H0. destr_in H0. inv H0. inv VEXT'. inv H2.
      eexists; split. simpl. eauto.
      rewrite Ptrofs.add_zero. econstructor; eauto.
  Qed.

  
  Lemma proj_value_inj_value:
    forall q v l,
      proj_value q l = v ->
      v <> Vundef ->
      inj_value q v = l.
  Proof.
    unfold proj_value.
    intros q v l PROJ NU.
    subst. destr. destr. destr.
    destruct q; simpl in Heqb;
      repeat match goal with
             | H: andb _ _ = true |- _ => rewrite andb_true_iff in H; destruct H
             | H: proj_sumbool (quantity_eq ?q1 ?q2) = true |- _ =>
               destruct (quantity_eq q1 q2); simpl in H; try congruence; subst
             | H: proj_sumbool (Val.eq ?q1 ?q2) = true |- _ =>
               destruct (Val.eq q1 q2); simpl in H; try congruence; subst
             | H: context [match ?a with _ => _ end] |- _ => destruct a eqn:?; simpl in *; intuition try congruence
             end.
  Qed.

  Lemma long_unsigned_ptrofs_repr_eq:
    Archi.ptr64 = true -> forall a, Int64.unsigned (Ptrofs.to_int64 (Ptrofs.repr a)) = Ptrofs.unsigned (Ptrofs.repr a).
  Proof.
    intros.
    unfold Ptrofs.to_int64.
    rewrite <- Ptrofs.agree64_repr; auto.
    rewrite Ptrofs.repr_unsigned. auto.
  Qed.

  Lemma int_unsigned_ptrofs_repr_eq:
    Archi.ptr64 = false -> forall a, Int.unsigned (Ptrofs.to_int (Ptrofs.repr a)) = Ptrofs.unsigned (Ptrofs.repr a).
  Proof.
    intros.
    unfold Ptrofs.to_int.
    rewrite <- Ptrofs.agree32_repr; auto.
    rewrite Ptrofs.repr_unsigned. auto.
  Qed.

  Lemma byte_decompose: forall i x, (Byte.unsigned i + x * 256) / 256 = x.
  Proof.
    intros.
    rewrite Z_div_plus_full.
    rewrite Zdiv_small. omega. apply Byte.unsigned_range. omega.
  Qed.

  Lemma ptrofs_wordsize: Ptrofs.zwordsize = 8 * size_chunk Mptr.
  Proof.
    unfold Ptrofs.zwordsize, Ptrofs.wordsize.
    unfold Wordsize_Ptrofs.wordsize. unfold Mptr.
    destr; omega.
  Qed.
  
  Lemma ptrofs_byte_modulus_ptr64:
    Archi.ptr64 = true ->
    Byte.modulus ^ 8 - 1 = Ptrofs.max_unsigned.
  Proof.
    unfold Ptrofs.max_unsigned. rewrite Ptrofs.modulus_power.
    rewrite ptrofs_wordsize.
    intros. unfold Mptr; rewrite H. simpl. reflexivity.
  Qed.

  Lemma ptrofs_byte_modulus_ptr32:
    Archi.ptr64 = false ->
    Byte.modulus ^ 4 - 1 = Ptrofs.max_unsigned.
  Proof.
    unfold Ptrofs.max_unsigned. rewrite Ptrofs.modulus_power.
    rewrite ptrofs_wordsize.
    intros. unfold Mptr; rewrite H. simpl. reflexivity.
  Qed.

  Lemma byte_compose_range:
    forall i x n,
      0 < n ->
      0 <= x < Byte.modulus ^ (n - 1) ->
      0 <= Byte.unsigned i + x * 256 < Byte.modulus ^ n.
  Proof.
    intros i x n POS RNG.
    split.
    generalize (Byte.unsigned_range i). omega.
    generalize (Byte.unsigned_range i). 
    change Byte.modulus with 256 in *. 
    replace n with ((n-1)+1) by omega. rewrite Zpower_exp by omega.
    change (256 ^ 1) with 256.
    assert (0 <= x * 256 < 256 ^ (n - 1) * 256).
    split. omega.
    apply Z.mul_lt_mono_pos_r. omega. omega.
    omega.
  Qed.

  Lemma le_m1_lt:
    forall a b,
      0 <= a < b ->
      0 <= a <= b - 1.
  Proof.
    intros; omega.
  Qed.

  Lemma byte_repr_plus i0 i:
    Byte.repr (Byte.unsigned i0 + i * 256) = i0.
  Proof.
    apply Byte.eqm_repr_eq.
    red. red. exists i.
    change Byte.modulus with 256 in *. omega.
  Qed.
  
  Lemma encode_decode_long:
    forall l,
      length l = 8%nat ->
      Archi.ptr64 = true ->
      encode_int 8 (Int64.unsigned (Ptrofs.to_int64 (Ptrofs.repr (decode_int l)))) = l.
  Proof.
    intros.
    repeat match goal with
           | H : length ?l = _ |- _ =>
             destruct l; simpl in H; inv H
           end. simpl.
    unfold encode_int, decode_int.
    unfold rev_if_be. destr.
    - simpl.
      rewrite Z.add_0_r.
      rewrite ! long_unsigned_ptrofs_repr_eq; auto.
      f_equal; rewrite ! Ptrofs.unsigned_repr.
      rewrite ! byte_decompose; apply Byte.repr_unsigned.
      rewrite <- ptrofs_byte_modulus_ptr64; auto.
      apply le_m1_lt.
      repeat (apply byte_compose_range; [omega |]).
      simpl Z.sub. apply Byte.unsigned_range.
      f_equal. rewrite ! byte_decompose. apply byte_repr_plus.
      f_equal. rewrite ! byte_decompose. apply byte_repr_plus.
      f_equal. rewrite ! byte_decompose. apply byte_repr_plus.
      f_equal. rewrite ! byte_decompose. apply byte_repr_plus.
      f_equal. rewrite ! byte_decompose. apply byte_repr_plus.
      f_equal. rewrite ! byte_decompose. apply byte_repr_plus.
      f_equal. apply byte_repr_plus.
      rewrite <- ptrofs_byte_modulus_ptr64; auto.
      apply le_m1_lt.
      repeat (apply byte_compose_range; [omega |]).
      simpl Z.sub. apply Byte.unsigned_range.
    - simpl.
      rewrite Z.add_0_r.
      rewrite ! long_unsigned_ptrofs_repr_eq; auto.
      f_equal; rewrite ! Ptrofs.unsigned_repr.
      apply byte_repr_plus.
      rewrite <- ptrofs_byte_modulus_ptr64; auto.
      apply le_m1_lt.
      repeat (apply byte_compose_range; [omega |]).
      simpl Z.sub. apply Byte.unsigned_range.
      f_equal. rewrite ! byte_decompose. apply byte_repr_plus.
      f_equal. rewrite ! byte_decompose. apply byte_repr_plus.
      f_equal. rewrite ! byte_decompose. apply byte_repr_plus.
      f_equal. rewrite ! byte_decompose. apply byte_repr_plus.
      f_equal. rewrite ! byte_decompose. apply byte_repr_plus.
      f_equal. rewrite ! byte_decompose. apply byte_repr_plus.
      f_equal. rewrite ! byte_decompose. apply Byte.repr_unsigned.
      rewrite <- ptrofs_byte_modulus_ptr64; auto.
      apply le_m1_lt.
      repeat (apply byte_compose_range; [omega |]).
      simpl Z.sub. apply Byte.unsigned_range.
  Qed.

  Lemma encode_decode_int:
    forall l,
      length l = 4%nat ->
      Archi.ptr64 = false ->
      encode_int 4 (Int.unsigned (Ptrofs.to_int (Ptrofs.repr (decode_int l)))) = l.
  Proof.
    intros.
    repeat match goal with
           | H : length ?l = _ |- _ =>
             destruct l; simpl in H; inv H
           end. simpl.
    unfold encode_int, decode_int.
    unfold rev_if_be. destr.
    - simpl.
      rewrite Z.add_0_r.
      rewrite ! int_unsigned_ptrofs_repr_eq; auto.
      f_equal; rewrite ! Ptrofs.unsigned_repr.
      rewrite ! byte_decompose; apply Byte.repr_unsigned.
      rewrite <- ptrofs_byte_modulus_ptr32; auto.
      apply le_m1_lt.
      repeat (apply byte_compose_range; [omega |]).
      simpl Z.sub. apply Byte.unsigned_range.
      f_equal. rewrite ! byte_decompose. apply byte_repr_plus.
      f_equal. rewrite ! byte_decompose. apply byte_repr_plus.
      f_equal. apply byte_repr_plus.
      rewrite <- ptrofs_byte_modulus_ptr32; auto.
      apply le_m1_lt.
      repeat (apply byte_compose_range; [omega |]).
      simpl Z.sub. apply Byte.unsigned_range.
    - simpl.
      rewrite Z.add_0_r.
      rewrite ! int_unsigned_ptrofs_repr_eq; auto.
      f_equal; rewrite ! Ptrofs.unsigned_repr.
      apply byte_repr_plus.
      rewrite <- ptrofs_byte_modulus_ptr32; auto.
      apply le_m1_lt.
      repeat (apply byte_compose_range; [omega |]).
      simpl Z.sub. apply Byte.unsigned_range.
      f_equal. rewrite ! byte_decompose. apply byte_repr_plus.
      f_equal. rewrite ! byte_decompose. apply byte_repr_plus.
      f_equal. rewrite ! byte_decompose. apply Byte.repr_unsigned.
      rewrite <- ptrofs_byte_modulus_ptr32; auto.
      apply le_m1_lt.
      repeat (apply byte_compose_range; [omega |]).
      simpl Z.sub. apply Byte.unsigned_range.
  Qed.

End WITHMEMORYMODEL.

End Mem.
