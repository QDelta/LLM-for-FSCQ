Require Import Arith.
Require Import Setoid.
Require Import Pred PredCrash.
Require Import Word.
Require Import Prog ProgMonad.
Require Import Hoare.
Require Import BasicProg.
Require Import Lia.
Require Import Lia.
Require Import Log.
Require Import Array.
Require Import List ListUtils.
Require Import Bool.
Require Import Eqdep_dec.
Require Import SepAuto.
Require Import Rec.
Require Import FunctionalExtensionality.
Require Import NArith.
Require Import WordAuto.
Require Import RecArrayUtils LogRecArray.
Require Import GenSepN.
Require Import Balloc.
Require Import ListPred.
Require Import FSLayout.
Require Import AsyncDisk.
Require Import Rounding.
Require Import Errno.
Require Import DiskSet.
Import SyncedMem.
Import ListNotations.
Set Implicit Arguments.
Module Type BlockPtrSig.
Parameter irec     : Type.
Parameter iattr    : Type.
Parameter NDirect  : addr.
Parameter NDirect_bound : NDirect <= addrlen.
Parameter IRLen    : irec -> addr.
Parameter IRIndPtr : irec -> addr.
Parameter IRDindPtr: irec -> addr.
Parameter IRTindPtr: irec -> addr.
Parameter IRBlocks : irec -> list waddr.
Parameter IRAttrs  : irec -> iattr.
Parameter upd_len  : irec -> addr -> irec.
Parameter upd_irec : forall (r : irec) (len : addr) (ibptr : addr)
                                                      (dibptr : addr)
                                                      (tibptr : addr)
                                                      (dbns : list waddr), irec.
Parameter upd_irec_eq_upd_len : forall ir len, goodSize addrlen len ->
    upd_len ir len = upd_irec ir len (IRIndPtr ir) (IRDindPtr ir) (IRTindPtr ir) (IRBlocks ir).
Parameter upd_len_get_len    : forall ir n, goodSize addrlen n -> IRLen (upd_len ir n) = n.
Parameter upd_len_get_ind    : forall ir n, IRIndPtr (upd_len ir n) = IRIndPtr ir.
Parameter upd_len_get_dind   : forall ir n, IRDindPtr (upd_len ir n) = IRDindPtr ir.
Parameter upd_len_get_tind   : forall ir n, IRTindPtr (upd_len ir n) = IRTindPtr ir.
Parameter upd_len_get_blk    : forall ir n, IRBlocks (upd_len ir n) = IRBlocks ir.
Parameter upd_len_get_iattr  : forall ir n, IRAttrs (upd_len ir n) = IRAttrs ir.
Parameter upd_irec_get_len   : forall ir len ibptr dibptr tibptr dbns,
     goodSize addrlen len -> IRLen (upd_irec ir len ibptr dibptr tibptr dbns) = len.
Parameter upd_irec_get_ind   : forall ir len ibptr dibptr tibptr dbns,
     goodSize addrlen ibptr -> IRIndPtr (upd_irec ir len ibptr dibptr tibptr dbns) = ibptr.
Parameter upd_irec_get_dind  : forall ir len ibptr dibptr tibptr dbns,
     goodSize addrlen dibptr -> IRDindPtr (upd_irec ir len ibptr dibptr tibptr dbns) = dibptr.
Parameter upd_irec_get_tind  : forall ir len ibptr dibptr tibptr dbns,
     goodSize addrlen tibptr -> IRTindPtr (upd_irec ir len ibptr dibptr tibptr dbns) = tibptr.
Parameter upd_irec_get_blk   : forall ir len ibptr dibptr tibptr dbns,
     IRBlocks (upd_irec ir len ibptr dibptr tibptr dbns) = dbns.
Parameter upd_irec_get_iattr : forall ir len ibptr dibptr tibptr dbns,
      IRAttrs (upd_irec ir len ibptr dibptr tibptr dbns) = IRAttrs ir.
Parameter get_len_goodSize  : forall ir, goodSize addrlen (IRLen ir).
Parameter get_ind_goodSize  : forall ir, goodSize addrlen (IRIndPtr ir).
Parameter get_dind_goodSize : forall ir, goodSize addrlen (IRDindPtr ir).
Parameter get_tind_goodSize : forall ir, goodSize addrlen (IRTindPtr ir).
End BlockPtrSig.
Module BlockPtr (BPtr : BlockPtrSig).
Import BPtr.
Definition indrectype := Rec.WordF addrlen.
Module IndSig <: RASig.
Definition xparams := addr.
Definition RAStart := fun (x : xparams) => x.
Definition RALen := fun (_ : xparams) => 1.
Definition xparams_ok (_ : xparams) := True.
Definition itemtype := indrectype.
Definition items_per_val := valulen / (Rec.len itemtype).
Theorem blocksz_ok : valulen = Rec.len (Rec.ArrayF itemtype items_per_val).
Proof.
(* original proof tokens: 30 *)

(* No more tactics to try *)
Admitted.

End IndSig.
Module IndRec  := LogRecArray IndSig.
Hint Extern 0 (okToUnify (IndRec.rep _ _) (IndRec.rep _ _)) => constructor : okToUnify.
Notation "'NIndirect'" := IndSig.items_per_val.
Notation "'NBlocks'"   := (NDirect + NIndirect + NIndirect ^ 2 + NIndirect ^ 3)%nat.
Lemma NIndirect_is : NIndirect = 512.
Proof.
(* original proof tokens: 25 *)

(* No more tactics to try *)
Admitted.

Lemma NBlocks_roundtrip : # (natToWord addrlen NBlocks) = NBlocks.
Proof.
(* original proof tokens: 109 *)

(* No more tactics to try *)
Admitted.

Lemma NDirect_roundtrip : # (natToWord addrlen NDirect) = NDirect.
Proof.
(* original proof tokens: 41 *)

(* No more tactics to try *)
Admitted.

Lemma NIndirect_roundtrip : # (natToWord addrlen NIndirect) = NIndirect.
Proof.
(* original proof tokens: 41 *)

(* No more tactics to try *)
Admitted.

Lemma le_ndirect_goodSize : forall n,
    n <= NDirect -> goodSize addrlen n.
Proof.
(* original proof tokens: 29 *)

(* No more tactics to try *)
Admitted.

Lemma le_nindirect_goodSize : forall n,
    n <= NIndirect -> goodSize addrlen n.
Proof.
(* original proof tokens: 29 *)

(* No more tactics to try *)
Admitted.

Lemma le_nblocks_goodSize : forall n,
    n <= NBlocks -> goodSize addrlen n.
Proof.
(* original proof tokens: 29 *)

(* No more tactics to try *)
Admitted.

Local Hint Resolve le_ndirect_goodSize le_nindirect_goodSize le_nblocks_goodSize.
Definition indrep_n_helper (Fs : @pred _ addr_eq_dec bool) bxp ibn iblocks :=
    (if (addr_eq_dec ibn 0)
      then [[ iblocks = repeat $0 NIndirect]] *
           [[ Fs <=p=> emp ]]
      else [[ BALLOCC.bn_valid bxp ibn ]] * IndRec.rep ibn iblocks *
          [[ (Fs <=p=> ibn |->?) ]]
    )%pred.
Fixpoint indrep_n_tree indlvl bxp Fs ibn l :=
    (match indlvl with
    | 0 => indrep_n_helper Fs bxp ibn l
    | S indlvl' =>
      exists iblocks Fs' lFs,
        [[ length lFs = length iblocks ]] *
        [[ Fs <=p=> Fs' * pred_fold_left lFs ]] *
        indrep_n_helper Fs' bxp ibn iblocks *
        exists l_part, [[ l = concat l_part ]] *
        listmatch (fun ibn'_fs l' =>
          indrep_n_tree indlvl' bxp (snd ibn'_fs) (# (fst ibn'_fs)) l') (combine iblocks lFs) l_part
    end)%pred.
Hint Extern 0 (okToUnify (indrep_n_helper _ _ _ _) (indrep_n_helper _ _ _ _)) => constructor : okToUnify.
Hint Extern 0 (okToUnify (indrep_n_tree _ _ _ _ _) (indrep_n_tree _ _ _ _ _ )) => constructor : okToUnify.
Local Hint Extern 0 (okToUnify (listmatch _ ?a _) (listmatch _ ?a _)) => constructor : okToUnify.
Local Hint Extern 0 (okToUnify (listmatch _ _ ?b) (listmatch _ _ ?b)) => constructor : okToUnify.
Local Hint Extern 0 (okToUnify (listmatch _ (combine ?a _) _) (listmatch _ (combine ?a _) _)) => constructor : okToUnify.
Set Regular Subst Tactic.
Local Hint Resolve IndRec.Defs.items_per_val_not_0.
Local Hint Resolve IndRec.Defs.items_per_val_gt_0'.
Lemma off_mod_len_l : forall T off (l : list T), length l = NIndirect -> off mod NIndirect < length l.
Proof.
(* original proof tokens: 21 *)

(* No more tactics to try *)
Admitted.

Fact divmod_n_zeros : forall n, fst (Nat.divmod n 0 0 0) = n.
Proof.
(* original proof tokens: 15 *)

(* No more tactics to try *)
Admitted.

Hint Rewrite divmod_n_zeros using auto.
Local Hint Resolve Nat.pow_nonzero off_mod_len_l mult_neq_0.
Local Hint Resolve mul_ge_l mul_ge_r.
Fact sub_sub_comm : forall a b c, a - b - c = a - c - b.
Proof.
(* original proof tokens: 33 *)

(* No more tactics to try *)
Admitted.

Fact sub_S_1 : forall n, n > 0 -> S (n - 1) = n.
Proof.
(* original proof tokens: 12 *)
(* generated proof tokens: 8 *)

lia.
Qed.

Fact sub_le_eq_0 : forall a b, a <= b -> a - b = 0.
Proof.
(* original proof tokens: 12 *)
(* generated proof tokens: 11 *)

intros.
lia.
Qed.

Local Hint Resolve Nat.lt_le_incl.
Local Hint Resolve Nat.mod_upper_bound.
Local Hint Resolve divup_gt_0.
Ltac min_cases :=
    let H := fresh in let H' := fresh in
    edestruct Min.min_spec as [ [H H']|[H H'] ];
    rewrite H' in *; clear H'.
Ltac mult_nonzero := 
    repeat (match goal with
    | [ |- mult _ _ <> 0 ] => apply mult_neq_0
    | [ |- mult _ _ > 0 ] => apply lt_mul_mono
    | [ |- _ ^ _ <> 0 ] => apply Nat.pow_nonzero
    | [ |- _ > 0 ] => unfold gt
    | [ |- 0 < _ ] => apply neq_0_lt
    | [ |- 0 <> _ ] => apply not_eq_sym
    | [ |- _] => solve [auto]
    | [ |- ?N <> 0 ] => subst N
    end).
Ltac divide_solve := match goal with
    | [ |- Nat.divide 1 ?n ] => apply Nat.divide_1_l
    | [ |- Nat.divide ?n 0 ] => apply Nat.divide_0_r
    | [ |- Nat.divide ?a ?a ] => apply Nat.divide_refl
    | [ |- Nat.divide ?a (?b * ?c) ] => solve [apply Nat.divide_mul_l; divide_solve |
                                               apply Nat.divide_mul_r; divide_solve ]
    | [ |- Nat.divide ?a (?b + ?c) ] => apply Nat.divide_add_r; solve [divide_solve]
    | [ |- Nat.divide ?a (?b - ?c) ] => apply Nat.divide_sub_r; solve [divide_solve]
    | [ |- Nat.divide ?n (roundup _ ?n) ] => unfold roundup; solve [divide_solve]
    | [H : ?a mod ?b = 0 |- Nat.divide ?b ?a ] => apply Nat.mod_divide; mult_nonzero; solve [divide_solve]
  end.
Local Hint Extern 1 (Nat.divide ?a ?b) => divide_solve.
Local Hint Extern 1 (?a <= roundup ?a ?b) => apply roundup_ge; mult_nonzero.
Local Hint Extern 1 (?a mod ?b < ?b) => apply Nat.mod_upper_bound; mult_nonzero.
Local Hint Resolve roundup_le.
Ltac incl_solve := match goal with
    | [|- incl ?a ?a ] => apply incl_refl
    | [|- incl (remove _ _ ?l) ?l ] => apply incl_remove
    | [|- incl ?l (_ :: ?l)] => apply incl_tl; solve [incl_solve]
    | [H : incl ?a ?b |- incl ?a ?c ] => eapply incl_tran; [> apply H|]; solve [incl_solve]
    | [H : incl ?b ?c |- incl ?a ?c ] => eapply incl_tran; [> |apply H]; solve [incl_solve]
  end.
Local Hint Extern 1 (incl ?a ?b) => incl_solve.
Ltac psubst :=
    repeat match goal with p: pred |- _ =>
      match goal with
      | H: p <=p=> _ |- _ =>
        rewrite H in *; clear H; clear p
      | H: _ <=p=> p |- _ =>
        rewrite <- H in *; clear H; clear p
      end
    end.
Theorem indrep_n_helper_valid : forall bxp bn Fs l,
    bn <> 0 -> indrep_n_helper Fs bxp bn l <=p=> [[ BALLOCC.bn_valid bxp bn ]] * IndRec.rep bn l * [[ (Fs <=p=> bn |->?) ]].
Proof.
(* original proof tokens: 35 *)

(* No more tactics to try *)
Admitted.

Theorem indrep_n_tree_valid : forall indlvl bxp Fs ir l,
    ir <> 0 -> indrep_n_tree indlvl bxp Fs ir l <=p=> indrep_n_tree indlvl bxp Fs ir l * [[ BALLOCC.bn_valid bxp ir ]].
Proof.
(* original proof tokens: 71 *)

(* No more tactics to try *)
Admitted.

Lemma indrep_n_helper_0 : forall Fs bxp l,
    indrep_n_helper Fs bxp 0 l <=p=> [[ l = repeat $0 NIndirect ]] * [[ Fs <=p=> emp ]].
Proof.
(* original proof tokens: 20 *)
(* generated proof tokens: 60 *)
split; intros; psubst.
apply piff_refl; unfold indrep_n_helper; simpl; intros; split; auto; try congruence.
apply piff_refl; unfold indrep_n_helper; simpl; intros; split; auto; try congruence.
Qed.

Lemma indrep_n_helper_0' : forall bxp l,
    indrep_n_helper emp bxp 0 l <=p=> [[ l = repeat $0 NIndirect ]].
Proof.
(* original proof tokens: 20 *)

(* No more tactics to try *)
Admitted.

Lemma pred_fold_left_Forall_emp: forall AT AEQ V (l : list (@pred AT AEQ V)),
    Forall (fun x => x <=p=> emp) l ->
    pred_fold_left l <=p=> emp.
Proof.
(* original proof tokens: 78 *)
eapply pimpl_refl.
(* No more tactics to try *)
Admitted.

Lemma pred_fold_left_cons: forall AT AEQ V (l : list (@pred AT AEQ V)) x,
    pred_fold_left (x :: l) <=p=> x * pred_fold_left l.
Proof.
(* original proof tokens: 63 *)

(* No more tactics to try *)
Admitted.

Lemma pred_fold_left_repeat_emp: forall AT AEQ V n,
    pred_fold_left (repeat (@emp AT AEQ V) n) <=p=> emp.
Proof.
(* original proof tokens: 28 *)

(* No more tactics to try *)
Admitted.

Lemma pred_fold_left_app: forall AT AEQ V (l l' : list (@pred AT AEQ V)),
    pred_fold_left (l ++ l') <=p=> pred_fold_left l * pred_fold_left l'.
Proof.
(* original proof tokens: 45 *)

(* No more tactics to try *)
Admitted.

Lemma pred_fold_left_selN_removeN: forall AT AEQ V (l : list (@pred AT AEQ V)) i,
    pred_fold_left l <=p=> (selN l i emp) * pred_fold_left (removeN l i).
Proof.
(* original proof tokens: 105 *)

(* No more tactics to try *)
Admitted.

Lemma pred_fold_left_updN_removeN: forall AT AEQ V l (p : @pred AT AEQ V) i,
    i < length l ->
    pred_fold_left (updN l i p) <=p=> pred_fold_left (removeN l i) * p.
Proof.
(* original proof tokens: 42 *)
eapply pimpl_piff_proper; auto.
(* No more tactics to try *)
Admitted.

Lemma in_combine_repeat_l : forall A B (a : A) n (b : list B) x,
    In x (combine (repeat a n) b) ->
    fst x = a.
Proof.
(* original proof tokens: 34 *)

(* No more tactics to try *)
Admitted.

Lemma listmatch_combine_l_length: forall A B C AT AEQ V (prd : _ -> _ -> @pred AT AEQ V) F m
    (a : list A) (b : list B) (c : list C),
    length a = length b ->
    (F * listmatch prd (combine a b) c)%pred m -> length a = length c /\ length b = length c.
Proof.
(* original proof tokens: 46 *)

(* No more tactics to try *)
Admitted.

Lemma listmatch_combine_l_length_l: forall A B C AT AEQ V (prd : _ -> _ -> @pred AT AEQ V) F m
    (a : list A) (b : list B) (c : list C),
    length a = length b ->
    (F * listmatch prd (combine a b) c)%pred m -> length a = length c.
Proof.
(* original proof tokens: 42 *)

(* No more tactics to try *)
Admitted.

Lemma listmatch_combine_l_length_r: forall A B C AT AEQ V (prd : _ -> _ -> @pred AT AEQ V) F m
    (a : list A) (b : list B) (c : list C),
    length a = length b ->
    (F * listmatch prd (combine a b) c)%pred m -> length b = length c.
Proof.
(* original proof tokens: 42 *)

(* No more tactics to try *)
Admitted.

Lemma listmatch_combine_l_length_pimpl: forall A B C AT AEQ V (prd : _ -> _ -> @pred AT AEQ V)
    (a : list A) (b : list B) (c : list C),
    length a = length b ->
    listmatch prd (combine a b) c =p=> [[ length a = length c /\ length b = length c ]]
      * listmatch prd (combine a b) c.
Proof.
(* original proof tokens: 42 *)

(* No more tactics to try *)
Admitted.

Theorem indrep_n_tree_0 : forall indlvl bxp Fs l,
    indrep_n_tree indlvl bxp Fs 0 l <=p=> [[ l = repeat $0 (NIndirect ^ S indlvl)]] * [[ Fs <=p=> emp ]].
Proof.
(* original proof tokens: 448 *)

(* No more tactics to try *)
Admitted.

Lemma listmatch_indrep_n_tree_empty': forall indlvl n bxp,
    listmatch (fun x y => indrep_n_tree indlvl bxp (snd x) # (fst x) y)
      (combine (repeat (@natToWord addrlen 0) n) (repeat emp n)) (repeat (repeat $0 (NIndirect ^ (S indlvl))) n) <=p=> emp.
Proof.
(* original proof tokens: 75 *)

(* No more tactics to try *)
Admitted.

Lemma listmatch_indrep_n_tree_empty'': forall indlvl n fsl l bxp,
    length fsl = n ->
    listmatch (fun x y => indrep_n_tree indlvl bxp (snd x) # (fst x) y)
      (combine (repeat (@natToWord addrlen 0) n) fsl) l =p=> [[ pred_fold_left fsl <=p=> emp ]] *
        [[ l = (repeat (repeat $0 (NIndirect ^ (S indlvl))) n) ]].
Proof.
(* original proof tokens: 296 *)
eapply pimpl_and; auto.
eapply pimpl_and; auto.
eapply pimpl_and; auto.
eapply pimpl_trans; [| eapply start_normalizing_left; [ | eapply pimpl_exists_l; intros; apply sep_star_lift_l; intros; destruct_lift H ] ].
eapply pimpl_refl.
apply piff_refl.
eapply pimpl_trans; [ | eapply restart_canceling ]; eauto.
eapply start_normalizing_right; [ | apply H ]; auto; eauto.
eapply restart_canceling; [| eauto].
eapply start_normalizing_right; [flatten|];eauto.
eapply start_normalizing_right; [flatten|];eauto.
eapply start_normalizing_right; [flatten|];eauto.
eapply start_normalizing_right; [flatten|];eauto.
eapply start_normalizing_right; [flatten|];eauto.
eapply start_normalizing_right; [flatten|];eauto.
eapply start_normalizing_right; [flatten|];eauto.
eapply start_normalizing_right; [flatten|];eauto.
eapply start_normalizing_right; [flatten|];eauto.
eapply start_normalizing_right; [flatten|];eauto.
eapply start_normalizing_right; [flatten|];eauto.
eapply start_normalizing_right; [flatten|];eauto.
eapply start_normalizing_right; [flatten|];eauto.
eapply start_normalizing_right; [flatten|];eauto.
eapply start_normalizing_right; [flatten|];eauto.
eapply start_normalizing_right; [flatten|];eauto.
eapply start_normalizing_right; [flatten|];eauto.
eapply start_normalizing_right; [flatten|];eauto.
eapply start_normalizing_right; [flatten|];eauto.
eapply start_normalizing_right; [flatten|];eauto.
eapply start_normalizing_right; [flatten|];eauto.
eapply start_normalizing_right; [flatten|];eauto.
eapply start_normalizing_right; [flatten|];eauto.
eapply start_normalizing_right; [flatten|];eauto.
eapply start_normalizing_right; [flatten|];eauto.
eapply start_normalizing_right; [flatten|];eauto.
eapply start_normalizing_right; [flatten|];eauto.
eapply start_normalizing_right; [flatten|];eauto.
eapply start_normalizing_right; [flatten|];eauto.
eapply start_normalizing_right; [flatten|];eauto.
eapply start_normalizing_right; [flatten|];eauto.
eapply start_normalizing_right; [flatten|];eauto.
eapply start_normalizing_right; [ | eapply H ]; auto; eauto.
eapply start_normalizing_right; [| eauto | ].
(* Reached max number of model calls *)
Admitted.

Lemma listmatch_indrep_n_tree_empty: forall indlvl bxp,
    let iblocks := (repeat $0 NIndirect) in
    indrep_n_helper emp bxp 0 iblocks *
    listmatch (fun x y => indrep_n_tree indlvl bxp (snd x) # (fst x) y)
      (combine iblocks (repeat emp NIndirect)) (repeat (repeat $0 (NIndirect ^ (S indlvl))) NIndirect) <=p=> emp.
Proof.
(* original proof tokens: 32 *)

(* No more tactics to try *)
Admitted.

Theorem indrep_n_helper_bxp_switch : forall Fs bxp bxp' ir iblocks,
    BmapNBlocks bxp = BmapNBlocks bxp' ->
    indrep_n_helper Fs bxp ir iblocks <=p=> indrep_n_helper Fs bxp' ir iblocks.
Proof.
(* original proof tokens: 28 *)
split; intros; psubst; auto; try apply pimpl_refl.
eapply pimpl_refl.
(* No more tactics to try *)
Admitted.

Theorem indrep_n_tree_bxp_switch : forall bxp bxp' indlvl Fs ir l,
    BmapNBlocks bxp = BmapNBlocks bxp' ->
    indrep_n_tree indlvl bxp Fs ir l <=p=> indrep_n_tree indlvl bxp' Fs ir l.
Proof.
(* original proof tokens: 88 *)

(* No more tactics to try *)
Admitted.

Theorem indrep_n_helper_sm_sync_invariant : forall Fs bxp ir l m F,
    (F * indrep_n_helper Fs bxp ir l)%pred m ->
    sm_sync_invariant Fs.
Proof.
(* original proof tokens: 78 *)

(* No more tactics to try *)
Admitted.

Lemma sm_sync_invariant_pred_fold_left: forall l,
    Forall sm_sync_invariant l ->
    sm_sync_invariant (pred_fold_left l).
Proof.
(* original proof tokens: 80 *)

(* No more tactics to try *)
Admitted.

Theorem indrep_n_tree_sm_sync_invariant : forall bxp indlvl Fs ir l F m,
    (F * indrep_n_tree indlvl bxp Fs ir l)%pred m ->
    sm_sync_invariant Fs.
Proof.
(* original proof tokens: 201 *)

(* No more tactics to try *)
Admitted.

Theorem listpred_indrep_n_tree_0 : forall indlvl bxp Fs l,
    listpred (fun l' => indrep_n_tree indlvl bxp Fs 0 l') l <=p=>
      [[ Forall (fun x => x = repeat $0 (NIndirect ^ S indlvl) /\ (Fs <=p=> emp))%type l ]].
Proof.
(* original proof tokens: 66 *)

(* No more tactics to try *)
Admitted.

Lemma indrep_n_helper_length : forall F Fs bxp ibn l m,
    (F * indrep_n_helper Fs bxp ibn l)%pred m -> length l = NIndirect.
Proof.
(* original proof tokens: 69 *)

(* No more tactics to try *)
Admitted.

Lemma indrep_n_helper_length_piff : forall Fs bxp ibn l,
    indrep_n_helper Fs bxp ibn l <=p=> indrep_n_helper Fs bxp ibn l * [[ length l = NIndirect ]].
Proof.
(* original proof tokens: 49 *)

(* No more tactics to try *)
Admitted.

Lemma indrep_n_length_pimpl : forall indlvl bxp ibn Fs l,
    indrep_n_tree indlvl bxp Fs ibn l <=p=>
    [[ length l = NIndirect ^ (S indlvl) ]] * indrep_n_tree indlvl bxp Fs ibn l.
Proof.
(* original proof tokens: 208 *)

(* No more tactics to try *)
Admitted.

Lemma listmatch_indrep_n_tree_forall_length : forall indlvl bxp (l1 : list (waddr * _)) l2,
    listmatch (fun a l' => indrep_n_tree indlvl bxp (snd a) # (fst a) l') l1 l2 <=p=>
    listmatch (fun a l' => indrep_n_tree indlvl bxp (snd a) # (fst a) l') l1 l2 *
    [[Forall (fun sublist : list waddr => (length sublist = NIndirect * NIndirect ^ indlvl)%nat) l2]].
Proof.
(* original proof tokens: 54 *)

(* No more tactics to try *)
Admitted.

Local Hint Extern 1 (Forall (fun x => length x = _) _) => match goal with
    | [H : context [listmatch (fun x y => indrep_n_tree _ _ (snd x) # (fst x) y) _ ?l]
        |- Forall (fun x => length x = _) ?l ] =>
          rewrite listmatch_indrep_n_tree_forall_length with (l2 := l) in H; destruct_lift H; solve [eassumption]
    | [|- Forall _ (upd_range ?l _ _ _)] => apply forall_upd_range; autorewrite with lists; eauto
  end.
Theorem indrep_n_helper_pts_piff : forall Fs bxp ir l,
    ir <> 0 -> indrep_n_helper Fs bxp ir l <=p=> [[ length l = NIndirect ]] *
                [[ BALLOCC.bn_valid bxp ir ]] * [[ Fs <=p=> ir |->? ]] *
                ir |-> (IndRec.Defs.block2val l, []).
Proof.
(* original proof tokens: 103 *)

(* No more tactics to try *)
Admitted.

Lemma indrep_n_tree_balloc_goodSize: forall F1 F2 bxp freelist ms indlvl Fs ir l m1 m2,
    (F1 * BALLOCC.rep bxp freelist ms)%pred m1 ->
     (F2 * indrep_n_tree indlvl bxp Fs ir l)%pred m2 ->
      goodSize addrlen ir.
Proof.
(* original proof tokens: 66 *)

(* No more tactics to try *)
Admitted.

Lemma indrep_n_tree_length: forall indlvl F ir l1 l2 lfs bxp Fs m,
    length lfs = NIndirect ->
    (F *
    indrep_n_helper Fs bxp ir l1 *
    listmatch
     (fun x l' => indrep_n_tree indlvl bxp (snd x) # (fst x) l') (combine l1 lfs) l2)%pred m->
     length (concat l2) = NIndirect * (NIndirect ^ (S indlvl)).
Proof.
(* original proof tokens: 133 *)

(* No more tactics to try *)
Admitted.

Lemma indrep_n_indlist_forall_length : forall F indlvl Fs bxp ir l1 fsl l2 m,
    length fsl = NIndirect ->
    ((F ✶ indrep_n_helper Fs bxp ir l1)
        ✶ listmatch
            (fun x l' => indrep_n_tree indlvl bxp (snd x) # (fst x) l') (combine l1 fsl) l2)%pred m ->
    Forall (fun sublist : list waddr => length sublist = NIndirect * NIndirect ^ indlvl) l2.
Proof.
(* original proof tokens: 57 *)

(* No more tactics to try *)
Admitted.

Lemma indrep_n_indlist_forall_length' : forall F F' indlvl Fs bxp ir fsl l1 l2 m,
    length fsl = NIndirect ->
    (((F ✶ indrep_n_helper Fs bxp ir l1)
        ✶ listmatch
            (fun x l' => indrep_n_tree indlvl bxp (snd x) # (fst x) l') (combine l1 fsl) l2) * F')%pred m ->
    Forall (fun sublist : list waddr => length sublist = NIndirect * NIndirect ^ indlvl) l2.
Proof.
(* original proof tokens: 37 *)

(* No more tactics to try *)
Admitted.

Lemma indrep_index_bound_helper : forall Fm Fs off indlvl bxp bn iblocks fsl l_part m,
      off < length (concat l_part) ->
      length fsl = NIndirect ->
      ((Fm * indrep_n_helper Fs bxp bn iblocks) *
       listmatch (fun x l' =>
                    indrep_n_tree indlvl bxp (snd x) # (fst x) l') (combine iblocks fsl) l_part)%pred m
      -> off / (NIndirect * NIndirect ^ indlvl) < NIndirect.
Proof.
(* original proof tokens: 46 *)

(* No more tactics to try *)
Admitted.

Lemma indrep_index_bound_helper' : forall Fm Fm' off indlvl bxp Fs bn iblocks l_part fsl m,
      off < length (concat l_part) ->
      length fsl = NIndirect ->
    ((Fm * indrep_n_helper Fs bxp bn iblocks) *
          listmatch (fun x (l' : list waddr) =>
            indrep_n_tree indlvl bxp (snd x) # (fst x) l') (combine iblocks fsl) l_part *
            Fm')%pred m
    -> off / (NIndirect * NIndirect ^ indlvl) < NIndirect.
Proof.
(* original proof tokens: 33 *)

(* No more tactics to try *)
Admitted.

Local Hint Resolve indrep_n_indlist_forall_length indrep_n_indlist_forall_length'.
Lemma indrep_n_roundup_helper_1 : forall a b n, n <> 0 ->
    n - a mod n < b -> roundup a n - a <= b.
Proof.
(* original proof tokens: 61 *)

(* No more tactics to try *)
Admitted.

Local Hint Resolve indrep_n_roundup_helper_1.
Theorem roundup_round : forall a n, roundup a n / n * n = roundup a n.
Proof.
(* original proof tokens: 40 *)

(* No more tactics to try *)
Admitted.

Theorem indclear_upd_range_helper_1 : forall T l l' l'' start (v : T) n k d,
    k <> 0 -> n <> 0 ->
    start mod (n * k) <> 0 ->
    start <= length (concat l) ->
    length l'' = n * k ->
    concat l' = upd_range l'' (start mod (n * k)) (roundup (start mod (n * k)) k - start mod (n * k)) v ->
    selN l (start / (n * k)) d = l'' ->
    Forall (fun x => length x = k) l' ->
    Forall (fun x => length x = n * k) l ->
    concat (updN l (start / (n * k)) (
      concat (upd_range l' (divup (start mod (n * k)) k) (n - divup (start mod (n * k)) k)
                (repeat v k)
    ))) = upd_range (concat l) start (n * k - start mod (n * k)) v.
Proof.
(* original proof tokens: 361 *)

(* No more tactics to try *)
Admitted.

Theorem indrep_bound_helper_1 : forall a b n N,
    N <> 0 ->
    b <> 0 ->
    a + b <= n * N ->
    N - a mod N < b ->
    (a + (N - a mod N)) / N + (b - (N - a mod N)) / N <= n.
Proof.
(* original proof tokens: 179 *)

(* No more tactics to try *)
Admitted.

Theorem xform_indrep_n_helper : forall Fs bxp ir l,
    crash_xform (indrep_n_helper Fs bxp ir l) <=p=> indrep_n_helper Fs bxp ir l.
Proof.
(* original proof tokens: 41 *)

(* No more tactics to try *)
Admitted.

Theorem xform_indrep_n_tree : forall xp indlvl Fs ir l,
    crash_xform (indrep_n_tree indlvl xp Fs ir l) <=p=> indrep_n_tree indlvl xp Fs ir l.
Proof.
(* original proof tokens: 129 *)

(* No more tactics to try *)
Admitted.

Hint Rewrite Nat.mul_1_r.
Ltac indrep_n_tree_bound_step := match goal with
    | [ |- _ ] => reflexivity
    | [ |- _ ] => assumption
    | [ |- Forall _ _ ] => auto
    | [ H : context [IndRec.Defs.item] |- _ ] => unfold IndRec.Defs.item in *; simpl Rec.data in *
    | [ |- context [IndRec.Defs.item] ] => unfold IndRec.Defs.item in *; simpl Rec.data in *
    | [ |- context [length (combine ?a ?b)] ] => rewrite combine_length_eq by congruence
    | [ |- _ ] => progress autorewrite with core lists
    | [ |- ?a * ?b = ?c * ?b ] => rewrite Nat.mul_cancel_r by mult_nonzero
    | [ |- ?a * ?b = ?b * ?c ] => rewrite mult_comm with (n := b) (m := c)
    | [ |- ?b * ?a = ?b * ?c ] => rewrite mult_comm with (n := b) (m := a)
    | [ H : ?a < ?b * ?c |- ?a < ?d * ?c] => replace d with b; [ eauto | ]
    | [ H : ?a < ?x |- ?a < ?y ] => replace y with x; [ auto | ]
    | [ H : ?a <= ?x |- ?a <= ?y ] => replace y with x; [ auto | ]
    | [ H : context [indrep_n_tree _ _ _ _ ?l] |- context [length ?l] ] =>
      rewrite indrep_n_tree_length in H; destruct_lift H
    | [ H : context [indrep_n_helper _ _ _ ?l] |- context [length ?l] ] =>
      replace (length l) with NIndirect by (erewrite indrep_n_helper_length; auto; pred_apply' H; cancel)
    | [ |- ?off / ?N < ?N' ] => apply Nat.div_lt_upper_bound; [ mult_nonzero |]
    | [ |- ?off < ?N * NIndirect] => rewrite mult_comm
    | [ |- context [Nat.min ?a ?b] ] => rewrite Nat.min_r by auto
    | [ |- context [Nat.min ?a ?b] ] => rewrite Nat.min_l by auto
    | [ H : ?a + ?b <= ?c |- ?a < ?d ] => eapply lt_le_trans with (m := a + b); [lia |]
    
    | [ H : context [listmatch ?P (combine ?A ?B) ?C] |- context [length ?C] ] =>
      replace (length C) with (length A) in * by (
        erewrite listmatch_combine_l_length_l with (a := A) (b := B) (c := C) (prd := P); auto;
        pred_apply' H; cancel)
    | [ H : context [listmatch ?P (combine ?A ?B) ?c] |- context [length ?C] ] =>
      replace (length c) with (length B) in * by (
        erewrite listmatch_combine_l_length_r with (a := A) (b := B) (c := C) (prd := P); auto;
        pred_apply' H; cancel)
    | [ H : context [listmatch _ (combine ?A ?B) _] |- context [length ?B] ] =>
      replace (length B) with (length A) by auto

    | [ H : context [listmatch _ ?A ?b] |- context [length ?b] ] =>
      replace (length b) with (length A) in * by (
        erewrite listmatch_length with (a := A); auto; pred_apply' H; cancel)
    | [ H : context [listmatch _ ?A ?b], H': context [length ?b] |- _ ] =>
      replace (length b) with (length A) in * by (
        erewrite listmatch_length with (a := A); auto; pred_apply' H; cancel)

    | [ H : context [lift_empty _] |- _ ] => progress destruct_lift H
    | [ |- context [length (concat _)] ] => erewrite concat_hom_length; eauto
    | [ |- context [Nat.min _ _] ] => rewrite min_l by lia
    | [ H: context [Nat.min _ _] |- _ ] => rewrite min_l in H by lia
    | [ |- _ ] => lia
    | [ |- ?a < ?b * ?c ] => rewrite mult_comm; lia
    | [ H : context [length (concat ?l)] |- _ ] => erewrite concat_hom_length in H by eauto
    end.
Ltac indrep_n_tree_bound :=
    match goal with
    | [l : list _ |- context [?x] ] => is_evar x; unify x l; solve [indrep_n_tree_bound]
    | _ => repeat indrep_n_tree_bound_step
  end.
Ltac indrep_n_extract := match goal with
    | [|- context [listmatch _ ?l] ] =>
      match goal with [l : list _ |- context [listmatch _ (removeN ?l ?n)] ] =>
        rewrite listmatch_isolate with (i := n) (a := l);
        autorewrite with lists in *; try lia; try erewrite snd_pair by eauto
      end
    | [|- context [selN ?l ?n] ] => rewrite listmatch_isolate with (i := n) (a := l);
        autorewrite with lists in *; try lia; try erewrite snd_pair by eauto
    | [|- context [selN ?l ?n] ] => rewrite listmatch_isolate with (i := n) (a := combine l _);
        autorewrite with lists in *; try rewrite selN_combine; try lia; try erewrite snd_pair by eauto;
        cbn [fst snd] in *
    | [H: context [listmatch _ (combine ?l _)] |- context [selN ?l ?n] ] =>
        rewrite listmatch_isolate with (i := n) (a := combine l _) in H;
        autorewrite with lists in *; erewrite ?selN_combine in H; try lia; erewrite ?snd_pair by eauto;
        cbn [fst snd] in *
    | [H: context [listmatch _ _ ?l] |- context [selN ?l ?n] ] =>
        rewrite listmatch_isolate with (i := n) (b := l) in H;
        autorewrite with lists in *; erewrite ?selN_combine in H; try lia; erewrite ?snd_pair by eauto;
        cbn [fst snd] in *
  end.
Ltac indrep_n_tree_extract_lengths :=
    repeat match goal with [H : context [indrep_n_tree _ _ _ _ ?x] |- _] =>
      match goal with
      | [H' : length ?y = _ |- _] => tryif (unify x y) then fail 1 else fail
      | [|- _] => rewrite indrep_n_length_pimpl with (l := x) in H; destruct_lift H
      end
    end; try rewrite mult_1_r in *.
Theorem indrep_n_tree_repeat_concat:
    forall indlvl F Fs lfs l1 l2 bxp m,
    length lfs = NIndirect ->
    ((F ✶ indrep_n_helper Fs bxp 0 l1)
     ✶ listmatch (fun x y => indrep_n_tree indlvl bxp (snd x) # (fst x) y) (combine l1 lfs) l2)%pred m ->
    concat l2 = repeat $0 (NIndirect * NIndirect ^ S indlvl).
Proof.
(* original proof tokens: 131 *)

(* No more tactics to try *)
Admitted.

Theorem indrep_n_tree_repeat_Fs:
    forall indlvl F Fs lfs l1 l2 bxp m,
    length lfs = NIndirect ->
    ((F ✶ indrep_n_helper Fs bxp 0 l1)
     ✶ listmatch (fun x y => indrep_n_tree indlvl bxp (snd x) # (fst x) y) (combine l1 lfs) l2)%pred m ->
    Fs * pred_fold_left lfs <=p=> emp.
Proof.
(* original proof tokens: 157 *)

(* No more tactics to try *)
Admitted.

Local Hint Extern 1 (BALLOCC.bn_valid _ _) => match goal with
    [H : context [indrep_n_helper _ _ ?ir] |- BALLOCC.bn_valid _ ?ir] =>
    rewrite indrep_n_helper_valid in H by lia; destruct_lift H; auto end.
Local Hint Extern 1 (goodSize _ _) => match goal with
  | [H: context [indrep_n_tree _ _ _ ?i] |- goodSize _ ?i ] =>
    match goal with H' : context [BALLOCC.rep ?B ?l] |- _ =>
      eapply indrep_n_tree_balloc_goodSize with (bxp := B) (freelist := l); eapply pimpl_apply;
      [| exact H' | | exact H]; cancel
    end
  end.
Hint Rewrite le_plus_minus_r using auto.
Local Hint Extern 1 (?a mod ?b < ?b) => apply Nat.mod_bound_pos; mult_nonzero.
Local Hint Extern 1 (0 < ?n - ?m) => (apply Nat.lt_add_lt_sub_r; simpl; auto).
Local Hint Resolve repeat_selN'.
Local Hint Extern 1 (Forall (fun x => length x = _) _) => eapply indrep_n_indlist_forall_length.
Lemma IndRec_items_valid_repeat : forall bn x,
    bn <> 0 -> IndRec.items_valid bn (repeat x NIndirect).
Proof.
(* original proof tokens: 44 *)

(* No more tactics to try *)
Admitted.

Local Hint Resolve IndRec_items_valid_repeat IndRec.items_valid_updN IndRec.items_valid_upd_range.
Local Hint Extern 1 (Rec.well_formed _) => unfold Rec.well_formed; cbn.
Lemma indrep_n_helper_items_valid : forall Fs bxp bn l,
    bn <> 0 ->
    indrep_n_helper Fs bxp bn l <=p=> [[ IndRec.items_valid bn l]] * indrep_n_helper Fs bxp bn l.
Proof.
(* original proof tokens: 56 *)

(* No more tactics to try *)
Admitted.

Local Hint Extern 1 (IndRec.items_valid _ _) => match goal with
    [H : context [indrep_n_helper _ _ ?bn] |- IndRec.items_valid ?bn _] =>
    rewrite indrep_n_helper_items_valid in H; destruct_lift H end.
Fixpoint indget (indlvl : nat) lxp (bn : addr) off ms :=
    If (addr_eq_dec bn 0) {
      Ret ^(ms, $ 0)
    } else {
      let divisor := NIndirect ^ indlvl in
      let^ (ms, v) <- IndRec.get lxp bn (off / divisor) ms;
      match indlvl with
      | 0 => Ret ^(ms, v)
      | S indlvl' => indget indlvl' lxp (# v) (off mod divisor) ms
      end
    }.
Theorem indget_ok : forall indlvl lxp bxp bn off ms,
    {< F Fm Fs m0 sm m l,
    PRE:hm
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms sm hm *
           [[[ m ::: Fm * indrep_n_tree indlvl Fs bxp bn l ]]] *
           [[ off < length l ]]
    POST:hm' RET:^(ms, r)
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms sm hm' *
           [[ r = selN l off $0 ]]
    CRASH:hm'  exists ms',
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms' sm hm'
    >} indget indlvl lxp bn off ms.
Proof.
(* original proof tokens: 318 *)

(* No more tactics to try *)
Admitted.

Local Hint Extern 1 ({{_}} Bind (indget _ _ _ _ _ ) _) => apply indget_ok : prog.
Opaque indget.
Fixpoint indread (indlvl : nat) lxp (ir : addr) ms :=
    If (addr_eq_dec ir 0) {
      Ret ^(ms, repeat $0 (NIndirect ^ S indlvl))
    } else {
      let^ (ms, indbns) <- IndRec.read lxp ir 1 ms;
      match indlvl with
        | 0 => Ret ^(ms, indbns)
        | S indlvl' =>
          let N := (NIndirect ^ (S indlvl')) in
          r <- ForEach b indbns' (rev indbns)
            Hashmap hm
            Ghost [ F Fm Fs fsl iblocks l_part l bxp crash m0 sm m ]
            Loopvar [ ms r ]
            Invariant
              exists remlen, [[ remlen = length indbns' ]] *
              LOG.rep lxp F (LOG.ActiveTxn m0 m) ms sm hm *
              [[[ m ::: Fm * indrep_n_helper Fs bxp ir iblocks *
                        listmatch (fun x l' => indrep_n_tree indlvl' bxp (snd x) (# (fst x)) l')
                          (combine iblocks fsl) l_part ]]] *
              [[ r = skipn (remlen * (NIndirect ^ indlvl)) l ]]
            OnCrash crash
            Begin
              let^ (ms, v) <- indread indlvl' lxp (# b) ms;
              Ret ^(ms, v ++ r)
            Rof ^(ms, nil);
            Ret r
      end
    }.
Theorem indread_ok : forall indlvl lxp bxp ir ms,
  {< F Fm Fs m0 sm m l,
    PRE:hm
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms sm hm *
           [[[ m ::: Fm * indrep_n_tree indlvl Fs bxp ir l ]]]
    POST:hm' RET:^(ms, r)
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms sm hm' *
           [[ r = l ]]
    CRASH:hm'  exists ms',
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms' sm hm'
    >} indread indlvl lxp ir ms.
Proof.
(* original proof tokens: 562 *)

(* No more tactics to try *)
Admitted.

Local Hint Extern 1 ({{_}} Bind (indread _ _ _ _ ) _) => apply indread_ok : prog.
Opaque indread.
Definition indread_aligned indlvl lxp (indbns : list waddr) ms :=
    ForEach bn rest (rev indbns)
      Hashmap hm
      Ghost [ F Fm l_part fsl bxp crash m0 sm m ]
      Loopvar [ ms r ]
      Invariant
        LOG.rep lxp F (LOG.ActiveTxn m0 m) ms sm hm *
        [[ length indbns = length fsl ]] *
        [[ r = concat (skipn (length rest) l_part) ]] *
        [[[ m ::: Fm * listmatch (fun x l' => indrep_n_tree indlvl bxp (snd x) # (fst x) l') (combine (rev indbns) (rev fsl)) (rev l_part) ]]]
      OnCrash crash
      Begin
        let^ (ms, blks) <- indread indlvl lxp # bn ms;
        Ret ^(ms, blks ++ r)
      Rof ^(ms, nil).
Hint Rewrite rev_length rev_involutive rev_app_distr : lists.
Theorem indread_aligned_ok : forall indlvl lxp indbns ms,
    {< F Fm m0 sm m bxp fsl l_part,
    PRE:hm
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms sm hm *
           [[[ m ::: (Fm * listmatch (fun x l => indrep_n_tree indlvl bxp (snd x) # (fst x) l) (combine indbns fsl) l_part) ]]] *
           [[ length fsl = length indbns ]]
    POST:hm' RET:^(ms, r)
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms sm hm' *
           [[ r = concat l_part ]]
    CRASH:hm'  LOG.intact lxp F m0 sm hm'
    >} indread_aligned indlvl lxp indbns ms.
Proof.
(* original proof tokens: 476 *)

(* No more tactics to try *)
Admitted.

Local Hint Extern 1 ({{_}} Bind (indread_aligned _ _ _ _ ) _) => apply indread_aligned_ok : prog.
Fixpoint indread_to_aligned indlvl lxp ir start ms :=
    let N := (NIndirect ^ S indlvl) in
    If (addr_eq_dec ir 0) {
      Ret ^(ms, repeat $0 (N - start))
    } else {
      let^ (ms, indbns) <- IndRec.read lxp ir 1 ms;
      match indlvl with
      | 0 =>
        Ret ^(ms, skipn start indbns)
      | S indlvl' =>
        let N := (NIndirect ^ S indlvl') in
        let^ (ms, r) <- indread_aligned indlvl' lxp (skipn (S (start / N)) indbns) ms;
        let ir' := selN indbns (start / N) $0 in
        let^ (ms, r') <- indread_to_aligned indlvl' lxp # ir' (start mod N) ms;
        Ret ^(ms, r' ++ r)
      end
    }.
Theorem indread_to_aligned_ok : forall indlvl lxp ir start ms,
    let N := NIndirect ^ S indlvl in
    {< F Fm IFs m0 sm m bxp l,
    PRE:hm
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms sm hm *
           [[[ m ::: Fm * indrep_n_tree indlvl bxp IFs ir l ]]] *
           [[ start < length l ]]
    POST:hm' RET:^(ms, r)
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms sm hm' *
           [[ r = skipn start l ]]
    CRASH:hm'  LOG.intact lxp F m0 sm hm'
    >} indread_to_aligned indlvl lxp ir start ms.
Proof.
(* original proof tokens: 382 *)

(* No more tactics to try *)
Admitted.

Opaque indread_to_aligned.
Local Hint Extern 1 ({{_}} Bind (indread_to_aligned _ _ _ _ _ ) _) => apply indread_to_aligned_ok : prog.
Fixpoint indread_from_aligned indlvl lxp ir len ms :=
    let N := (NIndirect ^ S indlvl) in
    If (addr_eq_dec ir 0) {
      Ret ^(ms, repeat $0 len)
    } else {
      let^ (ms, indbns) <- IndRec.read lxp ir 1 ms;
      match indlvl with
      | 0 =>
        Ret ^(ms, firstn len indbns)
      | S indlvl' =>
        let N := (NIndirect ^ S indlvl') in
        let^ (ms, r) <- indread_aligned indlvl' lxp (firstn (len / N) indbns) ms;
        If (addr_eq_dec (len mod N) 0) {
          Ret ^(ms, r)
        } else {
          let ir' := selN indbns (len / N) $0 in
          let^ (ms, r') <- indread_from_aligned indlvl' lxp # ir' (len mod N) ms;
          Ret ^(ms, r ++ r')
        }
      end
    }.
Theorem indread_from_aligned_ok : forall indlvl lxp ir len ms,
    let N := NIndirect ^ S indlvl in
    {< F Fm IFs m0 sm m bxp l,
    PRE:hm
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms sm hm *
           [[[ m ::: Fm * indrep_n_tree indlvl bxp IFs ir l ]]] *
           [[ len <= length l ]]
    POST:hm' RET:^(ms, r)
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms sm hm' *
           [[ r = firstn len l ]]
    CRASH:hm'  LOG.intact lxp F m0 sm hm'
    >} indread_from_aligned indlvl lxp ir len ms.
Proof.
(* original proof tokens: 467 *)

(* No more tactics to try *)
Admitted.

Local Hint Extern 1 ({{_}} Bind (indread_from_aligned _ _ _ _ _ ) _) => apply indread_from_aligned_ok : prog.
Definition indread_multiple_blocks indlvl lxp (indbns : list waddr) start len ms :=
    let N := NIndirect ^ S indlvl in
    
    let^ (ms, rl) <- indread_to_aligned indlvl lxp #(selN indbns (start / N) $0) (start mod N) ms;
    let start' := start + (N - start mod N) in
    let len' := len - (N - start mod N) in
    let^ (ms, rm) <- indread_aligned indlvl lxp (firstn (len' / N) (skipn (start' / N) indbns)) ms;
    let len'' := len' mod N in
    let start'' := start' + (len' / N * N) in
    let^ (ms, rr) <- indread_from_aligned indlvl lxp #(selN indbns (start'' / N) $0) len'' ms;
    Ret ^(ms, rl ++ (rm ++ rr)).
Theorem indread_multiple_blocks_ok : forall indlvl lxp indbns start len ms,
    let N := NIndirect ^ S indlvl in
    {< F Fm m0 sm m bxp l_part fsl,
    PRE:hm
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms sm hm *
           [[[ m ::: (Fm * listmatch (fun x l => indrep_n_tree indlvl bxp (snd x) #(fst x) l) (combine indbns fsl) l_part) ]]] *
           [[ start < length (concat l_part) ]] *
           [[ (N - start mod N) < len ]] *
           [[ start + len < length (concat l_part) ]] *
           [[ length indbns = length fsl ]]
    POST:hm' RET:^(ms, r)
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms sm hm' *
           [[ r = firstn len (skipn start (concat l_part)) ]]
    CRASH:hm'  LOG.intact lxp F m0 sm hm'
    >} indread_multiple_blocks indlvl lxp indbns start len ms.
Proof.
(* original proof tokens: 732 *)

(* No more tactics to try *)
Admitted.

Local Hint Extern 1 ({{_}} Bind (indread_multiple_blocks _ _ _ _ _ _ ) _) => apply indread_multiple_blocks_ok : prog.
Fixpoint indread_range indlvl lxp (root : addr) start len ms :=
    let N := NIndirect ^ indlvl in
    If (addr_eq_dec len 0) {
      Ret ^(ms, nil)
    } else {
      
      If (addr_eq_dec (start + len) (NIndirect * N)) {
        indread_to_aligned indlvl lxp root start ms
      } else {
        If (addr_eq_dec root 0) {
          Ret ^(ms, repeat $0 len)
        } else {
          let^ (ms, indbns) <- IndRec.read lxp root 1 ms;
          match indlvl with
          | 0 =>
             Ret ^(ms, firstn len (skipn start indbns))
          | S indlvl' =>
            If (le_dec len (N - start mod N)) {
              indread_range indlvl' lxp #(selN indbns (start / N) $0) (start mod N) len ms
            } else {
              indread_multiple_blocks indlvl' lxp indbns start len ms
            }
          end
        }
      }
    }.
Theorem indread_range_ok : forall indlvl lxp ir start len ms,
  {< F Fm Fs m0 sm m bxp l,
    PRE:hm
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms sm hm *
           [[[ m ::: Fm * indrep_n_tree indlvl Fs bxp ir l ]]] *
           [[ start + len <= length l ]]
    POST:hm' RET:^(ms, r)
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms sm hm' *
           [[ r = firstn len (skipn start l) ]]
    CRASH:hm'  LOG.intact lxp F m0 sm hm'
    >} indread_range indlvl lxp ir start len ms.
Proof.
(* original proof tokens: 422 *)

(* No more tactics to try *)
Admitted.

Local Hint Extern 1 ({{_}} Bind (indread_range _ _ _ _ _ _ ) _) => apply indread_range_ok : prog.
Fixpoint indclear_all indlvl lxp bxp root ms :=
    If (addr_eq_dec root 0) {
      Ret ms
    } else {
      let N := NIndirect ^ indlvl in
      ms <- match indlvl with
      | 0 => Ret ms
      | S indlvl' =>
        let^ (lms, indbns) <- IndRec.read lxp root 1 (BALLOCC.MSLog ms);
        let msn := BALLOCC.upd_memstate lms ms in
        let^ (msn) <- ForEach bn indbns' indbns
          Hashmap hm
          Ghost [ F Fm Fs bxp crash m0 sm freelist l_part fsl ]
          Loopvar [ msn ]
          Invariant
            exists m freelist',
            LOG.rep lxp F (LOG.ActiveTxn m0 m) (BALLOCC.MSLog msn) sm hm *
            let n := length indbns - length indbns' in
            [[[ m ::: Fm * listmatch (fun x l' => indrep_n_tree indlvl' bxp (snd x) (# (fst x)) l')
                          (combine (skipn n indbns) (skipn n fsl)) (skipn n l_part)
                         * BALLOCC.rep bxp freelist' msn ]]] *
            [[ incl freelist freelist' ]] *
            [[ (Fs * pred_fold_left (skipn n fsl) * BALLOCC.smrep freelist')%pred sm ]]
          OnCrash crash
          Begin
            msn <- indclear_all indlvl' lxp bxp # bn msn;
            Ret ^(msn)
          Rof ^(msn);
          Ret msn
      end;
      BALLOCC.free lxp bxp root ms
    }.
Theorem indclear_all_ok : forall indlvl lxp bxp ir ms,
    let N := NIndirect ^ indlvl in
    {< F Fm Fs IFS m0 sm m l freelist,
    PRE:hm
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (BALLOCC.MSLog ms) sm hm *
           [[[ m ::: (Fm * indrep_n_tree indlvl bxp IFS ir l *
              BALLOCC.rep bxp freelist ms) ]]] *
           [[ (Fs * IFS * BALLOCC.smrep freelist)%pred sm ]]
    POST:hm' RET: ms
           exists m' freelist' l',
           LOG.rep lxp F (LOG.ActiveTxn m0 m') (BALLOCC.MSLog ms) sm hm' *
           [[[ m' ::: (Fm * indrep_n_tree indlvl bxp emp 0 l' *
              BALLOCC.rep bxp freelist' ms) ]]] *
           [[ (Fs * BALLOCC.smrep freelist')%pred sm ]] *
           [[ incl freelist freelist' ]]
    CRASH:hm'  LOG.intact lxp F m0 sm hm'
    >} indclear_all indlvl lxp bxp ir ms.
Proof.
(* original proof tokens: 914 *)

(* No more tactics to try *)
Admitted.

Local Hint Extern 1 ({{_}} Bind (indclear_all _ _ _ _ _ ) _) => apply indclear_all_ok : prog.
Definition indclear_aligned indlvl lxp bxp (indbns : list waddr) start len ms :=
    let N := NIndirect ^ S indlvl in
    let indbns := firstn (len / N) (skipn (start / N) indbns) in
    ForEach bn rest indbns
      Hashmap hm
      Ghost [ F Fm Fs l_part fsl bxp crash m0 sm freelist ]
      Loopvar [ ms ]
      Invariant
        exists l_part' indbns' fsl' freelist' m,
        LOG.rep lxp F (LOG.ActiveTxn m0 m) (BALLOCC.MSLog ms) sm hm *
        let n := length indbns - length rest in
        [[ l_part' = skipn n l_part ]] *
        [[ indbns' = skipn n indbns ]] *
        [[ fsl' = skipn n fsl ]] *
        [[[ m ::: Fm * listmatch (fun x l' => indrep_n_tree indlvl bxp (snd x) # (fst x) l') (combine indbns' fsl') l_part' *
                  BALLOCC.rep bxp freelist' ms ]]] *
        [[ (Fs * pred_fold_left fsl' * BALLOCC.smrep freelist')%pred sm ]] *
        [[ incl freelist freelist' ]]
      OnCrash crash
      Begin
        ms <- indclear_all indlvl lxp bxp # bn ms;
        Ret ^(ms)
      Rof ^(ms).
Theorem indclear_aligned_ok : forall indlvl lxp bxp indbns start len ms,
    let N := NIndirect ^ S indlvl in
    {< F Fm Fs m0 sm m l_part fsl freelist,
    PRE:hm
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (BALLOCC.MSLog ms) sm hm *
           [[[ m ::: (Fm * listmatch (fun x l => indrep_n_tree indlvl bxp (snd x) # (fst x) l) (combine indbns fsl) l_part
                         * BALLOCC.rep bxp freelist ms) ]]] *
           [[ start / N + len / N <= length l_part ]] * [[ Nat.divide N start ]] * [[ Nat.divide N len ]] *
           [[ length fsl = length indbns ]] *
           [[ (Fs * BALLOCC.smrep freelist * pred_fold_left fsl)%pred sm ]]
    POST:hm' RET:^(ms)
           exists m' freelist' indbns' fsl' l_part', 
           LOG.rep lxp F (LOG.ActiveTxn m0 m') (BALLOCC.MSLog ms) sm hm' *
           [[[ m' ::: (Fm * listmatch (fun x l => indrep_n_tree indlvl bxp (snd x) #(fst x) l) (combine indbns' fsl') l_part'
                          * BALLOCC.rep bxp freelist' ms) ]]] *
           [[ indbns' = upd_range indbns (start / N) (len / N) $0 ]] *
           [[ l_part' = upd_range l_part (start / N) (len / N) (repeat $0 N) ]] *
           [[ incl freelist freelist' ]] *
           [[ length fsl' = length indbns' ]] *
           [[ (Fs * BALLOCC.smrep freelist' * pred_fold_left fsl')%pred sm ]]
    CRASH:hm'  LOG.intact lxp F m0 sm hm'
    >} indclear_aligned indlvl lxp bxp indbns start len ms.
Proof.
(* original proof tokens: 951 *)

(* No more tactics to try *)
Admitted.

Local Hint Extern 1 ({{_}} Bind (indclear_aligned _ _ _ _ _ _ _ ) _) => apply indclear_aligned_ok : prog.
Definition update_block lxp bxp bn contents new ms :=
    If (list_eq_dec waddr_eq_dec new (repeat $0 NIndirect)) {
      ms <- BALLOCC.free lxp bxp bn ms;
      Ret ^(ms, 0)
    } else {
      If (list_eq_dec waddr_eq_dec contents new) {
        Ret ^(ms, bn)
      } else {
        lms <- IndRec.write lxp bn new (BALLOCC.MSLog ms);
        Ret ^(BALLOCC.upd_memstate lms ms, bn)
      }
    }.
Lemma indrep_n_helper_valid_sm: forall Fs bxp ir l,
    ir <> 0 ->
    indrep_n_helper Fs bxp ir l =p=> indrep_n_helper Fs bxp ir l * [[ Fs <=p=> ir |->? ]].
Proof.
(* original proof tokens: 31 *)
eapply pimpl_and; try apply pimpl_refl; try apply indrep_n_helper_valid.
(* No more tactics to try *)
Admitted.

Theorem update_block_ok : forall lxp bxp ir indbns indbns' ms,
    {< F Fm Fs IFs m0 sm m freelist,
    PRE:hm
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (BALLOCC.MSLog ms) sm hm *
            [[ BALLOCC.bn_valid bxp ir ]] *
            [[ IndRec.items_valid ir indbns' ]] *
           [[[ m ::: (Fm * indrep_n_helper IFs bxp ir indbns) *
              BALLOCC.rep bxp freelist ms ]]] *
            [[ (Fs * BALLOCC.smrep freelist * IFs)%pred sm ]]
    POST:hm' RET: ^(ms, ir')
           exists m' freelist' IFs',
           LOG.rep lxp F (LOG.ActiveTxn m0 m') (BALLOCC.MSLog ms) sm hm' *
           [[[ m' ::: (Fm * indrep_n_helper IFs' bxp ir' indbns' *
              BALLOCC.rep bxp freelist' ms) ]]] *
           [[ (Fs * BALLOCC.smrep freelist' * IFs')%pred sm ]] *
           [[ incl freelist freelist' ]] *
           ([[ ir' = 0 ]] \/ [[ ir' = ir ]])
    CRASH:hm'  LOG.intact lxp F m0 sm hm'
    >} update_block lxp bxp ir indbns indbns' ms.
Proof.
(* original proof tokens: 207 *)

(* No more tactics to try *)
Admitted.

Local Hint Extern 1 ({{_}} Bind (update_block _ _ _ _ _ _) _) => apply update_block_ok : prog.
Fixpoint indclear_from_aligned indlvl lxp bxp iblocks start len ms :=
    
    If (addr_eq_dec len 0) {
      Ret ^(ms, iblocks)
    } else {
      let N := (NIndirect ^ S indlvl) in
      let ragged_bn := #(selN iblocks (start / N) $0) in
      If (addr_eq_dec ragged_bn 0) {
        Ret ^(ms, iblocks)
      } else {
        let^ (lms, indbns) <- IndRec.read lxp ragged_bn 1 (BALLOCC.MSLog ms);
        let ms := BALLOCC.upd_memstate lms ms in
        match indlvl with
        | 0 => 
          let indbns' := upd_range indbns 0 len $0 in
          let^ (ms, v) <- update_block lxp bxp ragged_bn indbns indbns' ms;
          Ret ^(ms, updN iblocks (start / N) $ v)
        | S indlvl' =>
          let N' := NIndirect ^ (S indlvl') in
          let^ (ms) <- indclear_aligned indlvl' lxp bxp indbns 0 (len / N' * N') ms;
          let indbns' := upd_range indbns 0 (len / N') $0 in
          let^ (ms, indbns'') <- indclear_from_aligned indlvl' lxp bxp indbns' (len / N' * N') (len mod N') ms;
          let^ (ms, v) <- update_block lxp bxp ragged_bn indbns indbns'' ms;
          Ret ^(ms, updN iblocks (start / N) $ v)
        end
      }
    }.
Theorem indclear_from_aligned_ok : forall indlvl lxp bxp indbns start len ms,
    let N := NIndirect ^ S indlvl in
    {< F Fm Fs m0 sm m l_part freelist fsl,
    PRE:hm
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (BALLOCC.MSLog ms) sm hm *
           [[[ m ::: (Fm * listmatch (fun x l => indrep_n_tree indlvl bxp (snd x) #(fst x) l) (combine indbns fsl) l_part
                         * BALLOCC.rep bxp freelist ms) ]]] *
           [[ start + len <= length (concat l_part) ]] * [[ Nat.divide N start ]] * [[ len < N ]] *
           [[ length fsl = length indbns ]] *
           [[ (Fs * pred_fold_left fsl * BALLOCC.smrep freelist)%pred sm ]]
    POST:hm' RET:^(ms, indbns')
           exists m' freelist' l_part' fsl',
           LOG.rep lxp F (LOG.ActiveTxn m0 m') (BALLOCC.MSLog ms) sm hm' *
           [[[ m' ::: (Fm * listmatch (fun x l => indrep_n_tree indlvl bxp (snd x) #(fst x) l) (combine indbns' fsl') l_part'
                          * BALLOCC.rep bxp freelist' ms) ]]] *
           [[ concat (l_part') = upd_range (concat l_part) start len $0 ]] *
           [[ length indbns' = length indbns ]] *
           [[ length fsl' = length indbns' ]] *
           [[ incl freelist freelist' ]] *
           [[ (Fs * pred_fold_left fsl' * BALLOCC.smrep freelist')%pred sm ]]
    CRASH:hm'  LOG.intact lxp F m0 sm hm'
    >} indclear_from_aligned indlvl lxp bxp indbns start len ms.
Proof.
(* original proof tokens: 2289 *)

(* No more tactics to try *)
Admitted.

Hint Extern 1 ({{_}} Bind (indclear_from_aligned _ _ _ _ _ _ _) _) => apply indclear_from_aligned_ok : prog.
Fixpoint indclear_to_aligned indlvl lxp bxp iblocks start ms :=
    let N := (NIndirect ^ S indlvl) in
    If (addr_eq_dec (start mod N) 0) {
      Ret ^(ms, iblocks)
    } else {
      let ragged_bn := #(selN iblocks (start / N) $0) in
      If (addr_eq_dec ragged_bn 0) {
        Ret ^(ms, iblocks)
      } else {
        let^ (lms, indbns) <- IndRec.read lxp ragged_bn 1 (BALLOCC.MSLog ms);
        let ms := BALLOCC.upd_memstate lms ms in
        match indlvl with
        | 0 =>
          let indbns' := upd_range indbns (start mod NIndirect) (NIndirect - (start mod NIndirect)) $0 in
          let^ (ms, v) <- update_block lxp bxp ragged_bn indbns indbns' ms;
          Ret ^(ms, updN iblocks (start / N) $ v)
        | S indlvl' =>
          let N' := NIndirect ^ S indlvl' in
          let start' := start mod N in
          let^ (ms, indbns') <- indclear_to_aligned indlvl' lxp bxp indbns start' ms;
          let^ (ms) <- indclear_aligned indlvl' lxp bxp indbns' (roundup start' N') (N - (roundup start' N')) ms;
          let indbns'' := upd_range indbns' (divup start' N') (NIndirect - (divup start' N')) $0 in
          let^ (ms, v) <- update_block lxp bxp ragged_bn indbns indbns'' ms;
          Ret ^(ms, updN iblocks (start / N) $ v)
        end
      }
    }.
Theorem indclear_to_aligned_ok : forall indlvl lxp bxp indbns start ms,
    let N := NIndirect ^ S indlvl in
    {< F Fm Fs m0 sm m fsl l_part freelist,
    PRE:hm
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (BALLOCC.MSLog ms) sm hm *
           [[[ m ::: (Fm * listmatch (fun x l => indrep_n_tree indlvl bxp (snd x) #(fst x) l) (combine indbns fsl) l_part
                         * BALLOCC.rep bxp freelist ms) ]]] *
           [[ (Fs * pred_fold_left fsl * BALLOCC.smrep freelist)%pred sm ]] *
           [[ start <= length (concat l_part) ]] *
           [[ length fsl = length indbns ]]
    POST:hm' RET:^(ms, indbns')
           exists m' freelist' fsl' l_part',
           LOG.rep lxp F (LOG.ActiveTxn m0 m') (BALLOCC.MSLog ms) sm hm' *
           [[[ m' ::: (Fm * listmatch (fun x l => indrep_n_tree indlvl bxp (snd x) #(fst x) l) (combine indbns' fsl') l_part'
                          * BALLOCC.rep bxp freelist' ms) ]]] *
           [[ concat (l_part') = upd_range (concat l_part) start (roundup start N - start) $0 ]] *
           [[ incl freelist freelist' ]] *
           [[ (Fs * pred_fold_left fsl' * BALLOCC.smrep freelist')%pred sm ]] *
           [[ length fsl' = length indbns' ]]
    CRASH:hm'  LOG.intact lxp F m0 sm hm'
    >} indclear_to_aligned indlvl lxp bxp indbns start ms.
Proof.
(* original proof tokens: 2883 *)

(* No more tactics to try *)
Admitted.

Local Hint Extern 1 ({{_}} Bind (indclear_to_aligned _ _ _ _ _ _) _) => apply indclear_to_aligned_ok : prog.
Definition indclear_multiple_blocks indlvl lxp bxp indbns start len ms :=
    let N := NIndirect ^ S indlvl in
    let^ (ms, indbns') <- indclear_to_aligned indlvl lxp bxp indbns start ms;
    let len' := len - (roundup start N - start) in
    let start' := start + (roundup start N - start) in
    let^ (ms) <- indclear_aligned indlvl lxp bxp indbns' start' (len' / N * N) ms;
    let indbns'' := upd_range indbns' (start' / N) (len' / N) $0 in
    let start'' := start' + (len' / N * N) in
    let len'' := len' mod N in
    indclear_from_aligned indlvl lxp bxp indbns'' start'' len'' ms.
Theorem indclear_multiple_blocks_ok : forall indlvl lxp bxp indbns start len ms,
    let N := NIndirect ^ S indlvl in
    {< F Fm Fs m0 sm m l_part freelist fsl,
    PRE:hm
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (BALLOCC.MSLog ms) sm hm *
           [[[ m ::: (Fm * listmatch (fun x l => indrep_n_tree indlvl bxp (snd x) #(fst x) l) (combine indbns fsl) l_part
                         * BALLOCC.rep bxp freelist ms) ]]] *
           [[ start <= length (concat l_part) ]] * [[ (N - start mod N) < len ]] *
           [[ start + len <= length (concat l_part) ]] *
           [[ (Fs * pred_fold_left fsl * BALLOCC.smrep freelist)%pred sm ]] *
           [[ length indbns = length fsl ]]
    POST:hm' RET:^(ms, indbns')
           exists m' freelist' l_part' fsl',
           LOG.rep lxp F (LOG.ActiveTxn m0 m') (BALLOCC.MSLog ms) sm hm' *
           [[[ m' ::: (Fm * listmatch (fun x l => indrep_n_tree indlvl bxp (snd x) #(fst x) l) (combine indbns' fsl') l_part'
                          * BALLOCC.rep bxp freelist' ms) ]]] *
           [[ concat (l_part') = upd_range (concat l_part) start len $0 ]] *
           [[ (Fs * pred_fold_left fsl' * BALLOCC.smrep freelist')%pred sm ]] *
           [[ length indbns' = length fsl' ]] *
           [[ incl freelist freelist' ]]
    CRASH:hm'  LOG.intact lxp F m0 sm hm'
    >} indclear_multiple_blocks indlvl lxp bxp indbns start len ms.
Proof.
(* original proof tokens: 679 *)

(* No more tactics to try *)
Admitted.

Local Hint Extern 1 ({{_}} Bind (indclear_multiple_blocks _ _ _ _ _ _ _) _) => apply indclear_multiple_blocks_ok : prog.
Fixpoint indclear indlvl lxp bxp (root : addr) start len ms :=
    let N := NIndirect ^ indlvl in
    If (addr_eq_dec root 0) {
      Ret ^(ms, 0)
    } else {
      If (addr_eq_dec len 0) {
        Ret ^(ms, root)
      } else {
        let^ (lms, indbns) <- IndRec.read lxp root 1 (BALLOCC.MSLog ms);
        let ms := BALLOCC.upd_memstate lms ms in
        let^ (ms, indbns') <- match indlvl with
        | 0 =>
           Ret ^(ms, upd_range indbns start len $0)
        | S indlvl' =>
          If (le_lt_dec len (N - start mod N)) {
            let^ (ms, v) <- indclear indlvl' lxp bxp #(selN indbns (start / N) $0) (start mod N) len ms;
            Ret ^(ms, updN indbns (start / N) $ v)
          } else {
            indclear_multiple_blocks indlvl' lxp bxp indbns start len ms
          }
        end;
        update_block lxp bxp root indbns indbns' ms
      }
    }.
Theorem indclear_ok : forall indlvl lxp bxp ir start len ms,
    {< F Fm Fs m0 sm m l freelist IFs,
    PRE:hm
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (BALLOCC.MSLog ms) sm hm *
           [[[ m ::: (Fm * indrep_n_tree indlvl bxp IFs ir l *
            BALLOCC.rep bxp freelist ms) ]]] *
           [[ start + len <= length l ]] *
           [[ (Fs * IFs * BALLOCC.smrep freelist)%pred sm ]]
    POST:hm' RET:^(ms, ir')
           exists m' freelist' l' IFs',
           LOG.rep lxp F (LOG.ActiveTxn m0 m') (BALLOCC.MSLog ms) sm hm' *
           [[[ m' ::: (Fm * indrep_n_tree indlvl bxp IFs' ir' l' *
              BALLOCC.rep bxp freelist' ms) ]]] *
           [[ incl freelist freelist' ]] * [[ l' = upd_range l start len $0 ]] *
           [[ (Fs * IFs' * BALLOCC.smrep freelist')%pred sm ]] *
           ([[ ir = ir' ]] \/ [[ ir' = 0 ]])
    CRASH:hm'  LOG.intact lxp F m0 sm hm'
    >} indclear indlvl lxp bxp ir start len ms.
Proof.
(* original proof tokens: 1434 *)

(* No more tactics to try *)
Admitted.

Local Hint Extern 1 ({{_}} Bind (indclear _ _ _ _ _ _ _ ) _) => apply indclear_ok : prog.
Opaque indclear.
Definition indput_get_blocks {P} {Q} lxp (is_alloc : {P} + {Q}) ir ms :=
    If (is_alloc) {
      Ret ^(ms, repeat $0 NIndirect)
    } else {
      IndRec.read lxp ir 1 ms
    }.
Theorem indput_get_blocks_ok : forall P Q lxp (is_alloc : {P} + {Q}) ir ms,
    {< F Fm m0 sm m bxp indbns Fs,
    PRE:hm
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms sm hm *
           [[ BALLOCC.bn_valid bxp ir ]] *
           [[ P -> ir = 0 ]] * [[ Q -> ir <> 0 ]] *
           [[[ m ::: (Fm * indrep_n_helper Fs bxp ir indbns) ]]]
    POST:hm' RET:^(ms, r)
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms sm hm' *
           [[ r = indbns ]]
    CRASH:hm'  LOG.intact lxp F m0 sm hm'
    >} indput_get_blocks lxp is_alloc ir ms.
Proof.
(* original proof tokens: 86 *)

(* No more tactics to try *)
Admitted.

Local Hint Extern 0 ({{_}} Bind (indput_get_blocks _ _ _ _) _) => apply indput_get_blocks_ok : prog.
Definition indrec_write_blind lxp xp items ms :=
    IndRec.write lxp xp items ms.
Theorem indrec_write_blind_ok : forall lxp xp items ms,
    {< F Fm m0 sm m old,
    PRE:hm
          LOG.rep lxp F (LOG.ActiveTxn m0 m) ms sm hm *
          [[ IndRec.items_valid xp items ]] * [[ xp <> 0 ]] *
          [[[ m ::: Fm * arrayN (@ptsto _ addr_eq_dec _) xp [old] ]]]
    POST:hm' RET:ms exists m',
          LOG.rep lxp F (LOG.ActiveTxn m0 m') ms sm hm' *
          [[[ m' ::: Fm * IndRec.rep xp items ]]]
    CRASH:hm' LOG.intact lxp F m0 sm hm'
    >} indrec_write_blind lxp xp items ms.
Proof.
(* original proof tokens: 112 *)

(* No more tactics to try *)
Admitted.

Local Hint Extern 0 ({{_}} Bind (indrec_write_blind _ _ _ _) _) => apply indrec_write_blind_ok : prog.
Definition indput_upd_if_necessary lxp ir v indbns to_grow ms := 
    If (addr_eq_dec v #(selN indbns to_grow $0)) {
      Ret ms
    } else {
      indrec_write_blind lxp ir (indbns ⟦ to_grow := ($ v)⟧) ms
    }.
Theorem indput_upd_if_necessary_ok : forall lxp ir v indbns to_grow ms,
    {< F Fm m0 sm m bxp Fs,
    PRE:hm
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms sm hm *
           [[ BALLOCC.bn_valid bxp ir ]] *
           [[[ m ::: (Fm * indrep_n_helper Fs bxp ir indbns) ]]]
    POST:hm' RET: ms
           exists m' indbns', 
           LOG.rep lxp F (LOG.ActiveTxn m0 m') ms sm hm' *
           [[ indbns' = updN indbns to_grow ($ v) ]] *
           [[[ m' ::: (Fm * indrep_n_helper Fs bxp ir indbns') ]]]
    CRASH:hm'  LOG.intact lxp F m0 sm hm'
    >} indput_upd_if_necessary lxp ir v indbns to_grow ms.
Proof.
(* original proof tokens: 127 *)

(* No more tactics to try *)
Admitted.

Local Hint Extern 1 ({{_}} Bind (indput_upd_if_necessary _ _ _ _ _ _) _) => apply indput_upd_if_necessary_ok : prog.
Fixpoint indput indlvl lxp bxp root off bn ms :=
    let N := NIndirect ^ indlvl in
    let is_alloc := (addr_eq_dec root 0) in
    let^ (ms, ir) <- If (is_alloc) {
        BALLOCC.alloc lxp bxp ms
      } else {
        Ret ^(ms, Some root)
      };
    match ir with
    | None => Ret ^(ms, 0)
    | Some ir =>
      match indlvl with
      | 0 => lms <- If (is_alloc) {
                      indrec_write_blind lxp ir ((repeat $0 NIndirect) ⟦ off := bn ⟧) (BALLOCC.MSLog ms)
                   } else {
                      IndRec.put lxp ir off bn (BALLOCC.MSLog ms)
                   };
        Ret ^((BALLOCC.upd_memstate lms ms), ir)
      | S indlvl' =>
        let to_grow := off / N in
        let^ (lms, indbns) <- indput_get_blocks lxp is_alloc ir (BALLOCC.MSLog ms);
        let ir_to_grow := #(selN indbns to_grow $0) in
        let^ (ms, v) <- indput indlvl' lxp bxp ir_to_grow (off mod N) bn 
                (BALLOCC.upd_memstate lms ms);
        If (addr_eq_dec v 0) {
          Ret ^(ms, 0)
        } else {
          lms <- indput_upd_if_necessary lxp ir v indbns to_grow (BALLOCC.MSLog ms);
          Ret ^((BALLOCC.upd_memstate lms ms), ir)
        }
      end
    end.
Lemma indrep_n_helper_0_sm: forall bxp l Fs,
    indrep_n_helper Fs bxp 0 l =p=> [[ Fs <=p=> emp ]] * indrep_n_helper Fs bxp 0 l.
Proof.
(* original proof tokens: 22 *)

(* No more tactics to try *)
Admitted.

Theorem indput_ok : forall indlvl lxp bxp ir off bn ms,
    {< F Fm Fs m0 sm m l freelist IFs,
    PRE:hm
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (BALLOCC.MSLog ms) sm hm *
           [[[ m ::: (Fm * indrep_n_tree indlvl bxp IFs ir l *
              BALLOCC.rep bxp freelist ms) ]]] *
           [[ off < length l ]] *
           [[ (Fs * IFs * BALLOCC.smrep freelist)%pred sm ]]
    POST:hm' RET:^(ms, ir')
           exists m', LOG.rep lxp F (LOG.ActiveTxn m0 m') (BALLOCC.MSLog ms) sm hm' *
           ([[ ir' = 0 ]] \/
           exists freelist' l' IFs',
           [[ ir = 0 \/ ir = ir' ]] *
           [[[ m' ::: (Fm * indrep_n_tree indlvl bxp IFs' ir' l' *
             BALLOCC.rep bxp freelist' ms) ]]] *
           [[ incl freelist' freelist ]] * [[ l' = updN l off bn ]] *
           [[ (Fs * IFs' * BALLOCC.smrep freelist')%pred sm ]])
    CRASH:hm'  LOG.intact lxp F m0 sm hm'
    >} indput indlvl lxp bxp ir off bn ms.
Proof.
(* original proof tokens: 1487 *)

(* No more tactics to try *)
Admitted.

Local Hint Extern 0 ({{_}} Bind (indput _ _ _ _ _ _ _) _) => apply indput_ok : prog.
Opaque indput.
Opaque indrep_n_tree.
Definition indrep bxp Fs ir (indlist : list waddr) :=
    (exists Fs0 Fs1 Fs2, [[ Fs <=p=> Fs0 * Fs1 * Fs2 ]] *
      indrep_n_tree 0 bxp Fs0 (IRIndPtr ir) (firstn NIndirect indlist) *
      indrep_n_tree 1 bxp Fs1 (IRDindPtr ir) (firstn (NIndirect ^ 2) (skipn NIndirect indlist)) *
      indrep_n_tree 2 bxp Fs2 (IRTindPtr ir) (skipn (NIndirect + NIndirect ^ 2) indlist)
    )%pred.
Definition rep bxp Fs (ir : irec) (l : list waddr) :=
    ( [[ length l = (IRLen ir) /\ length l <= NBlocks ]] *
      [[ length (IRBlocks ir) = NDirect ]] *
      exists indlist, indrep bxp Fs ir indlist *
      [[ l = firstn (length l) ((IRBlocks ir) ++ indlist) ]] *
      [[ list_same $0 (skipn (length l) ((IRBlocks ir) ++ indlist)) ]] )%pred.
Definition rep_direct bxp Fs (ir : irec) (l : list waddr) : @pred _ addr_eq_dec valuset :=
    ( [[ length l = (IRLen ir) /\ length l <= NBlocks /\ length l <= NDirect ]] *
      [[ length (IRBlocks ir) = NDirect ]] *
      exists indlist, indrep bxp Fs ir indlist *
      [[ l = firstn (length l) (IRBlocks ir) ]] *
      [[ list_same $0 (skipn (length l) (IRBlocks ir)) ]] *
      [[ list_same $0 indlist ]] )%pred.
Definition rep_indirect bxp Fs (ir : irec) (l : list waddr) :=
    ( [[ length l = (IRLen ir) /\ length l <= NBlocks /\ length l > NDirect ]] *
      [[ length (IRBlocks ir) = NDirect ]] *
      exists indlist, indrep bxp Fs ir indlist *
      [[ l = (IRBlocks ir) ++ firstn (length l - NDirect) indlist ]] *
      [[ list_same $0 (skipn (length l - NDirect) indlist) ]] )%pred.
Hint Resolve list_same_app_l.
Hint Resolve list_same_app_r.
Hint Resolve list_same_app_both.
Lemma rep_piff_direct : forall bxp Fs ir l,
    length l <= NDirect ->
    rep bxp Fs ir l <=p=> rep_direct bxp Fs ir l.
Proof.
(* original proof tokens: 96 *)

(* No more tactics to try *)
Admitted.

Lemma rep_piff_indirect : forall bxp Fs ir l,
    length l > NDirect ->
    rep bxp Fs ir l <=p=> rep_indirect bxp Fs ir l.
Proof.
(* original proof tokens: 141 *)

(* No more tactics to try *)
Admitted.

Lemma rep_selN_direct_ok : forall F bxp Fs ir l m off,
    (F * rep bxp Fs ir l)%pred m ->
    off < NDirect ->
    off < length l ->
    selN (IRBlocks ir) off $0 = selN l off $0.
Proof.
(* original proof tokens: 42 *)
eapply pimpl_apply; [ | eauto ].
eapply pimpl_apply; [ | eauto ].
eapply pimpl_trans.
eapply pimpl_trans.
eapply pimpl_trans2; [ | eapply pimpl_trans2 ]; eauto.
eapply pimpl_trans.
(* No more tactics to try *)
Admitted.

Theorem indrep_length_pimpl : forall bxp Fs ir l,
    indrep bxp Fs ir l <=p=> indrep bxp Fs ir l * [[ length l = NBlocks - NDirect ]].
Proof.
(* original proof tokens: 119 *)

(* No more tactics to try *)
Admitted.

Theorem indrep_bxp_switch : forall bxp bxp' Fs xp ilist,
    BmapNBlocks bxp = BmapNBlocks bxp' ->
    indrep bxp Fs xp ilist <=p=> indrep bxp' Fs xp ilist.
Proof.
(* original proof tokens: 125 *)

(* No more tactics to try *)
Admitted.

Theorem indrep_0 : forall bxp Fs ir l,
    IRIndPtr ir = 0 -> IRDindPtr ir = 0 -> IRTindPtr ir = 0 ->
    indrep bxp Fs ir l <=p=> [[l = repeat $0 (NBlocks - NDirect)]] * [[ Fs <=p=> emp ]].
Proof.
(* original proof tokens: 190 *)

(* No more tactics to try *)
Admitted.

Lemma rep_keep_blocks : forall bxp Fs ir ir' l,
    IRIndPtr ir = IRIndPtr ir' ->
    IRDindPtr ir = IRDindPtr ir' ->
    IRTindPtr ir = IRTindPtr ir' ->
    IRLen ir = IRLen ir' ->
    IRBlocks ir = IRBlocks ir' ->
    rep bxp Fs ir l =p=> rep bxp Fs ir' l.
Proof.
(* original proof tokens: 46 *)
eapply piff_refl; eauto.
(* No more tactics to try *)
Admitted.

Theorem rep_bxp_switch : forall bxp bxp' Fs xp ilist,
    BmapNBlocks bxp = BmapNBlocks bxp' ->
    rep bxp Fs xp ilist <=p=> rep bxp' Fs xp ilist.
Proof.
(* original proof tokens: 54 *)

(* No more tactics to try *)
Admitted.

Theorem xform_indrep : forall xp Fs ir l,
    crash_xform (indrep xp Fs ir l) <=p=> indrep xp Fs ir l.
Proof.
(* original proof tokens: 71 *)

(* No more tactics to try *)
Admitted.

Definition get lxp (ir : irec) off ms :=
    If (lt_dec off NDirect) {
      Ret ^(ms, selN (IRBlocks ir) off $0)
    } else {
      let off := off - NDirect in
      If (lt_dec off NIndirect) {
        indget 0 lxp (IRIndPtr ir) off ms
      } else {
        let off := off - NIndirect in
        If (lt_dec off (NIndirect ^ 2)) {
          indget 1 lxp (IRDindPtr ir) off ms
        } else {
          let off := off - NIndirect ^ 2 in
          indget 2 lxp (IRTindPtr ir) off ms
        }
      }
    }.
Definition read lxp (ir : irec) ms :=
    If (le_dec (IRLen ir) NDirect) {
      Ret ^(ms, firstn (IRLen ir) (IRBlocks ir))
    } else {
      let^ (ms, indbns) <- indread 0 lxp (IRIndPtr ir) ms;
      let^ (ms, dindbns) <- indread 1 lxp (IRDindPtr ir) ms;
      let^ (ms, tindbns) <- indread 2 lxp (IRTindPtr ir) ms;
      Ret ^(ms, (firstn (IRLen ir) ((IRBlocks ir) ++ indbns ++ dindbns ++ tindbns)))
    }.
Definition indread_range_helper indlvl lxp bn start len ms :=
    let localstart := fold_left plus (map (fun i => NIndirect ^ S i) (seq 0 indlvl)) 0 in
    let maxlen := NIndirect ^ S indlvl in
    If (lt_dec localstart (start + len)) {
      If (lt_dec start (localstart + maxlen)) {
        let start' := start - localstart in
        let len' := len - (localstart - start) in
        let len'' := Nat.min len' (maxlen - start') in
        indread_range indlvl lxp bn start' len'' ms
      } else {
        Ret ^(ms, nil)
      }
    } else {
      Ret ^(ms, nil)
    }.
Definition read_range lxp ir start len ms :=
    rdir <- Ret (firstn len (skipn start (IRBlocks ir)));
    let len := len - (NDirect - start) in
    let start := start - NDirect in
    let^ (ms, rind) <- indread_range_helper 0 lxp (IRIndPtr ir) start len ms;
    let^ (ms, rdind) <- indread_range_helper 1 lxp (IRDindPtr ir) start len ms;
    let^ (ms, rtind) <- indread_range_helper 2 lxp (IRTindPtr ir) start len ms;
    Ret ^(ms, rdir ++ rind ++ rdind ++ rtind).
Definition indshrink_helper indlvl lxp bxp bn nl ms :=
    let start := fold_left plus (map (fun i => NIndirect ^ S i) (seq 0 indlvl)) 0 in
    let len := NIndirect ^ S indlvl in
    If (lt_dec nl (start + len)) {
      indclear indlvl lxp bxp bn (nl - start) (len - (nl - start)) ms
    } else {
      Ret ^(ms, bn)
    }.
Definition indshrink lxp bxp ir nl ms :=
    let^ (ms, indptr)  <- indshrink_helper 0 lxp bxp (IRIndPtr ir)  nl ms;
    let^ (ms, dindptr) <- indshrink_helper 1 lxp bxp (IRDindPtr ir) nl ms;
    let^ (ms, tindptr) <- indshrink_helper 2 lxp bxp (IRTindPtr ir) nl ms;
    Ret ^(ms, indptr, dindptr, tindptr).
Definition shrink lxp bxp (ir : irec) nr ms :=
    let ol := (IRLen ir) in
    let nl := (ol - nr) in
    If (le_dec ol NDirect) {
      Ret ^(ms, upd_irec ir nl (IRIndPtr ir) (IRDindPtr ir) (IRTindPtr ir)
                         (upd_range_fast (IRBlocks ir) nl (NDirect - nl) $0))
    } else {
      let ol' := ol - NDirect in
      let nl' := nl - NDirect in
      let^ (ms, indptr, dindptr, tindptr) <- indshrink lxp bxp ir nl' ms;
      Ret ^(ms, upd_irec ir nl indptr dindptr tindptr
                         (upd_range_fast (IRBlocks ir) nl (NDirect - nl) $0))
    }.
Definition indgrow lxp bxp ir off bn ms :=
    If (lt_dec off NIndirect) {
      let^ (ms, v) <- indput 0 lxp bxp (IRIndPtr ir) off bn ms;
      Ret ^(ms, v, v, (IRDindPtr ir), (IRTindPtr ir))
    } else {
      let off := off - NIndirect in
      If (lt_dec off (NIndirect ^ 2)) {
        let^ (ms, v) <- indput 1 lxp bxp (IRDindPtr ir) off bn ms;
        Ret ^(ms, v, (IRIndPtr ir), v, (IRTindPtr ir))
      } else {
        let off := off - NIndirect ^ 2 in
        let^ (ms, v) <- indput 2 lxp bxp (IRTindPtr ir) off bn ms;
        Ret ^(ms, v, (IRIndPtr ir), (IRDindPtr ir), v)
      }
    }.
Definition grow lxp bxp (ir : irec) bn ms :=
    let len := (IRLen ir) in
    If (lt_dec len NDirect) {
      
      Ret ^(ms, OK (upd_irec ir (S len) (IRIndPtr ir) (IRDindPtr ir) (IRTindPtr ir) (updN (IRBlocks ir) len bn)))
    } else {
      let off := (len - NDirect) in
      If (waddr_eq_dec bn $0) {
        Ret ^(ms, OK (upd_len ir (S len)))
      } else {
        let^ (ms, v, indptr, dindptr, tindptr) <- indgrow lxp bxp ir off bn ms;
        If (addr_eq_dec v 0) {
          Ret ^(ms, Err ENOSPCBLOCK)
        } else {
          Ret ^(ms, OK (upd_irec ir (S len) indptr dindptr tindptr (IRBlocks ir)))
        }
      }
    }.
Theorem get_ok : forall lxp bxp ir off ms,
    {< F Fm IFs m0 sm m l,
    PRE:hm
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms sm hm *
           [[[ m ::: Fm * rep bxp IFs ir l ]]] *
           [[ off < length l ]]
    POST:hm' RET:^(ms, r)
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms sm hm' *
           [[ r = selN l off $0 ]]
    CRASH:hm'  exists ms',
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms' sm hm'
    >} get lxp ir off ms.
Proof.
(* original proof tokens: 129 *)

(* No more tactics to try *)
Admitted.

Theorem read_ok : forall lxp bxp ir ms,
    {< F Fm IFs m0 sm m l,
    PRE:hm
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms sm hm *
           [[[ m ::: Fm * rep bxp IFs ir l ]]]
    POST:hm' RET:^(ms, r)
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms sm hm' *
           [[ r = l ]]
    CRASH:hm'  exists ms',
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms' sm hm'
    >} read lxp ir ms.
Proof.
(* original proof tokens: 129 *)

(* No more tactics to try *)
Admitted.

Theorem indread_range_helper_ok : forall lxp bn indlvl start len ms,
    let localstart := fold_left plus (map (fun i => NIndirect ^ S i) (seq 0 indlvl)) 0 in
    {< F Fm IFs m0 sm m l bxp,
    PRE:hm
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms sm hm *
           [[[ m ::: (Fm * indrep_n_tree indlvl bxp IFs bn l) ]]]
    POST:hm' RET:^(ms, r)
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms sm hm' *
           let len' := (len - (localstart - start)) in
           [[ r = firstn len' (skipn (start - localstart) l) ]]
    CRASH:hm'  LOG.intact lxp F m0 sm hm'
    >} indread_range_helper indlvl lxp bn start len ms.
Proof.
(* original proof tokens: 143 *)

(* No more tactics to try *)
Admitted.

Local Hint Extern 1 ({{_}} Bind (indread_range_helper _ _ _ _ _ _ ) _) => apply indread_range_helper_ok : prog.
Lemma indrec_ptsto_pimpl : forall ibn indrec,
    IndRec.rep ibn indrec =p=> exists v, ibn |-> (v, nil).
Proof.
(* original proof tokens: 146 *)

(* No more tactics to try *)
Admitted.

Hint Rewrite cuttail_length : core.
Hint Rewrite upd_len_get_len upd_len_get_ind upd_len_get_dind upd_len_get_tind upd_len_get_blk upd_len_get_iattr : core.
Hint Rewrite upd_irec_get_len upd_irec_get_ind upd_irec_get_dind upd_irec_get_tind upd_irec_get_blk upd_irec_get_iattr : core.
Local Hint Resolve upd_len_get_iattr upd_irec_get_iattr.
Theorem upd_len_indrep : forall bxp Fs ir l n,
    indrep bxp Fs ir l <=p=> indrep bxp Fs (upd_len ir n) l.
Proof.
(* original proof tokens: 22 *)
eapply piff_refl.
(* No more tactics to try *)
Admitted.

Theorem upd_len_direct_indrep : forall bxp Fs ir l n b,
    indrep bxp Fs ir l <=p=> indrep bxp Fs (upd_irec ir n (IRIndPtr ir) (IRDindPtr ir) (IRTindPtr ir) b) l.
Proof.
(* original proof tokens: 45 *)

(* No more tactics to try *)
Admitted.

Theorem indshrink_helper_ok : forall lxp bxp bn nl indlvl ms,
    let start := fold_left plus (map (fun i => NIndirect ^ S i) (seq 0 indlvl)) 0 in
    {< F Fm Fs IFs m0 sm m l freelist,
    PRE:hm
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (BALLOCC.MSLog ms) sm hm *
           [[[ m ::: (Fm * indrep_n_tree indlvl bxp IFs bn l * BALLOCC.rep bxp freelist ms) ]]] *
           [[ (Fs * IFs * BALLOCC.smrep freelist)%pred sm ]]
    POST:hm' RET:^(ms, r)  exists m' freelist' IFs' l',
           LOG.rep lxp F (LOG.ActiveTxn m0 m') (BALLOCC.MSLog ms) sm hm' *
           [[[ m' ::: (Fm * indrep_n_tree indlvl bxp IFs' r l' * BALLOCC.rep bxp freelist' ms) ]]] *
           [[ l' = upd_range l (nl - start) (length l - (nl - start)) $0 ]] *
           [[ (Fs * IFs' * BALLOCC.smrep freelist')%pred sm ]] *
           [[ incl freelist freelist' ]]
    CRASH:hm'  LOG.intact lxp F m0 sm hm'
    >} indshrink_helper indlvl lxp bxp bn nl ms.
Proof.
(* original proof tokens: 55 *)

(* No more tactics to try *)
Admitted.

Local Hint Extern 1 ({{_}} Bind (indshrink_helper _ _ _ _ _ _ ) _) => apply indshrink_helper_ok : prog.
Theorem indshrink_ok : forall lxp bxp ir nl ms,
    {< F Fm Fs IFs0 IFs1 IFs2 m0 sm m l0 l1 l2 freelist,
    PRE:hm
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (BALLOCC.MSLog ms) sm hm *
           [[ nl <= length (l0 ++ l1 ++ l2) ]] *
           [[[ m ::: (Fm * indrep_n_tree 0 bxp IFs0 (IRIndPtr ir) l0 *
                           indrep_n_tree 1 bxp IFs1 (IRDindPtr ir) l1 *
                           indrep_n_tree 2 bxp IFs2 (IRTindPtr ir) l2 *
                           BALLOCC.rep bxp freelist ms) ]]] *
           [[ (Fs * IFs0 * IFs1 * IFs2 * BALLOCC.smrep freelist)%pred sm ]]
    POST:hm' RET:^(ms, indptr', dindptr', tindptr')
           exists m' freelist' l0' l1' l2' IFs0' IFs1' IFs2',
           LOG.rep lxp F (LOG.ActiveTxn m0 m') (BALLOCC.MSLog ms) sm hm' *
           [[[ m' ::: (Fm * indrep_n_tree 0 bxp IFs0' indptr' l0' *
                            indrep_n_tree 1 bxp IFs1' dindptr' l1' *
                            indrep_n_tree 2 bxp IFs2' tindptr' l2' * BALLOCC.rep bxp freelist' ms) ]]] *
           [[ l0' ++ l1' ++ l2' = upd_range (l0 ++ l1 ++ l2) nl (length (l0 ++ l1 ++ l2) - nl) $0 ]] *
           [[ (Fs * IFs0' * IFs1' * IFs2' * BALLOCC.smrep freelist')%pred sm ]] *
           [[ incl freelist freelist' ]]
    CRASH:hm'  LOG.intact lxp F m0 sm hm'
    >} indshrink lxp bxp ir nl ms.
Proof.
(* original proof tokens: 250 *)

(* No more tactics to try *)
Admitted.

Local Hint Extern 1 ({{_}} Bind (indshrink _ _ _ _ _) _) => apply indshrink_ok : prog.
Theorem shrink_ok : forall lxp bxp ir nr ms,
    {< F Fm Fs IFs m0 sm m l freelist,
    PRE:hm
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (BALLOCC.MSLog ms) sm hm *
           [[[ m ::: (Fm * rep bxp IFs ir l * BALLOCC.rep bxp freelist ms) ]]] *
           [[ (Fs * IFs * BALLOCC.smrep freelist)%pred sm ]]
    POST:hm' RET:^(ms, r)  exists m' freelist' l' IFs',
           LOG.rep lxp F (LOG.ActiveTxn m0 m') (BALLOCC.MSLog ms) sm hm' *
           [[[ m' ::: (Fm * rep bxp IFs' r l' * BALLOCC.rep bxp freelist' ms) ]]] *
           [[ (Fs * IFs' * BALLOCC.smrep freelist')%pred sm ]] *
           exists ind dind tind dirl, [[ r = upd_irec ir ((IRLen ir) - nr) ind dind tind dirl ]] *
           [[ l' = firstn (IRLen ir - nr) l ]] *
           [[ incl freelist freelist' ]]
    CRASH:hm'  LOG.intact lxp F m0 sm hm'
    >} shrink lxp bxp ir nr ms.
Proof.
(* original proof tokens: 1011 *)

(* No more tactics to try *)
Admitted.

Theorem indgrow_ok : forall lxp bxp ir off bn ms,
    {< F Fm Fs m0 sm m l0 l1 l2 freelist IFs0 IFs1 IFs2,
    PRE:hm
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (BALLOCC.MSLog ms) sm hm *
           [[ off < NBlocks - NDirect ]] * [[ bn <> $0 ]] *
           [[[ m ::: (Fm * indrep_n_tree 0 bxp IFs0 (IRIndPtr ir) l0 *
                           indrep_n_tree 1 bxp IFs1 (IRDindPtr ir) l1 *
                           indrep_n_tree 2 bxp IFs2 (IRTindPtr ir) l2 * BALLOCC.rep bxp freelist ms) ]]] *
           [[ (Fs * IFs0 * IFs1 * IFs2 * BALLOCC.smrep freelist)%pred sm ]]
    POST:hm' RET:^(ms, v, indptr', dindptr', tindptr')
           exists m', LOG.rep lxp F (LOG.ActiveTxn m0 m') (BALLOCC.MSLog ms) sm hm' *
           ([[ v = 0 ]] \/ [[ v <> 0 ]] *
           exists freelist' l0' l1' l2' IFs0' IFs1' IFs2',
           [[ updN (l0 ++ l1 ++ l2) off bn = l0' ++ l1' ++ l2' ]] *
           [[[ m' ::: (Fm * indrep_n_tree 0 bxp IFs0' indptr' l0' *
                            indrep_n_tree 1 bxp IFs1' dindptr' l1' *
                            indrep_n_tree 2 bxp IFs2' tindptr' l2' * BALLOCC.rep bxp freelist' ms) ]]] *
           [[ (Fs * IFs0' * IFs1' * IFs2' * BALLOCC.smrep freelist')%pred sm ]] *
           [[ incl freelist' freelist ]])
    CRASH:hm'  LOG.intact lxp F m0 sm hm'
    >} indgrow lxp bxp ir off bn ms.
Proof.
(* original proof tokens: 183 *)

(* No more tactics to try *)
Admitted.

Local Hint Extern 1 ({{_}} Bind (indgrow _ _ _ _ _ _) _) => apply indgrow_ok : prog.
Theorem grow_ok : forall lxp bxp ir bn ms,
    {< F Fm Fs m0 sm m IFs l freelist,
    PRE:hm
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (BALLOCC.MSLog ms) sm hm *
           [[ length l < NBlocks ]] *
           [[[ m ::: (Fm * rep bxp IFs ir l * BALLOCC.rep bxp freelist ms) ]]] *
           [[ (Fs * IFs * BALLOCC.smrep freelist)%pred sm ]]
    POST:hm' RET:^(ms, r)
           exists m',
           [[ isError r ]] * LOG.rep lxp F (LOG.ActiveTxn m0 m') (BALLOCC.MSLog ms) sm hm' \/
           exists freelist' ir' IFs',
           [[ r = OK ir' ]] * LOG.rep lxp F (LOG.ActiveTxn m0 m') (BALLOCC.MSLog ms) sm hm' *
           [[[ m' ::: (Fm * rep bxp IFs' ir' (l ++ [bn]) * BALLOCC.rep bxp freelist' ms) ]]] *
           [[ IRAttrs ir' = IRAttrs ir /\ length (IRBlocks ir') = length (IRBlocks ir) ]] *
           [[ (Fs * IFs' * BALLOCC.smrep freelist')%pred sm ]] *
           [[ incl freelist' freelist ]]
    CRASH:hm'  LOG.intact lxp F m0 sm hm'
    >} grow lxp bxp ir bn ms.
Proof.
(* original proof tokens: 963 *)

(* No more tactics to try *)
Admitted.

Hint Extern 1 ({{_}} Bind (get _ _ _ _) _) => apply get_ok : prog.
Hint Extern 1 ({{_}} Bind (read _ _ _) _) => apply read_ok : prog.
Hint Extern 1 ({{_}} Bind (shrink _ _ _ _ _) _) => apply shrink_ok : prog.
Hint Extern 1 ({{_}} Bind (grow _ _ _ _ _) _) => apply grow_ok : prog.
Hint Extern 0 (okToUnify (rep _ _ _ _) (rep _ _ _ _)) => constructor : okToUnify.
Hint Extern 0 (okToUnify (@selN (@pred _ _ bool) ?l _ _) (@selN (@pred _ _ bool) ?l _ _)) => constructor : okToUnify.
Lemma rep_IFs_sync_invariant: forall bxp IFs ir iblocks m F,
    (F * rep bxp IFs ir iblocks)%pred m ->
    sm_sync_invariant IFs.
Proof.
(* original proof tokens: 71 *)

(* No more tactics to try *)
Admitted.

Theorem xform_rep : forall xp Fs ir l,
    crash_xform (rep xp Fs ir l) <=p=> rep xp Fs ir l.
Proof.
(* original proof tokens: 71 *)

(* No more tactics to try *)
Admitted.

End BlockPtr.
