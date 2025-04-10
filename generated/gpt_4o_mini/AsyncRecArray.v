Require Import Arith.
Require Import Bool.
Require Import Pred PredCrash.
Require Import Prog.
Require Import Hoare.
Require Import SepAuto.
Require Import BasicProg.
Require Import Lia.
Require Import Word.
Require Import Rec.
Require Import Array.
Require Import WordAuto.
Require Import Cache.
Require Import Rounding.
Require Import List ListUtils.
Require Import Psatz.
Require Import AsyncDisk.
Require Import Classes.SetoidTactics.
Require Import RecArrayUtils.
Import ListNotations.
Set Implicit Arguments.
Module AsyncRecArray (RA : RASig).
Module Defs := RADefs RA.
Import RA Defs.
Definition items_valid xp start (items : itemlist) :=
    xparams_ok xp /\  start <= (RALen xp) /\
    Forall Rec.well_formed items /\
    length items <= (RALen xp - start) * items_per_val.
Inductive state : Type :=
  | Synced : itemlist -> state
  | Unsync : itemlist -> state
  .
Definition rep_common xp start items vl (vsl : list (list valu)) :=
    items_valid xp start items /\
    vl = ipack items /\ eqlen vl vsl.
Definition synced_array xp start items :=
    (exists vl vsl, [[ rep_common xp start items vl vsl /\
        vsl = nils (length vl) ]] *
    arrayS ((RAStart xp ) + start) (combine vl vsl))%pred.
Definition unsync_array xp start items :=
    (exists vl vsl, [[ rep_common xp start items vl vsl ]] *
    arrayS ((RAStart xp ) + start) (combine vl vsl))%pred.
Definition array_rep xp start (st : state) :=
   (match st with
    | Synced items => synced_array xp start items
    | Unsync items => unsync_array xp start items
    end)%pred.
Definition avail_rep xp start nr : rawpred :=
    (exists vsl, [[ length vsl = nr ]] *
     arrayS ((RAStart xp) + start) vsl)%pred.
Local Hint Extern 0 (okToUnify (arrayN (RAStart ?a) _ _) (arrayN (RAStart ?a) _ _)) => constructor : okToUnify.
Local Hint Extern 0 (okToUnify (arrayN (RAStart ?b + ?a) _ _) (arrayN (RAStart ?b + ?a) _ _)) 
    => constructor : okToUnify.
Definition nr_blocks st :=
    match st with
    | Synced l => (divup (length l) items_per_val)
    | Unsync l => (divup (length l) items_per_val)
    end.
Lemma items_valid_app : forall xp st a b,
    items_valid xp st (a ++ b) ->
    items_valid xp st a /\ items_valid xp st b.
Proof.
(* original proof tokens: 42 *)
split.
split.
(* No more tactics to try *)
Admitted.

Lemma le_add_helper: forall a b c d,
    b <= d -> a + d <= c -> a + b <= c.
Proof.
(* original proof tokens: 12 *)

(* No more tactics to try *)
Admitted.

Lemma le_add_le_sub : forall a b c,
    a <= c -> b <= c - a -> a + b <= c.
Proof.
(* original proof tokens: 12 *)

(* No more tactics to try *)
Admitted.

Lemma items_valid_app2 : forall xp st a b,
    length b <= (roundup (length a) items_per_val - length a)
    -> items_valid xp st a
    -> Forall Rec.well_formed b
    -> items_valid xp st (a ++ b).
Proof.
(* original proof tokens: 85 *)

(* No more tactics to try *)
Admitted.

Lemma items_valid_app3 : forall xp st a b na,
    length a = na * items_per_val ->
    items_valid xp st (a ++ b) -> items_valid xp (st + na) b.
Proof.
(* original proof tokens: 114 *)

(* No more tactics to try *)
Admitted.

Lemma items_valid_app4 : forall xp st a b na,
    length a = na * items_per_val ->
    items_valid xp st a ->
    items_valid xp (st + na) b ->
    items_valid xp st (a ++ b).
Proof.
(* original proof tokens: 66 *)

(* No more tactics to try *)
Admitted.

Lemma synced_array_is : forall xp start items,
    synced_array xp start items =p=>
    arrayS ((RAStart xp) + start) (combine (ipack items) (nils (length (ipack items)))).
Proof.
(* original proof tokens: 21 *)

(* No more tactics to try *)
Admitted.

Lemma array_rep_sync_nil : forall xp a,
    xparams_ok xp -> a <= (RALen xp) ->
    array_rep xp a (Synced nil) <=p=> emp.
Proof.
(* original proof tokens: 52 *)

(* No more tactics to try *)
Admitted.

Lemma array_rep_sync_nil_emp : forall xp a,
    array_rep xp a (Synced nil) =p=> emp.
Proof.
(* original proof tokens: 50 *)

(* No more tactics to try *)
Admitted.

Lemma array_rep_sync_nil_sep_star : forall xp a l,
    array_rep xp a (Synced l) =p=> array_rep xp a (Synced nil) * array_rep xp a (Synced l).
Proof.
(* original proof tokens: 72 *)
eapply sep_star_lift_l.
apply emp_pimpl_sep_star.
apply emp_star.
(* No more tactics to try *)
Admitted.

Theorem sync_invariant_array_rep : forall xp a st,
    sync_invariant (array_rep xp a st).
Proof.
(* original proof tokens: 25 *)

(* No more tactics to try *)
Admitted.

Theorem sync_invariant_avail_rep : forall xp a n,
    sync_invariant (avail_rep xp a n).
Proof.
(* original proof tokens: 15 *)

(* No more tactics to try *)
Admitted.

Hint Resolve sync_invariant_array_rep sync_invariant_avail_rep.
Hint Rewrite list_chunk_nil ipack_nil.
Hint Rewrite Nat.add_0_r Nat.add_0_l.
Hint Rewrite synced_array_is.
Hint Rewrite combine_length nils_length : lists.
Hint Rewrite ipack_length divup_mul.
Ltac rewrite_ignore H :=
    match type of H with
    | forall _, corr2 _ _ => idtac
    | sep_star _ _ _ => idtac
    end.
Ltac simplen_rewrite H := try progress (
    set_evars_in H; (rewrite_strat (topdown (hints core)) in H); subst_evars;
      [ try simplen_rewrite H | try autorewrite with core .. ];
    match type of H with
    | context [ length (list_chunk _ _ _) ] => rewrite block_chunk_length in H
    end).
Ltac simplen' := repeat match goal with
    | [H : @eqlen _ ?T ?a ?b |- context [length ?a] ] => setoid_replace (length a) with (length b) by auto
    | [H : context[length ?x] |- _] => progress ( first [ is_var x | rewrite_ignore H | simplen_rewrite H ] )
    | [H : length ?l = _  |- context [ length ?l ] ] => setoid_rewrite H
    | [H : ?l = _  |- context [ ?l ] ] => setoid_rewrite H
    | [H : ?l = _ , H2 : context [ ?l ] |- _ ] => rewrite H in H2
    | [H : @length ?T ?l = 0 |- context [?l] ] => replace l with (@nil T) by eauto
    | [H : @eqlen _ ?T ?l nil |- context [?l] ] => replace l with (@nil T) by eauto
    | [ |- _ < _ ] => try solve [eapply lt_le_trans; eauto; try lia ]
    end.
Ltac simplen := unfold eqlen; eauto; repeat (try subst; simpl;
    auto; simplen'; autorewrite with core lists); simpl; eauto; try lia.
Lemma xform_synced_array : forall xp st l,
    crash_xform (synced_array xp st l) =p=> synced_array xp st l.
Proof.
(* original proof tokens: 41 *)

(* No more tactics to try *)
Admitted.

Lemma xform_synced_rep : forall xp st l,
    crash_xform (array_rep xp st (Synced l)) =p=> array_rep xp st (Synced l).
Proof.
(* original proof tokens: 20 *)
eapply piff_refl.
(* No more tactics to try *)
Admitted.

Lemma xform_avail_rep : forall xp st nr,
    crash_xform (avail_rep xp st nr) =p=> avail_rep xp st nr.
Proof.
(* original proof tokens: 80 *)

(* No more tactics to try *)
Admitted.

Lemma xform_avail_rep_array_rep : forall xp st nr,
    (forall l', Forall (@Rec.well_formed itemtype) l') ->
    nr * items_per_val <= (RALen xp - st) * items_per_val ->
    xparams_ok xp ->
    st <= RALen xp ->
    crash_xform (avail_rep xp st nr) =p=>
      exists l, array_rep xp st (Synced l) *
      [[ length l = (nr * items_per_val)%nat ]].
Proof.
(* original proof tokens: 144 *)

(* No more tactics to try *)
Admitted.

Lemma xform_unsync_array_avail : forall xp st l,
    crash_xform (unsync_array xp st l) =p=>
      avail_rep xp st (divup (length l) items_per_val).
Proof.
(* original proof tokens: 72 *)

(* No more tactics to try *)
Admitted.

Lemma array_rep_size_ok : forall m xp start st,
    array_rep xp start st m ->
    nr_blocks st <= RALen xp - start.
Proof.
(* original proof tokens: 52 *)

(* No more tactics to try *)
Admitted.

Lemma array_rep_size_ok_pimpl : forall xp st,
    array_rep xp 0 st =p=>
    array_rep xp 0 st * [[ nr_blocks st <= RALen xp ]].
Proof.
(* original proof tokens: 34 *)

(* No more tactics to try *)
Admitted.

Lemma array_rep_avail : forall xp start st,
    array_rep xp start st =p=>
    avail_rep xp start (nr_blocks st).
Proof.
(* original proof tokens: 70 *)

(* No more tactics to try *)
Admitted.

Lemma array_rep_avail_synced : forall xp start items,
    array_rep xp start (Synced items) =p=>
    avail_rep xp start (divup (length items) items_per_val).
Proof.
(* original proof tokens: 16 *)

(* No more tactics to try *)
Admitted.

Lemma avail_rep_split : forall xp start nr n1 n2,
    n1 + n2 = nr ->
    avail_rep xp start nr =p=> avail_rep xp start n1 * avail_rep xp (start + n1) n2.
Proof.
(* original proof tokens: 88 *)

(* No more tactics to try *)
Admitted.

Lemma avail_rep_merge : forall xp start nr n1 n2,
    n1 + n2 = nr ->
    avail_rep xp start n1 * avail_rep xp (start + n1) n2 =p=> avail_rep xp start nr.
Proof.
(* original proof tokens: 56 *)

(* No more tactics to try *)
Admitted.

Lemma helper_add_sub : forall a b c,
    b <= c -> c <= a -> a >= b + (a - c).
Proof.
(* original proof tokens: 12 *)

(* No more tactics to try *)
Admitted.

Lemma helper_add_le : forall a b nb n,
    b <= nb -> n >= a + nb -> a + b <= n.
Proof.
(* original proof tokens: 12 *)
(* generated proof tokens: 18 *)

intros a b nb n H H0. lia.
Qed.

Local Hint Resolve items_per_val_not_0 items_per_val_gt_0 items_per_val_gt_0'.
Lemma array_rep_synced_app : forall xp start na a b,
    length a = na * items_per_val ->
    array_rep xp start (Synced a) *
    array_rep xp (start + (divup (length a) items_per_val)) (Synced b) =p=>
    array_rep xp start (Synced (a ++ b)).
Proof.
(* original proof tokens: 180 *)

(* No more tactics to try *)
Admitted.

Lemma array_rep_synced_app_rev : forall xp start na a b,
    length a = na * items_per_val ->
    array_rep xp start (Synced (a ++ b)) =p=>
    array_rep xp start (Synced a) *
    array_rep xp (start + (divup (length a) items_per_val)) (Synced b).
Proof.
(* original proof tokens: 132 *)

(* No more tactics to try *)
Admitted.

Definition read_all xp count cs :=
    let^ (cs, r) <- BUFCACHE.read_range (RAStart xp) count iunpack nil cs;
    Ret ^(cs, r).
Theorem read_all_ok : forall xp count cs,
    {< F d items,
    PRE:hm         BUFCACHE.rep cs d *
                   [[ length items = (count * items_per_val)%nat /\
                      Forall Rec.well_formed items /\ xparams_ok xp ]] *
                   [[ (F * array_rep xp 0 (Synced items))%pred d ]]
    POST:hm' RET:^(cs, r)
                   BUFCACHE.rep cs d *
                   [[ (F * array_rep xp 0 (Synced items))%pred d ]] *
                   [[ r = items ]]
    CRASH:hm'  exists cs', BUFCACHE.rep cs' d
    >} read_all xp count cs.
Proof.
(* original proof tokens: 71 *)

(* No more tactics to try *)
Admitted.

Lemma vsupd_range_unsync_array : forall xp start items old_vs,
    items_valid xp start items ->
    eqlen old_vs (ipack items) ->
    arrayS (RAStart xp + start) (vsupd_range old_vs (ipack items))
      =p=> unsync_array xp start items.
Proof.
(* original proof tokens: 61 *)

(* No more tactics to try *)
Admitted.

Lemma vsupd_range_nopad_unsync_array : forall xp start (items : itemlist) old_vs,
    items_valid xp start items ->
    length old_vs = divup (length items) items_per_val ->
    arrayS (RAStart xp + start) (vsupd_range old_vs (nopad_ipack items))
      =p=> unsync_array xp start items.
Proof.
(* original proof tokens: 95 *)

(* No more tactics to try *)
Admitted.

Lemma write_aligned_length_helper : forall n l,
    n <= length (map block2val (list_chunk l items_per_val item0)) ->
    n <= divup (length l) items_per_val.
Proof.
(* original proof tokens: 28 *)

(* No more tactics to try *)
Admitted.

Local Hint Resolve write_aligned_length_helper.
Definition write_aligned xp start (items: itemlist) cs :=
    let chunks := nopad_list_chunk items items_per_val in
    cs <- BUFCACHE.write_range ((RAStart xp) + start) (map block2val chunks) cs;
    Ret cs.
Theorem write_aligned_ok : forall xp start new cs,
    {< F d,
    PRE:hm         BUFCACHE.rep cs d *
                   [[ items_valid xp start new ]] *
                   [[ (F * avail_rep xp start (divup (length new) items_per_val))%pred d ]]
    POST:hm' RET: cs
                   exists d', BUFCACHE.rep cs d' *
                   [[ (F * array_rep xp start (Unsync new))%pred d' ]]
    XCRASH:hm'  exists cs' d',
                   BUFCACHE.rep cs' d' *
                   [[ (F * avail_rep xp start (divup (length new) items_per_val)) % pred d' ]]
    >} write_aligned xp start new cs.
Proof.
(* original proof tokens: 74 *)

(* No more tactics to try *)
Admitted.

Lemma vssync_range_sync_array : forall xp start items count vsl,
    items_valid xp start items ->
    length items = (count * items_per_val)%nat ->
    length vsl = count ->
    arrayS (RAStart xp + start) (vssync_range (combine (ipack items) vsl) count)
      =p=> synced_array xp start items.
Proof.
(* original proof tokens: 74 *)

(* No more tactics to try *)
Admitted.

Lemma helper_ipack_length_eq: forall (vsl : list (list valu)) count items,
    eqlen (ipack items) vsl ->
    length items = count * items_per_val ->
    count = length vsl.
Proof.
(* original proof tokens: 38 *)

(* No more tactics to try *)
Admitted.

Lemma helper_ipack_length_eq': forall (vsl : list (list valu)) count items,
    eqlen (ipack items) vsl ->
    length items = count * items_per_val ->
    length vsl = count.
Proof.
(* original proof tokens: 25 *)

(* No more tactics to try *)
Admitted.

Local Hint Resolve helper_ipack_length_eq helper_ipack_length_eq'.
Hint Rewrite ipack_length.
Lemma vssync_range_pimpl : forall xp start items vsl m,
    length items = (length vsl) * items_per_val ->
    m <= (length vsl) ->
    arrayS (RAStart xp + start) (vssync_range (combine (ipack items) vsl) m) =p=>
    arrayS (RAStart xp + start) (combine (ipack items) (repeat nil m ++ skipn m vsl)).
Proof.
(* original proof tokens: 79 *)

(* No more tactics to try *)
Admitted.

Definition sync_aligned xp start count cs :=
    cs <- BUFCACHE.sync_range ((RAStart xp) + start) count cs;
    Ret cs.
Theorem sync_aligned_ok : forall xp start count cs,
    {< F d0 d items,
    PRE:hm         BUFCACHE.synrep cs d0 d * 
                   [[ (F * array_rep xp start (Unsync items))%pred d ]] *
                   [[ length items = (count * items_per_val)%nat ]] *
                   [[ items_valid xp start items /\ sync_invariant F ]]
    POST:hm' RET: cs
                   exists d', BUFCACHE.synrep cs d0 d' *
                   [[ (F * array_rep xp start (Synced items))%pred d' ]]
    CRASH:hm'  exists cs', BUFCACHE.rep cs' d0
    >} sync_aligned xp start count cs.
Proof.
(* original proof tokens: 71 *)

(* No more tactics to try *)
Admitted.

Hint Extern 1 ({{_}} Bind (read_all _ _ _) _) => apply read_all_ok : prog.
Hint Extern 1 ({{_}} Bind (write_aligned _ _ _ _) _) => apply write_aligned_ok : prog.
Hint Extern 1 ({{_}} Bind (sync_aligned _ _ _ _) _) => apply sync_aligned_ok : prog.
End AsyncRecArray.
