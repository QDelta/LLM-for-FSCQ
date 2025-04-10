Require Import String.
Require Import Prog ProgMonad.
Require Import Log.
Require Import Word.
Require Import Lia.
Require Import BasicProg.
Require Import Bool.
Require Import Pred PredCrash.
Require Import DirName.
Require Import Hoare.
Require Import GenSepN.
Require Import ListPred.
Require Import SepAuto.
Require Import Idempotent.
Require Import Inode.
Require Import List ListUtils.
Require Import Balloc.
Require Import Bytes.
Require Import DirTree.
Require Import DirTreeDef.
Require Import DirTreeNames.
Require Import Rec.
Require Import Arith.
Require Import Array.
Require Import FSLayout.
Require Import Cache.
Require Import Errno.
Require Import AsyncDisk.
Require Import GroupLog.
Require Import DiskLogHash.
Require Import SuperBlock.
Require Import DiskSet.
Require Import Lia.
Require Import FunctionalExtensionality.
Require Import VBConv.
Require Import AsyncFS.
Require Import AByteFile.
Require Import TreeCrash.
Require Import DirSep.
Require Import Rounding.
Require Import TreeSeq.
Require Import AtomicCp.
Import DIRTREE.
Import DTCrash.
Import TREESEQ.
Import ATOMICCP.
Import ListNotations.
Set Implicit Arguments.
Notation tree_rep := ATOMICCP.tree_rep.
Hint Resolve valubytes_ne_O.
Hint Resolve valubytes_ge_O.
Fixpoint dsupd_iter ds bnl vsl:=
match vsl with
| nil => ds
| h::t => match bnl with
               | nil => ds
               | h'::t' => dsupd_iter (dsupd ds h' h) t' t
              end
end.
Fixpoint tsupd_iter ts pathname off vsl:=
match vsl with
| nil => ts
| h::t => tsupd_iter (tsupd ts pathname off h) pathname (S off) t
end.
Definition hpad_length len:=
match (len mod valubytes) with
| O => O
| S _ => valubytes - len mod valubytes
end.
Definition tpad_length l:=
  match l mod valubytes with 
  | O => valubytes
  | S _ => l mod valubytes
  end.
Ltac split_hypothesis_helper:=
  match goal with
  | [ H: exists _, _ |- _ ] => destruct H
  | [ H: _ /\ _ |- _] => destruct H
  end.
Ltac split_hypothesis:= repeat split_hypothesis_helper.
Ltac rewrite_proto:= 
match goal with
| [H: proto_bytefile_valid _ ?pfy |- context[PByFData ?pfy] ] => rewrite H
end.
Ltac length_rewrite_l_helper:= 
  rewrite app_length || rewrite map_length 
  || rewrite concat_hom_length with (k:= valubytes)
  || rewrite merge_bs_length || rewrite valu2list_len
  || rewrite firstn_length_l || rewrite skipn_length
  || rewrite valuset2bytesets_len || rewrite valuset2bytesets_rec_len
  || rewrite length_updN || (rewrite list_split_chunk_length; try rewrite min_l)
  || (rewrite get_sublist_length; try rewrite min_l) || (rewrite combine_length; try rewrite min_l).
Ltac length_rewrite_l:= repeat (length_rewrite_l_helper; simpl); try lia.
Ltac length_rewrite_r_helper:= 
  rewrite app_length || rewrite map_length 
  || rewrite concat_hom_length with (k:= valubytes)
  || rewrite merge_bs_length || rewrite valu2list_len
  || rewrite firstn_length_r || rewrite skipn_length
  || rewrite valuset2bytesets_len || rewrite valuset2bytesets_rec_len
  || rewrite length_updN || (rewrite list_split_chunk_length; try rewrite min_r)
  || (rewrite get_sublist_length; try rewrite min_r) || (rewrite combine_length;  try rewrite min_r).
Ltac length_rewrite_r:= repeat (length_rewrite_r_helper; simpl); try lia.
Ltac length_rewrite_safe_helper:= 
  rewrite app_length || rewrite map_length 
  || rewrite concat_hom_length with (k:= valubytes)
  || rewrite merge_bs_length || rewrite valu2list_len
  || rewrite firstn_length || rewrite skipn_length
  || rewrite valuset2bytesets_len || rewrite valuset2bytesets_rec_len
  || rewrite length_updN || rewrite list_split_chunk_length
  || rewrite get_sublist_length || rewrite combine_length.
Ltac length_rewrite_safe:= repeat (length_rewrite_safe_helper; simpl); try lia.
Opaque LOG.idempred.
Opaque crash_xform.
Lemma concat_valuset2bytesets_map_fstnil_comm: forall l,
 (concat (map valuset2bytesets (map (fun x : valuset => (fst x, [])) l))) =
    map (fun x : byteset => (fst x, [])) (concat (map valuset2bytesets l)).
Proof.
(* original proof tokens: 211 *)

(* No more tactics to try *)
Admitted.

Lemma merge_bs_map_fst: forall l l',
map fst (merge_bs l l') = l.
Proof.
(* original proof tokens: 50 *)

(* No more tactics to try *)
Admitted.

Lemma treeseq_upd_off_tree_rep: forall ts Ftree srcpath tmppath srcinum file tinum dstbase dstname dstfile vs off ,
   treeseq_pred (tree_rep Ftree srcpath tmppath srcinum file tinum dstbase dstname dstfile) ts ->
   treeseq_pred (tree_rep Ftree srcpath tmppath srcinum file tinum dstbase dstname  dstfile) (tsupd ts tmppath off vs).
Proof.
(* original proof tokens: 276 *)

(* No more tactics to try *)
Admitted.

Lemma treeseq_pushd_tree_rep: forall ts t Ftree srcpath tmppath srcinum file tinum dstbase dstname dstfile,
   tree_rep Ftree srcpath tmppath srcinum file tinum dstbase dstname dstfile t ->
   treeseq_pred (tree_rep Ftree srcpath tmppath srcinum file tinum dstbase dstname dstfile) ts ->
   treeseq_pred (tree_rep Ftree srcpath tmppath srcinum file tinum dstbase dstname dstfile) (pushd t ts).
Proof.
(* original proof tokens: 118 *)
(* generated proof tokens: 21 *)

intros.
eapply treeseq_pred_pushd; eauto.
Qed.

Lemma treeseq_upd_iter_tree_rep: forall  vsl ts Ftree srcpath tmppath srcinum file tinum dstbase dstname dstfile off,
   treeseq_pred (tree_rep Ftree srcpath tmppath srcinum file tinum dstbase dstname dstfile) ts ->
   treeseq_pred (tree_rep Ftree srcpath tmppath srcinum file tinum dstbase dstname dstfile) (tsupd_iter ts tmppath off vsl).
Proof.
(* original proof tokens: 37 *)

(* No more tactics to try *)
Admitted.

Definition synced_bdata (data: list byteset):= (map (fun x => (x, nil:list byte)) (map fst data)).
Lemma synced_bdata_length: forall l, length (synced_bdata l) = length l.
Proof.
(* original proof tokens: 25 *)
(* generated proof tokens: 14 *)

induction l; simpl; auto.
Qed.

Lemma bytefile_exists: forall f,
  roundup (# (INODE.ABytes (DFAttr f))) valubytes 
              = Datatypes.length (DFData f) * valubytes ->
  AByteFile.rep f 
      {| ByFData:= firstn (# (INODE.ABytes (DFAttr f)))
                        (concat (map valuset2bytesets (DFData f)));
        ByFAttr := (DFAttr f)|}.
Proof.
(* original proof tokens: 292 *)

(* No more tactics to try *)
Admitted.

Lemma tree_rep_update_subtree: forall ts tf ilist frees Ftree srcpath tmppath srcinum file tinum dstbase dstname dstfile,
   treeseq_pred (tree_rep Ftree srcpath tmppath srcinum file tinum dstbase dstname  dstfile) ts ->
   tree_rep Ftree srcpath tmppath srcinum file tinum dstbase dstname dstfile
                        {| TStree:= update_subtree tmppath (TreeFile tinum tf) (TStree ts !!);
                            TSilist:= ilist;
                            TSfree:= frees |}.
Proof.
(* original proof tokens: 378 *)

(* No more tactics to try *)
Admitted.

Lemma roundup_div_mul: forall a b,
b<>0 -> roundup a b / b * b = roundup a b.
Proof.
(* original proof tokens: 33 *)

(* No more tactics to try *)
Admitted.

Lemma in_not_in_name_eq: forall A (name name': A) (names: list A),
  ~ In name names ->
  In name' names ->
  name <> name'.
Proof.
(* original proof tokens: 59 *)

(* No more tactics to try *)
Admitted.

Lemma in_add_to_list_or: forall  tree name name' f,
  In name' (map fst (add_to_list name f tree)) ->
  name = name' \/ In name' (map fst tree).
Proof.
(* original proof tokens: 87 *)
(* generated proof tokens: 13 *)

apply in_add_to_list_or.
Qed.

Lemma NoDup_add_to_list: forall tree f fname,
  NoDup (map fst tree) ->
  ~ In fname (map fst tree) ->
  NoDup (map fst (add_to_list fname f tree)).
Proof.
(* original proof tokens: 154 *)
(* generated proof tokens: 13 *)

apply NoDup_add_to_list.
Qed.

Lemma in_add_to_list_tree_or: forall  tree name t t',
  In t (add_to_list name t' tree) ->
  t = (name, t') \/ In t tree.
Proof.
(* original proof tokens: 101 *)
(* generated proof tokens: 14 *)

apply in_add_to_list_tree_or.
Qed.

Hint Extern 1 (Forall (fun sublist : list byteset => Datatypes.length sublist = valubytes)
  (PByFData _)) => eapply proto_len; eauto.
Lemma proto_len_updN: forall f pfy a v,
proto_bytefile_valid f pfy ->
Forall (fun sublist : list byteset => Datatypes.length sublist = valubytes)
  (PByFData pfy) ⟦ a := valuset2bytesets v⟧.
Proof.
(* original proof tokens: 70 *)

(* No more tactics to try *)
Admitted.

Hint Extern 1 (Forall (fun sublist : list byteset => Datatypes.length sublist = valubytes)
  (PByFData _) ⟦ _ := valuset2bytesets _⟧) => eapply proto_len_updN; eauto.
Lemma bfile_bytefile_selN_firstn_skipn: forall f fy a b data F def,
AByteFile.rep f fy ->
(F * arrayN (ptsto (V:=byteset)) (a * valubytes + b) data)%pred (list2nmem (ByFData fy)) ->
b + length data <= valubytes ->
firstn (length data) (skipn b (valuset2bytesets (selN (DFData f) a def))) = data.
Proof.
(* original proof tokens: 292 *)

(* No more tactics to try *)
Admitted.

Ltac resolve_a_helper:= 
  repeat rewrite app_length;
  repeat rewrite map_length;
  repeat rewrite merge_bs_length; auto;
  repeat rewrite skipn_length;
  repeat rewrite valu2list_len;
  try rewrite firstn_length_l; auto;
  repeat rewrite <- concat_hom_firstn with (k:= valubytes); auto;
  repeat rewrite firstn_length_l; auto;
  try lia;
  try rewrite valu2list_len; try lia.
Ltac resolve_a:= 
    match goal with
      | [ |- _ >= _ ] => resolve_a_helper
      | [ |- _ - _ >= _  ] => resolve_a_helper
      | [ |- _ < _  ] => resolve_a_helper
      | [ |- _ - _ < _  ] => resolve_a_helper
      | [ |- _ - _ - _ < _ ] => resolve_a_helper
      | [ |- _ - _ - _ < _ - _ - _] => resolve_a_helper
    end.
Lemma exists_impl: forall (bsl: @Mem.mem addr addr_eq_dec _) (F: pred) a b_1 b_2,
    (F ✶ (exists old : list byte,
      a |-> (b_1, old) ✶ ⟦⟦ incl (b_1 :: old) (b_1 :: b_2) ⟧⟧))%pred bsl <->
   (exists old, (F ✶ a |-> (b_1, old) ✶ ⟦⟦ incl (b_1 :: old) (b_1 :: b_2) ⟧⟧))%pred bsl.
Proof.
(* original proof tokens: 19 *)

(* No more tactics to try *)
Admitted.

Lemma incl_dup_head: forall A (a: A) b c,
    incl (a::b) c -> incl (a::a::b) c.
Proof.
(* original proof tokens: 35 *)

(* No more tactics to try *)
Admitted.

Lemma dsupd_iter_dsupd_head: forall bnl vsl bn vs ds,
  dsupd_iter (dsupd ds bn vs) bnl vsl = dsupd_iter ds (bn::bnl) (vs::vsl).
Proof.
(* original proof tokens: 13 *)
(* generated proof tokens: 10 *)

reflexivity.
Qed.

Lemma dsupd_iter_dsupd_tail: forall bnl vsl bn vs ds,
  length bnl = length vsl ->
  dsupd (dsupd_iter ds bnl vsl) bn vs = dsupd_iter ds (bnl++[bn]) (vsl++[vs]).
Proof.
(* original proof tokens: 72 *)

(* No more tactics to try *)
Admitted.

Lemma combine_app_tail: forall A B (l1: list A) (l2: list B) e1 e2,
  Datatypes.length l1 = Datatypes.length l2 ->
  combine (l1++[e1]) (l2++[e2]) = (combine l1 l2 ++ [(e1, e2)])%list.
Proof.
(* original proof tokens: 75 *)

(* No more tactics to try *)
Admitted.

Lemma map_single: forall A B (f: A -> B) e,
  map f [e] = [f e].
Proof.
(* original proof tokens: 13 *)

(* No more tactics to try *)
Admitted.

Lemma get_sublist_app_tail: forall A (l: list A) a b def,
  length l >= S (a + b) ->
  get_sublist l a (S b) = (get_sublist l a b ++ [selN l (a+b) def])%list.
Proof.
(* original proof tokens: 118 *)

(* No more tactics to try *)
Admitted.

Lemma firstn_eq_nil: forall A n (l: list A),
  firstn n l = nil <-> n = 0 \/ l = nil.
Proof.
(* original proof tokens: 58 *)

(* No more tactics to try *)
Admitted.

Lemma skipn_eq_nil: forall A (l: list A)  n ,
  skipn n l = nil <-> n >= length l \/ l = nil.
Proof.
(* original proof tokens: 89 *)
firstorder.
(* No more tactics to try *)
Admitted.

Lemma bfile_selN_eq: forall f f' fy fy' F F' a l,
   AByteFile.rep f fy ->
   AByteFile.rep f' fy' ->
   (F ✶ arrayN (ptsto (V:=byteset)) (a * valubytes) l)%pred (list2nmem (ByFData fy)) ->
   (F' ✶ arrayN (ptsto (V:=byteset)) (a * valubytes) l)%pred (list2nmem (ByFData fy')) ->
   length l >= valubytes ->
   selN (DFData f) a valuset0 = selN (DFData f') a valuset0.
Proof.
(* original proof tokens: 885 *)

(* No more tactics to try *)
Admitted.

Lemma le_lt_false: forall a b, a <= b -> a > b -> False.
Proof.
(* original proof tokens: 10 *)
(* generated proof tokens: 35 *)

intros a b Hle Hgt.
apply le_not_gt in Hle. 
apply Hle in Hgt.
contradiction.
Qed.

Lemma combine_cons: forall A B (a:A) (b:B) c d,
   (a, b)::combine c d = combine (a::c) (b::d).
Proof.
(* original proof tokens: 12 *)
(* generated proof tokens: 11 *)

simpl. reflexivity.
Qed.

Lemma tsupd_iter_tsupd_head: forall vsl vs ts s pathname,
  tsupd_iter (tsupd ts pathname s vs) pathname (S s) vsl = tsupd_iter ts pathname s (vs::vsl).
Proof.
(* original proof tokens: 13 *)

(* No more tactics to try *)
Admitted.

Lemma tsupd_iter_tsupd_tail: forall vsl s a vs ts pathname,
  a = s + length vsl ->
  tsupd (tsupd_iter ts pathname s vsl) pathname a vs = tsupd_iter ts pathname s (vsl++[vs]).
Proof.
(* original proof tokens: 45 *)

(* No more tactics to try *)
Admitted.

Lemma dsupd_iter_merge: forall ds bnl data f f' fy fy' block_off bn Fd old_data num_of_full_blocks,
   AByteFile.rep f fy ->
   AByteFile.rep f' fy' ->
   (Fd ✶ arrayN (ptsto (V:=byteset)) (block_off * valubytes) old_data)%pred
  (list2nmem (ByFData fy)) ->
  length old_data = length data ->
  length data = num_of_full_blocks * valubytes ->
  length bnl < num_of_full_blocks ->
  (Fd * arrayN (ptsto (V:=byteset))
     (block_off * valubytes) (merge_bs (firstn (length bnl * valubytes) data) (firstn (length bnl * valubytes) old_data))
 ✶ arrayN (ptsto (V:=byteset))
     ((block_off + Datatypes.length bnl) * valubytes) (skipn (length bnl * valubytes) old_data))%pred
  (list2nmem (ByFData fy')) ->
   (dsupd
        (dsupd_iter ds bnl
           (combine
              (map list2valu
                 (list_split_chunk (Datatypes.length bnl) valubytes
                    (firstn (Datatypes.length bnl * valubytes) data)))
              (map vsmerge
                 (get_sublist (DFData f) block_off (Datatypes.length bnl)))))
        bn
        (list2valu
           (get_sublist data (Datatypes.length bnl * valubytes) valubytes),
        vsmerge (selN (DFData f') (block_off + Datatypes.length bnl) valuset0 ))) = 
        dsupd_iter ds (bnl++[bn])
              (combine
                 (map list2valu
                    (list_split_chunk (S (Datatypes.length bnl)) valubytes
                       (firstn ((S (Datatypes.length bnl)) * valubytes) data)))
                 (map vsmerge (get_sublist (DFData f) block_off (S (Datatypes.length bnl))))).
Proof.
(* original proof tokens: 1216 *)

(* No more tactics to try *)
Admitted.

Lemma tsupd_tsupd_iter_merge: forall ts pathname (bnl: list addr) data f f' fy fy' block_off Fd old_data num_of_full_blocks,
   AByteFile.rep f fy ->
   AByteFile.rep f' fy' ->
   (Fd ✶ arrayN (ptsto (V:=byteset)) (block_off * valubytes) old_data)%pred
  (list2nmem (ByFData fy)) ->
  length old_data = length data ->
  length data = num_of_full_blocks * valubytes ->
  length bnl < num_of_full_blocks ->
  (Fd * arrayN (ptsto (V:=byteset))
     (block_off * valubytes) (merge_bs (firstn (length bnl * valubytes) data) (firstn (length bnl * valubytes) old_data))
 ✶ arrayN (ptsto (V:=byteset))
     ((block_off + Datatypes.length bnl) * valubytes) (skipn (length bnl * valubytes) old_data))%pred
  (list2nmem (ByFData fy')) ->
   (tsupd
        (tsupd_iter ts pathname block_off
           (combine
              (map list2valu
                 (list_split_chunk (Datatypes.length bnl) valubytes
                    (firstn (Datatypes.length bnl * valubytes) data)))
              (map vsmerge
                 (get_sublist (DFData f) block_off (Datatypes.length bnl)))))
        pathname (block_off + Datatypes.length bnl)
        (list2valu
           (get_sublist data (Datatypes.length bnl * valubytes) valubytes),
        vsmerge (selN (DFData f') (block_off + Datatypes.length bnl) valuset0 ))) = 
        tsupd_iter ts pathname block_off
              (combine
                 (map list2valu
                    (list_split_chunk (S (Datatypes.length bnl)) valubytes
                       (firstn ((S (Datatypes.length bnl)) * valubytes) data)))
                 (map vsmerge (get_sublist (DFData f) block_off (S (Datatypes.length bnl))))).
Proof.
(* original proof tokens: 1247 *)

(* No more tactics to try *)
Admitted.

Lemma arrayN_merge_bs_split_firstn: forall l l' a b c,
    arrayN (ptsto (V:=byteset)) a (merge_bs (firstn b l) (firstn b l')) *
    arrayN (ptsto (V:=byteset)) (a + b) 
        (merge_bs (firstn c (skipn b l)) (firstn c (skipn b l'))) <=p=>
    arrayN (ptsto (V:=byteset)) a (merge_bs (firstn (b + c) l) (firstn (b + c) l')).
Proof.
(* original proof tokens: 137 *)

(* No more tactics to try *)
Admitted.

Lemma diskIs_ptsto_updN: forall {V} (l l': list V) a v,
(diskIs (mem_except (list2nmem l) a) * a |-> v)%pred (list2nmem l') ->
a < length l ->
l' = updN l a v.
Proof.
(* original proof tokens: 47 *)

(* No more tactics to try *)
Admitted.

Lemma list2nmem_arrayN_app_iff_general:
  forall (A : Type) (F : pred) (l l' : list A) a,
  a = length l ->
  (F ✶ arrayN (ptsto (V:=A)) a l')%pred (list2nmem (l ++ l')) ->
  F (list2nmem l).
Proof.
(* original proof tokens: 26 *)
unfold LOG.arrayP.
(* No more tactics to try *)
Admitted.

Lemma proto_bytefile_bytefile_arrayN_app_end_eq: forall a l f pfy ufy fy F,
proto_bytefile_valid f pfy ->
unified_bytefile_valid pfy ufy ->
bytefile_valid ufy fy ->
(F * arrayN (ptsto (V:=byteset)) (a * valubytes) l)%pred (list2nmem (ByFData fy)) ->
length l = length (ByFData fy) - a * valubytes ->
l <> nil ->
(ByFData fy) = (concat (firstn a (PByFData pfy)) ++ l)%list.
Proof.
(* original proof tokens: 142 *)

(* No more tactics to try *)
Admitted.

Lemma fold_valuset2bytesets: forall f block_off,
(map (list2byteset byte0)
     (valuset2bytesets_rec
        (valu2list (fst (selN (DFData f) block_off valuset0))
         :: map valu2list (snd (selN (DFData f) block_off valuset0))) valubytes)) = valuset2bytesets (selN (DFData f) block_off valuset0).
Proof.
(* original proof tokens: 9 *)

(* No more tactics to try *)
Admitted.

Lemma ppmmm_1_5_cancel: forall a b c d e,
a + b + c - d - a - e = b + c - d - e.
Proof.
(* original proof tokens: 10 *)

(* No more tactics to try *)
Admitted.

Lemma list2nmem_arrayN_bound_nonnil: forall V (l: list V) a F l',
l <> nil ->
(F * arrayN (ptsto(V:= V)) a l)%pred (list2nmem l') ->
a + length l <= length l'.
Proof.
(* original proof tokens: 36 *)

(* No more tactics to try *)
Admitted.

Lemma sep_star_modified_bytefile: forall f pfy ufy fy Fd block_off head_data old_data tail_data data, 
proto_bytefile_valid f pfy ->
unified_bytefile_valid pfy ufy ->
bytefile_valid ufy fy ->
ByFAttr fy = DFAttr f ->
# (INODE.ABytes (ByFAttr fy)) = length (ByFData fy) ->
roundup (length (ByFData fy)) valubytes = length (DFData f) * valubytes ->
(Fd ✶ arrayN (ptsto (V:=byteset)) (block_off * valubytes) (head_data ++ old_data++tail_data))%pred (list2nmem (ByFData fy)) ->
length old_data = length data ->
length data > 0 ->
length head_data + length data <= valubytes ->
Init.Nat.min
       (length (ByFData fy) -
        (block_off * valubytes + length head_data + length data))
       (valubytes - (length head_data + length data)) = length tail_data ->
       
(((Fd
   ✶ arrayN (ptsto (V:=byteset)) (block_off * valubytes)
       (merge_bs (map fst head_data) head_data))
  ✶ arrayN (ptsto (V:=byteset)) (block_off * valubytes + length head_data)
      (merge_bs data old_data))
 ✶ arrayN (ptsto (V:=byteset))
     (block_off * valubytes + length head_data + length data)
     (merge_bs (map fst tail_data) tail_data))%pred
  (list2nmem
     (ByFData
        {|
        ByFData := firstn (length (ByFData fy))
                     (concat
                        (PByFData pfy) ⟦ block_off
                        := valuset2bytesets
                             (list2valu
                                (firstn (length head_data)
                                   (valu2list (fst (selN (DFData f) block_off valuset0 ))) ++
                                 data ++
                                 skipn (length head_data + length data)
                                   (valu2list (fst (selN (DFData f) block_off valuset0 )))),
                             vsmerge (selN (DFData f) block_off valuset0 )) ⟧);
        ByFAttr := ByFAttr fy |})).
Proof.
(* original proof tokens: 2643 *)

(* No more tactics to try *)
Admitted.

Lemma map_app_tail: forall A B (f: A -> B) (l: list A) e,
    (map f l ++ [f e])%list = map f (l ++ [e])%list.
Proof.
(* original proof tokens: 19 *)

(* No more tactics to try *)
Admitted.

Lemma dir2flatmem2_tsupd_updN: forall Ftree pathname inum f f' ts block_off v,
        tree_names_distinct (TStree ts !!) ->
        (Ftree ✶ pathname |-> File inum f)%pred (dir2flatmem2 (TStree ts !!)) ->
        (Ftree ✶ pathname |-> File inum f')%pred
        (dir2flatmem2 (TStree (tsupd ts pathname block_off v) !!)) ->
        DFData f' = updN (DFData f) block_off v.
Proof.
(* original proof tokens: 124 *)

(* No more tactics to try *)
Admitted.

Lemma tree_names_distinct_treeseq_one_upd': forall t tmppath off vs,
        tree_names_distinct (TStree t) ->
        tree_names_distinct (TStree (treeseq_one_upd t tmppath off vs)).
Proof.
(* original proof tokens: 69 *)

(* No more tactics to try *)
Admitted.

Lemma tree_names_distinct_tsupd: forall t tmppath off vs,
        tree_names_distinct (TStree t !!) ->
        tree_names_distinct (TStree (tsupd t tmppath off vs) !!).
Proof.
(* original proof tokens: 32 *)

(* No more tactics to try *)
Admitted.

Lemma bfile_selN_tsupd_iter_eq: forall l Ftree pathname inum f f' ts block_off a,
    tree_names_distinct (TStree ts !!) ->
    (Ftree ✶ pathname |-> File inum f)%pred (dir2flatmem2 (TStree ts !!)) ->
    (Ftree ✶ pathname |-> File inum f')%pred
        (dir2flatmem2
           (TStree
              (tsupd_iter ts pathname block_off l) !!)) ->
        length l <= a ->
      selN (DFData f) (block_off + a) valuset0 =
      selN (DFData f') (block_off + a) valuset0.
Proof.
(* original proof tokens: 281 *)

(* No more tactics to try *)
Admitted.

Lemma tree_names_distinct_tsupd_iter:forall l ts pathname off,
        tree_names_distinct (TStree ts !!) ->
        tree_names_distinct
        (TStree
        (tsupd_iter ts pathname off l) !!).
Proof.
(* original proof tokens: 36 *)

(* No more tactics to try *)
Admitted.

Lemma roundup_div_S_eq: forall a b,
        b <> 0 ->
        a mod b > 0 ->
        roundup a b / b = S (a / b).
Proof.
(* original proof tokens: 50 *)

(* No more tactics to try *)
Admitted.

Lemma roundup_eq_mod_O: forall a b,
        b <> 0 ->
        a mod b = 0 ->
        roundup a b = a.
Proof.
(* original proof tokens: 33 *)

(* No more tactics to try *)
Admitted.

Lemma inlen_bfile_S: forall f fy l block_off Fd,
        AByteFile.rep f fy ->
        (Fd * arrayN (ptsto (V:=byteset)) (block_off * valubytes)
              l )%pred (list2nmem (ByFData fy)) ->
        length l > 0 ->
        S block_off <= length (DFData f).
Proof.
(* original proof tokens: 119 *)

(* No more tactics to try *)
Admitted.

Lemma min_eq_O: forall a b,
        min a b = 0 -> a = 0 \/ b = 0.
Proof.
(* original proof tokens: 40 *)

(* No more tactics to try *)
Admitted.

Lemma tsupd_tsupd_iter_merge': forall ts pathname data f fy 
        block_off Fd old_data tail_data,
   AByteFile.rep f fy ->
    ((Fd
       ✶ (arrayN (ptsto (V:=byteset)) (block_off * valubytes)
            (firstn (length data / valubytes * valubytes) old_data)
          ✶ arrayN (ptsto (V:=byteset))
              ((block_off + length data / valubytes) * valubytes)
              (skipn (length data / valubytes * valubytes) old_data)))
      ✶ arrayN (ptsto (V:=byteset))
          (block_off * valubytes + length old_data) tail_data)%pred
       (list2nmem (ByFData fy)) ->
  length old_data = length data ->
  0 < length (skipn (length data / valubytes * valubytes) data) ->
  min (length (ByFData fy) - (block_off * valubytes + length data))
       (hpad_length (length data)) = length tail_data ->
   tsupd
  (tsupd_iter ts pathname block_off
     (combine
        (map list2valu
           (list_split_chunk (length data / valubytes) valubytes
              (firstn (length data / valubytes * valubytes) data)))
        (map vsmerge
           (get_sublist (DFData f) block_off
              (length data / valubytes))))) pathname
  (block_off + length data / valubytes)
  (list2valu
     (skipn (length data / valubytes * valubytes) data ++
      skipn
        (length (skipn (length data / valubytes * valubytes) data))
        (valu2list
           (fst (selN (DFData f) (block_off + length data / valubytes) valuset0)))),
  vsmerge (selN (DFData f) (block_off + length data / valubytes) valuset0)) =
tsupd_iter ts pathname block_off
  (combine
     (map list2valu
        (list_split_chunk
           (roundup (length data) valubytes / valubytes) valubytes
           (data ++
            skipn (length data mod valubytes)
              (valu2list
                 (fst (selN (DFData f) (block_off + length data / valubytes) valuset0))))))
     (map vsmerge
        (firstn (roundup (length data) valubytes / valubytes)
           (skipn block_off (DFData f))))).
Proof.
(* original proof tokens: 725 *)

(* No more tactics to try *)
Admitted.

Lemma roundup_mod_0: forall a b,
    b <> 0 -> roundup a b mod b = 0.
Proof.
(* original proof tokens: 21 *)

(* No more tactics to try *)
Admitted.

Lemma list_split_chunk_app_l: forall {A} a  b (l1 l2: list A),
   length l1 >= a * b ->
   list_split_chunk a b (l1++l2) = list_split_chunk a b l1.
Proof.
(* original proof tokens: 102 *)

(* No more tactics to try *)
Admitted.

Lemma mod_lt_nonzero: forall a b,
   b <> 0 -> a > 0 -> a < b -> a mod b <> 0.
Proof.
(* original proof tokens: 46 *)

(* No more tactics to try *)
Admitted.

Lemma roundup_lt_one: forall a b,
  b <> 0 -> a > 0 -> a <= b -> roundup a b = b.
Proof.
(* original proof tokens: 26 *)

(* No more tactics to try *)
Admitted.

Lemma le_sub_le_add_l': forall a b c,
    a > 0 -> a <= b - c -> c + a <= b.
Proof.
(* original proof tokens: 10 *)

(* No more tactics to try *)
Admitted.

Lemma le_sub_le_add_r': forall a b c,
    a > 0 -> a <= b - c -> a + c <= b.
Proof.
(* original proof tokens: 10 *)

(* No more tactics to try *)
Admitted.

Lemma lt_sub_lt_add_l': forall a b c,
    a < b - c -> c + a < b.
Proof.
(* original proof tokens: 10 *)

(* No more tactics to try *)
Admitted.

Lemma lt_sub_lt_add_r': forall a b c,
    a < b - c -> a + c < b.
Proof.
(* original proof tokens: 10 *)

(* No more tactics to try *)
Admitted.

Lemma mm_dist': forall a b c,
  b >= c -> a - (b - c) = a + c - b.
Proof.
(* original proof tokens: 10 *)

(* No more tactics to try *)
Admitted.

Lemma bytefile_length_eq: forall f f' fy fy',
  AByteFile.rep f fy ->
  AByteFile.rep f' fy' ->
  ByFAttr fy = ByFAttr fy' ->
  length (ByFData fy) = length (ByFData fy').
Proof.
(* original proof tokens: 36 *)

(* No more tactics to try *)
Admitted.

Lemma roundup_div_minus_S: forall a b,
  b<>0 -> a >= b -> S (roundup (a - b) b / b) = roundup a b / b.
Proof.
(* original proof tokens: 75 *)

(* No more tactics to try *)
Admitted.

Lemma list_split_chunk_cons': forall A a b (l l': list A),
  length l = b ->
  l :: list_split_chunk a b l' = list_split_chunk (S a) b (l ++ l').
Proof.
(* original proof tokens: 65 *)

(* No more tactics to try *)
Admitted.

Lemma app_assoc_middle_2': forall A (l1 l2 l3 l4: list A),
  (l1 ++ l2 ++ l3 ++ l4)%list =  (l1 ++ (l2 ++ l3) ++ l4)%list.
Proof.
(* original proof tokens: 15 *)
(* generated proof tokens: 30 *)

Proof.
  intros A l1 l2 l3 l4.
  rewrite <- app_assoc.
  reflexivity.
Qed.

Lemma skipn_updN_oob_eq :
forall (A : Type) (l : list A) (i n : addr) (v : A),
n > i -> skipn n (l ⟦ i := v ⟧) = skipn n l.
Proof.
(* original proof tokens: 105 *)

(* No more tactics to try *)
Admitted.

Lemma roundup_div_minus:
  forall a b : addr,
  b <> 0 -> a >= b -> roundup (a - b) b / b = roundup a b / b - 1.
Proof.
(* original proof tokens: 32 *)

(* No more tactics to try *)
Admitted.

Lemma list_split_chunk_firstn_cancel: forall A a b (l: list A),
  list_split_chunk a b (firstn (a * b) l) = list_split_chunk a b l.
Proof.
(* original proof tokens: 48 *)

(* No more tactics to try *)
Admitted.

Lemma treeseq_pred_tree_rep_latest: forall Ftree srcpath tmppath srcinum file tinum dstbase dstname
           dstfile ts,  
  treeseq_pred
        (tree_rep Ftree srcpath tmppath srcinum file tinum dstbase dstname
           dstfile) ts ->
  tree_rep Ftree srcpath tmppath srcinum file tinum dstbase dstname dstfile
  ts !!.
Proof.
(* original proof tokens: 54 *)
(* generated proof tokens: 15 *)

apply treeseq_pred_tree_rep_latest.
Qed.

