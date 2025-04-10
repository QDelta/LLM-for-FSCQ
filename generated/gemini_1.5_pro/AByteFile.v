Require Import Min.
Require Import Arith.
Require Import Word.
Require Import Prog ProgMonad.
Require Import Hoare.
Require Import SepAuto.
Require Import BasicProg.
Require Import Lia.
Require Import Log.
Require Import Array.
Require Import List ListUtils.
Require Import Bool.
Require Import Setoid.
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
Require Import Inode.
Require Import GenSepAuto.
Require Import DiskSet.
Require Import DirTreeDef.
Require Import Bytes.
Require Import VBConv.
Require Import Fscq.Hashmap.
Require Import Errno.
Require Import PeanoNat.
Require Import Pred PredCrash.
Require Import Rounding.
Set Implicit Arguments.
Definition attr := INODE.iattr.
Definition attr0 := INODE.iattr0.
Record proto_bytefile := mk_proto_bytefile {
  PByFData : list (list byteset)
}.
Definition proto_bytefile0 := mk_proto_bytefile nil.
Record unified_bytefile := mk_unified_bytefile {
  UByFData : list byteset
}.
Definition unified_bytefile0 := mk_unified_bytefile nil.
Record bytefile := mk_bytefile {
  ByFData : list byteset;
  ByFAttr : INODE.iattr
}.
Definition bytefile0 := mk_bytefile nil attr0.
Definition bfiledata2protobytefile fd : proto_bytefile :=
mk_proto_bytefile (map valuset2bytesets fd).
Definition protobytefile2unifiedbytefile pfy : unified_bytefile :=
mk_unified_bytefile (concat (PByFData pfy)).
Definition unifiedbytefile2bytefiledata ufy len: list byteset :=
(firstn len (UByFData ufy)).
Definition unifiedbytefile2bytefile ufy len iattr: bytefile :=
mk_bytefile (firstn len (UByFData ufy)) iattr.
Definition bfiledata2bytefiledata fd len: list byteset:=
unifiedbytefile2bytefiledata (protobytefile2unifiedbytefile (bfiledata2protobytefile fd)) len.
Definition bfile2bytefile f len: bytefile:=
unifiedbytefile2bytefile (protobytefile2unifiedbytefile (bfiledata2protobytefile (DFData f))) len (DFAttr f).
Fixpoint upd_range {V} (m : @Mem.mem addr addr_eq_dec V) (a : addr) (l : list V) : @Mem.mem addr _ V :=
match l with
| nil => m
| h::t => upd_range (Mem.upd m a h) (a+1) t
end.
Definition some_strip {V} (o: option V) def: V :=
match o with
	| None => def
	| Some v => v
end.
Ltac split_hypothesis_helper:=
  match goal with
  | [ H: exists _, _ |- _ ] => destruct H
  | [ H: _ /\ _ |- _] => destruct H
  end.
Ltac split_hypothesis:= repeat split_hypothesis_helper.
Definition proto_bytefile_valid f pfy: Prop :=
(PByFData pfy) = map valuset2bytesets (DFData f).
Definition unified_bytefile_valid pfy ufy: Prop := 
UByFData ufy = concat (PByFData pfy).
Definition bytefile_valid ufy fy: Prop :=
ByFData fy = firstn (length(ByFData fy)) (UByFData ufy).
Definition rep (f:dirfile) (fy:bytefile) :=
  exists pfy ufy,
    proto_bytefile_valid f pfy /\
    unified_bytefile_valid pfy ufy /\
    bytefile_valid ufy fy /\ 
    ByFAttr fy = DFAttr f /\
    #(INODE.ABytes (ByFAttr fy)) = length (ByFData fy) /\
    (roundup (length (ByFData fy)) valubytes = (length (DFData f)) * valubytes)%nat.
Lemma diskIs_id: forall AT AEQ V (m:Mem.mem), @diskIs AT AEQ V m m.
Proof.
(* skipped proof tokens: 15 *)
Admitted.
Lemma addr_id: forall A (l: list A) a def, 
a < length l ->
((diskIs (mem_except (list2nmem l) a)) * a |-> (selN l a def))%pred (list2nmem l).
Proof.
(* skipped proof tokens: 34 *)
Admitted.
Lemma mem_except_range_O: forall AEQ V (m: @Mem.mem _ AEQ V) a,
mem_except_range m a 0 = m.
Proof.
(* skipped proof tokens: 52 *)
Admitted.
Fact out_except_range_then_in: forall (l: list valuset) s a n def,
a < length l ->
a < s \/ a >= s + n ->
(exists F0 : pred, (sep_star (AEQ:= addr_eq_dec) F0 (a |-> some_strip ((list2nmem l) a) def))%pred (@mem_except_range addr_eq_dec valuset (list2nmem l) s n)).
Proof.
(* skipped proof tokens: 162 *)
Admitted.
Fact mem_ex_mem_ex_range_head: forall V AEQ i j (m: @Mem.mem _ AEQ V),
mem_except (AEQ:= AEQ) (mem_except_range m (i + 1) j) i = mem_except_range m i (j + 1).
Proof.
(* skipped proof tokens: 201 *)
Admitted.
Fact mem_ex_mem_ex_range_tail: forall V AEQ i j (m: @Mem.mem _ AEQ V),
mem_except (AEQ:= AEQ) (mem_except_range m i j) (i + j) = mem_except_range m i (j + 1).
Proof.
(* skipped proof tokens: 145 *)
Admitted.
Lemma block_content_match: forall F f vs block_off def, 
(F * block_off|-> vs)%pred (list2nmem(DFData f))-> 
vs = selN (DFData f) block_off def.
Proof.
(* skipped proof tokens: 71 *)
Admitted.
Lemma pick_from_block: forall F f block_off vs i def def', 
i < valubytes -> (F * block_off |-> vs)%pred (list2nmem (DFData f)) ->
selN (valu2list (fst vs)) i def = selN (valu2list (fst (selN (DFData f) block_off def'))) i def.
Proof.
(* skipped proof tokens: 44 *)
Admitted.
Lemma len_f_fy: forall f fy,
ByFData fy =
     firstn (length(ByFData fy))
       (flat_map valuset2bytesets (DFData f))->
 length (ByFData fy) <= length (DFData f) * valubytes.
Proof.
(* skipped proof tokens: 26 *)
Admitted.
Lemma bytefile_unified_byte_len: forall ufy fy, 
bytefile_valid ufy fy -> 
length(ByFData fy) <= length(UByFData ufy).
Proof.
(* skipped proof tokens: 21 *)
Admitted.
Lemma unified_byte_protobyte_len: forall pfy ufy k,
unified_bytefile_valid pfy ufy ->
Forall (fun sublist : list byteset => length sublist = k) (PByFData pfy) ->
length(UByFData ufy) = length (PByFData pfy) * k.
Proof.
(* skipped proof tokens: 26 *)
Admitted.
Lemma byte2unifiedbyte: forall ufy fy F a b,
bytefile_valid ufy fy ->
(F * a|-> b)%pred (list2nmem (ByFData fy)) ->
 (F * (arrayN (ptsto (V:= byteset)) (length(ByFData fy)) 
          (skipn (length(ByFData fy)) (UByFData ufy)))
  * a|->b)%pred (list2nmem (UByFData ufy)).
Proof.
(* skipped proof tokens: 202 *)
Admitted.
Lemma unifiedbyte2protobyte: forall pfy ufy a b F k,
unified_bytefile_valid pfy ufy ->
Forall (fun sublist : list byteset => length sublist = k) (PByFData pfy) ->
k > 0 ->
(F * a|->b)%pred (list2nmem (UByFData ufy)) ->
(diskIs (mem_except (list2nmem (PByFData pfy)) (a/k))  * 
(a/k) |-> get_sublist (UByFData ufy) ((a/k) * k) k)%pred (list2nmem (PByFData pfy)).
Proof.
(* skipped proof tokens: 168 *)
Admitted.
Lemma protobyte2block: forall a b f pfy,
proto_bytefile_valid f pfy ->
(diskIs (mem_except (list2nmem (PByFData pfy)) a) * a|->b)%pred (list2nmem (PByFData pfy)) ->
(diskIs (mem_except (list2nmem (DFData f)) a) * a|->(bytesets2valuset b))%pred (list2nmem (DFData f)).
Proof.
(* skipped proof tokens: 119 *)
Admitted.
Lemma bytefile_bfile_eq: forall f pfy ufy fy,
proto_bytefile_valid f pfy -> 
unified_bytefile_valid pfy ufy -> 
bytefile_valid ufy fy ->
ByFData fy = firstn (length (ByFData fy)) (flat_map valuset2bytesets (DFData f)).
Proof.
(* skipped proof tokens: 53 *)
Admitted.
Fact inlen_bfile: forall f fy i j Fd data, 
rep f fy ->
j < valubytes -> 
length data > 0 ->
(Fd ✶ arrayN (ptsto (V:=byteset)) (i * valubytes + j) data)%pred (list2nmem (ByFData fy)) ->
i < length (DFData f).
Proof.
(* skipped proof tokens: 118 *)
Admitted.
Fact block_exists: forall f pfy ufy fy i j Fd data,
proto_bytefile_valid f pfy ->
unified_bytefile_valid pfy ufy ->
bytefile_valid ufy fy ->
j < valubytes -> length data > 0 ->
(Fd ✶ arrayN (ptsto (V:=byteset)) (i * valubytes + j) data)%pred (list2nmem (ByFData fy)) ->
exists F vs, (F ✶ i |-> vs)%pred (list2nmem (DFData f)).
Proof.
(* skipped proof tokens: 166 *)
Admitted.
Fact proto_len: forall f pfy,
proto_bytefile_valid f pfy ->
Forall (fun sublist : list byteset => length sublist = valubytes) (PByFData pfy).
Proof.
(* skipped proof tokens: 54 *)
Admitted.
Fact proto_skip_len: forall f pfy i,
proto_bytefile_valid f pfy ->
Forall (fun sublist : list byteset => length sublist = valubytes) (skipn i (PByFData pfy)).
Proof.
(* skipped proof tokens: 53 *)
Admitted.
Fact content_match: forall Fd f pfy ufy fy i j data,
proto_bytefile_valid f pfy ->
unified_bytefile_valid pfy ufy ->
bytefile_valid ufy fy ->
(Fd ✶ arrayN (ptsto (V:=byteset)) (i * valubytes + j) data)%pred (list2nmem (ByFData fy)) ->
j < valubytes ->
length data > 0 ->
j + length data <= valubytes ->
ByFAttr fy = DFAttr f ->
# (INODE.ABytes (ByFAttr fy)) = length (ByFData fy) ->
roundup (length (ByFData fy)) valubytes = length (DFData f) * valubytes ->
get_sublist (valu2list (fst (bytesets2valuset (selN (PByFData pfy) i nil)))) j (length data) = map fst data.
Proof.
(* skipped proof tokens: 370 *)
Admitted.
Fact flist_eq_ilist: forall F F' flist flist' ilist m, 
  (@sep_star addr addr_eq_dec valuset 
      F  (listmatch (fun (v : valuset) (a : addr) => a |-> v) flist ilist))%pred m ->
  (@sep_star addr addr_eq_dec valuset 
      F'  (listmatch (fun (v : valuset) (a : addr) => a |-> v) flist' ilist))%pred m ->
  forall i def, i < length flist -> selN flist i def = selN flist' i def.
Proof.
(* skipped proof tokens: 169 *)
Admitted.
Fact unibyte_len: forall f pfy ufy fy i,
proto_bytefile_valid f pfy ->
unified_bytefile_valid pfy ufy ->
bytefile_valid ufy fy ->
i * valubytes < length (ByFData fy) ->
(S i) * valubytes <= length (UByFData ufy).
Proof.
(* original proof tokens: 124 *)

(* No more tactics to try *)
Admitted.

Fact inbound_bytefile_bfile: forall a  b f pfy ufy fy,
  proto_bytefile_valid f pfy ->
  unified_bytefile_valid pfy ufy ->
  bytefile_valid ufy fy ->
  a * valubytes + b < length (ByFData fy) ->
  a < length (DFData f).
Proof.
(* skipped proof tokens: 109 *)
Admitted.
Fact bfile_bytefile_same: forall a  b f pfy ufy fy,
a * valubytes + b < length (ByFData fy) ->
b < valubytes ->
proto_bytefile_valid f pfy ->
unified_bytefile_valid pfy ufy ->
bytefile_valid ufy fy ->
selN (ByFData fy) (a * valubytes + b) byteset0 = selN (valuset2bytesets (selN (DFData f) a valuset0)) b byteset0.
Proof.
(* skipped proof tokens: 71 *)
Admitted.
Fact inbound_protobyte: forall f pfy ufy fy block_off m1 nb data Fd,
proto_bytefile_valid f pfy ->
unified_bytefile_valid pfy ufy ->
bytefile_valid ufy fy ->
(Fd ✶ arrayN (ptsto (V:=byteset)) (block_off * valubytes) data)%pred (list2nmem (ByFData fy)) -> 
nb > 0 ->
length data = nb * valubytes ->
m1 < nb ->
block_off + m1 < length (PByFData pfy).
Proof.
(* skipped proof tokens: 254 *)
Admitted.
Lemma exists_unique_bytefile_length: forall f pfy ufy fy,
proto_bytefile_valid f pfy ->
unified_bytefile_valid pfy ufy ->
bytefile_valid ufy fy ->
length (ByFData fy) mod valubytes = 0 ->
length (ByFData fy) > 0 ->
exists ! x, length (ByFData fy) = x * valubytes.
Proof.
(* skipped proof tokens: 121 *)
Admitted.
Lemma bfile_protobyte_len_eq: forall f pfy,
  proto_bytefile_valid f pfy ->
  length (PByFData pfy) = length (DFData f).
Proof.
(* skipped proof tokens: 15 *)
Admitted.
Lemma list2nmem_arrayN_middle: forall A  (l2 l1 l3: list A) a b (F:pred),
a = length l1 -> b = length l2 ->
F (mem_except_range (list2nmem (l1 ++ l2 ++ l3)) a b ) -> (F * arrayN (ptsto (V:= A)) a l2)%pred (list2nmem (l1 ++ l2 ++ l3)).
Proof.
(* skipped proof tokens: 778 *)
Admitted.
Lemma arrayN_frame_mem_ex_range: forall A (l: list A) (F:pred) a m,
(F * arrayN (ptsto (V:= A)) a l)%pred m -> F (mem_except_range m a (length l) ).
Proof.
(* skipped proof tokens: 321 *)
Admitted.
Lemma bfile_ge_block_off: forall f fy block_off old_data Fd m1 l_old_blocks,
m1 < l_old_blocks ->
length old_data = l_old_blocks * valubytes ->
rep f fy ->
(Fd ✶ arrayN (ptsto (V:=byteset)) (block_off * valubytes) old_data)%pred (list2nmem (ByFData fy)) ->
block_off <= length (DFData f).
Proof.
(* skipped proof tokens: 66 *)
Admitted.
Lemma bfile_gt_block_off_m1: forall f fy block_off Fd m1 old_blocks,
length old_blocks > 0 -> 
m1 < length old_blocks ->
rep f fy ->
(Fd ✶ arrayN (ptsto (V:=valuset)) block_off old_blocks)%pred (list2nmem (DFData f)) ->
block_off + m1 < length (DFData f).
Proof.
(* skipped proof tokens: 91 *)
Admitted.
Lemma bfile_ge_block_off_m1: forall f fy block_off Fd m1 old_blocks,
length old_blocks > 0 -> 
m1 < length old_blocks ->
rep f fy ->
(Fd ✶ arrayN (ptsto (V:=valuset)) block_off old_blocks)%pred (list2nmem (DFData f)) ->
block_off + m1 <= length (DFData f).
Proof.
(* skipped proof tokens: 91 *)
Admitted.
Lemma bytefile_ge_block_off_v: forall fy block_off Fd old_data, 
length old_data > 0 ->
(Fd ✶ arrayN (ptsto (V:=byteset)) (block_off * valubytes) old_data)%pred (list2nmem (ByFData fy)) ->
block_off * valubytes <= length (ByFData fy).
Proof.
(* skipped proof tokens: 38 *)
Admitted.
Lemma bytefile_ge_block_off_m1_v: forall fy block_off Fd old_data m1 l_old_blocks, 
m1 < l_old_blocks ->
length old_data = l_old_blocks * valubytes ->
(Fd ✶ arrayN (ptsto (V:=byteset)) (block_off * valubytes) old_data)%pred (list2nmem (ByFData fy)) ->
(block_off + m1 + 1) * valubytes <= length (ByFData fy).
Proof.
(* original proof tokens: 74 *)

(* No more tactics to try *)
Admitted.

Lemma bfile_bytefile_length: forall f pfy ufy fy,
  proto_bytefile_valid f pfy ->
  unified_bytefile_valid pfy ufy ->
  bytefile_valid ufy fy -> 
  length (ByFData fy) <= length (DFData f) * valubytes.
Proof.
(* skipped proof tokens: 59 *)
Admitted.
Lemma list2nmem_upd_updN: forall A a (l l': list A) x,
a < length l' ->
Mem.upd (list2nmem l') a x = list2nmem l -> l = updN l' a x.
Proof.
(* skipped proof tokens: 39 *)
Admitted.
Lemma mem_except_range_unfold: forall A (l: list A) a n,
a < length l ->
mem_except_range (list2nmem l) a (S n) = mem_except_range (mem_except (list2nmem l) a) (S a) n.
Proof.
(* skipped proof tokens: 177 *)
Admitted.
Lemma mem_except_range_out_apply: forall A (l1 l2 l2' l3: list A) a1 a2 le1 le2,
a1 = a2 -> le1 = le2 -> a1 = length l1 -> le1 = length l2 -> length l2 = length l2' ->
mem_except_range (list2nmem (l1++l2++l3)) a1 le1 = (mem_except_range (list2nmem (l1++l2'++l3)) a2 le2).
Proof.
(* skipped proof tokens: 168 *)
Admitted.
Lemma diskIs_arrayN: forall A (l: list A) a b,
a + b <= length l ->
(diskIs (mem_except_range (list2nmem l) a b) * arrayN (ptsto (V:= A)) a (firstn b (skipn a l)))%pred (list2nmem l).
Proof.
(* skipped proof tokens: 183 *)
Admitted.
Lemma diskIs_eq: forall AT AEQ V (m m': @Mem.mem AT AEQ V),
(diskIs m') m ->
m = m'.
Proof.
(* skipped proof tokens: 17 *)
Admitted.
Lemma upd_mem_except_range_comm: forall AEQ V a a0 b v (m: _ AEQ V),
a0 < a \/ a0 > a + b ->
Mem.upd (AEQ:= AEQ) (mem_except_range m a b) a0 v = mem_except_range (Mem.upd m a0 v) a b.
Proof.
(* skipped proof tokens: 65 *)
Admitted.
Lemma diskIs_combine_upd_range: forall V (l: list V) m a b ,
b = length l ->
(diskIs (mem_except_range m a b) * arrayN (ptsto (V:=V)) a l) =p=> diskIs (upd_range m a l).
Proof.
(* skipped proof tokens: 221 *)
Admitted.
Lemma upd_range_list2nmem_comm: forall A (l' l: list A) a,
a + length l' <= length l ->
upd_range (list2nmem l) a l' = list2nmem (firstn a l ++ l' ++ skipn (a + length l') l).
Proof.
(* original proof tokens: 287 *)

(* No more tactics to try *)
Admitted.

Lemma diskIs_arrayN_length: forall A b a (l l' l'': list A) ,
length l' = b ->
a + b <= length l ->
(diskIs (mem_except_range (list2nmem l) a b) * arrayN (ptsto (V:= A)) a l')%pred (list2nmem l'') ->
length l'' = length l.
Proof.
(* skipped proof tokens: 84 *)
Admitted.
Lemma bfile_length_eq: forall a f f' v,
a < length (DFData f) ->
(diskIs (mem_except (list2nmem (DFData f)) a) * a |-> v )%pred (list2nmem (DFData f')) ->
length (DFData f') = length (DFData f).
Proof.
(* skipped proof tokens: 62 *)
Admitted.
Lemma bfile_range_length_eq: forall a b f f' l,
length l = b ->
a + b <= length (DFData f) ->
(diskIs (mem_except_range (list2nmem (DFData f)) a b) * LOG.arrayP a l)%pred (list2nmem (DFData f')) ->
length (DFData f') = length (DFData f).
Proof.
(* original proof tokens: 24 *)

(* No more tactics to try *)
Admitted.

Lemma list2nmem_arrayN_updN_range: forall f f' l a,
a + length l <= length (DFData f) ->
(diskIs (upd_range (list2nmem (DFData f)) a l)) (list2nmem (DFData f')) ->
DFData f' = firstn a (DFData f) ++ l ++ skipn (a + length l) (DFData f).
Proof.
(* skipped proof tokens: 47 *)
Admitted.
Lemma off_div_v_inlen_bfile: forall off f fy old_data length_data Fd,
length_data > 0 ->
length old_data = length_data ->
rep f fy ->
(Fd ✶ arrayN (ptsto (V:=byteset)) off old_data)%pred (list2nmem (ByFData fy)) ->
off / valubytes < length (DFData f).
Proof.
(* skipped proof tokens: 90 *)
Admitted.
Lemma valu2list_sublist_v: forall f i,
Forall (fun sublist : list byte => length sublist = valubytes)
  (valu2list (fst (selN (DFData f) i valuset0))
   :: map valu2list (snd (selN (DFData f) i valuset0))).
Proof.
(* skipped proof tokens: 56 *)
Admitted.
Lemma bytefile_equiv1: forall fy off length_data,
0 < length_data ->
off / valubytes * valubytes + valubytes <= length (ByFData fy) ->
length_data <= valubytes - off mod valubytes ->
length (ByFData fy) - (off / valubytes * valubytes + valubytes) =
length (ByFData fy) - off / valubytes * valubytes -
(off / valubytes * valubytes + off mod valubytes - off / valubytes * valubytes +
 (length_data +
  (off / valubytes * valubytes + valubytes -
   (off / valubytes * valubytes + off mod valubytes + length_data)))).
Proof.
(* skipped proof tokens: 10 *)
Admitted.
Lemma off_plus_mod_inlen_unified: forall ufy fy off,
bytefile_valid ufy fy ->
off < length (ByFData fy) ->
off / valubytes * valubytes + off mod valubytes <= length (UByFData ufy).
Proof.
(* skipped proof tokens: 49 *)
Admitted.
Lemma off_div_mul_inlen_unified: forall ufy fy off,
bytefile_valid ufy fy ->
off < length (ByFData fy) ->
off / valubytes * valubytes <= length (UByFData ufy).
Proof.
(* skipped proof tokens: 53 *)
Admitted.
Lemma list2nmem_arrayN_app': forall A (l l': list A) a (F: pred),
a = length l ->
F (list2nmem l) ->
(F * arrayN (ptsto (V:= A)) a l')%pred (list2nmem (l++l')).
Proof.
(* skipped proof tokens: 21 *)
Admitted.
Lemma S_length_exists: forall A (l: list A) def,
l <> nil -> l = (selN l 0 def)::(skipn 1 l).
Proof.
(* skipped proof tokens: 34 *)
Admitted.
Lemma mapsnd_sndsplit: forall A B (l:list (A * B)),
map snd l = snd (split l).
Proof.
(* skipped proof tokens: 54 *)
Admitted.
Lemma merge_bs_nil_l: forall l,
merge_bs nil l = nil.
Proof.
(* skipped proof tokens: 12 *)
Admitted.
Lemma merge_bs_app: forall l1 l2 l1' l2',
	length l1 = length l1' ->
	merge_bs (l1 ++ l2) (l1'++l2') = merge_bs l1 l1' ++ merge_bs l2 l2'.
Proof.
(* skipped proof tokens: 82 *)
Admitted.
Lemma merge_bs_selN: forall l l' i,
i < length l ->
i < length l' ->
selN (merge_bs l l') i byteset0 = ((selN l i byte0),fst (selN l' i byteset0) :: snd (selN l' i byteset0)).
Proof.
(* skipped proof tokens: 65 *)
Admitted.
Lemma selN_eq: forall A (l l': list A) i def,
l = l' ->
selN l i def = selN l' i def.
Proof.
(* skipped proof tokens: 13 *)
Admitted.
Lemma merge_bs_firstn_skipn: forall a b c l l',
	a + b = c ->
	merge_bs (firstn c l) (firstn c l') = merge_bs (firstn a l) (firstn a l') 
																					++ merge_bs (firstn b (skipn a l)) (firstn b (skipn a l')).
Proof.
(* skipped proof tokens: 150 *)
Admitted.
Lemma arrayN_app': forall VP V (a b: list V) st l pts,
	l = length a ->
	(arrayN (VP:=VP)) pts st (a++b) <=p=> (arrayN (VP:=VP)) pts st a ✶ (arrayN (VP:=VP)) pts (st + l) b.
Proof.
(* skipped proof tokens: 16 *)
Admitted.
Lemma block_off_le_length_proto_bytefile: forall  f pfy ufy fy block_off byte_off data F,
proto_bytefile_valid f pfy ->
unified_bytefile_valid pfy ufy ->
bytefile_valid ufy fy -> 
ByFAttr fy = DFAttr f ->
# (INODE.ABytes (ByFAttr fy)) = length (ByFData fy) ->
roundup (length (ByFData fy)) valubytes = length (DFData f) * valubytes ->
(F * arrayN (ptsto(V:=byteset))(block_off * valubytes + byte_off) data)%pred (list2nmem (ByFData fy)) ->
byte_off < valubytes ->
length data > 0 ->
block_off <= length (PByFData pfy).
Proof.
(* skipped proof tokens: 55 *)
Admitted.
Lemma proto_len_firstn: forall f pfy a,
proto_bytefile_valid f pfy ->
Forall (fun sublist : list byteset => length sublist = valubytes) (firstn a (PByFData pfy)).
Proof.
(* skipped proof tokens: 63 *)
Admitted.
Lemma valu2list_selN_fst: forall block_off a0 f pfy ufy fy,
  proto_bytefile_valid f pfy ->
  unified_bytefile_valid pfy ufy ->
  bytefile_valid ufy fy ->
  block_off < length (DFData f) ->
  a0 < length (ByFData fy) ->
  block_off * valubytes + valubytes > a0 ->
  a0 >= block_off * valubytes ->
  (selN (valu2list (fst (selN (DFData f) block_off valuset0))) (a0 - block_off * valubytes) byte0) = fst (selN (ByFData fy) a0 byteset0).
Proof.
(* skipped proof tokens: 533 *)
Admitted.
Lemma byteset2list_selN_snd: forall block_off a0 f pfy ufy fy,
  proto_bytefile_valid f pfy ->
  unified_bytefile_valid pfy ufy ->
  bytefile_valid ufy fy ->
  block_off < length (DFData f) ->
  a0 < length (ByFData fy) ->
  block_off * valubytes + valubytes > a0 ->
  a0 >= block_off * valubytes ->
  (snd (selN (DFData f) block_off valuset0)) <> nil ->
fst (list2byteset byte0
        (selN (valuset2bytesets_rec (map valu2list (snd (selN (DFData f) block_off valuset0))) valubytes) (a0 - block_off * valubytes) nil))
   :: snd (list2byteset byte0
           (selN (valuset2bytesets_rec (map valu2list (snd (selN (DFData f) block_off valuset0))) valubytes) (a0 - block_off * valubytes) nil)) =
   snd (selN (ByFData fy) a0 byteset0).
Proof.
(* skipped proof tokens: 512 *)
Admitted.
Lemma bfile_bytefile_snd_nil: forall block_off a0 f pfy ufy fy,
  proto_bytefile_valid f pfy ->
  unified_bytefile_valid pfy ufy ->
  bytefile_valid ufy fy ->
  block_off < length (DFData f) ->
  a0 < length (ByFData fy) ->
  block_off * valubytes + valubytes > a0 ->
  a0 >= block_off * valubytes ->
  snd (selN (DFData f) block_off valuset0) = nil ->
  snd (selN (ByFData fy) a0 byteset0) = nil.
Proof.
(* skipped proof tokens: 330 *)
Admitted.
Lemma unified_bytefile_bytefile_selN_eq: forall a0 ufy fy,
  bytefile_valid ufy fy ->
  a0 < length (ByFData fy) ->
  selN (UByFData ufy) a0 byteset0 = selN (ByFData fy) a0 byteset0.
Proof.
(* skipped proof tokens: 26 *)
Admitted.
Lemma merge_bs_skipn_comm: forall l l1 a,
skipn a (merge_bs l l1) = merge_bs (skipn a l) (skipn a l1).
Proof.
(* skipped proof tokens: 59 *)
Admitted.
Lemma sep_star_mem_exists: forall {AT AEQ V} (m: @Mem.mem AT AEQ V),
    exists m1 m2 : Mem.mem,
    m = mem_union m1 m2 /\ mem_disjoint m1 m2.
Proof.
(* skipped proof tokens: 69 *)
Admitted.
Lemma bsplit_list_O_byte0: forall b l sz,
bsplit_list (natToWord (sz * 8) 0) = b::l ->
b = byte0.
Proof.
(* skipped proof tokens: 73 *)
Admitted.
Lemma unified_bytefile_bytefile_same: forall ufy fy,
bytefile_valid ufy fy ->
length (ByFData fy) = length (UByFData ufy) ->
ByFData fy = UByFData ufy.
Proof.
(* skipped proof tokens: 22 *)
Admitted.
Lemma list2nmem_app': forall V (F: pred) a (l: list V) v,
a = length l ->
F (list2nmem l) ->
(F * a |-> v)%pred (list2nmem (l ++ (v::nil))).
Proof.
(* skipped proof tokens: 19 *)
Admitted.
Lemma unified_bytefile_bytefile_firstn: forall a ufy fy,
a <= length (ByFData fy) ->
bytefile_valid ufy fy ->
firstn a (ByFData fy) = firstn a (UByFData ufy).
Proof.
(* skipped proof tokens: 39 *)
Admitted.
Lemma unified_bytefile_minus: forall f pfy ufy fy a,
		proto_bytefile_valid f pfy ->
		unified_bytefile_valid pfy ufy ->
		bytefile_valid ufy fy ->
		length (ByFData fy) > (length (DFData f) - 1) * valubytes ->
		 a >= valubytes ->
		 length (ByFData fy) >= length (UByFData ufy) - a.
Proof.
(* skipped proof tokens: 193 *)
Admitted.
Lemma bfile_bytefile_length_eq: forall f pfy ufy fy a,
	proto_bytefile_valid f pfy ->
	unified_bytefile_valid pfy ufy ->
	bytefile_valid ufy fy ->
	length (ByFData fy) = a - a mod valubytes ->
	length (ByFData fy) > (length (DFData f) - 1) * valubytes ->
	length (ByFData fy) = length (DFData f) * valubytes.
Proof.
(* skipped proof tokens: 115 *)
Admitted.
Lemma proto_bytefile_unified_bytefile_selN: forall a f pfy ufy,
proto_bytefile_valid f pfy ->
unified_bytefile_valid pfy ufy ->
a < length (PByFData pfy) ->
selN (PByFData pfy) a nil = get_sublist (UByFData ufy) (a * valubytes) valubytes.
Proof.
(* skipped proof tokens: 91 *)
Admitted.
Lemma unified_bytefile_bytefile_length_eq: forall f pfy ufy fy,
	proto_bytefile_valid f pfy ->
	unified_bytefile_valid pfy ufy ->
	bytefile_valid ufy fy ->
	length (ByFData fy) > (length (DFData f) - 1) * valubytes ->
	length (ByFData fy) mod valubytes = 0 ->
	length (ByFData fy) =length (UByFData ufy).
Proof.
(* skipped proof tokens: 87 *)
Admitted.
Lemma bytefile_bfile_minus_lt: forall f fy fy' n, 
	(length (ByFData fy) > 0 -> length (ByFData fy) > (length (DFData f) - 1) * valubytes) ->
	# (INODE.ABytes (ByFAttr fy)) = length (ByFData fy) ->
	ByFAttr fy =
      ($ (length (ByFData fy') + (valubytes - length (ByFData fy') mod valubytes)), snd (ByFAttr fy')) ->
  goodSize addrlen (length (ByFData fy') + n) ->
  0 < (n - (valubytes - length (ByFData fy') mod valubytes)) mod valubytes ->
  length (ByFData fy) > (length (DFData f) - 1) * valubytes.
Proof.
(* skipped proof tokens: 128 *)
Admitted.
Lemma bytefile_mod_0: forall fy fy' n, 
	# (INODE.ABytes (ByFAttr fy)) = length (ByFData fy) ->
	ByFAttr fy =
      ($ (length (ByFData fy') + (valubytes - length (ByFData fy') mod valubytes)), snd (ByFAttr fy')) ->
  goodSize addrlen (length (ByFData fy') + n) ->
  0 < (n - (valubytes - length (ByFData fy') mod valubytes)) mod valubytes ->
  length (ByFData fy) mod valubytes = 0.
Proof.
(* skipped proof tokens: 190 *)
Admitted.
Lemma Forall_map_v_app: forall n fy,
	Forall (fun sublist : list byteset => length sublist = valubytes)
  (map valuset2bytesets
     (synced_list (valu0_pad ((n - (valubytes - length (ByFData fy) mod valubytes)) / valubytes))) ++
   valuset2bytesets (valu0, nil) :: nil).
Proof.
(* skipped proof tokens: 66 *)
Admitted.
Lemma mod_lt_0_le: forall a b c,
  c <> 0 ->
  (a - b) mod c > 0 ->
  a >= b.
Proof.
(* skipped proof tokens: 25 *)
Admitted.
Lemma list_zero_pad_nil_skipn: forall a n,
  skipn (a) (list_zero_pad nil n) = list_zero_pad nil (n - a).
Proof.
(* skipped proof tokens: 50 *)
Admitted.
Lemma valu0_pad_length: forall a,
	length (valu0_pad a) = a.
Proof.
(* skipped proof tokens: 29 *)
Admitted.
Lemma pm_2_3_cancel: forall a b,
	a + b - b = a.
Proof.
(* skipped proof tokens: 10 *)
Admitted.
Lemma list2nmem_arrayN_app_general: forall A (F: pred) a (l l' l'': list A),
	F (list2nmem l) ->
	a = length l ->
	l' = l'' ->
	(F * arrayN (ptsto (V:= A)) a l')%pred (list2nmem (l ++ l'')).
Proof.
(* skipped proof tokens: 24 *)
Admitted.
Lemma list_zero_pad_nil_app: forall a b,
list_zero_pad nil a ++ list_zero_pad nil b = list_zero_pad nil (a + b).
Proof.
(* skipped proof tokens: 46 *)
Admitted.
Lemma Forall_map_vs2bs: forall l,
Forall (fun sublist : list byteset => length sublist = valubytes)
  (map valuset2bytesets l).
Proof.
(* skipped proof tokens: 39 *)
Admitted.
Lemma concat_hom_length_map_vs2bs: forall l,
length (concat (map valuset2bytesets l)) = (length l) * valubytes.
Proof.
(* skipped proof tokens: 39 *)
Admitted.
Lemma skipn_exact: forall A (l: list A),
skipn (length l) l = nil.
Proof.
(* skipped proof tokens: 23 *)
Admitted.
Lemma bytefile_length_sub: forall fy a b,
# (INODE.ABytes (ByFAttr fy)) = length (ByFData fy) ->
ByFAttr fy = ($ a, b) ->
goodSize addrlen a ->
length (ByFData fy) = a.
Proof.
(* skipped proof tokens: 32 *)
Admitted.
Lemma bsplit_list_0_list_zero_pad_eq: forall a,
  	bsplit_list (natToWord (a * 8) 0) = list_zero_pad nil a.
Proof.
(* original proof tokens: 94 *)

(* No more tactics to try *)
Admitted.

Lemma valu2list_valu0:
  valu2list valu0 = list_zero_pad nil valubytes.
Proof.
(* skipped proof tokens: 40 *)
Admitted.
Lemma valuset2bytesets_synced_list_valu0_pad_merge_bs_zero_pad_nil:
  valuset2bytesets (valu0, nil) = merge_bs (list_zero_pad nil valubytes) nil.
Proof.
(* skipped proof tokens: 65 *)
Admitted.
Lemma synced_list_map_nil_eq: forall (l:list valu),
synced_list l = map (fun x => (x, nil)) l.
Proof.
(* skipped proof tokens: 37 *)
Admitted.
Lemma merge_bs_map_x_nil_eq: forall l,
map (fun x : word 8 => (x, nil)) l = merge_bs l nil.
Proof.
(* skipped proof tokens: 25 *)
Admitted.
Lemma valuset2bytesets_valu0: 
	valuset2bytesets (valu0, nil) = merge_bs (list_zero_pad nil valubytes) nil.
Proof.
(* skipped proof tokens: 60 *)
Admitted.
Lemma merge_bs_nil_app: forall l1 l2,
merge_bs l1 nil ++ merge_bs l2 nil = merge_bs (l1++l2) nil.
Proof.
(* skipped proof tokens: 30 *)
Admitted.
Lemma concat_map_valuset2bytesets_valu0: forall a,
concat (map (fun x : valu => valuset2bytesets (x, nil))
     (valu0_pad a)) =  merge_bs (list_zero_pad nil (a*valubytes)) nil.
Proof.
(* skipped proof tokens: 52 *)
Admitted.
Lemma ge_1_gt_0: forall a, a > 0 -> a >= 1.
Proof.
(* skipped proof tokens: 10 *)
Admitted.
Lemma mod_ge_0: forall a b c,
a mod b > 0 ->
b <> 0 ->
a + c > 0.
Proof.
(* skipped proof tokens: 19 *)
Admitted.
Lemma mod_plus_minus_0: forall c b a,
b <> 0 ->
c > 0 ->
(a + ((c * b) - a mod b)) mod b = 0.
Proof.
(* skipped proof tokens: 79 *)
Admitted.
Lemma div_ge_0: forall a b,
b <> 0 ->
a / b > 0 ->
a > 0.
Proof.
(* skipped proof tokens: 28 *)
Admitted.
Lemma div_minus_ge_0: forall a b c,
b <> 0 ->
(a - c) / b > 0 ->
a > c.
Proof.
(* skipped proof tokens: 23 *)
Admitted.
Lemma gt_0_ge_1: forall a, a > 0 <-> a >= 1.
Proof.
(* skipped proof tokens: 12 *)
Admitted.
Lemma div_mod_0: forall a b,
b<>0 -> a/b = 0 -> a mod b = 0 -> a = 0.
Proof.
(* original proof tokens: 45 *)

(* No more tactics to try *)
Admitted.

Lemma mod_plus_minus_1_0: forall a b,
b<>0 ->
(a + (b - a mod b)) mod b = 0.
Proof.
(* skipped proof tokens: 41 *)
Admitted.
Lemma goodSize_le: forall a b c d,
goodSize a (b + c) ->
(c < d -> False) ->
 goodSize a (b + d).
Proof.
(* skipped proof tokens: 42 *)
Admitted.
Lemma unified_bytefile_bytefile_same': forall f pfy ufy fy,
proto_bytefile_valid f pfy ->
unified_bytefile_valid pfy ufy ->
bytefile_valid ufy fy ->
length (ByFData fy) = length (DFData f) * valubytes ->
ByFData fy = UByFData ufy.
Proof.
(* skipped proof tokens: 64 *)
Admitted.
Lemma f_pfy_selN_eq: forall f pfy i,
proto_bytefile_valid f pfy ->
i < length (DFData f) ->
valu2list (fst (selN (DFData f) i valuset0)) = map fst (selN (PByFData pfy) i nil).
Proof.
(* skipped proof tokens: 42 *)
Admitted.
Lemma v2l_fst_bs2vs_map_fst_eq: forall bsl,
bsl <> nil ->
length bsl = valubytes ->
map fst bsl = valu2list (fst (bytesets2valuset bsl)).
Proof.
(* skipped proof tokens: 94 *)
Admitted.
Lemma rep_sync_invariant: forall f fy F,
sync_invariant F -> sync_invariant ([[rep f fy ]] * F)%pred.
Proof.
(* skipped proof tokens: 22 *)
Admitted.
