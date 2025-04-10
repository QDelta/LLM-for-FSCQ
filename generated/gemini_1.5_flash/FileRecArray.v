Require Import Eqdep_dec Arith Lia List ListUtils Rounding Psatz.
Require Import Word WordAuto AsyncDisk Pred PredCrash GenSepN Array SepAuto.
Require Import Rec Prog BasicProg Hoare RecArrayUtils Log.
Require Import ProofIrrelevance.
Require Import Inode BFile MemMatch.
Require Import Errno.
Require Import ProgMonad.
Import ListNotations EqNotations.
Set Implicit Arguments.
Module Type FileRASig.
Parameter itemtype : Rec.type.
Parameter items_per_val : nat.
Parameter blocksz_ok : valulen = Rec.len (Rec.ArrayF itemtype items_per_val).
End FileRASig.
Module FileRecArray (FRA : FileRASig).
Module RA <: RASig.
Definition xparams := BFILE.bfile.
Definition RAStart := fun (_ : xparams) => 0.
Definition RALen := fun f => length (BFILE.BFData f).
Definition xparams_ok := fun (_ : xparams) => True.
Definition itemtype := FRA.itemtype.
Definition items_per_val := FRA.items_per_val.
Definition blocksz_ok := FRA.blocksz_ok.
Definition RAData f := (BFILE.BFData f).
Definition RAAttr f := (BFILE.BFAttr f).
End RA.
Module Defs := RADefs RA.
Import RA Defs.
Definition items_valid f (items : itemlist) :=
    length items = (RALen f) * items_per_val /\
    Forall Rec.well_formed items.
Definition rep f (items : itemlist) :=
    ( exists vl, [[ vl = ipack items ]] *
      [[ items_valid f items ]] *
      arrayN (@ptsto _ addr_eq_dec _) 0 (synced_list vl))%pred.
Definition get lxp ixp inum ix ms :=
    let '(bn, off) := (ix / items_per_val, ix mod items_per_val) in
    let^ (ms, v) <- BFILE.read_array lxp ixp inum 0 bn ms;
    Ret ^(ms, selN_val2block v off).
Definition put lxp ixp inum ix item ms :=
    let '(bn, off) := (ix / items_per_val, ix mod items_per_val) in
    let^ (ms, v) <- BFILE.read_array lxp ixp inum 0 bn ms;
    let v' := block2val_updN_val2block v off item in
    ms <- BFILE.write_array lxp ixp inum 0 bn v' ms;
    Ret ms.
Definition extend lxp bxp ixp inum item ms :=
    let v := block2val (updN block0 0 item) in
    let^ (ms, r) <- BFILE.grow lxp bxp ixp inum v ms;
    Ret ^(ms, r).
Definition readall lxp ixp inum ms :=
    let^ (ms, nr) <- BFILE.getlen lxp ixp inum ms;
    let^ (ms, r) <- BFILE.read_range lxp ixp inum 0 nr iunpack nil ms;
    Ret ^(ms, r).
Definition init lxp bxp ixp inum ms :=
    let^ (ms, nr) <- BFILE.getlen lxp ixp inum ms;
    ms <- BFILE.shrink lxp bxp ixp inum nr ms;
    Ret ms.
Notation MSLL := BFILE.MSLL.
Notation MSAlloc := BFILE.MSAlloc.
Notation MSAllocC := BFILE.MSAllocC.
Notation MSICache := BFILE.MSICache.
Notation MSCache := BFILE.MSCache.
Notation MSIAllocC := BFILE.MSIAllocC.
Notation MSDBlocks := BFILE.MSDBlocks.
Definition ifind lxp ixp inum (cond : item -> addr -> bool) ms0 :=
    let^ (ms, nr) <- BFILE.getlen lxp ixp inum ms0;
    let^ (ms, ret) <- ForN i < nr
    Hashmap hm
    Ghost [ bxp F Fm Fi crash m0 sm m flist f items ilist frees ]
    Loopvar [ ms ret ]
    Invariant
      LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLL ms) sm hm *
      [[[ m ::: (Fm * BFILE.rep bxp sm ixp flist ilist frees (MSAllocC ms) (MSCache ms) (MSICache ms) (MSDBlocks ms)) ]]] *
      [[[ flist ::: (Fi * inum |-> f) ]]] *
      [[[ RAData f ::: rep f items ]]] *
      [[ ret = None ->
         forall ix, ix < i * items_per_val ->
               cond (selN items ix item0) ix = false ]] *
      [[ forall st, ret = Some st ->
              cond (snd st) (fst st) = true
              /\ (fst st) < length items
              /\ snd st = selN items (fst st) item0 ]] *
      [[ MSAlloc ms = MSAlloc ms0 ]] *
      [[ MSCache ms = MSCache ms0 ]] *
      [[ MSIAllocC ms = MSIAllocC ms0 ]] *
      [[ MSAllocC ms = MSAllocC ms0 ]] *
      [[ MSDBlocks ms = MSDBlocks ms0 ]]
    OnCrash  crash
    Begin
        If (is_some ret) {
          Ret ^(ms, ret)
        } else {
            let^ (ms, v) <- BFILE.read_array lxp ixp inum 0 i ms;
            let r := ifind_block cond (val2block v) (i * items_per_val) in
            match r with
            | None => Ret ^(ms, None)
            | Some ifs => Ret ^(ms, Some ifs)
            end
        }
    Rof ^(ms, None);
    Ret ^(ms, ret).
Local Hint Resolve items_per_val_not_0 items_per_val_gt_0 items_per_val_gt_0'.
Lemma items_valid_updN : forall xp items a v,
    items_valid xp items ->
    Rec.well_formed v ->
    items_valid xp (updN items a v).
Proof.
(* original proof tokens: 36 *)

(* No more tactics to try *)
Admitted.

Lemma ifind_length_ok : forall xp i items,
    i < RALen xp ->
    items_valid xp items ->
    i < length (synced_list (ipack items)).
Proof.
(* original proof tokens: 27 *)

(* No more tactics to try *)
Admitted.

Lemma items_valid_length_eq : forall xp a b,
    items_valid xp a ->
    items_valid xp b ->
    length (ipack a) = length (ipack b).
Proof.
(* original proof tokens: 25 *)
(* generated proof tokens: 48 *)
intros.
eapply ipack_length_eq; eauto.
destruct H as [Hlen Hwf].
destruct H0 as [Hlen0 Hwf0].
apply Hlen.
apply H0.
Qed.

Hint Extern 0 (okToUnify (BFILE.rep _ _ _ _ _ _ _ _ _ _) (BFILE.rep _ _ _ _ _ _ _ _ _ _)) => setoid_rewrite <- surjective_pairing : okToUnify.
Theorem get_ok : forall lxp ixp bxp inum ix ms,
    {< F Fm Fi m0 sm m flist f items ilist frees,
    PRE:hm
          LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLL ms) sm hm *
          [[ ix < length items ]] *
          [[[ m ::: (Fm * BFILE.rep bxp sm ixp flist ilist frees (MSAllocC ms) (MSCache ms) (MSICache ms) (MSDBlocks ms)) ]]] *
          [[[ flist ::: (Fi * inum |-> f) ]]] *
          [[[ RAData f ::: rep f items ]]]
    POST:hm' RET:^(ms', r)
          LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLL ms') sm hm' *
          [[ r = selN items ix item0 ]] *
          [[[ m ::: (Fm * BFILE.rep bxp sm ixp flist ilist frees (MSAllocC ms') (MSCache ms') (MSICache ms') (MSDBlocks ms')) ]]] *
          [[ MSAlloc ms' = MSAlloc ms ]] *
          [[ MSCache ms' = MSCache ms ]] *
          [[ MSIAllocC ms' = MSIAllocC ms ]] *
          [[ MSDBlocks ms' = MSDBlocks ms ]] *
          [[ MSAllocC ms' = MSAllocC ms]]
    CRASH:hm'  exists ms',
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLL ms') sm hm'
    >} get lxp ixp inum ix ms.
Proof.
(* original proof tokens: 122 *)

(* No more tactics to try *)
Admitted.

Theorem put_ok : forall lxp ixp bxp inum ix e ms,
    {< F Fm Fi m0 sm m flist f items ilist frees,
    PRE:hm
          LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLL ms) sm hm *
          [[ ix < length items /\ Rec.well_formed e ]] *
          [[[ m ::: (Fm * BFILE.rep bxp sm ixp flist ilist frees (MSAllocC ms) (MSCache ms) (MSICache ms) (MSDBlocks ms)) ]]] *
          [[[ flist ::: (Fi * inum |-> f) ]]] *
          [[[ RAData f ::: rep f items ]]]
    POST:hm' RET:ms' exists m' flist' f',
          LOG.rep lxp F (LOG.ActiveTxn m0 m') (MSLL ms') sm hm' *
          [[[ m' ::: (Fm * BFILE.rep bxp sm ixp flist' ilist frees (MSAllocC ms') (MSCache ms') (MSICache ms') (MSDBlocks ms')) ]]] *
          [[[ flist' ::: (Fi * inum |-> f') ]]] *
          [[[ RAData f' ::: rep f' (updN items ix e) ]]] *
          [[ MSAlloc ms' = MSAlloc ms ]] *
          [[ MSCache ms' = MSCache ms ]] *
          [[ MSIAllocC ms' = MSIAllocC ms ]] *
          [[ MSAllocC ms' = MSAllocC ms ]] *
          [[ MSDBlocks ms' = MSDBlocks ms ]]
    CRASH:hm' LOG.intact lxp F m0 sm hm'
    >} put lxp ixp inum ix e ms.
Proof.
(* original proof tokens: 194 *)

(* No more tactics to try *)
Admitted.

Lemma extend_ok_helper : forall f e items,
    items_valid f items ->
    length (BFILE.BFData f) |-> (block2val (updN block0 0 e), []) *
    arrayN (@ptsto _ addr_eq_dec _) 0 (synced_list (ipack items)) =p=>
    arrayN (@ptsto _ addr_eq_dec _) 0 (synced_list (ipack (items ++ (updN block0 0 e)))).
Proof.
(* original proof tokens: 228 *)

(* No more tactics to try *)
Admitted.

Lemma extend_item_valid : forall f e items,
    Rec.well_formed e ->
    items_valid f items ->
    items_valid {| BFILE.BFData := BFILE.BFData f ++ [(block2val (updN block0 0 e), [])];
                   BFILE.BFAttr := BFILE.BFAttr f;
                   BFILE.BFCache := BFILE.BFCache f |}  (items ++ (updN block0 0 e)).
Proof.
(* original proof tokens: 99 *)

(* No more tactics to try *)
Admitted.

Theorem extend_ok : forall lxp ixp bxp inum e ms,
    {< F Fm Fi m0 sm m flist f items ilist frees,
    PRE:hm
          LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLL ms) sm hm *
          [[ Rec.well_formed e ]] *
          [[[ m ::: (Fm * BFILE.rep bxp sm ixp flist ilist frees (MSAllocC ms) (MSCache ms) (MSICache ms) (MSDBlocks ms)) ]]] *
          [[[ flist ::: (Fi * inum |-> f) ]]] *
          [[[ RAData f ::: rep f items ]]]
    POST:hm' RET: ^(ms', r) exists m',
         [[ MSAlloc ms' = MSAlloc ms ]] *
         [[ MSCache ms' = MSCache ms ]] *
         [[ MSIAllocC ms' = MSIAllocC ms ]] *
         ([[ isError r ]] * 
          LOG.rep lxp F (LOG.ActiveTxn m0 m') (MSLL ms') sm hm' \/
          [[ r = OK tt  ]] *
          exists flist' f' ilist' frees',
          LOG.rep lxp F (LOG.ActiveTxn m0 m') (MSLL ms') sm hm' *
          [[[ m' ::: (Fm * BFILE.rep bxp sm ixp flist' ilist' frees' (MSAllocC ms') (MSCache ms') (MSICache ms') (MSDBlocks ms')) ]]] *
          [[[ flist' ::: (Fi * inum |-> f') ]]] *
          [[[ RAData f' ::: rep f' (items ++ (updN block0 0 e)) ]]] *
          [[ BFILE.ilist_safe ilist  (BFILE.pick_balloc frees  (MSAlloc ms'))
                              ilist' (BFILE.pick_balloc frees' (MSAlloc ms')) ]] *
          [[ BFILE.treeseq_ilist_safe inum ilist ilist' ]] )
    CRASH:hm' LOG.intact lxp F m0 sm hm'
    >} extend lxp bxp ixp inum e ms.
Proof.
(* original proof tokens: 89 *)

(* No more tactics to try *)
Admitted.

Theorem readall_ok : forall lxp ixp bxp inum ms,
    {< F Fm Fi m0 sm m flist f items ilist frees,
    PRE:hm
          LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLL ms) sm hm *
          [[[ m ::: (Fm * BFILE.rep bxp sm ixp flist ilist frees (MSAllocC ms) (MSCache ms) (MSICache ms) (MSDBlocks ms)) ]]] *
          [[[ flist ::: (Fi * inum |-> f) ]]] *
          [[[ RAData f ::: rep f items ]]]
    POST:hm' RET:^(ms', r)
          LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLL ms') sm hm' *
          [[ r = items ]] *
          [[[ m ::: (Fm * BFILE.rep bxp sm ixp flist ilist frees (MSAllocC ms') (MSCache ms') (MSICache ms') (MSDBlocks ms')) ]]] *
          [[ MSAlloc ms' = MSAlloc ms ]] *
          [[ MSCache ms' = MSCache ms ]] *
          [[ MSIAllocC ms' = MSIAllocC ms ]] *
          [[ MSAllocC ms' = MSAllocC ms ]] *
          [[ MSDBlocks ms' = MSDBlocks ms ]]
    CRASH:hm'  exists ms',
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLL ms') sm hm'
    >} readall lxp ixp inum ms.
Proof.
(* original proof tokens: 125 *)

(* No more tactics to try *)
Admitted.

Theorem init_ok : forall lxp bxp ixp inum ms,
    {< F Fm Fi m0 sm m flist f ilist frees,
    PRE:hm
          LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLL ms) sm hm *
          [[[ m ::: (Fm * BFILE.rep bxp sm ixp flist ilist frees (MSAllocC ms) (MSCache ms) (MSICache ms) (MSDBlocks ms)) ]]] *
          [[[ flist ::: (Fi * inum |-> f) ]]]
    POST:hm' RET:ms' exists m' flist' f' ilist' frees',
          LOG.rep lxp F (LOG.ActiveTxn m0 m') (MSLL ms') sm hm' *
          [[[ m' ::: (Fm * BFILE.rep bxp sm ixp flist' ilist' frees' (MSAllocC ms') (MSCache ms') (MSICache ms') (MSDBlocks ms')) ]]] *
          [[[ flist' ::: (Fi * inum |-> f') ]]] *
          [[[ RAData f' ::: emp ]]] *
          [[ MSAlloc ms' = MSAlloc ms ]] *
          [[ MSCache ms' = MSCache ms ]] *
          [[ MSIAllocC ms' = MSIAllocC ms ]] *
          [[ BFILE.ilist_safe ilist  (BFILE.pick_balloc frees  (MSAlloc ms'))
                              ilist' (BFILE.pick_balloc frees' (MSAlloc ms')) ]]
    CRASH:hm' LOG.intact lxp F m0 sm hm'
    >} init lxp bxp ixp inum ms.
Proof.
(* original proof tokens: 71 *)

(* No more tactics to try *)
Admitted.

Theorem ifind_ok : forall lxp bxp ixp inum cond ms,
    {< F Fm Fi m0 sm m flist f items ilist frees,
    PRE:hm
          LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLL ms) sm hm *
          [[[ m ::: (Fm * BFILE.rep bxp sm ixp flist ilist frees (MSAllocC ms) (MSCache ms) (MSICache ms) (MSDBlocks ms)) ]]] *
          [[[ flist ::: (Fi * inum |-> f) ]]] *
          [[[ RAData f ::: rep f items ]]]
    POST:hm' RET:^(ms', r)
          LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLL ms') sm hm' *
          [[[ m ::: (Fm * BFILE.rep bxp sm ixp flist ilist frees (MSAllocC ms') (MSCache ms') (MSICache ms') (MSDBlocks ms')) ]]] *
          [[ MSAlloc ms' = MSAlloc ms ]] *
          [[ MSCache ms' = MSCache ms ]] *
          [[ MSAllocC ms' = MSAllocC ms ]] *
          [[ MSIAllocC ms' = MSIAllocC ms ]] *
          [[ MSDBlocks ms' = MSDBlocks ms ]] *
        ( [[ r = None /\ forall i, i < length items ->
                         cond (selN items i item0) i = false  ]]
          \/ exists st,
          [[ r = Some st /\ cond (snd st) (fst st) = true
                         /\ (fst st) < length items
                         /\ snd st = selN items (fst st) item0 ]])
    CRASH:hm'  exists ms',
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLL ms') sm hm'
    >} ifind lxp ixp inum cond ms.
Proof.
(* original proof tokens: 254 *)

(* No more tactics to try *)
Admitted.

Hint Extern 1 ({{_}} Bind (get _ _ _ _ _) _) => apply get_ok : prog.
Hint Extern 1 ({{_}} Bind (put _ _ _ _ _ _) _) => apply put_ok : prog.
Hint Extern 1 ({{_}} Bind (extend _ _ _ _ _ _) _) => apply extend_ok : prog.
Hint Extern 1 ({{_}} Bind (readall _ _ _ _) _) => apply readall_ok : prog.
Hint Extern 1 ({{_}} Bind (init _ _ _ _ _) _) => apply init_ok : prog.
Hint Extern 1 ({{_}} Bind (ifind _ _ _ _ _) _) => apply ifind_ok : prog.
Definition get_array lxp ixp inum ix ms :=
    r <- get lxp ixp inum ix ms;
    Ret r.
Definition put_array lxp ixp inum ix item ms :=
    r <- put lxp ixp inum ix item ms;
    Ret r.
Definition extend_array lxp bxp ixp inum item ms :=
    r <- extend lxp bxp ixp inum item ms;
    Ret r.
Definition ifind_array lxp ixp inum cond ms :=
    r <- ifind lxp ixp inum cond ms;
    Ret r.
Theorem get_array_ok : forall lxp ixp bxp inum ix ms,
    {< F Fm Fi Fe m0 sm m flist f items e ilist frees,
    PRE:hm
          LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLL ms) sm hm *
          [[[ m ::: (Fm * BFILE.rep bxp sm ixp flist ilist frees (MSAllocC ms) (MSCache ms) (MSICache ms) (MSDBlocks ms)) ]]] *
          [[[ flist ::: (Fi * inum |-> f) ]]] *
          [[[ RAData f ::: rep f items ]]] *
          [[[ items ::: Fe * ix |-> e ]]]
    POST:hm' RET:^(ms', r)
          LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLL ms') sm hm' *
          [[ r = e ]] *
          [[[ m ::: (Fm * BFILE.rep bxp sm ixp flist ilist frees (MSAllocC ms') (MSCache ms') (MSICache ms') (MSDBlocks ms')) ]]] *
          [[ MSAlloc ms' = MSAlloc ms ]] *
          [[ MSCache ms' = MSCache ms ]] *
          [[ MSIAllocC ms' = MSIAllocC ms ]] *
          [[ MSAllocC ms' = MSAllocC ms]]
    CRASH:hm'  exists ms',
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLL ms') sm hm'
    >} get_array lxp ixp inum ix ms.
Proof.
(* original proof tokens: 49 *)

(* No more tactics to try *)
Admitted.

Theorem put_array_ok : forall lxp ixp bxp inum ix e ms,
    {< F Fm Fi Fe m0 sm m flist f items e0 ilist frees,
    PRE:hm
          LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLL ms) sm hm *
          [[ Rec.well_formed e ]] *
          [[[ m ::: (Fm * BFILE.rep bxp sm ixp flist ilist frees (MSAllocC ms) (MSCache ms) (MSICache ms) (MSDBlocks ms)) ]]] *
          [[[ flist ::: (Fi * inum |-> f) ]]] *
          [[[ RAData f ::: rep f items ]]] *
          [[[ items ::: Fe * ix |-> e0 ]]]
    POST:hm' RET:ms' exists m' flist' f' items',
          LOG.rep lxp F (LOG.ActiveTxn m0 m') (MSLL ms') sm hm' *
          [[[ m' ::: (Fm * BFILE.rep bxp sm ixp flist' ilist frees (MSAllocC ms') (MSCache ms') (MSICache ms') (MSDBlocks ms')) ]]] *
          [[[ flist' ::: (Fi * inum |-> f') ]]] *
          [[[ RAData f' ::: rep f' items' ]]] *
          [[[ items' ::: Fe * ix |-> e ]]] *
          [[ items' = updN items ix e ]] *
          [[ MSAlloc ms' = MSAlloc ms ]] *
          [[ MSCache ms' = MSCache ms ]] *
          [[ MSIAllocC ms' = MSIAllocC ms ]] *
          [[ MSAllocC ms' = MSAllocC ms ]] *
          [[ MSDBlocks ms' = MSDBlocks ms ]]
    CRASH:hm' LOG.intact lxp F m0 sm hm'
    >} put_array lxp ixp inum ix e ms.
Proof.
(* original proof tokens: 44 *)

(* No more tactics to try *)
Admitted.

Theorem extend_array_ok : forall lxp bxp ixp inum e ms,
    {< F Fm Fi Fe m0 sm m flist f items ilist frees,
    PRE:hm
          LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLL ms) sm hm *
          [[ Rec.well_formed e ]] *
          [[[ m ::: (Fm * BFILE.rep bxp sm ixp flist ilist frees (MSAllocC ms) (MSCache ms) (MSICache ms) (MSDBlocks ms)) ]]] *
          [[[ flist ::: (Fi * inum |-> f) ]]] *
          [[[ RAData f ::: rep f items ]]] *
          [[[ items ::: Fe ]]]
    POST:hm' RET:^(ms', r) exists m',
         [[ MSAlloc ms' = MSAlloc ms ]] *
         [[ MSCache ms' = MSCache ms ]] *
         [[ MSIAllocC ms' = MSIAllocC ms ]] *
         ([[ isError r ]] * 
          LOG.rep lxp F (LOG.ActiveTxn m0 m') (MSLL ms') sm hm' \/
          [[ r = OK tt ]] *
          exists flist' f' items' ilist' frees',
          LOG.rep lxp F (LOG.ActiveTxn m0 m') (MSLL ms') sm hm' *
          [[[ m' ::: (Fm * BFILE.rep bxp sm ixp flist' ilist' frees' (MSAllocC ms') (MSCache ms') (MSICache ms') (MSDBlocks ms')) ]]] *
          [[[ flist' ::: (Fi * inum |-> f') ]]] *
          [[[ RAData f' ::: rep f' items' ]]] *
          [[[ items' ::: Fe * (length items) |-> e *
                arrayN (@ptsto _ addr_eq_dec _) (length items + 1) (repeat item0 (items_per_val - 1)) ]]] *
          [[ items' = items ++ (updN block0 0 e)  ]] *
          [[ BFILE.ilist_safe ilist  (BFILE.pick_balloc frees  (MSAlloc ms'))
                              ilist' (BFILE.pick_balloc frees' (MSAlloc ms')) ]] *
          [[ BFILE.treeseq_ilist_safe inum ilist ilist' ]] )
    CRASH:hm' LOG.intact lxp F m0 sm hm'
    >} extend_array lxp bxp ixp inum e ms.
Proof.
(* original proof tokens: 148 *)

(* No more tactics to try *)
Admitted.

Theorem ifind_array_ok : forall lxp bxp ixp inum cond ms,
    {< F Fm Fi m0 sm m flist f items ilist frees,
    PRE:hm
          LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLL ms) sm hm *
          [[[ m ::: (Fm * BFILE.rep bxp sm ixp flist ilist frees (MSAllocC ms) (MSCache ms) (MSICache ms) (MSDBlocks ms)) ]]] *
          [[[ flist ::: (Fi * inum |-> f) ]]] *
          [[[ RAData f ::: rep f items ]]]
    POST:hm' RET:^(ms', r)
          LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLL ms') sm hm' *
          [[[ m ::: (Fm * BFILE.rep bxp sm ixp flist ilist frees (MSAllocC ms') (MSCache ms') (MSICache ms') (MSDBlocks ms')) ]]] *
          [[ MSAlloc ms' = MSAlloc ms ]] *
          [[ MSCache ms' = MSCache ms ]] *
          [[ MSAllocC ms' = MSAllocC ms ]] *
          [[ MSIAllocC ms' = MSIAllocC ms ]] *
          [[ MSDBlocks ms' = MSDBlocks ms ]] *
        ( [[ r = None    /\ forall i, i < length items ->
                            cond (selN items i item0) i = false ]] \/
          exists st,
          [[ r = Some st /\ cond (snd st) (fst st) = true ]] *
          [[[ items ::: arrayN_ex (@ptsto _ addr_eq_dec _) items (fst st) * (fst st) |-> (snd st) ]]] )
    CRASH:hm'  exists ms',
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLL ms') sm hm'
    >} ifind_array lxp ixp inum cond ms.
Proof.
(* original proof tokens: 88 *)

(* No more tactics to try *)
Admitted.

Hint Extern 1 ({{_}} Bind (get_array _ _ _ _ _) _) => apply get_array_ok : prog.
Hint Extern 1 ({{_}} Bind (put_array _ _ _ _ _ _) _) => apply put_array_ok : prog.
Hint Extern 1 ({{_}} Bind (extend_array _ _ _ _ _ _) _) => apply extend_array_ok : prog.
Hint Extern 1 ({{_}} Bind (ifind_array _ _ _ _ _) _) => apply ifind_array_ok : prog.
Hint Extern 0 (okToUnify (rep ?xp _) (rep ?xp _)) => constructor : okToUnify.
Lemma items_wellformed : forall F xp l m,
    (F * rep xp l)%pred m -> Forall Rec.well_formed l.
Proof.
(* original proof tokens: 24 *)

(* No more tactics to try *)
Admitted.

Lemma items_wellformed_pimpl : forall xp l,
    rep xp l =p=> [[ Forall Rec.well_formed l ]] * rep xp l.
Proof.
(* original proof tokens: 16 *)

(* No more tactics to try *)
Admitted.

Lemma item_wellformed : forall F xp m l i,
    (F * rep xp l)%pred m -> Rec.well_formed (selN l i item0).
Proof.
(* original proof tokens: 57 *)

(* No more tactics to try *)
Admitted.

Lemma items_length_ok : forall F xp l m,
    (F * rep xp l)%pred m ->
    length l = (RALen xp) * items_per_val.
Proof.
(* original proof tokens: 24 *)

(* No more tactics to try *)
Admitted.

Lemma items_length_ok_pimpl : forall xp l,
    rep xp l =p=> [[ length l = ((RALen xp) * items_per_val)%nat ]] * rep xp l.
Proof.
(* original proof tokens: 16 *)

(* No more tactics to try *)
Admitted.

Definition unpack blocks := fold_left iunpack blocks nil.
Definition pack_unpack_cond (items : list item) :=
    Forall Rec.well_formed items /\ exists nr, length items = nr * items_per_val.
Lemma pack_unpack_id : forall items,
    pack_unpack_cond items ->
    unpack (ipack items) = items.
Proof.
(* original proof tokens: 32 *)
intros.
eapply iunpack_ipack; eauto.
eauto.
destruct H.
destruct H0.
destruct H.
constructor; auto.
constructor; auto; auto.
destruct H as [Hwf Hlen]; destruct Hlen.
eauto.
rewrite e.
(* No more tactics to try *)
Admitted.

Lemma ipack_injective :
    cond_injective (ipack) (pack_unpack_cond).
Proof.
(* original proof tokens: 46 *)
(* generated proof tokens: 41 *)
intros items1 items2 H1 H2 H3.
apply pack_unpack_id in H1; apply pack_unpack_id in H2; subst; auto.
congruence.
Qed.

Lemma synced_list_injective :
    cond_injective (synced_list) (fun _ => True).
Proof.
(* original proof tokens: 49 *)

(* No more tactics to try *)
Admitted.

Lemma rep_items_eq : forall m f vs1 vs2,
    rep f vs1 m ->
    rep f vs2 m ->
    vs1 = vs2.
Proof.
(* original proof tokens: 65 *)
intros m f vs1 vs2 H1 H2.
inversion H1; inversion H2; subst; auto.
inversion H1; inversion H2; subst; auto.
(* No more tactics to try *)
Admitted.

Lemma xform_rep : forall f vs,
    crash_xform (rep f vs) =p=> rep f vs.
Proof.
(* original proof tokens: 31 *)

(* No more tactics to try *)
Admitted.

Lemma file_crash_rep : forall f f' vs,
    BFILE.file_crash f f' ->
    rep f vs (list2nmem (BFILE.BFData f)) ->
    rep f' vs (list2nmem (BFILE.BFData f')).
Proof.
(* original proof tokens: 82 *)
intros.
eapply pimpl_trans.
(* No more tactics to try *)
Admitted.

Lemma file_crash_rep_eq : forall f f' vs1 vs2,
    BFILE.file_crash f f' ->
    rep f  vs1 (list2nmem (BFILE.BFData f)) ->
    rep f' vs2 (list2nmem (BFILE.BFData f')) ->
    vs1 = vs2.
Proof.
(* original proof tokens: 36 *)

(* No more tactics to try *)
Admitted.

End FileRecArray.
