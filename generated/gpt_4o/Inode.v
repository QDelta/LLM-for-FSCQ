Require Import Coq.Strings.String.
Require Import Arith.
Require Import Pred PredCrash.
Require Import Word.
Require Import Prog.
Require Import Hoare.
Require Import SepAuto.
Require Import BasicProg.
Require Import Lia.
Require Import Log.
Require Import Array.
Require Import List ListUtils.
Require Import Bool.
Require Import Eqdep_dec.
Require Import Setoid.
Require Import Rec.
Require Import NArith.
Require Import WordAuto.
Require Import RecArrayUtils LogRecArray.
Require Import GenSepN.
Require Import Balloc.
Require Import ListPred.
Require Import FSLayout.
Require Import AsyncDisk.
Require Import DiskSet.
Require Import BlockPtr.
Require Import GenSepAuto.
Require Import Errno.
Require Import SyncedMem.
Import ListNotations.
Open Scope list.
Set Implicit Arguments.
Module INODE.
Definition iattrtype : Rec.type := Rec.RecF ([
    ("bytes",  Rec.WordF 64) ;       
    ("uid",    Rec.WordF 32) ;        
    ("gid",    Rec.WordF 32) ;        
    ("dev",    Rec.WordF 64) ;        
    ("mtime",  Rec.WordF 32) ;        
    ("atime",  Rec.WordF 32) ;        
    ("ctime",  Rec.WordF 32) ;        
    ("itype",  Rec.WordF  8) ;        
    ("unused", Rec.WordF 24)          
  ]).
Definition NDirect := 7.
Definition irectype : Rec.type := Rec.RecF ([
    ("len", Rec.WordF addrlen);     
    ("attrs", iattrtype);           
    ("indptr", Rec.WordF addrlen);  
    ("dindptr", Rec.WordF addrlen); 
    ("tindptr", Rec.WordF addrlen); 
    ("blocks", Rec.ArrayF (Rec.WordF addrlen) NDirect)]).
Module IRecSig <: RASig.
Definition xparams := inode_xparams.
Definition RAStart := IXStart.
Definition RALen := IXLen.
Definition xparams_ok (_ : xparams) := True.
Definition itemtype := irectype.
Definition items_per_val := valulen / (Rec.len itemtype).
Theorem blocksz_ok : valulen = Rec.len (Rec.ArrayF itemtype items_per_val).
Proof.
(* skipped proof tokens: 29 *)
Admitted.
End IRecSig.
Module IRec := LogRecArrayCache IRecSig.
Hint Extern 0 (okToUnify (IRec.rep _ _) (IRec.rep _ _)) => constructor : okToUnify.
Definition iattr := Rec.data iattrtype.
Definition irec := IRec.Defs.item.
Definition bnlist := list waddr.
Module BPtrSig <: BlockPtrSig.
Definition irec     := irec.
Definition iattr    := iattr.
Definition NDirect  := NDirect.
Fact NDirect_bound : NDirect <= addrlen.
compute; lia.
Qed.
Definition IRLen     (x : irec) := Eval compute_rec in # ( x :-> "len").
Definition IRIndPtr  (x : irec) := Eval compute_rec in # ( x :-> "indptr").
Definition IRDindPtr (x : irec) := Eval compute_rec in # ( x :-> "dindptr").
Definition IRTindPtr (x : irec) := Eval compute_rec in # ( x :-> "tindptr").
Definition IRBlocks  (x : irec) := Eval compute_rec in ( x :-> "blocks").
Definition IRAttrs   (x : irec) := Eval compute_rec in ( x :-> "attrs").
Definition upd_len (x : irec) v : irec := Eval compute_rec in (x :=> "len" := $ v).
Definition upd_irec (x : irec) len ibptr dibptr tibptr dbns : irec :=
      Eval compute_rec in
        (x :=> "len" := $ len
           :=> "indptr" := $ ibptr
           :=> "dindptr" := $ dibptr
           :=> "tindptr" := $ tibptr
           :=> "blocks" := dbns).
Fact upd_len_get_len : forall ir n,
      goodSize addrlen n -> IRLen (upd_len ir n) = n.
Proof.
(* skipped proof tokens: 33 *)
Admitted.
Fact upd_len_get_ind : forall ir n, IRIndPtr (upd_len ir n) = IRIndPtr ir.
Proof.
(* original proof tokens: 12 *)
(* generated proof tokens: 29 *)

Proof.
  intros ir n.
  unfold upd_len, IRIndPtr.
  simpl.
  reflexivity.
Qed.

Fact upd_len_get_dind : forall ir n, IRDindPtr (upd_len ir n) = IRDindPtr ir.
Proof.
(* skipped proof tokens: 12 *)
Admitted.
Fact upd_len_get_tind : forall ir n, IRTindPtr (upd_len ir n) = IRTindPtr ir.
Proof.
(* skipped proof tokens: 12 *)
Admitted.
Fact upd_len_get_blk : forall ir n, IRBlocks (upd_len ir n) = IRBlocks ir.
Proof.
(* skipped proof tokens: 12 *)
Admitted.
Fact upd_len_get_iattr : forall ir n, IRAttrs (upd_len ir n) = IRAttrs ir.
Proof.
(* skipped proof tokens: 12 *)
Admitted.
Fact upd_irec_get_len : forall ir len ibptr dibptr tibptr dbns,
      goodSize addrlen len -> IRLen (upd_irec ir len ibptr dibptr tibptr dbns) = len.
Proof.
(* skipped proof tokens: 27 *)
Admitted.
Fact upd_irec_get_ind : forall ir len ibptr dibptr tibptr dbns,
      goodSize addrlen ibptr -> IRIndPtr (upd_irec ir len ibptr dibptr tibptr dbns) = ibptr.
Proof.
(* skipped proof tokens: 27 *)
Admitted.
Fact upd_irec_get_dind : forall ir len ibptr dibptr tibptr dbns,
      goodSize addrlen dibptr -> IRDindPtr (upd_irec ir len ibptr dibptr tibptr dbns) = dibptr.
Proof.
(* skipped proof tokens: 27 *)
Admitted.
Fact upd_irec_get_tind : forall ir len ibptr dibptr tibptr dbns,
      goodSize addrlen tibptr -> IRTindPtr (upd_irec ir len ibptr dibptr tibptr dbns) = tibptr.
Proof.
(* skipped proof tokens: 27 *)
Admitted.
Fact upd_irec_get_blk : forall ir len ibptr dibptr tibptr dbns,
      IRBlocks (upd_irec ir len ibptr dibptr tibptr dbns) = dbns.
Proof.
(* skipped proof tokens: 12 *)
Admitted.
Fact upd_irec_get_iattr : forall ir len ibptr dibptr tibptr dbns,
      IRAttrs (upd_irec ir len ibptr dibptr tibptr dbns) = IRAttrs ir.
Proof.
(* skipped proof tokens: 12 *)
Admitted.
Fact upd_irec_eq_upd_len : forall ir len, goodSize addrlen len ->
      upd_len ir len = upd_irec ir len (IRIndPtr ir) (IRDindPtr ir) (IRTindPtr ir) (IRBlocks ir).
Proof.
(* skipped proof tokens: 77 *)
Admitted.
Fact get_len_goodSize : forall ir, goodSize addrlen (IRLen ir).
Proof.
(* skipped proof tokens: 16 *)
Admitted.
Fact get_ind_goodSize : forall ir, goodSize addrlen (IRIndPtr ir).
Proof.
(* skipped proof tokens: 16 *)
Admitted.
Fact get_dind_goodSize : forall ir, goodSize addrlen (IRDindPtr ir).
Proof.
(* skipped proof tokens: 16 *)
Admitted.
Fact get_tind_goodSize : forall ir, goodSize addrlen (IRTindPtr ir).
Proof.
(* skipped proof tokens: 16 *)
Admitted.
End BPtrSig.
Module Ind := BlockPtr BPtrSig.
Definition NBlocks := let NIndirect := Ind.IndSig.items_per_val in
    NDirect + NIndirect + NIndirect ^ 2 + NIndirect ^ 3.
Definition items_per_val := IRecSig.items_per_val.
Definition init lxp xp ms :=
    ms <- IRec.init lxp xp ms;
    Ret ms.
Definition getlen lxp xp inum cache ms := Eval compute_rec in
    let^ (cache, ms, (ir : irec)) <- IRec.get_array lxp xp inum cache ms;
    Ret ^(cache, ms, # (ir :-> "len" )).
Definition ABytes  (a : iattr) := Eval cbn in ( a :-> "bytes" ).
Definition AMTime  (a : iattr) := Eval cbn in ( a :-> "mtime" ).
Definition AType   (a : iattr) := Eval cbn in ( a :-> "itype" ).
Definition ADev    (a : iattr) := Eval cbn in ( a :-> "dev" ).
Definition getattrs lxp xp inum cache ms := Eval compute_rec in
    let^ (cache, ms, (i : irec)) <- IRec.get_array lxp xp inum cache ms;
    Ret ^(cache, ms, (i :-> "attrs")).
Definition setattrs lxp xp inum attr cache ms := Eval compute_rec in
    let^ (cache, ms, (i : irec)) <- IRec.get_array lxp xp inum cache ms;
    let^ (cache, ms) <- IRec.put_array lxp xp inum (i :=> "attrs" := attr) cache ms;
    Ret ^(cache, ms).
Inductive iattrupd_arg :=
  | UBytes (v : word 64)
  | UMTime (v : word 32)
  | UType  (v : word  8)
  | UDev   (v : word 64)
  .
Definition iattr_upd (e : iattr) (a : iattrupd_arg) : iattr := Eval compute_rec in
  match a with
  | UBytes v => (e :=> "bytes" := v)
  | UMTime v => (e :=> "mtime" := v)
  | UType  v => (e :=> "itype" := v)
  | UDev   v => (e :=> "dev"   := v)
  end.
Definition updattr lxp xp inum a cache ms := Eval compute_rec in
    let^ (cache, ms, (i : irec)) <- IRec.get_array lxp xp inum cache ms;
    let^ (cache, ms) <- IRec.put_array lxp xp inum (i :=> "attrs" := (iattr_upd (i :-> "attrs") a)) cache ms;
    Ret ^(cache, ms).
Definition getbnum lxp xp inum off cache ms :=
    let^ (cache, ms, (ir : irec)) <- IRec.get_array lxp xp inum cache ms;
    let^ (ms, r) <- Ind.get lxp ir off ms;
    Ret ^(cache, ms, r).
Definition getallbnum lxp xp inum cache ms :=
    let^ (cache, ms, (ir : irec)) <- IRec.get_array lxp xp inum cache ms;
    let^ (ms, r) <- Ind.read lxp ir ms;
    Ret ^(cache, ms, r).
Definition shrink lxp bxp xp inum nr cache ms :=
    let^ (cache, lms, (ir : irec)) <- IRec.get_array lxp xp inum cache (BALLOCC.MSLog ms);
    let^ (ms, ir') <- Ind.shrink lxp bxp ir nr (BALLOCC.upd_memstate lms ms);
    let^ (cache, lms) <- IRec.put_array lxp xp inum ir' cache (BALLOCC.MSLog ms);
    Ret ^(cache, (BALLOCC.upd_memstate lms ms)).
Definition reset lxp bxp xp inum nr attr cache ms := Eval compute_rec in
    let^ (cache, lms, (ir : irec)) <- IRec.get_array lxp xp inum cache (BALLOCC.MSLog ms);
    let^ (ms, (ir': irec)) <- Ind.shrink lxp bxp ir nr (BALLOCC.upd_memstate lms ms);
    let^ (cache, lms) <- IRec.put_array lxp xp inum (ir' :=> "attrs" := attr) cache (BALLOCC.MSLog ms);
    Ret ^(cache, (BALLOCC.upd_memstate lms ms)).
Definition grow lxp bxp xp inum bn cache ms :=
    let^ (cache, lms, (ir : irec)) <- IRec.get_array lxp xp inum cache (BALLOCC.MSLog ms);
    let^ (ms, r) <- Ind.grow lxp bxp ir ($ bn) (BALLOCC.upd_memstate lms ms);
    match r with
    | Err e => Ret ^(cache, ms, Err e)
    | OK ir' =>
        let^ (cache, lms) <- IRec.put_array lxp xp inum ir' cache (BALLOCC.MSLog ms);
        Ret ^(cache, (BALLOCC.upd_memstate lms ms), OK tt)
    end.
Record inode := mk_inode {
    IBlocks : bnlist;
    IAttr   : iattr
  }.
Definition iattr0 := @Rec.of_word iattrtype $0.
Definition inode0 := mk_inode nil iattr0.
Definition irec0 := IRec.Defs.item0.
Definition inode_match bxp ino (ir : irec) := Eval compute_rec in
    let '(ino, IFs) := ino in
    ( [[ IAttr ino = (ir :-> "attrs") ]] *
      [[ Forall (fun a => BALLOCC.bn_valid bxp (# a) ) (IBlocks ino) ]] *
      Ind.rep bxp IFs ir (IBlocks ino) )%pred.
Definition rep bxp IFs xp (ilist : list inode) cache := (
     exists reclist fsl, IRec.rep xp reclist cache *
     [[ IFs <=p=> pred_fold_left fsl ]] * [[ length ilist = length fsl ]] *
     listmatch (inode_match bxp) (combine ilist fsl) reclist)%pred.
Lemma rep_length_pimpl : forall bxp xp IFs ilist cache,
    rep bxp IFs xp ilist cache =p=> rep bxp IFs xp ilist cache *
    [[ length ilist = ((IRecSig.RALen xp) * IRecSig.items_per_val)%nat ]].
Proof.
(* skipped proof tokens: 64 *)
Admitted.
Lemma irec_well_formed : forall Fm xp l i inum m cache,
    (Fm * IRec.rep xp l cache)%pred m
    -> i = selN l inum irec0
    -> Rec.well_formed i.
Proof.
(* skipped proof tokens: 25 *)
Admitted.
Lemma direct_blocks_length: forall (i : irec),
    Rec.well_formed i
    -> length (i :-> "blocks") = NDirect.
Proof.
(* skipped proof tokens: 34 *)
Admitted.
Lemma irec_blocks_length: forall m xp l inum Fm cache,
    (Fm * IRec.rep xp l cache)%pred m ->
    length (selN l inum irec0 :-> "blocks") = NDirect.
Proof.
(* skipped proof tokens: 29 *)
Admitted.
Lemma irec_blocks_length': forall m xp l inum Fm len attrs ind dind tind blks u cache,
    (Fm * IRec.rep xp l cache)%pred m ->
    (len, (attrs, (ind, (dind, (tind, (blks, u)))))) = selN l inum irec0 ->
    length blks = NDirect.
Proof.
(* skipped proof tokens: 56 *)
Admitted.
Theorem rep_bxp_switch : forall bxp bxp' xp IFs ilist cache,
    BmapNBlocks bxp = BmapNBlocks bxp' ->
    rep bxp IFs xp ilist cache <=p=> rep bxp' IFs xp ilist cache.
Proof.
(* skipped proof tokens: 104 *)
Admitted.
Lemma rep_clear_cache: forall bxp IFs xp ilist cache,
    rep bxp IFs xp ilist cache =p=> rep bxp IFs xp ilist IRec.cache0.
Proof.
(* skipped proof tokens: 30 *)
Admitted.
Lemma rep_upd_attrs: forall bxp Fs ir iblocks (attr : iattr),
    Ind.rep bxp Fs ir iblocks <=p=> Ind.rep bxp Fs (ir :=> "attrs" := attr) iblocks.
Proof.
(* skipped proof tokens: 78 *)
Admitted.
Fact resolve_selN_irec0 : forall l i d,
    d = irec0 -> selN l i d = selN l i irec0.
Proof.
(* skipped proof tokens: 14 *)
Admitted.
Fact resolve_selN_inode0 : forall l i d,
    d = inode0 -> selN l i d = selN l i inode0.
Proof.
(* skipped proof tokens: 14 *)
Admitted.
Hint Rewrite resolve_selN_irec0   using reflexivity : defaults.
Hint Rewrite resolve_selN_inode0  using reflexivity : defaults.
Ltac destruct_irec' x :=
    match type of x with
    | irec => let b := fresh in destruct x as [? b] eqn:? ; destruct_irec' b
    | iattr => let b := fresh in destruct x as [? b] eqn:? ; destruct_irec' b
    | prod _ _ => let b := fresh in destruct x as [? b] eqn:? ; destruct_irec' b
    | _ => idtac
    end.
Ltac destruct_irec x :=
    match x with
    | (?a, ?b) => (destruct_irec a || destruct_irec b)
    | fst ?a => destruct_irec a
    | snd ?a => destruct_irec a
    | _ => destruct_irec' x; simpl
    end.
Ltac smash_rec_well_formed' :=
    match goal with
    | [ |- Rec.well_formed ?x ] => destruct_irec x
    end.
Ltac smash_rec_well_formed :=
    subst; autorewrite with defaults;
    repeat smash_rec_well_formed';
    unfold Rec.well_formed; simpl;
    try rewrite Forall_forall; intuition.
Ltac irec_wf :=
    smash_rec_well_formed;
    match goal with
      | [ H : ?p %pred ?mm |- length ?d = NDirect ] =>
      match p with
        | context [ IRec.rep ?xp ?ll ?cc ] => 
          eapply irec_blocks_length' with (m := mm) (l := ll) (cache := cc) (xp := xp); eauto;
          pred_apply; cancel
      end
    end.
Arguments Rec.well_formed : simpl never.
Lemma inode_match_init_emp: forall bxp,
    inode_match bxp (inode0, emp) IRec.Defs.item0 <=p=> emp.
Proof.
(* skipped proof tokens: 104 *)
Admitted.
Lemma inode_match_init_ok : forall bxp n,
    emp =p=> listmatch (inode_match bxp) (repeat (inode0, emp) n) (repeat IRec.Defs.item0 n).
Proof.
(* skipped proof tokens: 44 *)
Admitted.
Theorem init_ok : forall lxp bxp xp ms,
    {< F Fm Fs m0 sm m l,
    PRE:hm 
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms sm hm *
           [[[ m ::: (Fm * arrayN (@ptsto _ _ _) (IXStart xp) l) ]]] *
           [[ Fs sm ]] *
           [[ length l = (IXLen xp) /\ (IXStart xp) <> 0 ]]
    POST:hm' RET:ms exists m' IFs,
           LOG.rep lxp F (LOG.ActiveTxn m0 m') ms sm hm' *
           [[[ m' ::: (Fm * rep bxp IFs xp (repeat inode0 ((IXLen xp) * IRecSig.items_per_val)) (IRec.cache0)) ]]] *
           [[ (Fs * IFs)%pred sm ]]
    CRASH:hm'  LOG.intact lxp F m0 sm hm'
    >} init lxp xp ms.
Proof.
(* skipped proof tokens: 70 *)
Admitted.
Theorem getlen_ok : forall lxp bxp xp inum cache ms,
    {< F Fm Fi m0 sm m IFs ilist ino,
    PRE:hm
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms sm hm *
           [[[ m ::: (Fm * rep bxp IFs xp ilist cache) ]]] *
           [[[ ilist ::: Fi * inum |-> ino ]]]
    POST:hm' RET:^(cache', ms,r)
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms sm hm' *
           [[[ m ::: (Fm * rep bxp IFs xp ilist cache') ]]] *
           [[ r = length (IBlocks ino) ]]
    CRASH:hm'  exists ms',
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms' sm hm'
    >} getlen lxp xp inum cache ms.
Proof.
(* skipped proof tokens: 76 *)
Admitted.
Theorem getattrs_ok : forall lxp bxp xp inum cache ms,
    {< F Fm Fi m0 sm m IFs ilist ino,
    PRE:hm
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms sm hm *
           [[[ m ::: (Fm * rep bxp IFs xp ilist cache) ]]] *
           [[[ ilist ::: (Fi * inum |-> ino) ]]]
    POST:hm' RET:^(cache',ms,r)
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms sm hm' *
           [[[ m ::: (Fm * rep bxp IFs xp ilist cache') ]]] *
           [[ r = IAttr ino ]]
    CRASH:hm'  exists ms',
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms' sm hm'
    >} getattrs lxp xp inum cache ms.
Proof.
(* skipped proof tokens: 54 *)
Admitted.
Theorem setattrs_ok : forall lxp bxp xp inum attr cache ms,
    {< F Fm Fi m0 sm m IFs ilist ino,
    PRE:hm 
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms sm hm *
           [[[ m ::: (Fm * rep bxp IFs xp ilist cache) ]]] *
           [[[ ilist ::: (Fi * inum |-> ino) ]]]
    POST:hm' RET:^(cache',ms) exists m' ilist' ino',
           LOG.rep lxp F (LOG.ActiveTxn m0 m') ms sm hm' *
           [[[ m' ::: (Fm * rep bxp IFs xp ilist' cache') ]]] *
           [[[ ilist' ::: (Fi * inum |-> ino') ]]] *
           [[ ino' = mk_inode (IBlocks ino) attr ]]
    CRASH:hm'  LOG.intact lxp F m0 sm hm'
    >} setattrs lxp xp inum attr cache ms.
Proof.
(* skipped proof tokens: 151 *)
Admitted.
Theorem updattr_ok : forall lxp bxp xp inum kv cache ms,
    {< F Fm Fi Fs m0 sm m IFs ilist ino,
    PRE:hm
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms sm hm *
           [[[ m ::: (Fm * rep bxp IFs xp ilist cache) ]]] *
           [[[ ilist ::: (Fi * inum |-> ino) ]]] *
           [[ (Fs * IFs)%pred sm ]]
    POST:hm' RET:^(cache',ms) exists m' ilist' ino' IFs',
           LOG.rep lxp F (LOG.ActiveTxn m0 m') ms sm hm' *
           [[[ m' ::: (Fm * rep bxp IFs' xp ilist' cache') ]]] *
           [[[ ilist' ::: (Fi * inum |-> ino') ]]] *
           [[ (Fs * IFs')%pred sm ]] *
           [[ ino' = mk_inode (IBlocks ino) (iattr_upd (IAttr ino) kv) ]]
    CRASH:hm'  LOG.intact lxp F m0 sm hm'
    >} updattr lxp xp inum kv cache ms.
Proof.
(* skipped proof tokens: 157 *)
Admitted.
Theorem getbnum_ok : forall lxp bxp xp inum off cache ms,
    {< F Fm Fi m0 sm m IFs ilist ino,
    PRE:hm
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms sm hm *
           [[ off < length (IBlocks ino) ]] *
           [[[ m ::: (Fm * rep bxp IFs xp ilist cache) ]]] *
           [[[ ilist ::: (Fi * inum |-> ino) ]]]
    POST:hm' RET:^(cache', ms, r)
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms sm hm' *
           [[[ m ::: (Fm * rep bxp IFs xp ilist cache') ]]] *
           [[ r = selN (IBlocks ino) off $0 ]]
    CRASH:hm'  exists ms',
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms' sm hm'
    >} getbnum lxp xp inum off cache ms.
Proof.
(* skipped proof tokens: 100 *)
Admitted.
Theorem getallbnum_ok : forall lxp bxp xp inum cache ms,
    {< F Fm Fi m0 sm m IFs ilist ino,
    PRE:hm
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms sm hm *
           [[[ m ::: (Fm * rep bxp IFs xp ilist cache) ]]] *
           [[[ ilist ::: (Fi * inum |-> ino) ]]]
    POST:hm' RET:^(cache', ms, r)
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms sm hm' *
           [[[ m ::: (Fm * rep bxp IFs xp ilist cache') ]]] *
           [[ r = (IBlocks ino) ]]
    CRASH:hm'  exists ms',
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms' sm hm'
    >} getallbnum lxp xp inum cache ms.
Proof.
(* skipped proof tokens: 98 *)
Admitted.
Local Hint Extern 0 (okToUnify (listmatch ?f _ ?b) (listmatch ?f _ ?b)) => constructor : okToUnify.
Theorem shrink_ok : forall lxp bxp xp inum nr cache ms,
    {< F Fm Fi Fs m0 sm m IFs ilist ino freelist,
    PRE:hm
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (BALLOCC.MSLog ms) sm hm *
           [[[ m ::: (Fm * rep bxp IFs xp ilist cache * BALLOCC.rep bxp freelist ms) ]]] *
           [[[ ilist ::: (Fi * inum |-> ino) ]]] *
           [[ (Fs * IFs * BALLOCC.smrep freelist)%pred sm ]]
    POST:hm' RET:^(cache', ms) exists m' ilist' ino' freelist' IFs',
           LOG.rep lxp F (LOG.ActiveTxn m0 m') (BALLOCC.MSLog ms) sm hm' *
           [[[ m' ::: (Fm * rep bxp IFs' xp ilist' cache' * BALLOCC.rep bxp freelist' ms) ]]] *
           [[[ ilist' ::: (Fi * inum |-> ino') ]]] *
           [[ (Fs * IFs' * BALLOCC.smrep freelist')%pred sm ]] *
           [[ ino' = mk_inode (cuttail nr (IBlocks ino)) (IAttr ino) ]] *
           [[ incl freelist freelist' ]]
    CRASH:hm'  LOG.intact lxp F m0 sm hm'
    >} shrink lxp bxp xp inum nr cache ms.
Proof.
(* skipped proof tokens: 384 *)
Admitted.
Theorem reset_ok : forall lxp bxp xp inum nr attr cache ms,
    {< F Fm Fi Fs m0 sm m IFs ilist ino freelist,
    PRE:hm
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (BALLOCC.MSLog ms) sm hm *
           [[[ m ::: (Fm * rep bxp IFs xp ilist cache * BALLOCC.rep bxp freelist ms) ]]] *
           [[[ ilist ::: (Fi * inum |-> ino) ]]] *
           [[ (Fs * IFs * BALLOCC.smrep freelist)%pred sm ]]
    POST:hm' RET:^(cache', ms) exists m' ilist' ino' freelist' IFs',
           LOG.rep lxp F (LOG.ActiveTxn m0 m') (BALLOCC.MSLog ms) sm hm' *
           [[[ m' ::: (Fm * rep bxp IFs' xp ilist' cache' * BALLOCC.rep bxp freelist' ms) ]]] *
           [[[ ilist' ::: (Fi * inum |-> ino') ]]] *
           [[ (Fs * IFs' * BALLOCC.smrep freelist')%pred sm ]] *
           [[ ilist' = updN ilist inum ino' ]] *
           [[ ino' = mk_inode (cuttail nr (IBlocks ino)) attr ]] *
           [[ incl freelist freelist' ]]
    CRASH:hm'  LOG.intact lxp F m0 sm hm'
    >} reset lxp bxp xp inum nr attr cache ms.
Proof.
(* skipped proof tokens: 389 *)
Admitted.
Lemma grow_wellformed : forall (a : BPtrSig.irec) inum reclist cache F1 F2 F3 F4 m xp,
    ((((F1 * IRec.rep xp reclist cache) * F2) * F3) * F4)%pred m ->
    length (BPtrSig.IRBlocks a) = length (BPtrSig.IRBlocks (selN reclist inum irec0)) ->
    inum < length reclist ->
    Rec.well_formed a.
Proof.
(* original proof tokens: 109 *)

(* No more tactics to try *)
Admitted.

Theorem grow_ok : forall lxp bxp xp inum bn cache ms,
    {< F Fm Fi Fs m0 sm m IFs ilist ino freelist,
    PRE:hm
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (BALLOCC.MSLog ms) sm hm *
           [[ length (IBlocks ino) < NBlocks ]] *
           [[ BALLOCC.bn_valid bxp bn ]] *
           [[[ m ::: (Fm * rep bxp IFs xp ilist cache * BALLOCC.rep bxp freelist ms) ]]] *
           [[[ ilist ::: (Fi * inum |-> ino) ]]] *
           [[ (Fs * IFs * BALLOCC.smrep freelist)%pred sm ]]
    POST:hm' RET:^(cache', ms, r)
           exists m',
           [[ isError r ]] * LOG.rep lxp F (LOG.ActiveTxn m0 m') (BALLOCC.MSLog ms) sm hm' \/
           [[ r = OK tt ]] * exists ilist' ino' freelist' IFs',
           LOG.rep lxp F (LOG.ActiveTxn m0 m') (BALLOCC.MSLog ms) sm hm' *
           [[[ m' ::: (Fm * rep bxp IFs' xp ilist' cache' * BALLOCC.rep bxp freelist' ms) ]]] *
           [[[ ilist' ::: (Fi * inum |-> ino') ]]] *
           [[ (Fs * IFs' * BALLOCC.smrep freelist')%pred sm ]] *
           [[ ino' = mk_inode ((IBlocks ino) ++ [$ bn]) (IAttr ino) ]] *
           [[ incl freelist' freelist ]]
    CRASH:hm'  LOG.intact lxp F m0 sm hm'
    >} grow lxp bxp xp inum bn cache ms.
Proof.
(* skipped proof tokens: 262 *)
Admitted.
Hint Extern 1 ({{_}} Bind (init _ _ _) _) => apply init_ok : prog.
Hint Extern 1 ({{_}} Bind (getlen _ _ _ _ _) _) => apply getlen_ok : prog.
Hint Extern 1 ({{_}} Bind (getattrs _ _ _ _ _) _) => apply getattrs_ok : prog.
Hint Extern 1 ({{_}} Bind (setattrs _ _ _ _ _ _) _) => apply setattrs_ok : prog.
Hint Extern 1 ({{_}} Bind (updattr _ _ _ _ _ _) _) => apply updattr_ok : prog.
Hint Extern 1 ({{_}} Bind (getbnum _ _ _ _ _ _) _) => apply getbnum_ok : prog.
Hint Extern 1 ({{_}} Bind (getallbnum _ _ _ _ _) _) => apply getallbnum_ok : prog.
Hint Extern 1 ({{_}} Bind (grow _ _ _ _ _ _ _) _) => apply grow_ok : prog.
Hint Extern 1 ({{_}} Bind (shrink _ _ _ _ _ _ _) _) => apply shrink_ok : prog.
Hint Extern 1 ({{_}} Bind (reset _ _ _ _ _ _ _ _) _) => apply reset_ok : prog.
Hint Extern 0 (okToUnify (rep _ _ _ _ _) (rep _ _ _ _ _)) => constructor : okToUnify.
Lemma inode_match_sm_sync_invariant: forall bxp x y,
    inode_match bxp x y <=p=> (inode_match bxp x y * [[ SyncedMem.sm_sync_invariant (snd x) ]])%pred.
Proof.
(* skipped proof tokens: 62 *)
Admitted.
Lemma rep_IFs_sync_invariant: forall bxp IFs ixp ilist icache m F,
    (F * INODE.rep bxp IFs ixp ilist icache)%pred m ->
    SyncedMem.sm_sync_invariant IFs.
Proof.
(* skipped proof tokens: 126 *)
Admitted.
Lemma inode_rep_bn_valid_piff : forall bxp IFs xp l c,
    rep bxp IFs xp l c <=p=> rep bxp IFs xp l c *
      [[ forall inum, inum < length l ->
         Forall (fun a => BALLOCC.bn_valid bxp (# a) ) (IBlocks (selN l inum inode0)) ]].
Proof.
(* skipped proof tokens: 79 *)
Admitted.
Lemma inode_rep_bn_nonzero_pimpl : forall bxp IFs xp l c,
    rep bxp IFs xp l c =p=> rep bxp IFs xp l c *
      [[ forall inum off, inum < length l ->
         off < length (IBlocks (selN l inum inode0)) ->
         # (selN (IBlocks (selN l inum inode0)) off $0) <> 0 ]].
Proof.
(* skipped proof tokens: 63 *)
Admitted.
Lemma crash_xform_inode_match : forall xp a b,
    crash_xform (inode_match xp a b) <=p=> inode_match xp a b.
Proof.
(* skipped proof tokens: 46 *)
Admitted.
Lemma listmatch_inode_match_sm_sync_invariant: forall bxp inodes lfs l,
    length inodes = length lfs ->
    listmatch (inode_match bxp) (combine inodes lfs) l =p=>
    listmatch (inode_match bxp) (combine inodes lfs) l * [[ sm_sync_invariant (pred_fold_left lfs) ]].
Proof.
(* skipped proof tokens: 116 *)
Admitted.
Theorem xform_rep : forall bxp Fs xp l c,
    crash_xform (rep bxp Fs xp l c) <=p=> rep bxp Fs xp l c * [[ sm_sync_invariant Fs ]].
Proof.
(* skipped proof tokens: 111 *)
Admitted.
End INODE.
