Require Import Prog.
Require Import Word.
Require Import Rec.
Require Import List.
Require Import Pred PredCrash.
Require Import Eqdep_dec.
Require Import Arith.
Require Import Hoare.
Require Import SepAuto.
Require Import Cache.
Require Import AsyncDisk.
Require Import Lia.
Import ListNotations.
Set Implicit Arguments.
Record log_xparams := {
  DataStart : addr; 
  LogHeader : addr; 

  LogDescriptor : addr; 
  LogDescLen : addr; 
  LogData : addr;    
  LogLen : addr      
}.
Record balloc_xparams := {
  BmapStart : addr;
  BmapNBlocks : addr
}.
Record inode_xparams := {
  IXStart : addr;
  IXLen : addr
}.
Record fs_xparams := {
  FSXPLog : log_xparams;
  FSXPInode : inode_xparams;
  FSXPBlockAlloc1 : balloc_xparams;
  FSXPBlockAlloc2 : balloc_xparams;
  FSXPInodeAlloc : balloc_xparams;
  FSXPRootInum : addr;
  FSXPMaxBlock : addr;
  FSXPMagic : addr
}.
Definition FSXPBlockAlloc fsxp :=
  (FSXPBlockAlloc1 fsxp, FSXPBlockAlloc2 fsxp).
Definition log_xparams_ok xp :=
  goodSize addrlen (DataStart xp) /\
  goodSize addrlen (LogHeader xp) /\
  goodSize addrlen ((LogDescriptor xp) + (LogDescLen xp)) /\
  goodSize addrlen ((LogData xp) + (LogLen xp)).
Definition balloc_xparams_ok xp :=
  goodSize addrlen ((BmapStart xp) + (BmapNBlocks xp)).
Definition inode_xparams_ok xp :=
  goodSize addrlen ((IXStart xp) + (IXLen xp)).
Definition fs_xparams_ok xp :=
  log_xparams_ok (FSXPLog xp) /\
  inode_xparams_ok (FSXPInode xp) /\
  balloc_xparams_ok (FSXPBlockAlloc1 xp) /\
  balloc_xparams_ok (FSXPBlockAlloc2 xp) /\
  balloc_xparams_ok (FSXPInodeAlloc xp) /\
  goodSize addrlen (FSXPRootInum xp) /\
  goodSize addrlen (FSXPMaxBlock xp) /\
  goodSize addrlen (FSXPMagic xp).
Ltac xparams_ok := 
  match goal with 
  | [ H: fs_xparams_ok ?xp |- goodSize _ _ ] =>
    unfold fs_xparams_ok, log_xparams_ok, balloc_xparams_ok, inode_xparams_ok in H;
    intuition; eauto
  end.
Definition addr2w (a : addr) : waddr := natToWord addrlen a.
