Require Import FunctionalExtensionality.
Set Implicit Arguments.
Definition EqDec (T : Type) := forall (a b : T), {a = b} + {a <> b}.
Definition mem {A : Type} {AEQ : EqDec A} {V : Type} := A -> option V.
Definition empty_mem {A : Type} {AEQ : EqDec A} {V : Type} : @mem A AEQ V := fun a => None.
Section GenMem.
Variable A : Type.
Variable V : Type.
Variable AEQ : EqDec A.
Definition upd (m : @mem A AEQ V) (a : A) (v : V) : @mem A AEQ V :=
    fun a' => if AEQ a' a then Some v else m a'.
Definition updSome (m : @mem A AEQ V) (a : A) (v : V) : @mem A AEQ V :=
    fun a' => if AEQ a' a then
      match m a with
      | None => None
      | Some _ => Some v
      end else m a'.
Definition delete (m : @mem A AEQ V) (a : A) : @mem A AEQ V :=
    fun a' => if AEQ a' a then None else m a'.
Definition insert (m : @mem A AEQ V) (a : A) (v : V) : @mem A AEQ V :=
    fun a' => if AEQ a' a then
      match m a with
      | None => Some v
      | Some _ => m a'
      end else m a'.
Theorem upd_eq : forall m (a : A) (v : V) a',
    a' = a -> upd m a v a' = Some v.
Proof.
(* original proof tokens: 26 *)
intros m a v a' H.
rewrite H.
(* No more tactics to try *)
Admitted.

Theorem updSome_eq : forall m (a : A) (v v' : V) a',
    m a = Some v' -> a' = a -> updSome m a v a' = Some v.
(* hint proof tokens: 31 *)
Proof.
    intros; subst; unfold updSome.
    rewrite H.
    destruct (AEQ a a); tauto.
  Qed.
Theorem insert_eq : forall m (a : A) (v v' : V) a',
    m a = None -> a' = a -> insert m a v a' = Some v.
(* hint proof tokens: 31 *)
Proof.
    intros; subst; unfold insert.
    rewrite H.
    destruct (AEQ a a); congruence.
  Qed.
Theorem upd_ne : forall m (a : A) (v : V) a',
    a' <> a -> upd m a v a' = m a'.
Proof.
(* original proof tokens: 27 *)
intros.
unfold upd.
destruct (AEQ a' a).
(* No more tactics to try *)
Admitted.

Theorem updSome_ne : forall m (a : A) (v : V) a',
    a' <> a -> updSome m a v a' = m a'.
(* hint proof tokens: 28 *)
Proof.
    intros; subst; unfold updSome.
    destruct (AEQ a' a); tauto.
  Qed.
Theorem insert_ne : forall m (a : A) (v : V) a',
    a' <> a -> insert m a v a' = m a'.
(* hint proof tokens: 28 *)
Proof.
    intros; subst; unfold insert.
    destruct (AEQ a' a); congruence.
  Qed.
Theorem upd_repeat: forall m (a : A) (v v':V),
    upd (upd m a v') a v = upd m a v.
Proof.
(* original proof tokens: 44 *)
(* generated proof tokens: 33 *)
intros.
unfold upd.
apply functional_extensionality.
intros x.
destruct (AEQ x a); congruence.
Qed.

Theorem updSome_repeat: forall m (a : A) (v v':V),
    updSome (updSome m a v') a v = updSome m a v.
Proof.
(* original proof tokens: 53 *)
intros.
unfold updSome.
destruct (AEQ a a).
(* No more tactics to try *)
Admitted.

Theorem insert_repeat: forall m (a : A) (v v':V),
    insert (insert m a v) a v' = insert m a v.
Proof.
(* original proof tokens: 76 *)
intros.
unfold insert.
destruct (m a).
apply functional_extensionality.
(* No more tactics to try *)
Admitted.

Theorem upd_nop: forall m (a : A) (v : V),
    m a = Some v ->
    upd m a v = m.
Proof.
(* original proof tokens: 49 *)
intros.
apply functional_extensionality.
intros x.
destruct (AEQ x a).
(* No more tactics to try *)
Admitted.

Theorem updSome_nop: forall m (a : A) (v : V),
    m a = Some v ->
    updSome m a v = m.
(* hint proof tokens: 51 *)
Proof.
    intros; apply functional_extensionality; intros.
    case_eq (AEQ a x); intros; subst.
    repeat erewrite updSome_eq; eauto.
    repeat rewrite updSome_ne; auto.
  Qed.
Theorem updSome_none : forall m (a : A) (v : V),
    m a = None ->
    updSome m a v = m.
(* hint proof tokens: 38 *)
Proof.
    unfold updSome; intros; apply functional_extensionality; intros.
    rewrite H.
    destruct (AEQ x a); subst; auto.
  Qed.
Theorem upd_comm: forall m (a0 : A) (v0 : V) a1 v1, a0 <> a1
    -> upd (upd m a0 v0) a1 v1 = upd (upd m a1 v1) a0 v0.
Proof.
(* original proof tokens: 73 *)
intros.
apply functional_extensionality; intros.
case_eq (AEQ x a0); intros; subst.
rewrite upd_ne; auto.
rewrite upd_ne; auto.
rewrite upd_eq; auto.
(* No more tactics to try *)
Admitted.

Theorem updSome_comm: forall m (a0 : A) (v0 : V) a1 v1, a0 <> a1
    -> updSome (updSome m a0 v0) a1 v1 = updSome (updSome m a1 v1) a0 v0.
Proof.
(* original proof tokens: 74 *)
intros.
apply functional_extensionality; intros.
case_eq (AEQ x a0); intros; subst.
rewrite updSome_ne; auto.
rewrite updSome_ne; auto.
rewrite updSome_ne; auto.
rewrite updSome_ne.
auto.
(* No more tactics to try *)
Admitted.

Theorem updSome_insert_comm: forall m (a0 : A) (v0 : V) a1 v1, a0 <> a1
    -> updSome (insert m a0 v0) a1 v1 = insert (updSome m a1 v1) a0 v0.
(* hint proof tokens: 76 *)
Proof.
    intros; apply functional_extensionality; unfold updSome, insert; intros.
    destruct (AEQ a1 a0); destruct (AEQ a0 a1); try congruence.
    case_eq (AEQ x a1); case_eq (AEQ x a0); intros; subst; try congruence.
  Qed.
Theorem updSome_delete_comm: forall m (a0 : A) a1 (v1 : V), a0 <> a1
    -> updSome (delete m a0) a1 v1 = delete (updSome m a1 v1) a0.
Proof.
(* original proof tokens: 76 *)
intros.
apply functional_extensionality; intros.
destruct (AEQ x a0); destruct (AEQ x a1); try congruence.
rewrite e.
(* No more tactics to try *)
Admitted.

Theorem insert_comm: forall m (a0 : A) (v0 : V) a1 v1, a0 <> a1
    -> insert (insert m a0 v0) a1 v1 = insert (insert m a1 v1) a0 v0.
(* hint proof tokens: 73 *)
Proof.
    intros; apply functional_extensionality; unfold insert; intros.
    destruct (AEQ a1 a0); destruct (AEQ a0 a1); try congruence.
    case_eq (AEQ x a1); case_eq (AEQ x a0); intros; subst; try congruence.
  Qed.
Theorem insert_delete_comm: forall m (a0 : A) a1 (v1 : V), a0 <> a1
    -> insert (delete m a0) a1 v1 = delete (insert m a1 v1) a0.
(* hint proof tokens: 75 *)
Proof.
    intros; apply functional_extensionality; unfold insert, delete; intros.
    destruct (AEQ a1 a0); destruct (AEQ a0 a1); try congruence.
    case_eq (AEQ x a1); case_eq (AEQ x a0); intros; subst; try congruence.
  Qed.
Theorem delete_comm: forall m (a0 : A) a1, a0 <> a1
    -> delete (delete m a0) a1 = delete (delete m a1) a0.
(* hint proof tokens: 73 *)
Proof.
    intros; apply functional_extensionality; unfold delete; intros.
    destruct (AEQ a1 a0); destruct (AEQ a0 a1); try congruence.
    case_eq (AEQ x a1); case_eq (AEQ x a0); intros; subst; try congruence.
  Qed.
End GenMem.
Hint Rewrite upd_eq using (solve [ auto ]) : upd.
Hint Rewrite upd_ne using (solve [ auto ]) : upd.
