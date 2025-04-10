Require Import Arith.
Require Import Lia.
Require Import List.
Require Import Prog ProgMonad.
Require Import Pred PredCrash.
Require Import Hoare.
Require Import Word.
Require Import AsyncDisk.
Require Import Hashmap.
Require Import Errno.
Require Import ADestructPair DestructVarname.
Set Implicit Arguments.
Hint Extern 1 (exists _, hashmap_subset _ _ _) => try solve_hashmap_subset.
Ltac set_evars :=
  repeat match goal with
              | [ |- context[?e] ] => is_evar e; 
                 match type of e with
                 | prod _ _ => idtac
                 | _ => let H := fresh in set (H := e)
                 end
            end.
Ltac subst_evars :=
  repeat match goal with
              | [ H := ?e |- _ ] => is_evar e; subst H
            end.
Ltac set_evars_in H :=
  repeat match type of H with
              | context[?e] => is_evar e; let E := fresh in set (E := e) in H
            end.
Ltac equate x y :=
  let dummy := constr:(eq_refl x : x = y) in idtac.
Ltac eassign' t :=
  match goal with
  | [ |- context [?x] ] => is_evar x; equate x t
  end.
Tactic Notation "eassign" constr(t) := eassign' t.
Ltac destruct_pairs :=
  repeat (destruct_varnames; simpl in *; try destruct_pair_once).
Lemma eexists_varname_pair : forall A B p,
  (exists (a:VARNAME(anon) * A) (b:VARNAME(anon) * B), p (varname_val, (snd a, snd b)))
  -> (exists (e:VARNAME(any) * (A*B)), p e).
(* hint proof tokens: 40 *)
Proof.
  intros.
  destruct H as [a H].
  destruct H as [b H].
  exists (varname_val, (snd a, snd b)); auto.
Qed.
Lemma eexists_varname_one : forall A p,
  (exists (a : A), p (varname_val, a))
  -> (exists (e : VARNAME(foo) * A), p e).
Proof.
(* original proof tokens: 27 *)
(* generated proof tokens: 27 *)

intros.
destruct H as [a H].
exists (varname_val, a); auto.
Qed.

Ltac eexists_one :=
  match goal with
  | [ |- exists (_ : unit), _ ] => exists tt
  | [ |- exists (_ : VARNAME(vn) * (?TA * ?TB)), _ ] =>
    apply eexists_varname_pair
  | [ |- exists (_ : VARNAME(vn) * ?T), _ ] =>
    let ev := fresh vn in
    evar (ev : T);
    apply eexists_varname_one;
    exists ev;
    unfold ev in *; clear ev
  | [ |- exists (_ : VARNAME(vn) * _ * _), _ ] =>
    apply eexists_pair
  | [ |- exists (_ : (_*_)), _ ] => apply eexists_pair
  | [ |- exists _, _ ] => eexists
  end.
Ltac pred_apply' H := eapply pimpl_apply; [ | exact H ].
Ltac pred_apply := match goal with
  | [ |- _ ?m ] => (has_evar m; fail 1) ||
    match goal with
    | [ H: _ ?m' |- _ ] => unify m m'; pred_apply' H
    end
  | [ |- exists _, _ ] => eexists; pred_apply
  end.
Ltac pred_apply_instantiate := match goal with
  | [ |- _ ?m ] =>
    match goal with
    | [ H: _ ?m' |- _ ] => unify m m'; pred_apply' H
    end
  | [ |- exists _, _ ] => eexists; pred_apply_instantiate
  end.
Ltac pimpl_crash :=
  try match goal with
  | [ |- _ =p=> emp * _ ] => eapply pimpl_trans; [| eapply pimpl_star_emp ]
  end;
  set_evars;
  try match goal with
  | [ H: _ =p=> _ |- _ =p=> ?crash ] => eapply pimpl_trans; [| solve [ eapply H ] ]
  | [ H: forall _, _ =p=> _ |- _ =p=> ?crash ] => eapply pimpl_trans; [| solve [ eapply H ] ]
  end;
  subst_evars.
Definition pred_fold_left AT AEQ V (l : list (@pred AT AEQ V)) : pred :=
  match l with
  | nil => emp
  | a :: t => fold_left sep_star t a
  end.
Definition stars {AT AEQ V} (ps : list (@pred AT AEQ V)) :=
  pred_fold_left ps.
Arguments stars : simpl never.
Ltac sep_imply'' H := eapply pimpl_apply; [ | apply H ].
Ltac sep_imply' m :=
  match goal with
  | [ H : _ m |- _ ] => sep_imply'' H
  | [ H : _ _ m |- _ ] => sep_imply'' H
  | [ H : _ _ _ m |- _ ] => sep_imply'' H
  end.
Ltac sep_imply :=
  match goal with
  | [ |- _ ?m ] => sep_imply' m
  | [ |- _ _ ?m ] => sep_imply' m
  | [ |- _ _ _ ?m ] => sep_imply' m
  end.
Theorem start_normalizing_left : forall AT AEQ V PT (p : @pred AT AEQ V) q ps P,
  p <=p=> (exists (x:PT), stars (ps x) * [[P x]])%pred
  -> ((exists (x:PT), stars (ps x) * stars nil * [[P x]]) =p=> q)
  -> p =p=> q.
(* hint proof tokens: 87 *)
Proof.
  unfold stars; simpl; intros.
  rewrite <- H0.
  rewrite H.
  eapply pimpl_exists_l; intro eP.
  eapply pimpl_exists_r; exists eP.
  eapply pimpl_trans; [apply pimpl_star_emp|].
  eapply pimpl_trans; [apply sep_star_assoc|].
  apply piff_star_r. apply sep_star_comm.
Qed.
Theorem start_normalizing_right : forall AT AEQ V QT (p : @pred AT AEQ V) q qs Q,
  q <=p=> (exists (x:QT), stars (qs x) * [[Q x]])%pred
  -> (p =p=> (exists (x:QT), stars (qs x) * [[Q x]]))
  -> p =p=> q.
(* hint proof tokens: 30 *)
Proof.
  unfold stars; simpl; intros.
  rewrite H0.
  rewrite <- H.
  apply pimpl_refl.
Qed.
Theorem start_normalizing_apply : forall AT AEQ V PT (p : @pred AT AEQ V) ps P m,
  p <=p=> (exists (x:PT), stars (ps x) * [[P x]])%pred
  -> p m
  -> (exists (x:PT), stars (ps x) * [[P x]])%pred m.
Proof.
(* original proof tokens: 9 *)
(* generated proof tokens: 18 *)
unfold piff, pimpl; intros.
apply H; auto.
Qed.

Theorem restart_canceling:
  forall AT AEQ V p (q : @pred AT AEQ V),
  (stars p * stars nil =p=> q) ->
  (stars nil * stars p =p=> q).
(* hint proof tokens: 25 *)
Proof.
  intros; eapply pimpl_trans; [ eapply sep_star_comm | eauto ].
Qed.
Lemma stars_prepend':
  forall AT AEQ V l x,
  fold_left sep_star l x <=p=> x * fold_left sep_star l (@emp AT AEQ V).
(* hint proof tokens: 132 *)
Proof.
  induction l.
  - simpl. intros.
    eapply piff_trans.
    apply emp_star.
    apply sep_star_comm.
  - simpl. intros.
    eapply piff_trans.
    eapply IHl.
    eapply piff_trans.
    eapply sep_star_assoc.
    eapply piff_star_l.
    eapply piff_comm.
    eapply piff_trans.
    eapply IHl.
    eapply piff_comm.
    eapply piff_trans.
    eapply emp_star.
    eapply piff_comm.
    eapply piff_trans.
    eapply sep_star_assoc.
    eapply piff_refl.
Qed.
Lemma stars_prepend:
  forall AT AEQ V l (x : @pred AT AEQ V),
  stars (x :: l) <=p=> x * stars l.
(* hint proof tokens: 149 *)
Proof.
  unfold stars, pred_fold_left; simpl; intros.
  destruct l.
  - simpl; split.
    eapply pimpl_trans; [| eapply sep_star_comm ]. eapply pimpl_star_emp.
    eapply pimpl_trans; [eapply sep_star_comm |]. eapply star_emp_pimpl.
  - eapply piff_trans. apply stars_prepend'.
    eapply piff_star_l.
    simpl.
    eapply piff_trans; [ apply stars_prepend' |].
    eapply piff_trans; [| apply piff_comm; apply stars_prepend' ].
    apply piff_star_r.
    split.
    apply star_emp_pimpl.
    apply pimpl_star_emp.
Qed.
Lemma flatten_default' : forall AT AEQ V (p : @pred AT AEQ V),
  p <=p=> stars (p :: nil).
Proof.
(* original proof tokens: 9 *)

(* No more tactics to try *)
Admitted.

Lemma flatten_default : forall AT AEQ V (p : @pred AT AEQ V),
  p <=p=> exists (x:unit), stars (p :: nil) * [[True]].
Proof.
(* original proof tokens: 66 *)
split; intros.
eapply pimpl_exists_r; eexists.
(* No more tactics to try *)
Admitted.

Lemma flatten_emp' : forall AT AEQ V, (@emp AT AEQ V) <=p=> stars nil.
(* hint proof tokens: 9 *)
Proof.
  firstorder.
Qed.
Lemma flatten_emp : forall AT AEQ V,
  (@emp AT AEQ V) <=p=> exists (x:unit), stars nil * [[True]].
(* hint proof tokens: 62 *)
Proof.
  split.
  - apply pimpl_exists_r; exists tt.
    apply sep_star_lift_r.
    firstorder.
  - apply pimpl_exists_l; intros.
    eapply pimpl_trans; [apply sep_star_lift2and|].
    firstorder.
Qed.
Lemma flatten_star' : forall AT AEQ V (p : @pred AT AEQ V) q ps qs,
  p <=p=> stars ps
  -> q <=p=> stars qs
  -> p * q <=p=> stars (ps ++ qs).
Proof.
(* original proof tokens: 163 *)

(* No more tactics to try *)
Admitted.

Lemma flatten_star : forall AT AEQ V PT QT (p : @pred AT AEQ V) q ps qs P Q,
  p <=p=> (exists (x:PT), stars (ps x) * [[P x]])%pred
  -> q <=p=> (exists (x:QT), stars (qs x) * [[Q x]])%pred
  -> p * q <=p=> exists (x:PT*QT), stars (ps (fst x) ++ qs (snd x)) * [[P (fst x) /\ Q (snd x)]].
Proof.
(* original proof tokens: 406 *)
split; intros.
(* No more tactics to try *)
Admitted.

Lemma flatten_exists : forall AT AEQ V T PT (p : _ -> @pred AT AEQ V) ps P,
  (forall ( a : T ), (p a <=p=> exists ( x : PT ), stars (ps a x) * [[ P a x ]]))
  -> (exists ( a : T ), p a) <=p=>
      (exists ( x : ( (VARNAME(dummy)*T) * PT ) ),
       stars (ps (snd (fst x)) (snd x)) *
       [[ P (snd (fst x)) (snd x) ]]).
Proof.
(* original proof tokens: 127 *)
split; intros.
eapply pimpl_exists_l; intro.
eapply pimpl_exists_r; eauto.
eapply pimpl_exists_l; intros.
eapply pimpl_exists_r; eauto.
eapply pimpl_exists_l; intros.
eapply pimpl_exists_l; intro.
eapply pimpl_exists_r; eauto.
eapply pimpl_exists_l; intros.
eapply pimpl_exists_l; eauto.
eapply pimpl_exists_l; intros.
(* Reached max number of model calls *)
Admitted.

Lemma flatten_lift_empty: forall AT AEQ V P,
  [[P]] <=p=> (exists (x:unit), stars (@nil (@pred AT AEQ V)) * [[P]]).
(* hint proof tokens: 37 *)
Proof.
  split.
  - apply pimpl_exists_r. exists tt. apply emp_star.
  - apply pimpl_exists_l; intros. apply emp_star.
Qed.
Ltac flatten_assign_name good_name :=
  match goal with
  | [ |- (exists lv : (VARNAME(dummy) * ?T) * ?PT, ?body) <=p=> _ ] =>
    set (LHS := (exists lv : (VARNAME(good_name) * T) * PT, body)%pred);
    unfold LHS in *; clear LHS;
    apply piff_refl
  end.
Ltac flatten :=
  repeat match goal with
  | [ |- emp <=p=> _ ] => apply flatten_emp
  | [ |- _ * _ <=p=> _ ] =>
    eapply piff_trans; [ apply flatten_star | apply piff_refl ]
  | [ |- (exists (varname : _), _)%pred <=p=> _ ] =>
    eapply piff_trans; [ apply flatten_exists | flatten_assign_name varname ]; intros ?varname
  | [ |- [[_]] <=p=> _ ] =>
    eapply piff_trans; [ apply flatten_lift_empty | apply piff_refl ]
  | _ => apply flatten_default
  end.
Definition okToUnify {AT AEQ V} (p1 p2 : @pred AT AEQ V) := p1 = p2.
Hint Extern 0 (okToUnify (?p |-> _) (?p |-> _)) => constructor : okToUnify.
Hint Extern 0 (okToUnify (?p |+> _) (?p |+> _)) => constructor : okToUnify.
Hint Extern 0 (okToUnify ?a ?a) => constructor : okToUnify.
Inductive pick {AT AEQ V} (lhs : pred) : list (@pred AT AEQ V) -> list pred -> Prop :=
| PickFirst : forall p ps,
  okToUnify lhs p
  -> pick lhs (p :: ps) ps
| PickLater : forall p ps ps',
  pick lhs ps ps'
  -> pick lhs (p :: ps) (p :: ps').
Lemma pick_later_and : forall AT AEQ V (p : @pred AT AEQ V) p' ps ps' (a b : @pred AT AEQ V),
  pick p ps ps' /\ (a =p=> b)
  -> pick p (p' :: ps) (p' :: ps') /\ (a =p=> b).
(* hint proof tokens: 14 *)
Proof.
  intuition; apply PickLater; auto.
Qed.
Lemma crash_xform_okToUnify : forall (P Q: rawpred),
  okToUnify P Q -> okToUnify (crash_xform P) (crash_xform Q).
Proof.
(* original proof tokens: 19 *)
(* generated proof tokens: 25 *)

intros.
unfold okToUnify in *.
rewrite H.
reflexivity.
Qed.

Ltac pick := solve [ repeat 
          ((apply PickFirst;
            solve [ try apply crash_xform_okToUnify; trivial with okToUnify ]
           ) || apply PickLater) ].
Theorem imply_one : forall AT AEQ V qs qs' (p : @pred AT AEQ V) q ps F,
  (pick q qs qs' /\ (p =p=> q))
  -> (stars ps * F =p=> stars qs')
  -> stars (p :: ps) * F =p=> stars qs.
Proof.
(* original proof tokens: 219 *)

(* No more tactics to try *)
Admitted.

Theorem cancel_one : forall AT AEQ V qs qs' (p : @pred AT AEQ V) ps F,
  pick p qs qs'
  -> (stars ps * F =p=> stars qs')
  -> stars (p :: ps) * F =p=> stars qs.
Proof.
(* original proof tokens: 17 *)

(* No more tactics to try *)
Admitted.

Ltac cancel_one := eapply cancel_one; [ pick | ].
Theorem delay_one : forall AT AEQ V (p : @pred AT AEQ V) ps q qs,
  (stars ps * stars (p :: qs) =p=> q)
  -> stars (p :: ps) * stars qs =p=> q.
Proof.
(* original proof tokens: 124 *)

(* No more tactics to try *)
Admitted.

Ltac delay_one := apply delay_one.
Lemma and_imp:
  forall (A B C:Prop),
  (A -> B)
  -> (A /\ C)
  -> (B /\ C).
Proof.
(* original proof tokens: 9 *)

(* No more tactics to try *)
Admitted.

Lemma finish_frame : forall AT AEQ V (p : @pred AT AEQ V),
  stars nil * p =p=> p.
(* hint proof tokens: 14 *)
Proof.
  intros. apply star_emp_pimpl.
Qed.
Ltac cancel' := repeat (cancel_one || delay_one);
                try solve [ unfold stars at 2 3; simpl;
                  match goal with
                  | [ |- stars nil * ?P =p=> ?Q] =>
                    match P with
                    | context[sep_star] => match Q with context[sep_star] => fail 2 end
                    | _ => idtac
                    end;
                    simple apply finish_frame
                  end ].
Theorem split_or_one : forall AT AEQ V (q : @pred AT AEQ V) pa pb ps F,
  stars (pa :: ps) * F =p=> q
  -> stars (pb :: ps) * F =p=> q
  -> stars ((pa \/ pb) :: ps) * F =p=> q.
(* hint proof tokens: 177 *)
Proof.
  intros.
  eapply pimpl_trans. eapply piff_star_r. eapply piff_comm. apply stars_prepend.
  eapply pimpl_trans. eapply sep_star_assoc.
  eapply pimpl_trans. eapply sep_star_comm.
  eapply pimpl_trans. eapply sep_star_or_distr.
  apply pimpl_or_l.
  - eapply pimpl_trans. eapply sep_star_comm.
    eapply pimpl_trans. eapply sep_star_assoc.
    eapply pimpl_trans. eapply piff_star_r. apply stars_prepend.
    eauto.
  - eapply pimpl_trans. eapply sep_star_comm.
    eapply pimpl_trans. eapply sep_star_assoc.
    eapply pimpl_trans. eapply piff_star_r. apply stars_prepend.
    eauto.
Qed.
Theorem exists_one : forall AT AEQ V T p ps F (q : @pred AT AEQ V),
  (forall a:T, stars (p a :: ps) * F =p=> q)
  -> stars ((exists a:T, p a) :: ps) * F =p=> q.
(* hint proof tokens: 126 *)
Proof.
  intros.
  eapply pimpl_trans. eapply piff_star_r. eapply piff_comm. apply stars_prepend.
  eapply pimpl_trans. eapply sep_star_assoc.
  eapply pimpl_exists_l_star.
  eapply pimpl_exists_l; intros.
  eapply pimpl_trans; [| eauto ].
  eapply pimpl_trans. eapply sep_star_assoc.
  eapply pimpl_sep_star; [| eapply pimpl_refl ].
  eapply pimpl_trans. apply stars_prepend.
  apply pimpl_refl.
Qed.
Ltac split_one := match goal with
                  | [ |- stars ((_ \/ _) :: _) * _ =p=> _ ]
                    => apply split_or_one
                  | [ |- stars ((exists _, _)%pred :: _) * _ =p=> _ ]
                    => apply exists_one; intro
                  end.
Ltac split_or_l := repeat ( (repeat split_one) ; delay_one );
                   apply restart_canceling.
Lemma stars_or_left: forall AT AEQ V (a b c : @pred AT AEQ V),
  (a =p=> stars (b :: nil))
  -> (a =p=> stars ((b \/ c) :: nil)).
(* hint proof tokens: 9 *)
Proof.
  firstorder.
Qed.
Lemma stars_or_right: forall AT AEQ V (a b c : @pred AT AEQ V),
  (a =p=> stars (c :: nil))
  -> (a =p=> stars ((b \/ c) :: nil)).
Proof.
(* original proof tokens: 9 *)

(* No more tactics to try *)
Admitted.

Ltac destruct_type T :=
  match goal with
  | [ H: T |- _ ] => destruct H
  end.
Ltac destruct_lift' H :=
  match type of H with
  | (?a /\ ?b) =>
    let Hlift0:=fresh in
    let Hlift1:=fresh in
    destruct H as [Hlift0 Hlift1]; destruct_lift' Hlift0; destruct_lift' Hlift1
  | ((sep_star _ _) _) =>
    eapply start_normalizing_apply in H; [| flatten ];
    let H1:=fresh in
    let H2:=fresh in
    unfold stars in H; simpl in H; destruct H as [? H1];
    apply sep_star_lift_apply in H1; destruct H1 as [? H2];
    destruct_lift' H2
  | ((and _ _) _) =>
    eapply start_normalizing_apply in H; [| flatten ];
    let H1:=fresh in
    let H2:=fresh in
    unfold stars in H; simpl in H; destruct H as [? H1];
    apply sep_star_lift_apply in H1; destruct H1 as [? H2];
    destruct_lift' H2
  | ((or _ _) _) =>
    eapply start_normalizing_apply in H; [| flatten ];
    let H1:=fresh in
    let H2:=fresh in
    unfold stars in H; simpl in H; destruct H as [? H1];
    apply sep_star_lift_apply in H1; destruct H1 as [? H2];
    destruct_lift' H2
  | ((exists _, _)%pred _) =>
    eapply start_normalizing_apply in H; [| flatten ];
    let H1:=fresh in
    let H2:=fresh in
    unfold stars in H; simpl in H; destruct H as [? H1];
    apply sep_star_lift_apply in H1; destruct H1 as [? H2];
    destruct_lift' H2
  | _ => idtac
  end.
Ltac destruct_lift H :=
  destruct_lift' H;
  destruct_pairs;
  simpl in *;
  repeat destruct_type True;
  repeat destruct_type unit;
  simpl in *;
  repeat clear_varname.
Ltac destruct_lifts := try progress match goal with 
  | [ H : sep_star _ _  _ |- _ ] => destruct_lift H
end.
Ltac norm'l := eapply start_normalizing_left; [ flatten | ];
               eapply pimpl_exists_l; intros;
               apply sep_star_lift_l; let Hlift:=fresh in intro Hlift;
               destruct_lift Hlift.
Ltac norm'r := eapply start_normalizing_right; [ flatten | ];
               eapply pimpl_exists_r; repeat eexists_one;
               apply sep_star_lift_r; apply pimpl_and_lift;
               simpl in *.
Create HintDb false_precondition_hint.
Ltac destruct_pair_eq :=
    match goal with
    | [ H : (_ , _) = (_, _) |- _ ] => inversion H; clear H
    end.
Ltac norml := unfold pair_args_helper;
             norm'l; repeat deex; repeat destruct_type valuset;
             repeat destruct_pair_eq;
             
             repeat ( split_or_l; [ | | .. ]; split_or_l; unfold stars; simpl; norm'l ).
Ltac norm := norml;
             solve [ exfalso ; auto with false_precondition_hint ] ||
             norm'r.
Ltac inv_option_eq' := repeat match goal with
  | [ H: None = None |- _ ] => clear H
  | [ H: None = Some _ |- _ ] => inversion H
  | [ H: Some _ = None |- _ ] => inversion H
  | [ H: Some _ = Some _ |- _ ] => inversion H; clear H
  | [ H: OK _ = OK _ |- _ ] => inversion H; clear H
  | [ H: Err _ = Err _ |- _ ] => inversion H; clear H
  | [ H: OK _ = Err _ |- _ ] => inversion H
  | [ H: Err _ = OK _ |- _ ] => inversion H
  | [ H: (_, _) = (_, _) |- _ ] => inversion H; clear H
  | [ H: isError (OK _) |- _ ] => inversion H
  end.
Ltac inv_option_eq := try ((progress inv_option_eq'); subst; eauto).
Tactic Notation "denote" open_constr(pattern) "as" ident(n) :=
  match goal with | [ H: context [ pattern ] |- _ ] => rename H into n end.
Tactic Notation "denote!" open_constr(pattern) "as" ident(n) :=
  match goal with | [ H: pattern |- _ ] => rename H into n end.
Tactic Notation "substl" :=
  subst; repeat match goal with
  | [ H : ?l = ?r |- _ ] => is_var l;
    match goal with
     | [ |- context [ r ] ] => idtac
     | _ => setoid_rewrite H
    end
  end.
Tactic Notation "substl" constr(term) "at" integer_list(pos) :=
  match goal with
  | [ H : term = _  |- _ ] => setoid_rewrite H at pos
  | [ H : _ = term  |- _ ] => setoid_rewrite <- H at pos
  end.
Tactic Notation "substl" constr(term) :=
  match goal with
  | [ H : term = _  |- _ ] => setoid_rewrite H
  | [ H : _ = term  |- _ ] => setoid_rewrite <- H
  end.
Ltac safecancel :=
  intros;
  unfold stars; simpl; try subst;
  pimpl_crash;
  norm;
  try match goal with
      | [ |- _ =p=> stars ((_ \/ _) :: nil) ] =>
        solve [ apply stars_or_left; safecancel
              | apply stars_or_right; safecancel ]
      | [ |- _ =p=> _ ] => cancel'
      end;
  set_evars; intuition; subst_evars;
  try ( pred_apply; safecancel );
  try congruence;
  unfold stars; simpl; inv_option_eq;
  try match goal with
  | [ |- emp * _ =p=> _ ] => eapply pimpl_trans; [ apply star_emp_pimpl |]
  end.
Ltac cancel_with' t intuition_t :=
  intros;
  unfold stars; simpl; try subst;
  pimpl_crash;
  norm;
  try match goal with
      | [ |- _ =p=> stars ((_ \/ _) :: nil) ] =>
        solve [ apply stars_or_left; cancel_with' t intuition_t
              | apply stars_or_right; cancel_with' t intuition_t ]
      | [ |- _ =p=> _ ] => cancel'
      end;
  intuition ( intuition_t;
    try ( pred_apply; cancel_with' t intuition_t);
    try congruence;
    try t;
    unfold stars; simpl; inv_option_eq;
    try match goal with
    | [ |- emp * _ =p=> _ ] => eapply pimpl_trans; [ apply star_emp_pimpl |]
    end ).
Ltac CRelationClasses.solve_crelation ::=
  match goal with
  | [ |- ?R ?x ?x ] => reflexivity
  | [ |- ?R ?y ?x ] =>
    match goal with
    | [ H : R x y |- _ ] => symmetry ; exact H
    end
  end.
Ltac RelationClasses.solve_relation ::= match goal with
  | |- ?R ?x ?x => reflexivity
  | |- ?R ?y ?x => match goal with
    | [ H:R x y |- _ ] => symmetry; exact H
    end
  end.
Ltac cancel_with t := cancel_with' t ltac:(auto with *).
Ltac cancel := cancel_with idtac.
Ltac cancel_exact := repeat match goal with 
  | [ |- (?a =p=> ?a)%pred ] =>
        eapply pimpl_refl
  | [ |- (_ * ?a =p=> _ * ?a)%pred ] =>
        eapply pimpl_sep_star; [ | eapply pimpl_refl]
  | [ |- ( ?a * _ =p=> ?a * _)%pred ] =>
        eapply pimpl_sep_star; [ eapply pimpl_refl | ]
  | [ |- ( ?a * _ =p=> _ * ?a)%pred ] =>
        rewrite sep_star_comm1
  | [ |- ( (?a * _) * _ =p=> ?a * _)%pred ] =>
        rewrite sep_star_assoc_1
end.
Ltac cancel_by H :=
  eapply pimpl_ext; [ eapply H | cancel | cancel ].
Theorem nop_ok :
  forall T A v (rx : A -> prog T),
  {{ fun vm hm done_ crash_ => exists F, F * [[ forall r_,
    {{ fun vm' hm' done' crash' => (fun r => F * [[ r = v ]]) r_ *
                           [[ hm = hm' ]] *
                           [[ vm = vm' ]] *
                           [[ done' = done_ ]] * [[ crash' = crash_ ]]}}
     rx r_ ]] * [[ F =p=> crash_ hm]] }} rx v.
Proof.
(* original proof tokens: 42 *)

(* No more tactics to try *)
Admitted.

Ltac autorewrite_fast_goal :=
  set_evars; (rewrite_strat (topdown (hints core))); subst_evars;
  try autorewrite_fast_goal.
Ltac autorewrite_fast :=
  match goal with
  | [ H: _ |- _ ] =>
    set_evars_in H; (rewrite_strat (topdown (hints core)) in H); subst_evars;
    [ try autorewrite_fast | try autorewrite_fast_goal .. ]
  | [ |- _ ] => autorewrite_fast_goal
  end.
Ltac destruct_branch :=
  match goal with
  | [ |- {{ _ }} Bind (match ?v with | Some _ => _ | None => _ end) _ ] => destruct v eqn:?
  | [ |- {{ _ }} Bind (match ?v with | None => _ | Some _ => _ end) _ ] => destruct v eqn:?
  | [ |- {{ _ }} Bind (if ?v then _ else _) _ ] => destruct v eqn:?
  | [ |- {{ _ }} Bind (let '_ := ?v in _) _ ] => destruct v eqn:?
  end.
Ltac prestep :=
  intros;
  try autounfold with hoare_unfold in *;
  repeat destruct_pair_once;
  try cancel;
  repeat (destruct_branch || monad_simpl_one);
  
  ((eapply pimpl_ok2; [ solve [ eauto with prog ] | ])
   || (eapply pimpl_ok2_cont; [ solve [ eauto with prog ] | | ])
   || (eapply pimpl_ok3; [ solve [ eauto with prog ] | ])
   || (eapply pimpl_ok3_cont; [ solve [ eauto with prog ] | | ])
   || (eapply pimpl_ok2; [
        match goal with
        | [ |- {{ _ }} ?rx _ ] => is_var rx
        end; solve [ eapply nop_ok ] | ]));
  intros; try subst;
  repeat destruct_type unit;  
  try autounfold with hoare_unfold in *; eauto.
Ltac poststep t :=
  let tac := match goal with
  | [ |- corr2 _ _ ] => idtac
  | _ => t
  end in
  intuition tac;
  try lia;
  try congruence;
  try tac.
Ltac safestep :=
    prestep; safecancel;
    set_evars; poststep auto; subst_evars.
Ltac or_r := apply pimpl_or_r; right.
Ltac or_l := apply pimpl_or_r; left.
Tactic Notation "step" "using" tactic(t) "with" ident(db) "in" "*" :=
  prestep;
  try ( cancel_with t ; try ( autorewrite with db in * |-; cancel_with t ) );
  poststep t.
Tactic Notation "step" "using" tactic(t) "with" ident(db) :=
  prestep;
  try ( cancel_with t ; try ( autorewrite with db; cancel_with t ) );
  poststep t.
Tactic Notation "step" "using" tactic(t) "with" "intuition" tactic(intuition_t) :=
  prestep;
  try (cancel_with' t intuition_t; try cancel_with' t intuition_t);
  poststep t.
Tactic Notation "step" "using" tactic(t) :=
  prestep;
  try (cancel_with t; try cancel_with t);
  poststep t.
Ltac step := step using eauto.
Ltac step_idtac := step using idtac with intuition idtac.
Tactic Notation "hoare" "using" tactic(t) "with" ident(db) "in" "*" :=
  repeat (step using t with db in *).
Tactic Notation "hoare" "using" tactic(t) "with" ident(db) :=
  repeat (step using t with db).
Tactic Notation "hoare" "using" tactic(t) :=
  repeat (step using t).
Ltac hoare := hoare using eauto.
Ltac xform_deex_r :=
    match goal with
    | [ |- pimpl _ (crash_xform (exis _)) ] =>
            rewrite crash_xform_exists_comm;
            apply pimpl_exists_r; eexists
    end.
Ltac xform_deex_l :=
    norml; unfold stars; simpl;
    try rewrite -> crash_xform_exists_comm;
    try (rewrite sep_star_comm, star_emp_pimpl);
    try match goal with
    | [ |- pimpl (exis _) _ ] => apply pimpl_exists_l; intro
    end.
Ltac xform_dist :=
  rewrite crash_xform_sep_star_dist ||
  rewrite crash_xform_or_dist ||
  rewrite crash_xform_lift_empty ||
  rewrite crash_invariant_emp ||
  rewrite <- crash_invariant_emp_r.
Ltac xform_norml :=
  repeat (xform_deex_l || xform_dist).
Ltac xform_normr :=
  repeat (xform_deex_r || xform_dist).
Ltac xform_norm :=
  xform_norml; xform_normr.
Ltac xcrash_rewrite :=
  match goal with
  | [ H : forall rc hm, (crash_xform rc =p=> crash_xform ?x) -> _ =p=> ?c hm |- _ =p=> ?c ?hm] =>
      eapply pimpl_trans; [ | eapply H ]; cancel; subst
  | [ H : crash_xform ?rc =p=> _ |- crash_xform ?rc =p=> _ ] => rewrite H
  end.
Ltac xcrash := subst; repeat xcrash_rewrite;
               xform_norm; cancel; xform_normr; cancel.
