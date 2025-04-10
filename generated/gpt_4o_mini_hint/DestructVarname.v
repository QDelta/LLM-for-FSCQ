Require Import AsyncDisk.
Set Implicit Arguments.
Definition varname_type (_ : unit) := unit.
Definition varname_val (_ : unit) := tt.
Notation "'VARNAME' ( varname )" := (forall (varname : unit), varname_type varname).
Ltac clear_varname :=
  match goal with
  | [ H: VARNAME(vn) |- _ ] => clear H
  end.
Ltac destruct_prod :=
  match goal with
  | [ v: valuset |- _ ] =>
    let v0 := fresh v "_cur" in
    let v1 := fresh v "_old" in
    destruct v as [v0 v1]
  | [ H: (VARNAME(vn) * ?b)%type |- _ ] => destruct H as [? ?vn]
  | [ H: (?a * ?b)%type |- _ ] => destruct H
  end.
Lemma eexists_pair: forall A B p,
  (exists (a:A) (b:B), p (a, b))
  -> (exists (e:A*B), p e).
Proof.
(* original proof tokens: 33 *)

(* No more tactics to try *)
Admitted.

Theorem destruct_varname1_0 : forall AN A (p : AN * A),
  exists an a, p = (an, a).
(* hint proof tokens: 14 *)
Proof.
  intros; destruct p; eauto.
Qed.
Theorem destruct_varname1_1 : forall AN A B (p : AN * A * B ),
  exists an a b, p = (an, a, b).
(* hint proof tokens: 17 *)
Proof.
  intros; do 2 destruct p; eauto.
Qed.
Theorem destruct_varname1_2 : forall AN A B C (p : AN * A * B * C),
  exists an a b c, p = (an, a, b, c).
Proof.
(* original proof tokens: 16 *)
destruct p.
eexists.
eexists.
eexists.
eexists.
(* No more tactics to try *)
Admitted.

Theorem destruct_varname1_4 : forall AN A B C D E (p : AN * A * B * C * D * E),
  exists an a b c d e, p = (an, a, b, c, d, e).
(* hint proof tokens: 16 *)
Proof.
  intros; repeat destruct_prod; repeat eexists.
Qed.
Theorem destruct_varname1_8 : forall AN A B C D E F G (p : AN * A * B * C * D * E * F * G),
  exists an a b c d e f g, p = (an, a, b, c, d, e, f, g).
Proof.
(* original proof tokens: 16 *)
(* generated proof tokens: 26 *)

intros AN A B C D E F G p; repeat destruct_prod; repeat eexists.
Qed.

Theorem destruct_varname2 : forall AN BN A B C (p : (AN * A) * ((BN * B) * C) ),
  exists an a bn b c, p = ((an, a), ((bn, b), c)).
Proof.
(* original proof tokens: 17 *)
eexists. destruct p. destruct p0. simpl. auto.
eexists.
eexists. destruct p, p0. simpl. auto.
eexists. eexists. eauto.
(* No more tactics to try *)
Admitted.

Ltac destruct_varname1 :=
  match goal with
  | [ H : VARNAME (_) * _ |- _ ] => let Hx := fresh in
      pose proof (destruct_varname1_0 H) as Hx;
      match type of Hx with
      | exists (_ : VARNAME (vn)) _, _ = _ =>
        destruct Hx as [? [?vn Hx] ]
      end
  | [ H : VARNAME (_) * _ * _ |- _ ] => let Hx := fresh in
      pose proof (destruct_varname1_1 H) as Hx;
      match type of Hx with
      | exists (_ : VARNAME (vn)) _ _, _ = _ =>
        destruct Hx as [? [?vn [? Hx] ] ]
      end
  | [ H : VARNAME (_) * _ * _ * _ |- _ ] => let Hx := fresh in
      pose proof (destruct_varname1_2 H) as Hx;
      match type of Hx with
      | exists (_ : VARNAME (vn)) _ _ _, _ = _ =>
        destruct Hx as [? [?vn [? [? Hx] ] ] ]
      end
  | [ H : VARNAME (_) * _ * _ * _ * _ * _ |- _ ] => let Hx := fresh in
      pose proof (destruct_varname1_4 H) as Hx;
      match type of Hx with
      | exists (_ : VARNAME (vn)) _ _ _ _ _, _ = _ =>
        destruct Hx as [? [?vn [? [? [? [? Hx] ] ] ] ] ]
      end
  | [ H : VARNAME (_) * _ * _ * _ * _ * _ * _ * _ |- _ ] => let Hx := fresh in
      pose proof (destruct_varname1_8 H) as Hx;
      match type of Hx with
      | exists (_ : VARNAME (vn)) _ _ _ _ _ _ _, _ = _ =>
        destruct Hx as [? [?vn [? [? [? [? [? [? Hx] ] ] ] ] ] ] ]
      end
  end.
Ltac destruct_varname2 :=
  match goal with
  | [ H : VARNAME (_) * _ * ((VARNAME (_) * _) * _) |- _ ] => let Hx := fresh in
      pose proof (destruct_varname2 H) as Hx;
      match type of Hx with
      | exists (_ : VARNAME (vn1)) _ (_ : VARNAME (vn2)) _ _, _ = _ =>
        destruct Hx as [? [?vn1 [? [?vn2 [? Hx] ] ] ] ]
      end
  end.
Theorem destruct_varname4 : forall XN1 X1 XN2 X2 XN3 X3 XN4 X4 X5 
				(p : (XN1 * X1) * ((XN2 * X2) * ((XN3 * X3) * ((XN4 * X4) * X5)))),
	exists xn1 x1 xn2 x2 xn3 x3 xn4 x4 x5, p = ((xn1, x1), ((xn2, x2), ((xn3, x3), ((xn4, x4), x5)))).
Proof.
(* original proof tokens: 16 *)
eexists; destruct p.
eexists; destruct p.
eexists; destruct p0.
eexists; destruct p.
eexists; destruct p0.
eexists.
eexists.
eexists.
eexists; destruct p.
(* Reached max number of model calls *)
Admitted.

Ltac destruct_varname4 :=
	match goal with
	| [ H : VARNAME (_) * _ * (VARNAME (_) * _ * (VARNAME (_) * _ * ((VARNAME (_) * _) * _))) |- _ ] =>
		let Hx := fresh in
		pose proof (destruct_varname4 H) as Hx;
		match type of Hx with
		| exists (_ : VARNAME (vn1)) _ (_ : VARNAME (vn2)) _ (_ : VARNAME (vn3)) _ (_ : VARNAME (vn4)) _ _ , _ = _ =>
			destruct Hx as [? [?vn1 [? [?vn2 [? [?vn3 [? [?vn4 [? Hx] ] ] ] ] ] ] ] ]
		end
	end.
Theorem destruct_varname6 : forall XN1 X1 XN2 X2 XN3 X3 XN4 X4 XN5 X5 XN6 X6 X7 
				(p : (XN1 * X1) * ((XN2 * X2) * ((XN3 * X3) * ((XN4 * X4) * ((XN5 * X5) * ((XN6 * X6) * X7)))))),
	exists xn1 x1 xn2 x2 xn3 x3 xn4 x4 xn5 x5 xn6 x6 x7, p = ((xn1, x1), ((xn2, x2), ((xn3, x3), ((xn4, x4), ((xn5, x5), ((xn6, x6), x7)))))).
Proof.
(* original proof tokens: 16 *)

(* No more tactics to try *)
Admitted.

Ltac destruct_varname6 :=
	match goal with
	| [ H : VARNAME (_) * _ * (VARNAME (_) * _ * (VARNAME (_) * _ * (VARNAME (_) * _ * (VARNAME (_) * _ * ((VARNAME (_) * _) * _))))) |- _ ] =>
		let Hx := fresh in
		pose proof (destruct_varname6 H) as Hx;
		match type of Hx with
		| exists (_ : VARNAME (vn1)) _ (_ : VARNAME (vn2)) _ (_ : VARNAME (vn3)) _ (_ : VARNAME (vn4)) _ (_ : VARNAME (vn5)) _ (_ : VARNAME (vn6)) _ _ , _ = _ =>
			destruct Hx as [? [?vn1 [? [?vn2 [? [?vn3 [? [?vn4 [? [?vn5 [? [?vn6 [? Hx] ] ] ] ] ] ] ] ] ] ] ] ]
		end
	end.
Theorem destruct_varname8 : forall XN1 X1 XN2 X2 XN3 X3 XN4 X4 XN5 X5 XN6 X6 XN7 X7 XN8 X8 X9 
				(p : (XN1 * X1) * ((XN2 * X2) * ((XN3 * X3) * ((XN4 * X4) * ((XN5 * X5) * ((XN6 * X6) * ((XN7 * X7) * ((XN8 * X8) * X9)))))))),
	exists xn1 x1 xn2 x2 xn3 x3 xn4 x4 xn5 x5 xn6 x6 xn7 x7 xn8 x8 x9, p = ((xn1, x1), ((xn2, x2), ((xn3, x3), ((xn4, x4), ((xn5, x5), ((xn6, x6), ((xn7, x7), ((xn8, x8), x9)))))))).
Proof.
(* original proof tokens: 16 *)

(* No more tactics to try *)
Admitted.

Ltac destruct_varname8 :=
	match goal with
	| [ H : VARNAME (_) * _ * (VARNAME (_) * _ * (VARNAME (_) * _ * (VARNAME (_) * _ * (VARNAME (_) * _ * (VARNAME (_) * _ * (VARNAME (_) * _ * ((VARNAME (_) * _) * _))))))) |- _ ] =>
		let Hx := fresh in
		pose proof (destruct_varname8 H) as Hx;
		match type of Hx with
		| exists (_ : VARNAME (vn1)) _ (_ : VARNAME (vn2)) _ (_ : VARNAME (vn3)) _ (_ : VARNAME (vn4)) _ (_ : VARNAME (vn5)) _ (_ : VARNAME (vn6)) _ (_ : VARNAME (vn7)) _ (_ : VARNAME (vn8)) _ _ , _ = _ =>
			destruct Hx as [? [?vn1 [? [?vn2 [? [?vn3 [? [?vn4 [? [?vn5 [? [?vn6 [? [?vn7 [? [?vn8 [? Hx] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ]
		end
	end.
Theorem destruct_varname10 : forall XN1 X1 XN2 X2 XN3 X3 XN4 X4 XN5 X5 XN6 X6 XN7 X7 XN8 X8 XN9 X9 XN10 X10 X11 
				(p : (XN1 * X1) * ((XN2 * X2) * ((XN3 * X3) * ((XN4 * X4) * ((XN5 * X5) * ((XN6 * X6) * ((XN7 * X7) * ((XN8 * X8) * ((XN9 * X9) * ((XN10 * X10) * X11)))))))))),
	exists xn1 x1 xn2 x2 xn3 x3 xn4 x4 xn5 x5 xn6 x6 xn7 x7 xn8 x8 xn9 x9 xn10 x10 x11, p = ((xn1, x1), ((xn2, x2), ((xn3, x3), ((xn4, x4), ((xn5, x5), ((xn6, x6), ((xn7, x7), ((xn8, x8), ((xn9, x9), ((xn10, x10), x11)))))))))).
(* hint proof tokens: 16 *)
Proof. intros. repeat destruct_prod. repeat eexists. Qed.
Ltac destruct_varname10 :=
	match goal with
	| [ H : VARNAME (_) * _ * (VARNAME (_) * _ * (VARNAME (_) * _ * (VARNAME (_) * _ * (VARNAME (_) * _ * (VARNAME (_) * _ * (VARNAME (_) * _ * (VARNAME (_) * _ * (VARNAME (_) * _ * ((VARNAME (_) * _) * _))))))))) |- _ ] =>
		let Hx := fresh in
		pose proof (destruct_varname10 H) as Hx;
		match type of Hx with
		| exists (_ : VARNAME (vn1)) _ (_ : VARNAME (vn2)) _ (_ : VARNAME (vn3)) _ (_ : VARNAME (vn4)) _ (_ : VARNAME (vn5)) _ (_ : VARNAME (vn6)) _ (_ : VARNAME (vn7)) _ (_ : VARNAME (vn8)) _ (_ : VARNAME (vn9)) _ (_ : VARNAME (vn10)) _ _ , _ = _ =>
			destruct Hx as [? [?vn1 [? [?vn2 [? [?vn3 [? [?vn4 [? [?vn5 [? [?vn6 [? [?vn7 [? [?vn8 [? [?vn9 [? [?vn10 [? Hx] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ]
		end
	end.
Theorem destruct_varname12 : forall XN1 X1 XN2 X2 XN3 X3 XN4 X4 XN5 X5 XN6 X6 XN7 X7 XN8 X8 XN9 X9 XN10 X10 XN11 X11 XN12 X12 X13 
				(p : (XN1 * X1) * ((XN2 * X2) * ((XN3 * X3) * ((XN4 * X4) * ((XN5 * X5) * ((XN6 * X6) * ((XN7 * X7) * ((XN8 * X8) * ((XN9 * X9) * ((XN10 * X10) * ((XN11 * X11) * ((XN12 * X12) * X13)))))))))))),
	exists xn1 x1 xn2 x2 xn3 x3 xn4 x4 xn5 x5 xn6 x6 xn7 x7 xn8 x8 xn9 x9 xn10 x10 xn11 x11 xn12 x12 x13, p = ((xn1, x1), ((xn2, x2), ((xn3, x3), ((xn4, x4), ((xn5, x5), ((xn6, x6), ((xn7, x7), ((xn8, x8), ((xn9, x9), ((xn10, x10), ((xn11, x11), ((xn12, x12), x13)))))))))))).
(* hint proof tokens: 16 *)
Proof. intros. repeat destruct_prod. repeat eexists. Qed.
Ltac destruct_varname12 :=
	match goal with
	| [ H : VARNAME (_) * _ * (VARNAME (_) * _ * (VARNAME (_) * _ * (VARNAME (_) * _ * (VARNAME (_) * _ * (VARNAME (_) * _ * (VARNAME (_) * _ * (VARNAME (_) * _ * (VARNAME (_) * _ * (VARNAME (_) * _ * (VARNAME (_) * _ * ((VARNAME (_) * _) * _))))))))))) |- _ ] =>
		let Hx := fresh in
		pose proof (destruct_varname12 H) as Hx;
		match type of Hx with
		| exists (_ : VARNAME (vn1)) _ (_ : VARNAME (vn2)) _ (_ : VARNAME (vn3)) _ (_ : VARNAME (vn4)) _ (_ : VARNAME (vn5)) _ (_ : VARNAME (vn6)) _ (_ : VARNAME (vn7)) _ (_ : VARNAME (vn8)) _ (_ : VARNAME (vn9)) _ (_ : VARNAME (vn10)) _ (_ : VARNAME (vn11)) _ (_ : VARNAME (vn12)) _ _ , _ = _ =>
			destruct Hx as [? [?vn1 [? [?vn2 [? [?vn3 [? [?vn4 [? [?vn5 [? [?vn6 [? [?vn7 [? [?vn8 [? [?vn9 [? [?vn10 [? [?vn11 [? [?vn12 [? Hx] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ]
		end
	end.
Theorem destruct_varname14 : forall XN1 X1 XN2 X2 XN3 X3 XN4 X4 XN5 X5 XN6 X6 XN7 X7 XN8 X8 XN9 X9 XN10 X10 XN11 X11 XN12 X12 XN13 X13 XN14 X14 X15 
				(p : (XN1 * X1) * ((XN2 * X2) * ((XN3 * X3) * ((XN4 * X4) * ((XN5 * X5) * ((XN6 * X6) * ((XN7 * X7) * ((XN8 * X8) * ((XN9 * X9) * ((XN10 * X10) * ((XN11 * X11) * ((XN12 * X12) * ((XN13 * X13) * ((XN14 * X14) * X15)))))))))))))),
	exists xn1 x1 xn2 x2 xn3 x3 xn4 x4 xn5 x5 xn6 x6 xn7 x7 xn8 x8 xn9 x9 xn10 x10 xn11 x11 xn12 x12 xn13 x13 xn14 x14 x15, p = ((xn1, x1), ((xn2, x2), ((xn3, x3), ((xn4, x4), ((xn5, x5), ((xn6, x6), ((xn7, x7), ((xn8, x8), ((xn9, x9), ((xn10, x10), ((xn11, x11), ((xn12, x12), ((xn13, x13), ((xn14, x14), x15)))))))))))))).
(* hint proof tokens: 16 *)
Proof. intros. repeat destruct_prod. repeat eexists. Qed.
Ltac destruct_varname14 :=
	match goal with
	| [ H : VARNAME (_) * _ * (VARNAME (_) * _ * (VARNAME (_) * _ * (VARNAME (_) * _ * (VARNAME (_) * _ * (VARNAME (_) * _ * (VARNAME (_) * _ * (VARNAME (_) * _ * (VARNAME (_) * _ * (VARNAME (_) * _ * (VARNAME (_) * _ * (VARNAME (_) * _ * (VARNAME (_) * _ * ((VARNAME (_) * _) * _))))))))))))) |- _ ] =>
		let Hx := fresh in
		pose proof (destruct_varname14 H) as Hx;
		match type of Hx with
		| exists (_ : VARNAME (vn1)) _ (_ : VARNAME (vn2)) _ (_ : VARNAME (vn3)) _ (_ : VARNAME (vn4)) _ (_ : VARNAME (vn5)) _ (_ : VARNAME (vn6)) _ (_ : VARNAME (vn7)) _ (_ : VARNAME (vn8)) _ (_ : VARNAME (vn9)) _ (_ : VARNAME (vn10)) _ (_ : VARNAME (vn11)) _ (_ : VARNAME (vn12)) _ (_ : VARNAME (vn13)) _ (_ : VARNAME (vn14)) _ _ , _ = _ =>
			destruct Hx as [? [?vn1 [? [?vn2 [? [?vn3 [? [?vn4 [? [?vn5 [? [?vn6 [? [?vn7 [? [?vn8 [? [?vn9 [? [?vn10 [? [?vn11 [? [?vn12 [? [?vn13 [? [?vn14 [? Hx] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ]
		end
	end.
Theorem destruct_varname16 : forall XN1 X1 XN2 X2 XN3 X3 XN4 X4 XN5 X5 XN6 X6 XN7 X7 XN8 X8 XN9 X9 XN10 X10 XN11 X11 XN12 X12 XN13 X13 XN14 X14 XN15 X15 XN16 X16 X17 
				(p : (XN1 * X1) * ((XN2 * X2) * ((XN3 * X3) * ((XN4 * X4) * ((XN5 * X5) * ((XN6 * X6) * ((XN7 * X7) * ((XN8 * X8) * ((XN9 * X9) * ((XN10 * X10) * ((XN11 * X11) * ((XN12 * X12) * ((XN13 * X13) * ((XN14 * X14) * ((XN15 * X15) * ((XN16 * X16) * X17)))))))))))))))),
	exists xn1 x1 xn2 x2 xn3 x3 xn4 x4 xn5 x5 xn6 x6 xn7 x7 xn8 x8 xn9 x9 xn10 x10 xn11 x11 xn12 x12 xn13 x13 xn14 x14 xn15 x15 xn16 x16 x17, p = ((xn1, x1), ((xn2, x2), ((xn3, x3), ((xn4, x4), ((xn5, x5), ((xn6, x6), ((xn7, x7), ((xn8, x8), ((xn9, x9), ((xn10, x10), ((xn11, x11), ((xn12, x12), ((xn13, x13), ((xn14, x14), ((xn15, x15), ((xn16, x16), x17)))))))))))))))).
(* hint proof tokens: 16 *)
Proof. intros. repeat destruct_prod. repeat eexists. Qed.
Ltac destruct_varname16 :=
	match goal with
	| [ H : VARNAME (_) * _ * (VARNAME (_) * _ * (VARNAME (_) * _ * (VARNAME (_) * _ * (VARNAME (_) * _ * (VARNAME (_) * _ * (VARNAME (_) * _ * (VARNAME (_) * _ * (VARNAME (_) * _ * (VARNAME (_) * _ * (VARNAME (_) * _ * (VARNAME (_) * _ * (VARNAME (_) * _ * (VARNAME (_) * _ * (VARNAME (_) * _ * ((VARNAME (_) * _) * _))))))))))))))) |- _ ] =>
		let Hx := fresh in
		pose proof (destruct_varname16 H) as Hx;
		match type of Hx with
		| exists (_ : VARNAME (vn1)) _ (_ : VARNAME (vn2)) _ (_ : VARNAME (vn3)) _ (_ : VARNAME (vn4)) _ (_ : VARNAME (vn5)) _ (_ : VARNAME (vn6)) _ (_ : VARNAME (vn7)) _ (_ : VARNAME (vn8)) _ (_ : VARNAME (vn9)) _ (_ : VARNAME (vn10)) _ (_ : VARNAME (vn11)) _ (_ : VARNAME (vn12)) _ (_ : VARNAME (vn13)) _ (_ : VARNAME (vn14)) _ (_ : VARNAME (vn15)) _ (_ : VARNAME (vn16)) _ _ , _ = _ =>
			destruct Hx as [? [?vn1 [? [?vn2 [? [?vn3 [? [?vn4 [? [?vn5 [? [?vn6 [? [?vn7 [? [?vn8 [? [?vn9 [? [?vn10 [? [?vn11 [? [?vn12 [? [?vn13 [? [?vn14 [? [?vn15 [? [?vn16 [? Hx] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ]
		end
	end.
Ltac destruct_varnames :=
	repeat (( destruct_varname16 || destruct_varname14 || destruct_varname12 || destruct_varname10 || destruct_varname8 || destruct_varname6 || destruct_varname4 || destruct_varname2 || destruct_varname1); subst).
