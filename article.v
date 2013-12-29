Require Import Psatz Fcore_FLX Fcore Fcalc_ops Fprop_relative.
(* Open Scope R_scope. *)
Ltac lraZ := try psatzl Z.

Add LoadPath "/home/thomas/Documents/M2/CR05_Floating_Point_Arithmetic/tpThery/rls/Complex".
Require Import Reals.
Require Import Cdefinitions.
Require Import Cbase.
Require Import Ctacfield.
Require Import Cnorm.


Variable beta : radix.
Variable p : Z. (* precision, also called prec in Fcore_FLX *)

Hypothesis Hbeta : (beta >= 2)%Z.
Hypothesis Hp : (2 <= p)%Z.
Hypothesis Hpgt0 : (0 < p)%Z.
(* Variable x : R. *)
(* Check FLX_format beta p x. *)

Print FLX_exp.
Definition fexp := FLX_exp p.
Notation format := (FLX_format beta p). (* a predicate saying that the argument is an FLX floating point number *)
Variable choice : Z -> bool. (* since the article does not depend on the choice function, we keep it as a parameter *)
Definition Round := round beta fexp (Znearest choice).  (* the rounding function *)
Definition Myulp (x : R) := if Req_EM_T x 0 then 0%R else (ulp beta fexp x) .
Definition u := (/ 2 * (bpow beta (- p + 1)))%R.
Open Scope R_scope.

Lemma ulp0 : Myulp 0 = 0.
unfold Myulp.
destruct (Req_EM_T 0 0); lra.
Qed.

Lemma ulpn0 : forall x, x <> 0 -> Myulp x = (ulp beta fexp x).
Proof.
intros x xn0.
unfold Myulp.
destruct (Req_EM_T x 0); lra.
Qed.

Lemma form2_1 : forall x : R, Rabs (Round x - x) <= / 2 * Myulp x.
Proof.
intros x.
unfold Round, ulp.
(* SearchAbout ulp. *)
assert (VE : Valid_exp fexp).
apply FLX_exp_valid.
exact Hpgt0.
unfold Myulp.
destruct (Req_dec x 0).
  rewrite H.
  replace (_ - 0) with 0.  rewrite Rabs_R0. replace (if Req_EM_T 0 0 then 0 else _) with 0.
  lra.
  destruct (Req_EM_T 0 0); try lra. rewrite round_0. ring. apply valid_rnd_N.
  destruct (Req_EM_T x 0); try lra.
  apply (ulp_half_error beta fexp choice x).
Qed.


(* Check (relative_error_N_FLX beta p). *)


Lemma form2_2 : forall x : R,  / 2 * Myulp x <= u * Rabs x.
intros x.
destruct (Req_dec x 0). rewrite H.
rewrite ulp0. rewrite Rabs_R0. lra.
rewrite ulpn0; try lra.
unfold fexp.
lazy beta delta [ulp canonic_exp FLX_exp ] in *.
set (r := ln_beta beta x).
destruct r as [r h2]; simpl.
unfold u.
rewrite !Rmult_assoc.
apply Rmult_le_compat; try lra.
apply (Rlt_le _ _ (bpow_gt_0 beta (r-p))).
apply (Rle_trans _ ((bpow beta (- p + 1)) * (bpow beta (r-1))) _).
rewrite <-bpow_plus. 
replace (- p + 1 + (r - 1))%Z with (r - p)%Z; try lra; try ring.
apply Rmult_le_compat.
apply (Rlt_le _ _ (bpow_gt_0 beta (-p+1))).
apply (Rlt_le _ _ (bpow_gt_0 beta (_))).
lra.
lra.
Qed.


Lemma form2_3 : forall x : R, Rabs (Round x - x)  <= u * Rabs x.
Proof.
intros x.
destruct (Req_dec x 0).
rewrite H; simpl.
assert (R0 : Round 0 = 0). 
apply round_0.
apply valid_rnd_N.
rewrite R0.
replace (0 - 0) with 0.
rewrite !Rabs_R0.
replace (u * 0) with 0.
lra.
lra.
lra.
apply (Rle_trans _ (/ 2 * Myulp x) _).
apply form2_1.
apply (form2_2 x).
Qed.


Variable a b c d : R.
Definition x := a +i b.
Definition y := c +i d.
Definition z := (x * y)%C.

Lemma prodxy : z = (a*c - b*d) +i (a*d + b*c).
Proof.
CusingR_simpl; ring.
Qed.

Definition R := Cre z.
Definition I := Cim z.
Definition r1 := (a*c - Round(b*d))%R.
Definition R1 := Round(r1).
Definition i1 := (a*d + Round(b*c))%R.
Definition I1 := Round(i1).
Definition z1 := R1 +i I1.


Lemma P3_1 : Rabs (R1 - R) <= u * (Rabs R) + u * Rabs (b*d) + u^2 * Rabs (b*d).
Proof.
destruct (relative_error_N_FLX_ex beta p Hpgt0 choice (b*d)) as [eps1 [heps1 heqeps1]].
destruct (relative_error_N_FLX_ex beta p Hpgt0 choice ((a * c - b * d * (1 + eps1)))) as [eps2 [heps2 heqeps2]].

assert (HR1 : (R1 = (a * c - b * d * (1 + eps1)) * (1 + eps2))%R).
  unfold R1,r1.
    assert (Hround1 : Round (b * d) =  (b * d * (1 + eps1))%R).
      unfold Round,fexp; rewrite  heqeps1. auto.
      rewrite Hround1.
      assert (Hround2 : Round (a * c - b * d * (1 + eps1)) = ((a * c - b * d * (1 + eps1)) * (1 + eps2))%R).
        unfold Round,fexp; rewrite heqeps2; auto.
        rewrite Hround2; auto.
  assert (eqInt : (R1 - R = R * eps2 - b * d *eps1 - b * d * eps1 * eps2)%R ).
    rewrite HR1; unfold R; simpl; ring.
    rewrite eqInt.
      set (x_1 := Rabs _) at 1.
      set (x_2 := (_ + _ + _)%R).
      set (x_3 := (Rabs (R * eps2) + Rabs(- b*d*eps1 - b*d*eps1*eps2))%R).
      apply (Rle_trans x_1 x_3 x_2).
        unfold x_1,x_3.
        assert (Hrew : (R * eps2 - b * d * eps1 - b * d * eps1 * eps2 = R * eps2 +  (- b * d * eps1 - b * d * eps1 * eps2) )%R) by ring; rewrite Hrew; apply Rabs_triang.
        
        unfold x_3,x_2; rewrite Rplus_assoc; apply Rplus_le_compat.
          rewrite Rabs_mult; rewrite Rmult_comm; apply Rmult_le_compat; try apply Rabs_pos; try lra; exact heps2.
        apply (Rle_trans _ (Rabs (- b*d*eps1) + Rabs (- b*d*eps1*eps2)) _).
          rewrite !Ropp_mult_distr_l_reverse; apply Rabs_triang.
          apply Rplus_le_compat.
            rewrite Rabs_mult; rewrite Rmult_comm; apply Rmult_le_compat; try apply Rabs_pos; try exact heps1; rewrite Ropp_mult_distr_l_reverse; rewrite Rabs_Ropp; lra.
            rewrite !Ropp_mult_distr_l_reverse; rewrite Rabs_Ropp; rewrite 2!Rabs_mult; 
            rewrite Rmult_assoc; rewrite Rmult_comm;  apply Rmult_le_compat. 
              rewrite <-Rabs_mult; apply Rabs_pos. 
              apply Rabs_pos.
              replace (u ^ 2) with (u*u)%R. 
                apply Rmult_le_compat; try apply Rabs_pos; auto. 
                ring.
  lra.
Qed.

(* Lemma P3_2_prelim : Myulp i1 <= Myulp I. *)
(* Proof. *)
(* (* this proof seems difficult. We need to know that if ulp(y) < ulp(x), there exists k such that |y| < beta^k <= |g| *) *)
(* SearchAbout (~ _ < _). *)
(* apply Rnot_lt_le. *)
(* intros Habs. *)


(* set (u := Myulp _) at 1. *)
(* set (v := Myulp _). *)
(* destruct (Rle_dec u v); try lra. *)

(* contradict. *)
(* unfold Myulp,fexp. *)
(* lazy beta delta [ulp canonic_exp FLX_exp ] in *. *)

(* SearchAbout (ulp _ < ulp _). *)
(* admit. *)
(* Qed. *)

Lemma P3_2 : (0 <= (a*b*c*d)) -> Rabs (I1 - I) <= u * Rabs I + u * Rabs (b*c).
intros Habcd.
destruct (Req_dec I 0) as [I0 | Ineq0].
  rewrite I0. replace (I1 - 0) with I1. rewrite Rabs_R0.
  unfold I1,i1. unfold I in I0; simpl in I0.
replace (u * 0) with 0.
rewrite Rplus_0_l.
replace (a * d + Round (b * c)) with (Round (b * c) - b * c).
apply form2_3.

SearchAbout (0 + _)
Check form2_3.


assert (fact1 : (I1 - I) =  (Round (i1) - i1) + (Round (b*c) - b*c)).
unfold I1,i1,I. simpl; ring.
rewrite fact1.
apply (Rle_trans _ (Rabs (Round (i1) - i1) + Rabs (Round (b*c) - b*c)) _).
apply Rabs_triang.
apply Rplus_le_compat.
  apply (Rle_trans _ (/ 2 * Myulp(i1)) _). 
    apply form2_1.
      destruct  (Rle_dec (Myulp i1) (Myulp I)).
      apply (Rle_trans _ (/ 2 * Myulp I) _). lra.
      apply form2_2.
      apply form2_3.
Qed.




Theorem P3_1 : Cnorm (z1 - z) <= 2 * u * Cnorm z. (* paper : Theorem 3.1 *)
admit.
Qed.

(* Pour découvrir CoqTail *)
(* Open Scope C_scope. *)

(* Definition C0 := R_R_to_C 0 0. *)
(* Definition C1 := R_R_to_C 1 0. *)
(* Definition Ci := R_R_to_C 0 1. *)
(* Definition C1i := 1 +i 1. *)
(* Check C1i. *)


(* Check (Ci*2). *)
(* Eval compute in (Ci*2). *)

(* Lemma Di : Ci*2 = R_R_to_C 0 2.  *)
(* Proof. *)
(* CusingR_simpl; ring. *)
(* Qed. *)

