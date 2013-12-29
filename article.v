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
Notation Round_P := (Rnd_NE_pt beta fexp).
Variable choice : Z -> bool. (* since the article does not depend on the choice function, we keep it as a parameter *)
Definition Round := round beta fexp (Znearest choice).  (* the rounding function *)
Definition Myulp (x : R) := if Req_EM_T x 0 then 0%R else (ulp beta fexp x) .
Definition u := (/ 2 * (bpow beta (- p + 1)))%R.
Open Scope R_scope.

Hypothesis RoundNeg : forall x, Round (-x) = -Round x.


Lemma ValFexp : Valid_exp fexp.
Proof.
apply FLX_exp_valid.
exact Hpgt0.
Qed.

Lemma ValidRound :  Valid_rnd (Znearest choice).
apply valid_rnd_N.
Qed.

Lemma RoundNPT : forall x, Rnd_N_pt (FLX_format beta p) x (Round x).
intros x0.
unfold Rnd_N_pt.
split.
apply FLX_format_generic.
exact Hpgt0.
(* apply round_generic. *)

apply generic_format_round.
apply ValFexp.
apply ValidRound.
intros g.
intros Fg.
apply round_N_pt.
apply ValFexp.
apply generic_format_FLX.
auto.
Qed.

Lemma roundStable : forall x, format x -> Round x = x.
Proof.
intros x0 fx0.
apply round_generic. apply ValidRound.
apply generic_format_FLX; auto.
Qed.


Lemma formBeta : forall k, format (bpow beta k).
intros k.
apply FLX_format_generic. 
exact Hpgt0.
apply generic_format_bpow.
unfold FLX_exp.
assert (0 < p)%Z by exact Hpgt0.
psatzl Z.
Qed.

Lemma upos : 0 <= u.
Proof.
unfold u.
SearchAbout (0 <= _ * _)%R.
apply Rmult_le_pos; try lra.
apply (Rlt_le _ _ (bpow_gt_0 beta (_))).
Qed.

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

Lemma ulpgt0 : forall x, x <> 0 -> 0 < Myulp x. 
Proof.
intros x Hxgt0.
rewrite ulpn0; try lra.
lazy beta delta [ulp canonic_exp FLX_exp ] in *.
apply bpow_gt_0.
Qed.


Lemma form2_1 : forall x : R, Rabs (Round x - x) <= / 2 * Myulp x.
Proof.
intros x.
unfold Round, ulp.
(* SearchAbout ulp. *)
assert (VE : Valid_exp fexp) by apply ValFexp.
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


Lemma P3_1_R : Rabs (R1 - R) <= u * (Rabs R) + u * Rabs (b*d) + u^2 * Rabs (b*d).
Proof.
destruct (relative_error_N_FLX_ex beta p Hpgt0 choice (b*d)) as [eps1 [heps1 heqeps1]].
(* unfold R1,R; simpl. *)
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

Lemma P3_1_I : Rabs (I1 - I) <= u * (Rabs I) + u * Rabs (b*c) + u^2 * Rabs (b*c).
Proof.
destruct (relative_error_N_FLX_ex beta p Hpgt0 choice (b*c)) as [eps1 [heps1 heqeps1]].
(* unfold I,I1; simpl. *)
destruct (relative_error_N_FLX_ex beta p Hpgt0 choice ((a * d + b * c * (1 + eps1)))) as [eps2 [heps2 heqeps2]].
assert (HI1 : (I1 = (a * d + b * c * (1 + eps1)) * (1 + eps2))%R).
  unfold I1,i1.
   replace (Round(b*c)) with  (b * c * (1 + eps1)).
   replace (Round (a*d + _*_*_)) with ((a * d + b * c * (1 + eps1)) * (1 + eps2)).
   lra.

rewrite HI1. unfold I.
replace (Cim z) with (a*d + b*c); try auto.
assert (Heqint1 :(a * d + b * c * (1 + eps1)) * (1 + eps2) - (a * d + b * c) =  I * eps2 + b * c * eps1  + b * c * eps1 * eps2) by (unfold I; simpl; ring).
rewrite Heqint1.
rewrite !Rplus_assoc.
set (u1 := I * _).
set (u2 := b*c*eps1).
set (u3 := u2*_).
apply (Rle_trans _ (Rabs u1 + Rabs (u2 +  u3)) _ ).
apply Rabs_triang.
apply Rplus_le_compat.
unfold u1. rewrite Rmult_comm.
rewrite Rabs_mult.
apply Rmult_le_compat; try apply Rabs_pos; try lra; try exact heps2.
unfold I; simpl;lra.
apply (Rle_trans _ (Rabs (u2) + Rabs  u3) _ ).
apply Rabs_triang.
apply Rplus_le_compat.
unfold u2; rewrite Rmult_comm.
rewrite Rabs_mult.
apply Rmult_le_compat; try apply Rabs_pos; try lra; try exact heps1.
unfold u3,u2.
rewrite Rmult_assoc; rewrite Rmult_comm.
rewrite !Rabs_mult.
rewrite <-!Rmult_assoc.
replace (u^2) with (u*u); try ring.
repeat apply Rmult_le_compat; repeat (try rewrite <-!Rabs_mult; apply Rabs_pos); try unfold u; try lra.
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

Lemma P3_2_implicit_1 : forall x y, Myulp(x) < Myulp(y) -> exists k, Rabs x < bpow beta k <= Rabs y.
intros x y Hulps.
destruct (Req_dec x 0).
rewrite H. rewrite Rabs_R0.
set (r := ln_beta beta y).
destruct (Req_dec y 0).
rewrite H,H0 in Hulps; lra.
destruct r as [r h2]; simpl.
exists (r-1)%Z. 
split.
apply bpow_gt_0.
lra.
destruct (Req_dec y 0).
rewrite H0 in Hulps. rewrite ulp0 in Hulps.
assert (Hcontr : Myulp x > 0).
exact (ulpgt0 x H).
lra.
(* now x and y <> 0, serious stuff begins *)
rewrite !ulpn0 in Hulps; try lra.
lazy beta delta [ulp canonic_exp FLX_exp ] in Hulps.
assert (HulpsMod : bpow beta ( (ln_beta beta x)) <
          bpow beta ( (ln_beta beta y))).
unfold fexp,FLX_exp in Hulps. 
replace (ln_beta beta x - p)%Z with (ln_beta beta x + (- p))%Z in Hulps; try ring.
replace (ln_beta beta y - p)%Z with (ln_beta beta y + (- p))%Z in Hulps; try ring.
rewrite !bpow_plus in Hulps.
apply (Rmult_lt_reg_r (bpow beta (-p)) _); try apply bpow_gt_0; lra.
exists (ln_beta beta x).
split.
apply  bpow_ln_beta_gt.
apply Rnot_gt_le.
intros  Habs.
assert ( Hy : (ln_beta beta y <= ln_beta beta x)%Z).
apply ln_beta_le_bpow; try lra.
(* SearchAbout (bpow _ _ < bpow _ _). *)
assert (Habs1 := (bpow_le beta (ln_beta beta y) (ln_beta beta x) Hy)).
lra.
Qed.


Lemma P3_2_Rabs : forall x y, (x*y)>= 0 -> Rabs (x + y) = Rabs x + Rabs y.
Proof.
intros x0 y0 Hxy.
destruct (Req_dec x0 0) as [Hx0 | Hxn0].
rewrite Hx0; rewrite Rplus_0_l; rewrite Rabs_R0;rewrite Rplus_0_l; lra.
destruct (Req_dec y0 0) as [Hy0 | Hyn0].
rewrite Hy0; rewrite Rplus_0_r; rewrite Rabs_R0;rewrite Rplus_0_r; lra.
destruct (Rle_dec x0 0).
destruct (Rle_dec y0 0).
(* x0, y0 < 0*)
replace (x0 + y0) with (-(-x0 -y0)); try lra.
rewrite Rabs_Ropp.
rewrite Rabs_pos_eq; try lra.
replace (Rabs x0) with (-x0); rewrite <-Rabs_Ropp; rewrite Rabs_pos_eq; lra.
(* x0 < 0, y0 > 0 *)
assert ( 0 > (x0 * y0)). SearchAbout ( _ < 0).
replace 0 with (x0 * 0); try ring.
apply (Rmult_lt_gt_compat_neg_l x0 0 y0); try lra.
lra.
destruct (Rle_dec y0 0).
(* x0 > 0, y0 < 0 *)
assert ( 0 > (y0 * x0)).
replace 0 with (y0 * 0); try ring.
apply (Rmult_lt_gt_compat_neg_l y0 0 x0); try lra.
lra.
(* x0 > 0, y0 > 0 *)
rewrite !Rabs_pos_eq; lra.
Qed.

Lemma P3_2 : (0 <= (a*b*c*d)) -> Rabs (I1 - I) <= u * Rabs I + u * Rabs (b*c).
intros Habcd.
assert (fact1 : (I1 - I) =  (Round (i1) - i1) + (Round (b*c) - b*c)).
unfold I1,i1,I. simpl; ring.
rewrite fact1.
apply (Rle_trans _ (Rabs (Round (i1) - i1) + Rabs (Round (b*c) - b*c)) _).
apply Rabs_triang.
apply Rplus_le_compat.
  destruct  (Rle_dec (Myulp i1) (Myulp I)).
      (* case when ulp(i1) <= ulp(I) *)
  apply (Rle_trans _ (/ 2 * Myulp(i1)) _). 
    apply form2_1.

      apply (Rle_trans _ (/ 2 * Myulp I) _). lra.
      apply form2_2.
      (* case when ulp(i1) > ulp(I) *)
      destruct (P3_2_implicit_1 I i1) as [k Hencadr]; try lra.
      assert (Hint2 : Rabs(Round(i1) - i1) <= Rabs i1 - bpow beta k).
      destruct (Rle_dec i1 0).
      (* case when i1 is >= 0 *)
      replace (Round i1) with (- Round (-i1)); try apply RoundNeg.
      apply (Rle_trans _ (Rabs (- i1 - bpow beta k)) _).
      replace (-Round (-i1) - i1) with (- i1 - Round(-i1)); try ring.
      assert (Rnd_N_pt (FLX_format beta p)  (-i1) (Round (-i1))). 
      apply RoundNPT.
      destruct H as [H H0].
      replace (- i1 - Round (- i1)) with (-(Round (- i1) - - i1)); try ring.
      rewrite Rabs_Ropp.
      replace (- i1 - bpow beta k) with (-((bpow beta k) - (- i1))); try ring.
      rewrite Rabs_Ropp.
      apply (H0 (bpow beta k)).
      SearchAbout FLX_format.
      apply formBeta.
      replace (-i1) with (Rabs i1).
      assert (Hpos : 0 <= Rabs i1 - bpow beta k) by lra.
      rewrite (Rabs_pos_eq ); try lra.
      apply Rabs_left1; lra.
      rewrite RoundNeg; lra.
      
      (*case when i1 is >0 *)
      assert (Rabsi1 : Rabs i1 = i1). try apply Rabs_pos_eq; try lra .
      assert (Hge : bpow beta k <= i1).
      try lra.
      rewrite Rabsi1.
            assert (Rnd_N_pt (FLX_format beta p)  i1 (Round i1)).
      apply RoundNPT.
      destruct H as [Fri1 RNEDef].
      apply (Rle_trans _ (Rabs (bpow beta k - i1)) _).
      apply (RNEDef).
      apply formBeta.
      replace (bpow beta k - i1) with (-(i1 - bpow beta k)); try lra.
      rewrite Rabs_Ropp.
      rewrite Rabs_pos_eq; try lra.
      assert (Hint3 : Rabs i1 - bpow beta k < Rabs i1 - Rabs I). lra. 
      assert (Hint4 : Rabs i1 - Rabs I <= Rabs (i1 - I)).
      apply Rabs_triang_inv.
      assert (Hint5 : (i1 - I) = Round (b*c) - b*c). 
        unfold i1,I; simpl; ring.
      assert (Hint6 : Rabs (i1 - I) <= u * Rabs (b*c)).
      rewrite Hint5. apply form2_3.
      assert (Hint7 : Rabs (Round i1 - i1) <= u * Rabs (b * c)) by lra.
      apply (Rle_trans _ (u * Rabs (b * c)) _); try lra.
      apply Rmult_le_compat; try apply Rabs_pos; try lra.
      exact upos.
      unfold I; simpl. rewrite P3_2_Rabs; try lra.
      Check Rplus_le_compat_l.
      rewrite <-Rplus_0_l at 1.
      apply Rplus_le_compat_r; try apply Rabs_pos.
      apply form2_3.
Qed.
      (* FRONT *)      


Lemma P3_3 : 0 <= (a*b*c*d) -> Rabs (a*c) < / 2 * Rabs (b*d) -> Rabs (R1 - R) <= u * Rabs (R) + u * Rabs (b * d). 
Proof.
intros Habcd H1.
set (ff := a*c - Round(b*d)).
(* Definition C b d ff := (~ (format (b*d))) /\ (~ (format ff)). *)
assert (Hfexp := ValFexp).
destruct (generic_format_EM beta fexp  (b*d)).
assert (Hint1 : Rabs(R1 - R)  <= u * Rabs R).
  unfold R1,R,r1; simpl.
rewrite (roundStable (b*d)); try apply FLX_format_generic; try apply Hpgt0; try auto.
apply form2_3.
apply (Rle_trans _ (u * Rabs R) _); try auto.
assert (Hint2 : 0 <= u * Rabs (b * d)).
apply Rmult_le_pos; try exact upos; try apply Rabs_pos.
lra.
destruct (generic_format_EM beta fexp ff).
assert (Hint3 : Rabs(R1 - R)  <= u * Rabs (b * d)).
unfold R1,R,r1; simpl.
rewrite (roundStable (_ * _ - _)); try apply FLX_format_generic; try apply Hpgt0; try auto.
replace (a * c - Round (b * d) - (a * c - b * d)) with (-(Round(b*d) - (b * d))); try ring.
rewrite Rabs_Ropp.
apply form2_3.
apply (Rle_trans _ (u * Rabs (b*d)) _); try lra.
assert (0 <= u * Rabs R).
apply Rmult_le_pos; try exact upos; try apply Rabs_pos.
lra.
(* In the paper : "we assume that (C) holds" *)

assert (Hint4 : R1 - R = (Round ff - ff) + (b*d - Round (b*d) )).
unfold R1,R,r1,ff;simpl. ring.
apply (Rle_trans _ (Rabs (Round ff - ff) + Rabs (b*d - Round (b*d))) _).
rewrite Hint4.
apply Rabs_triang.
(* Now in the special case when ulp(f) <= ulp(R): *)
destruct (Rle_dec (Myulp ff) (Myulp R)).
apply (Rle_trans _ (/ 2 * Myulp ff + u * Rabs (b * d)) _ ).
apply Rplus_le_compat.
apply form2_1.
apply form2_3.
SearchAbout (/ 2 * Myulp _).
SearchAbout ({ _ } + { _ }) (generic_format).

(*       assert ( Hint2 : Rabs (bpow beta k - i1) = Rabs i1 - bpow beta k). *)
     
(*       Check Rabs_pos_eq. *)
(*       replace (bpow beta k - i1) with (-(i1 - bpow beta k)); try ring. *)
(*       rewrite Rabs_Ropp. *)

(*       rewrite <-(Rabs_pos_eq (Rabs (i1 - bpow beta k))); try apply Rabs_pos. *)
(*       rewrite Rabs_pos_eq. *)
(*       replace (Rabs i1) with i1. *)
(*       ring. *)
(*       rewrite Rabs_pos_eq; try lra. *)
(*       apply (Rle_trans _ (bpow beta k) _). *)
(*       apply (Rlt_le _ _ (bpow_gt_0 beta (_))); lra. *)
(*       assert (bpow_gt_0 beta k). *)
(*       SearchAbout Rabs (- _). *)
(*       SearchAbout (Rabs) (0 <= _). *)

(* Check Round_P. *)

(* apply round_NE_pt. *)
(*       apply form2_3. *)
(* Qed. *)




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

