import AssertBytes240.Algebra.HilbertFunction
import AssertBytes240.Algebra.DegreeCalculus

/-!
# T2-W1b (part 2) — the degree of a homogeneous ideal and its calculus

Packages the Hilbert polynomial and the rational degree `degQ`.
The exported calculus covers positivity, multiplication under a homogeneous
nonzerodivisor cut, additivity over isolated intersections, and monotonicity at
fixed Hilbert-polynomial degree.
-/

open MvPolynomial Filter
open scoped fwdDiff

noncomputable section

variable {K : Type*} [Field K] {n : ℕ}

open Classical in
/-- The Hilbert polynomial of `R ⧸ I` (zero if none exists; unique when it does). -/
def hilbPoly (I : Ideal (MvPolynomial (Fin n) K)) : Polynomial ℚ :=
  if h : ∃ P : Polynomial ℚ, ∀ᶠ e in atTop, (HF I e : ℚ) = P.eval (e : ℚ) then
    h.choose else 0

/-- The (rational-valued) degree: `natDegree! · leadingCoeff`. Agrees with the
classical degree of the ideal for quotients of Krull dimension ≥ 1. -/
def degQ (I : Ideal (MvPolynomial (Fin n) K)) : ℚ :=
  (hilbPoly I).natDegree.factorial * (hilbPoly I).leadingCoeff

private lemma eventually_fwdDiff_iter_eq {G : Type*} [AddCommGroup G]
    {f g : ℕ → G} (k : ℕ) (h : ∀ᶠ e in atTop, f e = g e) :
    ∀ᶠ e in atTop, (fwdDiff (1 : ℕ))^[k] f e = (fwdDiff (1 : ℕ))^[k] g e := by
  rw [Filter.eventually_atTop] at h ⊢
  obtain ⟨N, hN⟩ := h
  refine ⟨N, ?_⟩
  intro e he
  rw [fwdDiff_iter_eq_sum_shift, fwdDiff_iter_eq_sum_shift]
  refine Finset.sum_congr rfl ?_
  intro i hi
  have hfg : f (e + i • (1 : ℕ)) = g (e + i • (1 : ℕ)) := by
    exact hN (e + i • (1 : ℕ)) (le_trans he (Nat.le_add_right e (i • (1 : ℕ))))
  rw [hfg]

private lemma fwdDiff_iter_eval_natCast (P : Polynomial ℚ) (k e : ℕ) :
    (fwdDiff (1 : ℕ))^[k] (fun e : ℕ => P.eval (e : ℚ)) e =
      (fwdDiff (1 : ℚ))^[k] P.eval (e : ℚ) := by
  induction k generalizing e with
  | zero => rfl
  | succ k ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      simp [fwdDiff, ih e, ih (e + 1)]

private lemma fwdDiff_iter_natCast_int (g : ℕ → ℕ) (k e : ℕ) :
    ∃ z : ℤ, (fwdDiff (1 : ℕ))^[k] (fun e : ℕ => (g e : ℚ)) e = (z : ℚ) := by
  induction k generalizing e with
  | zero =>
      exact ⟨g e, by simp⟩
  | succ k ih =>
      obtain ⟨z₁, hz₁⟩ := ih (e + 1)
      obtain ⟨z₀, hz₀⟩ := ih e
      refine ⟨z₁ - z₀, ?_⟩
      rw [Function.iterate_succ_apply']
      simp [fwdDiff, hz₁, hz₀]

private lemma normalizedLeadingCoeff_int_of_eventually_nat (P : Polynomial ℚ) (g : ℕ → ℕ)
    (hP : ∀ᶠ e in atTop, (g e : ℚ) = P.eval (e : ℚ)) :
    ∃ z : ℤ, (P.natDegree.factorial : ℚ) * P.leadingCoeff = z := by
  let N := P.natDegree
  let fN : ℕ → ℚ := fun e => (g e : ℚ)
  let fP : ℕ → ℚ := fun e => P.eval (e : ℚ)
  have hdiff : ∀ᶠ e in atTop, (fwdDiff (1 : ℕ))^[N] fN e =
      (fwdDiff (1 : ℕ))^[N] fP e :=
    eventually_fwdDiff_iter_eq N hP
  obtain ⟨e, he⟩ := hdiff.exists
  obtain ⟨z, hz⟩ := fwdDiff_iter_natCast_int g N e
  refine ⟨z, ?_⟩
  have hconst :
      (fwdDiff (1 : ℚ))^[P.natDegree] P.eval (e : ℚ) =
        P.leadingCoeff * (P.natDegree.factorial : ℚ) := by
    simpa [Pi.smul_apply, smul_eq_mul] using
      congr_fun (Polynomial.fwdDiff_iter_degree_eq_factorial P) (e : ℚ)
  have hnat :
      (fwdDiff (1 : ℕ))^[N] fP e =
        (fwdDiff (1 : ℚ))^[N] P.eval (e : ℚ) := by
    simpa [fP] using fwdDiff_iter_eval_natCast P N e
  have hseq : (fwdDiff (1 : ℕ))^[N] fP e = (z : ℚ) := by
    rw [← he]
    exact hz
  calc
    (P.natDegree.factorial : ℚ) * P.leadingCoeff
        = P.leadingCoeff * (P.natDegree.factorial : ℚ) := by ring
    _ = (fwdDiff (1 : ℚ))^[P.natDegree] P.eval (e : ℚ) := hconst.symm
    _ = (fwdDiff (1 : ℚ))^[N] P.eval (e : ℚ) := by rfl
    _ = (fwdDiff (1 : ℕ))^[N] fP e := hnat.symm
    _ = (z : ℚ) := hseq

theorem hilbPoly_spec [Infinite K] (I : Ideal (MvPolynomial (Fin n) K))
    (hI : IsHomog I) :
    ∀ᶠ e in atTop, (HF I e : ℚ) = (hilbPoly I).eval (e : ℚ) := by
  classical
  let h : ∃ P : Polynomial ℚ, ∀ᶠ e in atTop, (HF I e : ℚ) = P.eval (e : ℚ) :=
    HF_eventually_polynomial I hI
  unfold hilbPoly
  rw [dif_pos h]
  exact h.choose_spec

private lemma hilbPoly_leadingCoeff_pos [Infinite K]
    (I : Ideal (MvPolynomial (Fin n) K)) (hI : IsHomog I)
    (h0 : hilbPoly I ≠ 0) :
    0 < (hilbPoly I).leadingCoeff := by
  let P := hilbPoly I
  let J := sat I
  have hP : ∀ᶠ e in atTop, (HF I e : ℚ) = P.eval (e : ℚ) := by
    simpa [P] using hilbPoly_spec I hI
  have hJhom : IsHomog J := by
    simpa [J] using isHomog_sat I hI
  have hJsat : sat J = J := by
    simpa [J] using sat_sat I
  have hPJ : ∀ᶠ e in atTop, (HF J e : ℚ) = P.eval (e : ℚ) := by
    filter_upwards [HF_saturation_eventually_eq I hI, hP] with e hs hPe
    simpa [J, hs] using hPe
  have hJne : J ≠ ⊤ := by
    intro htop
    have hzero : ∀ᶠ e in atTop, P.eval ((e : ℕ) : ℚ) = 0 := by
      filter_upwards [hPJ] with e he
      rw [← he, htop, HF_top]
      norm_num
    exact h0 (by simpa [P] using poly_eq_zero_of_eventually_zero P hzero)
  exact (HF_poly_leadingCoeff_pos J hJhom hJsat hJne P hPJ).2

private lemma degQ_nonneg [Infinite K]
    (I : Ideal (MvPolynomial (Fin n) K)) (hI : IsHomog I) :
    0 ≤ degQ I := by
  by_cases h0 : hilbPoly I = 0
  · simp [degQ, h0]
  · have hlead : 0 < (hilbPoly I).leadingCoeff :=
      hilbPoly_leadingCoeff_pos I hI h0
    have hfac : 0 < ((hilbPoly I).natDegree.factorial : ℚ) := by
      exact_mod_cast Nat.factorial_pos (hilbPoly I).natDegree
    exact le_of_lt (mul_pos hfac hlead)

private lemma comp_X_sub_C_eq_taylor (P : Polynomial ℚ) (c : ℚ) :
    P.comp (Polynomial.X - Polynomial.C c) = Polynomial.taylor (-c) P := by
  simp [Polynomial.taylor_apply, sub_eq_add_neg]

private lemma coeff_sub_comp_X_sub_C_top (P : Polynomial ℚ) (c : ℚ) :
    (P - P.comp (Polynomial.X - Polynomial.C c)).coeff P.natDegree = 0 := by
  rw [Polynomial.coeff_sub]
  have hcomp : (P.comp (Polynomial.X - Polynomial.C c)).coeff P.natDegree =
      P.leadingCoeff := by
    rw [comp_X_sub_C_eq_taylor, Polynomial.coeff_taylor_natDegree]
  rw [hcomp]
  exact sub_self _

private lemma choose_pred_cast_eq (D : ℕ) (hD : 1 ≤ D) :
    ((D.choose (D - 1) : ℕ) : ℚ) = (D : ℚ) := by
  have hsym : D.choose (D - 1) = D.choose 1 := by
    rw [Nat.choose_symm hD]
  rw [hsym, Nat.choose_one_right]

private lemma coeff_sub_comp_X_sub_C_pred (P : Polynomial ℚ) {c : ℚ}
    (hD : 1 ≤ P.natDegree) :
    (P - P.comp (Polynomial.X - Polynomial.C c)).coeff (P.natDegree - 1) =
      (P.natDegree : ℚ) * c * P.leadingCoeff := by
  let D := P.natDegree
  have hD' : 1 ≤ D := by simpa [D] using hD
  have hlin : (Polynomial.hasseDeriv (D - 1) P).natDegree ≤ 1 := by
    have hle := Polynomial.natDegree_hasseDeriv_le P (D - 1)
    have htail : P.natDegree - (D - 1) ≤ 1 := by
      simp [D]
      omega
    exact le_trans hle htail
  have htaylor :
      (P.comp (Polynomial.X - Polynomial.C c)).coeff (D - 1) =
        (Polynomial.hasseDeriv (D - 1) P).eval (-c) := by
    rw [comp_X_sub_C_eq_taylor, Polynomial.taylor_coeff]
  have h_eval : (Polynomial.hasseDeriv (D - 1) P).eval (-c) =
      (Polynomial.hasseDeriv (D - 1) P).coeff 0 +
        (Polynomial.hasseDeriv (D - 1) P).coeff 1 * (-c) := by
    rw [Polynomial.eq_X_add_C_of_natDegree_le_one hlin]
    simp [Polynomial.eval_add, Polynomial.eval_mul]
    ring
  have hcoeff0 : (Polynomial.hasseDeriv (D - 1) P).coeff 0 = P.coeff (D - 1) := by
    rw [Polynomial.hasseDeriv_coeff]
    simp
  have hcoeff1 : (Polynomial.hasseDeriv (D - 1) P).coeff 1 =
      (D : ℚ) * P.leadingCoeff := by
    rw [Polynomial.hasseDeriv_coeff]
    have hone : 1 + (D - 1) = D := by omega
    rw [hone]
    rw [choose_pred_cast_eq D hD']
    have hlead : P.coeff D = P.leadingCoeff := by
      change P.coeff P.natDegree = P.leadingCoeff
      rfl
    rw [hlead]
  rw [Polynomial.coeff_sub, htaylor, h_eval, hcoeff0, hcoeff1]
  simp only [D] at *
  ring

private lemma natDegree_sub_comp_X_sub_C_eq_pred (P : Polynomial ℚ) {c : ℚ}
    (hc : c ≠ 0) (hD : 1 ≤ P.natDegree) :
    (P - P.comp (Polynomial.X - Polynomial.C c)).natDegree = P.natDegree - 1 := by
  let D := P.natDegree
  have hD' : 1 ≤ D := by simpa [D] using hD
  have hcompdeg : (P.comp (Polynomial.X - Polynomial.C c)).natDegree = D := by
    rw [comp_X_sub_C_eq_taylor, Polynomial.natDegree_taylor]
  have hle : (P - P.comp (Polynomial.X - Polynomial.C c)).natDegree ≤ D - 1 := by
    rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro m hm
    by_cases hmD : m = D
    · subst m
      simpa [D, Polynomial.coeff_sub] using coeff_sub_comp_X_sub_C_top P c
    · rw [Polynomial.coeff_sub]
      have hgtD : D < m := by omega
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt (p := P) (by simpa [D] using hgtD)]
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt
        (p := P.comp (Polynomial.X - Polynomial.C c)) (by simpa [hcompdeg] using hgtD)]
      simp
  have hP0 : P ≠ 0 := by
    intro hP
    have : P.natDegree = 0 := by simp [hP]
    omega
  have hlead : P.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hP0
  have hDne : ((D : ℚ) ≠ 0) := by exact_mod_cast (ne_of_gt hD')
  have hcoeff_ne : (P - P.comp (Polynomial.X - Polynomial.C c)).coeff (D - 1) ≠ 0 := by
    rw [show D - 1 = P.natDegree - 1 by rfl, coeff_sub_comp_X_sub_C_pred P hD]
    exact mul_ne_zero (mul_ne_zero hDne hc) hlead
  have hnat := Polynomial.natDegree_eq_of_le_of_coeff_ne_zero hle hcoeff_ne
  simpa [D] using hnat

private lemma natDegree_sub_comp_X_sub_C (P : Polynomial ℚ) {c : ℚ}
    (hc : c ≠ 0) (hD : 1 ≤ P.natDegree) :
    (P - P.comp (Polynomial.X - Polynomial.C c)).natDegree + 1 = P.natDegree := by
  rw [natDegree_sub_comp_X_sub_C_eq_pred P hc hD, Nat.sub_add_cancel hD]

private lemma leadingCoeff_sub_comp_X_sub_C (P : Polynomial ℚ) {c : ℚ}
    (hc : c ≠ 0) (hD : 1 ≤ P.natDegree) :
    (P - P.comp (Polynomial.X - Polynomial.C c)).leadingCoeff =
      (P.natDegree : ℚ) * c * P.leadingCoeff := by
  rw [Polynomial.leadingCoeff, natDegree_sub_comp_X_sub_C_eq_pred P hc hD]
  exact coeff_sub_comp_X_sub_C_pred P hD

private lemma isHomog_inf {A B : Ideal (MvPolynomial (Fin n) K)}
    (hA : IsHomog A) (hB : IsHomog B) : IsHomog (A ⊓ B) := by
  intro p hp e
  exact ⟨hA p hp.1 e, hB p hp.2 e⟩

/-- Uniqueness: any eventual polynomial for `HF I` is `hilbPoly I`. -/
theorem hilbPoly_eq_of_eventually (I : Ideal (MvPolynomial (Fin n) K))
    (P : Polynomial ℚ) (hP : ∀ᶠ e in atTop, (HF I e : ℚ) = P.eval (e : ℚ)) :
    hilbPoly I = P := by
  classical
  let h : ∃ Q : Polynomial ℚ, ∀ᶠ e in atTop, (HF I e : ℚ) = Q.eval (e : ℚ) :=
    ⟨P, hP⟩
  have hchoose : ∀ᶠ e in atTop, (HF I e : ℚ) = h.choose.eval (e : ℚ) :=
    h.choose_spec
  have hzero : ∀ᶠ e in atTop, (h.choose - P).eval ((e : ℕ) : ℚ) = 0 := by
    filter_upwards [hchoose, hP] with e hq hp
    rw [Polynomial.eval_sub, ← hq, ← hp, sub_self]
  have hdiff : h.choose - P = 0 := poly_eq_zero_of_eventually_zero (h.choose - P) hzero
  have hchoose_eq : h.choose = P := sub_eq_zero.mp hdiff
  unfold hilbPoly
  rw [dif_pos h]
  exact hchoose_eq

/-- Integrality: the degree is a natural number. -/
theorem degQ_eq_natCast [Infinite K] (I : Ideal (MvPolynomial (Fin n) K))
    (hI : IsHomog I) : ∃ D : ℕ, degQ I = D := by
  let P := hilbPoly I
  have hP : ∀ᶠ e in atTop, (HF I e : ℚ) = P.eval (e : ℚ) := by
    simpa [P] using hilbPoly_spec I hI
  obtain ⟨z, hz⟩ := normalizedLeadingCoeff_int_of_eventually_nat P (HF I) hP
  have hzdeg : degQ I = (z : ℚ) := by
    simpa [degQ, P] using hz
  have hz_nonneg : 0 ≤ z := by
    have hzq : (0 : ℚ) ≤ (z : ℚ) := by
      simpa [← hzdeg] using degQ_nonneg I hI
    exact_mod_cast hzq
  refine ⟨z.toNat, ?_⟩
  rw [hzdeg]
  exact_mod_cast (Int.toNat_of_nonneg hz_nonneg).symm

/-- Positivity: nonzero Hilbert polynomial forces degree ≥ 1. -/
theorem one_le_degQ [Infinite K] (I : Ideal (MvPolynomial (Fin n) K))
    (hI : IsHomog I) (h0 : hilbPoly I ≠ 0) : 1 ≤ degQ I := by
  obtain ⟨D, hD⟩ := degQ_eq_natCast I hI
  have hlead : 0 < (hilbPoly I).leadingCoeff :=
    hilbPoly_leadingCoeff_pos I hI h0
  have hfac : 0 < ((hilbPoly I).natDegree.factorial : ℚ) := by
    exact_mod_cast Nat.factorial_pos (hilbPoly I).natDegree
  have hpos : 0 < degQ I := by
    simpa [degQ] using mul_pos hfac hlead
  have hDpos : 0 < D := by
    have : (0 : ℚ) < (D : ℚ) := by
      simpa [hD] using hpos
    exact_mod_cast this
  have hDge : 1 ≤ D := Nat.succ_le_of_lt hDpos
  rw [hD]
  exact_mod_cast hDge

/-- Exact degree multiplication under a homogeneous nonzerodivisor cut (in
dimension ≥ 2, i.e. `natDegree ≥ 1`, which is where the recurrence uses it). -/
theorem degQ_sup_span_regular [Infinite K]
    (I : Ideal (MvPolynomial (Fin n) K)) (hI : IsHomog I)
    {f : MvPolynomial (Fin n) K} {d : ℕ}
    (hf : f ∈ homogeneousSubmodule (Fin n) K d) (hd : 0 < d)
    (hreg : IsSMulRegular (MvPolynomial (Fin n) K ⧸ I) f)
    (hdeg : 1 ≤ (hilbPoly I).natDegree) :
    degQ (I ⊔ Ideal.span {f}) = d * degQ I ∧
    (hilbPoly (I ⊔ Ideal.span {f})).natDegree + 1 = (hilbPoly I).natDegree := by
  let P := hilbPoly I
  let cut := I ⊔ Ideal.span {f}
  let R := P - P.comp (Polynomial.X - Polynomial.C (d : ℚ))
  have hdq : ((d : ℚ) ≠ 0) := by exact_mod_cast (ne_of_gt hd)
  have hP : ∀ᶠ e in atTop, (HF I e : ℚ) = P.eval (e : ℚ) := by
    simpa [P] using hilbPoly_spec I hI
  have hR : ∀ᶠ e in atTop, (HF cut e : ℚ) = R.eval (e : ℚ) := by
    rw [Filter.eventually_atTop] at hP ⊢
    obtain ⟨N, hN⟩ := hP
    refine ⟨N + d, ?_⟩
    intro e he
    have hde : d ≤ e := by omega
    have hNe : N ≤ e := by omega
    have hNsub : N ≤ e - d := by omega
    have hstep_nat := HF_step_regular I hI hf hd hreg e hde
    have hstep_q : (HF cut e : ℚ) + (HF I (e - d) : ℚ) = (HF I e : ℚ) := by
      exact_mod_cast hstep_nat
    have hcut : (HF cut e : ℚ) = (HF I e : ℚ) - (HF I (e - d) : ℚ) := by
      linarith
    have hcast : ((e - d : ℕ) : ℚ) = (e : ℚ) - (d : ℚ) := Nat.cast_sub hde
    calc
      (HF cut e : ℚ) = (HF I e : ℚ) - (HF I (e - d) : ℚ) := hcut
      _ = P.eval (e : ℚ) - P.eval ((e - d : ℕ) : ℚ) := by
        rw [hN e hNe, hN (e - d) hNsub]
      _ = R.eval (e : ℚ) := by
        simp [R, Polynomial.eval_sub, Polynomial.eval_comp, hcast]
  have hhilb : hilbPoly cut = R := hilbPoly_eq_of_eventually cut R hR
  have hnat : R.natDegree + 1 = P.natDegree := by
    simpa [R, P] using natDegree_sub_comp_X_sub_C P hdq (by simpa [P] using hdeg)
  have hlead : R.leadingCoeff = (P.natDegree : ℚ) * (d : ℚ) * P.leadingCoeff := by
    simpa [R, P] using leadingCoeff_sub_comp_X_sub_C P hdq (by simpa [P] using hdeg)
  have hnat_pred : R.natDegree = P.natDegree - 1 := by
    simpa [R, P] using natDegree_sub_comp_X_sub_C_eq_pred P hdq (by simpa [P] using hdeg)
  constructor
  · rw [degQ, degQ, hhilb]
    simp only [P, R] at hnat hlead hnat_pred ⊢
    rw [hnat_pred, hlead]
    have hfac :
        (((P.natDegree - 1).factorial : ℕ) : ℚ) *
            ((P.natDegree : ℚ) * (d : ℚ) * P.leadingCoeff) =
          (d : ℚ) * (((P.natDegree.factorial : ℕ) : ℚ) * P.leadingCoeff) := by
      have hDsucc : P.natDegree = (P.natDegree - 1) + 1 :=
        (Nat.sub_add_cancel (by simpa [P] using hdeg)).symm
      rw [hDsucc]
      rw [Nat.factorial_succ]
      norm_num
      ring
    simpa [mul_assoc] using hfac
  · simpa [cut, P, hhilb] using hnat

/-- Additivity over an intersection whose sum drops degree. -/
theorem degQ_inf_add [Infinite K]
    (A B : Ideal (MvPolynomial (Fin n) K)) (hA : IsHomog A) (hB : IsHomog B)
    {D : ℕ}
    (hDA : (hilbPoly A).natDegree = D) (hDB : (hilbPoly B).natDegree = D)
    (hA0 : hilbPoly A ≠ 0) (hB0 : hilbPoly B ≠ 0)
    (hsup : hilbPoly (A ⊔ B) = 0 ∨ (hilbPoly (A ⊔ B)).natDegree < D) :
    degQ (A ⊓ B) = degQ A + degQ B ∧
    (hilbPoly (A ⊓ B)).natDegree = D ∧ hilbPoly (A ⊓ B) ≠ 0 := by
  let PA := hilbPoly A
  let PB := hilbPoly B
  let PS := hilbPoly (A ⊔ B)
  let R := PA + PB - PS
  have hSupHom : IsHomog (A ⊔ B) := isHomog_sup hA hB
  have hInfHom : IsHomog (A ⊓ B) := isHomog_inf hA hB
  have hPA : ∀ᶠ e in atTop, (HF A e : ℚ) = PA.eval (e : ℚ) := by
    simpa [PA] using hilbPoly_spec A hA
  have hPB : ∀ᶠ e in atTop, (HF B e : ℚ) = PB.eval (e : ℚ) := by
    simpa [PB] using hilbPoly_spec B hB
  have hPS : ∀ᶠ e in atTop, (HF (A ⊔ B) e : ℚ) = PS.eval (e : ℚ) := by
    simpa [PS] using hilbPoly_spec (A ⊔ B) hSupHom
  have hR : ∀ᶠ e in atTop, (HF (A ⊓ B) e : ℚ) = R.eval (e : ℚ) := by
    filter_upwards [hPA, hPB, hPS] with e ha hb hs
    have hinf_nat := HF_inf_add_sup A B hA hB e
    have hinf_q :
        (HF (A ⊓ B) e : ℚ) + (HF (A ⊔ B) e : ℚ) =
          (HF A e : ℚ) + (HF B e : ℚ) := by
      exact_mod_cast hinf_nat
    calc
      (HF (A ⊓ B) e : ℚ) =
          (HF A e : ℚ) + (HF B e : ℚ) - (HF (A ⊔ B) e : ℚ) := by
        linarith
      _ = PA.eval (e : ℚ) + PB.eval (e : ℚ) - PS.eval (e : ℚ) := by
        rw [ha, hb, hs]
      _ = R.eval (e : ℚ) := by
        simp [R, Polynomial.eval_add, Polynomial.eval_sub]
  have hhilb : hilbPoly (A ⊓ B) = R := hilbPoly_eq_of_eventually (A ⊓ B) R hR
  have hleadA : 0 < PA.leadingCoeff := by
    simpa [PA] using hilbPoly_leadingCoeff_pos A hA hA0
  have hleadB : 0 < PB.leadingCoeff := by
    simpa [PB] using hilbPoly_leadingCoeff_pos B hB hB0
  have hPAcoeff : PA.coeff D = PA.leadingCoeff := by
    rw [← hDA]
    rfl
  have hPBcoeff : PB.coeff D = PB.leadingCoeff := by
    rw [← hDB]
    rfl
  have hPScoeffD : PS.coeff D = 0 := by
    rcases hsup with hzero | hlt
    · simp [PS, hzero]
    · exact Polynomial.coeff_eq_zero_of_natDegree_lt (by simpa [PS] using hlt)
  have hcoeffD : R.coeff D = PA.leadingCoeff + PB.leadingCoeff := by
    simp [R, Polynomial.coeff_add, Polynomial.coeff_sub, hPAcoeff, hPBcoeff, hPScoeffD]
  have hcoeffD_pos : 0 < R.coeff D := by
    rw [hcoeffD]
    exact add_pos hleadA hleadB
  have hRle : R.natDegree ≤ D := by
    rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro m hm
    have hPAzero : PA.coeff m = 0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt (by simpa [PA, hDA] using hm)
    have hPBzero : PB.coeff m = 0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt (by simpa [PB, hDB] using hm)
    have hPSzero : PS.coeff m = 0 := by
      rcases hsup with hzero | hlt
      · simp [PS, hzero]
      · exact Polynomial.coeff_eq_zero_of_natDegree_lt
          (by exact lt_trans (by simpa [PS] using hlt) hm)
    simp [R, Polynomial.coeff_add, Polynomial.coeff_sub, hPAzero, hPBzero, hPSzero]
  have hRdeg : R.natDegree = D :=
    Polynomial.natDegree_eq_of_le_of_coeff_ne_zero hRle (ne_of_gt hcoeffD_pos)
  have hRlead : R.leadingCoeff = PA.leadingCoeff + PB.leadingCoeff := by
    rw [Polynomial.leadingCoeff, hRdeg, hcoeffD]
  have hR0 : R ≠ 0 := by
    intro hzero
    have : R.coeff D = 0 := by simp [hzero]
    exact ne_of_gt hcoeffD_pos this
  constructor
  · rw [degQ, degQ, degQ, hhilb]
    simp only [PA, PB, PS, R] at hRdeg hRlead hDA hDB ⊢
    rw [hRdeg, hRlead, hDA, hDB]
    ring
  · constructor
    · simpa [hhilb] using hRdeg
    · intro hzero
      exact hR0 (by simpa [hhilb] using hzero)

/-- Monotonicity at equal degree: a bigger ideal has smaller degree. -/
theorem degQ_le_of_le [Infinite K]
    {A B : Ideal (MvPolynomial (Fin n) K)} (hA : IsHomog A) (hB : IsHomog B)
    (hAB : A ≤ B)
    (hD : (hilbPoly B).natDegree = (hilbPoly A).natDegree) :
    degQ B ≤ degQ A := by
  let P := hilbPoly A
  let Q := hilbPoly B
  let D := P.natDegree
  have hQD : Q.natDegree = D := by simpa [P, Q, D] using hD
  have hPA : ∀ᶠ e in atTop, (HF A e : ℚ) = P.eval (e : ℚ) := by
    simpa [P] using hilbPoly_spec A hA
  have hQB : ∀ᶠ e in atTop, (HF B e : ℚ) = Q.eval (e : ℚ) := by
    simpa [Q] using hilbPoly_spec B hB
  have hnonneg : ∀ᶠ (e : ℕ) in atTop, 0 ≤ (P - Q).eval (e : ℚ) := by
    filter_upwards [hPA, hQB] with e ha hb
    have hle_nat := HF_antitone hAB e
    have hle_q : (HF B e : ℚ) ≤ (HF A e : ℚ) := by
      exact_mod_cast hle_nat
    rw [Polynomial.eval_sub, ← ha, ← hb]
    linarith
  have hPcoeff : P.coeff D = P.leadingCoeff := by
    change P.coeff P.natDegree = P.leadingCoeff
    rfl
  have hQcoeff : Q.coeff D = Q.leadingCoeff := by
    rw [← hQD]
    rfl
  have hlead_le : Q.leadingCoeff ≤ P.leadingCoeff := by
    by_cases hzero : P - Q = 0
    · have hPQ : P = Q := sub_eq_zero.mp hzero
      rw [hPQ]
    · have hleadS_pos : 0 < (P - Q).leadingCoeff :=
        leadingCoeff_pos_of_eventually_nonneg (P - Q) hzero hnonneg
      have hSle : (P - Q).natDegree ≤ D := by
        have hPle : P.natDegree ≤ D := by simp [D]
        have hQle : Q.natDegree ≤ D := by simp [hQD]
        simpa using Polynomial.natDegree_sub_le_of_le (p := P) (q := Q) hPle hQle
      by_cases hlt : (P - Q).natDegree < D
      · have hcoeff0 : (P - Q).coeff D = 0 :=
          Polynomial.coeff_eq_zero_of_natDegree_lt hlt
        rw [Polynomial.coeff_sub, hPcoeff, hQcoeff] at hcoeff0
        linarith
      · have hSdeg : (P - Q).natDegree = D := le_antisymm hSle (le_of_not_gt hlt)
        have hleadS_nonneg : 0 ≤ (P - Q).leadingCoeff := le_of_lt hleadS_pos
        rw [Polynomial.leadingCoeff, hSdeg, Polynomial.coeff_sub, hPcoeff, hQcoeff] at hleadS_nonneg
        linarith
  have hfac_nonneg : 0 ≤ ((D.factorial : ℕ) : ℚ) := by positivity
  have hmul :
      ((D.factorial : ℕ) : ℚ) * Q.leadingCoeff ≤
        ((D.factorial : ℕ) : ℚ) * P.leadingCoeff :=
    mul_le_mul_of_nonneg_left hlead_le hfac_nonneg
  simpa [degQ, P, Q, D, hQD] using hmul

end
