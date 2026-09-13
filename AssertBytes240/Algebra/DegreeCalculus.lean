import AssertBytes240.Algebra.HilbertFunction

/-!
# T2-W1b (part 1) — Hilbert-function rank identities

Pure vector-space identities for the Hilbert function `HF`: antitonicity,
inclusion-exclusion for `inf`/`sup`, the top ideal value, and the ambient
binomial bound. `Degree.lean` uses these identities to prove the `degQ`
calculus.
-/

open MvPolynomial

noncomputable section

variable {K : Type*} [Field K] {n : ℕ}

private abbrev idealSubmodule (I : Ideal (MvPolynomial (Fin n) K)) :
    Submodule K (MvPolynomial (Fin n) K) :=
  I.restrictScalars K

private abbrev degreeIdealPiece (I : Ideal (MvPolynomial (Fin n) K)) (e : ℕ) :
    Submodule K (MvPolynomial (Fin n) K) :=
  (homogeneousSubmodule (Fin n) K e) ⊓ (idealSubmodule (K := K) (n := n) I)

private lemma finite_set_finsupp_degree_eq (n e : ℕ) :
    Set.Finite {s : Fin n →₀ ℕ | Finsupp.degree s = e} := by
  exact (Finsupp.finite_of_degree_le (σ := Fin n) e).subset (by
    intro s hs
    exact le_of_eq hs)

private lemma finite_set_finsupp_sum_eq (n e : ℕ) :
    Set.Finite {s : Fin n →₀ ℕ | s.sum (fun _ a => a) = e} := by
  exact (Finsupp.finite_of_degree_le (σ := Fin n) e).subset (by
    intro s hs
    have hdeg : Finsupp.degree s = e := by
      simpa [Finsupp.degree_eq_sum, Finsupp.sum_fintype] using hs
    exact le_of_eq hdeg)

private noncomputable instance instFintypeFinsuppDegreeEq (n e : ℕ) :
    Fintype {s : Fin n →₀ ℕ // Finsupp.degree s = e} :=
  (finite_set_finsupp_degree_eq n e).fintype

private noncomputable instance instFintypeFinsuppSumEq (n e : ℕ) :
    Fintype {s : Fin n →₀ ℕ // s.sum (fun _ a => a) = e} :=
  (finite_set_finsupp_sum_eq n e).fintype

private def degreeEqEquivNatSum (n e : ℕ) :
    {s : Fin n →₀ ℕ // Finsupp.degree s = e} ≃
      {s : Fin n →₀ ℕ // s.sum (fun _ a => a) = e} where
  toFun s := ⟨s.1, by
    simpa [Finsupp.degree_eq_sum, Finsupp.sum_fintype] using s.2⟩
  invFun s := ⟨s.1, by
    simpa [Finsupp.degree_eq_sum, Finsupp.sum_fintype] using s.2⟩
  left_inv s := rfl
  right_inv s := rfl

private lemma card_finsupp_degree_eq (n e : ℕ) :
    Fintype.card {s : Fin n →₀ ℕ // Finsupp.degree s = e} = Nat.multichoose n e := by
  classical
  letI : Fintype {s : Fin n →₀ ℕ // Finsupp.degree s = e} :=
    instFintypeFinsuppDegreeEq n e
  letI : Fintype {s : Fin n →₀ ℕ // s.sum (fun _ a => a) = e} :=
    instFintypeFinsuppSumEq n e
  calc
    Fintype.card {s : Fin n →₀ ℕ // Finsupp.degree s = e}
        = Fintype.card {s : Fin n →₀ ℕ // s.sum (fun _ a => a) = e} :=
          Fintype.card_congr (degreeEqEquivNatSum n e)
    _ = Fintype.card (Sym (Fin n) e) :=
          Fintype.card_congr (Equiv.symm (Sym.equivNatSum (Fin n) e))
    _ = Nat.multichoose n e := by
          simpa using Sym.card_sym_eq_multichoose (Fin n) e

-- `homogeneousSubmodule_finiteDimensional` is now provided by HilbertFunction.lean.

private lemma finrank_homogeneousSubmodule_eq_multichoose (e : ℕ) :
    Module.finrank K (homogeneousSubmodule (Fin n) K e) = Nat.multichoose n e := by
  classical
  rw [MvPolynomial.homogeneousSubmodule_eq_finsupp_supported]
  letI : Fintype ↑({s : Fin n →₀ ℕ | Finsupp.degree s = e} : Set (Fin n →₀ ℕ)) :=
    instFintypeFinsuppDegreeEq n e
  change Module.finrank K
    (MvPolynomial.restrictSupport K {s : Fin n →₀ ℕ | Finsupp.degree s = e}) =
      Nat.multichoose n e
  rw [Module.finrank_eq_card_basis
    (MvPolynomial.basisRestrictSupport K {s : Fin n →₀ ℕ | Finsupp.degree s = e})]
  exact card_finsupp_degree_eq n e

private lemma multichoose_le_degree_bound (n e : ℕ) :
    Nat.multichoose n e ≤ (e + (n - 1)).choose (n - 1) := by
  cases n with
  | zero =>
      cases e <;> simp
  | succ m =>
      rw [Nat.multichoose_eq]
      have htop : m.succ + e - 1 = e + m := by omega
      have hbot : m.succ - 1 = m := by simp
      rw [htop, hbot]
      exact le_of_eq Nat.choose_symm_add

private lemma quotient_mkₐ_ker (I : Ideal (MvPolynomial (Fin n) K)) :
    LinearMap.ker (Ideal.Quotient.mkₐ K I).toLinearMap =
      idealSubmodule (K := K) (n := n) I := by
  ext p
  change (Ideal.Quotient.mkₐ K I p = 0) ↔ p ∈ I
  rw [Ideal.Quotient.mkₐ_eq_mk]
  exact Ideal.Quotient.eq_zero_iff_mem

private lemma HF_eq_finrank_sub_inf (I : Ideal (MvPolynomial (Fin n) K)) (e : ℕ) :
    HF I e =
      Module.finrank K (homogeneousSubmodule (Fin n) K e) -
        Module.finrank K (degreeIdealPiece (K := K) (n := n) I e) := by
  let V : Submodule K (MvPolynomial (Fin n) K) := homogeneousSubmodule (Fin n) K e
  let q : MvPolynomial (Fin n) K →ₗ[K] MvPolynomial (Fin n) K ⧸ I :=
    (Ideal.Quotient.mkₐ K I).toLinearMap
  have hker :
      LinearMap.ker (q.domRestrict V) =
        Submodule.comap V.subtype (idealSubmodule (K := K) (n := n) I) := by
    rw [LinearMap.ker_domRestrict, quotient_mkₐ_ker (K := K) (n := n) I]
  have hker_finrank :
      Module.finrank K (LinearMap.ker (q.domRestrict V)) =
        Module.finrank K (degreeIdealPiece (K := K) (n := n) I e) := by
    rw [hker]
    rw [← Submodule.finrank_map_subtype_eq V
      (Submodule.comap V.subtype (idealSubmodule (K := K) (n := n) I))]
    rw [Submodule.map_comap_subtype]
  have hrn := LinearMap.finrank_range_add_finrank_ker (q.domRestrict V)
  have hrange : LinearMap.range (q.domRestrict V) = Submodule.map q V := by
    rw [LinearMap.range_domRestrict]
  unfold HF
  change Module.finrank K (Submodule.map q V) =
    Module.finrank K V - Module.finrank K (degreeIdealPiece (K := K) (n := n) I e)
  rw [← hrange, ← hker_finrank]
  exact Nat.eq_sub_of_add_eq hrn

private lemma homogeneous_inf_sup_eq
    (A B : Ideal (MvPolynomial (Fin n) K)) (hA : IsHomog A) (hB : IsHomog B) (e : ℕ) :
    degreeIdealPiece (K := K) (n := n) (A ⊔ B) e =
      degreeIdealPiece (K := K) (n := n) A e ⊔
        degreeIdealPiece (K := K) (n := n) B e := by
  classical
  let V : Submodule K (MvPolynomial (Fin n) K) := homogeneousSubmodule (Fin n) K e
  change V ⊓ (idealSubmodule (K := K) (n := n) (A ⊔ B)) =
      (V ⊓ (idealSubmodule (K := K) (n := n) A)) ⊔
        (V ⊓ (idealSubmodule (K := K) (n := n) B))
  apply le_antisymm
  · intro x hx
    rcases hx with ⟨hxV, hxAB⟩
    have hxAB' : x ∈ A ⊔ B := hxAB
    rcases (show ∃ a ∈ A, ∃ b ∈ B, a + b = x by
      rw [Submodule.mem_sup] at hxAB'
      exact hxAB') with ⟨a, ha, b, hb, hab⟩
    have hxcomp :
        homogeneousComponent e x = homogeneousComponent e a + homogeneousComponent e b := by
      rw [← hab]
      simp
    have hxself : homogeneousComponent e x = x := by
      simpa using
        (MvPolynomial.homogeneousComponent_of_mem (m := e) (n := e) (p := x) hxV)
    rw [Submodule.mem_sup]
    refine ⟨homogeneousComponent e a, ?_, homogeneousComponent e b, ?_, ?_⟩
    · exact ⟨MvPolynomial.homogeneousComponent_mem e a, hA a ha e⟩
    · exact ⟨MvPolynomial.homogeneousComponent_mem e b, hB b hb e⟩
    · exact (hxself.symm.trans hxcomp).symm
  · exact sup_le
      (le_inf inf_le_left (le_trans inf_le_right (show idealSubmodule (K := K) (n := n) A ≤
        idealSubmodule (K := K) (n := n) (A ⊔ B) from
          fun x hx => (le_sup_left : A ≤ A ⊔ B) hx)))
      (le_inf inf_le_left (le_trans inf_le_right (show idealSubmodule (K := K) (n := n) B ≤
        idealSubmodule (K := K) (n := n) (A ⊔ B) from
          fun x hx => (le_sup_right : B ≤ A ⊔ B) hx)))

private lemma homogeneous_inf_inf_eq (A B : Ideal (MvPolynomial (Fin n) K)) (e : ℕ) :
    degreeIdealPiece (K := K) (n := n) (A ⊓ B) e =
      degreeIdealPiece (K := K) (n := n) A e ⊓
        degreeIdealPiece (K := K) (n := n) B e := by
  ext x
  simp [and_left_comm, and_assoc]

theorem HF_antitone {A B : Ideal (MvPolynomial (Fin n) K)} (hAB : A ≤ B) (e : ℕ) :
    HF B e ≤ HF A e := by
  let V : Submodule K (MvPolynomial (Fin n) K) := homogeneousSubmodule (Fin n) K e
  let q : MvPolynomial (Fin n) K ⧸ A →ₗ[K] MvPolynomial (Fin n) K ⧸ B :=
    (Ideal.Quotient.factorₐ K hAB).toLinearMap
  have hmap :
      (Submodule.map (Ideal.Quotient.mkₐ K A).toLinearMap V).map q =
        Submodule.map (Ideal.Quotient.mkₐ K B).toLinearMap V := by
    rw [← Submodule.map_comp]
    rfl
  unfold HF
  change Module.finrank K (Submodule.map (Ideal.Quotient.mkₐ K B).toLinearMap V) ≤
    Module.finrank K (Submodule.map (Ideal.Quotient.mkₐ K A).toLinearMap V)
  rw [← hmap]
  exact Submodule.finrank_map_le q (Submodule.map (Ideal.Quotient.mkₐ K A).toLinearMap V)

set_option maxHeartbeats 1600000 in
theorem HF_inf_add_sup (A B : Ideal (MvPolynomial (Fin n) K))
    (hA : IsHomog A) (hB : IsHomog B) (e : ℕ) :
    HF (A ⊓ B) e + HF (A ⊔ B) e = HF A e + HF B e := by
  let V : Submodule K (MvPolynomial (Fin n) K) := homogeneousSubmodule (Fin n) K e
  let SA : Submodule K (MvPolynomial (Fin n) K) := degreeIdealPiece (K := K) (n := n) A e
  let SB : Submodule K (MvPolynomial (Fin n) K) := degreeIdealPiece (K := K) (n := n) B e
  let SInf : Submodule K (MvPolynomial (Fin n) K) := degreeIdealPiece (K := K) (n := n) (A ⊓ B) e
  let SSup : Submodule K (MvPolynomial (Fin n) K) := degreeIdealPiece (K := K) (n := n) (A ⊔ B) e
  let SAinfSB : Submodule K (MvPolynomial (Fin n) K) := SA ⊓ SB
  let SAsupSB : Submodule K (MvPolynomial (Fin n) K) := SA ⊔ SB
  have hInf : SInf = SAinfSB := by
    simpa [SInf, SAinfSB, SA, SB] using homogeneous_inf_inf_eq (K := K) (n := n) A B e
  have hSup : SSup = SAsupSB := by
    simpa [SSup, SAsupSB, SA, SB] using homogeneous_inf_sup_eq (K := K) (n := n) A B hA hB e
  have hdim : Module.finrank K SAsupSB + Module.finrank K SAinfSB =
      Module.finrank K SA + Module.finrank K SB := by
    simpa [SAsupSB, SAinfSB] using Submodule.finrank_sup_add_finrank_inf_eq SA SB
  have hdim' : Module.finrank K SSup + Module.finrank K SInf =
      Module.finrank K SA + Module.finrank K SB := by
    rw [hSup, hInf]
    exact hdim
  have hSA_le : SA ≤ V := by
    intro x hx
    exact hx.1
  have hSB_le : SB ≤ V := by
    intro x hx
    exact hx.1
  have hSA : Module.finrank K SA ≤ Module.finrank K V := by
    exact Submodule.finrank_mono hSA_le
  have hSB : Module.finrank K SB ≤ Module.finrank K V := by
    exact Submodule.finrank_mono hSB_le
  have hSSup : Module.finrank K SSup ≤ Module.finrank K V := by
    exact Submodule.finrank_mono (show SSup ≤ V from by
      intro x hx
      exact hx.1)
  have hSInf : Module.finrank K SInf ≤ Module.finrank K V := by
    exact Submodule.finrank_mono (show SInf ≤ V from by
      intro x hx
      exact hx.1)
  /-
  have hSsup_le : SAsupSB ≤ V := by
    rw [← hSup]
    intro x hx
    exact hx.1
  have hSinf_le : SAinfSB ≤ V := by
    rw [← hInf]
    intro x hx
    exact hx.1
  have hSsup : Module.finrank K SAsupSB ≤ Module.finrank K V := by
    exact Submodule.finrank_mono hSsup_le
  have hSinf : Module.finrank K SAinfSB ≤ Module.finrank K V := by
    exact Submodule.finrank_mono hSinf_le
  -/
  rw [HF_eq_finrank_sub_inf (K := K) (n := n) (A ⊓ B) e,
    HF_eq_finrank_sub_inf (K := K) (n := n) (A ⊔ B) e,
    HF_eq_finrank_sub_inf (K := K) (n := n) A e,
    HF_eq_finrank_sub_inf (K := K) (n := n) B e]
  change
      (Module.finrank K V - Module.finrank K SInf) +
        (Module.finrank K V - Module.finrank K SSup) =
      (Module.finrank K V - Module.finrank K SA) +
        (Module.finrank K V - Module.finrank K SB)
  omega

-- `HF_top` is now provided by HilbertFunction.lean (identical statement).

theorem HF_le_choose (I : Ideal (MvPolynomial (Fin n) K)) (e : ℕ) :
    HF I e ≤ (e + (n - 1)).choose (n - 1) := by
  calc
    HF I e ≤ Module.finrank K (homogeneousSubmodule (Fin n) K e) := by
      dsimp [HF]
      exact Submodule.finrank_map_le (Ideal.Quotient.mkₐ K I).toLinearMap
        (homogeneousSubmodule (Fin n) K e)
    _ = Nat.multichoose n e := finrank_homogeneousSubmodule_eq_multichoose (K := K) (n := n) e
    _ ≤ (e + (n - 1)).choose (n - 1) := multichoose_le_degree_bound n e

end
