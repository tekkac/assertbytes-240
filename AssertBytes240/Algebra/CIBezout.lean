import AssertBytes240.Algebra.ParamSystem
import AssertBytes240.Algebra.Telescope
import AssertBytes240.Algebra.GenericSequence

/-!
# Assembly: complete-intersection affine Bézout, `finrank ≤ d ^ n`

Combines `GenericSequence` and the filtration telescope to prove the
complete-intersection finrank bound. This is the general-`n` input used by
`goal_0dim_finrank_degree_bound`.
-/

open RingTheory.Sequence MvPolynomial

/-- Complete-intersection affine Bézout bound, assembled. Same statement as
`ci_bezout_finrank` in `AssertBytes240.Algebra.lean`, which will defer to this. -/
theorem ci_bezout_finrank_assembled
    {K : Type*} [Field K] [IsAlgClosed K] {n : ℕ}
    (g : Fin n → MvPolynomial (Fin n) K) (d : ℕ) (hd_pos : 1 ≤ d)
    (hd : ∀ j, (g j).totalDegree ≤ d)
    [FiniteDimensional K (MvPolynomial (Fin n) K ⧸ Ideal.span (Set.range g))] :
    Module.finrank K (MvPolynomial (Fin n) K ⧸ Ideal.span (Set.range g)) ≤ d ^ n := by
  classical
  -- W2+W4: a weakly regular sequence of K-combinations of the gᵢ.
  obtain ⟨hs, hlen, hspan, hreg⟩ := exists_weaklyRegular_in_span g
  -- Members have degree ≤ d.
  have hdeg : ∀ x ∈ hs, MvPolynomial.totalDegree x ≤ d := by
    intro x hx
    exact ParamSystem.totalDegree_le_of_mem_span (Set.range g)
      (by rintro p ⟨i, rfl⟩; exact hd i) (hspan x hx)
  -- The chain of partial ideals and its phi-functions.
  let Jk : ℕ → Ideal (MvPolynomial (Fin n) K) := fun k => Ideal.ofList (hs.take k)
  let f : ℕ → ℕ → ℕ := fun k e => phi (Jk k) e
  -- Step inequalities from `phi_step` + weak regularity (plumbing:
  -- convert `IsWeaklyRegular R hs` at index k into
  -- `IsSMulRegular (R ⧸ Jk k) (hs.get k)` and `Jk (k+1) = Jk k ⊔ span {hs.get k}`).
  have hstep : ∀ k < n, (∀ e, d ≤ e → f (k+1) e + f k (e - d) ≤ f k e) ∧
      (∀ e, e < d → f (k+1) e ≤ f k e) := by
    intro k hk
    have hk_len : k < hs.length := by simpa [hlen] using hk
    let h : MvPolynomial (Fin n) K := hs[k]'hk_len
    have hmem : h ∈ hs := by
      dsimp [h]
      exact List.getElem_mem hk_len
    have hJsucc : Jk (k + 1) = Jk k ⊔ Ideal.span {h} := by
      dsimp [Jk, h]
      rw [← List.take_concat_get' hs k hk_len, Ideal.ofList_append, Ideal.ofList_singleton]
    have hregk0 :
        IsSMulRegular ((MvPolynomial (Fin n) K) ⧸
          (Jk k * ⊤ : Ideal (MvPolynomial (Fin n) K))) h := by
      dsimp [Jk, h]
      simpa using hreg.regular_mod_prev k hk_len
    have hregk : IsSMulRegular ((MvPolynomial (Fin n) K) ⧸ Jk k) h := by
      let e : ((MvPolynomial (Fin n) K) ⧸
          (Jk k * ⊤ : Ideal (MvPolynomial (Fin n) K))) ≃ₗ[MvPolynomial (Fin n) K]
          ((MvPolynomial (Fin n) K) ⧸ Jk k) :=
        (Ideal.quotientEquivAlgOfEq (MvPolynomial (Fin n) K)
          (by rw [Ideal.mul_top] : Jk k * ⊤ = Jk k)).toLinearEquiv
      exact (e.isSMulRegular_congr h).mp hregk0
    have hphi := phi_step (K := K) (n := n) (Jk k) h d (hdeg h hmem) hregk
    constructor
    · intro e hde
      simpa [f, hJsucc] using hphi.1 e hde
    · intro e _he
      simpa [f, hJsucc] using hphi.2 e
  -- Base bound.
  have h0 : ∀ e, f 0 e ≤ (e + n).choose n := by
    intro e
    simpa [f, Jk] using phi_le_choose (Jk 0) e
  -- The final phi is bounded by d ^ n.
  have hbound : ∀ e, phi (Jk n) e ≤ d ^ n := by
    intro e₀
    by_contra hgt
    push_neg at hgt
    have hB : ∀ e, e₀ ≤ e → d ^ n + 1 ≤ phi (Jk n) e := fun e he =>
      le_trans hgt (phi_mono (Jk n) he)
    have := final_bound_of_chain (m := n) (d := d) (B := d ^ n + 1) (e₀ := e₀)
      hd_pos hstep h0 (by intro e he; simpa [f] using hB e he)
    omega
  -- Exhaustion: the quotient by the list ideal is finite-dimensional, ≤ d ^ n.
  obtain ⟨hfin, hrank⟩ := finiteDimensional_of_phi_bounded (Jk n) (d ^ n) hbound
  -- The list ideal sits inside I.
  have hle : Jk n ≤ Ideal.span (Set.range g) := by
    have hW_le_I : Submodule.span K (Set.range g) ≤
        Submodule.restrictScalars K
          (Ideal.span (Set.range g) : Ideal (MvPolynomial (Fin n) K)) := by
      exact Submodule.span_le.mpr (by intro y hy; exact Ideal.subset_span hy)
    dsimp [Jk]
    rw [show hs.take n = hs by simp [hlen]]
    rw [Ideal.ofList, Ideal.span_le]
    intro x hx
    exact hW_le_I (hspan x hx)
  -- Conclude via the quotient-of-quotient surjection (inline mono step).
  haveI := hfin
  have hmono :
      Module.finrank K
          (MvPolynomial (Fin n) K ⧸ Ideal.span (Set.range g)) ≤
        Module.finrank K (MvPolynomial (Fin n) K ⧸ Jk n) := by
    let q : (MvPolynomial (Fin n) K ⧸ Jk n) →ₗ[K]
        (MvPolynomial (Fin n) K ⧸ Ideal.span (Set.range g)) :=
      (Ideal.Quotient.factorₐ K hle).toLinearMap
    have hsurj : Function.Surjective q := by
      simpa [q] using Ideal.Quotient.factor_surjective hle
    have hrange : LinearMap.range q = ⊤ := LinearMap.range_eq_top.mpr hsurj
    calc
      Module.finrank K (MvPolynomial (Fin n) K ⧸ Ideal.span (Set.range g)) =
          Module.finrank K (LinearMap.range q) := by
        rw [hrange, finrank_top]
      _ ≤ Module.finrank K (MvPolynomial (Fin n) K ⧸ Jk n) := LinearMap.finrank_range_le q
  exact hmono.trans hrank
