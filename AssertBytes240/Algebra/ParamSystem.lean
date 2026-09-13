import Mathlib

/-!
# Generic system of parameters (support file for `reduce_to_n_generators`)

Provides prime avoidance, height facts for polynomial rings, and
`exists_sop_aux`, which chooses a system of parameters inside a finite
dimensional ideal. The aggregate affine bound uses this in
`reduce_to_n_generators`.
-/

noncomputable section
open MvPolynomial

namespace ParamSystem

/-- Elements of a `K`-span of polynomials of total degree `≤ d` again have total degree `≤ d`. -/
theorem totalDegree_le_of_mem_span
    {K σ : Type*} [Field K] {d : ℕ} (S : Set (MvPolynomial σ K))
    (hS : ∀ p ∈ S, p.totalDegree ≤ d) {v : MvPolynomial σ K}
    (hv : v ∈ Submodule.span K S) : v.totalDegree ≤ d := by
  induction hv using Submodule.span_induction with
  | mem x hx => exact hS x hx
  | zero => simp
  | add x y _ _ hx hy => exact (MvPolynomial.totalDegree_add x y).trans (max_le hx hy)
  | smul a x _ hx => exact (MvPolynomial.totalDegree_smul_le a x).trans hx

/-- **Prime avoidance over an infinite field.**  If a `K`-subspace `V` of a `K`-algebra `R`
is not contained in any of finitely many ideals `P`, then some vector of `V` avoids all of them. -/
theorem exists_mem_avoiding_finset
    {K R : Type*} [Field K] [Infinite K] [CommRing R] [Algebra K R]
    (V : Submodule K R) (s : Finset (Ideal R))
    (hs : ∀ P ∈ s, ¬ V ≤ Submodule.restrictScalars K P) :
    ∃ v ∈ V, ∀ P ∈ s, v ∉ P := by
  classical
  set p : {P // P ∈ s} → Subspace K V :=
    fun P => Submodule.comap V.subtype (Submodule.restrictScalars K P.1) with hp
  by_contra hcon
  push_neg at hcon
  have hcov : (⋃ i : {P // P ∈ s}, (p i : Set V)) = Set.univ := by
    ext w
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    obtain ⟨P, hP, hwP⟩ := hcon w.1 w.2
    exact ⟨⟨P, hP⟩, by simpa [hp, Submodule.mem_comap] using hwP⟩
  obtain ⟨i, hi⟩ := Subspace.exists_eq_top_of_iUnion_eq_univ hcov
  apply hs i.1 i.2
  intro x hx
  have hmem : (⟨x, hx⟩ : V) ∈ p i := by rw [hi]; trivial
  simpa [hp, Submodule.mem_comap] using hmem

/-- Every maximal ideal of `K[x₁,…,xₙ]` has height `n` (equidimensionality). -/
theorem height_maximal
    {K : Type*} [Field K] (n : ℕ) (M : Ideal (MvPolynomial (Fin n) K)) [M.IsMaximal] :
    M.height = (n : ℕ∞) := by
  suffices h : ∀ (m : ℕ) (N : Ideal (MvPolynomial (Fin m) K)), N.IsMaximal →
      N.height = (m : ℕ∞) by
    exact h n M ‹_›
  intro m
  induction m with
  | zero =>
    intro N hN
    haveI := hN
    have h1 : N.height ≤ ringKrullDim (MvPolynomial (Fin 0) K) :=
      Ideal.height_le_ringKrullDim_of_ne_top hN.ne_top
    have h2 : ringKrullDim (MvPolynomial (Fin 0) K) = (0 : WithBot ℕ∞) := by
      rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field K]; simp
    rw [h2] at h1
    have hle : N.height ≤ 0 := by exact_mod_cast h1
    simpa using hle
  | succ m ih =>
    intro N hN
    haveI := hN
    let e := (MvPolynomial.finSuccEquiv K m).toRingEquiv
    haveI hMmax : (N.map e).IsMaximal := inferInstance
    haveI hpmax : ((N.map e).comap Polynomial.C).IsMaximal :=
      Polynomial.isMaximal_comap_C_of_isJacobsonRing (N.map e)
    haveI : (N.map e).LiesOver ((N.map e).comap Polynomial.C) := ⟨rfl⟩
    have hht : (N.map e).height = ((N.map e).comap Polynomial.C).height + 1 :=
      Polynomial.height_eq_height_add_one _ (N.map e)
    have hp_ht : ((N.map e).comap Polynomial.C).height = (m : ℕ∞) := ih _ hpmax
    have hN_ht : N.height = (N.map e).height := (RingEquiv.height_map e N).symm
    rw [hN_ht, hht, hp_ht]
    push_cast; ring

/-- In a `0`-dimensional ideal (finite-dimensional quotient) of `K[x₁,…,xₙ]`, every prime
containing it has prime height `n`. -/
theorem primeHeight_eq_of_finiteDim
    {K : Type*} [Field K] {n : ℕ} (I : Ideal (MvPolynomial (Fin n) K))
    [FiniteDimensional K (MvPolynomial (Fin n) K ⧸ I)]
    {P : Ideal (MvPolynomial (Fin n) K)} (hP : P.IsPrime) (hIP : I ≤ P) :
    P.height = (n : ℕ∞) := by
  set R := MvPolynomial (Fin n) K
  haveI hk : Ring.KrullDimLE 0 (R ⧸ I) :=
    (Module.finite_iff_krullDimLE_zero K (R ⧸ I)).mp inferInstance
  haveI hPmax : P.IsMaximal := by
    have h𝕮 : (P.map (Ideal.Quotient.mk I)).IsPrime :=
      Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective
        (le_trans (le_of_eq Ideal.mk_ker) hIP)
    have h𝕮max : (P.map (Ideal.Quotient.mk I)).IsMaximal :=
      Ring.krullDimLE_zero_iff.mp hk _ h𝕮
    have hcm := Ideal.comap_isMaximal_of_surjective (Ideal.Quotient.mk I)
      Ideal.Quotient.mk_surjective (K := P.map (Ideal.Quotient.mk I)) (H := h𝕮max)
    rwa [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
      ← RingHom.ker_eq_comap_bot, Ideal.mk_ker, sup_eq_left.mpr hIP] at hcm
  exact height_maximal n P

/-- If every minimal prime of `J` has prime height `≥ n`, then `K[x₁,…,xₙ]/J` is
finite-dimensional. -/
theorem finiteDimensional_of_minimalPrimes_height
    {K : Type*} [Field K] {n : ℕ} (J : Ideal (MvPolynomial (Fin n) K))
    (h : ∀ P ∈ J.minimalPrimes, (n : ℕ∞) ≤ P.height) :
    FiniteDimensional K (MvPolynomial (Fin n) K ⧸ J) := by
  set R := MvPolynomial (Fin n) K
  have hdim : ringKrullDim R = (n : WithBot ℕ∞) := by
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field K]; simp
  haveI : FiniteRingKrullDim R := by
    rw [finiteRingKrullDim_iff_ne_bot_and_top, hdim]
    exact ⟨by simp, Ne.symm (not_eq_of_beq_eq_false rfl)⟩
  have hmax : ∀ Q : Ideal R, Q.IsPrime → J ≤ Q → Q.IsMaximal := by
    intro Q hQ hJQ
    obtain ⟨P, hP, hPQ⟩ := Ideal.exists_minimalPrimes_le hJQ
    haveI : P.IsPrime := Ideal.minimalPrimes_isPrime hP
    have hPn : P.primeHeight = ringKrullDim R := by
      have h1 : P.primeHeight ≤ ringKrullDim R := Ideal.primeHeight_le_ringKrullDim
      have h2 : (n : ℕ∞) ≤ P.primeHeight := by
        have := h P hP; rwa [Ideal.height_eq_primeHeight] at this
      rw [hdim] at h1 ⊢
      exact le_antisymm h1 (by exact_mod_cast h2)
    have hPmax : P.IsMaximal := Ideal.isMaximal_of_primeHeight_eq_ringKrullDim hPn
    exact hPmax.eq_of_le hQ.ne_top hPQ ▸ hPmax
  haveI : Ring.KrullDimLE 0 (R ⧸ J) := by
    rw [Ring.krullDimLE_zero_iff]
    intro 𝕮 h𝕮
    haveI hQmax : (𝕮.comap (Ideal.Quotient.mk J)).IsMaximal :=
      hmax _ (h𝕮.comap _) (le_trans (le_of_eq (Ideal.mk_ker).symm) (Ideal.ker_le_comap _))
    have hmap := Ideal.IsMaximal.map_of_surjective_of_ker_le (f := Ideal.Quotient.mk J)
        Ideal.Quotient.mk_surjective (m := 𝕮.comap (Ideal.Quotient.mk J))
        (Ideal.ker_le_comap _)
    rwa [Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective] at hmap
  exact (Module.finite_iff_krullDimLE_zero K (R ⧸ J)).mpr this

/-- **Inductive core.**  Building `k` generic elements of `V` whose span has all minimal primes
of height `≥ k`, for a `0`-dimensional `V`. -/
theorem exists_sop_aux
    {K : Type*} [Field K] [Infinite K] {n : ℕ}
    (V : Submodule K (MvPolynomial (Fin n) K))
    (hdim : ∀ P : Ideal (MvPolynomial (Fin n) K), P.IsPrime →
        Ideal.span (V : Set (MvPolynomial (Fin n) K)) ≤ P → P.height = (n : ℕ∞)) :
    ∀ k : ℕ, k ≤ n → ∃ g : Fin k → MvPolynomial (Fin n) K,
      (∀ j, g j ∈ V) ∧
      ∀ P ∈ (Ideal.span (Set.range g)).minimalPrimes, (k : ℕ∞) ≤ P.height := by
  classical
  intro k
  induction k with
  | zero =>
    intro _
    exact ⟨Fin.elim0, fun j => j.elim0, fun P _ => by simp⟩
  | succ k ih =>
    intro hk1
    obtain ⟨g, hgV, hgh⟩ := ih (Nat.le_of_succ_le hk1)
    have hfin : (Ideal.span (Set.range g)).minimalPrimes.Finite :=
      Ideal.finite_minimalPrimes_of_isNoetherianRing _ (Ideal.span (Set.range g))
    have havoid : ∀ P ∈ (Ideal.span (Set.range g)).minimalPrimes,
        ¬ V ≤ Submodule.restrictScalars K P := by
      intro P hP hVP
      haveI : P.IsPrime := Ideal.minimalPrimes_isPrime hP
      have hspan : Ideal.span (V : Set (MvPolynomial (Fin n) K)) ≤ P := by
        rw [Ideal.span_le]; intro x hx; exact hVP hx
      have hPn : P.height = (n : ℕ∞) := hdim P inferInstance hspan
      have hle : P.height ≤ ((Set.range g).ncard : ℕ∞) :=
        Ideal.height_le_card_of_mem_minimalPrimes_span (Set.finite_range g) hP
      have hcard : (Set.range g).ncard ≤ k := by
        rw [← Set.image_univ]
        exact (Set.ncard_image_le (Set.finite_univ)).trans (by simp [Set.ncard_univ])
      rw [hPn] at hle
      have h1 : (n : ℕ∞) ≤ (k : ℕ∞) := hle.trans (by exact_mod_cast hcard)
      have : n ≤ k := by exact_mod_cast h1
      omega
    obtain ⟨v, hvV, hvP⟩ :=
      exists_mem_avoiding_finset V hfin.toFinset
        (fun P hP => havoid P (hfin.mem_toFinset.mp hP))
    refine ⟨Fin.snoc g v, ?_, ?_⟩
    · intro j
      refine Fin.lastCases ?_ ?_ j
      · simpa using hvV
      · intro i; simpa using hgV i
    · intro Q hQ
      haveI : Q.IsPrime := Ideal.minimalPrimes_isPrime hQ
      have hrange : Set.range (Fin.snoc g v) = insert v (Set.range g) := Fin.range_snoc g v
      have hJQ : Ideal.span (Set.range g) ≤ Q := by
        refine le_trans (Ideal.span_mono ?_) hQ.1.2
        rw [hrange]; exact Set.subset_insert _ _
      have hvQ : v ∈ Q := by
        have hvs : v ∈ Ideal.span (Set.range (Fin.snoc g v)) := by
          apply Ideal.subset_span; rw [hrange]; exact Set.mem_insert _ _
        exact hQ.1.2 hvs
      obtain ⟨P, hP, hPQ⟩ := Ideal.exists_minimalPrimes_le hJQ
      haveI : P.IsPrime := Ideal.minimalPrimes_isPrime hP
      have hvnP : v ∉ P := hvP P (hfin.mem_toFinset.mpr hP)
      have hlt : P < Q := lt_of_le_of_ne hPQ (by rintro rfl; exact hvnP hvQ)
      have hstep : P.primeHeight + 1 ≤ Q.primeHeight :=
        Ideal.primeHeight_add_one_le_of_lt hlt
      have hPk : (k : ℕ∞) ≤ P.primeHeight := by
        have := hgh P hP; rwa [Ideal.height_eq_primeHeight] at this
      rw [Ideal.height_eq_primeHeight]
      calc ((k + 1 : ℕ) : ℕ∞) = (k : ℕ∞) + 1 := by push_cast; ring
        _ ≤ P.primeHeight + 1 := by gcongr
        _ ≤ Q.primeHeight := hstep

end ParamSystem
