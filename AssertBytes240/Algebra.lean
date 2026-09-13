import AssertBytes240.Algebra.Bezout
import AssertBytes240.Algebra.ParamSystem
import AssertBytes240.Algebra.CIBezout
import AssertBytes240.Algebra.DivdegRecurrence
import AssertBytes240.Algebra.AffineTransfer

/-!
# Affine Bézout endpoint for AssertBytes-240

This aggregate module assembles the two-variable, complete-intersection,
homogeneous divided-degree, and affine-transfer results into the exported
component bound `goal_minimalPrimes_ncard_le`.
-/

noncomputable section
open MvPolynomial

/-! ## Finite-dimensional quotient bounds -/

/-- If `Xᵢ ^ d ∈ I` for every variable, the quotient has `K`-dimension at most
`d ^ n`.  Monomial-box spanning-set argument. -/
theorem goal_0dim_finrank_pure_power
    {K : Type*} [Field K] {n d : ℕ}
    (I : Ideal (MvPolynomial (Fin n) K))
    (hpow : ∀ i : Fin n, (MvPolynomial.X i) ^ d ∈ I)
    [FiniteDimensional K (MvPolynomial (Fin n) K ⧸ I)] :
    Module.finrank K (MvPolynomial (Fin n) K ⧸ I) ≤ d ^ n := by
  set Q := MvPolynomial (Fin n) K ⧸ I
  set mk : MvPolynomial (Fin n) K →ₐ[K] Q := Ideal.Quotient.mkₐ K I;
  have h_span : Submodule.span K (Set.range (fun g : Fin n → Fin d => mk (MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm (fun i => (g i : ℕ))) 1))) = ⊤ := by
    have h_span : ∀ α : Fin n →₀ ℕ, mk (MvPolynomial.monomial α 1) ∈ Submodule.span K (Set.range (fun g : Fin n → Fin d => mk (MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm (fun i => (g i : ℕ))) 1))) := by
      intro α
      by_cases hα : ∀ i, α i < d;
      · refine' Submodule.subset_span ⟨ fun i => ⟨ α i, hα i ⟩, _ ⟩ ; aesop;
      · obtain ⟨i, hi⟩ : ∃ i, α i ≥ d := by
          aesop
        have h_monomial_in_I : MvPolynomial.monomial α 1 ∈ I := by
          obtain ⟨β, hβ⟩ : ∃ β : Fin n →₀ ℕ, α = β + Finsupp.single i d := by
            refine' ⟨ α - Finsupp.single i d, _ ⟩;
            ext j; by_cases hj : j = i <;> simp +decide [ hj, hi ] ;
          simp_all +decide [ MvPolynomial.monomial_eq, Finsupp.single_apply ];
          simp +decide [ Finset.prod_eq_mul_prod_diff_singleton ( Finset.mem_univ i ), pow_add, mul_assoc ];
          exact I.mul_mem_left _ ( I.mul_mem_right _ ( hpow i ) )
        have h_mk_zero : mk (MvPolynomial.monomial α 1) = 0 := by
          exact Ideal.Quotient.eq_zero_iff_mem.mpr h_monomial_in_I
        simp [h_mk_zero];
    refine' eq_top_iff.mpr fun x hx => _;
    obtain ⟨ p, rfl ⟩ := Ideal.Quotient.mk_surjective x;
    rw [ MvPolynomial.as_sum p ];
    simp +decide only [map_sum];
    refine' Submodule.sum_mem _ fun α hα => _;
    convert Submodule.smul_mem _ ( p.coeff α ) ( h_span α ) using 1;
    erw [ Ideal.Quotient.eq ];
    simp +decide [ MvPolynomial.smul_monomial ];
  convert finrank_le_of_span_eq_top h_span using 1;
  simp +decide

/-- Adding relations can only shrink the quotient dimension: `R ⧸ J` is a
further quotient of `R ⧸ I` when `I ≤ J`. -/
theorem step_finrank_quotient_mono
    {K R : Type*} [Field K] [CommRing R] [Algebra K R]
    (I J : Ideal R) (hIJ : I ≤ J)
    [FiniteDimensional K (R ⧸ I)] [FiniteDimensional K (R ⧸ J)] :
    Module.finrank K (R ⧸ J) ≤ Module.finrank K (R ⧸ I) := by
  obtain ⟨f, hf⟩ : ∃ f : (R ⧸ I) →ₗ[K] (R ⧸ J), Function.Surjective f := by
    refine' ⟨ _, _ ⟩;
    refine' ( Ideal.Quotient.liftₐ I ( Ideal.Quotient.mkₐ K J ) _ ).toLinearMap;
    exact fun x hx => Ideal.Quotient.eq_zero_iff_mem.mpr ( hIJ hx );
    intro x; obtain ⟨ y, rfl ⟩ := Ideal.Quotient.mk_surjective x; use Ideal.Quotient.mk I y; aesop;
  convert LinearMap.finrank_range_add_finrank_ker f |> fun h => h ▸ Nat.le_add_right _ _ using 1;
  rw [ LinearMap.range_eq_top.mpr hf, finrank_top ]

/-- In an Artinian ring the minimal primes are exactly the maximal ideals. -/
theorem minimalPrimes_eq_maximal_of_artinian
    {A : Type*} [CommRing A] [IsArtinianRing A] :
    minimalPrimes A = {P : Ideal A | P.IsMaximal} := by
  ext P
  simp only [Set.mem_setOf_eq]
  constructor
  · intro hP
    have hp : P.IsPrime := hP.1.1
    exact hp.isMaximal'
  · intro hP
    haveI : P.IsPrime := hP.isPrime
    refine ⟨⟨inferInstance, bot_le⟩, ?_⟩
    intro Q hQ hQP
    haveI : Q.IsPrime := hQ.1
    have hQm : Q.IsMaximal := hQ.1.isMaximal'
    exact (hQm.eq_of_le hP.ne_top hQP).ge

/-- The number of maximal ideals of a finite-dimensional `K`-algebra is at most
its `K`-dimension. -/
theorem maximal_ncard_le_finrank
    {K A : Type*} [Field K] [CommRing A] [Algebra K A] [FiniteDimensional K A] :
    Set.ncard {P : Ideal A | P.IsMaximal} ≤ Module.finrank K A := by
  haveI : IsArtinianRing A := IsArtinianRing.of_finite K A
  have hfin : {P : Ideal A | P.IsMaximal}.Finite := IsArtinianRing.setOf_isMaximal_finite A
  haveI : Fintype {P : Ideal A | P.IsMaximal} := hfin.fintype
  set S := {P : Ideal A | P.IsMaximal} with hS
  let f : S → Ideal A := fun P => P.1
  have hcop : Pairwise (Function.onFun IsCoprime f) := by
    intro P Q hPQ
    show IsCoprime (f P) (f Q)
    rw [Ideal.isCoprime_iff_sup_eq]
    exact P.2.coprime_of_ne Q.2 (fun h => hPQ (Subtype.ext h))
  let φ : A →ₗ[K] (∀ P : S, A ⧸ f P) :=
    LinearMap.pi (fun P => (Ideal.Quotient.mkₐ K (f P)).toLinearMap)
  have hφ : Function.Surjective φ := by
    intro x
    obtain ⟨r, hr⟩ := Ideal.pi_quotient_surjective hcop x
    exact ⟨r, by ext P; simpa [φ] using hr P⟩
  have hpi : Set.ncard S ≤ Module.finrank K (∀ P : S, A ⧸ f P) := by
    rw [Module.finrank_pi_fintype]
    have hone : ∀ P : S, 1 ≤ Module.finrank K (A ⧸ f P) := by
      intro P
      haveI : (f P).IsMaximal := P.2
      haveI : Field (A ⧸ f P) := Ideal.Quotient.field _
      exact Module.finrank_pos
    calc Set.ncard S = Fintype.card S := by
              rw [Set.ncard_eq_toFinset_card']; simp [Set.toFinset_card]
      _ = ∑ _P : S, 1 := by simp
      _ ≤ ∑ P : S, Module.finrank K (A ⧸ f P) := Finset.sum_le_sum (fun P _ => hone P)
  refine hpi.trans ?_
  have h := LinearMap.finrank_range_add_finrank_ker φ
  rw [LinearMap.range_eq_top.mpr hφ, finrank_top] at h
  omega

/-- Component count is bounded by quotient dimension: a finite-dimensional
`K`-algebra is Artinian, its primes are maximal, and CRT embeds the product of
residue fields, each contributing ≥ 1 dimension. (0-dimensional bridge.) -/
theorem step_components_le_finrank
    {K R : Type*} [Field K] [CommRing R] [Algebra K R]
    (I : Ideal R) [FiniteDimensional K (R ⧸ I)] :
    Set.ncard I.minimalPrimes ≤ Module.finrank K (R ⧸ I) := by
  haveI : IsArtinianRing (R ⧸ I) := IsArtinianRing.of_finite K (R ⧸ I)
  rw [Ideal.minimalPrimes_eq_comap,
    Set.ncard_image_of_injective _
      (Ideal.comap_injective_of_surjective _ Ideal.Quotient.mk_surjective),
    minimalPrimes_eq_maximal_of_artinian]
  exact maximal_ncard_le_finrank

/-- Chain-B foothold: in a finite-dimensional quotient every coordinate is
integral over `K`, with a monic annihilator of degree at most the quotient
dimension (Cayley–Hamilton on multiplication-by-`Xᵢ`). -/
theorem step_mulX_monic_annihilator
    {K : Type*} [Field K] {n : ℕ} (I : Ideal (MvPolynomial (Fin n) K))
    [FiniteDimensional K (MvPolynomial (Fin n) K ⧸ I)] (i : Fin n) :
    ∃ p : Polynomial K, p.Monic ∧
      p.natDegree ≤ Module.finrank K (MvPolynomial (Fin n) K ⧸ I) ∧
      Polynomial.aeval (Ideal.Quotient.mk I (MvPolynomial.X i)) p = 0 := by
  set A := MvPolynomial (Fin n) K ⧸ I
  set x := Ideal.Quotient.mk I (MvPolynomial.X i)
  refine ⟨(Algebra.lmul K A x).charpoly, LinearMap.charpoly_monic _, ?_, ?_⟩
  · rw [LinearMap.charpoly_natDegree]
  · have h := LinearMap.aeval_self_charpoly (Algebra.lmul K A x)
    rw [Polynomial.aeval_algHom_apply] at h
    exact Algebra.lmul_injective (h.trans (map_zero _).symm)

/- ========================================================================
   AFFINE BÉZOUT CORE
   ======================================================================== -/

/-- Two-variable 0-dimensional finrank bound. -/
theorem goal_0dim_finrank_degree_bound_dim_two
    {K : Type*} [Field K] [IsAlgClosed K] {ι : Type*} [Fintype ι]
    (f : ι → MvPolynomial (Fin 2) K) (d : ℕ) (hd_pos : 1 ≤ d)
    (hd : ∀ i, (f i).totalDegree ≤ d)
    [FiniteDimensional K (MvPolynomial (Fin 2) K ⧸ Ideal.span (Set.range f))] :
    Module.finrank K (MvPolynomial (Fin 2) K ⧸ Ideal.span (Set.range f)) ≤ d ^ 2 := by
  obtain ⟨g, h, hg, hh, hco, hgd, hhd⟩ :=
    AffineBezout.exists_coprime_pair f d hd
  obtain ⟨hfin, hbound⟩ := AffineBezout.bezout_two_curves g h hco
  haveI := hfin
  have hsub : Ideal.span {g, h} ≤ Ideal.span (Set.range f) := by
    rw [Ideal.span_le]
    intro x hx
    rcases hx with hx | hx
    · subst hx; exact hg
    · simp only [Set.mem_singleton_iff] at hx; subst hx; exact hh
  calc Module.finrank K (MvPolynomial (Fin 2) K ⧸ Ideal.span (Set.range f))
      ≤ Module.finrank K (MvPolynomial (Fin 2) K ⧸ Ideal.span {g, h}) :=
        step_finrank_quotient_mono _ _ hsub
    _ ≤ g.totalDegree * h.totalDegree := hbound
    _ ≤ d * d := Nat.mul_le_mul hgd hhd
    _ = d ^ 2 := (sq d).symm

/-- Generic system of parameters: a 0-dimensional bounded-degree ideal has an
`n`-generated bounded-degree sub-ideal that remains 0-dimensional. -/
theorem reduce_to_n_generators
    {K : Type*} [Field K] [IsAlgClosed K] {n : ℕ} {ι : Type*} [Fintype ι]
    (f : ι → MvPolynomial (Fin n) K) (d : ℕ) (hd_pos : 1 ≤ d)
    (hd : ∀ i, (f i).totalDegree ≤ d)
    [FiniteDimensional K (MvPolynomial (Fin n) K ⧸ Ideal.span (Set.range f))] :
    ∃ g : Fin n → MvPolynomial (Fin n) K,
      (∀ j, (g j).totalDegree ≤ d) ∧
      Ideal.span (Set.range g) ≤ Ideal.span (Set.range f) ∧
      FiniteDimensional K (MvPolynomial (Fin n) K ⧸ Ideal.span (Set.range g)) := by
  classical
  -- `V` sits inside the ideal it generates.
  have hVI : Submodule.span K (Set.range f) ≤
      (Ideal.span (Set.range f)).restrictScalars K :=
    Submodule.span_le.2 (fun x hx => Ideal.subset_span hx)
  -- The ideal `span (range f)` is `0`-dimensional, so every prime over it has height `n`.
  have hdim : ∀ P : Ideal (MvPolynomial (Fin n) K), P.IsPrime →
      Ideal.span ((Submodule.span K (Set.range f) : Submodule K (MvPolynomial (Fin n) K)) :
        Set (MvPolynomial (Fin n) K)) ≤ P → P.height = (n : ℕ∞) := by
    intro P hP hsub
    have hfP : Ideal.span (Set.range f) ≤ P :=
      (Ideal.span_mono Submodule.subset_span).trans hsub
    exact ParamSystem.primeHeight_eq_of_finiteDim (Ideal.span (Set.range f)) hP hfP
  obtain ⟨g, hgV, hgh⟩ :=
    ParamSystem.exists_sop_aux (Submodule.span K (Set.range f)) hdim n le_rfl
  refine ⟨g, ?_, ?_, ?_⟩
  · intro j
    exact ParamSystem.totalDegree_le_of_mem_span (Set.range f)
      (by rintro p ⟨i, rfl⟩; exact hd i) (hgV j)
  · rw [Ideal.span_le]
    rintro x ⟨j, rfl⟩
    simpa using hVI (hgV j)
  · exact ParamSystem.finiteDimensional_of_minimalPrimes_height (Ideal.span (Set.range g)) hgh

/-- Complete-intersection affine Bézout: `n` bounded-degree equations in `n`
variables with 0-dimensional quotient have `finrank ≤ d ^ n`. -/
theorem ci_bezout_finrank
    {K : Type*} [Field K] [IsAlgClosed K] {n : ℕ}
    (g : Fin n → MvPolynomial (Fin n) K) (d : ℕ) (hd_pos : 1 ≤ d)
    (hd : ∀ j, (g j).totalDegree ≤ d)
    [FiniteDimensional K (MvPolynomial (Fin n) K ⧸ Ideal.span (Set.range g))] :
    Module.finrank K (MvPolynomial (Fin n) K ⧸ Ideal.span (Set.range g)) ≤ d ^ n :=
  ci_bezout_finrank_assembled g d hd_pos hd

/-- General 0-dimensional affine Bézout finrank bound. -/
theorem goal_0dim_finrank_degree_bound
    {K : Type*} [Field K] [IsAlgClosed K] {n : ℕ} {ι : Type*} [Fintype ι]
    (f : ι → MvPolynomial (Fin n) K) (d : ℕ) (hd_pos : 1 ≤ d)
    (hd : ∀ i, (f i).totalDegree ≤ d)
    [FiniteDimensional K (MvPolynomial (Fin n) K ⧸ Ideal.span (Set.range f))] :
    Module.finrank K (MvPolynomial (Fin n) K ⧸ Ideal.span (Set.range f)) ≤ d ^ n := by
  obtain ⟨g, hgd, hsub, hgfin⟩ := reduce_to_n_generators f d hd_pos hd
  haveI := hgfin
  calc Module.finrank K (MvPolynomial (Fin n) K ⧸ Ideal.span (Set.range f))
      ≤ Module.finrank K (MvPolynomial (Fin n) K ⧸ Ideal.span (Set.range g)) :=
        step_finrank_quotient_mono _ _ hsub
    _ ≤ d ^ n := ci_bezout_finrank g d hd_pos hgd

private theorem pow_min_eq_min_pow (d C n : ℕ) (hd : 1 ≤ d) :
    d ^ min C n = min (d ^ C) (d ^ n) := by
  by_cases hCn : C ≤ n
  · rw [min_eq_left hCn, min_eq_left]
    exact pow_le_pow_right' hd hCn
  · have hnC : n ≤ C := le_of_not_ge hCn
    rw [min_eq_right hnC, min_eq_right]
    exact pow_le_pow_right' hd hnC

private theorem span_range_eq_top_of_nonzero_totalDegree_zero
    {K : Type*} [Field K] {n C : ℕ}
    {f : Fin C → MvPolynomial (Fin n) K}
    (h : ∃ i, f i ≠ 0 ∧ (f i).totalDegree = 0) :
    Ideal.span (Set.range f) = ⊤ := by
  classical
  obtain ⟨i, hfi_ne, hfi_deg⟩ := h
  have hfi_C : f i = MvPolynomial.C ((f i).coeff 0) :=
    (MvPolynomial.totalDegree_eq_zero_iff_eq_C (p := f i)).mp hfi_deg
  have hcoeff_ne : (f i).coeff 0 ≠ 0 := by
    intro hcoeff
    apply hfi_ne
    rw [hfi_C, hcoeff, map_zero]
  have hunit : IsUnit (f i) := by
    rw [MvPolynomial.isUnit_iff_eq_C_of_isReduced]
    exact ⟨(f i).coeff 0, hcoeff_ne.isUnit, hfi_C⟩
  exact (Ideal.span (Set.range f)).eq_top_of_isUnit_mem
    (Ideal.subset_span (Set.mem_range_self i : f i ∈ Set.range f)) hunit

private theorem affine_minimalPrimes_ncard_le_aux
    {K : Type*} [Field K] [IsAlgClosed K] {n C : ℕ}
    (f : Fin C → MvPolynomial (Fin n) K) (d : ℕ) (hd_pos : 1 ≤ d)
    (hd : ∀ i, (f i).totalDegree ≤ d) :
    Set.ncard (Ideal.span (Set.range f)).minimalPrimes ≤ min (d ^ C) (d ^ n) := by
  classical
  by_cases hconst : ∃ i, f i ≠ 0 ∧ (f i).totalDegree = 0
  · have htop : Ideal.span (Set.range f) = ⊤ :=
      span_range_eq_top_of_nonzero_totalDegree_zero hconst
    rw [htop, Ideal.minimalPrimes_top]
    simp
  · let S : Set (Ideal (MvPolynomial (Fin n) K)) :=
      (Ideal.span (Set.range f)).minimalPrimes
    let T : Set (Ideal (MvPolynomial (Fin (n + 1)) K)) :=
      {p ∈ (Ideal.span (Set.range (fun i => homog (f i)))).minimalPrimes |
        p ≠ varsIdeal (K := K) (n := n + 1)}
    have hfh :
        ∀ i : Fin C, ∃ e : ℕ, 1 ≤ e ∧ e ≤ d ∧
          homog (f i) ∈ homogeneousSubmodule (Fin (n + 1)) K e := by
      intro i
      by_cases hzero : f i = 0
      · refine ⟨1, le_rfl, hd_pos, ?_⟩
        simp [hzero, homog_zero]
      · have hdeg_ne : (f i).totalDegree ≠ 0 := by
          intro hdeg
          exact hconst ⟨i, hzero, hdeg⟩
        refine ⟨(f i).totalDegree, ?_, hd i, homog_homogeneous (f i)⟩
        omega
    have hhom_bound :
        Set.ncard T ≤ d ^ min C n := by
      have h :=
        homog_relevant_minimalPrimes_ncard_le (K := K) (n := n + 1)
          (C := C) (fun i => homog (f i)) d hd_pos hfh
      simpa [T] using h
    have hTfinite : T.Finite := by
      exact Set.Finite.subset
        (Ideal.finite_minimalPrimes_of_isNoetherianRing
          (MvPolynomial (Fin (n + 1)) K)
          (Ideal.span (Set.range (fun i => homog (f i)))))
        (by intro p hp; exact hp.1)
    have hmaps : ∀ p ∈ S, idealHomog p ∈ T := by
      intro p hp
      constructor
      · exact idealHomog_mem_minimalPrimes f hp
      · intro hpvars
        haveI : p.IsPrime := hp.1.1
        have hXnot :
            X (0 : Fin (n + 1)) ∉ idealHomog p :=
          X0_notMem_idealHomog_of_prime p
            ((show p.IsPrime from inferInstance).ne_top)
        exact hXnot (by
          rw [hpvars]
          exact Ideal.subset_span
            (Set.mem_range_self (0 : Fin (n + 1)) :
              X (0 : Fin (n + 1)) ∈
                Set.range (X : Fin (n + 1) → MvPolynomial (Fin (n + 1)) K)))
    have hinj : Set.InjOn (fun p => idealHomog p) S := by
      intro p hp q hq hpq
      have hmap := congrArg
        (fun J : Ideal (MvPolynomial (Fin (n + 1)) K) =>
          J.map (dehomog (K := K) (n := n)).toRingHom) hpq
      change
        (idealHomog p).map (dehomog (K := K) (n := n)).toRingHom =
          (idealHomog q).map (dehomog (K := K) (n := n)).toRingHom at hmap
      rw [dehomog_idealHomog (K := K) (n := n) p,
        dehomog_idealHomog (K := K) (n := n) q] at hmap
      exact hmap
    calc
      Set.ncard (Ideal.span (Set.range f)).minimalPrimes
          = Set.ncard S := rfl
      _ ≤ Set.ncard T := Set.ncard_le_ncard_of_injOn
        (fun p => idealHomog p) hmaps hinj hTfinite
      _ ≤ d ^ min C n := hhom_bound
      _ = min (d ^ C) (d ^ n) := pow_min_eq_min_pow d C n hd_pos

/-- Two-variable affine Bézout component bound. -/
theorem goal_minimalPrimes_ncard_le_dim_two
    {K : Type*} [Field K] [IsAlgClosed K] {C : ℕ}
    (f : Fin C → MvPolynomial (Fin 2) K) (d : ℕ) (hd_pos : 1 ≤ d)
    (hd : ∀ i, (f i).totalDegree ≤ d) :
    Set.ncard (Ideal.span (Set.range f)).minimalPrimes ≤ min (d ^ C) (d ^ 2) :=
  affine_minimalPrimes_ncard_le_aux f d hd_pos hd

/-- General affine Bézout component bound exported to the AssertBytes interface. -/
theorem goal_minimalPrimes_ncard_le
    {K : Type*} [Field K] [IsAlgClosed K] {n C : ℕ}
    (f : Fin C → MvPolynomial (Fin n) K) (d : ℕ) (hd_pos : 1 ≤ d)
    (hd : ∀ i, (f i).totalDegree ≤ d) :
    Set.ncard (Ideal.span (Set.range f)).minimalPrimes ≤ min (d ^ C) (d ^ n) :=
  affine_minimalPrimes_ncard_le_aux f d hd_pos hd

/- ========================================================================
   0-DIMENSIONAL COMPONENT COMPOSITION
   ======================================================================== -/

/-- The 0-dimensional component bound follows from the structural bridge and the
finrank bound. -/
theorem components_0dim_from_finrank
    {K : Type*} [Field K] [IsAlgClosed K] {n : ℕ} {ι : Type*} [Fintype ι]
    (f : ι → MvPolynomial (Fin n) K) (d : ℕ) (hd_pos : 1 ≤ d)
    (hd : ∀ i, (f i).totalDegree ≤ d)
    [FiniteDimensional K (MvPolynomial (Fin n) K ⧸ Ideal.span (Set.range f))] :
    Set.ncard (Ideal.span (Set.range f)).minimalPrimes ≤ d ^ n :=
  (step_components_le_finrank (Ideal.span (Set.range f))).trans
    (goal_0dim_finrank_degree_bound f d hd_pos hd)
