import Mathlib

/-!
# Finite scalar projections and minimal-prime components

Instead of constructing a bounded elimination quotient of `K[X]`, it is enough
to bound the number of minimal-prime components of the quadric ideal.  If the
scalar image is finite, the product `prod (ell - c)` over that image vanishes
on the locus.  Nullstellensatz puts this product in the radical, and primality
forces one factor `ell - c` into each minimal prime, making the scalar
projection constant on that component.

This file contains the axiom-free projection and component-count layer used by
the completed affine Bezout theorem in `AssertBytes240.Algebra`.
-/

noncomputable section

open MvPolynomial
open scoped BigOperators

namespace ZkGolfOptimality
namespace ComponentBound

attribute [local instance] UniqueFactorizationMonoid.normalizationMonoid

/--
A finite cover of `S` by pieces on which `f` has a specified constant value.

This is deliberately topological-geometry-free.  Irreducible components can be
plugged in later by proving they provide such a cover.
-/
structure ScalarConstantCover (α β : Type*) (S : Set α) (f : α → β) where
  ι : Type*
  fintype : Fintype ι
  pieces : ι → Set α
  value : ι → β
  covers : S ⊆ ⋃ i, pieces i
  constant : ∀ ⦃i : ι⦄ ⦃x : α⦄, x ∈ S → x ∈ pieces i → f x = value i

namespace ScalarConstantCover

/-- The number of pieces in a scalar-constant cover. -/
def card {α β : Type*} {S : Set α} {f : α → β}
    (cover : ScalarConstantCover α β S f) : ℕ := by
  letI := cover.fintype
  exact Fintype.card cover.ι

theorem image_ncard_le {α β : Type*} {S : Set α} {f : α → β}
    (cover : ScalarConstantCover α β S f) :
    (f '' S).ncard ≤ cover.card := by
  classical
  letI := cover.fintype
  have hsub : f '' S ⊆ cover.value '' (Set.univ : Set cover.ι) := by
    rintro y ⟨x, hxS, rfl⟩
    rcases Set.mem_iUnion.mp (cover.covers hxS) with ⟨i, hxi⟩
    exact ⟨i, Set.mem_univ i, (cover.constant hxS hxi).symm⟩
  calc
    (f '' S).ncard ≤ (cover.value '' (Set.univ : Set cover.ι)).ncard :=
      Set.ncard_le_ncard hsub ((Set.finite_univ : (Set.univ : Set cover.ι).Finite).image _)
    _ ≤ (Set.univ : Set cover.ι).ncard :=
      Set.ncard_image_le (s := (Set.univ : Set cover.ι)) (f := cover.value)
    _ = cover.card := by
      simp [card, Set.ncard_univ, Nat.card_eq_fintype_card]

theorem image_ncard_le_of_card_le {α β : Type*} {S : Set α} {f : α → β}
    (cover : ScalarConstantCover α β S f) {M : ℕ} (hcard : cover.card ≤ M) :
    (f '' S).ncard ≤ M :=
  cover.image_ncard_le.trans hcard

end ScalarConstantCover

/--
A finite cover of `S` by irreducible pieces contained in `S`.

For the intended algebraic application, `S` is the quadric locus and the pieces
are its irreducible components.
-/
structure IrreducibleCover (α : Type*) [TopologicalSpace α] (S : Set α) where
  ι : Type*
  fintype : Fintype ι
  pieces : ι → Set α
  covers : S ⊆ ⋃ i, pieces i
  subset : ∀ i, pieces i ⊆ S
  irreducible : ∀ i, IsIrreducible (pieces i)

namespace IrreducibleCover

/-- The number of pieces in an irreducible cover. -/
def card {α : Type*} [TopologicalSpace α] {S : Set α}
    (cover : IrreducibleCover α S) : ℕ := by
  letI := cover.fintype
  exact Fintype.card cover.ι

/--
Topological core: a continuous map from an irreducible set to a finite subset
of a T1 space is constant on that set.
-/
theorem image_subsingleton_of_finite
    {α β : Type*} [TopologicalSpace α] [TopologicalSpace β] [T1Space β]
    {S : Set α} {f : α → β}
    (hS : IsIrreducible S) (hf : ContinuousOn f S)
    (hfin : (f '' S).Finite) :
    (f '' S).Subsingleton :=
  hfin.isDiscrete.subsingleton_of_isPreirreducible (hS.isPreirreducible.image f hf)

/--
Build a scalar-constant cover from an irreducible cover when the scalar image is
finite.
-/
def toScalarConstantCover
    {α β : Type*} [TopologicalSpace α] [TopologicalSpace β] [T1Space β]
    {S : Set α} {f : α → β}
    (cover : IrreducibleCover α S)
    (hf : ∀ i, ContinuousOn f (cover.pieces i))
    (hfin : (f '' S).Finite) :
    ScalarConstantCover α β S f where
  ι := cover.ι
  fintype := cover.fintype
  pieces := cover.pieces
  value := fun i => f (Classical.choose (cover.irreducible i).nonempty)
  covers := cover.covers
  constant := by
    intro i x hxS hxi
    let p : α := Classical.choose (cover.irreducible i).nonempty
    have hp : p ∈ cover.pieces i :=
      Classical.choose_spec (cover.irreducible i).nonempty
    have hfin_piece : (f '' cover.pieces i).Finite :=
      hfin.subset (by
        rintro y ⟨z, hz, rfl⟩
        exact ⟨z, cover.subset i hz, rfl⟩)
    have hsubsingleton : (f '' cover.pieces i).Subsingleton :=
      image_subsingleton_of_finite (cover.irreducible i) (hf i) hfin_piece
    exact hsubsingleton ⟨x, hxi, rfl⟩ ⟨p, hp, rfl⟩

/--
An irreducible cover with at most `M` pieces bounds a finite scalar image by
`M`.
-/
theorem image_ncard_le_of_card_le
    {α β : Type*} [TopologicalSpace α] [TopologicalSpace β] [T1Space β]
    {S : Set α} {f : α → β}
    (cover : IrreducibleCover α S)
    (hf : ∀ i, ContinuousOn f (cover.pieces i))
    (hfin : (f '' S).Finite)
    {M : ℕ} (hcard : cover.card ≤ M) :
    (f '' S).ncard ≤ M := by
  let scalarCover := cover.toScalarConstantCover hf hfin
  have hsame : scalarCover.card = cover.card := by
    simp [scalarCover, toScalarConstantCover, ScalarConstantCover.card, card]
  exact scalarCover.image_ncard_le_of_card_le (hsame.trans_le hcard)

end IrreducibleCover

/-- The affine locus cut out by a finite list of polynomials. -/
def polynomialLocus {K : Type*} [Field K] {n C : ℕ}
    (q : Fin C → MvPolynomial (Fin n) K) : Set (Fin n → K) :=
  MvPolynomial.zeroLocus K (Ideal.span (Set.range q))

/-- The coordinate-ring ideal generated by the defining quadratic equations. -/
def quadricIdeal {K : Type*} [Field K] {n C : ℕ}
    (q : Fin C → MvPolynomial (Fin n) K) : Ideal (MvPolynomial (Fin n) K) :=
  Ideal.span (Set.range q)

lemma polynomialLocus_eq_zeroLocus_quadricIdeal
    {K : Type*} [Field K] {n C : ℕ}
    (q : Fin C → MvPolynomial (Fin n) K) :
    polynomialLocus q = MvPolynomial.zeroLocus K (quadricIdeal q) :=
  rfl

/-- A polynomial-list locus where every defining polynomial is quadratic or less. -/
def IsQuadricSystem {K : Type*} [Field K] {n C : ℕ}
    (q : Fin C → MvPolynomial (Fin n) K) : Prop :=
  ∀ i, (q i).totalDegree ≤ 2

/--
The degree contribution of one equation in the component-count Bezout bound.

The `max 1` handles zero or constant equations: a zero equation should not make
the product bound collapse to zero.
-/
def degreeCap {K : Type*} [Field K] {n : ℕ}
    (p : MvPolynomial (Fin n) K) : ℕ :=
  max 1 p.totalDegree

/-- The analogous capped degree for univariate polynomials. -/
def polynomialDegreeCap {K : Type*} [Field K]
    (p : Polynomial K) : ℕ :=
  max 1 p.natDegree

lemma multiset_card_le_sum_of_one_le {s : Multiset ℕ}
    (h : ∀ a ∈ s, 1 ≤ a) :
    s.card ≤ s.sum := by
  induction s using Multiset.induction_on with
  | empty =>
      simp
  | cons a s ih =>
      rw [Multiset.card_cons, Multiset.sum_cons]
      have ha : 1 ≤ a := h a (by simp)
      have hs : s.card ≤ s.sum := ih (by
        intro b hb
        exact h b (by simp [hb]))
      omega

lemma totalDegree_pos_of_irreducible
    {K : Type*} [Field K] {n : ℕ}
    {p : MvPolynomial (Fin n) K}
    (hp : Irreducible p) :
    0 < p.totalDegree := by
  by_contra hnot
  have hdeg : p.totalDegree = 0 := Nat.eq_zero_of_not_pos hnot
  have hpC : p = MvPolynomial.C (MvPolynomial.coeff 0 p) :=
    MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp hdeg
  have hcoeff_ne : MvPolynomial.coeff 0 p ≠ 0 := by
    intro hcoeff
    have hpzero : p = 0 := by
      rw [hpC, hcoeff]
      simp
    exact hp.ne_zero hpzero
  have hunitCoeff : IsUnit (MvPolynomial.coeff 0 p) := isUnit_iff_ne_zero.mpr hcoeff_ne
  have hunit : IsUnit p := by
    rw [MvPolynomial.isUnit_iff_totalDegree_of_isReduced]
    exact ⟨hunitCoeff, hdeg⟩
  exact hp.not_isUnit hunit

lemma totalDegree_multiset_prod_eq_of_forall_ne_zero
    {K : Type*} [Field K] {n : ℕ}
    (s : Multiset (MvPolynomial (Fin n) K))
    (h : ∀ p ∈ s, p ≠ 0) :
    s.prod.totalDegree = (s.map MvPolynomial.totalDegree).sum := by
  induction s using Multiset.induction_on with
  | empty =>
      simp
  | cons p s ih =>
      have hp : p ≠ 0 := h p (by simp)
      have hs_prod : s.prod ≠ 0 := by
        apply Multiset.prod_ne_zero
        intro hzero
        exact h 0 (by simp [hzero]) rfl
      rw [Multiset.prod_cons, Multiset.map_cons, Multiset.sum_cons]
      rw [MvPolynomial.totalDegree_mul_of_isDomain hp hs_prod]
      rw [ih (by
        intro q hq
        exact h q (by simp [hq]))]

lemma normalizedFactors_toFinset_card_le_totalDegree
    {K : Type*} [Field K] {n : ℕ}
    [DecidableEq (MvPolynomial (Fin n) K)]
    (p : MvPolynomial (Fin n) K) (hp : p ≠ 0) :
    (UniqueFactorizationMonoid.normalizedFactors p).toFinset.card ≤ p.totalDegree := by
  classical
  let s := UniqueFactorizationMonoid.normalizedFactors p
  have hcard_to : s.toFinset.card ≤ s.card := Multiset.toFinset_card_le s
  have hone :
      s.card ≤ (s.map MvPolynomial.totalDegree).sum := by
    rw [← Multiset.card_map MvPolynomial.totalDegree s]
    apply multiset_card_le_sum_of_one_le
    intro d hd
    rcases Multiset.mem_map.mp hd with ⟨q, hq, rfl⟩
    exact totalDegree_pos_of_irreducible
      (UniqueFactorizationMonoid.irreducible_of_normalized_factor q (by simpa [s] using hq))
  have hprod_degree :
      s.prod.totalDegree = (s.map MvPolynomial.totalDegree).sum := by
    apply totalDegree_multiset_prod_eq_of_forall_ne_zero
    intro q hq
    exact UniqueFactorizationMonoid.ne_zero_of_mem_normalizedFactors (by simpa [s] using hq)
  have hprod_le : s.prod.totalDegree ≤ p.totalDegree := by
    exact MvPolynomial.totalDegree_le_of_dvd_of_isDomain
      (UniqueFactorizationMonoid.prod_normalizedFactors hp).dvd hp
  simpa [s] using hcard_to.trans (hone.trans (by simpa [hprod_degree] using hprod_le))

lemma principal_minimalPrimes_subset_span_primeFactors
    {K : Type*} [Field K] {n : ℕ}
    (p : MvPolynomial (Fin n) K) (hp : p ≠ 0) :
    (Ideal.span ({p} : Set (MvPolynomial (Fin n) K))).minimalPrimes ⊆
      (fun q => Ideal.span ({q} : Set (MvPolynomial (Fin n) K))) ''
        (UniqueFactorizationMonoid.primeFactors p : Set (MvPolynomial (Fin n) K)) := by
  classical
  intro P hP
  have hPPrime : P.IsPrime := Ideal.minimalPrimes_isPrime hP
  have hp_mem_P : p ∈ P := by
    exact (Ideal.span_singleton_le_iff_mem P).mp hP.1.2
  have hprod_mem :
      (UniqueFactorizationMonoid.normalizedFactors p).prod ∈ P := by
    exact P.mem_of_dvd (UniqueFactorizationMonoid.prod_normalizedFactors hp).symm.dvd hp_mem_P
  obtain ⟨q, hq_factor, hq_mem_P⟩ :=
    (hPPrime.multiset_prod_mem_iff_exists_mem
      (UniqueFactorizationMonoid.normalizedFactors p)).mp hprod_mem
  have hq_prime : Prime q :=
    UniqueFactorizationMonoid.prime_of_normalized_factor q hq_factor
  have hq_span_prime : (Ideal.span ({q} : Set (MvPolynomial (Fin n) K))).IsPrime :=
    (Ideal.span_singleton_prime hq_prime.ne_zero).mpr hq_prime
  have hp_mem_span_q : p ∈ Ideal.span ({q} : Set (MvPolynomial (Fin n) K)) := by
    exact Ideal.mem_span_singleton.mpr
      (UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hq_factor)
  have hp_span_le_q_span :
      Ideal.span ({p} : Set (MvPolynomial (Fin n) K)) ≤
        Ideal.span ({q} : Set (MvPolynomial (Fin n) K)) := by
    exact (Ideal.span_singleton_le_iff_mem _).mpr hp_mem_span_q
  have hq_span_le_P :
      Ideal.span ({q} : Set (MvPolynomial (Fin n) K)) ≤ P := by
    exact (Ideal.span_singleton_le_iff_mem P).mpr hq_mem_P
  have hP_le_q_span :
      P ≤ Ideal.span ({q} : Set (MvPolynomial (Fin n) K)) :=
    hP.2 ⟨hq_span_prime, hp_span_le_q_span⟩ hq_span_le_P
  have hP_eq : P = Ideal.span ({q} : Set (MvPolynomial (Fin n) K)) :=
    le_antisymm hP_le_q_span hq_span_le_P
  refine ⟨q, ?_, hP_eq.symm⟩
  simpa [UniqueFactorizationMonoid.mem_primeFactors] using hq_factor

theorem principal_minimalPrimes_ncard_le_degreeCap
    {K : Type*} [Field K] {n : ℕ}
    (p : MvPolynomial (Fin n) K) :
    Set.ncard (Ideal.span ({p} : Set (MvPolynomial (Fin n) K))).minimalPrimes ≤
      degreeCap p := by
  classical
  letI : DecidableEq (MvPolynomial (Fin n) K) := Classical.decEq _
  by_cases hp : p = 0
  · subst p
    have hspan :
        Ideal.span ({(0 : MvPolynomial (Fin n) K)} :
          Set (MvPolynomial (Fin n) K)) =
          (⊥ : Ideal (MvPolynomial (Fin n) K)) := by
      exact Ideal.span_singleton_eq_bot.mpr rfl
    calc
      Set.ncard (Ideal.span ({(0 : MvPolynomial (Fin n) K)} :
          Set (MvPolynomial (Fin n) K))).minimalPrimes = 1 := by
        rw [hspan]
        change Set.ncard (minimalPrimes (MvPolynomial (Fin n) K)) = 1
        rw [IsDomain.minimalPrimes_eq_singleton_bot]
        simp
      _ ≤ degreeCap (0 : MvPolynomial (Fin n) K) := by
        simp [degreeCap]
  · by_cases hunit : IsUnit p
    · have htop :
          Ideal.span ({p} : Set (MvPolynomial (Fin n) K)) =
            (⊤ : Ideal (MvPolynomial (Fin n) K)) := by
        exact Ideal.span_singleton_eq_top.mpr hunit
      rw [htop, Ideal.minimalPrimes_top]
      simp [degreeCap]
    · have hsub := principal_minimalPrimes_subset_span_primeFactors p hp
      let pf := UniqueFactorizationMonoid.primeFactors p
      have hfinite_image :
          ((fun q => Ideal.span ({q} : Set (MvPolynomial (Fin n) K))) ''
            (pf : Set (MvPolynomial (Fin n) K))).Finite :=
        (Finset.finite_toSet pf).image _
      calc
        Set.ncard (Ideal.span ({p} : Set (MvPolynomial (Fin n) K))).minimalPrimes ≤
            Set.ncard
              ((fun q => Ideal.span ({q} : Set (MvPolynomial (Fin n) K))) ''
                (pf : Set (MvPolynomial (Fin n) K))) := by
          exact Set.ncard_le_ncard (by simpa [pf] using hsub) hfinite_image
        _ ≤ Set.ncard (pf : Set (MvPolynomial (Fin n) K)) :=
          Set.ncard_image_le (s := (pf : Set (MvPolynomial (Fin n) K)))
        _ = pf.card := by
          rw [Set.ncard_eq_toFinset_card (pf : Set (MvPolynomial (Fin n) K))]
          simp
        _ ≤ p.totalDegree := by
          simpa [pf, UniqueFactorizationMonoid.primeFactors] using
            normalizedFactors_toFinset_card_le_totalDegree p hp
        _ ≤ degreeCap p := by
          exact le_max_right 1 p.totalDegree

theorem polynomialSystem_minimalPrimes_ncard_le_degreeCapProduct_zero
    {K : Type*} [Field K] [IsAlgClosed K] {n : ℕ}
    (f : Fin 0 → MvPolynomial (Fin n) K) :
    Set.ncard (Ideal.span (Set.range f)).minimalPrimes ≤
      ∏ i : Fin 0, degreeCap (f i) := by
  have hrange : Set.range f = (∅ : Set (MvPolynomial (Fin n) K)) := by
    ext x
    constructor
    · rintro ⟨i, _⟩
      exact Fin.elim0 i
    · simp
  rw [hrange]
  rw [Ideal.span_empty]
  change Set.ncard (minimalPrimes (MvPolynomial (Fin n) K)) ≤
    ∏ i : Fin 0, degreeCap (f i)
  rw [IsDomain.minimalPrimes_eq_singleton_bot]
  simp

theorem polynomialSystem_minimalPrimes_ncard_le_degreeCapProduct_one
    {K : Type*} [Field K] [IsAlgClosed K] {n : ℕ}
    (f : Fin 1 → MvPolynomial (Fin n) K) :
    Set.ncard (Ideal.span (Set.range f)).minimalPrimes ≤
      ∏ i : Fin 1, degreeCap (f i) := by
  classical
  have hrange : Set.range f = ({f 0} : Set (MvPolynomial (Fin n) K)) := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i
      simp
    · intro hx
      rw [Set.mem_singleton_iff] at hx
      exact ⟨0, hx.symm⟩
  calc
    Set.ncard (Ideal.span (Set.range f)).minimalPrimes =
        Set.ncard (Ideal.span ({f 0} : Set (MvPolynomial (Fin n) K))).minimalPrimes := by
      rw [hrange]
    _ ≤ degreeCap (f 0) :=
      principal_minimalPrimes_ncard_le_degreeCap (f 0)
    _ = ∏ i : Fin 1, degreeCap (f i) := by
      simp

lemma polynomial_natDegree_pos_of_irreducible
    {K : Type*} [Field K] {p : Polynomial K}
    (hp : Irreducible p) :
    0 < p.natDegree := by
  by_contra hnot
  have hdeg : p.natDegree = 0 := Nat.eq_zero_of_not_pos hnot
  rcases Polynomial.natDegree_eq_zero.mp hdeg with ⟨x, hx⟩
  have hx_ne : x ≠ 0 := by
    intro hx_zero
    have hpzero : p = 0 := by
      rw [← hx, hx_zero]
      simp
    exact hp.ne_zero hpzero
  have hx_unit : IsUnit x := isUnit_iff_ne_zero.mpr hx_ne
  have hunit : IsUnit p := by
    rw [← hx]
    exact Polynomial.isUnit_C.mpr hx_unit
  exact hp.not_isUnit hunit

lemma polynomial_natDegree_multiset_prod_eq_of_forall_ne_zero
    {K : Type*} [Field K]
    (s : Multiset (Polynomial K))
    (h : ∀ p ∈ s, p ≠ 0) :
    s.prod.natDegree = (s.map Polynomial.natDegree).sum := by
  induction s using Multiset.induction_on with
  | empty =>
      simp
  | cons p s ih =>
      have hp : p ≠ 0 := h p (by simp)
      have hs_prod : s.prod ≠ 0 := by
        apply Multiset.prod_ne_zero
        intro hzero
        exact h 0 (by simp [hzero]) rfl
      rw [Multiset.prod_cons, Multiset.map_cons, Multiset.sum_cons]
      rw [Polynomial.natDegree_mul hp hs_prod]
      rw [ih (by
        intro q hq
        exact h q (by simp [hq]))]

lemma polynomial_normalizedFactors_toFinset_card_le_natDegree
    {K : Type*} [Field K]
    [DecidableEq (Polynomial K)]
    (p : Polynomial K) (hp : p ≠ 0) :
    (UniqueFactorizationMonoid.normalizedFactors p).toFinset.card ≤ p.natDegree := by
  classical
  let s := UniqueFactorizationMonoid.normalizedFactors p
  have hcard_to : s.toFinset.card ≤ s.card := Multiset.toFinset_card_le s
  have hone : s.card ≤ (s.map Polynomial.natDegree).sum := by
    rw [← Multiset.card_map Polynomial.natDegree s]
    apply multiset_card_le_sum_of_one_le
    intro d hd
    rcases Multiset.mem_map.mp hd with ⟨q, hq, rfl⟩
    exact polynomial_natDegree_pos_of_irreducible
      (UniqueFactorizationMonoid.irreducible_of_normalized_factor q (by simpa [s] using hq))
  have hprod_degree :
      s.prod.natDegree = (s.map Polynomial.natDegree).sum := by
    apply polynomial_natDegree_multiset_prod_eq_of_forall_ne_zero
    intro q hq
    exact UniqueFactorizationMonoid.ne_zero_of_mem_normalizedFactors (by simpa [s] using hq)
  have hprod_le : s.prod.natDegree ≤ p.natDegree := by
    exact Polynomial.natDegree_le_of_dvd
      (UniqueFactorizationMonoid.prod_normalizedFactors hp).dvd hp
  simpa [s] using hcard_to.trans (hone.trans (by simpa [hprod_degree] using hprod_le))

lemma polynomial_principal_minimalPrimes_subset_span_primeFactors
    {K : Type*} [Field K]
    (p : Polynomial K) (hp : p ≠ 0) :
    (Ideal.span ({p} : Set (Polynomial K))).minimalPrimes ⊆
      (fun q => Ideal.span ({q} : Set (Polynomial K))) ''
        (UniqueFactorizationMonoid.primeFactors p : Set (Polynomial K)) := by
  classical
  intro P hP
  have hPPrime : P.IsPrime := Ideal.minimalPrimes_isPrime hP
  have hp_mem_P : p ∈ P := by
    exact (Ideal.span_singleton_le_iff_mem P).mp hP.1.2
  have hprod_mem :
      (UniqueFactorizationMonoid.normalizedFactors p).prod ∈ P := by
    exact P.mem_of_dvd (UniqueFactorizationMonoid.prod_normalizedFactors hp).symm.dvd hp_mem_P
  obtain ⟨q, hq_factor, hq_mem_P⟩ :=
    (hPPrime.multiset_prod_mem_iff_exists_mem
      (UniqueFactorizationMonoid.normalizedFactors p)).mp hprod_mem
  have hq_prime : Prime q :=
    UniqueFactorizationMonoid.prime_of_normalized_factor q hq_factor
  have hq_span_prime : (Ideal.span ({q} : Set (Polynomial K))).IsPrime :=
    (Ideal.span_singleton_prime hq_prime.ne_zero).mpr hq_prime
  have hp_mem_span_q : p ∈ Ideal.span ({q} : Set (Polynomial K)) := by
    exact Ideal.mem_span_singleton.mpr
      (UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hq_factor)
  have hp_span_le_q_span :
      Ideal.span ({p} : Set (Polynomial K)) ≤
        Ideal.span ({q} : Set (Polynomial K)) := by
    exact (Ideal.span_singleton_le_iff_mem _).mpr hp_mem_span_q
  have hq_span_le_P :
      Ideal.span ({q} : Set (Polynomial K)) ≤ P := by
    exact (Ideal.span_singleton_le_iff_mem P).mpr hq_mem_P
  have hP_le_q_span :
      P ≤ Ideal.span ({q} : Set (Polynomial K)) :=
    hP.2 ⟨hq_span_prime, hp_span_le_q_span⟩ hq_span_le_P
  have hP_eq : P = Ideal.span ({q} : Set (Polynomial K)) :=
    le_antisymm hP_le_q_span hq_span_le_P
  refine ⟨q, ?_, hP_eq.symm⟩
  simpa [UniqueFactorizationMonoid.mem_primeFactors] using hq_factor

theorem polynomial_principal_minimalPrimes_ncard_le_degreeCap
    {K : Type*} [Field K]
    (p : Polynomial K) :
    Set.ncard (Ideal.span ({p} : Set (Polynomial K))).minimalPrimes ≤
      polynomialDegreeCap p := by
  classical
  letI : DecidableEq (Polynomial K) := Classical.decEq _
  by_cases hp : p = 0
  · subst p
    have hspan :
        Ideal.span ({(0 : Polynomial K)} : Set (Polynomial K)) =
          (⊥ : Ideal (Polynomial K)) := by
      exact Ideal.span_singleton_eq_bot.mpr rfl
    calc
      Set.ncard (Ideal.span ({(0 : Polynomial K)} : Set (Polynomial K))).minimalPrimes = 1 := by
        rw [hspan]
        change Set.ncard (minimalPrimes (Polynomial K)) = 1
        rw [IsDomain.minimalPrimes_eq_singleton_bot]
        simp
      _ ≤ polynomialDegreeCap (0 : Polynomial K) := by
        simp [polynomialDegreeCap]
  · by_cases hunit : IsUnit p
    · have htop :
          Ideal.span ({p} : Set (Polynomial K)) =
            (⊤ : Ideal (Polynomial K)) := by
        exact Ideal.span_singleton_eq_top.mpr hunit
      rw [htop, Ideal.minimalPrimes_top]
      simp [polynomialDegreeCap]
    · have hsub := polynomial_principal_minimalPrimes_subset_span_primeFactors p hp
      let pf := UniqueFactorizationMonoid.primeFactors p
      have hfinite_image :
          ((fun q => Ideal.span ({q} : Set (Polynomial K))) ''
            (pf : Set (Polynomial K))).Finite :=
        (Finset.finite_toSet pf).image _
      calc
        Set.ncard (Ideal.span ({p} : Set (Polynomial K))).minimalPrimes ≤
            Set.ncard
              ((fun q => Ideal.span ({q} : Set (Polynomial K))) ''
                (pf : Set (Polynomial K))) := by
          exact Set.ncard_le_ncard (by simpa [pf] using hsub) hfinite_image
        _ ≤ Set.ncard (pf : Set (Polynomial K)) :=
          Set.ncard_image_le (s := (pf : Set (Polynomial K)))
        _ = pf.card := by
          rw [Set.ncard_eq_toFinset_card (pf : Set (Polynomial K))]
          simp
        _ ≤ p.natDegree := by
          simpa [pf, UniqueFactorizationMonoid.primeFactors] using
            polynomial_normalizedFactors_toFinset_card_le_natDegree p hp
        _ ≤ polynomialDegreeCap p := by
          exact le_max_right 1 p.natDegree

theorem polynomialSystem_minimalPrimes_ncard_le_degreeBound
    {K : Type*} [Field K] [IsAlgClosed K]
    {ι : Type*} [Fintype ι]
    (g : ι → Polynomial K) (d : ℕ)
    (hd_pos : 1 ≤ d)
    (hd : ∀ i, polynomialDegreeCap (g i) ≤ d) :
    Set.ncard (Ideal.span (Set.range g)).minimalPrimes ≤ d := by
  classical
  let I : Ideal (Polynomial K) := Ideal.span (Set.range g)
  let a : Polynomial K := Submodule.IsPrincipal.generator I
  by_cases hzero : ∀ i, g i = 0
  · have hIbot : I = ⊥ := by
      change Ideal.span (Set.range g) = ⊥
      rw [Ideal.span_eq_bot]
      rintro x ⟨i, rfl⟩
      exact hzero i
    calc
      Set.ncard (Ideal.span (Set.range g)).minimalPrimes = 1 := by
        change Set.ncard I.minimalPrimes = 1
        rw [hIbot]
        change Set.ncard (minimalPrimes (Polynomial K)) = 1
        rw [IsDomain.minimalPrimes_eq_singleton_bot]
        simp
      _ ≤ d := hd_pos
  · push_neg at hzero
    obtain ⟨i, hgi_ne⟩ := hzero
    have hI : Ideal.span ({a} : Set (Polynomial K)) = I := by
      exact Ideal.span_singleton_generator I
    have hmem : g i ∈ I := by
      exact Ideal.subset_span (Set.mem_range_self i)
    have hdiv : a ∣ g i := by
      exact (Submodule.IsPrincipal.mem_iff_generator_dvd I).mp hmem
    have hdeg_a : a.natDegree ≤ (g i).natDegree :=
      Polynomial.natDegree_le_of_dvd hdiv hgi_ne
    have hcap_a : polynomialDegreeCap a ≤ d := by
      exact max_le hd_pos
        (hdeg_a.trans ((le_max_right 1 (g i).natDegree).trans (hd i)))
    calc
      Set.ncard (Ideal.span (Set.range g)).minimalPrimes =
          Set.ncard (Ideal.span ({a} : Set (Polynomial K))).minimalPrimes := by
        change Set.ncard I.minimalPrimes = _
        rw [← hI]
      _ ≤ polynomialDegreeCap a :=
        polynomial_principal_minimalPrimes_ncard_le_degreeCap a
      _ ≤ d := hcap_a

/-- One-variable multivariable polynomials are univariate polynomials. -/
def oneVarAlgEquiv (K : Type*) [Field K] :
    MvPolynomial (Fin 1) K ≃ₐ[K] Polynomial K :=
  (MvPolynomial.finSuccEquiv K 0).trans
    (Polynomial.mapAlgEquiv (MvPolynomial.isEmptyAlgEquiv K (Fin 0)))

lemma polynomialDegreeCap_oneVarAlgEquiv_le_degreeCap
    {K : Type*} [Field K]
    (p : MvPolynomial (Fin 1) K) :
    polynomialDegreeCap (oneVarAlgEquiv K p) ≤ degreeCap p := by
  have hnat : (oneVarAlgEquiv K p).natDegree ≤ p.totalDegree := by
    calc
      (oneVarAlgEquiv K p).natDegree ≤
          ((MvPolynomial.finSuccEquiv K 0) p).natDegree := by
        simpa [oneVarAlgEquiv] using
          (Polynomial.natDegree_map_le
            (f := (MvPolynomial.isEmptyAlgEquiv K (Fin 0) :
              MvPolynomial (Fin 0) K →+* K))
            (p := (MvPolynomial.finSuccEquiv K 0) p))
      _ = p.degreeOf 0 := MvPolynomial.natDegree_finSuccEquiv p
      _ ≤ p.totalDegree := MvPolynomial.degreeOf_le_totalDegree p 0
  exact max_le (le_max_left 1 p.totalDegree) (hnat.trans (le_max_right 1 p.totalDegree))

lemma minimalPrimes_ncard_le_map_of_ringEquiv
    {R S : Type*} [CommRing R] [CommRing S] [IsNoetherianRing S]
    (e : R ≃+* S) (I : Ideal R) :
    Set.ncard I.minimalPrimes ≤ Set.ncard (Ideal.map (e : R →+* S) I).minimalPrimes := by
  have hI : I = Ideal.comap (e : R →+* S) (Ideal.map (e : R →+* S) I) := by
    rw [I.comap_map_of_bijective (e : R →+* S) e.bijective]
  calc
    Set.ncard I.minimalPrimes =
        Set.ncard (Ideal.comap (e : R →+* S) (Ideal.map (e : R →+* S) I)).minimalPrimes :=
      congrArg (fun J : Ideal R => Set.ncard J.minimalPrimes) hI
    _ = Set.ncard (Ideal.comap (e : R →+* S) ''
        (Ideal.map (e : R →+* S) I).minimalPrimes) := by
      rw [Ideal.comap_minimalPrimes_eq_of_surjective (f := (e : R →+* S)) e.surjective]
    _ ≤ Set.ncard (Ideal.map (e : R →+* S) I).minimalPrimes :=
      Set.ncard_image_le
        (hs := Ideal.finite_minimalPrimes_of_isNoetherianRing S
          (Ideal.map (e : R →+* S) I))

theorem polynomialSystem_minimalPrimes_ncard_le_degreeBound_ambient_one
    {K : Type*} [Field K] [IsAlgClosed K]
    {ι : Type*} [Fintype ι]
    (f : ι → MvPolynomial (Fin 1) K) (d : ℕ)
    (hd_pos : 1 ≤ d)
    (hd : ∀ i, degreeCap (f i) ≤ d) :
    Set.ncard (Ideal.span (Set.range f)).minimalPrimes ≤ d ^ 1 := by
  classical
  let e := oneVarAlgEquiv K
  let g : ι → Polynomial K := fun i => e (f i)
  have hmapspan :
      Ideal.map (e : MvPolynomial (Fin 1) K →+* Polynomial K)
          (Ideal.span (Set.range f)) = Ideal.span (Set.range g) := by
    rw [Ideal.map_span]
    congr 1
    ext y
    constructor
    · rintro ⟨x, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨f i, Set.mem_range_self i, rfl⟩
  have hmap_bound :
      Set.ncard
          (Ideal.map (e : MvPolynomial (Fin 1) K →+* Polynomial K)
            (Ideal.span (Set.range f))).minimalPrimes ≤ d := by
    rw [hmapspan]
    exact polynomialSystem_minimalPrimes_ncard_le_degreeBound g d hd_pos (by
      intro i
      exact (polynomialDegreeCap_oneVarAlgEquiv_le_degreeCap (K := K) (f i)).trans (hd i))
  calc
    Set.ncard (Ideal.span (Set.range f)).minimalPrimes ≤
        Set.ncard
          (Ideal.map (e : MvPolynomial (Fin 1) K →+* Polynomial K)
            (Ideal.span (Set.range f))).minimalPrimes := by
      exact minimalPrimes_ncard_le_map_of_ringEquiv
        (e : MvPolynomial (Fin 1) K ≃+* Polynomial K)
        (Ideal.span (Set.range f))
    _ ≤ d := hmap_bound
    _ = d ^ 1 := by simp

/--
If a ring is isomorphic to a field, then its ideals are only `⊥` and `⊤`.

This is used for the zero-ambient-variable base case
`MvPolynomial (Fin 0) K ≃ K`.
-/
lemma ideal_eq_bot_or_top_of_ringEquiv_field
    {R F : Type*} [CommRing R] [Field F] (e : R ≃+* F) (I : Ideal R) :
    I = ⊥ ∨ I = ⊤ := by
  rcases Ideal.eq_bot_or_top (I.map e) with h | h
  · left
    have hc := congrArg (fun J : Ideal F => Ideal.comap (e : R →+* F) J) h
    change Ideal.comap (e : R →+* F) (Ideal.map (e : R →+* F) I) =
      Ideal.comap (e : R →+* F) (⊥ : Ideal F) at hc
    rw [I.comap_map_of_bijective (e : R →+* F) e.bijective] at hc
    rw [← RingHom.ker_eq_comap_bot (e : R →+* F),
      (RingHom.injective_iff_ker_eq_bot (e : R →+* F)).mp e.injective] at hc
    exact hc
  · right
    have hc := congrArg (fun J : Ideal F => Ideal.comap (e : R →+* F) J) h
    change Ideal.comap (e : R →+* F) (Ideal.map (e : R →+* F) I) =
      Ideal.comap (e : R →+* F) (⊤ : Ideal F) at hc
    rw [I.comap_map_of_bijective (e : R →+* F) e.bijective] at hc
    simpa using hc

/-- Any ideal in a domain that is isomorphic to a field has at most one
minimal prime. -/
lemma ideal_minimalPrimes_ncard_le_one_of_ringEquiv_field
    {R F : Type*} [CommRing R] [IsDomain R] [Field F] (e : R ≃+* F)
    (I : Ideal R) :
    Set.ncard I.minimalPrimes ≤ 1 := by
  rcases ideal_eq_bot_or_top_of_ringEquiv_field e I with rfl | rfl
  · change Set.ncard (minimalPrimes R) ≤ 1
    rw [IsDomain.minimalPrimes_eq_singleton_bot]
    simp
  · rw [Ideal.minimalPrimes_top]
    simp

/--
Unconditional zero-dimensional ambient case of the Heintz component-count
bound: in no variables the coordinate ring is just the base field, so there is
at most one component.
-/
theorem polynomialSystem_minimalPrimes_ncard_le_degreeBound_pow_ambient_zero
    {K : Type*} [Field K] [IsAlgClosed K] {ι : Type*} [Fintype ι]
    (f : ι → MvPolynomial (Fin 0) K) (d : ℕ) :
    Set.ncard (Ideal.span (Set.range f)).minimalPrimes ≤ d ^ 0 := by
  simpa using
    ideal_minimalPrimes_ncard_le_one_of_ringEquiv_field
      (MvPolynomial.isEmptyRingEquiv K (Fin 0))
      (Ideal.span (Set.range f))

/--
Unconditional one-equation positive-ambient case of the Heintz component-count
bound.

The UFD principal-ideal argument gives at most `degreeCap (f 0)` components,
and `degreeCap (f 0) ≤ d ≤ d^n` when `n > 0` and the equation has capped degree
at most `d`.
-/
theorem polynomialSystem_minimalPrimes_ncard_le_degreeBound_pow_one_equation
    {K : Type*} [Field K] [IsAlgClosed K] {n d : ℕ}
    (hn : 0 < n)
    (f : Fin 1 → MvPolynomial (Fin n) K)
    (hd : ∀ i, degreeCap (f i) ≤ d) :
    Set.ncard (Ideal.span (Set.range f)).minimalPrimes ≤ d ^ n := by
  have hd_pos : 1 ≤ d := by
    exact (le_max_left 1 (f 0).totalDegree).trans (hd 0)
  calc
    Set.ncard (Ideal.span (Set.range f)).minimalPrimes ≤
        ∏ i : Fin 1, degreeCap (f i) :=
      polynomialSystem_minimalPrimes_ncard_le_degreeCapProduct_one f
    _ = degreeCap (f 0) := by
      simp
    _ ≤ d :=
      hd 0
    _ ≤ d ^ n :=
      le_self_pow₀ hd_pos hn.ne'

/--
The dimension-sensitive component-count bound is now unconditional in ambient
dimension at most one.
-/
theorem polynomialSystem_minimalPrimes_ncard_le_degreeBound_pow_ambient_le_one
    {K : Type*} [Field K] [IsAlgClosed K]
    {n : ℕ} (hn : n ≤ 1) {ι : Type*} [Fintype ι]
    (f : ι → MvPolynomial (Fin n) K) (d : ℕ)
    (hd_pos : 1 ≤ d)
    (hd : ∀ i, degreeCap (f i) ≤ d) :
    Set.ncard (Ideal.span (Set.range f)).minimalPrimes ≤ d ^ n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn_pos
  · exact polynomialSystem_minimalPrimes_ncard_le_degreeBound_pow_ambient_zero f d
  · have hn_eq : n = 1 := by omega
    subst n
    exact polynomialSystem_minimalPrimes_ncard_le_degreeBound_ambient_one f d hd_pos hd

/--
The new minimal-prime components obtained by adding one equation `x = 0` that
lie over a fixed old component `P`.
-/
def newComponentsOver {R : Type*} [CommSemiring R]
    (I : Ideal R) (x : R) (P : Ideal R) : Set (Ideal R) :=
  {Q | Q ∈ (Ideal.span ({x} : Set R) ⊔ I).minimalPrimes ∧ P ≤ Q}

/--
Every minimal prime after adding one equation contains a minimal prime of the
old ideal.  This is the ring-theoretic bookkeeping behind "new components lie
over old components."
-/
lemma minimalPrime_sup_principal_lies_over_minimalPrime
    {R : Type*} [CommSemiring R]
    (I : Ideal R) (x : R) {Q : Ideal R}
    (hQ : Q ∈ (Ideal.span ({x} : Set R) ⊔ I).minimalPrimes) :
    ∃ P ∈ I.minimalPrimes, P ≤ Q := by
  have hQPrime : Q.IsPrime := Ideal.minimalPrimes_isPrime hQ
  letI : Q.IsPrime := hQPrime
  have hIleQ : I ≤ Q := le_trans le_sup_right hQ.1.2
  exact Ideal.exists_minimalPrimes_le (I := I) (J := Q) hIleQ

/--
The minimal primes of `I + (x)` are covered by the fibers over the minimal
primes of `I`.
-/
lemma minimalPrimes_sup_principal_subset_iUnion_newComponentsOver
    {R : Type*} [CommSemiring R]
    (I : Ideal R) (x : R) :
    (Ideal.span ({x} : Set R) ⊔ I).minimalPrimes ⊆
      ⋃ P ∈ I.minimalPrimes, newComponentsOver I x P := by
  intro Q hQ
  obtain ⟨P, hP, hPleQ⟩ :=
    minimalPrime_sup_principal_lies_over_minimalPrime I x hQ
  exact Set.mem_iUnion.mpr
    ⟨P, Set.mem_iUnion.mpr ⟨hP, ⟨hQ, hPleQ⟩⟩⟩

/--
Cardinality form of the component bookkeeping: the number of components after
adding one equation is at most the sum of the sizes of the fibers over the old
components.
-/
lemma minimalPrimes_sup_principal_ncard_le_sum_newComponentsOver
    {R : Type*} [CommSemiring R] [IsNoetherianRing R]
    (I : Ideal R) (x : R) :
    Set.ncard (Ideal.span ({x} : Set R) ⊔ I).minimalPrimes ≤
      ∑ᶠ P ∈ I.minimalPrimes, Set.ncard (newComponentsOver I x P) := by
  classical
  have hcover :=
    minimalPrimes_sup_principal_subset_iUnion_newComponentsOver I x
  have htarget :
      (⋃ P ∈ I.minimalPrimes, newComponentsOver I x P).Finite := by
    exact (Ideal.finite_minimalPrimes_of_isNoetherianRing R I).biUnion
      (fun P _hP =>
        (Ideal.finite_minimalPrimes_of_isNoetherianRing R
          (Ideal.span ({x} : Set R) ⊔ I)).subset
          (fun Q hQ => hQ.1))
  calc
    Set.ncard (Ideal.span ({x} : Set R) ⊔ I).minimalPrimes ≤
        Set.ncard (⋃ P ∈ I.minimalPrimes, newComponentsOver I x P) := by
      exact Set.ncard_le_ncard hcover htarget
    _ ≤ ∑ᶠ P ∈ I.minimalPrimes, Set.ncard (newComponentsOver I x P) := by
      exact (Ideal.finite_minimalPrimes_of_isNoetherianRing R I).ncard_biUnion_le
        (fun P => newComponentsOver I x P)

/--
Minimal primes of the principal hypersurface section of `P` are the comaps of
minimal primes of the principal ideal generated by the image of `x` in `R ⧸ P`.
-/
lemma minimalPrimes_sup_principal_eq_quotient
    {R : Type*} [CommRing R] (P : Ideal R) (x : R) :
    (Ideal.span ({x} : Set R) ⊔ P).minimalPrimes =
      Ideal.comap (Ideal.Quotient.mk P) ''
        (Ideal.span ({Ideal.Quotient.mk P x} : Set (R ⧸ P))).minimalPrimes := by
  rw [← Ideal.comap_minimalPrimes_eq_of_surjective Ideal.Quotient.mk_surjective]
  congr 1
  rw [← Set.image_singleton]
  rw [← Ideal.map_span]
  rw [Ideal.comap_map_of_surjective (Ideal.Quotient.mk P) Ideal.Quotient.mk_surjective]
  rw [← RingHom.ker_eq_comap_bot (Ideal.Quotient.mk P), Ideal.mk_ker]

/--
If `P` is an old minimal component of `I`, then every actual new component over
`P` is a component of the principal hypersurface section of `P`.
-/
lemma mem_minimalPrimes_sup_principal_of_mem_newComponentsOver
    {R : Type*} [CommRing R]
    {I P : Ideal R} {x : R}
    (hP : P ∈ I.minimalPrimes) {Q : Ideal R}
    (hQ : Q ∈ newComponentsOver I x P) :
    Q ∈ (Ideal.span ({x} : Set R) ⊔ P).minimalPrimes := by
  rcases hQ with ⟨hQmin, hPleQ⟩
  have hQPrime : Q.IsPrime := Ideal.minimalPrimes_isPrime hQmin
  have hQle : Ideal.span ({x} : Set R) ⊔ I ≤ Q := hQmin.1.2
  have hxleQ : Ideal.span ({x} : Set R) ≤ Q := (sup_le_iff.mp hQle).1
  refine ⟨⟨hQPrime, sup_le hxleQ hPleQ⟩, ?_⟩
  intro (J : Ideal R) hJ hJleQ
  have hJle : Ideal.span ({x} : Set R) ⊔ P ≤ J := hJ.2
  have hxleJ : Ideal.span ({x} : Set R) ≤ J := (sup_le_iff.mp hJle).1
  have hPleJ : P ≤ J := (sup_le_iff.mp hJle).2
  have hIleP : I ≤ P := hP.1.2
  have hIleJ : I ≤ J := hIleP.trans hPleJ
  have hspanIleJ : Ideal.span ({x} : Set R) ⊔ I ≤ J := sup_le hxleJ hIleJ
  exact hQmin.2 (y := J) ⟨hJ.1, hspanIleJ⟩ hJleQ

/--
Local quotient reduction for the real intersection step.

The inclusion is the correct direction for upper bounds.  The reverse inclusion
is false in general: a component of `V(P) ∩ V(x)` can be contained in a larger
component coming from another old minimal prime and therefore fail to be a
minimal component of the total new ideal.
-/
lemma newComponentsOver_subset_quotient_principal_minimalPrimes
    {R : Type*} [CommRing R]
    (I : Ideal R) (x : R) {P : Ideal R}
    (hP : P ∈ I.minimalPrimes) :
    newComponentsOver I x P ⊆
      Ideal.comap (Ideal.Quotient.mk P) ''
        (Ideal.span ({Ideal.Quotient.mk P x} : Set (R ⧸ P))).minimalPrimes := by
  intro Q hQ
  have hQ' : Q ∈ (Ideal.span ({x} : Set R) ⊔ P).minimalPrimes :=
    mem_minimalPrimes_sup_principal_of_mem_newComponentsOver hP hQ
  simpa [minimalPrimes_sup_principal_eq_quotient P x] using hQ'

/-- The multivariate polynomial representing a scalar linear form. -/
def linearFormPolynomial {K : Type*} [Field K] {n : ℕ}
    (L : (Fin n → K) →ₗ[K] K) : MvPolynomial (Fin n) K :=
  ∑ i : Fin n, MvPolynomial.C (L (Pi.single i 1)) * MvPolynomial.X i

lemma aeval_linearFormPolynomial
    {K : Type*} [Field K] {n : ℕ}
    (L : (Fin n → K) →ₗ[K] K) (x : Fin n → K) :
    MvPolynomial.aeval x (linearFormPolynomial L) = L x := by
  classical
  calc
    MvPolynomial.aeval x (linearFormPolynomial L)
        = ∑ i : Fin n, L (Pi.single i 1) * x i := by
      simp [linearFormPolynomial, mul_comm]
    _ = ∑ i : Fin n, L (Pi.single i (x i)) := by
      apply Finset.sum_congr rfl
      intro i _hi
      have hsingle : Pi.single i (x i) =
          (x i) • (Pi.single (M := fun _ : Fin n => K) i (1 : K)) := by
        rw [← Pi.single_smul, smul_eq_mul, mul_one]
      rw [hsingle, map_smul]
      exact mul_comm (L (Pi.single i 1)) (x i)
    _ = L x := by
      rw [← map_sum]
      simp [Finset.univ_sum_single]

/--
The product `∏ c in T, (ell - c)` as a multivariate polynomial in the ambient
coordinates.
-/
def scalarImageProduct {K : Type*} [Field K] {n : ℕ}
    (L : (Fin n → K) →ₗ[K] K) (T : Finset K) : MvPolynomial (Fin n) K :=
  T.prod fun t => linearFormPolynomial L - MvPolynomial.C t

lemma scalarImageProduct_mem_vanishingIdeal_of_image_subset
    {K : Type*} [Field K] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) K))
    (L : (Fin n → K) →ₗ[K] K) {T : Finset K}
    (hT : L '' MvPolynomial.zeroLocus K I ⊆ (T : Set K)) :
    scalarImageProduct L T ∈
      MvPolynomial.vanishingIdeal K (MvPolynomial.zeroLocus K I) := by
  intro x hx
  rw [scalarImageProduct, MvPolynomial.aeval_prod]
  have hlin : MvPolynomial.eval x (linearFormPolynomial L) = L x := by
    simpa using aeval_linearFormPolynomial L x
  exact Finset.prod_eq_zero (hT ⟨x, hx, rfl⟩) (by
    simp [hlin])

lemma scalarImageProduct_mem_radical_of_finite_image
    {K : Type*} [Field K] [IsAlgClosed K] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) K))
    (L : (Fin n → K) →ₗ[K] K)
    (hfin : (L '' MvPolynomial.zeroLocus K I).Finite) :
    scalarImageProduct L hfin.toFinset ∈ I.radical := by
  rw [← MvPolynomial.vanishingIdeal_zeroLocus_eq_radical (K := K) I]
  exact scalarImageProduct_mem_vanishingIdeal_of_image_subset I L (by
    intro t ht
    exact hfin.mem_toFinset.mpr ht)

lemma exists_linear_factor_mem_of_minimalPrime_of_finite_image
    {K : Type*} [Field K] [IsAlgClosed K] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) K))
    (L : (Fin n → K) →ₗ[K] K)
    (hfin : (L '' MvPolynomial.zeroLocus K I).Finite)
    (p : I.minimalPrimes) :
    ∃ t ∈ hfin.toFinset, linearFormPolynomial L - MvPolynomial.C t ∈ p.1 := by
  have hpPrime : p.1.IsPrime := Ideal.minimalPrimes_isPrime p.2
  have hrad_le : I.radical ≤ p.1 :=
    hpPrime.radical_le_iff.mpr p.2.1.2
  have hprod : scalarImageProduct L hfin.toFinset ∈ p.1 :=
    hrad_le (scalarImageProduct_mem_radical_of_finite_image I L hfin)
  letI : p.1.IsPrime := hpPrime
  simpa [scalarImageProduct] using
    (Ideal.IsPrime.prod_mem_iff
      (s := hfin.toFinset)
      (x := fun t => linearFormPolynomial L - MvPolynomial.C t)
      (p := p.1)).mp hprod

def minimalPrimeScalarConstantCover
    {K : Type*} [Field K] [IsAlgClosed K] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) K))
    (L : (Fin n → K) →ₗ[K] K)
    (hfin : (L '' MvPolynomial.zeroLocus K I).Finite) :
    ScalarConstantCover (Fin n → K) K (MvPolynomial.zeroLocus K I) L where
  ι := I.minimalPrimes
  fintype := (Ideal.finite_minimalPrimes_of_isNoetherianRing
    (MvPolynomial (Fin n) K) I).fintype
  pieces := fun p => MvPolynomial.zeroLocus K p.1
  value := fun p =>
    Classical.choose
      (exists_linear_factor_mem_of_minimalPrime_of_finite_image I L hfin p)
  covers := by
    intro x hx
    let J : Ideal (MvPolynomial (Fin n) K) :=
      MvPolynomial.vanishingIdeal K ({x} : Set (Fin n → K))
    have hIleJ : I ≤ J := by
      intro f hf
      rw [MvPolynomial.mem_vanishingIdeal_singleton_iff]
      exact hx f hf
    haveI : J.IsPrime := by
      dsimp [J]
      infer_instance
    obtain ⟨p, hp, hple⟩ := Ideal.exists_minimalPrimes_le (I := I) (J := J) hIleJ
    refine Set.mem_iUnion.mpr ⟨⟨p, hp⟩, ?_⟩
    intro f hf
    exact (MvPolynomial.mem_vanishingIdeal_singleton_iff x f).mp (hple hf)
  constant := by
    intro p x _hxS hxp
    let t : K :=
      Classical.choose
        (exists_linear_factor_mem_of_minimalPrime_of_finite_image I L hfin p)
    have htmem :
        linearFormPolynomial L - MvPolynomial.C t ∈ p.1 :=
      (Classical.choose_spec
        (exists_linear_factor_mem_of_minimalPrime_of_finite_image I L hfin p)).2
    have hxzero : MvPolynomial.aeval x (linearFormPolynomial L - MvPolynomial.C t) = 0 :=
      hxp (linearFormPolynomial L - MvPolynomial.C t) htmem
    have hlin : MvPolynomial.eval x (linearFormPolynomial L) = L x := by
      simpa using aeval_linearFormPolynomial L x
    have hsub : L x - t = 0 := by
      simpa [hlin] using hxzero
    exact sub_eq_zero.mp hsub

theorem minimalPrimeScalarConstantCover_card
    {K : Type*} [Field K] [IsAlgClosed K] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) K))
    (L : (Fin n → K) →ₗ[K] K)
    (hfin : (L '' MvPolynomial.zeroLocus K I).Finite) :
    (minimalPrimeScalarConstantCover I L hfin).card =
      Set.ncard I.minimalPrimes := by
  calc
    (minimalPrimeScalarConstantCover I L hfin).card =
        Set.ncard (Set.univ : Set I.minimalPrimes) := by
      simp only [minimalPrimeScalarConstantCover, ScalarConstantCover.card]
      rw [Set.ncard_univ]
      exact Fintype.card_eq_nat_card
    _ = Set.ncard I.minimalPrimes :=
      Set.ncard_coe (I.minimalPrimes)

theorem scalar_projection_ncard_le_of_minimalPrimes_bound
    {K : Type*} [Field K] [IsAlgClosed K] {n M : ℕ}
    (I : Ideal (MvPolynomial (Fin n) K))
    (L : (Fin n → K) →ₗ[K] K)
    (hfin : (L '' MvPolynomial.zeroLocus K I).Finite)
    (hbound : Set.ncard I.minimalPrimes ≤ M) :
    (L '' MvPolynomial.zeroLocus K I).ncard ≤ M := by
  let cover := minimalPrimeScalarConstantCover I L hfin
  have hcard : cover.card ≤ M := by
    simpa [cover, minimalPrimeScalarConstantCover_card I L hfin] using hbound
  exact cover.image_ncard_le_of_card_le hcard

end ComponentBound
end ZkGolfOptimality
