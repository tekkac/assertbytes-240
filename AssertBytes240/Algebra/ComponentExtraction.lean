import AssertBytes240.Algebra.HilbertFunction
import AssertBytes240.Algebra.Degree

/-!
# T2-W2 — Isolated primary components via localization

Defines the isolated component `isoComp I p` by localizing at a minimal prime
and contracting back. The file proves primariness, radical control,
homogeneity, monotonicity, and associated-prime control for those components.
-/

open MvPolynomial

noncomputable section

variable {K : Type*} [Field K] {n : ℕ}

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The isolated primary component of `I` at a minimal prime `p`. -/
def isoComp (I p : Ideal (MvPolynomial (Fin n) K)) [p.IsPrime] :
    Ideal (MvPolynomial (Fin n) K) :=
  Ideal.comap (algebraMap (MvPolynomial (Fin n) K) (Localization.AtPrime p))
    (Ideal.map (algebraMap (MvPolynomial (Fin n) K) (Localization.AtPrime p)) I)

private lemma ideal_isHomogeneous_of_IsHomog
    (J : Ideal (MvPolynomial (Fin n) K)) (hJ : IsHomog J) :
    J.IsHomogeneous (homogeneousSubmodule (Fin n) K) := by
  intro i r hr
  convert hJ r hr i using 1
  exact MvPolynomial.decomposition.decompose'_apply (R := K) (σ := Fin n) r i

private lemma isHomog_of_ideal_isHomogeneous
    (J : Ideal (MvPolynomial (Fin n) K))
    (hJ : J.IsHomogeneous (homogeneousSubmodule (Fin n) K)) :
    IsHomog J := by
  intro r hr i
  have h := hJ i hr
  convert h using 1
  exact (MvPolynomial.decomposition.decompose'_apply (R := K) (σ := Fin n) r i).symm

private lemma localized_radical_eq_maximal
    (I p : Ideal (MvPolynomial (Fin n) K)) [p.IsPrime]
    (hp : p ∈ I.minimalPrimes) :
    (Ideal.map (algebraMap (MvPolynomial (Fin n) K) (Localization.AtPrime p)) I).radical =
      IsLocalRing.maximalIdeal (Localization.AtPrime p) := by
  classical
  let Rₚ := Localization.AtPrime p
  let f : MvPolynomial (Fin n) K →+* Rₚ := algebraMap (MvPolynomial (Fin n) K) Rₚ
  let q : Ideal Rₚ := Ideal.map f I
  have hmins : q.minimalPrimes = {IsLocalRing.maximalIdeal Rₚ} := by
    ext P
    constructor
    · intro hP
      have hPprime : P.IsPrime := Ideal.minimalPrimes_isPrime hP
      have hset : (Ideal.map f I).minimalPrimes = Ideal.comap f ⁻¹' I.minimalPrimes := by
        simpa [f, Rₚ] using
          (IsLocalization.minimalPrimes_map p.primeCompl Rₚ I)
      have hPpre : Ideal.comap f P ∈ I.minimalPrimes := by
        have hmem : P ∈ Ideal.comap f ⁻¹' I.minimalPrimes := by
          rw [← hset]
          simpa [q] using hP
        exact hmem
      have hcomp_le_p : Ideal.comap f P ≤ p := by
        have h := ((IsLocalization.AtPrime.orderIsoOfPrime Rₚ p) ⟨P, hPprime⟩).2.2
        simpa [f, Rₚ] using h
      have hp_le_comp : p ≤ Ideal.comap f P :=
        hp.2 ⟨hPpre.1.1, hPpre.1.2⟩ hcomp_le_p
      have hcomp_eq : Ideal.comap f P = p := le_antisymm hcomp_le_p hp_le_comp
      have hP_eq : P = IsLocalRing.maximalIdeal Rₚ := by
        simpa [f, Rₚ] using
          (Localization.AtPrime.eq_maximalIdeal_iff_comap_eq (I := p) (J := P)).mp hcomp_eq
      simp [hP_eq]
    · intro hPmem
      have hP_eq : P = IsLocalRing.maximalIdeal Rₚ := by simpa using hPmem
      subst P
      have hset : (Ideal.map f I).minimalPrimes = Ideal.comap f ⁻¹' I.minimalPrimes := by
        simpa [f, Rₚ] using
          (IsLocalization.minimalPrimes_map p.primeCompl Rₚ I)
      have hpre : Ideal.comap f (IsLocalRing.maximalIdeal Rₚ) ∈ I.minimalPrimes := by
        rw [show Ideal.comap f (IsLocalRing.maximalIdeal Rₚ) = p by
          simpa [f, Rₚ] using (Localization.AtPrime.comap_maximalIdeal (I := p))]
        exact hp
      have hmem : IsLocalRing.maximalIdeal Rₚ ∈ Ideal.comap f ⁻¹' I.minimalPrimes := hpre
      rw [← hset] at hmem
      simpa [q] using hmem
  calc
    (Ideal.map (algebraMap (MvPolynomial (Fin n) K) (Localization.AtPrime p)) I).radical
        = q.radical := by rfl
    _ = sInf q.minimalPrimes := (Ideal.sInf_minimalPrimes (I := q)).symm
    _ = sInf ({IsLocalRing.maximalIdeal Rₚ} : Set (Ideal Rₚ)) := by rw [hmins]
    _ = IsLocalRing.maximalIdeal Rₚ := sInf_singleton

private def componentPoly {A : Type*} [Semiring A]
    (φ : MvPolynomial (Fin n) K →+* A) (r : MvPolynomial (Fin n) K) : Polynomial A :=
  ∑ d ∈ Finset.range (r.totalDegree + 1),
    Polynomial.C (φ (homogeneousComponent d r)) * Polynomial.X ^ d

private lemma coeff_componentPoly {A : Type*} [Semiring A]
    (φ : MvPolynomial (Fin n) K →+* A) (r : MvPolynomial (Fin n) K) (d : ℕ) :
    (componentPoly φ r).coeff d = φ (homogeneousComponent d r) := by
  classical
  by_cases hd : d < r.totalDegree + 1
  · simp [componentPoly, hd]
  · have hgt : r.totalDegree < d := by omega
    simp [componentPoly, hd, MvPolynomial.homogeneousComponent_eq_zero d r hgt]

private lemma homogeneousComponent_mul_eq_sum_antidiagonal
    (r t : MvPolynomial (Fin n) K) (e : ℕ) :
    homogeneousComponent e (r * t) =
      ∑ ij ∈ Finset.antidiagonal e,
        homogeneousComponent ij.1 r * homogeneousComponent ij.2 t := by
  classical
  let 𝒜 := homogeneousSubmodule (Fin n) K
  rw [← MvPolynomial.decomposition.decompose'_apply (R := K) (σ := Fin n) (r * t) e]
  change ((DirectSum.decompose 𝒜 (r * t)) e : MvPolynomial (Fin n) K) = _
  rw [DirectSum.decompose_mul]
  rw [DirectSum.coe_mul_apply_eq_sum_antidiagonal]
  apply Finset.sum_congr rfl
  intro ij _hij
  have h1 : (((DirectSum.decompose 𝒜) r) ij.1 : MvPolynomial (Fin n) K) =
      homogeneousComponent ij.1 r := by
    rw [← MvPolynomial.decomposition.decompose'_apply (R := K) (σ := Fin n) r ij.1]
    rfl
  have h2 : (((DirectSum.decompose 𝒜) t) ij.2 : MvPolynomial (Fin n) K) =
      homogeneousComponent ij.2 t := by
    rw [← MvPolynomial.decomposition.decompose'_apply (R := K) (σ := Fin n) t ij.2]
    rfl
  rw [h1, h2]

private lemma coeff_componentPoly_mul {A : Type*} [CommSemiring A]
    (φ : MvPolynomial (Fin n) K →+* A) (r t : MvPolynomial (Fin n) K) (e : ℕ) :
    (componentPoly φ r * componentPoly φ t).coeff e = φ (homogeneousComponent e (r * t)) := by
  classical
  rw [homogeneousComponent_mul_eq_sum_antidiagonal]
  simp [Polynomial.coeff_mul, coeff_componentPoly, map_sum, map_mul]

theorem le_isoComp (I p : Ideal (MvPolynomial (Fin n) K)) [p.IsPrime] :
    I ≤ isoComp I p := by
  exact Ideal.le_comap_map

/-- Membership description: `x ∈ isoComp I p ↔ ∃ s ∉ p, s * x ∈ I`. -/
theorem mem_isoComp_iff (I p : Ideal (MvPolynomial (Fin n) K)) [p.IsPrime]
    (x : MvPolynomial (Fin n) K) :
    x ∈ isoComp I p ↔ ∃ s ∉ p, s * x ∈ I := by
  change algebraMap (MvPolynomial (Fin n) K) (Localization.AtPrime p) x ∈
      Ideal.map (algebraMap (MvPolynomial (Fin n) K) (Localization.AtPrime p)) I ↔ _
  rw [IsLocalization.algebraMap_mem_map_algebraMap_iff p.primeCompl
    (Localization.AtPrime p) I x]
  constructor
  · rintro ⟨s, hs, hsx⟩
    exact ⟨s, hs, hsx⟩
  · rintro ⟨s, hs, hsx⟩
    exact ⟨s, hs, hsx⟩

theorem radical_isoComp (I p : Ideal (MvPolynomial (Fin n) K)) [p.IsPrime]
    (hp : p ∈ I.minimalPrimes) :
    (isoComp I p).radical = p := by
  classical
  let Rₚ := Localization.AtPrime p
  let f : MvPolynomial (Fin n) K →+* Rₚ := algebraMap (MvPolynomial (Fin n) K) Rₚ
  let q : Ideal Rₚ := Ideal.map f I
  have hqrad : q.radical = IsLocalRing.maximalIdeal Rₚ := by
    simpa [q, f, Rₚ] using localized_radical_eq_maximal (I := I) (p := p) hp
  calc
    (isoComp I p).radical
        = Ideal.comap f q.radical := by
            change (Ideal.comap f q).radical = Ideal.comap f q.radical
            rw [← Ideal.comap_radical]
    _ = Ideal.comap f (IsLocalRing.maximalIdeal Rₚ) := by rw [hqrad]
    _ = p := by simpa [f, Rₚ] using (Localization.AtPrime.comap_maximalIdeal (I := p))

theorem isoComp_isPrimary (I p : Ideal (MvPolynomial (Fin n) K)) [p.IsPrime]
    (hp : p ∈ I.minimalPrimes) :
    (isoComp I p).IsPrimary := by
  classical
  let Rₚ := Localization.AtPrime p
  let f : MvPolynomial (Fin n) K →+* Rₚ := algebraMap (MvPolynomial (Fin n) K) Rₚ
  let q : Ideal Rₚ := Ideal.map f I
  have hqrad : q.radical = IsLocalRing.maximalIdeal Rₚ := by
    simpa [q, f, Rₚ] using localized_radical_eq_maximal (I := I) (p := p) hp
  have hqprimary : q.IsPrimary := by
    apply Ideal.isPrimary_of_isMaximal_radical
    rw [hqrad]
    exact IsLocalRing.maximalIdeal.isMaximal Rₚ
  change (Ideal.comap f q).IsPrimary
  exact hqprimary.comap f

/-- Minimal primes of homogeneous ideals are homogeneous (concrete `IsHomog`). -/
theorem minimalPrimes_isHomog (I : Ideal (MvPolynomial (Fin n) K)) (hI : IsHomog I)
    {p : Ideal (MvPolynomial (Fin n) K)} (hp : p ∈ I.minimalPrimes) :
    IsHomog p := by
  classical
  let 𝒜 := homogeneousSubmodule (Fin n) K
  have hPprime : p.IsPrime := Ideal.minimalPrimes_isPrime hp
  have hImath : I.IsHomogeneous 𝒜 := ideal_isHomogeneous_of_IsHomog I hI
  have hCorePrime : (p.homogeneousCore 𝒜).toIdeal.IsPrime :=
    Ideal.IsPrime.homogeneousCore (𝒜 := 𝒜) hPprime
  have hI_le_core : I ≤ (p.homogeneousCore 𝒜).toIdeal := by
    calc
      I = (I.homogeneousCore 𝒜).toIdeal := hImath.toIdeal_homogeneousCore_eq_self.symm
      _ ≤ (p.homogeneousCore 𝒜).toIdeal := Ideal.homogeneousCore_mono 𝒜 hp.1.2
  have hcore_le_p : (p.homogeneousCore 𝒜).toIdeal ≤ p := Ideal.toIdeal_homogeneousCore_le 𝒜 p
  have hp_le_core : p ≤ (p.homogeneousCore 𝒜).toIdeal :=
    hp.2 ⟨hCorePrime, hI_le_core⟩ hcore_le_p
  have hcore_eq : (p.homogeneousCore 𝒜).toIdeal = p := le_antisymm hcore_le_p hp_le_core
  have hPhom : p.IsHomogeneous 𝒜 := by
    rw [← hcore_eq]
    exact HomogeneousIdeal.isHomogeneous (p.homogeneousCore 𝒜)
  exact isHomog_of_ideal_isHomogeneous p hPhom

set_option synthInstance.maxHeartbeats 200000 in
theorem isoComp_isHomog (I p : Ideal (MvPolynomial (Fin n) K)) [p.IsPrime] (hI : IsHomog I)
    (hp : p ∈ I.minimalPrimes) :
    IsHomog (isoComp I p) := by
  classical
  intro x hx e
  by_cases he : e < x.totalDegree + 1
  · obtain ⟨s, hsnotp, hsxI⟩ := (mem_isoComp_iff I p x).mp hx
    obtain ⟨d, hsd⟩ : ∃ d, homogeneousComponent d s ∉ p := by
      by_contra h
      have hcomp : ∀ d, homogeneousComponent d s ∈ p := by
        intro d
        by_contra hd
        exact h ⟨d, hd⟩
      exact hsnotp (by
        rw [← MvPolynomial.sum_homogeneousComponent s]
        exact p.sum_mem fun d _hd => hcomp d)
    let Rₚ := Localization.AtPrime p
    let f : MvPolynomial (Fin n) K →+* Rₚ := algebraMap (MvPolynomial (Fin n) K) Rₚ
    let J : Ideal Rₚ := Ideal.map f I
    let A := Rₚ ⧸ J
    let φ : MvPolynomial (Fin n) K →+* A := (Ideal.Quotient.mk J).comp f
    have hmulzero : componentPoly φ s * componentPoly φ x = 0 := by
      ext m
      rw [coeff_componentPoly_mul]
      have hcompI : homogeneousComponent m (s * x) ∈ I := hI (s * x) hsxI m
      change (Ideal.Quotient.mk J) (f (homogeneousComponent m (s * x))) = 0
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem f hcompI)
    have hunit_loc : IsUnit (f (homogeneousComponent d s)) := by
      exact (IsLocalization.AtPrime.isUnit_to_map_iff Rₚ p
        (homogeneousComponent d s)).2 hsd
    have hcoeff_nzd : (componentPoly φ s).coeff d ∈ nonZeroDivisors A := by
      rw [coeff_componentPoly φ s d]
      exact (hunit_loc.map (Ideal.Quotient.mk J)).mem_nonZeroDivisors
    have hF_nzd : componentPoly φ s ∈ nonZeroDivisors (Polynomial A) :=
      Polynomial.mem_nonzeroDivisors_of_coeff_mem d hcoeff_nzd
    have hGzero : componentPoly φ x = 0 := by
      exact (mem_nonZeroDivisors_iff_right.mp hF_nzd) (componentPoly φ x)
        (by simpa [mul_comm] using hmulzero)
    have hcoeff_zero : φ (homogeneousComponent e x) = 0 := by
      have := congrArg (fun P : Polynomial A => P.coeff e) hGzero
      simpa [coeff_componentPoly φ x e] using this
    change f (homogeneousComponent e x) ∈ J
    exact Ideal.Quotient.eq_zero_iff_mem.mp hcoeff_zero
  · have hgt : x.totalDegree < e := by omega
    simpa [MvPolynomial.homogeneousComponent_eq_zero e x hgt] using
      (Ideal.zero_mem (isoComp I p))

theorem isoComp_mono {I J p : Ideal (MvPolynomial (Fin n) K)} [p.IsPrime]
    (hIJ : I ≤ J) : isoComp I p ≤ isoComp J p := by
  exact Ideal.comap_mono (Ideal.map_mono hIJ)

/-- Avoiding the radicals of finitely many primary ideals gives a
nonzerodivisor modulo their (finite) intersection. -/
theorem isSMulRegular_inf_of_avoids
    {s : Finset (Ideal (MvPolynomial (Fin n) K))}
    (q : Ideal (MvPolynomial (Fin n) K) → Ideal (MvPolynomial (Fin n) K))
    (hq : ∀ p ∈ s, (q p).IsPrimary ∧ (q p).radical = p)
    (hne : (⨅ p ∈ s, q p) ≠ ⊤)
    {f : MvPolynomial (Fin n) K} (hf : ∀ p ∈ s, f ∉ p) :
    IsSMulRegular (MvPolynomial (Fin n) K ⧸ (⨅ p ∈ s, q p)) f := by
  classical
  have _ := hne
  rw [isSMulRegular_quotient_iff_mem_of_smul_mem]
  intro x hx
  rw [Ideal.mem_iInf]
  intro p
  rw [Ideal.mem_iInf]
  intro hp
  have hprimary : (q p).IsPrimary := (hq p hp).1
  have hrad : (q p).radical = p := (hq p hp).2
  have hfx : f * x ∈ q p := by
    have h1 := (Ideal.mem_iInf.mp hx) p
    have h2 := (Ideal.mem_iInf.mp h1) hp
    simpa [smul_eq_mul] using h2
  have hxf : x * f ∈ q p := by simpa [mul_comm] using hfx
  have hcase := (Ideal.isPrimary_iff.mp hprimary).2 hxf
  exact hcase.elim (fun hxq => hxq)
    (fun hfq => False.elim (hf p hp (by simpa [hrad] using hfq)))

end
