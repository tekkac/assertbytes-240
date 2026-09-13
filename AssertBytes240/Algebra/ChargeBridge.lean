import AssertBytes240.Algebra.Degree
import AssertBytes240.Algebra.ComponentExtraction
import AssertBytes240.Algebra.DimensionFormula
import AssertBytes240.Algebra.AffineDimension

/-!
# Bridge lemmas linking heights to Hilbert-polynomial degrees

Relates isolated components at minimal primes to the quotient dimension
formula, identifying the Hilbert-polynomial degree with the corresponding
height arithmetic. The divided-degree recurrence uses these bridge lemmas to
align `degQ` terms across components.
-/

open MvPolynomial

noncomputable section

namespace AristotleChargeBridge

open AristotleDimensionFormula

variable {K : Type*} [Field K] {n : ℕ}

/-
Krull dimension of the quotient depends only on the radical, so it agrees for
`isoComp I p` and `p`.
-/
theorem ringKrullDim_quotient_isoComp (I p : Ideal (MvPolynomial (Fin n) K)) [p.IsPrime]
    (hp : p ∈ I.minimalPrimes) :
    ringKrullDim (MvPolynomial (Fin n) K ⧸ isoComp I p)
      = ringKrullDim (MvPolynomial (Fin n) K ⧸ p) := by
  -- Since p is prime, we have p.radical = p.
  have h_radical_p : p.radical = p := Ideal.IsPrime.radical inferInstance
  -- Since the radicals are equal, their zero loci are the same.
  have h_zero_locus_eq : PrimeSpectrum.zeroLocus (isoComp I p : Set (MvPolynomial (Fin n) K)) = PrimeSpectrum.zeroLocus (p : Set (MvPolynomial (Fin n) K)) := by
    have h_radical_isoComp : (isoComp I p).radical = p := radical_isoComp I p hp
    convert PrimeSpectrum.zeroLocus_radical ( isoComp I p ) using 1;
    · simp +decide [ PrimeSpectrum.zeroLocus_radical ];
    · convert PrimeSpectrum.zeroLocus_radical ( isoComp I p ) using 1;
      rw [ h_radical_isoComp ];
  convert ringKrullDim_quotient ( isoComp I p ) |> Eq.trans <| ?_ using 1;
  rw [ h_zero_locus_eq, ringKrullDim_quotient ]

/-- The height of a minimal prime is at most `n`. -/
theorem height_toNat_le (p : Ideal (MvPolynomial (Fin n) K)) [hpp : p.IsPrime] :
    p.height.toNat ≤ n := by
  have hle := Ideal.height_le_ringKrullDim_of_ne_top (I := p) hpp.ne_top
  rw [mvPoly_ringKrullDim (K := K) n] at hle
  have : p.height ≤ (n : ℕ∞) := by exact_mod_cast hle
  exact_mod_cast (ENat.toNat_le_of_le_coe this)

/-- The isolated component of a minimal prime is proper. -/
theorem isoComp_ne_top (I p : Ideal (MvPolynomial (Fin n) K)) [hpp : p.IsPrime]
    (hp : p ∈ I.minimalPrimes) : isoComp I p ≠ ⊤ := by
  intro h
  have hr := radical_isoComp I p hp
  rw [h, Ideal.radical_top] at hr
  exact hpp.ne_top hr.symm

/-- If `height p < n` then the Hilbert polynomial of `isoComp I p` is nonzero. -/
theorem hilbPoly_isoComp_ne_zero_of_height_lt [Infinite K]
    (I : Ideal (MvPolynomial (Fin n) K)) (hI : IsHomog I)
    {p : Ideal (MvPolynomial (Fin n) K)} [hpp : p.IsPrime] (hp : p ∈ I.minimalPrimes)
    (hlt : p.height.toNat < n) :
    hilbPoly (isoComp I p) ≠ 0 := by
  intro h
  have hne : isoComp I p ≠ ⊤ := isoComp_ne_top I p hp
  have hhom : IsHomog (isoComp I p) := isoComp_isHomog I p hI hp
  haveI hfd : FiniteDimensional K (MvPolynomial (Fin n) K ⧸ isoComp I p) :=
    (HF_poly_natDegree (isoComp I p) hhom hne (hilbPoly (isoComp I p))
      (hilbPoly_spec (isoComp I p) hhom)).1.mp h
  have hdim0 : ringKrullDim (MvPolynomial (Fin n) K ⧸ isoComp I p) = 0 :=
    ringKrullDim_eq_zero_of_finiteDim (isoComp I p) hne
  rw [ringKrullDim_quotient_isoComp I p hp] at hdim0
  have hform := AristotleDimensionFormula.height_add_ringKrullDim_quotient p
  rw [hdim0, add_zero] at hform
  have hpe : p.height = (n : ℕ∞) := by exact_mod_cast hform
  rw [hpe] at hlt
  simp at hlt

/-
If `height p = n` then the Hilbert polynomial of `isoComp I p` is zero.
-/
theorem hilbPoly_isoComp_eq_zero_of_height_eq [Infinite K]
    (I : Ideal (MvPolynomial (Fin n) K)) (hI : IsHomog I)
    {p : Ideal (MvPolynomial (Fin n) K)} [hpp : p.IsPrime] (hp : p ∈ I.minimalPrimes)
    (heq : p.height.toNat = n) :
    hilbPoly (isoComp I p) = 0 := by
  -- Since $p$ is a minimal prime of $I$, we have $ringKrullDim (R ⧸ p) = 0$.
  have h_ringKrullDim_p : ringKrullDim (MvPolynomial (Fin n) K ⧸ p) = 0 := by
    have h_ringKrullDim_p : p.height = (n : WithBot ℕ∞) := by
      have h_height_finite : p.height ≠ ⊤ := by
        grind +suggestions;
      cases h : p.height <;> aesop;
    have := AristotleDimensionFormula.height_add_ringKrullDim_quotient p;
    cases h : ringKrullDim ( MvPolynomial ( Fin n ) K ⧸ p ) <;> simp_all +decide;
    norm_cast at this ; aesop;
  contrapose! h_ringKrullDim_p;
  have h_ringKrullDim_isoComp : ringKrullDim (MvPolynomial (Fin n) K ⧸ isoComp I p) = (hilbPoly (isoComp I p)).natDegree + 1 := by
    apply Eq.symm; exact (by
      have := HF_natDegree_add_one_eq_krullDim (isoComp I p) (isoComp_isHomog I p hI hp) (isoComp_ne_top I p hp) (hilbPoly (isoComp I p)) (hilbPoly_spec (isoComp I p) (isoComp_isHomog I p hI hp)) h_ringKrullDim_p;
      exact this);
  rw [ ← ringKrullDim_quotient_isoComp I p hp ];
  rw [ h_ringKrullDim_isoComp ] ; norm_cast

/-- The key height/degree bridge: `natDegree (hilbPoly (isoComp I p)) + 1 + height p = n`
whenever the Hilbert polynomial is nonzero (equivalently `height p < n`). -/
theorem natDegree_hilbPoly_isoComp_add [Infinite K]
    (I : Ideal (MvPolynomial (Fin n) K)) (hI : IsHomog I)
    {p : Ideal (MvPolynomial (Fin n) K)} [hpp : p.IsPrime] (hp : p ∈ I.minimalPrimes)
    (hlt : p.height.toNat < n) :
    (hilbPoly (isoComp I p)).natDegree + 1 + p.height.toNat = n := by
  have hne : isoComp I p ≠ ⊤ := isoComp_ne_top I p hp
  have hhom : IsHomog (isoComp I p) := isoComp_isHomog I p hI hp
  have hpoly_ne : hilbPoly (isoComp I p) ≠ 0 :=
    hilbPoly_isoComp_ne_zero_of_height_lt I hI hp hlt
  have hnat := (HF_poly_natDegree (isoComp I p) hhom hne (hilbPoly (isoComp I p))
    (hilbPoly_spec (isoComp I p) hhom)).2 hpoly_ne
  rw [ringKrullDim_quotient_isoComp I p hp] at hnat
  -- hnat : ((natDegree + 1 : ℕ) : WithBot ℕ∞) = ringKrullDim (R ⧸ p)
  have hform := AristotleDimensionFormula.height_add_ringKrullDim_quotient p
  rw [← hnat] at hform
  -- hform : (p.height : WithBot ℕ∞) + ((natDegree+1:ℕ):WithBot ℕ∞) = n
  have hpt : p.height ≠ ⊤ := by
    intro htop
    have hle := Ideal.height_le_ringKrullDim_of_ne_top (I := p) hpp.ne_top
    rw [mvPoly_ringKrullDim (K := K) n, htop] at hle
    norm_cast at hle
  have hpe : p.height = ((p.height.toNat : ℕ) : ℕ∞) := (ENat.coe_toNat hpt).symm
  rw [hpe] at hform
  have : p.height.toNat + ((hilbPoly (isoComp I p)).natDegree + 1) = n := by exact_mod_cast hform
  omega

end AristotleChargeBridge
