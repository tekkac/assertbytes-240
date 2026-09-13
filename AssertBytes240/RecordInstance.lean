import AssertBytes240.Optimality

/-!
# The record gadget is an instance of the model

One byte of David Wong's 240-point circuit, as a `ConcreteScalarChecker`:
seven witnessed low bits, seven booleanity rows, and one product row pinning
the byte to the recomposition or the recomposition plus 128.

This shows the hypotheses of `score_lower_bound` are satisfiable, and that the
record's per-byte gadget is covered by the theorem. Every witness is fixed to a
finite set by its own row, in every field.
-/

noncomputable section

open MvPolynomial

namespace ZkGolfOptimality.RecordInstance

open ComponentBound AssertBytes

variable {K : Type*} [Field K]

/-- Variable `0` is the byte; variable `i.succ` is low bit `i`. -/
abbrev bit (i : Fin 7) : Fin 8 := i.succ

/-- The affine recomposition `∑ 2^i · bᵢ` of the seven low bits. -/
def lowSum : MvPolynomial (Fin 8) K :=
  ∑ i : Fin 7, C ((2 : K) ^ (i : ℕ)) * X (bit i)

/-- Row `i < 7` is booleanity of bit `i`; the last row is the product row. -/
def rows : Fin 8 → MvPolynomial (Fin 8) K :=
  Fin.lastCases ((X 0 - lowSum) * (X 0 - lowSum - C 128))
    (fun i : Fin 7 => X (bit i) * (X (bit i) - 1))

lemma totalDegree_lowSum_le : (lowSum : MvPolynomial (Fin 8) K).totalDegree ≤ 1 := by
  unfold lowSum
  refine totalDegree_finsetSum_le fun i _ => ?_
  refine (totalDegree_mul _ _).trans ?_
  rw [totalDegree_C, totalDegree_X]

lemma rows_isQuadric : IsQuadricSystem (rows : Fin 8 → MvPolynomial (Fin 8) K) := by
  intro r
  refine Fin.lastCases ?_ (fun i => ?_) r
  · -- product row
    simp only [rows, Fin.lastCases_last]
    refine (totalDegree_mul _ _).trans ?_
    have h1 : (X 0 - lowSum : MvPolynomial (Fin 8) K).totalDegree ≤ 1 :=
      (totalDegree_sub _ _).trans (by simp [totalDegree_X, totalDegree_lowSum_le])
    have h2 : (X 0 - lowSum - C 128 : MvPolynomial (Fin 8) K).totalDegree ≤ 1 :=
      (totalDegree_sub _ _).trans (by simp [totalDegree_C, h1])
    omega
  · -- booleanity row
    simp only [rows, Fin.lastCases_castSucc]
    refine (totalDegree_mul _ _).trans ?_
    have h : (X (bit i) - 1 : MvPolynomial (Fin 8) K).totalDegree ≤ 1 :=
      (totalDegree_sub _ _).trans (by simp [totalDegree_X, totalDegree_one])
    simp only [totalDegree_X]
    omega

/-- Membership in the locus is exactly "every row vanishes". -/
lemma mem_locus_iff (v : Fin 8 → K) :
    v ∈ polynomialLocus (rows : Fin 8 → MvPolynomial (Fin 8) K) ↔
      ∀ r, aeval v (rows r : MvPolynomial (Fin 8) K) = 0 := by
  unfold polynomialLocus
  rw [zeroLocus_span]
  simp

lemma aeval_lowSum (v : Fin 8 → K) :
    aeval v (lowSum : MvPolynomial (Fin 8) K) = ∑ i : Fin 7, (2 : K) ^ (i : ℕ) * v (bit i) := by
  simp [lowSum]

lemma aeval_rows_last (v : Fin 8 → K) :
    aeval v (rows (Fin.last 7) : MvPolynomial (Fin 8) K)
      = (v 0 - ∑ i : Fin 7, (2 : K) ^ (i : ℕ) * v (bit i))
        * (v 0 - ∑ i : Fin 7, (2 : K) ^ (i : ℕ) * v (bit i) - 128) := by
  unfold rows
  rw [Fin.lastCases_last]
  simp [lowSum]

lemma aeval_rows_castSucc (v : Fin 8 → K) (i : Fin 7) :
    aeval v (rows i.castSucc : MvPolynomial (Fin 8) K) = v (bit i) * (v (bit i) - 1) := by
  unfold rows
  rw [Fin.lastCases_castSucc]
  simp

/-- Binary expansion below `2^k`, straight from `Nat.mod_mul`. -/
lemma mod_two_pow_eq_sum (n k : ℕ) :
    n % 2 ^ k = ∑ i : Fin k, 2 ^ (i : ℕ) * (n / 2 ^ (i : ℕ) % 2) := by
  induction k with
  | zero => simp [Nat.mod_one]
  | succ k ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [← ih, pow_succ, Nat.mod_mul]

/-- The packing functional: read off the byte. -/
def L : (Fin 8 → K) →ₗ[K] K := LinearMap.proj 0

/-- The locus's byte coordinate is always a cast natural below 256. -/
lemma locus_byte_lt (v : Fin 8 → K)
    (hv : v ∈ polynomialLocus (rows : Fin 8 → MvPolynomial (Fin 8) K)) :
    ∃ n : ℕ, n < 256 ∧ v 0 = n := by
  classical
  rw [mem_locus_iff] at hv
  have hbit : ∀ i : Fin 7, v (bit i) = 0 ∨ v (bit i) = 1 := by
    intro i
    have h := hv i.castSucc
    rw [aeval_rows_castSucc] at h
    rcases mul_eq_zero.mp h with h | h
    · exact Or.inl h
    · exact Or.inr (sub_eq_zero.mp h)
  set s : K := ∑ i : Fin 7, (2 : K) ^ (i : ℕ) * v (bit i) with hs
  have hprod : v 0 = s ∨ v 0 = s + 128 := by
    have h := hv (Fin.last 7)
    rw [aeval_rows_last] at h
    rcases mul_eq_zero.mp h with h | h
    · exact Or.inl (sub_eq_zero.mp h)
    · exact Or.inr (by linear_combination sub_eq_zero.mp h)
  -- the bits as naturals
  let b : Fin 7 → ℕ := fun i => if v (bit i) = 1 then 1 else 0
  have hb_le : ∀ i, b i ≤ 1 := by intro i; simp only [b]; split_ifs <;> omega
  have hb_cast : ∀ i, ((b i : ℕ) : K) = v (bit i) := by
    intro i; rcases hbit i with h | h <;> simp [b, h]
  have hs_cast : ((∑ i : Fin 7, 2 ^ (i : ℕ) * b i : ℕ) : K) = s := by
    rw [hs]; push_cast
    exact Finset.sum_congr rfl fun i _ => by rw [hb_cast]
  have hs_lt : ∑ i : Fin 7, 2 ^ (i : ℕ) * b i < 128 := by
    calc ∑ i : Fin 7, 2 ^ (i : ℕ) * b i ≤ ∑ i : Fin 7, 2 ^ (i : ℕ) * 1 :=
          Finset.sum_le_sum fun i _ => Nat.mul_le_mul_left _ (hb_le i)
      _ = 127 := by simp [Fin.sum_univ_succ]
      _ < 128 := by norm_num
  rcases hprod with h | h
  · exact ⟨∑ i : Fin 7, 2 ^ (i : ℕ) * b i, by omega, by rw [h, hs_cast]⟩
  · refine ⟨∑ i : Fin 7, 2 ^ (i : ℕ) * b i + 128, by omega, ?_⟩
    rw [h, Nat.cast_add, hs_cast]; simp

lemma image_finite :
    (L '' polynomialLocus (rows : Fin 8 → MvPolynomial (Fin 8) K)).Finite := by
  refine (Set.finite_Iio 256).image (fun n : ℕ => (n : K)) |>.subset ?_
  rintro _ ⟨v, hv, rfl⟩
  obtain ⟨n, hn, hvn⟩ := locus_byte_lt v hv
  exact ⟨n, hn, by simp [L, hvn]⟩

/-- The one-byte record gadget as a checker: 1 public, 7 allocations, 8 constraints. -/
def checker [IsAlgClosed K] : ConcreteScalarChecker K where
  publicVars := 1
  allocations := 7
  constraints := 8
  q := rows
  hq := rows_isQuadric
  L := L
  hfinite := image_finite

/-- The locus point for byte `n`: the byte, then its seven low bits. -/
def byteWitness (n : ℕ) : Fin 8 → K :=
  Fin.cases (n : K) (fun i : Fin 7 => ((n / 2 ^ (i : ℕ) % 2 : ℕ) : K))

@[simp] lemma byteWitness_zero (n : ℕ) : byteWitness (K := K) n 0 = n := by
  simp [byteWitness]

lemma byteWitness_bit (n : ℕ) (i : Fin 7) :
    byteWitness (K := K) n (bit i) = ((n / 2 ^ (i : ℕ) % 2 : ℕ) : K) := by
  simp [byteWitness, bit]

lemma byteWitness_mem (n : ℕ) (hn : n < 256) :
    byteWitness (K := K) n ∈ polynomialLocus (rows : Fin 8 → MvPolynomial (Fin 8) K) := by
  rw [mem_locus_iff]
  intro r
  refine Fin.lastCases ?_ (fun i => ?_) r
  · rw [aeval_rows_last]
    have hsum : ∑ i : Fin 7, (2 : K) ^ (i : ℕ) * byteWitness n (bit i)
        = ((n % 128 : ℕ) : K) := by
      rw [show (128 : ℕ) = 2 ^ 7 by norm_num, mod_two_pow_eq_sum]
      push_cast
      exact Finset.sum_congr rfl fun i _ => by rw [byteWitness_bit]
    rw [hsum, byteWitness_zero]
    have key : (n : K) = ((n % 128 : ℕ) : K) + 128 * ((n / 128 : ℕ) : K) := by
      conv_lhs => rw [← Nat.mod_add_div n 128]
      push_cast; ring
    have hdiv : n / 128 = 0 ∨ n / 128 = 1 := by omega
    rw [key]
    rcases hdiv with h | h <;> (rw [h]; push_cast; ring)
  · rw [aeval_rows_castSucc, byteWitness_bit]
    rcases Nat.mod_two_eq_zero_or_one (n / 2 ^ (i : ℕ)) with h | h <;> simp [h]

/-- Every natural below 256 is realised as the byte of some locus point. -/
lemma cast_mem_image (n : ℕ) (hn : n < 256) :
    (n : K) ∈ L '' polynomialLocus (rows : Fin 8 → MvPolynomial (Fin 8) K) :=
  ⟨byteWitness n, byteWitness_mem n hn, by simp [L]⟩

/-- With the casts of `0..255` distinct, the gadget checks one byte. -/
theorem checksBytes [IsAlgClosed K] (hinj : Set.InjOn (Nat.cast : ℕ → K) (Set.Iio 256)) :
    AssertBytes.ChecksBytes 1 (checker : ConcreteScalarChecker K) := by
  refine ⟨rfl, ?_⟩
  change 2 ^ (8 * 1) ≤ (L '' polynomialLocus (rows : Fin 8 → MvPolynomial (Fin 8) K)).ncard
  have hsub : (fun n : ℕ => (n : K)) '' Set.Iio 256 ⊆
      L '' polynomialLocus (rows : Fin 8 → MvPolynomial (Fin 8) K) := by
    rintro _ ⟨n, hn, rfl⟩
    exact cast_mem_image n hn
  have hcard : ((fun n : ℕ => (n : K)) '' Set.Iio 256).ncard = 256 := by
    rw [hinj.ncard_image]
    simp [Set.ncard_eq_toFinset_card']
  calc (2 : ℕ) ^ (8 * 1) = 256 := by norm_num
    _ = ((fun n : ℕ => (n : K)) '' Set.Iio 256).ncard := hcard.symm
    _ ≤ _ := Set.ncard_le_ncard hsub image_finite

/-- The bound applies to the record gadget, and it is achieved: score is exactly 15. -/
theorem score_eq [IsAlgClosed K] : (checker : ConcreteScalarChecker K).score = 15 := rfl

theorem bound_applies [IsAlgClosed K] (hinj : Set.InjOn (Nat.cast : ℕ → K) (Set.Iio 256)) :
    15 ≤ (checker : ConcreteScalarChecker K).score :=
  AssertBytes.single_byte_score_lower_bound _ (checksBytes hinj)

end ZkGolfOptimality.RecordInstance
