import AssertBytes240.RecordInstance

/-!
# The full record circuit is an instance of the model

All sixteen bytes of the 240-point circuit as a `ConcreteScalarChecker`: the
one-byte gadget on each of sixteen disjoint variable blocks, and the packing
map `∑ 256^j · x_j`. Score is 112 + 128 = 240 by definition and at least 240 by
`sixteen_bytes_score_lower_bound`.
-/

noncomputable section

open MvPolynomial

namespace ZkGolfOptimality.RecordInstance16

open ComponentBound AssertBytes RecordInstance

variable {K : Type*} [Field K]

/-- Variables: 16 public bytes, then 112 witness bits. -/
abbrev V := Fin (16 + 112)

/-- Public coordinate of byte `j`. -/
def pub (j : Fin 16) : V := Fin.castAdd 112 j

/-- Witness bit `i` of byte `j`. -/
def wit (j : Fin 16) (i : Fin 7) : V := Fin.natAdd 16 (finProdFinEquiv (j, i))

/-- Byte `j`'s copy of the one-byte variable set. -/
def emb (j : Fin 16) : Fin 8 → V := Fin.cases (pub j) (wit j)

/-- Row `(j, r)` is row `r` of the one-byte gadget on byte `j`'s variables. -/
def rows16 : Fin (16 * 8) → MvPolynomial V K :=
  fun k => rename (emb (finProdFinEquiv.symm k).1) (rows (finProdFinEquiv.symm k).2)

lemma rows16_isQuadric : IsQuadricSystem (rows16 : Fin (16 * 8) → MvPolynomial V K) :=
  fun _ => (totalDegree_rename_le _ _).trans (rows_isQuadric _)

lemma mem_locus16_iff (v : V → K) :
    v ∈ polynomialLocus (rows16 : Fin (16 * 8) → MvPolynomial V K) ↔
      ∀ j : Fin 16, (v ∘ emb j) ∈ polynomialLocus (rows : Fin 8 → MvPolynomial (Fin 8) K) := by
  simp only [polynomialLocus, zeroLocus_span, Set.mem_setOf_eq, Set.forall_mem_range, rows16,
    aeval_rename]
  constructor
  · intro h j r
    simpa using h (finProdFinEquiv (j, r))
  · intro h k
    exact h _ _

/-- The packing map `∑ 256^j · x_j`. -/
def L16 : (V → K) →ₗ[K] K := ∑ j : Fin 16, ((256 : K) ^ (j : ℕ)) • LinearMap.proj (pub j)

lemma L16_apply (v : V → K) : L16 v = ∑ j : Fin 16, (256 : K) ^ (j : ℕ) * v (pub j) := by
  simp [L16]

/-- Base-`b` expansion below `b^k`, from `Nat.mod_mul`. -/
lemma mod_pow_eq_sum (b n k : ℕ) :
    n % b ^ k = ∑ i : Fin k, b ^ (i : ℕ) * (n / b ^ (i : ℕ) % b) := by
  induction k with
  | zero => simp [Nat.mod_one]
  | succ k ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [← ih, pow_succ, Nat.mod_mul]

lemma emb_zero (j : Fin 16) : emb j 0 = pub j := rfl

lemma image_finite16 :
    (L16 '' polynomialLocus (rows16 : Fin (16 * 8) → MvPolynomial V K)).Finite := by
  refine (Set.finite_Iio (2 ^ 128)).image (fun n : ℕ => (n : K)) |>.subset ?_
  rintro _ ⟨v, hv, rfl⟩
  rw [mem_locus16_iff] at hv
  choose n hn hvn using fun j => locus_byte_lt (v ∘ emb j) (hv j)
  have hpub : ∀ j, v (pub j) = n j := fun j => by simpa [emb_zero] using hvn j
  refine ⟨∑ j : Fin 16, 256 ^ (j : ℕ) * n j, ?_, ?_⟩
  · show ∑ j : Fin 16, 256 ^ (j : ℕ) * n j < 2 ^ 128
    calc ∑ j : Fin 16, 256 ^ (j : ℕ) * n j ≤ ∑ j : Fin 16, 256 ^ (j : ℕ) * 255 :=
          Finset.sum_le_sum fun j _ => Nat.mul_le_mul_left _ (by have := hn j; omega)
      _ < 2 ^ 128 := by simp [Fin.sum_univ_succ]
  · rw [L16_apply]; push_cast
    exact Finset.sum_congr rfl fun j _ => by rw [hpub]

/-- The locus point for `N < 2^128`: byte `j` is the `j`-th base-256 digit of `N`. -/
def witness16 (N : ℕ) : V → K :=
  Fin.addCases (fun j : Fin 16 => byteWitness (N / 256 ^ (j : ℕ) % 256) 0)
    (fun w : Fin (16 * 7) =>
      byteWitness (N / 256 ^ ((finProdFinEquiv.symm w).1 : ℕ) % 256) (finProdFinEquiv.symm w).2.succ)

lemma witness16_comp_emb (N : ℕ) (j : Fin 16) :
    witness16 (K := K) N ∘ emb j = byteWitness (N / 256 ^ (j : ℕ) % 256) := by
  funext i
  refine Fin.cases ?_ (fun i => ?_) i
  · simp [witness16, emb, pub]
  · simp [witness16, emb, wit]

lemma cast_mem_image16 (N : ℕ) (hN : N < 2 ^ 128) :
    (N : K) ∈ L16 '' polynomialLocus (rows16 : Fin (16 * 8) → MvPolynomial V K) := by
  refine ⟨witness16 N, ?_, ?_⟩
  · rw [mem_locus16_iff]
    intro j
    rw [witness16_comp_emb]
    exact byteWitness_mem _ (Nat.mod_lt _ (by norm_num))
  · rw [L16_apply]
    have hdig : ∀ j : Fin 16,
        witness16 (K := K) N (pub j) = ((N / 256 ^ (j : ℕ) % 256 : ℕ) : K) := by
      intro j
      have h := congrFun (witness16_comp_emb (K := K) N j) 0
      simpa [emb_zero] using h
    simp_rw [hdig]
    have h16 : N < 256 ^ 16 := by
      have : (256 : ℕ) ^ 16 = 2 ^ 128 := by norm_num
      rw [this]; exact hN
    conv_rhs => rw [← Nat.mod_eq_of_lt h16, mod_pow_eq_sum]
    push_cast
    rfl

/-- The sixteen-byte record circuit as a checker: 16 public, 112 allocations, 128 constraints. -/
def checker16 [IsAlgClosed K] : ConcreteScalarChecker K where
  publicVars := 16
  allocations := 112
  constraints := 16 * 8
  q := rows16
  hq := rows16_isQuadric
  L := L16
  hfinite := image_finite16

/-- With the casts of `0..2^128 - 1` distinct, the circuit checks sixteen bytes. -/
theorem checksBytes16 [IsAlgClosed K]
    (hinj : Set.InjOn (Nat.cast : ℕ → K) (Set.Iio (2 ^ 128))) :
    ChecksBytes 16 (checker16 : ConcreteScalarChecker K) := by
  refine ⟨rfl, ?_⟩
  change 2 ^ (8 * 16) ≤
    (L16 '' polynomialLocus (rows16 : Fin (16 * 8) → MvPolynomial V K)).ncard
  have hsub : (fun n : ℕ => (n : K)) '' Set.Iio (2 ^ 128) ⊆
      L16 '' polynomialLocus (rows16 : Fin (16 * 8) → MvPolynomial V K) := by
    rintro _ ⟨n, hn, rfl⟩
    exact cast_mem_image16 n hn
  have hcard : ((fun n : ℕ => (n : K)) '' Set.Iio (2 ^ 128)).ncard = 2 ^ 128 := by
    rw [hinj.ncard_image]
    simp [Set.ncard_eq_toFinset_card']
  calc (2 : ℕ) ^ (8 * 16) = 2 ^ 128 := by norm_num
    _ = _ := hcard.symm
    _ ≤ _ := Set.ncard_le_ncard hsub image_finite16

/-- Over the closure of a prime field with `p ≥ 2^128`, the cast hypothesis holds. -/
theorem checksBytes16_of_charP [IsAlgClosed K] (p : ℕ) [CharP K p] (hp : 2 ^ 128 ≤ p) :
    ChecksBytes 16 (checker16 : ConcreteScalarChecker K) :=
  checksBytes16 ((CharP.natCast_injOn_Iio K p).mono (Set.Iio_subset_Iio hp))

theorem score16_eq [IsAlgClosed K] : (checker16 : ConcreteScalarChecker K).score = 240 := rfl

/-- The 240 bound applies to the record circuit, and the record attains it. -/
theorem bound_applies16 [IsAlgClosed K]
    (hinj : Set.InjOn (Nat.cast : ℕ → K) (Set.Iio (2 ^ 128))) :
    240 ≤ (checker16 : ConcreteScalarChecker K).score :=
  sixteen_bytes_score_lower_bound _ (checksBytes16 hinj)

end ZkGolfOptimality.RecordInstance16
