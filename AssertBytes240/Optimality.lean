import AssertBytes240.Algebra
import AssertBytes240.Components

/-!
# Optimality of the AssertBytes score

This file exposes the completed affine Bezout component bound, its finite
quadric-projection consequence, and the byte-count-parametric AssertBytes lower
bound.  It is deliberately independent of the zkGolf circuit DSL: a separate
adapter can connect a concrete circuit to `ConcreteScalarChecker`.
-/

noncomputable section

open MvPolynomial

namespace ZkGolfOptimality

namespace AffineBezout

open ComponentBound

/-- A degree-`d` system has at most `min (d^C) (d^n)` minimal-prime components. -/
theorem minimalPrimes_ncard_le
    {K : Type*} [Field K] [IsAlgClosed K] {n C : ℕ}
    (f : Fin C → MvPolynomial (Fin n) K) (d : ℕ) (hd_pos : 1 ≤ d)
    (hd : ∀ i, (f i).totalDegree ≤ d) :
    Set.ncard (Ideal.span (Set.range f)).minimalPrimes ≤ min (d ^ C) (d ^ n) :=
  goal_minimalPrimes_ncard_le f d hd_pos hd

/-- A system of `C` quadrics in `n` variables has at most `2^min(C,n)` components. -/
theorem quadric_minimalPrimes_ncard_le
    {K : Type*} [Field K] [IsAlgClosed K] {n C : ℕ}
    (q : Fin C → MvPolynomial (Fin n) K)
    (hq : IsQuadricSystem q) :
    Set.ncard (quadricIdeal q).minimalPrimes ≤ 2 ^ min C n := by
  have hbez :
      Set.ncard (Ideal.span (Set.range q)).minimalPrimes ≤
        min (2 ^ C) (2 ^ n) :=
    minimalPrimes_ncard_le q 2 (by norm_num) hq
  have hpow_min : min (2 ^ C) (2 ^ n) = 2 ^ min C n := by
    by_cases hCn : C ≤ n
    · have hpow : 2 ^ C ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hCn
      simp [min_eq_left hCn, min_eq_left hpow]
    · have hnC : n ≤ C := Nat.le_of_not_ge hCn
      have hpow : 2 ^ n ≤ 2 ^ C := Nat.pow_le_pow_right (by norm_num) hnC
      simp [min_eq_right hnC, min_eq_right hpow]
  simpa [quadricIdeal, hpow_min] using hbez

/-- A finite scalar projection of a quadric locus has at most `2^min(C,n)` values. -/
theorem scalar_projection_ncard_le
    {K : Type*} [Field K] [IsAlgClosed K] {n C : ℕ}
    (q : Fin C → MvPolynomial (Fin n) K)
    (hq : IsQuadricSystem q)
    (L : (Fin n → K) →ₗ[K] K)
    (hfin : (L '' polynomialLocus q).Finite) :
    (L '' polynomialLocus q).ncard ≤ 2 ^ min C n := by
  simpa [polynomialLocus_eq_zeroLocus_quadricIdeal q] using
    ComponentBound.scalar_projection_ncard_le_of_minimalPrimes_bound
      (quadricIdeal q) L
      (by simpa [polynomialLocus_eq_zeroLocus_quadricIdeal q] using hfin)
      (quadric_minimalPrimes_ncard_le q hq)

end AffineBezout

namespace AssertBytes

open AffineBezout ComponentBound

/--
An algebraic checker with quadratic constraints and a finite scalar projection
of its accepted locus.
-/
structure ConcreteScalarChecker (K : Type*) [Field K] [IsAlgClosed K] where
  publicVars : ℕ
  allocations : ℕ
  constraints : ℕ
  q : Fin constraints → MvPolynomial (Fin (publicVars + allocations)) K
  hq : IsQuadricSystem q
  L : (Fin (publicVars + allocations) → K) →ₗ[K] K
  hfinite : (L '' polynomialLocus q).Finite

namespace ConcreteScalarChecker

def totalVars {K : Type*} [Field K] [IsAlgClosed K]
    (X : ConcreteScalarChecker K) : ℕ :=
  X.publicVars + X.allocations

def score {K : Type*} [Field K] [IsAlgClosed K]
    (X : ConcreteScalarChecker K) : ℕ :=
  X.allocations + X.constraints

def acceptedScalarCard {K : Type*} [Field K] [IsAlgClosed K]
    (X : ConcreteScalarChecker K) : ℕ :=
  (X.L '' polynomialLocus X.q).ncard

end ConcreteScalarChecker

/-- A checker whose finite scalar image represents at least `B` independent bytes.

A lower bound, not an equality. The proofs only use `≤`. An instance over a
prime field only gives `≤` over the closure, since its accepted points inject
into the closure's points. -/
def ChecksBytes {K : Type*} [Field K] [IsAlgClosed K]
    (B : ℕ) (X : ConcreteScalarChecker K) : Prop :=
  X.publicVars = B ∧ 2 ^ (8 * B) ≤ X.acceptedScalarCard

theorem acceptedScalarCard_le
    {K : Type*} [Field K] [IsAlgClosed K]
    (X : ConcreteScalarChecker K) :
    X.acceptedScalarCard ≤ 2 ^ min X.constraints X.totalVars := by
  simpa [ConcreteScalarChecker.acceptedScalarCard, ConcreteScalarChecker.totalVars] using
    AffineBezout.scalar_projection_ncard_le X.q X.hq X.L X.hfinite

theorem constraints_lower_bound
    {K : Type*} [Field K] [IsAlgClosed K]
    (B : ℕ) (X : ConcreteScalarChecker K) (hX : ChecksBytes B X) :
    8 * B ≤ X.constraints := by
  have hcard : 2 ^ (8 * B) ≤ 2 ^ min X.constraints X.totalVars :=
    hX.2.trans (acceptedScalarCard_le X)
  have hmin : 8 * B ≤ min X.constraints X.totalVars :=
    (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hcard
  exact hmin.trans (min_le_left X.constraints X.totalVars)

theorem totalVars_lower_bound
    {K : Type*} [Field K] [IsAlgClosed K]
    (B : ℕ) (X : ConcreteScalarChecker K) (hX : ChecksBytes B X) :
    8 * B ≤ X.totalVars := by
  have hcard : 2 ^ (8 * B) ≤ 2 ^ min X.constraints X.totalVars :=
    hX.2.trans (acceptedScalarCard_le X)
  have hmin : 8 * B ≤ min X.constraints X.totalVars :=
    (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hcard
  exact hmin.trans (min_le_right X.constraints X.totalVars)

theorem allocations_lower_bound
    {K : Type*} [Field K] [IsAlgClosed K]
    (B : ℕ) (X : ConcreteScalarChecker K) (hX : ChecksBytes B X) :
    7 * B ≤ X.allocations := by
  have hvars := totalVars_lower_bound B X hX
  rw [ConcreteScalarChecker.totalVars, hX.1] at hvars
  omega

/-- Batching `B` byte checks cannot improve on the optimal per-byte score `15`. -/
theorem score_lower_bound
    {K : Type*} [Field K] [IsAlgClosed K]
    (B : ℕ) (X : ConcreteScalarChecker K) (hX : ChecksBytes B X) :
    15 * B ≤ X.score := by
  have hA := allocations_lower_bound B X hX
  have hC := constraints_lower_bound B X hX
  rw [ConcreteScalarChecker.score]
  omega

theorem single_byte_score_lower_bound
    {K : Type*} [Field K] [IsAlgClosed K]
    (X : ConcreteScalarChecker K) (hX : ChecksBytes 1 X) :
    15 ≤ X.score := by
  simpa using score_lower_bound 1 X hX

theorem sixteen_bytes_score_lower_bound
    {K : Type*} [Field K] [IsAlgClosed K]
    (X : ConcreteScalarChecker K) (hX : ChecksBytes 16 X) :
    240 ≤ X.score := by
  simpa using score_lower_bound 16 X hX

end AssertBytes
end ZkGolfOptimality
