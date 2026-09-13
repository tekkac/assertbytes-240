import AssertBytes240.Algebra.DimensionFormula

/-!
# Affine-domain dimension formula and the catenary height drop

Height inequalities for affine domains, derived from the polynomial-ring
dimension formula. These are the catenary height-drop facts used when the
divided-degree recurrence adjoins one more homogeneous equation.
-/

open MvPolynomial

noncomputable section

namespace AristotleAffineDimension

open AristotleDimensionFormula

/-
The ring map `A ⧸ (comap f P) → D ⧸ P` induced by an injective integral
ring hom `f : A → D` (with `P` a prime of `D`) is injective and integral;
hence the two quotient rings have the same Krull dimension.
-/
theorem ringKrullDim_quotient_comap_eq_of_isIntegral
    {A D : Type*} [CommRing A] [CommRing D] (f : A →+* D)
    (hf : Function.Injective f) (hint : f.IsIntegral) (P : Ideal D) :
    ringKrullDim (A ⧸ Ideal.comap f P) = ringKrullDim (D ⧸ P) := by
  convert ringKrullDim_eq_of_ringHom_isIntegral _ _ _ using 1;
  exact Ideal.quotientMap P f (by
  rfl)
  all_goals generalize_proofs at *;
  · intro x y hxy;
    obtain ⟨ a, rfl ⟩ := Ideal.Quotient.mk_surjective x; obtain ⟨ b, rfl ⟩ := Ideal.Quotient.mk_surjective y; simp_all +decide [ Ideal.Quotient.eq ] ;
  · grind +suggestions

/-- **Affine-domain dimension formula (the direction we need).**
For a prime `P` of a finitely generated domain over a field,
`dim D ≤ height P + dim (D ⧸ P)`. -/
theorem affine_ringKrullDim_le_height_add_quotient
    {K : Type*} [Field K] {D : Type*} [CommRing D] [IsDomain D] [Algebra K D]
    [Algebra.FiniteType K D] (P : Ideal D) [P.IsPrime] :
    ringKrullDim D ≤ (P.height : WithBot ℕ∞) + ringKrullDim (D ⧸ P) := by
  obtain ⟨s, g, hg_inj, hg_int⟩ := exists_integral_inj_algHom_of_fg K D
  let f : MvPolynomial (Fin s) K →+* D := g.toRingHom
  letI : Algebra (MvPolynomial (Fin s) K) D := f.toAlgebra
  haveI : Algebra.IsIntegral (MvPolynomial (Fin s) K) D := ⟨hg_int⟩
  haveI : FaithfulSMul (MvPolynomial (Fin s) K) D :=
    (faithfulSMul_iff_algebraMap_injective (MvPolynomial (Fin s) K) D).mpr hg_inj
  haveI : Algebra.HasGoingDown (MvPolynomial (Fin s) K) D := inferInstance
  haveI : IsNoetherianRing D := by
    have : Algebra.FiniteType K D := inferInstance
    exact Algebra.FiniteType.isNoetherianRing K D
  let pA : Ideal (MvPolynomial (Fin s) K) := Ideal.comap f P
  haveI hpAp : pA.IsPrime := Ideal.comap_isPrime f P
  haveI : P.LiesOver pA := ⟨rfl⟩
  have hdimD : ringKrullDim (MvPolynomial (Fin s) K) = ringKrullDim D :=
    ringKrullDim_eq_of_ringHom_isIntegral f hg_inj hg_int
  have hdimQ : ringKrullDim (MvPolynomial (Fin s) K ⧸ pA) = ringKrullDim (D ⧸ P) :=
    ringKrullDim_quotient_comap_eq_of_isIntegral f hg_inj hg_int P
  have hform : (pA.height : WithBot ℕ∞) + ringKrullDim (MvPolynomial (Fin s) K ⧸ pA)
      = (s : WithBot ℕ∞) :=
    height_add_ringKrullDim_quotient pA
  have hAdim : ringKrullDim (MvPolynomial (Fin s) K) = (s : WithBot ℕ∞) :=
    mvPoly_ringKrullDim (K := K) s
  have hle : pA.height ≤ P.height := by
    have hgd := Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown pA P
    rw [hgd]; exact le_self_add
  calc ringKrullDim D = ringKrullDim (MvPolynomial (Fin s) K) := hdimD.symm
    _ = (s : WithBot ℕ∞) := hAdim
    _ = (pA.height : WithBot ℕ∞) + ringKrullDim (MvPolynomial (Fin s) K ⧸ pA) := hform.symm
    _ = (pA.height : WithBot ℕ∞) + ringKrullDim (D ⧸ P) := by rw [hdimQ]
    _ ≤ (P.height : WithBot ℕ∞) + ringKrullDim (D ⧸ P) := by
        gcongr
        exact_mod_cast hle

/-- Passing to the domain `R ⧸ q`, a prime `m ⊇ q` minimal over `q ⊔ (x)` with
`x ∉ q` has height exactly one there. -/
theorem height_map_eq_one_of_minimalPrimes_sup
    {K : Type*} [Field K] {n : ℕ} {q m : Ideal (MvPolynomial (Fin n) K)}
    [q.IsPrime] (hqm : q ≤ m) {x : MvPolynomial (Fin n) K} (hx : x ∉ q)
    (hm : m ∈ (q ⊔ Ideal.span {x}).minimalPrimes) :
    (m.map (Ideal.Quotient.mk q)).height = 1 := by
  haveI : m.IsPrime := hm.1.1
  haveI hmb : (m.map (Ideal.Quotient.mk q)).IsPrime :=
    Ideal.isPrime_map_quotientMk_of_isPrime hqm
  refine le_antisymm (Ideal.map_height_le_one_of_mem_minimalPrimes (I := q) (x := x) hm) ?_
  have hxm : x ∈ m := hm.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self x))
  have hne : (m.map (Ideal.Quotient.mk q)) ≠ ⊥ := by
    intro h
    have hmem : Ideal.Quotient.mk q x ∈ (m.map (Ideal.Quotient.mk q)) :=
      Ideal.mem_map_of_mem _ hxm
    rw [h, Ideal.mem_bot] at hmem
    exact hx (by rwa [Ideal.Quotient.eq_zero_iff_mem] at hmem)
  rw [Ideal.height_eq_primeHeight, ENat.one_le_iff_ne_zero]
  intro h0
  rw [Ideal.primeHeight_eq_zero_iff] at h0
  have hbot : (⊥ : Ideal (MvPolynomial (Fin n) K ⧸ q)).IsPrime := Ideal.isPrime_bot
  have hle := h0.2 ⟨hbot, bot_le⟩ bot_le
  exact hne (le_bot_iff.mp hle)

/-- **Catenary height drop.** For primes `q ≤ m` of the polynomial ring, if
`x ∉ q` and `m` is minimal over `q ⊔ (x)`, then `m.height = q.height + 1`. -/
theorem height_eq_height_add_one_of_mem_minimalPrimes_sup
    {K : Type*} [Field K] {n : ℕ} {q m : Ideal (MvPolynomial (Fin n) K)}
    [q.IsPrime] (hqm : q ≤ m) {x : MvPolynomial (Fin n) K} (hx : x ∉ q)
    (hm : m ∈ (q ⊔ Ideal.span {x}).minimalPrimes) :
    m.height = q.height + 1 := by
  haveI hmp : m.IsPrime := hm.1.1
  -- E1, E2: dimension formula in R
  have E1 : (q.height : WithBot ℕ∞) + ringKrullDim (MvPolynomial (Fin n) K ⧸ q)
      = (n : WithBot ℕ∞) := height_add_ringKrullDim_quotient q
  have E2 : (m.height : WithBot ℕ∞) + ringKrullDim (MvPolynomial (Fin n) K ⧸ m)
      = (n : WithBot ℕ∞) := height_add_ringKrullDim_quotient m
  -- A: affine bound in the domain R⧸q
  have A : ringKrullDim (MvPolynomial (Fin n) K ⧸ q)
      ≤ 1 + ringKrullDim (MvPolynomial (Fin n) K ⧸ m) := by
    haveI : IsDomain (MvPolynomial (Fin n) K ⧸ q) := Ideal.Quotient.isDomain q
    haveI hmbar : (m.map (Ideal.Quotient.mk q)).IsPrime :=
      Ideal.isPrime_map_quotientMk_of_isPrime hqm
    have haff := affine_ringKrullDim_le_height_add_quotient (K := K)
      (m.map (Ideal.Quotient.mk q))
    rw [height_map_eq_one_of_minimalPrimes_sup hqm hx hm] at haff
    rw [ringKrullDim_quotQuot_eq q m hqm] at haff
    simpa using haff
  -- strict: q.height < m.height
  have hqm_lt : q < m := lt_of_le_of_ne hqm (fun h => hx (h.symm ▸
    hm.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self x))))
  have hmfin : m.height ≠ ⊤ := by
    intro htop
    have hle := Ideal.height_le_ringKrullDim_of_ne_top (I := m) hmp.ne_top
    rw [htop, mvPoly_ringKrullDim (K := K) n] at hle
    norm_cast at hle
  haveI : m.FiniteHeight := ⟨Or.inr hmfin⟩
  have lt : q.height < m.height := by
    rw [Ideal.height_eq_primeHeight, Ideal.height_eq_primeHeight]
    exact Ideal.primeHeight_strict_mono hqm_lt
  -- arithmetic
  set dq := ringKrullDim (MvPolynomial (Fin n) K ⧸ q) with hdq
  set dm := ringKrullDim (MvPolynomial (Fin n) K ⧸ m) with hdm
  clear_value dq dm
  have hdqbot : dq ≠ ⊥ := by rintro rfl; simp at E1
  have hdmbot : dm ≠ ⊥ := by rintro rfl; simp at E2
  lift dq to ℕ∞ using hdqbot with dq'
  lift dm to ℕ∞ using hdmbot with dm'
  rw [← WithBot.coe_add] at E1 E2
  norm_cast at E1 E2
  rw [← WithBot.coe_one, ← WithBot.coe_add, WithBot.coe_le_coe] at A
  have hqt : q.height ≠ ⊤ := by
    rintro h; rw [h, WithTop.top_add] at E1; exact absurd E1 WithTop.top_ne_coe
  have hmt : m.height ≠ ⊤ := hmfin
  have hdqt : dq' ≠ ⊤ := by
    rintro rfl; rw [WithTop.add_top] at E1; exact absurd E1 WithTop.top_ne_coe
  have hdmt : dm' ≠ ⊤ := by
    rintro rfl; rw [WithTop.add_top] at E2; exact absurd E2 WithTop.top_ne_coe
  set hqh := q.height with hqhdef
  set hmh := m.height with hmhdef
  clear_value hqh hmh
  lift hqh to ℕ using hqt
  lift hmh to ℕ using hmt
  lift dq' to ℕ using hdqt
  lift dm' to ℕ using hdmt
  norm_cast at *
  omega

end AristotleAffineDimension
