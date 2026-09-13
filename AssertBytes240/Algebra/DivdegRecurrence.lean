import AssertBytes240.Algebra.ComponentExtraction
import AssertBytes240.Algebra.GradeDescent
import AssertBytes240.Algebra.GradeHeight
import AssertBytes240.Algebra.AffineDimension
import AssertBytes240.Algebra.ChargeBridge

/-!
# T2-W4 — the divided-degree recurrence (homogeneous strong Bézout)

Implements Lazard's divided-degree recurrence for homogeneous systems.
It constructs `RegCond` recombinations, proves `divdegQ ≤ 1`, and turns that
charge estimate into the relevant homogeneous minimal-prime count consumed by
the affine transfer.
-/

open MvPolynomial RingTheory.Sequence

noncomputable section

attribute [local instance] MvPolynomial.gradedAlgebra

variable {K : Type*} [Field K] {n : ℕ}

/-
Convert Mathlib's graded homogeneity to the project's `IsHomog`.
-/
theorem IsHomog_of_isHomogeneous {I : Ideal (MvPolynomial (Fin n) K)}
    (hI : I.IsHomogeneous (homogeneousSubmodule (Fin n) K)) : IsHomog I := by
  convert hI using 1;
  ext;
  constructor;
  · intro h;
    intro i x hx;
    convert h x hx i using 1;
    convert MvPolynomial.decomposition.decompose'_apply _ _;
  · intro hI p hp e;
    convert hI _ hp;
    convert rfl;
    convert MvPolynomial.decomposition.decompose'_apply _ _

open Classical in
/-- Instance-free isolated component (⊤ at non-primes, harmless). -/
def isoComp' (I p : Ideal (MvPolynomial (Fin n) K)) : Ideal (MvPolynomial (Fin n) K) :=
  if h : p.IsPrime then @isoComp K _ n I p h else ⊤

open Classical in
/-- Uniform-`d` divided degree over the (finite) set of minimal primes. -/
def divdegQ (I : Ideal (MvPolynomial (Fin n) K)) (d : ℕ) : ℚ :=
  ∑ p ∈ (Ideal.finite_minimalPrimes_of_isNoetherianRing
      (MvPolynomial (Fin n) K) I).toFinset,
    degQ (isoComp' I p) / (d : ℚ) ^ (p.height.toNat)

/-- Lazard's Definition-4 regularity condition. -/
def RegCond {C : ℕ} (f : Fin C → MvPolynomial (Fin n) K) : Prop :=
  ∀ i : Fin C,
    ∀ p ∈ associatedPrimes (MvPolynomial (Fin n) K)
      ((MvPolynomial (Fin n) K) ⧸
        ((Ideal.span (f '' {j | j < i})) • ⊤ :
          Submodule (MvPolynomial (Fin n) K) (MvPolynomial (Fin n) K))),
      f i ∈ p → ∀ j : Fin C, i < j → f j ∈ p

/-
Affine prime avoidance over an infinite field: if an affine subspace
`a + V` (with `V` a `K`-submodule) is not contained in any of finitely many
prime ideals, then some point of `a + V` avoids all of them.
-/
theorem exists_mem_affine_avoiding
    {K R : Type*} [Field K] [Infinite K] [CommRing R] [Algebra K R]
    (a : R) (V : Submodule K R) (s : Finset (Ideal R))
    (hprime : ∀ P ∈ s, P.IsPrime)
    (hs : ∀ P ∈ s, ∃ v ∈ V, a + v ∉ P) :
    ∃ v ∈ V, ∀ P ∈ s, a + v ∉ P := by
  induction' s using Finset.cons_induction with P s hs ih;
  · exact ⟨ 0, V.zero_mem, by simp +decide ⟩;
  · obtain ⟨ v, hv₁, hv₂ ⟩ := ih ( fun P hP => hprime P ( Finset.mem_cons_of_mem hP ) ) ( fun P hP => hs P ( Finset.mem_cons_of_mem hP ) );
    by_cases hv₃ : a + v ∈ P;
    · obtain ⟨ w, hw₁, hw₂ ⟩ := hs P ( Finset.mem_cons_self _ _ );
      -- Consider the one-parameter family, for `t : K`, `z t := a + v + t • (w - v)` (with `v + t • (w - v) ∈ V` since `V` is a `K`-submodule).
      have h_family : ∀ P_1 ∈ Finset.cons P s ‹_›, Set.Finite {t : K | a + v + t • (w - v) ∈ P_1} := by
        intro P_1 hP_1
        by_cases hP_1_eq_P : P_1 = P;
        · refine' Set.Finite.subset ( Set.finite_singleton 0 ) _;
          intro t ht; simp_all +decide [ add_assoc, Ideal.add_mem_iff_right ] ;
          simp_all +decide [ ← add_assoc, Ideal.add_mem_iff_right ];
          contrapose! hw₂;
          convert P.add_mem hv₃ ( P.smul_mem ( algebraMap K R t⁻¹ ) ht ) using 1 ; simp +decide [ hw₂, Algebra.smul_def ];
          simp +decide [ ← mul_assoc, ← map_mul, hw₂ ];
        · have h_finite : ∀ t₁ t₂ : K, t₁ ≠ t₂ → a + v + t₁ • (w - v) ∈ P_1 → a + v + t₂ • (w - v) ∈ P_1 → False := by
            intro t₁ t₂ hne ht₁ ht₂
            have h_diff : (t₁ - t₂) • (w - v) ∈ P_1 := by
              convert P_1.sub_mem ht₁ ht₂ using 1 ; simp +decide [ sub_smul ];
            have h_unit : IsUnit (algebraMap K R (t₁ - t₂)) := by
              exact IsUnit.map ( algebraMap K R ) ( isUnit_iff_ne_zero.mpr ( sub_ne_zero.mpr hne ) );
            have h_unit : (w - v) ∈ P_1 := by
              convert P_1.mul_mem_left ( h_unit.unit.inv ) h_diff using 1 ; simp +decide [ Algebra.smul_def ];
              simp +decide [ ← mul_assoc, ← map_sub ];
            have h_unit : a + v ∈ P_1 := by
              convert P_1.sub_mem ht₁ ( P_1.mul_mem_left ( t₁ • 1 ) h_unit ) using 1 ; simp +decide [ mul_sub, sub_mul, mul_assoc, mul_left_comm ];
              simp +decide [ smul_sub ];
            exact hv₂ P_1 ( Finset.mem_of_mem_cons_of_ne hP_1 hP_1_eq_P ) h_unit;
          exact Set.Subsingleton.finite ( fun t₁ ht₁ t₂ ht₂ => Classical.not_not.1 fun h => h_finite t₁ t₂ h ht₁ ht₂ );
      -- Since $K$ is infinite, there exists a scalar $t₀$ such that $a + v + t₀ • (w - v) ∉ P_1$ for all $P_1 ∈ Finset.cons P s ‹_›$.
      obtain ⟨ t₀, ht₀ ⟩ : ∃ t₀ : K, ∀ P_1 ∈ Finset.cons P s ‹_›, a + v + t₀ • (w - v) ∉ P_1 := by
        have h_finite : Set.Finite (⋃ P_1 ∈ Finset.cons P s ‹_›, {t : K | a + v + t • (w - v) ∈ P_1}) := by
          exact Set.Finite.biUnion ( Finset.finite_toSet _ ) h_family;
        exact Exists.elim ( h_finite.exists_notMem ) fun t ht => ⟨ t, fun P_1 hP_1 => fun h => ht <| Set.mem_iUnion₂.mpr ⟨ P_1, hP_1, h ⟩ ⟩;
      exact ⟨ v + t₀ • ( w - v ), V.add_mem hv₁ ( V.smul_mem t₀ ( V.sub_mem hw₁ hv₁ ) ), fun P_1 hP_1 => by simpa [ add_assoc ] using ht₀ P_1 hP_1 ⟩;
    · exact ⟨ v, hv₁, by aesop ⟩

/-
Escape lemma: a positive-degree homogeneous polynomial `fm` outside a prime
`p` has, for any target degree `ei ≥ em`, a homogeneous multiple `c * fm` of
degree `ei` still outside `p`.
-/
theorem exists_homog_mul_notMem
    {p : Ideal (MvPolynomial (Fin n) K)} (hp : p.IsPrime)
    {fm : MvPolynomial (Fin n) K} {em ei : ℕ} (hem : 1 ≤ em) (hle : em ≤ ei)
    (hfm : fm ∈ homogeneousSubmodule (Fin n) K em) (hnotmem : fm ∉ p) :
    ∃ c, c ∈ homogeneousSubmodule (Fin n) K (ei - em) ∧ c * fm ∉ p ∧
      c * fm ∈ homogeneousSubmodule (Fin n) K ei := by
  obtain ⟨t, ht⟩ : ∃ t : Fin n, MvPolynomial.X t ∉ p := by
    contrapose! hnotmem;
    -- Since `fm` is homogeneous of degree `em ≥ 1`, it lies in `varsIdeal`.
    have hfm_varsIdeal : fm ∈ varsIdeal := by
      convert homogeneous_mem_varsIdeal_pow ( show 1 ≤ em from hem ) hfm;
      lia;
    exact Ideal.span_le.mpr ( Set.range_subset_iff.mpr hnotmem ) hfm_varsIdeal;
  refine' ⟨ ( MvPolynomial.X t ) ^ ( ei - em ), _, _, _ ⟩ <;> simp_all +decide [ homogeneousSubmodule ];
  · convert MvPolynomial.IsHomogeneous.pow ( MvPolynomial.isHomogeneous_X _ _ ) ( ei - em ) using 1;
    ring;
  · exact fun h => hnotmem <| hp.mem_or_mem h |>.resolve_left ( by exact fun h' => ht <| hp.mem_of_pow_mem _ h' );
  · convert MvPolynomial.IsHomogeneous.mul ( MvPolynomial.isHomogeneous_X _ _ |> MvPolynomial.IsHomogeneous.pow <| ei - em ) hfm using 1 ; simp +decide [ Nat.sub_add_cancel hle ]

/-
Triangular recombinations preserve the span: if each `g i` differs from
`f i` by an element of the span of the strictly-later `f j`, the two families
span the same ideal.
-/
theorem span_range_eq_of_triangular {R : Type*} [CommRing R] {C : ℕ}
    (f g : Fin C → R)
    (h : ∀ i, g i - f i ∈ Ideal.span (f '' {j | i < j})) :
    Ideal.span (Set.range g) = Ideal.span (Set.range f) := by
  refine' le_antisymm _ _;
  · rw [ Ideal.span_le, Set.range_subset_iff ];
    exact fun i => by simpa using Ideal.add_mem _ ( Ideal.subset_span ( Set.mem_range_self i ) ) ( Ideal.span_mono ( Set.image_subset_range _ _ ) ( h i ) ) ;
  · rw [ Ideal.span_le, Set.range_subset_iff ];
    -- By induction on $C - y.val$, we can show that $f y$ is in the ideal generated by the range of $g$.
    have h_ind : ∀ y : Fin C, (∀ z : Fin C, y < z → f z ∈ Ideal.span (Set.range g)) → f y ∈ Ideal.span (Set.range g) := by
      intro y hy
      have h_diff : g y - f y ∈ Ideal.span (Set.range g) := by
        exact Ideal.span_le.mpr ( Set.image_subset_iff.mpr fun z hz => hy z hz ) ( h y );
      simpa using Ideal.sub_mem _ ( Ideal.subset_span ( Set.mem_range_self y ) ) h_diff;
    intro y;
    induction' n : C - y.val using Nat.strong_induction_on with n ih generalizing y;
    exact h_ind y fun z hz => ih _ ( by omega ) _ rfl

open Classical in
/-- One recombination step: choose a homogeneous degree-`deg ik` correction
`v`, a combination of strictly-later generators, so that `f ik + v` avoids every
associated prime of the current prefix ideal from which some later generator
escapes. -/
theorem exists_step_value [Infinite K] {C : ℕ}
    (f : Fin C → MvPolynomial (Fin n) K) (deg : Fin C → ℕ)
    (hpos : ∀ i, 1 ≤ deg i)
    (hhom : ∀ i, f i ∈ homogeneousSubmodule (Fin n) K (deg i))
    (hanti : ∀ i j : Fin C, i ≤ j → deg j ≤ deg i)
    (g : Fin C → MvPolynomial (Fin n) K) (ik : Fin C) :
    ∃ v : MvPolynomial (Fin n) K,
      v ∈ homogeneousSubmodule (Fin n) K (deg ik) ∧
      v ∈ Ideal.span (f '' {j | ik < j}) ∧
      ∀ p ∈ associatedPrimes (MvPolynomial (Fin n) K)
          ((MvPolynomial (Fin n) K) ⧸
            ((Ideal.span (g '' {j | j < ik})) • ⊤ :
              Submodule (MvPolynomial (Fin n) K) (MvPolynomial (Fin n) K))),
        (∃ m : Fin C, ik ≤ m ∧ f m ∉ p) → f ik + v ∉ p := by
  have := @exists_mem_affine_avoiding;
  contrapose! this;
  refine' ⟨ _, _, _, _, _, _, _ ⟩;
  exact K;
  exact MvPolynomial ( Fin n ) K;
  all_goals try infer_instance;
  refine' ⟨ f ik, Submodule.span K { x | ∃ j : Fin C, ik < j ∧ ∃ c : MvPolynomial ( Fin n ) K, c ∈ homogeneousSubmodule ( Fin n ) K ( deg ik - deg j ) ∧ x = c * f j }, _, _, _, _ ⟩;
  exact Finset.filter ( fun p => ∃ m : Fin C, ik ≤ m ∧ f m ∉ p ) ( Set.Finite.toFinset ( associatedPrimes.finite ( MvPolynomial ( Fin n ) K ) ( ( MvPolynomial ( Fin n ) K ) ⧸ ( Ideal.span ( g '' { j | j < ik } ) • ⊤ : Submodule ( MvPolynomial ( Fin n ) K ) ( MvPolynomial ( Fin n ) K ) ) ) ) );
  · simp +decide [ associatedPrimes ];
    exact fun P hP x hx hx' => hP.1;
  · intro P hP;
    obtain ⟨ m, hm₁, hm₂ ⟩ := Finset.mem_filter.mp hP |>.2;
    by_cases hikm : ik < m;
    · obtain ⟨ c, hc₁, hc₂, hc₃ ⟩ := exists_homog_mul_notMem ( show P.IsPrime from by
                                                                simp +zetaDelta at *;
                                                                exact hP.1.1 ) ( hpos m ) ( hanti _ _ hikm.le ) ( hhom m ) hm₂;
      by_cases hikm : f ik ∈ P;
      · refine' ⟨ c * f m, _, _ ⟩;
        · exact Submodule.subset_span ⟨ m, by assumption, c, hc₁, rfl ⟩;
        · exact fun h => hc₂ <| by simpa using P.sub_mem h hikm;
      · exact ⟨ 0, Submodule.zero_mem _, by simpa using hikm ⟩;
    · simp_all +decide [ le_antisymm hm₁ ( not_lt.mp hikm ) ];
      exact ⟨ 0, Submodule.zero_mem _, by simpa using hm₂ ⟩;
  · intro v hv;
    refine' this v _ _ |> fun ⟨ p, hp₁, hp₂, hp₃ ⟩ => ⟨ p, _, hp₃ ⟩;
    · refine' Submodule.span_induction _ _ _ _ hv;
      · rintro x ⟨ j, hj, c, hc, rfl ⟩;
        convert MvPolynomial.IsHomogeneous.mul hc ( hhom j ) using 1;
        rw [ Nat.sub_add_cancel ( hanti _ _ hj.le ) ];
        rfl;
      · exact zero_mem _;
      · exact fun x y hx hy hx' hy' => Submodule.add_mem _ hx' hy';
      · exact fun a x hx hx' => Submodule.smul_mem _ _ hx';
    · rw [ Submodule.mem_span ] at hv;
      specialize hv ( Ideal.span ( f '' { j | ik < j } ) |> Submodule.restrictScalars K );
      exact hv fun x hx => by rcases hx with ⟨ j, hj, c, hc, rfl ⟩ ; exact Ideal.mul_mem_left _ _ ( Ideal.subset_span ⟨ j, hj, rfl ⟩ ) ;
    · simp +zetaDelta at *;
      exact ⟨ hp₁, hp₂ ⟩

/-
The prefix-recursion behind `exists_regCond_sorted`: after processing the
first `k` coordinates there is a family `g` agreeing with `f` from index `k` on,
homogeneous, triangular, and satisfying the escape condition on the processed
prefix.
-/
set_option maxHeartbeats 1600000 in
theorem exists_regCond_sorted_aux [Infinite K] {C : ℕ}
    (f : Fin C → MvPolynomial (Fin n) K) (deg : Fin C → ℕ)
    (hpos : ∀ i, 1 ≤ deg i)
    (hhom : ∀ i, f i ∈ homogeneousSubmodule (Fin n) K (deg i))
    (hanti : ∀ i j : Fin C, i ≤ j → deg j ≤ deg i) :
    ∀ k : ℕ, ∃ g : Fin C → MvPolynomial (Fin n) K,
      (∀ i : Fin C, k ≤ i.val → g i = f i) ∧
      (∀ i : Fin C, g i ∈ homogeneousSubmodule (Fin n) K (deg i)) ∧
      (∀ i : Fin C, g i - f i ∈ Ideal.span (f '' {j | i < j})) ∧
      (∀ i : Fin C, i.val < k → ∀ p ∈ associatedPrimes (MvPolynomial (Fin n) K)
          ((MvPolynomial (Fin n) K) ⧸
            ((Ideal.span (g '' {j | j < i})) • ⊤ :
              Submodule (MvPolynomial (Fin n) K) (MvPolynomial (Fin n) K))),
          (∃ m : Fin C, i ≤ m ∧ f m ∉ p) → g i ∉ p) := by
  intro k;
  induction' k with k ih;
  · aesop;
  · by_cases hk : k < C;
    · obtain ⟨ g, hg₁, hg₂, hg₃, hg₄ ⟩ := ih
      obtain ⟨ v, hv₁, hv₂, hv₃ ⟩ := exists_step_value f deg hpos hhom hanti g ⟨ k, hk ⟩
      use Function.update g ⟨ k, hk ⟩ (f ⟨ k, hk ⟩ + v);
      refine' ⟨ _, _, _, _ ⟩;
      · grind;
      · intro i; by_cases hi : i = ⟨ k, hk ⟩ <;> simp +decide [ *, Function.update_apply ] ;
        exact MvPolynomial.IsHomogeneous.add ( hhom _ ) hv₁;
      · intro i; by_cases hi : i = ⟨ k, hk ⟩ <;> simp +decide [ *, Function.update_apply ] ;
      · intro i hi p hp hp';
        by_cases hi' : i = ⟨ k, hk ⟩ <;> simp_all +decide [ Function.update_apply ];
        · subst i
          have hprefix :
              (Function.update g ⟨ k, hk ⟩ (f ⟨ k, hk ⟩ + v)) ''
                  {j : Fin C | j < ⟨ k, hk ⟩} =
                g '' {j : Fin C | j < ⟨ k, hk ⟩} := by
            ext x
            exact ⟨ fun ⟨ y, hy, hyx ⟩ => ⟨ y, hy, by rw [ Function.update_of_ne ( ne_of_lt hy ) ] at hyx; exact hyx ⟩,
              fun ⟨ y, hy, hyx ⟩ => ⟨ y, hy, by rw [ Function.update_of_ne ( ne_of_lt hy ) ]; exact hyx ⟩ ⟩
          have hp_old : p ∈ associatedPrimes (MvPolynomial (Fin n) K)
              ((MvPolynomial (Fin n) K) ⧸
                ((Ideal.span (g '' {j : Fin C | j < ⟨ k, hk ⟩})) • ⊤ :
                  Submodule (MvPolynomial (Fin n) K) (MvPolynomial (Fin n) K))) := by
            rw [hprefix] at hp
            exact hp
          exact hv₃ p hp_old hp'.choose hp'.choose_spec.1 hp'.choose_spec.2
        · convert hg₄ i ( lt_of_le_of_ne hi ( by simpa [ Fin.ext_iff ] using hi' ) ) p _ _ _ _ using 1;
          any_goals exact hp'.choose_spec.2;
          · convert hp using 1;
            rw [ show ( Function.update g ⟨ k, hk ⟩ ( f ⟨ k, hk ⟩ + v ) ) '' { j : Fin C | j < i } = g '' { j : Fin C | j < i } from ?_ ];
            ext; simp [Function.update];
            exact ⟨ fun ⟨ x, hx₁, hx₂ ⟩ => ⟨ x, hx₁, by rw [ if_neg ( by exact ne_of_lt ( lt_of_lt_of_le hx₁ ( Nat.le_of_lt_succ ( by linarith [ Fin.is_lt i ] ) ) ) ) ] at hx₂; exact hx₂ ⟩, fun ⟨ x, hx₁, hx₂ ⟩ => ⟨ x, hx₁, by rw [ if_neg ( by exact ne_of_lt ( lt_of_lt_of_le hx₁ ( Nat.le_of_lt_succ ( by linarith [ Fin.is_lt i ] ) ) ) ) ] ; exact hx₂ ⟩ ⟩;
          · exact hp'.choose_spec.1;
    · obtain ⟨ g, hg₁, hg₂, hg₃, hg₄ ⟩ := ih; use g; simp_all +decide [ Nat.lt_succ_iff ] ;
      grind

/-- Core of W3 for a family already sorted into non-increasing degree order. -/
theorem exists_regCond_sorted [Infinite K] {C : ℕ}
    (f : Fin C → MvPolynomial (Fin n) K) (deg : Fin C → ℕ)
    (hpos : ∀ i, 1 ≤ deg i)
    (hhom : ∀ i, f i ∈ homogeneousSubmodule (Fin n) K (deg i))
    (hanti : ∀ i j : Fin C, i ≤ j → deg j ≤ deg i) :
    ∃ g : Fin C → MvPolynomial (Fin n) K,
      Ideal.span (Set.range g) = Ideal.span (Set.range f) ∧
      (∀ i, g i ∈ homogeneousSubmodule (Fin n) K (deg i)) ∧ RegCond g := by
  obtain ⟨g, hagree, hhomg, htri, hreg⟩ := exists_regCond_sorted_aux f deg hpos hhom hanti C
  refine ⟨g, span_range_eq_of_triangular f g htri, hhomg, ?_⟩
  intro i p hp hgi j hij
  have hall : ∀ m : Fin C, i ≤ m → f m ∈ p := by
    intro m hm
    by_contra hfm
    exact hreg i i.is_lt p hp ⟨m, hm, hfm⟩ hgi
  have hgjfj : g j - f j ∈ p :=
    (Ideal.span_le.mpr (Set.image_subset_iff.mpr
      (fun l hl => hall l (le_trans hij.le (le_of_lt hl))))) (htri j)
  have hfj : f j ∈ p := hall j hij.le
  simpa using p.add_mem hgjfj hfj

/-
W3: generic triangular recombination achieving the regularity condition.
-/
theorem exists_regCond [Infinite K] {C : ℕ}
    (f : Fin C → MvPolynomial (Fin n) K) (d : ℕ)
    (hfh : ∀ i, ∃ e : ℕ, 1 ≤ e ∧ e ≤ d ∧ f i ∈ homogeneousSubmodule (Fin n) K e) :
    ∃ g : Fin C → MvPolynomial (Fin n) K,
      Ideal.span (Set.range g) = Ideal.span (Set.range f) ∧
      (∀ i, g i = 0 ∨ ∃ e : ℕ, 1 ≤ e ∧ e ≤ d ∧ g i ∈ homogeneousSubmodule (Fin n) K e) ∧
      RegCond g := by
  choose deg hdeg1 hdegd hdeg using hfh;
  -- Let `key : Fin C → ℕ := fun i => d - deg i` and `σ := Tuple.sort key : Equiv.Perm (Fin C)`.
  set key : Fin C → ℕ := fun i => d - deg i
  obtain ⟨σ, hσ⟩ : ∃ σ : Equiv.Perm (Fin C), Monotone (key ∘ σ) := by
    exact ⟨ Tuple.sort key, Tuple.monotone_sort key ⟩;
  obtain ⟨g, hg⟩ := exists_regCond_sorted (fun i => f (σ i)) (fun i => deg (σ i)) (fun i => hdeg1 (σ i)) (fun i => hdeg (σ i)) (fun i j hij => by
    exact Nat.le_of_not_lt fun h => not_lt_of_ge ( hσ hij ) ( Nat.sub_lt_sub_left ( by linarith [ hdegd ( σ i ), hdegd ( σ j ) ] ) h ));
  refine' ⟨ g, _, _, hg.2.2 ⟩;
  · rw [ hg.1, show Set.range ( fun i => f ( σ i ) ) = Set.range f from ?_ ];
    exact Set.ext fun x => ⟨ fun ⟨ i, hi ⟩ => ⟨ σ i, hi ⟩, fun ⟨ i, hi ⟩ => ⟨ σ.symm i, by simpa using hi ⟩ ⟩;
  · exact fun i => Or.inr ⟨ deg ( σ i ), hdeg1 _, hdegd _, hg.2.1 i ⟩

/-
The degree of the whole polynomial ring (`degQ ⊥`) is at most `1`
(it equals `1` for `n ≥ 1`, and `0` for `n = 0`).
-/
theorem degQ_bot_le_one [Infinite K] :
    degQ (⊥ : Ideal (MvPolynomial (Fin n) K)) ≤ 1 := by
  unfold degQ;
  rw [ hilbPoly_eq_of_eventually ];
  swap;
  exact if n = 0 then 0 else Polynomial.C 1 * ∏ i ∈ Finset.range ( n - 1 ), ( Polynomial.X + Polynomial.C ( i + 1 : ℚ ) ) * Polynomial.C ( 1 / ( i + 1 : ℚ ) );
  · split_ifs <;> simp_all +decide [ Polynomial.natDegree_prod', Polynomial.leadingCoeff_prod ];
    rw [ Polynomial.natDegree_prod ];
    · norm_cast;
      erw [ Finset.prod_congr rfl fun _ _ => by erw [ Polynomial.leadingCoeff_X_add_C ] ] ; norm_num;
      rw [ ← div_eq_mul_inv, div_le_iff₀ ] <;> norm_cast <;> norm_num;
      · refine' Nat.factorial_le _;
        refine' le_trans ( Finset.sum_le_sum fun _ _ => Polynomial.natDegree_mul_le .. ) _ ; norm_num;
        norm_cast;
        erw [ Finset.sum_congr rfl fun _ _ => Polynomial.natDegree_X_add_C _ ] ; norm_num;
      · positivity;
    · exact fun i hi => mul_ne_zero ( by exact ne_of_apply_ne Polynomial.derivative <| by norm_num ) <| Polynomial.C_ne_zero.mpr <| by positivity;
  · rcases n with ( _ | n ) <;> simp +decide [ Finset.prod_range_succ', Nat.cast_add_one_ne_zero ];
    · use 1;
      intro b hb
      have h_trivial : ∀ (p : MvPolynomial (Fin 0) K), p.IsHomogeneous b → p = 0 := by
        intro p hp
        have h_trivial : ∀ (m : Fin 0 →₀ ℕ), m = 0 := by
          exact fun m => Subsingleton.elim _ _;
        ext m; simp [h_trivial];
        rw [ hp.coeff_eq_zero ] ; aesop;
      refine' Module.finrank_eq_zero_iff.mpr _;
      rintro ⟨ x, hx ⟩;
      obtain ⟨ p, hp, rfl ⟩ := hx;
      exact ⟨ 1, one_ne_zero, by simp +decide [ h_trivial p hp ] ⟩;
    · -- We need to show that the Hilbert function of the whole ring is equal to the polynomial given.
      have h_hilb : ∀ e : ℕ, (HF (⊥ : Ideal (MvPolynomial (Fin (n + 1)) K)) e : ℚ) = Nat.multichoose (n + 1) e := by
        intro e;
        rw [ show HF ⊥ e = Module.finrank K ( homogeneousSubmodule ( Fin ( n + 1 ) ) K e ) from ?_ ];
        · have h_basis : Module.finrank K (homogeneousSubmodule (Fin (n + 1)) K e) = Fintype.card {s : Fin (n + 1) →₀ ℕ // Finsupp.degree s = e} := by
            rw [ MvPolynomial.homogeneousSubmodule_eq_finsupp_supported ];
            convert Module.finrank_eq_card_basis ( MvPolynomial.basisRestrictSupport K { d : Fin ( n + 1 ) →₀ ℕ | Finsupp.degree d = e } ) using 1;
          convert congr_arg ( ( ↑ ) : ℕ → ℚ ) h_basis using 1;
          convert congr_arg ( ( ↑ ) : ℕ → ℚ ) ( Fintype.card_congr ( Sym.equivNatSum ( Fin ( n + 1 ) ) e ) ) using 1;
          simp +decide [ Sym.card_sym_eq_multichoose ];
        · fapply LinearEquiv.finrank_eq;
          symm;
          refine' ( LinearEquiv.ofBijective _ ⟨ _, _ ⟩ );
          refine' { toFun := fun x => ⟨ _, ⟨ x, x.2, rfl ⟩ ⟩, map_add' := _, map_smul' := _ };
          all_goals simp +decide [ Function.Injective, Function.Surjective ];
          simp +decide [ Ideal.Quotient.eq ];
          exact fun a ha b hb h => sub_eq_zero.mp h;
      use 0; intro e he; simp +decide [ h_hilb, Polynomial.eval_prod ] ;
      have h_multichoose : Nat.multichoose (n + 1) e = Nat.choose (e + n) n := by
        rw [ Nat.add_comm, Nat.multichoose_eq ];
        rw [ add_assoc, add_tsub_cancel_left, add_comm, Nat.choose_symm_add ];
      rw [ h_multichoose, Nat.cast_choose ];
      · field_simp;
        rw [ Finset.prod_div_distrib, mul_div, eq_div_iff ] <;> norm_cast <;> first | positivity | induction' n with n ih <;> simp_all +decide [ Nat.factorial, Finset.prod_range_succ ] ; ring;
        rw [ show ( e + n ).factorial = e.factorial * ∏ x ∈ Finset.range n, ( 1 + e + x ) from ?_ ] ; ring;
        exact Nat.recOn n ( by norm_num ) fun n ih => by rw [ Nat.add_succ, Nat.factorial_succ, Finset.prod_range_succ ] ; nlinarith;
      · grind

/-
Base case of the recurrence: the divided degree of the whole ring is `≤ 1`
(the unique minimal prime `⊥` contributes `degQ ⊥ ≤ 1` at height `0`).
-/
theorem divdegQ_bot_le_one [Infinite K] (d : ℕ) :
    divdegQ (⊥ : Ideal (MvPolynomial (Fin n) K)) d ≤ 1 := by
  unfold divdegQ;
  rw [ Finset.sum_eq_single ⊥ ] <;> simp +decide [ isoComp' ];
  · convert degQ_bot_le_one;
    · simp +decide [ isoComp ];
      exact Ideal.isPrime_bot;
    · infer_instance;
  · simp +decide [ Ideal.minimalPrimes ];
    intro b hb hb_ne_bot
    have h_bot_prime : (⊥ : Ideal (MvPolynomial (Fin n) K)).IsPrime := by
      exact Ideal.isPrime_bot;
    have := hb.2 h_bot_prime ; aesop;
  · simp +decide [ Ideal.minimalPrimes ];
    simp +decide [ Minimal, Ideal.isPrime_iff ]

/-
S1a: quotients by homogeneous proper ideals with equal radical have equal
Hilbert-polynomial degree (their quotient rings have equal Krull dimension).
-/
theorem hilbPoly_natDegree_eq_of_radical_eq [Infinite K]
    {A B : Ideal (MvPolynomial (Fin n) K)}
    (hA : IsHomog A) (hB : IsHomog B) (hAne : A ≠ ⊤) (hBne : B ≠ ⊤)
    (hrad : A.radical = B.radical) :
    (hilbPoly A).natDegree = (hilbPoly B).natDegree := by
  -- Since A.radical = B.radical, the prime spectra zero loci coincide: PrimeSpectrum.zeroLocus (A : Set R) = PrimeSpectrum.zeroLocus (B : Set R).
  have h_zeroLocus : PrimeSpectrum.zeroLocus (A : Set (MvPolynomial (Fin n) K)) = PrimeSpectrum.zeroLocus (B : Set (MvPolynomial (Fin n) K)) := by
    grind +suggestions;
  -- Hence ringKrullDim (R ⧸ A) = ringKrullDim (R ⧸ B) by rewriting with ringKrullDim_quotient on both sides.
  have h_ringKrullDim : ringKrullDim (MvPolynomial (Fin n) K ⧸ A) = ringKrullDim (MvPolynomial (Fin n) K ⧸ B) := by
    rw [ringKrullDim_quotient, ringKrullDim_quotient];
    rw [h_zeroLocus];
  by_cases hA0 : hilbPoly A = 0 <;> by_cases hB0 : hilbPoly B = 0 <;> simp_all +decide [ HF_poly_natDegree ];
  · have := HF_poly_natDegree A hA hAne ( hilbPoly A ) ( hilbPoly_spec A hA ) ; have := HF_poly_natDegree B hB hBne ( hilbPoly B ) ( hilbPoly_spec B hB ) ; simp_all +decide ;
    have h_finiteDimensional : ringKrullDim (MvPolynomial (Fin n) K ⧸ B) = 0 := by
      rw [ ← h_ringKrullDim, ringKrullDim_eq_zero_of_finiteDim A hAne ];
    exact absurd ( this.2 this.1 ) ( by rw [ h_finiteDimensional ] ; exact ne_of_gt ( by exact_mod_cast Nat.succ_pos _ ) );
  · have := HF_poly_natDegree B hB hBne ( hilbPoly B ) ( hilbPoly_spec B hB ) ; simp_all +decide ;
    have := ringKrullDim_eq_zero_of_finiteDim B hBne; simp_all +decide ;
    have := HF_poly_natDegree A hA hAne ( hilbPoly A ) ( hilbPoly_spec A hA ) ; simp_all +decide ;
    norm_cast at this;
    tauto;
  · have := HF_poly_natDegree A hA hAne ( hilbPoly A ) ( hilbPoly_spec A hA ) ; have := HF_poly_natDegree B hB hBne ( hilbPoly B ) ( hilbPoly_spec B hB ) ; simp_all +decide [ WithBot.coe_eq_coe ] ;
    rename_i h; have := h.2 h.1; simp_all +decide [ WithBot.coe_eq_coe ] ;
    rw [ ← ‹¬hilbPoly B = 0 ∧ ( ¬hilbPoly B = 0 → ↑ ( hilbPoly B |> Polynomial.natDegree ) + 1 = ringKrullDim ( MvPolynomial ( Fin n ) K ⧸ B ) ) ›.2 ‹¬hilbPoly B = 0 ∧ ( ¬hilbPoly B = 0 → ↑ ( hilbPoly B |> Polynomial.natDegree ) + 1 = ringKrullDim ( MvPolynomial ( Fin n ) K ⧸ B ) ) ›.1 ] at this ; norm_cast at this;
    exact Nat.succ_injective this

/-
S1: frozen components. A prime `p` minimal over both `I` and the larger `J`
contributes no more to the divided degree of `J` than to that of `I`.
-/
theorem divdegQ_frozen_term_le [Infinite K]
    {I J p : Ideal (MvPolynomial (Fin n) K)}
    (hI : IsHomog I) (hJ : IsHomog J) (hIJ : I ≤ J)
    (hpI : p ∈ I.minimalPrimes) (hpJ : p ∈ J.minimalPrimes) (d : ℕ) :
    degQ (isoComp' J p) / (d : ℚ) ^ p.height.toNat ≤
      degQ (isoComp' I p) / (d : ℚ) ^ p.height.toNat := by
  gcongr;
  convert degQ_le_of_le _ _ _ _;
  · infer_instance;
  · convert isoComp_isHomog I p hI hpI;
    exact dif_pos ( by exact hpI.1.1 );
  · convert isoComp_isHomog J p hJ hpJ;
    exact dif_pos ( hpJ.1.1 );
  · unfold isoComp';
    split_ifs <;> simp_all +decide [ isoComp_mono ];
  · have h_radical_eq : (isoComp' I p).radical = p ∧ (isoComp' J p).radical = p := by
      constructor;
      · convert radical_isoComp I p hpI;
        exact dif_pos ( hpI.1.1 );
      · convert radical_isoComp J p hpJ;
        exact dif_pos ( hpJ.1.1 );
    apply hilbPoly_natDegree_eq_of_radical_eq;
    · convert isoComp_isHomog J p hJ hpJ;
      exact dif_pos ( by exact hpJ.1.1 );
    · convert isoComp_isHomog I p hI hpI;
      exact dif_pos ( by exact hpI.1.1 );
    · intro h; simp_all +decide [ Ideal.radical ] ;
      exact hpJ.1.1.ne_top ( by ext; simp +decide [ ← h_radical_eq.2 ] );
    · intro h; simp_all +decide [ Ideal.radical_top ] ;
      exact hpI.1.1.ne_top ( h_radical_eq.1.symm );
    · rw [ h_radical_eq.1, h_radical_eq.2 ]

/-- The span of the image of a homogeneous family is homogeneous. -/
theorem isHomog_span_image {C : ℕ} (f : Fin C → MvPolynomial (Fin n) K)
    (S : Set (Fin C))
    (hf : ∀ i, ∃ e : ℕ, f i ∈ homogeneousSubmodule (Fin n) K e) :
    IsHomog (Ideal.span (f '' S)) := by
  convert IsHomog_of_isHomogeneous _
  convert Ideal.homogeneous_span (homogeneousSubmodule (Fin n) K) (f '' S) ?_
  rintro _ ⟨i, hi, rfl⟩
  exact ⟨_, (hf i).choose_spec⟩

/-- Minimal primes depend only on the radical. -/
theorem minimalPrimes_eq_of_radical_eq {R : Type*} [CommRing R] {I J : Ideal R}
    (h : I.radical = J.radical) : I.minimalPrimes = J.minimalPrimes := by
  rw [← Ideal.radical_minimalPrimes, h, Ideal.radical_minimalPrimes]

/-
A minimal prime of `I` that still contains a larger ideal `J` (with `I ≤ J`)
is a minimal prime of `J` (the *frozen* direction).
-/
theorem mem_minimalPrimes_of_le {R : Type*} [CommRing R] {I J q : Ideal R}
    (hIJ : I ≤ J) (hq : q ∈ I.minimalPrimes) (hJq : J ≤ q) : q ∈ J.minimalPrimes := by
  refine' ⟨ ⟨ hq.1.1, hJq ⟩, _ ⟩;
  exact fun y hy hyq => hq.2 ⟨ hy.1, hIJ.trans hy.2 ⟩ hyq

/-- Classification (S2): a minimal prime `q` of `I` stays minimal after adjoining
`fr` iff it already contains `fr`. -/
theorem mem_minimalPrimes_sup_span_singleton_iff {R : Type*} [CommRing R]
    {I q : Ideal R} {fr : R} (hq : q ∈ I.minimalPrimes) :
    q ∈ (I ⊔ Ideal.span {fr}).minimalPrimes ↔ fr ∈ q := by
  constructor
  · intro hqmp
    have : I ⊔ Ideal.span {fr} ≤ q := hqmp.1.2
    exact (Ideal.span_le.mp (le_trans le_sup_right this)) (Set.mem_singleton _)
  · intro hfrq
    refine mem_minimalPrimes_of_le le_sup_left hq (sup_le hq.1.2 ?_)
    rw [Ideal.span_le, Set.singleton_subset_iff]; exact hfrq

open scoped Classical

/-- Local extraction of the `I0`-component at a prime `m`.

If every associated prime of `R ⧸ I0` lying below `m` is minimal over `I0`,
then the intersection of the isolated components over those minimal primes has
the same localization at `m` as `I0`, in the contraction direction used by the
charge argument. -/
theorem localized_component_extraction
    {I0 m : Ideal (MvPolynomial (Fin n) K)} [m.IsPrime]
    (hAss : ∀ P ∈ associatedPrimes (MvPolynomial (Fin n) K)
        ((MvPolynomial (Fin n) K) ⧸ I0), P ≤ m → P ∈ I0.minimalPrimes)
    {x : MvPolynomial (Fin n) K}
    (hx : ∃ s, s ∉ m ∧
      s * x ∈ (⨅ p : {p : Ideal (MvPolynomial (Fin n) K) //
          p ∈ I0.minimalPrimes ∧ p ≤ m}, isoComp' I0 p.1)) :
    ∃ t, t ∉ m ∧ t * x ∈ I0 := by
  classical
  let R := MvPolynomial (Fin n) K
  let N : Ideal R := I0.colon ({x} : Set R)
  by_cases hNm : N ≤ m
  · obtain ⟨P, hPminN, hPm⟩ := Ideal.exists_minimalPrimes_le (I := N) (J := m) hNm
    have hPassN : P ∈ associatedPrimes R (R ⧸ N) := by
      have hsubset :=
        Module.associatedPrimes.minimalPrimes_annihilator_subset_associatedPrimes
          R (R ⧸ N)
      exact hsubset (by simpa [Ideal.annihilator_quotient] using hPminN)
    let φ : R →ₗ[R] R ⧸ I0 :=
      { toFun := fun t => Ideal.Quotient.mk I0 (t * x)
        map_add' := by
          intro a b
          simp [add_mul]
        map_smul' := by
          intro a b
          change Ideal.Quotient.mk I0 ((a * b) * x) =
            (Ideal.Quotient.mk I0 a) * Ideal.Quotient.mk I0 (b * x)
          rw [← map_mul, mul_assoc] }
    have hker : N = LinearMap.ker φ := by
      ext t
      change t ∈ I0.colon ({x} : Set R) ↔ Ideal.Quotient.mk I0 (t * x) = 0
      rw [Submodule.mem_colon_singleton, Ideal.Quotient.eq_zero_iff_mem]
      simp [smul_eq_mul]
    let ψ : R ⧸ N →ₗ[R] R ⧸ I0 := N.liftQ φ (le_of_eq hker)
    have hψinj : Function.Injective ψ := by
      exact LinearMap.ker_eq_bot.mp
        (Submodule.ker_liftQ_eq_bot' (p := (N : Submodule R R)) φ hker)
    have hPassI0 : P ∈ associatedPrimes R (R ⧸ I0) :=
      associatedPrimes.subset_of_injective (f := ψ) hψinj hPassN
    have hPminI0 : P ∈ I0.minimalPrimes := hAss P hPassI0 hPm
    have hPprime : P.IsPrime := Ideal.minimalPrimes_isPrime hPminI0
    haveI : P.IsPrime := hPprime
    obtain ⟨s, hsnotm, hsx⟩ := hx
    let pS : {p : Ideal R // p ∈ I0.minimalPrimes ∧ p ≤ m} :=
      ⟨P, hPminI0, hPm⟩
    have hsxIso' : s * x ∈ isoComp' I0 P := by
      have := (Ideal.mem_iInf.mp hsx) pS
      simpa [pS] using this
    have hsxIso : s * x ∈ isoComp I0 P := by
      unfold isoComp' at hsxIso'
      rw [dif_pos hPprime] at hsxIso'
      exact hsxIso'
    obtain ⟨u, hunotP, husxI0⟩ := (mem_isoComp_iff I0 P (s * x)).mp hsxIso
    have hsnotP : s ∉ P := fun hsP => hsnotm (hPm hsP)
    have husN : u * s ∈ N := by
      change u * s ∈ I0.colon ({x} : Set R)
      rw [Submodule.mem_colon_singleton]
      simpa [smul_eq_mul, mul_assoc, mul_left_comm, mul_comm] using husxI0
    have husP : u * s ∈ P := hPminN.1.2 husN
    have hup_or_hsp := (show P.IsPrime from inferInstance).mem_or_mem husP
    exact False.elim (hup_or_hsp.elim hunotP hsnotP)
  · rw [SetLike.le_def] at hNm
    push_neg at hNm
    obtain ⟨t, htN, htm⟩ := hNm
    refine ⟨t, htm, ?_⟩
    change t ∈ I0.colon ({x} : Set R) at htN
    simpa [smul_eq_mul] using (Submodule.mem_colon_singleton.mp htN)

/-- Local identity at a prime `m` (the S3 localization bridge): the
`I0`-component at `m` agrees with the component of the intersection of the
isolated components of `I0` over the minimal primes below `m`, *provided* the
associated-prime control `hAss` holds at `m` (every associated prime of `R ⧸ I0`
below `m` is a minimal prime of `I0`).

This is the direct composition of the associated-prime control (HALF A, supplied
here as the hypothesis `hAss`) with `localized_component_extraction`.  It is the
fully-formalized bridge that reduces the S3 step of the charge to establishing
`hAss` at each new minimal prime. -/
theorem isoComp_eq_iInf_components_of_ass_control {C : ℕ}
    (f : Fin C → MvPolynomial (Fin n) K) (r : ℕ)
    {m : Ideal (MvPolynomial (Fin n) K)} [m.IsPrime]
    (hAss : ∀ P ∈ associatedPrimes (MvPolynomial (Fin n) K)
        (MvPolynomial (Fin n) K ⧸ Ideal.span (f '' {i : Fin C | i.val < r})),
        P ≤ m → P ∈ (Ideal.span (f '' {i : Fin C | i.val < r})).minimalPrimes) :
    isoComp (Ideal.span (f '' {i : Fin C | i.val < r})) m =
      isoComp (⨅ q : {q : Ideal (MvPolynomial (Fin n) K) //
          q ∈ (Ideal.span (f '' {i : Fin C | i.val < r})).minimalPrimes ∧ q ≤ m},
        isoComp' (Ideal.span (f '' {i : Fin C | i.val < r})) q.1) m := by
  refine' le_antisymm _ _;
  · refine' isoComp_mono _;
    simp +decide [ isoComp' ];
    intro a ha hq; split_ifs <;> simp_all +decide [ Ideal.minimalPrimes ] ;
    exact le_isoComp _ _;
  · intro x hx;
    obtain ⟨ s, hs ⟩ := mem_isoComp_iff _ _ _ |>.1 hx;
    convert localized_component_extraction _ _;
    convert mem_isoComp_iff _ _ _;
    · infer_instance;
    · exact hAss;
    · exact ⟨ s, hs ⟩

/-! ## HALF A: associated-prime control at a minimal prime of `I_r`. -/

/-- (F2) A prime squeezed between `I` and a minimal prime `m` of `I` equals `m`. -/
theorem eq_of_le_minimalPrime {R : Type*} [CommRing R] {I m p : Ideal R}
    (hm : m ∈ I.minimalPrimes) (hp : p.IsPrime) (h1 : I ≤ p) (h2 : p ≤ m) : p = m :=
  le_antisymm h2 (hm.2 ⟨hp, h1⟩ h2)

/-
An associated prime of `R ⧸ (I • ⊤)` contains `I`.
-/
theorem ideal_le_of_mem_ass_smul_top {R : Type*} [CommRing R] [IsNoetherianRing R]
    {I P : Ideal R} (hP : P ∈ associatedPrimes R (R ⧸ (I • ⊤ : Submodule R R))) :
    I ≤ P := by
  obtain ⟨ x, hx ⟩ := hP;
  obtain ⟨ y, rfl ⟩ := hx;
  obtain ⟨ z, rfl ⟩ := Submodule.mkQ_surjective _ y;
  intro y hy; simp_all +decide [ Submodule.Quotient.mk_eq_zero, Submodule.smul_mem_smul ] ;
  erw [ Ideal.Quotient.eq_zero_iff_mem ];
  exact Ideal.mul_mem_mul hy ( Submodule.mem_top : z ∈ ⊤ )

/-
**Localization bridge for the associated maximal ideal.** If `P` is an
associated prime of `R ⧸ (I • ⊤)`, then the maximal ideal of `R_P` is an
associated prime of `R_P ⧸ ((map I)_P • ⊤)`.
-/
theorem maximalIdeal_mem_ass_localized_quot {R : Type*} [CommRing R] [IsNoetherianRing R]
    {P : Ideal R} [P.IsPrime] {I : Ideal R}
    (hP : P ∈ associatedPrimes R (R ⧸ (I • ⊤ : Submodule R R))) :
    IsLocalRing.maximalIdeal (Localization.AtPrime P) ∈
      associatedPrimes (Localization.AtPrime P)
        (Localization.AtPrime P ⧸
          (Ideal.map (algebraMap R (Localization.AtPrime P)) I • ⊤ :
            Submodule (Localization.AtPrime P) (Localization.AtPrime P))) := by
  -- Let $R' = \text{Localization.AtPrime } P$, $S = P.primeCompl$, $M = R ⧸ (I • ⊤)$, and $M' = R' ⧸ I' • ⊤$ where $I' = \text{Ideal.map } R'$.
  set R' := Localization.AtPrime P
  set S := P.primeCompl
  set M := R ⧸ (I • ⊤ : Submodule R R)
  set M' := R' ⧸ (Ideal.map (algebraMap R R') I • ⊤ : Submodule R' R');
  have h_localization : (IsLocalRing.maximalIdeal R').comap (algebraMap R R') ∈ associatedPrimes R M := by
    convert hP using 2;
    exact Localization.AtPrime.comap_maximalIdeal;
  have h_localization : (IsLocalRing.maximalIdeal R') ∈ associatedPrimes R' (R' ⧸ (I • ⊤ : Submodule R R).localized' R' S (Algebra.linearMap R R')) := by
    convert Module.associatedPrimes.mem_associatedPrimes_of_comap_mem_associatedPrimes_of_isLocalizedModule S _ _ h_localization using 1;
    exact inferInstance;
    exact ( I • ⊤ : Submodule R R ).toLocalizedQuotient' R' S ( Algebra.linearMap R R' ); all_goals infer_instance;
  convert h_localization using 1;
  rw [ Submodule.localized'_smul, Submodule.localized'_top ];
  rw [ Ideal.localized'_eq_map ]

/-
Iterated Rees grade descent along a weakly regular list `pre`.
-/
theorem grade_descent_list {S : Type*} [CommRing S] [IsNoetherianRing S]
    {M : Type*} [AddCommGroup M] [Module S M] [Module.Finite S M]
    (a : Ideal S) (pre : List S) (hpre_mem : ∀ x ∈ pre, x ∈ a)
    (hpre : IsWeaklyRegular M pre)
    (rs : List S) (hmem : ∀ r ∈ rs, r ∈ a) (hwreg : IsWeaklyRegular M rs) :
    ∃ rs' : List S, rs'.length = rs.length - pre.length ∧ (∀ r ∈ rs', r ∈ a) ∧
      IsWeaklyRegular (M ⧸ (Ideal.ofList pre • ⊤ : Submodule S M)) rs' := by
  revert rs hwreg;
  induction' pre with x pre ih generalizing M;
  · intro rs hmem hwreg;
    refine' ⟨ rs, _, _, _ ⟩ <;> simp_all +decide [ Ideal.ofList ];
    convert LinearEquiv.isWeaklyRegular_congr _ _ |>.2 hwreg;
    convert Submodule.quotEquivOfEqBot _ _;
    simp +decide [ Submodule.smul_def ];
  · intro rs hmem hwreg
    obtain ⟨rs1, h1⟩ : ∃ rs1 : List S, rs1.length = rs.length - 1 ∧ (∀ r ∈ rs1, r ∈ a) ∧ IsWeaklyRegular (QuotSMulTop x M) rs1 := by
      apply grade_descent a (hpre_mem x (by simp)) (by
      rw [ isWeaklyRegular_cons_iff ] at hpre ; tauto) rs hmem hwreg;
    obtain ⟨rs', h2⟩ : ∃ rs' : List S, rs'.length = rs1.length - pre.length ∧ (∀ r ∈ rs', r ∈ a) ∧ IsWeaklyRegular ((QuotSMulTop x M) ⧸ (Ideal.ofList pre • ⊤ : Submodule S (QuotSMulTop x M))) rs' := by
      apply ih (fun y hy => hpre_mem y (List.mem_cons_of_mem _ hy)) (by
      grind +suggestions) rs1 h1.right.left h1.right.right;
    obtain ⟨e, he⟩ : ∃ e : (M ⧸ (Ideal.ofList (x :: pre) • ⊤ : Submodule S M)) ≃ₗ[S] (QuotSMulTop x M) ⧸ (Ideal.ofList pre • ⊤ : Submodule S (QuotSMulTop x M)), True := by
      exact ⟨ Submodule.quotOfListConsSMulTopEquivQuotSMulTopInner M x pre, trivial ⟩;
    refine' ⟨ rs', _, _, _ ⟩;
    · grind;
    · exact h2.2.1;
    · convert e.isWeaklyRegular_congr rs' |>.2 h2.2.2 using 1

/-
**Grade lower bound (height ≤ length).**
-/
set_option maxHeartbeats 1600000 in
theorem height_le_of_localized_weaklyRegular [IsAlgClosed K]
    {P : Ideal (MvPolynomial (Fin n) K)} [P.IsPrime]
    (L : List (MvPolynomial (Fin n) K)) (hL : ∀ x ∈ L, x ∈ P)
    (hreg : IsWeaklyRegular (Localization.AtPrime P)
       (L.map (algebraMap (MvPolynomial (Fin n) K) (Localization.AtPrime P))))
    (hass : IsLocalRing.maximalIdeal (Localization.AtPrime P) ∈
       associatedPrimes (Localization.AtPrime P)
         (Localization.AtPrime P ⧸
           (Ideal.ofList (L.map (algebraMap (MvPolynomial (Fin n) K)
               (Localization.AtPrime P))) • ⊤ :
             Submodule (Localization.AtPrime P) (Localization.AtPrime P)))) :
    P.height ≤ (L.length : ℕ∞) := by
  by_contra h;
  obtain ⟨rs, hrs⟩ := grade_ge_height P (L.length + 1) (by
    have hlt := not_le.mp h
    have : (L.length : ℕ∞) + 1 ≤ P.height := Order.add_one_le_of_lt hlt
    push_cast; exact this);
  obtain ⟨rs', hrs'⟩ : ∃ rs' : List (Localization.AtPrime P), rs'.length = rs.length - L.length ∧ (∀ r ∈ rs', r ∈ IsLocalRing.maximalIdeal (Localization.AtPrime P)) ∧ IsWeaklyRegular ((Localization.AtPrime P) ⧸ (Ideal.ofList (L.map (algebraMap _ (Localization.AtPrime P))) • ⊤ : Submodule (Localization.AtPrime P) (Localization.AtPrime P))) rs' := by
    convert grade_descent_list ( IsLocalRing.maximalIdeal ( Localization.AtPrime P ) ) ( List.map ( algebraMap ( MvPolynomial ( Fin n ) K ) ( Localization.AtPrime P ) ) L ) _ hreg ( List.map ( algebraMap ( MvPolynomial ( Fin n ) K ) ( Localization.AtPrime P ) ) rs ) _ hrs.2.2 using 1;
    · simp +decide [ hrs.1 ];
    · simp +decide [ IsLocalRing.mem_maximalIdeal ];
      intro x hx;
      rw [ isUnit_iff_exists_inv ];
      rintro ⟨ b, hb ⟩;
      obtain ⟨ y, hy ⟩ := IsLocalization.exists_mk'_eq P.primeCompl b;
      obtain ⟨ z, hz ⟩ := hy;
      rw [ ← hz, IsLocalization.mul_mk'_eq_mk'_of_mul ] at hb;
      rw [ IsLocalization.mk'_eq_iff_eq_mul ] at hb;
      rw [ one_mul, IsLocalization.eq_iff_exists P.primeCompl ] at hb;
      obtain ⟨ c, hc ⟩ := hb;
      have h_contra : x * y = z := by
        exact mul_left_cancel₀ ( show ( c : MvPolynomial ( Fin n ) K ) ≠ 0 from fun h => c.2 <| h.symm ▸ P.zero_mem ) <| by linear_combination' hc;
      exact z.2 ( h_contra ▸ P.mul_mem_right _ ( hL x hx ) );
    · simp +decide [ IsLocalRing.mem_maximalIdeal ];
      intro x hx;
      rw [ isUnit_iff_exists_inv ];
      rintro ⟨ b, hb ⟩;
      rcases IsLocalization.mk'_surjective P.primeCompl b with ⟨ y, s, rfl ⟩;
      rw [ ← IsLocalization.mk'_one ( M := P.primeCompl ) ] at hb;
      rw [ ← IsLocalization.mk'_mul, IsLocalization.mk'_eq_iff_eq_mul ] at hb;
      rw [ one_mul, IsLocalization.eq_iff_exists P.primeCompl ] at hb;
      obtain ⟨ c, hc ⟩ := hb;
      simp_all +decide [ mul_assoc, mul_comm, mul_left_comm ];
      have h_contra : x * y.1 = y.2 := by
        exact mul_left_cancel₀ ( show ( c : MvPolynomial ( Fin n ) K ) ≠ 0 from by aesop ) ( by linear_combination' hc );
      exact y.2.2 ( h_contra ▸ P.mul_mem_right _ ( hrs.2.1 _ hx ) );
  obtain ⟨w, hw⟩ : ∃ w : Localization.AtPrime P, w ∈ IsLocalRing.maximalIdeal (Localization.AtPrime P) ∧ IsSMulRegular ((Localization.AtPrime P) ⧸ (Ideal.ofList (L.map (algebraMap _ (Localization.AtPrime P))) • ⊤ : Submodule (Localization.AtPrime P) (Localization.AtPrime P))) w := by
    rcases rs' with ( _ | ⟨ w, _ | ⟨ w', rs' ⟩ ⟩ ) <;> simp_all +decide;
    exact ⟨ w, hrs'.1, hrs'.2 ⟩;
  have := GradeDescent.not_subset_associatedPrime_of_isSMulRegular_mem ( show w ∈ IsLocalRing.maximalIdeal ( Localization.AtPrime P ) from hw.1 ) hw.2 hass;
  exact this ( Set.Subset.refl _ )

/-
In a Noetherian local ring, if `R' ⧸ J` has Krull dimension `0`, the maximal
ideal is a minimal prime of `J`.
-/
theorem maximalIdeal_mem_minimalPrimes_of_ringKrullDim_zero {R' : Type*} [CommRing R']
    [IsNoetherianRing R'] [IsLocalRing R'] {J : Ideal R'}
    (hJ : J ≠ ⊤) (hdim : ringKrullDim (R' ⧸ J) = 0) :
    IsLocalRing.maximalIdeal R' ∈ J.minimalPrimes := by
  have h_maximal : ∀ q : Ideal R', q.IsPrime → J ≤ q → q = IsLocalRing.maximalIdeal R' := by
    intro q hq hqJ
    have hq_max : Ideal.IsMaximal (Ideal.map (Ideal.Quotient.mk J) q) := by
      have hq_max : ∀ p : Ideal (R' ⧸ J), p.IsPrime → p.IsMaximal := by
        convert Ring.krullDimLE_zero_iff.mp _;
        grind +suggestions;
      exact hq_max _ ( Ideal.map_isPrime_of_surjective ( Ideal.Quotient.mk_surjective ) ( by aesop ) );
    have hq_eq : Ideal.map (Ideal.Quotient.mk J) q = Ideal.map (Ideal.Quotient.mk J) (IsLocalRing.maximalIdeal R') := by
      have hq_eq : Ideal.IsMaximal (Ideal.map (Ideal.Quotient.mk J) (IsLocalRing.maximalIdeal R')) := by
        have hq_max : ∀ q : Ideal (R' ⧸ J), q.IsPrime → q.IsMaximal := by
          convert Ring.krullDimLE_zero_iff.mp _;
          convert Ring.krullDimLE_iff.mpr _;
          exact hdim.le;
        apply hq_max;
        apply Ideal.map_isPrime_of_surjective;
        · exact Ideal.Quotient.mk_surjective;
        · simp +decide [ IsLocalRing.maximalIdeal ];
          exact fun x hx => fun hx' => hJ <| J.eq_top_of_isUnit_mem hx hx';
      convert hq_max.eq_of_le hq_eq.ne_top _;
      exact Ideal.map_mono ( IsLocalRing.le_maximalIdeal hq.ne_top );
    rw [ Ideal.map_eq_iff_sup_ker_eq_of_surjective ] at hq_eq <;> norm_num at *;
    · rw [ sup_eq_left.mpr hqJ ] at hq_eq;
      rw [ hq_eq, sup_eq_left.mpr ( IsLocalRing.le_maximalIdeal hJ ) ];
    · exact Ideal.Quotient.mk_surjective;
  refine' ⟨ _, fun q hq => _ ⟩;
  · contrapose! h_maximal;
    exact False.elim ( h_maximal ⟨ Ideal.IsMaximal.isPrime ( IsLocalRing.maximalIdeal.isMaximal _ ), IsLocalRing.le_maximalIdeal hJ ⟩ );
  · exact fun h => h_maximal q hq.1 hq.2 ▸ le_rfl

/-
**Minimality from a localized regular prefix.**
-/
theorem minimalPrimes_of_localized_weaklyRegular [IsAlgClosed K]
    {P : Ideal (MvPolynomial (Fin n) K)} [P.IsPrime]
    (L : List (MvPolynomial (Fin n) K)) (hL : ∀ x ∈ L, x ∈ P)
    (hreg : IsWeaklyRegular (Localization.AtPrime P)
       (L.map (algebraMap (MvPolynomial (Fin n) K) (Localization.AtPrime P))))
    (hass : IsLocalRing.maximalIdeal (Localization.AtPrime P) ∈
       associatedPrimes (Localization.AtPrime P)
         (Localization.AtPrime P ⧸
           (Ideal.ofList (L.map (algebraMap (MvPolynomial (Fin n) K)
               (Localization.AtPrime P))) • ⊤ :
             Submodule (Localization.AtPrime P) (Localization.AtPrime P)))) :
    P ∈ (Ideal.ofList L).minimalPrimes := by
  have hJ : Ideal.ofList (List.map (algebraMap (MvPolynomial (Fin n) K) (Localization.AtPrime P)) L) ≠ ⊤ := by
    obtain ⟨ x, hx ⟩ := hass.2;
    intro h_top
    have h_contra : x = 0 := by
      obtain ⟨ y, rfl ⟩ := Ideal.Quotient.mk_surjective x;
      rw [ h_top ] ; simp +decide [ Submodule.mem_colon ];
      exact Ideal.Quotient.eq_zero_iff_mem.mpr ( by simp +decide [ Ideal.mul_top ] );
    simp_all +decide [ SetLike.ext_iff ];
    exact hx 1 isUnit_one;
  have hdim : ringKrullDim (Localization.AtPrime P ⧸ Ideal.ofList (List.map (algebraMap (MvPolynomial (Fin n) K) (Localization.AtPrime P)) L)) = 0 := by
    have hdim : ringKrullDim (Localization.AtPrime P ⧸ Ideal.ofList (List.map (algebraMap (MvPolynomial (Fin n) K) (Localization.AtPrime P)) L)) + L.length = P.height := by
      convert ringKrullDim_add_length_eq_ringKrullDim_of_isRegular _ _;
      · rw [ List.length_map ];
      · convert IsLocalization.AtPrime.ringKrullDim_eq_height P ( Localization.AtPrime P ) |> Eq.symm;
      · infer_instance;
      · infer_instance;
      · constructor;
        · exact hreg;
        · contrapose! hJ;
          simp_all +decide [ Submodule.eq_top_iff' ];
    have hht : P.height ≤ L.length := by
      apply height_le_of_localized_weaklyRegular L hL hreg hass;
    cases h : P.height <;> simp_all +decide [ WithBot.add_eq_coe ];
    obtain ⟨ a', ha', x, hx, h ⟩ := hdim;
    cases a' <;> cases x <;> norm_cast at * ; aesop;
  convert maximalIdeal_mem_minimalPrimes_of_ringKrullDim_zero hJ hdim using 1;
  convert IsLocalization.minimalPrimes_map P.primeCompl ( Localization.AtPrime P ) ( Ideal.ofList L ) using 1;
  constructor <;> intro h <;> simp_all +decide [ Set.ext_iff ];
  · convert IsLocalization.minimalPrimes_map P.primeCompl ( Localization.AtPrime P ) ( Ideal.ofList L ) using 1;
    simp +decide [ Set.ext_iff, Ideal.map_ofList ];
  · rw [ Localization.AtPrime.comap_maximalIdeal ]

/-
**Stagewise regularity ⇒ weak regularity.**
-/
theorem localized_weaklyRegular_of_stages
    {P : Ideal (MvPolynomial (Fin n) K)} [P.IsPrime]
    (L : List (MvPolynomial (Fin n) K))
    (hstage : ∀ (k : ℕ) (hk : k < L.length),
        IsSMulRegular
          (Localization.AtPrime P ⧸
            (Ideal.ofList ((L.take k).map
                (algebraMap (MvPolynomial (Fin n) K) (Localization.AtPrime P))) • ⊤ :
              Submodule (Localization.AtPrime P) (Localization.AtPrime P)))
          (algebraMap (MvPolynomial (Fin n) K) (Localization.AtPrime P) (L.get ⟨k, hk⟩))) :
    IsWeaklyRegular (Localization.AtPrime P)
      (L.map (algebraMap (MvPolynomial (Fin n) K) (Localization.AtPrime P))) := by
  rw [ RingTheory.Sequence.isWeaklyRegular_iff_Fin ];
  intro i;
  convert hstage i ( by simpa using i.2 ) using 1;
  · rw [ List.map_take ];
  · simp +decide [ List.getElem_map ]

/-
Forward direction of the associated-prime localization correspondence for the
ring quotient by a localized ideal.
-/
theorem comap_mem_ass_of_mem_ass_localized_quot {R : Type*} [CommRing R] [IsNoetherianRing R]
    {P : Ideal R} [P.IsPrime] {I : Ideal R} {q : Ideal (Localization.AtPrime P)}
    (hq : q ∈ associatedPrimes (Localization.AtPrime P)
      (Localization.AtPrime P ⧸
        (Ideal.map (algebraMap R (Localization.AtPrime P)) I • ⊤ :
          Submodule (Localization.AtPrime P) (Localization.AtPrime P)))) :
    q.comap (algebraMap R (Localization.AtPrime P)) ∈
      associatedPrimes R (R ⧸ (I • ⊤ : Submodule R R)) := by
  -- Apply `IsLocalRing.CommRing.maximalIdeal_mem_associatedPrimes_of_mem_associatedPrimes_ofLocalized` and simplify.
  convert Module.associatedPrimes.comap_mem_associatedPrimes_of_mem_associatedPrimes_of_isLocalizedModule_of_fg (P.primeCompl) _ q _ _;
  exact Localization.AtPrime P ⧸ ( I • ⊤ : Submodule R R ).localized' ( Localization.AtPrime P ) P.primeCompl ( Algebra.linearMap R ( Localization.AtPrime P ) );
  all_goals try infer_instance;
  exact Submodule.toLocalizedQuotient' _ _ _ _;
  · infer_instance;
  · convert hq using 1;
    rw [ Submodule.localized'_smul, Submodule.localized'_top ];
    rw [ Ideal.localized'_eq_map ];
  · exact ( isNoetherianRing_iff_ideal_fg R ).mp ‹_› _

/-- **Localized stage regularity from avoidance of associated primes.** -/
theorem isSMulRegular_localized_quot_of_stage
    {P : Ideal (MvPolynomial (Fin n) K)} [P.IsPrime]
    (I : Ideal (MvPolynomial (Fin n) K)) (x : MvPolynomial (Fin n) K)
    (hx : ∀ p ∈ associatedPrimes (MvPolynomial (Fin n) K)
        ((MvPolynomial (Fin n) K) ⧸ (I • ⊤ :
          Submodule (MvPolynomial (Fin n) K) (MvPolynomial (Fin n) K))),
        p ≤ P → x ∉ p) :
    IsSMulRegular
      (Localization.AtPrime P ⧸
        (Ideal.map (algebraMap (MvPolynomial (Fin n) K) (Localization.AtPrime P)) I • ⊤ :
          Submodule (Localization.AtPrime P) (Localization.AtPrime P)))
      (algebraMap (MvPolynomial (Fin n) K) (Localization.AtPrime P) x) := by
  have hkey := GradeDescent.isSMulRegular_of_notMem_associatedPrimes
    (R := Localization.AtPrime P)
    (M := Localization.AtPrime P ⧸
      (Ideal.map (algebraMap (MvPolynomial (Fin n) K) (Localization.AtPrime P)) I • ⊤ :
        Submodule (Localization.AtPrime P) (Localization.AtPrime P)))
    (z := algebraMap (MvPolynomial (Fin n) K) (Localization.AtPrime P) x)
    (by
      intro q hq hxq
      refine hx _ (comap_mem_ass_of_mem_ass_localized_quot hq) ?_ (Ideal.mem_comap.mpr hxq)
      have hle := Ideal.comap_mono
        (f := algebraMap (MvPolynomial (Fin n) K) (Localization.AtPrime P))
        (IsLocalRing.le_maximalIdeal hq.1.ne_top)
      rwa [Localization.AtPrime.comap_maximalIdeal] at hle)
  exact hkey

/-
The prefix list `[f 0, …, f (j-1)]` (as an `ℕ`-indexed `dite`) spans `I_j`.
-/
theorem ofList_range_dite_eq_span {C : ℕ} (f : Fin C → MvPolynomial (Fin n) K)
    (j : ℕ) (hjC : j ≤ C) :
    Ideal.ofList ((List.range j).map (fun k => if h : k < C then f ⟨k, h⟩ else 0))
      = Ideal.span (f '' {i : Fin C | i.val < j}) := by
  refine' le_antisymm ( Ideal.span_le.mpr _ ) ( Ideal.span_le.mpr _ );
  · intro x hx;
    simp +zetaDelta at *;
    rcases hx with ⟨ a, ha, rfl ⟩ ; split_ifs <;> simp_all +decide [ Ideal.mem_span ] ;
    exact fun p hp => hp ( show ( ⟨ a, by linarith ⟩ : Fin C ) ∈ { i : Fin C | ( i : ℕ ) < j } from ha );
  · rintro _ ⟨ i, hi, rfl ⟩;
    simp +decide [ Ideal.ofList, List.mem_map, List.mem_range ];
    exact Ideal.subset_span ⟨ i, hi, by aesop ⟩

/-- **HALF A.** For a `RegCond` family, every associated prime `P` of `R ⧸ I_j`
(with `j ≤ r`) lying below a minimal prime `m` of the full-stage ideal `I_r` is a
minimal prime of `I_j`. -/
theorem ass_control_at_minimalPrime [IsAlgClosed K] {C : ℕ}
    (f : Fin C → MvPolynomial (Fin n) K)
    (hreg : RegCond f) (r : ℕ) (hrC : r ≤ C)
    {m : Ideal (MvPolynomial (Fin n) K)}
    (hm : m ∈ (Ideal.span (f '' {i : Fin C | i.val < r})).minimalPrimes)
    {P : Ideal (MvPolynomial (Fin n) K)} (j : ℕ) (hj : j ≤ r)
    (hP : P ∈ associatedPrimes (MvPolynomial (Fin n) K)
      ((MvPolynomial (Fin n) K) ⧸
        ((Ideal.span (f '' {i : Fin C | i.val < j})) • ⊤ :
          Submodule (MvPolynomial (Fin n) K) (MvPolynomial (Fin n) K))))
    (hPm : P ≤ m) :
    P ∈ (Ideal.span (f '' {i : Fin C | i.val < j})).minimalPrimes := by
  suffices H : ∀ (j : ℕ), j ≤ r → ∀ (Q : Ideal (MvPolynomial (Fin n) K)),
      Q ∈ associatedPrimes (MvPolynomial (Fin n) K)
        ((MvPolynomial (Fin n) K) ⧸
          ((Ideal.span (f '' {i : Fin C | i.val < j})) • ⊤ :
            Submodule (MvPolynomial (Fin n) K) (MvPolynomial (Fin n) K))) →
      Q ≤ m → Q ∈ (Ideal.span (f '' {i : Fin C | i.val < j})).minimalPrimes by
    exact H j hj P hP hPm
  clear hj hP hPm
  intro j
  induction j using Nat.strong_induction_on with
  | _ j IH =>
  intro hj Q hQ hQm
  have hjC : j ≤ C := le_trans hj hrC
  have hQprime : Q.IsPrime := hQ.1
  have hIjQ : Ideal.span (f '' {i : Fin C | i.val < j}) ≤ Q := ideal_le_of_mem_ass_smul_top hQ
  by_cases hcase : ∀ k < j, ∀ p ∈ associatedPrimes (MvPolynomial (Fin n) K)
      ((MvPolynomial (Fin n) K) ⧸ (Ideal.span (f '' {i : Fin C | i.val < k}) • ⊤ :
        Submodule (MvPolynomial (Fin n) K) (MvPolynomial (Fin n) K))),
      p ≤ Q → (if h : k < C then f ⟨k, h⟩ else 0) ∉ p
  · -- CASE 1: the localized prefix is weakly regular; conclude via the dimension count.
    set g : ℕ → MvPolynomial (Fin n) K := fun k => if h : k < C then f ⟨k, h⟩ else 0 with hg
    set L : List (MvPolynomial (Fin n) K) := (List.range j).map g with hLdef
    set alg := algebraMap (MvPolynomial (Fin n) K) (Localization.AtPrime Q) with halg
    have hLspan : Ideal.ofList L = Ideal.span (f '' {i : Fin C | i.val < j}) :=
      ofList_range_dite_eq_span f j hjC
    rw [← hLspan]
    apply minimalPrimes_of_localized_weaklyRegular L
    · -- membership in `Q`
      intro x hx
      exact hIjQ (hLspan ▸ Ideal.subset_span hx)
    · -- weak regularity via the stagewise criterion
      apply localized_weaklyRegular_of_stages
      intro k hk
      have hkj : k < j := by
        rw [hLdef] at hk; simpa using hk
      have hkC : k ≤ C := le_of_lt (lt_of_lt_of_le hkj hjC)
      have hstage := isSMulRegular_localized_quot_of_stage (P := Q)
        (Ideal.span (f '' {i : Fin C | i.val < k})) (g k) (hcase k hkj)
      have hget : L.get ⟨k, hk⟩ = g k := by
        simp [hLdef, List.get_eq_getElem, List.getElem_map, List.getElem_range]
      have htake : Ideal.ofList ((L.take k).map alg)
          = Ideal.map alg (Ideal.span (f '' {i : Fin C | i.val < k})) := by
        have h1 : L.take k = (List.range k).map g := by
          rw [hLdef, ← List.map_take, List.take_range, Nat.min_eq_left (le_of_lt hkj)]
        rw [h1, ← Ideal.map_ofList, ofList_range_dite_eq_span f k hkC]
      rw [hget, htake]
      exact hstage
    · -- the maximal ideal is associated
      have hmap : Ideal.ofList (L.map alg)
          = Ideal.map alg (Ideal.span (f '' {i : Fin C | i.val < j})) := by
        rw [← Ideal.map_ofList, hLspan]
      rw [hmap]
      exact maximalIdeal_mem_ass_localized_quot hQ
  · -- CASE 2: some stage fails; `RegCond` forces `Q = m` and the IH gives minimality.
    push_neg at hcase
    obtain ⟨k, hkj, p, hp₁, hp₂, hp₃⟩ := hcase
    have hkC : k < C := lt_of_lt_of_le hkj hjC
    have hp₃' : f ⟨k, hkC⟩ ∈ p := by
      simpa [dif_pos hkC] using hp₃
    have hsetEq : {j' : Fin C | j' < (⟨k, hkC⟩ : Fin C)} = {i : Fin C | i.val < k} := by
      ext i; simp [Fin.lt_iff_val_lt_val]
    have hprop : ∀ j' : Fin C, (⟨k, hkC⟩ : Fin C) < j' → f j' ∈ p :=
      hreg ⟨k, hkC⟩ p (by rw [hsetEq]; exact hp₁) hp₃'
    have hIkp : Ideal.span (f '' {i : Fin C | i.val < k}) ≤ p :=
      ideal_le_of_mem_ass_smul_top hp₁
    have hp_all : ∀ i : Fin C, f i ∈ p := by
      intro i
      rcases lt_trichotomy i.val k with h | h | h
      · exact hIkp (Ideal.subset_span (Set.mem_image_of_mem f h))
      · have hi : i = ⟨k, hkC⟩ := Fin.ext h
        rw [hi]; exact hp₃'
      · exact hprop i (by rw [Fin.lt_iff_val_lt_val]; exact h)
    have hIrp : Ideal.span (f '' {i : Fin C | i.val < r}) ≤ p :=
      Ideal.span_le.mpr (Set.image_subset_iff.mpr (fun i _ => hp_all i))
    have hpeqm : p = m := eq_of_le_minimalPrime hm hp₁.1 hIrp (le_trans hp₂ hQm)
    have hQeqp : Q = p := le_antisymm (hpeqm.symm ▸ hQm) hp₂
    have hkr : k ≤ r := le_of_lt (lt_of_lt_of_le hkj hj)
    have hIkj : Ideal.span (f '' {i : Fin C | i.val < k})
        ≤ Ideal.span (f '' {i : Fin C | i.val < j}) :=
      Ideal.span_mono (Set.image_mono (fun i (hi : i.val < k) => lt_of_lt_of_le hi (le_of_lt hkj)))
    have hpmin : p ∈ (Ideal.span (f '' {i : Fin C | i.val < k})).minimalPrimes :=
      IH k hkj hkr p hp₁ (le_trans hp₂ hQm)
    rw [hQeqp]
    exact mem_minimalPrimes_of_le hIkj hpmin (hQeqp ▸ hIjQ)

/-! ## Wrappers translating `ChargeBridge` (about `isoComp`) to `isoComp'`. -/

/-- `isoComp'` agrees with `isoComp` at a minimal prime. -/
theorem isoComp'_eq_isoComp {I p : Ideal (MvPolynomial (Fin n) K)}
    (hp : p ∈ I.minimalPrimes) :
    isoComp' I p = @isoComp K _ n I p hp.1.1 := by
  unfold isoComp'
  rw [dif_pos hp.1.1]

/-- `isoComp'` of a minimal prime of a homogeneous ideal is homogeneous. -/
theorem isHomog_isoComp' {I : Ideal (MvPolynomial (Fin n) K)} (hI : IsHomog I)
    {p : Ideal (MvPolynomial (Fin n) K)} (hp : p ∈ I.minimalPrimes) :
    IsHomog (isoComp' I p) := by
  haveI : p.IsPrime := hp.1.1
  rw [isoComp'_eq_isoComp hp]
  exact isoComp_isHomog I p hI hp

/-- Height/degree bridge, phrased for `isoComp'`. -/
theorem natDegree_hilbPoly_isoComp'_add [Infinite K]
    {I : Ideal (MvPolynomial (Fin n) K)} (hI : IsHomog I)
    {p : Ideal (MvPolynomial (Fin n) K)} (hp : p ∈ I.minimalPrimes)
    (hlt : p.height.toNat < n) :
    (hilbPoly (isoComp' I p)).natDegree + 1 + p.height.toNat = n := by
  haveI : p.IsPrime := hp.1.1
  rw [isoComp'_eq_isoComp hp]
  exact AristotleChargeBridge.natDegree_hilbPoly_isoComp_add I hI hp hlt

theorem hilbPoly_isoComp'_ne_zero [Infinite K]
    {I : Ideal (MvPolynomial (Fin n) K)} (hI : IsHomog I)
    {p : Ideal (MvPolynomial (Fin n) K)} (hp : p ∈ I.minimalPrimes)
    (hlt : p.height.toNat < n) :
    hilbPoly (isoComp' I p) ≠ 0 := by
  haveI : p.IsPrime := hp.1.1
  rw [isoComp'_eq_isoComp hp]
  exact AristotleChargeBridge.hilbPoly_isoComp_ne_zero_of_height_lt I hI hp hlt

theorem hilbPoly_isoComp'_eq_zero [Infinite K]
    {I : Ideal (MvPolynomial (Fin n) K)} (hI : IsHomog I)
    {p : Ideal (MvPolynomial (Fin n) K)} (hp : p ∈ I.minimalPrimes)
    (heq : p.height.toNat = n) :
    hilbPoly (isoComp' I p) = 0 := by
  haveI : p.IsPrime := hp.1.1
  rw [isoComp'_eq_isoComp hp]
  exact AristotleChargeBridge.hilbPoly_isoComp_eq_zero_of_height_eq I hI hp heq

/-- `degQ (isoComp' I p) = 0` when `p` is the irrelevant maximal ideal (height `n`). -/
theorem degQ_isoComp'_eq_zero_of_height_eq [Infinite K]
    {I : Ideal (MvPolynomial (Fin n) K)} (hI : IsHomog I)
    {p : Ideal (MvPolynomial (Fin n) K)} (hp : p ∈ I.minimalPrimes)
    (heq : p.height.toNat = n) :
    degQ (isoComp' I p) = 0 := by
  unfold degQ
  rw [hilbPoly_isoComp'_eq_zero hI hp heq]
  simp

/-! ## Iterated additivity of `degQ` over equal-height isolated components. -/

/-
The radical of a finite intersection of isolated components is the
intersection of the corresponding primes.
-/
theorem radical_finset_inf_isoComp' {I : Ideal (MvPolynomial (Fin n) K)}
    (S : Finset (Ideal (MvPolynomial (Fin n) K)))
    (hS : ∀ q ∈ S, q ∈ I.minimalPrimes) :
    (S.inf (isoComp' I)).radical = S.inf id := by
  revert hS;
  induction' S using Finset.induction with q S hS ih;
  · simp +decide [ Ideal.radical_top ];
  · intro h; specialize ih fun q hq => h q ( Finset.mem_insert_of_mem hq ) ; simp_all +decide [ Finset.inf_insert, Ideal.radical_inf ] ;
    rw [ isoComp'_eq_isoComp, radical_isoComp ] ; aesop;
    exact h.1

/-
The Krull dimension of `R ⧸ p` for a prime `p` is `n - height p`.
-/
theorem ringKrullDim_quotient_prime_eq (p : Ideal (MvPolynomial (Fin n) K)) [hp : p.IsPrime] :
    ringKrullDim (MvPolynomial (Fin n) K ⧸ p) = ((n - p.height.toNat : ℕ) : WithBot ℕ∞) := by
  by_contra h_contra;
  have h_eq : (p.height : WithBot ℕ∞) + ringKrullDim (MvPolynomial (Fin n) K ⧸ p) = n := by
    convert AristotleDimensionFormula.height_add_ringKrullDim_quotient p;
  cases h : ringKrullDim ( MvPolynomial ( Fin n ) K ⧸ p ) <;> simp_all +decide;
  norm_cast at *;
  cases h : p.height <;> simp_all +decide;
  cases ‹ℕ∞› <;> norm_cast at *;
  exact h_contra ( by rw [ Nat.sub_eq_of_eq_add ] ; linarith )

/-
If every prime containing `J` strictly contains the prime `p`, then the
quotient by `J` has strictly smaller Krull dimension than the quotient by `p`.
-/
set_option maxHeartbeats 1000000 in
theorem ringKrullDim_quotient_lt_of_forall_prime_gt
    (p : Ideal (MvPolynomial (Fin n) K)) [hp : p.IsPrime]
    (J : Ideal (MvPolynomial (Fin n) K)) (hJ : J ≠ ⊤)
    (hfin : ringKrullDim (MvPolynomial (Fin n) K ⧸ p) ≠ ⊤)
    (hgt : ∀ P : Ideal (MvPolynomial (Fin n) K), P.IsPrime → J ≤ P → p < P) :
    ringKrullDim (MvPolynomial (Fin n) K ⧸ J)
      < ringKrullDim (MvPolynomial (Fin n) K ⧸ p) := by
  contrapose! hfin;
  -- Let `x₀ : PrimeSpectrum R := ⟨p, hp⟩`. Its coheight is finite (`ringKrullDim (R ⧸ p) ≠ ⊤` gives `Order.coheight x₀ ≠ ⊤`).
  obtain ⟨x₀, hx₀⟩ : ∃ x₀ : PrimeSpectrum (MvPolynomial (Fin n) K), x₀.asIdeal = p := by
    exact ⟨ ⟨ p, hp ⟩, rfl ⟩;
  have h_coheight : ∀ s : LTSeries (PrimeSpectrum.zeroLocus (J : Set (MvPolynomial (Fin n) K))), s.length + 1 ≤ Order.coheight x₀ := by
    intro s
    have h_head : x₀ < s.head := by
      have h_head : J ≤ (s.head : PrimeSpectrum (MvPolynomial (Fin n) K)).asIdeal := by
        exact s.head.2;
      convert hgt _ _ h_head using 1;
      · simp +decide [ ← hx₀, PrimeSpectrum.asIdeal_lt_asIdeal ];
      · exact ( s.head : PrimeSpectrum ( MvPolynomial ( Fin n ) K ) ).2;
    have h_length : s.length ≤ Order.coheight (s.head : PrimeSpectrum (MvPolynomial (Fin n) K)) := by
      have h_length : s.length ≤ Order.coheight (s.head : PrimeSpectrum (MvPolynomial (Fin n) K)) := by
        have h_series : ∃ t : LTSeries (PrimeSpectrum (MvPolynomial (Fin n) K)), t.length = s.length ∧ t.head = s.head := by
          refine' ⟨ ⟨ s.length, fun i => s i, _ ⟩, rfl, rfl ⟩;
          exact fun i => s.step i
        obtain ⟨ t, ht₁, ht₂ ⟩ := h_series;
        rw [ ← ht₁, ← ht₂ ];
        grind +suggestions;
      exact h_length;
    have h_coheight : Order.coheight (s.head : PrimeSpectrum (MvPolynomial (Fin n) K)) + 1 ≤ Order.coheight x₀ := by
      grind +suggestions;
    refine' le_trans _ h_coheight;
    gcongr;
  have h_coheight : Order.krullDim (PrimeSpectrum.zeroLocus (J : Set (MvPolynomial (Fin n) K))) ≤ (Order.coheight x₀ - 1 : ℕ∞) := by
    refine' iSup_le _;
    intro s;
    cases h : Order.coheight x₀ <;> simp_all +decide;
    norm_cast at *;
    exact Nat.le_sub_one_of_lt ( h_coheight s );
  have h_coheight : ringKrullDim (MvPolynomial (Fin n) K ⧸ J) ≤ (Order.coheight x₀ - 1 : ℕ∞) := by
    convert h_coheight using 1;
    convert ringKrullDim_quotient J using 1;
  have h_coheight : ringKrullDim (MvPolynomial (Fin n) K ⧸ p) = (Order.coheight x₀ : ℕ∞) := by
    convert AristotleDimensionFormula.ringKrullDim_quotient_eq_coheight p;
  cases h : Order.coheight x₀ <;> simp_all +decide;
  cases ‹ℕ› <;> simp_all +decide [ WithBot.coe_le_coe ];
  · have := Ideal.exists_le_maximal J hJ; obtain ⟨ m, hm₁, hm₂ ⟩ := this; specialize hgt m; simp_all +decide [ IsMax ] ;
    exact absurd ( h ( show x₀ ≤ ⟨ m, hm₁.isPrime ⟩ from by
                        exact hx₀.symm ▸ hgt hm₁.isPrime |>.le ) ) ( by
                        exact fun h => lt_irrefl _ ( lt_of_lt_of_le ( hgt hm₁.isPrime ) ( by aesop ) ) );
  · exact not_lt_of_ge ‹_› ( Nat.cast_lt.mpr ( Nat.lt_succ_self _ ) |> lt_of_lt_of_le <| hfin )

/-
The Hilbert polynomial of the whole (trivial) quotient is zero.
-/
theorem hilbPoly_top_eq_zero :
    hilbPoly (⊤ : Ideal (MvPolynomial (Fin n) K)) = 0 := by
  refine' hilbPoly_eq_of_eventually _ _ _;
  simp +decide [ HF, Module.finrank ]

/-
A finite intersection of homogeneous isolated components is homogeneous.
-/
theorem isHomog_finset_inf_isoComp' {I : Ideal (MvPolynomial (Fin n) K)} (hI : IsHomog I)
    (S : Finset (Ideal (MvPolynomial (Fin n) K)))
    (hS : ∀ q ∈ S, q ∈ I.minimalPrimes) :
    IsHomog (S.inf (isoComp' I)) := by
  induction S using Finset.induction <;> simp_all +decide [ Finset.inf_insert ];
  · unfold IsHomog; aesop;
  · rename_i h₁ h₂ h₃;
    -- By `isHomog_isoComp'`, `isoComp' I a✝` is homogeneous.
    have h_isoComp : IsHomog (isoComp' I ‹_›) := by
      exact isHomog_isoComp' hI hS.1;
    intro r hr i; exact ⟨by
    exact h_isoComp _ hr.1 _, by
      exact h₃ _ hr.2 _⟩

/-
Every prime containing `isoComp' I q ⊔ S.inf (isoComp' I)` strictly contains `q`.
-/
theorem forall_prime_ge_sup_isoComp'_gt
    {I : Ideal (MvPolynomial (Fin n) K)} {h : ℕ}
    {q : Ideal (MvPolynomial (Fin n) K)} (hq : q ∈ I.minimalPrimes)
    (hqh : q.height.toNat = h)
    (S : Finset (Ideal (MvPolynomial (Fin n) K)))
    (hS : ∀ q' ∈ S, q' ∈ I.minimalPrimes ∧ q'.height.toNat = h) (hqS : q ∉ S)
    {P : Ideal (MvPolynomial (Fin n) K)} (hP : P.IsPrime)
    (hle : isoComp' I q ⊔ S.inf (isoComp' I) ≤ P) :
    q < P := by
  refine' lt_of_le_of_ne _ _;
  · convert Ideal.radical_mono ( le_trans ( le_sup_left ) hle ) using 1;
    · convert Eq.symm ( radical_isoComp I q hq ) using 1;
      rw [ isoComp'_eq_isoComp hq ];
    · exact (Ideal.IsPrime.radical hP).symm;
  · intro hqP;
    have hq'_le_q : ∃ q' ∈ S, q' ≤ q := by
      have hq'_le_q : S.inf id ≤ q := by
        convert Ideal.radical_mono ( show S.inf ( isoComp' I ) ≤ P from le_trans ( le_sup_right ) hle ) using 1;
        · rw [ radical_finset_inf_isoComp' S fun q' hq' => ( hS q' hq' ).1 ];
        · rw [ hqP, hP.radical ];
      contrapose! hq'_le_q;
      simp +decide [ Ideal.IsPrime.inf_le', hq.1.1 ];
      exact hq'_le_q;
    obtain ⟨ q', hq'S, hq'q ⟩ := hq'_le_q;
    have := eq_of_le_minimalPrime hq ( hS q' hq'S |>.1 ).1.1 ( hS q' hq'S |>.1 ).1.2 hq'q; aesop;

/-- General position: adjoining a new equal-height component to a finite
intersection of components strictly drops the Hilbert-polynomial degree (or
kills it). -/
theorem hilbPoly_sup_isoComp'_lt [Infinite K]
    {I : Ideal (MvPolynomial (Fin n) K)} (hI : IsHomog I) {h : ℕ} (hhn : h < n)
    {q : Ideal (MvPolynomial (Fin n) K)} (hq : q ∈ I.minimalPrimes)
    (hqh : q.height.toNat = h)
    (S : Finset (Ideal (MvPolynomial (Fin n) K)))
    (hS : ∀ q' ∈ S, q' ∈ I.minimalPrimes ∧ q'.height.toNat = h) (hqS : q ∉ S)
    (hSne : S.Nonempty) :
    hilbPoly (isoComp' I q ⊔ S.inf (isoComp' I)) = 0 ∨
      (hilbPoly (isoComp' I q ⊔ S.inf (isoComp' I))).natDegree < n - 1 - h := by
  haveI hqp : q.IsPrime := hq.1.1
  set J := isoComp' I q ⊔ S.inf (isoComp' I) with hJdef
  have h_homog : IsHomog J :=
    isHomog_sup (isHomog_isoComp' hI hq)
      (isHomog_finset_inf_isoComp' hI S (fun q' hq' => (hS q' hq').1))
  by_cases hz : hilbPoly J = 0
  · exact Or.inl hz
  · right
    have hJtop : J ≠ ⊤ := fun htop => hz (htop ▸ hilbPoly_top_eq_zero)
    have hqdim := ringKrullDim_quotient_prime_eq q
    rw [hqh] at hqdim
    have hfin : ringKrullDim (MvPolynomial (Fin n) K ⧸ q) ≠ ⊤ := by
      rw [hqdim]
      have hcast : (((n - h : ℕ)) : WithBot ℕ∞) = (((n - h : ℕ) : ℕ∞) : WithBot ℕ∞) := by
        norm_cast
      rw [hcast]; exact_mod_cast ENat.coe_ne_top (n - h)
    have hlt := ringKrullDim_quotient_lt_of_forall_prime_gt q J hJtop hfin
      (fun P hP hle => forall_prime_ge_sup_isoComp'_gt hq hqh S hS hqS hP hle)
    rw [hqdim] at hlt
    have hnat := (HF_poly_natDegree J h_homog hJtop (hilbPoly J) (hilbPoly_spec J h_homog)).2 hz
    rw [← hnat] at hlt
    have : (hilbPoly J).natDegree + 1 < n - h := by exact_mod_cast hlt
    omega

/-
Iterated `degQ` additivity over a finite set of equal-height minimal primes.
-/
theorem degQ_finset_inf_isoComp'_eq_sum [Infinite K]
    {I : Ideal (MvPolynomial (Fin n) K)} (hI : IsHomog I) {h : ℕ} (hhn : h < n)
    (S : Finset (Ideal (MvPolynomial (Fin n) K)))
    (hS : ∀ q ∈ S, q ∈ I.minimalPrimes ∧ q.height.toNat = h) :
    degQ (S.inf (isoComp' I)) = ∑ q ∈ S, degQ (isoComp' I q) ∧
      (S.Nonempty → (hilbPoly (S.inf (isoComp' I))).natDegree = n - 1 - h ∧
        hilbPoly (S.inf (isoComp' I)) ≠ 0) := by
  induction' S using Finset.induction with q S hqS ih;
  · simp +decide [ degQ, hilbPoly_top_eq_zero ];
  · simp_all +decide [ Finset.inf_insert ];
    by_cases hSempty : S.Nonempty;
    · have := hilbPoly_sup_isoComp'_lt hI hhn hS.1.1 hS.1.2 S hS.2 hqS hSempty;
      convert degQ_inf_add ( isoComp' I q ) ( S.inf ( isoComp' I ) ) ( isHomog_isoComp' hI hS.1.1 ) ( isHomog_finset_inf_isoComp' hI S ( fun q' hq' => hS.2 q' hq' |>.1 ) ) _ _ _ _ this using 1;
      · rw [ ih.1 ];
      · grind +suggestions;
      · exact ih.2 hSempty |>.1;
      · exact hilbPoly_isoComp'_ne_zero hI hS.1.1 ( by omega );
      · exact ih.2 hSempty |>.2;
    · simp_all +decide [ Finset.not_nonempty_iff_eq_empty.mp hSempty ];
      exact ⟨ by have := natDegree_hilbPoly_isoComp'_add hI hS.1 ( by omega ) ; omega, hilbPoly_isoComp'_ne_zero hI hS.1 ( by omega ) ⟩

/-! ## S3 bridge and the per-height-class charge. -/

/-
S3 bridge (containment form): the intersection of the isolated `I_r`-components
over the minimal primes of `I_r` below a new minimal prime `m` of `I_{r+1}` is
contained in the `I_{r+1}`-component at `m`.
-/
theorem iInf_components_le_isoComp'_I1 [IsAlgClosed K] {C : ℕ}
    (f : Fin C → MvPolynomial (Fin n) K) (hreg : RegCond f) (r : ℕ) (hr : r < C)
    {m : Ideal (MvPolynomial (Fin n) K)}
    (hm : m ∈ (Ideal.span (f '' {i : Fin C | i.val < r + 1})).minimalPrimes) :
    (⨅ q : {q : Ideal (MvPolynomial (Fin n) K) //
        q ∈ (Ideal.span (f '' {i : Fin C | i.val < r})).minimalPrimes ∧ q ≤ m},
      isoComp' (Ideal.span (f '' {i : Fin C | i.val < r})) q.1)
      ≤ isoComp' (Ideal.span (f '' {i : Fin C | i.val < r + 1})) m := by
  have h_ass : ∀ P ∈ associatedPrimes (MvPolynomial (Fin n) K) ((MvPolynomial (Fin n) K) ⧸ (Ideal.span (f '' {i : Fin C | i.val < r}))), P ≤ m → P ∈ (Ideal.span (f '' {i : Fin C | i.val < r})).minimalPrimes := by
    intros P hP hPm;
    convert ass_control_at_minimalPrime f hreg ( r + 1 ) ( by linarith ) ( by simpa using hm ) r ( by linarith ) _ hPm using 1;
    convert hP using 1;
    simp +decide [ Submodule.smul_def ];
    rw [ Ideal.mul_top ];
  have h_isoComp_eq : @isoComp K _ n (Ideal.span (f '' {i : Fin C | i.val < r})) m hm.1.1 = @isoComp K _ n (⨅ q : {q : Ideal (MvPolynomial (Fin n) K) // q ∈ (Ideal.span (f '' {i : Fin C | i.val < r})).minimalPrimes ∧ q ≤ m}, isoComp' (Ideal.span (f '' {i : Fin C | i.val < r})) q.1) m hm.1.1 := by
    convert isoComp_eq_iInf_components_of_ass_control f r h_ass using 1;
  convert le_trans _ ( h_isoComp_eq.le.trans _ ) using 1;
  · convert le_isoComp ( ⨅ q : { q : Ideal ( MvPolynomial ( Fin n ) K ) // q ∈ ( Ideal.span ( f '' { i : Fin C | ( i : ℕ ) < r } ) ).minimalPrimes ∧ q ≤ m }, isoComp' ( Ideal.span ( f '' { i : Fin C | ( i : ℕ ) < r } ) ) q.1 ) m using 1;
  · convert @isoComp_mono K _ n ( Ideal.span ( f '' { i : Fin C | ( i : ℕ ) < r } ) ) ( Ideal.span ( f '' { i : Fin C | ( i : ℕ ) < r + 1 } ) ) m _ _ using 1;
    exact h_isoComp_eq.symm;
    · exact isoComp'_eq_isoComp hm;
    · exact Ideal.span_mono ( Set.image_mono ( fun i hi => by exact Set.mem_setOf.mpr ( Nat.lt_succ_of_lt hi ) ) )

/-
Containment for the charge: with `Ch` a finset containing every minimal prime
of `I_r` below `m`, the intersection of the `I_r`-components over `Ch`, joined with
`span{f_r}`, lands in the `I_{r+1}`-component at `m`.
-/
theorem finset_inf_sup_span_le_isoComp'_I1 [IsAlgClosed K] {C : ℕ}
    (f : Fin C → MvPolynomial (Fin n) K) (hreg : RegCond f) (r : ℕ) (hr : r < C)
    {m : Ideal (MvPolynomial (Fin n) K)}
    (hm : m ∈ (Ideal.span (f '' {i : Fin C | i.val < r + 1})).minimalPrimes)
    (Ch : Finset (Ideal (MvPolynomial (Fin n) K)))
    (hCh : ∀ q ∈ (Ideal.span (f '' {i : Fin C | i.val < r})).minimalPrimes, q ≤ m → q ∈ Ch) :
    Ch.inf (isoComp' (Ideal.span (f '' {i : Fin C | i.val < r})))
        ⊔ Ideal.span {f ⟨r, hr⟩}
      ≤ isoComp' (Ideal.span (f '' {i : Fin C | i.val < r + 1})) m := by
  refine' sup_le _ _;
  · refine' le_trans _ ( iInf_components_le_isoComp'_I1 f hreg r hr hm );
    simp +decide [ iInf_le_iff ];
    exact fun q hq hqm => Finset.inf_le ( hCh q hq hqm );
  · have h_f_r_in_I1 : f ⟨r, hr⟩ ∈ Ideal.span (f '' {i : Fin C | i.val < r + 1}) := by
      exact Ideal.subset_span ⟨ _, by simp +decide, rfl ⟩;
    have h_le_isoComp : Ideal.span (f '' {i : Fin C | i.val < r + 1}) ≤ isoComp' (Ideal.span (f '' {i : Fin C | i.val < r + 1})) m := by
      convert le_isoComp _ _;
      convert isoComp'_eq_isoComp hm;
    exact le_trans ( Ideal.span_le.mpr ( Set.singleton_subset_iff.mpr h_f_r_in_I1 ) ) h_le_isoComp

/-
A minimal prime `q` of `I_r` below a new minimal prime `m` of `I_{r+1}` is a
cut prime (`f_r ∉ q`) and its height is one less than that of `m`.
-/
theorem new_prime_cut_below [IsAlgClosed K] {C : ℕ}
    (f : Fin C → MvPolynomial (Fin n) K)
    (hfhom : ∀ i, ∃ e : ℕ, f i ∈ homogeneousSubmodule (Fin n) K e)
    (r : ℕ) (hr : r < C)
    {m q : Ideal (MvPolynomial (Fin n) K)}
    (hm : m ∈ (Ideal.span (f '' {i : Fin C | i.val < r + 1})).minimalPrimes)
    (hmI0 : m ∉ (Ideal.span (f '' {i : Fin C | i.val < r})).minimalPrimes)
    (hqmin : q ∈ (Ideal.span (f '' {i : Fin C | i.val < r})).minimalPrimes)
    (hqm : q ≤ m) :
    f ⟨r, hr⟩ ∉ q ∧ m.height = q.height + 1 := by
  have hI1eq : Ideal.span (f '' {i : Fin C | i.val < r + 1}) = Ideal.span (f '' {i : Fin C | i.val < r}) ⊔ Ideal.span {f ⟨r, hr⟩} := by
    rw [ ← Ideal.span_union ];
    congr with x;
    grind;
  have hfr_not_in_q : f ⟨r, hr⟩ ∉ q := by
    intro hqfr;
    have hqI1 : q ∈ (Ideal.span (f '' {i : Fin C | i.val < r + 1})).minimalPrimes := by
      rw [hI1eq];
      apply mem_minimalPrimes_sup_span_singleton_iff hqmin |>.2 hqfr;
    have hq_eq_m : q = m := by
      apply eq_of_le_minimalPrime hm;
      · exact hqmin.1.1;
      · exact hqI1.1.2;
      · exact hqm;
    grind;
  have h_minimal : m ∈ (q ⊔ Ideal.span {f ⟨r, hr⟩}).minimalPrimes := by
    refine' ⟨ ⟨ _, _ ⟩, _ ⟩;
    · exact hm.1.1;
    · have hfr_in_m : f ⟨r, hr⟩ ∈ m := by
        exact hm.1.2 ( Ideal.subset_span ⟨ ⟨ r, hr ⟩, by simp +decide, rfl ⟩ );
      exact sup_le hqm ( Ideal.span_le.mpr ( Set.singleton_subset_iff.mpr hfr_in_m ) );
    · intro p hp hpm
      have hI1_le_p : Ideal.span (f '' {i : Fin C | i.val < r + 1}) ≤ p := by
        simp_all +decide [ Ideal.span_le, Set.image_subset_iff ];
        intro i hi; exact hp.2.1 (hqmin.1.2 (Ideal.subset_span (Set.mem_image_of_mem _ hi))) ;
      exact hm.2 ⟨ hp.1, hI1_le_p ⟩ hpm;
  exact ⟨ hfr_not_in_q, by haveI := hqmin.1.1; exact AristotleAffineDimension.height_eq_height_add_one_of_mem_minimalPrimes_sup hqm hfr_not_in_q h_minimal ⟩

/-- The divided degree of a homogeneous component is nonnegative. -/
theorem degQ_nonneg [Infinite K] {I : Ideal (MvPolynomial (Fin n) K)} (hI : IsHomog I) :
    0 ≤ degQ I := by
  obtain ⟨D, hD⟩ := degQ_eq_natCast I hI
  rw [hD]
  exact Nat.cast_nonneg D

/-- A minimal prime `q` of `I_r` below a new minimal prime `m` of height `h+1` is
cut (`q ∉ minimalPrimes I_{r+1}`) and has height `h`. -/
theorem cut_below_new_props [IsAlgClosed K] {C : ℕ}
    (f : Fin C → MvPolynomial (Fin n) K)
    (hfhom : ∀ i, ∃ e : ℕ, f i ∈ homogeneousSubmodule (Fin n) K e)
    (r : ℕ) (hr : r < C) {h : ℕ}
    {m q : Ideal (MvPolynomial (Fin n) K)}
    (hmI1 : m ∈ (Ideal.span (f '' {i : Fin C | i.val < r + 1})).minimalPrimes)
    (hmI0 : m ∉ (Ideal.span (f '' {i : Fin C | i.val < r})).minimalPrimes)
    (hmh : m.height.toNat = h + 1)
    (hqmin : q ∈ (Ideal.span (f '' {i : Fin C | i.val < r})).minimalPrimes)
    (hqm : q ≤ m) :
    q ∉ (Ideal.span (f '' {i : Fin C | i.val < r + 1})).minimalPrimes ∧ q.height.toNat = h := by
  classical
  obtain ⟨hfr_not_q, hheight⟩ :=
    new_prime_cut_below f hfhom r hr hmI1 hmI0 hqmin hqm
  constructor
  · intro hqI1
    have hfr_mem_I1 :
        f ⟨r, hr⟩ ∈ Ideal.span (f '' {i : Fin C | i.val < r + 1}) := by
      exact Ideal.subset_span ⟨⟨r, hr⟩, by simp +decide, rfl⟩
    exact hfr_not_q (hqI1.1.2 hfr_mem_I1)
  · have hqheight_ne_top : q.height ≠ ⊤ := by
      have hle := Ideal.height_le_ringKrullDim_of_ne_top (I := q) hqmin.1.1.ne_top
      rw [AristotleDimensionFormula.mvPoly_ringKrullDim (K := K) n] at hle
      intro htop
      rw [htop] at hle
      exact ENat.coe_ne_top n (WithBot.coe_eq_top.mp (top_le_iff.mp hle))
    have htoNat :
        (q.height + 1).toNat = q.height.toNat + 1 := by
      simpa using ENat.toNat_add hqheight_ne_top (by simp : (1 : ℕ∞) ≠ ⊤)
    have hsucc : q.height.toNat + 1 = h + 1 := by
      rw [← htoNat, ← hheight, hmh]
    omega

/-- Per-height-class charge: the new minimal primes of `I_{r+1}` of height `h+1`
contribute (in aggregate `degQ`) at most `e` times the cut minimal primes of `I_r`
of height `h`, where `e = deg f_r`. -/
theorem divdegQ_class_charge [IsAlgClosed K] {C : ℕ}
    (f : Fin C → MvPolynomial (Fin n) K)
    (hfhom : ∀ i, ∃ e : ℕ, f i ∈ homogeneousSubmodule (Fin n) K e)
    (hreg : RegCond f) (r : ℕ) (hr : r < C)
    {e : ℕ} (he1 : 1 ≤ e) (hfe : f ⟨r, hr⟩ ∈ homogeneousSubmodule (Fin n) K e) (h : ℕ) :
    (∑ m ∈ ((Ideal.finite_minimalPrimes_of_isNoetherianRing (MvPolynomial (Fin n) K)
        (Ideal.span (f '' {i : Fin C | i.val < r + 1}))).toFinset \
        (Ideal.finite_minimalPrimes_of_isNoetherianRing (MvPolynomial (Fin n) K)
        (Ideal.span (f '' {i : Fin C | i.val < r}))).toFinset).filter
          (fun p => p.height.toNat = h + 1),
      degQ (isoComp' (Ideal.span (f '' {i : Fin C | i.val < r + 1})) m))
    ≤ (e : ℚ) *
      (∑ q ∈ ((Ideal.finite_minimalPrimes_of_isNoetherianRing (MvPolynomial (Fin n) K)
        (Ideal.span (f '' {i : Fin C | i.val < r}))).toFinset \
        (Ideal.finite_minimalPrimes_of_isNoetherianRing (MvPolynomial (Fin n) K)
        (Ideal.span (f '' {i : Fin C | i.val < r + 1}))).toFinset).filter
          (fun p => p.height.toNat = h),
        degQ (isoComp' (Ideal.span (f '' {i : Fin C | i.val < r})) q)) := by
  classical
  set I0 := Ideal.span (f '' {i : Fin C | i.val < r}) with hI0def
  set I1 := Ideal.span (f '' {i : Fin C | i.val < r + 1}) with hI1def
  set FI0 := (Ideal.finite_minimalPrimes_of_isNoetherianRing (MvPolynomial (Fin n) K)
      I0).toFinset with hFI0def
  set FI1 := (Ideal.finite_minimalPrimes_of_isNoetherianRing (MvPolynomial (Fin n) K)
      I1).toFinset with hFI1def
  set NEWh := (FI1 \ FI0).filter (fun p => p.height.toNat = h + 1) with hNEWhdef
  set CUTh := (FI0 \ FI1).filter (fun p => p.height.toNat = h) with hCUThdef
  -- Basic structural facts.
  have hhomI0 : IsHomog I0 := isHomog_span_image f _ hfhom
  have hhomI1 : IsHomog I1 := isHomog_span_image f _ hfhom
  have hI0I1 : I0 ≤ I1 := by
    rw [hI0def, hI1def]
    exact Ideal.span_mono (Set.image_mono (fun i hi => lt_trans hi (Nat.lt_succ_self r)))
  have hI1eq : I1 = I0 ⊔ Ideal.span {f ⟨r, hr⟩} := by
    rw [hI1def, hI0def, ← Ideal.span_union]
    congr 1
    ext x
    constructor
    · rintro ⟨i, hi, rfl⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h' | h'
      · exact Or.inl ⟨i, h', rfl⟩
      · refine Or.inr ?_
        simp only [Set.mem_singleton_iff]
        congr 1
        exact Fin.ext h'
    · rintro (⟨i, hi, rfl⟩ | hx)
      · exact ⟨i, Nat.lt_succ_of_lt hi, rfl⟩
      · simp only [Set.mem_singleton_iff] at hx
        exact ⟨⟨r, hr⟩, by simp, hx.symm⟩
  -- Membership characterisations of the two index finsets.
  have hNEWh_mem : ∀ m ∈ NEWh, m ∈ I1.minimalPrimes ∧ m ∉ I0.minimalPrimes ∧
      m.height.toNat = h + 1 := by
    intro m hm
    rw [hNEWhdef, Finset.mem_filter, Finset.mem_sdiff] at hm
    obtain ⟨⟨hmFI1, hmFI0⟩, hmht⟩ := hm
    refine ⟨?_, ?_, hmht⟩
    · rw [hFI1def, Set.Finite.mem_toFinset] at hmFI1; exact hmFI1
    · intro hcon; apply hmFI0; rw [hFI0def, Set.Finite.mem_toFinset]; exact hcon
  have hCUTh_mem : ∀ q ∈ CUTh, q ∈ I0.minimalPrimes ∧ q ∉ I1.minimalPrimes ∧
      q.height.toNat = h := by
    intro q hq
    rw [hCUThdef, Finset.mem_filter, Finset.mem_sdiff] at hq
    obtain ⟨⟨hqFI0, hqFI1⟩, hqht⟩ := hq
    refine ⟨?_, ?_, hqht⟩
    · rw [hFI0def, Set.Finite.mem_toFinset] at hqFI0; exact hqFI0
    · intro hcon; apply hqFI1; rw [hFI1def, Set.Finite.mem_toFinset]; exact hcon
  -- Cut primes below a new prime lie in `CUTh`.
  have hbelow : ∀ m ∈ NEWh, ∀ q ∈ I0.minimalPrimes, q ≤ m → q ∈ CUTh := by
    intro m hm q hqmin hqm
    obtain ⟨hmmin, hmnotI0, hmht⟩ := hNEWh_mem m hm
    obtain ⟨hqnotI1, hqht⟩ :=
      cut_below_new_props f hfhom r hr hmmin hmnotI0 hmht hqmin hqm
    rw [hCUThdef, Finset.mem_filter, Finset.mem_sdiff]
    refine ⟨⟨?_, ?_⟩, hqht⟩
    · rw [hFI0def, Set.Finite.mem_toFinset]; exact hqmin
    · intro hcon; apply hqnotI1; rw [hFI1def, Set.Finite.mem_toFinset] at hcon; exact hcon
  -- The RHS sum is nonnegative.
  have hRHS_nonneg : 0 ≤ ∑ q ∈ CUTh, degQ (isoComp' I0 q) := by
    apply Finset.sum_nonneg
    intro q hq
    exact degQ_nonneg (isHomog_isoComp' hhomI0 (hCUTh_mem q hq).1)
  have heQ : (0 : ℚ) ≤ (e : ℚ) := by positivity
  -- Edge case: no new primes of this height class.
  rcases NEWh.eq_empty_or_nonempty with hempty | hne
  · rw [hempty, Finset.sum_empty]
    exact mul_nonneg heQ hRHS_nonneg
  -- From now on `NEWh` is nonempty; deduce `h + 1 ≤ n`.
  obtain ⟨m0, hm0⟩ := id hne
  obtain ⟨hm0min, hm0notI0, hm0ht⟩ := hNEWh_mem m0 hm0
  haveI : m0.IsPrime := hm0min.1.1
  have hh1_le_n : h + 1 ≤ n := by
    have := AristotleChargeBridge.height_toNat_le (K := K) (n := n) m0
    rw [hm0ht] at this; exact this
  by_cases hcase : h + 1 < n
  · -- Main case.
    -- `CUTh` is nonempty: pick a minimal prime of `I0` below `m0`.
    obtain ⟨q0, hq0min, hq0m⟩ :=
      Ideal.exists_minimalPrimes_le (hI0I1.trans hm0min.1.2)
    have hCUThne : CUTh.Nonempty := ⟨q0, hbelow m0 hm0 q0 hq0min hq0m⟩
    -- Degree/sum identity for the new primes (class `h+1`).
    have hCsum := degQ_finset_inf_isoComp'_eq_sum hhomI1 (h := h + 1) hcase NEWh
      (fun m hm => ⟨(hNEWh_mem m hm).1, (hNEWh_mem m hm).2.2⟩)
    -- Degree/sum identity for the cut primes (class `h`).
    have hGsum := degQ_finset_inf_isoComp'_eq_sum hhomI0 (h := h) (by omega) CUTh
      (fun q hq => ⟨(hCUTh_mem q hq).1, (hCUTh_mem q hq).2.2⟩)
    have hJhom : IsHomog (CUTh.inf (isoComp' I0)) :=
      isHomog_finset_inf_isoComp' hhomI0 CUTh (fun q hq => (hCUTh_mem q hq).1)
    have hJdeg : (hilbPoly (CUTh.inf (isoComp' I0))).natDegree = n - 1 - h :=
      (hGsum.2 hCUThne).1
    have hJne : hilbPoly (CUTh.inf (isoComp' I0)) ≠ 0 := (hGsum.2 hCUThne).2
    -- `f r` is a nonzerodivisor modulo `J = CUTh.inf`.
    have hJiInf : CUTh.inf (isoComp' I0) = ⨅ p ∈ CUTh, isoComp' I0 p :=
      Finset.inf_eq_iInf CUTh (isoComp' I0)
    have hreg' : IsSMulRegular (MvPolynomial (Fin n) K ⧸ CUTh.inf (isoComp' I0))
        (f ⟨r, hr⟩) := by
      rw [hJiInf]
      refine isSMulRegular_inf_of_avoids (isoComp' I0) ?_ ?_ ?_
      · intro p hp
        have hpmin := (hCUTh_mem p hp).1
        haveI : p.IsPrime := hpmin.1.1
        rw [isoComp'_eq_isoComp hpmin]
        exact ⟨isoComp_isPrimary I0 p hpmin, radical_isoComp I0 p hpmin⟩
      · rw [← hJiInf]
        intro htop
        exact hJne (htop ▸ hilbPoly_top_eq_zero)
      · intro p hp hfrp
        apply (hCUTh_mem p hp).2.1
        rw [hI1eq]
        exact (mem_minimalPrimes_sup_span_singleton_iff (hCUTh_mem p hp).1).2 hfrp
    have hJdeg1 : 1 ≤ (hilbPoly (CUTh.inf (isoComp' I0))).natDegree := by
      rw [hJdeg]; omega
    have hfrhom : (f ⟨r, hr⟩).IsHomogeneous e :=
      (MvPolynomial.mem_homogeneousSubmodule e (f ⟨r, hr⟩)).mp hfe
    have hF := degQ_sup_span_regular (CUTh.inf (isoComp' I0)) hJhom hfe (by omega) hreg' hJdeg1
    -- Containment `J ⊔ span{f r} ≤ NEWh.inf`.
    have hcontain : ∀ m ∈ NEWh,
        CUTh.inf (isoComp' I0) ⊔ Ideal.span {f ⟨r, hr⟩} ≤ isoComp' I1 m := by
      intro m hm
      exact finset_inf_sup_span_le_isoComp'_I1 f hreg r hr (hNEWh_mem m hm).1 CUTh
        (fun q hq hqm => hbelow m hm q hq hqm)
    have hDcont : CUTh.inf (isoComp' I0) ⊔ Ideal.span {f ⟨r, hr⟩} ≤ NEWh.inf (isoComp' I1) :=
      Finset.le_inf (fun m hm => hcontain m hm)
    -- Homogeneity of the two ideals compared by `degQ_le_of_le`.
    have hAhom : IsHomog (CUTh.inf (isoComp' I0) ⊔ Ideal.span {f ⟨r, hr⟩}) :=
      isHomog_sup hJhom (isHomog_span_singleton hfrhom)
    have hBhom : IsHomog (NEWh.inf (isoComp' I1)) :=
      isHomog_finset_inf_isoComp' hhomI1 NEWh (fun m hm => (hNEWh_mem m hm).1)
    -- natDegree matching.
    have hBdeg : (hilbPoly (NEWh.inf (isoComp' I1))).natDegree = n - 1 - (h + 1) :=
      (hCsum.2 hne).1
    have hAdeg : (hilbPoly (CUTh.inf (isoComp' I0) ⊔ Ideal.span {f ⟨r, hr⟩})).natDegree
        = n - 1 - (h + 1) := by
      have h2 := hF.2
      rw [hJdeg] at h2
      omega
    have hEle : degQ (NEWh.inf (isoComp' I1))
        ≤ degQ (CUTh.inf (isoComp' I0) ⊔ Ideal.span {f ⟨r, hr⟩}) :=
      degQ_le_of_le hAhom hBhom hDcont (by rw [hBdeg, hAdeg])
    -- Assemble the chain.
    calc
      (∑ m ∈ NEWh, degQ (isoComp' I1 m))
          = degQ (NEWh.inf (isoComp' I1)) := hCsum.1.symm
      _ ≤ degQ (CUTh.inf (isoComp' I0) ⊔ Ideal.span {f ⟨r, hr⟩}) := hEle
      _ = (e : ℚ) * degQ (CUTh.inf (isoComp' I0)) := hF.1
      _ = (e : ℚ) * ∑ q ∈ CUTh, degQ (isoComp' I0 q) := by rw [hGsum.1]
  · -- Edge case `h + 1 = n`: every new prime has height `n`, so its degree is `0`.
    have hn : h + 1 = n := by omega
    have hLHS0 : (∑ m ∈ NEWh, degQ (isoComp' I1 m)) = 0 := by
      apply Finset.sum_eq_zero
      intro m hm
      obtain ⟨hmmin, _, hmht⟩ := hNEWh_mem m hm
      exact degQ_isoComp'_eq_zero_of_height_eq hhomI1 hmmin (by rw [hmht, hn])
    rw [hLHS0]
    exact mul_nonneg heQ hRHS_nonneg

/-- Per-height S3/S4 charge package for `divdegQ_charge_core`.

The estimate charges new minimal primes after adjoining `f r` to the cut
minimal primes of the previous ideal, using the associated-prime control above,
height-class additivity of `degQ`, and the one-step height increase. -/
theorem divdegQ_charge_core_s3_s4_residual [IsAlgClosed K] {C : ℕ}
    (f : Fin C → MvPolynomial (Fin n) K) (d : ℕ) (hd : 1 ≤ d)
    (hfh : ∀ i, ∃ e : ℕ, 1 ≤ e ∧ e ≤ d ∧ f i ∈ homogeneousSubmodule (Fin n) K e)
    (hreg : RegCond f) (r : ℕ) (hr : r < C)
    (hfrad : f ⟨r, hr⟩ ∉ (Ideal.span (f '' {i : Fin C | i.val < r})).radical) :
    (∑ p ∈ (Ideal.finite_minimalPrimes_of_isNoetherianRing (MvPolynomial (Fin n) K)
        (Ideal.span (f '' {i : Fin C | i.val < r + 1}))).toFinset \
        (Ideal.finite_minimalPrimes_of_isNoetherianRing (MvPolynomial (Fin n) K)
        (Ideal.span (f '' {i : Fin C | i.val < r}))).toFinset,
      degQ (isoComp' (Ideal.span (f '' {i : Fin C | i.val < r + 1})) p)
        / (d : ℚ) ^ p.height.toNat)
    ≤
    (∑ q ∈ (Ideal.finite_minimalPrimes_of_isNoetherianRing (MvPolynomial (Fin n) K)
        (Ideal.span (f '' {i : Fin C | i.val < r}))).toFinset \
        (Ideal.finite_minimalPrimes_of_isNoetherianRing (MvPolynomial (Fin n) K)
        (Ideal.span (f '' {i : Fin C | i.val < r + 1}))).toFinset,
      degQ (isoComp' (Ideal.span (f '' {i : Fin C | i.val < r})) q)
        / (d : ℚ) ^ q.height.toNat) := by
  classical
  set I0 := Ideal.span (f '' {i : Fin C | i.val < r}) with hI0def
  set I1 := Ideal.span (f '' {i : Fin C | i.val < r + 1}) with hI1def
  set FI0 := (Ideal.finite_minimalPrimes_of_isNoetherianRing
      (MvPolynomial (Fin n) K) I0).toFinset with hFI0def
  set FI1 := (Ideal.finite_minimalPrimes_of_isNoetherianRing
      (MvPolynomial (Fin n) K) I1).toFinset with hFI1def
  set NEW := FI1 \ FI0 with hNEWdef
  set CUT := FI0 \ FI1 with hCUTdef
  have hfhom : ∀ i, ∃ e : ℕ, f i ∈ homogeneousSubmodule (Fin n) K e := by
    intro i
    obtain ⟨e, _he1, _hed, hfe⟩ := hfh i
    exact ⟨e, hfe⟩
  obtain ⟨e, he1, hed, hfe⟩ := hfh ⟨r, hr⟩
  have hI0I1 : I0 ≤ I1 := by
    rw [hI0def, hI1def]
    apply Ideal.span_mono
    apply Set.image_mono
    intro i hi
    exact lt_trans hi (Nat.lt_succ_self r)
  have hhomI0 : IsHomog I0 := by
    rw [hI0def]
    exact isHomog_span_image f _ hfhom
  have hNEW_height_le : ∀ p ∈ NEW, p.height.toNat ≤ n := by
    intro p hpNEW
    have hpFI1 : p ∈ FI1 := (Finset.mem_sdiff.mp hpNEW).1
    have hpmin : p ∈ I1.minimalPrimes := by
      simpa [hFI1def] using hpFI1
    haveI : p.IsPrime := hpmin.1.1
    exact AristotleChargeBridge.height_toNat_le (K := K) (n := n) p
  have hCUT_height_le : ∀ p ∈ CUT, p.height.toNat ≤ n := by
    intro p hpCUT
    have hpFI0 : p ∈ FI0 := (Finset.mem_sdiff.mp hpCUT).1
    have hpmin : p ∈ I0.minimalPrimes := by
      simpa [hFI0def] using hpFI0
    haveI : p.IsPrime := hpmin.1.1
    exact AristotleChargeBridge.height_toNat_le (K := K) (n := n) p
  have hNEW_height_pos : ∀ p ∈ NEW, 0 < p.height.toNat := by
    intro p hpNEW
    have hpFI1 : p ∈ FI1 := (Finset.mem_sdiff.mp hpNEW).1
    have hpnotFI0 : p ∉ FI0 := (Finset.mem_sdiff.mp hpNEW).2
    have hpminI1 : p ∈ I1.minimalPrimes := by
      simpa [hFI1def] using hpFI1
    have hpnotminI0 : p ∉ I0.minimalPrimes := by
      intro hpminI0
      exact hpnotFI0 (by simpa [hFI0def] using hpminI0)
    haveI : p.IsPrime := hpminI1.1.1
    obtain ⟨q, hqmin, hqp⟩ := Ideal.exists_minimalPrimes_le (I := I0) (J := p)
      (hI0I1.trans hpminI1.1.2)
    obtain ⟨_hfr_not_q, hheight⟩ :=
      new_prime_cut_below f hfhom r hr hpminI1 hpnotminI0 hqmin hqp
    have hqheight_ne_top : q.height ≠ ⊤ := by
      have hle := Ideal.height_le_ringKrullDim_of_ne_top (I := q) hqmin.1.1.ne_top
      rw [AristotleDimensionFormula.mvPoly_ringKrullDim (K := K) n] at hle
      intro htop
      rw [htop] at hle
      exact ENat.coe_ne_top n (WithBot.coe_eq_top.mp (top_le_iff.mp hle))
    have htoNat : (q.height + 1).toNat = q.height.toNat + 1 := by
      simpa using ENat.toNat_add hqheight_ne_top (by simp : (1 : ℕ∞) ≠ ⊤)
    rw [hheight, htoNat]
    omega
  let newDeg : ℕ → ℚ := fun h =>
    ∑ p ∈ NEW.filter (fun p => p.height.toNat = h + 1),
      degQ (isoComp' I1 p)
  let cutDeg : ℕ → ℚ := fun h =>
    ∑ p ∈ CUT.filter (fun p => p.height.toNat = h),
      degQ (isoComp' I0 p)
  have hclass : ∀ h : ℕ, newDeg h ≤ (e : ℚ) * cutDeg h := by
    intro h
    simpa [newDeg, cutDeg, hI0def, hI1def, hFI0def, hFI1def, hNEWdef, hCUTdef]
      using divdegQ_class_charge f hfhom hreg r hr he1 hfe h
  have hcutDeg_nonneg : ∀ h : ℕ, 0 ≤ cutDeg h := by
    intro h
    apply Finset.sum_nonneg
    intro p hp
    have hpCUT : p ∈ CUT := (Finset.mem_filter.mp hp).1
    have hpFI0 : p ∈ FI0 := (Finset.mem_sdiff.mp hpCUT).1
    have hpmin : p ∈ I0.minimalPrimes := by
      simpa [hFI0def] using hpFI0
    exact degQ_nonneg (isHomog_isoComp' hhomI0 hpmin)
  have hclass_weighted :
      ∀ h ∈ Finset.range (n + 1),
        newDeg h / (d : ℚ) ^ (h + 1) ≤ cutDeg h / (d : ℚ) ^ h := by
    intro h _hh
    have hdpos : (0 : ℚ) < d := by exact_mod_cast hd
    have hden1 : (0 : ℚ) < (d : ℚ) ^ (h + 1) := pow_pos hdpos _
    have hden0 : (0 : ℚ) < (d : ℚ) ^ h := pow_pos hdpos _
    have hfirst :
        newDeg h / (d : ℚ) ^ (h + 1) ≤
          ((e : ℚ) * cutDeg h) / (d : ℚ) ^ (h + 1) := by
      exact div_le_div_of_nonneg_right (hclass h) (le_of_lt hden1)
    have hsecond :
        ((e : ℚ) * cutDeg h) / (d : ℚ) ^ (h + 1) ≤
          cutDeg h / (d : ℚ) ^ h := by
      rw [div_le_div_iff₀ hden1 hden0]
      rw [pow_succ]
      have hedQ : (e : ℚ) ≤ d := by exact_mod_cast hed
      have hS : 0 ≤ cutDeg h := hcutDeg_nonneg h
      have hmul :
          ((e : ℚ) * cutDeg h) * (d : ℚ) ^ h ≤
            ((d : ℚ) * cutDeg h) * (d : ℚ) ^ h :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hedQ hS) (le_of_lt hden0)
      ring_nf at hmul ⊢
      exact hmul
    exact le_trans hfirst hsecond
  have hLHS_partition :
      (∑ p ∈ NEW, degQ (isoComp' I1 p) / (d : ℚ) ^ p.height.toNat) =
        ∑ h ∈ Finset.range (n + 1), newDeg h / (d : ℚ) ^ (h + 1) := by
    rw [eq_comm]
    simp_rw [newDeg, Finset.sum_div, Finset.sum_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro p hpNEW
    have hpos : 0 < p.height.toNat := hNEW_height_pos p hpNEW
    have hle : p.height.toNat ≤ n := hNEW_height_le p hpNEW
    have hidx : p.height.toNat - 1 ∈ Finset.range (n + 1) := by
      rw [Finset.mem_range]
      omega
    rw [Finset.sum_eq_single_of_mem (p.height.toNat - 1) hidx]
    · have hsucc : p.height.toNat = p.height.toNat - 1 + 1 := by omega
      rw [if_pos hsucc, ← hsucc]
    · intro h hh hne
      have hneq : ¬p.height.toNat = h + 1 := by
        intro hheight
        have : h = p.height.toNat - 1 := by omega
        exact hne this
      rw [if_neg hneq]
  have hRHS_partition :
      (∑ p ∈ CUT, degQ (isoComp' I0 p) / (d : ℚ) ^ p.height.toNat) =
        ∑ h ∈ Finset.range (n + 1), cutDeg h / (d : ℚ) ^ h := by
    rw [eq_comm]
    simp_rw [cutDeg, Finset.sum_div, Finset.sum_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro p hpCUT
    have hle : p.height.toNat ≤ n := hCUT_height_le p hpCUT
    have hidx : p.height.toNat ∈ Finset.range (n + 1) := by
      rw [Finset.mem_range]
      omega
    rw [Finset.sum_eq_single_of_mem p.height.toNat hidx]
    · simp
    · intro h hh hne
      have hneq : ¬p.height.toNat = h := by
        intro hheight
        exact hne hheight.symm
      simp [hneq]
  have hsum_le :
      (∑ h ∈ Finset.range (n + 1), newDeg h / (d : ℚ) ^ (h + 1)) ≤
        ∑ h ∈ Finset.range (n + 1), cutDeg h / (d : ℚ) ^ h := by
    exact Finset.sum_le_sum hclass_weighted
  have hmain :
      (∑ p ∈ NEW, degQ (isoComp' I1 p) / (d : ℚ) ^ p.height.toNat) ≤
        ∑ p ∈ CUT, degQ (isoComp' I0 p) / (d : ℚ) ^ p.height.toNat := by
    calc
      (∑ p ∈ NEW, degQ (isoComp' I1 p) / (d : ℚ) ^ p.height.toNat)
          = ∑ h ∈ Finset.range (n + 1), newDeg h / (d : ℚ) ^ (h + 1) :=
            hLHS_partition
      _ ≤ ∑ h ∈ Finset.range (n + 1), cutDeg h / (d : ℚ) ^ h := hsum_le
      _ = ∑ p ∈ CUT, degQ (isoComp' I0 p) / (d : ℚ) ^ p.height.toNat :=
            hRHS_partition.symm
  simpa [hI0def, hI1def, hFI0def, hFI1def, hNEWdef, hCUTdef] using hmain

/-- S4-core: the charge inequality in the essential case where `r < C` and the
new generator `f r` avoids the radical of `I_r` (so it genuinely cuts).

This is the research-scale heart of Lazard's strong Bézout inequality.
Everything else in the recurrence (`divdegQ_step_le`, `divdegQ_le_one`,
`homog_relevant_minimalPrimes_ncard_le`) is proved and reduces to this one
inequality.

Intended proof (S2/S3/S4). Let `I0 = span(f''{i<r})`, `fr = f r`,
`I1 = I0 ⊔ span{fr}`. The RHS sums over `CUT = FI0 \ FI1` and the LHS over
`NEW = FI1 \ FI0`. By `mem_minimalPrimes_sup_span_singleton_iff`,
`CUT = {q ∈ I0.minimalPrimes : fr ∉ q}` (S2). Put `J' = ⨅ q ∈ CUT, isoComp I0 q`;
then `fr` is a nonzerodivisor mod `J'` (`isSMulRegular_inf_of_avoids`), and the
charge follows from `degQ_sup_span_regular` (`degQ (J' ⊔ span{fr}) = e · degQ J'`)
and iterated `degQ_inf_add`, split over height classes of `CUT`.

OBSTRUCTION (S3, the localized U-induction). The charge requires, at every new
minimal prime `m ∈ NEW`, the *local agreement* `(I0)_m = (J')_m` — i.e. `I0` has
no embedded associated prime below `m` beyond the isolated components collected
in `J'`. This is exactly where `RegCond` is used: localizing the RegCond prefix
`f_0, …, f_{r-1}` at `m` yields (via `grade_descent`) a weakly regular sequence,
and `grade_ge_height` supplies the depth needed to force `m R_m ∉ Ass`, killing
embedded components at `m`. Formalizing this step needs the transport between
`R_m ∕ (J R_m)` and iterated `QuotSMulTop` (cf. `GradeHeight.lean` /
`GenericSequence.lean`) and the localization behaviour of associated primes; it
is the deep commutative-algebra kernel that has not yet been discharged here. -/
theorem divdegQ_charge_core [IsAlgClosed K] {C : ℕ}
    (f : Fin C → MvPolynomial (Fin n) K) (d : ℕ) (hd : 1 ≤ d)
    (hfh : ∀ i, ∃ e : ℕ, 1 ≤ e ∧ e ≤ d ∧ f i ∈ homogeneousSubmodule (Fin n) K e)
    (hreg : RegCond f) (r : ℕ) (hr : r < C)
    (hfrad : f ⟨r, hr⟩ ∉ (Ideal.span (f '' {i : Fin C | i.val < r})).radical) :
    (∑ p ∈ (Ideal.finite_minimalPrimes_of_isNoetherianRing (MvPolynomial (Fin n) K)
        (Ideal.span (f '' {i : Fin C | i.val < r + 1}))).toFinset \
        (Ideal.finite_minimalPrimes_of_isNoetherianRing (MvPolynomial (Fin n) K)
        (Ideal.span (f '' {i : Fin C | i.val < r}))).toFinset,
      degQ (isoComp' (Ideal.span (f '' {i : Fin C | i.val < r + 1})) p)
        / (d : ℚ) ^ p.height.toNat)
    ≤
    (∑ q ∈ (Ideal.finite_minimalPrimes_of_isNoetherianRing (MvPolynomial (Fin n) K)
        (Ideal.span (f '' {i : Fin C | i.val < r}))).toFinset \
        (Ideal.finite_minimalPrimes_of_isNoetherianRing (MvPolynomial (Fin n) K)
        (Ideal.span (f '' {i : Fin C | i.val < r + 1}))).toFinset,
      degQ (isoComp' (Ideal.span (f '' {i : Fin C | i.val < r})) q)
        / (d : ℚ) ^ q.height.toNat) := by
  exact divdegQ_charge_core_s3_s4_residual f d hd hfh hreg r hr hfrad

/-- S4 (the charge): the *new* minimal primes of `I_{r+1}` — those not minimal
over `I_r` — contribute, in aggregate, no more to the divided degree than the
*cut* minimal primes of `I_r` — those no longer minimal over `I_{r+1}`. This is
the deep step of the Lazard recurrence: it packages the classification (S2), the
localized U-induction (S3), and the exact degree charge (`degQ_sup_span_regular`
+ `degQ_inf_add`). -/
theorem divdegQ_charge [IsAlgClosed K] {C : ℕ}
    (f : Fin C → MvPolynomial (Fin n) K) (d : ℕ) (hd : 1 ≤ d)
    (hfh : ∀ i, ∃ e : ℕ, 1 ≤ e ∧ e ≤ d ∧ f i ∈ homogeneousSubmodule (Fin n) K e)
    (hreg : RegCond f) (r : ℕ) :
    (∑ p ∈ (Ideal.finite_minimalPrimes_of_isNoetherianRing (MvPolynomial (Fin n) K)
        (Ideal.span (f '' {i : Fin C | i.val < r + 1}))).toFinset \
        (Ideal.finite_minimalPrimes_of_isNoetherianRing (MvPolynomial (Fin n) K)
        (Ideal.span (f '' {i : Fin C | i.val < r}))).toFinset,
      degQ (isoComp' (Ideal.span (f '' {i : Fin C | i.val < r + 1})) p)
        / (d : ℚ) ^ p.height.toNat)
    ≤
    (∑ q ∈ (Ideal.finite_minimalPrimes_of_isNoetherianRing (MvPolynomial (Fin n) K)
        (Ideal.span (f '' {i : Fin C | i.val < r}))).toFinset \
        (Ideal.finite_minimalPrimes_of_isNoetherianRing (MvPolynomial (Fin n) K)
        (Ideal.span (f '' {i : Fin C | i.val < r + 1}))).toFinset,
      degQ (isoComp' (Ideal.span (f '' {i : Fin C | i.val < r})) q)
        / (d : ℚ) ^ q.height.toNat) := by
  classical
  -- The two index finsets coincide exactly when the two ideals have equal
  -- minimal primes; in that (degenerate) case both diff-sums vanish.
  have htriv : ∀ {A B : Ideal (MvPolynomial (Fin n) K)},
      A.minimalPrimes = B.minimalPrimes →
      (Ideal.finite_minimalPrimes_of_isNoetherianRing (MvPolynomial (Fin n) K) A).toFinset =
      (Ideal.finite_minimalPrimes_of_isNoetherianRing (MvPolynomial (Fin n) K) B).toFinset := by
    intro A B h
    ext p
    rw [Set.Finite.mem_toFinset, Set.Finite.mem_toFinset, h]
  by_cases hr : r < C
  · by_cases hfrad : f ⟨r, hr⟩ ∈ (Ideal.span (f '' {i : Fin C | i.val < r})).radical
    · -- `f r` lies in the radical of `I_r`, so `I_{r+1}` has the same radical,
      -- hence the same minimal primes: both diff-sums are empty.
      have hset : {i : Fin C | i.val < r + 1} = insert (⟨r, hr⟩ : Fin C) {i : Fin C | i.val < r} := by
        ext i
        simp only [Set.mem_setOf_eq, Set.mem_insert_iff]
        constructor
        · intro hi; rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | h
          · exact Or.inr h
          · exact Or.inl (Fin.ext h)
        · rintro (rfl | h)
          · exact Nat.lt_succ_self r
          · exact Nat.lt_succ_of_lt h
      have hI1 : Ideal.span (f '' {i : Fin C | i.val < r + 1}) =
          Ideal.span (f '' {i : Fin C | i.val < r}) ⊔ Ideal.span {f ⟨r, hr⟩} := by
        rw [hset, Set.image_insert_eq, Ideal.span_insert, sup_comm]
      have hrad : (Ideal.span (f '' {i : Fin C | i.val < r + 1})).radical =
          (Ideal.span (f '' {i : Fin C | i.val < r})).radical := by
        rw [hI1]
        apply le_antisymm
        · calc
            (Ideal.span (f '' {i : Fin C | i.val < r}) ⊔ Ideal.span {f ⟨r, hr⟩}).radical
                ≤ ((Ideal.span (f '' {i : Fin C | i.val < r})).radical).radical := by
                  apply Ideal.radical_mono
                  apply sup_le Ideal.le_radical
                  rw [Ideal.span_le, Set.singleton_subset_iff]; exact hfrad
            _ = (Ideal.span (f '' {i : Fin C | i.val < r})).radical := Ideal.radical_idem _
        · exact Ideal.radical_mono le_sup_left
      have hmp := minimalPrimes_eq_of_radical_eq hrad
      rw [htriv hmp]
      simp
    · exact divdegQ_charge_core f d hd hfh hreg r hr hfrad
  · -- `r ≥ C`: both index sets are all of `Fin C`, so the ideals are equal.
    have hset : {i : Fin C | i.val < r + 1} = {i : Fin C | i.val < r} := by
      ext i
      simp only [Set.mem_setOf_eq]
      have hi := i.is_lt
      have hCr : C ≤ r := Nat.le_of_not_lt hr
      omega
    rw [hset]

/-- Inductive step of the Lazard strong-Bézout recurrence: adjoining one more
generator does not increase the divided degree.

The minimal primes of `I_{r+1}` split into the *frozen* ones (also minimal over
`I_r`) and the *new* ones; the minimal primes of `I_r` split into the frozen ones
and the *cut* ones (no longer minimal over `I_{r+1}`). The frozen terms do not
increase (`divdegQ_frozen_term_le`, from `isoComp_mono` + `degQ_le_of_le` with
equal Hilbert-polynomial degree via `hilbPoly_natDegree_eq_of_radical_eq`); the
aggregate new-vs-cut inequality is `divdegQ_charge`. This lemma is now the pure
Finset assembly of those two facts (an inter/diff split of the two index sets). -/
theorem divdegQ_step_le [IsAlgClosed K] {C : ℕ}
    (f : Fin C → MvPolynomial (Fin n) K) (d : ℕ) (hd : 1 ≤ d)
    (hfh : ∀ i, ∃ e : ℕ, 1 ≤ e ∧ e ≤ d ∧ f i ∈ homogeneousSubmodule (Fin n) K e)
    (hreg : RegCond f) (r : ℕ) :
    divdegQ (Ideal.span (f '' {i : Fin C | i.val < r + 1})) d ≤
      divdegQ (Ideal.span (f '' {i : Fin C | i.val < r})) d := by
  classical
  set I0 := Ideal.span (f '' {i : Fin C | i.val < r}) with hI0def
  set I1 := Ideal.span (f '' {i : Fin C | i.val < r + 1}) with hI1def
  have hI0I1 : I0 ≤ I1 := by
    apply Ideal.span_mono
    apply Set.image_mono
    intro i hi; exact lt_trans hi (Nat.lt_succ_self r)
  have hhomI0 : IsHomog I0 := isHomog_span_image f _ (fun i => (hfh i).imp (fun e h => h.2.2))
  have hhomI1 : IsHomog I1 := isHomog_span_image f _ (fun i => (hfh i).imp (fun e h => h.2.2))
  set FI0 := (Ideal.finite_minimalPrimes_of_isNoetherianRing (MvPolynomial (Fin n) K) I0).toFinset
    with hFI0def
  set FI1 := (Ideal.finite_minimalPrimes_of_isNoetherianRing (MvPolynomial (Fin n) K) I1).toFinset
    with hFI1def
  simp only [divdegQ]
  rw [← Finset.sum_inter_add_sum_diff FI1 FI0
      (fun p => degQ (isoComp' I1 p) / (d : ℚ) ^ p.height.toNat),
    ← Finset.sum_inter_add_sum_diff FI0 FI1
      (fun p => degQ (isoComp' I0 p) / (d : ℚ) ^ p.height.toNat)]
  rw [Finset.inter_comm FI0 FI1]
  apply add_le_add
  · -- frozen part, termwise
    apply Finset.sum_le_sum
    intro p hp
    rw [Finset.mem_inter] at hp
    have hpI1 : p ∈ I1.minimalPrimes := by
      have := hp.1; rwa [hFI1def, Set.Finite.mem_toFinset] at this
    have hpI0 : p ∈ I0.minimalPrimes := by
      have := hp.2; rwa [hFI0def, Set.Finite.mem_toFinset] at this
    exact divdegQ_frozen_term_le hhomI0 hhomI1 hI0I1 hpI0 hpI1 d
  · -- charge part
    exact divdegQ_charge f d hd hfh hreg r

/-- W4 core: the strong Bézout inequality for the uniform divided degree. -/
theorem divdegQ_le_one [IsAlgClosed K] {C : ℕ}
    (f : Fin C → MvPolynomial (Fin n) K) (d : ℕ) (hd : 1 ≤ d)
    (hfh : ∀ i, ∃ e : ℕ, 1 ≤ e ∧ e ≤ d ∧ f i ∈ homogeneousSubmodule (Fin n) K e)
    (hreg : RegCond f)
    (hne : Ideal.span (Set.range f) ≠ ⊥) :
    divdegQ (Ideal.span (Set.range f)) d ≤ 1 := by
  have key : ∀ r : ℕ,
      divdegQ (Ideal.span (f '' {i : Fin C | i.val < r})) d ≤ 1 := by
    intro r
    induction r with
    | zero =>
        have hempty : {i : Fin C | i.val < 0} = (∅ : Set (Fin C)) := by
          ext i; simp
        rw [hempty, Set.image_empty, Ideal.span_empty]
        exact divdegQ_bot_le_one d
    | succ r ih => exact le_trans (divdegQ_step_le f d hd hfh hreg r) ih
  have huniv : Ideal.span (f '' {i : Fin C | i.val < C}) = Ideal.span (Set.range f) := by
    have : {i : Fin C | i.val < C} = (Set.univ : Set (Fin C)) := by
      ext i; simp [i.is_lt]
    rw [this, Set.image_univ]
  rw [← huniv]
  exact key C

/-
The span of homogeneous generators is a homogeneous ideal.
-/
theorem isHomog_span_range_of_homog {C : ℕ} (g : Fin C → MvPolynomial (Fin n) K)
    (hg : ∀ i, ∃ e : ℕ, g i ∈ homogeneousSubmodule (Fin n) K e) :
    IsHomog (Ideal.span (Set.range g)) := by
  convert IsHomog_of_isHomogeneous _;
  convert Ideal.homogeneous_span ( homogeneousSubmodule ( Fin n ) K ) ( Set.range g ) ?_;
  rintro _ ⟨ i, rfl ⟩ ; exact ⟨ _, hg i |> Classical.choose_spec ⟩ ;

/-
Height bound for a relevant minimal prime: at most `min C (n-1)`.
-/
theorem height_toNat_le_min {C : ℕ} (g : Fin C → MvPolynomial (Fin n) K)
    {p : Ideal (MvPolynomial (Fin n) K)}
    (hp : p ∈ (Ideal.span (Set.range g)).minimalPrimes)
    (hg : ∀ i, ∃ e : ℕ, g i ∈ homogeneousSubmodule (Fin n) K e)
    (hpv : p ≠ varsIdeal) :
    p.height.toNat ≤ min C (n - 1) := by
  -- Since p is a proper subset of varsIdeal, its height is strictly less than n.
  have h_height_lt : p.height < n := by
    have h_lt : p < varsIdeal := by
      refine' lt_of_le_of_ne _ hpv;
      convert minimalPrimes_le_varsIdeal ( Ideal.span ( Set.range g ) ) ( isHomog_span_range_of_homog g hg ) hp;
    convert Ideal.primeHeight_strict_mono h_lt;
    convert Ideal.height_eq_primeHeight;
    any_goals exact MvPolynomial ( Fin n ) K;
    all_goals try infer_instance;
    any_goals exact varsIdeal_isMaximal.isPrime;
    any_goals exact hp.1.1;
    · constructor <;> intro h <;> simp_all +decide [ Ideal.height ];
      · convert Ideal.height_eq_primeHeight;
      · convert h p;
    · rw [ ← Ideal.height_eq_primeHeight ];
      convert ParamSystem.height_maximal n varsIdeal |> Eq.symm;
      exact varsIdeal_isMaximal;
  have h_height_le_C : p.height ≤ C := by
    refine' le_trans _ ( Nat.cast_le.mpr ( show ( Set.ncard ( Set.range g ) : ℕ ) ≤ C from _ ) );
    · convert Ideal.height_le_card_of_mem_minimalPrimes_span ( Set.finite_range g ) hp;
    · exact le_trans ( Set.ncard_le_ncard ( show Set.range g ⊆ Set.image g Set.univ from Set.range_subset_iff.mpr fun i => Set.mem_image_of_mem _ ( Set.mem_univ _ ) ) ) ( Set.ncard_image_le ( Set.toFinite _ ) ) |> le_trans <| by simp +decide [ Set.ncard_univ ] ;
  cases h : p.height <;> simp_all +decide [ Nat.lt_succ_iff ];
  exact Nat.le_pred_of_lt h_height_lt

/-
Lower bound on the degree of the isolated component at a relevant minimal
prime.
-/
theorem one_le_degQ_isoComp' [Infinite K] {C : ℕ} (g : Fin C → MvPolynomial (Fin n) K)
    {p : Ideal (MvPolynomial (Fin n) K)}
    (hp : p ∈ (Ideal.span (Set.range g)).minimalPrimes)
    (hg : ∀ i, ∃ e : ℕ, g i ∈ homogeneousSubmodule (Fin n) K e)
    (hpv : p ≠ varsIdeal) :
    1 ≤ degQ (isoComp' (Ideal.span (Set.range g)) p) := by
  by_cases h : p.IsPrime;
  · -- Since `p` is prime, `isoComp' I p = isoComp I p` (unfold `isoComp'`, `dif_pos hpp`).
    -- Set `J := isoComp I p`.
    set J := isoComp (Ideal.span (Set.range g)) p
    have hJhom : IsHomog J := isoComp_isHomog (Ideal.span (Set.range g)) p (isHomog_span_range_of_homog g hg) hp;
    convert one_le_degQ J hJhom _;
    · exact dif_pos h;
    · intro hJ0
      have hJne_top : J ≠ ⊤ := by
        have hJle_p : J ≤ p := by
          convert radical_isoComp ( Ideal.span ( Set.range g ) ) p hp ▸ Ideal.le_radical;
        exact fun h => hJle_p |> fun h' => by simp_all +decide [ Ideal.IsPrime.ne_top ] ;
      have hJfin : FiniteDimensional K (MvPolynomial (Fin n) K ⧸ J) := by
        have := HF_poly_natDegree J hJhom hJne_top ( hilbPoly J ) ( hilbPoly_spec J hJhom ) ; aesop;
      have hpfin : FiniteDimensional K (MvPolynomial (Fin n) K ⧸ p) := by
        have hpfin : J ≤ p := by
          convert Ideal.le_radical using 1;
          exact Eq.symm ( radical_isoComp _ _ hp );
        have hpfin : ∃ (f : (MvPolynomial (Fin n) K ⧸ J) →ₗ[K] (MvPolynomial (Fin n) K ⧸ p)), Function.Surjective ⇑f := by
          refine' ⟨ _, _ ⟩;
          refine' { .. };
          exact fun x => Ideal.Quotient.factor hpfin x;
          all_goals simp +decide [ Function.Surjective ];
          · intro m x; induction x using Quotient.inductionOn' ; aesop;
          · exact fun b => by rcases Ideal.Quotient.mk_surjective b with ⟨ x, rfl ⟩ ; exact ⟨ Ideal.Quotient.mk J x, rfl ⟩ ;
        exact FiniteDimensional.of_surjective _ hpfin.choose_spec
      have hpfield : IsField (MvPolynomial (Fin n) K ⧸ p) := by
        convert isField_of_isIntegral_of_isField' (Field.toIsField K) using 1;
        all_goals infer_instance
      have hpmax : p.IsMaximal := by
        convert Ideal.Quotient.maximal_of_isField _ hpfield
      have hp_eq_varsIdeal : p = varsIdeal := by
        exact Ideal.IsMaximal.eq_of_le hpmax (varsIdeal_isMaximal.ne_top) (minimalPrimes_le_varsIdeal _ (isHomog_span_range_of_homog g hg) hp)
      contradiction;
  · exact False.elim ( h ( Ideal.minimalPrimes_isPrime hp ) )

/-
Counting arithmetic: if the nonnegative terms over `F` sum to at most `1`,
and each term over a subfamily `Rel` is at least `1 / d ^ m`, then `Rel` has at
most `d ^ m` elements.
-/
theorem card_le_of_sum_div_pow {R : Type*} (F Rel : Finset R) (hsub : Rel ⊆ F)
    (term : R → ℚ) (hnonneg : ∀ p ∈ F, 0 ≤ term p) (m d : ℕ) (hd : 1 ≤ d)
    (hlb : ∀ p ∈ Rel, 1 / (d : ℚ) ^ m ≤ term p) (hsum : ∑ p ∈ F, term p ≤ 1) :
    Rel.card ≤ d ^ m := by
  have h_card_le : (Rel.card : ℚ) / (d : ℚ) ^ m ≤ ∑ p ∈ Rel, term p := by
    simpa using Finset.sum_le_sum hlb;
  exact_mod_cast ( by rw [ div_le_iff₀ ( by positivity ) ] at h_card_le; nlinarith [ show ( ∑ p ∈ Rel, term p : ℚ ) ≤ 1 by exact hsum.trans' ( Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => hnonneg _ ‹_› ), show ( d : ℚ ) ^ m > 0 by positivity ] : ( Rel.card : ℚ ) ≤ d ^ m )

/-
The homogeneous component count: minimal primes other than the variables
ideal number at most `d ^ min(C, n−1)`.
-/
theorem homog_relevant_minimalPrimes_ncard_le [IsAlgClosed K] {C : ℕ}
    (f : Fin C → MvPolynomial (Fin n) K) (d : ℕ) (hd : 1 ≤ d)
    (hfh : ∀ i, ∃ e : ℕ, 1 ≤ e ∧ e ≤ d ∧ f i ∈ homogeneousSubmodule (Fin n) K e) :
    Set.ncard {p ∈ (Ideal.span (Set.range f)).minimalPrimes |
        p ≠ varsIdeal (K := K) (n := n)} ≤ d ^ min C (n - 1) := by
  by_cases h : Ideal.span ( Set.range f ) = ⊥ <;> simp_all +decide [ Set.ncard_def ];
  · refine' le_trans ( Set.ncard_le_ncard <| show { p : Ideal ( MvPolynomial ( Fin n ) K ) | p ∈ ( ⊥ : Ideal ( MvPolynomial ( Fin n ) K ) ).minimalPrimes ∧ ¬p = varsIdeal } ⊆ { ⊥ } from _ ) _ <;> norm_num [ Set.ncard_singleton ];
    · simp +decide [ Ideal.minimalPrimes ];
      intro p hp hp_ne_vars
      have hp_zero : p = ⊥ := by
        have := hp.1.1; simp_all +decide [ Ideal.isPrime_iff ] ;
        have := hp.2 ( show ¬⊥ = ⊤ ∧ ∀ { x y : MvPolynomial ( Fin n ) K }, x * y ∈ ⊥ → x ∈ ⊥ ∨ y ∈ ⊥ from ⟨ by simp +decide [ Ideal.eq_top_iff_one ], by simp +decide [ Ideal.mem_bot ] ⟩ ) ; simp_all +decide [ Ideal.eq_top_iff_one ] ;
      exact hp_zero;
    · exact Nat.one_le_pow _ _ hd;
  · obtain ⟨g, hg⟩ := exists_regCond f d hfh;
    have h_divdegQ_le_one : divdegQ (Ideal.span (Set.range g)) d ≤ 1 := by
      apply divdegQ_le_one g d hd;
      · intro i; specialize hg; rcases hg.2.1 i with ( h | ⟨ e, he₁, he₂, he₃ ⟩ ) <;> [ exact ⟨ 1, by decide, by linarith, by simp +decide [ h ] ⟩ ; exact ⟨ e, he₁, he₂, he₃ ⟩ ] ;
      · exact hg.2.2;
      · grind +revert;
    have h_card_le : ∀ p ∈ (Ideal.span (Set.range g)).minimalPrimes, p ≠ varsIdeal → 1 / (d : ℚ) ^ (min C (n - 1)) ≤ degQ (isoComp' (Ideal.span (Set.range g)) p) / (d : ℚ) ^ (p.height.toNat) := by
      intro p hp hpv
      have h_degQ_ge_one : 1 ≤ degQ (isoComp' (Ideal.span (Set.range g)) p) := by
        apply one_le_degQ_isoComp' g hp (fun i => by
          cases' hg.2.1 i with hi hi <;> [ exact ⟨ 0, by simp +decide [ hi ] ⟩ ; exact hi.imp fun e he => he.2.2 ]) hpv
      have h_height_le_min : p.height.toNat ≤ min C (n - 1) := by
        apply height_toNat_le_min g hp (fun i => by
          rcases hg.2.1 i with ( h | ⟨ e, he₁, he₂, he₃ ⟩ ) <;> [ exact ⟨ 0, by simp +decide [ h ] ⟩ ; exact ⟨ e, he₃ ⟩ ]) hpv
      have h_term_ge_one_div_d_pow_min : 1 / (d : ℚ) ^ (min C (n - 1)) ≤ degQ (isoComp' (Ideal.span (Set.range g)) p) / (d : ℚ) ^ (p.height.toNat) := by
        gcongr ; norm_cast
      exact h_term_ge_one_div_d_pow_min;
    have h_card_le : ∀ (s : Finset (Ideal (MvPolynomial (Fin n) K))), (∀ p ∈ s, p ∈ (Ideal.span (Set.range g)).minimalPrimes ∧ p ≠ varsIdeal) → s.card ≤ d ^ min C (n - 1) := by
      intros s hs
      have h_sum_le_one : ∑ p ∈ s, degQ (isoComp' (Ideal.span (Set.range g)) p) / (d : ℚ) ^ (p.height.toNat) ≤ 1 := by
        refine' le_trans _ h_divdegQ_le_one;
        refine' Finset.sum_le_sum_of_subset_of_nonneg _ _;
        · intro p hp; specialize hs p hp; aesop;
        · intro p hp hps
          have h_degQ_nonneg : 0 ≤ degQ (isoComp' (Ideal.span (Set.range g)) p) := by
            have h_degQ_nonneg : IsHomog (isoComp' (Ideal.span (Set.range g)) p) := by
              have h_isoComp_homog : IsHomog (Ideal.span (Set.range g)) := by
                apply isHomog_span_range_of_homog;
                intro i
                obtain hi | ⟨ e, he₁, he₂, he₃ ⟩ := hg.2.1 i
                · exact ⟨ 0, by simp [ hi ] ⟩
                · exact ⟨ e, he₃ ⟩;
              by_cases hprime : p.IsPrime <;> simp_all +decide [ isoComp' ];
              · exact isoComp_isHomog _ _ h_isoComp_homog ‹_›;
              · have hp_min : p ∈ (Ideal.span (Set.range g)).minimalPrimes := by
                  simpa [hg.1] using hp
                exact False.elim (hprime (Ideal.minimalPrimes_isPrime hp_min));
            exact degQ_eq_natCast _ h_degQ_nonneg |> fun ⟨ D, hD ⟩ => hD.symm ▸ Nat.cast_nonneg _
          exact div_nonneg h_degQ_nonneg (pow_nonneg (Nat.cast_nonneg d) (p.height.toNat));
      have := card_le_of_sum_div_pow s s ( Finset.Subset.refl s ) ( fun p => degQ ( isoComp' ( Ideal.span ( Set.range g ) ) p ) / ( d : ℚ ) ^ p.height.toNat ) ?_ ( min C ( n - 1 ) ) d hd ?_ h_sum_le_one;
      · exact this;
      · exact fun p hp => le_trans ( by positivity ) ( h_card_le p ( hs p hp |>.1 ) ( hs p hp |>.2 ) );
      · exact fun p hp => h_card_le p ( hs p hp |>.1 ) ( hs p hp |>.2 );
    rw [ ← hg.1 ];
    have h_finite : Set.Finite {p : Ideal (MvPolynomial (Fin n) K) | p ∈ (Ideal.span (Set.range g)).minimalPrimes ∧ ¬p = varsIdeal} := by
      exact Set.Finite.subset ( Set.finite_coe_iff.mp ( Ideal.finite_minimalPrimes_of_isNoetherianRing _ _ ) ) fun p hp => hp.1;
    rw [ h_finite.encard_eq_coe_toFinset_card ] ; aesop

end
