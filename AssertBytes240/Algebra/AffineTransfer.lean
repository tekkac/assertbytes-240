import AssertBytes240.Algebra.HilbertFunction

/-!
# T2-W5 — the affine transfer via homogenization

Defines `homog`, `dehomog`, and `idealHomog`, then proves the minimal-prime
correspondence needed to move the homogeneous component bound in `n+1`
variables back to the affine statement in `n` variables.
-/

open MvPolynomial

noncomputable section

attribute [local instance] MvPolynomial.gradedAlgebra

variable {K : Type*} [Field K] {n : ℕ}

/-- Fixed-degree `x₀`-homogenization.  The public `homog` below is the
special case where the degree is `f.totalDegree`. -/
def homogOfDegree (D : ℕ) (f : MvPolynomial (Fin n) K) :
    MvPolynomial (Fin (n + 1)) K :=
  ∑ e ∈ Finset.range (D + 1),
    (X (0 : Fin (n + 1))) ^ (D - e) *
      rename Fin.succ (homogeneousComponent e f)

/-- `x₀`-homogenization of an affine polynomial (degree-stratified sum). -/
def homog (f : MvPolynomial (Fin n) K) : MvPolynomial (Fin (n + 1)) K :=
  homogOfDegree f.totalDegree f

/-- Dehomogenization: `x₀ ↦ 1`, `x_{i+1} ↦ x_i`. -/
def dehomog : MvPolynomial (Fin (n + 1)) K →ₐ[K] MvPolynomial (Fin n) K :=
  aeval (Fin.cases 1 X)

/-- Homogenization of an ideal. -/
def idealHomog (I : Ideal (MvPolynomial (Fin n) K)) :
    Ideal (MvPolynomial (Fin (n + 1)) K) :=
  Ideal.span (homog '' (I : Set (MvPolynomial (Fin n) K)))

private theorem IsHomog_of_isHomogeneous {I : Ideal (MvPolynomial (Fin n) K)}
    (hI : I.IsHomogeneous (homogeneousSubmodule (Fin n) K)) : IsHomog I := by
  intro r hr e
  have h := hI e hr
  convert h using 1
  exact (MvPolynomial.decomposition.decompose'_apply (R := K) (σ := Fin n) r e).symm

private theorem ideal_isHomogeneous_of_IsHomog
    (I : Ideal (MvPolynomial (Fin n) K)) (hI : IsHomog I) :
    I.IsHomogeneous (homogeneousSubmodule (Fin n) K) := by
  intro e r hr
  convert hI r hr e using 1
  exact MvPolynomial.decomposition.decompose'_apply (R := K) (σ := Fin n) r e

theorem homogOfDegree_homogeneous (D : ℕ) (f : MvPolynomial (Fin n) K) :
    homogOfDegree D f ∈ homogeneousSubmodule (Fin (n + 1)) K D := by
  classical
  rw [homogOfDegree]
  refine Submodule.sum_mem _ fun e he => ?_
  refine (mem_homogeneousSubmodule D _).mpr ?_
  have heD : e ≤ D := Nat.le_of_lt_succ (Finset.mem_range.mp he)
  have hX : ((X (R := K) (0 : Fin (n + 1))) ^ (D - e)).IsHomogeneous (D - e) :=
    by
      simpa using
        (MvPolynomial.IsHomogeneous.pow
          (MvPolynomial.isHomogeneous_X K (0 : Fin (n + 1))) (D - e))
  have hc :
      (rename Fin.succ (homogeneousComponent e f)).IsHomogeneous e :=
    (MvPolynomial.homogeneousComponent_isHomogeneous e f).rename_isHomogeneous
  convert hX.mul hc using 1
  omega

theorem homog_homogeneous (f : MvPolynomial (Fin n) K) :
    homog f ∈ homogeneousSubmodule (Fin (n + 1)) K f.totalDegree := by
  exact homogOfDegree_homogeneous f.totalDegree f

theorem dehomog_rename (g : MvPolynomial (Fin n) K) :
    dehomog (rename Fin.succ g) = g := by
  rw [dehomog, MvPolynomial.aeval_rename]
  simpa [Function.comp_def] using MvPolynomial.aeval_X_left_apply (R := K) g

theorem dehomog_X_zero :
    dehomog (X (0 : Fin (n + 1))) = (1 : MvPolynomial (Fin n) K) := by
  simp [dehomog]

theorem finSuccEquiv_rename_succ (g : MvPolynomial (Fin n) K) :
    MvPolynomial.finSuccEquiv K n (rename Fin.succ g) = Polynomial.C g := by
  change (((MvPolynomial.finSuccEquiv K n).toAlgHom.comp (rename Fin.succ)) g) =
    (Polynomial.CAlgHom : MvPolynomial (Fin n) K →ₐ[K] Polynomial (MvPolynomial (Fin n) K)) g
  congr 1
  apply MvPolynomial.algHom_ext
  intro i
  simp [MvPolynomial.finSuccEquiv_X_succ]

theorem dehomog_eq_eval_finSuccEquiv (F : MvPolynomial (Fin (n + 1)) K) :
    dehomog (K := K) (n := n) F =
      Polynomial.eval (1 : MvPolynomial (Fin n) K) (MvPolynomial.finSuccEquiv K n F) := by
  induction F using MvPolynomial.induction_on with
  | C c =>
      simp [dehomog, MvPolynomial.finSuccEquiv_apply]
  | add p q hp hq =>
      simp [map_add, hp, hq]
  | mul_X p i hp =>
      by_cases hi : i = 0
      · subst i
        simpa [map_mul, dehomog, MvPolynomial.finSuccEquiv_X_zero] using hp
      · obtain ⟨j, rfl⟩ := Fin.exists_succ_eq_of_ne_zero hi
        simpa [map_mul, dehomog, MvPolynomial.finSuccEquiv_X_succ] using hp

theorem dehomog_homogOfDegree {D : ℕ} {f : MvPolynomial (Fin n) K}
    (hD : f.totalDegree ≤ D) : dehomog (homogOfDegree D f) = f := by
  classical
  calc
    dehomog (homogOfDegree D f)
        = ∑ e ∈ Finset.range (D + 1), homogeneousComponent e f := by
            rw [homogOfDegree, map_sum]
            refine Finset.sum_congr rfl fun e he => ?_
            simp [dehomog_X_zero, dehomog_rename]
    _ = ∑ e ∈ Finset.range (f.totalDegree + 1), homogeneousComponent e f := by
            symm
            refine Finset.sum_subset ?_ ?_
            · intro e he
              exact Finset.mem_range.mpr (Nat.lt_succ_of_le
                (le_trans (Nat.le_of_lt_succ (Finset.mem_range.mp he)) hD))
            · intro e _heD hef
              have hlt : f.totalDegree < e := by
                exact Nat.lt_of_not_ge (fun hle => hef (Finset.mem_range.mpr (Nat.lt_succ_of_le hle)))
              simp [MvPolynomial.homogeneousComponent_eq_zero e f hlt]
    _ = f := MvPolynomial.sum_homogeneousComponent f

theorem dehomog_homog (f : MvPolynomial (Fin n) K) : dehomog (homog f) = f := by
  exact dehomog_homogOfDegree (D := f.totalDegree) le_rfl

theorem homogOfDegree_zero (D : ℕ) :
    homogOfDegree (K := K) (n := n) D 0 = 0 := by
  simp [homogOfDegree]

theorem homog_zero :
    homog (K := K) (n := n) 0 = 0 := by
  simp [homog, homogOfDegree]

theorem homogOfDegree_add (D : ℕ) (f g : MvPolynomial (Fin n) K) :
    homogOfDegree D (f + g) = homogOfDegree D f + homogOfDegree D g := by
  simp [homogOfDegree, map_add, mul_add, Finset.sum_add_distrib]

theorem homogOfDegree_sum {ι : Type*} (D : ℕ) (s : Finset ι)
    (f : ι → MvPolynomial (Fin n) K) :
    homogOfDegree D (∑ i ∈ s, f i) = ∑ i ∈ s, homogOfDegree D (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp [homogOfDegree_zero]
  | insert a s ha ih =>
      simp [Finset.sum_insert, ha, homogOfDegree_add, ih]

theorem homogOfDegree_neg (D : ℕ) (f : MvPolynomial (Fin n) K) :
    homogOfDegree D (-f) = -homogOfDegree D f := by
  simp [homogOfDegree]

theorem homog_neg (f : MvPolynomial (Fin n) K) :
    homog (-f) = -homog f := by
  simp [homog, MvPolynomial.totalDegree_neg, homogOfDegree]

theorem homog_one :
    homog (K := K) (n := n) 1 = 1 := by
  simp [homog, homogOfDegree]

theorem coeff_dehomog_of_homogeneous {D : ℕ} {F : MvPolynomial (Fin (n + 1)) K}
    (hF : F ∈ homogeneousSubmodule (Fin (n + 1)) K D)
    (m : Fin n →₀ ℕ) :
    coeff m (dehomog (K := K) (n := n) F) =
      if _hm : m.degree ≤ D then coeff (m.cons (D - m.degree)) F else 0 := by
  classical
  let p := MvPolynomial.finSuccEquiv K n F
  have hFhom : F.IsHomogeneous D := (mem_homogeneousSubmodule D F).mp hF
  have htd : F.totalDegree ≤ D := hFhom.totalDegree_le
  have hnat : p.natDegree < D + 1 := by
    have hdeg0 : degreeOf (0 : Fin (n + 1)) F ≤ F.totalDegree :=
      degreeOf_le_totalDegree F 0
    have hnatle : p.natDegree ≤ D := by
      simpa [p, MvPolynomial.natDegree_finSuccEquiv] using le_trans hdeg0 htd
    omega
  calc
    coeff m (dehomog (K := K) (n := n) F)
        = coeff m (Polynomial.eval (1 : MvPolynomial (Fin n) K) p) := by
            simp [p, dehomog_eq_eval_finSuccEquiv]
    _ = coeff m
          (∑ i ∈ Finset.range (D + 1), p.coeff i * (1 : MvPolynomial (Fin n) K) ^ i) := by
            rw [Polynomial.eval_eq_sum_range' hnat]
    _ = ∑ i ∈ Finset.range (D + 1), coeff m (p.coeff i) := by
            simp [coeff_sum]
    _ = if hm : m.degree ≤ D then coeff (m.cons (D - m.degree)) F else 0 := by
            by_cases hm : m.degree ≤ D
            · rw [dif_pos hm]
              calc
                (∑ i ∈ Finset.range (D + 1), coeff m (p.coeff i))
                    = coeff m (p.coeff (D - m.degree)) := by
                        exact Finset.sum_eq_single (s := Finset.range (D + 1))
                          (f := fun i => coeff m (p.coeff i)) (D - m.degree)
                          (by
                            intro i hi hineq
                            simpa [p, MvPolynomial.finSuccEquiv_coeff_coeff] using
                              hFhom.coeff_eq_zero (d := m.cons i) (by
                                change (Finsupp.cons i m).sum (fun _ e => e) ≠ D
                                rw [Finsupp.sum_cons]
                                change i + m.degree ≠ D
                                omega))
                          (by
                            intro hnot
                            exact False.elim (hnot (Finset.mem_range.mpr (by omega))))
                _ = coeff (m.cons (D - m.degree)) F := by
                    simp [p, MvPolynomial.finSuccEquiv_coeff_coeff]
            · rw [dif_neg hm]
              refine Finset.sum_eq_zero fun i hi => ?_
              simpa [p, MvPolynomial.finSuccEquiv_coeff_coeff] using
                hFhom.coeff_eq_zero (d := m.cons i) (by
                  change (Finsupp.cons i m).sum (fun _ e => e) ≠ D
                  rw [Finsupp.sum_cons]
                  change i + m.degree ≠ D
                  omega)

theorem coeff_finSuccEquiv_homogOfDegree (D k : ℕ)
    (f : MvPolynomial (Fin n) K) (m : Fin n →₀ ℕ) :
    coeff m (((MvPolynomial.finSuccEquiv K n) (homogOfDegree D f)).coeff k) =
      if _hk : k ≤ D then coeff m (homogeneousComponent (D - k) f) else 0 := by
  classical
  rw [homogOfDegree, map_sum]
  simp only [map_mul, map_pow, MvPolynomial.finSuccEquiv_X_zero,
    finSuccEquiv_rename_succ]
  rw [Polynomial.finset_sum_coeff, coeff_sum]
  by_cases hk : k ≤ D
  · rw [dif_pos hk]
    calc
      (∑ x ∈ Finset.range (D + 1),
          coeff m ((Polynomial.X ^ (D - x) *
            Polynomial.C (homogeneousComponent x f)).coeff k))
          = coeff m ((Polynomial.X ^ (D - (D - k)) *
              Polynomial.C (homogeneousComponent (D - k) f)).coeff k) := by
              exact Finset.sum_eq_single (s := Finset.range (D + 1))
                (f := fun x => coeff m ((Polynomial.X ^ (D - x) *
                  Polynomial.C (homogeneousComponent x f)).coeff k)) (D - k)
                (by
                  intro x hx hneq
                  change coeff m ((Polynomial.X ^ (D - x) *
                    Polynomial.C (homogeneousComponent x f)).coeff k) = 0
                  have hxD : x ≤ D := Nat.le_of_lt_succ (Finset.mem_range.mp hx)
                  have hpowne : k ≠ D - x := by omega
                  rw [Polynomial.coeff_X_pow_mul']
                  by_cases hle : D - x ≤ k
                  · rw [if_pos hle]
                    have hsubne : k - (D - x) ≠ 0 := by omega
                    rw [Polynomial.coeff_C, if_neg hsubne]
                    simp
                  · rw [if_neg hle]
                    simp)
                (by
                  intro hnot
                  exact False.elim (hnot (Finset.mem_range.mpr (by omega))))
      _ = coeff m (homogeneousComponent (D - k) f) := by
          rw [Polynomial.coeff_X_pow_mul']
          rw [if_pos (by omega : D - (D - k) ≤ k)]
          have hzero : k - (D - (D - k)) = 0 := by omega
          rw [hzero, Polynomial.coeff_C]
          simp
  · rw [dif_neg hk]
    refine Finset.sum_eq_zero fun x hx => ?_
    change coeff m ((Polynomial.X ^ (D - x) *
      Polynomial.C (homogeneousComponent x f)).coeff k) = 0
    have hkgt : D < k := Nat.lt_of_not_ge hk
    have hlt : D - x < k := lt_of_le_of_lt (Nat.sub_le D x) hkgt
    rw [Polynomial.coeff_X_pow_mul']
    rw [if_pos (le_of_lt hlt)]
    have hsubne : k - (D - x) ≠ 0 := by omega
    rw [Polynomial.coeff_C, if_neg hsubne]
    simp

theorem homogOfDegree_dehomog_of_homogeneous {D : ℕ}
    {F : MvPolynomial (Fin (n + 1)) K}
    (hF : F ∈ homogeneousSubmodule (Fin (n + 1)) K D) :
    homogOfDegree D (dehomog (K := K) (n := n) F) = F := by
  classical
  apply (MvPolynomial.finSuccEquiv K n).injective
  apply Polynomial.ext
  intro k
  apply MvPolynomial.ext
  intro m
  rw [coeff_finSuccEquiv_homogOfDegree]
  rw [MvPolynomial.finSuccEquiv_coeff_coeff]
  have hFhom : F.IsHomogeneous D := (mem_homogeneousSubmodule D F).mp hF
  by_cases hk : k ≤ D
  · rw [dif_pos hk]
    rw [MvPolynomial.coeff_homogeneousComponent]
    by_cases hdeg : m.degree = D - k
    · rw [if_pos hdeg]
      have hmle : m.degree ≤ D := by omega
      rw [coeff_dehomog_of_homogeneous hF m, dif_pos hmle]
      have hk_eq : D - m.degree = k := by omega
      rw [hk_eq]
    · rw [if_neg hdeg]
      symm
      apply hFhom.coeff_eq_zero
      change (Finsupp.cons k m).sum (fun _ e => e) ≠ D
      rw [Finsupp.sum_cons]
      change k + m.degree ≠ D
      intro hsum
      apply hdeg
      omega
  · rw [dif_neg hk]
    symm
    apply hFhom.coeff_eq_zero
    change (Finsupp.cons k m).sum (fun _ e => e) ≠ D
    rw [Finsupp.sum_cons]
    change k + m.degree ≠ D
    intro hsum
    apply hk
    omega

theorem homogOfDegree_eq_X0_pow_mul_homog {D : ℕ}
    {f : MvPolynomial (Fin n) K} (hD : f.totalDegree ≤ D) :
    homogOfDegree D f =
      (X (0 : Fin (n + 1))) ^ (D - f.totalDegree) * homog f := by
  classical
  rw [homog]
  unfold homogOfDegree
  calc
    (∑ e ∈ Finset.range (D + 1),
        X (0 : Fin (n + 1)) ^ (D - e) *
          rename Fin.succ (homogeneousComponent e f))
        = ∑ e ∈ Finset.range (f.totalDegree + 1),
            X (0 : Fin (n + 1)) ^ (D - e) *
              rename Fin.succ (homogeneousComponent e f) := by
            symm
            refine Finset.sum_subset ?_ ?_
            · intro e he
              exact Finset.mem_range.mpr (Nat.lt_succ_of_le
                (le_trans (Nat.le_of_lt_succ (Finset.mem_range.mp he)) hD))
            · intro e heD hef
              have hlt : f.totalDegree < e := by
                exact Nat.lt_of_not_ge
                  (fun hle => hef (Finset.mem_range.mpr (Nat.lt_succ_of_le hle)))
              simp [MvPolynomial.homogeneousComponent_eq_zero e f hlt]
    _ = ∑ e ∈ Finset.range (f.totalDegree + 1),
          X (0 : Fin (n + 1)) ^ (D - f.totalDegree) *
            (X (0 : Fin (n + 1)) ^ (f.totalDegree - e) *
              rename Fin.succ (homogeneousComponent e f)) := by
            refine Finset.sum_congr rfl fun e he => ?_
            have hedeg : e ≤ f.totalDegree :=
              Nat.le_of_lt_succ (Finset.mem_range.mp he)
            have hpow : D - e = (D - f.totalDegree) + (f.totalDegree - e) := by
              omega
            rw [hpow, pow_add]
            ring
    _ = X (0 : Fin (n + 1)) ^ (D - f.totalDegree) *
          ∑ e ∈ Finset.range (f.totalDegree + 1),
            X (0 : Fin (n + 1)) ^ (f.totalDegree - e) *
              rename Fin.succ (homogeneousComponent e f) := by
            exact (Finset.mul_sum (s := Finset.range (f.totalDegree + 1))
              (a := X (0 : Fin (n + 1)) ^ (D - f.totalDegree))
              (f := fun e => X (0 : Fin (n + 1)) ^ (f.totalDegree - e) *
                rename Fin.succ (homogeneousComponent e f))).symm

theorem homogOfDegree_eq_X0_pow_mul_homogOfDegree {E D : ℕ}
    {f : MvPolynomial (Fin n) K} (hfE : f.totalDegree ≤ E) (hED : E ≤ D) :
    homogOfDegree D f =
      (X (0 : Fin (n + 1))) ^ (D - E) * homogOfDegree E f := by
  rw [homogOfDegree_eq_X0_pow_mul_homog (le_trans hfE hED),
    homogOfDegree_eq_X0_pow_mul_homog hfE]
  rw [← mul_assoc, ← pow_add]
  have hpow : D - E + (E - f.totalDegree) = D - f.totalDegree := by omega
  rw [hpow]

theorem homogOfDegree_mem_idealHomog {I : Ideal (MvPolynomial (Fin n) K)}
    {D : ℕ} {f : MvPolynomial (Fin n) K} (hf : f ∈ I)
    (hD : f.totalDegree ≤ D) :
    homogOfDegree D f ∈ idealHomog I := by
  rw [homogOfDegree_eq_X0_pow_mul_homog hD]
  exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨f, hf, rfl⟩)

theorem totalDegree_dehomog_le_of_homogeneous {D : ℕ}
    {F : MvPolynomial (Fin (n + 1)) K}
    (hF : F ∈ homogeneousSubmodule (Fin (n + 1)) K D) :
    (dehomog (K := K) (n := n) F).totalDegree ≤ D := by
  classical
  rw [MvPolynomial.totalDegree]
  refine Finset.sup_le fun m hm => ?_
  rw [mem_support_iff] at hm
  by_contra hle
  change ¬m.degree ≤ D at hle
  have hcoeff := coeff_dehomog_of_homogeneous hF m
  rw [dif_neg hle] at hcoeff
  exact hm hcoeff

theorem totalDegree_dehomog_le (F : MvPolynomial (Fin (n + 1)) K) :
    (dehomog (K := K) (n := n) F).totalDegree ≤ F.totalDegree := by
  classical
  have hsum :
      dehomog (K := K) (n := n) F =
        ∑ e ∈ Finset.range (F.totalDegree + 1),
          dehomog (K := K) (n := n) (homogeneousComponent e F) := by
    rw [← map_sum, MvPolynomial.sum_homogeneousComponent]
  rw [hsum]
  refine MvPolynomial.totalDegree_finsetSum_le ?_
  intro e he
  exact (totalDegree_dehomog_le_of_homogeneous
    (K := K) (n := n) (MvPolynomial.homogeneousComponent_mem e F)).trans
      (Nat.le_of_lt_succ (Finset.mem_range.mp he))

theorem isHomog_idealHomog (I : Ideal (MvPolynomial (Fin n) K)) :
    IsHomog (idealHomog I) := by
  refine IsHomog_of_isHomogeneous ?_
  unfold idealHomog
  refine Ideal.homogeneous_span
    (𝒜 := homogeneousSubmodule (Fin (n + 1)) K)
    (homog '' (I : Set (MvPolynomial (Fin n) K))) ?_
  rintro F ⟨g, _hg, rfl⟩
  exact ⟨g.totalDegree, homog_homogeneous g⟩

theorem map_dehomog_idealHomog_le (I : Ideal (MvPolynomial (Fin n) K)) :
    (idealHomog I).map (dehomog (K := K) (n := n)).toRingHom ≤ I := by
  rw [Ideal.map_le_iff_le_comap]
  unfold idealHomog
  rw [Ideal.span_le]
  rintro F ⟨g, hg, rfl⟩
  change dehomog (homog g) ∈ I
  simpa [dehomog_homog] using hg

theorem homogeneous_mem_idealHomog_iff {I : Ideal (MvPolynomial (Fin n) K)}
    {D : ℕ} {F : MvPolynomial (Fin (n + 1)) K}
    (hF : F ∈ homogeneousSubmodule (Fin (n + 1)) K D) :
    F ∈ idealHomog I ↔ dehomog (K := K) (n := n) F ∈ I := by
  constructor
  · intro h
    have hmap :
        (dehomog (K := K) (n := n)).toRingHom F ∈
          (idealHomog I).map (dehomog (K := K) (n := n)).toRingHom :=
      Ideal.mem_map_of_mem _ h
    exact map_dehomog_idealHomog_le (K := K) (n := n) I hmap
  · intro h
    rw [← homogOfDegree_dehomog_of_homogeneous hF]
    exact homogOfDegree_mem_idealHomog h
      (totalDegree_dehomog_le_of_homogeneous (K := K) (n := n) hF)

theorem dehomog_surjective :
    Function.Surjective (dehomog (K := K) (n := n)).toRingHom := by
  intro g
  exact ⟨rename Fin.succ g, by simpa [dehomog_rename]⟩

theorem homog_mul {g h : MvPolynomial (Fin n) K} (hg : g ≠ 0) (hh : h ≠ 0) :
    homog (g * h) = homog g * homog h := by
  classical
  let D := g.totalDegree + h.totalDegree
  have hprodHom : homog g * homog h ∈ homogeneousSubmodule (Fin (n + 1)) K D := by
    have hgHom : (homog g).IsHomogeneous g.totalDegree :=
      (mem_homogeneousSubmodule g.totalDegree (homog g)).mp (homog_homogeneous g)
    have hhHom : (homog h).IsHomogeneous h.totalDegree :=
      (mem_homogeneousSubmodule h.totalDegree (homog h)).mp (homog_homogeneous h)
    exact (mem_homogeneousSubmodule D (homog g * homog h)).mpr (hgHom.mul hhHom)
  have hdeh :
      dehomog (K := K) (n := n) (homog g * homog h) = g * h := by
    simp [map_mul, dehomog_homog]
  calc
    homog (g * h) = homogOfDegree D (g * h) := by
      rw [homog, MvPolynomial.totalDegree_mul_of_isDomain hg hh]
    _ = homogOfDegree D (dehomog (K := K) (n := n) (homog g * homog h)) := by
      rw [hdeh]
    _ = homog g * homog h := homogOfDegree_dehomog_of_homogeneous hprodHom

theorem mem_of_X0_pow_mul_mem_of_notMem {Q : Ideal (MvPolynomial (Fin (n + 1)) K)}
    [Q.IsPrime] (hX : X (0 : Fin (n + 1)) ∉ Q)
    {F : MvPolynomial (Fin (n + 1)) K} {k : ℕ}
    (h : (X (0 : Fin (n + 1))) ^ k * F ∈ Q) : F ∈ Q := by
  by_cases hk : k = 0
  · simpa [hk] using h
  · have hpow_not : (X (0 : Fin (n + 1))) ^ k ∉ Q := by
      intro hpow
      exact hX ((show Q.IsPrime from inferInstance).mem_of_pow_mem k hpow)
    exact ((show Q.IsPrime from inferInstance).mem_or_mem h).resolve_left hpow_not

theorem homog_dehomog_mem_of_mem_of_isHomog
    {Q : Ideal (MvPolynomial (Fin (n + 1)) K)} [Q.IsPrime]
    (hQhom : IsHomog Q) (hX : X (0 : Fin (n + 1)) ∉ Q)
    {F : MvPolynomial (Fin (n + 1)) K} (hFQ : F ∈ Q) :
    homog (dehomog (K := K) (n := n) F) ∈ Q := by
  classical
  let M := F.totalDegree
  have hdecomp :
      dehomog (K := K) (n := n) F =
        ∑ e ∈ Finset.range (M + 1),
          dehomog (K := K) (n := n) (homogeneousComponent e F) := by
    dsimp [M]
    rw [← map_sum, MvPolynomial.sum_homogeneousComponent]
  have hfixed : homogOfDegree M (dehomog (K := K) (n := n) F) ∈ Q := by
    rw [hdecomp, homogOfDegree_sum]
    refine Q.sum_mem fun e he => ?_
    have heM : e ≤ M := Nat.le_of_lt_succ (Finset.mem_range.mp he)
    have hcompHom :
        homogeneousComponent e F ∈ homogeneousSubmodule (Fin (n + 1)) K e :=
      MvPolynomial.homogeneousComponent_mem e F
    have hcompQ : homogeneousComponent e F ∈ Q := hQhom F hFQ e
    have hdeg :
        (dehomog (K := K) (n := n) (homogeneousComponent e F)).totalDegree ≤ e :=
      totalDegree_dehomog_le_of_homogeneous (K := K) (n := n) hcompHom
    rw [homogOfDegree_eq_X0_pow_mul_homogOfDegree hdeg heM]
    exact Ideal.mul_mem_left _ _ (by
      simpa [homogOfDegree_dehomog_of_homogeneous hcompHom] using hcompQ)
  have hdegF : (dehomog (K := K) (n := n) F).totalDegree ≤ M :=
    totalDegree_dehomog_le (K := K) (n := n) F
  rw [homogOfDegree_eq_X0_pow_mul_homog hdegF] at hfixed
  exact mem_of_X0_pow_mul_mem_of_notMem (K := K) (n := n) hX hfixed

theorem X0_notMem_idealHomog_of_prime
    (p : Ideal (MvPolynomial (Fin n) K)) [p.IsPrime] (hp : p ≠ ⊤) :
    X (0 : Fin (n + 1)) ∉ idealHomog p := by
  intro hX
  have hmap :
      (dehomog (K := K) (n := n)).toRingHom (X (0 : Fin (n + 1))) ∈
        (idealHomog p).map (dehomog (K := K) (n := n)).toRingHom :=
    Ideal.mem_map_of_mem _ hX
  have h1 : (1 : MvPolynomial (Fin n) K) ∈ p := by
    simpa [dehomog] using (map_dehomog_idealHomog_le (K := K) (n := n) p hmap)
  exact hp ((Ideal.eq_top_iff_one p).mpr h1)

theorem idealHomog_isPrime (p : Ideal (MvPolynomial (Fin n) K)) [p.IsPrime] :
    (idealHomog p).IsPrime := by
  classical
  let 𝒜 := homogeneousSubmodule (Fin (n + 1)) K
  have hhom : (idealHomog p).IsHomogeneous 𝒜 :=
    ideal_isHomogeneous_of_IsHomog (idealHomog p) (isHomog_idealHomog p)
  refine (Ideal.IsHomogeneous.isPrime_iff (𝒜 := 𝒜) hhom).mpr ?_
  constructor
  · intro htop
    have hX : X (0 : Fin (n + 1)) ∈ idealHomog p := by
      rw [htop]
      trivial
    exact X0_notMem_idealHomog_of_prime p
      ((show p.IsPrime from inferInstance).ne_top) hX
  · intro x y hx hy hxy
    have hdehxy : dehomog (K := K) (n := n) x *
        dehomog (K := K) (n := n) y ∈ p := by
      have hmap :
          (dehomog (K := K) (n := n)).toRingHom (x * y) ∈
            (idealHomog p).map (dehomog (K := K) (n := n)).toRingHom :=
        Ideal.mem_map_of_mem _ hxy
      simpa [map_mul] using (map_dehomog_idealHomog_le (K := K) (n := n) p hmap)
    rcases (show p.IsPrime from inferInstance).mem_or_mem hdehxy with hxmem | hymem
    · rcases hx with ⟨D, hxD⟩
      exact Or.inl ((homogeneous_mem_idealHomog_iff (I := p) hxD).mpr hxmem)
    · rcases hy with ⟨D, hyD⟩
      exact Or.inr ((homogeneous_mem_idealHomog_iff (I := p) hyD).mpr hymem)

theorem dehomog_idealHomog (I : Ideal (MvPolynomial (Fin n) K)) :
    (idealHomog I).map (dehomog (K := K) (n := n)).toRingHom = I := by
  apply le_antisymm
  · exact map_dehomog_idealHomog_le I
  · intro g hg
    have hgen : homog g ∈ idealHomog I := by
      unfold idealHomog
      exact Ideal.subset_span ⟨g, hg, rfl⟩
    have hmap :
        (dehomog (K := K) (n := n)).toRingHom (homog g) ∈
          (idealHomog I).map (dehomog (K := K) (n := n)).toRingHom :=
      Ideal.mem_map_of_mem _ hgen
    simpa [dehomog_homog] using hmap

/-- The transfer: a minimal prime of the affine ideal homogenizes to a minimal
prime of the ideal of homogenized generators. -/
theorem idealHomog_mem_minimalPrimes {C : ℕ}
    (f : Fin C → MvPolynomial (Fin n) K)
    {p : Ideal (MvPolynomial (Fin n) K)}
    (hp : p ∈ (Ideal.span (Set.range f)).minimalPrimes) :
    idealHomog p ∈
      (Ideal.span (Set.range (fun i => homog (f i)))).minimalPrimes := by
  classical
  haveI : p.IsPrime := hp.1.1
  let J : Ideal (MvPolynomial (Fin (n + 1)) K) :=
    Ideal.span (Set.range (fun i => homog (f i)))
  let P : Ideal (MvPolynomial (Fin (n + 1)) K) := idealHomog p
  change P ∈ J.minimalPrimes
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · exact idealHomog_isPrime p
  · dsimp [J, P]
    rw [Ideal.span_le]
    rintro F ⟨i, rfl⟩
    unfold idealHomog
    exact Ideal.subset_span
      ⟨f i, hp.1.2 (Ideal.subset_span ⟨i, rfl⟩), rfl⟩
  · intro Q hQ hQP
    let 𝒜 := homogeneousSubmodule (Fin (n + 1)) K
    let Q₀ : Ideal (MvPolynomial (Fin (n + 1)) K) := (Q.homogeneousCore 𝒜).toIdeal
    have hQ₀prime : Q₀.IsPrime := by
      dsimp [Q₀]
      exact Ideal.IsPrime.homogeneousCore (𝒜 := 𝒜) hQ.1
    letI : Q₀.IsPrime := hQ₀prime
    have hQ₀_le_Q : Q₀ ≤ Q := by
      dsimp [Q₀]
      exact Ideal.toIdeal_homogeneousCore_le 𝒜 Q
    have hQ₀_le_P : Q₀ ≤ P := hQ₀_le_Q.trans hQP
    have hJmath : J.IsHomogeneous 𝒜 := by
      dsimp [J, 𝒜]
      refine Ideal.homogeneous_span
        (𝒜 := homogeneousSubmodule (Fin (n + 1)) K)
        (Set.range (fun i => homog (f i))) ?_
      rintro F ⟨i, rfl⟩
      exact ⟨(f i).totalDegree, homog_homogeneous (f i)⟩
    have hJ_le_Q₀ : J ≤ Q₀ := by
      calc
        J = (J.homogeneousCore 𝒜).toIdeal := hJmath.toIdeal_homogeneousCore_eq_self.symm
        _ ≤ (Q.homogeneousCore 𝒜).toIdeal := Ideal.homogeneousCore_mono 𝒜 hQ.2
        _ = Q₀ := rfl
    have hQ₀math : Q₀.IsHomogeneous 𝒜 := by
      dsimp [Q₀]
      exact HomogeneousIdeal.isHomogeneous (Q.homogeneousCore 𝒜)
    have hQ₀hom : IsHomog Q₀ := IsHomog_of_isHomogeneous hQ₀math
    have hXnotP : X (0 : Fin (n + 1)) ∉ P := by
      dsimp [P]
      exact X0_notMem_idealHomog_of_prime p
        ((show p.IsPrime from inferInstance).ne_top)
    have hXnotQ₀ : X (0 : Fin (n + 1)) ∉ Q₀ := fun hX => hXnotP (hQ₀_le_P hX)
    let q' : Ideal (MvPolynomial (Fin n) K) :=
      Q₀.map (dehomog (K := K) (n := n)).toRingHom
    have hq'prime : q'.IsPrime := by
      rw [Ideal.isPrime_iff]
      constructor
      · intro htop
        have h1 : (1 : MvPolynomial (Fin n) K) ∈ q' := by
          rw [htop]
          trivial
        obtain ⟨F, hFQ, hFdeh⟩ :=
          (Ideal.mem_map_iff_of_surjective _
            (dehomog_surjective (K := K) (n := n))).mp h1
        have hhomog :
            homog (dehomog (K := K) (n := n) F) ∈ Q₀ :=
          homog_dehomog_mem_of_mem_of_isHomog (K := K) (n := n)
            hQ₀hom hXnotQ₀ hFQ
        have hFdeh' : dehomog (K := K) (n := n) F = 1 := hFdeh
        have h1Q₀ : (1 : MvPolynomial (Fin (n + 1)) K) ∈ Q₀ := by
          rw [hFdeh', homog_one] at hhomog
          exact hhomog
        exact (show Q₀.IsPrime from inferInstance).ne_top
          ((Ideal.eq_top_iff_one Q₀).mpr h1Q₀)
      · intro a b hab
        by_cases ha : a = 0
        · left
          simpa [ha]
        by_cases hb : b = 0
        · right
          simpa [hb]
        obtain ⟨F, hFQ, hFdeh⟩ :=
          (Ideal.mem_map_iff_of_surjective _
            (dehomog_surjective (K := K) (n := n))).mp hab
        have hhomog :
            homog (dehomog (K := K) (n := n) F) ∈ Q₀ :=
          homog_dehomog_mem_of_mem_of_isHomog (K := K) (n := n)
            hQ₀hom hXnotQ₀ hFQ
        have hFdeh' : dehomog (K := K) (n := n) F = a * b := hFdeh
        have hprod : homog a * homog b ∈ Q₀ := by
          rw [hFdeh', homog_mul (K := K) (n := n) ha hb] at hhomog
          exact hhomog
        rcases (show Q₀.IsPrime from inferInstance).mem_or_mem hprod with haQ | hbQ
        · left
          rw [Ideal.mem_map_iff_of_surjective _
            (dehomog_surjective (K := K) (n := n))]
          exact ⟨homog a, haQ, by simp [dehomog_homog]⟩
        · right
          rw [Ideal.mem_map_iff_of_surjective _
            (dehomog_surjective (K := K) (n := n))]
          exact ⟨homog b, hbQ, by simp [dehomog_homog]⟩
    have hI_le_q' : Ideal.span (Set.range f) ≤ q' := by
      rw [Ideal.span_le]
      rintro g ⟨i, rfl⟩
      show f i ∈ q'
      refine (Ideal.mem_map_iff_of_surjective _
        (dehomog_surjective (K := K) (n := n))).mpr ⟨homog (f i), ?_, ?_⟩
      · exact hJ_le_Q₀ (Ideal.subset_span ⟨i, rfl⟩)
      · show dehomog (K := K) (n := n) (homog (f i)) = f i
        exact dehomog_homog (f i)
    have hq'_le_p : q' ≤ p := by
      intro g hg
      obtain ⟨F, hFQ, hFdeh⟩ :=
        (Ideal.mem_map_iff_of_surjective _
          (dehomog_surjective (K := K) (n := n))).mp hg
      have hFP : F ∈ P := hQ₀_le_P hFQ
      have hmap :
          (dehomog (K := K) (n := n)).toRingHom F ∈
            P.map (dehomog (K := K) (n := n)).toRingHom :=
        Ideal.mem_map_of_mem _ hFP
      have hdeh_mem : dehomog (K := K) (n := n) F ∈ p := by
        dsimp [P] at hmap
        exact map_dehomog_idealHomog_le (K := K) (n := n) p hmap
      have hFdeh' : dehomog (K := K) (n := n) F = g := hFdeh
      exact hFdeh' ▸ hdeh_mem
    have hp_le_q' : p ≤ q' := hp.2 ⟨hq'prime, hI_le_q'⟩ hq'_le_p
    have hP_le_Q₀ : P ≤ Q₀ := by
      dsimp [P]
      rw [idealHomog, Ideal.span_le]
      rintro F ⟨g, hg, rfl⟩
      have hgq' : g ∈ q' := hp_le_q' hg
      obtain ⟨G, hGQ, hGdeh⟩ :=
        (Ideal.mem_map_iff_of_surjective _
          (dehomog_surjective (K := K) (n := n))).mp hgq'
      have hhomog :
          homog (dehomog (K := K) (n := n) G) ∈ Q₀ :=
        homog_dehomog_mem_of_mem_of_isHomog (K := K) (n := n)
          hQ₀hom hXnotQ₀ hGQ
      have hGdeh' : dehomog (K := K) (n := n) G = g := hGdeh
      rw [hGdeh'] at hhomog
      exact hhomog
    exact hP_le_Q₀.trans hQ₀_le_Q

end
