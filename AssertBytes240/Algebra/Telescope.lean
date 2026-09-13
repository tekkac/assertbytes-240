import Mathlib

/-!
# W1 — Filtration telescope and lattice counting

Defines the truncation rank `phi` and proves the filtration-step inequality,
the lattice telescope, and the bounded-rank-to-finite-dimensional conclusion.
`CIBezout` uses this as its linear-algebra/combinatorics layer.
-/

open MvPolynomial Filter Topology

noncomputable section

variable {K : Type*} [Field K] {n : ℕ}

/-- Image of the degree-`≤ e` filtration piece in the quotient by `J`. -/
def truncImage (J : Ideal (MvPolynomial (Fin n) K)) (e : ℕ) :
    Submodule K (MvPolynomial (Fin n) K ⧸ J) :=
  (restrictTotalDegree (Fin n) K e).map (Ideal.Quotient.mkₐ K J).toLinearMap

/-- `phi J e` = dimension of the image of the degree-`≤ e` piece in `R ⧸ J`. -/
def phi (J : Ideal (MvPolynomial (Fin n) K)) (e : ℕ) : ℕ :=
  Module.finrank K (truncImage J e)

instance truncImage_finiteDimensional
    (J : Ideal (MvPolynomial (Fin n) K)) (e : ℕ) :
    FiniteDimensional K (truncImage J e) := by
  dsimp [truncImage]
  infer_instance

theorem phi_mono (J : Ideal (MvPolynomial (Fin n) K)) :
    Monotone (phi J) := by
  intro a b hab
  dsimp [phi]
  apply Submodule.finrank_mono
  intro x hx
  rcases hx with ⟨p, hp, rfl⟩
  refine ⟨p, ?_, rfl⟩
  exact (MvPolynomial.mem_restrictTotalDegree (σ := Fin n) (R := K) (m := b) p).mpr
    (((MvPolynomial.mem_restrictTotalDegree (σ := Fin n) (R := K) (m := a) p).mp hp).trans hab)

private lemma truncImage_mono (J : Ideal (MvPolynomial (Fin n) K)) :
    Monotone (truncImage J) := by
  intro a b hab x hx
  rcases hx with ⟨p, hp, rfl⟩
  refine ⟨p, ?_, rfl⟩
  exact (MvPolynomial.mem_restrictTotalDegree (σ := Fin n) (R := K) (m := b) p).mpr
    (((MvPolynomial.mem_restrictTotalDegree (σ := Fin n) (R := K) (m := a) p).mp hp).trans hab)

private lemma finite_set_finsupp_sum_le (n e : ℕ) :
    Set.Finite {s : Fin n →₀ ℕ | s.sum (fun _ a => a) ≤ e} := by
  classical
  simpa [Finsupp.degree_eq_sum, Finsupp.sum_fintype] using
    (Finsupp.finite_of_degree_le (σ := Fin n) e)

private lemma finite_set_finsupp_sum_eq (n t : ℕ) :
    Set.Finite {s : Fin n →₀ ℕ | s.sum (fun _ a => a) = t} := by
  exact (finite_set_finsupp_sum_le n t).subset (by
    intro s hs
    exact le_of_eq hs)

private noncomputable instance instFintypeFinsuppSumLe (n e : ℕ) :
    Fintype {s : Fin n →₀ ℕ // s.sum (fun _ a => a) ≤ e} :=
  (finite_set_finsupp_sum_le n e).fintype

private noncomputable instance instFintypeFinsuppSumEq (n t : ℕ) :
    Fintype {s : Fin n →₀ ℕ // s.sum (fun _ a => a) = t} :=
  (finite_set_finsupp_sum_eq n t).fintype

private def degreeLeEquivSigma (n e : ℕ) :
    {s : Fin n →₀ ℕ // s.sum (fun _ a => a) ≤ e} ≃
      Sigma (fun t : Fin (e + 1) => {s : Fin n →₀ ℕ // s.sum (fun _ a => a) = t.1}) where
  toFun s := ⟨⟨s.1.sum (fun _ a => a), Nat.lt_succ_of_le s.2⟩, ⟨s.1, rfl⟩⟩
  invFun t := ⟨t.2.1, by rw [t.2.2]; exact Nat.le_of_lt_succ t.1.2⟩
  left_inv s := by
    ext
    rfl
  right_inv t := by
    rcases t with ⟨⟨t, ht⟩, s, hs⟩
    dsimp at hs
    subst t
    rfl

private lemma card_degreeLe (n e : ℕ) :
    Fintype.card {s : Fin n →₀ ℕ // s.sum (fun _ a => a) ≤ e} = (e + n).choose n := by
  classical
  calc
    Fintype.card {s : Fin n →₀ ℕ // s.sum (fun _ a => a) ≤ e}
        = Fintype.card (Sigma (fun t : Fin (e + 1) =>
            {s : Fin n →₀ ℕ // s.sum (fun _ a => a) = t.1})) :=
          Fintype.card_congr (degreeLeEquivSigma n e)
    _ = ∑ t : Fin (e + 1),
          Fintype.card {s : Fin n →₀ ℕ // s.sum (fun _ a => a) = t.1} := by
          simp
    _ = ∑ t : Fin (e + 1), Nat.multichoose n t.1 := by
          apply Finset.sum_congr rfl
          intro t _ht
          calc
            Fintype.card {s : Fin n →₀ ℕ // s.sum (fun _ a => a) = t.1}
                = Fintype.card (Sym (Fin n) t.1) :=
              Fintype.card_congr (Equiv.symm (Sym.equivNatSum (Fin n) t.1))
            _ = Nat.multichoose n t.1 := by
              simpa using Sym.card_sym_eq_multichoose (Fin n) t.1
    _ = ∑ i ∈ Finset.range (e + 1), Nat.multichoose n i := by
          rw [← Fin.sum_univ_eq_sum_range]
    _ = (e + n).choose n := by
          exact Nat.sum_range_multichoose e n

private lemma finrank_restrictTotalDegree (e : ℕ) :
    Module.finrank K (MvPolynomial.restrictTotalDegree (Fin n) K e) = (e + n).choose n := by
  classical
  rw [MvPolynomial.restrictTotalDegree]
  letI : Fintype ↑{s : Fin n →₀ ℕ | s.sum (fun _ a => a) ≤ e} :=
    instFintypeFinsuppSumLe n e
  rw [Module.finrank_eq_card_basis
    (MvPolynomial.basisRestrictSupport K {s : Fin n →₀ ℕ | s.sum (fun _ a => a) ≤ e})]
  exact card_degreeLe n e

theorem phi_le_choose (J : Ideal (MvPolynomial (Fin n) K)) (e : ℕ) :
    phi J e ≤ (e + n).choose n := by
  dsimp [phi, truncImage]
  calc
    Module.finrank K
        ((MvPolynomial.restrictTotalDegree (Fin n) K e).map
          (Ideal.Quotient.mkₐ K J).toLinearMap)
        ≤ Module.finrank K (MvPolynomial.restrictTotalDegree (Fin n) K e) :=
      Submodule.finrank_map_le (Ideal.Quotient.mkₐ K J).toLinearMap
        (MvPolynomial.restrictTotalDegree (Fin n) K e)
    _ = (e + n).choose n := finrank_restrictTotalDegree (K := K) (n := n) e

private lemma truncImage_map_factor
    (J H : Ideal (MvPolynomial (Fin n) K)) (hJH : J ≤ H) (e : ℕ) :
    (truncImage J e).map (Ideal.Quotient.factorₐ K hJH).toLinearMap = truncImage H e := by
  unfold truncImage
  rw [← Submodule.map_comp]
  rfl

private lemma mul_mem_truncImage
    (J : Ideal (MvPolynomial (Fin n) K)) (h : MvPolynomial (Fin n) K)
    {d e : ℕ} (hdeg : h.totalDegree ≤ d) (hde : d ≤ e)
    {x : MvPolynomial (Fin n) K ⧸ J} (hx : x ∈ truncImage J (e - d)) :
    (Ideal.Quotient.mk J h) * x ∈ truncImage J e := by
  rcases hx with ⟨p, hp, rfl⟩
  refine ⟨h * p, ?_, ?_⟩
  · apply (MvPolynomial.mem_restrictTotalDegree (σ := Fin n) (R := K) (m := e) (h * p)).mpr
    have hpdeg :=
      (MvPolynomial.mem_restrictTotalDegree (σ := Fin n) (R := K) (m := e - d) p).mp hp
    calc
      (h * p).totalDegree ≤ h.totalDegree + p.totalDegree := MvPolynomial.totalDegree_mul h p
      _ ≤ d + (e - d) := Nat.add_le_add hdeg hpdeg
      _ = e := Nat.add_sub_of_le hde
  · simp

private lemma mul_truncImage_injective
    (J : Ideal (MvPolynomial (Fin n) K)) (h : MvPolynomial (Fin n) K)
    {d e : ℕ} (hdeg : h.totalDegree ≤ d) (hde : d ≤ e)
    (hreg : IsSMulRegular (MvPolynomial (Fin n) K ⧸ J) h) :
    Function.Injective
      (((LinearMap.mulLeft K (Ideal.Quotient.mk J h)).domRestrict (truncImage J (e - d))).codRestrict
        (truncImage J e) (fun x => mul_mem_truncImage J h hdeg hde x.2)) := by
  intro x y hxy
  apply Subtype.ext
  exact hreg (by
    have hmul : (Ideal.Quotient.mk J h) * (x : MvPolynomial (Fin n) K ⧸ J) =
        (Ideal.Quotient.mk J h) * (y : MvPolynomial (Fin n) K ⧸ J) := by
      simpa only [LinearMap.codRestrict_apply, LinearMap.domRestrict_apply,
        LinearMap.mulLeft_apply] using congrArg Subtype.val hxy
    change (algebraMap (MvPolynomial (Fin n) K) (MvPolynomial (Fin n) K ⧸ J) h) *
        (x : MvPolynomial (Fin n) K ⧸ J) =
      (algebraMap (MvPolynomial (Fin n) K) (MvPolynomial (Fin n) K ⧸ J) h) *
        (y : MvPolynomial (Fin n) K ⧸ J)
    simpa only [Ideal.Quotient.algebraMap_eq] using hmul)

private lemma mul_range_le_projection_ker
    (J : Ideal (MvPolynomial (Fin n) K)) (h : MvPolynomial (Fin n) K)
    {d e : ℕ} (hdeg : h.totalDegree ≤ d) (hde : d ≤ e) :
    LinearMap.range
      (((LinearMap.mulLeft K (Ideal.Quotient.mk J h)).domRestrict (truncImage J (e - d))).codRestrict
        (truncImage J e) (fun x => mul_mem_truncImage J h hdeg hde x.2))
      ≤ LinearMap.ker
        (((Ideal.Quotient.factorₐ K (show J ≤ J ⊔ Ideal.span {h} from le_sup_left)).toLinearMap).domRestrict
          (truncImage J e)) := by
  rintro y ⟨x, rfl⟩
  rcases x.2 with ⟨p, _hp, hpx⟩
  rw [LinearMap.mem_ker]
  change (Ideal.Quotient.factorₐ K (show J ≤ J ⊔ Ideal.span {h} from le_sup_left)).toLinearMap
      ((Ideal.Quotient.mk J h) * (x : MvPolynomial (Fin n) K ⧸ J)) = 0
  rw [← hpx]
  change Ideal.Quotient.mk (J ⊔ Ideal.span {h}) (h * p) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem]
  exact (J ⊔ Ideal.span {h}).mul_mem_right p
    (show h ∈ J ⊔ Ideal.span {h} from
      (le_sup_right : Ideal.span ({h} : Set (MvPolynomial (Fin n) K)) ≤ J ⊔ Ideal.span {h})
        (Ideal.subset_span (by simp)))

/-- **Recurrence.** If `h` has `totalDegree ≤ d` and is a nonzerodivisor modulo
`J`, then the dimension counts of the truncated quotients satisfy the sharp
step inequality. (For `e < d` the second summand is absent; both cases stated.) -/
theorem phi_step
    (J : Ideal (MvPolynomial (Fin n) K)) (h : MvPolynomial (Fin n) K)
    (d : ℕ) (hdeg : h.totalDegree ≤ d)
    (hreg : IsSMulRegular (MvPolynomial (Fin n) K ⧸ J) h) :
    (∀ e, d ≤ e →
      phi (J ⊔ Ideal.span {h}) e + phi J (e - d) ≤ phi J e) ∧
    (∀ e, phi (J ⊔ Ideal.span {h}) e ≤ phi J e) := by
  constructor
  · intro e hde
    dsimp [phi]
    let H : Ideal (MvPolynomial (Fin n) K) := J ⊔ Ideal.span {h}
    let q : (MvPolynomial (Fin n) K ⧸ J) →ₗ[K] (MvPolynomial (Fin n) K ⧸ H) :=
      (Ideal.Quotient.factorₐ K (show J ≤ H from le_sup_left)).toLinearMap
    let π : truncImage J e →ₗ[K] (MvPolynomial (Fin n) K ⧸ H) :=
      q.domRestrict (truncImage J e)
    let μ : truncImage J (e - d) →ₗ[K] truncImage J e :=
      (((LinearMap.mulLeft K (Ideal.Quotient.mk J h)).domRestrict (truncImage J (e - d))).codRestrict
        (truncImage J e) (fun x => mul_mem_truncImage J h hdeg hde x.2))
    have hπrange : LinearMap.range π = truncImage H e := by
      dsimp [π, q]
      rw [LinearMap.range_domRestrict]
      simpa [H] using
        truncImage_map_factor (K := K) (n := n) J H (show J ≤ H from le_sup_left) e
    have hμinj : Function.Injective μ := by
      simpa [μ] using mul_truncImage_injective J h hdeg hde hreg
    have hμker : LinearMap.range μ ≤ LinearMap.ker π := by
      simpa [H, q, π, μ] using mul_range_le_projection_ker J h hdeg hde
    have hrn := LinearMap.finrank_range_add_finrank_ker π
    rw [hπrange] at hrn
    have hμdim :
        Module.finrank K (truncImage J (e - d)) ≤ Module.finrank K (LinearMap.ker π) := by
      calc
        Module.finrank K (truncImage J (e - d)) = Module.finrank K (LinearMap.range μ) :=
          (LinearMap.finrank_range_of_inj hμinj).symm
        _ ≤ Module.finrank K (LinearMap.ker π) := Submodule.finrank_mono hμker
    calc
      Module.finrank K (truncImage H e) + Module.finrank K (truncImage J (e - d))
          ≤ Module.finrank K (truncImage H e) + Module.finrank K (LinearMap.ker π) :=
        Nat.add_le_add_left hμdim _
      _ = Module.finrank K (truncImage J e) := hrn
  · intro e
    dsimp [phi]
    let H : Ideal (MvPolynomial (Fin n) K) := J ⊔ Ideal.span {h}
    let q : (MvPolynomial (Fin n) K ⧸ J) →ₗ[K] (MvPolynomial (Fin n) K ⧸ H) :=
      (Ideal.Quotient.factorₐ K (show J ≤ H from le_sup_left)).toLinearMap
    have hmap : (truncImage J e).map q = truncImage H e := by
      simpa [H, q] using
        truncImage_map_factor (K := K) (n := n) J H (show J ≤ H from le_sup_left) e
    rw [← hmap]
    exact Submodule.finrank_map_le q (truncImage J e)

private lemma div_sub_self_add_one {d e : ℕ} (hd : 1 ≤ d) (hde : d ≤ e) :
    e / d = (e - d) / d + 1 := by
  have hdvd : d ∣ d := dvd_rfl
  calc
    e / d = ((e - d) + d) / d := by rw [Nat.sub_add_cancel hde]
    _ = (e - d) / d + d / d := Nat.add_div_of_dvd_left hdvd
    _ = (e - d) / d + 1 := by rw [Nat.div_self (show 0 < d from hd)]

private lemma tail_term_eq {d e i : ℕ} :
    e - (i + 1) * d = e - d - i * d := by
  rw [Nat.add_mul, one_mul, add_comm (i * d) d, tsub_add_eq_tsub_tsub]

private lemma telescope_sum_split {g : ℕ → ℕ} {d e : ℕ} (hd : 1 ≤ d) (hde : d ≤ e) :
    (∑ i ∈ Finset.range (e / d + 1), g (e - i * d)) =
      g e + ∑ i ∈ Finset.range ((e - d) / d + 1), g ((e - d) - i * d) := by
  rw [div_sub_self_add_one hd hde]
  rw [show ((e - d) / d + 1 + 1) = ((e - d) / d + 1) + 1 by rfl]
  rw [Finset.sum_range_succ']
  simp only [zero_mul, tsub_zero]
  rw [add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro i _hi
  congr 1
  exact tail_term_eq (d := d) (e := e) (i := i)

/-- **Single-stage telescope** (pure arithmetic). -/
theorem telescope_sum {f g : ℕ → ℕ} {d : ℕ} (hd : 1 ≤ d)
    (h1 : ∀ e, d ≤ e → g e + f (e - d) ≤ f e)
    (h2 : ∀ e, e < d → g e ≤ f e) :
    ∀ e, ∑ i ∈ Finset.range (e / d + 1), g (e - i * d) ≤ f e := by
  intro e
  induction e using Nat.strong_induction_on with
  | h e ih =>
      by_cases hde : d ≤ e
      · rw [telescope_sum_split (g := g) hd hde]
        have hdpos : 0 < d := hd
        have hepos : 0 < e := lt_of_lt_of_le hdpos hde
        exact (Nat.add_le_add_left (ih (e - d) (Nat.sub_lt hepos hdpos)) (g e)).trans
          (h1 e hde)
      · have he_lt : e < d := Nat.lt_of_not_ge hde
        have hdiv : e / d = 0 := Nat.div_eq_of_lt he_lt
        simp [hdiv, h2 e he_lt]

private def S (d : ℕ) (g : ℕ → ℕ) (e : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (e / d + 1), g (e - i * d)

private def iterS (d : ℕ) : ℕ → (ℕ → ℕ) → ℕ → ℕ
  | 0, g => g
  | r + 1, g => S d (iterS d r g)

@[simp] private lemma iterS_zero (d : ℕ) (g : ℕ → ℕ) :
    iterS d 0 g = g := rfl

@[simp] private lemma iterS_succ (d r : ℕ) (g : ℕ → ℕ) :
    iterS d (r + 1) g = S d (iterS d r g) := rfl

private lemma S_chain_step {m d : ℕ} (hd : 1 ≤ d) {f : ℕ → ℕ → ℕ}
    (hstep : ∀ k < m, (∀ e, d ≤ e → f (k+1) e + f k (e - d) ≤ f k e) ∧
      (∀ e, e < d → f (k+1) e ≤ f k e))
    {k : ℕ} (hk : k < m) :
    ∀ e, S d (f (k + 1)) e ≤ f k e := by
  simpa [S] using telescope_sum (d := d) hd (hstep k hk).1 (hstep k hk).2

private lemma iterS_chain_le {m d : ℕ} (hd : 1 ≤ d) {f : ℕ → ℕ → ℕ}
    (hstep : ∀ k < m, (∀ e, d ≤ e → f (k+1) e + f k (e - d) ≤ f k e) ∧
      (∀ e, e < d → f (k+1) e ≤ f k e)) :
    ∀ r, r ≤ m → ∀ e, iterS d r (f m) e ≤ f (m - r) e := by
  intro r
  induction r with
  | zero =>
      intro _hr e
      simp
  | succ r ih =>
      intro hr e
      have hrle : r ≤ m := by omega
      let k : ℕ := m - (r + 1)
      have hk : k < m := by omega
      have hk1 : k + 1 = m - r := by omega
      have hmonoS : S d (iterS d r (f m)) e ≤ S d (f (m - r)) e := by
        dsimp [S]
        apply Finset.sum_le_sum
        intro i _hi
        exact ih hrle (e - i * d)
      calc
        iterS d (r + 1) (f m) e = S d (iterS d r (f m)) e := rfl
        _ ≤ S d (f (m - r)) e := hmonoS
        _ = S d (f (k + 1)) e := by rw [← hk1]
        _ ≤ f k e := S_chain_step hd hstep hk e
        _ = f (m - (r + 1)) e := rfl

private lemma sum_range_sub_add_choose (T r : ℕ) :
    (∑ i ∈ Finset.range (T + 1), (T - i + r).choose r) =
      (T + r + 1).choose (r + 1) := by
  calc
    (∑ i ∈ Finset.range (T + 1), (T - i + r).choose r)
        = ∑ i ∈ Finset.range (T + 1), ((T + 1) - 1 - i + r).choose r := by
          simp
    _ = ∑ i ∈ Finset.range (T + 1), (i + r).choose r := by
          exact Finset.sum_range_reflect (fun j => (j + r).choose r) (T + 1)
    _ = (T + r + 1).choose (r + 1) := Nat.sum_range_add_choose T r

private lemma sub_mul_add_eq {e0 T i d : ℕ} (hi : i ≤ T) :
    e0 + T * d - i * d = e0 + (T - i) * d := by
  calc
    e0 + T * d - i * d = e0 + (T * d - i * d) := by
      rw [Nat.add_sub_assoc (Nat.mul_le_mul_right d hi)]
    _ = e0 + (T - i) * d := by rw [Nat.sub_mul]

private lemma le_div_of_mul_le {a b c : ℕ} (hc : 0 < c) (h : a * c ≤ b) :
    a ≤ b / c := by
  exact (Nat.le_div_iff_mul_le hc).2 h

private lemma iterS_lower {d B e0 : ℕ} (hd : 1 ≤ d) {g : ℕ → ℕ}
    (hB : ∀ e, e0 ≤ e → B ≤ g e) :
    ∀ r T, B * (T + r).choose r ≤ iterS d r g (e0 + T * d) := by
  intro r
  induction r with
  | zero =>
      intro T
      simpa using hB (e0 + T * d) (Nat.le_add_right e0 (T * d))
  | succ r ih =>
      intro T
      have hdpos : 0 < d := hd
      have hTdiv : T ≤ (e0 + T * d) / d := by
        apply le_div_of_mul_le hdpos
        exact Nat.le_add_left (T * d) e0
      have hsubset : Finset.range (T + 1) ⊆ Finset.range ((e0 + T * d) / d + 1) := by
        intro i hi
        rw [Finset.mem_range] at hi ⊢
        omega
      calc
        B * (T + (r + 1)).choose (r + 1)
            = B * (∑ i ∈ Finset.range (T + 1), (T - i + r).choose r) := by
              rw [show T + (r + 1) = T + r + 1 by omega, sum_range_sub_add_choose T r]
        _ = ∑ i ∈ Finset.range (T + 1), B * (T - i + r).choose r := by
              rw [Finset.mul_sum]
        _ ≤ ∑ i ∈ Finset.range (T + 1), iterS d r g (e0 + T * d - i * d) := by
              apply Finset.sum_le_sum
              intro i hi
              have hiT : i ≤ T := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
              rw [sub_mul_add_eq (e0 := e0) (d := d) hiT]
              exact ih (T - i)
        _ ≤ ∑ i ∈ Finset.range ((e0 + T * d) / d + 1),
              iterS d r g (e0 + T * d - i * d) := by
              exact Finset.sum_le_sum_of_subset_of_nonneg hsubset (by
                intro x _hx _hnot
                exact Nat.zero_le _)
        _ = iterS d (r + 1) g (e0 + T * d) := rfl

private lemma le_pow_of_choose_bound {m d B e0 : ℕ}
    (hchoose : ∀ T, B * (T + m).choose m ≤ (e0 + T * d + m).choose m) :
    B ≤ d ^ m := by
  have hseq : ∀ T : ℕ,
      (B : ℝ) ≤ (((e0 + T * d + m : ℕ) : ℝ) / ((T + 1 : ℕ) : ℝ)) ^ m := by
    intro T
    have hchooseR : (B : ℝ) * ((T + m).choose m : ℝ) ≤
        ((e0 + T * d + m).choose m : ℝ) := by
      exact_mod_cast hchoose T
    have hlower : (((T + 1 : ℕ) : ℝ) ^ m) / (m.factorial : ℝ) ≤
        ((T + m).choose m : ℝ) := by
      have h := Nat.pow_le_choose (α := ℝ) m (T + m)
      have htm : T + m + 1 - m = T + 1 := by omega
      simpa [htm, Nat.cast_pow] using h
    have hupper : ((e0 + T * d + m).choose m : ℝ) ≤
        (((e0 + T * d + m : ℕ) : ℝ) ^ m) / (m.factorial : ℝ) := by
      simpa [Nat.cast_pow] using
        (Nat.choose_le_pow_div (α := ℝ) m (e0 + T * d + m))
    have hfacpos : (0 : ℝ) < (m.factorial : ℝ) := by positivity
    have hdiv : ((B : ℝ) * (((T + 1 : ℕ) : ℝ) ^ m)) / (m.factorial : ℝ) ≤
        (((e0 + T * d + m : ℕ) : ℝ) ^ m) / (m.factorial : ℝ) := by
      calc
        ((B : ℝ) * (((T + 1 : ℕ) : ℝ) ^ m)) / (m.factorial : ℝ)
            = (B : ℝ) * ((((T + 1 : ℕ) : ℝ) ^ m) / (m.factorial : ℝ)) := by ring
        _ ≤ (B : ℝ) * ((T + m).choose m : ℝ) := by
              exact mul_le_mul_of_nonneg_left hlower (by positivity)
        _ ≤ ((e0 + T * d + m).choose m : ℝ) := hchooseR
        _ ≤ (((e0 + T * d + m : ℕ) : ℝ) ^ m) / (m.factorial : ℝ) := hupper
    have hpow : (B : ℝ) * (((T + 1 : ℕ) : ℝ) ^ m) ≤
        (((e0 + T * d + m : ℕ) : ℝ) ^ m) := by
      exact (div_le_div_iff_of_pos_right hfacpos).mp hdiv
    have hdenpos : 0 < (((T + 1 : ℕ) : ℝ) ^ m) := by positivity
    rw [div_pow]
    rw [le_div_iff₀' hdenpos]
    simpa [mul_comm] using hpow
  have hratio : Tendsto (fun T : ℕ =>
      ((e0 + T * d + m : ℕ) : ℝ) / ((T + 1 : ℕ) : ℝ)) atTop (𝓝 (d : ℝ)) := by
    convert (tendsto_add_mul_div_add_mul_atTop_nhds (𝕜 := ℝ)
      ((e0 + m : ℕ) : ℝ) (1 : ℝ) (d : ℝ) (d := (1 : ℝ)) one_ne_zero) using 1
    · ext T
      norm_num [Nat.cast_add, Nat.cast_mul]
      ring
    · norm_num
  have hBleR : (B : ℝ) ≤ (d : ℝ) ^ m := by
    exact ge_of_tendsto (hratio.pow m) (Eventually.of_forall hseq)
  exact_mod_cast hBleR

/-- **Iterated telescope + eventual lower bound.** If a chain
`f 0, f 1, …, f m` of functions satisfies the step inequality at every stage,
`f 0 ≤ (· + n).choose n`, and the final `f m` is monotone and eventually
`≥ B`, then `B ≤ d ^ m` — the sharp lattice-count comparison. Stated in the
exact form consumed by the assembly. -/
theorem final_bound_of_chain {m d B e₀ : ℕ} (hd : 1 ≤ d)
    {f : ℕ → ℕ → ℕ}
    (hstep : ∀ k < m, (∀ e, d ≤ e → f (k+1) e + f k (e - d) ≤ f k e) ∧
      (∀ e, e < d → f (k+1) e ≤ f k e))
    (h0 : ∀ e, f 0 e ≤ (e + m).choose m)
    (hB : ∀ e, e₀ ≤ e → B ≤ f m e) :
    B ≤ d ^ m := by
  apply le_pow_of_choose_bound (e0 := e₀)
  intro T
  calc
    B * (T + m).choose m ≤ iterS d m (f m) (e₀ + T * d) :=
      iterS_lower hd hB m T
    _ ≤ f (m - m) (e₀ + T * d) :=
      iterS_chain_le hd hstep m le_rfl (e₀ + T * d)
    _ = f 0 (e₀ + T * d) := by rw [Nat.sub_self]
    _ ≤ (e₀ + T * d + m).choose m := h0 (e₀ + T * d)

/-- **Exhaustion.** If all truncation images have dimension `≤ B`, the quotient
is finite-dimensional of dimension `≤ B`. -/
theorem finiteDimensional_of_phi_bounded
    (J : Ideal (MvPolynomial (Fin n) K)) (B : ℕ)
    (hB : ∀ e, phi J e ≤ B) :
    FiniteDimensional K (MvPolynomial (Fin n) K ⧸ J) ∧
      Module.finrank K (MvPolynomial (Fin n) K ⧸ J) ≤ B := by
  classical
  let s : Finset ℕ := (Finset.range (B + 1)).filter (fun r => ∃ e, phi J e = r)
  have hsne : s.Nonempty := by
    refine ⟨phi J 0, ?_⟩
    simp [s, hB 0]
  let M : ℕ := s.max' hsne
  have hMmem : M ∈ s := Finset.max'_mem s hsne
  rcases (Finset.mem_filter.mp hMmem).2 with ⟨e0, he0M⟩
  have hmax : ∀ e, phi J e ≤ M := by
    intro e
    have hemem : phi J e ∈ s := by
      simp [s, hB e]
    exact Finset.le_max' s (phi J e) hemem
  have htop : truncImage J e0 = ⊤ := by
    rw [eq_top_iff]
    intro x _hx
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
    by_cases hp : p.totalDegree ≤ e0
    · exact (truncImage_mono J hp)
        ⟨p, (MvPolynomial.mem_restrictTotalDegree (σ := Fin n) (R := K)
          (m := p.totalDegree) p).mpr le_rfl, rfl⟩
    · have he0le : e0 ≤ p.totalDegree := Nat.le_of_not_ge hp
      have hle : truncImage J e0 ≤ truncImage J p.totalDegree := truncImage_mono J he0le
      have hfinle : Module.finrank K (truncImage J p.totalDegree) ≤
          Module.finrank K (truncImage J e0) := by
        dsimp [phi] at he0M hmax
        rw [he0M]
        exact hmax p.totalDegree
      have heq : truncImage J e0 = truncImage J p.totalDegree :=
        Submodule.eq_of_le_of_finrank_le hle hfinle
      rw [heq]
      exact ⟨p, (MvPolynomial.mem_restrictTotalDegree (σ := Fin n) (R := K)
        (m := p.totalDegree) p).mpr le_rfl, rfl⟩
  haveI htopFinite : FiniteDimensional K (⊤ : Submodule K (MvPolynomial (Fin n) K ⧸ J)) := by
    rw [← htop]
    infer_instance
  haveI hquotFinite : FiniteDimensional K (MvPolynomial (Fin n) K ⧸ J) :=
    (Submodule.topEquiv : (⊤ : Submodule K (MvPolynomial (Fin n) K ⧸ J)) ≃ₗ[K]
      MvPolynomial (Fin n) K ⧸ J).finiteDimensional
  refine ⟨inferInstance, ?_⟩
  rw [← finrank_top K (MvPolynomial (Fin n) K ⧸ J), ← htop]
  dsimp [phi] at hB
  exact hB e0

end
