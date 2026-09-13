import AssertBytes240.Algebra.ParamSystem
import AssertBytes240.Algebra.GradeDescent

/-!
# T2-W1a — Hilbert function of a homogeneous ideal: eventual polynomiality

Defines the concrete homogeneous Hilbert function `HF` and proves the exact
regular-step identity, saturation invariance, eventual polynomiality,
dimension bridge, and leading-coefficient positivity needed by the degree
calculus.
-/

open MvPolynomial Filter

noncomputable section

variable {K : Type*} [Field K] {n : ℕ}

/-- Degree-`e` Hilbert function value of `R ⧸ I`: dimension of the image of the
degree-`e` homogeneous forms. -/
def HF (I : Ideal (MvPolynomial (Fin n) K)) (e : ℕ) : ℕ :=
  Module.finrank K
    ((homogeneousSubmodule (Fin n) K e).map (Ideal.Quotient.mkₐ K I).toLinearMap)

/-- Concrete homogeneity: an ideal containing all homogeneous components of its
members. -/
def IsHomog (I : Ideal (MvPolynomial (Fin n) K)) : Prop :=
  ∀ p ∈ I, ∀ e : ℕ, homogeneousComponent e p ∈ I

/-- Saturation of `I` at the irrelevant ideal (union of the colon ideals by
powers of the ideal of variables). -/
def sat (I : Ideal (MvPolynomial (Fin n) K)) : Ideal (MvPolynomial (Fin n) K) :=
  ⨆ k : ℕ, I.colon ((Ideal.span (Set.range (X : Fin n → MvPolynomial (Fin n) K)) ^ k) : Ideal _)

/-! ### Helpers for the exact step identity (graded analogue of `phi_step`). -/

/-- Image of the degree-`e` homogeneous forms in `R ⧸ I`. -/
def hfImg (I : Ideal (MvPolynomial (Fin n) K)) (e : ℕ) :
    Submodule K (MvPolynomial (Fin n) K ⧸ I) :=
  (homogeneousSubmodule (Fin n) K e).map (Ideal.Quotient.mkₐ K I).toLinearMap

theorem HF_eq_finrank_hfImg (I : Ideal (MvPolynomial (Fin n) K)) (e : ℕ) :
    HF I e = Module.finrank K (hfImg I e) := rfl

instance homogeneousSubmodule_finiteDimensional (e : ℕ) :
    FiniteDimensional K (homogeneousSubmodule (Fin n) K e) := by
  have hle : homogeneousSubmodule (Fin n) K e ≤ restrictTotalDegree (Fin n) K e := by
    intro p hp
    rw [mem_restrictTotalDegree]
    exact ((mem_homogeneousSubmodule e p).mp hp).totalDegree_le
  exact Submodule.finiteDimensional_of_le hle

instance hfImg_finiteDimensional (I : Ideal (MvPolynomial (Fin n) K)) (e : ℕ) :
    FiniteDimensional K (hfImg I e) := by
  dsimp [hfImg]; infer_instance

/-
Homogeneous component of a product by a homogeneous factor: for `f` homogeneous
of degree `d` and `d ≤ e`, the degree-`e` component of `f * g` is `f` times the
degree-`(e - d)` component of `g`.
-/
theorem homogeneousComponent_mul_left {f : MvPolynomial (Fin n) K} {d : ℕ}
    (hf : f.IsHomogeneous d) (g : MvPolynomial (Fin n) K) {e : ℕ} (hde : d ≤ e) :
    homogeneousComponent e (f * g) = f * homogeneousComponent (e - d) g := by
  ext c;
  by_cases hc : c.degree = e <;> simp_all +decide [ MvPolynomial.coeff_mul, MvPolynomial.coeff_homogeneousComponent ];
  · refine' Finset.sum_congr rfl fun x hx => _;
    by_cases h : x.1.degree = d <;> simp_all +decide [ Finsupp.degree ];
    · intro h';
      contrapose! h';
      rw [ ← hc, ← h, ← hx ];
      refine' eq_tsub_of_add_eq _;
      rw [ add_comm, Finset.sum_subset ( show ( x.1 + x.2 |> Finsupp.support ) ⊆ x.1.support ∪ x.2.support from fun i hi => by by_cases hi1 : x.1 i = 0 <;> by_cases hi2 : x.2 i = 0 <;> aesop ) ] ; simp +decide [ Finset.sum_add_distrib ];
      · rw [ ← Finset.sum_subset ( Finset.subset_union_left ), ← Finset.sum_subset ( Finset.subset_union_right ) ] <;> aesop;
      · simp +contextual [ Finsupp.mem_support_iff ];
    · contrapose! h;
      convert hf h.2.1 using 1;
      simp +decide [ Finsupp.weight ];
      simp +decide [ Finsupp.linearCombination_apply, Finsupp.sum ];
  · refine' Eq.symm ( Finset.sum_eq_zero fun x hx => _ );
    split_ifs <;> simp_all +decide [ Finset.mem_antidiagonal, Finsupp.degree ];
    contrapose! hc;
    have := hf hc.1; simp_all +decide [ ← hx, Finsupp.sum_add_index' ] ;
    simp_all +decide [ Finsupp.weight, Finset.sum_add_distrib ];
    simp_all +decide [ Finsupp.linearCombination_apply, Finsupp.sum ];
    rw [ ← Finset.sum_subset ( show x.1.support ⊆ ( x.1 + x.2 ).support from fun i hi => by aesop ), ← Finset.sum_subset ( show x.2.support ⊆ ( x.1 + x.2 ).support from fun i hi => by aesop ) ] <;> simp_all +decide [ Finset.sum_add_distrib ]

/-
Multiplying a degree-`(e-d)` class by the class of a homogeneous degree-`d`
form lands in the degree-`e` piece.
-/
theorem mul_mem_hfImg
    (I : Ideal (MvPolynomial (Fin n) K)) {f : MvPolynomial (Fin n) K} {d : ℕ}
    (hf : f.IsHomogeneous d) {e : ℕ} (hde : d ≤ e)
    {x : MvPolynomial (Fin n) K ⧸ I} (hx : x ∈ hfImg I (e - d)) :
    (Ideal.Quotient.mk I f) * x ∈ hfImg I e := by
  obtain ⟨ p, hp, rfl ⟩ := hx;
  refine' ⟨ f * p, _, _ ⟩ <;> simp_all +decide [ homogeneousSubmodule ];
  convert hf.mul hp using 1 ; rw [ Nat.add_sub_of_le hde ]

/-
The multiplication-by-`f` map on graded pieces is injective when `f` is a
nonzerodivisor mod `I`.
-/
theorem mul_hfImg_injective
    (I : Ideal (MvPolynomial (Fin n) K)) {f : MvPolynomial (Fin n) K} {d : ℕ}
    (hf : f.IsHomogeneous d) {e : ℕ} (hde : d ≤ e)
    (hreg : IsSMulRegular (MvPolynomial (Fin n) K ⧸ I) f) :
    Function.Injective
      (((LinearMap.mulLeft K (Ideal.Quotient.mk I f)).domRestrict (hfImg I (e - d))).codRestrict
        (hfImg I e) (fun x => mul_mem_hfImg I hf hde x.2)) := by
  intro x y hxy;
  rw [ Subtype.ext_iff ] at hxy ⊢;
  convert hreg _ using 1;
  convert hxy using 1

theorem hfImg_map_factor
    (J H : Ideal (MvPolynomial (Fin n) K)) (hJH : J ≤ H) (e : ℕ) :
    (hfImg J e).map (Ideal.Quotient.factorₐ K hJH).toLinearMap = hfImg H e := by
  ext; simp [hfImg]

/-
The kernel of the projection to `R ⧸ (I ⊔ ⟨f⟩)` restricted to the degree-`e`
image is EXACTLY the image of multiplication by `f` (uses homogeneity of `I`
and `f`).
-/
theorem ker_projection_eq_mul_range
    (I : Ideal (MvPolynomial (Fin n) K)) (hI : IsHomog I)
    {f : MvPolynomial (Fin n) K} {d : ℕ} (hf : f.IsHomogeneous d) {e : ℕ} (hde : d ≤ e) :
    LinearMap.range
      (((LinearMap.mulLeft K (Ideal.Quotient.mk I f)).domRestrict (hfImg I (e - d))).codRestrict
        (hfImg I e) (fun x => mul_mem_hfImg I hf hde x.2))
      = LinearMap.ker
        (((Ideal.Quotient.factorₐ K (show I ≤ I ⊔ Ideal.span {f} from le_sup_left)).toLinearMap).domRestrict
          (hfImg I e)) := by
  ext y;
  constructor <;> intro hy;
  · obtain ⟨ x, hx ⟩ := hy;
    obtain ⟨ p, hp, hp' ⟩ := x.2;
    rw [ ← hx ];
    simp +decide [ hp', Ideal.Quotient.eq_zero_iff_mem.mpr ( Ideal.mem_sup_right ( Ideal.mem_span_singleton_self f ) ) ];
  · -- Since $y \in \ker(\pi)$, we have $\pi(y) = 0$, which means $y$ is in the image of $I + \langle f \rangle$.
    obtain ⟨x, hx⟩ : ∃ x : MvPolynomial (Fin n) K, y.val = Ideal.Quotient.mk I x ∧ x ∈ I ⊔ Ideal.span {f} ∧ x.IsHomogeneous e := by
      rcases y with ⟨ y, ⟨ x, hx, rfl ⟩ ⟩;
      refine' ⟨ x, rfl, _, hx ⟩;
      rw [ LinearMap.mem_ker ] at hy;
      erw [ Submodule.Quotient.mk_eq_zero ] at hy;
      exact hy;
    -- Since $x \in I + \langle f \rangle$, we can write $x = i + f * a$ for some $i \in I$ and $a \in R$.
    obtain ⟨i, a, hi, ha⟩ : ∃ i ∈ I, ∃ a : MvPolynomial (Fin n) K, x = i + f * a := by
      rcases Submodule.mem_sup.mp hx.2.1 with ⟨ i, hi, j, hj, rfl ⟩;
      exact ⟨ i, hi, by rcases Ideal.mem_span_singleton.mp hj with ⟨ a, rfl ⟩ ; exact ⟨ a, by ring ⟩ ⟩;
    -- Since $x$ is homogeneous of degree $e$, we have $x = \sum_{e' + d = e} f * a_{e'}$ where $a_{e'}$ is homogeneous of degree $e'$.
    have hx_homogeneous : x = f * homogeneousComponent (e - d) hi + homogeneousComponent e i := by
      have hx_homogeneous : x = homogeneousComponent e (f * hi) + homogeneousComponent e i := by
        rw [ ha, add_comm, ← map_add ];
        rw [ homogeneousComponent_of_mem ];
        rw [ if_pos rfl ];
        convert hx.2.2 using 1 ; rw [ ha ] ; ring;
        exact mem_homogeneousSubmodule e (f * hi + i);
      rw [ hx_homogeneous, homogeneousComponent_mul_left hf hi hde ];
    -- Since $i \in I$, we have $homogeneousComponent e i \in I$.
    have h_homogeneousComponent_i : homogeneousComponent e i ∈ I := by
      exact hI i a e;
    refine' ⟨ ⟨ Ideal.Quotient.mk I ( homogeneousComponent ( e - d ) hi ), _ ⟩, _ ⟩ <;> simp_all +decide [ hfImg ];
    exact ⟨ _, MvPolynomial.homogeneousComponent_isHomogeneous _ _, rfl ⟩;
    ext; simp +decide [ hx_homogeneous, h_homogeneousComponent_i ] ;
    rw [ hx.1, hx_homogeneous ] ; simp +decide [ Ideal.Quotient.eq_zero_iff_mem.mpr h_homogeneousComponent_i ] ;

/-- 1. Exact step identity for a homogeneous nonzerodivisor cut. -/
theorem HF_step_regular
    (I : Ideal (MvPolynomial (Fin n) K)) (hI : IsHomog I)
    {f : MvPolynomial (Fin n) K} {d : ℕ} (hf : f ∈ homogeneousSubmodule (Fin n) K d)
    (hd : 0 < d) (hreg : IsSMulRegular (MvPolynomial (Fin n) K ⧸ I) f) :
    ∀ e, d ≤ e → HF (I ⊔ Ideal.span {f}) e + HF I (e - d) = HF I e := by
  intro e hde
  have hfh : f.IsHomogeneous d := (mem_homogeneousSubmodule d f).mp hf
  simp only [HF_eq_finrank_hfImg]
  set π : hfImg I e →ₗ[K] (MvPolynomial (Fin n) K ⧸ (I ⊔ Ideal.span {f})) :=
    ((Ideal.Quotient.factorₐ K (show I ≤ I ⊔ Ideal.span {f} from le_sup_left)).toLinearMap).domRestrict
      (hfImg I e) with hπdef
  set μ : hfImg I (e - d) →ₗ[K] hfImg I e :=
    (((LinearMap.mulLeft K (Ideal.Quotient.mk I f)).domRestrict (hfImg I (e - d))).codRestrict
        (hfImg I e) (fun x => mul_mem_hfImg I hfh hde x.2)) with hμdef
  have hπrange : LinearMap.range π = hfImg (I ⊔ Ideal.span {f}) e := by
    rw [hπdef, LinearMap.range_domRestrict]
    exact hfImg_map_factor I (I ⊔ Ideal.span {f}) le_sup_left e
  have hμinj : Function.Injective μ := by
    rw [hμdef]; exact mul_hfImg_injective I hfh hde hreg
  have hker : LinearMap.range μ = LinearMap.ker π := by
    rw [hμdef, hπdef]; exact ker_projection_eq_mul_range I hI hfh hde
  have hrn := LinearMap.finrank_range_add_finrank_ker π
  rw [hπrange] at hrn
  have hkereq : Module.finrank K (LinearMap.ker π) = Module.finrank K (hfImg I (e - d)) := by
    rw [← hker, LinearMap.finrank_range_of_inj hμinj]
  rw [hkereq] at hrn
  exact hrn

/-! ### Helpers for saturation. -/

/-- The irrelevant (variables) ideal. -/
def varsIdeal : Ideal (MvPolynomial (Fin n) K) :=
  Ideal.span (Set.range (X : Fin n → MvPolynomial (Fin n) K))

theorem sat_eq_iSup_colon (I : Ideal (MvPolynomial (Fin n) K)) :
    sat I = ⨆ k : ℕ, I.colon ((varsIdeal ^ k : Ideal (MvPolynomial (Fin n) K))) := rfl

/-- A homogeneous form of degree `e` lies in every power `varsIdeal ^ k` with `k ≤ e`. -/
theorem homogeneous_mem_varsIdeal_pow {e k : ℕ} (hk : k ≤ e)
    {p : MvPolynomial (Fin n) K} (hp : p.IsHomogeneous e) :
    p ∈ (varsIdeal ^ k : Ideal (MvPolynomial (Fin n) K)) := by
  have hmem : p ∈ (MvPolynomial.idealOfVars (Fin n) K) ^ k := by
    rw [MvPolynomial.mem_pow_idealOfVars_iff]
    intro x hx
    have hz := hp.coeff_eq_zero (d := x)
    have hxdeg : Finsupp.degree x = e := by
      by_contra h
      exact (MvPolynomial.mem_support_iff.mp hx) (hz h)
    omega
  simpa [MvPolynomial.idealOfVars, varsIdeal] using hmem

/-
`varsIdeal ^ k` is a homogeneous ideal.
-/
theorem isHomog_varsIdeal_pow (k : ℕ) :
    IsHomog (varsIdeal ^ k : Ideal (MvPolynomial (Fin n) K)) := by
  intro p hp e;
  -- By definition of `varsIdeal ^ k`, we know that every monomial in `p` has degree at least `k`.
  have h_deg : ∀ x ∈ p.support, k ≤ Finsupp.degree x := by
    have h_deg : p ∈ (MvPolynomial.idealOfVars (Fin n) K) ^ k := by
      convert hp using 1;
    rw [ MvPolynomial.mem_pow_idealOfVars_iff ] at h_deg ; aesop;
  -- Since the degree of each monomial in `p` is at least `k`, the degree of each monomial in `homogeneousComponent e p` is also at least `k`.
  have h_deg_homogeneous : ∀ x ∈ (homogeneousComponent e p).support, k ≤ Finsupp.degree x := by
    intro x hx; specialize h_deg x; simp_all +decide [ MvPolynomial.coeff_homogeneousComponent ] ;
  rw [ ← MvPolynomial.mem_pow_idealOfVars_iff ] at *;
  convert h_deg_homogeneous using 1

/-
The colon of a homogeneous ideal by a homogeneous ideal is homogeneous.
-/
theorem isHomog_colon {I J : Ideal (MvPolynomial (Fin n) K)}
    (hI : IsHomog I) (hJ : IsHomog J) : IsHomog (I.colon J) := by
  intro r hr e
  simp [Submodule.mem_colon] at hr;
  intro s hs;
  obtain ⟨ s, hs, rfl ⟩ := hs;
  -- Decompose s by its homogeneous components: s = ∑ j ∈ Finset.range (s.totalDegree + 1), homogeneousComponent j s.
  have hs_decomp : s = ∑ j ∈ Finset.range (s.totalDegree + 1), homogeneousComponent j s := by
    exact (sum_homogeneousComponent s).symm;
  -- By definition of homogeneous components, we know that $(homogeneousComponent e r) * (homogeneousComponent j s) = homogeneousComponent (e + j) (r * homogeneousComponent j s)$.
  have h_homogeneous : ∀ j, (homogeneousComponent e r) * (homogeneousComponent j s) = homogeneousComponent (e + j) (r * homogeneousComponent j s) := by
    intro j
    have h_homogeneous : (homogeneousComponent e r) * (homogeneousComponent j s) = homogeneousComponent (e + j) (homogeneousComponent j s * r) := by
      convert homogeneousComponent_mul_left ( show ( homogeneousComponent j s ).IsHomogeneous j from ?_ ) r ( show j ≤ e + j from ?_ ) |> Eq.symm using 1;
      · simp +decide [ mul_comm ];
      · exact homogeneousComponent_isHomogeneous j s;
      · grind;
    rw [ h_homogeneous, mul_comm ];
  convert I.sum_mem fun j ( hj : j ∈ Finset.range ( s.totalDegree + 1 ) ) => hI ( r * homogeneousComponent j s ) ( hr _ ( hJ _ hs j ) ) ( e + j ) using 1;
  simp +decide [ ← h_homogeneous, ← Finset.mul_sum _ _ _, ← Finset.sum_mul, ← hs_decomp ]

/-
The colon ideals `I.colon (varsIdeal ^ k)` are monotone in `k`.
-/
theorem colon_varsIdeal_pow_mono (I : Ideal (MvPolynomial (Fin n) K)) :
    Monotone (fun k : ℕ => I.colon ((varsIdeal ^ k : Ideal (MvPolynomial (Fin n) K)))) := by
  intro m n hmn x hx;
  simp_all +decide [ Submodule.mem_colon ];
  exact fun s hs => hx s ( Ideal.pow_le_pow_right hmn hs )

/-
Noetherian stabilization: the saturation is a single colon ideal.
-/
theorem exists_sat_eq_colon (I : Ideal (MvPolynomial (Fin n) K)) :
    ∃ k : ℕ, sat I = I.colon ((varsIdeal ^ k : Ideal (MvPolynomial (Fin n) K))) := by
  -- Let g : ℕ →o Ideal _ be the monotone chain k ↦ I.colon (varsIdeal^k), packaged as an OrderHom using colon_varsIdeal_pow_mono.
  set g : ℕ →o (Ideal (MvPolynomial (Fin n) K)) := ⟨fun k => I.colon ((varsIdeal ^ k : Ideal (MvPolynomial (Fin n) K))), colon_varsIdeal_pow_mono I⟩
  generalize_proofs at *; (
  -- By the ascending chain condition on ideals in a Noetherian ring, the chain `g k` stabilizes.
  obtain ⟨K, hK⟩ : ∃ K, ∀ m ≥ K, g K = g m := by
    have h_noetherian : IsNoetherianRing (MvPolynomial (Fin n) K) := by
      infer_instance
    generalize_proofs at *; (
    have := h_noetherian.wf.has_min { g k | k : ℕ } ⟨ _, Set.mem_range_self 0 ⟩ ; simp_all +decide [ Set.Nonempty ] ;
    obtain ⟨ K, hK ⟩ := this; use K; intro m hm; exact le_antisymm ( g.monotone hm ) ( by contrapose! hK; tauto ) ;)
  generalize_proofs at *; (
  refine' ⟨ K, le_antisymm _ _ ⟩ <;> simp_all +decide [ sat_eq_iSup_colon ];
  · intro i; specialize hK ( Max.max i K ) ( le_max_right i K ) ; aesop;
  · exact le_iSup_of_le K le_rfl))

theorem le_sat (I : Ideal (MvPolynomial (Fin n) K)) : I ≤ sat I := by
  refine' le_iSup_of_le 0 _;
  simp +decide

/-
The saturation of a homogeneous ideal is homogeneous.
-/
theorem isHomog_sat (I : Ideal (MvPolynomial (Fin n) K)) (hI : IsHomog I) :
    IsHomog (sat I) := by
  obtain ⟨ k, hk ⟩ := exists_sat_eq_colon I; rw [ hk ] ; exact isHomog_colon hI ( isHomog_varsIdeal_pow k ) ;

/-
If `I` and `J` have the same degree-`e` homogeneous parts, their Hilbert
function values at `e` agree.
-/
theorem HF_eq_of_degreePart_eq (I J : Ideal (MvPolynomial (Fin n) K)) (e : ℕ)
    (h : ∀ p ∈ homogeneousSubmodule (Fin n) K e, (p ∈ I ↔ p ∈ J)) :
    HF I e = HF J e := by
  -- By the hypothesis h, the kernels of the quotient maps are equal.
  have h_ker_eq : LinearMap.ker ((Ideal.Quotient.mkₐ K I).toLinearMap.domRestrict (homogeneousSubmodule (Fin n) K e)) = LinearMap.ker ((Ideal.Quotient.mkₐ K J).toLinearMap.domRestrict (homogeneousSubmodule (Fin n) K e)) := by
    ext p;
    rw [ LinearMap.mem_ker, LinearMap.mem_ker ];
    erw [ Ideal.Quotient.eq_zero_iff_mem, Ideal.Quotient.eq_zero_iff_mem ] ; aesop;
  have := LinearMap.finrank_range_add_finrank_ker ( Ideal.Quotient.mkₐ K I |> AlgHom.toLinearMap |> LinearMap.domRestrict <| homogeneousSubmodule ( Fin n ) K e ) ; have := LinearMap.finrank_range_add_finrank_ker ( Ideal.Quotient.mkₐ K J |> AlgHom.toLinearMap |> LinearMap.domRestrict <| homogeneousSubmodule ( Fin n ) K e ) ; simp_all +decide [ hfImg, HF_eq_finrank_hfImg, LinearMap.range_domRestrict ] ;
  rw [ ← h_ker_eq ] at *; simp_all +decide [ LinearMap.range_domRestrict ] ;
  rw [ ← LinearMap.range_domRestrict, ← LinearMap.range_domRestrict ] at * ; linarith!;

/-- A homogeneous ideal has a finite generating set of homogeneous elements with a
common degree bound. -/
theorem exists_homog_gens (J : Ideal (MvPolynomial (Fin n) K)) (hJ : IsHomog J) :
    ∃ (T : Finset (MvPolynomial (Fin n) K)) (D : ℕ),
      Ideal.span (T : Set (MvPolynomial (Fin n) K)) = J ∧
      (∀ t ∈ T, ∃ d, d ≤ D ∧ t.IsHomogeneous d) ∧
      (∀ t ∈ T, t ∈ J) := by
  classical
  obtain ⟨S, hS⟩ : J.FG := IsNoetherian.noetherian J
  refine ⟨S.biUnion (fun s => (Finset.range (s.totalDegree + 1)).image
      (fun j => homogeneousComponent j s)),
    S.sup (fun s => s.totalDegree), ?_, ?_, ?_⟩
  · apply le_antisymm
    · rw [Ideal.span_le]
      intro t ht
      simp only [Finset.coe_biUnion, Finset.coe_image, Finset.coe_range, Set.mem_iUnion,
        Set.mem_image, Set.mem_Iio] at ht
      obtain ⟨s, hs, j, _, rfl⟩ := ht
      exact hJ s (hS ▸ Ideal.subset_span hs) j
    · rw [← hS, Ideal.span_le]
      intro s hs
      have hsum : s = ∑ j ∈ Finset.range (s.totalDegree + 1), homogeneousComponent j s :=
        (sum_homogeneousComponent s).symm
      rw [SetLike.mem_coe, hsum]
      apply Submodule.sum_mem
      intro j hj
      apply Ideal.subset_span
      simp only [Finset.coe_biUnion, Finset.coe_image, Finset.coe_range, Set.mem_iUnion,
        Set.mem_image, Set.mem_Iio]
      exact ⟨s, hs, j, Finset.mem_range.mp hj, rfl⟩
  · intro t ht
    simp only [Finset.mem_biUnion, Finset.mem_image, Finset.mem_range] at ht
    obtain ⟨s, hs, j, hj, rfl⟩ := ht
    refine ⟨j, ?_, homogeneousComponent_isHomogeneous j s⟩
    exact le_trans (Nat.le_of_lt_succ hj) (Finset.le_sup hs)
  · intro t ht
    simp only [Finset.mem_biUnion, Finset.mem_image, Finset.mem_range] at ht
    obtain ⟨s, hs, j, _, rfl⟩ := ht
    exact hJ s (hS ▸ Ideal.subset_span hs) j

/-- Core algebraic step: a high-degree homogeneous form in the span of homogeneous
generators, each of which annihilates `varsIdeal ^ k` into `I`, lies in `I`. -/
theorem mem_of_homog_span_colon
    (I : Ideal (MvPolynomial (Fin n) K)) (k D : ℕ)
    (T : Finset (MvPolynomial (Fin n) K))
    (hTh : ∀ t ∈ T, ∃ d, d ≤ D ∧ t.IsHomogeneous d)
    (hTc : ∀ t ∈ T, t ∈ I.colon ((varsIdeal ^ k : Ideal (MvPolynomial (Fin n) K))))
    {e : ℕ} (he : D + k ≤ e) {p : MvPolynomial (Fin n) K}
    (hp : p.IsHomogeneous e) (hpT : p ∈ Ideal.span (T : Set (MvPolynomial (Fin n) K))) :
    p ∈ I := by
  classical
  have hpT' : p ∈ Submodule.span (MvPolynomial (Fin n) K) (T : Set (MvPolynomial (Fin n) K)) := hpT
  rw [Submodule.mem_span_finset] at hpT'
  obtain ⟨c, _hsupp, hc⟩ := hpT'
  have hpe : p = ∑ t ∈ T, homogeneousComponent e (c t * t) := by
    have hpp : homogeneousComponent e p = p := by
      rw [homogeneousComponent_of_mem ((mem_homogeneousSubmodule e p).mpr hp), if_pos rfl]
    rw [← hpp, ← hc, map_sum]
    apply Finset.sum_congr rfl
    intro t _; simp [smul_eq_mul]
  rw [hpe]
  apply Ideal.sum_mem
  intro t ht
  obtain ⟨d, hdD, hth⟩ := hTh t ht
  have hde : d ≤ e := le_trans hdD (le_trans (Nat.le_add_right D k) he)
  have hcomp : homogeneousComponent e (c t * t) = t * homogeneousComponent (e - d) (c t) := by
    rw [mul_comm (c t) t, homogeneousComponent_mul_left hth (c t) hde]
  rw [hcomp]
  have hb : (homogeneousComponent (e - d) (c t)).IsHomogeneous (e - d) :=
    homogeneousComponent_isHomogeneous (e - d) (c t)
  have hkled : k ≤ e - d := by omega
  have hbmem := homogeneous_mem_varsIdeal_pow hkled hb
  have := (Submodule.mem_colon.mp (hTc t ht)) _ hbmem
  simpa [smul_eq_mul] using this

/-- For `e` large, every degree-`e` form of `sat I` already lies in `I`. -/
theorem sat_degreePart_subset (I : Ideal (MvPolynomial (Fin n) K)) (hI : IsHomog I) :
    ∃ E : ℕ, ∀ e, E ≤ e → ∀ p : MvPolynomial (Fin n) K, p.IsHomogeneous e →
      p ∈ sat I → p ∈ I := by
  obtain ⟨k, hk⟩ := exists_sat_eq_colon I
  obtain ⟨T, D, hspan, hTh, _hTmem⟩ := exists_homog_gens (sat I) (isHomog_sat I hI)
  have hTc : ∀ t ∈ T, t ∈ I.colon ((varsIdeal ^ k : Ideal (MvPolynomial (Fin n) K))) := by
    intro t ht
    have : t ∈ sat I := by rw [← hspan]; exact Ideal.subset_span ht
    rwa [hk] at this
  refine ⟨D + k, fun e he p hp hpsat => ?_⟩
  refine mem_of_homog_span_colon I k D T hTh hTc he hp ?_
  rw [hspan]; exact hpsat

/-- 2. Saturation changes the Hilbert function in only finitely many degrees. -/
theorem HF_saturation_eventually_eq
    (I : Ideal (MvPolynomial (Fin n) K)) (hI : IsHomog I) :
    ∀ᶠ e in atTop, HF (sat I) e = HF I e := by
  obtain ⟨E, hE⟩ := sat_degreePart_subset I hI
  have hIsat : I ≤ sat I := le_sat I
  rw [Filter.eventually_atTop]
  refine ⟨E, fun e he => ?_⟩
  refine HF_eq_of_degreePart_eq (sat I) I e (fun p hp => ?_)
  have hph : p.IsHomogeneous e := (mem_homogeneousSubmodule e p).mp hp
  constructor
  · intro hpsat; exact hE e he p hph hpsat
  · intro hpI; exact hIsat hpI

/-! ### Helpers for eventual polynomiality (theorem 3). -/

/-
The Hilbert function of the whole ring is identically zero.
-/
theorem HF_top (e : ℕ) : HF (⊤ : Ideal (MvPolynomial (Fin n) K)) e = 0 := by
  unfold HF;
  rw [ Module.finrank_zero_iff ];
  constructor;
  rintro ⟨ a, ha ⟩ ⟨ b, hb ⟩;
  exact Subsingleton.elim _ _

/-
Saturation is idempotent.
-/
theorem sat_sat (I : Ideal (MvPolynomial (Fin n) K)) : sat (sat I) = sat I := by
  refine' le_antisymm ( _ : _ ≤ _ ) ( le_sat _ );
  obtain ⟨ k, hk ⟩ := exists_sat_eq_colon I;
  -- It suffices to show (sat I).colon (varsIdeal^a) ≤ I.colon (varsIdeal^(a+k)).
  have h_colon_le : ∀ a : ℕ, (sat I).colon ((varsIdeal ^ a : Ideal (MvPolynomial (Fin n) K))) ≤ I.colon ((varsIdeal ^ (a + k) : Ideal (MvPolynomial (Fin n) K))) := by
    intro a x hx t ht; simp_all +decide [ pow_add, Ideal.mul_mem_left, Ideal.mul_mem_right ] ;
    rw [ Set.mem_smul_set ] at ht; obtain ⟨ u, hu, rfl ⟩ := ht; simp_all +decide [ Submodule.mem_colon ] ;
    refine' Submodule.mul_induction_on hu _ _;
    · simpa only [ mul_assoc ] using hx;
    · exact fun y z hy hz => by simpa only [ mul_add ] using I.add_mem hy hz;
  refine' iSup_le _;
  exact fun a => le_iSup_of_le ( a + k ) ( h_colon_le a )

/-
Antidifference of a rational polynomial: `Δ R = Q` where `Δ R = R(X+1) - R`.
-/
theorem exists_antidiff (Q : Polynomial ℚ) :
    ∃ R : Polynomial ℚ, R.comp (Polynomial.X + 1) - R = Q := by
  induction' Q using Polynomial.induction_on' with Q hQ;
  · case _ h₁ h₂ => obtain ⟨ R₁, hR₁ ⟩ := h₁; obtain ⟨ R₂, hR₂ ⟩ := h₂; exact ⟨ R₁ + R₂, by simpa [ Polynomial.comp_assoc ] using by linear_combination' hR₁ + hR₂ ⟩ ;
  · rename_i n a;
    -- We'll use the fact that $\Delta(x(x-1)\cdots(x-n+1)) = (n+1)x(x-1)\cdots(x-n+1)$.
    have h_delta_factorial : ∀ n : ℕ, ∃ R : Polynomial ℚ, R.comp (.X + 1) - R = Polynomial.X ^ n := by
      intro n
      induction' n using Nat.strong_induction_on with n ih;
      -- Consider the polynomial $R(x) = \frac{x^{n+1}}{n+1}$.
      obtain ⟨R, hR⟩ : ∃ R : Polynomial ℚ, R.comp (Polynomial.X + 1) - R = Polynomial.X ^ n := by
        have h_sum : ∃ S : Polynomial ℚ, S.comp (Polynomial.X + 1) - S = ∑ k ∈ Finset.range n, Polynomial.C (Nat.choose (n + 1) k : ℚ) * Polynomial.X ^ k := by
          choose! R hR using ih;
          use ∑ k ∈ Finset.range n, Polynomial.C (Nat.choose (n + 1) k : ℚ) * R k;
          simp +decide [ ← hR, Polynomial.comp_assoc, Finset.sum_mul _ _ _ ];
          rw [ ← Finset.sum_sub_distrib ] ; exact Finset.sum_congr rfl fun x hx => by rw [ ← mul_sub, hR x ( Finset.mem_range.mp hx ) ] ;
        obtain ⟨ S, hS ⟩ := h_sum;
        use Polynomial.C (1 / (n + 1 : ℚ)) * (Polynomial.X ^ (n + 1) - S);
        simp_all +decide [ Polynomial.comp_assoc, sub_eq_iff_eq_add ];
        refine' Polynomial.funext fun x => _;
        simp +decide [ Polynomial.eval_finset_sum, add_pow ];
        simp +decide [ Finset.sum_range_succ, mul_comm ];
        -- Combine like terms and simplify the expression.
        field_simp
        ring;
      use R;
    obtain ⟨ R, hR ⟩ := h_delta_factorial n; use R * Polynomial.C a; simp_all +decide [ ← Polynomial.C_mul_X_pow_eq_monomial ] ; ring;
    rw [ add_comm, ← hR ] ; ring

/-
Discrete integration: if the forward difference of `g` is eventually a
polynomial, then so is `g`.
-/
theorem eventually_poly_of_fwdDiff (g : ℕ → ℚ) (Q : Polynomial ℚ)
    (h : ∀ᶠ e in atTop, g (e + 1) - g e = Q.eval (e : ℚ)) :
    ∃ P : Polynomial ℚ, ∀ᶠ e in atTop, g e = P.eval (e : ℚ) := by
  -- Use `exists_antidiff` to obtain R : ℚ[X] with R.comp (X+1) - R = Q.
  obtain ⟨R, hR⟩ : ∃ R : Polynomial ℚ, R.comp (Polynomial.X + 1) - R = Q := exists_antidiff Q;
  -- Consider the function $d(e) := g(e) - R(e)$.
  set d : ℕ → ℚ := fun e => g e - R.eval (e : ℚ);
  -- From the hypothesis, eventually (for e ≥ N say) g (e+1) - g e = Q.eval e = R.eval (e+1) - R.eval e, hence d (e+1) = d e eventually.
  obtain ⟨N, hN⟩ : ∃ N, ∀ e ≥ N, d (e + 1) = d e := by
    simp +zetaDelta at *;
    obtain ⟨ N, hN ⟩ := h; use N; intros e he; have := hN e he; have := congr_arg ( Polynomial.eval ( e : ℚ ) ) hR; norm_num at * ; linarith;
  -- So d is eventually constant: there is a constant c = d N with d e = c for all e ≥ N.
  obtain ⟨c, hc⟩ : ∃ c, ∀ e ≥ N, d e = c := by
    exact ⟨ d N, fun e he => Nat.le_induction rfl ( fun k hk ih => hN k hk ▸ ih ) e he ⟩;
  exact ⟨ R + Polynomial.C c, Filter.eventually_atTop.mpr ⟨ N, fun e he => by simpa [ sub_eq_iff_eq_add'.mp ( hc e he ) ] ⟩ ⟩

/-
Base case: with no variables, the Hilbert function is eventually zero.
-/
theorem HF_base_zero [Infinite K] (I : Ideal (MvPolynomial (Fin 0) K)) (hI : IsHomog I) :
    ∃ P : Polynomial ℚ, ∀ᶠ e in atTop, (HF I e : ℚ) = P.eval (e : ℚ) := by
  -- Since $n = 0$, the only polynomials are constants, so the Hilbert function is eventually zero.
  have h_const : ∀ e ≥ 1, (hfImg I e) = ⊥ := by
    intro e he
    have h_const : ∀ p : MvPolynomial (Fin 0) K, p.IsHomogeneous e → p = 0 := by
      intro p hp;
      ext x; simp_all +decide [ Finsupp.degree ] ;
      convert hp.coeff_eq_zero ?_;
      exact ne_of_lt ( lt_of_le_of_lt ( by simp +decide [ Finsupp.degree ] ) he );
    ext x;
    constructor <;> intro hx;
    · obtain ⟨ p, hp, rfl ⟩ := hx; specialize h_const p; aesop;
    · aesop;
  use 0; filter_upwards [ Filter.eventually_ge_atTop 1 ] with e he; simp +decide [ h_const e he, HF_eq_finrank_hfImg ] ;

/-
The variables ideal is maximal.
-/
theorem varsIdeal_isMaximal :
    (varsIdeal : Ideal (MvPolynomial (Fin n) K)).IsMaximal := by
  refine' Ideal.isMaximal_iff.mpr ⟨ _, _ ⟩;
  · rw [ varsIdeal ];
    rw [ Ideal.mem_span_range_iff_exists_fun ];
    exact fun ⟨ c, hc ⟩ => by simpa using congr_arg ( MvPolynomial.eval 0 ) hc;
  · intro J x hJ hx hxJ
    obtain ⟨c, hc⟩ : ∃ c : K, x - MvPolynomial.C c ∈ varsIdeal := by
      use MvPolynomial.constantCoeff x;
      have h_const : ∀ p : MvPolynomial (Fin n) K, p - MvPolynomial.C (MvPolynomial.constantCoeff p) ∈ varsIdeal := by
        intro p
        induction' p using MvPolynomial.induction_on with p hp ih;
        · simp +decide [ MvPolynomial.constantCoeff_C ];
        · convert Ideal.add_mem _ ‹hp - C ( constantCoeff hp ) ∈ varsIdeal› ‹ih - C ( constantCoeff ih ) ∈ varsIdeal› using 1 ; simp +decide [ sub_add_sub_comm ];
        · simp_all +decide [ mul_sub, sub_mul ];
          exact Ideal.mul_mem_left _ _ ( Ideal.subset_span ( Set.mem_range_self _ ) );
      exact h_const x;
    convert J.mul_mem_left ( MvPolynomial.C c⁻¹ ) ( J.sub_mem hxJ ( hJ hc ) ) using 1 ; simp +decide [ hx, sub_eq_iff_eq_add ];
    by_cases hc : c = 0 <;> simp_all +decide [ ← MvPolynomial.C_mul ]

/-
For a proper saturated ideal, the irrelevant (variables) ideal is not an
associated prime of the quotient.
-/
theorem varsIdeal_notMem_associatedPrimes
    (J : Ideal (MvPolynomial (Fin n) K)) (hJsat : sat J = J) (hJne : J ≠ ⊤) :
    (varsIdeal : Ideal (MvPolynomial (Fin n) K)) ∉
      associatedPrimes (MvPolynomial (Fin n) K) (MvPolynomial (Fin n) K ⧸ J) := by
  by_contra h_contra
  obtain ⟨x, hx⟩ : ∃ x : MvPolynomial (Fin n) K ⧸ J, varsIdeal = Submodule.annihilator (Submodule.span (MvPolynomial (Fin n) K) {x}) := by
    obtain ⟨ x, hx ⟩ := h_contra.2; use x; simp_all +decide [ Submodule.mem_annihilator, Submodule.mem_span_singleton ] ;
    grind +suggestions;
  -- Lift x to y : R with x = Ideal.Quotient.mk J y.
  obtain ⟨y, yJ⟩ : ∃ y : MvPolynomial (Fin n) K, Ideal.Quotient.mk J y = x ∧ y ∉ J := by
    obtain ⟨ y, rfl ⟩ := Ideal.Quotient.mk_surjective x; use y; simp +decide [ Ideal.Quotient.eq_zero_iff_mem ] ;
    intro hy_mem_J;
    have h_annihilator : Submodule.annihilator (Submodule.span (MvPolynomial (Fin n) K) {(Ideal.Quotient.mk J) y}) = ⊤ := by
      simp +decide [ Submodule.annihilator_bot, Ideal.Quotient.eq_zero_iff_mem.mpr hy_mem_J ];
    exact h_contra.1.ne_top ( hx.trans h_annihilator );
  -- Now varsIdeal = ann(x) means every r ∈ varsIdeal kills x: r • x = 0, i.e. r * y ∈ J. In particular varsIdeal • y ⊆ J, i.e. for all r ∈ varsIdeal, r * y ∈ J.
  have h_varsIdeal_y : ∀ r ∈ varsIdeal, r * y ∈ J := by
    intro r hr
    have hr_ann : r • x = 0 := by
      rw [hx] at hr;
      rw [ Submodule.mem_annihilator ] at hr;
      exact hr x ( Submodule.mem_span_singleton_self x );
    rw [ ← yJ.1 ] at hr_ann; erw [ Ideal.Quotient.eq_zero_iff_mem ] at hr_ann; aesop;
  -- This says y ∈ J.colon (varsIdeal) = J.colon (varsIdeal^1). Since J.colon (varsIdeal^1) ≤ sat J (le_iSup via sat_eq_iSup_colon, index 1), and sat J = J (hJsat), we get y ∈ J.
  have h_y_in_J : y ∈ J.colon ((varsIdeal ^ 1 : Ideal (MvPolynomial (Fin n) K))) := by
    simp +decide [ Submodule.mem_colon, h_varsIdeal_y ];
    simpa only [ mul_comm ] using h_varsIdeal_y;
  exact yJ.2 ( hJsat ▸ le_iSup ( fun k : ℕ => J.colon ( varsIdeal ^ k : Ideal ( MvPolynomial ( Fin n ) K ) ) ) 1 h_y_in_J )

/-- Existence of a homogeneous linear nonzerodivisor modulo a proper saturated
homogeneous ideal (in at least one variable), by prime avoidance over the space
of linear forms. -/
theorem exists_linear_nzd [Infinite K] {m : ℕ}
    (J : Ideal (MvPolynomial (Fin (m + 1)) K)) (hJhom : IsHomog J)
    (hJsat : sat J = J) (hJne : J ≠ ⊤) :
    ∃ ℓ : MvPolynomial (Fin (m + 1)) K, ℓ ∈ homogeneousSubmodule (Fin (m + 1)) K 1 ∧ ℓ ≠ 0 ∧
      IsSMulRegular (MvPolynomial (Fin (m + 1)) K ⧸ J) ℓ := by
  haveI hnt : Nontrivial (MvPolynomial (Fin (m + 1)) K ⧸ J) :=
    Ideal.Quotient.nontrivial hJne
  have hfin : (associatedPrimes (MvPolynomial (Fin (m + 1)) K)
      (MvPolynomial (Fin (m + 1)) K ⧸ J)).Finite :=
    associatedPrimes.finite _ _
  have hne : (associatedPrimes (MvPolynomial (Fin (m + 1)) K)
      (MvPolynomial (Fin (m + 1)) K ⧸ J)).Nonempty :=
    associatedPrimes.nonempty _ _
  have havoid : ∀ P ∈ hfin.toFinset,
      ¬ (homogeneousSubmodule (Fin (m + 1)) K 1) ≤ Submodule.restrictScalars K P := by
    intro P hP hle
    have hPass := hfin.mem_toFinset.mp hP
    have hvars : (varsIdeal : Ideal (MvPolynomial (Fin (m + 1)) K)) ≤ P := by
      rw [varsIdeal, Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      exact hle (by rw [mem_homogeneousSubmodule]; exact isHomogeneous_X K i)
    have heq : (varsIdeal : Ideal (MvPolynomial (Fin (m + 1)) K)) = P :=
      varsIdeal_isMaximal.eq_of_le hPass.1.ne_top hvars
    exact varsIdeal_notMem_associatedPrimes J hJsat hJne (heq ▸ hPass)
  obtain ⟨ℓ, hℓV, hℓP⟩ :=
    ParamSystem.exists_mem_avoiding_finset
      (homogeneousSubmodule (Fin (m + 1)) K 1) hfin.toFinset havoid
  refine ⟨ℓ, hℓV, ?_, ?_⟩
  · obtain ⟨P, hP⟩ := hne
    intro h0
    exact hℓP P (hfin.mem_toFinset.mpr hP) (h0 ▸ P.zero_mem)
  · exact GradeDescent.isSMulRegular_of_notMem_associatedPrimes
      (fun P hP => hℓP P (hfin.mem_toFinset.mpr hP))

/-
**Graded transfer.** A surjective `K`-algebra map `ψ` between polynomial rings
that carries degree-`e` forms onto degree-`e` forms, whose kernel is contained in
`I`, preserves the Hilbert function value at `e` (between `I` and its image).
-/
theorem HF_transfer {N₁ N₂ : ℕ}
    (ψ : MvPolynomial (Fin N₁) K →ₐ[K] MvPolynomial (Fin N₂) K)
    (hsurj : Function.Surjective ψ)
    (hgraded : ∀ e, (homogeneousSubmodule (Fin N₁) K e).map ψ.toLinearMap
        = homogeneousSubmodule (Fin N₂) K e)
    (I : Ideal (MvPolynomial (Fin N₁) K)) (hker : RingHom.ker ψ ≤ I) (e : ℕ) :
    HF I e = HF (I.map ψ) e := by
  obtain ⟨θ, hθ⟩ : ∃ θ : (MvPolynomial (Fin N₁) K ⧸ I) ≃ₐ[K] (MvPolynomial (Fin N₂) K ⧸ Ideal.map ψ I), ∀ x : MvPolynomial (Fin N₁) K, θ (Ideal.Quotient.mk I x) = Ideal.Quotient.mk (Ideal.map ψ I) (ψ x) := by
    refine' ⟨ _, _ ⟩;
    refine' AlgEquiv.ofBijective ( Ideal.quotientMapₐ _ _ _ ) ⟨ _, _ ⟩;
    exact ψ;
    exact fun x hx => Ideal.mem_comap.mpr ( Ideal.mem_map_of_mem _ hx );
    all_goals simp_all +decide [ Function.Injective, Function.Surjective ];
    · rintro ⟨ a ⟩ ⟨ b ⟩ h;
      erw [ Ideal.Quotient.eq ] at *;
      rw [ Ideal.mem_map_iff_of_surjective ψ hsurj ] at h;
      obtain ⟨ x, hx, hx' ⟩ := h;
      exact hker ( show ψ ( a - b - x ) = 0 from by simp +decide [ hx', sub_eq_iff_eq_add ] ) |> fun h => by simpa using I.add_mem h hx;
    · rintro ⟨ b ⟩;
      obtain ⟨ a, rfl ⟩ := hsurj b; exact ⟨ Ideal.Quotient.mk I a, rfl ⟩ ;
  have h_map_eq : Submodule.map (Ideal.Quotient.mkₐ K (Ideal.map ψ I)).toLinearMap (homogeneousSubmodule (Fin N₂) K e) = Submodule.map θ.toLinearMap (Submodule.map (Ideal.Quotient.mkₐ K I).toLinearMap (homogeneousSubmodule (Fin N₁) K e)) := by
    rw [ ← hgraded e ];
    ext; simp [hθ];
  rw [ HF_eq_finrank_hfImg, HF_eq_finrank_hfImg, hfImg, hfImg, h_map_eq ];
  exact LinearEquiv.finrank_eq ( θ.toLinearEquiv.submoduleMap ( Submodule.map ( Ideal.Quotient.mkₐ K I ).toLinearMap ( homogeneousSubmodule ( Fin N₁ ) K e ) ) ) ▸ rfl

/-
The image of a homogeneous ideal under a surjective graded algebra map is
homogeneous.
-/
theorem isHomog_map_graded {N₁ N₂ : ℕ}
    (ψ : MvPolynomial (Fin N₁) K →ₐ[K] MvPolynomial (Fin N₂) K)
    (hsurj : Function.Surjective ψ)
    (hgraded : ∀ e, (homogeneousSubmodule (Fin N₁) K e).map ψ.toLinearMap
        = homogeneousSubmodule (Fin N₂) K e)
    (I : Ideal (MvPolynomial (Fin N₁) K)) (hI : IsHomog I) :
    IsHomog (I.map ψ) := by
  intro q hq e
  obtain ⟨p, hpI, rfl⟩ : ∃ p : MvPolynomial (Fin N₁) K, p ∈ I ∧ ψ p = q := by
    rw [ Ideal.mem_map_iff_of_surjective _ hsurj ] at hq; tauto;
  have h_comm : (homogeneousComponent e (ψ p)) = ∑ e' ∈ Finset.range (p.totalDegree + 1), ψ (homogeneousComponent e' p |> homogeneousComponent e) := by
    have h_comm : (homogeneousComponent e (ψ p)) = (homogeneousComponent e (∑ e' ∈ Finset.range (p.totalDegree + 1), ψ (homogeneousComponent e' p))) := by
      rw [ ← map_sum, sum_homogeneousComponent ];
    rw [ h_comm, map_sum ];
    refine' Finset.sum_congr rfl fun e' he' => _;
    have h_comm : ψ (homogeneousComponent e' p) ∈ homogeneousSubmodule (Fin N₂) K e' := by
      exact hgraded e' ▸ Submodule.mem_map_of_mem ( show homogeneousComponent e' p ∈ homogeneousSubmodule ( Fin N₁ ) K e' from by simp +decide [ homogeneousComponent_isHomogeneous ] );
    rw [ homogeneousComponent_of_mem h_comm, homogeneousComponent_of_mem ( show ( homogeneousComponent e' p ) ∈ homogeneousSubmodule ( Fin N₁ ) K e' from by rw [ mem_homogeneousSubmodule ] ; exact homogeneousComponent_isHomogeneous e' p ) ] ; aesop;
  rw [h_comm];
  refine' Ideal.sum_mem _ fun e' he' => _;
  exact Ideal.mem_map_of_mem _ ( hI _ ( hI _ hpI _ ) _ )

/-
An algebra map sending each variable to a homogeneous degree-1 form preserves
homogeneity degree.
-/
theorem isHomogeneous_aeval_of_X_homog {N : ℕ}
    (φ : MvPolynomial (Fin N) K →ₐ[K] MvPolynomial (Fin N) K)
    (hφ : ∀ i, (φ (X i)).IsHomogeneous 1) {e : ℕ} {p : MvPolynomial (Fin N) K}
    (hp : p.IsHomogeneous e) : (φ p).IsHomogeneous e := by
  have h_aeval : p = MvPolynomial.aeval (fun i => MvPolynomial.X i) p := by
    simp +decide;
  convert hp.aeval ( fun i => ?_ ) using 1;
  rotate_left;
  exact Fin N;
  exact K;
  exact inferInstance;
  exact 1;
  exact inferInstance;
  exact φ ( MvPolynomial.X i );
  simp +decide [ hφ ];
  convert Iff.rfl;
  ext; simp +decide [ MvPolynomial.aeval_def ] ;

/-
If an algebra automorphism and its inverse send variables to homogeneous
degree-1 forms, it is graded.
-/
theorem gradedMap_of_X_homog {N : ℕ}
    (φ : MvPolynomial (Fin N) K ≃ₐ[K] MvPolynomial (Fin N) K)
    (hφ : ∀ i, (φ (X i)).IsHomogeneous 1)
    (hφinv : ∀ i, (φ.symm (X i)).IsHomogeneous 1) :
    ∀ e, (homogeneousSubmodule (Fin N) K e).map φ.toAlgHom.toLinearMap
      = homogeneousSubmodule (Fin N) K e := by
  intro e;
  refine' le_antisymm _ _;
  · intro y hy; obtain ⟨ p, hp, rfl ⟩ := hy; exact isHomogeneous_aeval_of_X_homog φ.toAlgHom hφ ( by simpa [ mem_homogeneousSubmodule ] using hp ) ;
  · intro q hq;
    use φ.symm q;
    convert isHomogeneous_aeval_of_X_homog ( φ.symm.toAlgHom ) hφinv ( show q.IsHomogeneous e from by simpa [ mem_homogeneousSubmodule ] using hq ) using 1;
    simp +decide [ mem_homogeneousSubmodule ]

/-- Substitution automorphism: for a form `∑ C(cc i) * X i` whose `X 0`-coefficient
`cc 0` is a unit, there is an automorphism (graded on variables) sending it to `X 0`. -/
theorem exists_subst_equiv {N : ℕ} (cc : Fin (N + 1) → K) (h0 : cc 0 ≠ 0) :
    ∃ σ : MvPolynomial (Fin (N + 1)) K ≃ₐ[K] MvPolynomial (Fin (N + 1)) K,
      (∀ i, (σ (X i)).IsHomogeneous 1) ∧ (∀ i, (σ.symm (X i)).IsHomogeneous 1) ∧
      σ (∑ i, C (cc i) * X i) = X 0 := by
  classical
  set L : MvPolynomial (Fin (N+1)) K := ∑ i, C (cc i) * X i with hL
  set r : MvPolynomial (Fin (N+1)) K := ∑ i ∈ Finset.univ.erase 0, C (cc i) * X i with hr
  set v : MvPolynomial (Fin (N+1)) K := (cc 0)⁻¹ • (X 0 - r) with hv
  set gA : Fin (N+1) → MvPolynomial (Fin (N+1)) K := Function.update (fun i => X i) 0 L with hgA
  set gA' : Fin (N+1) → MvPolynomial (Fin (N+1)) K := Function.update (fun i => X i) 0 v with hgA'
  have hLr : L = C (cc 0) * X 0 + r := by
    rw [hL, hr, ← Finset.add_sum_erase _ _ (Finset.mem_univ 0)]
  have hevalL : ∀ w : MvPolynomial (Fin (N+1)) K,
      aeval (Function.update (fun i => X i) 0 w) L = C (cc 0) * w + r := by
    intro w
    rw [hL, map_sum, ← Finset.add_sum_erase _ _ (Finset.mem_univ 0)]
    congr 1
    · rw [map_mul, aeval_C, aeval_X, Function.update_self, MvPolynomial.algebraMap_eq]
    · apply Finset.sum_congr rfl
      intro i hi
      rw [map_mul, aeval_C, aeval_X, Function.update_of_ne (Finset.ne_of_mem_erase hi),
        MvPolynomial.algebraMap_eq]
  have hgAr : aeval gA r = r := by
    rw [hr, map_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [map_mul, aeval_C, aeval_X, hgA, Function.update_of_ne (Finset.ne_of_mem_erase hi),
      MvPolynomial.algebraMap_eq]
  have hgA0 : gA 0 = L := by rw [hgA, Function.update_self]
  have hA'L : aeval gA' L = X 0 := by
    rw [hevalL v, hv, mul_smul_comm, ← smul_eq_C_mul, smul_smul, inv_mul_cancel₀ h0, one_smul,
      sub_add_cancel]
  have hAv : aeval gA v = X 0 := by
    rw [hv, map_smul, map_sub, hgAr, aeval_X, hgA0, hLr, add_sub_cancel_right, ← smul_eq_C_mul,
      smul_smul, inv_mul_cancel₀ h0, one_smul]
  have hLhom : L ∈ homogeneousSubmodule (Fin (N+1)) K 1 := by
    rw [hL]; apply Submodule.sum_mem
    intro i _; rw [mem_homogeneousSubmodule]; exact isHomogeneous_C_mul_X _ _
  have hrhom : r ∈ homogeneousSubmodule (Fin (N+1)) K 1 := by
    rw [hr]; apply Submodule.sum_mem
    intro i _; rw [mem_homogeneousSubmodule]; exact isHomogeneous_C_mul_X _ _
  have hvhom : v ∈ homogeneousSubmodule (Fin (N+1)) K 1 := by
    rw [hv]; apply Submodule.smul_mem
    apply Submodule.sub_mem
    · rw [mem_homogeneousSubmodule]; exact isHomogeneous_X K 0
    · exact hrhom
  set σ : MvPolynomial (Fin (N+1)) K ≃ₐ[K] MvPolynomial (Fin (N+1)) K :=
    AlgEquiv.ofAlgHom (aeval gA') (aeval gA)
      (by
        apply MvPolynomial.algHom_ext
        intro k
        rw [AlgHom.comp_apply, aeval_X, AlgHom.id_apply]
        rcases eq_or_ne k 0 with rfl | hk
        · rw [hgA0, hA'L]
        · rw [hgA, Function.update_of_ne hk, aeval_X, hgA', Function.update_of_ne hk])
      (by
        apply MvPolynomial.algHom_ext
        intro k
        rw [AlgHom.comp_apply, aeval_X, AlgHom.id_apply]
        rcases eq_or_ne k 0 with rfl | hk
        · rw [hgA', Function.update_self, hAv]
        · rw [hgA', Function.update_of_ne hk, aeval_X, hgA, Function.update_of_ne hk]) with hσ
  refine ⟨σ, ?_, ?_, ?_⟩
  · intro i
    have hsi : σ (X i) = gA' i := by rw [hσ, AlgEquiv.ofAlgHom_apply, aeval_X]
    rw [hsi, hgA']
    rcases eq_or_ne i 0 with rfl | hi
    · rw [Function.update_self]; exact (mem_homogeneousSubmodule _ _).mp hvhom
    · rw [Function.update_of_ne hi]; exact isHomogeneous_X K i
  · intro i
    have hsi : σ.symm (X i) = gA i := by rw [hσ, AlgEquiv.ofAlgHom_symm_apply, aeval_X]
    rw [hsi, hgA]
    rcases eq_or_ne i 0 with rfl | hi
    · rw [Function.update_self]; exact (mem_homogeneousSubmodule _ _).mp hLhom
    · rw [Function.update_of_ne hi]; exact isHomogeneous_X K i
  · rw [hσ, AlgEquiv.ofAlgHom_apply]; exact hA'L

/-
A degree-1 homogeneous form is the sum of its linear coefficients times the
variables.
-/
theorem homog_one_as_sum {N : ℕ} (p : MvPolynomial (Fin N) K) (hp : p.IsHomogeneous 1) :
    p = ∑ i, C (coeff (Finsupp.single i 1) p) * X i := by
  -- Since p is homogeneous of degree 1, every monomial in p has degree 1.
  have h_deg1 : ∀ m ∈ p.support, m.degree = 1 := by
    intro m hm; specialize hp ( Finsupp.mem_support_iff.mp hm ) ; simp_all +decide [ Finsupp.degree ] ;
    simp_all +decide [ Finsupp.weight ];
    simp_all +decide [ Finsupp.linearCombination_apply, Finsupp.sum ];
  -- Since p is homogeneous of degree 1, every monomial in p has exactly one variable with exponent 1.
  have h_monomial : ∀ m ∈ p.support, ∃ i : Fin N, m = Finsupp.single i 1 := by
    intro m hm; specialize h_deg1 m hm; simp_all +decide [ Finsupp.degree ] ;
    obtain ⟨ i, hi ⟩ := Finset.exists_ne_zero_of_sum_ne_zero ( by linarith : ∑ i ∈ m.support, m i ≠ 0 ) ; use i; ext j; by_cases hj : j = i <;> simp_all +decide [ Finsupp.single_apply ] ;
    · exact le_antisymm ( h_deg1 ▸ Finset.single_le_sum ( fun a _ => Nat.zero_le ( m a ) ) ( by aesop ) ) ( Nat.pos_of_ne_zero hi );
    · contrapose! h_deg1;
      rw [ Finset.sum_eq_add_sum_diff_singleton ( show i ∈ m.support from by aesop ) ];
      exact ne_of_gt ( lt_add_of_pos_of_le ( Nat.pos_of_ne_zero hi ) ( Nat.one_le_iff_ne_zero.mpr ( by exact ne_of_gt ( lt_of_lt_of_le ( Nat.pos_of_ne_zero h_deg1 ) ( Finset.single_le_sum ( fun x _ => Nat.zero_le ( m x ) ) ( by aesop ) ) ) ) ) );
  ext m; by_cases hm : m ∈ p.support <;> simp_all +decide [ MvPolynomial.coeff_sum, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X ] ;
  · obtain ⟨ i, rfl ⟩ := h_monomial m hm; simp +decide [ MvPolynomial.coeff_X ] ;
  · rw [ Finset.sum_eq_zero ] ; intros ; simp_all +decide [ MvPolynomial.coeff_X' ]

/-- A graded `K`-algebra automorphism carrying a given nonzero linear form to the
first coordinate. -/
theorem exists_graded_auto_X0 {N : ℕ} (ℓ : MvPolynomial (Fin (N + 1)) K)
    (hℓ : ℓ ∈ homogeneousSubmodule (Fin (N + 1)) K 1) (hℓne : ℓ ≠ 0) :
    ∃ φ : MvPolynomial (Fin (N + 1)) K ≃ₐ[K] MvPolynomial (Fin (N + 1)) K,
      (∀ e, (homogeneousSubmodule (Fin (N + 1)) K e).map φ.toAlgHom.toLinearMap
        = homogeneousSubmodule (Fin (N + 1)) K e) ∧ φ ℓ = X 0 := by
  classical
  have hℓhom : ℓ.IsHomogeneous 1 := (mem_homogeneousSubmodule _ _).mp hℓ
  set c : Fin (N+1) → K := fun i => coeff (Finsupp.single i 1) ℓ with hc
  have hℓsum : ℓ = ∑ i, C (c i) * X i := homog_one_as_sum ℓ hℓhom
  -- some coefficient is nonzero
  obtain ⟨j, hj⟩ : ∃ j, c j ≠ 0 := by
    by_contra h
    push_neg at h
    apply hℓne
    rw [hℓsum]
    apply Finset.sum_eq_zero
    intro i _; rw [h i]; simp
  -- swap 0 and j, and set cc = c ∘ swap so cc 0 = c j ≠ 0
  set e0 : Equiv.Perm (Fin (N+1)) := Equiv.swap 0 j with he0
  set cc : Fin (N+1) → K := fun i => c (e0 i) with hcc
  have hcc0 : cc 0 ≠ 0 := by rw [hcc]; simp only [he0, Equiv.swap_apply_left]; exact hj
  obtain ⟨σ, hσX, hσsymmX, hσL⟩ := exists_subst_equiv cc hcc0
  -- τ = rename by swap; τ ℓ = ∑ i, C (cc i) * X i
  set τ : MvPolynomial (Fin (N+1)) K ≃ₐ[K] MvPolynomial (Fin (N+1)) K :=
    MvPolynomial.renameEquiv K e0 with hτ
  have hτℓ : τ ℓ = ∑ i, C (cc i) * X i := by
    rw [hτ, hℓsum, map_sum]
    apply Fintype.sum_equiv e0
    intro i
    simp only [MvPolynomial.renameEquiv_apply, map_mul, MvPolynomial.rename_C,
      MvPolynomial.rename_X, hcc, he0, Equiv.swap_apply_self]
  refine ⟨τ.trans σ, ?_, ?_⟩
  · apply gradedMap_of_X_homog
    · intro i
      rw [AlgEquiv.trans_apply, hτ, MvPolynomial.renameEquiv_apply, MvPolynomial.rename_X]
      exact hσX (e0 i)
    · intro i
      rw [AlgEquiv.symm_trans_apply]
      apply isHomogeneous_aeval_of_X_homog τ.symm.toAlgHom
      · intro k
        have hts : τ.symm (X k) = X (e0.symm k) := by
          simp only [hτ, MvPolynomial.renameEquiv_symm, MvPolynomial.renameEquiv_apply,
            MvPolynomial.rename_X]
        rw [AlgEquiv.coe_algHom, hts]; exact isHomogeneous_X K (e0.symm k)
      · exact hσsymmX i
  · rw [AlgEquiv.trans_apply, hτℓ, hσL]

/-
Dropping the first variable: a graded surjection onto the polynomial ring in
one fewer variable, with kernel `(X 0)`.
-/
theorem exists_dropFirst {N : ℕ} :
    ∃ ψ : MvPolynomial (Fin (N + 1)) K →ₐ[K] MvPolynomial (Fin N) K,
      Function.Surjective ψ ∧
      (∀ e, (homogeneousSubmodule (Fin (N + 1)) K e).map ψ.toLinearMap
        = homogeneousSubmodule (Fin N) K e) ∧
      RingHom.ker ψ = Ideal.span {X 0} := by
  -- Define the homomorphism ψ by mapping X 0 to 0 and each X i.succ to X i.
  let ψ : MvPolynomial (Fin (N + 1)) K →ₐ[K] MvPolynomial (Fin N) K := MvPolynomial.aeval (Fin.cons 0 (fun i => MvPolynomial.X i));
  refine' ⟨ ψ, _, _, _ ⟩;
  · intro q
    use MvPolynomial.rename (Fin.succ) q
    simp [ψ];
    induction q using MvPolynomial.induction_on <;> aesop;
  · intro e
    apply le_antisymm;
    · intro p hp;
      obtain ⟨ q, hq, rfl ⟩ := hp;
      convert MvPolynomial.IsHomogeneous.eval₂ hq _ _;
      rotate_left;
      exact Fin N;
      exact K;
      exact inferInstance;
      exact 1;
      exact algebraMap K ( MvPolynomial ( Fin N ) K );
      exact fun i => Fin.cases 0 ( fun i => MvPolynomial.X i ) i;
      simp +decide [ MvPolynomial.IsHomogeneous ];
      simp +decide [ IsWeightedHomogeneous ];
      simp +decide [ Finsupp.weight ];
      simp +decide [ Fin.forall_fin_succ, MvPolynomial.coeff_X' ];
      rfl;
    · intro p hp
      obtain ⟨q, hq⟩ : ∃ q : MvPolynomial (Fin (N + 1)) K, q.IsHomogeneous e ∧ ψ q = p := by
        refine' ⟨ MvPolynomial.rename ( Fin.succ ) p, _, _ ⟩;
        · convert hp using 1;
          simp +decide [ mem_homogeneousSubmodule ];
          grind +suggestions;
        · erw [ MvPolynomial.aeval_rename ];
          erw [ show ( Fin.cons 0 fun i => X i : Fin ( N + 1 ) → MvPolynomial ( Fin N ) K ) ∘ Fin.succ = fun i => X i from funext fun i => rfl ] ; aesop;
      use q
      aesop;
  · ext p;
    have h_iso : ∃ (iso : MvPolynomial (Fin (N + 1)) K ≃ₐ[K] Polynomial (MvPolynomial (Fin N) K)), iso (MvPolynomial.X 0) = Polynomial.X ∧ ∀ i : Fin N, iso (MvPolynomial.X (Fin.succ i)) = Polynomial.C (MvPolynomial.X i) := by
      refine' ⟨ MvPolynomial.finSuccEquiv K N, _, _ ⟩ <;> simp +decide [ MvPolynomial.finSuccEquiv_X_zero, MvPolynomial.finSuccEquiv_X_succ ];
    obtain ⟨iso, h_iso_X0, h_iso_succ⟩ := h_iso;
    have h_iso_eval : ψ = (Polynomial.evalRingHom 0).comp (iso.toRingHom) := by
      ext i;
      · simp +decide [ ψ, h_iso_X0, h_iso_succ ];
        rw [ show iso ( C i ) = Polynomial.C ( MvPolynomial.C i ) from ?_ ];
        · split_ifs <;> simp_all +decide [ Polynomial.coeff_C ];
        · exact iso.commutes i;
      · induction i using Fin.inductionOn <;> aesop;
    have h_iso_eval : ψ p = 0 ↔ Polynomial.eval 0 (iso p) = 0 := by
      replace h_iso_eval := congr_arg ( fun f => f p ) h_iso_eval; aesop;
    have h_iso_eval : Polynomial.eval 0 (iso p) = 0 ↔ Polynomial.X ∣ iso p := by
      rw [ Polynomial.X_dvd_iff ];
      rw [ Polynomial.coeff_zero_eq_eval_zero ];
    have h_iso_eval : Polynomial.X ∣ iso p ↔ iso p ∈ Ideal.span {Polynomial.X} := by
      rw [ Ideal.mem_span_singleton ];
    have h_iso_eval : iso p ∈ Ideal.span {Polynomial.X} ↔ p ∈ Ideal.span {MvPolynomial.X 0} := by
      rw [ ← h_iso_X0, Ideal.mem_span_singleton, Ideal.mem_span_singleton ];
      exact ⟨ fun h => by simpa using iso.symm.toAlgHom.map_dvd h, fun h => by simpa using iso.toAlgHom.map_dvd h ⟩;
    aesop

/-- Transport: cutting a homogeneous ideal by a nonzero linear form reduces the
number of variables by one, so (using the induction hypothesis in `m` variables)
its Hilbert function is eventually polynomial. -/
theorem HF_sup_linear_eventually_poly [Infinite K] {m : ℕ}
    (ih : ∀ I : Ideal (MvPolynomial (Fin m) K), IsHomog I →
      ∃ P : Polynomial ℚ, ∀ᶠ e in atTop, (HF I e : ℚ) = P.eval (e : ℚ))
    (J : Ideal (MvPolynomial (Fin (m + 1)) K)) (hJhom : IsHomog J)
    {ℓ : MvPolynomial (Fin (m + 1)) K} (hℓ : ℓ ∈ homogeneousSubmodule (Fin (m + 1)) K 1)
    (hℓne : ℓ ≠ 0) :
    ∃ P : Polynomial ℚ, ∀ᶠ e in atTop,
      (HF (J ⊔ Ideal.span {ℓ}) e : ℚ) = P.eval (e : ℚ) := by
  obtain ⟨φ, hφgr, hφℓ⟩ := exists_graded_auto_X0 ℓ hℓ hℓne
  obtain ⟨ψ, hψsurj, hψgr, hψker⟩ := exists_dropFirst (K := K) (N := m)
  -- Step 1: apply the graded automorphism `φ`.
  have hkerphi : RingHom.ker φ.toAlgHom ≤ (J ⊔ Ideal.span {ℓ}) := by
    intro x hx
    have hx0 : x = 0 := φ.injective (by simpa [RingHom.mem_ker] using hx)
    rw [hx0]; exact Submodule.zero_mem _
  have h1 : ∀ e, HF (J ⊔ Ideal.span {ℓ}) e = HF ((J ⊔ Ideal.span {ℓ}).map φ.toAlgHom) e :=
    fun e => HF_transfer φ.toAlgHom φ.surjective hφgr (J ⊔ Ideal.span {ℓ}) hkerphi e
  have hmapφ : (J ⊔ Ideal.span {ℓ}).map φ.toAlgHom
      = J.map φ.toAlgHom ⊔ Ideal.span {(X 0 : MvPolynomial (Fin (m + 1)) K)} := by
    rw [Ideal.map_sup, Ideal.map_span, Set.image_singleton]
    congr 2
    simpa using hφℓ
  set J1 := J.map φ.toAlgHom with hJ1def
  have hJ1hom : IsHomog J1 := isHomog_map_graded φ.toAlgHom φ.surjective hφgr J hJhom
  -- Step 2: drop the first variable via `ψ`.
  have hkerpsi : RingHom.ker ψ ≤ (J1 ⊔ Ideal.span {(X 0 : MvPolynomial (Fin (m + 1)) K)}) := by
    rw [hψker]; exact le_sup_right
  have h2 : ∀ e, HF (J1 ⊔ Ideal.span {(X 0 : MvPolynomial (Fin (m + 1)) K)}) e
      = HF ((J1 ⊔ Ideal.span {(X 0 : MvPolynomial (Fin (m + 1)) K)}).map ψ) e :=
    fun e => HF_transfer ψ hψsurj hψgr _ hkerpsi e
  have hmapψ : (J1 ⊔ Ideal.span {(X 0 : MvPolynomial (Fin (m + 1)) K)}).map ψ = J1.map ψ := by
    rw [Ideal.map_sup, Ideal.map_span, Set.image_singleton]
    have hX0 : ψ (X 0) = 0 := by
      have : (X 0 : MvPolynomial (Fin (m + 1)) K) ∈ RingHom.ker ψ := by
        rw [hψker]; exact Ideal.subset_span (Set.mem_singleton _)
      simpa [RingHom.mem_ker] using this
    rw [hX0]
    simp
  have hJ2hom : IsHomog (J1.map ψ) := isHomog_map_graded ψ hψsurj hψgr J1 hJ1hom
  obtain ⟨P, hP⟩ := ih (J1.map ψ) hJ2hom
  refine ⟨P, ?_⟩
  filter_upwards [hP] with e hPe
  have e1 : HF (J ⊔ Ideal.span {ℓ}) e = HF (J1.map ψ) e := by
    rw [h1 e, hmapφ, h2 e, hmapψ]
  rw [e1]; exact hPe

/-- Inductive step for eventual polynomiality. -/
theorem HF_succ_step [Infinite K] {m : ℕ}
    (ih : ∀ I : Ideal (MvPolynomial (Fin m) K), IsHomog I →
      ∃ P : Polynomial ℚ, ∀ᶠ e in atTop, (HF I e : ℚ) = P.eval (e : ℚ))
    (I : Ideal (MvPolynomial (Fin (m + 1)) K)) (hI : IsHomog I) :
    ∃ P : Polynomial ℚ, ∀ᶠ e in atTop, (HF I e : ℚ) = P.eval (e : ℚ) := by
  -- Work with `J := sat I`; it is homogeneous, saturated, and has the same
  -- eventual Hilbert function as `I`.
  set J := sat I with hJ
  have hJhom : IsHomog J := isHomog_sat I hI
  have hJsat : sat J = J := by rw [hJ]; exact sat_sat I
  have hIJ : ∀ᶠ e in atTop, HF J e = HF I e := HF_saturation_eventually_eq I hI
  suffices hsuff : ∃ P : Polynomial ℚ, ∀ᶠ e in atTop, (HF J e : ℚ) = P.eval (e : ℚ) by
    obtain ⟨P, hP⟩ := hsuff
    refine ⟨P, ?_⟩
    filter_upwards [hP, hIJ] with e hPe hIJe
    rw [← hIJe]; exact hPe
  by_cases hJtop : J = ⊤
  · refine ⟨0, ?_⟩
    filter_upwards with e
    rw [hJtop, HF_top]; simp
  · obtain ⟨ℓ, hℓhom, hℓne, hreg⟩ := exists_linear_nzd J hJhom hJsat hJtop
    obtain ⟨Q, hQ⟩ := HF_sup_linear_eventually_poly ih J hJhom hℓhom hℓne
    have hstep := HF_step_regular J hJhom hℓhom (by norm_num) hreg
    -- forward difference of `HF J` is eventually `Q(e+1)`
    have hdiff : ∀ᶠ e in atTop, (HF J (e + 1) : ℚ) - (HF J e : ℚ) =
        (Q.comp (Polynomial.X + 1)).eval (e : ℚ) := by
      have hQshift : ∀ᶠ e in atTop, (HF (J ⊔ Ideal.span {ℓ}) (e + 1) : ℚ) =
          (Q.comp (Polynomial.X + 1)).eval (e : ℚ) := by
        rw [Filter.eventually_atTop] at hQ ⊢
        obtain ⟨N, hN⟩ := hQ
        refine ⟨N, fun e he => ?_⟩
        rw [Polynomial.eval_comp]
        simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one]
        have := hN (e + 1) (by omega)
        rw [this]; push_cast; ring_nf
      filter_upwards [hQshift] with e heq
      have hs := hstep (e + 1) (by omega)
      have hs' : HF (J ⊔ Ideal.span {ℓ}) (e + 1) + HF J e = HF J (e + 1) := by
        simpa using hs
      have : (HF (J ⊔ Ideal.span {ℓ}) (e + 1) : ℚ) + (HF J e : ℚ) = (HF J (e + 1) : ℚ) := by
        exact_mod_cast hs'
      rw [← heq]; linarith
    obtain ⟨P, hP⟩ := eventually_poly_of_fwdDiff (fun e => (HF J e : ℚ))
      (Q.comp (Polynomial.X + 1)) hdiff
    exact ⟨P, hP⟩

/-- Eventual polynomiality of the Hilbert function, for any number of variables. -/
theorem HF_eventually_poly_aux [Infinite K] :
    ∀ (m : ℕ) (I : Ideal (MvPolynomial (Fin m) K)), IsHomog I →
      ∃ P : Polynomial ℚ, ∀ᶠ e in atTop, (HF I e : ℚ) = P.eval (e : ℚ) := by
  intro m
  induction m with
  | zero => intro I hI; exact HF_base_zero I hI
  | succ m ih => intro I hI; exact HF_succ_step ih I hI

/-- 3. Eventual polynomiality of the Hilbert function. -/
theorem HF_eventually_polynomial [Infinite K]
    (I : Ideal (MvPolynomial (Fin n) K)) (hI : IsHomog I) :
    ∃ P : Polynomial ℚ, ∀ᶠ e in atTop, (HF I e : ℚ) = P.eval (e : ℚ) :=
  HF_eventually_poly_aux n I hI

/-- If the degree-`e` Hilbert value is `0`, then every degree-`e` form lies in `I`. -/
theorem homog_le_of_HF_zero (I : Ideal (MvPolynomial (Fin n) K)) {e : ℕ} (h : HF I e = 0)
    {p : MvPolynomial (Fin n) K} (hp : p.IsHomogeneous e) : p ∈ I := by
  have h_p_zero : (Ideal.Quotient.mk I p) = 0 := by
    have hfImg_bot : hfImg I e = ⊥ := by
      convert Submodule.finrank_eq_zero.mp h;
    rw [ Submodule.eq_bot_iff ] at hfImg_bot;
    exact hfImg_bot _ ( Submodule.mem_map_of_mem ( show p ∈ homogeneousSubmodule ( Fin n ) K e from by simpa [ mem_homogeneousSubmodule ] using hp ) );
  rwa [ Ideal.Quotient.eq_zero_iff_mem ] at h_p_zero

/-- If some Hilbert value vanishes, the saturation is the whole ring. -/
theorem sat_top_of_HF_zero (I : Ideal (MvPolynomial (Fin n) K)) {e : ℕ} (h : HF I e = 0) :
    sat I = ⊤ := by
  have h_varsIdeal_pow_sub : (varsIdeal : Ideal (MvPolynomial (Fin n) K))^e ≤ I := by
    have h_varsIdeal_pow : (varsIdeal : Ideal (MvPolynomial (Fin n) K))^e = Ideal.span (Set.image (fun x : Fin n →₀ ℕ => MvPolynomial.monomial x 1) {x : Fin n →₀ ℕ | x.degree = e}) := by
      convert MvPolynomial.pow_idealOfVars_eq_span e;
    rw [ h_varsIdeal_pow, Ideal.span_le ];
    rintro _ ⟨ x, hx, rfl ⟩;
    apply homog_le_of_HF_zero I h;
    grind +suggestions;
  refine' eq_top_iff.mpr _;
  refine' le_trans _ ( le_iSup _ e );
  intro x hx; simp_all +decide [ Submodule.mem_colon ] ;
  exact fun s hs => I.mul_mem_left x ( h_varsIdeal_pow_sub hs )

/-
If `sat I = ⊤`, some power of the variables ideal already lies in `I`.
-/
theorem varsPow_le_of_sat_top (I : Ideal (MvPolynomial (Fin n) K)) (h : sat I = ⊤) :
    ∃ k, (varsIdeal ^ k : Ideal (MvPolynomial (Fin n) K)) ≤ I := by
  have := h;
  contrapose! this;
  simp +decide [ Ideal.eq_top_iff_one, sat ];
  rw [ Submodule.mem_iSup_of_directed ];
  · simp +decide [ Submodule.mem_colon, this ];
    exact fun k => by simpa using Set.not_subset.mp ( this k ) ;
  · exact colon_varsIdeal_pow_mono I |> ( fun h => Monotone.directed_le h )

/-
If a power of the variables ideal lies in `I`, the quotient is finite-dimensional.
-/
theorem finiteDim_of_varsPow_le (I : Ideal (MvPolynomial (Fin n) K)) (k : ℕ)
    (hk : (varsIdeal ^ k : Ideal (MvPolynomial (Fin n) K)) ≤ I) :
    FiniteDimensional K (MvPolynomial (Fin n) K ⧸ I) := by
  -- Since $varsIdeal^k \leq I$, the quotient $MvPolynomial (Fin n) K ⧸ I$ is a quotient of $MvPolynomial (Fin n) K ⧸ varsIdeal^k$.
  have h_quotient : ∃ (f : (MvPolynomial (Fin n) K ⧸ varsIdeal ^ k) →ₐ[K] (MvPolynomial (Fin n) K ⧸ I)), Function.Surjective f := by
    refine' ⟨ _, _ ⟩;
    exact Ideal.Quotient.liftₐ ( varsIdeal ^ k ) ( Ideal.Quotient.mkₐ K I ) fun x hx => Ideal.Quotient.eq_zero_iff_mem.mpr ( hk hx );
    intro x; obtain ⟨ y, rfl ⟩ := Ideal.Quotient.mk_surjective x; use Ideal.Quotient.mk ( varsIdeal ^ k ) y; simp +decide ;
  obtain ⟨ f, hf ⟩ := h_quotient;
  have h_finite_dim : FiniteDimensional K (MvPolynomial (Fin n) K ⧸ varsIdeal ^ k) := by
    have h_span : ∀ p : MvPolynomial (Fin n) K, p - (∑ d ∈ Finset.range k, homogeneousComponent d p) ∈ varsIdeal ^ k := by
      intro p
      have h_trunc : p - ∑ d ∈ Finset.range k, homogeneousComponent d p ∈ idealOfVars (Fin n) K ^ k := by
        rw [ MvPolynomial.mem_pow_idealOfVars_iff ];
        intro x hx; contrapose! hx; simp_all +decide [ MvPolynomial.coeff_sub, MvPolynomial.coeff_sum, MvPolynomial.coeff_homogeneousComponent ] ;
      exact h_trunc
    have h_finite_dim : ∀ p : MvPolynomial (Fin n) K, ∃ q : MvPolynomial (Fin n) K, q ∈ MvPolynomial.restrictTotalDegree (Fin n) K (k - 1) ∧ p - q ∈ varsIdeal ^ k := by
      intro p
      use ∑ d ∈ Finset.range k, homogeneousComponent d p;
      simp_all +decide [ MvPolynomial.mem_restrictTotalDegree ];
      simp +decide [ MvPolynomial.totalDegree ];
      intro b hb; contrapose! hb; simp_all +decide [ MvPolynomial.coeff_sum, MvPolynomial.coeff_homogeneousComponent ] ;
      exact fun h => False.elim <| hb.not_ge <| Nat.le_sub_one_of_lt h;
    have h_finite_dim : ∀ p : MvPolynomial (Fin n) K ⧸ varsIdeal ^ k, ∃ q : MvPolynomial (Fin n) K, q ∈ MvPolynomial.restrictTotalDegree (Fin n) K (k - 1) ∧ p = Ideal.Quotient.mk (varsIdeal ^ k) q := by
      rintro ⟨ p ⟩;
      obtain ⟨ q, hq₁, hq₂ ⟩ := h_finite_dim p;
      exact ⟨ q, hq₁, Ideal.Quotient.eq.2 hq₂ ⟩;
    have h_finite_dim : FiniteDimensional K (MvPolynomial (Fin n) K ⧸ varsIdeal ^ k) := by
      have h_surjective : Function.Surjective (Ideal.Quotient.mk (varsIdeal ^ k) ∘ Submodule.subtype (MvPolynomial.restrictTotalDegree (Fin n) K (k - 1))) := by
        exact fun p => by obtain ⟨ q, hq, rfl ⟩ := ‹∀ p : MvPolynomial ( Fin n ) K ⧸ varsIdeal ^ k, ∃ q ∈ restrictTotalDegree ( Fin n ) K ( k - 1 ), p = Ideal.Quotient.mk ( varsIdeal ^ k ) q› p; exact ⟨ ⟨ q, hq ⟩, rfl ⟩ ;
      convert Module.Finite.of_surjective ( LinearMap.comp ( Ideal.Quotient.mkₐ K ( varsIdeal ^ k ) |> AlgHom.toLinearMap ) ( Submodule.subtype ( MvPolynomial.restrictTotalDegree ( Fin n ) K ( k - 1 ) ) ) ) h_surjective using 1;
    exact h_finite_dim;
  exact Module.Finite.of_surjective ( f.toLinearMap ) ( by aesop )

/-
The graded pieces of `R ⧸ I` are independent (homogeneity), so the partial sums
of the Hilbert function are bounded by the total dimension.
-/
theorem HF_partialSum_le_finrank (I : Ideal (MvPolynomial (Fin n) K)) (hI : IsHomog I)
    [FiniteDimensional K (MvPolynomial (Fin n) K ⧸ I)] (N : ℕ) :
    ∑ d ∈ Finset.range N, HF I d ≤ Module.finrank K (MvPolynomial (Fin n) K ⧸ I) := by
  -- By definition of $hfImg$, we know that $\sum_{d=0}^{N-1} \text{hfImg}(I, d)$ is a subspace of $R/I$.
  have h_sum_subspace : (∑ d ∈ Finset.range N, hfImg I d) ≤ ⊤ := by
    exact le_top;
  convert Submodule.finrank_mono h_sum_subspace using 1;
  · induction' N with N ih;
    · simp +decide [ Module.finrank ];
    · have h_disjoint : hfImg I N ⊓ (∑ d ∈ Finset.range N, hfImg I d) = ⊥ := by
        simp +decide [ Submodule.eq_bot_iff ];
        intro x hx₁ hx₂
        obtain ⟨p, hp₁, hp₂⟩ : ∃ p : MvPolynomial (Fin n) K, p ∈ homogeneousSubmodule (Fin n) K N ∧ x = Ideal.Quotient.mk I p := by
          obtain ⟨ p, hp₁, rfl ⟩ := hx₁; exact ⟨ p, hp₁, rfl ⟩ ;
        obtain ⟨q, hq₁, hq₂⟩ : ∃ q : MvPolynomial (Fin n) K, q ∈ ⨆ d ∈ Finset.range N, homogeneousSubmodule (Fin n) K d ∧ x = Ideal.Quotient.mk I q := by
          have hq : x ∈ Submodule.map (Ideal.Quotient.mkₐ K I).toLinearMap (⨆ d ∈ Finset.range N, homogeneousSubmodule (Fin n) K d) := by
            convert hx₂ using 1;
            simp +decide [ hfImg, Submodule.map_iSup ];
            refine' le_antisymm _ _;
            · simp +decide [ iSup_le_iff ];
              exact fun i hi => Finset.le_sup ( f := fun x => Submodule.map ( Ideal.Quotient.mkₐ K I ).toLinearMap ( homogeneousSubmodule ( Fin n ) K x ) ) ( Finset.mem_range.mpr hi );
            · exact Finset.sup_le fun i hi => le_iSup₂_of_le i ( Finset.mem_range.mp hi ) le_rfl;
          exact ⟨ _, hq.choose_spec.1, hq.choose_spec.2.symm ⟩
        have hq_zero : homogeneousComponent N q = 0 := by
          rw [ Submodule.mem_iSup_iff_exists_finsupp ] at hq₁;
          obtain ⟨ f, hf₁, hf₂ ⟩ := hq₁; rw [ ← hf₂ ] ; simp +decide [ Finsupp.sum ] ;
          refine' Finset.sum_eq_zero fun i hi => _;
          specialize hf₁ i; by_cases hi' : i < N <;> simp_all +decide [ homogeneousSubmodule ] ;
          rw [ homogeneousComponent_of_mem ( by simpa [ mem_homogeneousSubmodule ] using hf₁ ) ] ; aesop
        have hp_zero : p ∈ I := by
          have hp_zero : p - q ∈ I := by
            rw [ ← Ideal.Quotient.eq_zero_iff_mem ] ; aesop;
          have hp_zero : homogeneousComponent N (p - q) ∈ I := by
            exact hI _ hp_zero _;
          convert hp_zero using 1;
          simp +decide [ hq_zero, homogeneousComponent_of_mem hp₁ ]
        have hx_zero : x = 0 := by
          exact hp₂.trans ( Ideal.Quotient.eq_zero_iff_mem.mpr hp_zero )
        exact hx_zero;
      have := Submodule.finrank_sup_add_finrank_inf_eq ( hfImg I N ) ( ∑ d ∈ Finset.range N, hfImg I d ) ; simp_all +decide [ Finset.sum_range_succ ] ;
      rw [ Finset.sum_range_succ, add_comm ];
      rw [ add_comm, Submodule.add_eq_sup ];
      rw [ add_comm, sup_comm ];
      rw [ h_disjoint, finrank_bot ] at this ; linarith! [ HF_eq_finrank_hfImg I N ];
  · simp +decide [ Module.finrank_self ]

/-- If the quotient is finite-dimensional, the Hilbert function is eventually zero. -/
theorem HF_eventually_zero_of_finiteDim (I : Ideal (MvPolynomial (Fin n) K)) (hI : IsHomog I)
    [FiniteDimensional K (MvPolynomial (Fin n) K ⧸ I)] :
    ∀ᶠ e in atTop, HF I e = 0 := by
  have hSle : ∀ N, (∑ d ∈ Finset.range N, HF I d) ≤
      Module.finrank K (MvPolynomial (Fin n) K ⧸ I) := HF_partialSum_le_finrank I hI
  have hSmono : Monotone (fun N => ∑ d ∈ Finset.range N, HF I d) := by
    intro a b hab
    apply Finset.sum_le_sum_of_subset
    exact Finset.range_mono hab
  obtain ⟨M, hM⟩ : ∃ M, ∀ N, M ≤ N →
      (∑ d ∈ Finset.range N, HF I d) = ∑ d ∈ Finset.range M, HF I d := by
    have hbdd : BddAbove (Set.range (fun N => ∑ d ∈ Finset.range N, HF I d)) :=
      ⟨Module.finrank K (MvPolynomial (Fin n) K ⧸ I), by rintro _ ⟨N, rfl⟩; exact hSle N⟩
    obtain ⟨M, hMeq⟩ := Nat.sSup_mem (⟨_, ⟨0, rfl⟩⟩ : (Set.range
      (fun N => ∑ d ∈ Finset.range N, HF I d)).Nonempty) hbdd
    exact ⟨M, fun N hN => le_antisymm ((le_csSup hbdd ⟨N, rfl⟩).trans_eq hMeq.symm) (hSmono hN)⟩
  rw [Filter.eventually_atTop]
  refine ⟨M, fun e he => ?_⟩
  have h1 := hM (e + 1) (by omega)
  have h2 := hM e he
  rw [Finset.sum_range_succ] at h1
  omega

/-
A rational polynomial vanishing on all large naturals is zero.
-/
theorem poly_eq_zero_of_eventually_zero (P : Polynomial ℚ)
    (h : ∀ᶠ e in atTop, P.eval ((e : ℕ) : ℚ) = 0) : P = 0 := by
  -- If $P$ is a non-zero polynomial, it has only finitely many roots.
  by_contra hP_nonzero
  have hP_finite_roots : Set.Finite {x : ℚ | P.eval x = 0} := by
    exact P.roots.toFinset.finite_toSet.subset fun x hx => by aesop;
  exact hP_finite_roots.not_infinite <| Set.infinite_of_forall_exists_gt fun x => by rcases Filter.eventually_atTop.mp h with ⟨ N, hN ⟩ ; exact ⟨ N + ⌊x⌋₊ + 1, by simpa using hN ( N + ⌊x⌋₊ + 1 ) ( by linarith ), by linarith [ Nat.lt_floor_add_one x ] ⟩ ;

attribute [local instance] MvPolynomial.gradedAlgebra

private lemma ideal_isHomogeneous_of_IsHomog
    (J : Ideal (MvPolynomial (Fin n) K)) (hJ : IsHomog J) :
    J.IsHomogeneous (homogeneousSubmodule (Fin n) K) := by
  intro i r hr
  convert hJ r hr i using 1
  exact MvPolynomial.decomposition.decompose'_apply (R := K) (σ := Fin n) r i

private lemma mem_varsIdeal_of_coeff_zero
    (p : MvPolynomial (Fin n) K) (hc : coeff 0 p = 0) :
    p ∈ (varsIdeal : Ideal (MvPolynomial (Fin n) K)) := by
  rw [varsIdeal]
  change p ∈ MvPolynomial.idealOfVars (Fin n) K
  rw [← pow_one (MvPolynomial.idealOfVars (Fin n) K),
    MvPolynomial.mem_pow_idealOfVars_iff]
  intro x hx
  exact Nat.succ_le_iff.mpr (Nat.pos_of_ne_zero fun hdeg => by
    have hx0 : x = 0 := (Finsupp.degree_eq_zero_iff x).mp hdeg
    have hcoeff : coeff x p ≠ 0 := MvPolynomial.mem_support_iff.mp hx
    exact hcoeff (by simpa [hx0] using hc))

private lemma isHomogeneous_le_varsIdeal
    (P : Ideal (MvPolynomial (Fin n) K))
    (hP : P.IsHomogeneous (homogeneousSubmodule (Fin n) K)) (hPne : P ≠ ⊤) :
    P ≤ varsIdeal := by
  intro p hp
  apply mem_varsIdeal_of_coeff_zero p
  by_contra hc
  have hCmem : C (coeff 0 p) ∈ P := by
    have h0 := hP 0 hp
    convert h0 using 1
    exact ((MvPolynomial.decomposition.decompose'_apply (R := K) (σ := Fin n) p 0).trans
      (MvPolynomial.homogeneousComponent_zero p)).symm
  have hunitC : IsUnit (C (coeff 0 p) : MvPolynomial (Fin n) K) := by
    exact MvPolynomial.isUnit_iff_eq_C_of_isReduced.mpr
      ⟨coeff 0 p, isUnit_iff_ne_zero.mpr hc, rfl⟩
  exact hPne (P.eq_top_of_isUnit_mem hCmem hunitC)

/-- All minimal primes of a homogeneous ideal are contained in the variables ideal. -/
theorem minimalPrimes_le_varsIdeal (J : Ideal (MvPolynomial (Fin n) K)) (hJ : IsHomog J)
    {P : Ideal (MvPolynomial (Fin n) K)} (hP : P ∈ J.minimalPrimes) :
    P ≤ varsIdeal := by
  classical
  let 𝒜 := homogeneousSubmodule (Fin n) K
  have hPprime : P.IsPrime := Ideal.minimalPrimes_isPrime hP
  have hJmath : J.IsHomogeneous 𝒜 := ideal_isHomogeneous_of_IsHomog J hJ
  have hCorePrime : (P.homogeneousCore 𝒜).toIdeal.IsPrime :=
    Ideal.IsPrime.homogeneousCore (𝒜 := 𝒜) hPprime
  have hJ_le_core : J ≤ (P.homogeneousCore 𝒜).toIdeal := by
    calc
      J = (J.homogeneousCore 𝒜).toIdeal := hJmath.toIdeal_homogeneousCore_eq_self.symm
      _ ≤ (P.homogeneousCore 𝒜).toIdeal := Ideal.homogeneousCore_mono 𝒜 hP.1.2
  have hcore_le_P : (P.homogeneousCore 𝒜).toIdeal ≤ P := Ideal.toIdeal_homogeneousCore_le 𝒜 P
  have hP_le_core : P ≤ (P.homogeneousCore 𝒜).toIdeal :=
    hP.2 ⟨hCorePrime, hJ_le_core⟩ hcore_le_P
  have hcore_eq : (P.homogeneousCore 𝒜).toIdeal = P := le_antisymm hcore_le_P hP_le_core
  have hPhom : P.IsHomogeneous 𝒜 := by
    rw [← hcore_eq]
    exact HomogeneousIdeal.isHomogeneous (P.homogeneousCore 𝒜)
  exact isHomogeneous_le_varsIdeal P hPhom hPprime.ne_top

/-- The image of `varsIdeal` in `R ⧸ J` is a proper (maximal) ideal, so its height
is at most the Krull dimension of the quotient. -/
theorem height_map_varsIdeal_le_krullDim (J : Ideal (MvPolynomial (Fin n) K)) (hJ : IsHomog J)
    (hne : J ≠ ⊤) :
    ((varsIdeal.map (Ideal.Quotient.mk J)).height : WithBot ℕ∞)
      ≤ ringKrullDim (MvPolynomial (Fin n) K ⧸ J) := by
  have hle : J ≤ (varsIdeal : Ideal (MvPolynomial (Fin n) K)) :=
    isHomogeneous_le_varsIdeal J (ideal_isHomogeneous_of_IsHomog J hJ) hne
  have hne' : (varsIdeal.map (Ideal.Quotient.mk J)) ≠ ⊤ := by
    intro htop
    rw [Ideal.eq_top_iff_one, Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective] at htop
    obtain ⟨x, hx, hx1⟩ := htop
    have hx1' : (Ideal.Quotient.mk J) x = (Ideal.Quotient.mk J) 1 := by simpa using hx1
    have hxsub : x - 1 ∈ J := (Ideal.Quotient.eq).mp hx1'
    have hxJ : x - 1 ∈ (varsIdeal : Ideal (MvPolynomial (Fin n) K)) := hle hxsub
    have hone : (1 : MvPolynomial (Fin n) K) ∈ (varsIdeal : Ideal (MvPolynomial (Fin n) K)) := by
      have := sub_mem hx hxJ
      simpa [sub_sub_cancel] using this
    exact varsIdeal_isMaximal.ne_top (Ideal.eq_top_iff_one _ |>.mpr hone)
  exact Ideal.height_le_ringKrullDim_of_ne_top hne'

/-
An integral ring extension does not increase the Krull dimension (incomparability):
if `f : A →+* B` is integral then `ringKrullDim B ≤ ringKrullDim A`.
-/
theorem ringKrullDim_le_of_isIntegral {A B : Type*} [CommRing A] [CommRing B]
    (f : A →+* B) (hint : f.IsIntegral) :
    ringKrullDim B ≤ ringKrullDim A := by
  convert Order.krullDim_le_of_strictMono ( PrimeSpectrum.comap f ) _;
  intro Q₁ Q₂ hQ;
  obtain ⟨x, hx⟩ : ∃ x : B, x ∈ Q₂.asIdeal ∧ x ∉ Q₁.asIdeal := by
    exact SetLike.exists_of_lt hQ;
  have h_int : IsIntegral (↥(RingHom.range f)) x := by
    obtain ⟨ p, hp ⟩ := ‹f.IsIntegral› x;
    refine' ⟨ p.map ( RingHom.rangeRestrict f ), _, _ ⟩;
    · exact hp.1.map _;
    · simp_all +decide [ Polynomial.eval₂_map ];
      convert hp.2 using 1;
  have h_int : IsIntegral (↥(RingHom.range f)) x → Ideal.comap (algebraMap (↥(RingHom.range f)) B) Q₁.asIdeal < Ideal.comap (algebraMap (↥(RingHom.range f)) B) Q₂.asIdeal := by
    intro h_int
    apply Ideal.comap_lt_comap_of_integral_mem_sdiff;
    exacts [ hQ.le, ⟨ hx.1, hx.2 ⟩, h_int ];
  convert h_int ‹_› using 1;
  simp +decide [ PrimeSpectrum.comap, Ideal.comap ];
  simp +decide [ SetLike.lt_iff_le_and_exists, SetLike.le_def ];
  constructor <;> intro h <;> simp_all +decide [ SetLike.lt_iff_le_and_exists ];
  · exact fun a x hx ha => hQ.le <| by aesop;
  · exact ⟨ fun x hx => h.1 _ _ rfl hx, fun hx => by obtain ⟨ a, ⟨ x, rfl ⟩, ha₁, ha₂ ⟩ := h.2; exact ha₂ <| hx ha₁ ⟩

/-
**Equidimensionality of affine domains.** In a finitely generated domain over a
field, every maximal ideal has height equal to the Krull dimension; in particular the
Krull dimension is at most the height of any maximal ideal.
-/
theorem ringKrullDim_le_height_of_isMaximal_of_finiteType
    {D : Type*} [CommRing D] [IsDomain D] [Algebra K D] [Algebra.FiniteType K D]
    (M : Ideal D) [hM : M.IsMaximal] :
    ringKrullDim D ≤ (M.height : WithBot ℕ∞) := by
  revert hM;
  obtain ⟨ s, g, hg ⟩ := exists_integral_inj_algHom_of_fg K D;
  have h_upper : ringKrullDim D ≤ s := by
    have h_upper : ringKrullDim D ≤ ringKrullDim (MvPolynomial (Fin s) K) := by
      convert ringKrullDim_le_of_isIntegral g.toRingHom hg.2 using 1;
    convert h_upper using 1;
    simp +decide [ ringKrullDim_eq_zero_of_field ];
  intro hM
  set A := MvPolynomial (Fin s) K
  letI := g.toRingHom.toAlgebra
  have h_faithful : FaithfulSMul A D := by
    constructor;
    intro m₁ m₂ h; specialize h 1; simp_all +decide [ Algebra.smul_def ] ;
    exact hg.1 h
  have h_integral : Algebra.IsIntegral A D := by
    exact ⟨ fun x => hg.2 x ⟩
  have h_int_closed : IsIntegrallyClosed A := by
    infer_instance
  have h_has_going_down : Algebra.HasGoingDown A D := by
    infer_instance
  set p := M.comap (algebraMap A D)
  have hp_max : p.IsMaximal := by
    convert Ideal.isMaximal_comap_of_isIntegral_of_isMaximal M using 1;
    exact h_integral
  have hp_height : p.height = s := by
    have := ParamSystem.height_maximal s p;
    exact this
  have hM_lies_over_p : M.LiesOver p := by
    constructor ; aesop
  have hM_height : M.height = p.height + (Ideal.map (Ideal.Quotient.mk (Ideal.map (algebraMap A D) p)) M).height := by
    convert Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown p M;
    have h_noetherian : IsNoetherianRing D := by
      have h_finite_type : Algebra.FiniteType K D := by
        infer_instance
      convert h_finite_type.isNoetherianRing;
    exact h_noetherian
  have hM_height_ge_s : (s : ℕ∞) ≤ M.height := by
    exact hp_height ▸ hM_height ▸ le_add_of_nonneg_right ( zero_le _ )
  exact h_upper.trans (by
  exact WithBot.coe_le_coe.mpr hM_height_ge_s)

/-
Under a surjection, the height of a prime is at most the height of its contraction.
-/
theorem height_le_height_comap_of_surjective {S T : Type*} [CommRing S] [CommRing T]
    (φ : S →+* T) (hφ : Function.Surjective φ) (P : Ideal T) [P.IsPrime] :
    P.height ≤ (P.comap φ).height := by
  have hg := @RingHom.strictMono_comap_of_surjective;
  have := hg hφ;
  have h_height_le : ∀ (Q : PrimeSpectrum T), (Order.height Q) ≤ (Order.height (PrimeSpectrum.comap φ Q)) := by
    grind +suggestions;
  convert h_height_le ⟨ P, by assumption ⟩ using 1;
  · convert Ideal.height_eq_primeHeight P;
  · convert Ideal.height_eq_primeHeight ( Ideal.comap φ P ) using 1

/-
The height of a prime is bounded by the Krull dimension of the quotient by a
minimal prime lying below it.
-/
theorem exists_minimalPrime_le_height_le_ringKrullDim_quotient {S : Type*} [CommRing S]
    [FiniteRingKrullDim S] (P : Ideal S) [P.IsPrime] :
    ∃ q ∈ (⊥ : Ideal S).minimalPrimes, q ≤ P ∧
      (P.height : WithBot ℕ∞) ≤ ringKrullDim (S ⧸ q) := by
  obtain ⟨l, hl⟩ : ∃ l : LTSeries (PrimeSpectrum S), RelSeries.last l = ⟨P, by assumption⟩ ∧ (l.length : WithBot ℕ∞) = P.height := by
    convert Ideal.exists_ltSeries_length_eq_height P;
    norm_cast;
  -- By `Ideal.exists_minimalPrimes_le (bot_le : ⊥ ≤ l.head.asIdeal)`, get q ∈ (⊥ : Ideal S).minimalPrimes with q ≤ l.head.asIdeal; q is prime by `Ideal.minimalPrimes_isPrime`.
  obtain ⟨q, hq_min, hq_le⟩ : ∃ q ∈ (⊥ : Ideal S).minimalPrimes, q ≤ l.head.asIdeal := by
    convert Ideal.exists_minimalPrimes_le ( bot_le : ⊥ ≤ l.head.asIdeal ) using 1;
  refine' ⟨ q, hq_min, _, _ ⟩;
  · have h_head_le_last : l.head ≤ l.last := by
      exact l.strictMono.monotone ( Nat.zero_le _ );
    exact le_trans hq_le ( by simpa [ hl.1 ] using h_head_le_last );
  · rw [ ← hl.2, ringKrullDim_quotient ];
    have h_lies_in_zeroLocus : ∀ i : Fin (l.length + 1), l i ∈ PrimeSpectrum.zeroLocus (q : Set S) := by
      intro i
      have h_l_head_le_l_i : l.toFun 0 ≤ l.toFun i := by
        exact l.strictMono.monotone ( Nat.zero_le _ );
      exact le_trans hq_le h_l_head_le_l_i;
    refine' le_trans _ ( Order.LTSeries.length_le_krullDim _ );
    swap;
    refine' ⟨ l.length, fun i => ⟨ l i, h_lies_in_zeroLocus i ⟩, _ ⟩;
    exact fun i => l.step i;
    rfl

/-- The double quotient `(R ⧸ I) ⧸ (J.map (mk I))` has the same Krull dimension as `R ⧸ J`
(for `I ≤ J`). -/
theorem ringKrullDim_quotQuot_eq {R' : Type*} [CommRing R'] (I J : Ideal R') (h : I ≤ J) :
    ringKrullDim ((R' ⧸ I) ⧸ (J.map (Ideal.Quotient.mk I))) = ringKrullDim (R' ⧸ J) := by
  rw [ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotSup I J)]
  rw [sup_eq_right.mpr h]

/-
Contracting the image of `varsIdeal` along `R ⧸ J → R ⧸ p` recovers its image in `R ⧸ J`.
-/
theorem comap_factor_map_varsIdeal {J p : Ideal (MvPolynomial (Fin n) K)} (hJp : J ≤ p)
    (hpv : p ≤ varsIdeal) :
    (varsIdeal.map (Ideal.Quotient.mk p)).comap (Ideal.Quotient.factor hJp)
      = varsIdeal.map (Ideal.Quotient.mk J) := by
  refine' le_antisymm _ _;
  · intro x hx;
    obtain ⟨ y, rfl ⟩ := Ideal.Quotient.mk_surjective x;
    simp_all +decide [ Ideal.mem_comap, Ideal.mem_map_iff_of_surjective ];
    exact Ideal.mem_sup_left hx;
  · intro x hx;
    obtain ⟨ y, hy, rfl ⟩ := Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective |>.mp hx;
    exact Ideal.mem_map_of_mem _ hy

/-- The quotient of the polynomial ring by a proper ideal has finite Krull dimension. -/
theorem finiteRingKrullDim_quotient (J : Ideal (MvPolynomial (Fin n) K)) (hne : J ≠ ⊤) :
    FiniteRingKrullDim (MvPolynomial (Fin n) K ⧸ J) := by
  rw [finiteRingKrullDim_iff_ne_bot_and_top]
  haveI : Nontrivial (MvPolynomial (Fin n) K ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr hne
  have hdimR : ringKrullDim (MvPolynomial (Fin n) K) = (n : WithBot ℕ∞) := by
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]; simp
  have hle : ringKrullDim (MvPolynomial (Fin n) K ⧸ J) ≤ (n : WithBot ℕ∞) := by
    rw [← hdimR]; exact ringKrullDim_quotient_le J
  refine ⟨?_, ?_⟩
  · have h0 : (0 : WithBot ℕ∞) ≤ ringKrullDim (MvPolynomial (Fin n) K ⧸ J) :=
      ringKrullDim_nonneg_of_nontrivial
    intro h; rw [h] at h0; simp at h0
  · intro h; rw [h] at hle; exact (Ne.symm (not_eq_of_beq_eq_false rfl)) (le_antisymm le_top hle)

/-- **Hard graded direction.** The Krull dimension of `R ⧸ J` is realized at the
vertex: it is at most the height of the image of the irrelevant ideal `varsIdeal`.
(For a graded ring with a field in degree zero, `dim = height` of the irrelevant
maximal ideal.) -/
theorem krullDim_le_height_map_varsIdeal (J : Ideal (MvPolynomial (Fin n) K)) (hJ : IsHomog J)
    (hne : J ≠ ⊤) :
    ringKrullDim (MvPolynomial (Fin n) K ⧸ J)
      ≤ ((varsIdeal.map (Ideal.Quotient.mk J)).height : WithBot ℕ∞) := by
  haveI := finiteRingKrullDim_quotient J hne
  rw [ringKrullDim_le_iff_isMaximal_height_le]
  intro m hm
  haveI : m.IsPrime := hm.isPrime
  obtain ⟨q, hq_mem, hq_le, hq_dim⟩ :=
    exists_minimalPrime_le_height_le_ringKrullDim_quotient m
  set p := q.comap (Ideal.Quotient.mk J) with hp_def
  have hp_mem : p ∈ J.minimalPrimes := by
    rw [Ideal.minimalPrimes_eq_comap]; exact ⟨q, hq_mem, rfl⟩
  haveI : p.IsPrime := Ideal.minimalPrimes_isPrime hp_mem
  have hJp : J ≤ p := by
    intro x hx
    rw [hp_def, Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr hx]
    exact q.zero_mem
  have hpv : p ≤ varsIdeal := minimalPrimes_le_varsIdeal J hJ hp_mem
  have hq_eq : q = p.map (Ideal.Quotient.mk J) := by
    rw [hp_def, Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective]
  have hdimeq : ringKrullDim ((MvPolynomial (Fin n) K ⧸ J) ⧸ q)
      = ringKrullDim (MvPolynomial (Fin n) K ⧸ p) := by
    rw [hq_eq]; exact ringKrullDim_quotQuot_eq J p hJp
  haveI : IsDomain (MvPolynomial (Fin n) K ⧸ p) := Ideal.Quotient.isDomain p
  haveI : (varsIdeal : Ideal (MvPolynomial (Fin n) K)).IsMaximal := varsIdeal_isMaximal
  haveI hmp_max : (varsIdeal.map (Ideal.Quotient.mk p)).IsMaximal := by
    apply Ideal.IsMaximal.map_of_surjective_of_ker_le Ideal.Quotient.mk_surjective
    rw [Ideal.mk_ker]; exact hpv
  have hdom : ringKrullDim (MvPolynomial (Fin n) K ⧸ p)
      ≤ ((varsIdeal.map (Ideal.Quotient.mk p)).height : WithBot ℕ∞) :=
    ringKrullDim_le_height_of_isMaximal_of_finiteType (K := K) _
  have hcomp : (varsIdeal.map (Ideal.Quotient.mk p)).height
      ≤ (varsIdeal.map (Ideal.Quotient.mk J)).height := by
    have h1 := height_le_height_comap_of_surjective (Ideal.Quotient.factor hJp)
      (Ideal.Quotient.factor_surjective hJp) (varsIdeal.map (Ideal.Quotient.mk p))
    rwa [comap_factor_map_varsIdeal hJp hpv] at h1
  calc (m.height : WithBot ℕ∞)
      ≤ ringKrullDim ((MvPolynomial (Fin n) K ⧸ J) ⧸ q) := hq_dim
    _ = ringKrullDim (MvPolynomial (Fin n) K ⧸ p) := hdimeq
    _ ≤ ((varsIdeal.map (Ideal.Quotient.mk p)).height : WithBot ℕ∞) := hdom
    _ ≤ ((varsIdeal.map (Ideal.Quotient.mk J)).height : WithBot ℕ∞) :=
        WithBot.coe_le_coe.mpr hcomp

/-- The image of the variables ideal in `R ⧸ J` has height equal to the Krull
dimension (the cone dimension is realized at the vertex). -/
theorem height_map_varsIdeal_eq_krullDim (J : Ideal (MvPolynomial (Fin n) K)) (hJ : IsHomog J)
    (hne : J ≠ ⊤) :
    ((varsIdeal.map (Ideal.Quotient.mk J)).height : WithBot ℕ∞)
      = ringKrullDim (MvPolynomial (Fin n) K ⧸ J) :=
  le_antisymm (height_map_varsIdeal_le_krullDim J hJ hne)
    (krullDim_le_height_map_varsIdeal J hJ hne)

/-- Saturation does not change the Krull dimension of the quotient (when proper). -/
theorem krullDim_sat_eq (I : Ideal (MvPolynomial (Fin n) K)) (hI : IsHomog I)
    (hne : sat I ≠ ⊤) :
    ringKrullDim (MvPolynomial (Fin n) K ⧸ sat I) = ringKrullDim (MvPolynomial (Fin n) K ⧸ I) := by
  classical
  let R := MvPolynomial (Fin n) K
  have hsat_le_vars : sat I ≤ (varsIdeal : Ideal R) :=
    isHomogeneous_le_varsIdeal (sat I)
      (ideal_isHomogeneous_of_IsHomog (sat I) (isHomog_sat I hI)) hne
  obtain ⟨k, hk⟩ := exists_sat_eq_colon I
  have hsat_le_rad : sat I ≤ I.radical := by
    intro x hx
    rw [Ideal.radical_eq_sInf, Submodule.mem_sInf]
    intro P hP
    rcases hP with ⟨hIP, hPprime⟩
    by_cases hmP : (varsIdeal : Ideal R) ≤ P
    · exact hmP (hsat_le_vars hx)
    · obtain ⟨y, hym, hyP⟩ := Set.not_subset.mp hmP
      have hx_colon : x ∈ I.colon ((varsIdeal ^ k : Ideal R)) := by
        simpa [R] using (hk ▸ hx)
      have hyk_mem : y ^ k ∈ (varsIdeal ^ k : Ideal R) := Ideal.pow_mem_pow hym k
      have hxyI : x * y ^ k ∈ I := by
        simpa [smul_eq_mul] using (Submodule.mem_colon.mp hx_colon) (y ^ k) hyk_mem
      have hykP : y ^ k ∉ P := fun hykP => hyP (hPprime.mem_of_pow_mem k hykP)
      exact (hPprime.mem_or_mem (hIP hxyI)).resolve_right hykP
  have hrad : (sat I).radical = I.radical := by
    exact le_antisymm ((Ideal.radical_isRadical I).radical_le_iff.mpr hsat_le_rad)
      (Ideal.radical_mono (le_sat I))
  have hz :
      PrimeSpectrum.zeroLocus (R := R) (sat I : Set R) =
        PrimeSpectrum.zeroLocus (R := R) (I : Set R) := by
    rw [← PrimeSpectrum.zeroLocus_radical (sat I), hrad, PrimeSpectrum.zeroLocus_radical I]
  rw [ringKrullDim_quotient, ringKrullDim_quotient, hz]

/-
Finite difference: if `P` is constant, its first difference vanishes.
-/
theorem firstDiff_eq_zero_of_natDegree_zero (P : Polynomial ℚ) (h : P.natDegree = 0) :
    P - P.comp (Polynomial.X - 1) = 0 := by
  rw [ Polynomial.eq_C_of_natDegree_eq_zero h ] ; simp +decide [ Polynomial.comp ] ;

/-
Finite difference: the first difference of a nonconstant polynomial has degree
one less.
-/
theorem natDegree_firstDiff (P : Polynomial ℚ) (h : 1 ≤ P.natDegree) :
    (P - P.comp (Polynomial.X - 1)).natDegree + 1 = P.natDegree := by
  refine' le_antisymm _ _;
  · refine' Nat.succ_le_of_lt ( lt_of_le_of_lt ( Polynomial.natDegree_le_of_degree_le _ ) _ );
    exact P.natDegree - 1;
    · rw [ Polynomial.degree_le_iff_coeff_zero ];
      norm_num [ Polynomial.comp, Polynomial.eval₂_eq_sum_range ];
      intro m hm; rw [ Finset.sum_eq_single m ] <;> norm_num [ Polynomial.coeff_X_pow, sub_eq_add_neg ] ;
      · erw [ ← Polynomial.C_neg, Polynomial.coeff_X_add_C_pow ] ; norm_num;
      · exact fun n hn hnm => Or.inr <| Polynomial.coeff_eq_zero_of_natDegree_lt <| by erw [ Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C ] ; norm_num ; omega;
      · exact fun h => Or.inl <| Polynomial.coeff_eq_zero_of_natDegree_lt h;
    · exact Nat.pred_lt ( ne_bot_of_gt h );
  · -- Let $d = P.natDegree$.
    set d := P.natDegree with hd
    have hd_pos : 1 ≤ d := by
      exact h;
    -- Consider the coefficient of $x^{d-1}$ in $P(x) - P(x-1)$.
    have h_coeff : Polynomial.coeff (P - P.comp (Polynomial.X - 1)) (d - 1) = d * Polynomial.leadingCoeff P := by
      rw [ Polynomial.comp, Polynomial.eval₂_eq_sum_range ];
      norm_num [ Finset.sum_range_succ, Polynomial.coeff_X_pow, sub_eq_add_neg ];
      erw [ Finset.sum_eq_single ( d - 1 ) ] <;> norm_num;
      · erw [ ← Polynomial.C_neg, Polynomial.coeff_X_add_C_pow, Polynomial.coeff_X_add_C_pow ] ; norm_num;
        rcases k : P.natDegree with ( _ | _ | k ) <;> simp_all +decide [ Nat.succ_eq_add_one, pow_add ] ; ring;
      · exact fun n hn hn' => Or.inr <| Polynomial.coeff_eq_zero_of_natDegree_lt <| by erw [ Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C ] ; norm_num ; omega;
      · exact fun h => absurd h ( Nat.not_le_of_gt ( Nat.pred_lt ( ne_bot_of_gt hd_pos ) ) );
    exact Nat.sub_le_iff_le_add.mp ( Polynomial.le_natDegree_of_ne_zero <| by aesop )

/-
Finite difference: the first difference of a nonconstant polynomial is nonzero.
-/
theorem firstDiff_ne_zero (P : Polynomial ℚ) (h : 1 ≤ P.natDegree) :
    P - P.comp (Polynomial.X - 1) ≠ 0 := by
  have := natDegree_firstDiff P h;
  intro H; simp_all +decide ;
  rw [ Polynomial.eq_X_add_C_of_natDegree_le_one ( le_of_eq this.symm ) ] at H; norm_num at H;
  replace H := congr_arg ( Polynomial.eval 0 ) H ; norm_num at H ; aesop

/-
**Dimension drop.** Cutting a proper homogeneous ideal by a nonzero linear form
that is a nonzerodivisor drops the Krull dimension of the quotient by exactly one.
-/
theorem dim_drop_of_linear_nzd (J : Ideal (MvPolynomial (Fin n) K)) (hJ : IsHomog J)
    (hne : J ≠ ⊤) {ℓ : MvPolynomial (Fin n) K} (hℓ : ℓ ∈ homogeneousSubmodule (Fin n) K 1)
    (hℓne : ℓ ≠ 0) (hreg : IsSMulRegular (MvPolynomial (Fin n) K ⧸ J) ℓ) :
    ringKrullDim (MvPolynomial (Fin n) K ⧸ (J ⊔ Ideal.span {ℓ})) + 1
      = ringKrullDim (MvPolynomial (Fin n) K ⧸ J) := by
  have h_drop : ringKrullDim ( ( MvPolynomial ( Fin n ) K ⧸ J ) ⧸ ( Ideal.span { Ideal.Quotient.mk J ℓ } : Ideal ( MvPolynomial ( Fin n ) K ⧸ J ) ) ) + 1 = ringKrullDim ( MvPolynomial ( Fin n ) K ⧸ J ) := by
    have h_r_nonzeroDivisor : Ideal.Quotient.mk J ℓ ∈ nonZeroDivisors (MvPolynomial (Fin n) K ⧸ J) := by
      refine' ⟨ fun x hx => _, fun x hx => _ ⟩;
      · convert hreg _;
        simp +decide [ Algebra.smul_def, hx ];
      · convert hreg _;
        convert hx using 1;
        · simp +decide [ mul_comm, Algebra.smul_def ];
        · simp +decide [ Algebra.smul_def ];
    have h_p_prime : (varsIdeal.map (Ideal.Quotient.mk J)).IsPrime := by
      convert Ideal.map_isPrime_of_surjective ( Ideal.Quotient.mk_surjective ) _ using 1;
      · convert varsIdeal_isMaximal.isPrime using 1;
      · simp +decide [ Ideal.mk_ker ];
        exact isHomogeneous_le_varsIdeal J ( ideal_isHomogeneous_of_IsHomog J hJ ) hne;
    convert Module.ringKrullDim_quotient_add_one_of_mem_nonZeroDivisors h_r_nonzeroDivisor _ _ using 1;
    exact Ideal.map ( Ideal.Quotient.mk J ) varsIdeal;
    · exact h_p_prime;
    · convert height_map_varsIdeal_eq_krullDim J hJ hne using 1;
    · exact Ideal.mem_map_of_mem _ ( show ℓ ∈ varsIdeal from by simpa using homogeneous_mem_varsIdeal_pow ( k := 1 ) ( e := 1 ) ( by norm_num ) hℓ );
  convert h_drop using 1;
  rw [ ← ringKrullDim_eq_of_ringEquiv ( DoubleQuot.quotQuotEquivQuotSup J ( Ideal.span { ℓ } ) ) ];
  rw [ Ideal.map_span, Set.image_singleton ]

/-
The sup of two homogeneous ideals is homogeneous.
-/
theorem isHomog_sup {A B : Ideal (MvPolynomial (Fin n) K)} (hA : IsHomog A) (hB : IsHomog B) :
    IsHomog (A ⊔ B) := by
  intro p hp e;
  rw [ Submodule.mem_sup ] at hp ⊢;
  obtain ⟨ y, hy, z, hz, rfl ⟩ := hp;
  exact ⟨ _, hA _ hy _, _, hB _ hz _, by rw [ map_add ] ⟩

/-
The ideal generated by a single homogeneous form is homogeneous.
-/
theorem isHomog_span_singleton {ℓ : MvPolynomial (Fin n) K} {d : ℕ} (hℓ : ℓ.IsHomogeneous d) :
    IsHomog (Ideal.span {ℓ}) := by
  intro p hp e;
  obtain ⟨q, rfl⟩ : ∃ q : MvPolynomial (Fin n) K, p = ℓ * q := by
    exact Ideal.mem_span_singleton.mp hp;
  by_cases he : d ≤ e;
  · convert Ideal.mul_mem_right _ _ ( Ideal.subset_span <| Set.mem_singleton ℓ ) using 1;
    rw [ homogeneousComponent_mul_left hℓ q he ];
  · have h_homogeneous : ∀ m ∈ (ℓ * q).support, m.degree ≥ d := by
      intro m hm; contrapose! hm; simp_all +decide [ MvPolynomial.coeff_mul ] ;
      refine' Finset.sum_eq_zero fun x hx => _;
      by_cases h : x.1.degree = d <;> simp_all +decide [ MvPolynomial.coeff_eq_zero_of_totalDegree_lt ];
      · exact Or.inl ( by rw [ hℓ.coeff_eq_zero ( by aesop ) ] );
      · exact Or.inl ( hℓ.coeff_eq_zero fun h' => h <| by simp_all +decide [ Finsupp.degree ] );
    rw [ homogeneousComponent_apply ];
    rw [ Finset.sum_eq_zero ] <;> simp_all +decide [ Ideal.mem_span_singleton ];
    exact fun m hm => ne_of_gt ( lt_of_lt_of_le he ( h_homogeneous m hm ) )

/-
A proper finite-dimensional quotient has Krull dimension `0`.
-/
theorem ringKrullDim_eq_zero_of_finiteDim (I : Ideal (MvPolynomial (Fin n) K)) (hne : I ≠ ⊤)
    [FiniteDimensional K (MvPolynomial (Fin n) K ⧸ I)] :
    ringKrullDim (MvPolynomial (Fin n) K ⧸ I) = 0 := by
  refine' le_antisymm _ _;
  · convert ( Module.finite_iff_krullDimLE_zero K ( MvPolynomial ( Fin n ) K ⧸ I ) ).mp ‹_› using 1;
    simp +decide [ Ring.KrullDimLE ];
    rw [ Order.krullDimLE_iff ];
    convert Iff.rfl using 1;
  · have h_nontrivial : Nontrivial (MvPolynomial (Fin n) K ⧸ I) := by
      exact Ideal.Quotient.nontrivial hne;
    convert ringKrullDim_nonneg_of_nontrivial;
    exact h_nontrivial

/-- If some Hilbert value vanishes, the quotient is finite-dimensional. -/
theorem finiteDim_of_HF_zero (I : Ideal (MvPolynomial (Fin n) K)) {e : ℕ} (h : HF I e = 0) :
    FiniteDimensional K (MvPolynomial (Fin n) K ⧸ I) := by
  obtain ⟨k, hk⟩ := varsPow_le_of_sat_top I (sat_top_of_HF_zero I h)
  exact finiteDim_of_varsPow_le I k hk

/-
Strong-induction core of the dimension bridge.
-/
set_option maxHeartbeats 1000000 in
theorem HF_natDegree_add_one_eq_krullDim_aux [Infinite K] :
    ∀ d : ℕ, ∀ (I : Ideal (MvPolynomial (Fin n) K)), IsHomog I → I ≠ ⊤ →
      ∀ (P : Polynomial ℚ), (∀ᶠ e in atTop, (HF I e : ℚ) = P.eval (e : ℚ)) → P ≠ 0 →
      P.natDegree = d →
      ((P.natDegree + 1 : ℕ) : WithBot ℕ∞) = ringKrullDim (MvPolynomial (Fin n) K ⧸ I) := by
  intro d
  induction' d using Nat.strong_induction_on with d ih generalizing n;
  intro I hI hne P hP hP0 hdeg;
  rcases n with ( _ | n ) <;> simp_all +decide [ HF_eventually_zero_of_finiteDim ];
  · have h_finite_dim : FiniteDimensional K (MvPolynomial (Fin 0) K ⧸ I) := by
      have h_finite_dim : FiniteDimensional K (MvPolynomial (Fin 0) K) := by
        refine' ⟨ _, _ ⟩;
        exact { 1 };
        simp +decide [ Submodule.eq_top_iff' ];
        intro x; exact (by
        rw [ MvPolynomial.eq_C_of_isEmpty x ] ; simp +decide [ Submodule.mem_span_singleton ];
        exact ⟨ coeff 0 x, by simp +decide [ Algebra.smul_def ] ⟩);
      infer_instance;
    have := HF_eventually_zero_of_finiteDim I hI; simp_all +decide [ Filter.eventually_atTop ] ;
    obtain ⟨ a, ha ⟩ := this; obtain ⟨ b, hb ⟩ := hP; exact False.elim ( hP0 <| poly_eq_zero_of_eventually_zero P <| Filter.eventually_atTop.mpr ⟨ Max.max a b, fun n hn => by simpa [ ha n ( le_trans ( le_max_left _ _ ) hn ) ] using hb n ( le_trans ( le_max_right _ _ ) hn ) |> Eq.symm ⟩ ) ;
  · -- Set J := sat I; hJhom := isHomog_sat I hI; hJsat := sat_sat I.
    set J := sat I with hJ
    have hJhom : IsHomog J := by
      exact isHomog_sat I hI
    have hJsat : sat J = sat I := by
      grind +suggestions
    have hJne : J ≠ ⊤ := by
      by_contra hJtop;
      have h_finiteDim : FiniteDimensional K (MvPolynomial (Fin (n + 1)) K ⧸ I) := by
        exact finiteDim_of_varsPow_le I ( Classical.choose ( varsPow_le_of_sat_top I hJtop ) ) ( Classical.choose_spec ( varsPow_le_of_sat_top I hJtop ) );
      have hP_zero : P = 0 := by
        apply poly_eq_zero_of_eventually_zero P;
        have := HF_eventually_zero_of_finiteDim I hI;
        filter_upwards [ this, Filter.eventually_ge_atTop hP.choose ] with e he₁ he₂ using by simpa [ he₁ ] using hP.choose_spec e he₂ |> Eq.symm;
      contradiction
    have hPJ : ∀ᶠ e in atTop, (HF J e : ℚ) = P.eval (e : ℚ) := by
      exact HF_saturation_eventually_eq I hI |> fun h => hP |> fun ⟨ a, ha ⟩ => h.and ( Filter.eventually_ge_atTop a ) |> fun h => h.mono fun e he => by aesop;
    obtain ⟨ℓ, hℓ⟩ := exists_linear_nzd J hJhom hJsat hJne;
    -- Set I' := J ⊔ Ideal.span {ℓ}; hI'hom := isHomog_sup hJhom (isHomog_span_singleton ((mem_homogeneousSubmodule 1 ℓ).mp hℓhom)).
    set I' := J ⊔ Ideal.span {ℓ} with hI'
    have hI'hom : IsHomog I' := by
      exact isHomog_sup hJhom ( isHomog_span_singleton ( by simpa using hℓ.1 ) )
    have hI'ne : I' ≠ ⊤ := by
      intro hI'top
      have hI'top' : ringKrullDim (MvPolynomial (Fin (n + 1)) K ⧸ I') = ⊥ := by
        convert ringKrullDim_eq_bot_of_subsingleton;
        rw [ hI'top ] ; infer_instance;
      have hI'top'' : ringKrullDim (MvPolynomial (Fin (n + 1)) K ⧸ J) ≥ 0 := by
        convert ringKrullDim_nonneg_of_nontrivial using 1;
        exact Ideal.Quotient.nontrivial hJne;
      have := dim_drop_of_linear_nzd J hJhom hJne hℓ.1 hℓ.2.1 hℓ.2.2; simp_all +decide ;
      exact absurd this ( by erw [ hI'top' ] ; exact ne_of_lt ( lt_of_lt_of_le ( by simp +decide ) hI'top'' ) )
    have hP' : ∀ᶠ e in atTop, (HF I' e : ℚ) = (P - P.comp (Polynomial.X - 1)).eval (e : ℚ) := by
      have hP' : ∀ᶠ e in atTop, (HF I' e : ℚ) + (HF J (e - 1) : ℚ) = (HF J e : ℚ) := by
        have := HF_step_regular J hJhom hℓ.1 ( by norm_num : 0 < 1 ) hℓ.2.2;
        exact Filter.eventually_atTop.mpr ⟨ 1, fun e he => mod_cast this e he ⟩;
      simp +zetaDelta at *;
      obtain ⟨ a, ha ⟩ := hPJ; obtain ⟨ b, hb ⟩ := hP'; use Max.max a b + 1; intros c hc; have := ha ( c - 1 ) ( Nat.le_sub_one_of_lt ( by linarith [ le_max_left a b, le_max_right a b ] ) ) ; have := hb c ( by linarith [ le_max_left a b, le_max_right a b ] ) ; simp_all +decide [ Nat.cast_sub ( show 1 ≤ c from by linarith [ le_max_left a b, le_max_right a b ] ) ] ;
      linarith [ ha c hc.1.le ];
    by_cases hP1 : P.natDegree = 0;
    · have hP'_zero : ∀ᶠ e in atTop, HF I' e = 0 := by
        rw [ Polynomial.eq_C_of_natDegree_eq_zero hP1 ] at hP' ; aesop;
      have hP'_zero : ringKrullDim (MvPolynomial (Fin (n + 1)) K ⧸ I') = 0 := by
        convert ringKrullDim_eq_zero_of_finiteDim I' hI'ne using 1;
        exact finiteDim_of_HF_zero I' ( hP'_zero.exists.choose_spec );
      have := dim_drop_of_linear_nzd J hJhom hJne hℓ.1 hℓ.2.1 hℓ.2.2; simp_all +decide ;
      rw [ krullDim_sat_eq I hI hJne ] at this ; aesop;
    · have hP'_deg : (P - P.comp (Polynomial.X - 1)).natDegree + 1 = P.natDegree := by
        exact natDegree_firstDiff P ( Nat.pos_of_ne_zero hP1 );
      have hP'_nonzero : P - P.comp (Polynomial.X - 1) ≠ 0 := by
        exact firstDiff_ne_zero P ( Nat.pos_of_ne_zero hP1 );
      obtain ⟨ x, hx ⟩ := Filter.eventually_atTop.mp hP';
      have := ih ( Polynomial.natDegree ( P - P.comp ( Polynomial.X - 1 ) ) ) ( by linarith ) I' hI'hom hI'ne ( P - P.comp ( Polynomial.X - 1 ) ) x hx hP'_nonzero rfl;
      have := dim_drop_of_linear_nzd J hJhom hJne hℓ.1 hℓ.2.1 hℓ.2.2; simp_all +decide [ add_comm, add_left_comm, add_assoc ] ;
      rw [ ← hP'_deg ] ; norm_cast at * ; simp_all +decide [ add_comm, add_left_comm, add_assoc ] ;
      convert this using 1;
      exact krullDim_sat_eq I hI hJne ▸ rfl

/-- Part 2 of the dimension bridge: for a nonzero Hilbert polynomial, its degree is
one less than the Krull dimension of the quotient. -/
theorem HF_natDegree_add_one_eq_krullDim [Infinite K]
    (I : Ideal (MvPolynomial (Fin n) K)) (hI : IsHomog I) (hne : I ≠ ⊤)
    (P : Polynomial ℚ) (hP : ∀ᶠ e in atTop, (HF I e : ℚ) = P.eval (e : ℚ)) (hP0 : P ≠ 0) :
    ((P.natDegree + 1 : ℕ) : WithBot ℕ∞) = ringKrullDim (MvPolynomial (Fin n) K ⧸ I) :=
  HF_natDegree_add_one_eq_krullDim_aux P.natDegree I hI hne P hP hP0 rfl

/-- 4. Dimension bridge: the eventual polynomial detects finite-dimensionality
and, when nonzero, its degree is one less than the Krull dimension of `R ⧸ I`. -/
theorem HF_poly_natDegree [Infinite K]
    (I : Ideal (MvPolynomial (Fin n) K)) (hI : IsHomog I) (hne : I ≠ ⊤)
    (P : Polynomial ℚ) (hP : ∀ᶠ e in atTop, (HF I e : ℚ) = P.eval (e : ℚ)) :
    (P = 0 ↔ FiniteDimensional K (MvPolynomial (Fin n) K ⧸ I)) ∧
    (P ≠ 0 → ((P.natDegree + 1 : ℕ) : WithBot ℕ∞) =
      ringKrullDim (MvPolynomial (Fin n) K ⧸ I)) := by
  refine ⟨?_, ?_⟩
  · constructor
    · intro hP0
      rw [hP0] at hP
      simp only [Polynomial.eval_zero] at hP
      obtain ⟨e0, he0⟩ := hP.exists
      have hHF : HF I e0 = 0 := by exact_mod_cast he0
      obtain ⟨k, hk⟩ := varsPow_le_of_sat_top I (sat_top_of_HF_zero I hHF)
      exact finiteDim_of_varsPow_le I k hk
    · intro hfd
      have hev : ∀ᶠ e in atTop, P.eval ((e : ℕ) : ℚ) = 0 := by
        filter_upwards [HF_eventually_zero_of_finiteDim I hI, hP] with e hz he
        rw [← he, hz]; simp
      exact poly_eq_zero_of_eventually_zero P hev
  · intro hP0
    exact HF_natDegree_add_one_eq_krullDim I hI hne P hP hP0

/-
A nonzero rational polynomial eventually nonnegative on the naturals has positive
leading coefficient.
-/
theorem leadingCoeff_pos_of_eventually_nonneg (P : Polynomial ℚ) (hP0 : P ≠ 0)
    (h : ∀ᶠ e in atTop, 0 ≤ P.eval ((e : ℕ) : ℚ)) : 0 < P.leadingCoeff := by
  by_contra h_neg;
  -- Since $P$ is a nonzero polynomial with a non-positive leading coefficient, $P$ tends to $-\infty$ as $x$ tends to $\infty$.
  have h_tendsto_neg_infty : Filter.Tendsto (fun x : ℚ => P.eval x) Filter.atTop Filter.atBot := by
    cases lt_or_eq_of_le ( le_of_not_gt h_neg ) <;> simp_all +decide [ Polynomial.tendsto_atBot_iff_leadingCoeff_nonpos ];
    contrapose! h;
    rw [ Polynomial.eq_C_of_degree_le_zero h ] at hP0 ‹P.leadingCoeff < 0› ⊢ ; aesop;
  contrapose! h;
  exact h_tendsto_neg_infty.comp tendsto_natCast_atTop_atTop |> fun h => h.eventually ( Filter.eventually_lt_atBot 0 ) |> fun h => h.frequently

/-- 5. Positivity for proper saturated ideals. -/
theorem HF_poly_leadingCoeff_pos [Infinite K]
    (I : Ideal (MvPolynomial (Fin n) K)) (hI : IsHomog I)
    (hsat : sat I = I) (hne : I ≠ ⊤)
    (P : Polynomial ℚ) (hP : ∀ᶠ e in atTop, (HF I e : ℚ) = P.eval (e : ℚ)) :
    P ≠ 0 ∧ 0 < P.leadingCoeff := by
  have hP0 : P ≠ 0 := by
    intro hP0
    rw [hP0] at hP
    simp only [Polynomial.eval_zero] at hP
    obtain ⟨e0, he0⟩ := hP.exists
    have hHF : HF I e0 = 0 := by exact_mod_cast he0
    have := sat_top_of_HF_zero I hHF
    rw [hsat] at this
    exact hne this
  refine ⟨hP0, ?_⟩
  refine leadingCoeff_pos_of_eventually_nonneg P hP0 ?_
  filter_upwards [hP] with e he
  rw [← he]
  exact_mod_cast Nat.zero_le _

end
