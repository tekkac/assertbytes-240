import Mathlib

/-!
# Affine Bézout in two variables — supporting lemmas

Proves the two ingredients for the `n = 2` 0-dimensional finrank bound:
extraction of a coprime pair from a bounded-degree ideal, and the affine
Bézout finrank estimate for that pair.
-/

noncomputable section
open MvPolynomial

namespace AffineBezout

variable {K : Type*} [Field K]

/-
A two-variable polynomial with both partial degrees zero, if nonzero, is a unit
(it is a nonzero constant).
-/
theorem isUnit_of_degreeOf_eq_zero (p : MvPolynomial (Fin 2) K) (hp0 : p ≠ 0)
    (h0 : degreeOf 0 p = 0) (h1 : degreeOf 1 p = 0) : IsUnit p := by
  -- From both, every monomial in the support is the zero function, so support ⊆ {0}, hence p = C (p.coeff 0).
  have h_support : p.support ⊆ {0} := by
    simp_all +decide [ degreeOf_eq_sup ];
    exact Finset.eq_singleton_iff_nonempty_unique_mem.mpr ⟨ Finset.nonempty_of_ne_empty ( by aesop ), fun i hi => by ext j; fin_cases j <;> aesop ⟩;
  -- Since the support of $p$ is a subset of $\{0\}$, we have $p = C(p.coeff 0)$.
  have h_eq_C : p = MvPolynomial.C (p.coeff 0) := by
    ext m; by_cases hm : m = 0 <;> simp_all +decide [ MvPolynomial.coeff_C ] ;
    exact fun _ => by rw [ MvPolynomial.notMem_support_iff.mp ( by aesop ) ] ;
  rw [ h_eq_C ] at hp0 ⊢; simp_all +singlePass ;

/-
A divisor of a polynomial with `degreeOf i = 0` also has `degreeOf i = 0`.
-/
theorem degreeOf_eq_zero_of_dvd {a b : MvPolynomial (Fin 2) K} (i : Fin 2)
    (hab : a ∣ b) (hb : b ≠ 0) (h : degreeOf i b = 0) : degreeOf i a = 0 := by
  cases hab;
  rename_i c hc;
  by_cases ha : a = 0 <;> by_cases hc : c = 0 <;> simp_all +decide [ degreeOf_mul_eq ]

/-
If the quotient by `span {p}` is finite dimensional, then for each variable `i`
there is a nonzero multiple of `p` involving only that variable.
-/
theorem exists_dvd_single_var (p : MvPolynomial (Fin 2) K) (i : Fin 2)
    [FiniteDimensional K (MvPolynomial (Fin 2) K ⧸ Ideal.span {p})] :
    ∃ Q : MvPolynomial (Fin 2) K, Q ≠ 0 ∧ (∀ j, j ≠ i → degreeOf j Q = 0) ∧ p ∣ Q := by
  obtain ⟨q, hq⟩ : ∃ q : Polynomial K, q ≠ 0 ∧ Polynomial.aeval (MvPolynomial.X i : MvPolynomial (Fin 2) K) q ∈ Ideal.span {p} := by
    -- By definition of $A$, we know that $x_i$ is algebraic over $K$.
    have h_alg : IsIntegral K (Ideal.Quotient.mk (Ideal.span {p}) (MvPolynomial.X i)) := by
      exact IsIntegral.of_finite K ((Ideal.Quotient.mk (Ideal.span {p})) (X i))
    obtain ⟨ q, hq ⟩ := h_alg;
    refine' ⟨ q, hq.1.ne_zero, _ ⟩;
    rw [ Polynomial.aeval_def, Polynomial.eval₂_eq_sum_range ] at *;
    erw [ ← Ideal.Quotient.eq_zero_iff_mem ] ; aesop;
  refine' ⟨ Polynomial.aeval ( MvPolynomial.X i ) q, _, _, _ ⟩;
  · simp_all +decide [ Polynomial.aeval_def ];
    rw [ Polynomial.eval₂_eq_sum_range ];
    intro h; replace h := congr_arg ( fun f => MvPolynomial.coeff ( Finsupp.single i ( q.natDegree ) ) f ) h; simp_all +decide [ MvPolynomial.coeff_sum, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X_pow ] ;
    rw [ Finset.sum_eq_single ( q.natDegree ) ] at h <;> simp_all +decide [ Finsupp.single_eq_single_iff ];
    aesop;
  · intro j hj;
    simp +decide [ Polynomial.aeval_eq_sum_range, degreeOf_eq_sup ];
    simp +decide [ MvPolynomial.coeff_sum, MvPolynomial.coeff_smul, MvPolynomial.coeff_X_pow ];
    intro m hm; contrapose! hm; simp_all +decide;
    rw [ Finset.sum_eq_zero ] ; intros ; aesop;
  · exact Ideal.mem_span_singleton.mp hq.2

/-- A quotient by a single nonunit is never finite dimensional over `K`
(the curve `V(p)` is positive dimensional). -/
theorem quotient_span_single_not_finiteDimensional
    (p : MvPolynomial (Fin 2) K) (hp : ¬ IsUnit p) :
    ¬ FiniteDimensional K (MvPolynomial (Fin 2) K ⧸ Ideal.span {p}) := by
  intro hfd
  obtain ⟨Q0, hQ0ne, hQ0deg, hpQ0⟩ := exists_dvd_single_var p 0
  obtain ⟨Q1, hQ1ne, hQ1deg, hpQ1⟩ := exists_dvd_single_var p 1
  have hp0 : p ≠ 0 := by
    rintro rfl; exact hQ0ne (by simpa using hpQ0)
  have hd1 : degreeOf 1 p = 0 :=
    degreeOf_eq_zero_of_dvd 1 hpQ0 hQ0ne (hQ0deg 1 (by decide))
  have hd0 : degreeOf 0 p = 0 :=
    degreeOf_eq_zero_of_dvd 0 hpQ1 hQ1ne (hQ1deg 0 (by decide))
  exact hp (isUnit_of_degreeOf_eq_zero p hp0 hd0 hd1)

/-
`K[x,y]` itself is not finite dimensional over `K`.
-/
theorem not_finiteDimensional_self :
    ¬ FiniteDimensional K (MvPolynomial (Fin 2) K) := by
  -- Consider the infinite basis $\{X_0^i \mid i \in \mathbb{N}\}$ for $K[X_0]$.
  have h_basis : LinearIndependent K (fun i : ℕ => (MvPolynomial.X 0 : MvPolynomial (Fin 2) K)^i) := by
    refine' linearIndependent_iff'.mpr _;
    intro s g hg i hi; replace hg := congr_arg ( fun p => MvPolynomial.coeff ( Finsupp.single 0 i ) p ) hg; simp_all +decide [ MvPolynomial.coeff_sum, MvPolynomial.coeff_X_pow ] ;
    simp_all +decide [ Finsupp.single_eq_single_iff ];
    rw [ Finset.sum_eq_single i ] at hg <;> aesop;
  contrapose! h_basis
  exact Module.Finite.not_linearIndependent_of_infinite fun i => X 0 ^ i

/-
If the quotient by the span of a family is finite dimensional, some member is
nonzero (otherwise the span is `⊥` and the whole ring would be finite dimensional).
-/
theorem exists_nonzero_generator {ι : Type*} [Fintype ι]
    (f : ι → MvPolynomial (Fin 2) K)
    [FiniteDimensional K (MvPolynomial (Fin 2) K ⧸ Ideal.span (Set.range f))] :
    ∃ i, f i ≠ 0 := by
  have h_inf : ¬ FiniteDimensional K (MvPolynomial (Fin 2) K ⧸ (⊥ : Ideal (MvPolynomial (Fin 2) K))) := by
    convert not_finiteDimensional_self using 1
    convert Iff.rfl
    exact Iff.symm (Module.Finite.iff_cofg_bot K (MvPolynomial (Fin 2) K))
  grind +suggestions

/-
A nonzero element of the UFD `K[x,y]` has a finite set of irreducible factors
covering (up to associates) every irreducible divisor.
-/
theorem exists_finset_irreducible_factors
    (g : MvPolynomial (Fin 2) K) (hg : g ≠ 0) :
    ∃ P : Finset (MvPolynomial (Fin 2) K),
      (∀ π ∈ P, Irreducible π ∧ π ∣ g) ∧
      (∀ π, Irreducible π → π ∣ g → ∃ π' ∈ P, Associated π π') := by
  by_contra h;
  -- By definition of prime factors, there exists a finite set of irreducible factors of g.
  have h_prime_factors : ∃ P : Multiset (MvPolynomial (Fin 2) K), (∀ π ∈ P, Irreducible π ∧ π ∣ g) ∧ (∀ π : MvPolynomial (Fin 2) K, Irreducible π → π ∣ g → ∃ π' ∈ P, Associated π π') := by
    obtain ⟨ P, hP ⟩ := UniqueFactorizationMonoid.exists_prime_factors g hg;
    refine' ⟨ P, _, _ ⟩;
    · exact fun π hπ => ⟨ hP.1 π hπ |> Prime.irreducible, dvd_trans ( Multiset.dvd_prod hπ ) ( hP.2.dvd ) ⟩;
    · intro π hπ hπg
      have h_div : π ∣ P.prod := by
        exact dvd_trans hπg ( hP.2.symm.dvd );
      have h_div : ∀ {m : Multiset (MvPolynomial (Fin 2) K)}, (∀ π ∈ m, Prime π) → π ∣ m.prod → ∃ π' ∈ m, π ∣ π' := by
        intros m hm h_div; induction m using Multiset.induction <;> simp_all +decide [ dvd_mul_of_dvd_left, dvd_mul_of_dvd_right ] ;
        · exact hπ.not_dvd_one h_div;
        · exact Classical.or_iff_not_imp_left.2 fun h => by have := hπ.prime.dvd_or_dvd h_div; tauto;
      obtain ⟨ π', hπ', hππ' ⟩ := h_div hP.1 ‹_›;
      exact ⟨ π', hπ', hπ.associated_of_dvd ( hP.1 π' hπ' |> Prime.irreducible ) hππ' ⟩;
  convert h ⟨ h_prime_factors.choose.toFinset, ?_, ?_ ⟩;
  exact Classical.decEq _;
  · grind +splitImp;
  · grind +locals

/-
Avoidance: if for every irreducible factor `π` of `g` some `f j` is not divisible
by `π`, then some `K`-linear combination of the `f j` is relatively prime to `g`.
-/
theorem avoid_factors [IsAlgClosed K] {ι : Type*} [Fintype ι]
    (g : MvPolynomial (Fin 2) K) (hg : g ≠ 0) (f : ι → MvPolynomial (Fin 2) K)
    (hdvd : ∀ π, Irreducible π → π ∣ g → ∃ j, ¬ π ∣ f j) :
    ∃ c : ι → K, IsRelPrime g (∑ j, C (c j) * f j) := by
  -- By `Submodule.exists_forall_notMem_of_forall_ne_top` with the family indexed by the subtype `P` (i.e. `fun π : P => Sπ`), which is `Finite` (Finset), over the infinite field K: get c with `∀ π : P, c ∉ Sπ`, i.e. `∀ π ∈ P, ¬ π ∣ ∑ j, C (c j) * f j` (using the iff, contrapositive).
  obtain ⟨c, hc⟩ : ∃ c : ι → K, ∀ π : MvPolynomial (Fin 2) K, Irreducible π → π ∣ g → ¬π ∣ ∑ j, C (c j) * f j := by
    obtain ⟨ P, hP₁, hP₂ ⟩ := exists_finset_irreducible_factors g hg;
    have hS : ∀ π ∈ P, ∃ Sπ : Submodule K (ι → K), (∀ c : ι → K, c ∈ Sπ ↔ π ∣ ∑ j, C (c j) * f j) ∧ Sπ ≠ ⊤ := by
      intro π hπ
      obtain ⟨j₀, hj₀⟩ := hdvd π (hP₁ π hπ).left (hP₁ π hπ).right
      set Lπ : (ι → K) →ₗ[K] MvPolynomial (Fin 2) K ⧸ Ideal.span {π} := LinearMap.comp (Ideal.Quotient.mkₐ K (Ideal.span {π})) (show (ι → K) →ₗ[K] MvPolynomial (Fin 2) K from ∑ j, (LinearMap.smulRight (LinearMap.proj j) (f j))) with hLπ
      have hSπ : ∃ Sπ : Submodule K (ι → K), (∀ c : ι → K, c ∈ Sπ ↔ π ∣ ∑ j, C (c j) * f j) := by
        refine' ⟨ LinearMap.ker Lπ, fun c => _ ⟩;
        simp +decide [ Lπ, Ideal.Quotient.eq_zero_iff_mem ];
        rw [ ← map_sum, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton ];
        simp +decide [ Algebra.smul_def ];
      obtain ⟨ Sπ, hSπ ⟩ := hSπ;
      refine' ⟨ Sπ, hSπ, _ ⟩;
      intro hSπ_top
      have h_contra : π ∣ f j₀ := by
        convert hSπ ( fun j => if j = j₀ then 1 else 0 ) |>.1 ( hSπ_top.symm ▸ Submodule.mem_top ) using 1 ; simp +decide [ Finset.sum_ite, Finset.filter_eq', Finset.filter_ne' ];
        rw [ Finset.sum_eq_single j₀ ] <;> simp +contextual;
        exact fun j => Classical.propDecidable (j = j₀)
      contradiction;
    choose! S hS₁ hS₂ using hS;
    obtain ⟨c, hc⟩ : ∃ c : ι → K, ∀ π ∈ P, c ∉ S π := by
      convert Submodule.exists_forall_notMem_of_forall_ne_top ( fun π : P => S π ) ( fun π => hS₂ π π.2 ) using 1;
      simp +decide [ funext_iff ];
    use c;
    intro π hπ₁ hπ₂ hπ₃; obtain ⟨ π', hπ'₁, hπ'₂ ⟩ := hP₂ π hπ₁ hπ₂; specialize hc π' hπ'₁; simp_all +decide [ Associated ] ;
    obtain ⟨ u, rfl ⟩ := hπ'₂; simp_all +decide ;
  refine' ⟨ c, fun d hdg hdh => _ ⟩;
  contrapose! hc;
  exact Exists.elim ( WfDvdMonoid.exists_irreducible_factor hc ( by aesop ) ) fun π hπ => ⟨ π, hπ.1, hπ.2.trans hdg, hπ.2.trans hdh ⟩

/-
Two injective endomorphisms with the same range differ by a linear automorphism.
-/
theorem exists_linearEquiv_of_range_eq
    {R Mod : Type*} [CommRing R] [AddCommGroup Mod] [Module R Mod]
    {Φ D : Mod →ₗ[R] Mod} (hΦ : Function.Injective Φ) (hD : Function.Injective D)
    (hr : LinearMap.range D = LinearMap.range Φ) :
    ∃ e : Mod ≃ₗ[R] Mod, D = Φ ∘ₗ (e : Mod →ₗ[R] Mod) := by
  -- Define the linear equivalence e by composing D' with the inverse of Φ'.
  set D' : Mod ≃ₗ[R] LinearMap.range D := LinearEquiv.ofInjective D hD
  set Φ' : Mod ≃ₗ[R] LinearMap.range Φ := LinearEquiv.ofInjective Φ hΦ
  set e : Mod ≃ₗ[R] Mod := D'.trans ((LinearEquiv.ofEq _ _ hr : LinearMap.range D ≃ₗ[R] LinearMap.range Φ).trans Φ'.symm);
  refine' ⟨ e, _ ⟩;
  ext x;
  simp +decide [ e, D', Φ' ]

/-
For an injective `K[X]`-linear endomorphism of a finite free `K[X]`-module `M`
(carrying a compatible `K`-action), the `K`-dimension of the cokernel equals the
degree of the determinant.  (Smith normal form over the PID `K[X]`.)
-/
theorem finrank_quotient_range_eq_natDegree_det
    {M : Type*} [AddCommGroup M] [Module (Polynomial K) M] [Module K M]
    [IsScalarTower K (Polynomial K) M] [Module.Free (Polynomial K) M]
    [Module.Finite (Polynomial K) M]
    (Φ : M →ₗ[Polynomial K] M) (hΦ : Function.Injective Φ) :
    Module.finrank K (M ⧸ LinearMap.range Φ) = (LinearMap.det Φ).natDegree := by
  revert Φ;
  intro Φ hΦ_inj
  set R := Polynomial K
  set N := LinearMap.range Φ
  have h := LinearMap.finrank_range_of_inj hΦ_inj
  let b := Module.finBasis R M
  set bM := Submodule.smithNormalFormTopBasis b h
  set bN := Submodule.smithNormalFormBotBasis b h
  set a := Submodule.smithNormalFormCoeffs b h
  have hN_decomp : N = Submodule.span R (Set.range (fun i => (bN i : M))) := by
    have hN_decomp : Submodule.span R (Set.range (fun i => (bN i : M))) = Submodule.map N.subtype (Submodule.span R (Set.range bN)) := by
      rw [ Submodule.map_span ];
      exact congr_arg _ ( by ext; aesop );
    aesop
  have h_det_D : LinearMap.det (bM.constr R (fun i => (bN i : M))) = ∏ i, a i := by
    have h_det_D : LinearMap.toMatrix bM bM (bM.constr R (fun i => (bN i : M))) = Matrix.diagonal a := by
      ext i j; simp +decide [ LinearMap.toMatrix_apply, bM.constr_basis ] ;
      by_cases hij : i = j <;> simp +decide [ hij, Submodule.smithNormalFormBotBasis_def ];
      · rw [ show ( bN j : M ) = a j • bM j from Submodule.smithNormalFormBotBasis_def b h j ] ; simp +decide [ bM.repr_self ];
      · rw [ show ( bN j : M ) = a j • bM j from Submodule.smithNormalFormBotBasis_def b h j ] ; simp +decide [ hij, bM.repr_self ] ;
    rw [ ← LinearMap.det_toMatrix bM, h_det_D, Matrix.det_diagonal ]
  have h_range_D : LinearMap.range (bM.constr R (fun i => (bN i : M))) = N := by
    convert bM.constr_range _
  have h_det_eq : Associated (LinearMap.det Φ) (∏ i, a i) := by
    have h_det_eq : ∃ e : M ≃ₗ[R] M, (bM.constr R (fun i => (bN i : M))) = Φ ∘ₗ e := by
      apply exists_linearEquiv_of_range_eq;
      · exact hΦ_inj;
      · have h_det_ne_zero : LinearMap.det (bM.constr R (fun i => (bN i : M))) ≠ 0 := by
          rw [ h_det_D ];
          exact Finset.prod_ne_zero_iff.mpr fun i _ => Submodule.smithNormalFormCoeffs_ne_zero b h i;
        have h_det_ne_zero : ∀ (f : M →ₗ[R] M), LinearMap.det f ≠ 0 → Function.Injective f := by
          intro f hf_det_ne_zero
          have h_det_ne_zero : LinearMap.ker f = ⊥ := by
            grind +suggestions;
          exact LinearMap.ker_eq_bot.mp h_det_ne_zero;
        exact h_det_ne_zero _ ‹_›;
      · exact h_range_D;
    obtain ⟨ e, he ⟩ := h_det_eq
    have h_det_eq : LinearMap.det (bM.constr R (fun i => (bN i : M))) = LinearMap.det Φ * LinearMap.det (e : M →ₗ[R] M) := by
      rw [ he, LinearMap.det_comp ];
    rw [ ← h_det_D, h_det_eq ];
    have h_det_e : LinearMap.det (e : M →ₗ[R] M) * LinearMap.det (e.symm : M →ₗ[R] M) = 1 := by
      simp +decide [ ← LinearMap.det_comp ];
    exact ⟨ Units.mkOfMulEqOne _ _ h_det_e, by simp +decide ⟩
  have h_finrank_N : Module.finrank K (M ⧸ N) = ∑ i, (a i).natDegree := by
    have h_finrank_N : ∀ i, FiniteDimensional K (R ⧸ Ideal.span {a i}) := by
      intro i
      have h_nonzero : a i ≠ 0 := by
        exact Submodule.smithNormalFormCoeffs_ne_zero b h i
      exact (AdjoinRoot.powerBasis h_nonzero).finite;
    convert Submodule.finrank_quotient_eq_sum K b h using 1;
    refine' Finset.sum_congr rfl fun i _ => _;
    have := @finrank_quotient_span_eq_natDegree K;
    exact this.symm
  have h_det_natDegree_eq : (LinearMap.det Φ).natDegree = (∏ i, a i).natDegree := by
    exact Polynomial.natDegree_eq_of_degree_eq ( Polynomial.degree_eq_degree_of_associated h_det_eq )
  have h_final : Module.finrank K (M ⧸ N) = (∏ i, a i).natDegree := by
    rw [ h_finrank_N, Polynomial.natDegree_prod ];
    exact fun i _ => Submodule.smithNormalFormCoeffs_ne_zero b h i
  exact (by
  rw [h_final, h_det_natDegree_eq])

/-
Determinant degree bound: if every entry of an `m × m` matrix over `K[X]`
satisfies `natDegree (M i j) + i ≤ D + j`, then `natDegree (det M) ≤ m * D`.

Weighted-degree ("total degree") is preserved by `modByMonic` against a monic
divisor whose own weighted degree is `≤ natDegree`.  The weight of the `Y`-power-`k`
coefficient `Q.coeff k` (an element of `K[X]`) is `(Q.coeff k).natDegree + k`.

Companion to the crux: the cokernel of an injective endomorphism of a finite free
`K[X]`-module is finite dimensional over `K`.
-/
theorem finrank_quotient_range_finiteDimensional
    {M : Type*} [AddCommGroup M] [Module (Polynomial K) M] [Module K M]
    [IsScalarTower K (Polynomial K) M] [Module.Free (Polynomial K) M]
    [Module.Finite (Polynomial K) M]
    (Φ : M →ₗ[Polynomial K] M) (hΦ : Function.Injective Φ) :
    FiniteDimensional K (M ⧸ LinearMap.range Φ) := by
  -- Let `N := LinearMap.range Φ`, `h := LinearMap.finrank_range_of_inj hΦ` (full rank), `b := Module.finBasis (Polynomial K) M`, and `a := Submodule.smithNormalFormCoeffs` for this `h`.
  set N := LinearMap.range Φ
  set h := LinearMap.finrank_range_of_inj hΦ
  set b := Module.finBasis (Polynomial K) M
  set a := Submodule.smithNormalFormCoeffs b h;
  -- By definition of `a`, each `a i` is nonzero.
  have ha_nonzero : ∀ i, a i ≠ 0 := by
    apply Submodule.smithNormalFormCoeffs_ne_zero;
  -- By `Submodule.quotientEquivDirectSum`, there is a K-linear equivalence `(M ⧸ N) ≃ₗ[K] ⨁ i, R ⧸ Ideal.span {a i}`.
  have h_equiv : (M ⧸ N) ≃ₗ[K] (DirectSum (Fin (Module.finrank (Polynomial K) M)) fun i => (Polynomial K) ⧸ (Ideal.span {a i})) := by
    convert Submodule.quotientEquivDirectSum K b h;
  -- Each summand `R ⧸ Ideal.span {a i}` with `a i ≠ 0` is finite dimensional over K.
  have h_summand_finite : ∀ i, FiniteDimensional K ((Polynomial K) ⧸ (Ideal.span {a i})) := by
    intro i;
    convert ( AdjoinRoot.powerBasis ( ha_nonzero i ) ).finite;
  convert h_equiv.symm.finiteDimensional

set_option maxHeartbeats 1600000 in
theorem modByMonic_weighted_le (G : Polynomial (Polynomial K)) (hG : G.Monic)
    (hGtot : ∀ k, G.coeff k ≠ 0 → (G.coeff k).natDegree + k ≤ G.natDegree)
    (Q : Polynomial (Polynomial K)) (W : ℕ)
    (hQ : ∀ k, Q.coeff k ≠ 0 → (Q.coeff k).natDegree + k ≤ W) :
    ∀ i, (Q %ₘ G).coeff i ≠ 0 → ((Q %ₘ G).coeff i).natDegree + i ≤ W := by
  by_contra h_contra;
  obtain ⟨N, hN⟩ : ∃ N, N = Q.natDegree ∧ ¬(∀ i, (Q %ₘ G).coeff i ≠ 0 → (Polynomial.natDegree ((Q %ₘ G).coeff i)) + i ≤ W) := by
    exact ⟨ _, rfl, h_contra ⟩;
  induction' N using Nat.strong_induction_on with N ih generalizing Q;
  by_cases h_deg : Polynomial.natDegree G ≤ N;
  · -- Let $c := Q.coeff N$ and $k := N - G.natDegree$.
    set c := Q.coeff N
    set k := N - G.natDegree
    set Q₁ := Q - Polynomial.C c * Polynomial.X ^ k * G
    have hQ₁ : Q₁ %ₘ G = Q %ₘ G := by
      rw [ Polynomial.sub_modByMonic ] ; aesop
    have hQ₁_deg : Polynomial.natDegree Q₁ < N := by
      have hQ₁_deg : Polynomial.coeff Q₁ N = 0 := by
        simp +zetaDelta at *;
        rw [ Polynomial.coeff_mul, Finset.sum_eq_single ( N - G.natDegree, G.natDegree ) ] <;> simp +decide [ hG, h_deg ];
        exact fun a b hab h₁ h₂ => False.elim <| h₁ h₂ <| by omega;
      rw [ Polynomial.natDegree_lt_iff_degree_lt, Polynomial.degree_lt_iff_coeff_zero ];
      · intro m hm; rcases eq_or_lt_of_le hm with rfl | hm' <;> simp_all +decide [ Polynomial.coeff_eq_zero_of_natDegree_lt ] ;
        rw [ Polynomial.coeff_sub, Polynomial.coeff_eq_zero_of_natDegree_lt hm', Polynomial.coeff_eq_zero_of_natDegree_lt ];
        · norm_num;
        · by_cases hc : c = 0 <;> by_cases hG : G = 0 <;> simp_all +decide [ Polynomial.natDegree_mul' ];
          · linarith;
          · omega;
      · rw [ eq_comm ] at hQ₁ ; aesop ( simp_config := { singlePass := true } ) ;
    have hQ₁_bound : ∀ j, Q₁.coeff j ≠ 0 → (Polynomial.natDegree (Q₁.coeff j)) + j ≤ W := by
      intro j hj
      have hQ₁_coeff : Q₁.coeff j = Q.coeff j - (Polynomial.C c * Polynomial.X ^ k * G).coeff j := by
        simp [Q₁]
      have hQ₁_coeff_bound : (Polynomial.natDegree ((Polynomial.C c * Polynomial.X ^ k * G).coeff j)) + j ≤ W := by
        by_cases hk : k ≤ j <;> simp_all +decide [ mul_assoc, Polynomial.coeff_C_mul ];
        · by_cases h : G.coeff ( j - k ) = 0 <;> simp_all +decide [ Polynomial.coeff_mul ];
          · rw [ Finset.sum_eq_zero ] <;> simp_all +decide [ Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk ];
            · linarith [ hQ j hj ];
            · aesop;
          · have hQ₁_coeff_bound : (Polynomial.natDegree (c * G.coeff (j - k))) + j ≤ W := by
              have hQ₁_coeff_bound : (Polynomial.natDegree c) + N ≤ W ∧ (Polynomial.natDegree (G.coeff (j - k))) + (j - k) ≤ G.natDegree := by
                exact ⟨ hQ N ( by aesop ), hGtot _ h ⟩;
              have hQ₁_coeff_bound : (Polynomial.natDegree (c * G.coeff (j - k))) ≤ (Polynomial.natDegree c) + (Polynomial.natDegree (G.coeff (j - k))) := by
                exact Polynomial.natDegree_mul_le;
              omega;
            rw [ Finset.sum_eq_single ( k, j - k ) ] <;> aesop;
        · rw [ Polynomial.coeff_mul, Finset.sum_eq_zero ] <;> simp_all +decide [ Polynomial.coeff_X_pow ];
          · exact le_trans ( Nat.le_of_lt hk ) ( Nat.sub_le_of_le_add <| by linarith [ hQ N <| by aesop ] );
          · intros; linarith;
      have hQ₁_coeff_bound' : (Polynomial.natDegree (Q₁.coeff j)) + j ≤ W := by
        have hQ₁_coeff_bound' : (Polynomial.natDegree (Q₁.coeff j)) ≤ max (Polynomial.natDegree (Q.coeff j)) (Polynomial.natDegree ((Polynomial.C c * Polynomial.X ^ k * G).coeff j)) := by
          exact hQ₁_coeff.symm ▸ Polynomial.natDegree_sub_le _ _ |> le_trans <| max_le_max ( le_rfl ) ( le_rfl ) ;
        by_cases h : Q.coeff j = 0 <;> simp_all +decide [ add_comm ];
        cases hQ₁_coeff_bound' <;> linarith [ hQ j h ]
      exact hQ₁_coeff_bound'
    exact ih (Polynomial.natDegree Q₁) (by
    exact hQ₁_deg) Q₁ hQ₁_bound (by
    exact hQ₁.symm ▸ hN.2) ⟨by
    rfl, by
      exact hQ₁.symm ▸ hN.2⟩;
  · have h_mod : Q %ₘ G = Q := by
      rw [ Polynomial.modByMonic_eq_self_iff ];
      · rw [ Polynomial.degree_eq_natDegree, Polynomial.degree_eq_natDegree ] <;> norm_cast <;> aesop;
      · exact hG;
    grind

theorem Matrix_det_natDegree_le_shift {m : ℕ}
    (M : Matrix (Fin m) (Fin m) (Polynomial K)) (D : ℕ)
    (hM : ∀ i j, M i j ≠ 0 → (M i j).natDegree + (i : ℕ) ≤ D + (j : ℕ)) :
    (M.det).natDegree ≤ m * D := by
  rw [ Matrix.det_apply' ];
  refine' le_trans ( Polynomial.natDegree_sum_le _ _ ) ( Finset.sup_le _ );
  intro σ _; by_cases hσ : ∃ i, M (σ i) i = 0 <;> simp_all +decide ;
  · obtain ⟨ i, hi ⟩ := hσ; simp +decide [ Finset.prod_eq_zero ( Finset.mem_univ i ), hi ] ;
  · refine' le_trans ( Polynomial.natDegree_mul_le .. ) _;
    refine' le_trans ( add_le_add ( Polynomial.natDegree_C _ |> le_of_eq ) ( Polynomial.natDegree_prod_le _ _ ) ) _;
    have := Equiv.sum_comp σ fun i => ( i : ℕ ) ; simp_all +decide ;
    have := Finset.sum_le_sum fun i ( hi : i ∈ Finset.univ ) => hM ( σ i ) i ( hσ i ) ; simp_all +decide [ Finset.sum_add_distrib ] ;

/-
Monic core, finrank part: `finrank_K (K[x][Y] / (G,H))` equals the degree of the
determinant of multiplication by the image of `H` in `AdjoinRoot G` (which is
`K[x][Y]/(G)`), when `G` is monic and `G, H` share no factor.
-/
set_option maxHeartbeats 800000 in
theorem poly_quot_finrank_eq_det
    (G H : Polynomial (Polynomial K)) (hG : G.Monic) (hcop : IsRelPrime G H) :
    FiniteDimensional K (Polynomial (Polynomial K) ⧸ Ideal.span {G, H}) ∧
    Module.finrank K (Polynomial (Polynomial K) ⧸ Ideal.span {G, H})
      = (LinearMap.det (LinearMap.mulLeft (Polynomial K) (AdjoinRoot.mk G H))).natDegree := by
  have h_quotient : (Polynomial (Polynomial K) ⧸ Ideal.span {G, H}) ≃ₐ[K] (AdjoinRoot G ⧸ Ideal.span {(AdjoinRoot.mk G) H}) := by
    rw [ Ideal.span_insert ];
    have h_quotient : ∀ (I J : Ideal (Polynomial (Polynomial K))), (Polynomial (Polynomial K) ⧸ (I ⊔ J)) ≃ₐ[K] (Polynomial (Polynomial K) ⧸ I) ⧸ Ideal.map (Ideal.Quotient.mk I) J := by
      intro I J;
      have := DoubleQuot.quotQuotEquivQuotSupₐ K I J;
      exact this.symm;
    convert h_quotient ( Ideal.span { G } ) ( Ideal.span { H } ) using 1;
    · rw [ Ideal.map_span ] ; aesop;
    · congr! 1;
      rw [ Ideal.map_span ] ; aesop;
    · congr! 1;
      rw [ Ideal.map_span ] ; aesop;
  have h_finrank : FiniteDimensional K (AdjoinRoot G ⧸ Ideal.span {(AdjoinRoot.mk G) H}) ∧ Module.finrank K (AdjoinRoot G ⧸ Ideal.span {(AdjoinRoot.mk G) H}) = (LinearMap.det (LinearMap.mulLeft (Polynomial K) ((AdjoinRoot.mk G) H))).natDegree := by
    have h_injective : Function.Injective (LinearMap.mulLeft (Polynomial K) ((AdjoinRoot.mk G) H)) := by
      intro x y hxy;
      obtain ⟨ p, rfl ⟩ := AdjoinRoot.mk_surjective x; obtain ⟨ q, rfl ⟩ := AdjoinRoot.mk_surjective y; simp_all +decide [ AdjoinRoot.mk_eq_mk ] ;
      erw [ AdjoinRoot.mk_eq_mk ] at hxy;
      exact hcop.dvd_of_dvd_mul_left ( by simpa only [ mul_sub ] using hxy );
    have h_finrank : Module.finrank K (AdjoinRoot G ⧸ Ideal.span {(AdjoinRoot.mk G) H}) = (LinearMap.det (LinearMap.mulLeft (Polynomial K) ((AdjoinRoot.mk G) H))).natDegree := by
      convert finrank_quotient_range_eq_natDegree_det ( LinearMap.mulLeft ( Polynomial K ) ( AdjoinRoot.mk G H ) ) h_injective using 1;
      · rw [ show ( LinearMap.mulLeft ( Polynomial K ) ( AdjoinRoot.mk G H ) ).range = Submodule.restrictScalars ( Polynomial K ) ( Ideal.span { ( AdjoinRoot.mk G H ) } ) from ?_ ];
        · convert rfl;
        · ext; simp [LinearMap.mem_range, Ideal.mem_span_singleton];
          exact ⟨ fun ⟨ y, hy ⟩ => ⟨ y, hy.symm ⟩, fun ⟨ y, hy ⟩ => ⟨ y, hy.symm ⟩ ⟩;
      · convert Module.Free.of_basis ( AdjoinRoot.powerBasis' hG ).basis;
      · exact Polynomial.Monic.finite_adjoinRoot hG;
    have h_finiteDimensional : FiniteDimensional K (AdjoinRoot G ⧸ LinearMap.range (LinearMap.mulLeft (Polynomial K) ((AdjoinRoot.mk G) H))) := by
      convert finrank_quotient_range_finiteDimensional ( LinearMap.mulLeft ( Polynomial K ) ( AdjoinRoot.mk G H ) ) h_injective;
      · convert Module.Free.of_basis ( PowerBasis.basis ( AdjoinRoot.powerBasis' hG ) );
      · exact Polynomial.Monic.finite_adjoinRoot hG;
    convert h_finiteDimensional;
    rw [ show ( LinearMap.mulLeft ( Polynomial K ) ( AdjoinRoot.mk G H ) ).range = Submodule.restrictScalars ( Polynomial K ) ( Ideal.span { ( AdjoinRoot.mk G ) H } ) from ?_ ];
    · constructor <;> intro h <;> have := h <;> simp_all +decide [ Submodule.restrictScalars ];
      · convert this.1;
      · convert h;
    · ext; simp [LinearMap.mem_range, Ideal.mem_span_singleton];
      exact ⟨ fun ⟨ y, hy ⟩ => ⟨ y, hy.symm ⟩, fun ⟨ y, hy ⟩ => ⟨ y, hy.symm ⟩ ⟩;
  convert h_finrank using 1;
  · exact ⟨ fun _ => h_finrank.1, fun _ => by exact h_quotient.symm.toLinearEquiv.finiteDimensional ⟩;
  · rw [ ← h_finrank.2, ← h_quotient.toLinearEquiv.finrank_eq ]

/-
Monic core, degree bound: the determinant of multiplication by `AdjoinRoot.mk G H`
has `natDegree ≤ (deg_Y G)(dH)` when the weighted (total) degrees of `G` and `H` are
controlled.
-/
theorem mulLeft_det_natDegree_le
    (G H : Polynomial (Polynomial K)) (hG : G.Monic)
    (hGtot : ∀ k, G.coeff k ≠ 0 → (G.coeff k).natDegree + k ≤ G.natDegree)
    (dH : ℕ) (hHtot : ∀ k, H.coeff k ≠ 0 → (H.coeff k).natDegree + k ≤ dH) :
    (LinearMap.det (LinearMap.mulLeft (Polynomial K) (AdjoinRoot.mk G H))).natDegree
      ≤ G.natDegree * dH := by
  convert Matrix_det_natDegree_le_shift _ dH _;
  rotate_left;
  exact ( LinearMap.toMatrix ( AdjoinRoot.powerBasis' hG ).basis ( AdjoinRoot.powerBasis' hG ).basis ) ( LinearMap.mulLeft ( Polynomial K ) ( AdjoinRoot.mk G H ) );
  · intro i j hij;
    -- By definition of matrix multiplication and the properties of the power basis, we have:
    have h_coeff : (LinearMap.toMatrix (AdjoinRoot.powerBasis' hG).basis (AdjoinRoot.powerBasis' hG).basis (LinearMap.mulLeft (Polynomial K) (AdjoinRoot.mk G H))) i j = ((Polynomial.X ^ (j : ℕ) * H) %ₘ G).coeff (i : ℕ) := by
      simp +decide [ LinearMap.toMatrix_apply, AdjoinRoot.powerBasis' ];
      simp +decide [ AdjoinRoot.powerBasisAux', mul_comm ];
      rw [ Finset.sum_eq_single j ] <;> simp +decide [ Polynomial.X_pow_eq_monomial ];
      · erw [ AdjoinRoot.modByMonicHom_mk ];
      · aesop;
    have := modByMonic_weighted_le G hG hGtot ( Polynomial.X ^ ( j : ℕ ) * H ) ( dH + ( j : ℕ ) ) ?_ i ?_ <;> simp_all +decide [ Polynomial.coeff_mul ];
    intro k hk; rw [ Finset.sum_eq_single ( j.val, k - j.val ) ] <;> simp_all +decide [ Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk ] ;
    · linarith [ hHtot ( k - j ) hk.2, Nat.sub_add_cancel hk.1 ];
    · intros; omega;
  · exact
      Eq.symm
        (LinearMap.det_toMatrix (AdjoinRoot.powerBasis' hG).basis
          (LinearMap.mulLeft (Polynomial K) ((AdjoinRoot.mk G) H)))

/-- Monic core (combined): for `G` monic and coprime to `H` in `K[x][Y]`, with the
total-degree bounds, `K[x][Y]/(G,H)` is finite dimensional of dimension `≤ (deg_Y G)·dH`. -/
theorem poly_bezout
    (G H : Polynomial (Polynomial K)) (hG : G.Monic) (hcop : IsRelPrime G H)
    (hGtot : ∀ k, G.coeff k ≠ 0 → (G.coeff k).natDegree + k ≤ G.natDegree)
    (dH : ℕ) (hHtot : ∀ k, H.coeff k ≠ 0 → (H.coeff k).natDegree + k ≤ dH) :
    FiniteDimensional K (Polynomial (Polynomial K) ⧸ Ideal.span {G, H}) ∧
    Module.finrank K (Polynomial (Polynomial K) ⧸ Ideal.span {G, H}) ≤ G.natDegree * dH := by
  obtain ⟨hfin, heq⟩ := poly_quot_finrank_eq_det G H hG hcop
  exact ⟨hfin, heq ▸ mulLeft_det_natDegree_le G H hG hGtot dH hHtot⟩

/-- Transport equivalence `K[x₀] ≅ K[x]` (single variable to univariate). -/
def E1 : MvPolynomial (Fin 1) K ≃ₐ[K] Polynomial K :=
  (MvPolynomial.finSuccEquiv K 0).trans
    (Polynomial.mapAlgEquiv (MvPolynomial.isEmptyAlgEquiv K (Fin 0)))

/-- Transport equivalence `K[x₀,x₁] ≅ K[x][Y]` (with `Y` the image of `x₀`). -/
def E : MvPolynomial (Fin 2) K ≃ₐ[K] Polynomial (Polynomial K) :=
  (MvPolynomial.finSuccEquiv K 1).trans (Polynomial.mapAlgEquiv E1)

/-- For a one-variable multivariate polynomial, `degreeOf 0` equals the total degree. -/
theorem degreeOf_zero_eq_totalDegree (c : MvPolynomial (Fin 1) K) :
    degreeOf 0 c = c.totalDegree := by
  rw [MvPolynomial.degreeOf_eq_sup, MvPolynomial.totalDegree]
  apply Finset.sup_congr rfl
  intro m hm
  have : ∑ x ∈ m.support, m x = ∑ x : Fin 1, m x :=
    Finset.sum_subset (Finset.subset_univ _) (fun x _ hx => Finsupp.notMem_support_iff.mp hx)
  simp only [Finsupp.sum, this, Fin.sum_univ_one]

/-- `E1` does not increase degree: `natDegree (E1 c) ≤ totalDegree c`. -/
theorem E1_natDegree_le (c : MvPolynomial (Fin 1) K) : (E1 c).natDegree ≤ c.totalDegree := by
  unfold E1
  simp only [AlgEquiv.trans_apply]
  rw [show (Polynomial.mapAlgEquiv (MvPolynomial.isEmptyAlgEquiv K (Fin 0)))
        (MvPolynomial.finSuccEquiv K 0 c)
      = (MvPolynomial.finSuccEquiv K 0 c).map (MvPolynomial.isEmptyAlgEquiv K (Fin 0)).toRingEquiv by
        simp [Polynomial.mapAlgEquiv]]
  refine le_trans (Polynomial.natDegree_map_le) ?_
  rw [natDegree_finSuccEquiv, degreeOf_zero_eq_totalDegree]

/-- Transport degree bound: the weight `natDegree + k` of the `Y^k`-coefficient of
`E p` is bounded by the total degree of `p`. -/
theorem coeff_E_add_le (p : MvPolynomial (Fin 2) K) (k : ℕ)
    (hk : (E p).coeff k ≠ 0) : ((E p).coeff k).natDegree + k ≤ p.totalDegree := by
  set f := MvPolynomial.finSuccEquiv K 1 p with hf
  have hcoeff : (E p).coeff k = E1 (f.coeff k) := by
    unfold E
    simp [Polynomial.mapAlgEquiv, Polynomial.coeff_map, hf]
  have hfk : f.coeff k ≠ 0 := by
    intro h; apply hk; rw [hcoeff, h, map_zero]
  calc ((E p).coeff k).natDegree + k = (E1 (f.coeff k)).natDegree + k := by rw [hcoeff]
    _ ≤ (f.coeff k).totalDegree + k := Nat.add_le_add_right (E1_natDegree_le _) k
    _ ≤ p.totalDegree := MvPolynomial.totalDegree_coeff_finSuccEquiv_add_le p k hfk

/-- Monic transport: if `E g` is monic and `g`'s total degree equals its `Y`-degree,
the affine Bézout bound for `(g,h)` follows from the `K[x][Y]` monic core. -/
theorem bezout_monic_transport (g h : MvPolynomial (Fin 2) K) (hcop : IsRelPrime g h)
    (hmonic : (E g).Monic) (hdeg : g.totalDegree ≤ (E g).natDegree) :
    FiniteDimensional K (MvPolynomial (Fin 2) K ⧸ Ideal.span {g, h}) ∧
    Module.finrank K (MvPolynomial (Fin 2) K ⧸ Ideal.span {g, h})
      ≤ g.totalDegree * h.totalDegree := by
  have hcop' : IsRelPrime (E g) (E h) := by
    intro d hdg hdh
    have h1 : E.symm d ∣ g := by simpa using map_dvd E.symm hdg
    have h2 : E.symm d ∣ h := by simpa using map_dvd E.symm hdh
    have hu := hcop h1 h2
    simpa using hu.map E.toRingEquiv
  have hEgne : E g ≠ 0 := hmonic.ne_zero
  have hEgle : (E g).natDegree ≤ g.totalDegree := by
    have hlc : (E g).coeff (E g).natDegree ≠ 0 := by
      rw [Polynomial.coeff_natDegree]
      exact Polynomial.leadingCoeff_ne_zero.mpr hEgne
    have := coeff_E_add_le g (E g).natDegree hlc
    omega
  have hEgeq : (E g).natDegree = g.totalDegree := le_antisymm hEgle hdeg
  have hGtot : ∀ k, (E g).coeff k ≠ 0 → ((E g).coeff k).natDegree + k ≤ (E g).natDegree := by
    intro k hk; rw [hEgeq]; exact coeff_E_add_le g k hk
  have hHtot : ∀ k, (E h).coeff k ≠ 0 → ((E h).coeff k).natDegree + k ≤ h.totalDegree :=
    fun k hk => coeff_E_add_le h k hk
  obtain ⟨hfin, hbound⟩ := poly_bezout (E g) (E h) hmonic hcop' hGtot h.totalDegree hHtot
  have hmap : Ideal.span {E g, E h} = Ideal.map (↑E) (Ideal.span {g, h}) := by
    rw [Ideal.map_span, Set.image_pair]
  let iso := Ideal.quotientEquivAlg (Ideal.span {g, h}) (Ideal.span {E g, E h}) E hmap
  haveI := hfin
  refine ⟨iso.symm.toLinearEquiv.finiteDimensional, ?_⟩
  rw [iso.toLinearEquiv.finrank_eq]
  calc Module.finrank K (Polynomial (Polynomial K) ⧸ Ideal.span {E g, E h})
      ≤ (E g).natDegree * h.totalDegree := hbound
    _ = g.totalDegree * h.totalDegree := by rw [hEgeq]

/-
========================================================================
   Generic shear to monic position (closing `bezout_two_curves`)
   ========================================================================

Degree-`≤ 1` substitutions do not increase total degree.
-/
theorem totalDegree_aeval_le {σ τ R : Type*} [CommSemiring R]
    (f : σ → MvPolynomial τ R) (hf : ∀ i, (f i).totalDegree ≤ 1)
    (p : MvPolynomial σ R) : (aeval f p).totalDegree ≤ p.totalDegree := by
  rw [ MvPolynomial.as_sum p ];
  simp +decide only [map_sum, aeval_monomial];
  have h_deg : ∀ m ∈ p.support, (MvPolynomial.totalDegree (MvPolynomial.C (p.coeff m) * m.prod (fun i k => (f i) ^ k))) ≤ m.sum (fun i k => k) := by
    intro m hm
    have h_deg : (m.prod (fun i k => (f i) ^ k)).totalDegree ≤ m.sum (fun i k => k) := by
      have h_deg : ∀ i ∈ m.support, (f i ^ m i).totalDegree ≤ m i := by
        intro i hi;
        exact Nat.recOn ( m i ) ( by simp +decide ) fun n ihn => by simpa only [ pow_succ' ] using le_trans ( MvPolynomial.totalDegree_mul _ _ ) ( by linarith [ hf i ] ) ;
      have h_deg : ∀ {S : Finset σ}, (∀ i ∈ S, (f i ^ m i).totalDegree ≤ m i) → (Finset.prod S (fun i => f i ^ m i)).totalDegree ≤ Finset.sum S (fun i => m i) := by
        intro S hS; induction S using Finset.induction <;> simp_all +decide [ Finset.sum_insert, Finset.prod_insert ] ;
        · exact le_trans ( MvPolynomial.totalDegree_mul _ _ ) ( add_le_add hS.1 ‹_› );
        · exact Classical.decEq σ;
      exact h_deg ‹_›;
    exact le_trans ( MvPolynomial.totalDegree_mul _ _ ) ( by aesop );
  have h_deg_sum : ∀ {S : Finset (σ →₀ ℕ)}, (∀ m ∈ S, (MvPolynomial.totalDegree (MvPolynomial.C (p.coeff m) * m.prod (fun i k => (f i) ^ k))) ≤ p.totalDegree) → (MvPolynomial.totalDegree (∑ m ∈ S, MvPolynomial.C (p.coeff m) * m.prod (fun i k => (f i) ^ k))) ≤ p.totalDegree := by
    intro S hS; induction S using Finset.induction <;> simp_all +decide ;
    · exact le_trans ( MvPolynomial.totalDegree_add _ _ ) ( max_le hS.1 ‹_› );
    · exact Classical.decEq _;
  convert h_deg_sum _;
  · conv_rhs => rw [ p.as_sum ] ;
  · exact fun m hm => le_trans ( h_deg m hm ) ( MvPolynomial.le_totalDegree hm )

/-- The forward shear `X₀ ↦ X₀`, `X₁ ↦ X₁ + c·X₀` as an algebra hom. -/
def shearHom (c : K) : MvPolynomial (Fin 2) K →ₐ[K] MvPolynomial (Fin 2) K :=
  aeval ![X 0, X 1 + C c * X 0]

theorem shearHom_apply_comp (c : K) :
    (shearHom (-c)).comp (shearHom c) = AlgHom.id K (MvPolynomial (Fin 2) K) := by
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i <;>
    simp [shearHom, AlgHom.comp_apply, Matrix.cons_val_zero, Matrix.cons_val_one]

/-- The shear automorphism `X₀ ↦ X₀`, `X₁ ↦ X₁ + c·X₀`. -/
def shear (c : K) : MvPolynomial (Fin 2) K ≃ₐ[K] MvPolynomial (Fin 2) K :=
  AlgEquiv.ofAlgHom (shearHom c) (shearHom (-c))
    (by have h := shearHom_apply_comp (-c); rwa [neg_neg] at h)
    (shearHom_apply_comp c)

theorem shear_apply (c : K) (p : MvPolynomial (Fin 2) K) :
    (shear c) p = aeval ![X 0, X 1 + C c * X 0] p := rfl

/-
The shear preserves total degree.
-/
theorem shear_totalDegree (c : K) (p : MvPolynomial (Fin 2) K) :
    (shear c p).totalDegree = p.totalDegree := by
  have h_total_degree_le : (shear c p).totalDegree ≤ p.totalDegree := by
    convert totalDegree_aeval_le _ _ p using 1;
    simp +decide [ Fin.forall_fin_two ];
    refine' le_trans ( MvPolynomial.totalDegree_add _ _ ) _ ; simp +decide [ MvPolynomial.totalDegree_X ];
    exact le_trans ( MvPolynomial.totalDegree_mul _ _ ) ( by simp +decide );
  refine' le_antisymm h_total_degree_le _;
  have h_total_degree_ge : (shear (-c) (shear c p)).totalDegree ≤ (shear c p).totalDegree := by
    apply totalDegree_aeval_le;
    simp +decide [ Fin.forall_fin_two ];
    refine' le_trans ( MvPolynomial.totalDegree_add _ _ ) _ ; simp +decide [ MvPolynomial.totalDegree_X ];
    exact le_trans ( MvPolynomial.totalDegree_mul _ _ ) ( by simp +decide );
  convert h_total_degree_ge using 1;
  convert rfl using 2;
  convert ( shear c ).symm_apply_apply p using 1

/-- Transport of the pair-quotient along an algebra automorphism. -/
def quotSpanPairAlgEquiv (φ : MvPolynomial (Fin 2) K ≃ₐ[K] MvPolynomial (Fin 2) K)
    (g h : MvPolynomial (Fin 2) K) :
    (MvPolynomial (Fin 2) K ⧸ Ideal.span {g, h}) ≃ₐ[K]
      (MvPolynomial (Fin 2) K ⧸ Ideal.span {φ g, φ h}) :=
  Ideal.quotientEquivAlg _ _ φ (by rw [Ideal.map_span, Set.image_pair]; rfl)

/-
Rescaling a generator by a nonzero constant leaves the ideal unchanged.
-/
theorem span_pair_C_mul_left (a : K) (ha : a ≠ 0) (u v : MvPolynomial (Fin 2) K) :
    Ideal.span ({C a * u, v} : Set (MvPolynomial (Fin 2) K)) = Ideal.span {u, v} := by
  refine' le_antisymm _ _ <;> simp +decide [ Ideal.span_le, Set.insert_subset_iff ];
  · exact ⟨ Ideal.mul_mem_left _ _ ( Ideal.subset_span ( Set.mem_insert _ _ ) ), Ideal.subset_span ( Set.mem_insert_of_mem _ ( Set.mem_singleton _ ) ) ⟩;
  · refine' ⟨ _, Ideal.subset_span ( Set.mem_insert_of_mem _ ( Set.mem_singleton _ ) ) ⟩
    generalize_proofs at *; (
    rw [ Ideal.mem_span_pair ];
    exact ⟨ C a⁻¹, 0, by rw [ show C a⁻¹ * ( C a * u ) = u by rw [ ← mul_assoc, ← MvPolynomial.C_mul, inv_mul_cancel₀ ha, MvPolynomial.C_1, one_mul ] ] ; ring ⟩)

/-
For a homogeneous form `F` of degree `D`, the coefficient of `X₀^D` in the
sheared form `shear c F` is `F(1, c)`.
-/
theorem coeff_top_shear_homogeneous (c : K) (F : MvPolynomial (Fin 2) K) (D : ℕ)
    (hF : F.IsHomogeneous D) :
    coeff (Finsupp.single 0 D) (shear c F) = eval ![1, c] F := by
  convert MvPolynomial.eval_eq ( fun i => if i = 0 then 1 else 0 ) ( ( shear c ) F ) using 1;
  · have h_homogeneous : (shear c F).IsHomogeneous D := by
      convert MvPolynomial.IsHomogeneous.aeval ( hF ) _ _ using 1;
      rw [ one_mul ];
      simp +decide [ Fin.forall_fin_two, MvPolynomial.isHomogeneous_X ];
      exact MvPolynomial.IsHomogeneous.add ( MvPolynomial.isHomogeneous_X _ _ ) ( MvPolynomial.IsHomogeneous.mul ( MvPolynomial.isHomogeneous_C _ _ ) ( MvPolynomial.isHomogeneous_X _ _ ) );
    rw [ MvPolynomial.eval_eq' ];
    rw [ Finset.sum_eq_single ( Finsupp.single 0 D ) ] <;> simp +contextual [ h_homogeneous ];
    intro b hb hb' hb''; have := h_homogeneous hb; simp_all +decide [ Finsupp.weight ] ;
    simp_all +decide [ Finsupp.linearCombination_apply, Finsupp.sum_fintype ];
    exact hb' ( Finsupp.ext fun i => by fin_cases i <;> simp +decide [ * ] );
  · convert MvPolynomial.eval_eq ( fun i => if i = 0 then 1 else 0 ) ( ( shear c ) F ) using 1;
    erw [ MvPolynomial.aeval_bind₁ ];
    congr ; ext i ; fin_cases i <;> simp +decide [ MvPolynomial.aeval_X ]

/-
The top `X₀`-coefficient of `shear c g` only sees the top homogeneous part of `g`.
-/
theorem coeff_top_shear_eq_component (c : K) (g : MvPolynomial (Fin 2) K) :
    coeff (Finsupp.single 0 g.totalDegree) (shear c g)
      = coeff (Finsupp.single 0 g.totalDegree)
          (shear c (homogeneousComponent g.totalDegree g)) := by
  -- By definition of `shear`, we know that `shear c g = ∑ k ∈ Finset.range (g.totalDegree + 1), shear c (homogeneousComponent k g)`.
  have h_shear : (shear c) g = ∑ k ∈ Finset.range (g.totalDegree + 1), (shear c) (homogeneousComponent k g) := by
    rw [ ← map_sum, MvPolynomial.sum_homogeneousComponent ];
  -- For $k < D$, the top $X_0$-coefficient of $\text{shear}(c, F_k)$ is zero.
  have h_zero : ∀ k < g.totalDegree, coeff (Finsupp.single 0 g.totalDegree) (shear c (homogeneousComponent k g)) = 0 := by
    intro k hk_lt_totalDegree
    by_cases hk_zero : homogeneousComponent k g = 0;
    · aesop;
    · have h_total_degree_lt : (shear c (homogeneousComponent k g)).totalDegree < g.totalDegree := by
        have h_total_degree_lt : (homogeneousComponent k g).totalDegree = k := by
          exact MvPolynomial.IsHomogeneous.totalDegree ( MvPolynomial.homogeneousComponent_isHomogeneous k g ) hk_zero;
        rw [ shear_totalDegree ] ; linarith;
      contrapose! h_total_degree_lt;
      exact MvPolynomial.le_totalDegree ( Finsupp.mem_support_iff.mpr h_total_degree_lt ) |> le_trans ( by simp +decide [ Finsupp.sum_single_index ] );
  rw [ h_shear, Finset.sum_range_succ ] ; simp +decide [ h_zero ] ;
  rw [ MvPolynomial.coeff_sum, Finset.sum_eq_zero ] ; aesop

/-- The univariate specialization `X₀ ↦ 1`, `X₁ ↦ X`. -/
def dehom (F : MvPolynomial (Fin 2) K) : Polynomial K :=
  aeval ![Polynomial.C 1, Polynomial.X] F

theorem dehom_eval (F : MvPolynomial (Fin 2) K) (c : K) :
    (dehom F).eval c = eval ![1, c] F := by
  simp +decide [ dehom, MvPolynomial.eval_eq', Polynomial.eval_finset_sum ];
  simp +decide [ Polynomial.eval_finset_sum, MvPolynomial.aeval_def, MvPolynomial.eval₂_eq' ]

theorem dehom_ne_zero_of_homogeneous (F : MvPolynomial (Fin 2) K) (D : ℕ)
    (hF : F.IsHomogeneous D) (hF0 : F ≠ 0) : dehom F ≠ 0 := by
  simp +decide [ dehom, Polynomial.ext_iff ];
  obtain ⟨ m, hm ⟩ := F.support_nonempty.2 hF0; use m 1; simp_all +decide [ Polynomial.coeff_X_pow, MvPolynomial.aeval_def, MvPolynomial.eval₂_eq' ] ;
  rw [ Finset.sum_eq_single m ] <;> simp_all +decide [ MvPolynomial.IsHomogeneous ];
  intro n hn hnm; contrapose! hnm; ext i; fin_cases i <;> simp_all +decide [ IsWeightedHomogeneous ] ;
  have := hF hm; have := hF hn; simp_all +decide [ Finsupp.weight ] ;
  have := hF hm; have := hF hn; simp_all +decide [ Finsupp.linearCombination_apply, Finsupp.sum_fintype ] ;
  linarith [ hF hn ]

/-
Genericity: over an infinite field there is a shear making the top `X₀`-coefficient
nonzero (so the sheared curve is in monic position).
-/
theorem exists_shear_leadingCoeff [Infinite K] (g : MvPolynomial (Fin 2) K) (hg : g ≠ 0) :
    ∃ c : K, coeff (Finsupp.single 0 g.totalDegree) (shear c g) ≠ 0 := by
  obtain ⟨c, hc⟩ : ∃ c : K, (MvPolynomial.eval ![1, c] (MvPolynomial.homogeneousComponent g.totalDegree g)) ≠ 0 := by
    convert dehom_ne_zero_of_homogeneous ( MvPolynomial.homogeneousComponent g.totalDegree g ) ( g.totalDegree ) ( MvPolynomial.homogeneousComponent_isHomogeneous _ _ ) _ using 1;
    · constructor <;> intro h <;> contrapose! h <;> simp_all +decide [ Polynomial.ext_iff ];
      · intro c; specialize h; rw [ ← dehom_eval ] ; simp_all +decide [ Polynomial.eval_eq_sum_range ] ;
      · exact fun n => by rw [ show dehom ( homogeneousComponent g.totalDegree g ) = 0 from Polynomial.funext fun x => by simpa [ dehom_eval ] using h x ] ; simp +decide ;
    · simp +decide [ hg, MvPolynomial.coeff_homogeneousComponent ];
      simp +decide [ hg, homogeneousComponent_apply ];
      simp +decide [ MvPolynomial.ext_iff ];
      obtain ⟨ m, hm ⟩ := Finset.exists_max_image g.support ( fun x => x.degree ) ⟨ Classical.choose ( Finset.nonempty_of_ne_empty ( by aesop_cat : g.support ≠ ∅ ) ), Classical.choose_spec ( Finset.nonempty_of_ne_empty ( by aesop_cat : g.support ≠ ∅ ) ) ⟩ ; use m; simp_all +decide [ MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial ] ;
      exact le_antisymm ( Finset.le_sup ( f := fun x => Finsupp.degree x ) ( by aesop ) ) ( Finset.sup_le fun x hx => hm.2 x ( by aesop ) );
  exact ⟨ c, by rw [ coeff_top_shear_eq_component, coeff_top_shear_homogeneous _ _ _ ( MvPolynomial.homogeneousComponent_isHomogeneous _ _ ) ] ; exact hc ⟩

/-
`E` reads off the `X₀`-degree as its `natDegree`.
-/
theorem E_natDegree (p : MvPolynomial (Fin 2) K) : (E p).natDegree = degreeOf 0 p := by
  convert MvPolynomial.natDegree_finSuccEquiv p using 1;
  convert Polynomial.natDegree_map_eq_of_injective _ _;
  exact RingEquiv.injective _

/-
If the top `X₀`-coefficient of `p` is a nonzero constant `a`, then after rescaling by
`a⁻¹` the polynomial is in monic position for `E`.
-/
theorem E_monic_of_top_coeff (p : MvPolynomial (Fin 2) K) (a : K) (ha : a ≠ 0)
    (hcoeff : coeff (Finsupp.single 0 p.totalDegree) p = a) :
    (E (C a⁻¹ * p)).Monic ∧
      (C a⁻¹ * p).totalDegree ≤ (E (C a⁻¹ * p)).natDegree := by
  have h_deg : (E p).natDegree = p.totalDegree := by
    rw [ E_natDegree, le_antisymm_iff ];
    refine' ⟨ MvPolynomial.degreeOf_le_totalDegree p 0, _ ⟩;
    refine' Finset.sup_le _;
    intro b hb; rw [ degreeOf_eq_sup ] ; simp +decide [ Finsupp.sum_fintype ] ;
    have := MvPolynomial.le_totalDegree hb; simp_all +decide [ Finsupp.sum_fintype ] ;
    refine' le_trans _ ( Finset.le_sup <| show ( fun₀ | 0 => p.totalDegree ) ∈ p.support from _ ) <;> simp_all +decide [ Finsupp.single_apply ];
  have h_leading_coeff : (E p).coeff (p.totalDegree) = Polynomial.C a := by
    have h_coeff : (MvPolynomial.finSuccEquiv K 1 p).coeff p.totalDegree = MvPolynomial.C a := by
      ext m; simp [MvPolynomial.finSuccEquiv_coeff_coeff];
      split_ifs with hm <;> simp_all +decide [ Finsupp.cons ];
      · convert hcoeff using 2 ; ext i ; fin_cases i ; aesop;
        simp +decide [ Finsupp.equivFunOnFinite, hm.symm ];
      · rw [ MvPolynomial.coeff_eq_zero_of_totalDegree_lt ];
        simp +decide [ Finset.sum_filter, Fin.sum_univ_succ ];
        split_ifs <;> simp_all +decide [ Finsupp.ext_iff, Fin.forall_fin_two ]; all_goals exact Nat.pos_of_ne_zero ‹_›;
    unfold E;
    simp +decide [ Polynomial.mapAlgEquiv, h_coeff ];
    unfold E1; simp +decide [ MvPolynomial.finSuccEquiv ] ;
  have h_leading_coeff_inv : (E (MvPolynomial.C a⁻¹ * p)).leadingCoeff = Polynomial.C (a⁻¹ * a) := by
    convert congr_arg ( fun x : Polynomial ( Polynomial K ) => x.leadingCoeff ) ( show E ( C a⁻¹ * p ) = Polynomial.C ( Polynomial.C a⁻¹ ) * E p from ?_ ) using 1;
    · rw [ Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C ];
      rw [ Polynomial.leadingCoeff, h_deg, h_leading_coeff, Polynomial.C_mul ];
    · simp +decide [ E, Polynomial.map_mul, Polynomial.map_C ];
      simp +decide [ E1, MvPolynomial.finSuccEquiv ];
  simp_all +decide [ Polynomial.Monic ];
  rw [ Polynomial.natDegree_mul' ] <;> simp_all +decide [ Polynomial.leadingCoeff_eq_zero ];
  refine' le_trans ( MvPolynomial.totalDegree_mul _ _ ) _ ; simp +decide

/-- Affine Bézout upper bound for two plane curves with no common factor:
`K[x,y]/(g,h)` is finite dimensional with `K`-dimension `≤ (deg g)(deg h)`.

Given `g` in *monic position* (i.e. `E g` monic with `g.totalDegree = (E g).natDegree`),
`bezout_monic_transport` establishes exactly this bound.  The reduction to monic position is
carried out here by a generic linear change of coordinates: the shear
`X₁ ↦ X₁ + c·X₀` (`shear c`), with `c` chosen over the infinite field `K` so that the top
`X₀`-coefficient of `shear c g` is a nonzero constant (`exists_shear_leadingCoeff`), followed
by a unit rescaling (`E_monic_of_top_coeff`).  The shear is an algebra automorphism, so it
preserves the quotient dimension (`quotSpanPairAlgEquiv`) and total degrees
(`shear_totalDegree`); the harmless edge case `Ideal.span {g,h} = ⊤` (trivial quotient) is
handled separately.  Requires `[Infinite K]` for the genericity argument. -/
theorem bezout_two_curves [Infinite K]
    (g h : MvPolynomial (Fin 2) K) (hco : IsRelPrime g h) :
    FiniteDimensional K (MvPolynomial (Fin 2) K ⧸ Ideal.span {g, h}) ∧
      Module.finrank K (MvPolynomial (Fin 2) K ⧸ Ideal.span {g, h})
        ≤ g.totalDegree * h.totalDegree := by
  by_cases hTop : Ideal.span { g, h } = ⊤;
  · rw [ hTop ];
    exact ⟨ inferInstance, by rw [ Module.finrank_zero_of_subsingleton ] ; exact Nat.zero_le _ ⟩;
  · -- Apply the exists_shear_leadingCoeff lemma to obtain such a c.
    obtain ⟨c, hc⟩ : ∃ c : K, coeff (Finsupp.single 0 g.totalDegree) (shear c g) ≠ 0 := by
      apply exists_shear_leadingCoeff g (by
      intro hg; simp_all +decide [ Ideal.span_insert ] ;
      exact hTop ( hco ( by simp +decide ) ( by simp +decide ) ));
    -- Let $b = \text{coeff}(\text{single}(0, g.\text{totalDegree}))(\text{shear}(c, g))$.
    set b := coeff (Finsupp.single 0 g.totalDegree) (shear c g) with hb_def
    have hb_ne_zero : b ≠ 0 := hc
    have hb_inv_ne_zero : b⁻¹ ≠ 0 := inv_ne_zero hb_ne_zero
    have hb_inv_mul_b : b⁻¹ * b = 1 := inv_mul_cancel₀ hb_ne_zero
    have hg'_mon : (E (MvPolynomial.C b⁻¹ * shear c g)).Monic := by
      apply (E_monic_of_top_coeff (shear c g) b hb_ne_zero (by
      rw [ shear_totalDegree ])).left
    have hg'_deg : (MvPolynomial.C b⁻¹ * shear c g).totalDegree ≤ (E (MvPolynomial.C b⁻¹ * shear c g)).natDegree := by
      have := E_monic_of_top_coeff ( shear c g ) b hb_ne_zero ( by
        rw [ shear_totalDegree ] ) ; aesop;
    have gg' : IsRelPrime (MvPolynomial.C b⁻¹ * shear c g) (shear c h) := by
      have h_trans : IsRelPrime (shear c g) (shear c h) := by
        intro d hdg hdh; have := hco ( show ( shear c ).symm d ∣ g from ?_ ) ( show ( shear c ).symm d ∣ h from ?_ ) ; aesop;
        · convert map_dvd ( shear c ).symm hdg using 1 ; aesop;
        · convert map_dvd ( shear c ).symm hdh using 1 ; aesop;
      convert isRelPrime_mul_unit_left_left ( show IsUnit ( MvPolynomial.C b⁻¹ ) from ?_ ) |>.2 h_trans using 1;
      exact isUnit_iff_exists_inv.mpr ⟨ MvPolynomial.C b, by rw [ ← MvPolynomial.C_mul, hb_inv_mul_b, MvPolynomial.C_1 ] ⟩
    have hbound : Module.finrank K (MvPolynomial (Fin 2) K ⧸ Ideal.span {MvPolynomial.C b⁻¹ * shear c g, shear c h}) ≤ (MvPolynomial.C b⁻¹ * shear c g).totalDegree * (shear c h).totalDegree := by
      exact bezout_monic_transport _ _ gg' hg'_mon hg'_deg |>.2
    have hfin : FiniteDimensional K (MvPolynomial (Fin 2) K ⧸ Ideal.span {MvPolynomial.C b⁻¹ * shear c g, shear c h}) := by
      exact bezout_monic_transport ( MvPolynomial.C b⁻¹ * shear c g ) ( shear c h ) gg' hg'_mon hg'_deg |>.1
    have hfin' : FiniteDimensional K (MvPolynomial (Fin 2) K ⧸ Ideal.span {shear c g, shear c h}) := by
      have hfin' : Ideal.span {MvPolynomial.C b⁻¹ * shear c g, shear c h} = Ideal.span {shear c g, shear c h} := by
        convert span_pair_C_mul_left b⁻¹ hb_inv_ne_zero ( shear c g ) ( shear c h ) using 1
      generalize_proofs at *; (
      exact hfin'.symm ▸ hfin)
    have hfin'' : FiniteDimensional K (MvPolynomial (Fin 2) K ⧸ Ideal.span {g, h}) := by
      have h_iso : (MvPolynomial (Fin 2) K ⧸ Ideal.span {g, h}) ≃ₐ[K] (MvPolynomial (Fin 2) K ⧸ Ideal.span {(shear c) g, (shear c) h}) := by
        convert quotSpanPairAlgEquiv ( shear c ) g h using 1;
      exact h_iso.symm.toLinearEquiv.finiteDimensional
    have hbound' : Module.finrank K (MvPolynomial (Fin 2) K ⧸ Ideal.span {g, h}) ≤ g.totalDegree * h.totalDegree := by
      have hbound'' : Module.finrank K (MvPolynomial (Fin 2) K ⧸ Ideal.span {MvPolynomial.C b⁻¹ * shear c g, shear c h}) = Module.finrank K (MvPolynomial (Fin 2) K ⧸ Ideal.span {shear c g, shear c h}) := by
        rw [ span_pair_C_mul_left b⁻¹ hb_inv_ne_zero ];
      have hbound''' : Module.finrank K (MvPolynomial (Fin 2) K ⧸ Ideal.span {shear c g, shear c h}) = Module.finrank K (MvPolynomial (Fin 2) K ⧸ Ideal.span {g, h}) := by
        exact ( quotSpanPairAlgEquiv ( shear c ) g h ).toLinearEquiv.finrank_eq.symm;
      have hbound'''' : (MvPolynomial.C b⁻¹ * shear c g).totalDegree ≤ g.totalDegree := by
        exact le_trans ( MvPolynomial.totalDegree_mul _ _ ) ( by simp +decide [ shear_totalDegree ] )
      have hbound''''' : (shear c h).totalDegree ≤ h.totalDegree := by
        exact le_of_eq ( shear_totalDegree c h )
      have hbound'''''' : (MvPolynomial.C b⁻¹ * shear c g).totalDegree * (shear c h).totalDegree ≤ g.totalDegree * h.totalDegree := by
        exact Nat.mul_le_mul hbound'''' hbound'''''
      linarith [hbound, hbound'', hbound''', hbound'''', hbound''''', hbound'''''']
    exact ⟨hfin'', hbound'⟩

/-- Inside a 0-dimensional ideal generated in total degree `≤ d` there are two
elements of total degree `≤ d` sharing no common factor. -/
theorem exists_coprime_pair [IsAlgClosed K] {ι : Type*} [Fintype ι]
    (f : ι → MvPolynomial (Fin 2) K) (d : ℕ)
    (hd : ∀ i, (f i).totalDegree ≤ d)
    [FiniteDimensional K (MvPolynomial (Fin 2) K ⧸ Ideal.span (Set.range f))] :
    ∃ g h : MvPolynomial (Fin 2) K,
      g ∈ Ideal.span (Set.range f) ∧ h ∈ Ideal.span (Set.range f) ∧
      IsRelPrime g h ∧ g.totalDegree ≤ d ∧ h.totalDegree ≤ d := by
  by_cases hTop : Ideal.span (Set.range f) = ⊤
  · refine ⟨1, 1, ?_, ?_, isRelPrime_one_left, ?_, ?_⟩
    · rw [hTop]; exact Submodule.mem_top
    · rw [hTop]; exact Submodule.mem_top
    · simp
    · simp
  · obtain ⟨i0, hi0⟩ := exists_nonzero_generator f
    have hdvd : ∀ π, Irreducible π → π ∣ f i0 → ∃ j, ¬ π ∣ f j := by
      intro π hπ hπg
      by_contra hall
      push_neg at hall
      have hsub : Ideal.span (Set.range f) ≤ Ideal.span {π} := by
        rw [Ideal.span_le]
        rintro x ⟨j, rfl⟩
        exact Ideal.mem_span_singleton.mpr (hall j)
      have : FiniteDimensional K (MvPolynomial (Fin 2) K ⧸ Ideal.span {π}) :=
        Module.Finite.of_surjective (Ideal.Quotient.factorₐ K hsub).toLinearMap
          (Ideal.Quotient.factor_surjective hsub)
      exact quotient_span_single_not_finiteDimensional π hπ.not_isUnit this
    obtain ⟨c, hc⟩ := avoid_factors (f i0) hi0 f hdvd
    refine ⟨f i0, ∑ j, C (c j) * f j, ?_, ?_, hc, hd i0, ?_⟩
    · exact Ideal.subset_span ⟨i0, rfl⟩
    · exact Ideal.sum_mem _ (fun j _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨j, rfl⟩))
    · refine (MvPolynomial.totalDegree_finset_sum _ _).trans ?_
      apply Finset.sup_le
      intro j _
      exact (MvPolynomial.totalDegree_mul _ _).trans (by simpa using hd j)

end AffineBezout
