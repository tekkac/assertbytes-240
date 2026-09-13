import Mathlib

/-!
# W3 — Grade descent (Rees exchange), Ext-free

Proves the Rees-exchange grade descent lemma for weakly regular sequences and
the explicit translated-coordinate regular sequence in polynomial rings. These
are the depth inputs used by `GenericSequence`.
-/

open RingTheory.Sequence
open scoped Pointwise

namespace GradeDescent

universe u v

/-! ## Prime avoidance helpers -/

/-
Pure prime avoidance: if a finite set `s` of primes is such that `a` is not
contained in any of them, then there is an element of `a` outside all of them.
-/
lemma exists_notMem_of_finite_primes {R : Type u} [CommRing R] (a : Ideal R)
    (s : Set (Ideal R)) (hs : s.Finite) (hp : ∀ P ∈ s, P.IsPrime)
    (hsub : ∀ P ∈ s, ¬ (a : Set R) ⊆ (P : Set R)) :
    ∃ z ∈ a, ∀ P ∈ s, z ∉ P := by
  by_contra! h;
  have := Ideal.subset_union_prime_finite hs ( f := id ) ⊥ ⊥ ( fun i hi _ _ => hp i hi ) ( I := a ) ; simp_all +decide [ Set.subset_def ] ;
  obtain ⟨ P, hP₁, hP₂ ⟩ := this; obtain ⟨ x, hx₁, hx₂ ⟩ := hsub P hP₁; exact hx₂ ( hP₂ hx₁ ) ;

/-
If `z` avoids every associated prime of `M`, it is a nonzerodivisor on `M`.
-/
lemma isSMulRegular_of_notMem_associatedPrimes {R : Type u} [CommRing R]
    [IsNoetherianRing R] {M : Type v} [AddCommGroup M] [Module R M] {z : R}
    (h : ∀ P ∈ associatedPrimes R M, z ∉ P) : IsSMulRegular M z := by
  contrapose! h;
  -- By definition of associated primes, if $z$ is not a regular element on $M$, then $z$ is in the union of the associated primes of $M$.
  have h_union : z ∈ ⋃ P ∈ associatedPrimes R M, (P : Set R) := by
    rw [ biUnion_associatedPrimes_eq_compl_regular ];
    exact h;
  aesop

/-
If `a` contains an `M`-regular element, then `a` is not contained in any
associated prime of `M`.
-/
lemma not_subset_associatedPrime_of_isSMulRegular_mem {R : Type u} [CommRing R]
    [IsNoetherianRing R] {M : Type v} [AddCommGroup M] [Module R M]
    {a : Ideal R} {w : R} (hw : w ∈ a) (hreg : IsSMulRegular M w)
    {P : Ideal R} (hP : P ∈ associatedPrimes R M) : ¬ (a : Set R) ⊆ (P : Set R) := by
  intro h;
  contrapose! hreg; have := biUnion_associatedPrimes_eq_compl_regular ( R := R ) ( M := M ) ; simp_all +decide [ Set.subset_def ] ;
  exact this.subset <| Set.mem_iUnion₂.mpr ⟨ P, hP, h _ hw ⟩

/-! ## Length-2 exchange -/

/-
**Length-2 exchange.** If `x` is `M`-regular and `z` is regular on `M ⧸ x M`,
then `x` is regular on `M ⧸ z M`.
-/
lemma isSMulRegular_quotSMulTop_exchange {R : Type u} [CommRing R]
    {M : Type v} [AddCommGroup M] [Module R M] {x z : R}
    (hx : IsSMulRegular M x)
    (hzx : IsSMulRegular (QuotSMulTop x M) z) :
    IsSMulRegular (QuotSMulTop z M) x := by
  intro a b;
  obtain ⟨ a, rfl ⟩ := Quotient.mk''_surjective a; obtain ⟨ b, rfl ⟩ := Quotient.mk''_surjective b; simp_all +decide [ QuotSMulTop ] ;
  erw [ Submodule.Quotient.eq, Submodule.Quotient.eq ] at * ; simp_all +decide [ Submodule.mem_smul_pointwise_iff_exists ];
  intro c hc; have := hzx; simp_all +decide [ ← smul_sub ] ;
  have := @this ( Submodule.Quotient.mk c ) 0 ; simp_all +decide [ Submodule.Quotient.mk_eq_zero ] ;
  erw [ Submodule.Quotient.mk_eq_zero ] at this ; simp_all +decide [ Submodule.mem_smul_pointwise_iff_exists ] ;
  obtain ⟨ d, rfl ⟩ := this; simp_all +decide [ ← smul_assoc ] ;
  exact ⟨ d, hx <| by simpa [ mul_comm, smul_smul ] using hc ⟩

/-! ## Swap of iterated quotients -/

/-
The two iterated quotients `M ⧸ aM ⧸ bM` and `M ⧸ bM ⧸ aM` carry the same
weakly regular sequences.
-/
lemma isWeaklyRegular_quotSMulTop_comm {R : Type u} [CommRing R]
    {M : Type v} [AddCommGroup M] [Module R M] (a b : R) (ws : List R) :
    IsWeaklyRegular (QuotSMulTop a (QuotSMulTop b M)) ws ↔
      IsWeaklyRegular (QuotSMulTop b (QuotSMulTop a M)) ws := by
  set P₁ : Submodule R M := Ideal.ofList [a, b] • ⊤
  set P₂ : Submodule R M := Ideal.ofList [b, a] • ⊤;
  have h_equiv : P₁ = P₂ := by
    simp +zetaDelta at *;
    rw [ sup_comm ];
  convert ( Submodule.quotOfListConsSMulTopEquivQuotSMulTopOuter ( M ) a [ b ] ).symm.isWeaklyRegular_congr ws |> Iff.trans <| ( Submodule.quotEquivOfEq P₁ P₂ h_equiv ).isWeaklyRegular_congr ws |> Iff.trans <| ( Submodule.quotOfListConsSMulTopEquivQuotSMulTopOuter ( M ) b [ a ] ).isWeaklyRegular_congr ws using 1;
  · convert Iff.rfl;
    all_goals ext; simp +decide ;
    all_goals rw [ Submodule.ideal_span_singleton_smul ] ;
  · convert Iff.rfl;
    all_goals ext; simp +decide [ Submodule.ideal_span_singleton_smul ] ;

/-! ## Sub-lemma S (the switch) -/

/-
Pure-module core of sub-lemma S: if `m` witnesses an associated prime of
`M ⧸ x M` (i.e. `m ∉ x M` but `a • m ⊆ x M`), then the classical Kaplansky
switch produces a contradiction with `(y₁, y₂)` being weakly regular.
-/
lemma sublemma_S_core {R : Type u} [CommRing R]
    {M : Type v} [AddCommGroup M] [Module R M]
    {a : Ideal R} {x y₁ y₂ : R}
    (hxreg : IsSMulRegular M x) (hy1reg : IsSMulRegular M y₁)
    (hy2reg : IsSMulRegular (QuotSMulTop y₁ M) y₂)
    (hy1 : y₁ ∈ a) (hy2 : y₂ ∈ a)
    {m : M} (hm : m ∉ (x • ⊤ : Submodule R M))
    (hmem : ∀ α ∈ a, α • m ∈ (x • ⊤ : Submodule R M)) : False := by
  -- Step 1. Since `y₁ ∈ a`, `hmem y₁ hy1 : y₁ • m ∈ x • ⊤`, so there is `m₁` with `x • m₁ = y₁ • m`.
  obtain ⟨m₁, hm₁⟩ : ∃ m₁ : M, x • m₁ = y₁ • m := by
    obtain ⟨ m₁, hm₁ ⟩ := hmem y₁ hy1;
    exact ⟨ m₁, hm₁.2 ⟩;
  -- Step 2. Claim: for every `α ∈ a`, `α • m₁ ∈ y₁ • ⊤`. Given `α ∈ a`, `hmem α hα` gives `mα` with `x • mα = α • m`. Compute:
  have h_step2 : ∀ α ∈ a, α • m₁ ∈ y₁ • (⊤ : Submodule R M) := by
    intro α hα
    obtain ⟨mα, hmα⟩ : ∃ mα : M, x • mα = α • m := by
      obtain ⟨ mα, hmα ⟩ := hmem α hα;
      exact ⟨ mα, hmα.2 ⟩
    have h_eq : x • (α • m₁) = x • (y₁ • mα) := by
      simp +decide only [← smul_comm α x, hm₁, ← smul_comm y₁ x, hmα];
      rw [ SMulCommClass.smul_comm ]
    have h_eq' : α • m₁ = y₁ • mα := by
      exact hxreg h_eq
    exact h_eq'.symm ▸ Submodule.smul_mem_pointwise_smul mα y₁ ⊤ (by simp);
  -- Step 3. `m₁ ∉ y₁ • ⊤`: suppose `m₁ = y₁ • m'`. Then `y₁ • m = x • m₁ = x • (y₁ • m') = y₁ • (x • m')`, so `hy1reg` (injectivity of `y₁ • ·`) gives `m = x • m'`, i.e. `m ∈ x • ⊤`, contradicting `hm`.
  have h_step3 : m₁ ∉ y₁ • (⊤ : Submodule R M) := by
    contrapose! hm; simp_all +decide [ Submodule.mem_smul_pointwise_iff_exists ] ;
    obtain ⟨ b, rfl ⟩ := hm; use b; simp_all +decide [ smul_smul, mul_comm ] ;
    exact hy1reg ( by simpa [ mul_comm, smul_smul ] using hm₁ );
  -- Step 4. Consider the class `Submodule.Quotient.mk m₁ : QuotSMulTop y₁ M`. By Step 3 and `Submodule.Quotient.mk_eq_zero` it is nonzero. By Step 2 applied to `α = y₂` (`hy2 : y₂ ∈ a`), `y₂ • m₁ ∈ y₁ • ⊤`, so `y₂ • Submodule.Quotient.mk m₁ = Submodule.Quotient.mk (y₂ • m₁) = 0` (using `Submodule.Quotient.mk_smul` and `Submodule.Quotient.mk_eq_zero`).
  have h_step4 : y₂ • (Submodule.Quotient.mk m₁ : QuotSMulTop y₁ M) = 0 := by
    convert Submodule.Quotient.mk_eq_zero _ |>.2 ( h_step2 y₂ hy2 ) using 1;
  have := hy2reg;
  exact h_step3 ( by simpa [ Submodule.Quotient.mk_eq_zero ] using this ( show y₂ • Submodule.Quotient.mk m₁ = y₂ • 0 by simpa [ Submodule.Quotient.mk_eq_zero ] using h_step4 ) )

/-- **Sub-lemma S.** If `(y₁, y₂)` is weakly regular on `M`, `x, y₁, y₂ ∈ a`, and
`x` is `M`-regular, then `a` is contained in no associated prime of `M ⧸ x M`. -/
lemma sublemma_S {R : Type u} [CommRing R] [IsNoetherianRing R]
    {M : Type v} [AddCommGroup M] [Module R M]
    {a : Ideal R} {x y₁ y₂ : R}
    (hxreg : IsSMulRegular M x)
    (hy1 : y₁ ∈ a) (hy2 : y₂ ∈ a)
    (hwr : IsWeaklyRegular M [y₁, y₂]) :
    ∀ P ∈ associatedPrimes R (QuotSMulTop x M), ¬ (a : Set R) ⊆ (P : Set R) := by
  rw [isWeaklyRegular_cons_iff, isWeaklyRegular_singleton_iff] at hwr
  obtain ⟨hy1reg, hy2reg⟩ := hwr
  rintro P ⟨hPprime, n, hPcolon⟩ hsub
  -- lift the witness `n` of the associated prime to `m : M`
  obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ n
  have hn0 : (Submodule.Quotient.mk m : QuotSMulTop x M) ≠ 0 := by
    intro h0
    apply hPprime.ne_top
    rw [hPcolon]
    rw [h0]
    ext r
    simp [Submodule.mem_colon_singleton]
  have hm : m ∉ (x • ⊤ : Submodule R M) := by
    intro hmem
    exact hn0 ((Submodule.Quotient.mk_eq_zero _).mpr hmem)
  have hmem : ∀ α ∈ a, α • m ∈ (x • ⊤ : Submodule R M) := by
    intro α hα
    have h1 : α ∈ P := hsub hα
    rw [hPcolon, Submodule.mem_colon_singleton] at h1
    have h2 : (Submodule.Quotient.mk (α • m) : QuotSMulTop x M) = 0 := by
      rw [Submodule.Quotient.mk_smul]
      simpa using h1
    exact (Submodule.Quotient.mk_eq_zero _).mp h2
  exact sublemma_S_core hxreg hy1reg hy2reg hy1 hy2 hm hmem

/-! ## The grade descent induction -/

lemma grade_descent_aux :
    ∀ (t : ℕ) {S : Type u} [CommRing S] [IsNoetherianRing S]
      {M : Type v} [AddCommGroup M] [Module S M] [Module.Finite S M]
      (a : Ideal S) {x : S}, x ∈ a → IsSMulRegular M x →
      ∀ (rs : List S), rs.length = t → (∀ r ∈ rs, r ∈ a) → IsWeaklyRegular M rs →
      ∃ rs' : List S, rs'.length = t - 1 ∧ (∀ r ∈ rs', r ∈ a) ∧
        IsWeaklyRegular (QuotSMulTop x M) rs' := by
  intro t
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    intro S _ _ M _ _ _ a x hx hreg rs hlen hmem hwr
    rcases rs with _ | ⟨y₁, _ | ⟨y₂, rest⟩⟩
    · -- rs = []
      refine ⟨[], ?_, by simp, IsWeaklyRegular.nil _ _⟩
      simp only [List.length_nil] at hlen ⊢; omega
    · -- rs = [y₁]
      refine ⟨[], ?_, by simp, IsWeaklyRegular.nil _ _⟩
      simp only [List.length_nil, List.length_cons] at hlen ⊢; omega
    · -- rs = y₁ :: y₂ :: rest, length t ≥ 2
      simp only [List.length_cons] at hlen
      have hy1a : y₁ ∈ a := hmem y₁ (by simp)
      have hy2a : y₂ ∈ a := hmem y₂ (by simp)
      rw [isWeaklyRegular_cons_iff] at hwr
      obtain ⟨hy1reg, hwr'⟩ := hwr
      have hy2reg : IsSMulRegular (QuotSMulTop y₁ M) y₂ :=
        ((isWeaklyRegular_cons_iff _ _ _).mp hwr').1
      have hwr12 : IsWeaklyRegular M [y₁, y₂] :=
        IsWeaklyRegular.cons hy1reg ((isWeaklyRegular_singleton_iff _ _).mpr hy2reg)
      -- Choose z regular on M, M/xM, M/y₁M simultaneously.
      obtain ⟨z, hza, hznotmem⟩ := exists_notMem_of_finite_primes a
        (associatedPrimes S M ∪ associatedPrimes S (QuotSMulTop x M) ∪
          associatedPrimes S (QuotSMulTop y₁ M))
        (((associatedPrimes.finite S M).union
            (associatedPrimes.finite S (QuotSMulTop x M))).union
          (associatedPrimes.finite S (QuotSMulTop y₁ M)))
        (by
          rintro P ((hP | hP) | hP)
          · exact IsAssociatedPrime.isPrime hP
          · exact IsAssociatedPrime.isPrime hP
          · exact IsAssociatedPrime.isPrime hP)
        (by
          rintro P ((hP | hP) | hP)
          · exact not_subset_associatedPrime_of_isSMulRegular_mem hy1a hy1reg hP
          · exact sublemma_S hreg hy1a hy2a hwr12 P hP
          · exact not_subset_associatedPrime_of_isSMulRegular_mem hy2a hy2reg hP)
      have hzx : IsSMulRegular (QuotSMulTop x M) z :=
        isSMulRegular_of_notMem_associatedPrimes
          (fun P hP => hznotmem P (Or.inl (Or.inr hP)))
      have hzy1 : IsSMulRegular (QuotSMulTop y₁ M) z :=
        isSMulRegular_of_notMem_associatedPrimes
          (fun P hP => hznotmem P (Or.inr hP))
      -- Step 1: descent on M/y₁M along z, sequence (y₂ :: rest).
      have hlen1 : (y₂ :: rest).length = t - 1 := by
        simp only [List.length_cons]; omega
      have hmem1 : ∀ r ∈ (y₂ :: rest), r ∈ a :=
        fun r hr => hmem r (List.mem_cons_of_mem _ hr)
      obtain ⟨w, hwlen, hwmem, hwreg⟩ :=
        ih (t - 1) (by omega) (M := QuotSMulTop y₁ M) a hza hzy1
          (y₂ :: rest) hlen1 hmem1 hwr'
      -- (y₁ :: w) is weakly regular on M/zM.
      have hy1_zM : IsSMulRegular (QuotSMulTop z M) y₁ :=
        isSMulRegular_quotSMulTop_exchange hy1reg hzy1
      have hwr_y1w : IsWeaklyRegular (QuotSMulTop z M) (y₁ :: w) :=
        IsWeaklyRegular.cons hy1_zM
          ((isWeaklyRegular_quotSMulTop_comm z y₁ w).mp hwreg)
      -- x is regular on M/zM.
      have hx_zM : IsSMulRegular (QuotSMulTop z M) x :=
        isSMulRegular_quotSMulTop_exchange hreg hzx
      -- Step 4: descent on M/zM along x, sequence (y₁ :: w).
      have hlen2 : (y₁ :: w).length = t - 1 := by
        simp only [List.length_cons] at hwlen ⊢; omega
      have hmem2 : ∀ r ∈ (y₁ :: w), r ∈ a := by
        intro r hr
        rcases List.mem_cons.mp hr with rfl | hr
        · exact hy1a
        · exact hwmem r hr
      obtain ⟨w2, hw2len, hw2mem, hw2reg⟩ :=
        ih (t - 1) (by omega) (M := QuotSMulTop z M) a hx hx_zM
          (y₁ :: w) hlen2 hmem2 hwr_y1w
      -- Final: rs' = z :: w2.
      refine ⟨z :: w2, ?_, ?_, ?_⟩
      · simp only [List.length_cons] at hw2len ⊢; omega
      · intro r hr
        rcases List.mem_cons.mp hr with rfl | hr
        · exact hza
        · exact hw2mem r hr
      · exact IsWeaklyRegular.cons hzx
          ((isWeaklyRegular_quotSMulTop_comm x z w2).mp hw2reg)

/-! ## Transport lemma for `translated_coords` -/

open MvPolynomial

/-
General transport: if `R ⧸ (r)` is ring-isomorphic to `A`, then a list `L` of
elements of `R` is weakly regular on `QuotSMulTop r R` provided its image in `A`
(via the quotient map composed with the isomorphism) is weakly regular on `A`.
-/
lemma isWeaklyRegular_quotSMulTop_of_ringEquiv {R : Type u} {A : Type v}
    [CommRing R] [CommRing A] {r : R} (Φ : (R ⧸ Ideal.span {r}) ≃+* A)
    (L : List R)
    (hL : IsWeaklyRegular A
      (L.map (fun p => Φ (Ideal.Quotient.mk (Ideal.span {r}) p)))) :
    IsWeaklyRegular (QuotSMulTop r R) L := by
  convert hL using 1;
  have h_quot : (r • ⊤ : Submodule R R) = Ideal.span {r} := by
    ext; simp [Submodule.mem_smul_pointwise_iff_exists];
    simp +decide [ Ideal.mem_span_singleton', eq_comm ];
    simp +decide only [mul_comm];
  convert LinearEquiv.isWeaklyRegular_congr ( Submodule.quotEquivOfEq ( r • ⊤ : Submodule R R ) ( Ideal.span { r } ) h_quot ) L using 1;
  convert Iff.symm ( LinearEquiv.isWeaklyRegular_congr' ( Φ.toSemilinearEquiv ) ( L.map ( Ideal.Quotient.mk ( Ideal.span { r } ) ) ) ) using 1;
  · simp +decide;
    rfl;
  · convert Iff.symm ( isWeaklyRegular_map_algebraMap_iff ( R ⧸ Ideal.span { r } ) ( R ⧸ Ideal.span { r } ) L ) using 1

/-
`X i - C c` is a nonzerodivisor on the polynomial ring over a field.
-/
lemma isSMulRegular_X_sub_C {K : Type u} [Field K] {n : ℕ} (i : Fin n) (c : K) :
    IsSMulRegular (MvPolynomial (Fin n) K) (X i - C c) := by
  intro f g hfg;
  exact mul_left_cancel₀ ( show ( X i - C c ) ≠ 0 from sub_ne_zero.mpr <| ne_of_apply_ne ( MvPolynomial.eval <| fun _ => c + 1 ) <| by simp +decide ) hfg

/-- The ring isomorphism `K[x₀,…,xₙ] ⧸ (x₀ - a₀) ≃ K[x₁,…,xₙ]`, built from
`finSuccEquiv` and the `X - C` quotient of a univariate polynomial ring. -/
noncomputable def finSuccQuotEquiv {K : Type u} [Field K] {n : ℕ} (a : Fin (n + 1) → K) :
    (MvPolynomial (Fin (n + 1)) K ⧸ Ideal.span {X (0 : Fin (n + 1)) - C (a 0)}) ≃+*
      MvPolynomial (Fin n) K :=
  (Ideal.quotientEquivAlg (Ideal.span {X (0 : Fin (n + 1)) - C (a 0)})
      (Ideal.span {(Polynomial.X - Polynomial.C (C (a 0)) :
        Polynomial (MvPolynomial (Fin n) K))})
      (MvPolynomial.finSuccEquiv K n)
      (by
        rw [Ideal.map_span, Set.image_singleton]
        congr 1
        rw [show (↑(MvPolynomial.finSuccEquiv K n) :
                MvPolynomial (Fin (n + 1)) K →+* _)
              (X (0 : Fin (n + 1)) - C (a 0))
            = (MvPolynomial.finSuccEquiv K n) (X (0 : Fin (n + 1)) - C (a 0)) from rfl]
        rw [map_sub, finSuccEquiv_X_zero]
        congr 1
        simp [MvPolynomial.finSuccEquiv_apply,
          MvPolynomial.eval₂Hom_C])).toRingEquiv.trans
    (Polynomial.quotientSpanXSubCAlgEquiv (C (a 0))).toRingEquiv

lemma finSuccQuotEquiv_mk_X_succ_sub_C {K : Type u} [Field K] {n : ℕ}
    (a : Fin (n + 1) → K) (j : Fin n) :
    finSuccQuotEquiv a
        (Ideal.Quotient.mk _ (X j.succ - C (a j.succ))) = X j - C (a j.succ) := by
  simp only [finSuccQuotEquiv, RingEquiv.trans_apply, AlgEquiv.toRingEquiv_eq_coe,
    AlgEquiv.coe_ringEquiv, Ideal.quotientEquivAlg_mk,
    Polynomial.quotientSpanXSubCAlgEquiv_mk]
  rw [map_sub]
  simp [MvPolynomial.finSuccEquiv_apply, MvPolynomial.eval₂Hom_C]

/-- The inductive step for `translated_coords`, packaged via `finSuccEquiv`. -/
lemma isWeaklyRegular_quotSMulTop_finSucc {K : Type u} [Field K] {n : ℕ}
    (a : Fin (n + 1) → K)
    (hIH : IsWeaklyRegular (MvPolynomial (Fin n) K)
      ((List.finRange n).map (fun i => X i - C (a i.succ)))) :
    IsWeaklyRegular (QuotSMulTop (X (0 : Fin (n + 1)) - C (a 0))
        (MvPolynomial (Fin (n + 1)) K))
      ((List.finRange n).map
        (fun i => (X i.succ - C (a i.succ) : MvPolynomial (Fin (n + 1)) K))) := by
  apply isWeaklyRegular_quotSMulTop_of_ringEquiv (finSuccQuotEquiv a)
  have hmap : ((List.finRange n).map
        (fun i => (X i.succ - C (a i.succ) : MvPolynomial (Fin (n + 1)) K))).map
        (fun p => finSuccQuotEquiv a (Ideal.Quotient.mk (Ideal.span _) p))
      = (List.finRange n).map (fun i => X i - C (a i.succ)) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro i _
    exact finSuccQuotEquiv_mk_X_succ_sub_C a i
  rw [hmap]
  exact hIH

lemma translated_coords_aux {K : Type u} [Field K] :
    ∀ (n : ℕ) (a : Fin n → K), IsWeaklyRegular (MvPolynomial (Fin n) K)
      ((List.finRange n).map (fun i => X i - C (a i))) := by
  intro n
  induction n with
  | zero => intro a; simp [IsWeaklyRegular.nil]
  | succ n ih =>
    intro a
    rw [List.finRange_succ, List.map_cons, List.map_map]
    rw [isWeaklyRegular_cons_iff]
    refine ⟨isSMulRegular_X_sub_C 0 (a 0), ?_⟩
    have hstep := isWeaklyRegular_quotSMulTop_finSucc a (ih (fun i => a i.succ))
    convert hstep using 2

end GradeDescent

/-- **W3a (grade descent).** If the ideal `a` contains a weakly regular sequence
of length `t` on the finitely generated module `M` over the Noetherian ring `S`,
and `x ∈ a` is a nonzerodivisor on `M`, then `a` contains a weakly regular
sequence of length `t - 1` on `M ⧸ x • M`. -/
theorem grade_descent
    {S : Type*} [CommRing S] [IsNoetherianRing S]
    {M : Type*} [AddCommGroup M] [Module S M] [Module.Finite S M]
    (a : Ideal S) {x : S} (hx : x ∈ a) (hreg : IsSMulRegular M x)
    (rs : List S) (hmem : ∀ r ∈ rs, r ∈ a) (hwreg : IsWeaklyRegular M rs) :
    ∃ rs' : List S, rs'.length = rs.length - 1 ∧ (∀ r ∈ rs', r ∈ a) ∧
      IsWeaklyRegular (QuotSMulTop x M) rs' :=
  GradeDescent.grade_descent_aux rs.length a hx hreg rs rfl hmem hwreg

/-- **W3b (explicit depth witness).** The translated coordinate sequence is
weakly regular on the polynomial ring. -/
theorem translated_coords_isWeaklyRegular
    {K : Type*} [Field K] {n : ℕ} (a : Fin n → K) :
    IsWeaklyRegular (MvPolynomial (Fin n) K)
      ((List.finRange n).map
        (fun i => MvPolynomial.X i - MvPolynomial.C (a i))) :=
  GradeDescent.translated_coords_aux n a
