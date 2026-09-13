import AssertBytes240.Algebra.ParamSystem
import AssertBytes240.Algebra.HilbertFunction

/-!
# The dimension formula for polynomial rings over a field

Proves the polynomial-ring height/dimension identity
`height p + dim (K[x] ⧸ p) = n` for prime ideals. This is the catenary
dimension formula used by the affine-height and divided-degree arguments.
-/

noncomputable section

open MvPolynomial Order

namespace AristotleDimensionFormula

/-- The Krull dimension of `R ⧸ p` for a prime `p` equals the coheight of `p` in the
prime spectrum of `R`. -/
theorem ringKrullDim_quotient_eq_coheight {R : Type*} [CommRing R] (p : Ideal R) [hp : p.IsPrime] :
    ringKrullDim (R ⧸ p) = ((Order.coheight (⟨p, hp⟩ : PrimeSpectrum R) : ℕ∞) : WithBot ℕ∞) := by
  rw [ringKrullDim_quotient, Order.coheight_eq_krullDim_Ici]
  have hset : PrimeSpectrum.zeroLocus (p : Set R) = Set.Ici (⟨p, hp⟩ : PrimeSpectrum R) := by
    ext q; rw [PrimeSpectrum.mem_zeroLocus, Set.mem_Ici]; exact Iff.rfl
  exact Order.krullDim_eq_of_orderIso (OrderIso.setCongr _ _ hset)

/-- `dim K[x₀,…,xₙ₋₁] = n`. -/
theorem mvPoly_ringKrullDim {K : Type*} [Field K] (n : ℕ) :
    ringKrullDim (MvPolynomial (Fin n) K) = (n : WithBot ℕ∞) := by
  rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field K]; simp

/-- **Easy inequality.** `height p + dim (R ⧸ p) ≤ n`. This is the order-theoretic
`height x + coheight x ≤ krullDim` fact, valid in complete generality. -/
theorem height_add_ringKrullDim_quotient_le {K : Type*} [Field K] {n : ℕ}
    (p : Ideal (MvPolynomial (Fin n) K)) [hp : p.IsPrime] :
    (p.height : WithBot ℕ∞) + ringKrullDim (MvPolynomial (Fin n) K ⧸ p) ≤ (n : WithBot ℕ∞) := by
  rw [Ideal.height_eq_primeHeight, Ideal.primeHeight, ringKrullDim_quotient_eq_coheight,
    ← mvPoly_ringKrullDim (K := K) n]
  set x : PrimeSpectrum (MvPolynomial (Fin n) K) := ⟨p, hp⟩
  have hne : Nonempty (PrimeSpectrum (MvPolynomial (Fin n) K)) := ⟨x⟩
  rw [ringKrullDim, Order.krullDim_eq_iSup_height_add_coheight_of_nonempty, ← WithBot.coe_add]
  exact_mod_cast le_iSup (fun a => Order.height a + Order.coheight a) x

/-- For an integral ring hom `f : A →+* B`, `dim B ≤ dim A` (incomparability). -/
theorem ringKrullDim_comap_le_of_isIntegral {A B : Type*} [CommRing A] [CommRing B]
    (f : A →+* B) (hint : f.IsIntegral) :
    ringKrullDim B ≤ ringKrullDim A := by
  letI := f.toAlgebra
  haveI : Algebra.IsIntegral A B := by
    rw [Algebra.isIntegral_def]; intro x; exact hint x
  have hmono : StrictMono (PrimeSpectrum.comap f) := by
    intro Q Q' hQQ'
    have hlt : Q.asIdeal < Q'.asIdeal := hQQ'
    obtain ⟨x, hxQ', hxQ⟩ := SetLike.exists_of_lt hlt
    haveI := Q.isPrime
    have h := Ideal.comap_lt_comap_of_integral_mem_sdiff (R := A) (I := Q.asIdeal) (J := Q'.asIdeal)
      hlt.le (x := x) ⟨hxQ', hxQ⟩ (Algebra.IsIntegral.isIntegral x)
    show (PrimeSpectrum.comap f Q) < (PrimeSpectrum.comap f Q')
    rw [← PrimeSpectrum.asIdeal_lt_asIdeal]
    exact h
  exact Order.krullDim_le_of_strictMono _ hmono

/-- For an injective integral ring hom `f : A →+* B`, `dim A ≤ dim B` (going up). -/
theorem ringKrullDim_le_of_isIntegral_of_injective {A B : Type*} [CommRing A] [CommRing B]
    (f : A →+* B) (hf : Function.Injective f) (hint : f.IsIntegral) :
    ringKrullDim A ≤ ringKrullDim B := by
  letI := f.toAlgebra
  haveI : Algebra.IsIntegral A B := by rw [Algebra.isIntegral_def]; intro x; exact hint x
  have hker : RingHom.ker (algebraMap A B) = ⊥ := (RingHom.injective_iff_ker_eq_bot _).mp hf
  have lift_one : ∀ q : PrimeSpectrum A, ∃ Q : PrimeSpectrum B, Q.asIdeal.comap f = q.asIdeal := by
    intro q
    haveI := q.isPrime
    obtain ⟨Q, -, hQp, hQc⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (S := B) q.asIdeal ⊥
      (by rw [← RingHom.ker_eq_comap_bot]; exact hker.le.trans bot_le)
    exact ⟨⟨Q, hQp⟩, hQc⟩
  have lift_step : ∀ (Q : PrimeSpectrum B) (p : PrimeSpectrum A),
      Q.asIdeal.comap f < p.asIdeal →
        ∃ Q' : PrimeSpectrum B, Q < Q' ∧ Q'.asIdeal.comap f = p.asIdeal := by
    intro Q p hlt
    haveI := Q.isPrime
    haveI := p.isPrime
    obtain ⟨Q', hQQ', hQ'p, hQ'c⟩ := Ideal.exists_ideal_over_prime_of_isIntegral_of_isPrime
      (S := B) p.asIdeal Q.asIdeal hlt.le
    refine ⟨⟨Q', hQ'p⟩, ?_, hQ'c⟩
    rw [← PrimeSpectrum.asIdeal_lt_asIdeal]
    refine lt_of_le_of_ne hQQ' (fun h => (ne_of_lt hlt) ?_)
    show Q.asIdeal.comap f = p.asIdeal
    rw [h]; exact hQ'c
  have main : ∀ (l : LTSeries (PrimeSpectrum A)),
      ∃ L : LTSeries (PrimeSpectrum B),
        L.length = l.length ∧ L.last.asIdeal.comap f = l.last.asIdeal := by
    intro l
    induction l using RelSeries.inductionOn' with
    | singleton q =>
      obtain ⟨Q, hQ⟩ := lift_one q
      exact ⟨RelSeries.singleton _ Q, rfl, by simpa using hQ⟩
    | snoc l q hq ih =>
      obtain ⟨L, hlen, hlast⟩ := ih
      have hlt : L.last.asIdeal.comap f < q.asIdeal := by rw [hlast]; exact hq
      obtain ⟨Q', hQQ', hQ'c⟩ := lift_step L.last q hlt
      refine ⟨L.snoc Q' hQQ', ?_, ?_⟩
      · rw [RelSeries.snoc_length, RelSeries.snoc_length, hlen]
      · rw [RelSeries.last_snoc, RelSeries.last_snoc]; exact hQ'c
  rw [ringKrullDim, ringKrullDim, Order.krullDim, Order.krullDim]
  apply iSup_le
  intro l
  obtain ⟨L, hlen, -⟩ := main l
  rw [← hlen]
  exact le_iSup (fun L : LTSeries (PrimeSpectrum B) => (L.length : WithBot ℕ∞)) L

/-- **Integral extensions preserve Krull dimension.** If `f : A →+* B` is an injective
integral ring homomorphism between commutative rings, then `dim A = dim B`. -/
theorem ringKrullDim_eq_of_ringHom_isIntegral {A B : Type*} [CommRing A] [CommRing B]
    (f : A →+* B) (hf : Function.Injective f) (hint : f.IsIntegral) :
    ringKrullDim A = ringKrullDim B :=
  le_antisymm (ringKrullDim_le_of_isIntegral_of_injective f hf hint)
    (ringKrullDim_comap_le_of_isIntegral f hint)

/-! ### Localization and the fibre lower bound (ingredients for the hard direction) -/

/-- Localizing at one element cannot increase the Krull dimension. -/
theorem ringKrullDim_localizationAway_le {D : Type*} [CommRing D] (c : D) :
    ringKrullDim (Localization.Away c) ≤ ringKrullDim D := by
  apply Order.krullDim_le_of_strictMono (PrimeSpectrum.comap (algebraMap D (Localization.Away c)))
  intro a b h
  have hinj := PrimeSpectrum.localization_comap_injective (Localization.Away c) (Submonoid.powers c)
  have hmono : PrimeSpectrum.comap (algebraMap D (Localization.Away c)) a
      ≤ PrimeSpectrum.comap (algebraMap D (Localization.Away c)) b := by
    rw [← PrimeSpectrum.asIdeal_le_asIdeal]
    exact Ideal.comap_mono h.le
  exact lt_of_le_of_ne hmono (fun he => absurd (hinj he) h.ne)

/-- **Localization at a nonzero element preserves dimension of an affine domain.**
Because an affine domain is Jacobson and equidimensional, a maximal ideal `M` avoiding `c`
has height `= dim D`, and the whole chain below `M` avoids `c`, hence survives in `D[1/c]`. -/
theorem le_ringKrullDim_localizationAway
    {K : Type*} [Field K] {D : Type*} [CommRing D] [IsDomain D] [Algebra K D]
    [Algebra.FiniteType K D] {c : D} (hc : c ≠ 0) :
    ringKrullDim D ≤ ringKrullDim (Localization.Away c) := by
  haveI : IsJacobsonRing D := isJacobsonRing_of_finiteType (A := K) (B := D)
  obtain ⟨s, g, hginj, hgint⟩ := exists_integral_inj_algHom_of_fg K D
  have hdimlt : ringKrullDim D < ⊤ := by
    have hle : ringKrullDim D ≤ ringKrullDim (MvPolynomial (Fin s) K) :=
      ringKrullDim_le_of_isIntegral g.toRingHom hgint
    have heq : ringKrullDim (MvPolynomial (Fin s) K) = (s : WithBot ℕ∞) := by
      rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field K]; simp
    rw [heq] at hle
    exact lt_of_le_of_lt hle (compareOfLessAndEq_eq_lt.mp rfl)
  obtain ⟨M, hMmax, hcM⟩ : ∃ M : Ideal D, M.IsMaximal ∧ c ∉ M := by
    by_contra h
    push_neg at h
    have hcj : c ∈ (⊥ : Ideal D).jacobson := Ideal.mem_sInf.mpr (fun M hM => h M hM.2)
    have hbotrad : (⊥ : Ideal D).IsRadical := Ideal.isRadical_bot_of_noZeroDivisors
    rw [IsJacobsonRing.out' ⊥ hbotrad] at hcj
    exact hc (by simpa using hcj)
  haveI : M.IsPrime := hMmax.isPrime
  have hMheight : (M.height : WithBot ℕ∞) = ringKrullDim D := by
    refine le_antisymm ?_ (ringKrullDim_le_height_of_isMaximal_of_finiteType (K := K) M)
    exact Ideal.height_le_ringKrullDim_of_ne_top hMmax.ne_top
  haveI : M.FiniteHeight := by
    rw [Ideal.finiteHeight_iff]
    refine Or.inr (fun htop => ?_)
    rw [htop] at hMheight
    rw [← hMheight] at hdimlt
    simp at hdimlt
  obtain ⟨l, hllast, hllen⟩ := Ideal.exists_ltSeries_length_eq_height M
  have havoid : ∀ i, c ∉ (l i).asIdeal := by
    intro i hci
    have hle : l i ≤ l.last := l.monotone (Fin.le_last i)
    rw [hllast] at hle
    exact hcM (hle hci)
  set e := IsLocalization.orderIsoOfPrime (Submonoid.powers c) (Localization.Away c)
  have hdisj : ∀ i, Disjoint (↑(Submonoid.powers c)) (↑(l i).asIdeal : Set D) := by
    intro i
    rw [Set.disjoint_left]
    rintro x ⟨k, rfl⟩ hx
    exact havoid i ((l i).isPrime.mem_of_pow_mem k hx)
  let f : Fin (l.length + 1) → PrimeSpectrum (Localization.Away c) := fun i =>
    ⟨(e.symm ⟨(l i).asIdeal, ⟨(l i).isPrime, hdisj i⟩⟩ :
        {p : Ideal (Localization.Away c) // p.IsPrime}),
      (e.symm ⟨(l i).asIdeal, ⟨(l i).isPrime, hdisj i⟩⟩).2⟩
  have hfmono : StrictMono f := by
    intro i j hij
    have hlt : (l i).asIdeal < (l j).asIdeal := l.strictMono hij
    show (f i).asIdeal < (f j).asIdeal
    exact e.symm.strictMono (a := ⟨(l i).asIdeal, ⟨(l i).isPrime, hdisj i⟩⟩)
      (b := ⟨(l j).asIdeal, ⟨(l j).isPrime, hdisj j⟩⟩) hlt
  let L : LTSeries (PrimeSpectrum (Localization.Away c)) :=
    { length := l.length, toFun := f, step := fun i => hfmono (by simp) }
  calc ringKrullDim D = (M.height : WithBot ℕ∞) := hMheight.symm
    _ = (l.length : WithBot ℕ∞) := by rw [← hllen]; norm_cast
    _ = (L.length : WithBot ℕ∞) := rfl
    _ ≤ ringKrullDim (Localization.Away c) := Order.LTSeries.length_le_krullDim L

/-
**Fibre lower bound.** For an affine domain `D` and a nonzero prime `P` of `D[X]`
with zero contraction to `D`, the quotient `D[X]/P` has dimension at least `dim D`.
(The image of `X` is integral over `D[1/c]` where `c` is a leading coefficient in `P`.)
-/
theorem le_ringKrullDim_polyQuot_of_comap_C_bot
    {K : Type*} [Field K] {D : Type*} [CommRing D] [IsDomain D] [Algebra K D]
    [Algebra.FiniteType K D] {P : Ideal (Polynomial D)} [P.IsPrime] (hPbot : P ≠ ⊥)
    (hcomap : P.comap (Polynomial.C) = ⊥) :
    ringKrullDim D ≤ ringKrullDim (Polynomial D ⧸ P) := by
  -- Let `f ∈ P`, `f ≠ 0`.
  obtain ⟨f, hfP, hf0⟩ : ∃ f ∈ P, f ≠ 0 :=
    Submodule.exists_mem_ne_zero_of_ne_bot hPbot
  set P' := P.comap Polynomial.C
  have hP' : P' = ⊥ := by
    exact hcomap
  have hlc : (Polynomial.map (Ideal.Quotient.mk P') f).leadingCoeff ≠ 0 := by
    simp_all +decide [ Polynomial.ext_iff ];
    simp_all +decide [ Ideal.Quotient.eq_zero_iff_mem ];
  set lc := (Polynomial.map (Ideal.Quotient.mk P') f).leadingCoeff
  set Rₘ := Localization.Away lc
  set φ : D ⧸ P' →+* Polynomial D ⧸ P := Ideal.quotientMap P Polynomial.C le_rfl
  set Sₘ := Localization.Away (φ lc);
  have hφint : (IsLocalization.map Sₘ φ (Submonoid.powers lc).le_comap_map : Rₘ →+* Sₘ).IsIntegral := by
    apply Polynomial.isIntegral_isLocalization_polynomial_quotient P f hfP;
  have hφinj : Function.Injective φ := by
    convert Ideal.quotientMap_injective' _;
    exact le_rfl;
  have hRₘinj : Function.Injective (IsLocalization.map Sₘ φ (Submonoid.powers lc).le_comap_map : Rₘ →+* Sₘ) := by
    convert IsLocalization.map_injective_of_injective _ _ _ _;
    exact hφinj;
  have hRₘdim : ringKrullDim D ≤ ringKrullDim Rₘ := by
    convert le_ringKrullDim_localizationAway ( K := K ) ( D := D ⧸ P' ) ( c := lc ) hlc using 1;
    rw [ hP' ];
    exact ringKrullDim_eq_of_ringEquiv ( RingEquiv.quotientBot D ) |> Eq.symm;
  refine' le_trans hRₘdim ( le_trans _ ( ringKrullDim_localizationAway_le _ ) );
  convert ringKrullDim_le_of_isIntegral_of_injective _ hRₘinj hφint

/-- **Fibre formula (≥ half).** For an affine domain `D` and a prime `P` of `D[X]` with zero
contraction to `D`, `dim D + 1 ≤ height P + dim (D[X]/P)`. -/
theorem le_ht_add_dim_polyQuot
    {K : Type*} [Field K] {D : Type*} [CommRing D] [IsDomain D] [Algebra K D]
    [Algebra.FiniteType K D] (P : Ideal (Polynomial D)) [P.IsPrime]
    (hcomap : P.comap (Polynomial.C) = ⊥) :
    ringKrullDim D + 1 ≤ (P.height : WithBot ℕ∞) + ringKrullDim (Polynomial D ⧸ P) := by
  haveI : IsNoetherianRing D := (‹Algebra.FiniteType K D›).isNoetherianRing
  by_cases hP : P = ⊥
  · subst hP
    rw [Ideal.height_bot]
    have hquot : ringKrullDim (Polynomial D ⧸ (⊥ : Ideal (Polynomial D)))
        = ringKrullDim (Polynomial D) := ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot _)
    rw [hquot, Polynomial.ringKrullDim_of_isNoetherianRing]
    simp
  · have hht : (1 : ℕ∞) ≤ P.height := by
      rw [Ideal.height_eq_primeHeight]
      have hlt : (⊥ : Ideal (Polynomial D)) < P := bot_lt_iff_ne_bot.mpr hP
      have h1 := Order.height_add_one_le
        (a := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (Polynomial D)))
        (b := (⟨P, ‹_›⟩ : PrimeSpectrum (Polynomial D))) hlt
      calc (1 : ℕ∞) ≤ Order.height (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (Polynomial D)) + 1 :=
            le_add_self
        _ ≤ _ := h1
    have hdim : ringKrullDim D ≤ ringKrullDim (Polynomial D ⧸ P) :=
      le_ringKrullDim_polyQuot_of_comap_C_bot (K := K) (P := P) hP hcomap
    calc ringKrullDim D + 1
          ≤ ringKrullDim (Polynomial D ⧸ P) + (P.height : WithBot ℕ∞) := by
          apply add_le_add hdim; exact_mod_cast hht
      _ = (P.height : WithBot ℕ∞) + ringKrullDim (Polynomial D ⧸ P) := add_comm _ _

set_option maxHeartbeats 800000 in
/-- **Hard inequality.** `n ≤ height p + dim (R ⧸ p)`. Proved by induction on `n` via
`R = R'[X]` (flat going-down height split) together with the fibre formula
`le_ht_add_dim_polyQuot`. -/
theorem le_height_add_ringKrullDim_quotient {K : Type*} [Field K] {n : ℕ}
    (p : Ideal (MvPolynomial (Fin n) K)) [hp : p.IsPrime] :
    (n : WithBot ℕ∞) ≤ (p.height : WithBot ℕ∞) + ringKrullDim (MvPolynomial (Fin n) K ⧸ p) := by
  suffices H : ∀ (m : ℕ) (P : Ideal (MvPolynomial (Fin m) K)) [P.IsPrime],
      (m : WithBot ℕ∞) ≤ (P.height : WithBot ℕ∞) + ringKrullDim (MvPolynomial (Fin m) K ⧸ P) by
    exact H n p
  intro m
  induction m with
  | zero =>
    intro P hP
    haveI : Nontrivial (MvPolynomial (Fin 0) K ⧸ P) := Ideal.Quotient.nontrivial_iff.mpr hP.ne_top
    have h1 : (0 : WithBot ℕ∞) ≤ (P.height : WithBot ℕ∞) := by exact_mod_cast (zero_le P.height)
    have h2 : (0 : WithBot ℕ∞) ≤ ringKrullDim (MvPolynomial (Fin 0) K ⧸ P) :=
      ringKrullDim_nonneg_of_nontrivial
    calc ((0 : ℕ) : WithBot ℕ∞) = 0 + 0 := by simp
      _ ≤ _ := add_le_add h1 h2
  | succ m ih =>
    intro P hP
    set R' := MvPolynomial (Fin m) K with hR'
    set e : MvPolynomial (Fin (m + 1)) K ≃+* Polynomial R' :=
      (MvPolynomial.finSuccEquiv K m).toRingEquiv with he
    set Q : Ideal (Polynomial R') := P.map e with hQ
    haveI hQp : Q.IsPrime := Ideal.map_isPrime_of_equiv e
    have hht : P.height = Q.height := (RingEquiv.height_map e P).symm
    have hdim : ringKrullDim (MvPolynomial (Fin (m+1)) K ⧸ P) = ringKrullDim (Polynomial R' ⧸ Q) :=
      ringKrullDim_eq_of_ringEquiv (Ideal.quotientEquiv P Q e rfl)
    rw [hht, hdim]
    set q : Ideal R' := Q.comap (Polynomial.C) with hqdef
    haveI hqp : q.IsPrime := hqdef ▸ Ideal.comap_isPrime _ _
    haveI hlo : Q.LiesOver q := ⟨rfl⟩
    haveI : IsNoetherianRing R' := by infer_instance
    have hsplit := Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown q Q
    set qC : Ideal (Polynomial R') := q.map (Polynomial.C) with hqC
    have hqCleQ : qC ≤ Q := by rw [hqC, Ideal.map_le_iff_le_comap]
    haveI hkerle : RingHom.ker (Ideal.Quotient.mk qC) ≤ Q := by rw [Ideal.mk_ker]; exact hqCleQ
    set Pbar : Ideal (Polynomial R' ⧸ qC) := Q.map (Ideal.Quotient.mk qC) with hPbar
    haveI hPbarp : Pbar.IsPrime :=
      Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective hkerle
    rw [Polynomial.algebraMap_eq, ← hqC, ← hPbar] at hsplit
    haveI : IsDomain (R' ⧸ q) := Ideal.Quotient.isDomain q
    set E := q.polynomialQuotientEquivQuotientPolynomial with hE
    set Ptil : Ideal (Polynomial (R' ⧸ q)) := Pbar.map E.symm with hPtil
    haveI hPtilp : Ptil.IsPrime := Ideal.map_isPrime_of_equiv E.symm
    have ha : Ptil.height = Pbar.height := (RingEquiv.height_map E.symm Pbar)
    have hc : ringKrullDim (Polynomial (R' ⧸ q) ⧸ Ptil) = ringKrullDim (Polynomial R' ⧸ Q) := by
      have h1 : ringKrullDim ((Polynomial R' ⧸ qC) ⧸ Pbar) = ringKrullDim (Polynomial R' ⧸ Q) :=
        ringKrullDim_quotQuot_eq qC Q hqCleQ
      have h2 : ringKrullDim ((Polynomial R' ⧸ qC) ⧸ Pbar)
          = ringKrullDim (Polynomial (R' ⧸ q) ⧸ Ptil) :=
        ringKrullDim_eq_of_ringEquiv (Ideal.quotientEquiv Pbar Ptil E.symm rfl)
      rw [← h2, h1]
    have hb : Ptil.comap (Polynomial.C) = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      rw [Ideal.mem_comap, hPtil, Ideal.map_symm, Ideal.mem_comap] at hx
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
      have hEval : E (Polynomial.C ((Ideal.Quotient.mk q) r))
          = Ideal.Quotient.mk qC (Polynomial.C r) := by
        have h := q.polynomialQuotientEquivQuotientPolynomial_map_mk (Polynomial.C r)
        rw [Polynomial.map_C] at h
        rw [hE]; exact h
      rw [hEval, hPbar, Ideal.mem_quotient_iff_mem hqCleQ] at hx
      have hrq : r ∈ q := by rw [hqdef, Ideal.mem_comap]; exact hx
      rw [Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem]
      exact hrq
    have hfib : ringKrullDim (R' ⧸ q) + 1 ≤ (Ptil.height : WithBot ℕ∞)
        + ringKrullDim (Polynomial (R' ⧸ q) ⧸ Ptil) :=
      le_ht_add_dim_polyQuot (K := K) Ptil hb
    have hIH : (m : WithBot ℕ∞) ≤ (q.height : WithBot ℕ∞) + ringKrullDim (R' ⧸ q) := ih q
    rw [← hc, hsplit, ← ha]
    push_cast
    calc ((m : WithBot ℕ∞) + 1)
        ≤ ((q.height : WithBot ℕ∞) + ringKrullDim (R' ⧸ q)) + 1 := by gcongr
      _ = (q.height : WithBot ℕ∞) + (ringKrullDim (R' ⧸ q) + 1) := by ring
      _ ≤ (q.height : WithBot ℕ∞) + ((Ptil.height : WithBot ℕ∞)
            + ringKrullDim (Polynomial (R' ⧸ q) ⧸ Ptil)) := by gcongr
      _ = (q.height : WithBot ℕ∞) + (Ptil.height : WithBot ℕ∞)
            + ringKrullDim (Polynomial (R' ⧸ q) ⧸ Ptil) := by ring

/-- **The dimension formula for polynomial rings over a field.**
`height p + dim (K[x₀,…,xₙ₋₁] ⧸ p) = n`. -/
theorem height_add_ringKrullDim_quotient {K : Type*} [Field K] {n : ℕ}
    (p : Ideal (MvPolynomial (Fin n) K)) [hp : p.IsPrime] :
    (p.height : WithBot ℕ∞) + ringKrullDim (MvPolynomial (Fin n) K ⧸ p) = (n : WithBot ℕ∞) :=
  le_antisymm (height_add_ringKrullDim_quotient_le p) (le_height_add_ringKrullDim_quotient p)

end AristotleDimensionFormula
