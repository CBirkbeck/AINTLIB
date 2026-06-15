module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.CyclotomicLocalSetup.Part2.Concrete

@[expose] public section

noncomputable section

open scoped NumberField

namespace BernoulliRegular

namespace Furtwaengler

universe u v w

namespace ConductorFlexibleConcreteStickelbergerSetup

variable {ℓ p : ℕ} [Fact ℓ.Prime] [Fact p.Prime]
variable {k : Type u} [Field k] [Fintype k]
variable {K : Type v} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
variable {R' : Type w} [Field R'] [NumberField R'] [Algebra K R']
  [IsScalarTower ℚ K R']
variable [IsScalarTower ℤ (𝓞 K) (𝓞 R')]

variable (S : ConductorFlexibleConcreteStickelbergerSetup ℓ p k K R')

/-! ### Flexible descent prime and ramification-index descent

These are the conductor-flexible analogues of the exact pair-cyclotomic
`ConcreteStickelbergerSetup` descent-prime API above. The proofs use only the
chosen prime `Q`, the map `𝓞 K → 𝓞 R'`, and explicit structural hypotheses; no
`[IsCyclotomicExtension {p, ℓ} ℚ R']` shortcut is used. -/

/-- The descent prime in `𝓞 K`: `q_K := S.Q.under (𝓞 K)`. -/
noncomputable def descentPrime : Ideal (𝓞 K) := S.Q.under (𝓞 K)

omit [IsScalarTower ℤ (𝓞 K) (𝓞 R')] in
theorem descentPrime_isPrime : (S.descentPrime).IsPrime := haveI := S.hQ_prime
  Q_under_isPrime (K := K) S.Q

theorem descentPrime_contains_ell : (ℓ : 𝓞 K) ∈ S.descentPrime :=
  haveI := S.hQ_prime
  Q_under_contains_ell (K := K) (ℓ := ℓ) S.Q S.hQ

theorem descentPrime_ne_bot : S.descentPrime ≠ ⊥ :=
  haveI := S.hQ_prime
  Q_under_ne_bot (K := K) (ℓ := ℓ) S.Q S.hQ

omit [IsScalarTower ℤ (𝓞 K) (𝓞 R')] in
/-- Pushforward: `x ∈ S.descentPrime^n` implies `(x : 𝓞 R') ∈ S.Q^n`. -/
theorem mem_Q_pow_of_mem_descentPrime_pow {x : 𝓞 K} {n : ℕ} (hx : x ∈ S.descentPrime ^ n) :
    algebraMap (𝓞 K) (𝓞 R') x ∈ S.Q ^ n := by
  have h_le : S.descentPrime ^ n ≤
      Ideal.comap (algebraMap (𝓞 K) (𝓞 R')) (S.Q ^ n) :=
    Ideal.le_comap_pow (algebraMap (𝓞 K) (𝓞 R')) (K := S.Q) n
  exact h_le hx

omit [IsScalarTower ℤ (𝓞 K) (𝓞 R')] in
/-- The `descentPrime` is the comap of `S.Q` under `algebraMap (𝓞 K) (𝓞 R')`. -/
theorem descentPrime_eq_comap : S.descentPrime = Ideal.comap (algebraMap (𝓞 K) (𝓞 R')) S.Q :=
  rfl

omit [IsScalarTower ℤ (𝓞 K) (𝓞 R')] in
/-- Bundle accessor: `x ∈ S.descentPrime ↔ algebraMap x ∈ S.Q`. -/
theorem mem_descentPrime_iff (x : 𝓞 K) :
    x ∈ S.descentPrime ↔ algebraMap (𝓞 K) (𝓞 R') x ∈ S.Q := by
  rw [descentPrime_eq_comap, Ideal.mem_comap]

/-- The ramification index of `Q ⊂ 𝓞 R'` over `descentPrime ⊂ 𝓞 K`. -/
noncomputable def descentRamificationIdx : ℕ :=
  Ideal.ramificationIdx S.descentPrime S.Q

omit [IsScalarTower ℤ (𝓞 K) (𝓞 R')] in
/-- Image of `descentPrime` in `𝓞 R'` is contained in `S.Q^e`. -/
theorem map_descentPrime_le : Ideal.map (algebraMap (𝓞 K) (𝓞 R')) S.descentPrime ≤
      S.Q ^ S.descentRamificationIdx :=
  Ideal.le_pow_ramificationIdx

omit [IsScalarTower ℤ (𝓞 K) (𝓞 R')] in
/-- For `x ∈ S.descentPrime`, the algebra map sends `x` into `S.Q^e`. -/
theorem algebraMap_mem_Q_pow_ramificationIdx_of_mem_descentPrime
    {x : 𝓞 K} (hx : x ∈ S.descentPrime) :
    algebraMap (𝓞 K) (𝓞 R') x ∈ S.Q ^ S.descentRamificationIdx :=
  S.map_descentPrime_le (Ideal.mem_map_of_mem _ hx)

omit [IsScalarTower ℤ (𝓞 K) (𝓞 R')] in
/-- Power-form ramification containment: image of `descentPrime^n` sits
inside `S.Q^(e*n)`. -/
theorem map_descentPrime_pow_le (n : ℕ) :
    Ideal.map (algebraMap (𝓞 K) (𝓞 R')) (S.descentPrime ^ n) ≤
      S.Q ^ (S.descentRamificationIdx * n) := by
  rw [Ideal.map_pow, pow_mul]
  exact Ideal.pow_right_mono S.map_descentPrime_le n

omit [IsScalarTower ℤ (𝓞 K) (𝓞 R')] in
/-- For `x ∈ S.descentPrime^n`, the algebra map sends `x` into `S.Q^(e*n)`. -/
theorem algebraMap_mem_Q_pow_of_mem_descentPrime_pow
    {x : 𝓞 K} {n : ℕ} (hx : x ∈ S.descentPrime ^ n) :
    algebraMap (𝓞 K) (𝓞 R') x ∈ S.Q ^ (S.descentRamificationIdx * n) :=
  S.map_descentPrime_pow_le n (Ideal.mem_map_of_mem _ hx)

omit [IsScalarTower ℤ (𝓞 K) (𝓞 R')] in
/-- The bundle's prime `S.Q` is not the zero ideal. -/
theorem Q_ne_bot' : S.Q ≠ ⊥ := by
  intro h
  have h_in : (ℓ : 𝓞 R') ∈ (⊥ : Ideal (𝓞 R')) := h ▸ S.hQ
  rw [Ideal.mem_bot] at h_in
  have : (ℓ : 𝓞 R') ≠ 0 := by exact_mod_cast (Fact.out : ℓ.Prime).ne_zero
  exact this h_in

/-- `S.Q.LiesOver S.descentPrime` (definitional). -/
instance Q_liesOver_descentPrime : S.Q.LiesOver S.descentPrime :=
  ⟨rfl⟩

/-- Multiplicity descent: `v_Q(algebraMap x) = e · v_q(x)` for any nonzero
`x ∈ 𝓞 K`. -/
theorem emultiplicity_Q_eq_ramificationIdx_mul_emultiplicity_descentPrime
    [FaithfulSMul (𝓞 K) (𝓞 R')]
    {x : 𝓞 K} (hx : x ≠ 0) :
    emultiplicity S.Q (Ideal.span ({algebraMap (𝓞 K) (𝓞 R') x} : Set (𝓞 R'))) =
      S.descentRamificationIdx *
        emultiplicity S.descentPrime (Ideal.span ({x} : Set (𝓞 K))) := by
  haveI := S.descentPrime_isPrime
  have h_descent_ne_bot : S.descentPrime ≠ ⊥ := S.descentPrime_ne_bot
  haveI := S.hQ_prime
  have hQ_ne : S.Q ≠ ⊥ := S.Q_ne_bot'
  haveI := S.Q_liesOver_descentPrime
  have h_map : Ideal.map (algebraMap (𝓞 K) (𝓞 R'))
        (Ideal.span ({x} : Set (𝓞 K))) =
      Ideal.span ({algebraMap (𝓞 K) (𝓞 R') x} : Set (𝓞 R')) := by
    rw [Ideal.map_span, Set.image_singleton]
  rw [← h_map]
  have hspan_ne : Ideal.span ({x} : Set (𝓞 K)) ≠ ⊥ := by
    rwa [Ne, Ideal.span_singleton_eq_bot]
  have hQ_irred : Irreducible S.Q :=
    UniqueFactorizationMonoid.irreducible_iff_prime.mpr
      (Ideal.prime_of_isPrime hQ_ne S.hQ_prime)
  have hq_irred : Irreducible S.descentPrime :=
    UniqueFactorizationMonoid.irreducible_iff_prime.mpr
      (Ideal.prime_of_isPrime h_descent_ne_bot S.descentPrime_isPrime)
  exact Ideal.IsDedekindDomain.emultiplicity_map_eq_ramificationIdx_mul
    hspan_ne hq_irred hQ_irred hQ_ne

/-- The descent ramification index is non-zero. -/
theorem descentRamificationIdx_ne_zero
    [IsDomain (𝓞 K)] [Module.IsTorsionFree (𝓞 K) (𝓞 R')] :
    S.descentRamificationIdx ≠ 0 := by
  haveI := S.descentPrime_isPrime
  haveI := S.hQ_prime
  haveI := S.Q_liesOver_descentPrime
  exact Ideal.IsDedekindDomain.ramificationIdx_ne_zero_of_liesOver
    S.Q S.descentPrime_ne_bot

/-- The descent ramification index is positive. -/
theorem descentRamificationIdx_pos
    [IsDomain (𝓞 K)] [Module.IsTorsionFree (𝓞 K) (𝓞 R')] :
    0 < S.descentRamificationIdx :=
  Nat.pos_of_ne_zero S.descentRamificationIdx_ne_zero

/-- Iff form of valuation descent. -/
theorem mem_descentPrime_pow_iff_algebraMap_mem_Q_pow_mul
    [FaithfulSMul (𝓞 K) (𝓞 R')]
    [Module.IsTorsionFree (𝓞 K) (𝓞 R')]
    {x : 𝓞 K} (hx : x ≠ 0) (n : ℕ) :
    x ∈ S.descentPrime ^ n ↔
      algebraMap (𝓞 K) (𝓞 R') x ∈ S.Q ^ (S.descentRamificationIdx * n) := by
  haveI := S.descentPrime_isPrime
  have h_descent_ne_bot : S.descentPrime ≠ ⊥ := S.descentPrime_ne_bot
  haveI := S.hQ_prime
  have hQ_ne : S.Q ≠ ⊥ := S.Q_ne_bot'
  haveI := S.Q_liesOver_descentPrime
  have hspan_x_ne : Ideal.span ({x} : Set (𝓞 K)) ≠ ⊥ := by
    rwa [Ne, Ideal.span_singleton_eq_bot]
  have hQ_irred : Irreducible S.Q :=
    UniqueFactorizationMonoid.irreducible_iff_prime.mpr
      (Ideal.prime_of_isPrime hQ_ne S.hQ_prime)
  have hq_irred : Irreducible S.descentPrime :=
    UniqueFactorizationMonoid.irreducible_iff_prime.mpr
      (Ideal.prime_of_isPrime h_descent_ne_bot S.descentPrime_isPrime)
  have h_emult :=
    S.emultiplicity_Q_eq_ramificationIdx_mul_emultiplicity_descentPrime hx
  have h_lhs : x ∈ S.descentPrime ^ n ↔
      S.descentPrime ^ n ∣ Ideal.span ({x} : Set (𝓞 K)) := by
    rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
  have h_rhs : algebraMap (𝓞 K) (𝓞 R') x ∈ S.Q ^ (S.descentRamificationIdx * n) ↔
      S.Q ^ (S.descentRamificationIdx * n) ∣
        Ideal.span ({algebraMap (𝓞 K) (𝓞 R') x} : Set (𝓞 R')) := by
    rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
  rw [h_lhs, h_rhs]
  rw [pow_dvd_iff_le_emultiplicity, pow_dvd_iff_le_emultiplicity]
  rw [h_emult]
  have he_ne : (S.descentRamificationIdx : ℕ∞) ≠ 0 := by
    exact_mod_cast S.descentRamificationIdx_ne_zero
  have he_top : (S.descentRamificationIdx : ℕ∞) ≠ ⊤ := ENat.coe_ne_top _
  rw [show ((S.descentRamificationIdx * n : ℕ) : ℕ∞) =
      (S.descentRamificationIdx : ℕ∞) * (n : ℕ∞) by push_cast; ring]
  exact (ENat.mul_le_mul_left_iff he_ne he_top).symm

/-- Exact-order descent at the flexible descent prime. -/
theorem mem_descentPrime_pow_and_not_succ_iff
    [FaithfulSMul (𝓞 K) (𝓞 R')]
    [Module.IsTorsionFree (𝓞 K) (𝓞 R')]
    {x : 𝓞 K} (hx : x ≠ 0) (n : ℕ) :
    (x ∈ S.descentPrime ^ n ∧ x ∉ S.descentPrime ^ (n + 1)) ↔
      (algebraMap (𝓞 K) (𝓞 R') x ∈ S.Q ^ (S.descentRamificationIdx * n) ∧
        algebraMap (𝓞 K) (𝓞 R') x ∉
          S.Q ^ (S.descentRamificationIdx * (n + 1))) := by
  have h1 := S.mem_descentPrime_pow_iff_algebraMap_mem_Q_pow_mul hx n
  have h2 := S.mem_descentPrime_pow_iff_algebraMap_mem_Q_pow_mul hx (n + 1)
  rw [h1, h2]

/-! ### Flexible Galois descent for `gaussSumInt a ^ p` -/

/-- Statement: there exists a `γ ∈ 𝓞 K` with
`algebraMap γ = S.gaussSumInt a ^ p`. -/
def IsGalDescentTo_OK (a : ℕ) : Prop :=
  ∃ γ : 𝓞 K, algebraMap (𝓞 K) (𝓞 R') γ = S.gaussSumInt a ^ p

omit [IsScalarTower ℤ (𝓞 K) (𝓞 R')] in
/-- Field-level descent of `S.gaussSumInt a ^ p` gives integral descent to
`𝓞 K`. -/
theorem isGalDescentTo_OK_of_field_descent (a : ℕ) (h : ∃ y : K, algebraMap K R' y =
      algebraMap (𝓞 R') R' (S.gaussSumInt a ^ p)) :
    S.IsGalDescentTo_OK a := by
  obtain ⟨y, hy⟩ := h
  have h_int_R' : IsIntegral ℤ (algebraMap K R' y) := by
    rw [hy]
    exact NumberField.RingOfIntegers.isIntegral_coe (S.gaussSumInt a ^ p)
  have h_int : IsIntegral ℤ y :=
    (isIntegral_algebraMap_iff (FaithfulSMul.algebraMap_injective K R')).mp h_int_R'
  refine ⟨⟨y, h_int⟩, ?_⟩
  apply NumberField.RingOfIntegers.coe_injective (K := R')
  show algebraMap (𝓞 R') R' (algebraMap (𝓞 K) (𝓞 R') ⟨y, h_int⟩) =
        algebraMap (𝓞 R') R' (S.gaussSumInt a ^ p)
  rw [← IsScalarTower.algebraMap_apply (𝓞 K) (𝓞 R') R',
      IsScalarTower.algebraMap_apply (𝓞 K) K R']
  change algebraMap K R' y = _
  exact hy

omit [IsScalarTower ℤ (𝓞 K) (𝓞 R')] in
/-- Galois-fixed-elements form of flexible integral descent. -/
theorem isGalDescentTo_OK_of_galois_fixed
    [IsGalois K R'] [FiniteDimensional K R']
    (a : ℕ)
    (h_fixed : ∀ f : R' ≃ₐ[K] R',
      f (algebraMap (𝓞 R') R' (S.gaussSumInt a ^ p)) =
        algebraMap (𝓞 R') R' (S.gaussSumInt a ^ p)) :
    S.IsGalDescentTo_OK a := by
  have h_in_range :
      algebraMap (𝓞 R') R' (S.gaussSumInt a ^ p) ∈
        Set.range (algebraMap K R') :=
    (IsGalois.mem_range_algebraMap_iff_fixed
      (algebraMap (𝓞 R') R' (S.gaussSumInt a ^ p))).mpr h_fixed
  obtain ⟨y, hy⟩ := h_in_range
  exact S.isGalDescentTo_OK_of_field_descent a ⟨y, hy⟩

omit [IsScalarTower ℤ (𝓞 K) (𝓞 R')] in
/-- Coercing the integral residue character to `R'` recovers the original
field-valued residue character. -/
theorem residueCharInt_ringHomComp :
    S.residueCharInt.ringHomComp (algebraMap (𝓞 R') R') = S.residueChar := by
  ext u
  letI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  simp [ConductorFlexibleConcreteStickelbergerSetup.residueCharInt,
    ConductorFlexibleConcreteStickelbergerSetup.residueChar,
    StickelbergerSetup.residueChar,
    ConductorFlexibleConcreteStickelbergerSetup.abstractSetup,
    S.zeta_p_int_spec,
    residueMulChar_apply_unit]

omit [IsScalarTower ℤ (𝓞 K) (𝓞 R')] in
/-- Coercing the integral additive character to `R'` recovers the original
field-valued additive character. -/
@[simp]
theorem algebraMap_psiInt (x : k) : algebraMap (𝓞 R') R' (S.psiInt x) = S.psi x := by
  change algebraMap (𝓞 R') R' (S.zeta_ell_int ^ S.psiExponent x) = S.psi x
  rw [map_pow, S.algebraMap_zeta_ell_int]
  exact (S.psi_pow_form x).symm

omit [IsScalarTower ℤ (𝓞 K) (𝓞 R')] in
/-- Additive-character form of `algebraMap_psiInt`. -/
theorem psiInt_ringHomComp :
    (algebraMap (𝓞 R') R').toMonoidHom.compAddChar S.psiInt = S.psi := by
  ext x
  exact S.algebraMap_psiInt x

omit [IsScalarTower ℤ (𝓞 K) (𝓞 R')] in
/-- Coercing the flexible integral Gauss sum to the field target recovers the
field-valued Gauss sum used in the abstract Stickelberger setup. -/
theorem algebraMap_gaussSumInt (a : ℕ) :
    algebraMap (𝓞 R') R' (S.gaussSumInt a) =
      _root_.gaussSum (S.residueChar ^ a) S.psi := by
  unfold ConductorFlexibleConcreteStickelbergerSetup.gaussSumInt
  rw [gaussSum_ringHomComp]
  have hχ :
      (S.residueCharInt ^ a).ringHomComp (algebraMap (𝓞 R') R') =
        S.residueChar ^ a := by
    rw [← MulChar.ringHomComp_pow, S.residueCharInt_ringHomComp]
  rw [hχ, S.psiInt_ringHomComp]

omit [IsScalarTower ℤ (𝓞 K) (𝓞 R')] in
/-- Pure ring-hom form of Galois invariance for the field-level
`gaussSumInt^p`. -/
theorem algebraMap_gaussSumInt_pow_p_invariant
    (a : ℕ)
    (σ : R' →+* R') {a' : kˣ}
    (hσχ : (S.residueChar ^ a).ringHomComp σ = S.residueChar ^ a)
    (hσψ : σ.toMonoidHom.compAddChar S.psi = AddChar.mulShift S.psi a') :
    σ (algebraMap (𝓞 R') R' (S.gaussSumInt a ^ p)) =
      algebraMap (𝓞 R') R' (S.gaussSumInt a ^ p) := by
  rw [map_pow, S.algebraMap_gaussSumInt]
  have hχap : (S.residueChar ^ a) ^ p = 1 := by
    have hχp : S.residueChar ^ p = 1 := by
      simpa [ConductorFlexibleConcreteStickelbergerSetup.residueChar] using
        S.abstractSetup.residueChar_pow_eq_one
    rw [← pow_mul, mul_comm, pow_mul, hχp, one_pow]
  exact gaussSum_pow_invariant_of_pow_eq_one
    (S.residueChar ^ a) S.psi hχap σ a' hσχ hσψ

/-- Galois compatibility predicate for the flexible concrete setup. -/
def IsGalCompatible (a : ℕ) : Prop :=
  ∀ f : R' ≃ₐ[K] R',
    ∃ a' : kˣ,
      (S.residueChar ^ a).ringHomComp (f : R' →+* R') = S.residueChar ^ a ∧
        (f : R' →+* R').toMonoidHom.compAddChar S.psi =
          AddChar.mulShift S.psi a'

omit [IsScalarTower ℤ (𝓞 K) (𝓞 R')] in
/-- If a ring hom `σ : R' →+* R'` fixes `S.zeta_p`, then it fixes
`S.residueChar`. -/
theorem residueChar_ringHomComp_eq_of_fixes_zeta_p (σ : R' →+* R')
    (h_fixes : σ ((S.zeta_p : R'ˣ) : R') = ((S.zeta_p : R'ˣ) : R')) :
    S.residueChar.ringHomComp σ = S.residueChar := by
  letI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have h_pow1 : ((S.zeta_p : R'ˣ) : R') ^ 1 = ((S.zeta_p : R'ˣ) : R') := pow_one _
  have := residueMulChar_ringHomComp_pow_eq
    S.zeta_k S.hzeta_k S.hdiv S.zeta_p S.hzeta_p σ 1 (h_fixes.trans h_pow1.symm)
  rw [pow_one] at this
  exact this

omit [IsScalarTower ℤ (𝓞 K) (𝓞 R')] in
/-- Power-form: σ fixing `zeta_p` implies σ fixes `residueChar^a`. -/
theorem residueChar_pow_ringHomComp_eq_of_fixes_zeta_p
    (a : ℕ) (σ : R' →+* R')
    (h_fixes : σ ((S.zeta_p : R'ˣ) : R') = ((S.zeta_p : R'ˣ) : R')) :
    (S.residueChar ^ a).ringHomComp σ = S.residueChar ^ a := by
  rw [← MulChar.ringHomComp_pow, residueChar_ringHomComp_eq_of_fixes_zeta_p _ σ h_fixes]

omit [NumberField K] [NumberField R'] [IsScalarTower ℚ K R']
    [IsScalarTower ℤ (𝓞 K) (𝓞 R')] in
/-- For any `f : R' ≃ₐ[K] R'`, `f` fixes elements in the range of
`algebraMap K R'`. -/
theorem algEquiv_fixes_algebraMap_range
    (f : R' ≃ₐ[K] R') (x : R') (hx : x ∈ Set.range (algebraMap K R')) :
    f x = x := by
  obtain ⟨y, rfl⟩ := hx
  exact f.commutes y

omit [IsScalarTower ℤ (𝓞 K) (𝓞 R')] in
/-- If `S.zeta_p` lifts to `K`, every K-algebra automorphism of `R'` fixes it. -/
theorem algEquiv_fixes_zeta_p_of_in_range
    (h_in_range : ((S.zeta_p : R'ˣ) : R') ∈ Set.range (algebraMap K R')) :
    ∀ f : R' ≃ₐ[K] R',
      (f : R' →+* R') ((S.zeta_p : R'ˣ) : R') = ((S.zeta_p : R'ˣ) : R') := fun f =>
  algEquiv_fixes_algebraMap_range f _ h_in_range

omit [IsScalarTower ℤ (𝓞 K) (𝓞 R')] in
/-- The bundle's primitive `p`-th root in `R'` is in the image of
`algebraMap K R'`. -/
theorem zeta_p_in_algebraMap_range : ((S.zeta_p : R'ˣ) : R') ∈ Set.range (algebraMap K R') := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  obtain ⟨ξ, hξ⟩ := IsCyclotomicExtension.exists_isPrimitiveRoot ℚ K (S := {p})
    (Set.mem_singleton p) (Fact.out : p.Prime).ne_zero
  have hξ_R' : IsPrimitiveRoot (algebraMap K R' ξ) p :=
    hξ.map_of_injective (FaithfulSMul.algebraMap_injective K R')
  have hzp_pow : ((S.zeta_p : R'ˣ) : R') ^ p = 1 := by
    rw [← Units.val_pow_eq_pow_val, S.hzeta_p.pow_eq_one, Units.val_one]
  obtain ⟨i, _, hi⟩ := hξ_R'.eq_pow_of_pow_eq_one hzp_pow
  refine ⟨ξ ^ i, ?_⟩
  rw [map_pow]
  exact hi

omit [IsScalarTower ℤ (𝓞 K) (𝓞 R')] in
/-- Every K-algebra automorphism of `R'` fixes the bundle's primitive
`p`-th root. -/
theorem algEquiv_fixes_zeta_p (f : R' ≃ₐ[K] R') :
    (f : R' →+* R') ((S.zeta_p : R'ˣ) : R') = ((S.zeta_p : R'ˣ) : R') :=
  S.algEquiv_fixes_zeta_p_of_in_range S.zeta_p_in_algebraMap_range f

omit [IsScalarTower ℤ (𝓞 K) (𝓞 R')] in
/-- Every K-algebra automorphism of `R'` fixes `residueChar^a`. -/
theorem residueChar_pow_ringHomComp_eq_of_algEquiv
    (a : ℕ) (f : R' ≃ₐ[K] R') :
    (S.residueChar ^ a).ringHomComp (f : R' →+* R') = S.residueChar ^ a :=
  S.residueChar_pow_ringHomComp_eq_of_fixes_zeta_p a (f : R' →+* R')
    (S.algEquiv_fixes_zeta_p f)

/-- The psi-shift compatibility predicate. -/
def IsGalPsiShiftCompatible : Prop :=
  ∀ f : R' ≃ₐ[K] R', ∃ a' : kˣ,
    (f : R' →+* R').toMonoidHom.compAddChar S.psi =
      AddChar.mulShift S.psi a'

omit [IsScalarTower ℤ (𝓞 K) (𝓞 R')] in
/-- Psi-shift compatibility implies `IsGalCompatible a` for every `a`. -/
theorem isGalCompatible_of_isGalPsiShiftCompatible
    (a : ℕ) (h : S.IsGalPsiShiftCompatible) :
    S.IsGalCompatible a := by
  intro f
  obtain ⟨a', hψ⟩ := h f
  exact ⟨a', S.residueChar_pow_ringHomComp_eq_of_algEquiv a f, hψ⟩

omit [IsScalarTower ℤ (𝓞 K) (𝓞 R')] in
/-- From flexible Galois compatibility and standard Galois conditions, the
field-level fixedness condition holds and hence integral descent holds. -/
theorem isGalDescentTo_OK_of_galCompatible
    [IsGalois K R'] [FiniteDimensional K R']
    (a : ℕ) (h : S.IsGalCompatible a) :
    S.IsGalDescentTo_OK a := by
  apply S.isGalDescentTo_OK_of_galois_fixed a
  intro f
  obtain ⟨a', hσχ, hσψ⟩ := h f
  exact S.algebraMap_gaussSumInt_pow_p_invariant a (f : R' →+* R') hσχ hσψ

omit [IsScalarTower ℤ (𝓞 K) (𝓞 R')] in
/-- Flexible integral descent from the psi-shift compatibility predicate. -/
theorem isGalDescentTo_OK_of_isGalPsiShiftCompatible
    [IsGalois K R'] [FiniteDimensional K R']
    (a : ℕ) (h : S.IsGalPsiShiftCompatible) :
    S.IsGalDescentTo_OK a :=
  S.isGalDescentTo_OK_of_galCompatible a
    (S.isGalCompatible_of_isGalPsiShiftCompatible a h)

omit [IsScalarTower ℤ (𝓞 K) (𝓞 R')] in
/-- `gaussSumInt a ^ p ≠ 0` whenever `gaussSumInt a ≠ 0`. -/
theorem gaussSumInt_pow_p_ne_zero_of_ne_zero {a : ℕ} (h : S.gaussSumInt a ≠ 0) :
    S.gaussSumInt a ^ p ≠ 0 :=
  pow_ne_zero p h

omit [IsScalarTower ℤ (𝓞 K) (𝓞 R')] in
/-- `gaussSumInt a ≠ 0` whenever an exact-order witness proves it is not in
the next power of `Q`. -/
theorem gaussSumInt_ne_zero_of_not_mem_Q_pow_succ
    {a d : ℕ} (h : S.gaussSumInt a ∉ S.Q ^ (d + 1)) :
    S.gaussSumInt a ≠ 0 := by
  intro h_zero
  apply h
  rw [h_zero]
  exact (S.Q ^ (d + 1)).zero_mem

end ConductorFlexibleConcreteStickelbergerSetup

namespace CyclotomicLocalSetup

end CyclotomicLocalSetup

end Furtwaengler

end BernoulliRegular

end
