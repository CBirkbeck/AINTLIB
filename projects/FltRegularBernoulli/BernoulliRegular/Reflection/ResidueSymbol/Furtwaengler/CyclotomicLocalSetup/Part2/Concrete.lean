module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.ConcreteSetup
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.KummerFurtwaengler
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.CanonicalResidueRoot
public import Mathlib.NumberTheory.Cyclotomic.Basic
public import Mathlib.RingTheory.Ideal.GoingUp
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.CyclotomicLocalSetup.PrimitiveRootsResidueFieldBundle


/-!
# Concrete cyclotomic local setup at a prime above ℓ ≠ p

This file is the home for **REF-18c2c5-b** — constructing a
`ConcreteStickelbergerSetup ℓ p k K R'` instance where
`K = ℚ(ζ_p)`, `R' ⊃ K` is a cyclotomic extension containing `ζ_ℓ`,
and the user supplies a prime `Q ⊂ 𝓞 R'` above ℓ.

## Strategy

We provide a CONSTRUCTOR `mkConcreteStickelbergerSetup` taking the
prime `Q` (above ℓ in `𝓞 R'`) as input and assembling all the required
witnesses from mathlib's cyclotomic API:

* `zeta_p` and `zeta_ell` come from
  `IsCyclotomicExtension.exists_isPrimitiveRoot` applied to `R'`.
* `zeta_p_int`, `zeta_ell_int` come from `IsPrimitiveRoot.toInteger`.
* The residue field `k = 𝓞 R' / Q` is the canonical choice; the
  residue map is `Ideal.Quotient.mk Q`.
* `card_k = ℓ ^ f` requires the inertia degree of Q over ℓ.
* The primitive p-th root in k is the image of `zetaPInt` under the
  residue map; primitivity requires `p ∣ #k - 1`.

## Status

Stage 1 (primitive roots in R') — DONE.
Stage 2 (integral lifts in 𝓞 R') — DONE.
Stage 3 (residue field and map) — DONE.
Stage 4 (assembly into the bundle) — REMAINING (still needs `card_k`,
   `hzeta_k`, `hdiv` and the bundle-building tactic).
-/

@[expose] public section

noncomputable section

open scoped NumberField

namespace BernoulliRegular

namespace Furtwaengler

universe u v w

namespace ConcreteStickelbergerSetup

variable {ℓ p : ℕ} [Fact ℓ.Prime] [Fact p.Prime]
variable {k : Type u} [Field k] [Fintype k]
variable {K : Type v} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
variable {R' : Type w} [Field R'] [NumberField R'] [Algebra K R']
  [IsScalarTower ℚ K R'] [IsCyclotomicExtension {p, ℓ} ℚ R']
variable [IsScalarTower ℤ (𝓞 K) (𝓞 R')]

variable (S : ConcreteStickelbergerSetup ℓ p k K R')

/-! ### Membership descent

For `x ∈ 𝓞 K`, membership of `x` in `S.descentPrime^n` implies
membership of its image in `S.Q^n`. This is the "easy" direction —
the reverse needs ramification index. -/

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

/-! ### Ramification index of `descentPrime` in `S.Q`

For the cyclotomic extension `K → R' = K(ζ_ℓ)`, the prime `Q ⊂ 𝓞 R'`
above `descentPrime` has ramification index given by `Ideal.ramificationIdx`.
This packages the abstract ramification index for downstream descent
arguments. -/

/-- The ramification index of `Q ⊂ 𝓞 R'` over `descentPrime ⊂ 𝓞 K`. -/
noncomputable def descentRamificationIdx : ℕ :=
  Ideal.ramificationIdx S.descentPrime S.Q

omit [IsScalarTower ℤ (𝓞 K) (𝓞 R')] in
/-- Image of `descentPrime` in `𝓞 R'` is contained in `S.Q^e` (ramification
containment). This is the standard `le_pow_ramificationIdx`. -/
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

/-! ### Multiplicity descent (full Galois descent of valuations)

The substantive Dedekind-domain content connecting `S.Q`-adic and
`S.descentPrime`-adic valuations: for any `x ∈ 𝓞 K \ {0}`,
`v_Q(algebraMap x) = e · v_q(x)`. Standard application of
`Ideal.emultiplicity_map_eq_ramificationIdx_mul`. -/

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

/-! ### Iff form of valuation descent

Combining the multiplicity-equality + ramification-index-positivity:
for `x ∈ 𝓞 K \ {0}`, the algebra map sends `x` into `Q^(e*n)` iff
`x ∈ descentPrime^n`. -/

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
  -- Translate everything to multiplicities.
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
  -- LHS membership ↔ pow_dvd of the span by descentPrime.
  have h_lhs : x ∈ S.descentPrime ^ n ↔
      S.descentPrime ^ n ∣ Ideal.span ({x} : Set (𝓞 K)) := by
    rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
  -- RHS membership ↔ pow_dvd of the image span by Q.
  have h_rhs : algebraMap (𝓞 K) (𝓞 R') x ∈ S.Q ^ (S.descentRamificationIdx * n) ↔
      S.Q ^ (S.descentRamificationIdx * n) ∣
        Ideal.span ({algebraMap (𝓞 K) (𝓞 R') x} : Set (𝓞 R')) := by
    rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
  rw [h_lhs, h_rhs]
  rw [pow_dvd_iff_le_emultiplicity, pow_dvd_iff_le_emultiplicity]
  rw [h_emult]
  -- Goal: (n : ℕ∞) ≤ emult ↔ (e * n : ℕ∞) ≤ e * emult, where e ≥ 1.
  have he_ne : (S.descentRamificationIdx : ℕ∞) ≠ 0 := by
    exact_mod_cast S.descentRamificationIdx_ne_zero
  have he_top : (S.descentRamificationIdx : ℕ∞) ≠ ⊤ := ENat.coe_ne_top _
  rw [show ((S.descentRamificationIdx * n : ℕ) : ℕ∞) =
      (S.descentRamificationIdx : ℕ∞) * (n : ℕ∞) by push_cast; ring]
  exact (ENat.mul_le_mul_left_iff he_ne he_top).symm

/-- Exact-order descent: combining the iff with its negation gives the
exact descentPrime-adic order from the exact Q-adic order. -/
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

/-! ### Translation of step 2 to `descentPrime`

If we are supplied with a Galois-invariance witness `γ ∈ 𝓞 K` with
`algebraMap γ = S.gaussSumInt a ^ p`, the iff form transports the
step-2 Q-adic data into 𝓞 K.

The Galois-invariance witness itself is an open piece (see ticket
REF-18c2c5-b's c.1.4): one shows `S.gaussSumInt a ^ p` is fixed by
`Gal(R'/K)` (using `gaussSumInt_pow_p_invariant` from
`Stickelberger.lean` plus the cyclotomic Galois action), and combined
with `IsCyclotomicExtension.isGalois` and Galois-fixed-implies-in-K
plus `isIntegral_algebraMap_iff`-style descent, this packages a
γ ∈ 𝓞 K. -/

/-- Statement: there exists a `γ ∈ 𝓞 K` with `algebraMap γ = S.gaussSumInt a ^ p`.
This is the Galois-invariance descent, the open c.1.4 substantive
content. Currently a `Prop` predicate; a future proof would witness it
via the `Stickelberger.gaussSum_pow_invariant_of_pow_eq_one` lemma plus
the Galois-fixed-equals-K lemma in cyclotomic extensions. -/
def IsGalDescentTo_OK (a : ℕ) : Prop :=
  ∃ γ : 𝓞 K, algebraMap (𝓞 K) (𝓞 R') γ = S.gaussSumInt a ^ p

omit [IsScalarTower ℤ (𝓞 K) (𝓞 R')] in
/-- Sufficient condition for the Galois descent: at the field level, if
`(algebraMap (𝓞 R') R') (S.gaussSumInt a ^ p)` is in the range of
`algebraMap K R'`, we obtain the integral descent. The hypothesis is
exactly the field-level Galois-fixed condition (via
`mem_range_algebraMap_iff_fixed` for `IsGalois K R'`). -/
theorem isGalDescentTo_OK_of_field_descent (a : ℕ) (h : ∃ y : K, algebraMap K R' y =
      algebraMap (𝓞 R') R' (S.gaussSumInt a ^ p)) :
    S.IsGalDescentTo_OK a := by
  obtain ⟨y, hy⟩ := h
  -- y is integral over ℤ. Strategy: algebraMap K R' y is in 𝓞 R'-image,
  -- which is integral. By injectivity of algebraMap K R', y is integral.
  have h_int_R' : IsIntegral ℤ (algebraMap K R' y) := by
    rw [hy]
    exact NumberField.RingOfIntegers.isIntegral_coe (S.gaussSumInt a ^ p)
  have h_int : IsIntegral ℤ y :=
    (isIntegral_algebraMap_iff (FaithfulSMul.algebraMap_injective K R')).mp h_int_R'
  refine ⟨⟨y, h_int⟩, ?_⟩
  -- The algebraMap (𝓞 K) (𝓞 R') γ has the right image in R'.
  apply NumberField.RingOfIntegers.coe_injective (K := R')
  show algebraMap (𝓞 R') R' (algebraMap (𝓞 K) (𝓞 R') ⟨y, h_int⟩) =
        algebraMap (𝓞 R') R' (S.gaussSumInt a ^ p)
  rw [← IsScalarTower.algebraMap_apply (𝓞 K) (𝓞 R') R',
      IsScalarTower.algebraMap_apply (𝓞 K) K R']
  change algebraMap K R' y = _
  exact hy

omit [IsScalarTower ℤ (𝓞 K) (𝓞 R')] in
/-- Galois-fixed-elements form: given `IsGalois K R'` and finite
dimension, if every K-algebra automorphism of R' fixes `gaussSumInt a^p`,
then `IsGalDescentTo_OK a` holds. -/
theorem isGalDescentTo_OK_of_galois_fixed
    [IsGalois K R'] [FiniteDimensional K R']
    (a : ℕ)
    (h_fixed : ∀ f : R' ≃ₐ[K] R',
      f (algebraMap (𝓞 R') R' (S.gaussSumInt a ^ p)) =
        algebraMap (𝓞 R') R' (S.gaussSumInt a ^ p)) :
    S.IsGalDescentTo_OK a := by
  -- Apply mem_range_algebraMap_iff_fixed.
  have h_in_range :
      algebraMap (𝓞 R') R' (S.gaussSumInt a ^ p) ∈
        Set.range (algebraMap K R') :=
    (IsGalois.mem_range_algebraMap_iff_fixed
      (algebraMap (𝓞 R') R' (S.gaussSumInt a ^ p))).mpr h_fixed
  obtain ⟨y, hy⟩ := h_in_range
  exact S.isGalDescentTo_OK_of_field_descent a ⟨y, hy⟩

omit [IsScalarTower ℤ (𝓞 K) (𝓞 R')] in
/-- Pure ring-hom form of Galois invariance for the field-level
`gaussSumInt^p`. Reduction: σ fixing residueChar^a and shifting psi by a
unit fixes `gaussSum (residueChar^a) psi)^p` via the abstract
Stickelberger theorem. -/
theorem algebraMap_gaussSumInt_pow_p_invariant (a : ℕ)
    (σ : R' →+* R') {a' : kˣ}
    (hσχ : (S.residueChar ^ a).ringHomComp σ = S.residueChar ^ a)
    (hσψ : σ.toMonoidHom.compAddChar S.psi = AddChar.mulShift S.psi a') :
    σ (algebraMap (𝓞 R') R' (S.gaussSumInt a ^ p)) =
      algebraMap (𝓞 R') R' (S.gaussSumInt a ^ p) := by
  rw [map_pow, S.algebraMap_gaussSumInt]
  -- Build (residueChar^a)^p = 1.
  have hχap : (S.residueChar ^ a) ^ p = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, S.residueChar_pow_eq_one, one_pow]
  exact gaussSum_pow_invariant_of_pow_eq_one
    (S.residueChar ^ a) S.psi hχap σ a' hσχ hσψ

/-- A `IsGalCompatible` predicate isolates the structural assumption
underlying c.1.4: every K-algebra automorphism of R' satisfies the
two abstract Stickelberger invariance hypotheses (fix χ^a, shift ψ).

This is the cleanest separation of the open content from the bundled
descent. -/
def IsGalCompatible (a : ℕ) : Prop :=
  ∀ f : R' ≃ₐ[K] R',
    ∃ a' : kˣ,
      (S.residueChar ^ a).ringHomComp (f : R' →+* R') = S.residueChar ^ a ∧
        (f : R' →+* R').toMonoidHom.compAddChar S.psi =
          AddChar.mulShift S.psi a'

omit [IsScalarTower ℤ (𝓞 K) (𝓞 R')] in
/-- If a ring hom `σ : R' →+* R'` fixes `S.zeta_p`, then it fixes
`S.residueChar`. This is the structural half of `IsGalCompatible` —
applied to a K-algebra auto f and using `S.zeta_p ∈ K`, this says the
Galois action fixes residueChar. -/
theorem residueChar_ringHomComp_eq_of_fixes_zeta_p (σ : R' →+* R')
    (h_fixes : σ ((S.zeta_p : R'ˣ) : R') = ((S.zeta_p : R'ˣ) : R')) :
    S.residueChar.ringHomComp σ = S.residueChar := by
  letI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  -- residueChar = residueMulChar zeta_k hzeta_k hdiv S.zeta_p hzeta_p
  -- Apply residueMulChar_ringHomComp_pow_eq with a = 1.
  have h_pow1 : ((S.zeta_p : R'ˣ) : R') ^ 1 = ((S.zeta_p : R'ˣ) : R') := pow_one _
  have := residueMulChar_ringHomComp_pow_eq
    S.zeta_k S.hzeta_k S.hdiv S.zeta_p S.hzeta_p σ 1 (h_fixes.trans h_pow1.symm)
  -- The result has `^1` on the RHS; reduce to the unit power.
  rw [pow_one] at this
  exact this

omit [IsScalarTower ℤ (𝓞 K) (𝓞 R')] in
/-- Power-form: σ fixing `zeta_p` implies σ fixes `residueChar^a`. -/
theorem residueChar_pow_ringHomComp_eq_of_fixes_zeta_p
    (a : ℕ) (σ : R' →+* R')
    (h_fixes : σ ((S.zeta_p : R'ˣ) : R') = ((S.zeta_p : R'ˣ) : R')) :
    (S.residueChar ^ a).ringHomComp σ = S.residueChar ^ a := by
  rw [← MulChar.ringHomComp_pow, residueChar_ringHomComp_eq_of_fixes_zeta_p _ σ h_fixes]

omit [IsScalarTower ℤ (𝓞 K) (𝓞 R')] in
/-- Reduction of `IsGalCompatible` to the psi-shift hypothesis alone:
given that every K-alg auto fixes `zeta_p` (provable from K =
ℚ(ζ_p)) and shifts psi by a unit, we obtain `IsGalCompatible`. -/
theorem isGalCompatible_of_psi_shift
    (a : ℕ)
    (h_fix_zeta_p : ∀ f : R' ≃ₐ[K] R',
      (f : R' →+* R') ((S.zeta_p : R'ˣ) : R') = ((S.zeta_p : R'ˣ) : R'))
    (h_psi : ∀ f : R' ≃ₐ[K] R', ∃ a' : kˣ,
      (f : R' →+* R').toMonoidHom.compAddChar S.psi =
        AddChar.mulShift S.psi a') :
    S.IsGalCompatible a := by
  intro f
  obtain ⟨a', hψ⟩ := h_psi f
  refine ⟨a', ?_, hψ⟩
  exact S.residueChar_pow_ringHomComp_eq_of_fixes_zeta_p a (f : R' →+* R')
    (h_fix_zeta_p f)

omit [NumberField K] [NumberField R'] [IsScalarTower ℚ K R']
    [IsScalarTower ℤ (𝓞 K) (𝓞 R')] in
/-- For any `f : R' ≃ₐ[K] R'`, `f` fixes any element in the range of
`algebraMap K R'`. (Trivial: K-alg autos fix K elements.) -/
theorem algEquiv_fixes_algebraMap_range
    (f : R' ≃ₐ[K] R') (x : R') (hx : x ∈ Set.range (algebraMap K R')) :
    f x = x := by
  obtain ⟨y, rfl⟩ := hx
  exact f.commutes y

omit [IsScalarTower ℤ (𝓞 K) (𝓞 R')] in
/-- If `S.zeta_p` lifts to `K`, then every K-algebra automorphism of `R'`
fixes it. -/
theorem algEquiv_fixes_zeta_p_of_in_range
    (h_in_range : ((S.zeta_p : R'ˣ) : R') ∈ Set.range (algebraMap K R')) :
    ∀ f : R' ≃ₐ[K] R',
      (f : R' →+* R') ((S.zeta_p : R'ˣ) : R') = ((S.zeta_p : R'ˣ) : R') := fun f =>
  algEquiv_fixes_algebraMap_range f _ h_in_range

omit [IsScalarTower ℤ (𝓞 K) (𝓞 R')] in
/-- The bundle's primitive `p`-th root in `R'` is in the image of
`algebraMap K R'`, i.e., it lifts to `K`. This is automatic for the
cyclotomic setup since `K` already contains all `p`-th roots of unity. -/
theorem zeta_p_in_algebraMap_range : ((S.zeta_p : R'ˣ) : R') ∈ Set.range (algebraMap K R') := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  -- Get a primitive p-th root in K.
  obtain ⟨ξ, hξ⟩ := IsCyclotomicExtension.exists_isPrimitiveRoot ℚ K (S := {p})
    (Set.mem_singleton p) (Fact.out : p.Prime).ne_zero
  -- Its image is a primitive p-th root in R'.
  have hξ_R' : IsPrimitiveRoot (algebraMap K R' ξ) p :=
    hξ.map_of_injective (FaithfulSMul.algebraMap_injective K R')
  -- S.zeta_p satisfies (zeta_p : R')^p = 1.
  have hzp_pow : ((S.zeta_p : R'ˣ) : R') ^ p = 1 := by
    rw [← Units.val_pow_eq_pow_val, S.hzeta_p.pow_eq_one, Units.val_one]
  -- Apply eq_pow_of_pow_eq_one: ∃ i, (ξ : R')^i = (zeta_p : R').
  obtain ⟨i, _, hi⟩ := hξ_R'.eq_pow_of_pow_eq_one hzp_pow
  refine ⟨ξ ^ i, ?_⟩
  rw [map_pow]; exact hi

omit [IsScalarTower ℤ (𝓞 K) (𝓞 R')] in
/-- Every K-algebra automorphism of `R'` fixes the bundle's primitive
`p`-th root. Combines `zeta_p_in_algebraMap_range` with the trivial
fact that K-alg autos fix K-image. -/
theorem algEquiv_fixes_zeta_p (f : R' ≃ₐ[K] R') :
    (f : R' →+* R') ((S.zeta_p : R'ˣ) : R') = ((S.zeta_p : R'ˣ) : R') :=
  S.algEquiv_fixes_zeta_p_of_in_range S.zeta_p_in_algebraMap_range f

omit [IsScalarTower ℤ (𝓞 K) (𝓞 R')] in
/-- Power-form of `algEquiv_fixes_zeta_p`-derived residueChar fixedness:
every K-alg auto of `R'` fixes `residueChar^a`. Closes the χ-half
of `IsGalCompatible` from the cyclotomic structural facts alone. -/
theorem residueChar_pow_ringHomComp_eq_of_algEquiv
    (a : ℕ) (f : R' ≃ₐ[K] R') :
    (S.residueChar ^ a).ringHomComp (f : R' →+* R') = S.residueChar ^ a :=
  S.residueChar_pow_ringHomComp_eq_of_fixes_zeta_p a (f : R' →+* R')
    (S.algEquiv_fixes_zeta_p f)

omit [IsScalarTower ℤ (𝓞 K) (𝓞 R')] in
/-- Final reduction of `IsGalCompatible` to the psi-shift hypothesis
(no longer requires the zeta_p-fix hypothesis). -/
theorem isGalCompatible_of_psi_shift_only
    (a : ℕ)
    (h_psi : ∀ f : R' ≃ₐ[K] R', ∃ a' : kˣ,
      (f : R' →+* R').toMonoidHom.compAddChar S.psi =
        AddChar.mulShift S.psi a') :
    S.IsGalCompatible a := by
  intro f
  obtain ⟨a', hψ⟩ := h_psi f
  exact ⟨a', S.residueChar_pow_ringHomComp_eq_of_algEquiv a f, hψ⟩

/-- The psi-shift compatibility predicate. This isolates the genuine
open content for `IsGalCompatible` once the cyclotomic structural
χ-fixedness has been discharged. -/
def IsGalPsiShiftCompatible : Prop :=
  ∀ f : R' ≃ₐ[K] R', ∃ a' : kˣ,
    (f : R' →+* R').toMonoidHom.compAddChar S.psi =
      AddChar.mulShift S.psi a'

omit [IsScalarTower ℤ (𝓞 K) (𝓞 R')] in
/-- The psi-shift compatibility implies `IsGalCompatible a` for every a. -/
theorem isGalCompatible_of_isGalPsiShiftCompatible
    (a : ℕ) (h : S.IsGalPsiShiftCompatible) :
    S.IsGalCompatible a :=
  S.isGalCompatible_of_psi_shift_only a h

omit [IsScalarTower ℤ (𝓞 K) (𝓞 R')] in
/-- From `IsGalCompatible` and the standard Galois conditions, the
field-level Galois fixedness condition holds — and so does
`IsGalDescentTo_OK`. -/
theorem isGalDescentTo_OK_of_galCompatible
    [IsGalois K R'] [FiniteDimensional K R']
    (a : ℕ) (h : S.IsGalCompatible a) :
    S.IsGalDescentTo_OK a := by
  apply S.isGalDescentTo_OK_of_galois_fixed a
  intro f
  obtain ⟨a', hσχ, hσψ⟩ := h f
  exact S.algebraMap_gaussSumInt_pow_p_invariant a (f : R' →+* R') hσχ hσψ

/-- Galois-invariance descent of `gaussSumInt a ^ p`: given a
`γ ∈ 𝓞 K` whose image is `gaussSumInt a ^ p`, we get
`γ ∈ S.descentPrime^?` for the right exponent. (For now we use the
`^ p` step-2 statement and divide by `e`; in general we'd want the
exact-order step-2 statement and a divisibility argument.) -/
theorem gaussSumInt_pow_descentPrime_pow_of_galois_descent
    [FaithfulSMul (𝓞 K) (𝓞 R')]
    [Module.IsTorsionFree (𝓞 K) (𝓞 R')]
    {a : ℕ} (ha₁ : 1 ≤ a) (ha₂ : a ≤ p - 1)
    {γ : 𝓞 K} (hγ_ne : γ ≠ 0)
    (hγ : algebraMap (𝓞 K) (𝓞 R') γ = S.gaussSumInt a ^ p)
    {n : ℕ} (hn : S.descentRamificationIdx * n ≤ p) :
    γ ∈ S.descentPrime ^ n := by
  -- Step 2: gaussSumInt a ^ p ∈ Q^p.
  have h_step2 : S.gaussSumInt a ^ p ∈ S.Q ^ p :=
    S.gaussSumInt_pow_mem_Q_pow ha₁ ha₂
  -- Lift to algebraMap γ ∈ Q^p.
  have h_image : algebraMap (𝓞 K) (𝓞 R') γ ∈ S.Q ^ p := hγ ▸ h_step2
  -- Q^p ≤ Q^(e*n) when e*n ≤ p.
  have h_pow_le : S.Q ^ p ≤ S.Q ^ (S.descentRamificationIdx * n) :=
    Ideal.pow_le_pow_right hn
  have h_image' :
      algebraMap (𝓞 K) (𝓞 R') γ ∈ S.Q ^ (S.descentRamificationIdx * n) :=
    h_pow_le h_image
  -- Apply the iff.
  exact (S.mem_descentPrime_pow_iff_algebraMap_mem_Q_pow_mul hγ_ne n).mpr h_image'

/-- Galois descent maximum: when supplied with the descent witness γ,
γ ∈ S.descentPrime^(p / e) (using Nat division). -/
theorem gaussSumInt_pow_descentPrime_pow_div_of_galois_descent
    [FaithfulSMul (𝓞 K) (𝓞 R')]
    [Module.IsTorsionFree (𝓞 K) (𝓞 R')]
    {a : ℕ} (ha₁ : 1 ≤ a) (ha₂ : a ≤ p - 1)
    {γ : 𝓞 K} (hγ_ne : γ ≠ 0)
    (hγ : algebraMap (𝓞 K) (𝓞 R') γ = S.gaussSumInt a ^ p) :
    γ ∈ S.descentPrime ^ (p / S.descentRamificationIdx) := by
  apply S.gaussSumInt_pow_descentPrime_pow_of_galois_descent ha₁ ha₂ hγ_ne hγ
  -- Goal: e * (p / e) ≤ p. Standard: Nat.div_mul_le_self gives p / e * e ≤ p.
  rw [mul_comm]
  exact Nat.div_mul_le_self p S.descentRamificationIdx

/-- **End-to-end descent assembly.** Given `IsGalCompatible`, `IsGalois K R'`,
`FiniteDimensional K R'`, and the standard step-2 hypotheses, the bundle
produces a γ ∈ 𝓞 K with `γ ∈ S.descentPrime^(p / e)`. -/
theorem exists_descentPrime_pow_div_of_galCompatible
    [IsGalois K R'] [FiniteDimensional K R']
    [FaithfulSMul (𝓞 K) (𝓞 R')]
    [Module.IsTorsionFree (𝓞 K) (𝓞 R')]
    {a : ℕ} (ha₁ : 1 ≤ a) (ha₂ : a ≤ p - 1)
    (h : S.IsGalCompatible a)
    (h_ne_zero : S.gaussSumInt a ^ p ≠ 0) :
    ∃ γ : 𝓞 K, γ ≠ 0 ∧
      algebraMap (𝓞 K) (𝓞 R') γ = S.gaussSumInt a ^ p ∧
      γ ∈ S.descentPrime ^ (p / S.descentRamificationIdx) := by
  -- Apply IsGalCompatible to get IsGalDescentTo_OK.
  obtain ⟨γ, hγ⟩ := S.isGalDescentTo_OK_of_galCompatible a h
  have hγ_ne : γ ≠ 0 := by
    intro hγ_zero
    rw [hγ_zero, map_zero] at hγ
    exact h_ne_zero hγ.symm
  refine ⟨γ, hγ_ne, hγ, ?_⟩
  exact S.gaussSumInt_pow_descentPrime_pow_div_of_galois_descent ha₁ ha₂ hγ_ne hγ

/-- **End-to-end descent assembly from psi-shift only.** Given:
* `IsGalois K R'`, `FiniteDimensional K R'` (cyclotomic structural),
* `FaithfulSMul (𝓞 K) (𝓞 R')`, `Module.IsTorsionFree (𝓞 K) (𝓞 R')`
  (number-field structural),
* the standard step-2 hypotheses (1 ≤ a ≤ p-1, gaussSumInt^p ≠ 0),
* the genuine psi-shift hypothesis,
the bundle produces a γ ∈ 𝓞 K nonzero with `algebraMap γ = gaussSumInt^p`
and `γ ∈ S.descentPrime^(p / e)`. This is the c.1.4 conclusion modulo
the psi-shift content alone. -/
theorem exists_descentPrime_pow_div_of_psi_shift
    [IsGalois K R'] [FiniteDimensional K R']
    [FaithfulSMul (𝓞 K) (𝓞 R')]
    [Module.IsTorsionFree (𝓞 K) (𝓞 R')]
    {a : ℕ} (ha₁ : 1 ≤ a) (ha₂ : a ≤ p - 1)
    (h_psi : ∀ f : R' ≃ₐ[K] R', ∃ a' : kˣ,
      (f : R' →+* R').toMonoidHom.compAddChar S.psi =
        AddChar.mulShift S.psi a')
    (h_ne_zero : S.gaussSumInt a ^ p ≠ 0) :
    ∃ γ : 𝓞 K, γ ≠ 0 ∧
      algebraMap (𝓞 K) (𝓞 R') γ = S.gaussSumInt a ^ p ∧
      γ ∈ S.descentPrime ^ (p / S.descentRamificationIdx) :=
  S.exists_descentPrime_pow_div_of_galCompatible ha₁ ha₂
    (S.isGalCompatible_of_psi_shift_only a h_psi) h_ne_zero

/-- **End-to-end descent assembly with cyclotomic Galois instances
synthesized.** Drops the IsGalois / FiniteDimensional / FaithfulSMul /
IsTorsionFree hypotheses by deriving them from the cyclotomic structure.
The remaining hypotheses are step-2 + the psi-shift content. -/
theorem exists_descentPrime_pow_div_cyclotomic
    {a : ℕ} (ha₁ : 1 ≤ a) (ha₂ : a ≤ p - 1)
    (h_psi : ∀ f : R' ≃ₐ[K] R', ∃ a' : kˣ,
      (f : R' →+* R').toMonoidHom.compAddChar S.psi =
        AddChar.mulShift S.psi a')
    (h_ne_zero : S.gaussSumInt a ^ p ≠ 0) :
    ∃ γ : 𝓞 K, γ ≠ 0 ∧
      algebraMap (𝓞 K) (𝓞 R') γ = S.gaussSumInt a ^ p ∧
      γ ∈ S.descentPrime ^ (p / S.descentRamificationIdx) := by
  haveI := isGalois_K_R'_of_cyclotomic S
  haveI := finiteDimensional_K_R'_of_cyclotomic S
  haveI := faithfulSMul_OK_OR'_of_cyclotomic S
  exact S.exists_descentPrime_pow_div_of_psi_shift ha₁ ha₂ h_psi h_ne_zero

/-- **End-to-end descent assembly with single Prop predicate hypothesis.**
Phrases the c.1.4-mod-bundle-constructor closure as: given step-2
hypotheses + `IsGalPsiShiftCompatible`, produce the descent. -/
theorem exists_descentPrime_pow_div_of_isGalPsiShiftCompatible
    {a : ℕ} (ha₁ : 1 ≤ a) (ha₂ : a ≤ p - 1)
    (h : S.IsGalPsiShiftCompatible)
    (h_ne_zero : S.gaussSumInt a ^ p ≠ 0) :
    ∃ γ : 𝓞 K, γ ≠ 0 ∧
      algebraMap (𝓞 K) (𝓞 R') γ = S.gaussSumInt a ^ p ∧
      γ ∈ S.descentPrime ^ (p / S.descentRamificationIdx) :=
  S.exists_descentPrime_pow_div_cyclotomic ha₁ ha₂ h h_ne_zero

/-! ### Non-vanishing helper

In a domain `𝓞 R'`, `x ^ p ≠ 0 ↔ x ≠ 0` (since p ≥ 1). The bundle's
step-2 always gives `gaussSumInt a ∈ S.Q`, but we need a direct
non-vanishing witness for the descent assembly. This is provided as
a helper. -/

omit [IsScalarTower ℤ (𝓞 K) (𝓞 R')] in
/-- `gaussSumInt a ^ p ≠ 0` whenever `gaussSumInt a ≠ 0`. -/
theorem gaussSumInt_pow_p_ne_zero_of_ne_zero {a : ℕ} (h : S.gaussSumInt a ≠ 0) :
    S.gaussSumInt a ^ p ≠ 0 :=
  pow_ne_zero p h

omit [IsScalarTower ℤ (𝓞 K) (𝓞 R')] in
/-- `gaussSumInt a ≠ 0` whenever the bundle's step-2 EXACT-order witness
gives `gaussSumInt a ∉ S.Q^(d+1)` for some d. (Since 0 ∈ Q^(d+1).) -/
theorem gaussSumInt_ne_zero_of_not_mem_Q_pow_succ
    {a d : ℕ} (h : S.gaussSumInt a ∉ S.Q ^ (d + 1)) :
    S.gaussSumInt a ≠ 0 := by
  intro h_zero
  apply h
  rw [h_zero]
  exact (S.Q ^ (d + 1)).zero_mem

end ConcreteStickelbergerSetup

end Furtwaengler

end BernoulliRegular

end
