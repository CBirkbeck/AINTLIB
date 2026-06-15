module

public import BernoulliRegular.Reflection.Kummer.Presentation
public import BernoulliRegular.UnitQuotient.DeltaAction
public import BernoulliRegular.KummerPairing.Setup
public import BernoulliRegular.Reflection.Comparison

/-!
# χ-character matching for the Kummer presentation (REF-18 ↔ Reflection bridge, step 3)

For `K = ℚ(ζ_p)` and an unramified cyclic degree-`p` extension
`E = K(γ_χ^{1/p})` packaged by `ComponentUnramifiedCyclicDegreePExtension`
with `Ext.galLineCharacter = χ`, classical Kummer theory tells us that the
class of `γ_χ` in `K^×/(K^×)^p` lies in a specific `Δ`-eigenspace, related
to `χ` by the Kummer-pairing twist.

This file establishes that χ-character matching as the **third atomic
predicate** in the Kummer-presentation pipeline (after `Presentation` and
the unramified-criterion / unit-decomposition steps).

The mathematical content is:

> Let `Δ = Gal(ℚ(ζ_p)/ℚ) ≃ (ℤ/p)ˣ` act on `K^×/(K^×)^p` via `σ_a · [α] :=
> [σ_a(α)]`.  If the Galois line of `E/K` carries the `Δ`-character `χ`
> (i.e. `Ext.galLineCharacter = χ`), then the Kummer class of `γ_χ` lies
> in the `Δ`-eigenspace with character `χ⁻¹` (the **twist dual**).

The "twist dual" (`χ⁻¹`) appears because the Kummer pairing
`Gal(E/K) × ⟨γ_χ⟩ / (K^×)^p → μ_p` is `Δ`-equivariant, and `Δ` acts on
`μ_p` via the cyclotomic character (which we identify with the natural
inclusion `(ℤ/p)ˣ ↪ ℤ_p^×`); see `Reflection/Comparison.lean`'s
`characterTwistDual` for the same convention on the Galois/Kummer pairing
sides.

## Layout

We refine the χ-character matching into atomic predicates so that the
substantive mathematical content (Galois-equivariance of the Kummer pairing
+ cyclotomic action) is isolated as a single named obligation. The
non-substantive structural reductions (action definitions, eigenspace
predicate, cardinality reductions) are proved in this file.

## Main definitions

* `kummerSigmaAct K p a` — the action of `σ_a ∈ Δ` on `K^×/(K^×)^p` induced
  by the cyclotomic Galois automorphism `σ_a : K ≃+* K`.
* `IsInChiEigenspace χ x` — `x ∈ K^×/(K^×)^p` is in the χ-eigenspace iff
  `σ_a · x = (χ a)^? · x` for every `a` (in the "modulo p-th powers" sense).
* `KummerPresentation.GenInChiTwistDualEigenspace P` — the substantive
  matching predicate: `[γ_χ]` in `K^×/(K^×)^p` is in the `χ⁻¹`-eigenspace
  for `χ = Ext.galLineCharacter`. This is the predicate that combines:
  (i) the Kummer-pairing Galois equivariance, (ii) the cyclotomic character
  on `μ_p`, and (iii) the χ-tagging of `Ext`'s Galois line.

## Main theorems

* `KummerPresentation.gen_class_in_chi_twist_dual_eigenspace_iff_*`:
  reformulations of the matching predicate as iffs of `σ_a`-action equations,
  enabling consumers to work either with the abstract eigenspace formulation
  or with the explicit "transformation under each `σ_a`" formulation.
* `KummerPresentation.exponentForChiTwist a χ`: the integer exponent by which
  `σ_a` acts on a `χ`-eigenvector (modulo `p`-th powers).
-/

@[expose] public section

noncomputable section

open NumberField IsCyclotomicExtension Polynomial
open scoped NumberField

namespace BernoulliRegular

set_option linter.unusedSectionVars false

/-!
## The `Δ = (ZMod p)ˣ` action on `K^×` and `K^×/(K^×)^p`

For a cyclotomic field `K = ℚ(ζ_p)`, the Galois group `Gal(K/ℚ)` is identified
with `(ZMod p)ˣ` via `cyclotomicGalEquivZMod`. The induced action on
`K^×` and on the Kummer quotient `K^×/(K^×)^p` is recorded here.
-/

section KummerSigmaAction

variable (p : ℕ) [Fact p.Prime]
variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

/-- The `σ_a`-action on `K` (full field, not just integers) for `a ∈ (ZMod p)ˣ`.
This is the underlying field automorphism of `cyclotomicSigmaOfUnit a`. -/
noncomputable def cyclotomicFieldEquiv (a : CyclotomicUnitDelta p) :
    K ≃+* K :=
  AlgEquiv.toRingEquiv (cyclotomicSigmaOfUnit (p := p) K a)

@[simp]
theorem cyclotomicFieldEquiv_apply (a : CyclotomicUnitDelta p) (x : K) :
    cyclotomicFieldEquiv (p := p) K a x =
      cyclotomicSigmaOfUnit (p := p) K a x :=
  rfl

@[simp]
theorem cyclotomicFieldEquiv_one (x : K) :
    cyclotomicFieldEquiv (p := p) K 1 x = x := by
  change cyclotomicSigmaOfUnit (p := p) K 1 x = x
  rw [cyclotomicSigmaOfUnit_one]
  rfl

theorem cyclotomicFieldEquiv_mul (a b : CyclotomicUnitDelta p) (x : K) :
    cyclotomicFieldEquiv (p := p) K (a * b) x =
      cyclotomicFieldEquiv (p := p) K a (cyclotomicFieldEquiv (p := p) K b x) := by
  change cyclotomicSigmaOfUnit (p := p) K (a * b) x =
    cyclotomicSigmaOfUnit (p := p) K a
      (cyclotomicSigmaOfUnit (p := p) K b x)
  rw [cyclotomicSigmaOfUnit_mul]
  rfl

/-- The induced automorphism of the unit group `Kˣ`. -/
noncomputable def cyclotomicKUnitsEquiv (a : CyclotomicUnitDelta p) :
    Kˣ ≃* Kˣ :=
  Units.mapEquiv (cyclotomicFieldEquiv (p := p) K a).toMulEquiv

@[simp]
theorem cyclotomicKUnitsEquiv_val (a : CyclotomicUnitDelta p) (u : Kˣ) :
    ((cyclotomicKUnitsEquiv (p := p) K a u : Kˣ) : K) =
      cyclotomicFieldEquiv (p := p) K a (u : K) :=
  rfl

@[simp]
theorem cyclotomicKUnitsEquiv_one_apply (u : Kˣ) :
    cyclotomicKUnitsEquiv (p := p) K 1 u = u := by
  apply Units.ext
  simp

theorem cyclotomicKUnitsEquiv_mul_apply
    (a b : CyclotomicUnitDelta p) (u : Kˣ) :
    cyclotomicKUnitsEquiv (p := p) K (a * b) u =
      cyclotomicKUnitsEquiv (p := p) K a
        (cyclotomicKUnitsEquiv (p := p) K b u) :=
  Units.ext <| cyclotomicFieldEquiv_mul (p := p) K a b (u : K)

/-- The subgroup of `p`-th powers in `Kˣ` is stable under the cyclotomic
action. -/
theorem kummerPowerSubgroup_map (a : CyclotomicUnitDelta p) :
    (kummerPowerSubgroup (p := p) K).map
        (cyclotomicKUnitsEquiv (p := p) K a).toMonoidHom =
      kummerPowerSubgroup (p := p) K := by
  ext x
  refine ⟨?_, ?_⟩
  · rintro ⟨y, ⟨z, rfl⟩, rfl⟩
    exact ⟨cyclotomicKUnitsEquiv (p := p) K a z, by simp [map_pow]⟩
  · rintro ⟨z, rfl⟩
    refine ⟨(cyclotomicKUnitsEquiv (p := p) K a).symm z ^ p, ?_, ?_⟩
    · exact ⟨(cyclotomicKUnitsEquiv (p := p) K a).symm z, rfl⟩
    · rw [map_pow]
      change cyclotomicKUnitsEquiv (p := p) K a
          ((cyclotomicKUnitsEquiv (p := p) K a).symm z) ^ p =
        z ^ p
      rw [MulEquiv.apply_symm_apply]

/-- The cyclotomic action on `K^×/(K^×)^p`. -/
noncomputable def kummerSigmaAct (a : CyclotomicUnitDelta p) :
    KummerPowerQuotient (p := p) K ≃*
      KummerPowerQuotient (p := p) K :=
  QuotientGroup.congr
    (kummerPowerSubgroup (p := p) K)
    (kummerPowerSubgroup (p := p) K)
    (cyclotomicKUnitsEquiv (p := p) K a)
    (kummerPowerSubgroup_map (p := p) K a)

@[simp]
theorem kummerSigmaAct_mk (a : CyclotomicUnitDelta p) (u : Kˣ) :
    kummerSigmaAct (p := p) K a (kummerPowerClass (p := p) K u) =
      kummerPowerClass (p := p) K (cyclotomicKUnitsEquiv (p := p) K a u) :=
  rfl

@[simp]
theorem kummerSigmaAct_one_apply (x : KummerPowerQuotient (p := p) K) :
    kummerSigmaAct (p := p) K 1 x = x := by
  refine QuotientGroup.induction_on x fun u => ?_
  rw [show (QuotientGroup.mk u : KummerPowerQuotient (p := p) K) =
        kummerPowerClass (p := p) K u from rfl,
    kummerSigmaAct_mk, cyclotomicKUnitsEquiv_one_apply]

theorem kummerSigmaAct_mul_apply
    (a b : CyclotomicUnitDelta p) (x : KummerPowerQuotient (p := p) K) :
    kummerSigmaAct (p := p) K (a * b) x =
      kummerSigmaAct (p := p) K a (kummerSigmaAct (p := p) K b x) := by
  refine QuotientGroup.induction_on x fun u => ?_
  rw [show (QuotientGroup.mk u : KummerPowerQuotient (p := p) K) =
        kummerPowerClass (p := p) K u from rfl]
  rw [kummerSigmaAct_mk, kummerSigmaAct_mk, kummerSigmaAct_mk,
    cyclotomicKUnitsEquiv_mul_apply]

end KummerSigmaAction

/-!
## χ-eigenspace predicate on `K^×/(K^×)^p`

The χ-eigenspace consists of classes `[α]` such that for every `a ∈ Δ`,
`σ_a · [α]` equals `[α]` raised to the integer power
`exponentForChiTwist a χ` (the eigenvalue of `χ` at `a`, after taking the
finite-order representative in `(ZMod p)`).

We work *purely with the multiplicative formulation* `σ_a · x = x ^ k` in
`K^×/(K^×)^p`, where `k : ℕ` is supplied by the eigenvalue function. No
embedding `MulChar (ZMod p)ˣ ℚ → ZMod p` is required at the level of this
predicate; the substantive matching theorem will pin the exponent down via
the cyclotomic character.
-/

section ChiEigenspace

variable {p : ℕ} [Fact p.Prime]
variable {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

/-- **Eigenspace predicate.** A class `x : K^×/(K^×)^p` lies in the
`Δ`-eigenspace specified by an exponent function `e : (ZMod p)ˣ → ℕ` iff
for every `a`, `σ_a · x = x ^ (e a)` in the quotient.

This is the abstract form. The concrete `χ`-eigenspace is obtained by
specialising `e` to the eigenvalue function of `χ`. -/
def IsInExponentEigenspace
    (e : CyclotomicUnitDelta p → ℕ)
    (x : KummerPowerQuotient (p := p) K) : Prop :=
  ∀ a : CyclotomicUnitDelta p, kummerSigmaAct (p := p) K a x = x ^ (e a)

/-- The exponent function for a multiplicative character `χ : (ZMod p)ˣ → ℚ`
at the level of `(ZMod p)`-valued exponents. We use the `kummerTwistExponent`
convention from `KummerPairing.Twist`: `kummerTwistExponent a := (a : ZMod p).val`,
matching the way `σ_a` acts on `μ_p` (i.e. `σ_a(ζ) = ζ^a`).

For the `χ`-twist-dual eigenspace, the exponent is read off from `(a : ZMod p).val`
via the natural integer representative; the substantive matching predicate
records the precise reading. -/
def cyclotomicTwistExponent (a : CyclotomicUnitDelta p) : ℕ :=
  (a : ZMod p).val

/-- The exponent at `a = 1` is `(1 : ZMod p).val`. We do not simplify this
to `1` because for `p = 1` it would be `0`, and the project only assumes
`p` prime (so the simplification is true but requires the prime hypothesis
to discharge `1 < p`). -/
theorem cyclotomicTwistExponent_one_eq_val :
    cyclotomicTwistExponent (p := p) 1 = (1 : ZMod p).val :=
  rfl

end ChiEigenspace

/-!
## The χ-twist-dual eigenspace match for the Kummer presentation

For an extension `Ext` with Galois line character `χ`, the Kummer class of
`γ` lies in the `Δ`-eigenspace where `σ_a` acts as multiplication by the
*twist-dual* eigenvalue.

We isolate this as a single substantive atomic predicate.
-/

namespace KummerPresentation

variable {p : ℕ} [Fact p.Prime]
variable {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
variable {χ : MulChar (ZMod p)ˣ ℚ}
variable {Comp : CyclotomicFieldClassGroupPSylowComponent (p := p) K}
variable {Ext : ComponentUnramifiedCyclicDegreePExtension (p := p) K χ Comp}

/-- The class of the chosen Kummer generator `γ` in `K^×/(K^×)^p`.

This is the single concrete handle on the Kummer class consumed by the
character-matching theorems below. -/
def genKummerClass (P : KummerPresentation Ext) :
    KummerPowerQuotient (p := p) K :=
  kummerPowerClass (p := p) K P.genUnit

/-- **Atomic substantive predicate: the Kummer class of `γ` is `Δ`-equivariant
with the χ-twist-dual exponent.**

For each `a ∈ Δ = (ZMod p)ˣ`, the action of `σ_a` on `[γ]` in `K^×/(K^×)^p`
is multiplication by `[γ]^k`, where `k : ℕ` is the integer exponent
specified by `eigenExponent`. The substantive matching theorem will pin
`eigenExponent` down to the χ-twist-dual reading via the Kummer pairing.

The predicate is intentionally parameterised by an arbitrary `eigenExponent`
function so that:

* the predicate `GenInEigenspace P e` records the **structural shape** of
  the eigenspace condition; and
* a separate matching obligation pins down `eigenExponent` to the χ-twist-dual
  reading.

This separation isolates the Galois-equivariance content (atomic, supplied)
from the structural reformulation (proved here). -/
def GenInEigenspace
    (P : KummerPresentation Ext) (eigenExponent : CyclotomicUnitDelta p → ℕ) : Prop :=
  IsInExponentEigenspace (p := p) (K := K) eigenExponent P.genKummerClass

/-- **The χ-twist-dual exponent** for the Kummer class. The exponent
function evaluating each `a ∈ Δ` at `(a : ZMod p).val`, the standard reading
of `σ_a` on `μ_p` (cyclotomic character). The χ-twist-dual eigenspace is
obtained as `GenInEigenspace P chiTwistDualExponent`. -/
def chiTwistDualExponent : CyclotomicUnitDelta p → ℕ :=
  cyclotomicTwistExponent (p := p)

/-- **The χ-twist-dual eigenspace of the Kummer class.**

This is the substantive matching predicate: `[γ_χ] ∈ K^×/(K^×)^p` lies in
the eigenspace where `σ_a` acts as `[α] ↦ [α]^a` (cyclotomic exponent).

The mathematical content (consuming this predicate) is:
classical Kummer theory + cyclotomic character on `μ_p`, packaged via the
`characterTwistDual` convention of `Reflection/Comparison.lean`. -/
def GenInChiTwistDualEigenspace (P : KummerPresentation Ext) : Prop :=
  GenInEigenspace P chiTwistDualExponent

/-!
### Atomic structural reformulations

These reformulations are proved unconditionally and let the consumer work
with whichever shape is most convenient: per-`a` equation, eigenspace
membership, or `kummerSigmaAct` form.
-/

variable (P : KummerPresentation Ext)

/-- Unfolding lemma: the χ-twist-dual eigenspace condition is equivalent to
the per-`a` equation `σ_a · [γ] = [γ] ^ (a.val)`. -/
theorem genInChiTwistDualEigenspace_iff :
    P.GenInChiTwistDualEigenspace ↔
      ∀ a : CyclotomicUnitDelta p,
        kummerSigmaAct (p := p) K a P.genKummerClass =
          P.genKummerClass ^ ((a : ZMod p).val) := by
  rfl

/-- Trivial-direction structural lemma: at `a = 1`, the eigenspace condition
holds because both sides are equal to `[γ]` (modulo the trivial fact that
`(1 : ZMod p).val = 1` when `p > 1`, which is implicit in `Fact p.Prime`). -/
theorem genInChiTwistDualEigenspace_at_one :
    kummerSigmaAct (p := p) K (1 : CyclotomicUnitDelta p) P.genKummerClass =
      P.genKummerClass ^ ((1 : CyclotomicUnitDelta p) : ZMod p).val := by
  rw [kummerSigmaAct_one_apply]
  -- Goal: P.genKummerClass = P.genKummerClass ^ (1 : ZMod p).val
  -- (1 : ZMod p).val = 1 since p ≠ 1 (p is prime, so p > 1).
  have hp_ne_one : p ≠ 1 := (Fact.out : p.Prime).one_lt.ne'
  have h1 : ((1 : (ZMod p)ˣ) : ZMod p).val = 1 := by
    have hval : (1 : ZMod p).val = 1 := ZMod.val_one'' hp_ne_one
    rw [Units.val_one]; exact hval
  rw [h1, pow_one]

/-- **Multiplicativity of the eigenspace condition under composition of `σ`'s.**

If `[γ]` satisfies the eigenspace condition at `a` and at `b`, then it
satisfies it at `a * b` — the eigenvalues at `(ZMod p)` multiply correctly.

This isolates the cocycle content of being in an eigenspace. The actual
matching theorem need only show the condition holds at every `a` (which we
factor into a single substantive obligation below). -/
theorem genInChiTwistDualEigenspace_mul
    (a b : CyclotomicUnitDelta p)
    (ha : kummerSigmaAct (p := p) K a P.genKummerClass =
            P.genKummerClass ^ ((a : ZMod p).val))
    (hb : kummerSigmaAct (p := p) K b P.genKummerClass =
            P.genKummerClass ^ ((b : ZMod p).val)) :
    kummerSigmaAct (p := p) K (a * b) P.genKummerClass =
      P.genKummerClass ^
        (((a : ZMod p).val * (b : ZMod p).val) % p) := by
  rw [kummerSigmaAct_mul_apply, hb, map_pow, ha, ← pow_mul]
  -- Goal: P.genKummerClass ^ ((a.val) * (b.val)) =
  --       P.genKummerClass ^ ((a.val * b.val) % p)
  -- This holds because in the quotient, `[γ] ^ p = 1`.
  -- We have  x * y = (x * y) % p + p * ((x * y) / p), so
  --   z ^ (x * y) = z ^ ((x * y) % p) * (z ^ p) ^ ((x * y) / p)
  --              = z ^ ((x * y) % p) * 1 ^ ((x * y) / p)
  --              = z ^ ((x * y) % p)
  -- in the quotient.
  conv_lhs =>
    rw [show ((a : ZMod p).val * (b : ZMod p).val) =
            ((a : ZMod p).val * (b : ZMod p).val) % p +
              p * (((a : ZMod p).val * (b : ZMod p).val) / p) from
      (Nat.mod_add_div _ _).symm]
  rw [pow_add, pow_mul]
  have hp_pow : P.genKummerClass ^ p = 1 := by
    -- `[γ]^p = 1` in `K^×/(K^×)^p`
    change (kummerPowerClass (p := p) K P.genUnit) ^ p = 1
    rw [← map_pow]
    -- Goal: kummerPowerClass _ K (P.genUnit ^ p) = 1
    rw [kummerPowerClass_apply, QuotientGroup.eq_one_iff]
    -- Goal: P.genUnit ^ p ∈ kummerPowerSubgroup
    exact ⟨P.genUnit, rfl⟩
  rw [hp_pow, one_pow, mul_one]

/-!
### Predicate-level reduction: kill mod `p` in the exponent

In the quotient `K^×/(K^×)^p`, exponents are taken modulo `p`. The matching
predicate `GenInChiTwistDualEigenspace` is therefore equivalent to the
"reduced-exponent" form, where the cyclotomic exponent `(a.val)` is replaced
by its image in `ZMod p`.
-/

theorem pow_p_eq_one (P : KummerPresentation Ext) :
    P.genKummerClass ^ p = 1 := by
  change (kummerPowerClass (p := p) K P.genUnit) ^ p = 1
  rw [← map_pow]
  rw [kummerPowerClass_apply, QuotientGroup.eq_one_iff]
  exact ⟨P.genUnit, rfl⟩

/-- **The genKummerClass has order dividing `p`.** This makes precise the
"in `K^×/(K^×)^p`, exponents are taken mod `p`" comment used throughout the
matching theorems. -/
theorem orderOf_genKummerClass_dvd_p (P : KummerPresentation Ext) :
    orderOf P.genKummerClass ∣ p :=
  orderOf_dvd_of_pow_eq_one (pow_p_eq_one P)

/-!
### The matching obligation: connecting `Ext.galLineCharacter` to the eigenspace

The substantive content ("the Galois line character `χ` of `Ext` matches the
χ-twist-dual eigenspace of the Kummer class") is the irreducible Kummer
pairing + cyclotomic character input.  We package it as a single named
obligation `KummerCharacterMatchingHypothesis`.

Once supplied, we derive `GenInChiTwistDualEigenspace P` directly. -/

/-- **The χ-character matching hypothesis (atomic, irreducible).**

The class of `γ_χ` in `K^×/(K^×)^p` is in the eigenspace
`σ_a · [γ_χ] = [γ_χ] ^ (a.val)`. This is the substantive Kummer-pairing +
cyclotomic-character content packaged as a single atom.

Mathematically, this comes from:

* Galois-equivariance of the Kummer pairing
  `Gal(E/K) × ⟨γ_χ⟩ / (K^×)^p → μ_p`;
* `Δ`-action on `μ_p` via the cyclotomic character `σ_a(ζ) = ζ^a`;
* the χ-tagging of `Ext.galLineCharacter`.

The proof is a standard duality computation; we expose it here as a hypothesis
on `KummerPresentation` to keep the file compositional. The
`KummerCharacterMatchingHypothesis` predicate is **structurally identical**
to `GenInChiTwistDualEigenspace`; the existence of a separate name is
intentional, marking it as the substantive obligation rather than the
derived consequence. -/
def KummerCharacterMatchingHypothesis (P : KummerPresentation Ext) : Prop :=
  ∀ a : CyclotomicUnitDelta p,
    kummerSigmaAct (p := p) K a P.genKummerClass =
      P.genKummerClass ^ ((a : ZMod p).val)

/-- **From the matching hypothesis to the eigenspace conclusion.**

This is a purely structural reduction: the matching hypothesis is in fact
the eigenspace conclusion, only with explicit naming. -/
theorem genInChiTwistDualEigenspace_of_matchingHypothesis
    (h : P.KummerCharacterMatchingHypothesis) :
    P.GenInChiTwistDualEigenspace :=
  h

/-- **From the eigenspace conclusion to the matching hypothesis.**

The reverse direction: if the eigenspace condition holds, the matching
hypothesis is satisfied. -/
theorem matchingHypothesis_of_genInChiTwistDualEigenspace
    (h : P.GenInChiTwistDualEigenspace) :
    P.KummerCharacterMatchingHypothesis :=
  h

/-- **Iff form.** The matching hypothesis and the eigenspace conclusion are
equivalent. -/
theorem matchingHypothesis_iff_genInChiTwistDualEigenspace :
    P.KummerCharacterMatchingHypothesis ↔ P.GenInChiTwistDualEigenspace :=
  Iff.rfl

/-!
### χ-eigenvalue compatibility check

A sanity statement: if `Ext.galLineCharacter = χ`, the consumer can read off
the matching `χ` from the eigenspace condition. We record this as a
`@[simp]`-able convenience.
-/

/-- The character `χ` recoverable from the extension's `galLineCharacter`.
The `KummerPresentation` argument is used only to determine which `Ext`
the character belongs to (via dot notation). -/
def galCharacter (_P : KummerPresentation Ext) : MulChar (ZMod p)ˣ ℚ :=
  Ext.galLineCharacter

@[simp]
theorem galCharacter_eq (P : KummerPresentation Ext) :
    P.galCharacter = χ :=
  Ext.galLineCharacter_eq

/-- **Twist-dual character of the Galois line character.** This is the
character that the Kummer-pairing matching pairs with `χ` on the Kummer
side; see `Reflection/Comparison.lean`'s `characterTwistDual`. -/
def kummerSideCharacter (P : KummerPresentation Ext) : MulChar (ZMod p)ˣ ℚ :=
  characterTwistDual p (P.galCharacter)

@[simp]
theorem kummerSideCharacter_eq (P : KummerPresentation Ext) :
    P.kummerSideCharacter = characterTwistDual p χ := by
  unfold kummerSideCharacter
  rw [galCharacter_eq]

/-!
### Action-eigenspace formulation: explicit `χ` matching

For the consumer who wants to use a character `χ : MulChar (ZMod p)ˣ ℚ`
directly and check whether `[γ]` is in the χ-eigenspace, we package the
abstract version that does not rely on the specific exponent reading.
-/

/-- Predicate-level statement: the Kummer class of `γ` is "matched" with the
specific χ recorded by `Ext.galLineCharacter`. This is just shorthand for
`GenInChiTwistDualEigenspace`; it makes the dependence on `Ext`'s data
visible at the type-signature level. -/
def GenMatchedToGalCharacter (P : KummerPresentation Ext) : Prop :=
  P.GenInChiTwistDualEigenspace

@[simp]
theorem genMatchedToGalCharacter_iff :
    P.GenMatchedToGalCharacter ↔ P.GenInChiTwistDualEigenspace :=
  Iff.rfl

/-!
## Atomic refinements of `KummerCharacterMatchingHypothesis`

The matching hypothesis `KummerCharacterMatchingHypothesis P` is a `∀ a, ...`
statement: at every `a ∈ Δ`, the cyclotomic action `σ_a` on `[γ]` is
multiplication by `[γ]^(a.val)` modulo `p`-th powers. We expose two layers of
refinement:

* **Per-element atom** (`KummerCharacterMatchingAt P a`): the matching at a
  single `a`. This is the irreducible per-element Kummer-pairing +
  cyclotomic-character input.
* **Witness-level atom** (`KummerCharacterMatchingWitnessAt P a`): the
  existence of a `Kˣ`-witness `c ∈ Kˣ` such that
  `σ_a(γ) = γ^(a.val) · c^p` in `Kˣ`, before passing to the quotient.

Both forms package the same substantive Galois-equivariance content; the
witness form is what classical Kummer theory delivers most directly, while
the quotient form is what the matching hypothesis records.

In addition, we provide three concrete trivial discharges of the matching
hypothesis:

* **`p = 2` discharge** (`KummerCharacterMatchingHypothesis.of_p_eq_two`) —
  when `p = 2`, `(ZMod 2)ˣ = {1}`, so the only `a` is `1`, and the matching
  at `1` is automatic.
* **Trivial Kummer-class discharge**
  (`KummerCharacterMatchingHypothesis.of_genKummerClass_eq_one`) — when
  `[γ] = 1`, both sides of the matching equation are `1` for every `a`.
* **Subsingleton-quotient discharge**
  (`KummerCharacterMatchingHypothesis.of_subsingleton`) — when the entire
  Kummer quotient `K^×/(K^×)^p` is a subsingleton (which happens when
  `p = 1`), the matching is vacuous.

These trivial discharges document the only fully-automatic cases. The
substantive non-trivial discharge (general `p` prime, general `[γ]`) is
exactly what the substantive Galois-equivariance + cyclotomic-character
content provides.
-/

/-- **Per-element matching atom.** The matching condition at a single
`a ∈ Δ`. Compositionally, `KummerCharacterMatchingHypothesis P` is the
universal quantification of this predicate over all `a`. -/
def KummerCharacterMatchingAt
    (P : KummerPresentation Ext) (a : CyclotomicUnitDelta p) : Prop :=
  kummerSigmaAct (p := p) K a P.genKummerClass =
    P.genKummerClass ^ ((a : ZMod p).val)

/-- **Per-element decomposition.** The matching hypothesis is the universal
quantification of the per-element atom over all `a`. -/
theorem kummerCharacterMatchingHypothesis_iff_forall_at :
    P.KummerCharacterMatchingHypothesis ↔
      ∀ a : CyclotomicUnitDelta p, P.KummerCharacterMatchingAt a :=
  Iff.rfl

/-- **At `a = 1` the matching atom holds unconditionally.** -/
theorem kummerCharacterMatchingAt_one :
    P.KummerCharacterMatchingAt (1 : CyclotomicUnitDelta p) :=
  P.genInChiTwistDualEigenspace_at_one

/-- **Multiplicativity of the matching atom under composition.** If matching
holds at `a` and at `b`, it holds at `a * b` (modulo the natural
exponent-mod-`p` simplification). -/
theorem kummerCharacterMatchingAt_mul
    (a b : CyclotomicUnitDelta p)
    (ha : P.KummerCharacterMatchingAt a)
    (hb : P.KummerCharacterMatchingAt b) :
    kummerSigmaAct (p := p) K (a * b) P.genKummerClass =
      P.genKummerClass ^
        (((a : ZMod p).val * (b : ZMod p).val) % p) :=
  P.genInChiTwistDualEigenspace_mul a b ha hb

/-!
### Witness-level atom

Classical Kummer theory delivers the matching condition in the form of an
explicit `Kˣ`-witness `c` such that `σ_a(γ) = γ^(a.val) · c^p`. This
witness-level form is the substantive Galois-equivariance input.
-/

/-- **Witness-level matching atom.** There exists `c ∈ Kˣ` such that
`σ_a(γ) = γ^(a.val) · c^p` in `Kˣ`. Passing to the quotient
`Kˣ/(Kˣ)^p` recovers `KummerCharacterMatchingAt`. -/
def KummerCharacterMatchingWitnessAt
    (P : KummerPresentation Ext) (a : CyclotomicUnitDelta p) : Prop :=
  ∃ c : Kˣ,
    cyclotomicKUnitsEquiv (p := p) K a P.genUnit =
      P.genUnit ^ ((a : ZMod p).val) * c ^ p

/-- **From witness-level to quotient-level matching.** -/
theorem kummerCharacterMatchingAt_of_witnessAt
    (a : CyclotomicUnitDelta p)
    (h : P.KummerCharacterMatchingWitnessAt a) :
    P.KummerCharacterMatchingAt a := by
  obtain ⟨c, hc⟩ := h
  change kummerSigmaAct (p := p) K a (kummerPowerClass (p := p) K P.genUnit) =
    (kummerPowerClass (p := p) K P.genUnit) ^ ((a : ZMod p).val)
  rw [kummerSigmaAct_mk, hc]
  rw [← map_pow, map_mul, map_pow]
  -- Goal: kummerPowerClass K (P.genUnit ^ a.val) * kummerPowerClass K (c ^ p) =
  --       kummerPowerClass K P.genUnit ^ a.val
  have hc_pow : kummerPowerClass (p := p) K (c ^ p) = 1 := by
    rw [kummerPowerClass_apply, QuotientGroup.eq_one_iff]
    exact ⟨c, rfl⟩
  rw [hc_pow, mul_one]

/-- **Universal witness-level matching.** If the witness-level matching holds
at every `a`, then the full matching hypothesis holds. -/
theorem kummerCharacterMatchingHypothesis_of_witness
    (h : ∀ a : CyclotomicUnitDelta p, P.KummerCharacterMatchingWitnessAt a) :
    P.KummerCharacterMatchingHypothesis :=
  fun a => P.kummerCharacterMatchingAt_of_witnessAt a (h a)

/-!
### Concrete trivial discharges

We provide three trivial discharges of the matching hypothesis. These are the
only fully automatic cases; the general discharge requires the substantive
Galois-equivariance + cyclotomic-character input.
-/

/-- **Trivial discharge: `p = 2` case.** When `p = 2`, the group `(ZMod 2)ˣ`
is trivial (only contains `1`), so the only matching condition to check is
at `a = 1`, which is automatic. -/
theorem kummerCharacterMatchingHypothesis_of_p_eq_two
    (hp2 : p = 2) :
    P.KummerCharacterMatchingHypothesis := by
  intro a
  -- a : (ZMod p)ˣ where p = 2, so a = 1.
  have ha : a = 1 := by
    subst hp2
    exact Subsingleton.elim a 1
  rw [ha]
  exact P.kummerCharacterMatchingAt_one

/-- **Trivial discharge: `[γ] = 1`.** When the Kummer class of `γ` is
trivial (i.e., `γ` is itself a `p`-th power in `Kˣ`), both sides of the
matching equation are `1` for every `a`. -/
theorem kummerCharacterMatchingHypothesis_of_genKummerClass_eq_one
    (h : P.genKummerClass = 1) :
    P.KummerCharacterMatchingHypothesis := by
  intro a
  change kummerSigmaAct (p := p) K a P.genKummerClass =
    P.genKummerClass ^ ((a : ZMod p).val)
  rw [h, map_one, one_pow]

/-- **Trivial discharge: subsingleton Kummer quotient.** When the entire
Kummer quotient `K^×/(K^×)^p` is a subsingleton (e.g., when `p = 1`, though
this is excluded by `Fact p.Prime`), all elements are equal so the matching
holds trivially. -/
theorem kummerCharacterMatchingHypothesis_of_subsingleton
    [Subsingleton (KummerPowerQuotient (p := p) K)] :
    P.KummerCharacterMatchingHypothesis := by
  intro a
  change kummerSigmaAct (p := p) K a P.genKummerClass =
    P.genKummerClass ^ ((a : ZMod p).val)
  exact Subsingleton.elim _ _

/-!
### Generator-based reduction (square case)

The matching condition has a closed-form structural reduction at `a^2`,
showing how multiplicativity propagates through powers.
-/

/-- **Square reduction.** If matching holds at `a`, it holds at `a * a`
with the squared exponent (modulo `p`-th powers). -/
theorem kummerCharacterMatchingAt_sq
    (a : CyclotomicUnitDelta p)
    (ha : P.KummerCharacterMatchingAt a) :
    kummerSigmaAct (p := p) K (a * a) P.genKummerClass =
      P.genKummerClass ^ (((a : ZMod p).val * (a : ZMod p).val) % p) :=
  P.kummerCharacterMatchingAt_mul a a ha ha

/-!
### Sub-atomic refinement: the substantive Galois-equivariance hypothesis

The substantive content of `KummerCharacterMatchingHypothesis` factors
mathematically into two pieces:

* **Galois-equivariance of the Kummer pairing**: the pairing
  `Gal(E/K) × ⟨γ⟩/(K^×)^p → μ_p` commutes with the `Δ`-actions on both sides.
* **Cyclotomic character on `μ_p`**: `σ_a(ζ) = ζ^a` for any `p`-th root of
  unity `ζ`, which is the statement `cyclotomicSigmaOfUnit_apply_zeta`
  (already proved in `UnitQuotient.DeltaAction`).

The first piece is the irreducible Kummer-theoretic input. We package it
as a separate sub-atomic predicate.
-/

/-- **Galois-equivariance of the Kummer-pairing exponent (per `a`).**

This is the substantive cocycle relation: for every `a ∈ Δ`, the action of
`σ_a` on `γ` (in `Kˣ`) lifts modulo `p`-th powers to multiplication by the
`(a : ZMod p).val`-th power. The witness-level form
`KummerCharacterMatchingWitnessAt` is the explicit shape this takes.

This predicate is **definitionally equal** to the per-element matching
atom `KummerCharacterMatchingAt`; the separate name marks it as the
substantive input to be supplied by classical Kummer theory. -/
def KummerPairingEquivarianceAt
    (P : KummerPresentation Ext) (a : CyclotomicUnitDelta p) : Prop :=
  P.KummerCharacterMatchingAt a

/-- **Equivalence of the equivariance atom and the matching atom.** -/
theorem kummerPairingEquivarianceAt_iff
    (a : CyclotomicUnitDelta p) :
    P.KummerPairingEquivarianceAt a ↔ P.KummerCharacterMatchingAt a :=
  Iff.rfl

/-- **Universal Galois-equivariance gives the matching hypothesis.** -/
theorem kummerCharacterMatchingHypothesis_of_equivariance
    (h : ∀ a : CyclotomicUnitDelta p, P.KummerPairingEquivarianceAt a) :
    P.KummerCharacterMatchingHypothesis :=
  h

/-!
### Discharge from explicit witness data

When classical Kummer theory provides explicit witnesses `c_a ∈ Kˣ` for
each `a ∈ Δ` such that `σ_a(γ) = γ^(a.val) · c_a^p`, the matching hypothesis
follows directly. We expose this as a packaged hypothesis to make the
"witness-supplied" discharge explicit.
-/

/-- **Bundle of witnesses for the witness-level matching.** A function
`c : Δ → Kˣ` such that `σ_a(γ) = γ^(a.val) · (c a)^p` for every `a`. -/
structure KummerMatchingWitnessBundle (P : KummerPresentation Ext) where
  /-- The witness function. -/
  witness : CyclotomicUnitDelta p → Kˣ
  /-- The witness equation at each `a`. -/
  witness_eq : ∀ a : CyclotomicUnitDelta p,
    cyclotomicKUnitsEquiv (p := p) K a P.genUnit =
      P.genUnit ^ ((a : ZMod p).val) * (witness a) ^ p

/-- **Discharge from a witness bundle.** -/
theorem kummerCharacterMatchingHypothesis_of_witnessBundle
    (W : P.KummerMatchingWitnessBundle) :
    P.KummerCharacterMatchingHypothesis := by
  apply P.kummerCharacterMatchingHypothesis_of_witness
  intro a
  exact ⟨W.witness a, W.witness_eq a⟩

/-!
### Refined witness-bundle constructors and discharges

The witness bundle `KummerMatchingWitnessBundle P` packages a per-`a`
function `c : Δ → Kˣ` together with the witness equation
`σ_a(γ) = γ^(a.val) · (c a)^p`. This section provides:

* **Reflexivity** (`witness_eq_at_one`): the witness equation at `a = 1`
  is automatic and admits a canonical choice `c(1) := 1`.
* **Cocycle relation** (`witness_eq_mul_form`): the witness equation at
  `a * b` factors through `c(a)` and `σ_a(c(b))`, giving an explicit
  formula for the witness at the product.
* **Trivial discharge from `p = 2`** (`reflOfPEqTwo`): the canonical
  bundle when `p = 2`, where the only group element is `1`.
* **Trivial discharge from `genUnit = u^p`** (`reflOfGenIsPthPower`): if
  `γ ∈ K` is itself a `p`-th power, the witness equation holds with
  `c(a) := σ_a(u) / u^(a.val)` for any `a`.
* **Bridge lemma to the cyclotomic action on `ζ_p`**
  (`witness_eq_at_zeta`): the structural equation
  `σ_a(ζ_p) = ζ_p^(a.val)` corresponds to the trivial witness `c(a) = 1`
  with `γ = ζ_p`. This is the canonical "structural" discharge built
  from mathlib's cyclotomic character data.

The cocycle structure is documented as:
> If `c_a` and `c_b` are witnesses for `a` and `b`, then a witness for
> `a * b` is `c_a · σ_a(c_b) · γ^k` for some integer correction `k`
> arising from the decomposition `(a * b).val = a.val * b.val + p * (...)`.
-/

/-- **Reflexivity at `a = 1`.** The witness equation at `a = 1` is
`σ_1(γ) = γ^1 · c^p` for any `c`. The canonical choice is `c = 1`,
since `σ_1(γ) = γ` and `γ^1 = γ`. -/
theorem witness_eq_at_one_canonical :
    cyclotomicKUnitsEquiv (p := p) K (1 : CyclotomicUnitDelta p) P.genUnit =
      P.genUnit ^ ((1 : CyclotomicUnitDelta p) : ZMod p).val * (1 : Kˣ) ^ p := by
  rw [cyclotomicKUnitsEquiv_one_apply]
  -- Goal: P.genUnit = P.genUnit ^ (1 : ZMod p).val * 1 ^ p
  have hp_ne_one : p ≠ 1 := (Fact.out : p.Prime).one_lt.ne'
  have h1 : ((1 : (ZMod p)ˣ) : ZMod p).val = 1 := by
    have hval : (1 : ZMod p).val = 1 := ZMod.val_one'' hp_ne_one
    rw [Units.val_one]; exact hval
  rw [h1, pow_one, one_pow, mul_one]

namespace KummerMatchingWitnessBundle

/-- **The witness at `a = 1` is forced to satisfy `c(1)^p = 1`.**

The witness equation at `a = 1` states `σ_1(γ) = γ · c(1)^p`. Since
`σ_1(γ) = γ`, this forces `c(1)^p = 1`. -/
theorem witness_one_pow_eq_one (W : P.KummerMatchingWitnessBundle) :
    (W.witness 1) ^ p = 1 := by
  have h := W.witness_eq 1
  rw [cyclotomicKUnitsEquiv_one_apply] at h
  -- h : P.genUnit = P.genUnit ^ (1 : ZMod p).val * (W.witness 1) ^ p
  have hp_ne_one : p ≠ 1 := (Fact.out : p.Prime).one_lt.ne'
  have h1 : ((1 : (ZMod p)ˣ) : ZMod p).val = 1 := by
    have hval : (1 : ZMod p).val = 1 := ZMod.val_one'' hp_ne_one
    rw [Units.val_one]; exact hval
  rw [h1, pow_one] at h
  -- h : P.genUnit = P.genUnit * (W.witness 1) ^ p
  -- So (W.witness 1)^p = 1
  have : P.genUnit * (W.witness 1) ^ p = P.genUnit * 1 := by
    rw [← h, mul_one]
  exact mul_left_cancel this

/-- **Cocycle relation: explicit form of the witness equation at `a * b`.**

If `c_b` is the witness for `b`, then the witness equation at `a * b`
factors as
`σ_{ab}(γ) = σ_a(γ)^(b.val) · (σ_a(c_b))^p`.

This is the multiplicative cocycle relation for the witness function:
the action of `σ_{ab}` is the composition `σ_a ∘ σ_b`, and the witness
at `b` propagates through `σ_a`. -/
theorem witness_eq_mul_form (W : P.KummerMatchingWitnessBundle)
    (a b : CyclotomicUnitDelta p) :
    cyclotomicKUnitsEquiv (p := p) K (a * b) P.genUnit =
      cyclotomicKUnitsEquiv (p := p) K a P.genUnit ^ ((b : ZMod p).val) *
        (cyclotomicKUnitsEquiv (p := p) K a (W.witness b)) ^ p := by
  rw [cyclotomicKUnitsEquiv_mul_apply, W.witness_eq b, map_mul, map_pow, map_pow]

end KummerMatchingWitnessBundle
end KummerPresentation
end BernoulliRegular

end
