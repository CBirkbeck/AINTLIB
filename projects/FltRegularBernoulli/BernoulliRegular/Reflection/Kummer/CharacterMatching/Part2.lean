module

public import BernoulliRegular.Reflection.Kummer.Presentation
public import BernoulliRegular.UnitQuotient.DeltaAction
public import BernoulliRegular.KummerPairing.Setup
public import BernoulliRegular.Reflection.Comparison
public import BernoulliRegular.Reflection.Kummer.CharacterMatching.Part1

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

namespace KummerPresentation

variable {p : ℕ} [Fact p.Prime]
variable {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
variable {χ : MulChar (ZMod p)ˣ ℚ}
variable {Comp : CyclotomicFieldClassGroupPSylowComponent (p := p) K}
variable {Ext : ComponentUnramifiedCyclicDegreePExtension (p := p) K χ Comp}

variable (P : KummerPresentation Ext)

namespace KummerMatchingWitnessBundle

/-- **Cocycle relation in the witness function.**

Substituting the witness equation at `a` into the previous lemma
gives the explicit cocycle for `c(a * b)`:
`σ_{ab}(γ) = γ^(a.val * b.val) · (c_a^(b.val) · σ_a(c_b))^p`.

The substantive content is that the LHS witness `c(a * b)` is determined
by `c(a)`, `σ_a(c(b))`, and the correction power coming from exponent
reconciliation `(a*b).val ≡ a.val * b.val (mod p)`. -/
theorem cocycle_pow_eq (W : P.KummerMatchingWitnessBundle)
    (a b : CyclotomicUnitDelta p) :
    cyclotomicKUnitsEquiv (p := p) K (a * b) P.genUnit =
      P.genUnit ^ ((a : ZMod p).val * (b : ZMod p).val) *
        ((W.witness a) ^ ((b : ZMod p).val) *
          cyclotomicKUnitsEquiv (p := p) K a (W.witness b)) ^ p := by
  rw [cyclotomicKUnitsEquiv_mul_apply, W.witness_eq b, map_mul, map_pow,
    map_pow, W.witness_eq a]
  -- Goal: (P.genUnit ^ a.val * (W.witness a) ^ p) ^ b.val *
  --        (cyclotomicKUnitsEquiv K a (W.witness b)) ^ p =
  --       P.genUnit ^ (a.val * b.val) *
  --        ((W.witness a) ^ b.val * cyclotomicKUnitsEquiv K a (W.witness b)) ^ p
  rw [mul_pow]
  -- Goal: P.genUnit ^ (a.val) ^ (b.val) * ((W.witness a) ^ p) ^ (b.val) *
  --        cyclotomicKUnitsEquiv ... ^ p =
  --       P.genUnit ^ (a.val * b.val) *
  --        ((W.witness a) ^ (b.val) * cyclotomicKUnitsEquiv ...) ^ p
  rw [← pow_mul P.genUnit, ← pow_mul (W.witness a)]
  rw [mul_comm p ((b : ZMod p).val), pow_mul (W.witness a) _ p, mul_assoc,
    ← mul_pow]

/-- **Reflexivity constructor `refl`: the trivial witness bundle when
`P.genUnit` is itself a `p`-th power.**

If `P.genUnit = u^p` for some `u : Kˣ`, then `σ_a(γ) = σ_a(u)^p` and
`γ^(a.val) = u^(a.val * p) = (u^(a.val))^p`. So the witness equation
becomes `σ_a(u)^p = (u^(a.val))^p · c^p`, satisfied by
`c(a) := σ_a(u) · u^(-a.val)`.

This is the canonical "trivial" discharge. -/
def reflOfGenIsPthPower (u : Kˣ)
    (hu : P.genUnit = u ^ p) : P.KummerMatchingWitnessBundle where
  witness a :=
    cyclotomicKUnitsEquiv (p := p) K a u * u⁻¹ ^ ((a : ZMod p).val)
  witness_eq a := by
    -- Goal: σ_a(γ) = γ^(a.val) * (σ_a(u) · u⁻¹^(a.val))^p
    -- After rw [hu, map_pow]:
    --   σ_a(u)^p = (u^p)^(a.val) * (σ_a(u) · u⁻¹^(a.val))^p
    rw [hu, map_pow, mul_pow]
    -- Goal: σ_a(u)^p = (u^p)^(a.val) * (σ_a(u)^p * (u⁻¹^(a.val))^p)
    -- Push (u⁻¹^(a.val))^p = (u^(a.val * p))⁻¹.
    rw [show (u⁻¹ ^ ((a : ZMod p).val)) ^ p = (u ^ ((a : ZMod p).val * p))⁻¹ by
      rw [inv_pow, inv_pow, ← pow_mul]]
    -- Goal: σ_a(u)^p = (u^p)^(a.val) * (σ_a(u)^p * (u^((a.val) * p))⁻¹)
    rw [← pow_mul, mul_comm p ((a : ZMod p).val)]
    -- Goal: σ_a(u)^p = u^((a.val) * p) * (σ_a(u)^p * (u^((a.val) * p))⁻¹)
    rw [mul_comm (u ^ ((a : ZMod p).val * p)) _,
      mul_assoc, inv_mul_cancel, mul_one]

/-- **Reflexivity at `a = 1`** in the trivial-`p`-th-power bundle. -/
theorem reflOfGenIsPthPower_witness_one
    (u : Kˣ) (hu : P.genUnit = u ^ p) :
    (reflOfGenIsPthPower (P := P) u hu).witness 1 = 1 := by
  change cyclotomicKUnitsEquiv (p := p) K 1 u * u⁻¹ ^ ((1 : (ZMod p)ˣ) : ZMod p).val = 1
  rw [cyclotomicKUnitsEquiv_one_apply]
  have hp_ne_one : p ≠ 1 := (Fact.out : p.Prime).one_lt.ne'
  have h1 : ((1 : (ZMod p)ˣ) : ZMod p).val = 1 := by
    rw [Units.val_one]
    exact ZMod.val_one'' hp_ne_one
  rw [h1, pow_one, mul_inv_cancel]

/-- **`p = 2` discharge: the trivial witness bundle.**

When `p = 2`, the group `(ZMod 2)ˣ` is trivial, so the only required
witness is at `a = 1`. The canonical choice `c(1) := 1` works. -/
def reflOfPEqTwo (hp2 : p = 2) :
    P.KummerMatchingWitnessBundle where
  witness _ := 1
  witness_eq a := by
    -- a : (ZMod 2)ˣ, so a = 1
    have ha : a = 1 := by
      subst hp2; exact Subsingleton.elim a 1
    rw [ha]
    exact witness_eq_at_one_canonical P

/-- **Witness at `a = 1` for the `p = 2` bundle is `1`.** -/
theorem reflOfPEqTwo_witness_one (hp2 : p = 2) :
    (reflOfPEqTwo (P := P) hp2).witness 1 = 1 := rfl

/-!
### Bridge to mathlib's cyclotomic character data on `ζ_p`

The cyclotomic Galois action on a primitive `p`-th root of unity is
`σ_a(ζ) = ζ^(a.val)` (lemma `cyclotomicSigmaOfUnit_apply_zeta` in
`UnitQuotient.DeltaAction`). Reading this through the witness-bundle
formalism, the canonical witness for the case `γ = ζ` is the trivial
function `c(a) := 1`, since `σ_a(ζ) = ζ^(a.val) · 1^p`.

We package this as a structural identity, giving the consumer access
to the cyclotomic character at the witness-bundle level. -/

/-- **Cyclotomic character identity at the unit level.**

For any unit `u : Kˣ` whose underlying value equals `IsCyclotomicExtension.zeta p ℚ K`,
the cyclotomic Galois action satisfies
`σ_a(u) = u^(a.val)` exactly (no `p`-th-power correction).

This is the structural identity from
`cyclotomicSigmaOfUnit_apply_zeta`, transferred to the unit group. -/
theorem cyclotomicKUnitsEquiv_apply_zeta_unit (a : CyclotomicUnitDelta p)
    (u : Kˣ) (hu : (u : K) = IsCyclotomicExtension.zeta p ℚ K) :
    (cyclotomicKUnitsEquiv (p := p) K a u : K) =
      (u : K) ^ ((a : ZMod p).val) := by
  rw [cyclotomicKUnitsEquiv_val, hu]
  exact cyclotomicSigmaOfUnit_apply_zeta (p := p) (K := K) a

/-- **Witness bundle for `γ = ζ_p`: the trivial witness.**

If `P.genUnit` represents the cyclotomic primitive root `ζ_p`, then the
canonical witness function `c(a) := 1` works because
`σ_a(ζ) = ζ^(a.val) = ζ^(a.val) · 1^p`. -/
def reflOfGenIsZeta
    (hu : (P.genUnit : K) = IsCyclotomicExtension.zeta p ℚ K) :
    P.KummerMatchingWitnessBundle where
  witness _ := 1
  witness_eq a := by
    -- Goal: σ_a(P.genUnit) = P.genUnit ^ (a.val) * 1 ^ p
    rw [one_pow, mul_one]
    apply Units.ext
    rw [cyclotomicKUnitsEquiv_apply_zeta_unit (p := p) (K := K) a P.genUnit hu]
    push_cast
    rfl

/-- **Witness at every `a` for the `ζ` bundle is `1`.** -/
theorem reflOfGenIsZeta_witness
    (hu : (P.genUnit : K) = IsCyclotomicExtension.zeta p ℚ K)
    (a : CyclotomicUnitDelta p) :
    (reflOfGenIsZeta (P := P) hu).witness a = 1 := rfl

/-!
### Discharge: trivial generator

If `P.genUnit = 1`, the witness equation reduces to `σ_a(1) = 1^(a.val) · c^p`,
satisfied by `c(a) := 1`. This is the most degenerate trivial discharge,
corresponding to `γ = 1`. -/

/-- **Trivial discharge: `P.genUnit = 1`.** When the chosen Kummer generator
is `1`, the witness function `c(a) := 1` satisfies the witness equation
trivially: both sides equal `1`. -/
def reflOfGenIsOne (hu : P.genUnit = 1) :
    P.KummerMatchingWitnessBundle where
  witness _ := 1
  witness_eq a := by
    -- Goal: σ_a(P.genUnit) = P.genUnit ^ (a.val) * 1 ^ p
    rw [hu, one_pow, one_pow, mul_one]
    -- Goal: cyclotomicKUnitsEquiv K a 1 = 1
    exact map_one _

/-- **Witness at every `a` for the `genUnit = 1` bundle is `1`.** -/
theorem reflOfGenIsOne_witness (hu : P.genUnit = 1) (a : CyclotomicUnitDelta p) :
    (reflOfGenIsOne (P := P) hu).witness a = 1 := rfl

/-!
### Cyclotomic action on rational (prime-subfield) elements

The cyclotomic Galois automorphism `σ_a : K ≃ₐ[ℚ] K` fixes the prime
subfield `ℚ ⊂ K`. This gives a structural identity for any unit `u : Kˣ`
whose underlying value is the image of a rational. -/

/-- **The cyclotomic action fixes the prime subfield (rational elements).**

If `(u : K) = algebraMap ℚ K q` for some `q : ℚ`, then
`σ_a(u) = u` (i.e., `cyclotomicKUnitsEquiv K a u = u`) for every `a`. -/
theorem cyclotomicKUnitsEquiv_apply_rational (a : CyclotomicUnitDelta p)
    (u : Kˣ) (q : ℚ) (hu : (u : K) = algebraMap ℚ K q) :
    cyclotomicKUnitsEquiv (p := p) K a u = u := by
  apply Units.ext
  rw [cyclotomicKUnitsEquiv_val, hu]
  -- Goal: cyclotomicFieldEquiv K a (algebraMap ℚ K q) = algebraMap ℚ K q
  change (cyclotomicSigmaOfUnit (p := p) K a) (algebraMap ℚ K q) = algebraMap ℚ K q
  exact AlgEquiv.commutes _ q

/-- **The cyclotomic action fixes integer-valued units.**

If `(u : K) = (n : K)` for some `n : ℤ`, then `σ_a(u) = u`. This
is the integer special case of `cyclotomicKUnitsEquiv_apply_rational`. -/
theorem cyclotomicKUnitsEquiv_apply_intCast (a : CyclotomicUnitDelta p)
    (u : Kˣ) (n : ℤ) (hu : (u : K) = (n : K)) :
    cyclotomicKUnitsEquiv (p := p) K a u = u := by
  apply Units.ext
  rw [cyclotomicKUnitsEquiv_val, hu]
  change (cyclotomicSigmaOfUnit (p := p) K a) ((n : K)) = ((n : K))
  exact map_intCast _ n

/-!
### Discharge: generator in the prime subfield

If `(P.genUnit : K) = q : ℚ`, then `σ_a(γ) = γ` for all `a`, and the
witness equation `γ = γ^(a.val) · c_a^p` reduces to providing `c_a` such
that `c_a^p = γ * γ^(-a.val)`. We provide a parametric discharge taking
the witness data as input. -/

/-- **Discharge: rational generator with prescribed Kummer witness.**

If `(P.genUnit : K) = algebraMap ℚ K q` and we are given a witness
function `d : Δ → Kˣ` such that `P.genUnit = P.genUnit^(a.val) * (d a)^p`
for every `a`, then we obtain a witness bundle.

Mathematically, the witness equation at `a` is `σ_a(γ) = γ^(a.val) · c_a^p`,
which (since `σ_a(γ) = γ`) becomes `γ = γ^(a.val) · c_a^p`. -/
def reflOfPrimeSubfield (q : ℚ) (hu : (P.genUnit : K) = algebraMap ℚ K q)
    (d : CyclotomicUnitDelta p → Kˣ)
    (hd : ∀ a : CyclotomicUnitDelta p,
      P.genUnit = P.genUnit ^ ((a : ZMod p).val) * (d a) ^ p) :
    P.KummerMatchingWitnessBundle where
  witness := d
  witness_eq a := by
    -- σ_a(γ) = γ (since γ ∈ ℚ), so the equation is γ = γ^(a.val) · (d a)^p.
    rw [cyclotomicKUnitsEquiv_apply_rational (p := p) (K := K) a P.genUnit q hu]
    exact hd a

/-- **Discharge: integer generator with prescribed Kummer witness.**

The integer special case of `reflOfPrimeSubfield`. -/
def reflOfRationalInteger (n : ℤ) (hu : (P.genUnit : K) = (n : K))
    (d : CyclotomicUnitDelta p → Kˣ)
    (hd : ∀ a : CyclotomicUnitDelta p,
      P.genUnit = P.genUnit ^ ((a : ZMod p).val) * (d a) ^ p) :
    P.KummerMatchingWitnessBundle where
  witness := d
  witness_eq a := by
    rw [cyclotomicKUnitsEquiv_apply_intCast (p := p) (K := K) a P.genUnit n hu]
    exact hd a

/-!
### Composition / perturbation API

Given a witness bundle `W`, we can perturb the witness function by
multiplying by any function `e : Δ → Kˣ` whose `p`-th power evaluates to
`1` (i.e., `(e a)^p = 1`). This produces another witness bundle for the
same `P`. -/

/-- **Perturbation by a `p`-th-root-of-unity-valued function.**

If `W` is a witness bundle and `e : Δ → Kˣ` satisfies `(e a)^p = 1` for
all `a`, then `(c a) * (e a)` is also a valid witness function. -/
def perturbByPthRootUnity (W : P.KummerMatchingWitnessBundle)
    (e : CyclotomicUnitDelta p → Kˣ)
    (he : ∀ a : CyclotomicUnitDelta p, (e a) ^ p = 1) :
    P.KummerMatchingWitnessBundle where
  witness a := W.witness a * e a
  witness_eq a := by
    rw [W.witness_eq a, mul_pow, he a, mul_one]

/-- **Perturbation preserves the witness modulo `e`.** -/
@[simp]
theorem perturbByPthRootUnity_witness (W : P.KummerMatchingWitnessBundle)
    (e : CyclotomicUnitDelta p → Kˣ)
    (he : ∀ a : CyclotomicUnitDelta p, (e a) ^ p = 1)
    (a : CyclotomicUnitDelta p) :
    (perturbByPthRootUnity (P := P) W e he).witness a = W.witness a * e a := rfl

/-- **Trivial perturbation by the constant-`1` function.** Perturbing by
`e = 1` returns the same witness function. -/
theorem perturbByPthRootUnity_one (W : P.KummerMatchingWitnessBundle) :
    perturbByPthRootUnity (P := P) W (fun _ => 1) (fun _ => one_pow _) = W := by
  cases W with
  | mk w heq =>
    simp only [perturbByPthRootUnity, mul_one]

/-!
### Multiplicativity of the witness equation under exponent simplification

These theorems package the structural identities the consumer would
otherwise rederive when chaining matching atoms. -/

/-- **Cocycle: explicit witness at `a * b` in terms of `c_a`, `σ_a(c_b)`,
and the exponent reconciliation.**

Combining `cocycle_pow_eq` with the cocycle `c_{ab} := c_a^(b.val) ·
σ_a(c_b) · γ^k_{a,b}` for the explicit power-correction `k_{a,b}` arising
from `(a*b).val ≡ a.val · b.val (mod p)`. We expose only the witness-product
side, which is the core compositional identity. -/
theorem witness_product_pow_eq (W : P.KummerMatchingWitnessBundle)
    (a b : CyclotomicUnitDelta p) :
    (cyclotomicKUnitsEquiv (p := p) K (a * b) P.genUnit) =
      P.genUnit ^ ((a : ZMod p).val * (b : ZMod p).val) *
        ((W.witness a) ^ ((b : ZMod p).val) *
          cyclotomicKUnitsEquiv (p := p) K a (W.witness b)) ^ p :=
  cocycle_pow_eq (P := P) W a b

end KummerMatchingWitnessBundle

/-!
### Direct discharges from witness-bundle constructors

The witness-bundle constructors above directly imply the matching
hypothesis. We expose convenience theorems naming each discharge. -/

/-- **Discharge: trivial bundle from `p = 2`.** -/
theorem kummerCharacterMatchingHypothesis_of_p_eq_two_via_bundle
    (hp2 : p = 2) :
    P.KummerCharacterMatchingHypothesis :=
  P.kummerCharacterMatchingHypothesis_of_witnessBundle
    (KummerMatchingWitnessBundle.reflOfPEqTwo (P := P) hp2)

/-- **Discharge: trivial bundle when `genUnit` is a `p`-th power.** -/
theorem kummerCharacterMatchingHypothesis_of_genIsPthPower
    (u : Kˣ) (hu : P.genUnit = u ^ p) :
    P.KummerCharacterMatchingHypothesis :=
  P.kummerCharacterMatchingHypothesis_of_witnessBundle
    (KummerMatchingWitnessBundle.reflOfGenIsPthPower (P := P) u hu)

/-- **Discharge: trivial bundle when `genUnit = ζ_p`.** -/
theorem kummerCharacterMatchingHypothesis_of_genIsZeta
    (hu : (P.genUnit : K) = IsCyclotomicExtension.zeta p ℚ K) :
    P.KummerCharacterMatchingHypothesis :=
  P.kummerCharacterMatchingHypothesis_of_witnessBundle
    (KummerMatchingWitnessBundle.reflOfGenIsZeta (P := P) hu)

/-- **Discharge: trivial bundle when `genUnit = 1`.**

When the Kummer generator is `1`, the matching is automatic: both sides
of `σ_a(1) = 1^(a.val) · c^p` are `1`. -/
theorem kummerCharacterMatchingHypothesis_of_genIsOne
    (hu : P.genUnit = 1) :
    P.KummerCharacterMatchingHypothesis :=
  P.kummerCharacterMatchingHypothesis_of_witnessBundle
    (KummerMatchingWitnessBundle.reflOfGenIsOne (P := P) hu)

/-- **Discharge: bundle from a rational generator with prescribed Kummer witness.**

If `(P.genUnit : K) = algebraMap ℚ K q` for some rational `q`, and an
explicit witness function `d : Δ → Kˣ` is provided satisfying
`P.genUnit = P.genUnit^(a.val) * (d a)^p` for every `a`, then the matching
hypothesis follows. -/
theorem kummerCharacterMatchingHypothesis_of_genInPrimeSubfield
    (q : ℚ) (hu : (P.genUnit : K) = algebraMap ℚ K q)
    (d : CyclotomicUnitDelta p → Kˣ)
    (hd : ∀ a : CyclotomicUnitDelta p,
      P.genUnit = P.genUnit ^ ((a : ZMod p).val) * (d a) ^ p) :
    P.KummerCharacterMatchingHypothesis :=
  P.kummerCharacterMatchingHypothesis_of_witnessBundle
    (KummerMatchingWitnessBundle.reflOfPrimeSubfield (P := P) q hu d hd)

/-- **Discharge: bundle from an integer generator with prescribed Kummer witness.**

The integer special case of `kummerCharacterMatchingHypothesis_of_genInPrimeSubfield`. -/
theorem kummerCharacterMatchingHypothesis_of_genIsRationalInteger
    (n : ℤ) (hu : (P.genUnit : K) = (n : K))
    (d : CyclotomicUnitDelta p → Kˣ)
    (hd : ∀ a : CyclotomicUnitDelta p,
      P.genUnit = P.genUnit ^ ((a : ZMod p).val) * (d a) ^ p) :
    P.KummerCharacterMatchingHypothesis :=
  P.kummerCharacterMatchingHypothesis_of_witnessBundle
    (KummerMatchingWitnessBundle.reflOfRationalInteger (P := P) n hu d hd)

end KummerPresentation

end BernoulliRegular

end
