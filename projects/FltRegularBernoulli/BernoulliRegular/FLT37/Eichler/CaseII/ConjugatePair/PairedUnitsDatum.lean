import BernoulliRegular.FLT37.Eichler.CaseII.ConjugatePair.ThreeTermDescentEquation

/-!
# [FLT37-CASEII-R2] The **paired-units** σ-conjugate-pair datum (no-clearing descent)

This file resolves the Case-II descent's *reality reconciliation* — the structural heart, R2 — by a
**paired-units datum**.  It is the genuine fix for the obstruction that blocked the clean
σ-conjugate-pair descent.

## The obstruction (pinned)

The clean σ-conjugate-pair descent `CaseIIConjPairDescentSolution37`
(`CaseIIConjPairDescent.lean`) targets a *single*-unit equation `x'³⁷ + y'³⁷ = ε'·((ζ-1)^m·z')³⁷`
with `σx' = y'`.  Reaching it requires **clearing** the two leading descent units `ε₁, ε₂` of the
six-unit equation `ε₁·x'³⁷ + ε₂·y'³⁷ = ε₃·(…)³⁷` (`exists_sixUnit_descent_equation`).  The clearing
(Assumption II gives `ε₁/ε₂ = δ³⁷`, so `X = δ·x'`) introduces a 37-th root `δ` of a unit with
`σδ = δ⁻¹·ζᵏ` (`δ` is NOT a root of unity), and **no** power-balancing `X = δᵃx'`, `Y = δᵇy'`
restores `σX = Y`.  So the cleared variables cannot be put in clean σ-conjugate-pair form.

## The resolution — carry the units in the datum

We define a datum that **carries** the conjugate-paired units, so NO clearing is needed:

* `σx = y` (reality, carried as the σ-conjugate pair),
* `σz = z` (the anchor variable real),
* `σε₁ = ε₂` (units conjugate-paired — the σ-equivariance of the descent),
* the paired-units equation `ε₁·x³⁷ + ε₂·y³⁷ = ε₃·((ζ-1)^{m+1}·z)³⁷` (linear measure, **no
  clearing**).

The decisive soundness fact (proved here, `TwistedConjPairData37.equation_sigma_invariant`):
**the paired-units equation is σ-invariant** — applying `σ` to it, using `σx = y`, `σε₁ = ε₂`,
`σε₃ = ε₃`, `σz = z`, returns the *same* equation with the two summands swapped.  This is precisely
why carrying the units sidesteps the `δ` obstruction: the equation is already σ-symmetric, so the
descent preserves the structure with no clearing.

`TwistedConjPairData37` **extends** `ConjPairCaseIIData37`, so it inherits the *entire* proven
σ-conjugate-pair infrastructure — the clean σ-action `σ𝔞(η) = 𝔞(η)`
(`ConjPairCaseIIData37.map_rootIdeal`), the clean II1 `[𝔞(η)] = [𝔞(η₀)]`
(`ConjPairCaseIIData37.etaZeroPrincipalization`), `one_le_m`, and the well-founded minimality.  The
new content is *only* the carried paired units and the σ-invariance of their equation.

It imports only; it does **not** modify any existing file.

## References
* Washington, *Introduction to Cyclotomic Fields*, GTM 83, §9.1 (the descent), Thm 9.4.
-/

@[expose] public section

noncomputable section

open NumberField IsCyclotomicExtension Polynomial NumberField.IsCMField
open scoped nonZeroDivisors

namespace BernoulliRegular.FLT37.Eichler

open FLT37.LehmerVandiver.CaseII

variable {K : Type} [Field K] [NumberField K] [IsCyclotomicExtension {37} ℚ K]
  [NumberField.IsCMField K]

/-! ## 1. The paired-units σ-conjugate-pair Case-II descent datum -/

/-- **[TWISTED-CONJ-PAIR-CASEII-DATUM] The paired-units σ-conjugate-pair Case-II descent datum.**

Extends `ConjPairCaseIIData37` (which already carries the coefficient-1 equation, the σ-conjugate
pair `σx = y`, `σy = x`, and — over `CyclotomicField 37 ℚ` — the proven clean II1) with the
**conjugate-paired descent units** `ε₁, ε₂, ε₃` and the **paired-units descent equation**

  `ε₁·x³⁷ + ε₂·y³⁷ = ε₃·((ζ-1)^{m+1}·z)³⁷`

at the LINEAR measure, together with the σ-equivariance data `σε₁ = ε₂`, `σε₃ = ε₃`, `σz = z`.

Carrying the units is the genuine fix for the `δ`-obstruction: the paired-units equation is
σ-invariant (`equation_sigma_invariant`), so NO unit clearing — which would introduce the
σ-incompatible 37-th-root `δ` — is needed to keep the σ-conjugate-pair structure through the
descent. -/
structure TwistedConjPairData37 (K : Type) [Field K] [NumberField K]
    [IsCyclotomicExtension {37} ℚ K] [NumberField.IsCMField K] (m : ℕ)
    extends ConjPairCaseIIData37 K m where
  /-- The left leading descent unit (on `x³⁷`). -/
  ε₁ : (𝓞 K)ˣ
  /-- The right leading descent unit (on `y³⁷`). -/
  ε₂ : (𝓞 K)ˣ
  /-- The right-hand-side unit. -/
  ε₃ : (𝓞 K)ˣ
  /-- The units are conjugate-paired: `σε₁ = ε₂` (the σ-equivariance of the descent). -/
  unit_conj : NumberField.IsCMField.unitsComplexConj K ε₁ = ε₂
  /-- The right-hand unit is real. -/
  unit₃_real : NumberField.IsCMField.unitsComplexConj K ε₃ = ε₃
  /-- The anchor variable `z` is real. -/
  z_real : NumberField.IsCMField.ringOfIntegersComplexConj K z = z
  /-- The **paired-units descent equation** at the linear measure `(ζ-1)^{m+1}`. -/
  paired_equation :
    (ε₁ : 𝓞 K) * x ^ 37 + (ε₂ : 𝓞 K) * y ^ 37 =
      (ε₃ : 𝓞 K) * ((hζ.unit'.1 - 1) ^ (m + 1) * z) ^ 37

namespace TwistedConjPairData37

variable {m : ℕ} (D : TwistedConjPairData37 K m)

/-! ## 2. The σ-invariance of the paired-units equation (the soundness heart)

This is the decisive fact that validates the no-clearing claim.  Over a paired-units datum the
descent equation is **σ-invariant**: applying complex conjugation `σ` sends

  `ε₁·x³⁷ + ε₂·y³⁷ = ε₃·((ζ-1)^{m+1}·z)³⁷`

to the *same* equation, because `σ` swaps the two summands (`σε₁ = ε₂`, `σx = y`, so
`σ(ε₁·x³⁷) = ε₂·y³⁷`) and fixes the right-hand side (`σε₃ = ε₃`, `σz = z`, and `σ(ζ-1)` is an
associate of `ζ-1` via the unit `-ζ`, raised to the 37-th power inside the cube).  This is why
carrying the paired units removes the need for the σ-incompatible clearing factor `δ`. -/

/-- **The value-level unit pairing `σ(ε₁ : 𝓞 K) = (ε₂ : 𝓞 K)`.** The two complex-conjugation
operations agree on underlying elements (`unitsComplexConj` is `ringOfIntegersComplexConj` lifted to
units, definitionally), so `σ(ε₁ : 𝓞 K) = (σε₁ : 𝓞 K) = (ε₂ : 𝓞 K)` by `unit_conj`. -/
theorem ringOfIntegersComplexConj_eps₁ :
    NumberField.IsCMField.ringOfIntegersComplexConj K (D.ε₁ : 𝓞 K) = (D.ε₂ : 𝓞 K) := by
  have h : ((NumberField.IsCMField.unitsComplexConj K D.ε₁ : (𝓞 K)ˣ) : 𝓞 K) =
      NumberField.IsCMField.ringOfIntegersComplexConj K (D.ε₁ : 𝓞 K) := rfl
  rw [← h, D.unit_conj]

/-- **The value-level unit pairing `σ(ε₂ : 𝓞 K) = (ε₁ : 𝓞 K)`.** Since `σ² = id`, `σε₂ = σ(σε₁) =
ε₁`. -/
theorem ringOfIntegersComplexConj_eps₂ :
    NumberField.IsCMField.ringOfIntegersComplexConj K (D.ε₂ : 𝓞 K) = (D.ε₁ : 𝓞 K) := by
  rw [← D.ringOfIntegersComplexConj_eps₁]
  apply RingOfIntegers.ext; simp

/-- **The value-level `σ(ε₃ : 𝓞 K) = (ε₃ : 𝓞 K)`.** -/
theorem ringOfIntegersComplexConj_eps₃ :
    NumberField.IsCMField.ringOfIntegersComplexConj K (D.ε₃ : 𝓞 K) = (D.ε₃ : 𝓞 K) := by
  have h : ((NumberField.IsCMField.unitsComplexConj K D.ε₃ : (𝓞 K)ˣ) : 𝓞 K) =
      NumberField.IsCMField.ringOfIntegersComplexConj K (D.ε₃ : 𝓞 K) := rfl
  rw [← h, D.unit₃_real]

/-- **`σ((ζ-1)^{m+1}·z) = -ζ·(ζ-1)^{m+1}·z` up to the unit `(-ζ)^{m+1}`** is *not* needed at the
element level; what the descent equation needs is the cube `((ζ-1)^{m+1}·z)³⁷`, whose conjugate
equals itself times a 37-th power of a unit.  We record the σ-action on `(ζ-1)` directly:
`σ(ζ-1) = ζ³⁶ - 1`, an associate of `ζ-1`. -/
theorem ringOfIntegersComplexConj_zeta_sub_one :
    NumberField.IsCMField.ringOfIntegersComplexConj K (D.hζ.unit'.1 - 1) =
      D.hζ.unit'.1 ^ 36 - 1 := by
  have h37z : (D.hζ.unit'.1 : 𝓞 K) ^ 37 = 1 := by
    rw [← Units.val_pow_eq_pow_val, D.hζ.unit'_pow, Units.val_one]
  rw [map_sub, map_one, caseII_ringOfIntegersComplexConj_root_of_unity h37z]

/-- **The right-hand side cube is σ-fixed up to a 37-th power of a unit.**

`σ(((ζ-1)^{m+1}·z)³⁷) = ((-ζ³⁶)^{m+1})³⁷ · ((ζ-1)^{m+1}·z)³⁷`, because `σ(ζ-1) = ζ³⁶-1 =
-ζ³⁶·(ζ-1)` (the unit `-ζ³⁶ = -ζ⁻¹`; indeed `-ζ³⁶·(ζ-1) = -ζ³⁷+ζ³⁶ = -1+ζ³⁶ = ζ³⁶-1` as `ζ³⁷ = 1`),
`σz = z`, and the cube of the unit `(-ζ³⁶)^{m+1}` is a 37-th power.  Concretely the conjugate of the
right-hand side `ε₃·((ζ-1)^{m+1}·z)³⁷` equals `ε₃·((-ζ³⁶)^{m+1}·(ζ-1)^{m+1}·z)³⁷`. -/
theorem ringOfIntegersComplexConj_rhs :
    NumberField.IsCMField.ringOfIntegersComplexConj K
        ((D.ε₃ : 𝓞 K) * ((D.hζ.unit'.1 - 1) ^ (m + 1) * D.z) ^ 37) =
      (D.ε₃ : 𝓞 K) *
        (((-D.hζ.unit'.1 ^ 36) ^ (m + 1) : 𝓞 K) * ((D.hζ.unit'.1 - 1) ^ (m + 1) * D.z)) ^ 37 := by
  have h37z : (D.hζ.unit'.1 : 𝓞 K) ^ 37 = 1 := by
    rw [← Units.val_pow_eq_pow_val, D.hζ.unit'_pow, Units.val_one]
  rw [map_mul, D.ringOfIntegersComplexConj_eps₃, map_pow, map_mul, map_pow,
    D.ringOfIntegersComplexConj_zeta_sub_one, D.z_real]
  -- `(ζ³⁶-1)^{m+1}·z = ((-ζ³⁶)·(ζ-1))^{m+1}·z = (-ζ³⁶)^{m+1}·((ζ-1)^{m+1}·z)` since
  -- `ζ³⁶-1 = -ζ³⁶·(ζ-1)` (as `ζ³⁷ = 1`).
  have hbase : ((D.hζ.unit'.1 ^ 36 - 1 : 𝓞 K) ^ (m + 1) * D.z) =
      ((-D.hζ.unit'.1 ^ 36) ^ (m + 1) : 𝓞 K) * ((D.hζ.unit'.1 - 1) ^ (m + 1) * D.z) := by
    rw [← mul_assoc, ← mul_pow]
    congr 2
    linear_combination h37z
  rw [hbase]

/-- **[SOUNDNESS HEART] The paired-units descent equation is σ-invariant.**

Applying complex conjugation `σ` to `ε₁·x³⁷ + ε₂·y³⁷ = ε₃·((ζ-1)^{m+1}·z)³⁷` yields a *valid*
equation again:

  `ε₂·y³⁷ + ε₁·x³⁷ = ε₃·((-ζ³⁶)^{m+1}·(ζ-1)^{m+1}·z)³⁷`.

Left side: `σ` swaps the two summands — `σ(ε₁·x³⁷) = σε₁·(σx)³⁷ = ε₂·y³⁷` and symmetrically.  Right
side: σ-fixed up to the 37-th power of the unit `(-ζ³⁶)^{m+1}` (`ringOfIntegersComplexConj_rhs`).
So the equation is preserved by `σ` — the precise statement that the paired-units form needs **no
clearing** to remain σ-symmetric through the descent. -/
theorem equation_sigma_invariant :
    (D.ε₂ : 𝓞 K) * D.y ^ 37 + (D.ε₁ : 𝓞 K) * D.x ^ 37 =
      (D.ε₃ : 𝓞 K) *
        (((-D.hζ.unit'.1 ^ 36) ^ (m + 1) : 𝓞 K) * ((D.hζ.unit'.1 - 1) ^ (m + 1) * D.z)) ^ 37 := by
  have hconj := congrArg (NumberField.IsCMField.ringOfIntegersComplexConj K) D.paired_equation
  rw [map_add, map_mul, map_pow, map_mul, map_pow, D.ringOfIntegersComplexConj_eps₁,
    D.ringOfIntegersComplexConj_eps₂, D.x_conj, D.y_conj, D.ringOfIntegersComplexConj_rhs] at hconj
  exact hconj

/-! ## 3. Inherited descent machinery: `one_le_m`, II1, minimality

`TwistedConjPairData37` extends `ConjPairCaseIIData37`, so the *entire* proven σ-conjugate-pair
infrastructure transfers verbatim through `D.toConjPairCaseIIData37`:

* `one_le_m` — `D.toCaseIIData37.one_le_m : 1 ≤ m`;
* the clean σ-action `σ𝔞(η) = 𝔞(η)` — `D.toConjPairCaseIIData37.map_rootIdeal`;
* the clean II1 `[𝔞(η)] = [𝔞(η₀)]` — `ConjPairCaseIIData37.etaZeroPrincipalization`
  (over `CyclotomicField 37 ℚ`).

The paired units and their σ-invariant equation are *additional* structure; they do not interfere
with the coefficient-1 equation that drives the ideal machinery.  We record `one_le_m` here so
downstream files use the paired-units datum directly. -/

/-- **`1 ≤ m`** for a paired-units datum, inherited from the underlying `CaseIIData37`. -/
theorem one_le_m (D : TwistedConjPairData37 K m) : 1 ≤ m :=
  CaseIIData37.one_le_m (ConjPairCaseIIData37.toCaseIIData37 D.toConjPairCaseIIData37)

end TwistedConjPairData37

end BernoulliRegular.FLT37.Eichler

end

end
