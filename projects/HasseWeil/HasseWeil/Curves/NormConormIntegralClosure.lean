/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import HasseWeil.Curves.LocalizedDictionary
import HasseWeil.Curves.PushforwardDivisor
import HasseWeil.Curves.RamificationFinite
import HasseWeil.Curves.OrdAtInftyRamification
import HasseWeil.Curves.RankOneDomination
import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing
import Mathlib.RingTheory.Valuation.IsTrivialOn

/-!
# The norm–conorm count over the integral closure `B` (CoordHom-free, Silverman II.3.6)

For a finite separable extension `K(C₁) / K(C₂)` of smooth-curve function fields that has *no*
global affine `CoordHom` (e.g. the pullback of a genuine isogeny, whose pullback of the
coordinate generators has poles at the affine kernel), the affine norm–conorm template of
`HasseWeil/Curves/PushforwardDivisor.lean` (`relNorm_maximalIdealAt_eq`,
`count_relNorm_eq_sum_fiber`) does not apply: it routes through the affine coordinate-ring
extension `F[C₂] → F[C₁]`.  Instead we work over the **integral closure**

  `B := integralClosure C₂.CoordinateRing C₁.FunctionField`,

whose maximal ideals are in bijection with *all* the places of `C₁` over the affine places of
`C₂` (supplied by `HasseWeil/Curves/LocalizedDictionary.lean`, instantiated at the trivial
localization `Af := C₂.CoordinateRing`, `f := 1`, valid at *every* affine place).

This file ports the affine template over `B`:
* the `s = 1` core `relNorm_{C₂.CoordinateRing}(P) = m_{below}` for a maximal `P` of `B`;
* the per-place count `count_{m_Q}(relNorm(span{w})) = Σ_{P over m_Q} count_P(span{w})`.

## References

* [Silverman, *The Arithmetic of Elliptic Curves*], II.2.6, II.3.6, III.4.10(c).
-/

open WeierstrassCurve
open scoped nonZeroDivisors

set_option linter.unusedSectionVars false

namespace HasseWeil.Curves.NormConormIntegralClosure

open HasseWeil.Curves HasseWeil.Curves.LocalizedDictionary

variable {F : Type*} [Field F] [IsAlgClosed F]
variable {C₁ C₂ : SmoothPlaneCurve F} [C₁.toAffine.IsElliptic] [C₂.toAffine.IsElliptic]
variable [IsIntegrallyClosed C₂.CoordinateRing]
variable [algKL : Algebra C₂.FunctionField C₁.FunctionField]
  [finKL : FiniteDimensional C₂.FunctionField C₁.FunctionField]
  [sepKL : Algebra.IsSeparable C₂.FunctionField C₁.FunctionField]
  [algCR1 : Algebra C₂.CoordinateRing C₁.FunctionField]
  [tw1 : IsScalarTower C₂.CoordinateRing C₂.FunctionField C₁.FunctionField]
  [twF : IsScalarTower F C₂.FunctionField C₁.FunctionField]

/-- The integral closure `B` of `C₂.CoordinateRing` inside `C₁.FunctionField` (as a subalgebra;
its coercion to a type carries the Dedekind/finite/fraction-ring structure of the AKLB setup). -/
noncomputable abbrev B : Subalgebra C₂.CoordinateRing C₁.FunctionField :=
  integralClosure C₂.CoordinateRing C₁.FunctionField

/-! ### The trivial localization `Af := C₂.CoordinateRing`, `f := 1` -/

noncomputable instance instAway1 :
    IsLocalization.Away (1 : C₂.CoordinateRing) C₂.CoordinateRing :=
  IsLocalization.away_of_isUnit_of_bijective _ isUnit_one Function.bijective_id

noncomputable instance instTowTrivial :
    IsScalarTower C₂.CoordinateRing C₂.CoordinateRing C₂.FunctionField :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

/-- `1 ∉ m_Q` for every smooth point `Q` (a maximal ideal is proper). -/
theorem one_notMem_maximalIdealAt (Q : C₂.SmoothPoint) :
    (1 : C₂.CoordinateRing) ∉ C₂.maximalIdealAt Q := by
  rw [← Ideal.eq_top_iff_one]
  exact (C₂.maximalIdealAt_isMaximal Q).ne_top

/-- `awayIdealAt C₂.CoordinateRing Q = m_Q` (the localization at `f := 1` is trivial, so the
extended ideal is the original maximal ideal). -/
theorem awayIdealAt_eq_maximalIdealAt (Q : C₂.SmoothPoint) :
    awayIdealAt (C₂ := C₂) C₂.CoordinateRing Q = C₂.maximalIdealAt Q := by
  rw [awayIdealAt, Algebra.algebraMap_self, Ideal.map_id]

/-! ### The Dedekind/finite/torsion-free/fraction-ring instances for `B` (T-A1) -/

set_option backward.isDefEq.respectTransparency false in
/-- `B` is a Dedekind domain (Krull–Akizuki, separable case). -/
instance instDedekindB : IsDedekindDomain (B (C₁ := C₁) (C₂ := C₂)) :=
  RamificationFinite.isDedekindDomain C₂.CoordinateRing C₂.FunctionField C₁.FunctionField _

set_option backward.isDefEq.respectTransparency false in
/-- `B` is module-finite over `C₂.CoordinateRing`. -/
instance instModuleFiniteB :
    Module.Finite C₂.CoordinateRing (B (C₁ := C₁) (C₂ := C₂)) :=
  RamificationFinite.module_finite C₂.CoordinateRing C₂.FunctionField C₁.FunctionField _

set_option backward.isDefEq.respectTransparency false in
/-- `B` has fraction field `C₁.FunctionField`. -/
instance instFractionRingB :
    IsFractionRing (B (C₁ := C₁) (C₂ := C₂)) C₁.FunctionField :=
  RamificationFinite.isFractionRing C₂.CoordinateRing C₂.FunctionField C₁.FunctionField _

set_option backward.isDefEq.respectTransparency false in
/-- `B` is a torsion-free `C₂.CoordinateRing`-module. -/
instance instTorsionFreeB :
    Module.IsTorsionFree C₂.CoordinateRing (B (C₁ := C₁) (C₂ := C₂)) :=
  RamificationFinite.isTorsionFree C₂.CoordinateRing C₂.FunctionField C₁.FunctionField _

/-! ### The coordinate ring of `C₁` lands in `B` (T-A2, integrality sub-wall)

The coordinate generators `x₁ = coordXFun C₁`, `y₁ = coordYFun C₁` of `C₁`, regarded inside
`K(C₁)`, are integral over `C₂.CoordinateRing`: each is regular at every place of `C₁` lying
over an *affine* place of `C₂` (their only poles — at `∞` of `C₁` and at the affine kernel —
all lie over `∞` of `C₂`).  Hence the entire coordinate ring `F[C₁] = F[x₁, y₁]` lands in `B`.

This is the integral-closure analogue of the affine `coordRing_mem_integralClosure`
(`LocalizedDictionary.lean`) at the *global* base (`Af := C₂.CoordinateRing`, `f := 1`).  Its
content is the genuine geometric input (regularity of the coordinate functions at all places
over the affine part of `C₂`); everything downstream is structural. -/

/-- The basepoint-regularity hypothesis: the function-field map `K(C₂) → K(C₁)` (the pullback of
the underlying isogeny) carries functions regular at `∞` of `C₂` to functions regular at `∞` of
`C₁` (i.e. the morphism is defined at the basepoint `O₁`, mapping it to `O₂`).  This is the spelled
form of `EC.Isogeny.pullback_ordAtInfty_nonneg` / `EC.Isogeny.reflects_ordAtInfty` for the abstract
algebra `algKL`.  It is the single geometric input that pins the *only* pole of the coordinate
generators of `C₁` (at `∞` of `C₁`) to lie over `∞` of `C₂`, hence away from every affine place. -/
abbrev OrdAtInftyReg : Prop :=
  ∀ f : C₂.FunctionField, 0 ≤ C₂.ordAtInfty f →
    0 ≤ C₁.ordAtInfty (algebraMap C₂.FunctionField C₁.FunctionField f)

/-! #### The valuative-criterion reduction of integrality (structural, non-circular)

The integral closure `B` is a Dedekind domain with fraction field `K(C₁)`, so an element
`z ∈ K(C₁)` lies in `B` iff it is `v`-integral at *every* height-one prime `v` of `B`
(mathlib's `IsDedekindDomain.HeightOneSpectrum.mem_integers_of_valuation_le_one`).  This
**non-circular** criterion (it does *not* presuppose `coordRingToClosure`, i.e. the very
integralities we are proving — contrast `LocalizedDictionary.pointAt`) reduces both generator
integralities to the single geometric statement that the `B`-prime valuations are `≤ 1` on the
coordinate generators of `C₁`.

The valuation `v.valuation K(C₁)` of a height-one prime `v` of `B` is a place of `C₁` lying over
the affine place `v.asIdeal.under C₂.CoordinateRing` of `C₂` (a nonzero — hence height-one —
prime of `C₂.CoordinateRing`, since `B` is module-finite over `C₂.CoordinateRing`).  The
coordinate generators `x₁, y₁ ∈ F[C₁]` are regular at *every affine point* of `C₁` (their only
pole is `∞` of `C₁`, `pointValuation_algebraMap_le_one`), and `∞` of `C₁` lies over `∞` of `C₂`
by `hreg` (the basepoint), hence away from the affine `v`.  Identifying `v.valuation` with a point
valuation of `C₁` is exactly the **global-`B` place dictionary** — the project's standing wall;
it is the non-structural content isolated in `BPrimeValuationCoordGenLeOne` below. -/

/-- **The genuine geometric residual (the global-`B` place dictionary)**: every height-one prime
`v` of `B` has valuation `≤ 1` on the two coordinate generators of `C₁`.  Equivalently, the place
of `C₁` cut out by `v` lies over an affine place of `C₂` (so it is *not* `∞` of `C₁`, where `x₁`,
`y₁` have their poles).  This packages the place-identification `B`-prime ↔ affine point of `C₁`
(over the affine part of `C₂`) that the localized `LocalizedDictionary.pointAt` provides only off a
denominator locus; the global version requires `hreg` (to exclude `∞`) plus the place classification
of `C₁`.  Stated as a named hypothesis so that the integrality reduction below is structural.

**Reduction (this file).**  This residual is now *derived* from the sharper, single-content
hypothesis `BPrimePlaceClassification` (the curve-completeness statement: every `B`-prime valuation
is a point valuation or the `∞`-place) together with the basepoint-regularity `OrdAtInftyReg`, via
`bPrimeValuationCoordGenLeOne_of_classification_of_reg`.  The geometric `∞`-exclusion half is
discharged here (`bPrime_valuation_ne_ordAtInfty`, from the ramification-at-`∞` pullback formula),
leaving `BPrimePlaceClassification` as the *only* genuine remaining input. -/
def BPrimeValuationCoordGenLeOne : Prop :=
  ∀ v : IsDedekindDomain.HeightOneSpectrum (B (C₁ := C₁) (C₂ := C₂)),
    v.valuation C₁.FunctionField (coordXFun C₁) ≤ 1 ∧
    v.valuation C₁.FunctionField (coordYFun C₁) ≤ 1

/-- **The sharp irreducible place classification (the genuine remaining wall)**: the valuation of
every height-one prime `v` of `B`, as a valuation on `K(C₁)`, is *either* a point valuation
`C₁.pointValuation P` (the affine case) *or* the place at infinity `C₁.ordAtInftyValuation` (the
`∞` case).  This is the function-field completeness statement for the smooth curve `C₁` (every
`F`-trivial DVR of `K(C₁)` is a point or `∞`), restricted to `B`-primes — the project's standing
place-classification wall in its sharpest form.  Note: the `∞` alternative is *vacuous* once `hreg`
is in play (`exists_smoothPoint_under` plus the ramification-at-`∞` pullback formula exclude it at
the concrete isogeny level), so this is exactly the missing content of
`BPrimeValuationCoordGenLeOne`. -/
def BPrimePlaceClassification : Prop :=
  ∀ v : IsDedekindDomain.HeightOneSpectrum (B (C₁ := C₁) (C₂ := C₂)),
    (∃ P : C₁.SmoothPoint, v.valuation C₁.FunctionField = C₁.pointValuation P) ∨
      v.valuation C₁.FunctionField = C₁.ordAtInftyValuation

/-- **The reduction of the place dictionary to its sharp form** (structural, axiom-clean): given the
place classification `BPrimePlaceClassification` *and* the `∞`-exclusion `hinf` (no `B`-prime is the
place at infinity of `C₁`), the place-dictionary residual `BPrimeValuationCoordGenLeOne` follows.
In the point case the coordinate generators are regular (they are `algebraMap`-images of
coordinate-ring elements, `pointValuation_algebraMap_le_one`); the `∞` case is excluded by `hinf`.

This isolates the genuine content into the two clean hypotheses: the *curve-completeness*
classification `BPrimePlaceClassification` (no `hreg`), and the *geometric* `∞`-exclusion `hinf`
(discharged at the concrete isogeny level by the ramification-at-`∞` pullback formula, where the
pullback of `coordX C₂` — a base-ring element, hence `v`-integral — has a pole at `∞` of `C₁`). -/
theorem bPrimeValuationCoordGenLeOne_of_classification
    (hclass : BPrimePlaceClassification (C₁ := C₁) (C₂ := C₂))
    (hinf : ∀ v : IsDedekindDomain.HeightOneSpectrum (B (C₁ := C₁) (C₂ := C₂)),
      v.valuation C₁.FunctionField ≠ C₁.ordAtInftyValuation) :
    BPrimeValuationCoordGenLeOne (C₁ := C₁) (C₂ := C₂) := by
  intro v
  rcases hclass v with ⟨P, hP⟩ | hP
  · rw [hP]
    exact ⟨C₁.pointValuation_algebraMap_le_one _ P, C₁.pointValuation_algebraMap_le_one _ P⟩
  · exact absurd hP (hinf v)

/-- **Structural valuative-criterion reduction**: an element `z ∈ K(C₁)` lies in `B` as soon as it
is `v`-integral (valuation `≤ 1`) at every height-one prime `v` of `B`.  Direct from mathlib's
`mem_integers_of_valuation_le_one` for the Dedekind domain `B` with fraction field `K(C₁)`, plus
the subalgebra-membership ↔ `algebraMap`-range translation. -/
theorem mem_B_of_forall_valuation_le_one (z : C₁.FunctionField)
    (hz : ∀ v : IsDedekindDomain.HeightOneSpectrum (B (C₁ := C₁) (C₂ := C₂)),
      v.valuation C₁.FunctionField z ≤ 1) :
    z ∈ (B (C₁ := C₁) (C₂ := C₂)) := by
  have hmem : z ∈ (algebraMap (B (C₁ := C₁) (C₂ := C₂)) C₁.FunctionField).range :=
    IsDedekindDomain.HeightOneSpectrum.mem_integers_of_valuation_le_one C₁.FunctionField z hz
  obtain ⟨⟨y, hy⟩, rfl⟩ := hmem
  exact hy

/-! #### The place-classification structural facts for `B`-primes (reusable, axiom-clean)

The following lemmas are the *structural half* of the global-`B` place dictionary: they pin down
the relationship between a height-one prime `v` of `B` and the curve geometry, *without* the
coordinate-ring membership (so non-circular, available before `BPrimeValuationCoordGenLeOne`).

The decisive structural fact is the **center on `C₂`**: every height-one prime of `B` lies over a
*nonzero* (hence maximal, hence a smooth point `Q`) prime of `C₂.CoordinateRing` — because the only
prime of the *affine* coordinate ring `C₂.CoordinateRing` below `⊥` is `⊥`, and `B`-primes are
nonzero.  This is what excludes the `∞`-place of `C₁` once `hreg` is in play (the `∞`-place of `C₁`
lies over the `∞`-place of `C₂`, which is *not* in `Spec C₂.CoordinateRing`).  Together with the
DVR structure of the `v`-adic valuation subring and the `valuation ≤ 1` on the base-ring image, this
reduces the place dictionary to the single irreducible classification "an `F`-trivial DVR of `K(C₁)`
that is *not* the place at `∞` is a point valuation". -/

/-- **`v`-valuation `≤ 1` on the base-ring image**: every height-one prime `v` of `B` has
`v.valuation ≤ 1` on the image of `C₂.CoordinateRing` in `K(C₁)` (these elements lie in `B`, the
base ring, so are `v`-adic integers).  Direct from `valuation_le_one`. -/
theorem valuation_algebraMap_coordinateRing_le_one
    (v : IsDedekindDomain.HeightOneSpectrum (B (C₁ := C₁) (C₂ := C₂)))
    (b : C₂.CoordinateRing) :
    v.valuation C₁.FunctionField (algebraMap C₂.CoordinateRing C₁.FunctionField b) ≤ 1 := by
  have key : algebraMap C₂.CoordinateRing C₁.FunctionField b =
      algebraMap (B (C₁ := C₁) (C₂ := C₂)) C₁.FunctionField
        (algebraMap C₂.CoordinateRing (B (C₁ := C₁) (C₂ := C₂)) b) :=
    IsScalarTower.algebraMap_apply C₂.CoordinateRing (B (C₁ := C₁) (C₂ := C₂))
      C₁.FunctionField b
  rw [key]
  exact v.valuation_le_one (K := C₁.FunctionField)
    (algebraMap C₂.CoordinateRing (B (C₁ := C₁) (C₂ := C₂)) b)

/-- **The under-prime of a `B`-prime is nonzero**: for a height-one prime `v` of `B`, the
contraction `v.asIdeal.under C₂.CoordinateRing` is `≠ ⊥`.  Because `B`-primes are nonzero and
`algebraMap C₂.CoordinateRing B` is injective (its `comap ⊥ = ⊥`). -/
theorem under_ne_bot (v : IsDedekindDomain.HeightOneSpectrum (B (C₁ := C₁) (C₂ := C₂))) :
    v.asIdeal.under C₂.CoordinateRing ≠ ⊥ := by
  intro h_eq
  exact v.ne_bot (Ideal.eq_bot_of_comap_eq_bot (R := C₂.CoordinateRing)
    (S := B (C₁ := C₁) (C₂ := C₂)) h_eq)

/-- **The center of a `B`-prime on `C₂` is a smooth point** (the affine-place restriction): every
height-one prime `v` of `B` lies over the maximal ideal `m_Q` of *some* smooth point `Q` of `C₂`.
This is the key structural fact excluding the `∞`-place: a `B`-prime never restricts to the
`∞`-place of `C₂` (which is absent from `Spec C₂.CoordinateRing`).  The under-prime is maximal
(`isMaximal_comap_of_isIntegral_of_isMaximal`, as `B/C₂.CoordinateRing` is integral) and nonzero
(`under_ne_bot`), hence a smooth point (`exists_smoothPoint_of_isMaximal`). -/
theorem exists_smoothPoint_under
    (v : IsDedekindDomain.HeightOneSpectrum (B (C₁ := C₁) (C₂ := C₂))) :
    ∃ Q : C₂.SmoothPoint, v.asIdeal.under C₂.CoordinateRing = C₂.maximalIdealAt Q := by
  haveI hPunder_max : (v.asIdeal.under C₂.CoordinateRing).IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal v.asIdeal
  obtain ⟨Q, hQ⟩ := C₂.exists_smoothPoint_of_isMaximal hPunder_max
  exact ⟨Q, hQ.symm⟩

/-- **The `v`-adic valuation subring of a `B`-prime is a DVR** (rank-one).  The `v`-adic valuation
on `K(C₁)` is surjective onto `ℤᵐ⁰` (mathlib's `valuation_surjective`), so its value group is `⊤`,
hence cyclic and nontrivial, hence the valuation subring is a discrete valuation ring
(`Valuation.valuationSubring_isDiscreteValuationRing`).  This is the rank-one input demanded by the
DVR-domination engine `rankOne_valuationSubring_le_eq_of_ne_top`. -/
theorem valuationSubring_isDVR
    (v : IsDedekindDomain.HeightOneSpectrum (B (C₁ := C₁) (C₂ := C₂))) :
    IsDiscreteValuationRing (v.valuation C₁.FunctionField).valuationSubring :=
  valuationSubring_isDVR_of_surjective_withZeroInt _ (v.valuation_surjective C₁.FunctionField)

/-- The coercion `ℤ → WithTop ℤ` commutes with `nsmul`. -/
private theorem coe_nsmul_int (k : ℕ) (a : ℤ) :
    (k • ((a : ℤ) : WithTop ℤ)) = ((((k : ℤ) * a : ℤ)) : WithTop ℤ) := by
  induction k with
  | zero => simp
  | succ n ih => rw [succ_nsmul, ih, ← WithTop.coe_add]; congr 1; push_cast; ring

/-- **`v` ≤ 1 on the pullback of `coordX C₂`** (the base-ring input to the `∞`-exclusion): for every
height-one prime `v` of `B`, the image `φ^* coordX₂ = algebraMap K(C₂) K(C₁) (coordX C₂)` is a
base-ring element of `B`, hence a `v`-adic integer.  Routes the image through `C₂.CoordinateRing`
(where `valuation_algebraMap_coordinateRing_le_one` applies): `coordX C₂ = algMap_{C₂.CR→K(C₁)}
(mk (C X))` via the coordinate-ring tower. -/
private theorem valuation_pullback_coordX₂_le_one
    (v : IsDedekindDomain.HeightOneSpectrum (B (C₁ := C₁) (C₂ := C₂))) :
    v.valuation C₁.FunctionField
      (algebraMap C₂.FunctionField C₁.FunctionField C₂.coordX) ≤ 1 := by
  have hcr : algebraMap C₂.CoordinateRing C₁.FunctionField
        (WeierstrassCurve.Affine.CoordinateRing.mk C₂.toAffine (Polynomial.C Polynomial.X)) =
      algebraMap C₂.FunctionField C₁.FunctionField C₂.coordX := by
    rw [SmoothPlaneCurve.coordX,
      IsScalarTower.algebraMap_apply C₂.CoordinateRing C₂.FunctionField C₁.FunctionField]
    rfl
  rw [← hcr]
  exact valuation_algebraMap_coordinateRing_le_one v _

/-- **The ramified pole of `φ^* coordX₂` at `∞` of `C₁`, from regularity**: given `OrdAtInftyReg`
(`hreg`), there is a ramification index `e ≥ 1` at `∞` with `ord_∞^{C₁}(φ^* coordX₂) = e·(−2)`.
Combines the pullback ramification formula `ord_∞^{C₁}(φ^* g) = e·ord_∞^{C₂}(g)`
(`exists_pos_ramificationIdx_ordAtInfty_ringHom_of_isAlgebraic`, with `e ≥ 1` and `K(C₁)/K(C₂)`
algebraic from finiteness) with `ord_∞^{C₂}(coordX₂) = −2` (`ordAtInfty_coordX`). -/
private theorem exists_pos_ramificationIdx_pole_pullback_coordX₂
    (hreg : OrdAtInftyReg (C₁ := C₁) (C₂ := C₂)) :
    ∃ e : ℕ, 1 ≤ e ∧ C₁.ordAtInfty (algebraMap C₂.FunctionField C₁.FunctionField C₂.coordX) =
      ((((e : ℤ) * (-2 : ℤ)) : ℤ) : WithTop ℤ) := by
  -- the ramification index `e ≥ 1` at `∞`, from `hreg` + algebraicity (finiteness)
  obtain ⟨e, he, hform⟩ :
      ∃ e : ℕ, 1 ≤ e ∧ ∀ g : C₂.FunctionField, g ≠ 0 →
        C₁.ordAtInfty (algebraMap C₂.FunctionField C₁.FunctionField g) = e • C₂.ordAtInfty g := by
    have halg : letI : Algebra C₂.FunctionField C₁.FunctionField := algKL
        IsAlgebraic C₂.FunctionField C₁.coordX :=
      Algebra.IsAlgebraic.isAlgebraic C₁.coordX
    exact SmoothPlaneCurve.exists_pos_ramificationIdx_ordAtInfty_ringHom_of_isAlgebraic
      (algebraMap C₂.FunctionField C₁.FunctionField) hreg halg
  -- the pole of `φ^* coordX₂` at `∞` of `C₁`: `ord_∞ = e·(-2) < 0`
  exact ⟨e, he, by rw [hform C₂.coordX C₂.coordX_ne_zero, C₂.ordAtInfty_coordX, coe_nsmul_int]⟩

/-- **A ramified pole is negative in `ℤᵐ⁰`**: for `e ≥ 1`, the value `e·(−2)` is not `≥ 0` in
`WithTop ℤ`.  The arithmetic core of the `∞`-exclusion: `ord_∞ ≥ 0` (the `≤ 1`/integrality
condition) is incompatible with a strictly-negative ramified pole. -/
private theorem not_zero_le_coe_mul_neg_two {e : ℕ} (he : 1 ≤ e) :
    ¬ (0 : WithTop ℤ) ≤ ((((e : ℤ) * (-2 : ℤ)) : ℤ) : WithTop ℤ) := by
  rw [show (0 : WithTop ℤ) = ((0 : ℤ) : WithTop ℤ) from rfl, WithTop.coe_le_coe]
  have : (1 : ℤ) ≤ e := by exact_mod_cast he
  omega

/-- **The `∞`-exclusion `hinf`, discharged from regularity** (axiom-clean): given `OrdAtInftyReg`
(`hreg`, the basepoint-regularity carried by an isogeny), *no* height-one prime `v` of `B` has
`v.valuation = C₁.ordAtInftyValuation`.  This is the geometric content excluding the place at
infinity of `C₁`, and it is *provable* (not residual): the coordinate generator `coordX C₂` is a
base-ring element of `B`, so `v` is `≤ 1` on its image (`valuation_algebraMap_coordinateRing_le_one`);
were `v` the `∞`-place, this would force `ord_∞^{C₁}(φ^* coordX₂) ≥ 0`.  But the
ramification-at-`∞` pullback formula (`exists_pos_ramificationIdx_ordAtInfty_ringHom_of_isAlgebraic`,
with `e ≥ 1` and `K(C₁)/K(C₂)` algebraic from finiteness) gives
`ord_∞^{C₁}(φ^* coordX₂) = e · ord_∞^{C₂}(coordX₂) = e · (−2) < 0` — a contradiction. -/
theorem bPrime_valuation_ne_ordAtInfty (hreg : OrdAtInftyReg (C₁ := C₁) (C₂ := C₂))
    (v : IsDedekindDomain.HeightOneSpectrum (B (C₁ := C₁) (C₂ := C₂))) :
    v.valuation C₁.FunctionField ≠ C₁.ordAtInftyValuation := by
  intro hv
  -- `coordX₂` image is a base-ring element of `B`, so `v ≤ 1` on it; with `v = ordAtInftyValuation`
  -- this forces `ord_∞^{C₁}(φ^* coordX₂) ≥ 0`
  have hle := valuation_pullback_coordX₂_le_one v
  rw [hv] at hle
  have halg_ne : algebraMap C₂.FunctionField C₁.FunctionField C₂.coordX ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective C₂.FunctionField C₁.FunctionField)]
    exact C₂.coordX_ne_zero
  -- but the ramified pole `ord_∞^{C₁}(φ^* coordX₂) = e·(-2) < 0` (`e ≥ 1` from `hreg`) contradicts it
  obtain ⟨e, he, hpole⟩ := exists_pos_ramificationIdx_pole_pullback_coordX₂ hreg
  rw [C₁.ordAtInftyValuation_le_one_iff_ordAtInfty_nonneg halg_ne, hpole] at hle
  exact not_zero_le_coe_mul_neg_two he hle

/-! ### The point case of the place classification (curve-completeness, affine half)

If a height-one prime `v` of `B` has `v`-valuation `≤ 1` on *both* coordinate generators
`x₁ = coordXFun C₁`, `y₁ = coordYFun C₁` of `C₁`, then the whole coordinate ring `F[C₁] = F[x₁, y₁]`
lands in the `v`-adic integers `O_v`, and `v` *is* the point valuation at a smooth point `P` of `C₁`.

The point `P` is the center of `v` on `C₁`: the contraction `c := {a ∈ F[C₁] | v(a) < 1}` is a
nonzero prime (nonzero because `v` is nontrivial on `K(C₁) = Frac F[C₁]`, prime because it is the
preimage of the `v`-adic maximal ideal), hence — `F[C₁]` being a Dedekind domain — maximal, hence
`maximalIdealAt P` for a smooth `F`-rational point `P` (`exists_smoothPoint_of_isMaximal`).  Then the
local ring `O_P = (F[C₁])_{m_P}` sits inside `O_v` (a fraction `a/s` with `s ∉ m_P = c` has
`v(s) = 1`, so `v(a/s) = v(a) ≤ 1`), i.e. `O_{pointValuation P} ⊆ O_v`.  The point valuation subring
`O_{pointValuation P}` is rank-one (a DVR), so the DVR-domination engine
`rankOne_valuationSubring_le_eq_of_ne_top` forces `O_{pointValuation P} = O_v`, whence the two
(surjective `ℤᵐ⁰`-valued) valuations are equal. -/

/-- **`v` ≤ 1 on the whole coordinate ring of `C₁`, from the two generators** (the affine-center
input): if the height-one prime `v` of `B` is `≤ 1` on `coordXFun C₁` and `coordYFun C₁`, then it is
`≤ 1` on the image of *every* element of `C₁.CoordinateRing`.  Mirrors
`LocalizedDictionary.coordRing_mem_integralClosure` with `O_v` in place of the integral closure:
`F[C₁] = F[x₁, y₁]` is generated by the two coordinate classes over `F`, and `F`-constants are
base-ring elements of `B` (hence `v`-integral, `valuation_algebraMap_coordinateRing_le_one`). -/
theorem valuation_algebraMap_coordinateRing_C₁_le_one
    (v : IsDedekindDomain.HeightOneSpectrum (B (C₁ := C₁) (C₂ := C₂)))
    (hx : v.valuation C₁.FunctionField (coordXFun C₁) ≤ 1)
    (hy : v.valuation C₁.FunctionField (coordYFun C₁) ≤ 1)
    (r : C₁.CoordinateRing) :
    v.valuation C₁.FunctionField (algebraMap C₁.CoordinateRing C₁.FunctionField r) ≤ 1 := by
  set w := v.valuation C₁.FunctionField with hw
  obtain ⟨g, rfl⟩ := AdjoinRoot.mk_surjective r
  induction g using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add, map_add]
    exact le_trans (w.map_add _ _) (max_le hp hq)
  | monomial n a =>
    rw [← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_mul, map_pow, map_pow, w.map_mul,
      map_pow w]
    refine mul_le_one' ?_ (pow_le_one₀ zero_le hy)
    induction a using Polynomial.induction_on' with
    | add p q hp hq =>
      rw [Polynomial.C_add, map_add, map_add]
      exact le_trans (w.map_add _ _) (max_le hp hq)
    | monomial m c =>
      rw [← Polynomial.C_mul_X_pow_eq_monomial, Polynomial.C_mul, Polynomial.C_pow,
        map_mul, map_mul, map_pow, map_pow, w.map_mul, map_pow w]
      refine mul_le_one' ?_ (pow_le_one₀ zero_le hx)
      -- the `F`-constant `c`: a base-ring element of `B`, hence `v`-integral.  Route the
      -- `F`-constant through `C₂.CoordinateRing` (where `valuation_algebraMap_coordinateRing_le_one`
      -- applies): `(mk (C (C c)))_{C₁} = algMap_F c = algMap_{C₂.CR}(algMap_F c)` via the towers.
      have hc : algebraMap C₁.CoordinateRing C₁.FunctionField
          (AdjoinRoot.mk C₁.toAffine.polynomial (Polynomial.C (Polynomial.C c))) =
          algebraMap C₂.CoordinateRing C₁.FunctionField (algebraMap F C₂.CoordinateRing c) := by
        rw [show (AdjoinRoot.mk C₁.toAffine.polynomial (Polynomial.C (Polynomial.C c)) :
              C₁.CoordinateRing) = algebraMap F C₁.CoordinateRing c from rfl,
          ← IsScalarTower.algebraMap_apply F C₁.CoordinateRing C₁.FunctionField,
          IsScalarTower.algebraMap_apply F C₂.FunctionField C₁.FunctionField,
          IsScalarTower.algebraMap_apply F C₂.CoordinateRing C₂.FunctionField,
          ← IsScalarTower.algebraMap_apply C₂.CoordinateRing C₂.FunctionField C₁.FunctionField]
      rw [hc]
      exact valuation_algebraMap_coordinateRing_le_one v _

/-- **The center ideal of a `B`-prime on `C₁`** (in the point case): the contraction
`c_v := {a ∈ F[C₁] | v(a) < 1}` of the `v`-adic maximal ideal to `C₁.CoordinateRing`.  It is an ideal
(preimage of the maximal ideal of `O_v` under `F[C₁] → O_v ⊆ K(C₁)`): closed under addition by the
non-archimedean inequality, and an ideal because `v ≤ 1` on the whole coordinate ring
(`valuation_algebraMap_coordinateRing_C₁_le_one`). -/
noncomputable def centerIdealOnC₁
    (v : IsDedekindDomain.HeightOneSpectrum (B (C₁ := C₁) (C₂ := C₂)))
    (hx : v.valuation C₁.FunctionField (coordXFun C₁) ≤ 1)
    (hy : v.valuation C₁.FunctionField (coordYFun C₁) ≤ 1) :
    Ideal C₁.CoordinateRing where
  carrier := {a | v.valuation C₁.FunctionField
    (algebraMap C₁.CoordinateRing C₁.FunctionField a) < 1}
  add_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq, map_add] at ha hb ⊢
    exact lt_of_le_of_lt ((v.valuation C₁.FunctionField).map_add _ _) (max_lt ha hb)
  zero_mem' := by simp only [Set.mem_setOf_eq, map_zero, map_zero]; exact zero_lt_one' _
  smul_mem' r a ha := by
    simp only [Set.mem_setOf_eq, smul_eq_mul, map_mul, (v.valuation C₁.FunctionField).map_mul] at ha ⊢
    calc v.valuation C₁.FunctionField (algebraMap C₁.CoordinateRing C₁.FunctionField r) *
            v.valuation C₁.FunctionField (algebraMap C₁.CoordinateRing C₁.FunctionField a)
          ≤ 1 * v.valuation C₁.FunctionField
              (algebraMap C₁.CoordinateRing C₁.FunctionField a) :=
            mul_le_mul_left (valuation_algebraMap_coordinateRing_C₁_le_one v hx hy r) _
      _ < 1 := by rw [one_mul]; exact ha

@[simp] theorem mem_centerIdealOnC₁
    (v : IsDedekindDomain.HeightOneSpectrum (B (C₁ := C₁) (C₂ := C₂)))
    (hx : v.valuation C₁.FunctionField (coordXFun C₁) ≤ 1)
    (hy : v.valuation C₁.FunctionField (coordYFun C₁) ≤ 1)
    (a : C₁.CoordinateRing) :
    a ∈ centerIdealOnC₁ v hx hy ↔
      v.valuation C₁.FunctionField (algebraMap C₁.CoordinateRing C₁.FunctionField a) < 1 :=
  Iff.rfl

/-- **A surjective `ℤᵐ⁰`-valued valuation is nontrivial.**  Surjectivity hits `exp 1`, an element
with valuation `≠ 0, 1`.  The shared rank-one input to the DVR-domination step (`O ≠ ⊤`), used by
both the point case and the `∞` case of the place classification below. -/
private theorem isNontrivial_of_surjective_withZeroInt
    (w : Valuation C₁.FunctionField (WithZero (Multiplicative ℤ)))
    (hwsurj : Function.Surjective w) :
    w.IsNontrivial := by
  refine ⟨?_⟩
  obtain ⟨z, hz⟩ := hwsurj (WithZero.exp (1 : ℤ))
  refine ⟨z, ?_, ?_⟩
  · rw [hz]; exact WithZero.exp_ne_zero
  · rw [hz, show (1 : WithZero (Multiplicative ℤ)) = WithZero.exp (0 : ℤ) from
      (WithZero.exp_zero).symm, Ne, WithZero.exp_inj]; norm_num

/-- **The valuation subring of a surjective `ℤᵐ⁰`-valued valuation is proper** (`≠ ⊤`).  Direct from
nontriviality (`isNontrivial_of_surjective_withZeroInt`) via `valuationSubring_eq_top_iff`. -/
private theorem valuationSubring_ne_top_of_surjective
    (w : Valuation C₁.FunctionField (WithZero (Multiplicative ℤ)))
    (hwsurj : Function.Surjective w) :
    w.valuationSubring ≠ ⊤ := fun htop =>
  (Valuation.valuationSubring_eq_top_iff _).mp htop
    (isNontrivial_of_surjective_withZeroInt w hwsurj)

/-- **The center ideal of a `B`-prime on `C₁` is prime** (point case): `centerIdealOnC₁ v hx hy` is a
prime ideal.  Properness is `w 1 = 1 ≮ 1`; primality is the non-archimedean factorisation
`w(ab) = w a · w b < 1`, which forces one factor `< 1` since both are `≤ 1`
(`valuation_algebraMap_coordinateRing_C₁_le_one`). -/
private theorem centerIdealOnC₁_isPrime
    (v : IsDedekindDomain.HeightOneSpectrum (B (C₁ := C₁) (C₂ := C₂)))
    (hx : v.valuation C₁.FunctionField (coordXFun C₁) ≤ 1)
    (hy : v.valuation C₁.FunctionField (coordYFun C₁) ≤ 1) :
    (centerIdealOnC₁ v hx hy).IsPrime := by
  set w := v.valuation C₁.FunctionField with hw
  refine ⟨?_, ?_⟩
  · rw [Ideal.ne_top_iff_one, mem_centerIdealOnC₁, map_one, map_one]
    exact lt_irrefl 1
  · intro a b hab
    rw [mem_centerIdealOnC₁, map_mul, w.map_mul] at hab
    by_contra h
    push_neg at h
    obtain ⟨ha, hb⟩ := h
    rw [mem_centerIdealOnC₁, not_lt] at ha hb
    have ha1 : w (algebraMap C₁.CoordinateRing C₁.FunctionField a) = 1 :=
      le_antisymm (valuation_algebraMap_coordinateRing_C₁_le_one v hx hy a) ha
    have hb1 : w (algebraMap C₁.CoordinateRing C₁.FunctionField b) = 1 :=
      le_antisymm (valuation_algebraMap_coordinateRing_C₁_le_one v hx hy b) hb
    rw [ha1, hb1, one_mul] at hab
    exact lt_irrefl 1 hab

/-- **The center ideal of a `B`-prime on `C₁` is nonzero** (point case): `centerIdealOnC₁ v hx hy ≠ ⊥`.
Otherwise `w (algMap a) = 1` for every nonzero `a ∈ F[C₁]` (such an `a` would lie in the center if
`< 1`), hence `w f = 1` for every `f ∈ K(C₁) = Frac F[C₁]` (write `f = a/b`) — contradicting that the
surjective `w` takes the value `exp 1 ≠ 1`. -/
private theorem centerIdealOnC₁_ne_bot
    (v : IsDedekindDomain.HeightOneSpectrum (B (C₁ := C₁) (C₂ := C₂)))
    (hx : v.valuation C₁.FunctionField (coordXFun C₁) ≤ 1)
    (hy : v.valuation C₁.FunctionField (coordYFun C₁) ≤ 1) :
    centerIdealOnC₁ v hx hy ≠ ⊥ := by
  set w := v.valuation C₁.FunctionField with hw
  have hwsurj : Function.Surjective w := v.valuation_surjective C₁.FunctionField
  intro hc0
  -- `c = ⊥` ⟹ every nonzero coordinate-ring element has `w (algMap ·) = 1`
  have hunit : ∀ a : C₁.CoordinateRing, a ≠ 0 →
      w (algebraMap C₁.CoordinateRing C₁.FunctionField a) = 1 := by
    intro a ha0
    refine le_antisymm (valuation_algebraMap_coordinateRing_C₁_le_one v hx hy a) ?_
    by_contra hlt
    rw [not_le] at hlt
    exact ha0 ((Submodule.eq_bot_iff _).mp hc0 a
      ((mem_centerIdealOnC₁ v hx hy a).mpr hlt))
  -- pick `f` with `w f ≠ 1` (surjectivity onto `ℤᵐ⁰`), then derive `w f = 1` — contradiction
  obtain ⟨f, hf⟩ := hwsurj (WithZero.exp (1 : ℤ))
  have hf1 : w f ≠ 1 := by
    rw [hf, show (1 : WithZero (Multiplicative ℤ)) = WithZero.exp (0 : ℤ) from
      (WithZero.exp_zero).symm, Ne, WithZero.exp_inj]
    norm_num
  apply hf1
  obtain ⟨a, b, hb_mem, hfab⟩ :=
    IsFractionRing.div_surjective (A := C₁.CoordinateRing) f
  have hb_ne : b ≠ 0 := nonZeroDivisors.ne_zero hb_mem
  have hb_map_ne : algebraMap C₁.CoordinateRing C₁.FunctionField b ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective C₁.CoordinateRing C₁.FunctionField)).mpr hb_ne
  -- if `a = 0` then `f = 0`, but `w f = exp 1 ≠ 0`; so `a ≠ 0`
  have ha_ne : a ≠ 0 := by
    rintro rfl
    rw [map_zero, zero_div] at hfab
    rw [← hfab, map_zero] at hf
    exact WithZero.exp_ne_zero hf.symm
  rw [← hfab, map_div₀ w, hunit a ha_ne, hunit b hb_ne, div_one]

/-- **The center ideal of a `B`-prime on `C₁` is maximal** (point case): a nonzero prime in the
Dedekind domain `F[C₁]` (which needs `[IsIntegrallyClosed C₁.CoordinateRing]`).  Combines
`centerIdealOnC₁_isPrime` and `centerIdealOnC₁_ne_bot` via `IsPrime.isMaximal`. -/
private theorem centerIdealOnC₁_isMaximal [IsIntegrallyClosed C₁.CoordinateRing]
    (v : IsDedekindDomain.HeightOneSpectrum (B (C₁ := C₁) (C₂ := C₂)))
    (hx : v.valuation C₁.FunctionField (coordXFun C₁) ≤ 1)
    (hy : v.valuation C₁.FunctionField (coordYFun C₁) ≤ 1) :
    (centerIdealOnC₁ v hx hy).IsMaximal :=
  (centerIdealOnC₁_isPrime v hx hy).isMaximal (centerIdealOnC₁_ne_bot v hx hy)

/-- **The point local ring of `C₁` sits inside the `v`-adic integers** (point case): if the center of
`v` on `C₁` is the maximal ideal at the smooth point `P` (`hP`), then
`O_{pointValuation P} ⊆ O_v`.  A `pointValuation P`-integer is `algMap (localRingAt P) x` with
`x = mk' a s`, `s ∉ m_P`; since `m_P = centerIdealOnC₁ v`, `s` is *not* in the center so
`w (algMap s) = 1`, whence `w (algMap a / algMap s) = w (algMap a) ≤ 1`
(`valuation_algebraMap_coordinateRing_C₁_le_one`). -/
private theorem pointValuationSubring_le_valuationSubring
    (v : IsDedekindDomain.HeightOneSpectrum (B (C₁ := C₁) (C₂ := C₂)))
    (hx : v.valuation C₁.FunctionField (coordXFun C₁) ≤ 1)
    (hy : v.valuation C₁.FunctionField (coordYFun C₁) ≤ 1)
    {P : C₁.SmoothPoint} (hP : centerIdealOnC₁ v hx hy = C₁.maximalIdealAt P) :
    (C₁.pointValuation P).valuationSubring ≤ (v.valuation C₁.FunctionField).valuationSubring := by
  set w := v.valuation C₁.FunctionField with hw
  intro f hf
  -- `f ∈ Bv` ⟺ `f = algMap (localRingAt P) x` for some `x`
  obtain ⟨x, hx_eq⟩ := (SmoothPlaneCurve.mem_localRingAt_image_iff_pointValuation_le_one f).mpr
    ((Valuation.mem_valuationSubring_iff _ f).mp hf)
  -- write `x = mk' a s`, with `sv := (s : F[C₁])` avoiding the prime `m_P`
  obtain ⟨a, s, hxas⟩ := IsLocalization.exists_mk'_eq
    (C₁.maximalIdealAt P).primeCompl x
  set sv : C₁.CoordinateRing := (s : C₁.CoordinateRing) with hsv
  -- `sv ∉ m_P` (it is in the prime complement)
  have hs_notin : sv ∉ C₁.maximalIdealAt P := Ideal.mem_primeCompl_iff.mp s.2
  -- `algMap_CR sv ≠ 0` (`sv ≠ 0`, it avoids the prime)
  have hs_ne : sv ≠ 0 := fun h => hs_notin (h ▸ Submodule.zero_mem _)
  have hs_map_ne : algebraMap C₁.CoordinateRing C₁.FunctionField sv ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective C₁.CoordinateRing C₁.FunctionField)).mpr hs_ne
  -- `f = algMap_CR a / algMap_CR sv`, via `mk'_spec` pushed through `localRingAt P → FF`.
  have hf_eq : f = algebraMap C₁.CoordinateRing C₁.FunctionField a /
      algebraMap C₁.CoordinateRing C₁.FunctionField sv := by
    rw [eq_div_iff hs_map_ne, ← hx_eq, ← hxas,
      IsScalarTower.algebraMap_apply C₁.CoordinateRing (C₁.localRingAt P) C₁.FunctionField sv,
      IsScalarTower.algebraMap_apply C₁.CoordinateRing (C₁.localRingAt P) C₁.FunctionField a,
      ← map_mul]
    congr 1
    exact IsLocalization.mk'_spec (C₁.localRingAt P) a s
  -- `w (algMap sv) = 1`: `sv ∉ maximalIdealAt P = c`, so `¬ (w (algMap sv) < 1)`, and `≤ 1`
  have hws : w (algebraMap C₁.CoordinateRing C₁.FunctionField sv) = 1 := by
    refine le_antisymm (valuation_algebraMap_coordinateRing_C₁_le_one v hx hy sv) ?_
    by_contra hlt
    rw [not_le] at hlt
    have hsv_in_c : sv ∈ centerIdealOnC₁ v hx hy := (mem_centerIdealOnC₁ v hx hy sv).mpr hlt
    exact hs_notin (hP ▸ hsv_in_c)
  refine (Valuation.mem_valuationSubring_iff _ f).mpr ?_
  rw [hf_eq, map_div₀ w, hws, div_one]
  exact valuation_algebraMap_coordinateRing_C₁_le_one v hx hy a

/-- **The point case of the place classification**: if a height-one prime `v` of `B` has
`v`-valuation `≤ 1` on the two coordinate generators of `C₁`, then `v` is the point valuation
`C₁.pointValuation P` at a smooth point `P` of `C₁`.  Here `[IsIntegrallyClosed C₁.CoordinateRing]`
(automatic for an elliptic curve, away from characteristics `2, 3`) is used to make `F[C₁]` a
Dedekind domain so that the nonzero prime `centerIdealOnC₁ v` is maximal.

Strategy: the center `c_v = centerIdealOnC₁ v` is a nonzero prime (nonzero because `v` is nontrivial
on `K(C₁)`; prime as the contraction of the `v`-adic maximal ideal), hence maximal, hence
`maximalIdealAt P`.  The local ring `O_P = F[C₁]_{m_P}` lands in `O_v` (a fraction `a/s`,
`s ∉ m_P = c_v`, has `v(s) = 1`), so the rank-one DVR `O_{pointValuation P}` dominates downward into
`O_v`, forcing equality of the valuation subrings (`rankOne_valuationSubring_le_eq_of_ne_top`) and
hence of the two surjective `ℤᵐ⁰`-valued valuations. -/
theorem bPrime_valuation_eq_pointValuation_of_coordGen_le_one
    [IsIntegrallyClosed C₁.CoordinateRing]
    (v : IsDedekindDomain.HeightOneSpectrum (B (C₁ := C₁) (C₂ := C₂)))
    (hx : v.valuation C₁.FunctionField (coordXFun C₁) ≤ 1)
    (hy : v.valuation C₁.FunctionField (coordYFun C₁) ≤ 1) :
    ∃ P : C₁.SmoothPoint, v.valuation C₁.FunctionField = C₁.pointValuation P := by
  classical
  set w := v.valuation C₁.FunctionField with hw
  have hwsurj : Function.Surjective w := v.valuation_surjective C₁.FunctionField
  -- The center `c = centerIdealOnC₁ v` is a nonzero prime, hence maximal, hence `m_P` at a point `P`.
  obtain ⟨P, hP⟩ := C₁.exists_smoothPoint_of_isMaximal (centerIdealOnC₁_isMaximal v hx hy)
  refine ⟨P, ?_⟩
  -- `O_{pointValuation P}` is a rank-one DVR sitting inside the `v`-adic integers `O_v`.
  haveI : IsDiscreteValuationRing (C₁.pointValuation P).valuationSubring :=
    valuationSubring_isDVR_of_surjective_withZeroInt _
      ((IsDiscreteValuationRing.maximalIdeal (C₁.localRingAt P)).valuation_surjective
        C₁.FunctionField)
  have hBA : (C₁.pointValuation P).valuationSubring ≤ w.valuationSubring :=
    pointValuationSubring_le_valuationSubring v hx hy hP.symm
  -- DVR-domination forces the subrings (`O_v ≠ ⊤` as `w` is nontrivial) and hence the valuations equal.
  have hEq : (C₁.pointValuation P).valuationSubring = w.valuationSubring :=
    rankOne_valuationSubring_le_eq_of_ne_top _ _ hBA
      (valuationSubring_ne_top_of_surjective w hwsurj)
  refine Valuation.isEquiv_iff_eq_of_surjective_withZeroInt _ _ hwsurj
    ((IsDiscreteValuationRing.maximalIdeal (C₁.localRingAt P)).valuation_surjective
      C₁.FunctionField) ?_
  rw [Valuation.isEquiv_iff_valuationSubring]; exact hEq.symm

/-! ### The ∞ case of the place classification (curve-completeness, infinity half)

If a height-one prime `v` of `B` has a *pole* of `coordXFun C₁` (`1 < v(x₁)`), then `v` is the place
at infinity `ordAtInftyValuation`.  The structural reduction below
(`bPrime_valuation_eq_ordAtInfty_of_subring_le`) packages `ordAtInftyValuation` as the rank-one
valuation it is and runs the same DVR-domination as the point case, *given* the valuation-subring
inclusion `O_v ⊆ O_∞` — i.e. `v(g) ≤ 1 → 0 ≤ ord_∞ g` for all `g`.

**That inclusion is the genuine remaining content** (the project's standing curve-completeness wall in
its sharpest, fully-isolated form).  It is the statement that a `v`-integral function is regular at
`∞`, for a `B`-prime `v` whose center on `C₁` is at infinity (`1 < v(x₁)`).  Equivalently it is the
*uniqueness of the place of `K(C₁)` over the `∞`-place of `F(x₁)`* — the fundamental identity
`Σ e·f = [K(C₁) : F(x₁)] = 2` with the `∞`-place totally accounting for it (`e = 2`, `f = 1`, one
point at infinity).  The `RamificationAtInfinity.Sinf` machinery (`finrank_eq_sum_ramificationIdx_…`)
is the intended vehicle, but `ordAtInftyValuation` is *not* packaged as the adic valuation of a local
ring at `∞` in the project (it is the degree-based `−intDegree ∘ N`), so the center-domination route
that closes the point case has no `∞` analogue without first building that packaging.  This is
isolated as the named hypothesis `hsub` below. -/

/-- **The ∞ case of the place classification, structural reduction**: given the valuation-subring
inclusion `O_v ⊆ O_∞` (`hsub`), a height-one prime `v` of `B` *is* the place at infinity.  Mirrors
the point case: `O_v` is a rank-one DVR, `O_∞ ≠ ⊤` (`ordAtInftyValuation` nontrivial), so
`rankOne_valuationSubring_le_eq_of_ne_top` forces `O_v = O_∞`, and the two surjective `ℤᵐ⁰`-valued
valuations are equal. -/
theorem bPrime_valuation_eq_ordAtInfty_of_subring_le
    (v : IsDedekindDomain.HeightOneSpectrum (B (C₁ := C₁) (C₂ := C₂)))
    (hsub : (v.valuation C₁.FunctionField).valuationSubring ≤
      C₁.ordAtInftyValuation.valuationSubring) :
    v.valuation C₁.FunctionField = C₁.ordAtInftyValuation := by
  set w := v.valuation C₁.FunctionField with hw
  have hwsurj : Function.Surjective w := v.valuation_surjective C₁.FunctionField
  haveI : IsDiscreteValuationRing w.valuationSubring := valuationSubring_isDVR v
  -- DVR-domination (`O_∞ ≠ ⊤`, as `ordAtInftyValuation` is surjective onto `ℤᵐ⁰`): `O_v = O_∞`,
  -- then upgrade equal subrings to the value identity.
  have hEq : w.valuationSubring = C₁.ordAtInftyValuation.valuationSubring :=
    rankOne_valuationSubring_le_eq_of_ne_top _ _ hsub
      (valuationSubring_ne_top_of_surjective _ C₁.ordAtInftyValuation_surjective)
  refine Valuation.isEquiv_iff_eq_of_surjective_withZeroInt _ _ hwsurj
    C₁.ordAtInftyValuation_surjective ?_
  rw [Valuation.isEquiv_iff_valuationSubring]; exact hEq

/-- **The ∞ case of the place classification, structural reduction (natural direction)**: given the
valuation-subring inclusion `O_∞ ⊆ O_v` (`hsup`), a height-one prime `v` of `B` *is* the place at
infinity.  This is the direction an eventual proof produces naturally: the `∞`-chart integral closure
`B_∞ = integralClosure F[1/x₁] K(C₁)` is `v`-integral (`O_v` is integrally closed and contains
`1/x₁`), so `O_∞ = (B_∞)_{m_∞} ⊆ O_v`.  Here `O_∞` is the rank-one DVR, so
`rankOne_valuationSubring_le_eq_of_ne_top` forces `O_∞ = O_v` and the two surjective `ℤᵐ⁰`-valued
valuations are equal. -/
theorem bPrime_valuation_eq_ordAtInfty_of_subring_ge
    (v : IsDedekindDomain.HeightOneSpectrum (B (C₁ := C₁) (C₂ := C₂)))
    (hsup : C₁.ordAtInftyValuation.valuationSubring ≤
      (v.valuation C₁.FunctionField).valuationSubring)
    (hvtop : (v.valuation C₁.FunctionField).valuationSubring ≠ ⊤) :
    v.valuation C₁.FunctionField = C₁.ordAtInftyValuation := by
  set w := v.valuation C₁.FunctionField with hw
  have hwsurj : Function.Surjective w := v.valuation_surjective C₁.FunctionField
  -- `O_∞` is a rank-one DVR (`ordAtInftyValuation` surjective onto `ℤᵐ⁰`).
  haveI : IsDiscreteValuationRing C₁.ordAtInftyValuation.valuationSubring :=
    valuationSubring_isDVR_of_surjective_withZeroInt _ C₁.ordAtInftyValuation_surjective
  -- DVR-domination: `O_∞ = O_v`, then upgrade equal subrings to the value identity.
  have hEq : C₁.ordAtInftyValuation.valuationSubring = w.valuationSubring :=
    rankOne_valuationSubring_le_eq_of_ne_top _ _ hsup hvtop
  refine Valuation.isEquiv_iff_eq_of_surjective_withZeroInt _ _ hwsurj
    C₁.ordAtInftyValuation_surjective ?_
  rw [Valuation.isEquiv_iff_valuationSubring]; exact hEq.symm

/-- **The ∞-inclusion residual (the sharply-isolated curve-completeness wall)**: for every
height-one prime `v` of `B` that is *not* `≤ 1` on both coordinate generators of `C₁` (so its center
is at infinity), the `v`-adic valuation subring is contained in the `∞`-place subring.  Equivalently:
a `v`-integral function is regular at `∞`, for a `B`-prime `v` with a pole of `x₁` — i.e. there is a
*unique* place of `K(C₁)` over the `∞`-place of `F(x₁)`.  This is the only remaining input of the
place classification (the `∞` half); the point half is discharged unconditionally
(`bPrime_valuation_eq_pointValuation_of_coordGen_le_one`). -/
def BPrimeInftyInclusion : Prop :=
  ∀ v : IsDedekindDomain.HeightOneSpectrum (B (C₁ := C₁) (C₂ := C₂)),
    ¬ (v.valuation C₁.FunctionField (coordXFun C₁) ≤ 1 ∧
        v.valuation C₁.FunctionField (coordYFun C₁) ≤ 1) →
      (v.valuation C₁.FunctionField).valuationSubring ≤ C₁.ordAtInftyValuation.valuationSubring

/-- **The place classification, reduced to the ∞-inclusion residual** (the affine half discharged):
given `BPrimeInftyInclusion`, the full curve-completeness classification `BPrimePlaceClassification`
holds.  Case split on whether `v` is `≤ 1` on both coordinate generators: if so, the *point* case
`bPrime_valuation_eq_pointValuation_of_coordGen_le_one` (axiom-clean) gives the point alternative; if
not, the *infinity* case `bPrime_valuation_eq_ordAtInfty_of_subring_le` together with the residual
inclusion gives the `∞` alternative.

This isolates the entire remaining content of the classification into the single geometric hypothesis
`BPrimeInftyInclusion` (uniqueness of the place over `∞` of `F(x₁)`). -/
theorem bPrimePlaceClassification_of_inftyInclusion
    [IsIntegrallyClosed C₁.CoordinateRing]
    (hincl : BPrimeInftyInclusion (C₁ := C₁) (C₂ := C₂)) :
    BPrimePlaceClassification (C₁ := C₁) (C₂ := C₂) := by
  intro v
  by_cases hgen : v.valuation C₁.FunctionField (coordXFun C₁) ≤ 1 ∧
      v.valuation C₁.FunctionField (coordYFun C₁) ≤ 1
  · -- point case (affine half, axiom-clean)
    obtain ⟨P, hP⟩ :=
      bPrime_valuation_eq_pointValuation_of_coordGen_le_one v hgen.1 hgen.2
    exact Or.inl ⟨P, hP⟩
  · -- infinity case (modulo the inclusion residual)
    exact Or.inr (bPrime_valuation_eq_ordAtInfty_of_subring_le v (hincl v hgen))

/-- **The place-dictionary residual from the curve-completeness classification + regularity**
(axiom-clean): given the sharp place classification `BPrimePlaceClassification` and the
basepoint-regularity `OrdAtInftyReg` (`hreg`), the residual `BPrimeValuationCoordGenLeOne` follows
— the `∞` alternative of the classification is excluded by `bPrime_valuation_ne_ordAtInfty`.  This is
the cleanest reduction: it removes the geometric `∞`-exclusion entirely, leaving the *single*
genuine wall, the curve-completeness classification `BPrimePlaceClassification`. -/
theorem bPrimeValuationCoordGenLeOne_of_classification_of_reg
    (hclass : BPrimePlaceClassification (C₁ := C₁) (C₂ := C₂))
    (hreg : OrdAtInftyReg (C₁ := C₁) (C₂ := C₂)) :
    BPrimeValuationCoordGenLeOne (C₁ := C₁) (C₂ := C₂) :=
  bPrimeValuationCoordGenLeOne_of_classification hclass
    (bPrime_valuation_ne_ordAtInfty hreg)

/-- **The place dictionary, reduced to the single ∞-inclusion residual** (the affine half discharged,
axiom-clean): composing the classification reduction `bPrimePlaceClassification_of_inftyInclusion`
(point half done) with `bPrimeValuationCoordGenLeOne_of_classification_of_reg`, the place-dictionary
residual `BPrimeValuationCoordGenLeOne` — and hence all of `coordXFun_mem_B`, `coordYFun_mem_B`,
`coordRing_mem_B` — follows from the single geometric residual `BPrimeInftyInclusion` together with
the basepoint-regularity `hreg`.  This is the sharpest statement of the remaining wall: the entire
norm–conorm integral-closure chain is one curve-completeness fact (uniqueness of the place over `∞` of
`F(x₁)`) away from unconditional. -/
theorem bPrimeValuationCoordGenLeOne_of_inftyInclusion_of_reg
    [IsIntegrallyClosed C₁.CoordinateRing]
    (hincl : BPrimeInftyInclusion (C₁ := C₁) (C₂ := C₂))
    (hreg : OrdAtInftyReg (C₁ := C₁) (C₂ := C₂)) :
    BPrimeValuationCoordGenLeOne (C₁ := C₁) (C₂ := C₂) :=
  bPrimeValuationCoordGenLeOne_of_classification_of_reg
    (bPrimePlaceClassification_of_inftyInclusion hincl) hreg

/-! ### The ∞-inclusion residual, DISCHARGED via explicit local coordinates at `∞`

This section discharges `BPrimeInftyInclusion` *unconditionally* (the genuine curve-completeness
content), by proving the valuation-subring inclusion `O_∞ ⊆ O_v` for every `B`-prime `v` that has a
pole of `x₁` (`1 < v(x₁)`).  The route is the explicit local-coordinate description of the place at
infinity of `C₁` (over the place at `∞` of `F(x₁)`), avoiding the abstract `Sinf` `Σ e·f`
machinery entirely:

* `1 < v(x₁)` gives `v(1/x₁) < 1`, so `1/x₁ ∈ m_v` and `F[1/x₁] ⊆ O_v`.
* `w := y₁/x₁²` is *integral over* `F[1/x₁]` (explicit monic quadratic from the Weierstrass
  relation: `w² + (a₁/x₁ + a₃/x₁²) w − (1/x₁ + a₂/x₁² + a₄/x₁³ + a₆/x₁⁴) = 0`), so `w ∈ O_v`
  (`O_v` is a valuation ring, hence integrally closed).
* every `g` regular at `∞` (`0 ≤ ord_∞ g`) is `v`-integral: decompose `g = a + b·y₁` with
  `a, b ∈ F(x₁)`; the regularity at `∞` forces `a` and `b·x₁²` to be `F(x₁)`-elements regular at
  `∞`, hence in the local ring `F[1/x₁]_{(1/x₁)} ⊆ O_v`, and `b·y₁ = (b·x₁²)·w`.

Then the natural-direction rank-one domination `bPrime_valuation_eq_ordAtInfty_of_subring_ge`
turns `O_∞ ⊆ O_v` into `v = ordAtInftyValuation` — which `bPrime_valuation_ne_ordAtInfty` (the
`hreg`-fed `∞`-exclusion) forbids.  Hence no `B`-prime has an `x₁`-pole, i.e.
`BPrimeValuationCoordGenLeOne` holds. -/

/-- `coordXFun C₁` is the image of `Polynomial.X` under `F[X] → K(C₁)` (`= C₁.coordX`).  The two
descriptions agree through the scalar tower `F[X] → F[C₁] → K(C₁)`. -/
theorem coordXFun_eq_coordX : coordXFun C₁ = C₁.coordX := by
  rw [coordXFun, SmoothPlaneCurve.coordX,
    IsScalarTower.algebraMap_apply (Polynomial F) C₁.CoordinateRing C₁.FunctionField]
  rfl

/-- `coordYFun C₁` is `C₁.coordYInFunctionField` (both are `algebraMap (AdjoinRoot.root W)`). -/
theorem coordYFun_eq_coordYInFunctionField :
    coordYFun C₁ = C₁.coordYInFunctionField := rfl

/-- `ord_∞(x₁) = -2`. -/
theorem ordAtInfty_coordXFun : C₁.ordAtInfty (coordXFun C₁) = ((-2 : ℤ) : WithTop ℤ) := by
  rw [coordXFun_eq_coordX]; exact C₁.ordAtInfty_coordX

/-- `ord_∞(y₁) = -3`. -/
theorem ordAtInfty_coordYFun : C₁.ordAtInfty (coordYFun C₁) = ((-3 : ℤ) : WithTop ℤ) := by
  rw [coordYFun_eq_coordYInFunctionField]; exact C₁.ordAtInfty_coordYInFunctionField

/-- `coordYFun C₁ ≠ 0`. -/
theorem coordYFun_ne_zero : coordYFun C₁ ≠ 0 := by
  rw [coordYFun_eq_coordYInFunctionField]; exact C₁.coordYInFunctionField_ne_zero

/-- An `F`-constant is a `v`-adic *unit* for every `B`-prime `v`: `w_v(algebraMap_F c) = 1` for
`c ≠ 0` (both `c` and `c⁻¹` are base-ring elements of `B`, hence `≤ 1`).  The `F`-constants factor
through `C₂.CoordinateRing`, so this is two applications of
`valuation_algebraMap_coordinateRing_le_one`. -/
theorem valuation_algebraMap_F_eq_one
    (v : IsDedekindDomain.HeightOneSpectrum (B (C₁ := C₁) (C₂ := C₂)))
    {c : F} (hc : c ≠ 0) :
    v.valuation C₁.FunctionField (algebraMap F C₁.FunctionField c) = 1 := by
  have hroute : ∀ d : F, algebraMap F C₁.FunctionField d =
      algebraMap C₂.CoordinateRing C₁.FunctionField (algebraMap F C₂.CoordinateRing d) := by
    intro d
    rw [IsScalarTower.algebraMap_apply C₂.CoordinateRing C₂.FunctionField C₁.FunctionField,
      ← IsScalarTower.algebraMap_apply F C₂.CoordinateRing C₂.FunctionField,
      ← IsScalarTower.algebraMap_apply F C₂.FunctionField C₁.FunctionField]
  refine le_antisymm (by rw [hroute]; exact valuation_algebraMap_coordinateRing_le_one v _) ?_
  -- `1 = w_v(c · c⁻¹) = w_v(c) · w_v(c⁻¹) ≤ w_v(c) · 1`, so `1 ≤ w_v(c)`.
  have hcinv_le : v.valuation C₁.FunctionField (algebraMap F C₁.FunctionField c⁻¹) ≤ 1 := by
    rw [hroute]; exact valuation_algebraMap_coordinateRing_le_one v _
  have hprod : v.valuation C₁.FunctionField (algebraMap F C₁.FunctionField c) *
      v.valuation C₁.FunctionField (algebraMap F C₁.FunctionField c⁻¹) = 1 := by
    rw [← map_mul, ← map_mul, mul_inv_cancel₀ hc, map_one, map_one]
  -- `1 = w(c)·w(c⁻¹) ≤ w(c)·1 = w(c)`.
  calc (1 : WithZero (Multiplicative ℤ))
      = v.valuation C₁.FunctionField (algebraMap F C₁.FunctionField c) *
        v.valuation C₁.FunctionField (algebraMap F C₁.FunctionField c⁻¹) := hprod.symm
    _ ≤ v.valuation C₁.FunctionField (algebraMap F C₁.FunctionField c) * 1 :=
        mul_le_mul_right hcinv_le _
    _ = v.valuation C₁.FunctionField (algebraMap F C₁.FunctionField c) := mul_one _

/-- **The Weierstrass relation in `K(C₁)` with `F`-constant coefficients**:
`y₁² + (a₁·x₁ + a₃)·y₁ = x₁³ + a₂·x₁² + a₄·x₁ + a₆` where `aᵢ = algebraMap F` constants and
`x₁ = coordXFun C₁`, `y₁ = coordYFun C₁`. -/
theorem weierstrass_relation_coordFun :
    coordYFun C₁ ^ 2 +
        (algebraMap F C₁.FunctionField C₁.toAffine.a₁ * coordXFun C₁ +
          algebraMap F C₁.FunctionField C₁.toAffine.a₃) * coordYFun C₁ =
      coordXFun C₁ ^ 3 +
        algebraMap F C₁.FunctionField C₁.toAffine.a₂ * coordXFun C₁ ^ 2 +
        algebraMap F C₁.FunctionField C₁.toAffine.a₄ * coordXFun C₁ +
        algebraMap F C₁.FunctionField C₁.toAffine.a₆ := by
  have hsq := C₁.coordYInFunctionField_sq
  rw [← coordYFun_eq_coordYInFunctionField] at hsq
  -- expand the `algebraMap (Polynomial F)` of `C aᵢ`, `X` into `F`-constants and `coordXFun`
  have hX : algebraMap (Polynomial F) C₁.FunctionField Polynomial.X = coordXFun C₁ := by
    rw [coordXFun_eq_coordX]; rfl
  have hC : ∀ c : F, algebraMap (Polynomial F) C₁.FunctionField (Polynomial.C c) =
      algebraMap F C₁.FunctionField c := fun c => by
    rw [show (Polynomial.C c : Polynomial F) = algebraMap F (Polynomial F) c from rfl,
      ← IsScalarTower.algebraMap_apply F (Polynomial F) C₁.FunctionField]
  simp only [map_add, map_mul, map_pow, hX, hC] at hsq
  linear_combination hsq

set_option maxHeartbeats 800000 in
/-- The `v`-valuation of `coordXFun C₁` is nonzero (it is a nonzero field element). -/
theorem valuation_coordXFun_ne_zero
    (v : IsDedekindDomain.HeightOneSpectrum (B (C₁ := C₁) (C₂ := C₂))) :
    v.valuation C₁.FunctionField (coordXFun C₁) ≠ 0 := by
  have hne : coordXFun C₁ ≠ 0 := by rw [coordXFun_eq_coordX]; exact C₁.coordX_ne_zero
  rw [Ne, Valuation.zero_iff]; exact hne

set_option maxHeartbeats 800000 in
/-- `w_v(a₁·x₁ + a₃) ≤ w_v(x₁)` when `1 < w_v(x₁)` (the linear Weierstrass coefficient is dominated
by `x₁`, since the constants are `v`-units `≤ 1 < w_v(x₁)`). -/
theorem valuation_a₁X_add_a₃_le
    (v : IsDedekindDomain.HeightOneSpectrum (B (C₁ := C₁) (C₂ := C₂)))
    (hx : 1 < v.valuation C₁.FunctionField (coordXFun C₁)) :
    v.valuation C₁.FunctionField
        (algebraMap F C₁.FunctionField C₁.toAffine.a₁ * coordXFun C₁ +
          algebraMap F C₁.FunctionField C₁.toAffine.a₃) ≤
      v.valuation C₁.FunctionField (coordXFun C₁) := by
  set w := v.valuation C₁.FunctionField with hw
  have ha₁x : w (algebraMap F C₁.FunctionField C₁.toAffine.a₁ * coordXFun C₁) ≤
      w (coordXFun C₁) := by
    rw [w.map_mul]
    rcases eq_or_ne C₁.toAffine.a₁ 0 with h0 | h0
    · rw [h0, map_zero (algebraMap F C₁.FunctionField), w.map_zero, zero_mul]; exact zero_le
    · rw [valuation_algebraMap_F_eq_one v h0, one_mul]
  have ha₃ : w (algebraMap F C₁.FunctionField C₁.toAffine.a₃) ≤ w (coordXFun C₁) := by
    rcases eq_or_ne C₁.toAffine.a₃ 0 with h0 | h0
    · rw [h0, map_zero (algebraMap F C₁.FunctionField), w.map_zero]; exact zero_le
    · rw [valuation_algebraMap_F_eq_one v h0]; exact le_of_lt hx
  exact le_trans (w.map_add _ _) (max_le ha₁x ha₃)

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 400000 in
/-- **Generic ultrametric monomial bound** (instance-light): if a valuation `w` on `K(C₁)` is `≤ 1`
on the `F`-constant `algebraMap_F c` (`hc`) and `m ≤ X := w t`, then `w (algebraMap_F c * t^k) ≤ X^k`
... specialised below.  Stated as a free lemma over an *arbitrary* valuation `w` and element `t` to
keep the heavy `B`-instance `v.valuation` out of the unifier during the power arithmetic. -/
theorem valuation_const_mul_pow_le {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
    (w : Valuation C₁.FunctionField Γ₀) (t : C₁.FunctionField) (h1 : 1 ≤ w t)
    (hc : ∀ c : F, w (algebraMap F C₁.FunctionField c) ≤ 1) (c : F) {k : ℕ} (hk : k ≤ 3) :
    w (algebraMap F C₁.FunctionField c * t ^ k) ≤ w t ^ 3 := by
  rw [w.map_mul, map_pow]
  calc w (algebraMap F C₁.FunctionField c) * w t ^ k
      ≤ 1 * w t ^ k := mul_le_mul_left (hc c) _
    _ = w t ^ k := one_mul _
    _ ≤ w t ^ 3 := pow_le_pow_right₀ h1 hk

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 400000 in
/-- **Generic ultrametric Weierstrass-cubic bound** (instance-light): for an arbitrary valuation `w`
that is `≤ 1` on `F`-constants and has `1 ≤ w t`, the value of the Weierstrass cubic in `t` is
`≤ (w t)^3`. -/
theorem valuation_weierstrassCubic_le_generic {Γ₀ : Type*}
    [LinearOrderedCommGroupWithZero Γ₀]
    (w : Valuation C₁.FunctionField Γ₀) (t : C₁.FunctionField) (h1 : 1 ≤ w t)
    (hc : ∀ c : F, w (algebraMap F C₁.FunctionField c) ≤ 1) :
    w (t ^ 3 + algebraMap F C₁.FunctionField C₁.toAffine.a₂ * t ^ 2 +
        algebraMap F C₁.FunctionField C₁.toAffine.a₄ * t +
        algebraMap F C₁.FunctionField C₁.toAffine.a₆) ≤ w t ^ 3 := by
  have hx3 : w (t ^ 3) ≤ w t ^ 3 := le_of_eq (map_pow _ _ _)
  have ha₂ : w (algebraMap F C₁.FunctionField C₁.toAffine.a₂ * t ^ 2) ≤ w t ^ 3 :=
    valuation_const_mul_pow_le w t h1 hc _ (by norm_num)
  have ha₄ : w (algebraMap F C₁.FunctionField C₁.toAffine.a₄ * t) ≤ w t ^ 3 := by
    have := valuation_const_mul_pow_le w t h1 hc C₁.toAffine.a₄ (k := 1) (by norm_num)
    rwa [pow_one] at this
  have ha₆ : w (algebraMap F C₁.FunctionField C₁.toAffine.a₆) ≤ w t ^ 3 :=
    le_trans (hc _) (one_le_pow₀ h1)
  have hstep1 : w (t ^ 3 + algebraMap F C₁.FunctionField C₁.toAffine.a₂ * t ^ 2) ≤ w t ^ 3 :=
    le_trans (w.map_add _ _) (max_le hx3 ha₂)
  have hstep2 : w (t ^ 3 + algebraMap F C₁.FunctionField C₁.toAffine.a₂ * t ^ 2 +
        algebraMap F C₁.FunctionField C₁.toAffine.a₄ * t) ≤ w t ^ 3 :=
    le_trans (w.map_add _ _) (max_le hstep1 ha₄)
  exact le_trans (w.map_add _ _) (max_le hstep2 ha₆)

set_option maxHeartbeats 1600000 in
/-- `w_v(x₁³ + a₂x₁² + a₄x₁ + a₆) ≤ w_v(x₁)³` when `1 < w_v(x₁)`: the `B`-prime specialisation of
`valuation_weierstrassCubic_le_generic`. -/
theorem valuation_weierstrassCubic_le
    (v : IsDedekindDomain.HeightOneSpectrum (B (C₁ := C₁) (C₂ := C₂)))
    (hx : 1 < v.valuation C₁.FunctionField (coordXFun C₁)) :
    v.valuation C₁.FunctionField
        (coordXFun C₁ ^ 3 +
          algebraMap F C₁.FunctionField C₁.toAffine.a₂ * coordXFun C₁ ^ 2 +
          algebraMap F C₁.FunctionField C₁.toAffine.a₄ * coordXFun C₁ +
          algebraMap F C₁.FunctionField C₁.toAffine.a₆) ≤
      v.valuation C₁.FunctionField (coordXFun C₁) ^ 3 :=
  valuation_weierstrassCubic_le_generic (v.valuation C₁.FunctionField) (coordXFun C₁)
    (le_of_lt hx) (fun c => by
      rcases eq_or_ne c 0 with h0 | h0
      · rw [h0, map_zero (algebraMap F C₁.FunctionField), (v.valuation C₁.FunctionField).map_zero]
        exact zero_le
      · exact le_of_eq (valuation_algebraMap_F_eq_one v h0))

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 400000 in
/-- **Generic linear-coefficient bound** (instance-light): `w (a₁ x₁ + a₃) ≤ w x₁` for an arbitrary
valuation `w` with `1 ≤ w x₁` that is `≤ 1` on `F`-constants. -/
theorem valuation_a₁X_add_a₃_le_generic {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
    (w : Valuation C₁.FunctionField Γ₀) (h1 : 1 ≤ w (coordXFun C₁))
    (hc : ∀ c : F, w (algebraMap F C₁.FunctionField c) ≤ 1) :
    w (algebraMap F C₁.FunctionField C₁.toAffine.a₁ * coordXFun C₁ +
        algebraMap F C₁.FunctionField C₁.toAffine.a₃) ≤ w (coordXFun C₁) := by
  have ha₁x : w (algebraMap F C₁.FunctionField C₁.toAffine.a₁ * coordXFun C₁) ≤
      w (coordXFun C₁) := by
    rw [w.map_mul]
    calc w (algebraMap F C₁.FunctionField C₁.toAffine.a₁) * w (coordXFun C₁)
        ≤ 1 * w (coordXFun C₁) := mul_le_mul_left (hc _) _
      _ = w (coordXFun C₁) := one_mul _
  have ha₃ : w (algebraMap F C₁.FunctionField C₁.toAffine.a₃) ≤ w (coordXFun C₁) :=
    le_trans (hc _) h1
  exact le_trans (w.map_add _ _) (max_le ha₁x ha₃)

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 400000 in
/-- **Generic `y₁`-pole bound** (instance-light): for an arbitrary valuation `w` with `1 < w x₁`
that is `≤ 1` on `F`-constants, `w y₁ ≤ (w x₁)²`.  This is the explicit "`y₁/x₁²` is integral over
`F[1/x₁]`" fact, proved by ultrametric on the Weierstrass relation `y₁² = c − b·y₁`:
`(w y₁)² ≤ max(w c, w b · w y₁) ≤ max((w x₁)³, w x₁ · w y₁)`, which forces `w y₁ ≤ (w x₁)²`. -/
theorem valuation_coordYFun_le_sq_generic {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
    (w : Valuation C₁.FunctionField Γ₀) (hx : 1 < w (coordXFun C₁))
    (hc : ∀ c : F, w (algebraMap F C₁.FunctionField c) ≤ 1) :
    w (coordYFun C₁) ≤ w (coordXFun C₁) ^ 2 := by
  set X := w (coordXFun C₁) with hXdef
  set Y := w (coordYFun C₁) with hYdef
  have h1X : 1 ≤ X := le_of_lt hx
  -- from the Weierstrass relation: `Y² = w(c - b·y₁)`
  have hrel := weierstrass_relation_coordFun (C₁ := C₁)
  -- `y₁² = cubic - (a₁x₁+a₃)·y₁`
  have hyeq : coordYFun C₁ ^ 2 =
      (coordXFun C₁ ^ 3 + algebraMap F C₁.FunctionField C₁.toAffine.a₂ * coordXFun C₁ ^ 2 +
        algebraMap F C₁.FunctionField C₁.toAffine.a₄ * coordXFun C₁ +
        algebraMap F C₁.FunctionField C₁.toAffine.a₆) -
      (algebraMap F C₁.FunctionField C₁.toAffine.a₁ * coordXFun C₁ +
        algebraMap F C₁.FunctionField C₁.toAffine.a₃) * coordYFun C₁ := by
    linear_combination hrel
  have hYsq : Y ^ 2 ≤ max (X ^ 3) (X * Y) := by
    rw [hYdef, ← map_pow, hyeq]
    refine le_trans (Valuation.map_sub w _ _) (max_le_max ?_ ?_)
    · exact valuation_weierstrassCubic_le_generic w (coordXFun C₁) h1X hc
    · rw [w.map_mul]
      exact mul_le_mul_left (valuation_a₁X_add_a₃_le_generic w h1X hc) _
  -- trichotomy: `Y ≤ X²`
  by_contra hcon
  rw [not_le] at hcon
  have hYne : Y ≠ 0 := by
    rw [hYdef, Ne, Valuation.zero_iff]; exact coordYFun_ne_zero (C₁ := C₁)
  have hX0 : (0 : Γ₀) < X := lt_of_lt_of_le one_pos h1X
  have hY0 : (0 : Γ₀) < Y := zero_lt_iff.mpr hYne
  have hXleX2 : X ≤ X ^ 2 := by
    calc X = X * 1 := (mul_one X).symm
      _ ≤ X * X := mul_le_mul_right h1X X
      _ = X ^ 2 := (sq X).symm
  -- `X³ < X·Y` and `X·Y < Y²`, so `max(X³, X·Y) < Y²` — contradicting `hYsq`.
  have hX3_lt : X ^ 3 < X * Y := by
    have hstep : X ^ 2 * X < Y * X := (mul_lt_mul_iff_left₀ hX0).mpr hcon
    rw [mul_comm (X ^ 2) X, mul_comm Y X, ← pow_succ' X 2] at hstep
    exact hstep
  have hXltY : X < Y := lt_of_le_of_lt hXleX2 hcon
  have hXY_lt : X * Y < Y ^ 2 := by
    have hstep : X * Y < Y * Y := (mul_lt_mul_iff_left₀ hY0).mpr hXltY
    rwa [← sq Y] at hstep
  have : max (X ^ 3) (X * Y) < Y ^ 2 := max_lt (lt_trans hX3_lt hXY_lt) hXY_lt
  exact absurd hYsq (not_le.mpr this)

/-- `Polynomial.aeval (coordXFun C₁) p = algebraMap (Polynomial F) K(C₁) p` (evaluating the formal
polynomial at `x₁` is the structure map, since `x₁ = algebraMap X`).  Both are `F`-algebra maps
`F[X] → K(C₁)` sending `X ↦ x₁`. -/
theorem aeval_coordXFun_eq (p : Polynomial F) :
    Polynomial.aeval (coordXFun C₁) p = algebraMap (Polynomial F) C₁.FunctionField p := by
  rw [coordXFun_eq_coordX]
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, map_add, hp, hq]
  | monomial n a =>
      rw [Polynomial.aeval_monomial, SmoothPlaneCurve.coordX, ← map_pow,
        ← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_pow,
        IsScalarTower.algebraMap_apply F (Polynomial F) C₁.FunctionField,
        Polynomial.algebraMap_eq]

/-- **The `v`-valuation of a polynomial in `x₁` is `w_v(x₁)` to its degree**, when `1 < w_v(x₁)`:
the top-degree term dominates the non-archimedean sum.  Mathlib's
`Polynomial.valuation_aeval_eq_valuation_X_pow_natDegree_of_one_lt_valuation_X` for the valuation
`v.valuation`, which is `IsTrivialOn F` (constants are `v`-units). -/
theorem valuation_algebraMap_polynomial_eq
    (v : IsDedekindDomain.HeightOneSpectrum (B (C₁ := C₁) (C₂ := C₂)))
    (hx : 1 < v.valuation C₁.FunctionField (coordXFun C₁))
    {p : Polynomial F} (hp : p ≠ 0) :
    v.valuation C₁.FunctionField (algebraMap (Polynomial F) C₁.FunctionField p) =
      v.valuation C₁.FunctionField (coordXFun C₁) ^ p.natDegree := by
  haveI hTriv : (v.valuation C₁.FunctionField).IsTrivialOn F :=
    ⟨fun a ha => valuation_algebraMap_F_eq_one v ha⟩
  rw [← aeval_coordXFun_eq]
  exact Polynomial.valuation_aeval_eq_valuation_X_pow_natDegree_of_one_lt_valuation_X
    (coordXFun C₁) hx hp

set_option maxHeartbeats 1600000 in
/-- **The `F(x₁)`-regular-at-∞ bound (sublemma I)**: for `r ∈ FractionRing F[X]` whose image in
`K(C₁)` is *regular at `∞`* (`0 ≤ ord_∞`), and a `B`-prime `v` with `1 < w_v(x₁)`, the value
`w_v(algebraMap r) ≤ 1`.  Writing `r = p/d` with `p, d ∈ F[X]`, regularity at `∞` reads
`natDeg p ≤ natDeg d`, and `w_v(p(x₁))/w_v(d(x₁)) = w_v(x₁)^{natDeg p − natDeg d} ≤ 1` since
`1 < w_v(x₁)`. -/
theorem valuation_algebraMap_fracPolyX_le_one_of_ordAtInfty_nonneg
    (v : IsDedekindDomain.HeightOneSpectrum (B (C₁ := C₁) (C₂ := C₂)))
    (hx : 1 < v.valuation C₁.FunctionField (coordXFun C₁))
    {r : FractionRing (Polynomial F)}
    (hr : (0 : WithTop ℤ) ≤
      C₁.ordAtInfty (algebraMap (FractionRing (Polynomial F)) C₁.FunctionField r)) :
    v.valuation C₁.FunctionField
        (algebraMap (FractionRing (Polynomial F)) C₁.FunctionField r) ≤ 1 := by
  set w := v.valuation C₁.FunctionField with hw
  set X := w (coordXFun C₁) with hXdef
  have h1X : 1 ≤ X := le_of_lt hx
  rcases eq_or_ne r 0 with hr0 | hr0
  · rw [hr0, map_zero, w.map_zero]; exact zero_le_one
  -- decompose `r = algMap p / algMap d`
  obtain ⟨⟨p, ⟨d, hd_mem⟩⟩, hpd⟩ := IsLocalization.surj (nonZeroDivisors (Polynomial F)) r
  have hd_ne : d ≠ 0 := nonZeroDivisors.ne_zero hd_mem
  have hp_ne : p ≠ 0 := by
    intro hp0
    apply hr0
    have hz : r * algebraMap (Polynomial F) (FractionRing (Polynomial F)) d = 0 := by
      rw [hpd, hp0, map_zero]
    rcases mul_eq_zero.mp hz with h | h
    · exact h
    · exact absurd h ((map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr hd_ne)
  -- images in `K(C₁)`: `r ↦ P/D`
  set P : C₁.FunctionField := algebraMap (Polynomial F) C₁.FunctionField p with hPdef
  set D : C₁.FunctionField := algebraMap (Polynomial F) C₁.FunctionField d with hDdef
  have hD_ne : D ≠ 0 :=
    (map_ne_zero_iff _ (C₁.algebraMap_polynomialX_functionField_injective)).mpr hd_ne
  have hP_ne : P ≠ 0 :=
    (map_ne_zero_iff _ (C₁.algebraMap_polynomialX_functionField_injective)).mpr hp_ne
  have hrPD : algebraMap (FractionRing (Polynomial F)) C₁.FunctionField r = P / D := by
    rw [eq_div_iff hD_ne, hPdef, hDdef,
      IsScalarTower.algebraMap_apply (Polynomial F) (FractionRing (Polynomial F)) C₁.FunctionField p,
      IsScalarTower.algebraMap_apply (Polynomial F) (FractionRing (Polynomial F)) C₁.FunctionField d,
      ← map_mul, ← hpd, map_mul]
  -- degree comparison from regularity at `∞`
  have hordP : C₁.ordAtInfty P = ((-2 * (p.natDegree : ℤ) : ℤ) : WithTop ℤ) := by
    rw [hPdef]; exact C₁.ordAtInfty_algebraMap_polynomial_of_ne_zero hp_ne
  have hordD : C₁.ordAtInfty D = ((-2 * (d.natDegree : ℤ) : ℤ) : WithTop ℤ) := by
    rw [hDdef]; exact C₁.ordAtInfty_algebraMap_polynomial_of_ne_zero hd_ne
  have hdeg : p.natDegree ≤ d.natDegree := by
    rw [hrPD, C₁.ordAtInfty_div_of_ord_eq hD_ne (-2 * (p.natDegree : ℤ)) (-2 * (d.natDegree : ℤ))
      hordP hordD] at hr
    rw [show (0 : WithTop ℤ) = ((0 : ℤ) : WithTop ℤ) from rfl, WithTop.coe_le_coe] at hr
    omega
  -- valuation comparison
  rw [hrPD, map_div₀, valuation_algebraMap_polynomial_eq v hx hp_ne,
    valuation_algebraMap_polynomial_eq v hx hd_ne, ← hXdef]
  rw [div_le_one₀ (pow_ne_zero _ (by rw [hXdef]; exact valuation_coordXFun_ne_zero v) |>.bot_lt)]
  exact pow_le_pow_right₀ h1X hdeg

set_option maxHeartbeats 1600000 in
/-- `w_v(y₁ / x₁²) ≤ 1` for a `B`-prime `v` with `1 < w_v(x₁)` (from `w_v(y₁) ≤ w_v(x₁)²`). -/
theorem valuation_coordYFun_div_coordXFun_sq_le_one
    (v : IsDedekindDomain.HeightOneSpectrum (B (C₁ := C₁) (C₂ := C₂)))
    (hx : 1 < v.valuation C₁.FunctionField (coordXFun C₁)) :
    v.valuation C₁.FunctionField (coordYFun C₁ / coordXFun C₁ ^ 2) ≤ 1 := by
  set w := v.valuation C₁.FunctionField with hw
  have hxne : coordXFun C₁ ≠ 0 := by rw [coordXFun_eq_coordX]; exact C₁.coordX_ne_zero
  have hx2ne : (coordXFun C₁ ^ 2 : C₁.FunctionField) ≠ 0 := pow_ne_zero _ hxne
  have hwx2ne : w (coordXFun C₁ ^ 2) ≠ 0 := by rw [Ne, Valuation.zero_iff]; exact hx2ne
  rw [map_div₀, div_le_one₀ (zero_lt_iff.mpr hwx2ne), map_pow]
  have hc : ∀ c : F, w (algebraMap F C₁.FunctionField c) ≤ 1 := fun c => by
    rcases eq_or_ne c 0 with h0 | h0
    · rw [h0, map_zero (algebraMap F C₁.FunctionField), w.map_zero]; exact zero_le
    · exact le_of_eq (valuation_algebraMap_F_eq_one v h0)
  exact valuation_coordYFun_le_sq_generic w hx hc

/-- `coordXFun C₁ = algebraMap (FractionRing F[X]) K(C₁) (algebraMap F[X] _ X)` (the `x₁` coordinate
as the image of the fraction-field `X`). -/
theorem coordXFun_eq_algebraMap_fracX :
    coordXFun C₁ = algebraMap (FractionRing (Polynomial F)) C₁.FunctionField
      (algebraMap (Polynomial F) (FractionRing (Polynomial F)) Polynomial.X) := by
  rw [coordXFun_eq_coordX, SmoothPlaneCurve.coordX,
    IsScalarTower.algebraMap_apply (Polynomial F) (FractionRing (Polynomial F)) C₁.FunctionField]

/-- **Splitting off `x₁²`**: for any coefficient `b`, the basis term `b·y₁` factors as
`(b·x₁²)·(y₁/x₁²)`.  A pure algebraic identity (`y₁ = (y₁/x₁²)·x₁²`, `x₁ ≠ 0`), used to trade the
pole of `y₁` for the regular factor `b·x₁²` and the bounded factor `y₁/x₁²`. -/
private theorem coordYInFunctionField_eq_coordXFun_sq_mul (b : C₁.FunctionField) :
    b * C₁.coordYInFunctionField =
      (b * coordXFun C₁ ^ 2) * (coordYFun C₁ / coordXFun C₁ ^ 2) := by
  have hxne : coordXFun C₁ ≠ 0 := by rw [coordXFun_eq_coordX]; exact C₁.coordX_ne_zero
  rw [coordYFun_eq_coordYInFunctionField]
  field_simp

/-- **Regularity is preserved by clearing the `y₁`-pole with `x₁²`** (the parity step): if
`b = algebraMap q` for `q ≠ 0` and the basis term `b·y₁` is regular at `∞` (`0 ≤ ord_∞(b·y₁)`),
then so is `b·x₁²`.  Because `ord_∞` is *even* on `F(x₁)` (`ord_∞ b = 2k`) while `ord_∞ y₁ = -3`,
regularity `0 ≤ 2k - 3` forces `2k ≥ 4`, whence `0 ≤ 2k - 4 = ord_∞(b·x₁²)`. -/
private theorem ordAtInfty_algebraMap_fracPolyX_mul_coordXFun_sq_nonneg
    {q : FractionRing (Polynomial F)} (hq0 : q ≠ 0)
    (hgby : (0 : WithTop ℤ) ≤
      C₁.ordAtInfty (algebraMap (FractionRing (Polynomial F)) C₁.FunctionField q) +
        C₁.ordAtInfty C₁.coordYInFunctionField) :
    (0 : WithTop ℤ) ≤
      C₁.ordAtInfty
        (algebraMap (FractionRing (Polynomial F)) C₁.FunctionField q * coordXFun C₁ ^ 2) := by
  set bcoeff : C₁.FunctionField :=
    algebraMap (FractionRing (Polynomial F)) C₁.FunctionField q with hb_def
  have hbne : bcoeff ≠ 0 :=
    (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective _ _)).mpr hq0
  obtain ⟨k, hk⟩ : ∃ k : ℤ, C₁.ordAtInfty bcoeff = ((2 * k : ℤ) : WithTop ℤ) := by
    refine ⟨-(RatFunc.ofFractionRing q : RatFunc F).intDegree, ?_⟩
    rw [hb_def, C₁.ordAtInfty_algebraMap_fracPolyX_of_ne_zero hq0]
    congr 1; ring
  rw [hk, C₁.ordAtInfty_coordYInFunctionField, ← WithTop.coe_add,
    show (0 : WithTop ℤ) = ((0 : ℤ) : WithTop ℤ) from rfl, WithTop.coe_le_coe] at hgby
  have h2k : (4 : ℤ) ≤ 2 * k := by omega
  have hxne : coordXFun C₁ ≠ 0 := by rw [coordXFun_eq_coordX]; exact C₁.coordX_ne_zero
  have hx2ne : (coordXFun C₁ ^ 2 : C₁.FunctionField) ≠ 0 := pow_ne_zero _ hxne
  rw [C₁.ordAtInfty_mul hbne hx2ne, hk,
    show C₁.ordAtInfty (coordXFun C₁ ^ 2) = ((2 * (-2) : ℤ) : WithTop ℤ) by
      rw [C₁.ordAtInfty_pow hxne 2, ordAtInfty_coordXFun]; norm_cast,
    ← WithTop.coe_add,
    show (0 : WithTop ℤ) = ((0 : ℤ) : WithTop ℤ) from rfl, WithTop.coe_le_coe]
  omega

set_option maxHeartbeats 1600000 in
/-- **A regular `F(x₁)`-multiple of `y₁` has `w_v ≤ 1`** (sublemma (II) of the `∞`-domination): for a
`B`-prime `v` with `1 < w_v(x₁)` and `b = algebraMap q` (`q ∈ F(x₁)`), if `b·y₁` is regular at `∞`
then `w_v(b·y₁) ≤ 1`.  Write `b·y₁ = (b·x₁²)·(y₁/x₁²)`
(`coordYInFunctionField_eq_coordXFun_sq_mul`); the factor `b·x₁²` is again the image of a polynomial
multiple `q·X²`, regular at `∞` (`ordAtInfty_algebraMap_fracPolyX_mul_coordXFun_sq_nonneg`), so
`w_v(b·x₁²) ≤ 1` by sublemma (I), and `w_v(y₁/x₁²) ≤ 1`; multiply. -/
private theorem valuation_algebraMap_fracPolyX_mul_coordYInFunctionField_le_one
    (v : IsDedekindDomain.HeightOneSpectrum (B (C₁ := C₁) (C₂ := C₂)))
    (hx : 1 < v.valuation C₁.FunctionField (coordXFun C₁))
    {q : FractionRing (Polynomial F)} (hq0 : q ≠ 0)
    (hgby : (0 : WithTop ℤ) ≤
      C₁.ordAtInfty (algebraMap (FractionRing (Polynomial F)) C₁.FunctionField q) +
        C₁.ordAtInfty C₁.coordYInFunctionField) :
    v.valuation C₁.FunctionField
        (algebraMap (FractionRing (Polynomial F)) C₁.FunctionField q *
          C₁.coordYInFunctionField) ≤ 1 := by
  set w := v.valuation C₁.FunctionField with hw
  set bcoeff : C₁.FunctionField :=
    algebraMap (FractionRing (Polynomial F)) C₁.FunctionField q with hb_def
  -- `bcoeff·x₁² = algMap (q · X²)`, so sublemma (I) applies to it
  have hbx2 : bcoeff * coordXFun C₁ ^ 2 =
      algebraMap (FractionRing (Polynomial F)) C₁.FunctionField
        (q * (algebraMap (Polynomial F) (FractionRing (Polynomial F)) Polynomial.X) ^ 2) := by
    rw [map_mul, map_pow, hb_def, ← coordXFun_eq_algebraMap_fracX]
  have hwbx2 : w (bcoeff * coordXFun C₁ ^ 2) ≤ 1 := by
    rw [hbx2]
    exact valuation_algebraMap_fracPolyX_le_one_of_ordAtInfty_nonneg v hx
      (hbx2 ▸ ordAtInfty_algebraMap_fracPolyX_mul_coordXFun_sq_nonneg hq0 hgby)
  rw [coordYInFunctionField_eq_coordXFun_sq_mul bcoeff, w.map_mul]
  calc w (bcoeff * coordXFun C₁ ^ 2) * w (coordYFun C₁ / coordXFun C₁ ^ 2)
      ≤ 1 * 1 := mul_le_mul' hwbx2 (valuation_coordYFun_div_coordXFun_sq_le_one v hx)
    _ = 1 := mul_one 1

set_option maxHeartbeats 2400000 in
/-- **`O_∞ ⊆ O_v` (the curve-completeness crux, value form)**: for a `B`-prime `v` with `1 < w_v(x₁)`
and any `g` regular at `∞` of `C₁` (`0 ≤ ord_∞ g`), the value `w_v(g) ≤ 1`.  Decompose
`g = a + b·y₁` with `a, b ∈ F(x₁)`; regularity at `∞` gives `0 ≤ ord_∞ a` and `0 ≤ ord_∞(b·y₁)`,
the latter forcing (parity: `ord_∞` is even on `F(x₁)`) `0 ≤ ord_∞(b·x₁²)`.  Then `w_v(a) ≤ 1` and
`w_v(b·y₁) = w_v(b·x₁²)·w_v(y₁/x₁²) ≤ 1` by sublemmas (I) and the `y₁/x₁²` bound. -/
theorem valuation_le_one_of_ordAtInfty_nonneg
    (v : IsDedekindDomain.HeightOneSpectrum (B (C₁ := C₁) (C₂ := C₂)))
    (hx : 1 < v.valuation C₁.FunctionField (coordXFun C₁))
    {g : C₁.FunctionField} (hg : (0 : WithTop ℤ) ≤ C₁.ordAtInfty g) :
    v.valuation C₁.FunctionField g ≤ 1 := by
  set w := v.valuation C₁.FunctionField with hw
  obtain ⟨p, q, hpq⟩ := C₁.exists_decomp g
  -- rewrite `g = a + bcoeff·y₁` with `a, bcoeff ∈ F(x₁)`
  set a : C₁.FunctionField :=
    algebraMap (FractionRing (Polynomial F)) C₁.FunctionField p with ha_def
  set bcoeff : C₁.FunctionField :=
    algebraMap (FractionRing (Polynomial F)) C₁.FunctionField q with hb_def
  have hg_eq : g = a + bcoeff * C₁.coordYInFunctionField := by
    rw [hpq, Algebra.smul_def, mul_one, Algebra.smul_def]
  -- regularity at `∞` splits along the basis: `0 ≤ ord_∞ a` and `0 ≤ ord_∞(bcoeff·y₁)`
  rw [show C₁.ordAtInfty g =
      min (C₁.ordAtInfty a) (C₁.ordAtInfty bcoeff + C₁.ordAtInfty C₁.coordYInFunctionField) by
        rw [hg_eq, ha_def, hb_def]; exact C₁.ordAtInfty_basis_eq_min p q,
    le_min_iff] at hg
  obtain ⟨hga, hgby⟩ := hg
  -- `w_v(a) ≤ 1` (sublemma I) and `w_v(bcoeff·y₁) ≤ 1` (sublemma II); combine ultrametrically
  have hwa : w a ≤ 1 := valuation_algebraMap_fracPolyX_le_one_of_ordAtInfty_nonneg v hx hga
  have hwby : w (bcoeff * C₁.coordYInFunctionField) ≤ 1 := by
    rcases eq_or_ne q 0 with hq0 | hq0
    · rw [hb_def, hq0, map_zero, zero_mul, w.map_zero]; exact zero_le_one
    · exact valuation_algebraMap_fracPolyX_mul_coordYInFunctionField_le_one v hx hq0 hgby
  rw [hg_eq]
  exact le_trans (w.map_add _ _) (max_le hwa hwby)

/-- **The `v`-adic valuation subring of a `B`-prime is `≠ ⊤`** (it is nontrivial, surjecting onto
`ℤᵐ⁰`).  Needed for the `∞`-domination. -/
theorem valuationSubring_ne_top
    (v : IsDedekindDomain.HeightOneSpectrum (B (C₁ := C₁) (C₂ := C₂))) :
    (v.valuation C₁.FunctionField).valuationSubring ≠ ⊤ := by
  have hNontriv : (v.valuation C₁.FunctionField).IsNontrivial := by
    refine ⟨?_⟩
    obtain ⟨z, hz⟩ := v.valuation_surjective C₁.FunctionField (WithZero.exp (1 : ℤ))
    refine ⟨z, ?_, ?_⟩
    · rw [hz]; exact WithZero.exp_ne_zero
    · rw [hz, show (1 : WithZero (Multiplicative ℤ)) = WithZero.exp (0 : ℤ) from
        (WithZero.exp_zero).symm, Ne, WithZero.exp_inj]; norm_num
  intro htop
  exact (Valuation.valuationSubring_eq_top_iff _).mp htop hNontriv

set_option maxHeartbeats 1600000 in
/-- **No `B`-prime has an `x₁`-pole** (the `coordXFun` half of `BPrimeValuationCoordGenLeOne`,
discharged via the `∞`-exclusion `hreg`): for a `B`-prime `v`, `w_v(x₁) ≤ 1`.  By contradiction: if
`1 < w_v(x₁)`, then `O_∞ ⊆ O_v` (`valuation_le_one_of_ordAtInfty_nonneg`), so the rank-one domination
`bPrime_valuation_eq_ordAtInfty_of_subring_ge` forces `v = ordAtInftyValuation` — which
`bPrime_valuation_ne_ordAtInfty` (fed by `hreg`) forbids. -/
theorem valuation_coordXFun_le_one (hreg : OrdAtInftyReg (C₁ := C₁) (C₂ := C₂))
    (v : IsDedekindDomain.HeightOneSpectrum (B (C₁ := C₁) (C₂ := C₂))) :
    v.valuation C₁.FunctionField (coordXFun C₁) ≤ 1 := by
  by_contra hcon
  rw [not_le] at hcon
  -- `O_∞ ⊆ O_v`
  have hsup : C₁.ordAtInftyValuation.valuationSubring ≤
      (v.valuation C₁.FunctionField).valuationSubring := by
    intro f hf
    rw [Valuation.mem_valuationSubring_iff] at hf ⊢
    rcases eq_or_ne f 0 with hf0 | hf0
    · rw [hf0, (v.valuation C₁.FunctionField).map_zero]; exact zero_le_one
    · exact valuation_le_one_of_ordAtInfty_nonneg v hcon
        ((C₁.ordAtInftyValuation_le_one_iff_ordAtInfty_nonneg hf0).mp hf)
  -- domination ⟹ `v = ordAtInftyValuation`, contradicting the `∞`-exclusion
  exact bPrime_valuation_ne_ordAtInfty hreg v
    (bPrime_valuation_eq_ordAtInfty_of_subring_ge v hsup (valuationSubring_ne_top v))

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 400000 in
/-- **Generic ultrametric monomial bound, `≤ 1` regime** (instance-light): if a valuation `w` on
`K(C₁)` is `≤ 1` on the `F`-constant `algebraMap_F c` (`hc`) and `w t ≤ 1`, then
`w (algebraMap_F c * t^k) ≤ 1`.  The `w t ≤ 1` dual of `valuation_const_mul_pow_le` (bound by `1`
rather than `w t ^ 3`); stated over an arbitrary `w` and `t` to keep the heavy `B`-instance out of
the power arithmetic. -/
private theorem valuation_const_mul_pow_le_one_generic {Γ₀ : Type*}
    [LinearOrderedCommGroupWithZero Γ₀]
    (w : Valuation C₁.FunctionField Γ₀) (t : C₁.FunctionField) (h1 : w t ≤ 1)
    (hc : ∀ c : F, w (algebraMap F C₁.FunctionField c) ≤ 1) (c : F) (k : ℕ) :
    w (algebraMap F C₁.FunctionField c * t ^ k) ≤ 1 := by
  rw [w.map_mul, map_pow]
  calc w (algebraMap F C₁.FunctionField c) * w t ^ k
      ≤ 1 * 1 := mul_le_mul' (hc c) (pow_le_one₀ zero_le h1)
    _ = 1 := mul_one 1

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 400000 in
/-- **Generic ultrametric Weierstrass-cubic bound, `≤ 1` regime** (instance-light): for an arbitrary
valuation `w` that is `≤ 1` on `F`-constants and has `w t ≤ 1`, the Weierstrass cubic in `t` is
`≤ 1`.  The `w t ≤ 1` dual of `valuation_weierstrassCubic_le_generic`. -/
private theorem valuation_weierstrassCubic_le_one_generic {Γ₀ : Type*}
    [LinearOrderedCommGroupWithZero Γ₀]
    (w : Valuation C₁.FunctionField Γ₀) (t : C₁.FunctionField) (h1 : w t ≤ 1)
    (hc : ∀ c : F, w (algebraMap F C₁.FunctionField c) ≤ 1) :
    w (t ^ 3 + algebraMap F C₁.FunctionField C₁.toAffine.a₂ * t ^ 2 +
        algebraMap F C₁.FunctionField C₁.toAffine.a₄ * t +
        algebraMap F C₁.FunctionField C₁.toAffine.a₆) ≤ 1 := by
  have hx3 : w (t ^ 3) ≤ 1 := by rw [map_pow]; exact pow_le_one₀ zero_le h1
  have ha₂ : w (algebraMap F C₁.FunctionField C₁.toAffine.a₂ * t ^ 2) ≤ 1 :=
    valuation_const_mul_pow_le_one_generic w t h1 hc _ 2
  have ha₄ : w (algebraMap F C₁.FunctionField C₁.toAffine.a₄ * t) ≤ 1 := by
    have := valuation_const_mul_pow_le_one_generic w t h1 hc C₁.toAffine.a₄ 1; rwa [pow_one] at this
  have hstep1 : w (t ^ 3 + algebraMap F C₁.FunctionField C₁.toAffine.a₂ * t ^ 2) ≤ 1 :=
    le_trans (w.map_add _ _) (max_le hx3 ha₂)
  have hstep2 : w (t ^ 3 + algebraMap F C₁.FunctionField C₁.toAffine.a₂ * t ^ 2 +
      algebraMap F C₁.FunctionField C₁.toAffine.a₄ * t) ≤ 1 :=
    le_trans (w.map_add _ _) (max_le hstep1 ha₄)
  exact le_trans (w.map_add _ _) (max_le hstep2 (hc _))

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 400000 in
/-- **Generic linear-coefficient bound, `≤ 1` regime** (instance-light): `w (a₁ x₁ + a₃) ≤ 1` for an
arbitrary valuation `w` with `w x₁ ≤ 1` that is `≤ 1` on `F`-constants.  The `w x₁ ≤ 1` dual of
`valuation_a₁X_add_a₃_le_generic`. -/
private theorem valuation_a₁X_add_a₃_le_one_generic {Γ₀ : Type*}
    [LinearOrderedCommGroupWithZero Γ₀]
    (w : Valuation C₁.FunctionField Γ₀) (h1 : w (coordXFun C₁) ≤ 1)
    (hc : ∀ c : F, w (algebraMap F C₁.FunctionField c) ≤ 1) :
    w (algebraMap F C₁.FunctionField C₁.toAffine.a₁ * coordXFun C₁ +
        algebraMap F C₁.FunctionField C₁.toAffine.a₃) ≤ 1 := by
  have ha₁ : w (algebraMap F C₁.FunctionField C₁.toAffine.a₁ * coordXFun C₁) ≤ 1 := by
    rw [w.map_mul]
    calc w (algebraMap F C₁.FunctionField C₁.toAffine.a₁) * w (coordXFun C₁)
        ≤ 1 * 1 := mul_le_mul' (hc _) h1
      _ = 1 := mul_one 1
  exact le_trans (w.map_add _ _) (max_le ha₁ (hc _))

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 400000 in
/-- **Generic `y₁`-integrality bound, `≤ 1` regime** (instance-light): for an arbitrary valuation `w`
with `w x₁ ≤ 1` that is `≤ 1` on `F`-constants, `w y₁ ≤ 1`.  Proved by ultrametric on the rearranged
Weierstrass relation `y₁² = c − b·y₁`: a pole `1 < w y₁` would give
`(w y₁)² = w(c − b·y₁) ≤ max(w c, w b · w y₁) ≤ w y₁`, contradicting `w y₁ < (w y₁)²`.  The `w x₁ ≤ 1`
dual of `valuation_coordYFun_le_sq_generic`. -/
private theorem valuation_coordYFun_le_one_generic {Γ₀ : Type*}
    [LinearOrderedCommGroupWithZero Γ₀]
    (w : Valuation C₁.FunctionField Γ₀) (hxle : w (coordXFun C₁) ≤ 1)
    (hc : ∀ c : F, w (algebraMap F C₁.FunctionField c) ≤ 1) :
    w (coordYFun C₁) ≤ 1 := by
  -- the Weierstrass relation, rearranged: `y₁² = c − b·y₁`
  have hyeq : coordYFun C₁ ^ 2 =
      (coordXFun C₁ ^ 3 + algebraMap F C₁.FunctionField C₁.toAffine.a₂ * coordXFun C₁ ^ 2 +
        algebraMap F C₁.FunctionField C₁.toAffine.a₄ * coordXFun C₁ +
        algebraMap F C₁.FunctionField C₁.toAffine.a₆) -
      (algebraMap F C₁.FunctionField C₁.toAffine.a₁ * coordXFun C₁ +
        algebraMap F C₁.FunctionField C₁.toAffine.a₃) * coordYFun C₁ := by
    linear_combination weierstrass_relation_coordFun (C₁ := C₁)
  have hcubic := valuation_weierstrassCubic_le_one_generic w (coordXFun C₁) hxle hc
  have hlin := valuation_a₁X_add_a₃_le_one_generic w hxle hc
  -- ultrametric: `w(y₁)² ≤ max(1, w(y₁))`, force `w(y₁) ≤ 1`
  by_contra hcon
  rw [not_le] at hcon
  have hYsq : w (coordYFun C₁) ^ 2 ≤ w (coordYFun C₁) := by
    rw [← map_pow, hyeq]
    refine le_trans (Valuation.map_sub w _ _) (max_le (le_trans hcubic (le_of_lt hcon)) ?_)
    rw [w.map_mul]
    calc w (algebraMap F C₁.FunctionField C₁.toAffine.a₁ * coordXFun C₁ +
            algebraMap F C₁.FunctionField C₁.toAffine.a₃) * w (coordYFun C₁)
        ≤ 1 * w (coordYFun C₁) := mul_le_mul_left hlin _
      _ = w (coordYFun C₁) := one_mul _
  have hYne : w (coordYFun C₁) ≠ 0 := by
    rw [Ne, Valuation.zero_iff]; exact coordYFun_ne_zero (C₁ := C₁)
  have hY0 : (0 : Γ₀) < w (coordYFun C₁) := zero_lt_iff.mpr hYne
  -- `w(y₁)² > w(y₁)` since `w(y₁) > 1`, contradicting `hYsq`
  have hlt : w (coordYFun C₁) < w (coordYFun C₁) ^ 2 := by
    have hstep := (mul_lt_mul_iff_left₀ hY0).mpr hcon
    rwa [one_mul, ← sq] at hstep
  exact absurd hYsq (not_le.mpr hlt)

/-- **No `B`-prime has a `y₁`-pole** (the `coordYFun` half): for a `B`-prime `v`, `w_v(y₁) ≤ 1`.
Once `w_v(x₁) ≤ 1` (`valuation_coordXFun_le_one`), `y₁` is `v`-integral because it is integral over
`F[x₁]` (the Weierstrass relation `y₁² + b·y₁ = c` with `w_v(b), w_v(c) ≤ 1`): a pole of `y₁` would
make `w_v(y₁)² = w_v(c − b·y₁) ≤ max(w_v c, w_v b · w_v y₁) ≤ w_v(y₁)`, impossible.  The ultrametric
content is `valuation_coordYFun_le_one_generic`; here we feed it the `B`-prime facts `w_v(x₁) ≤ 1`
(`valuation_coordXFun_le_one`) and `w_v(F-const) ≤ 1` (`valuation_algebraMap_F_eq_one`). -/
theorem valuation_coordYFun_le_one (hreg : OrdAtInftyReg (C₁ := C₁) (C₂ := C₂))
    (v : IsDedekindDomain.HeightOneSpectrum (B (C₁ := C₁) (C₂ := C₂))) :
    v.valuation C₁.FunctionField (coordYFun C₁) ≤ 1 :=
  valuation_coordYFun_le_one_generic (v.valuation C₁.FunctionField)
    (valuation_coordXFun_le_one hreg v) (fun c => by
      rcases eq_or_ne c 0 with h0 | h0
      · rw [h0, map_zero (algebraMap F C₁.FunctionField), (v.valuation C₁.FunctionField).map_zero]
        exact zero_le
      · exact le_of_eq (valuation_algebraMap_F_eq_one v h0))

/-- **`BPrimeValuationCoordGenLeOne`, DISCHARGED** (the genuine curve-completeness content, now
unconditional modulo the basepoint-regularity `hreg`): every `B`-prime `v` is `≤ 1` on both
coordinate generators of `C₁`.  This combines the two pole-free lemmas
`valuation_coordXFun_le_one` / `valuation_coordYFun_le_one`. -/
theorem bPrimeValuationCoordGenLeOne_of_reg (hreg : OrdAtInftyReg (C₁ := C₁) (C₂ := C₂)) :
    BPrimeValuationCoordGenLeOne (C₁ := C₁) (C₂ := C₂) := fun v =>
  ⟨valuation_coordXFun_le_one hreg v, valuation_coordYFun_le_one hreg v⟩

/-! ### The minimal-polynomial reduction (non-circular, place-dictionary-free)

The whole content of `coordXFun_mem_B` / `coordYFun_mem_B` (and hence `coordRing_mem_B`) reduces —
*without any place dictionary* — to a single sharp **algebraic** statement about the minimal
polynomial of the coordinate generator over `K(C₂)`:

> the coefficients of `minpoly K(C₂) z` lie in `C₂.CoordinateRing` (`MinpolyCoeffsRegular z`).

Indeed, if the monic `minpoly K(C₂) z` has coefficients in (the image of) `C₂.CoordinateRing`,
then it lifts to a monic polynomial over `C₂.CoordinateRing` annihilating `z`, so `z` is *integral*
over `C₂.CoordinateRing`, i.e. `z ∈ B`.  This is exactly `LocalizedDictionary.isIntegral_of_denominator`
at the trivial localization `Af := C₂.CoordinateRing`, `f := 1` (where the denominator condition
collapses to "coefficients are coordinate-ring elements").

This is the **sharpest, cleanest, non-circular** isolation of the remaining wall: it bypasses the
entire place-classification chain (`BPrimePlaceClassification` / `BPrimeInftyInclusion` /
`BPrimeValuationCoordGenLeOne`), it is *true* (curve-completeness: the only poles of `z = x₁, y₁`
are at `∞` of `C₁`, which lies over `∞` of `C₂` by `hreg`, so the symmetric functions of the
conjugates of `z` — i.e. the minpoly coefficients — have no affine poles, hence lie in
`C₂.CoordinateRing`), and the residual content (the norm/trace pole estimate that pushes `z`'s
`∞`-only poles down to `C₂`) is purely on the `C₂` side. -/

/-- **The minpoly-coefficient regularity residual** for an element `z ∈ K(C₁)`: every coefficient
of the minimal polynomial of `z` over `K(C₂)` lies in (the image of) `C₂.CoordinateRing`.  For the
coordinate generators `z = coordXFun C₁`, `coordYFun C₁` this is the genuine curve-completeness
content of `coordXFun_mem_B` / `coordYFun_mem_B`: the poles of `z` (only at `∞` of `C₁`) lie over
`∞` of `C₂`, so the minpoly coefficients (symmetric functions of the conjugates of `z`) have no
affine poles on `C₂`, hence lie in `C₂.CoordinateRing`. -/
def MinpolyCoeffsRegular (z : C₁.FunctionField) : Prop :=
  ∀ i : ℕ, ∃ a : C₂.CoordinateRing,
    (minpoly C₂.FunctionField z).coeff i = algebraMap C₂.CoordinateRing C₂.FunctionField a

/-- **Integrality of a generator from minpoly-coefficient regularity** (the non-circular reduction):
if every coefficient of `minpoly K(C₂) z` lies in `C₂.CoordinateRing`, then `z` is integral over
`C₂.CoordinateRing`, i.e. `z ∈ B`.  This is `LocalizedDictionary.isIntegral_of_denominator` at the
trivial localization `Af := C₂.CoordinateRing`, `f := 1` (so the denominator condition reads "the
coefficients are coordinate-ring elements"), followed by `mem_integralClosure_iff`. -/
theorem mem_B_of_minpolyCoeffsRegular {z : C₁.FunctionField}
    (hz : MinpolyCoeffsRegular (C₁ := C₁) (C₂ := C₂) z) :
    z ∈ (B (C₁ := C₁) (C₂ := C₂)) := by
  have hint : IsIntegral C₂.CoordinateRing z := by
    refine LocalizedDictionary.isIntegral_of_denominator C₂ (1 : C₂.CoordinateRing)
      C₂.CoordinateRing one_ne_zero z (fun i => ?_)
    obtain ⟨a, ha⟩ := hz i
    refine ⟨a, ?_⟩
    rw [map_one, mul_one, ha]
  exact hint

/-- **The `x`-generator of `C₁` is integral over `C₂.CoordinateRing`, from minpoly-coefficient
regularity** (non-circular, place-dictionary-free): `coordXFun C₁ ∈ B` follows directly from
`MinpolyCoeffsRegular (coordXFun C₁)`. -/
theorem coordXFun_mem_B_of_minpolyCoeffsRegular
    (hx : MinpolyCoeffsRegular (C₁ := C₁) (C₂ := C₂) (coordXFun C₁)) :
    coordXFun C₁ ∈ (B (C₁ := C₁) (C₂ := C₂)) :=
  mem_B_of_minpolyCoeffsRegular hx

/-- **The `y`-generator of `C₁` is integral over `C₂.CoordinateRing`, from minpoly-coefficient
regularity** (non-circular, place-dictionary-free). -/
theorem coordYFun_mem_B_of_minpolyCoeffsRegular
    (hy : MinpolyCoeffsRegular (C₁ := C₁) (C₂ := C₂) (coordYFun C₁)) :
    coordYFun C₁ ∈ (B (C₁ := C₁) (C₂ := C₂)) :=
  mem_B_of_minpolyCoeffsRegular hy

/-- **The coordinate ring of `C₁` lands in `B`, from minpoly-coefficient regularity of the two
generators** (Silverman II.2.6, the non-circular place-dictionary-free form): for every
`r ∈ F[C₁]`, the image `algebraMap r ∈ K(C₁)` is integral over `C₂.CoordinateRing`. -/
theorem coordRing_mem_B_of_minpolyCoeffsRegular
    (hx : MinpolyCoeffsRegular (C₁ := C₁) (C₂ := C₂) (coordXFun C₁))
    (hy : MinpolyCoeffsRegular (C₁ := C₁) (C₂ := C₂) (coordYFun C₁))
    (r : C₁.CoordinateRing) :
    algebraMap C₁.CoordinateRing C₁.FunctionField r ∈ (B (C₁ := C₁) (C₂ := C₂)) :=
  coordRing_mem_integralClosure C₂ C₂.CoordinateRing
    (coordXFun_mem_B_of_minpolyCoeffsRegular hx)
    (coordYFun_mem_B_of_minpolyCoeffsRegular hy) r

/-! #### Bridge to the place-classification chain

The minpoly-coefficient reduction subsumes the place-classification chain: if both coordinate
generators have minpoly coefficients in `C₂.CoordinateRing` (so `x₁, y₁ ∈ B`), then *every* `B`-prime
is `≤ 1` on both generators (`BPrimeValuationCoordGenLeOne`), since `B`-elements are `v`-adic integers.
Consequently no `B`-prime has an `x₁`-pole, so the residual `BPrimeInftyInclusion` holds *vacuously*.
This shows the cleaner Prop `MinpolyCoeffsRegular` is strictly stronger than (and replaces) the
awkward `∞`-inclusion residual `BPrimeInftyInclusion`. -/

/-- **A `v`-adic integer of `B`**: if `z ∈ B`, then `v.valuation z ≤ 1` for every `B`-prime `v`. -/
theorem valuation_le_one_of_mem_B
    (v : IsDedekindDomain.HeightOneSpectrum (B (C₁ := C₁) (C₂ := C₂)))
    {z : C₁.FunctionField} (hz : z ∈ (B (C₁ := C₁) (C₂ := C₂))) :
    v.valuation C₁.FunctionField z ≤ 1 :=
  v.valuation_le_one (K := C₁.FunctionField) (⟨z, hz⟩ : B (C₁ := C₁) (C₂ := C₂))

/-- **The place dictionary from minpoly-coefficient regularity** (place-classification-free): if both
coordinate generators have minpoly coefficients in `C₂.CoordinateRing`, then every `B`-prime is `≤ 1`
on both — the residual `BPrimeValuationCoordGenLeOne`, with *no* place classification and *no* `hreg`
(those are absorbed into `MinpolyCoeffsRegular`). -/
theorem bPrimeValuationCoordGenLeOne_of_minpolyCoeffsRegular
    (hx : MinpolyCoeffsRegular (C₁ := C₁) (C₂ := C₂) (coordXFun C₁))
    (hy : MinpolyCoeffsRegular (C₁ := C₁) (C₂ := C₂) (coordYFun C₁)) :
    BPrimeValuationCoordGenLeOne (C₁ := C₁) (C₂ := C₂) := fun v =>
  ⟨valuation_le_one_of_mem_B v (coordXFun_mem_B_of_minpolyCoeffsRegular hx),
   valuation_le_one_of_mem_B v (coordYFun_mem_B_of_minpolyCoeffsRegular hy)⟩

/-- **The `∞`-inclusion residual `BPrimeInftyInclusion` is discharged (vacuously) by
minpoly-coefficient regularity**: once both coordinate generators have minpoly coefficients in
`C₂.CoordinateRing`, every `B`-prime is `≤ 1` on both generators, so the hypothesis of
`BPrimeInftyInclusion` (a `B`-prime *failing* `v(x₁) ≤ 1 ∧ v(y₁) ≤ 1`) is never met — the inclusion
holds vacuously.  This closes the task's literal target (`BPrimeInftyInclusion`) modulo the strictly
cleaner, place-dictionary-free residual `MinpolyCoeffsRegular`. -/
theorem bPrimeInftyInclusion_of_minpolyCoeffsRegular
    (hx : MinpolyCoeffsRegular (C₁ := C₁) (C₂ := C₂) (coordXFun C₁))
    (hy : MinpolyCoeffsRegular (C₁ := C₁) (C₂ := C₂) (coordYFun C₁)) :
    BPrimeInftyInclusion (C₁ := C₁) (C₂ := C₂) := by
  intro v hv
  exact absurd (bPrimeValuationCoordGenLeOne_of_minpolyCoeffsRegular hx hy v) hv

/-- **The `x`-generator of `C₁` is integral over `C₂.CoordinateRing`** (regular at every place
of `C₁` over an affine place of `C₂`).  Reduced — *non-circularly*, via the valuative criterion
`mem_B_of_forall_valuation_le_one` — to the global-`B` place dictionary
`BPrimeValuationCoordGenLeOne` (which consumes `hreg`).  Once the place dictionary is supplied this
is a one-liner; the residual is the project's standing global-place wall. -/
theorem coordXFun_mem_B (_hreg : OrdAtInftyReg (C₁ := C₁) (C₂ := C₂))
    (hplace : BPrimeValuationCoordGenLeOne (C₁ := C₁) (C₂ := C₂)) :
    coordXFun C₁ ∈ (B (C₁ := C₁) (C₂ := C₂)) :=
  mem_B_of_forall_valuation_le_one _ fun v => (hplace v).1

/-- **The `y`-generator of `C₁` is integral over `C₂.CoordinateRing`.**  Reduced — non-circularly,
via the valuative criterion — to the same global-`B` place dictionary residual. -/
theorem coordYFun_mem_B (_hreg : OrdAtInftyReg (C₁ := C₁) (C₂ := C₂))
    (hplace : BPrimeValuationCoordGenLeOne (C₁ := C₁) (C₂ := C₂)) :
    coordYFun C₁ ∈ (B (C₁ := C₁) (C₂ := C₂)) :=
  mem_B_of_forall_valuation_le_one _ fun v => (hplace v).2

/-- **The coordinate ring of `C₁` lands in `B`** (Silverman II.2.6, the integral-closure form):
for every `r ∈ F[C₁]`, the image `algebraMap r ∈ K(C₁)` is integral over `C₂.CoordinateRing`.
Built from the two generator integralities via `LocalizedDictionary.coordRing_mem_integralClosure`
(at the trivial localization `Af := C₂.CoordinateRing`). -/
theorem coordRing_mem_B (hreg : OrdAtInftyReg (C₁ := C₁) (C₂ := C₂))
    (hplace : BPrimeValuationCoordGenLeOne (C₁ := C₁) (C₂ := C₂)) (r : C₁.CoordinateRing) :
    algebraMap C₁.CoordinateRing C₁.FunctionField r ∈ (B (C₁ := C₁) (C₂ := C₂)) :=
  coordRing_mem_integralClosure C₂ C₂.CoordinateRing
    (coordXFun_mem_B hreg hplace) (coordYFun_mem_B hreg hplace) r

/-! ### The coordinate ring lands in `B` — UNCONDITIONAL (modulo basepoint regularity `hreg`)

With `BPrimeValuationCoordGenLeOne` now *proved* (`bPrimeValuationCoordGenLeOne_of_reg`, the
curve-completeness content discharged via explicit local coordinates at `∞`), the entire
`coordRing_mem_B` chain — and the sharp `MinpolyCoeffsRegular` residual — are unconditional: they
require only the basepoint-regularity `hreg` (`OrdAtInftyReg`), which is carried by every honest
isogeny pullback (`EC.Isogeny.pullback_ordAtInfty_nonneg`). -/

/-- **`coordXFun C₁ ∈ B`, UNCONDITIONAL** (modulo `hreg`). -/
theorem coordXFun_mem_B_of_reg (hreg : OrdAtInftyReg (C₁ := C₁) (C₂ := C₂)) :
    coordXFun C₁ ∈ (B (C₁ := C₁) (C₂ := C₂)) :=
  coordXFun_mem_B hreg (bPrimeValuationCoordGenLeOne_of_reg hreg)

/-- **`coordYFun C₁ ∈ B`, UNCONDITIONAL** (modulo `hreg`). -/
theorem coordYFun_mem_B_of_reg (hreg : OrdAtInftyReg (C₁ := C₁) (C₂ := C₂)) :
    coordYFun C₁ ∈ (B (C₁ := C₁) (C₂ := C₂)) :=
  coordYFun_mem_B hreg (bPrimeValuationCoordGenLeOne_of_reg hreg)

/-- **The coordinate ring of `C₁` lands in `B`, UNCONDITIONAL** (Silverman II.2.6, modulo `hreg`):
for every `r ∈ F[C₁]`, the image `algebraMap r ∈ K(C₁)` is integral over `C₂.CoordinateRing`. -/
theorem coordRing_mem_B_of_reg (hreg : OrdAtInftyReg (C₁ := C₁) (C₂ := C₂)) (r : C₁.CoordinateRing) :
    algebraMap C₁.CoordinateRing C₁.FunctionField r ∈ (B (C₁ := C₁) (C₂ := C₂)) :=
  coordRing_mem_B hreg (bPrimeValuationCoordGenLeOne_of_reg hreg) r

/-- **`MinpolyCoeffsRegular` for any `z ∈ B`** (the integrally-closed minpoly fact): if `z` is
integral over `C₂.CoordinateRing`, then every coefficient of `minpoly K(C₂) z` lies in (the image of)
`C₂.CoordinateRing`.  Direct from `minpoly.isIntegrallyClosed_eq_field_fractions'`
(`minpoly K(C₂) z = (minpoly C₂.CoordinateRing z).map (algebraMap …)`), so each coefficient is the
`algebraMap`-image of the corresponding coefficient over `C₂.CoordinateRing`. -/
theorem minpolyCoeffsRegular_of_mem_B {z : C₁.FunctionField}
    (hz : z ∈ (B (C₁ := C₁) (C₂ := C₂))) :
    MinpolyCoeffsRegular (C₁ := C₁) (C₂ := C₂) z := by
  have hint : IsIntegral C₂.CoordinateRing z := hz
  have hmap : minpoly C₂.FunctionField z =
      (minpoly C₂.CoordinateRing z).map (algebraMap C₂.CoordinateRing C₂.FunctionField) :=
    minpoly.isIntegrallyClosed_eq_field_fractions' C₂.FunctionField hint
  intro i
  exact ⟨(minpoly C₂.CoordinateRing z).coeff i, by rw [hmap, Polynomial.coeff_map]⟩

/-- **`MinpolyCoeffsRegular (coordXFun C₁)`, DISCHARGED** (modulo `hreg`): the task's literal target
for the `x`-generator.  Combines `coordXFun_mem_B_of_reg` with `minpolyCoeffsRegular_of_mem_B`. -/
theorem minpolyCoeffsRegular_coordXFun (hreg : OrdAtInftyReg (C₁ := C₁) (C₂ := C₂)) :
    MinpolyCoeffsRegular (C₁ := C₁) (C₂ := C₂) (coordXFun C₁) :=
  minpolyCoeffsRegular_of_mem_B (coordXFun_mem_B_of_reg hreg)

/-- **`MinpolyCoeffsRegular (coordYFun C₁)`, DISCHARGED** (modulo `hreg`): the task's literal target
for the `y`-generator. -/
theorem minpolyCoeffsRegular_coordYFun (hreg : OrdAtInftyReg (C₁ := C₁) (C₂ := C₂)) :
    MinpolyCoeffsRegular (C₁ := C₁) (C₂ := C₂) (coordYFun C₁) :=
  minpolyCoeffsRegular_of_mem_B (coordYFun_mem_B_of_reg hreg)

/-! ### Inertia degree `1` and the `s = 1` core over `B` (T-A2 core) -/

/-- **Inertia degree `1`** for a prime `P` of `B` lying over the maximal ideal `m_Q` of
`C₂.CoordinateRing`: over an algebraically closed base the residue fields are trivial.  This is
`LocalizedDictionary.inertiaDeg_eq_one_of_under_eq` instantiated at the trivial localization
`Af := C₂.CoordinateRing`, `f := 1` (valid at *every* affine place since `1 ∉ m_Q`). -/
theorem inertiaDeg_eq_one (P : Ideal (B (C₁ := C₁) (C₂ := C₂)))
    (Q : C₂.SmoothPoint) (hPp : P.IsPrime)
    (hPq : P.under C₂.CoordinateRing = C₂.maximalIdealAt Q) :
    Ideal.inertiaDeg (C₂.maximalIdealAt Q) P = 1 := by
  have hfQ : (1 : C₂.CoordinateRing) ∉ C₂.maximalIdealAt Q := one_notMem_maximalIdealAt Q
  have hPq' : P.under C₂.CoordinateRing = awayIdealAt (C₂ := C₂) C₂.CoordinateRing Q := by
    rw [hPq, awayIdealAt_eq_maximalIdealAt]
  have := inertiaDeg_eq_one_of_under_eq C₂ (1 : C₂.CoordinateRing) C₂.CoordinateRing
    one_ne_zero hfQ hPp hPq'
  rwa [awayIdealAt_eq_maximalIdealAt] at this

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 800000 in
attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra in
/-- **Finrank coherence for `B`**: the relative-norm finrank `[Frac(C₂.CoordinateRing) : Frac(B)]`
(computed by `Ideal.relNorm_algebraMap` with the canonical `FractionRing.liftAlgebra` structure)
agrees with the geometric extension degree `[K(C₁) : K(C₂)]`.  Because `C₂.FunctionField` *is*
`FractionRing C₂.CoordinateRing` (defeq abbrev) and `C₁.FunctionField` is the fraction field of `B`
(`instFractionRingB`), the two `finrank`s are identified by the canonical `FractionRing.algEquiv`s,
via `Algebra.finrank_eq_of_equiv_equiv`.  This is the integral-closure analogue of the affine
template's `hcoh` (`PushforwardDivisor.relNorm_maximalIdealAt_eq`), but more direct: `B`'s fraction
field is literally `C₁.FunctionField`, so no `liftAlgebra`-vs-pullback identification is needed.

Stated with the `FractionRing.liftAlgebra` local instance active, so its LHS matches the finrank
term produced by `Ideal.relNorm_algebraMap` verbatim. -/
theorem finrank_fractionRing_B_eq :
    Module.finrank (FractionRing C₂.CoordinateRing) (FractionRing (B (C₁ := C₁) (C₂ := C₂))) =
      Module.finrank C₂.FunctionField C₁.FunctionField := by
  refine Algebra.finrank_eq_of_equiv_equiv
    (FractionRing.algEquiv C₂.CoordinateRing C₂.FunctionField).toRingEquiv
    (FractionRing.algEquiv (B (C₁ := C₁) (C₂ := C₂)) C₁.FunctionField).toRingEquiv ?_
  apply IsLocalization.ringHom_ext (nonZeroDivisors C₂.CoordinateRing)
  refine RingHom.ext fun a => ?_
  show (algebraMap C₂.FunctionField C₁.FunctionField)
      ((FractionRing.algEquiv C₂.CoordinateRing C₂.FunctionField)
        ((algebraMap C₂.CoordinateRing (FractionRing C₂.CoordinateRing)) a)) =
    (FractionRing.algEquiv (B (C₁ := C₁) (C₂ := C₂)) C₁.FunctionField)
      ((algebraMap (FractionRing C₂.CoordinateRing) (FractionRing (B (C₁ := C₁) (C₂ := C₂))))
        ((algebraMap C₂.CoordinateRing (FractionRing C₂.CoordinateRing)) a))
  rw [AlgEquiv.commutes,
    ← IsScalarTower.algebraMap_apply C₂.CoordinateRing (FractionRing C₂.CoordinateRing)
      (FractionRing (B (C₁ := C₁) (C₂ := C₂))),
    IsScalarTower.algebraMap_apply C₂.CoordinateRing (B (C₁ := C₁) (C₂ := C₂))
      (FractionRing (B (C₁ := C₁) (C₂ := C₂))), AlgEquiv.commutes,
    ← IsScalarTower.algebraMap_apply C₂.CoordinateRing C₂.FunctionField C₁.FunctionField,
    IsScalarTower.algebraMap_apply C₂.CoordinateRing (B (C₁ := C₁) (C₂ := C₂)) C₁.FunctionField]

/-- **The relative-norm exponent of a prime over `m_Q` is positive**: if a prime `P'` of `B`
lies over the maximal ideal `m_Q` of `C₂.CoordinateRing` and `relNorm(P') = m_Q ^ t`, then
`1 ≤ t`.  Otherwise `t = 0` gives `relNorm(P') = ⊤`, contradicting
`relNorm(P') ≤ comap P' = m_Q ≠ ⊤` (`Ideal.relNorm_le_comap`).  `B`-analogue of the affine
template's `one_le_of_relNorm_eq_pow`. -/
private theorem one_le_relNormExp_of_liesOver (Q : C₂.SmoothPoint)
    (P' : Ideal (B (C₁ := C₁) (C₂ := C₂))) [P'.LiesOver (C₂.maximalIdealAt Q)] (t : ℕ)
    (ht : Ideal.relNorm C₂.CoordinateRing P' = C₂.maximalIdealAt Q ^ t) :
    1 ≤ t := by
  haveI hQmax : (C₂.maximalIdealAt Q).IsMaximal := C₂.maximalIdealAt_isMaximal Q
  rcases Nat.eq_zero_or_pos t with ht0 | ht0
  · exfalso
    have hcomap : P'.comap (algebraMap C₂.CoordinateRing (B (C₁ := C₁) (C₂ := C₂))) =
        C₂.maximalIdealAt Q := (Ideal.LiesOver.over (p := C₂.maximalIdealAt Q) (P := P')).symm
    have hbound := Ideal.relNorm_le_comap (R := C₂.CoordinateRing) P'
    rw [hcomap, ht, ht0, pow_zero, Ideal.one_eq_top, top_le_iff] at hbound
    exact hQmax.ne_top hbound
  · exact ht0

/-- **Each prime over `m_Q` has relative norm a positive power of `m_Q`**: for every prime `P'`
of `B` in `(m_Q).primesOver B`, there is `t ≥ 1` with `relNorm(P') = m_Q ^ t`.  Combines
`Ideal.exists_relNorm_eq_pow_of_isPrime` (the power form) with `one_le_relNormExp_of_liesOver`
(positivity). -/
private theorem exists_relNormExp_pos_of_mem_primesOver (Q : C₂.SmoothPoint)
    (P' : Ideal (B (C₁ := C₁) (C₂ := C₂)))
    (hP' : P' ∈ (C₂.maximalIdealAt Q).primesOver (B (C₁ := C₁) (C₂ := C₂))) :
    ∃ t : ℕ, 1 ≤ t ∧ Ideal.relNorm C₂.CoordinateRing P' = C₂.maximalIdealAt Q ^ t := by
  obtain ⟨hP'prime, hP'lies⟩ := hP'
  haveI : P'.IsPrime := hP'prime
  haveI : P'.LiesOver (C₂.maximalIdealAt Q) := hP'lies
  obtain ⟨t, ht⟩ := Ideal.exists_relNorm_eq_pow_of_isPrime P' (C₂.maximalIdealAt Q)
  exact ⟨t, one_le_relNormExp_of_liesOver Q P' t ht, ht⟩

/-- **A uniform relative-norm-exponent function over the fibre `m_Q`**: there is a single
`sfn : Ideal B → ℕ` such that every prime `P'` over `m_Q` has `sfn(P') ≥ 1` and
`relNorm(P') = m_Q ^ sfn(P')`.  Packages the per-prime exponents of
`exists_relNormExp_pos_of_mem_primesOver` into one function via a dependent choice
(`Classical.choose` guarded by membership), so the global balance can sum over it. -/
private theorem exists_relNormExp_fn (Q : C₂.SmoothPoint) :
    ∃ sfn : Ideal (B (C₁ := C₁) (C₂ := C₂)) → ℕ,
      (∀ P' ∈ (C₂.maximalIdealAt Q).primesOver (B (C₁ := C₁) (C₂ := C₂)), 1 ≤ sfn P') ∧
      ∀ P' ∈ (C₂.maximalIdealAt Q).primesOver (B (C₁ := C₁) (C₂ := C₂)),
        Ideal.relNorm C₂.CoordinateRing P' = C₂.maximalIdealAt Q ^ sfn P' := by
  classical
  refine ⟨fun P' => if hP' : P' ∈ (C₂.maximalIdealAt Q).primesOver (B (C₁ := C₁) (C₂ := C₂)) then
    (exists_relNormExp_pos_of_mem_primesOver Q P' hP').choose else 0, ?_, ?_⟩
  · intro P' hP'
    simp only [dif_pos hP']
    exact (exists_relNormExp_pos_of_mem_primesOver Q P' hP').choose_spec.1
  · intro P' hP'
    simp only [dif_pos hP']
    exact (exists_relNormExp_pos_of_mem_primesOver Q P' hP').choose_spec.2

/-- **Inertia degree `1` for every prime over `m_Q`**: every prime `P'` of `B` in
`(m_Q).primesOver B` has `inertiaDeg(m_Q, P') = 1`.  Such a `P'` lies over `m_Q`, so
`P'.under = m_Q`, and the per-prime `inertiaDeg_eq_one` (residue fields all `F`) applies. -/
private theorem inertiaDeg_eq_one_of_mem_primesOver (Q : C₂.SmoothPoint)
    (P' : Ideal (B (C₁ := C₁) (C₂ := C₂)))
    (hP' : P' ∈ (C₂.maximalIdealAt Q).primesOver (B (C₁ := C₁) (C₂ := C₂))) :
    Ideal.inertiaDeg (C₂.maximalIdealAt Q) P' = 1 := by
  obtain ⟨hP'prime, hP'lies⟩ := hP'
  have hunder : P'.under C₂.CoordinateRing = C₂.maximalIdealAt Q := hP'lies.over.symm
  exact inertiaDeg_eq_one P' Q hP'prime hunder

/-- **Ramification index positive for primes over `m_Q`**: every prime `P'` of `B` in
`(m_Q).primesOver B` has `e_{P'} ≥ 1`.  The ramification index of a prime over a nonzero ideal
is nonzero in a Dedekind domain (`ramificationIdx_ne_zero_of_liesOver`).  `B`-analogue of the
affine template's `one_le_ramificationIdx_of_liesOver_maximalIdealAt`. -/
private theorem one_le_ramificationIdx_of_mem_primesOver (Q : C₂.SmoothPoint)
    (P' : Ideal (B (C₁ := C₁) (C₂ := C₂)))
    (hP' : P' ∈ (C₂.maximalIdealAt Q).primesOver (B (C₁ := C₁) (C₂ := C₂))) :
    1 ≤ (C₂.maximalIdealAt Q).ramificationIdx P' := by
  obtain ⟨hP'prime, hP'lies⟩ := hP'
  haveI : P'.IsPrime := hP'prime
  haveI : P'.LiesOver (C₂.maximalIdealAt Q) := hP'lies
  have hp0 : C₂.maximalIdealAt Q ≠ ⊥ := C₂.maximalIdealAt_ne_bot Q
  rw [Nat.one_le_iff_ne_zero]
  exact Ideal.IsDedekindDomain.ramificationIdx_ne_zero_of_liesOver P' hp0

/-- **The fibre over `m_Q` as a `primesOver`-`toFinset`**: the explicit fibre finset
`IsDedekindDomain.primesOverFinset m_Q B` equals `((m_Q).primesOver B).toFinset`.  Both name the
finite set of primes of `B` lying over the nonzero ideal `m_Q`; coerced to a set they agree
(`IsDedekindDomain.coe_primesOverFinset`, `Set.coe_toFinset`).  Established once with `m_Q.IsMaximal`
in scope so the `Fintype (primesOver)` instance behind `.toFinset` is available. -/
private theorem primesOverFinset_eq_toFinset (Q : C₂.SmoothPoint) :
    haveI : (C₂.maximalIdealAt Q).IsMaximal := C₂.maximalIdealAt_isMaximal Q
    IsDedekindDomain.primesOverFinset (C₂.maximalIdealAt Q) (B (C₁ := C₁) (C₂ := C₂)) =
      ((C₂.maximalIdealAt Q).primesOver (B (C₁ := C₁) (C₂ := C₂))).toFinset := by
  haveI : (C₂.maximalIdealAt Q).IsMaximal := C₂.maximalIdealAt_isMaximal Q
  have hp0 : C₂.maximalIdealAt Q ≠ ⊥ := C₂.maximalIdealAt_ne_bot Q
  apply Finset.coe_injective
  rw [IsDedekindDomain.coe_primesOverFinset hp0, Set.coe_toFinset]

/-- **Sum of ramification indices equals the geometric degree**: over a smooth point `Q` of `C₂`,
`Σ_{P' / m_Q} e_{P'} = [K(C₁) : K(C₂)]`.  Combines the fundamental identity
`Σ e_{P'}·f_{P'} = [K(C₁):K(C₂)]` (`Ideal.sum_ramification_inertia`, applicable *directly* because
`B` is the integral closure) with every residue degree `f_{P'} = 1`
(`inertiaDeg_eq_one_of_mem_primesOver`).  Stated over the explicit fibre finset
`IsDedekindDomain.primesOverFinset` (no `Fintype`-at-type-level needed).  `B`-analogue of the affine
template's `sum_ramificationIdx_eq_degree`. -/
private theorem sum_ramificationIdx_eq_finrank (Q : C₂.SmoothPoint) :
    ∑ P' ∈ IsDedekindDomain.primesOverFinset (C₂.maximalIdealAt Q) (B (C₁ := C₁) (C₂ := C₂)),
      (C₂.maximalIdealAt Q).ramificationIdx P' =
      Module.finrank C₂.FunctionField C₁.FunctionField := by
  haveI hQmax : (C₂.maximalIdealAt Q).IsMaximal := C₂.maximalIdealAt_isMaximal Q
  set p : Ideal C₂.CoordinateRing := C₂.maximalIdealAt Q with hp_def
  have hp0 : p ≠ ⊥ := C₂.maximalIdealAt_ne_bot Q
  have hsumef := Ideal.sum_ramification_inertia (B (C₁ := C₁) (C₂ := C₂)) C₂.FunctionField
    C₁.FunctionField (p := p) hp0
  rw [← hsumef]
  apply Finset.sum_congr rfl
  intro P' hP'
  have hmem : P' ∈ p.primesOver (B (C₁ := C₁) (C₂ := C₂)) :=
    (IsDedekindDomain.mem_primesOverFinset_iff (B := B (C₁ := C₁) (C₂ := C₂)) hp0).mp hP'
  rw [inertiaDeg_eq_one_of_mem_primesOver Q P' hmem, mul_one]

set_option maxHeartbeats 1600000 in
/-- **The degree balance `[K(C₁):K(C₂)] = Σ sfn(P')·e(P')`**: if, over a smooth point `Q` of `C₂`,
the relative norm of each prime `P' / m_Q` is the power `relNorm(P') = m_Q ^ sfn(P')`, then
`[K(C₁):K(C₂)] = Σ_{P' / m_Q} sfn(P')·e_{P'}`.  Apply `relNorm` to the prime factorisation
`m_Q·B = ∏ P'^{e_{P'}}` (`Ideal.map_algebraMap_eq_finsetProd_pow`): the left side is
`m_Q ^ finrank = m_Q ^ [K(C₁):K(C₂)]` (`Ideal.relNorm_algebraMap` + `finrank_fractionRing_B_eq`),
the right side `m_Q ^ Σ sfn·e`, and `m_Q` not being a unit lets us cancel the bases
(`pow_inj_of_not_isUnit`).  `B`-analogue of the affine template's
`degree_eq_sum_relNormExp_mul_ramificationIdx`. -/
private theorem finrank_eq_sum_relNormExp_mul_ramificationIdx (Q : C₂.SmoothPoint)
    (sfn : Ideal (B (C₁ := C₁) (C₂ := C₂)) → ℕ)
    (hsfn_relNorm : ∀ P' ∈ (C₂.maximalIdealAt Q).primesOver (B (C₁ := C₁) (C₂ := C₂)),
      Ideal.relNorm C₂.CoordinateRing P' = C₂.maximalIdealAt Q ^ sfn P') :
    Module.finrank C₂.FunctionField C₁.FunctionField =
      ∑ P' ∈ IsDedekindDomain.primesOverFinset (C₂.maximalIdealAt Q) (B (C₁ := C₁) (C₂ := C₂)),
        sfn P' * (C₂.maximalIdealAt Q).ramificationIdx P' := by
  haveI hQmax : (C₂.maximalIdealAt Q).IsMaximal := C₂.maximalIdealAt_isMaximal Q
  set p : Ideal C₂.CoordinateRing := C₂.maximalIdealAt Q with hp_def
  have hp0 : p ≠ ⊥ := C₂.maximalIdealAt_ne_bot Q
  have hpNotUnit : ¬ IsUnit p := by rw [Ideal.isUnit_iff]; exact hQmax.ne_top
  set ee : Ideal (B (C₁ := C₁) (C₂ := C₂)) → ℕ := fun P' => p.ramificationIdx P' with hee_def
  rw [primesOverFinset_eq_toFinset Q]
  have hfact := Ideal.map_algebraMap_eq_finsetProd_pow (R := B (C₁ := C₁) (C₂ := C₂))
    (S := C₂.CoordinateRing) (p := p) hp0
  have hrel := congr_arg (Ideal.relNorm C₂.CoordinateRing) hfact
  rw [Ideal.relNorm_algebraMap (B (C₁ := C₁) (C₂ := C₂)) p, map_prod,
    finrank_fractionRing_B_eq] at hrel
  have hrhs : ∏ P' ∈ (p.primesOver (B (C₁ := C₁) (C₂ := C₂))).toFinset,
      Ideal.relNorm C₂.CoordinateRing (P' ^ ee P') =
      p ^ (∑ P' ∈ (p.primesOver (B (C₁ := C₁) (C₂ := C₂))).toFinset, sfn P' * ee P') := by
    rw [← Finset.prod_pow_eq_pow_sum]
    apply Finset.prod_congr rfl
    intro P' hP'
    have hmem : P' ∈ p.primesOver (B (C₁ := C₁) (C₂ := C₂)) := Set.mem_toFinset.mp hP'
    rw [map_pow, hsfn_relNorm P' hmem, ← pow_mul]
  rw [hrhs] at hrel
  exact (pow_inj_of_not_isUnit hpNotUnit hp0).mp hrel

/-- **A `ℕ`-valued sum squeeze**: if `∑ c = ∑ a·c` over a finset `s` with every `a i ≥ 1` and every
`c i ≥ 1`, then `a i₀ = 1` for each `i₀ ∈ s`.  Each summand satisfies `c i ≤ a i · c i`, so equality
of the sums forces `c i = a i · c i` pointwise (`Finset.sum_eq_sum_iff_of_le`); cancelling the
positive `c i₀` gives `a i₀ = 1`. -/
private theorem eq_one_of_sum_eq_sum_mul {ι : Type*} (s : Finset ι) (a c : ι → ℕ)
    (hsum : ∑ i ∈ s, c i = ∑ i ∈ s, a i * c i)
    (ha : ∀ i ∈ s, 1 ≤ a i) (hc : ∀ i ∈ s, 1 ≤ c i)
    {i₀ : ι} (hi₀ : i₀ ∈ s) : a i₀ = 1 := by
  have hpointwise : ∀ i ∈ s, c i ≤ a i * c i := fun i hi ↦ by
    nlinarith [ha i hi, hc i hi]
  have heach := (Finset.sum_eq_sum_iff_of_le hpointwise).mp hsum
  have hi := heach i₀ hi₀
  nlinarith [hi, hc i₀ hi₀]

set_option maxHeartbeats 1600000 in
/-- **The `s = 1` core — Silverman II.3.6**: for a maximal ideal `P` of `B` lying over the
maximal ideal `m_Q` of `C₂.CoordinateRing`, `relNorm_{C₂.CoordinateRing}(P) = m_Q`.

This is the perfect-base-free reproof (char-`p` separable leaf).  Instead of mathlib's
`relNorm_eq_pow_of_isMaximal` (which presupposes a perfect fraction field of the base ring),
we run the **global balance** over the integral closure `B`, exactly as the affine template
`PushforwardDivisor.relNorm_maximalIdealAt_eq`:

* `relNorm(P) = m_Q ^ s` for some `s` (`exists_relNorm_eq_pow_of_isPrime`), and `1 ≤ s`
  (else `relNorm P = ⊤`, contradicting `relNorm P ≤ comap P = m_Q ≠ ⊤`);
* `relNorm(m_Q · B) = m_Q ^ [K(C₁):K(C₂)]` (`relNorm_algebraMap` + `finrank_fractionRing_B_eq`);
* `m_Q · B = ∏_{P' | m_Q} P'^{e(P')}` (`map_algebraMap_eq_finsetProd_pow`), so the same norm is
  `m_Q ^ (Σ s(P')·e(P'))` with every `s(P') ≥ 1`; hence `[K(C₁):K(C₂)] = Σ s(P')·e(P')`;
* `Σ e(P')·f(P') = [K(C₁):K(C₂)]` (`Ideal.sum_ramification_inertia`, applicable *directly* because
  `B` is the integral closure) with `f(P') = 1` (`inertiaDeg_eq_one`), so `Σ e(P') = [K(C₁):K(C₂)]`;
* combining `Σ e(P') = Σ s(P')·e(P')` with `s(P'), e(P') ≥ 1` forces every `s(P') = 1`, in
  particular our `s`. -/
theorem relNorm_eq_of_under (P : Ideal (B (C₁ := C₁) (C₂ := C₂)))
    (hP : P.IsMaximal) (Q : C₂.SmoothPoint)
    (hPq : P.under C₂.CoordinateRing = C₂.maximalIdealAt Q) :
    Ideal.relNorm C₂.CoordinateRing P = C₂.maximalIdealAt Q := by
  classical
  haveI hQmax : (C₂.maximalIdealAt Q).IsMaximal := C₂.maximalIdealAt_isMaximal Q
  haveI hLies : P.LiesOver (C₂.maximalIdealAt Q) := ⟨hPq.symm⟩
  haveI hPprime : P.IsPrime := hP.isPrime
  set p : Ideal C₂.CoordinateRing := C₂.maximalIdealAt Q with hp_def
  have hp0 : p ≠ ⊥ := C₂.maximalIdealAt_ne_bot Q
  have hpNotUnit : ¬ IsUnit p := by rw [Ideal.isUnit_iff]; exact hQmax.ne_top
  -- `relNorm P = p ^ s`; it suffices to show `s = 1`, and `1 ≤ s`.
  obtain ⟨s, hs⟩ := Ideal.exists_relNorm_eq_pow_of_isPrime P p
  suffices hs1 : s = 1 by rw [hs, hs1, pow_one]
  have hge1 : 1 ≤ s := one_le_relNormExp_of_liesOver Q P s hs
  -- A uniform exponent function `sfn` on the fibre over `p`: `relNorm(P') = p ^ sfn(P')`, `sfn ≥ 1`.
  obtain ⟨sfn, hsfn_ge, hsfn_relNorm⟩ := exists_relNormExp_fn (C₁ := C₁) Q
  set ee : Ideal (B (C₁ := C₁) (C₂ := C₂)) → ℕ := fun P' => p.ramificationIdx P' with hee_def
  -- Membership in the explicit fibre finset gives `IsPrime ∧ LiesOver`.
  have hmem_iff : ∀ P', P' ∈ IsDedekindDomain.primesOverFinset p (B (C₁ := C₁) (C₂ := C₂)) ↔
      P' ∈ p.primesOver (B (C₁ := C₁) (C₂ := C₂)) :=
    fun P' => IsDedekindDomain.mem_primesOverFinset_iff (B := B (C₁ := C₁) (C₂ := C₂)) hp0
  -- The two balances: `d = Σ sfn·e` (relative-norm side) and `Σ e = d` (ramification side).
  have hdeg_eq : Module.finrank C₂.FunctionField C₁.FunctionField =
      ∑ P' ∈ IsDedekindDomain.primesOverFinset p (B (C₁ := C₁) (C₂ := C₂)), sfn P' * ee P' :=
    finrank_eq_sum_relNormExp_mul_ramificationIdx Q sfn hsfn_relNorm
  have hsume : ∑ P' ∈ IsDedekindDomain.primesOverFinset p (B (C₁ := C₁) (C₂ := C₂)), ee P' =
      Module.finrank C₂.FunctionField C₁.FunctionField :=
    sum_ramificationIdx_eq_finrank Q
  -- `Σ e = Σ sfn·e` with `e, sfn ≥ 1` pins every `sfn(P') = 1`, in particular `sfn P = s`.
  have hP_mem : P ∈ p.primesOver (B (C₁ := C₁) (C₂ := C₂)) := ⟨hPprime, hLies⟩
  have hsfn_P : sfn P = s :=
    (pow_inj_of_not_isUnit hpNotUnit hp0).mp ((hsfn_relNorm P hP_mem).symm.trans hs)
  have hsfn_one : sfn P = 1 :=
    eq_one_of_sum_eq_sum_mul (IsDedekindDomain.primesOverFinset p (B (C₁ := C₁) (C₂ := C₂))) sfn ee
      (by rw [hsume, ← hdeg_eq]) (fun P' hP' => hsfn_ge P' ((hmem_iff P').mp hP'))
      (fun P' hP' => one_le_ramificationIdx_of_mem_primesOver Q P' ((hmem_iff P').mp hP'))
      ((hmem_iff P).mpr hP_mem)
  rw [← hsfn_P, hsfn_one]

/-- **The `s = 1` core, smooth-point-free form**: for a maximal ideal `P` of `B` lying over the
maximal ideal `m` of `C₂.CoordinateRing` corresponding (via `exists_smoothPoint_of_isMaximal`) to
*some* smooth point of `C₂`, `relNorm(P) = m`.  Wraps `relNorm_eq_of_under` so the count lemma can
use it for a general `B`-prime without first naming the target smooth point. -/
theorem relNorm_eq_under (P : Ideal (B (C₁ := C₁) (C₂ := C₂)))
    (hP : P.IsMaximal) (hm : (P.under C₂.CoordinateRing).IsMaximal) :
    Ideal.relNorm C₂.CoordinateRing P = P.under C₂.CoordinateRing := by
  obtain ⟨Q, hQ⟩ := C₂.exists_smoothPoint_of_isMaximal hm
  rw [relNorm_eq_of_under P hP Q hQ.symm, hQ]

/-- **The `B`-primes over a maximal ideal are nonzero**: every prime `P` of `B` in
`primesOverFinset p` is `≠ ⊥`.  If `P = ⊥` then, since `C₂.CoordinateRing → B` is injective,
`P.under = ⊥`, contradicting maximality of `p`.  Supplies the `≠ ⊥` data needed to repackage each
fibre prime as a `HeightOneSpectrum`.  (`B`-analogue of `primesOverFinset_ne_bot` in
`PushforwardDivisor.lean`.) -/
private theorem primesOverFinset_B_ne_bot {p : Ideal C₂.CoordinateRing} [p.IsMaximal]
    (hp_ne : p ≠ ⊥) (P : Ideal (B (C₁ := C₁) (C₂ := C₂)))
    (hP : P ∈ IsDedekindDomain.primesOverFinset p (B (C₁ := C₁) (C₂ := C₂))) : P ≠ ⊥ := by
  rw [IsDedekindDomain.mem_primesOverFinset_iff (B := B (C₁ := C₁) (C₂ := C₂)) hp_ne] at hP
  intro h_eq
  apply hp_ne
  have h_over : p = P.under C₂.CoordinateRing := hP.2.over
  rw [h_eq, Ideal.under, Ideal.comap_bot_of_injective _
    (FaithfulSMul.algebraMap_injective C₂.CoordinateRing (B (C₁ := C₁) (C₂ := C₂)))] at h_over
  exact h_over

/-- **The associated relative-norm power is nonzero (over `B`)**: for a height-one prime `P` of `B`
and any exponent `k`, the associate of `(relNorm P.asIdeal)^k` is nonzero — the relative norm of a
nonzero ideal is nonzero (`relNorm_eq_bot_iff`) and powers of a nonzero ideal are nonzero.  Supplies
the nonvanishing side-condition of `count_finset_prod_factors`.  (`B`-analogue of
`associates_relNorm_pow_ne_zero`.) -/
private theorem associates_relNorm_B_pow_ne_zero
    (P : IsDedekindDomain.HeightOneSpectrum (B (C₁ := C₁) (C₂ := C₂))) (k : ℕ) :
    Associates.mk ((Ideal.relNorm C₂.CoordinateRing P.asIdeal) ^ k) ≠ 0 := by
  rw [Associates.mk_ne_zero]
  apply pow_ne_zero
  rw [Ne, Ideal.zero_eq_bot, Ideal.relNorm_eq_bot_iff]
  exact P.ne_bot

set_option maxHeartbeats 1600000 in
/-- **The relative norm of `span{w}` factors as a support sum of counts (over `B`)**: the
multiplicity of `m_Q` in `relNorm(span{w})` for `w ∈ B` equals `∑_{P ∈ S} count_{m_Q}((relNorm
P.asIdeal)^(count_P(span{w})))` for any finset `S` containing the multiplicative support of `P ↦
P.maxPowDividing(span{w})`.  Rewrite `span{w}` by its height-one factorisation, push `relNorm` and
`Associates.mk` through the finite product (`map_prod`), and apply `count_finset_prod_factors` (each
factor is nonzero by `associates_relNorm_B_pow_ne_zero`).  This isolates the product/`count`
bookkeeping from the per-place geometry.  (`B`-analogue of `count_relNorm_span_eq_sum_support`.) -/
private theorem count_relNorm_span_B_eq_sum_support (Q : C₂.SmoothPoint)
    {w : B (C₁ := C₁) (C₂ := C₂)} (hw : w ≠ 0)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum (B (C₁ := C₁) (C₂ := C₂))))
    (hS_supp : Function.mulSupport
      (fun P : IsDedekindDomain.HeightOneSpectrum (B (C₁ := C₁) (C₂ := C₂)) =>
        P.maxPowDividing (Ideal.span ({w} : Set _))) ⊆ ↑S) :
    (Associates.mk (C₂.maximalIdealAt Q)).count
        (Associates.mk (Ideal.relNorm C₂.CoordinateRing (Ideal.span {w}))).factors =
      ∑ P ∈ S, (Associates.mk (C₂.maximalIdealAt Q)).count
        (Associates.mk ((Ideal.relNorm C₂.CoordinateRing P.asIdeal) ^
          ((Associates.mk P.asIdeal).count
            (Associates.mk (Ideal.span ({w} : Set _))).factors))).factors := by
  classical
  set p : Ideal C₂.CoordinateRing := C₂.maximalIdealAt Q with hp_def
  haveI hpMax : p.IsMaximal := C₂.maximalIdealAt_isMaximal Q
  have hp_ne : p ≠ ⊥ := C₂.maximalIdealAt_ne_bot Q
  let vp : IsDedekindDomain.HeightOneSpectrum C₂.CoordinateRing :=
    ⟨p, hpMax.isPrime, hp_ne⟩
  have h_vp_irr : Irreducible (Associates.mk vp.asIdeal) := vp.associates_irreducible
  have hI_ne : Ideal.span ({w} : Set (B (C₁ := C₁) (C₂ := C₂))) ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hw
  have h_finprod_eq_prod :
      (∏ᶠ P : IsDedekindDomain.HeightOneSpectrum (B (C₁ := C₁) (C₂ := C₂)),
        P.maxPowDividing (Ideal.span ({w} : Set _))) =
      ∏ P ∈ S, P.maxPowDividing (Ideal.span ({w} : Set _)) :=
    finprod_eq_prod_of_mulSupport_subset _ hS_supp
  conv_lhs =>
    rw [← Ideal.finprod_heightOneSpectrum_factorization hI_ne, h_finprod_eq_prod,
      map_prod (Ideal.relNorm C₂.CoordinateRing)]
  simp_rw [IsDedekindDomain.HeightOneSpectrum.maxPowDividing, map_pow]
  rw [show Associates.mk (∏ P ∈ S, (Ideal.relNorm C₂.CoordinateRing) P.asIdeal ^
        (Associates.mk P.asIdeal).count
          (Associates.mk (Ideal.span ({w} : Set _))).factors) =
      ∏ P ∈ S, Associates.mk ((Ideal.relNorm C₂.CoordinateRing) P.asIdeal ^
        (Associates.mk P.asIdeal).count
          (Associates.mk (Ideal.span ({w} : Set _))).factors) from
      map_prod (Associates.mkMonoidHom (M := Ideal C₂.CoordinateRing)) _ _]
  rw [count_finset_prod_factors (fun P _ => associates_relNorm_B_pow_ne_zero P _) h_vp_irr]

set_option maxHeartbeats 1600000 in
/-- **Per-term count split** of the `relNorm`-factorisation product (over `B`): the count of `m_Q`
in `(relNorm P.asIdeal)^k` is `k` when `P` lies over `m_Q` and `0` otherwise.  In the matching
branch `relNorm(P) = m_Q` (via `relNorm_eq_under`, using `LiesOver`), so the count is `k`; in the
non-matching branch `relNorm(P) = P.under` is a different maximal ideal (realised as a smooth point
via `exists_smoothPoint_of_isMaximal`), so the count is `0`.  This is the `if-then-else` body that,
summed over the support finset, collapses the relative norm of the factorisation to the fibre sum.
(`B`-analogue of `count_factors_relNorm_pow_eq_ite`.) -/
private theorem count_factors_relNorm_B_pow_eq_ite (Q : C₂.SmoothPoint)
    (P : IsDedekindDomain.HeightOneSpectrum (B (C₁ := C₁) (C₂ := C₂))) (k : ℕ) :
    (Associates.mk (C₂.maximalIdealAt Q)).count
        (Associates.mk ((Ideal.relNorm C₂.CoordinateRing P.asIdeal) ^ k)).factors =
      if P.asIdeal ∈ IsDedekindDomain.primesOverFinset (C₂.maximalIdealAt Q)
          (B (C₁ := C₁) (C₂ := C₂)) then k else 0 := by
  classical
  set p : Ideal C₂.CoordinateRing := C₂.maximalIdealAt Q with hp_def
  haveI hpMax : p.IsMaximal := C₂.maximalIdealAt_isMaximal Q
  have hp_ne : p ≠ ⊥ := C₂.maximalIdealAt_ne_bot Q
  let vp : IsDedekindDomain.HeightOneSpectrum C₂.CoordinateRing :=
    ⟨p, hpMax.isPrime, hp_ne⟩
  have h_vp_irr : Irreducible (Associates.mk vp.asIdeal) := vp.associates_irreducible
  haveI hPmax : P.asIdeal.IsMaximal := Ideal.IsPrime.isMaximal P.isPrime P.ne_bot
  haveI hPunder_max : (P.asIdeal.under C₂.CoordinateRing).IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal P.asIdeal
  have hrelP : Ideal.relNorm C₂.CoordinateRing P.asIdeal = P.asIdeal.under C₂.CoordinateRing :=
    relNorm_eq_under P.asIdeal hPmax hPunder_max
  by_cases h_over : P.asIdeal ∈ IsDedekindDomain.primesOverFinset p (B (C₁ := C₁) (C₂ := C₂))
  · rw [if_pos h_over]
    haveI hPlies : P.asIdeal.LiesOver p :=
      ((IsDedekindDomain.mem_primesOverFinset_iff (B := B (C₁ := C₁) (C₂ := C₂)) hp_ne).mp
        h_over).2
    have hunder_eq : P.asIdeal.under C₂.CoordinateRing = p := hPlies.over.symm
    rw [hrelP, hunder_eq, Associates.mk_pow]
    change (Associates.mk vp.asIdeal).count (Associates.mk vp.asIdeal ^ _).factors = _
    rw [Associates.count_pow (by rw [Associates.mk_ne_zero]; exact hp_ne) h_vp_irr,
      Associates.count_self h_vp_irr, mul_one]
  · rw [if_neg h_over]
    have hPne : P.asIdeal.under C₂.CoordinateRing ≠ p := by
      intro hpe
      apply h_over
      rw [IsDedekindDomain.mem_primesOverFinset_iff (B := B (C₁ := C₁) (C₂ := C₂)) hp_ne]
      exact ⟨P.isPrime, ⟨hpe.symm⟩⟩
    rw [hrelP, Associates.mk_pow]
    obtain ⟨Q', hQ'⟩ := C₂.exists_smoothPoint_of_isMaximal hPunder_max
    have hP'_ne_bot2 : P.asIdeal.under C₂.CoordinateRing ≠ ⊥ := by
      rw [← hQ']; exact C₂.maximalIdealAt_ne_bot Q'
    let vP' : IsDedekindDomain.HeightOneSpectrum C₂.CoordinateRing :=
      ⟨_, hPunder_max.isPrime, hP'_ne_bot2⟩
    have h_vP'_irr : Irreducible (Associates.mk vP'.asIdeal) := vP'.associates_irreducible
    have h_vp_ne_vP' : (Associates.mk vp.asIdeal) ≠ (Associates.mk vP'.asIdeal) := by
      intro h_eq
      apply hPne
      rw [Associates.mk_eq_mk_iff_associated] at h_eq
      exact (associated_iff_eq.mp h_eq).symm
    change (Associates.mk vp.asIdeal).count (Associates.mk vP'.asIdeal ^ _).factors = 0
    rw [Associates.count_pow (by rw [Associates.mk_ne_zero]; exact hP'_ne_bot2) h_vp_irr,
      Associates.count_eq_zero_of_ne h_vp_irr h_vP'_irr h_vp_ne_vP', Nat.mul_zero]

/-- **A height-one support sum re-indexes onto a target ideal finset (over `B`)**: summing a term
`g P.asIdeal` over the height-one primes of `B` in a finset `S` whose ideal lies in a target finset
`T`, equals `∑_{I ∈ T} g I`, provided a repackaging `toHOS : T → HeightOneSpectrum` with
`(toHOS I).asIdeal = I` landing back in `S`.  The bijection sends `P ↦ P.asIdeal` with inverse
`toHOS`.  Purely combinatorial (no algebra); collapses the `relNorm`-factorisation support sum onto
`primesOverFinset`.  (`B`-analogue of `sum_filter_heightOneSpectrum_eq_sum_of_asIdeal`.) -/
private theorem sum_filter_heightOneSpectrum_B_eq_sum_of_asIdeal
    (S : Finset (IsDedekindDomain.HeightOneSpectrum (B (C₁ := C₁) (C₂ := C₂))))
    (T : Finset (Ideal (B (C₁ := C₁) (C₂ := C₂))))
    (toHOS : ∀ I ∈ T, IsDedekindDomain.HeightOneSpectrum (B (C₁ := C₁) (C₂ := C₂)))
    (htoHOS_asIdeal : ∀ I (hI : I ∈ T), (toHOS I hI).asIdeal = I)
    (htoHOS_mem : ∀ I (hI : I ∈ T), toHOS I hI ∈ S)
    (g : Ideal (B (C₁ := C₁) (C₂ := C₂)) → ℕ) :
    ∑ P ∈ S.filter (fun P => P.asIdeal ∈ T), g P.asIdeal = ∑ I ∈ T, g I := by
  refine Finset.sum_bij'
    (i := fun (P : IsDedekindDomain.HeightOneSpectrum (B (C₁ := C₁) (C₂ := C₂))) _ => P.asIdeal)
    (j := fun (I : Ideal (B (C₁ := C₁) (C₂ := C₂))) hI => toHOS I hI) ?_ ?_ ?_ ?_ ?_
  · intro P hP
    exact (Finset.mem_filter.mp hP).2
  · intro I hI
    refine Finset.mem_filter.mpr ⟨htoHOS_mem I hI, ?_⟩
    rw [htoHOS_asIdeal I hI]
    exact hI
  · intro P hP
    apply IsDedekindDomain.HeightOneSpectrum.ext
    exact htoHOS_asIdeal P.asIdeal (Finset.mem_filter.mp hP).2
  · intro I hI
    exact htoHOS_asIdeal I hI
  · intro P _
    rfl

/-! ### The per-place norm–divisor count over `B` (T-A2, the core)

The `B`-analogue of `CurveMap.count_relNorm_eq_sum_fiber` (`PushforwardDivisor.lean`): the
multiplicity of `m_Q` in `relNorm_{C₂.CoordinateRing}(span{w})` for `w ∈ B` is the fibre sum of the
multiplicities of the `B`-primes over `m_Q`.  Built on the `s = 1` core `relNorm_eq_under`
(`relNorm(P) = P.under` for a maximal `P` of `B`) — the genuine arithmetic of Silverman II.3.6 —
together with `relNorm` multiplicativity and `relNorm_singleton`. -/

set_option maxHeartbeats 1600000 in
/-- **The per-place norm–divisor count over `B`** (T-A2): for `w ∈ B` nonzero and a smooth point
`Q` of `C₂`, the `m_Q`-adic multiplicity of `relNorm(span{w})` equals the sum over the `B`-primes
`P` above `m_Q` of the `P`-adic multiplicity of `span{w}`.  All inertia degrees are `1`
(`inertiaDeg_eq_one`), so `relNorm(P^k) = m_Q^k` for `P` over `m_Q` and `relNorm(P'^k)` is prime to
`m_Q` for `P'` over a different maximal ideal. -/
theorem count_relNorm_eq_sum_fiber_B {w : B (C₁ := C₁) (C₂ := C₂)} (hw : w ≠ 0)
    (Q : C₂.SmoothPoint) :
    (Associates.mk (C₂.maximalIdealAt Q)).count
        (Associates.mk (Ideal.relNorm C₂.CoordinateRing (Ideal.span {w}))).factors =
      ∑ P ∈ IsDedekindDomain.primesOverFinset (C₂.maximalIdealAt Q)
          (B (C₁ := C₁) (C₂ := C₂)),
        (Associates.mk P).count (Associates.mk (Ideal.span ({w} : Set _))).factors := by
  classical
  set p : Ideal C₂.CoordinateRing := C₂.maximalIdealAt Q with hp_def
  haveI hpMax : p.IsMaximal := C₂.maximalIdealAt_isMaximal Q
  have hp_ne : p ≠ ⊥ := C₂.maximalIdealAt_ne_bot Q
  have hI_ne : Ideal.span ({w} : Set (B (C₁ := C₁) (C₂ := C₂))) ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hw
  -- The support finset `S`: the actual support of `span{w}` together with the (possibly
  -- non-dividing) primes over `p`, repackaged as height-one spectra, so both `S`-sums share it.
  have h_supp := Ideal.hasFiniteMulSupport (R := B (C₁ := C₁) (C₂ := C₂)) hI_ne
  let toHOS : ∀ P ∈ IsDedekindDomain.primesOverFinset p (B (C₁ := C₁) (C₂ := C₂)),
      IsDedekindDomain.HeightOneSpectrum (B (C₁ := C₁) (C₂ := C₂)) := fun P hP =>
    ⟨P, ((IsDedekindDomain.mem_primesOverFinset_iff (B := B (C₁ := C₁) (C₂ := C₂)) hp_ne).mp hP).1,
      primesOverFinset_B_ne_bot hp_ne P hP⟩
  let sH : Finset (IsDedekindDomain.HeightOneSpectrum (B (C₁ := C₁) (C₂ := C₂))) :=
    (IsDedekindDomain.primesOverFinset p (B (C₁ := C₁) (C₂ := C₂))).attach.image
      (fun ⟨P, hP⟩ => toHOS P hP)
  set S : Finset (IsDedekindDomain.HeightOneSpectrum (B (C₁ := C₁) (C₂ := C₂))) :=
    h_supp.toFinset ∪ sH with hS_def
  have hS_supp : Function.mulSupport
      (fun P : IsDedekindDomain.HeightOneSpectrum (B (C₁ := C₁) (C₂ := C₂)) =>
        P.maxPowDividing (Ideal.span ({w} : Set _))) ⊆ ↑S := by
    intro P hP
    simp only [hS_def, Finset.coe_union, Set.mem_union]
    left
    exact h_supp.mem_toFinset.mpr hP
  -- Factor the count of `m_Q` in `relNorm(span{w})` over the support `S`.
  rw [count_relNorm_span_B_eq_sum_support Q hw S hS_supp]
  -- Each term: `count_{m_Q}((relNorm P)^k) = k` if `P` lies over `m_Q`, else `0`.
  rw [Finset.sum_congr rfl (fun P _ => count_factors_relNorm_B_pow_eq_ite Q P _),
    Finset.sum_ite, Finset.sum_const_zero, add_zero]
  -- Re-index the surviving terms (primes over `m_Q`) onto `primesOverFinset`.
  exact sum_filter_heightOneSpectrum_B_eq_sum_of_asIdeal S
    (IsDedekindDomain.primesOverFinset p (B (C₁ := C₁) (C₂ := C₂))) toHOS
    (fun _ _ => rfl)
    (fun P'' hP'' => by
      simp only [hS_def, Finset.mem_union]
      right
      simp only [sH, Finset.mem_image, Finset.mem_attach, true_and, Subtype.exists]
      exact ⟨P'', hP'', rfl⟩)
    (fun P => (Associates.mk P).count (Associates.mk (Ideal.span ({w} : Set _))).factors)

end HasseWeil.Curves.NormConormIntegralClosure
