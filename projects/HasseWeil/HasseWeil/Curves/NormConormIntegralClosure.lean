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
variable [PerfectField (FractionRing C₂.CoordinateRing)]
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
  have hpole : C₁.ordAtInfty (algebraMap C₂.FunctionField C₁.FunctionField C₂.coordX) =
      ((((e : ℤ) * (-2 : ℤ)) : ℤ) : WithTop ℤ) := by
    rw [hform C₂.coordX C₂.coordX_ne_zero, C₂.ordAtInfty_coordX, coe_nsmul_int]
  intro hv
  -- `coordX₂` image is a base-ring element of `B`, so `v ≤ 1` on it
  have hle : v.valuation C₁.FunctionField
      (algebraMap C₂.FunctionField C₁.FunctionField C₂.coordX) ≤ 1 := by
    have hcr : algebraMap C₂.CoordinateRing C₁.FunctionField
          (WeierstrassCurve.Affine.CoordinateRing.mk C₂.toAffine (Polynomial.C Polynomial.X)) =
        algebraMap C₂.FunctionField C₁.FunctionField C₂.coordX := by
      rw [SmoothPlaneCurve.coordX,
        IsScalarTower.algebraMap_apply C₂.CoordinateRing C₂.FunctionField C₁.FunctionField]
      rfl
    rw [← hcr]
    exact valuation_algebraMap_coordinateRing_le_one v _
  -- but `v = ordAtInftyValuation` and the pole forces `> 1`
  rw [hv] at hle
  have halg_ne : algebraMap C₂.FunctionField C₁.FunctionField C₂.coordX ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective C₂.FunctionField C₁.FunctionField)]
    exact C₂.coordX_ne_zero
  rw [C₁.ordAtInftyValuation_le_one_iff_ordAtInfty_nonneg halg_ne, hpole] at hle
  have he2 : ((e : ℤ) * (-2 : ℤ)) < 0 := by
    have : (1 : ℤ) ≤ e := by exact_mod_cast he
    nlinarith
  rw [show (0 : WithTop ℤ) = ((0 : ℤ) : WithTop ℤ) from rfl, WithTop.coe_le_coe] at hle
  omega

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
    refine mul_le_one' ?_ (pow_le_one₀ zero_le' hy)
    induction a using Polynomial.induction_on' with
    | add p q hp hq =>
      rw [Polynomial.C_add, map_add, map_add]
      exact le_trans (w.map_add _ _) (max_le hp hq)
    | monomial m c =>
      rw [← Polynomial.C_mul_X_pow_eq_monomial, Polynomial.C_mul, Polynomial.C_pow,
        map_mul, map_mul, map_pow, map_pow, w.map_mul, map_pow w]
      refine mul_le_one' ?_ (pow_le_one₀ zero_le' hx)
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
            mul_le_mul_right' (valuation_algebraMap_coordinateRing_C₁_le_one v hx hy r) _
      _ < 1 := by rw [one_mul]; exact ha

@[simp] theorem mem_centerIdealOnC₁
    (v : IsDedekindDomain.HeightOneSpectrum (B (C₁ := C₁) (C₂ := C₂)))
    (hx : v.valuation C₁.FunctionField (coordXFun C₁) ≤ 1)
    (hy : v.valuation C₁.FunctionField (coordYFun C₁) ≤ 1)
    (a : C₁.CoordinateRing) :
    a ∈ centerIdealOnC₁ v hx hy ↔
      v.valuation C₁.FunctionField (algebraMap C₁.CoordinateRing C₁.FunctionField a) < 1 :=
  Iff.rfl

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
  set c : Ideal C₁.CoordinateRing := centerIdealOnC₁ v hx hy with hc_def
  -- `c` is prime: `1 ∉ c` (`w 1 = 1`), and `w (algMap a)·w (algMap b) < 1` forces one factor `< 1`.
  have hc_prime : c.IsPrime := by
    refine ⟨?_, ?_⟩
    · rw [Ideal.ne_top_iff_one, hc_def, mem_centerIdealOnC₁, map_one, map_one]
      exact lt_irrefl 1
    · intro a b hab
      rw [hc_def, mem_centerIdealOnC₁, map_mul, (w).map_mul] at hab
      by_contra h
      push_neg at h
      obtain ⟨ha, hb⟩ := h
      rw [hc_def, mem_centerIdealOnC₁, not_lt] at ha hb
      have ha1 : w (algebraMap C₁.CoordinateRing C₁.FunctionField a) = 1 :=
        le_antisymm (valuation_algebraMap_coordinateRing_C₁_le_one v hx hy a) ha
      have hb1 : w (algebraMap C₁.CoordinateRing C₁.FunctionField b) = 1 :=
        le_antisymm (valuation_algebraMap_coordinateRing_C₁_le_one v hx hy b) hb
      rw [ha1, hb1, one_mul] at hab
      exact lt_irrefl 1 hab
  -- `c ≠ ⊥`: otherwise `w` is trivial (`w (algMap a) = 1` for all nonzero `a`, so `w f = 1` ∀ f).
  have hc_ne_bot : c ≠ ⊥ := by
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
  -- `c` is maximal: a nonzero prime in the Dedekind domain `F[C₁]`.
  have hc_max : c.IsMaximal := hc_prime.isMaximal hc_ne_bot
  obtain ⟨P, hP⟩ := C₁.exists_smoothPoint_of_isMaximal hc_max
  refine ⟨P, ?_⟩
  -- The two valuation subrings: `A := O_v`, `B' := O_{pointValuation P}`.
  set A : ValuationSubring C₁.FunctionField := w.valuationSubring with hA
  set Bv : ValuationSubring C₁.FunctionField := (C₁.pointValuation P).valuationSubring with hBv
  -- `B'` is a DVR (rank-one): `pointValuation P` is surjective onto `ℤᵐ⁰`.
  have hpvsurj : Function.Surjective (C₁.pointValuation P) :=
    (IsDiscreteValuationRing.maximalIdeal (C₁.localRingAt P)).valuation_surjective C₁.FunctionField
  haveI : IsDiscreteValuationRing Bv :=
    valuationSubring_isDVR_of_surjective_withZeroInt _ hpvsurj
  -- `Bv ⊆ A`: every `pointValuation P`-integer is a `v`-integer.
  have hBA : Bv ≤ A := by
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
      have hsv_in_c : sv ∈ c := (mem_centerIdealOnC₁ v hx hy sv).mpr hlt
      exact hs_notin (hP.symm ▸ hsv_in_c)
    refine (Valuation.mem_valuationSubring_iff _ f).mpr ?_
    rw [hf_eq, map_div₀ w, hws, div_one]
    exact valuation_algebraMap_coordinateRing_C₁_le_one v hx hy a
  -- `A ≠ ⊤`: `w = v.valuation` is nontrivial (surjective onto `ℤᵐ⁰`).
  have hAtop : A ≠ ⊤ := by
    have hNontriv : w.IsNontrivial := by
      refine ⟨?_⟩
      obtain ⟨z, hz⟩ := hwsurj (WithZero.exp (1 : ℤ))
      refine ⟨z, ?_, ?_⟩
      · rw [hz]; exact WithZero.exp_ne_zero
      · rw [hz, show (1 : WithZero (Multiplicative ℤ)) = WithZero.exp (0 : ℤ) from
          (WithZero.exp_zero).symm, Ne, WithZero.exp_inj]; norm_num
    intro htop
    rw [hA] at htop
    exact (Valuation.valuationSubring_eq_top_iff _).mp htop hNontriv
  -- DVR-domination: `Bv = A`, then upgrade the equal subrings to the value identity.
  have hEq : Bv = A := rankOne_valuationSubring_le_eq_of_ne_top Bv A hBA hAtop
  have h_isEquiv : w.IsEquiv (C₁.pointValuation P) := by
    rw [Valuation.isEquiv_iff_valuationSubring]; rw [hA, hBv] at hEq; exact hEq.symm
  exact Valuation.isEquiv_iff_eq_of_surjective_withZeroInt _ _ hwsurj hpvsurj h_isEquiv

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
  -- `O_∞ ≠ ⊤`: `ordAtInftyValuation` is nontrivial (surjective onto `ℤᵐ⁰`).
  have hBtop : C₁.ordAtInftyValuation.valuationSubring ≠ ⊤ := by
    have hNontriv : C₁.ordAtInftyValuation.IsNontrivial := by
      refine ⟨?_⟩
      obtain ⟨z, hz⟩ := C₁.ordAtInftyValuation_surjective (WithZero.exp (1 : ℤ))
      refine ⟨z, ?_, ?_⟩
      · rw [hz]; exact WithZero.exp_ne_zero
      · rw [hz, show (1 : WithZero (Multiplicative ℤ)) = WithZero.exp (0 : ℤ) from
          (WithZero.exp_zero).symm, Ne, WithZero.exp_inj]; norm_num
    intro htop; exact (Valuation.valuationSubring_eq_top_iff _).mp htop hNontriv
  -- DVR-domination: `O_v = O_∞`, then upgrade equal subrings to the value identity.
  have hEq : w.valuationSubring = C₁.ordAtInftyValuation.valuationSubring :=
    rankOne_valuationSubring_le_eq_of_ne_top _ _ hsub hBtop
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
        mul_le_mul_left' hcinv_le _
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
    · rw [h0, map_zero (algebraMap F C₁.FunctionField), w.map_zero, zero_mul]; exact zero_le'
    · rw [valuation_algebraMap_F_eq_one v h0, one_mul]
  have ha₃ : w (algebraMap F C₁.FunctionField C₁.toAffine.a₃) ≤ w (coordXFun C₁) := by
    rcases eq_or_ne C₁.toAffine.a₃ 0 with h0 | h0
    · rw [h0, map_zero (algebraMap F C₁.FunctionField), w.map_zero]; exact zero_le'
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
      ≤ 1 * w t ^ k := mul_le_mul_right' (hc c) _
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
        exact zero_le'
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
        ≤ 1 * w (coordXFun C₁) := mul_le_mul_right' (hc _) _
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
      exact mul_le_mul_right' (valuation_a₁X_add_a₃_le_generic w h1X hc) _
  -- trichotomy: `Y ≤ X²`
  by_contra hcon
  rw [not_le] at hcon
  have hYne : Y ≠ 0 := by
    rw [hYdef, Ne, Valuation.zero_iff]; exact coordYFun_ne_zero (C₁ := C₁)
  have hX0 : (0 : Γ₀) < X := lt_of_lt_of_le one_pos h1X
  have hY0 : (0 : Γ₀) < Y := zero_lt_iff.mpr hYne
  have hXleX2 : X ≤ X ^ 2 := by
    calc X = X * 1 := (mul_one X).symm
      _ ≤ X * X := mul_le_mul_left' h1X X
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
    · rw [h0, map_zero (algebraMap F C₁.FunctionField), w.map_zero]; exact zero_le'
    · exact le_of_eq (valuation_algebraMap_F_eq_one v h0)
  exact valuation_coordYFun_le_sq_generic w hx hc

/-- `coordXFun C₁ = algebraMap (FractionRing F[X]) K(C₁) (algebraMap F[X] _ X)` (the `x₁` coordinate
as the image of the fraction-field `X`). -/
theorem coordXFun_eq_algebraMap_fracX :
    coordXFun C₁ = algebraMap (FractionRing (Polynomial F)) C₁.FunctionField
      (algebraMap (Polynomial F) (FractionRing (Polynomial F)) Polynomial.X) := by
  rw [coordXFun_eq_coordX, SmoothPlaneCurve.coordX,
    IsScalarTower.algebraMap_apply (Polynomial F) (FractionRing (Polynomial F)) C₁.FunctionField]

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
  -- rewrite `g = a + bcoeff·y₁`
  set a : C₁.FunctionField :=
    algebraMap (FractionRing (Polynomial F)) C₁.FunctionField p with ha_def
  set bcoeff : C₁.FunctionField :=
    algebraMap (FractionRing (Polynomial F)) C₁.FunctionField q with hb_def
  have hg_eq : g = a + bcoeff * C₁.coordYInFunctionField := by
    rw [hpq, Algebra.smul_def, mul_one, Algebra.smul_def]
  -- the basis ord identity
  have hmin : C₁.ordAtInfty g =
      min (C₁.ordAtInfty a) (C₁.ordAtInfty bcoeff + C₁.ordAtInfty C₁.coordYInFunctionField) := by
    rw [hg_eq, ha_def, hb_def]; exact C₁.ordAtInfty_basis_eq_min p q
  rw [hmin, le_min_iff] at hg
  obtain ⟨hga, hgby⟩ := hg
  -- `w_v(a) ≤ 1`
  have hwa : w a ≤ 1 := valuation_algebraMap_fracPolyX_le_one_of_ordAtInfty_nonneg v hx hga
  -- `w_v(bcoeff · y₁) ≤ 1`
  have hwby : w (bcoeff * C₁.coordYInFunctionField) ≤ 1 := by
    rcases eq_or_ne q 0 with hq0 | hq0
    · rw [hb_def, hq0, map_zero, zero_mul, w.map_zero]; exact zero_le_one
    · -- `ord_∞ bcoeff` is even
      obtain ⟨k, hk⟩ : ∃ k : ℤ, C₁.ordAtInfty bcoeff = ((2 * k : ℤ) : WithTop ℤ) := by
        refine ⟨-(RatFunc.ofFractionRing q : RatFunc F).intDegree, ?_⟩
        rw [hb_def, C₁.ordAtInfty_algebraMap_fracPolyX_of_ne_zero hq0]
        congr 1; ring
      -- from `0 ≤ ord_∞ bcoeff + ord_∞ y₁ = 2k - 3`: `2k ≥ 4`, so `0 ≤ ord_∞(bcoeff·x₁²)`
      rw [hk, C₁.ordAtInfty_coordYInFunctionField, ← WithTop.coe_add,
        show (0 : WithTop ℤ) = ((0 : ℤ) : WithTop ℤ) from rfl, WithTop.coe_le_coe] at hgby
      have h2k : (4 : ℤ) ≤ 2 * k := by omega
      -- `bcoeff·y₁ = (bcoeff·x₁²)·(y₁/x₁²)`
      have hxne : coordXFun C₁ ≠ 0 := by rw [coordXFun_eq_coordX]; exact C₁.coordX_ne_zero
      have hx2ne : (coordXFun C₁ ^ 2 : C₁.FunctionField) ≠ 0 := pow_ne_zero _ hxne
      have hsplit : bcoeff * C₁.coordYInFunctionField =
          (bcoeff * coordXFun C₁ ^ 2) * (coordYFun C₁ / coordXFun C₁ ^ 2) := by
        rw [coordYFun_eq_coordYInFunctionField]
        field_simp
      -- `bcoeff·x₁² = algMap (q · X²)`, regular at `∞`
      have hbx2 : bcoeff * coordXFun C₁ ^ 2 =
          algebraMap (FractionRing (Polynomial F)) C₁.FunctionField
            (q * (algebraMap (Polynomial F) (FractionRing (Polynomial F)) Polynomial.X) ^ 2) := by
        rw [map_mul, map_pow, hb_def, ← coordXFun_eq_algebraMap_fracX]
      have hord_bx2 : (0 : WithTop ℤ) ≤ C₁.ordAtInfty (bcoeff * coordXFun C₁ ^ 2) := by
        have hbne : bcoeff ≠ 0 :=
          (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective _ _)).mpr hq0
        rw [C₁.ordAtInfty_mul hbne hx2ne, hk]
        rw [show C₁.ordAtInfty (coordXFun C₁ ^ 2) = ((2 * (-2) : ℤ) : WithTop ℤ) by
          rw [C₁.ordAtInfty_pow hxne 2, ordAtInfty_coordXFun]; norm_cast,
          ← WithTop.coe_add,
          show (0 : WithTop ℤ) = ((0 : ℤ) : WithTop ℤ) from rfl, WithTop.coe_le_coe]
        omega
      have hwbx2 : w (bcoeff * coordXFun C₁ ^ 2) ≤ 1 := by
        rw [hbx2]
        exact valuation_algebraMap_fracPolyX_le_one_of_ordAtInfty_nonneg v hx (hbx2 ▸ hord_bx2)
      rw [hsplit, w.map_mul]
      calc w (bcoeff * coordXFun C₁ ^ 2) * w (coordYFun C₁ / coordXFun C₁ ^ 2)
          ≤ 1 * 1 := mul_le_mul' hwbx2 (valuation_coordYFun_div_coordXFun_sq_le_one v hx)
        _ = 1 := mul_one 1
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
/-- **No `B`-prime has a `y₁`-pole** (the `coordYFun` half): for a `B`-prime `v`, `w_v(y₁) ≤ 1`.
Once `w_v(x₁) ≤ 1` (`valuation_coordXFun_le_one`), `y₁` is `v`-integral because it is integral over
`F[x₁]` (the Weierstrass relation `y₁² + b·y₁ = c` with `w_v(b), w_v(c) ≤ 1`): a pole of `y₁` would
make `w_v(y₁)² = w_v(c − b·y₁) ≤ max(w_v c, w_v b · w_v y₁) ≤ w_v(y₁)`, impossible. -/
theorem valuation_coordYFun_le_one (hreg : OrdAtInftyReg (C₁ := C₁) (C₂ := C₂))
    (v : IsDedekindDomain.HeightOneSpectrum (B (C₁ := C₁) (C₂ := C₂))) :
    v.valuation C₁.FunctionField (coordYFun C₁) ≤ 1 := by
  set w := v.valuation C₁.FunctionField with hw
  have hxle : w (coordXFun C₁) ≤ 1 := valuation_coordXFun_le_one hreg v
  have hc : ∀ c : F, w (algebraMap F C₁.FunctionField c) ≤ 1 := fun c => by
    rcases eq_or_ne c 0 with h0 | h0
    · rw [h0, map_zero (algebraMap F C₁.FunctionField), w.map_zero]; exact zero_le'
    · exact le_of_eq (valuation_algebraMap_F_eq_one v h0)
  -- the Weierstrass relation, rearranged: `y₁² = c − b·y₁`
  have hyeq : coordYFun C₁ ^ 2 =
      (coordXFun C₁ ^ 3 + algebraMap F C₁.FunctionField C₁.toAffine.a₂ * coordXFun C₁ ^ 2 +
        algebraMap F C₁.FunctionField C₁.toAffine.a₄ * coordXFun C₁ +
        algebraMap F C₁.FunctionField C₁.toAffine.a₆) -
      (algebraMap F C₁.FunctionField C₁.toAffine.a₁ * coordXFun C₁ +
        algebraMap F C₁.FunctionField C₁.toAffine.a₃) * coordYFun C₁ := by
    linear_combination weierstrass_relation_coordFun (C₁ := C₁)
  -- bounds on the cubic and linear coefficients (using `w x₁ ≤ 1`)
  have hcubic : w (coordXFun C₁ ^ 3 +
      algebraMap F C₁.FunctionField C₁.toAffine.a₂ * coordXFun C₁ ^ 2 +
      algebraMap F C₁.FunctionField C₁.toAffine.a₄ * coordXFun C₁ +
      algebraMap F C₁.FunctionField C₁.toAffine.a₆) ≤ 1 := by
    have hx3 : w (coordXFun C₁ ^ 3) ≤ 1 := by
      rw [map_pow]; exact pow_le_one₀ zero_le' hxle
    have hmono : ∀ (cf : F) (k : ℕ),
        w (algebraMap F C₁.FunctionField cf * coordXFun C₁ ^ k) ≤ 1 := by
      intro cf k
      rw [w.map_mul, map_pow]
      calc w (algebraMap F C₁.FunctionField cf) * w (coordXFun C₁) ^ k
          ≤ 1 * 1 := mul_le_mul' (hc cf) (pow_le_one₀ zero_le' hxle)
        _ = 1 := mul_one 1
    have ha₂ := hmono C₁.toAffine.a₂ 2
    have ha₄' : w (algebraMap F C₁.FunctionField C₁.toAffine.a₄ * coordXFun C₁) ≤ 1 := by
      have := hmono C₁.toAffine.a₄ 1; rwa [pow_one] at this
    have hstep1 : w (coordXFun C₁ ^ 3 +
        algebraMap F C₁.FunctionField C₁.toAffine.a₂ * coordXFun C₁ ^ 2) ≤ 1 :=
      le_trans (w.map_add _ _) (max_le hx3 ha₂)
    have hstep2 : w (coordXFun C₁ ^ 3 +
        algebraMap F C₁.FunctionField C₁.toAffine.a₂ * coordXFun C₁ ^ 2 +
        algebraMap F C₁.FunctionField C₁.toAffine.a₄ * coordXFun C₁) ≤ 1 :=
      le_trans (w.map_add _ _) (max_le hstep1 ha₄')
    exact le_trans (w.map_add _ _) (max_le hstep2 (hc _))
  have hlin : w (algebraMap F C₁.FunctionField C₁.toAffine.a₁ * coordXFun C₁ +
      algebraMap F C₁.FunctionField C₁.toAffine.a₃) ≤ 1 := by
    have ha₁ : w (algebraMap F C₁.FunctionField C₁.toAffine.a₁ * coordXFun C₁) ≤ 1 := by
      rw [w.map_mul]
      calc w (algebraMap F C₁.FunctionField C₁.toAffine.a₁) * w (coordXFun C₁)
          ≤ 1 * 1 := mul_le_mul' (hc _) hxle
        _ = 1 := mul_one 1
    exact le_trans (w.map_add _ _) (max_le ha₁ (hc _))
  -- ultrametric: `w(y₁)² ≤ max(1, w(y₁))`, force `w(y₁) ≤ 1`
  by_contra hcon
  rw [not_le] at hcon
  have hYsq : w (coordYFun C₁) ^ 2 ≤ w (coordYFun C₁) := by
    rw [← map_pow, hyeq]
    refine le_trans (Valuation.map_sub w _ _) (max_le (le_trans hcubic (le_of_lt hcon)) ?_)
    rw [w.map_mul]
    calc w (algebraMap F C₁.FunctionField C₁.toAffine.a₁ * coordXFun C₁ +
            algebraMap F C₁.FunctionField C₁.toAffine.a₃) * w (coordYFun C₁)
        ≤ 1 * w (coordYFun C₁) := mul_le_mul_right' hlin _
      _ = w (coordYFun C₁) := one_mul _
  have hYne : w (coordYFun C₁) ≠ 0 := by
    rw [Ne, Valuation.zero_iff]; exact coordYFun_ne_zero (C₁ := C₁)
  have hY0 : (0 : WithZero (Multiplicative ℤ)) < w (coordYFun C₁) := zero_lt_iff.mpr hYne
  -- `w(y₁)² > w(y₁)` since `w(y₁) > 1`, contradicting `hYsq`
  have hlt : w (coordYFun C₁) < w (coordYFun C₁) ^ 2 := by
    have hstep := (mul_lt_mul_iff_left₀ hY0).mpr hcon
    rwa [one_mul, ← sq] at hstep
  exact absurd hYsq (not_le.mpr hlt)

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

/-- **The `s = 1` core — Silverman II.3.6**: for a maximal ideal `P` of `B` lying over the
maximal ideal `m_Q` of `C₂.CoordinateRing`, `relNorm_{C₂.CoordinateRing}(P) = m_Q`.  Over char-0
this is mathlib's `relNorm_eq_pow_of_isMaximal` (`relNorm P = m_Q ^ inertiaDeg`) with the inertia
degree `1` over an algebraically closed base. -/
theorem relNorm_eq_of_under (P : Ideal (B (C₁ := C₁) (C₂ := C₂)))
    (hP : P.IsMaximal) (Q : C₂.SmoothPoint)
    (hPq : P.under C₂.CoordinateRing = C₂.maximalIdealAt Q) :
    Ideal.relNorm C₂.CoordinateRing P = C₂.maximalIdealAt Q := by
  haveI : (C₂.maximalIdealAt Q).IsMaximal := C₂.maximalIdealAt_isMaximal Q
  haveI hLies : P.LiesOver (C₂.maximalIdealAt Q) := ⟨hPq.symm⟩
  rw [Ideal.relNorm_eq_pow_of_isMaximal P (C₂.maximalIdealAt Q),
    inertiaDeg_eq_one P Q hP.isPrime hPq, pow_one]

/-- **The `s = 1` core, smooth-point-free form**: for a maximal ideal `P` of `B` lying over the
maximal ideal `m` of `C₂.CoordinateRing` corresponding (via `exists_smoothPoint_of_isMaximal`) to
*some* smooth point of `C₂`, `relNorm(P) = m`.  Wraps `relNorm_eq_of_under` so the count lemma can
use it for a general `B`-prime without first naming the target smooth point. -/
theorem relNorm_eq_under (P : Ideal (B (C₁ := C₁) (C₂ := C₂)))
    (hP : P.IsMaximal) (hm : (P.under C₂.CoordinateRing).IsMaximal) :
    Ideal.relNorm C₂.CoordinateRing P = P.under C₂.CoordinateRing := by
  obtain ⟨Q, hQ⟩ := C₂.exists_smoothPoint_of_isMaximal hm
  rw [relNorm_eq_of_under P hP Q hQ.symm, hQ]

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
  let vp : IsDedekindDomain.HeightOneSpectrum C₂.CoordinateRing :=
    ⟨p, hpMax.isPrime, hp_ne⟩
  have h_vp_irr : Irreducible (Associates.mk vp.asIdeal) := vp.associates_irreducible
  have hI_ne : Ideal.span ({w} : Set (B (C₁ := C₁) (C₂ := C₂))) ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hw
  have h_supp := Ideal.hasFiniteMulSupport (R := B (C₁ := C₁) (C₂ := C₂)) hI_ne
  have h_prime_ne_bot : ∀ P ∈ IsDedekindDomain.primesOverFinset p (B (C₁ := C₁) (C₂ := C₂)),
      P ≠ ⊥ := by
    intro P hP
    rw [IsDedekindDomain.mem_primesOverFinset_iff (B := B (C₁ := C₁) (C₂ := C₂)) hp_ne] at hP
    intro h_eq
    apply hp_ne
    have h_over : p = P.under C₂.CoordinateRing := hP.2.over
    rw [h_eq, Ideal.under, Ideal.comap_bot_of_injective _
      (FaithfulSMul.algebraMap_injective C₂.CoordinateRing (B (C₁ := C₁) (C₂ := C₂)))] at h_over
    exact h_over
  let toHOS : ∀ P ∈ IsDedekindDomain.primesOverFinset p (B (C₁ := C₁) (C₂ := C₂)),
      IsDedekindDomain.HeightOneSpectrum (B (C₁ := C₁) (C₂ := C₂)) := fun P hP =>
    ⟨P, ((IsDedekindDomain.mem_primesOverFinset_iff (B := B (C₁ := C₁) (C₂ := C₂)) hp_ne).mp hP).1,
      h_prime_ne_bot P hP⟩
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
  have h_finprod_eq_prod :
      (∏ᶠ P : IsDedekindDomain.HeightOneSpectrum (B (C₁ := C₁) (C₂ := C₂)),
        P.maxPowDividing (Ideal.span ({w} : Set _))) =
      ∏ P ∈ S, P.maxPowDividing (Ideal.span ({w} : Set _)) :=
    finprod_eq_prod_of_mulSupport_subset _ hS_supp
  conv_lhs =>
    rw [← Ideal.finprod_heightOneSpectrum_factorization hI_ne, h_finprod_eq_prod,
      map_prod (Ideal.relNorm C₂.CoordinateRing)]
  simp_rw [IsDedekindDomain.HeightOneSpectrum.maxPowDividing, map_pow]
  have h_term_ne : ∀ P ∈ S,
      Associates.mk ((Ideal.relNorm C₂.CoordinateRing P.asIdeal) ^
        ((Associates.mk P.asIdeal).count
          (Associates.mk (Ideal.span ({w} : Set _))).factors)) ≠ 0 := by
    intro P _
    rw [Associates.mk_ne_zero]
    apply pow_ne_zero
    rw [Ne, Ideal.zero_eq_bot, Ideal.relNorm_eq_bot_iff]
    exact P.ne_bot
  rw [show Associates.mk (∏ P ∈ S, (Ideal.relNorm C₂.CoordinateRing) P.asIdeal ^
        (Associates.mk P.asIdeal).count
          (Associates.mk (Ideal.span ({w} : Set _))).factors) =
      ∏ P ∈ S, Associates.mk ((Ideal.relNorm C₂.CoordinateRing) P.asIdeal ^
        (Associates.mk P.asIdeal).count
          (Associates.mk (Ideal.span ({w} : Set _))).factors) from
      map_prod (Associates.mkMonoidHom (M := Ideal C₂.CoordinateRing)) _ _]
  rw [count_finset_prod_factors h_term_ne h_vp_irr]
  have h_S_split : ∀ P ∈ S,
      (Associates.mk vp.asIdeal).count
        (Associates.mk ((Ideal.relNorm C₂.CoordinateRing P.asIdeal) ^
          ((Associates.mk P.asIdeal).count
            (Associates.mk (Ideal.span ({w} : Set _))).factors))).factors =
      if P.asIdeal ∈ IsDedekindDomain.primesOverFinset p (B (C₁ := C₁) (C₂ := C₂)) then
        (Associates.mk P.asIdeal).count (Associates.mk (Ideal.span ({w} : Set _))).factors
      else 0 := by
    intro P _
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
  rw [Finset.sum_congr rfl h_S_split, Finset.sum_ite, Finset.sum_const_zero, add_zero]
  refine Finset.sum_bij'
    (i := fun (P : IsDedekindDomain.HeightOneSpectrum (B (C₁ := C₁) (C₂ := C₂))) _ => P.asIdeal)
    (j := fun (P'' : Ideal (B (C₁ := C₁) (C₂ := C₂))) hP'' => toHOS P'' hP'') ?_ ?_ ?_ ?_ ?_
  · intro P hP
    exact (Finset.mem_filter.mp hP).2
  · intro P'' hP''
    refine Finset.mem_filter.mpr ⟨?_, ?_⟩
    · simp only [hS_def, Finset.mem_union]
      right
      simp only [sH, Finset.mem_image, Finset.mem_attach, true_and, Subtype.exists]
      exact ⟨P'', hP'', rfl⟩
    · exact hP''
  · intro P hP
    apply IsDedekindDomain.HeightOneSpectrum.ext
    rfl
  · intro P'' hP''
    rfl
  · intro P hP
    rfl

end HasseWeil.Curves.NormConormIntegralClosure
