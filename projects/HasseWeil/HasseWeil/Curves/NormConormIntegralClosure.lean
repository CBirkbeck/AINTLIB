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
