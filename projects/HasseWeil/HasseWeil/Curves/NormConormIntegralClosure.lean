/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import HasseWeil.Curves.LocalizedDictionary
import HasseWeil.Curves.PushforwardDivisor
import HasseWeil.Curves.RamificationFinite
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
of `C₁`.  Stated as a named hypothesis so that the integrality reduction below is structural. -/
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
    IsDiscreteValuationRing (v.valuation C₁.FunctionField).valuationSubring := by
  have hsurj : Function.Surjective (v.valuation C₁.FunctionField) :=
    v.valuation_surjective C₁.FunctionField
  set w := v.valuation C₁.FunctionField with hw
  have hvg : MonoidWithZeroHom.valueGroup (.ofClass w) = ⊤ := by
    rw [eq_top_iff]
    intro y _
    rw [MonoidWithZeroHom.mem_valueGroup_iff_of_comm]
    refine ⟨1, by simp, ?_⟩
    obtain ⟨x, hx⟩ := hsurj (y : WithZero (Multiplicative ℤ))
    exact ⟨x, by rw [map_one, one_mul]; exact hx.symm⟩
  haveI : IsCyclic (WithZero (Multiplicative ℤ))ˣ :=
    isCyclic_of_surjective WithZero.unitsWithZeroEquiv.symm.toMonoidHom
      WithZero.unitsWithZeroEquiv.symm.surjective
  haveI : Nontrivial (WithZero (Multiplicative ℤ))ˣ :=
    WithZero.unitsWithZeroEquiv.symm.toEquiv.nontrivial
  haveI : IsCyclic (MonoidWithZeroHom.valueGroup (.ofClass w)) := by
    rw [hvg]
    exact isCyclic_of_surjective Subgroup.topEquiv.symm.toMonoidHom
      Subgroup.topEquiv.symm.surjective
  haveI : Nontrivial (MonoidWithZeroHom.valueGroup (.ofClass w)) := by
    rw [hvg]; exact Subgroup.topEquiv.symm.toEquiv.nontrivial
  exact Valuation.valuationSubring_isDiscreteValuationRing w

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
