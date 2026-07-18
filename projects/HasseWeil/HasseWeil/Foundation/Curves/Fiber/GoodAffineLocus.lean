/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import HasseWeil.Foundation.Curves.IntegralClosure
import HasseWeil.Foundation.Curves.Ramification.RamificationFinite
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.Localization.LocalizationLocalization

/-!
# Good affine loci on a smooth plane curve and finiteness of the ramified locus

**ROUTE-W, ticket W-1** (curve instantiation of `HasseWeil.Curves.RamificationFinite`).

For a smooth plane curve `C₂` we take as "coordinate ring of a good affine open" a
localization `Af` of `C₂.CoordinateRing` away from a single nonzero element `f`
(equivalently, away from the finite set of points where `f` vanishes), packaged
abstractly as `[IsLocalization.Away f Af]`; the concrete model `Localization.Away f`
satisfies this.  We prove:

* `GoodAffineLocus.isDomain_away`, `GoodAffineLocus.isDedekindDomain_away`: `Af` is a
  Dedekind domain (a localization of the Dedekind domain `C₂.CoordinateRing` at a
  submonoid of nonzero elements, mathlib's `IsLocalization.isDedekindDomain`).  As in
  `HasseWeil/Curves/IntegralClosure.lean`, Dedekindness of the coordinate ring is
  carried as the hypothesis `[IsIntegrallyClosed C₂.CoordinateRing]`.
* `GoodAffineLocus.isFractionRing_away`: localizing does not change the fraction field,
  so `Af` still has fraction field `C₂.FunctionField`
  (mathlib's `IsFractionRing.isFractionRing_of_isDomain_of_isLocalization`).
* Along a finite separable extension `C₂.FunctionField → C₁.FunctionField` (for a curve
  map `φ : CurveMap C₁ C₂` this is `φ.pullback`, with the algebra structure
  `φ.toAlgebra`), the integral closure `B := integralClosure Af C₁.FunctionField` is a
  Dedekind domain, module-finite over `Af`, with fraction field `C₁.FunctionField`
  (`GoodAffineLocus.isDedekindDomain_integralClosure` etc.), and **all but finitely many
  primes of `Af` are unramified in `B`**
  (`GoodAffineLocus.exists_finite_ramification_locus`).

## Wiring notes for W-3

The extension `C₂.FunctionField → C₁.FunctionField` is taken as an abstract algebra
structure `[Algebra C₂.FunctionField C₁.FunctionField]` together with
`[FiniteDimensional _ _]` and `[Algebra.IsSeparable _ _]`.  For a concrete curve map
`φ : CurveMap C₁ C₂` these are supplied at the use site by
`haveI := φ.toAlgebra` (see the degree section of `HasseWeil/Curves/CurveMap.lean` for
this idiom) together with the project's finiteness/separability results for `φ`.
Similarly the compatible `Af`-algebra structure on `C₁.FunctionField` is supplied by
`(algebraMap _ _).comp (algebraMap _ _)` along the tower
`Af → C₂.FunctionField → C₁.FunctionField`; see the precise list at the end of the
module docstring of this file's `Extension` section.
-/

namespace HasseWeil.Curves.GoodAffineLocus

open scoped nonZeroDivisors

variable {F : Type*} [Field F] (C₂ : SmoothPlaneCurve F) (f : C₂.CoordinateRing)
variable (Af : Type*) [CommRing Af] [Algebra C₂.CoordinateRing Af] [IsLocalization.Away f Af]

/-! ### The good affine open: a localization of the coordinate ring (W-1)

`Af` is any realization of the localization of `C₂.CoordinateRing` away from `f ≠ 0`,
e.g. `Localization.Away f`. -/

/-- A localization of the coordinate ring away from a nonzero element is a domain. -/
theorem isDomain_away (hf : f ≠ 0) : IsDomain Af :=
  IsLocalization.isDomain_of_le_nonZeroDivisors Af
    (Submonoid.powers_le.mpr (mem_nonZeroDivisors_of_ne_zero hf))

/-- **W-1**: the coordinate ring of a good affine open is a Dedekind domain — a
localization of the Dedekind domain `C₂.CoordinateRing` away from a nonzero element
(mathlib's `IsLocalization.isDedekindDomain`).  Dedekindness of the full coordinate
ring is the standing smoothness hypothesis `[IsIntegrallyClosed C₂.CoordinateRing]`,
as in `HasseWeil/Curves/IntegralClosure.lean`. -/
theorem isDedekindDomain_away [IsIntegrallyClosed C₂.CoordinateRing] (hf : f ≠ 0) :
    IsDedekindDomain Af := by
  haveI := isDomain_away C₂ f Af hf
  exact IsLocalization.isDedekindDomain C₂.CoordinateRing
    (Submonoid.powers_le.mpr (mem_nonZeroDivisors_of_ne_zero hf)) Af

include f in
/-- **W-1**: localizing away from `f` does not change the fraction field: `Af` has
fraction field `C₂.FunctionField`
(mathlib's `IsFractionRing.isFractionRing_of_isDomain_of_isLocalization`). -/
theorem isFractionRing_away [Algebra Af C₂.FunctionField]
    [IsScalarTower C₂.CoordinateRing Af C₂.FunctionField] :
    IsFractionRing Af C₂.FunctionField :=
  IsFractionRing.isFractionRing_of_isDomain_of_isLocalization (Submonoid.powers f)
    Af C₂.FunctionField

/-! ### The concrete model `Localization.Away f`

The abstract hypotheses on `Af` above are satisfiable: for `f ≠ 0`, the concrete
localization `Localization.Away f` carries a canonical `C₂.FunctionField`-valued algebra
structure (`IsLocalization.lift`) compatible with the tower over `C₂.CoordinateRing`.
W-3 can either use these or any other realization of `IsLocalization.Away f`. -/

/-- The canonical algebra structure `Localization.Away f → C₂.FunctionField` for
`f ≠ 0` (inverting powers of `f` inside the function field via
`IsLocalization.lift`).  Not an instance: it depends on the proof `hf`.
See note [reducible non-instances]. -/
noncomputable abbrev awayAlgebra (hf : f ≠ 0) :
    Algebra (Localization.Away f) C₂.FunctionField :=
  (IsLocalization.lift (M := Submonoid.powers f) (S := Localization.Away f)
    fun y ↦ IsLocalization.map_units (M := C₂.CoordinateRing⁰) C₂.FunctionField
      ⟨y.1, Submonoid.powers_le.mpr (mem_nonZeroDivisors_of_ne_zero hf) y.2⟩).toAlgebra

/-- `awayAlgebra` is compatible with the maps from the coordinate ring, so
`Localization.Away f` satisfies all the `Af`-hypotheses of this file. -/
theorem awayAlgebra_isScalarTower (hf : f ≠ 0) :
    letI := awayAlgebra C₂ f hf
    IsScalarTower C₂.CoordinateRing (Localization.Away f) C₂.FunctionField :=
  letI := awayAlgebra C₂ f hf
  IsScalarTower.of_algebraMap_eq fun x ↦ (IsLocalization.lift_eq _ x).symm

/-! ### The extension along a separable curve-map pullback

`C₁.FunctionField / C₂.FunctionField` is a finite separable extension (abstract algebra
structure; instantiate with `φ.toAlgebra` for a curve map `φ : CurveMap C₁ C₂`).  `B` is
the integral closure of `Af` in `C₁.FunctionField`; the subalgebra instances
`Algebra Af B`, `Algebra B C₁.FunctionField`, `IsScalarTower Af B C₁.FunctionField` and
`IsIntegralClosure B Af C₁.FunctionField` are all found automatically for
`B := integralClosure Af C₁.FunctionField`. -/

section Extension

variable {C₁ : SmoothPlaneCurve F}
variable [Algebra C₂.FunctionField C₁.FunctionField]
  [FiniteDimensional C₂.FunctionField C₁.FunctionField]
  [Algebra.IsSeparable C₂.FunctionField C₁.FunctionField]
  [Algebra Af C₂.FunctionField] [IsScalarTower C₂.CoordinateRing Af C₂.FunctionField]
  [Algebra Af C₁.FunctionField] [IsScalarTower Af C₂.FunctionField C₁.FunctionField]

variable [IsIntegrallyClosed C₂.CoordinateRing]

/-- The integral closure of the good affine coordinate ring `Af` in `C₁.FunctionField`
is a Dedekind domain (Krull–Akizuki via the pure layer). -/
theorem isDedekindDomain_integralClosure (hf : f ≠ 0) :
    IsDedekindDomain (integralClosure Af C₁.FunctionField) := by
  haveI := isDedekindDomain_away C₂ f Af hf
  haveI := isFractionRing_away C₂ f Af
  exact RamificationFinite.isDedekindDomain Af C₂.FunctionField C₁.FunctionField
    (integralClosure Af C₁.FunctionField)

/-- The integral closure of `Af` in `C₁.FunctionField` is module-finite over `Af`
(separable case of Krull–Akizuki). -/
theorem module_finite_integralClosure (hf : f ≠ 0) :
    Module.Finite Af (integralClosure Af C₁.FunctionField) := by
  haveI := isDedekindDomain_away C₂ f Af hf
  haveI := isFractionRing_away C₂ f Af
  exact RamificationFinite.module_finite Af C₂.FunctionField C₁.FunctionField
    (integralClosure Af C₁.FunctionField)

omit [Algebra.IsSeparable C₂.FunctionField C₁.FunctionField] in
/-- The integral closure of `Af` in `C₁.FunctionField` has fraction field
`C₁.FunctionField`. -/
theorem isFractionRing_integralClosure (hf : f ≠ 0) :
    IsFractionRing (integralClosure Af C₁.FunctionField) C₁.FunctionField := by
  haveI := isDedekindDomain_away C₂ f Af hf
  haveI := isFractionRing_away C₂ f Af
  exact RamificationFinite.isFractionRing Af C₂.FunctionField C₁.FunctionField
    (integralClosure Af C₁.FunctionField)

/-- **The finite-ramified-locus statement for the curve extension** (W-1 + W-2): for a
good affine open of `C₂` with coordinate ring `Af` and a finite separable extension
`C₁.FunctionField / C₂.FunctionField` (e.g. the pullback of a separable curve map
`φ : C₁ → C₂`), all but finitely many primes of `Af` are unramified in the integral
closure `B` of `Af` in `C₁.FunctionField`: there is a finite set `S` of ideals of `Af`
such that every prime `P` of `B` lying over a prime `q ∉ S` has
`Ideal.ramificationIdx' q P = 1`. -/
theorem exists_finite_ramification_locus (hf : f ≠ 0) :
    ∃ S : Set (Ideal Af), S.Finite ∧
      ∀ q : Ideal Af, q ∉ S →
        ∀ P : Ideal (integralClosure Af C₁.FunctionField), P.IsPrime → P.under Af = q →
          Ideal.ramificationIdx' q P = 1 := by
  haveI := isDedekindDomain_away C₂ f Af hf
  haveI := isFractionRing_away C₂ f Af
  exact RamificationFinite.exists_finite_ramification_locus Af C₂.FunctionField
    C₁.FunctionField (integralClosure Af C₁.FunctionField)

end Extension

end HasseWeil.Curves.GoodAffineLocus
