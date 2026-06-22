/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import HasseWeil.Curves.CoordHomFinite
import HasseWeil.Curves.PicZeroPushforward
import HasseWeil.Curves.NormValuation

/-!
# The divisor pushforward of a finite curve map preserves principal divisors

For a (nonconstant) curve map `φ : C₁ → C₂` between smooth plane curves, the
**divisor pushforward** `φ_∗ : Div(C₁) → Div(C₂)` sends `Σ nᵢ (Pᵢ)` to
`Σ nᵢ (φ Pᵢ)`.  Silverman II.3.6 / II.3.7 says it carries *principal* divisors
to *principal* divisors, via the **norm–conorm identity**

  `div(N_φ f) = φ_∗(div f)`            (Silverman II.3.6)

where `N_φ f = Norm_{K(C₁)/φ*K(C₂)}(f) ∈ K(C₂)` is the field norm (already
defined as `CurveMap.pushforward`).  This is the only deep input to Silverman
III.4.8 (every isogeny is a group homomorphism, proved at the divisor/σ level in
`HasseWeil/EC/IsogenyAG/GroupHom.lean`).

## The valuation-theoretic pushforward

We realise the divisor pushforward as `Finsupp.mapDomain` along the place-image
map `P ↦ φ(P)` (affine smooth point `↦` affine smooth point, `∞ ↦ ∞`), supplied
by a coordinate-ring witness `cd : φ.CoordHom`.  This is definitionally the
point-map pushforward `pushforwardProjectiveDivisor`, so the compatibility
sub-leaf NEW-1(iii) is `rfl`; the mathematical content is concentrated in the
norm–conorm identity NEW-1(ii).

## Main definitions

* `CurveMap.pushforwardDivisorVal` — the valuation-theoretic divisor pushforward
  (= `pushforwardProjectiveDivisor`, via the place-image map).

## Main results

* `CurveMap.projectiveDivisorOf_pushforward_eq_pushforwardDivisorVal` — the
  norm–conorm identity `div(N_φ f) = φ_∗(div f)` (Silverman II.3.6).
* `EC.Isogeny.pushforward_preserves_principal` — the gap `h_pres`: the
  pushforward of a principal projective divisor is principal (Silverman II.3.7).

## References

* [Silverman, *The Arithmetic of Elliptic Curves*], II.3.6, II.3.7, III.4.8.
-/

open WeierstrassCurve

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false

namespace HasseWeil.Curves.CurveMap

variable {F : Type*} [Field F]
variable {C₁ C₂ : SmoothPlaneCurve F}
  [C₁.toAffine.IsElliptic] [C₂.toAffine.IsElliptic]

/-! ### NEW-1(i): the valuation-theoretic divisor pushforward -/

/-- The place-image map on the projective closure induced by a curve map `φ`
together with a coordinate-ring witness: an affine smooth point `P` is sent to
the affine smooth point `φ(P) = toPointMap cd P`, the place at infinity is fixed.
This is the geometric "image point" of `P` (Silverman II.2.4(c)). -/
noncomputable def placeImage (φ : CurveMap C₁ C₂) (cd : φ.CoordHom) :
    ProjectiveSmoothPoint C₁ → ProjectiveSmoothPoint C₂
  | .affine P => .affine (toPointMap cd P)
  | .infinity => .infinity

/-- The **valuation-theoretic divisor pushforward** `φ_∗ : Div(C₁) → Div(C₂)`:
`Σ nᵢ (Pᵢ) ↦ Σ nᵢ (φ Pᵢ)`, realised as `Finsupp.mapDomain` along the
place-image map `placeImage`.  Equivalently the coefficient at a place `Q` of
`C₂` is `Σ_{P ↦ Q} (coeff_P D)` (the fibre sum).  Reference: Silverman II.3.6. -/
noncomputable def pushforwardDivisorVal (φ : CurveMap C₁ C₂) (cd : φ.CoordHom) :
    ProjectiveDivisor C₁ →+ ProjectiveDivisor C₂ :=
  Finsupp.mapDomain.addMonoidHom (placeImage φ cd)

@[simp] theorem pushforwardDivisorVal_apply (φ : CurveMap C₁ C₂) (cd : φ.CoordHom)
    (D : ProjectiveDivisor C₁) :
    pushforwardDivisorVal φ cd D = Finsupp.mapDomain (placeImage φ cd) D := rfl

@[simp] theorem pushforwardDivisorVal_single (φ : CurveMap C₁ C₂) (cd : φ.CoordHom)
    (P : ProjectiveSmoothPoint C₁) (n : ℤ) :
    pushforwardDivisorVal φ cd (Finsupp.single P n) =
      Finsupp.single (placeImage φ cd P) n := by
  rw [pushforwardDivisorVal_apply, Finsupp.mapDomain_single]

/-- The valuation-theoretic pushforward preserves degree (the fibre sum
redistributes coefficients without changing their total). -/
theorem degree_pushforwardDivisorVal (φ : CurveMap C₁ C₂) (cd : φ.CoordHom)
    (D : ProjectiveDivisor C₁) :
    (pushforwardDivisorVal φ cd D).degree = D.degree := by
  rw [pushforwardDivisorVal_apply]
  unfold ProjectiveDivisor.degree
  rw [Finsupp.sum_mapDomain_index (h := fun _ n ↦ n) (fun _ ↦ rfl) (fun _ _ _ ↦ rfl)]

/-! ### NEW-1(ii): the norm–conorm identity `div(N_φ f) = φ_∗(div f)`

The mathematical content is the per-place identity (Silverman II.3.6)

  `ord_Q(N_φ u) = Σ_{P ↦ Q} f_{P/Q}·ord_P(u)`,

with residue (inertia) degrees `f_{P/Q} = 1` over `[IsAlgClosed F]`.  We build it
by generalising the `F[X] → F[C]` machinery of `NormValuation.lean` to the
coordinate-ring extension `F[C₂] → F[C₁]` supplied by a `CoordHom`.  The generic
ideal/localisation lemmas (`count_preservation_localization`,
`count_finset_prod_factors`, `map_eq_localRing_max_pow_count`, …) are reused
verbatim; the curve-specific inputs are `inertiaDeg = 1`, `relNorm m_P = m_{φP}`,
and the fibre bijection `maximalIdealAt_toPointMap`. -/

section NormConorm

variable [IsAlgClosed F]
  [IsDedekindDomain C₁.CoordinateRing] [IsDedekindDomain C₂.CoordinateRing]
  [IsIntegrallyClosed C₁.CoordinateRing] [IsIntegrallyClosed C₂.CoordinateRing]
  (φ : CurveMap C₁ C₂) (cd : φ.CoordHom)

/-- The coordinate-ring comorphism `cd.toAlgHom : F[C₂] → F[C₁]` is injective:
its composite with `algebraMap F[C₁] F(C₁)` is `φ.pullback ∘ algebraMap F[C₂] F(C₂)`
(by `cd.compat`), a composite of injective maps. -/
theorem coordHom_injective : Function.Injective cd.toAlgHom := by
  intro a b hab
  apply IsFractionRing.injective C₂.CoordinateRing C₂.FunctionField
  apply φ.pullback_injective
  rw [cd.compat, cd.compat, hab]

/-- `F[C₁]` is torsion-free as an `F[C₂]`-module via `cd` (the comorphism is
injective into a domain). -/
theorem isTorsionFree_coordHom :
    @Module.IsTorsionFree C₂.CoordinateRing C₁.CoordinateRing _ _ cd.toAlgebra.toModule := by
  letI : Algebra C₂.CoordinateRing C₁.CoordinateRing := cd.toAlgebra
  haveI : FaithfulSMul C₂.CoordinateRing C₁.CoordinateRing :=
    (faithfulSMul_iff_algebraMap_injective C₂.CoordinateRing C₁.CoordinateRing).mpr
      (CurveMap.coordHom_injective φ cd)
  infer_instance

/-- **Residue-field scalar tower at a smooth point**: `F → F[C₂]/m_{φP} → F[C₁]/m_P`
is an `IsScalarTower`.  Both `F`-algebra structures factor through the residue map
`F[C₂]/m_{φP} → F[C₁]/m_P` because the comorphism `cd : F[C₂] → F[C₁]` is an
`F`-algebra hom, so `algebraMap F (F[C₁]/m_P)` equals the composite, which is exactly
`IsScalarTower.of_algebraMap_eq`. -/
private theorem isScalarTower_residueField_maximalIdealAt (P : C₁.SmoothPoint) :
    letI : Algebra C₂.CoordinateRing C₁.CoordinateRing := cd.toAlgebra
    haveI : (C₁.maximalIdealAt P).LiesOver (C₂.maximalIdealAt (toPointMap cd P)) :=
      ⟨maximalIdealAt_toPointMap cd P⟩
    IsScalarTower F (C₂.CoordinateRing ⧸ C₂.maximalIdealAt (toPointMap cd P))
      (C₁.CoordinateRing ⧸ C₁.maximalIdealAt P) := by
  letI : Algebra C₂.CoordinateRing C₁.CoordinateRing := cd.toAlgebra
  haveI : (C₁.maximalIdealAt P).LiesOver (C₂.maximalIdealAt (toPointMap cd P)) :=
    ⟨maximalIdealAt_toPointMap cd P⟩
  set Q := toPointMap cd P with hQ
  refine IsScalarTower.of_algebraMap_eq fun c ↦ ?_
  have hlhs : (algebraMap F (C₁.CoordinateRing ⧸ C₁.maximalIdealAt P)) c =
      Ideal.Quotient.mk (C₁.maximalIdealAt P) (algebraMap F C₁.CoordinateRing c) :=
    IsScalarTower.algebraMap_apply F C₁.CoordinateRing
      (C₁.CoordinateRing ⧸ C₁.maximalIdealAt P) c
  have hrhs : (algebraMap (C₂.CoordinateRing ⧸ C₂.maximalIdealAt Q)
        (C₁.CoordinateRing ⧸ C₁.maximalIdealAt P))
        ((algebraMap F (C₂.CoordinateRing ⧸ C₂.maximalIdealAt Q)) c) =
      Ideal.Quotient.mk (C₁.maximalIdealAt P)
        (algebraMap C₂.CoordinateRing C₁.CoordinateRing (algebraMap F C₂.CoordinateRing c)) := by
    rw [IsScalarTower.algebraMap_apply F C₂.CoordinateRing
      (C₂.CoordinateRing ⧸ C₂.maximalIdealAt Q) c]
    rfl
  rw [hlhs, hrhs, ← IsScalarTower.algebraMap_apply F C₂.CoordinateRing C₁.CoordinateRing c]

/-- **Residue degree `≤ 1` at a smooth point**: the residue extension
`F[C₂]/m_{φP} → F[C₁]/m_P` has `F[C₂]/m_{φP}`-rank `≤ 1`.  Over `[IsAlgClosed F]` the
map `algebraMap F (F[C₁]/m_P)` is surjective (`algebraMap_bijective_quotient_of_maximal`),
so every `w` is `(algebraMap F _ c) • 1`; rewriting that scalar action through the
residue-field scalar tower exhibits `w` as a `(F[C₂]/m_{φP})`-multiple of `1`, whence
`finrank_le_one`. -/
private theorem finrank_residueField_maximalIdealAt_le_one (P : C₁.SmoothPoint) :
    letI : Algebra C₂.CoordinateRing C₁.CoordinateRing := cd.toAlgebra
    haveI : (C₁.maximalIdealAt P).LiesOver (C₂.maximalIdealAt (toPointMap cd P)) :=
      ⟨maximalIdealAt_toPointMap cd P⟩
    Module.finrank (C₂.CoordinateRing ⧸ C₂.maximalIdealAt (toPointMap cd P))
      (C₁.CoordinateRing ⧸ C₁.maximalIdealAt P) ≤ 1 := by
  letI : Algebra C₂.CoordinateRing C₁.CoordinateRing := cd.toAlgebra
  haveI : (C₁.maximalIdealAt P).LiesOver (C₂.maximalIdealAt (toPointMap cd P)) :=
    ⟨maximalIdealAt_toPointMap cd P⟩
  set Q := toPointMap cd P with hQ
  haveI hQmax : (C₂.maximalIdealAt Q).IsMaximal := C₂.maximalIdealAt_isMaximal Q
  haveI hPmax : (C₁.maximalIdealAt P).IsMaximal := C₁.maximalIdealAt_isMaximal P
  haveI : Field (C₂.CoordinateRing ⧸ C₂.maximalIdealAt Q) := Ideal.Quotient.field _
  haveI : Field (C₁.CoordinateRing ⧸ C₁.maximalIdealAt P) := Ideal.Quotient.field _
  haveI htower := isScalarTower_residueField_maximalIdealAt φ cd P
  have hbijSP := C₁.algebraMap_bijective_quotient_of_maximal hPmax
  refine finrank_le_one (1 : C₁.CoordinateRing ⧸ C₁.maximalIdealAt P) fun w ↦ ?_
  obtain ⟨c, hc⟩ := hbijSP.2 w
  refine ⟨algebraMap F (C₂.CoordinateRing ⧸ C₂.maximalIdealAt Q) c, ?_⟩
  have key : (algebraMap F (C₂.CoordinateRing ⧸ C₂.maximalIdealAt Q) c) •
      (1 : C₁.CoordinateRing ⧸ C₁.maximalIdealAt P) =
      algebraMap F (C₁.CoordinateRing ⧸ C₁.maximalIdealAt P) c := by
    rw [Algebra.smul_def]
    rw [show (algebraMap (C₂.CoordinateRing ⧸ C₂.maximalIdealAt Q)
        (C₁.CoordinateRing ⧸ C₁.maximalIdealAt P))
        ((algebraMap F (C₂.CoordinateRing ⧸ C₂.maximalIdealAt Q)) c) *
        (1 : C₁.CoordinateRing ⧸ C₁.maximalIdealAt P) =
        (algebraMap (C₂.CoordinateRing ⧸ C₂.maximalIdealAt Q)
        (C₁.CoordinateRing ⧸ C₁.maximalIdealAt P))
        ((algebraMap F (C₂.CoordinateRing ⧸ C₂.maximalIdealAt Q)) c) from mul_one _]
    rw [← IsScalarTower.algebraMap_apply F (C₂.CoordinateRing ⧸ C₂.maximalIdealAt Q)
        (C₁.CoordinateRing ⧸ C₁.maximalIdealAt P) c]
  rw [key]; exact hc

/-- **Inertia degree 1** for the coordinate-ring extension at a smooth point.
Over `[IsAlgClosed F]` both residue fields `F[C₁]/m_P` and `F[C₂]/m_{φP}` are
`F`, so the residue extension `F[C₂]/m_{φP} → F[C₁]/m_P` has `F`-rank 1. -/
theorem inertiaDeg_maximalIdealAt_toPointMap (P : C₁.SmoothPoint) :
    letI : Algebra C₂.CoordinateRing C₁.CoordinateRing := cd.toAlgebra
    haveI : (C₁.maximalIdealAt P).LiesOver (C₂.maximalIdealAt (toPointMap cd P)) :=
      ⟨(maximalIdealAt_toPointMap cd P)⟩
    Ideal.inertiaDeg (C₂.maximalIdealAt (toPointMap cd P)) (C₁.maximalIdealAt P) = 1 := by
  letI : Algebra C₂.CoordinateRing C₁.CoordinateRing := cd.toAlgebra
  haveI hLies : (C₁.maximalIdealAt P).LiesOver (C₂.maximalIdealAt (toPointMap cd P)) :=
    ⟨maximalIdealAt_toPointMap cd P⟩
  set Q := toPointMap cd P with hQ
  haveI hPmax : (C₁.maximalIdealAt P).IsMaximal := C₁.maximalIdealAt_isMaximal P
  rw [Ideal.inertiaDeg_algebraMap]
  -- The residue field `F[C₁]/m_P` is `F` (alg-closed), hence nontrivial.
  haveI : Field (C₁.CoordinateRing ⧸ C₁.maximalIdealAt P) := Ideal.Quotient.field _
  haveI : Nontrivial (C₁.CoordinateRing ⧸ C₁.maximalIdealAt P) :=
    (Ideal.Quotient.nontrivial_iff).mpr hPmax.ne_top
  -- Squeeze the residue rank between `1` (`finrank_pos`) and `1` (alg-closed surjectivity).
  have hSP : Module.finrank F (C₁.CoordinateRing ⧸ C₁.maximalIdealAt P) = 1 :=
    C₁.finrank_quotientMaximalIdealAt P
  have h_le : Module.finrank (C₂.CoordinateRing ⧸ C₂.maximalIdealAt Q)
      (C₁.CoordinateRing ⧸ C₁.maximalIdealAt P) ≤ 1 :=
    finrank_residueField_maximalIdealAt_le_one φ cd P
  haveI : Module.Finite F (C₁.CoordinateRing ⧸ C₁.maximalIdealAt P) :=
    Module.finite_of_finrank_pos (by rw [hSP]; norm_num)
  haveI : Module.Finite (C₂.CoordinateRing ⧸ C₂.maximalIdealAt Q)
      (C₁.CoordinateRing ⧸ C₁.maximalIdealAt P) :=
    Module.Finite.of_restrictScalars_finite F _ _
  have h_ge : 1 ≤ Module.finrank (C₂.CoordinateRing ⧸ C₂.maximalIdealAt Q)
      (C₁.CoordinateRing ⧸ C₁.maximalIdealAt P) := Module.finrank_pos
  omega

/-- The maximal ideal `m_P` of `F[C₁]` lies over `m_{φP}` of `F[C₂]`.  This is the
scheme-theoretic image-point relation `m_{φP} = (cd)⁻¹(m_P)` (Silverman II.2.4(c)),
packaged as a `LiesOver` instance for the `cd`-induced algebra. -/
theorem maximalIdealAt_liesOver_toPointMap (P : C₁.SmoothPoint) :
    letI : Algebra C₂.CoordinateRing C₁.CoordinateRing := cd.toAlgebra
    (C₁.maximalIdealAt P).LiesOver (C₂.maximalIdealAt (toPointMap cd P)) :=
  letI : Algebra C₂.CoordinateRing C₁.CoordinateRing := cd.toAlgebra
  ⟨maximalIdealAt_toPointMap cd P⟩

end NormConorm

/-! ### NEW-1(ii) — structural sub-lemmas of the norm–conorm identity

The norm–conorm identity is assembled below from three sub-lemmas, each carrying its
own elaboration budget so the assembling theorem stays light:
* `relNorm_maximalIdealAt_eq` — the **`s = 1` core** `relNorm(m_R) = m_{φR}`;
* `count_relNorm_eq_sum_fiber` — the **affine count identity** matching
  `count_{m_Q}(relNorm(span{w}))` to the fibre sum `Σ_{φP=Q} count_{m_P}(span{w})`;
* `projectiveDivisorOf_pushforward_algebraMap_eq` — the **`algebraMap` case** of the
  norm–conorm identity (affine coefficients via the count identity, infinity
  coefficient forced by degree).
The `f = u/v` reduction is then a short additivity argument in the main theorem. -/

section NormConormSteps

variable [IsAlgClosed F]
  [IsDedekindDomain C₁.CoordinateRing] [IsDedekindDomain C₂.CoordinateRing]
  [IsIntegrallyClosed C₁.CoordinateRing] [IsIntegrallyClosed C₂.CoordinateRing]
  (φ : CurveMap C₁ C₂) (cd : φ.CoordHom)

set_option synthInstance.maxHeartbeats 100000 in
-- Establishing the finite extension `K(C₂) → K(C₁)` goes through the integral-closure
-- localisation instance and the `tower1` scalar-tower derivation, both of which are
-- heartbeat-heavy; hence the scoped bumps.
set_option maxHeartbeats 800000 in
include cd in
/-- `K(C₁)` is a finite extension of `φ*K(C₂)` (the fraction fields of the finite ring
extension `F[C₂] → F[C₁]` induced by `cd`).  Used for `Algebra.norm_zero` in the
`f = 0` branch of the `f = u/v` reduction. -/
theorem finiteDimensional_functionField :
    letI : Algebra C₂.FunctionField C₁.FunctionField := φ.toAlgebra
    FiniteDimensional C₂.FunctionField C₁.FunctionField := by
  have hfin : @Module.Finite C₂.CoordinateRing C₁.CoordinateRing _ _
      cd.toAlgebra.toModule := by
    exact cd.module_finite
  letI algCR : Algebra C₂.CoordinateRing C₁.CoordinateRing := cd.toAlgebra
  letI modCR : Module C₂.CoordinateRing C₁.CoordinateRing := algCR.toModule
  haveI hfin' : @Module.Finite C₂.CoordinateRing C₁.CoordinateRing _ _ modCR := hfin
  haveI hint : Algebra.IsIntegral C₂.CoordinateRing C₁.CoordinateRing :=
    Algebra.IsIntegral.of_finite C₂.CoordinateRing C₁.CoordinateRing
  haveI faith : FaithfulSMul C₂.CoordinateRing C₁.FunctionField := by
    haveI tower2 : IsScalarTower C₂.CoordinateRing C₁.CoordinateRing C₁.FunctionField :=
      inferInstance
    rw [faithfulSMul_iff_algebraMap_injective,
      IsScalarTower.algebraMap_eq C₂.CoordinateRing C₁.CoordinateRing C₁.FunctionField]
    exact (IsFractionRing.injective C₁.CoordinateRing C₁.FunctionField).comp
      (CurveMap.coordHom_injective φ cd)
  letI algFF : Algebra C₂.FunctionField C₁.FunctionField := φ.toAlgebra
  haveI tower1 : IsScalarTower C₂.CoordinateRing C₂.FunctionField C₁.FunctionField := by
    refine IsScalarTower.of_algebraMap_smul fun r x ↦ ?_
    rw [Algebra.smul_def]
    show φ.pullback ((algebraMap C₂.CoordinateRing C₂.FunctionField) r) * x = r • x
    rw [cd.compat r, ← IsScalarTower.algebraMap_smul C₁.CoordinateRing r x, ← Algebra.smul_def]
    rfl
  haveI hicl : IsIntegralClosure C₁.CoordinateRing C₂.CoordinateRing C₁.FunctionField :=
    IsIntegralClosure.of_isIntegrallyClosed C₁.CoordinateRing C₂.CoordinateRing _
  haveI hab : Algebra.IsAlgebraic C₂.CoordinateRing C₁.CoordinateRing :=
    Algebra.IsIntegral.isAlgebraic
  haveI halgAB : Algebra.IsAlgebraic C₂.CoordinateRing C₁.FunctionField :=
    (IsFractionRing.isAlgebraic_iff' C₂.CoordinateRing C₁.CoordinateRing C₁.FunctionField).mp hab
  haveI halgFF : Algebra.IsAlgebraic C₂.FunctionField C₁.FunctionField :=
    (IsFractionRing.comap_isAlgebraic_iff (A := C₂.CoordinateRing)
      (K := C₂.FunctionField) (C := C₁.FunctionField)).mp halgAB
  haveI hloc : IsLocalization
      (Algebra.algebraMapSubmonoid C₁.CoordinateRing (nonZeroDivisors C₂.CoordinateRing))
      C₁.FunctionField :=
    IsIntegralClosure.isLocalization C₂.CoordinateRing C₂.FunctionField C₁.FunctionField
      C₁.CoordinateRing
  exact Module.Finite.of_isLocalization C₂.CoordinateRing C₁.CoordinateRing
    (nonZeroDivisors C₂.CoordinateRing)

set_option synthInstance.maxHeartbeats 100000 in
-- The `FractionRing.liftAlgebra` / `Module.finrank` defeq here (identifying
-- `FractionRing C₂.CR` with `C₂.FunctionField`) is heartbeat-heavy, hence the bumps.
set_option maxHeartbeats 600000 in
include φ cd in
/-- **The fraction-field degree equals `φ.degree`**: the `K(C₂)`-rank of `K(C₁)`,
computed through `FractionRing.liftAlgebra C₂.CR C₁.FF`, is `φ.degree`.  The key step
identifies that lift-algebra with `φ.toAlgebra` via `IsFractionRing.lift_unique`
(both restrict to `cd` on `F[C₂]`, by `cd.compat`), after which the rank is `φ.degree`
by `rfl`.  This supplies the global balance `relNorm(m_Q·F[C₁]) = m_Q^{φ.degree}`. -/
private theorem finrank_functionField_eq_degree :
    letI algCR : Algebra C₂.CoordinateRing C₁.CoordinateRing := cd.toAlgebra
    haveI faith : FaithfulSMul C₂.CoordinateRing C₁.FunctionField :=
      (faithfulSMul_iff_algebraMap_injective C₂.CoordinateRing C₁.FunctionField).mpr
        ((IsScalarTower.algebraMap_eq C₂.CoordinateRing C₁.CoordinateRing C₁.FunctionField).symm ▸
          (IsFractionRing.injective C₁.CoordinateRing C₁.FunctionField).comp
            (CurveMap.coordHom_injective φ cd))
    @Module.finrank C₂.FunctionField C₁.FunctionField _ _
      (FractionRing.liftAlgebra C₂.CoordinateRing C₁.FunctionField).toModule = φ.degree := by
  letI algCR : Algebra C₂.CoordinateRing C₁.CoordinateRing := cd.toAlgebra
  haveI tower2 : IsScalarTower C₂.CoordinateRing C₁.CoordinateRing C₁.FunctionField :=
    inferInstance
  haveI faith : FaithfulSMul C₂.CoordinateRing C₁.FunctionField := by
    rw [faithfulSMul_iff_algebraMap_injective,
      IsScalarTower.algebraMap_eq C₂.CoordinateRing C₁.CoordinateRing C₁.FunctionField]
    exact (IsFractionRing.injective C₁.CoordinateRing C₁.FunctionField).comp
      (CurveMap.coordHom_injective φ cd)
  have halgmap :
      IsFractionRing.lift (A := C₂.CoordinateRing) (K := C₂.FunctionField)
        (FaithfulSMul.algebraMap_injective C₂.CoordinateRing C₁.FunctionField) =
      φ.pullback.toRingHom := by
    apply IsFractionRing.lift_unique
      (FaithfulSMul.algebraMap_injective C₂.CoordinateRing C₁.FunctionField)
    intro u
    show φ.pullback (algebraMap C₂.CoordinateRing C₂.FunctionField u) =
      algebraMap C₂.CoordinateRing C₁.FunctionField u
    rw [cd.compat u, IsScalarTower.algebraMap_apply C₂.CoordinateRing
      C₁.CoordinateRing C₁.FunctionField u]
    rfl
  have halg : FractionRing.liftAlgebra C₂.CoordinateRing C₁.FunctionField = φ.toAlgebra := by
    show RingHom.toAlgebra _ = RingHom.toAlgebra _
    rw [halgmap]
  rw [halg]; rfl

include φ cd in
/-- **A relative-norm exponent over a maximal ideal is positive**: if a prime `P'`
of `F[C₁]` lies over a maximal ideal `q` of `F[C₂]` and `relNorm(P') = q ^ t`, then
`1 ≤ t`.  Were `t = 0` the bound `relNorm(P') ≤ comap P' = q` would force `q = ⊤`,
contradicting maximality.  (`relNorm_le_comap` + `LiesOver`.) -/
private theorem one_le_of_relNorm_eq_pow
    {P' : Ideal C₁.CoordinateRing} {q : Ideal C₂.CoordinateRing}
    (hqmax : q.IsMaximal) (t : ℕ)
    (hlies : letI : Algebra C₂.CoordinateRing C₁.CoordinateRing := cd.toAlgebra
      P'.LiesOver q)
    (ht : letI algCR : Algebra C₂.CoordinateRing C₁.CoordinateRing := cd.toAlgebra
      letI modCR : Module C₂.CoordinateRing C₁.CoordinateRing := algCR.toModule
      haveI : @Module.Finite C₂.CoordinateRing C₁.CoordinateRing _ _ modCR :=
        cd.module_finite
      haveI : @Module.IsTorsionFree C₂.CoordinateRing C₁.CoordinateRing _ _ modCR :=
        isTorsionFree_coordHom φ cd
      Ideal.relNorm C₂.CoordinateRing P' = q ^ t) :
    1 ≤ t := by
  letI algCR : Algebra C₂.CoordinateRing C₁.CoordinateRing := cd.toAlgebra
  letI modCR : Module C₂.CoordinateRing C₁.CoordinateRing := algCR.toModule
  haveI hfin' : @Module.Finite C₂.CoordinateRing C₁.CoordinateRing _ _ modCR :=
    cd.module_finite
  haveI htf : @Module.IsTorsionFree C₂.CoordinateRing C₁.CoordinateRing _ _ modCR :=
    isTorsionFree_coordHom φ cd
  haveI : P'.LiesOver q := hlies
  rcases Nat.eq_zero_or_pos t with ht0 | ht0
  · exfalso
    have hcomap : P'.comap (algebraMap C₂.CoordinateRing C₁.CoordinateRing) = q :=
      (Ideal.LiesOver.over (p := q) (P := P')).symm
    have hbound := Ideal.relNorm_le_comap (R := C₂.CoordinateRing) P'
    rw [hcomap, ht, ht0, pow_zero, Ideal.one_eq_top, top_le_iff] at hbound
    exact hqmax.ne_top hbound
  · exact ht0

include φ cd in
/-- **Inertia degree 1 for any prime over a smooth point's maximal ideal**: every
prime `P'` of `F[C₁]` lying over `m_Q` (for a smooth point `Q` of `C₂`) has inertia
degree `1`.  Such a `P'` is itself maximal, hence `m_{P''}` for a smooth point `P''`
of `C₁` (`exists_smoothPoint_of_isMaximal`); since `φP'' ` then lies over the same
`m_Q`, this reduces to the per-point `inertiaDeg_maximalIdealAt_toPointMap`. -/
private theorem inertiaDeg_eq_one_of_liesOver_maximalIdealAt (Q : C₂.SmoothPoint)
    (P' : Ideal C₁.CoordinateRing) (hP'prime : P'.IsPrime)
    (hP'lies : letI : Algebra C₂.CoordinateRing C₁.CoordinateRing := cd.toAlgebra
      P'.LiesOver (C₂.maximalIdealAt Q)) :
    letI algCR : Algebra C₂.CoordinateRing C₁.CoordinateRing := cd.toAlgebra
    letI modCR : Module C₂.CoordinateRing C₁.CoordinateRing := algCR.toModule
    haveI : @Module.Finite C₂.CoordinateRing C₁.CoordinateRing _ _ modCR :=
      cd.module_finite
    haveI : @Module.IsTorsionFree C₂.CoordinateRing C₁.CoordinateRing _ _ modCR :=
      isTorsionFree_coordHom φ cd
    Ideal.inertiaDeg (C₂.maximalIdealAt Q) P' = 1 := by
  letI algCR : Algebra C₂.CoordinateRing C₁.CoordinateRing := cd.toAlgebra
  letI modCR : Module C₂.CoordinateRing C₁.CoordinateRing := algCR.toModule
  haveI hfin' : @Module.Finite C₂.CoordinateRing C₁.CoordinateRing _ _ modCR :=
    cd.module_finite
  haveI htf : @Module.IsTorsionFree C₂.CoordinateRing C₁.CoordinateRing _ _ modCR :=
    isTorsionFree_coordHom φ cd
  haveI hP'prime' : P'.IsPrime := hP'prime
  haveI hP'lies' : P'.LiesOver (C₂.maximalIdealAt Q) := hP'lies
  haveI hQmax : (C₂.maximalIdealAt Q).IsMaximal := C₂.maximalIdealAt_isMaximal Q
  have hQ0 : C₂.maximalIdealAt Q ≠ ⊥ := C₂.maximalIdealAt_ne_bot Q
  have hP'_ne_bot : P' ≠ ⊥ := by
    intro h
    apply hQ0
    have hh : C₂.maximalIdealAt Q = P'.under C₂.CoordinateRing := hP'lies.over
    rw [hh, h, Ideal.under_bot]
  haveI hP'max : P'.IsMaximal := Ideal.IsPrime.isMaximal hP'prime hP'_ne_bot
  obtain ⟨P'', hP''⟩ := C₁.exists_smoothPoint_of_isMaximal hP'max
  haveI hlies'' : (C₁.maximalIdealAt P'').LiesOver
      (C₂.maximalIdealAt (toPointMap cd P'')) :=
    maximalIdealAt_liesOver_toPointMap φ cd P''
  have h1 : C₂.maximalIdealAt (toPointMap cd P'') =
      (C₁.maximalIdealAt P'').under C₂.CoordinateRing := hlies''.over
  have h2 : C₂.maximalIdealAt Q = P'.under C₂.CoordinateRing := hP'lies.over
  rw [hP''] at h1
  have hpeq : C₂.maximalIdealAt (toPointMap cd P'') = C₂.maximalIdealAt Q := h1.trans h2.symm
  have hid := inertiaDeg_maximalIdealAt_toPointMap φ cd P''
  rw [← hP'', ← hpeq]
  exact hid

include φ cd in
/-- **Sum of ramification indices equals `φ.degree`**: over a smooth point `Q` of
`C₂`, `Σ_{P' / m_Q} e_{P'} = φ.degree`.  Combines the fundamental identity
`Σ e_{P'} f_{P'} = φ.degree` (`sum_ramificationIdx_mul_inertiaDeg_eq_degree`) with the
fact that every residue degree `f_{P'}` is `1`
(`inertiaDeg_eq_one_of_liesOver_maximalIdealAt`). -/
private theorem sum_ramificationIdx_eq_degree (Q : C₂.SmoothPoint)
    (hfin : @Module.Finite C₂.CoordinateRing C₁.CoordinateRing _ _ cd.toAlgebra.toModule) :
    letI algCR : Algebra C₂.CoordinateRing C₁.CoordinateRing := cd.toAlgebra
    letI modCR : Module C₂.CoordinateRing C₁.CoordinateRing := algCR.toModule
    haveI : @Module.Finite C₂.CoordinateRing C₁.CoordinateRing _ _ modCR :=
      cd.module_finite
    haveI : @Module.IsTorsionFree C₂.CoordinateRing C₁.CoordinateRing _ _ modCR :=
      isTorsionFree_coordHom φ cd
    ∑ P' ∈ IsDedekindDomain.primesOverFinset (C₂.maximalIdealAt Q) C₁.CoordinateRing,
      (C₂.maximalIdealAt Q).ramificationIdx P' = φ.degree := by
  letI algCR : Algebra C₂.CoordinateRing C₁.CoordinateRing := cd.toAlgebra
  letI modCR : Module C₂.CoordinateRing C₁.CoordinateRing := algCR.toModule
  haveI hfin' : @Module.Finite C₂.CoordinateRing C₁.CoordinateRing _ _ modCR := hfin
  haveI htf : @Module.IsTorsionFree C₂.CoordinateRing C₁.CoordinateRing _ _ modCR :=
    isTorsionFree_coordHom φ cd
  haveI hQmax : (C₂.maximalIdealAt Q).IsMaximal := C₂.maximalIdealAt_isMaximal Q
  have hQ0 : C₂.maximalIdealAt Q ≠ ⊥ := C₂.maximalIdealAt_ne_bot Q
  have hsumef := φ.sum_ramificationIdx_mul_inertiaDeg_eq_degree cd hfin hQmax hQ0
  rw [← hsumef]
  apply Finset.sum_congr rfl
  intro P' hP'
  obtain ⟨hP'prime, hP'lies⟩ :=
    (IsDedekindDomain.mem_primesOverFinset_iff (B := C₁.CoordinateRing) hQ0).mp hP'
  rw [inertiaDeg_eq_one_of_liesOver_maximalIdealAt φ cd Q P' hP'prime hP'lies, mul_one]

set_option synthInstance.maxHeartbeats 100000 in
-- Establishing the global balance reuses `finrank_functionField_eq_degree` and the
-- `FractionRing.liftAlgebra` / `Module.finrank` defeq, which is heartbeat-heavy.
set_option maxHeartbeats 600000 in
include φ cd in
/-- **The degree balance `φ.degree = Σ sfn(P')·e(P')`**: if, over a smooth point `Q`
of `C₂`, the relative norm of each prime `P' / m_Q` is the corresponding power
`relNorm(P') = m_Q ^ sfn(P')`, then `φ.degree = Σ_{P' / m_Q} sfn(P')·e_{P'}`.  Apply
`relNorm` to the prime factorisation `m_Q·F[C₁] = ∏ P'^{e_{P'}}`: the left side is
`m_Q ^ finrank = m_Q ^ φ.degree` (`relNorm_algebraMap` + `finrank_functionField_eq_degree`),
the right side `m_Q ^ Σ sfn·e`, and `m_Q` not being a unit lets us cancel the bases. -/
private theorem degree_eq_sum_relNormExp_mul_ramificationIdx (Q : C₂.SmoothPoint)
    (hfin : @Module.Finite C₂.CoordinateRing C₁.CoordinateRing _ _ cd.toAlgebra.toModule)
    (sfn : Ideal C₁.CoordinateRing → ℕ)
    (hsfn_relNorm :
      letI algCR : Algebra C₂.CoordinateRing C₁.CoordinateRing := cd.toAlgebra
      letI modCR : Module C₂.CoordinateRing C₁.CoordinateRing := algCR.toModule
      haveI : @Module.Finite C₂.CoordinateRing C₁.CoordinateRing _ _ modCR :=
        cd.module_finite
      haveI : @Module.IsTorsionFree C₂.CoordinateRing C₁.CoordinateRing _ _ modCR :=
        isTorsionFree_coordHom φ cd
      ∀ P' ∈ (C₂.maximalIdealAt Q).primesOver C₁.CoordinateRing,
        Ideal.relNorm C₂.CoordinateRing P' = C₂.maximalIdealAt Q ^ sfn P') :
    letI algCR : Algebra C₂.CoordinateRing C₁.CoordinateRing := cd.toAlgebra
    letI modCR : Module C₂.CoordinateRing C₁.CoordinateRing := algCR.toModule
    haveI : @Module.Finite C₂.CoordinateRing C₁.CoordinateRing _ _ modCR :=
      cd.module_finite
    haveI : @Module.IsTorsionFree C₂.CoordinateRing C₁.CoordinateRing _ _ modCR :=
      isTorsionFree_coordHom φ cd
    haveI : (C₂.maximalIdealAt Q).IsMaximal := C₂.maximalIdealAt_isMaximal Q
    φ.degree = ∑ P' ∈ ((C₂.maximalIdealAt Q).primesOver C₁.CoordinateRing).toFinset,
      sfn P' * (C₂.maximalIdealAt Q).ramificationIdx P' := by
  letI algCR : Algebra C₂.CoordinateRing C₁.CoordinateRing := cd.toAlgebra
  letI modCR : Module C₂.CoordinateRing C₁.CoordinateRing := algCR.toModule
  haveI hfin' : @Module.Finite C₂.CoordinateRing C₁.CoordinateRing _ _ modCR := hfin
  haveI htf : @Module.IsTorsionFree C₂.CoordinateRing C₁.CoordinateRing _ _ modCR :=
    isTorsionFree_coordHom φ cd
  haveI hQmax : (C₂.maximalIdealAt Q).IsMaximal := C₂.maximalIdealAt_isMaximal Q
  set p : Ideal C₂.CoordinateRing := C₂.maximalIdealAt Q with hp_def
  have hp0 : p ≠ ⊥ := C₂.maximalIdealAt_ne_bot Q
  have hpNotUnit : ¬ IsUnit p := by rw [Ideal.isUnit_iff]; exact hQmax.ne_top
  have hcoh : @Module.finrank C₂.FunctionField C₁.FunctionField _ _
      (FractionRing.liftAlgebra C₂.CoordinateRing C₁.FunctionField).toModule = φ.degree :=
    finrank_functionField_eq_degree φ cd
  have hfact := Ideal.map_algebraMap_eq_finsetProd_pow (R := C₁.CoordinateRing)
    (S := C₂.CoordinateRing) (p := p) hp0
  have hrel := congr_arg (Ideal.relNorm C₂.CoordinateRing) hfact
  rw [Ideal.relNorm_algebraMap C₁.CoordinateRing p, hcoh, map_prod] at hrel
  have hrhs : ∏ P' ∈ (p.primesOver C₁.CoordinateRing).toFinset,
      Ideal.relNorm C₂.CoordinateRing (P' ^ p.ramificationIdx P') =
      p ^ (∑ P' ∈ (p.primesOver C₁.CoordinateRing).toFinset, sfn P' * p.ramificationIdx P') := by
    rw [← Finset.prod_pow_eq_pow_sum]
    apply Finset.prod_congr rfl
    intro P' hP'
    have hmem : P' ∈ p.primesOver C₁.CoordinateRing := Set.mem_toFinset.mp hP'
    rw [map_pow, hsfn_relNorm P' hmem, ← pow_mul]
  rw [hrhs] at hrel
  exact (pow_inj_of_not_isUnit hpNotUnit hp0).mp hrel

include φ cd in
/-- **Ramification index positive for primes over `m_Q`**: every prime `P'` of
`F[C₁]` lying over the maximal ideal `m_Q` has `e_{P'} ≥ 1`.  The ramification index
of a prime over a nonzero ideal is nonzero in a Dedekind domain
(`ramificationIdx_ne_zero_of_liesOver`). -/
private theorem one_le_ramificationIdx_of_liesOver_maximalIdealAt (Q : C₂.SmoothPoint)
    (P' : Ideal C₁.CoordinateRing) (hP'prime : P'.IsPrime)
    (hP'lies : letI : Algebra C₂.CoordinateRing C₁.CoordinateRing := cd.toAlgebra
      P'.LiesOver (C₂.maximalIdealAt Q)) :
    letI algCR : Algebra C₂.CoordinateRing C₁.CoordinateRing := cd.toAlgebra
    letI modCR : Module C₂.CoordinateRing C₁.CoordinateRing := algCR.toModule
    haveI : @Module.Finite C₂.CoordinateRing C₁.CoordinateRing _ _ modCR :=
      cd.module_finite
    haveI : @Module.IsTorsionFree C₂.CoordinateRing C₁.CoordinateRing _ _ modCR :=
      isTorsionFree_coordHom φ cd
    1 ≤ (C₂.maximalIdealAt Q).ramificationIdx P' := by
  letI algCR : Algebra C₂.CoordinateRing C₁.CoordinateRing := cd.toAlgebra
  letI modCR : Module C₂.CoordinateRing C₁.CoordinateRing := algCR.toModule
  haveI hfin' : @Module.Finite C₂.CoordinateRing C₁.CoordinateRing _ _ modCR :=
    cd.module_finite
  haveI htf : @Module.IsTorsionFree C₂.CoordinateRing C₁.CoordinateRing _ _ modCR :=
    isTorsionFree_coordHom φ cd
  haveI : P'.IsPrime := hP'prime
  haveI : P'.LiesOver (C₂.maximalIdealAt Q) := hP'lies
  have hp0 : C₂.maximalIdealAt Q ≠ ⊥ := C₂.maximalIdealAt_ne_bot Q
  rw [Nat.one_le_iff_ne_zero]
  exact Ideal.IsDedekindDomain.ramificationIdx_ne_zero_of_liesOver P' hp0

/-- **A `ℕ`-valued sum squeeze**: if `∑ c = ∑ a·c` over a finset `s` with every
`a i ≥ 1` and every `c i ≥ 1`, then `a i₀ = 1` for each `i₀ ∈ s`.  Each summand
satisfies `c i ≤ a i · c i`, so equality of the sums forces `c i = a i · c i`
pointwise (`Finset.sum_eq_sum_iff_of_le`); cancelling the positive `c i₀` gives
`a i₀ = 1`. -/
private theorem eq_one_of_sum_eq_sum_mul {ι : Type*} (s : Finset ι) (a c : ι → ℕ)
    (hsum : ∑ i ∈ s, c i = ∑ i ∈ s, a i * c i)
    (ha : ∀ i ∈ s, 1 ≤ a i) (hc : ∀ i ∈ s, 1 ≤ c i)
    {i₀ : ι} (hi₀ : i₀ ∈ s) : a i₀ = 1 := by
  have hpointwise : ∀ i ∈ s, c i ≤ a i * c i := fun i hi ↦ by
    nlinarith [ha i hi, hc i hi]
  have heach := (Finset.sum_eq_sum_iff_of_le hpointwise).mp hsum
  have hi := heach i₀ hi₀
  nlinarith [hi, hc i₀ hi₀]

set_option synthInstance.maxHeartbeats 100000 in
-- Assembling the global balance still synthesises the cross-algebra instances and the
-- `FractionRing.liftAlgebra` / `Module.finrank` defeq (via `finrank_functionField_eq_degree`),
-- which is heartbeat-heavy, hence the scoped bumps.
set_option maxHeartbeats 600000 in
/-- **The `s = 1` core — Silverman II.3.6**: the relative norm of the maximal ideal
`m_R` of `F[C₁]` is the maximal ideal `m_{φR}` of `F[C₂]`.  Proof via the global
balance `relNorm(m_Q·F[C₁]) = m_Q^{φ.degree} = ∏ relNorm(m_{P'})^{e_{P'}}` together
with `Σ e_{P'}·f_{P'} = φ.degree` and `f_{P'} = 1`, forcing each exponent to `1`. -/
theorem relNorm_maximalIdealAt_eq
    (R : C₁.SmoothPoint) :
    letI algCR : Algebra C₂.CoordinateRing C₁.CoordinateRing := cd.toAlgebra
    letI modCR : Module C₂.CoordinateRing C₁.CoordinateRing := algCR.toModule
    haveI : @Module.Finite C₂.CoordinateRing C₁.CoordinateRing _ _ modCR :=
      cd.module_finite
    haveI : @Module.IsTorsionFree C₂.CoordinateRing C₁.CoordinateRing _ _ modCR :=
      isTorsionFree_coordHom φ cd
    Ideal.relNorm C₂.CoordinateRing (C₁.maximalIdealAt R) =
      C₂.maximalIdealAt (toPointMap cd R) := by
  classical
  have hfin : @Module.Finite C₂.CoordinateRing C₁.CoordinateRing _ _
      cd.toAlgebra.toModule := by
    exact cd.module_finite
  letI algCR : Algebra C₂.CoordinateRing C₁.CoordinateRing := cd.toAlgebra
  letI modCR : Module C₂.CoordinateRing C₁.CoordinateRing := algCR.toModule
  haveI hfin' : @Module.Finite C₂.CoordinateRing C₁.CoordinateRing _ _ modCR := hfin
  haveI htf : @Module.IsTorsionFree C₂.CoordinateRing C₁.CoordinateRing _ _ modCR :=
    isTorsionFree_coordHom φ cd
  set Q := toPointMap cd R with hQ
  haveI hLies : (C₁.maximalIdealAt R).LiesOver (C₂.maximalIdealAt Q) :=
    maximalIdealAt_liesOver_toPointMap φ cd R
  haveI hQmax : (C₂.maximalIdealAt Q).IsMaximal := C₂.maximalIdealAt_isMaximal Q
  haveI hRmax : (C₁.maximalIdealAt R).IsMaximal := C₁.maximalIdealAt_isMaximal R
  haveI hRprime : (C₁.maximalIdealAt R).IsPrime := hRmax.isPrime
  have hQ0 : C₂.maximalIdealAt Q ≠ ⊥ := C₂.maximalIdealAt_ne_bot Q
  obtain ⟨s, hs⟩ := Ideal.exists_relNorm_eq_pow_of_isPrime
    (C₁.maximalIdealAt R) (C₂.maximalIdealAt Q)
  suffices hs1 : s = 1 by rw [hs, hs1, pow_one]
  -- Lower bound: the exponent `s` is at least `1`.
  have hge1 : 1 ≤ s := one_le_of_relNorm_eq_pow φ cd hQmax s hLies hs
  set p : Ideal C₂.CoordinateRing := C₂.maximalIdealAt Q with hp_def
  -- Every residue degree over `m_Q` is `1`.
  have hinertia : ∀ P' ∈ p.primesOver C₁.CoordinateRing, Ideal.inertiaDeg p P' = 1 := by
    intro P' hP'
    obtain ⟨hP'prime, hP'lies⟩ := hP'
    exact inertiaDeg_eq_one_of_liesOver_maximalIdealAt φ cd Q P' hP'prime hP'lies
  have hp0 : p ≠ ⊥ := hQ0
  have hpNotUnit : ¬ IsUnit p := by
    rw [Ideal.isUnit_iff]; exact hQmax.ne_top
  haveI hpMax : p.IsMaximal := hQmax
  -- Each relative norm over `m_Q` is a positive power of `m_Q`.
  have hexp : ∀ P' ∈ p.primesOver C₁.CoordinateRing,
      ∃ t : ℕ, 1 ≤ t ∧ Ideal.relNorm C₂.CoordinateRing P' = p ^ t := by
    intro P' hP'
    obtain ⟨hP'prime, hP'lies⟩ := hP'
    haveI : P'.IsPrime := hP'prime
    haveI : P'.LiesOver p := hP'lies
    obtain ⟨t, ht⟩ := Ideal.exists_relNorm_eq_pow_of_isPrime P' p
    exact ⟨t, one_le_of_relNorm_eq_pow φ cd hpMax t hP'lies ht, ht⟩
  let sfn : Ideal C₁.CoordinateRing → ℕ := fun P' ↦
    if hP' : P' ∈ p.primesOver C₁.CoordinateRing then (hexp P' hP').choose else 0
  have hsfn_ge : ∀ P' ∈ p.primesOver C₁.CoordinateRing, 1 ≤ sfn P' := by
    intro P' hP'
    simp only [sfn, dif_pos hP']
    exact (hexp P' hP').choose_spec.1
  have hsfn_relNorm : ∀ P' ∈ p.primesOver C₁.CoordinateRing,
      Ideal.relNorm C₂.CoordinateRing P' = p ^ sfn P' := by
    intro P' hP'
    simp only [sfn, dif_pos hP']
    exact (hexp P' hP').choose_spec.2
  set ee : Ideal C₁.CoordinateRing → ℕ := fun P' ↦ p.ramificationIdx P'
  -- Global balance: `φ.degree = Σ sfn(P')·e_{P'}`.
  have hdeg_eq : φ.degree = ∑ P' ∈ (p.primesOver C₁.CoordinateRing).toFinset, sfn P' * ee P' :=
    degree_eq_sum_relNormExp_mul_ramificationIdx φ cd Q hfin sfn hsfn_relNorm
  -- Sum of ramification indices over `m_Q` is `φ.degree` (residue degrees are `1`).
  have hsume : ∑ P' ∈ IsDedekindDomain.primesOverFinset p C₁.CoordinateRing, ee P' = φ.degree :=
    sum_ramificationIdx_eq_degree φ cd Q hfin
  have hfinset_eq : IsDedekindDomain.primesOverFinset p C₁.CoordinateRing =
      (p.primesOver C₁.CoordinateRing).toFinset := by
    apply Finset.coe_injective
    rw [IsDedekindDomain.coe_primesOverFinset hp0, Set.coe_toFinset]
  rw [hfinset_eq] at hsume
  -- Squeeze `Σ e = Σ sfn·e` with `sfn, e ≥ 1` to force `sfn(m_R) = 1`, whence `s = 1`.
  have hee_ge : ∀ P' ∈ (p.primesOver C₁.CoordinateRing).toFinset, 1 ≤ ee P' := by
    intro P' hP'
    obtain ⟨hP'prime, hP'lies⟩ := Set.mem_toFinset.mp hP'
    exact one_le_ramificationIdx_of_liesOver_maximalIdealAt φ cd Q P' hP'prime hP'lies
  have hR_mem : C₁.maximalIdealAt R ∈ p.primesOver C₁.CoordinateRing :=
    ⟨hRprime, hLies⟩
  have hR_fs : C₁.maximalIdealAt R ∈ (p.primesOver C₁.CoordinateRing).toFinset :=
    Set.mem_toFinset.mpr hR_mem
  have hsfn_R : sfn (C₁.maximalIdealAt R) = s := by
    simp only [sfn, dif_pos hR_mem]
    have h1 := (hexp (C₁.maximalIdealAt R) hR_mem).choose_spec.2
    have h2 : p ^ (hexp (C₁.maximalIdealAt R) hR_mem).choose = p ^ s := by
      rw [← h1]; exact hs
    exact (pow_inj_of_not_isUnit hpNotUnit hp0).mp h2
  have hsfn_one : sfn (C₁.maximalIdealAt R) = 1 :=
    eq_one_of_sum_eq_sum_mul (p.primesOver C₁.CoordinateRing).toFinset sfn ee
      (by rw [hsume, ← hdeg_eq]) (fun P' hP' ↦ hsfn_ge P' (Set.mem_toFinset.mp hP')) hee_ge hR_fs
  rw [hsfn_R] at hsfn_one
  exact hsfn_one

include φ cd in
/-- **Primes over a nonzero maximal ideal are nonzero**: every prime `Q'` of `F[C₁]`
in `primesOverFinset p` (for a nonzero maximal ideal `p` of `F[C₂]`) is itself nonzero.
Were `Q' = ⊥`, its contraction `Q'.under = comap ⊥` would be `⊥` (the comorphism is
injective), forcing `p = ⊥`. -/
private theorem primesOverFinset_ne_bot {p : Ideal C₂.CoordinateRing}
    (hpMax : p.IsMaximal) (hp_ne : p ≠ ⊥) :
    letI algCR : Algebra C₂.CoordinateRing C₁.CoordinateRing := cd.toAlgebra
    ∀ Q' ∈ IsDedekindDomain.primesOverFinset p C₁.CoordinateRing, Q' ≠ ⊥ := by
  letI algCR : Algebra C₂.CoordinateRing C₁.CoordinateRing := cd.toAlgebra
  letI modCR : Module C₂.CoordinateRing C₁.CoordinateRing := algCR.toModule
  haveI hfin' : @Module.Finite C₂.CoordinateRing C₁.CoordinateRing _ _ modCR :=
    cd.module_finite
  haveI htf : @Module.IsTorsionFree C₂.CoordinateRing C₁.CoordinateRing _ _ modCR :=
    isTorsionFree_coordHom φ cd
  haveI faithCR : FaithfulSMul C₂.CoordinateRing C₁.CoordinateRing :=
    (faithfulSMul_iff_algebraMap_injective C₂.CoordinateRing C₁.CoordinateRing).mpr
      (CurveMap.coordHom_injective φ cd)
  haveI hpMax' : p.IsMaximal := hpMax
  intro Q' hQ'
  rw [IsDedekindDomain.mem_primesOverFinset_iff (B := C₁.CoordinateRing) hp_ne] at hQ'
  intro h_eq
  apply hp_ne
  have h_over : p = Q'.under C₂.CoordinateRing := hQ'.2.over
  rw [h_eq, Ideal.under, Ideal.comap_bot_of_injective _
    (FaithfulSMul.algebraMap_injective C₂.CoordinateRing C₁.CoordinateRing)] at h_over
  exact h_over

include φ cd in
/-- **A prime's relative norm is a smooth-point maximal ideal**: any maximal prime
`Q'` of `F[C₁]` arises as `m_{P'}` for a smooth point `P'` of `C₁`
(`exists_smoothPoint_of_isMaximal`), and then its relative norm is the maximal ideal
`m_{φP'}` of `F[C₂]` (the `s = 1` core `relNorm_maximalIdealAt_eq`), under which `Q'`
lies (`maximalIdealAt_liesOver_toPointMap`).  This is the common geometric input to
both branches of the per-place count split. -/
private theorem exists_smoothPoint_relNorm_maximalIdealAt_eq
    {Q' : Ideal C₁.CoordinateRing} (hQ'max : Q'.IsMaximal) :
    letI algCR : Algebra C₂.CoordinateRing C₁.CoordinateRing := cd.toAlgebra
    letI modCR : Module C₂.CoordinateRing C₁.CoordinateRing := algCR.toModule
    haveI : @Module.Finite C₂.CoordinateRing C₁.CoordinateRing _ _ modCR :=
      cd.module_finite
    haveI : @Module.IsTorsionFree C₂.CoordinateRing C₁.CoordinateRing _ _ modCR :=
      isTorsionFree_coordHom φ cd
    ∃ P' : C₁.SmoothPoint, C₁.maximalIdealAt P' = Q' ∧
      Ideal.relNorm C₂.CoordinateRing Q' = C₂.maximalIdealAt (toPointMap cd P') ∧
      Q'.LiesOver (C₂.maximalIdealAt (toPointMap cd P')) := by
  letI algCR : Algebra C₂.CoordinateRing C₁.CoordinateRing := cd.toAlgebra
  letI modCR : Module C₂.CoordinateRing C₁.CoordinateRing := algCR.toModule
  haveI hfin' : @Module.Finite C₂.CoordinateRing C₁.CoordinateRing _ _ modCR :=
    cd.module_finite
  haveI htf : @Module.IsTorsionFree C₂.CoordinateRing C₁.CoordinateRing _ _ modCR :=
    isTorsionFree_coordHom φ cd
  haveI hQ'max' : Q'.IsMaximal := hQ'max
  obtain ⟨P', hP'⟩ := C₁.exists_smoothPoint_of_isMaximal hQ'max
  haveI hlies' : (C₁.maximalIdealAt P').LiesOver
      (C₂.maximalIdealAt (toPointMap cd P')) :=
    maximalIdealAt_liesOver_toPointMap φ cd P'
  refine ⟨P', hP', ?_, hP' ▸ hlies'⟩
  rw [← hP', relNorm_maximalIdealAt_eq φ cd P']

include φ cd in
/-- **Count of `relNorm(Q')^k` at `m_Q`, the matching prime**: if a maximal prime `Q'`
of `F[C₁]` lies over the smooth-point maximal ideal `p = m_Q` of `F[C₂]`, then
`count_{m_Q}((relNorm Q')^k) = k`.  Here `relNorm Q' = m_{φP'} = p` (because both `p`
and `m_{φP'}` are the contraction of `Q'`, by uniqueness of `LiesOver`), and
`count_p(p^k) = k`. -/
private theorem count_maximalIdealAt_relNorm_pow_self (Q : C₂.SmoothPoint)
    {Q' : Ideal C₁.CoordinateRing} (hQ'max : Q'.IsMaximal)
    (hQ'lies : letI : Algebra C₂.CoordinateRing C₁.CoordinateRing := cd.toAlgebra
      Q'.LiesOver (C₂.maximalIdealAt Q)) (k : ℕ) :
    letI algCR : Algebra C₂.CoordinateRing C₁.CoordinateRing := cd.toAlgebra
    letI modCR : Module C₂.CoordinateRing C₁.CoordinateRing := algCR.toModule
    haveI : @Module.Finite C₂.CoordinateRing C₁.CoordinateRing _ _ modCR :=
      cd.module_finite
    haveI : @Module.IsTorsionFree C₂.CoordinateRing C₁.CoordinateRing _ _ modCR :=
      isTorsionFree_coordHom φ cd
    (Associates.mk (C₂.maximalIdealAt Q)).count
        (Associates.mk ((Ideal.relNorm C₂.CoordinateRing Q') ^ k)).factors = k := by
  letI algCR : Algebra C₂.CoordinateRing C₁.CoordinateRing := cd.toAlgebra
  letI modCR : Module C₂.CoordinateRing C₁.CoordinateRing := algCR.toModule
  haveI hfin' : @Module.Finite C₂.CoordinateRing C₁.CoordinateRing _ _ modCR :=
    cd.module_finite
  haveI htf : @Module.IsTorsionFree C₂.CoordinateRing C₁.CoordinateRing _ _ modCR :=
    isTorsionFree_coordHom φ cd
  haveI hQ'lies' : Q'.LiesOver (C₂.maximalIdealAt Q) := hQ'lies
  set p : Ideal C₂.CoordinateRing := C₂.maximalIdealAt Q with hp_def
  haveI hpMax : p.IsMaximal := C₂.maximalIdealAt_isMaximal Q
  have hp_ne : p ≠ ⊥ := C₂.maximalIdealAt_ne_bot Q
  have h_vp_irr : Irreducible (Associates.mk p) :=
    (⟨p, hpMax.isPrime, hp_ne⟩ :
      IsDedekindDomain.HeightOneSpectrum C₂.CoordinateRing).associates_irreducible
  obtain ⟨P', _, hrel, hlies'⟩ := exists_smoothPoint_relNorm_maximalIdealAt_eq φ cd hQ'max
  -- `m_{φP'} = p`: both are the contraction of `Q'` (uniqueness of `LiesOver`).
  have hpeq : C₂.maximalIdealAt (toPointMap cd P') = p := by
    have h1 : C₂.maximalIdealAt (toPointMap cd P') = Q'.under C₂.CoordinateRing := hlies'.over
    have h2 : p = Q'.under C₂.CoordinateRing := hQ'lies'.over
    exact h1.trans h2.symm
  rw [hrel, hpeq, Associates.mk_pow,
    Associates.count_pow (by rw [Associates.mk_ne_zero]; exact hp_ne) h_vp_irr,
    Associates.count_self h_vp_irr, mul_one]

include φ cd in
/-- **Count of `relNorm(Q')^k` at `m_Q`, a non-matching prime**: if a maximal prime
`Q'` of `F[C₁]` does *not* lie over `p = m_Q`, then `count_{m_Q}((relNorm Q')^k) = 0`.
Here `relNorm Q' = m_{φP'}` for some smooth point `P'`, and `m_{φP'} ≠ p` (else `Q'`
would lie over `p`); distinct maximal ideals have `count = 0`. -/
private theorem count_maximalIdealAt_relNorm_pow_of_not_liesOver (Q : C₂.SmoothPoint)
    {Q' : Ideal C₁.CoordinateRing} (hQ'max : Q'.IsMaximal)
    (hQ'not : ¬ letI : Algebra C₂.CoordinateRing C₁.CoordinateRing := cd.toAlgebra
      Q'.LiesOver (C₂.maximalIdealAt Q)) (k : ℕ) :
    letI algCR : Algebra C₂.CoordinateRing C₁.CoordinateRing := cd.toAlgebra
    letI modCR : Module C₂.CoordinateRing C₁.CoordinateRing := algCR.toModule
    haveI : @Module.Finite C₂.CoordinateRing C₁.CoordinateRing _ _ modCR :=
      cd.module_finite
    haveI : @Module.IsTorsionFree C₂.CoordinateRing C₁.CoordinateRing _ _ modCR :=
      isTorsionFree_coordHom φ cd
    (Associates.mk (C₂.maximalIdealAt Q)).count
        (Associates.mk ((Ideal.relNorm C₂.CoordinateRing Q') ^ k)).factors = 0 := by
  letI algCR : Algebra C₂.CoordinateRing C₁.CoordinateRing := cd.toAlgebra
  letI modCR : Module C₂.CoordinateRing C₁.CoordinateRing := algCR.toModule
  haveI hfin' : @Module.Finite C₂.CoordinateRing C₁.CoordinateRing _ _ modCR :=
    cd.module_finite
  haveI htf : @Module.IsTorsionFree C₂.CoordinateRing C₁.CoordinateRing _ _ modCR :=
    isTorsionFree_coordHom φ cd
  set p : Ideal C₂.CoordinateRing := C₂.maximalIdealAt Q with hp_def
  haveI hpMax : p.IsMaximal := C₂.maximalIdealAt_isMaximal Q
  have hp_ne : p ≠ ⊥ := C₂.maximalIdealAt_ne_bot Q
  have h_vp_irr : Irreducible (Associates.mk p) :=
    (⟨p, hpMax.isPrime, hp_ne⟩ :
      IsDedekindDomain.HeightOneSpectrum C₂.CoordinateRing).associates_irreducible
  obtain ⟨_, _, hrel, hlies'⟩ := exists_smoothPoint_relNorm_maximalIdealAt_eq φ cd hQ'max
  -- `m_{φP'} ≠ p`, else `Q'` would lie over `p` (contradicting `hQ'not`).
  have hPne : Ideal.relNorm C₂.CoordinateRing Q' ≠ p := by
    rw [hrel]
    intro hpe
    exact hQ'not (hpe ▸ hlies')
  haveI hP'max2 : (Ideal.relNorm C₂.CoordinateRing Q').IsMaximal := hrel ▸ C₂.maximalIdealAt_isMaximal _
  have hP'_ne_bot2 : Ideal.relNorm C₂.CoordinateRing Q' ≠ ⊥ := hrel ▸ C₂.maximalIdealAt_ne_bot _
  have h_vP'_irr : Irreducible (Associates.mk (Ideal.relNorm C₂.CoordinateRing Q')) :=
    (⟨_, hP'max2.isPrime, hP'_ne_bot2⟩ :
      IsDedekindDomain.HeightOneSpectrum C₂.CoordinateRing).associates_irreducible
  have h_vp_ne_vP' :
      (Associates.mk p) ≠ (Associates.mk (Ideal.relNorm C₂.CoordinateRing Q')) := by
    intro h_eq
    apply hPne
    rw [Associates.mk_eq_mk_iff_associated] at h_eq
    exact (associated_iff_eq.mp h_eq).symm
  rw [Associates.mk_pow,
    Associates.count_pow (by rw [Associates.mk_ne_zero]; exact hP'_ne_bot2) h_vp_irr,
    Associates.count_eq_zero_of_ne h_vp_irr h_vP'_irr h_vp_ne_vP', Nat.mul_zero]

include φ cd in
/-- **Per-term count split** of the `relNorm`-factorisation product: the count of
`m_Q` in `(relNorm Q')^k` is `k` when `Q'` lies over `m_Q` and `0` otherwise.  This is
the `if-then-else` body that, summed over the support finset, collapses the relative
norm of the factorisation to the fibre sum.  Combines the matching / non-matching
branches `count_maximalIdealAt_relNorm_pow_self` and
`count_maximalIdealAt_relNorm_pow_of_not_liesOver`. -/
private theorem count_factors_relNorm_pow_eq_ite (Q : C₂.SmoothPoint)
    {Q' : Ideal C₁.CoordinateRing} (hQ'max : Q'.IsMaximal) (k : ℕ) :
    letI algCR : Algebra C₂.CoordinateRing C₁.CoordinateRing := cd.toAlgebra
    letI modCR : Module C₂.CoordinateRing C₁.CoordinateRing := algCR.toModule
    haveI : @Module.Finite C₂.CoordinateRing C₁.CoordinateRing _ _ modCR :=
      cd.module_finite
    haveI : @Module.IsTorsionFree C₂.CoordinateRing C₁.CoordinateRing _ _ modCR :=
      isTorsionFree_coordHom φ cd
    (Associates.mk (C₂.maximalIdealAt Q)).count
        (Associates.mk ((Ideal.relNorm C₂.CoordinateRing Q') ^ k)).factors =
      if Q' ∈ IsDedekindDomain.primesOverFinset (C₂.maximalIdealAt Q) C₁.CoordinateRing
        then k else 0 := by
  letI algCR : Algebra C₂.CoordinateRing C₁.CoordinateRing := cd.toAlgebra
  letI modCR : Module C₂.CoordinateRing C₁.CoordinateRing := algCR.toModule
  haveI hfin' : @Module.Finite C₂.CoordinateRing C₁.CoordinateRing _ _ modCR :=
    cd.module_finite
  haveI htf : @Module.IsTorsionFree C₂.CoordinateRing C₁.CoordinateRing _ _ modCR :=
    isTorsionFree_coordHom φ cd
  have hp_ne : C₂.maximalIdealAt Q ≠ ⊥ := C₂.maximalIdealAt_ne_bot Q
  haveI hpMax : (C₂.maximalIdealAt Q).IsMaximal := C₂.maximalIdealAt_isMaximal Q
  by_cases h_over : Q' ∈ IsDedekindDomain.primesOverFinset (C₂.maximalIdealAt Q) C₁.CoordinateRing
  · rw [if_pos h_over]
    haveI hQ'lies : Q'.LiesOver (C₂.maximalIdealAt Q) :=
      ((IsDedekindDomain.mem_primesOverFinset_iff (B := C₁.CoordinateRing) hp_ne).mp h_over).2
    exact count_maximalIdealAt_relNorm_pow_self φ cd Q hQ'max hQ'lies k
  · rw [if_neg h_over]
    refine count_maximalIdealAt_relNorm_pow_of_not_liesOver φ cd Q hQ'max (fun hlies ↦ ?_) k
    exact h_over ((IsDedekindDomain.mem_primesOverFinset_iff
      (B := C₁.CoordinateRing) hp_ne).mpr ⟨hQ'max.isPrime, hlies⟩)

/-- **A height-one support sum re-indexes onto a target ideal finset**: summing a term
`g Q'.asIdeal` over the height-one primes of `F[C₁]` in a finset `S` whose ideal lies
in a target finset `T`, equals `∑_{I ∈ T} g I`, provided a repackaging `toHOS : T →
HeightOneSpectrum` with `(toHOS I).asIdeal = I` landing back in `S`.  The bijection
sends `Q' ↦ Q'.asIdeal` with inverse `toHOS`.  Purely combinatorial (no algebra); used
to collapse the `relNorm`-factorisation support sum onto `primesOverFinset`. -/
private theorem sum_filter_heightOneSpectrum_eq_sum_of_asIdeal
    (S : Finset (IsDedekindDomain.HeightOneSpectrum C₁.CoordinateRing))
    (T : Finset (Ideal C₁.CoordinateRing))
    (toHOS : ∀ I ∈ T, IsDedekindDomain.HeightOneSpectrum C₁.CoordinateRing)
    (htoHOS_asIdeal : ∀ I (hI : I ∈ T), (toHOS I hI).asIdeal = I)
    (htoHOS_mem : ∀ I (hI : I ∈ T), toHOS I hI ∈ S)
    (g : Ideal C₁.CoordinateRing → ℕ) :
    ∑ Q' ∈ S.filter (fun Q' ↦ Q'.asIdeal ∈ T), g Q'.asIdeal = ∑ I ∈ T, g I := by
  refine Finset.sum_bij'
    (i := fun (Q' : IsDedekindDomain.HeightOneSpectrum C₁.CoordinateRing) _ ↦ Q'.asIdeal)
    (j := fun (I : Ideal C₁.CoordinateRing) hI ↦ toHOS I hI) ?_ ?_ ?_ ?_ ?_
  · intro Q' hQ'
    exact (Finset.mem_filter.mp hQ').2
  · intro I hI
    refine Finset.mem_filter.mpr ⟨htoHOS_mem I hI, ?_⟩
    rw [htoHOS_asIdeal I hI]
    exact hI
  · intro Q' hQ'
    apply IsDedekindDomain.HeightOneSpectrum.ext
    exact htoHOS_asIdeal Q'.asIdeal (Finset.mem_filter.mp hQ').2
  · intro I hI
    exact htoHOS_asIdeal I hI
  · intro Q' _
    rfl

include φ cd in
/-- **The associated relative-norm power is nonzero**: for a height-one prime `Q'` of
`F[C₁]` and any exponent `k`, the associate of `(relNorm Q'.asIdeal)^k` is nonzero —
the relative norm of a nonzero ideal is nonzero (`relNorm_eq_bot_iff`), and powers of a
nonzero ideal are nonzero.  Supplies the nonvanishing side-condition of
`count_finset_prod_factors`. -/
private theorem associates_relNorm_pow_ne_zero
    (Q' : IsDedekindDomain.HeightOneSpectrum C₁.CoordinateRing) (k : ℕ) :
    letI algCR : Algebra C₂.CoordinateRing C₁.CoordinateRing := cd.toAlgebra
    letI modCR : Module C₂.CoordinateRing C₁.CoordinateRing := algCR.toModule
    haveI : @Module.Finite C₂.CoordinateRing C₁.CoordinateRing _ _ modCR :=
      cd.module_finite
    haveI : @Module.IsTorsionFree C₂.CoordinateRing C₁.CoordinateRing _ _ modCR :=
      isTorsionFree_coordHom φ cd
    Associates.mk ((Ideal.relNorm C₂.CoordinateRing Q'.asIdeal) ^ k) ≠ 0 := by
  letI algCR : Algebra C₂.CoordinateRing C₁.CoordinateRing := cd.toAlgebra
  letI modCR : Module C₂.CoordinateRing C₁.CoordinateRing := algCR.toModule
  haveI hfin' : @Module.Finite C₂.CoordinateRing C₁.CoordinateRing _ _ modCR :=
    cd.module_finite
  haveI htf : @Module.IsTorsionFree C₂.CoordinateRing C₁.CoordinateRing _ _ modCR :=
    isTorsionFree_coordHom φ cd
  rw [Associates.mk_ne_zero]
  apply pow_ne_zero
  rw [Ne, Ideal.zero_eq_bot, Ideal.relNorm_eq_bot_iff]
  exact Q'.ne_bot

include φ cd in
/-- **The relative norm of `span{w}` factors as a support sum of counts**: the
multiplicity of `m_Q` in `relNorm(span{w})` equals `∑_{Q' ∈ S} count_{m_Q}((relNorm
Q'.asIdeal)^(count_{Q'}(span{w})))` for any finset `S` containing the multiplicative
support of `Q' ↦ Q'.maxPowDividing(span{w})`.  Rewrite `span{w}` by its height-one
factorisation `∏ Q'.maxPowDividing`, push `relNorm` and `Associates.mk` through the
finite product (`map_prod`), and apply `count_finset_prod_factors` (each factor is
nonzero by `associates_relNorm_pow_ne_zero`).  This is the analytic backbone of the
affine count identity, isolating the product/`count` bookkeeping from the per-place
geometry. -/
private theorem count_relNorm_span_eq_sum_support (Q : C₂.SmoothPoint)
    (w : C₁.CoordinateRing) (hw : w ≠ 0)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum C₁.CoordinateRing))
    (hS_supp : Function.mulSupport
      (fun Q' : IsDedekindDomain.HeightOneSpectrum C₁.CoordinateRing ↦
        Q'.maxPowDividing (Ideal.span ({w} : Set _))) ⊆ ↑S) :
    letI algCR : Algebra C₂.CoordinateRing C₁.CoordinateRing := cd.toAlgebra
    letI modCR : Module C₂.CoordinateRing C₁.CoordinateRing := algCR.toModule
    haveI : @Module.Finite C₂.CoordinateRing C₁.CoordinateRing _ _ modCR :=
      cd.module_finite
    haveI : @Module.IsTorsionFree C₂.CoordinateRing C₁.CoordinateRing _ _ modCR :=
      isTorsionFree_coordHom φ cd
    (Associates.mk (C₂.maximalIdealAt Q)).count
        (Associates.mk (Ideal.relNorm C₂.CoordinateRing (Ideal.span ({w} : Set _)))).factors =
      ∑ Q' ∈ S, (Associates.mk (C₂.maximalIdealAt Q)).count
        (Associates.mk ((Ideal.relNorm C₂.CoordinateRing Q'.asIdeal) ^
          ((Associates.mk Q'.asIdeal).count
            (Associates.mk (Ideal.span ({w} : Set _))).factors))).factors := by
  letI algCR : Algebra C₂.CoordinateRing C₁.CoordinateRing := cd.toAlgebra
  letI modCR : Module C₂.CoordinateRing C₁.CoordinateRing := algCR.toModule
  haveI hfin' : @Module.Finite C₂.CoordinateRing C₁.CoordinateRing _ _ modCR :=
    cd.module_finite
  haveI htf : @Module.IsTorsionFree C₂.CoordinateRing C₁.CoordinateRing _ _ modCR :=
    isTorsionFree_coordHom φ cd
  set p : Ideal C₂.CoordinateRing := C₂.maximalIdealAt Q with hp_def
  haveI hpMax : p.IsMaximal := C₂.maximalIdealAt_isMaximal Q
  have hp_ne : p ≠ ⊥ := C₂.maximalIdealAt_ne_bot Q
  have h_vp_irr : Irreducible (Associates.mk p) :=
    (⟨p, hpMax.isPrime, hp_ne⟩ :
      IsDedekindDomain.HeightOneSpectrum C₂.CoordinateRing).associates_irreducible
  have hI_ne : Ideal.span ({w} : Set C₁.CoordinateRing) ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hw
  have h_finprod_eq_prod :
      (∏ᶠ Q' : IsDedekindDomain.HeightOneSpectrum C₁.CoordinateRing,
        Q'.maxPowDividing (Ideal.span ({w} : Set _))) =
      ∏ Q' ∈ S, Q'.maxPowDividing (Ideal.span ({w} : Set _)) :=
    finprod_eq_prod_of_mulSupport_subset _ hS_supp
  conv_lhs =>
    rw [← Ideal.finprod_heightOneSpectrum_factorization hI_ne, h_finprod_eq_prod,
      map_prod (Ideal.relNorm C₂.CoordinateRing)]
  simp_rw [IsDedekindDomain.HeightOneSpectrum.maxPowDividing, map_pow]
  rw [show Associates.mk (∏ Q' ∈ S, (Ideal.relNorm C₂.CoordinateRing) Q'.asIdeal ^
        (Associates.mk Q'.asIdeal).count
          (Associates.mk (Ideal.span ({w} : Set _))).factors) =
      ∏ Q' ∈ S, Associates.mk ((Ideal.relNorm C₂.CoordinateRing) Q'.asIdeal ^
        (Associates.mk Q'.asIdeal).count
          (Associates.mk (Ideal.span ({w} : Set _))).factors) from
      map_prod (Associates.mkMonoidHom (M := Ideal C₂.CoordinateRing)) _ _]
  rw [count_finset_prod_factors
    (fun Q' _ ↦ associates_relNorm_pow_ne_zero φ cd Q' _) h_vp_irr]

/-- **The affine count identity — Silverman II.3.6, per-place**: for nonzero
`w ∈ F[C₁]` and a smooth point `Q` of `C₂`, the multiplicity of `m_Q` in the
relative norm `relNorm(span{w})` equals the fibre sum `Σ_{Q' over m_Q}` of the
multiplicities of `Q'` in `span{w}`.  This matches the `mapDomain` fibre sum of
`pushforwardDivisorVal`.  Built on the `s = 1` core `relNorm_maximalIdealAt_eq`. -/
theorem count_relNorm_eq_sum_fiber :
    letI algCR : Algebra C₂.CoordinateRing C₁.CoordinateRing := cd.toAlgebra
    letI modCR : Module C₂.CoordinateRing C₁.CoordinateRing := algCR.toModule
    haveI : @Module.Finite C₂.CoordinateRing C₁.CoordinateRing _ _ modCR :=
      cd.module_finite
    haveI : @Module.IsTorsionFree C₂.CoordinateRing C₁.CoordinateRing _ _ modCR :=
      isTorsionFree_coordHom φ cd
    ∀ (w : C₁.CoordinateRing), w ≠ 0 → ∀ (Q : C₂.SmoothPoint),
      (Associates.mk (C₂.maximalIdealAt Q)).count
        (Associates.mk (Ideal.span
          {Algebra.intNorm C₂.CoordinateRing C₁.CoordinateRing w})).factors =
      ∑ Q' ∈ IsDedekindDomain.primesOverFinset (C₂.maximalIdealAt Q) C₁.CoordinateRing,
        (Associates.mk Q').count (Associates.mk (Ideal.span ({w} : Set _))).factors := by
  classical
  letI algCR : Algebra C₂.CoordinateRing C₁.CoordinateRing := cd.toAlgebra
  letI modCR : Module C₂.CoordinateRing C₁.CoordinateRing := algCR.toModule
  haveI hfin' : @Module.Finite C₂.CoordinateRing C₁.CoordinateRing _ _ modCR :=
    cd.module_finite
  haveI htf : @Module.IsTorsionFree C₂.CoordinateRing C₁.CoordinateRing _ _ modCR :=
    isTorsionFree_coordHom φ cd
  intro w hw Q
  set p : Ideal C₂.CoordinateRing := C₂.maximalIdealAt Q with hp_def
  haveI hpMax : p.IsMaximal := C₂.maximalIdealAt_isMaximal Q
  have hp_ne : p ≠ ⊥ := C₂.maximalIdealAt_ne_bot Q
  have hI_ne : Ideal.span ({w} : Set C₁.CoordinateRing) ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hw
  have h_supp := Ideal.hasFiniteMulSupport (R := C₁.CoordinateRing) hI_ne
  have h_prime_ne_bot : ∀ Q' ∈ IsDedekindDomain.primesOverFinset p C₁.CoordinateRing, Q' ≠ ⊥ :=
    primesOverFinset_ne_bot φ cd hpMax hp_ne
  -- The support finset `S`: the actual support of `span{w}` together with the (possibly
  -- non-dividing) primes over `m_Q`, so both `S`-sums below range over a common finset.
  let toHOS : ∀ Q' ∈ IsDedekindDomain.primesOverFinset p C₁.CoordinateRing,
      IsDedekindDomain.HeightOneSpectrum C₁.CoordinateRing := fun Q' hQ' ↦
    ⟨Q', ((IsDedekindDomain.mem_primesOverFinset_iff (B := C₁.CoordinateRing) hp_ne).mp hQ').1,
      h_prime_ne_bot Q' hQ'⟩
  let sH : Finset (IsDedekindDomain.HeightOneSpectrum C₁.CoordinateRing) :=
    (IsDedekindDomain.primesOverFinset p C₁.CoordinateRing).attach.image (fun ⟨Q', hQ'⟩ ↦ toHOS Q' hQ')
  set S : Finset (IsDedekindDomain.HeightOneSpectrum C₁.CoordinateRing) :=
    h_supp.toFinset ∪ sH with hS_def
  have hS_supp : Function.mulSupport
      (fun Q' : IsDedekindDomain.HeightOneSpectrum C₁.CoordinateRing ↦
        Q'.maxPowDividing (Ideal.span ({w} : Set _))) ⊆ ↑S := by
    intro Q' hQ'
    simp only [hS_def, Finset.coe_union, Set.mem_union]
    left
    exact h_supp.mem_toFinset.mpr hQ'
  -- span{intNorm w} = relNorm(span{w}); then factor the count over the support `S`.
  rw [show Ideal.span ({Algebra.intNorm C₂.CoordinateRing C₁.CoordinateRing w} : Set _) =
      Ideal.relNorm C₂.CoordinateRing (Ideal.span ({w} : Set _)) from
    (Ideal.relNorm_singleton (R := C₂.CoordinateRing) w).symm,
    count_relNorm_span_eq_sum_support φ cd Q w hw S hS_supp]
  -- Each term: `count_{m_Q}((relNorm Q')^k) = k` if `Q'` lies over `m_Q`, else `0`.
  have h_S_split : ∀ Q' ∈ S,
      (Associates.mk p).count
        (Associates.mk ((Ideal.relNorm C₂.CoordinateRing Q'.asIdeal) ^
          ((Associates.mk Q'.asIdeal).count
            (Associates.mk (Ideal.span ({w} : Set _))).factors))).factors =
      if Q'.asIdeal ∈ IsDedekindDomain.primesOverFinset p C₁.CoordinateRing then
        (Associates.mk Q'.asIdeal).count (Associates.mk (Ideal.span ({w} : Set _))).factors
      else 0 := fun Q' _ ↦
    count_factors_relNorm_pow_eq_ite φ cd Q
      (Ideal.IsPrime.isMaximal Q'.isPrime Q'.ne_bot) _
  rw [Finset.sum_congr rfl h_S_split, Finset.sum_ite, Finset.sum_const_zero, add_zero]
  -- Re-index the surviving terms (primes over `m_Q`) onto `primesOverFinset`.
  exact sum_filter_heightOneSpectrum_eq_sum_of_asIdeal S
    (IsDedekindDomain.primesOverFinset p C₁.CoordinateRing) toHOS
    (fun _ _ ↦ rfl)
    (fun Q'' hQ'' ↦ by
      simp only [hS_def, Finset.mem_union]
      right
      simp only [sH, Finset.mem_image, Finset.mem_attach, true_and, Subtype.exists]
      exact ⟨Q'', hQ'', rfl⟩)
    (fun Q' ↦ (Associates.mk Q').count (Associates.mk (Ideal.span ({w} : Set _))).factors)

/-- **Infinity coefficient pinned by degree**: two projective divisors on `C` with
equal degree whose coefficients agree at every affine place agree at infinity as
well.  (The difference is supported only at infinity, so its degree *is* its
infinity coefficient.)  This pins the place at infinity in `II.3.6` once the affine
coefficients are matched and both divisors have degree `0`. -/
private theorem projDivisor_infinity_coeff_eq_of_affine_eq {C : SmoothPlaneCurve F}
    (D₁ D₂ : ProjectiveDivisor C) (hdeg : D₁.degree = D₂.degree)
    (haff : ∀ Q : C.SmoothPoint,
      D₁ (ProjectiveSmoothPoint.affine Q) = D₂ (ProjectiveSmoothPoint.affine Q)) :
    D₁ ProjectiveSmoothPoint.infinity = D₂ ProjectiveSmoothPoint.infinity := by
  classical
  set E : ProjectiveDivisor C := D₁ - D₂ with hE_def
  have hE_aff : ∀ Q : C.SmoothPoint, E (ProjectiveSmoothPoint.affine Q) = 0 := by
    intro Q
    rw [hE_def, Finsupp.sub_apply, haff Q, sub_self]
  have hE_supp : E.support ⊆ {ProjectiveSmoothPoint.infinity} := by
    intro x hx
    rw [Finsupp.mem_support_iff] at hx
    cases x with
    | affine Q => exact absurd (hE_aff Q) hx
    | infinity => exact Finset.mem_singleton_self _
  have hE_single : E = Finsupp.single ProjectiveSmoothPoint.infinity
      (E ProjectiveSmoothPoint.infinity) :=
    (Finsupp.support_subset_singleton.mp hE_supp)
  have hE_deg : E.degree = 0 := by
    rw [hE_def, ProjectiveDivisor.degree_sub, hdeg, sub_self]
  have hEinf : E ProjectiveSmoothPoint.infinity = 0 := by
    have : E.degree = E ProjectiveSmoothPoint.infinity := by
      conv_lhs => rw [hE_single]
      unfold ProjectiveDivisor.degree
      rw [Finsupp.sum_single_index rfl]
    rw [this] at hE_deg
    exact hE_deg
  have : D₁ ProjectiveSmoothPoint.infinity - D₂ ProjectiveSmoothPoint.infinity = 0 := by
    rw [← Finsupp.sub_apply]; exact hEinf
  linarith [this]

set_option synthInstance.maxHeartbeats 100000 in
-- Synthesising the cross-algebra `Algebra C₂.CR C₁.FF` for the scalar towers (needed
-- by `Algebra.algebraMap_intNorm`) is heartbeat-heavy, hence the scoped bumps.
set_option maxHeartbeats 400000 in
include φ cd in
/-- **Conorm of an `algebraMap` is the `algebraMap` of the integral norm**: for
`w ∈ F[C₁]`, the pushforward `φ_∗(algebraMap w)` equals `algebraMap (N_{F[C₂]} w)`,
the image in `K(C₂)` of the integral norm of `w` for the finite ring extension
`F[C₂] → F[C₁]` induced by `cd`.  This is the algebraic reformulation underlying
the `algebraMap` case of `II.3.6`. -/
private theorem pushforward_algebraMap_eq_algebraMap_intNorm (w : C₁.CoordinateRing) :
    letI algCR : Algebra C₂.CoordinateRing C₁.CoordinateRing := cd.toAlgebra
    letI modCR : Module C₂.CoordinateRing C₁.CoordinateRing := algCR.toModule
    haveI : @Module.Finite C₂.CoordinateRing C₁.CoordinateRing _ _ modCR :=
      cd.module_finite
    haveI : @Module.IsTorsionFree C₂.CoordinateRing C₁.CoordinateRing _ _ modCR :=
      isTorsionFree_coordHom φ cd
    φ.pushforward (algebraMap C₁.CoordinateRing C₁.FunctionField w) =
      algebraMap C₂.CoordinateRing C₂.FunctionField
        (Algebra.intNorm C₂.CoordinateRing C₁.CoordinateRing w) := by
  classical
  letI algCR : Algebra C₂.CoordinateRing C₁.CoordinateRing := cd.toAlgebra
  letI modCR : Module C₂.CoordinateRing C₁.CoordinateRing := algCR.toModule
  haveI hfin' : @Module.Finite C₂.CoordinateRing C₁.CoordinateRing _ _ modCR :=
    cd.module_finite
  haveI htf : @Module.IsTorsionFree C₂.CoordinateRing C₁.CoordinateRing _ _ modCR :=
    isTorsionFree_coordHom φ cd
  haveI hint : Algebra.IsIntegral C₂.CoordinateRing C₁.CoordinateRing :=
    Algebra.IsIntegral.of_finite C₂.CoordinateRing C₁.CoordinateRing
  haveI tower2 : IsScalarTower C₂.CoordinateRing C₁.CoordinateRing C₁.FunctionField :=
    inferInstance
  haveI faith : FaithfulSMul C₂.CoordinateRing C₁.FunctionField := by
    rw [faithfulSMul_iff_algebraMap_injective,
      IsScalarTower.algebraMap_eq C₂.CoordinateRing C₁.CoordinateRing C₁.FunctionField]
    exact (IsFractionRing.injective C₁.CoordinateRing C₁.FunctionField).comp
      (CurveMap.coordHom_injective φ cd)
  letI algFF : Algebra C₂.FunctionField C₁.FunctionField := φ.toAlgebra
  haveI tower1 : IsScalarTower C₂.CoordinateRing C₂.FunctionField C₁.FunctionField := by
    refine IsScalarTower.of_algebraMap_smul fun r x ↦ ?_
    rw [Algebra.smul_def]
    show φ.pullback ((algebraMap C₂.CoordinateRing C₂.FunctionField) r) * x = r • x
    rw [cd.compat r, ← IsScalarTower.algebraMap_smul C₁.CoordinateRing r x, ← Algebra.smul_def]
    rfl
  haveI hfd : FiniteDimensional C₂.FunctionField C₁.FunctionField :=
    finiteDimensional_functionField φ cd
  rw [Algebra.algebraMap_intNorm (A := C₂.CoordinateRing) (B := C₁.CoordinateRing)
    (K := C₂.FunctionField) (L := C₁.FunctionField) w]
  rfl

include φ cd in
/-- **The integral norm of a nonzero element is nonzero**: for `w ∈ F[C₁]` with
`w ≠ 0`, `N_{F[C₂]} w ≠ 0`.  Follows from
`pushforward_algebraMap_eq_algebraMap_intNorm` since `φ_∗` and `algebraMap` both
preserve nonzeroness. -/
private theorem intNorm_ne_zero_of_ne_zero (w : C₁.CoordinateRing) (hw : w ≠ 0) :
    letI algCR : Algebra C₂.CoordinateRing C₁.CoordinateRing := cd.toAlgebra
    letI modCR : Module C₂.CoordinateRing C₁.CoordinateRing := algCR.toModule
    haveI : @Module.Finite C₂.CoordinateRing C₁.CoordinateRing _ _ modCR :=
      cd.module_finite
    haveI : @Module.IsTorsionFree C₂.CoordinateRing C₁.CoordinateRing _ _ modCR :=
      isTorsionFree_coordHom φ cd
    Algebra.intNorm C₂.CoordinateRing C₁.CoordinateRing w ≠ 0 := by
  classical
  letI algCR : Algebra C₂.CoordinateRing C₁.CoordinateRing := cd.toAlgebra
  letI modCR : Module C₂.CoordinateRing C₁.CoordinateRing := algCR.toModule
  haveI hfin' : @Module.Finite C₂.CoordinateRing C₁.CoordinateRing _ _ modCR :=
    cd.module_finite
  haveI htf : @Module.IsTorsionFree C₂.CoordinateRing C₁.CoordinateRing _ _ modCR :=
    isTorsionFree_coordHom φ cd
  have hw_FF : algebraMap C₁.CoordinateRing C₁.FunctionField w ≠ 0 := by
    intro h
    exact hw ((IsFractionRing.injective C₁.CoordinateRing C₁.FunctionField)
      (h.trans (map_zero _).symm))
  have hpush_ne : φ.pushforward (algebraMap C₁.CoordinateRing C₁.FunctionField w) ≠ 0 :=
    (IsUnit.map φ.pushforward (isUnit_iff_ne_zero.mpr hw_FF)).ne_zero
  rw [pushforward_algebraMap_eq_algebraMap_intNorm φ cd w] at hpush_ne
  intro hN
  rw [hN, map_zero] at hpush_ne
  exact hpush_ne rfl

/-- **Affine coefficient of `div(algebraMap w)` as an ideal count**: for a nonzero
`w ∈ F[C₁]` and a smooth point `P'` of `C₁`, the `affine P'` coefficient of the
principal divisor `div(algebraMap w)` equals `count_{m_{P'}}(span{w})`.  Pure local
computation: `projectiveDivisorOf_apply_affine` followed by `ord_P_algebraMap_eq_count`. -/
private theorem projectiveDivisorOf_algebraMap_apply_affine_eq_count
    (w : C₁.CoordinateRing) (hw : w ≠ 0) (P' : C₁.SmoothPoint) :
    (C₁.projectiveDivisorOf (algebraMap C₁.CoordinateRing C₁.FunctionField w))
        (ProjectiveSmoothPoint.affine P') =
      ((Associates.mk (C₁.maximalIdealAt P')).count
        (Associates.mk (Ideal.span ({w} : Set _))).factors : ℤ) := by
  rw [C₁.projectiveDivisorOf_apply_affine, C₁.ord_P_algebraMap_eq_count P' hw,
    WithTop.untopD_coe]

include φ cd in
/-- **Affine pushforward coefficient as a sum over the support fibre**: for any
projective divisor `D` on `C₁` and any smooth point `Q` of `C₂`, the `affine Q`
coefficient of `φ_∗ D` is the sum of `D` over the support places mapping to `affine Q`.
Pure `Finsupp.mapDomain` bookkeeping; no algebra structure required. -/
private theorem pushforwardDivisorVal_apply_affine_eq_sum_filter_support
    (D : ProjectiveDivisor C₁) (Q : C₂.SmoothPoint) :
    φ.pushforwardDivisorVal cd D (ProjectiveSmoothPoint.affine Q) =
      ∑ x ∈ D.support.filter
        (fun x ↦ placeImage φ cd x = ProjectiveSmoothPoint.affine Q), D x := by
  rw [pushforwardDivisorVal_apply, Finsupp.mapDomain,
    Finsupp.sum_apply, Finsupp.sum, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro x hx
  rw [Finsupp.single_apply]

include φ cd in
/-- **The fibre over a place is realised by a smooth point** (the existence half of the
fibre bijection): every prime `Q'` of `F[C₁]` lying over the maximal ideal `m_Q` is
`m_{P'}` for some smooth point `P'` of `C₁` with `φ P' = Q`.  Built from
`exists_smoothPoint_of_isMaximal` (a smooth point realising the maximal prime `Q'`) and
`maximalIdealAt_liesOver_toPointMap` + `maximalIdealAt_injective` (its image is `Q`). -/
private theorem exists_smoothPoint_maximalIdealAt_eq_of_mem_primesOverFinset
    (Q : C₂.SmoothPoint) (Q' : Ideal C₁.CoordinateRing)
    (hQ' : letI : Algebra C₂.CoordinateRing C₁.CoordinateRing := cd.toAlgebra
      Q' ∈ IsDedekindDomain.primesOverFinset (C₂.maximalIdealAt Q) C₁.CoordinateRing) :
    ∃ P' : C₁.SmoothPoint, C₁.maximalIdealAt P' = Q' ∧ toPointMap cd P' = Q := by
  letI algCR : Algebra C₂.CoordinateRing C₁.CoordinateRing := cd.toAlgebra
  letI modCR : Module C₂.CoordinateRing C₁.CoordinateRing := algCR.toModule
  haveI hfin' : @Module.Finite C₂.CoordinateRing C₁.CoordinateRing _ _ modCR :=
    cd.module_finite
  haveI htf : @Module.IsTorsionFree C₂.CoordinateRing C₁.CoordinateRing _ _ modCR :=
    isTorsionFree_coordHom φ cd
  haveI hpMax : (C₂.maximalIdealAt Q).IsMaximal := C₂.maximalIdealAt_isMaximal Q
  have hp_ne : C₂.maximalIdealAt Q ≠ ⊥ := C₂.maximalIdealAt_ne_bot Q
  rw [IsDedekindDomain.mem_primesOverFinset_iff (B := C₁.CoordinateRing) hp_ne] at hQ'
  obtain ⟨hQ'prime, hQ'lies⟩ := hQ'
  haveI : Q'.IsPrime := hQ'prime
  haveI : Q'.LiesOver (C₂.maximalIdealAt Q) := hQ'lies
  haveI hQ'max : Q'.IsMaximal := Ideal.IsPrime.isMaximal hQ'prime (by
    intro h; apply hp_ne
    have : C₂.maximalIdealAt Q = Q'.under C₂.CoordinateRing := hQ'lies.over
    rw [this, h, Ideal.under_bot])
  obtain ⟨P', hP'⟩ := C₁.exists_smoothPoint_of_isMaximal hQ'max
  refine ⟨P', hP', ?_⟩
  haveI hlies' : (C₁.maximalIdealAt P').LiesOver
      (C₂.maximalIdealAt (toPointMap cd P')) :=
    maximalIdealAt_liesOver_toPointMap φ cd P'
  have h1 : C₂.maximalIdealAt (toPointMap cd P') =
      (C₁.maximalIdealAt P').under C₂.CoordinateRing := hlies'.over
  have h2 : C₂.maximalIdealAt Q = Q'.under C₂.CoordinateRing := hQ'lies.over
  rw [hP'] at h1
  exact C₂.maximalIdealAt_injective (h1.trans h2.symm)

include φ cd in
/-- **A `maximalIdealAt`-recovering section is injective after `affine`**: if a section
`g` of the fibre satisfies `m_{g Q'} = Q'`, then `Q' ↦ affine (g Q'.1 Q'.2)` is injective
on the attached prime finset.  Two equal images give equal points (`affine` and
`maximalIdealAt` are injective), hence equal indices. -/
private theorem affine_section_injOn_attach (Q : C₂.SmoothPoint) :
    letI algCR : Algebra C₂.CoordinateRing C₁.CoordinateRing := cd.toAlgebra
    letI modCR : Module C₂.CoordinateRing C₁.CoordinateRing := algCR.toModule
    haveI : @Module.Finite C₂.CoordinateRing C₁.CoordinateRing _ _ modCR :=
      cd.module_finite
    haveI : @Module.IsTorsionFree C₂.CoordinateRing C₁.CoordinateRing _ _ modCR :=
      isTorsionFree_coordHom φ cd
    ∀ (g : (Q' : Ideal C₁.CoordinateRing) →
        Q' ∈ IsDedekindDomain.primesOverFinset (C₂.maximalIdealAt Q) C₁.CoordinateRing →
        C₁.SmoothPoint)
      (_ : ∀ Q' (hQ' : Q' ∈ IsDedekindDomain.primesOverFinset
        (C₂.maximalIdealAt Q) C₁.CoordinateRing), C₁.maximalIdealAt (g Q' hQ') = Q')
      ⦃a : {x // x ∈ IsDedekindDomain.primesOverFinset (C₂.maximalIdealAt Q) C₁.CoordinateRing}⦄
      (_ : a ∈ (IsDedekindDomain.primesOverFinset (C₂.maximalIdealAt Q) C₁.CoordinateRing).attach)
      ⦃b : {x // x ∈ IsDedekindDomain.primesOverFinset (C₂.maximalIdealAt Q) C₁.CoordinateRing}⦄
      (_ : b ∈ (IsDedekindDomain.primesOverFinset (C₂.maximalIdealAt Q) C₁.CoordinateRing).attach),
      ProjectiveSmoothPoint.affine (g a.1 a.2) = ProjectiveSmoothPoint.affine (g b.1 b.2) →
        a = b := by
  letI algCR : Algebra C₂.CoordinateRing C₁.CoordinateRing := cd.toAlgebra
  letI modCR : Module C₂.CoordinateRing C₁.CoordinateRing := algCR.toModule
  haveI hfin' : @Module.Finite C₂.CoordinateRing C₁.CoordinateRing _ _ modCR :=
    cd.module_finite
  haveI htf : @Module.IsTorsionFree C₂.CoordinateRing C₁.CoordinateRing _ _ modCR :=
    isTorsionFree_coordHom φ cd
  intro g hg a _ b _ hab
  simp only [ProjectiveSmoothPoint.affine.injEq] at hab
  apply Subtype.ext
  have hh : C₁.maximalIdealAt (g a.1 a.2) = C₁.maximalIdealAt (g b.1 b.2) := by rw [hab]
  rw [hg a.1 a.2, hg b.1 b.2] at hh
  exact hh

include φ cd in
/-- **Restricting the support fibre sum to the image of a section** (the `sum_subset`
step): for any divisor `D`, summing `D` over the support places mapping to `affine Q`
equals summing over the image of any section `g` of the primes over `m_Q` whose points
recover the ideal (`m_{g Q'} = Q'`) and map to `Q` (`φ (g Q') = Q`).  Both inclusions of
`Finset.sum_subset`: image places lie in the (filtered) support unless `D` vanishes
there, and a filtered-support place `affine P'` is the image of its own ideal `m_{P'}`. -/
private theorem sum_filter_support_eq_sum_image_section
    (D : ProjectiveDivisor C₁) (Q : C₂.SmoothPoint) :
    letI algCR : Algebra C₂.CoordinateRing C₁.CoordinateRing := cd.toAlgebra
    letI modCR : Module C₂.CoordinateRing C₁.CoordinateRing := algCR.toModule
    haveI : @Module.Finite C₂.CoordinateRing C₁.CoordinateRing _ _ modCR :=
      cd.module_finite
    haveI : @Module.IsTorsionFree C₂.CoordinateRing C₁.CoordinateRing _ _ modCR :=
      isTorsionFree_coordHom φ cd
    ∀ (g : (Q' : Ideal C₁.CoordinateRing) →
        Q' ∈ IsDedekindDomain.primesOverFinset (C₂.maximalIdealAt Q) C₁.CoordinateRing →
        C₁.SmoothPoint)
      (_ : ∀ Q' (hQ' : Q' ∈ IsDedekindDomain.primesOverFinset
        (C₂.maximalIdealAt Q) C₁.CoordinateRing), C₁.maximalIdealAt (g Q' hQ') = Q')
      (_ : ∀ Q' (hQ' : Q' ∈ IsDedekindDomain.primesOverFinset
        (C₂.maximalIdealAt Q) C₁.CoordinateRing), toPointMap cd (g Q' hQ') = Q),
      (∑ x ∈ D.support.filter
          (fun x ↦ placeImage φ cd x = ProjectiveSmoothPoint.affine Q), D x) =
        ∑ x ∈ (IsDedekindDomain.primesOverFinset (C₂.maximalIdealAt Q) C₁.CoordinateRing).attach.image
          (fun Q' ↦ ProjectiveSmoothPoint.affine (g Q'.1 Q'.2)), D x := by
  letI algCR : Algebra C₂.CoordinateRing C₁.CoordinateRing := cd.toAlgebra
  letI modCR : Module C₂.CoordinateRing C₁.CoordinateRing := algCR.toModule
  haveI hfin' : @Module.Finite C₂.CoordinateRing C₁.CoordinateRing _ _ modCR :=
    cd.module_finite
  haveI htf : @Module.IsTorsionFree C₂.CoordinateRing C₁.CoordinateRing _ _ modCR :=
    isTorsionFree_coordHom φ cd
  intro g hg_ideal hg_Q
  have hp_ne : C₂.maximalIdealAt Q ≠ ⊥ := C₂.maximalIdealAt_ne_bot Q
  apply Finset.sum_subset
  · intro x hx
    rw [Finset.mem_filter] at hx
    obtain ⟨hx_supp, hx_place⟩ := hx
    cases x with
    | infinity => simp [placeImage] at hx_place
    | affine P' =>
      simp only [placeImage, ProjectiveSmoothPoint.affine.injEq] at hx_place
      subst hx_place
      haveI hlies' : (C₁.maximalIdealAt P').LiesOver
          (C₂.maximalIdealAt (toPointMap cd P')) :=
        maximalIdealAt_liesOver_toPointMap φ cd P'
      haveI : (C₂.maximalIdealAt (toPointMap cd P')).IsMaximal :=
        C₂.maximalIdealAt_isMaximal _
      have hmemP : C₁.maximalIdealAt P' ∈
          IsDedekindDomain.primesOverFinset (C₂.maximalIdealAt (toPointMap cd P'))
            C₁.CoordinateRing := by
        rw [IsDedekindDomain.mem_primesOverFinset_iff (B := C₁.CoordinateRing) hp_ne]
        exact ⟨(C₁.maximalIdealAt_isMaximal P').isPrime, hlies'⟩
      simp only [Finset.mem_image, Finset.mem_attach, true_and, Subtype.exists]
      refine ⟨C₁.maximalIdealAt P', hmemP, ?_⟩
      congr 1
      apply C₁.maximalIdealAt_injective
      rw [hg_ideal _ hmemP]
  · intro x hx_fib hx_notfilt
    simp only [Finset.mem_image, Finset.mem_attach, true_and, Subtype.exists] at hx_fib
    obtain ⟨Q', hQ'mem, hxeq⟩ := hx_fib
    have hplace : placeImage φ cd x = ProjectiveSmoothPoint.affine Q := by
      rw [← hxeq]; simp only [placeImage]; rw [hg_Q Q' hQ'mem]
    rw [Finset.mem_filter, not_and] at hx_notfilt
    by_contra hDx
    exact hx_notfilt (Finsupp.mem_support_iff.mpr hDx) hplace

include φ cd in
/-- **The image fibre sum is the primes-over count sum** (the `sum_image` reindexing
step): for nonzero `w` and a section `g` recovering ideals (`m_{g Q'} = Q'`), summing
`div(algebraMap w)` over the image of `g` equals `Σ_{Q' over m_Q} count_{Q'}(span{w})`.
Reindexes along the injective image (`affine_section_injOn_attach`), then identifies each
coefficient via `projectiveDivisorOf_algebraMap_apply_affine_eq_count` and `m_{g Q'} = Q'`. -/
private theorem sum_image_section_eq_sum_primesOver
    (w : C₁.CoordinateRing) (hw : w ≠ 0) (Q : C₂.SmoothPoint) :
    letI algCR : Algebra C₂.CoordinateRing C₁.CoordinateRing := cd.toAlgebra
    letI modCR : Module C₂.CoordinateRing C₁.CoordinateRing := algCR.toModule
    haveI : @Module.Finite C₂.CoordinateRing C₁.CoordinateRing _ _ modCR :=
      cd.module_finite
    haveI : @Module.IsTorsionFree C₂.CoordinateRing C₁.CoordinateRing _ _ modCR :=
      isTorsionFree_coordHom φ cd
    ∀ (g : (Q' : Ideal C₁.CoordinateRing) →
        Q' ∈ IsDedekindDomain.primesOverFinset (C₂.maximalIdealAt Q) C₁.CoordinateRing →
        C₁.SmoothPoint)
      (_ : ∀ Q' (hQ' : Q' ∈ IsDedekindDomain.primesOverFinset
        (C₂.maximalIdealAt Q) C₁.CoordinateRing), C₁.maximalIdealAt (g Q' hQ') = Q'),
      (∑ x ∈ (IsDedekindDomain.primesOverFinset (C₂.maximalIdealAt Q) C₁.CoordinateRing).attach.image
          (fun Q' ↦ ProjectiveSmoothPoint.affine (g Q'.1 Q'.2)),
          (C₁.projectiveDivisorOf (algebraMap C₁.CoordinateRing C₁.FunctionField w)) x) =
        ∑ Q' ∈ IsDedekindDomain.primesOverFinset (C₂.maximalIdealAt Q) C₁.CoordinateRing,
          ((Associates.mk Q').count (Associates.mk (Ideal.span ({w} : Set _))).factors : ℤ) := by
  letI algCR : Algebra C₂.CoordinateRing C₁.CoordinateRing := cd.toAlgebra
  letI modCR : Module C₂.CoordinateRing C₁.CoordinateRing := algCR.toModule
  haveI hfin' : @Module.Finite C₂.CoordinateRing C₁.CoordinateRing _ _ modCR :=
    cd.module_finite
  haveI htf : @Module.IsTorsionFree C₂.CoordinateRing C₁.CoordinateRing _ _ modCR :=
    isTorsionFree_coordHom φ cd
  intro g hg_ideal
  rw [Finset.sum_image (affine_section_injOn_attach φ cd Q g hg_ideal)]
  rw [← Finset.sum_attach (IsDedekindDomain.primesOverFinset (C₂.maximalIdealAt Q) C₁.CoordinateRing)
    (fun Q' ↦ ((Associates.mk Q').count
      (Associates.mk (Ideal.span ({w} : Set _))).factors : ℤ))]
  apply Finset.sum_congr rfl
  intro Q' _
  rw [projectiveDivisorOf_algebraMap_apply_affine_eq_count w hw (g Q'.1 Q'.2),
    hg_ideal Q'.1 Q'.2]

set_option synthInstance.maxHeartbeats 100000 in
-- The fibre bijection `{primes over m_Q} ≃ {P : φP = Q}` and the supporting
-- `LiesOver`/`maximalIdealAt` defeq are heartbeat-heavy, hence the scoped bumps.
set_option maxHeartbeats 400000 in
include φ cd in
/-- **The pushforward coefficient at an affine place is the fibre sum** (the heart of
the affine matching in `II.3.6`): the `affine Q` coefficient of
`φ_∗(div(algebraMap w))` equals `Σ_{Q' over m_Q} count_{Q'}(span{w})`, the sum over
the primes `Q'` of `F[C₁]` lying over the maximal ideal `m_Q`.  Proof via the fibre
bijection `{P : φP = Q} ≃ {primes over m_Q}` (`exists_smoothPoint_of_isMaximal` +
`maximalIdealAt_liesOver_toPointMap`), realised as a `Finset.sum_subset` /
`Finset.sum_image` reindexing of the `mapDomain` defining `pushforwardDivisorVal`. -/
private theorem pushforwardDivisorVal_projectiveDivisorOf_affine_eq_sum_fiber
    (w : C₁.CoordinateRing) (hw : w ≠ 0) (Q : C₂.SmoothPoint) :
    letI algCR : Algebra C₂.CoordinateRing C₁.CoordinateRing := cd.toAlgebra
    letI modCR : Module C₂.CoordinateRing C₁.CoordinateRing := algCR.toModule
    haveI : @Module.Finite C₂.CoordinateRing C₁.CoordinateRing _ _ modCR :=
      cd.module_finite
    haveI : @Module.IsTorsionFree C₂.CoordinateRing C₁.CoordinateRing _ _ modCR :=
      isTorsionFree_coordHom φ cd
    φ.pushforwardDivisorVal cd (C₁.projectiveDivisorOf
        (algebraMap C₁.CoordinateRing C₁.FunctionField w))
        (ProjectiveSmoothPoint.affine Q) =
      ∑ Q' ∈ IsDedekindDomain.primesOverFinset (C₂.maximalIdealAt Q) C₁.CoordinateRing,
        ((Associates.mk Q').count (Associates.mk (Ideal.span ({w} : Set _))).factors : ℤ) := by
  classical
  letI algCR : Algebra C₂.CoordinateRing C₁.CoordinateRing := cd.toAlgebra
  letI modCR : Module C₂.CoordinateRing C₁.CoordinateRing := algCR.toModule
  haveI hfin' : @Module.Finite C₂.CoordinateRing C₁.CoordinateRing _ _ modCR :=
    cd.module_finite
  haveI htf : @Module.IsTorsionFree C₂.CoordinateRing C₁.CoordinateRing _ _ modCR :=
    isTorsionFree_coordHom φ cd
  -- Choose a section `pt` of the fibre `{primes over m_Q} → {smooth points P'}`, with
  -- `m_{pt Q'} = Q'` and `φ (pt Q') = Q`, via the existence lemma.
  let pt : (Q' : Ideal C₁.CoordinateRing) →
      Q' ∈ IsDedekindDomain.primesOverFinset (C₂.maximalIdealAt Q) C₁.CoordinateRing →
      C₁.SmoothPoint :=
    fun Q' hQ' ↦ (exists_smoothPoint_maximalIdealAt_eq_of_mem_primesOverFinset φ cd Q Q' hQ').choose
  have hpt_ideal : ∀ Q' (hQ' : Q' ∈ IsDedekindDomain.primesOverFinset
        (C₂.maximalIdealAt Q) C₁.CoordinateRing), C₁.maximalIdealAt (pt Q' hQ') = Q' :=
    fun Q' hQ' ↦
      (exists_smoothPoint_maximalIdealAt_eq_of_mem_primesOverFinset φ cd Q Q' hQ').choose_spec.1
  have hpt_Q : ∀ Q' (hQ' : Q' ∈ IsDedekindDomain.primesOverFinset
        (C₂.maximalIdealAt Q) C₁.CoordinateRing), toPointMap cd (pt Q' hQ') = Q :=
    fun Q' hQ' ↦
      (exists_smoothPoint_maximalIdealAt_eq_of_mem_primesOverFinset φ cd Q Q' hQ').choose_spec.2
  -- Affine coefficient = support fibre sum (`H2`) = image fibre sum (`H5`) = primes-over
  -- count sum (`H6`); the last is the goal.
  rw [pushforwardDivisorVal_apply_affine_eq_sum_filter_support φ cd
      (C₁.projectiveDivisorOf (algebraMap C₁.CoordinateRing C₁.FunctionField w)) Q,
    sum_filter_support_eq_sum_image_section φ cd
      (C₁.projectiveDivisorOf (algebraMap C₁.CoordinateRing C₁.FunctionField w)) Q
      pt hpt_ideal hpt_Q,
    sum_image_section_eq_sum_primesOver φ cd w hw Q pt hpt_ideal]

set_option synthInstance.maxHeartbeats 100000 in
-- Synthesising the cross-algebra `Algebra C₂.CR C₁.FF` for the scalar towers (needed
-- by `Algebra.algebraMap_intNorm`) is heartbeat-heavy, hence the scoped bumps.
set_option maxHeartbeats 500000 in
include φ cd in
/-- **Affine coefficients of the `algebraMap` norm–conorm identity agree**: for a
nonzero `w ∈ F[C₁]` and any smooth point `Q` of `C₂`, the `affine Q` coefficient of
`div(N_φ (algebraMap w))` equals that of `φ_∗(div(algebraMap w))`.  The left side is
the ideal count `count_{m_Q}(span{N w})` (via
`pushforward_algebraMap_eq_algebraMap_intNorm` + `ord_P_algebraMap_eq_count`); the
right side is the fibre sum (via `pushforwardDivisorVal_projectiveDivisorOf_affine_eq_sum_fiber`);
the two are matched by `count_relNorm_eq_sum_fiber`. -/
private theorem projectiveDivisorOf_pushforward_algebraMap_apply_affine
    (w : C₁.CoordinateRing) (hw : w ≠ 0) (Q : C₂.SmoothPoint) :
    letI algCR : Algebra C₂.CoordinateRing C₁.CoordinateRing := cd.toAlgebra
    letI modCR : Module C₂.CoordinateRing C₁.CoordinateRing := algCR.toModule
    haveI : @Module.Finite C₂.CoordinateRing C₁.CoordinateRing _ _ modCR :=
      cd.module_finite
    haveI : @Module.IsTorsionFree C₂.CoordinateRing C₁.CoordinateRing _ _ modCR :=
      isTorsionFree_coordHom φ cd
    C₂.projectiveDivisorOf (φ.pushforward (algebraMap C₁.CoordinateRing C₁.FunctionField w))
        (ProjectiveSmoothPoint.affine Q) =
      φ.pushforwardDivisorVal cd (C₁.projectiveDivisorOf
        (algebraMap C₁.CoordinateRing C₁.FunctionField w)) (ProjectiveSmoothPoint.affine Q) := by
  classical
  letI algCR : Algebra C₂.CoordinateRing C₁.CoordinateRing := cd.toAlgebra
  letI modCR : Module C₂.CoordinateRing C₁.CoordinateRing := algCR.toModule
  haveI hfin' : @Module.Finite C₂.CoordinateRing C₁.CoordinateRing _ _ modCR :=
    cd.module_finite
  haveI htf : @Module.IsTorsionFree C₂.CoordinateRing C₁.CoordinateRing _ _ modCR :=
    isTorsionFree_coordHom φ cd
  have hnw : Algebra.intNorm C₂.CoordinateRing C₁.CoordinateRing w ≠ 0 :=
    intNorm_ne_zero_of_ne_zero φ cd w hw
  rw [pushforward_algebraMap_eq_algebraMap_intNorm φ cd w,
    C₂.projectiveDivisorOf_apply_affine, C₂.ord_P_algebraMap_eq_count Q hnw, WithTop.untopD_coe,
    pushforwardDivisorVal_projectiveDivisorOf_affine_eq_sum_fiber φ cd w hw Q]
  exact_mod_cast count_relNorm_eq_sum_fiber φ cd w hw Q

include φ cd in
/-- **Both sides of the `algebraMap` norm–conorm identity have equal degree**: for any
`w ∈ F[C₁]`, `div(N_φ (algebraMap w))` and `φ_∗(div(algebraMap w))` both have degree
`0` (each principal projective divisor has degree `0` by
`projectiveDivisorOf_degree_eq_zero`, and `φ_∗` preserves degree).  This forces the
coefficient at infinity once the affine coefficients agree. -/
private theorem projectiveDivisorOf_pushforward_algebraMap_degree_eq
    (w : C₁.CoordinateRing) :
    (C₂.projectiveDivisorOf (φ.pushforward
        (algebraMap C₁.CoordinateRing C₁.FunctionField w))).degree =
      (φ.pushforwardDivisorVal cd (C₁.projectiveDivisorOf
        (algebraMap C₁.CoordinateRing C₁.FunctionField w))).degree := by
  rw [C₂.projectiveDivisorOf_degree_eq_zero, degree_pushforwardDivisorVal,
    C₁.projectiveDivisorOf_degree_eq_zero]

/-- **The `algebraMap` case of the norm–conorm identity — Silverman II.3.6**: for a
nonzero `w ∈ F[C₁]`, `div(N_φ (algebraMap w)) = φ_∗(div(algebraMap w))`.  Two
projective divisors agree iff their affine coefficients and their infinity coefficient
agree (`Finsupp.ext`): the affine coefficients are handled by
`projectiveDivisorOf_pushforward_algebraMap_apply_affine`, and the infinity coefficient
is forced by both divisors having equal degree
(`projectiveDivisorOf_pushforward_algebraMap_degree_eq`,
`projDivisor_infinity_coeff_eq_of_affine_eq`). -/
theorem projectiveDivisorOf_pushforward_algebraMap_eq
    (w : C₁.CoordinateRing) (hw : w ≠ 0) :
    C₂.projectiveDivisorOf (φ.pushforward (algebraMap C₁.CoordinateRing C₁.FunctionField w)) =
      φ.pushforwardDivisorVal cd (C₁.projectiveDivisorOf
        (algebraMap C₁.CoordinateRing C₁.FunctionField w)) := by
  classical
  apply Finsupp.ext
  intro v
  cases v with
  | affine Q => exact projectiveDivisorOf_pushforward_algebraMap_apply_affine φ cd w hw Q
  | infinity =>
    exact projDivisor_infinity_coeff_eq_of_affine_eq _ _
      (projectiveDivisorOf_pushforward_algebraMap_degree_eq φ cd w)
      (fun Q ↦ projectiveDivisorOf_pushforward_algebraMap_apply_affine φ cd w hw Q)

end NormConormSteps

/-! ### NEW-1(ii): the `f = u/v` reduction

The deep per-place arithmetic is the `algebraMap` case
`projectiveDivisorOf_pushforward_algebraMap_eq` (in `section NormConormSteps`).
The norm–conorm identity for a *general* `f ∈ K(C₁)` follows from it by the
multiplicativity of both sides together with `IsFractionRing.div_surjective`.
The next four `private` helpers package that reduction:
* the `f = 0` base case;
* the two multiplicativity identities (one per side of the goal);
* the assembly turning the `algebraMap` case into the statement for all `f`. -/

/-- The projective divisor of the pushforward of `0` matches the pushforward of
the projective divisor of `0`: both sides vanish (`φ.pushforward 0 = 0` is
`Algebra.norm_zero`, needing finiteness of `K(C₁)/φ*K(C₂)`, and
`projectiveDivisorOf 0 = 0` on each side). -/
private theorem projectiveDivisorOf_pushforward_zero (φ : CurveMap C₁ C₂)
    (cd : φ.CoordHom)
    (hfd : letI : Algebra C₂.FunctionField C₁.FunctionField := φ.toAlgebra
      FiniteDimensional C₂.FunctionField C₁.FunctionField) :
    C₂.projectiveDivisorOf (φ.pushforward (0 : C₁.FunctionField)) =
      φ.pushforwardDivisorVal cd (C₁.projectiveDivisorOf (0 : C₁.FunctionField)) := by
  letI algFF : Algebra C₂.FunctionField C₁.FunctionField := φ.toAlgebra
  haveI : FiniteDimensional C₂.FunctionField C₁.FunctionField := hfd
  rw [show φ.pushforward (0 : C₁.FunctionField) = 0 from Algebra.norm_zero,
    C₂.projectiveDivisorOf_zero, C₁.projectiveDivisorOf_zero, map_zero]

/-- **LHS multiplicativity.** The projective divisor of the pushforward of a
product splits additively: `φ.pushforward` is a monoid hom and
`projectiveDivisorOf` is additive on nonzero products
(`projectiveDivisorOf_mul`). -/
private theorem projectiveDivisorOf_pushforward_mul (φ : CurveMap C₁ C₂)
    {g h : C₁.FunctionField} (hg : g ≠ 0) (hh : h ≠ 0) :
    C₂.projectiveDivisorOf (φ.pushforward (g * h)) =
      C₂.projectiveDivisorOf (φ.pushforward g) +
        C₂.projectiveDivisorOf (φ.pushforward h) := by
  have hpg : φ.pushforward g ≠ 0 := (IsUnit.map φ.pushforward (isUnit_iff_ne_zero.mpr hg)).ne_zero
  have hph : φ.pushforward h ≠ 0 := (IsUnit.map φ.pushforward (isUnit_iff_ne_zero.mpr hh)).ne_zero
  rw [map_mul, C₂.projectiveDivisorOf_mul hpg hph]

/-- **RHS multiplicativity.** The pushforward of the projective divisor of a
product splits additively: `projectiveDivisorOf` is additive on nonzero products
(`projectiveDivisorOf_mul`) and `pushforwardDivisorVal` is an additive hom. -/
private theorem pushforwardDivisorVal_projectiveDivisorOf_mul (φ : CurveMap C₁ C₂)
    (cd : φ.CoordHom) {g h : C₁.FunctionField} (hg : g ≠ 0) (hh : h ≠ 0) :
    φ.pushforwardDivisorVal cd (C₁.projectiveDivisorOf (g * h)) =
      φ.pushforwardDivisorVal cd (C₁.projectiveDivisorOf g) +
        φ.pushforwardDivisorVal cd (C₁.projectiveDivisorOf h) := by
  rw [C₁.projectiveDivisorOf_mul hg hh, map_add]

/-- **The `f = u/v` reduction.** Given the norm–conorm identity on the image of
`algebraMap` (the `algebraMap` case `key`), it holds for every `f ∈ K(C₁)`.
Writing a nonzero `f` as `au / av` with `au, av` images of nonzero coordinate-ring
elements (`IsFractionRing.div_surjective`), `f * av = au`; multiplicativity of
both sides (`projectiveDivisorOf_pushforward_mul`,
`pushforwardDivisorVal_projectiveDivisorOf_mul`) reduces the goal for `f` to the
`algebraMap` case applied to `u` and `v`. -/
private theorem projectiveDivisorOf_pushforward_eq_of_algebraMap (φ : CurveMap C₁ C₂)
    (cd : φ.CoordHom)
    (hfd : letI : Algebra C₂.FunctionField C₁.FunctionField := φ.toAlgebra
      FiniteDimensional C₂.FunctionField C₁.FunctionField)
    (key : ∀ w : C₁.CoordinateRing, w ≠ 0 →
      C₂.projectiveDivisorOf (φ.pushforward (algebraMap C₁.CoordinateRing C₁.FunctionField w)) =
        φ.pushforwardDivisorVal cd (C₁.projectiveDivisorOf
          (algebraMap C₁.CoordinateRing C₁.FunctionField w)))
    (f : C₁.FunctionField) :
    C₂.projectiveDivisorOf (φ.pushforward f) =
      φ.pushforwardDivisorVal cd (C₁.projectiveDivisorOf f) := by
  by_cases hf : f = 0
  · subst hf; exact projectiveDivisorOf_pushforward_zero φ cd hfd
  · obtain ⟨u, v, hv_mem, hf_eq⟩ := IsFractionRing.div_surjective (A := C₁.CoordinateRing) f
    have hv_ne : v ≠ 0 := nonZeroDivisors.ne_zero hv_mem
    set au := algebraMap C₁.CoordinateRing C₁.FunctionField u with hau
    set av := algebraMap C₁.CoordinateRing C₁.FunctionField v with hav
    have hav_ne : av ≠ 0 := fun h ↦
      hv_ne ((IsFractionRing.injective C₁.CoordinateRing C₁.FunctionField)
        (h.trans (map_zero _).symm))
    have hu_ne : u ≠ 0 := fun hu ↦ hf (by rw [← hf_eq, hau, hu, map_zero, zero_div])
    -- `f * av = au`, so additivity of both sides reduces `f` to `u` and `v`.
    have hf_av : f * av = au := by rw [← hf_eq, div_mul_cancel₀ _ hav_ne]
    have hgoalL : C₂.projectiveDivisorOf (φ.pushforward f) =
        C₂.projectiveDivisorOf (φ.pushforward au) -
          C₂.projectiveDivisorOf (φ.pushforward av) := by
      rw [← hf_av, projectiveDivisorOf_pushforward_mul φ hf hav_ne]; abel
    have hgoalR : φ.pushforwardDivisorVal cd (C₁.projectiveDivisorOf f) =
        φ.pushforwardDivisorVal cd (C₁.projectiveDivisorOf au) -
          φ.pushforwardDivisorVal cd (C₁.projectiveDivisorOf av) := by
      rw [← hf_av, pushforwardDivisorVal_projectiveDivisorOf_mul φ cd hf hav_ne]; abel
    rw [hgoalL, hgoalR, hau, hav, key u hu_ne, key v hv_ne]

/-- **NEW-1(ii) — Silverman II.3.6, norm–conorm identity** `div(N_φ f) = φ_∗(div f)`.
For a curve map `φ : C₁ → C₂` with coordinate-ring witness `cd` and a function
`f ∈ K(C₁)`, the projective divisor of the conorm `N_φ f = φ.pushforward f`
equals the valuation-theoretic pushforward of the projective divisor of `f`.

The content is the per-place identity `ord_Q(N_φ f) = Σ_{P ↦ Q} f_{P/Q}·ord_P(f)`
(with inertia degrees `f_{P/Q} = 1` over an algebraically closed field), proved
via `Ideal.sum_ramification_inertia`, `Ideal.relNorm`, and `Algebra.intNorm`.

The proof is the generalisation of the `F[X] → F[C]` machinery of
`NormValuation.lean` (`count_relNorm_singleton_eq_sum_count_fiber`,
`relNorm_maximalIdealAt`) to the *coordinate-ring extension* `F[C₂] → F[C₁]`
induced by `cd`.  The instance-heavy steps are factored into the sub-lemmas of
`section NormConormSteps`, each re-establishing the `cd`-induced algebra and its
`Module.Finite`/`IsTorsionFree` structure internally (a `relNorm`/`intNorm`
statement only typechecks with those instances in scope, so the sub-lemmas state
them via `letI`/`haveI`-in-type and re-derive them in the body):
* `finiteDimensional_functionField` — the finite extension `K(C₂) → K(C₁)`
  (needed only for the `f = 0` branch below);
* the degree/`finrank` coherence `finrank_{liftAlgebra} = φ.degree`
  (`IsFractionRing.lift_unique` + `cd.compat`, so `relNorm_algebraMap` yields
  `m_Q ^ φ.degree`), computed inside `relNorm_maximalIdealAt_eq`;
* `relNorm_maximalIdealAt_eq` — the **`s = 1` core** `relNorm_{F[C₂]}(m_P) = m_{φP}`
  from the global balance `relNorm(m_Q·F[C₁]) = m_Q^{φ.degree} =
  ∏ relNorm(m_{P'})^{e_{P'}}` together with `Σ e_{P'}·f_{P'} = φ.degree`
  (`sum_ramificationIdx_mul_inertiaDeg_eq_degree`) and `f_{P'} = 1`
  (`inertiaDeg_maximalIdealAt_toPointMap`), forcing each exponent to 1;
* `count_relNorm_eq_sum_fiber` — the affine count identity
  `count_{m_Q}(relNorm (span{u})) = Σ_{Q' over m_Q} count_{Q'}(span{u})`;
* `projectiveDivisorOf_pushforward_algebraMap_eq` — the `algebraMap` case, matching
  the affine coefficients to the `mapDomain` fibre sum of `pushforwardDivisorVal`
  via the bijection `{P : φP = Q} ≃ {primes over m_Q}` (`maximalIdealAt_toPointMap`
  + `exists_smoothPoint_of_isMaximal`), the place at infinity being forced by
  `projectiveDivisorOf_degree_eq_zero` (both projective divisors have degree `0`,
  and `pushforwardDivisorVal` preserves degree).
Here the general `f = u/v` reduces to `f = algebraMap u`, `u ∈ F[C₁]` nonzero, via
`IsFractionRing.div_surjective` and the additivity of both sides
(`projectiveDivisorOf_mul`, `pushforward_mul`, `pushforwardDivisorVal` a hom). -/
theorem projectiveDivisorOf_pushforward_eq_pushforwardDivisorVal [IsAlgClosed F]
    [IsDedekindDomain C₁.CoordinateRing] [IsDedekindDomain C₂.CoordinateRing]
    [IsIntegrallyClosed C₁.CoordinateRing] [IsIntegrallyClosed C₂.CoordinateRing]
    (φ : CurveMap C₁ C₂) (cd : φ.CoordHom)
    (f : C₁.FunctionField) :
    C₂.projectiveDivisorOf (φ.pushforward f) =
      φ.pushforwardDivisorVal cd (C₁.projectiveDivisorOf f) := by
  -- The deep per-place arithmetic is the `algebraMap` case
  -- `projectiveDivisorOf_pushforward_algebraMap_eq` (affine coefficients via the
  -- count identity, infinity coefficient forced by degree).  The general `f`
  -- follows by the `f = u/v` reduction `projectiveDivisorOf_pushforward_eq_of_algebraMap`,
  -- which only uses multiplicativity of both sides and `div_surjective` (plus
  -- finiteness of `K(C₁)/φ*K(C₂)` for the `f = 0` branch).
  exact projectiveDivisorOf_pushforward_eq_of_algebraMap φ cd
    (finiteDimensional_functionField φ cd)
    (projectiveDivisorOf_pushforward_algebraMap_eq φ cd) f

end HasseWeil.Curves.CurveMap

/-! ### NEW-1(iii)/(iv): compatibility + the gap `h_pres` -/

namespace HasseWeil.EC.Isogeny

open HasseWeil.Curves

variable {F : Type*} [Field F] [DecidableEq F]
variable {W₁ W₂ : Affine F} [W₁.IsElliptic] [W₂.IsElliptic]

/-- **NEW-1(iii)**: the point-map pushforward `pushforwardProjectiveDivisor`
agrees with the valuation-theoretic pushforward `pushforwardDivisorVal`.  By
construction the two `mapDomain` place-image maps coincide, so this is `rfl`
up to the `(φP).toProjectiveSmoothPoint = affine (toPointMap cd P)` identity. -/
theorem pushforwardProjectiveDivisor_eq_pushforwardDivisorVal (φ : Isogeny W₁ W₂)
    (cd : φ.toCurveMap.CoordHom) (D : ProjectiveDivisor (⟨W₁⟩ : SmoothPlaneCurve F)) :
    pushforwardProjectiveDivisor φ cd D =
      φ.toCurveMap.pushforwardDivisorVal cd D := by
  rw [pushforwardProjectiveDivisor_apply, CurveMap.pushforwardDivisorVal_apply]
  -- The two `mapDomain` place-image maps agree pointwise.
  congr 1
  funext P
  cases P with
  | infinity =>
    -- `∞.toAffinePoint = 0`, `φ.toPointMap cd 0 = 0`, `(0).toProjectiveSmoothPoint = ∞`.
    rfl
  | affine P' =>
    -- `(affine P').toAffinePoint = some P'.x P'.y …`; the point map promotes to
    -- `affine (toPointMap cd P')` after the round-trip.
    rfl

/-- **NEW-1(iv) / `h_pres` — Silverman II.3.7**: the pushforward `φ_∗` carries
principal projective divisors to principal ones.  This is the sole deep input to
Silverman III.4.8 (`EC.Isogeny.addHomProperty`); it falls out of the norm–conorm
identity (NEW-1 ii) since the pushforward of `div f` is `div(N_φ f)`, again
principal. -/
theorem pushforward_preserves_principal [IsAlgClosed F]
    [IsDedekindDomain (⟨W₁⟩ : SmoothPlaneCurve F).CoordinateRing]
    [IsDedekindDomain (⟨W₂⟩ : SmoothPlaneCurve F).CoordinateRing]
    [IsIntegrallyClosed (⟨W₁⟩ : SmoothPlaneCurve F).CoordinateRing]
    [IsIntegrallyClosed (⟨W₂⟩ : SmoothPlaneCurve F).CoordinateRing]
    (φ : Isogeny W₁ W₂) (cd : φ.toCurveMap.CoordHom)
    (D : ProjectiveDivisor (⟨W₁⟩ : SmoothPlaneCurve F))
    (hD : D ∈ (⟨W₁⟩ : SmoothPlaneCurve F).projPrincipalSubgroup) :
    pushforwardProjectiveDivisor φ cd D ∈
      (⟨W₂⟩ : SmoothPlaneCurve F).projPrincipalSubgroup := by
  -- `D = projectiveDivisorOf f` for some nonzero `f`; its pushforward is
  -- `projectiveDivisorOf (N_φ f)` by the norm–conorm identity, hence principal.
  obtain ⟨f, hf_ne, hfD⟩ := hD
  refine ⟨φ.toCurveMap.pushforward f, ?_, ?_⟩
  · -- `N_φ f ≠ 0`: the norm (a monoid hom) sends the unit `f` to a unit.
    exact (IsUnit.map φ.toCurveMap.pushforward (hf_ne.isUnit)).ne_zero
  · -- `div(N_φ f) = φ_∗(div f) = φ_∗ D`.
    rw [pushforwardProjectiveDivisor_eq_pushforwardDivisorVal, ← hfD,
      CurveMap.projectiveDivisorOf_pushforward_eq_pushforwardDivisorVal
        φ.toCurveMap cd f]

end HasseWeil.EC.Isogeny
