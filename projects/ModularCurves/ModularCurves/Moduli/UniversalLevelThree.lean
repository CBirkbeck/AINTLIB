/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.Moduli.UniversalLegendre
import ModularCurves.EllipticCurve.AffineSectionSpecPoints
import ModularCurves.ForMathlib.E3RelSquarefree
import ModularCurves.ForMathlib.PairGeneratesOfCardSq
import ModularCurves.Moduli.LevelSpaceEtale
import ModularCurves.EllipticCurve.E3NormalForm

/-!
# The universal naive level-3 object `ℰ₃` over `ℤ[1/3]` (T-E15a)

**(STREAM-OMEGA 2026-07-14; the KM Ex. 2.2.2 / GME 2.2.10 bootstrap object.)** The
moduli ring `R[1/3][β, γ][((a₁³−27a₃)a₃)⁻¹]/(β³−(β+γ)³)` carrying the universal
`[3]P = 0`-normal-form curve `y² + a₁xy + a₃y = x³` with `a₁ = 3γ − 1`,
`a₃ = −3γ² − β − 3βγ`, marked `P = (0, 0)` and `Q = (γ, β + γ)` — the engine input
for KM 4.7.0's `(3, GL₂(𝔽₃))`-instantiation (`naiveLevelThree_representable_by_affine`,
`Moduli/Bootstrap.lean`).

The construction replays the T-E14-AX1 stack (`Moduli/UniversalLegendre.lean`):
moduli ring → universal curve → ellipticity → tautological presentation → marked
sections via `projModelAffineSection`.
-/

universe u

noncomputable section

namespace ModularCurves

open AlgebraicGeometry CategoryTheory Limits Scheme MvPolynomial LocalPresentation

variable (R : CommRingCat.{u})

/-- **(T-E15a)** The `a₁`-parameter polynomial `3γ − 1` in `R[β, γ]`
(`X 0 = β`, `X 1 = γ`). -/
def e3A₁Poly : MvPolynomial (Fin 2) R :=
  3 * X 1 - 1

/-- **(T-E15a)** The `a₃`-parameter polynomial `−3γ² − β − 3βγ`. -/
def e3A₃Poly : MvPolynomial (Fin 2) R :=
  -3 * X 1 ^ 2 - X 0 - 3 * X 0 * X 1

/-- **(T-E15a)** The flex relation `β³ − (β + γ)³`. -/
def e3Rel : MvPolynomial (Fin 2) R :=
  X 0 ^ 3 - (X 0 + X 1) ^ 3

/-- **(T-E15a)** The coordinate ring of the flex locus: `R[β, γ]/(β³ − (β+γ)³)`. -/
abbrev E3Quotient : Type u :=
  MvPolynomial (Fin 2) R ⧸ Ideal.span {e3Rel R}

/-- **(T-E15a; B2-fix v10.256)** The discriminant-type element `(a₁³ − 27a₃) · a₃ · γ`
in the flex-locus ring. The **`γ` factor** (added 2026-07-15, owner-approved) inverts
`γ = x(Q)`, excluding the degenerate locus `γ = 0` where `Q = (0, β) = −P ∈ ⟨P⟩` fails
to be a full level-`3` basis (it generates only `ℤ/3`). Without it `E3ModuliRing`
over-represented the naive level-`3` functor. -/
def e3Delta : E3Quotient R :=
  Ideal.Quotient.mk _ ((e3A₁Poly R ^ 3 - 27 * e3A₃Poly R) * e3A₃Poly R * X 1)

/-- **(T-E15a)** The T-E15 moduli ring
`R[β, γ][((a₁³−27a₃)a₃γ)⁻¹]/(β³−(β+γ)³)` — KM Ex. 2.2.2's `ℰ₃`-base (with `γ` inverted:
`Q ∉ ⟨P⟩`). -/
abbrev E3ModuliRing : Type u :=
  Localization.Away (e3Delta R)

/-- **(T-E15a)** The universal `β`. -/
def e3Beta : E3ModuliRing R :=
  algebraMap (E3Quotient R) (E3ModuliRing R) (Ideal.Quotient.mk _ (X 0))

/-- **(T-E15a)** The universal `γ`. -/
def e3Gamma : E3ModuliRing R :=
  algebraMap (E3Quotient R) (E3ModuliRing R) (Ideal.Quotient.mk _ (X 1))

/-- **(T-E15a)** The universal naive-level-3 curve `y² + a₁xy + a₃y = x³`:
`a₁ = 3γ − 1`, `a₃ = −3γ² − β − 3βγ`, `a₂ = a₄ = a₆ = 0` (the `[3]P = 0` normal form —
`P = (0,0)` is a flex with horizontal tangent). -/
def universalE3 : WeierstrassCurve (E3ModuliRing R) :=
  ⟨3 * e3Gamma R - 1, 0, -3 * e3Gamma R ^ 2 - e3Beta R - 3 * e3Beta R * e3Gamma R,
    0, 0⟩

/-- The universal curve's discriminant is `a₃³(a₁³ − 27a₃)` — for the `[3]`-normal
form `y² + a₁xy + a₃y = x³`. -/
theorem universalE3_Δ :
    (universalE3 R).Δ = (universalE3 R).a₃ ^ 3 *
      ((universalE3 R).a₁ ^ 3 - 27 * (universalE3 R).a₃) := by
  simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈, universalE3]
  ring

/-- The composite `R[β,γ] → moduli ring` ring map. -/
def e3Map : MvPolynomial (Fin 2) R →+* E3ModuliRing R :=
  (algebraMap (E3Quotient R) (E3ModuliRing R)).comp
    (Ideal.Quotient.mk (Ideal.span {e3Rel R}))

/-- The `a₁`-parameter lands on the universal `a₁`. -/
theorem e3Map_a₁Poly : e3Map R (e3A₁Poly R) = (universalE3 R).a₁ := by
  show e3Map R (3 * X 1 - 1) = 3 * e3Gamma R - 1
  rw [map_sub, map_mul, map_one, map_ofNat]
  rfl

/-- The `a₃`-parameter lands on the universal `a₃`. -/
theorem e3Map_a₃Poly : e3Map R (e3A₃Poly R) = (universalE3 R).a₃ := by
  show e3Map R (-3 * X 1 ^ 2 - X 0 - 3 * X 0 * X 1) =
    -3 * e3Gamma R ^ 2 - e3Beta R - 3 * e3Beta R * e3Gamma R
  rw [map_sub, map_sub, map_mul, map_pow, map_mul, map_mul, map_neg, map_ofNat]
  rfl

/-- The image of the defining element under the localization is the curve's
`(a₁³ − 27a₃)·a₃·γ`. -/
theorem e3Delta_map :
    algebraMap (E3Quotient R) (E3ModuliRing R) (e3Delta R) =
      ((universalE3 R).a₁ ^ 3 - 27 * (universalE3 R).a₃) * (universalE3 R).a₃ * e3Gamma R := by
  show e3Map R ((e3A₁Poly R ^ 3 - 27 * e3A₃Poly R) * e3A₃Poly R * X 1) = _
  rw [map_mul, map_mul, map_sub, map_pow, map_mul, map_ofNat, e3Map_a₁Poly, e3Map_a₃Poly]
  rfl

instance : (universalE3 R).IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff, universalE3_Δ]
  have h := IsLocalization.Away.algebraMap_isUnit
    (S := E3ModuliRing R) (e3Delta R)
  rw [e3Delta_map] at h
  replace h := isUnit_of_mul_isUnit_left h
  have h3 : IsUnit ((universalE3 R).a₃ ^ 3 *
      ((universalE3 R).a₁ ^ 3 - 27 * (universalE3 R).a₃)) ↔
    IsUnit (((universalE3 R).a₃ *
      ((universalE3 R).a₁ ^ 3 - 27 * (universalE3 R).a₃)) *
      ((universalE3 R).a₃ * (universalE3 R).a₃)) := by
    constructor <;> intro hu <;>
      [skip; skip] <;>
      · refine (isUnit_iff_exists_inv.mpr ?_)
        obtain ⟨v, hv⟩ := isUnit_iff_exists_inv.mp hu
        exact ⟨v, by linear_combination hv⟩
  rw [h3]
  refine IsUnit.mul ?_ ?_
  · rwa [mul_comm ((universalE3 R).a₁ ^ 3 - 27 * (universalE3 R).a₃)] at h
  · have ha₃ : IsUnit (((universalE3 R).a₁ ^ 3 - 27 * (universalE3 R).a₃) *
        (universalE3 R).a₃) := h
    exact (isUnit_of_mul_isUnit_right ha₃).mul (isUnit_of_mul_isUnit_right ha₃)

/-- **(B2-fix v10.256)** The universal `γ = x(Q)` is a unit — this is the whole point of
inverting it in `e3Delta`: it certifies `Q ∉ ⟨P⟩` (the level-`3` basis condition). -/
theorem isUnit_e3Gamma : IsUnit (e3Gamma R) := by
  have h := IsLocalization.Away.algebraMap_isUnit (S := E3ModuliRing R) (e3Delta R)
  rw [e3Delta_map] at h
  exact isUnit_of_mul_isUnit_right h

/-- The flex relation vanishes in the moduli ring. -/
theorem e3Rel_map_eq_zero : e3Map R (e3Rel R) = 0 := by
  show (algebraMap (E3Quotient R) (E3ModuliRing R))
    (Ideal.Quotient.mk _ (e3Rel R)) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr
    (Ideal.subset_span (Set.mem_singleton _)), map_zero]

/-! ### Stage-D: functoriality of the `ℰ₃` moduli ring in the coefficient ring -/

section StageD

open MvPolynomial in
/-- **(Stage D-1)** Functoriality of the flex-locus quotient in the coefficient ring. -/
noncomputable def e3QuotientMapRing {R R' : CommRingCat.{u}} (f : R ⟶ R') :
    E3Quotient R →+* E3Quotient R' :=
  Ideal.Quotient.lift _
    ((Ideal.Quotient.mk (Ideal.span {e3Rel R'})).comp (MvPolynomial.map f.hom))
    (by
      intro a ha
      rw [Ideal.mem_span_singleton] at ha
      obtain ⟨c, rfl⟩ := ha
      rw [RingHom.comp_apply, map_mul]
      rw [show MvPolynomial.map f.hom (e3Rel R) = e3Rel R' from by
        simp only [e3Rel, map_sub, map_pow, map_add, MvPolynomial.map_X]]
      have hz : (Ideal.Quotient.mk (Ideal.span {e3Rel R'})) (e3Rel R') = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
      rw [map_mul]
      exact mul_eq_zero_of_left hz _)

open MvPolynomial in
theorem e3QuotientMapRing_mk {R R' : CommRingCat.{u}} (f : R ⟶ R')
    (a : MvPolynomial (Fin 2) R) :
    e3QuotientMapRing f (Ideal.Quotient.mk _ a) =
      Ideal.Quotient.mk _ (MvPolynomial.map f.hom a) :=
  Ideal.Quotient.lift_mk _ _ _

open MvPolynomial in
theorem e3QuotientMapRing_delta {R R' : CommRingCat.{u}} (f : R ⟶ R') :
    e3QuotientMapRing f (e3Delta R) = e3Delta R' := by
  rw [e3Delta, e3QuotientMapRing_mk]
  congr 1
  simp only [e3A₁Poly, e3A₃Poly, map_mul, map_sub, map_pow, map_add, map_neg,
    map_ofNat, MvPolynomial.map_X, map_one]

/-- **(Stage D-1)** Functoriality of the `ℰ₃` moduli ring in the coefficient ring. -/
noncomputable def e3ModuliRingMap {R R' : CommRingCat.{u}} (f : R ⟶ R') :
    E3ModuliRing R →+* E3ModuliRing R' :=
  IsLocalization.Away.lift (e3Delta R)
    (g := (algebraMap (E3Quotient R') (E3ModuliRing R')).comp (e3QuotientMapRing f))
    (by
      rw [RingHom.comp_apply, e3QuotientMapRing_delta]
      exact IsLocalization.Away.algebraMap_isUnit (S := E3ModuliRing R') (e3Delta R'))

open MvPolynomial in
theorem e3ModuliRingMap_algebraMap {R R' : CommRingCat.{u}} (f : R ⟶ R')
    (a : E3Quotient R) :
    e3ModuliRingMap f (algebraMap (E3Quotient R) (E3ModuliRing R) a) =
      algebraMap (E3Quotient R') (E3ModuliRing R') (e3QuotientMapRing f a) := by
  rw [e3ModuliRingMap, IsLocalization.Away.lift_eq]
  rfl

open MvPolynomial in
theorem e3ModuliRingMap_gamma {R R' : CommRingCat.{u}} (f : R ⟶ R') :
    e3ModuliRingMap f (e3Gamma R) = e3Gamma R' := by
  rw [e3Gamma, e3ModuliRingMap_algebraMap, e3QuotientMapRing_mk]
  congr 2
  exact MvPolynomial.map_X _ _

open MvPolynomial in
theorem e3ModuliRingMap_beta {R R' : CommRingCat.{u}} (f : R ⟶ R') :
    e3ModuliRingMap f (e3Beta R) = e3Beta R' := by
  rw [e3Beta, e3ModuliRingMap_algebraMap, e3QuotientMapRing_mk]
  congr 2
  exact MvPolynomial.map_X _ _

/-- **(Stage D-1)** The universal curve is functorial: mapping the coefficients along
`e3ModuliRingMap` recovers the primed universal curve. -/
theorem universalE3_ringMap {R R' : CommRingCat.{u}} (f : R ⟶ R') :
    (universalE3 R).map (e3ModuliRingMap f) = universalE3 R' := by
  have hγ := e3ModuliRingMap_gamma f
  have hβ := e3ModuliRingMap_beta f
  ext
  · show e3ModuliRingMap f (3 * e3Gamma R - 1) = 3 * e3Gamma R' - 1
    rw [map_sub, map_mul, map_ofNat, map_one, hγ]
  · show e3ModuliRingMap f 0 = 0
    exact map_zero _
  · show e3ModuliRingMap f (-3 * e3Gamma R ^ 2 - e3Beta R - 3 * e3Beta R * e3Gamma R)
      = -3 * e3Gamma R' ^ 2 - e3Beta R' - 3 * e3Beta R' * e3Gamma R'
    simp only [map_sub, map_mul, map_neg, map_ofNat, map_pow, hγ, hβ]
  · show e3ModuliRingMap f 0 = 0
    exact map_zero _
  · show e3ModuliRingMap f 0 = 0
    exact map_zero _

end StageD

/-- **(B2-fix v10.256)** The universal `Q = (γ, β+γ)` is a `3`-torsion point at the
coordinate level: `x(Q) = γ` roots the `3`-division cofactor `3x³ + a₁²x² + 3a₁a₃x + 3a₃²`.
This is now provable — it was *false* pre-B2 on the (now-excluded) `γ = 0` component. The
flex relation `γ(3β²+3βγ+γ²) = 0` (the moduli relation `β³=(β+γ)³`) together with `γ` a unit
(`isUnit_e3Gamma`) forces `3β²+3βγ+γ² = 0`, and `hcubic = (3γ+1)²(3β²+3βγ+γ²) = 0`. This is
the universal instance of the `hcubic` hypothesis of `isE3Datum_of_flexCharts`. -/
theorem universalE3_hcubic :
    3 * e3Gamma R ^ 3 + (universalE3 R).a₁ ^ 2 * e3Gamma R ^ 2
      + 3 * (universalE3 R).a₁ * (universalE3 R).a₃ * e3Gamma R
      + 3 * (universalE3 R).a₃ ^ 2 = 0 := by
  have hrel : e3Map R (X 0 ^ 3 - (X 0 + X 1) ^ 3) = 0 := e3Rel_map_eq_zero R
  rw [map_sub, map_pow, map_pow, map_add] at hrel
  have hrel' : e3Beta R ^ 3 - (e3Beta R + e3Gamma R) ^ 3 = 0 := hrel
  have hflex : e3Gamma R * (3 * e3Beta R ^ 2 + 3 * e3Beta R * e3Gamma R + e3Gamma R ^ 2)
      = 0 := by linear_combination -hrel'
  have hS : 3 * e3Beta R ^ 2 + 3 * e3Beta R * e3Gamma R + e3Gamma R ^ 2 = 0 :=
    (isUnit_e3Gamma R).mul_right_eq_zero.mp hflex
  show 3 * e3Gamma R ^ 3 + (3 * e3Gamma R - 1) ^ 2 * e3Gamma R ^ 2
      + 3 * (3 * e3Gamma R - 1)
        * (-3 * e3Gamma R ^ 2 - e3Beta R - 3 * e3Beta R * e3Gamma R) * e3Gamma R
      + 3 * (-3 * e3Gamma R ^ 2 - e3Beta R - 3 * e3Beta R * e3Gamma R) ^ 2 = 0
  linear_combination (3 * e3Gamma R + 1) ^ 2 * hS

/-- **([T-E15-NORM] the non-`2`-torsion certificate ★)** `den := β + γ − 3βγ` is a unit in
the `ℰ₃` moduli ring — the universal marked `Q = (γ, β+γ)` is nowhere `2`-torsion
(`y(Q) ≠ negY(Q)` on every fibre), which is what the Stage-A doubling computation
(`three_zsmul_some_e3Q`) consumes. Certificate (CAS-cofactor):
`D·γ³ = A·den + B·(γ·S)` with `D = a₁³−27a₃` (a unit), `γ·S = 0` (the flex relation),
`A = 27βγ³+36βγ²+3βγ+27γ⁴+18γ³`, `B = 27γ³+27γ²−9γ−1` — so `A·den = D·γ³` is a unit. -/
theorem isUnit_e3Den :
    IsUnit (e3Beta R + e3Gamma R - 3 * e3Beta R * e3Gamma R) := by
  have hrel : e3Map R (X 0 ^ 3 - (X 0 + X 1) ^ 3) = 0 := e3Rel_map_eq_zero R
  rw [map_sub, map_pow, map_pow, map_add] at hrel
  have hrel' : e3Beta R ^ 3 - (e3Beta R + e3Gamma R) ^ 3 = 0 := hrel
  have hflex : e3Gamma R * (3 * e3Beta R ^ 2 + 3 * e3Beta R * e3Gamma R
      + e3Gamma R ^ 2) = 0 := by
    linear_combination -hrel'
  have hDunit : IsUnit ((universalE3 R).a₁ ^ 3 - 27 * (universalE3 R).a₃) := by
    have h := IsLocalization.Away.algebraMap_isUnit (S := E3ModuliRing R) (e3Delta R)
    rw [e3Delta_map] at h
    exact isUnit_of_mul_isUnit_left (isUnit_of_mul_isUnit_left h)
  have hkey : ((universalE3 R).a₁ ^ 3 - 27 * (universalE3 R).a₃) * e3Gamma R ^ 3
      = (27 * e3Beta R * e3Gamma R ^ 3 + 36 * e3Beta R * e3Gamma R ^ 2
          + 3 * e3Beta R * e3Gamma R + 27 * e3Gamma R ^ 4 + 18 * e3Gamma R ^ 3)
        * (e3Beta R + e3Gamma R - 3 * e3Beta R * e3Gamma R) := by
    show ((3 * e3Gamma R - 1) ^ 3
        - 27 * (-3 * e3Gamma R ^ 2 - e3Beta R - 3 * e3Beta R * e3Gamma R))
        * e3Gamma R ^ 3 = _
    linear_combination (27 * e3Gamma R ^ 3 + 27 * e3Gamma R ^ 2 - 9 * e3Gamma R - 1)
      * hflex
  exact isUnit_of_mul_isUnit_right
    (hkey ▸ hDunit.mul ((isUnit_e3Gamma R).pow 3))

/-- **(T-E15a)** `(0, 0)` lies on the universal curve (`a₆ = 0`). -/
theorem universalE3_equation_zero :
    (universalE3 R).toAffine.Equation 0 0 := by
  rw [WeierstrassCurve.Affine.equation_iff]
  show (0 : E3ModuliRing R) ^ 2 + (universalE3 R).a₁ * 0 * 0 +
    (universalE3 R).a₃ * 0 =
    0 ^ 3 + (universalE3 R).a₂ * 0 ^ 2 + (universalE3 R).a₄ * 0 + (universalE3 R).a₆
  show (0 : E3ModuliRing R) ^ 2 + (universalE3 R).a₁ * 0 * 0 +
    (universalE3 R).a₃ * 0 = 0 ^ 3 + 0 * 0 ^ 2 + 0 * 0 + 0
  ring

/-- **(T-E15a ★)** `Q = (γ, β + γ)` lies on the universal curve: the affine equation
at `(γ, β+γ)` is EXACTLY the negative of the flex relation `β³ − (β+γ)³`. -/
theorem universalE3_equation_Q :
    (universalE3 R).toAffine.Equation (e3Gamma R) (e3Beta R + e3Gamma R) := by
  rw [WeierstrassCurve.Affine.equation_iff]
  have hrel : e3Map R (X 0 ^ 3 - (X 0 + X 1) ^ 3) = 0 := e3Rel_map_eq_zero R
  rw [map_sub, map_pow, map_pow, map_add] at hrel
  show (e3Beta R + e3Gamma R) ^ 2 +
      (universalE3 R).a₁ * e3Gamma R * (e3Beta R + e3Gamma R) +
      (universalE3 R).a₃ * (e3Beta R + e3Gamma R) =
    e3Gamma R ^ 3 + (universalE3 R).a₂ * e3Gamma R ^ 2 +
      (universalE3 R).a₄ * e3Gamma R + (universalE3 R).a₆
  show (e3Beta R + e3Gamma R) ^ 2 +
      (3 * e3Gamma R - 1) * e3Gamma R * (e3Beta R + e3Gamma R) +
      (-3 * e3Gamma R ^ 2 - e3Beta R - 3 * e3Beta R * e3Gamma R) *
        (e3Beta R + e3Gamma R) =
    e3Gamma R ^ 3 + 0 * e3Gamma R ^ 2 + 0 * e3Gamma R + 0
  have hrel' : (e3Beta R) ^ 3 - (e3Beta R + e3Gamma R) ^ 3 = 0 := hrel
  linear_combination hrel'

/-- **(T-E15a)** The universal `Ell/R`-object `ℰ₃`. -/
def universalE3Obj : EllObj R where
  base := Spec (CommRingCat.of (E3ModuliRing R))
  structMap := Spec.map (CommRingCat.ofHom (algebraMap R (E3ModuliRing R)))
  curve := modelEllipticCurve (universalE3 R)

/-- **(T-E15a)** The universally marked `P = (0, 0)`. -/
def universalE3P : (universalE3Obj R).curve.Section :=
  ⟨projModelAffineSection (universalE3 R) 0 0 (universalE3_equation_zero R),
    projModelAffineSection_projModelπ _ _ _ _⟩

/-- **(T-E15a)** The universally marked `Q = (γ, β + γ)`. -/
def universalE3Q : (universalE3Obj R).curve.Section :=
  ⟨projModelAffineSection (universalE3 R) (e3Gamma R) (e3Beta R + e3Gamma R)
      (universalE3_equation_Q R),
    projModelAffineSection_projModelπ _ _ _ _⟩

/-! ### The section-level killing ([T-E15-NORM] hL-killing): Stages A+B+C assemble -/

open WeierstrassCurve in
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1600000 in
/-- **([T-E15-NORM] the killing engine ★★)** Over a reduced universal base, a marked
affine-point section of the universal `ℰ₃` curve whose evaluation at every field point
is `3`-torsion (in mathlib's affine point group) is killed by `3` at the section level:
the Stage-B fibre evaluation + additive dictionary convert the fibre hypothesis to the
morphism-level killing at each field point, and the Stage-B collision principle
(separatedness + reducedness) glues. -/
theorem universalE3_section_killing
    [IsReduced (Spec (CommRingCat.of (E3ModuliRing R)))]
    (p q : E3ModuliRing R) (hpq : (universalE3 R).toAffine.Equation p q)
    (hfield : ∀ (K : Type u) [Field K] [DecidableEq K] [Algebra (E3ModuliRing R) K]
      (hns : ((universalE3 R).baseChange K).toAffine.Nonsingular
        (algebraMap (E3ModuliRing R) K p) (algebraMap (E3ModuliRing R) K q)),
      (3 : ℤ) • (WeierstrassCurve.Affine.Point.some _ _ hns :
        ((universalE3 R).baseChange K).toAffine.Point) = 0) :
    (3 : ℤ) • (⟨projModelAffineSection (universalE3 R) p q hpq,
        projModelAffineSection_projModelπ _ _ _ _⟩ :
      (universalE3Obj R).curve.Section) = 0 := by
  refine nsmul_section_eq_zero_of_forall_specPoint (universalE3 R) 3 _ ?_
  intro K _ pt
  letI : DecidableEq K := Classical.decEq K
  letI : Algebra (E3ModuliRing R) K := (Spec.preimage pt).hom.toAlgebra
  have halg : CommRingCat.ofHom (algebraMap (E3ModuliRing R) K) = Spec.preimage pt :=
    rfl
  have hpt : pt = Spec.map (CommRingCat.ofHom (algebraMap (E3ModuliRing R) K)) := by
    rw [halg, Spec.map_preimage]
  -- the evaluated point, as a `Point` of the model over the algebra map
  set σK : (modelEllipticCurve (universalE3 R)).Point
      (Spec.map (CommRingCat.ofHom (algebraMap (E3ModuliRing R) K))) :=
    ⟨(affineSectionSpecPoint (universalE3 R) K p q hpq).1,
      (affineSectionSpecPoint (universalE3 R) K p q hpq).2⟩ with hσK
  -- nonsingularity of the evaluated coordinates
  haveI : (((universalE3 R).baseChange K)).IsElliptic :=
    inferInstanceAs (((universalE3 R).map (algebraMap (E3ModuliRing R) K)).IsElliptic)
  have hns : ((universalE3 R).baseChange K).toAffine.Nonsingular
      (algebraMap (E3ModuliRing R) K p) (algebraMap (E3ModuliRing R) K q) :=
    WeierstrassCurve.Affine.equation_iff_nonsingular.mp
      (WeierstrassCurve.Affine.Equation.map _ hpq)
  -- the point-level killing, via the additive dictionary + the field hypothesis
  have hkill : (3 : ℤ) • σK = 0 := by
    apply (modelPointAddEquiv (universalE3 R)).injective
    rw [map_zsmul, map_zero]
    have hval : modelPointAddEquiv (universalE3 R) σK =
        WeierstrassCurve.Affine.Point.some _ _ hns := by
      show projModelPointsEquiv (universalE3 R) K
        (affineSectionSpecPoint (universalE3 R) K p q hpq) = _
      exact projModelPointsEquiv_affineSectionSpecPoint (universalE3 R) p q hpq hns
    rw [hval]
    exact hfield K hns
  -- back to the morphism level
  have hmor := (EllipticCurve.smul_eq_zero_iff_comp_mulByHom
    (modelEllipticCurve (universalE3 R))
    (Spec.map (CommRingCat.ofHom (algebraMap (E3ModuliRing R) K))) 3 σK).mp hkill
  rw [hpt]
  rw [show σK.1 = Spec.map (CommRingCat.ofHom (algebraMap (E3ModuliRing R) K)) ≫
      projModelAffineSection (universalE3 R) p q hpq from rfl] at hmor
  rw [← Category.assoc]
  exact hmor

open LocalPresentation in
set_option backward.isDefEq.respectTransparency false in
/-- **(T-E15a stage 3 ★)** The tautological presentation marks the universal `P` at
`(0, 0)` (the banked generic universal marking, instantiated at `ℰ₃`). -/
theorem tautPresentation_marksAt_e3P :
    (tautPresentation (universalE3 R)).MarksAt
      (universalE3P R).2
      ((Scheme.ΓSpecIso (CommRingCat.of (E3ModuliRing R))).inv.hom 0)
      ((Scheme.ΓSpecIso (CommRingCat.of (E3ModuliRing R))).inv.hom 0) :=
  tautPresentation_marksAt (universalE3 R) 0 0 (universalE3_equation_zero R)

open LocalPresentation in
set_option backward.isDefEq.respectTransparency false in
/-- **(T-E15a stage 3 ★)** The tautological presentation marks the universal `Q` at
`(γ, β + γ)`. -/
theorem tautPresentation_marksAt_e3Q :
    (tautPresentation (universalE3 R)).MarksAt
      (universalE3Q R).2
      ((Scheme.ΓSpecIso (CommRingCat.of (E3ModuliRing R))).inv.hom (e3Gamma R))
      ((Scheme.ΓSpecIso (CommRingCat.of (E3ModuliRing R))).inv.hom
        (e3Beta R + e3Gamma R)) :=
  tautPresentation_marksAt (universalE3 R) (e3Gamma R) (e3Beta R + e3Gamma R)
    (universalE3_equation_Q R)

/-- **(T-E15a)** The `[3]`-normal-form shape: `a₂ = a₄ = a₆ = 0` with `a₁, a₃` the
`ℰ₃`-parameter expressions at `(β, γ)`-values. A chart curve of this shape with the
markings is a level-3 witness (KM Ex. 2.2.2: the flex-at-origin normal form). -/
def IsE3Form {A : Type u} [CommRing A] (W : WeierstrassCurve A) (β γ : A) : Prop :=
  W.a₁ = 3 * γ - 1 ∧ W.a₂ = 0 ∧ W.a₃ = -3 * γ ^ 2 - β - 3 * β * γ ∧
    W.a₄ = 0 ∧ W.a₆ = 0

/-- The universal curve is of `ℰ₃`-form at the universal parameters. -/
theorem universalE3_isE3Form :
    IsE3Form (universalE3 R) (e3Beta R) (e3Gamma R) :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- **(T-E15a)** `IsE3Form` is functorial under a ring hom: the `ℰ₃`-form shape (five
coefficient equations) is preserved by `WeierstrassCurve.map`. -/
theorem IsE3Form.map {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B)
    {W : WeierstrassCurve A} {β γ : A} (h : IsE3Form W β γ) :
    IsE3Form (W.map f) (f β) (f γ) := by
  obtain ⟨ha₁, ha₂, ha₃, ha₄, ha₆⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [WeierstrassCurve.map_a₁, ha₁]
    simp only [map_sub, map_mul, map_ofNat, map_one]
  · rw [WeierstrassCurve.map_a₂, ha₂, map_zero]
  · rw [WeierstrassCurve.map_a₃, ha₃]
    simp only [map_sub, map_neg, map_mul, map_ofNat, map_pow]
  · rw [WeierstrassCurve.map_a₄, ha₄, map_zero]
  · rw [WeierstrassCurve.map_a₆, ha₆, map_zero]

open WeierstrassCurve in
/-- **([T-E15-NORM] the Q-normalization certificate ★★)** The `ℰ₃`-form emerges from a
flex normal form by *pure scaling*. Given `W` already in flex shape (`a₂ = a₄ = a₆ = 0`,
supplied by `ofTwiceNeZero` at an order-`3` point `P` — see
`EllipticCurve/E3NormalForm.lean`), a marked point `(p, q)` (the second generator `Q`),
and a **unit** `u` satisfying

* `hurel : u² + a₁·u = 3·p` — the scaling relation, which is exactly `a₁' = 3γ − 1`, and
* `hsheet : B·u + A = 0` — the sheet-selecting relation, where
  `A = −3a₁²p² − 3a₁a₃p − 3a₁pq − 9p³`, `B = a₁³p + a₁²a₃ + a₁²q + 6a₁p² + 3a₃p + 6pq`,

the scaled curve `⟨u,0,0,0⟩ • W` is of `ℰ₃`-form with `γ = p·u⁻²`, `β = q·u⁻³ − p·u⁻²`.

The content is that no `√-3` / Weil-pairing datum is needed: the correct scaling
`u = −A/B` is a *rational function of the coordinates*, so the level-3 normalization is
Zariski-local. Only `a₁' = 3γ−1` (`hurel`) and `a₃' = −3γ²−β−3βγ` (`hsheet`) are
non-trivial; `a₂', a₄', a₆'` vanish because `W` is already in flex shape. -/
theorem isE3Form_of_scaling {A : Type u} [CommRing A] {W : WeierstrassCurve A}
    (ha₂ : W.a₂ = 0) (ha₄ : W.a₄ = 0) (ha₆ : W.a₆ = 0)
    (p q : A) (u : Aˣ)
    (hurel : (u : A) ^ 2 + W.a₁ * (u : A) = 3 * p)
    (hsheet : (W.a₁ ^ 3 * p + W.a₁ ^ 2 * W.a₃ + W.a₁ ^ 2 * q + 6 * W.a₁ * p ^ 2
                + 3 * W.a₃ * p + 6 * p * q) * (u : A)
              + (-3 * W.a₁ ^ 2 * p ^ 2 - 3 * W.a₁ * W.a₃ * p - 3 * W.a₁ * p * q
                - 9 * p ^ 3) = 0) :
    IsE3Form ((⟨u, 0, 0, 0⟩ : VariableChange A) • W)
      (q * ((u⁻¹ : Aˣ) : A) ^ 3 - p * ((u⁻¹ : Aˣ) : A) ^ 2)
      (p * ((u⁻¹ : Aˣ) : A) ^ 2) := by
  have hv : ((u⁻¹ : Aˣ) : A) * (u : A) = 1 := u.inv_mul
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [variableChange_a₁]
    linear_combination ((u⁻¹ : Aˣ) : A) ^ 2 * hurel
      - (W.a₁ * ((u⁻¹ : Aˣ) : A) + 1 + ((u⁻¹ : Aˣ) : A) * (u : A)) * hv
  · rw [variableChange_a₂, ha₂]; ring
  · have hmul : (u : A) * ((W.a₃ + q) * (u : A) ^ 2 - p * (u : A) ^ 3 + 3 * p * q) = 0 := by
      linear_combination (-W.a₁ ^ 2 * p - W.a₁ * W.a₃ + W.a₁ * p * (u : A) - W.a₁ * q
        + W.a₃ * (u : A) - 3 * p ^ 2 - p * (u : A) ^ 2 + q * (u : A)) * hurel + hsheet
    have hE5 : (W.a₃ + q) * (u : A) ^ 2 - p * (u : A) ^ 3 + 3 * p * q = 0 :=
      (u.isUnit.mul_right_eq_zero).mp hmul
    rw [variableChange_a₃]
    linear_combination ((u⁻¹ : Aˣ) : A) ^ 5 * hE5
      + (-W.a₃ * (u : A) * ((u⁻¹ : Aˣ) : A) ^ 4 - W.a₃ * ((u⁻¹ : Aˣ) : A) ^ 3
        + p * (u : A) ^ 2 * ((u⁻¹ : Aˣ) : A) ^ 4 + p * (u : A) * ((u⁻¹ : Aˣ) : A) ^ 3
        + p * ((u⁻¹ : Aˣ) : A) ^ 2 - q * (u : A) * ((u⁻¹ : Aˣ) : A) ^ 4
        - q * ((u⁻¹ : Aˣ) : A) ^ 3) * hv
  · rw [variableChange_a₄, ha₄]; ring
  · rw [variableChange_a₆, ha₆]; ring

open WeierstrassCurve in
/-- **([T-E15-NORM] scaling existence on the `B`-unit locus ★★)** On the open where the
`ℰ₃`-denominator `B` is a unit, a flex-NF curve `W` (`a₂=a₄=a₆=0`) with a marked
`3`-torsion point `(p, q)` admits the `ℰ₃`-normalization. The scaling `u = −A·B⁻¹` is a
unit — `p = x(Q)` is a unit from the `3`-division relation `hcubic`
(`p·(3p²+a₁²p+3a₁a₃) = −3a₃²`), so `3p` is a unit and `u·(u+a₁)=3p` forces `u` a unit —
and it satisfies both `hurel` (via `A²−a₁AB−3pB² = 0`, a `linear_combination` of `hcurve`
and `hcubic`) and `hsheet` (by construction). No `√-3` / Weil pairing: `u` is rational
in the coordinates. -/
theorem isE3Form_of_threeTorsion {A : Type u} [CommRing A] {W : WeierstrassCurve A}
    (ha₂ : W.a₂ = 0) (ha₄ : W.a₄ = 0) (ha₆ : W.a₆ = 0)
    (p q : A)
    (hcurve : q ^ 2 + W.a₁ * p * q + W.a₃ * q = p ^ 3)
    (hcubic : 3 * p ^ 3 + W.a₁ ^ 2 * p ^ 2 + 3 * W.a₁ * W.a₃ * p + 3 * W.a₃ ^ 2 = 0)
    (ha₃ : IsUnit W.a₃) (h3 : IsUnit (3 : A))
    (hB : IsUnit (W.a₁ ^ 3 * p + W.a₁ ^ 2 * W.a₃ + W.a₁ ^ 2 * q + 6 * W.a₁ * p ^ 2
            + 3 * W.a₃ * p + 6 * p * q)) :
    ∃ u : Aˣ, IsE3Form ((⟨u, 0, 0, 0⟩ : VariableChange A) • W)
      (q * ((u⁻¹ : Aˣ) : A) ^ 3 - p * ((u⁻¹ : Aˣ) : A) ^ 2)
      (p * ((u⁻¹ : Aˣ) : A) ^ 2) := by
  -- `p = x(Q)` is a unit
  have hp : IsUnit p := by
    apply isUnit_of_mul_isUnit_left (y := 3 * p ^ 2 + W.a₁ ^ 2 * p + 3 * W.a₁ * W.a₃)
    have hpX : p * (3 * p ^ 2 + W.a₁ ^ 2 * p + 3 * W.a₁ * W.a₃) = -(3 * W.a₃ ^ 2) := by
      linear_combination hcubic
    rw [hpX]; exact (h3.mul (ha₃.pow 2)).neg
  -- the ℰ₃ numerator/denominator and the scaling `w = −A·B⁻¹`
  obtain ⟨Bu, hBu⟩ := hB
  set Aex : A := -3 * W.a₁ ^ 2 * p ^ 2 - 3 * W.a₁ * W.a₃ * p - 3 * W.a₁ * p * q - 9 * p ^ 3
    with hAex
  set Bex : A := W.a₁ ^ 3 * p + W.a₁ ^ 2 * W.a₃ + W.a₁ ^ 2 * q + 6 * W.a₁ * p ^ 2
    + 3 * W.a₃ * p + 6 * p * q with hBex
  have hBinv : Bex * (↑Bu⁻¹ : A) = 1 := by rw [← hBu]; exact Bu.mul_inv
  set w : A := -Aex * (↑Bu⁻¹ : A) with hw
  -- `A² − a₁AB − 3pB² = 0`
  have hAB : Aex ^ 2 - W.a₁ * Aex * Bex - 3 * p * Bex ^ 2 = 0 := by
    rw [hAex, hBex]
    linear_combination (-9 * p ^ 2 * (W.a₁ ^ 2 + 12 * p)) * hcurve + (-9 * p ^ 3) * hcubic
  -- `hurel : w² + a₁w = 3p`
  have hwurel : w ^ 2 + W.a₁ * w = 3 * p := by
    have key : w ^ 2 + W.a₁ * w = (Aex ^ 2 - W.a₁ * Aex * Bex) * (↑Bu⁻¹ : A) ^ 2 := by
      rw [hw]; linear_combination (W.a₁ * Aex * (↑Bu⁻¹ : A)) * hBinv
    rw [key, show Aex ^ 2 - W.a₁ * Aex * Bex = 3 * p * Bex ^ 2 by linear_combination hAB]
    linear_combination (3 * p * (Bex * (↑Bu⁻¹ : A) + 1)) * hBinv
  -- `w` is a unit
  have hwu : IsUnit w := by
    apply isUnit_of_mul_isUnit_left (y := w + W.a₁)
    rw [show w * (w + W.a₁) = 3 * p by linear_combination hwurel]; exact h3.mul hp
  -- `hsheet : B·w + A = 0`
  have hsheet : Bex * w + Aex = 0 := by rw [hw]; linear_combination (-Aex) * hBinv
  -- assemble
  refine ⟨hwu.unit, ?_⟩
  have hunit : (↑hwu.unit : A) = w := hwu.unit_spec
  exact isE3Form_of_scaling ha₂ ha₄ ha₆ p q hwu.unit
    (by rw [hunit]; exact hwurel)
    (by rw [hunit, ← hBex, ← hAex]; exact hsheet)

open LocalPresentation in
set_option backward.isDefEq.respectTransparency false in
/-- **([T-E15-NORM] marking transport under `ofVC` ★)** If a presentation `P` marks a
section `σ` at the `C`-preimage `(u²p+r, u³q+su²p+t)`, then the `C`-twisted presentation
`P.ofVC C` marks `σ` at `(p, q)`. For the `ℰ₃`-scaling `C = ⟨u,0,0,0⟩` this sends a
`Q`-marking `(p₀, q₀)` to `(p₀·u⁻², q₀·u⁻³) = (γ, β+γ)` — exactly the `ℰ₃`-datum marking.
Built on `projModelVCIso_affineSection` (the VC-iso ↔ affine-section compatibility). -/
theorem LocalPresentation.MarksAt.ofVC {S : Scheme.{u}} {G : EllipticCurveGeom S}
    {V : S.affineOpens} (P : LocalPresentation G V)
    {σ : S ⟶ G.E} {hσ : σ ≫ G.π = 𝟙 S} (C : WeierstrassCurve.VariableChange Γ(S, V.1))
    {p q : Γ(S, V.1)} (hEq : (C • P.W).toAffine.Equation p q)
    (hM : P.MarksAt hσ ((C.u : Γ(S, V.1)) ^ 2 * p + C.r)
      ((C.u : Γ(S, V.1)) ^ 3 * q + C.s * (C.u : Γ(S, V.1)) ^ 2 * p + C.t)) :
    (P.ofVC C).MarksAt hσ p q := by
  obtain ⟨h', hMeq⟩ := hM
  refine ⟨hEq, ?_⟩
  have he : (P.ofVC C).e.hom = P.e.hom ≫ (projModelVCIso C P.W).inv := by
    show (P.e ≪≫ (projModelVCIso C P.W).symm).hom = _
    rw [Iso.trans_hom, Iso.symm_hom]
  rw [he, show (V.2.isoSpec.inv ≫ sectionLift G hσ V) ≫ P.e.hom ≫ (projModelVCIso C P.W).inv
      = ((V.2.isoSpec.inv ≫ sectionLift G hσ V) ≫ P.e.hom) ≫ (projModelVCIso C P.W).inv from
    (Category.assoc _ _ _).symm, hMeq, Iso.comp_inv_eq]
  exact (projModelVCIso_affineSection C P.W p q hEq h').symm

open LocalPresentation WeierstrassCurve in
set_option backward.isDefEq.respectTransparency false in
/-- **([T-E15-NORM] the local `ℰ₃`-datum ★★★, modulo the torsion→coordinate bridges)** From a
**flex-normal-form chart** `P₀` (`a₂=a₄=a₆=0`) marking the order-`3` section `P` at the origin and
the second generator `Q` at `(p, q)`, together with the `3`-torsion coordinate relation `hcubic`
(the bridge output of `3 • Q = 0`) and the unit conditions, the twisted chart `P₀.ofVC ⟨u,0,0,0⟩`
is a genuine `ℰ₃`-form presentation marking `P` at `(0,0)` and `Q` at `(γ, β+γ)`. This composes the
whole `ℰ₃`-normalization at a single point: `isE3Form_of_threeTorsion` (the scaling `u`) with
`MarksAt.ofVC` (the two markings) and `equation_smul` (the `Q`-equation). Everything is keystone-FREE
— the only inputs from the group law are `hMP`/`hMQ` (the markings, from the section data) and
`hcubic` (the `3`-torsion coordinate relation). Assembling these charts over a cover of the base
(and producing the flex-NF chart from `3 • P = 0 ⟹ μ_P = 0`) yields `IsE3Datum`. -/
theorem isE3Chart {S : Scheme.{u}} {G : EllipticCurveGeom S} {V : S.affineOpens}
    (P₀ : LocalPresentation G V) (ha₂ : P₀.W.a₂ = 0) (ha₄ : P₀.W.a₄ = 0) (ha₆ : P₀.W.a₆ = 0)
    {σP σQ : S ⟶ G.E} {hσP : σP ≫ G.π = 𝟙 S} {hσQ : σQ ≫ G.π = 𝟙 S}
    (hMP : P₀.MarksAt hσP 0 0) {p q : Γ(S, V.1)} (hMQ : P₀.MarksAt hσQ p q)
    (hcubic : 3 * p ^ 3 + P₀.W.a₁ ^ 2 * p ^ 2 + 3 * P₀.W.a₁ * P₀.W.a₃ * p + 3 * P₀.W.a₃ ^ 2 = 0)
    (ha₃ : IsUnit P₀.W.a₃) (h3 : IsUnit (3 : Γ(S, V.1)))
    (hB : IsUnit (P₀.W.a₁ ^ 3 * p + P₀.W.a₁ ^ 2 * P₀.W.a₃ + P₀.W.a₁ ^ 2 * q + 6 * P₀.W.a₁ * p ^ 2
            + 3 * P₀.W.a₃ * p + 6 * p * q)) :
    ∃ (Pr : LocalPresentation G V) (β γ : Γ(S, V.1)),
      IsE3Form Pr.W β γ ∧ Pr.MarksAt hσP 0 0 ∧ Pr.MarksAt hσQ γ (β + γ) ∧ IsUnit γ := by
  obtain ⟨hcurveEq, -⟩ := id hMQ
  have hcurve : q ^ 2 + P₀.W.a₁ * p * q + P₀.W.a₃ * q = p ^ 3 := by
    have h := hcurveEq
    rw [Affine.equation_iff, ha₂, ha₄, ha₆] at h; linear_combination h
  have hp : IsUnit p := by
    apply isUnit_of_mul_isUnit_left
      (y := 3 * p ^ 2 + P₀.W.a₁ ^ 2 * p + 3 * P₀.W.a₁ * P₀.W.a₃)
    rw [show p * (3 * p ^ 2 + P₀.W.a₁ ^ 2 * p + 3 * P₀.W.a₁ * P₀.W.a₃)
        = -(3 * P₀.W.a₃ ^ 2) by linear_combination hcubic]
    exact (h3.mul (ha₃.pow 2)).neg
  obtain ⟨u, hE3⟩ := isE3Form_of_threeTorsion ha₂ ha₄ ha₆ p q hcurve hcubic ha₃ h3 hB
  have hmul : (↑u : Γ(S, V.1)) * ↑u⁻¹ = 1 := u.mul_inv
  set C : VariableChange Γ(S, V.1) := ⟨u, 0, 0, 0⟩ with hC
  refine ⟨P₀.ofVC C, q * (↑u⁻¹) ^ 3 - p * (↑u⁻¹) ^ 2, p * (↑u⁻¹) ^ 2, ?_, ?_, ?_,
    hp.mul (u⁻¹.isUnit.pow 2)⟩
  · show IsE3Form (C • P₀.W) _ _; exact hE3
  · have hEqP : (C • P₀.W).toAffine.Equation 0 0 := by
      rw [hC, Affine.equation_zero, variableChange_a₆]; simp [ha₆]
    have hMP' : P₀.MarksAt hσP ((↑C.u : Γ(S, V.1)) ^ 2 * 0 + C.r)
        ((↑C.u : Γ(S, V.1)) ^ 3 * 0 + C.s * (↑C.u : Γ(S, V.1)) ^ 2 * 0 + C.t) := by
      rw [hC]; simpa using hMP
    exact LocalPresentation.MarksAt.ofVC P₀ C hEqP hMP'
  · have hEqQ : (C • P₀.W).toAffine.Equation
        (p * (↑u⁻¹) ^ 2) ((q * (↑u⁻¹) ^ 3 - p * (↑u⁻¹) ^ 2) + p * (↑u⁻¹) ^ 2) := by
      have hkey := C.equation_smul P₀.W hcurveEq
      have h1 : C.vcX p = p * (↑u⁻¹) ^ 2 := by
        rw [hC]; dsimp only [WeierstrassCurve.VariableChange.vcX]; ring
      have h2 : C.vcY p q = (q * (↑u⁻¹) ^ 3 - p * (↑u⁻¹) ^ 2) + p * (↑u⁻¹) ^ 2 := by
        rw [hC]; dsimp only [WeierstrassCurve.VariableChange.vcY]; ring
      rw [h1, h2] at hkey; exact hkey
    have hMQ' : P₀.MarksAt hσQ
        ((↑C.u : Γ(S, V.1)) ^ 2 * (p * (↑u⁻¹) ^ 2) + C.r)
        ((↑C.u : Γ(S, V.1)) ^ 3 * ((q * (↑u⁻¹) ^ 3 - p * (↑u⁻¹) ^ 2) + p * (↑u⁻¹) ^ 2)
          + C.s * (↑C.u : Γ(S, V.1)) ^ 2 * (p * (↑u⁻¹) ^ 2) + C.t) := by
      rw [hC]
      rw [show (↑u : Γ(S, V.1)) ^ 2 * (p * (↑u⁻¹) ^ 2) + 0 = p by
            linear_combination (p * ((↑u : Γ(S, V.1)) * ↑u⁻¹ + 1)) * hmul,
        show (↑u : Γ(S, V.1)) ^ 3 * ((q * (↑u⁻¹) ^ 3 - p * (↑u⁻¹) ^ 2) + p * (↑u⁻¹) ^ 2)
            + 0 * (↑u : Γ(S, V.1)) ^ 2 * (p * (↑u⁻¹) ^ 2) + 0 = q by
          linear_combination (q * ((↑u : Γ(S, V.1)) * ↑u⁻¹) ^ 2 + q * ((↑u : Γ(S, V.1)) * ↑u⁻¹)
            + q) * hmul]
      exact hMQ
    exact LocalPresentation.MarksAt.ofVC P₀ C hEqQ hMQ'

open WeierstrassCurve in
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1600000 in
/-- **(T-E15a stage 4, the ring-level uniqueness certificate ★★)** A variable change
between marked `ℰ₃`-forms is trivial and identifies the parameters: given `r = t = 0`
(from the `P`-marking) and the `Q`-marking coordinate identities, the `a₁/a₄`-
transforms plus the flex relation force `w := u − 1` to satisfy `w(w²+w+1) = 0`, and
the `(a₁³−27a₃)`-unit kills the residual `ω`-branch: `u³·D·w = w(1−w³) = 0`. -/
theorem e3_vc_marked {A : Type u} [CommRing A] {C : VariableChange A}
    {W₁ W₂ : WeierstrassCurve A} {β₁ γ₁ β₂ γ₂ : A}
    (hW₁ : IsE3Form W₁ β₁ γ₁) (hW₂ : IsE3Form W₂ β₂ γ₂)
    (hC : C • W₂ = W₁) (hr : C.r = 0) (ht : C.t = 0)
    (hγ : (C.u : A) ^ 2 * γ₁ = γ₂)
    (hβγ : (C.u : A) ^ 3 * (β₁ + γ₁) + C.s * (C.u : A) ^ 2 * γ₁ = β₂ + γ₂)
    (hflex₁ : γ₁ * (3 * β₁ ^ 2 + 3 * β₁ * γ₁ + γ₁ ^ 2) = 0)
    (hflex₂ : γ₂ * (3 * β₂ ^ 2 + 3 * β₂ * γ₂ + γ₂ ^ 2) = 0)
    (ha₃ : IsUnit W₂.a₃)
    (hD : IsUnit (W₁.a₁ ^ 3 - 27 * W₁.a₃)) (h3 : IsUnit (3 : A)) :
    C = 1 ∧ γ₁ = γ₂ ∧ β₁ = β₂ := by
  obtain ⟨h₁a₁, h₁a₂, h₁a₃, h₁a₄, h₁a₆⟩ := hW₁
  obtain ⟨h₂a₁, h₂a₂, h₂a₃, h₂a₄, h₂a₆⟩ := hW₂
  have hu : (C.u : A) * ((C.u⁻¹ : Aˣ) : A) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel C.u, Units.val_one]
  have hcanc4 : (C.u : A) ^ 4 * ((C.u⁻¹ : Aˣ) : A) ^ 4 = 1 := by
    rw [← mul_pow, hu, one_pow]
  -- s = 0 from the a₄-transform (a₄ vanishes on both sides; a₃Q is a unit)
  have ha₄ := congrArg WeierstrassCurve.a₄ hC
  rw [variableChange_a₄, hr, ht, h₁a₄, h₂a₄, h₂a₃, h₂a₂, h₂a₁] at ha₄
  have hs : C.s = 0 := by
    have h'' : W₂.a₃ * C.s = 0 := by
      rw [h₂a₃]
      linear_combination (-(C.u : A) ^ 4) * ha₄ +
        (-(C.s * (-3 * γ₂ ^ 2 - β₂ - 3 * β₂ * γ₂))) * hcanc4
    exact (ha₃.mul_right_eq_zero).mp h''
  -- the a₁-transform gives [A]: `w := u − 1` acts as the scalar `3uγ₁`
  have ha₁ := congrArg WeierstrassCurve.a₁ hC
  rw [variableChange_a₁, hs, h₁a₁, h₂a₁] at ha₁
  set w : A := (C.u : A) - 1 with hwdef
  have h' : 3 * γ₂ - 1 = (C.u : A) * (3 * γ₁ - 1) := by
    linear_combination (C.u : A) * ha₁ - (3 * γ₂ - 1) * hu
  have hA : w * (3 * (C.u : A) * γ₁ + 1) = 0 := by
    rw [hwdef]; linear_combination h' + 3 * hγ
  -- flex 2, unit-reduced: divide off the `u²`
  have hgq2 : γ₁ * (3 * β₂ ^ 2 + 3 * β₂ * γ₂ + γ₂ ^ 2) = 0 := by
    refine ((C.u.isUnit.pow 2).mul_right_eq_zero).mp ?_
    rw [show (C.u : A) ^ 2 * (γ₁ * (3 * β₂ ^ 2 + 3 * β₂ * γ₂ + γ₂ ^ 2)) =
        ((C.u : A) ^ 2 * γ₁) * (3 * β₂ ^ 2 + 3 * β₂ * γ₂ + γ₂ ^ 2) by ring, hγ]
    exact hflex₂
  -- the substituted `β₂`
  have hβ₂ : β₂ = (C.u : A) ^ 3 * β₁ + (C.u : A) ^ 2 * γ₁ * w := by
    linear_combination -hβγ + ((C.u : A) + C.s - w) * hγ + γ₂ * hs - γ₂ * hwdef
  -- [G']: the scalar `9u²β₁` is pinned  (CAS-certified cofactors)
  have hGp : 9 * (C.u : A) ^ 2 * β₁ * w - 2 * w ^ 2 - w = 0 := by
    linear_combination (-81*β₁*β₂*(C.u : A)^2*γ₁ - 27*β₁*(C.u : A)^3*γ₁ - 81*β₁*(C.u : A)^2*γ₁*γ₂ + 9*β₁*(C.u : A)^2 + 27*β₁*(C.u : A)*γ₂ - 81*β₂*(C.u : A)*γ₁^2*w - 27*β₂*(C.u : A)*γ₁ + 27*β₂*γ₁*w - 27*(C.u : A)^3*γ₁^2 + 9*(C.u : A)^2*γ₁ - 81*(C.u : A)*γ₁^2*γ₂*w - 27*(C.u : A)*γ₁^2*γ₂ + 9*(C.u : A)*γ₁*γ₂ - 3*(C.u : A)*γ₁ - 2*(C.u : A) + 27*γ₁*γ₂*w + 9*γ₁*γ₂ - 3*γ₂ + 1) * hA + (-27*(C.u : A)^5) * hflex₁ + (81*γ₁*w + 27) * hgq2 + (-81*β₁*(C.u : A)^2*γ₁ - 243*β₂*γ₁^2*w - 81*β₂*γ₁ - 81*(C.u : A)^2*γ₁^2 - 243*γ₁^2*γ₂*w + 27*γ₁*w) * hβ₂ + (-81*β₁*β₂*(C.u : A) + 81*β₁*β₂*w + 81*β₁*β₂ + 27*β₁*(C.u : A)*w + 81*β₂*γ₁ + 27*(C.u : A)^3*γ₁^2 + 27*(C.u : A)*γ₁*γ₂ + 81*γ₁^2*γ₂*w - 27*γ₁*γ₂*w + 27*γ₁*w^2 + 9*γ₁*w - 3*w) * hγ + (81*β₁*β₂*γ₂ - 27*β₂*γ₁*w - 27*γ₁*γ₂^2 - 2*w) * hwdef
  -- the D-unit kill:  3·u³·D·w = 0  (CAS-certified cofactors)
  have hDp : W₁.a₁ ^ 3 - 27 * W₁.a₃ =
      (3 * γ₁ - 1) ^ 3 - 27 * (-3 * γ₁ ^ 2 - β₁ - 3 * β₁ * γ₁) := by
    rw [h₁a₁, h₁a₃]
  have hkill : (3 * (C.u : A) ^ 3 *
      ((3 * γ₁ - 1) ^ 3 - 27 * (-3 * γ₁ ^ 2 - β₁ - 3 * β₁ * γ₁))) * w = 0 := by
    linear_combination (-81*β₁^2*(C.u : A)^5 - 162*β₁^2*(C.u : A)^4*w + 324*β₁^2*(C.u : A)^4 - 81*β₁*(C.u : A)^5*γ₁ - 162*β₁*(C.u : A)^4*γ₁*w + 324*β₁*(C.u : A)^4*γ₁ + 27*β₁*(C.u : A)^4 + 54*β₁*(C.u : A)^3*w - 108*β₁*(C.u : A)^3 + 81*β₁*(C.u : A)^2 - 27*(C.u : A)^5*γ₁^2 - 54*(C.u : A)^4*γ₁^2*w + 108*(C.u : A)^4*γ₁^2 + 9*(C.u : A)^4*γ₁ + 18*(C.u : A)^3*γ₁*w - 36*(C.u : A)^3*γ₁ - 3*(C.u : A)^3 + 27*(C.u : A)^2*γ₁^2 + 54*(C.u : A)^2*γ₁ - 6*(C.u : A)^2*w + 21*(C.u : A)^2 - 9*(C.u : A)*γ₁ - 18*(C.u : A) + 3) * hA + (81*(C.u : A)^6*w + 162*(C.u : A)^5*w^2 - 324*(C.u : A)^5*w) * hflex₁ + (9*β₁*(C.u : A)^3 + 18*β₁*(C.u : A)^2*w - 36*β₁*(C.u : A)^2 - 3*(C.u : A)^2 - 4*(C.u : A)*w + 22*(C.u : A) + 4*w^2 - 6*w - 13) * hGp + (24*(C.u : A)*w + 8*w^3 - 16*w^2 - 16*w) * hwdef
  have hunit : IsUnit (3 * (C.u : A) ^ 3 *
      ((3 * γ₁ - 1) ^ 3 - 27 * (-3 * γ₁ ^ 2 - β₁ - 3 * β₁ * γ₁))) := by
    rw [← hDp]; exact (h3.mul (C.u.isUnit.pow 3)).mul hD
  have hwzero : w = 0 := (hunit.mul_right_eq_zero).mp hkill
  have hu1 : (C.u : A) = 1 := by
    have := hwzero; rw [hwdef] at this; linear_combination this
  have huu1 : C.u = 1 := Units.ext hu1
  refine ⟨?_, ?_, ?_⟩
  · ext
    · exact hu1
    · exact hr
    · exact hs
    · exact ht
  · rw [← hγ, hu1]; ring
  · rw [hβ₂, hu1, hwzero]; ring

open LocalPresentation WeierstrassCurve in
set_option backward.isDefEq.respectTransparency false in
open WeierstrassCurve in
/-- **([T-E15-NORM] Stage C applied)** Over a UFD coefficient ring with `3` invertible,
the universal `ℰ₃` base is reduced — this discharges the reducedness hypothesis of the
killing theorems (`three_zsmul_universalE3P/Q`): `E3Quotient` is reduced by the
squarefreeness of the flex relation (`isReduced_e3RelQuotient`), localization preserves
reducedness, and `Spec` of a reduced ring is reduced. -/
theorem isReduced_spec_e3ModuliRing (R : CommRingCat.{u}) [IsDomain R]
    [UniqueFactorizationMonoid R] (h3 : IsUnit (3 : R)) :
    AlgebraicGeometry.IsReduced (Spec (CommRingCat.of (E3ModuliRing R))) := by
  haveI : _root_.IsReduced (E3Quotient R) := isReduced_e3RelQuotient h3
  haveI : _root_.IsReduced (E3ModuliRing R) :=
    inferInstanceAs (_root_.IsReduced (Localization (Submonoid.powers (e3Delta R))))
  infer_instance

/-- **(T-E15a stage 5)** From `IsE3Form` + ellipticity: `a₃` and `a₁³−27a₃` are
units (the two factors of the discriminant `Δ = a₃³(a₁³−27a₃)`). -/
theorem e3form_units {A : Type u} [CommRing A] {W : WeierstrassCurve A} {β γ : A}
    (hW : IsE3Form W β γ) (hell : W.IsElliptic) :
    IsUnit W.a₃ ∧ IsUnit (W.a₁ ^ 3 - 27 * W.a₃) := by
  obtain ⟨ha₁, ha₂, ha₃, ha₄, ha₆⟩ := hW
  have hΔ : W.Δ = W.a₃ ^ 3 * (W.a₁ ^ 3 - 27 * W.a₃) := by
    simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
      WeierstrassCurve.b₆, WeierstrassCurve.b₈, ha₂, ha₄, ha₆]
    ring
  have hu : IsUnit (W.a₃ ^ 3 * (W.a₁ ^ 3 - 27 * W.a₃)) := by
    rw [← hΔ]; exact (WeierstrassCurve.isElliptic_iff W).mp hell
  refine ⟨?_, isUnit_of_mul_isUnit_right hu⟩
  have h3 : IsUnit (W.a₃ ^ 3) := isUnit_of_mul_isUnit_left hu
  exact (isUnit_pow_iff (n := 3) (by norm_num)).mp h3

open LocalPresentation WeierstrassCurve in
open WeierstrassCurve in
set_option backward.isDefEq.respectTransparency false in
/-- **([T-E15-NORM] hL-killing, `P` ★★)** The universal marked `P = (0,0)` is killed by
`3`, over any coefficient ring with reduced universal base (e.g. any UFD with `3`
invertible, via `isReduced_e3RelQuotient`). -/
theorem three_zsmul_universalE3P
    [IsReduced (Spec (CommRingCat.of (E3ModuliRing R)))] :
    (3 : ℤ) • universalE3P R = 0 := by
  refine universalE3_section_killing R 0 0 (universalE3_equation_zero R) ?_
  intro K _ _ _ hns
  haveI : (((universalE3 R).baseChange K)).IsElliptic :=
    inferInstanceAs (((universalE3 R).map (algebraMap (E3ModuliRing R) K)).IsElliptic)
  simp only [map_zero] at hns ⊢
  have hE3K := IsE3Form.map (algebraMap (E3ModuliRing R) K) (universalE3_isE3Form R)
  have hflex : ((universalE3 R).baseChange K).IsFlexNF :=
    ⟨hE3K.2.1, hE3K.2.2.2.1, hE3K.2.2.2.2⟩
  have ha₃ : ((universalE3 R).baseChange K).a₃ ≠ 0 := by
    have hu := (e3form_units (universalE3_isE3Form R) inferInstance).1
    have huK : IsUnit (((universalE3 R).baseChange K).a₃) := by
      rw [show ((universalE3 R).baseChange K).a₃
          = algebraMap (E3ModuliRing R) K ((universalE3 R).a₃) from rfl]
      exact hu.map _
    exact huK.ne_zero
  exact WeierstrassCurve.Affine.Point.three_zsmul_some_origin hflex ha₃ hns

open WeierstrassCurve in
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
/-- **([T-E15-NORM] hL-killing, `Q` ★★)** The universal marked `Q = (γ, β+γ)` is killed
by `3`: the Stage-A doubling (`slope = den/den = 1`) with the `den`-unit certificate
`isUnit_e3Den` supplying the nowhere-`2`-torsion input. -/
theorem three_zsmul_universalE3Q
    [IsReduced (Spec (CommRingCat.of (E3ModuliRing R)))] :
    (3 : ℤ) • universalE3Q R = 0 := by
  refine universalE3_section_killing R (e3Gamma R) (e3Beta R + e3Gamma R)
    (universalE3_equation_Q R) ?_
  intro K _ _ _ hns
  haveI : (((universalE3 R).baseChange K)).IsElliptic :=
    inferInstanceAs (((universalE3 R).map (algebraMap (E3ModuliRing R) K)).IsElliptic)
  simp only [map_add] at hns ⊢
  have hE3K := IsE3Form.map (algebraMap (E3ModuliRing R) K) (universalE3_isE3Form R)
  have hden : algebraMap (E3ModuliRing R) K (e3Beta R)
      + algebraMap (E3ModuliRing R) K (e3Gamma R)
      - 3 * algebraMap (E3ModuliRing R) K (e3Beta R)
        * algebraMap (E3ModuliRing R) K (e3Gamma R) ≠ 0 := by
    have hu := (isUnit_e3Den R).map (algebraMap (E3ModuliRing R) K)
    have hform : algebraMap (E3ModuliRing R) K
        (e3Beta R + e3Gamma R - 3 * e3Beta R * e3Gamma R)
        = algebraMap (E3ModuliRing R) K (e3Beta R)
          + algebraMap (E3ModuliRing R) K (e3Gamma R)
          - 3 * algebraMap (E3ModuliRing R) K (e3Beta R)
            * algebraMap (E3ModuliRing R) K (e3Gamma R) := by
      rw [map_sub, map_add, map_mul, map_mul, map_ofNat]
    rw [hform] at hu
    exact hu.ne_zero
  refine WeierstrassCurve.Affine.Point.three_zsmul_some_e3Q ?_ ?_ ?_ ?_ hden hns
  · rw [show ((universalE3 R).baseChange K).a₁
        = algebraMap (E3ModuliRing R) K ((universalE3 R).a₁) from rfl]
    show algebraMap (E3ModuliRing R) K (3 * e3Gamma R - 1) = _
    rw [map_sub, map_mul, map_ofNat, map_one]
  · exact hE3K.2.1
  · rw [show ((universalE3 R).baseChange K).a₃
        = algebraMap (E3ModuliRing R) K ((universalE3 R).a₃) from rfl]
    show algebraMap (E3ModuliRing R) K
      (-3 * e3Gamma R ^ 2 - e3Beta R - 3 * e3Beta R * e3Gamma R) = _
    simp only [map_sub, map_mul, map_neg, map_ofNat, map_pow]
  · exact hE3K.2.2.2.1

/-! ### The unconditional killing: transport from `ℤ[1/3]` (Stage D instantiation)

`ZInvThree := ULift ℤ[1/3]` is a UFD in universe `u`, so its universal base is reduced
(`isReduced_spec_e3ModuliRing`) and the conditional killings fire there; the classifying
map `ℤ[1/3] → R` (initiality of the localization) plus the Stage-D transport
`nsmul_section_map_eq_zero_of_nsmul_eq_zero` then carry the killing to every coefficient
ring with `3` invertible — no reducedness hypothesis on `R`. -/

/-- `ℤ[1/3]` in universe `u` — the initial coefficient ring with `3` invertible. -/
abbrev ZInvThree : Type u := ULift.{u} (Localization.Away (3 : ℤ))

instance : IsDomain (Localization.Away (3 : ℤ)) :=
  IsLocalization.isDomain_localization
    (powers_le_nonZeroDivisors_of_noZeroDivisors (by norm_num))

instance : IsDomain ZInvThree.{u} :=
  Function.Injective.isDomain
    (ULift.ringEquiv : ZInvThree.{u} ≃+* Localization.Away (3 : ℤ))
    (ULift.ringEquiv : ZInvThree.{u} ≃+* Localization.Away (3 : ℤ)).injective

instance : IsPrincipalIdealRing (Localization.Away (3 : ℤ)) := by
  constructor
  intro J
  obtain ⟨⟨a, ha⟩⟩ := IsPrincipalIdealRing.principal
    (J.comap (algebraMap ℤ (Localization.Away (3 : ℤ))))
  rw [Ideal.submodule_span_eq] at ha
  refine ⟨⟨algebraMap ℤ _ a, ?_⟩⟩
  conv_lhs => rw [← IsLocalization.map_under (Submonoid.powers (3 : ℤ))
    (Localization.Away (3 : ℤ)) J]
  show Ideal.map _ (J.comap _) = _
  rw [ha, Ideal.map_span, Set.image_singleton, Ideal.submodule_span_eq]

instance : UniqueFactorizationMonoid ZInvThree.{u} :=
  ((ULift.ringEquiv : ZInvThree.{u} ≃+* Localization.Away (3 : ℤ)).symm.toMulEquiv).uniqueFactorizationMonoid
    inferInstance

theorem isUnit_three_zInvThree : IsUnit (3 : ZInvThree.{u}) := by
  have h := IsLocalization.Away.algebraMap_isUnit
    (S := Localization.Away (3 : ℤ)) (3 : ℤ)
  rw [map_ofNat] at h
  have h2 := h.map
    (ULift.ringEquiv : ZInvThree.{u} ≃+* Localization.Away (3 : ℤ)).symm.toRingHom
  rwa [map_ofNat] at h2

/-- **(Stage D)** The classifying map `ℤ[1/3] ⟶ R` for any `R` with `3` invertible. -/
noncomputable def zInvThreeHom (R : CommRingCat.{u}) (hR : IsUnit (3 : R)) :
    CommRingCat.of ZInvThree.{u} ⟶ R :=
  CommRingCat.ofHom <|
    (IsLocalization.Away.lift (S := Localization.Away (3 : ℤ)) (3 : ℤ)
        (g := Int.castRingHom R) (by rw [map_ofNat]; exact hR)).comp
      (ULift.ringEquiv : ZInvThree.{u} ≃+* Localization.Away (3 : ℤ)).toRingHom

open WeierstrassCurve in
set_option backward.isDefEq.respectTransparency false in
/-- Transport a marked-section killing along an equality of Weierstrass curves
(the `Equation` witnesses and the ellipticity instances are proof-irrelevant). -/
theorem section_killing_congr {A : Type u} [CommRing A] {W₁ W₂ : WeierstrassCurve A}
    (hW : W₁ = W₂) [W₁.IsElliptic] [W₂.IsElliptic] (n : ℤ) (p q : A)
    (h₁ : W₁.toAffine.Equation p q) (h₂ : W₂.toAffine.Equation p q)
    (hk : n • (⟨projModelAffineSection W₁ p q h₁,
        projModelAffineSection_projModelπ _ _ _ _⟩ :
      EllipticCurve.Section (modelEllipticCurve W₁)) = 0) :
    n • (⟨projModelAffineSection W₂ p q h₂,
        projModelAffineSection_projModelπ _ _ _ _⟩ :
      EllipticCurve.Section (modelEllipticCurve W₂)) = 0 := by
  subst hW
  exact hk

open WeierstrassCurve in
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1600000 in
/-- **(Stage D instantiation ★★)** Transport of a marked-section killing from `ℤ[1/3]`'s
universal base to `R`'s along the classifying map: the D-1 functoriality identifies the
mapped universal curve with `R`'s, and the Stage-D transport
`nsmul_section_map_eq_zero_of_nsmul_eq_zero` carries the section-level killing. -/
theorem three_zsmul_section_map (R₀ R : CommRingCat.{u}) (f : R₀ ⟶ R)
    (p₀ q₀ : E3ModuliRing R₀)
    (h₀ : (universalE3 R₀).toAffine.Equation p₀ q₀)
    (hkill : (3 : ℤ) • (⟨projModelAffineSection _ p₀ q₀ h₀,
        projModelAffineSection_projModelπ _ _ _ _⟩ :
      (universalE3Obj R₀).curve.Section) = 0)
    (p q : E3ModuliRing R)
    (hp : e3ModuliRingMap f p₀ = p)
    (hq : e3ModuliRingMap f q₀ = q)
    (h : (universalE3 R).toAffine.Equation p q) :
    (3 : ℤ) • (⟨projModelAffineSection (universalE3 R) p q h,
        projModelAffineSection_projModelπ _ _ _ _⟩ :
      (universalE3Obj R).curve.Section) = 0 := by
  letI : Algebra (E3ModuliRing R₀) (E3ModuliRing R) :=
    (e3ModuliRingMap (f)).toAlgebra
  have halg : ∀ x, algebraMap (E3ModuliRing R₀)
      (E3ModuliRing R) x = e3ModuliRingMap (f) x := fun _ => rfl
  -- the mapped equation witness
  have h' : ((universalE3 R₀).map
      (algebraMap (E3ModuliRing R₀)
        (E3ModuliRing R))).toAffine.Equation
      (algebraMap _ (E3ModuliRing R) p₀) (algebraMap _ (E3ModuliRing R) q₀) :=
    WeierstrassCurve.Affine.Equation.map _ h₀
  -- the transported killing (ℕ-cast form)
  have hkill' : ((3 : ℕ) : ℤ) •
      (⟨projModelAffineSection (universalE3 R₀) p₀ q₀ h₀,
        projModelAffineSection_projModelπ _ _ _ _⟩ :
      EllipticCurve.Section (modelEllipticCurve
        (universalE3 R₀))) = 0 := by
    rw [show (((3 : ℕ) : ℤ)) = (3 : ℤ) from by norm_num]
    exact hkill
  have hT := nsmul_section_map_eq_zero_of_nsmul_eq_zero
    (W := universalE3 R₀) 3 p₀ q₀ h₀ h' hkill'
  have huniv : (universalE3 R₀).map (algebraMap (E3ModuliRing R₀) (E3ModuliRing R))
      = universalE3 R := universalE3_ringMap f
  -- convert the coordinates (simp's proof-irrelevant congruence handles the
  -- `Equation`-witness dependence)
  simp only [halg, hp, hq] at hT
  rw [show (((3 : ℕ) : ℤ)) = (3 : ℤ) from by norm_num] at hT
  exact section_killing_congr huniv _ p q _ h hT

open WeierstrassCurve in
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1600000 in
/-- **([T-E15-NORM] hL-killing unconditional, `P` ★★★)** `[3]P = 0` on the universal
`ℰ₃` over ANY coefficient ring with `3` invertible — Stage D transports the `ℤ[1/3]`
(UFD ⟹ reduced-base) killing along the classifying map. -/
theorem three_zsmul_universalE3P_of_isUnit (R : CommRingCat.{u})
    (hR : IsUnit (3 : R)) :
    (3 : ℤ) • universalE3P R = 0 := by
  haveI : IsDomain (CommRingCat.of ZInvThree.{u}) :=
    inferInstanceAs (IsDomain ZInvThree.{u})
  haveI : UniqueFactorizationMonoid (CommRingCat.of ZInvThree.{u}) :=
    inferInstanceAs (UniqueFactorizationMonoid ZInvThree.{u})
  haveI := isReduced_spec_e3ModuliRing (CommRingCat.of ZInvThree.{u})
    isUnit_three_zInvThree
  exact three_zsmul_section_map (CommRingCat.of ZInvThree.{u}) R
    (zInvThreeHom R hR) 0 0
    (universalE3_equation_zero _) (three_zsmul_universalE3P _) 0 0
    (map_zero _) (map_zero _) (universalE3_equation_zero R)

open WeierstrassCurve in
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1600000 in
/-- **([T-E15-NORM] hL-killing unconditional, `Q` ★★★)** `[3]Q = 0` on the universal
`ℰ₃` over ANY coefficient ring with `3` invertible — Stage D transports the `ℤ[1/3]`
killing along the classifying map (`γ`, `β` are functorial by D-1). -/
theorem three_zsmul_universalE3Q_of_isUnit (R : CommRingCat.{u})
    (hR : IsUnit (3 : R)) :
    (3 : ℤ) • universalE3Q R = 0 := by
  haveI : IsDomain (CommRingCat.of ZInvThree.{u}) :=
    inferInstanceAs (IsDomain ZInvThree.{u})
  haveI : UniqueFactorizationMonoid (CommRingCat.of ZInvThree.{u}) :=
    inferInstanceAs (UniqueFactorizationMonoid ZInvThree.{u})
  haveI := isReduced_spec_e3ModuliRing (CommRingCat.of ZInvThree.{u})
    isUnit_three_zInvThree
  exact three_zsmul_section_map (CommRingCat.of ZInvThree.{u}) R
    (zInvThreeHom R hR) (e3Gamma _)
    (e3Beta _ + e3Gamma _) (universalE3_equation_Q _) (three_zsmul_universalE3Q _)
    (e3Gamma R) (e3Beta R + e3Gamma R) (e3ModuliRingMap_gamma _)
    (by rw [map_add, e3ModuliRingMap_beta, e3ModuliRingMap_gamma])
    (universalE3_equation_Q R)

open WeierstrassCurve in
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1600000 in
/-- **([T-E15-NORM] hL-generation ★★)** At every geometric point of the universal base,
the pulled marked pair `(P̄, Q̄)` generates the `3`-torsion of the point group: KM's
`torsion_geometricFibre_rank_two` supplies `#T₃ = 9`, the Stage-B dictionary evaluates the
pulled sections to `some(0,0)` and `some(γ̄, β̄+γ̄)` with `γ̄ ≠ 0` (independence), the
`p = 3` reduction `combos3_ne_zero` feeds GH's criterion of record
`pair_generates_iff_combos_ne_zero`, and the subtype closure transports down. -/
theorem universalE3_generation (hR : IsUnit (3 : R)) (k : Type u) [Field k]
    [IsAlgClosed k]
    (t : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of (E3ModuliRing R)))
    (x : (universalE3Obj R).curve.Point t) (hx : ((3 : ℕ) : ℤ) • x = 0) :
    x ∈ AddSubgroup.closure
      {EllipticCurve.Point.pull (universalE3Obj R).curve t (universalE3P R),
       EllipticCurve.Point.pull (universalE3Obj R).curve t (universalE3Q R)} := by
  letI : DecidableEq k := Classical.decEq k
  obtain ⟨φ, rfl⟩ : ∃ φ : CommRingCat.of (E3ModuliRing R) ⟶ CommRingCat.of k,
      Spec.map φ = t := ⟨Spec.preimage t, Spec.map_preimage t⟩
  letI : Algebra (E3ModuliRing R) k := φ.hom.toAlgebra
  haveI : (((universalE3 R).baseChange k)).IsElliptic :=
    inferInstanceAs (((universalE3 R).map (algebraMap (E3ModuliRing R) k)).IsElliptic)
  have hφ : CommRingCat.ofHom (algebraMap (E3ModuliRing R) k) = φ := rfl
  -- the evaluated marked points and their dictionary values
  set PP := EllipticCurve.Point.pull (universalE3Obj R).curve (Spec.map φ)
    (universalE3P R) with hPP
  set QQ := EllipticCurve.Point.pull (universalE3Obj R).curve (Spec.map φ)
    (universalE3Q R) with hQQ
  have hnsP : ((universalE3 R).baseChange k).toAffine.Nonsingular
      (algebraMap (E3ModuliRing R) k 0) (algebraMap (E3ModuliRing R) k 0) :=
    WeierstrassCurve.Affine.equation_iff_nonsingular.mp
      (WeierstrassCurve.Affine.Equation.map _ (universalE3_equation_zero R))
  have hnsQ : ((universalE3 R).baseChange k).toAffine.Nonsingular
      (algebraMap (E3ModuliRing R) k (e3Gamma R))
      (algebraMap (E3ModuliRing R) k (e3Beta R + e3Gamma R)) :=
    WeierstrassCurve.Affine.equation_iff_nonsingular.mp
      (WeierstrassCurve.Affine.Equation.map _ (universalE3_equation_Q R))
  have hPval : modelPointAddEquiv (universalE3 R) PP
      = WeierstrassCurve.Affine.Point.some _ _ hnsP := by
    show projModelPointsEquiv (universalE3 R) k
      (affineSectionSpecPoint (universalE3 R) k 0 0 (universalE3_equation_zero R)) = _
    exact projModelPointsEquiv_affineSectionSpecPoint (universalE3 R) 0 0
      (universalE3_equation_zero R) hnsP
  have hQval : modelPointAddEquiv (universalE3 R) QQ
      = WeierstrassCurve.Affine.Point.some _ _ hnsQ := by
    show projModelPointsEquiv (universalE3 R) k
      (affineSectionSpecPoint (universalE3 R) k (e3Gamma R) (e3Beta R + e3Gamma R)
        (universalE3_equation_Q R)) = _
    exact projModelPointsEquiv_affineSectionSpecPoint (universalE3 R) _ _
      (universalE3_equation_Q R) hnsQ
  -- torsionness of the evaluated points (Stage A through the dictionary)
  have h3P : (3 : ℤ) • PP = 0 := by
    apply (modelPointAddEquiv (universalE3 R)).injective
    rw [map_zsmul, map_zero, hPval]
    have hE3K := IsE3Form.map (algebraMap (E3ModuliRing R) k) (universalE3_isE3Form R)
    have hflex : ((universalE3 R).baseChange k).IsFlexNF :=
      ⟨hE3K.2.1, hE3K.2.2.2.1, hE3K.2.2.2.2⟩
    have ha₃ : ((universalE3 R).baseChange k).a₃ ≠ 0 := by
      have hu := (e3form_units (universalE3_isE3Form R) inferInstance).1
      have huK : IsUnit (((universalE3 R).baseChange k).a₃) := by
        rw [show ((universalE3 R).baseChange k).a₃
            = algebraMap (E3ModuliRing R) k ((universalE3 R).a₃) from rfl]
        exact hu.map _
      exact huK.ne_zero
    have h := WeierstrassCurve.Affine.Point.three_zsmul_some_origin hflex ha₃
      (by simpa only [map_zero] using hnsP)
    simpa only [map_zero] using h
  have h3Q : (3 : ℤ) • QQ = 0 := by
    apply (modelPointAddEquiv (universalE3 R)).injective
    rw [map_zsmul, map_zero, hQval]
    have hE3K := IsE3Form.map (algebraMap (E3ModuliRing R) k) (universalE3_isE3Form R)
    have hden : algebraMap (E3ModuliRing R) k (e3Beta R)
        + algebraMap (E3ModuliRing R) k (e3Gamma R)
        - 3 * algebraMap (E3ModuliRing R) k (e3Beta R)
          * algebraMap (E3ModuliRing R) k (e3Gamma R) ≠ 0 := by
      have hu := (isUnit_e3Den R).map (algebraMap (E3ModuliRing R) k)
      have hform : algebraMap (E3ModuliRing R) k
          (e3Beta R + e3Gamma R - 3 * e3Beta R * e3Gamma R)
          = algebraMap (E3ModuliRing R) k (e3Beta R)
            + algebraMap (E3ModuliRing R) k (e3Gamma R)
            - 3 * algebraMap (E3ModuliRing R) k (e3Beta R)
              * algebraMap (E3ModuliRing R) k (e3Gamma R) := by
        rw [map_sub, map_add, map_mul, map_mul, map_ofNat]
      rw [hform] at hu
      exact hu.ne_zero
    have hnsQ' : ((universalE3 R).map
        (algebraMap (E3ModuliRing R) k)).toAffine.Nonsingular
        (algebraMap (E3ModuliRing R) k (e3Gamma R))
        (algebraMap (E3ModuliRing R) k (e3Beta R)
          + algebraMap (E3ModuliRing R) k (e3Gamma R)) := by
      haveI : (((universalE3 R).map (algebraMap (E3ModuliRing R) k))).IsElliptic :=
        inferInstanceAs (((universalE3 R).baseChange k)).IsElliptic
      have heq := WeierstrassCurve.Affine.Equation.map
        (algebraMap (E3ModuliRing R) k) (universalE3_equation_Q R)
      rw [map_add] at heq
      exact WeierstrassCurve.Affine.equation_iff_nonsingular.mp heq
    have h := WeierstrassCurve.Affine.Point.three_zsmul_some_e3Q
      (β := algebraMap (E3ModuliRing R) k (e3Beta R))
      (γ := algebraMap (E3ModuliRing R) k (e3Gamma R))
      (by show algebraMap (E3ModuliRing R) k (3 * e3Gamma R - 1) = _
          rw [map_sub, map_mul, map_ofNat, map_one])
      hE3K.2.1
      (by show algebraMap (E3ModuliRing R) k
            (-3 * e3Gamma R ^ 2 - e3Beta R - 3 * e3Beta R * e3Gamma R) = _
          simp only [map_sub, map_mul, map_neg, map_ofNat, map_pow])
      hE3K.2.2.2.1 hden hnsQ'
    simpa only [map_add] using h
  -- independence of the evaluated points
  have hγne : algebraMap (E3ModuliRing R) k (e3Gamma R) ≠ 0 :=
    ((isUnit_e3Gamma R).map (algebraMap (E3ModuliRing R) k)).ne_zero
  have hPne : PP ≠ 0 := by
    intro hc
    exact WeierstrassCurve.Affine.Point.some_ne_zero hnsP
      (by rw [← hPval, hc, map_zero])
  have hQne : QQ ≠ 0 := by
    intro hc
    exact WeierstrassCurve.Affine.Point.some_ne_zero hnsQ
      (by rw [← hQval, hc, map_zero])
  have hQP : QQ ≠ PP := by
    intro hc
    have h := hQval.symm.trans ((congrArg (modelPointAddEquiv (universalE3 R)) hc).trans
      hPval)
    injection h with h1 h2
    exact hγne (h1.trans (map_zero _))
  have hQnP : QQ ≠ -PP := by
    intro hc
    have h := hQval.symm.trans ((congrArg (modelPointAddEquiv (universalE3 R)) hc).trans
      (by rw [map_neg, hPval, WeierstrassCurve.Affine.Point.neg_some]))
    injection h with h1 h2
    exact hγne (h1.trans (map_zero _))
  -- the torsion subgroup, its count, and the criterion of record
  have h3k : ((3 : ℕ) : k) ≠ 0 := by
    have hu := (hR.map ((algebraMap (E3ModuliRing R) k).comp
      (algebraMap R (E3ModuliRing R)))).ne_zero
    rw [map_ofNat] at hu
    rwa [show ((3 : ℕ) : k) = (3 : k) by norm_num]
  obtain ⟨e⟩ := (universalE3Obj R).curve.torsion_geometricFibre_rank_two 3 k
    (Spec.map φ) h3k
  have hcard : Nat.card (Submodule.torsionBy ℤ
      ((universalE3Obj R).curve.Point (Spec.map φ)) ((3 : ℕ) : ℤ)) = 3 ^ 2 := by
    rw [Nat.card_congr e.toEquiv]
    simp [Nat.card_pi, Nat.card_zmod]
  have hmemP : PP ∈ Submodule.torsionBy ℤ
      ((universalE3Obj R).curve.Point (Spec.map φ)) ((3 : ℕ) : ℤ) :=
    (Submodule.mem_torsionBy_iff _ _).mpr (by exact_mod_cast h3P)
  have hmemQ : QQ ∈ Submodule.torsionBy ℤ
      ((universalE3Obj R).curve.Point (Spec.map φ)) ((3 : ℕ) : ℤ) :=
    (Submodule.mem_torsionBy_iff _ _).mpr (by exact_mod_cast h3Q)
  have hmemX : x ∈ Submodule.torsionBy ℤ
      ((universalE3Obj R).curve.Point (Spec.map φ)) ((3 : ℕ) : ℤ) :=
    (Submodule.mem_torsionBy_iff _ _).mpr (by exact_mod_cast hx)
  have hkillT : ∀ g : Submodule.torsionBy ℤ
      ((universalE3Obj R).curve.Point (Spec.map φ)) ((3 : ℕ) : ℤ),
      ((3 : ℕ) : ℤ) • g = 0 := fun g => Submodule.smul_torsionBy _ _
  have hcombosT : ∀ ab : ZMod 3 × ZMod 3, ab ≠ 0 →
      ((ab.1.val : ℤ)) • (⟨PP, hmemP⟩ : Submodule.torsionBy ℤ
          ((universalE3Obj R).curve.Point (Spec.map φ)) ((3 : ℕ) : ℤ))
        + ((ab.2.val : ℤ)) • ⟨QQ, hmemQ⟩ ≠ 0 := by
    intro ab hab hc
    refine combos3_ne_zero h3P h3Q hPne hQne hQP hQnP ab hab ?_
    have := congrArg (Subtype.val) hc
    simpa using this
  have hgen := (pair_generates_iff_combos_ne_zero 3 hcard hkillT
    ⟨PP, hmemP⟩ ⟨QQ, hmemQ⟩).mp hcombosT ⟨x, hmemX⟩
  -- transport the closure membership down the subtype
  have hmap := AddMonoidHom.map_closure
    ((Submodule.torsionBy ℤ ((universalE3Obj R).curve.Point (Spec.map φ))
      ((3 : ℕ) : ℤ)).subtype.toAddMonoidHom)
    ({⟨PP, hmemP⟩, ⟨QQ, hmemQ⟩} : Set _)
  have hx' : x ∈ AddSubgroup.map
      ((Submodule.torsionBy ℤ ((universalE3Obj R).curve.Point (Spec.map φ))
        ((3 : ℕ) : ℤ)).subtype.toAddMonoidHom)
      (AddSubgroup.closure {⟨PP, hmemP⟩, ⟨QQ, hmemQ⟩}) :=
    ⟨⟨x, hmemX⟩, hgen, rfl⟩
  rw [hmap] at hx'
  simpa [Set.image_insert_eq] using hx'


open WeierstrassCurve in
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1600000 in
/-- **([T-E14-LVL-b] E[2]-generation ★★)** At every geometric point of the Legendre
base, the pulled marked pair `(P̄, Q̄) = (some(0,0), some(1,0))` generates the
`2`-torsion of the point group: KM's `torsion_geometricFibre_rank_two` supplies
`#T₂ = 4`, the Stage-B dictionary evaluates the pulled sections, the `p = 2`
reduction `combos2_ne_zero` feeds the criterion of record
`pair_generates_iff_combos_ne_zero`, and the subtype closure transports down.
(The Legendre analog of `universalE3_generation`; the fibre killing comes from the
section-level `two_zsmul_universalLegendreP/Q` through `Point.pull_zsmul`.) -/
theorem universalLegendre_generation (hR : IsUnit (2 : R)) (k : Type u) [Field k]
    [IsAlgClosed k]
    (t : Spec (CommRingCat.of k) ⟶ (universalLegendreObj R hR).base)
    (x : (universalLegendreObj R hR).curve.Point t) (hx : ((2 : ℕ) : ℤ) • x = 0) :
    x ∈ AddSubgroup.closure
      {EllipticCurve.Point.pull (universalLegendreObj R hR).curve t
        (universalLegendreP R hR),
       EllipticCurve.Point.pull (universalLegendreObj R hR).curve t
        (universalLegendreQ R hR)} := by
  haveI := universalLegendre_isElliptic R hR
  letI : DecidableEq k := Classical.decEq k
  obtain ⟨φ, rfl⟩ : ∃ φ : CommRingCat.of (LegendreModuliRing R) ⟶ CommRingCat.of k,
      Spec.map φ = t := ⟨Spec.preimage t, Spec.map_preimage t⟩
  letI : Algebra (LegendreModuliRing R) k := φ.hom.toAlgebra
  haveI : (((universalLegendre R).baseChange k)).IsElliptic :=
    inferInstanceAs (((universalLegendre R).map
      (algebraMap (LegendreModuliRing R) k)).IsElliptic)
  -- the evaluated marked points and their dictionary values
  set PP := EllipticCurve.Point.pull (universalLegendreObj R hR).curve (Spec.map φ)
    (universalLegendreP R hR) with hPP
  set QQ := EllipticCurve.Point.pull (universalLegendreObj R hR).curve (Spec.map φ)
    (universalLegendreQ R hR) with hQQ
  have hnsP : ((universalLegendre R).baseChange k).toAffine.Nonsingular
      (algebraMap (LegendreModuliRing R) k 0) (algebraMap (LegendreModuliRing R) k 0) :=
    WeierstrassCurve.Affine.equation_iff_nonsingular.mp
      (WeierstrassCurve.Affine.Equation.map _
        (legendreCurve_equation_zero (universalLambda R)))
  have hnsQ : ((universalLegendre R).baseChange k).toAffine.Nonsingular
      (algebraMap (LegendreModuliRing R) k 1) (algebraMap (LegendreModuliRing R) k 0) :=
    WeierstrassCurve.Affine.equation_iff_nonsingular.mp
      (WeierstrassCurve.Affine.Equation.map _
        (legendreCurve_equation_one (universalLambda R)))
  have hPval : modelPointAddEquiv (universalLegendre R) PP
      = WeierstrassCurve.Affine.Point.some _ _ hnsP := by
    show projModelPointsEquiv (universalLegendre R) k
      (affineSectionSpecPoint (universalLegendre R) k 0 0
        (legendreCurve_equation_zero (universalLambda R))) = _
    exact projModelPointsEquiv_affineSectionSpecPoint (universalLegendre R) 0 0
      (legendreCurve_equation_zero (universalLambda R)) hnsP
  have hQval : modelPointAddEquiv (universalLegendre R) QQ
      = WeierstrassCurve.Affine.Point.some _ _ hnsQ := by
    show projModelPointsEquiv (universalLegendre R) k
      (affineSectionSpecPoint (universalLegendre R) k 1 0
        (legendreCurve_equation_one (universalLambda R))) = _
    exact projModelPointsEquiv_affineSectionSpecPoint (universalLegendre R) 1 0
      (legendreCurve_equation_one (universalLambda R)) hnsQ
  -- fibre killing through the section-level killing
  have h2P : (2 : ℤ) • PP = 0 := by
    rw [hPP, ← EllipticCurve.Point.pull_zsmul, two_zsmul_universalLegendreP R hR,
      EllipticCurve.Point.pull_zero]
  have h2Q : (2 : ℤ) • QQ = 0 := by
    rw [hQQ, ← EllipticCurve.Point.pull_zsmul, two_zsmul_universalLegendreQ R hR,
      EllipticCurve.Point.pull_zero]
  -- independence of the evaluated points
  have hPne : PP ≠ 0 := by
    intro hc
    exact WeierstrassCurve.Affine.Point.some_ne_zero hnsP
      (by rw [← hPval, hc, map_zero])
  have hQne : QQ ≠ 0 := by
    intro hc
    exact WeierstrassCurve.Affine.Point.some_ne_zero hnsQ
      (by rw [← hQval, hc, map_zero])
  have hPQ : PP + QQ ≠ 0 := by
    intro hc
    have hQeq : QQ = -PP := by rwa [add_comm, add_eq_zero_iff_eq_neg] at hc
    have h := hQval.symm.trans
      ((congrArg (modelPointAddEquiv (universalLegendre R)) hQeq).trans
        (by rw [map_neg, hPval, WeierstrassCurve.Affine.Point.neg_some]))
    injection h with h1 h2
    rw [map_one, map_zero] at h1
    exact one_ne_zero h1
  -- the torsion subgroup, its count, and the criterion of record
  have h2k : ((2 : ℕ) : k) ≠ 0 := by
    have hu := (hR.map ((algebraMap (LegendreModuliRing R) k).comp
      (algebraMap R (LegendreModuliRing R)))).ne_zero
    rw [map_ofNat] at hu
    rwa [show ((2 : ℕ) : k) = (2 : k) by norm_num]
  obtain ⟨e⟩ := (universalLegendreObj R hR).curve.torsion_geometricFibre_rank_two 2 k
    (Spec.map φ) h2k
  have hcard : Nat.card (Submodule.torsionBy ℤ
      ((universalLegendreObj R hR).curve.Point (Spec.map φ)) ((2 : ℕ) : ℤ)) = 2 ^ 2 := by
    rw [Nat.card_congr e.toEquiv]
    simp [Nat.card_pi, Nat.card_zmod]
  have hmemP : PP ∈ Submodule.torsionBy ℤ
      ((universalLegendreObj R hR).curve.Point (Spec.map φ)) ((2 : ℕ) : ℤ) :=
    (Submodule.mem_torsionBy_iff _ _).mpr (by exact_mod_cast h2P)
  have hmemQ : QQ ∈ Submodule.torsionBy ℤ
      ((universalLegendreObj R hR).curve.Point (Spec.map φ)) ((2 : ℕ) : ℤ) :=
    (Submodule.mem_torsionBy_iff _ _).mpr (by exact_mod_cast h2Q)
  have hmemX : x ∈ Submodule.torsionBy ℤ
      ((universalLegendreObj R hR).curve.Point (Spec.map φ)) ((2 : ℕ) : ℤ) :=
    (Submodule.mem_torsionBy_iff _ _).mpr (by exact_mod_cast hx)
  have hkillT : ∀ g : Submodule.torsionBy ℤ
      ((universalLegendreObj R hR).curve.Point (Spec.map φ)) ((2 : ℕ) : ℤ),
      ((2 : ℕ) : ℤ) • g = 0 := fun g => Submodule.smul_torsionBy _ _
  have hcombosT : ∀ ab : ZMod 2 × ZMod 2, ab ≠ 0 →
      ((ab.1.val : ℤ)) • (⟨PP, hmemP⟩ : Submodule.torsionBy ℤ
          ((universalLegendreObj R hR).curve.Point (Spec.map φ)) ((2 : ℕ) : ℤ))
        + ((ab.2.val : ℤ)) • ⟨QQ, hmemQ⟩ ≠ 0 := by
    intro ab hab hc
    refine combos2_ne_zero hPne hQne hPQ ab hab ?_
    have := congrArg (Subtype.val) hc
    simpa using this
  have hgen := (pair_generates_iff_combos_ne_zero 2 hcard hkillT
    ⟨PP, hmemP⟩ ⟨QQ, hmemQ⟩).mp hcombosT ⟨x, hmemX⟩
  -- transport the closure membership down the subtype
  have hmap := AddMonoidHom.map_closure
    ((Submodule.torsionBy ℤ ((universalLegendreObj R hR).curve.Point (Spec.map φ))
      ((2 : ℕ) : ℤ)).subtype.toAddMonoidHom)
    ({⟨PP, hmemP⟩, ⟨QQ, hmemQ⟩} : Set _)
  have hx' : x ∈ AddSubgroup.map
      ((Submodule.torsionBy ℤ ((universalLegendreObj R hR).curve.Point (Spec.map φ))
        ((2 : ℕ) : ℤ)).subtype.toAddMonoidHom)
      (AddSubgroup.closure {⟨PP, hmemP⟩, ⟨QQ, hmemQ⟩}) :=
    ⟨⟨x, hmemX⟩, hgen, rfl⟩
  rw [hmap] at hx'
  simpa [Set.image_insert_eq] using hx'

/-- **(T-E15a stage 5)** `Q = (γ, β+γ)` on an `E3`-form curve is the flex relation
`γ(3β²+3βγ+γ²) = 0`. -/
theorem e3form_flex {A : Type u} [CommRing A] {W : WeierstrassCurve A} {β γ : A}
    (hW : IsE3Form W β γ) (hQ : W.toAffine.Equation γ (β + γ)) :
    γ * (3 * β ^ 2 + 3 * β * γ + γ ^ 2) = 0 := by
  obtain ⟨ha₁, ha₂, ha₃, ha₄, ha₆⟩ := hW
  rw [WeierstrassCurve.Affine.equation_iff] at hQ
  rw [ha₁, ha₂, ha₃, ha₄, ha₆] at hQ
  linear_combination -hQ

open LocalPresentation WeierstrassCurve in
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
/-- **(T-E15a stage 5)** The marking chase: a section marked at `(p₁,q₁)` on `Pr` and
`(p₂,q₂)` on `Qr` gives the variable-change coordinate identities for `Pr.transVC Qr`. -/
theorem e3_markChase {S : Scheme.{u}} {G : EllipticCurveGeom S} {V : S.affineOpens}
    {Pr Qr : LocalPresentation G V} {σ : S ⟶ G.E} {hσ : σ ≫ G.π = 𝟙 S}
    {p₁ q₁ p₂ q₂ : Γ(S, V.1)}
    (hPrM : Pr.MarksAt hσ p₁ q₁) (hQrM : Qr.MarksAt hσ p₂ q₂) :
    ((Pr.transVC Qr).u : Γ(S, V.1)) ^ 2 * p₁ + (Pr.transVC Qr).r = p₂ ∧
      ((Pr.transVC Qr).u : Γ(S, V.1)) ^ 3 * q₁ +
        (Pr.transVC Qr).s * ((Pr.transVC Qr).u : Γ(S, V.1)) ^ 2 * p₁ +
        (Pr.transVC Qr).t = q₂ := by
  obtain ⟨hP1, hPeq⟩ := hPrM
  obtain ⟨hP2, hQeq⟩ := hQrM
  have hchase : projModelAffineSection Pr.W p₁ q₁ hP1 ≫ (Pr.pointedIso Qr).hom =
      projModelAffineSection Qr.W p₂ q₂ hP2 := by
    rw [← hPeq, ← hQeq]
    show ((V.2.isoSpec.inv ≫ sectionLift G hσ V) ≫ Pr.e.hom) ≫
      (Pr.e.symm ≪≫ Qr.e).hom = _
    rw [Iso.trans_hom, Iso.symm_hom, Category.assoc, Category.assoc,
      Iso.hom_inv_id_assoc, Category.assoc]
  rw [Pr.transVC_spec Qr] at hchase
  have hWeq : Pr.W = Pr.transVC Qr • Qr.W := (Pr.transVC_smul Qr).symm
  rw [← Category.assoc, projModelAffineSection_congr hWeq p₁ q₁ hP1] at hchase
  rw [projModelVCIso_affineSection (Pr.transVC Qr) Qr.W p₁ q₁ (hWeq ▸ hP1)
    (equation_smul_image (Pr.transVC Qr) Qr.W (hWeq ▸ hP1))] at hchase
  exact projModelAffineSection_injective Qr.W _ hP2 hchase

open LocalPresentation WeierstrassCurve in
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1600000 in
/-- **(T-E15a stage 5 ★★)** KM Ex. 2.2.2 uniqueness at the presentation level: two
`E3`-form witnesses marking the same `P` at `(0,0)` and `Q` at `(γᵢ, βᵢ+γᵢ)` have
`transVC = 1` and equal parameters. -/
theorem e3_witness_transVC_eq_one {S : Scheme.{u}} {G : EllipticCurveGeom S}
    {V : S.affineOpens} {Pr Qr : LocalPresentation G V}
    {β₁ γ₁ β₂ γ₂ : Γ(S, V.1)}
    (hPrW : IsE3Form Pr.W β₁ γ₁) (hQrW : IsE3Form Qr.W β₂ γ₂)
    {σP σQ : S ⟶ G.E} {hσP : σP ≫ G.π = 𝟙 S} {hσQ : σQ ≫ G.π = 𝟙 S}
    (hPrP : Pr.MarksAt hσP 0 0) (hQrP : Qr.MarksAt hσP 0 0)
    (hPrQ : Pr.MarksAt hσQ γ₁ (β₁ + γ₁)) (hQrQ : Qr.MarksAt hσQ γ₂ (β₂ + γ₂))
    (h3 : IsUnit (3 : Γ(S, V.1))) :
    Pr.transVC Qr = 1 ∧ γ₁ = γ₂ ∧ β₁ = β₂ := by
  set C := Pr.transVC Qr with hCdef
  have hPchase := e3_markChase hPrP hQrP
  have hQchase := e3_markChase hPrQ hQrQ
  have hr : C.r = 0 := by
    have h := hPchase.1; simp only [mul_zero, zero_add] at h; exact h
  have ht : C.t = 0 := by
    have h := hPchase.2; simp only [mul_zero, zero_add] at h; exact h
  have hγ : (C.u : Γ(S, V.1)) ^ 2 * γ₁ = γ₂ := by
    have h := hQchase.1; rwa [hr, add_zero] at h
  have hβγ : (C.u : Γ(S, V.1)) ^ 3 * (β₁ + γ₁) +
      C.s * (C.u : Γ(S, V.1)) ^ 2 * γ₁ = β₂ + γ₂ := by
    have h := hQchase.2; rwa [ht, add_zero] at h
  -- ellipticity of the witness curves (from the E3-form + IsElliptic instance on the
  -- chart)
  have hell₁ : Pr.W.IsElliptic := Pr.elliptic
  have hell₂ : Qr.W.IsElliptic := Qr.elliptic
  obtain ⟨ha₃₂, _⟩ := e3form_units hQrW hell₂
  obtain ⟨_, hD₁⟩ := e3form_units hPrW hell₁
  obtain ⟨hPeq0, _⟩ := hPrQ
  obtain ⟨hQeq0, _⟩ := hQrQ
  have hflex₁ := e3form_flex hPrW hPeq0
  have hflex₂ := e3form_flex hQrW hQeq0
  exact e3_vc_marked hPrW hQrW (Pr.transVC_smul Qr) hr ht hγ hβγ hflex₁ hflex₂
    ha₃₂ hD₁ h3

open LocalPresentation WeierstrassCurve in
set_option backward.isDefEq.respectTransparency false in
/-- **(T-E15a stage 6)** `IsE3Form` restricts (coefficient-wise) with the restricted
parameters. -/
theorem restrict_W_e3form {S : Scheme.{u}} {G : EllipticCurveGeom S}
    {V : S.affineOpens} {Pr : LocalPresentation G V} {β γ : Γ(S, V.1)}
    (hW : IsE3Form Pr.W β γ) {V' : S.affineOpens} (h : V'.1 ≤ V.1) :
    IsE3Form (Pr.restrict h).W (Scheme.resLE h β) (Scheme.resLE h γ) := by
  obtain ⟨ha₁, ha₂, ha₃, ha₄, ha₆⟩ := hW
  have hmap : ∀ x : Γ(S, V.1),
      (sectionsMapLE (𝟙 S) (show V'.1 ≤ (𝟙 S : S ⟶ S) ⁻¹ᵁ V.1 by simpa using h)) x =
        Scheme.resLE h x :=
    fun x => congrArg (fun (r : Γ(S, V.1) →+* Γ(S, V'.1)) => r x)
      (sectionsMapLE_id (by simpa using h))
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · show (Pr.W.map (sectionsMapLE (𝟙 S) _)).a₁ = _
    rw [WeierstrassCurve.map_a₁, ha₁, map_sub, map_mul, map_ofNat, map_one, hmap]
  · show (Pr.W.map (sectionsMapLE (𝟙 S) _)).a₂ = _
    rw [WeierstrassCurve.map_a₂, ha₂, map_zero]
  · show (Pr.W.map (sectionsMapLE (𝟙 S) _)).a₃ = _
    rw [WeierstrassCurve.map_a₃, ha₃]
    rw [map_sub, map_sub, map_mul, map_neg, map_ofNat, map_pow, map_mul, map_mul,
      map_ofNat, hmap, hmap]
  · show (Pr.W.map (sectionsMapLE (𝟙 S) _)).a₄ = _
    rw [WeierstrassCurve.map_a₄, ha₄, map_zero]
  · show (Pr.W.map (sectionsMapLE (𝟙 S) _)).a₆ = _
    rw [WeierstrassCurve.map_a₆, ha₆, map_zero]

open LocalPresentation in
/-- **(T-E15a stage 6, the corrected KM Ex. 2.2.2 datum)** An `E3` datum on `E/S`: a
naive full level-`3` structure `(P, Q)` such that, locally, there is a chart
presentation of `E3`-form marking `P` at `(0,0)` and `Q` at `(γ, β+γ)`. -/
def IsE3Datum {R : CommRingCat.{u}} (X : EllObj R)
    (L : X.curve.FullLevelPt 3) : Prop :=
  ∀ s : X.base, ∃ (V : X.base.affineOpens) (_ : s ∈ V.1)
    (Pr : LocalPresentation X.curve.toEllipticCurveGeom V)
    (β γ : Γ(X.base, V.1)),
      IsE3Form Pr.W β γ ∧ Pr.MarksAt L.1.1.2 0 0 ∧
      Pr.MarksAt L.1.2.2 γ (β + γ) ∧ IsUnit γ

open LocalPresentation in
/-- **([T-E15-NORM] the `ℰ₃`-datum from per-point flex-NF charts ★★, the cover assembly)** An
`IsE3Datum` is exactly a choice, at every point of the base, of a **flex-normal-form chart**
(`a₂=a₄=a₆=0`) marking the order-`3` section `P` at the origin and the second generator `Q` at some
`(p, q)`, together with the `3`-torsion coordinate relation and the unit conditions. This is the
reduction of NORM to its two remaining inputs — both supplied by the torsion→coordinate bridges:
`3•P=0 ⟹ μ_P=0` (which produces the flex-NF chart with `P` at the origin) and `3•Q=0 ⟹ hcubic`. Each
point's data is fed through `isE3Chart`; the `(β,γ)` and the `ℰ₃`-form chart come out. Keystone-free
apart from the bridge outputs carried in the hypothesis. -/
theorem isE3Datum_of_flexCharts {R : CommRingCat.{u}} (X : EllObj R)
    (L : X.curve.FullLevelPt 3)
    (h : ∀ s : X.base, ∃ (V : X.base.affineOpens) (_ : s ∈ V.1)
      (P₀ : LocalPresentation X.curve.toEllipticCurveGeom V) (p q : Γ(X.base, V.1)),
        P₀.W.a₂ = 0 ∧ P₀.W.a₄ = 0 ∧ P₀.W.a₆ = 0 ∧
        P₀.MarksAt L.1.1.2 0 0 ∧ P₀.MarksAt L.1.2.2 p q ∧
        3 * p ^ 3 + P₀.W.a₁ ^ 2 * p ^ 2 + 3 * P₀.W.a₁ * P₀.W.a₃ * p + 3 * P₀.W.a₃ ^ 2 = 0 ∧
        IsUnit P₀.W.a₃ ∧ IsUnit (3 : Γ(X.base, V.1)) ∧
        IsUnit (P₀.W.a₁ ^ 3 * p + P₀.W.a₁ ^ 2 * P₀.W.a₃ + P₀.W.a₁ ^ 2 * q + 6 * P₀.W.a₁ * p ^ 2
          + 3 * P₀.W.a₃ * p + 6 * p * q)) :
    IsE3Datum X L := by
  intro s
  obtain ⟨V, hsV, P₀, p, q, ha₂, ha₄, ha₆, hMP, hMQ, hcubic, ha₃, h3, hB⟩ := h s
  obtain ⟨Pr, β, γ, hE3, hMPr, hMQr, hγu⟩ := isE3Chart P₀ ha₂ ha₄ ha₆ hMP hMQ hcubic ha₃ h3 hB
  exact ⟨V, hsV, Pr, β, γ, hE3, hMPr, hMQr, hγu⟩

open LocalPresentation in
set_option backward.isDefEq.respectTransparency false in
/-- **([T-E15-NORM] the universal `ℰ₃`-datum ★★★, B2-fix-unblocked)** Given the naive-full-
level-`3` clause `hL` for the universal marked pair (the section-level killing `[3]P=[3]Q=0`
+ geometric generation — the [T-E15-NORM] level input, gated on the E[3]/BB-DEG substrate),
the tautologically marked universal `(P, Q)` IS an `ℰ₃`-datum: the tautological presentation
is of `ℰ₃`-form (`universalE3_isE3Form` transported by `IsE3Form.map`), marks `P` at `(0,0)`
and `Q` at `(γ, β+γ)` (`tautPresentation_marksAt_e3P/Q`), and `γ` is a unit (`isUnit_e3Gamma`
— **the B2 fix**, certifying `Q ∉ ⟨P⟩`). Everything but `hL` is now discharged. -/
theorem universalE3_isE3Datum
    (hL : (universalE3Obj R).curve.IsNaiveFullLevel 3
      (universalE3P R) (universalE3Q R)) :
    IsE3Datum (universalE3Obj R) ⟨⟨universalE3P R, universalE3Q R⟩, hL⟩ := by
  haveI : IsAffine (universalE3Obj R).base :=
    inferInstanceAs (IsAffine (Spec (CommRingCat.of (E3ModuliRing R))))
  intro s
  refine ⟨⟨⊤, isAffineOpen_top _⟩, trivial, tautPresentation (universalE3 R),
    (Scheme.ΓSpecIso (CommRingCat.of (E3ModuliRing R))).inv.hom (e3Beta R),
    (Scheme.ΓSpecIso (CommRingCat.of (E3ModuliRing R))).inv.hom (e3Gamma R),
    ?_, ?_, ?_, ?_⟩
  · exact IsE3Form.map _ (universalE3_isE3Form R)
  · have h := tautPresentation_marksAt_e3P R
    rw [map_zero] at h
    exact h
  · have h := tautPresentation_marksAt_e3Q R
    rw [map_add] at h
    exact h
  · exact (isUnit_e3Gamma R).map _

open LocalPresentation in
set_option backward.isDefEq.respectTransparency false in
/-- **([T-E15-NORM] `ℰ₃`-datum functoriality ★)** An `ℰ₃`-datum pulls back along a morphism
`φ : X' ⟶ X` of `Ell/R`-objects: the transported chart is of `ℰ₃`-form (`IsE3Form.map`),
transports the markings (`MarksAt.transport`), and the `γ`-unit persists (`IsUnit.map`).
Adapts `IsLegendreDatum.map`, dropping the ω-basis and adding the `IsUnit γ` clause. -/
theorem IsE3Datum.map {R : CommRingCat.{u}} {X' X : EllObj R} (φ : X' ⟶ X)
    {L : X.curve.FullLevelPt 3} (hD : IsE3Datum X L) (L' : X'.curve.FullLevelPt 3)
    (hL'P : L'.1.1.1 = (EllHom.pullSection R φ L.1.1).1)
    (hL'Q : L'.1.2.1 = (EllHom.pullSection R φ L.1.2).1) :
    IsE3Datum X' L' := by
  intro s'
  obtain ⟨V, hsV, Pr, β, γ, hF, hP, hQ, hγu⟩ := hD (φ.baseHom.base s')
  obtain ⟨V'₀, hV'aff, hs'V', hV'sub⟩ := exists_isAffineOpen_mem_and_subset
    (show s' ∈ (φ.baseHom ⁻¹ᵁ V.1 : X'.base.Opens) from hsV)
  have hle : (⟨V'₀, hV'aff⟩ : X'.base.affineOpens).1 ≤ φ.baseHom ⁻¹ᵁ V.1 := hV'sub
  refine ⟨⟨V'₀, hV'aff⟩, hs'V',
    Pr.transport φ.baseHom φ.top φ.isPullback φ.zero_w hle,
    sectionsMapLE φ.baseHom hle β, sectionsMapLE φ.baseHom hle γ, ?_, ?_, ?_, ?_⟩
  · rw [transport_W]; exact IsE3Form.map _ hF
  · have h0 := MarksAt.transport φ.baseHom φ.top φ.isPullback φ.zero_w hP
      (EllHom.pullSection R φ L.1.1).2
      (φ.isPullback.lift_fst _ _ _) hle
    rw [map_zero] at h0
    exact MarksAt.congr_section hL'P.symm L'.1.1.2 h0
  · have h1 := MarksAt.transport φ.baseHom φ.top φ.isPullback φ.zero_w hQ
      (EllHom.pullSection R φ L.1.2).2
      (φ.isPullback.lift_fst _ _ _) hle
    rw [map_add] at h1
    exact MarksAt.congr_section hL'Q.symm L'.1.2.2 h1
  · exact hγu.map _

open LocalPresentation WeierstrassCurve in
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1600000 in
/-- **(T-E15a stage 6 ★)** Witness `(β,γ)`-values agree on common affines: restrict
both witnesses and apply the KM Ex. 2.2.2 uniqueness. -/
theorem e3_witness_param_agree {R : CommRingCat.{u}} {X : EllObj R}
    {L : X.curve.FullLevelPt 3} (h3 : IsUnit (3 : Γ(X.base, ⊤)))
    {V₁ V₂ : X.base.affineOpens}
    {Pr₁ : LocalPresentation X.curve.toEllipticCurveGeom V₁}
    {Pr₂ : LocalPresentation X.curve.toEllipticCurveGeom V₂}
    {β₁ γ₁ : Γ(X.base, V₁.1)} {β₂ γ₂ : Γ(X.base, V₂.1)}
    (hW₁ : IsE3Form Pr₁.W β₁ γ₁) (hW₂ : IsE3Form Pr₂.W β₂ γ₂)
    (hP₁ : Pr₁.MarksAt L.1.1.2 0 0) (hP₂ : Pr₂.MarksAt L.1.1.2 0 0)
    (hQ₁ : Pr₁.MarksAt L.1.2.2 γ₁ (β₁ + γ₁))
    (hQ₂ : Pr₂.MarksAt L.1.2.2 γ₂ (β₂ + γ₂))
    {W : X.base.affineOpens} (hWV₁ : W.1 ≤ V₁.1) (hWV₂ : W.1 ≤ V₂.1) :
    Scheme.resLE hWV₁ γ₁ = Scheme.resLE hWV₂ γ₂ ∧
      Scheme.resLE hWV₁ β₁ = Scheme.resLE hWV₂ β₂ := by
  have hP₁' := hP₁.restrict hWV₁; have hP₂' := hP₂.restrict hWV₂
  rw [map_zero] at hP₁' hP₂'
  have hQ₁' := hQ₁.restrict hWV₁; have hQ₂' := hQ₂.restrict hWV₂
  rw [map_add] at hQ₁' hQ₂'
  have key := e3_witness_transVC_eq_one
    (restrict_W_e3form hW₁ hWV₁) (restrict_W_e3form hW₂ hWV₂)
    hP₁' hP₂' hQ₁' hQ₂' (isUnit_ofNat_res h3 W.1)
  exact ⟨key.2.1, key.2.2⟩

open LocalPresentation TopologicalSpace in
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 3200000 in
/-- **(T-E15a stage 7)** The glued γ parameter of an `E3` datum. -/
noncomputable def e3GammaGlued {R : CommRingCat.{u}} (X : EllObj R)
    (L : X.curve.FullLevelPt 3) (hD : IsE3Datum X L)
    (h3 : IsUnit (3 : Γ(X.base, ⊤))) :
    { g : Γ(X.base, ⊤) //
      ∀ (V : X.base.affineOpens)
        (Pr : LocalPresentation X.curve.toEllipticCurveGeom V)
        (β γ : Γ(X.base, V.1)), IsE3Form Pr.W β γ →
        Pr.MarksAt L.1.1.2 0 0 → Pr.MarksAt L.1.2.2 γ (β + γ) →
        Scheme.resLE (le_top : V.1 ≤ ⊤) g = γ } := by
  classical
  choose Vx hxVx Prx βx γx hFx hPx hQx _hγux using hD
  have hcover : (⊤ : X.base.Opens) ≤ iSup (fun x : X.base => (Vx x).1) :=
    fun x _ => Opens.mem_iSup.mpr ⟨x, hxVx x⟩
  have hcoverInf : ∀ (V V' : X.base.Opens), V ⊓ V' ≤
      iSup (fun r : {W : X.base.affineOpens // W.1 ≤ V ⊓ V'} => r.1.1) := by
    intro V V' x hx
    obtain ⟨W₀, hWaff, hxW, hWle⟩ := exists_isAffineOpen_mem_and_subset hx
    exact Opens.mem_iSup.mpr ⟨⟨⟨W₀, hWaff⟩, hWle⟩, hxW⟩
  have hpair : TopCat.Presheaf.IsCompatible X.base.sheaf.1
      (fun x : X.base => (Vx x).1) (fun x => γx x) := by
    intro x y
    refine TopCat.Sheaf.eq_of_locally_eq' X.base.sheaf
      (fun r : {W : X.base.affineOpens // W.1 ≤ (Vx x).1 ⊓ (Vx y).1} => r.1.1)
      ((Vx x).1 ⊓ (Vx y).1) (fun r => homOfLE r.2) (hcoverInf _ _) _ _ (fun r => ?_)
    show Scheme.resLE r.2 (Scheme.resLE inf_le_left (γx x)) =
      Scheme.resLE r.2 (Scheme.resLE inf_le_right (γx y))
    rw [Scheme.resLE_resLE, Scheme.resLE_resLE]
    exact (e3_witness_param_agree h3 (hFx x) (hFx y) (hPx x) (hPx y) (hQx x) (hQx y)
      (r.2.trans inf_le_left) (r.2.trans inf_le_right)).1
  have hglue := TopCat.Sheaf.existsUnique_gluing' X.base.sheaf
    (fun x : X.base => (Vx x).1) ⊤ (fun x => homOfLE le_top) hcover
    (fun x => γx x) hpair
  refine ⟨hglue.choose, fun V Pr β γ hF hP hQ => ?_⟩
  refine TopCat.Sheaf.eq_of_locally_eq' X.base.sheaf
    (fun w : {w : X.base.affineOpens × X.base // w.1.1 ≤ V.1 ⊓ (Vx w.2).1} =>
      w.1.1.1) V.1 (fun w => homOfLE (w.2.trans inf_le_left)) ?_ _ _ (fun w => ?_)
  · intro x hxV
    have hx : x ∈ V.1 ⊓ (Vx x).1 := ⟨hxV, hxVx x⟩
    obtain ⟨W₀, hWaff, hxW, hWle⟩ := exists_isAffineOpen_mem_and_subset hx
    exact Opens.mem_iSup.mpr ⟨⟨⟨⟨W₀, hWaff⟩, x⟩, hWle⟩, hxW⟩
  · obtain ⟨⟨W, x⟩, hWle⟩ := w
    show Scheme.resLE (hWle.trans inf_le_left)
        (Scheme.resLE (le_top : V.1 ≤ ⊤) hglue.choose) =
      Scheme.resLE (hWle.trans inf_le_left) γ
    rw [Scheme.resLE_resLE]
    have hg : Scheme.resLE ((hWle.trans inf_le_right).trans
        (le_top : (Vx x).1 ≤ ⊤)) hglue.choose =
        Scheme.resLE (hWle.trans inf_le_right) (γx x) := by
      have h : Scheme.resLE (le_top : (Vx x).1 ≤ ⊤) hglue.choose = γx x :=
        hglue.choose_spec.1 x
      have h' := congrArg (Scheme.resLE (hWle.trans inf_le_right)) h
      rwa [Scheme.resLE_resLE] at h'
    rw [show (hWle.trans inf_le_left).trans (le_top : V.1 ≤ ⊤) =
      ((hWle.trans inf_le_right).trans (le_top : (Vx x).1 ≤ ⊤)) from rfl, hg]
    exact (e3_witness_param_agree h3 (hFx x) hF (hPx x) hP (hQx x) hQ
      (hWle.trans inf_le_right) (hWle.trans inf_le_left)).1

open LocalPresentation TopologicalSpace in
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 3200000 in
/-- **(T-E15a stage 7)** The glued β parameter of an `E3` datum. -/
noncomputable def e3BetaGlued {R : CommRingCat.{u}} (X : EllObj R)
    (L : X.curve.FullLevelPt 3) (hD : IsE3Datum X L)
    (h3 : IsUnit (3 : Γ(X.base, ⊤))) :
    { g : Γ(X.base, ⊤) //
      ∀ (V : X.base.affineOpens)
        (Pr : LocalPresentation X.curve.toEllipticCurveGeom V)
        (β γ : Γ(X.base, V.1)), IsE3Form Pr.W β γ →
        Pr.MarksAt L.1.1.2 0 0 → Pr.MarksAt L.1.2.2 γ (β + γ) →
        Scheme.resLE (le_top : V.1 ≤ ⊤) g = β } := by
  classical
  choose Vx hxVx Prx βx γx hFx hPx hQx _hγux using hD
  have hcover : (⊤ : X.base.Opens) ≤ iSup (fun x : X.base => (Vx x).1) :=
    fun x _ => Opens.mem_iSup.mpr ⟨x, hxVx x⟩
  have hcoverInf : ∀ (V V' : X.base.Opens), V ⊓ V' ≤
      iSup (fun r : {W : X.base.affineOpens // W.1 ≤ V ⊓ V'} => r.1.1) := by
    intro V V' x hx
    obtain ⟨W₀, hWaff, hxW, hWle⟩ := exists_isAffineOpen_mem_and_subset hx
    exact Opens.mem_iSup.mpr ⟨⟨⟨W₀, hWaff⟩, hWle⟩, hxW⟩
  have hpair : TopCat.Presheaf.IsCompatible X.base.sheaf.1
      (fun x : X.base => (Vx x).1) (fun x => βx x) := by
    intro x y
    refine TopCat.Sheaf.eq_of_locally_eq' X.base.sheaf
      (fun r : {W : X.base.affineOpens // W.1 ≤ (Vx x).1 ⊓ (Vx y).1} => r.1.1)
      ((Vx x).1 ⊓ (Vx y).1) (fun r => homOfLE r.2) (hcoverInf _ _) _ _ (fun r => ?_)
    show Scheme.resLE r.2 (Scheme.resLE inf_le_left (βx x)) =
      Scheme.resLE r.2 (Scheme.resLE inf_le_right (βx y))
    rw [Scheme.resLE_resLE, Scheme.resLE_resLE]
    exact (e3_witness_param_agree h3 (hFx x) (hFx y) (hPx x) (hPx y) (hQx x) (hQx y)
      (r.2.trans inf_le_left) (r.2.trans inf_le_right)).2
  have hglue := TopCat.Sheaf.existsUnique_gluing' X.base.sheaf
    (fun x : X.base => (Vx x).1) ⊤ (fun x => homOfLE le_top) hcover
    (fun x => βx x) hpair
  refine ⟨hglue.choose, fun V Pr β γ hF hP hQ => ?_⟩
  refine TopCat.Sheaf.eq_of_locally_eq' X.base.sheaf
    (fun w : {w : X.base.affineOpens × X.base // w.1.1 ≤ V.1 ⊓ (Vx w.2).1} =>
      w.1.1.1) V.1 (fun w => homOfLE (w.2.trans inf_le_left)) ?_ _ _ (fun w => ?_)
  · intro x hxV
    have hx : x ∈ V.1 ⊓ (Vx x).1 := ⟨hxV, hxVx x⟩
    obtain ⟨W₀, hWaff, hxW, hWle⟩ := exists_isAffineOpen_mem_and_subset hx
    exact Opens.mem_iSup.mpr ⟨⟨⟨⟨W₀, hWaff⟩, x⟩, hWle⟩, hxW⟩
  · obtain ⟨⟨W, x⟩, hWle⟩ := w
    show Scheme.resLE (hWle.trans inf_le_left)
        (Scheme.resLE (le_top : V.1 ≤ ⊤) hglue.choose) =
      Scheme.resLE (hWle.trans inf_le_left) β
    rw [Scheme.resLE_resLE]
    have hg : Scheme.resLE ((hWle.trans inf_le_right).trans
        (le_top : (Vx x).1 ≤ ⊤)) hglue.choose =
        Scheme.resLE (hWle.trans inf_le_right) (βx x) := by
      have h : Scheme.resLE (le_top : (Vx x).1 ≤ ⊤) hglue.choose = βx x :=
        hglue.choose_spec.1 x
      have h' := congrArg (Scheme.resLE (hWle.trans inf_le_right)) h
      rwa [Scheme.resLE_resLE] at h'
    rw [show (hWle.trans inf_le_left).trans (le_top : V.1 ≤ ⊤) =
      ((hWle.trans inf_le_right).trans (le_top : (Vx x).1 ≤ ⊤)) from rfl, hg]
    exact (e3_witness_param_agree h3 (hFx x) hF (hPx x) hP (hQx x) hQ
      (hWle.trans inf_le_right) (hWle.trans inf_le_left)).2

open LocalPresentation TopologicalSpace in
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1600000 in
/-- **(T-E15a stage 8)** The glued parameters satisfy the flex relation `β³=(β+γ)³`. -/
theorem e3_glued_flex {R : CommRingCat.{u}} (X : EllObj R)
    (L : X.curve.FullLevelPt 3) (hD : IsE3Datum X L)
    (h3 : IsUnit (3 : Γ(X.base, ⊤))) :
    (e3BetaGlued X L hD h3).1 ^ 3 -
      ((e3BetaGlued X L hD h3).1 + (e3GammaGlued X L hD h3).1) ^ 3 = 0 := by
  classical
  have hDc := hD
  choose Vx hxVx Prx βx γx hFx hPx hQx _hγux using hDc
  have hcover : (⊤ : X.base.Opens) ≤ iSup (fun s : X.base => (Vx s).1) :=
    fun s _ => Opens.mem_iSup.mpr ⟨s, hxVx s⟩
  refine TopCat.Sheaf.eq_of_locally_eq' X.base.sheaf
    (fun s : X.base => (Vx s).1) ⊤ (fun s => homOfLE le_top) hcover _ _ (fun s => ?_)
  have hβ := (e3BetaGlued X L hD h3).2 (Vx s) (Prx s) (βx s) (γx s)
    (hFx s) (hPx s) (hQx s)
  have hγ := (e3GammaGlued X L hD h3).2 (Vx s) (Prx s) (βx s) (γx s)
    (hFx s) (hPx s) (hQx s)
  have hflex := e3form_flex (hFx s) (hQx s).choose
  show Scheme.resLE (le_top : (Vx s).1 ≤ ⊤) _ = Scheme.resLE le_top 0
  rw [map_zero, map_sub, map_pow, map_pow, map_add, hβ, hγ]
  linear_combination -hflex

open LocalPresentation TopologicalSpace WeierstrassCurve in
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1600000 in
/-- **(T-E15a stage 8 ★)** The discriminant factor `(a₁³−27a₃)·a₃` at the glued
parameters is a global unit (germwise: chartwise the witness discriminant, a unit by
ellipticity). -/
theorem e3Delta_glued_isUnit {R : CommRingCat.{u}} (X : EllObj R)
    (L : X.curve.FullLevelPt 3) (hD : IsE3Datum X L)
    (h3 : IsUnit (3 : Γ(X.base, ⊤))) :
    IsUnit ((((3 * (e3GammaGlued X L hD h3).1 - 1) ^ 3 -
        27 * (-3 * (e3GammaGlued X L hD h3).1 ^ 2 - (e3BetaGlued X L hD h3).1 -
          3 * (e3BetaGlued X L hD h3).1 * (e3GammaGlued X L hD h3).1)) *
      (-3 * (e3GammaGlued X L hD h3).1 ^ 2 - (e3BetaGlued X L hD h3).1 -
        3 * (e3BetaGlued X L hD h3).1 * (e3GammaGlued X L hD h3).1)) *
      (e3GammaGlued X L hD h3).1) := by
  set gB := (e3BetaGlued X L hD h3).1 with hgB
  set gG := (e3GammaGlued X L hD h3).1 with hgG
  apply X.base.toRingedSpace.isUnit_of_isUnit_germ
  intro x _
  obtain ⟨V, hxV, Pr, β, γ, hF, hP, hQ, hγu⟩ := hD x
  set D := (((3 * gG - 1) ^ 3 - 27 * (-3 * gG ^ 2 - gB - 3 * gB * gG)) *
    (-3 * gG ^ 2 - gB - 3 * gB * gG)) * gG with hDdef
  have hgerm : X.base.presheaf.germ ⊤ x trivial D =
      X.base.presheaf.germ V.1 x hxV (Scheme.resLE (le_top : V.1 ≤ ⊤) D) := by
    rw [show Scheme.resLE (le_top : V.1 ≤ ⊤) D =
      (X.base.presheaf.map (homOfLE (le_top : V.1 ≤ ⊤)).op).hom D from rfl]
    exact (X.base.presheaf.germ_res_apply (homOfLE le_top) x hxV _).symm
  rw [hgerm]
  refine IsUnit.map _ ?_
  have hβ := (e3BetaGlued X L hD h3).2 V Pr β γ hF hP hQ
  have hγ := (e3GammaGlued X L hD h3).2 V Pr β γ hF hP hQ
  obtain ⟨ha₁, ha₂, ha₃, ha₄, ha₆⟩ := hF
  have hres : Scheme.resLE (le_top : V.1 ≤ ⊤) D =
      (Pr.W.a₁ ^ 3 - 27 * Pr.W.a₃) * Pr.W.a₃ * γ := by
    rw [hDdef]
    simp only [map_mul, map_sub, map_pow, map_neg, map_ofNat, map_one]
    rw [hgB, hgG, hβ, hγ, ha₁, ha₃]
  rw [hres]
  obtain ⟨hu3, huD⟩ := e3form_units ⟨ha₁, ha₂, ha₃, ha₄, ha₆⟩ Pr.elliptic
  exact (huD.mul hu3).mul hγu

open LocalPresentation MvPolynomial in
set_option backward.isDefEq.respectTransparency false in
/-- **(T-E15a stage 9 ★)** The base ring map of an `E3` datum:
`MvPolynomial (Fin 2) R → Γ(X.base, ⊤)`, `X 0 ↦ βGlued, X 1 ↦ γGlued`. -/
noncomputable def e3BaseMap {R : CommRingCat.{u}} (X : EllObj R)
    (L : X.curve.FullLevelPt 3) (hD : IsE3Datum X L)
    (h3 : IsUnit (3 : Γ(X.base, ⊤))) :
    MvPolynomial (Fin 2) R →+* Γ(X.base, ⊤) :=
  eval₂Hom X.baseRingHom ![(e3BetaGlued X L hD h3).1, (e3GammaGlued X L hD h3).1]

open LocalPresentation MvPolynomial in
/-- The base map kills the flex relation, so descends to the flex-locus ring. -/
theorem e3BaseMap_e3Rel {R : CommRingCat.{u}} (X : EllObj R)
    (L : X.curve.FullLevelPt 3) (hD : IsE3Datum X L)
    (h3 : IsUnit (3 : Γ(X.base, ⊤))) :
    e3BaseMap X L hD h3 (e3Rel R) = 0 := by
  rw [e3BaseMap,
    show e3Rel R = MvPolynomial.X 0 ^ 3 - (MvPolynomial.X 0 + MvPolynomial.X 1) ^ 3
      from rfl]
  simp only [map_sub, map_pow, map_add, eval₂Hom_X', Matrix.cons_val_zero,
    Matrix.cons_val_one]
  linear_combination e3_glued_flex X L hD h3

open LocalPresentation MvPolynomial in
set_option backward.isDefEq.respectTransparency false in
/-- The descended map on the flex-locus ring `R[β,γ]/(β³−(β+γ)³)`. -/
noncomputable def e3QuotientMap {R : CommRingCat.{u}} (X : EllObj R)
    (L : X.curve.FullLevelPt 3) (hD : IsE3Datum X L)
    (h3 : IsUnit (3 : Γ(X.base, ⊤))) :
    E3Quotient R →+* Γ(X.base, ⊤) :=
  Ideal.Quotient.lift _ (e3BaseMap X L hD h3) (by
    intro a ha
    rw [Ideal.mem_span_singleton] at ha
    obtain ⟨c, rfl⟩ := ha
    rw [map_mul, e3BaseMap_e3Rel, zero_mul])

open LocalPresentation MvPolynomial in
set_option backward.isDefEq.respectTransparency false in
/-- **(T-E15a stage 9 ★)** The classifying ring map of an `E3` datum:
`R[β,γ][δ⁻¹]/(β³−(β+γ)³) → Γ(X.base, ⊤)` (KM Ex. 2.2.2's map to `ℰ₃`). -/
noncomputable def e3ClassifyingRingHom {R : CommRingCat.{u}} (X : EllObj R)
    (L : X.curve.FullLevelPt 3) (hD : IsE3Datum X L)
    (h3 : IsUnit (3 : Γ(X.base, ⊤))) :
    E3ModuliRing R →+* Γ(X.base, ⊤) := by
  refine IsLocalization.Away.lift (e3Delta R) (g := e3QuotientMap X L hD h3) ?_
  rw [show e3QuotientMap X L hD h3 (e3Delta R) =
      (((3 * (e3GammaGlued X L hD h3).1 - 1) ^ 3 -
        27 * (-3 * (e3GammaGlued X L hD h3).1 ^ 2 - (e3BetaGlued X L hD h3).1 -
          3 * (e3BetaGlued X L hD h3).1 * (e3GammaGlued X L hD h3).1)) *
      (-3 * (e3GammaGlued X L hD h3).1 ^ 2 - (e3BetaGlued X L hD h3).1 -
        3 * (e3BetaGlued X L hD h3).1 * (e3GammaGlued X L hD h3).1)) *
      (e3GammaGlued X L hD h3).1 from by
    show (e3QuotientMap X L hD h3).comp (Ideal.Quotient.mk _)
        ((e3A₁Poly R ^ 3 - 27 * e3A₃Poly R) * e3A₃Poly R * MvPolynomial.X 1) = _
    show e3BaseMap X L hD h3
        ((e3A₁Poly R ^ 3 - 27 * e3A₃Poly R) * e3A₃Poly R * MvPolynomial.X 1) = _
    rw [e3BaseMap]
    simp only [e3A₁Poly, e3A₃Poly, map_mul, map_sub, map_pow, map_neg,
      map_ofNat, map_one, eval₂Hom_X', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons]]
  exact e3Delta_glued_isUnit X L hD h3

open AlgebraicGeometry CategoryTheory Scheme LocalPresentation in
/-- **(T-E15a stage 9)** The classifying morphism `X.base ⟶ ℰ₃ = Spec R[β,γ][δ⁻¹]/(rel)`. -/
noncomputable def e3ClassifyingMap {R : CommRingCat.{u}} (X : EllObj R)
    (L : X.curve.FullLevelPt 3) (hD : IsE3Datum X L)
    (h3 : IsUnit (3 : Γ(X.base, ⊤))) :
    X.base ⟶ Spec (CommRingCat.of (E3ModuliRing R)) :=
  X.base.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (e3ClassifyingRingHom X L hD h3))

open AlgebraicGeometry CategoryTheory Scheme MvPolynomial in
set_option backward.isDefEq.respectTransparency false in
/-- **(T-E15a stage 9)** The classifying algebra restricts to the structure algebra
on `R`-scalars. -/
theorem e3ClassifyingRingHom_algebraMap {R : CommRingCat.{u}} (X : EllObj R)
    (L : X.curve.FullLevelPt 3) (hD : IsE3Datum X L)
    (h3 : IsUnit (3 : Γ(X.base, ⊤))) (r : R) :
    e3ClassifyingRingHom X L hD h3 (algebraMap R (E3ModuliRing R) r) =
      X.baseRingHom r := by
  have h1 : algebraMap R (E3ModuliRing R) r =
      algebraMap (E3Quotient R) (E3ModuliRing R)
        (Ideal.Quotient.mk _ (MvPolynomial.C r)) := by
    rw [IsScalarTower.algebraMap_apply R (E3Quotient R) (E3ModuliRing R),
      IsScalarTower.algebraMap_apply R (MvPolynomial (Fin 2) R) (E3Quotient R)]
    rfl
  rw [h1, e3ClassifyingRingHom, IsLocalization.Away.lift_eq]
  show e3QuotientMap X L hD h3 (Ideal.Quotient.mk _ (MvPolynomial.C r)) = _
  show e3BaseMap X L hD h3 (MvPolynomial.C r) = _
  rw [e3BaseMap, eval₂Hom_C]

open LocalPresentation MvPolynomial in
/-- The classifying map sends the universal `γ` to `γGlued`. -/
theorem e3ClassifyingRingHom_gamma {R : CommRingCat.{u}} (X : EllObj R)
    (L : X.curve.FullLevelPt 3) (hD : IsE3Datum X L)
    (h3 : IsUnit (3 : Γ(X.base, ⊤))) :
    e3ClassifyingRingHom X L hD h3 (e3Gamma R) = (e3GammaGlued X L hD h3).1 := by
  rw [e3Gamma, e3ClassifyingRingHom, IsLocalization.Away.lift_eq]
  show e3QuotientMap X L hD h3 (Ideal.Quotient.mk _ (MvPolynomial.X 1)) = _
  show e3BaseMap X L hD h3 (MvPolynomial.X 1) = _
  rw [e3BaseMap, eval₂Hom_X']
  rfl

open LocalPresentation MvPolynomial in
/-- The classifying map sends the universal `β` to `βGlued`. -/
theorem e3ClassifyingRingHom_beta {R : CommRingCat.{u}} (X : EllObj R)
    (L : X.curve.FullLevelPt 3) (hD : IsE3Datum X L)
    (h3 : IsUnit (3 : Γ(X.base, ⊤))) :
    e3ClassifyingRingHom X L hD h3 (e3Beta R) = (e3BetaGlued X L hD h3).1 := by
  rw [e3Beta, e3ClassifyingRingHom, IsLocalization.Away.lift_eq]
  show e3QuotientMap X L hD h3 (Ideal.Quotient.mk _ (MvPolynomial.X 0)) = _
  show e3BaseMap X L hD h3 (MvPolynomial.X 0) = _
  rw [e3BaseMap, eval₂Hom_X']
  rfl

open LocalPresentation MvPolynomial WeierstrassCurve in
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1600000 in
/-- **(T-E15a stage 10 ★, the E1 coefficient match)** Specializing the universal `ℰ₃`
curve along the classifying map, restricted to a witness affine, recovers the witness
chart curve. -/
theorem universalE3_map_classifying {R : CommRingCat.{u}} (X : EllObj R)
    (L : X.curve.FullLevelPt 3) (hD : IsE3Datum X L)
    (h3 : IsUnit (3 : Γ(X.base, ⊤))) (V : X.base.affineOpens)
    (Pr : LocalPresentation X.curve.toEllipticCurveGeom V) (β γ : Γ(X.base, V.1))
    (hF : IsE3Form Pr.W β γ) (hP : Pr.MarksAt L.1.1.2 0 0)
    (hQ : Pr.MarksAt L.1.2.2 γ (β + γ)) :
    (universalE3 R).map
      (((X.base.presheaf.map (homOfLE (le_top : V.1 ≤ ⊤)).op).hom).comp
        (e3ClassifyingRingHom X L hD h3)) = Pr.W := by
  obtain ⟨ha₁, ha₂, ha₃, ha₄, ha₆⟩ := hF
  have hγ := (e3GammaGlued X L hD h3).2 V Pr β γ ⟨ha₁,ha₂,ha₃,ha₄,ha₆⟩ hP hQ
  have hβ := (e3BetaGlued X L hD h3).2 V Pr β γ ⟨ha₁,ha₂,ha₃,ha₄,ha₆⟩ hP hQ
  have hcγ : ((X.base.presheaf.map (homOfLE (le_top : V.1 ≤ ⊤)).op).hom).comp
      (e3ClassifyingRingHom X L hD h3) (e3Gamma R) = γ := by
    rw [RingHom.comp_apply, e3ClassifyingRingHom_gamma]; exact hγ
  have hcβ : ((X.base.presheaf.map (homOfLE (le_top : V.1 ≤ ⊤)).op).hom).comp
      (e3ClassifyingRingHom X L hD h3) (e3Beta R) = β := by
    rw [RingHom.comp_apply, e3ClassifyingRingHom_beta]; exact hβ
  ext
  · show ((X.base.presheaf.map (homOfLE (le_top : V.1 ≤ ⊤)).op).hom).comp
      (e3ClassifyingRingHom X L hD h3) (universalE3 R).a₁ = _
    rw [show (universalE3 R).a₁ = 3 * e3Gamma R - 1 from rfl, map_sub, map_mul,
      map_ofNat, map_one, hcγ, ha₁]
  · show ((X.base.presheaf.map (homOfLE (le_top : V.1 ≤ ⊤)).op).hom).comp
      (e3ClassifyingRingHom X L hD h3) (universalE3 R).a₂ = _
    rw [show (universalE3 R).a₂ = 0 from rfl, map_zero, ha₂]
  · show ((X.base.presheaf.map (homOfLE (le_top : V.1 ≤ ⊤)).op).hom).comp
      (e3ClassifyingRingHom X L hD h3) (universalE3 R).a₃ = _
    rw [show (universalE3 R).a₃ =
        -3 * e3Gamma R ^ 2 - e3Beta R - 3 * e3Beta R * e3Gamma R from rfl,
      map_sub, map_sub, map_mul, map_neg, map_ofNat, map_pow, map_mul, map_mul,
      map_ofNat, hcγ, hcβ, ha₃]
  · show ((X.base.presheaf.map (homOfLE (le_top : V.1 ≤ ⊤)).op).hom).comp
      (e3ClassifyingRingHom X L hD h3) (universalE3 R).a₄ = _
    rw [show (universalE3 R).a₄ = 0 from rfl, map_zero, ha₄]
  · show ((X.base.presheaf.map (homOfLE (le_top : V.1 ≤ ⊤)).op).hom).comp
      (e3ClassifyingRingHom X L hD h3) (universalE3 R).a₆ = _
    rw [show (universalE3 R).a₆ = 0 from rfl, map_zero, ha₆]

/-- **(T-E15a stage 10)** A bundled `E3` witness. -/
structure E3Witness {R : CommRingCat.{u}} (X : EllObj R)
    (L : X.curve.FullLevelPt 3) where
  V : X.base.affineOpens
  Pr : LocalPresentation X.curve.toEllipticCurveGeom V
  β : Γ(X.base, V.1)
  γ : Γ(X.base, V.1)
  hF : IsE3Form Pr.W β γ
  hP : Pr.MarksAt L.1.1.2 0 0
  hQ : Pr.MarksAt L.1.2.2 γ (β + γ)

open LocalPresentation in
set_option backward.isDefEq.respectTransparency false in
/-- **(T-E15a stage 10)** The per-witness classifying piece. -/
noncomputable def e3Piece {R : CommRingCat.{u}} {X : EllObj R}
    {L : X.curve.FullLevelPt 3} (hD : IsE3Datum X L)
    (h3 : IsUnit (3 : Γ(X.base, ⊤))) (w : E3Witness X L) :
    (pullback X.curve.toEllipticCurveGeom.π w.V.1.ι : Scheme.{u}) ⟶
      projModel (universalE3 R) :=
  w.Pr.e.hom ≫
    eqToHom (congrArg projModel
      (universalE3_map_classifying X L hD h3 w.V w.Pr w.β w.γ w.hF w.hP w.hQ).symm) ≫
    projModelBaseChange
      (((X.base.presheaf.map (homOfLE (le_top : w.V.1 ≤ ⊤)).op).hom).comp
        (e3ClassifyingRingHom X L hD h3)) (universalE3 R)

open LocalPresentation WeierstrassCurve in
set_option backward.isDefEq.respectTransparency false in
/-- **(T-E15a stage 10)** Witnesses restrict. -/
noncomputable def E3Witness.restrict {R : CommRingCat.{u}} {X : EllObj R}
    {L : X.curve.FullLevelPt 3} (w : E3Witness X L)
    {W : X.base.affineOpens} (h : W.1 ≤ w.V.1) : E3Witness X L where
  V := W
  Pr := w.Pr.restrict h
  β := Scheme.resLE h w.β
  γ := Scheme.resLE h w.γ
  hF := restrict_W_e3form w.hF h
  hP := by have := w.hP.restrict h; rwa [map_zero] at this
  hQ := by have := w.hQ.restrict h; rwa [map_add] at this

open LocalPresentation WeierstrassCurve in
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1600000 in
/-- **(T-E15a stage 10)** The pieces are compatible with restriction (KM Ex. 2.2.2
uniqueness). -/
theorem e3Piece_restrict {R : CommRingCat.{u}} {X : EllObj R}
    {L : X.curve.FullLevelPt 3} (hD : IsE3Datum X L)
    (h3 : IsUnit (3 : Γ(X.base, ⊤))) (w w' : E3Witness X L) (h : w'.V.1 ≤ w.V.1) :
    restrictTheta h ≫ e3Piece hD h3 w = e3Piece hD h3 w' := by
  have hPres := w.hP.restrict h; rw [map_zero] at hPres
  have hQres := w.hQ.restrict h; rw [map_add] at hQres
  have hVC : w'.Pr.transVC (w.Pr.restrict h) = 1 :=
    (e3_witness_transVC_eq_one w'.hF (restrict_W_e3form w.hF h)
      w'.hP hPres w'.hQ hQres (isUnit_ofNat_res h3 w'.V.1)).1
  have hWeq : (w.Pr.restrict h).W = w'.Pr.W := by
    have := w'.Pr.transVC_smul (w.Pr.restrict h)
    rwa [hVC, one_smul] at this
  have hIso := pointedIso_hom_of_transVC_eq_one hVC
  have hE : (w.Pr.restrict h).e.hom =
      w'.Pr.e.hom ≫ eqToHom (congrArg projModel hWeq.symm) := by
    have h1 : w'.Pr.e.inv ≫ (w.Pr.restrict h).e.hom =
        eqToHom (congrArg projModel hWeq.symm) := by
      have h0 := hIso
      rw [show (w'.Pr.pointedIso (w.Pr.restrict h)).hom =
        w'.Pr.e.inv ≫ (w.Pr.restrict h).e.hom from rfl] at h0
      exact h0
    rw [← h1, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  have hσ : ((X.base.presheaf.map (homOfLE (le_top : w'.V.1 ≤ ⊤)).op).hom).comp
      (e3ClassifyingRingHom X L hD h3) =
    (sectionsMapLE (𝟙 X.base) h).comp
      (((X.base.presheaf.map (homOfLE (le_top : w.V.1 ≤ ⊤)).op).hom).comp
        (e3ClassifyingRingHom X L hD h3)) := by
    rw [sectionsMapLE_id]
    show ((X.base.presheaf.map (homOfLE (le_top : w'.V.1 ≤ ⊤)).op).hom).comp
        (e3ClassifyingRingHom X L hD h3) =
      (((X.base.presheaf.map (homOfLE (le_top : w.V.1 ≤ ⊤)).op) ≫
        (X.base.presheaf.map (homOfLE (show w'.V.1 ≤ w.V.1 by
          simpa using h)).op)).hom).comp
        (e3ClassifyingRingHom X L hD h3)
    rw [← Functor.map_comp, ← op_comp]
    rfl
  rw [e3Piece, e3Piece, ← Category.assoc, ← restrict_e_baseChange, hE]
  simp only [Category.assoc]
  rw [cancel_epi (w'.Pr.e.hom)]
  rw [projModelBaseChange_congr'' (sectionsMapLE (𝟙 X.base) h)
      (universalE3_map_classifying X L hD h3 w.V w.Pr w.β w.γ
        w.hF w.hP w.hQ).symm]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_trans, eqToHom_refl,
    Category.id_comp]
  rw [← projModelBaseChange_comp',
    projModelBaseChange_congr_hom hσ.symm (universalE3 R),
    ← Category.assoc, eqToHom_trans]

open AlgebraicGeometry CategoryTheory Limits Scheme LocalPresentation in
/-- **(T-E15a stage 10)** The witness cover of the total space. -/
noncomputable def e3WitnessCover {R : CommRingCat.{u}} {X : EllObj R}
    {L : X.curve.FullLevelPt 3} (hD : IsE3Datum X L) :
    X.curve.toEllipticCurveGeom.E.OpenCover :=
  Scheme.Cover.mkOfCovers (E3Witness X L)
    (fun w => pullback X.curve.toEllipticCurveGeom.π w.V.1.ι)
    (fun w => pullback.fst X.curve.toEllipticCurveGeom.π w.V.1.ι)
    (fun x => by
      obtain ⟨V, hxV, Pr, β, γ, hF, hP, hQ, _hγu⟩ := hD
        (X.curve.toEllipticCurveGeom.π.base x)
      have hx : x ∈ Set.range (pullback.fst X.curve.toEllipticCurveGeom.π
          V.1.ι).base := by
        rw [Scheme.Pullback.range_fst, Set.mem_preimage, Scheme.Opens.range_ι,
          SetLike.mem_coe]
        exact hxV
      obtain ⟨y, hy⟩ := hx
      exact ⟨⟨V, Pr, β, γ, hF, hP, hQ⟩, y, hy⟩)

open CategoryTheory Limits in
@[simp] theorem e3WitnessCover_f {R : CommRingCat.{u}} {X : EllObj R}
    {L : X.curve.FullLevelPt 3} (hD : IsE3Datum X L) (w : E3Witness X L) :
    (e3WitnessCover hD).f w =
      pullback.fst X.curve.toEllipticCurveGeom.π w.V.1.ι := rfl

open AlgebraicGeometry CategoryTheory Limits Scheme LocalPresentation WeierstrassCurve in
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1600000 in
/-- **(T-E15a stage 10)** The piece is witness-independent at a fixed affine. -/
theorem e3Piece_congr {R : CommRingCat.{u}} {X : EllObj R}
    {L : X.curve.FullLevelPt 3} (hD : IsE3Datum X L)
    (h3 : IsUnit (3 : Γ(X.base, ⊤)))
    (w₁ w₂ : E3Witness X L) (hV : w₁.V = w₂.V) :
    e3Piece hD h3 w₁ = eqToHom (by rw [hV]) ≫ e3Piece hD h3 w₂ := by
  obtain ⟨V₁, Pr₁, β₁, γ₁, hF₁, hP₁, hQ₁⟩ := w₁
  obtain ⟨V₂, Pr₂, β₂, γ₂, hF₂, hP₂, hQ₂⟩ := w₂
  obtain rfl : V₁ = V₂ := hV
  rw [eqToHom_refl, Category.id_comp]
  have hVC : Pr₂.transVC Pr₁ = 1 :=
    (e3_witness_transVC_eq_one hF₂ hF₁ hP₂ hP₁ hQ₂ hQ₁
      (isUnit_ofNat_res h3 V₁.1)).1
  have hWeq : Pr₁.W = Pr₂.W := by
    have := Pr₂.transVC_smul Pr₁
    rwa [hVC, one_smul] at this
  have hIso := pointedIso_hom_of_transVC_eq_one hVC
  have hE : Pr₁.e.hom = Pr₂.e.hom ≫ eqToHom (congrArg projModel hWeq.symm) := by
    have h1 : Pr₂.e.inv ≫ Pr₁.e.hom = eqToHom (congrArg projModel hWeq.symm) := by
      have h0 := hIso
      rw [show (Pr₂.pointedIso Pr₁).hom = Pr₂.e.inv ≫ Pr₁.e.hom from rfl] at h0
      exact h0
    rw [← h1, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  show Pr₁.e.hom ≫ _ ≫ _ = Pr₂.e.hom ≫ _ ≫ _
  rw [hE]
  simp only [Category.assoc, eqToHom_trans_assoc]

open AlgebraicGeometry CategoryTheory Limits Scheme LocalPresentation in
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 3200000 in
private theorem e3Piece_agree {R : CommRingCat.{u}} {X : EllObj R}
    {L : X.curve.FullLevelPt 3}
    (hD : IsE3Datum X L) (h3 : IsUnit (3 : Γ(X.base, ⊤)))
    (p q : E3Witness X L) :
    pullback.fst ((e3WitnessCover hD).f p) ((e3WitnessCover hD).f q) ≫
        e3Piece hD h3 p =
      pullback.snd ((e3WitnessCover hD).f p) ((e3WitnessCover hD).f q) ≫
        e3Piece hD h3 q := by
  haveI hOIp : IsOpenImmersion ((e3WitnessCover hD).f p) := by
    rw [e3WitnessCover_f]; infer_instance
  haveI hOIq : IsOpenImmersion ((e3WitnessCover hD).f q) := by
    rw [e3WitnessCover_f]; infer_instance
  have hchoice : ∀ z : (pullback ((e3WitnessCover hD).f p)
      ((e3WitnessCover hD).f q) : Scheme.{u}),
      ∃ (W : X.base.affineOpens), W.1 ≤ p.V.1 ⊓ q.V.1 ∧
        X.curve.toEllipticCurveGeom.π.base
          ((pullback.fst ((e3WitnessCover hD).f p)
            ((e3WitnessCover hD).f q) ≫
            (e3WitnessCover hD).f p).base z) ∈ W.1 := by
    intro z
    have hsp : X.curve.toEllipticCurveGeom.π.base
        ((pullback.fst ((e3WitnessCover hD).f p)
          ((e3WitnessCover hD).f q) ≫
          (e3WitnessCover hD).f p).base z) ∈ p.V.1 := by
      have hr : ((pullback.fst ((e3WitnessCover hD).f p)
          ((e3WitnessCover hD).f q) ≫ (e3WitnessCover hD).f p).base z) ∈
          Set.range (pullback.fst X.curve.toEllipticCurveGeom.π p.V.1.ι).base :=
        ⟨(pullback.fst ((e3WitnessCover hD).f p)
          ((e3WitnessCover hD).f q)).base z, rfl⟩
      rw [Scheme.Pullback.range_fst] at hr
      simpa [Scheme.Opens.range_ι] using hr
    have hcond : (pullback.fst ((e3WitnessCover hD).f p)
        ((e3WitnessCover hD).f q) ≫ (e3WitnessCover hD).f p).base z =
      (pullback.snd ((e3WitnessCover hD).f p)
        ((e3WitnessCover hD).f q) ≫ (e3WitnessCover hD).f q).base z := by
      have := congrArg (fun t => t.base z) (pullback.condition
        (f := (e3WitnessCover hD).f p) (g := (e3WitnessCover hD).f q))
      simpa using this
    have hsq : X.curve.toEllipticCurveGeom.π.base
        ((pullback.fst ((e3WitnessCover hD).f p)
          ((e3WitnessCover hD).f q) ≫
          (e3WitnessCover hD).f p).base z) ∈ q.V.1 := by
      have hr : ((pullback.fst ((e3WitnessCover hD).f p)
          ((e3WitnessCover hD).f q) ≫ (e3WitnessCover hD).f p).base z) ∈
          Set.range (pullback.fst X.curve.toEllipticCurveGeom.π q.V.1.ι).base := by
        rw [hcond]
        exact ⟨(pullback.snd ((e3WitnessCover hD).f p)
          ((e3WitnessCover hD).f q)).base z, rfl⟩
      rw [Scheme.Pullback.range_fst] at hr
      simpa [Scheme.Opens.range_ι] using hr
    obtain ⟨W₀, hWaff, hxW, hWle⟩ := exists_isAffineOpen_mem_and_subset
      (show X.curve.toEllipticCurveGeom.π.base
        ((pullback.fst ((e3WitnessCover hD).f p)
          ((e3WitnessCover hD).f q) ≫
          (e3WitnessCover hD).f p).base z) ∈ p.V.1 ⊓ q.V.1 from ⟨hsp, hsq⟩)
    exact ⟨⟨W₀, hWaff⟩, hWle, hxW⟩
  choose W hWle hmem using hchoice
  have hfsteq : ∀ z, (restrictTheta (G := X.curve.toEllipticCurveGeom)
      ((hWle z).trans inf_le_left) ≫ (e3WitnessCover hD).f p) =
    restrictTheta ((hWle z).trans inf_le_right) ≫ (e3WitnessCover hD).f q := by
    intro z
    rw [e3WitnessCover_f, e3WitnessCover_f, restrictTheta_fst,
      restrictTheta_fst]
  let hω : ∀ z, (pullback X.curve.toEllipticCurveGeom.π (W z).1.ι : Scheme.{u}) ⟶
      pullback ((e3WitnessCover hD).f p) ((e3WitnessCover hD).f q) :=
    fun z => pullback.lift (restrictTheta ((hWle z).trans inf_le_left))
      (restrictTheta ((hWle z).trans inf_le_right)) (hfsteq z)
  have hcomp : ∀ z, hω z ≫ pullback.fst ((e3WitnessCover hD).f p)
      ((e3WitnessCover hD).f q) ≫ (e3WitnessCover hD).f p =
    pullback.fst X.curve.toEllipticCurveGeom.π (W z).1.ι := by
    intro z
    rw [← Category.assoc, show hω z ≫ pullback.fst ((e3WitnessCover hD).f p)
        ((e3WitnessCover hD).f q) =
      restrictTheta ((hWle z).trans inf_le_left) from pullback.lift_fst _ _ _,
      e3WitnessCover_f, restrictTheta_fst]
  have hmapOI : ∀ z, IsOpenImmersion (hω z) := by
    intro z
    haveI : IsOpenImmersion (pullback.fst ((e3WitnessCover hD).f p)
        ((e3WitnessCover hD).f q) ≫ (e3WitnessCover hD).f p) :=
      inferInstance
    haveI : IsOpenImmersion (hω z ≫ pullback.fst ((e3WitnessCover hD).f p)
        ((e3WitnessCover hD).f q) ≫ (e3WitnessCover hD).f p) := by
      rw [hcomp z]; infer_instance
    exact IsOpenImmersion.of_comp _ (pullback.fst ((e3WitnessCover hD).f p)
      ((e3WitnessCover hD).f q) ≫ (e3WitnessCover hD).f p)
  refine (Scheme.Cover.mkOfCovers
    (X := (pullback ((e3WitnessCover hD).f p)
      ((e3WitnessCover hD).f q) : Scheme.{u}))
    (pullback ((e3WitnessCover hD).f p) ((e3WitnessCover hD).f q) :
      Scheme.{u})
    (fun z => pullback X.curve.toEllipticCurveGeom.π (W z).1.ι)
    (fun z => hω z) ?_ (fun z => hmapOI z)).hom_ext _ _ (fun z => ?_)
  · intro z
    have hz : (pullback.fst ((e3WitnessCover hD).f p)
        ((e3WitnessCover hD).f q) ≫ (e3WitnessCover hD).f p).base z ∈
      Set.range (pullback.fst X.curve.toEllipticCurveGeom.π (W z).1.ι).base := by
      rw [Scheme.Pullback.range_fst]
      simpa [Scheme.Opens.range_ι] using hmem z
    obtain ⟨w, hw⟩ := hz
    refine ⟨z, w, ?_⟩
    have hinj : Function.Injective
        ((pullback.fst ((e3WitnessCover hD).f p)
          ((e3WitnessCover hD).f q) ≫ (e3WitnessCover hD).f p).base) :=
      (pullback.fst ((e3WitnessCover hD).f p)
        ((e3WitnessCover hD).f q) ≫
        (e3WitnessCover hD).f p).isOpenEmbedding.injective
    apply hinj
    calc (pullback.fst ((e3WitnessCover hD).f p)
          ((e3WitnessCover hD).f q) ≫
          (e3WitnessCover hD).f p).base ((hω z).base w)
        = (hω z ≫ pullback.fst ((e3WitnessCover hD).f p)
            ((e3WitnessCover hD).f q) ≫
            (e3WitnessCover hD).f p).base w := rfl
      _ = (pullback.fst X.curve.toEllipticCurveGeom.π (W z).1.ι).base w := by
          rw [hcomp z]
      _ = _ := hw
  · show hω z ≫ pullback.fst _ _ ≫ e3Piece hD h3 p =
      hω z ≫ pullback.snd _ _ ≫ e3Piece hD h3 q
    rw [← Category.assoc, show hω z ≫ pullback.fst ((e3WitnessCover hD).f p)
        ((e3WitnessCover hD).f q) =
      restrictTheta ((hWle z).trans inf_le_left) from pullback.lift_fst _ _ _,
      ← Category.assoc, show hω z ≫ pullback.snd ((e3WitnessCover hD).f p)
        ((e3WitnessCover hD).f q) =
      restrictTheta ((hWle z).trans inf_le_right) from pullback.lift_snd _ _ _,
      e3Piece_restrict hD h3 p (p.restrict ((hWle z).trans inf_le_left))
        ((hWle z).trans inf_le_left),
      e3Piece_restrict hD h3 q (q.restrict ((hWle z).trans inf_le_right))
        ((hWle z).trans inf_le_right)]
    rw [e3Piece_congr hD h3 (p.restrict ((hWle z).trans inf_le_left))
      (q.restrict ((hWle z).trans inf_le_right)) rfl, eqToHom_refl,
      Category.id_comp]

open AlgebraicGeometry CategoryTheory Limits Scheme LocalPresentation in
/-- **(T-E14-CLS-5 ★★, ≈E4)** The classifying morphism upstairs: the witness-glued
map from the total space to the universal Legendre model (mirrors `classifyingTop`). -/
noncomputable def e3Top {R : CommRingCat.{u}} {X : EllObj R}
    {L : X.curve.FullLevelPt 3}
    (hD : IsE3Datum X L) (h3 : IsUnit (3 : Γ(X.base, ⊤))) :
    X.curve.toEllipticCurveGeom.E ⟶ projModel (universalE3 R) :=
  (e3WitnessCover hD).glueMorphisms
    (fun w => e3Piece hD h3 w)
    (e3Piece_agree hD h3)

open AlgebraicGeometry CategoryTheory Limits Scheme LocalPresentation in
@[reassoc]
theorem e3Top_piece {R : CommRingCat.{u}} {X : EllObj R}
    {L : X.curve.FullLevelPt 3}
    (hD : IsE3Datum X L) (h3 : IsUnit (3 : Γ(X.base, ⊤)))
    (w : E3Witness X L) :
    (e3WitnessCover hD).f w ≫ e3Top hD h3 =
      e3Piece hD h3 w :=
  (e3WitnessCover hD).ι_glueMorphisms _ _ w

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
/-- **(T-E14-CLS-6, ≈E2-π)** The piece map lies over the restricted classifying map
(mirrors `chartPiece_π`). -/
theorem e3Piece_π {R : CommRingCat.{u}} {X : EllObj R}
    {L : X.curve.FullLevelPt 3}
    (hD : IsE3Datum X L) (h3 : IsUnit (3 : Γ(X.base, ⊤)))
    (w : E3Witness X L) :
    e3Piece hD h3 w ≫ projModelπ (universalE3 R) =
      pullback.snd X.curve.toEllipticCurveGeom.π w.V.1.ι ≫ w.V.2.isoSpec.hom ≫
        Spec.map (CommRingCat.ofHom
          (((X.base.presheaf.map (homOfLE (le_top : w.V.1 ≤ ⊤)).op).hom).comp
            (e3ClassifyingRingHom X L hD h3))) := by
  have hw : projModelBaseChange
      (((X.base.presheaf.map (homOfLE (le_top : w.V.1 ≤ ⊤)).op).hom).comp
        (e3ClassifyingRingHom X L hD h3)) (universalE3 R) ≫
      projModelπ (universalE3 R) =
    projModelπ ((universalE3 R).map
      (((X.base.presheaf.map (homOfLE (le_top : w.V.1 ≤ ⊤)).op).hom).comp
        (e3ClassifyingRingHom X L hD h3))) ≫
      Spec.map (CommRingCat.ofHom
        (((X.base.presheaf.map (homOfLE (le_top : w.V.1 ≤ ⊤)).op).hom).comp
          (e3ClassifyingRingHom X L hD h3))) := by
    letI : Algebra (E3ModuliRing R) Γ(X.base, w.V.1) :=
      ((((X.base.presheaf.map (homOfLE (le_top : w.V.1 ≤ ⊤)).op).hom).comp
        (e3ClassifyingRingHom X L hD h3))).toAlgebra
    exact (isPullback_projModelBaseChange (universalE3 R)).w
  rw [e3Piece, Category.assoc, Category.assoc, hw,
    reassoc_of% projModelπ_congr
      (universalE3_map_classifying X L hD h3 w.V w.Pr w.β w.γ
        w.hF w.hP w.hQ).symm]
  rw [← Category.assoc, w.Pr.compat_π, Category.assoc]

open AlgebraicGeometry CategoryTheory Limits Scheme LocalPresentation in
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1600000 in
/-- **(T-E14-CLS-6, ≈E4-π ★)** The glued comparison lies over the classifying map
(mirrors `classifyingTop_π_w`). -/
theorem e3Top_π_w {R : CommRingCat.{u}} {X : EllObj R}
    {L : X.curve.FullLevelPt 3}
    (hD : IsE3Datum X L) (h3 : IsUnit (3 : Γ(X.base, ⊤))) :
    e3Top hD h3 ≫ projModelπ (universalE3 R) =
      X.curve.toEllipticCurveGeom.π ≫ e3ClassifyingMap X L hD h3 := by
  refine (e3WitnessCover hD).hom_ext _ _ (fun w => ?_)
  rw [← Category.assoc, e3Top_piece, e3Piece_π]
  have hsplit : Spec.map (CommRingCat.ofHom
      (((X.base.presheaf.map (homOfLE (le_top : w.V.1 ≤ ⊤)).op).hom).comp
        (e3ClassifyingRingHom X L hD h3))) =
    Spec.map (X.base.presheaf.map (homOfLE (le_top : w.V.1 ≤ ⊤)).op) ≫
      Spec.map (CommRingCat.ofHom (e3ClassifyingRingHom X L hD h3)) := by
    rw [← Spec.map_comp]
    rfl
  rw [hsplit,
    show w.V.2.isoSpec.hom = w.V.1.toSpecΓ from IsAffineOpen.isoSpec_hom _]
  rw [show w.V.1.toSpecΓ ≫
      Spec.map (X.base.presheaf.map (homOfLE (le_top : w.V.1 ≤ ⊤)).op) ≫
      Spec.map (CommRingCat.ofHom (e3ClassifyingRingHom X L hD h3)) =
    (w.V.1.ι ≫ X.base.toSpecΓ) ≫
      Spec.map (CommRingCat.ofHom (e3ClassifyingRingHom X L hD h3)) from by
    rw [← Category.assoc, Scheme.Opens.toSpecΓ_SpecMap_presheaf_map_top]]
  rw [show (w.V.1.ι ≫ X.base.toSpecΓ) ≫
      Spec.map (CommRingCat.ofHom (e3ClassifyingRingHom X L hD h3)) =
    w.V.1.ι ≫ e3ClassifyingMap X L hD h3 from by
    rw [Category.assoc]; rfl]
  rw [← Category.assoc, ← pullback.condition, Category.assoc, e3WitnessCover_f]

open AlgebraicGeometry CategoryTheory Limits Scheme LocalPresentation in
/-- **(T-E14-CLS-6, ≈E4)** The witness cover of the base. -/
noncomputable def e3BaseCover {R : CommRingCat.{u}} {X : EllObj R}
    {L : X.curve.FullLevelPt 3}
    (hD : IsE3Datum X L) : X.base.OpenCover :=
  Scheme.Cover.mkOfCovers
    (E3Witness X L)
    (fun w => w.V.1.toScheme)
    (fun w => w.V.1.ι)
    (fun x => by
      obtain ⟨V, hxV, Pr, lam, hAd, hW, hMP, hMQ, _hγu⟩ := hD x
      exact ⟨⟨V, Pr, lam, hAd, hW, hMP, hMQ⟩, ⟨x, hxV⟩, rfl⟩)

open AlgebraicGeometry CategoryTheory Limits Scheme LocalPresentation in
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1600000 in
/-- **(T-E14-CLS-6 ★, ≈E4-zero)** The glued comparison respects the zero sections
(mirrors `classifyingTop_zero`). -/
theorem e3Top_zero {R : CommRingCat.{u}} {X : EllObj R}
    {L : X.curve.FullLevelPt 3}
    (hD : IsE3Datum X L) (h3 : IsUnit (3 : Γ(X.base, ⊤))) :
    X.curve.toEllipticCurveGeom.zero ≫ e3Top hD h3 =
      e3ClassifyingMap X L hD h3 ≫ projModelZero (universalE3 R) := by
  refine (e3BaseCover hD).hom_ext _ _ (fun w => ?_)
  have hzfac : w.V.1.ι ≫ X.curve.toEllipticCurveGeom.zero =
      pullback.lift (w.V.1.ι ≫ X.curve.toEllipticCurveGeom.zero) (𝟙 _)
        (by rw [Category.assoc, X.curve.toEllipticCurveGeom.zero_π,
          Category.comp_id, Category.id_comp]) ≫
      (e3WitnessCover hD).f w := by
    rw [e3WitnessCover_f, pullback.lift_fst]
  rw [show (e3BaseCover hD).f w = w.V.1.ι from rfl, ← Category.assoc, hzfac,
    Category.assoc, e3Top_piece]
  have hz := w.Pr.compat_zero
  have hlift : pullback.lift (w.V.1.ι ≫ X.curve.toEllipticCurveGeom.zero) (𝟙 _)
      (by rw [Category.assoc, X.curve.toEllipticCurveGeom.zero_π,
        Category.comp_id, Category.id_comp]) ≫ w.Pr.e.hom =
    w.V.2.isoSpec.hom ≫ projModelZero w.Pr.W := by
    rw [← Iso.inv_comp_eq, ← Category.assoc]
    exact hz
  rw [e3Piece, ← Category.assoc, hlift]
  rw [Category.assoc,
    show projModelZero w.Pr.W = projModelZero ((universalE3 R).map
        (((X.base.presheaf.map (homOfLE (le_top : w.V.1 ≤ ⊤)).op).hom).comp
          (e3ClassifyingRingHom X L hD h3))) ≫
      eqToHom (congrArg projModel
        (universalE3_map_classifying X L hD h3 w.V w.Pr w.β w.γ
          w.hF w.hP w.hQ)) from
      projModelZero_congr
        (universalE3_map_classifying X L hD h3 w.V w.Pr w.β w.γ
          w.hF w.hP w.hQ).symm]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  have hbc : projModelZero ((universalE3 R).map
      (((X.base.presheaf.map (homOfLE (le_top : w.V.1 ≤ ⊤)).op).hom).comp
        (e3ClassifyingRingHom X L hD h3))) ≫
      projModelBaseChange
        (((X.base.presheaf.map (homOfLE (le_top : w.V.1 ≤ ⊤)).op).hom).comp
          (e3ClassifyingRingHom X L hD h3)) (universalE3 R) =
    Spec.map (CommRingCat.ofHom
      (((X.base.presheaf.map (homOfLE (le_top : w.V.1 ≤ ⊤)).op).hom).comp
        (e3ClassifyingRingHom X L hD h3))) ≫
      projModelZero (universalE3 R) := by
    letI : Algebra (E3ModuliRing R) Γ(X.base, w.V.1) :=
      ((((X.base.presheaf.map (homOfLE (le_top : w.V.1 ≤ ⊤)).op).hom).comp
        (e3ClassifyingRingHom X L hD h3))).toAlgebra
    exact projModelZero_baseChange (universalE3 R)
  rw [hbc]
  have hsplit : Spec.map (CommRingCat.ofHom
      (((X.base.presheaf.map (homOfLE (le_top : w.V.1 ≤ ⊤)).op).hom).comp
        (e3ClassifyingRingHom X L hD h3))) =
    Spec.map (X.base.presheaf.map (homOfLE (le_top : w.V.1 ≤ ⊤)).op) ≫
      Spec.map (CommRingCat.ofHom (e3ClassifyingRingHom X L hD h3)) := by
    rw [← Spec.map_comp]
    rfl
  rw [← Category.assoc, hsplit,
    show w.V.2.isoSpec.hom = w.V.1.toSpecΓ from IsAffineOpen.isoSpec_hom _]
  rw [show w.V.1.toSpecΓ ≫
      Spec.map (X.base.presheaf.map (homOfLE (le_top : w.V.1 ≤ ⊤)).op) ≫
      Spec.map (CommRingCat.ofHom (e3ClassifyingRingHom X L hD h3)) =
    (w.V.1.ι ≫ X.base.toSpecΓ) ≫
      Spec.map (CommRingCat.ofHom (e3ClassifyingRingHom X L hD h3)) from by
    rw [← Category.assoc, Scheme.Opens.toSpecΓ_SpecMap_presheaf_map_top]]
  rw [show (w.V.1.ι ≫ X.base.toSpecΓ) ≫
      Spec.map (CommRingCat.ofHom (e3ClassifyingRingHom X L hD h3)) =
    w.V.1.ι ≫ e3ClassifyingMap X L hD h3 from by rw [Category.assoc]; rfl]
  simp only [Category.assoc]

open AlgebraicGeometry CategoryTheory Scheme in
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1600000 in
/-- **(T-E14-CLS-6, ≈E4)** The classifying map lies over `Spec R` (mirrors
`classifyingMap_structMap`). -/
theorem e3ClassifyingMap_structMap {R : CommRingCat.{u}} {X : EllObj R}
    {L : X.curve.FullLevelPt 3}
    (hD : IsE3Datum X L) (h3 : IsUnit (3 : Γ(X.base, ⊤))) :
    e3ClassifyingMap X L hD h3 ≫ (universalE3Obj R).structMap =
      X.structMap := by
  show (X.base.toSpecΓ ≫ Spec.map (CommRingCat.ofHom
      (e3ClassifyingRingHom X L hD h3))) ≫
    Spec.map (CommRingCat.ofHom (algebraMap R (E3ModuliRing R))) = X.structMap
  rw [Category.assoc, ← Spec.map_comp,
    show CommRingCat.ofHom (algebraMap R (E3ModuliRing R)) ≫
        CommRingCat.ofHom (e3ClassifyingRingHom X L hD h3) =
      CommRingCat.ofHom (X.baseRingHom) from by
      ext r
      exact e3ClassifyingRingHom_algebraMap X L hD h3 r,
    show CommRingCat.ofHom X.baseRingHom =
      (Scheme.ΓSpecIso R).inv ≫ X.structMap.appTop from rfl,
    Spec.map_comp, ← Scheme.toSpecΓ_naturality_assoc, ← SpecMap_ΓSpecIso_hom R,
    ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id]
  exact Category.comp_id _

open AlgebraicGeometry CategoryTheory Limits Scheme LocalPresentation in
set_option backward.isDefEq.respectTransparency false in
/-- **(T-E14-CLS-6)** The classifying map restricted to a witness affine (mirrors
`restrict_classifyingMap`). -/
theorem restrict_e3ClassifyingMap {R : CommRingCat.{u}} {X : EllObj R}
    {L : X.curve.FullLevelPt 3}
    (hD : IsE3Datum X L) (h3 : IsUnit (3 : Γ(X.base, ⊤)))
    (V : X.base.affineOpens) :
    V.1.ι ≫ e3ClassifyingMap X L hD h3 =
      V.2.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom
        (((X.base.presheaf.map (homOfLE (le_top : V.1 ≤ ⊤)).op).hom).comp
          (e3ClassifyingRingHom X L hD h3))) := by
  have hsplit : Spec.map (CommRingCat.ofHom
      (((X.base.presheaf.map (homOfLE (le_top : V.1 ≤ ⊤)).op).hom).comp
        (e3ClassifyingRingHom X L hD h3))) =
    Spec.map (X.base.presheaf.map (homOfLE (le_top : V.1 ≤ ⊤)).op) ≫
      Spec.map (CommRingCat.ofHom (e3ClassifyingRingHom X L hD h3)) := by
    rw [← Spec.map_comp]
    rfl
  rw [hsplit, show V.2.isoSpec.hom = V.1.toSpecΓ from IsAffineOpen.isoSpec_hom _,
    ← Category.assoc, Scheme.Opens.toSpecΓ_SpecMap_presheaf_map_top, Category.assoc]
  rfl

open AlgebraicGeometry CategoryTheory Limits Scheme LocalPresentation in
set_option backward.isDefEq.respectTransparency false in
/-- **([T-E15-NORM] rt2c helper)** The sectionsMapLE ∘ ΓSpecIso.inv compat for e3ClassifyingMap (adapts sectionsMapLE_legendreClassifyingMap, ω-free). -/
theorem sectionsMapLE_e3ClassifyingMap {R : CommRingCat.{u}} {X : EllObj R}
    {L : X.curve.FullLevelPt 3}
    (hD : IsE3Datum X L) (h3 : IsUnit (3 : Γ(X.base, ⊤)))
    (V : X.base.affineOpens) (hTop : V.1 ≤ e3ClassifyingMap X L hD h3 ⁻¹ᵁ
      (⊤ : (Spec (CommRingCat.of (E3ModuliRing R))).Opens)) :
    (sectionsMapLE (e3ClassifyingMap X L hD h3) hTop).comp
      ((Scheme.ΓSpecIso (CommRingCat.of (E3ModuliRing R))).inv.hom) =
    ((X.base.presheaf.map (homOfLE (le_top : V.1 ≤ ⊤)).op).hom).comp
      (e3ClassifyingRingHom X L hD h3) := by
  have hLm : V.2.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom
      ((sectionsMapLE (e3ClassifyingMap X L hD h3) hTop).comp
        ((Scheme.ΓSpecIso (CommRingCat.of (E3ModuliRing R))).inv.hom))) =
    V.1.ι ≫ e3ClassifyingMap X L hD h3 := by
    rw [show CommRingCat.ofHom
        ((sectionsMapLE (e3ClassifyingMap X L hD h3) hTop).comp
          ((Scheme.ΓSpecIso (CommRingCat.of (E3ModuliRing R))).inv.hom)) =
      (Scheme.ΓSpecIso (CommRingCat.of (E3ModuliRing R))).inv ≫
        (e3ClassifyingMap X L hD h3).appLE ⊤ V.1 hTop from rfl,
      Spec.map_comp,
      show V.2.isoSpec.hom = V.1.toSpecΓ from IsAffineOpen.isoSpec_hom _,
      ← Category.assoc, Scheme.Opens.toSpecΓ_SpecMap_appLE, Category.assoc]
    rw [show (⊤ : (Spec (CommRingCat.of (E3ModuliRing R))).Opens).toSpecΓ ≫
        Spec.map (Scheme.ΓSpecIso (CommRingCat.of (E3ModuliRing R))).inv =
      (⊤ : (Spec (CommRingCat.of (E3ModuliRing R))).Opens).ι from by
      rw [Scheme.Opens.toSpecΓ_top, Category.assoc, ← SpecMap_ΓSpecIso_hom,
        ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id, Category.comp_id]]
    rw [Scheme.Hom.resLE_comp_ι]
  have hRm : V.2.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom
      (((X.base.presheaf.map (homOfLE (le_top : V.1 ≤ ⊤)).op).hom).comp
        (e3ClassifyingRingHom X L hD h3))) =
    V.1.ι ≫ e3ClassifyingMap X L hD h3 :=
    (restrict_e3ClassifyingMap hD h3 V).symm
  have hSpec := hLm.trans hRm.symm
  rw [cancel_epi] at hSpec
  have hofHom := Spec.map_injective hSpec
  exact congrArg CommRingCat.Hom.hom hofHom


open AlgebraicGeometry CategoryTheory Limits Scheme LocalPresentation in
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1600000 in
/-- **(T-E14-CLS-6, ≈E4)** The per-witness classifying square is cartesian (mirrors
`chartPiece_isPullback`). -/
theorem e3Piece_isPullback {R : CommRingCat.{u}} {X : EllObj R}
    {L : X.curve.FullLevelPt 3}
    (hD : IsE3Datum X L) (h3 : IsUnit (3 : Γ(X.base, ⊤)))
    (w : E3Witness X L) :
    IsPullback (e3Piece hD h3 w)
      (pullback.snd X.curve.toEllipticCurveGeom.π w.V.1.ι)
      (projModelπ (universalE3 R))
      (w.V.2.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom
        (((X.base.presheaf.map (homOfLE (le_top : w.V.1 ≤ ⊤)).op).hom).comp
          (e3ClassifyingRingHom X L hD h3)))) := by
  have hleft : IsPullback
      (w.Pr.e.hom ≫ eqToHom (congrArg projModel
        (universalE3_map_classifying X L hD h3 w.V w.Pr w.β w.γ
          w.hF w.hP w.hQ).symm))
      (pullback.snd X.curve.toEllipticCurveGeom.π w.V.1.ι)
      (projModelπ ((universalE3 R).map
        (((X.base.presheaf.map (homOfLE (le_top : w.V.1 ≤ ⊤)).op).hom).comp
          (e3ClassifyingRingHom X L hD h3))))
      w.V.2.isoSpec.hom := by
    refine IsPullback.of_horiz_isIso ⟨?_⟩
    rw [Category.assoc, projModelπ_congr
      (universalE3_map_classifying X L hD h3 w.V w.Pr w.β w.γ
        w.hF w.hP w.hQ).symm]
    exact w.Pr.compat_π
  have hright : IsPullback
      (projModelBaseChange
        (((X.base.presheaf.map (homOfLE (le_top : w.V.1 ≤ ⊤)).op).hom).comp
          (e3ClassifyingRingHom X L hD h3)) (universalE3 R))
      (projModelπ ((universalE3 R).map
        (((X.base.presheaf.map (homOfLE (le_top : w.V.1 ≤ ⊤)).op).hom).comp
          (e3ClassifyingRingHom X L hD h3))))
      (projModelπ (universalE3 R))
      (Spec.map (CommRingCat.ofHom
        (((X.base.presheaf.map (homOfLE (le_top : w.V.1 ≤ ⊤)).op).hom).comp
          (e3ClassifyingRingHom X L hD h3)))) := by
    letI : Algebra (E3ModuliRing R) Γ(X.base, w.V.1) :=
      ((((X.base.presheaf.map (homOfLE (le_top : w.V.1 ≤ ⊤)).op).hom).comp
        (e3ClassifyingRingHom X L hD h3))).toAlgebra
    exact isPullback_projModelBaseChange (universalE3 R)
  have hpaste := hleft.paste_horiz hright
  rw [show (w.Pr.e.hom ≫ eqToHom (congrArg projModel
      (universalE3_map_classifying X L hD h3 w.V w.Pr w.β w.γ
        w.hF w.hP w.hQ).symm)) ≫
    projModelBaseChange
      (((X.base.presheaf.map (homOfLE (le_top : w.V.1 ≤ ⊤)).op).hom).comp
        (e3ClassifyingRingHom X L hD h3)) (universalE3 R) =
    e3Piece hD h3 w from by
    rw [e3Piece, Category.assoc]] at hpaste
  exact hpaste

open AlgebraicGeometry CategoryTheory Limits Scheme LocalPresentation in
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 3200000 in
/-- **(T-E14-CLS-6 ★★, ≈E4)** The classifying square is cartesian: `X` is the
pullback of the universal Legendre curve along the classifying map (mirrors
`isPullback_classifyingTop`). -/
theorem isPullback_e3Top {R : CommRingCat.{u}} {X : EllObj R}
    {L : X.curve.FullLevelPt 3}
    (hD : IsE3Datum X L) (h3 : IsUnit (3 : Γ(X.base, ⊤))) :
    IsPullback (e3Top hD h3) X.curve.toEllipticCurveGeom.π
      (projModelπ (universalE3 R)) (e3ClassifyingMap X L hD h3) := by
  refine (isPullback_of_iSup_eq_top (f := X.curve.toEllipticCurveGeom.π)
    (g := e3Top hD h3) (h := e3ClassifyingMap X L hD h3)
    (k := projModelπ (universalE3 R))
    (e3Top_π_w hD h3).symm
    (ι := E3Witness X L)
    (fun w => w.V.1) ?_ (fun w => ?_)).flip
  · rw [eq_top_iff]
    intro x _
    obtain ⟨V, hxV, Pr, lam, hAd, hW, hMP, hMQ, _hγu⟩ := hD x
    exact TopologicalSpace.Opens.mem_iSup.mpr
      ⟨⟨V, Pr, lam, hAd, hW, hMP, hMQ⟩, hxV⟩
  · set fpre := (X.curve.toEllipticCurveGeom.π ⁻¹ᵁ w.V.1).ι with hfpre
    have hcomm : fpre ≫ X.curve.toEllipticCurveGeom.π =
        (X.curve.toEllipticCurveGeom.π ∣_ w.V.1) ≫ w.V.1.ι :=
      (morphismRestrict_ι X.curve.toEllipticCurveGeom.π w.V.1).symm
    set m := pullback.lift fpre (X.curve.toEllipticCurveGeom.π ∣_ w.V.1) hcomm
      with hm
    have hm₁ : m ≫ pullback.fst X.curve.toEllipticCurveGeom.π w.V.1.ι = fpre :=
      pullback.lift_fst _ _ _
    have hm₂ : m ≫ pullback.snd X.curve.toEllipticCurveGeom.π w.V.1.ι =
        X.curve.toEllipticCurveGeom.π ∣_ w.V.1 :=
      pullback.lift_snd _ _ _
    have hmiso : IsIso m := by
      refine (isPullback_morphismRestrict X.curve.toEllipticCurveGeom.π
        w.V.1).flip.isIso_of_isPullback
        (IsPullback.of_hasPullback X.curve.toEllipticCurveGeom.π w.V.1.ι) m hm₁ hm₂
    have hmsq : IsPullback m (X.curve.toEllipticCurveGeom.π ∣_ w.V.1)
        (pullback.snd X.curve.toEllipticCurveGeom.π w.V.1.ι) (𝟙 _) :=
      IsPullback.of_horiz_isIso ⟨by rw [hm₂, Category.comp_id]⟩
    have hp := hmsq.paste_horiz (e3Piece_isPullback hD h3 w)
    rw [show m ≫ e3Piece hD h3 w =
        (X.curve.toEllipticCurveGeom.π ⁻¹ᵁ w.V.1).ι ≫ e3Top hD h3 from by
        rw [← e3Top_piece hD h3 w, e3WitnessCover_f, ← Category.assoc,
          hm₁],
      show (𝟙 _) ≫ w.V.2.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom
          (((X.base.presheaf.map (homOfLE (le_top : w.V.1 ≤ ⊤)).op).hom).comp
            (e3ClassifyingRingHom X L hD h3))) =
        w.V.1.ι ≫ e3ClassifyingMap X L hD h3 from by
        rw [Category.id_comp, ← restrict_e3ClassifyingMap]] at hp
    exact hp.flip

open AlgebraicGeometry CategoryTheory Scheme in
set_option backward.isDefEq.respectTransparency false in
/-- **(T-E14-CLS-6 ★★)** The classifying morphism of a Legendre datum in `Ell/R`:
KM 4.6.2's universal property, forward direction (mirrors `classifyingEllHom`). -/
noncomputable def e3ClassifyingEllHom {R : CommRingCat.{u}} {X : EllObj R}
    {L : X.curve.FullLevelPt 3}
    (hD : IsE3Datum X L) (h3 : IsUnit (3 : Γ(X.base, ⊤))) :
    X ⟶ universalE3Obj R where
  baseHom := e3ClassifyingMap X L hD h3
  base_w := e3ClassifyingMap_structMap hD h3
  top := e3Top hD h3
  isPullback := isPullback_e3Top hD h3
  zero_w := e3Top_zero hD h3

open AlgebraicGeometry CategoryTheory Limits Scheme LocalPresentation in
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1600000 in
/-- **(T-E15a stage 11, rt1)** The marking downstairs: a marked section composed with
the glued comparison is the classifying map followed by the universal marked point. -/
theorem section_comp_e3Top {R : CommRingCat.{u}} {X : EllObj R}
    {L : X.curve.FullLevelPt 3} (hD : IsE3Datum X L)
    (h3 : IsUnit (3 : Γ(X.base, ⊤)))
    {σ : X.base ⟶ X.curve.toEllipticCurveGeom.E}
    (hσ : σ ≫ X.curve.toEllipticCurveGeom.π = 𝟙 X.base) (p q : E3ModuliRing R)
    (hpq : (universalE3 R).toAffine.Equation p q)
    (hmark : ∀ w : E3Witness X L,
      w.Pr.MarksAt hσ
        (((X.base.presheaf.map (homOfLE (le_top : w.V.1 ≤ ⊤)).op).hom)
          (e3ClassifyingRingHom X L hD h3 p))
        (((X.base.presheaf.map (homOfLE (le_top : w.V.1 ≤ ⊤)).op).hom)
          (e3ClassifyingRingHom X L hD h3 q))) :
    σ ≫ e3Top hD h3 =
      e3ClassifyingMap X L hD h3 ≫
        projModelAffineSection (universalE3 R) p q hpq := by
  refine (e3BaseCover hD).hom_ext _ _ (fun w => ?_)
  show w.V.1.ι ≫ σ ≫ e3Top hD h3 = _
  have hfac : w.V.1.ι ≫ σ =
      sectionLift X.curve.toEllipticCurveGeom hσ w.V ≫
        (e3WitnessCover hD).f w := by
    rw [e3WitnessCover_f]
    unfold sectionLift
    rw [pullback.lift_fst]
  rw [← Category.assoc, hfac, Category.assoc, e3Top_piece]
  obtain ⟨hpq', hMeq⟩ := hmark w
  have hMeq' : sectionLift X.curve.toEllipticCurveGeom hσ w.V ≫ w.Pr.e.hom =
      w.V.2.isoSpec.hom ≫ projModelAffineSection w.Pr.W _ _ hpq' := by
    calc sectionLift X.curve.toEllipticCurveGeom hσ w.V ≫ w.Pr.e.hom
        = w.V.2.isoSpec.hom ≫ (w.V.2.isoSpec.inv ≫
            sectionLift X.curve.toEllipticCurveGeom hσ w.V) ≫ w.Pr.e.hom := by
          rw [← Category.assoc, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]
      _ = _ := by rw [hMeq]
  rw [e3Piece, ← Category.assoc, hMeq']
  rw [Category.assoc, ← Category.assoc (projModelAffineSection w.Pr.W _ _ hpq'),
    projModelAffineSection_congr
      (universalE3_map_classifying X L hD h3 w.V w.Pr w.β w.γ
        w.hF w.hP w.hQ).symm]
  letI : Algebra (E3ModuliRing R) Γ(X.base, w.V.1) :=
    ((((X.base.presheaf.map (homOfLE (le_top : w.V.1 ≤ ⊤)).op).hom).comp
      (e3ClassifyingRingHom X L hD h3))).toAlgebra
  have hbc := projModelAffineSection_baseChange (universalE3 R) p q hpq
    (WeierstrassCurve.Affine.Equation.map (algebraMap (E3ModuliRing R)
      Γ(X.base, w.V.1)) hpq)
  rw [show projModelAffineSection ((universalE3 R).map
      (((X.base.presheaf.map (homOfLE (le_top : w.V.1 ≤ ⊤)).op).hom).comp
        (e3ClassifyingRingHom X L hD h3)))
      (((X.base.presheaf.map (homOfLE (le_top : w.V.1 ≤ ⊤)).op).hom)
        (e3ClassifyingRingHom X L hD h3 p))
      (((X.base.presheaf.map (homOfLE (le_top : w.V.1 ≤ ⊤)).op).hom)
        (e3ClassifyingRingHom X L hD h3 q))
      ((universalE3_map_classifying X L hD h3 w.V w.Pr w.β w.γ
        w.hF w.hP w.hQ).symm ▸ hpq') ≫
      projModelBaseChange
        (((X.base.presheaf.map (homOfLE (le_top : w.V.1 ≤ ⊤)).op).hom).comp
          (e3ClassifyingRingHom X L hD h3))
        (universalE3 R) =
    Spec.map (CommRingCat.ofHom
      (((X.base.presheaf.map (homOfLE (le_top : w.V.1 ≤ ⊤)).op).hom).comp
        (e3ClassifyingRingHom X L hD h3))) ≫
      projModelAffineSection (universalE3 R) p q hpq from hbc]
  rw [← Category.assoc, ← restrict_e3ClassifyingMap hD h3 w.V, Category.assoc]
  rfl

open AlgebraicGeometry CategoryTheory Scheme LocalPresentation in
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1600000 in
/-- **(T-E15a stage 11, rt1 ★★)** Pulling the universal marked `P` back recovers `P`. -/
theorem pullSection_e3ClassifyingEllHom_P {R : CommRingCat.{u}} {X : EllObj R}
    {L : X.curve.FullLevelPt 3} (hD : IsE3Datum X L)
    (h3 : IsUnit (3 : Γ(X.base, ⊤))) :
    EllHom.pullSection R (e3ClassifyingEllHom hD h3) (universalE3P R) = L.1.1 := by
  have hdown : L.1.1.1 ≫ e3Top hD h3 =
      e3ClassifyingMap X L hD h3 ≫
        projModelAffineSection (universalE3 R) 0 0 (universalE3_equation_zero R) := by
    refine section_comp_e3Top hD h3 L.1.1.2 0 0 (universalE3_equation_zero R)
      (fun w => ?_)
    have hz : ((X.base.presheaf.map (homOfLE (le_top : w.V.1 ≤ ⊤)).op).hom)
        (e3ClassifyingRingHom X L hD h3 (0 : E3ModuliRing R)) =
      (0 : Γ(X.base, w.V.1)) := by rw [map_zero, map_zero]
    rw [hz]; exact w.hP
  refine Subtype.ext ?_
  refine (e3ClassifyingEllHom hD h3).isPullback.hom_ext ?_ ?_
  · rw [show (EllHom.pullSection R (e3ClassifyingEllHom hD h3)
        (universalE3P R)).1 ≫ (e3ClassifyingEllHom hD h3).top =
      (e3ClassifyingEllHom hD h3).baseHom ≫ (universalE3P R).1
      from (e3ClassifyingEllHom hD h3).isPullback.lift_fst _ _ _]
    show _ = L.1.1.1 ≫ e3Top hD h3
    rw [hdown]; rfl
  · rw [show (EllHom.pullSection R (e3ClassifyingEllHom hD h3)
        (universalE3P R)).1 ≫ X.curve.π = 𝟙 X.base from
      (EllHom.pullSection R (e3ClassifyingEllHom hD h3) (universalE3P R)).2]
    exact L.1.1.2.symm

open AlgebraicGeometry CategoryTheory Scheme LocalPresentation in
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1600000 in
/-- **(T-E15a stage 11, rt1 ★★)** Pulling the universal marked `Q` back recovers `Q`. -/
theorem pullSection_e3ClassifyingEllHom_Q {R : CommRingCat.{u}} {X : EllObj R}
    {L : X.curve.FullLevelPt 3} (hD : IsE3Datum X L)
    (h3 : IsUnit (3 : Γ(X.base, ⊤))) :
    EllHom.pullSection R (e3ClassifyingEllHom hD h3) (universalE3Q R) = L.1.2 := by
  have hdown : L.1.2.1 ≫ e3Top hD h3 =
      e3ClassifyingMap X L hD h3 ≫
        projModelAffineSection (universalE3 R) (e3Gamma R) (e3Beta R + e3Gamma R)
          (universalE3_equation_Q R) := by
    refine section_comp_e3Top hD h3 L.1.2.2 (e3Gamma R) (e3Beta R + e3Gamma R)
      (universalE3_equation_Q R) (fun w => ?_)
    have hg : ((X.base.presheaf.map (homOfLE (le_top : w.V.1 ≤ ⊤)).op).hom)
        (e3ClassifyingRingHom X L hD h3 (e3Gamma R)) = w.γ := by
      rw [e3ClassifyingRingHom_gamma]
      exact (e3GammaGlued X L hD h3).2 w.V w.Pr w.β w.γ w.hF w.hP w.hQ
    have hb : ((X.base.presheaf.map (homOfLE (le_top : w.V.1 ≤ ⊤)).op).hom)
        (e3ClassifyingRingHom X L hD h3 (e3Beta R + e3Gamma R)) = w.β + w.γ := by
      rw [map_add, e3ClassifyingRingHom_beta, e3ClassifyingRingHom_gamma, map_add,
        (e3BetaGlued X L hD h3).2 w.V w.Pr w.β w.γ w.hF w.hP w.hQ,
        (e3GammaGlued X L hD h3).2 w.V w.Pr w.β w.γ w.hF w.hP w.hQ]
    rw [hg, hb]; exact w.hQ
  refine Subtype.ext ?_
  refine (e3ClassifyingEllHom hD h3).isPullback.hom_ext ?_ ?_
  · rw [show (EllHom.pullSection R (e3ClassifyingEllHom hD h3)
        (universalE3Q R)).1 ≫ (e3ClassifyingEllHom hD h3).top =
      (e3ClassifyingEllHom hD h3).baseHom ≫ (universalE3Q R).1
      from (e3ClassifyingEllHom hD h3).isPullback.lift_fst _ _ _]
    show _ = L.1.2.1 ≫ e3Top hD h3
    rw [hdown]; rfl
  · rw [show (EllHom.pullSection R (e3ClassifyingEllHom hD h3)
        (universalE3Q R)).1 ≫ X.curve.π = 𝟙 X.base from
      (EllHom.pullSection R (e3ClassifyingEllHom hD h3) (universalE3Q R)).2]
    exact L.1.2.2.symm

open CategoryTheory in
/-- **([T-E15-NORM] the `ℰ₃` datum problem)** The subfunctor of the naive level-`3`
problem cut out by "the marked pair is an `ℰ₃`-datum" (locally normalisable to `ℰ₃`-form).
This — like the Legendre `δ` — is the object whose representability by `universalE3Obj` is
the KM 4.7.0 `(3, GL₂(𝔽₃))`-engine input over `ℤ[1/3]`. Adapts `legendreDeltaProblem`,
dropping the ω-basis factor (the `ℰ₃`-form is rigid without a chosen invariant differential). -/
noncomputable def e3DatumProblem (R : CommRingCat.{u}) : ModuliProblem R where
  obj X := { x : (gammaFullNaiveProblem R 3).obj X // IsE3Datum X.unop x }
  map φ := ↾fun x => ⟨(gammaFullNaiveProblem R 3).map φ x.1,
    IsE3Datum.map φ.unop x.2 _ rfl rfl⟩
  map_id X := by
    ext x
    exact FunctorToTypes.map_id_apply (gammaFullNaiveProblem R 3) x.1
  map_comp {X Y Z} φ ψ := by
    ext x
    exact FunctorToTypes.map_comp_apply (gammaFullNaiveProblem R 3) φ ψ x.1

section Rt2

variable {R : CommRingCat.{u}} {X : EllObj R} (φ : X ⟶ universalE3Obj R)
  (hL : (universalE3Obj R).curve.IsNaiveFullLevel 3
    (universalE3P R) (universalE3Q R))

open AlgebraicGeometry CategoryTheory Scheme LocalPresentation in
set_option backward.isDefEq.respectTransparency false in
/-- **([T-E15-NORM] rt2 prerequisite ★)** The pulled-witness family: over each affine `V`
of `X.base`, the tautological universal `ℰ₃`-chart transported along `φ` is an `E3Witness`
for the pulled datum. Adapts Legendre's `pulledWitness` (drops the ω-basis `lam`/`hAd`,
carries `β, γ` + `IsE3Form`; the `Q`-marking is at `(γ, β+γ)`). -/
noncomputable def e3PulledWitness (V : X.base.affineOpens) :
    E3Witness X ((gammaFullNaiveProblem R 3).map (Opposite.op φ)
      ⟨⟨universalE3P R, universalE3Q R⟩, hL⟩) := by
  refine
    { V := V
      Pr := (tautPresentation (universalE3 R)).transport
        φ.baseHom φ.top φ.isPullback φ.zero_w
        (show V.1 ≤ φ.baseHom ⁻¹ᵁ
          (⟨⊤, isAffineOpen_top _⟩ : (Spec (CommRingCat.of
            (E3ModuliRing R))).affineOpens).1 from fun x _ => trivial)
      β := sectionsMapLE φ.baseHom
        (show V.1 ≤ φ.baseHom ⁻¹ᵁ
          (⟨⊤, isAffineOpen_top _⟩ : (Spec (CommRingCat.of
            (E3ModuliRing R))).affineOpens).1 from fun x _ => trivial)
        ((Scheme.ΓSpecIso (CommRingCat.of (E3ModuliRing R))).inv.hom (e3Beta R))
      γ := sectionsMapLE φ.baseHom
        (show V.1 ≤ φ.baseHom ⁻¹ᵁ
          (⟨⊤, isAffineOpen_top _⟩ : (Spec (CommRingCat.of
            (E3ModuliRing R))).affineOpens).1 from fun x _ => trivial)
        ((Scheme.ΓSpecIso (CommRingCat.of (E3ModuliRing R))).inv.hom (e3Gamma R))
      hF := ?_
      hP := ?_
      hQ := ?_ }
  · rw [transport_W]; exact IsE3Form.map _ (IsE3Form.map _ (universalE3_isE3Form R))
  · have hmark := tautPresentation_marksAt_e3P R
    rw [map_zero] at hmark
    have hcomm : (EllHom.pullSection R φ (universalE3P R)).1 ≫ φ.top =
        φ.baseHom ≫ (universalE3P R).1 := φ.isPullback.lift_fst _ _ _
    have htr := LocalPresentation.MarksAt.transport φ.baseHom φ.top
      φ.isPullback φ.zero_w hmark
      (EllHom.pullSection R φ (universalE3P R)).2 hcomm
      (V' := V) (fun x _ => trivial)
    rw [map_zero] at htr
    exact htr
  · have hmark := tautPresentation_marksAt_e3Q R
    rw [map_add] at hmark
    have hcomm : (EllHom.pullSection R φ (universalE3Q R)).1 ≫ φ.top =
        φ.baseHom ≫ (universalE3Q R).1 := φ.isPullback.lift_fst _ _ _
    have htr := LocalPresentation.MarksAt.transport φ.baseHom φ.top
      φ.isPullback φ.zero_w hmark
      (EllHom.pullSection R φ (universalE3Q R)).2 hcomm
      (V' := V) (fun x _ => trivial)
    rw [map_add] at htr
    exact htr

open AlgebraicGeometry CategoryTheory Scheme LocalPresentation MvPolynomial in
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 3200000 in
/-- **([T-E15-NORM] rt2a ★)** The classifying ring map of the pulled datum is the ring map
of `φ` itself. Adapts Legendre's `legendreClassifyingRingHom_pulled`: `R`-scalars via
`base_w` (`hψR`), then the **two** generators `γ, β` via the pulled-witness family +
`e3GammaGlued`/`e3BetaGlued`'s universal specs (`hnat_γ`, `hnat_β`); the ext peels the `Away`
localization, then the **`E3Quotient` layer** (`mk_surjective` + `MvPolynomial.induction_on`),
then closes on `R`/`β`/`γ`. -/
theorem e3ClassifyingRingHom_pulled (h3 : IsUnit (3 : Γ(X.base, ⊤))) :
    e3ClassifyingRingHom X
      ((gammaFullNaiveProblem R 3).map (Opposite.op φ)
        ⟨⟨universalE3P R, universalE3Q R⟩, hL⟩)
      (IsE3Datum.map φ (universalE3_isE3Datum R hL)
        ((gammaFullNaiveProblem R 3).map (Opposite.op φ)
          ⟨⟨universalE3P R, universalE3Q R⟩, hL⟩) rfl rfl) h3 =
    ((Scheme.ΓSpecIso (CommRingCat.of (E3ModuliRing R))).inv ≫
      φ.baseHom.appTop).hom := by
  set hD' := IsE3Datum.map φ (universalE3_isE3Datum R hL)
    ((gammaFullNaiveProblem R 3).map (Opposite.op φ)
      ⟨⟨universalE3P R, universalE3Q R⟩, hL⟩) rfl rfl with hD'def
  have hψR : ∀ r : R,
      ((Scheme.ΓSpecIso (CommRingCat.of (E3ModuliRing R))).inv ≫
        φ.baseHom.appTop).hom (algebraMap R (E3ModuliRing R) r) = X.baseRingHom r := by
    intro r
    have hb : CommRingCat.ofHom (algebraMap R (E3ModuliRing R)) ≫
        (Scheme.ΓSpecIso (CommRingCat.of (E3ModuliRing R))).inv ≫ φ.baseHom.appTop =
        CommRingCat.ofHom X.baseRingHom := by
      rw [Scheme.ΓSpecIso_inv_naturality_assoc, ← Scheme.Hom.comp_appTop,
        show φ.baseHom ≫ Spec.map (CommRingCat.ofHom
            (algebraMap R (E3ModuliRing R))) = X.structMap from φ.base_w]
      rfl
    exact congrArg (fun g => CommRingCat.Hom.hom g r) hb
  have hcover : (⊤ : X.base.Opens) ≤
      iSup (fun V : X.base.affineOpens => V.1) := by
    intro x _
    obtain ⟨V₀, hVaff, hxV, -⟩ := exists_isAffineOpen_mem_and_subset
      (show x ∈ (⊤ : X.base.Opens) from trivial)
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨V₀, hVaff⟩, hxV⟩
  have hnat_γ : (e3GammaGlued X _ hD' h3).1 =
      ((Scheme.ΓSpecIso (CommRingCat.of (E3ModuliRing R))).inv ≫
        φ.baseHom.appTop).hom (e3Gamma R) := by
    refine TopCat.Sheaf.eq_of_locally_eq' X.base.sheaf
      (fun V : X.base.affineOpens => V.1) ⊤
      (fun V => homOfLE le_top) hcover _ _ (fun V => ?_)
    show Scheme.resLE le_top (e3GammaGlued X _ hD' h3).1 =
      Scheme.resLE le_top
        (((Scheme.ΓSpecIso (CommRingCat.of (E3ModuliRing R))).inv ≫
          φ.baseHom.appTop).hom (e3Gamma R))
    have hres : Scheme.resLE (le_top : V.1 ≤ ⊤)
        (((Scheme.ΓSpecIso (CommRingCat.of (E3ModuliRing R))).inv ≫
          φ.baseHom.appTop).hom (e3Gamma R)) =
        sectionsMapLE φ.baseHom
          (show V.1 ≤ φ.baseHom ⁻¹ᵁ
            (⟨⊤, isAffineOpen_top _⟩ : (Spec (CommRingCat.of
              (E3ModuliRing R))).affineOpens).1 from fun x _ => trivial)
          ((Scheme.ΓSpecIso (CommRingCat.of (E3ModuliRing R))).inv.hom
            (e3Gamma R)) := rfl
    rw [hres]
    exact (e3GammaGlued X _ hD' h3).2
      (e3PulledWitness φ hL V).V (e3PulledWitness φ hL V).Pr
      (e3PulledWitness φ hL V).β (e3PulledWitness φ hL V).γ
      (e3PulledWitness φ hL V).hF (e3PulledWitness φ hL V).hP
      (e3PulledWitness φ hL V).hQ
  have hnat_β : (e3BetaGlued X _ hD' h3).1 =
      ((Scheme.ΓSpecIso (CommRingCat.of (E3ModuliRing R))).inv ≫
        φ.baseHom.appTop).hom (e3Beta R) := by
    refine TopCat.Sheaf.eq_of_locally_eq' X.base.sheaf
      (fun V : X.base.affineOpens => V.1) ⊤
      (fun V => homOfLE le_top) hcover _ _ (fun V => ?_)
    show Scheme.resLE le_top (e3BetaGlued X _ hD' h3).1 =
      Scheme.resLE le_top
        (((Scheme.ΓSpecIso (CommRingCat.of (E3ModuliRing R))).inv ≫
          φ.baseHom.appTop).hom (e3Beta R))
    have hres : Scheme.resLE (le_top : V.1 ≤ ⊤)
        (((Scheme.ΓSpecIso (CommRingCat.of (E3ModuliRing R))).inv ≫
          φ.baseHom.appTop).hom (e3Beta R)) =
        sectionsMapLE φ.baseHom
          (show V.1 ≤ φ.baseHom ⁻¹ᵁ
            (⟨⊤, isAffineOpen_top _⟩ : (Spec (CommRingCat.of
              (E3ModuliRing R))).affineOpens).1 from fun x _ => trivial)
          ((Scheme.ΓSpecIso (CommRingCat.of (E3ModuliRing R))).inv.hom
            (e3Beta R)) := rfl
    rw [hres]
    exact (e3BetaGlued X _ hD' h3).2
      (e3PulledWitness φ hL V).V (e3PulledWitness φ hL V).Pr
      (e3PulledWitness φ hL V).β (e3PulledWitness φ hL V).γ
      (e3PulledWitness φ hL V).hF (e3PulledWitness φ hL V).hP
      (e3PulledWitness φ hL V).hQ
  refine IsLocalization.ringHom_ext (Submonoid.powers (e3Delta R)) ?_
  refine RingHom.ext fun x => ?_
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [RingHom.comp_apply]
  induction a using MvPolynomial.induction_on with
  | C r =>
    have hcr : (algebraMap (E3Quotient R) (E3ModuliRing R))
        (Ideal.Quotient.mk _ (MvPolynomial.C r)) = algebraMap R (E3ModuliRing R) r := by
      rw [IsScalarTower.algebraMap_apply R (E3Quotient R) (E3ModuliRing R),
        IsScalarTower.algebraMap_apply R (MvPolynomial (Fin 2) R) (E3Quotient R)]
      rfl
    rw [hcr, e3ClassifyingRingHom_algebraMap]
    exact (hψR r).symm
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p j hp =>
    simp only [map_mul, hp]
    congr 1
    fin_cases j
    · show e3ClassifyingRingHom X _ hD' h3 (e3Beta R) = _
      rw [e3ClassifyingRingHom_beta]; exact hnat_β
    · show e3ClassifyingRingHom X _ hD' h3 (e3Gamma R) = _
      rw [e3ClassifyingRingHom_gamma]; exact hnat_γ

open AlgebraicGeometry CategoryTheory Scheme LocalPresentation in
set_option backward.isDefEq.respectTransparency false in
/-- **([T-E15-NORM] rt2b ★)** BaseHom determination: the classifying morphism of the pulled
datum IS `φ`'s base morphism. Adapts `legendreClassifyingMap_pulled` (uses rt2a
`e3ClassifyingRingHom_pulled` + `Spec.map`/`toSpecΓ` naturality). -/
theorem e3ClassifyingMap_pulled (h3 : IsUnit (3 : Γ(X.base, ⊤))) :
    e3ClassifyingMap X
      ((gammaFullNaiveProblem R 3).map (Opposite.op φ)
        ⟨⟨universalE3P R, universalE3Q R⟩, hL⟩)
      (IsE3Datum.map φ (universalE3_isE3Datum R hL)
        ((gammaFullNaiveProblem R 3).map (Opposite.op φ)
          ⟨⟨universalE3P R, universalE3Q R⟩, hL⟩) rfl rfl) h3 = φ.baseHom := by
  show X.base.toSpecΓ ≫ Spec.map (CommRingCat.ofHom
    (e3ClassifyingRingHom X _ _ h3)) = φ.baseHom
  rw [show CommRingCat.ofHom
      (e3ClassifyingRingHom X
        ((gammaFullNaiveProblem R 3).map (Opposite.op φ)
          ⟨⟨universalE3P R, universalE3Q R⟩, hL⟩)
        (IsE3Datum.map φ (universalE3_isE3Datum R hL)
          ((gammaFullNaiveProblem R 3).map (Opposite.op φ)
            ⟨⟨universalE3P R, universalE3Q R⟩, hL⟩) rfl rfl) h3) =
    (Scheme.ΓSpecIso (CommRingCat.of (E3ModuliRing R))).inv ≫
      φ.baseHom.appTop from by
    rw [e3ClassifyingRingHom_pulled φ hL h3]
    rfl]
  rw [Spec.map_comp, ← Scheme.toSpecΓ_naturality_assoc]
  show φ.baseHom ≫ (Spec (CommRingCat.of (E3ModuliRing R))).toSpecΓ ≫
    Spec.map (Scheme.ΓSpecIso (CommRingCat.of (E3ModuliRing R))).inv =
    φ.baseHom
  rw [← SpecMap_ΓSpecIso_hom, ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id]
  exact Category.comp_id _

open AlgebraicGeometry CategoryTheory Limits Scheme LocalPresentation in
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 6400000 in
/-- **([T-E15-NORM] rt2c ★★)** Top determination: the glued classifying comparison of the
pulled datum IS φ's total-space morphism. Adapts legendreTop_pulled (ω-basis-independent
transport/pullback; e3Piece_congr at e3PulledWitness). -/
theorem e3Top_pulled (h3 : IsUnit (3 : Γ(X.base, ⊤))) :
    e3Top (IsE3Datum.map φ (universalE3_isE3Datum R hL)
      ((gammaFullNaiveProblem R 3).map (Opposite.op φ)
        ⟨⟨universalE3P R, universalE3Q R⟩, hL⟩) rfl rfl) h3 = φ.top := by
  set hD' := IsE3Datum.map φ
    (universalE3_isE3Datum R hL)
    ((gammaFullNaiveProblem R 3).map (Opposite.op φ)
      ⟨⟨universalE3P R, universalE3Q R⟩, hL⟩)
    rfl rfl with hD'def
  letI : Algebra (E3ModuliRing R)
      Γ(Spec (CommRingCat.of (E3ModuliRing R)), ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of (E3ModuliRing R))).inv.hom.toAlgebra
  haveI : IsIso (⊤ : (Spec (CommRingCat.of (E3ModuliRing R))).Opens).ι := by
    rw [← Scheme.topIso_hom]
    infer_instance
  haveI : IsIso (Spec.map (CommRingCat.ofHom (algebraMap (E3ModuliRing R)
      Γ(Spec (CommRingCat.of (E3ModuliRing R)), ⊤)))) := by
    have h : CommRingCat.ofHom (algebraMap (E3ModuliRing R)
        Γ(Spec (CommRingCat.of (E3ModuliRing R)), ⊤)) =
      (Scheme.ΓSpecIso (CommRingCat.of (E3ModuliRing R))).inv := rfl
    rw [h]
    infer_instance
  have hfst : pullback.fst (projModelπ (universalE3 R))
      (⊤ : (Spec (CommRingCat.of (E3ModuliRing R))).Opens).ι =
      (tautPresentation (universalE3 R)).e.hom ≫
        (isPullback_projModelBaseChange (universalE3 R)).isoPullback.hom ≫
        pullback.fst (projModelπ (universalE3 R))
          (Spec.map (CommRingCat.ofHom (algebraMap (E3ModuliRing R)
            Γ(Spec (CommRingCat.of (E3ModuliRing R)), ⊤)))) := by
    rw [show (tautPresentation (universalE3 R)).e.hom =
      (asIso (pullback.fst (projModelπ (universalE3 R))
        (⊤ : (Spec (CommRingCat.of (E3ModuliRing R))).Opens).ι) ≪≫
      (asIso (pullback.fst (projModelπ (universalE3 R))
        (Spec.map (CommRingCat.ofHom (algebraMap (E3ModuliRing R)
          Γ(Spec (CommRingCat.of (E3ModuliRing R)), ⊤)))))).symm ≪≫
      (isPullback_projModelBaseChange (universalE3 R)).isoPullback.symm).hom
      from rfl]
    simp only [Iso.trans_hom, Iso.symm_hom, asIso_hom, asIso_inv, Category.assoc,
      Iso.inv_hom_id_assoc, IsIso.inv_hom_id, Category.comp_id]
  refine (e3WitnessCover hD').hom_ext _ _ (fun w => ?_)
  rw [e3Top_piece hD' h3 w, e3WitnessCover_f]
  rw [e3Piece_congr hD' h3 w (e3PulledWitness φ hL w.V) rfl, eqToHom_refl,
    Category.id_comp]
  -- now: chartPiece(pulled) = fst ≫ φ.top; unfold the φ-side through the transport
  rw [show pullback.fst X.curve.toEllipticCurveGeom.π w.V.1.ι ≫ φ.top =
    transportTheta φ.baseHom φ.top φ.isPullback
      (show w.V.1 ≤ φ.baseHom ⁻¹ᵁ
        (⟨⊤, isAffineOpen_top _⟩ : (Spec (CommRingCat.of
          (E3ModuliRing R))).affineOpens).1 from fun x _ => trivial) ≫
      pullback.fst (projModelπ (universalE3 R))
        (⊤ : (Spec (CommRingCat.of (E3ModuliRing R))).Opens).ι from
    (transportTheta_fst φ.baseHom φ.top φ.isPullback _).symm]
  rw [hfst, ← Category.assoc,
    show transportTheta φ.baseHom φ.top φ.isPullback
        (show w.V.1 ≤ φ.baseHom ⁻¹ᵁ
          (⟨⊤, isAffineOpen_top _⟩ : (Spec (CommRingCat.of
            (E3ModuliRing R))).affineOpens).1 from fun x _ => trivial) ≫
      (tautPresentation (universalE3 R)).e.hom =
    ((tautPresentation (universalE3 R)).transport
      φ.baseHom φ.top φ.isPullback φ.zero_w
      (show w.V.1 ≤ φ.baseHom ⁻¹ᵁ
        (⟨⊤, isAffineOpen_top _⟩ : (Spec (CommRingCat.of
          (E3ModuliRing R))).affineOpens).1 from fun x _ => trivial)).e.hom ≫
      projModelBaseChange (sectionsMapLE φ.baseHom
        (show w.V.1 ≤ φ.baseHom ⁻¹ᵁ
          (⟨⊤, isAffineOpen_top _⟩ : (Spec (CommRingCat.of
            (E3ModuliRing R))).affineOpens).1 from fun x _ => trivial))
        (tautPresentation (universalE3 R)).W from
    (transport_e_baseChange φ.baseHom φ.top φ.isPullback φ.zero_w
      (tautPresentation (universalE3 R)) _).symm]
  -- collapse the universal-side chain into a single base change along the composite
  have hσ : (sectionsMapLE φ.baseHom
      (show w.V.1 ≤ φ.baseHom ⁻¹ᵁ
        (⟨⊤, isAffineOpen_top _⟩ : (Spec (CommRingCat.of
          (E3ModuliRing R))).affineOpens).1 from fun x _ => trivial)).comp
      ((Scheme.ΓSpecIso (CommRingCat.of (E3ModuliRing R))).inv.hom) =
      ((X.base.presheaf.map (homOfLE (le_top : w.V.1 ≤ ⊤)).op).hom).comp
        (e3ClassifyingRingHom X _ hD' h3) := by
    rw [sectionsMapLE_congr_hom (e3ClassifyingMap_pulled φ hL h3).symm
      (show w.V.1 ≤ φ.baseHom ⁻¹ᵁ
        (⟨⊤, isAffineOpen_top _⟩ : (Spec (CommRingCat.of
          (E3ModuliRing R))).affineOpens).1 from fun x _ => trivial)]
    exact sectionsMapLE_e3ClassifyingMap hD' h3 w.V (fun x _ => trivial)
  rw [show projModelBaseChange (sectionsMapLE φ.baseHom
      (show w.V.1 ≤ φ.baseHom ⁻¹ᵁ
        (⟨⊤, isAffineOpen_top _⟩ : (Spec (CommRingCat.of
          (E3ModuliRing R))).affineOpens).1 from fun x _ => trivial))
      (tautPresentation (universalE3 R)).W =
    projModelBaseChange (sectionsMapLE φ.baseHom
      (show w.V.1 ≤ φ.baseHom ⁻¹ᵁ
        (⟨⊤, isAffineOpen_top _⟩ : (Spec (CommRingCat.of
          (E3ModuliRing R))).affineOpens).1 from fun x _ => trivial))
      ((universalE3 R).map
        ((Scheme.ΓSpecIso (CommRingCat.of (E3ModuliRing R))).inv.hom)) from rfl]
  rw [show (isPullback_projModelBaseChange (universalE3 R)).isoPullback.hom ≫
      pullback.fst (projModelπ (universalE3 R))
        (Spec.map (CommRingCat.ofHom (algebraMap (E3ModuliRing R)
          Γ(Spec (CommRingCat.of (E3ModuliRing R)), ⊤)))) =
    projModelBaseChange
      ((Scheme.ΓSpecIso (CommRingCat.of (E3ModuliRing R))).inv.hom)
      (universalE3 R) from
    (isPullback_projModelBaseChange (universalE3 R)).isoPullback_hom_fst]
  rw [Category.assoc, ← projModelBaseChange_comp',
    projModelBaseChange_congr_hom hσ (universalE3 R)]
  rw [e3Piece]
  rfl

open AlgebraicGeometry CategoryTheory Scheme LocalPresentation in
/-- **([T-E15-NORM] rt2 ★★★, the uniqueness half of KM Ex. 2.2.2's universal property)**
ANY `Ell/R`-morphism to the universal `ℰ₃` object IS the classifying morphism of the
datum it pulls back. Assembles the baseHom (rt2b) + top (rt2c) determinations via
`EllHom.ext`. Adapts `legendreClassifyingEllHom_pulled`. -/
theorem e3ClassifyingEllHom_pulled (h3 : IsUnit (3 : Γ(X.base, ⊤))) :
    e3ClassifyingEllHom
      (IsE3Datum.map φ (universalE3_isE3Datum R hL)
        ((gammaFullNaiveProblem R 3).map (Opposite.op φ)
          ⟨⟨universalE3P R, universalE3Q R⟩, hL⟩) rfl rfl) h3 = φ :=
  EllHom.ext (e3ClassifyingMap_pulled φ hL h3) (e3Top_pulled φ hL h3)

end Rt2

open AlgebraicGeometry CategoryTheory Scheme in
/-- If `3` is a unit in `R`, it is a unit in the global sections of every `Ell/R`-object's
base. -/
theorem EllObj.isUnit_three {R : CommRingCat.{u}} (Y : EllObj R)
    (hR : IsUnit (3 : R)) : IsUnit (3 : Γ(Y.base, ⊤)) := by
  have h := hR.map Y.baseRingHom
  rwa [map_ofNat] at h

open AlgebraicGeometry CategoryTheory Scheme LocalPresentation in
set_option backward.isDefEq.respectTransparency false in
/-- **([T-E15-NORM] KM 4.7.0's `(3, GL₂(𝔽₃))` engine axiom 1, conditional on `hL`)** GIVEN
the naive-full-level-`3` clause for the universal marked pair (the [T-E15-NORM] level input,
bridge-gated on the E[3]/BB-DEG substrate), the `ℰ₃` datum problem is representable by the
universal `ℰ₃` object: `φ ↦` the pulled datum; inverse `= e3ClassifyingEllHom`; roundtrips
are rt1 (`pullSection_e3ClassifyingEllHom_P/Q`) and rt2 (`e3ClassifyingEllHom_pulled`). -/
noncomputable def e3DatumRepresentableBy (R : CommRingCat.{u}) (hR : IsUnit (3 : R))
    (hL : (universalE3Obj R).curve.IsNaiveFullLevel 3
      (universalE3P R) (universalE3Q R)) :
    (e3DatumProblem R).RepresentableBy (universalE3Obj R) where
  homEquiv {X} :=
    { toFun := fun φ => (e3DatumProblem R).map (Opposite.op φ)
        ⟨⟨⟨universalE3P R, universalE3Q R⟩, hL⟩, universalE3_isE3Datum R hL⟩
      invFun := fun x => e3ClassifyingEllHom x.2 (X.isUnit_three hR)
      left_inv := fun φ => e3ClassifyingEllHom_pulled φ hL (X.isUnit_three hR)
      right_inv := fun x => by
        refine Subtype.ext (Subtype.ext (Prod.ext ?_ ?_))
        · exact pullSection_e3ClassifyingEllHom_P x.2 (X.isUnit_three hR)
        · exact pullSection_e3ClassifyingEllHom_Q x.2 (X.isUnit_three hR) }
  homEquiv_comp {X X'} f g :=
    FunctorToTypes.map_comp_apply (e3DatumProblem R)
      (Opposite.op g) (Opposite.op f) _

open AlgebraicGeometry CategoryTheory Scheme in
/-- **([T-E15-NORM] the ℰ₃ datum-problem discharge, conditional on `hL`)** The `ℰ₃` datum
problem is representable by an object with **affine** base — `Y(3) = Spec E3ModuliRing`.
The `naiveLevelThree_representable_by_affine` headline (for the raw naive functor) adds the
bridge-gated naive↔datum equivalence on top of this. -/
theorem e3Datum_representable_by_affine_of_level (R : CommRingCat.{u}) (hR : IsUnit (3 : R))
    (hL : (universalE3Obj R).curve.IsNaiveFullLevel 3
      (universalE3P R) (universalE3Q R)) :
    ∃ X : EllObj R, IsAffine X.base ∧
      Nonempty ((e3DatumProblem R).RepresentableBy X) :=
  ⟨universalE3Obj R,
    inferInstanceAs (IsAffine (Spec (CommRingCat.of (E3ModuliRing R)))),
    ⟨e3DatumRepresentableBy R hR hL⟩⟩

open AlgebraicGeometry CategoryTheory Scheme LocalPresentation in
set_option backward.isDefEq.respectTransparency false in
/-- **([T-E15-NORM] the RAW naive-functor RepresentableBy, conditional on `hL` + `hArb`)**
Given `hL` (the universal marked pair is a level-`3` structure) and `hArb` (every naive
level-`3` structure IS an `ℰ₃`-datum — the arbitrary-datum direction, bridge-gated on the
E[3]/BB-DEG substrate), the raw naive level-`3` functor is representable by `universalE3Obj`.
The inverse classifies via `hArb`; `IsE3Datum` is a `Prop`, so `hArb X x` is defeq to the
pulled datum, making the roundtrips reduce to rt1/rt2. This is `naiveLevelThree_representable_by_affine`
(Bootstrap:74) modulo `hL` (killing+generation) and `hArb` (the bridges). -/
noncomputable def naiveLevelThreeRepresentableBy (R : CommRingCat.{u}) (hR : IsUnit (3 : R))
    (hL : (universalE3Obj R).curve.IsNaiveFullLevel 3
      (universalE3P R) (universalE3Q R))
    (hArb : ∀ (X : EllObj R) (L : X.curve.FullLevelPt 3), IsE3Datum X L) :
    (gammaFullNaiveProblem R 3).RepresentableBy (universalE3Obj R) where
  homEquiv {X} :=
    { toFun := fun φ => (gammaFullNaiveProblem R 3).map (Opposite.op φ)
        ⟨⟨universalE3P R, universalE3Q R⟩, hL⟩
      invFun := fun x => e3ClassifyingEllHom (hArb X x) (X.isUnit_three hR)
      left_inv := fun φ => e3ClassifyingEllHom_pulled φ hL (X.isUnit_three hR)
      right_inv := fun x => by
        refine Subtype.ext (Prod.ext ?_ ?_)
        · exact pullSection_e3ClassifyingEllHom_P (hArb X x) (X.isUnit_three hR)
        · exact pullSection_e3ClassifyingEllHom_Q (hArb X x) (X.isUnit_three hR) }
  homEquiv_comp {X X'} f g :=
    FunctorToTypes.map_comp_apply (gammaFullNaiveProblem R 3)
      (Opposite.op g) (Opposite.op f) _

open AlgebraicGeometry CategoryTheory Scheme in
/-- **([T-E15-NORM] `naiveLevelThree_representable_by_affine` reduced)** The raw naive
level-`3` problem is representable by an object with **affine** base, given `hL` + `hArb`.
This is exactly Bootstrap's `naiveLevelThree_representable_by_affine` modulo the two
keystone/bridge inputs. -/
theorem naiveLevelThree_representable_by_affine_of_conditions
    (R : CommRingCat.{u}) (hR : IsUnit (3 : R))
    (hL : (universalE3Obj R).curve.IsNaiveFullLevel 3
      (universalE3P R) (universalE3Q R))
    (hArb : ∀ (X : EllObj R) (L : X.curve.FullLevelPt 3), IsE3Datum X L) :
    ∃ X : EllObj R, IsAffine X.base ∧
      Nonempty ((gammaFullNaiveProblem R 3).RepresentableBy X) :=
  ⟨universalE3Obj R,
    inferInstanceAs (IsAffine (Spec (CommRingCat.of (E3ModuliRing R)))),
    ⟨naiveLevelThreeRepresentableBy R hR hL hArb⟩⟩

end ModularCurves
