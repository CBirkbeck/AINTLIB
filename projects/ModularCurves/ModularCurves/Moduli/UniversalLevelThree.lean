/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.Moduli.UniversalLegendre

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

/-- **(T-E15a)** The discriminant-type element `(a₁³ − 27a₃) · a₃` in the flex-locus
ring. -/
def e3Delta : E3Quotient R :=
  Ideal.Quotient.mk _ ((e3A₁Poly R ^ 3 - 27 * e3A₃Poly R) * e3A₃Poly R)

/-- **(T-E15a)** The T-E15 moduli ring
`R[β, γ][((a₁³−27a₃)a₃)⁻¹]/(β³−(β+γ)³)` — KM Ex. 2.2.2's `ℰ₃`-base. -/
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
`(a₁³ − 27a₃)·a₃`. -/
theorem e3Delta_map :
    algebraMap (E3Quotient R) (E3ModuliRing R) (e3Delta R) =
      ((universalE3 R).a₁ ^ 3 - 27 * (universalE3 R).a₃) * (universalE3 R).a₃ := by
  show e3Map R ((e3A₁Poly R ^ 3 - 27 * e3A₃Poly R) * e3A₃Poly R) = _
  rw [map_mul, map_sub, map_pow, map_mul, map_ofNat, e3Map_a₁Poly, e3Map_a₃Poly]

instance : (universalE3 R).IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff, universalE3_Δ]
  have h := IsLocalization.Away.algebraMap_isUnit
    (S := E3ModuliRing R) (e3Delta R)
  rw [e3Delta_map] at h
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

/-- The flex relation vanishes in the moduli ring. -/
theorem e3Rel_map_eq_zero : e3Map R (e3Rel R) = 0 := by
  show (algebraMap (E3Quotient R) (E3ModuliRing R))
    (Ideal.Quotient.mk _ (e3Rel R)) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr
    (Ideal.subset_span (Set.mem_singleton _)), map_zero]

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

end ModularCurves
