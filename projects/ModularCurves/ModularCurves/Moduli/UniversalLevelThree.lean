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
      Pr.MarksAt L.1.2.2 γ (β + γ)

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
  choose Vx hxVx Prx βx γx hFx hPx hQx using hD
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
  choose Vx hxVx Prx βx γx hFx hPx hQx using hD
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
  choose Vx hxVx Prx βx γx hFx hPx hQx using hDc
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
        3 * (e3BetaGlued X L hD h3).1 * (e3GammaGlued X L hD h3).1))) := by
  set gB := (e3BetaGlued X L hD h3).1 with hgB
  set gG := (e3GammaGlued X L hD h3).1 with hgG
  apply X.base.toRingedSpace.isUnit_of_isUnit_germ
  intro x _
  obtain ⟨V, hxV, Pr, β, γ, hF, hP, hQ⟩ := hD x
  set D := ((3 * gG - 1) ^ 3 - 27 * (-3 * gG ^ 2 - gB - 3 * gB * gG)) *
    (-3 * gG ^ 2 - gB - 3 * gB * gG) with hDdef
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
      (Pr.W.a₁ ^ 3 - 27 * Pr.W.a₃) * Pr.W.a₃ := by
    rw [hDdef]
    simp only [map_mul, map_sub, map_pow, map_neg, map_ofNat, map_one]
    rw [hgB, hgG, hβ, hγ, ha₁, ha₃]
  rw [hres]
  obtain ⟨hu3, huD⟩ := e3form_units ⟨ha₁, ha₂, ha₃, ha₄, ha₆⟩ Pr.elliptic
  exact huD.mul hu3

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
    Matrix.cons_val_one, Matrix.head_cons]
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
        3 * (e3BetaGlued X L hD h3).1 * (e3GammaGlued X L hD h3).1)) from by
    show (e3QuotientMap X L hD h3).comp (Ideal.Quotient.mk _)
        ((e3A₁Poly R ^ 3 - 27 * e3A₃Poly R) * e3A₃Poly R) = _
    show e3BaseMap X L hD h3 ((e3A₁Poly R ^ 3 - 27 * e3A₃Poly R) * e3A₃Poly R) = _
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

end ModularCurves
