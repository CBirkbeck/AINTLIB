/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.EllipticCurve.ComparisonBridge

/-!
# Faithfulness of the projective variable-change action (T-W7.1b b5)

The uniqueness (b5) leaf of the T-W7.1b comparison theorem: the variable change inducing a given
pointed model isomorphism is unique. Concretely, if two variable changes `C₁`, `C₂` act equally on
`W` (so `C₁ • W = C₂ • W`) and their comparison isomorphisms `projModelVCIso Cᵢ W` agree modulo the
induced curve equality, then `C₁ = C₂` (`projModelVCIso_injective'`).

The proof reads the `(u, r, s, t)` coefficients off the coordinate action: `bridge_coordX` /
`bridge_coordY` give `pointedIsoCoordEquiv (projModelVCIso Cᵢ W)` explicitly, `coordXY_ext` extracts
the scalar equations, and cancelling the unit `↑u²` pins the four fields.

The one subtlety is transporting `pointedIsoCoordEquiv` across the curve equality `C₁ • W = C₂ • W`
without forcing the kernel to whnf the huge coordinate-ring carrier. `transport_general` states the
transport with the *two models as free variables*, so `subst` collapses the equality and the
identity `coordRingCongr_refl_apply` — applied to an opaque element via `rw` — discharges the
`coordRingCongr`-of-`rfl` without unfolding the carrier. `pointedIsoCoordEquiv_congr` (dependence on
`e.hom` only) then closes it on the now-opaque isos; the main theorem instantiates the two isos by
pure function application, so nothing large is ever re-checked.

This is the self-contained `projModelVCIso_injective'`; it discharges the `projModelVCIso_injective`
sorry in `ModelVariableChange.lean` once the b2 filtration leaf lands and the wiring is done.

AINTLIB ModularCurves T-W7.1b (lane P3-parallel, beastmode-P3b3).
-/

open WeierstrassCurve CategoryTheory

namespace ModularCurves

universe u
variable {R : Type u} [CommRing R]

/-- `pointedIsoCoordEquiv` depends only on `e.hom`. -/
lemma pointedIsoCoordEquiv_congr {W W' : WeierstrassCurve R}
    (e₁ e₂ : projModel W ≅ projModel W')
    (heq : e₁.hom = e₂.hom)
    (h1π : e₁.hom ≫ projModelπ W' = projModelπ W)
    (h1z : projModelZero W ≫ e₁.hom = projModelZero W')
    (h2π : e₂.hom ≫ projModelπ W' = projModelπ W)
    (h2z : projModelZero W ≫ e₂.hom = projModelZero W') :
    pointedIsoCoordEquiv e₁ h1π h1z = pointedIsoCoordEquiv e₂ h2π h2z := by
  obtain rfl : e₁ = e₂ := Iso.ext heq
  rfl

/-- Coordinate-ring transport along a curve equality. -/
noncomputable def coordRingCongr {V₁ V₂ : WeierstrassCurve R} (h : V₁ = V₂) :
    V₁.toAffine.CoordinateRing ≃ₐ[R] V₂.toAffine.CoordinateRing :=
  h ▸ AlgEquiv.refl

@[simp] lemma coordRingCongr_self {V : WeierstrassCurve R} (h : V = V) :
    coordRingCongr h = AlgEquiv.refl := by rw [Subsingleton.elim h rfl]; rfl

/-- `coordRingCongr` of a reflexivity proof is the identity (proved on an opaque argument, so it
transports no large term through the kernel). -/
lemma coordRingCongr_refl_apply {V : WeierstrassCurve R} (h : V = V)
    (x : V.toAffine.CoordinateRing) : coordRingCongr h x = x := by
  rw [coordRingCongr_self]; rfl

@[simp] lemma coordRingCongr_coordX {V₁ V₂ : WeierstrassCurve R} (h : V₁ = V₂) :
    coordRingCongr h (coordX V₁) = coordX V₂ := by subst h; rfl

@[simp] lemma coordRingCongr_coordY {V₁ V₂ : WeierstrassCurve R} (h : V₁ = V₂) :
    coordRingCongr h (coordY V₁) = coordY V₂ := by subst h; rfl

@[simp] lemma coordRingCongr_algebraMap {V₁ V₂ : WeierstrassCurve R} (h : V₁ = V₂) (r : R) :
    coordRingCongr h (algebraMap R _ r) = algebraMap R _ r := by subst h; rfl

@[simp] lemma coordRingCongr_algebraMap_mul_coordX {V₁ V₂ : WeierstrassCurve R} (h : V₁ = V₂)
    (c : R) : coordRingCongr h (algebraMap R _ c * coordX V₁) = algebraMap R _ c * coordX V₂ := by
  subst h; rfl

@[simp] lemma coordRingCongr_algebraMap_mul_coordY {V₁ V₂ : WeierstrassCurve R} (h : V₁ = V₂)
    (c : R) : coordRingCongr h (algebraMap R _ c * coordY V₁) = algebraMap R _ c * coordY V₂ := by
  subst h; rfl

/-- Per-element transport of `pointedIsoCoordEquiv` along a curve equality, with the two models
free variables so the equality is discharged by `subst` (never transporting the large
`pointedIsoCoordEquiv` carrier through the kernel). -/
lemma transport_general {W V₁ V₂ : WeierstrassCurve R} (hV : V₁ = V₂)
    (e₁ : projModel V₁ ≅ projModel W) (e₂ : projModel V₂ ≅ projModel W)
    (hπ₁ : e₁.hom ≫ projModelπ W = projModelπ V₁)
    (hz₁ : projModelZero V₁ ≫ e₁.hom = projModelZero W)
    (hπ₂ : e₂.hom ≫ projModelπ W = projModelπ V₂)
    (hz₂ : projModelZero V₂ ≫ e₂.hom = projModelZero W)
    (h : e₁.hom = eqToHom (congrArg projModel hV) ≫ e₂.hom)
    (a : W.toAffine.CoordinateRing) :
    pointedIsoCoordEquiv e₁ hπ₁ hz₁ a
      = coordRingCongr hV.symm (pointedIsoCoordEquiv e₂ hπ₂ hz₂ a) := by
  subst hV
  rw [coordRingCongr_refl_apply]
  have h' : e₁.hom = e₂.hom := by rw [h]; simp
  exact DFunLike.congr_fun (pointedIsoCoordEquiv_congr e₁ e₂ h' hπ₁ hz₁ hπ₂ hz₂) a

/-- **(T-W7.1b-b5)** Injectivity of the projective variable-change action: if two variable changes
`C₁`, `C₂` act equally on `W` and their comparison isomorphisms agree (modulo the induced curve
equality), then `C₁ = C₂`. -/
theorem projModelVCIso_injective' (C₁ C₂ : VariableChange R) (W : WeierstrassCurve R)
    (hW : C₁ • W = C₂ • W)
    (h : (projModelVCIso C₁ W).hom = eqToHom (by rw [hW]) ≫ (projModelVCIso C₂ W).hom) :
    C₁ = C₂ := by
  rcases subsingleton_or_nontrivial R with hs | hn
  · -- Subsingleton base: `VariableChange R` is a subsingleton.
    haveI := hs
    exact VariableChange.ext (Units.ext (Subsingleton.elim _ _)) (Subsingleton.elim _ _)
      (Subsingleton.elim _ _) (Subsingleton.elim _ _)
  · -- Nontrivial base: read coefficients off the coordinate action.
    haveI := hn
    have transport : ∀ a : W.toAffine.CoordinateRing,
        pointedIsoCoordEquiv (projModelVCIso C₁ W) (projModelVCIso_π C₁ W)
            (projModelVCIso_zero C₁ W) a
          = coordRingCongr hW.symm (pointedIsoCoordEquiv (projModelVCIso C₂ W)
              (projModelVCIso_π C₂ W) (projModelVCIso_zero C₂ W) a) := fun a =>
      transport_general hW (projModelVCIso C₁ W) (projModelVCIso C₂ W)
        (projModelVCIso_π C₁ W) (projModelVCIso_zero C₁ W)
        (projModelVCIso_π C₂ W) (projModelVCIso_zero C₂ W) h a
    -- Coefficient equations from `x` and `y`.
    have hX := transport (coordX W)
    rw [bridge_coordX C₁ W, bridge_coordX C₂ W] at hX
    simp only [map_add, coordRingCongr_algebraMap_mul_coordX, coordRingCongr_algebraMap] at hX
    have hY := transport (coordY W)
    rw [bridge_coordY C₁ W, bridge_coordY C₂ W] at hY
    simp only [map_add, coordRingCongr_algebraMap_mul_coordY, coordRingCongr_algebraMap_mul_coordX,
      coordRingCongr_algebraMap] at hY
    -- Reshape into `coordXY_ext` form and extract the coefficients.
    have hXe : algebraMap R (C₁ • W).toAffine.CoordinateRing C₁.r
          + algebraMap R _ ((↑C₁.u : R) ^ 2) * coordX (C₁ • W)
          + algebraMap R _ (0 : R) * coordY (C₁ • W)
        = algebraMap R _ C₂.r + algebraMap R _ ((↑C₂.u : R) ^ 2) * coordX (C₁ • W)
          + algebraMap R _ (0 : R) * coordY (C₁ • W) := by
      simp only [map_zero, zero_mul, add_zero]; linear_combination hX
    obtain ⟨hr, hu2, -⟩ := coordXY_ext hXe
    have hYe : algebraMap R (C₁ • W).toAffine.CoordinateRing C₁.t
          + algebraMap R _ (C₁.s * (↑C₁.u : R) ^ 2) * coordX (C₁ • W)
          + algebraMap R _ ((↑C₁.u : R) ^ 3) * coordY (C₁ • W)
        = algebraMap R _ C₂.t + algebraMap R _ (C₂.s * (↑C₂.u : R) ^ 2) * coordX (C₁ • W)
          + algebraMap R _ ((↑C₂.u : R) ^ 3) * coordY (C₁ • W) := by
      linear_combination hY
    obtain ⟨ht, hsu2, hu3⟩ := coordXY_ext hYe
    -- Unit arithmetic.
    have hu2unit : IsUnit ((↑C₁.u : R) ^ 2) := by
      rw [← Units.val_pow_eq_pow_val]; exact (C₁.u ^ 2).isUnit
    have huu : (↑C₁.u : R) * (↑C₁.u : R) ^ 2 = (↑C₂.u : R) * (↑C₁.u : R) ^ 2 := by
      linear_combination hu3 - (↑C₂.u : R) * hu2
    have hu : (↑C₁.u : R) = (↑C₂.u : R) := (hu2unit.mul_left_inj).mp huu
    have hs2 : C₁.s * (↑C₁.u : R) ^ 2 = C₂.s * (↑C₁.u : R) ^ 2 := by
      linear_combination hsu2 - C₂.s * hu2
    have hsval : C₁.s = C₂.s := (hu2unit.mul_left_inj).mp hs2
    exact VariableChange.ext (Units.ext hu) hr hsval ht

end ModularCurves
