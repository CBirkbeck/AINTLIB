/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.Moduli.UniversalLevelThree

/-!
# The universal cube root of unity on the `ℰ₃` base (WP-A7.3 at `N = 3`)

Route A needs a root of unity on the trivialising cover, transforming by the inverse
determinant. The plan routed that through the universal object: build the root over the
`ℰ₃` moduli ring and pull it back. The plan's first step was to prove that ring is an
integral domain, so that a root of unity in its fraction field descends (WP-A7.2).

**None of that is necessary — the root is explicit.** On the `ℰ₃` base the defining
relation, after `γ` is inverted, is `3β² + 3βγ + γ² = 0`
(`universalE3_quadratic_rel`). Homogenising, `(3β + γ)² + (3β + γ)γ + γ² = 0`, so

  `ζ := (3β + γ) / γ`

satisfies `ζ² + ζ + 1 = 0` on the nose, hence `ζ³ = 1`. No domain hypothesis, no fraction
field, no integrality argument — and no division by `2`, which matters because the base is
`ℤ[1/3]`.

This is the arithmetic shadow of a geometric fact: the surviving relation has discriminant
`−3γ²` in `β`, so the `ℰ₃` base is exactly where `√−3`, equivalently `ζ₃`, becomes
available. The field of definition of `Y(3)`'s geometric components and the root of unity
the Weil pairing's determinant twist needs are the same phenomenon.
-/

universe u

open AlgebraicGeometry CategoryTheory

namespace ModularCurves

variable (R : CommRingCat.{u})

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **(WP-A7.3, `N = 3`)** The universal cube root of unity on the `ℰ₃` moduli ring:
`ζ = (3β + γ)/γ`, with `γ` inverted by `isUnit_e3Gamma`. -/
noncomputable def e3Zeta : E3ModuliRing R :=
  (3 * e3Beta R + e3Gamma R) *
    ((isUnit_e3Gamma R).unit⁻¹ : (E3ModuliRing R)ˣ)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- `γ · γ⁻¹ = 1` in the shape the `ζ`-computations use. -/
theorem e3Gamma_mul_inv :
    e3Gamma R * ((isUnit_e3Gamma R).unit⁻¹ : (E3ModuliRing R)ˣ) = 1 := by
  have h : (((isUnit_e3Gamma R).unit : (E3ModuliRing R)ˣ) : E3ModuliRing R) *
      (((isUnit_e3Gamma R).unit⁻¹ : (E3ModuliRing R)ˣ) : E3ModuliRing R) = 1 :=
    (isUnit_e3Gamma R).unit.mul_inv
  have hval : (((isUnit_e3Gamma R).unit : (E3ModuliRing R)ˣ) : E3ModuliRing R) =
      e3Gamma R := rfl
  calc e3Gamma R * ((isUnit_e3Gamma R).unit⁻¹ : (E3ModuliRing R)ˣ)
      = (((isUnit_e3Gamma R).unit : (E3ModuliRing R)ˣ) : E3ModuliRing R) *
          ((isUnit_e3Gamma R).unit⁻¹ : (E3ModuliRing R)ˣ) := by rw [hval]
    _ = 1 := h

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **(WP-A7.3, `N = 3`)** The universal `ζ` is a primitive cube root of unity: it satisfies
the cyclotomic relation `ζ² + ζ + 1 = 0`.

Homogenise `universalE3_quadratic_rel` and divide by `γ²`. -/
theorem e3Zeta_cyclotomic : e3Zeta R ^ 2 + e3Zeta R + 1 = 0 := by
  have hhom : (3 * e3Beta R + e3Gamma R) ^ 2 +
      (3 * e3Beta R + e3Gamma R) * e3Gamma R + e3Gamma R ^ 2 = 0 := by
    linear_combination (3 : E3ModuliRing R) * universalE3_quadratic_rel R
  have hu := e3Gamma_mul_inv R
  have hkey : (e3Zeta R ^ 2 + e3Zeta R + 1) * e3Gamma R ^ 2 = 0 := by
    unfold e3Zeta
    linear_combination hhom +
      ((3 * e3Beta R + e3Gamma R) ^ 2 *
          ((isUnit_e3Gamma R).unit⁻¹ : (E3ModuliRing R)ˣ) * e3Gamma R +
        (3 * e3Beta R + e3Gamma R) ^ 2 +
        (3 * e3Beta R + e3Gamma R) * e3Gamma R) * hu
  exact ((isUnit_e3Gamma R).pow 2).mul_left_eq_zero.mp hkey

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **(WP-A7.3, `N = 3`)** The universal `ζ` is a cube root of unity. -/
theorem e3Zeta_pow_three : e3Zeta R ^ 3 = 1 := by
  have h := e3Zeta_cyclotomic R
  linear_combination (e3Zeta R - 1) * h

/-! ## WP-A7.4 — transport to an arbitrary base -/

section Transport

variable {R} {X : EllObj R} (L : X.curve.FullLevelPt 3) (hD : IsE3Datum X L)
  (h3 : IsUnit (3 : Γ(X.base, (⊤ : X.base.Opens))))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **(WP-A7.4)** The cube root of unity attached to a full level-3 structure on an
arbitrary base: pull the universal `ζ` back along the classifying ring map.

Non-circularity is the point here. The classifying map exists because `universalE3Obj`
represents the naive full level-3 problem, and that representability
(`naiveLevelThree_representable_by_affine`) is proved **by hand** from the `ℰ₃` normal
form — never via the Weil pairing. So sourcing the pairing's root of unity from the
universal object introduces no circular dependency. -/
noncomputable def e3ZetaAt : Γ(X.base, (⊤ : X.base.Opens)) :=
  e3ClassifyingRingHom X L hD h3 (e3Zeta R)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **(WP-A7.4)** The transported root satisfies the cyclotomic relation. -/
theorem e3ZetaAt_cyclotomic :
    e3ZetaAt L hD h3 ^ 2 + e3ZetaAt L hD h3 + 1 = 0 := by
  have h := congrArg (e3ClassifyingRingHom X L hD h3) (e3Zeta_cyclotomic R)
  simpa only [map_add, map_pow, map_one, map_zero, e3ZetaAt] using h

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **(WP-A7.4)** The transported root is a cube root of unity — the `N = 3` instance of
the root datum that `WeilPairingLocalData` needs on the trivialising cover. -/
theorem e3ZetaAt_pow_three : e3ZetaAt L hD h3 ^ 3 = 1 := by
  have h := congrArg (e3ClassifyingRingHom X L hD h3) (e3Zeta_pow_three R)
  simpa only [map_pow, map_one, e3ZetaAt] using h

end Transport

end ModularCurves
