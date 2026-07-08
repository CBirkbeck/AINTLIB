/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.Moduli.WeierstrassAtlas

/-!
# The Weierstrass coordinate-change action and the moduli groupoid `M_ell^W = [U/G]`

AINTLIB ModularCurves T-W4 (+ the T-W6 substrate): the coordinate-change group
`G = WeierstrassCurve.VariableChange` acting on the universal Weierstrass atlas
`U = weierstrassAtlas = Spec ℤ[a₁,…,a₆][Δ⁻¹]` (T-W5), at the level demanded by the
v9.2 severance and the v10.36 architecture finding: `G` is an affine group **scheme**
(`𝔾_m ⋉ 𝔸³`), so the quotient groupoid at a base `S` must use the `S`-points
`G(Γ) = VariableChange Γ` acting on `U(Γ) = {W : WeierstrassCurve Γ // IsUnit W.Δ}` —
ring-by-ring, functorially — rather than a single abstract group acting by scheme
automorphisms (`SchemeAction` is the Q-finite vocabulary, not this one).

Everything is mathlib-native: `WeierstrassCurve.map`/`map_Δ` (coefficient base change),
`VariableChange` group + `•` action, `VariableChange.map` + `map_variableChange`
(base-change naturality of the action). The atlas dictionary
`(WeierstrassAtlasRing →+* B) ≃ ellipticW B` is the universal property of
`MvPolynomial (Fin 5) ℤ` localized away from `Δ`.

* `ellipticW B`: Weierstrass curves over `B` with invertible discriminant — the
  `B`-points of `U`.
* `ellipticW.map`: functorial base change; `smul` preserves `ellipticW` (the action of
  `VariableChange B`).
* `toRingHom` / `ofRingHom`: the atlas dictionary, with round-trip and naturality
  lemmas (sorried leaves of this ticket).

The groupoid-valued functor `M_ell^W` and the T-W6 equivalence with Weierstrass-data
records (T-A8) build on this layer in the same file, next increment. Decomposition
notes: board v10.36; v10.24(b) interfaces accompany each heavy definition as it lands.
-/

open AlgebraicGeometry CategoryTheory WeierstrassCurve

namespace ModularCurves

universe u

variable {B C : Type*} [CommRing B] [CommRing C]

/-- Weierstrass curves with invertible discriminant over `B`: the `B`-points of the
universal Weierstrass atlas `U` (T-W5). -/
def ellipticW (B : Type*) [CommRing B] : Type _ :=
  {W : WeierstrassCurve B // IsUnit W.Δ}

namespace ellipticW

/-- Base change of an atlas point along a ring map. -/
def map (f : B →+* C) (W : ellipticW B) : ellipticW C :=
  ⟨W.1.map f, by rw [map_Δ]; exact W.2.map f⟩

@[simp] theorem map_coe (f : B →+* C) (W : ellipticW B) : (W.map f).1 = W.1.map f :=
  rfl

theorem map_id (W : ellipticW B) : W.map (RingHom.id B) = W :=
  Subtype.ext W.1.map_id

theorem map_comp {D : Type*} [CommRing D] (f : B →+* C) (g : C →+* D) (W : ellipticW B) :
    (W.map f).map g = W.map (g.comp f) :=
  Subtype.ext (W.1.map_map f g)

/-- The coordinate-change action preserves invertibility of the discriminant
(`variableChange_Δ`: `Δ` scales by the unit `u⁻¹²`). -/
theorem isUnit_smul_Δ (C' : VariableChange B) (W : ellipticW B) :
    IsUnit (C' • W.1).Δ := by
  rw [variableChange_Δ]
  exact ((C'.u⁻¹).isUnit.pow 12).mul W.2

/-- The action of the coordinate-change group `G(B) = VariableChange B` on the
`B`-points of the atlas. -/
instance : SMul (VariableChange B) (ellipticW B) :=
  ⟨fun C' W => ⟨C' • W.1, isUnit_smul_Δ C' W⟩⟩

@[simp] theorem smul_coe (C' : VariableChange B) (W : ellipticW B) :
    (C' • W).1 = C' • W.1 :=
  rfl

instance : MulAction (VariableChange B) (ellipticW B) where
  one_smul W := Subtype.ext (one_smul _ _)
  mul_smul C₁ C₂ W := Subtype.ext (mul_smul _ _ _)

/-- Base-change naturality of the action (mathlib's `map_variableChange`). -/
theorem map_smul (f : B →+* C) (C' : VariableChange B) (W : ellipticW B) :
    (C' • W).map f = C'.map f • W.map f :=
  Subtype.ext (map_variableChange _ _ _).symm

end ellipticW

/-- The atlas dictionary, forward direction: a ring map out of the atlas ring gives a
Weierstrass curve with invertible discriminant (push the universal curve forward). -/
noncomputable def ellipticWOfRingHom (φ : WeierstrassAtlasRing →+* B) : ellipticW B :=
  ⟨universalWeierstrassLoc.map φ, by
    rw [map_Δ]
    exact universalWeierstrassLoc.isUnit_Δ.map φ⟩

end ModularCurves
