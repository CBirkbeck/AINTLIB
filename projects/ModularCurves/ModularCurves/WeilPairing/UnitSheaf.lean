/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.Picard.RigidDescent

/-!
# The unit sheaf `K_E^×` normalized along the zero section (`AP-D1`)

Katz–Mazur, *Arithmetic Moduli of Elliptic Curves*, p. 88, verbatim: *"Let `K_E^× ⊂ 𝒪_E^×` denote
the subsheaf of invertible functions on `E` which take the value "1" along the zero-section of
`E/S`."*

In this tree's vocabulary the curve is presented as `pullback p g ⟶ T` (structure map
`pullback.snd p g`) with zero section `z` (`hz : z ≫ pullback.snd p g = 𝟙 T`), and KM's sections of
`K_E^×` over `π⁻¹(U_i)` — the `h_i` and `f_{i,j}` of the pairing construction (pp. 88–89) — live on
preimage opens `pullback.snd p g ⁻¹ᵁ U`. So the definition is per base open `U : T.Opens`:
`kUnits g hz U` is the subgroup of `Γ(X_T, f⁻¹U)ˣ` killed by the zero-section evaluation, realised as
`MonoidHom.ker` of `Units.map` of `z.appLE` — the group structure is free, and `mem_kUnits_iff`
unfolds membership to the equation the gluing lemmas (`Picard/RigidDescent.lean`'s `hnorm`) already
use.

`H⁰(E, K_E^×) = {1}` — KM (2.8.1.6) — is `AP-D2`: it is exactly `eq_one_of_pullback_eq_one`
(`EllipticCurve/SectionRigidity.lean:83`), already proved, read through `mem_kUnits_iff`.
Precision pin 3 (round 19): the `H¹(K^×) ≅ ker(0^*)` identification (`AP-D3`) works on the Zariski
site via the five-term sequence, with no hypothesis on `Pic(S)`.
-/

universe u

open CategoryTheory AlgebraicGeometry Limits

namespace ModularCurves

variable {X S : Scheme.{u}} {p : X ⟶ S} {T : Scheme.{u}} (g : T ⟶ S)

/-- Zero-section evaluation on units: `Γ(X_T, f⁻¹U)ˣ →* Γ(T, U)ˣ`, restriction along the section
`z`. `kUnits` is its kernel. -/
noncomputable def kUnitsEval {z : T ⟶ pullback p g} (hz : z ≫ pullback.snd p g = 𝟙 T)
    (U : T.Opens) :
    Γ(pullback p g, pullback.snd p g ⁻¹ᵁ U)ˣ →* Γ(T, U)ˣ :=
  Units.map ((z.appLE (pullback.snd p g ⁻¹ᵁ U) U (le_preimage_preimage g hz U)).hom :
    Γ(pullback p g, pullback.snd p g ⁻¹ᵁ U) →* Γ(T, U))

/-- **(AP-D1, KM p. 88)** `K_E^×` over the base open `U`: the subgroup of units on `f⁻¹U` taking the
value `1` along the zero section. -/
noncomputable def kUnits {z : T ⟶ pullback p g} (hz : z ≫ pullback.snd p g = 𝟙 T)
    (U : T.Opens) :
    Subgroup Γ(pullback p g, pullback.snd p g ⁻¹ᵁ U)ˣ :=
  (kUnitsEval g hz U).ker

/-- Membership in `kUnits` is the zero-section normalization equation — the exact shape consumed by
`nonempty_unitObj_iso_of_normalized_glue`'s `hnorm` and by KM's `h_i` patching (p. 89). -/
theorem mem_kUnits_iff {z : T ⟶ pullback p g} (hz : z ≫ pullback.snd p g = 𝟙 T)
    (U : T.Opens) (u : Γ(pullback p g, pullback.snd p g ⁻¹ᵁ U)ˣ) :
    u ∈ kUnits g hz U ↔
      (z.appLE (pullback.snd p g ⁻¹ᵁ U) U (le_preimage_preimage g hz U)).hom (u : _) = 1 := by
  rw [kUnits, MonoidHom.mem_ker, Units.ext_iff]
  rfl

/-- **(AP-D2, KM (2.8.1.6))** `H⁰` of `K_E^×` is trivial: over a universally `O`-connected family, a
unit equal to `1` along the zero section is `1`. This is `eq_one_of_pullback_eq_one`, read through
`mem_kUnits_iff`. -/
theorem kUnits_eq_bot (hp : UniversallyOConnected p) {z : T ⟶ pullback p g}
    (hz : z ≫ pullback.snd p g = 𝟙 T) (U : T.Opens) :
    kUnits g hz U = ⊥ := by
  ext u
  simp only [Subgroup.mem_bot, mem_kUnits_iff]
  constructor
  · intro h
    exact Units.ext (eq_one_of_pullback_eq_one g hp hz U (le_preimage_preimage g hz U) h)
  · rintro rfl
    simp

end ModularCurves
