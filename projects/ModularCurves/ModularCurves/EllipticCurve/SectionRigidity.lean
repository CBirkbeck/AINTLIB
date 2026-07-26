/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.EllipticCurve.Rigidity

/-!
# Rigidity of sections along the zero section (Gap A, the normalization half)

For `p : X ⟶ S` universally `O`-connected and a section `z` of the base change
`f = pr₂ : X ×_S T ⟶ T`, a regular function on `X_T` is **determined by its restriction to
the zero section**:

* `sectionRigidity` — `z^* u = z^* v ⟹ u = v` on any `f ⁻¹ᵁ U`;
* `eq_one_of_pullback_eq_one` — the pointed form, `z^* u = 1 ⟹ u = 1`;
* `unitsEquiv` — consequently `Γ(T,U)ˣ ≃* Γ(X_T, f ⁻¹ᵁ U)ˣ`.

This is the *uniqueness* half of the rigidification used by the Katz–Mazur / GME
construction of the relative Weil pairing. `(★′)`
(`ModularCurves.picMap_mulByHom_kappa_eq_one`) supplies the *existence* of a trivialization
of `[N]^* L_Q`; two trivializations differ by a unit on `X_T`, and `eq_one_of_pullback_eq_one`
says that normalizing along the zero section pins the trivialization down uniquely. Without
it the pairing would only be defined up to a unit, since `Pic` is built through `Skeleton`
and an equality of classes yields a mere `Nonempty` of isomorphisms.

Everything here is elementary: `UniversallyOConnected` says exactly that `f.app U` is a ring
isomorphism, and `z` splits it.
-/

universe u

open CategoryTheory AlgebraicGeometry Limits

namespace ModularCurves

variable {X S : Scheme.{u}} {p : X ⟶ S} {T : Scheme.{u}} (g : T ⟶ S)

/-- `appLE` of an endomorphism that *is* the identity. Stated separately so that `hz` is
substituted rather than rewritten under the (dependent) `≤`-proof. -/
private theorem appLE_eq_id_of_eq_id {Z : Scheme.{u}} {φ : Z ⟶ Z} (hφ : φ = 𝟙 Z)
    (U : Z.Opens) (h : U ≤ φ ⁻¹ᵁ U) : φ.appLE U U h = 𝟙 _ := by
  subst hφ
  simp only [Scheme.Hom.appLE, Scheme.Hom.id_app, Category.id_comp]
  first
    | exact Z.presheaf.map_id _
    | exact (congrArg Z.presheaf.map (Subsingleton.elim _ (𝟙 (Opposite.op U)))).trans
        (Z.presheaf.map_id _)

/-- The zero section splits `f.app U`: restricting a function pulled back from the base
along the section gives the function back. -/
theorem app_appLE_section {z : T ⟶ pullback p g} (hz : z ≫ pullback.snd p g = 𝟙 T)
    (U : T.Opens) (e : U ≤ z ⁻¹ᵁ (pullback.snd p g ⁻¹ᵁ U)) :
    (pullback.snd p g).app U ≫ z.appLE (pullback.snd p g ⁻¹ᵁ U) U e = 𝟙 _ := by
  have h1 : (pullback.snd p g).app U
      = (pullback.snd p g).appLE U (pullback.snd p g ⁻¹ᵁ U) le_rfl :=
    (Scheme.Hom.appLE_eq_app _).symm
  rw [h1, Scheme.Hom.appLE_comp_appLE]
  exact appLE_eq_id_of_eq_id hz U _

/-- **Rigidity of sections.** For a universally `O`-connected `p`, a regular function on
`X ×_S T` over an open `U` of `T` is determined by its restriction along a section `z`. -/
theorem sectionRigidity (hp : UniversallyOConnected p) {z : T ⟶ pullback p g}
    (hz : z ≫ pullback.snd p g = 𝟙 T) (U : T.Opens)
    (e : U ≤ z ⁻¹ᵁ (pullback.snd p g ⁻¹ᵁ U))
    {u v : Γ(pullback p g, pullback.snd p g ⁻¹ᵁ U)}
    (h : (z.appLE (pullback.snd p g ⁻¹ᵁ U) U e).hom u
        = (z.appLE (pullback.snd p g ⁻¹ᵁ U) U e).hom v) :
    u = v := by
  haveI := hp g U
  obtain ⟨a, rfl⟩ := ((ConcreteCategory.bijective_of_isIso
    ((pullback.snd p g).app U)).2) u
  obtain ⟨b, rfl⟩ := ((ConcreteCategory.bijective_of_isIso
    ((pullback.snd p g).app U)).2) v
  have key : ∀ w : Γ(T, U), (z.appLE (pullback.snd p g ⁻¹ᵁ U) U e).hom
      (((pullback.snd p g).app U).hom w) = w := fun w =>
    congrArg (fun φ : Γ(T, U) ⟶ Γ(T, U) => φ.hom w) (app_appLE_section g hz U e)
  rw [key a, key b] at h
  exact congrArg (fun w => ((pullback.snd p g).app U).hom w) h

/-- The pointed form of `sectionRigidity`: a function trivial along the zero section is
trivial. This is what makes a zero-section-normalized trivialization unique. -/
theorem eq_one_of_pullback_eq_one (hp : UniversallyOConnected p) {z : T ⟶ pullback p g}
    (hz : z ≫ pullback.snd p g = 𝟙 T) (U : T.Opens)
    (e : U ≤ z ⁻¹ᵁ (pullback.snd p g ⁻¹ᵁ U))
    {u : Γ(pullback p g, pullback.snd p g ⁻¹ᵁ U)}
    (h : (z.appLE (pullback.snd p g ⁻¹ᵁ U) U e).hom u = 1) :
    u = 1 :=
  sectionRigidity g hp hz U e (by rw [h, map_one])

/-- Variant of `eq_one_of_pullback_eq_one` for an open that is only *equal* to a preimage
`f ⁻¹ᵁ U`, not syntactically one — e.g. `f ⁻¹ᵁ U ⊓ f ⁻¹ᵁ V`, which is the shape overlaps
take in a gluing argument. -/
theorem eq_one_of_pullback_eq_one' (hp : UniversallyOConnected p) {z : T ⟶ pullback p g}
    (hz : z ≫ pullback.snd p g = 𝟙 T) (U : T.Opens) (V : (pullback p g).Opens)
    (hV : V = pullback.snd p g ⁻¹ᵁ U) (e : U ≤ z ⁻¹ᵁ V)
    {w : Γ(pullback p g, V)} (h : (z.appLE V U e).hom w = 1) : w = 1 := by
  subst hV
  exact eq_one_of_pullback_eq_one g hp hz U e h

/-- Units on `X ×_S T` over `f ⁻¹ᵁ U` are exactly units pulled back from `U`. -/
noncomputable def unitsEquiv (hp : UniversallyOConnected p) (U : T.Opens) :
    Γ(T, U)ˣ ≃* Γ(pullback p g, pullback.snd p g ⁻¹ᵁ U)ˣ :=
  haveI := hp g U
  Units.mapEquiv (asIso ((pullback.snd p g).app U)).commRingCatIsoToRingEquiv.toMulEquiv

end ModularCurves
