/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project

ForMathlib (OURS, not vendored): upstream candidate.
Adapted from the Apache-licensed `SchemeIsomorphismOpenShrink.lean`
in Vilin97/Clawristotle.
-/
import Mathlib.AlgebraicGeometry.Restrict

/-!
# Shrinking an isomorphism open

If a morphism is an isomorphism over a target open, an upstairs open can
be transported through the inverse to a smaller target open. Its inverse
image is the intersection with the original isomorphism locus.
-/

open CategoryTheory Limits TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- An isomorphism over an open remains an isomorphism after shrinking
the target open. -/
theorem isIso_morphismRestrict_of_le
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (U V : Y.Opens) (hVU : V ≤ U)
    [IsIso (f ∣_ U)] :
    IsIso (f ∣_ V) := by
  let h :=
    IsOpenImmersion.isPullback
      (f ∣_ V)
      (X.homOfLE (f.preimage_mono hVU))
      (Y.homOfLE hVU)
      (f ∣_ U)
      (morphismRestrict_homOfLE f V U hVU).symm
      (by
        simp only [Scheme.opensRange_homOfLE,
          ← Scheme.Hom.comp_preimage, morphismRestrict_ι])
  exact h.isIso_fst_of_isIso

/-- Transport an upstairs open through the inverse over a target
isomorphism open. -/
noncomputable def isomorphismTargetShrink
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (U : Y.Opens) [IsIso (f ∣_ U)]
    (W : X.Opens) : Y.Opens :=
  U.ι ''ᵁ
    (((inv (f ∣_ U)) ≫ (f ⁻¹ᵁ U).ι) ⁻¹ᵁ W)

/-- The transported open is contained in the original isomorphism
open. -/
theorem isomorphismTargetShrink_le
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (U : Y.Opens) [IsIso (f ∣_ U)]
    (W : X.Opens) :
    f.isomorphismTargetShrink U W ≤ U :=
  U.ι_image_le _

/-- The inverse image of the transported open is its intersection with
the original isomorphism locus. -/
theorem preimage_isomorphismTargetShrink
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (U : Y.Opens) [IsIso (f ∣_ U)]
    (W : X.Opens) :
    f ⁻¹ᵁ f.isomorphismTargetShrink U W =
      (f ⁻¹ᵁ U) ⊓ W := by
  rw [isomorphismTargetShrink,
    ← image_morphismRestrict_preimage]
  simp only [← Scheme.Hom.comp_preimage,
    IsIso.hom_inv_id_assoc,
    Scheme.Hom.image_preimage_eq_opensRange_inf,
    Scheme.Opens.opensRange_ι]

/-- The morphism remains an isomorphism over the transported open. -/
theorem isIso_isomorphismTargetShrink
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (U : Y.Opens) [IsIso (f ∣_ U)]
    (W : X.Opens) :
    IsIso (f ∣_ f.isomorphismTargetShrink U W) :=
  f.isIso_morphismRestrict_of_le U _
    (f.isomorphismTargetShrink_le U W)

/-- A point lies in the transported target open when its inverse image
over the original open lies in the upstairs open. -/
theorem mem_isomorphismTargetShrink
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (U : Y.Opens) [IsIso (f ∣_ U)]
    (W : X.Opens) (x : U.toScheme)
    (hx :
      (f ⁻¹ᵁ U).ι ((inv (f ∣_ U)) x) ∈ W) :
    U.ι x ∈ f.isomorphismTargetShrink U W := by
  change x ∈ U.ι ⁻¹ᵁ f.isomorphismTargetShrink U W
  rw [isomorphismTargetShrink,
    U.ι.preimage_image_eq]
  exact hx

end AlgebraicGeometry.Scheme.Hom
