/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.WeilPairing.FieldLeaf

/-!
# The glue dataset ([G2])

`exists_normalized_chart_dataset`: the zero-section–normalized dataset built from the
common-principal chart family, with transitions **dressed by the generator ratios** on
every overlap. This is `exists_normalized_dataset` (KMDataset) replayed with the
`[G1]` chart family in place of the invertibility choice, tracking the transition
formula through the normalisation's refine-and-rescale.
-/

universe u

open CategoryTheory AlgebraicGeometry Limits TopologicalSpace

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace ModularCurves

variable {S : Scheme.{u}} (E : EllipticCurve S) {T : Scheme.{u}}
variable (hsm : SmoothOfRelativeDimension 1 E.π) [IsSeparated E.π] (t : T ⟶ S)

/-- **([G2] the normalized chart dataset)** From a `κ(Q)`-presentation `M` with a
tensor-ideal dictionary and common-principal covers for both ideals, there is a
zero-section–normalized trivialisation dataset for `M` whose transitions on every
inhabited overlap are the generator-ratio units up to overlap-unit dressing, with the
generator data exposed at the charts. -/
theorem exists_normalized_chart_dataset
    (Q : (E.baseChange t).Point (𝟙 T)) (M : (CategoryTheory.Limits.pullback E.π t).Modules)
    (hM : letI := Scheme.Modules.monoidalCategory (CategoryTheory.Limits.pullback E.π t)
      (kappa E hsm t Q).val = toSkeleton M)
    [AlgebraicGeometry.IsIntegral (CategoryTheory.Limits.pullback E.π t)]
    [IsAffineHom (Limits.pullback.diagonal (Limits.terminal.from (CategoryTheory.Limits.pullback E.π t)))]
    (J₁ J₂ : (CategoryTheory.Limits.pullback E.π t).IdealSheafData)
    (e_dict : M.tensorObj (Scheme.Modules.idealModule J₁) ≅ Scheme.Modules.idealModule J₂)
    (h₁ : ∀ c : ↥(CategoryTheory.Limits.pullback E.π t), ∃ V : (CategoryTheory.Limits.pullback E.π t).affineOpens,
      c ∈ V.1 ∧ ∃ f : ↑((CategoryTheory.Limits.pullback E.π t).presheaf.obj (Opposite.op (V.1))),
      J₁.ideal V = Ideal.span {f} ∧ f ∈ nonZeroDivisors ↑((CategoryTheory.Limits.pullback E.π t).presheaf.obj (Opposite.op (V.1))))
    (h₂ : ∀ c : ↥(CategoryTheory.Limits.pullback E.π t), ∃ V : (CategoryTheory.Limits.pullback E.π t).affineOpens,
      c ∈ V.1 ∧ ∃ f : ↑((CategoryTheory.Limits.pullback E.π t).presheaf.obj (Opposite.op (V.1))),
      J₂.ideal V = Ideal.span {f} ∧ f ∈ nonZeroDivisors ↑((CategoryTheory.Limits.pullback E.π t).presheaf.obj (Opposite.op (V.1)))) :
    ∃ (V : ↥(CategoryTheory.Limits.pullback E.π t) → (CategoryTheory.Limits.pullback E.π t).affineOpens)
      (f₁ f₂ : ∀ c, ↑((CategoryTheory.Limits.pullback E.π t).presheaf.obj (Opposite.op ((V c).1))))
      (ι' : Type u) (W : ι' → (CategoryTheory.Limits.pullback E.π t).Opens) (_ : iSup W = ⊤)
      (e : ∀ i, M.over (W i) ≅
        _root_.SheafOfModules.unit ((CategoryTheory.Limits.pullback E.π t).ringCatSheaf.over (W i))),
      (∀ c, J₁.ideal (V c) = Ideal.span {f₁ c}) ∧
      (∀ c, f₁ c ∈ nonZeroDivisors ↑((CategoryTheory.Limits.pullback E.π t).presheaf.obj (Opposite.op ((V c).1)))) ∧
      (∀ c, J₂.ideal (V c) = Ideal.span {f₂ c}) ∧
      (∀ c, f₂ c ∈ nonZeroDivisors ↑((CategoryTheory.Limits.pullback E.π t).presheaf.obj (Opposite.op ((V c).1)))) ∧
      (∀ i j, transitionUnitOfCover M W e i j ∈
        sectionUnits (Scheme.Modules.baseChangeZero E.π E.zero E.zero_π t) (W i ⊓ W j)) ∧
      (∀ i j, Nonempty ↥((W i ⊓ W j) : (CategoryTheory.Limits.pullback E.π t).Opens) →
        ∃ (c d : ↥(CategoryTheory.Limits.pullback E.π t)) (hWc : W i ≤ (V c).1) (hWd : W j ≤ (V d).1)
          (a b u₁ u₂ : ↑((CategoryTheory.Limits.pullback E.π t).presheaf.obj (Opposite.op (W i ⊓ W j)))ˣ),
          transitionUnitOfCover M W e i j = a * (u₂ * u₁⁻¹) * b⁻¹ ∧
          (CategoryTheory.Limits.pullback E.π t).presheaf.map
              (homOfLE ((inf_le_left).trans hWc : W i ⊓ W j ≤ (V c).1)).op (f₁ c) =
            (CategoryTheory.Limits.pullback E.π t).presheaf.map
              (homOfLE ((inf_le_right).trans hWd : W i ⊓ W j ≤ (V d).1)).op (f₁ d) *
              (u₁ : ↑((CategoryTheory.Limits.pullback E.π t).presheaf.obj (Opposite.op (W i ⊓ W j)))) ∧
          (CategoryTheory.Limits.pullback E.π t).presheaf.map
              (homOfLE ((inf_le_left).trans hWc : W i ⊓ W j ≤ (V c).1)).op (f₂ c) =
            (CategoryTheory.Limits.pullback E.π t).presheaf.map
              (homOfLE ((inf_le_right).trans hWd : W i ⊓ W j ≤ (V d).1)).op (f₂ d) *
              (u₂ : ↑((CategoryTheory.Limits.pullback E.π t).presheaf.obj (Opposite.op (W i ⊓ W j))))) := by
  sorry

end ModularCurves
