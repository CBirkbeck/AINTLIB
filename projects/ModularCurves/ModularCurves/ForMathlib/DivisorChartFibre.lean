/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import ModularCurves.ForMathlib.FibrewiseFinite

/-!
# A smooth chart on which a finite closed subscheme has finite fibres

Let `π : C ⟶ S` be smooth of relative dimension `n` and let `J` be an ideal sheaf whose
closed subscheme is **finite over `S`** (the situation of a relative effective Cartier
divisor). Around any point `c` of the support we produce a standard-smooth affine chart
`V₀ ⊆ C` over an affine `U₀ ⊆ S` on which `Γ(C,V₀) ⧸ J(V₀)` has **finite fibres** over
`Γ(S,U₀)` (`ModularCurves.HasFiniteFibres`).

The finiteness of `J`'s subscheme over `S` does **not** survive to a chart — a chart cuts the
subscheme down to an open piece, and an open piece of a finite scheme is finite only over the
locus where it is *clopen*, which Zariski-locally one cannot arrange (splitting a fibre point
off needs henselisation). Arranging containment in a single affine instead would need `C/S`
quasi-projective, which is not available for an abstract relative curve.

What *does* work — and is what the consumers need — is to shrink the chart so that the trace
of the subscheme on it is a **basic** open of an affine chart of the subscheme
(`exists_basicOpen_chart`). Then `Γ` of that trace is a localization away from one element of
a module-finite algebra, and `module_finite_tensor_of_localizationAway` applies fibre by
fibre.
-/

universe u

open CategoryTheory AlgebraicGeometry TensorProduct

namespace ModularCurves

variable {C S : Scheme.{u}}

/-- **Chart shrinking.** Given an affine chart `V₁ ∋ c` of `C` over an affine `U₀ ⊆ S`, there
is a function `a` on `V₁`, nonvanishing at `c`, such that the trace of the closed subscheme
of `J` on the basic open `C.basicOpen a` is a *basic* open of the affine chart
`(J.subschemeι ≫ π) ⁻¹ᵁ U₀` of that subscheme.

The point: basic opens of an affine are localizations at one element, and that is what
survives base change to a fibre. -/
theorem exists_basicOpen_chart (π : C ⟶ S) (J : C.IdealSheafData)
    [IsFinite (J.subschemeι ≫ π)] {U₀ : S.Opens} (hU₀ : IsAffineOpen U₀)
    {V₁ : C.Opens} (hV₁ : IsAffineOpen V₁) (e₁ : V₁ ≤ π ⁻¹ᵁ U₀) {c : C} (hcV₁ : c ∈ V₁)
    (d : J.subscheme) (hd : J.subschemeι.base d = c) :
    ∃ (a : Γ(C, V₁)) (b : Γ(J.subscheme, (J.subschemeι ≫ π) ⁻¹ᵁ U₀)),
      c ∈ C.basicOpen a ∧
      J.subschemeι ⁻¹ᵁ (C.basicOpen a) = J.subscheme.basicOpen b := by
  classical
  have hGU : IsAffineOpen ((J.subschemeι ≫ π) ⁻¹ᵁ U₀) := hU₀.preimage (J.subschemeι ≫ π)
  have hdW₁ : d ∈ J.subschemeι ⁻¹ᵁ V₁ := by
    show J.subschemeι.base d ∈ V₁
    rw [hd]; exact hcV₁
  have hW₁GU : (J.subschemeι ⁻¹ᵁ V₁) ≤ (J.subschemeι ≫ π) ⁻¹ᵁ U₀ := fun x hx => e₁ hx
  obtain ⟨b, hbW₁, hdb⟩ :=
    hGU.exists_basicOpen_le (⟨d, hdW₁⟩ : (J.subschemeι ⁻¹ᵁ V₁)) (hW₁GU hdW₁)
  obtain ⟨a, ha⟩ := J.subschemeι_app_surjective ⟨V₁, hV₁⟩
    (J.subscheme.presheaf.map (homOfLE hW₁GU).op b)
  have hpre : J.subschemeι ⁻¹ᵁ (C.basicOpen a) = J.subscheme.basicOpen b := by
    rw [Scheme.preimage_basicOpen, ha, Scheme.basicOpen_res]
    exact inf_eq_right.mpr hbW₁
  refine ⟨a, b, ?_, hpre⟩
  have hmem : d ∈ J.subschemeι ⁻¹ᵁ (C.basicOpen a) := by rw [hpre]; exact hdb
  have : J.subschemeι.base d ∈ C.basicOpen a := hmem
  rwa [hd] at this

/-- The `Γ(S,U₀)`-algebra comparison `Γ(subscheme, ι⁻¹V) ≃ Γ(C,V) ⧸ J(V)` on an affine chart
`V` lying over an affine `U₀`. -/
noncomputable def subschemeChartAlgEquiv (π : C ⟶ S) (J : C.IdealSheafData) {U₀ : S.Opens}
    {V : C.Opens} (hV : IsAffineOpen V) (e : V ≤ π ⁻¹ᵁ U₀)
    (e' : J.subschemeι ⁻¹ᵁ V ≤ (J.subschemeι ≫ π) ⁻¹ᵁ U₀) :
    letI : Algebra Γ(S, U₀) Γ(C, V) := (π.appLE U₀ V e).hom.toAlgebra
    letI : Algebra Γ(S, U₀) Γ(J.subscheme, J.subschemeι ⁻¹ᵁ V) :=
      ((J.subschemeι ≫ π).appLE U₀ (J.subschemeι ⁻¹ᵁ V) e').hom.toAlgebra
    Γ(J.subscheme, J.subschemeι ⁻¹ᵁ V) ≃ₐ[Γ(S, U₀)] (Γ(C, V) ⧸ J.ideal ⟨V, hV⟩) := by
  letI : Algebra Γ(S, U₀) Γ(C, V) := (π.appLE U₀ V e).hom.toAlgebra
  letI : Algebra Γ(S, U₀) Γ(J.subscheme, J.subschemeι ⁻¹ᵁ V) :=
    ((J.subschemeι ≫ π).appLE U₀ (J.subschemeι ⁻¹ᵁ V) e').hom.toAlgebra
  have hcomp : (J.subschemeι ≫ π).appLE U₀ (J.subschemeι ⁻¹ᵁ V) e' ≫
      (J.subschemeObjIso (⟨V, hV⟩ : C.affineOpens)).hom
      = π.appLE U₀ V e ≫ CommRingCat.ofHom (Ideal.Quotient.mk (J.ideal ⟨V, hV⟩)) := by
    have h1 : (J.subschemeι ≫ π).appLE U₀ (J.subschemeι ⁻¹ᵁ V) e'
        = π.appLE U₀ V e ≫ J.subschemeι.appLE V (J.subschemeι ⁻¹ᵁ V) le_rfl := by
      rw [Scheme.Hom.appLE_comp_appLE]
    have h2 : J.subschemeι.appLE V (J.subschemeι ⁻¹ᵁ V) le_rfl = J.subschemeι.app V :=
      Scheme.Hom.appLE_eq_app _
    rw [h1, h2, J.subschemeι_app ⟨V, hV⟩, Category.assoc, Category.assoc,
      Iso.inv_hom_id, Category.comp_id]
  refine AlgEquiv.ofRingEquiv
    (f := Iso.commRingCatIsoToRingEquiv (J.subschemeObjIso (⟨V, hV⟩ : C.affineOpens)))
    (fun r => ?_)
  exact congrArg
    (fun w : Γ(S, U₀) ⟶ CommRingCat.of (Γ(C, V) ⧸ J.ideal ⟨V, hV⟩) => w.hom r) hcomp

/-- **The chart existence theorem.** Around any point of the support of an ideal sheaf whose
closed subscheme is finite over `S`, a smooth relative scheme has a standard-smooth affine
chart on which the quotient has finite fibres over the base. -/
theorem exists_affineChart_hasFiniteFibres (π : C ⟶ S) (J : C.IdealSheafData)
    [IsFinite (J.subschemeι ≫ π)] (n : ℕ) [SmoothOfRelativeDimension n π] (c : C)
    (hc : c ∈ J.support) :
    ∃ (U₀ : S.Opens) (_ : IsAffineOpen U₀) (V₀ : C.Opens) (hV₀ : IsAffineOpen V₀)
      (_ : c ∈ V₀) (e₀ : V₀ ≤ π ⁻¹ᵁ U₀)
      (_ : RingHom.IsStandardSmoothOfRelativeDimension n (π.appLE U₀ V₀ e₀).hom),
      letI : Algebra Γ(S, U₀) Γ(C, V₀) := (π.appLE U₀ V₀ e₀).hom.toAlgebra
      HasFiniteFibres Γ(S, U₀) Γ(C, V₀) (J.ideal ⟨V₀, hV₀⟩) := by
  classical
  obtain ⟨U₀, hU₀, V₁, hV₁, hcV₁, e₁, hstd₁⟩ :=
    SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension (n := n) (f := π) c
  obtain ⟨d, hd⟩ : ∃ d, J.subschemeι.base d = c := by
    have := J.range_subschemeι
    rw [Set.ext_iff] at this
    exact (this c).mpr hc
  obtain ⟨a, b, hca, hpre⟩ :=
    exists_basicOpen_chart π J hU₀ hV₁ e₁ hcV₁ d hd
  have hGU : IsAffineOpen ((J.subschemeι ≫ π) ⁻¹ᵁ U₀) := hU₀.preimage (J.subschemeι ≫ π)
  have eW₀ : (J.subschemeι ⁻¹ᵁ (C.basicOpen a)) ≤ (J.subschemeι ≫ π) ⁻¹ᵁ U₀ :=
    fun x hx => ((C.basicOpen_le a).trans e₁) hx
  haveI : IsLocalization.Away a Γ(C, C.basicOpen a) := hV₁.isLocalization_basicOpen a
  refine ⟨U₀, hU₀, C.basicOpen a, hV₁.basicOpen a, hca,
    (C.basicOpen_le a).trans e₁, ?_, ?_⟩
  · -- standard smoothness: `Γ(C, D(a))` is a localization away of the standard-smooth `Γ(C,V₁)`
    have h := (RingHom.isStandardSmoothOfRelativeDimension_stableUnderCompositionWithLocalizationAway
      (n := n)).right Γ(C, C.basicOpen a) a (π.appLE U₀ V₁ e₁).hom hstd₁
    have heq : (algebraMap Γ(C, V₁) Γ(C, C.basicOpen a)).comp (π.appLE U₀ V₁ e₁).hom
        = (π.appLE U₀ (C.basicOpen a) ((C.basicOpen_le a).trans e₁)).hom := by
      rw [RingHom.algebraMap_toAlgebra, ← CommRingCat.hom_comp, Scheme.Hom.appLE_map]
    rwa [heq] at h
  · -- fibrewise finiteness, via the basic-open trace on the finite subscheme
    letI instGU : Algebra Γ(S, U₀) Γ(J.subscheme, (J.subschemeι ≫ π) ⁻¹ᵁ U₀) :=
      ((J.subschemeι ≫ π).app U₀).hom.toAlgebra
    letI instW : Algebra Γ(S, U₀) Γ(J.subscheme, J.subschemeι ⁻¹ᵁ (C.basicOpen a)) :=
      ((J.subschemeι ≫ π).appLE U₀ (J.subschemeι ⁻¹ᵁ (C.basicOpen a)) eW₀).hom.toAlgebra
    letI instA : Algebra Γ(S, U₀) Γ(C, C.basicOpen a) :=
      (π.appLE U₀ (C.basicOpen a) ((C.basicOpen_le a).trans e₁)).hom.toAlgebra
    letI instBW : Algebra Γ(J.subscheme, (J.subschemeι ≫ π) ⁻¹ᵁ U₀)
        Γ(J.subscheme, J.subschemeι ⁻¹ᵁ (C.basicOpen a)) :=
      (J.subscheme.presheaf.map (homOfLE eW₀).op).hom.toAlgebra
    haveI : IsScalarTower Γ(S, U₀) Γ(J.subscheme, (J.subschemeι ≫ π) ⁻¹ᵁ U₀)
        Γ(J.subscheme, J.subschemeι ⁻¹ᵁ (C.basicOpen a)) := by
      refine IsScalarTower.of_algebraMap_eq' ?_
      rw [RingHom.algebraMap_toAlgebra, RingHom.algebraMap_toAlgebra,
        RingHom.algebraMap_toAlgebra, ← CommRingCat.hom_comp,
        ← Scheme.Hom.appLE_eq_app (f := J.subschemeι ≫ π) (U := U₀), Scheme.Hom.appLE_map]
    haveI : IsLocalization.Away b Γ(J.subscheme, J.subschemeι ⁻¹ᵁ (C.basicOpen a)) :=
      hGU.isLocalization_of_eq_basicOpen b (homOfLE eW₀) hpre
    haveI : Module.Finite Γ(S, U₀) Γ(J.subscheme, (J.subschemeι ≫ π) ⁻¹ᵁ U₀) :=
      IsFinite.finite_app (J.subschemeι ≫ π) U₀ hU₀
    exact hasFiniteFibres_of_algEquiv Γ(S, U₀) Γ(C, C.basicOpen a) _
      (subschemeChartAlgEquiv π J (hV₁.basicOpen a) ((C.basicOpen_le a).trans e₁) eW₀)
      (fun K _ _ => module_finite_tensor_of_localizationAway Γ(S, U₀)
        Γ(J.subscheme, (J.subschemeι ≫ π) ⁻¹ᵁ U₀) K _ b)

end ModularCurves
