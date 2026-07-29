/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.ForMathlib.AcyclicAffineCechComparison
import ModularCurves.ForMathlib.SchemeModuleBaseCechHomology
import ModularCurves.ForMathlib.SchemeModuleBaseCechPushforward
import ModularCurves.ForMathlib.SchemeModuleQuasicoherent

/-!
# Cohomology of pushforwards from affine schemes

This file proves positive-degree cohomology vanishing for the pushforward of a quasicoherent
module along an affine morphism with affine source. The proof transports exactness between
native base-linear Cech complexes and then applies the finite affine-cover Cech comparison.
-/

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Modules

open TopCat TopCat.Sheaf

/-- A quasicoherent module pushed forward along an affine morphism from an affine scheme has
vanishing positive-degree cohomology on a separated target admitting a finite affine cover. -/
theorem subsingleton_H_pushforward_of_isAffineHom
    {X Y : Scheme.{u}} [IsAffine X] [Y.IsSeparated]
    (f : X ⟶ Y) [IsAffineHom f]
    (M : X.Modules) [M.IsQuasicoherent]
    {ι : Type u} [Finite ι]
    (U : ι → Y.Opens) (hU : IsOpenCover U)
    (hUaff : ∀ i, IsAffineOpen (U i)) (n : ℕ) :
    Subsingleton (CategoryTheory.Sheaf.H
      ((pushforward f).obj M).sheaf (n + 1)) := by
  let N := (pushforward f).obj M
  letI : N.IsQuasicoherent :=
    isQuasicoherent_pushforward_of_isAffineHom f
  let Uf : ι → X.Opens := fun i => f ⁻¹ᵁ U i
  have hUf : IsOpenCover Uf := f.iSup_preimage_eq_top hU
  have hUfaff : ∀ i, IsAffineOpen (Uf i) :=
    fun i => (hUaff i).preimage f
  have hSourceNative :
      ((cechComplexFunctor Uf).obj M.sheaf.obj).ExactAt (n + 1) :=
    cechComplex_exactAt_succ_of_affine_openCover M Uf hUf hUfaff n
      (affine_subsingleton_H M n)
  have hSourceBase :
      (baseCechComplex (f ≫ 𝟙 Y) M Uf).ExactAt (n + 1) :=
    (baseCechComplex_exactAt_iff (f ≫ 𝟙 Y) M Uf (n + 1)).2
      hSourceNative
  have hTargetBase :
      (baseCechComplex (𝟙 Y) N U).ExactAt (n + 1) :=
    hSourceBase.of_iso (baseCechComplexPushforwardIso f (𝟙 Y) M U)
  have hTargetNative :
      ((cechComplexFunctor U).obj N.sheaf.obj).ExactAt (n + 1) :=
    (baseCechComplex_exactAt_iff (𝟙 Y) N U (n + 1)).1 hTargetBase
  exact
    (cechComplex_exactAt_succ_iff_subsingleton_H_of_subsingleton_restrict_H
      U N.sheaf (by simpa only [IsOpenCover] using hU)
      (fun p i q => cechIntersection_subsingleton_H N U hUaff p i q) n).1
      hTargetNative

end AlgebraicGeometry.Scheme.Modules
