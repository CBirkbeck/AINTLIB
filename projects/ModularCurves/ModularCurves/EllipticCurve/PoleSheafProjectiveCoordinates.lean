/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.RingTheory.Flat.LocallyFree
import Mathlib.RingTheory.Localization.Free
import ModularCurves.EllipticCurve.PoleSheafProjectiveBaseChange

/-!
# Local coordinates for projectively presented pole-section modules

This file turns finite projectivity and constant rank of the pole-section modules into
bases on principal neighborhoods of the affine base.
-/

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace ModularCurves

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Around every prime of the affine base, the sections of `O(n[0])` on a projectively
presented fibrewise elliptic family admit a basis indexed by `Fin n` on a principal
neighborhood. -/
theorem FibrewiseElliptic.exists_sectionPoleSheafPower_projectiveClosed_away_basis
    {R : Type u} {σ : Type} [CommRing R]
    [Fintype σ] [LinearOrder σ] [Nontrivial σ] [IsNoetherianRing R]
    {E : Scheme.{u}}
    (f : E ⟶ Proj (MvPolynomial.homogeneousSubmodule σ R))
    [IsClosedImmersion f]
    (hsm : SmoothOfRelativeDimension 1
      (f ≫ MvPolynomial.homogeneousProjπ (R := R) (σ := σ)))
    (z : Spec (.of R) ⟶ E)
    (hz : z ≫ (f ≫ MvPolynomial.homogeneousProjπ (R := R) (σ := σ)) =
      𝟙 (Spec (.of R)))
    (h : FibrewiseElliptic
      (f ≫ MvPolynomial.homogeneousProjπ (R := R) (σ := σ)) z hz)
    {n : ℕ} (hn : 1 ≤ n)
    (p : Ideal Γ(Spec (.of R), (⊤ : (Spec (.of R)).Opens))) [p.IsPrime] :
    let π := f ≫ MvPolynomial.homogeneousProjπ (R := R) (σ := σ)
    let M := sectionPoleSheafPower π z hz n
    let B := Γ(Spec (.of R), (⊤ : (Spec (.of R)).Opens))
    ∃ a : B, a ∉ p ∧ Nonempty
      (Module.Basis (Fin n) (Localization.Away a)
        (LocalizedModule.Away a (Scheme.Modules.baseSections π M))) := by
  dsimp only
  let π := f ≫ MvPolynomial.homogeneousProjπ (R := R) (σ := σ)
  let M := sectionPoleSheafPower π z hz n
  let B := Γ(Spec (.of R), (⊤ : (Spec (.of R)).Opens))
  let P := Scheme.Modules.baseSections π M
  obtain ⟨hfinite, hprojective, hrank⟩ :=
    h.sectionPoleSheafPower_projectiveClosed_baseSections_data
      f hsm z hz hn
  letI : Module.Finite B P := hfinite
  letI : Module.Projective B P := hprojective
  letI : Module.FinitePresentation B P :=
    Module.finitePresentation_of_projective B P
  let Rp := Localization.AtPrime p
  let Pp := LocalizedModule.AtPrime p P
  letI : Module.Finite Rp Pp := inferInstance
  letI : Module.Flat Rp Pp := inferInstance
  letI : Module.Free Rp Pp := Module.free_of_flat_of_isLocalRing
  have hrankp : Module.finrank Rp Pp = n := by
    change Module.rankAtStalk (R := B) P ⟨p, inferInstance⟩ = n
    rw [hrank]
  let bp : Module.Basis (Fin n) Rp Pp :=
    Module.finBasisOfFinrankEq Rp Pp hrankp
  obtain ⟨a, ha, ba, _⟩ :=
    Module.FinitePresentation.exists_basis_localizedModule_powers
      p.primeCompl (LocalizedModule.mkLinearMap p.primeCompl P) Rp bp
  exact ⟨a, ha, ⟨ba⟩⟩

end ModularCurves
