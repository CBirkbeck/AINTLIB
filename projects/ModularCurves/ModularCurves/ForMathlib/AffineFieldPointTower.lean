/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.ForMathlib.SchemeModuleOrderedBaseCechAlternating

/-!
# The scalar tower attached to a field-valued point of an affine scheme

For an affine scheme `S` and a field `K` over `Γ(S, ⊤)`, the morphism `Spec K ⟶ S` factors through the
residue field of the point `s` it hits. These two lemmas record the resulting scalar towers

  `Γ(S, ⊤) → Γ(Spec κ(s), ⊤) → K`   and   `Γ(S, ⊤) → κ(s) → K`,

which is what lets a statement about `⊗ K` for an arbitrary field `K` be reduced to the residue fields —
e.g. via `LinearMap.finrank_ker_baseChange_eq` (`ForMathlib/BaseChangeKerCoker.lean`).

There is no elliptic-curve content here. Both lemmas were `private` in
`EllipticCurve/PoleSheafBaseCechHigher.lean`; they are relocated here, unchanged, so that
`ForMathlib/Seesaw.lean` can cite them too instead of duplicating the proofs.
-/

open AlgebraicGeometry CategoryTheory Limits TensorProduct TopologicalSpace

universe u

namespace ModularCurves

theorem affineFieldFactor_isScalarTower
    {S : Scheme.{u}} [IsAffine S]
    (K : Type u) [Field K] [Algebra Γ(S, (⊤ : S.Opens)) K] :
    let t : Spec (.of K) ⟶ S :=
      Spec.map (CommRingCat.ofHom (algebraMap Γ(S, (⊤ : S.Opens)) K)) ≫
        S.isoSpec.inv
    let x := Scheme.SpecToEquivOfField K S t
    let s := x.1
    let ψ := x.2
    let A := Γ(Spec (S.residueField s),
      (⊤ : (Spec (S.residueField s)).Opens))
    letI : Algebra Γ(S, (⊤ : S.Opens)) A :=
      (S.fromSpecResidueField s).appTop.hom.toAlgebra
    let χ : A →+* K :=
      ((Scheme.ΓSpecIso (S.residueField s)).hom ≫ ψ).hom
    letI : Algebra A K := χ.toAlgebra
    IsScalarTower Γ(S, (⊤ : S.Opens)) A K := by
  dsimp only
  let R := Γ(S, (⊤ : S.Opens))
  let t : Spec (.of K) ⟶ S :=
    Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ S.isoSpec.inv
  let x := Scheme.SpecToEquivOfField K S t
  let s := x.1
  let ψ := x.2
  let A := Γ(Spec (S.residueField s),
    (⊤ : (Spec (S.residueField s)).Opens))
  letI : Algebra R A :=
    (S.fromSpecResidueField s).appTop.hom.toAlgebra
  let χ : A →+* K :=
    ((Scheme.ΓSpecIso (S.residueField s)).hom ≫ ψ).hom
  letI : Algebra A K := χ.toAlgebra
  have hfac : Spec.map ψ ≫ S.fromSpecResidueField s = t := by
    simpa only [x, s, ψ, Scheme.SpecToEquivOfField_symm_apply] using
      (Scheme.SpecToEquivOfField K S).symm_apply_apply t
  have hcomp₀ :
      (S.fromSpecResidueField s).appTop ≫
          (Spec.map ψ).appTop ≫ (Scheme.ΓSpecIso (.of K)).hom =
        CommRingCat.ofHom (algebraMap R K) := by
    rw [← Category.assoc]
    rw [← Scheme.Hom.comp_appTop (Spec.map ψ)
      (S.fromSpecResidueField s), hfac]
    dsimp only [t]
    rw [Scheme.Hom.comp_appTop, Category.assoc,
      Scheme.ΓSpecIso_naturality]
    have hΓ : (Scheme.ΓSpecIso (.of R)).hom =
        S.isoSpec.hom.appTop := by
      dsimp only [R]
      exact (Scheme.toSpecΓ_appTop S).symm
    rw [hΓ]
    rw [← Category.assoc]
    rw [← Scheme.Hom.comp_appTop S.isoSpec.hom S.isoSpec.inv,
      S.isoSpec.hom_inv_id]
    simp only [Scheme.Hom.id_app, Category.id_comp]
  have hcomp : CommRingCat.ofHom (algebraMap R K) =
      (S.fromSpecResidueField s).appTop ≫
        (Scheme.ΓSpecIso (S.residueField s)).hom ≫ ψ := by
    rw [← Scheme.ΓSpecIso_naturality ψ]
    exact hcomp₀.symm
  apply IsScalarTower.of_algebraMap_eq'
  change (CommRingCat.ofHom (algebraMap R K)).hom =
    ((S.fromSpecResidueField s).appTop ≫
      (Scheme.ΓSpecIso (S.residueField s)).hom ≫ ψ).hom
  exact congrArg CommRingCat.Hom.hom hcomp

theorem affineFieldFactor_residue_isScalarTower
    {S : Scheme.{u}} [IsAffine S]
    (K : Type u) [Field K] [Algebra Γ(S, (⊤ : S.Opens)) K] :
    let t : Spec (.of K) ⟶ S :=
      Spec.map (CommRingCat.ofHom (algebraMap Γ(S, (⊤ : S.Opens)) K)) ≫
        S.isoSpec.inv
    let x := Scheme.SpecToEquivOfField K S t
    let s := x.1
    let ψ := x.2
    let k := ↑(S.residueField s)
    letI : Algebra Γ(S, (⊤ : S.Opens)) k :=
      ((S.fromSpecResidueField s).appTop ≫
        (Scheme.ΓSpecIso (S.residueField s)).hom).hom.toAlgebra
    letI : Algebra k K := ψ.hom.toAlgebra
    IsScalarTower Γ(S, (⊤ : S.Opens)) k K := by
  dsimp only
  let R := Γ(S, (⊤ : S.Opens))
  let t : Spec (.of K) ⟶ S :=
    Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ S.isoSpec.inv
  let x := Scheme.SpecToEquivOfField K S t
  let s := x.1
  let ψ := x.2
  let k := ↑(S.residueField s)
  letI : Algebra R k :=
    ((S.fromSpecResidueField s).appTop ≫
      (Scheme.ΓSpecIso (S.residueField s)).hom).hom.toAlgebra
  letI : Algebra k K := ψ.hom.toAlgebra
  let A := Γ(Spec (S.residueField s),
    (⊤ : (Spec (S.residueField s)).Opens))
  letI : Algebra R A :=
    (S.fromSpecResidueField s).appTop.hom.toAlgebra
  let χ : A →+* K :=
    ((Scheme.ΓSpecIso (S.residueField s)).hom ≫ ψ).hom
  letI : Algebra A K := χ.toAlgebra
  letI : IsScalarTower R A K := affineFieldFactor_isScalarTower K
  apply IsScalarTower.of_algebraMap_eq
  intro r
  exact IsScalarTower.algebraMap_apply R A K r

end ModularCurves
