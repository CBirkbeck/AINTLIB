/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.EllipticCurve.AbelSkeleton
import ModularCurves.ForMathlib.SchemeModuleBaseCechResidueTransport

/-!
# Assembly of the degree-one fibre cohomology package (`AP2-A1d`)

`hasDegreeOneFibreCohomology_of_fibre_data` assembles `HasDegreeOneFibreCohomology π M U`
(`AbelSkeleton`) from two per-point inputs on an affine-based proper family:

* vanishing of `H^{q+1}` of the fibre pullback of `M` at every point — supplied for a
  presented invertible module by `twoCover_subsingleton_H_one` (`q = 0`, from the
  strong-approximation splitting) and `subsingleton_H_add_two_of_two_affine_open_cover`
  (`q ≥ 1`, generic) through a fibre model;
* the one-dimensionality of the degree-zero Čech kernel after base change to each residue
  field — supplied through the `H⁰` reading (`twoCover_mem_ker_iff` and companions) and
  `ell_eq_one_of_deg_eq_one`.

The composition is the module-generic residue-field route of the pole-sheaf engine: stage B is
`orderedBaseCech_residueField_exactAt_succ_of_pullback_subsingleton_H`, the per-field lifts are
`cochainComplex_baseChange_functionExact_of_map_exactAt`,
`baseChange_exact_of_forall_schemeResidueField_baseChange_exact`, and
`LinearMap.finrank_ker_baseChange_eq`.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace ModularCurves

/-- **(`AP2-A1d`)** The degree-one fibre cohomology package from per-point fibre data:
fibre-pullback cohomology vanishing in positive degrees and residue-field kernel rank one. -/
theorem hasDegreeOneFibreCohomology_of_fibre_data
    {E S : Scheme.{u}} {π : E ⟶ S} [IsProper π] [IsAffine S]
    (M : E.Modules) [M.IsQuasicoherent]
    {ι : Type u} [Fintype ι] [LinearOrder ι] (U : ι → E.Opens)
    (hU : IsOpenCover U) (hUaff : ∀ i, IsAffineOpen (U i))
    (hqc : ∀ s : S, ((Scheme.Modules.pullback
      (pullback.fst π (S.fromSpecResidueField s))).obj M).IsQuasicoherent)
    (hH : ∀ (s : S) (q : ℕ), Subsingleton (CategoryTheory.Sheaf.H
      ((Scheme.Modules.pullback
        (pullback.fst π (S.fromSpecResidueField s))).obj M).sheaf (q + 1)))
    (hker : ∀ s : S,
      letI : Algebra Γ(S, (⊤ : S.Opens)) (S.residueField s) :=
        ((S.fromSpecResidueField s).appTop ≫
          (Scheme.ΓSpecIso (S.residueField s)).hom).hom.toAlgebra
      Module.finrank (S.residueField s)
        (LinearMap.ker (((Scheme.Modules.orderedBaseCechComplex π M U).d 0 1).hom.baseChange
          (S.residueField s))) = 1) :
    HasDegreeOneFibreCohomology π M U := by
  intro K _ _
  constructor
  · -- positive-degree exactness, lifted from the residue fields
    intro n _
    apply ModularCurves.baseChange_exact_of_forall_schemeResidueField_baseChange_exact
      (S := S) _ _ _ K
    intro s
    letI := hqc s
    letI : Algebra Γ(S, (⊤ : S.Opens)) Γ(Spec (S.residueField s),
        (⊤ : (Spec (S.residueField s)).Opens)) :=
      (S.fromSpecResidueField s).appTop.hom.toAlgebra
    exact cochainComplex_baseChange_functionExact_of_map_exactAt _
      (Scheme.Modules.orderedBaseCechComplex π M U) n
      (Scheme.Modules.orderedBaseCech_residueField_exactAt_succ_of_pullback_subsingleton_H
        π M U hU hUaff s n (hH s n))
  · -- the kernel rank, lifted from the residue field of the point below `K`
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
    letI : IsScalarTower R k K := affineFieldFactor_residue_isScalarTower K
    exact (LinearMap.finrank_ker_baseChange_eq k K
      ((Scheme.Modules.orderedBaseCechComplex π M U).d 0 1).hom).trans (hker s)

end ModularCurves
