/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.EllipticCurve.AbelSkeleton
import ModularCurves.ForMathlib.SchemeModuleBaseCechResidueTransport
import ModularCurves.ForMathlib.SchemeModuleProperLowDegreeCechFinite
import ModularCurves.ForMathlib.SchemeModuleOrderedBaseCechZero

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

/-- The exists-cover form of `hasDegreeOneFibreCohomology_of_fibre_data`: a proper family over
an affine base always admits a finite affine cover, so per-point fibre data yields the package
on some cover, provided the residue-field kernel rank is available on every such cover. -/
theorem exists_hasDegreeOneFibreCohomology_of_fibre_data
    {E S : Scheme.{u}} {π : E ⟶ S} [IsProper π] [IsAffine S]
    (M : E.Modules) [M.IsQuasicoherent]
    (hqc : ∀ s : S, ((Scheme.Modules.pullback
      (pullback.fst π (S.fromSpecResidueField s))).obj M).IsQuasicoherent)
    (hH : ∀ (s : S) (q : ℕ), Subsingleton (CategoryTheory.Sheaf.H
      ((Scheme.Modules.pullback
        (pullback.fst π (S.fromSpecResidueField s))).obj M).sheaf (q + 1)))
    (hker : ∀ {ι : Type u} [Fintype ι] [LinearOrder ι] (U : ι → E.Opens),
      IsOpenCover U → (∀ i, IsAffineOpen (U i)) → ∀ s : S,
      letI : Algebra Γ(S, (⊤ : S.Opens)) (S.residueField s) :=
        ((S.fromSpecResidueField s).appTop ≫
          (Scheme.ΓSpecIso (S.residueField s)).hom).hom.toAlgebra
      Module.finrank (S.residueField s)
        (LinearMap.ker (((Scheme.Modules.orderedBaseCechComplex π M U).d 0 1).hom.baseChange
          (S.residueField s))) = 1) :
    ∃ (ι : Type u) (_ : Fintype ι) (_ : LinearOrder ι) (U : ι → E.Opens),
      IsOpenCover U ∧ (∀ i, IsAffineOpen (U i)) ∧
        HasDegreeOneFibreCohomology π M U := by
  obtain ⟨ι, hι, U, hU, hUaff, -⟩ :=
    π.exists_finite_affine_openCover_of_isProper
  letI : Finite ι := hι
  letI : Fintype ι := Fintype.ofFinite ι
  letI : LinearOrder ι := IsWellOrder.linearOrder WellOrderingRel
  exact ⟨ι, inferInstance, inferInstance, U, hU, hUaff,
    hasDegreeOneFibreCohomology_of_fibre_data M U hU hUaff hqc hH
      (hker U hU hUaff)⟩

/-- **(`AP2-A2`, kernel data)** For an invertible module with the degree-one fibre cohomology
package on a proper family over a Noetherian affine base, the degree-zero Čech kernel — the
pushforward's sections — is finite projective of constant rank one, and commutes with
arbitrary algebra base change. Module-generic instance of the pole-sheaf model
(`sectionPoleSheafPower_projectiveClosed_orderedBaseCech_kernel_data`). -/
theorem kernel_data_of_hasDegreeOneFibreCohomology
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    {E : Scheme.{u}} {π : E ⟶ Spec (.of R)} [IsProper π] [Flat π]
    [IsNoetherian E] [LocallyOfFinitePresentation π]
    (M : E.Modules) (hM : M.IsInvertible)
    {ι : Type u} [Fintype ι] [LinearOrder ι] (U : ι → E.Opens)
    (hU : IsOpenCover U) (hUaff : ∀ i, IsAffineOpen (U i))
    (hpkg : HasDegreeOneFibreCohomology π M U) :
    let C := Scheme.Modules.orderedBaseCechComplex π M U
    let B := Γ(Spec (.of R), (⊤ : (Spec (.of R)).Opens))
    Module.Finite B (LinearMap.ker (C.d 0 1).hom) ∧
      Module.Projective B (LinearMap.ker (C.d 0 1).hom) ∧
      (∀ (A : Type u) [CommRing A] [Algebra B A],
        Function.Bijective (kerBaseChangeComparison A (C.d 0 1).hom)) ∧
      Module.rankAtStalk (R := B) (LinearMap.ker (C.d 0 1).hom) = fun _ ↦ 1 := by
  dsimp only
  let C := Scheme.Modules.orderedBaseCechComplex π M U
  let B := Γ(Spec (.of R), (⊤ : (Spec (.of R)).Opens))
  letI : E.IsSeparated := ⟨by
    rw [← terminal.comp_from π]
    infer_instance⟩
  letI : M.IsQuasicoherent := hM.isQuasicoherent
  letI : M.IsFinitePresentation := hM.isFinitePresentation
  letI : M.IsFiniteType :=
    SheafOfModules.instIsFiniteTypeOfIsFinitePresentation M
  letI (q : ℕ) : Module.Flat B (C.X q) :=
    Scheme.Modules.orderedBaseCechObject_flat_of_isInvertible π M hM U hUaff q
  have hfinite := Scheme.Modules.orderedBaseCechHomologyFinite_of_isProper
    (xπ := π) U hU hUaff M
  letI (q : ℕ) : Module.Finite B (C.homology q) := hfinite q
  let N := Fintype.card ι
  letI : Subsingleton (C.X (N + 1)) :=
    Scheme.Modules.orderedBaseCechObject_subsingleton_of_card_le π M U (N + 1)
      (Nat.le_succ N)
  have hexact : ∀ q, q < N →
      Function.Exact (C.d q (q + 1)).hom (C.d (q + 1) (q + 2)).hom := by
    intro q hq
    exact
      HomologicalComplex.functionExact_of_bounded_flat_forall_field_baseChange_exact_of_finite_homology
        C N (fun i hi K _ _ ↦ (hpkg K).1 i hi) q hq
  have hkerFinite : Module.Finite B (LinearMap.ker (C.d 0 1).hom) :=
    HomologicalComplex.finite_kernel_zero_of_finite_homology C
  letI : Module.Finite B (LinearMap.ker (C.d 0 1).hom) := hkerFinite
  letI : IsNoetherianRing B :=
    isNoetherianRing_of_ringEquiv R
      (Scheme.ΓSpecIso (.of R)).symm.commRingCatIsoToRingEquiv
  have hkerProjective : Module.Projective B (LinearMap.ker (C.d 0 1).hom) :=
    Module.Projective.ker_of_bounded_exact_of_finite
      (fun q ↦ C.X q) (fun q ↦ (C.d q (q + 1)).hom) N hexact
  letI : Module.Projective B (LinearMap.ker (C.d 0 1).hom) := hkerProjective
  have hbase : ∀ (A : Type u) [CommRing A] [Algebra B A],
      Function.Bijective (kerBaseChangeComparison A (C.d 0 1).hom) := by
    intro A _ _
    exact kerBaseChangeComparison_bijective_of_bounded_exact
      A (fun q ↦ C.X q) (fun q ↦ (C.d q (q + 1)).hom) N hexact
  have hrankAt :
      Module.rankAtStalk (R := B) (LinearMap.ker (C.d 0 1).hom) = fun _ ↦ 1 := by
    letI : Module.Flat B (LinearMap.ker (C.d 0 1).hom) := inferInstance
    funext p
    rw [Module.rankAtStalk_eq]
    let e : p.asIdeal.Fiber (LinearMap.ker (C.d 0 1).hom) ≃ₗ[p.asIdeal.ResidueField]
        LinearMap.ker ((C.d 0 1).hom.baseChange p.asIdeal.ResidueField) :=
      LinearEquiv.ofBijective
        (kerBaseChangeComparison p.asIdeal.ResidueField (C.d 0 1).hom)
        (hbase p.asIdeal.ResidueField)
    exact e.finrank_eq.trans (hpkg p.asIdeal.ResidueField).2
  exact ⟨hkerFinite, hkerProjective, hbase, hrankAt⟩

/-- **(`AP2-A2`, sections form)** Under the kernel-data hypotheses, the pushforward's global
sections `baseSections π M` are finite projective of constant rank one over the base ring. -/
theorem baseSections_data_of_hasDegreeOneFibreCohomology
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    {E : Scheme.{u}} {π : E ⟶ Spec (.of R)} [IsProper π] [Flat π]
    [IsNoetherian E] [LocallyOfFinitePresentation π]
    (M : E.Modules) (hM : M.IsInvertible)
    {ι : Type u} [Fintype ι] [LinearOrder ι] (U : ι → E.Opens)
    (hU : IsOpenCover U) (hUaff : ∀ i, IsAffineOpen (U i))
    (hpkg : HasDegreeOneFibreCohomology π M U) :
    let B := Γ(Spec (.of R), (⊤ : (Spec (.of R)).Opens))
    Module.Finite B (Scheme.Modules.baseSections π M) ∧
      Module.Projective B (Scheme.Modules.baseSections π M) ∧
      Module.rankAtStalk (R := B) (Scheme.Modules.baseSections π M) = fun _ ↦ 1 := by
  dsimp only
  let C := Scheme.Modules.orderedBaseCechComplex π M U
  let B := Γ(Spec (.of R), (⊤ : (Spec (.of R)).Opens))
  obtain ⟨hfinite, hprojective, -, hrank⟩ :=
    kernel_data_of_hasDegreeOneFibreCohomology M hM U hU hUaff hpkg
  letI : Module.Finite B (LinearMap.ker (C.d 0 1).hom) := hfinite
  letI : Module.Projective B (LinearMap.ker (C.d 0 1).hom) := hprojective
  let e := (Scheme.Modules.baseSectionsIsoKernelOrderedBaseCechDifferential
    π M U hU).toLinearEquiv
  exact ⟨Module.Finite.equiv e.symm, Module.Projective.of_equiv' e.symm,
    (Module.rankAtStalk_eq_of_equiv e).trans hrank⟩

end ModularCurves
