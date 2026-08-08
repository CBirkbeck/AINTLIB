/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.EllipticCurve.PoleSheafBaseCechHigher

/-!
# Residue-field transport for base-linear Čech exactness, module-generically

The pole-sheaf line (`PoleSheafBaseCechHigher`) transports fibre cohomology vanishing to
base-changed Čech exactness for `𝒪(n[0])` specifically. This file extracts the transport
**for an arbitrary quasicoherent module**: the only fibre input is vanishing of `H^{q+1}` of
the fibre pullback of `M`, and the output is exactness at `q + 1` of the ordered base-linear
Čech complex after extension of scalars to the residue field. Consumed by `AP2-A1d`, whose
fibre input is produced by `twoCover_subsingleton_H_one` (`q = 0`) and
`subsingleton_H_add_two_of_two_affine_open_cover` (`q ≥ 1`) on a presented invertible module.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Modules

noncomputable section

/-- Module-generic residue-field transport, unordered form: if the fibre pullback of `M` at
`s` has vanishing `H^{q+1}`, then the base-linear Čech complex of any finite affine cover is
exact at `q + 1` after extension of scalars to the residue field of `s`. -/
theorem baseCech_residueField_exactAt_succ_of_pullback_subsingleton_H
    {E S : Scheme.{u}} (π : E ⟶ S) [IsProper π] [IsAffine S] (M : E.Modules)
    [M.IsQuasicoherent]
    {ι : Type u} [Fintype ι] (U : ι → E.Opens)
    (hU : IsOpenCover U) (hUaff : ∀ i, IsAffineOpen (U i)) (s : S) (q : ℕ)
    [((Scheme.Modules.pullback
      (pullback.fst π (S.fromSpecResidueField s))).obj M).IsQuasicoherent]
    (hH : Subsingleton (CategoryTheory.Sheaf.H
      ((Scheme.Modules.pullback
        (pullback.fst π (S.fromSpecResidueField s))).obj M).sheaf (q + 1))) :
    (((ModuleCat.extendScalars
        (S.fromSpecResidueField s).appTop.hom).mapHomologicalComplex
          (.up ℕ)).obj
      (Scheme.Modules.baseCechComplex π M U)).ExactAt (q + 1) := by
  let t := S.fromSpecResidueField s
  let Uf : ι → (π.fiber s).Opens :=
    fun i ↦ pullback.fst π t ⁻¹ᵁ U i
  letI : E.IsSeparated := ⟨by
    rw [← terminal.comp_from π]
    infer_instance⟩
  letI hsepFiber : IsSeparated (π.fiberToSpecResidueField s) := by
    change IsSeparated (pullback.snd π t)
    infer_instance
  letI : (π.fiber s).IsSeparated := ⟨by
    rw [← terminal.comp_from (π.fiberToSpecResidueField s)]
    infer_instance⟩
  letI : (Limits.pullback π t).IsSeparated := ⟨by
    rw [← terminal.comp_from (pullback.snd π t)]
    infer_instance⟩
  have hUf : IsOpenCover Uf :=
    Scheme.Hom.iSup_preimage_eq_top (pullback.fst π t) hU
  have hUfaff : ∀ i, IsAffineOpen (Uf i) := by
    intro i
    exact IsAffineOpen.preimage_pullback_fst π t (hUaff i)
  have hNativeExact :
      ((cechComplexFunctor Uf).obj
        ((Scheme.Modules.pullback (pullback.fst π t)).obj M).sheaf.obj).ExactAt
          (q + 1) := by
    exact Scheme.Modules.cechComplex_exactAt_succ_of_affine_openCover
      (U := Uf) ((Scheme.Modules.pullback (pullback.fst π t)).obj M)
        hUf hUfaff q hH
  have hFiberExact :
      (Scheme.Modules.baseCechComplex (pullback.snd π t)
        ((Scheme.Modules.pullback (pullback.fst π t)).obj M) Uf).ExactAt
          (q + 1) := by
    exact (Scheme.Modules.baseCechComplex_exactAt_iff
      (pullback.snd π t)
      ((Scheme.Modules.pullback (pullback.fst π t)).obj M)
      Uf (q + 1)).mpr hNativeExact
  exact hFiberExact.of_iso
    (Scheme.Modules.baseCechComplexBaseChangeIso
      π t M U hUaff).symm

/-- Module-generic residue-field transport, ordered form: the ordered base-linear Čech complex
is exact at `q + 1` after extension of scalars to the residue field, given fibre `H^{q+1}`
vanishing. -/
theorem orderedBaseCech_residueField_exactAt_succ_of_pullback_subsingleton_H
    {E S : Scheme.{u}} (π : E ⟶ S) [IsProper π] [IsAffine S] (M : E.Modules)
    [M.IsQuasicoherent]
    {ι : Type u} [Fintype ι] [LinearOrder ι] (U : ι → E.Opens)
    (hU : IsOpenCover U) (hUaff : ∀ i, IsAffineOpen (U i)) (s : S) (q : ℕ)
    [((Scheme.Modules.pullback
      (pullback.fst π (S.fromSpecResidueField s))).obj M).IsQuasicoherent]
    (hH : Subsingleton (CategoryTheory.Sheaf.H
      ((Scheme.Modules.pullback
        (pullback.fst π (S.fromSpecResidueField s))).obj M).sheaf (q + 1))) :
    (((ModuleCat.extendScalars
        (S.fromSpecResidueField s).appTop.hom).mapHomologicalComplex
          (.up ℕ)).obj
      (Scheme.Modules.orderedBaseCechComplex π M U)).ExactAt (q + 1) := by
  let F := (ModuleCat.extendScalars
    (S.fromSpecResidueField s).appTop.hom).mapHomologicalComplex (.up ℕ)
  have hbase :=
    baseCech_residueField_exactAt_succ_of_pullback_subsingleton_H
      π M U hU hUaff s q hH
  change (F.obj (Scheme.Modules.orderedBaseCechComplex π M U)).ExactAt (q + 1)
  change (F.obj (Scheme.Modules.baseCechComplex π M U)).ExactAt (q + 1) at hbase
  exact hbase.of_retract
    (F.map (Scheme.Modules.orderedToBaseCechAlternating π M U))
    (F.map (Scheme.Modules.baseCechToOrdered π M U))
    (by
      rw [← F.map_comp,
        Scheme.Modules.orderedToBaseCechAlternating_comp_baseCechToOrdered,
        F.map_id])

end

end AlgebraicGeometry.Scheme.Modules
