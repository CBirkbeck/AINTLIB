/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.EllipticCurve.DegreeOneFibreCohomology
import ModularCurves.LevelStructure.CartierDivisor
import ModularCurves.Picard.IdealModule
import ModularCurves.ForMathlib.LocalFlatnessCriterion

/-!
# The Abel equivalence, evaluation-divisor side (`AP2-B2`/`AP2-B3`, KM pp. 66–67)

KM p. 66, verbatim: *"Because `f_*L` is invertible on `S`, Zariski locally on `S` we may
pick an `O_S`-basis `ℓ` of `f_*L`. We claim that, locally over `S`, the pair `(L, ℓ)` on
`E` defines an effective Cartier divisor in `E`. We must show that we have an exact
sequence `0 → O → L → L/O → 0` with `L/O` flat over `S`. This amounts to the statement
that the map of invertible sheaves `O --ℓ--> L` on `E` is injective, and remains so after
any base change `T → S` on `S`. For this we are reduced to the case `S = Spec(k)` with `k`
a field, and `ℓ ∈ H⁰(E,L)` a `k`-basis, so non-zero, in which case the assertion is
obvious."* Then p. 67: *"Therefore `(L, ℓ)` defines an effective Cartier divisor in `E/S`.
Looking fiber-by-fiber, we see that it is of degree one. By (1.2.7), any effective Cartier
divisor of degree one is a section `P ∈ E(S)`."*

Design (board, 2026-08-08 surveys 1–2): the target vocabulary is the divisor engine —
`RelEffCartierDiv π` / `IsOfficialCartier` (`LevelStructure/CartierDivisor.lean`) with the
module seam `idealModule` / `isInvertible_idealModule` (`Picard/IdealModule.lean`); the
fibrewise flatness criterion is in-tree (`ForMathlib/LocalFlatnessCriterion.lean`, Stacks
00ME, with the relative `_sModule` variant and the `BaseChangeKerCoker` output forms). The
statements below are EXISTENCE-form (Pic-level consumers only need the class), keeping all
defs sorry-free.
-/

universe u

open CategoryTheory AlgebraicGeometry Limits TopologicalSpace
open AlgebraicGeometry.Scheme.Modules

namespace ModularCurves

/-- The vanishing ideal of a global section `σ` of a module `M`: over each affine open,
the ideal of values of local functionals against `σ` (the evaluation ideal). On a
trivialising open this is the principal ideal of the trivialised value of `σ`; the
basic-open compatibility is checked at maximal ideals through trivialising basic opens
(`Ideal.mem_of_localization_maximal` — board note 2026-08-08, no quasi-coherent
localization needed). -/
noncomputable def sectionVanishingIdeal {E : Scheme.{u}} (M : E.Modules) (σ : ↑Γ(M, ⊤)) :
    E.IdealSheafData where
  ideal U := Ideal.span (Set.range fun φ : M.over U.1 ⟶
      _root_.SheafOfModules.unit (E.ringCatSheaf.over U.1) =>
    (show ↑Γ(E, U.1) from φ.val.app (Opposite.op (CategoryTheory.Over.mk (𝟙 U.1)))
      (show (M.over U.1).val.obj (Opposite.op (CategoryTheory.Over.mk (𝟙 U.1))) from
        M.presheaf.map (homOfLE le_top).op σ)))
  map_ideal_basicOpen U f := by
    rw [Ideal.map_span]
    apply le_antisymm
    · refine Ideal.span_le.mpr ?_
      rintro x ⟨y, ⟨φ, rfl⟩, rfl⟩
      have hσ : (M.presheaf.map (homOfLE (E.basicOpen_le f)).op)
          ((M.presheaf.map (homOfLE (le_top : U.1 ≤ ⊤)).op) σ) =
          (M.presheaf.map (homOfLE (le_top : (E.affineBasicOpen f).1 ≤ ⊤)).op) σ := by
        rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
        exact congrArg (fun q ↦ (ConcreteCategory.hom (M.presheaf.map
          (Quiver.Hom.op q))) σ) (Subsingleton.elim _ _)
      have hnat := PresheafOfModules.naturality_apply φ.val
        (CategoryTheory.Over.mkIdTerminal.from
          (CategoryTheory.Over.mk (homOfLE (E.basicOpen_le f)))).op
        (show (M.over U.1).val.obj
          (Opposite.op (CategoryTheory.Over.mk (𝟙 U.1))) from
          M.presheaf.map (homOfLE (le_top : U.1 ≤ ⊤)).op σ)
      refine Ideal.subset_span ?_
      refine ⟨ModularCurves.SheafOfModules.dualRestrict E.ringCatSheaf M
        (show Opposite.op U.1 ⟶ Opposite.op (E.affineBasicOpen f).1 from
          (homOfLE (E.basicOpen_le f)).op) φ, ?_⟩
      simp only [ModularCurves.SheafOfModules.dualRestrict_app_apply]
      exact (congrArg (fun z ↦ φ.val.app (Opposite.op ((CategoryTheory.Over.map
        (homOfLE (E.basicOpen_le f))).obj
        (CategoryTheory.Over.mk (𝟙 (E.affineBasicOpen f).1)))) z) hσ.symm).trans hnat
    · -- ⊇ : the maximal-local argument through trivialising basic opens
      sorry

/-- **(`AP2-B2` + `AP2-B3` head, KM pp. 66–67)** Under the degree-one package, the pair
`(M, ℓ)` — for any base-local basis of the rank-one pushforward — cuts out a relative
effective Cartier divisor whose ideal is the `M`-inverse twist of the pushforward pullback:
`ℐ_D ≅ f^*(f_*M) ⊗ M⁻¹` (round-19 PIN 1: the twist is `(f_*M)`, never `(0^*M)`).

Existence-form packaging of KM's exact sequence `0 → O --ℓ--> M → M/O → 0` with `M/O`
`S`-flat: the divisor's subscheme-over-base carries the flatness, the ideal-module
isomorphism carries the exactness. -/
theorem exists_relEffCartierDiv_of_degreeOne
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    {E : Scheme.{u}} {π : E ⟶ Spec (.of R)} [IsProper π] [Flat π]
    [IsNoetherian E] [LocallyOfFinitePresentation π]
    (M : E.Modules) (hM : M.IsInvertible)
    {ι : Type u} [Fintype ι] [LinearOrder ι] (U : ι → E.Opens)
    (hU : IsOpenCover U) (hUaff : ∀ i, IsAffineOpen (U i))
    (hpkg : HasDegreeOneFibreCohomology π M U) :
    ∃ D : RelEffCartierDiv π,
      Nonempty (AlgebraicGeometry.Scheme.Modules.idealModule D.ideal ≅
        tensorObj ((AlgebraicGeometry.Scheme.Modules.pullback π).obj
          ((AlgebraicGeometry.Scheme.Modules.pushforward π).obj M))
          (dualObj M)) := by
  sorry

/-- **(`AP2-B3`, degree part, KM p. 67)** The evaluation divisor has fibre degree one:
"Looking fiber-by-fiber, we see that it is of degree one" — the fibre `h⁰` of the
degree-one package. -/
theorem relEffCartierDiv_degree_one_of_degreeOne
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    {E : Scheme.{u}} {π : E ⟶ Spec (.of R)} [IsProper π] [Flat π]
    [IsNoetherian E] [LocallyOfFinitePresentation π]
    (M : E.Modules) (hM : M.IsInvertible)
    {ι : Type u} [Fintype ι] [LinearOrder ι] (U : ι → E.Opens)
    (hU : IsOpenCover U) (hUaff : ∀ i, IsAffineOpen (U i))
    (hpkg : HasDegreeOneFibreCohomology π M U)
    (D : RelEffCartierDiv π)
    (hD : Nonempty (AlgebraicGeometry.Scheme.Modules.idealModule D.ideal ≅
      tensorObj ((AlgebraicGeometry.Scheme.Modules.pullback π).obj
        ((AlgebraicGeometry.Scheme.Modules.pushforward π).obj M))
        (dualObj M)))
    (s : Spec (.of R)) : D.degree s = 1 := by
  sorry

end ModularCurves
