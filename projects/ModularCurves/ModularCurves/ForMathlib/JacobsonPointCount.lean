/-
Copyright (c) 2026 The AINTLIB Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AINTLIB Authors
-/
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal

/-!
# Point counting on Jacobson schemes (BB-QF bridge, ForMathlib)

Two bridge facts for fibre-finiteness arguments over a field:

* `finite_of_jacobsonSpace_of_finite_closedPoints` — a Jacobson space with finitely many
  closed points is finite (the space *is* its closed points).
* `Scheme.exists_section_through_closedPoint` — on a scheme locally of finite type over
  `Spec k` with `k` algebraically closed, every closed point is hit by a `k`-section
  (Zariski's lemma / Nullstellensatz: the residue field at a closed point is a finite,
  hence trivial, extension of `k`).

Together: the space of such a scheme injects (via closed points) into its set of
`k`-sections, so finitely many `k`-sections force a finite space.
-/

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace ModularCurves

/-- A Jacobson space with finitely many closed points is finite. -/
theorem finite_of_jacobsonSpace_of_finite_closedPoints {X : Type*} [TopologicalSpace X]
    [JacobsonSpace X] (h : (closedPoints X).Finite) : Finite X := by
  have hclosed : IsClosed (closedPoints X) := by
    have hun : closedPoints X = ⋃ x ∈ h.toFinset, ({x} : Set X) := by
      ext x
      simp only [Set.mem_iUnion, Set.mem_singleton_iff, Set.Finite.mem_toFinset]
      exact ⟨fun hx => ⟨x, hx, rfl⟩, fun ⟨y, hy, hxy⟩ => hxy ▸ hy⟩
    rw [hun]
    exact Set.Finite.isClosed_biUnion (Set.finite_mem_finset h.toFinset)
      (fun x hx => (Set.Finite.mem_toFinset h).mp hx)
  have huniv : (Set.univ : Set X) = closedPoints X := by
    rw [← closure_closedPoints, hclosed.closure_eq]
  rw [← Set.finite_univ_iff, huniv]
  exact h

/-- **(Zariski's lemma, scheme-level)** On a scheme locally of finite type over an
algebraically closed field, every closed point is hit by a section. -/
theorem Scheme.exists_section_through_closedPoint {k : Type u} [Field k] [IsAlgClosed k]
    {F : Scheme.{u}} (f : F ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f]
    {z : F} (hz : IsClosed ({z} : Set F)) :
    ∃ g : Spec (CommRingCat.of k) ⟶ F, g ≫ f = 𝟙 _ ∧ z ∈ Set.range g.base := by
  -- the residue morphism at `z` is a closed immersion, hence of finite type
  haveI hci : IsClosedImmersion (F.fromSpecResidueField z) :=
    IsClosedImmersion.of_isPreimmersion _
      (by rw [Scheme.range_fromSpecResidueField]; exact hz)
  haveI : LocallyOfFiniteType (F.fromSpecResidueField z) := inferInstance
  haveI : LocallyOfFiniteType (F.fromSpecResidueField z ≫ f) := inferInstance
  -- the corresponding ring map `k ⟶ κ(z)` is of finite type
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (F.fromSpecResidueField z ≫ f)
  have hft : ψ.hom.FiniteType := by
    have h1 : LocallyOfFiniteType (Spec.map ψ) := by rw [hψ]; infer_instance
    rwa [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)] at h1
  -- Zariski's lemma: the extension is finite, hence algebraic, hence trivial
  letI : Algebra k (F.residueField z) := ψ.hom.toAlgebra
  haveI : Algebra.FiniteType k (F.residueField z) := hft
  haveI : Module.Finite k (F.residueField z) :=
    finite_of_finite_type_of_isJacobsonRing k (F.residueField z)
  haveI : Algebra.IsAlgebraic k (F.residueField z) := Algebra.IsAlgebraic.of_finite _ _
  have hbij : Function.Bijective (algebraMap k (F.residueField z)) :=
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  set e : k ≃+* F.residueField z := RingEquiv.ofBijective _ hbij with he
  refine ⟨Spec.map (CommRingCat.ofHom (e.symm : F.residueField z →+* k)) ≫
    F.fromSpecResidueField z, ?_, ?_⟩
  · rw [Category.assoc, ← hψ, ← Spec.map_comp]
    have hcomp : ψ ≫ CommRingCat.ofHom (e.symm : F.residueField z →+* k) = 𝟙 _ := by
      refine CommRingCat.hom_ext (RingHom.ext fun x => ?_)
      show e.symm (ψ.hom x) = x
      exact e.symm_apply_apply x
    exact (congrArg Spec.map hcomp).trans (Spec.map_id _)
  · obtain ⟨pt⟩ : Nonempty ↑(Spec (CommRingCat.of k)) := inferInstance
    refine ⟨pt, ?_⟩
    rw [Scheme.Hom.comp_apply]
    have h2 := Scheme.range_fromSpecResidueField (X := F) z
    have h3 : (F.fromSpecResidueField z).base
        ((Spec.map (CommRingCat.ofHom (e.symm : F.residueField z →+* k))).base pt) ∈
        ({z} : Set F) := h2 ▸ Set.mem_range_self _
    exact h3

/-- A scheme locally of finite type over an algebraically closed field with finitely many
sections has finite underlying space. -/
theorem Scheme.finite_of_finite_sections {k : Type u} [Field k] [IsAlgClosed k]
    {F : Scheme.{u}} (f : F ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f]
    (h : Finite {g : Spec (CommRingCat.of k) ⟶ F // g ≫ f = 𝟙 _}) : Finite F := by
  haveI : JacobsonSpace F := LocallyOfFiniteType.jacobsonSpace f
  refine finite_of_jacobsonSpace_of_finite_closedPoints ?_
  rw [← Set.finite_coe_iff]
  -- inject the closed points into the sections
  have hsec : ∀ z : closedPoints F,
      ∃ g : {g : Spec (CommRingCat.of k) ⟶ F // g ≫ f = 𝟙 _}, z.1 ∈ Set.range g.1.base :=
    fun z => by
      obtain ⟨g, hgf, hgz⟩ := Scheme.exists_section_through_closedPoint f z.2
      exact ⟨⟨g, hgf⟩, hgz⟩
  choose c hc using hsec
  haveI : Finite {g : Spec (CommRingCat.of k) ⟶ F // g ≫ f = 𝟙 _} := h
  refine Finite.of_injective c (fun z₁ z₂ hz => ?_)
  obtain ⟨p₁, hp₁⟩ := hc z₁
  obtain ⟨p₂, hp₂⟩ := hc z₂
  have hpp : p₁ = p₂ := Subsingleton.elim _ _
  refine Subtype.ext ?_
  rw [← hp₁, ← hp₂, hz, hpp]

/-- Sections of the second projection of a pullback along a point are morphisms into the
first factor with prescribed composite. -/
noncomputable def Scheme.pullbackSndSectionEquiv {X Z W : Scheme.{u}}
    (q : X ⟶ Z) (w : W ⟶ Z) :
    {g : W ⟶ Limits.pullback q w // g ≫ Limits.pullback.snd q w = 𝟙 _} ≃
    {h : W ⟶ X // h ≫ q = w} where
  toFun g := ⟨g.1 ≫ Limits.pullback.fst q w, by
    rw [Category.assoc, Limits.pullback.condition, ← Category.assoc, g.2,
      Category.id_comp]⟩
  invFun h := ⟨Limits.pullback.lift h.1 (𝟙 _) (by rw [h.2, Category.id_comp]), by
    rw [Limits.pullback.lift_snd]⟩
  left_inv g := by
    refine Subtype.ext ?_
    refine Limits.pullback.hom_ext ?_ ?_
    · rw [Limits.pullback.lift_fst]
    · rw [Limits.pullback.lift_snd, g.2]
  right_inv h := by
    refine Subtype.ext ?_
    show Limits.pullback.lift _ _ _ ≫ Limits.pullback.fst q w = h.1
    rw [Limits.pullback.lift_fst]

end ModularCurves
