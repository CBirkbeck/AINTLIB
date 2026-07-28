/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project
-/
import ModularCurves.EllipticCurve.ProjectiveSpaceTwistFinitePresentation

/-!
# Fixed-coordinate presentations by projective twists

The coordinate chart carrying a local section need not be the coordinate used
to model `O(1)`. Consequently, every finite-type quasicoherent module is a
quotient of finitely many negative powers of one fixed model of `O(-1)`.
-/

namespace MvPolynomial

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits HomogeneousIdeal
  MonoidalCategory

noncomputable section

universe u

variable {R : Type u} {σ : Type} [CommRing R]

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable local instance (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X

/-- A section on one coordinate chart extends after twisting by the positive
power attached to any fixed coordinate. -/
lemma exists_coordinateTwist_extension_fixed [Fintype σ]
    (M : (Proj (homogeneousSubmodule σ R)).Modules) [M.IsQuasicoherent]
    (i j : σ) (s : Γ(M, coordinateOpen (R := R) i)) :
    ∃ (n : ℕ)
        (q : Γ(M ⊗ coordinateHyperplanePoleSheafPower (R := R) j n, ⊤)),
      (M ⊗ coordinateHyperplanePoleSheafPower (R := R) j n).presheaf.map
          (homOfLE (le_top : coordinateOpen (R := R) i ≤
            (⊤ : (Proj (homogeneousSubmodule σ R)).Opens))).op q =
        coordinateChartTwistedSection (R := R) M i j n s := by
  classical
  obtain ⟨n, t, ht⟩ := exists_coordinateChartExtension_forall M i s
  obtain ⟨m, hm⟩ := exists_pow_coordinateChartDifference_eq_zero_forall
    M i n s t ht
  let d := n + m
  let c : ∀ k : σ, Γ(M, coordinateOpen (R := R) k) := fun k =>
    coordinateHyperplaneLocalEquation (R := R) k i ^ m • t k
  have hc : ∀ k l : σ,
      M.presheaf.map
          (homOfLE (coordinateOpenOverlap_le_left (R := R) k l)).op (c k) =
        (coordinateOpenTransitionUnit (R := R) k l :
            Γ(Proj (homogeneousSubmodule σ R),
              coordinateOpenOverlap (R := R) k l)) ^ d •
          M.presheaf.map
            (homOfLE (coordinateOpenOverlap_le_right (R := R) k l)).op
            (c l) := by
    intro k l
    exact coordinateChartExtensions_corrected_compatible
      (R := R) M k l i n m (t k) (t l) (hm k l)
  obtain ⟨q, hq⟩ := exists_global_coordinateChartTwistedSection M j d c hc
  refine ⟨d, q, ?_⟩
  calc
    (M ⊗ coordinateHyperplanePoleSheafPower (R := R) j d).presheaf.map
          (homOfLE (le_top : coordinateOpen (R := R) i ≤
            (⊤ : (Proj (homogeneousSubmodule σ R)).Opens))).op q =
        coordinateChartTwistedSection (R := R) M i j d (c i) := hq i
    _ = coordinateChartTwistedSection (R := R) M i j d s := by
      apply congrArg (coordinateChartTwistedSection (R := R) M i j d)
      dsimp only [c]
      rw [coordinateHyperplaneLocalEquation_self, one_pow, one_smul]
      exact eq_of_coordinateChartExtension_self M i n s (t i) (ht i)

/-- A local section is the image of the standard frame of a negative power
attached to any fixed coordinate. -/
theorem exists_coordinateNegativeTwistHom_fixed_frameSection_eq
    [Fintype σ]
    (M : (Proj (homogeneousSubmodule σ R)).Modules) [M.IsQuasicoherent]
    (i j : σ) (s : Γ(M, coordinateOpen (R := R) i)) :
    ∃ (n : ℕ)
        (f : coordinateHyperplaneIdealModulePower (R := R) j n ⟶ M),
      f.val.app (.op (coordinateOpen (R := R) i))
          (coordinateHyperplaneIdealModulePowerFrameSection
            (R := R) i j n) = s := by
  obtain ⟨n, q, hq⟩ := exists_coordinateTwist_extension_fixed M i j s
  let f := ModularCurves.sectionContractionHom
    (coordinateHyperplaneIdealModulePower (R := R) j n) M
    (coordinateHyperplanePoleSheafPower (R := R) j n)
    (coordinateHyperplanePowerPairing (R := R) j n) q
  refine ⟨n, f, ?_⟩
  have h :=
    ModularCurves.sectionContractionHom_apply_of_restrict_eq_tensorSection
      (coordinateHyperplaneIdealModulePower (R := R) j n) M
      (coordinateHyperplanePoleSheafPower (R := R) j n)
      (coordinateHyperplanePowerPairing (R := R) j n) q
      (coordinateOpen (R := R) i)
      (coordinateHyperplaneIdealModulePowerFrameSection
        (R := R) i j n) s
      (coordinateHyperplanePoleSheafPowerFrameSection
        (R := R) i j n) hq
  change f.val.app (.op (coordinateOpen (R := R) i))
      (coordinateHyperplaneIdealModulePowerFrameSection
        (R := R) i j n) = _ at h
  rw [coordinateHyperplanePowerPairing_frameSection, one_smul] at h
  exact h

private theorem moduleSectionsOfTop_eval_top_fixed
    {X : Scheme.{u}} (M : X.Modules) (s : M.sections) :
    ModularCurves.moduleSectionsOfTop M (s.eval (Opposite.op ⊤)) = s := by
  apply PresheafOfModules.sections_ext
  intro V
  change M.val.map (homOfLE (le_top : V.unop ≤ (⊤ : X.Opens))).op
      (s.val (Opposite.op ⊤)) = s.val V
  exact s.property _

private theorem sectionsMap_moduleSectionsOfTop_fixed
    {X : Scheme.{u}} {M N : X.Modules} (f : M ⟶ N)
    (x : Γ(M, (⊤ : X.Opens))) :
    SheafOfModules.sectionsMap f (ModularCurves.moduleSectionsOfTop M x) =
      ModularCurves.moduleSectionsOfTop N (f.val.app (Opposite.op ⊤) x) := by
  apply PresheafOfModules.sections_ext
  intro V
  let k := (homOfLE (le_top : V.unop ≤ (⊤ : X.Opens))).op
  change f.val.app V (M.val.map k x) =
    N.val.map k (f.val.app (Opposite.op ⊤) x)
  exact ConcreteCategory.congr_hom (f.val.naturality k) x

private theorem exists_finite_fixedCoordinateNegativeTwist_quotient
    [Fintype σ]
    (M : (Proj (homogeneousSubmodule σ R)).Modules)
    [M.IsQuasicoherent] [M.IsFiniteType] (j₀ : σ) :
    ∃ (I : Type u) (_ : Finite I) (n : I → ℕ)
        (f : (∐ fun i : I ↦
          coordinateHyperplaneIdealModulePower (R := R) j₀ (n i)) ⟶ M),
      Epi f := by
  classical
  let X := Proj (homogeneousSubmodule σ R)
  let U : σ → X.Opens := fun i ↦ coordinateOpen (R := R) i
  have hgenerators (i : σ) :
      ∃ G : ((Scheme.Modules.restrictFunctor (U i).ι).obj M).GeneratingSections,
        G.IsFiniteType := by
    exact
      Scheme.Modules.exists_generatingSections_restrict_of_isFiniteType_of_isAffineOpen
        M ⟨U i, coordinateOpen_isAffineOpen (R := R) i⟩
  choose G hG using hgenerators
  letI generatorsFiniteType (i : σ) : (G i).IsFiniteType := hG i
  letI generatorIndexFinite (i : σ) : Finite (G i).I := (hG i).finite
  let chartSection (i : σ) (a : (G i).I) : Γ(M, U i) :=
    (M.presheaf.mapIso (eqToIso (U i).ι_image_top).op).inv
      ((M.restrictAppIso (U i).ι ⊤).hom
        (((G i).s a).eval (Opposite.op ⊤)))
  have hnegative (i : σ) (a : (G i).I) :=
    exists_coordinateNegativeTwistHom_fixed_frameSection_eq
      M i j₀ (chartSection i a)
  choose n f hf using hnegative
  let I := Σ i : σ, (G i).I
  let ni : I → ℕ := fun i ↦ n i.1 i.2
  let L : I → X.Modules := fun i ↦
    coordinateHyperplaneIdealModulePower (R := R) j₀ (ni i)
  let p : ∀ i : I, L i ⟶ M := fun i ↦ f i.1 i.2
  let q : (∐ L) ⟶ M := Limits.Sigma.desc p
  let restrictedSummandFrame (i : σ) (a : (G i).I) :
      Γ((Scheme.Modules.restrictFunctor (U i).ι).obj (L ⟨i, a⟩), ⊤) :=
    (((L ⟨i, a⟩).restrictAppIso (U i).ι ⊤).inv)
      (((L ⟨i, a⟩).presheaf.mapIso
        (eqToIso (U i).ι_image_top).op).hom
          (coordinateHyperplaneIdealModulePowerFrameSection
            (R := R) i j₀ (n i a)))
  let restrictedFrame (i : σ) (a : (G i).I) :
      Γ((Scheme.Modules.restrictFunctor (U i).ι).obj (∐ L), ⊤) :=
    ((Scheme.Modules.restrictFunctor (U i).ι).map
      (Limits.Sigma.ι L ⟨i, a⟩)).val.app (Opposite.op ⊤)
        (restrictedSummandFrame i a)
  have hrestrictedFrame (i : σ) (a : (G i).I) :
      ((Scheme.Modules.restrictFunctor (U i).ι).map q).val.app
          (Opposite.op ⊤) (restrictedFrame i a) =
        ((G i).s a).eval (Opposite.op ⊤) := by
    have hmor :
        (Scheme.Modules.restrictFunctor (U i).ι).map
              (Limits.Sigma.ι L ⟨i, a⟩) ≫
            (Scheme.Modules.restrictFunctor (U i).ι).map q =
          (Scheme.Modules.restrictFunctor (U i).ι).map (f i a) := by
      rw [← (Scheme.Modules.restrictFunctor (U i).ι).map_comp]
      change (Scheme.Modules.restrictFunctor (U i).ι).map
        (Limits.Sigma.ι L ⟨i, a⟩ ≫ Limits.Sigma.desc p) = _
      rw [Limits.Sigma.ι_desc]
    have happ := congrArg
      (fun r ↦ r.val.app (Opposite.op ⊤) (restrictedSummandFrame i a)) hmor
    change ((Scheme.Modules.restrictFunctor (U i).ι).map q).val.app
        (Opposite.op ⊤) (restrictedFrame i a) =
      ((Scheme.Modules.restrictFunctor (U i).ι).map (f i a)).val.app
        (Opposite.op ⊤) (restrictedSummandFrame i a) at happ
    rw [happ]
    change (f i a).val.app
        ((U i).ι.opensFunctor.op.obj (Opposite.op ⊤))
          (restrictedSummandFrame i a) = _
    change (f i a).val.app
      (Opposite.op ((U i).ι ''ᵁ (⊤ : (U i).toScheme.Opens)))
        (restrictedSummandFrame i a) = _
    change (f i a).val.app
        (Opposite.op ((U i).ι ''ᵁ (⊤ : (U i).toScheme.Opens)))
          (((coordinateHyperplaneIdealModulePower
              (R := R) j₀ (n i a)).presheaf.mapIso
            (eqToIso (U i).ι_image_top).op).hom
              (coordinateHyperplaneIdealModulePowerFrameSection
                (R := R) i j₀ (n i a))) =
      ((M.restrictAppIso (U i).ι ⊤).hom
        (((G i).s a).eval (Opposite.op ⊤)))
    have hnat := PresheafOfModules.naturality_apply (f i a).val
      (eqToIso (U i).ι_image_top).op.hom
      (coordinateHyperplaneIdealModulePowerFrameSection
        (R := R) i j₀ (n i a))
    change (f i a).val.app
        (Opposite.op ((U i).ι ''ᵁ (⊤ : (U i).toScheme.Opens)))
          (((coordinateHyperplaneIdealModulePower
              (R := R) j₀ (n i a)).presheaf.mapIso
            (eqToIso (U i).ι_image_top).op).hom
              (coordinateHyperplaneIdealModulePowerFrameSection
                (R := R) i j₀ (n i a))) =
      (M.presheaf.mapIso (eqToIso (U i).ι_image_top).op).hom
        ((f i a).val.app (Opposite.op (U i))
          (coordinateHyperplaneIdealModulePowerFrameSection
            (R := R) i j₀ (n i a))) at hnat
    rw [hnat, hf i a]
    simp only [chartSection, Iso.inv_hom_id_apply]
    rfl
  let localFrame (i : σ) (a : (G i).I) :
      ((Scheme.Modules.restrictFunctor (U i).ι).obj (∐ L)).sections :=
    ModularCurves.moduleSectionsOfTop _ (restrictedFrame i a)
  let lift (i : σ) :
      SheafOfModules.free (G i).I ⟶
        (Scheme.Modules.restrictFunctor (U i).ι).obj (∐ L) :=
    (((Scheme.Modules.restrictFunctor (U i).ι).obj (∐ L)).freeHomEquiv).symm
      (localFrame i)
  have hlift (i : σ) :
      lift i ≫ (Scheme.Modules.restrictFunctor (U i).ι).map q = (G i).π := by
    have hlocal :
        (fun a ↦ SheafOfModules.sectionsMap
          ((Scheme.Modules.restrictFunctor (U i).ι).map q) (localFrame i a)) =
          (G i).s := by
      funext a
      change SheafOfModules.sectionsMap
          ((Scheme.Modules.restrictFunctor (U i).ι).map q)
            (ModularCurves.moduleSectionsOfTop _ (restrictedFrame i a)) =
        (G i).s a
      rw [sectionsMap_moduleSectionsOfTop_fixed]
      rw [hrestrictedFrame]
      exact moduleSectionsOfTop_eval_top_fixed _ _
    change
      (((Scheme.Modules.restrictFunctor (U i).ι).obj (∐ L)).freeHomEquiv).symm
          (localFrame i) ≫
        (Scheme.Modules.restrictFunctor (U i).ι).map q =
      (((Scheme.Modules.restrictFunctor (U i).ι).obj M).freeHomEquiv).symm
        ((G i).s)
    calc
      _ = (((Scheme.Modules.restrictFunctor (U i).ι).obj M).freeHomEquiv).symm
          (fun a ↦ SheafOfModules.sectionsMap
            ((Scheme.Modules.restrictFunctor (U i).ι).map q) (localFrame i a)) :=
        SheafOfModules.freeHomEquiv_symm_comp (localFrame i)
          ((Scheme.Modules.restrictFunctor (U i).ι).map q)
      _ = _ := congrArg
        (((Scheme.Modules.restrictFunctor (U i).ι).obj M).freeHomEquiv).symm hlocal
  have hrestrictedEpi (i : σ) :
      Epi ((Scheme.Modules.restrictFunctor (U i).ι).map q) := by
    constructor
    intro Z g h hgh
    apply (G i).epi.left_cancellation g h
    have hpre := congrArg
      (fun k : (Scheme.Modules.restrictFunctor (U i).ι).obj (∐ L) ⟶ Z ↦
        lift i ≫ k) hgh
    have hcomp :
        (lift i ≫ (Scheme.Modules.restrictFunctor (U i).ι).map q) ≫ g =
          (lift i ≫ (Scheme.Modules.restrictFunctor (U i).ι).map q) ≫ h := by
      exact (Category.assoc _ _ _).trans
        (hpre.trans (Category.assoc _ _ _).symm)
    have hleft := congrArg (fun k ↦ k ≫ g) (hlift i)
    have hright := congrArg (fun k ↦ k ≫ h) (hlift i)
    exact hleft.symm.trans (hcomp.trans hright)
  have hU : ⨆ i, U i = ⊤ := by
    simpa only [U] using iSup_coordinateOpen_eq_top (R := R) (σ := σ)
  have hq : Epi q :=
    Scheme.Modules.epi_of_restrictFunctor_map_epi_of_iSup_eq_top
      U hU q hrestrictedEpi
  letI : Finite I := inferInstance
  exact ⟨I, inferInstance, ni, q, hq⟩

/-- Every finite-type quasicoherent module is a quotient of finitely many
negative twists attached to one fixed coordinate. -/
theorem exists_fin_fixedCoordinateNegativeTwist_quotient [Fintype σ]
    (M : (Proj (homogeneousSubmodule σ R)).Modules)
    [M.IsQuasicoherent] [M.IsFiniteType] (j : σ) :
    ∃ (r : ℕ) (n : Fin r → ℕ)
        (f : (∐ fun i : Fin r ↦
          coordinateHyperplaneIdealModulePower (R := R) j (n i)) ⟶ M),
      Epi f := by
  classical
  obtain ⟨I, hI, n, f, hf⟩ :=
    exists_finite_fixedCoordinateNegativeTwist_quotient M j
  letI : Finite I := hI
  let e : Fin (Nat.card I) ≃ I := (Finite.equivFin I).symm
  let L : I → (Proj (homogeneousSubmodule σ R)).Modules := fun i ↦
    coordinateHyperplaneIdealModulePower (R := R) j (n i)
  let g : (∐ fun k : Fin (Nat.card I) ↦ L (e k)) ⟶ M :=
    (Sigma.reindex e L).hom ≫ f
  refine ⟨Nat.card I, fun k ↦ n (e k), g, ?_⟩
  dsimp only [g]
  infer_instance

end

end MvPolynomial
