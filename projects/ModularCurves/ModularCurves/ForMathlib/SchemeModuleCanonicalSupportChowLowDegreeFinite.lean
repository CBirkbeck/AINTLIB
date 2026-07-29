/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project
-/
import ModularCurves.EllipticCurve.RelativeProjectiveCoordinateTwistCechVanishing
import ModularCurves.ForMathlib.ProjectiveFactorizationCechHOne
import ModularCurves.ForMathlib.ProjectiveFactorizationFiniteSections
import ModularCurves.ForMathlib.SchemeModuleBaseCechPushforward
import ModularCurves.ForMathlib.SchemeModuleCanonicalSupportChowComparison
import ModularCurves.ForMathlib.SchemeModuleCechAffineRestriction
import ModularCurves.ForMathlib.SchemeModuleOrderedBaseCechHomologyRetract
import ModularCurves.ForMathlib.SchemeModuleOrderedBaseCechLowDegreeFinite
import ModularCurves.ForMathlib.SchemeModuleOrderedBaseCechPushforward
import ModularCurves.ForMathlib.SheafModuleCechTwoCoverHomology

/-!
# Low-degree Cech finiteness from support-adapted Chow charts

A support-adapted Chow chart supplies a relative projective cover and a
coordinate whose sufficiently positive twists have vanishing first
cohomology over a prescribed finite affine cover. Comparing the pullback
of that cover with an affine cover of the projective source transfers
finite generation in Cech degrees zero and one to the coordinate comodel.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

open TopCat TopCat.Sheaf

private theorem cechSingletonIntersection_eq
    {X : TopCat.{u}} {ι : Type u}
    (U : ι → TopologicalSpace.Opens X) (i : Fin 1 → ι) :
    (∏ᶜ fun k : Fin 1 => U (i k)) = U (i 0) := by
  apply le_antisymm
  · exact leOfHom (Limits.Pi.π (fun k : Fin 1 => U (i k)) 0)
  · exact leOfHom (Limits.Pi.lift fun k : Fin 1 => homOfLE (by
      rw [Subsingleton.elim k 0]))

private theorem finiteIntersectionOpen_insert
    {X : Scheme.{u}} {ι : Type u} [DecidableEq ι]
    (U : ι → X.Opens) (a : ι) (s : Finset ι) :
    X.finiteIntersectionOpen U (insert a s) =
      U a ⊓ X.finiteIntersectionOpen U s := by
  rw [Scheme.finiteIntersectionOpen, Scheme.finiteIntersectionOpen]
  apply le_antisymm
  · refine le_inf
      (iInf_le_of_le a (iInf_le_of_le (by simp) le_rfl)) ?_
    refine le_iInf fun j => le_iInf fun hj => ?_
    exact iInf_le_of_le j (iInf_le_of_le (by simp [hj]) le_rfl)
  · refine le_iInf fun j => le_iInf fun hj => ?_
    change j ∈ insert a s at hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact inf_le_left
    · exact inf_le_right.trans
        (iInf_le_of_le j (iInf_le_of_le hj le_rfl))

private theorem preimage_finiteIntersectionOpen
    {X Y : Scheme.{u}} {ι : Type u} [DecidableEq ι]
    (f : Y ⟶ X) (U : ι → X.Opens) (s : Finset ι) :
    Y.finiteIntersectionOpen (fun i => f ⁻¹ᵁ U i) s =
      f ⁻¹ᵁ X.finiteIntersectionOpen U s := by
  induction s using Finset.induction with
  | empty =>
      simp [Scheme.finiteIntersectionOpen]
  | @insert a s _ ih =>
      rw [finiteIntersectionOpen_insert _ _ _,
        finiteIntersectionOpen_insert _ _ _,
        Scheme.Hom.preimage_inf, ih]

private theorem cechIntersection_eq_finiteIntersectionOpen
    {X : Scheme.{u}} {ι : Type u} [Fintype ι] [DecidableEq ι]
    (U : ι → X.Opens) (q : ℕ) (i : Fin (q + 1) → ι) :
    (∏ᶜ fun k : Fin (q + 1) => U (i k)) =
      X.finiteIntersectionOpen U (Finset.univ.image i) := by
  rw [Scheme.finiteIntersectionOpen]
  apply le_antisymm
  · refine le_iInf fun j => le_iInf fun hj => ?_
    rw [Finset.mem_coe] at hj
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hj
    exact leOfHom (Limits.Pi.π (fun k : Fin (q + 1) => U (i k)) k)
  · exact leOfHom (Limits.Pi.lift fun k =>
      homOfLE (iInf_le_of_le (i k)
        (iInf_le_of_le (by simp) le_rfl)))

private theorem cechPreimageIntersection_eq_finiteIntersectionOpen
    {X Y : Scheme.{u}} {ι : Type u} [Fintype ι] [DecidableEq ι]
    (f : Y ⟶ X) (U : ι → X.Opens) (q : ℕ) (i : Fin (q + 1) → ι) :
    (∏ᶜ fun k : Fin (q + 1) => f ⁻¹ᵁ U (i k)) =
      f ⁻¹ᵁ X.finiteIntersectionOpen U (Finset.univ.image i) := by
  rw [cechIntersection_eq_finiteIntersectionOpen
    (fun j => f ⁻¹ᵁ U j) q i]
  exact preimage_finiteIntersectionOpen f U (Finset.univ.image i)

private theorem affineOpen_preimage_preimage
    {Y X : Scheme.{u}} [X.IsSeparated]
    (f : Y ⟶ X) (V : Y.Opens) (hV : IsAffineOpen V)
    (U : X.Opens) (hU : IsAffineOpen U) :
    IsAffineOpen (V.ι ⁻¹ᵁ (f ⁻¹ᵁ U)) := by
  letI : IsAffine V.toScheme := hV
  haveI : IsAffineHom (V.ι ≫ f) := by
    exact IsAffineHom.of_comp (V.ι ≫ f) (terminal.from X)
  change IsAffineOpen ((V.ι ≫ f) ⁻¹ᵁ U)
  exact hU.preimage (V.ι ≫ f)

private theorem affineOpen_preimage_affine_of_preimage
    {Y X : Scheme.{u}} [X.IsSeparated]
    (f : Y ⟶ X) (V : Y.Opens) (hV : IsAffineOpen V)
    (U : X.Opens) (hU : IsAffineOpen U) :
    IsAffineOpen ((f ⁻¹ᵁ U).ι ⁻¹ᵁ V) := by
  have hpre : IsAffineOpen (V.ι ⁻¹ᵁ (f ⁻¹ᵁ U)) :=
    affineOpen_preimage_preimage f V hV U hU
  have himage : IsAffineOpen (V ⊓ f ⁻¹ᵁ U) := by
    have h := V.ι.isAffineOpen_iff_of_isOpenImmersion.mpr hpre
    simpa [Scheme.Hom.image_preimage_eq_opensRange_inf,
      Scheme.Opens.opensRange_ι] using h
  apply (f ⁻¹ᵁ U).ι.isAffineOpen_iff_of_isOpenImmersion.mp
  rw [Scheme.Hom.image_preimage_eq_opensRange_inf,
    Scheme.Opens.opensRange_ι]
  simpa [inf_comm] using himage

namespace SupportAdaptedChowChart

/-- A sufficiently positive coordinate comodel on a support-adapted Chow
chart has finite ordered base-Cech homology in degrees zero and one. -/
theorem exists_coordinateComodel_orderedBaseCechLowDegreeFinite
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    {X : Scheme.{u}} [IsNoetherian X] [X.IsSeparated]
    {xπ : X ⟶ Spec (.of R)} {M : X.Modules}
    [M.IsQuasicoherent] [M.IsFiniteType]
    (C : SupportAdaptedChowChart xπ M)
    {ι : Type u} [Fintype ι] [LinearOrder ι]
    (U : ι → X.Opens) (hU : IsOpenCover U)
    (hUaff : ∀ i, IsAffineOpen (U i)) :
    ∃ n, OrderedBaseCechLowDegreeFinite xπ U
      (C.coordinateComodel n) := by
  classical
  let sourceπ := C.cover ≫ xπ
  letI : IsProper sourceπ := C.sourceProjective.isProper
  letI : C.source.IsSeparated := ⟨by
    rw [← terminal.comp_from sourceπ]
    infer_instance⟩
  letI : IsProper C.cover := C.relativeProjective.isProper
  letI : C.pulledBackModel.IsQuasicoherent :=
    isQuasicoherent_pullback C.cover M
  letI : C.pulledBackModel.IsFiniteType :=
    isFiniteType_pullback C.cover M
  choose bound hbound using fun i =>
    C.relativeProjective.coordinateTwist_eventually_subsingleton_H_of_pos
      C.pulledBackModel C.coordinate (U i) (hUaff i)
  let n := Finset.univ.sup bound
  have hboundn (i : ι) : bound i ≤ n :=
    Finset.le_sup (f := bound) (Finset.mem_univ i)
  let N := C.coordinateTwist n
  let E := C.coordinateComodel n
  letI : N.IsQuasicoherent :=
    C.coordinateTwist_isQuasicoherent n
  letI : N.IsFiniteType :=
    C.coordinateTwist_isFiniteType n
  letI : E.IsQuasicoherent :=
    C.coordinateComodel_isQuasicoherent n
  obtain ⟨κ, hκ, V, hV, hVaff, _⟩ :=
    sourceπ.exists_finite_affine_openCover_of_isProper
  letI : Finite κ := hκ
  let W : ι → C.source.Opens := fun i => C.cover ⁻¹ᵁ U i
  have hW : IsOpenCover W :=
    C.cover.iSup_preimage_eq_top hU
  let F := baseModuleTopSheaf sourceπ N
  have hrow :
      ((cechComplexFunctor W).obj
        (moduleCechTerm F V 0).obj).ExactAt 1 := by
    apply moduleCechTerm_cech_exactAt_one_of_factors
    intro i
    apply moduleCechFixedFactorNative_exactAt_one_of_app_exact
    let A := ∏ᶜ fun k : Fin 1 => V (i k)
    have hA : IsAffineOpen A :=
      IsAffineOpen.cechIntersection V hVaff 0 i
    apply moduleCechShortComplexApp_exact_of_restrict_subsingleton_H
      sourceπ N W hW A
    · intro j
      exact affineOpen_preimage_preimage C.cover A hA (U j) (hUaff j)
    · letI : IsAffine A.toScheme := hA
      exact affine_subsingleton_H (N.restrict A.ι) 0
  have hcol :
      ∀ i : Fin 1 → ι,
        (moduleCechShortComplexApp F V 0
          (∏ᶜ fun k : Fin 1 => W (i k))).Exact := by
    intro i
    rw [cechSingletonIntersection_eq W i]
    apply moduleCechShortComplexApp_exact_of_restrict_subsingleton_H
      sourceπ N V hV (W (i 0))
    · intro j
      exact affineOpen_preimage_affine_of_preimage
        C.cover (V j) (hVaff j) (U (i 0)) (hUaff (i 0))
    · exact hbound (i 0) n (hboundn (i 0)) 1 (by simp)
  letI : Module.Finite Γ(Spec (.of R), (⊤ : (Spec (.of R)).Opens))
      (((cechComplexFunctor V).obj F.obj).homology 1) :=
    C.sourceProjective.baseModuleCech_homology_one_module_finite_of_affine_openCover
      N V hV hVaff
  have hWOne :
      Module.Finite Γ(Spec (.of R), (⊤ : (Spec (.of R)).Opens))
        (((cechComplexFunctor W).obj F.obj).homology 1) :=
    moduleCechTwoCover_homology_one_module_finite
      F V W hV hW hrow hcol
  letI : Module.Finite Γ(Spec (.of R), (⊤ : (Spec (.of R)).Opens))
      ((baseCechComplex sourceπ N W).homology 1) := by
    exact hWOne
  let eOne := HomologicalComplex.homologyMapIso
    (baseCechComplexPushforwardIso C.cover xπ N U) 1
  letI : Module.Finite Γ(Spec (.of R), (⊤ : (Spec (.of R)).Opens))
      ((baseCechComplex xπ E U).homology 1) :=
    Module.Finite.equiv eOne.toLinearEquiv
  have hOne :
      Module.Finite Γ(Spec (.of R), (⊤ : (Spec (.of R)).Opens))
        ((orderedBaseCechComplex xπ E U).homology 1) :=
    orderedBaseCechComplex_homology_module_finite_of_baseCechComplex
      xπ E U 1
  letI : Module.Finite Γ(Spec (.of R), (⊤ : (Spec (.of R)).Opens))
      ((orderedBaseCechComplex sourceπ N W).homology 0) :=
    C.sourceProjective.orderedBaseCechComplex_homology_zero_module_finite
      N W hW
  let eZero := HomologicalComplex.homologyMapIso
    (orderedBaseCechComplexPushforwardIso C.cover xπ N U) 0
  have hZero :
      Module.Finite Γ(Spec (.of R), (⊤ : (Spec (.of R)).Opens))
        ((orderedBaseCechComplex xπ E U).homology 0) :=
    Module.Finite.equiv eZero.toLinearEquiv
  exact ⟨n, hZero, hOne⟩

end SupportAdaptedChowChart

end AlgebraicGeometry.Scheme.Modules
