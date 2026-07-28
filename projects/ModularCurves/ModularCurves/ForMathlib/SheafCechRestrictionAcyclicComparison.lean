import Mathlib.Algebra.Homology.HomologySequenceLemmas
import ModularCurves.ForMathlib.SheafCechFlasqueExact
import ModularCurves.ForMathlib.SheafCechInjectiveCokernel
import ModularCurves.ForMathlib.SheafCechInjectiveComparison

/-!
# Cech comparison from acyclic finite intersections

This file proves the Leray-style comparison needed for affine Cech covers.
Starting from one injective presentation, local `H¹` vanishing gives a short
exact sequence of native Cech complexes. Dimension shifting transfers both
the global cohomology hypothesis and acyclicity on every finite intersection
to the cokernel.
-/

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace TopCat.Sheaf

noncomputable section

variable {X : TopCat.{u}}
variable {ι : Type u} (U : ι → Opens X)

private theorem cechSingletonIntersection_eq (i : Fin 1 → ι) :
    (∏ᶜ fun k : Fin 1 ↦ U (i k)) = U (i 0) := by
  apply le_antisymm
  · exact leOfHom (Limits.Pi.π (fun k : Fin 1 ↦ U (i k)) 0)
  · exact leOfHom (Limits.Pi.lift fun k : Fin 1 ↦ homOfLE (by
      rw [Subsingleton.elim k 0]))

private theorem injectiveResolutionCokernel_subsingleton_H
    (F : Sheaf AddCommGrpCat.{u} X) (q : ℕ)
    (hF : Subsingleton (CategoryTheory.Sheaf.H F ((q + 1) + 1))) :
    Subsingleton (CategoryTheory.Sheaf.H
      (cokernel ((injectiveResolution (toSiteSheaf F)).ι.f 0)) (q + 1)) := by
  let I := injectiveResolution (toSiteSheaf F)
  let S := injectiveResolutionCokernelShortComplex F
  have hS := injectiveResolutionCokernelShortComplex_shortExact F
  letI : IsFlasque (I.cocomplex.X 0) :=
    @IsFlasque.of_injective X (I.cocomplex.X 0) (I.injective 0)
  have hmiddle : Subsingleton (CategoryTheory.Sheaf.H S.X₂ (q + 1)) := by
    change Subsingleton (CategoryTheory.Sheaf.H (I.cocomplex.X 0) (q + 1))
    exact IsFlasque.subsingleton_H q
  have hleft : Subsingleton (CategoryTheory.Sheaf.H S.X₁ ((q + 1) + 1)) := by
    change Subsingleton (CategoryTheory.Sheaf.H F ((q + 1) + 1))
    exact hF
  exact subsingleton_H_X₃_of_shortExact hS (q + 1) hmiddle hleft

private theorem subsingleton_H_X₁_succ_of_shortExact
    {S : ShortComplex (Sheaf AddCommGrpCat.{u} X)} (hS : S.ShortExact)
    (q : ℕ) (hright : Subsingleton (CategoryTheory.Sheaf.H S.X₃ q))
    (hmiddle : Subsingleton (CategoryTheory.Sheaf.H S.X₂ (q + 1))) :
    Subsingleton (CategoryTheory.Sheaf.H S.X₁ (q + 1)) := by
  letI : AddCommGroup (CategoryTheory.Sheaf.H S.X₁ (q + 1)) :=
    CategoryTheory.Abelian.Ext.instAddCommGroup
  letI : Subsingleton (CategoryTheory.Sheaf.H S.X₃ q) := hright
  letI : Subsingleton (CategoryTheory.Sheaf.H S.X₂ (q + 1)) := hmiddle
  refine subsingleton_of_forall_eq 0 fun x ↦ ?_
  obtain ⟨x₃, hx₃⟩ := CategoryTheory.Sheaf.H.longSequence_exact₁
    hS q (q + 1) rfl x (Subsingleton.elim _ _)
  rw [Subsingleton.elim x₃ 0, map_zero] at hx₃
  exact hx₃.symm

private theorem injectiveResolution_subsingleton_H_of_cokernel
    (F : Sheaf AddCommGrpCat.{u} X) (q : ℕ)
    (hQ : Subsingleton (CategoryTheory.Sheaf.H
      (cokernel ((injectiveResolution (toSiteSheaf F)).ι.f 0)) (q + 1))) :
    Subsingleton (CategoryTheory.Sheaf.H F ((q + 1) + 1)) := by
  let I := injectiveResolution (toSiteSheaf F)
  let S := injectiveResolutionCokernelShortComplex F
  have hS := injectiveResolutionCokernelShortComplex_shortExact F
  letI : IsFlasque (I.cocomplex.X 0) :=
    @IsFlasque.of_injective X (I.cocomplex.X 0) (I.injective 0)
  have hmiddle :
      Subsingleton (CategoryTheory.Sheaf.H S.X₂ ((q + 1) + 1)) := by
    change Subsingleton (CategoryTheory.Sheaf.H (I.cocomplex.X 0) ((q + 1) + 1))
    exact IsFlasque.subsingleton_H (q + 1)
  have hright : Subsingleton (CategoryTheory.Sheaf.H S.X₃ (q + 1)) := by
    change Subsingleton (CategoryTheory.Sheaf.H
      (cokernel ((injectiveResolution (toSiteSheaf F)).ι.f 0)) (q + 1))
    exact hQ
  exact subsingleton_H_X₁_succ_of_shortExact hS (q + 1) hright hmiddle

private theorem injectiveResolutionCokernel_restrict_subsingleton_H
    (F : Sheaf AddCommGrpCat.{u} X) (V : Opens X)
    (hF : ∀ q : ℕ, Subsingleton (CategoryTheory.Sheaf.H
      ((restrict AddCommGrpCat V.isOpenEmbedding).obj F) (q + 1)))
    (q : ℕ) :
    Subsingleton (CategoryTheory.Sheaf.H
      ((restrict AddCommGrpCat V.isOpenEmbedding).obj
        (cokernel ((injectiveResolution (toSiteSheaf F)).ι.f 0))) (q + 1)) := by
  let I := injectiveResolution (toSiteSheaf F)
  let S := injectiveResolutionCokernelShortComplex F
  have hS := injectiveResolutionCokernelShortComplex_shortExact F
  let R := restrict AddCommGrpCat.{u} V.isOpenEmbedding
  haveI : R.Additive := restrict_additive V.isOpenEmbedding
  have hR : R.PreservesZeroMorphisms :=
    { map_zero := fun _ _ ↦ R.mapAddHom.map_zero }
  have hRlim : PreservesFiniteLimits R := by
    dsimp [R]
    exact restrict_preservesFiniteLimits V.isOpenEmbedding
  have hRcolim : PreservesFiniteColimits R := by
    dsimp [R]
    infer_instance
  let SV := @ShortComplex.map _ _ _ _ _ _ S R hR
  have hSV : SV.ShortExact := by
    exact @ShortComplex.ShortExact.map_of_exact _ _ _ _ _ _ S hS R hR
      hRlim hRcolim
  letI : IsFlasque (I.cocomplex.X 0) :=
    @IsFlasque.of_injective X (I.cocomplex.X 0) (I.injective 0)
  letI : IsFlasque (R.obj (I.cocomplex.X 0)) :=
    IsFlasque.of_restrict AddCommGrpCat (I.cocomplex.X 0) V.isOpenEmbedding
  have hmiddle : Subsingleton (CategoryTheory.Sheaf.H SV.X₂ (q + 1)) := by
    change Subsingleton (CategoryTheory.Sheaf.H
      (R.obj (I.cocomplex.X 0)) (q + 1))
    exact IsFlasque.subsingleton_H q
  have hleft : Subsingleton (CategoryTheory.Sheaf.H SV.X₁ ((q + 1) + 1)) := by
    change Subsingleton (CategoryTheory.Sheaf.H (R.obj F) ((q + 1) + 1))
    exact hF (q + 1)
  have hQ := subsingleton_H_X₃_of_shortExact hSV (q + 1) hmiddle hleft
  change Subsingleton (CategoryTheory.Sheaf.H
    (R.obj (cokernel (I.ι.f 0))) (q + 1)) at hQ
  exact hQ

/-- If every positive cohomology group vanishes after restriction to every
finite intersection in a finite open cover, then the native Cech complex
computes the corresponding global cohomology vanishing in every positive
degree. -/
theorem cechComplex_exactAt_succ_of_subsingleton_restrict_H [Finite ι]
    (F : Sheaf AddCommGrpCat.{u} X) (hU : ⨆ i, U i = ⊤)
    (hinter : ∀ (p : ℕ) (i : Fin (p + 1) → ι) (q : ℕ),
      Subsingleton (CategoryTheory.Sheaf.H
        ((restrict AddCommGrpCat
          (∏ᶜ fun k : Fin (p + 1) ↦ U (i k)).isOpenEmbedding).obj F) (q + 1)))
    (n : ℕ) (hF : Subsingleton (CategoryTheory.Sheaf.H F (n + 1))) :
    ((cechComplexFunctor U).obj F.obj).ExactAt (n + 1) := by
  induction n generalizing F with
  | zero =>
      letI : Subsingleton (CategoryTheory.Sheaf.H F 1) := by simpa using hF
      letI : AddCommGroup (CategoryTheory.Sheaf.H F 1) :=
        CategoryTheory.Abelian.Ext.instAddCommGroup
      rw [HomologicalComplex.exactAt_iff_isZero_homology]
      have hzero : IsZero (AddCommGrpCat.of (CategoryTheory.Sheaf.H F 1)) :=
        AddCommGrpCat.isZero_of_subsingleton _
      have hcover (i : ι) : Subsingleton (CategoryTheory.Sheaf.H
          ((restrict AddCommGrpCat (U i).isOpenEmbedding).obj F) 1) := by
        let j : Fin 1 → ι := fun _ ↦ i
        have h := hinter 0 j 0
        rw [cechSingletonIntersection_eq U j] at h
        exact h
      exact IsZero.of_iso hzero
        (cechHomologyOneIso_of_subsingleton_H U F hU hcover)
  | succ n ih =>
      let I := injectiveResolution (toSiteSheaf F)
      let Q := cokernel (I.ι.f 0)
      have hQ : Subsingleton (CategoryTheory.Sheaf.H Q (n + 1)) := by
        apply injectiveResolutionCokernel_subsingleton_H F n
        simpa only [Nat.succ_eq_add_one] using hF
      have hQinter (p : ℕ) (i : Fin (p + 1) → ι) (q : ℕ) :
          Subsingleton (CategoryTheory.Sheaf.H
            ((restrict AddCommGrpCat
              (∏ᶜ fun k : Fin (p + 1) ↦ U (i k)).isOpenEmbedding).obj Q) (q + 1)) :=
        injectiveResolutionCokernel_restrict_subsingleton_H F
          (∏ᶜ fun k : Fin (p + 1) ↦ U (i k)) (hinter p i) q
      have hQexact := ih Q hQinter hQ
      letI : IsFlasque (I.cocomplex.X 0) :=
        @IsFlasque.of_injective X (I.cocomplex.X 0) (I.injective 0)
      have hIexact := cechComplex_exactAt_succ_of_isFlasque U
        (I.cocomplex.X 0) hU (n + 1)
      let S := cechInjectiveResolutionCokernelShortComplex U F
      have hS : S.ShortExact :=
        cechInjectiveResolutionCokernelShortComplex_shortExact U F
          (fun p i ↦ hinter p i 0)
      rw [HomologicalComplex.exactAt_iff_isZero_homology]
      have hQzero := hQexact.isZero_homology
      have hIzero := hIexact.isZero_homology
      change IsZero (S.X₁.homology ((n + 1) + 1))
      change IsZero (S.X₃.homology (n + 1)) at hQzero
      change IsZero (S.X₂.homology ((n + 1) + 1)) at hIzero
      exact (hS.homology_exact₁ (n + 1) ((n + 1) + 1) (by simp)).isZero_X₂
        (hQzero.eq_of_src _ _) (hIzero.eq_of_tgt _ _)

/-- For a finite cover acyclic on every finite intersection, exactness of
the native Cech complex is equivalent to vanishing of the corresponding
positive sheaf cohomology group. -/
theorem cechComplex_exactAt_succ_iff_subsingleton_H_of_subsingleton_restrict_H
    [Finite ι]
    (F : Sheaf AddCommGrpCat.{u} X) (hU : ⨆ i, U i = ⊤)
    (hinter : ∀ (p : ℕ) (i : Fin (p + 1) → ι) (q : ℕ),
      Subsingleton (CategoryTheory.Sheaf.H
        ((restrict AddCommGrpCat
          (∏ᶜ fun k : Fin (p + 1) ↦ U (i k)).isOpenEmbedding).obj F) (q + 1)))
    (n : ℕ) :
    ((cechComplexFunctor U).obj F.obj).ExactAt (n + 1) ↔
      Subsingleton (CategoryTheory.Sheaf.H F (n + 1)) := by
  constructor
  · intro hF
    induction n generalizing F with
    | zero =>
        letI : AddCommGroup (CategoryTheory.Sheaf.H F 1) :=
          CategoryTheory.Abelian.Ext.instAddCommGroup
        rw [HomologicalComplex.exactAt_iff_isZero_homology] at hF
        have hcover (i : ι) : Subsingleton (CategoryTheory.Sheaf.H
            ((restrict AddCommGrpCat (U i).isOpenEmbedding).obj F) 1) := by
          let j : Fin 1 → ι := fun _ ↦ i
          have h := hinter 0 j 0
          rw [cechSingletonIntersection_eq U j] at h
          exact h
        have hzero : IsZero
            ((CategoryTheory.Sheaf.functorH
              (Opens.grothendieckTopology X) 1).obj F) :=
          IsZero.of_iso hF
            (cechHomologyOneIso_of_subsingleton_H U F hU hcover).symm
        exact AddCommGrpCat.subsingleton_of_isZero hzero
    | succ n ih =>
        let I := injectiveResolution (toSiteSheaf F)
        let Q := cokernel (I.ι.f 0)
        have hQinter (p : ℕ) (i : Fin (p + 1) → ι) (q : ℕ) :
            Subsingleton (CategoryTheory.Sheaf.H
              ((restrict AddCommGrpCat
                (∏ᶜ fun k : Fin (p + 1) ↦ U (i k)).isOpenEmbedding).obj Q) (q + 1)) :=
          injectiveResolutionCokernel_restrict_subsingleton_H F
            (∏ᶜ fun k : Fin (p + 1) ↦ U (i k)) (hinter p i) q
        letI : IsFlasque (I.cocomplex.X 0) :=
          @IsFlasque.of_injective X (I.cocomplex.X 0) (I.injective 0)
        have hIexact := cechComplex_exactAt_succ_of_isFlasque U
          (I.cocomplex.X 0) hU n
        let S := cechInjectiveResolutionCokernelShortComplex U F
        have hS : S.ShortExact :=
          cechInjectiveResolutionCokernelShortComplex_shortExact U F
            (fun p i ↦ hinter p i 0)
        have hQexact :
            ((cechComplexFunctor U).obj Q.obj).ExactAt (n + 1) := by
          rw [HomologicalComplex.exactAt_iff_isZero_homology]
          have hFzero := hF.isZero_homology
          have hIzero := hIexact.isZero_homology
          change IsZero (S.X₃.homology (n + 1))
          change IsZero (S.X₂.homology (n + 1)) at hIzero
          change IsZero (S.X₁.homology ((n + 1) + 1)) at hFzero
          exact (hS.homology_exact₃ (n + 1) ((n + 1) + 1) (by simp)).isZero_X₂
            (hIzero.eq_of_src _ _) (hFzero.eq_of_tgt _ _)
        have hQ : Subsingleton (CategoryTheory.Sheaf.H Q (n + 1)) :=
          ih Q hQinter hQexact
        exact injectiveResolution_subsingleton_H_of_cokernel F n hQ
  · exact cechComplex_exactAt_succ_of_subsingleton_restrict_H U F hU hinter n

end

end TopCat.Sheaf
