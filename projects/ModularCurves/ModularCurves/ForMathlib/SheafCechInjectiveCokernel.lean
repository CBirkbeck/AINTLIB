import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import ModularCurves.ForMathlib.SheafCechInjectiveAugmentation

/-!
# Cech complexes of an injective presentation

An injective presentation `0 → F → I⁰ → Q → 0` remains short exact after
applying a native Cech complex whenever `H¹(F)` vanishes on every finite
intersection in the cover. The only right-exactness input is the resulting
local surjectivity on sections.
-/

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace TopCat.Sheaf

noncomputable section

variable {X : TopCat.{u}}
variable {ι : Type u} (U : ι → Opens X)

/-- The short exact injective presentation of a sheaf. -/
noncomputable def injectiveResolutionCokernelShortComplex
    (F : Sheaf AddCommGrpCat.{u} X) :
    ShortComplex
      (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :=
  let I := injectiveResolution (toSiteSheaf F)
  ShortComplex.mk (I.ι.f 0) (cokernel.π (I.ι.f 0))
    (cokernel.condition (I.ι.f 0))

/-- The injective presentation of a sheaf is short exact. -/
theorem injectiveResolutionCokernelShortComplex_shortExact
    (F : Sheaf AddCommGrpCat.{u} X) :
    (injectiveResolutionCokernelShortComplex F).ShortExact := by
  let I := injectiveResolution (toSiteSheaf F)
  change (ShortComplex.mk (I.ι.f 0) (cokernel.π (I.ι.f 0))
    (cokernel.condition (I.ι.f 0))).ShortExact
  exact ShortComplex.ShortExact.mk (ShortComplex.exact_cokernel (I.ι.f 0))

/-- Apply the native Cech complex to the injective presentation of a sheaf. -/
noncomputable def cechInjectiveResolutionCokernelShortComplex
    (F : Sheaf AddCommGrpCat.{u} X) :
    ShortComplex (CochainComplex AddCommGrpCat.{u} ℕ) :=
  (injectiveResolutionCokernelShortComplex F).map
    (cechSheafComplexFunctor U)

private noncomputable abbrev cechInjectiveResolutionCokernelDegree
    (F : Sheaf AddCommGrpCat.{u} X) (p : ℕ) :
    ShortComplex AddCommGrpCat.{u} :=
  (cechInjectiveResolutionCokernelShortComplex U F).map
    (HomologicalComplex.eval AddCommGrpCat (.up ℕ) p)

private theorem cechMap_apply
    {P Q : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}} (f : P ⟶ Q) (p : ℕ)
    (x : ((cechComplexFunctor U).obj P).X p)
    (i : Fin (p + 1) → ι) :
    cechCochainAddEquiv Q U p (((cechComplexFunctor U).map f).f p x) i =
      f.app (Opposite.op (∏ᶜ fun k : Fin (p + 1) ↦ U (i k)))
        (cechCochainAddEquiv P U p x i) := by
  rw [cechCochainAddEquiv_apply, cechCochainAddEquiv_apply]
  exact ConcreteCategory.congr_hom
    (Limits.Pi.map_π (fun j : Fin (p + 1) → ι ↦
      f.app (Opposite.op (∏ᶜ fun k : Fin (p + 1) ↦ U (j k)))) i) x

private noncomputable instance cechInjectiveResolutionCokernelDegree_mono
    (F : Sheaf AddCommGrpCat.{u} X) (p : ℕ) :
    Mono (cechInjectiveResolutionCokernelDegree U F p).f := by
  let I := injectiveResolution (toSiteSheaf F)
  change Mono (((cechComplexFunctor U).map (I.ι.f 0).hom).f p)
  exact cechInjectiveResolutionAugmentation_f_mono U F p

private theorem cechInjectiveResolutionCokernelDegree_exact
    (F : Sheaf AddCommGrpCat.{u} X) (p : ℕ) :
    (cechInjectiveResolutionCokernelDegree U F p).Exact := by
  let I := injectiveResolution (toSiteSheaf F)
  let Q := cokernel (I.ι.f 0)
  let T := cechInjectiveResolutionCokernelDegree U F p
  change T.Exact
  rw [ShortComplex.ab_exact_iff]
  intro y hy
  have hy' :
      Limits.Pi.map (fun i : Fin (p + 1) → ι ↦
        (cokernel.π (I.ι.f 0)).hom.app
          (Opposite.op (∏ᶜ fun k : Fin (p + 1) ↦ U (i k)))) y = 0 := hy
  have preimage (i : Fin (p + 1) → ι) :
      ∃ x : F.obj.obj
          (Opposite.op (∏ᶜ fun k : Fin (p + 1) ↦ U (i k))),
        (I.ι.f 0).hom.app
            (Opposite.op (∏ᶜ fun k : Fin (p + 1) ↦ U (i k))) x =
          Limits.Pi.π (fun j : Fin (p + 1) → ι ↦
            (I.cocomplex.X 0).obj.obj
              (Opposite.op (∏ᶜ fun k : Fin (p + 1) ↦ U (j k)))) i y := by
    let V := ∏ᶜ fun k : Fin (p + 1) ↦ U (i k)
    let S := injectiveResolutionCokernelShortComplex F
    have hyi :
        (cokernel.π (I.ι.f 0)).hom.app (Opposite.op V)
          (Limits.Pi.π (fun j : Fin (p + 1) → ι ↦
            (I.cocomplex.X 0).obj.obj
              (Opposite.op (∏ᶜ fun k : Fin (p + 1) ↦ U (j k)))) i y) = 0 := by
      have hmap := ConcreteCategory.congr_hom
        (Limits.Pi.map_π (fun j : Fin (p + 1) → ι ↦
          (cokernel.π (I.ι.f 0)).hom.app
            (Opposite.op (∏ᶜ fun k : Fin (p + 1) ↦ U (j k)))) i) y
      calc
        _ = Limits.Pi.π (fun j : Fin (p + 1) → ι ↦
              Q.obj.obj
                (Opposite.op (∏ᶜ fun k : Fin (p + 1) ↦ U (j k)))) i
              (Limits.Pi.map (fun j : Fin (p + 1) → ι ↦
                (cokernel.π (I.ι.f 0)).hom.app
                  (Opposite.op (∏ᶜ fun k : Fin (p + 1) ↦ U (j k)))) y) :=
          hmap.symm
        _ = 0 := by rw [hy', map_zero]
    have hS := injectiveResolutionCokernelShortComplex_shortExact F
    exact Sheaf.sections_exact_of_left_exact hS.exact hS.mono_f _ hyi
  choose x hx using preimage
  let x' := (cechCochainAddEquiv F.obj U p).symm x
  refine ⟨x', ?_⟩
  apply (cechCochainAddEquiv (I.cocomplex.X 0).obj U p).injective
  funext i
  calc
    _ = (I.ι.f 0).hom.app
          (Opposite.op (∏ᶜ fun k : Fin (p + 1) ↦ U (i k)))
          (cechCochainAddEquiv F.obj U p x' i) := by
      change cechCochainAddEquiv (I.cocomplex.X 0).obj U p
        (((cechComplexFunctor U).map (I.ι.f 0).hom).f p x') i = _
      exact cechMap_apply U (I.ι.f 0).hom p x' i
    _ = (I.ι.f 0).hom.app
          (Opposite.op (∏ᶜ fun k : Fin (p + 1) ↦ U (i k))) (x i) := by
      simp [x']
    _ = Limits.Pi.π (fun j : Fin (p + 1) → ι ↦
        (I.cocomplex.X 0).obj.obj
          (Opposite.op (∏ᶜ fun k : Fin (p + 1) ↦ U (j k)))) i y := hx i
    _ = _ := (cechCochainAddEquiv_apply (I.cocomplex.X 0).obj U p y i).symm

private theorem cechInjectiveResolutionCokernelDegree_surjective
    (F : Sheaf AddCommGrpCat.{u} X) (p : ℕ)
    (hH : ∀ i : Fin (p + 1) → ι,
      Subsingleton (CategoryTheory.Sheaf.H
        ((restrict AddCommGrpCat
          (∏ᶜ fun k : Fin (p + 1) ↦ U (i k)).isOpenEmbedding).obj F) 1)) :
    Function.Surjective
      (cechInjectiveResolutionCokernelDegree U F p).g := by
  let I := injectiveResolution (toSiteSheaf F)
  let Q := cokernel (I.ι.f 0)
  intro y
  have preimage (i : Fin (p + 1) → ι) :
      ∃ x : (I.cocomplex.X 0).obj.obj
          (Opposite.op (∏ᶜ fun k : Fin (p + 1) ↦ U (i k))),
        (cokernel.π (I.ι.f 0)).hom.app
            (Opposite.op (∏ᶜ fun k : Fin (p + 1) ↦ U (i k))) x =
          cechCochainAddEquiv Q.obj U p y i := by
    letI := hH i
    exact injectiveResolution_cokernel_app_surjective_of_subsingleton_H F
      (∏ᶜ fun k : Fin (p + 1) ↦ U (i k)) _
  choose x hx using preimage
  let x' := (cechCochainAddEquiv (I.cocomplex.X 0).obj U p).symm x
  refine ⟨x', ?_⟩
  apply (cechCochainAddEquiv Q.obj U p).injective
  funext i
  calc
    _ = (cokernel.π (I.ι.f 0)).hom.app
          (Opposite.op (∏ᶜ fun k : Fin (p + 1) ↦ U (i k)))
          (cechCochainAddEquiv (I.cocomplex.X 0).obj U p x' i) := by
      change cechCochainAddEquiv Q.obj U p
        (((cechComplexFunctor U).map (cokernel.π (I.ι.f 0)).hom).f p x') i = _
      exact cechMap_apply U (cokernel.π (I.ι.f 0)).hom p x' i
    _ = (cokernel.π (I.ι.f 0)).hom.app
          (Opposite.op (∏ᶜ fun k : Fin (p + 1) ↦ U (i k))) (x i) := by
      simp [x']
    _ = cechCochainAddEquiv Q.obj U p y i := hx i

/-- If `H¹` of a sheaf vanishes on every finite Cech intersection, applying
the native Cech complex to its injective presentation gives a short exact
sequence of cochain complexes. -/
theorem cechInjectiveResolutionCokernelShortComplex_shortExact
    (F : Sheaf AddCommGrpCat.{u} X)
    (hH : ∀ (p : ℕ) (i : Fin (p + 1) → ι),
      Subsingleton (CategoryTheory.Sheaf.H
        ((restrict AddCommGrpCat
          (∏ᶜ fun k : Fin (p + 1) ↦ U (i k)).isOpenEmbedding).obj F) 1)) :
    (cechInjectiveResolutionCokernelShortComplex U F).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro p
  let T := cechInjectiveResolutionCokernelDegree U F p
  change T.ShortExact
  haveI : Mono T.f := cechInjectiveResolutionCokernelDegree_mono U F p
  haveI : Epi T.g := (AddCommGrpCat.epi_iff_surjective _).2
    (cechInjectiveResolutionCokernelDegree_surjective U F p (hH p))
  exact ShortComplex.ShortExact.mk
    (cechInjectiveResolutionCokernelDegree_exact U F p)

end

end TopCat.Sheaf
