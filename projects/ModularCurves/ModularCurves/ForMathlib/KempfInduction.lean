import Mathlib.Topology.Sets.OpenCover
import ModularCurves.ForMathlib.KempfLocalKilling

/-!
# Kempf's local-killing induction

This file proves the induction which upgrades local vanishing of sheaf cohomology on a basis to
an open cover killing a class in the next degree. The short-exact restriction calculation and
cohomological naturality step are separated into option-free helpers.
-/

open CategoryTheory Limits Opposite TopologicalSpace

universe u

namespace TopCat.Sheaf

variable {X : TopCat.{u}}

open Topology

private lemma restrict_cokernel_H_subsingleton
    (pres : ShortComplex (Sheaf AddCommGrpCat.{u} X)) (presEx : pres.ShortExact)
    [pres.X₂.IsFlasque] (r : ℕ) (U : Opens X) (hr : 1 ≤ r)
    (hnext : Subsingleton (H ((restrict AddCommGrpCat U.isOpenEmbedding).obj pres.X₁) (r + 1))) :
    Subsingleton (H ((restrict AddCommGrpCat U.isOpenEmbedding).obj pres.X₃) r) := by
  let presU := pres.map (restrict AddCommGrpCat U.isOpenEmbedding)
  have presUEx : presU.ShortExact := presEx.map_of_exact _
  have hnext' : Subsingleton (presU.X₁.H (r + 1)) := hnext
  refine subsingleton_of_forall_eq 0 fun x => ?_
  obtain ⟨x₂, rfl⟩ := CategoryTheory.Sheaf.H.longSequence_exact₃
    presUEx r (r + 1) rfl x (Subsingleton.elim _ _)
  have hmiddle : Subsingleton (presU.X₂.H r) := by
    haveI : presU.X₂.IsFlasque := IsFlasque.of_restrict _ pres.X₂ U.isOpenEmbedding
    rw [(Nat.sub_eq_iff_eq_add hr).mp rfl]
    infer_instance
  rw [Subsingleton.elim x₂ 0]
  simp only [map_zero]
  rfl

private lemma map_restrictPushforward_shortExact
    (pres : ShortComplex (Sheaf AddCommGrpCat.{u} X)) (presEx : pres.ShortExact)
    {B : Set (Opens X)} (hB : Opens.IsBasis B)
    (hinter : ∀ U V : Opens X, U ∈ B → V ∈ B → U ⊓ V ∈ B)
    (U : Opens X) (hU : U ∈ B)
    (hHOne : ∀ V : Opens X, V ∈ B →
      Subsingleton (H ((restrict AddCommGrpCat V.isOpenEmbedding).obj pres.X₁) 1)) :
    (pres.map (restrict AddCommGrpCat U.isOpenEmbedding ⋙
      pushforward AddCommGrpCat U.inclusion')).ShortExact := by
  have hleft := ((restrict AddCommGrpCat U.isOpenEmbedding ⋙
    pushforward AddCommGrpCat U.inclusion').preservesFiniteLimits_tfae.out
      3 1 rfl rfl).mp inferInstance pres ⟨presEx.1, presEx.2⟩
  refine ShortComplex.ShortExact.mk' hleft.1 hleft.2 ?_
  dsimp
  rw [← isLocallySurjective_iff_epi, Presheaf.isLocallySurjective_iff]
  intro V s x hx
  obtain ⟨W, hW⟩ := Opens.isBasis_iff_nbhd.mp hB hx
  refine ⟨W, hW.2.2, ?_, hW.2.1⟩
  have fs {V : Opens X} (hV : V ∈ B) :
      Function.Surjective (pres.g.hom.app (op V)) := by
    erw [← Opens.isOpenEmbedding_obj_top V]
    let presV := pres.map (restrict AddCommGrpCat V.isOpenEmbedding)
    have presVEx : presV.ShortExact := presEx.map_of_exact _
    have hH : Subsingleton (presV.X₁.H 1) := hHOne V hV
    exact CategoryTheory.Sheaf.H.longSequence_surjective_of_subsingleton_H
      presVEx isTerminalTop
  have hBasis : U.isOpenEmbedding.functor.obj ((Opens.map U.inclusion').obj W) ∈ B := by
    rw [Opens.functor_map_eq_inf]
    exact hinter _ _ hW.1 hU
  apply fs hBasis

private lemma map_toRestrict_delta_eq_zero
    (pres : ShortComplex (Sheaf AddCommGrpCat.{u} X)) (presEx : pres.ShortExact)
    (U : Opens X) (n : ℕ)
    (hrestricted : (pres.map (restrict AddCommGrpCat U.isOpenEmbedding ⋙
      pushforward AddCommGrpCat U.inclusion')).ShortExact)
    (b : pres.X₃.H (n + 1))
    (hb : H.map ((toRestrict AddCommGrpCat U).app pres.X₃) (n + 1) b = 0) :
    H.map ((toRestrict AddCommGrpCat U).app pres.X₁) (n + 2)
      (CategoryTheory.Sheaf.H.δ presEx (n + 1) (n + 2) rfl b) = 0 := by
  let res := pres.mapNatTrans (toRestrict AddCommGrpCat U)
  let presU := pres.map (restrict AddCommGrpCat U.isOpenEmbedding ⋙
    pushforward AddCommGrpCat U.inclusion')
  let δPres : H pres.X₃ (n + 1) →+ H pres.X₁ (n + 2) :=
    CategoryTheory.Sheaf.H.δ presEx (n + 1) (n + 2) rfl
  let δPresU : H presU.X₃ (n + 1) →+ H presU.X₁ (n + 2) :=
    CategoryTheory.Sheaf.H.δ hrestricted (n + 1) (n + 2) rfl
  have hnat : δPresU (H.map res.τ₃ (n + 1) b) =
      H.map res.τ₁ (n + 2) (δPres b) := by
    exact CategoryTheory.Sheaf.H.δ_naturality
      (n + 1) (n + 2) rfl presEx hrestricted res b
  have hτ₃ : H.map res.τ₃ (n + 1) b = 0 := by
    change H.map ((toRestrict AddCommGrpCat U).app pres.X₃) (n + 1) b = 0
    exact hb
  have hzero : δPresU (H.map res.τ₃ (n + 1) b) = 0 :=
    (congrArg δPresU hτ₃).trans (map_zero δPresU)
  change H.map res.τ₁ (n + 2) (δPres b) = 0
  exact hnat.symm.trans hzero

/-- Kempf's local-killing induction: if cohomology in degrees `1` through `n` vanishes on a
basis stable under intersections, then every class in degree `n + 1` vanishes on a cover by
basis opens. -/
theorem kempfProp1 (F : Sheaf AddCommGrpCat.{u} X) (n : ℕ) {B : Set (Opens X)}
    (hB : Opens.IsBasis B)
    (hinter : ∀ U V : Opens X, U ∈ B → V ∈ B → U ⊓ V ∈ B)
    (vanish : ∀ (r : ℕ) (U : Opens X), 1 ≤ r → r ≤ n → U ∈ B →
      Subsingleton (H ((restrict AddCommGrpCat.{u} U.isOpenEmbedding).obj F) r))
    (c : H F (n + 1)) :
    ∃ (I : Type u) (U : I → Opens X), IsOpenCover U ∧
      ∀ i, U i ∈ B ∧ H.map ((toRestrict _ (U i)).app F) (n + 1) c = 0 := by
  induction n generalizing F with
  | zero =>
      let U : X → Opens X := fun x => (one_ex_opens_toRestrict_app_zero F hB c x).choose
      refine ⟨X, U, ?_, fun x => (one_ex_opens_toRestrict_app_zero F hB c x).choose_spec.2⟩
      rw [IsOpenCover, eq_top_iff]
      intro x _
      exact (le_iSup U x) (one_ex_opens_toRestrict_app_zero F hB c x).choose_spec.1
  | succ n hn =>
      let pres := (EnoughInjectives.presentation F).some.shortComplex
      have presEx : pres.ShortExact :=
        (EnoughInjectives.presentation F).some.shortExact_shortComplex
      obtain ⟨b, hb⟩ := CategoryTheory.Sheaf.H.longSequence_exact₁ presEx
        (n + 1) (n + 2) rfl c (Subsingleton.elim _ _)
      obtain ⟨I, U, hU₁, hU₂⟩ := hn pres.X₃ (by
        intro r U hr₁ hr₂ hU
        exact restrict_cokernel_H_subsingleton pres presEx r U hr₁
          (vanish (r + 1) U (by omega) (by omega) hU)) b
      refine ⟨I, U, hU₁, fun i => ⟨(hU₂ i).1, ?_⟩⟩
      have hrestricted :
          (pres.map (restrict AddCommGrpCat (U i).isOpenEmbedding ⋙
            pushforward AddCommGrpCat (U i).inclusion')).ShortExact :=
        map_restrictPushforward_shortExact pres presEx hB hinter (U i) (hU₂ i).1
          (fun V hV => vanish 1 V (le_refl 1) (by omega) hV)
      rw [← hb]
      exact map_toRestrict_delta_eq_zero pres presEx (U i) n hrestricted b (hU₂ i).2

end TopCat.Sheaf
