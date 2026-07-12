import Mathlib.Topology.Sheaves.Flasque

import ModularCurves.ForMathlib.KempfLocalKilling

/-!
# Degree-one cohomology from a two-open cover

This file proves the elementwise Mayer--Vietoris criterion needed for the pole-chart
calculation. It avoids the cohomology presheaf `H'`: a degree-one class is represented
using an injective presentation, lifted over the two opens, adjusted on their overlap,
and then killed by ordinary sheaf gluing.
-/

open CategoryTheory Limits Opposite TopologicalSpace

universe u

namespace TopCat.Sheaf

variable {X : TopCat.{u}}

private lemma section_surjective_of_restrict_H_one_subsingleton
    {S : ShortComplex (Sheaf AddCommGrpCat.{u} X)} (hS : S.ShortExact)
    (U : Opens X)
    (hH : Subsingleton (CategoryTheory.Sheaf.H
      ((restrict AddCommGrpCat U.isOpenEmbedding).obj S.X₁) 1)) :
    Function.Surjective (S.g.hom.app (op U)) := by
  erw [← Opens.isOpenEmbedding_obj_top U]
  let SU := S.map (restrict AddCommGrpCat U.isOpenEmbedding)
  have hSU : SU.ShortExact := hS.map_of_exact _
  letI : Subsingleton (CategoryTheory.Sheaf.H SU.X₁ 1) := hH
  exact CategoryTheory.Sheaf.H.longSequence_surjective_of_subsingleton_H
    hSU isTerminalTop

private lemma exists_global_lift_of_two_open_cover
    {S : ShortComplex (Sheaf AddCommGrpCat.{u} X)} (hS : S.ShortExact)
    (U V : Opens X) (hUV : U ⊔ V = ⊤)
    (hsections : ∀ a : S.X₁.obj.obj (op (U ⊓ V)),
      ∃ aU : S.X₁.obj.obj (op U), ∃ aV : S.X₁.obj.obj (op V),
        S.X₁.obj.map (homOfLE inf_le_left).op aU -
          S.X₁.obj.map (homOfLE inf_le_right).op aV = a)
    (hU : Function.Surjective (S.g.hom.app (op U)))
    (hV : Function.Surjective (S.g.hom.app (op V))) :
    Function.Surjective (S.g.hom.app (op (⊤ : Opens X))) := by
  intro b
  let bU := S.X₃.obj.map (homOfLE (le_top : U ≤ ⊤)).op b
  let bV := S.X₃.obj.map (homOfLE (le_top : V ≤ ⊤)).op b
  obtain ⟨sU, hsU⟩ := hU bU
  obtain ⟨sV, hsV⟩ := hV bV
  let d := S.X₂.obj.map (homOfLE inf_le_left).op sU -
    S.X₂.obj.map (homOfLE inf_le_right).op sV
  have hd : S.g.hom.app (op (U ⊓ V)) d = 0 := by
    dsimp only [d]
    rw [map_sub, hom_naturality_apply, hom_naturality_apply, hsU, hsV]
    dsimp only [bU, bV]
    rw [restrict_restrict_apply b (U ⊓ V).leTop.op
        (homOfLE (le_top : U ≤ ⊤)).op
        (homOfLE inf_le_left).op,
      restrict_restrict_apply b (U ⊓ V).leTop.op
        (homOfLE (le_top : V ≤ ⊤)).op
        (homOfLE inf_le_right).op,
      sub_self]
  obtain ⟨a, ha⟩ := Sheaf.sections_exact_of_left_exact hS.1 hS.2 d hd
  obtain ⟨aU, aV, haUV⟩ := hsections a
  let sU' := sU - S.f.hom.app (op U) aU
  let sV' := sV - S.f.hom.app (op V) aV
  have hsUV : S.X₂.obj.map (homOfLE inf_le_left).op sU' =
      S.X₂.obj.map (homOfLE inf_le_right).op sV' := by
    dsimp only [sU', sV']
    rw [map_sub, map_sub,
      ← hom_naturality_apply S.f (homOfLE inf_le_left).op aU,
      ← hom_naturality_apply S.f (homOfLE inf_le_right).op aV]
    dsimp only [d] at ha
    have hdiff :
        S.X₂.obj.map (homOfLE inf_le_left).op sU -
            S.X₂.obj.map (homOfLE inf_le_right).op sV =
          S.f.hom.app (op (U ⊓ V))
              (S.X₁.obj.map (homOfLE inf_le_left).op aU) -
            S.f.hom.app (op (U ⊓ V))
              (S.X₁.obj.map (homOfLE inf_le_right).op aV) := by
      rw [← ha, ← map_sub, haUV]
    calc
      _ = (S.X₂.obj.map (homOfLE inf_le_left).op sU -
              S.X₂.obj.map (homOfLE inf_le_right).op sV) +
            (S.X₂.obj.map (homOfLE inf_le_right).op sV -
              S.f.hom.app (op (U ⊓ V))
                (S.X₁.obj.map (homOfLE inf_le_left).op aU)) := by abel
      _ = (S.f.hom.app (op (U ⊓ V))
              (S.X₁.obj.map (homOfLE inf_le_left).op aU) -
            S.f.hom.app (op (U ⊓ V))
              (S.X₁.obj.map (homOfLE inf_le_right).op aV)) +
            (S.X₂.obj.map (homOfLE inf_le_right).op sV -
              S.f.hom.app (op (U ⊓ V))
                (S.X₁.obj.map (homOfLE inf_le_left).op aU)) := by rw [hdiff]
      _ = _ := by abel
  let W : Fin 2 → Opens X := ![U, V]
  let s : ∀ i, S.X₂.obj.obj (op (W i))
    | 0 => sU'
    | 1 => sV'
  have hcompatible : Presheaf.IsCompatible S.X₂.obj W s := by
    simp only [Presheaf.IsCompatible, Fin.forall_fin_two]
    refine ⟨⟨rfl, hsUV⟩, ?_, rfl⟩
    let e : V ⊓ U ≤ U ⊓ V := le_of_eq (inf_comm V U)
    have hswap := congrArg
      (fun q ↦ S.X₂.obj.map (homOfLE e).op q) hsUV
    rw [restrict_restrict_apply sU'
        (homOfLE (show V ⊓ U ≤ U from inf_le_right)).op
        (homOfLE (show U ⊓ V ≤ U from inf_le_left)).op (homOfLE e).op,
      restrict_restrict_apply sV'
        (homOfLE (show V ⊓ U ≤ V from inf_le_left)).op
        (homOfLE (show U ⊓ V ≤ V from inf_le_right)).op (homOfLE e).op] at hswap
    simp only [W, s, Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [Subsingleton.elim (V.infLELeft U).op
        (homOfLE (show V ⊓ U ≤ V from inf_le_left)).op,
      Subsingleton.elim (V.infLERight U).op
        (homOfLE (show V ⊓ U ≤ U from inf_le_right)).op]
    exact hswap.symm
  have hcover : (⊤ : Opens X) ≤ iSup W := by
    rw [← hUV]
    apply sup_le
    · simpa only [W, Matrix.cons_val_zero] using le_iSup W 0
    · simpa only [W, Matrix.cons_val_one, Matrix.cons_val_zero] using le_iSup W 1
  obtain ⟨t, ht, -⟩ := S.X₂.existsUnique_gluing' W ⊤ (fun _ ↦ homOfLE le_top)
    hcover s hcompatible
  have htU : S.X₂.obj.map (homOfLE (le_top : U ≤ ⊤)).op t = sU' := by
    convert ht 0 using 1 <;>
      simp only [W, s, Matrix.cons_val_zero] <;> rfl
  have htV : S.X₂.obj.map (homOfLE (le_top : V ≤ ⊤)).op t = sV' := by
    convert ht 1 using 1 <;>
      simp only [W, s, Matrix.cons_val_one, Matrix.cons_val_zero] <;> rfl
  refine ⟨t, ?_⟩
  apply S.X₃.eq_of_locally_eq₂ (homOfLE (le_top : U ≤ ⊤))
    (homOfLE (le_top : V ≤ ⊤))
    (by rw [hUV]) (S.g.hom.app (op ⊤) t) b
  · calc
      S.X₃.obj.map (homOfLE (le_top : U ≤ ⊤)).op (S.g.hom.app (op ⊤) t) =
          S.g.hom.app (op U)
            (S.X₂.obj.map (homOfLE (le_top : U ≤ ⊤)).op t) :=
        (hom_naturality_apply S.g (homOfLE (le_top : U ≤ ⊤)).op t).symm
      _ = S.g.hom.app (op U) sU' := congrArg _ htU
      _ = S.X₃.obj.map (homOfLE (le_top : U ≤ ⊤)).op b := by
        have hzero : S.g.hom.app (op U) (S.f.hom.app (op U) aU) = 0 := by
          have h := comp_app_apply S.zero (op U) aU
          change S.g.hom.app (op U) (S.f.hom.app (op U) aU) = 0 at h
          exact h
        dsimp only [sU']
        rw [map_sub, hzero, sub_zero, hsU]
  · calc
      S.X₃.obj.map (homOfLE (le_top : V ≤ ⊤)).op (S.g.hom.app (op ⊤) t) =
          S.g.hom.app (op V)
            (S.X₂.obj.map (homOfLE (le_top : V ≤ ⊤)).op t) :=
        (hom_naturality_apply S.g (homOfLE (le_top : V ≤ ⊤)).op t).symm
      _ = S.g.hom.app (op V) sV' := congrArg _ htV
      _ = S.X₃.obj.map (homOfLE (le_top : V ≤ ⊤)).op b := by
        have hzero : S.g.hom.app (op V) (S.f.hom.app (op V) aV) = 0 := by
          have h := comp_app_apply S.zero (op V) aV
          change S.g.hom.app (op V) (S.f.hom.app (op V) aV) = 0 at h
          exact h
        dsimp only [sV']
        rw [map_sub, hzero, sub_zero, hsV]

/-- If two opens cover a space, degree-one cohomology vanishes provided it vanishes on
each open and every overlap section is a difference of sections from the two opens. -/
theorem subsingleton_H_one_of_two_open_cover
    (F : Sheaf AddCommGrpCat.{u} X) (U V : Opens X) (hUV : U ⊔ V = ⊤)
    (hHU : Subsingleton (CategoryTheory.Sheaf.H
      ((restrict AddCommGrpCat U.isOpenEmbedding).obj F) 1))
    (hHV : Subsingleton (CategoryTheory.Sheaf.H
      ((restrict AddCommGrpCat V.isOpenEmbedding).obj F) 1))
    (hsections : ∀ a : F.obj.obj (op (U ⊓ V)),
      ∃ aU : F.obj.obj (op U), ∃ aV : F.obj.obj (op V),
        F.obj.map (homOfLE inf_le_left).op aU -
          F.obj.map (homOfLE inf_le_right).op aV = a) :
    Subsingleton (CategoryTheory.Sheaf.H F 1) := by
  refine subsingleton_of_forall_eq 0 fun c ↦ ?_
  let S := (EnoughInjectives.presentation F).some.shortComplex
  have hS : S.ShortExact :=
    (EnoughInjectives.presentation F).some.shortExact_shortComplex
  obtain ⟨b, hb⟩ := CategoryTheory.Sheaf.H.longSequence_equiv₀_exact₁
    hS isTerminalTop c (Subsingleton.elim _ _)
  have hU := section_surjective_of_restrict_H_one_subsingleton hS U hHU
  have hV := section_surjective_of_restrict_H_one_subsingleton hS V hHV
  obtain ⟨t, ht⟩ := exists_global_lift_of_two_open_cover hS U V hUV hsections hU hV b
  rw [← hb, ← ht, ← CategoryTheory.Sheaf.H.equiv₀_symm_naturality,
    CategoryTheory.Sheaf.H.longSequence_comp_zero₃]

end TopCat.Sheaf
