/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanModularForms contributors
-/
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.NumberTheory.ModularForms.QExpansion
import LeanModularForms.HeckeRIngs.GL2.Gamma1Pair
import LeanModularForms.HeckeRIngs.GL2.HeckeT_n
import LeanModularForms.HeckeRIngs.GL2.LevelRaise
import LeanModularForms.Modularforms.QExpansionSlash

/-!
# Miyake Theorem 4.6.5 — coprime sieving (downstream-facing helpers)

This file exposes the level/Nebentypus compatibility lemmas used downstream
by the SMO obligation chain.

## References

* Miyake, *Modular Forms*, Theorem 4.6.5.
* Diamond–Shurman, *A First Course in Modular Forms*, §5.6.
-/

open scoped ModularForm ArithmeticFunction MatrixGroups
open ModularFormClass CongruenceSubgroup Matrix.SpecialLinearGroup

namespace HeckeRing.GL2.MainLemma

/-- For `N ∣ M`, the image `(Γ₁(M)).map (mapGL ℝ)` is contained in
`(Γ₁(N)).map (mapGL ℝ)` inside `GL(2, ℝ)`. -/
theorem Gamma1_mapGL_le_of_dvd {M N : ℕ} (h : N ∣ M) :
    (Gamma1 M).map (mapGL ℝ) ≤ (Gamma1 N).map (mapGL ℝ) :=
  Subgroup.map_mono (Gamma1_le_of_dvd h)

/-- Restriction along `Γ₁(N) ≤ Γ₁(M)` (for `M ∣ N`) carries
`modFormCharSpace k χ` into `modFormCharSpace k (χ.comp (ZMod.unitsMap h))`,
i.e. the Nebentypus pulls back along the natural map `(ZMod N)ˣ → (ZMod M)ˣ`. -/
theorem restrictSubgroup_mem_modFormCharSpace
    {M N : ℕ} [NeZero M] [NeZero N] {k : ℤ} (χ : (ZMod M)ˣ →* ℂˣ)
    (h : M ∣ N) (f : ModularForm ((Gamma1 M).map (mapGL ℝ)) k)
    (hf : f ∈ modFormCharSpace k χ) :
    ModularForm.restrictSubgroup
        (Gamma1_mapGL_le_of_dvd h) f ∈
      modFormCharSpace k (χ.comp (ZMod.unitsMap h)) := by
  rw [modFormCharSpace_iff_nebentypus] at hf ⊢
  intro g
  have hg_M : (g : SL(2, ℤ)) ∈ Gamma0 M := Gamma0_le_of_dvd h g.property
  suffices h_units :
      Gamma0MapUnits (⟨(g : SL(2, ℤ)), hg_M⟩ : ↥(Gamma0 M)) =
        ZMod.unitsMap h (Gamma0MapUnits g) by
    rw [ModularForm.coe_restrictSubgroup, hf ⟨(g : SL(2, ℤ)), hg_M⟩,
      MonoidHom.comp_apply, h_units]
  apply Units.ext
  rw [ZMod.unitsMap_val, Gamma0MapUnits_val, Gamma0MapUnits_val]
  exact (ZMod.cast_intCast h (((g : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 1)).symm

/-- The Hecke operator `heckeT_p_divN` (level-`N` no-diamond case,
`p ∣ N`) preserves every `modFormCharSpace k χ` at level
`Γ₁(N).map mapGL ℝ`. -/
theorem heckeT_p_divN_preserves_modFormCharSpace
    {N : ℕ} [NeZero N] {k : ℤ} {p : ℕ}
    (hp : Nat.Prime p) (hpN : ¬ Nat.Coprime p N) (χ : (ZMod N)ˣ →* ℂˣ)
    {f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k}
    (hf : f ∈ modFormCharSpace k χ) :
    heckeT_p_divN k p hp hpN f ∈ modFormCharSpace k χ := by
  rw [modFormCharSpace_iff_nebentypus] at hf ⊢
  intro g
  show (heckeT_p_ut k p hp.pos ⇑f) ∣[k] mapGL ℝ (g : SL(2, ℤ)) =
    ↑(χ (Gamma0MapUnits g)) • heckeT_p_ut k p hp.pos ⇑f
  rw [heckeT_p_ut_orbit_comm_gamma0_fun k p hp hpN f g]
  show heckeT_p_ut k p hp.pos (⇑f ∣[k] mapGL ℝ (g : SL(2, ℤ))) = _
  rw [hf g]
  exact DFunLike.ext _ _ fun _ ↦ DFunLike.congr_fun
    ((heckeT_p_divN k p hp hpN).map_smul _ f) _

private theorem levelRaise_conj_char_eq
    (M : ℕ) [NeZero M] (d : ℕ) [NeZero d] (χ : (ZMod M)ˣ →* ℂˣ)
    (γ' : ↥(Gamma0 (d * M)))
    (hdvd : (d : ℤ) ∣ ((γ' : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0)
    (h_conj_G0 :
      (levelRaiseConjOfDvd d (γ' : SL(2, ℤ)) hdvd : SL(2, ℤ)) ∈
        Gamma0 M) :
    χ (Gamma0MapUnits (⟨_, h_conj_G0⟩ : ↥(Gamma0 M))) =
      (χ.comp (ZMod.unitsMap (Nat.dvd_mul_left M d))) (Gamma0MapUnits γ') := by
  rw [MonoidHom.comp_apply]
  congr 1
  apply Units.ext
  rw [ZMod.unitsMap_val, Gamma0MapUnits_val, Gamma0MapUnits_val]
  show (((levelRaiseConjOfDvd d (γ' : SL(2, ℤ)) hdvd
    : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ZMod M) = _
  rw [levelRaiseConjOfDvd_lower_right]
  exact (ZMod.cast_intCast (Nat.dvd_mul_left M d)
    (((γ' : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 1)).symm

/-- Level-raising pulls back the Nebentypus: for `f ∈ modFormCharSpace k χ`
at level `Γ₁(M)` and `d ≥ 1`, the level-raised form
`modularFormLevelRaise M d k f` at level `Γ₁(d·M)` lies in
`modFormCharSpace k (χ.comp (ZMod.unitsMap (Nat.dvd_mul_left M d)))`. -/
theorem modularFormLevelRaise_mem_modFormCharSpace
    (M : ℕ) [NeZero M] (d : ℕ) [NeZero d] (k : ℤ) (χ : (ZMod M)ˣ →* ℂˣ)
    {f : ModularForm ((Gamma1 M).map (mapGL ℝ)) k}
    (hf : f ∈ modFormCharSpace k χ) :
    modularFormLevelRaise M d k f ∈
      modFormCharSpace k (χ.comp (ZMod.unitsMap (Nat.dvd_mul_left M d))) := by
  rw [modFormCharSpace_iff_nebentypus] at hf ⊢
  intro γ'
  have hdvd : (d : ℤ) ∣ ((γ' : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0 :=
    Gamma0_dmul_lower_left_dvd d M _ γ'.property
  rw [coe_modularFormLevelRaise,
    slash_mapGL_levelRaiseFun d k _ hdvd]
  have h_conj_G0 :
      (levelRaiseConjOfDvd d (γ' : SL(2, ℤ)) hdvd : SL(2, ℤ)) ∈
        Gamma0 M :=
    levelRaiseConjOfDvd_mem_Gamma0 d M _ γ'.property
  rw [hf ⟨_, h_conj_G0⟩, levelRaise_conj_char_eq M d χ γ' hdvd h_conj_G0]
  exact DFunLike.ext _ _ fun _ ↦ DFunLike.congr_fun
    ((modularFormLevelRaise M d k).map_smul _ f) _

end HeckeRing.GL2.MainLemma
