/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.HeckeRIngs.GL2.CharacterDecomp
import LeanModularForms.HeckeRIngs.GL2.HeckeModularForm_Gamma0
import LeanModularForms.HeckeRIngs.GL2.HeckeT_n
import LeanModularForms.HeckeRIngs.GL2.HeckeT_p_Gamma0
import LeanModularForms.HeckeRIngs.GL2.HeckeT_p_Gamma1

/-!
# Hecke operators restricted to `modFormCharSpace k χ`

This file packages the Hecke operators as endomorphisms of the character eigenspace
`modFormCharSpace k χ`.  The character-space *preservation* lemmas they rely on
(`heckeT_p_all_preserves_modFormCharSpace`, `heckeT_ppow_preserves_modFormCharSpace`,
`heckeT_n_preserves_modFormCharSpace_all`, `heckeT_n_preserves_charSpace`) live in
`HeckeT_n.lean`, since they are proved directly by block induction over the construction of
`T_n` (no commutativity needed) and are consumed there and in `FourierHecke.lean`.

## Main definitions

* `heckeT_p_all_charRestrict` — `heckeT_p_all k p hp` as an endomorphism of
  `modFormCharSpace k χ`.
* `heckeT_n_charRestrict` — `heckeT_n k n` (for `n` coprime to `N`) restricted
  to `modFormCharSpace k χ`.
* `heckeT_n_charRestrictAll` — the same for **arbitrary** positive `n`.

## References

* Shimura, *Introduction to the Arithmetic Theory of Automorphic Functions*, §3.4.
* Diamond–Shurman, *A First Course in Modular Forms*, §5.2.
-/

open Matrix Matrix.SpecialLinearGroup HeckeRing.GLn CongruenceSubgroup
open HeckeRing

open scoped Pointwise MatrixGroups ModularForm UpperHalfPlane

namespace HeckeRing.GL2

variable {N : ℕ} [NeZero N]

/-- `heckeT_p_all k p hp` restricted to `modFormCharSpace k χ` as a `ℂ`-linear
endomorphism. -/
noncomputable def heckeT_p_all_charRestrict (k : ℤ) (p : ℕ) (hp : Nat.Prime p)
    (χ : (ZMod N)ˣ →* ℂˣ) :
    Module.End ℂ (modFormCharSpace k χ) where
  toFun f :=
    ⟨heckeT_p_all k p hp (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k),
      heckeT_p_all_preserves_modFormCharSpace k p hp χ f.property⟩
  map_add' _ _ := Subtype.ext (map_add (heckeT_p_all k p hp) _ _)
  map_smul' c _ := Subtype.ext (map_smul (heckeT_p_all k p hp) c _)

@[simp] lemma heckeT_p_all_charRestrict_coe (k : ℤ) (p : ℕ) (hp : Nat.Prime p)
    (χ : (ZMod N)ˣ →* ℂˣ) (f : modFormCharSpace k χ) :
    ((heckeT_p_all_charRestrict k p hp χ f :
        modFormCharSpace k χ) : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) =
    heckeT_p_all k p hp (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) := rfl

/-- `heckeT_n k n` (for `n` coprime to `N`) restricted to `modFormCharSpace k χ`
as a `ℂ`-linear endomorphism. -/
noncomputable def heckeT_n_charRestrict (k : ℤ) (n : ℕ) [NeZero n]
    (hn : Nat.Coprime n N) (χ : (ZMod N)ˣ →* ℂˣ) :
    Module.End ℂ (modFormCharSpace k χ) where
  toFun f :=
    ⟨heckeT_n k n (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k),
      heckeT_n_preserves_charSpace k n hn χ f.property⟩
  map_add' _ _ := Subtype.ext (map_add (heckeT_n k n) _ _)
  map_smul' c _ := Subtype.ext (map_smul (heckeT_n k n) c _)

@[simp] lemma heckeT_n_charRestrict_coe (k : ℤ) (n : ℕ) [NeZero n]
    (hn : Nat.Coprime n N) (χ : (ZMod N)ˣ →* ℂˣ) (f : modFormCharSpace k χ) :
    ((heckeT_n_charRestrict k n hn χ f :
        modFormCharSpace k χ) : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) =
    heckeT_n k n (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) := rfl

/-- `heckeT_n k n` restricted to `modFormCharSpace k χ`, for **arbitrary** positive `n`
(extends `heckeT_n_charRestrict`, which requires `n` coprime to `N`). -/
noncomputable def heckeT_n_charRestrictAll (k : ℤ) (n : ℕ) [NeZero n]
    (χ : (ZMod N)ˣ →* ℂˣ) :
    Module.End ℂ (modFormCharSpace k χ) where
  toFun f :=
    ⟨heckeT_n k n (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k),
      heckeT_n_preserves_modFormCharSpace_all k n χ f.property⟩
  map_add' _ _ := Subtype.ext (map_add (heckeT_n k n) _ _)
  map_smul' c _ := Subtype.ext (map_smul (heckeT_n k n) c _)

@[simp] lemma heckeT_n_charRestrictAll_coe (k : ℤ) (n : ℕ) [NeZero n]
    (χ : (ZMod N)ˣ →* ℂˣ) (f : modFormCharSpace k χ) :
    ((heckeT_n_charRestrictAll k n χ f :
        modFormCharSpace k χ) : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) =
    heckeT_n k n (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) := rfl

end HeckeRing.GL2
