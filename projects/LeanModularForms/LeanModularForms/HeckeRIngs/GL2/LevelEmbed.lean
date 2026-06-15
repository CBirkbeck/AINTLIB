/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.HeckeRIngs.GL2.Gamma1Pair

/-!
# Level monotonicity of the congruence subgroups

Basic monotonicity lemmas for `Γ₁(N)` and `Γ₀(N)` under the divisibility order on levels —
definition-level prerequisites for level-raising and primitive-form theory (Miyake §4.6).

## Main results

* `Gamma1_le_of_dvd` / `Gamma0_le_of_dvd` — if `M ∣ N` then `Γ₁(N) ≤ Γ₁(M)` and `Γ₀(N) ≤ Γ₀(M)`.
* `Gamma1_le_Gamma0` — the standard inclusion `Γ₁(N) ≤ Γ₀(N)`.

## References

* Miyake, *Modular Forms*, §4.6 (Lemma 4.6.1, p.162)
* Diamond–Shurman, *A First Course in Modular Forms*, §5.7
-/

open Matrix Matrix.SpecialLinearGroup CongruenceSubgroup

open scoped MatrixGroups ModularForm

namespace HeckeRing.GL2

/-- `Gamma1(N) ≤ Gamma1(M)` when `M ∣ N`: if `a ≡ 1 mod N` then `a ≡ 1 mod M`,
and if `N ∣ c` then `M ∣ c`. -/
theorem Gamma1_le_of_dvd {M N : ℕ} (h : M ∣ N) :
    Gamma1 N ≤ Gamma1 M := by
  intro A hA
  rw [Gamma1_mem] at hA ⊢
  set φ := ZMod.castHom h (ZMod M)
  exact ⟨by simpa [map_intCast, map_one] using congr_arg φ hA.1,
    by simpa [map_intCast, map_one] using congr_arg φ hA.2.1,
    by simpa [map_intCast, map_zero] using congr_arg φ hA.2.2⟩

/-- `Gamma0(N) ≤ Gamma0(M)` when `M ∣ N`: if `N ∣ c` then `M ∣ c`. -/
theorem Gamma0_le_of_dvd {M N : ℕ} (h : M ∣ N) :
    Gamma0 N ≤ Gamma0 M := by
  intro A hA
  rw [Gamma0_mem] at hA ⊢
  simpa [map_intCast, map_zero] using congr_arg (ZMod.castHom h (ZMod M)) hA

/-- `Gamma1(N) ≤ Gamma0(N)` (standard inclusion, for convenience). -/
theorem Gamma1_le_Gamma0 (N : ℕ) : Gamma1 N ≤ Gamma0 N :=
  Gamma1_in_Gamma0 N

end HeckeRing.GL2
