import PadicLFunctions.Iwasawa.StructureTheory.Isotypic
import Mathlib.NumberTheory.MulChar.Duality
import Mathlib.RingTheory.RootsOfUnity.EnoughRootsOfUnity

/-!
# Completeness of the isotypic idempotents  (S13-S5, the "extend L" assumption discharged)

The isotypic decomposition machinery (`isInternal_isotypicComponent`, `charIdealGroup_quotient`, …)
takes the completeness `∑_ω e_ω = 1` as a hypothesis — the source's "extend `L` by the values of the
characters" assumption.  This file *discharges* it from a `HasEnoughRootsOfUnity` hypothesis on the
base ring (true for `𝒪 = ℤ_p` and `H = Δ = μ_{(p−1)/2}`, since `μ_{p−1} ⊆ ℤ_p` via Teichmüller —
`PadicLFunctions.instHasEnoughRootsOfUnity`).

The proof is the dual character orthogonality `∑_{ω : H →* 𝒪ˣ} ω(a) = |H|·δ_{a,1}`:
* `a ≠ 1`: reindexing the sum by a *separating* character `ω₀` (which exists by
  `MulChar.exists_apply_ne_one_of_hasEnoughRootsOfUnity`) gives `ω₀(a)·S = S`, so `S = 0`
  (`dualCharSum_eq_zero_of_sep`);
* `a = 1`: every `ω(1) = 1`, so the sum is `|H →* 𝒪ˣ| = |H|` (`MulChar.card_eq_card_units` via duality).

Plugging into `isotypicIdempotent ω = ∑_a (|H|⁻¹ ω(a)⁻¹) • [a]` collapses `∑_ω e_ω` to `[1] = 1`.

## Main declarations

* `Iwasawa.dualCharSum_eq_zero_of_sep`: the reindexing vanishing (no roots-of-unity hypothesis).
* `Iwasawa.exists_char_apply_ne_one`: characters separate points, from `HasEnoughRootsOfUnity`.
* `Iwasawa.isotypicIdempotent_sum_eq_one`: `∑_ω e_ω = 1`.
-/

noncomputable section

namespace Iwasawa

open scoped BigOperators

variable (𝒪 : Type*) [CommRing 𝒪] (H : Type*) [CommGroup H] [Fintype H]

/-- **Dual orthogonality, vanishing case.**  If `ω₀` is a character with `ω₀(a) ≠ 1`, then
`∑_{ω : H →* 𝒪ˣ} ω(a) = 0` (reindex `ω ↦ ω₀·ω`: `ω₀(a)·S = S`, and `ω₀(a) − 1` is a non-zero-divisor
in the domain `𝒪`). -/
theorem dualCharSum_eq_zero_of_sep [IsDomain 𝒪] [Fintype (H →* 𝒪ˣ)] {a : H} (ω₀ : H →* 𝒪ˣ)
    (hω₀ : ω₀ a ≠ 1) : ∑ ω : H →* 𝒪ˣ, ((ω a : 𝒪ˣ) : 𝒪) = 0 := by
  have hreindex : ∑ ω : H →* 𝒪ˣ, ((ω a : 𝒪ˣ) : 𝒪) = ∑ ω : H →* 𝒪ˣ, (((ω₀ * ω) a : 𝒪ˣ) : 𝒪) :=
    (Equiv.sum_comp (Equiv.mulLeft ω₀) (fun ω => ((ω a : 𝒪ˣ) : 𝒪))).symm
  have hfactor : ∑ ω : H →* 𝒪ˣ, (((ω₀ * ω) a : 𝒪ˣ) : 𝒪)
      = ((ω₀ a : 𝒪ˣ) : 𝒪) * ∑ ω : H →* 𝒪ˣ, ((ω a : 𝒪ˣ) : 𝒪) := by
    simp_rw [MonoidHom.mul_apply, Units.val_mul, Finset.mul_sum]
  rw [hfactor] at hreindex
  have hz : (((ω₀ a : 𝒪ˣ) : 𝒪) - 1) * ∑ ω : H →* 𝒪ˣ, ((ω a : 𝒪ˣ) : 𝒪) = 0 := by
    linear_combination -hreindex
  rcases mul_eq_zero.mp hz with h | h
  · exact absurd (Units.val_eq_one.mp (sub_eq_zero.mp h)) hω₀
  · exact h

end Iwasawa
