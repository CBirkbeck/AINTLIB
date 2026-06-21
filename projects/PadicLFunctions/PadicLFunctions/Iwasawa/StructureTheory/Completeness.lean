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

/-- `HasEnoughRootsOfUnity 𝒪 (exponent Hˣ)` from `(exponent H)` (equal, since `H ≃* Hˣ`). -/
theorem hasEnoughRootsOfUnity_units [HasEnoughRootsOfUnity 𝒪 (Monoid.exponent H)] :
    HasEnoughRootsOfUnity 𝒪 (Monoid.exponent Hˣ) := by
  rw [Monoid.exponent_eq_of_mulEquiv (toUnits : H ≃* Hˣ).symm]; infer_instance

/-- **Characters separate points** (from enough roots of unity): for `a ≠ 1` there is a character
`ω : H →* 𝒪ˣ` with `ω a ≠ 1`.  (`MulChar.exists_apply_ne_one_of_hasEnoughRootsOfUnity` transported
across `MulChar H 𝒪 ≃ (Hˣ →* 𝒪ˣ)` (`equivToUnitHom`) and `H ≃* Hˣ` (`toUnits`).) -/
theorem exists_char_apply_ne_one [IsDomain 𝒪] [HasEnoughRootsOfUnity 𝒪 (Monoid.exponent H)]
    {a : H} (ha : a ≠ 1) : ∃ ω : H →* 𝒪ˣ, ω a ≠ 1 := by
  haveI := hasEnoughRootsOfUnity_units 𝒪 H
  obtain ⟨χ, hχ⟩ := MulChar.exists_apply_ne_one_of_hasEnoughRootsOfUnity H 𝒪 ha
  refine ⟨(MulChar.equivToUnitHom χ).comp (toUnits : H ≃* Hˣ).toMonoidHom, ?_⟩
  intro h
  apply hχ
  have hco : ((MulChar.equivToUnitHom χ) (toUnits a) : 𝒪) = χ a := by
    rw [MulChar.coe_equivToUnitHom]; simp
  rw [← hco]; exact Units.val_eq_one.mpr h

/-- The character group `H →* 𝒪ˣ` has the same cardinality as `H`
(`CommGroup.monoidHom_mulEquiv_of_hasEnoughRootsOfUnity`: `(H →* 𝒪ˣ) ≃* H`). -/
theorem card_charHom_eq [IsDomain 𝒪] [HasEnoughRootsOfUnity 𝒪 (Monoid.exponent H)]
    [Fintype (H →* 𝒪ˣ)] : Fintype.card (H →* 𝒪ˣ) = Fintype.card H := by
  obtain ⟨e⟩ := CommGroup.monoidHom_mulEquiv_of_hasEnoughRootsOfUnity H 𝒪
  rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, Nat.card_congr e.toEquiv]

/-- **Dual character orthogonality**: `∑_{ω : H →* 𝒪ˣ} ω(a) = |H|·δ_{a,1}`.  (`a = 1`: every
`ω(1) = 1`, so the sum is `|H →* 𝒪ˣ| = |H|` by `card_charHom_eq`; `a ≠ 1`: `dualCharSum_eq_zero_of_sep`
with the separating character from `exists_char_apply_ne_one`.) -/
theorem dualCharSum [IsDomain 𝒪] [DecidableEq H] [HasEnoughRootsOfUnity 𝒪 (Monoid.exponent H)]
    [Fintype (H →* 𝒪ˣ)] (a : H) :
    ∑ ω : H →* 𝒪ˣ, ((ω a : 𝒪ˣ) : 𝒪) = if a = 1 then (Fintype.card H : 𝒪) else 0 := by
  split_ifs with ha
  · subst ha
    simp only [map_one, Units.val_one, Finset.sum_const, Finset.card_univ, card_charHom_eq 𝒪 H,
      nsmul_eq_mul, mul_one]
  · obtain ⟨ω₀, hω₀⟩ := exists_char_apply_ne_one 𝒪 H ha
    exact dualCharSum_eq_zero_of_sep 𝒪 H ω₀ hω₀

/-- **Completeness of the isotypic idempotents** (the "extend `L`" assumption discharged): under
`HasEnoughRootsOfUnity 𝒪 (exponent H)`, `∑_ω e_ω = 1`.  Swapping the sums in
`e_ω = ∑_a (|H|⁻¹ ω(a)⁻¹)·[a]` and applying the dual orthogonality `∑_ω ω(a)⁻¹ = ∑_ω ω(a⁻¹) =
|H|·δ_{a,1}` collapses everything to `[1] = 1`. -/
theorem isotypicIdempotent_sum_eq_one [IsDomain 𝒪] [Invertible (Fintype.card H : 𝒪)]
    [HasEnoughRootsOfUnity 𝒪 (Monoid.exponent H)] [Fintype (H →* 𝒪ˣ)] :
    ∑ ω : H →* 𝒪ˣ, isotypicIdempotent 𝒪 H ω = 1 := by
  classical
  simp only [isotypicIdempotent]
  rw [Finset.sum_comm]
  have hstep : ∀ a : H, ∑ ω : H →* 𝒪ˣ,
      MonoidAlgebra.single a
        (algebraMap 𝒪 (IwasawaAlgebra 𝒪) (⅟(Fintype.card H : 𝒪) * ((ω a)⁻¹ : 𝒪ˣ)))
      = MonoidAlgebra.single a (if a = 1 then (1 : IwasawaAlgebra 𝒪) else 0) := by
    intro a
    have hsingle : ∑ ω : H →* 𝒪ˣ, MonoidAlgebra.single a
          (algebraMap 𝒪 (IwasawaAlgebra 𝒪) (⅟(Fintype.card H : 𝒪) * ((ω a)⁻¹ : 𝒪ˣ)))
        = MonoidAlgebra.single a (∑ ω : H →* 𝒪ˣ,
            algebraMap 𝒪 (IwasawaAlgebra 𝒪) (⅟(Fintype.card H : 𝒪) * ((ω a)⁻¹ : 𝒪ˣ))) :=
      (map_sum (Finsupp.singleAddHom a) _ _).symm
    rw [hsingle]
    congr 1
    rw [← map_sum,
      show (∑ ω : H →* 𝒪ˣ, ⅟(Fintype.card H : 𝒪) * ((ω a)⁻¹ : 𝒪ˣ))
          = ⅟(Fintype.card H : 𝒪) * ∑ ω : H →* 𝒪ˣ, (((ω a)⁻¹ : 𝒪ˣ) : 𝒪) from by
        rw [Finset.mul_sum]]
    have hdual : ∑ ω : H →* 𝒪ˣ, (((ω a)⁻¹ : 𝒪ˣ) : 𝒪)
        = if a = 1 then (Fintype.card H : 𝒪) else 0 := by
      simp_rw [show ∀ ω : H →* 𝒪ˣ, (((ω a)⁻¹ : 𝒪ˣ) : 𝒪) = ((ω a⁻¹ : 𝒪ˣ) : 𝒪) from
        fun ω => by rw [← map_inv]]
      rw [dualCharSum 𝒪 H a⁻¹, inv_eq_one]
    rw [hdual]
    split_ifs with ha
    · rw [invOf_mul_self, map_one]
    · rw [mul_zero, map_zero]
  rw [Finset.sum_congr rfl (fun a _ => hstep a), Finset.sum_eq_single (1 : H)]
  · rw [if_pos rfl]; exact (MonoidAlgebra.one_def).symm
  · intro a _ ha; rw [if_neg ha, MonoidAlgebra.single_zero]
  · intro h; exact absurd (Finset.mem_univ (1 : H)) h
