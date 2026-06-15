import BernoulliRegular.FLT37.LehmerVandiver.PlusCoprime.Sinnott.IndexFormula
import BernoulliRegular.FLT37.LehmerVandiver.PlusCoprime.Sinnott.CyclotomicUnitFamily


/-!
# `PollaczekInFamily` — Pollaczek descent to the family subgroup

The Pollaczek unit `pollaczekUnitPlus p K i = ∏_b cyclotomicRealUnit b ^ exp_b`
is by construction a finite product of real cyclotomic units. Each
`cyclotomicRealUnit b` (for `b ∈ {2, ..., (p-1)/2}`) descends to the K⁺-side
family element `cyclotomicUnitFamilyKplus (b - 2)`. The b=1 term is trivial.

Hence the K⁺-side preimage `v` of `pollaczekUnitPlus` is the corresponding
product of family elements raised to the same exponents — and lies in
`⟨family⟩` (a Subgroup).

This proves `PollaczekInFamily`.
-/

@[expose] public section

noncomputable section

open NumberField NumberField.IsCMField

namespace BernoulliRegular

namespace FLT37

namespace Sinnott

variable (p : ℕ) [hp : Fact p.Prime]
variable (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
  [IsCMField K]

set_option backward.isDefEq.respectTransparency false in
/-- The K⁺-side preimage of `pollaczekUnitPlus`: the product of family
elements raised to the Pollaczek exponents.

For `i_irreg : ℕ` (the irregular index), define

  `pollaczekUnitPlusKplus = ∏_{j : Fin ((p-3)/2)} family(j) ^ ((j+2)^(p-1-i_irreg))`

in `(𝓞 K⁺)ˣ`. By σ-distribution and the algebraMap identity for cyclotomic
units, its image under `algebraMap` equals `pollaczekUnitPlus p K i_irreg`. -/
noncomputable def pollaczekUnitPlusKplus (i_irreg : ℕ) (hp_odd : p ≠ 2)
    (hp_three : 3 ≤ p) :
    (𝓞 (NumberField.maximalRealSubfield K))ˣ :=
  ∏ j : Fin (NumberField.Units.rank
      (NumberField.maximalRealSubfield K)),
    cyclotomicUnitFamilyKplusFinRank p K hp_odd hp_three j ^
      (((j : ℕ) + 2) ^ (p - 1 - i_irreg))

set_option backward.isDefEq.respectTransparency false in
/-- `pollaczekUnitPlusKplus ∈ ⟨family⟩`. Direct from `Subgroup.prod_mem` +
`Subgroup.pow_mem` + `Subgroup.subset_closure`. -/
theorem pollaczekUnitPlusKplus_mem_familyClosure (i_irreg : ℕ) (hp_odd : p ≠ 2)
    (hp_three : 3 ≤ p) :
    pollaczekUnitPlusKplus p K i_irreg hp_odd hp_three ∈
      Subgroup.closure
        (Set.range (cyclotomicUnitFamilyKplusFinRank p K hp_odd hp_three)) := by
  unfold pollaczekUnitPlusKplus
  apply Subgroup.prod_mem
  intro j _
  exact Subgroup.pow_mem _ (Subgroup.subset_closure (Set.mem_range_self j)) _

set_option backward.isDefEq.respectTransparency false in
/-- `pollaczekUnitPlusKplus ∈ ⟨family⟩ ⊔ torsion`. Weakening the previous
membership. -/
theorem pollaczekUnitPlusKplus_mem (i_irreg : ℕ) (hp_odd : p ≠ 2)
    (hp_three : 3 ≤ p) :
    pollaczekUnitPlusKplus p K i_irreg hp_odd hp_three ∈
      Subgroup.closure
        (Set.range (cyclotomicUnitFamilyKplusFinRank p K hp_odd hp_three)) ⊔
      NumberField.Units.torsion (NumberField.maximalRealSubfield K) :=
  Subgroup.mem_sup_left
    (pollaczekUnitPlusKplus_mem_familyClosure p K i_irreg hp_odd hp_three)

/-! ## Algebra: `algebraMap pollaczekUnitPlusKplus = pollaczekUnitPlus`

The K⁺-side preimage `pollaczekUnitPlusKplus` maps under `algebraMap` to
the K-side `pollaczekUnitPlus p K i`. This requires:
* Distributing `algebraMap` through the product.
* For each `j`, `algebraMap (family j) = cyclotomicRealUnit (j+2)`
  (= the σ-symmetric K-side cyclotomic unit at `j+2`).
* `pollaczekUnitPlus = pollaczekUnit · σ(pollaczekUnit) =
   ∏_b cyclotomicRealUnit(b)^{exp_b}` (σ-distribution over product).
-/

set_option backward.isDefEq.respectTransparency false in
/-- Predicate: `algebraMap` of K⁺-side preimage equals K-side
`pollaczekUnitPlus`.

Substantive content: combines algebraMap distribution + σ-symmetric
factor pairing. Establishes `PollaczekInFamily`. -/
def AlgebraMapPollaczekUnitPlusKplus_eq (i_irreg : ℕ)
    (hp_odd : p ≠ 2) (hp_three : 3 ≤ p) : Prop :=
  (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)
      (pollaczekUnitPlusKplus p K i_irreg hp_odd hp_three :
        𝓞 (NumberField.maximalRealSubfield K)) : 𝓞 K) =
    ((FLT37.pollaczekUnitPlus p K i_irreg : (𝓞 K)ˣ) : 𝓞 K)

set_option backward.isDefEq.respectTransparency false in
/-- **`PollaczekInFamily` from the algebraMap equation**: combine
`pollaczekUnitPlusKplus_mem` (subgroup membership) with the algebraMap
equation. -/
theorem pollaczekInFamily_of_algebraMap_eq (i_irreg : ℕ)
    (hp_odd : p ≠ 2) (hp_three : 3 ≤ p)
    (h : AlgebraMapPollaczekUnitPlusKplus_eq p K i_irreg hp_odd hp_three) :
    PollaczekInFamily p K i_irreg hp_odd hp_three :=
  ⟨pollaczekUnitPlusKplus p K i_irreg hp_odd hp_three, h,
   pollaczekUnitPlusKplus_mem p K i_irreg hp_odd hp_three⟩

/-! ## Proof of `AlgebraMapPollaczekUnitPlusKplus_eq`

The claim: image of `pollaczekUnitPlusKplus` under `algebraMap` equals
`pollaczekUnitPlus` in `𝓞 K`. Proof outline:

1. `algebraMap` distributes through products and powers.
2. `algebraMap (family j) = (cyclotomicRealUnit (j+2) : 𝓞 K)`
   (via `algebraMap_realCyclotomicUnitPlus` + unit-value identity).
3. `pollaczekUnitPlus = ∏_b cyclotomicRealUnit(b)^{exp_b}` (σ-distribution
   over the Pollaczek product).
4. The b=1 term is trivial (`cyclotomicRealUnit 1 = 1`).
5. Reindex `b = j + 2` to match. -/

set_option backward.isDefEq.respectTransparency false in
/-- **Each family element's algebraMap is the K-side `realCyclotomicUnit`**.

Direct from `realCyclotomicUnitPlusUnit_val` + `algebraMap_realCyclotomicUnitPlus`. -/
theorem algebraMap_cyclotomicUnitFamilyKplus
    (j : Fin (NumberField.Units.rank
        (NumberField.maximalRealSubfield K)))
    (hp_odd : p ≠ 2) (hp_three : 3 ≤ p) :
    algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)
        ((cyclotomicUnitFamilyKplusFinRank p K hp_odd hp_three j :
          (𝓞 (NumberField.maximalRealSubfield K))ˣ) :
          𝓞 (NumberField.maximalRealSubfield K)) =
      FLT37.realCyclotomicUnit p K
        ((j.cast ((NumberField.IsCMField.units_rank_eq_units_rank (K := K)).trans
          (BernoulliRegular.units_rank_eq_prime_sub_three_div_two
            (p := p) (K := K)))) + 2) := by
  unfold cyclotomicUnitFamilyKplusFinRank cyclotomicUnitFamilyKplus
  rw [realCyclotomicUnitPlusUnit_val]
  exact FLT37.algebraMap_realCyclotomicUnitPlus p K _

set_option backward.isDefEq.respectTransparency false in
/-- **σ-distribution for `pollaczekUnit · σ(pollaczekUnit)`**: as elements
of `𝓞 K`, the σ-symmetric Pollaczek unit factors as a product of
real cyclotomic units.

  `(pollaczekUnitPlus : 𝓞 K) = ∏_{b ∈ Ico 1 ((p-1)/2+1)} realCyclotomicUnit b ^ (b^(p-1-i))`

Proof: σ-distribution + commutativity in `𝓞 K`. -/
theorem pollaczekUnitPlus_val_eq_prod_realCyclotomicUnit (i : ℕ) :
    ((FLT37.pollaczekUnitPlus p K i : (𝓞 K)ˣ) : 𝓞 K) =
      ∏ b ∈ (Finset.Ico 1 ((p - 1) / 2 + 1)).attach,
        FLT37.realCyclotomicUnit p K b.1 ^ ((b.1 : ℕ) ^ (p - 1 - i)) := by
  unfold FLT37.pollaczekUnitPlus
  rw [Units.val_mul]
  -- LHS: (pollaczekUnit · σ(pollaczekUnit) : 𝓞 K).
  -- = (pollaczekUnit : 𝓞 K) · (σ(pollaczekUnit) : 𝓞 K)
  -- = (pollaczekUnit : 𝓞 K) · ringOfIntegersComplexConj K (pollaczekUnit : 𝓞 K).
  unfold FLT37.pollaczekUnit
  -- pollaczekUnit = ∏ pollaczekFactor b ^ (b ^ (p - 1 - i)).
  rw [Units.coe_prod]
  rw [show ((unitsComplexConj K
      (∏ b ∈ (Finset.Ico 1 ((p - 1) / 2 + 1)).attach,
        FLT37.pollaczekFactor p K b.2 ^ ((b.1 : ℕ) ^ (p - 1 - i))) :
        (𝓞 K)ˣ) : 𝓞 K) =
      ringOfIntegersComplexConj K
        ((∏ b ∈ (Finset.Ico 1 ((p - 1) / 2 + 1)).attach,
          FLT37.pollaczekFactor p K b.2 ^ ((b.1 : ℕ) ^ (p - 1 - i))) :
          (𝓞 K)ˣ).val from rfl]
  rw [Units.coe_prod, map_prod]
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun b _ => ?_
  -- Each factor combines into
  -- `(pollaczekFactor b · σ(pollaczekFactor b)) ^ ...`.
  --             = realCyclotomicUnit b ^ ...
  rw [Units.val_pow_eq_pow_val, map_pow, ← mul_pow]
  congr 1

set_option backward.isDefEq.respectTransparency false in
/-- **`pollaczekUnitPlus` as a product over the family-index range**:
the product over `b ∈ Ico 1 ((p-1)/2 + 1)` reduces to a product over
`b ∈ Ico 2 ((p-1)/2 + 1)` since the b=1 term is `realCyclotomicUnit 1 = 1`. -/
theorem pollaczekUnitPlus_val_eq_prod_Ico_two (i : ℕ) (hp_three : 3 ≤ p) :
    ((FLT37.pollaczekUnitPlus p K i : (𝓞 K)ˣ) : 𝓞 K) =
      ∏ b ∈ Finset.Ico 2 ((p - 1) / 2 + 1),
        FLT37.realCyclotomicUnit p K b ^ (b ^ (p - 1 - i)) := by
  rw [pollaczekUnitPlus_val_eq_prod_realCyclotomicUnit]
  rw [Finset.prod_attach (Finset.Ico 1 ((p - 1) / 2 + 1))
        (fun b => FLT37.realCyclotomicUnit p K b ^ (b ^ (p - 1 - i)))]
  have h_half : 1 ≤ (p - 1) / 2 := by omega
  have h_split : Finset.Ico 1 ((p - 1) / 2 + 1) =
      insert 1 (Finset.Ico 2 ((p - 1) / 2 + 1)) := by
    ext x
    rw [Finset.mem_insert, Finset.mem_Ico, Finset.mem_Ico]
    omega
  have h_one_not_mem : (1 : ℕ) ∉ Finset.Ico 2 ((p - 1) / 2 + 1) := by
    rw [Finset.mem_Ico]; omega
  rw [h_split, Finset.prod_insert h_one_not_mem]
  rw [FLT37.realCyclotomicUnit_one]
  simp

set_option backward.isDefEq.respectTransparency false in
omit hp in
/-- **Reindex**: the product over `Fin ((p-3)/2)` indexed by `j+2`
equals the product over `Finset.Ico 2 ((p-1)/2 + 1)`. -/
theorem prod_Fin_eq_prod_Ico_two
    {β : Type*} [CommMonoid β] (hp_three : 3 ≤ p) (f : ℕ → β) :
    ∏ j : Fin ((p - 3) / 2), f ((j : ℕ) + 2) =
      ∏ b ∈ Finset.Ico 2 ((p - 1) / 2 + 1), f b := by
  -- (p-3)/2 = (p-1)/2 - 1 (when p ≥ 3 odd; for p ≥ 3 even, also ok via Nat.sub).
  -- Use Finset.prod_bij with j ↦ j + 2.
  -- Alternative: use Finset.sum_range_eq_sum_Ico-style lemmas.
  -- Direct: ∏ j : Fin n, f (j + 2) = ∏ j ∈ Finset.range n, f (j + 2)
  --         = ∏ b ∈ Finset.range n |>.image (· + 2), f b
  --         = ∏ b ∈ Finset.Ico 2 (n + 2), f b.
  rw [show ∏ j : Fin ((p - 3) / 2), f ((j : ℕ) + 2) =
        ∏ j ∈ Finset.range ((p - 3) / 2), f (j + 2) from
        (Finset.prod_range fun j => f (j + 2)).symm]
  rw [show Finset.Ico 2 ((p - 1) / 2 + 1) = Finset.Ico (0 + 2) ((p - 3) / 2 + 2) by
        congr 1
        omega]
  rw [Finset.prod_Ico_eq_prod_range]
  simp only [zero_add]
  refine Finset.prod_congr rfl fun j _ => ?_
  congr 1
  omega

set_option backward.isDefEq.respectTransparency false in
/-- **`AlgebraMapPollaczekUnitPlusKplus_eq` PROVEN**: the K⁺-side
preimage of `pollaczekUnitPlus` under `algebraMap` equals
`pollaczekUnitPlus` itself, via the family-product expression.

Direct chain:
* `pollaczekUnitPlusKplus = ∏_j family(j)^{(j+2)^exp}` (def).
* `algebraMap (∏ ...) = ∏ algebraMap (family(j))^{(j+2)^exp}` (mathlib).
* Each `algebraMap (family(j)) = realCyclotomicUnit (j+2)`
  (`algebraMap_cyclotomicUnitFamilyKplus`).
* Reindex `j ↔ b - 2` (`prod_Fin_eq_prod_Ico_two`).
* `∏_b realCyclotomicUnit(b)^{b^exp}` (over Ico 2) = `pollaczekUnitPlus`
  (`pollaczekUnitPlus_val_eq_prod_Ico_two`). -/
theorem algebraMapPollaczekUnitPlusKplus_eq (i_irreg : ℕ)
    (hp_odd : p ≠ 2) (hp_three : 3 ≤ p) :
    AlgebraMapPollaczekUnitPlusKplus_eq p K i_irreg hp_odd hp_three := by
  unfold AlgebraMapPollaczekUnitPlusKplus_eq pollaczekUnitPlusKplus
  -- LHS: algebraMap (∏_j family(j) ^ ((j+2)^...) : 𝓞 K⁺) : 𝓞 K.
  rw [Units.coe_prod, map_prod]
  -- RHS: pollaczekUnitPlus = ∏_b realCyclotomicUnit b ^ b^... over Ico 2.
  rw [pollaczekUnitPlus_val_eq_prod_Ico_two p K i_irreg hp_three]
  -- Reindex via prod_Fin_eq_prod_Ico_two on the RHS.
  rw [show (∏ b ∈ Finset.Ico 2 ((p - 1) / 2 + 1),
        FLT37.realCyclotomicUnit p K b ^ (b ^ (p - 1 - i_irreg))) =
        ∏ j : Fin ((p - 3) / 2),
          FLT37.realCyclotomicUnit p K ((j : ℕ) + 2) ^
            (((j : ℕ) + 2) ^ (p - 1 - i_irreg)) from
        (prod_Fin_eq_prod_Ico_two (p := p) hp_three
          (fun b => FLT37.realCyclotomicUnit p K b ^ (b ^ (p - 1 - i_irreg)))).symm]
  -- Now both sides indexed by Fin; match term-wise.
  -- LHS: ∏ x : Fin (rank K⁺), algebraMap (family(x) ^ ((x+2)^...)).val.
  -- RHS: ∏ j : Fin ((p-3)/2), realCyclotomicUnit (j+2) ^ ((j+2)^...).
  -- We need to relate these via the rank cast.
  -- Use Fintype.prod_equiv with the rank-cast equiv.
  have h_rank_eq :
      NumberField.Units.rank (NumberField.maximalRealSubfield K) = (p - 3) / 2 :=
    (NumberField.IsCMField.units_rank_eq_units_rank (K := K)).trans
      (BernoulliRegular.units_rank_eq_prime_sub_three_div_two (p := p) (K := K))
  rw [Fintype.prod_equiv (finCongr h_rank_eq)
        (fun x => algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)
          ((cyclotomicUnitFamilyKplusFinRank p K hp_odd hp_three x ^
              (((x : ℕ) + 2) ^ (p - 1 - i_irreg)) :
              (𝓞 (NumberField.maximalRealSubfield K))ˣ) :
              𝓞 (NumberField.maximalRealSubfield K)))
        (fun j => FLT37.realCyclotomicUnit p K ((j : ℕ) + 2) ^
          (((j : ℕ) + 2) ^ (p - 1 - i_irreg)))]
  intro x
  -- Term-wise: algebraMap (family(x) ^ ((x+2)^...)) = realCyclotomicUnit (x+2)^((x+2)^...).
  rw [Units.val_pow_eq_pow_val, map_pow]
  congr 1
  exact algebraMap_cyclotomicUnitFamilyKplus p K x hp_odd hp_three

set_option backward.isDefEq.respectTransparency false in
/-- **`PollaczekInFamily` PROVEN**: combining the algebraMap equation
with the subgroup membership. -/
theorem pollaczekInFamily (i_irreg : ℕ) (hp_odd : p ≠ 2) (hp_three : 3 ≤ p) :
    PollaczekInFamily p K i_irreg hp_odd hp_three :=
  pollaczekInFamily_of_algebraMap_eq p K i_irreg hp_odd hp_three
    (algebraMapPollaczekUnitPlusKplus_eq p K i_irreg hp_odd hp_three)

set_option backward.isDefEq.respectTransparency false in
/-- **Final synthesis: `Cor8_19Bridge` from `PollaczekForward` alone**.

Combining the proven `pollaczekInFamily` with the proven bridge
construction `cor8_19Bridge_of_pollaczekForward`, only the
`PollaczekForward` Prop remains. -/
theorem cor8_19Bridge_of_pollaczekForward_full (i : ℕ) (hp_odd : p ≠ 2)
    (hp_three : 3 ≤ p)
    (h_forward : PollaczekForward p K i hp_odd hp_three) :
    Cor8_19Bridge p K i :=
  cor8_19Bridge_of_pollaczekForward p K i hp_odd hp_three
    (pollaczekInFamily p K i hp_odd hp_three) h_forward

end Sinnott

end FLT37

end BernoulliRegular

end
