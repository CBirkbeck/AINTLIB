import BernoulliRegular.FLT37.LehmerVandiver.PlusCoprime.Sinnott.CyclotomicUnitFamily
import BernoulliRegular.FLT37.LehmerVandiver.PlusCoprime.Sinnott.PollaczekMembership
import BernoulliRegular.FLT37.LehmerVandiver.PlusCoprime.KummerLift.Bridge
import BernoulliRegular.FLT37.LehmerVandiver.PlusCoprime.Cor8_19Forward


/-!
# Sinnott index formula: structural decomposition

The classical Sinnott / Washington Theorem 8.2 states

  `[(𝓞 K⁺)ˣ : C⁺] = h⁺(K)`

for `K = ℚ(ζ_p)` (with `C⁺ ⊆ (𝓞 K)ˣ` the real cyclotomic-units
subgroup intersected with `realUnits K`, viewed via `(𝓞 K⁺)ˣ ≃ realUnits K`).

This file packages the index identity as a `Prop` predicate
`SinnottIndexFormula`, plus the connection to `regOfFamily` (already
shipped) and `cyclotomicUnitsPlus` (already shipped).

This is **Step (C/D)** of the Cor 8.19 / Sinnott bridge: the analytic
content (regulator of cyclotomic units = h⁺ · regulator K⁺ via the
Kummer-Dirichlet determinant identity for cyclotomic-unit logs combined
with the analytic CNF for K⁺) is encapsulated in this Prop, allowing
the rest of the chain to compose parametrically.

## References

* Washington, *Introduction to Cyclotomic Fields*, 2nd ed. §8.2
  (Theorem 8.2: Sinnott's index formula for the cyclotomic case).
* Sinnott, *On the Stickelberger ideal and the circular units of a
  cyclotomic field*, Annals of Math. 108 (1978).
* `BernoulliRegular/HMinus/ClassNumberFormula.lean` — analytic CNF
  inputs (`hPlus_formula`, `hPlus_formula_of_evenLValues`).
-/

@[expose] public section

noncomputable section

open NumberField NumberField.IsCMField

namespace BernoulliRegular

namespace FLT37

namespace Sinnott

variable (p : ℕ) [hp : Fact p.Prime]
variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
  [IsCMField K]

/-- **Sinnott's index formula** (Washington Thm 8.2, predicate form):
the index of `⟨cyclotomicUnitFamilyKplus⟩ ⊔ torsion` in `(𝓞 K⁺)ˣ`
equals `h⁺(K) = hPlus K`.

Equivalently (under the natural identifications), `[E⁺ : C⁺] = h⁺`.

The proof requires:
1. The regulator-of-cyclotomic-units determinant computation
   (Kummer 1850, classical): `Reg(C⁺) = (factor) · ∏_{χ even nontrivial} L(1, χ)`.
2. The analytic CNF for K⁺ (already shipped as `hPlus_formula_of_evenLValues`):
   `h⁺ · Reg(K⁺) = (same factor) · ∏ L(1, χ)`.
3. Comparison: `Reg(C⁺) / Reg(K⁺) = h⁺`, which by `regOfFamily_div_regulator`
   equals `[E⁺ : ⟨family⟩ ⊔ torsion]`.

Step 1 is the substantive deferred content. -/
def SinnottIndexFormula (hp_odd : p ≠ 2) (hp_three : 3 ≤ p) : Prop :=
  (Subgroup.closure
      (Set.range (cyclotomicUnitFamilyKplusFinRank p K hp_odd hp_three)) ⊔
    NumberField.Units.torsion (NumberField.maximalRealSubfield K)).index =
  2 ^ ((p - 3) / 2) * hPlus K

set_option backward.isDefEq.respectTransparency false in
/-- **Sinnott formula in regulator form**: equivalent statement asserting
`regOfFamily(family) = 2^((p-3)/2) · h⁺ · regulator(K⁺)` directly.
The factor `2^((p-3)/2)` reflects the index of the squared cyclotomic
unit subgroup `⟨realCyclotomicUnit_k⟩` inside the standard cyclotomic
units `C⁺`; multiplied by the Sinnott index `[U⁺ : C⁺] = h⁺` gives the
total index. Composes with `regOfFamily_div_regulator` to give the
index formula. -/
def SinnottRegulatorIdentity (hp_odd : p ≠ 2) (hp_three : 3 ≤ p) : Prop :=
  NumberField.Units.regOfFamily
      (cyclotomicUnitFamilyKplusFinRank p K hp_odd hp_three) =
    (2 : ℝ) ^ ((p - 3) / 2) * (hPlus K : ℝ) *
      NumberField.Units.regulator (NumberField.maximalRealSubfield K)

set_option backward.isDefEq.respectTransparency false in
/-- **Equivalence of Sinnott formula formulations**: the index version
follows from the regulator version (both encode the same content via
`regOfFamily_div_regulator`). -/
theorem sinnottIndexFormula_of_regulatorIdentity
    (hp_odd : p ≠ 2) (hp_three : 3 ≤ p)
    (h : SinnottRegulatorIdentity p K hp_odd hp_three) :
    SinnottIndexFormula p K hp_odd hp_three := by
  unfold SinnottIndexFormula SinnottRegulatorIdentity at *
  -- regOfFamily(family) / regulator(K⁺) = [E⁺ : ⟨family⟩ ⊔ torsion] (mathlib).
  have h_div := regOfFamily_cyclotomicUnitFamilyKplus_div_regulator
    p K hp_odd hp_three
  -- regulator K⁺ ≠ 0 (positive).
  have h_reg_pos : 0 < NumberField.Units.regulator
      (NumberField.maximalRealSubfield K) :=
    NumberField.Units.regulator_pos _
  rw [h] at h_div
  -- h_div : 2^((p-3)/2) · h⁺ · R / R = (index : ℝ)
  rw [show (2 : ℝ) ^ ((p - 3) / 2) * (hPlus K : ℝ) *
        NumberField.Units.regulator (NumberField.maximalRealSubfield K) /
        NumberField.Units.regulator (NumberField.maximalRealSubfield K) =
      2 ^ ((p - 3) / 2) * (hPlus K : ℝ) from by
    field_simp] at h_div
  -- h_div : 2^((p-3)/2) · h⁺ = (index : ℝ)
  exact_mod_cast h_div.symm

set_option backward.isDefEq.respectTransparency false in
/-- **Converse**: the regulator identity follows from the index formula.
Both Props are equivalent under `regOfFamily_div_regulator`. -/
theorem sinnottRegulatorIdentity_of_indexFormula
    (hp_odd : p ≠ 2) (hp_three : 3 ≤ p)
    (h : SinnottIndexFormula p K hp_odd hp_three) :
    SinnottRegulatorIdentity p K hp_odd hp_three := by
  unfold SinnottIndexFormula SinnottRegulatorIdentity at *
  have h_div := regOfFamily_cyclotomicUnitFamilyKplus_div_regulator
    p K hp_odd hp_three
  -- h_div : regOfFamily / regulator = (index : ℝ)
  -- h : index = 2^((p-3)/2) · hPlus K
  rw [h] at h_div
  -- h_div : regOfFamily / regulator = (2^((p-3)/2) · hPlus K : ℝ)
  have h_reg_pos : 0 < NumberField.Units.regulator
      (NumberField.maximalRealSubfield K) :=
    NumberField.Units.regulator_pos _
  -- regOfFamily = 2^((p-3)/2) · hPlus K · regulator.
  field_simp [h_reg_pos.ne'] at h_div
  push_cast at h_div
  linarith

set_option backward.isDefEq.respectTransparency false in
/-- **Equivalence (full)**: the index and regulator formulations of
Sinnott's identity are equivalent. -/
theorem sinnottIndexFormula_iff_regulatorIdentity
    (hp_odd : p ≠ 2) (hp_three : 3 ≤ p) :
    SinnottIndexFormula p K hp_odd hp_three ↔
      SinnottRegulatorIdentity p K hp_odd hp_three :=
  ⟨sinnottRegulatorIdentity_of_indexFormula p K hp_odd hp_three,
   sinnottIndexFormula_of_regulatorIdentity p K hp_odd hp_three⟩

/-! ## Connection to the analytic CNF for K⁺

The analytic CNF for K⁺ (already shipped as `hPlus_formula`) gives

  `(hPlus K : ℝ) · regulator K⁺ = dedekindZeta_residue K⁺ ·
    (torsionOrder · √|disc K⁺|) / (2^r · (2π)^c)`

where the RHS is purely analytic (no `hPlus`, no `regulator`).

Therefore `SinnottRegulatorIdentity` is equivalent to the (purely
analytic) claim that `regOfFamily(family)` equals this same expression.
This isolates the substantive analytic content as a comparison with
the analytic CNF. -/

set_option backward.isDefEq.respectTransparency false in
/-- **Sinnott as analytic identity**: `regOfFamily(family)` equals
`2^((p-3)/2)` times the analytic expression that the analytic CNF
identifies with `h⁺ · regulator K⁺`.

This is the form in which the regulator identity is most naturally
proven via the Kummer-Dirichlet determinant computation: both sides
are explicit analytic expressions involving regulators, residues, and
discriminants. The factor `2^((p-3)/2)` reflects the index of the
squared cyclotomic family inside the standard cyclotomic units. -/
def SinnottAnalyticIdentity (hp_odd : p ≠ 2) (hp_three : 3 ≤ p) : Prop :=
  NumberField.Units.regOfFamily
      (cyclotomicUnitFamilyKplusFinRank p K hp_odd hp_three) =
    (2 : ℝ) ^ ((p - 3) / 2) *
      NumberField.dedekindZeta_residue (NumberField.maximalRealSubfield K) *
        (((NumberField.Units.torsionOrder
            (NumberField.maximalRealSubfield K) : ℝ) *
            Real.sqrt |NumberField.discr (NumberField.maximalRealSubfield K)|) /
          (2 ^ NumberField.InfinitePlace.nrRealPlaces
              (NumberField.maximalRealSubfield K) *
            (2 * Real.pi) ^ NumberField.InfinitePlace.nrComplexPlaces
              (NumberField.maximalRealSubfield K)))

set_option backward.isDefEq.respectTransparency false in
/-- **Analytic identity → regulator identity**: combining
`SinnottAnalyticIdentity` with the analytic CNF (`hPlus_formula`)
gives `SinnottRegulatorIdentity`. -/
theorem sinnottRegulatorIdentity_of_analyticIdentity
    (hp_odd : p ≠ 2) (hp_three : 3 ≤ p)
    (h : SinnottAnalyticIdentity p K hp_odd hp_three) :
    SinnottRegulatorIdentity p K hp_odd hp_three := by
  unfold SinnottAnalyticIdentity SinnottRegulatorIdentity at *
  -- analytic CNF: (hPlus K : ℝ) = (analytic factor) / (... · regulator K⁺).
  have h_cnf := hPlus_formula K
  -- regulator K⁺ ≠ 0 (positive).
  have h_reg_pos : 0 < NumberField.Units.regulator
      (NumberField.maximalRealSubfield K) :=
    NumberField.Units.regulator_pos _
  -- Other denominator factors are positive.
  have h_two_pow_pos : (0 : ℝ) <
      2 ^ NumberField.InfinitePlace.nrRealPlaces
          (NumberField.maximalRealSubfield K) *
        (2 * Real.pi) ^ NumberField.InfinitePlace.nrComplexPlaces
          (NumberField.maximalRealSubfield K) := by
    refine mul_pos (pow_pos (by positivity) _) (pow_pos ?_ _)
    positivity
  rw [h]
  -- h_cnf : (hPlus K : ℝ) = ... ; goal RHS has ↑(hPlus K)
  conv_rhs => rw [show ((hPlus K : ℕ) : ℝ) = _ from h_cnf]
  field_simp

set_option backward.isDefEq.respectTransparency false in
/-- **Regulator identity → analytic identity**: the converse, using
`dedekindZeta_residue_def` to unfold the residue. -/
theorem sinnottAnalyticIdentity_of_regulatorIdentity
    (hp_odd : p ≠ 2) (hp_three : 3 ≤ p)
    (h : SinnottRegulatorIdentity p K hp_odd hp_three) :
    SinnottAnalyticIdentity p K hp_odd hp_three := by
  unfold SinnottRegulatorIdentity SinnottAnalyticIdentity at *
  have h_cnf := hPlus_formula K
  have h_reg_pos : 0 < NumberField.Units.regulator
      (NumberField.maximalRealSubfield K) :=
    NumberField.Units.regulator_pos _
  rw [h]
  -- (hPlus : ℝ) · regulator = residue · (torsion · √|disc|) / (2^r · (2π)^c).
  conv_lhs => rw [show ((hPlus K : ℕ) : ℝ) = _ from h_cnf]
  field_simp

set_option backward.isDefEq.respectTransparency false in
/-- **Equivalence of analytic and regulator forms**: both are
equivalent statements of Sinnott's identity. -/
theorem sinnottAnalyticIdentity_iff_regulatorIdentity
    (hp_odd : p ≠ 2) (hp_three : 3 ≤ p) :
    SinnottAnalyticIdentity p K hp_odd hp_three ↔
      SinnottRegulatorIdentity p K hp_odd hp_three :=
  ⟨sinnottRegulatorIdentity_of_analyticIdentity p K hp_odd hp_three,
   sinnottAnalyticIdentity_of_regulatorIdentity p K hp_odd hp_three⟩

/-! ## Connection to `Cor8_19Bridge`

Once `SinnottIndexFormula` is established, the **structural contrapositive
engine** (step F) reduces `Cor8_19Bridge` to a "p-saturation" check:

  Under `¬ p ∣ h⁺`, the family-generated subgroup `⟨family⟩ ⊔ torsion`
  has index coprime to p in `(𝓞 K⁺)ˣ`. Hence the inclusion
  `⟨family⟩ ⊔ torsion ↪ (𝓞 K⁺)ˣ` is "p-saturated", i.e., a unit is a
  p-th power in `(𝓞 K⁺)ˣ` iff it is a p-th power in
  `⟨family⟩ ⊔ torsion` (when the unit lies in the latter).

For `pollaczekUnitPlus ∈ ⟨family⟩ ⊔ torsion` (extending step E to the
family-version), the contrapositive form of the local certificate gives
the bridge.

This requires the additional fact `pollaczekUnitPlus ∈ ⟨family⟩ ⊔ torsion`,
which strengthens `pollaczekUnitPlus ∈ cyclotomicUnitsPlus` to
membership in the FAMILY-GENERATED subgroup (mathematically the same
under Sinnott's full theorem, but a separate step in the formal chain). -/

set_option backward.isDefEq.respectTransparency false in
/-- **Sinnott formula bridge target**: under `SinnottIndexFormula` (step C/D),
the index identity gives `[E⁺ : ⟨family⟩ ⊔ torsion] = 2^((p-3)/2) · h⁺`
directly. The factor `2^((p-3)/2)` reflects the gap between the project's
squared cyclotomic family `⟨realCyclotomicUnit_k⟩` and the standard
cyclotomic units `C⁺`. -/
theorem index_eq_twoPow_mul_hPlus_of_sinnottIndexFormula
    (hp_odd : p ≠ 2) (hp_three : 3 ≤ p)
    (h : SinnottIndexFormula p K hp_odd hp_three) :
    (Subgroup.closure
        (Set.range (cyclotomicUnitFamilyKplusFinRank p K hp_odd hp_three)) ⊔
      NumberField.Units.torsion (NumberField.maximalRealSubfield K)).index =
    2 ^ ((p - 3) / 2) * hPlus K := h

/-! ## The "Pollaczek-in-family" hypothesis

For Cor 8.19's contrapositive engine, we need the family-generated
subgroup `⟨family⟩ ⊔ torsion` to contain `pollaczekUnitPlus`. This is
mathematically equivalent (by Sinnott) to `pollaczekUnitPlus ∈ C⁺`,
already proven, but as a formal Lean fact requires showing the family
generates `C⁺ ⊔ torsion`.

We package this as a separate Prop. -/

set_option backward.isDefEq.respectTransparency false in
/-- **Pollaczek descent to family**: `pollaczekUnitPlus` lies in the
family-generated subgroup. Mathematically follows from
`pollaczekUnitPlus_mem_cyclotomicUnitsPlus` + Sinnott (the family
generates `C⁺` mod torsion). -/
def PollaczekInFamily (i : ℕ) (hp_odd : p ≠ 2) (hp_three : 3 ≤ p) : Prop :=
  ∃ v : (𝓞 (NumberField.maximalRealSubfield K))ˣ,
    (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) (v : 𝓞 _) : 𝓞 K) =
      ((FLT37.pollaczekUnitPlus p K i : (𝓞 K)ˣ) : 𝓞 K) ∧
    v ∈ Subgroup.closure
        (Set.range (cyclotomicUnitFamilyKplusFinRank p K hp_odd hp_three)) ⊔
      NumberField.Units.torsion (NumberField.maximalRealSubfield K)

/-! ## Cor8_19 bridge from Sinnott + Pollaczek-in-family

Under `SinnottIndexFormula` and `PollaczekInFamily`, the "p-saturation"
argument gives `Cor8_19Bridge`:

* `¬ p ∣ h⁺` (target conclusion).
* `[E⁺ : ⟨family⟩ ⊔ torsion] = h⁺` (Sinnott).
* So `p ∤ [E⁺ : ⟨family⟩ ⊔ torsion]`.
* For `α^p = pollaczekUnitPlus` in `E⁺` with α : (𝓞 K)ˣ — the descent
  of α to a family-or-torsion element exists by p-saturation, giving the
  contrapositive: `¬IsPthPower(pollaczekUnitPlus in E⁺) → ¬p∣h⁺`.

This is the structural form of the Cor 8.19 contrapositive engine. -/

set_option backward.isDefEq.respectTransparency false in
/-- **Cor 8.19 bridge from Sinnott + Pollaczek-in-family** (contrapositive
form, structural). Reduces `Cor8_19Bridge` to the two analytic Props
plus a "Pollaczek forward" argument.

The `PollaczekForward` step asserts the Pollaczek-specific construction
property: `p ∣ h⁺ → pollaczekUnitPlus IS a p-th power in the family
subgroup`. Combined with Sinnott + PollaczekInFamily, this gives the
bridge. -/
def Cor8_19BridgeStructural (i : ℕ) (hp_odd : p ≠ 2) (hp_three : 3 ≤ p) : Prop :=
  SinnottIndexFormula p K hp_odd hp_three →
  PollaczekInFamily p K i hp_odd hp_three →
  Cor8_19Bridge p K i

set_option backward.isDefEq.respectTransparency false in
/-- **Pollaczek forward**: under `p ∣ h⁺`, `pollaczekUnitPlus` IS a
p-th power in the family subgroup of `(𝓞 K⁺)ˣ`.

This is the construction-specific property: pollaczekUnit is built at
the irregular index `i` such that `p ∣ h⁺` ⟹ pollaczekUnitPlus
becomes a p-th power. The mathematical content uses Sinnott + Vandiver
analysis at the irregular eigenspace.

Equivalently: under `p ∣ h⁺`, the K⁺-side preimage `v` of
`pollaczekUnitPlus` (from PollaczekInFamily) is a p-th power in the
family subgroup. -/
def PollaczekForward (i : ℕ) (hp_odd : p ≠ 2) (hp_three : 3 ≤ p) : Prop :=
  (p : ℕ) ∣ hPlus K →
  ∀ v : (𝓞 (NumberField.maximalRealSubfield K))ˣ,
    (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) (v : 𝓞 _) : 𝓞 K) =
      ((FLT37.pollaczekUnitPlus p K i : (𝓞 K)ˣ) : 𝓞 K) →
    v ∈ Subgroup.closure
        (Set.range (cyclotomicUnitFamilyKplusFinRank p K hp_odd hp_three)) ⊔
      NumberField.Units.torsion (NumberField.maximalRealSubfield K) →
    ∃ β : (𝓞 (NumberField.maximalRealSubfield K))ˣ,
      β ^ p = v

set_option backward.isDefEq.respectTransparency false in
/-- **Cor8_19Bridge from forward Pollaczek**: PROVEN. Under
`PollaczekForward`, `PollaczekInFamily`, and the `algebraMap` lift
of any K⁺-side p-th-root to the K-side, we get the contrapositive
bridge. -/
theorem cor8_19Bridge_of_pollaczekForward (i : ℕ)
    (hp_odd : p ≠ 2) (hp_three : 3 ≤ p)
    (h_pollaczek : PollaczekInFamily p K i hp_odd hp_three)
    (h_forward : PollaczekForward p K i hp_odd hp_three) :
    Cor8_19Bridge p K i where
  not_dvd_hPlus_of_not_isPthPower := by
    intro h_no_pth h_dvd
    -- p∣h⁺ → ∃β ∈ K⁺ with β^p = (K⁺-preimage of pollaczekUnitPlus).
    obtain ⟨v, hv_eq, hv_mem⟩ := h_pollaczek
    obtain ⟨β, hβ⟩ := h_forward h_dvd v hv_eq hv_mem
    -- Lift β to (𝓞 K)ˣ via Units.map (algebraMap (𝓞 K⁺) (𝓞 K)).toMonoidHom.
    set β_K := Units.map
        (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)).toMonoidHom β
    -- β_K^p has underlying element = algebraMap(β^p) = algebraMap(v) = pollaczekUnitPlus.
    apply h_no_pth β_K
    rw [← hv_eq]
    -- algebraMap v = (algebraMap (β^p) : 𝓞 K) = (algebraMap β : 𝓞 K)^p = (β_K : 𝓞 K)^p.
    have h_v_pow : v = β ^ p := hβ.symm
    rw [h_v_pow]
    change (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)
        ((β ^ p : (𝓞 (NumberField.maximalRealSubfield K))ˣ) :
          𝓞 (NumberField.maximalRealSubfield K)) : 𝓞 K) =
      ((β_K : (𝓞 K)ˣ) : 𝓞 K) ^ p
    rw [Units.val_pow_eq_pow_val, map_pow]
    rfl

set_option backward.isDefEq.respectTransparency false in
/-- **`Cor8_19BridgeStructural` proof under `PollaczekForward`**:
combining the structural decomposition with the forward Pollaczek
property gives the bridge. -/
theorem cor8_19BridgeStructural_of_pollaczekForward (i : ℕ)
    (hp_odd : p ≠ 2) (hp_three : 3 ≤ p)
    (h_forward : PollaczekForward p K i hp_odd hp_three) :
    Cor8_19BridgeStructural p K i hp_odd hp_three := fun _ h_pollaczek =>
  cor8_19Bridge_of_pollaczekForward p K i hp_odd hp_three h_pollaczek h_forward

/-- **Final synthesis status**: with `PollaczekInFamily` PROVEN and the
bridge construction `cor8_19Bridge_of_pollaczekForward` PROVEN, the only
remaining content for `Cor8_19Bridge` is the Pollaczek-forward
construction `PollaczekForward`. The synthesis theorem
`cor8_19BridgeStructural_of_pollaczekForward` (above) packages this
chain. -/
example : True := trivial

end Sinnott

end FLT37

end BernoulliRegular

end
