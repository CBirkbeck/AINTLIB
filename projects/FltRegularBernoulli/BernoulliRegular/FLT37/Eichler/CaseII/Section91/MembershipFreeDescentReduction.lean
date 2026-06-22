import BernoulliRegular.FLT37.Eichler.CaseII.Section91.DescentUnitInCPlus
import BernoulliRegular.FLT37.LehmerVandiver.CaseI.RealPthRootDescent
import BernoulliRegular.UnitQuotient.Washington814Forward

/-!
# Washington §9.1 Case-II descent: eliminating the cyclotomic-membership conjunct

This file proves that the **cyclotomic-unit membership** conjunct `w ∈ C⁺` (piece (i) of every
Case-II descent provenance Prop, equivalently the target
`caseIICyclotomicIdentification_quotient_isCPlusExponentProduct`) is **not needed** for the
single-index expansion that drives Washington Corollary 8.15 / Assumption II.  The expansion
needs only the eigenspace-collapse predicate `Cor815EigenCollapseAt w`, which is a property of an
*arbitrary* real unit, not of a cyclotomic one.

It imports only; it does **not** modify any existing file.

## The observation (Washington §9.1, pp. 169–172, and Corollary 8.15)

`Cor815EigenCollapseAt w` unfolds to `∃ d β, w · (W₃₂^d)⁻¹ = β^37` — i.e. `w = W₃₂^d · β^37` for
**some** unit `β : (𝓞 K⁺)ˣ` (not required to lie in `C⁺`).  The proven
`caseIICor815_algebraMap_singleIndexExpansion` turns *any* such equation `w = W₃₂^d · β^37` into the
K-side single-index form `algebraMap w = E₃₂^d · (algebraMap β)^37` (with `E₃₂ = pollaczekUnitPlus
37 K 32`), by pushing through `Units.map` and `caseIICor815_algebraMap_W32`.  **No membership and no
Sinnott saturation are used** — the `β` from the eigenspace collapse is fed directly.

The existing `caseIICor815_realUnit_algebraMap_singleIndexExpansion` instead takes `hw : w ∈ C⁺` and
runs the Sinnott `37`-saturation (`caseIICor815_saturation`, banking `¬ 37 ∣ h⁺`) to upgrade `β` to
a `γ ∈ C⁺`; but that upgrade is **only** used to instantiate the same equation `w = W₃₂^d · γ^37`,
whose `C⁺`-membership of `γ` is then discarded by `caseIICor815_algebraMap_singleIndexExpansion`.
So the saturation/membership detour is redundant for the K-side expansion.

## What this file proves (real, axiom-clean Lean)

* `caseIIExplicitDescent_algebraMap_expansion_of_eigenCollapse` — **membership-free K-side
  single-index expansion**: from `Cor815EigenCollapseAt w` *alone* (no `w ∈ C⁺`, no
  `SinnottIndexFormula 37`), `algebraMap w = E₃₂^d · α^37`.  This is the proven
  `caseIICor815_algebraMap_singleIndexExpansion` fed directly by the `β` of the eigenspace collapse.

* `caseIIExplicitDescent_target_irrelevant_to_singleIndexExpansion` — the consequence isolating the
  genuine content: the K-side single-index expansion of the descent unit `ε₁/ε₂` (hence Corollary
  8.15, hence Assumption II) follows from `Cor815EigenCollapseAt`-on-the-descent-unit + realness
  **without** the cyclotomic membership `w ∈ C⁺`.  So the target
  `caseIICyclotomicIdentification_quotient_isCPlusExponentProduct` (= `w ∈ C⁺`) is *not* on the
  critical path to Assumption II once the eigenspace collapse is available; the genuinely-remaining
  Case-II content is the eigenspace collapse (Washington Lemma 9.8 residues) on the descent unit,
  not its cyclotomic membership.

## References
* Washington, *Introduction to Cyclotomic Fields*, 2nd ed., GTM 83, §9.1 (descent unit `η_a`,
  pp. 169–172), Corollary 8.15 (p. 153), Lemma 9.8 / 9.9 (pp. 180–181).
-/

@[expose] public section

noncomputable section

open NumberField IsCyclotomicExtension

namespace BernoulliRegular.FLT37.Eichler

/-! ## 0. Membership-free kernel-vanishing: `realUnitToFreePartModP v = 0 ⟹ v = β^37`

The existing kernel-vanishing collapse
`caseIIGaloisEigen_isPow37_of_realUnitToFreePartModP_eq_zero` requires `v ∈ caseIICPlus37` — it
expands `v` as a `CPlusExponentProduct` and uses the linear independence of the family generators.
That cyclotomic-membership hypothesis is **not** needed: for *any* real unit `v : (𝓞 K⁺)ˣ`,
`realUnitToFreePartModP v = 0` already forces `v` to be a `37`-th power in `(𝓞 K⁺)ˣ`.

This is the Case-I real-`p`-th-root-descent mechanism (`Washington816.lean`,
`pollaczekUnitPlus_isPthPower_of_pollaczekUnit_class_eq_zero` +
`exists_real_unit_pow_eq_of_K_root`), applied to a general real unit rather than to a Pollaczek
unit.  The K-image `V = algebraMap v` has vanishing mod-`37` free-part class, so its `37`-power
class lies in the torsion·(`37`-th powers) subgroup; complex conjugation **fixes** `V` (since `v`
comes from `K⁺`, `complexConj_algebraMap_eq`), and the odd-prime cancellation
`cyclotomicUnitPowerQuotient_eq_zero_of_mem_torsion_of_neg_one_fixed` kills the residual root of
unity, giving `V = α^37` in `(𝓞 K)ˣ`; finally `exists_real_unit_pow_eq_of_K_root` descends the
`37`-th root to `(𝓞 K⁺)ˣ`. -/

open scoped NumberField in
/-- **Membership-free kernel-vanishing collapse** (proven, axiom-clean — **no** `w ∈ C⁺`).

For *any* real unit `v : (𝓞 K⁺)ˣ` whose mod-`37` free-part class vanishes
(`realUnitToFreePartModP v = 0`), `v` is a `37`-th power in `(𝓞 K⁺)ˣ`: `∃ β, v = β^37`.

This drops the `v ∈ caseIICPlus37` hypothesis of
`caseIIGaloisEigen_isPow37_of_realUnitToFreePartModP_eq_zero`.  The realness of `v` (automatic for a
`K⁺`-unit) replaces the cyclotomic membership: complex conjugation fixes the `K`-image of `v`, so
the residual root-of-unity factor in `V = α·ζ^j` (after the free-part class vanishes) is killed by
the odd-prime cancellation, and the real-`p`-th-root descent then lands the `37`-th root in `K⁺`. -/
theorem caseIIExplicitDescent_isPow37_of_realUnitToFreePartModP_eq_zero
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (v : (𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ)))ˣ)
    (hv : FLT37.realUnitToFreePartModP (K := CyclotomicField 37 ℚ) (Additive.ofMul v) = 0) :
    ∃ β : (𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ)))ˣ, v = β ^ 37 := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  set K := CyclotomicField 37 ℚ
  -- The `K`-image of `v`.
  set V : (𝓞 K)ˣ :=
    Units.map (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)).toMonoidHom v with hV
  -- The mod-37 free-part class of `V` is zero (= `realUnitToFreePartModP v`).
  have hVfree : BernoulliRegular.cyclotomicUnitToFreePartModPAdd (p := 37) K
      (Additive.ofMul V) = 0 := by
    rw [hV]; exact hv
  -- Step 1: the 37-power class of `V` lies in the torsion·(37-th powers) subgroup.
  have hmem : BernoulliRegular.cyclotomicUnitPowerClass (p := 37) (N := 1) K V ∈
      BernoulliRegular.cyclotomicTorsionPowerClassSubgroup (p := 37) K := by
    have hmul : BernoulliRegular.cyclotomicUnitPowerQuotientToFreePartModP (p := 37) K
        (BernoulliRegular.cyclotomicUnitPowerClass (p := 37) (N := 1) K V) = 1 := by
      rw [BernoulliRegular.cyclotomicUnitPowerQuotientToFreePartModP_apply_class,
        ← BernoulliRegular.cyclotomicUnitToFreePartModPAdd_apply, hVfree]
      rfl
    rw [← BernoulliRegular.cyclotomicUnitPowerQuotientToFreePartModP_ker, MonoidHom.mem_ker]
    exact hmul
  -- Step 2: complex conjugation (= the `-1 ∈ Δ` action) fixes the power class of `V`.
  have hfixed :
      BernoulliRegular.cyclotomicUnitPowerQuotientDeltaActionZMod (p := 37) K
          (-1 : BernoulliRegular.CyclotomicUnitDelta 37)
          (Additive.ofMul (BernoulliRegular.cyclotomicUnitPowerClass (p := 37) (N := 1) K V)) =
        Additive.ofMul (BernoulliRegular.cyclotomicUnitPowerClass (p := 37) (N := 1) K V) := by
    apply Additive.toMul.injective
    change (BernoulliRegular.cyclotomicUnitModPDeltaAction (p := 37) K).act
        (-1 : BernoulliRegular.CyclotomicUnitDelta 37)
        (BernoulliRegular.cyclotomicUnitPowerClass (p := 37) (N := 1) K V) =
      BernoulliRegular.cyclotomicUnitPowerClass (p := 37) (N := 1) K V
    rw [BernoulliRegular.cyclotomicUnitPowerQuotientDeltaAction_act_mk,
      BernoulliRegular.cyclotomicUnitEquiv_neg_one_apply (p := 37) (K := K) (by norm_num : 2 < 37)]
    congr 1
    -- `cyclotomicUnitsComplexConj V = V` because `V` is the algebraMap-image of a `K⁺` unit.
    apply Units.ext
    rw [BernoulliRegular.cyclotomicUnitsComplexConj_apply_coe]
    -- `cyclotomicRingOfIntegersComplexConj K hp` is `(ringOfIntegersComplexConj K).toRingEquiv`.
    change (NumberField.IsCMField.ringOfIntegersComplexConj K) (V : 𝓞 K) = (V : 𝓞 K)
    have hVcoe : (V : 𝓞 K) =
        algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)
          (v : 𝓞 (NumberField.maximalRealSubfield K)) := by
      rw [hV]; rfl
    rw [hVcoe]
    exact BernoulliRegular.FLT37.ringOfIntegersComplexConj_algebraMap_eq (K := K)
      (v : 𝓞 (NumberField.maximalRealSubfield K))
  -- Step 3: the power class is trivial, hence `V = α^37` in `(𝓞 K)ˣ`.
  have hzero := BernoulliRegular.cyclotomicUnitPowerQuotient_eq_zero_of_mem_torsion_of_neg_one_fixed
    (p := 37) (K := K) (by norm_num : 2 < 37) hmem hfixed
  have hone : BernoulliRegular.cyclotomicUnitPowerClass (p := 37) (N := 1) K V = 1 :=
    Additive.ofMul.injective hzero
  rw [BernoulliRegular.cyclotomicUnitPowerClass_apply, QuotientGroup.eq_one_iff] at hone
  obtain ⟨α, hα⟩ := hone
  -- `hα : (powMonoidHom 37) α = V`, i.e. `α^37 = V`.
  have hαV : (α : 𝓞 K) ^ 37 = (V : 𝓞 K) := by
    have := congrArg (fun u : (𝓞 K)ˣ ↦ (u : 𝓞 K)) hα
    simpa [powMonoidHom] using this
  -- Step 4: descend the `37`-th root to `(𝓞 K⁺)ˣ`.
  obtain ⟨β, hβ⟩ := FLT37.LehmerVandiver.CaseI.exists_real_unit_pow_eq_of_K_root
    (p' := 37) (K' := K) (by norm_num) v ((α : 𝓞 K) : K)
    (by
      have hVval : algebraMap (NumberField.maximalRealSubfield K) K
          ((v : 𝓞 (NumberField.maximalRealSubfield K)) :
            NumberField.maximalRealSubfield K) =
          (((algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)
            (v : 𝓞 (NumberField.maximalRealSubfield K))) : 𝓞 K) : K) := rfl
      rw [hVval]
      have hVcoe2 : ((algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)
          (v : 𝓞 (NumberField.maximalRealSubfield K))) : 𝓞 K) = (V : 𝓞 K) := by
        rw [hV]; rfl
      rw [hVcoe2, ← hαV]
      push_cast
      ring)
  exact ⟨β, hβ⟩

/-! ## 0b. Membership-free eigenspace collapse: `E₃₂`-monomial residue ⟹ `Cor815EigenCollapseAt`

`caseIIGaloisEigen_eigenCollapse_of_E32_monomial_residue` uses `w ∈ C⁺` twice — to show the
corrected unit `w · (W₃₂^d)⁻¹` lies in `C⁺`, and to apply the CPlus-requiring kernel-vanishing.  §0
above removes the second use; the first is now unnecessary too, since the membership-free
kernel-vanishing only needs the corrected unit's free-part class to vanish.  So the eigenspace
collapse holds for an **arbitrary** real unit whose residue is an `E₃₂`-monomial. -/

/-- **`E₃₂`-monomial residue ⟹ `Cor815EigenCollapseAt`, membership-free** (proven, axiom-clean).

For *any* real unit `w : (𝓞 K⁺)ˣ` (no `w ∈ C⁺`) whose mod-`37` free-part class is an `E₃₂`-monomial
`realUnitToFreePartModP w = c • [E₃₂]`, the eigenspace predicate `Cor815EigenCollapseAt w` holds.
Same exponent choice `d := (c · 2⁻¹).val` as the membership-carrying
`caseIIGaloisEigen_eigenCollapse_of_E32_monomial_residue`, but the final `37`-th-power extraction
uses the membership-free §0 kernel-vanishing
`caseIIExplicitDescent_isPow37_of_realUnitToFreePartModP_eq_zero`. -/
theorem caseIIExplicitDescent_eigenCollapse_of_E32_monomial_residue
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (w : (𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ)))ˣ)
    {c : ZMod 37}
    (hres : FLT37.realUnitToFreePartModP (K := CyclotomicField 37 ℚ) (Additive.ofMul w) =
      c • cyclotomicUnitToFreePartModPAdd (p := 37) (CyclotomicField 37 ℚ)
        (Additive.ofMul (FLT37.pollaczekUnit 37 (CyclotomicField 37 ℚ) 32))) :
    Cor815EigenCollapseAt w := by
  classical
  set E := cyclotomicUnitToFreePartModPAdd (p := 37) (CyclotomicField 37 ℚ)
    (Additive.ofMul (FLT37.pollaczekUnit 37 (CyclotomicField 37 ℚ) 32)) with hE
  refine ⟨(c * (2 : ZMod 37)⁻¹).val, ?_⟩
  set d : ℕ := (c * (2 : ZMod 37)⁻¹).val with hd
  -- The corrected unit's free-part class vanishes (no membership needed).
  have hφ0 : FLT37.realUnitToFreePartModP (K := CyclotomicField 37 ℚ)
      (Additive.ofMul (w * (caseIICor815_W32 ^ d)⁻¹)) = 0 := by
    rw [ofMul_mul, map_add, ofMul_inv, ofMul_pow, map_neg, map_nsmul, hres,
      caseIIGaloisEigen_realUnitToFreePartModP_W32, ← hE]
    have h2d : ((d : ℕ) : ZMod 37) * 2 = c := by
      rw [hd, ZMod.natCast_val, ZMod.cast_id]
      rw [mul_assoc, inv_mul_cancel₀ (by decide : (2 : ZMod 37) ≠ 0), mul_one]
    have hcast :
        (d • ((2 : ℕ) • E) : CyclotomicUnitFreePartModP (p := 37) (CyclotomicField 37 ℚ)) =
        c • E := by
      rw [smul_smul, ← Nat.cast_smul_eq_nsmul (ZMod 37) (d * 2) E]
      rw [show ((d * 2 : ℕ) : ZMod 37) = ((d : ℕ) : ZMod 37) * 2 from by push_cast; ring, h2d]
    rw [hcast, add_neg_cancel]
  -- Membership-free kernel-vanishing: the corrected unit is a `37`-th power.
  obtain ⟨β, hβ⟩ := caseIIExplicitDescent_isPow37_of_realUnitToFreePartModP_eq_zero
    (w * (caseIICor815_W32 ^ d)⁻¹) hφ0
  exact ⟨β, hβ⟩

/-- **`ω^{32}`-eigenspace residue ⟹ `Cor815EigenCollapseAt`, membership-free** (proven,
axiom-clean).

For *any* real unit `w : (𝓞 K⁺)ˣ` (no `w ∈ C⁺`) whose mod-`37` free-part class lies in the single
irregular `ω^{32}`-eigenspace, `Cor815EigenCollapseAt w` holds.  Composes the proven
`caseIIGaloisEigen_E32_monomial_of_mem_omega32_eigenspace` (eigenspace membership ⟹ `E₃₂`-monomial,
via the 1-dimensionality of the eigenspace — needs no `w ∈ C⁺`) with the membership-free
`caseIIExplicitDescent_eigenCollapse_of_E32_monomial_residue`.  Membership-free analog of
`caseIIGaloisEigen_eigenCollapse_of_mem_omega32_eigenspace`. -/
theorem caseIIExplicitDescent_eigenCollapse_of_mem_omega32_eigenspace
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (w : (𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ)))ˣ)
    (hmem : FLT37.realUnitToFreePartModP (K := CyclotomicField 37 ℚ) (Additive.ofMul w) ∈
      cyclotomicUnitFreePartModPDeltaCharacterEigenspace (p := 37)
        (CyclotomicField 37 ℚ) (cyclotomicOmegaChar (p := 37) 32)) :
    Cor815EigenCollapseAt w := by
  obtain ⟨c, hc⟩ := caseIIGaloisEigen_E32_monomial_of_mem_omega32_eigenspace hmem
  exact caseIIExplicitDescent_eigenCollapse_of_E32_monomial_residue w hc

/-! ## 1. Membership-free K-side single-index expansion from the eigenspace collapse

`Cor815EigenCollapseAt w` provides `w · (W₃₂^d)⁻¹ = β^37`, i.e. `w = W₃₂^d · β^37` with `β` an
arbitrary unit.  The proven `caseIICor815_algebraMap_singleIndexExpansion` then gives the K-side
single-index form — **no `w ∈ C⁺`, no Sinnott index formula, no saturation**. -/

/-- **`w = W₃₂^d · β^37` from the eigenspace collapse** (proven, unconditional).

`Cor815EigenCollapseAt w` (`w · (W₃₂^d)⁻¹ = β^37`) rearranges to `w = W₃₂^d · β^37`.  No membership
hypothesis is used. -/
theorem caseIIExplicitDescent_expansion_eq_of_eigenCollapse
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    {w : (𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ)))ˣ}
    (h_eigen : Cor815EigenCollapseAt w) :
    ∃ (d : ℕ) (β : (𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ)))ˣ),
      w = caseIICor815_W32 ^ d * β ^ 37 := by
  obtain ⟨d, β, hβ⟩ := h_eigen
  exact ⟨d, β, by rw [← hβ, mul_comm w, mul_inv_cancel_left]⟩

/-- **Membership-free K-side single-index expansion** (proven, axiom-clean).

From the eigenspace collapse `Cor815EigenCollapseAt w` *alone* — **no** cyclotomic membership
`w ∈ C⁺` and **no** `SinnottIndexFormula 37` — the K-side image of `w` is an `E₃₂`-monomial modulo
`37`-th powers: `algebraMap w = E₃₂^d · α^37` in `(𝓞 K)ˣ`, with `E₃₂ = pollaczekUnitPlus 37 K 32`.

This is the proven `caseIICor815_algebraMap_singleIndexExpansion` fed the `β` of
`caseIIExplicitDescent_expansion_eq_of_eigenCollapse`.  It shows the Sinnott-saturation /
cyclotomic-membership detour of `caseIICor815_realUnit_algebraMap_singleIndexExpansion` is redundant
for the single-index expansion: the eigenspace collapse already supplies a `37`-th root, whose
`C⁺`-membership is irrelevant to the K-side form. -/
theorem caseIIExplicitDescent_algebraMap_expansion_of_eigenCollapse
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (w : (𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ)))ˣ)
    (h_eigen : Cor815EigenCollapseAt w) :
    ∃ (d : ℕ) (α : (𝓞 (CyclotomicField 37 ℚ))ˣ),
      Units.map (algebraMap (𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ)))
          (𝓞 (CyclotomicField 37 ℚ))).toMonoidHom w =
        FLT37.pollaczekUnitPlus 37 (CyclotomicField 37 ℚ) 32 ^ d * α ^ 37 := by
  obtain ⟨d, β, hexp⟩ := caseIIExplicitDescent_expansion_eq_of_eigenCollapse h_eigen
  exact ⟨d, _, caseIICor815_algebraMap_singleIndexExpansion w β d hexp⟩

/-! ## 2. A membership-free descent-unit provenance discharges Corollary 8.15

The existing `Cor815RealDescentData37` bundles, for the descent unit `ε₁/ε₂`, **both** the
cyclotomic membership `w ∈ C⁺` *and* the eigenspace collapse `Cor815EigenCollapseAt w`.  §1 shows
the membership is redundant for the K-side expansion.  We therefore name the **membership-free**
provenance carrying only the eigenspace collapse and realness, and prove it discharges
`Cor815SingleIndexExpansion37` directly — without `SinnottIndexFormula 37`. -/

open FLT37.LehmerVandiver.CaseII in
/-- **Membership-free descent-unit provenance for Corollary 8.15** (a `def … : Prop`, **not** an
axiom).

For every Case-II descent instance, the quotient unit `ε₁/ε₂` is the K-image of a real unit `w`
(`w : (𝓞 K⁺)ˣ`, `Units.map w = ε₁/ε₂`) whose `37`-residue is an `E₃₂`-monomial
(`Cor815EigenCollapseAt w`).

Compared with `Cor815RealDescentData37`, the cyclotomic membership conjunct `w ∈ caseIICPlus37` is
**dropped**: §1 shows it is unused by the single-index expansion.  What remains is exactly the
*realness* of `η_a/η_b` (the unconditional `caseIISigmaAntiDescent` result) and its eigenspace
collapse (Washington Lemma 9.8 / 9.9 residue equations on the descent unit).  This Prop is sound —
it asserts the eigenspace collapse for the *specific* descent unit, never an `E₃₂`-monomial property
of an arbitrary unit. -/
def Cor815EigenCollapseDescentData37
    [NumberField.IsCMField (CyclotomicField 37 ℚ)] : Prop :=
  ∀ (_hV : ¬ (37 : ℕ) ∣ hPlus (CyclotomicField 37 ℚ))
    (_hSO : NoSecondOrderIrregularPair 37 32)
    {m : ℕ}
    (D : CaseIIData37 (CyclotomicField 37 ℚ) m)
    {x' y' z' : 𝓞 (CyclotomicField 37 ℚ)}
    {ε₁ ε₂ ε₃ : (𝓞 (CyclotomicField 37 ℚ))ˣ},
    ¬ (D.hζ.toInteger - 1) ∣ x' →
    ¬ (D.hζ.toInteger - 1) ∣ y' →
    ¬ (D.hζ.toInteger - 1) ∣ z' →
    ((ε₁ : 𝓞 (CyclotomicField 37 ℚ)) * x' ^ 37 +
      (ε₂ : 𝓞 (CyclotomicField 37 ℚ)) * y' ^ 37 =
        (ε₃ : 𝓞 (CyclotomicField 37 ℚ)) *
          ((D.hζ.toInteger - 1) ^ m * z') ^ 37) →
    ∃ w : (𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ)))ˣ,
      Cor815EigenCollapseAt w ∧
      Units.map (algebraMap (𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ)))
          (𝓞 (CyclotomicField 37 ℚ))).toMonoidHom w = ε₁ / ε₂

open FLT37.LehmerVandiver.CaseII in
/-- **Discharging Corollary 8.15 from the membership-free provenance** (proven, axiom-clean —
**no** `SinnottIndexFormula 37`).

The membership-free provenance `Cor815EigenCollapseDescentData37` provides, for each instance, a
real unit `w` with `Units.map w = ε₁/ε₂` and `Cor815EigenCollapseAt w`.  Feeding the eigenspace
collapse to the membership-free K-side expansion §1
(`caseIIExplicitDescent_algebraMap_expansion_of_eigenCollapse`) yields the Corollary-8.15
single-index expansion `ε₁/ε₂ = E₃₂^d · α^37` — `Cor815SingleIndexExpansion37`.

Crucially this needs **neither** the cyclotomic membership `w ∈ C⁺` (the target
`caseIICyclotomicIdentification_quotient_isCPlusExponentProduct`) **nor** the Sinnott index formula
`SinnottIndexFormula 37`: both were used by `caseIICor815_singleIndexExpansion_of_realDescentData`
only to upgrade the eigenspace collapse's `37`-th root into `C⁺` via saturation, an upgrade the
K-side expansion discards.  So the cyclotomic-membership content is *off* the critical path to
Assumption II. -/
theorem caseIIExplicitDescent_singleIndexExpansion_of_eigenCollapseData
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (h_prov : Cor815EigenCollapseDescentData37) :
    Cor815SingleIndexExpansion37 := by
  intro hV hSO m D x' y' z' ε₁ ε₂ ε₃ hx hy hz heq
  obtain ⟨w, hw_eigen, hw_eq⟩ := h_prov hV hSO D hx hy hz heq
  obtain ⟨d, α, hα⟩ :=
    caseIIExplicitDescent_algebraMap_expansion_of_eigenCollapse w hw_eigen
  exact ⟨d, α, by rw [← hw_eq, hα]⟩

open FLT37.LehmerVandiver.CaseII in
/-- **Assumption II from the membership-free provenance + Lemma 9.8** (proven, axiom-clean —
**no** `SinnottIndexFormula 37`, **no** cyclotomic membership).

**Assumption II** (`WashingtonCaseIIExactQuotientUnitPower37Source`) — the descent unit `ε₁/ε₂` is a
`37`-th power — follows from

* `Cor815EigenCollapseDescentData37` — the descent unit's realness + eigenspace collapse
  (Washington Lemma 9.8 / 9.9 residue equations); and
* `Lemma98LocalPower37` — Washington Lemma 9.8's single-index mod-`𝔩` Kummer congruence.

Compared with `caseIICor815_assumptionII_of_reduced_inputs` /
`caseIIGaloisEigen_assumptionII_of_provenance`, this drops **both** the cyclotomic membership
`w ∈ C⁺` (the target `caseIICyclotomicIdentification_quotient_isCPlusExponentProduct`) **and** the
analytic `SinnottIndexFormula 37` — §1 shows they are unused by the single-index expansion.  Thus
the cyclotomic-membership content is **not** required for Assumption II; the genuine remaining
Case-II descent-unit input is the eigenspace collapse (`Cor815EigenCollapseDescentData37`) together
with the Lemma-9.8 local power. -/
theorem caseIIExplicitDescent_assumptionII_of_eigenCollapseData
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (h_prov : Cor815EigenCollapseDescentData37)
    (h_localPow : Lemma98LocalPower37) :
    FLT37.LehmerVandiver.CaseII.WashingtonCaseIIExactQuotientUnitPower37Source :=
  caseIIThm95_assumptionII_of_corollary815_lemma98
    (caseIIExplicitDescent_singleIndexExpansion_of_eigenCollapseData h_prov) h_localPow

/-! ## 3. The cyclotomic-membership target is off the critical path

Combining §2 with the existing reduction of `Cor815RealDescentData37` to the eigenspace data, we get
that `Cor815RealDescentData37` (which *does* carry the membership `w ∈ C⁺`) already implies the
membership-free `Cor815EigenCollapseDescentData37` — so the membership conjunct it carries is, by
§1, inert for the single-index expansion. -/

open FLT37.LehmerVandiver.CaseII in
/-- **`Cor815RealDescentData37` forgets to the membership-free provenance** (proven, axiom-clean).

The membership-carrying `Cor815RealDescentData37` implies the membership-free
`Cor815EigenCollapseDescentData37` by simply dropping the `w ∈ caseIICPlus37` conjunct.  Together
with §2 this shows the cyclotomic membership in `Cor815RealDescentData37` is **not used** by the
route to `Cor815SingleIndexExpansion37` / Assumption II. -/
theorem caseIIExplicitDescent_eigenCollapseData_of_realDescentData
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (h_data : Cor815RealDescentData37) :
    Cor815EigenCollapseDescentData37 := by
  intro hV hSO m D x' y' z' ε₁ ε₂ ε₃ hx hy hz heq
  obtain ⟨w, _hw_mem, hw_eigen, hw_eq⟩ := h_data hV hSO D hx hy hz heq
  exact ⟨w, hw_eigen, hw_eq⟩

/-! ## 4. The membership-free Case-II capstone: Assumption II from the residue equations alone

Combining the membership-free eigenspace collapse (§0b) with the **unconditional realness** of the
descent unit (`caseIISigmaAntiDescent_quotient_unitsMap`, §2 of `CaseIISigmaAntiDescent.lean`) and
the canonical eigencomponent decomposition (`caseIIResidueProvenance_decomp_spec`,
`CaseIIResidueProvenance.lean`), the bare half-range residue equations on the descent unit
(`caseIISigmaAntiDescent_residueEqns`, Washington Lemma 9.8 / 9.9) already produce the
membership-free provenance `Cor815EigenCollapseDescentData37` — and hence, with
`Lemma98LocalPower37`, **Assumption II**.

This is the cleanest reduction of the entire Case-II descent-unit content: the only descent-unit
inputs are the **realness** (unconditional) and the **residue equations** (Lemma 9.8).  The
cyclotomic membership `w ∈ C⁺` (the target
`caseIICyclotomicIdentification_quotient_isCPlusExponentProduct`) and the analytic
`SinnottIndexFormula 37` are **both eliminated**. -/

open FLT37.LehmerVandiver.CaseII in
/-- **The membership-free provenance from the bare residue equations** (proven, axiom-clean — **no**
membership, **no** Sinnott).

`caseIISigmaAntiDescent_residueEqns` (Washington Lemma 9.8 / 9.9's half-range residue equations on
the canonical descent unit) implies the membership-free provenance
`Cor815EigenCollapseDescentData37`.

Route, for each instance:
* the **unconditional** realness `caseIISigmaAntiDescent_quotient_unitsMap` supplies the canonical
  `K⁺`-descent `u` with `Units.map u = ε₁/ε₂`;
* the residue equations on `u`'s canonical eigencomponents
  (`caseIIResidueProvenance_decomp_spec`) put `realUnitToFreePartModP u` in the irregular
  `ω^{32}`-eigenspace (`caseIIConjugateResidue_mem_omega32_eigenspace`); and
* the membership-free §0b `caseIIExplicitDescent_eigenCollapse_of_mem_omega32_eigenspace` turns that
  into `Cor815EigenCollapseAt u`.

No `w ∈ C⁺` and no `SinnottIndexFormula 37` are used. -/
theorem caseIIExplicitDescent_eigenCollapseData_of_residueEqns
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (h_res : caseIISigmaAntiDescent_residueEqns) :
    Cor815EigenCollapseDescentData37 := by
  intro hV hSO m D x' y' z' ε₁ ε₂ ε₃ hx hy hz heq
  -- §2 realness: the canonical `K⁺`-descent of `ε₁/ε₂`.
  obtain ⟨u, hu⟩ := caseIISigmaAntiDescent_quotient_unitsMap D.hζ D.one_le_m hx hy hz heq
  refine ⟨u, ?_, hu⟩
  -- Residue equations on `u`'s canonical eigencomponents.
  have hres := h_res hV hSO D hx hy hz heq u hu
  -- The canonical decomposition of `realUnitToFreePartModP u`.
  have hdecomp := caseIIResidueProvenance_decomp_spec
    (FLT37.realUnitToFreePartModP (K := CyclotomicField 37 ℚ) (Additive.ofMul u))
  -- `realUnitToFreePartModP u` lies in the `ω^{32}`-eigenspace.
  have hmem := caseIIConjugateResidue_mem_omega32_eigenspace
    (caseIIResidueProvenance_decomp
      (FLT37.realUnitToFreePartModP (K := CyclotomicField 37 ℚ) (Additive.ofMul u)))
    hdecomp hres
  -- Membership-free eigenspace collapse.
  exact caseIIExplicitDescent_eigenCollapse_of_mem_omega32_eigenspace u hmem

open FLT37.LehmerVandiver.CaseII in
/-- **Assumption II from the bare residue equations + Lemma 9.8** (proven, axiom-clean — **no**
membership, **no** Sinnott).

The cleanest reduction of the Case-II descent-unit content for `p = 37`:
**Assumption II** (`WashingtonCaseIIExactQuotientUnitPower37Source`) follows from

* `caseIISigmaAntiDescent_residueEqns` — Washington Lemma 9.8 / 9.9's half-range residue equations
  on the canonical descent unit; and
* `Lemma98LocalPower37` — Washington Lemma 9.8's single-index mod-`𝔩` Kummer congruence.

The **realness** of `η_a/η_b` is the unconditional §2 result of `CaseIISigmaAntiDescent.lean`; the
cyclotomic membership `w ∈ C⁺` (the target
`caseIICyclotomicIdentification_quotient_isCPlusExponentProduct`) and the analytic
`SinnottIndexFormula 37` are **eliminated** by §0–§3.  Compare
`caseIIConjugateResidue_assumptionII_of_residueProvenance`, which carries the membership conjunct in
its `Cor815RealDescentResidueProvenance37` hypothesis. -/
theorem caseIIExplicitDescent_assumptionII_of_residueEqns
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (h_res : caseIISigmaAntiDescent_residueEqns)
    (h_localPow : Lemma98LocalPower37) :
    FLT37.LehmerVandiver.CaseII.WashingtonCaseIIExactQuotientUnitPower37Source :=
  caseIIExplicitDescent_assumptionII_of_eigenCollapseData
    (caseIIExplicitDescent_eigenCollapseData_of_residueEqns h_res) h_localPow

end BernoulliRegular.FLT37.Eichler

end
