import BernoulliRegular.UnitQuotient.Washington814Forward
import BernoulliRegular.CyclotomicUnits.UnitQuotientForward
import BernoulliRegular.FLT37.LehmerVandiver.PlusCoprime.Sinnott.PollaczekFamilyDescent

/-!
# Washington Theorem 8.14 forward step — the `(d)` index bridge

The eigenspace work of `Washington814Forward.lean` shows that, **assuming every even
Pollaczek class `[E_i]` (`2 ≤ i ≤ 34`) is nonzero**, the symmetrised Pollaczek classes
span the mod-37 free part `(E_K free)/37`.  This file converts that span statement into
`¬ 37 ∣ h⁺` by transporting it, via `algebraMap : 𝓞 K⁺ → 𝓞 K`, onto the real
cyclotomic-unit family that generates `C⁺ = cyclotomicUnitIndexSubgroup`.

The composite map

  `φ : (𝓞 K⁺)ˣ → (E_K free)/37`,   `φ = [algebraMap (·)]_{mod 37}`

is an additive homomorphism.  Since `pollaczekUnitPlusKplus i ∈ ⟨family⟩` and
`algebraMap (pollaczekUnitPlusKplus i) = pollaczekUnitPlus i`, the images `φ(family_j)`
span everything the symmetrised classes do — i.e. all of `(E_K free)/37` under the span
hypothesis.  Seventeen generators spanning a rank-17 space are linearly independent, which
is exactly the exponent-vanishing hypothesis of
`CPlus_pSaturated_of_generator_exponents_modP_zero`.  That yields `p`-saturation of `C⁺`,
hence `37 ∤ [E⁺ : C⁺]`, hence `37 ∤ h⁺` by Sinnott's index formula.

Crucially the span hypothesis is **not** unconditional: it carries the local certificate
(for `i = 32`) and the Bernoulli/Theorem-8.16 input (for `i ≠ 32`).  The determinant route
(`cyclotomicUnits_pSaturated_of_kummerLog_det_ne_zero`) is unavailable here because
`37 ∣ B₃₂` makes that determinant vanish; the per-eigencomponent argument below is the
irreducible replacement.

## References
* Washington, *Introduction to Cyclotomic Fields*, 2nd ed., GTM 83, §8.3 Thm 8.14.
-/

@[expose] public section

noncomputable section

open NumberField

namespace BernoulliRegular

namespace FLT37

variable {K : Type} [Field K] [NumberField K] [IsCyclotomicExtension {37} ℚ K]
  [hp37 : Fact (Nat.Prime 37)] [NumberField.IsCMField K]

local notation3 "K⁺" => NumberField.maximalRealSubfield K

/-- The composite additive homomorphism `(𝓞 K⁺)ˣ → (E_K free)/37`: push a real unit to
`K` via `algebraMap`, then take its mod-37 free-part class. -/
noncomputable def realUnitToFreePartModP :
    Additive ((𝓞 K⁺)ˣ) →+ CyclotomicUnitFreePartModP (p := 37) K :=
  (cyclotomicUnitToFreePartModPAdd (p := 37) K).comp
    (MonoidHom.toAdditive (Units.map (algebraMap (𝓞 K⁺) (𝓞 K)).toMonoidHom))

omit [NumberField K] [IsCyclotomicExtension {37} ℚ K] hp37 [IsCMField K] in
@[simp]
theorem realUnitToFreePartModP_apply (u : (𝓞 K⁺)ˣ) :
    realUnitToFreePartModP (K := K) (Additive.ofMul u) =
      cyclotomicUnitToFreePartModPAdd (p := 37) K
        (Additive.ofMul (Units.map (algebraMap (𝓞 K⁺) (𝓞 K)).toMonoidHom u)) :=
  rfl

/-- **φ of the K⁺-side symmetrised Pollaczek unit is twice the bare class.**
`algebraMap (pollaczekUnitPlusKplus i) = pollaczekUnitPlus i`
(`algebraMapPollaczekUnitPlusKplus_eq`), so `φ(pollaczekUnitPlusKplus i)` is the mod-37
free-part class of `pollaczekUnitPlus i`, which is `2 • [pollaczekUnit i]`. -/
theorem realUnitToFreePartModP_pollaczekUnitPlusKplus (i : ℕ) :
    realUnitToFreePartModP (K := K)
        (Additive.ofMul (Sinnott.pollaczekUnitPlusKplus 37 K i (by norm_num) (by norm_num))) =
      (2 : ℕ) • cyclotomicUnitToFreePartModPAdd (p := 37) K
        (Additive.ofMul (pollaczekUnit 37 K i)) := by
  rw [realUnitToFreePartModP_apply]
  rw [show Units.map (algebraMap (𝓞 K⁺) (𝓞 K)).toMonoidHom
        (Sinnott.pollaczekUnitPlusKplus 37 K i (by norm_num) (by norm_num)) =
      pollaczekUnitPlus 37 K i from ?_]
  · exact pollaczekUnitPlus_class_eq_two_smul_pollaczekUnit_class_in_modp_freepart_general i
  · apply Units.ext
    rw [Units.coe_map]
    exact Sinnott.algebraMapPollaczekUnitPlusKplus_eq 37 K i (by norm_num) (by norm_num)

omit [NumberField K] [IsCyclotomicExtension {37} ℚ K] [IsCMField K] in
/-- **φ kills the sign generator.** `-1` is 2-torsion, and `2` is invertible mod 37, so
its mod-37 free-part class vanishes. -/
theorem realUnitToFreePartModP_neg_one :
    realUnitToFreePartModP (K := K) (Additive.ofMul (-1 : (𝓞 K⁺)ˣ)) = 0 := by
  have h2ne : (2 : ZMod 37) ≠ 0 := by
    rw [show (2 : ZMod 37) = ((2 : ℕ) : ZMod 37) from by push_cast; ring,
      show (0 : ZMod 37) = ((0 : ℕ) : ZMod 37) from by push_cast; ring, Ne,
      ZMod.natCast_eq_natCast_iff]
    decide
  have h2 : (2 : ℕ) • realUnitToFreePartModP (K := K) (Additive.ofMul (-1 : (𝓞 K⁺)ˣ)) = 0 := by
    rw [← map_nsmul, ← ofMul_pow, neg_one_sq, ofMul_one, map_zero]
  have h2' : (2 : ZMod 37) •
      realUnitToFreePartModP (K := K) (Additive.ofMul (-1 : (𝓞 K⁺)ˣ)) = 0 := by
    rw [show (2 : ZMod 37) = ((2 : ℕ) : ZMod 37) from by push_cast; ring,
      Nat.cast_smul_eq_nsmul]
    exact h2
  exact (smul_eq_zero.mp h2').resolve_left h2ne

/-- **φ of a `CPlusExponentProduct` is the integer combination of the generator images.**
The sign factor `(-1)^s` dies (φ kills `-1`); each `CPlusGenerator_a ^ (e a)` contributes
`e a • φ(CPlusGenerator_a)`. -/
theorem realUnitToFreePartModP_CPlusExponentProduct (s : ℤ)
    (e : Fin ((37 - 3) / 2) → ℤ) :
    realUnitToFreePartModP (K := K)
        (Additive.ofMul (CPlusExponentProduct (p := 37) (K := K) (by norm_num) s e)) =
      ∑ a : Fin ((37 - 3) / 2), e a • realUnitToFreePartModP (K := K)
        (Additive.ofMul (CPlusGenerator (p := 37) (K := K) (by norm_num) a)) := by
  unfold CPlusExponentProduct
  rw [ofMul_mul, map_add, ofMul_zpow, map_zsmul, realUnitToFreePartModP_neg_one,
    zsmul_zero, zero_add, ofMul_prod, map_sum]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [ofMul_zpow, map_zsmul]

/-- **φ maps `C⁺` into the span of the generator images.** Every `C⁺` element is a
`CPlusExponentProduct`, whose φ-image is an integer combination of the `φ(CPlusGenerator_a)`. -/
theorem realUnitToFreePartModP_mem_span_of_mem_CPlus (u : (𝓞 K⁺)ˣ)
    (hu : u ∈ CPlus (p := 37) (K := K) (by norm_num)) :
    realUnitToFreePartModP (K := K) (Additive.ofMul u) ∈
      Submodule.span (ZMod 37) (Set.range (fun a : Fin ((37 - 3) / 2) =>
        realUnitToFreePartModP (K := K)
          (Additive.ofMul (CPlusGenerator (p := 37) (K := K) (by norm_num) a)))) := by
  obtain ⟨s, e, hse⟩ :=
    exists_CPlusExponentProduct_of_mem_CPlus (p := 37) (K := K) (by norm_num) hu
  rw [← hse, realUnitToFreePartModP_CPlusExponentProduct]
  exact Submodule.sum_mem _
    (fun a _ => zsmul_mem (Submodule.subset_span (Set.mem_range_self a)) (e a))

/-- **WF-814b (d) span transfer: the generator images span the mod-37 free part** (under the
all-components-nonzero hypothesis). Each bare class `[pollaczekUnit_{2k+2}]` equals
`2⁻¹ · φ(pollaczekUnitPlusKplus_{2k+2})`, which lies in `span{φ(CPlusGenerator_a)}` because
`pollaczekUnitPlusKplus ∈ C⁺`; and those bare classes span everything by `(b)`. -/
theorem CPlusGenerator_image_span_eq_top
    (h_all : ∀ i : ℕ, Even i → 2 ≤ i → i ≤ 34 →
      cyclotomicUnitFreePartModPClass (p := 37) K
        (Additive.ofMul (cyclotomicUnitFreeClass K (pollaczekUnit 37 K i))) ≠ 0) :
    Submodule.span (ZMod 37) (Set.range (fun a : Fin ((37 - 3) / 2) =>
      realUnitToFreePartModP (K := K)
        (Additive.ofMul (CPlusGenerator (p := 37) (K := K) (by norm_num) a)))) = ⊤ := by
  have h2ne : (2 : ZMod 37) ≠ 0 := by
    rw [show (2 : ZMod 37) = ((2 : ℕ) : ZMod 37) from by push_cast; ring,
      show (0 : ZMod 37) = ((0 : ℕ) : ZMod 37) from by push_cast; ring, Ne,
      ZMod.natCast_eq_natCast_iff]
    decide
  apply le_antisymm le_top
  rw [← pollaczekUnit_image_span_eq_top (K := K) h_all]
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨k, rfl⟩
  simp only []
  rw [← cyclotomicUnitToFreePartModPAdd_apply]
  have hmem : Sinnott.pollaczekUnitPlusKplus 37 K (2 * (k : ℕ) + 2) (by norm_num) (by norm_num) ∈
      CPlus (p := 37) (K := K) (by norm_num) := by
    rw [← cyclotomicUnitIndexSubgroup_eq_CPlus (p := 37) (K := K) (by norm_num) (by norm_num)]
    exact Sinnott.pollaczekUnitPlusKplus_mem 37 K (2 * (k : ℕ) + 2) (by norm_num) (by norm_num)
  have hspan := realUnitToFreePartModP_mem_span_of_mem_CPlus
    (Sinnott.pollaczekUnitPlusKplus 37 K (2 * (k : ℕ) + 2) (by norm_num) (by norm_num)) hmem
  rw [realUnitToFreePartModP_pollaczekUnitPlusKplus] at hspan
  rw [show cyclotomicUnitToFreePartModPAdd (p := 37) K
        (Additive.ofMul (pollaczekUnit 37 K (2 * (k : ℕ) + 2))) =
      (2⁻¹ : ZMod 37) • ((2 : ℕ) • cyclotomicUnitToFreePartModPAdd (p := 37) K
        (Additive.ofMul (pollaczekUnit 37 K (2 * (k : ℕ) + 2)))) from ?_]
  · exact Submodule.smul_mem _ _ hspan
  · rw [← Nat.cast_smul_eq_nsmul (ZMod 37), smul_smul,
      show ((2 : ℕ) : ZMod 37) = (2 : ZMod 37) from by push_cast; ring,
      inv_mul_cancel₀ h2ne, one_smul]

/-- **WF-814b (d): the generator images are linearly independent** (under the
all-components-nonzero hypothesis). They span a 17-dimensional space and there are exactly
`(37-3)/2 = 17` of them, so spanning forces independence. -/
theorem CPlusGenerator_image_linearIndependent
    (h_all : ∀ i : ℕ, Even i → 2 ≤ i → i ≤ 34 →
      cyclotomicUnitFreePartModPClass (p := 37) K
        (Additive.ofMul (cyclotomicUnitFreeClass K (pollaczekUnit 37 K i))) ≠ 0) :
    LinearIndependent (ZMod 37) (fun a : Fin ((37 - 3) / 2) =>
      realUnitToFreePartModP (K := K)
        (Additive.ofMul (CPlusGenerator (p := 37) (K := K) (by norm_num) a))) := by
  apply linearIndependent_of_top_le_span_of_card_eq_finrank
  · exact (CPlusGenerator_image_span_eq_top h_all).ge
  · rw [Fintype.card_fin, cyclotomicUnitFreePartModP_finrank_eq (p := 37) (K := K)
      (by norm_num : (2 : ℕ) < 37)]

/-- **WF-814b (d): the generator exponent-vanishing condition for 37**, under the
all-components-nonzero hypothesis. This is exactly the hypothesis of
`CPlus_pSaturated_of_generator_exponents_modP_zero`. A 37-th-power `CPlusExponentProduct`
has vanishing φ-image (37-torsion); expanding via the generators and applying their linear
independence forces every exponent to vanish mod 37. -/
theorem flt37_CPlusGenerator_exponents_modP_zero
    (h_all : ∀ i : ℕ, Even i → 2 ≤ i → i ≤ 34 →
      cyclotomicUnitFreePartModPClass (p := 37) K
        (Additive.ofMul (cyclotomicUnitFreeClass K (pollaczekUnit 37 K i))) ≠ 0)
    (s : ℤ) (e : Fin ((37 - 3) / 2) → ℤ)
    (hpow : CPlusExponentProduct (p := 37) (K := K) (by norm_num) s e ∈
        pPowerSubgroup (EPlus (K := K)) 37) :
    ∀ a, (e a : ZMod 37) = 0 := by
  have hφ0 : realUnitToFreePartModP (K := K)
      (Additive.ofMul (CPlusExponentProduct (p := 37) (K := K) (by norm_num) s e)) = 0 := by
    obtain ⟨w, _, hw37⟩ := hpow
    rw [← hw37, ofMul_pow, map_nsmul, ← Nat.cast_smul_eq_nsmul (ZMod 37),
      ZMod.natCast_self, zero_smul]
  rw [realUnitToFreePartModP_CPlusExponentProduct] at hφ0
  simp_rw [← Int.cast_smul_eq_zsmul (ZMod 37)] at hφ0
  exact Fintype.linearIndependent_iff.mp (CPlusGenerator_image_linearIndependent h_all)
    (fun a => (e a : ZMod 37)) hφ0

/-- **WF-814b (d): `¬ 37 ∣ h⁺` from all even Pollaczek classes nonzero.** The generator
exponent-vanishing condition gives `p`-saturation of `C⁺` in `E⁺`, hence `37 ∤ [E⁺ : C⁺]`,
hence `37 ∤ h⁺` by Sinnott's index formula. (Not unconditional: `h_all` carries the local
certificate at `i = 32` and the Theorem-8.16/Bernoulli input at `i ≠ 32`.) -/
theorem flt37_not_dvd_hPlus_of_pollaczekUnit_classes_ne_zero
    (h_all : ∀ i : ℕ, Even i → 2 ≤ i → i ≤ 34 →
      cyclotomicUnitFreePartModPClass (p := 37) K
        (Additive.ofMul (cyclotomicUnitFreeClass K (pollaczekUnit 37 K i))) ≠ 0) :
    ¬ (37 : ℕ) ∣ hPlus K := by
  have hdet : FLT37.Sinnott.KummerDirichletDeterminant 37 K (by norm_num) (by norm_num) :=
    kummerDirichletDeterminant_of_deletedFourier (p := 37) (K := K)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hsat : pSaturated (CPlus (p := 37) (K := K) (by norm_num)) (EPlus (K := K)) 37 :=
    CPlus_pSaturated_of_generator_exponents_modP_zero (p := 37) (K := K) (by norm_num)
      (by norm_num) (fun s e hpow => flt37_CPlusGenerator_exponents_modP_zero h_all s e hpow)
  have hidx : ¬ (37 : ℕ) ∣
      (cyclotomicUnitIndexSubgroup (p := 37) (K := K) (by norm_num) (by norm_num)).index := by
    rw [cyclotomicUnitIndexSubgroup_eq_CPlus (p := 37) (K := K) (by norm_num) (by norm_num)]
    exact not_dvd_index_of_pSaturated (p := 37) (K := K) (by norm_num) hsat
  exact (not_dvd_cyclotomicUnitIndex_iff_not_dvd_hPlus_of_kummerDirichletDeterminant
    (p := 37) (K := K) (by norm_num) (by norm_num) hdet).mp hidx

end FLT37

end BernoulliRegular

end
