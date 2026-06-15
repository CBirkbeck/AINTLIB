import BernoulliRegular.Thaine.PollaczekUnitPlusGaloisAction.Part2

/-!
# Washington Theorem 8.14 forward step — general-index component lemmas

This file generalises the `i = 32` Pollaczek mod-`p` structural lemmas of
`Thaine/PollaczekUnitPlusGaloisAction/Part2.lean` to an arbitrary index `i`,
toward the unit-side Washington Theorem 8.14 forward step `Washington814Forward37`
(`37 ∣ h⁺ ⟹ some even `E_i` is a 37-th power`), which must handle every even
`i ∈ [2,34]`, not only the irregular index 32.

The `i = 32` proofs in `Part2.lean` are index-agnostic except for the reverse
direction of the cert equivalence (which invokes the local certificate, special
to 32). The *structural* content — that the symmetrised class is twice the bare
class, and that a 37-th power has vanishing mod-37 free-part class — holds for
every index and is recorded here.

## References
* Washington, *Introduction to Cyclotomic Fields*, 2nd ed., GTM 83, §8.3 Thm 8.14.
-/

@[expose] public section

noncomputable section

open NumberField

namespace BernoulliRegular

namespace FLT37

variable {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {37} ℚ K]
  [hp37 : Fact (Nat.Prime 37)] [NumberField.IsCMField K]

/-- **General-index form of `pollaczekUnitPlus_class_eq_two_smul_pollaczekUnit_class`.**
For every index `i`, the mod-37 free-part class of the symmetrised Pollaczek unit
`pollaczekUnitPlus 37 K i` is twice that of the bare `pollaczekUnit 37 K i`
(complex conjugation acts trivially on the free part). The proof is the `i = 32`
proof verbatim, with `32` replaced by the variable `i`. -/
theorem pollaczekUnitPlus_class_eq_two_smul_pollaczekUnit_class_in_modp_freepart_general
    (i : ℕ) :
    cyclotomicUnitToFreePartModPAdd (p := 37) K
        (Additive.ofMul (pollaczekUnitPlus 37 K i)) =
      (2 : ℕ) • cyclotomicUnitToFreePartModPAdd (p := 37) K
        (Additive.ofMul (pollaczekUnit 37 K i)) := by
  unfold pollaczekUnitPlus
  rw [ofMul_mul, map_add]
  rw [show cyclotomicUnitToFreePartModPAdd (p := 37) K
        (Additive.ofMul (NumberField.IsCMField.unitsComplexConj K
          (pollaczekUnit 37 K i))) =
      cyclotomicUnitToFreePartModPAdd (p := 37) K
        (Additive.ofMul (pollaczekUnit 37 K i)) from ?_]
  · rw [two_smul]
  · rw [cyclotomicUnitToFreePartModPAdd_apply, cyclotomicUnitToFreePartModPAdd_apply]
    have hp_two : (2 : ℕ) < 37 := by omega
    rw [show Additive.ofMul (cyclotomicUnitFreeClass K
            (NumberField.IsCMField.unitsComplexConj K (pollaczekUnit 37 K i))) =
        Additive.ofMul (cyclotomicUnitFreeClass K (pollaczekUnit 37 K i)) from
      cyclotomicUnitFreePart_unitsComplexConj_eq (p := 37) (K := K) hp_two _]

/-- **A 37-th-power Pollaczek unit has vanishing mod-37 free-part class** (general `i`).
If `pollaczekUnitPlus 37 K i = α^37` for some unit `α`, then the bare class
`[pollaczekUnit 37 K i]` in `CyclotomicUnitFreePartModP` is zero. This is the
index-agnostic forward direction of `flt37_pollaczekUnit_class_in_modp_freepart_ne_zero_iff_cert`
(the reverse there is `i = 32`-specific, using the certificate). Proof: the mod-37
free-part map kills 37-th powers, so `[PUP i] = 0`; and `[PUP i] = 2·[PU i]` with `2`
invertible in `ZMod 37`, so `[PU i] = 0`. -/
theorem pollaczekUnit_class_in_modp_freepart_eq_zero_of_pthPower
    (i : ℕ) (h : ∃ α : (𝓞 K)ˣ, pollaczekUnitPlus 37 K i = α ^ 37) :
    cyclotomicUnitToFreePartModPAdd (p := 37) K
        (Additive.ofMul (pollaczekUnit 37 K i)) = 0 := by
  obtain ⟨α, hα⟩ := h
  have h_PUP_zero :
      cyclotomicUnitToFreePartModPAdd (p := 37) K
          (Additive.ofMul (pollaczekUnitPlus 37 K i)) = 0 := by
    rw [hα]
    have := cyclotomicUnitToFreePartModPMul_pow_eq_one (p := 37) (K := K) α
    apply Multiplicative.ext
    exact this
  have h_two_PU :
      (2 : ℕ) • cyclotomicUnitToFreePartModPAdd (p := 37) K
          (Additive.ofMul (pollaczekUnit 37 K i)) = 0 := by
    rw [← pollaczekUnitPlus_class_eq_two_smul_pollaczekUnit_class_in_modp_freepart_general]
    exact h_PUP_zero
  set y : CyclotomicUnitFreePartModP (p := 37) K :=
    cyclotomicUnitToFreePartModPAdd (p := 37) K
      (Additive.ofMul (pollaczekUnit 37 K i)) with hy
  letI : Invertible ((2 : ZMod 37)) :=
    twoInvertibleZModOfPrimeGtTwo (p := 37) (by omega)
  have h_two_smul_zmod : ((2 : ZMod 37)) • y = 0 := by
    have h_cast : (((2 : ℕ) : ZMod 37)) • y = ((2 : ℕ) : ℕ) • y :=
      Nat.cast_smul_eq_nsmul (R := ZMod 37) 2 y
    have h_eq : ((2 : ZMod 37)) • y = ((2 : ℕ) : ZMod 37) • y := by norm_cast
    rw [h_eq, h_cast]
    exact h_two_PU
  calc y
      = (1 : ZMod 37) • y := (one_smul _ _).symm
    _ = (⅟(2 : ZMod 37) * (2 : ZMod 37)) • y := by rw [invOf_mul_self]
    _ = ⅟(2 : ZMod 37) • ((2 : ZMod 37) • y) := by rw [mul_smul]
    _ = ⅟(2 : ZMod 37) • (0 : _) := by rw [h_two_smul_zmod]
    _ = 0 := smul_zero _

/-- **Reverse, step 1/2 (general `i`).** If `[pollaczekUnit i]_modp = 0` then the power class
of the *symmetrised* `pollaczekUnitPlus 37 K i` lies in the torsion·(p-th-powers) subgroup
`cyclotomicTorsionPowerClassSubgroup` — i.e. `pollaczekUnitPlus i = ζ·β^37` for a root of unity
`ζ`. Composes the general two-smul lemma with the kernel characterisation
`cyclotomicUnitPowerQuotientToFreePartModP_ker`. -/
theorem pollaczekUnitPlus_powerClass_mem_torsion_of_pollaczekUnit_class_eq_zero
    (i : ℕ)
    (h : cyclotomicUnitToFreePartModPAdd (p := 37) K
        (Additive.ofMul (pollaczekUnit 37 K i)) = 0) :
    cyclotomicUnitPowerClass (p := 37) (N := 1) K (pollaczekUnitPlus 37 K i) ∈
      cyclotomicTorsionPowerClassSubgroup (p := 37) K := by
  have hPUP : cyclotomicUnitToFreePartModPAdd (p := 37) K
      (Additive.ofMul (pollaczekUnitPlus 37 K i)) = 0 := by
    rw [pollaczekUnitPlus_class_eq_two_smul_pollaczekUnit_class_in_modp_freepart_general, h]
    simp
  have hmul : cyclotomicUnitPowerQuotientToFreePartModP (p := 37) K
      (cyclotomicUnitPowerClass (p := 37) (N := 1) K (pollaczekUnitPlus 37 K i)) = 1 := by
    rw [cyclotomicUnitPowerQuotientToFreePartModP_apply_class,
      ← cyclotomicUnitToFreePartModPAdd_apply, hPUP]
    rfl
  rw [← cyclotomicUnitPowerQuotientToFreePartModP_ker, MonoidHom.mem_ker]
  exact hmul

/-- **Reverse (general `i`): `[pollaczekUnit i]_modp = 0 ⟹ pollaczekUnitPlus i` is a 37-th power.**
This is the structural direction WF-814c needs (the converse of
`pollaczekUnit_class_in_modp_freepart_eq_zero_of_pthPower`), valid for *every* index, with no
certificate. Proof: by the previous lemma the power class of the σ-fixed `pollaczekUnitPlus i`
lies in the torsion subgroup; complex conjugation (the `-1 ∈ Δ` action) fixes it
(`pollaczekUnitPlus_complexConj`), so the odd-prime argument
`cyclotomicUnitPowerQuotient_eq_zero_of_mem_torsion_of_neg_one_fixed` makes the power class
trivial, i.e. `pollaczekUnitPlus i ∈ E^{37}`. -/
theorem pollaczekUnitPlus_isPthPower_of_pollaczekUnit_class_eq_zero
    (i : ℕ)
    (h : cyclotomicUnitToFreePartModPAdd (p := 37) K
        (Additive.ofMul (pollaczekUnit 37 K i)) = 0) :
    ∃ α : (𝓞 K)ˣ, pollaczekUnitPlus 37 K i = α ^ 37 := by
  have hmem := pollaczekUnitPlus_powerClass_mem_torsion_of_pollaczekUnit_class_eq_zero (K := K) i h
  have hfixed :
      cyclotomicUnitPowerQuotientDeltaActionZMod (p := 37) K (-1 : CyclotomicUnitDelta 37)
          (Additive.ofMul (cyclotomicUnitPowerClass (p := 37) (N := 1) K
            (pollaczekUnitPlus 37 K i))) =
        Additive.ofMul (cyclotomicUnitPowerClass (p := 37) (N := 1) K
          (pollaczekUnitPlus 37 K i)) := by
    apply Additive.toMul.injective
    change (cyclotomicUnitModPDeltaAction (p := 37) K).act (-1 : CyclotomicUnitDelta 37)
        (cyclotomicUnitPowerClass (p := 37) (N := 1) K (pollaczekUnitPlus 37 K i)) =
      cyclotomicUnitPowerClass (p := 37) (N := 1) K (pollaczekUnitPlus 37 K i)
    rw [cyclotomicUnitPowerQuotientDeltaAction_act_mk,
      cyclotomicUnitEquiv_neg_one_apply (p := 37) (K := K) (by norm_num : 2 < 37)]
    congr 1
    exact pollaczekUnitPlus_complexConj 37 K i
  have hzero := cyclotomicUnitPowerQuotient_eq_zero_of_mem_torsion_of_neg_one_fixed
    (p := 37) (K := K) (by norm_num : 2 < 37) hmem hfixed
  have hone : cyclotomicUnitPowerClass (p := 37) (N := 1) K (pollaczekUnitPlus 37 K i) = 1 :=
    Additive.ofMul.injective hzero
  rw [cyclotomicUnitPowerClass_apply, QuotientGroup.eq_one_iff] at hone
  obtain ⟨v, hv⟩ := hone
  refine ⟨v, ?_⟩
  simpa [powMonoidHom] using hv.symm

omit [NumberField K] [IsCyclotomicExtension {37} ℚ K] [IsCMField K] in
/-- **General-`i` power-sum vanishing in the mod-37 free part** (WF-814b leaf a, link 1).
Generalises `cyclotomicUnitFreePartModP_powerSum_smul_eq_zero_FLT37` (exponent `36-32`) to every
even `i ∈ [2,34]`: the coefficient `∑_{b=1}^{18} b^{36-i}` is divisible by 37 (the `b ↔ 37-b`
pairing makes it twice a half-sum of even powers, and `37 ∤ 36-i` so the full sum vanishes mod 37),
hence its `ℕ`-scalar action is zero. Divisibility is decided over the finite range. -/
theorem cyclotomicUnitFreePartModP_powerSum_smul_eq_zero_general
    (i : ℕ) (hi_even : Even i) (hi2 : 2 ≤ i) (hi34 : i ≤ 34)
    (x : CyclotomicUnitFreePartModP (p := 37) K) :
    (∑ b ∈ Finset.Ico (1 : ℕ) (((37 : ℕ) - 1) / 2 + 1),
        b ^ ((37 : ℕ) - 1 - i)) • x = 0 := by
  haveI : NeZero (37 : ℕ) := ⟨by decide⟩
  have h_S_dvd : (37 : ℕ) ∣ ∑ b ∈ Finset.Ico (1 : ℕ) (((37 : ℕ) - 1) / 2 + 1),
      b ^ ((37 : ℕ) - 1 - i) := by
    interval_cases i <;> revert hi_even <;> decide
  have h_S_zmod : ((∑ b ∈ Finset.Ico (1 : ℕ) (((37 : ℕ) - 1) / 2 + 1),
      b ^ ((37 : ℕ) - 1 - i) : ℕ) : ZMod 37) = 0 :=
    (ZMod.natCast_eq_zero_iff _ 37).mpr h_S_dvd
  rw [show ((∑ b ∈ Finset.Ico (1 : ℕ) (((37 : ℕ) - 1) / 2 + 1),
        b ^ ((37 : ℕ) - 1 - i)) • x : CyclotomicUnitFreePartModP (p := 37) K) =
      ((∑ b ∈ Finset.Ico (1 : ℕ) (((37 : ℕ) - 1) / 2 + 1),
        b ^ ((37 : ℕ) - 1 - i) : ℕ) : ZMod 37) • x from
    (Nat.cast_smul_eq_nsmul (R := ZMod 37) _ x).symm]
  rw [h_S_zmod, zero_smul]

omit [IsCMField K] in
/-- **General-`i` Pollaczek eigenvalue in the mod-37 free part** (WF-814b leaf a, link 2).
Generalises `pollaczekUnit_image_eigenvalue_FLT37` to even `i ∈ [2,34]`: the Galois image of
`pollaczekUnit 37 K i` has additive mod-37 free-part class `(a^i).val • [pollaczekUnit i]`. The
37-th-power, power-sum, and sign+ζ correction factors of the unit-level eigenvalue identity all
vanish in the free part. -/
theorem pollaczekUnit_image_eigenvalue_general
    (i : ℕ) (hi_even : Even i) (hi2 : 2 ≤ i) (hi34 : i ≤ 34)
    (a : (ZMod 37)ˣ) (ha_coprime : ((a : ZMod 37).val).Coprime 37) :
    cyclotomicUnitToFreePartModPAdd (p := 37) K
        (Additive.ofMul (cyclotomicUnitEquiv (p := 37) K a (pollaczekUnit 37 K i))) =
      (((a ^ i : (ZMod 37)ˣ) : ZMod 37).val : ℕ) •
        cyclotomicUnitToFreePartModPAdd (p := 37) K
          (Additive.ofMul (pollaczekUnit 37 K i)) := by
  have heven_sub : Even (37 - 1 - i) := by
    rw [show (37 : ℕ) - 1 - i = 36 - i by norm_num]
    exact (Nat.even_sub (by omega : i ≤ 36)).mpr ⟨fun _ => hi_even, fun _ => by decide⟩
  obtain ⟨γ, hγ⟩ :=
    cyclotomicSigmaOfUnit_smul_pollaczekUnit_almost_eigenvalue_units
      (p := 37) (K := K) a i (by decide : (37 : ℕ) ≠ 2) (by decide : 2 ≤ 37)
      (by omega : (i : ℕ) ≤ 37 - 1) heven_sub ha_coprime
  have h_class := congrArg
    (fun u => cyclotomicUnitToFreePartModPAdd (p := 37) K (Additive.ofMul u)) hγ
  simp only [ofMul_mul, map_add, ofMul_pow, map_nsmul] at h_class
  rw [show ((∑ b ∈ Finset.Ico 1 ((37 - 1) / 2 + 1), b ^ (37 - 1 - i)) •
        cyclotomicUnitToFreePartModPAdd (p := 37) K
          (Additive.ofMul (cyclotomicUnitUnit 37 K ((a : ZMod 37).val) ha_coprime
            (by decide : 2 ≤ 37) : CyclotomicUnitGroup K))
        : CyclotomicUnitFreePartModP (p := 37) K) = 0 from
      cyclotomicUnitFreePartModP_powerSum_smul_eq_zero_general i hi_even hi2 hi34 _,
    add_zero] at h_class
  rw [signZeta_prefactor_class_eq_zero (p := 37) (K := K) a i, zero_add] at h_class
  have h_gamma_vanish : ((37 : ℕ) •
      cyclotomicUnitToFreePartModPAdd (p := 37) K
        (Additive.ofMul (γ : CyclotomicUnitGroup K))
      : CyclotomicUnitFreePartModP (p := 37) K) = 0 := by
    rw [← Nat.cast_smul_eq_nsmul (R := ZMod 37) 37 _, ZMod.natCast_self]
    exact zero_smul _ _
  rw [h_gamma_vanish, add_zero] at h_class
  exact h_class

omit [IsCMField K] in
/-- WF-814b leaf a, link 3: the additive Δ-action form of the general-`i` eigenvalue. -/
theorem pollaczekUnit_image_action_eq_general
    (i : ℕ) (hi_even : Even i) (hi2 : 2 ≤ i) (hi34 : i ≤ 34)
    (a : (ZMod 37)ˣ) (ha_coprime : ((a : ZMod 37).val).Coprime 37) :
    cyclotomicUnitFreePartModPClass (p := 37) K
        (cyclotomicUnitFreePartLinearEquiv (p := 37) K a
          (Additive.ofMul (cyclotomicUnitFreeClass K (pollaczekUnit 37 K i)))) =
      (((a ^ i : (ZMod 37)ˣ) : ZMod 37).val : ℕ) •
        cyclotomicUnitFreePartModPClass (p := 37) K
          (Additive.ofMul (cyclotomicUnitFreeClass K (pollaczekUnit 37 K i))) := by
  rw [cyclotomicUnitFreePartLinearEquiv_apply_class]
  exact pollaczekUnit_image_eigenvalue_general i hi_even hi2 hi34 a ha_coprime

omit [IsCMField K] in
/-- WF-814b leaf a, link 4: the `ZMod`-action form of the general-`i` eigenvalue. -/
theorem pollaczekUnit_image_DeltaActionZMod_eq_general
    (i : ℕ) (hi_even : Even i) (hi2 : 2 ≤ i) (hi34 : i ≤ 34)
    (a : (ZMod 37)ˣ) (ha_coprime : ((a : ZMod 37).val).Coprime 37) :
    cyclotomicUnitFreePartModPDeltaActionZMod (p := 37) K a
        (cyclotomicUnitFreePartModPClass (p := 37) K
          (Additive.ofMul (cyclotomicUnitFreeClass K (pollaczekUnit 37 K i)))) =
      (((a ^ i : (ZMod 37)ˣ) : ZMod 37).val : ℕ) •
        cyclotomicUnitFreePartModPClass (p := 37) K
          (Additive.ofMul (cyclotomicUnitFreeClass K (pollaczekUnit 37 K i))) := by
  rw [cyclotomicUnitFreePartModPDeltaActionZMod_apply,
      cyclotomicUnitFreePartModPLinearEquiv_apply_class]
  exact pollaczekUnit_image_action_eq_general i hi_even hi2 hi34 a ha_coprime

omit [IsCMField K] in
/-- WF-814b leaf a, link 5: eigenvalue in `ZMod 37`-scalar form (general `i`). -/
theorem pollaczekUnit_image_eigenvalue_zmod_general
    (i : ℕ) (hi_even : Even i) (hi2 : 2 ≤ i) (hi34 : i ≤ 34)
    (a : (ZMod 37)ˣ) (ha_coprime : ((a : ZMod 37).val).Coprime 37) :
    cyclotomicUnitFreePartModPDeltaActionZMod (p := 37) K a
        (cyclotomicUnitFreePartModPClass (p := 37) K
          (Additive.ofMul (cyclotomicUnitFreeClass K (pollaczekUnit 37 K i)))) =
      (((a ^ i : (ZMod 37)ˣ) : ZMod 37)) •
        cyclotomicUnitFreePartModPClass (p := 37) K
          (Additive.ofMul (cyclotomicUnitFreeClass K (pollaczekUnit 37 K i))) := by
  rw [pollaczekUnit_image_DeltaActionZMod_eq_general i hi_even hi2 hi34 a ha_coprime]
  set y : CyclotomicUnitFreePartModP (p := 37) K :=
    cyclotomicUnitFreePartModPClass (p := 37) K
      (Additive.ofMul (cyclotomicUnitFreeClass K (pollaczekUnit 37 K i)))
  haveI : NeZero (37 : ℕ) := ⟨by decide⟩
  rw [show (((a ^ i : (ZMod 37)ˣ) : ZMod 37)) • y =
      ((((a ^ i : (ZMod 37)ˣ) : ZMod 37).val : ℕ) : ZMod 37) • y from by
    rw [ZMod.natCast_val, ZMod.cast_id]]
  exact (Nat.cast_smul_eq_nsmul (R := ZMod 37)
    (((a ^ i : (ZMod 37)ˣ) : ZMod 37).val) y).symm

omit [IsCMField K] in
/-- WF-814b leaf a, link 6: ZMod-scalar eigenvalue for all `a` (general `i`). -/
theorem pollaczekUnit_image_eigenvalue_zmod_general_forall
    (i : ℕ) (hi_even : Even i) (hi2 : 2 ≤ i) (hi34 : i ≤ 34)
    (a : (ZMod 37)ˣ) :
    cyclotomicUnitFreePartModPDeltaActionZMod (p := 37) K a
        (cyclotomicUnitFreePartModPClass (p := 37) K
          (Additive.ofMul (cyclotomicUnitFreeClass K (pollaczekUnit 37 K i)))) =
      (((a ^ i : (ZMod 37)ˣ) : ZMod 37)) •
        cyclotomicUnitFreePartModPClass (p := 37) K
          (Additive.ofMul (cyclotomicUnitFreeClass K (pollaczekUnit 37 K i))) :=
  pollaczekUnit_image_eigenvalue_zmod_general i hi_even hi2 hi34 a
    (ZMod.val_coe_unit_coprime a)

omit [IsCMField K] in
/-- **WF-814b leaf a (goal): `[pollaczekUnit i]` lies in the ω^i-eigenspace** of the mod-37
free part, for every even `i ∈ [2,34]`. Generalises
`pollaczekUnit_image_in_omegaChar32_eigenspace_FLT37`. -/
theorem pollaczekUnit_image_in_omegaChar_eigenspace_general
    (i : ℕ) (hi_even : Even i) (hi2 : 2 ≤ i) (hi34 : i ≤ 34) :
    cyclotomicUnitFreePartModPClass (p := 37) K
        (Additive.ofMul (cyclotomicUnitFreeClass K (pollaczekUnit 37 K i))) ∈
      cyclotomicUnitFreePartModPDeltaCharacterEigenspace (p := 37) K
        (cyclotomicOmegaChar (p := 37) i) := by
  intro a
  rw [cyclotomicOmegaChar_apply]
  rw [show ((a : ZMod 37)) ^ i = ((a ^ i : (ZMod 37)ˣ) : ZMod 37) from by push_cast; rfl]
  exact pollaczekUnit_image_eigenvalue_zmod_general_forall i hi_even hi2 hi34 a

omit [IsCMField K] in
/-- **WF-814b leaf c: a nonzero `[E_i]` spans its (rank-1) ω^i-eigenspace** (general even `i`).
Generalises `flt37_pollaczekUnit_image_spans_omegaChar32_eigenspace`: the ω^i-eigenspace is
1-dimensional, and `[E_i]` lies in it (leaf a), so if `[E_i] ≠ 0` it generates the eigenspace.
(`ω^i ≠ 1` is taken as a hypothesis, discharged at the call site over the even range.) -/
theorem pollaczekUnit_image_spans_omegaChar_eigenspace_general
    (i : ℕ) (hi_even : Even i) (hi2 : 2 ≤ i) (hi34 : i ≤ 34)
    (hi_ne_one : cyclotomicOmegaChar (p := 37) i ≠
      (1 : MulChar (CyclotomicUnitDelta 37) (ZMod 37)))
    (h_ne : (⟨cyclotomicUnitFreePartModPClass (p := 37) K
          (Additive.ofMul (cyclotomicUnitFreeClass K (pollaczekUnit 37 K i))),
        pollaczekUnit_image_in_omegaChar_eigenspace_general i hi_even hi2 hi34⟩ :
        cyclotomicUnitFreePartModPDeltaCharacterEigenspace (p := 37) K
          (cyclotomicOmegaChar (p := 37) i)) ≠ 0) :
    Submodule.span (ZMod 37)
        ({⟨cyclotomicUnitFreePartModPClass (p := 37) K
              (Additive.ofMul (cyclotomicUnitFreeClass K (pollaczekUnit 37 K i))),
            pollaczekUnit_image_in_omegaChar_eigenspace_general i hi_even hi2 hi34⟩} :
          Set (cyclotomicUnitFreePartModPDeltaCharacterEigenspace (p := 37) K
            (cyclotomicOmegaChar (p := 37) i))) = ⊤ := by
  letI : Fintype {w : NumberField.InfinitePlace K //
      w ≠ NumberField.Units.dirichletUnitTheorem.w₀} := Fintype.ofFinite _
  letI : DiscreteTopology (NumberField.Units.unitLattice K) :=
    NumberField.Units.instDiscrete_unitLattice K
  letI : IsZLattice ℝ (NumberField.Units.unitLattice K) := by
    refine ⟨?_⟩
    convert NumberField.Units.dirichletUnitTheorem.unitLattice_span_eq_top K
  have h_finrank :
      Module.finrank (ZMod 37)
        (cyclotomicUnitFreePartModPDeltaCharacterEigenspace (p := 37) K
          (cyclotomicOmegaChar (p := 37) i)) = 1 :=
    cyclotomicUnitFreePartModPDeltaCharacterEigenspace_finrank_of_even_ne_one
      (p := 37) (K := K) (by omega)
      (cyclotomicOmegaChar_even_of_even (p := 37) i hi_even) hi_ne_one
  exact (finrank_eq_one_iff_of_nonzero _ h_ne).mp h_finrank

/-- **`ω^i` is non-trivial for `i ∈ [2,34]`** — evaluate at the unit `2`, where `2^i ≠ 1` in
`ZMod 37` (the order of `2` is `36 > 34`). Discharges the `ω^i ≠ 1` hypothesis of the rank-one
and spanning lemmas over the even range. Generalises `cyclotomicOmegaChar_32_ne_one_FLT37`. -/
theorem cyclotomicOmegaChar_ne_one_of_range (i : ℕ) (hi2 : 2 ≤ i) (hi34 : i ≤ 34) :
    cyclotomicOmegaChar (p := 37) i ≠
      (1 : MulChar (CyclotomicUnitDelta 37) (ZMod 37)) := by
  intro h
  have h2 : Nat.Coprime 2 37 := by decide
  have h_apply :
      cyclotomicOmegaChar (p := 37) i (ZMod.unitOfCoprime 2 h2 : CyclotomicUnitDelta 37) =
        (1 : ZMod 37) := by
    rw [h]; exact MulChar.one_apply (Group.isUnit (ZMod.unitOfCoprime 2 h2))
  rw [cyclotomicOmegaChar_apply, ZMod.coe_unitOfCoprime, ← Nat.cast_pow,
    ← Nat.cast_one (R := ZMod 37), ZMod.natCast_eq_natCast_iff] at h_apply
  -- `h_apply : 2 ^ i ≡ 1 [MOD 37]` — a statement in ℕ, free of `ZMod` instance variables.
  revert h_apply
  interval_cases i <;> decide

/-- **`ω^·` is injective on `[2,34]`** — distinct indices in the range give distinct characters
(`2` has order `36 > 32 ≥ |i-j|`). Feeds the counting argument for the (b)-assembly: the 17
characters `{ω^j : j even ∈ [2,34]}` are distinct, hence exhaust the 17 even non-trivial
characters. -/
theorem cyclotomicOmegaChar_injOn_range {i j : ℕ}
    (hi2 : 2 ≤ i) (hi34 : i ≤ 34) (hj2 : 2 ≤ j) (hj34 : j ≤ 34)
    (h : cyclotomicOmegaChar (p := 37) i = cyclotomicOmegaChar (p := 37) j) : i = j := by
  have h2 : Nat.Coprime 2 37 := by decide
  have hval :
      cyclotomicOmegaChar (p := 37) i (ZMod.unitOfCoprime 2 h2 : CyclotomicUnitDelta 37) =
        cyclotomicOmegaChar (p := 37) j (ZMod.unitOfCoprime 2 h2 : CyclotomicUnitDelta 37) := by
    rw [h]
  rw [cyclotomicOmegaChar_apply, cyclotomicOmegaChar_apply, ZMod.coe_unitOfCoprime,
    ← Nat.cast_pow, ← Nat.cast_pow, ZMod.natCast_eq_natCast_iff] at hval
  -- `hval : 2 ^ i ≡ 2 ^ j [MOD 37]` in ℕ.
  revert hval
  interval_cases i <;> interval_cases j <;> decide

/-- **The descended even characters `{descend(ω^i)}` are distinct on `[2,34]`** — apply the
pullback retraction (`evenDeltaCharacterPullback_descend`) and the injectivity of `ω^·`. Feeds
the linear-independence step of the (b)-assembly. -/
theorem cyclotomicOmegaChar_descend_injOn_range {i j : ℕ}
    (hi_even : Even i) (hi2 : 2 ≤ i) (hi34 : i ≤ 34)
    (hj_even : Even j) (hj2 : 2 ≤ j) (hj34 : j ≤ 34)
    (h : evenDeltaCharacterDescend (p := 37) (cyclotomicOmegaChar (p := 37) i)
          (cyclotomicOmegaChar_even_of_even (p := 37) i hi_even) =
        evenDeltaCharacterDescend (p := 37) (cyclotomicOmegaChar (p := 37) j)
          (cyclotomicOmegaChar_even_of_even (p := 37) j hj_even)) : i = j := by
  apply cyclotomicOmegaChar_injOn_range hi2 hi34 hj2 hj34
  have hpb := congrArg (evenDeltaCharacterPullback (p := 37)) h
  rwa [evenDeltaCharacterPullback_descend, evenDeltaCharacterPullback_descend] at hpb

/-- **`(2 : ZMod 37)^·` is injective on `[2,34]`** — the eigenvalues of `[E_i]` under the
Galois action by the generator `2` are distinct. This is the `Function.Injective` hypothesis of
`Module.End.eigenvectors_linearIndependent'`, by which the `{[E_i]}` are linearly independent. -/
theorem pow_two_zmod_injOn_range {i j : ℕ}
    (hi2 : 2 ≤ i) (hi34 : i ≤ 34) (hj2 : 2 ≤ j) (hj34 : j ≤ 34)
    (h : (2 : ZMod 37) ^ i = (2 : ZMod 37) ^ j) : i = j := by
  rw [show (2 : ZMod 37) = ((2 : ℕ) : ZMod 37) from by norm_cast,
    ← Nat.cast_pow, ← Nat.cast_pow, ZMod.natCast_eq_natCast_iff] at h
  revert h
  interval_cases i <;> interval_cases j <;> decide

omit [IsCMField K] in
/-- **WF-814b (b): `[E_i]` is an eigenvector of the action by the generator `2`** with eigenvalue
`(2 : ZMod 37)^i`. From sub-leaf (a) (the eigenvalue identity) and `[E_i] ≠ 0`. -/
theorem pollaczekUnit_image_hasEigenvector (i : ℕ)
    (hi_even : Even i) (hi2 : 2 ≤ i) (hi34 : i ≤ 34)
    (h_ne : cyclotomicUnitFreePartModPClass (p := 37) K
        (Additive.ofMul (cyclotomicUnitFreeClass K (pollaczekUnit 37 K i))) ≠ 0) :
    Module.End.HasEigenvector
      (cyclotomicUnitFreePartModPDeltaActionZMod (p := 37) K
        (ZMod.unitOfCoprime 2 (by decide : Nat.Coprime 2 37))).toLinearMap
      ((2 : ZMod 37) ^ i)
      (cyclotomicUnitFreePartModPClass (p := 37) K
        (Additive.ofMul (cyclotomicUnitFreeClass K (pollaczekUnit 37 K i)))) := by
  rw [Module.End.hasEigenvector_iff]
  refine ⟨?_, h_ne⟩
  rw [Module.End.mem_eigenspace_iff]
  change cyclotomicUnitFreePartModPDeltaActionZMod (p := 37) K
      (ZMod.unitOfCoprime 2 (by decide : Nat.Coprime 2 37))
      (cyclotomicUnitFreePartModPClass (p := 37) K
        (Additive.ofMul (cyclotomicUnitFreeClass K (pollaczekUnit 37 K i)))) = _
  rw [pollaczekUnit_image_eigenvalue_zmod_general_forall i hi_even hi2 hi34
      (ZMod.unitOfCoprime 2 (by decide : Nat.Coprime 2 37))]
  congr 1

omit [IsCMField K] in
/-- **WF-814b (b): the 17 Pollaczek classes are linearly independent** (when all nonzero) — they
are eigenvectors of the action by `2` with the distinct eigenvalues `(2)^{2k+2}`. -/
theorem pollaczekUnit_image_linearIndependent
    (h_all : ∀ i : ℕ, Even i → 2 ≤ i → i ≤ 34 →
      cyclotomicUnitFreePartModPClass (p := 37) K
        (Additive.ofMul (cyclotomicUnitFreeClass K (pollaczekUnit 37 K i))) ≠ 0) :
    LinearIndependent (ZMod 37) (fun k : Fin 17 =>
      cyclotomicUnitFreePartModPClass (p := 37) K
        (Additive.ofMul (cyclotomicUnitFreeClass K
          (pollaczekUnit 37 K (2 * (k : ℕ) + 2))))) := by
  refine Module.End.eigenvectors_linearIndependent'
    (cyclotomicUnitFreePartModPDeltaActionZMod (p := 37) K
      (ZMod.unitOfCoprime 2 (by decide : Nat.Coprime 2 37))).toLinearMap
    (fun k : Fin 17 => (2 : ZMod 37) ^ (2 * (k : ℕ) + 2)) ?_ _ ?_
  · intro k k' hkk'
    have hk : (k : ℕ) < 17 := k.isLt
    have hk' : (k' : ℕ) < 17 := k'.isLt
    have heq := pow_two_zmod_injOn_range (i := 2 * (k : ℕ) + 2) (j := 2 * (k' : ℕ) + 2)
      (by omega) (by omega) (by omega) (by omega) hkk'
    exact Fin.ext (by omega)
  · intro k
    have hk : (k : ℕ) < 17 := k.isLt
    exact pollaczekUnit_image_hasEigenvector (2 * (k : ℕ) + 2)
      ⟨(k : ℕ) + 1, by ring⟩ (by omega) (by omega)
      (h_all _ ⟨(k : ℕ) + 1, by ring⟩ (by omega) (by omega))

omit [IsCMField K] in
/-- **WF-814b (b)-assembly: the Pollaczek classes span the mod-37 free part** (when all nonzero).
17 linearly independent vectors in the 17-dimensional space form a basis, hence span `⊤`. -/
theorem pollaczekUnit_image_span_eq_top
    (h_all : ∀ i : ℕ, Even i → 2 ≤ i → i ≤ 34 →
      cyclotomicUnitFreePartModPClass (p := 37) K
        (Additive.ofMul (cyclotomicUnitFreeClass K (pollaczekUnit 37 K i))) ≠ 0) :
    Submodule.span (ZMod 37) (Set.range (fun k : Fin 17 =>
      cyclotomicUnitFreePartModPClass (p := 37) K
        (Additive.ofMul (cyclotomicUnitFreeClass K
          (pollaczekUnit 37 K (2 * (k : ℕ) + 2)))))) = ⊤ := by
  letI : Fintype {w : NumberField.InfinitePlace K //
      w ≠ NumberField.Units.dirichletUnitTheorem.w₀} := Fintype.ofFinite _
  letI : DiscreteTopology (NumberField.Units.unitLattice K) :=
    NumberField.Units.instDiscrete_unitLattice K
  letI : IsZLattice ℝ (NumberField.Units.unitLattice K) := by
    refine ⟨?_⟩
    convert NumberField.Units.dirichletUnitTheorem.unitLattice_span_eq_top K
  have hcard : Fintype.card (Fin 17) =
      Module.finrank (ZMod 37) (CyclotomicUnitFreePartModP (p := 37) K) := by
    rw [Fintype.card_fin, cyclotomicUnitFreePartModP_finrank_eq (p := 37) (K := K)
      (by norm_num : (2 : ℕ) < 37)]
  have hspan := (basisOfLinearIndependentOfCardEqFinrank
    (pollaczekUnit_image_linearIndependent h_all) hcard).span_eq
  rwa [coe_basisOfLinearIndependentOfCardEqFinrank] at hspan

omit hp37 in
/-- **Nakayama–Cauchy core (d)**: a finite commutative group on which raising to the `p`-th
power is surjective has order coprime to `p`. (If `p ∣ |G|`, Cauchy gives an order-`p` element,
but `(·)^p` injective—from surjective + finite—forces it to be trivial.) -/
theorem not_dvd_card_of_pow_surjective {G : Type*} [CommGroup G] [Finite G] (p : ℕ)
    [Fact p.Prime] (h : Function.Surjective (fun y : G => y ^ p)) : ¬ p ∣ Nat.card G := by
  intro hdvd
  have hinj : Function.Injective (fun y : G => y ^ p) :=
    Finite.injective_iff_surjective.mpr h
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := G) p hdvd
  have hx1 : x = 1 := hinj (by simpa using pow_orderOf_eq_one x ▸ hx ▸ rfl)
  rw [hx1, orderOf_one] at hx
  exact (Fact.out : p.Prime).ne_one hx.symm

/-- **WF-814b (d) step: the symmetrised Pollaczek classes span the mod-37 free part** (when all
bare classes are nonzero). Since `[PUP_i] = 2·[PU_i]` and `2` is a unit in `ZMod 37`, the
symmetrised family spans the same subspace as the bare family, which is `⊤` by (b). -/
theorem pollaczekUnitPlus_image_span_eq_top
    (h_all : ∀ i : ℕ, Even i → 2 ≤ i → i ≤ 34 →
      cyclotomicUnitFreePartModPClass (p := 37) K
        (Additive.ofMul (cyclotomicUnitFreeClass K (pollaczekUnit 37 K i))) ≠ 0) :
    Submodule.span (ZMod 37) (Set.range (fun k : Fin 17 =>
      cyclotomicUnitToFreePartModPAdd (p := 37) K
        (Additive.ofMul (pollaczekUnitPlus 37 K (2 * (k : ℕ) + 2))))) = ⊤ := by
  have hb := pollaczekUnit_image_span_eq_top (K := K) h_all
  -- Each `[PUP_{2k+2}] = (2 : ℕ) • [PU_{2k+2}]`, so the symmetrised range is `2 •` the bare range.
  have hrw : (fun k : Fin 17 =>
      cyclotomicUnitToFreePartModPAdd (p := 37) K
        (Additive.ofMul (pollaczekUnitPlus 37 K (2 * (k : ℕ) + 2)))) =
      fun k : Fin 17 => ((2 : ZMod 37)) •
        cyclotomicUnitFreePartModPClass (p := 37) K
          (Additive.ofMul (cyclotomicUnitFreeClass K (pollaczekUnit 37 K (2 * (k : ℕ) + 2)))) := by
    funext k
    rw [pollaczekUnitPlus_class_eq_two_smul_pollaczekUnit_class_in_modp_freepart_general,
      cyclotomicUnitToFreePartModPAdd_apply, ← Nat.cast_smul_eq_nsmul (ZMod 37)]
    norm_num
  rw [hrw]
  apply le_antisymm le_top
  rw [← hb]
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨k, rfl⟩
  simp only []
  have h2k : (2 : ZMod 37) • cyclotomicUnitFreePartModPClass (p := 37) K
        (Additive.ofMul (cyclotomicUnitFreeClass K (pollaczekUnit 37 K (2 * (k : ℕ) + 2)))) ∈
      Submodule.span (ZMod 37) (Set.range (fun k : Fin 17 => (2 : ZMod 37) •
        cyclotomicUnitFreePartModPClass (p := 37) K
          (Additive.ofMul (cyclotomicUnitFreeClass K (pollaczekUnit 37 K (2 * (k : ℕ) + 2)))))) :=
    Submodule.subset_span (Set.mem_range_self k)
  have hinv : cyclotomicUnitFreePartModPClass (p := 37) K
        (Additive.ofMul (cyclotomicUnitFreeClass K (pollaczekUnit 37 K (2 * (k : ℕ) + 2)))) =
      (2⁻¹ : ZMod 37) • ((2 : ZMod 37) • cyclotomicUnitFreePartModPClass (p := 37) K
        (Additive.ofMul (cyclotomicUnitFreeClass K (pollaczekUnit 37 K (2 * (k : ℕ) + 2))))) := by
    have h2ne : (2 : ZMod 37) ≠ 0 := by
      rw [show (2 : ZMod 37) = ((2 : ℕ) : ZMod 37) from by push_cast; ring,
        show (0 : ZMod 37) = ((0 : ℕ) : ZMod 37) from by push_cast; ring, Ne,
        ZMod.natCast_eq_natCast_iff]
      decide
    rw [smul_smul, inv_mul_cancel₀ h2ne, one_smul]
  rw [hinv]
  exact Submodule.smul_mem _ _ h2k

end FLT37

end BernoulliRegular

end
