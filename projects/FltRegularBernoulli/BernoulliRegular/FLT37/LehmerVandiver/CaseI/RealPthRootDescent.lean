import BernoulliRegular.FLT37.LehmerVandiver.CaseI.RealKummerLemma
import BernoulliRegular.FLT37.LehmerVandiver.PlusCoprime.Sinnott.PollaczekFamilyDescent
import BernoulliRegular.FLT37.LehmerVandiver.PlusCoprime.Thaine.CertificateAudit
import BernoulliRegular.FLT37.LehmerVandiver.PlusCoprime.Thaine.UnitClassBridge
import BernoulliRegular.FLT37.Final
import BernoulliRegular.FLT37.LehmerVandiver.PlusCoprime.Sinnott.FinalSynthesis
import BernoulliRegular.FLT37.LehmerVandiver.PlusCoprime.RealBundle
import BernoulliRegular.FLT37.LehmerVandiver.PlusCoprime.RealPthPower


/-!
# K^×-level cohomology fact for real `p`-th powers

For a CM field `K` with the project's setup, if `α ∈ K^×` has `α^p`
real (i.e., σ-fixed), then `(σα)/α` is a p-th root of unity in `K`.

This is the Galois-cohomology shadow: `α ↦ σ(α)/α` is the
1-cocycle map for `H¹(σ, K^×)`, and `(σα)/α ∈ μ_p` says the cocycle
class lies in `H¹(σ, μ_p)`. For `σ` of order 2 and `μ_p` of order `p`
coprime to 2, this group vanishes — providing the descent.

This is the K^×-level analogue of `unit_inv_conj_is_root_of_unity`
(flt-regular's Cyclotomic.UnitLemmas), which is at the `(𝓞 K)ˣ` level
and uses Kronecker's absolute-value bound. The K^×-level statement
needs only the algebraic fact that `(σα)^p = α^p` forces `σα/α` to
have p-th power 1.

## References

* Washington, *Introduction to Cyclotomic Fields*, §9.3 (real p-th root descent).
* `unit_inv_conj_is_root_of_unity` (flt-regular Cyclotomic.UnitLemmas).
-/

@[expose] public section

noncomputable section

open NumberField IsCyclotomicExtension

namespace BernoulliRegular

namespace FLT37

namespace LehmerVandiver

namespace CaseI

variable {p : ℕ} [Fact p.Prime]
variable {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
  [NumberField.IsCMField K]

omit [Fact p.Prime] [IsCyclotomicExtension {p} ℚ K] in
/-- **K^×-level cohomology vanishing**: for `α ∈ K^×` with `α^p` real,
`(σα)/α` is a p-th root of unity in `K`. -/
theorem complexConj_div_self_pow_eq_one_of_pow_real {α : K} (hα : α ≠ 0)
    (h_pow_real : NumberField.IsCMField.complexConj K (α ^ p) = α ^ p) :
    (NumberField.IsCMField.complexConj K α / α) ^ p = 1 := by
  rw [div_pow, ← map_pow, h_pow_real, div_self (pow_ne_zero p hα)]

omit [NumberField.IsCMField K] in
/-- **Existence of explicit `p`-th-root-of-unity decomposition**: in
the cyclotomic field `K = ℚ(ζ_p)`, every `x ∈ K` with `x^p = 1` equals
`(ζ_p)^k` for some `k : ℕ`. -/
theorem exists_pow_zeta_eq_of_pth_root_of_unity {x : K} (hx : x ^ p = 1) :
    ∃ k : ℕ, k < p ∧
      x = (((zeta_spec p ℚ K).toInteger : 𝓞 K) : K) ^ k := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hζ : IsPrimitiveRoot
      (((zeta_spec p ℚ K).toInteger : 𝓞 K) : K) p := zeta_spec p ℚ K
  obtain ⟨k, hk_lt, hk_eq⟩ := hζ.eq_pow_of_pow_eq_one hx
  exact ⟨k, hk_lt, hk_eq.symm⟩

/-- **Combined**: for `α ∈ K^×` with `α^p` real, there exist `k < p`
such that `(σα)/α = ζ^k`. This is the explicit form of the
cohomology-vanishing fact, ready to feed into the descent argument
(`β = ζ^j · α` with `j ≡ k · 2⁻¹ (mod p)`). -/
theorem exists_pow_zeta_eq_complexConj_div_self_of_pow_real
    {α : K} (hα : α ≠ 0)
    (h_pow_real : NumberField.IsCMField.complexConj K (α ^ p) = α ^ p) :
    ∃ k : ℕ, k < p ∧
      NumberField.IsCMField.complexConj K α / α =
        (((zeta_spec p ℚ K).toInteger : 𝓞 K) : K) ^ k :=
  exists_pow_zeta_eq_of_pth_root_of_unity
    (complexConj_div_self_pow_eq_one_of_pow_real hα h_pow_real)

/-- **σ-action on `ζ_p`**: complex conjugation inverts the primitive
p-th root of unity at the K-value level. -/
theorem complexConj_zeta_eq_inv :
    NumberField.IsCMField.complexConj K
        (((zeta_spec p ℚ K).toInteger : 𝓞 K) : K) =
      (((zeta_spec p ℚ K).toInteger : 𝓞 K) : K)⁻¹ := by
  have hp_prime : p.Prime := Fact.out
  set ζU : (𝓞 K)ˣ :=
    ((zeta_spec p ℚ K).toInteger_isPrimitiveRoot.isUnit hp_prime.ne_zero).unit
  have hζU_val : ((ζU : (𝓞 K)ˣ) : 𝓞 K) = (zeta_spec p ℚ K).toInteger :=
    ((zeta_spec p ℚ K).toInteger_isPrimitiveRoot.isUnit hp_prime.ne_zero).unit_spec
  have hζU_pow : ζU ^ p = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_one, hζU_val]
    exact (zeta_spec p ℚ K).toInteger_isPrimitiveRoot.pow_eq_one
  have hζ_torsion : ζU ∈ NumberField.Units.torsion K :=
    (CommGroup.mem_torsion _).2
      (isOfFinOrder_iff_pow_eq_one.2 ⟨p, hp_prime.pos, hζU_pow⟩)
  have h_unit_conj : NumberField.IsCMField.unitsComplexConj K ζU = ζU⁻¹ :=
    NumberField.IsCMField.unitsComplexConj_torsion (K := K) ⟨ζU, hζ_torsion⟩
  have h_val_eq :
      (((NumberField.IsCMField.unitsComplexConj K ζU : (𝓞 K)ˣ) : 𝓞 K) : K) =
      (((ζU⁻¹ : (𝓞 K)ˣ) : 𝓞 K) : K) := by rw [h_unit_conj]
  have hRHS : (((ζU⁻¹ : (𝓞 K)ˣ) : 𝓞 K) : K) = (((ζU : (𝓞 K)ˣ) : 𝓞 K) : K)⁻¹ :=
    eq_inv_of_mul_eq_one_left <| by
      rw [← map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, map_one]
  rw [hRHS, hζU_val] at h_val_eq
  exact h_val_eq

omit [NumberField.IsCMField K] in
/-- **`ζ^p = 1` at K-value level**. -/
theorem zeta_pow_p_eq_one : (((zeta_spec p ℚ K).toInteger : 𝓞 K) : K) ^ p = 1 := by
  have h_int : ((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ p = 1 :=
    (zeta_spec p ℚ K).toInteger_isPrimitiveRoot.pow_eq_one
  exact_mod_cast congrArg (algebraMap (𝓞 K) K) h_int

/-- **K^×-level real `p`-th-root descent (explicit form)**.
For `α : K` non-zero with `α^p` σ-fixed (real), there exists a σ-fixed
`β : K` with `β^p = α^p`. Concretely `β = ζ^j · α` where `j := k(p+1)/2`
with `k` from `exists_pow_zeta_eq_complexConj_div_self_of_pow_real`.
For `p` odd, `p+1` is even, so `k(p+1)/2` is an exact natural division.

The argument: `2j = k(p+1) = kp + k`, so `ζ^{2j} = ζ^{kp} · ζ^k = ζ^k`
(using `ζ^p = 1`). Hence `σ(ζ^j α) = ζ^{-j} · ζ^k α = ζ^j α` (since
`ζ^{2j} = ζ^k` gives `ζ^{k-j} = ζ^j`). -/
theorem exists_complexConj_fixed_pow_eq_pow_of_pow_real
    (hp_two : 2 < p) {α : K} (hα : α ≠ 0)
    (h_pow_real : NumberField.IsCMField.complexConj K (α ^ p) = α ^ p) :
    ∃ β : K, NumberField.IsCMField.complexConj K β = β ∧ β ^ p = α ^ p := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  obtain ⟨k, _hk_lt, hk_eq⟩ :=
    exists_pow_zeta_eq_complexConj_div_self_of_pow_real hα h_pow_real
  set ζ : K := (((zeta_spec p ℚ K).toInteger : 𝓞 K) : K)
  have hk_mul : NumberField.IsCMField.complexConj K α = ζ ^ k * α := by
    field_simp at hk_eq
    rw [hk_eq]; ring
  have hζ_pow_p : ζ ^ p = 1 := zeta_pow_p_eq_one
  have hζ_ne_zero : ζ ≠ 0 := fun hζ_zero =>
    zero_ne_one (α := K) <| by
      rw [← hζ_pow_p, hζ_zero, zero_pow (Fact.out : p.Prime).pos.ne']
  have hσζ : NumberField.IsCMField.complexConj K ζ = ζ⁻¹ := complexConj_zeta_eq_inv
  -- For `p` odd, `p + 1` is even; write `p + 1 = 2 * q` and set `j := k * q`.
  have hp_odd : Odd p := (Fact.out : p.Prime).odd_of_ne_two (Nat.ne_of_gt hp_two)
  obtain ⟨q, hq⟩ := Odd.add_one hp_odd
  have hq_eq : p + 1 = 2 * q := by omega
  set j : ℕ := k * q
  have h_two_j : 2 * j = k * (p + 1) := by
    change 2 * (k * q) = k * (p + 1)
    rw [hq_eq]; ring
  have hζ_2j_eq_k : ζ ^ (2 * j) = ζ ^ k := by
    rw [h_two_j, mul_add, mul_one, mul_comm k p, pow_add, pow_mul, hζ_pow_p,
        one_pow, one_mul]
  refine ⟨ζ ^ j * α, ?_, ?_⟩
  · rw [map_mul, map_pow, hσζ, hk_mul, inv_pow]
    -- `ζ ^ k = ζ ^ (2 * j) = ζ ^ j * ζ ^ j`, so `(ζ ^ j)⁻¹ * ζ ^ k = ζ ^ j`.
    have h_pow_eq : ζ ^ k = ζ ^ j * ζ ^ j := by
      rw [← pow_add, ← two_mul, hζ_2j_eq_k]
    rw [h_pow_eq, mul_assoc (ζ ^ j) (ζ ^ j), ← mul_assoc (ζ ^ j)⁻¹,
        inv_mul_cancel₀ (pow_ne_zero j hζ_ne_zero), one_mul]
  · rw [mul_pow, ← pow_mul, mul_comm j p, pow_mul, hζ_pow_p, one_pow, one_mul]

/-- **K^×-side root ⟹ K^+-side unit**: bridges the K^×-level descent
to the unit level. Given `u : (𝓞 K^+)ˣ` and `v ∈ K` with `v^p = (u : K)`
(algebraMap-image of `u` in `K`), there exists `w : (𝓞 K^+)ˣ` with `u = w^p`.

The argument: `v^p = (u : K)` is integral over ℤ, so `v` is integral
(by `IsIntegral.of_pow`). So `v ∈ 𝓞 K`. Since `v^p = (u : K)` is a unit,
`v` is a unit in `𝓞 K`. Apply the project's `realKummerExtract_unconditional`.
(Universe-restricted to `Type` to match `realKummerExtract_unconditional`.) -/
theorem exists_real_unit_pow_eq_of_K_root
    {p' : ℕ} [Fact p'.Prime] {K' : Type} [Field K'] [NumberField K']
    [IsCyclotomicExtension {p'} ℚ K'] [NumberField.IsCMField K']
    (hp_two : 2 < p') (u : (𝓞 (NumberField.maximalRealSubfield K'))ˣ)
    (v : K') (hv : v ^ p' =
      algebraMap (NumberField.maximalRealSubfield K') K' u) :
    ∃ w : (𝓞 (NumberField.maximalRealSubfield K'))ˣ, u = w ^ p' := by
  haveI : NeZero p' := ⟨(Fact.out : p'.Prime).ne_zero⟩
  have hp_pos : 0 < p' := (Fact.out : p'.Prime).pos
  have hv_int : IsIntegral ℤ v := by
    apply IsIntegral.of_pow hp_pos
    rw [hv]
    have h_uK : algebraMap (NumberField.maximalRealSubfield K') K'
        ((u : 𝓞 (NumberField.maximalRealSubfield K')) :
          NumberField.maximalRealSubfield K') =
        ((algebraMap (𝓞 (NumberField.maximalRealSubfield K')) (𝓞 K')
          (u : 𝓞 (NumberField.maximalRealSubfield K')) : 𝓞 K') : K') :=
      rfl
    rw [h_uK]
    exact NumberField.RingOfIntegers.isIntegral_coe _
  let v_OK : 𝓞 K' := ⟨v, hv_int⟩
  have h_pow_eq :
      v_OK ^ p' =
        algebraMap (𝓞 (NumberField.maximalRealSubfield K')) (𝓞 K') u := by
    apply Subtype.ext
    change v ^ p' = _
    rw [hv]
    rfl
  have hv_OK_unit : IsUnit v_OK := by
    rw [← isUnit_pow_iff hp_pos.ne', h_pow_eq]
    exact (Units.map (algebraMap (𝓞 (NumberField.maximalRealSubfield K'))
      (𝓞 K')).toMonoidHom u).isUnit
  let v_unit : (𝓞 K')ˣ := hv_OK_unit.unit
  have hv_unit_val_pow :
      (v_unit : 𝓞 K') ^ p' =
      algebraMap (𝓞 (NumberField.maximalRealSubfield K')) (𝓞 K') u := by
    rw [hv_OK_unit.unit_spec]; exact h_pow_eq
  exact realKummerExtract_unconditional p' K' hp_two u v_unit hv_unit_val_pow

/-- **K-side certificate ⟹ K^+-side certificate** (contrapositive form).
If `algebraMap v = pollaczekUnitPlus` and the K-side certificate
`∀ α : (𝓞 K)ˣ, pollaczekUnitPlus ≠ α^p` holds, then `v` itself is not
a `p`-th power in `(𝓞 K^+)ˣ`.

This descends the K-side certificate (which is what `flt37_realLocalCert_global`
proves) to a corresponding K^+-side certificate on `v`. Together with
`pollaczekInFamily` (which provides the explicit K^+-preimage `v`), this
gives a K^+-level certificate suitable for the `PollaczekForward`
contrapositive engine.

Concretely: if v = β^p in (𝓞 K^+)ˣ, then algebraMap v = (algebraMap β)^p
= (Units.map (algebraMap _ _).toMonoidHom β)^p in (𝓞 K)ˣ. But algebraMap v
= pollaczekUnitPlus, so pollaczekUnitPlus = (Units.map β)^p, contradicting
the K-side cert. -/
theorem not_isPthPower_Kplus_of_not_isPthPower_K
    {p' : ℕ} [Fact p'.Prime] {K' : Type*} [Field K'] [NumberField K']
    [IsCyclotomicExtension {p'} ℚ K'] [NumberField.IsCMField K']
    (i : ℕ)
    (h_K_cert : ∀ α : (𝓞 K')ˣ,
        ((FLT37.pollaczekUnitPlus p' K' i : (𝓞 K')ˣ) : 𝓞 K') ≠
          ((α : (𝓞 K')ˣ) : 𝓞 K') ^ p')
    (v : (𝓞 (NumberField.maximalRealSubfield K'))ˣ)
    (hv_eq : (algebraMap (𝓞 (NumberField.maximalRealSubfield K'))
        (𝓞 K') (v : 𝓞 _) : 𝓞 K') =
      ((FLT37.pollaczekUnitPlus p' K' i : (𝓞 K')ˣ) : 𝓞 K')) :
    ∀ β : (𝓞 (NumberField.maximalRealSubfield K'))ˣ, v ≠ β ^ p' := by
  intro β h_eq
  -- `v = β ^ p` ⟹ `algebraMap v = (algebraMap β) ^ p`, contradicting the K-side cert.
  set β_K : (𝓞 K')ˣ :=
    Units.map (algebraMap (𝓞 (NumberField.maximalRealSubfield K')) (𝓞 K')).toMonoidHom β
  apply h_K_cert β_K
  rw [← hv_eq, h_eq, Units.val_pow_eq_pow_val, map_pow, ← Units.val_pow_eq_pow_val]
  rfl

/-- **K^+-side certificate on `pollaczekUnitPlusKplus` for FLT37**.
Combining the project's `flt37_realLocalCert_global` (LV004g chain — the
K-side certificate `∀ α : (𝓞 K)ˣ, pollaczekUnitPlus ≠ α^p`),
`pollaczekInFamily` (project — provides `pollaczekUnitPlusKplus` as the
canonical K^+-preimage with the algebraMap equation), and the descent
bridge `not_isPthPower_Kplus_of_not_isPthPower_K` (this file), we get
the K^+-side certificate:

  `∀ β : (𝓞 K^+)ˣ, pollaczekUnitPlusKplus ≠ β^p`

i.e., `pollaczekUnitPlusKplus` is genuinely not a `p`-th power in
`(𝓞 K^+)ˣ`. This is exactly the contrapositive form needed by
`PollaczekForward`: if `pollaczekUnitPlusKplus` IS such a non-p-th-power,
then `¬ p ∣ h⁺` (under `PollaczekForward`).

The certificate side is now FULLY DERIVED — no parametric input needed
on the K^+-side. The remaining open content for the Cor 8.19 bridge is
just `PollaczekForward` itself (the `p ∣ h⁺ ⟹ ∃ β, β^p = v` direction). -/
theorem flt37_pollaczekUnitPlusKplus_not_isPthPower
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (hp_three : 3 ≤ 37) :
    haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
    ∀ β : (𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ)))ˣ,
      Sinnott.pollaczekUnitPlusKplus 37 (CyclotomicField 37 ℚ) 32
        (by decide : (37 : ℕ) ≠ 2) hp_three ≠ β ^ 37 := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  have h_alg_eq :=
    Sinnott.algebraMapPollaczekUnitPlusKplus_eq 37 (CyclotomicField 37 ℚ) 32
      (by decide : (37 : ℕ) ≠ 2) hp_three
  unfold Sinnott.AlgebraMapPollaczekUnitPlusKplus_eq at h_alg_eq
  exact not_isPthPower_Kplus_of_not_isPthPower_K (p' := 37)
    (K' := CyclotomicField 37 ℚ) 32 FLT37.flt37_realLocalCert_global
    (Sinnott.pollaczekUnitPlusKplus 37 (CyclotomicField 37 ℚ) 32
      (by decide : (37 : ℕ) ≠ 2) hp_three)
    h_alg_eq

/-- **FLT37 Cor 8.19 closure under `PollaczekForward`**: combining
`flt37_pollaczekUnitPlusKplus_not_isPthPower` (this file — the K^+-side
certificate fully proven for FLT37) with `pollaczekInFamily` and
`PollaczekForward`, derives `¬ 37 ∣ hPlus K` for `K = ℚ(ζ_37)` directly.

This is the FLT37 specialisation of the Cor 8.19 contrapositive engine
under just `PollaczekForward`'s remaining open hypothesis. -/
theorem flt37_not_dvd_hPlus_of_pollaczekForward
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (hp_three : 3 ≤ 37)
    (h_forward : haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
      Sinnott.PollaczekForward 37 (CyclotomicField 37 ℚ) 32
        (by decide : (37 : ℕ) ≠ 2) hp_three) :
    haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
    ¬ (37 : ℕ) ∣ hPlus (CyclotomicField 37 ℚ) := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  intro h_dvd
  set v_K_plus :=
    Sinnott.pollaczekUnitPlusKplus 37 (CyclotomicField 37 ℚ) 32
      (by decide : (37 : ℕ) ≠ 2) hp_three
  have h_alg_eq :=
    Sinnott.algebraMapPollaczekUnitPlusKplus_eq 37 (CyclotomicField 37 ℚ) 32
      (by decide : (37 : ℕ) ≠ 2) hp_three
  unfold Sinnott.AlgebraMapPollaczekUnitPlusKplus_eq at h_alg_eq
  have h_mem :=
    Sinnott.pollaczekUnitPlusKplus_mem 37 (CyclotomicField 37 ℚ) 32
      (by decide : (37 : ℕ) ≠ 2) hp_three
  -- `PollaczekForward` gives `β` with `β ^ 37 = v_K_plus`, refuted by the cert.
  obtain ⟨β, hβ⟩ := h_forward h_dvd v_K_plus h_alg_eq h_mem
  exact flt37_pollaczekUnitPlusKplus_not_isPthPower hp_three β hβ.symm

/-- **Injectivity of `Units.map` (algebraMap K^+ K) on units**.
Direct consequence of `FaithfulSMul.algebraMap_injective` — the
algebra-map embedding `𝓞 K^+ → 𝓞 K` is injective on rings, hence
also on units. -/
theorem units_algebraMap_injective_Kplus_K
    (p' : ℕ) [Fact p'.Prime] (K' : Type*) [Field K'] [NumberField K']
    [IsCyclotomicExtension {p'} ℚ K'] [NumberField.IsCMField K'] :
    Function.Injective
      (Units.map
        (algebraMap (𝓞 (NumberField.maximalRealSubfield K')) (𝓞 K')).toMonoidHom) := by
  intro u v h
  apply Units.ext
  exact FaithfulSMul.algebraMap_injective
    (𝓞 (NumberField.maximalRealSubfield K')) (𝓞 K') (congrArg Units.val h)

/-- **Uniqueness of K^+-side preimage** under the algebra-map embedding.
For `pollaczekUnitPlus p K i ∈ (𝓞 K)ˣ`, any two K^+-side units `v₁, v₂`
mapping to it under `algebraMap` are equal. Direct consequence of
`units_algebraMap_injective_Kplus_K`. -/
theorem unique_Kplus_preimage_of_pollaczekUnitPlus
    {p' : ℕ} [Fact p'.Prime] {K' : Type*} [Field K'] [NumberField K']
    [IsCyclotomicExtension {p'} ℚ K'] [NumberField.IsCMField K']
    (i : ℕ)
    {v₁ v₂ : (𝓞 (NumberField.maximalRealSubfield K'))ˣ}
    (h₁ : (algebraMap (𝓞 (NumberField.maximalRealSubfield K'))
        (𝓞 K') (v₁ : 𝓞 _) : 𝓞 K') =
      ((FLT37.pollaczekUnitPlus p' K' i : (𝓞 K')ˣ) : 𝓞 K'))
    (h₂ : (algebraMap (𝓞 (NumberField.maximalRealSubfield K'))
        (𝓞 K') (v₂ : 𝓞 _) : 𝓞 K') =
      ((FLT37.pollaczekUnitPlus p' K' i : (𝓞 K')ˣ) : 𝓞 K')) :
    v₁ = v₂ := by
  apply units_algebraMap_injective_Kplus_K p' K'
  apply Units.ext
  change (algebraMap (𝓞 (NumberField.maximalRealSubfield K')) (𝓞 K') (v₁ : 𝓞 _)) =
    (algebraMap (𝓞 (NumberField.maximalRealSubfield K')) (𝓞 K') (v₂ : 𝓞 _))
  rw [h₁, h₂]

/-- **Canonical K⁺ Pollaczek root from `PollaczekForward`.**

This is the reverse direction to
`pollaczekForward_of_pollaczekUnitPlusKplus_isPthPower`: applying
`PollaczekForward` to the canonical K⁺ preimage
`pollaczekUnitPlusKplus` gives exactly the simplified root statement used by
the final FLT37 assembly. -/
theorem pollaczekUnitPlusKplus_isPthPower_of_pollaczekForward
    {p' : ℕ} [Fact p'.Prime] {K' : Type} [Field K'] [NumberField K']
    [IsCyclotomicExtension {p'} ℚ K'] [NumberField.IsCMField K']
    (i : ℕ) (hp_odd : p' ≠ 2) (hp_three : 3 ≤ p')
    (h_forward : Sinnott.PollaczekForward p' K' i hp_odd hp_three)
    (h_dvd : (p' : ℕ) ∣ hPlus K') :
      ∃ β : (𝓞 (NumberField.maximalRealSubfield K'))ˣ,
        β ^ p' =
          Sinnott.pollaczekUnitPlusKplus p' K' i hp_odd hp_three := by
  have h_alg_eq :
      Sinnott.AlgebraMapPollaczekUnitPlusKplus_eq p' K' i hp_odd hp_three :=
    Sinnott.algebraMapPollaczekUnitPlusKplus_eq p' K' i hp_odd hp_three
  have h_mem :
      Sinnott.pollaczekUnitPlusKplus p' K' i hp_odd hp_three ∈
        Subgroup.closure
          (Set.range
            (Sinnott.cyclotomicUnitFamilyKplusFinRank p' K' hp_odd hp_three)) ⊔
        NumberField.Units.torsion (NumberField.maximalRealSubfield K') :=
    Sinnott.pollaczekUnitPlusKplus_mem p' K' i hp_odd hp_three
  exact
    h_forward h_dvd
      (Sinnott.pollaczekUnitPlusKplus p' K' i hp_odd hp_three)
      h_alg_eq h_mem

/-- **`PollaczekForward` simplifies to a claim about `pollaczekUnitPlusKplus`**.
By `unique_Kplus_preimage_of_pollaczekUnitPlus`, the K^+-side preimage
of `pollaczekUnitPlus` under `algebraMap` is unique. Combined with
`pollaczekInFamily` (giving the canonical witness `pollaczekUnitPlusKplus`),
`PollaczekForward` reduces to:

  `Under p ∣ h⁺, pollaczekUnitPlusKplus is a p-th power in (𝓞 K^+)ˣ`.

This packages the simplification as a clean if-direction. -/
theorem pollaczekForward_of_pollaczekUnitPlusKplus_isPthPower
    {p' : ℕ} [Fact p'.Prime] {K' : Type} [Field K'] [NumberField K']
    [IsCyclotomicExtension {p'} ℚ K'] [NumberField.IsCMField K']
    (i : ℕ) (hp_odd : p' ≠ 2) (hp_three : 3 ≤ p')
    (h_simplified : (p' : ℕ) ∣ hPlus K' →
      ∃ β : (𝓞 (NumberField.maximalRealSubfield K'))ˣ,
        β ^ p' =
          Sinnott.pollaczekUnitPlusKplus p' K' i hp_odd hp_three) :
    Sinnott.PollaczekForward p' K' i hp_odd hp_three := by
  intro h_dvd v hv_eq _hv_mem
  have h_alg_eq :
      (algebraMap (𝓞 (NumberField.maximalRealSubfield K')) (𝓞 K')
        ((Sinnott.pollaczekUnitPlusKplus p' K' i hp_odd hp_three :
          𝓞 (NumberField.maximalRealSubfield K')) :
          𝓞 (NumberField.maximalRealSubfield K')) : 𝓞 K') =
      ((FLT37.pollaczekUnitPlus p' K' i : (𝓞 K')ˣ) : 𝓞 K') :=
    Sinnott.algebraMapPollaczekUnitPlusKplus_eq p' K' i hp_odd hp_three
  have hv : v = Sinnott.pollaczekUnitPlusKplus p' K' i hp_odd hp_three :=
    unique_Kplus_preimage_of_pollaczekUnitPlus i hv_eq h_alg_eq
  rw [hv]
  exact h_simplified h_dvd

/-- **Exact Pollaczek source equivalence.**

The project's `PollaczekForward` endpoint is equivalent to the canonical
K⁺ Pollaczek-unit p-th-root statement under `p ∣ h⁺`.  This keeps the final
FLT37 path tied to the concrete unit `pollaczekUnitPlusKplus`, rather than to
an opaque Corollary 8.19-shaped package. -/
theorem pollaczekForward_iff_pollaczekUnitPlusKplus_isPthPower
    {p' : ℕ} [Fact p'.Prime] {K' : Type} [Field K'] [NumberField K']
    [IsCyclotomicExtension {p'} ℚ K'] [NumberField.IsCMField K']
    (i : ℕ) (hp_odd : p' ≠ 2) (hp_three : 3 ≤ p') :
    Sinnott.PollaczekForward p' K' i hp_odd hp_three ↔
      ((p' : ℕ) ∣ hPlus K' →
        ∃ β : (𝓞 (NumberField.maximalRealSubfield K'))ˣ,
          β ^ p' =
            Sinnott.pollaczekUnitPlusKplus p' K' i hp_odd hp_three) := by
  constructor
  · intro h_forward h_dvd
    exact
      pollaczekUnitPlusKplus_isPthPower_of_pollaczekForward
        i hp_odd hp_three h_forward h_dvd
  · intro h_root
    exact
      pollaczekForward_of_pollaczekUnitPlusKplus_isPthPower
        i hp_odd hp_three h_root

/-- **Canonical K⁺ Pollaczek root from the real Cor 8.19 bridge.**

This is the converse direction to the final source reduction: a proved
`Cor8_19Bridge` forces the canonical K⁺ preimage
`pollaczekUnitPlusKplus` to be a p-th power under `p ∣ h⁺`.  The proof first
uses the bridge contrapositively on the K-side real unit
`pollaczekUnitPlus`, then descends the p-th root from `𝓞 K` to `𝓞 K⁺` via
`FLT37.isPthPower_image_iff`. -/
theorem pollaczekUnitPlusKplus_isPthPower_of_cor8_19Bridge
    {p' : ℕ} [Fact p'.Prime] {K' : Type} [Field K'] [NumberField K']
    [IsCyclotomicExtension {p'} ℚ K'] [NumberField.IsCMField K']
    (i : ℕ) (hp_odd : p' ≠ 2) (hp_three : 3 ≤ p')
    (B : Cor8_19Bridge p' K' i)
    (h_dvd : (p' : ℕ) ∣ hPlus K') :
      ∃ β : (𝓞 (NumberField.maximalRealSubfield K'))ˣ,
        β ^ p' =
          Sinnott.pollaczekUnitPlusKplus p' K' i hp_odd hp_three := by
  let uPlus : (𝓞 (NumberField.maximalRealSubfield K'))ˣ :=
    Sinnott.pollaczekUnitPlusKplus p' K' i hp_odd hp_three
  have h_alg_eq :
      (algebraMap (𝓞 (NumberField.maximalRealSubfield K')) (𝓞 K')
        (uPlus : 𝓞 (NumberField.maximalRealSubfield K')) : 𝓞 K') =
      ((FLT37.pollaczekUnitPlus p' K' i : (𝓞 K')ˣ) : 𝓞 K') :=
    Sinnott.algebraMapPollaczekUnitPlusKplus_eq p' K' i hp_odd hp_three
  have h_image :
      ∃ α : (𝓞 K')ˣ,
        Units.map
          (algebraMap (𝓞 (NumberField.maximalRealSubfield K')) (𝓞 K')).toMonoidHom
          uPlus = α ^ p' := by
    by_contra h_no_image
    have h_no_k :
        ∀ α : (𝓞 K')ˣ,
          ((FLT37.pollaczekUnitPlus p' K' i : (𝓞 K')ˣ) : 𝓞 K') ≠
            ((α : (𝓞 K')ˣ) : 𝓞 K') ^ p' := by
      intro α hα
      apply h_no_image
      refine ⟨α, ?_⟩
      apply Units.ext
      change
        (algebraMap (𝓞 (NumberField.maximalRealSubfield K')) (𝓞 K')
          (uPlus : 𝓞 (NumberField.maximalRealSubfield K'))) =
          ((α ^ p' : (𝓞 K')ˣ) : 𝓞 K')
      rw [h_alg_eq]
      simpa [Units.val_pow_eq_pow_val] using hα
    exact (B.not_dvd_hPlus_of_not_isPthPower h_no_k) h_dvd
  obtain ⟨β, hβ⟩ :=
    (_root_.BernoulliRegular.FLT37.isPthPower_image_iff
      (p := p') (K := K') hp_odd uPlus).mp h_image
  exact ⟨β, hβ.symm⟩

/-- **Canonical K⁺ Pollaczek root from the refined Thaine bridge.**

The refined Thaine bridge is the source-faithful Pollaczek route: a concrete
eigenspace identification, a single-character Pollaczek/Thaine discharge, and
the reflection discharge for the other components.  Once those are available,
the exact root statement used by the final FLT37 assembly follows by the
already-proved `Cor8_19Bridge` adapter. -/
theorem pollaczekUnitPlusKplus_isPthPower_of_refinedThaineBridge
    {p' : ℕ} [Fact p'.Prime] {K' : Type} [Field K'] [NumberField K']
    [IsCyclotomicExtension {p'} ℚ K'] [NumberField.IsCMField K']
    (i : ℕ) (hp_odd : p' ≠ 2) (hp_three : 3 ≤ p')
    (B : FLT37UnitClassBridgeRefined p' K' i)
    (h_dvd : (p' : ℕ) ∣ hPlus K') :
      ∃ β : (𝓞 (NumberField.maximalRealSubfield K'))ˣ,
        β ^ p' =
          Sinnott.pollaczekUnitPlusKplus p' K' i hp_odd hp_three :=
  pollaczekUnitPlusKplus_isPthPower_of_cor8_19Bridge
    i hp_odd hp_three (cor8_19Bridge_of_refined (p := p') (K := K') B)
    h_dvd

/-- **FLT37 exact Pollaczek root source from the refined Thaine bridge.** -/
theorem flt37_pollaczekUnitPlusKplus_isPthPower_of_refinedThaineBridge
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (B : FLT37UnitClassBridgeRefined 37 (CyclotomicField 37 ℚ) 32)
    (h_dvd : (37 : ℕ) ∣ hPlus (CyclotomicField 37 ℚ)) :
      ∃ β : (𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ)))ˣ,
        β ^ 37 =
          Sinnott.pollaczekUnitPlusKplus 37 (CyclotomicField 37 ℚ) 32
            (by decide : (37 : ℕ) ≠ 2) (by decide : 3 ≤ 37) := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  exact
    pollaczekUnitPlusKplus_isPthPower_of_refinedThaineBridge
      (i := 32) (p' := 37) (K' := CyclotomicField 37 ℚ)
      (by decide : (37 : ℕ) ≠ 2) (by decide : 3 ≤ 37) B h_dvd

/-- **`PollaczekForward 37` from `Vandiver37PlusCoprime`** (vacuous under
the antecedent). Under `Vandiver37PlusCoprime` (the project's standard
hypothesis-form for `¬ 37 ∣ hPlus(K_37)`), the antecedent of
`PollaczekForward` (`37 ∣ hPlus K`) is false, so the implication
holds vacuously.

This closes `PollaczekForward 37 K 32` under the project's existing
hypothesis interface for the FLT37 plus-coprime claim. -/
theorem pollaczekForward_FLT37_of_vandiver37PlusCoprime
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (hp_three : 3 ≤ 37)
    (h_vandiver : FLT37.Vandiver37PlusCoprime) :
    haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
    Sinnott.PollaczekForward 37 (CyclotomicField 37 ℚ) 32
      (by decide : (37 : ℕ) ≠ 2) hp_three := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  intro h_dvd _ _ _
  exfalso
  exact FLT37.not_dvd_hPlus_thirtyseven_of_vandiver37PlusCoprime h_vandiver h_dvd

/-- **FLT37 `Cor8_19Bridge` from `Vandiver37PlusCoprime`**: composes
`pollaczekForward_FLT37_of_vandiver37PlusCoprime` with the project's
`cor8_19Bridge_of_pollaczekForward_full` to derive the Cor 8.19 bridge
under the project's standard `Vandiver37PlusCoprime` hypothesis. -/
theorem flt37_cor8_19Bridge_of_vandiver37PlusCoprime
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (hp_three : 3 ≤ 37)
    (h_vandiver : FLT37.Vandiver37PlusCoprime) :
    haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
    Cor8_19Bridge 37 (CyclotomicField 37 ℚ) 32 := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  exact Sinnott.cor8_19Bridge_closed 37 (CyclotomicField 37 ℚ) 32
    (by decide : (37 : ℕ) ≠ 2) hp_three
    (pollaczekForward_FLT37_of_vandiver37PlusCoprime hp_three h_vandiver)

/-- **FLT37 from `Vandiver37PlusCoprime` + remaining bridges**: composite
entry point. Under `Vandiver37PlusCoprime` (rules out `37 ∣ h⁺(K_37)`),
combined with the remaining bridges (caseI, noSecondOrderIrregular,
caseII), derives `FermatLastTheoremFor 37`.

This composes:
* `flt37_cor8_19Bridge_of_vandiver37PlusCoprime` (this file) → Cor8_19Bridge.
* The provided caseI, noSecondOrder, caseII bridges.
* Project's `FLT37BridgeBundle.ofRemaining` + `fermatLastTheoremFor_thirtyseven_of_bundle`.

This is the cleanest top-level entry point packaging all session ships
into a single FLT37 derivation. -/
theorem fermatLastTheoremFor_thirtyseven_of_vandiver37PlusCoprime_and_remaining
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (hp_three : 3 ≤ 37)
    (h_vandiver : FLT37.Vandiver37PlusCoprime)
    (caseI : CaseIBridge 37 (CyclotomicField 37 ℚ))
    (noSecondOrderIrregular : NoSecondOrderIrregularPair 37 32)
    (caseII : CaseIIBridge 37 (CyclotomicField 37 ℚ) 32) :
    FermatLastTheoremFor 37 :=
  fermatLastTheoremFor_thirtyseven_of_remaining
    (flt37_cor8_19Bridge_of_vandiver37PlusCoprime hp_three h_vandiver)
    caseI noSecondOrderIrregular caseII

end CaseI

end LehmerVandiver

end FLT37

end BernoulliRegular

end
