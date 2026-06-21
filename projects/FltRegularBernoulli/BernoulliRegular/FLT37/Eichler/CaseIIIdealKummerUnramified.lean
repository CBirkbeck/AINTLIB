import BernoulliRegular.FLT37.Eichler.CaseIIRawRatioCongruence

/-!
# [FLT37-CASEII-IDEAL-KUMMER] The non-circular discharge of the Case-II II1 unramifiedness

This file attacks the **single remaining undischarged piece** of the Case-II II1 leaf,
`CaseIICorrectedRadicalUnramified37` (the corrected anti-Kummer radical generates an unramified
Kummer extension, Washington Lemma 9.1), by **breaking the circularity** that the prior `R1`
reduction (`caseII_correctedRadicalUnramified37_of_R1`) left in place.

## The circularity that was there

The prior reduction `caseII_correctedRadicalUnramified37_of_R1`
(`CaseIIRawRatioCongruence.lean`) reduced unramifiedness to the existence of the **integer
Washington unit form** `x + yη = (-η)·u·γ^{37}·(x + yη^{36})`.  That hypothesis is *circular*: the
unit form `α = u·γ^{37}` says `(α) = (γ)^{37}`, i.e. the fractional ideal
`𝔟 := 𝔞(η)/𝔞(η⁻¹)` (for which `(α) = 𝔟^{37}` holds **unconditionally**) is **principal** — which is
exactly the class equality `[𝔞(η)] = [𝔞(η⁻¹)]` we are trying to prove.

## What is discharged here, unconditionally (the circularity break)

Two facts are proved with **no** unit-form / class-equality input:

1. **Unconditional primarity** (`caseII_correctedRadical_sub_one_eq`,
   `caseII_correctedRadical_primary_witness`): the corrected radical
   `α = caseII_correctedRadical D η (caseII_correctionUnit η) = (-η)⁻¹·(x+yη)/(x+yη^{36})` satisfies
   `α ≡ 1 (mod (ζ-1)^{37})` — concretely, `α - 1 = algebraMap(-η⁻¹·(ζ-1)^{37m}·N) / algebraMap(c)`
   with `x + yη^{36} = (ζ-1)·c`, `¬(ζ-1) ∣ c` (so `c` is a `𝔭`-unit) and `N ∈ 𝓞 K`.  This is read
   straight off the **unconditional** `caseII_raw_ratio_numerator_congr` (Washington Lemma 9.1's
   integer congruence) and the sharp denominator valuation `v_𝔭(x+yη^{36}) = 1`
   (`caseII_etaInv_denom_factor`).  `m ≥ 1` gives `37m ≥ 37`.  **No unit form is used.**

2. **Unconditional ideal-`p`-th-power structure** (`caseII_correctedRadical_fractionalIdeal_eq`):
   `spanSingleton α = (𝔞(η)/𝔞(η⁻¹))^{37}` as fractional ideals (the unit `-η` and the `𝔪·𝔭`
   common factors drop), with **no** assertion that `𝔞(η)/𝔞(η⁻¹)` is principal.

## The genuine, non-circular residual

What is *not* in flt-regular is **Washington Lemma 9.1 in its ideal form**: a primary radical whose
fractional ideal is a `p`-th power generates an unramified Kummer extension.  flt-regular's
`KummersLemma.isUnramified` is stated only for a radical that is a **unit** times a `p`-th power
(`Field.lean`, via `separable_poly_aux`'s `IsUnit (⟨α,_⟩ : 𝓞 L)` step), i.e. it *presupposes* the
principal generator — the circular input.  We isolate the missing local content as
`CaseIIIdealKummerUnramified37`: the *ideal-theoretic* Lemma 9.1, taking the ideal-`p`-th-power
**as a fractional ideal `𝔟`** (never asserting `𝔟` principal — this is what makes it verifiably
non-circular), with the primarity **discharged** (supplied by fact 1 above).  From it, fact 1 + fact
2 prove `CaseIICorrectedRadicalUnramified37`, hence (via the prior chain)
`CaseIIRootClassConjFixed37` and the `c = 1` real-data collapse.

It imports only `CaseIIRawRatioCongruence.lean`; it does **not** modify any existing file.

## References
* Washington, *Introduction to Cyclotomic Fields*, GTM 83, §9.1 (Lemma 9.1, Lemma 9.2), Thm 9.4.
-/

@[expose] public section

noncomputable section

open NumberField IsCyclotomicExtension Polynomial NumberField.IsCMField
open scoped nonZeroDivisors

namespace BernoulliRegular.FLT37.Eichler

open FLT37.LehmerVandiver.CaseII

variable {K : Type} [Field K] [NumberField K] [IsCyclotomicExtension {37} ℚ K]
  [NumberField.IsCMField K]

variable {m : ℕ}

/-! ## 1. The unconditional primarity of the corrected radical (the circularity break)

The corrected radical `α = (-η)⁻¹·(x+yη)/(x+yη^{36})` satisfies `α ≡ 1 (mod (ζ-1)^{37})`, proved
with **no** unit form.  The proof: from the exact identity, `α - 1` has numerator
`(x+yη) - (-η)·(x+yη^{36}) = (x+y)·(1+η)`, divisible by `(ζ-1)^{37m+1}`
(`caseII_raw_ratio_numerator_congr`), over the denominator `x+yη^{36} = (ζ-1)·c` (`v_𝔭 = 1`).  One
`(ζ-1)` cancels, leaving `(ζ-1)^{37m}` with `m ≥ 1`. -/

/-- **The exact `(α - 1)` field identity over `𝓞 K`.** Writing `α = (-η)⁻¹·(x+yη)/(x+yη^{36})`, the
numerator of `α - 1` is `(-η)⁻¹·[(x+yη) - (-η)·(x+yη^{36})]`, the **unconditional**
`caseII_raw_ratio_numerator` quantity.  Concretely, with `D₃₆ := x + yη^{36} ≠ 0`,

  `(α - 1) · algebraMap D₃₆ = algebraMap ((-η)⁻¹·((x+yη) - (-η)·(x+yη^{36})))`.

No unit form, no class equality. -/
theorem caseII_correctedRadical_sub_one_mul (D : RealCaseIIData37 K m) (hp : (37 : ℕ) ≠ 2)
    (η : nthRootsFinset 37 (1 : 𝓞 K)) :
    (caseII_correctedRadical D η (caseII_correctionUnit η) - 1) *
        algebraMap (𝓞 K) K (D.x + D.y * (η : 𝓞 K) ^ 36) =
      algebraMap (𝓞 K) K
        ((((caseII_correctionUnit η)⁻¹ : (𝓞 K)ˣ) : 𝓞 K) *
          ((D.x + D.y * (η : 𝓞 K)) - (-(η : 𝓞 K)) * (D.x + D.y * (η : 𝓞 K) ^ 36))) := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  have hden_ne := caseII_algebraMap_x_add_y_etaInv_ne_zero D hp η
  rw [caseII_correctedRadical, caseII_rootRatioK]
  -- inverse of `algebraMap u₀` is `algebraMap u₀⁻¹`.
  have hinv : (algebraMap (𝓞 K) K (caseII_correctionUnit η : 𝓞 K))⁻¹ =
      algebraMap (𝓞 K) K (((caseII_correctionUnit η)⁻¹ : (𝓞 K)ˣ) : 𝓞 K) :=
    (map_units_inv (algebraMap (𝓞 K) K) (caseII_correctionUnit η)).symm
  -- the key unit relation `algebraMap(u₀⁻¹) · algebraMap(η) = -1` (since `u₀⁻¹ = -(η^36)`).
  have hrel : algebraMap (𝓞 K) K (((caseII_correctionUnit η)⁻¹ : (𝓞 K)ˣ) : 𝓞 K) *
      algebraMap (𝓞 K) K (η : 𝓞 K) = -1 := by
    have h37 : (η : 𝓞 K) ^ 37 = 1 := (mem_nthRootsFinset (by norm_num) _).mp η.2
    rw [caseII_correctionUnit_inv_val, map_neg, neg_mul, ← map_mul, ← pow_succ, h37, map_one]
  rw [hinv]
  simp only [map_mul, map_sub, map_neg]
  rw [sub_mul, one_mul, mul_assoc, div_mul_cancel₀ _ hden_ne]
  linear_combination
    (-algebraMap (𝓞 K) K (D.x + D.y * (η : 𝓞 K) ^ 36)) * hrel

/-- **[FLT37-CASEII-CIRCULARITY-BREAK] The unconditional primarity witness.**

For every real Case-II datum `D` and adjacent root `η ≠ η₀`, the corrected radical
`α = caseII_correctedRadical D η (caseII_correctionUnit η)` satisfies `α ≡ 1 (mod (ζ-1)^{37})` in
the precise sense: there exist `N, c ∈ 𝓞 K` with

  `¬(ζ-1) ∣ c`   (so `c` is a `𝔭`-unit, `v_𝔭(c) = 0`), and
  `(α - 1) · algebraMap c = algebraMap ((ζ-1)^{37} · N)`.

Hence `v_𝔭(α - 1) = v_𝔭((ζ-1)^{37}·N) - v_𝔭(c) ≥ 37` — the Washington Lemma 9.1 primarity.

**This is the circularity break.**  It is read off the *unconditional*
`caseII_raw_ratio_numerator_congr` (the integer congruence `(ζ-1)^{37m+1} ∣ (x+yη)-(-η)(x+yη^{36})`)
and the sharp denominator valuation `v_𝔭(x+yη^{36}) = 1` (`caseII_etaInv_denom_factor`), with
`m ≥ 1` (`RealCaseIIData37.one_le_m`).  **No integer/field unit form `α = u·γ^{37}` is used** — so
this does *not* presuppose `𝔞(η)/𝔞(η⁻¹)` principal (the class equality). -/
theorem caseII_correctedRadical_primary_witness (D : RealCaseIIData37 K m) (hp : (37 : ℕ) ≠ 2)
    (η : nthRootsFinset 37 (1 : 𝓞 K)) (hη : η ≠ D.etaZero) :
    ∃ N c : 𝓞 K, ¬ (D.hζ.toInteger - 1 : 𝓞 K) ∣ c ∧
      (caseII_correctedRadical D η (caseII_correctionUnit η) - 1) * algebraMap (𝓞 K) K c =
        algebraMap (𝓞 K) K ((D.hζ.toInteger - 1 : 𝓞 K) ^ 37 * N) := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  set π : 𝓞 K := (D.hζ.toInteger - 1 : 𝓞 K)
  have hπ_ne : π ≠ 0 := D.hζ.zeta_sub_one_prime'.ne_zero
  -- denominator factorisation `x + yη^{36} = π·c`, `¬π ∣ c` (v_𝔭 = 1 exactly).
  obtain ⟨c, hc, hπ_not_dvd_c⟩ := caseII_etaInv_denom_factor D hp η hη
  -- raw numerator divisibility `π^{37m+1} ∣ (x+yη) - (-η)·(x+yη^{36})`.
  obtain ⟨M, hM⟩ := caseII_raw_ratio_numerator_congr D hp η
  -- the exact field identity from part 1.
  have hfield := caseII_correctedRadical_sub_one_mul D hp η
  -- substitute `x+yη^{36} = π·c` and the raw numerator into the field identity, cancel one `π`.
  -- `m ≥ 1` ⟹ `37m + 1 = 37 + (37·(m-1) + 1)`, so `π^{37m+1} = π^{37} · π^{37·(m-1)+1}`.
  have hm : 1 ≤ m := D.toCaseIIData37.one_le_m
  set α := caseII_correctedRadical D η (caseII_correctionUnit η)
  -- witness `N := (-η)⁻¹ · π^{37·(m-1)} · M`, after cancelling one `π` from numerator and denom.
  refine ⟨(((caseII_correctionUnit η)⁻¹ : (𝓞 K)ˣ) : 𝓞 K) * π ^ (37 * (m - 1)) * M, c,
    hπ_not_dvd_c, ?_⟩
  have hπK_ne : algebraMap (𝓞 K) K π ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 K) K)]; exact hπ_ne
  have hpow : (37 : ℕ) * m + 1 = 37 + (37 * (m - 1) + 1) := by
    omega
  -- Prove the `·algebraMap π`-multiplied equation (it equals `hfield` after `x+yη^{36} = π·c`),
  -- then cancel the nonzero `algebraMap π`.
  apply mul_right_cancel₀ hπK_ne
  -- LHS·algebraMap π = (α-1)·algebraMap(π·c) = algebraMap(u₀⁻¹·rawnum) (via hfield, hc).
  -- RHS·algebraMap π = algebraMap(π^{37}·N · π).
  have hLHS : (α - 1) * algebraMap (𝓞 K) K c * algebraMap (𝓞 K) K π =
      algebraMap (𝓞 K) K
        ((((caseII_correctionUnit η)⁻¹ : (𝓞 K)ˣ) : 𝓞 K) * (π ^ (37 * m + 1) * M)) := by
    have : (α - 1) * algebraMap (𝓞 K) K c * algebraMap (𝓞 K) K π =
        (α - 1) * algebraMap (𝓞 K) K (D.x + D.y * (η : 𝓞 K) ^ 36) := by
      rw [hc, map_mul]; ring
    rw [this, hfield, hM, map_mul, map_mul]
  rw [hLHS, ← map_mul]
  -- both sides as `algebraMap` of `𝓞 K`-elements; reduce to a `𝓞 K` equation and `ring` with hpow.
  congr 1
  rw [hpow, pow_add, pow_add, pow_one]
  ring

/-! ## 2. The unconditional ideal-`p`-th-power structure of the corrected radical

`spanSingleton α = (𝔞(η)/𝔞(η⁻¹))^{37}` as fractional ideals, where `𝔞(η)` is the Washington root
ideal `rootDivZetaSubOneDvdGcd`.  The unit `-η` and the common `𝔪·𝔭` factors of numerator and
denominator drop.  **No principality** of `𝔞(η)/𝔞(η⁻¹)` is asserted. -/

/-- **The corrected radical's fractional ideal is the `37`-th power of `𝔞(η)/𝔞(η⁻¹)`.**

`spanSingleton α = (coeIdeal 𝔞(η) / coeIdeal 𝔞(η⁻¹))^{37}` where `α = (-η)⁻¹·(x+yη)/(x+yη^{36})` and
`𝔞(ν) = rootDivZetaSubOneDvdGcd … ν`.  Proof: the unit `(-η)⁻¹` drops at the span level; the
Washington factorisations `(x+yη) = 𝔪·𝔠(η)·𝔭`, `(x+yη^{36}) = 𝔪·𝔠(η⁻¹)·𝔭` and `𝔠(ν) = 𝔞(ν)^{37}`
turn the ratio into `𝔞(η)^{37}/𝔞(η⁻¹)^{37} = (𝔞(η)/𝔞(η⁻¹))^{37}`, the common `𝔪·𝔭` cancelling.

This is the **unconditional** ideal-`p`-th-power structure feeding Washington Lemma 9.1; it does
**not** require `𝔞(η)/𝔞(η⁻¹)` to be principal. -/
theorem caseII_correctedRadical_fractionalIdeal_eq (D : RealCaseIIData37 K m) (hp : (37 : ℕ) ≠ 2)
    (η : nthRootsFinset 37 (1 : 𝓞 K)) :
    FractionalIdeal.spanSingleton (𝓞 K)⁰
        (caseII_correctedRadical D η (caseII_correctionUnit η)) =
      ((rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy η :
          FractionalIdeal (𝓞 K)⁰ K) /
        (rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy (caseII_etaInv η) :
          FractionalIdeal (𝓞 K)⁰ K)) ^ 37 := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  have hden_ne := caseII_algebraMap_x_add_y_etaInv_ne_zero D hp η
  -- `α = algebraMap((-η)⁻¹·(x+yη)) / algebraMap(x+yη^{36})`.
  have hα_div : caseII_correctedRadical D η (caseII_correctionUnit η) =
      algebraMap (𝓞 K) K
        (((caseII_correctionUnit η)⁻¹ : (𝓞 K)ˣ) * (D.x + D.y * (η : 𝓞 K))) /
      algebraMap (𝓞 K) K (D.x + D.y * (η : 𝓞 K) ^ 36) := by
    rw [caseII_correctedRadical, caseII_rootRatioK, map_mul,
      map_units_inv (algebraMap (𝓞 K) K) (caseII_correctionUnit η)]
    field_simp
  rw [hα_div, ← FractionalIdeal.spanSingleton_div_spanSingleton,
    ← FractionalIdeal.coeIdeal_span_singleton, ← FractionalIdeal.coeIdeal_span_singleton]
  -- unit `(-η)⁻¹` drops: `span{(-η)⁻¹·(x+yη)} = span{x+yη}`.
  rw [Ideal.span_singleton_mul_left_unit (caseII_correctionUnit η)⁻¹.isUnit]
  -- Name the integral ideals so the coercions fold cleanly.
  set Im : Ideal (𝓞 K) := gcd (Ideal.span {D.x}) (Ideal.span {D.y}) with hIm
  set Ip : Ideal (𝓞 K) := Ideal.span {(D.hζ.toInteger - 1 : 𝓞 K)} with hIp
  set Aη : Ideal (𝓞 K) := rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy η with hAη
  set Aι : Ideal (𝓞 K) := rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy (caseII_etaInv η)
    with hAι
  -- Washington factorisations and `𝔠 = 𝔞^{37}`.
  have hnum : Ideal.span ({D.x + D.y * (η : 𝓞 K)} : Set (𝓞 K)) = Im * Aη ^ 37 * Ip := by
    rw [hIm, hAη, hIp, ← m_mul_c_mul_p hp D.hζ D.equation D.hy η,
      ← root_div_zeta_sub_one_dvd_gcd_spec hp D.hζ D.equation D.hy η]
  have hden : Ideal.span ({D.x + D.y * (η : 𝓞 K) ^ 36} : Set (𝓞 K)) = Im * Aι ^ 37 * Ip := by
    have h := m_mul_c_mul_p hp D.hζ D.equation D.hy (caseII_etaInv η)
    rw [caseII_etaInv_coe] at h
    rw [hIm, hAι, hIp, ← h, ← root_div_zeta_sub_one_dvd_gcd_spec hp D.hζ D.equation D.hy
      (caseII_etaInv η)]
  rw [hnum, hden, div_pow]
  -- Normalise all `coeIdeal` of products/powers.
  simp only [FractionalIdeal.coeIdeal_mul, FractionalIdeal.coeIdeal_pow]
  -- Cancel the common nonzero `↑Im·↑Ip` from numerator and denominator.
  have h𝔪_ne : (Im : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 := by
    rw [Ne, FractionalIdeal.coeIdeal_eq_zero, ← Ideal.zero_eq_bot, hIm]
    exact m_ne_zero D.hζ D.hy
  have h𝔭_ne : (Ip : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 := by
    rw [Ne, FractionalIdeal.coeIdeal_eq_zero, ← Ideal.zero_eq_bot, hIp]
    exact p_ne_zero D.hζ
  have hreshape : ∀ Z : FractionalIdeal (𝓞 K)⁰ K,
      (Im : FractionalIdeal (𝓞 K)⁰ K) * Z ^ 37 * (Ip : FractionalIdeal (𝓞 K)⁰ K) =
        ((Im : FractionalIdeal (𝓞 K)⁰ K) * (Ip : FractionalIdeal (𝓞 K)⁰ K)) * Z ^ 37 :=
    fun Z => by ring
  rw [hreshape (Aη : FractionalIdeal (𝓞 K)⁰ K), hreshape (Aι : FractionalIdeal (𝓞 K)⁰ K),
    mul_div_mul_left _ _ (mul_ne_zero h𝔪_ne h𝔭_ne)]

/-! ## 3. The genuine, non-circular residual: the ideal-theoretic Kummer Lemma 9.1

flt-regular's `KummersLemma.isUnramified` only handles a radical that is a **unit** times a `p`-th
power (its proof, in `Field.lean`'s `separable_poly_aux`, hinges on `IsUnit (⟨α,_⟩ : 𝓞 L)`).  The
Case-II corrected radical `α = (-η)⁻¹·(x+yη)/(x+yη^{36})` is *not* a unit; its fractional ideal is
`𝔟^{37}` with `𝔟 = 𝔞(η)/𝔞(η⁻¹)` **not known to be principal** (that is the class equality we are
proving).  Washington Lemma 9.1 in its ideal form — primary radical with ideal a `p`-th power ⟹
unramified — is the missing local content.  We state it taking the ideal-`p`-th-power **as a
fractional ideal `𝔟`** (existentially), with **no** principality assertion; this is what makes it
verifiably non-circular, and both its hypotheses are *discharged* above for the corrected radical
(primarity by `caseII_correctedRadical_primary_witness`, ideal structure by
`caseII_correctedRadical_fractionalIdeal_eq`). -/

/-- **[FLT37-CASEII-LEMMA-9.1-IDEAL] The ideal-theoretic Kummer unramifiedness (Washington Lemma
9.1).**

For a radical `α : K`, `α ≠ 0`, that is **primary** (`α ≡ 1 mod (ζ-1)^{37}`, in the witness form
`(α-1)·algebraMap c = algebraMap ((ζ-1)^{37}·N)` with `¬(ζ-1) ∣ c`) and whose fractional ideal
`spanSingleton α` is a `37`-th power `𝔟^{37}` of **some** fractional ideal `𝔟`, the anti-Kummer
extension `K(α^{1/37})/K` is **unramified** over `𝓞 K`.

This is the genuine missing local content (flt-regular's `KummersLemma.isUnramified` requires the
radical to be a **unit** times a `p`-th power, i.e. presupposes `𝔟` principal — the circular input).
It is **non-circular**: `𝔟` is an arbitrary fractional ideal, **never** asserted principal.  Stated
as a named `def … : Prop` (not an axiom) over `CyclotomicField 37 ℚ`. -/
def CaseIIIdealKummerUnramified37
    [NumberField.IsCMField (CyclotomicField 37 ℚ)] : Prop :=
  ∀ (α : CyclotomicField 37 ℚ) (hα : α ≠ 0),
    (∃ (ζ : CyclotomicField 37 ℚ) (hζ : IsPrimitiveRoot ζ 37)
        (N c : 𝓞 (CyclotomicField 37 ℚ)), ¬ (hζ.toInteger - 1 : 𝓞 _) ∣ c ∧
        (α - 1) * algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) c =
          algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ)
            ((hζ.toInteger - 1 : 𝓞 _) ^ 37 * N)) →
    (∃ 𝔟 : FractionalIdeal (𝓞 (CyclotomicField 37 ℚ))⁰ (CyclotomicField 37 ℚ),
        FractionalIdeal.spanSingleton (𝓞 (CyclotomicField 37 ℚ))⁰ α = 𝔟 ^ 37) →
    Algebra.Unramified (𝓞 (CyclotomicField 37 ℚ))
      (𝓞 (FLT37.LehmerVandiver.CaseI.AntiKummer.antiKummerLift (p := 37)
        (CyclotomicField 37 ℚ) α hα))

/-! ## 4. The discharge: `CaseIICorrectedRadicalUnramified37` from the ideal-theoretic Lemma 9.1

Both hypotheses of `CaseIIIdealKummerUnramified37` are now **proved** for the corrected radical
(facts 1, 2).  Feeding them in discharges `CaseIICorrectedRadicalUnramified37` with the **proved**
anti-fixed correction unit `u₀ = caseII_correctionUnit η`.  The reduction
`caseIIRootRatioUnitPthPower37_of_correctedRadicalUnramified` (prior chain) then turns it into the
class equality `CaseIIRootClassConjFixed37` and the `c = 1` real-data collapse — **all** under the
single, non-circular residual `CaseIIIdealKummerUnramified37`. -/

/-- **[FLT37-CASEII-CIRCULARITY-BROKEN] `CaseIICorrectedRadicalUnramified37` from the
ideal-theoretic Lemma 9.1, with primarity and ideal structure discharged.**

The prior reduction `caseII_correctedRadicalUnramified37_of_R1` required the **circular** integer
unit form `x+yη = (-η)·u·γ^{37}·(x+yη^{36})` (⟺ `𝔞(η)/𝔞(η⁻¹)` principal ⟺ the class equality).  This
discharge replaces it by the strictly-more-primitive, **non-circular**
`CaseIIIdealKummerUnramified37` (the ideal-theoretic Washington Lemma 9.1): for the corrected
radical, the **primarity** is the *unconditional* `caseII_correctedRadical_primary_witness` and the
**ideal-`p`-th-power** is the *unconditional* `caseII_correctedRadical_fractionalIdeal_eq` — neither
presupposes the class equality.  The anti-fixed correction unit `u₀ = caseII_correctionUnit η` is
the proved `caseII_correctionUnit_anti`. -/
theorem caseII_correctedRadicalUnramified37_of_idealKummer
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (h_ideal : CaseIIIdealKummerUnramified37) :
    CaseIICorrectedRadicalUnramified37 := by
  intro m D η hη
  have hp : (37 : ℕ) ≠ 2 := by decide
  -- the correction unit `u₀ = -η`, anti-fixed.
  refine ⟨caseII_correctionUnit η, caseII_correctionUnit_anti η, ?_⟩
  set α := caseII_correctedRadical D η (caseII_correctionUnit η)
  have hα_ne : α ≠ 0 :=
    caseII_correctedRadical_ne_zero D hp η (caseII_correctionUnit η)
  -- Fact 1: the unconditional primarity witness.
  obtain ⟨N, c, hc_not_dvd, hc_eq⟩ :=
    caseII_correctedRadical_primary_witness D hp η hη
  -- Fact 2: the unconditional ideal-`37`-th-power structure.
  have hideal : FractionalIdeal.spanSingleton (𝓞 (CyclotomicField 37 ℚ))⁰ α =
      ((rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy η :
          FractionalIdeal (𝓞 (CyclotomicField 37 ℚ))⁰ (CyclotomicField 37 ℚ)) /
        (rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy
            (caseII_etaInv η) :
          FractionalIdeal (𝓞 (CyclotomicField 37 ℚ))⁰ (CyclotomicField 37 ℚ))) ^ 37 :=
    caseII_correctedRadical_fractionalIdeal_eq D hp η
  -- Apply the ideal-theoretic Lemma 9.1.
  exact h_ideal α hα_ne
    ⟨D.ζ, D.hζ, N, c, hc_not_dvd, hc_eq⟩
    ⟨_, hideal⟩

/-! ## 5. The full Case-II II1 chain and FLT-37 endpoint, on the single non-circular residual

Composing the discharge with the prior proven chain
(`caseIIRootClassConjFixed37_of_correctedRadicalUnramified`,
`fermatLastTheoremFor_thirtyseven_of_lemma91Residual`), the Washington Lemma 9.2 class consequence
`CaseIIRootClassConjFixed37` and FLT for `37` rest on the **single, non-circular** residual
`CaseIIIdealKummerUnramified37` (the ideal-theoretic Lemma 9.1), replacing the previously-circular
unit-form input. -/

/-- **`CaseIIRootClassConjFixed37` from the ideal-theoretic Lemma 9.1.**

The class equality `[𝔞(η)] = [𝔞(η⁻¹)]` (over real data) — and hence the `c = 1` real-data collapse
(`caseII_real_anchored_class_trivial_of_classConjFixed`) — follows from the **single non-circular**
residual `CaseIIIdealKummerUnramified37`, via the discharge
`caseII_correctedRadicalUnramified37_of_idealKummer` (primarity + ideal structure both discharged)
and the prior chain `caseIIRootClassConjFixed37_of_correctedRadicalUnramified`. -/
theorem caseIIRootClassConjFixed37_of_idealKummer
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (h_ideal : CaseIIIdealKummerUnramified37) :
    CaseIIRootClassConjFixed37 :=
  caseIIRootClassConjFixed37_of_correctedRadicalUnramified
    (caseII_correctedRadicalUnramified37_of_idealKummer h_ideal)

/-- **Fermat's Last Theorem for `37` from the single non-circular ideal-theoretic Lemma 9.1
residual** (plus the other already-isolated Case-II inputs and the second-order Bernoulli Prop).

The maximally-reduced Case-II II1 endpoint with the circularity broken: the Washington Lemma 9.2
class consequence is now proved from the **strictly-more-primitive, non-circular**
`CaseIIIdealKummerUnramified37` (the ideal-theoretic Lemma 9.1, taking the ideal-`p`-th-power as an
arbitrary fractional ideal, never principal) — with primarity and ideal structure **discharged
unconditionally** (`caseII_correctedRadical_primary_witness`,
`caseII_correctedRadical_fractionalIdeal_eq`).  This replaces the `caseII_lemma91`
(`CaseIICorrectedRadicalUnramified37`) input of
`fermatLastTheoremFor_thirtyseven_of_lemma91Residual`, whose only discharge route
(`caseII_correctedRadicalUnramified37_of_R1`) was circular. -/
theorem fermatLastTheoremFor_thirtyseven_of_idealKummerResidual
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (caseII_idealKummer : CaseIIIdealKummerUnramified37)
    (caseII_realDescent : CaseIIRealSingleRootDescentPreservesReality37)
    (caseII_leadingExp : LeadingExponentEigenCollapse37)
    (caseII_localPow : Lemma98LocalPower37)
    (noSecondOrderIrregular : NoSecondOrderIrregularPair 37 32) :
    FermatLastTheoremFor 37 :=
  fermatLastTheoremFor_thirtyseven_of_lemma91Residual
    (caseII_correctedRadicalUnramified37_of_idealKummer caseII_idealKummer)
    caseII_realDescent caseII_leadingExp caseII_localPow noSecondOrderIrregular

end BernoulliRegular.FLT37.Eichler

end
