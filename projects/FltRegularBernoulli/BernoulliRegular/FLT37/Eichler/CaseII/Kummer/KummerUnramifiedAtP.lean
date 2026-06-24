import BernoulliRegular.FLT37.Eichler.CaseII.Kummer.KummerDifferentTrivial
import BernoulliRegular.FLT37.Eichler.CaseII.Kummer.PrimaryRadicalUnramified
import BernoulliRegular.FLT37.LehmerVandiver.CaseI.AKPrimarity

/-!
# [FLT37-CASEII-LEMMA-9.1-AT37] The "at 37" half of Washington Lemma 9.1

This file **proves** `CaseIIKummerUnramifiedAt37` (stated in
`CaseIIIdealKummerUnramifiedProof.lean`), the primary half of Washington Lemma 9.1: for a
**primary** radical `α : K = ℚ(ζ₃₇)` (`α ≡ 1 mod (ζ-1)^{37}`, witness form `(α-1)·c = (ζ-1)^{37}·N`,
`(ζ-1) ∤ c`), every prime `P` of `𝓞 L` (`L = K(α^{1/37})`) lying over the rational prime `37` is
unramified over `𝓞 K`.

## The integralization (turning the field radical `α` into an integral primary radical)

The target's `α : K` is a *field* element (non-integral in general).  The single-prime non-unit
unramifiedness tool `NonUnitKummer.isUnramifiedAt_local` needs an **integral, primary, non-`p`-th
power** radical `a : 𝓞 K`.  We integralize as follows.

* From the primary witness, `α·c = c + (ζ-1)^{37}·N ∈ 𝓞 K`, so the *denominator-witness* `c` already
  clears `α`'s denominator.
* `(ζ-1) ∤ c` and `span{ζ-1}` is a maximal ideal of the Dedekind domain `𝓞 K`, so
  `IsCoprime c (ζ-1)`: pick `s, t` with `s·c + t·(ζ-1) = 1` and set `γ := s·c ∈ 𝓞 K`.  Then `c ∣ γ`
  and
  `γ ≡ 1 mod (ζ-1)`.
* The integral radical is `a := γ^{37} + (ζ-1)^{37}·(N·s^{37}·c^{36}) ∈ 𝓞 K`.  Cleaning denominators
  shows `algebraMap a = α·γ^{37}`, so `a/α = γ^{37}` is a `37`-th power and the splitting fields of
  `X^{37} - C α` and `X^{37} - C a` agree (`isSplittingField_X_pow_sub_C_unit_of_unit_form`).  The
  identity also gives `a - 1 = (γ^{37} - 1) + (ζ-1)^{37}·(…)`, both summands divisible by
  `(ζ-1)^{37}` (the `(1+j)^{37} ≡ 1 mod (ζ-1)^{37}` congruence via `exists_add_pow_prime_eq` and
  `37 ~ (ζ-1)^{36}`), so `a` is primary; and `(ζ-1) ∤ a` (from `a ≡ 1 mod (ζ-1)`).

## The local consumer

`P` lies over `37`, equivalently over `(ζ-1)` (the unique ramified prime of `K/ℚ`), because
`37 ~ (ζ-1)^{36}` and `span{ζ-1}` is maximal: `P.under (𝓞 K) = span{ζ-1}`.  We split on whether
`X^{37} - C α` is irreducible (i.e. whether `α` — equivalently `a` — is a `37`-th power in `K`):

* **non-`37`-th power:** `X^{37} - C a` is irreducible; the splitting-field transfer puts
  `L = antiKummerLift K α` in the form required by `NonUnitKummer.isUnramifiedAt_local`, which gives
  `IsUnramifiedAt (𝓞 L) (span{ζ-1})`, transported to `Algebra.IsUnramifiedAt (𝓞 K) P` via the bridge
  `algebra_isUnramifiedAt_of_isUnramifiedAt`.
* **`37`-th power:** then `X^{37} - C α` splits over `K`, so `L = K`, `Module.finrank K L = 1`, and
  `ramificationIdx_le_finrank` forces `e(P) ≤ 1`; with `e(P) ≥ 1` this gives `e(P) = 1`, i.e.
  unramified.

It imports only; it does **not** modify any existing file.

## References
* Washington, *Introduction to Cyclotomic Fields*, GTM 83, §9.1 (Lemma 9.1, at-`p` half).
* flt-regular `FltRegular.NumberTheory.KummersLemma`,
  `MoreLemmas.associated_zeta_sub_one_pow_prime`.
-/

@[expose] public section

noncomputable section

open NumberField

namespace BernoulliRegular.FLT37.Eichler.CaseIIAt37

/-! ## 1. Arithmetic preliminaries over a cyclotomic ring `𝓞 K` (`p` prime, `p ≠ 2`)

These are radical-agnostic facts about the prime `(ζ-1)` of `𝓞 K`: that `span{ζ-1}` is maximal, that
`IsCoprime c (ζ-1)` when `(ζ-1) ∤ c`, and the congruence `(ζ-1) ∣ γ-1 ⟹ (ζ-1)^p ∣ γ^p - 1`. -/

section Arith

variable {K : Type*} {p : ℕ} [hpri : Fact p.Prime] [Field K] [NumberField K]
  [IsCyclotomicExtension {p} ℚ K] {ζ : K} (hζ : IsPrimitiveRoot ζ p)

omit [NumberField K] [IsCyclotomicExtension {p} ℚ K] in
/-- `ζ - 1 ≠ 0` (since `p > 1`). -/
lemma zeta_sub_one_ne_zero : (hζ.toInteger - 1 : 𝓞 K) ≠ 0 :=
  hζ.toInteger_isPrimitiveRoot.sub_one_ne_zero hpri.out.one_lt

/-- `span{ζ-1}` is a maximal ideal of `𝓞 K` (a nonzero prime ideal of the Dedekind domain `𝓞 K`). -/
lemma isMaximal_span_zeta_sub_one :
    (Ideal.span {(hζ.toInteger - 1 : 𝓞 K)}).IsMaximal := by
  haveI : Fact (Nat.Prime p) := hpri
  have hbot : (Ideal.span {(hζ.toInteger - 1 : 𝓞 K)}) ≠ ⊥ :=
    mt Ideal.span_singleton_eq_bot.mp (zeta_sub_one_ne_zero hζ)
  haveI : (Ideal.span {(hζ.toInteger - 1 : 𝓞 K)}).IsPrime :=
    (Ideal.span_singleton_prime (zeta_sub_one_ne_zero hζ)).mpr hζ.zeta_sub_one_prime'
  exact Ideal.IsPrime.isMaximal inferInstance hbot

omit [NumberField K] [IsCyclotomicExtension {p} ℚ K] in
/-- `span{ζ-1} ≠ ⊥`. -/
lemma span_zeta_sub_one_ne_bot :
    (Ideal.span {(hζ.toInteger - 1 : 𝓞 K)}) ≠ ⊥ :=
  mt Ideal.span_singleton_eq_bot.mp (zeta_sub_one_ne_zero hζ)

/-- **Coprimality from non-divisibility**: if `(ζ-1) ∤ c` then `c` and `ζ-1` are coprime in `𝓞 K`.
`span{ζ-1}` is maximal, and `c ∉ span{ζ-1}`, so `span{c} ⊔ span{ζ-1} = ⊤`. -/
lemma isCoprime_of_not_zeta_sub_one_dvd {c : 𝓞 K} (hc : ¬ (hζ.toInteger - 1 : 𝓞 K) ∣ c) :
    IsCoprime c (hζ.toInteger - 1 : 𝓞 K) := by
  haveI : Fact (Nat.Prime p) := hpri
  haveI hmax := isMaximal_span_zeta_sub_one hζ
  rw [← Ideal.isCoprime_span_singleton_iff]
  refine Ideal.coprime_of_no_prime_ge ?_
  intro P hcP hzP hP
  -- `span{ζ-1} ≤ P` with `span{ζ-1}` maximal forces `P = span{ζ-1}`; then `c ∈ P` contradicts `hc`.
  have hPeq : Ideal.span {(hζ.toInteger - 1 : 𝓞 K)} = P := hmax.eq_of_le hP.ne_top hzP
  have hcmem : c ∈ P := hcP (Ideal.mem_span_singleton_self c)
  rw [← hPeq, Ideal.mem_span_singleton] at hcmem
  exact hc hcmem

omit [NumberField K] [IsCyclotomicExtension {p} ℚ K] in
/-- **The `(1+j)^p ≡ 1 mod (ζ-1)^p` congruence** in element form: if `(ζ-1) ∣ γ - 1`, then
`(ζ-1)^p ∣ γ^p - 1`.  Via `exists_add_pow_prime_eq` (`γ^p = 1 + j^p + p·j·r`, `j = γ-1`) and
`p ~ (ζ-1)^{p-1}` (`associated_zeta_sub_one_pow_prime`). -/
lemma zeta_sub_one_pow_dvd_pow_sub_one {γ : 𝓞 K}
    (hγ : (hζ.toInteger - 1 : 𝓞 K) ∣ γ - 1) :
    (hζ.toInteger - 1 : 𝓞 K) ^ p ∣ γ ^ p - 1 := by
  haveI : Fact (Nat.Prime p) := hpri
  set ϖ : 𝓞 K := (hζ.toInteger - 1 : 𝓞 K) with hϖ
  set j : 𝓞 K := γ - 1 with hj
  have hγeq : γ = 1 + j := by rw [hj]; ring
  -- `γ^p = 1 + j^p + p·j·r`.
  obtain ⟨r, hr⟩ := exists_add_pow_prime_eq hpri.out (1 : 𝓞 K) j
  have hpow : γ ^ p - 1 = j ^ p + (p : 𝓞 K) * j * r := by
    rw [hγeq, hr]; ring
  rw [hpow]
  -- `ϖ^p ∣ j^p` since `ϖ ∣ j`; for the cross term, `ϖ^{p-1} ∣ p` and `ϖ ∣ j` give
  -- `ϖ^p = ϖ^{p-1}·ϖ ∣ p·j ∣ p·j·r`.
  refine dvd_add (pow_dvd_pow_of_dvd hγ p) ?_
  have hpdvd : ϖ ^ (p - 1) ∣ (p : 𝓞 K) := (associated_zeta_sub_one_pow_prime hζ).dvd
  have hsplit : ϖ ^ p = ϖ ^ (p - 1) * ϖ := by
    rw [← pow_succ, Nat.sub_add_cancel hpri.out.one_lt.le]
  rw [hsplit, mul_assoc]
  exact mul_dvd_mul hpdvd (Dvd.dvd.mul_right hγ r)

end Arith

/-! ## 2. The integral primary radical

From the field-level primary witness `(α-1)·c = (ζ-1)^p·N` with `(ζ-1) ∤ c`, we build an integral
`a : 𝓞 K` with `algebraMap a = α·γ^p` (`γ := s·c`, `s·c + t·(ζ-1) = 1`), which is primary
(`(ζ-1)^p ∣ a-1`), not divisible by `(ζ-1)`, and nonzero. -/

section Integralize

variable {K : Type*} {p : ℕ} [hpri : Fact p.Prime] [Field K] [NumberField K]
  [IsCyclotomicExtension {p} ℚ K] {ζ : K} (hζ : IsPrimitiveRoot ζ p)

/-- **The integral primary radical existence lemma.**  Given the field-level primary data — `α ∈ K`,
the denominator-witness `c : 𝓞 K` with `(ζ-1) ∤ c`, `N : 𝓞 K`, and the cross-multiplied identity
`(α-1)·c = (ζ-1)^p·N` in `K` — there is an integral `a : 𝓞 K` and a nonzero `γ : 𝓞 K` with:

* `algebraMap a = α·γ^p` (so `a/α = γ^p` is a `p`-th power: the splitting fields agree);
* `(ζ-1)^p ∣ a - 1` (`a` is primary);
* `¬ (ζ-1) ∣ a` (equivalently `a ∉ span{ζ-1}`).

`γ := s·c` for a Bézout pair `s·c + t·(ζ-1) = 1` (so `c ∣ γ` and `γ ≡ 1 mod (ζ-1)`), and
`a := γ^p + (ζ-1)^p·(N·s^p·c^{p-1})`. -/
lemma exists_integral_primary_radical (_hp : p ≠ 2) (α : K) {c N : 𝓞 K}
    (hc : ¬ (hζ.toInteger - 1 : 𝓞 K) ∣ c)
    (hform : (α - 1) * algebraMap (𝓞 K) K c =
      algebraMap (𝓞 K) K ((hζ.toInteger - 1 : 𝓞 K) ^ p * N)) :
    ∃ (a γ : 𝓞 K), γ ≠ 0 ∧
      algebraMap (𝓞 K) K a = α * algebraMap (𝓞 K) K γ ^ p ∧
      (hζ.toInteger - 1 : 𝓞 K) ^ p ∣ a - 1 ∧
      ¬ (hζ.toInteger - 1 : 𝓞 K) ∣ a := by
  haveI : Fact (Nat.Prime p) := hpri
  set ϖ : 𝓞 K := (hζ.toInteger - 1 : 𝓞 K) with hϖ
  -- Bézout: `s·c + t·ϖ = 1`.
  obtain ⟨s, t, hst⟩ := isCoprime_of_not_zeta_sub_one_dvd hζ hc
  -- `γ := s·c`.
  set γ : 𝓞 K := s * c with hγ_def
  have hγ_sub_one : ϖ ∣ γ - 1 := ⟨-t, by rw [hγ_def]; linear_combination hst⟩
  have hγ_ne : γ ≠ 0 := by
    -- If `γ = 0` then `ϖ ∣ γ - 1 = -1`, so `ϖ` is a unit — contradiction.
    intro h0
    refine hζ.zeta_sub_one_prime'.not_unit ?_
    refine isUnit_of_dvd_one (dvd_neg.mp ?_)
    have := hγ_sub_one; rwa [h0, zero_sub] at this
  -- The integral radical `a := γ^p + ϖ^p·(N·s^p·c^{p-1})`.
  set M : 𝓞 K := N * s ^ p * c ^ (p - 1) with hM_def
  set a : 𝓞 K := γ ^ p + ϖ ^ p * M with ha_def
  -- `ϖ^p ∣ a - 1 = (γ^p - 1) + ϖ^p·M` (primarity), used for both the congruence and `¬ ϖ ∣ a`.
  have ha_cong : ϖ ^ p ∣ a - 1 := by
    rw [ha_def, show γ ^ p + ϖ ^ p * M - 1 = (γ ^ p - 1) + ϖ ^ p * M by ring]
    exact dvd_add (zeta_sub_one_pow_dvd_pow_sub_one hζ hγ_sub_one) (Dvd.intro M rfl)
  refine ⟨a, γ, hγ_ne, ?_, ha_cong, ?_⟩
  · -- `algebraMap a = α·γ^p`.  Field identity from `hform`: `(α-1)·c = ϖ^p·N`.
    -- Split-map form of the primary witness.
    have hform' : (α - 1) * algebraMap (𝓞 K) K c =
        algebraMap (𝓞 K) K ϖ ^ p * algebraMap (𝓞 K) K N := by
      have := hform; rwa [map_mul, map_pow] at this
    -- Expand `algebraMap a`, `algebraMap γ`, `algebraMap M` with explicit factorizations.
    have hγK : algebraMap (𝓞 K) K γ =
        algebraMap (𝓞 K) K s * algebraMap (𝓞 K) K c := by
      rw [hγ_def, map_mul]
    have hMK : algebraMap (𝓞 K) K M =
        algebraMap (𝓞 K) K N * algebraMap (𝓞 K) K s ^ p *
          algebraMap (𝓞 K) K c ^ (p - 1) := by
      rw [hM_def, map_mul, map_mul, map_pow, map_pow]
    have haK : algebraMap (𝓞 K) K a =
        algebraMap (𝓞 K) K γ ^ p +
          algebraMap (𝓞 K) K ϖ ^ p * algebraMap (𝓞 K) K M := by
      rw [ha_def, map_add, map_mul, map_pow, map_pow]
    rw [haK, hγK, hMK, mul_pow]
    -- Rewrite `(algebraMap c)^p = (algebraMap c)·(algebraMap c)^{p-1}` to avoid symbolic-exp arith.
    have hBsplit : algebraMap (𝓞 K) K c ^ p =
        algebraMap (𝓞 K) K c * algebraMap (𝓞 K) K c ^ (p - 1) := by
      rw [← pow_succ', Nat.sub_add_cancel hpri.out.one_lt.le]
    rw [hBsplit]
    linear_combination
      (-(algebraMap (𝓞 K) K s ^ p * algebraMap (𝓞 K) K c ^ (p - 1))) * hform'
  · -- `¬ ϖ ∣ a`: `a ≡ 1 mod ϖ` (from `ϖ ∣ ϖ^p ∣ a - 1`), so `ϖ ∣ a ⟹ ϖ ∣ 1`.
    intro hdvd
    refine hζ.zeta_sub_one_prime'.not_unit (isUnit_of_dvd_one ?_)
    have ha1 : ϖ ∣ a - 1 := (dvd_pow_self ϖ hpri.out.ne_zero).trans ha_cong
    have : ϖ ∣ a - (a - 1) := dvd_sub hdvd ha1
    rwa [sub_sub_cancel] at this

end Integralize

/-! ## 3. The per-prime assembly (the "at-`p`" half of Washington Lemma 9.1)

For a primary radical `α` (field-level witness `(α-1)·c = (ζ-1)^p·N`, `(ζ-1) ∤ c`) and a prime `P`
of `𝓞 L` (`L = K(α^{1/p})`) lying over the rational prime `p` (`(p:𝓞 L) ∈ P`), `P` is unramified
over `𝓞 K`.

We integralize `α` to an integral primary radical `a = α·γ^p ∈ 𝓞 K`
(`exists_integral_primary_radical`), identify `P.under (𝓞 K) = span{ζ-1}` (the unique ramified prime
of `K/ℚ`, since `p ~ (ζ-1)^{p-1}`), and split on whether `X^p - C α` is irreducible:

* **irreducible:** the integral radical `a` is not a `p`-th power, so the splitting-field transfer
  `isSplittingField_X_pow_sub_C_unit_of_unit_form` puts `L` as `IsSplittingField K L (X^p - C a)`,
  and the non-unit primary unramifiedness `NonUnitKummer.isUnramifiedAt_local` (at `I = span{ζ-1}`,
  using `a ∉ I` and the primarity congruence) gives `IsUnramifiedAt (𝓞 L) (span{ζ-1})`, transported
  to `Algebra.IsUnramifiedAt (𝓞 K) P` via `algebra_isUnramifiedAt_of_isUnramifiedAt`;
* **reducible:** `X^p - C α` splits over `K`, so `Module.finrank K L = 1`, forcing the ramification
  index `e(P) ≤ 1`; with `e(P) ≥ 1` (Dedekind) this gives `e(P) = 1`, i.e. unramified. -/

section Assembly

open FLT37.LehmerVandiver.CaseI.AntiKummer FLT37.LehmerVandiver.CaseI

variable {K : Type} {p : ℕ} [hpri : Fact p.Prime] [Field K] [NumberField K]
  [IsCyclotomicExtension {p} ℚ K] [NumberField.IsCMField K] {ζ : K} (hζ : IsPrimitiveRoot ζ p)

omit [NumberField.IsCMField K] in
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1600000 in
-- The `antiKummerLift` splitting-field whnf and the `IsUnramifiedAt`/different-ideal coercions make
-- this assembly heavier than the default heartbeat budget.
/-- **The per-prime "at-`p`" unramifiedness from a field-level primary witness.**  For a primary
radical `α` (witness `(α-1)·c = (ζ-1)^p·N`, `(ζ-1) ∤ c`) and a prime `P` of `𝓞 L`
(`L = antiKummerLift K α`) over the rational prime `p` (`(p:𝓞 L) ∈ P`), `P` is unramified over
`𝓞 K`. -/
lemma isUnramifiedAt_of_primary_witness (hp : p ≠ 2) (α : K) (hα : α ≠ 0)
    {N c : 𝓞 K} (hc : ¬ (hζ.toInteger - 1 : 𝓞 K) ∣ c)
    (hform : (α - 1) * algebraMap (𝓞 K) K c =
      algebraMap (𝓞 K) K ((hζ.toInteger - 1 : 𝓞 K) ^ p * N))
    (P : Ideal (𝓞 (antiKummerLift (p := p) K α hα))) [P.IsPrime] (hP_bot : P ≠ ⊥)
    (hp_mem : (p : 𝓞 (antiKummerLift (p := p) K α hα)) ∈ P) :
    Algebra.IsUnramifiedAt (𝓞 K) P := by
  haveI : Fact (Nat.Prime p) := hpri
  have hp_pos : 0 < p := hpri.out.pos
  set L := antiKummerLift (p := p) K α hα with hL
  haveI : IsScalarTower (𝓞 K) (𝓞 L) L := IsScalarTower.of_algebraMap_eq' rfl
  haveI : NoZeroSMulDivisors (𝓞 K) (𝓞 L) := ⟨fun {c x} h => by
    rw [Algebra.smul_def, mul_eq_zero] at h
    rcases h with hc | hx
    · exact Or.inl ((map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 K) (𝓞 L))).mp hc)
    · exact Or.inr hx⟩
  have hK_prim : (primitiveRoots p K).Nonempty :=
    ⟨_, (mem_primitiveRoots hp_pos).mpr (IsCyclotomicExtension.zeta_spec p ℚ K)⟩
  -- Step 1: integral primary radical `a = α·γ^p ∈ 𝓞 K`.
  obtain ⟨a, γ, hγ_ne, ha_eq, ha_cong, ha_ndvd⟩ :=
    exists_integral_primary_radical hζ hp α hc hform
  have ha_ne : a ≠ 0 := fun h0 => ha_ndvd (h0 ▸ dvd_zero _)
  have hγK_ne : algebraMap (𝓞 K) K γ ≠ 0 :=
    (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 K) K)).mpr hγ_ne
  -- `a ∉ span{ζ-1}`.
  have haI : a ∉ Ideal.span {(hζ.toInteger - 1 : 𝓞 K)} := by
    rw [Ideal.mem_span_singleton]; exact ha_ndvd
  -- Step 2: `P.under (𝓞 K) = span{ζ-1}`.
  have hp_under : (p : 𝓞 K) ∈ P.under (𝓞 K) := by
    rw [Ideal.under_def, Ideal.mem_comap, map_natCast]; exact hp_mem
  have hpow_mem : (hζ.toInteger - 1 : 𝓞 K) ^ (p - 1) ∈ P.under (𝓞 K) := by
    obtain ⟨w, hw⟩ := (associated_zeta_sub_one_pow_prime hζ).symm.dvd
    rw [hw]; exact (P.under (𝓞 K)).mul_mem_right w hp_under
  have hzeta_mem : (hζ.toInteger - 1 : 𝓞 K) ∈ P.under (𝓞 K) :=
    Ideal.IsPrime.mem_of_pow_mem inferInstance _ hpow_mem
  have hP_under : P.under (𝓞 K) = Ideal.span {(hζ.toInteger - 1 : 𝓞 K)} := by
    refine ((isMaximal_span_zeta_sub_one hζ).eq_of_le
      (Ideal.IsPrime.ne_top inferInstance) ?_).symm
    rw [Ideal.span_le, Set.singleton_subset_iff]; exact hzeta_mem
  -- Maximality / nonzero-ness of `P.under (𝓞 K)` via the identification with `span{ζ-1}`.
  haveI hUnderMax : (P.under (𝓞 K)).IsMaximal := by
    rw [hP_under]; exact isMaximal_span_zeta_sub_one hζ
  have hUnderBot : P.under (𝓞 K) ≠ ⊥ := by
    rw [hP_under]; exact span_zeta_sub_one_ne_bot hζ
  haveI hLiesOver : P.LiesOver (P.under (𝓞 K)) := ⟨rfl⟩
  -- Base splitting-field instance from the `antiKummerLift` definition (`L` is defeq to it).
  haveI hSF0 : Polynomial.IsSplittingField K L (Polynomial.X ^ p - Polynomial.C α) :=
    inferInstanceAs (Polynomial.IsSplittingField K
      (Polynomial.SplittingField (Polynomial.X ^ p - Polynomial.C α)) _)
  -- Step 3: split on irreducibility of `X^p - C α`.
  by_cases h_irr : Irreducible (Polynomial.X ^ p - Polynomial.C α)
  · -- Irreducible case: `finrank K L = p`, splitting-field transfer + non-unit local unramified.
    have h_finrank : Module.finrank K L = p :=
      antiKummerLift_finrank_of_irreducible (K := K) (p := p) α hα h_irr
    -- `α = a · (γ⁻¹)^p` (field form for the transfer).
    have hα_form : α = algebraMap (𝓞 K) K a * (algebraMap (𝓞 K) K γ)⁻¹ ^ p := by
      rw [ha_eq, mul_assoc, ← mul_pow, mul_inv_cancel₀ hγK_ne, one_pow, mul_one]
    -- Transferred splitting-field instance for the integral radical.
    haveI hSF : Polynomial.IsSplittingField K L
        (Polynomial.X ^ p - Polynomial.C (algebraMap (𝓞 K) K a)) :=
      isSplittingField_X_pow_sub_C_unit_of_unit_form (K := K) (p := p) hp_pos hK_prim
        α (algebraMap (𝓞 K) K a) (algebraMap (𝓞 K) K γ)⁻¹
        (inv_ne_zero hγK_ne) hα_form h_finrank h_irr
    -- The non-`p`-th-power condition for the integral radical.
    have hu : ∀ v : K, v ^ p ≠ algebraMap (𝓞 K) K a := by
      intro v hv
      apply (X_pow_sub_C_irreducible_iff_of_prime hpri.out).mp h_irr (v * (algebraMap (𝓞 K) K γ)⁻¹)
      rw [mul_pow, hv, ha_eq, mul_assoc, ← mul_pow, mul_inv_cancel₀ hγK_ne, one_pow, mul_one]
    -- Non-unit single-prime unramifiedness at `span{ζ-1}`: every prime over it has `e = 1`.
    haveI hImax : (Ideal.span {(hζ.toInteger - 1 : 𝓞 K)}).IsMaximal :=
      isMaximal_span_zeta_sub_one hζ
    have hloc : ∀ Q ∈ (Ideal.span {(hζ.toInteger - 1 : 𝓞 K)}).primesOver (𝓞 L),
        Ideal.ramificationIdx (Ideal.span {(hζ.toInteger - 1 : 𝓞 K)}) Q = 1 :=
      NonUnitKummer.isUnramifiedAt_local hp hζ a ha_cong hu L ha_ne
        (Ideal.span {(hζ.toInteger - 1 : 𝓞 K)}) (span_zeta_sub_one_ne_bot hζ) haI
    -- Transport to `Algebra.IsUnramifiedAt (𝓞 K) P` via the per-prime bridge.
    refine algebra_isUnramifiedAt_of_isUnramifiedAt (K := K) (L := L) P hP_bot ?_
    rw [hP_under]; exact hloc
  · -- Reducible case: `α` is a `p`-th power, `X^p - C α` splits, `finrank K L = 1`.
    rw [X_pow_sub_C_irreducible_iff_of_prime hpri.out, not_forall] at h_irr
    obtain ⟨β, hβ⟩ := h_irr
    rw [not_not] at hβ
    have hsplits : (Polynomial.X ^ p - Polynomial.C α).Splits :=
      X_pow_sub_C_splits_of_isPrimitiveRoot hζ hβ
    have hfinrank1 : Module.finrank K L = 1 :=
      Subalgebra.bot_eq_top_iff_finrank_eq_one.mp
        ((Polynomial.IsSplittingField.splits_iff L (Polynomial.X ^ p - Polynomial.C α)).mp
          hsplits).symm
    -- `e(P) = 1` from `e(P) ≤ finrank = 1` and `e(P) ≠ 0`.
    have hle : Ideal.ramificationIdx (P.under (𝓞 K)) P ≤ Module.finrank K L :=
      Ideal.ramificationIdx_le_finrank (R := 𝓞 K) (S := 𝓞 L) (K := K) (L := L)
        (p := P.under (𝓞 K)) P
    have hne : Ideal.ramificationIdx (P.under (𝓞 K)) P ≠ 0 :=
      Ideal.IsDedekindDomain.ramificationIdx_ne_zero_of_liesOver P hUnderBot
    refine (Algebra.isUnramifiedAt_iff_of_isDedekindDomain hP_bot).mpr ?_
    rw [hfinrank1] at hle
    lia

end Assembly

end BernoulliRegular.FLT37.Eichler.CaseIIAt37

/-! ## 4. The final theorem: `CaseIIKummerUnramifiedAt37`

Instantiate the per-prime assembly at `p = 37`, `K = ℚ(ζ₃₇)`, matching the target predicate
(`hζ.toInteger - 1` is the integral-element form of `ζ - 1`, and `(37 : 𝓞 L)` is the
`OfNat`-form of `((37 : ℕ) : 𝓞 L)`). -/

namespace BernoulliRegular.FLT37.Eichler

open FLT37.LehmerVandiver.CaseI.AntiKummer

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1600000 in
-- The `antiKummerLift` splitting-field whnf at `p = 37` makes elaboration heavier than the default.
/-- **[FLT37-CASEII-LEMMA-9.1-AT37] The "at 37" half of Washington Lemma 9.1, proved.**

For a **primary** radical `α : K = ℚ(ζ₃₇)` (`α ≡ 1 mod (ζ-1)^{37}`, witness form
`(α-1)·c = (ζ-1)^{37}·N` with `(ζ-1) ∤ c`), every prime `P` of `𝓞 L` (`L = K(α^{1/37})`) lying over
the rational prime `37` is unramified over `𝓞 K`.  See
`CaseIIAt37.isUnramifiedAt_of_primary_witness` for the assembly. -/
theorem caseIIKummerUnramifiedAt37_proven : CaseIIKummerUnramifiedAt37 := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  intro α hα h_primary P _ hP_bot h37
  obtain ⟨ζ, hζ, N, c, hc, hform⟩ := h_primary
  refine CaseIIAt37.isUnramifiedAt_of_primary_witness (K := CyclotomicField 37 ℚ) (p := 37)
    hζ (by decide) α hα (N := N) (c := c) hc hform P hP_bot ?_
  -- `((37 : ℕ) : 𝓞 L) = (37 : 𝓞 L)`.
  rwa [Nat.cast_ofNat]

end BernoulliRegular.FLT37.Eichler

end
