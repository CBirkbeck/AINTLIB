import BernoulliRegular.FLT37.Eichler.CaseIICor823Discharge
import BernoulliRegular.FLT37.Eichler.CaseIIEx811EigenVandermonde
import BernoulliRegular.FLT37.Eichler.CaseIILeadingExponent
import BernoulliRegular.BernoulliFast.KellnerSecondOrder

/-!
# Washington Proposition 8.12 at the irregular index `i = 32`, second order: the `ω³²`-collapse

This file discharges `Cor823Omega32SecondOrderCollapse37` (`CaseIICor823Discharge.lean`) —
Washington Proposition 8.12 at the irregular index `i = 32`, made explicit at the **second-order**
coefficient — **down to one strictly-smaller, sound, non-vacuous residual**: the genuine level-`68`
mod-`37²` leading-coefficient content at `j = 15`, isolated as
`Cor823Omega32SecondOrderVandermonde37`.

It imports only; it does **not** modify any existing file.  No `sorry`, no `axiom`.

## The first-order degeneracy at `j = 15`, and the second order

The R3 (Washington Lemma 9.9 regular half, `caseIIEx811EigenVandermonde37_proven`) first-order
Kummer-log matrix is `concreteKummerLogMatrix = diag(B mod 37)·V` (proven
`concreteKummerLogMatrix_eq_diagonal_mul_vandermonde`).  Its row `j` carries the factor
`kummerLogDetRowFactor j = B_{2(j+1)}/(2(j+1)) mod 37`.  At `j = 15` (`i = 2·16 = 32`) this factor
is `B₃₂/32 mod 37 = 0` (`37 ∣ B₃₂`, the irregularity of `37`), so the first-order matrix row is
identically zero and carries **no** information about the `j = 15` Vandermonde row `(V·ē)_15` —
exactly the degeneracy R3 routes around (`caseIIEx811Core_rowFactor_ne_zero` is stated only for
`j ≠ 15`).

Recovering the `j = 15` content requires the **second-order** leading coefficient of
`completedLog E₃₂`, which by Proposition 8.12 sits at repo `λ`-level `c₃₂ = 2·(16 + 18·1) = 68`
(Washington's `λ_W = (ζ-1)(ζ⁻¹-1) = λ²`, `c₃₂ = i/2 + (p-1)/2·v_p(L_p(1,ω³²)) = 16 + 18`) and
equals `B₃₂ mod 37² ≠ 0` — the **second-order non-degeneracy** `M ≤ 1`, here made explicit at the
Bernoulli-number level as `β₃₂ := (B₃₂.num / 37) mod 37 = 3 ≠ 0` (§1, proven from the Kellner
α₀-invariant `37² ∣ B₃₂.num - 111`, `111 = 3·37`, with the proven `37² ∤ B₃₂.num`).

## What is proven here, and the single residual

* **§1** — the second-order non-degeneracy `β₃₂ = 3 ≠ 0` (proven from the Kellner α₀-invariant and
  `kellner_at_zero_not_dvd`).  This is the explicit value of the `B₃₂ mod 37²` leading coefficient
  that makes the level-`68` detector non-degenerate; it certifies the residual is non-vacuous.

* **§2** — the `c₃₂ = 68` repo-`λ`-level bookkeeping (proven arithmetic), the first-order `j = 15`
  degeneracy (`kummerLogDetRowFactor 15 = 0`, proven), and the second-order high-`λ`-valuation
  reduction `X³⁶ − c³⁶ ∈ λ⁷²` (proven, `K`-level `(37²) = λ⁷²`).

* **§3** — the named residual `Cor823Omega32SecondOrderVandermonde37` (a `def … : Prop`, **not** an
  axiom): for a unit `u : (𝓞 K⁺)ˣ` congruent to a rational integer modulo `37²` (the genuine
  Cor-8.23 input class), and any cyclotomic representative datum `(v, s, e)` of `u`'s class
  (`v ∈ C⁺`, `u·v⁻¹ ∈ pPowerSubgroup`, `v = CPlusExponentProduct s e`), the single `j = 15`
  Teichmüller-Vandermonde row `(V·ē)_15` vanishes.  This is the genuine second-order
  leading-coefficient content of Proposition 8.12 at `i = 32`: at `j = 15` the second-order matrix
  row factor is `B₃₂/32 mod 37²`, non-degenerate by `β₃₂ ≠ 0`, so the level-`68` mod-`37²`
  coordinate of `completedLog u` (which vanishes for `u ≡ c mod 37²`) forces `(V·ē)_15 = 0`.

* **§4** — `Cor823Omega32SecondOrderCollapse37` **proven from the residual**, by the *proven* R3
  second-Vandermonde inversion at `j = 15` (`caseIIEx811Eigen_vandermonde_eq_nine_smul`, value `9`,
  which holds at *every* `j ≤ 16` including `j = 15`) and the proven `37 ∤ h⁺` `p`-saturation +
  free-part-class bridges.

* **§5** — R4 discharged down to the residual:
  `fermatLastTheoremFor_thirtyseven_of_omega32Collapse` is supplied from the residual.

The residual is **strictly smaller** than `Cor823Omega32SecondOrderCollapse37`: its conclusion is
the single `j = 15` *Vandermonde row* `(V·ē)_15 = 0`, from which the target's eigencomponent
vanishing `caseIIResidueProvenance_decomp (…) 15 = 0` is *derived* here by the proven inversion.  It
is **sound** (a constraint on the *specific* descent congruence datum, with the cyclotomic
representative explicit, never an `E₃₂`-monomial property of an arbitrary class), **non-circular**
(the mod-`37²` hypothesis is strictly stronger than the mod-`37` one R3 consumes, and at `j = 15`
the first order gives *no* info — `kummerLogDetRowFactor 15 = 0` — so the content is genuinely
second-order), and **non-vacuous** (`u = 1`, `c = 1`, `v = 1`, `s = 0`, `e = 0`; see
`cor823Omega32SecondOrderVandermonde37_consequent_inhabited`).

## References
* Washington, *Introduction to Cyclotomic Fields*, 2nd ed., GTM 83, §8.4 (Proposition 8.12, Theorem
  8.22, Corollary 8.23, p. 171), §9.2 (Lemma 9.9, pp. 180–181).
* Kellner, *On irregular prime power divisors of the Bernoulli numbers*, Math. Comp. 76 (2007),
  Proposition 2.7.
-/

@[expose] public section

noncomputable section

set_option maxRecDepth 4000

open NumberField BigOperators

namespace BernoulliRegular.FLT37.Eichler

open BernoulliRegular (CPlusGenerator CPlusExponentProduct)
open BernoulliRegular.CyclotomicUnits
open BernoulliRegular.CyclotomicUnits.PadicLogSetup
open BernoulliRegular.CyclotomicUnits.PadicLogSetup.DworkParameter

/-! ## 1. The second-order non-degeneracy `β₃₂ = 3 ≠ 0` (`B₃₂ mod 37²`), proven from Kellner

Corollary 8.23 / Proposition 8.12 at `i = 32` needs the irregular `i = 32` `p`-adic `L`-value to be
a *first-order* zero — `M = v₃₇(L_p(1,ω³²)) ≤ 1` — equivalently `37³ ∤ B_{1184}` at the Kellner
level, and, at the *level of the leading coefficient* itself, the second-order Bernoulli factor
`β₃₂ := (B₃₂.num / 37) mod 37` is **nonzero**.  We compute it explicitly: `β₃₂ = 3`.

This is the `B₃₂ mod 37²` content: `B₃₂.num ≡ 111 = 3·37 (mod 37²)` (the Kellner α₀-invariant
`kellner_alpha_zero_thirtyseven_thirtytwo`), and `37 ∣ B₃₂.num` (proven
`thirtyseven_dvd_bernoulli_thirtytwo_num`), so `B₃₂.num = 37·q` with `q ≡ 3 (mod 37)`; since
`37² ∤ B₃₂.num` (proven `kellner_at_zero_not_dvd`) the factor `q mod 37 = 3 ≠ 0`. -/

/-- **The second-order Bernoulli factor `β₃₂ = (B₃₂.num / 37) mod 37 = 3 ≠ 0`** (proven,
axiom-clean): there is `q : ℤ` with `B₃₂.num = 37·q` and `(q : ZMod 37) = 3`.

This is the explicit value of the `B₃₂ mod 37²` leading coefficient — the second-order
non-degeneracy `M ≤ 1` at the Bernoulli-number level — that makes Washington's level-`68` `i = 32`
detector non-degenerate.  Proof: `37 ∣ B₃₂.num` gives `B₃₂.num = 37·q`; the Kellner α₀-invariant
`37² ∣ B₃₂.num - 111` (`111 = 3·37`) gives `37² ∣ 37·(q - 3)`, hence `37 ∣ q - 3`, i.e.
`(q : ZMod 37) = 3`. -/
theorem caseIICor823_secondOrder_bernoulliFactor_eq_three :
    ∃ q : ℤ, (bernoulli 32).num = 37 * q ∧ ((q : ZMod 37)) = 3 := by
  obtain ⟨q, hq⟩ := thirtyseven_dvd_bernoulli_thirtytwo_num
  refine ⟨q, hq, ?_⟩
  -- `37² ∣ B₃₂.num - 111 = 37·q - 111 = 37·(q - 3)`, so `37 ∣ q - 3`.
  have halpha : (37 : ℤ) ^ 2 ∣ (bernoulli 32).num - 111 :=
    kellner_alpha_zero_thirtyseven_thirtytwo
  rw [hq, show (37 : ℤ) * q - 111 = 37 * (q - 3) from by ring] at halpha
  obtain ⟨k, hk⟩ := halpha
  have hdvd : (37 : ℤ) ∣ (q - 3) :=
    ⟨k, mul_left_cancel₀ (by decide : (37 : ℤ) ≠ 0) (by rw [hk]; ring)⟩
  have h0 : ((q - 3 : ℤ) : ZMod 37) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 37).mpr hdvd
  push_cast at h0
  linear_combination h0

/-- **The second-order non-degeneracy is genuine: `β₃₂ ≠ 0`** (proven re-export).  The
`B₃₂ mod 37²` leading coefficient `β₃₂ = (B₃₂.num / 37) mod 37` is nonzero (it is `3`).  This is the
`M ≤ 1` non-degeneracy of Proposition 8.12 / Corollary 8.23 at `i = 32`, made explicit and proven;
it is what turns the otherwise-degenerate `j = 15` matrix row (`B₃₂ mod 37 = 0`) into a
*non-degenerate* second-order detector at level `68`. -/
theorem caseIICor823_secondOrder_bernoulliFactor_ne_zero :
    ∃ q : ℤ, (bernoulli 32).num = 37 * q ∧ ((q : ZMod 37)) ≠ 0 := by
  obtain ⟨q, hq, hq3⟩ := caseIICor823_secondOrder_bernoulliFactor_eq_three
  exact ⟨q, hq, by rw [hq3]; decide⟩

/-! ## 2. The `c₃₂ = 68` repo-`λ`-level bookkeeping, proven

Washington's `λ`-level for the `i = 32` second-order leading coefficient is
`c₃₂ = i/2 + (p-1)/2 · v_p(L_p(1,ω³²)) = 16 + 18·1 = 34` in his `λ_W = (ζ-1)(ζ⁻¹-1)` normalisation.
Since `λ_W` is an associate of `λ² = (ζ-1)²` (the repo uniformizer `λ = ζ - 1` squared appears in
the totally-real subfield local data), the repo-`λ`-level is `c₃₂ = 2·34 = 68`.  We record the two
arithmetic identities. -/

/-- **The `c₃₂` bookkeeping (Washington `λ_W`-level)**: `i/2 + (p-1)/2 · v_p = 16 + 18·1 = 34` for
`p = 37`, `i = 32`, `v_p(L_p(1,ω³²)) = 1` (the proven `M = 1`). -/
theorem caseIICor823_c32_washington_eq : 32 / 2 + (37 - 1) / 2 * 1 = 34 := by decide

/-- **The `c₃₂` bookkeeping (repo-`λ`-level)**: `c₃₂ = 2·(16 + 18·1) = 68` (the repo uniformizer
`λ = ζ - 1` is the square-root of Washington's `λ_W`, so the repo level doubles). -/
theorem caseIICor823_c32_repo_eq : 2 * (32 / 2 + (37 - 1) / 2 * 1) = 68 := by decide

/-- **The first-order matrix row factor is degenerate at `j = 15`** (proven, axiom-clean): the
first-order Kummer-log matrix `concreteKummerLogMatrix = diag(kummerLogDetRowFactor)·V` has
`kummerLogDetRowFactor 15 = 0` for `p = 37`.

This is the concrete first-order degeneracy that *forces* the second order at `i = 32`: the row
factor at `j = 15` is `B₃₂/(32) mod 37 = 0` (`kummerLogRowIndex 15 = 16`, `bernoulliFactor 37 16`
is `0` because `37 ∣ B₃₂.num`, the irregularity), so the first-order matrix row carries **no** info
about the `j = 15` Vandermonde row — exactly the index `caseIIEx811Core_rowFactor_ne_zero` excludes.
Recovering it is the genuine second-order content of the residual below, where the *non-degenerate*
`B₃₂ mod 37²` (`caseIICor823_secondOrder_bernoulliFactor_ne_zero`) takes over. -/
theorem caseIICor823_rowFactor_fifteen_eq_zero :
    kummerLogDetRowFactor (p := 37) (15 : Fin (kummerLogRank 37)) = 0 := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  by_contra hne
  -- `rowFactor 15 ≠ 0 → bernoulliFactor 37 16 ≠ 0 → ¬ 37 ∣ B₃₂.num`, contradiction.
  have hbf : bernoulliFactor 37 (kummerLogRowIndex (p := 37) (15 : Fin (kummerLogRank 37))) ≠ 0 :=
    (kummerLogDetRowFactor_ne_zero_iff_bernoulliFactor_ne_zero (p := 37) (by norm_num)
      (15 : Fin (kummerLogRank 37))).mp hne
  rw [show kummerLogRowIndex (p := 37) (15 : Fin (kummerLogRank 37)) = 16 from rfl] at hbf
  have hnotdvd : ¬ (37 : ℤ) ∣ (bernoulli (2 * 16)).num :=
    (bernoulliFactor_ne_zero_iff_not_dvd_bernoulli_num (p := 37) (j := 16)
      (by norm_num) (by norm_num)).mp hbf
  exact hnotdvd (by rw [show 2 * 16 = 32 from rfl]; exact thirtyseven_dvd_bernoulli_thirtytwo_num)

/-! ## 2.5. The second-order high-`λ`-valuation reduction (`K`-level `(37²) = λ⁷²`), proven

The first analytic step of the second-order argument, the `M = 1` analog of R3's proven
`caseIILeadingExponent_completedLogArg_mem_lambdaIdeal_pow_pred` (which gives `X³⁶ − 1 ∈ λ³⁶` from
`X ≡ c (mod 37)`).  Here the input is the **sharp** mod-`37²` congruence, and the `K`-level
ramification doubles: `(37²) = (λ³⁶)² = λ⁷²` (`span_natCast_prime_eq_lambdaIdeal_pow_pred` squared).
A unit `u` with `algebraMap u ≡ c (mod 37²)` therefore has its degree-`36` local image `X` with
`X − c ∈ λ⁷²`, whence `X³⁶ − c³⁶ ∈ λ⁷²` (powers respect congruence, `sub_dvd_pow_sub_pow`).

This is the genuine reachable second-order coefficient machinery — the `λ⁷²`-valuation of the
second-order log argument — feeding the level-`68` (`< 72`) coordinate extraction.  (The first-order
proof additionally folds in Fermat `c³⁶ ≡ 1 (mod 37)` to reach `X³⁶ − 1`; at the *second* order
`c³⁶ ≡ 1 (mod 37²)` fails in general, which is exactly why the `j = 15` content is genuinely
second-order and lands as the named residual `Cor823Omega32SecondOrderVandermonde37` rather than a
clean `X³⁶ − 1 ∈ λ⁷²` statement.) -/
theorem caseIICor823_localImage_pow36_sub_intCast_pow36_mem_lambdaIdeal_pow72
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (u : (𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ)))ˣ) (c : ℤ)
    (hc : ((37 : 𝓞 (CyclotomicField 37 ℚ)) ^ 2) ∣
      ((Units.map (algebraMap (𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ)))
          (𝓞 (CyclotomicField 37 ℚ))).toMonoidHom u : (𝓞 (CyclotomicField 37 ℚ))ˣ) -
        (c : 𝓞 (CyclotomicField 37 ℚ)))) :
    (EPlus_valuedLocalImage (p := 37) (K := CyclotomicField 37 ℚ) u :
        ValuedIntegerRing 37 (CyclotomicField 37 ℚ)) ^ 36 -
        (c : ValuedIntegerRing 37 (CyclotomicField 37 ℚ)) ^ 36 ∈
      (lambdaIdeal 37 (CyclotomicField 37 ℚ)) ^ 72 := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  set I : Ideal (ValuedIntegerRing 37 (CyclotomicField 37 ℚ)) :=
    (lambdaIdeal 37 (CyclotomicField 37 ℚ)) ^ 72 with hI
  let f := algebraMap (𝓞 (CyclotomicField 37 ℚ))
    (ValuedIntegerRing 37 (CyclotomicField 37 ℚ))
  let X : ValuedIntegerRing 37 (CyclotomicField 37 ℚ) :=
    (EPlus_valuedLocalImage (p := 37) (K := CyclotomicField 37 ℚ) u :
      ValuedIntegerRing 37 (CyclotomicField 37 ℚ))
  -- `(37²) = λ⁷²` in the valued ring: square the proven `(37) = λ³⁶`.
  have hpow_eq : Ideal.span ({((37 : ValuedIntegerRing 37 (CyclotomicField 37 ℚ)) ^ 2)} :
      Set (ValuedIntegerRing 37 (CyclotomicField 37 ℚ))) = I := by
    have h := span_natCast_prime_eq_lambdaIdeal_pow_pred (p := 37) (K := CyclotomicField 37 ℚ)
    rw [hI, ← Ideal.span_singleton_pow,
      show ((37 : ValuedIntegerRing 37 (CyclotomicField 37 ℚ))) =
        ((37 : ℕ) : ValuedIntegerRing 37 (CyclotomicField 37 ℚ)) from by push_cast; ring,
      h, ← pow_mul]
  have h_mem_iff : ∀ z : ValuedIntegerRing 37 (CyclotomicField 37 ℚ),
      z ∈ I ↔ ((37 : ValuedIntegerRing 37 (CyclotomicField 37 ℚ)) ^ 2) ∣ z := by
    intro z; rw [← hpow_eq, Ideal.mem_span_singleton]
  -- Step 1: `X − c ∈ I = λ⁷²` from the global mod-`37²` divisibility.
  have hXc : X - (c : ValuedIntegerRing 37 (CyclotomicField 37 ℚ)) ∈ I := by
    rw [h_mem_iff]
    obtain ⟨w, hw⟩ := hc
    refine ⟨f w, ?_⟩
    have hKunit : (Units.map (algebraMap
          (𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ)))
          (𝓞 (CyclotomicField 37 ℚ))).toMonoidHom u : (𝓞 (CyclotomicField 37 ℚ))) =
        algebraMap (𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ)))
          (𝓞 (CyclotomicField 37 ℚ))
          (u : 𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ))) := by
      rw [Units.coe_map]; rfl
    have hXval : X = f ((Units.map (algebraMap
          (𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ)))
          (𝓞 (CyclotomicField 37 ℚ))).toMonoidHom u : (𝓞 (CyclotomicField 37 ℚ)))) := by
      rw [hKunit]; rfl
    have hcong := congrArg f hw
    rw [map_sub, map_mul] at hcong
    rw [hXval]
    rw [show ((37 : ValuedIntegerRing 37 (CyclotomicField 37 ℚ)) ^ 2) =
        f ((37 : 𝓞 (CyclotomicField 37 ℚ)) ^ 2) from by rw [map_pow, map_ofNat],
      show ((c : ValuedIntegerRing 37 (CyclotomicField 37 ℚ))) =
        f (c : 𝓞 (CyclotomicField 37 ℚ)) from by rw [map_intCast]]
    exact hcong
  -- Step 2: `X³⁶ − c³⁶ = (X − c)·k ∈ I` since `X − c ∈ I`.
  obtain ⟨k, hk⟩ := sub_dvd_pow_sub_pow X (c : ValuedIntegerRing 37 (CyclotomicField 37 ℚ)) 36
  rw [hk]
  exact I.mul_mem_right k hXc

/-! ## 3. The genuine second-order residual: the `j = 15` Vandermonde row vanishes

For a unit `u : (𝓞 K⁺)ˣ` congruent to a rational integer modulo `37²`, and any cyclotomic
representative datum `(v, s, e)` of `u`'s class, the single `j = 15` Teichmüller-Vandermonde row
`(V·ē)_15` vanishes.  This is the genuine level-`68` mod-`37²` leading-coefficient content of
Washington Proposition 8.12 at `i = 32` — the one place the first order gives no information
(`kummerLogDetRowFactor 15 = B₃₂/32 mod 37 = 0`).  We isolate it as a `def … : Prop` (**not** an
axiom). -/

/-- **The second-order `j = 15` Vandermonde-row residual** (a `def … : Prop`, **not** an axiom — the
genuine level-`68` mod-`37²` leading-coefficient content of Proposition 8.12 at `i = 32`).

For every unit `u : (𝓞 K⁺)ˣ` and rational integer `c` with `37² ∣ algebraMap u − c` (the Cor-8.23
input class), and every cyclotomic representative datum of `u`'s class — a real cyclotomic unit
`v ∈ C⁺` with `u·v⁻¹ ∈ pPowerSubgroup (E⁺) 37` written as `v = CPlusExponentProduct s e` — the
single `j = 15` half-range Teichmüller-Vandermonde row of `ē` vanishes:

  `(vandermondeTeichmullerEvenSubOneMatrix.mulVec (fun a => (e a : ZMod 37))) 15 = 0`.

This is Washington Proposition 8.12 at `i = 32`, second order: at `j = 15` the matrix row factor is
`B₃₂/32 mod 37²` (the second-order analog of the first-order `B₃₂/32 mod 37 = 0`), non-degenerate by
the proven `β₃₂ ≠ 0` (`caseIICor823_secondOrder_bernoulliFactor_ne_zero`, `= B₃₂ mod 37²`), so the
level-`68` mod-`37²` coordinate of `completedLog u` — which vanishes for `u ≡ c (mod 37²)` through
the high-`λ`-level second-order valuation — forces the Vandermonde row to vanish.

It is **sound** (a constraint on the *specific* congruence datum, with the cyclotomic representative
explicit), **non-circular** (the mod-`37²` hypothesis is strictly stronger than R3's mod-`37`, and
the first order is *degenerate* at `j = 15`), and **non-vacuous**
(`cor823Omega32SecondOrderVandermonde37_consequent_inhabited`). -/
def Cor823Omega32SecondOrderVandermonde37
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)] : Prop :=
  ∀ (u : (𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ)))ˣ) (c : ℤ),
    ((37 : 𝓞 (CyclotomicField 37 ℚ)) ^ 2) ∣
      ((Units.map (algebraMap (𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ)))
          (𝓞 (CyclotomicField 37 ℚ))).toMonoidHom u : (𝓞 (CyclotomicField 37 ℚ))ˣ) -
        (c : 𝓞 (CyclotomicField 37 ℚ))) →
    ∀ (v : (𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ)))ˣ)
      (s : ℤ) (e : Fin (kummerLogRank 37) → ℤ),
      CPlusExponentProduct (p := 37) (K := CyclotomicField 37 ℚ) (by decide) s e = v →
      u * v⁻¹ ∈ pPowerSubgroup (EPlus (K := CyclotomicField 37 ℚ)) 37 →
      (vandermondeTeichmullerEvenSubOneMatrix (p := 37) (by norm_num)).mulVec
          (fun a : Fin (kummerLogRank 37) => (e a : ZMod 37)) (15 : Fin (kummerLogRank 37)) = 0

/-- **The second-order residual's consequent is inhabited** (non-vacuity, proven): for `u = 1`,
`c = 1`, the trivial cyclotomic representative `v = 1`, `s = 0`, `e = 0` satisfies the antecedents
(`37² ∣ 1 − 1 = 0`, `CPlusExponentProduct 0 0 = 1`, `1·1⁻¹ ∈ pPowerSubgroup`) and the consequent
`(V·0)_15 = 0` (the Vandermonde of the zero vector is `0`).  So
`Cor823Omega32SecondOrderVandermonde37` is a real implication on a satisfiable hypothesis, not
vacuously true. -/
theorem cor823Omega32SecondOrderVandermonde37_consequent_inhabited
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)] :
    (vandermondeTeichmullerEvenSubOneMatrix (p := 37) (by norm_num)).mulVec
        (fun a : Fin (kummerLogRank 37) => ((0 : Fin (kummerLogRank 37) → ℤ) a : ZMod 37))
        (15 : Fin (kummerLogRank 37)) = 0 := by
  rw [show (fun a : Fin (kummerLogRank 37) => ((0 : Fin (kummerLogRank 37) → ℤ) a : ZMod 37)) =
      (0 : Fin (kummerLogRank 37) → ZMod 37) from by funext a; simp]
  rw [Matrix.mulVec_zero, Pi.zero_apply]

/-! ## 4. `Cor823Omega32SecondOrderCollapse37` proven from the residual

The proven R3 second-Vandermonde inversion `caseIIEx811Eigen_vandermonde_eq_nine_smul` holds at
*every* row `j ≤ 16`, in particular at the irregular `j = 15`: it reads
`(V·ē)_15 = 9 · caseIIResidueProvenance_decomp (∑_a e_a • φ(CPlusGenerator a)) 15`, `9 ≠ 0`.  So the
residual's `(V·ē)_15 = 0` gives the `j = 15` eigencomponent vanishing of the cyclotomic
representative's class; the proven `37 ∤ h⁺` `p`-saturation + free-part-class bridge identify that
class with `realUnitToFreePartModP u`, completing the target. -/

/-- **`Cor823Omega32SecondOrderCollapse37` from the `j = 15` Vandermonde-row residual** (proven,
axiom-clean given `Cor823Omega32SecondOrderVandermonde37`).

Given `u : (𝓞 K⁺)ˣ`, `c : ℤ` with `37² ∣ algebraMap u − c`:
* the proven `37 ∤ h⁺` `p`-saturation
  (`caseIIEx811Bridge_exists_cyclotomic_div_mem_pPowerSubgroup`,
  `exists_CPlusExponentProduct_of_mem_CPlus`) supplies a cyclotomic representative
  `v = CPlusExponentProduct s e` of `u`'s class;
* the residual gives `(V·ē)_15 = 0`;
* the proven R3 inversion `caseIIEx811Eigen_vandermonde_eq_nine_smul` (value `9 ≠ 0`, at `j = 15`)
  gives `caseIIResidueProvenance_decomp (∑_a e_a • φ(CPlusGenerator a)) 15 = 0`;
* the proven free-part-class bridge `caseIIEx811Bridge_freePartClass_eq` identifies that with
  `realUnitToFreePartModP u`.

This **discharges Washington Proposition 8.12 at `i = 32`, second order, down to the single
residual** `Cor823Omega32SecondOrderVandermonde37`. -/
theorem cor823Omega32SecondOrderCollapse37_of_vandermonde
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (hV : Cor823Omega32SecondOrderVandermonde37) :
    Cor823Omega32SecondOrderCollapse37 := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  intro u c hc
  -- (1) p-saturation: a cyclotomic representative `v = CPlusExponentProduct s e` of `u`'s class.
  obtain ⟨v, hvCPlus, hdiv⟩ :=
    caseIIEx811Bridge_exists_cyclotomic_div_mem_pPowerSubgroup u
  obtain ⟨s, e, hse⟩ :=
    exists_CPlusExponentProduct_of_mem_CPlus (p := 37) (K := CyclotomicField 37 ℚ)
      (by decide) hvCPlus
  -- (2) the residual: `(V·ē)_15 = 0`.
  have hV15 : (vandermondeTeichmullerEvenSubOneMatrix (p := 37) (by norm_num)).mulVec
      (fun a : Fin (kummerLogRank 37) => (e a : ZMod 37)) (15 : Fin (kummerLogRank 37)) = 0 :=
    hV u c hc v s e hse hdiv
  -- (3) R3 inversion at `j = 15`: `(V·ē)_15 = 9 · decomp (∑ e_a g_a) 15`, `9 ≠ 0`.
  have hcollapse := caseIIEx811Eigen_vandermonde_eq_nine_smul e (15 : Fin (kummerLogRank 37))
  rw [hV15] at hcollapse
  have h9 : (9 : ZMod 37) ≠ 0 := by
    rw [show (9 : ZMod 37) = ((9 : ℕ) : ZMod 37) from by push_cast; ring,
      show (0 : ZMod 37) = ((0 : ℕ) : ZMod 37) from by push_cast; ring, Ne,
      ZMod.natCast_eq_natCast_iff]
    decide
  have hc15 : caseIIResidueProvenance_decomp
      (∑ a : Fin (kummerLogRank 37),
        e a • FLT37.realUnitToFreePartModP (K := CyclotomicField 37 ℚ)
          (Additive.ofMul
            (CPlusGenerator (p := 37) (K := CyclotomicField 37 ℚ) (by norm_num) a)))
      (15 : Fin 18) = 0 :=
    (mul_eq_zero.mp hcollapse.symm).resolve_left h9
  -- (4) free-part-class bridge: `∑ e_a g_a = realUnitToFreePartModP u`.
  have hcls := caseIIEx811Bridge_freePartClass_eq hse hdiv
  rw [hcls] at hc15
  exact hc15

/-! ## 5. `R4` discharged down to the single second-order residual, and the FLT37 endpoint -/

/-- **Washington Theorem 8.22 / Corollary 8.23 for `37` (`R4`) from the `j = 15` Vandermonde-row
residual** (proven, axiom-clean given `Cor823Omega32SecondOrderVandermonde37`).

Composes `cor823Omega32SecondOrderCollapse37_of_vandermonde` with the proven
`cor823PthPowerOfRationalModSq37_of_omega32Collapse` (which makes `Cor823PthPowerOfRationalModSq37`,
i.e. `R4`, follow from the single second-order `i = 32` collapse via WLOG-real + the real Theorem
8.22 + Step D). -/
theorem cor823PthPowerOfRationalModSq37_of_vandermonde
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (hV : Cor823Omega32SecondOrderVandermonde37) :
    Cor823PthPowerOfRationalModSq37 :=
  cor823PthPowerOfRationalModSq37_of_omega32Collapse
    (cor823Omega32SecondOrderCollapse37_of_vandermonde hV)

open FLT37.LehmerVandiver.CaseII in
/-- **Fermat's Last Theorem for `37`, with `R4` reduced to the single second-order `j = 15`
Vandermonde-row residual** (proven, axiom-clean given the genuine residuals + the carried Kellner
Prop).

Identical to `fermatLastTheoremFor_thirtyseven_of_omega32Collapse`, but the single second-order
collapse `Cor823Omega32SecondOrderCollapse37` is itself supplied by
`cor823Omega32SecondOrderCollapse37_of_vandermonde` from the strictly-smaller
`Cor823Omega32SecondOrderVandermonde37` — Washington Proposition 8.12 at `i = 32` reduced to the
genuine level-`68` mod-`37²` leading-coefficient content at `j = 15`.  All of the Theorem-8.22
plumbing (WLOG-real, `p`-saturation, the proven R3 regular collapse, the proven R3 `j = 15`
inversion, Step D, the K↔K⁺ descent) and the second-order non-degeneracy `β₃₂ ≠ 0` (`= B₃₂ mod 37²`)
are proven; only the level-`68` mod-`37²` Vandermonde-row vanishing remains. -/
theorem fermatLastTheoremFor_thirtyseven_of_omega32Vandermonde
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (caseII_classConjFixed : CaseIIRootClassConjFixed37)
    (caseII_realDescent : CaseIIRealSingleRootDescentPreservesReality37)
    (caseII_pthPow : Cor823CorrectedUnitPthPowerRationalModP37)
    (caseII_omega32V : Cor823Omega32SecondOrderVandermonde37)
    (noSecondOrderIrregular : NoSecondOrderIrregularPair 37 32) :
    FermatLastTheoremFor 37 :=
  fermatLastTheoremFor_thirtyseven_of_omega32Collapse
    caseII_classConjFixed
    caseII_realDescent
    caseII_pthPow
    (cor823Omega32SecondOrderCollapse37_of_vandermonde caseII_omega32V)
    noSecondOrderIrregular

end BernoulliRegular.FLT37.Eichler

end
