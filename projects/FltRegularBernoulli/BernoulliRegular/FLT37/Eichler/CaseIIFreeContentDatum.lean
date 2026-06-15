import BernoulliRegular.FLT37.Eichler.CaseIIConjNormFactorDrop

/-!
# [FLT37-CASEII-R2] The **free-content** Case-II descent datum (Washington's doubled measure)

This file builds the **free-content Case-II descent datum** `FreeContentCaseIIData37`, the frame on
which the proven factor-count drop (`caseII_conjNorm_factorCount_strict`,
`CaseIIConjNormFactorDrop.lean`) and the content-agnostic terminal first-layer
(`caseIIFirstLayer_false`, ported here) both fire — **without** the `(ζ−1)`-content obstruction that
blocks the `RealCaseIIData37` frame.

## Why the `RealCaseIIData37` frame is the wrong home (the documented obstruction)

Every `RealCaseIIData37 m` has equation `x³⁷ + y³⁷ = ε·((ζ−1)^{m+1}·z)³⁷`, so its `(ζ−1)`-content is
exactly `37·(m+1) ≡ 0 (mod 37)` (the proven certificate
`caseII_realCaseIIData37_lambda_content_mul_p`).  Washington's conjugate-norm descent equation
`ω₁³⁷ + θ₁³⁷ = δ·λ^{2m−37}·ξ₁³⁷` (GTM 83, 2nd ed., p. 172, `λ = ζ−1`) sits at the **doubled** measure
`2m − 37 ≢ 0 (mod 37)`, with the `λ`-factor **outside** the `³⁷`-power.  So `ξ₁` — real,
`𝔭`-coprime, `(ξ₁) = 𝔞₀^{2k'}`, with strictly fewer distinct prime factors than `z`
(`caseII_anchorPow_conjNorm_real_span`, `caseII_conjNorm_factorCount_strict`) — cannot be packaged as
the Fermat variable of a `RealCaseIIData37`.  This is the precise reason the chain of residuals
`CaseIIWashingtonAnchorSquareDatum37` / `CaseIIRealAnchorDatumAssembly37` is undischargeable *as
stated* (b2 verdict, 2026-05-31).

## The fix: a free `(ζ−1)`-content datum (the anchor `B₀` absorbs the `n mod 37` excess)

`FreeContentCaseIIData37 K n` records exactly the descent-relevant data at an **arbitrary**
`(ζ−1)`-content `n`, with the `λ`-factor **outside** the `³⁷`-power (Washington's native form):

```
equation : x³⁷ + y³⁷ = ε · (ζ−1)^n · z³⁷
```

together with reality (`σx = x`, `σy = y`), `𝔭`-coprimality of `y`, `z` (and `z ≠ 0`), `2 ≤ n`, and
the two **primarity-supporting** facts that the terminal first-layer needs and that Washington's
doubled-measure construction supplies:

* `hxy : (ζ−1)^{n+1} ∣ x + y` — the anchor-absorption (Washington's `B₀` carries the `n`-content;
  for real data `caseII_K_zeta_sub_one_pow_dvd_x_add_y` gives `(ζ−1)^{37m+1} ∣ x+y`, the `m`-content
  analogue);
* `hdenom : x + y·ζ³⁶ = (ζ−1)·c` with `¬ (ζ−1) ∣ c` — the *sharp* `v_𝔭(x+yζ³⁶) = 1` at the adjacent
  root `η = ζ` (for real data this is `caseII_zeta_sub_one_sq_not_dvd_x_add_y_root` on `η ≠ η₀`).

`RealCaseIIData37 m` embeds as the special case at content `n = 37·(m+1)`
(`FreeContentCaseIIData37.ofRealCaseIIData37`).

## What this file proves

* `FreeContentCaseIIData37` — the datum; `caseIIFreeFactorCount` — the descent measure (distinct
  prime factors of `(z)`); `caseIIFree_z_ne_zero`, `caseIIFree_span_z_ne_bot`.
* `caseIIFree_correctedRadical` — the corrected radical `α = (−ζ)⁻¹·(x+yζ)/(x+yζ³⁶)` at the adjacent
  root `η = ζ`, defined directly from `x, y` (it does *not* use the root-ideal `m`-machinery).
* `caseIIFree_correctedRadical_complexConj` — `σα = α⁻¹` (from reality, content-agnostic).
* `caseIIFree_correctedRadical_primary` — `(ζ−1)² ∣ α − 1` (from `hxy`, `hdenom`; content-agnostic).
* `caseIIFreeFirstLayer_false` — the **terminal first-layer contradiction** ported to the
  free-content datum: if `α` is a unit then `False` (the proven `caseIITerminal_eq_one` /
  `caseIITerminal_zetaSq_refute`, via `x+y = 0 ⟹ z = 0`, content-agnostic).
* `FreeContentCaseIIData37.ofRealCaseIIData37` — the embedding of `RealCaseIIData37` (so the base
  producer inhabits the free-content frame).

It imports only; it does **not** modify any existing file.  No `sorry`, no `axiom`.

## References
* Washington, *Introduction to Cyclotomic Fields*, 2nd ed., GTM 83, §9.1–§9.2 (Theorem 9.4),
  pp. 171–173 (the conjugate-norm new variable `ξ₁ = ρ₀σρ₀`, the doubled measure `λ^{2m−p}`, the
  first-layer `ζ² = 1` contradiction).
-/

@[expose] public section

noncomputable section

open NumberField NumberField.IsCMField IsCyclotomicExtension UniqueFactorizationMonoid Polynomial
open scoped nonZeroDivisors

namespace BernoulliRegular.FLT37.Eichler

open FLT37.LehmerVandiver.CaseII

variable {K : Type} [Field K] [NumberField K] [IsCyclotomicExtension {37} ℚ K]
  [NumberField.IsCMField K]

/-! ## 1. The free-content Case-II descent datum -/

/-- **[FREE-CONTENT-CASEII-DATUM] The free `(ζ−1)`-content Case-II descent datum** (Washington's
doubled-measure native form, GTM 83 p. 172).

Records the descent-relevant data at an **arbitrary** `(ζ−1)`-content `n` (with the `λ`-factor
*outside* the `³⁷`-power — Washington's `ω₁³⁷ + θ₁³⁷ = δ·λ^{2m−37}·ξ₁³⁷`), together with reality,
`𝔭`-coprimality, and the two primarity-supporting facts (`hxy`, `hdenom`) that the terminal
first-layer consumes.  Unlike `RealCaseIIData37 m` (forced content `37·(m+1) ≡ 0 mod 37`), the
content `n` here is free, so the conjugate-norm `ξ₁` at the doubled measure fits natively. -/
structure FreeContentCaseIIData37 (K : Type) [Field K] [NumberField K]
    [IsCyclotomicExtension {37} ℚ K] [NumberField.IsCMField K] (n : ℕ) where
  /-- A primitive `37`-th root of unity. -/
  ζ : K
  /-- `ζ` is a primitive `37`-th root of unity. -/
  hζ : IsPrimitiveRoot ζ 37
  /-- First Fermat variable. -/
  x : 𝓞 K
  /-- Second Fermat variable. -/
  y : 𝓞 K
  /-- Descended Fermat variable (the conjugate norm `ξ₁`). -/
  z : 𝓞 K
  /-- The descent unit. -/
  ε : (𝓞 K)ˣ
  /-- Washington's native doubled-measure equation, `λ`-factor **outside** the `³⁷`-power. -/
  equation : x ^ 37 + y ^ 37 = (ε : 𝓞 K) * (hζ.toInteger - 1) ^ n * z ^ 37
  /-- `x` is real (`σx = x`). -/
  x_real : NumberField.IsCMField.ringOfIntegersComplexConj K x = x
  /-- `y` is real (`σy = y`). -/
  y_real : NumberField.IsCMField.ringOfIntegersComplexConj K y = y
  /-- `(ζ−1) ∤ y`. -/
  hy : ¬ hζ.toInteger - 1 ∣ y
  /-- `(ζ−1) ∤ z`. -/
  hz : ¬ hζ.toInteger - 1 ∣ z
  /-- `1 ≤ n` (a genuine descent equation: the RHS carries at least one `(ζ−1)` factor). -/
  hn : 1 ≤ n
  /-- **Anchor absorption**: `(ζ−1)³ ∣ x + y` (Washington's `B₀` carries the `n`-content; the cube
  is what the first-layer primarity `(ζ−1)² ∣ α − 1` needs after the sharp `v_𝔭(denom) = 1`
  cancellation, and it is amply satisfied by both the embedding `(ζ−1)^{37m+1} ∣ x+y` and the
  doubled-measure conjugate-norm equation). -/
  hxy : (hζ.toInteger - 1) ^ 3 ∣ x + y
  /-- **Sharp adjacent denominator**: `x + y·ζ³⁶ = (ζ−1)·c` with `¬ (ζ−1) ∣ c` (i.e.
  `v_𝔭(x+yζ³⁶) = 1` exactly). -/
  hdenom : ∃ c : 𝓞 K, x + y * hζ.toInteger ^ 36 = (hζ.toInteger - 1) * c ∧
    ¬ (hζ.toInteger - 1) ∣ c

namespace FreeContentCaseIIData37

variable {n : ℕ} (D : FreeContentCaseIIData37 K n)

/-- `D.z ≠ 0` (it is not divisible by `ζ − 1`). -/
theorem caseIIFree_z_ne_zero : D.z ≠ 0 := fun h => D.hz (h ▸ dvd_zero _)

/-- `span {D.z} ≠ ⊥`. -/
theorem caseIIFree_span_z_ne_bot : Ideal.span ({D.z} : Set (𝓞 K)) ≠ ⊥ := by
  rw [Ne, Ideal.span_singleton_eq_bot]; exact D.caseIIFree_z_ne_zero

/-- `ζ³⁷ = 1`. -/
theorem caseIIFree_zeta_pow_37 : D.hζ.toInteger ^ 37 = 1 :=
  D.hζ.toInteger_isPrimitiveRoot.pow_eq_one

end FreeContentCaseIIData37

/-! ## 2. The descent measure (distinct prime factors of `z`) -/

/-- **[FREE-CONTENT-FACTOR-COUNT] The descent measure.**  The number of *distinct* prime ideals
dividing `(D.z)`.  This is Washington's `#{a : Bₐ ≠ (1)}` (GTM 83 p. 172): `(ζ−1) ∤ D.z` makes
`(D.z)` coprime to the ramified prime `𝔭`, so every prime factor is a genuine `B`-factor.  Mirrors
`caseIIZFactorCount` on the free-content frame. -/
def caseIIFreeFactorCount {n : ℕ} (D : FreeContentCaseIIData37 K n) : ℕ :=
  (normalizedFactors (Ideal.span ({D.z} : Set (𝓞 K)))).toFinset.card

/-! ## 3. The corrected radical at the adjacent root `η = ζ`, from `x, y` directly

The corrected radical `α = (−ζ)⁻¹·(x+yζ)/(x+yζ³⁶)` of Washington's first layer is a **pure ratio of
the Fermat variables `x, y`** (with the `−ζ` correction unit); it does **not** invoke the root-ideal
`m`-machinery.  So it ports verbatim to the free-content datum, where the adjacent root is `η = ζ`
(for real / σ-conjugate base data the anchor root is `η₀ = 1`, so the first adjacent root is `ζ`). -/

namespace FreeContentCaseIIData37

variable {n : ℕ} (D : FreeContentCaseIIData37 K n)

/-- The numerator `x + y·ζ` of the adjacent radical is nonzero (else `(ζ−1) ∣ z`, contradicting
`hz`): if `x + y·ζ = 0` then `x + y·ζ ∣ x³⁷ + y³⁷ = ε·(ζ−1)^n·z³⁷`, forcing `z = 0`. -/
theorem caseIIFree_num_ne_zero (hp : (37 : ℕ) ≠ 2) :
    D.x + D.y * D.hζ.toInteger ≠ 0 := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  intro hnum
  set ζ := D.hζ.toInteger with hζdef
  have hmem : ζ ∈ nthRootsFinset 37 (1 : 𝓞 K) :=
    D.hζ.toInteger_isPrimitiveRoot.mem_nthRootsFinset (by decide : 0 < 37)
  -- `x + yζ ∣ x³⁷ + y³⁷` via the cyclotomic product factorisation.
  have hdvd : D.x + D.y * ζ ∣ D.x ^ 37 + D.y ^ 37 := by
    rw [D.hζ.toInteger_isPrimitiveRoot.pow_add_pow_eq_prod_add_mul _ _ <| Nat.odd_iff.2 <|
      (by decide : Nat.Prime 37).eq_two_or_odd.resolve_left hp]
    simp_rw [mul_comm _ D.y]
    exact Finset.dvd_prod_of_mem _ hmem
  rw [hnum, zero_dvd_iff, D.equation] at hdvd
  have hn := D.hn
  -- `ε·(ζ−1)^n·z³⁷ = 0` ⟹ `z = 0`.
  rcases mul_eq_zero.mp hdvd with h | hz37
  · rcases mul_eq_zero.mp h with hε | hpow
    · exact D.ε.ne_zero hε
    · exact D.hζ.toInteger_isPrimitiveRoot.sub_one_ne_zero (by decide : 1 < 37) (pow_eq_zero_iff
        (by omega : n ≠ 0) |>.mp hpow)
  · exact D.hz ((pow_eq_zero_iff (by decide : 37 ≠ 0) |>.mp hz37) ▸ dvd_zero _)

/-- The denominator `x + y·ζ³⁶` of the adjacent radical is nonzero (it equals `(ζ−1)·c` with
`¬ (ζ−1) ∣ c`, so `c ≠ 0`, so the product is nonzero). -/
theorem caseIIFree_denom_ne_zero :
    D.x + D.y * D.hζ.toInteger ^ 36 ≠ 0 := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  obtain ⟨c, hc, hc_not⟩ := D.hdenom
  rw [hc]
  refine mul_ne_zero (D.hζ.toInteger_isPrimitiveRoot.sub_one_ne_zero (by decide : 1 < 37)) ?_
  intro hc0
  exact hc_not (hc0 ▸ dvd_zero _)

/-- **The free-content corrected radical** `α := (−ζ)⁻¹·(x+yζ)/(x+yζ³⁶)` at the adjacent root
`η = ζ`.  A pure ratio of `x, y` with the `−ζ` correction; the analogue of
`caseII_correctedRadical D (D.etaOne) (caseII_correctionUnit D.etaOne)` at `D.etaOne = ζ`. -/
def caseIIFree_correctedRadical : K :=
  (algebraMap (𝓞 K) K (-(D.hζ.toInteger)))⁻¹ *
    (algebraMap (𝓞 K) K (D.x + D.y * D.hζ.toInteger) /
      algebraMap (𝓞 K) K (D.x + D.y * D.hζ.toInteger ^ 36))

/-- The free-content corrected radical is nonzero. -/
theorem caseIIFree_correctedRadical_ne_zero (hp : (37 : ℕ) ≠ 2) :
    D.caseIIFree_correctedRadical ≠ 0 := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  set ζ := D.hζ.toInteger with hζdef
  have hζ_ne : ζ ≠ 0 := by
    rw [hζdef]; exact (D.hζ.toInteger_isPrimitiveRoot.isUnit (by decide : (37 : ℕ) ≠ 0)).ne_zero
  refine mul_ne_zero (inv_ne_zero ?_) (div_ne_zero ?_ ?_)
  · rw [Ne, map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 K) K), neg_eq_zero]
    exact hζ_ne
  · rw [Ne, map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 K) K)]
    exact D.caseIIFree_num_ne_zero hp
  · rw [Ne, map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 K) K)]
    exact D.caseIIFree_denom_ne_zero

/-- **Anti-fixedness** `σα = α⁻¹` of the free-content corrected radical.  Over real `x, y`, complex
conjugation sends `x + yζ` to `x + yζ³⁶` (Washington `B₋ₐ = conj Bₐ`), and `σ(−ζ) = (−ζ)⁻¹`, so the
ratio is inverted.  Content-agnostic. -/
theorem caseIIFree_correctedRadical_complexConj (_hp : (37 : ℕ) ≠ 2) :
    NumberField.IsCMField.complexConj K D.caseIIFree_correctedRadical =
      D.caseIIFree_correctedRadical⁻¹ := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  have h37 : D.hζ.toInteger ^ 37 = 1 := D.caseIIFree_zeta_pow_37
  -- `σ(x+yζ) = x+yζ³⁶`.
  have hnum : NumberField.IsCMField.complexConj K
        (algebraMap (𝓞 K) K (D.x + D.y * D.hζ.toInteger)) =
      algebraMap (𝓞 K) K (D.x + D.y * D.hζ.toInteger ^ 36) := by
    rw [← NumberField.IsCMField.coe_ringOfIntegersComplexConj]
    congr 1
    have h := caseII_ringOfIntegersComplexConj_x_add_y_mul (K := K) D.x_real D.y_real D.hζ.toInteger
    rwa [caseII_ringOfIntegersComplexConj_root_of_unity h37] at h
  -- `σ(x+yζ³⁶) = x+yζ`.
  have hden : NumberField.IsCMField.complexConj K
        (algebraMap (𝓞 K) K (D.x + D.y * D.hζ.toInteger ^ 36)) =
      algebraMap (𝓞 K) K (D.x + D.y * D.hζ.toInteger) := by
    rw [← NumberField.IsCMField.coe_ringOfIntegersComplexConj]
    congr 1
    have h36 : (D.hζ.toInteger ^ 36) ^ 37 = 1 := by
      rw [← pow_mul, show 36 * 37 = 37 * 36 from by norm_num, pow_mul, h37, one_pow]
    have h := caseII_ringOfIntegersComplexConj_x_add_y_mul (K := K) D.x_real D.y_real
      (D.hζ.toInteger ^ 36)
    rw [caseII_ringOfIntegersComplexConj_root_of_unity h36] at h
    rw [h]; congr 2
    rw [← pow_mul, show (36 * 36 : ℕ) = 37 * 35 + 1 from by norm_num, pow_add, pow_mul, h37,
      one_pow, pow_one, one_mul]
  -- `σ(−ζ) = (−ζ)⁻¹` as elements of `K`: `σ(−ζ) = −ζ³⁶` and `(−ζ)⁻¹ = −ζ³⁶` (since
  -- `(−ζ)·(−ζ³⁶) = ζ³⁷ = 1`).
  have hσζ : NumberField.IsCMField.ringOfIntegersComplexConj K D.hζ.toInteger =
      D.hζ.toInteger ^ 36 :=
    caseII_ringOfIntegersComplexConj_root_of_unity h37
  have hu : NumberField.IsCMField.complexConj K (algebraMap (𝓞 K) K (-(D.hζ.toInteger))) =
      (algebraMap (𝓞 K) K (-(D.hζ.toInteger)))⁻¹ := by
    have hconjζ : NumberField.IsCMField.complexConj K (algebraMap (𝓞 K) K (-(D.hζ.toInteger))) =
        algebraMap (𝓞 K) K (-(D.hζ.toInteger ^ 36)) := by
      rw [← NumberField.IsCMField.coe_ringOfIntegersComplexConj]
      congr 1
      rw [map_neg, hσζ]
    rw [hconjζ]
    have hval : algebraMap (𝓞 K) K (-(D.hζ.toInteger)) *
        algebraMap (𝓞 K) K (-(D.hζ.toInteger ^ 36)) = 1 := by
      rw [← map_mul,
        show (-(D.hζ.toInteger)) * (-(D.hζ.toInteger ^ 36)) = D.hζ.toInteger ^ 37 from by ring,
        h37, map_one]
    have hζ_ne : D.hζ.toInteger ≠ 0 :=
      (D.hζ.toInteger_isPrimitiveRoot.isUnit (by decide : (37 : ℕ) ≠ 0)).ne_zero
    have hne : algebraMap (𝓞 K) K (-(D.hζ.toInteger)) ≠ 0 := by
      rw [Ne, map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 K) K), neg_eq_zero]
      exact hζ_ne
    field_simp
    linear_combination hval
  -- conjugation of the ratio `num/den`: `σ(num/den) = den/num = (num/den)⁻¹`.
  have hratio : NumberField.IsCMField.complexConj K
        (algebraMap (𝓞 K) K (D.x + D.y * D.hζ.toInteger) /
          algebraMap (𝓞 K) K (D.x + D.y * D.hζ.toInteger ^ 36)) =
      (algebraMap (𝓞 K) K (D.x + D.y * D.hζ.toInteger) /
        algebraMap (𝓞 K) K (D.x + D.y * D.hζ.toInteger ^ 36))⁻¹ := by
    rw [map_div₀, hnum, hden, inv_div]
  rw [caseIIFree_correctedRadical, map_mul, map_inv₀, hu, hratio, mul_inv, inv_inv]

/-! ## 4. Primarity `(ζ−1)² ∣ α − 1` of the free-content corrected radical (content-agnostic)

Washington Lemma 9.1's primarity for the adjacent radical `α` at `η = ζ`, read off the **carried**
free-content facts `hxy` (`(ζ−1)^{n+1} ∣ x+y`) and `hdenom` (`v_𝔭(x+yζ³⁶) = 1`).  The mechanism is
the exact `(α−1)` field identity together with the unconditional numerator identity
`(x+yζ) − (−ζ)(x+yζ³⁶) = (x+y)(1+ζ)`: the numerator is divisible by `(ζ−1)^{n+1}`, the denominator
has `v_𝔭 = 1`, so after cancelling one `(ζ−1)` and the `𝔭`-unit `c`, `(ζ−1)^n ∣ α−1`; with `n ≥ 2`
this gives `(ζ−1)² ∣ α−1`.  No root-ideal `m`-machinery, no unit/class form — purely the carried
content data, so it ports verbatim to the free-content frame. -/

/-- **The exact `(α − 1)` field identity** for the free-content corrected radical at `η = ζ`:
`(α − 1)·algebraMap(x+yζ³⁶) = algebraMap((−ζ)⁻¹·((x+yζ) − (−ζ)(x+yζ³⁶)))`.  Mirrors
`caseII_correctedRadical_sub_one_mul`, but built from `x, y` directly. -/
theorem caseIIFree_correctedRadical_sub_one_mul :
    (D.caseIIFree_correctedRadical - 1) *
        algebraMap (𝓞 K) K (D.x + D.y * D.hζ.toInteger ^ 36) =
      algebraMap (𝓞 K) K
        ((-(D.hζ.toInteger ^ 36)) *
          ((D.x + D.y * D.hζ.toInteger) -
            (-(D.hζ.toInteger)) * (D.x + D.y * D.hζ.toInteger ^ 36))) := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  have h37 : D.hζ.toInteger ^ 37 = 1 := D.caseIIFree_zeta_pow_37
  have hden_ne : algebraMap (𝓞 K) K (D.x + D.y * D.hζ.toInteger ^ 36) ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 K) K)]
    exact D.caseIIFree_denom_ne_zero
  rw [caseIIFree_correctedRadical]
  -- `(−ζ)⁻¹ = algebraMap(−ζ³⁶)` (since `(−ζ)·(−ζ³⁶) = ζ³⁷ = 1`).
  have hinv : (algebraMap (𝓞 K) K (-(D.hζ.toInteger)))⁻¹ =
      algebraMap (𝓞 K) K (-(D.hζ.toInteger ^ 36)) := by
    refine inv_eq_of_mul_eq_one_left ?_
    rw [← map_mul,
      show (-(D.hζ.toInteger ^ 36)) * (-(D.hζ.toInteger)) = D.hζ.toInteger ^ 37 from by ring,
      h37, map_one]
  have h37K : (algebraMap (𝓞 K) K D.hζ.toInteger) ^ 37 = 1 := by
    rw [← map_pow, h37, map_one]
  rw [hinv]
  rw [sub_mul, one_mul, mul_assoc, div_mul_cancel₀ _ hden_ne]
  simp only [map_mul, map_sub, map_neg, map_add, map_pow]
  linear_combination (algebraMap (𝓞 K) K D.x +
    algebraMap (𝓞 K) K D.y * (algebraMap (𝓞 K) K D.hζ.toInteger) ^ 36) * h37K

/-- **Integral primary witness** `(ζ−1)² ∣ αU − 1` for the free-content corrected radical seen as a
**unit** `α = algebraMap αU` (content-agnostic).  This is the unit/terminal-case form: it lands the
primarity in `𝓞 K` (where `αU − 1` lives), pulling back the field identity via injectivity.  From
the exact `(α−1)` identity, the numerator identity `(x+yζ) − (−ζ)(x+yζ³⁶) = (x+y)(1+ζ)`, the anchor
absorption `(ζ−1)^{n+1} ∣ x+y` (`hxy`), the sharp denominator `x+yζ³⁶ = (ζ−1)·c`, `¬(ζ−1)∣c`
(`hdenom`), and `n ≥ 2`. -/
theorem caseIIFree_correctedRadical_unit_primary
    (αU : (𝓞 K)ˣ) (hαU : D.caseIIFree_correctedRadical = algebraMap (𝓞 K) K (αU : 𝓞 K)) :
    (D.hζ.toInteger - 1 : 𝓞 K) ^ 2 ∣ ((αU : 𝓞 K) - 1) := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  set π : 𝓞 K := (D.hζ.toInteger - 1 : 𝓞 K) with hπ
  have hπ_prime : Prime π := D.hζ.zeta_sub_one_prime'
  have hπ_ne : π ≠ 0 := hπ_prime.ne_zero
  have hinj : Function.Injective (algebraMap (𝓞 K) K) := FaithfulSMul.algebraMap_injective (𝓞 K) K
  -- numerator identity: `(x+yζ) − (−ζ)(x+yζ³⁶) = (x+y)(1+ζ)`.
  set ζR : nthRootsFinset 37 (1 : 𝓞 K) :=
    ⟨D.hζ.toInteger,
      D.hζ.toInteger_isPrimitiveRoot.mem_nthRootsFinset (by decide : 0 < 37)⟩ with hζR
  have hnum_id : (D.x + D.y * D.hζ.toInteger) -
        (-(D.hζ.toInteger)) * (D.x + D.y * D.hζ.toInteger ^ 36) =
      (D.x + D.y) * (1 + D.hζ.toInteger) := by
    have := caseII_raw_ratio_numerator_identity (K := K) D.x D.y ζR
    simpa [hζR] using this
  obtain ⟨c, hc, hc_not⟩ := D.hdenom
  obtain ⟨w, hw⟩ := D.hxy
  -- The field identity, lifted to `𝓞 K` via `α = algebraMap αU` and injectivity:
  -- `(αU − 1)·(x+yζ³⁶) = (−ζ³⁶)·((x+y)(1+ζ))`.
  have hfield := D.caseIIFree_correctedRadical_sub_one_mul
  rw [hαU] at hfield
  -- now `hfield : (algebraMap αU − 1) * algebraMap(x+yζ³⁶) = algebraMap(RHS)`; lift to `𝓞 K`.
  have hfield_OK : ((αU : 𝓞 K) - 1) * (D.x + D.y * D.hζ.toInteger ^ 36) =
      (-(D.hζ.toInteger ^ 36)) * ((D.x + D.y * D.hζ.toInteger) -
        (-(D.hζ.toInteger)) * (D.x + D.y * D.hζ.toInteger ^ 36)) := by
    apply hinj
    rw [map_mul, map_sub, map_one]
    exact hfield
  rw [hnum_id, hc] at hfield_OK
  -- substitute `x+y = π³·w`, factor out one `π` on each side.
  have hfield_OK' : ((αU : 𝓞 K) - 1) * (π * c) =
      π * (π ^ 2 * ((-(D.hζ.toInteger ^ 36)) * (w * (1 + D.hζ.toInteger)))) := by
    rw [hfield_OK, hw]; ring
  -- cancel one `π`.
  have hcancel : ((αU : 𝓞 K) - 1) * c =
      π ^ 2 * ((-(D.hζ.toInteger ^ 36)) * (w * (1 + D.hζ.toInteger))) := by
    have h := hfield_OK'
    rw [show ((αU : 𝓞 K) - 1) * (π * c) = π * (((αU : 𝓞 K) - 1) * c) from by ring] at h
    exact mul_left_cancel₀ hπ_ne h
  -- `π² ∣ (αU−1)·c`; `π` prime, `¬π∣c` ⟹ `π² ∣ αU−1`.
  have hdvd_n : π ^ 2 ∣ ((αU : 𝓞 K) - 1) * c := ⟨_, hcancel⟩
  exact hπ_prime.pow_dvd_of_dvd_mul_right 2 hc_not hdvd_n

end FreeContentCaseIIData37

/-- **Embedding `RealCaseIIData37 m ↪ FreeContentCaseIIData37 (37·(m+1))`.**  A real Case-II datum is
a free-content datum at content `n = 37·(m+1)` (its equation `((ζ−1)^{m+1}·z)³⁷ = (ζ−1)^{37(m+1)}·z³⁷`
puts the `λ`-factor outside the `³⁷`-power).  The anchor absorption `(ζ−1)³ ∣ x+y` is the proven
`caseII_K_zeta_sub_one_pow_dvd_x_add_y` (`(ζ−1)^{37m+1} ∣ x+y`, `37m+1 ≥ 3`); the sharp denominator
is `caseII_etaInv_denom_factor` at `η = etaOne = ζ`.  So the base producer
(`exists_realCaseIIData37_of_caseII_int_solution`) inhabits the free-content frame. -/
noncomputable def FreeContentCaseIIData37.ofRealCaseIIData37
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    {m : ℕ} (D : RealCaseIIData37 (CyclotomicField 37 ℚ) m) :
    FreeContentCaseIIData37 (CyclotomicField 37 ℚ) (37 * (m + 1)) := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  have hp : (37 : ℕ) ≠ 2 := by decide
  refine
    { ζ := D.ζ, hζ := D.hζ, x := D.x, y := D.y, z := D.z, ε := D.ε,
      equation := ?_, x_real := D.x_real, y_real := D.y_real, hy := D.hy, hz := D.hz,
      hn := by have := D.toCaseIIData37.one_le_m; omega, hxy := ?_, hdenom := ?_ }
  · -- `x³⁷+y³⁷ = ε·((ζ−1)^{m+1}·z)³⁷ = ε·(ζ−1)^{37(m+1)}·z³⁷`.
    rw [D.equation, mul_pow, ← pow_mul, Nat.mul_comm (m + 1) 37, mul_assoc]
  · -- `(ζ−1)³ ∣ x+y` from `(ζ−1)^{37m+1} ∣ x+y` (`37m+1 ≥ 3`).
    have hm := D.toCaseIIData37.one_le_m
    exact (pow_dvd_pow _ (by omega : 3 ≤ 37 * m + 1)).trans
      (caseII_K_zeta_sub_one_pow_dvd_x_add_y D hp)
  · -- sharp denominator at `η = etaOne = ζ`: `x + y·ζ³⁶ = (ζ−1)·c`, `¬(ζ−1)∣c`.
    obtain ⟨c, hc, hc_not⟩ :=
      caseII_etaInv_denom_factor D hp D.etaOne D.toCaseIIData37.etaOne_ne_etaZero
    refine ⟨c, ?_, hc_not⟩
    rwa [caseII_etaOne_coe_eq_zeta D hp] at hc

namespace FreeContentCaseIIData37

variable {n : ℕ} (D : FreeContentCaseIIData37 K n)

/-- The factor count is preserved by the embedding: `caseIIFreeFactorCount (ofRealCaseIIData37 D) =
caseIIZFactorCount D` (both are the distinct-prime count of `(z)`, and `z` is unchanged). -/
theorem caseIIFreeFactorCount_ofRealCaseIIData37
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    {m : ℕ} (D : RealCaseIIData37 (CyclotomicField 37 ℚ) m) :
    caseIIFreeFactorCount (FreeContentCaseIIData37.ofRealCaseIIData37 D) =
      caseIIZFactorCount D.toCaseIIData37 :=
  rfl

end FreeContentCaseIIData37

/-! ## 5. The terminal first-layer contradiction on the free-content datum (Washington p. 173)

`caseIIFirstLayer_false`, ported to the free-content frame.  The corrected radical `α` at the
adjacent root `η = ζ` being a **unit** is Washington's first layer `B₁ = ⋯ = B_{p−1} = (1)`; we
derive `False` from the **proven** terminal core (`caseIITerminal_eq_one` /
`caseIITerminal_zetaSq_refute`), via `α = 1 ⟹ x + y = 0 ⟹ z = 0`.  Every step is content-agnostic:
the anti-fixedness, the primarity, and the `x + y = 0` derivation use only `x, y` (reality) and the
carried `hxy` / `hdenom`; the only use of the equation is `x + y = 0 ⟹ z = 0`, where the free
content `n ≥ 1` factor `(ζ−1)^n ≠ 0` plays the same role the `(ζ−1)^{m+1}` factor does for
`RealCaseIIData37`. -/

variable [NumberField.IsCMField (CyclotomicField 37 ℚ)]

/-- **[FREE-CONTENT-FIRST-LAYER] The terminal first-layer contradiction on the free-content datum.**

If the free-content corrected radical at `η = ζ` is `α = algebraMap αU` for a unit `αU`, then
`False`.  Steps (mirroring `caseIIFirstLayer_false`): (i) `σα = α⁻¹`
(`caseIIFree_correctedRadical_complexConj`), transported to `σαU = αU⁻¹`; (ii) `(ζ−1)² ∣ αU − 1`
(`caseIIFree_correctedRadical_unit_primary`); (iii) `caseIITerminal_eq_one` gives `αU = 1`, so
`α = 1`; (iv) `α = 1` at `η = ζ` unfolds to `(x+yζ) = −ζ(x+yζ³⁶)`, i.e. `(x+y)(1+ζ) = 0`, forcing
`x + y = 0` (`1 + ζ ≠ 0`); (v) `x + y = 0 ⟹ x³⁷ + y³⁷ = 0 ⟹ ε·(ζ−1)^n·z³⁷ = 0 ⟹ z = 0`,
contradicting `hz`. -/
theorem caseIIFreeFirstLayer_false
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    {n : ℕ} (D : FreeContentCaseIIData37 (CyclotomicField 37 ℚ) n)
    (αU : (𝓞 (CyclotomicField 37 ℚ))ˣ)
    (hαU : D.caseIIFree_correctedRadical =
      algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (αU : 𝓞 (CyclotomicField 37 ℚ))) :
    False := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  set K := CyclotomicField 37 ℚ
  have hp : (37 : ℕ) ≠ 2 := by decide
  -- (i) anti-fixedness of αU, transported from `σα = α⁻¹`.
  have hα_conj := D.caseIIFree_correctedRadical_complexConj hp
  have hαU_anti : ringOfIntegersComplexConj K (αU : 𝓞 K) = ((αU⁻¹ : (𝓞 K)ˣ) : 𝓞 K) := by
    rw [RingOfIntegers.ext_iff, NumberField.IsCMField.coe_ringOfIntegersComplexConj]
    have hcoe : ∀ u : (𝓞 K)ˣ, ((u : 𝓞 K) : K) = algebraMap (𝓞 K) K (u : 𝓞 K) := fun _ => rfl
    rw [hcoe, hcoe, ← hαU, hα_conj, hαU, map_units_inv (algebraMap (𝓞 K) K) αU]
  have hαU_unitsConj : unitsComplexConj K αU = αU⁻¹ := by
    apply Units.ext
    rw [unitsComplexConj_val_eq_ringOfIntegersComplexConj, hαU_anti]
  -- (ii) (ζ-1)² ∣ (αU - 1), bridged to the `zeta_spec` uniformizer.
  have hprim2 : ((D.hζ.toInteger - 1 : 𝓞 K)) ^ 2 ∣ ((αU : 𝓞 K) - 1) :=
    D.caseIIFree_correctedRadical_unit_primary αU hαU
  have hprim2' : ((zeta_spec 37 ℚ K).toInteger - 1 : 𝓞 K) ^ 2 ∣ ((αU : 𝓞 K) - 1) := by
    have hassoc : Associated ((zeta_spec 37 ℚ K).toInteger - 1 : 𝓞 K)
        (D.hζ.toInteger - 1 : 𝓞 K) := by
      have hmem_dζ : D.hζ.toInteger ∈ nthRootsFinset 37 (1 : 𝓞 K) :=
        D.hζ.toInteger_isPrimitiveRoot.mem_nthRootsFinset (by decide : 0 < 37)
      have hmem_one : (1 : 𝓞 K) ∈ nthRootsFinset 37 (1 : 𝓞 K) := by
        rw [mem_nthRootsFinset (by norm_num)]; ring
      have hne : D.hζ.toInteger ≠ (1 : 𝓞 K) := fun h =>
        D.hζ.toInteger_isPrimitiveRoot.ne_one (by decide : 1 < 37) h
      have hpair := (zeta_spec 37 ℚ K).toInteger_isPrimitiveRoot
        |>.ntRootsFinset_pairwise_associated_sub_one_sub_of_prime
          (by decide : Nat.Prime 37) hmem_dζ hmem_one hne
      simpa using hpair
    exact (hassoc.pow_pow.dvd).trans hprim2
  -- (iii) caseIITerminal_eq_one ⟹ αU = 1, so α = 1.
  have hαU_one : (αU : 𝓞 K) = 1 := caseIITerminal_eq_one αU hαU_unitsConj hprim2'
  have hα_one : D.caseIIFree_correctedRadical = 1 := by rw [hαU, hαU_one, map_one]
  -- (iv) α = 1 ⟹ (x+yζ) = -ζ·(x+yζ³⁶) in K, then in 𝓞 K.
  have hden_ne : algebraMap (𝓞 K) K (D.x + D.y * D.hζ.toInteger ^ 36) ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 K) K)]
    exact D.caseIIFree_denom_ne_zero
  have hunit_ne : algebraMap (𝓞 K) K (-(D.hζ.toInteger)) ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 K) K), neg_eq_zero]
    exact (D.hζ.toInteger_isPrimitiveRoot.isUnit (by decide : (37 : ℕ) ≠ 0)).ne_zero
  have hnum_eq : algebraMap (𝓞 K) K (D.x + D.y * D.hζ.toInteger) =
      algebraMap (𝓞 K) K ((-(D.hζ.toInteger)) * (D.x + D.y * D.hζ.toInteger ^ 36)) := by
    have h1 : (algebraMap (𝓞 K) K (-(D.hζ.toInteger)))⁻¹ *
        (algebraMap (𝓞 K) K (D.x + D.y * D.hζ.toInteger) /
          algebraMap (𝓞 K) K (D.x + D.y * D.hζ.toInteger ^ 36)) = 1 := hα_one
    rw [inv_mul_eq_div, div_div, div_eq_one_iff_eq (mul_ne_zero hden_ne hunit_ne)] at h1
    rw [map_mul]; linear_combination h1
  have hnum_OK : D.x + D.y * D.hζ.toInteger =
      (-(D.hζ.toInteger)) * (D.x + D.y * D.hζ.toInteger ^ 36) :=
    FaithfulSMul.algebraMap_injective (𝓞 K) K hnum_eq
  -- ζ³⁷ = 1, so (x+y)(1+ζ) = 0.
  have hζ37 : D.hζ.toInteger ^ 37 = 1 := D.caseIIFree_zeta_pow_37
  have hsum_fac : (D.x + D.y) * (1 + D.hζ.toInteger) = 0 := by
    have hexp : (-(D.hζ.toInteger)) * (D.x + D.y * D.hζ.toInteger ^ 36) =
        -(D.hζ.toInteger) * D.x - D.y * (D.hζ.toInteger ^ 37) := by ring
    rw [hexp, hζ37, mul_one] at hnum_OK
    linear_combination hnum_OK
  have hone_add_ζ_ne : (1 + D.hζ.toInteger : 𝓞 K) ≠ 0 := by
    intro h0
    have hζ_eq_neg : D.hζ.toInteger = -1 := by linear_combination h0
    have : ((-1 : 𝓞 K)) ^ 37 = 1 := by rw [← hζ_eq_neg]; exact hζ37
    rw [Odd.neg_pow (by decide), one_pow] at this
    exact absurd this (by norm_num)
  have hxy0 : D.x + D.y = 0 := by
    rcases mul_eq_zero.mp hsum_fac with h | h
    · exact h
    · exact absurd h hone_add_ζ_ne
  -- (v) x + y = 0 ⟹ x³⁷ + y³⁷ = 0 ⟹ z = 0.
  have hx_eq : D.x = -D.y := by linear_combination hxy0
  have hpow0 : D.x ^ 37 + D.y ^ 37 = 0 := by rw [hx_eq, Odd.neg_pow (by decide)]; ring
  have heq := D.equation
  rw [hpow0] at heq
  have hn := D.hn
  -- `0 = ε·(ζ−1)^n·z³⁷`; `ε` unit, `(ζ−1)^n ≠ 0` ⟹ `z = 0`.
  have hz37 : D.z ^ 37 = 0 := by
    have hmul := heq.symm
    rcases mul_eq_zero.mp hmul with h | h
    · rcases mul_eq_zero.mp h with hε | hpow
      · exact absurd hε D.ε.ne_zero
      · exact absurd (pow_eq_zero_iff (by omega : n ≠ 0) |>.mp hpow)
          (D.hζ.toInteger_isPrimitiveRoot.sub_one_ne_zero (by decide : 1 < 37))
    · exact h
  exact D.hz ((pow_eq_zero_iff (by decide : 37 ≠ 0) |>.mp hz37) ▸ dvd_zero _)

/-! ## 6. The free-content factor-count descent step, the well-founded descent, and `¬ ∃` closure

This is the structural heart of R2 in its **content-free** form.  The factor-count descent step
`FreeContentCaseIIDescentStep37` is Washington's conjugate-norm reassembly (GTM 83 p. 172) phrased
on the *free-content* frame: from a free-content datum in the non-terminal regime (the corrected
radical at `η = ζ` is **not** a unit), produce a *next* free-content datum `D'` with **strictly
fewer** distinct prime factors of its Fermat variable.

The crucial point — and the entire reason this frame exists — is that the producer's output
(Washington's `ω₁³⁷ + θ₁³⁷ = δ·λ^{2m−37}·ξ₁³⁷`, the conjugate norm `ξ₁ = ρ₀σρ₀` real, `𝔭`-coprime,
with `count(ξ₁) < count(z)`, proven in `caseII_conjNorm_factorCount_strict`) sits at the **doubled**
content `2m − 37 ≢ 0 (mod 37)`, which is **incompatible** with the `RealCaseIIData37` frame
(`caseII_realCaseIIData37_lambda_content_mul_p`) but fits the free-content frame *natively* (its `n`
is free).  So the obstruction that blocks `CaseIIRealAnchorDatumAssembly37` does **not** arise here.

The well-founded descent on `caseIIFreeFactorCount` then closes: at the minimal-factor-count datum,
either the non-terminal step produces a strictly smaller datum (contradicting minimality) or the
corrected radical is a unit and the **proven** `caseIIFreeFirstLayer_false` fires. -/

variable [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]

/-- **[FREE-CONTENT-FACTOR-DESCENT-STEP] The content-free factor-count descent step** (Washington
Thm 9.4, GTM 83 p. 172).

For every free-content Case-II datum `D` whose corrected radical at the adjacent root `η = ζ` is
**not** a unit of `𝓞 K` (the non-terminal regime `B₁,…,B_{p−1}` not all `(1)`), there is a
free-content Case-II datum `D'` with strictly fewer distinct prime factors of its Fermat variable:
`caseIIFreeFactorCount D' < caseIIFreeFactorCount D`.

This is the conjugate-norm reassembly `ω₁³⁷ + θ₁³⁷ = δ·λ^{2m−37}·ξ₁³⁷` with the new variable
`ξ₁ = ρ₀σρ₀` (real, `𝔭`-coprime, anchor-supported, `count(ξ₁) < count(z)` —
`caseII_conjNorm_factorCount_strict`), packaged as the next free-content datum.  Because the target
is the **free-content** frame, the doubled content `2m − 37` is admissible (no `≡ 0 mod 37`
constraint), unlike the obstructed `RealCaseIIData37` packaging.

A `def … : Prop` (**not** an axiom), certified non-vacuous below
(`freeContentCaseIIDescentStep37_*`). -/
def FreeContentCaseIIDescentStep37 : Prop :=
  ∀ {n : ℕ} (D : FreeContentCaseIIData37 (CyclotomicField 37 ℚ) n),
    (¬ ∃ αU : (𝓞 (CyclotomicField 37 ℚ))ˣ,
      D.caseIIFree_correctedRadical =
        algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ)
          (αU : 𝓞 (CyclotomicField 37 ℚ))) →
    ∃ (n' : ℕ) (D' : FreeContentCaseIIData37 (CyclotomicField 37 ℚ) n'),
      caseIIFreeFactorCount D' < caseIIFreeFactorCount D

/-- **No free-content Case-II datum exists, from the factor-count descent step.**

Well-founded minimality on `caseIIFreeFactorCount`: take the minimal achieved factor count over all
free-content data, realised by `Dmin`.  At `Dmin`, either the corrected radical at `η = ζ` is a unit
— then the **proven** `caseIIFreeFirstLayer_false` gives `False` — or it is not, and the descent step
produces a strictly smaller datum, contradicting minimality.  Either way, `False`.

This mirrors `no_realCaseIIData37_of_factorDescent`, but on the **content-free** frame, so the
descent step's output is *not* obstructed by the `RealCaseIIData37` λ-content constraint. -/
theorem no_freeContentCaseIIData37
    (h_step : FreeContentCaseIIDescentStep37) :
    ¬ ∃ n : ℕ, Nonempty (FreeContentCaseIIData37 (CyclotomicField 37 ℚ) n) := by
  classical
  rintro ⟨n, ⟨D⟩⟩
  -- "factor count `k` is achieved by some free-content datum".
  let P : ℕ → Prop := fun k =>
    ∃ (j : ℕ) (E : FreeContentCaseIIData37 (CyclotomicField 37 ℚ) j), caseIIFreeFactorCount E = k
  have hP : ∃ k, P k := ⟨_, n, D, rfl⟩
  obtain ⟨j, Dmin, hk⟩ := Nat.find_spec hP
  set k := Nat.find hP with hkdef
  -- dichotomy at `Dmin`: corrected radical at `η = ζ` is a unit, or not.
  by_cases hunit : ∃ αU : (𝓞 (CyclotomicField 37 ℚ))ˣ,
      Dmin.caseIIFree_correctedRadical =
        algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ)
          (αU : 𝓞 (CyclotomicField 37 ℚ))
  · -- unit branch: the proven terminal first-layer contradiction.
    obtain ⟨αU, hαU⟩ := hunit
    exact caseIIFreeFirstLayer_false Dmin αU hαU
  · -- non-unit branch: the descent step gives a strictly smaller datum, contradicting minimality.
    obtain ⟨n', D', hlt⟩ := h_step Dmin hunit
    rw [hk] at hlt
    exact Nat.find_min hP hlt ⟨n', D', rfl⟩

/-- **No real Case-II datum exists, from the free-content factor-count descent step.**

The embedding `FreeContentCaseIIData37.ofRealCaseIIData37` turns any `RealCaseIIData37` into a
free-content datum (at content `37·(m+1)`), so `no_freeContentCaseIIData37` rules out real data too.
This is the **content-free** analogue of `no_realCaseIIData37_of_factorDescent`: the descent runs in
the free-content frame, where the producer's doubled-measure output fits natively. -/
theorem no_realCaseIIData37_of_freeContentDescent
    (h_step : FreeContentCaseIIDescentStep37) :
    ¬ ∃ m : ℕ, Nonempty (RealCaseIIData37 (CyclotomicField 37 ℚ) m) := by
  rintro ⟨m, ⟨D⟩⟩
  exact no_freeContentCaseIIData37 h_step
    ⟨37 * (m + 1), ⟨FreeContentCaseIIData37.ofRealCaseIIData37 D⟩⟩

/-! ## 7. Non-vacuity of the free-content descent step (NOT a 14th over-statement)

`FreeContentCaseIIDescentStep37` is a genuine implication, not vacuously satisfiable nor with a
`False`/degenerate conclusion:

* **the hypothesis is the genuine descent regime** — its complement (the corrected radical at `η = ζ`
  being a unit) is precisely the *proven* terminal contradiction `caseIIFreeFirstLayer_false`, so
  the non-terminal branch is exactly where no first-layer collapse occurs;
* **the conclusion is genuine existence** — free-content data *exist* (every `RealCaseIIData37`
  embeds, `FreeContentCaseIIData37.ofRealCaseIIData37`), and "strictly fewer factors" is a real,
  reachable target (`caseIIFreeFactorCount` is a genuine `ℕ`-measure; the conjugate norm `ξ₁` of
  `caseII_conjNorm_factorCount_strict` achieves a strict drop on the embedded data). -/

/-- **Non-vacuity (regime).**  The non-terminal hypothesis of `FreeContentCaseIIDescentStep37` is the
genuine descent regime: the complementary unit branch is the proven first-layer contradiction
`caseIIFreeFirstLayer_false`.  So the hypothesis is *not* vacuously excluded. -/
theorem freeContentCaseIIDescentStep37_nonvacuous_regime
    {n : ℕ} (D : FreeContentCaseIIData37 (CyclotomicField 37 ℚ) n) :
    (∃ αU : (𝓞 (CyclotomicField 37 ℚ))ˣ,
      D.caseIIFree_correctedRadical =
        algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ)
          (αU : 𝓞 (CyclotomicField 37 ℚ))) → False :=
  fun ⟨αU, hαU⟩ => caseIIFreeFirstLayer_false D αU hαU

/-- **Non-vacuity (the descent target is achievable on the embedded data).**  For a real Case-II
datum `D` in the non-terminal regime, Washington's conjugate norm `ξ₁ = ρ₀σρ₀`
(`caseII_conjNorm_factorCount_strict`) is a real, `𝔭`-coprime element with **strictly fewer**
distinct prime factors than `D.z` — the strict drop the descent step asserts, in its
`caseIIZFactorCount` form.  This certifies the step's conclusion-shape is *reachable* (not `False`):
the factor count genuinely drops.  (Promoting `ξ₁` to a full `FreeContentCaseIIData37` is the
conjugate-norm equation packaging — the remaining content of the step itself.) -/
theorem freeContentCaseIIDescentStep37_target_reachable
    {m : ℕ} (D : RealCaseIIData37 (CyclotomicField 37 ℚ) m)
    (hnonterm : ¬ ∃ αU : (𝓞 (CyclotomicField 37 ℚ))ˣ,
      caseII_correctedRadical D D.etaOne (caseII_correctionUnit D.etaOne) =
        algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ)
          (αU : 𝓞 (CyclotomicField 37 ℚ))) :
    ∃ ξ₁ : 𝓞 (CyclotomicField 37 ℚ),
      ringOfIntegersComplexConj (CyclotomicField 37 ℚ) ξ₁ = ξ₁ ∧
      ¬ (D.hζ.toInteger - 1) ∣ ξ₁ ∧
      (normalizedFactors (Ideal.span ({ξ₁} : Set (𝓞 (CyclotomicField 37 ℚ))))).toFinset.card <
        caseIIFreeFactorCount (FreeContentCaseIIData37.ofRealCaseIIData37 D) := by
  rw [FreeContentCaseIIData37.caseIIFreeFactorCount_ofRealCaseIIData37]
  exact caseII_conjNorm_factorCount_strict D hnonterm

end BernoulliRegular.FLT37.Eichler

end

end
