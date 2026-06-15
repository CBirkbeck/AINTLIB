import BernoulliRegular.FLT37.Eichler.CaseIIFreeContentAssembly
import BernoulliRegular.FLT37.Eichler.CaseIIThm95RationalDescent
import BernoulliRegular.FLT37.Eichler.CaseIILemma98RealData

/-!
# [FLT37-CASEII-R2] The combined `ℓ ∣ z` **free-content** descent: factor-count well-ordering
meets the finite-field Lemma-9.8

This file fuses the two FLT37 Case-II descent threads into a single, source-faithful frame:

* **The free-content factor-count well-ordering** (`CaseIIFreeContentDatum.lean`): Washington
  Theorem 9.4/9.5 minimises the counterexample by the **number of distinct prime ideal factors of
  the Fermat variable** (GTM 83 p. 172, `#{a : Bₐ ≠ (1)}`), *not* by the `(ζ−1)`-content / anchor
  exponent.  The free-content frame `FreeContentCaseIIData37` is the one on which this minimisation
  runs (the doubled measure `λ^{2m−37}` is admissible because the content `n` is **free**); the
  obstructed linear-measure `∃ m' < m` (b2 `ROUTEA-DESCENTSTEP-WELLORDER`, the σ-pair product
  *doubles* valuations) is **avoided**.

* **The `ℓ ∣ z`-restricted minimisation domain** (`CaseIIThm95RationalDescent.lean`): Washington
  takes the minimal counterexample **subject to `ℓ ∣ ξ`** (p. 178, `ℓ = 149`).  Carrying the
  Lemma-9.6/9.7 conditions `z ∈ 𝔩 ∧ x, y ∉ 𝔩` as **datum fields** makes Washington Lemma 9.8's
  local power a **finite-field** statement (`caseII_real_x_add_y_mem_of_dvd_z` is PROVEN:
  `ℓ ∣ z ∧ ℓ ∤ xy ⟹ ℓ ∣ (x+y)`, via `Q₃₂⁴ ≢ 1`), so the deep `p`-adic Lemma-9.8 dependency is
  **gone**.

The combination is `FreeContentCaseIIDvdZData37`: a free-content datum that **additionally** carries
`z ∈ 𝔩 ∧ x, y ∉ 𝔩`.  Its descent measure is `caseIIFreeFactorCount` (distinct prime factors of
`(z)`, the correct Washington well-ordering), and its `ℓ ∣ z` fields make the finite-field Lemma 9.8
available at every datum in the domain.

## What this file proves (real, axiom-clean Lean — no `sorry`, no `axiom`)

* `FreeContentCaseIIDvdZData37` — the combined datum; `caseIIFreeDvdZFactorCount` — its descent
  measure (the underlying `caseIIFreeFactorCount`).

* `FreeContentCaseIIDvdZDescentStep37` — the **combined factor-count descent step** (a `def … :
  Prop`, **not** an axiom): from a combined datum in the non-terminal regime (corrected radical at
  `η = ζ` not a unit), a combined datum with **strictly fewer** distinct prime factors.  This is the
  `ℓ ∣ z`-preserving form of `FreeContentCaseIIDescentStep37`, on the correct factor-count
  well-ordering.

* `no_freeContentCaseIIDvdZData37` — **the well-founded closure** (proven): no combined datum
  exists, from the combined step.  Minimality on `caseIIFreeFactorCount`; the unit branch is the
  **proven** terminal first-layer `caseIIFreeFirstLayer_false` (content-agnostic), the non-unit
  branch is the step, contradicting minimality.

* `FreeContentCaseIIDvdZData37.ofRealCaseIIDvdZData37` — the embedding of the `ℓ ∣ z`-restricted
  real datum `RealCaseIIDvdZData37` (so the rational seed inhabits the combined frame).

* `no_realCaseIIDvdZData37_of_freeContentDvdZDescent`,
  `caseIIBridge_thirtyseven_of_freeContentDvdZDescent`,
  `fermatLastTheoremFor_thirtyseven_of_freeContentDvdZDescent` — the closure to FLT37 Case-II: the
  rational Fermat solution enters the combined domain through the **proven** Lemma 9.7
  (`furtwangler_37_149`) and the factor-count minimality closes it, given the combined step + the
  carried Kellner + Washington Lemma 9.6.

## Soundness (B2-checked)

* The `ℓ ∣ z ∧ ℓ ∤ x, y` conditions are **datum fields** (true *of the data*, exactly as in
  `RealCaseIIDvdZData37`), never an abstract universal.  The universal "every combined datum has
  `ℓ ∣ z`" is **not** asserted.
* The well-ordering is `caseIIFreeFactorCount` **only** — the obstructed `∃ m' < m` linear-measure
  descent is **not** reintroduced.
* Coprimality `IsCoprime ((x)) ((y))` is **not** a datum field and is **not** asserted universally
  (it is provably false universally, b2 `project_flt37_freecontent_assembly_findings`); where the
  §9.1 factor equations need it, it is threaded as a hypothesis (in
  `freeContentCaseIIData37_pContent_descend_of_anchorExtractionData`, reused, not re-asserted).

It imports only; it does **not** modify any existing file.

## References
* Washington, *Introduction to Cyclotomic Fields*, 2nd ed., GTM 83, §9.1 (Theorem 9.4, the
  prime-factor-count minimisation, pp. 167–173) and §9.2 (Theorem 9.5, Lemmas 9.6–9.9, the `ℓ ∣ ξ`
  restriction, pp. 176–181).
-/

@[expose] public section

noncomputable section

open NumberField NumberField.IsCMField IsCyclotomicExtension UniqueFactorizationMonoid Polynomial
open scoped nonZeroDivisors

namespace BernoulliRegular.FLT37.Eichler

open FLT37.LehmerVandiver.CaseII

variable [NumberField.IsCMField (CyclotomicField 37 ℚ)]

/-! ## 0. A richer packaging lemma exposing `D'.x = ω`, `D'.y = θ`, `D'.z = z'`

The proven `freeContentCaseIIData37_of_descended_equation`
(`CaseIIFreeContentDatumPackaging.lean`) constructs the descended datum with `x := ω`, `y := θ`,
`z := z'` but exposes only `D'.z = z'` in its return type.  For the combined `ℓ ∣ z` frame we need
the descended datum's `x`, `y` fields too (to attach `ω ∉ 𝔩`, `θ ∉ 𝔩`).  We re-derive the same
datum here exposing **all three** field equalities; the proof is the identical construction (the
unit/exponent repackaging `Λ^{2e-1} → ε'·(ζ−1)^{2(2e-1)}`). -/

variable {K : Type} [Field K] [NumberField K] [IsCyclotomicExtension {37} ℚ K]
  [NumberField.IsCMField K]

omit [NumberField.IsCMField (CyclotomicField 37 ℚ)] in
/-- **[FREE-CONTENT-PACKAGING'] The descended free-content datum, exposing `x = ω, y = θ, z = z'`.**

Identical to `freeContentCaseIIData37_of_descended_equation` but with the three field equalities of
the constructed datum exposed.  From the integer descended equation
`ω³⁷ + θ³⁷ = δ·((1−ζ)(1−ζ³⁶))^{2e−1}·z'³⁷` and the reality / `𝔭`-coprimality / invariant inputs,
there is a free-content datum `D'` at content `2(2e−1)` with `D'.x = ω`, `D'.y = θ`, `D'.z = z'`. -/
theorem freeContentCaseIIData37_of_descended_equation_xyz
    {ζ : K} (hζ : IsPrimitiveRoot ζ 37)
    {ω θ z' : 𝓞 K} {δ : (𝓞 K)ˣ} {e : ℕ}
    (he : 1 ≤ e)
    (hequation : ω ^ 37 + θ ^ 37 =
      (δ : 𝓞 K) * ((1 - hζ.toInteger) * (1 - hζ.toInteger ^ 36)) ^ (2 * e - 1) * z' ^ 37)
    (hω_real : NumberField.IsCMField.ringOfIntegersComplexConj K ω = ω)
    (hθ_real : NumberField.IsCMField.ringOfIntegersComplexConj K θ = θ)
    (hθ_cop : ¬ hζ.toInteger - 1 ∣ θ)
    (hz'_cop : ¬ hζ.toInteger - 1 ∣ z')
    (hxy' : (hζ.toInteger - 1) ^ 3 ∣ ω + θ)
    (hdenom' : ∃ c : 𝓞 K, ω + θ * hζ.toInteger ^ 36 = (hζ.toInteger - 1) * c ∧
      ¬ (hζ.toInteger - 1) ∣ c) :
    ∃ (n' : ℕ) (D' : FreeContentCaseIIData37 K n'),
      D'.x = ω ∧ D'.y = θ ∧ D'.z = z' := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  set η36u : (𝓞 K)ˣ := (freeContentPackaging_neg_zeta_pow_36_isUnit hζ).unit with hη36u_def
  have hη36u_val : (η36u : 𝓞 K) = -(hζ.toInteger ^ 36) := by
    rw [hη36u_def, IsUnit.unit_spec]
  set ε' : (𝓞 K)ˣ := δ * η36u ^ (2 * e - 1) with hε'_def
  set n' : ℕ := 2 * (2 * e - 1) with hn'_def
  have hequation' : ω ^ 37 + θ ^ 37 = (ε' : 𝓞 K) * (hζ.toInteger - 1) ^ n' * z' ^ 37 := by
    rw [hequation, freeContentPackaging_Lambda_eq hζ, mul_pow, ← pow_mul]
    rw [hε'_def, Units.val_mul, Units.val_pow_eq_pow_val, hη36u_val, hn'_def]
    ring
  have hn'_ge : 1 ≤ n' := by rw [hn'_def]; omega
  let D' : FreeContentCaseIIData37 K n' :=
    { ζ := ζ, hζ := hζ, x := ω, y := θ, z := z', ε := ε',
      equation := hequation', x_real := hω_real, y_real := hθ_real, hy := hθ_cop, hz := hz'_cop,
      hn := hn'_ge, hxy := hxy', hdenom := hdenom' }
  exact ⟨n', D', rfl, rfl, rfl⟩

/-! ## 1. The combined `ℓ ∣ z` free-content Case-II descent datum -/

/-- **[FREE-CONTENT-DVDZ-DATUM] The `ℓ ∣ z`-restricted free-content Case-II descent datum.**

A `FreeContentCaseIIData37` (Washington's doubled-measure native frame, the **factor-count**
well-ordering) **carrying** Washington's Lemma-9.6/9.7 conditions on its own data:

* `z_mem` — **Lemma 9.7** (`ℓ ∣ z`): the descended Fermat variable lies in `𝔩 = lv149` (so the
  minimisation domain is the `ℓ ∣ ξ` one of Washington p. 178);
* `x_notMem`, `y_notMem` — **Lemma 9.6** (`ℓ ∤ xy`): the two Fermat variables avoid `𝔩`, so the
  finite-field Lemma 9.8 (`ℓ ∣ z ∧ ℓ ∤ xy ⟹ ℓ ∣ (x+y)`, PROVEN) is available.

These are **datum fields** — true *of the data*, exactly as in `RealCaseIIDvdZData37`, never an
abstract universal.  Combining the free `(ζ−1)`-content (correct doubled-measure frame) with the
`ℓ ∣ z` restriction makes Assumption II's Lemma-9.8 payload a finite-field statement at every datum
in the domain. -/
structure FreeContentCaseIIDvdZData37 (n : ℕ)
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    extends FreeContentCaseIIData37 (CyclotomicField 37 ℚ) n where
  /-- **Lemma 9.7** (`ℓ ∣ z`): the descended Fermat variable lies in `𝔩 = lv149`. -/
  z_mem : toFreeContentCaseIIData37.z ∈ lv149
  /-- **Lemma 9.6** (`ℓ ∤ x`): the first Fermat variable avoids `𝔩`. -/
  x_notMem : toFreeContentCaseIIData37.x ∉ lv149
  /-- **Lemma 9.6** (`ℓ ∤ y`): the second Fermat variable avoids `𝔩`. -/
  y_notMem : toFreeContentCaseIIData37.y ∉ lv149

/-- **The combined descent measure** — the distinct-prime-factor count of `(z)`, the correct
Washington factor-count well-ordering (inherited from the underlying free-content datum). -/
def caseIIFreeDvdZFactorCount {n : ℕ} (D : FreeContentCaseIIDvdZData37 n) : ℕ :=
  caseIIFreeFactorCount D.toFreeContentCaseIIData37

/-- **Promotion of a combined datum at content `37·(m+1)` to a `RealCaseIIDvdZData37 m`** (the
`ℓ ∣ z`-restricted real datum), combining `freeContentCaseIIData37_toReal` with the `ℓ`-membership
fields carried verbatim.  The promotion on which the finite-field Lemma 9.8 runs. -/
def FreeContentCaseIIDvdZData37.toReal
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    {m : ℕ} (D : FreeContentCaseIIDvdZData37 (37 * (m + 1))) :
    RealCaseIIDvdZData37 m where
  toRealCaseIIData37 := freeContentCaseIIData37_toReal D.toFreeContentCaseIIData37
  z_mem := D.z_mem
  x_notMem := D.x_notMem
  y_notMem := D.y_notMem

/-- **Washington Lemma 9.8 is a finite-field statement at any combined datum** (proven,
axiom-clean).

For any combined datum `D` at content `37·(m+1)`, the descended sum `x + y ∈ lv149` (`ℓ ∣ (ω + θ)`,
Washington's `j = 0`), under the carried Kellner input `hSO`.  This is the **finite-field**
Lemma-9.8 input (route (a)) — the `Q₃₂⁴ ≢ 1` core `caseII_real_x_add_y_mem_of_dvd_z` applied to the
promotion `D.toReal` — which makes the `ℓ ∣ ξ₁` propagation in `CaseIISection91DvdZExtractionData37`
(`z' ∈ 𝔩`) a finite-field consequence (`ℓ ∣ (x+y) ⟹ ℓ ∣ ρ₀ ⟹ ℓ ∣ ξ₁ = ρ₀²`, the anchor equation
opening), rather than the deep `p`-adic Lemma 9.8.  Carrying the `ℓ ∣ z ∧ ℓ ∤ x, y` datum fields is
exactly what makes this available. -/
theorem caseII_freeContentDvdZ_x_add_y_mem
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    (hSO : NoSecondOrderIrregularPair 37 32)
    {m : ℕ} (D : FreeContentCaseIIDvdZData37 (37 * (m + 1))) :
    D.x + D.y ∈ lv149 :=
  caseII_real_x_add_y_mem_of_dvd_z hSO D.toReal.toRealCaseIIData37
    D.toReal.z_mem D.toReal.x_notMem D.toReal.y_notMem

/-! ## 2. The combined factor-count descent step (the residual, `def … : Prop`) -/

variable [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]

/-- **[FREE-CONTENT-DVDZ-DESCENT-STEP] The combined `ℓ ∣ z` factor-count descent step** (Washington
Theorem 9.4/9.5, the `ℓ ∣ ξ`-restricted prime-factor-count minimisation, GTM 83 p. 172/178).

A `def … : Prop` (**not** an axiom).  For every combined datum `D` whose corrected radical at the
adjacent root `η = ζ` is **not** a unit (the non-terminal regime `B₁,…,B_{p−1}` not all `(1)`),
there is a combined datum `D'` with strictly fewer distinct prime factors of its Fermat variable:
`caseIIFreeDvdZFactorCount D' < caseIIFreeDvdZFactorCount D`.

This is the `ℓ ∣ z`-preserving form of `FreeContentCaseIIDescentStep37`
(`CaseIIFreeContentDatum.lean`): the conjugate-norm reassembly `ω₁³⁷ + θ₁³⁷ = δ·λ^{2m−37}·ξ₁³⁷`
(with `ξ₁ = ρ₀σρ₀` real, `𝔭`-coprime, `count(ξ₁) < count(z)` —
`caseII_conjNorm_factorCount_strict`) packaged as the next combined datum, the descent maintaining
the `ℓ ∣ ξ₁ ∧ ℓ ∤ ω₁, θ₁` conditions (Washington's `ℓ ∣ ρ₀ ⟹ ℓ ∣ ξ₁` from `ℓ ∣ (ω+θ)`, plus
Lemma 9.6 for the new `ω₁, θ₁`).  Because the target is the **free-content** frame, the doubled
content `2m − 37` is admissible (no `≡ 0 mod 37` constraint), and because the datum carries `ℓ ∣ z`,
Assumption II's Lemma-9.8 payload is a finite-field statement (route (a)). -/
def FreeContentCaseIIDvdZDescentStep37 : Prop :=
  ∀ {n : ℕ} (D : FreeContentCaseIIDvdZData37 n),
    (¬ ∃ αU : (𝓞 (CyclotomicField 37 ℚ))ˣ,
      D.toFreeContentCaseIIData37.caseIIFree_correctedRadical =
        algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ)
          (αU : 𝓞 (CyclotomicField 37 ℚ))) →
    ∃ (n' : ℕ) (D' : FreeContentCaseIIDvdZData37 n'),
      caseIIFreeDvdZFactorCount D' < caseIIFreeDvdZFactorCount D

/-! ## 3. The well-founded closure on the combined factor count -/

/-- **No combined `ℓ ∣ z` free-content datum exists, from the combined factor-count descent step**
(proven, axiom-clean).

Well-founded minimality on `caseIIFreeDvdZFactorCount` (= `caseIIFreeFactorCount`): take the minimal
achieved factor count over all combined data, realised by `Dmin`.  At `Dmin`, either the corrected
radical at `η = ζ` is a unit — then the **proven** terminal first-layer `caseIIFreeFirstLayer_false`
(content-agnostic, on the underlying free-content datum) gives `False` — or it is not, and the
combined descent step produces a strictly smaller combined datum, contradicting minimality.  Either
way, `False`.

This mirrors `no_freeContentCaseIIData37`, but on the **combined** frame, so `Dmin` carries `z ∈ 𝔩`
*by membership* (no universal) and the descent step's output is on the **correct factor-count**
well-ordering (not the obstructed `∃ m' < m`). -/
theorem no_freeContentCaseIIDvdZData37
    (h_step : FreeContentCaseIIDvdZDescentStep37) :
    ¬ ∃ n : ℕ, Nonempty (FreeContentCaseIIDvdZData37 n) := by
  classical
  rintro ⟨n, ⟨D⟩⟩
  -- "factor count `k` is achieved by some combined datum".
  let P : ℕ → Prop := fun k =>
    ∃ (j : ℕ) (E : FreeContentCaseIIDvdZData37 j), caseIIFreeDvdZFactorCount E = k
  have hP : ∃ k, P k := ⟨_, n, D, rfl⟩
  obtain ⟨j, Dmin, hk⟩ := Nat.find_spec hP
  set k := Nat.find hP with hkdef
  -- dichotomy at `Dmin`: corrected radical at `η = ζ` is a unit, or not.
  by_cases hunit : ∃ αU : (𝓞 (CyclotomicField 37 ℚ))ˣ,
      Dmin.toFreeContentCaseIIData37.caseIIFree_correctedRadical =
        algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ)
          (αU : 𝓞 (CyclotomicField 37 ℚ))
  · -- unit branch: the proven terminal first-layer contradiction (on the underlying datum).
    obtain ⟨αU, hαU⟩ := hunit
    exact caseIIFreeFirstLayer_false Dmin.toFreeContentCaseIIData37 αU hαU
  · -- non-unit branch: the combined step gives a strictly smaller datum, contradicting minimality.
    obtain ⟨n', D', hlt⟩ := h_step Dmin hunit
    rw [hk] at hlt
    exact Nat.find_min hP hlt ⟨n', D', rfl⟩

/-! ## 4. The embedding `RealCaseIIDvdZData37 m ↪ FreeContentCaseIIDvdZData37 (37·(m+1))` -/

/-- **Embedding `RealCaseIIDvdZData37 m ↪ FreeContentCaseIIDvdZData37 (37·(m+1))`.**

The `ℓ ∣ z`-restricted real datum embeds as a combined free-content datum at content `37·(m+1)`,
combining `FreeContentCaseIIData37.ofRealCaseIIData37` (the free-content embedding) with the
`ℓ ∣ z ∧ ℓ ∤ x, y` fields carried over verbatim (`z`, `x`, `y` unchanged by the embedding).  So the
rational seed (`exists_realCaseIIDvdZData37_of_caseII_int_solution`) inhabits the combined frame. -/
noncomputable def FreeContentCaseIIDvdZData37.ofRealCaseIIDvdZData37
    {m : ℕ} (D : RealCaseIIDvdZData37 m) :
    FreeContentCaseIIDvdZData37 (37 * (m + 1)) where
  toFreeContentCaseIIData37 :=
    FreeContentCaseIIData37.ofRealCaseIIData37 D.toRealCaseIIData37
  z_mem := D.z_mem
  x_notMem := D.x_notMem
  y_notMem := D.y_notMem

/-- **No `ℓ ∣ z`-restricted real Case-II datum exists, from the combined free-content factor-count
descent step** (proven, axiom-clean).

The embedding `FreeContentCaseIIDvdZData37.ofRealCaseIIDvdZData37` turns any `RealCaseIIDvdZData37`
into a combined datum (at content `37·(m+1)`), so `no_freeContentCaseIIDvdZData37` rules out the
restricted real data too.  This is the **correct-well-ordering** analogue of
`no_realCaseIIDvdZData37_of_dvdZDescentStep` (whose `∃ m' < m` is the obstructed linear measure):
here the descent runs in the **combined free-content** frame, on the **factor-count** measure, where
the producer's doubled-measure output fits natively. -/
theorem no_realCaseIIDvdZData37_of_freeContentDvdZDescent
    (h_step : FreeContentCaseIIDvdZDescentStep37) :
    ¬ ∃ m : ℕ, Nonempty (RealCaseIIDvdZData37 m) := by
  rintro ⟨m, ⟨D⟩⟩
  exact no_freeContentCaseIIDvdZData37 h_step
    ⟨37 * (m + 1), ⟨FreeContentCaseIIDvdZData37.ofRealCaseIIDvdZData37 D⟩⟩

/-! ## 5. The closure to FLT37 Case-II, at the rational seed (factor-count well-ordering) -/

/-- **The public Case-II bridge from the combined free-content `ℓ ∣ z` factor-count descent**
(proven, axiom-clean *given* the named inputs + Washington Lemma 9.6).

`CaseIIBridge 37 K 32` from:

* `h_step` (`FreeContentCaseIIDvdZDescentStep37`): the combined factor-count descent step (the
  `ℓ ∣ z`-preserving free-content step on the **correct** factor-count well-ordering — Washington's
  prime-factor-count minimisation, GTM 83 p. 172, **not** the obstructed `∃ m' < m`);
* `h_lemma96`: **Washington Lemma 9.6** (`149 ∤ x` for each `x ∈ {a, b, c}` with `37 ∤ x`) — the
  genuine arithmetic input certifying the `ℓ ∣ ξ` minimisation domain is non-empty.

The rational Fermat solution `a³⁷ + b³⁷ = c³⁷` enters the combined domain through the **proven**
Lemma 9.7 (`furtwangler_37_149`, via `exists_realCaseIIDvdZData37_of_caseII_int_solution`), and the
factor-count minimality `no_realCaseIIDvdZData37_of_freeContentDvdZDescent` closes it.  Unlike
`caseIIBridge_thirtyseven_of_thm95RationalDescent` (whose descent step is the obstructed linear
measure `∃ m' < m`), this bridge runs the minimisation on `caseIIFreeFactorCount`, the well-ordering
Washington actually uses, so the doubled-measure descent output is admissible. -/
theorem caseIIBridge_thirtyseven_of_freeContentDvdZDescent
    (h_step : FreeContentCaseIIDvdZDescentStep37)
    (h_lemma96 : ∀ a b c : ℤ, a * b * c ≠ 0 → ({a, b, c} : Finset ℤ).gcd id = 1 →
      (37 : ℤ) ∣ a * b * c → a ^ 37 + b ^ 37 = c ^ 37 →
      ∀ x : ℤ, (¬ (37 : ℤ) ∣ x) → (x = a ∨ x = b ∨ x = c) → ¬ (149 : ℤ) ∣ x) :
    BernoulliRegular.CaseIIBridge 37 (CyclotomicField 37 ℚ) 32 := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  refine ⟨?_⟩
  intro _hV _hSO a b c hprod hgcd hcase hEq
  exact (no_realCaseIIDvdZData37_of_freeContentDvdZDescent h_step)
    (exists_realCaseIIDvdZData37_of_caseII_int_solution hprod hgcd hcase hEq
      (h_lemma96 a b c hprod hgcd hcase hEq))

/-- **Fermat's Last Theorem for `37`, via the combined free-content `ℓ ∣ z` factor-count descent**
(proven, axiom-clean *given* the named inputs).

`FermatLastTheoremFor 37` from:

* `h_step` (`FreeContentCaseIIDvdZDescentStep37`): the combined factor-count descent step — the
  genuine remaining R2 content, on the **correct** factor-count well-ordering (Washington's
  prime-factor-count minimisation, GTM 83 p. 172) and with the `ℓ ∣ z` conditions making
  Assumption II's Lemma-9.8 payload a finite-field statement (route (a)); strictly avoids both the
  obstructed `∃ m' < m` linear measure *and* the false `Lemma98LocalPower37` universal;
* `h_lemma96` (**Washington Lemma 9.6**, `ℓ ∤ xy`): for each `x ∈ {a, b, c}` with `37 ∤ x`,
  `149 ∤ x` — the genuine arithmetic input certifying the `ℓ ∣ ξ` minimisation domain is non-empty;
* `noSecondOrderIrregular` (`NoSecondOrderIrregularPair 37 32`): the carried Kellner input.

Case I is the unconditional Eichler first-case proof (`caseIBridge_thirtyseven_eichler`);
`¬ 37 ∣ h⁺` is the proven `Sinnott.flt37_not_dvd_hPlus` (through `cor8_19Bridge_of_not_dvd_hPlus`);
the `ℓ ∣ z` content (Washington Lemma 9.7) is the **proven** `furtwangler_37_149`, consumed at the
rational seed.  This endpoint realises Washington Theorem 9.4/9.5 on the **prime-factor-count**
well-ordering at the rational entry, with the doubled-measure descent output fitting the
free-content frame natively. -/
theorem fermatLastTheoremFor_thirtyseven_of_freeContentDvdZDescent
    (h_step : FreeContentCaseIIDvdZDescentStep37)
    (h_lemma96 : ∀ a b c : ℤ, a * b * c ≠ 0 → ({a, b, c} : Finset ℤ).gcd id = 1 →
      (37 : ℤ) ∣ a * b * c → a ^ 37 + b ^ 37 = c ^ 37 →
      ∀ x : ℤ, (¬ (37 : ℤ) ∣ x) → (x = a ∨ x = b ∨ x = c) → ¬ (149 : ℤ) ∣ x)
    (noSecondOrderIrregular : NoSecondOrderIrregularPair 37 32) :
    FermatLastTheoremFor 37 := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  haveI : NeZero 37 := ⟨by decide⟩
  exact BernoulliRegular.fermatLastTheoremFor_thirtyseven_of_remaining
    (BernoulliRegular.cor8_19Bridge_of_not_dvd_hPlus 37 (CyclotomicField 37 ℚ)
      Sinnott.flt37_not_dvd_hPlus)
    caseIBridge_thirtyseven_eichler
    noSecondOrderIrregular
    (caseIIBridge_thirtyseven_of_freeContentDvdZDescent h_step h_lemma96)

/-! ## 6. The combined descent step at content `37·(m+1)`, from the §9.1 extraction data with
the `ℓ ∣ ξ₁`-propagation (the genuine residual mapped against the proven reassembly)

This section discharges the combined descent step **at the contents `37·(m+1)`** (the contents
reachable by the promotion `freeContentCaseIIData37_toReal`, where the flt-regular root-ideal
factor-equation extraction runs), reducing it to:

* the proven §9.1 reassembly capstone `freeContentCaseIIData37_of_factorEquations` (which supplies
  *all* of the descended datum's geometric fields — equation, `x' = ω`, `y' = θ` real, `hy'`/`hz'`
  `𝔭`-coprimality, the σ-fixed descent unit `δ'`, the two sharp invariants `hxy'`/`hdenom'`), and
* the §9.1 extraction data `CaseIISection91AnchorExtractionData37` (anchor equation, Assumption II,
  the integer witnesses + invariants + anchor-support), **extended** with the
  Lemma-9.6/9.7 propagation `z' ∈ 𝔩 ∧ ω ∉ 𝔩 ∧ θ ∉ 𝔩` that keeps the descended datum in the
  `ℓ ∣ ξ` domain.

The `ℓ`-propagation is keyed to the §9.1 outputs `(ω, θ, z')`: it is Washington's
`ℓ ∣ ρ₀ ⟹ ℓ ∣ ξ₁ = ρ₀²` (from the finite-field Lemma 9.8 `ℓ ∣ (x+y)`, PROVEN
`caseII_real_x_add_y_mem_of_dvd_z`, opened by the anchor equation) plus Lemma 9.6 for the new
`ω, θ` — a **descent-output** predicate, exactly the genuine narrowing of
`CaseIIThm95DvdZDescentStep37` on the correct factor-count well-ordering, never an abstract
universal. -/

open scoped Classical in
/-- **[FLT37-CASEII-§9.1-DVDZ-EXTRACTION-DATA] The §9.1 extraction data with the `ℓ ∣ ξ₁`
propagation** (a `def … : Prop`, **not** an axiom).

`CaseIISection91AnchorExtractionData37` (the §9.1 anchor equation, Assumption II `η_a = u³⁷·η_b`,
integer witnesses, invariants, anchor-support) **with** the three additional Lemma-9.6/9.7
membership facts on the descended building blocks `(ω, θ, z')`: `z' ∈ 𝔩` (Washington `ℓ ∣ ξ₁` from
`ℓ ∣ ρ₀`), `ω ∉ 𝔩`, `θ ∉ 𝔩` (Lemma 9.6 for the new variables).

The `ℓ`-membership hypotheses `D.x ∉ 𝔩`, `D.y ∉ 𝔩`, `D.z ∈ 𝔩` of the *source* datum are carried so
the propagation is conditioned exactly where Washington's argument supplies it (the finite-field
Lemma 9.8 `ℓ ∣ (x+y)` is available from them, PROVEN).  This is the combined-frame analogue of
`CaseIISection91AnchorExtractionData37`: it adds *only* the descent-maintained `ℓ ∣ ξ` propagation,
keeping the deep §9.1 content (Assumption II) exactly as before — now with the local-power half a
finite-field statement (route (a)). -/
def CaseIISection91DvdZExtractionData37 : Prop :=
  ∀ {m : ℕ} (D : RealCaseIIDvdZData37 m),
    IsCoprime (Ideal.span ({D.x} : Set (𝓞 (CyclotomicField 37 ℚ))))
      (Ideal.span ({D.y} : Set (𝓞 (CyclotomicField 37 ℚ)))) →
    ∀ (ηa ηb : (CyclotomicField 37 ℚ)ˣ) (ρa ρb : CyclotomicField 37 ℚ),
      complexConj (CyclotomicField 37 ℚ) (ηa : CyclotomicField 37 ℚ) =
          (ηa : CyclotomicField 37 ℚ) →
      complexConj (CyclotomicField 37 ℚ) (ηb : CyclotomicField 37 ℚ) =
          (ηb : CyclotomicField 37 ℚ) →
      (algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) D.x +
          algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (D.hζ.toInteger) *
            algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) D.y =
        (1 - algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (D.hζ.toInteger)) *
          (ηa : CyclotomicField 37 ℚ) * ρa ^ 37) →
      (algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) D.x +
          algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (D.hζ.toInteger ^ 2) *
            algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) D.y =
        (1 - algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (D.hζ.toInteger ^ 2)) *
          (ηb : CyclotomicField 37 ℚ) * ρb ^ 37) →
      ∃ (e k : ℕ) (η0 u : (CyclotomicField 37 ℚ)ˣ) (ρ0 : CyclotomicField 37 ℚ)
        (ω θ z' : 𝓞 (CyclotomicField 37 ℚ)) (δ' : (𝓞 (CyclotomicField 37 ℚ))ˣ),
        1 ≤ e ∧ 1 ≤ k ∧
        algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (D.x + D.y) =
          (η0 : CyclotomicField 37 ℚ) *
            (algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ)
              ((1 - (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger) *
                (1 - (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger ^ 36))) ^ e * ρ0 ^ 37 ∧
        (ηa : (CyclotomicField 37 ℚ)ˣ) = u ^ 37 * ηb ∧
        complexConj (CyclotomicField 37 ℚ) (η0 : CyclotomicField 37 ℚ) =
          (η0 : CyclotomicField 37 ℚ) ∧
        algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) ω =
          (u : CyclotomicField 37 ℚ) ^ 2 * (ρa * complexConj (CyclotomicField 37 ℚ) ρa) ∧
        algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) θ =
          -(ρb * complexConj (CyclotomicField 37 ℚ) ρb) ∧
        algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) z' = ρ0 ^ 2 ∧
        (∀ δ : (CyclotomicField 37 ℚ)ˣ,
          complexConj (CyclotomicField 37 ℚ) (δ : CyclotomicField 37 ℚ) =
              (δ : CyclotomicField 37 ℚ) →
          ((u : CyclotomicField 37 ℚ) ^ 2 *
                (ρa * complexConj (CyclotomicField 37 ℚ) ρa)) ^ 37 +
              (-(ρb * complexConj (CyclotomicField 37 ℚ) ρb)) ^ 37 =
            (δ : CyclotomicField 37 ℚ) *
              (algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ)
                ((1 - (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger) *
                  (1 - (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger ^ 36))) ^ (2 * e - 1) *
              (ρ0 ^ 2) ^ 37 →
          (δ : CyclotomicField 37 ℚ) =
            algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (δ' : 𝓞 _)) ∧
        ringOfIntegersComplexConj (CyclotomicField 37 ℚ) ω = ω ∧
        ringOfIntegersComplexConj (CyclotomicField 37 ℚ) θ = θ ∧
        ¬ (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger - 1 ∣ θ ∧
        ((zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger - 1) ^ 3 ∣ ω + θ ∧
        (∃ c : 𝓞 (CyclotomicField 37 ℚ),
          ω + θ * (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger ^ 36 =
              ((zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger - 1) * c ∧
            ¬ ((zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger - 1) ∣ c) ∧
        Ideal.span ({z'} : Set (𝓞 (CyclotomicField 37 ℚ))) =
          aEtaZeroDvdPPow (by decide : (37 : ℕ) ≠ 2) D.hζ D.equation D.hy ^ k ∧
        -- the Lemma-9.6/9.7 propagation (Washington's `ℓ ∣ ξ₁ ∧ ℓ ∤ ω₁, θ₁` descent maintenance):
        z' ∈ lv149 ∧ ω ∉ lv149 ∧ θ ∉ lv149

set_option maxRecDepth 4000 in
/-- **The combined `ℓ ∣ z` factor-count descent step at content `37·(m+1)`, from the §9.1
extraction data with the `ℓ ∣ ξ₁` propagation** (proven, axiom-clean *given* the extraction data
and the coprimality of the promoted Fermat variables).

For a combined datum `D` at content `37·(m+1)` in the non-terminal regime (corrected radical at
`η = ζ` not a unit), with coprime Fermat variables, the §9.1 `ℓ ∣ ξ₁`-extraction data
`CaseIISection91DvdZExtractionData37` yields a combined datum `D'` with strictly fewer distinct
prime factors of its Fermat variable.

Proof: promote `D` to a `RealCaseIIDvdZData37 m`; the proven factor equations at `ζ`, `ζ²`
(`caseII_section91_factorEquations_etaOne_etaTwo`) feed the extraction data to obtain the §9.1
outputs **and** the `ℓ`-propagation `z' ∈ 𝔩 ∧ ω ∉ 𝔩 ∧ θ ∉ 𝔩`; the proven packaging steps
(`washington_section91_integer_descended_equation` + the
`freeContentCaseIIData37_of_descended_equation` construction inlined) build the descended
free-content datum *with* `D'.x = ω`, `D'.y = θ`, `D'.z = z'`; attaching the three `ℓ`-facts yields
the combined datum; and the **proven** anchor-support strict drop gives `count(z') < count(z)`. -/
theorem freeContentCaseIIDvdZData37_pContent_descend_of_dvdZExtractionData
    (h_data : CaseIISection91DvdZExtractionData37)
    {m : ℕ} (D : FreeContentCaseIIDvdZData37 (37 * (m + 1)))
    (hcop : IsCoprime
      (Ideal.span ({(freeContentCaseIIData37_toReal D.toFreeContentCaseIIData37).x} :
        Set (𝓞 (CyclotomicField 37 ℚ))))
      (Ideal.span ({(freeContentCaseIIData37_toReal D.toFreeContentCaseIIData37).y} :
        Set (𝓞 (CyclotomicField 37 ℚ)))))
    (hnonterm : ¬ ∃ αU : (𝓞 (CyclotomicField 37 ℚ))ˣ,
      D.toFreeContentCaseIIData37.caseIIFree_correctedRadical =
        algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ)
          (αU : 𝓞 (CyclotomicField 37 ℚ))) :
    ∃ (n' : ℕ) (D' : FreeContentCaseIIDvdZData37 n'),
      caseIIFreeDvdZFactorCount D' < caseIIFreeDvdZFactorCount D := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  have hp : (37 : ℕ) ≠ 2 := by decide
  -- Promote the underlying free-content datum to a real datum, then to a `ℓ ∣ z` real datum.
  set Dr := freeContentCaseIIData37_toReal D.toFreeContentCaseIIData37 with hDr
  -- `Dr.x = D.x`, `Dr.y = D.y`, `Dr.z = D.z` definitionally; transport the `ℓ`-membership fields.
  let Drz : RealCaseIIDvdZData37 m :=
    { toRealCaseIIData37 := Dr
      z_mem := D.z_mem
      x_notMem := D.x_notMem
      y_notMem := D.y_notMem }
  -- Transfer the non-terminal hypothesis to the real datum `Dr`.
  have hnonterm' : ¬ ∃ αU : (𝓞 (CyclotomicField 37 ℚ))ˣ,
      caseII_correctedRadical Dr Dr.etaOne (caseII_correctionUnit Dr.etaOne) =
        algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ)
          (αU : 𝓞 (CyclotomicField 37 ℚ)) := by
    rw [← caseIIFree_correctedRadical_eq_real D.toFreeContentCaseIIData37]; exact hnonterm
  -- The proven factor equations at `ζ`, `ζ²`.
  obtain ⟨ηa, ηb, ρa, ρb, hηa_real, hηb_real, hfa_pos, hfa_neg, hfb_pos, hfb_neg⟩ :=
    caseII_section91_factorEquations_etaOne_etaTwo Dr hcop
  -- The §9.1 `ℓ ∣ ξ₁`-extraction data: §9.1 outputs + the `ℓ`-propagation `z'∈𝔩 ∧ ω∉𝔩 ∧ θ∉𝔩`.
  obtain ⟨e, k, η0, u, ρ0, ω, θ, z', δ', he, hk, hanchor, hII, hη0real, hω, hθ, hz',
      hδ', hω_real, hθ_real, hθ_cop, hxy', hdenom', hz'_span, hz'_mem, hω_notMem, hθ_notMem⟩ :=
    h_data Drz hcop ηa ηb ρa ρb hηa_real hηb_real hfa_pos hfb_pos
  -- `¬ (zeta_spec − 1) ∣ z'`: from `(z') = 𝔞₀ᵏ` (`𝔭`-coprime) + associatedness.
  have hz'cop_dζ : ¬ (Dr.hζ.toInteger - 1) ∣ z' := by
    have hnot : ¬ Ideal.span ({(Dr.hζ.toInteger - 1 : 𝓞 (CyclotomicField 37 ℚ))} : Set _) ∣
        Ideal.span ({z'} : Set (𝓞 (CyclotomicField 37 ℚ))) := by
      rw [hz'_span]
      intro hdvd
      exact not_p_div_a_zero hp Dr.hζ Dr.equation Dr.hy Dr.hz
        ((Ideal.prime_span_singleton_iff.mpr Dr.hζ.zeta_sub_one_prime').dvd_of_dvd_pow hdvd)
    rwa [Ideal.dvd_span_singleton, Ideal.mem_span_singleton] at hnot
  have hz'_cop : ¬ (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger - 1 ∣ z' := by
    have hassoc := caseII_section91_zeta_sub_one_associated_zeta_spec Dr
    intro hdvd
    exact hz'cop_dζ (hassoc.dvd.trans hdvd)
  -- The capstone's root data `ηA = ζ`, `ηB = ζ²` and the `Λ`-units.
  set ηA : 𝓞 (CyclotomicField 37 ℚ) := Dr.hζ.toInteger with hηA
  set ηB : 𝓞 (CyclotomicField 37 ℚ) := Dr.hζ.toInteger ^ 2 with hηB
  have hA37 : ηA ^ 37 = 1 := by
    rw [hηA]; exact Dr.hζ.toInteger_isPrimitiveRoot.pow_eq_one
  have hB37 : ηB ^ 37 = 1 := by
    rw [hηB, ← pow_mul, show 2 * 37 = 37 * 2 from by norm_num, pow_mul, hA37, one_pow]
  have hA1 : ηA ≠ 1 := Dr.hζ.toInteger_isPrimitiveRoot.ne_one (by decide : 1 < 37)
  have hB1 : ηB ≠ 1 := by
    rw [hηB]
    exact Dr.hζ.toInteger_isPrimitiveRoot.pow_ne_one_of_pos_of_lt (by omega) (by decide : 2 < 37)
  have hAB : ηA ≠ ηB := by
    rw [hηA, hηB, pow_two]
    intro h
    have hz0 : Dr.hζ.toInteger * (Dr.hζ.toInteger - 1) = 0 := by linear_combination -h
    rcases mul_eq_zero.mp hz0 with h0 | h1
    · exact Dr.hζ.toInteger_isPrimitiveRoot.ne_zero (by decide : 37 ≠ 0) h0
    · exact hA1 (by rw [hηA]; linear_combination h1)
  have hABp : ηA * ηB ≠ 1 := by
    rw [hηA, hηB, show Dr.hζ.toInteger * Dr.hζ.toInteger ^ 2 = Dr.hζ.toInteger ^ 3 from by ring]
    exact Dr.hζ.toInteger_isPrimitiveRoot.pow_ne_one_of_pos_of_lt (by omega) (by decide : 3 < 37)
  have hΛne : ∀ (η : 𝓞 (CyclotomicField 37 ℚ)), η ^ 37 = 1 → η ≠ 1 →
      algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ)
        ((1 - η) * (1 - η ^ 36)) ≠ 0 := by
    intro η hη37 hη1
    rw [Ne, map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective _ _)]
    refine mul_ne_zero (fun h0 => hη1 (by linear_combination -h0)) (fun h0 => ?_)
    have h36 : η ^ 36 = 1 := by linear_combination -h0
    have : η = 1 := by
      have hsucc : η ^ 37 = η ^ 36 * η := by rw [pow_succ]
      rw [hη37, h36, one_mul] at hsucc; exact hsucc.symm
    exact hη1 this
  set Λa : (CyclotomicField 37 ℚ)ˣ := Units.mk0 _ (hΛne ηA hA37 hA1) with hΛa_def
  set Λb : (CyclotomicField 37 ℚ)ˣ := Units.mk0 _ (hΛne ηB hB37 hB1) with hΛb_def
  have hΛspec_ne := hΛne (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger
    ((zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger_isPrimitiveRoot.pow_eq_one)
    ((zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger_isPrimitiveRoot.ne_one (by decide : 1 < 37))
  set Λ : (CyclotomicField 37 ℚ)ˣ := Units.mk0 _ hΛspec_ne with hΛ_def
  have hΛa_val : (Λa : CyclotomicField 37 ℚ) = algebraMap (𝓞 (CyclotomicField 37 ℚ))
      (CyclotomicField 37 ℚ) ((1 - ηA) * (1 - ηA ^ 36)) := rfl
  have hΛb_val : (Λb : CyclotomicField 37 ℚ) = algebraMap (𝓞 (CyclotomicField 37 ℚ))
      (CyclotomicField 37 ℚ) ((1 - ηB) * (1 - ηB ^ 36)) := rfl
  have hΛ_val : (Λ : CyclotomicField 37 ℚ) = algebraMap (𝓞 (CyclotomicField 37 ℚ))
      (CyclotomicField 37 ℚ)
      ((1 - (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger) *
        (1 - (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger ^ 36)) := rfl
  have hanchor' : algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) Dr.x +
      algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) Dr.y =
      (η0 : CyclotomicField 37 ℚ) * (Λ : CyclotomicField 37 ℚ) ^ e * ρ0 ^ 37 := by
    rw [hΛ_val, ← map_add]; exact hanchor
  -- The proven integer descended equation `ω³⁷ + θ³⁷ = δ'·Λ^{2e-1}·z'³⁷`.
  have hint_eq := washington_section91_integer_descended_equation (K := CyclotomicField 37 ℚ)
    (x := algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) Dr.x)
    (y := algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) Dr.y)
    (ρa := ρa) (ρb := ρb) (ρ0 := ρ0) (ηa := ηa) (ηb := ηb) (η0 := η0) (u := u)
    (ηA := ηA) (ηB := ηB) (Λa := Λa) (Λb := Λb) (Λ := Λ) (e := e)
    he hA37 hB37 hA1 hB1 hAB hABp hΛa_val hΛb_val hΛ_val
    hfa_pos hfa_neg hfb_pos hfb_neg hanchor' hII hη0real hηb_real
    hω hθ hz' hδ'
  -- The proven richer packaging: build the descended free-content datum with `Dnew.x = ω`,
  -- `Dnew.y = θ`, `Dnew.z = z'` (so the `ℓ`-membership facts attach directly).  We use the
  -- canonical `zeta_spec` primitive root, in whose `.toInteger`-terms `hint_eq`, `hxy'`, `hdenom'`
  -- are stated.
  obtain ⟨n', Dnew, hDnew_x, hDnew_y, hDnew_z⟩ :=
    freeContentCaseIIData37_of_descended_equation_xyz
      (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)) he
      hint_eq hω_real hθ_real hθ_cop hz'_cop hxy' hdenom'
  -- Assemble the combined datum and the factor-count strict drop.
  let Dcomb : FreeContentCaseIIDvdZData37 n' :=
    { toFreeContentCaseIIData37 := Dnew,
      z_mem := by rw [hDnew_z]; exact hz'_mem,
      x_notMem := by rw [hDnew_x]; exact hω_notMem,
      y_notMem := by rw [hDnew_y]; exact hθ_notMem }
  refine ⟨n', Dcomb, ?_⟩
  -- the factor-count strict drop (anchor-support), on the underlying counts.
  change caseIIFreeFactorCount Dnew < caseIIFreeFactorCount D.toFreeContentCaseIIData37
  rw [caseIIFreeFactorCount, hDnew_z, caseIIFreeFactorCount_toReal D.toFreeContentCaseIIData37]
  have hsupp := caseII_anchorSupported_of_span_eq_anchorPow Dr hk hz'_span
  exact caseIIZFactorCount_strict_of_anchor_supported Dr hp hnonterm' hsupp

/-! ## 7. Non-vacuity of the `ℓ ∣ ξ₁`-extraction data, and the honest residual map

The combined descent step `freeContentCaseIIDvdZData37_pContent_descend_of_dvdZExtractionData` (§6)
discharges the combined step **at the contents `37·(m+1)`** (the contents reachable by the promotion
`freeContentCaseIIData37_toReal`, where the flt-regular root-ideal factor-equation extraction runs),
**from** the §9.1 `ℓ ∣ ξ₁`-extraction data `CaseIISection91DvdZExtractionData37` **and** the
coprimality of the promoted Fermat variables — both threaded as genuine inputs, never false
universals.

### What the combined frame banks (the value-add over `CaseIISection91AnchorExtractionData37`)

The §9.1 geometric content is **entirely supplied by the proven reassembly**: the descended
equation, the descended variables `x' = ω`, `y' = θ` (real, `hy'`/`hz'` `𝔭`-coprime), the σ-fixed
descent unit `δ'`, the sharp invariants `hxy'`/`hdenom'`, and the factor-count strict drop — *all*
proven (`freeContentCaseIIData37_of_descended_equation_xyz`,
`caseIIZFactorCount_strict_of_anchor_supported`).  The combined frame adds **only** the
Lemma-9.6/9.7 `ℓ ∣ ξ₁`-propagation `z' ∈ 𝔩 ∧ ω ∉ 𝔩 ∧ θ ∉ 𝔩`, which makes Assumption II's **local
power** a finite-field statement: over a `RealCaseIIDvdZData37` (which the combined datum promotes
to), Washington Lemma 9.8 `ℓ ∣ (x+y)` is **PROVEN** (`caseII_real_x_add_y_mem_of_dvd_z`, the
`Q₃₂⁴ ≢ 1` core), so `ℓ ∣ ρ₀` (via the anchor equation, `ℓ ∤ Λ` since `149 ≠ 37`) and
`ℓ ∣ ξ₁ = ρ₀²`.  This is the route-(a) finite-field replacement of the deep `p`-adic Lemma 9.8.

### Why the inputs are genuine (soundness verdict, B2-checked)

* **The `ℓ`-propagation is a descent-output predicate, not a universal.**  It asserts the descended
  building blocks `(ω, θ, z')` — *keyed to the §9.1 outputs* — stay in the `ℓ ∣ ξ ∧ ℓ ∤ ω, θ` domain
  (Washington's `ℓ ∣ ξ₁` from `ℓ ∣ ρ₀`, plus Lemma 9.6 for the new variables).  This is **true**
  (Washington Lemma 9.6/9.7 for the descended datum) and strictly narrower than the false
  `Lemma98LocalPower37` universal (B2 `CASEII-LEMMA98-LOCALPOWER`): it never asserts the local power
  for an arbitrary datum.

* **Assumption II (`η_a = u³⁷·η_b`) is carried, not asserted free.**  It is the §9.1 Lemma-9.9
  unit-power step; over the combined frame its **local-power half** is finite-field
  (`caseII_real_x_add_y_mem_of_dvd_z`, proven), but the **global** `37`-th-power conclusion still
  needs the single-index Corollary-8.15 expansion (`Cor815SingleIndexExpansion37` / its descent-unit
  provenance) — that is the remaining R4 content, NOT discharged here.  It is carried inside
  `CaseIISection91DvdZExtractionData37` exactly as in `CaseIISection91AnchorExtractionData37`.

* **Coprimality `IsCoprime ((x)) ((y))` is not a datum field** (verified: the structures carry only
  `hy`, `hz`) and the universal "every combined datum has coprime `x, y`" is **provably false**
  (scale a base datum by a rational prime `p ≠ 37`; b2
  `project_flt37_freecontent_assembly_findings`).
  Threaded as an explicit hypothesis of the descent theorem, never asserted.

* **The non-`p`-content regime is genuinely open.**
  `freeContentCaseIIDvdZData37_pContent_descend_*` covers content `37·(m+1)` only; one descent step
  lands at content `2·(2e−1) = 4e−2`, which is `≢ 0 (mod 37)` in general (the non-`p`-content gap),
  where the root-ideal factor extraction (`span{x³⁷+y³⁷} = (𝔭·z)³⁷`, a *perfect* `37`-th power)
  does **not** apply to a free-content datum.  This is **not** closed here; it is the residual the
  combined frame is built to address but does not yet dispatch.

So the full `FreeContentCaseIIDvdZDescentStep37` is **not** discharged by §6 alone: §6 discharges it
*at content `37·(m+1)`*, reducing that content's case to `CaseIISection91DvdZExtractionData37` +
coprimality.  The combined `def … : Prop` below certifies the extraction data's antecedent is
inhabited (the factor equations exist), so the residual is a *genuine implication*. -/

/-- **Non-vacuity of `CaseIISection91DvdZExtractionData37` (antecedent inhabited).**  For a combined
`ℓ ∣ z` real Case-II datum `D` with coprime Fermat variables, the factor-equation outputs the
extraction data is keyed to **exist** (`caseII_section91_factorEquations_etaOne_etaTwo`, from the
proven product half).  So the extraction data consumes inhabited input — it is a genuine
implication, not vacuously true for the wrong reason. -/
theorem caseIISection91DvdZExtractionData37_antecedent_inhabited
    {m : ℕ} (D : RealCaseIIDvdZData37 m)
    (hcop : IsCoprime (Ideal.span ({D.x} : Set (𝓞 (CyclotomicField 37 ℚ))))
      (Ideal.span ({D.y} : Set (𝓞 (CyclotomicField 37 ℚ))))) :
    ∃ (ηa ηb : (CyclotomicField 37 ℚ)ˣ) (ρa ρb : CyclotomicField 37 ℚ),
      complexConj (CyclotomicField 37 ℚ) (ηa : CyclotomicField 37 ℚ) =
          (ηa : CyclotomicField 37 ℚ) ∧
      complexConj (CyclotomicField 37 ℚ) (ηb : CyclotomicField 37 ℚ) =
          (ηb : CyclotomicField 37 ℚ) ∧
      (algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) D.x +
          algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (D.hζ.toInteger) *
            algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) D.y =
        (1 - algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (D.hζ.toInteger)) *
          (ηa : CyclotomicField 37 ℚ) * ρa ^ 37) ∧
      (algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) D.x +
          algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (D.hζ.toInteger ^ 2) *
            algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) D.y =
        (1 - algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (D.hζ.toInteger ^ 2)) *
          (ηb : CyclotomicField 37 ℚ) * ρb ^ 37) := by
  obtain ⟨ηa, ηb, ρa, ρb, hηa_real, hηb_real, hfa_pos, _, hfb_pos, _⟩ :=
    caseII_section91_factorEquations_etaOne_etaTwo D.toRealCaseIIData37 hcop
  exact ⟨ηa, ηb, ρa, ρb, hηa_real, hηb_real, hfa_pos, hfb_pos⟩

end BernoulliRegular.FLT37.Eichler

end

end
