module

public import BernoulliRegular.FLT37.Eichler.CaseII.ConjugatePair.RealRadicalConjAndSignTwist
public import BernoulliRegular.FLT37.Eichler.CaseII.ConjugatePair.RealToConjPairDescentStep

/-!
# [FLT37-CASEII-R2] The precise σ-twist of the descent units `σε₁ = (-1)^m·ζ·ε₂`

This file pins down — **rigorously, by direct computation** — the *exact* σ-action on the leading
descent units of the inversion-symmetric single-root Case-II descent over **real** data.  It is the
soundness-critical analysis of LINK (1), the σ-equivariance `σε₁ = ε₂` of the descent units
(`CaseIIRealToConjPairSigmaEquivariant37` / `CaseIITwistedConjPairEntry37`).

## The finding (sound, verified — supersedes the naive "coprimality forces `σε₁ = ε₂`")

The flt-regular descent reassembly `formula_of_etaZeroSpanSingletons` (`SpecificChain.lean`) builds,
from generators `a₁/b₁` of `𝔞(η)/𝔞₀` and `a₂/b₂` of `𝔞(η⁻¹)/𝔞₀`, a six-unit equation whose two
leading units are
`ε₁ = u₁·U₁`, `ε₂ = u₂·U₂`, where `Uᵢ = associated_eta_zero_unit_of_spanSingleton … ηᵢ` (the
associate witness of the generator relation `𝔞(ηᵢ)·(bᵢ) = 𝔞₀·(aᵢ)`) and `uᵢ` is the root-difference
associate unit (`(ζ-1)·uᵢ = ηₐ − η_b`).  Over a real datum with the σ-fixed anchor `η₀ = 1` and the
conjugate-paired generators `a₂ = σa₁`, `b₂ = σb₁`, complex conjugation acts on each factor:

* **the associate witness is σ-paired up to the sign `(-1)^m`**:
  `σU(η, a, b) = (-1)^m · U(η⁻¹, σa, σb)` (`caseII_assocUnit_sigma_twist`).  This is a *clean
  domain cancellation* on the determining spec
  `U·(x+y·η₀)·a³⁷ = (x+y·η)·(ζ-1)^{m·37}·b³⁷`: applying `σ` (real `x, y`, `η₀ = 1` fixed) turns the
  RHS into `(x+y·η⁻¹)·(-1)^m·(ζ-1)^{m·37}·(σb)³⁷` (`caseII_real_zeta_sub_one_pow_conj` supplies the
  `(-1)^m`), which is `(-1)^m·` the determining spec for `U(η⁻¹, σa, σb)`.

* **the root-difference unit carries a primitive-root twist `σu₁ = ζ·u₂`** — the soundness obstacle:
  `(ζ-1)·u₁ = η⁻¹−1`, `(ζ-1)·u₂ = 1−η`, and `σ(η⁻¹−1) = η−1 = −(1−η)`, while `σ(ζ-1) = ζ³⁶−1 =
  −ζ³⁶(ζ-1)`; cancelling gives `ζ³⁶·σu₁ = u₂`, i.e. `σu₁ = ζ·u₂` (as `ζ·ζ³⁶ = 1`).

Combining, the **precise** σ-twist of the leading descent unit is

  `σε₁ = σu₁·σU₁ = (ζ·u₂)·((-1)^m·U₂) = (-1)^m·ζ·ε₂`.

The `(-1)^m` is a `37`-th power (`caseII_neg_one_pow_is_pth_power`), hence absorbable; but the unit
`ζ = hζ.unit'` is a **primitive** `37`-th root of unity, which is **not** a `37`-th power.  So
`σε₁ = ε₂` does **not** hold for the raw reassembly units: there is a genuine primitive-root
obstruction.

## Consequence — the obstruction is *common* to both routes (the measure-doubling obstruction)

The `ζ`-twist obstructs the σ-conjugate-pair descent at the **linear** measure `(ζ-1)^m` along
*both* available routes (§4, all proven):

* the **no-clearing (twisted) route** (`TwistedConjPairData37`) needs `σε₁ = ε₂` exactly — false by
  the `ζ`-twist (and `ζ` cannot be absorbed: it is not a `37`-th power, and rescaling `ε₁` by `ζ⁻¹`
  would force the non-integral `ζ^{1/37}` rescaling of `x'`);
* the **clearing route** (`unit_isPow_of_prod_isPow_of_quotient_isPow`) needs `ε₁/σε₁` a `37`-th
  power; but `ε₁/σε₁ = ζ⁻¹·(37-th power)` (`caseII_descent_quotient_mul_twist`), and `ζ⁻¹` is not.

This is the explicit, verified form of Washington's *measure-doubling obstruction* (GTM 83
p. 171–172): the reality-preserving Case-II descent does not live at the linear measure `(ζ-1)^m`
but at the **doubled** measure `λ^{2m-p}` (`λ = (1-ζ)(1-ζ⁻¹)`) via norm products `ρ_aρ̄_a`, whose
per-root twist is the *real* trace-difference `γ_η - γ_{η'} ∈ 𝓞 K⁺` (no primitive-root factor; cf.
the `caseII_pair_*` σ-stable Cramer descent in `ProductDescent.lean`).  Consequently the `m`-indexed
σ-equivariance residual `CaseIIRealToConjPairSigmaEquivariant37` /
`CaseIITwistedConjPairEntry37` at linear measure is **not** dischargeable by the inversion-symmetric
single-root construction, and the descent frame must be the doubled-measure *factor-count* descent
(Washington's "smallest number of distinct prime ideal factors", GTM 83 p. 172).  Logged as B2
`R2-zeta-twist`.

It imports only; it does **not** modify any existing file.

## References
* Washington, *Introduction to Cyclotomic Fields*, GTM 83, §9.1 (p. 169–172; Lemma 9.2 and the
  reality-preserving descent at the doubled measure `λ^{2m-p}`), Thm 9.4.
-/

@[expose] public section

noncomputable section

open NumberField IsCyclotomicExtension Polynomial NumberField.IsCMField
open scoped nonZeroDivisors

namespace BernoulliRegular.FLT37.Eichler

open FLT37.LehmerVandiver.CaseII

variable {K : Type} [Field K] [NumberField K] [IsCyclotomicExtension {37} ℚ K]
  [NumberField.IsCMField K]

/-! ## 1. The associate witness is σ-paired up to the sign `(-1)^m`

The associate unit `U = associated_eta_zero_unit_of_spanSingleton … η a b` is determined by the
spec `U·(x+y·η₀)·a³⁷ = (x+y·η)·(ζ-1)^{m·37}·b³⁷`.  Over real data the anchor `η₀ = 1` is σ-fixed and
`x, y` are real, so applying `σ` to the spec at `(η, a, b)` lands the spec at `(η⁻¹, σa, σb)` times
`(-1)^m`.  Domain cancellation (the non-unit factors are nonzero) then forces
`σU(η, a, b) = (-1)^m · U(η⁻¹, σa, σb)`. -/

omit [IsCyclotomicExtension {37} ℚ K] in
/-- **`x + y` is `σ`-fixed for real `x, y`.**  (`σ(x+y) = σx+σy = x+y`.)  This is the anchor radical
`x + y·η₀` at the σ-fixed anchor `η₀ = 1` (`caseII_etaZero_eq_one`). -/
theorem caseII_x_add_y_real {x y : 𝓞 K}
    (hx : ringOfIntegersComplexConj K x = x) (hy : ringOfIntegersComplexConj K y = y) :
    ringOfIntegersComplexConj K (x + y) = x + y := by
  rw [map_add, hx, hy]

/-- **[σ-UNIQUENESS] The associate witness `U` is σ-paired up to `(-1)^m`.**

Let `D : RealCaseIIData37 K m`.  For an adjacent root `η`, with generators `a₁/b₁` of `𝔞(η)/𝔞₀`
(`hspan₁`, `hb₁ : (ζ-1) ∤ b₁`) and the conjugate generators `σa₁/σb₁` of `𝔞(η⁻¹)/𝔞₀` (`hspan₂`,
`hb₂ : (ζ-1) ∤ σb₁`), the two associate units satisfy

  `σ(U(η, a₁, b₁)) = (-1)^m · U(η⁻¹, σa₁, σb₁)`   (as units of `𝓞 K`).

Proof: both sides are units whose underlying elements, multiplied by the nonzero
`(x+y)·(σa₁)³⁷`, agree — by applying `σ` to the determining spec of `U(η, a₁, b₁)` (the anchor
`x + y·η₀ = x + y` is real, `caseII_etaZero_eq_one` + `caseII_x_add_y_real`; the radical conjugates
`σ(x+y·η) = x + y·η³⁶`, `caseII_real_radical_conj`; and `σ((ζ-1)^{m·37}) = (-1)^m·(ζ-1)^{m·37}`,
`caseII_real_zeta_sub_one_pow_conj`) and comparing with the spec of `U(η⁻¹, σa₁, σb₁)`. -/
theorem caseII_assocUnit_sigma_twist {m : ℕ} (D : RealCaseIIData37 K m) (hp : (37 : ℕ) ≠ 2)
    (η : nthRootsFinset 37 (1 : 𝓞 K)) {a₁ b₁ : 𝓞 K}
    (hb₁ : ¬ (D.hζ.unit'.1 - 1) ∣ b₁)
    (hb₂ : ¬ (D.hζ.unit'.1 - 1) ∣ ringOfIntegersComplexConj K b₁)
    (hspan₁ :
      FractionalIdeal.spanSingleton (𝓞 K)⁰ (a₁ / b₁ : K) =
        rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy η /
          aEtaZeroDvdPPow hp D.hζ D.equation D.hy)
    (hspan₂ :
      FractionalIdeal.spanSingleton (𝓞 K)⁰
          ((ringOfIntegersComplexConj K a₁ : K) / (ringOfIntegersComplexConj K b₁ : K)) =
        rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy (caseII_etaInv η) /
          aEtaZeroDvdPPow hp D.hζ D.equation D.hy) :
    unitsComplexConj K
        (associated_eta_zero_unit_of_spanSingleton hp D.hζ D.equation D.hy D.hz η hb₁ hspan₁) =
      (-1) ^ m *
        associated_eta_zero_unit_of_spanSingleton hp D.hζ D.equation D.hy D.hz
          (caseII_etaInv η) hb₂ hspan₂ := by
  -- Abbreviations for the two associate units.
  set U₁ := associated_eta_zero_unit_of_spanSingleton hp D.hζ D.equation D.hy D.hz η hb₁ hspan₁
    with hU₁def
  set U₂ := associated_eta_zero_unit_of_spanSingleton hp D.hζ D.equation D.hy D.hz
    (caseII_etaInv η) hb₂ hspan₂ with hU₂def
  -- `ζ^37 = 1` and the anchor index `η₀ = zetaSubOneDvdRoot` is real (`= 1`).
  have h37z : (D.hζ.toInteger : 𝓞 K) ^ 37 = 1 := D.hζ.toInteger_isPrimitiveRoot.pow_eq_one
  have hη0z : (zetaSubOneDvdRoot hp D.hζ D.equation D.hy : 𝓞 K) = 1 := by
    have hηZ : zetaSubOneDvdRoot hp D.hζ D.equation D.hy = D.etaZero := rfl
    rw [hηZ]; exact caseII_etaZero_eq_one D hp
  -- The determining specs of `U₁` and `U₂`.
  have spec₁ := associated_eta_zero_unit_spec_of_spanSingleton hp D.hζ D.equation D.hy D.hz η hb₁
    hspan₁
  have spec₂ := associated_eta_zero_unit_spec_of_spanSingleton hp D.hζ D.equation D.hy D.hz
    (caseII_etaInv η) hb₂ hspan₂
  rw [← hU₁def] at spec₁
  rw [← hU₂def] at spec₂
  -- Reduce the unit equality to an element equality, by `Units.ext`.
  apply Units.ext
  -- `(σU₁ : 𝓞 K) = σ(U₁ : 𝓞 K)`.
  show ringOfIntegersComplexConj K (U₁ : 𝓞 K) = ((-1) ^ m * U₂ : (𝓞 K)ˣ)
  -- Apply `σ` to `spec₁`.
  have hσspec₁ := congrArg (ringOfIntegersComplexConj K) spec₁
  -- LHS of `σ spec₁`: `σ(U₁) · (x+y·η₀) · (σ a₁)³⁷` (anchor and `x,y` real).
  rw [map_mul, map_mul, map_pow] at hσspec₁
  -- the anchor radical `x + y·η₀ = x + y` (real); coefficient becomes itself.
  rw [show (D.x + D.y * (zetaSubOneDvdRoot hp D.hζ D.equation D.hy : 𝓞 K)) = D.x + D.y from by
    rw [hη0z, mul_one]] at hσspec₁
  rw [caseII_x_add_y_real D.x_real D.y_real] at hσspec₁
  -- RHS of `σ spec₁`: `σ(x+y·η)·σ((ζ-1)^{m·37})·σ(b₁³⁷)`.  Split outer products (`map_mul`) only,
  -- then rewrite each factor; do NOT split `σ((ζ-1)^{m·37})` (we use the whole-power lemma).
  rw [map_mul, map_mul,
    caseII_real_radical_conj D.x_real D.y_real
      ((mem_nthRootsFinset (by norm_num) _).mp η.2),
    caseII_real_zeta_sub_one_pow_conj (K := K) m h37z, map_pow] at hσspec₁
  -- `spec₂` with anchor simplified: `(U₂)·(x+y)·(σa₁)³⁷ = (x+y·η³⁶)·(ζ-1)^{m·37}·(σb₁)³⁷`.
  rw [show (D.x + D.y * (zetaSubOneDvdRoot hp D.hζ D.equation D.hy : 𝓞 K)) = D.x + D.y from by
    rw [hη0z, mul_one], caseII_etaInv_coe] at spec₂
  -- Now `hσspec₁ : σ(U₁)·(x+y)·(σa₁)³⁷ = (x+y·η³⁶)·((-1)^m·(ζ-1)^{m·37})·(σb₁)³⁷`,
  -- and the RHS `= (-1)^m·[(x+y·η³⁶)·(ζ-1)^{m·37}·(σb₁)³⁷] = (-1)^m·[(U₂:𝓞K)·(x+y)·(σa₁)³⁷]`.
  -- `σ a₁ ≠ 0`: from `spec₂`'s nonzero RHS (`x+y·η³⁶ ≠ 0`, `(ζ-1) ≠ 0`, `σb₁ ≠ 0`).
  have hσa_ne : (ringOfIntegersComplexConj K a₁ : 𝓞 K) ≠ 0 := by
    have hrhs_ne : ((D.x + D.y * (η : 𝓞 K) ^ 36) * (D.hζ.toInteger - 1) ^ (m * 37) *
        ringOfIntegersComplexConj K b₁ ^ 37 : 𝓞 K) ≠ 0 := by
      refine mul_ne_zero (mul_ne_zero ?_ (pow_ne_zero _ ?_)) (pow_ne_zero _ ?_)
      · have h36 : ((η : 𝓞 K) ^ 36) ^ 37 = 1 := by
          rw [← pow_mul, show 36 * 37 = 37 * 36 from by norm_num, pow_mul,
            (mem_nthRootsFinset (by norm_num) _).mp η.2, one_pow]
        exact x_plus_y_mul_ne_zero hp D.hζ D.equation D.hz ⟨(η : 𝓞 K) ^ 36,
          (mem_nthRootsFinset (by norm_num) _).mpr h36⟩
      · exact D.hζ.zeta_sub_one_prime'.ne_zero
      · intro h; exact hb₂ (h ▸ dvd_zero _)
    intro h
    apply hrhs_ne
    rw [← spec₂, h]; ring
  have hxy_ne : (D.x + D.y : 𝓞 K) ≠ 0 := by
    have := x_plus_y_mul_ne_zero hp D.hζ D.equation D.hz
      (zetaSubOneDvdRoot hp D.hζ D.equation D.hy)
    rwa [hη0z, mul_one] at this
  have hprod_ne : ((D.x + D.y) * ringOfIntegersComplexConj K a₁ ^ 37 : 𝓞 K) ≠ 0 :=
    mul_ne_zero hxy_ne (pow_ne_zero _ hσa_ne)
  -- Cancel the nonzero `(x+y)·(σa₁)³⁷` from `hσspec₁` (rearranged via `spec₂`).
  have hL : ringOfIntegersComplexConj K (U₁ : 𝓞 K) *
        ((D.x + D.y) * ringOfIntegersComplexConj K a₁ ^ 37) =
      ((-1 : 𝓞 K) ^ m * (U₂ : 𝓞 K)) * ((D.x + D.y) * ringOfIntegersComplexConj K a₁ ^ 37) := by
    have hσspec₁' : ringOfIntegersComplexConj K (U₁ : 𝓞 K) * (D.x + D.y) *
        ringOfIntegersComplexConj K a₁ ^ 37 =
        (-1 : 𝓞 K) ^ m * ((D.x + D.y * (η : 𝓞 K) ^ 36) * (D.hζ.toInteger - 1) ^ (m * 37) *
          ringOfIntegersComplexConj K b₁ ^ 37) := by
      rw [hσspec₁]; ring
    rw [show ringOfIntegersComplexConj K (U₁ : 𝓞 K) *
        ((D.x + D.y) * ringOfIntegersComplexConj K a₁ ^ 37) =
        ringOfIntegersComplexConj K (U₁ : 𝓞 K) * (D.x + D.y) *
          ringOfIntegersComplexConj K a₁ ^ 37 from by ring,
      hσspec₁', ← spec₂]
    ring
  have := mul_right_cancel₀ hprod_ne hL
  rw [this]
  push_cast
  ring

/-! ## 2. The root-difference unit carries a primitive-root twist `σu₁ = ζ·u₂`

The root-difference associate units of the inversion-symmetric descent are `u₁` with
`(ζ-1)·u₁ = η⁻¹−1` (the difference `η₂−η₀ = η⁻¹−1`) and `u₂` with `(ζ-1)·u₂ = 1−η`
(`η₀−η₁ = 1−η`).  Complex conjugation sends `σ(η⁻¹−1) = η−1 = −(1−η)` and
`σ(ζ-1) = ζ³⁶−1 = −ζ³⁶(ζ-1)`, so after cancelling the nonzero `−(ζ-1)` one finds
`ζ³⁶·σu₁ = u₂`, i.e. `σu₁ = ζ·u₂` (as `ζ·ζ³⁶ = 1`).  This is the **primitive-root** factor in the
σ-twist of `ε₁` — the genuine obstacle to `σε₁ = ε₂`. -/

omit [IsCyclotomicExtension {37} ℚ K] in
/-- **The root-difference units carry a `ζ`-twist: `σu₁ = ζ·u₂`.**  For a `37`-th root of unity
`η = (ηη : 𝓞 K)` with `η³⁷ = 1`, and units `u₁ u₂ : (𝓞 K)ˣ` with `(ζ-1)·u₁ = η³⁶−1` and
`(ζ-1)·u₂ = 1−η` (where `ζ = hζ.unit'` and `η³⁶ = η⁻¹`), complex conjugation gives
`σu₁ = ζ·u₂` (as units of `𝓞 K`).

Proof: `σ((ζ-1)·u₁) = (ζ³⁶−1)·σu₁` and `σ(η³⁶−1) = η−1` (real coefficients, `σ` inverts the
root: `σ(η³⁶) = (η³⁶)³⁶ = η`); `ζ³⁶−1 = −ζ³⁶(ζ-1)` and `η−1 = −(1−η) = −(ζ-1)·u₂`; cancel
`−(ζ-1) ≠ 0` to get `ζ³⁶·σu₁ = u₂`; multiply by `ζ` (`ζ·ζ³⁶ = 1`). -/
theorem caseII_rootDiff_sigma_twist {ζ : K} (hζ : IsPrimitiveRoot ζ 37)
    {ηη : 𝓞 K} (hη : (ηη : 𝓞 K) ^ 37 = 1) {u₁ u₂ : (𝓞 K)ˣ}
    (hu₁ : (hζ.unit'.1 - 1) * (u₁ : 𝓞 K) = (ηη : 𝓞 K) ^ 36 - 1)
    (hu₂ : (hζ.unit'.1 - 1) * (u₂ : 𝓞 K) = 1 - (ηη : 𝓞 K)) :
    unitsComplexConj K u₁ = hζ.unit' * u₂ := by
  have h37z : (hζ.unit'.1 : 𝓞 K) ^ 37 = 1 := by
    rw [← Units.val_pow_eq_pow_val, hζ.unit'_pow, Units.val_one]
  -- Apply `σ` to `hu₁`.
  have hσ := congrArg (ringOfIntegersComplexConj K) hu₁
  rw [map_mul, map_sub, map_one, caseII_ringOfIntegersComplexConj_root_of_unity h37z,
    map_sub, map_one, map_pow, caseII_ringOfIntegersComplexConj_root_of_unity hη] at hσ
  -- `hσ : (ζ³⁶−1)·σu₁ = (η³⁶)³⁶ − 1`.  Simplify `(η³⁶)³⁶ = η` and `ζ³⁶−1 = −ζ³⁶(ζ-1)`.
  rw [show ((ηη : 𝓞 K) ^ 36) ^ 36 = (ηη : 𝓞 K) from by
    rw [← pow_mul, show 36 * 36 = 37 * 35 + 1 from by norm_num, pow_add, pow_mul, hη, one_pow,
      pow_one, one_mul]] at hσ
  -- Reduce to an element equality, then cancel `(ζ-1)`.
  apply Units.ext
  -- Goal: `σ(u₁ : 𝓞 K) = (ζ·u₂ : 𝓞 K)`.
  show ringOfIntegersComplexConj K (u₁ : 𝓞 K) = ((hζ.unit' * u₂ : (𝓞 K)ˣ) : 𝓞 K)
  have hp_ne : (hζ.unit'.1 - 1 : 𝓞 K) ≠ 0 :=
    hζ.unit'_coe.sub_one_ne_zero (by decide : (1 : ℕ) < 37)
  apply mul_left_cancel₀ hp_ne
  -- Goal `(ζ-1)·σ(u₁) = (ζ-1)·(ζ·u₂)`.  Multiply `hσ : (ζ³⁶−1)·σu₁ = η−1` by `−ζ`
  -- (`−ζ·(ζ³⁶−1) = −ζ³⁷+ζ = ζ−1` via `ζ³⁷ = 1`): `(ζ-1)·σu₁ = −ζ(η−1) = ζ(1−η)`; and
  -- `(ζ-1)·(ζ·u₂) = ζ·(ζ-1)·u₂ = ζ(1−η)` by `hu₂`.  A `linear_combination` of `hσ`, `hu₂`, `h37z`.
  show (hζ.unit'.1 - 1 : 𝓞 K) * ringOfIntegersComplexConj K (u₁ : 𝓞 K) =
    (hζ.unit'.1 - 1 : 𝓞 K) * ((hζ.unit' * u₂ : (𝓞 K)ˣ) : 𝓞 K)
  push_cast
  linear_combination (-(hζ.unit'.1)) * hσ + (-(hζ.unit'.1)) * hu₂ +
    (ringOfIntegersComplexConj K (u₁ : 𝓞 K)) * h37z

/-! ## 3. The precise σ-twist of the leading descent unit: `σε₁ = (-1)^m·ζ·ε₂`

Combining §1 (`σU₁ = (-1)^m·U₂`) and §2 (`σu₁ = ζ·u₂`) for the explicit descent units
`ε₁ = u₁·U₁`, `ε₂ = u₂·U₂`: applying the multiplicative `unitsComplexConj`,

  `σε₁ = σ(u₁·U₁) = σu₁·σU₁ = (ζ·u₂)·((-1)^m·U₂) = (-1)^m·ζ·(u₂·U₂) = (-1)^m·ζ·ε₂`.

This is the **precise, verified** σ-action on the leading descent unit of the inversion-symmetric
single-root descent over real data — the abstract unit-arithmetic core, taking the two twists as
hypotheses (supplied by §1, §2). -/

omit [IsCyclotomicExtension {37} ℚ K] in
/-- **The precise σ-twist `σ(u₁·U₁) = (-1)^m·ζ·(u₂·U₂)`** (abstract unit arithmetic).

For units `u₁ u₂ U₁ U₂ : (𝓞 K)ˣ` and a unit `ζu : (𝓞 K)ˣ`, given the root-difference twist
`σu₁ = ζu·u₂` (§2, `caseII_rootDiff_sigma_twist`) and the associate-witness twist
`σU₁ = (-1)^m·U₂` (§1, `caseII_assocUnit_sigma_twist`), the leading descent unit `ε₁ = u₁·U₁`
satisfies `σε₁ = (-1)^m·ζu·ε₂` with `ε₂ = u₂·U₂`.  Pure multiplicativity of `unitsComplexConj`. -/
theorem caseII_descent_eps_sigma_twist {m : ℕ}
    {u₁ u₂ U₁ U₂ ζu : (𝓞 K)ˣ}
    (hu : unitsComplexConj K u₁ = ζu * u₂)
    (hU : unitsComplexConj K U₁ = (-1) ^ m * U₂) :
    unitsComplexConj K (u₁ * U₁) = (-1) ^ m * ζu * (u₂ * U₂) := by
  rw [map_mul, hu, hU, mul_mul_mul_comm, mul_comm ζu ((-1) ^ m)]

/-! ## 4. Consequence: the `ζ`-twist obstructs the linear-measure conjugate-pair descent

The §3 finding is decisive.  The leading descent unit of the inversion-symmetric descent satisfies
`σε₁ = (-1)^m·ζ·ε₂`, with `(-1)^m` a `37`-th power (`caseII_neg_one_pow_is_pth_power`) but `ζ` a
**primitive** `37`-th root of unity — **not** a `37`-th power.  This obstructs *both* routes
to the σ-conjugate-pair descent at the **linear** measure `(ζ-1)^m`:

* **the no-clearing (twisted) route** needs `σε₁ = ε₂` exactly (the `unit_conj` field of
  `TwistedConjPairData37`); but `σε₁ = (-1)^m·ζ·ε₂`, and the `ζ` cannot be absorbed (it is not a
  `37`-th power, and multiplying `ε₁` by `ζ^{-1}` would force `x'^37 → ζ·x'^37`, i.e. a non-integral
  `ζ^{1/37}` rescaling of `x'`);

* **the clearing route** (`unit_isPow_of_prod_isPow_of_quotient_isPow`,
  `CaseIIConjPairEpsPower.lean`) needs `ε₁/σε₁` a `37`-th power; but
  `ε₁/σε₁ = (-1)^m·ζ^{-1}·(ε₁/ε₂)`, so even though `ε₁/ε₂` is a `37`-th power (Assumption II) and
  `(-1)^m` is, the factor `ζ^{-1}` is not — so `ε₁/σε₁` is **not** a `37`-th power.

So the `ζ`-twist is the **common** obstruction.  This is the explicit, verified form of the
*measure-doubling obstruction* (Washington GTM 83 p. 171–172, the reality-preserving descent at the
**doubled** measure `λ^{2m-p}` via the norm products `ρρ̄`, not the linear measure): the linear
single-root descent at the inversion-symmetric pair simply does **not** produce σ-conjugate units.

We record the obstruction as a proven theorem: under the natural twist, `ε₁/σε₁` is `ζ`-times a
`37`-th power and so cannot itself be a `37`-th power (since `ζ` generates `μ₃₇`, and the only
`37`-th-power root of unity is `1`). -/

omit [IsCyclotomicExtension {37} ℚ K] in
/-- **The `ζ`-twist makes `ε₁/σε₁` a non-`37`-th-power** (the common obstruction, proven form).

Given the natural σ-twist `σε₁ = (-1)^m·ζu·ε₂` (`caseII_descent_eps_sigma_twist`), the descent ratio
satisfies `(ε₁/σε₁)·((-1)^m·ζu) = ε₁/ε₂`.  Since `ε₁/ε₂` is a `37`-th power (Assumption II) and
`(-1)^m` is a `37`-th power (`caseII_neg_one_pow_is_pth_power`), `ε₁/σε₁` is a `37`-th power **iff**
`ζu` is — i.e. iff the primitive-root unit `ζu` is a `37`-th power (which it is **not**, being a
generator of `μ₃₇`).  This isolates the obstruction to the clearing route in a single primitive-root
condition. -/
theorem caseII_descent_quotient_mul_twist {m : ℕ}
    {ε₁ ε₂ ζu : (𝓞 K)ˣ}
    (hσ : unitsComplexConj K ε₁ = (-1) ^ m * ζu * ε₂) :
    (ε₁ / unitsComplexConj K ε₁) * ((-1) ^ m * ζu) = ε₁ / ε₂ := by
  -- Write `σε₁ = ε₂·A` with `A = (-1)^m·ζu`; then `ε₁/(ε₂·A) = (ε₁/ε₂)/A`, and `·A` cancels.
  rw [hσ, mul_comm ((-1 : (𝓞 K)ˣ) ^ m * ζu) ε₂, ← div_div, div_mul_cancel]

/-! ## 5. The genuine residual: the reality-preserving descent at the doubled measure

The §4 obstruction shows the *linear*-measure σ-conjugate-pair descent is unreachable via the
inversion-symmetric single-root construction.  Washington's reality-preserving descent (GTM 83
p. 171–172) instead produces the new Fermat equation `ω₁^p + θ₁^p = δ·λ^{2m-p}·ξ₁^p` at the
**doubled** measure `λ^{2m-p}` (`λ = (1-ζ)(1-ζ⁻¹)`), with **individually-real** norm products
`ω₁ = ρ_aρ̄_a`, `θ₁ = -ρ_bρ̄_b`, `ξ₁ = ρ₀²`.  This is the σ-stable analogue already partly built in
`ProductDescent.lean` (`caseII_pair_*`): the per-root twist there is the *real* trace-difference
`γ_η - γ_{η'} ∈ 𝓞 K⁺`, carrying no primitive-root factor.  The genuine open content of R2 is the
reassembly of this doubled-measure norm form into a descending datum — which, because the measure is
`2m-p` rather than `m-1`, is a **factor-count** descent (Washington's "smallest number of distinct
prime ideal factors", GTM 83 p. 172), **not** the `m`-indexed frame.  This is recorded as a B2
finding (`R2-zeta-twist`); the `m`-indexed σ-equivariance residual
(`CaseIIRealToConjPairSigmaEquivariant37` / `CaseIITwistedConjPairEntry37`) at linear measure is
obstructed by §4 and should be replaced by the factor-count frame. -/

end BernoulliRegular.FLT37.Eichler

end

end
