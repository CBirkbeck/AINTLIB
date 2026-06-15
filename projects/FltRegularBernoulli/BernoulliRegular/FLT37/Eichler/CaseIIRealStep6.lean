import BernoulliRegular.FLT37.Eichler.CaseIILemma98Mirimanoff5
import BernoulliRegular.FLT37.Eichler.CaseIIConjugatePairedGenerators

/-!
# Washington Lemma 9.8 step 6 over `RealCaseIIData37` (the `ρ_a`-reality core, real data)

This file re-keys Washington *Introduction to Cyclotomic Fields*, 2nd ed., GTM 83, Lemma 9.8
**step 6** — the `ρ_a`-reality cyclic-power congruence — from the bare-`CaseIIData37` form
`CaseIIMirimanoffStep6Cong37` (`CaseIILemma98Mirimanoff5.lean`) to the reality-restricted datum
`RealCaseIIData37` (`σx = x`, `σy = y`).  This is the form Washington's proof actually uses: the
real generators `ρ_a` (`σρ_a = ρ_{-a}`) of step 6 exist as elements only over real data
(II1 / `c = 1`,
`caseIIRootClassConjFixed37_proven`), not over a bare `CaseIIData37`
(`RealCaseIIData37.map_rootIdeal`: `σ𝔞(η) = 𝔞(η⁻¹)`).

## The σ-reduction (proved here, in full)

Over `RealCaseIIData37`, with the *global* `ζ = zetaPow 37 K`, complex conjugation `σ`
(`ringOfIntegersComplexConj`) sends `σ(ζ^e) = ζ^{-e}` (`caseII_complexConj_zetaPow`) and fixes
`x, y`.  Writing `β = x + ζ^a·y`, conjugation gives `σβ = x + ζ^{-a}·y`, and the elementary identity

  `ζ^a·x + y = ζ^a·(x + ζ^{-a}·y) = ζ^a·σβ`

turns Washington's step-6 congruence `Q(β)^4 = Q(ζ^a·x + y)^4` into the manifestly σ-structured

  `Q(β)^4 = Q(ζ^a)^4 · Q(σβ)^4`     in `𝓞 K / 𝔩`.                                     (★)

This equivalence (`caseII_realStep6_iff_sigma`) is *exact* — `(★)` is neither weaker nor stronger
than step 6 over real data.  We also prove `𝔩 ∤ β` for `a ≢ j (mod 37)`
(`caseII_real_x_add_zetaPow_y_notMem`), from the factor hypothesis `x + ζ^j·y ∈ 𝔩` and
coprimality of conjugate factors mod the prime `𝔩` (the residue-field computation
`Q(β) = Q(y)·Q(ζ^a - ζ^j) ≠ 0`).

## The smallest residual: Washington's `ρ_a`-reality (the conjugate `γ`-ratio is a `p`-th power)

The remaining content of step 6 is exactly Washington's `ρ_a`-reality conclusion *over real data*.
`β` factors by the genuinely-principal `(1 - ζ^a)` (which divides `β`, as `(ζ-1) ∣ (β)` and `1-ζ^a`
is associate to `ζ-1`): `β = (1 - ζ^a)·γ` with `γ ∈ 𝓞 K` the Washington normalization
`γ_a = (ω+ζ^aθ)/(1-ζ^a)`; conjugation then forces `σβ = (1 - ζ^{-a})·σγ`.  The *only* surviving
content is that the conjugate ratio is a `p`-th power mod `𝔩`:

  `Q(γ)·Q(σγ)⁻¹ = v^{37}`     in `𝓞 K / 𝔩`.

This is `ρ_a`-reality: `γ_a = ρ_a^p·(real cyclotomic unit)` with `ρ_a` real (`σρ_a = ρ_{-a}`, from
II1's `c = 1` / the conjugate-paired generators of §9.1), so `γ_a/γ_{-a} = (ρ_a/σρ_a)^p`.  From
`(★)` *follows* from this by the proved `(1-ζ^a)`-bookkeeping
(`(1-ζ^a)^4 = ζ^{4a}(1-ζ^{-a})^4`) and the **cyclic-group descent**
(`(Q(γ)·Q(σγ)⁻¹)^4 = v^{148} = 1` because the residue unit group has order `148 = 4·37`, hence
`Q(γ)^4 = Q(σγ)^4`), both proved in full in `caseII_realStep6_sigma_of_gammaRatio`.  We isolate the
`γ`-ratio as the single named residual `CaseIIRealStep6GammaRatioPthPower37` (a `def … : Prop`,
**not** an axiom).  We do **not** posit an element factorization `β = u·w^p` (unsound: the `gcd`
ideal `𝔪` of `(β) = 𝔪·𝔞(ν_a)^p·𝔭` is not a `p`-th power).  The residual is strictly smaller than
step 6 (it drops the `ζ^a`/`(1-ζ^a)` bookkeeping and the cyclic-group step, all proved here), and is
non-vacuous: under it, *no* nontrivial conjugate factor `x + η·y ∈ 𝔩` (`η ≠ 1`) can occur over real
data (`caseII_realStep6_no_nontrivial_factor`), via the proven `caseIIThm95_engine_runs`.

It imports only; it does **not** modify any existing file.

## References
* Washington, *Introduction to Cyclotomic Fields*, 2nd ed., GTM 83, §9.1–9.2 (Lemma 9.8,
  pp. 178–179, steps 1–9).
-/

@[expose] public section

noncomputable section

open NumberField IsCyclotomicExtension Finset Polynomial NumberField.IsCMField

namespace BernoulliRegular.FLT37.Eichler

open FLT37 FLT37.LehmerVandiver.CaseII BernoulliRegular

/-! ## 0. The cyclic-group fact: `𝔩 ∤ w ⟹ (Q w ^ 37) ^ 4 = 1` -/

/-- **`w^{148} ≡ 1 (mod 𝔩)` for `𝔩 ∤ w`**, in the form `((Q w)^37)^4 = 1`.

`(𝓞 K / 𝔩)ˣ` is cyclic of order `148 = 4·37` (`lv149_unit_card`); for `w ∉ 𝔩` its residue `Q w` is a
unit, so `(Q w)^148 = 1`, i.e. `((Q w)^37)^4 = 1`.  This is the cyclic-group step that kills the
`37`-th powers `w^{37} = ρ_a^{37}` in the step-6 congruence. -/
theorem caseII_pow37_pow4_eq_one_of_notMem {w : 𝓞 (CyclotomicField 37 ℚ)} (hw : w ∉ lv149) :
    ((Ideal.Quotient.mk lv149 w) ^ 37) ^ 4 = 1 := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  set Q := Ideal.Quotient.mk lv149 with hQ
  have hw0 : Q w ≠ 0 := fun h => hw ((Ideal.Quotient.eq_zero_iff_mem).mp h)
  -- The residue as a unit `u = Units.mk0 (Q w)`; its order divides `Nat.card (…)ˣ = 148`.
  set u : (𝓞 (CyclotomicField 37 ℚ) ⧸ lv149)ˣ := Units.mk0 (Q w) hw0 with hu
  have hcard : u ^ Nat.card (𝓞 (CyclotomicField 37 ℚ) ⧸ lv149)ˣ = 1 := pow_card_eq_one'
  rw [lv149_unit_card] at hcard
  -- `((Q w)^37)^4 = (Q w)^148 = (u : F)^148 = 1`.
  have hval : ((Q w) ^ 37) ^ 4 = ((u : 𝓞 (CyclotomicField 37 ℚ) ⧸ lv149) ^ 148) := by
    rw [← pow_mul, hu, Units.val_mk0]
  rw [hval, ← Units.val_pow_eq_pow_val, hcard, Units.val_one]

/-! ## 1. The σ-reduction over real data: step 6 ⟺ `Q(β)^4 = Q(ζ^a)^4·Q(σβ)^4` -/

/-- **`ζ^a·x + y = ζ^a·σβ` over real data**, where `β = x + ζ^a·y` and `σβ = x + ζ^{-a}·y`.

The algebraic heart of the reduction: with `σx = x`, `σy = y` and `σ(ζ^a) = ζ^{-a}`, the second
Washington factor `ζ^a·x + y` equals `ζ^a·(x + ζ^{-a}·y) = ζ^a·σβ`.  Stated as an identity in `𝓞 K`,
purely from `σ(ζ^a) = ζ^{-a}` (`caseII_complexConj_zetaPow`) and `zetaPow` multiplicativity
(`ζ^a·ζ^{-a} = 1`). -/
theorem caseII_real_zetaPow_x_add_y_eq {m : ℕ}
    (D : RealCaseIIData37 (CyclotomicField 37 ℚ) m) (a : ℤ) :
    zetaPow 37 (CyclotomicField 37 ℚ) a * D.x + D.y =
      zetaPow 37 (CyclotomicField 37 ℚ) a *
        (D.x + zetaPow 37 (CyclotomicField 37 ℚ) (-a) * D.y) := by
  have hmul : zetaPow 37 (CyclotomicField 37 ℚ) a *
      zetaPow 37 (CyclotomicField 37 ℚ) (-a) = 1 := by
    rw [← zetaPow_add, add_neg_cancel]
    simp [zetaPow]
  -- Expand and use `ζ^a·ζ^{-a} = 1`.
  linear_combination -D.y * hmul

/-- **`σβ = x + ζ^{-a}·y` over real data**, where `β = x + ζ^a·y`.

Complex conjugation fixes `x, y` (`x_real`, `y_real`) and inverts `ζ^a`
(`caseII_complexConj_zetaPow`, `σ(ζ^a) = ζ^{-a}`), so `σ(x + ζ^a·y) = x + ζ^{-a}·y`. -/
theorem caseII_real_complexConj_x_add_zetaPow_y {m : ℕ}
    (D : RealCaseIIData37 (CyclotomicField 37 ℚ) m) (a : ℤ) :
    ringOfIntegersComplexConj (CyclotomicField 37 ℚ)
        (D.x + zetaPow 37 (CyclotomicField 37 ℚ) a * D.y) =
      D.x + zetaPow 37 (CyclotomicField 37 ℚ) (-a) * D.y := by
  rw [map_add, map_mul, caseII_complexConj_zetaPow, D.x_real, D.y_real]

/-- **The σ-reduction of step 6 (one configuration), over real data.**

For `β = x + ζ^a·y`, Washington's step-6 congruence `Q(β)^4 = Q(ζ^a·x + y)^4` is **equivalent** to
the manifestly σ-structured `Q(β)^4 = Q(ζ^a)^4·Q(σβ)^4`, where `σβ = x + ζ^{-a}·y`.  Proof: rewrite
`ζ^a·x + y = ζ^a·σβ` (`caseII_real_zetaPow_x_add_y_eq` + `caseII_real_complexConj_x_add_zetaPow_y`),
push `Q` through the product, and expand `(Q(ζ^a)·Q(σβ))^4`.  This is *exact*: no inequality, no
extra hypothesis. -/
theorem caseII_realStep6_iff_sigma {m : ℕ}
    (D : RealCaseIIData37 (CyclotomicField 37 ℚ) m) (a : ℤ) :
    (Ideal.Quotient.mk lv149 (D.x + zetaPow 37 (CyclotomicField 37 ℚ) a * D.y)) ^ 4 =
        (Ideal.Quotient.mk lv149
          (zetaPow 37 (CyclotomicField 37 ℚ) a * D.x + D.y)) ^ 4 ↔
      (Ideal.Quotient.mk lv149 (D.x + zetaPow 37 (CyclotomicField 37 ℚ) a * D.y)) ^ 4 =
        (Ideal.Quotient.mk lv149 (zetaPow 37 (CyclotomicField 37 ℚ) a)) ^ 4 *
          (Ideal.Quotient.mk lv149
            (ringOfIntegersComplexConj (CyclotomicField 37 ℚ)
              (D.x + zetaPow 37 (CyclotomicField 37 ℚ) a * D.y))) ^ 4 := by
  set Q := Ideal.Quotient.mk lv149 with hQ
  -- `ζ^a·x + y = ζ^a·σβ`, so `Q(ζ^a·x+y) = Q(ζ^a)·Q(σβ)`.
  have hfac : Q (zetaPow 37 (CyclotomicField 37 ℚ) a * D.x + D.y) =
      Q (zetaPow 37 (CyclotomicField 37 ℚ) a) *
        Q (ringOfIntegersComplexConj (CyclotomicField 37 ℚ)
          (D.x + zetaPow 37 (CyclotomicField 37 ℚ) a * D.y)) := by
    rw [caseII_real_zetaPow_x_add_y_eq D a, map_mul,
      caseII_real_complexConj_x_add_zetaPow_y D a]
  rw [hfac, mul_pow]

/-! ## 2. `𝔩 ∤ β` for the conjugate factors `a ≢ j (mod 37)` -/

/-- **`𝔩 ∤ (x + ζ^a·y)` for `a ≢ j (mod 37)`**, given the factor hypothesis `x + ζ^j·y ∈ 𝔩` and
`𝔩 ∤ y` (Lemma 9.6).

In the residue field, the factor hypothesis gives `Q(x) = -Q(ζ^j)·Q(y)`, so
`Q(x + ζ^a·y) = Q(y)·Q(ζ^a - ζ^j)`.  Both factors are nonzero — `Q(y) ≠ 0` (`𝔩 ∤ y`) and
`Q(ζ^a - ζ^j) ≠ 0` (`caseII_zetaPow_sub_zetaPow_notMem`, `a ≢ j`) — so in the field `𝓞 K / 𝔩` the
product is nonzero, i.e. `x + ζ^a·y ∉ 𝔩`.  (The same computation as in
`caseII_step7_of_step6`'s factor identity.) -/
theorem caseII_real_x_add_zetaPow_y_notMem {m : ℕ}
    (D : RealCaseIIData37 (CyclotomicField 37 ℚ) m) {j : ℤ}
    (hfac : D.x + zetaPow 37 (CyclotomicField 37 ℚ) j * D.y ∈ lv149)
    (hy : D.y ∉ lv149) {a : ℤ} (haj : ¬ (37 : ℤ) ∣ (a - j)) :
    D.x + zetaPow 37 (CyclotomicField 37 ℚ) a * D.y ∉ lv149 := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  set Q := Ideal.Quotient.mk lv149 with hQ
  intro hmem
  -- `Q(x) = -Q(ζ^j)·Q(y)` from the factor hypothesis.
  have hx_eq : Q D.x =
      -(Q (zetaPow 37 (CyclotomicField 37 ℚ) j) * Q D.y) := by
    have hzero : Q (D.x + zetaPow 37 (CyclotomicField 37 ℚ) j * D.y) = 0 :=
      (Ideal.Quotient.eq_zero_iff_mem).mpr hfac
    rw [map_add, map_mul] at hzero
    linear_combination hzero
  -- `Q(x + ζ^a·y) = Q(y)·Q(ζ^a - ζ^j)`.
  have hL : Q (D.x + zetaPow 37 (CyclotomicField 37 ℚ) a * D.y) =
      Q D.y * Q (zetaPow 37 (CyclotomicField 37 ℚ) a -
        zetaPow 37 (CyclotomicField 37 ℚ) j) := by
    rw [map_add, map_mul, map_sub, hx_eq]; ring
  -- This is `0` by `hmem`, so the product of two nonzero field elements is `0` — contradiction.
  have hzeroL : Q (D.x + zetaPow 37 (CyclotomicField 37 ℚ) a * D.y) = 0 :=
    (Ideal.Quotient.eq_zero_iff_mem).mpr hmem
  rw [hL] at hzeroL
  have hy0 : Q D.y ≠ 0 := fun h => hy ((Ideal.Quotient.eq_zero_iff_mem).mp h)
  have hz0 : Q (zetaPow 37 (CyclotomicField 37 ℚ) a -
      zetaPow 37 (CyclotomicField 37 ℚ) j) ≠ 0 := fun h =>
    caseII_zetaPow_sub_zetaPow_notMem haj ((Ideal.Quotient.eq_zero_iff_mem).mp h)
  exact (mul_ne_zero hy0 hz0) hzeroL

/-! ## 3. The smallest residual: Washington's `ρ_a`-reality (the conjugate `γ`-ratio is a `p`-th
power mod `𝔩`)

The honest, exactly-equivalent decomposition of step 6 over real data factors `β` *only* by the
genuinely-principal `(1 - ζ^a)` (which divides `β`, since `(ζ-1) ∣ (β)` and `1-ζ^a` is associate to
`ζ-1`): `β = (1 - ζ^a)·γ` with `γ ∈ 𝓞 K` (the Washington-normalized `γ_a = (ω+ζ^aθ)/(1-ζ^a)`).
Conjugation then forces `σβ = (1 - ζ^{-a})·σγ`, so `σγ` is the conjugate normalized element
`γ_{-a}`.

The *only* surviving content of step 6 is then Washington's `ρ_a`-reality: `γ_a/γ_{-a}` is a `p`-th
power mod `𝔩`.  Indeed `γ_a = ρ_a^p·(real unit)` with `ρ_a` real (`σρ_a = ρ_{-a}`, from II1's
`c = 1` and the conjugate-paired generators), so
`γ_a/γ_{-a} = (ρ_a/ρ_{-a})^p·(unit/σunit) = (ρ_a/σρ_a)^p`,
a `p`-th power mod `𝔩`.  We isolate exactly this, **not** an element-level factorization `β = u·w^p`
(unsound: the `gcd` ideal `𝔪` of `(β) = 𝔪·𝔞(ν_a)^p·𝔭` is not a `p`-th power, so `β/(1-ζ^a)` is not
`unit·w^p`).  The `(1-ζ^a)`-factorization and the cyclic-group descent `(γ/σγ a p-th power) ⟹
γ^4 ≡ σγ^4` are proved in full (`caseII_realStep6_sigma_of_gammaRatio`); the residual is strictly
smaller than step 6 (it drops the `ζ^a`/`(1-ζ^a)` bookkeeping which is proved here). -/

open FLT37.LehmerVandiver.CaseII in
/-- **[FLT37-CASEII-REAL-STEP6-RESIDUAL] Washington Lemma 9.8 `ρ_a`-reality, over real data.**

For every `RealCaseIIData37` configuration with a nontrivial conjugate factor `x + η·y ∈ 𝔩`
(`η = ζ^j ≠ 1`, `𝔩 ∤ x, y`) and every `a ≢ ±j (mod 37)`, the conjugate factor `β = x + ζ^a·y`
factors as `β = (1 - ζ^a)·γ` (the Washington normalization `γ = γ_a = (ω+ζ^aθ)/(1-ζ^a)`), with
`γ, σγ ∉ 𝔩`,
and the conjugate ratio is a `p`-th power mod `𝔩`: `Q(γ)·Q(σγ)⁻¹ = v^{37}` for some
`v : 𝓞 K / 𝔩`.

This is the genuine `ρ_a`-reality conclusion of Washington Lemma 9.8 (pp. 178–179) *over real data*:
`γ_a = ρ_a^p·(real cyclotomic unit)` with `ρ_a` generating a representative of the root ideal
`𝔞(ν_a)` (principal as a twist of `𝔞(η₀)` by II1's `c = 1`, `caseIIRootClassConjFixed37_proven`) and
`σρ_a = ρ_{-a}` (the conjugate-paired generator, `choose_conjugate_paired_generators`), so
`γ_a/γ_{-a} = (ρ_a/σρ_a)^p` is a `p`-th power mod `𝔩`.  Isolated as a named hypothesis (`def`, not
`axiom`); it is strictly smaller than step 6 over real data — step 6 is recovered from it by the
proved `(1-ζ^a)`-bookkeeping and the cyclic-group descent
(`caseII_realStep6_sigma_of_gammaRatio`). -/
def CaseIIRealStep6GammaRatioPthPower37
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)] : Prop :=
  ∀ {m : ℕ} (D : RealCaseIIData37 (CyclotomicField 37 ℚ) m)
    {η : 𝓞 (CyclotomicField 37 ℚ)},
    η ∈ nthRootsFinset 37 (1 : 𝓞 (CyclotomicField 37 ℚ)) →
    η ≠ 1 →
    D.x ∉ lv149 → D.y ∉ lv149 →
    D.x + η * D.y ∈ lv149 →
    ∀ (j : ℤ), zetaPow 37 (CyclotomicField 37 ℚ) j = η →
    ∀ (a : ℤ), ¬ (37 : ℤ) ∣ (a - j) → ¬ (37 : ℤ) ∣ (a + j) →
      ∃ (γ : 𝓞 (CyclotomicField 37 ℚ)),
        D.x + zetaPow 37 (CyclotomicField 37 ℚ) a * D.y =
            (1 - zetaPow 37 (CyclotomicField 37 ℚ) a) * γ ∧
          γ ∉ lv149 ∧
          ringOfIntegersComplexConj (CyclotomicField 37 ℚ) γ ∉ lv149 ∧
          ∃ (v : 𝓞 (CyclotomicField 37 ℚ) ⧸ lv149),
            (Ideal.Quotient.mk lv149 γ) *
                (Ideal.Quotient.mk lv149
                  (ringOfIntegersComplexConj (CyclotomicField 37 ℚ) γ))⁻¹ = v ^ 37

/-! ## 4. Step 6 (σ-form) from the `γ`-ratio residual, via the cyclic-group descent -/

/-- **`(1 - ζ^a)^4 = ζ^{4a}·(1 - ζ^{-a})^4`.**  From `1 - ζ^a = -ζ^a·(1 - ζ^{-a})` (since
`ζ^a·(1-ζ^{-a}) = ζ^a - 1`) and `(-1)^4 = 1`. -/
theorem caseII_one_sub_zetaPow_pow4 (a : ℤ) :
    (1 - zetaPow 37 (CyclotomicField 37 ℚ) a) ^ 4 =
      zetaPow 37 (CyclotomicField 37 ℚ) a ^ 4 *
        (1 - zetaPow 37 (CyclotomicField 37 ℚ) (-a)) ^ 4 := by
  have hmul : zetaPow 37 (CyclotomicField 37 ℚ) a *
      zetaPow 37 (CyclotomicField 37 ℚ) (-a) = 1 := by
    rw [← zetaPow_add, add_neg_cancel]; simp [zetaPow]
  -- `1 - ζ^a = -ζ^a·(1 - ζ^{-a})`, so the 4th powers (even exponent) match with `ζ^{4a}`.
  have hbase : (1 - zetaPow 37 (CyclotomicField 37 ℚ) a) =
      -(zetaPow 37 (CyclotomicField 37 ℚ) a *
        (1 - zetaPow 37 (CyclotomicField 37 ℚ) (-a))) := by
    rw [mul_sub, mul_one, hmul]; ring
  rw [hbase, neg_pow, mul_pow]
  norm_num

/-- **`v^{148} = 1` for `v ≠ 0` in the residue field `𝓞 K / 𝔩`.**  The residue field is finite with
unit group of order `148` (`lv149_unit_card`), so any nonzero `v` is a unit with `v^{148} = 1`. -/
theorem caseII_residue_pow148_eq_one {v : 𝓞 (CyclotomicField 37 ℚ) ⧸ lv149} (hv0 : v ≠ 0) :
    v ^ 148 = 1 := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  have hcard : (Units.mk0 v hv0) ^ Nat.card (𝓞 (CyclotomicField 37 ℚ) ⧸ lv149)ˣ = 1 :=
    pow_card_eq_one'
  rw [lv149_unit_card] at hcard
  calc v ^ 148 = ((Units.mk0 v hv0 : 𝓞 (CyclotomicField 37 ℚ) ⧸ lv149)) ^ 148 := by
          rw [Units.val_mk0]
    _ = ((Units.mk0 v hv0 ^ 148 : (𝓞 (CyclotomicField 37 ℚ) ⧸ lv149)ˣ) :
          𝓞 (CyclotomicField 37 ℚ) ⧸ lv149) := by rw [Units.val_pow_eq_pow_val]
    _ = 1 := by rw [hcard, Units.val_one]

/-- **The cyclic-group descent: a `p`-th-power ratio is `4`th-power-trivial mod `𝔩`.**

For `γ, δ ∉ 𝔩` with `Q(γ)·Q(δ)⁻¹ = v^{37}` (Washington's `ρ_a`-reality), the `4`th powers agree:
`Q(γ)^4 = Q(δ)^4`.  Proof: `(Q(γ)·Q(δ)⁻¹)^4 = (v^{37})^4 = v^{148} = 1` (the residue unit group has
order `148 = 4·37`, `caseII_residue_pow148_eq_one`; `v ≠ 0` since `Q(γ) ≠ 0`), and `Q(δ) ≠ 0`
cancels. -/
theorem caseII_pow4_eq_of_ratio_isPthPower {γ δ : 𝓞 (CyclotomicField 37 ℚ)}
    (hγ : γ ∉ lv149) (hδ : δ ∉ lv149)
    {v : 𝓞 (CyclotomicField 37 ℚ) ⧸ lv149}
    (hv : (Ideal.Quotient.mk lv149 γ) * (Ideal.Quotient.mk lv149 δ)⁻¹ = v ^ 37) :
    (Ideal.Quotient.mk lv149 γ) ^ 4 = (Ideal.Quotient.mk lv149 δ) ^ 4 := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  set Q := Ideal.Quotient.mk lv149 with hQ
  have hγ0 : Q γ ≠ 0 := fun h => hγ ((Ideal.Quotient.eq_zero_iff_mem).mp h)
  have hδ0 : Q δ ≠ 0 := fun h => hδ ((Ideal.Quotient.eq_zero_iff_mem).mp h)
  -- `v ≠ 0`: else `v^37 = 0 = Q γ·(Q δ)⁻¹`, but `Q γ ≠ 0` and `(Q δ)⁻¹ ≠ 0`.
  have hv0 : v ≠ 0 := by
    rintro rfl
    rw [zero_pow (by decide : (37 : ℕ) ≠ 0)] at hv
    exact (mul_ne_zero hγ0 (inv_ne_zero hδ0)) hv
  -- `(Q γ·(Q δ)⁻¹)^4 = (v^37)^4 = v^148 = 1`.
  have hv4 : (Q γ * (Q δ)⁻¹) ^ 4 = 1 := by
    rw [hv, ← pow_mul]; exact caseII_residue_pow148_eq_one hv0
  -- `Q(γ)^4 = (Q γ·(Q δ)⁻¹)^4·(Q δ)^4 = (Q δ)^4`.
  have hexpand : (Q γ) ^ 4 = (Q γ * (Q δ)⁻¹) ^ 4 * (Q δ) ^ 4 := by
    rw [mul_pow, inv_pow, inv_mul_cancel_right₀ (pow_ne_zero 4 hδ0)]
  rw [hexpand, hv4, one_mul]

/-- **Step 6 (σ-form) from the `γ`-ratio residual** (proven, axiom-clean *given* the residual).

Given `β = (1-ζ^a)·γ` with `γ, σγ ∉ 𝔩` and `Q(γ)·Q(σγ)⁻¹` a `p`-th power mod `𝔩`, the σ-structured
step-6 congruence `Q(β)^4 = Q(ζ^a)^4·Q(σβ)^4` holds.

Proof:
* `Q(β)^4 = Q(1-ζ^a)^4·Q(γ)^4`;
* `σβ = (1-ζ^{-a})·σγ` (apply `σ` to `β = (1-ζ^a)·γ`), so `Q(σβ)^4 = Q(1-ζ^{-a})^4·Q(σγ)^4`, and
  `Q(ζ^a)^4·Q(1-ζ^{-a})^4 = Q(1-ζ^a)^4` (`caseII_one_sub_zetaPow_pow4`);
* the cyclic-group descent `caseII_pow4_eq_of_ratio_isPthPower` gives `Q(γ)^4 = Q(σγ)^4`;
hence `Q(ζ^a)^4·Q(σβ)^4 = Q(1-ζ^a)^4·Q(σγ)^4 = Q(1-ζ^a)^4·Q(γ)^4 = Q(β)^4`. -/
theorem caseII_realStep6_sigma_of_gammaRatio {m : ℕ}
    (D : RealCaseIIData37 (CyclotomicField 37 ℚ) m) (a : ℤ)
    {γ : 𝓞 (CyclotomicField 37 ℚ)}
    (hγ : γ ∉ lv149)
    (hσγ : ringOfIntegersComplexConj (CyclotomicField 37 ℚ) γ ∉ lv149)
    (hβ : D.x + zetaPow 37 (CyclotomicField 37 ℚ) a * D.y =
      (1 - zetaPow 37 (CyclotomicField 37 ℚ) a) * γ)
    {v : 𝓞 (CyclotomicField 37 ℚ) ⧸ lv149}
    (hv : (Ideal.Quotient.mk lv149 γ) *
        (Ideal.Quotient.mk lv149
          (ringOfIntegersComplexConj (CyclotomicField 37 ℚ) γ))⁻¹ = v ^ 37) :
    (Ideal.Quotient.mk lv149 (D.x + zetaPow 37 (CyclotomicField 37 ℚ) a * D.y)) ^ 4 =
      (Ideal.Quotient.mk lv149 (zetaPow 37 (CyclotomicField 37 ℚ) a)) ^ 4 *
        (Ideal.Quotient.mk lv149
          (ringOfIntegersComplexConj (CyclotomicField 37 ℚ)
            (D.x + zetaPow 37 (CyclotomicField 37 ℚ) a * D.y))) ^ 4 := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  set Q := Ideal.Quotient.mk lv149 with hQ
  -- `σβ = (1-ζ^{-a})·σγ` (apply `σ` to `hβ`).
  have hσβ : ringOfIntegersComplexConj (CyclotomicField 37 ℚ)
      (D.x + zetaPow 37 (CyclotomicField 37 ℚ) a * D.y) =
      (1 - zetaPow 37 (CyclotomicField 37 ℚ) (-a)) *
        ringOfIntegersComplexConj (CyclotomicField 37 ℚ) γ := by
    rw [hβ, map_mul, map_sub, map_one, caseII_complexConj_zetaPow]
  -- The cyclic-group descent: `Q(γ)^4 = Q(σγ)^4`.
  have hγ4 := caseII_pow4_eq_of_ratio_isPthPower hγ hσγ hv
  -- `Q(β)^4 = Q(1-ζ^a)^4·Q(γ)^4`.
  have hβ4 : (Q (D.x + zetaPow 37 (CyclotomicField 37 ℚ) a * D.y)) ^ 4 =
      (Q (1 - zetaPow 37 (CyclotomicField 37 ℚ) a)) ^ 4 * (Q γ) ^ 4 := by
    rw [hβ, map_mul, mul_pow]
  -- `Q(σβ)^4 = Q(1-ζ^{-a})^4·Q(σγ)^4`.
  have hσβ4 : (Q (ringOfIntegersComplexConj (CyclotomicField 37 ℚ)
      (D.x + zetaPow 37 (CyclotomicField 37 ℚ) a * D.y))) ^ 4 =
      (Q (1 - zetaPow 37 (CyclotomicField 37 ℚ) (-a))) ^ 4 *
        (Q (ringOfIntegersComplexConj (CyclotomicField 37 ℚ) γ)) ^ 4 := by
    rw [hσβ, map_mul, mul_pow]
  -- `Q(ζ^a)^4·Q(1-ζ^{-a})^4 = Q(1-ζ^a)^4`, from `(1-ζ^a)^4 = ζ^{4a}·(1-ζ^{-a})^4`.
  have hzpow : (Q (zetaPow 37 (CyclotomicField 37 ℚ) a)) ^ 4 *
      (Q (1 - zetaPow 37 (CyclotomicField 37 ℚ) (-a))) ^ 4 =
      (Q (1 - zetaPow 37 (CyclotomicField 37 ℚ) a)) ^ 4 := by
    rw [← map_pow, ← map_pow, ← map_mul, ← caseII_one_sub_zetaPow_pow4 a, map_pow]
  -- Assemble: `Q(ζ^a)^4·Q(σβ)^4 = Q(1-ζ^a)^4·Q(σγ)^4 = Q(1-ζ^a)^4·Q(γ)^4 = Q(β)^4`.
  rw [hβ4, hσβ4, hγ4, ← mul_assoc, hzpow]

/-! ## 5. Washington Lemma 9.8 step 6 over `RealCaseIIData37`, and its discharge -/

open FLT37.LehmerVandiver.CaseII in
/-- **Washington Lemma 9.8 step 6 over `RealCaseIIData37` for `p = 37`** (a `def … : Prop`,
**not** an axiom) — the reality core, re-keyed to the genuine real data.

This is the exact `RealCaseIIData37` analog of `CaseIIMirimanoffStep6Cong37`
(`CaseIILemma98Mirimanoff5.lean`): for every real Case-II descent instance with a *nontrivial*
conjugate factor `D.x + η·D.y ∈ lv149` (`η ∈ μ₃₇`, `η ≠ 1`, `ℓ ∤ D.x, D.y`), the index `j` with
`ζ^j = η`, and every `a ≢ ±j (mod 37)`, Washington's step-6 cyclic-power congruence

  `Q((D.x + ζ^a·D.y)^4) = Q((ζ^a·D.x + D.y)^4)`     in `𝓞 K / lv149`.

Re-keyed to `RealCaseIIData37` (`σx = x`, `σy = y`) because the `ρ_a`-reality global factorization
that proves it (`σρ_a = ρ_{-a}`, `[𝔞(η)] = [𝔞(η⁻¹)]`) exists only over real data (II1 / `c = 1`,
`caseIIRootClassConjFixed37_proven`), **not** over a bare `CaseIIData37`. -/
def CaseIIMirimanoffStep6CongReal37
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)] : Prop :=
  ∀ {m : ℕ}
    (D : RealCaseIIData37 (CyclotomicField 37 ℚ) m)
    {η : 𝓞 (CyclotomicField 37 ℚ)},
    η ∈ nthRootsFinset 37 (1 : 𝓞 (CyclotomicField 37 ℚ)) →
    η ≠ 1 →
    D.x ∉ lv149 → D.y ∉ lv149 →
    D.x + η * D.y ∈ lv149 →
    ∀ (j : ℤ), zetaPow 37 (CyclotomicField 37 ℚ) j = η →
    ∀ (a : ℤ), ¬ (37 : ℤ) ∣ (a - j) → ¬ (37 : ℤ) ∣ (a + j) →
      (Ideal.Quotient.mk lv149
          (D.x + zetaPow 37 (CyclotomicField 37 ℚ) a * D.y)) ^ 4 =
        (Ideal.Quotient.mk lv149
          (zetaPow 37 (CyclotomicField 37 ℚ) a * D.x + D.y)) ^ 4

open FLT37.LehmerVandiver.CaseII in
/-- **Step 6 over real data, from the `ρ_a`-reality `γ`-ratio residual** (proven, axiom-clean
*given* `CaseIIRealStep6GammaRatioPthPower37`).

Composes the two proved halves: the residual gives `β = (1-ζ^a)·γ` with `Q(γ)·Q(σγ)⁻¹` a `p`-th
power mod `𝔩`, from which `caseII_realStep6_sigma_of_gammaRatio` (the `(1-ζ^a)`-bookkeeping + the
cyclic-group descent) proves the σ-form `Q(β)^4 = Q(ζ^a)^4·Q(σβ)^4`, and
`caseII_realStep6_iff_sigma` converts that *exactly* into Washington's step-6 form. -/
theorem caseIIMirimanoffStep6CongReal37_of_gammaRatio
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (h_ratio : CaseIIRealStep6GammaRatioPthPower37) :
    CaseIIMirimanoffStep6CongReal37 := by
  intro m D η hη_mem hη_ne hx hy hsum j hj a haj haj'
  -- The `ρ_a`-reality `γ`-ratio at this configuration.
  obtain ⟨γ, hβ, hγ, hσγ, v, hv⟩ := h_ratio D hη_mem hη_ne hx hy hsum j hj a haj haj'
  -- The σ-form congruence, then convert to Washington's step-6 form.
  rw [caseII_realStep6_iff_sigma D a]
  exact caseII_realStep6_sigma_of_gammaRatio D a hγ hσγ hβ hv

/-! ## 6. The producer over real data, and non-vacuity

The real-data step-6 core feeds the proven step-7/§8.1/producer chain on the underlying
`CaseIIData37` exactly as the bare-data core does, but now over the genuine real data.  Through the
producer it forces `MirimanoffRhoReality37 (i : ZMod 37)`, whose `i ≠ 0` instance is **false**
(`caseII_not_rhoReality_of_ne_zero`, via `caseIIThm95_engine_runs`), so the real-data step-6 core
genuinely asserts Washington's `j = 0`: no nontrivial conjugate factor occurs over real data. -/

open FLT37.LehmerVandiver.CaseII in
/-- **`MirimanoffRhoReality37 (i : ZMod 37)` from the real-data step-6 core** (proven, axiom-clean
*given* `CaseIIMirimanoffStep6CongReal37`).

The real-data step-6 congruence at `j = (i : ℤ)`, fed (on the underlying `CaseIIData37`) through the
proven `caseII_step7_of_step6` (step 7) and `caseII_xiRatio_ind_of_step7` (Washington steps 8–9 +
§8.1), produces `MirimanoffRhoReality37 (i : ZMod 37)` — the same exponent bookkeeping as
`caseII_mirimanoffRhoRealityProducer37_of_step6`, but keyed to the real datum.  `_hV`, `_hSO` are
Washington's standing hypotheses (`¬ 37 ∣ h⁺`, the second-order input), carried to match the
producer shape. -/
theorem caseII_realRhoReality37_of_step6Real
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (h_step6 : CaseIIMirimanoffStep6CongReal37)
    (_hV : ¬ (37 : ℕ) ∣ hPlus (CyclotomicField 37 ℚ))
    (_hSO : NoSecondOrderIrregularPair 37 32)
    {m : ℕ}
    (D : RealCaseIIData37 (CyclotomicField 37 ℚ) m)
    {η : 𝓞 (CyclotomicField 37 ℚ)}
    (hη_mem : η ∈ nthRootsFinset 37 (1 : 𝓞 (CyclotomicField 37 ℚ)))
    (hη_ne : η ≠ 1) (hx : D.x ∉ lv149) (hy : D.y ∉ lv149)
    (hsum : D.x + η * D.y ∈ lv149)
    (i : ℕ)
    (hi : ((zetaU 37 (CyclotomicField 37 ℚ) : 𝓞 (CyclotomicField 37 ℚ)) ^ i = η)) :
    MirimanoffRhoReality37 (i : ZMod 37) := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  -- `zetaPow (i : ℤ) = η`.
  have hzη : zetaPow 37 (CyclotomicField 37 ℚ) ((i : ℕ) : ℤ) = η := by
    rw [zetaPow_natCast]; exact hi
  set iZ : ZMod 37 := (i : ZMod 37) with hiZ
  intro b hb hb2
  -- Washington's exponent `aZ = b + iZ`; integer representative `a = aZ.val`.
  set aZ : ZMod 37 := b + iZ with haZ
  set a : ℤ := ((aZ.val : ℕ) : ℤ) with ha
  -- `s = (b + 2iZ).val`, `d = b.val`, and their coprimality.
  have hs_cop : ((b + 2 * iZ).val).Coprime 37 := caseII_val_coprime hb2
  have hd_cop : (b.val).Coprime 37 := caseII_val_coprime hb
  -- The `ZMod 37` images of `a ± j`.
  have ha_im : ((a : ℤ) : ZMod 37) = aZ := by
    rw [ha]; push_cast; rw [ZMod.natCast_val, ZMod.cast_id]
  have hai_im : ((a + (i : ℤ) : ℤ) : ZMod 37) = b + 2 * iZ := by
    rw [show ((a + (i : ℤ) : ℤ) : ZMod 37)
        = ((a : ℤ) : ZMod 37) + ((i : ℕ) : ZMod 37) from by push_cast; ring, ha_im, haZ, hiZ]
    ring
  have hami_im : ((a - (i : ℤ) : ℤ) : ZMod 37) = b := by
    rw [show ((a - (i : ℤ) : ℤ) : ZMod 37)
        = ((a : ℤ) : ZMod 37) - ((i : ℕ) : ZMod 37) from by push_cast; ring, ha_im, haZ, hiZ]
    ring
  -- Exponent congruences for `xi_ratio_identity` (`s ≡ a+i`, `d ≡ a-i`).
  have hs_eq : zetaU 37 (CyclotomicField 37 ℚ) ^ (a + (i : ℤ)) =
      zetaU 37 (CyclotomicField 37 ℚ) ^ (((b + 2 * iZ).val : ℕ) : ℤ) :=
    caseII_zetaU_zpow_val_eq hai_im
  have hd_eq : zetaU 37 (CyclotomicField 37 ℚ) ^ (a - (i : ℤ)) =
      zetaU 37 (CyclotomicField 37 ℚ) ^ ((b.val : ℕ) : ℤ) :=
    caseII_zetaU_zpow_val_eq hami_im
  -- `a - i ≢ 0`, `a + i ≢ 0`.
  have haj : ¬ (37 : ℤ) ∣ (a - (i : ℤ)) :=
    caseII_not_dvd_of_zmod_ne_zero (by rw [hami_im]; exact hb)
  have haj' : ¬ (37 : ℤ) ∣ (a + (i : ℤ)) :=
    caseII_not_dvd_of_zmod_ne_zero (by rw [hai_im]; exact hb2)
  have hsj : ¬ (37 : ℤ) ∣ (((b + 2 * iZ).val : ℕ) : ℤ) := by
    apply caseII_not_dvd_of_zmod_ne_zero
    push_cast
    rw [ZMod.natCast_val, ZMod.cast_id]
    exact hb2
  -- Real-data step 6 at `j = (i : ℤ)`, `a`.
  have hstep6 := h_step6 D hη_mem hη_ne hx hy hsum ((i : ℕ) : ℤ) hzη a haj haj'
  -- Step 7 from step 6 + the factor hypothesis.
  have hfacL : D.x + zetaPow 37 (CyclotomicField 37 ℚ) ((i : ℕ) : ℤ) * D.y ∈ lv149 := by
    rwa [hzη]
  have hstep7 := caseII_step7_of_step6 D.x D.y a ((i : ℕ) : ℤ) hfacL hy hstep6
  -- Bridge `ζ^{a+i} = ζ^{(b+2i).val}`.
  have hzbridge : zetaPow 37 (CyclotomicField 37 ℚ) (a + ((i : ℕ) : ℤ)) =
      zetaPow 37 (CyclotomicField 37 ℚ) (((b + 2 * iZ).val : ℕ) : ℤ) := by
    apply zetaPow_congr
    have h0 : ((a + ((i : ℕ) : ℤ) - (((b + 2 * iZ).val : ℕ) : ℤ) : ℤ) : ZMod 37) = 0 := by
      rw [Int.cast_sub, hai_im,
        show ((((b + 2 * iZ).val : ℕ) : ℤ) : ZMod 37) = ((b + 2 * iZ).val : ZMod 37) from by
          push_cast; ring,
        ZMod.natCast_val, ZMod.cast_id, sub_self]
    rwa [ZMod.intCast_zmod_eq_zero_iff_dvd] at h0
  rw [hzbridge] at hstep7
  -- Washington steps 8–9 + §8.1.
  have hind := caseII_xiRatio_ind_of_step7 a ((i : ℕ) : ℤ) (b + 2 * iZ).val b.val hs_cop hd_cop
    hs_eq hd_eq haj hsj hstep7
  rw [caseII_xiUnitZMod_eq_xiUnit (c := b + 2 * iZ) hb2 hs_cop,
    caseII_xiUnitZMod_eq_xiUnit (c := b) hb hd_cop,
    isPthPowerModPrime_iff_residueInd37_eq_zero, residueInd37_mul, caseII_residueInd37_inv]
  linear_combination hind

open FLT37.LehmerVandiver.CaseII in
/-- **Non-vacuity of the real-data step-6 core, made explicit.**

Under `CaseIIMirimanoffStep6CongReal37`, for every real Case-II descent no *nontrivial* conjugate
factor `D.x + η·D.y ∈ lv149` (`η ≠ 1`, `ℓ ∤ x, y`) can occur — Washington's `j = 0` over real data.
The real-data step-6 core turns (via `caseII_realRhoReality37_of_step6Real`) into
`MirimanoffRhoReality37 (i : ZMod 37)` (`η = ζ^i`, `i ≠ 0`), which
`caseII_not_rhoReality_of_ne_zero` refutes via the proven `caseIIThm95_engine_runs` (`Q₃₂⁴ ≢ 1`).
So the real-data step-6 congruence is neither vacuously true nor weaker than the bare-data step 6:
it carries exactly Washington's `j = 0` conclusion. -/
theorem caseII_realStep6_no_nontrivial_factor
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (h_step6 : CaseIIMirimanoffStep6CongReal37)
    (hV : ¬ (37 : ℕ) ∣ hPlus (CyclotomicField 37 ℚ))
    (hSO : NoSecondOrderIrregularPair 37 32)
    {m : ℕ}
    (D : RealCaseIIData37 (CyclotomicField 37 ℚ) m)
    {η : 𝓞 (CyclotomicField 37 ℚ)}
    (hη_mem : η ∈ nthRootsFinset 37 (1 : 𝓞 (CyclotomicField 37 ℚ)))
    (hη_ne : η ≠ 1) (hx : D.x ∉ lv149) (hy : D.y ∉ lv149) :
    D.x + η * D.y ∉ lv149 := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  haveI : NeZero (37 : ℕ) := ⟨by decide⟩
  intro hsum
  -- `η = ζ^i` with `i ≠ 0`.
  have hη_pow : η ^ 37 = 1 := by
    rw [mem_nthRootsFinset (by decide : 0 < 37)] at hη_mem; exact hη_mem
  obtain ⟨i, _hi_lt, hi_eq⟩ :=
    (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger_isPrimitiveRoot.eq_pow_of_pow_eq_one hη_pow
  have hi_ne : (i : ZMod 37) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    intro hdvd
    have : i = 0 := by omega
    rw [this, pow_zero] at hi_eq
    exact hη_ne hi_eq.symm
  exact caseII_not_rhoReality_of_ne_zero hi_ne
    (caseII_realRhoReality37_of_step6Real h_step6 hV hSO D hη_mem hη_ne hx hy hsum i hi_eq)

end BernoulliRegular.FLT37.Eichler

end
