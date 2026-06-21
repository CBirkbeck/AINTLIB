import BernoulliRegular.FLT37.Eichler.CaseIIRealAnchoredClass

/-!
# [FLT37-CASEII-R2] The σ-conjugate-pair descent datum and its clean σ-action

This file establishes the **correct invariant** for the FLT37 Case-II reality-preserving descent
(the "structural heart", R2).  Prior endpoints reduced R2 to a residual demanding a solution at the
*linear* descent measure `m'` with `x', y'` **individually σ-fixed** (`σx' = x'`, `σy' = y'`; the
`CaseIIRealDescentSolution37` shape).  But the natural single-root
descent at the σ-stable root pair `{η, η⁻¹}` with conjugate-paired generators produces (per
`caseII_descent_sigma_swap`, `CaseIIRealThetaSolution.lean`) base variables forming a **σ-conjugate
pair** `σx' = y'`, `σy' = x'`, **not** individually σ-fixed.  Uniting the two (Washington's
individually-real `ρ_aρ̄_a` norm form lives at the *doubled* measure `λ^{2m-(p-1)}`) is the
documented obstruction.

The resolution implemented here: descend over **σ-conjugate-pair data** directly.  This is the
structure the linear descent naturally produces and (as proven downstream) preserves.

## The key clean σ-action (this file)

For σ-conjugate-pair data `D` (`σx = y`, `σy = x`), and any `37`-th root `η`:

  `σ(x + y·η) = σx + σy·σ(η) = y + x·η⁻¹ = η⁻¹·(x + y·η)`,

so `x + y·η` and its conjugate are **associates** — and the root ideal `𝔞(η)` is therefore
**individually σ-FIXED**:

  `σ𝔞(η) = 𝔞(η)`.

This is *cleaner* than the individually-real case (where `σ𝔞(η) = 𝔞(η⁻¹)`, `caseII_map_rootIdeal`):
over a σ-conjugate pair each root ideal is its own conjugate.  Consequently `σ[𝔞(η)] = [𝔞(η)]`
holds *for free* (no Lemma 9.2 input), which — combined with the proven `c·σc = 1` (Vandiver,
`37 ∤ h⁺`) — collapses the anchored class `c = [𝔞(η)]·[𝔞(η₀)]⁻¹` to `c² = 1` and (with `c³⁷ = 1`)
to `c = 1`, i.e. the η₀-principalization, *over σ-conjugate-pair data*.

This file proves:
* `ConjPairCaseIIData37` — the σ-conjugate-pair datum (extends `CaseIIData37` with `σx = y`,
  `σy = x`);
* `ConjPairCaseIIData37.map_gcd` — `σ𝔪 = 𝔪` (gcd is symmetric in `x, y`);
* `ConjPairCaseIIData37.conj_x_add_y_eta` — `σ(x+yη) = η⁻¹·(x+yη)` (the associate identity);
* `ConjPairCaseIIData37.map_span_x_add_y_eta` — `σ(x+yη) = (x+yη)` at the principal-ideal level;
* `ConjPairCaseIIData37.map_c`, `.map_rootIdeal` — `σ𝔠(η) = 𝔠(η)`, `σ𝔞(η) = 𝔞(η)` (σ-fixedness).

It imports only; it does **not** modify any existing file.

## References
* Washington, *Introduction to Cyclotomic Fields*, GTM 83, §9.1 (Lemma 9.1, Lemma 9.2), Thm 9.4.
-/

@[expose] public section

noncomputable section

open NumberField Polynomial NumberField.IsCMField

namespace BernoulliRegular.FLT37.Eichler

open FLT37.LehmerVandiver.CaseII

variable {K : Type} [Field K] [NumberField K] [IsCyclotomicExtension {37} ℚ K]
  [NumberField.IsCMField K]

/-! ## 1. The σ-conjugate-pair Case-II descent datum -/

/-- **[CONJ-PAIR-CASEII-DATUM] σ-conjugate-pair Case-II descent datum.**

Washington's second-case descent (GTM 83 §9.1 / Thm 9.4) at the σ-stable root pair `{η, η⁻¹}` with
conjugate-paired generators produces base variables forming a **σ-conjugate pair**: `σx = y`,
`σy = x` (rather than the individually-real `σx = x`, `σy = y` that the rational *base* of the
descent satisfies, and that `RealCaseIIData37` records).  This is the genuine invariant the *linear*
single-root descent preserves.

Over such a datum the σ-action is cleaner: `σ(x+yη) = η⁻¹·(x+yη)` is an *associate* of `x+yη`, so
each root ideal `𝔞(η)` is *individually* σ-fixed (`map_rootIdeal` below) — even stronger than the
individually-real `σ𝔞(η) = 𝔞(η⁻¹)` of `caseII_map_rootIdeal`. -/
structure ConjPairCaseIIData37 (K : Type) [Field K] [NumberField K]
    [IsCyclotomicExtension {37} ℚ K] [NumberField.IsCMField K] (m : ℕ)
    extends CaseIIData37 K m where
  x_conj : NumberField.IsCMField.ringOfIntegersComplexConj K x = y
  y_conj : NumberField.IsCMField.ringOfIntegersComplexConj K y = x

namespace ConjPairCaseIIData37

variable {m : ℕ} (D : ConjPairCaseIIData37 K m)

/-! ## 2. The clean σ-action on the Washington ideals over a σ-conjugate pair -/

/-- **`σ𝔪 = 𝔪`** over a σ-conjugate pair.  `σ` sends `gcd((x),(y))` to `gcd((σx),(σy)) =
gcd((y),(x)) = gcd((x),(y))` — the gcd is symmetric in its two arguments, so even though `σ`
*swaps* `x` and `y`, the ideal `𝔪` is fixed. -/
theorem map_gcd :
    (gcd (Ideal.span ({D.x} : Set (𝓞 K))) (Ideal.span ({D.y} : Set (𝓞 K)))).map
        (ringOfIntegersComplexConj K).toRingEquiv.toRingHom =
      gcd (Ideal.span ({D.x} : Set (𝓞 K))) (Ideal.span ({D.y} : Set (𝓞 K))) := by
  rw [Ideal.gcd_eq_sup, Ideal.map_sup]
  -- `σ(span{x}) = span{σx} = span{y}` and `σ(span{y}) = span{σy} = span{x}`.
  have hx : (Ideal.span ({D.x} : Set (𝓞 K))).map
        (ringOfIntegersComplexConj K).toRingEquiv.toRingHom =
      Ideal.span ({D.y} : Set (𝓞 K)) := by
    rw [Ideal.map_span, Set.image_singleton, show
      (ringOfIntegersComplexConj K).toRingEquiv.toRingHom D.x = D.y from D.x_conj]
  have hy : (Ideal.span ({D.y} : Set (𝓞 K))).map
        (ringOfIntegersComplexConj K).toRingEquiv.toRingHom =
      Ideal.span ({D.x} : Set (𝓞 K)) := by
    rw [Ideal.map_span, Set.image_singleton, show
      (ringOfIntegersComplexConj K).toRingEquiv.toRingHom D.y = D.x from D.y_conj]
  rw [hx, hy, sup_comm, ← Ideal.gcd_eq_sup]

/-- **`σ(x + y·η) = η⁻¹·(x + y·η)`** over a σ-conjugate pair: the conjugate of the Washington
radical `x + y·η` is an *associate* of itself (via the unit `η⁻¹ = η³⁶`).  Proof:
`σ(x+yη) = σx + σy·σ(η) = y + x·η³⁶`, and `y + x·η³⁶ = η³⁶·(x + y·η)` since `η³⁷ = 1`. -/
theorem conj_x_add_y_eta {η : 𝓞 K} (hη : η ^ 37 = 1) :
    NumberField.IsCMField.ringOfIntegersComplexConj K (D.x + D.y * η) =
      η ^ 36 * (D.x + D.y * η) := by
  rw [map_add, map_mul, D.x_conj, D.y_conj,
    caseII_ringOfIntegersComplexConj_root_of_unity hη]
  -- `y + x·η³⁶ = η³⁶·(x + y·η)`, using `η³⁷ = 1` (so `η³⁶·η = 1`).
  linear_combination -D.y * hη

/-- **`σ(𝔦(η)) = 𝔦(η)`** at the principal-ideal level over a σ-conjugate pair: complex conjugation
*fixes* the principal ideal `(x + y·η)` (unlike the individually-real case
`caseII_map_span_x_add_y_eta`, where it maps to `(x + y·η⁻¹)`).  Since `σ(x+yη) = η⁻¹·(x+yη)` is an
associate of `x+yη` (`conj_x_add_y_eta`), the spans coincide. -/
theorem map_span_x_add_y_eta {η : 𝓞 K} (hη : η ^ 37 = 1) :
    (Ideal.span ({D.x + D.y * η} : Set (𝓞 K))).map
        (ringOfIntegersComplexConj K).toRingEquiv.toRingHom =
      Ideal.span ({D.x + D.y * η} : Set (𝓞 K)) := by
  rw [Ideal.map_span, Set.image_singleton]
  have hfe : (ringOfIntegersComplexConj K).toRingEquiv.toRingHom (D.x + D.y * η) =
      η ^ 36 * (D.x + D.y * η) := D.conj_x_add_y_eta hη
  rw [hfe, Ideal.span_singleton_eq_span_singleton]
  -- `Associated (η³⁶·(x+yη)) (x+yη)`: the unit `u = η` (since `η³⁶·(x+yη)·η = η³⁷·(x+yη) = x+yη`).
  exact ⟨⟨η, η ^ 36, by linear_combination hη, by linear_combination hη⟩,
    by linear_combination (D.x + D.y * η) * hη⟩

/-! ## 3. σ-fixedness of the Washington ideals `𝔠(η)`, `𝔞(η)` over a σ-conjugate pair

Mirroring `caseII_map_c` / `caseII_map_rootIdeal` (which give `σ𝔠(η) = 𝔠(η⁻¹)`, `σ𝔞(η) = 𝔞(η⁻¹)`
over individually-real data), but over a σ-conjugate pair the conclusion is the *stronger*
`σ𝔠(η) = 𝔠(η)`, `σ𝔞(η) = 𝔞(η)`:  the σ-action that previously swapped `η ↔ η⁻¹` now *fixes* every
root ideal, because `𝔪` is fixed (gcd symmetric), `𝔭 = (ζ-1)` is fixed, and the principal radical
`(x+yη)` is fixed (`map_span_x_add_y_eta`).  This is the source of the clean `σ[𝔞(η)] = [𝔞(η)]`. -/

variable (hp : (37 : ℕ) ≠ 2)

/-- **`σ𝔠(η) = 𝔠(η)`** over a σ-conjugate pair.  Apply `σ` to `𝔪·𝔠(η)·𝔭 = (x+yη)`, use `σ𝔪 = 𝔪`
(`map_gcd`), `σ𝔭 = 𝔭` (`caseII_map_zetaSubOne_span`), and the *fixedness* `σ(x+yη) = (x+yη)`
(`map_span_x_add_y_eta`), then cancel the (nonzero) `𝔪`, `𝔭` factors. -/
theorem map_c (η : nthRootsFinset 37 (1 : 𝓞 K)) :
    (divZetaSubOneDvdGcd hp D.hζ D.equation D.hy η).map
        (ringOfIntegersComplexConj K).toRingEquiv.toRingHom =
      divZetaSubOneDvdGcd hp D.hζ D.equation D.hy η := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  have h37z : (D.hζ.toInteger) ^ 37 = 1 := D.hζ.toInteger_isPrimitiveRoot.pow_eq_one
  have h37e : (η : 𝓞 K) ^ 37 = 1 := (mem_nthRootsFinset (by norm_num) _).mp η.2
  have hkey := m_mul_c_mul_p hp D.hζ D.equation D.hy η
  have hmap := congrArg
    (Ideal.map (ringOfIntegersComplexConj K).toRingEquiv.toRingHom) hkey
  rw [Ideal.map_mul, Ideal.map_mul, D.map_gcd,
    caseII_map_zetaSubOne_span h37z, D.map_span_x_add_y_eta h37e, ← hkey] at hmap
  have hpne : Ideal.span {(D.hζ.toInteger - 1 : 𝓞 K)} ≠ 0 := p_ne_zero D.hζ
  have hmne : gcd (Ideal.span {D.x}) (Ideal.span {D.y}) ≠ 0 := m_ne_zero D.hζ D.hy
  exact mul_left_cancel₀ hmne (mul_right_cancel₀ hpne hmap)

/-- **`σ𝔞(η) = 𝔞(η)`** over a σ-conjugate pair — the central conjugation identity, *cleaner* than
the individually-real `caseII_map_rootIdeal` (`σ𝔞(η) = 𝔞(η⁻¹)`).  Here each root ideal is its own
conjugate.  Proof: `σ` of `(𝔞 η)^37 = 𝔠(η)` gives `(σ𝔞(η))^37 = 𝔠(η) = (𝔞(η))^37` (`map_c`), then
`p`-th-root uniqueness in the Dedekind ideal monoid. -/
theorem map_rootIdeal (η : nthRootsFinset 37 (1 : 𝓞 K)) :
    (rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy η).map
        (ringOfIntegersComplexConj K).toRingEquiv.toRingHom =
      rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy η := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  have hspec := root_div_zeta_sub_one_dvd_gcd_spec hp D.hζ D.equation D.hy η
  have h1 : ((rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy η).map
        (ringOfIntegersComplexConj K).toRingEquiv.toRingHom) ^ 37 =
      (rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy η) ^ 37 := by
    rw [← Ideal.map_pow, hspec, D.map_c hp η]
  have hAB := (UniqueFactorizationMonoid.pow_dvd_pow_iff_dvd (n := 37) (by norm_num)).mp h1.dvd
  have hBA := (UniqueFactorizationMonoid.pow_dvd_pow_iff_dvd (n := 37) (by norm_num)).mp h1.symm.dvd
  exact le_antisymm (Ideal.dvd_iff_le.mp hBA) (Ideal.dvd_iff_le.mp hAB)

end ConjPairCaseIIData37

end BernoulliRegular.FLT37.Eichler

end

end
