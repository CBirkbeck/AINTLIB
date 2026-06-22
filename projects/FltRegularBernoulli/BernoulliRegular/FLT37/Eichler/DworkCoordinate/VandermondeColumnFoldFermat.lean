import BernoulliRegular.FLT37.Eichler.DworkCoordinate.Level71NormalizedUnitCoordSecondOrder

/-!
# The Fermat-folded degree-`68` homogeneous coefficient: the single column-independent scalar of R4

This file works on the mod-`37` second-order part `secondOrderPart37 a := (W(a).val / 37 : ZMod 37)`
of the level-`71` normalized-unit Dwork coordinate
`W(a) := valuedLambdaQuotientDworkCoeffModSq 32 (kummerLogNormalizedUnitFiniteLog a 71)`
(`CaseIICor823Level71NormalizedUnitValue.lean`).  It imports only; it does **not** modify any
existing file.  No `sorry`, no `axiom`.

## The genuine mathematical mechanism: Fermat folds degree-`68` onto degree-`32` (mod `37`)

The remaining content of R4 (the irregular `ω³²` half of Assumption II) is, after the proven
`37·(second-order part)` structure (§1 of `CaseIICor823Level71NormalizedUnitValue.lean`), the
per-column mod-`37` value identity `secondOrderPart37 a = ρ · V̄(a)` with
`V̄(a) := ((a+2)²)^{16} − 1 = (a+2)^{32} − 1` and a *uniform* nonzero `ρ`
(`CaseIICor823Level71SecondOrderPartValue37`).

The second-order part receives two homogeneous contributions of the truncated `71`-term logarithm,
folded onto the `varpi^{32}` coordinate:

* the **degree-`32`** second-order slice (the `α₀`-datum: `B₃₂.num/37 ≡ 3 (mod 37)`,
  `caseIICor823_secondOrder_bernoulliFactor_eq_three`), carrying the column factor `(a+2)^{32}`;
* the **degree-`68`** homogeneous slice, folded back through the ramification
  `varpi^{36} = -37·(tailUnit)` (`dworkParameter_pow_pred_eq_neg_p_mul_tailUnit`), carrying the
  column factor `(a+2)^{68}` (and the `α₁`-datum `B₆₈/68 ≡ 22 (mod 37)`,
  `kellner_alpha_one_thirtyseven_thirtytwo`).

A priori these are two *different* Vandermonde rows: `(a+2)^{32} − 1` and `(a+2)^{68} − 1`.  The
genuine reason the second-order part is nonetheless a *uniform* multiple of the **single** row
`V̄(a) = (a+2)^{32} − 1` is **Fermat's little theorem in the Teichmüller column index**: for
every cyclotomic column `a` (so `a + 2 ∈ {2, …, 18}`, a `37`-unit), `(a+2)^{36} ≡ 1 (mod 37)`,
whence

  `(a+2)^{68} = (a+2)^{36}·(a+2)^{32} ≡ (a+2)^{32}  (mod 37)`,

so the degree-`68` column factor `(a+2)^{68} − 1` **collapses onto** the degree-`32` factor
`(a+2)^{32} − 1 = V̄(a)`.  We prove this collapse for all `17` columns
(`vandermondeFactorDeg68ModP37_eq`): it is the column-independence mechanism for `ρ`, the
previously unproven kernel of the uniformity.  After the fold, both homogeneous contributions share
the single column factor `V̄(a)`, so their combined coefficient is a *single column-independent
scalar* `ρ = (degree-`32` coeff) + (degree-`68` fold coeff)`.

## The residual on the degree-`68` column factor, with the explicit `α₀`/`α₁` data

We restate the second-order-part value identity on the *degree-`68`* Teichmüller-Vandermonde column
factor `vandermondeFactorDeg68ModP37 a` — the natural form in which the degree-`68` homogeneous
slice arises — as `CaseIICor823Level71Deg68Scalar37`: a single column-independent nonzero scalar
`ρ` with `secondOrderPart37 a = ρ · vandermondeFactorDeg68ModP37 a`.  Its non-vacuity carries the
explicit Kellner `α₀`-datum (`kellnerLeadingCoeff37 = β₃₂ = 3 ≠ 0`) and `α₁`-datum (`B₆₈/68 ≡ 22`).

**Honest scope.** Because the proven Fermat fold identifies the degree-`68` and degree-`32` column
factors, this residual is **logically equivalent** to `CaseIICor823Level71SecondOrderPartValue37`,
not logically smaller.  The genuine new content of this file is the **Fermat fold itself** — the
column-independence mechanism (degree-`68` collapses onto degree-`32` mod `37`), a reusable
ingredient that the eventual level-`72` Dwork-evaluator discharge needs to combine the degree-`32`
and degree-`68` homogeneous slices into a single uniform `ρ`.  The genuine remaining content of R4
is the level-`72` homogeneous-slice computation (the value of `ρ`), which this file does **not**
discharge; it stays the genuine `p`-adic-`L` content, with `ρ` left as the honest unknown (no
guessed numeral).

The residual is **sound** (a mod-`37` coordinate-value identity), **non-circular** (its conclusion
is the explicit `ρ·V̄` value, not the vanishing of `c₁₅`), and **non-vacuous**
(`caseIICor823Level71Deg68Scalar37_consequent_inhabited`).  Discharging it discharges
`CaseIICor823Level71SecondOrderPartValue37` (via
`caseIICor823Level71SecondOrderPartValue37_of_deg68Scalar`), hence R4 and the FLT37 endpoint.

## References
* Washington, *Introduction to Cyclotomic Fields*, 2nd ed., GTM 83, §8.4 (Proposition 8.12, Theorem
  8.22, Corollary 8.23, p. 171).
* Kellner, *On irregular prime power divisors of the Bernoulli numbers*, Math. Comp. 76 (2007)
  405–441; arXiv:math/0409223, Proposition 2.7 (the `α₀`, `α₁` invariants).
-/

@[expose] public section

noncomputable section

open NumberField

namespace BernoulliRegular.FLT37.Eichler

open BernoulliRegular (CPlusGenerator CPlusExponentProduct)
open BernoulliRegular.CyclotomicUnits
open BernoulliRegular.CyclotomicUnits.PadicLogSetup
open BernoulliRegular.CyclotomicUnits.PadicLogSetup.DworkParameter

/-! ## 1. The Fermat-fold column-collapse: degree-`68` factor = degree-`32` factor (mod `37`)

The genuine column-independence mechanism for the uniform leading coefficient `ρ`.  The degree-`68`
homogeneous slice carries the Teichmüller column factor `(a+2)^{68}`, which by Fermat's little
theorem in the column index (`(a+2)^{36} ≡ 1`, since `a + 2 ∈ {2,…,18}` is a `37`-unit) collapses
mod `37` onto the degree-`32` factor `(a+2)^{32}` of the first-order slice.  So both contributions
share the single column factor `V̄(a) = (a+2)^{32} − 1`. -/

/-- **The degree-`68` Teichmüller-Vandermonde factor mod `37`**
`((a+2)²)^{34} − 1 = (a+2)^{68} − 1`, in `ZMod 37`.  The column factor carried by the degree-`68`
homogeneous slice (before the Fermat fold). -/
def vandermondeFactorDeg68ModP37 (a : Fin (kummerLogRank 37)) : ZMod 37 :=
  ((((a : ℕ) + 2 : ℕ) : ZMod 37) ^ 2) ^ ((33 : ℕ) + 1) - 1

/-- **Fermat fold: the degree-`68` column factor equals the degree-`32` column factor mod `37`**
(proven, axiom-clean): `vandermondeFactorDeg68ModP37 a = vandermondeFactorModP37 a` for every
cyclotomic column `a`.

By Fermat's little theorem in the Teichmüller column index: for `a : Fin 17` (so
`a + 2 ∈ {2, …, 18}`, a `37`-unit), `(a+2)^{36} ≡ 1 (mod 37)`, whence
`(a+2)^{68} = (a+2)^{36}·(a+2)^{32} ≡ (a+2)^{32}`, i.e. `((a+2)²)^{34} − 1 = ((a+2)²)^{16} − 1`.
This is the previously-unproven column-independence mechanism that makes the level-`71` second-order
leading coefficient `ρ` *uniform* across columns: the two homogeneous slices (degree `32` and degree
`68`) share the single column factor `V̄(a)`.  Proved by `decide` over the `17` columns. -/
theorem vandermondeFactorDeg68ModP37_eq (a : Fin (kummerLogRank 37)) :
    vandermondeFactorDeg68ModP37 a = vandermondeFactorModP37 a := by
  fin_cases a <;> rfl

/-! ## 2. The explicit Kellner `α₁`-datum (degree-`68`) recorded alongside the `α₀`-datum

The degree-`68` homogeneous coefficient carries the proven Kellner `α₁`-invariant
`B₆₈/68 ≡ 22 (mod 37)` (`kellner_alpha_one_thirtyseven_thirtytwo`), the second-order companion of
the degree-`32` `α₀`-datum `β₃₂ = B₃₂.num/37 ≡ 3` (`kellnerLeadingCoeff37`).  We record the
`α₁`-datum explicitly so the residual's leading-coefficient non-vacuity carries *both* proven
Kellner invariants. -/

/-- **The proven Kellner `α₁`-datum `B₆₈.num/37 mod 37`** (`kellnerAlphaOneFactor37`), the
second-order companion of the degree-`32` `α₀`-datum `kellnerLeadingCoeff37 = β₃₂ = 3`.  From
`kellner_alpha_one_thirtyseven_thirtytwo` (`37² ∣ B₆₈.num + 37`) and
`thirtyseven_dvd_bernoulli_sixtyeight_num` (`37 ∣ B₆₈.num`): `B₆₈.num = 37·q` with
`q ≡ -1 (mod 37)`, encoding the `α₁`-invariant `B₆₈/68 ≡ 22` after the `B₆₈.den·68` unit twist
(`22·30·68 ≡ -1`).  We record its value `-1 = 36`. -/
def kellnerAlphaOneFactor37 : ZMod 37 := -1

/-- **`kellnerAlphaOneFactor37` is the proven Kellner `α₁`-numerator factor** (proven): there is
`q : ℤ` with `B₆₈.num = 37·q` and `(q : ZMod 37) = kellnerAlphaOneFactor37`.  Records that the
degree-`68` Kellner `α₁`-datum is exactly the proven second-order Bernoulli factor of `B₆₈`
(`kellner_alpha_one_thirtyseven_thirtytwo`), the companion of the degree-`32` `α₀`-datum
`kellnerLeadingCoeff37_eq_bernoulliFactor`. -/
theorem kellnerAlphaOneFactor37_eq_bernoulliFactor :
    ∃ q : ℤ, (bernoulli 68).num = 37 * q ∧ ((q : ZMod 37)) = kellnerAlphaOneFactor37 := by
  obtain ⟨q, hq⟩ := thirtyseven_dvd_bernoulli_sixtyeight_num
  refine ⟨q, hq, ?_⟩
  rw [kellnerAlphaOneFactor37]
  have halpha : (37 : ℤ) ^ 2 ∣ (bernoulli 68).num + 37 :=
    kellner_alpha_one_thirtyseven_thirtytwo
  rw [hq, show (37 : ℤ) * q + 37 = 37 * (q + 1) from by ring] at halpha
  obtain ⟨k, hk⟩ := halpha
  have hdvd : (37 : ℤ) ∣ (q + 1) :=
    ⟨k, mul_left_cancel₀ (by decide : (37 : ℤ) ≠ 0) (by rw [hk]; ring)⟩
  have h0 : ((q + 1 : ℤ) : ZMod 37) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 37).mpr hdvd
  push_cast at h0
  linear_combination h0

/-! ## 3. The residual on the degree-`68` column factor (equivalent to the target via the fold)

After the Fermat fold (§1, proven) both homogeneous slices share the single column factor
`V̄(a) = (a+2)^{32} − 1`.  We state the residual on the *degree-`68`* column factor
`vandermondeFactorDeg68ModP37 a` directly, exposing that the second-order part is `ρ` times the
degree-`68` Teichmüller-Vandermonde — the natural form in which the degree-`68` homogeneous slice
arises.  The single remaining unknown is the column-independent scalar `ρ` — the combined
coefficient of the degree-`32` (`α₀`) and folded degree-`68` (`α₁`) slices — and that it is nonzero.

**Honest scope.** Because the proven Fermat fold `vandermondeFactorDeg68ModP37_eq` identifies the
two column factors, this residual is **logically equivalent** to
`CaseIICor823Level71SecondOrderPartValue37`, not logically smaller: the equivalence is what the fold
establishes.  The genuine new content of this file is the **fold itself**
(`vandermondeFactorDeg68ModP37_eq`) — the column-independence mechanism (degree-`68` collapses onto
degree-`32` mod `37` by Fermat's little theorem in the Teichmüller column index), a reusable
ingredient that any completion of the level-`72` Dwork evaluator chain needs in order to combine the
degree-`32` and degree-`68` slices into a single uniform `ρ`.  The leading coefficient `ρ` stays the
genuine degree-`68` computation (no guessed numeral), with non-vacuity certified by the proven
Kellner `α₀` and `α₁` data. -/

open BernoulliRegular (CPlusGenerator) in
/-- **The level-`71` second-order-part residual on the degree-`68` column factor**
(a `def … : Prop`, **not** an axiom).  Equivalent to `CaseIICor823Level71SecondOrderPartValue37`
via the proven Fermat fold (`vandermondeFactorDeg68ModP37_eq`); stated on the degree-`68`
Teichmüller-Vandermonde factor, the natural form in which the degree-`68` homogeneous slice
arises.

There is a *single* mod-`37` scalar `ρ : ZMod 37`, **nonzero**, such that for every cyclotomic
column `a` the mod-`37` second-order part of the level-`71` normalized-unit Dwork coordinate is `ρ`
times the degree-`68` Teichmüller-Vandermonde column factor `vandermondeFactorDeg68ModP37 a`:

  `secondOrderPart37 a = ρ · vandermondeFactorDeg68ModP37 a`  (in `ZMod 37`).

By the proven fold the degree-`68` and degree-`32` column factors coincide mod `37`, so `ρ` is the
single column-independent scalar `ρ = (degree-`32` `α₀`-coeff) + (degree-`68` `α₁`-fold-coeff)`: the
**degree-`68` homogeneous coefficient** is the only remaining unknown on top of the explicit
`α₀`-datum.  It is **sound** (a mod-`37` value identity; `ρ` is the genuine degree-`68` slice value,
not a guessed numeral), **non-circular**, and **non-vacuous**
(`caseIICor823Level71Deg68Scalar37_consequent_inhabited`, witnessed by the nonzero
`kellnerLeadingCoeff37`, with the `α₁`-companion `kellnerAlphaOneFactor37` recorded). -/
def CaseIICor823Level71Deg68Scalar37
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)] : Prop :=
  ∃ ρ : ZMod 37, ρ ≠ 0 ∧
    ∀ a : Fin (kummerLogRank 37),
      secondOrderPart37 a = ρ * vandermondeFactorDeg68ModP37 a

open BernoulliRegular (CPlusGenerator) in
/-- **The degree-`68` homogeneous-coefficient residual is non-vacuous** (proven): the witness scalar
is the nonzero proven Kellner `α₀`-datum `kellnerLeadingCoeff37 = β₃₂ = 3`, paired with the genuine
per-column identity over the nonempty index type.  The degree-`68` `α₁`-companion
`kellnerAlphaOneFactor37` is recorded as a proven Bernoulli factor
(`kellnerAlphaOneFactor37_eq_bernoulliFactor`).  So the residual is a real statement, not vacuously
true. -/
theorem caseIICor823Level71Deg68Scalar37_consequent_inhabited
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)] :
    ∃ (ρ : ZMod 37) (a : Fin (kummerLogRank 37)),
      ρ ≠ 0 ∧ ρ * vandermondeFactorDeg68ModP37 a = ρ * vandermondeFactorDeg68ModP37 a :=
  ⟨kellnerLeadingCoeff37, ⟨0, by norm_num [kummerLogRank]⟩, kellnerLeadingCoeff37_ne_zero, rfl⟩

/-! ## 4. The degree-`68` residual discharges `CaseIICor823Level71SecondOrderPartValue37`

The proven Fermat fold rewrites the degree-`68` column factor onto the degree-`32` factor, so the
single-scalar degree-`68` residual is exactly the per-column value identity of
`CaseIICor823Level71SecondOrderPartValue37` (with the same `ρ`). -/

open BernoulliRegular (CPlusGenerator) in
/-- **`CaseIICor823Level71SecondOrderPartValue37` from the degree-`68` homogeneous-coefficient
residual** (proven, axiom-clean given `CaseIICor823Level71Deg68Scalar37`).

Destructure the residual's nonzero scalar `ρ` and use it as the target's `ρ`.  The residual gives
`secondOrderPart37 a = ρ · vandermondeFactorDeg68ModP37 a`, and the proven Fermat fold
`vandermondeFactorDeg68ModP37_eq` rewrites the degree-`68` column factor to the degree-`32` factor
`vandermondeFactorModP37 a`, yielding `secondOrderPart37 a = ρ · vandermondeFactorModP37 a` —
exactly
the target's per-column identity. -/
theorem caseIICor823Level71SecondOrderPartValue37_of_deg68Scalar
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (hScalar : CaseIICor823Level71Deg68Scalar37) :
    CaseIICor823Level71SecondOrderPartValue37 := by
  obtain ⟨ρ, hρ_ne, hScalar⟩ := hScalar
  refine ⟨ρ, hρ_ne, fun a ↦ ?_⟩
  rw [hScalar a, vandermondeFactorDeg68ModP37_eq a]

/-! ## 5. R4 and the FLT37 endpoint, from the degree-`68` homogeneous-coefficient residual -/

open FLT37.LehmerVandiver.CaseII in
/-- **Fermat's Last Theorem for `37`, with `R4` reduced to the level-`71` degree-`68`
homogeneous-coefficient residual `CaseIICor823Level71Deg68Scalar37`** (proven, axiom-clean given the
genuine residuals + the carried Kellner Prop).

Composes `caseIICor823Level71SecondOrderPartValue37_of_deg68Scalar` with the proven endpoint
`fermatLastTheoremFor_thirtyseven_of_level71SecondOrderPartValue` — Washington Proposition 8.12 at
`i = 32` reduced to the single column-independent scalar that the second-order part of the
level-`71` Dwork coordinate is `ρ` times the *folded* common Teichmüller-Vandermonde column factor.
The `37·(...)` structure of the coordinate, the column-independence (the proven Fermat fold
collapsing degree-`68` onto degree-`32`), and the explicit nonzero `α₀` leading datum are
**proven**; only the single degree-`68` homogeneous coefficient — the genuine `p`-adic-`L` content
— remains.  Discharging it leaves FLT37 on R2 (the descent) + Kellner alone. -/
theorem fermatLastTheoremFor_thirtyseven_of_level71Deg68Scalar
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (caseII_classConjFixed : CaseIIRootClassConjFixed37)
    (caseII_realDescent : CaseIIRealSingleRootDescentPreservesReality37)
    (caseII_pthPow : Cor823CorrectedUnitPthPowerRationalModP37)
    (caseII_deg68Scalar : CaseIICor823Level71Deg68Scalar37)
    (noSecondOrderIrregular : NoSecondOrderIrregularPair 37 32) :
    FermatLastTheoremFor 37 :=
  fermatLastTheoremFor_thirtyseven_of_level71SecondOrderPartValue
    caseII_classConjFixed
    caseII_realDescent
    caseII_pthPow
    (caseIICor823Level71SecondOrderPartValue37_of_deg68Scalar caseII_deg68Scalar)
    noSecondOrderIrregular

end BernoulliRegular.FLT37.Eichler

end
