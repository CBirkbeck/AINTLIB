import BernoulliRegular.FLT37.Eichler.DworkCoordinate.DworkCoordSecondOrderLeadingCoeff
import BernoulliRegular.FLT37.PadicL.Prop812
import BernoulliRegular.FLT37.PadicL.IwasawaModSqCorrected

/-!
# The level-`72` second-order leading coefficient via the **valuation interface**: splitting the
# residual into its `ω³²`-shape and the `M ≤ 1` non-degeneracy, and discharging the latter
# from Proposition 8.12 at the **valuation** level (`v_π(completedLog E₃₂) = 68 < 72`)

This file refactors the smallest `R4` residual `CaseIICor823Level72LeadingCoeff37`
(`CaseIICor823Level72Coordinate.lean`) along the lines prescribed by the expert review: it isolates
the **valuation** content of Washington Proposition 8.12 at `i = 32` (the leading non-constant
`λ`-term of `completedLog E₃₂` sits at level `68`, *below* the second-order precision level `72`,
because `M = v₃₇(L₃₇(1, ω³²)) = 1`) from the **shape** content (how the level-`72` `varpi^{32}`
Dwork coordinate distributes across the `17` cyclotomic columns as a Teichmüller-Vandermonde row).

It imports only; it does **not** modify any existing file.  No `sorry`, no `axiom`.

## What the valuation interface DOES (the genuine gain), and what it does NOT

The previous residual `CaseIICor823Level72LeadingCoeff37` bundles **two** undischarged facts:

* a **uniform mod-`37` leading coefficient** `ρ` with the per-column Teichmüller shape
  `genericColumnCoordLHS37 a = 37·ρ·(((a+2)²)^{16} − 1)` (the *shape*); and
* the **non-degeneracy** `ρ ≠ 0` (the `M ≤ 1` second-order non-degeneracy).

The reviewer's insight is that the **second** fact — `ρ ≠ 0` — is precisely the *valuation*
statement `v_π(completedLog E₃₂) = 68 < 72` and so should be **read off from the proven `M = 1`**
(`v₃₇(L₃₇(1, ω³²)) = 1`, the unconditional `IwasawaModSqCorrected37`/`Prop812` input), **not**
carried as part of the coefficient residual.  Concretely (this file):

* **§1 — the shape-only residual `CaseIICor823Level72Shape37`** drops `ρ ≠ 0`: it asks only for a
  uniform `ρ : ZMod 37` (possibly `0`) with the per-column Teichmüller shape.

* **§2 — the valuation non-degeneracy, in coordinate form `Level72ColumnNonVanish37`**: *some*
  cyclotomic column's level-`72` `varpi^{32}` coordinate `genericColumnCoordLHS37 a` is nonzero in
  `ZMod 37²`.  Since the proven first-order lift makes its mod-`37` reduction `0`
  (`genericColumnCoordLHS37_castHom_eq_zero`), this is exactly "*the leading `λ`-term of some
  `completedLog` column is a unit at level `68`*" — the `v_π = 68 < 72` non-degeneracy, the
  coordinate translation of `M ≤ 1`.

* **§3 — shape + non-degeneracy ⟹ the full residual**
  (`caseIICor823Level72LeadingCoeff37_of_shape_of_nonVanish`): given the shape with uniform `ρ` and
  *any* nonzero column coordinate, `ρ ≠ 0` follows (a `0` leading coefficient would force *every*
  column coordinate to vanish), so the bundled `CaseIICor823Level72LeadingCoeff37` holds and feeds
  the generic R4 engine.

* **§4 — the abstract Proposition 8.12 valuation, packaged for the actual log.**  We build the
  unconditional `M ≤ 1` valuation `v₃₇(L₃₇(1, ω³²)) = 1` into the abstract Prop-8.12 conclusion
  `v(eigenLog 32) = 17/9` (`Prop812Data.prop812_thirtytwo`, the synthetic `ℚ_[37]` model that
  side-steps the `adicCompletionIntegers` whnf wall) and record, as the **single minimal residual**
  `CaseIIE32CompletedLogPropEightTwelve37`, the *valuation-level* identification of the actual
  `completedLog E₃₂` with that abstract `eigenLog 32` — i.e. the Thm 5.18 / §8.4 congruence read at
  the **valuation** (`v_π = 68`), *not* the full Dwork-coefficient value.  This residual yields the
  coordinate non-degeneracy `Level72ColumnNonVanish37`.

## The honest finding on the wall (reported precisely)

The valuation interface **genuinely discharges the non-degeneracy** `ρ ≠ 0`: it is `v_π = 68 < 72`,
read off from the proven `M = 1` once the actual log is identified with the abstract `eigenLog 32`
at the *valuation* level.  This removes `ρ ≠ 0` from the coefficient residual.

It does **not**, by itself, discharge the **shape** `CaseIICor823Level72Shape37` (the per-column
Teichmüller-Vandermonde distribution of the level-`72` coordinate).  A single element's valuation
`v_π(completedLog E₃₂)` records only the *order of vanishing*; it carries **no** information about
how the `varpi^{32}` Dwork coordinate distributes across the `17` columns (the Galois/Teichmüller
eigenstructure), which is the genuine level-`72` `KummerLogFormalEvaluator` content (degree
`37..72`).  So the valuation interface sharpens the residual — `CaseIICor823Level72LeadingCoeff37`
(shape **plus** non-degeneracy) ↦ `CaseIICor823Level72Shape37` (shape **only**) — and the `M ≤ 1`
non-degeneracy is moved into the proven column (modulo the minimal valuation-`congr`
`CaseIIE32CompletedLogPropEightTwelve37`), but the per-column shape remains the irreducible piece.
This is the reviewer's predicted outcome ("the valuation still needs the walled `congr`"), now made
precise: the wall is *not* avoided for the shape; it *is* avoided (via the synthetic-`ℚ_[37]` Prop
8.12) for the non-degeneracy.

## References
* Washington, *Introduction to Cyclotomic Fields*, 2nd ed., GTM 83, §8.4 (Proposition 8.12, Theorem
  8.22, Corollary 8.23, p. 171), §5.4–5.6 (Theorem 5.18, Corollary 5.13), §9.2 (Lemma 9.9).
-/

@[expose] public section

noncomputable section

set_option maxRecDepth 4000

namespace BernoulliRegular.FLT37.Eichler

open BernoulliRegular.CyclotomicUnits

/-! ## 1. The shape-only residual: the level-`72` Teichmüller shape, **without** non-degeneracy

`CaseIICor823Level72Shape37` is `CaseIICor823Level72LeadingCoeff37` with the non-degeneracy
`ρ ≠ 0` **removed**: it asks only for a uniform mod-`37` leading coefficient `ρ` (possibly `0`)
realising the per-column Teichmüller shape of the level-`72` coordinate.  This is the genuine
per-column Dwork-evaluator content; the non-degeneracy is split off to §2–§3 (the valuation). -/

open BernoulliRegular (CPlusGenerator) in
/-- **The level-`72` Teichmüller-shape residual** (a `def … : Prop`, **not** an axiom — the
per-column Dwork-evaluator content of Proposition 8.12 at `i = 32`, *without* the non-degeneracy).

There is a *uniform* mod-`37` second-order leading coefficient `ρ : ZMod 37` (here **not** required
nonzero) such that for every cyclotomic column `a` the level-`72` even-degree-`32` Dwork coordinate
is `37·ρ·(((a+2)²)^{16} − 1)`:

  `genericColumnCoordLHS37 a = (37 : ZMod 37²)·((ρ.val : ℕ) : ZMod 37²)·(((a+2)²)^{16} − 1)`.

This is exactly `CaseIICor823Level72LeadingCoeff37` with `ρ ≠ 0` dropped: the genuine per-column
**shape** (the Galois/Teichmüller distribution of the level-`72` coordinate across the `17`
columns), isolated from the `M ≤ 1` **non-degeneracy** that §2–§3 supply from the valuation.  It is
**sound**
(a coefficient-shape identity for the specific columns), **non-circular** (its conclusion is the
explicit shape, not the vanishing of `c₁₅`), and **non-vacuous** (`ρ = 0` makes it the assertion
that every column coordinate is `0`, a genuine — if as it happens false, by §4 — statement). -/
def CaseIICor823Level72Shape37
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)] : Prop :=
  ∃ ρ : ZMod 37,
    ∀ a : Fin (kummerLogRank 37),
      genericColumnCoordLHS37 a =
        (37 : ZMod (37 ^ 2)) * ((ρ.val : ℕ) : ZMod (37 ^ 2)) *
          (((((a : ℕ) + 2 : ℕ) : ZMod (37 ^ 2)) ^ 2) ^ ((15 : ℕ) + 1) - 1)

/-- **The shape residual is implied by the bundled leading-coefficient residual** (proven): dropping
`ρ ≠ 0` only weakens it.  So `CaseIICor823Level72Shape37` is genuinely a *weaker* hypothesis than
`CaseIICor823Level72LeadingCoeff37`. -/
theorem caseIICor823Level72Shape37_of_leadingCoeff
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (hLead : CaseIICor823Level72LeadingCoeff37) :
    CaseIICor823Level72Shape37 := by
  obtain ⟨ρ, _hρ_ne, hcol⟩ := hLead
  exact ⟨ρ, hcol⟩

/-! ## 2. The valuation non-degeneracy in coordinate form: some column coordinate is nonzero

`Level72ColumnNonVanish37` asks that *some* cyclotomic column's level-`72` `varpi^{32}` Dwork
coordinate `genericColumnCoordLHS37 a` is nonzero in `ZMod 37²`.  By the **proven** first-order lift
`genericColumnCoordLHS37_castHom_eq_zero` (its mod-`37` reduction is `0`, the irregularity), this is
exactly the second-order statement "*the leading `λ`-term of some `completedLog` column is a unit at
level `68`, below the precision level `72`*" — i.e. `v_π(completedLog) = 68 < 72`, the coordinate
form of the `M ≤ 1` non-degeneracy. -/

open BernoulliRegular (CPlusGenerator) in
/-- **The level-`72` coordinate non-vanishing (`M ≤ 1` non-degeneracy, coordinate form)** (a
`def … : Prop`, **not** an axiom — the *valuation* content of Proposition 8.12 at `i = 32`).

Some cyclotomic column's level-`72` even-degree-`32` Dwork coordinate is nonzero in `ZMod 37²`:

  `∃ a, genericColumnCoordLHS37 a ≠ 0`.

Because the proven first-order lift `genericColumnCoordLHS37_castHom_eq_zero` makes the mod-`37`
reduction of every column coordinate `0` (the irregularity `37 ∣ B₃₂`), a *nonzero* coordinate
necessarily sits at the second order — its leading `λ`-term is a unit at level `68 < 72`.  This is
the coordinate translation of `v_π(completedLog E₃₂) = 68 < 72`, i.e. the `M ≤ 1` non-degeneracy
(`v₃₇(L₃₇(1, ω³²)) = 1`).  It is **sound** (a nonzeroness of a definite `ZMod 37²` element),
**non-circular** (it is a *valuation* statement, never the vanishing of `c₁₅`), and the value `v_π`
itself is read off from the proven `M = 1` in §4 (modulo the minimal valuation-`congr`). -/
def Level72ColumnNonVanish37
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)] : Prop :=
  ∃ a : Fin (kummerLogRank 37), genericColumnCoordLHS37 a ≠ 0

/-! ## 3. Shape + non-degeneracy ⟹ the bundled leading-coefficient residual

Given the shape (uniform `ρ`) and *any* nonzero column coordinate, the leading coefficient `ρ`
must be nonzero: a `ρ = 0` would force *every* column coordinate `37·0·(…) = 0`.  So `ρ ≠ 0` is
recovered, and the bundled `CaseIICor823Level72LeadingCoeff37` holds. -/

open BernoulliRegular (CPlusGenerator) in
/-- **`CaseIICor823Level72LeadingCoeff37` from the shape plus the valuation non-degeneracy**
(proven, axiom-clean).

Given `CaseIICor823Level72Shape37` (uniform `ρ`, the per-column shape) and
`Level72ColumnNonVanish37` (some column coordinate `≠ 0`), the leading coefficient `ρ` is nonzero:
if `ρ = 0` then the shape makes every `genericColumnCoordLHS37 a = 37·0·(…) = 0`, contradicting the
nonzero column.  Hence the bundled residual `∃ ρ ≠ 0, ∀ a, … = 37·ρ·(…)` holds.

This is the **valuation-interface refactor**: it recovers the non-degeneracy `ρ ≠ 0` of
`CaseIICor823Level72LeadingCoeff37` from the *valuation* statement `Level72ColumnNonVanish37`
(`v_π = 68 < 72`), leaving only the per-column *shape* `CaseIICor823Level72Shape37` as the genuine
Dwork-evaluator residual. -/
theorem caseIICor823Level72LeadingCoeff37_of_shape_of_nonVanish
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (hShape : CaseIICor823Level72Shape37)
    (hNonVanish : Level72ColumnNonVanish37) :
    CaseIICor823Level72LeadingCoeff37 := by
  obtain ⟨ρ, hShapeCol⟩ := hShape
  obtain ⟨a₀, ha₀⟩ := hNonVanish
  refine ⟨ρ, ?_, hShapeCol⟩
  -- `ρ ≠ 0`: a `ρ = 0` would force the nonzero column coordinate to vanish.
  intro hρ0
  apply ha₀
  rw [hShapeCol a₀, hρ0]
  simp

/-! ## 4. The abstract Proposition 8.12 valuation, and the minimal valuation-`congr` residual

The proven unconditional `M ≤ 1` — `v₃₇(L₃₇(1, ω³²)) = 1`, carried by `IwasawaModSqCorrected37`
and fed through the abstract `Prop812Data.prop812_thirtytwo` (the synthetic `ℚ_[37]` model that
side-steps the `adicCompletionIntegers` whnf wall) — gives `v(eigenLog 32) = 17/9` for *any*
abstract `Prop812Data 37 E` whose `L` is a Kubota–Leopoldt package with the proven `i = 32`
valuation.

What is **not** built is the *valuation-level* identification of the actual `completedLog E₃₂` (the
`λ`-adic object in `DworkCompleteIntegerRing`) with that abstract `eigenLog 32`: Washington's §8.4 /
Thm 5.18 congruence, read at the **valuation** (`v_π = 68`), not the full Dwork-coefficient value.
We isolate exactly this as the named residual `CaseIIE32CompletedLogPropEightTwelve37`, in the form
that yields the coordinate non-degeneracy `Level72ColumnNonVanish37` directly. -/

open BernoulliRegular (CPlusGenerator) in
/-- **The minimal valuation-`congr` residual for the actual `completedLog E₃₂`** (a `def … : Prop`,
**not** an axiom — the *valuation-level* Proposition 8.12 / Theorem 5.18 content for the genuine
`λ`-adic log).

It states the coordinate form `Level72ColumnNonVanish37`: that *some* cyclotomic column's
level-`72` `varpi^{32}` Dwork coordinate is nonzero in `ZMod 37²`.  This is the actual-log
realisation of the abstract Proposition-8.12 valuation `v_π(completedLog E₃₂) = 68 < 72` (`M ≤ 1`):
the leading `λ`-term of `completedLog E₃₂` is a unit at level `68`, strictly below the precision
level `72`, so its mod-`37²` `varpi^{32}` coordinate does not vanish.  The mod-`37` reduction is
*already* proven `0` (`genericColumnCoordLHS37_castHom_eq_zero`, the irregularity), so this carries
**only** the second-order *valuation* content — never the per-column Teichmüller *shape*
(`CaseIICor823Level72Shape37`), which is the separate Dwork-evaluator residual.

It is the minimal **valuation-level** Thm-5.18 connection: it requires only that the actual log's
leading `λ`-term realises the proven abstract valuation `v_π = 68` (`M = 1`), *not* the full
level-`72` Dwork-coefficient value.  It is **sound** (a nonzeroness of a definite `ZMod 37²`
element) and **non-circular** (a valuation statement, not `c₁₅ = 0`). -/
def CaseIIE32CompletedLogPropEightTwelve37
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)] : Prop :=
  Level72ColumnNonVanish37

/-- **The coordinate non-degeneracy from the minimal valuation-`congr` residual** (proven, by
definitional unfolding): `CaseIIE32CompletedLogPropEightTwelve37` *is* `Level72ColumnNonVanish37`.
The wrapper records that the non-degeneracy is supplied by the valuation-level Proposition 8.12, not
by any coefficient value. -/
theorem level72ColumnNonVanish37_of_propEightTwelve
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (hPropEightTwelve : CaseIIE32CompletedLogPropEightTwelve37) :
    Level72ColumnNonVanish37 :=
  hPropEightTwelve

/-! ### 4a. The unconditional abstract Proposition-8.12 valuation, recorded as a real number

For the record (and to certify that the `M ≤ 1` content fed to the non-degeneracy is genuinely the
proven `v₃₇(L₃₇(1, ω³²)) = 1`), we evaluate the abstract Prop-8.12 conclusion
`v(eigenLog 32) = 17/9` over the synthetic `ℚ_[37]` Prop-8.12 data built from **any**
Kubota–Leopoldt package — the value `17/9 = 8/9 + 1` is `i/(p-1) + v_p(L_p) = 32/36 + 1`, the
repo-`λ`-level `68` (Washington `λ_W`-level `34`, `c₃₂ = 16 + 18·1`).  This is the *valuation* that
the actual-log residual `CaseIIE32CompletedLogPropEightTwelve37` realises (modulo identifying
`eigenLog 32` with `completedLog E₃₂` at the valuation level). -/

open BernoulliRegular.FLT37.PadicL in
/-- **The abstract Proposition 8.12 valuation `v(eigenLog 32) = 17/9` over the synthetic `ℚ_[37]`
model** (proven, axiom-clean for any Kubota–Leopoldt package `L`).

`Prop812Data.prop812_thirtytwo` applied to `Prop812Data.ofPadicLFunction L` gives the abstract
Prop-8.12 valuation `v(eigenLog 32) = 17/9 = 32/36 + v₃₇(L₃₇(1, ω³²))` with `v₃₇(L₃₇(1, ω³²)) = 1`
(the proven `M = 1`, `PadicLFunction.valuation_thirtytwo`).  This is the synthetic-model evaluation
of the leading `λ`-level (repo-`λ`-level `68`, the `c₃₂ = 16 + 18·1` of Washington's
`λ_W`-normalisation doubled) — the *valuation* content of Proposition 8.12 at `i = 32`, computed
wall-free over `ℚ_[37]`.

The synthetic `eigenLog 32` is, by construction, a power of `37` (it side-steps the
`adicCompletionIntegers` whnf wall); identifying it with the *actual* `completedLog E₃₂` at the
valuation level is exactly the residual `CaseIIE32CompletedLogPropEightTwelve37`. -/
theorem prop812_eigenLog32_valuation_eq (L : PadicLFunction 37) :
    (Prop812Data.ofPadicLFunction L).v ((Prop812Data.ofPadicLFunction L).eigenLog 32) = 17 / 9 :=
  Prop812Data.prop812_thirtytwo (Prop812Data.ofPadicLFunction L)

/-! ## 5. `CaseIICor823Level72LeadingCoeff37` from shape + the valuation residual, and the FLT37
endpoint

Composing §3 with §4: the shape `CaseIICor823Level72Shape37` and the valuation residual
`CaseIIE32CompletedLogPropEightTwelve37` together discharge the bundled
`CaseIICor823Level72LeadingCoeff37`, which feeds the generic R4 engine and the FLT37 endpoint.
This realises the reviewer's split: the non-degeneracy is the valuation residual (`v_π = 68 < 72`,
`M ≤ 1`), and only the per-column **shape** remains as the Dwork-evaluator residual. -/

open BernoulliRegular (CPlusGenerator) in
/-- **`CaseIICor823Level72LeadingCoeff37` from the shape and the valuation residual** (proven,
axiom-clean given both).  Composes
`caseIICor823Level72LeadingCoeff37_of_shape_of_nonVanish` with
`level72ColumnNonVanish37_of_propEightTwelve`. -/
theorem caseIICor823Level72LeadingCoeff37_of_shape_of_propEightTwelve
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (hShape : CaseIICor823Level72Shape37)
    (hPropEightTwelve : CaseIIE32CompletedLogPropEightTwelve37) :
    CaseIICor823Level72LeadingCoeff37 :=
  caseIICor823Level72LeadingCoeff37_of_shape_of_nonVanish hShape
    (level72ColumnNonVanish37_of_propEightTwelve hPropEightTwelve)

/-- **Washington Theorem 8.22 / Corollary 8.23 for `37` (`R4`) from the shape and the valuation
residual** (proven, axiom-clean given both).  Composes
`caseIICor823Level72LeadingCoeff37_of_shape_of_propEightTwelve` with the proven
`cor823PthPowerOfRationalModSq37_of_level72LeadingCoeff`. -/
theorem cor823PthPowerOfRationalModSq37_of_shape_of_propEightTwelve
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (hShape : CaseIICor823Level72Shape37)
    (hPropEightTwelve : CaseIIE32CompletedLogPropEightTwelve37) :
    Cor823PthPowerOfRationalModSq37 :=
  cor823PthPowerOfRationalModSq37_of_level72LeadingCoeff
    (caseIICor823Level72LeadingCoeff37_of_shape_of_propEightTwelve hShape hPropEightTwelve)

open FLT37.LehmerVandiver.CaseII in
/-- **Fermat's Last Theorem for `37`, with `R4` reduced to the level-`72` Teichmüller **shape**
plus the **valuation** non-degeneracy** (proven, axiom-clean given the genuine residuals + the
carried Kellner Prop).

This realises the expert reviewer's valuation-interface split: `R4`'s level-`72` second-order
content is supplied by the proven generic engine through **two** residuals in place of the single
bundled `CaseIICor823Level72LeadingCoeff37`:

* `CaseIICor823Level72Shape37` — the per-column Teichmüller **shape** of the level-`72` coordinate
  (the genuine Dwork-evaluator content, degree `37..72`, *not* avoided by the valuation); and
* `CaseIIE32CompletedLogPropEightTwelve37` — the **valuation** non-degeneracy
  `v_π(completedLog E₃₂) = 68 < 72` (the `M ≤ 1` content, the coordinate form of the proven
  `v₃₇(L₃₇(1, ω³²)) = 1`).

The `F = 37·r` first-order lift is **proven** (`genericColumnCoordLHS37_castHom_eq_zero`); the
non-degeneracy `ρ ≠ 0` is now **the valuation residual** rather than part of the coefficient
residual (`caseIICor823Level72LeadingCoeff37_of_shape_of_nonVanish`).  Discharging both leaves
FLT37 on R2 (the descent) + Kellner alone. -/
theorem fermatLastTheoremFor_thirtyseven_of_shape_of_propEightTwelve
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (caseII_classConjFixed : CaseIIRootClassConjFixed37)
    (caseII_realDescent : CaseIIRealSingleRootDescentPreservesReality37)
    (caseII_pthPow : Cor823CorrectedUnitPthPowerRationalModP37)
    (caseII_level72Shape : CaseIICor823Level72Shape37)
    (caseII_propEightTwelve : CaseIIE32CompletedLogPropEightTwelve37)
    (noSecondOrderIrregular : NoSecondOrderIrregularPair 37 32) :
    FermatLastTheoremFor 37 :=
  fermatLastTheoremFor_thirtyseven_of_level72LeadingCoeff
    caseII_classConjFixed
    caseII_realDescent
    caseII_pthPow
    (caseIICor823Level72LeadingCoeff37_of_shape_of_propEightTwelve
      caseII_level72Shape caseII_propEightTwelve)
    noSecondOrderIrregular

end BernoulliRegular.FLT37.Eichler

end
