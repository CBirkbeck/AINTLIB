# `/mathlibable` report — `PadicLFunctions.integerRing.isUnit_of_norm_eq_one`

**Final five-bucket verdict: `NO-mathlib-has-it`**

Mathlib already has this fact, as the iff `Valued.integer.isUnit_iff_norm_eq_one`
(`Mathlib/Topology/Algebra/Valued/LocallyCompact.lean:60`); the target theorem is
the `.mpr` direction of it, stated against the project's own `integerRing L`
subring instead of mathlib's `𝒪[L]` (same carrier, defeq as sets, different
bundling).

---

### Baseline (Phase 0)

- lake build:               build not re-run; reasoned from source (per task note — `lake build` stale/slow here; Phase-0 fallback used)
- decl `PadicLFunctions.integerRing.isUnit_of_norm_eq_one`: ✓ resolved at `projects/PadicLFunctions/PadicLFunctions/Coefficients.lean:130`
- kind:                      theorem
- has sorry:                 no
- module docstring summary:  Coefficient rings for §5 — the integer ring (norm-unit ball) `integerRing L` of a nonarchimedean complete normed `ℚ_[p]`-algebra `L`, and root-of-unity norm facts (W1–W3).

---

### Statement (Phase 1)

`PadicLFunctions.integerRing.isUnit_of_norm_eq_one` is a theorem stating the following:

Let `L` be a nonarchimedean (ultrametric) normed field and let `𝒪 = {x ∈ L : ‖x‖ ≤ 1}`
be its ring of integers (the closed unit ball, a subring because the norm is
ultrametric and multiplicative). Then any `x ∈ 𝒪` with `‖x‖ = 1` is a unit of `𝒪`.
The witness is the field inverse `x⁻¹`: since `‖x⁻¹‖ = ‖x‖⁻¹ = 1 ≤ 1`, `x⁻¹` lies in
`𝒪`, and `x · x⁻¹ = 1`. This is the "hard" (mpr) half of the standard
characterisation `𝒪ˣ = {x : ‖x‖ = 1}`.

Variables / typeclasses involved (Lean side, after the `omit`):
- `L : Type*` with `[NormedField L]` — the ambient nonarchimedean field.
- `[IsUltrametricDist L]` — ultrametric (strong triangle) inequality; makes the unit ball a subring.
- (The surrounding section also fixes `p`, `[Fact p.Prime]`, `[NormedAlgebra ℚ_[p] L]`, `[CompleteSpace L]`, but this theorem `omit`s `[NormedAlgebra ℚ_[p] L]` and `[CompleteSpace L]`, so it uses only `[NormedField L] [IsUltrametricDist L]`.)
- `x : integerRing L` — an element of the unit-ball subring (a `Subtype` of `L`).

Hypotheses (Lean side):
- `hx : ‖(x : L)‖ = 1` — the coerced element has norm exactly one.

Conclusion (math): `x` is invertible in the ring of integers `𝒪`.

Conclusion (Lean): `IsUnit x` (where `x : integerRing L`).

---

### Size classification (Phase 2a)

Verdict: SMALL
Reason: a one-direction helper lemma about a project-defined subring; not a named theorem, not a new structure, not a `## Main results` headline (the file's headline declarations are `integerRing`, `IsPrimitiveRoot.norm_sub_one_lt`, `IsPrimitiveRoot.norm_pow_sub_one_eq_one`). It is the standard "norm-1 ⟹ unit" half of `𝒪ˣ = {‖·‖ = 1}`.

(Literature width is EXHAUSTIVE regardless. BIG/SMALL is recorded for framing only.)

### One-line check (Phase 2b)

Body line count: 4 substantive lines (`have hx0 …`, `refine IsUnit.of_mul_eq_one …`, the inverse witness, `exact Subtype.ext …`).
One-liner verdict: n/a — kind is `theorem`, not `def`/`abbrev`/`structure`. The 2b exemption table does not apply.

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                                  | Hit? | Standard form found                                          | Notes |
|----|----------------------------------|--------------------------------------------------------------------------------------------------------|------|--------------------------------------------------------------|-------|
|  1 | WebSearch (specific form)        | "element of valuation ring is a unit iff its norm equals one nonarchimedean field"                     | yes  | `x ∈ 𝒪` is a unit `⇔ |x| = 1`                              | MIT 18.785 Lec 1 & 8; Berkovich/perfectoid notes (arXiv 2304.09266): "|x|=1 ⇔ x ∈ 𝒪ˣ" |
|  2 | WebSearch (general form)         | "ring of integers nonarchimedean field unit iff norm one valuation ring"                               | yes  | `𝒪ˣ = {x ∈ K : |x| = 1}`; units are valuation-0 elements   | Wikipedia "Valuation ring"; the general statement is for any valuation ring `{v ≥ 0}` |
|  3 | WebSearch (named-after / aliases)| `"unit" "norm 1" p-adic integers Z_p invertible iff norm one local field`                              | yes  | `ℤ_pˣ = {x : |x|_p = 1}` (the special case)                | ProofWiki "P-adic Unit has Norm Equal to One"; Encyclopedia of Math "p-adic number"; W&M local-fields notes |
|  4 | ChatGPT MCP                      | (intended: "standard form + generality + historical evolution of 𝒪ˣ = {‖·‖=1}")                       | n/a  | —                                                            | ChatGPT MCP not configured in this environment (no `mcp__…chatgpt…ask` tool resolvable via ToolSearch). Recorded n/a; the four web/reference/nLab/Stacks channels below cover the standard-form question redundantly. |
|  5 | Local references                 | grep `.mathlib-quality/references/` and `refs/PadicLFunctions/`                                          | n/a  | (no references dir)                                          | Neither `projects/PadicLFunctions/.mathlib-quality/references/` nor `refs/` exists — recorded n/a. (Project TeX refs are PDF-only / local; not present here.) |
|  6 | nLab                             | "valuation ring units norm absolute value equal one nonarchimedean"                                     | yes  | `R× = {x : |x| = 1}`; `Â = {v ≥ 0} = {|·|_v ≤ 1}`           | nLab "valuation"; Climbing-Mount-Bourbaki (Akhil Mathew) "DVRs and absolute values" |
|  7 | nCatLab (if categorical)         | —                                                                                                       | n/a  | not a categorical concept                                   | The statement is an elementary fact about a 1-ring; no (higher-)categorical content. |
|  8 | Stacks Project (if alg geom)     | "valuation ring local ring unit maximal ideal valuation"                                                | yes  | valuation ring is local; non-units = `{v > 0}` = `𝔪`        | Stacks 07BH (local rings), 00P7/034X (valuation rings). Units are exactly `{v = 0}` = norm 1. |
|  9 | MathOverflow / Math.StackExchange| (covered by #1–#3, #6 hits)                                                                              | yes  | same: `𝒪ˣ = {|·| = 1}`                                       | The fact is folklore-standard; the textbook/nLab/Stacks hits already pin the canonical form, so no extra MO query was needed. |
| 10 | recent arXiv (last 5 years)      | (surfaced under #1/#2) "Berkovich approach to perfectoid spaces" (2304.09266)                            | yes  | restates `|x| = 1 ⇔ x ∈ K≤1ˣ` as a basic fact              | Confirms the form is still the working definition in contemporary nonarchimedean-geometry papers; no newer/more-general variant exists — the statement is structurally maximal already. |

Protocol pass check:
- WebSearch ran 3 distinct queries at three generality levels (specific 𝒪; general valuation ring `𝒪ˣ = {|·|=1}`; the ℤ_p special case + aliases). ✓
- ChatGPT MCP: n/a (tool not configured) — recorded with reason; redundantly covered by #1, #2, #6, #8. 
- Local references checked (absent → n/a with reason). ✓
- nLab checked. ✓
- Stacks / nCatLab / MathOverflow / arXiv each checked or n/a-with-reason. ✓

### Literature summary (Phase 3)

Concept identified as: **the unit group of the ring of integers (valuation ring) of a nonarchimedean field equals the elements of norm one** — `𝒪ˣ = {x : ‖x‖ = 1}`. The target is the forward "norm 1 ⟹ unit" half.
Sources agree on the standard form: **yes**. Every source (MIT 18.785, Wikipedia, nLab, Stacks, ProofWiki, Encyclopedia of Math, perfectoid-geometry arXiv) states the same characterisation.
Most general standard form: for **any** valuation `v : K → Γ₀` on a field with integers `𝒪 = {v ≤ 1}`, an element is a unit of `𝒪` iff `v(x) = 1` (equivalently norm 1 in the rank-one / real-valued case). The norm phrasing is the rank-one specialisation; the valuation phrasing is the fully general one.
Generality dimensions where the literature varies:
  - value group: real norm `‖·‖ : K → ℝ≥0` (rank one) **vs** arbitrary `Γ₀ : LinearOrderedCommGroupWithZero`. The most general is the latter (mathlib's `Valuation.Integers.isUnit_iff_valuation_eq_one`).
  - field hypothesis: "field with absolute value" / "complete nonarchimedean field" in texts; mathlib's general lemma needs only `[Ring R] [LinearOrderedCommGroupWithZero Γ₀]` plus an `Integers v O` witness — no completeness, no nontriviality.
Disagreement with the literature: **none**. The target is exactly the standard statement (specialised to a real norm and to one direction of the iff).

---

### Generality analysis — `PadicLFunctions.integerRing.isUnit_of_norm_eq_one`

Literature-standard form (from Phase 3): for a valuation `v` on a field with integers `𝒪`, `x ∈ 𝒪ˣ ⇔ v(x) = 1`. Real-norm specialisation: `x ∈ 𝒪ˣ ⇔ ‖x‖ = 1`.

| # | Parameter / hypothesis        | Current Lean form                | Literature-standard form                  | Weaker form exists? | Reason it can/can't be weakened |
|---|-------------------------------|----------------------------------|--------------------------------------------|---------------------|----------------------------------|
| 1 | `[NormedField L]`             | normed field (real-valued norm)  | field with any `Γ₀`-valuation              | yes (valuation)     | The whole statement generalises to `Valuation.Integers v O` over `LinearOrderedCommGroupWithZero Γ₀` — mathlib's `Valuation.Integers.isUnit_iff_valuation_eq_one`. The real-norm version is the rank-one case. |
| 2 | `[IsUltrametricDist L]`       | ultrametric (strong triangle)    | used only to make `𝒪` a subring            | n/a here            | Needed so `{‖·‖ ≤ 1}` is closed under `+` and hence a ring; not used in this lemma's proof beyond the ambient subring already existing. The valuation-level statement bakes this in via `Valuation`. |
| 3 | `{x : integerRing L}`         | project's bespoke unit-ball Subring | `𝒪[L] = (NormedField.valuation L).integer` (mathlib) | yes (re-aim)        | `integerRing L` and `𝒪[L]` have the **same carrier** `{x : ‖x‖ ≤ 1}` (defeq as sets — both via `IsUltrametricDist.norm_add_le_max` for additive closure), but are distinct `Subring` terms. Stating against `𝒪[L]` is the mathlib-idiomatic target. |
| 4 | (conclusion) one direction    | `‖x‖ = 1 → IsUnit x` (mpr only)  | the full iff `IsUnit x ↔ ‖x‖ = 1`          | —                   | Mathlib states the iff; this is strictly weaker (one half). The companion `not_isUnit_of_norm_lt_one` (line 120) supplies a related converse-ish fact. |

### Generality verdict (Phase 4b)

The current form is: STRICTLY NARROWER THAN STANDARD (on two axes: real-norm vs valuation; and one-direction vs iff), **but this does not change the bucket** — see Phase 5, which finds mathlib *already has* the more general iff (`Valued.integer.isUnit_iff_norm_eq_one`) and the maximally-general valuation form (`Valuation.Integers.isUnit_iff_valuation_eq_one`). When mathlib already has the general form, the verdict is `NO-mathlib-has-it`, not `YES-but-generalise-first`.
Number of weakening opportunities found: 2 (valuation-level value group; iff vs one-direction) — both already realised in mathlib.
Proposed restatement: n/a for upstreaming (mathlib has it); the project-internal fix is to re-aim onto `𝒪[L]` — see Phase 7 refactor plan.
Cost of restatement: n/a (no new mathlib lemma needed).

Note on the apparent extra generality (`NormedField` vs mathlib's `NontriviallyNormedField`): the target uses `[NormedField L]`, while `Valued.integer.isUnit_iff_norm_eq_one` is stated under `[NontriviallyNormedField K]`. This is **not** a genuine generalisation worth shipping:
- A `NormedField` that is *not* nontrivially-normed carries the trivial discrete norm (`‖x‖ = 1` for all `x ≠ 0`); then `integerRing L = L`, every nonzero element is a unit (it's a field), and the statement is vacuously trivial — no mathematical content in the gap.
- The mathlib lemma's `NontriviallyNormedField` is **inherited from its file section variable** (it powers the locally-compact theorems in the same file), not used by this iff: the proof goes through `(Valuation.integer.integers (NormedField.valuation)).isUnit_iff_valuation_eq_one`, whose own hypotheses are only `[Ring R] [LinearOrderedCommGroupWithZero Γ₀]`. So mathlib *could* relax the wrapper to `[NormedField K]` trivially; the content is identical. The right action for the `NormedField`-vs-`NontriviallyNormedField` hairline is a one-line `/generalise` on the *mathlib* lemma, not a new project lemma — out of scope for this decl.

### Modern-idiom check (Phase 4c)

| #  | Question                                                                                          | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|---------------------------------------------------------------------------------------------------|----------|------------------------|----------------------------------|
|  1 | "let `L` be a normed field" preamble → typeclasses?                                                | no       | already a typeclass     | already idiomatic |
|  2 | sequences/metric → filters/topological?                                                            | no       | —                      | no limit/convergence content |
|  3 | construct an object where a universal property would characterise it?                             | no       | —                      | this is a property, not a construction |
|  4 | set-with-closure-predicate → bundled substructure?                                                | **yes (already exists in mathlib)** | `𝒪[L] = (NormedField.valuation L).integer` — mathlib's bundled `Valued.integer` subring | the entire `Valuation.Integers` API: `isUnit_iff_valuation_eq_one`, `valuation_irreducible_lt_one`, DVR/residue-field machinery, `Mathlib/Topology/Algebra/Valued/LocallyCompact.lean` |
|  5 | vector-space/metric/field-specific → weaken to module/(semi)ring/valuation?                       | **yes (already exists in mathlib)** | `Valuation.Integers.isUnit_iff_valuation_eq_one` over `LinearOrderedCommGroupWithZero Γ₀` | the full valuation-theory stack, independent of rank-one/real norm |
|  6 | 1-categorical → higher-categorical?                                                                | no       | —                      | n/a |
|  7 | concrete index (ℕ/ℤ/ℝ) → arbitrary monoid/group?                                                  | no       | the "index" here is the value group, covered by row 5 | n/a |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **yes — but it is already in mathlib**, which is precisely why the verdict is `NO-mathlib-has-it` rather than `YES-but-generalise-first`. The mathlib-idiomatic form is `Valued.integer.isUnit_iff_norm_eq_one` for `𝒪[L]` (rank-one) and `Valuation.Integers.isUnit_iff_valuation_eq_one` (fully general). The project's `‖x‖ = 1 → IsUnit x` against `integerRing L` is the older "set-with-predicate subring + one direction" formulation of a fact mathlib already carries in its bundled, fully-general form. No real downstream improvement is *added* by re-shipping it — the improvement is to *consume* the existing mathlib lemma.

---

### Diamond / defeq risk — `PadicLFunctions.integerRing.isUnit_of_norm_eq_one`

n/a — declaration kind is `theorem` (no definitional equalities or typeclass-search paths introduced). Phase 4.5 skipped.

---

### Mathlib search-status: `PadicLFunctions.integerRing.isUnit_of_norm_eq_one`

[A] Lean-Finder       (NL: "element of valuation ring unit iff norm one")   n/a: Lean-Finder MCP not configured; substituted by [C]/[D]/[E] + the doc-site fetch below
[B] Loogle            `IsUnit _ ↔ ‖_‖ = 1`, `‖_‖ = 1 → IsUnit _`             Loogle MCP not configured; substituted by name-pattern grep [E] over mathlib source (exhaustive on the symbol)
[C] LeanSearch        (NL: "unit ball valuation ring norm one is a unit")    n/a (MCP not configured); the WebSearch doc hits + doc-site fetch cover the NL angle
[D] Grep mathlib src  `isUnit.*norm.*one`, `norm.*one.*isUnit`, `unitBall`, `valuationSubring`, `Valued.integer` | **HIT**: `Valued.integer.isUnit_iff_norm_eq_one` (`Mathlib/Topology/Algebra/Valued/LocallyCompact.lean:60`); `Valuation.Integers.isUnit_iff_valuation_eq_one` (`Mathlib/RingTheory/Valuation/Integers.lean:160`); `Valuation.Integers.isUnit_of_one'` (`:156`)
[E] Name pattern      grep `(lemma|theorem) .*(isUnit|IsUnit).*(norm|Norm)` over all `Mathlib/` | **HIT**: same `isUnit_iff_norm_eq_one`; plus the maximal-ideal/DVR neighbours in the same namespace

Doc-site confirmation (WebFetch of mathlib4_docs): `Valued.integer.isUnit_iff_norm_eq_one {K} [NontriviallyNormedField K] [IsUltrametricDist K] {u : ↥(integer K)} : IsUnit u ↔ ‖u‖ = 1`. Same-namespace companions: `norm_unit`, `norm_coe_unit`, `mem_iff` (`x ∈ 𝒪[K] ↔ ‖x‖ ≤ 1`).

Searched for both:
- the user's current form (`‖x‖ = 1 → IsUnit x` on a unit-ball subring) — covered by [D]/[E];
- the literature-standard / more general forms (the iff on `𝒪[K]`; the valuation-level iff over `Γ₀`) — both found.

Concluded: **found in mathlib as `Valued.integer.isUnit_iff_norm_eq_one` (the iff); the target is its `.mpr` direction.** The maximally-general valuation form is also present as `Valuation.Integers.isUnit_iff_valuation_eq_one` / `isUnit_of_one'`. The only mismatch is the *subring object*: the target is stated for the project's `integerRing L`, mathlib's lemma for `𝒪[L] = (NormedField.valuation L).integer` — same carrier `{‖·‖ ≤ 1}` (defeq sets via the identical `IsUltrametricDist.norm_add_le_max` closure proof), distinct `Subring` terms.

---

### Call sites — `PadicLFunctions.integerRing.isUnit_of_norm_eq_one`

Internal use count: **3** (within the project, excluding the declaring file `Coefficients.lean`).
External-to-file callers: **1 distinct file** (`Interpolation/NonTame.lean`).

| Caller file:line                                   | Usage pattern (one-line excerpt) |
|----------------------------------------------------|-----------------------------------|
| `Interpolation/NonTame.lean:47`  | `refine integerRing.isUnit_of_norm_eq_one ?_` (constant coeff `ζ^c − 1` of `C(ζ^c)·(1+X) − 1`) |
| `Interpolation/NonTame.lean:62`  | `refine integerRing.isUnit_of_norm_eq_one ?_` (Gauss sum `G(η⁻¹)` is a unit) |
| `Interpolation/NonTame.lean:115` | `refine integerRing.isUnit_of_norm_eq_one ?_` (constant coeff `ζ^c·w − 1` is a unit) |

Inline-derivation grep (was the equivalent re-derived elsewhere without using the lemma?): **(none)** — all three "norm-1 ⟹ unit of `integerRing`" needs route through this lemma; no site re-proves it by hand, and no site uses the mathlib `𝒪[L]` lemma (consistent with the project using its own `integerRing`).

Call-sites signal: **K = 3 internal uses, no inline re-derivation.** Per the signal table this would normally read as "real API; lean YES" — *but* Phase 5 shows the content is a mathlib duplicate, so the K = 3 instead measures how many sites would consume the mathlib lemma after the `integerRing → 𝒪[L]` re-aim. It confirms the lemma is *used* (not dead code), not that it is *novel*.

---

### Composition check (Phase 6)

Can `PadicLFunctions.integerRing.isUnit_of_norm_eq_one` be derived from mathlib in ≤3 chained calls?

Attempt 1 (against mathlib's `𝒪[L]`, i.e. after the re-aim): `Valued.integer.isUnit_iff_norm_eq_one.mpr hx`
  - Mathlib decls used: `Valued.integer.isUnit_iff_norm_eq_one` (`.mpr`).
  - Result: **succeeds** — 1 call. (Needs `x : 𝒪[L]` and `[NontriviallyNormedField L]`; in the project's actual setting `L` is a `NormedAlgebra ℚ_[p] L`, which is nontrivially normed since `‖(p:L)‖ < 1`, so the typeclass is available. For the degenerate trivial-norm case the gap is mathematically empty, as noted in Phase 4b.)

Attempt 2 (against the maximally-general valuation form): `(Valuation.integer.integers (NormedField.valuation (K := L))).isUnit_of_one' (by simpa using hx)`
  - Mathlib decls used: `Valuation.integer.integers`, `Valuation.Integers.isUnit_of_one'`.
  - Result: **succeeds** — 1–2 calls.

Attempt 3 (keeping the project's *own* `integerRing L`, no re-aim): the project would need a bridge `Valuation.Integers (NormedField.valuation L) (integerRing L)` (injective subtype map + range `= {v ≤ 1}`) before applying `isUnit_of_one'`.
  - Result: **partial** — establishing the `Integers` witness for the bespoke subring is itself a few lines (it is essentially "`integerRing L` is *the* integers of `NormedField.valuation`"). This is the friction created purely by the project rolling its own subring rather than using `𝒪[L]`.

Conclusion: **COMPOSABLE / NO-mathlib-has-it.** The cleanest reading is `NO-mathlib-has-it` (mathlib has the iff; this is the `.mpr` half) — the derivation is a single `.mpr` call once the object is `𝒪[L]`. The only reason it is not a *zero-friction* drop-in today is the `integerRing L` vs `𝒪[L]` object mismatch, which is the structural decision already flagged at the `integerRing` *def* level (see the sibling report `PadicLFunctions.integerRing.md`, verdict `BORDERLINE-needs-human`).

---

## Verdict: `PadicLFunctions.integerRing.isUnit_of_norm_eq_one`

**Category:** `NO-mathlib-has-it`

**Evidence:**
- Literature search (Phase 3): `𝒪ˣ = {x : ‖x‖ = 1}` is textbook-standard (MIT 18.785, Wikipedia, nLab, Stacks 07BH, ProofWiki, Encyclopedia of Math, perfectoid arXiv). The target is the "norm 1 ⟹ unit" half.
- Generality analysis (Phase 4): STRICTLY NARROWER than the standard (real-norm + one direction), and mathlib already carries the more general iff — so the gate routes to NO, not YES-but-generalise. The `NormedField` vs `NontriviallyNormedField` hairline is a content-free degenerate gap, not a shippable generalisation.
- Mathlib search (Phase 5): **found in mathlib as `Valued.integer.isUnit_iff_norm_eq_one`** (the iff), with the maximally-general `Valuation.Integers.isUnit_iff_valuation_eq_one` / `isUnit_of_one'` underneath.
- Composition check (Phase 6): COMPOSABLE — `Valued.integer.isUnit_iff_norm_eq_one.mpr hx`, a single `.mpr` once the object is `𝒪[L]`.

**Rationale (1–2 paragraphs):**

The mathematical content of this theorem — an element of the ring of integers of a
nonarchimedean field is a unit iff its norm is one — is one of the most standard facts
in the subject (every channel in Phase 3 states it verbatim) and is already in mathlib,
*as an iff*, at `Valued.integer.isUnit_iff_norm_eq_one` (`Mathlib/Topology/Algebra/Valued/LocallyCompact.lean:60`),
with the fully general value-group version `Valuation.Integers.isUnit_iff_valuation_eq_one`
(`Mathlib/RingTheory/Valuation/Integers.lean:160`) beneath it. The target theorem is
literally the `.mpr` direction of that iff. It exists separately in the project only
because the project defines its own unit-ball subring `integerRing L` instead of using
mathlib's `𝒪[L] = (NormedField.valuation L).integer` — and those two `Subring`s have the
**same carrier** `{x : ‖x‖ ≤ 1}` (defeq as sets; both prove additive closure with the
identical `IsUltrametricDist.norm_add_le_max` lemma), differing only as bundled terms.

This is therefore a duplication of an existing mathlib lemma, not a contribution. The
verdict on *this declaration's* mathlib-worthiness is unambiguous (`NO-mathlib-has-it`):
mathlib has it, the derivation is one `.mpr` call. The genuinely open question — whether
to re-aim the project's `integerRing` onto `𝒪[L]` (which would make this lemma a one-line
alias to delete) — is a *structural* decision about the `integerRing` **definition**, and
is already surfaced as `BORDERLINE-needs-human` in the sibling report
`PadicLFunctions.integerRing.md`. It is not a question about *this* theorem's content, so
it does not make *this* verdict BORDERLINE. (Cost of the 606-usage re-aim is, per the skill,
never a verdict factor outside BORDERLINE — and the BORDERLINE call lives at the def, not here.)

**WHY not (refactor-actionable detail):**
Mathlib already has the result. The exact decl is `Valued.integer.isUnit_iff_norm_eq_one`,
the iff `IsUnit u ↔ ‖u‖ = 1` for `u : 𝒪[K]` under `[NontriviallyNormedField K] [IsUltrametricDist K]`;
the target is its `.mpr`. The maximally general form is `Valuation.Integers.isUnit_iff_valuation_eq_one`
(any field valuation over `LinearOrderedCommGroupWithZero`). The detail needed to plan the
refactor: `integerRing L` is set-equal to `𝒪[L]` (carrier `{‖·‖ ≤ 1}`), so once consumers
work with `𝒪[L]` the target follows in one line.

Existing mathlib decl:        `Valued.integer.isUnit_iff_norm_eq_one`
Located at:                   `Mathlib/Topology/Algebra/Valued/LocallyCompact.lean:60`
(general form: `Valuation.Integers.isUnit_iff_valuation_eq_one`, `Mathlib/RingTheory/Valuation/Integers.lean:160`)

Our form follows in ≤1 line (once the object is `𝒪[L]`):
```lean
-- with `x : 𝒪[L]` (= mathlib's `Valued.integer L`) and `hx : ‖(x : L)‖ = 1`:
example {x : 𝒪[L]} (hx : ‖(x : L)‖ = 1) : IsUnit x :=
  Valued.integer.isUnit_iff_norm_eq_one.mpr hx
```

Call sites in our project (from Phase 6.0):  K = 3 (all in `Interpolation/NonTame.lean`: lines 47, 62, 115).

Refactor plan (two valid routes; the choice is the `integerRing`-def BORDERLINE decision, not this theorem's):
- **Route A — re-aim onto `𝒪[L]` (the mathlib-idiomatic fix; tracked at the def level).** Resolve the sibling `PadicLFunctions.integerRing` BORDERLINE in favour of replacing `integerRing L` with `(NormedField.valuation L).integer` / `𝒪[L]` (or a thin `abbrev`). Then delete `integerRing.isUnit_of_norm_eq_one` and at each of the 3 call sites replace `integerRing.isUnit_of_norm_eq_one ?_` with `Valued.integer.isUnit_iff_norm_eq_one.mpr (by …)` — same goal shape (`refine`'s remaining `?_` is the norm-equality proof, unchanged). Ensure `[NontriviallyNormedField L]` is in scope (it is, via `NormedAlgebra ℚ_[p] L` ⇒ `‖(p:L)‖ < 1`); add it as an instance/hypothesis where the lemma is now stated more generally.
- **Route B — keep `integerRing L` local but stop re-proving the fact.** If the project keeps its bespoke subring (Route A's def-level BORDERLINE answered "keep local"), then `integerRing.isUnit_of_norm_eq_one` should become a one-line wrapper that *derives* from mathlib rather than re-proving: build the `Valuation.Integers (NormedField.valuation L) (integerRing L)` witness once (a short `Common/` lemma: the subtype map is injective with range `{v ≤ 1}`) and define `integerRing.isUnit_of_norm_eq_one := … .isUnit_of_one' …`. The 3 call sites are then untouched. This removes the duplicated *proof* while keeping the project-local name.

Next action: this verdict is gated on the `PadicLFunctions.integerRing` def decision (sibling report, `BORDERLINE-needs-human`). Once that is answered, apply Route A (delete + retarget the 3 sites to `Valued.integer.isUnit_iff_norm_eq_one.mpr`) or Route B (rewrite the body to derive from `Valuation.Integers.isUnit_of_one'`, keeping the name and the 3 sites). Either way, **do not upstream this theorem** — mathlib already has it.

---

## Next step

This verdict is gated on the `PadicLFunctions.integerRing` def decision (its own report is `BORDERLINE-needs-human`). Once that is settled, either (Route A) re-aim `integerRing` → mathlib's `𝒪[L]`, delete `integerRing.isUnit_of_norm_eq_one`, and replace the 3 `Interpolation/NonTame.lean` call sites (lines 47, 62, 115) with `Valued.integer.isUnit_iff_norm_eq_one.mpr`; or (Route B) keep `integerRing` local and rewrite this lemma's body as a one-line derivation from `Valuation.Integers.isUnit_of_one'` (via a small `Valuation.Integers (NormedField.valuation L) (integerRing L)` bridge lemma), leaving the 3 call sites unchanged. Do not open a mathlib PR for this theorem — `Valued.integer.isUnit_iff_norm_eq_one` already covers it.
