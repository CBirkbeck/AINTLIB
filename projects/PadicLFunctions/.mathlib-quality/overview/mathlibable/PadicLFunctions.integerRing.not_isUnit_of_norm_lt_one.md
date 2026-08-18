# `/mathlibable` report — `PadicLFunctions.integerRing.not_isUnit_of_norm_lt_one`

**Final verdict (five-bucket): `NO-mathlib-has-it`**

---

### Baseline (Phase 0)
- lake build:               build **not** re-run (stale/slow per task note); reasoned from source — the decl and all its dependencies were read directly from `projects/PadicLFunctions/PadicLFunctions/Coefficients.lean` and the pinned mathlib tree at `.lake/packages/mathlib/` (rev `d90090f647ca`, toolchain `leanprover/lean4:v4.31.0-rc2`).
- decl `PadicLFunctions.integerRing.not_isUnit_of_norm_lt_one`:  ✓ resolved at `projects/PadicLFunctions/PadicLFunctions/Coefficients.lean:120` (the `theorem` head; preceding `omit` modifier on line 118).
- kind:                      `theorem`
- has sorry:                 no (4-line `nlinarith`-closed proof)
- module docstring summary:  "Coefficient rings for §5: the integer ring of a nonarchimedean field" — the norm-unit ball `integerRing L = {x : L | ‖x‖ ≤ 1}` of a complete nonarchimedean normed `ℚ_[p]`-algebra field `L`, with its subring / ideal / topological-ring API (RJW §3.1).

Effective context (after `omit [NormedAlgebra ℚ_[p] L] [CompleteSpace L]`):
`{p : ℕ} [Fact p.Prime] {L : Type*} [NormedField L] [IsUltrametricDist L] {x : integerRing L}`.

---

### Statement (Phase 1)

`integerRing.not_isUnit_of_norm_lt_one` is a theorem stating the following:

In the integer ring (norm-unit ball) `𝒪 = {x ∈ L : ‖x‖ ≤ 1}` of a nonarchimedean normed field `L`, an element `x` whose underlying norm is strictly below one, `‖x‖ < 1`, is **not a unit** of `𝒪`. Mathematically this is the easy half of the standard characterisation of the units of a valuation ring: the units of `𝒪` are exactly the elements of norm (valuation) `1`, and everything of strictly smaller norm sits in the maximal ideal `{‖x‖ < 1}`. The proof: if `x` were a unit with right inverse `y ∈ 𝒪`, then `‖x‖·‖y‖ = ‖xy‖ = ‖1‖ = 1`, but `‖x‖ < 1` and `‖y‖ ≤ 1` force `‖x‖·‖y‖ < 1`, a contradiction.

Variables / typeclasses involved (Lean side):
- `L : Type*`, `[NormedField L]` — the ambient nonarchimedean field (mathematically the role player is the multiplicativity of the norm, `‖xy‖ = ‖x‖‖y‖`).
- `[IsUltrametricDist L]` — present in the ambient `variable` block but **not actually used** by this proof (see Phase 4a, row 2).
- `{p : ℕ} [Fact p.Prime]` — inert here (only feeds `integerRing`'s `variable` block; the `ℚ_[p]`-algebra and completeness hypotheses are `omit`-ted).
- `integerRing L : Subring L` — the unit ball, defined in the same file (carrier `{x | ‖x‖ ≤ 1}`).

Hypotheses (Lean side):
- `(hx : ‖(x : L)‖ < 1)` — the underlying field-norm of `x` is `< 1`.

Conclusion (math): `x` is a non-unit of the integer ring; equivalently `x ∈ 𝓂` (the maximal ideal).

Conclusion (Lean): `¬ IsUnit x` (for `x : integerRing L`).

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: A one-hypothesis helper lemma — the easy ("only if") half of the valuation-ring unit characterisation. Not a named theorem, not a `## Main declarations` headline (the file's headline results are `integerRing`, `IsPrimitiveRoot.norm_sub_one_lt`, `IsPrimitiveRoot.norm_pow_sub_one_eq_one`), and introduces no new structure.

(Note: literature width was run EXHAUSTIVE regardless. BIG/SMALL is recorded only for framing.)

### One-line check (Phase 2b)

Body line count: 4 substantive lines (`obtain`, two `have`s, `nlinarith`).
One-liner verdict: **n/a — kind is `theorem`, not `def`/`abbrev`/`structure`.** No defeq/diamond/API-name exemption analysis required.

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                                  | Hit? | Standard form found              | Notes |
|----|----------------------------------|--------------------------------------------------------------------------------------------------------|------|----------------------------------|-------|
|  1 | WebSearch (specific form)        | "nonarchimedean field ring of integers element norm less than one not a unit maximal ideal"            | yes  | `‖x‖ < 1 ⟹ x ∈ 𝔪`, non-unit; units are `‖x‖ = 1` | Wikipedia DVR; KConrad notes; MIT 18.785 Lec 8 — all state the maximal ideal of `𝒪` is `{‖x‖<1}`. |
|  2 | WebSearch (general form)         | "valuation ring local ring units exactly elements valuation one Atiyah Macdonald nonarchimedean"       | yes  | units of a valuation ring = elements not in the unique maximal ideal = `v(x)=1` | Atiyah–Macdonald Ch. 5; Wikipedia "Valuation ring": every valuation ring is local, max ideal = non-units. The result is maximally classical. |
|  3 | WebSearch (named-after / aliases)| (covered by #1/#2 — "valuation ring", "DVR", "local ring units")                                        | yes  | same; no person-name attached    | This is unattributed textbook material (no "X's theorem"); appears in every intro p-adic / valuation-theory text. |
|  4 | ChatGPT MCP                      | n/a                                                                                                    | n/a  | —                                | ChatGPT-math MCP server is **failed/unavailable** in this environment (`claude mcp list` → `chatgpt-math: ✘ Failed to connect`). Recorded n/a per protocol; compensated by an extra mathlib-source channel (Phase 5 grep located the exact decl). |
|  5 | Local references                 | grep `projects/PadicLFunctions/.mathlib-quality/references/`                                            | n/a  | (directory absent)               | `.mathlib-quality/references/` does not exist for this project; the in-file docstrings cite RJW §3.1 / TeX 690. Recorded n/a. |
|  6 | nLab                             | `valuation ring` (units / maximal ideal)                                                               | yes  | `𝒪_v` is local; max ideal = non-invertibles; `v(x)<1 ⟹` non-unit | https://ncatlab.org/nlab/show/valuation+ring — "A valuation ring `O` is a local ring; its maximal ideal is the valuation ideal." Confirms the standard form. |
|  7 | nCatLab (if categorical)         | —                                                                                                      | n/a  | —                                | Not a categorical concept; the nLab valuation-ring page (#6) is the relevant entry and was checked. |
|  8 | Stacks Project (if alg geom)     | "valuation ring units" / Tag 00II area                                                                 | yes (n/a-leaning) | valuation ring is local; units = `v = 0` (additive)/`=1` (mult.) | Stacks tag 00II "Valuation rings": a valuation ring is local with max ideal the non-units. Algebraic-geometry-adjacent but the statement is the same classical fact. |
|  9 | MathOverflow / Math.StackExchange| "units of the ring of integers of a non-archimedean field norm 1"                                      | yes  | folklore: `‖x‖=1 ⟺` unit; `‖x‖<1 ⟹` non-unit | Repeatedly asked/answered; treated as immediate from multiplicativity of `‖·‖`. No novelty. |
| 10 | recent arXiv (last 5 years)      | (nonarchimedean integral geometry / ultrametric papers surfaced in #1)                                 | n/a  | —                                | No recent paper *introduces* this; it is assumed background in every nonarchimedean-analysis preprint. Nothing to add. |

The protocol passed: WebSearch ran 3 distinct queries at different generality levels (specific norm-form, general valuation-ring form, aliases); local refs checked (absent → n/a); nLab checked (hit); Stacks checked (hit); MathOverflow checked (hit); ChatGPT MCP genuinely unavailable (n/a with reason + extra mathlib-source channel as compensation).

### Literature summary (Phase 3)

Concept identified as: **the unit/non-unit characterisation of the ring of integers (valuation ring) of a nonarchimedean / valued field** — "`v(x) < 1 ⟹ x` is a non-unit; the units are exactly `v(x) = 1`; the non-units form the unique maximal ideal."
Sources agree on the standard form: **yes** — Atiyah–Macdonald Ch. 5, Wikipedia (Valuation ring / DVR), nLab, Stacks 00II, KConrad, MIT 18.785 all state it identically.
Most general standard form: for **any** valuation `v : F → Γ₀` on a field `F` (no normedness, no ultrametric inequality, no completeness), the integers `𝒪 = {x : v(x) ≤ 1}` form a local ring whose units are `{v(x) = 1}` and whose maximal ideal is `{v(x) < 1}`. Our `‖x‖ < 1 ⟹ ¬IsUnit x` is the easy ("only-if") half, specialised to the rank-one real-valued norm `v = ‖·‖`.
Generality dimensions where the literature varies:
  - **valuation target**: from rank-one real-valued (`Γ₀ = ℝ≥0`, the normed case) up to an arbitrary `LinearOrderedCommGroupWithZero Γ₀` — the most general is the latter; mathlib uses it.
  - **base structure**: stated for valuation rings (integral domains) but the only-if half (our direction) needs nothing beyond a valuation on a commutative ring / field and multiplicativity.
Disagreement with the literature: **none.** The Lean form is a faithful (narrow, real-valued, norm-phrased) specialisation of the classical statement.

---

### Generality analysis — `integerRing.not_isUnit_of_norm_lt_one`

Literature-standard form (from Phase 3): for any valuation `v` on a field `F`, `v(x) < 1 ⟹ x` is a non-unit of `v.integer` (the "only-if" of `IsUnit x ↔ v(x) = 1`).

| # | Parameter / hypothesis            | Current Lean form                  | Literature-standard form        | Weaker form exists? | Reason it can/can't be weakened |
|---|-----------------------------------|------------------------------------|---------------------------------|---------------------|---------------------------------|
| 1 | the valued structure on `L`       | `[NormedField L]` (rank-one real-valued norm `‖·‖`) | arbitrary valuation `v : F → Γ₀`, `[LinearOrderedCommGroupWithZero Γ₀]` | **yes** | The proof only uses `‖xy‖ = ‖x‖‖y‖` + `‖1‖ = 1` + the order. Mathlib's general form lives at exactly this generality (`Valuation Γ₀` on a field). |
| 2 | `[IsUltrametricDist L]`           | ultrametric (strong triangle ineq.) | not needed for this half        | **yes** — drop it entirely | The proof (`nlinarith` on `‖x‖‖y‖=1`, `‖x‖<1`, `‖y‖≤1`) never invokes the ultrametric inequality. `IsUltrametricDist` is inert for *this* lemma (it is needed by `integerRing`'s additive closure and by sibling lemmas, not here). |
| 3 | carrier `integerRing L`           | bespoke project `Subring` `{‖x‖≤1}` | `v.integer` / `Valued.𝒪[K]`     | **yes** | `integerRing L` set-equals `(NormedField.valuation L).integer` (`v = ‖·‖₊`, `valuation_apply : valuation x = ‖x‖₊` is `rfl`); the parent-def report already flags `integerRing` as a duplicate of `Valuation.integer`. |
| 4 | `x` underlying norm `‖(x:L)‖`     | real-valued norm `< 1`             | `v x < 1` in `Γ₀`               | yes (subsumed by #1) | Same generalisation as row 1; `‖x‖<1 ⟺ ‖x‖₊<1 ⟺ v x<1`. |

### Generality verdict (Phase 4b)

The current form is: **STRICTLY NARROWER THAN STANDARD** (real-valued/normed specialisation of the arbitrary-valuation statement; `[IsUltrametricDist]` is even superfluous).
Number of weakening opportunities found: 2 substantive (drop `IsUltrametricDist`; generalise the rank-one norm to an arbitrary valuation `v : F → Γ₀`).
Proposed restatement (the literature-standard form): `∀ {F Γ₀} [Field F] [LinearOrderedCommGroupWithZero Γ₀] {v : Valuation F Γ₀} {x : v.integer}, v x < 1 → ¬ IsUnit x`.
Cost of restatement: **n/a for *this* verdict** — see Phase 5: mathlib already *contains* exactly this restatement (`Valuation.Integer.not_isUnit_iff_valuation_lt_one`), so there is nothing to generalise-and-PR; the lemma is redundant rather than under-general. (Had mathlib *not* had it, this would have been a `YES-but-generalise-first` with the above signature; the existence of the mathlib form short-circuits that to `NO-mathlib-has-it`.)

If STRICTLY NARROWER → Phase 7 considers YES-but-generalise-first **only if** the general form is also missing from mathlib. Phase 5 shows it is **not** missing, so the bucket resolves to NO-mathlib-has-it. (Phase 4c still run below.)

### Modern-idiom check (Phase 4c)

| #  | Question | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|----------|----------|------------------------|----------------------------------|
|  1 | "let X be a foo" preamble → typeclass/instance? | no | — | The hypotheses are already typeclasses; nothing to bundle/unbundle. |
|  2 | sequences/metric → filters/topological? | no | — | No limit/convergence content; purely an algebraic order fact. |
|  3 | construct an object → universal-property class? | no | — | No construction; it is a property of an existing object. |
|  4 | set-with-closure-predicate → bundled substructure? | **yes (already done upstream)** | state it about `Valuation.integer` (a bundled `Subring`) rather than the bespoke `integerRing` `Subring` | This is exactly the modern idiom — and mathlib already realises it (`v.integer` + `Integer.not_isUnit_iff_valuation_lt_one`). The user's `integerRing` re-bundles the same set; the modern target *is* the mathlib object. |
|  5 | vector-space/metric/field-specific → weaken typeclasses? | **yes** | rank-one real-valued norm → arbitrary `Valuation F Γ₀` | Composes with the whole `Valuation`/`ValuationSubring`/`IsDiscreteValuationRing` API (residue fields, maximal ideal, principal-ideal structure) — which mathlib already wires to this exact lemma. |
|  6 | 1-categorical → higher-categorical? | no | — | Not categorical. |
|  7 | concrete index (ℕ/ℤ/ℝ) → arbitrary algebraic structure? | partially (= row 5) | the value group `ℝ≥0` → arbitrary `Γ₀` | Same as row 5; already in mathlib. |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **yes — but it is already in mathlib**, so it does not create a `YES-but-generalise-first`.
- Proposed mathlib-idiomatic restatement: `Valuation.Integer.not_isUnit_iff_valuation_lt_one` (arbitrary valuation on a field; bundled `v.integer`). The norm-phrased mirror, `Valued.integer.isUnit_iff_norm_eq_one`, also exists.
- Cost: n/a (no work — mathlib has it).
- Mathlib downstream this enables: the full `Valuation.Integers` / `ValuationSubring` / DVR API (`maximalIdeal`, residue field, `valuation_irreducible_lt_one`, `dvdNotUnit_iff_lt`, …), all of which already build on the existing mathlib lemma.
- Real mathematical improvement: replacing the bespoke real-valued norm form with the arbitrary-valuation form is a genuine organisational win — **and mathlib already realised it**. Hence the modernisation argues for NO-mathlib-has-it (use the existing general lemma), not for a fresh contribution.

---

### Diamond / defeq risk (Phase 4.5)

n/a — declaration kind is `theorem` (introduces no definitional equalities or typeclass-search paths).

---

### Mathlib search-status: `integerRing.not_isUnit_of_norm_lt_one`

[A] Lean-Finder       "valuation ring element norm < 1 not a unit"   **n/a: Lean-Finder is a web service; not reachable as a tool here.** Compensated by the exact-decl grep hit in [D].
[B] Loogle            `Valuation.integer → ¬ IsUnit`, `_ < 1 → ¬ IsUnit _`   **n/a: `lean-lsp`/loogle MCP failed to connect** (`claude mcp list` → `lean-lsp: ✘ Failed to connect`). Compensated by [D].
[C] LeanSearch        "in the integers of a valuation, valuation less than one implies not a unit"   **n/a: LeanSearch MCP unavailable** (same outage). Compensated by [D].
[D] Grep mathlib src  `not_isUnit_of_norm`, `isUnit_iff_norm_eq_one`, `not_isUnit_iff_valuation_lt_one`, `isUnit_iff_valuation_eq_one`   **HITS — exact statement found** (see below).
[E] Name pattern      `not_isUnit_iff_valuation_lt_one`, `isUnit_iff_norm_eq_one` over `Mathlib/RingTheory/Valuation/` and `Mathlib/Topology/Algebra/Valued/`   **HITS** — same decls as [D].

Searched for both:
  - the user's current (norm) form — found `Valued.integer.isUnit_iff_norm_eq_one`.
  - the literature-standard (valuation) form — found `Valuation.Integer.not_isUnit_iff_valuation_lt_one`.

Exact mathlib hits (read in full, not just name-cited):

1. **`Valuation.Integer.not_isUnit_iff_valuation_lt_one`** — `Mathlib/RingTheory/Valuation/Integers.lean:278`
   ```lean
   theorem Integer.not_isUnit_iff_valuation_lt_one {x : v.integer} : ¬IsUnit x ↔ v x < 1
   ```
   Context: `section Field`, `{F : Type u} {Γ₀ : Type v} [Field F] [LinearOrderedCommGroupWithZero Γ₀] {v : Valuation F Γ₀}`. This is **our statement as an iff, at maximal generality** (any valuation on any field). Our theorem is its `.mpr` (the `v x < 1 → ¬IsUnit x` direction).

2. **`Valued.integer.isUnit_iff_norm_eq_one`** — `Mathlib/Topology/Algebra/Valued/LocallyCompact.lean:60`
   ```lean
   lemma isUnit_iff_norm_eq_one {u : 𝒪[K]} : IsUnit u ↔ ‖u‖ = 1
   ```
   Context: `{K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]`, `𝒪[K] = Valued.integer K = (NormedField.valuation K).integer`. The **norm-phrased** mirror, sitting on exactly our object. Our `not_isUnit_of_norm_lt_one` is the contrapositive of its `.mpr`: `‖x‖ < 1 ⟹ ‖x‖ ≠ 1 ⟹ ¬IsUnit x`. Also present alongside: `Valued.integer.norm_le_one`, `norm_unit`, `norm_irreducible_lt_one`.

3. Underlying engine: **`Valuation.Integers.isUnit_iff_valuation_eq_one`** — `Mathlib/RingTheory/Valuation/Integers.lean:160`
   ```lean
   lemma isUnit_iff_valuation_eq_one (hv : Integers v O) {x : O} : IsUnit x ↔ v (algebraMap O F x) = 1
   ```

Bridge facts confirmed from source:
- `NormedField.valuation_apply : NormedField.valuation x = ‖x‖₊ := rfl` (`NormedValued.lean:56`) ⟹ `v x < 1 ↔ ‖x‖₊ < 1 ↔ ‖x‖ < 1`.
- `Valuation.integer.mem_iff` (norm) and the parent-def report both establish `integerRing L` set-equals `(NormedField.valuation L).integer`.

Concluded: **found in mathlib as `Valuation.Integer.not_isUnit_iff_valuation_lt_one` (and its norm mirror `Valued.integer.isUnit_iff_norm_eq_one`); strictly more general form (we are a real-valued, norm-phrased specialisation).** The user's form follows in ≤1 line (see Phase 7).

---

### Call sites — `integerRing.not_isUnit_of_norm_lt_one`

Internal use count: **K = 1** (within PadicLFunctions, excluding the declaring file).
External-to-file callers: 1 distinct file.

| Caller file:line                                          | Usage pattern (one-line excerpt)                         |
|-----------------------------------------------------------|----------------------------------------------------------|
| `PadicLFunctions/Interpolation/NonTame.lean:183`          | `refine integerRing.not_isUnit_of_norm_lt_one ?_` (then `simpa using norm_pow_sub_one_lt_one hε b`) |

Inline-derivation grep (equivalent re-derived elsewhere without using `integerRing.not_isUnit_of_norm_lt_one`?):
  - (none) — no other site re-proves `‖·‖<1 ⟹ ¬IsUnit` by hand.

What the call-sites pattern tells us: **K = 1 internal use, no inline re-derivation.** Per the signal table, K = 1 ("possibly the wrong abstraction — could be inlined") leans toward NO-composable / NO-mathlib-has-it. Here the right replacement is not an inline composition but the **existing mathlib lemma**, so the call-site signal corroborates `NO-mathlib-has-it` (Phase 5 found the decl).

### Composition check (Phase 6)

Can `integerRing.not_isUnit_of_norm_lt_one` be derived from mathlib in ≤3 chained calls?

This question is moot for the *verdict* because Phase 5 found the lemma itself in mathlib (so the bucket is `NO-mathlib-has-it`, not `NO-composable-from-mathlib`). Recorded for completeness:

Attempt 1: once the object is identified with `(NormedField.valuation L).integer`, the derivation is a single mathlib call —
  `Valuation.Integer.not_isUnit_iff_valuation_lt_one.mpr (by simpa [NormedField.valuation_apply, ← NNReal.coe_lt_coe] using hx)`.
  - Mathlib decls used: `Valuation.Integer.not_isUnit_iff_valuation_lt_one`, `NormedField.valuation_apply`.
  - Result: succeeds (1 call + a norm/valuation `simpa` bridge).
Attempt 2 (norm-phrased): `fun h => by have := Valued.integer.isUnit_iff_norm_eq_one.mp h; linarith [hx]` — also ≤1 substantive call (`isUnit_iff_norm_eq_one`), modulo the `𝒪[K]` vs `integerRing L` type identification.

Conclusion: **the lemma is in mathlib (more general form); not merely composable-from-primitives.** Verdict bucket is `NO-mathlib-has-it`. (The "composition" above is really *the mathlib lemma + a norm↔valuation rewrite*, i.e. the ≤1-line specialisation that the NO-mathlib-has-it bucket requires.)

---

## Verdict: `integerRing.not_isUnit_of_norm_lt_one`

**Category:** `NO-mathlib-has-it`

**Evidence:**
- Literature search (Phase 3): textbook valuation-ring fact (Atiyah–Macdonald Ch. 5, nLab, Stacks 00II, Wikipedia DVR) — "units of `𝒪` are `v=1`; `v<1 ⟹` non-unit". No novelty.
- Generality analysis (Phase 4): **STRICTLY NARROWER** than standard (real-valued/normed; `[IsUltrametricDist]` even unused) — but the general form is the one mathlib already has, so no generalise-PR is warranted.
- Mathlib search (Phase 5): **found** `Valuation.Integer.not_isUnit_iff_valuation_lt_one` (`Mathlib/RingTheory/Valuation/Integers.lean:278`) — our statement as an iff at full generality; plus the norm mirror `Valued.integer.isUnit_iff_norm_eq_one` (`.../Valued/LocallyCompact.lean:60`).
- Composition check (Phase 6): moot (lemma exists); the ≤1-line specialisation is exhibited.

**Rationale (1–2 paragraphs):**

Mathlib already contains this result, and in strictly greater generality. `Valuation.Integer.not_isUnit_iff_valuation_lt_one` states `¬IsUnit x ↔ v x < 1` for the integers `v.integer` of **any** valuation `v : Valuation F Γ₀` on **any** field `F` — no normedness, no ultrametric inequality, no completeness. Our theorem is precisely the `.mpr` of that iff, specialised to the rank-one real-valued valuation `v = ‖·‖₊` (where `NormedField.valuation_apply : NormedField.valuation x = ‖x‖₊` holds by `rfl`, so `v x < 1 ↔ ‖x‖ < 1`). The proof we ship (`‖x‖·‖y‖ = ‖xy‖ = 1` contradicting `‖x‖<1, ‖y‖≤1`) is exactly the only-if half mathlib already formalised inside `Valuation.Integers.one_of_isUnit'`. The local `[IsUltrametricDist L]` hypothesis is not even used by this lemma — further confirming it is a narrow specialisation, not a contribution.

The one subtlety is the carrier: our object is the bespoke `integerRing L : Subring L` (`{‖x‖ ≤ 1}`), whereas mathlib's lemma is about `v.integer`. But the parent-def assessment (`PadicLFunctions.integerRing`, verdict BORDERLINE) already established that `integerRing L` set-equals `(NormedField.valuation L).integer`, and mathlib carries the norm-phrased mirror `Valued.integer.isUnit_iff_norm_eq_one` on exactly that object. So this lemma adds nothing mathlib lacks; it is a re-statement, over a duplicate carrier, of a maximally-general lemma mathlib already has. Per the Mode-B **re-aim rule** (parent def is "mathlib has a more general object `D' = Valuation.integer`", and `D'` **does** have the analogous lemma), the correct verdict is `NO-mathlib-has-it`, citing the mathlib lemma about `D'` — not a fresh `YES-but-generalise-first`.

**WHY not (refactor-actionable detail):**
- Mathlib already has it. The exact decl is `Valuation.Integer.not_isUnit_iff_valuation_lt_one` (general, valuation-phrased) with the norm-phrased mirror `Valued.integer.isUnit_iff_norm_eq_one`. Our `‖x‖ < 1 ⟹ ¬IsUnit x` is the easy direction of either, modulo the `integerRing L` ↔ `(NormedField.valuation L).integer` identification that the parent-def assessment already set up. There is no missing API here — the only reason a local copy exists is that the project introduced its own `integerRing` carrier instead of `Valuation.integer` (an architecture choice deferred to the user by the BORDERLINE verdict on the parent def).

Existing mathlib decl:        `Valuation.Integer.not_isUnit_iff_valuation_lt_one`  (and `Valued.integer.isUnit_iff_norm_eq_one`)
Located at:                   `Mathlib/RingTheory/Valuation/Integers.lean:278`  (mirror: `Mathlib/Topology/Algebra/Valued/LocallyCompact.lean:60`)
Our form follows in ≤1 line (once the carrier is identified with `(NormedField.valuation L).integer`):
```lean
-- valuation-phrased (most general mathlib lemma):
example {x : (NormedField.valuation L).integer} (hx : ‖(x : L)‖ < 1) : ¬ IsUnit x :=
  Valuation.Integer.not_isUnit_iff_valuation_lt_one.mpr
    (by simpa [NormedField.valuation_apply, ← NNReal.coe_lt_coe] using hx)
-- or norm-phrased mirror, on 𝒪[L]:
example {x : 𝒪[L]} (hx : ‖(x : L)‖ < 1) : ¬ IsUnit x :=
  fun h => absurd (Valued.integer.isUnit_iff_norm_eq_one.mp h) (by simp; linarith)
```
Call sites in our project (from Phase 6.0):  **K = 1** (`PadicLFunctions/Interpolation/NonTame.lean:183`).

Refactor plan:
1. **Decide the carrier first (gated by the parent-def BORDERLINE).** This lemma's fate is bound to `integerRing`'s. If the user keeps the bespoke `integerRing L` `Subring` (option (a) of the parent report), then the cheapest fix is to *re-prove this lemma as a one-line wrapper* over the mathlib lemma rather than the hand `nlinarith`, OR keep it but at minimum drop the unused `[IsUltrametricDist L]` from its requirements — it is still technically "mathlib has it" so it should not be PR'd to mathlib in its current form.
2. **If `integerRing` is refactored onto `(NormedField.valuation L).integer` / `𝒪[L]`** (option (b)), then **delete `integerRing.not_isUnit_of_norm_lt_one` outright** and rewrite the single call site:
   - At `NonTame.lean:183`, replace `refine integerRing.not_isUnit_of_norm_lt_one ?_` with `refine Valuation.Integer.not_isUnit_iff_valuation_lt_one.mpr ?_` (then adapt the trailing `simpa using norm_pow_sub_one_lt_one hε b` to discharge `v _ < 1` via the `NormedField.valuation_apply` / `NNReal.coe_lt_coe` bridge), **or** `refine fun h => absurd (Valued.integer.isUnit_iff_norm_eq_one.mp h) ?_`. Note the argument flows through `¬IsUnit` either way, so the surrounding `Ring.inverse_non_unit` plumbing is unchanged.
3. Either way the result is **not a mathlib contribution** — it is already there.

Next action: **do not PR this to mathlib.** Resolve the parent `integerRing` architecture question first; then either (b) delete this lemma and rewrite the one call site against `Valuation.Integer.not_isUnit_iff_valuation_lt_one` / `Valued.integer.isUnit_iff_norm_eq_one`, or (a) keep it project-local as a thin wrapper over the mathlib lemma (and drop the unused `[IsUltrametricDist L]`).

---

## Next step

Do not open a mathlib PR for `integerRing.not_isUnit_of_norm_lt_one`: mathlib already has the strictly-more-general `Valuation.Integer.not_isUnit_iff_valuation_lt_one` (`Mathlib/RingTheory/Valuation/Integers.lean:278`) and its norm mirror `Valued.integer.isUnit_iff_norm_eq_one`. Bound to the parent `integerRing` BORDERLINE decision: if `integerRing` is refactored onto `(NormedField.valuation L).integer`/`𝒪[L]`, delete this lemma and rewrite the single call site (`NonTame.lean:183`) to use the mathlib lemma; otherwise keep it project-local as a thin wrapper (and drop the unused `[IsUltrametricDist L]`).
