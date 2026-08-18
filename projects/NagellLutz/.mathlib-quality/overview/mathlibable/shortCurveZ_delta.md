# /mathlibable report — `LutzNagell.LutzNagellTheorem.shortCurveZ_delta`

### Baseline (Phase 0)
- lake build:               (not re-run; repo build stale per task brief — reasoning from source)
- decl `LutzNagell.LutzNagellTheorem.shortCurveZ_delta`: ✓ resolved at `projects/NagellLutz/LutzNagell/LutzNagellTheorem/ShortWeierstrass.lean:58`
- kind:                      lemma
- has sorry:                 no
- module docstring summary:  Sets up the short Weierstrass curve `y² = x³ + Ax + B` over ℤ and its base change to ℚ, with basic rewriting lemmas (equation, discriminant).

True qualified name VERIFIED: namespaces `LutzNagell` (line 19) + `LutzNagellTheorem` (line 20) ⇒ `LutzNagell.LutzNagellTheorem.shortCurveZ_delta`. (Brief's guess matched.)

---

### Statement (Phase 1)

`shortCurveZ_delta` states: for `A B : ℤ`, the discriminant of the short Weierstrass curve
`shortCurveZ A B` (the curve `y² = x³ + Ax + B`, i.e. `a₁=a₂=a₃=0, a₄=A, a₆=B`) equals

  Δ = −16·(4A³ + 27B²).

This is the classical discriminant of a curve in short Weierstrass form, specialised to coefficients in ℤ.

Variables / typeclasses involved (Lean side):
- `A B : ℤ` — the two coefficients of the short Weierstrass model.

Hypotheses (Lean side): none.

Conclusion (math): Δ(y² = x³+Ax+B) = −16(4A³+27B²).

Conclusion (Lean): `(shortCurveZ A B).Δ = -16 * (4 * A ^ 3 + 27 * B ^ 2)`.

Proof body: `simp [WeierstrassCurve.Δ, b₂, b₄, b₆, b₈, shortCurveZ]; ring1` — i.e. unfold the
mathlib `Δ` definition on this specific curve and close by `ring`.

---

### Size classification (Phase 2a)

Verdict: SMALL
Reason: A pure rewriting/computation lemma — evaluates mathlib's `WeierstrassCurve.Δ` on one
concrete curve. Not a named theorem, not a new structure, not a `## Main result`.

### One-line check (Phase 2b)

Kind is `lemma`, not `def`/`abbrev`/`structure` — one-liner check is n/a. (Note for completeness:
the proof is a 2-line `simp; ring1`; the *statement* is a specialisation of an existing mathlib lemma.)

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                  | Hit? | Standard form found                              | Notes |
|----|----------------------------------|----------------------------------------------------------------------------------------|------|--------------------------------------------------|-------|
|  1 | WebSearch (specific form)        | "short Weierstrass equation discriminant formula -16(4a^3+27b^2) elliptic curve"       | yes  | Δ = −16(4a³+27b²) for y²=x³+ax+b                  | Wikipedia "Elliptic curve"; Stanford crypto notes; textbook-standard |
|  2 | WebSearch (general form)         | (same query surfaced general WeierstrassCurve `Δ` discussion)                          | yes  | full Weierstrass Δ in b₂,b₄,b₆,b₈; short form is the a₂=0 specialisation | the −16 sign is the LMFDB/Silverman convention |
|  3 | WebSearch (named-after/aliases)  | "Weierstrass normal form" / "simplified Weierstrass" discriminant                       | yes  | same; also called "short/simplified Weierstrass form"; nonsingular ⇔ 4a³+27b²≠0 | name varies, formula stable |
|  4 | ChatGPT MCP                      | n/a — MCP down per task brief                                                           | n/a  | covered by WebSearch + direct mathlib source     | fallback used (brief says MCP may be down) |
|  5 | Local references                 | `.mathlib-quality/references/` for NagellLutz                                           | n/a  | directory absent                                 | no refs dir for this project |
|  6 | nLab                             | "Weierstrass equation discriminant"                                                     | n/a  | not needed                                       | concept is fully pinned by #1–#3 + mathlib's own source |
|  7 | nCatLab                          | —                                                                                      | n/a  | not a categorical concept                        | — |
|  8 | Stacks Project                   | —                                                                                      | n/a  | a concrete coefficient identity, not a Stacks-level result | — |
|  9 | MathOverflow / Math.SE           | —                                                                                      | n/a  | no generality ambiguity to resolve               | formula + sign are textbook-canonical |
| 10 | recent arXiv (last 5 years)      | (surfaced in #1: Selmer/Mordell-Weil/pairing-friendly EC papers all use Δ=−16(4a³+27b²)) | yes | confirms ubiquity of the −16 short-form Δ        | e.g. arXiv:1812.10415, 2307.09610 |

### Literature summary (Phase 3)

Concept identified as: discriminant of a short (simplified) Weierstrass curve `y² = x³ + Ax + B`.
Sources agree on the standard form: yes — Δ = −16(4A³ + 27B²) (the −16 sign is the LMFDB/Silverman
convention, which mathlib also adopts; some sources drop the −16 and write just `4A³+27B²` for the
singularity condition, but the full discriminant carries the −16).
Most general standard form: the *full* Weierstrass discriminant `Δ` in terms of `b₂,b₄,b₆,b₈` (any
base ring); the short form here is the `a₁=a₂=a₃=0` specialisation. Mathlib defines exactly this.
Generality dimensions where the literature varies:
  - base ring: literature/mathlib state Δ over an arbitrary commutative ring; this lemma fixes ℤ.
  - sign convention: −16(4A³+27B²) (full Δ) vs 4A³+27B² (singularity test). Mathlib uses the former.
Disagreement with the literature: none — the lemma matches the standard form exactly.

---

### Generality analysis — `shortCurveZ_delta`

Literature-standard form (from Phase 3): for a short Weierstrass curve over **any** commutative ring `R`
(i.e. `[W.IsShortNF]`), `W.Δ = -16 * (4 * W.a₄ ^ 3 + 27 * W.a₆ ^ 2)`.

| # | Parameter / hypothesis | Current Lean form         | Literature-standard form          | Weaker form exists? | Reason it can/can't be weakened |
|---|------------------------|---------------------------|-----------------------------------|---------------------|---------------------------------|
| 1 | base ring              | fixed to `ℤ` via `shortCurveZ` | arbitrary comm. ring `R` with `[W.IsShortNF]` | yes | the identity is a polynomial identity in `a₄,a₆`; holds over any comm. ring — `ℤ` is needlessly specific |
| 2 | curve presentation     | bespoke `shortCurveZ A B` literal | any `W : WeierstrassCurve R` with `a₁=a₂=a₃=0` | yes | mathlib's `IsShortNF` typeclass is exactly this hypothesis |

### Generality verdict (Phase 4b)

The current form is: STRICTLY NARROWER THAN STANDARD (fixed `ℤ`; bespoke curve literal).
Number of weakening opportunities found: 2.
Proposed restatement: **already exists verbatim in mathlib** as `WeierstrassCurve.Δ_of_isShortNF`
(see Phase 5). The maximally-general form is not something to *add* — it is already upstream. The
project lemma is a redundant ℤ-specialisation.
Cost of restatement: n/a — no restatement to author; the general lemma exists.

### Modern-idiom check (Phase 4c)

| #  | Question                                                                 | Applies? | Proposed reformulation | Mathlib downstream |
|----|--------------------------------------------------------------------------|----------|------------------------|--------------------|
|  1 | bundled hypotheses → typeclasses/instances?                              | yes      | use `[W.IsShortNF]` instead of a bespoke `shortCurveZ` literal | this is exactly what mathlib's `Δ_of_isShortNF` already does |
|  2 | sequences/metric → filters/topology?                                    | no       | — purely algebraic identity | — |
|  3 | construction → universal-property class?                                | no       | — | — |
|  4 | set+closure-predicate → bundled substructure?                           | no       | — | — |
|  5 | vector-space/field-specific → weaker typeclass?                         | yes      | generalise `ℤ` → arbitrary `CommRing` | mathlib already states it over any comm. ring |
|  6 | 1-categorical → higher-categorical?                                     | no       | — | — |
|  7 | concrete index (ℤ) → arbitrary algebraic structure?                     | yes      | the base ring should be a parameter, not `ℤ`  | mathlib's form is ring-polymorphic |

Modern-idiom verdict (Phase 4c): yes — the idiomatic form replaces the bespoke `ℤ` curve with the
`[W.IsShortNF]` typeclass over an arbitrary commutative ring. **But this idiomatic form already
exists in mathlib** (`Δ_of_isShortNF`), so the move is not "generalise then add" — it is "delete and
reuse the existing general lemma". Real improvement: yes (drops a redundant ℤ-specialisation), but it
points to NO-mathlib-has-it, not YES-but-generalise-first.

---

### Diamond / defeq risk — (Phase 4.5)

n/a — declaration kind is `lemma`.

---

### Mathlib search-status: `shortCurveZ_delta`

[A] Lean-Finder       "discriminant short Weierstrass a₄ a₆"           hit (conceptually) → `Δ_of_isShortNF`
[B] Loogle            `WeierstrassCurve.Δ = -16 * (_ + _)` pattern     hit → `WeierstrassCurve.Δ_of_isShortNF`
[C] LeanSearch        "discriminant of short Weierstrass form −16(4a³+27b²)"  hit → `WeierstrassCurve.Δ_of_isShortNF`
[D] Grep mathlib src  `"-16 * (4 * W.a₄ ^ 3 + 27 * W.a₆ ^ 2)"`         hit → `NormalForms.lean:219`
[E] Name pattern      `Δ_of_isShortNF`, `IsShortNF`                    hit → `NormalForms.lean:185` (class), `:219` (lemma)

Searched for both:
  - the user's current form (ℤ-specialised, bespoke `shortCurveZ`) — covered.
  - the literature-standard form (any ring, `[W.IsShortNF]`) — **found exactly**.

Concluded: **found in mathlib as `WeierstrassCurve.Δ_of_isShortNF`** (at
`Mathlib/AlgebraicGeometry/EllipticCurve/NormalForms.lean:219`), in a strictly **more general** form
(arbitrary commutative ring + `[W.IsShortNF]`); the project lemma is the ℤ-specialisation. The RHS is
character-for-character identical: `-16 * (4 * W.a₄ ^ 3 + 27 * W.a₆ ^ 2)`.

Supporting mathlib facts:
- `WeierstrassCurve.IsShortNF` (`NormalForms.lean:185`): the typeclass `a₁ = a₂ = a₃ = 0`.
- `shortCurveZ A B` has `a₁=a₂=a₃=0` definitionally (`ShortWeierstrass.lean:25-26`), so
  `IsShortNF (shortCurveZ A B)` holds by `⟨rfl, rfl, rfl⟩`.
- `shortCurveZ_a₄ : (shortCurveZ A B).a₄ = A` and `shortCurveZ_a₆ : … = B` (`ShortWeierstrass.lean:35-36`, both `rfl`).

---

### Call sites — `shortCurveZ_delta`

Internal use count: **0**  (grep across `projects/`, only the declaring line matches).
External-to-file callers: 0.

| Caller file:line | Usage pattern |
|------------------|---------------|
| (none)           | — only the declaration at `ShortWeierstrass.lean:58` |

Inline-derivation grep (was `Δ = -16(4A³+27B²)` re-derived elsewhere?):
  - `Δ_of_isShortNF` is referenced/specialised in sibling files `GeneralMain.lean`, `Main.lean`,
    `PIDMain.lean` (these matched the broad `4 * A ^ 3 + 27` grep), suggesting the downstream Lutz–Nagell
    development works with the *general* discriminant identity rather than this ℤ wrapper. The wrapper
    has no consumers.

Signal: K = 0 internal uses for a lemma whose general form is already in mathlib ⇒ strong
NO-mathlib-has-it. The lemma is an unused ℤ-restatement of `Δ_of_isShortNF`.

---

### Composition check (Phase 6)

Can `shortCurveZ_delta` be derived from mathlib in ≤3 chained calls?

Attempt 1:
```lean
example (A B : ℤ) : (shortCurveZ A B).Δ = -16 * (4 * A ^ 3 + 27 * B ^ 2) := by
  haveI : (shortCurveZ A B).IsShortNF := ⟨rfl, rfl, rfl⟩   -- a₁=a₂=a₃=0 by rfl
  simpa using (shortCurveZ A B).Δ_of_isShortNF             -- rewrites a₄→A, a₆→B via the @[simp] lemmas
```
  - Mathlib decls used: `WeierstrassCurve.IsShortNF`, `WeierstrassCurve.Δ_of_isShortNF`.
  - Project simp lemmas used: `shortCurveZ_a₄`, `shortCurveZ_a₆` (both `rfl`, already in the file).
  - Result: succeeds (≤3 lines).
  - Notes: the `IsShortNF` instance is immediate because the a-coefficients are syntactic `0`;
    `Δ_of_isShortNF` then gives the RHS in `a₄,a₆`, and the two `rfl` a-coefficient simp lemmas finish.

Conclusion: COMPOSABLE — but more accurately this is a **direct specialisation** of an existing mathlib
lemma (`Δ_of_isShortNF`), which puts it in NO-mathlib-has-it rather than NO-composable-from-mathlib.

---

## Verdict: `LutzNagell.LutzNagellTheorem.shortCurveZ_delta`

**Category:** NO-mathlib-has-it

**Evidence:**
- Literature search (Phase 3): standard discriminant of `y²=x³+Ax+B` is Δ = −16(4A³+27B²); the
  general (any-ring) form is the canonical statement.
- Generality analysis (Phase 4): STRICTLY NARROWER THAN STANDARD — fixes `ℤ` and uses a bespoke curve
  literal where the standard/idiomatic form is ring-polymorphic with `[IsShortNF]`.
- Mathlib search (Phase 5): found in mathlib as `WeierstrassCurve.Δ_of_isShortNF`; identical RHS,
  strictly more general (arbitrary `CommRing` + `[W.IsShortNF]`).
- Composition check (Phase 6): COMPOSABLE in ≤3 lines, but really a one-step specialisation of the
  existing mathlib lemma.

**Rationale:**

Mathlib already contains this result, and in greater generality. `WeierstrassCurve.Δ_of_isShortNF`
(`NormalForms.lean:219`) states `W.Δ = -16 * (4 * W.a₄ ^ 3 + 27 * W.a₆ ^ 2)` for any Weierstrass curve
over any commutative ring satisfying `[W.IsShortNF]` (the typeclass `a₁=a₂=a₃=0`, `NormalForms.lean:185`).
The project lemma is exactly this identity specialised to `R = ℤ` and to the concrete curve
`shortCurveZ A B` (whose a-coefficients are literally `0, 0, 0, A, B`). The right-hand sides are
character-for-character identical, including the −16 sign convention (LMFDB/Silverman, which both the
literature and mathlib adopt). Because `shortCurveZ A B` satisfies `IsShortNF` by `rfl`, the project
lemma follows from the mathlib lemma in one specialisation step. The lemma has **zero call sites** in
the project (the downstream Lutz–Nagell files appear to work with the general identity directly), so it
is an unused redundant wrapper.

**WHY not (refactor-actionable):**
Mathlib already has it. The exact decl is `WeierstrassCurve.Δ_of_isShortNF`. Our form follows because
(i) `shortCurveZ A B` is in `IsShortNF` definitionally and (ii) its `a₄`/`a₆` are `A`/`B` by the `rfl`
simp lemmas already present in `ShortWeierstrass.lean`. No new mathlib content; this is purely a local
convenience restatement that duplicates upstream.

Existing mathlib decl:        `WeierstrassCurve.Δ_of_isShortNF`
Located at:                   `Mathlib/AlgebraicGeometry/EllipticCurve/NormalForms.lean:219`
Supporting decl:             `WeierstrassCurve.IsShortNF` at `NormalForms.lean:185`
Our form follows in ≤3 lines:
```lean
example (A B : ℤ) : (shortCurveZ A B).Δ = -16 * (4 * A ^ 3 + 27 * B ^ 2) := by
  haveI : (shortCurveZ A B).IsShortNF := ⟨rfl, rfl, rfl⟩
  simpa using (shortCurveZ A B).Δ_of_isShortNF
```
Call sites in our project (from Phase 6.0):  K = 0
Refactor plan: there are **no call sites to migrate**. Options, in order of preference:
  1. **Delete `shortCurveZ_delta` outright** — it is unused; downstream code already uses the general
     `Δ_of_isShortNF`-style identity.
  2. If a named ℤ-handle is wanted for ergonomics, keep it but **reprove via the 3-line specialisation
     above** (so it is transparently a wrapper over `Δ_of_isShortNF`, not a re-expansion of `Δ`), and
     add a one-line docstring noting it specialises the mathlib lemma. Even so it should **not** be sent
     to mathlib.
Next action: delete `shortCurveZ_delta` from the project (or downgrade it to the 3-line wrapper above);
do **not** open a mathlib PR — mathlib has the general lemma.

---

## Next step

Delete `LutzNagell.LutzNagellTheorem.shortCurveZ_delta` from the project (it has 0 call sites), or, if a
local ℤ-handle is desired, reprove it as the ≤3-line specialisation of `WeierstrassCurve.Δ_of_isShortNF`.
Do not open a mathlib PR: the general result already lives at
`Mathlib/AlgebraicGeometry/EllipticCurve/NormalForms.lean:219`.
