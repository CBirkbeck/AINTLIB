# `/mathlibable` report — `PadicLFunctions.norm_natCast_self_lt_one`

**Final verdict: `NO-composable-from-mathlib`** — mathlib has the two building
blocks (`Padic.norm_p_lt_one` + `norm_algebraMap'`); the statement is a 3-call
composition through `map_natCast`. No new lemma is justified; inline at the
single call site.

---

### Baseline (Phase 0)

- lake build:               build not re-run; reasoned from source (per task BUILD NOTE — `lake build` stale/slow here; read decl + dependencies directly from `.lake/packages/mathlib`)
- decl `PadicLFunctions.norm_natCast_self_lt_one`: ✓ resolved at `projects/PadicLFunctions/PadicLFunctions/Coefficients.lean:140`
- kind:                      theorem
- has sorry:                 no
- module docstring summary:  Coefficient rings for §5 — the integer ring (norm-unit ball) of a nonarchimedean complete normed `ℚ_[p]`-algebra field `L`, plus norm facts about roots of unity. RJW §3.1/§5.

Dependencies read from source (all confirmed present in the pinned mathlib):
- `Padic.norm_p_lt_one` — `Mathlib/NumberTheory/Padics/PadicNumbers.lean:858` — `‖(p : ℚ_[p])‖ < 1`.
- `norm_algebraMap'` — `Mathlib/Analysis/Normed/Module/Basic.lean:293` — `[NormOneClass 𝕜'] (x : 𝕜) : ‖algebraMap 𝕜 𝕜' x‖ = ‖x‖`.
- `NormedDivisionRing.to_normOneClass` — `Mathlib/Analysis/Normed/Field/Basic.lean:62` (priority 900) — every `NormedField` is a `NormOneClass`, so the `norm_algebraMap'` hypothesis on `L` is discharged automatically.
- `map_natCast` (RingHom version) — used in the project proof to rewrite `((p : ℕ) : L) = algebraMap ℚ_[p] L ((p : ℕ) : ℚ_[p])`.

---

### Statement (Phase 1)

`PadicLFunctions.norm_natCast_self_lt_one` is a theorem stating the following:

> Let `p` be a prime and let `L` be a normed field that is a normed `ℚ_p`-algebra.
> Then the norm of `p` (the image of the natural number `p` in `L`) is strictly
> less than `1`.

Mathematically: in any normed `ℚ_p`-algebra-field `L`, the absolute value
extends the `p`-adic absolute value on the scalars `ℚ_p` (the scalar embedding
`ℚ_p ↪ L` is norm-preserving because `‖1‖ = 1`), so `‖p‖_L = ‖p‖_{ℚ_p} = 1/p < 1`.
Equivalently, `p` lies in the maximal ideal of the valuation ring of `L`.

Variables / typeclasses involved (Lean side):
- `p : ℕ`, `[hp : Fact p.Prime]` — the residue characteristic / the prime.
- `L : Type*`, `[NormedField L]` — a normed field (the extension field).
- `[NormedAlgebra ℚ_[p] L]` — `L` is a normed algebra over `ℚ_p`; this is what
  forces the norm on `L` to extend the `p`-adic norm on scalars.
- `[IsUltrametricDist L]`, `[CompleteSpace L]` — **present in the section
  `variable` block but explicitly `omit`-ed for this theorem** (see the
  `omit [IsUltrametricDist L] [CompleteSpace L] in` on line 137). The theorem
  uses neither completeness nor the ultrametric inequality.

Hypotheses (Lean side): none beyond the typeclass context (it is a closed
inequality about the structure).

Conclusion (math): `‖p‖ < 1` in `L`.

Conclusion (Lean): `‖((p : ℕ) : L)‖ < 1`.

---

### Size classification (Phase 2a)

Verdict: **SMALL**

Reason: a one-step helper inequality — neither a named-after-a-person theorem,
nor a `## Main results` entry (the docstring lists `integerRing`,
`IsPrimitiveRoot.norm_sub_one_lt`, `IsPrimitiveRoot.norm_pow_sub_one_eq_one`;
this lemma supports `integerRing.not_isUnit`-style reasoning). It introduces no
new structure.

(Note: literature width is EXHAUSTIVE regardless. BIG/SMALL is recorded for
report framing only; it did not gate which channels Phase 3 ran.)

### One-line check (Phase 2b)

Body line count: 3 substantive lines (rewrite via `map_natCast`,
`norm_algebraMap'`, then `simpa … Padic.norm_p_lt_one`).
One-liner verdict: **n/a — kind is `theorem`, not `def`** (the Phase 2b
def-exemption table applies only to definitions). Recorded as a one-line note
and skipped.

---

## PHASE 3 — Literature search (EXHAUSTIVE protocol)

### Literature search table

| #  | Channel                          | Query | Hit? | Standard form found | Notes |
|----|----------------------------------|-------|------|---------------------|-------|
|  1 | WebSearch (specific form)        | "p-adic field ring of integers norm of p less than one maximal ideal uniformizer" | yes | `\|p\|_p = 1/p < 1`; maximal ideal `= {x : \|x\| < 1}`; `p` is a uniformizer of `ℤ_p` | MIT 18.785 notes, Cambridge p-adic-analysis notes, Wikipedia DVR — uniform agreement |
|  2 | WebSearch (general form)         | "extension of p-adic absolute value normed Qp-algebra \|p\| < 1 nonarchimedean" | yes | a finite (or any algebraic) extension `L/ℚ_p` carries a **unique** norm extending the `p`-adic one; hence `\|p\|_L = \|p\|_{ℚ_p} < 1` | Kedlaya 18.787, Conrad "absolute values", Stanford handouts; de Frutos-Fernández ITP 2023 "Formalizing Norm Extensions" is the relevant formalization context |
|  3 | WebSearch (named-after / aliases)| "nonarchimedean valuation ring uniformizer maximal ideal norm less than 1 local field" | yes | valuation ring `= {\|x\| ≤ 1}`, maximal ideal `m = {\|x\| < 1}`; uniformizer `π` generates `m`; for a nonarchimedean local field `K`, `m = {x : \|x\| < 1}` and `p ∈ m` | Berkeley Local Fields notes, MIT 18.785 Lecture 9; classical (Serre *Local Fields*, Neukirch ch. II) |
|  4 | ChatGPT MCP                      | (intended: "standard form + generality + historical evolution of `\|p\| < 1` over a p-adic field") | **n/a** | — | **MCP not configured in this session** (no `mcp__chatgpt*` tool present). Substituted with two extra WebSearch queries (#2, #3) at differing generality + the nLab fetch (#6), per the skill's fallback for an absent channel. |
|  5 | Local references                 | `.mathlib-quality/references/` (PadicLFunctions) for "norm p" / "valuation" | n/a | — | The project references store is `refs/<project>/` (gitignored, LOCAL ONLY, symlinked per worktree) and is not populated in this checkout; recorded `n/a`. The fact is in any of the cited standard texts. |
|  6 | nLab                             | `p-adic number` (fetched the page) | yes | nLab states `\|x\|_p = p^{-v_p(x)}`, so `\|p\|_p = p^{-1} = 1/p < 1`; a `p`-adic integer `u` is a unit iff `p ∤ u`, hence `p` lies in the maximal ideal | Presented as a **fundamental definitional fact**, not a derived theorem |
|  7 | nCatLab (if categorical)         | — | n/a | — | Not a categorical concept (a norm inequality on a valued field); nLab `p-adic number` already covered the abstract statement in #6. |
|  8 | Stacks Project (if alg geom)     | — | n/a | — | Not an algebraic-geometry / scheme statement. The underlying object (DVR / valuation ring) appears in Stacks (tag 00I8 etc.), but the specific norm inequality is elementary valuation theory, fully covered by #1–#3. |
|  9 | MathOverflow / Math.StackExchange| "norm of p in extension of Qp less than 1" (covered via #1–#3 web sweep) | yes | community answers reproduce: extend the valuation uniquely; `\|p\| = 1/p` | No research-level subtlety — it is a first-course p-adic fact; not separately tabulated to avoid a duplicate row |
| 10 | recent arXiv (last 5 years)      | "Qp-algebra norm" / "norm extension p-adic" | n/a (no novel form) | — | The only relevant modern item is the formalization line (de Frutos-Fernández, ITP 2023) about *norm extensions* infrastructure, not a new mathematical form of this inequality. The mathematics is ~century old. |

Protocol pass check:
- WebSearch ran 3 distinct queries at different generality levels (specific
  `ℚ_p`/`ℤ_p` form, the general extension-field form, the
  uniformizer/valuation-ring aliasing) — ✓.
- ChatGPT MCP: not available; substituted with extra WebSearch + nLab, reason
  recorded — handled per fallback.
- Local references checked (`n/a`, reason recorded) — ✓.
- nLab checked (hit) — ✓.
- Stacks / nCatLab / MathOverflow / arXiv each checked or `n/a` with reason — ✓.

### Literature summary (Phase 3)

Concept identified as: **the norm of a uniformizer / of `p` in a nonarchimedean
field extending `ℚ_p`** — equivalently, "`p` lies in the maximal ideal of the
valuation ring", a basic fact of `p`-adic / local-field theory.

Sources agree on the standard form: **yes**. Every source gives
`‖p‖ = p^{-1} = 1/p`, hence `< 1`, in `ℚ_p`; and the unique-extension theorem
propagates this to any complete (indeed any algebraic) normed extension `L/ℚ_p`.

Most general standard form: in any nonarchimedean valued field `L` whose
absolute value restricts to (a power of) the `p`-adic one on `ℚ_p` — i.e. any
normed `ℚ_p`-algebra field — `‖p‖_L < 1`. More generally still, for **any**
nonarchimedean valued ring/field, the norm of a non-unit of the valuation ring
is `< 1`; `p` being a non-unit in `ℤ_p` is the special case.

Generality dimensions where the literature varies:
- *Base/extension*: from `ℚ_p` itself (`Padic.norm_p_lt_one`), to `ℤ_p`
  (`PadicInt.norm_p`), to finite extensions `L/ℚ_p` (local-field theory), to
  `ℂ_p = PadicAlgCl p` (mathlib `Mathlib/NumberTheory/Padics/Complex.lean`),
  to an arbitrary normed `ℚ_p`-algebra field (the user's form).
- *Abstraction*: stated with an absolute value `|·|` or with a valuation
  `v(p) = 1`; the two are the same up to taking `-log`.

Disagreement with the literature: **none**. The user's `L` (normed
`ℚ_p`-algebra field) sits at a natural, standard generality. The literature
fact is not novel for mathlib in any way — it is the most elementary
consequence of the algebra-map being norm-preserving (a fact mathlib already
provides) combined with `‖p‖_{ℚ_p} < 1` (also already in mathlib).

---

## PHASE 4 — Generality analysis

Literature-standard form (from Phase 3): `‖p‖ < 1` in any nonarchimedean field
extending `ℚ_p` (and, at maximal abstraction, the norm of any non-unit of a
nonarchimedean valuation ring is `< 1`).

### Generality status table (Phase 4a)

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason it can/can't be weakened |
|---|------------------------|-------------------|--------------------------|---------------------|---------------------------------|
| 1 | `[NormedField L]` | normed field | any nonarchimedean valued **ring**/field extending `ℚ_p` | yes (mildly) | The proof only needs `‖1‖ = 1` (`NormOneClass`) + a `NormedAlgebra ℚ_[p]` structure. The general "non-unit ⇒ norm `< 1`" form lives in valuation-theory typeclasses, not in the normed-`ℚ_p`-algebra packaging — a *different statement*, not a free weakening of this one. |
| 2 | `[NormedAlgebra ℚ_[p] L]` | `L` is a normed `ℚ_p`-algebra | absolute value of `L` extends the `p`-adic one | NO (essential) | This is exactly the hypothesis that makes `‖p‖_L = ‖p‖_{ℚ_p}`. Cannot be dropped. |
| 3 | `[IsUltrametricDist L]` | ultrametric | — | yes — **already dropped** | The theorem `omit`s it (line 137). Not used. |
| 4 | `[CompleteSpace L]` | complete | — | yes — **already dropped** | The theorem `omit`s it (line 137). Not used. |

The hypotheses actually consumed are the minimal pair `[NormedField L]` +
`[NormedAlgebra ℚ_[p] L]` (`NormedField ⇒ NormOneClass` automatically). The two
unused typeclasses are already `omit`-ed, so the *effective* statement is
already lean and at a sensible generality.

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL** (within the normed-`ℚ_p`-algebra
framing). The two non-essential typeclasses are already omitted; the remaining
two are exactly what the one-line content needs. A strictly more general
*valuation-theoretic* restatement ("norm of a non-unit of a nonarchimedean
valuation ring is `< 1`") is a genuinely *different* theorem in a different part
of the library, not a weakening of this one — and (see Phase 5) mathlib's
valuation layer already carries that general fact (e.g.
`Valuation.uniformizer_lt_one` / `val_map_lt_one_iff`).

Number of weakening opportunities found: 0 that keep this same statement.
Proposed restatement: none (already minimal for the chosen framing).
Cost of restatement: n/a.

### Modern-idiom check (Phase 4c)

| #  | Question | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|----------|----------|------------------------|----------------------------------|
|  1 | "let X be a foo" preambles → typeclasses? | no | — | Already fully typeclass-driven (`NormedField` + `NormedAlgebra ℚ_[p]`); nothing to de-bundle. |
|  2 | sequences/metric → filters/topological? | no | — | A pointwise norm inequality; no limit/convergence content to filter-ise. |
|  3 | construct an object → universal-property class? | no | — | No object constructed; it is an inequality. |
|  4 | set-with-closure-predicate → bundled substructure? | no | — | No subset/closure here (that is the neighbouring `integerRing` def, not this lemma). |
|  5 | vector-space/metric/field-specific → weakened typeclass (module/seminormed/(semi)ring)? | partially | the valuation-theoretic form `v(p) < 1` for a nonarchimedean valuation ring / `Valuation.val_map_lt_one_iff` | This is the *modern* mathlib idiom for "norm < 1 ⇔ in the maximal ideal". But it is a **different lemma in a different file**, and mathlib already has it (Phase 5). It does not turn the user's lemma into a contribution. |
|  6 | 1-categorical → higher-categorical? | no | — | No categorical content. |
|  7 | concrete index ℕ/ℤ/ℝ → arbitrary monoid/group? | no | — | `p` is intrinsically a specific prime natural number here; generalising the *index* is meaningless for this fact. |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no** (none that would make *this* lemma a mathlib
contribution). The only "more modern" framing — phrasing via mathlib's
`Valuation` / `ValuativeRel` layer (`v(p) < 1` ⇔ `p ∈ maximal ideal`) — is a
distinct, already-present mathlib statement, not a reformulation that upgrades
the user's lemma into something worth adding. Reason this is not a
modernisation move: the user's lemma is a one-step consequence of two existing
mathlib lemmas; "modernising" it just rediscovers other existing mathlib API.

---

## PHASE 4.5 — Diamond / defeq risk

n/a — declaration kind is `theorem`. (No definitional equalities or
typeclass-search paths introduced.)

---

## PHASE 5 — Mathlib search

### Mathlib search-status: `PadicLFunctions.norm_natCast_self_lt_one`

[A] Lean-Finder — n/a: the hosted Lean-Finder Space was not reachable as a
    programmatic endpoint from this session. Substituted with LeanSearch (C)
    + Loogle (B) + grep (D) + name-pattern (E), all of which converged.

[B] Loogle — queries:
    - `‖((?p : ℕ) : ?L)‖ < 1` → hits: `Padic.norm_p_lt_one`
      (`‖(p : ℚ_[p])‖ < 1`), `PadicInt.norm_natCast_lt_one_iff`
      (`‖(n : ℤ_[p])‖ < 1 ↔ p ∣ n`), `PadicInt.norm_lt_one_mul`. **None over a
      general normed `ℚ_[p]`-algebra `L`.**
    - `Isometry (algebraMap ?k ?L)` → hits: **`algebraMap_isometry`**
      (`[NormOneClass 𝕜'] : Isometry (algebraMap 𝕜 𝕜')`),
      `NumberField.InfinitePlace.LiesOver.isometry_algebraMap`, and CFC isometry
      lemmas. → confirms the algebra-map isometry building block exists
      generically.

[C] LeanSearch — query: "norm of p less than one in a normed Qp-algebra" →
    returned exactly `Padic.norm_p_lt_one`, `PadicInt.norm_natCast_lt_one_iff`,
    `PadicInt.norm_lt_one_mul`. (Subsequent endpoint variants 404/405'd, but the
    first call returned a clean result set.) **No general-`L` lemma.**

[D] Grep mathlib src — terms tried over `.lake/packages/mathlib/Mathlib/`:
    `norm_p_lt_one`, `norm_natCast`, `norm_natCast_self`,
    `natCast_self_lt_one`, `self_lt_one`, `norm_algebraMap'`, `algebraMap_isometry`,
    `NormedAlgebra ℚ_[p]`, `norm_algebraMap.*lt`, `lt_one.*algebraMap`.
    Findings:
    - `Padic.norm_p_lt_one` @ `PadicNumbers.lean:858`, `Padic.norm_p` @ 852,
      `PadicInt.norm_p` @ `PadicIntegers.lean:234` — the scalar/`ℤ_p` forms.
    - `norm_algebraMap'` @ `Analysis/Normed/Module/Basic.lean:293`,
      `algebraMap_isometry` @ `:340` — the building blocks.
    - `NormedAlgebra ℚ_[p]` appears in mathlib **only** in
      `NumberTheory/Padics/Complex.lean` (for `ℂ_p = PadicAlgCl p`), where
      `valuation_p` computes `‖(p : ℂ_p)‖` via `norm_extends` + `Padic.norm_p`
      — i.e. mathlib does the *same* composition ad hoc for `ℂ_p` and does **not**
      extract a reusable general-`L` lemma.
    - Mathlib's general `norm_natCast` (`Analysis/Normed/Module/Basic.lean:75`)
      gives `‖(a:α)‖ = a` only under `[NormOneClass α] [NormSMulClass ℤ α]` — an
      archimedean-flavoured hypothesis that **fails** for a nonarchimedean
      `ℚ_p`-algebra (where `‖p‖ < 1`), so it is NOT a hit.

[E] Name-pattern (`lean_local_search` proxy via grep) — terms:
    `self_lt_one`, `norm_p_lt_one`, `uniformizer.*lt_one`, `norm_uniformizer`.
    Hits: `Padic.norm_p_lt_one`; `Valuation…uniformizer_lt_one`
    (`ValuativeRel/Basic.lean:1145`, the valuation-theoretic general form);
    `Valuation.val_map_lt_one_iff` (`Valuation/Extension.lean:89`,
    `vA (algebraMap R A x) < 1 ↔ vR x < 1`). These are the *general
    valuation-layer* facts — they confirm the content is standard and already
    present in mathlib's valuation framework, not in the normed-`ℚ_p`-algebra
    packaging.

Searched for both:
- the user's current form (`‖(p:L)‖ < 1` over a normed `ℚ_p`-algebra) — **not
  found** as a single declaration;
- the literature-standard / more-general forms (`‖p‖_{ℚ_p} < 1`; algebra-map
  isometry; `v(non-unit) < 1`) — **all present** as separate pieces
  (`Padic.norm_p_lt_one`, `norm_algebraMap'` / `algebraMap_isometry`,
  `Valuation.val_map_lt_one_iff`).

Concluded: **found building blocks** (`Padic.norm_p_lt_one`, `norm_algebraMap'`,
`map_natCast`; plus `NormedDivisionRing.to_normOneClass` to discharge
`NormOneClass L` for free) — composition yields our exact form. The packaged
general-`L` statement itself is **not** in mathlib (all five methods exhausted,
plus the literature-standard and valuation-theoretic forms).

---

## PHASE 6 — Composition check (+ call-sites)

### Call sites — `PadicLFunctions.norm_natCast_self_lt_one`

Internal use count: **K = 1** (within `PadicLFunctions`, not counting the
declaring line).
External-to-file callers: 0 distinct files (the one use is in the same file,
`Coefficients.lean`).

| Caller file:line | Usage pattern (one-line excerpt) |
|------------------|----------------------------------|
| `projects/PadicLFunctions/PadicLFunctions/Coefficients.lean:196` | `exact (hple.trans_lt norm_natCast_self_lt_one).false` |

Context: line 196 is the final contradiction step of
`IsPrimitiveRoot.norm_sub_one_lt` (W2): having derived `1 ≤ ‖(p:L)‖` (`hple`),
it chains `‖(p:L)‖ < 1` to close `1 < 1` and discharge the `by_contra`.

Inline-derivation grep (was the equivalent re-derived elsewhere without using
`norm_natCast_self_lt_one`?): **none** found — but note mathlib itself
re-derives the same `‖p‖` computation inline for `ℂ_p` in
`NumberTheory/Padics/Complex.lean:101` (`valuation_p`, via `norm_extends` +
`Padic.norm_p`), which is exactly the pattern this lemma would generalise.

Call-sites signal (per the Phase 6.0.1 table): **K = 1 internal use only →
"possibly the wrong abstraction — could be inlined; lean toward
NO-composable."** No downstream/external consumer; it is a single-use private
convenience.

### Composition check (Phase 6)

Can `norm_natCast_self_lt_one` be derived from mathlib in ≤3 chained calls?

Attempt 1 (the project's own proof, which *is* the composition):
```lean
example : ‖((p : ℕ) : L)‖ < 1 := by
  rw [show ((p : ℕ) : L) = algebraMap ℚ_[p] L ((p : ℕ) : ℚ_[p]) by simp [map_natCast],
    norm_algebraMap']
  simpa using Padic.norm_p_lt_one (p := p)
```
- Mathlib decls used: `map_natCast` (rewrite `(p:L) = algebraMap ℚ_[p] L (p:ℚ_[p])`),
  `norm_algebraMap'` (drops to `‖(p:ℚ_[p])‖`, with `NormOneClass L` free via
  `NormedDivisionRing.to_normOneClass`), `Padic.norm_p_lt_one`.
- Result: **succeeds** — this is literally the 3-line proof body in
  `Coefficients.lean:141–143`.
- Notes: per the Phase 6b heuristics, a `rw [...]; simpa using <lemma>` of two
  named mathlib rewrites + one closing lemma is a borderline-to-clean
  composition. It is **not** a "proof in disguise": there are no `have`-chains,
  no `nlinarith`/`ring_nf`/`aesop`, no case analysis — just normalise the cast
  and apply the scalar fact. It sits at the "trivial composition" end.

Attempt 2 (even tighter, term-mode flavour): `‖(p:L)‖` rewrites by
`norm_algebraMap'` to `‖(p:ℚ_[p])‖`, then `Padic.norm_p_lt_one`. The only glue
is the `map_natCast` cast-normalisation, which `simp`/`norm_cast` handles.

Conclusion: **COMPOSABLE** (≤3 mathlib calls; the project's own proof is the
witness).

---

## Verdict: `PadicLFunctions.norm_natCast_self_lt_one`

**Category:** `NO-composable-from-mathlib`

**Evidence:**
- Literature search (Phase 3): the fact `‖p‖ < 1` in a nonarchimedean field
  extending `ℚ_p` is a fundamental, century-old definitional fact (Serre,
  Neukirch, Koblitz; nLab calls it definitional). Standard form confirmed across
  ≥3 channels.
- Generality analysis (Phase 4): MAXIMALLY GENERAL for the chosen framing (the
  two unused typeclasses are already `omit`-ed); no modern-idiom upgrade turns
  it into a contribution (Phase 4c "no").
- Mathlib search (Phase 5): not present as a single decl over a general normed
  `ℚ_[p]`-algebra, but **all** building blocks are present —
  `Padic.norm_p_lt_one`, `norm_algebraMap'` (`+ NormedDivisionRing.to_normOneClass`),
  `map_natCast`; mathlib even does the same inline composition for `ℂ_p` in
  `Padics/Complex.lean`.
- Composition check (Phase 6): COMPOSABLE — the project's own 3-line proof is
  the ≤3-call composition; K = 1 internal call site, no external consumer.

**Rationale:**

This theorem is a thin, single-use convenience around two mathlib lemmas: the
scalar fact `Padic.norm_p_lt_one` (`‖p‖_{ℚ_p} < 1`) and the algebra-map norm
identity `norm_algebraMap'` (`‖algebraMap ℚ_[p] L x‖ = ‖x‖`, whose `NormOneClass L`
hypothesis is automatic for the `NormedField L` here). The cast bookkeeping
`(p:L) = algebraMap ℚ_[p] L (p:ℚ_[p])` is just `map_natCast`. Mathlib already
performs this very composition ad hoc when it needs `‖(p : ℂ_p)‖` in
`NumberTheory/Padics/Complex.lean` (`valuation_p`) — it did **not** extract a
reusable wrapper, which is the right call: the composition is short and the
hypotheses are exactly the ambient typeclass context. The "more general" form
(norm of a non-unit of a nonarchimedean valuation ring is `< 1`) already lives
in mathlib's valuation layer (`Valuation.val_map_lt_one_iff`,
`ValuativeRel…uniformizer_lt_one`), so there is no missing general statement to
contribute either. With K = 1 internal use and no external consumer, the
call-sites signal is "possibly the wrong abstraction — could be inlined", which
aligns with NO-composable. This is not a YES bucket: nothing here is novel for
mathlib, the generality is already correct, and the proof is a 3-call
composition rather than a real lemma.

**WHY not (refactor-actionable detail):** Mathlib has the building blocks; the
user's form is a ≤3-mathlib-call composition. No new lemma is justified.

Mathlib building blocks:
- `Padic.norm_p_lt_one` — `Mathlib/NumberTheory/Padics/PadicNumbers.lean:858` —
  `‖(p : ℚ_[p])‖ < 1`.
- `norm_algebraMap'` — `Mathlib/Analysis/Normed/Module/Basic.lean:293` —
  `[NormOneClass 𝕜'] (x : 𝕜) : ‖algebraMap 𝕜 𝕜' x‖ = ‖x‖`.
- `NormedDivisionRing.to_normOneClass` — `Mathlib/Analysis/Normed/Field/Basic.lean:62` —
  supplies `NormOneClass L` from `NormedField L` automatically.
- `map_natCast` — for the cast normalisation
  `((p:ℕ):L) = algebraMap ℚ_[p] L ((p:ℕ):ℚ_[p])`.

Composition sketch (≤3 lines — this is the existing proof body):
```lean
example : ‖((p : ℕ) : L)‖ < 1 := by
  rw [show ((p : ℕ) : L) = algebraMap ℚ_[p] L ((p : ℕ) : ℚ_[p]) by simp [map_natCast],
    norm_algebraMap']
  simpa using Padic.norm_p_lt_one (p := p)
```

Call sites in our project (from Phase 6.0): **K = 1** —
`Coefficients.lean:196` (`(hple.trans_lt norm_natCast_self_lt_one).false`,
inside `IsPrimitiveRoot.norm_sub_one_lt`).

Refactor plan: at the single call site (line 196), inline the composition.
Concretely, replace `norm_natCast_self_lt_one` with a local
`have hp1 : ‖((p:ℕ):L)‖ < 1 := by rw [show ((p:ℕ):L) = algebraMap ℚ_[p] L ((p:ℕ):ℚ_[p]) from by simp [map_natCast], norm_algebraMap']; simpa using Padic.norm_p_lt_one (p := p)`
and use `(hple.trans_lt hp1).false`; or, since this is the only use, keep the
3-line proof but `private` it / leave it project-local rather than treating it
as a mathlib candidate.

**Caveat (project-local nuance, not a blocker for the verdict).** Because the
same expression `‖((p:ℕ):L)‖` and the same little composition would recur in
several places in this `§5` development (e.g. the bound at lines 178–183 already
manipulates `‖((p:ℕ):L)‖`), keeping it as a *named, project-local* helper is
reasonable engineering. The verdict `NO-composable-from-mathlib` is about
**mathlib inclusion**: mathlib should not receive this wrapper. The project may
legitimately retain it locally; that is an internal-API decision, not a mathlib
contribution.

Next action: do **not** open a mathlib PR for this lemma. Inline the
composition at its single call site (or keep it as a private project-local
helper). When mathlib's `valuation`/`norm` API needs the general fact it already
has `Valuation.val_map_lt_one_iff`; no upstreaming is warranted here.

---

## Next step

Do not open a mathlib PR. Inline the ≤3-call composition
(`Padic.norm_p_lt_one` + `norm_algebraMap'` via `map_natCast`) at the single
call site `Coefficients.lean:196`, or retain `norm_natCast_self_lt_one` as a
private project-local helper. No new mathlib lemma is justified — mathlib has
both the building blocks and (in its valuation layer) the more general fact.
