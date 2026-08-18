# /mathlibable report — `invar₂_normEDS`

Project: NagellLutz (Nagell–Lutz theorem; elliptic curves; division polynomials; elliptic divisibility sequences)
Declaration site: `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:1491`
Date: 2026-06-21 (full 10-phase re-assessment; supersedes the 2026-06-18 overview-triage note)

> Note on the prior verdict. The earlier overview-triage note for this decl recorded
> **YES-but-generalise-first** with "BORDERLINE-needs-human" called out as its close second.
> This full pass lands on **BORDERLINE-needs-human**. Reason: the "generalise-first" target the
> triage named (the index-general invariant identity) *already exists in the same file* as
> `invar_normEDS` — so there is nothing to generalise *to*; the open question is instead one of
> grain/policy (ship as a `private` helper inside a mathlib EDS PR vs keep project-internal vs
> dedup the cross-project duplicate), which is exactly the BORDERLINE shape.

---

### Baseline (Phase 0)
- lake build:               not re-run (local build stale, per task note); the decl is read directly from committed source and elaborates in-tree. Assessment reasons from the source statement.
- decl `invar₂_normEDS`:     ✓ resolved at `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:1491`
- qualified name:            **`invar₂_normEDS`** (top-level — VERIFIED). At line 1491 we are inside `@[expose] public section` (l.81) → `section NormEDS` (l.881, a *section*, no prefix) → an anonymous `section` (l.1462). The enclosing `namespace EllSequence` blocks (ll.90–597 and ll.1356–1431) and `namespace IsEllSequence` (ll.643–702) are all CLOSED before line 1491. No namespace prefix. The prompt's parse is correct.
- kind:                      `lemma` (preceded by `omit ellW ellU in` and `open MvPolynomial Param in`)
- has sorry:                 no
- module docstring summary:  "Elliptic divisibility sequences" — defines EDS and constructs normalised EDSs from initial terms. This file is a **heavily-extended fork** of `Mathlib.NumberTheory.EllipticDivisibilitySequence` (same author, David Kurniadi Angdinata): it re-defines `IsEllSequence`/`normEDS`/`complEDS`/… from scratch (the file does NOT import the mathlib EDS file) and adds the `invarNum`/`invarDenom` invariant apparatus + `net`/`rel₄`/`universalNormEDS` to PROVE results that mathlib's EDS file lists as open TODOs.

```lean
omit ellW ellU in
open MvPolynomial Param in
lemma invar₂_normEDS {m : ℤ} :
    invarNum (normEDS b c d) 1 m * c = invarDenom (normEDS b c d) 1 m * (d + b ^ 4) := by
  have := congr(aeval (Param.rec b c d) $(invar₂_normEDS_of_mem_nonZeroDivisors
    (c := X Param.C) (d := X D) (mem_nonZeroDivisors_of_ne_zero <| X_ne_zero (R := ℤ) B) m))
  rw [← universalNormEDS] at this
  simp only [map_mul, map_invarNum, map_invarDenom, map_add, map_pow, aeval_X] at this
  rwa [show (⇑(aeval fun t ↦ Param.rec b c d t) ∘ universalNormEDS) =
    normEDS b c d from funext fun n ↦ by simp [universalNormEDS, map_normEDS, aeval_X]] at this
```

---

### Statement (Phase 1)

`invar₂_normEDS` states that for a normalised elliptic divisibility sequence `W = normEDS b c d` over a commutative ring `R`, and for every integer `m`:

> invarNum(W, 1, m) · c = invarDenom(W, 1, m) · (d + b⁴)

where (file-local definitions, `EllSequence` namespace):
- `invarNum W s n = (W(n+2s)·W(n−s)² + W(n+s)²·W(n−2s))·W(s)² + W(n)³·W(2s)²`  (l.140)
- `invarDenom W s n = W(n+s)·W(n)·W(n−s)`  (l.145)

Mathematically: the "invariant" `invarNum(s,·)/invarDenom(s,·)` of an EDS is, for fixed `s`, independent of the index — a cross-ratio-type invariant (sibling lemma `invar_normEDS`, l.1478, proves `invarNum(s,m)·invarDenom(s,n) = invarNum(s,n)·invarDenom(s,m)`). This lemma pins the *value* of that invariant at `s = 1` by evaluating it at the anchor index `n = 2`, where `invarNum(1,2) = (d+b⁴)·b` and `invarDenom(1,2) = c·b` (lemmas `invarNum_normEDS_two`, `invarDenom_normEDS_two`); cancelling the common factor `b` (a non-zero-divisor) gives the cross-multiplied identity with the constants `c` and `d + b⁴`.

Variables / typeclasses (Lean side):
- `{R : Type u} [CommRing R]` — ambient commutative ring
- `(b c d : R)` — the three normalising parameters of `normEDS`
- `{m : ℤ}` — implicit running index

Hypotheses: none beyond the ambient ring. The `b ∈ R⁰` non-zero-divisor hypothesis is used only in the `private` helper `invar₂_normEDS_of_mem_nonZeroDivisors` (l.1484); the public lemma removes it via a universal `MvPolynomial.aeval`-transfer over `ℤ[B,C,D]`, where the indeterminate `B` is itself a non-zero-divisor (`universalNormEDS`).

Conclusion (math): `invarNum(1,m)·c = invarDenom(1,m)·(d + b⁴)` for all `m`.
Conclusion (Lean): `invarNum (normEDS b c d) 1 m * c = invarDenom (normEDS b c d) 1 m * (d + b ^ 4)`.

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: a corollary/specialisation of `invar_normEDS` at the fixed indices `s = 1, n = 2`. Not a `## Main statement` (the file's main statement is `isEllDivSequence_normEDS`), not named after a person/place, introduces no structure. Intermediate scaffolding. (Lit width still EXHAUSTIVE per skill; BIG/SMALL is narrative only.)

### One-line check (Phase 2b)

Kind is `lemma`, not `def`/`abbrev`/`structure` → **n/a**. (Body is a 6-line `aeval`-transfer proof, not a definitional one-liner.)

---

### Literature search — EXHAUSTIVE protocol (Phase 3)

| #  | Channel | Query | Hit? | Standard form found | Notes |
|----|---------|-------|------|---------------------|-------|
|  1 | WebSearch (specific form) | "EDS invariant Ward W(n+s)W(n−s) normalized numerator denominator" | partial | EDS recurrence; canonical height; σ-form `W_n = σ(nz)/σ(z)^{n²}` | Wikipedia "Elliptic divisibility sequence"; arXiv math/0402415 (Silverman–Stephens). NO named `invarNum/invarDenom`. |
|  2 | WebSearch (general / named-after) | "Nagell-Lutz EDS division polynomial b c d invariant d+b^4 Lean mathlib" | partial | mathlib `normEDS b c d`; division polys ψₙ/φₙ/ωₙ | Confirms the `normEDS b c d` framing is Angdinata's mathlib formalisation. NO standalone `invar₂` identity. |
|  3 | WebSearch (aliases) | "elliptic net invariant cross-ratio Stange Shipsey division polynomial relation" | partial | elliptic nets (Stange); Shipsey thesis | net relations exist; this particular `invarNum/invarDenom` quotient is not a named net invariant. |
|  4 | ChatGPT MCP | self-contained Q1/Q2 (is invarNum/invarDenom named? is the s=1,n=2 identity standalone?) | **n/a — MCP DOWN** (Codex exec failed, as the task warned) | — | Fell back to source reasoning + the three WebSearches + the direct mathlib grep, jointly conclusive. |
|  5 | Local references | `projects/NagellLutz/.mathlib-quality/references/` | n/a | directory absent | only `overview/` exists under `.mathlib-quality/`; recorded n/a. |
|  6 | nLab | "elliptic divisibility sequence" | n/a | — | no EDS / Ward-invariant page; not a categorical concept. |
|  7 | nCatLab | — | n/a | — | not a categorical concept. |
|  8 | Stacks Project | — | n/a | — | EDS recurrence identities are out of Stacks' scope (schemes/stacks). |
|  9 | MathOverflow / MathSE | "elliptic divisibility sequence invariant independent of index" | partial | EDS invariants / periodicity discussion | no named `invarNum/invarDenom` quotient; consistent with #1–3. |
| 10 | recent arXiv (≤5 yr) | "recurrence relation elliptic divisibility sequence" (arXiv 2102.07573) | partial | recurrence-relation papers | none isolates this `s=1,n=2` constant-pinning identity as a result. |

### Literature summary (Phase 3)

Concept identified as: the **canonical "invariant" of an EDS** — the fact that a numerator/denominator ratio is index-independent. The underlying mathematics (EDS recurrence, invariants, σ-function form) is classical (Ward's *Memoir*; Silverman–Stephens; Stange's elliptic nets; Shipsey's thesis).
Sources agree on a standard form: **no** — there is no *standard named* `invarNum`/`invarDenom` object. The closed-form quotient as packaged here is **bespoke proof scaffolding** introduced by this formalisation (Angdinata) to drive the EDS proofs; the literature uses the recurrence directly.
Most general standard form: the EDS recurrence itself (`Rel₃`/`net`) is the literature object; `invarNum/invarDenom` are derived helpers.
Generality dimensions where the literature varies: ring of definition (ℤ vs general `CommRing` — the file already takes a general `CommRing`); index set (ℤ, already maximal).
Disagreement with the literature: none on the mathematics; the literature simply does not isolate THIS lemma (the `s=1,n=2` constant-pinning identity) as a named result — it is an internal step.

---

### Generality analysis (Phase 4)

Literature-standard form (Phase 3): no literature-standard form of THIS identity to weaken against; the parent object (the EDS recurrence / the index-general invariant) is already at full ring generality in the file.

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason |
|---|------------------------|-------------------|--------------------------|---------------------|--------|
| 1 | `[CommRing R]` | commutative ring | comm. ring (Ward over ℤ; mathlib EDS over any `CommRing`) | NO | already maximal — `normEDS`/`invarNum`/`invarDenom` defined for any `CommRing`; the proof is a polynomial identity, universal over `ℤ[B,C,D]`. Commutativity is intrinsic (the recurrence is symmetric). |
| 2 | `(b c d : R)` | three free ring elements | three free parameters | NO | these ARE the defining data of `normEDS`. |
| 3 | `{m : ℤ}` | integer index | integer index | NO | already maximal (ℤ). |
| 4 | fixed `s = 1, n = 2` | the two anchors hard-coded | — | n/a | not hypotheses to weaken — they are the *content* of the specialisation. Generalising the indices back to variables just recovers the already-existing `invar_normEDS`. |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL** in its free parameters `R, b, c, d, m`. It is a deliberate specialisation in the *index* arguments `s=1, n=2`, and the more-general index form ALREADY EXISTS in the file as `invar_normEDS`. So "generalise the indices" is not an open action — the general statement is already present; `invar₂_normEDS` is its concrete consequence.
Number of weakening opportunities found: 0.
Cost of restatement: n/a (nothing to restate; the general form already exists separately).

### Modern-idiom check (Phase 4c)

| # | Question | Applies? | Notes |
|---|----------|----------|-------|
| 1 | bundled hyps → typeclasses? | no | the only hyp (`b ∈ R⁰`) is already eliminated via the universal-polynomial transfer; public form is hypothesis-free. |
| 2 | sequences → filters/topology? | no | pure algebraic identity; no limits/topology. |
| 3 | construction → universal property? | no | an equation about a fixed construction, not a construction. |
| 4 | set-with-closure → bundled substructure? | no | no substructures. |
| 5 | field/metric-specific → weakened typeclass? | no | already a `CommRing` identity. |
| 6 | 1-categorical → higher-categorical? | no | no categorical content. |
| 7 | concrete index → general additive structure? | no | index is ℤ, intrinsic to EDS; the `s=1,n=2` constants are the point, not a generalisable index. |
| 8 | concrete-via-abstract (named obj vanishes in proof)? | NO (inverted) | the proof of `invar₂_normEDS` IS the concrete `s=1,n=2` shadow of the abstract `invar_normEDS`; the abstract form already exists and is invoked. No hidden more-general theorem to extract — it is already extracted as `invar_normEDS`. |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no**. A finite algebraic specialisation; the abstract parent (`invar_normEDS`) is already present. No Bourbaki-2.0 reformulation applies.

---

### Diamond / defeq risk (Phase 4.5)

**n/a** — declaration kind is `lemma` (no definitional equalities or typeclass-search paths introduced).

---

### Mathlib search-status: `invar₂_normEDS` (Phase 5)

[A] Lean-Finder       — no MCP/index tool available in this environment   n/a: tool absent (deferred-tool search returned none)
[B] Loogle            — no Loogle tool available                          n/a: tool absent
[C] LeanSearch        — no LeanSearch tool available                      n/a: tool absent
[D] Grep mathlib src  `invarNum`/`invarDenom`/`redInvar`/`invar_normEDS`/`invar₂`/`def invar`/`theorem invar`b/`lemma invar`b over `.lake/packages/mathlib/Mathlib/`   **no hits.** The only `invar*` in mathlib are unrelated: `Analysis/Normed/Unbundled/InvariantExtension.invariantExtension` (algebra norms), `RepresentationTheory/Invariants.invariants`, `MeasureTheory/MeasurableSpace/Invariants.invariants` — none about EDS.
[E] Name pattern      grep `net` / `rel₄` / `universalNormEDS` over mathlib   **no hits** — the ENTIRE proof apparatus (`net`, `rel₄`, `universalNormEDS`, `invarNum`, `invarDenom`, `invar_of_net`, `invar_normEDS`) is ABSENT from mathlib.

Searched for both:
  - the user's current form (`invar₂_normEDS`) — absent.
  - the parent/general form (`invar_normEDS`, and the whole `invarNum/invarDenom` invariant) — absent.

Decisive context: mathlib's `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean` (lines 44–45) carries exactly the two open TODOs this invariant machinery exists to discharge:
```
* TODO: prove that `normEDS` satisfies `IsEllDivSequence`.
* TODO: prove that a normalised sequence satisfying `IsEllDivSequence` can be given by `normEDS`.
```
Neither this lemma nor its supporting apparatus is in mathlib; mathlib's EDS file is a definitions-only stub for exactly this territory.

Concluded: **not in mathlib** (grep methods exhausted over both forms; index/MCP search tools unavailable in this environment, recorded n/a).

---

### Composition check (Phase 6)

### 6.0 — Call sites of `invar₂_normEDS`

Internal use count (NagellLutz, excluding the declaring file): **0**.
External-to-file callers: **0 distinct files**.
Only in-file use: line 1504, inside `private redInvar_normEDS_of_mem_nonZeroDivisors`, which feeds `redInvar_normEDS` (l.1509), which is consumed by `projects/NagellLutz/LutzNagell/DivisionPolynomialOmega.lean:84` (the ω-division-polynomial construction).

| Caller file:line | Usage pattern |
|------------------|---------------|
| EllipticDivisibilitySequence.lean:1504 (same file, `private` helper) | `… ← invarNum_eq_redInvarNum_mul, invar₂_normEDS, invarDenom_eq_redInvarDenom_mul …` |

Inline-derivation grep: not re-derived inline elsewhere in NagellLutz.

**Cross-project duplicate (load-bearing).** The identical lemma exists in the HasseWeil project at `projects/HasseWeil/HasseWeil/Auxiliary/EllipticDivisibilitySequence.lean:973` (private helper :965; downstream `redInvar_normEDS` :997 → `DivisionPolynomial.lean:104`). So the lemma is **duplicated verbatim across two AINTLIB projects** that each fork the same mathlib EDS file — strong evidence it is shared *forked* infrastructure, NOT a one-off, and NOT yet in mathlib (else both forks would import it).

Call-sites signal: **K = 0 external uses, single in-file `private` consumer, plus a cross-project verbatim duplicate.** Pattern = "internal scaffolding inside a larger development", not standalone API.

### 6a — Composition attempt

Can `invar₂_normEDS` be derived from **mathlib** in ≤3 chained calls? **No.**

Attempt 1: the proof is `invar_normEDS 1 m 2` (project-local general invariant) + `simp only [invarNum_normEDS_two, invarDenom_normEDS_two]` + `mul_cancel_right_mem_nonZeroDivisors` (mathlib) + a universal `MvPolynomial.aeval` transfer over `ℤ[B,C,D]`.
  - Mathlib decls used: `mul_cancel_right_mem_nonZeroDivisors`, `mem_nonZeroDivisors_of_ne_zero`, `MvPolynomial.X_ne_zero`, `aeval`, `map_*`. **The load-bearing steps all go through PROJECT-LOCAL lemmas** (`invar_normEDS`, `invarNum_normEDS_two`, `invarDenom_normEDS_two`, `universalNormEDS`) that **do not exist in mathlib**.
  - Result: **fails as a mathlib-only composition** — the essential input `invar_normEDS` (resting on `invar_of_net`/`net_normEDS`/`universalNormEDS`) is absent from mathlib.

Conclusion: **NOT-COMPOSABLE** from mathlib primitives. Composable only from this project's own EDS invariant apparatus.

---

## Verdict: `invar₂_normEDS`

**Category:** **BORDERLINE-needs-human**

**Evidence:**
- Literature search (Phase 3): the EDS invariant idea is classical (Ward / Silverman–Stephens / Stange / Shipsey), but there is **no named `invarNum/invarDenom` object** and **no standalone `s=1,n=2` constant-pinning identity** in the literature. ChatGPT MCP was down; three WebSearches + the direct mathlib grep are jointly conclusive.
- Generality analysis (Phase 4): MAXIMALLY GENERAL in free params; the index-general parent `invar_normEDS` already exists in-file; no modern-idiom reformulation (4c all `no`).
- Mathlib search (Phase 5): **not in mathlib** — neither the lemma, its parent invariant, nor any apparatus (`net`/`rel₄`/`universalNormEDS`); mathlib's EDS file is a stub carrying the matching TODOs (ll.44–45).
- Composition check (Phase 6): **NOT-COMPOSABLE** from mathlib (the essential input `invar_normEDS` is project-local); **K = 0** external call sites; **verbatim duplicate** in HasseWeil.

**Rationale (why BORDERLINE, not a clean bucket):**

Two facts pull in opposite directions, and resolving them is a human judgment about *grain and policy*, not something the evidence settles. (1) On its own, `invar₂_normEDS` is **not mathlib-worthy as a standalone lemma**: it is a fixed-index (`s=1, n=2`) specialisation of `invar_normEDS`; it has zero external consumers (its sole user is a same-file `private` helper, two links up the chain to the ω-division-polynomial construction); the literature gives it no independent standing; and it exists verbatim in two projects as forked scaffolding. That profile (`K=0`, specialisation, private-flavoured, duplicated) is the textbook NO-composable / internal-helper signature. (2) **But** the standard NO buckets do not fit: `NO-mathlib-has-it` is false (mathlib has nothing here — it has the *open TODOs*), and `NO-composable-from-mathlib` is false too (the proof's load-bearing step `invar_normEDS` is project-local and absent from mathlib, so there is no ≤3-call mathlib composition and nothing to "inline at the call site"). Deleting the lemma and replacing its one call site with mathlib is therefore **impossible** — the usual NO-bucket refactor action cannot be carried out, which is precisely why a flat NO verdict would be wrong.

What makes this genuinely BORDERLINE is that the lemma's *parent development is squarely mathlib-targeted*: this whole `invarNum/invarDenom` + `net` + `universalNormEDS` apparatus is exactly the machinery needed to close mathlib's two long-standing EDS TODOs ("prove `normEDS` satisfies `IsEllDivSequence`" and its converse). If that apparatus is upstreamed as a unit (the natural, valuable move — by the very author of the mathlib file), then `invar₂_normEDS` should ride along **as a `private`/internal helper of that PR**, not as a public mathlib lemma and not as an independent contribution. Whether to upstream now, and at what internal/public granularity, is a maintainer decision (and a dedup decision: the NagellLutz/HasseWeil duplication should be unified into AINTLIB `Common/` regardless of the mathlib question). The skill must not silently pick "YES, ship this lemma" vs "NO, it's just a helper" — that is the human call, so the verdict is BORDERLINE with the questions spelled out.

**Numbered questions for the human (≤5):**

1. Do you intend to upstream the project's EDS **invariant apparatus** (`invarNum`/`invarDenom`/`invar_of_net`/`invar`/`net`/`rel₄`/`universalNormEDS`/`invar_normEDS`/`redInvar_normEDS`) to mathlib to discharge the two open TODOs in `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean` (ll.44–45)? (yes → `invar₂_normEDS` ships *inside* that PR; no → it stays project-internal.)
2. If yes to (1): should `invar₂_normEDS` (and its private helper `invar₂_normEDS_of_mem_nonZeroDivisors`) be **`private`/internal** to that mathlib file rather than a public-API lemma? (It has no standalone use; it is two links up from the ω-division-polynomial construction.)
3. The lemma is **duplicated verbatim** in NagellLutz and HasseWeil (both fork the same mathlib EDS file). Independently of mathlib, should the shared fork be lifted into an AINTLIB `Common/` module so the two copies don't drift? (This is a `/cleanup` dedup action, not a mathlib action.)
4. Is the `s=1, n=2` specialisation reused anywhere beyond the `redInvar_normEDS` → ω-division-polynomial chain (e.g. in the Nagell–Lutz reduction proof proper)? If it is genuinely single-use, do you prefer to **inline** it into `redInvar_normEDS_of_mem_nonZeroDivisors` rather than keep a named lemma? (yes-inline → drop the name even in-project.)
5. Naming: if it does go to mathlib, the subscript-`₂` name `invar₂_normEDS` is opaque out of context — would you prefer a descriptive name tying it to the constant it pins (e.g. `normEDS_invar_one_eq` / `invar_normEDS_one`)?

**Next action:** human answers Q1–Q5. Most likely resolution: **Q1 = yes** (the apparatus closes real mathlib TODOs and is by the mathlib file's own author) ⇒ `invar₂_normEDS` is **upstreamed as a `private` helper inside that EDS PR** (not as a standalone public lemma) ⇒ re-run `/mathlibable` on the *parent* results (`isEllDivSequence_normEDS` and the `invarNum/invarDenom` invariant) as the real upstreaming units. Orthogonally, run `/cleanup` to dedup the NagellLutz/HasseWeil copies into `Common/`.
