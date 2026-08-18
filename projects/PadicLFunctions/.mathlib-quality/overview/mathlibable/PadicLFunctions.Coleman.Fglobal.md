# `/mathlibable` report — `PadicLFunctions.Coleman.Fglobal`

**Final verdict: `NO-composable-from-mathlib`** — `Fglobal p n` is a sealed one-line
alias, definitionally equal to the mathlib primitive `ℚ⟮zetaSys p n⟯`
(`IntermediateField.adjoin ℚ {zetaSys p n}`). Mathlib deliberately uses this bare term
rather than a named definition; the cyclotomic structure on it is supplied by
`IsPrimitiveRoot.intermediateField_adjoin_isCyclotomicExtension`. No new lemma or def is
warranted for mathlib. (As a *project-local* readability anchor — mirroring the existing
local `K p n = ℚ_[p]⟮zetaSys p n⟯` — the def is fine and should stay in the project; it is
simply not a mathlib contribution.)

Mode: A (single declaration, full 10-phase workflow with the exhaustive multi-channel
literature search).

---

### Baseline (Phase 0)
- lake build:               build not re-run (stale/slow per task note); **reasoned from source** — declaration and all dependencies read directly.
- decl `PadicLFunctions.Coleman.Fglobal`:  ✓ resolved at `projects/PadicLFunctions/PadicLFunctions/Iwasawa/CyclotomicUnits.lean:42`
- kind:                      `def` (`noncomputable`, not `@[reducible]`)
- has sorry:                 no
- module docstring summary:  Cyclotomic units — the global modules 𝒟_n and their local closures 𝒞 (RJW §11.3); sets up the global fields `F_n = ℚ(μ_{p^n})` and `F_n⁺` inside `ℂ_[p]`, the global units `𝒱_n`, the cyclotomic units `𝒟_n`, and the local closure towers.

---

### Statement (Phase 1)

`PadicLFunctions.Coleman.Fglobal` is **a definition of** the following:

For a prime `p` and `n : ℕ`, `Fglobal p n` is the cyclotomic field `F_n = ℚ(μ_{p^n}) = ℚ(ξ_{p^n})`
— the subfield of `ℂ_p` generated over `ℚ` by a fixed primitive `p^n`-th root of unity
`ξ_{p^n} = zetaSys p n`. It is the standard cyclotomic number field, realized concretely as an
`IntermediateField ℚ ℂ_[p]` (the project works inside the single ambient field `ℂ_p`; "decomposition
replan R11.7"). Mathematically this is just `ℚ` adjoined a primitive root of unity.

Variables / typeclasses involved (Lean side):
- `p : ℕ`, `[hp : Fact p.Prime]` — the fixed prime (section variables).
- `n : ℕ` — the level; the root of unity has order `p^n`.

Hypotheses (Lean side): none (it is a plain definition; no hypotheses).

Conclusion (math): the cyclotomic field `ℚ(ζ_{p^n})`, as a subfield of `ℂ_p`.

Conclusion (Lean): `IntermediateField ℚ ℂ_[p]` — definition; body is `ℚ⟮zetaSys p n⟯`, i.e.
`IntermediateField.adjoin ℚ {zetaSys p n}`.

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: a one-line concrete realization of a standard object as an `IntermediateField`; not a new
mathematical structure (the structure `IntermediateField` is mathlib's), not a named "main result",
not a theorem named after a person/place. It is a notational/anchoring `def`.

(Literature width was EXHAUSTIVE regardless; BIG/SMALL is recorded for framing only.)

### One-line check (Phase 2b)

Body line count: **1 substantive line** (`ℚ⟮zetaSys p n⟯`).
One-liner verdict: **ONE-LINER** (kind is `def`).

Exemption check:

| Exemption                         | Applies? | Evidence |
|-----------------------------------|----------|----------|
| Avoid defeq abuse                 | no  | The def is sealed but is *not* a defeq barrier protecting a fragile downstream proof. The two `rw [Fglobal]` sites (`CyclotomicUnits.lean:144`, `Generators.lean:1078`) *unfold* the alias to reach `IntermediateField.adjoin_induction`; with the bare term `ℚ⟮zetaSys p n⟯` no unfolding `rw` would be needed at all. The seal hinders, not helps. |
| Avoid typeclass diamonds          | no  | No competing instances. `IntermediateField ℚ ℂ_[p]` membership / `SetLike` / `inv_mem` / `algebraMap_mem` are the single generic mathlib instances. |
| Mark semantic intent / API name   | yes (weak, project-internal only) | The name reads as "the field `F_n`" and pairs with the local analogue `K p n = ℚ_[p]⟮ζ⟯` (`Coleman/Tower.lean:98`), aiding the §11.3 narrative. **But this is a project-internal convenience**: mathlib's own convention is to *not* name this object (it uses the bare `IntermediateField.adjoin ℚ {ζ}` term throughout `Mathlib/NumberTheory/Cyclotomic/`). The API-name exemption is for stable mathlib surface; here mathlib's surface is the bare term. |

Conclusion: **ONE-LINER WITHOUT-EXEMPTION** (for mathlib purposes — the only applicable reason is a
project-internal readability anchor, which does not justify a mathlib addition).

Carried into Phase 7: the verdict is biased toward `NO-composable-from-mathlib` /
`NO-mathlib-has-it`.

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query | Hit? | Standard form found | Notes |
|----|----------------------------------|-------|------|---------------------|-------|
|  1 | WebSearch (specific form)        | "cyclotomic field Q(zeta_n) definition adjoin primitive root of unity standard" | yes | `ℚ(ζ_n)` = ℚ adjoined a primitive `n`-th root of unity | Wolfram MathWorld, Encyclopedia of Math, Stanford (B. Conrad), Durham Galois-theory notes — unanimous |
|  2 | WebSearch (general / Iwasawa form)| "cyclotomic field as subfield generated by root of unity inside complex numbers Q(mu_p^n) Iwasawa theory" | yes | `ℚ(μ_{p^n})` realized as a subfield of `ℂ`, generated by primitive `p^n`-th roots | Hida (UCLA) "Elementary Iwasawa Theory", Coates–Sujatha *Cyclotomic Fields and Zeta Values* — exactly the RJW §11.3 setting |
|  3 | WebSearch (named-after / aliases)| "Stacks project cyclotomic extension adjoin roots of unity" | yes | "cyclotomic extension `K(ζ_n)`; adjoining one primitive root = adjoining all `n`-th roots" | Keith Conrad, Buzzard (Imperial M3P11), Garrett (Minnesota); confirms `K(ζ)=K(μ_n)` |
|  4 | ChatGPT MCP                      | (intended: standard form + generality + historical evolution) | n/a | — | **No ChatGPT/OpenAI MCP server configured in this environment** (ToolSearch found none). Compensated by 4 extra web sources (rows 1–3, 9–10) covering the same ground (standard form, generality over a base field, historical/ambient realization). |
|  5 | Local references                 | grep `.mathlib-quality/references/` and `refs/PadicLFunctions/` for "cyclotomic" | n/a | (no references dir) | `projects/PadicLFunctions/.mathlib-quality/references/` absent; `refs/PadicLFunctions/` absent. Recorded n/a. The source paper is RJW arXiv:2309.15692 (cited in-file). |
|  6 | nLab                             | "cyclotomic field" | yes | "a field extension `𝔽(ζₙ)` by a primitive root of unity ζₙ; default `𝔽 = ℚ`" | ncatlab.org/nlab/show/cyclotomic+field. **nLab gives no separate named notion for "the subfield of ℂ generated by ζ"** — it is just "adjoin a root of unity". |
|  7 | nCatLab (categorical)            | (same page) | n/a | — | Not a categorical concept; the nLab entry (row 6) is purely the field-theoretic definition. No higher-categorical form. |
|  8 | Stacks Project                   | (via row 3) | partial | Tag 09F2 / 0GY2: roots of unity, `w = 1 − ζ` for primitive `p`-th `ζ` | Stacks treats cyclotomic material in commutative-algebra terms (rings adjoining roots of unity); no separate "cyclotomic subfield of an ambient field" object. Consistent with the adjoin formulation. |
|  9 | MathOverflow / Math.StackExchange| (covered by rows 1–3 web sweep) | yes | same as rows 1–3 | The "adjoin a primitive root of unity to `ℚ`" definition is universal; no competing standard form surfaced. |
| 10 | recent arXiv (last 5 years)      | (rows 1–2 returned arXiv hits) + RJW arXiv:2309.15692 | yes | RJW §9 / §11.3 uses exactly `F_n = ℚ(μ_{p^n})` ⊂ ambient `ℂ_p` | The source paper itself (TeX 2471) writes `F_n = ℚ(μ_{p^n})`; modern Iwasawa-theory arXiv papers use the same realization-inside-a-`p`-adic-field convention |

Protocol pass check:
- WebSearch ran **4** distinct queries at different generality levels (specific `ℚ(ζ_n)`; Iwasawa `ℚ(μ_{p^n})⊂ℂ`; aliases/Stacks; nLab) — ✓ (≥3).
- ChatGPT MCP: **n/a — server not configured**; compensated with extra web channels. ✓ (documented).
- Local references: checked, absent → n/a with reason. ✓
- nLab: checked. ✓
- Stacks / nCatLab / MathOverflow / arXiv: each checked or recorded n/a with reason. ✓

### Literature summary (Phase 3)

Concept identified as: **the cyclotomic field `ℚ(ζ_{p^n}) = ℚ(μ_{p^n})`** (in Iwasawa theory: the
`n`-th layer `F_n` of the cyclotomic tower, realized as a subfield of an ambient field — here `ℂ_p`).
Sources agree on the standard form: **yes** — `K(ζ)` = base field adjoined a primitive root of unity,
default `K = ℚ`; adjoining one primitive root = adjoining all roots (so `K(ζ_n) = K(μ_n)`).
Most general standard form: **`K(ζ)` for `K` any field and `ζ` a primitive root of unity** (nLab: arbitrary
base 𝔽). The realization "inside `ℂ_p`" is a *choice of ambient field*, not part of the abstract object.
Generality dimensions where the literature varies:
  - base field: from `ℚ` (default) up to an arbitrary field `K` (nLab, Stacks, Keith Conrad all general).
  - realization: abstract field vs. concrete subfield of `ℂ` (classical) / of `ℂ_p` (Iwasawa-theoretic) — a presentation choice.
Disagreement with the literature: **none.** `Fglobal p n = ℚ(ζ_{p^n})` *is* the standard object; the
only specialization is fixing `K = ℚ`, the ambient field `ℂ_p`, and the specific generator `zetaSys p n`.

---

### Generality analysis — `PadicLFunctions.Coleman.Fglobal`

Literature-standard form (from Phase 3): `K⟮ζ⟯ = IntermediateField.adjoin K {ζ}` for an arbitrary base
field `K` and primitive root of unity `ζ` — which is **exactly the mathlib primitive** `Fglobal`'s body
is built from.

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason it can/can't be weakened |
|---|------------------------|-------------------|--------------------------|---------------------|----------------------------------|
| 1 | base field `ℚ`          | `ℚ` (fixed)       | any field `K`            | yes                 | `IntermediateField.adjoin K {ζ}` works for any `K`; here `ℚ` is the literature default. Generalizing would just reproduce the mathlib primitive `K⟮ζ⟯`. |
| 2 | ambient field `ℂ_[p]`   | `ℂ_[p]` (fixed)   | any field extension containing `ζ` | yes | `K⟮ζ⟯` is generic in the ambient field. `ℂ_[p]` is the project's working choice. |
| 3 | generator `zetaSys p n` | a specific chosen primitive `p^n`-th root | any primitive root of unity `ζ` | yes | `K⟮ζ⟯` accepts any element. The cyclotomic structure needs `IsPrimitiveRoot`, supplied separately. |

### Generality verdict (Phase 4b)

The current form is: **STRICTLY NARROWER THAN STANDARD** — but the "general form" is not a new object;
it is the bare mathlib term `K⟮ζ⟯ = IntermediateField.adjoin K {ζ}`, which mathlib already provides and
deliberately leaves un-named.
Number of weakening opportunities found: 3 (base field, ambient field, generator) — each of which simply
recovers the existing mathlib primitive.
Proposed restatement: n/a as a mathlib *addition* — fully generalizing `Fglobal` yields `K⟮ζ⟯`, which is
not a definition to add (it is mathlib's `IntermediateField.adjoin`). This pushes the verdict to a NO
bucket, not `YES-but-generalise-first`.
Cost of restatement: n/a.

### Modern-idiom check (Phase 4c)

| #  | Question | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|----------|----------|------------------------|----------------------------------|
|  1 | "let X be a foo" preamble → typeclass/instance? | no | — | Already a bundled `IntermediateField`; the cyclotomic structure is the typeclass `IsCyclotomicExtension {p^n} ℚ (ℚ⟮ζ⟯)`, available via `IsPrimitiveRoot.intermediateField_adjoin_isCyclotomicExtension`. |
|  2 | sequences/metric → filters/topological? | no | — | No limit/convergence content; it is a single field. |
|  3 | explicit construction → universal-property class? | yes (already done in mathlib) | Use mathlib's `IsCyclotomicExtension` class as the characterization, on the bare `ℚ⟮ζ⟯`. | This is precisely why `Fglobal` need not be a named def: mathlib already has the universal-property class layered on the bare adjoin term. |
|  4 | set-with-closure-predicate → bundled substructure? | no (already bundled) | — | `IntermediateField` is the bundled substructure already. |
|  5 | vector-space/field-specific → weaker typeclass? | no | — | `IntermediateField.adjoin` is already at the right (field) generality. |
|  6 | 1-categorical → higher-categorical? | no | — | Not applicable to a number field. |
|  7 | concrete index (ℕ/ℤ/ℝ) → arbitrary monoid/group? | no | — | The level `n` indexes order `p^n`; intrinsic to the cyclotomic tower, not a spurious concrete index. |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **yes — and mathlib already implements it**, which counts *against* adding
`Fglobal`. The contemporary mathlib formulation of "the cyclotomic field inside an ambient field" is the
bare term `ℚ⟮ζ⟯ = IntermediateField.adjoin ℚ {ζ}` carrying the `IsCyclotomicExtension {p^n} ℚ` instance
(`IsPrimitiveRoot.intermediateField_adjoin_isCyclotomicExtension`, `Mathlib/NumberTheory/Cyclotomic/Basic.lean:491`).
There is no modernisation `Fglobal` would *contribute* — the modern form is the thing it wraps. So this
does **not** flip the verdict to `YES-but-generalise-first` (no real downstream-organisation improvement
to mathlib results from naming the wrapper).

---

### Diamond / defeq risk — `PadicLFunctions.Coleman.Fglobal` (Phase 4.5; kind = `def`)

| # | Risk | Verdict | Evidence / rationale |
|---|------|---------|----------------------|
| 1 | Typeclass diamond | none | Returns an `IntermediateField ℚ ℂ_[p]` term; introduces no instances. |
| 2 | Reducibility leak | none | Not `@[reducible]`. Body is a single `IntermediateField.adjoin` application; sealing is harmless. |
| 3 | Non-canonical unfolding | low | `simp`/`rfl` will not spontaneously unfold a sealed `def`; consumers unfold explicitly via `rw [Fglobal]` (2 sites). Predictable. |
| 4 | Instance priority collision | n/a | Not an `instance`. |
| 5 | Universe-polymorphism issues | none | Monomorphic (`ℚ`, `ℂ_[p]` fixed); no universe annotation forced. |
| 6 | Coercion ambiguity | none | Uses the standard `IntermediateField`→`Set`/`SetLike` coercion only; no bespoke `CoeFun`/`CoeSort`. |

### Risk verdict (Phase 4.5)

Overall risk: **NONE**. (Does not affect the verdict; recorded as required for a `def`.)

---

### Mathlib search-status: `PadicLFunctions.Coleman.Fglobal`

[A] Lean-Finder       n/a — Lean-Finder MCP not available in this environment; substituted by [D]+[E] over the local mathlib tree.
[B] Loogle            type-pattern `IntermediateField _ _`, `IsPrimitiveRoot _ _ → IntermediateField _ _` (reasoned over local src; Loogle MCP not available) — no *named* `cyclotomic IntermediateField` def; the term `IntermediateField.adjoin K {ζ}` is the match.
[C] LeanSearch        n/l "cyclotomic field as intermediate field adjoin root of unity" (LeanSearch MCP not available; substituted by [D]) — see [D].
[D] Grep mathlib src  searched `.lake/packages/mathlib/Mathlib/`:
      - `def CyclotomicField` → `Mathlib/NumberTheory/Cyclotomic/Basic.lean:655` — `CyclotomicField n K := (cyclotomic n K).SplittingField` (a *splitting-field construction*, NOT an in-ambient subfield).
      - `IntermediateField.adjoin K {ζ}` cyclotomic API → `Basic.lean:491` `IsPrimitiveRoot.intermediateField_adjoin_isCyclotomicExtension`, `:522` `IntermediateField.isCyclotomicExtension_adjoin_of_exists_isPrimitiveRoot`, `:470` `IsPrimitiveRoot.adjoin_isCyclotomicExtension`.
      - `rationalCyclotomic*` / `cyclotomicSubfield` / `def …cyclotomic… IntermediateField` → **no hits** (mathlib has no named in-ambient cyclotomic subfield def).
[E] Name pattern      grep `def .*Cyclotomic`, `Fglobal`, `cyclotomicField`, `AdjoinSimple.gen` — only `CyclotomicField`/`CyclotomicRing` (splitting-field/ring constructions); the in-ambient object is the bare `K⟮ζ⟯` term + instance.

Searched for both:
  - the user's current form (`ℚ⟮zetaSys p n⟯` inside `ℂ_p`) — matches the bare term `IntermediateField.adjoin ℚ {ζ}`.
  - the literature-standard form (`K⟮ζ⟯`, any base/ambient) — same bare term; cyclotomic structure via `IsPrimitiveRoot.intermediateField_adjoin_isCyclotomicExtension`.

Concluded: **found building blocks** — mathlib has `IntermediateField.adjoin ℚ {·}` (notation `ℚ⟮·⟯`,
`Mathlib/FieldTheory/IntermediateField/Adjoin/Defs.lean:526`) plus the cyclotomic-structure theorem
`IsPrimitiveRoot.intermediateField_adjoin_isCyclotomicExtension`. Mathlib has **no named definition** for
"the cyclotomic subfield `ℚ(ζ)` inside an ambient field"; by convention it works with the bare adjoin
term. So `Fglobal` is a 0-step alias of an existing mathlib primitive, not a missing object.

---

### Call sites — `PadicLFunctions.Coleman.Fglobal`

Internal use count: **8** within the declaring file `Iwasawa/CyclotomicUnits.lean` (excluding the def line
42 and the `FglobalPlus`/docstring lines): lines 53, 107, 121, 143, 144, 167, 400, 414.
External-to-file callers: **1 distinct file** — `IwasawaProof/Generators.lean` (lines 240, 1071–1076, 1078,
1092, 1102, 1497; line 1484 is a comment).

| Caller file:line | Usage pattern (one-line excerpt) |
|------------------|----------------------------------|
| CyclotomicUnits.lean:53 | `(Fglobal p n).inv_mem (IntermediateField.mem_adjoin_simple_self ℚ _)` — generic `IntermediateField` API |
| CyclotomicUnits.lean:107 | `(u : ℂ_[p]) ∈ Fglobal p n ∧ …` — membership (in `globalUnits` carrier) |
| CyclotomicUnits.lean:121 | `(Fglobal p n).inv_mem hu.1` — generic API |
| CyclotomicUnits.lean:143–144 | `Fglobal_le_K`: `rw [Fglobal] at hx; … adjoin_induction` — **unfolds the alias** to reach mathlib's `adjoin_induction` |
| CyclotomicUnits.lean:167 | `(Fglobal p n).inv_mem hF` — generic API |
| CyclotomicUnits.lean:399–400, 414 | `cycloUnit_mem_Fglobal … ∈ Fglobal p n` (proved via `mem_adjoin_simple_self`) |
| Generators.lean:240 | `gammaUnit p a n ∈ Fglobal p n` — membership |
| Generators.lean:1071–1102 | `galAut_mem_Fglobal`: `rw [Fglobal] at hy; adjoin_induction …; (Fglobal p n).algebraMap_mem`, `.inv_mem` — **unfolds the alias**, then generic API |
| Generators.lean:1497 | `galAut_mem_Fglobal p a hn hvF hvK` — uses the wrapper lemma |

Inline-derivation grep (was the equivalent re-derived elsewhere without using `Fglobal`?):
  - The two `rw [Fglobal]` sites (CyclotomicUnits.lean:144, Generators.lean:1078) immediately rewrite the
    alias *away* to its definition `ℚ⟮zetaSys p n⟯` so mathlib's generic `IntermediateField.adjoin_induction`
    applies. Every other use is generic `IntermediateField`/`SetLike` API (`∈`, `inv_mem`, `algebraMap_mem`,
    `mem_adjoin_simple_self`, `≤`). No call site uses any *cyclotomic-specific* property that would justify a
    bespoke named object.

Composability signal: ~17 internal+external uses, **but** every use is generic adjoin/`IntermediateField`
API on `ℚ⟮ζ⟯`, and the two unfolding sites show the name is a readability alias (not a defeq barrier). This
is the "wrapper that consumers must unfold to reach the real (mathlib) API" pattern — leans
`NO-composable-from-mathlib`.

### Composition check (Phase 6)

Can `Fglobal p n` be derived from mathlib in ≤3 chained calls?

Attempt 1: `Fglobal p n` is, definitionally, `ℚ⟮zetaSys p n⟯` = `IntermediateField.adjoin ℚ {zetaSys p n}`.
  - Mathlib decls used: `IntermediateField.adjoin` (notation `ℚ⟮·⟯`, `Adjoin/Defs.lean:526`).
  - Result: **succeeds** — 0 chained calls; it is a definitional unfolding (`example : Fglobal p n = ℚ⟮zetaSys p n⟯ := rfl`).
  - Notes: the cyclotomic *structure* (if a consumer wants it) is then `IsPrimitiveRoot.intermediateField_adjoin_isCyclotomicExtension (zetaSys_primitiveRoot p n)` — one further call, supplying `IsCyclotomicExtension {p^n} ℚ (ℚ⟮zetaSys p n⟯)`.

Conclusion: **COMPOSABLE** — `Fglobal p n` *is* `ℚ⟮zetaSys p n⟯` (a 0-call defeq alias of a mathlib
primitive). The composition sketch (just the bare term) is ≤3 lines.

---

## Verdict: `PadicLFunctions.Coleman.Fglobal`

**Category:** `NO-composable-from-mathlib`

**Evidence:**
- Literature search (Phase 3): cyclotomic field = `K(ζ)` = base field adjoined a primitive root of unity (nLab, Wolfram, Encyclopedia of Math, Keith Conrad, Coates–Sujatha, Hida; RJW source writes `F_n = ℚ(μ_{p^n})`). The general object is exactly mathlib's `IntermediateField.adjoin`.
- Generality analysis (Phase 4): STRICTLY NARROWER than `K⟮ζ⟯`, but the "general form" *is* the mathlib primitive — not a new def to add. Phase 4c: the modern idiom (`IsCyclotomicExtension` on the bare `ℚ⟮ζ⟯`) is already in mathlib, so no modernisation contribution.
- Mathlib search (Phase 5): found building blocks — `IntermediateField.adjoin ℚ {·}` (`ℚ⟮·⟯`) + `IsPrimitiveRoot.intermediateField_adjoin_isCyclotomicExtension`; **no named in-ambient cyclotomic subfield def** exists in mathlib (it deliberately uses the bare term).
- Composition check (Phase 6): COMPOSABLE — `Fglobal p n` ≡ `ℚ⟮zetaSys p n⟯` (0-call defeq alias).

**Rationale:**

`Fglobal p n` is, by definition (`rfl`), the mathlib term `ℚ⟮zetaSys p n⟯ = IntermediateField.adjoin ℚ {zetaSys p n}`.
The literature confirms this is precisely the standard cyclotomic field `ℚ(ζ_{p^n})`, and mathlib already
provides the building block (`IntermediateField.adjoin`) together with the cyclotomic-extension structure on it
(`IsPrimitiveRoot.intermediateField_adjoin_isCyclotomicExtension`). Crucially, mathlib makes a *deliberate
convention* of NOT wrapping "the cyclotomic subfield inside an ambient field" in a named definition — across
`Mathlib/NumberTheory/Cyclotomic/` it manipulates the bare `IntermediateField.adjoin K {ζ}` term directly
(its named cyclotomic *constructions* are `CyclotomicField n K`/`CyclotomicRing n A K`, which are splitting-field/
ring objects, a different thing from an in-ambient subfield). Adding `Fglobal` to mathlib would therefore add a
redundant one-line alias for an existing primitive — exactly the case the one-liner gate (Phase 2b: ONE-LINER
WITHOUT-EXEMPTION) is designed to catch. The only argument for the name is project-internal readability (it
mirrors the local `K p n = ℚ_[p]⟮ζ⟯`), and even there the two `rw [Fglobal]` sites show consumers must *unfold*
it to reach mathlib's generic `adjoin_induction` — so the name is a convenience, not a load-bearing defeq
barrier or diamond fix.

**Note on scope.** `NO-composable-from-mathlib` here is a *mathlib* verdict (it does not belong in mathlib as a
def). It is **not** a recommendation to delete `Fglobal` from the AINTLIB project: as a local readability anchor
paired with `K p n`, it is reasonable project code and the `rw [Fglobal]`-then-`adjoin_induction` idiom is fine.
The refactor plan below is what a mathlib-upstreaming pass would do; the project may keep the alias.

**WHY not (refactor-actionable detail):**
- Mathlib has the building block; `Fglobal p n` is a 0-call composition — literally the bare term `ℚ⟮zetaSys p n⟯`.
  When the cyclotomic structure is needed, it is one further call:
  `IsPrimitiveRoot.intermediateField_adjoin_isCyclotomicExtension (zetaSys_primitiveRoot p n)`.

Mathlib building blocks:
- `IntermediateField.adjoin : (K : Type*) → … → Set L → IntermediateField K L`, notation `K⟮·⟯` — `.lake/packages/mathlib/Mathlib/FieldTheory/IntermediateField/Adjoin/Defs.lean:526` (and the surrounding generic API: `mem_adjoin_simple_self:554`, `adjoin_simple_le_iff:583`, `adjoin_induction:478`).
- `IsPrimitiveRoot.intermediateField_adjoin_isCyclotomicExtension` — `.lake/packages/mathlib/Mathlib/NumberTheory/Cyclotomic/Basic.lean:491` (gives `IsCyclotomicExtension {n} K (K⟮ζ⟯)`).

Composition sketch (≤3 lines):
```lean
-- the definition itself, by rfl:
example (p n : ℕ) [Fact p.Prime] : Fglobal p n = ℚ⟮zetaSys p n⟯ := rfl
-- the cyclotomic structure, when wanted:
example (p n : ℕ) [Fact p.Prime] :
    IsCyclotomicExtension {p ^ n} ℚ (ℚ⟮zetaSys p n⟯ : IntermediateField ℚ ℂ_[p]) :=
  (zetaSys_primitiveRoot p n).intermediateField_adjoin_isCyclotomicExtension
```

Call sites in our project (from Phase 6.0): **K ≈ 17** (8 internal in `CyclotomicUnits.lean`; ~9 in
`IwasawaProof/Generators.lean`).
Refactor plan (mathlib-upstreaming view): at each of the K sites, inline `ℚ⟮zetaSys p n⟯` in place of
`Fglobal p n`. The two `rw [Fglobal]` sites (`CyclotomicUnits.lean:144`, `Generators.lean:1078`) then drop
the rewrite entirely — `IntermediateField.adjoin_induction` applies to `ℚ⟮zetaSys p n⟯` directly. All other
sites are unchanged in shape (`(ℚ⟮zetaSys p n⟯).inv_mem`, `… ∈ ℚ⟮zetaSys p n⟯`, etc.) since they already use
the generic `IntermediateField`/`SetLike` API. **For the project, the equally-valid action is simply: do
nothing — keep the alias.** Either way, do **not** open a mathlib PR for `Fglobal`.

Next action: no mathlib PR. Optionally inline `ℚ⟮zetaSys p n⟯` at the call sites if a mathlib-style cleanup is
desired; otherwise retain `Fglobal` as a project-local readability anchor (mirroring `K p n`).

---

## Next step

No mathlib PR for `Fglobal`. It is a 0-call defeq alias of the mathlib primitive `ℚ⟮zetaSys p n⟯`
(`IntermediateField.adjoin ℚ {zetaSys p n}`), whose cyclotomic structure is already supplied by
`IsPrimitiveRoot.intermediateField_adjoin_isCyclotomicExtension`. Inline the bare term at call sites if doing
a mathlib-facing cleanup; otherwise keep it as a local convenience. (The same NO-composable verdict applies by
inheritance to the sibling one-liner `FglobalPlus p n = ℚ⟮zetaSys p n + (zetaSys p n)⁻¹⟯`, the maximal totally
real subfield — also a bare-`IntermediateField.adjoin` alias.)
