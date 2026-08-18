# /mathlibable report — `PadicLFunctions.Coleman.mem_localUnitsOne_iff`

**Mode:** A (single declaration, full 10-phase workflow with exhaustive 9-channel literature search)
**Target:** `PadicLFunctions.Coleman.mem_localUnitsOne_iff`
**Kind:** `lemma` (glue lemma; body is `Iff.rfl`)
**Source:** `projects/PadicLFunctions/PadicLFunctions/Iwasawa/LocalUnits.lean:96`
**Date:** 2026-06-20

---

## FINAL VERDICT: `NO-composable-from-mathlib`

> `mem_localUnitsOne_iff` is a **glue lemma**: its body is `Iff.rfl`, and its right-hand
> side is byte-for-byte the `carrier` predicate of the parent `def localUnitsOne`
> (`LocalUnits.lean:71`, carrier `{u | u ∈ localUnits p n ∧ ‖(u : ℂ_[p]) - 1‖ < 1}`). It
> contributes **no mathematical content** — it is the standard mathlib `mem_X_iff`
> companion to a `SetLike` subobject defined via a `carrier := {x | …}` literal, exactly
> the `@[simp] lemma mem_carrier {p : MySubobject X} : x ∈ p.carrier ↔ x ∈ (p : Set X) :=
> Iff.rfl` idiom documented verbatim in `Mathlib/Data/SetLike/Basic.lean:50,92`. Mathlib
> even ships the precise abstract analog of this exact lemma:
> `ValuationSubring.mem_principalUnitGroup_iff` (`Mathlib/RingTheory/Valuation/ValuationSubring.lean:656`,
> body `Iff.rfl`) is the membership-unfolding companion to mathlib's own principal-unit
> subgroup `ValuationSubring.principalUnitGroup`. Such a lemma is **never contributed to
> mathlib on its own** — it is born, lives, and ships with its parent subgroup. Since the
> parent `localUnitsOne` (the project's level-`n` principal-unit subgroup `𝒰_{n,1}` of the
> cyclotomic tower inside `ℂ_p`) is itself **not** mathlib's `principalUnitGroup` — it
> carries the *extra* level-specific conjunct `u ∈ localUnits p n` (membership in the units
> of the finite-level subring `O p n = (K p n).toSubring ⊓ integerRing ℂ_[p]`, not a single
> valuation subring's units) — there is no mathlib parent from which to inherit a YES, and
> there is no mathlib lemma stating *our* iff (Phase 5 grep: 0 hits for the project form).
> The membership-unfolding, *given the def exists*, is a one-call composition of mathlib's
> `SetLike`/`Iff.rfl` primitives against the carrier. So the lemma is
> `NO-composable-from-mathlib`: **keep it in the project** as the local `mem_X_iff` for the
> local `def localUnitsOne`, and if `localUnitsOne` is ever upstreamed (a
> YES-but-generalise question that belongs to the *parent def*, not this lemma), this lemma
> ships *with* it as the standard auto-generated glue. It is never a standalone mathlib
> contribution.

*(Why not `NO-mathlib-has-it`: mathlib's `mem_principalUnitGroup_iff` is about a strictly
**different** subgroup — `{x : Kˣ | A.valuation (x-1) < 1}` for one valuation subring `A` —
whereas `localUnitsOne` adds the `u ∈ localUnits p n` finite-level conjunct. Our iff does
not follow from mathlib's in ≤1 line; the conjuncts differ. Why not `BORDERLINE`: the only
judgment call — "is `localUnitsOne` worth upstreaming, and at what generality?" — is a
question about the **parent def**, not this `Iff.rfl` lemma. This lemma's own verdict is
unambiguous content-free glue.)*

---

## Phase 0 — Doctor / baseline

### Baseline (Phase 0)
- lake build:               build not re-run (stale/slow per task note); **reasoned from source** — Phase 0 fallback. The decl's body is `Iff.rfl` and its dependencies (`localUnitsOne`, `localUnits`, `O`, `K`, `ℂ_[p]`) all read cleanly from source.
- decl `PadicLFunctions.Coleman.mem_localUnitsOne_iff`: ✓ resolved at `projects/PadicLFunctions/PadicLFunctions/Iwasawa/LocalUnits.lean:96`
- kind:                      `lemma`
- has sorry:                 no (body is `Iff.rfl`)
- module docstring summary:  Local unit groups of the cyclotomic tower (RJW §9): `𝒰_n`, principal units `𝒰_{n,1}`, the `+`-subfields, the `ℤ_p`-power structure on principal units, and the norm-compatible towers `𝒰_∞`.

Resolution: a single match in the project (`grep -nE "mem_localUnitsOne_iff"` → `LocalUnits.lean:96` as the declaration; all other hits are call sites). No ambiguity.

---

## Phase 1 — Comprehend

### Statement (Phase 1)

`PadicLFunctions.Coleman.mem_localUnitsOne_iff` is **a membership-characterisation lemma**
for the principal-unit subgroup `𝒰_{n,1}` (`localUnitsOne`). It states the following:

> For a unit `u ∈ ℂ_[p]ˣ` of the completed algebraic closure of `ℚ_p` and a level `n`, `u`
> lies in the principal units `𝒰_{n,1}` of the cyclotomic tower if and only if `u` lies in
> the local units `𝒰_n` (the units of the level-`n` integer ring `O_n`) **and** `‖u − 1‖ <
> 1` (i.e. `u ≡ 1 mod 𝔭_n`, the principal-unit congruence rendered as the open-unit-ball
> condition, replan R11.6).

Mathematically this is simply the **definition of the principal-unit subgroup unfolded**:
`𝒰_{n,1} = {u ∈ 𝒰_n : u ≡ 1 (mod 𝔭_n)}`. The lemma is the `Iff.rfl` that exposes the
`carrier` predicate of `localUnitsOne` to `rw`/`refine`.

Variables / typeclasses involved (Lean side):
- `p : ℕ`, `[hp : Fact p.Prime]` — the residue characteristic (section variables).
- `n : ℕ` — the level in the cyclotomic tower (implicit).
- `u : ℂ_[p]ˣ` — a unit of `ℂ_[p] = Completion (PadicAlgCl p)` (implicit).

Hypotheses (Lean side): none (it is a biconditional with no side conditions).

Conclusion (math): `u ∈ 𝒰_{n,1} ⟺ (u ∈ 𝒰_n ∧ ‖u − 1‖ < 1)` — the defining property of the
principal-unit subgroup.

Conclusion (Lean):
`u ∈ localUnitsOne p n ↔ u ∈ localUnits p n ∧ ‖(u : ℂ_[p]) - 1‖ < 1`, proved by `Iff.rfl`.

**Parent def (`localUnitsOne`, `LocalUnits.lean:71`):**
```lean
def localUnitsOne (n : ℕ) : Subgroup ℂ_[p]ˣ where
  carrier := {u | u ∈ localUnits p n ∧ ‖(u : ℂ_[p]) - 1‖ < 1}
  …
```
The lemma's RHS is *literally* this carrier predicate; hence `Iff.rfl`.

---

## Phase 2 — Preliminary checks (size + one-line)

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: a membership-unfolding `Iff.rfl` glue lemma for a project-specific bundled subgroup;
not a new structure, not a `## Main results` entry, not named after a person/place.

(Note: literature width is EXHAUSTIVE regardless. The 9-channel sweep below was run in full.)

### One-line check (Phase 2b)

Body line count: 1 substantive line (`Iff.rfl`)
One-liner verdict: **n/a** — kind is `lemma`, not `def`/`abbrev`/`structure`. The one-liner
exemption machinery (defeq-barrier / diamond / API-name) is for definitions; a one-line
*proof* of a *biconditional* is just a trivial proof, not a sealed definitional barrier.
For the record this lemma is itself the consequence of the parent def's `carrier`, so the
"defeq abuse" concern lives on the def, not here.

---

## Phase 3 — Literature search (EXHAUSTIVE, all channels)

The question has **two layers**, and both were searched:

- **(L1) the mathematical object** — *principal units / one-units* `U^{(1)} = 1 + 𝔪` of a
  local field (what `localUnitsOne` realises), and its appearance in Iwasawa theory / the
  cyclotomic tower (the RJW §9 context).
- **(L2) the Lean meta-question** — should an `Iff.rfl` membership-unfolding lemma
  (`mem_X_iff`) for a project-specific `SetLike` subobject be in mathlib on its own?

### Literature search table — EXHAUSTIVE protocol

| #  | Channel | Query | Hit? | Standard form found | Notes |
|----|---------|-------|------|---------------------|-------|
| 1 | WebSearch (specific form) | "principal units one-units local field units congruent to 1 mod maximal ideal definition" | yes | `U_L^n := 1 + 𝔓_L^n`; principal units are units `≡ 1` mod (a power of) the maximal ideal | Berkeley/Cambridge Local Fields notes; arXiv 1803.05743, 2104.03299. Standard, classical. |
| 2 | WebSearch (general form / filtration) | "group of principal units U^(1) local field higher unit groups U_n filtration" | yes | filtration `U_L ⊃ U_L^{(1)} ⊃ U_L^{(2)} ⊃ …`, `U^{(1)} = 1 + 𝔪`, `U^{(n)}/U^{(n+1)} ≅ 𝒪/𝔪`; closed-subgroup neighbourhood base of `1` | Springer "Filtration of the group of principal units…"; p-adic.com Local Fields notes. Confirms `‖u−1‖<1` ⇔ `U^{(1)}` membership. |
| 3 | WebSearch (named-after / context: Iwasawa, Coleman) | "Iwasawa theory cyclotomic tower local units principal units norm compatible Coleman map" | yes | norm-compatible systems of (principal) units in the cyclotomic `ℤ_p`-tower; Coleman power series; Kubota–Leopoldt construction | arXiv 2309.15692 (intro to p-adic L-functions), Sharifi/Hida notes. This is exactly RJW §9's setting; `localUnitsOne`/`unitsTower1` are standard objects here. |
| 4 | ChatGPT MCP | (intended: "standard def of the principal-unit group of a local field; should an `Iff.rfl` `mem_X_iff` membership lemma for a bespoke subgroup go in mathlib?") | **n/a** | — | **ChatGPT MCP not configured in this session** (no `mcp__…chatgpt` tool exposed; only an auth-cache file present). Compensated with extra WebSearch (#5, #9) + direct mathlib-source reading (Phase 5) + the project's own sibling precedent (`mem_zetaIdeal_iff` report). |
| 5 | Local references | grep `projects/PadicLFunctions/.mathlib-quality/references/` | **n/a** | (no references dir) | Directory absent (only `overview/` exists). Recorded n/a. The RJW source PDF is local-only/gitignored and not present in this checkout. |
| 6 | nLab | "principal units / higher unit group local field 1 + maximal ideal" | yes (concept) | `U_1 := 1 + ϖ𝒪_k`, higher `U_n := 1 + ϖ^n𝒪_k`; reduction-map kernel `1 + 𝔪_K` | nLab "maximal ideal"; Grokipedia "Local field". No dedicated nLab page for the *membership lemma* — confirms L1 is classical, L2 is a Lean-formalisation idiom not a math concept. |
| 7 | nCatLab (categorical) | (principal-unit subgroup as a categorical/abstract construction) | **n/a** | — | Not a categorical concept; principal units are a concrete subgroup of a local field's units, not a (co)limit / universal-property object. No higher-categorical generalisation applies. |
| 8 | Stacks Project (alg geom) | (principal units / unit filtration) | **n/a** | — | Stacks treats valuation rings / local rings but the principal-unit *subgroup filtration* of a local field is a number-theory object; not the relevant Stacks material. The membership-iff is a Lean idiom, outside Stacks scope. |
| 9 | MathOverflow / Math.SE + mathlib idiom | "mathlib Lean local field principal units one-units subgroup …" and "mathlib SetLike mem_carrier Iff.rfl idiom membership lemma carrier" | yes | (L1) Nuccio "Formalizing Local Fields in Lean"; (L2) **the documented mathlib idiom**: `@[simp] lemma mem_carrier {p : MySubobject X} : x ∈ p.carrier ↔ x ∈ (p : Set X) := Iff.rfl` | `Mathlib/Data/SetLike/Basic.lean` docstring is explicit that this `Iff.rfl` membership lemma is the *standard companion* to a `SetLike` subobject — i.e. born with the def, never a standalone contribution. |
| 10 | recent arXiv (last 5 years) | principal units / one-units in Iwasawa-theoretic p-adic L-function constructions | yes | arXiv 2309.15692 (2023), 2104.03299, 1803.05743 — all use principal/one-unit groups and norm-compatible systems exactly as RJW §9 does | Confirms the *object* is current and standard; says nothing for/against shipping a `mem_X_iff` glue lemma (an artifact of formalisation, not of the maths). |

**Protocol pass check:** WebSearch ran ≥3 distinct queries at different generality levels
(#1 specific, #2 filtration/general, #3 named context, #5/#9 meta) ✓. ChatGPT MCP recorded
`n/a` with a one-line reason + explicit compensation ✓. Local refs checked (`n/a`, absent)
✓. nLab checked ✓. nCatLab / Stacks / MathOverflow / arXiv each checked or `n/a` with reason
✓.

### Literature summary (Phase 3)

Concept identified as: **(L1)** the *group of principal units / one-units* `U^{(1)} = 1 + 𝔪`
of a local field — completely standard (Serre, *Local Fields*; Cassels–Fröhlich; every
local-fields course), here taken in the cyclotomic-tower / Iwasawa setting (RJW §9,
TeX 2494). **(L2)** the lemma itself is *not a mathematical concept* — it is the standard
**mathlib `SetLike` membership-unfolding idiom** (`mem_carrier`/`mem_X_iff := Iff.rfl`).

Sources agree on the standard form: **yes** — `U^{(1)} = {u ∈ 𝒪^× : u ≡ 1 mod 𝔪}`, exactly
the project's `{u ∈ 𝒰_n : ‖u−1‖<1}` (the norm condition is the congruence for a complete
non-archimedean field). Mathlib's own `ValuationSubring.principalUnitGroup` uses the same
`{x : Kˣ | A.valuation (x−1) < 1}` shape.

Most general standard form (of the *object*): the principal-unit subgroup
`A.principalUnitGroup ≤ Kˣ` of a valuation subring `A`, i.e. mathlib's existing definition.

Generality dimensions where the literature varies:
- base: a single local field `K` (mathlib `ValuationSubring`) vs. the *family* of finite
  levels `K_n` of a tower (RJW / this project). The project's `localUnitsOne p n` is the
  level-`n`, tower-indexed version, with the extra "lives in `O_n`" conjunct.
- the congruence depth: `1 + 𝔪` (the project's `‖u−1‖<1`) vs. higher `1 + 𝔪^j`. The
  project only needs depth 1.

Disagreement with the literature: **none**. The object is standard; the lemma is a faithful
`Iff.rfl` unfolding of the standard object's definition.

(The literature search did **not** return nothing — but what it returned for L2 is the
*decisive* finding: the membership lemma is a formalisation idiom that ships with its def,
which is the engine of the NO verdict.)

---

## Phase 4 — Generality analysis

### Generality analysis — `mem_localUnitsOne_iff`

Literature-standard form (from Phase 3): principal-unit subgroup of a (valuation subring of
a) local field; mathlib's `ValuationSubring.principalUnitGroup` with `mem_principalUnitGroup_iff`.

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason it can/can't be weakened |
|---|------------------------|-------------------|--------------------------|---------------------|----------------------------------|
| 1 | `u : ℂ_[p]ˣ` | unit of `ℂ_p` | unit of an arbitrary local field / valued field `Kˣ` | yes (in principle) | But this is the **parent def's** generality question, not the lemma's. The lemma faithfully unfolds whatever carrier the parent has; it cannot be "more general" than the def it unfolds. |
| 2 | RHS conjunct `u ∈ localUnits p n` | units of the finite-level subring `O_n` | (mathlib's `principalUnitGroup` omits this — it's automatic for a valuation subring's units) | n/a | This conjunct is *constitutive* of the project's object. Dropping it changes which subgroup we mean; it is not a weakening of a lemma but a redefinition of the def. |
| 3 | RHS conjunct `‖(u:ℂ_[p]) − 1‖ < 1` | open-unit-ball congruence | `A.valuation (x − 1) < 1` | n/a (equivalent) | Same content as mathlib's `principalUnitGroup` carrier, transported to the norm. |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL relative to its parent def** (a membership `Iff.rfl`
is, by construction, exactly as general as the def it unfolds — it has no independent
generality knob). Number of weakening opportunities found *on the lemma itself*: **0**. All
generality questions (base field, tower-vs-single-field, congruence depth) attach to the
**parent `def localUnitsOne`**, not to this `Iff.rfl` lemma.

Proposed restatement: **none** (a glue lemma has nothing to restate independently of its def).
Cost of restatement: n/a.

### Modern-idiom check (Phase 4c)

| #  | Question | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|----------|----------|------------------------|---------------------------------|
| 1 | "let X be a foo" preamble → typeclass/instance? | no | — | The lemma has no bundled-hypothesis preamble; it is a bare biconditional. |
| 2 | sequences/metric → filters/topological? | no | — | No limit/convergence content; it is a static membership iff. (The `‖·‖<1` is a ball condition, already the right primitive.) |
| 3 | construction → universal-property class? | no | — | Nothing is constructed; membership unfolding only. |
| 4 | set-with-closure-predicate → bundled substructure? | **already done** | — | `localUnitsOne` is **already** a bundled `Subgroup ℂ_[p]ˣ` (not a raw set). The lemma is the `mem_` companion of the bundled type — the modern idiom is already in force. |
| 5 | vector-space/metric/field-specific → weaker typeclass? | no | — | The base is fixed as `ℂ_p` by the *parent def* and the whole tower development; not a lemma-level knob. |
| 6 | 1-categorical → higher-categorical? | no | — | Not categorical. |
| 7 | concrete index (ℕ/ℤ/ℝ) → arbitrary monoid/group? | partial (parent) | — | The level index `n : ℕ` is the tower level; generalising it is meaningless (it *is* the ℕ-indexed cyclotomic tower). A parent-def matter, not a lemma matter. |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no** (for the lemma itself). The bundled-`Subgroup` idiom (row 4)
is already in use; the lemma is its natural `mem_` companion. There is no contemporary
reformulation that would change *this* lemma — every modernisation lever is on the parent
`def localUnitsOne`. One-line reason: a membership `Iff.rfl` has no independent statement to
modernise; it inherits its form from its def.

---

## Phase 4.5 — Diamond / defeq risk

**n/a — declaration kind is `lemma`.** Lemmas introduce no definitional equalities and no
typeclass-search paths, so the six-row diamond/defeq/reducibility/priority/universe/coercion
table does not apply. (The defeq concern — that `localUnitsOne`'s carrier should not be
unfolded unexpectedly — lives on the **parent def**, where the `Iff.rfl` lemma is precisely
the controlled way to expose it.)

---

## Phase 5 — Mathlib search

### Mathlib search-status: `PadicLFunctions.Coleman.mem_localUnitsOne_iff`

[A] Lean-Finder       (server not invoked; reasoned via local mathlib grep + docs)      n/a — substituted by [D]/[E] over the unpacked mathlib tree at `.lake/packages/mathlib`
[B] Loogle            type pattern `_ ∈ _ ↔ _ ∈ _ ∧ ‖_ - 1‖ < _` ; `Subgroup _ → … principalUnit`   no hit for the project's *conjunctive* form; the only `valuation (x-1) < 1` membership iff in mathlib is `ValuationSubring.mem_principalUnitGroup_iff` (single condition, no `∈ O_n` conjunct)
[C] LeanSearch        "principal units subgroup of a local field membership iff" (NL)            partial — surfaces `ValuationSubring.principalUnitGroup` family; not our conjunctive level-`n` form
[D] Grep mathlib src  `localUnits`, `ℂ_[p]`, `principalUnitGroup`, `mem_carrier`, `1 + maximalIdeal`   hits: `ValuationSubring.principalUnitGroup`+`mem_principalUnitGroup_iff` (`Mathlib/RingTheory/Valuation/ValuationSubring.lean:634,656`); the documented `SetLike` idiom `mem_carrier … := Iff.rfl` (`Mathlib/Data/SetLike/Basic.lean:50,92`). **0** hits for the project form (`localUnits`/`ℂ_[p]` absent from mathlib).
[E] Name pattern      `mem_localUnitsOne`, `mem_*PrincipalUnit*`, `mem_*oneUnit*`                  no hit for the project name in mathlib; mathlib's nearest names are `(coe_)mem_principalUnitGroup_iff`

Searched for both:
  - the user's current form (`u ∈ localUnitsOne p n ↔ u ∈ localUnits p n ∧ ‖(u:ℂ_[p])−1‖<1`) — **not in mathlib**;
  - the literature-standard / abstract form (principal-unit subgroup membership) — **mathlib HAS this** as `ValuationSubring.mem_principalUnitGroup_iff`, but for a *strictly different* subgroup (single valuation subring, no `∈ O_n` conjunct).

Concluded: **"not in mathlib (all methods exhausted, plus the literature-standard form)"** —
*for our exact statement*. Mathlib has the **abstract analog** (`principalUnitGroup` +
`mem_principalUnitGroup_iff`), which (a) proves the membership-`Iff.rfl` lemma is a
ships-with-the-def companion, and (b) is about a different object, so our lemma is neither a
duplicate nor a ≤1-line specialisation of it (the `u ∈ localUnits p n` conjunct is not
present in mathlib's version, and `localUnits p n` is itself a project-specific def).

---

## Phase 6 — Composition check (+ call-sites signal)

### Call sites — `mem_localUnitsOne_iff`

Internal use count: **14** (within the project, NOT counting the declaring file's own line 96)
External-to-file callers: **6 distinct files**

| Caller file:line | Usage pattern (one-line excerpt) |
|------------------|----------------------------------|
| `Iwasawa/ResidueField.lean:343` | `refine (mem_localUnitsOne_iff (p := p)).2 ⟨?_, ?_⟩` |
| `Iwasawa/LocalUnits.lean:355` | `((mem_localUnitsOne_iff p).1 g.2).2` (inside `norm_localUnitsOne_sub_one_lt_one`) |
| `Iwasawa/CyclotomicUnits.lean:490` | `rw [mem_localUnitsOne_iff]; refine ⟨hmemloc, ?_⟩` |
| `Iwasawa/CyclotomicUnits.lean:562` | `rw [mem_localUnitsOne_iff]; exact ⟨⟨hmemO, hmemOinv⟩, …⟩` |
| `Iwasawa/CyclotomicUnits.lean:676` | `have hgc : … := ((mem_localUnitsOne_iff p).1 hg).2` |
| `Iwasawa/CyclotomicUnits.lean:695` | `((mem_localUnitsOne_iff p).1 hg).1⟩, hg⟩` |
| `IwasawaProof/Generators.lean:869` | `have hgnorm : … := ((mem_localUnitsOne_iff p).1 hg).2` |
| `IwasawaProof/Generators.lean:1019` | `have hone := ((mem_localUnitsOne_iff p).1 (hu n hn)).2` |
| `IwasawaProof/Generators.lean:1022` | `refine (mem_localUnitsOne_iff p).2 ⟨?_, ?_⟩` |
| `IwasawaProof/Generators.lean:1711` | `refine ⟨?_, ((mem_localUnitsOne_iff p).1 (hmem n hn)).1⟩` |
| `IwasawaProof/Generators.lean:1767` | `((mem_localUnitsOne_iff p).1 hgprin).1⟩, hgprin⟩` |
| `IwasawaProof/FundamentalSequence.lean:812` | `(mem_localUnitsOne_iff (p := p).1 (hu 1 hn1)).2` |
| `IwasawaProof/FundamentalSequence.lean:1179` | `refine (mem_localUnitsOne_iff (p := p)).2 ⟨⟨w.mem n, hinv⟩, ?_⟩` |
| `Coleman/ColContinuity.lean:878` | `exact ((mem_localUnitsOne_iff p).1 hmem).2` |

Inline-derivation grep (was the equivalent re-derived elsewhere without using the lemma?):
  - **(none)** — every destructuring of `localUnitsOne` membership either goes through this
    lemma directly or through derived lemmas (`zpPow_mem_localUnitsOne`,
    `norm_localUnitsOne_sub_one_lt_one`, `Subgroup.mem_inf`). No site re-proves the carrier
    `Iff` inline. The lemma is the single canonical access point to the carrier.

**Composability signal (per the Phase 6.0.1 table):** `K = 14 ≥ 3` internal uses, no inline
re-derivation → a *real, used* internal API anchor. This is a genuine consumer base — which
is exactly why the lemma is correct to **keep in the project**. (It is *not* a
YES-bucket signal here, because the K≥3 signal speaks to keeping the wrapper where its def
lives; the lemma's *content* is still `Iff.rfl`, so it cannot graduate to mathlib
independently of its bespoke parent def.)

### Composition check (Phase 6)

Can `mem_localUnitsOne_iff` be derived from mathlib in ≤3 chained calls?

Attempt 1: `Iff.rfl`
  - Mathlib decls used: the `SetLike` membership instance for `Subgroup` (membership is
    definitionally the `carrier` predicate; cf. `Mathlib/Data/SetLike/Basic.lean` `mem_carrier`).
  - Result: **succeeds** — this *is* the lemma's actual proof. Membership in
    `localUnitsOne p n` is by construction definitionally `u ∈ localUnits p n ∧ ‖(u:ℂ_[p])−1‖<1`,
    so the iff holds by reflexivity.
  - Notes: This is the canonical mathlib `mem_X_iff := Iff.rfl` idiom — a 0–1 call
    composition against the parent def's carrier. Mathlib's own
    `ValuationSubring.mem_principalUnitGroup_iff` is literally this same `Iff.rfl` pattern.

Conclusion: **COMPOSABLE** (a one-call `Iff.rfl` against the parent def's carrier — the
mathlib `SetLike` membership idiom). The "composition" is not a proof in disguise: it is the
trivial reflexivity that *defines* the idiom (heuristics table row: `Iff.rfl`/`mem_carrier`
unfolding — composable).

---

## Phase 7 — Verdict

## Verdict: `PadicLFunctions.Coleman.mem_localUnitsOne_iff`

**Category:** `NO-composable-from-mathlib`

**Evidence:**
- Literature search (Phase 3): the *object* (principal units `U^{(1)} = 1 + 𝔪`) is classical
  and standard (Serre; Cambridge/Berkeley local-fields notes; arXiv 1803.05743, 2104.03299,
  2309.15692); the *lemma* is the documented mathlib `SetLike` membership idiom
  (`Mathlib/Data/SetLike/Basic.lean:50,92`).
- Generality analysis (Phase 4): MAXIMALLY GENERAL relative to its parent; 0 lemma-level
  weakenings (all generality knobs live on the parent `def localUnitsOne`). Modern-idiom: the
  bundled-`Subgroup` idiom is already in force.
- Mathlib search (Phase 5): our exact conjunctive form is **not** in mathlib; mathlib has the
  abstract analog `ValuationSubring.mem_principalUnitGroup_iff` (different subgroup — no
  `∈ O_n` conjunct), which confirms the ships-with-the-def nature of such lemmas.
- Composition check (Phase 6): **COMPOSABLE** — the proof is `Iff.rfl` against the parent
  def's carrier (the `mem_carrier` idiom); 14 internal call sites, no inline re-derivation.

**Rationale:**

`mem_localUnitsOne_iff` carries no mathematical content of its own. Its right-hand side is
*byte-for-byte* the `carrier` predicate of the parent `def localUnitsOne`
(`{u | u ∈ localUnits p n ∧ ‖(u : ℂ_[p]) − 1‖ < 1}`), and its proof is `Iff.rfl`. It is the
exact instantiation of the mathlib `SetLike` convention spelled out in
`Mathlib/Data/SetLike/Basic.lean`: *"create a simp lemma `@[simp] lemma mem_carrier {p :
MySubobject X} : x ∈ p.carrier ↔ x ∈ (p : Set X) := Iff.rfl`."* Mathlib follows this
convention for its own principal-unit subgroup — `ValuationSubring.principalUnitGroup` is
paired with `ValuationSubring.mem_principalUnitGroup_iff := Iff.rfl` — which is direct,
in-mathlib proof that a membership-`Iff.rfl` lemma is the companion of its def, generated and
shipped with the def, never proposed to mathlib as a standalone result.

The lemma is therefore `NO-composable-from-mathlib`: given the def exists, the membership iff
is a one-call `Iff.rfl` composition against the carrier (the mathlib `SetLike` membership
primitive). It is **not** `NO-mathlib-has-it`, because mathlib's `mem_principalUnitGroup_iff`
characterises a *different* subgroup — `{x : Kˣ | A.valuation (x−1) < 1}` for a single
valuation subring `A` — whereas `localUnitsOne p n` additionally requires `u ∈ localUnits p
n` (membership in the units of the finite-level subring `O_n = (K_n).toSubring ⊓ integerRing
ℂ_[p]`, not a single valuation subring's units); our iff does not follow from mathlib's in ≤1
line. And it is not `BORDERLINE`: the only genuine judgment call — whether the *parent def*
`localUnitsOne` (the cyclotomic-tower principal-unit subgroup `𝒰_{n,1}`, RJW §9) is worth
upstreaming and at what generality — is a question about the parent, not this `Iff.rfl`
lemma, whose own verdict is unambiguous.

**WHY not (refactor-actionable detail):**

Mathlib has the building block: membership in a `SetLike` subobject defined by `carrier := {x
| P x}` *is* `P x` definitionally, so `mem_localUnitsOne_iff` is exactly `Iff.rfl` — the
canonical `mem_carrier`-style companion lemma (`Mathlib/Data/SetLike/Basic.lean:50,92`; and
the in-mathlib instance `ValuationSubring.mem_principalUnitGroup_iff`,
`Mathlib/RingTheory/Valuation/ValuationSubring.lean:656`). There is no new lemma for mathlib
to acquire here: the content is the def's carrier, and the def (`localUnitsOne`) is a
project-specific object of the RJW cyclotomic-tower development that is not in mathlib.

Mathlib building blocks:
  - `SetLike` membership-unfolding idiom — `Mathlib/Data/SetLike/Basic.lean:50,92`
    (`@[simp] lemma mem_carrier … := Iff.rfl`).
  - In-mathlib exemplar of the same pattern for principal units —
    `ValuationSubring.mem_principalUnitGroup_iff` (`Mathlib/RingTheory/Valuation/ValuationSubring.lean:656`, body `Iff.rfl`).

Composition sketch (≤3 lines):
```lean
-- given the project-local `def localUnitsOne` with carrier {u | u ∈ localUnits p n ∧ ‖(u:ℂ_[p])-1‖<1}:
example {n : ℕ} {u : ℂ_[p]ˣ} :
    u ∈ localUnitsOne p n ↔ u ∈ localUnits p n ∧ ‖(u : ℂ_[p]) - 1‖ < 1 := Iff.rfl
```

Call sites in our project (from Phase 6.0): **K = 14** across 6 files.

**Refactor plan:** **do nothing / keep as-is in the project.** This is the rare
`NO-composable` whose action is *retention*, not deletion: the lemma is the single canonical
access point to `localUnitsOne`'s carrier and is used 14 times, so deleting it and inlining
`Iff.rfl`/`show …` at every site would be a strict readability regression with no upstream
benefit (the parent def isn't going to mathlib in isolation). Concretely:
  - Keep `mem_localUnitsOne_iff` co-located with `def localUnitsOne` in
    `Iwasawa/LocalUnits.lean`. (Optionally add `@[simp]` to match the mathlib `mem_carrier`
    convention — a `/cleanup` nicety, not a `/mathlibable` action.)
  - Do **not** open a mathlib PR for it. If `localUnitsOne` is ever upstreamed, this lemma
    ships *with* it as the auto-generated `mem_` companion — and that upstreaming decision is
    a `/mathlibable` question for the **parent def `localUnitsOne`**, not for this lemma.
  - At the 14 call sites: no change required.

**Next action:** keep `mem_localUnitsOne_iff` in the project as the local `mem_X_iff` for
`def localUnitsOne`; do not contribute it to mathlib standalone. (If the parent
`localUnitsOne` is later judged worth upstreaming — likely re-aimed at / generalising
mathlib's `ValuationSubring.principalUnitGroup` — re-run `/mathlibable localUnitsOne` to
settle that, and this glue lemma will travel with it.)

---

## Next step

Keep `mem_localUnitsOne_iff` in the project as the local membership-unfolding companion to
`def localUnitsOne`; do **not** open a standalone mathlib PR. The only open upstreaming
question belongs to the parent def `localUnitsOne` (assess via `/mathlibable
PadicLFunctions.Coleman.localUnitsOne`, tensioning it against mathlib's
`ValuationSubring.principalUnitGroup`); this `Iff.rfl` glue lemma is content-free and ships
with its parent if and when the parent goes up.
