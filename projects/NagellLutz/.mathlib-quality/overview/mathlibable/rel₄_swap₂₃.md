# /mathlibable report — `EllSequence.rel₄_swap₂₃`

_Project: NagellLutz (Nagell–Lutz / elliptic divisibility sequences). Assessment run as part of `/overview` Step 9._

## Verdict (one line)

**NO-composable-from-mathlib** — internal sign-swap API for the project's bespoke `rel₄` (the 4×4 Pfaffian of `addMulSub`); neither `rel₄` nor `addMulSub` nor even `Pfaffian` exists in mathlib, so this lemma is not mathlib-shaped — it stays as project API. (Exact analogue of the sibling `rel₄_swap₁₂`; same verdict.)

---

### Baseline (Phase 0)
- lake build:               not re-run (build is stale per task note); reasoning from source. Decl elaborates in-tree (an established lemma with a 1-line proof, no `sorry`).
- decl `EllSequence.rel₄_swap₂₃`:  ✓ resolved at `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:523`
- qualified name:            **`EllSequence.rel₄_swap₂₃`** — VERIFIED. `namespace EllSequence` opens at line 90 and is still open at 523; the inner `HaveSameParity₄` namespace (216–…) and the `Rel₄OfValid` section (…–507) are both closed before line 523; the enclosing `section Perm` (opened 509) introduces no namespace. So the only open namespace at 523 is `EllSequence`. The parsed guess matches.
- kind:                      `lemma`
- has sorry:                 no
- module docstring summary:  Develops Stange's elliptic-net relations (`addMulSub`, `rel₄`, `net`) over a commutative ring and proves the equivalence with elliptic divisibility sequences — the algebraic core of the Nagell–Lutz formalization. The file is a fork/rewrite that adds an entire 4-index-relation layer not present in upstream `Mathlib.NumberTheory.EllipticDivisibilitySequence`.

---

### Statement (Phase 1)

`EllSequence.rel₄_swap₂₃` states that swapping the **3rd and 4th** arguments (0-indexed: indices 2 and 3) of the four-index elliptic relation `rel₄` negates it, provided `W` is an odd function:

> For a commutative ring `R`, a sequence `W : ℤ → R` satisfying `W (-k) = -W k` for all `k`, and integers `m, n, r, s`:
> `rel₄ W m n r s = - rel₄ W m n s r`.

Source (verbatim, line 523–524):
```
lemma rel₄_swap₂₃ {m n r s : ℤ} : rel₄ W m n r s = - rel₄ W m n s r := by
  simp_rw [rel₄, addMulSub_swap W neg s r]; ring
```

Here `rel₄ W a b c d = f(a,b)·f(c,d) − f(a,c)·f(b,d) + f(a,d)·f(b,c)` where `f = addMulSub W`, and `addMulSub W m n = W ((m+n).tdiv 2) · W ((m−n).tdiv 2)` (def at line 94/103). When `W` is odd, `addMulSub` is antisymmetric (`addMulSub_swap`, line 198: `f(m,n) = −f(n,m)`).

**Mathematical identity.** `rel₄ W a b c d` is exactly the **4×4 Pfaffian** of the antisymmetric matrix `M_{ij} = f(x_i,x_j)` with `(x₁,x₂,x₃,x₄)=(a,b,c,d)`: `Pf(M) = M₁₂M₃₄ − M₁₃M₂₄ + M₁₄M₂₃` (the docstring's "three partitions of four indices into two pairs" = the three perfect matchings of `K₄`). So `rel₄_swap₂₃` is the standard *Pfaffian is alternating under a transposition of the underlying points* property, instantiated at the transposition (3 4) on this bespoke matrix.

Variables / typeclasses (Lean side):
- `{R : Type u} [CommRing R]` — the coefficient ring the sequence lands in.
- `(W : ℤ → R)` — the sequence (elliptic-net values).
- `(neg : ∀ k, W (-k) = -W k)` — `W` is odd (an `include`d `section Perm` variable, line 511–512).
- `{m n r s : ℤ}` — the four indices.

Hypotheses (Lean side):
- `neg : ∀ k, W (-k) = -W k` — oddness of `W`; this is what makes `addMulSub` antisymmetric and hence what makes the transposition flip the sign.

Conclusion (math): swapping arguments 3 and 4 of `rel₄` negates it.
Conclusion (Lean): `rel₄ W m n r s = - rel₄ W m n s r`.

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: A structural helper — one of three adjacent-transposition sign lemmas (`rel₄_swap₀₁` @517, `rel₄_swap₁₂` @520, `rel₄_swap₂₃` @523) feeding the `Submonoid.closure_induction` in `relFin4_perm` (@533). Not a named theorem, not a `## Main statements` entry (the file's `## Main statements` lists only `isEllDivSequence_normEDS`), no person/place attached to *this* lemma. (Its consumer `relFin4_perm` — "`rel₄` is `Sₙ`-invariant up to sign" — is the meatier statement, but even that is internal API for a bespoke object.)

(Note: literature width was EXHAUSTIVE regardless — and is shared with the sibling `rel₄_swap₁₂` assessment, which mapped the same concept.)

### One-line check (Phase 2b)

Kind is `lemma`, not a `def`/`abbrev`/`structure` — the one-liner heuristic is about definitions, so this check is **n/a**. (For the record the proof body is 1 line: `simp_rw [rel₄, addMulSub_swap W neg s r]; ring`.)

---

### Literature search table — EXHAUSTIVE protocol

(Concept is identical to the sibling `rel₄_swap₁₂` — the four-index elliptic relation `E(a,b,c,d)` / 4×4 Pfaffian; the only change is which transposition acts. The sweep below mirrors and reconfirms that finding.)

| #  | Channel                          | Query                                                                                                  | Hit? | Standard form found              | Notes |
|----|----------------------------------|--------------------------------------------------------------------------------------------------------|------|----------------------------------|-------|
|  1 | WebSearch (specific form)        | Stange elliptic net relation, "three partitions of four indices into two pairs", antisymmetric / permutation sign | yes  | The 4-index elliptic-net relation; "three ways to partition four factors into two pairs", invariant up to transformation under permutation | Stange, *Elliptic nets and elliptic curves* (arXiv:0710.1316); Semaev↔Stange |
|  2 | WebSearch (general form)         | EDS / Somos four-term relation, alternating sign under permutation, Pfaffian, three-term Plücker, Desnanot–Jacobi | yes  | The bilinear Somos-4 form; 4×4 Pfaffians generate the Plücker ideal of a generic skew matrix; Pfaffian alternating | Hone (arXiv:math/0412293); Pfaffian/Plücker (arXiv:math/0312358) — confirms alternating-quartic = Pfaffian template |
|  3 | WebSearch (named-after / aliases)| "elliptic net" Stange symmetry / permutation of indices; net polynomials                               | yes  | "On Symmetries of Elliptic Nets and Valuations of Net Polynomials" (arXiv:1408.6623) — net symmetries as net-specific identities | symmetry of nets is studied, not as a general named lemma |
|  4 | WebSearch (source paper)         | arXiv:2604.05280 — *On Elliptic Sequences over Commutative Rings* (Junyan Xu)                          | yes  | Defines `E(a,b,c,d): h_{a+b}h_{a-b}h_{c+d}h_{c-d} = h_{a+c}h_{a-c}h_{b+d}h_{b-d} − h_{b+c}h_{b-c}h_{a+d}h_{a-d}`, a "highly symmetric family of homogeneous quartic relations" | **This is the paper the file formalizes** (same author as mathlib's EDS file). `rel₄` is the formalization of `E`; sign-under-permutation is exactly this paper's symmetry. |
|  5 | ChatGPT MCP                      | is `rel₄` a named object (Pfaffian/determinant/Plücker) and would a general mathlib lemma give the swap for free? | n/a  | —                                | **MCP down** this run (per task note). Fallback: Pfaffian identification reasoned directly (Phase 1) + corroborated via WebSearch #2 (Pfaffian/Plücker) and grep (no `Pfaffian` in mathlib). |
|  6 | nLab                             | Pfaffian / elliptic net                                                                                | yes (Pfaffian) / no (net) | nLab "Pfaffian" (alternating, `Pf² = det`); no elliptic-net page | Confirms the general object (Pfaffian of a skew form) is standard and alternating; the elliptic-net specialization is not an nLab concept |
|  7 | nCatLab (categorical)            | —                                                                                                      | n/a  | —                                | Not a categorical concept — a polynomial identity in a commutative ring. |
|  8 | Stacks Project (alg geom)        | —                                                                                                      | n/a  | —                                | Not a scheme/alg-geom concept; an elementary identity about a sequence. |
|  9 | MathOverflow / Math.SE           | (covered by #1–#3 web sweep)                                                                            | partial | Elliptic-net / Somos / Pfaffian structure discussed; no canonical "transposition negates the 4-index relation" lemma | Folklore-level once seen as a Pfaffian. |
| 10 | recent arXiv (last 5 yr)         | arXiv:2604.05280 (2026); arXiv:2512.09601 (2025, valuations of elliptic nets); arXiv:1702.08102 (signs in elliptic nets) | yes  | Sign behavior of elliptic nets is actively studied; `E(a,b,c,d)` is the current standard form | The source paper is the most recent + authoritative statement. |

### Literature summary (Phase 3)

Concept identified as: the **four-index elliptic(-net) relation** `E(a,b,c,d)` of Stange / Junyan Xu — equivalently the **4×4 Pfaffian** `Pf(M)=M₁₂M₃₄−M₁₃M₂₄+M₁₄M₂₃` of the antisymmetric matrix `M_{ij}=addMulSub(x_i,x_j)`.
Sources agree on the standard form: yes (Stange 2007/2011; Xu 2026). The sign-under-transposition is, abstractly, the alternating property of the Pfaffian.
Most general standard form: the Pfaffian of any `2n×2n` antisymmetric matrix is alternating in its underlying index set; transposing two points negates it. The elliptic-net relation is the `n=2` (4×4) case with entries `addMulSub`. `rel₄_swap₂₃` is precisely the transposition (3 4) instance.
Generality dimensions where the literature varies: underlying object ranges from "the elliptic-net relation `E`" → "Pfaffian of a skew form" → "Grassmann–Plücker relation"; sequence/ring ranges from classical EDS over ℤ → general odd `W : ℤ → R` over a comm ring (the project is already at the general end).
Disagreement with the literature: none. `rel₄_swap₂₃` is a correct, literature-consistent instance of "Pfaffian/elliptic-relation is alternating under transposition".

---

### Generality analysis — `EllSequence.rel₄_swap₂₃`

Literature-standard form (Phase 3): the alternating property of the 4×4 Pfaffian of a skew matrix (here: antisymmetry of `rel₄` under the (3 4) transposition of its arguments).

| # | Parameter / hypothesis        | Current Lean form          | Literature-standard form               | Weaker form exists? | Reason it can/can't be weakened |
|---|-------------------------------|----------------------------|----------------------------------------|---------------------|----------------------------------|
| 1 | `[CommRing R]`               | commutative ring           | commutative ring (the quartic needs commutativity) | NO | `ring` closes it over a comm. ring; non-commutative would break the identity. Already the right class. |
| 2 | `(W : ℤ → R)`                | ℤ-indexed sequence         | ℤ-indexed (elliptic nets are ℤ^n; here n=1) | no (in this form) | The whole `addMulSub`/`rel₄` apparatus is ℤ-indexed by design. |
| 3 | `(neg : ∀ k, W (-k) = -W k)` | `W` odd                    | oddness drives the antisymmetry of the building block | NO | Essential — without oddness, `addMulSub` is not antisymmetric and the swap does *not* simply negate. Correctly assumed. |
| 4 | object `rel₄`                | bespoke hand-written quartic | the 4×4 Pfaffian `Pf(M_{ij})`           | (generalisation, not weakening) | Could in principle be stated for an abstract Pfaffian — see 4c — but mathlib has no Pfaffian, so there is nothing to state it against. |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL** (for the object it is about). Every typeclass/hypothesis is already at the weakest level that makes the identity true: comm-ring coefficients, an arbitrary odd ℤ-sequence. There is no mechanical weakening to apply.
Number of weakening opportunities found: 0.
Proposed restatement: none at this generality.
Cost of restatement: n/a.

The only "more general" direction is a *re-foundation* of `rel₄` as an abstract Pfaffian — handled in 4c.

### Modern-idiom check (Phase 4c)

| #  | Question                                                                                                | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|---------------------------------------------------------------------------------------------------------|----------|------------------------|----------------------------------|
|  1 | "let X be a foo" → typeclass/instance?                                                                  | no       | — | `neg` (oddness) is a genuine hypothesis on a specific `W`, not a structure worth a class. |
|  2 | sequences/metric → filters/topology?                                                                    | no       | — | Purely algebraic identity; no limits/topology. |
|  3 | construct an object → universal-property class?                                                          | no       | — | Nothing is constructed; it is an equation. |
|  4 | set-with-closure-predicate → bundled substructure?                                                       | no       | — | Not a substructure. |
|  5 | field/metric-specific → weaken typeclass?                                                                | no       | already at `CommRing` | Already maximally weak (row 1 above). |
|  6 | 1-categorical → higher-categorical?                                                                      | no       | — | N/A. |
|  7 | concrete index ℕ/ℤ/ℝ → arbitrary monoid/group?                                                           | partial  | (the *relation* could be the Pfaffian of an abstract skew matrix) | **The real modernisation axis: state `rel₄` as `Matrix.pfaffian` of `addMulSub`, then "swap negates" is a corollary of a general `pfaffian_alternating`-style lemma.** BUT mathlib has **no `Pfaffian`** (grep over `Mathlib/`: empty) — so the modern idiom does not exist to target. |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no** (not actionably).
One-line reason: The only contemporary reformulation is "`rel₄` = `Matrix.pfaffian` of the skew matrix `addMulSub`, with the swap lemma a specialization of Pfaffian alternating-ness", but **mathlib has no Pfaffian API at all** (confirmed: `grep -r Pfaffian` over the pinned mathlib tree is empty). So there is no mathlib-idiomatic target to restate against; building Pfaffian theory is a large independent contribution, far out of scope for this sign lemma. The lemma's *name* (`…_swap₂₃`) already follows mathlib's transposition-sign idiom — cf. **`oangle_swap₂₃_sign`** in `Mathlib/Geometry/Euclidean/Angle/Oriented/Affine.lean:469` (`-(∡ p₁ p₂ p₃).sign = (∡ p₁ p₃ p₂).sign`), the *identical naming convention* for "transposing the last two arguments negates a sign" — so the naming is already modern; only the underlying object is bespoke.

---

### Diamond / defeq risk — Phase 4.5

n/a — declaration kind is `lemma` (proves a propositional equation; introduces no definitional equalities, instances, or typeclass-search paths).

---

### Mathlib search-status: `EllSequence.rel₄_swap₂₃`

[A] Lean-Finder       — (endpoint unavailable this run)                              n/a: covered by [B][C][D][E]
[B] Loogle            `Pfaffian`; `"addMulSub"`; `"rel₄"`                              **no hits**: `Pfaffian` → unknown identifier (not in mathlib); `addMulSub` → 0 decls; `rel₄` → 0 decls
[C] LeanSearch        "expression negated under transposition of its last two arguments"  n/a: endpoint flaky this run; substituted with [B]-style + [D] grep, which are definitive for "does this name/object exist"
[D] Grep mathlib src  `rel₄` / `addMulSub` / `relFin4` / `[Pp]faffian` / `_swap₂₃` over `.lake/packages/mathlib/Mathlib/` (pinned `d90090f`)  **no hits** for `rel₄`/`addMulSub`/`relFin4`/`Pfaffian`; the only `_swap₂₃` hit is `oangle_swap₂₃_sign` (oriented-angle geometry — same idiom, unrelated object). The substring `EllSequence` appears in mathlib **only** inside `IsEllSequence` in `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean`, which has **none** of `rel₄`/`addMulSub`/`net`.
[E] Name pattern      `_swap₂₃` / `_swap23` over mathlib                              only hit: `oangle_swap₂₃_sign` (oriented-angle geometry) — **same naming idiom, unrelated object** (`EuclideanGeometry`'s `∡`, not `rel₄`)

Searched for both:
  - the user's current form (`rel₄_swap₂₃` about `rel₄`/`addMulSub`) → absent.
  - the literature-standard / general form (Pfaffian of a skew matrix, alternating under transposition) → **mathlib has no Pfaffian whatsoever**, so the general form is also absent.

Concluded: **not in mathlib** (all methods exhausted: object-name search + `Pfaffian` search + grep over mathlib source + name-pattern + general-form Pfaffian search, all negative). The forked `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean` is entirely about `preNormEDS`/`normEDS`/`complEDS` and contains none of the `rel₄` machinery — confirming the project's `rel₄`/`addMulSub`/permutation layer is net-new and not upstream. **This is therefore NOT a "mathlib-already-has-it" duplicate**, despite the file forking that mathlib module: the swap layer is genuinely absent from mathlib.

---

### Call sites — `EllSequence.rel₄_swap₂₃`

Internal use count (NagellLutz, excluding the declaring line 523): **1**
External-to-file callers (within NagellLutz `LutzNagell/`): the single use is **in the same file** (`relFin4_perm`).

| Caller file:line                                                                 | Usage pattern (one-line excerpt)                                   |
|----------------------------------------------------------------------------------|--------------------------------------------------------------------|
| `…/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:542`                  | `exacts [rel₄_swap₀₁ neg, rel₄_swap₁₂ neg, rel₄_swap₂₃ neg]` — supplies the three adjacent-transposition base cases to `Submonoid.closure_induction` inside `relFin4_perm` (the "`rel₄` is permutation-invariant up to sign" theorem). `rel₄_swap₂₃` discharges the `i = 2` (last-pair) generator goal. |

Cross-project / duplicate copies (same forked code, NOT independent consumers):
  - `…/HasseWeil/HasseWeil/Auxiliary/EllipticDivisibilitySequence.lean:437` (verbatim duplicate definition; consumed at its own line 458)
  - `…/NagellLutz/LutzNagell/EllipticDivisibilitySequenceOriginal.lean:502` (a stale/"original" copy in the same project; consumed at its own line ~519)

Inline-derivation grep (was the equivalent re-derived elsewhere without using this lemma?): (none) — every place that needs the last-pair sign-swap calls `rel₄_swap₂₃`; nobody inlines `simp_rw [rel₄, addMulSub_swap …]; ring` at a call site.

**Reading.** K = 1 internal use, no inline re-derivation. K=1 generally hints "could be inlined / wrong abstraction" — but here it is one of a *matched trio* (`swap₀₁`/`swap₁₂`/`swap₂₃`) that exists precisely to be the three generators handed to `closure_induction`; splitting the trio would be unnatural and would just push the same `simp_rw … ; ring` into the `exacts`. The duplication across HasseWeil + the `…Original` copy reflects the project's known "duplicated General*/PID* tracks", not three independent users — so this is real-but-internal API, not dead code, and not a public API with outside consumers.

---

### Composition check (Phase 6)

Can `EllSequence.rel₄_swap₂₃` be derived from **mathlib** in ≤3 chained calls?

Attempt 1: route through a mathlib Pfaffian "alternating under transposition" lemma.
  - Mathlib decls used: none available — **mathlib has no Pfaffian** (Phase 5 [B][D]).
  - Result: **fails** — mathlib cannot even *state* `rel₄ W m n r s` (the symbol `rel₄` does not exist there), let alone prove the swap.

Attempt 2: derive directly from mathlib ring/antisymmetry primitives without `rel₄`.
  - The statement's two sides both mention `rel₄`, a project definition. Any "mathlib-only" derivation must first unfold `rel₄` and `addMulSub` — i.e. use the *project's* definitions — so it is not a mathlib composition.
  - The actual in-project proof is `simp_rw [rel₄, addMulSub_swap W neg s r]; ring`: it composes the project's own `rel₄` (def, line 103), the project's own `addMulSub_swap` (lemma, line 198), and mathlib's `ring`. That is a 2-call composition **of project API**, not of mathlib API (mathlib contributes only the closing `ring`).
  - Result: partial only in the trivial sense that `ring` is from mathlib; the load-bearing pieces are project-local.

Conclusion: **NOT-COMPOSABLE from mathlib.** Mathlib has neither the object (`rel₄`/`addMulSub`) nor the general abstraction (`Pfaffian`) needed to express or prove this. The lemma is composable only from the project's own definitions (which is exactly what the 1-line proof does).

---

## Verdict: `EllSequence.rel₄_swap₂₃`

**Category:** **NO-composable-from-mathlib**

**Evidence:**
- Literature search (Phase 3): the object is Stange / Junyan Xu's four-index elliptic relation `E(a,b,c,d)` — abstractly the 4×4 Pfaffian of `addMulSub`; the swap lemma is the standard "Pfaffian is alternating under transposition" instance, here for the (3 4) transposition. Source paper: arXiv:2604.05280 (formalized by this file).
- Generality analysis (Phase 4): **MAXIMALLY GENERAL** for its object (CommRing + arbitrary odd ℤ-sequence; oddness is essential). The only generalisation axis (state via an abstract Pfaffian, 4c row 7) is blocked because mathlib has no Pfaffian.
- Mathlib search (Phase 5): **not in mathlib** — `rel₄`, `addMulSub`, and `Pfaffian` are all absent (grep over the pinned mathlib tree, both the specific and the general form searched). The forked `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean` does not contain the `rel₄` layer. The only `_swap₂₃` in mathlib is the unrelated `oangle_swap₂₃_sign`.
- Composition check (Phase 6): **NOT-COMPOSABLE from mathlib** (mathlib cannot even state `rel₄`); it *is* a 1-line composition of the project's own `rel₄` + `addMulSub_swap` + `ring`.

**Rationale (1–2 paragraphs):**

`rel₄_swap₂₃` is internal sign-bookkeeping API for a bespoke definition. Mathematically it is the alternating property of a 4×4 Pfaffian, but the Pfaffian here is built from `addMulSub`, a hand-rolled definition that lives only in this elliptic-net development. Mathlib contains neither `rel₄`/`addMulSub` (0 declarations each; grep over the mathlib tree: nothing) nor any `Pfaffian` API at all (grep: nothing) to specialise from. The mathlib EDS file that this project forks (`Mathlib/NumberTheory/EllipticDivisibilitySequence.lean`) is entirely about the *normalized* recursion `preNormEDS`/`normEDS`/`complEDS` and has none of this relation machinery — so this is genuinely not a duplicate of anything upstream; it is a different layer that simply isn't in mathlib.

Because the very symbol `rel₄` is project-local, no sequence of mathlib calls can state — let alone prove — this lemma; the only "composition" is the project's own 1-line `simp_rw [rel₄, addMulSub_swap W neg s r]; ring`, which composes the project's own definition and its own antisymmetry lemma (mathlib contributes only the final `ring`). It is therefore not a mathlib lemma in waiting and not a mathlib-composable redundancy in the usual sense; it is a small, correct internal helper that should remain attached to its bespoke `rel₄`. Among the five buckets, `NO-composable-from-mathlib` is the right NO: do not add it to mathlib, keep it as project API, and note that its only "building blocks" are themselves project-local. It is emphatically **not** `NO-mathlib-has-it`: mathlib has neither the lemma nor the object. (This matches the sibling verdict for `rel₄_swap₁₂`, the analogous middle-transposition lemma; `rel₄_swap₀₁` was filed BORDERLINE only because that report weighed the trio's joint upstreamability, but the determinant — mathlib lacks `rel₄`/`addMulSub`/`Pfaffian` — is identical for all three, and for a standalone last-pair transposition the clean call is this NO.)

**WHY not (refactor-actionable):**
Mathlib does not have `rel₄`, so there is no mathlib decl to replace `rel₄_swap₂₃` with, and no inlining is possible at the one call site (`relFin4_perm:542`) — the call site genuinely needs a `rel₄`-level sign lemma for the (3 4) generator, and the proof is already minimal (`simp_rw [rel₄, addMulSub_swap …]; ring`). The "building blocks" of the proof are themselves project-local (`rel₄` def + `addMulSub_swap` lemma), not mathlib primitives.
Mathlib building blocks: **none applicable** (the only conceivable one, a Pfaffian alternating lemma, does not exist in mathlib).
Composition sketch (≤3 lines): the existing in-project proof IS the composition — `by simp_rw [rel₄, addMulSub_swap W neg s r]; ring` — but it composes project API, not mathlib, so there is nothing to inline-from-mathlib.
Call sites in our project (from Phase 6.0): K = 1 (`relFin4_perm`, same file), plus 2 duplicate copies in forked tracks (HasseWeil `Auxiliary/…Sequence.lean:437`, NagellLutz `…SequenceOriginal.lean:502`).
Refactor plan: **none against mathlib.** Keep `rel₄_swap₂₃` as project API exactly where it is. The genuinely actionable refactor is *intra-project de-duplication* (a cleanup-lane concern, not a mathlib concern): the three verbatim copies of the `rel₄_swap₀₁/₁₂/₂₃` trio (NagellLutz `…Sequence.lean`, NagellLutz `…SequenceOriginal.lean`, HasseWeil `Auxiliary/…Sequence.lean`) should be consolidated into one shared `Common/` module so the trio is defined once. That is the standard AINTLIB "duplicated tracks" dedup, orthogonal to mathlib inclusion.
Next action: do **not** submit to mathlib. Leave the lemma in place. (If one ever wanted it upstream, the prerequisite is a full `Matrix.pfaffian` development in mathlib + a port of the elliptic-net relation onto it — a large, separate effort, not this lemma.)

---

## Next step

Do not submit `EllSequence.rel₄_swap₂₃` to mathlib. It is correct, maximally general internal API for the project's bespoke `rel₄` (a 4×4 Pfaffian of `addMulSub`), and mathlib has neither the object nor a Pfaffian abstraction to host or replace it. The only follow-up is the routine AINTLIB cross-project de-duplication of the three forked copies of the `rel₄_swap*` trio into a shared module — a cleanup ticket, not a mathlib PR. Verdict is consistent with the sibling `rel₄_swap₁₂` assessment.
