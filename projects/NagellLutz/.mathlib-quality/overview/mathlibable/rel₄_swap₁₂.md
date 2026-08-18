# /mathlibable report — `EllSequence.rel₄_swap₁₂`

_Project: NagellLutz (Nagell–Lutz / elliptic divisibility sequences). Assessment run as part of `/overview` Step 9._

## Verdict (one line)

**NO-composable-from-mathlib** — internal sign-swap API for the project's bespoke `rel₄` (the 4×4 Pfaffian of `addMulSub`); neither `rel₄` nor `addMulSub` nor even `Pfaffian` exists in mathlib, so this lemma is not mathlib-shaped — it stays as project API.

---

### Baseline (Phase 0)
- lake build:               not re-run (build is stale per task note); reasoning from source. Decl elaborates in-tree (it is an established lemma with a 2-line proof, no `sorry`).
- decl `EllSequence.rel₄_swap₁₂`:  ✓ resolved at `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:520`
- qualified name:            **`EllSequence.rel₄_swap₁₂`** — VERIFIED. `namespace EllSequence` opens at line 90; the `HaveSameParity₄` namespace (216–297) and `Rel₄OfValid` section (…–507) are both closed before line 520; no nested namespace is open at 520. The parsed guess matches.
- kind:                      `lemma`
- has sorry:                 no
- module docstring summary:  Develops Stange's elliptic-net relations (`addMulSub`, `rel₄`, `net`) over a commutative ring and proves the equivalence with elliptic divisibility sequences — the algebraic core of the Nagell–Lutz formalization. Follows Junyan Xu, *On Elliptic Sequences over Commutative Rings* (arXiv:2604.05280).

---

### Statement (Phase 1)

`EllSequence.rel₄_swap₁₂` states that swapping the 2nd and 3rd arguments of the four-index elliptic relation `rel₄` negates it, provided `W` is an odd function:

> For a commutative ring `R`, a sequence `W : ℤ → R` satisfying `W (-k) = -W k` for all `k`, and integers `m, n, r, s`:
> `rel₄ W m n r s = - rel₄ W m r n s`.

Here `rel₄ W a b c d = f(a,b)·f(c,d) − f(a,c)·f(b,d) + f(a,d)·f(b,c)` where `f = addMulSub W`, and `addMulSub W m n = W ((m+n).tdiv 2) · W ((m−n).tdiv 2)`. When `W` is odd, `addMulSub` is antisymmetric (`addMulSub_swap`: `f(m,n) = −f(n,m)`).

**Mathematical identity.** `rel₄ W a b c d` is exactly the **4×4 Pfaffian** of the antisymmetric matrix `M_{ij} = f(x_i,x_j)` with `(x₁,x₂,x₃,x₄)=(a,b,c,d)`: `Pf(M) = M₁₂M₃₄ − M₁₃M₂₄ + M₁₄M₂₃`. The docstring's "three partitions of four indices into two pairs" is the textbook description of the three perfect matchings of `K₄` summed by the 4×4 Pfaffian. So `rel₄_swap₁₂` is an instance of the standard *Pfaffian is alternating in the underlying points* property, applied to this bespoke matrix.

Variables / typeclasses (Lean side):
- `{R : Type u} [CommRing R]` — the coefficient ring (mathematical role: ring the sequence lands in).
- `(W : ℤ → R)` — the sequence (the elliptic-net values).
- `(neg : ∀ k, W (-k) = -W k)` — hypothesis that `W` is an odd function (an `include`d section variable).
- `{m n r s : ℤ}` — the four indices.

Hypotheses (Lean side):
- `neg : ∀ k, W (-k) = -W k` — oddness of `W`; this is what makes `addMulSub` antisymmetric and hence what makes the transposition flip the sign.

Conclusion (math): swapping arguments 2 and 3 of `rel₄` negates it.
Conclusion (Lean): `rel₄ W m n r s = - rel₄ W m r n s`.

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: A structural helper lemma — one of three adjacent-transposition sign lemmas (`rel₄_swap₀₁`, `rel₄_swap₁₂`, `rel₄_swap₂₃`) feeding the `Submonoid.closure_induction` in `relFin4_perm`. Not a named theorem, not a `## Main results` entry, no person/place attached to *this* lemma. (Its consumer `relFin4_perm` — "`rel₄` is `Sₙ`-invariant up to sign" — is the meatier statement, but even that is internal API for a bespoke object.)

(Note: literature width was EXHAUSTIVE regardless.)

### One-line check (Phase 2b)

Kind is `lemma`, not a `def`/`abbrev`/`structure` — the one-liner heuristic is about definitions, so this check is **n/a**. (For the record the proof body is 2 lines: `simp_rw [rel₄, addMulSub_swap W neg r n]; ring`.)

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                                  | Hit? | Standard form found              | Notes |
|----|----------------------------------|--------------------------------------------------------------------------------------------------------|------|----------------------------------|-------|
|  1 | WebSearch (specific form)        | Stange elliptic net rel4, three partitions of four indices into two pairs, antisymmetric / permutation sign | yes  | The 4-index elliptic-net relation; "three ways to partition four factors into two pairs"; each partition leaves the product invariant up to transformation | researchgate (Semaev↔Stange); arXiv:0710.1316 (Stange, *Elliptic nets and elliptic curves*) |
|  2 | WebSearch (general form)         | EDS / Somos four-term relation, alternating sign under permutation, Pfaffian, three-term Plücker, Desnanot–Jacobi | yes  | The bilinear `s_{n+2}s_{n-2}=A s_{n+1}s_{n-1}+B s_n²` Somos form; 4×4 Pfaffians generate the Plücker ideal of a generic skew matrix | arXiv:math/0412293 (Hone, every Somos-4 is Somos-k); arXiv:math/0312358 (Pfaffian/Plücker) — confirms the alternating quartic = Pfaffian template |
|  3 | WebSearch (named-after / aliases)| "elliptic net" Stange symmetry / permutation of indices; net polynomials                               | yes  | "On Symmetries of Elliptic Nets and Valuations of Net Polynomials" (arXiv:1408.6623); recurrence `Ω…Ω + Ω…Ω + Ω…Ω = 0` is the antisymmetric 3-term form | symmetry of nets is studied, but as net-specific identities, not a general named lemma |
|  4 | WebSearch (source paper)         | arXiv:2604.05280 — *On Elliptic Sequences over Commutative Rings* (Junyan Xu)                          | yes  | Defines `E(a,b,c,d): h_{a+b}h_{a-b}h_{c+d}h_{c-d} = h_{a+c}h_{a-c}h_{b+d}h_{b-d} − h_{b+c}h_{b-c}h_{a+d}h_{a-d}`, a "highly symmetric family of homogeneous quartic relations" | **This is the paper the file formalizes** (same author as mathlib's EDS file). `rel₄` is the formalization of `E`; its sign-under-permutation is exactly the symmetry discussed here. |
|  5 | ChatGPT MCP                      | self-contained question: is `rel₄` a named object (Pfaffian/determinant/Plücker), and would a general mathlib lemma give the sign-swap for free? | n/a  | —                                | **MCP server down** (Codex exec failed — matches the task's "ChatGPT MCP may be down" note). Fallback: reasoned the Pfaffian identification directly (see Phase 1) and corroborated via WebSearch #2 (Pfaffian/Plücker) and loogle (no `Pfaffian` in mathlib). |
|  6 | nLab                             | Pfaffian / elliptic net                                                                                | yes (Pfaffian) / no (net) | nLab has "Pfaffian" (alternating, `Pf² = det`); no elliptic-net page | Confirms the *general* object (Pfaffian of a skew form) is standard and alternating; the elliptic-net specialization is not an nLab concept |
|  7 | nCatLab (categorical)            | —                                                                                                      | n/a  | —                                | Not a categorical concept — it is a polynomial identity in a commutative ring. |
|  8 | Stacks Project (alg geom)        | —                                                                                                      | n/a  | —                                | Not an algebraic-geometry/scheme concept; it is an elementary identity about a sequence. (EDS appear in arithmetic but this sign lemma is pure algebra.) |
|  9 | MathOverflow / Math.SE           | (covered by #1–#3 web sweep)                                                                            | partial | Discussion of elliptic-net relations and Somos/Pfaffian structure exists but no canonical "transposition negates the 4-index relation" lemma | The fact is folklore-level once you see it is a Pfaffian. |
| 10 | recent arXiv (last 5 yr)         | arXiv:2604.05280 (2026), arXiv:2512.09601 (2025, valuations of elliptic nets), arXiv:1702.08102 (signs in elliptic nets) | yes  | Sign behavior of elliptic nets is actively studied; `E(a,b,c,d)` is the current standard form | The source paper itself is the most recent and authoritative statement of the relation. |

### Literature summary (Phase 3)

Concept identified as: the **four-index elliptic(-net) relation** `E(a,b,c,d)` of Stange / Junyan Xu — equivalently the **4×4 Pfaffian** `Pf(M)=M₁₂M₃₄−M₁₃M₂₄+M₁₄M₂₃` of the antisymmetric matrix `M_{ij}=addMulSub(x_i,x_j)`.
Sources agree on the standard form: yes — the "three partitions of four indices into two pairs" quartic is the consistent form (Stange 2007/2011; Xu 2026). The sign-under-transposition is, abstractly, the alternating property of the Pfaffian.
Most general standard form: the Pfaffian of any `2n×2n` antisymmetric matrix is alternating in its underlying index set; transposing two points negates it. The elliptic-net relation is the `n=2` (4×4) case with the specific entries `addMulSub`.
Generality dimensions where the literature varies:
  - underlying object: from "the elliptic-net relation `E`" (very specific) up to "Pfaffian of a skew form" (fully general) up to "Grassmann–Plücker relation". The most general is the Pfaffian/Plücker statement.
  - sequence vs. ring: classical EDS over ℤ → general odd sequence `W : ℤ → R` over a commutative ring (the project is already at the general end).
Disagreement with the literature: none. `rel₄_swap₁₂` is a correct, literature-consistent instance of "Pfaffian/elliptic-relation is alternating under transposition".

---

### Generality analysis — `EllSequence.rel₄_swap₁₂`

Literature-standard form (from Phase 3): the alternating property of the 4×4 Pfaffian of a skew matrix (or, in this development's terms, the antisymmetry of `rel₄` under a transposition of its four arguments).

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
|  7 | concrete index ℕ/ℤ/ℝ → arbitrary monoid/group?                                                           | partial  | (the *relation* could be the Pfaffian of an abstract skew matrix) | **This is the real modernisation axis: state `rel₄` as `Matrix.pfaffian` of `addMulSub`, then "swap negates" would be a corollary of a general `pfaffian_alternating`-style lemma.** BUT mathlib has **no `Pfaffian`** (loogle: unknown identifier) — so the modern idiom does not exist to target. |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no** (not actionably).
One-line reason: The only contemporary reformulation is "`rel₄` = `Matrix.pfaffian` of the skew matrix `addMulSub`, with the swap lemma a specialization of `pfaffian` alternating-ness", but **mathlib has no Pfaffian API at all** (confirmed: `grep -r Pfaffian Mathlib/` and loogle both empty). So there is no mathlib-idiomatic target to restate against; building Pfaffian theory is a large independent contribution, far out of scope for this sign lemma. The lemma's *name* (`…_swap₁₂`) already follows mathlib's transposition-sign idiom (cf. `oangle_swap₁₂_sign` in `Mathlib/Geometry/Euclidean/Angle/Oriented/Affine.lean`), so the naming is already modern; only the underlying object is bespoke.

---

### Diamond / defeq risk — Phase 4.5

n/a — declaration kind is `lemma` (proves a propositional equation; introduces no definitional equalities, instances, or typeclass-search paths).

---

### Mathlib search-status: `EllSequence.rel₄_swap₁₂`

[A] Lean-Finder       — (endpoint unavailable this run)                              n/a: covered by [B][C][D][E]
[B] Loogle            `Pfaffian`; `"addMulSub"`; `"rel₄"`                              **no hits**: `Pfaffian` → "unknown identifier" (not in mathlib); `addMulSub` → 0 decls; `rel₄` → 0 decls
[C] LeanSearch        "alternating expression negated under transposition of two args" via leansearch.net API   n/a: endpoint returned HTTP 404 (index moved); substituted with [B] loogle + [D] grep, which are definitive for "does this name/object exist"
[D] Grep mathlib src  `rel₄` / `addMulSub` / `relFin4` / `namespace EllSequence` / `[Pp]faffian` over `.lake/packages/mathlib/Mathlib/`  **no hits** for any (the `EllSequence` substring appears only inside `IsEllSequence` in `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean`, which has **none** of `rel₄`/`addMulSub`/`net`) |
[E] Name pattern      `_swap₁₂` / `_swap12` over mathlib                              only hit: `oangle_swap₁₂_sign` (oriented-angle geometry) — **same naming idiom, unrelated object** (it is about `EuclideanGeometry`'s `∡`, not `rel₄`)

Searched for both:
  - the user's current form (`rel₄_swap₁₂` about `rel₄`/`addMulSub`) → absent.
  - the literature-standard / general form (Pfaffian of a skew matrix, alternating under transposition) → **mathlib has no Pfaffian whatsoever**, so the general form is also absent.

Concluded: **not in mathlib** (all methods exhausted: loogle on the object names + on `Pfaffian`, grep over mathlib source, name-pattern, and the general-form Pfaffian search all negative). The forked mathlib file `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean` is entirely about `preNormEDS`/`normEDS`/`complEDS` and contains none of the `rel₄` machinery — confirming the project's `rel₄`/`addMulSub`/permutation layer is net-new and not upstream.

---

### Call sites — `EllSequence.rel₄_swap₁₂`

Internal use count (NagellLutz, excluding the declaring line 520): **1**
External-to-file callers (within NagellLutz `LutzNagell/`): the single use is **in the same file** (`relFin4_perm`).

| Caller file:line                                                                 | Usage pattern (one-line excerpt)                                   |
|----------------------------------------------------------------------------------|--------------------------------------------------------------------|
| `…/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:542`                  | `exacts [rel₄_swap₀₁ neg, rel₄_swap₁₂ neg, rel₄_swap₂₃ neg]` — supplies the three adjacent-transposition base cases to `Submonoid.closure_induction` inside `relFin4_perm` (the "`rel₄` is permutation-invariant up to sign" theorem) |

Cross-project / duplicate copies (same forked code, NOT independent consumers):
  - `…/HasseWeil/HasseWeil/Auxiliary/EllipticDivisibilitySequence.lean:434` (verbatim duplicate definition; used at its own line 458)
  - `…/NagellLutz/LutzNagell/EllipticDivisibilitySequenceOriginal.lean:499` (a stale/"original" copy in the same project; used at its own line 519)

Inline-derivation grep (was the equivalent re-derived elsewhere without using this lemma?): (none) — every place that needs the sign-swap calls one of the three `rel₄_swap*` lemmas; nobody inlines `simp_rw [rel₄, addMulSub_swap …]; ring` at a call site.

**Reading.** K = 1 internal use, no inline re-derivation. Per the call-site table, K=1 leans toward "could be inlined / wrong abstraction" in general — but here it is one of a *matched trio* (`swap₀₁`/`swap₁₂`/`swap₂₃`) that exists precisely to be the three generators handed to `closure_induction`; splitting the trio would be unnatural. The duplication across HasseWeil + the `…Original` copy reflects the project's known "duplicated General*/PID* tracks", not three independent users — so this is real-but-internal API, not dead code, and not a public API with outside consumers.

---

### Composition check (Phase 6)

Can `EllSequence.rel₄_swap₁₂` be derived from **mathlib** in ≤3 chained calls?

Attempt 1: route through a mathlib Pfaffian "alternating under transposition" lemma.
  - Mathlib decls used: none available — **mathlib has no Pfaffian** (Phase 5 [B][D]).
  - Result: **fails** — mathlib cannot even *state* `rel₄ W m n r s` (the symbol `rel₄` does not exist there), let alone prove the swap.

Attempt 2: derive directly from mathlib ring/antisymmetry primitives without `rel₄`.
  - The statement's two sides both mention `rel₄`, a project definition. Any "mathlib-only" derivation would first have to unfold `rel₄` and `addMulSub` — i.e. use the *project's* definitions — so it is not a mathlib composition.
  - The actual in-project proof is `simp_rw [rel₄, addMulSub_swap W neg r n]; ring`: it composes the project's own `rel₄` (def), the project's own `addMulSub_swap` (lemma), and mathlib's `ring`. That is a 2-call composition **of project API**, not of mathlib API.
  - Result: partial only in the trivial sense that `ring` is from mathlib; the load-bearing pieces are project-local.

Conclusion: **NOT-COMPOSABLE from mathlib.** Mathlib has neither the object (`rel₄`/`addMulSub`) nor the general abstraction (`Pfaffian`) needed to express or prove this. The lemma is composable only from the project's own definitions (which is exactly what the 2-line proof does).

---

## Verdict: `EllSequence.rel₄_swap₁₂`

**Category:** **NO-composable-from-mathlib**

**Evidence:**
- Literature search (Phase 3): the object is Stange / Junyan Xu's four-index elliptic relation `E(a,b,c,d)` — abstractly the 4×4 Pfaffian of `addMulSub`; the swap lemma is the standard "Pfaffian is alternating under transposition" instance. Source paper: arXiv:2604.05280 (formalized by this file).
- Generality analysis (Phase 4): **MAXIMALLY GENERAL** for its object (CommRing + arbitrary odd ℤ-sequence; oddness is essential). The only generalisation axis (state via an abstract Pfaffian, 4c row 7) is blocked because mathlib has no Pfaffian.
- Mathlib search (Phase 5): **not in mathlib** — `rel₄`, `addMulSub`, and `Pfaffian` are all absent (loogle + grep, both forms searched). The forked `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean` does not contain the `rel₄` layer.
- Composition check (Phase 6): **NOT-COMPOSABLE from mathlib** (mathlib cannot even state `rel₄`); it *is* a 2-line composition of the project's own `rel₄` + `addMulSub_swap` + `ring`.

**Rationale (1–2 paragraphs):**

`rel₄_swap₁₂` is internal sign-bookkeeping API for a bespoke definition. Mathematically it is the alternating property of a 4×4 Pfaffian, but the Pfaffian here is built from `addMulSub`, a hand-rolled definition that lives only in this elliptic-net development. Mathlib contains neither `rel₄`/`addMulSub` (loogle: 0 declarations each; grep over the mathlib tree: nothing) nor any `Pfaffian` API at all (loogle: "unknown identifier 'Pfaffian'"; grep: nothing) to specialise from. The mathlib EDS file that this project forks (`Mathlib/NumberTheory/EllipticDivisibilitySequence.lean`) is entirely about the *normalized* recursion `preNormEDS`/`normEDS`/`complEDS` and has none of this relation machinery — so this is genuinely not a duplicate of anything upstream; it is a different layer that simply isn't in mathlib.

Because the very symbol `rel₄` is project-local, no sequence of mathlib calls can state — let alone prove — this lemma; the only "composition" is the project's own 2-line `simp_rw [rel₄, addMulSub_swap W neg r n]; ring`, which composes the project's own definition and its own antisymmetry lemma (mathlib contributes only the final `ring`). It is therefore not a mathlib lemma in waiting and not a mathlib-composable redundancy in the usual sense; it is a small, correct internal helper that should remain attached to its bespoke `rel₄`. The honest bucket is NO-composable-from-mathlib: it is composed from the project's own primitives, and there is nothing to upstream and nothing in mathlib to replace it with. (Strictly, "composable from mathlib" is only *partly* apt — mathlib lacks the object entirely — but among the five buckets this is the correct NO: do not add it to mathlib; keep it as project API. It is emphatically **not** NO-mathlib-has-it: mathlib has neither the lemma nor the object.)

**WHY not (refactor-actionable):**
Mathlib does not have `rel₄`, so there is no mathlib decl to replace `rel₄_swap₁₂` with, and no inlining is possible at the one call site (`relFin4_perm:542`) — the call site genuinely needs a `rel₄`-level sign lemma, and the proof is already minimal (`simp_rw [rel₄, addMulSub_swap …]; ring`). The "building blocks" of the proof are themselves project-local (`rel₄` def + `addMulSub_swap` lemma), not mathlib primitives.
Mathlib building blocks: **none applicable** (the only conceivable one, a Pfaffian alternating lemma, does not exist in mathlib).
Composition sketch (≤3 lines): the existing in-project proof IS the composition — `by simp_rw [rel₄, addMulSub_swap W neg r n]; ring` — but it composes project API, not mathlib, so there is nothing to inline-from-mathlib.
Call sites in our project (from Phase 6.0): K = 1 (`relFin4_perm`, same file), plus 2 duplicate copies in forked tracks (HasseWeil, `…Original`).
Refactor plan: **none against mathlib.** Keep `rel₄_swap₁₂` as project API exactly where it is. The genuinely actionable refactor is *intra-project de-duplication* (a cleanup-lane concern, not a mathlib concern): the three verbatim copies (NagellLutz `…Sequence.lean`, NagellLutz `…SequenceOriginal.lean`, HasseWeil `Auxiliary/…Sequence.lean`) should be consolidated into one shared `Common/` module so the trio `rel₄_swap₀₁/₁₂/₂₃` is defined once. That is the standard AINTLIB "duplicated tracks" dedup, orthogonal to mathlib inclusion.
Next action: do **not** submit to mathlib. Leave the lemma in place. (If one ever wanted it upstream, the prerequisite is a full `Matrix.pfaffian` development in mathlib + a port of the elliptic-net relation onto it — a large, separate effort, tracked as a hypothetical future contribution, not this lemma.)

---

## Next step

Do not submit `EllSequence.rel₄_swap₁₂` to mathlib. It is correct, maximally general internal API for the project's bespoke `rel₄` (a 4×4 Pfaffian of `addMulSub`), and mathlib has neither the object nor a Pfaffian abstraction to host or replace it. The only follow-up is the routine AINTLIB cross-project de-duplication of the three forked copies into a shared module — a cleanup ticket, not a mathlib PR.
