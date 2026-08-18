# /mathlibable report — `EllSequence.HaveSameParity₄.addMulSub_transf`

_Step-9 single-declaration mathlibable assessment (AINTLIB /overview), NagellLutz project._
_Note: local Lean build is stale; verdict reasoned from the source statement + the full mathlib
checkout under `.lake/packages/mathlib` (authoritative) + WebSearch. ChatGPT MCP was down._

### Baseline (Phase 0)
- lake build:               n/a — build stale; reasoned from source + vendored mathlib tree
- decl `EllSequence.HaveSameParity₄.addMulSub_transf`: ✓ resolved at
  `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:270`
- qualified name (VERIFIED): `EllSequence.HaveSameParity₄.addMulSub_transf`
  (namespaces: `EllSequence` L90 → `HaveSameParity₄` L216; the parsed name in the prompt is correct)
- kind:                      lemma (Prop-valued; conjunction of six equalities)
- has sorry:                 no
- module docstring summary:  "Elliptic divisibility sequences (EDS): defines EDS and constructs
  normalised EDSs from initial terms." This file is a **fork+extension** of upstream
  `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean`, adding the `addMulSub`/`rel₄`/`net`/
  `HaveSameParity₄` apparatus (David Angdinata's machinery) to prove `normEDS` is elliptic — the
  upstream file's open TODO.

### Statement (Phase 1)

Let `R` be a commutative ring and `W : ℤ → R`. Define the proof-internal primitives:
- `addMulSub W m n = W((m+n) tdiv 2) · W((m−n) tdiv 2)` (Stange-net building block; `tdiv` = truncated ÷2),
- `addMulSub₄ W a b c d = W((a+b) tdiv 2) · W((c−d) tdiv 2)` (a "hybrid" cross-product),
- `avg₄ a b c d = (a+b+c+d)/2`,
- `HaveSameParity₄ a b c d` : the four integers share a common parity.

Under `same : HaveSameParity₄ a b c d`, `addMulSub_transf` asserts a **conjunction of six equalities**
identifying the `addMulSub` of pairs of *average-shifted* indices `(avg₄ − d, avg₄ − c, avg₄ − b,
|avg₄ − a|)` with the six `addMulSub₄` hybrid products on a permutation of `a b c d`:

```
addMulSub W (avg₄−d) (avg₄−c) = addMulSub₄ W a b c d   ∧
addMulSub W (avg₄−d) (avg₄−b) = addMulSub₄ W a c b d   ∧
addMulSub W (avg₄−d) |avg₄−a| = addMulSub₄ W b c a d   ∧
addMulSub W (avg₄−c) (avg₄−b) = addMulSub₄ W a d b c   ∧
addMulSub W (avg₄−c) |avg₄−a| = addMulSub₄ W b d a c   ∧
addMulSub W (avg₄−b) |avg₄−a| = addMulSub₄ W c d a b
```

Mathematical content: because `(avg₄−d)+(avg₄−c) = (a+b+c+d) − c − d = a+b` and
`(avg₄−d)−(avg₄−c) = c−d`, etc., the average-shifted indices recombine — inside `tdiv 2` — into the
original pairwise sums/differences. The `same`/`abs` only serve to discharge the parity bookkeeping
(`Even (a+b+c+d)` so `avg₄+avg₄ = a+b+c+d`, and `addMulSub_abs₁` kills the `|·|`). The proof is one
line: `simp_rw [addMulSub_abs₁, addMulSub, addMulSub₄, sub_add_sub_comm, same.avg₄_add_avg₄];
refine ⟨…⟩ <;> ring_nf`.

- Variables: `{R} [CommRing R] (W : ℤ → R)`, `{a b c d : ℤ}`.
- Hypotheses: `same : HaveSameParity₄ a b c d` (supplies `avg₄_add_avg₄`).
- Conclusion (math): six reindexing identities packaging `addMulSub`→`addMulSub₄`.
- Conclusion (Lean): a 6-fold `∧` of `addMulSub … = addMulSub₄ …` equalities.

### Size classification (Phase 2a)
Verdict: **SMALL**. Reason: a proof-internal helper lemma — not a `def`/`class`, not named after a
person/place, not a `## Main statement`. It is the algebraic glue feeding the very next theorem
(`rel₄_transf`). (Lit width still run exhaustively below.)

### One-line check (Phase 2b)
Kind is `lemma`, not `def`/`abbrev`/`structure` → n/a (one-liner check applies only to definitions).
Note for the record: the *proof body* is essentially one tactic line, reinforcing "helper, not result".

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                         | Query                                                                                          | Hit? | Standard form found | Notes |
|----|---------------------------------|------------------------------------------------------------------------------------------------|------|---------------------|-------|
| 1  | WebSearch (specific form)       | "elliptic net rel₄/addMulSub four-index relation transformation"                               | no   | —                   | The `net` *relation* is standard (Stange); the `addMulSub`→`addMulSub₄` reindexing is not a named result. |
| 2  | WebSearch (general form)        | Stange elliptic nets / Ward recurrence / EDS proof + Angdinata + Lean/mathlib                  | yes  | Stange net recurrence `W(p+q+s)W(p−q)W(r+s)W(r) + … = 0` | arXiv:0710.1316; Stange "Formulary"; matches the file's `net` def (L115–118) exactly. |
| 3  | WebSearch (named-after/aliases) | "Somos / Ward / Shipsey EDS recurrence", "On Elliptic Sequences over Commutative Rings"        | yes  | EDS three-term + net four-term relations | arXiv:2604.05280 (2026) acknowledges **Angdinata** for the division-polynomial problem — same circle. No "transf" identity surfaced. |
| 4  | ChatGPT MCP                     | "Is addMulSub_transf a named result; are addMulSub/rel₄/avg₄ library primitives?"              | n/a  | — (MCP down)        | Codex exec failed (prompt warned). Compensated by #1–#3, #6–#10. |
| 5  | Local references                | `.mathlib-quality/references/` and `refs/NagellLutz/` for "elliptic"/"Stange"                  | n/a  | —                   | No references dir / refs store present for this project (both absent). |
| 6  | nLab                            | "elliptic divisibility sequence", "elliptic net"                                               | no   | —                   | nLab has no EDS/elliptic-net page; not a categorical concept. |
| 7  | nCatLab                         | (categorical?)                                                                                 | n/a  | —                   | Not a categorical concept — a concrete integer-recurrence identity. |
| 8  | Stacks Project                  | "elliptic divisibility sequence"                                                               | n/a  | —                   | Not in Stacks scope (no EDS/division-polynomial recurrence material). |
| 9  | MathOverflow / MSE              | "elliptic net four-term relation reindexing average of indices"                                | no   | —                   | Net recurrence discussed; this specific six-way `addMulSub` repackaging is not. |
| 10 | recent arXiv (≤5 yrs)           | "elliptic nets symmetries / net polynomials valuations 2024–2026"                              | yes  | net recurrence + symmetry/periodicity results | arXiv:1408.6623, 2512.09601, 2604.05280 — the *relation* and its *symmetries* appear; no "transf" reindexing lemma named or cited standalone. |

### Literature summary (Phase 3)

Concept identified as: a **bespoke reindexing identity** internal to the `rel₄`/`net` formalisation of
the elliptic (Stange-net) relation for EDS. The surrounding objects map to the literature — `net`
(L115) is **verbatim Stange's elliptic-net defining recurrence**, and `rel₄`/`Rel₃` are the
four-/three-index elliptic relations (Ward, Stange "Formulary"). The `avg₄`-shift "transformation"
(`rel₄_transf`, which this lemma serves) is the move that realigns four same-parity indices so the net
relation applies — a known *manoeuvre* in the EDS-ellipticity proof, but not a separately-named theorem.
- Sources agree on the standard form of the **net relation**: yes.
- `addMulSub`, `addMulSub₄`, `avg₄`, and the six-fold `addMulSub_transf` identity: **no literature
  analog as standalone objects/results** — they are formalisation-specific intermediate constructions
  (the natural Lean factoring of the net/`rel₄` algebra; `tdiv 2` is an implementation device, per the
  L95–98 implementation note, to make `addMulSub_neg₀` hold unconditionally).
- Disagreement with the literature: none — it is *below* the literature's granularity (an arithmetic
  step inside a proof, not a stated proposition).

### Generality analysis — `addMulSub_transf`

Literature-standard form (from Phase 3): n/a — there is no literature statement to match; the lemma is
already at maximal natural generality for what it is (`R` an arbitrary `CommRing`, `W` an arbitrary
`ℤ → R`, indices arbitrary same-parity integers).

| # | Parameter / hypothesis            | Current Lean form        | Literature-standard form | Weaker form exists? | Reason |
|---|-----------------------------------|--------------------------|--------------------------|---------------------|--------|
| 1 | `[CommRing R]`                    | commutative ring         | n/a (no lit statement)   | NO                  | `ring_nf`/`addMulSub₄` need commutative multiplication; already the right base. |
| 2 | `W : ℤ → R`                       | arbitrary integer seq    | arbitrary                | NO                  | fully general; no positivity/divisibility assumed. |
| 3 | `same : HaveSameParity₄ a b c d`  | four same-parity ints    | n/a                      | NO                  | needed only for `avg₄_add_avg₄` (so `avg₄+avg₄ = a+b+c+d`); essential. |

### Generality verdict (Phase 4b)
The current form is: **MAXIMALLY GENERAL** (for its content). Weakening opportunities: 0. It is an
identity over an arbitrary commutative ring with an arbitrary integer-indexed sequence — there is
nothing to weaken. (This does **not** push toward YES: maximal generality of a *proof-internal* helper
does not make it a mathlib result.)

### Modern-idiom check (Phase 4c)

| #  | Question | Applies? | Proposed reformulation | Downstream |
|----|----------|----------|------------------------|------------|
| 1 | "let X be a foo" → typeclass? | no | — | hypotheses are already minimal data; nothing to classify. |
| 2 | sequences/metric → filters/topology? | no | — | a finite algebraic identity; no limiting/topological content. |
| 3 | construct → universal property? | no | — | nothing is being constructed; it's an equation. |
| 4 | set+closure-pred → bundled substructure? | no | — | n/a. |
| 5 | vector-space/field-specific → weaken typeclass? | no | — | already `CommRing`; can't go lower (needs ring mult + subtraction). |
| 6 | 1-categorical → higher-categorical? | no | — | n/a. |
| 7 | concrete index (ℤ) → arbitrary group? | no | — | EDS are intrinsically ℤ-indexed (Ward/Stange); generalising the index is not the EDS theory. |

Modern idiom available: **no**. Reason: this is a finite commutative-ring identity packaging six
`ring` facts; there is no contemporary mathlib reformulation that reorganises it — the modern idiom
question lives at the level of the *whole development* (see Phase 7), not this leaf.

### Diamond / defeq risk — (Phase 4.5)
n/a — declaration kind is `lemma` (no new definitional equalities or typeclass-search paths introduced).

### Mathlib search-status: `EllSequence.HaveSameParity₄.addMulSub_transf`

Searched the **full vendored mathlib tree** `.lake/packages/mathlib/Mathlib` (authoritative; the
project's current pin). Dedicated loogle/leansearch index tools are not exposed in this environment;
the source-grep over the actual checkout is the strongest available "is it in mathlib" check, and was
run for both the user's form and every underlying primitive.

```
[A] Lean-Finder       (not available in env)                              n/a: index tool not exposed
[B] Loogle            (not available in env)                              n/a: index tool not exposed
[C] LeanSearch        (not available in env)                              n/a: index tool not exposed
[D] Grep mathlib src  addMulSub / addMulSub₄ / rel₄ / net / HaveSameParity₄ / avg₄ / *_transf
                                                                           NO HITS (the only "net" grep
                      hits are the English word in NetEntropy/Cover/… — unrelated)
[E] Name pattern      "*transf*" across all of Mathlib                    NO HITS in NumberTheory or
                      AlgebraicGeometry/EllipticCurve (only TransfiniteIteration / Translate / prose)
```

Searched for both:
  - the user's form (`addMulSub_transf`) → absent;
  - the underlying primitives and the literature-standard `net` relation → the *relation* is the
    project's own `net`/`rel₄` (mirroring Stange), but mathlib's EDS file contains **none** of
    `addMulSub`/`rel₄`/`net`/`HaveSameParity₄`. Mathlib's
    `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean` stops at `IsEllSequence`/`preNormEDS`/
    `normEDS`/`complEDS`/`map_*` and **still carries the open TODO** "prove that a normalised sequence
    satisfying `IsEllDivSequence` can be given by `normEDS`" — i.e. the very ellipticity result this
    apparatus exists to prove is not yet upstream.

Concluded: **not in mathlib** (source-exhausted: the decl, all its primitives, and any `*_transf`
sibling are absent; the upstream EDS file's ellipticity TODO is open).

### Call sites — `EllSequence.HaveSameParity₄.addMulSub_transf`

Internal use count (this NagellLutz file, excluding the declaration): **1** — `rel₄_transf` at
`EllipticDivisibilitySequence.lean:283` (`obtain … := same.addMulSub_transf (W := W)`).
External-to-file callers (other files / other projects): **0** non-trivial.

| Caller file:line                                                  | Usage pattern |
|-------------------------------------------------------------------|---------------|
| NagellLutz/…/EllipticDivisibilitySequence.lean:283                | `obtain ⟨h₁,…,h₆⟩ := same.addMulSub_transf (W := W)` → into `rel₄_transf` |

Duplication across the repo's forked tracks (same lemma, copy-paste — **not** independent consumers):
- NagellLutz/…/EllipticDivisibilitySequenceOriginal.lean:259 (def) + :272 (its own `rel₄_transf`)
- HasseWeil/HasseWeil/Auxiliary/EllipticDivisibilitySequence.lean:226 (def) + :239 (its own `rel₄_transf`)

Inline-derivation grep (re-derived elsewhere without the lemma): none — every site that needs it is a
verbatim duplicate of the lemma+its single caller.

**Call-sites signal:** K = 1 internal use, 0 external, 0 inline re-derivation; the only other
occurrences are byte-for-byte duplicates of the lemma in the forked EDS tracks. Per the Phase-6 table
this is the "K = 1 internal use only → possibly the wrong abstraction / could be inlined; lean toward
NO-composable" pattern — except (crucial caveat) the composition is **not** from mathlib (see Phase 6),
so the honest reading is "proof-local helper of `rel₄_transf`", not a mathlib-composable.

### Composition check (Phase 6)

Can `addMulSub_transf` be derived from **mathlib** in ≤3 chained calls? **No.**

Attempt 1: `simp [addMulSub, addMulSub₄, …] ; ring`-style — but `addMulSub`, `addMulSub₄`, `avg₄`,
`HaveSameParity₄.avg₄_add_avg₄`, `addMulSub_abs₁` are **project-defined**, not mathlib. Mathlib supplies
only the genuinely-generic finishers (`ring`/`ring_nf`, `sub_add_sub_comm`, `Int.tdiv` lemmas, parity).
  - Mathlib decls usable: `ring_nf`, `sub_add_sub_comm`, `Int` div/parity API — these close the
    arithmetic *once the project definitions are unfolded*, but cannot state the lemma.
  - Result: **fails as a mathlib composition** — the statement itself is phrased entirely in
    project-only vocabulary.

Conclusion: **NOT-COMPOSABLE** (from mathlib). It is composable *from the project's own* `addMulSub`/
`addMulSub₄`/`avg₄` layer by a one-line `simp_rw; ring_nf`, which is exactly why it is a natural
proof-local helper rather than a standalone contribution.

## Verdict: `EllSequence.HaveSameParity₄.addMulSub_transf`

**Category:** **BORDERLINE-needs-human**

**Evidence:**
- Literature search (Phase 3): the surrounding `net`/`rel₄` *relation* is standard (Stange/Ward); this
  six-fold `addMulSub`→`addMulSub₄` reindexing identity has **no standalone literature name** — it is
  below the literature's granularity (a step in the EDS-ellipticity proof).
- Generality analysis (Phase 4): MAXIMALLY GENERAL; no modern-idiom reformulation at this leaf.
- Mathlib search (Phase 5): **not in mathlib** — the decl, all its primitives, and any `*_transf`
  sibling are absent; upstream EDS ellipticity is still an open TODO.
- Composition check (Phase 6): NOT-COMPOSABLE from mathlib (stated in project-only vocabulary);
  trivially composable from the project's own `addMulSub` layer.
- Call sites (Phase 6.0): K = 1 internal (`rel₄_transf`), 0 external; only duplicates elsewhere.

**Rationale.**
`addMulSub_transf` is a **proof-internal bookkeeping lemma**, not a self-standing mathematical result.
It bundles six `ring`-true equalities saying that the average-shifted indices `(avg₄−d, avg₄−c, …)`
recombine, inside `tdiv 2`, into the original pairwise sums/differences — pure glue consumed exactly
once, by the immediately-following `rel₄_transf`. No mathematician cites "these six addMulSub products
equal these six addMulSub₄ products"; they cite (at most) the *transformation-invariance of the
four-index relation* it feeds. So on its own it is clearly **not** `YES-add-as-is` (a one-use,
unnamed, sub-granularity helper), and `YES-but-generalise-first` does not apply (it is already maximal
and there is no better idiom for the leaf).

Yet the two NO buckets are also wrong, and that is the whole tension. `NO-mathlib-has-it` is false:
mathlib has neither this lemma nor any of its primitives (`addMulSub`/`rel₄`/`net`/`HaveSameParity₄`/
`avg₄`), and the upstream EDS file's ellipticity TODO — the very thing this apparatus proves — is
**open**. `NO-composable-from-mathlib` is false in the literal sense the bucket requires: the lemma is
phrased entirely in project-defined vocabulary, so there is no ≤3-line *mathlib* composition to inline
at the call site (the one-line proof composes from the project's own definitions, not mathlib's).
That mismatch — "mathlib doesn't have it, but it also isn't an upstreamable result on its own" — is
exactly what BORDERLINE exists for. The real question is a **packaging/policy** judgment the skill
cannot settle alone: the natural upstreaming unit is the *entire* David-Angdinata `rel₄`/`net`
EDS-ellipticity development (which would close mathlib's TODO), and within that PR `addMulSub_transf`
belongs as a `private`/proof-local helper of `rel₄_transf` — never as a standalone public lemma. Whether
to undertake that upstreaming, and at what helper granularity, is a human decision (and an AINTLIB-vs-
mathlib scope decision), not a five-bucket auto-pick on this single leaf.

**Numbered questions (≤5):**
1. Is the plan to **upstream the whole `EllSequence` apparatus** (`addMulSub`, `rel₄`, `net`,
   `HaveSameParity₄`, `…_transf`, culminating in `normEDS` ⇒ `IsEllDivSequence`) to mathlib, thereby
   closing the existing TODO in `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean`? (If **no** —
   AINTLIB-internal only — then this lemma simply stays put and the verdict is effectively
   NO-keep-local.)
2. If yes: are you content for `addMulSub_transf` to ship **as a `private` / proof-local helper of
   `rel₄_transf`** (it has exactly one use site and no independent name), rather than as a public
   mathlib lemma?
3. The lemma is **triplicated** (NagellLutz `…Sequence.lean` + `…Original.lean`, and HasseWeil
   `Auxiliary/EllipticDivisibilitySequence.lean`). Should the consolidation first **de-duplicate to a
   single shared copy** (e.g. under `Common/`) before any mathlib-direction decision? This is the more
   pressing cleanup action regardless of the mathlib answer.
4. Coordinate with upstream: arXiv:2604.05280 (2026, "On Elliptic Sequences over Commutative Rings")
   explicitly acknowledges Angdinata in this exact area — should the upstreaming be **deferred / aligned**
   to whatever EDS-ellipticity formalisation route lands in mathlib, to avoid a near-duplicate of the
   `net`/`rel₄` layer?

**Next action:** answer Q1–Q4. If Q1 is "no" (or Q3 is "consolidate first"), there is no per-leaf
mathlib action — fold this lemma into the shared EDS copy and stop. If Q1 is "yes", treat the **whole
`rel₄`/`net`/`HaveSameParity₄` development** as the upstreaming unit (a `/develop` → `/cleanup` →
mathlib-PR effort that closes the upstream TODO), with `addMulSub_transf` carried inside `rel₄_transf`'s
proof as a `private` helper — not as a standalone `/mathlibable` YES.

---

## Next step

Answer the four numbered questions above. The decisive fork is Q1 (upstream the entire EDS-ellipticity
apparatus, or keep AINTLIB-internal). This single leaf is never a standalone mathlib lemma either way;
the only per-leaf cleanup worth doing now is de-duplicating its three copies (Q3).
