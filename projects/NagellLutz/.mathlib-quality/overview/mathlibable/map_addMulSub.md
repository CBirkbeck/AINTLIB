# /mathlibable report — `map_addMulSub`

> Step-9 mathlibable assessment, NagellLutz project (Nagell–Lutz; elliptic curves;
> division polynomials; elliptic divisibility sequences / Stange elliptic nets).

### Baseline (Phase 0)
- lake build:               ⚠ not re-run (local build stale per task brief); decl read directly from source.
- decl `map_addMulSub`:     ✓ resolved at `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:1162`.
- kind:                     `lemma`.
- has sorry:                no (proof is `by simp_rw [addMulSub, map_mul, Function.comp]`).
- module docstring summary: the file defines elliptic divisibility sequences (EDS) and builds
  normalised EDSs from initial terms; it **forks** `Mathlib.NumberTheory.EllipticDivisibilitySequence`
  and extends it with Stange's elliptic-net machinery (`addMulSub`, `rel₄`, `net`, `invarNum`, …)
  that is **not** in mathlib.

**Qualified name (VERIFIED):** `map_addMulSub` (root / top-level namespace).
Namespace audit at line 1162: the first `namespace EllSequence` (opened line 90) closed at line 597;
a second `namespace EllSequence` (line 1079) closed at line 1112; `section Map` (line 1116) opens **no**
namespace. Open-namespace depth at line 1162 = 0, so the lemma is top-level. The bare `addMulSub` in
its statement resolves through a file-level `open EllSequence` (line 599), but the lemma *itself* is
**not** in the `EllSequence` namespace — contrast lines 1140/1152 where the author wrote
`lemma EllSequence.map_compl'` / `lemma EllSequence.map_compl` *explicitly* and deliberately did **not**
do so for `map_addMulSub`. Parsed name `map_addMulSub` was therefore correct (it is **not**
`EllSequence.map_addMulSub`).

---

### Statement (Phase 1)

`map_addMulSub` is a **naturality / functoriality** fact: a ring homomorphism commutes with the basic
two-factor building block `addMulSub` of the elliptic relations.

With `addMulSub` defined (line 94) by

  addMulSub(W, m, n) = W((m+n) tdiv 2) · W((m−n) tdiv 2)

(using `Int.tdiv _ 2`, not `_ / 2`, so that `(−m).tdiv 2 = −(m.tdiv 2)` and the sign lemmas hold
unconditionally), the lemma asserts, for a ring hom `f : R → S`, sequence `W : ℤ → R`, integers `m n`:

  f( addMulSub(W, m, n) ) = addMulSub(f ∘ W, m, n).

Mathematically: `addMulSub` is a **product of two values of `W`**, i.e. a ℤ-polynomial (in fact a
single degree-2 monomial) in the values of `W`; a ring hom preserves `×`, so it passes straight
through. This is the atomic case of the whole `map_*` family in this file — `map_rel₄`, `map_net`,
`map_invarNum`, `map_invarDenom` all reduce to it (line 1166: `map_rel₄` is
`simp_rw [rel₄, map_add, map_sub, map_mul, map_addMulSub]`).

Variables / typeclasses (Lean side, from the file header lines 85–86):
- `{R S} [CommRing R] [CommRing S]` — source/target commutative rings.
- `(W : ℤ → R)` — the sequence.
- `{F} [FunLike F R S] [RingHomClass F R S] (f : F)` — a **bundled-class** ring hom (not bare `R →+* S`).
- `(m n : ℤ)` — the two indices.

Hypotheses: none (unconditional). Note the `tdiv` design means the lemma needs no parity assumption on
`m, n`.

Conclusion (Lean): `f (addMulSub W m n) = addMulSub (f ∘ W) m n`.

---

### Size classification (Phase 2a)

Verdict: **SMALL**.
Reason: a glue/naturality `map_*` lemma whose body is a single `simp_rw`; not a new structure, not a
named theorem, not a `## Main results` entry. (Literature width was nonetheless run EXHAUSTIVE, as the
whole elliptic-net layer is the real object of interest.)

### One-line check (Phase 2b)

Kind is `lemma`, not `def`/`abbrev`/`structure`, so the one-liner gate (which biases *definitions*
toward NO) does not apply. Recorded note: the **proof** is literally one substantive line
(`simp_rw [addMulSub, map_mul, Function.comp]`) — the statement is trivial plumbing — but Phase 2b
imposes no constraint on lemmas.

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                                       | Hit? | Standard form found                              | Notes |
|----|----------------------------------|-------------------------------------------------------------------------------------------------------------|------|--------------------------------------------------|-------|
|  1 | WebSearch (specific form)        | EDS net polynomial ring homomorphism base change naturality `W((m+n)/2)W((m−n)/2)`                          | partial | EDS recurrence + "elliptic nets generalise EDS; net polynomials in coeffs of E and Pᵢ"; the specific `W((m±n)/2)` product / its naturality **not** a named result | arXiv math/0402415 (sign of EDS), msp ANT 2008, arXiv 1108.3051, Warwick CM-EDS notes |
|  2 | WebSearch (named-after Stange)   | Stange elliptic nets `addMulSub` building-block four-index relation `W(m+n/2)W(m−n/2)`                       | yes  | **exact net relation** `W(p+q+s)W(p−q)W(r+s)W(r)+…=0` returned; `addMulSub` is its atomic factor | arXiv 0710.1316, eprint 2006/392, Stange *Formulary for EDS and elliptic nets*, arXiv 0803.0728, 2512.09601 |
|  3 | WebSearch (formalization/Lean)   | "division polynomial"/"net polynomial" base-change ring-hom naturality lemma elliptic curve Lean mathlib    | partial | mathlib has division-/net-poly defs + `@[simp] map_*` EDS lemmas; **no** named "naturality of the addMulSub factor" | mathlib4_docs `EllipticDivisibilitySequence`, `DivisionPolynomial.Basic` |
|  4 | ChatGPT MCP                      | Is `f(addMulSub W m n)=addMulSub (f∘W) m n` citable, or trivial ring-hom-commutes-with-a-product?           | n/a  | (MCP **down** — task brief warned; Codex unavailable) | fell back to WebSearch ×3 + mathlib-source precedent |
|  5 | Local references                 | `.mathlib-quality/references/` for "addMulSub"/"naturality"/"map"                                            | n/a  | refs are local-only & gitignored; none surfaced  | recorded n/a |
|  6 | nLab                             | "elliptic divisibility sequence" / "elliptic net"                                                            | n/a  | no nLab page; the concept is arithmetic-geometry, not categorical | the naturality is the generic "monomial functor preserves ring maps" — folklore |
|  7 | nCatLab                          | —                                                                                                           | n/a  | not a categorical concept beyond "natural in the ring" | — |
|  8 | Stacks Project                   | elliptic net / division polynomial                                                                          | n/a  | no EDS/elliptic-net chapter | wrong venue |
|  9 | MathOverflow / MSE               | (covered by #1–#3; no thread isolates the naturality of the `addMulSub` factor as a stated lemma)           | n/a  | —                                                | used implicitly, never highlighted |
| 10 | recent arXiv (≤5y)               | elliptic nets over commutative rings / valuations / CM (2512.09601, 2604.05280)                              | yes  | EDS/nets treated over general commutative rings; the `map_*`/base-change step is used implicitly | confirms `[CommRing R]` is the standard general setting |

Protocol pass: WebSearch ran 3 queries at different generality levels (specific factor, named-after-
Stange, formalization). ChatGPT MCP attempted and recorded down with fallback. Local refs, nLab,
nCatLab, Stacks, MathOverflow/MSE, recent arXiv each checked or `n/a` with reason.

### Literature summary (Phase 3)

Concept identified as: the **naturality, under a ring homomorphism, of the basic two-factor block
`addMulSub`** — the `W((m+n)/2)·W((m−n)/2)` monomial that is the atom of Stange's elliptic-net
relation. WebSearch #2 returned the elliptic-net relation verbatim and confirms `addMulSub` is exactly
the product appearing in each term.
Sources agree on the standard form of the *relation*: yes. The **naturality** of the `addMulSub`
factor itself is never a named/citable theorem — it is the folklore "a ring hom commutes with a
product / a ℤ-polynomial expression," invoked implicitly whenever one base-changes an EDS / net
polynomial (e.g. specialising the universal net polynomial via `aeval`).
Most general standard form: for any `CommRing` map `f : R → S`, `f` commutes with any ℤ-polynomial
combination of the `W` values; `addMulSub` is the simplest such (a single monomial of degree 2).
Generality dimensions where the literature varies:
  - coefficient ring: ℤ (classical EDS) up to **arbitrary commutative rings** (arXiv 2604.05280); the
    project's `[CommRing R]` is already at the general end.
  - the map: literature says "a ring homomorphism" generally; the project uses the **bundled-class**
    `[RingHomClass F R S]`, *more* general than a bare `R →+* S` (covers `AlgHom`, `RingEquiv`, …).
Disagreement with the literature: none.

---

### Generality analysis — `map_addMulSub`

Literature-standard form (Phase 3): `f` commutes with the `addMulSub` product, for `f` any ring hom
and `R, S` any commutative rings — exactly the project's statement.

| # | Parameter / hypothesis                          | Current Lean form                | Literature-standard form | Weaker form exists? | Reason |
|---|-------------------------------------------------|----------------------------------|--------------------------|---------------------|--------|
| 1 | `[CommRing R] [CommRing S]`                      | commutative rings                | commutative rings        | NO (already maximal)| `addMulSub` is a product in `R`/`S`; one needs a (comm) ring on both sides. mathlib's own `map_normEDS` family also fixes `CommRing`. |
| 2 | `[FunLike F R S] [RingHomClass F R S] (f : F)`  | bundled ring-hom class           | "a ring homomorphism"    | NO (already maximal)| class form is **strictly more general** than `R →+* S`; the modern mathlib idiom. |
| 3 | `(W : ℤ → R)`                                    | sequence on ℤ                    | sequence on ℤ            | NO                  | indices are genuine integers (`(m+n).tdiv 2`, `(m−n).tdiv 2`); domain is intrinsically ℤ. |
| 4 | `(m n : ℤ)`                                      | two integer indices              | two integer indices      | NO                  | the block is defined on integer index-pairs. |

Note: although only `map_mul` is actually used in the proof (`addMulSub` is a single product), the
**commutative-ring** ambient is dictated by the surrounding EDS file and matches mathlib's own EDS
`map_*` lemmas; narrowing the typeclass to e.g. `MulHomClass`/`Mul` would *diverge* from the family
for no gain (the lemma must sit beside `map_rel₄`/`map_net`, which genuinely need `+`,`−`,`×`).
Recorded as "borderline / not worth diverging," exactly as the sibling `map_invarNum` report notes.

### Generality verdict (Phase 4b)

Current form is: **MAXIMALLY GENERAL** (for its intended home beside the EDS family).
Weakening opportunities found: 0 meaningful. It is already *more* general than mathlib's own analogous
`map_normEDS` (which fixes `f : R →+* S`): `map_addMulSub` uses `RingHomClass F R S`.
Proposed restatement: none.
Cost of restatement: n/a.

### Modern-idiom check (Phase 4c)

| #  | Question                                                            | Applies? | Proposed reformulation | Mathlib downstream |
|----|--------------------------------------------------------------------|----------|------------------------|--------------------|
|  1 | "let X be a foo" preamble → typeclass?                              | no       | already `RingHomClass` typeclass hypothesis | — |
|  2 | sequences/metric → filters/topology?                               | no       | purely algebraic identity | — |
|  3 | construct an object → universal-property class?                    | no       | it's an equation about a fixed expression | — |
|  4 | set-with-closure → bundled substructure?                           | no       | no substructure | — |
|  5 | field/vector-space-specific → weaken typeclass?                    | no       | already `CommRing` (could be looser for *this* lemma alone, but see Phase 4b note: keep family-consistent) | — |
|  6 | 1-categorical → higher-categorical?                                | no       | "natural in the ring" is the whole content | — |
|  7 | concrete index ℤ → arbitrary additive structure?                   | partial  | Stange's *full* nets index by `ℤⁿ`; this is the **rank-1** (`ℤ → R`) slice. A general elliptic-net API would index by `ℤⁿ`. | a redesign of the **`addMulSub`/`net` defs**, not of this naturality lemma |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no** (for `map_addMulSub` itself). It already uses the contemporary
`RingHomClass` bundling. The only lever (row 7: `ℤ → R` ⟶ `ℤⁿ → R` multi-rank nets) is a change to the
**underlying `addMulSub` definition**, not its naturality companion, and belongs to the
`addMulSub`/`net` upstreaming question, not here. One-line reason: `map_addMulSub` is the `map_*`
companion of `addMulSub`; its form is forced by `addMulSub`'s form.

---

### Diamond / defeq risk (Phase 4.5)

n/a — kind is `lemma` (introduces no definitional equalities or typeclass-search paths).

---

### Mathlib search-status: `map_addMulSub`

[A] Lean-Finder       (tool not available this session)                                  n/a: lean_loogle/lean_leansearch not loadable here; used authoritative grep of the **pinned** mathlib tree instead.
[B] Loogle            (tool not available)                                               n/a: same.
[C] LeanSearch        (tool not available)                                               n/a: same.
[D] Grep mathlib src  `addMulSub`, `map_addMulSub`, `EllSequence`, `def rel₄`, `def net`, `EllipticNet`, `elliptic net`, `Stange` over `.lake/packages/mathlib/Mathlib/` (NumberTheory + AlgebraicGeometry/EllipticCurve) | **no hits** for any.
[E] Name pattern      `map_addMulSub` / `addMulSub` anywhere in mathlib                  | **no hits**.

Searched for both:
  - the user's current form (`map_addMulSub`) — absent.
  - the literature-standard "naturality of the `addMulSub` factor" — absent (mathlib has **no**
    `addMulSub` / `EllSequence` net-relation concept at all; its EDS file stops at
    `normEDS`/`preNormEDS`/`complEDS₂`/`complEDS`).

**Decisive context.** Mathlib's `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean` (547 lines on
the pinned commit) *does* carry the analogous `map_*` naturality lemmas for **its own** EDS defs —
`map_preNormEDS'`, `map_preNormEDS`, `map_complEDS₂`, `map_normEDS`, `map_complEDS'`, `map_complEDS`
(lines 510–545) — and **every one of them is tagged `@[simp]`**, each proved by `simp [<def>, …]`. So
the *pattern* (ship a `@[simp] map_*` lemma next to each EDS def) is mathlib-idiomatic. But mathlib has
**no `addMulSub`/`rel₄`/`net`** — these are project-original Stange-net additions on top of mathlib's
EDS file. `map_addMulSub` is the naturality companion of a def that is not upstream. (Also: unlike the
mathlib analogues, the project's `map_addMulSub` is **not** tagged `@[simp]` — a one-line fix if
upstreamed.)

Concluded: **not in mathlib** (grep over the pinned tree exhausted across both the NumberTheory EDS
file and the AlgebraicGeometry DivisionPolynomial track; the literature-standard form is absent too,
because the parent `addMulSub` concept is absent).

---

### Call sites — `map_addMulSub`

Internal use count (this NagellLutz file, excluding the declaring line): **1**
- `EllipticDivisibilitySequence.lean:1166` — `map_rel₄`'s proof:
  `simp_rw [rel₄, map_add, map_sub, map_mul, map_addMulSub]`. This is the *only* direct consumer; from
  there `map_net` (`net_eq_rel₄`), `map_invarNum`, `map_invarDenom`, and the `…_eq_aeval` reductions
  inherit it transitively. So `map_addMulSub` is the **base of the whole `map_*` tower** in this file.

Inline-derivation grep (was `f (addMulSub …) = addMulSub (f∘…)` re-derived without `map_addMulSub`?):
none found — every consumer routes through `map_addMulSub`.

Cross-project (the General*/PID* + HasseWeil duplicate tracks the task flagged):
| Caller file:line                                                                            | Usage pattern |
|---------------------------------------------------------------------------------------------|---------------|
| `projects/HasseWeil/HasseWeil/Auxiliary/EllipticDivisibilitySequence.lean:134`              | duplicate **definition** of `map_addMulSub` (forked copy) |
| `projects/HasseWeil/HasseWeil/Auxiliary/EllipticDivisibilitySequence.lean:138`              | that copy's consumer (its `map_rel₄`: `simp_rw [rel₄, …, map_addMulSub]`) |
| `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequenceOriginal.lean` (older fork)     | duplicate **definition** + its own `map_rel₄` consumer (this file is the cleaned successor of that one) |

So `map_addMulSub`, like `map_net`/`rel₄`/`addMulSub`, is **duplicated across the consolidation
monorepo** (NagellLutz, NagellLutz-Original, HasseWeil) — each copy with the single `map_rel₄`
consumer. No site re-derives the identity inline.

---

### Composition check (Phase 6)

Can `map_addMulSub` be derived from mathlib in ≤3 chained calls? **As stated against the project's
`addMulSub`, it cannot — because `addMulSub` is not in mathlib.** The question only makes sense
relative to the project's own (non-mathlib) def, where the proof is:

Attempt 1 (the actual project proof): `by simp_rw [addMulSub, map_mul, Function.comp]`
  - Decls used: the project def `addMulSub` (to unfold), then mathlib `map_mul` and `Function.comp`.
  - Result: succeeds in one `simp_rw`. Unrolled, it is literally "unfold the product, push `f` through
    one `map_mul`, recognise `f (W k) = (f ∘ W) k`." A 1-step composition *given* the def.
  - Notes: the canonical "ring hom commutes with a product"; trivial *given* `addMulSub`, but
    `addMulSub` is project-local.

Conclusion: **NOT-COMPOSABLE from mathlib alone** (mathlib lacks `addMulSub`). It IS a 1-call
composition from the project's own elliptic-net API. The lemma's fate is therefore inseparable from
whether that API (`addMulSub` + its `map_*` companion, and the `rel₄`/`net` layer above it) is
upstreamed. (Once `addMulSub` exists upstream, `map_addMulSub` is `map_mul` + a `Function.comp`
rewrite — exactly the shape of mathlib's existing `@[simp] map_*` EDS lemmas.)

---

## Verdict: `map_addMulSub`

**Category:** **BORDERLINE-needs-human**

**Evidence:**
- Literature (Phase 3): `addMulSub` = the atomic `W((m+n)/2)·W((m−n)/2)` factor of Stange's
  elliptic-net relation (relation matched verbatim, WebSearch #2). Its naturality is folklore "ring
  hom commutes with a product / ℤ-polynomial," never a citable named result.
- Generality (Phase 4): **MAXIMALLY GENERAL** — already `RingHomClass` (more general than mathlib's own
  `map_normEDS`, which fixes `R →+* S`). No meaningful weakening; the lone narrowing (drop to
  `Mul`/`MulHomClass` for this one lemma) would split it off from the `map_rel₄`/`map_net` family for
  no benefit.
- Mathlib search (Phase 5): **not in mathlib** (grep over the pinned NumberTheory + DivisionPolynomial
  trees exhausted); parent `addMulSub`/`rel₄`/`net` also absent. But mathlib **does** keep the
  analogous `@[simp] map_*` lemmas (`map_normEDS`, …) for its own EDS defs — the pattern is idiomatic.
- Composition (Phase 6): NOT-COMPOSABLE from mathlib (no `addMulSub`); a 1-call composition from the
  project's own (non-upstream) net API.

**Rationale.**

`map_addMulSub` is neither independently shippable to mathlib nor independently rejectable — its status
is **entirely downstream of the parent `addMulSub` definition** (and the `rel₄`/`net` layer it
underpins), which encodes the atom of Stange's elliptic-net relation and is *not* in mathlib. This is
the same situation as the sibling `map_net` / `map_invarNum` / `map_invarDenom` reports, and it is the
**most foundational** node of that chain: `map_addMulSub` is the single lemma every other `map_*` in
the file is built on (via `map_rel₄`). The parent `addMulSub.md` itself was assessed
**YES-but-generalise-first** (a real candidate, but to be packaged with its family, not shipped alone),
which is exactly why this companion is BORDERLINE rather than a flat NO.

- If the **Stange elliptic-net layer** (`EllSequence.addMulSub`, `rel₄`, `net`, `net_eq_rel₄`, …) is
  upstreamed into `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean`, then `map_addMulSub`
  **should** ship with it: mathlib already keeps exactly this kind of `@[simp]` naturality lemma beside
  every EDS def, precisely so that base-changing to the universal polynomial ring via `aeval` is one
  rewrite — which is what the whole `map_*` tower here is for. In that world it becomes
  `YES-add-as-is`, **with `@[simp]` added** (the project copy lacks the tag) and placed next to
  `map_normEDS`.
- If that layer is *not* upstreamed (judged too niche, or pending the more general `ℤⁿ → R` multi-rank
  net redesign of Phase 4c row 7), then `map_addMulSub` stays a project-local helper and collapses to
  `NO-composable-from-mathlib`: the bare identity is a one-line `map_mul`/`Function.comp` step no one
  would add standalone, and AINTLIB should simply de-duplicate the three forked copies into a shared
  `Common/` module.

The decision is the same **API-scope / mathematical-taste** call the skill cannot make alone: *should
mathlib gain Stange's elliptic-net layer (`addMulSub`/`rel₄`/`net`) on top of its existing EDS file?*
`map_addMulSub` rides along with the answer — and because it is the **root** of the file's `map_*`
tower, it is the cleanest single decl to bundle into that PR.

Numbered questions (≤5):
  1. Should the **Stange elliptic-net API** (`EllSequence.addMulSub`, `rel₄`, `net`, `net_eq_rel₄`, and
     the `invarNum`/`invarDenom` invariants above them) be upstreamed into mathlib's
     `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean`? (yes ⇒ `map_addMulSub` ships with it as
     `YES-add-as-is`, **tagged `@[simp]`**, beside `map_normEDS`; no ⇒ it stays project-local and is
     `NO-composable-from-mathlib`.)
  2. If yes to (1): keep the current **rank-1** `ℤ → R` generality, or first redesign to Stange's full
     **multi-rank** `ℤⁿ → R` nets (Phase 4c row 7)? (A redesign changes the signature of `addMulSub`
     and hence of `map_addMulSub`.)
  3. Independently of mathlib: the project **triplicates** `addMulSub` + `map_addMulSub` (+ the
     `rel₄`/`net` layer) across NagellLutz, NagellLutz-Original, and HasseWeil. De-duplicate into one
     shared AINTLIB `Common/` module now (an on-`main` cleanup ticket), regardless of the mathlib
     decision?

**Next action:** answer the questions — chiefly Q1. If (1) = yes, treat `addMulSub` + `map_addMulSub`
(then `rel₄`/`map_rel₄`, `net`/`map_net`, …) as a single staged PR onto mathlib's EDS file: add
`@[simp]` to `map_addMulSub`, place it beside the existing `@[simp] map_*` EDS lemmas, then re-run
`/mathlibable map_addMulSub` to convert to `YES-add-as-is`. If (1) = no, the verdict is
`NO-composable-from-mathlib` (collapse the three forked copies into a shared AINTLIB helper per Q3).
This matches the pre-existing ledger entry (`mathlibable_ledger.tsv:126 → BORDERLINE-needs-human`) and
the sibling `map_net` verdict.

---

## Next step

Answer the three numbered questions — chiefly **Q1: should mathlib gain the Stange elliptic-net layer
(`addMulSub`/`rel₄`/`net`)?** `map_addMulSub` is the naturality companion of `addMulSub` and the root
of this file's entire `map_*` tower; it ships with whatever that answer is. mathlib precedent (its own
`@[simp] map_normEDS` family) means: if `addMulSub` goes up, `map_addMulSub` goes up with it (add
`@[simp]`); if not, it is a trivial project-local helper to de-duplicate within AINTLIB.

Sources consulted (literature): arXiv 0710.1316 (Stange, *Elliptic nets and elliptic curves*);
eprint 2006/392 (Stange, *The Tate pairing via elliptic nets*); Stange, *Formulary for elliptic
divisibility sequences and elliptic nets*; arXiv math/0402415 (Everest–Ward, sign of an EDS);
arXiv 0803.0728, arXiv 2512.09601, arXiv 2604.05280 (EDS/nets over commutative rings); mathlib4_docs
`Mathlib.NumberTheory.EllipticDivisibilitySequence` and `…EllipticCurve.DivisionPolynomial.Basic`.
