# /mathlibable report — `EllSequence.rel₄`

## Verdict (TL;DR)

**`YES-add-as-is`** — but as part of the EDS-elliptic fork shipped together, not in isolation.

`EllSequence.rel₄` is the **"elliptic relation"** of Junyan Xu's 2026 paper *On Elliptic
Sequences over Commutative Rings* (arXiv:2604.05280): a 4-parameter, highly symmetric,
homogeneous quartic relation over a general commutative ring. It is the modern, maximally-general
formulation that subsumes both Ward's 3-index relation and Stange's elliptic-net relation. Mathlib
has none of this API; the form is the literature-standard (and the literature is brand-new, with
this very Lean development as its algebraic companion). It anchors a ~20-declaration named API and
cannot be inlined or composed away.

---

### Baseline (Phase 0)
- lake build:               (stale per task note — reasoning from source; decl elaborates in the green `main` build per CLAUDE.md)
- decl `EllSequence.rel₄`:   ✓ resolved at `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:103`
- kind:                      `def`
- has sorry:                 no
- module docstring summary:  Defines elliptic divisibility sequences (EDS) and constructs normalised EDSs (`preNormEDS`, `normEDS`); the `addMulSub`/`rel₄`/`net` Stange-net machinery proves `normEDS` is elliptic.

---

### Statement (Phase 1)

`EllSequence.rel₄` is a **definition**. For a commutative ring `R` and a sequence `W : ℤ → R`, and
four integers `a b c d` (intended to share the same parity), with the building block

  `addMulSub W m n := W ((m+n) tdiv 2) * W ((m-n) tdiv 2)`   (truncated division by 2),

it defines the **signed sum over the three pairings of the four indices**:

  `rel₄ W a b c d = addMulSub W a b · addMulSub W c d`
  `             − addMulSub W a c · addMulSub W b d`
  `             + addMulSub W a d · addMulSub W b c`.

Mathematically this is a **homogeneous degree-4 (quartic) form** in the values of `W`, manifestly
symmetric: under `S₄` permutation of `(a,b,c,d)` it is invariant up to sign, vanishing whenever two
indices coincide (`rel₄_same`). It vanishes (`rel₄ … = 0`) exactly when the four-index
elliptic/net relation holds. The project proves:
- `rel₄_eq_net` / `net_eq_rel₄`: `rel₄` equals Stange's `net` after the change of variables
  `(p,q,r,s) ↦ (2p+s, 2q+s, 2r+s, s)`;
- `rel₃_iff₄`: Ward's 3-index relation `Rel₃ W m n r ↔ rel₄ W (2m) (2n) (2r) 0 = 0`.

Variables / typeclasses (Lean side):
- `{R : Type u} [CommRing R]` — coefficient ring (fully general; no field, no characteristic, no integral-domain hypothesis).
- `(W : ℤ → R)` — the sequence.
- `(a b c d : ℤ)` — the four indices.

Hypotheses: none on the `def` itself (same-parity is documented intent; lemmas like
`addMulSub_even`/`addMulSub_odd` and `HaveSameParity₄` supply it where needed).

Conclusion (math): n/a — definition (a quartic form `R`).
Conclusion (Lean): `R`.

---

### Size classification (Phase 2a)

Verdict: **BIG**
Reason: It introduces a **named mathematical object** — the central organizing relation of an entire
theory (elliptic sequences over commutative rings), the namesake of a 2026 research paper, and the
engine of the project's main result (`normEDS` is an EDS). Not a helper/corollary.

### One-line check (Phase 2b)

Body line count: **3 substantive lines** (a three-term signed sum across two lines + the `def` head).
One-liner verdict: **MULTI-LINE**. (Even setting aside the line count, the body is a genuine quartic
expression, not an alias.) The one-liner negative signal does not apply.

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                                  | Hit? | Standard form found                                                  | Notes |
|----|----------------------------------|--------------------------------------------------------------------------------------------------------|------|----------------------------------------------------------------------|-------|
|  1 | WebSearch (specific form)        | "Stange elliptic nets definition four-index relation elliptic divisibility sequences"                  | yes  | net relation `W(p+q+s)W(p-q)W(r+s)W(r) + … = 0`                       | arXiv:0710.1316 (Stange); Colorado EDS formulary |
|  2 | WebSearch (general form)         | "elliptic net 'net polynomial' Stange Ward … three-term relation"                                      | yes  | Ward 3-term `W_{n+m}W_{n-m}=W_{n+1}W_{n-1}W_m²−W_{m+1}W_{m-1}W_n²`    | both 3-index and net forms standard; net generalises EDS to ℤⁿ |
|  3 | WebSearch (named-after/aliases)  | "elliptic net four-index relation symmetric 'three pairings' OR 'half-index' … reformulation"          | yes  | **"4-parameter, highly symmetric family of homogeneous quartic relations called elliptic relations"** | surfaced arXiv:2604.05280 — the decisive hit |
|  4 | ChatGPT MCP                      | standard-name + generality of the symmetric `rel₄`/`addMulSub` form                                     | n/a  | —                                                                    | **MCP down** (Codex `exec` stdin error, both `high` and `medium`); fell back to arXiv source |
|  5 | Local references                 | `.mathlib-quality/references/` + `refs/NagellLutz/`                                                     | n/a  | (directories absent)                                                 | recorded n/a — neither dir exists |
|  6 | nLab                             | elliptic divisibility sequence / elliptic net                                                          | n/a  | (no page; HTTP 404)                                                  | nLab has no EDS/elliptic-net entry |
|  7 | nCatLab (if categorical)         | —                                                                                                      | n/a  | —                                                                    | not a categorical concept (a recurrence on ℤ → R) |
|  8 | Stacks Project (if alg geom)     | —                                                                                                      | n/a  | —                                                                    | Stacks has no EDS / elliptic-net material |
|  9 | MathOverflow / MSE               | symmetric four-index elliptic relation                                                                 | no   | —                                                                    | no MO/MSE thread on this specific symmetric form |
| 10 | recent arXiv (last 5 years)      | (via #3) "On Elliptic Sequences over Commutative Rings"                                                 | yes  | **arXiv:2604.05280, Junyan Xu (2026)** — defines "elliptic relations" exactly as `rel₄` | author of this very Lean file; "purely algebraic", "follow-up paper on division polynomials" |
| 11 | Loogle / LeanSearch (mathlib)    | `EllSequence.rel₄`, addMulSub, four-index elliptic                                                      | no   | —                                                                    | Loogle: "unknown identifier"; LeanSearch: no hit (see Phase 5) |

The protocol passed: WebSearch ran 3 distinct queries at different generality levels (specific net
form, general 3-index form, symmetric-quartic/aliases); ChatGPT MCP attempted twice and recorded
`n/a` with the failure mode; local refs, nLab, nCatLab, Stacks, MO/MSE, arXiv all checked/recorded.

### Literature summary (Phase 3)

Concept identified as: the **"elliptic relation"** of Junyan Xu, *On Elliptic Sequences over
Commutative Rings* (arXiv:2604.05280, 2026) — a 4-parameter, highly symmetric, homogeneous quartic
relation. Equivalent (over the relevant index sublattice) to **Stange's elliptic-net relation**
(arXiv:0710.1316) and, after specialisation, to **Ward's three-index elliptic relation**.

Sources agree on the standard form: **yes**. The net relation (Stange) and the 3-index relation
(Ward, Wikipedia, the Colorado formulary) are the long-standing classical anchors; Xu's 2026 paper
introduces precisely the symmetric-quartic packaging that `rel₄` implements and names it "elliptic
relation". The Lean `rel₄` IS that object.

Most general standard form: a homogeneous quartic relation `rel₄ W a b c d = 0` over an **arbitrary
commutative ring** `R`, with full `S₄` index symmetry — strictly more general than:
- Ward's 3-index relation (recovered: `Rel₃ ⇔ rel₄(2m,2n,2r,0)=0`);
- Stange's net relation (recovered: `rel₄ = net` after a linear change of indices).

Generality dimensions where the literature varies:
- Coefficient domain: classically ℤ (Ward) → field K (Stange) → **arbitrary commutative ring**
  (Xu 2026 / this file). The Lean form sits at the most general end.
- Arity/symmetry: 3-index asymmetric (Ward) → net 4-index with partial symmetry (Stange) →
  **fully `S₄`-symmetric 4-index** (`rel₄`). The `rel₄` form is the most symmetric.

Disagreement with the literature: none. `rel₄` is the modern (2026) standard form, stated at maximal
generality. The `addMulSub` half-index coordinatization (`W((m±n)/2)`, with `tdiv` so
`(-m).tdiv 2 = -(m.tdiv 2)`) is the device that makes the `S₄` symmetry manifest — an
implementation-level packaging of the same relation, not a competing mathematical object.

---

### Generality analysis — `EllSequence.rel₄`

Literature-standard form (Phase 3): a fully-`S₄`-symmetric homogeneous quartic "elliptic relation"
over an arbitrary commutative ring (Xu 2026), subsuming Stange's net relation and Ward's 3-index
relation.

| # | Parameter / hypothesis        | Current Lean form            | Literature-standard form       | Weaker form exists? | Reason it can/can't be weakened |
|---|-------------------------------|------------------------------|---------------------------------|---------------------|----------------------------------|
| 1 | `[CommRing R]`               | commutative ring             | arbitrary commutative ring (Xu) | **NO**              | already the maximal sensible base; the quartic uses `+ − ·` only, no division / no domain / no characteristic hypothesis. Mathlib would keep `CommRing`. |
| 2 | `(W : ℤ → R)`                | unconstrained sequence       | unconstrained                   | NO                  | the relation is a pointwise polynomial identity in `W`'s values; no structure on `W` assumed in the `def`. |
| 3 | `(a b c d : ℤ)`              | four integer indices         | four indices in ℤ (or ℤⁿ for nets) | borderline       | nets generalise to ℤⁿ, but the EDS (rank-1) case is genuinely the ℤ case; the `def` is the rank-1 object by design. Not a weakening of *this* object. |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL** (over `CommRing`, no extra hypotheses).
Number of weakening opportunities found: **0**.
Cost of restatement: n/a — nothing to restate.

### Modern-idiom check (Phase 4c)

| #  | Question                                                                 | Applies? | Proposed reformulation | Mathlib downstream |
|----|--------------------------------------------------------------------------|----------|------------------------|--------------------|
|  1 | "let X be a foo" preambles → typeclasses/instances?                       | no       | — (already `[CommRing R]` typeclass; `W` is a bare hypothesis as it must be) | — |
|  2 | sequences/metric → filters/nets/topology?                                 | no       | — (this is an algebraic identity, no limits/topology) | — |
|  3 | construct object → universal-property class?                              | no       | — (it is itself a relation/test, not a constructed object) | — |
|  4 | set-with-closure-predicate → bundled substructure?                        | no       | — (not a substructure) | — |
|  5 | vector-space/metric/field-specific → weaken typeclass?                    | no       | — (already at `CommRing`, the floor) | — |
|  6 | 1-categorical → higher-categorical?                                       | no       | — (elementary commutative algebra) | — |
|  7 | concrete index (ℕ/ℤ/ℝ) → arbitrary group/monoid?                          | no/borderline | The `net`-to-ℤⁿ (elliptic-net) generalisation exists in the literature, but the rank-1 ℤ object is the intended one and is what mathlib's existing `IsEllSequence` lives at. | (would be a *different* def: higher-rank nets) |

**Design sub-question (the only real one):** should the mathlib primitive be `rel₄` (the
`addMulSub`/half-index symmetric form) or `net` (Stange's literal four-term form)? The project
**already provides both and proves them equivalent** (`rel₄_eq_net` ↔ `net_eq_rel₄`), and its
docstrings argue `rel₄` is the better organizing primitive precisely because all four indices enjoy
`S₄` symmetry (whereas `net` only has 3-index symmetry). Xu's 2026 paper centres the symmetric
quartic. So `rel₄` is the *right* primitive — `net` is the compatibility shim with Stange's notation,
not a replacement target.

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no** (the current form already IS the modern idiom — it is the 2026
literature-standard symmetric-quartic "elliptic relation"). One-line reason: there is no cleaner
contemporary mathlib formulation; `rel₄` is itself the contemporary formulation, and its companion
`net` is kept only as the bridge to Stange's classical notation.

---

### Diamond / defeq risk — `EllSequence.rel₄`

| # | Risk                          | Verdict | Evidence / rationale |
|---|-------------------------------|---------|----------------------|
| 1 | Typeclass diamond            | none    | `def` produces a *term* of `R`; introduces no instance, no class. No search path affected. |
| 2 | Reducibility leak            | none    | Plain `def` — **not** `@[reducible]`, not `abbrev`. Body is a non-trivial quartic; it is sealed, so `simp`/unification won't unfold it spuriously. (The downstream proofs `unfold`/`simp_rw [rel₄]` explicitly — controlled.) |
| 3 | Non-canonical unfolding      | none    | No `@[simp]` attribute; never auto-unfolded. |
| 4 | Instance priority collision  | n/a     | Not an `instance`. |
| 5 | Universe-polymorphism issues | none    | `R : Type u`, result in `R`; no forced universe annotation. |
| 6 | Coercion ambiguity           | none    | No `CoeFun`/`CoeSort`. |

### Risk verdict (Phase 4.5)

Overall risk: **NONE**. Top risks: none. (A sealed, plain `def` returning an element of `R`.)

---

### Mathlib search-status: `EllSequence.rel₄`

[A] Lean-Finder       four-index elliptic relation / elliptic sequence quartic   no hits
[B] Loogle            `EllSequence.rel₄`, `addMulSub`                              no hits — "unknown identifier 'EllSequence.rel₄'"
[C] LeanSearch        "four-index elliptic relation addMulSub elliptic divisibility sequence"   no hits
[D] Grep mathlib src  `addMulSub|rel₄|Stange|elliptic net|EllSequence` over `.lake/packages/mathlib/Mathlib/`   no hits (only unrelated `IsEllSequence`/`IsEllDivSequence` in the canonical EDS file)
[E] Name pattern      `def rel₄` / `def addMulSub` / `def net` in mathlib tree    no hits

Searched for both the user's form (`rel₄`, `addMulSub`-quartic) and the literature-standard forms
(Stange's `net` relation; Ward's 3-index relation). Mathlib's `Mathlib/NumberTheory/
EllipticDivisibilitySequence.lean` (547 lines) defines `IsEllSequence`/`IsDivSequence`/
`IsEllDivSequence`/`preNormEDS`/`normEDS`/`complEDS` — but its `IsEllSequence` is stated directly via
the inline 3-index equation and it contains **no** `addMulSub`, `rel₄`, `net`, or any four-index /
symmetric-quartic machinery.

Concluded: **not in mathlib** (all 5 methods exhausted, plus both literature-standard forms — the
four-index/net layer is entirely absent from mathlib's EDS file).

---

### Call sites — `EllSequence.rel₄`

Internal use count: **~88** occurrences inside the declaring live file
(`EllipticDivisibilitySequence.lean`, excluding the 2-line `def` itself), spanning **~20 distinct
top-level declarations** that are *named for or built on* `rel₄`. (A near-identical full copy also
exists at `projects/HasseWeil/HasseWeil/Auxiliary/EllipticDivisibilitySequence.lean`, 66
occurrences — a sibling fork, not an external consumer.)
External-to-file callers: the duplicate-track `EllipticDivisibilitySequenceOriginal.lean` (dead;
slated for deletion per `05-duplications.md`) and the HasseWeil auxiliary copy.

| Caller (`EllipticDivisibilitySequence.lean`):line | Usage pattern (one-line excerpt) |
|---------------------------------------------------|----------------------------------|
| net_eq_rel₄:121                                   | `net W p q r s = rel₄ W (2*p+s) (2*q+s) (2*r+s) s` |
| rel₄_eq_net:222                                   | `rel₄ W a b c d = net W ((a-d)/2) …` |
| rel₄_transf:280                                   | `rel₄ W (avg₄ … - d) … = rel₄ W a b c d` |
| addMulSub_sq_mul_rel₄_eq₉:344                     | `(addMulSub W c d)^2 * rel₄ W m n r s = …` |
| rel₄_iff_evenRec:373                              | `rel₄ W (2m+1) (2m-1) 3 1 = 0 ↔ EvenRec W m` |
| rel₄_fix₁_of_fix₂:427 / rel₄_of_fix₂:442          | inductive reduction of `rel₄` over fixed indices |
| rel₄_of_min₂:457 / rel₄_of_anti_oddRec_evenRec:477| `rel₄ W a b c d = 0` from odd/even recurrences |
| rel₄_abs:514 / rel₄_swap₀₁/₁₂/₂₃:517-523          | `S₄`-symmetry lemmas |
| rel₄_same₀₁/₁₂/₂₃:553-561                         | vanishing on repeated index |
| rel₄_of_oddRec_evenRec:570                        | the bridge to the recurrence characterisation |
| map_rel₄:1166                                     | `f (rel₄ W p q r s) = rel₄ (f∘W) p q r s` (ring-hom transport) |
| rel₄_normEDS:1468                                 | `rel₄ (normEDS …) … = 0` — the payoff toward `isEllDivSequence_normEDS` |

Inline-derivation grep: none — consumers always go through `rel₄`/`net`, never re-derive the quartic
inline. The object is the genuine API surface.

Composability signal: **K ≫ 3 internal uses, no inline re-derivation → real API; strongly YES-leaning.**

---

### Composition check (Phase 6)

Can `EllSequence.rel₄` be derived from mathlib in ≤3 chained calls?

Attempt 1: rebuild `rel₄` from a mathlib primitive.
  - Mathlib decls available: `Mathlib.NumberTheory.EllipticDivisibilitySequence` provides
    `IsEllSequence`/`normEDS`/… but **no `addMulSub`, no four-index quartic, no `net`**.
  - Result: **fails** — there is no mathlib building block for the half-index `addMulSub` product, let
    alone the symmetric-quartic combination. A "composition" would just be writing the `def` out.

Conclusion: **NOT-COMPOSABLE**. `rel₄` is a *new named primitive*; mathlib has nothing to compose it
from in ≤3 calls. (Furthermore, even if it could be spelled inline, ~20 lemmas are *about* `rel₄` —
the value is the named object plus its API, which by construction cannot be inlined away.)

---

## Verdict: `EllSequence.rel₄`

**Category:** `YES-add-as-is`

**Evidence:**
- Literature search (Phase 3): identified as the **"elliptic relation"** of Xu 2026 (arXiv:2604.05280)
  — a 4-parameter symmetric homogeneous quartic; equals Stange's `net` (arXiv:0710.1316) and
  specialises to Ward's 3-index relation. Standard, maximally-general form.
- Generality analysis (Phase 4): **MAXIMALLY GENERAL** over `CommRing` (0 weakenings); Phase 4c found
  no cleaner modern idiom (`rel₄` already IS the modern symmetric form; `net` is its classical-notation shim).
- Mathlib search (Phase 5): **not in mathlib** (5 methods + both literature forms; the canonical
  mathlib EDS file has no four-index/`addMulSub`/`net` layer at all).
- Composition check (Phase 6): **NOT-COMPOSABLE** (no mathlib building blocks for the half-index
  quartic; and ~20 lemmas depend on it as a named object).
- Diamond/defeq risk (Phase 4.5): **NONE** (sealed plain `def` returning `R`).

**Rationale.**

`EllSequence.rel₄` is exactly the central object of a 2026 research paper — Junyan Xu's *On Elliptic
Sequences over Commutative Rings* defines elliptic sequences by "a 4-parameter, highly symmetric
family of homogeneous quartic relations among terms which we call elliptic relations", and this Lean
file (same author lineage, the algebraic-division-polynomial development the paper announces as its
follow-up) is the formalisation of precisely that object. The half-index `addMulSub` coordinatization
is the device that makes the full `S₄` symmetry manifest; the project proves `rel₄` equals Stange's
classical `net` relation (`rel₄_eq_net`) and that Ward's 3-index relation is the `d=0` specialisation
(`rel₃_iff₄`). So `rel₄` is not idiosyncratic — it is the modern, maximally-general (arbitrary
commutative ring, no characteristic/division/domain hypotheses) packaging of the long-standing
elliptic relation, stated in the form the current literature has converged on. Mathlib has the EDS
*sequences* (`normEDS`, `IsEllSequence`) but is entirely missing the four-index relational layer that
makes the algebraic theory work; `rel₄` is the keystone of that layer.

It clears every YES gate: literature-standard at maximal generality (so not
YES-but-generalise-first); absent from mathlib by all five search methods (so not NO-mathlib-has-it);
not a ≤3-call composition and the named anchor of ~20 lemmas plus the main theorem `rel₄_normEDS →
isEllDivSequence_normEDS` (so not NO-composable); a sealed plain `def` with zero diamond/defeq risk;
and multi-line, so the one-liner caveat is moot.

**WHY add it (refactor-actionable).** The specific mathlib gap: `Mathlib/NumberTheory/
EllipticDivisibilitySequence.lean` defines `IsEllSequence W` via the bare 3-index equation and proves
`normEDS` satisfies it, but it has **no reusable relational API** — no four-index relation, no
`S₄`-symmetry lemmas, no `net`/`rel₄` equivalence, no ring-hom transport (`map_rel₄`), no
recurrence↔relation bridge (`rel₄_of_oddRec_evenRec`). Anyone proving facts about elliptic sequences
(e.g. the Hasse–Weil project, which already vendored a full copy) must re-derive this layer — and in
this repo it has been duplicated twice (HasseWeil + the dead `…Original` track), which is the textbook
symptom of a missing mathlib primitive. Adding `rel₄` (with `addMulSub`/`net` and the symmetry API)
gives mathlib the canonical object that Xu's paper and these formalisations are all built on; it
composes with mathlib's existing `IsEllSequence`/`normEDS` by supplying the relational characterisation
those defs currently lack (`rel₃_iff₄`, `rel₄_normEDS`).

**Important grain caveat (the realistic unit of contribution).** `rel₄` should **not** be PR'd in
isolation — it is meaningless without `addMulSub` (its building block) and gains its value from the
`net` equivalence and the `rel₄_*` symmetry/recurrence API. The honest verdict is: this whole
EDS-elliptic fork is a **YES for mathlib as a unit** (it is the formalisation companion to a published
paper and an upgrade of mathlib's own EDS file), and `rel₄` is the keystone `def` within it. The PR is
an *upstream-the-fork* effort, ideally coordinated with the paper's author (Junyan Xu) who is already
a mathlib contributor.

Proposed mathlib location:    `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean` (extend the
                              existing file) — or a new `Mathlib/NumberTheory/EllipticDivisibility/
                              Relation.lean` if the four-index layer is split out.
Proposed PR title:            "feat(NumberTheory): four-index elliptic relation `rel₄` for elliptic sequences"
PR grouping:                  ship `EllSequence.addMulSub`, `EllSequence.rel₄`, `EllSequence.net`,
                              `net_eq_rel₄`/`rel₄_eq_net`, `rel₃_iff₄`, the `rel₄_swap*`/`rel₄_same*`
                              symmetry lemmas, `map_rel₄`, and `rel₄_normEDS` as one coherent PR
                              (the relational-API layer). The `rel₄_of_*Rec` recurrence bridge and
                              `normEDS`-is-elliptic payoff can follow in a second PR.
Pre-PR checklist before opening:
  - [ ] First deduplicate within the repo: delete `EllipticDivisibilitySequenceOriginal.lean` and
        unify the HasseWeil copy (per `05-duplications.md`) so there is one source of truth to upstream.
  - [ ] `/generalise EllSequence.rel₄` — confirm `CommRing` is the floor (expected: yes, no weakening).
  - [ ] `/cleanup <file> EllSequence.rel₄` — full audit (naming, the `tdiv`-vs-`ediv` note, docstrings)
        before the mathlib PR.
  - [ ] Coordinate with Junyan Xu / pick a `Mathlib/NumberTheory/` reviewer (the existing EDS file was
        authored by David Kurniadi Angdinata — a natural reviewer).

---

## Next step

This whole EDS-elliptic relational layer is a YES-add-as-is for mathlib, with `EllSequence.rel₄` as
its keystone `def`. Before any PR: (1) deduplicate the three in-repo copies down to one source of
truth; (2) run `/generalise` and `/cleanup` on the unified file; (3) PR the relational API
(`addMulSub`/`rel₄`/`net` + equivalence + `S₄` symmetry + `map_rel₄` + `rel₄_normEDS`) as one group
into `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean`, coordinating with the area's authors
(Angdinata / Xu).
