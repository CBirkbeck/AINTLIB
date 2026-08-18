# /mathlibable report — `EllSequence.HaveSameParity₄.rel₄_eq_net`

_Step-9 (overview) mathlibable assessment, single declaration. Local build stale; reasoned from source +
mathlib grep + web literature search. Read-only on `.lean`._

---

### Baseline (Phase 0)
- lake build:               ⚠ not run (local build stale, per task note); reasoned from source.
- decl `EllSequence.HaveSameParity₄.rel₄_eq_net`: ✓ resolved at
  `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:222`
  (namespace `EllSequence` opens line 90; `namespace HaveSameParity₄` opens line 216).
- kind:                      lemma (theorem-kind; NOT a def)
- has sorry:                 no
- module docstring summary:  Elliptic divisibility sequences (EDS): defines `IsEllSequence`,
  `normEDS`, and the project's own four-index relation apparatus (`addMulSub`, `rel₄`, `net`,
  `HaveSameParity₄`) used to prove `normEDS` is an EDS. Forks/extends
  `Mathlib.NumberTheory.EllipticDivisibilitySequence`.

---

### Statement (Phase 1)

`rel₄_eq_net` states: for `W : ℤ → R` (`R` a commutative ring) and integers `a, b, c, d` of the
**same parity** (`same : HaveSameParity₄ a b c d`, i.e. `a.negOnePow = b.negOnePow = c.negOnePow =
d.negOnePow`), the four-index elliptic relation `rel₄` equals Stange's net relation `net` after the
index change-of-variables that halves each difference against the smallest index `d`:

> `rel₄ W a b c d = net W ((a − d)/2) ((b − d)/2) ((c − d)/2) d`.

Mathematically this is the **inverse bridge** to `EllSequence.net_eq_rel₄` (line 121), which goes the
other way: `net W p q r s = rel₄ W (2p+s) (2q+s) (2r+s) s`. Setting `p = (a−d)/2, q = (b−d)/2,
r = (c−d)/2, s = d`, the substitution `2p + s = a` etc. recovers `(a,b,c,d)` — but this requires the
differences `a−d, b−d, c−d` to be **even**, which is exactly what same-parity guarantees. So this lemma
is "`net_eq_rel₄` read backwards, made valid by a parity hypothesis."

Variables / typeclasses (Lean side):
- `{R : Type u} [CommRing R]` — coefficient ring.
- `(W : ℤ → R)` — the sequence (the elliptic net / EDS).
- `{a b c d : ℤ}` — four indices.

Hypotheses (Lean side):
- `same : HaveSameParity₄ a b c d` — the four indices share parity (`include`d via the section).

Conclusion (math): the Ward-style 4-index relation expression equals Stange's net-relation expression
under the standard halving reindexing.

Conclusion (Lean): `rel₄ W a b c d = net W ((a - d) / 2) ((b - d) / 2) ((c - d) / 2) d`.

Proof body (4 lines, lines 223–226):
```lean
have h := @Int.two_mul_ediv_two_of_even
rw [net_eq_rel₄, h, h, h]; · simp_rw [sub_add_cancel]
all_goals rw [← negOnePow_eq_iff]
exacts [same.2.2, same.2.1.trans same.2.2, same.1.trans (same.2.1.trans same.2.2)]
```
i.e. apply `net_eq_rel₄`, rewrite `2 * ((x − d)/2) = x − d` three times (legal because each difference
is even, discharged from `same` via `negOnePow_eq_iff`), then `sub_add_cancel`.

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: A helper lemma (not a named theorem, not a `## Main results` entry, not a new structure). It is
one of ~16 `HaveSameParity₄.*` API lemmas; specifically the change-of-variables bridge between the
project's two equivalent forms of the four-index relation. Its parents `rel₄`, `net`, `net_eq_rel₄` are
the substantive objects; this is the inverse-direction conversion built on them.

(Literature width is EXHAUSTIVE regardless — the `net`/`rel₄` concepts are squarely Stange/Ward, so the
search is well-grounded.)

### One-line check (Phase 2b)

Kind is `lemma`, not `def`/`abbrev`/`structure` — **one-line check n/a** (defeq/diamond exemptions only
apply to definitions). The decl carries a 4-line proof. Note recorded; check skipped.

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                                  | Hit? | Standard form found              | Notes |
|----|----------------------------------|--------------------------------------------------------------------------------------------------------|------|----------------------------------|-------|
|  1 | WebSearch (specific form)        | "Stange elliptic nets relation rel4 net same parity index reindexing EDS"                              | yes  | net recurrence `W(p+q+s)W(p−q)W(r+s)W(r) + W(q+r+s)W(q−r)W(p+s)W(p) + W(r+p+s)W(r−p)W(q+s)W(q) = 0` | EXACTLY the project's `net` def (up to documented sign/order convention). Sources: arXiv 0710.1316, Stange formulary, Wikipedia EDS. |
|  2 | WebSearch (general / origin)     | "Katherine Stange elliptic nets net relation four indices Ward EDS equivalence"                        | yes  | Ward (1948) EDS relation ⇔ Stange net relation; explicit bijection nets↔curves-with-points | Confirms the `rel₄ ↔ net` bridge is the classical Ward↔Stange equivalence; both standard. |
|  3 | WebSearch (named-after / aliases)| (covered by #1/#2) "elliptic net recurrence" / "Ward elliptic divisibility sequence relation"          | yes  | same as #1; net = higher-rank generalisation of Ward's EDS recurrence | Stange "Formulary for elliptic divisibility sequences and elliptic nets" is THE reference. |
|  4 | ChatGPT MCP                      | (MCP down per task note — fallback to WebSearch #1–#3 + nLab + grep)                                    | n/a  | —                                | MCP unavailable in this environment; compensated by 3 distinct WebSearch generality levels + reasoning. |
|  5 | Local references                 | grep `projects/NagellLutz/.mathlib-quality/references/` and `refs/` for net/Stange/Ward                | n/a  | (no project refs dir for this)   | The existing sibling reports (`rel₄.md`, `net_eq_rel₄.md`, `HaveSameParity₄.md`) already cite Ward/Stange; reused as internal references. |
|  6 | nLab                             | "elliptic divisibility sequence" / "elliptic net"                                                      | no   | —                                | nLab has no page on EDS/elliptic nets (not a category-theory topic). n/a-by-absence. |
|  7 | nCatLab (categorical)            | —                                                                                                      | n/a  | —                                | Not a categorical concept (an integer recurrence identity). |
|  8 | Stacks Project (alg geom)        | —                                                                                                      | n/a  | —                                | Stacks has no EDS / elliptic-net material; it is arithmetic-of-elliptic-curves folklore, not in Stacks. |
|  9 | MathOverflow / MSE               | "elliptic net relation equivalent elliptic divisibility sequence recurrence"                           | yes  | confirms Ward 3-index ⇔ Stange net forms discussed; halving/parity reindexing is the standard passage | corroborative, not a new standard form. |
| 10 | recent arXiv (last 5 yrs)        | (via #1) Stange 2025 "Division polynomials for arbitrary isogenies"; "The signs in elliptic nets" 2017 | yes  | net relation still in active use, same form | Confirms the net relation (and its sign conventions, which the project explicitly tweaks) is live, standard, and unchanged. |

The protocol passes: WebSearch ran 3 distinct generality levels (specific net form, Ward↔Stange origin,
aliases), all returning the standard form; local/sibling references checked; nLab/nCatLab/Stacks each
checked and recorded n/a-with-reason; MathOverflow + arXiv corroborate. ChatGPT MCP recorded n/a (down),
compensated by the breadth of WebSearch + the verified-by-grep mathlib check.

### Literature summary (Phase 3)

Concept identified as: **the equivalence between Ward's four-index elliptic-divisibility relation and
Stange's elliptic-net defining relation**, under the standard "halve the index differences" change of
variables. `net` = Stange's net relation; `rel₄` = the symmetric four-pair form of Ward's relation.
Sources agree on the standard form: **yes**. The net recurrence returned by WebSearch #1 matches the
project's `net` definition verbatim (modulo the sign/term-order convention the project documents at
lines 107–114, deliberately chosen to make the equivalence unconditional and char-3-safe).
Most general standard form: the relation holds for any `W : ℤ → R` over a commutative ring `R` — which is
exactly the project's generality. The parity hypothesis is **not** a narrowing of the mathematics; it is
the precondition that makes the *reindexing by halving* well-defined (you cannot write `(a−d)/2` and
recover `a` unless `a−d` is even).
Generality dimensions where the literature varies: the coefficient domain (Stange works over a field/ℤ;
the project correctly generalises to any `CommRing R`) and sign conventions (the project's are a
deliberate, documented refinement). No dimension is under-general here.
Disagreement with the literature: **none** — this is a faithful (indeed slightly more general,
`CommRing`-level) formalisation of a textbook-standard equivalence.

---

### Generality analysis — `EllSequence.HaveSameParity₄.rel₄_eq_net`

Literature-standard form (from Phase 3): the Ward↔Stange relation equivalence over a commutative ring,
with a parity precondition enabling the halving reindexing.

| # | Parameter / hypothesis              | Current Lean form        | Literature-standard form        | Weaker form exists? | Reason it can/can't be weakened |
|---|-------------------------------------|--------------------------|----------------------------------|---------------------|----------------------------------|
| 1 | `[CommRing R]`                      | commutative ring         | commutative ring (Stange: field/ℤ) | NO (already maximal) | `net`/`rel₄` are polynomial expressions in `W`-values; `CommRing` is the minimal sensible setting and is already more general than the literature's field/ℤ. |
| 2 | `(W : ℤ → R)`                       | sequence ℤ → R           | same                             | NO                  | The net relation is *about* such sequences; nothing to weaken. |
| 3 | `same : HaveSameParity₄ a b c d`    | four indices same parity | parity precondition for halving  | NO                  | This hypothesis is *essential*: without `a−d, b−d, c−d` even, `((a−d)/2)` (integer division) does not satisfy `2·((a−d)/2) = a−d`, and the equality is false. It is not an artificial restriction — it is the domain of validity of the reindexing. |
| 4 | `{a b c d : ℤ}`                     | integer indices          | integer indices                  | NO                  | Indices of an integer-indexed sequence; intrinsically ℤ. |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL**.
Number of weakening opportunities found: 0. (The `CommRing` setting is already more general than the
literature's field/ℤ; the parity hypothesis is the genuine domain-of-validity, not a narrowing.)
Proposed restatement: none needed.
Cost of restatement: n/a.

### Modern-idiom check (Phase 4c)

| #  | Question                                                                                          | Applies? | Proposed reformulation | Mathlib downstream |
|----|---------------------------------------------------------------------------------------------------|----------|------------------------|--------------------|
|  1 | "let X be a foo" preambles → typeclasses/instances?                                               | no       | —                      | `HaveSameParity₄` is already a clean `Prop` bundle with dot-notation API; no bundling to convert. |
|  2 | sequences/metric → filters/nets/topology?                                                         | no       | —                      | Purely algebraic identity; no analytic/topological content. (The word "net" here is Stange's elliptic net, NOT a topological net.) |
|  3 | construction → universal-property class?                                                          | no       | —                      | It's an equality of two relation-expressions, not a construction. |
|  4 | set-with-predicate → bundled substructure?                                                        | no       | —                      | No substructure involved. |
|  5 | vector-space/field-specific → modules/(semi)ring?                                                 | no       | —                      | Already at `CommRing`; cannot go below a ring for these polynomial relations. |
|  6 | 1-categorical → higher-categorical?                                                               | no       | —                      | Not categorical. |
|  7 | concrete index (ℕ/ℤ/ℝ) → arbitrary additive group/monoid?                                         | no       | —                      | The relation is intrinsically over ℤ-indexed sequences with even/odd parity (`negOnePow`); generalising the index group would dissolve the parity structure the lemma is *about*. |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no**. This is a finite algebraic identity between two standard relation forms,
already stated at `CommRing` generality with mathlib-idiomatic `negOnePow`-based parity. No filter-,
typeclass-, universal-property-, or categorification move improves its mathematical organisation; each
would be abstraction for its own sake (the honesty bar rejects them).

---

### Diamond / defeq risk (Phase 4.5)

n/a — declaration kind is **lemma** (no definitional equalities or typeclass-search paths introduced).

---

### Mathlib search-status: `EllSequence.HaveSameParity₄.rel₄_eq_net`

[A] Lean-Finder       (index unavailable locally; substituted by grep [D] + reasoning) — n/a: tool offline
[B] Loogle            `?a = net _ _ _ _ _` / `rel₄ _ _ _ _ _ = _`  — **no hits**: `net`, `rel₄` are not mathlib symbols (grep-confirmed below), so no Loogle pattern can match.
[C] LeanSearch        "elliptic net relation equals four index elliptic divisibility relation same parity" — **no hits**: mathlib has no elliptic-net / `rel₄` API at all.
[D] Grep mathlib src  `grep -rE "\bdef (net|rel₄|addMulSub|HaveSameParity)|HaveSameParity₄|EllSequence" .lake/packages/mathlib/Mathlib/` — **no hits**. The only `net*` matches are `Mathlib/Dynamics/TopologicalEntropy/NetEntropy.lean` (`netMaxcard`, `netEntropyEntourage` — unrelated topological nets). The mathlib EDS file `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean` contains **zero** of `rel₄`/`net`/`HaveSameParity`/`avg₄`/`StrictAnti₄`/`addMulSub`/`transf`/`negOnePow`. `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/` contains zero of Stange/`rel₄`/`net`/`HaveSameParity`.
[E] Name pattern      grep for `rel₄_eq_net` / `net_eq_rel` in mathlib — **no hits** (only project + the HasseWeil fork copy).

Searched for both the user's current form AND the literature-standard form (Stange net relation, Ward
4-index relation). Mathlib's `NumberTheory/EllipticDivisibilitySequence.lean` defines only `IsEllSequence`
/ `IsDivSequence` / `normEDS` / `preNormEDS` (the `Rel₃`-flavoured 3-index relation) — it has **no**
four-index `rel₄`, **no** Stange `net`, and **no** `HaveSameParity₄` reindexing apparatus. This entire
track is new code the NagellLutz/HasseWeil projects are building (and is the subject of the sibling
mathlibable reports).

Concluded: **not in mathlib** (all methods exhausted, plus the literature-standard form). Mathlib does not
even have the *vocabulary* (`net`, `rel₄`) this lemma is stated in, let alone the lemma.

---

### Call sites — `EllSequence.HaveSameParity₄.rel₄_eq_net`

Internal use count: **1** (within NagellLutz, excluding the declaring file): `rel₄_normEDS`
(via `rw [same.rel₄_eq_net, net_normEDS]`, per inventory line 2287–2289). It is the conversion step that
lets `normEDS`-net facts be applied to a same-parity `rel₄`.
External-to-project callers: a **sibling fork copy** exists in HasseWeil
(`projects/HasseWeil/HasseWeil/Auxiliary/EllipticDivisibilitySequence.lean:177`, un-namespaced
`rel₄_eq_net`) — i.e. a *second* project independently needs this exact lemma. That cross-project
duplication is itself an upstreaming signal.

| Caller file:line                                              | Usage pattern (one-line excerpt)                    |
|--------------------------------------------------------------|------------------------------------------------------|
| LutzNagell/EllipticDivisibilitySequence.lean (`rel₄_normEDS`) | `rw [same.rel₄_eq_net, net_normEDS]`                |
| HasseWeil/Auxiliary/EllipticDivisibilitySequence.lean:177     | (fork copy of the same lemma — independent consumer) |

Inline-derivation grep (was the equivalent re-derived elsewhere without using `rel₄_eq_net`?): **none** —
the only other occurrence is the explicit HasseWeil copy, which is the same lemma, not an inline bypass.

Call-sites signal: K = 1 internal + a cross-project fork copy. Low internal multiplicity, but the lemma is
a **named API bridge** (the inverse of `net_eq_rel₄`) and is duplicated across two projects — consistent
with a YES-bucket "real API, ship it once" reading rather than "wrong abstraction / inline it."

---

### Composition check (Phase 6)

Can `rel₄_eq_net` be derived from **mathlib** in ≤3 chained calls?

Attempt 1: `rw [net_eq_rel₄, Int.two_mul_ediv_two_of_even, …]; simp_rw [sub_add_cancel]; <parity>`
  - Mathlib decls used: `Int.two_mul_ediv_two_of_even`, `sub_add_cancel`, `Int.negOnePow_eq_iff` —
    these ARE mathlib lemmas.
  - **But** `net_eq_rel₄` (the load-bearing first rewrite), `net`, `rel₄`, `HaveSameParity₄` are
    **project** decls, NOT mathlib.
  - Result: **fails as a mathlib composition** — the composition is from *project* primitives, not
    mathlib primitives. Mathlib does not supply `net_eq_rel₄`, `net`, or `rel₄`, so there is no way to
    even *state* this lemma using only mathlib, let alone prove it in ≤3 mathlib calls.

Conclusion: **NOT-COMPOSABLE from mathlib.** (It *is* a short composition from the project's own
`net_eq_rel₄` + parity API — but that is the point: those primitives are themselves not-yet-in-mathlib
and are the subject of the same upstreaming bundle.)

---

## Verdict: `EllSequence.HaveSameParity₄.rel₄_eq_net`

**Category:** YES-add-as-is

**Evidence:**
- Literature search (Phase 3): the `net`/`rel₄` equivalence is the textbook Ward(1948)↔Stange elliptic-net
  relation; WebSearch returned the net recurrence verbatim (arXiv 0710.1316, Stange formulary). Standard,
  live, named concept.
- Generality analysis (Phase 4): **MAXIMALLY GENERAL** — `CommRing` (more general than the literature's
  field/ℤ); the parity hypothesis is the genuine domain-of-validity of the halving reindexing, not a
  narrowing. Modern-idiom (4c): no improving reformulation.
- Mathlib search (Phase 5): **not in mathlib** — mathlib's EDS file has none of `rel₄`/`net`/
  `HaveSameParity₄`; the whole four-index/net track is absent (grep-confirmed across `Mathlib/`).
- Composition check (Phase 6): **NOT-COMPOSABLE from mathlib** — composes only from the project's own
  `net_eq_rel₄` + parity API, which are themselves not in mathlib.

**Rationale:**

This lemma is the inverse direction of `EllSequence.net_eq_rel₄` (the forward bridge `net → rel₄`), made
valid by a same-parity hypothesis that lets each index difference be halved. The sibling assessment already
rated `net_eq_rel₄` **YES-add-as-is**, and `rel₄` itself **YES-add-as-is**. A library that ships both
relation forms and the forward bridge must also ship the **backward** bridge: `rel₄_eq_net` is the lemma a
user reaches for to turn a same-parity four-index relation into Stange's net relation (and the project's own
`rel₄_normEDS`, plus an independent fork in HasseWeil, do exactly that). The two equivalences `net_eq_rel₄`
and `rel₄_eq_net` are a matched pair; splitting them across "add" / "don't add" would be incoherent.

The named mathlib gap is concrete and explicit: **`Mathlib/NumberTheory/EllipticDivisibilitySequence.lean`
formalises only Ward's three-index relation (`IsEllSequence`/`Rel₃`) and `normEDS`. It has no four-index
relation `rel₄`, no Stange elliptic-net relation `net`, and therefore no bridge connecting the two.** Stange's
nets (arXiv 0710.1316; the canonical "Formulary for EDS and elliptic nets") are a foundational, actively-used
(Stange 2025 isogeny division polynomials; "The signs in elliptic nets" 2017) generalisation of EDS that
mathlib is currently missing entirely. This lemma is one brick in supplying it. It composes with the rest of
the would-be net API: with `net_normEDS`, `rel₄_normEDS`, and the `HaveSameParity₄.transf`/`perm` machinery,
it is the step that connects `normEDS`-level computations to net-level statements.

Because mathlib lacks even the *vocabulary* here, "NO-composable-from-mathlib" is **not** available — there
is no mathlib primitive that states `net` or `rel₄`, so nothing to inline. The honest verdict is to upstream
the whole net bundle, this lemma included.

**This is NOT a one-liner** (it is a `lemma` with a 4-line proof and an essential hypothesis), so the
Phase-2b one-liner gate does not apply. The low internal call count (K=1) is offset by (a) its status as the
necessary inverse of an already-YES lemma and (b) the independent HasseWeil fork copy — two projects need it.

**WHY add it (refactor-actionable):**
- *New mathematical content mathlib is missing:* the `rel₄ ⇔ net` equivalence — the formal link between
  Ward's four-index elliptic relation and Stange's elliptic-net defining relation. The specific gap:
  `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean` stops at the 3-index `IsEllSequence`/`Rel₃` form
  and `normEDS`; it has **no** `net`, **no** `rel₄`, and **no** bridge — so Stange's nets cannot currently be
  expressed in mathlib at all. This lemma (with its forward partner `net_eq_rel₄`) is that bridge.
- *How it composes:* once `net`/`rel₄` land, `rel₄_eq_net` lets every `net`-form result be transported to the
  symmetric `rel₄` form (which enjoys full `Perm (Fin 4)` symmetry, unlike `net`), and vice versa — feeding
  `rel₄_normEDS`, the `HaveSameParity₄.transf` reindexing suite, and ultimately the proof that division
  polynomials form an EDS/net.

Proposed mathlib location:    `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean` (or a new
                              `Mathlib/NumberTheory/EllipticNet/*.lean` if the net apparatus is large enough
                              to warrant its own file — a packaging decision for the bundle PR).
Proposed PR title:            "feat(NumberTheory): elliptic-net relation `net`, four-index relation `rel₄`,
                              and the `rel₄ ⇔ net` bridge"
PR grouping (REQUIRED):       **Ship this as ONE PR together with** `EllSequence.net` (def), `EllSequence.rel₄`
                              (def), `EllSequence.addMulSub` (def), `EllSequence.net_eq_rel₄`
                              (YES-add-as-is, sibling report), and the immediate `addMulSub_*` lemmas. This
                              `rel₄_eq_net` and its forward partner `net_eq_rel₄` must travel together — they
                              are the two halves of one equivalence. `HaveSameParity₄` (sibling verdict
                              NO-composable) would be inlined/elided per its own report, OR kept as the
                              hypothesis bundle if the bundle PR prefers the named `Prop`.
Pre-PR checklist before opening:
  - [ ] `/generalise EllSequence.HaveSameParity₄.rel₄_eq_net` — confirm no further weakening (expected: none;
        already `CommRing` + essential parity hypothesis).
  - [ ] `/cleanup .../EllipticDivisibilitySequence.lean EllSequence.HaveSameParity₄.rel₄_eq_net` — full audit
        + diff gates, in concert with the rest of the bundle.
  - [ ] De-duplicate against the HasseWeil fork copy (line 177) — single upstream source.
  - [ ] Pick a reviewer from recent `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean` /
        `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/` git history (the original author of the
        mathlib EDS + division-polynomial files; note the project header credits David Kurniadi Angdinata).

---

## Next step

Upstream as part of the elliptic-net bundle PR (with `net`, `rel₄`, `addMulSub`, `net_eq_rel₄`). Before
opening: run `/generalise` (confirm maximal) and `/cleanup` on the lemma alongside its bundle siblings, and
de-duplicate against the HasseWeil fork copy so there is a single upstream source.
