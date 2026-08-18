# /mathlibable report — `EllSequence.relFin4`

> Step-9 (overview) mathlibable assessment, NagellLutz project (Nagell–Lutz theorem; elliptic
> divisibility sequences; division polynomials). Run with the local Lean build **stale**; reasoning
> is from the source statement, the vendored mathlib source tree (`.lake/packages/mathlib`, rev
> `d90090f`), WebSearch, and grep. ChatGPT MCP (Codex) was **down** this session — its channel is
> recorded `n/a (tool down)` and compensated by extra WebSearch + grep. This report reuses the
> settled sibling verdicts in this same directory: `rel₄.md` (the keystone `def`, **YES-add-as-is**
> but only as part of upstreaming the whole fork as a unit) and the `rel₄_abs.md` /
> `rel₄_swap₀₁.md` / `rel₄_swap₁₂.md` family (all **NO-composable** — fork-internal `S₄`-symmetry
> glue). `relFin4` is the `def` those `relFin4_perm*` lemmas are stated over, so it sits in exactly
> that glue layer.

---

## Verdict (TL;DR)

**`NO-composable-from-mathlib`** — a trivial tuple-currying adapter `def` over a non-mathlib subject.

`relFin4 W t := rel₄ W (t 0) (t 1) (t 2) (t 3)` is a one-line definitional wrapper that repackages
the four-index elliptic relation `rel₄` to take a single tuple `t : Fin 4 → ℤ` instead of four
separate integers. It exists for **one** purpose: so that a permutation `σ : Equiv.Perm (Fin 4)` can
act on the indices by precomposition `t ∘ σ`, which is what lets `relFin4_perm` state "`rel₄` is
`S₄`-equivariant up to sign". Its subject `rel₄` (and the building block `addMulSub`) **do not exist
in mathlib**, so `relFin4` can never be a standalone mathlib `def`; and even granting the fork, it is
a bare definitional unfolding (`rel₄` applied to the four tuple components) — the `Fin 4` curry/uncurry
is standard mathlib idiom that never warrants its own named adapter. It rides along with the
`rel₄`/`addMulSub` API if/when that is upstreamed, as internal plumbing for the permutation proof; it
is never an independent contribution.

---

### Baseline (Phase 0)
- lake build:               ⚠ stale (build/lib empty) — reasoned from source per task instructions
- decl `EllSequence.relFin4`: ✓ resolved at
  `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:530`
- kind:                      **def** (plain `def`, not `noncomputable`/`abbrev`/`structure`)
- has sorry:                 no
- module docstring summary:  Elliptic divisibility sequences — defines `IsEllSequence`, `preNormEDS`,
  `normEDS`, and (unlike upstream mathlib) **proves** `isEllDivSequence_normEDS` via the
  `addMulSub`/`rel₄`/`net` Stange-net machinery. A forward-port / extension of
  `Mathlib.NumberTheory.EllipticDivisibilitySequence`.

**Namespace / qualified-name verification.** The `def` sits inside `namespace EllSequence` (opened
line 90, closed line 597), in `section Perm` (opened line 509) under `variable (neg : ∀ k, W (-k) =
-W k)` + `include neg` (lines 511–512), with a local `variable (W) in` (line 528) re-introducing the
explicit `W`. Parsed qualified name in the task prompt — `EllSequence.relFin4` — is **CORRECT**
(confirmed against the project inventory at
`.mathlib-quality/overview/inventory/LutzNagell_EllipticDivisibilitySequence.md:733`,
`### def EllSequence.relFin4`, "Lines: 528-530").

Note on the `include neg` context: `relFin4` itself does **not** use `neg` (it is a pure repackaging
of `rel₄`), so the oddness hypothesis is not part of its signature — `neg` only enters the *lemmas*
about `relFin4` (`relFin4_perm`, `relFin4_perm'`).

---

### Statement (Phase 1)

```lean
variable (W) in
/-- The four-index elliptic relation with a tuple as input. -/
def relFin4 (t : Fin 4 → ℤ) : R := rel₄ W (t 0) (t 1) (t 2) (t 3)
```

`relFin4 W t` is **definitionally** `rel₄ W (t 0) (t 1) (t 2) (t 3)` — the four-index elliptic
relation `rel₄` fed its four integer indices from a single tuple `t : Fin 4 → ℤ` (read off as
`t 0, t 1, t 2, t 3`). It is a pure **uncurrying / tuple-input adapter**: same value as `rel₄`, only
the calling convention changes (four scalar args → one `Fin 4 → ℤ` argument).

Here `rel₄` is the **project-local** definition (line 103):
`rel₄ W a b c d = addMulSub W a b * addMulSub W c d − addMulSub W a c * addMulSub W b d
+ addMulSub W a d * addMulSub W b c` — the signed sum over the three pairings of the four indices,
built from `addMulSub W m n := W ((m+n).tdiv 2) * W ((m−n).tdiv 2)` (line 94).

Variables / typeclasses (Lean side):
- `{R : Type u}` `[CommRing R]` — the codomain ring (file-level `variable`).
- `(W : ℤ → R)` — the sequence (file-level `variable`, made explicit here by `variable (W) in`).
- `(t : Fin 4 → ℤ)` — the tuple of four integer indices.

Hypotheses: **none** (it is a definition; `neg`/`zero`/`one`/… do not enter).

Output (math): the value of the elliptic-relation quartic at the indices `t 0, …, t 3`.
Output (Lean): `relFin4 W t : R`, definitionally `rel₄ W (t 0) (t 1) (t 2) (t 3)`.

**Role in the development (why it exists).** The sole reason `relFin4` exists is to host a
**permutation action on the four indices**. A `σ : Equiv.Perm (Fin 4)` acts naturally on a tuple
`t : Fin 4 → ℤ` by precomposition (`t ∘ σ`), but it cannot act on four *separate* integer arguments
of `rel₄`. So the development:
1. defines `relFin4 W t := rel₄ W (t 0) (t 1) (t 2) (t 3)` to convert the index list into a tuple;
2. proves `relFin4_perm` (line 533): `relFin4 W (t ∘ σ) = Perm.sign σ • relFin4 W t` — i.e. `rel₄`
   is `S₄`-equivariant up to the sign of `σ`, by reducing `σ` to adjacent transpositions
   (`Perm.mclosure_swap_castSucc_succ`) and applying the three `rel₄_swap₀₁/₁₂/₂₃` lemmas;
3. uses `relFin4_perm'` (the inverted form) inside `rel₄_of_oddRec_evenRec` (line 580:
   `rw [← relFin4_perm' neg σ, relFin4]; simp_rw [Function.comp]`) to **sort the four indices into
   descending order** (via `Tuple.sort` / `Fin.revPerm`) so the antitone-case lemma
   `rel₄_of_anti_oddRec_evenRec` becomes applicable.

It is thus formalization plumbing for the "WLOG the indices are sorted" step — the tuple form is the
only thing that makes `Equiv.Perm`/`Tuple.sort` usable on `rel₄`'s arguments.

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: a one-line definitional adapter (tuple-input repackaging) for a Lean-local definition; not a
named mathematical object, not a `## Main definition`, introduces no structure and no new mathematics.
It is the tuple-currying member of the `rel₄`-permutation micro-API
(`relFin4`, `relFin4_perm`, `relFin4_perm'`) whose entire job is to let `Equiv.Perm (Fin 4)` act on
`rel₄`'s indices. Mathematically `relFin4 W t = rel₄ W (t 0) (t 1) (t 2) (t 3)` carries **zero**
content beyond `rel₄`.

(Note: literature width is EXHAUSTIVE regardless — inherited from the settled keystone `rel₄.md`. The
`def` it adapts, `rel₄`, is BIG and its own report is YES-add-as-is; this *adapter over it* is SMALL
glue.)

### One-line check (Phase 2b)

Kind **is** `def`, so the one-liner-def check **applies** and is decisive: the body is the single
expression `rel₄ W (t 0) (t 1) (t 2) (t 3)` — a literal re-application of an existing definition to
the four projections of its tuple argument. This is the canonical "trivial wrapper / notation
convenience" pattern: it adds no definitional content, only an alternate calling convention. Such
one-line currying adapters are not mathlib `def`s in their own right; mathlib expresses the same thing
inline (apply the curried function to `t 0, t 1, t 2, t 3`, or use `Matrix.cons`/`![…]` and
`Function.comp`). Strong signal toward **NO-composable**.

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                                  | Hit? | Standard form found | Notes |
|----|----------------------------------|--------------------------------------------------------------------------------------------------------|------|---------------------|-------|
|  1 | WebSearch (specific form)        | "elliptic relation four indices tuple permutation S_4 symmetric group acting on indices elliptic divisibility sequence sign of permutation" | partial | Stange net symmetry; Ward symmetric relation | confirms the *subject* (the symmetric four-index elliptic relation and its `S₄`-up-to-sign symmetry); **no** notion of a separate "tuple-input form" — that is a Lean encoding artifact, not a mathematical object |
|  2 | WebSearch (named-after / source) | "Junyan Xu 'On Elliptic Sequences over Commutative Rings' elliptic relation E(a,b,c,d) symmetric group permutation indices" | yes | **arXiv:2604.05280** — elliptic relation `E(a,b,c,d)`, "4-parameter, highly symmetric family of homogeneous quartic relations", antisymmetric/symmetric under permuting the four arguments | the paper behind the `EllSequence`/`rel₄` API; the relation's `S₄`-symmetry-up-to-sign is exactly what `relFin4` + `relFin4_perm` formalize; the paper writes `E(a,b,c,d)` (four scalar args), never a tuple wrapper |
|  3 | WebSearch (general form)         | "function of a Fin n tuple permutation action precompose Equiv.Perm uncurry currying" | yes | standard "uncurried form of an n-ary function so a permutation can act" — a Lean/typed-functional idiom | the general pattern is the well-known "to let `Equiv.Perm (Fin n)` act, take the `Fin n → α` (uncurried) form"; mathlib does this inline with `Function.comp`/`Matrix.cons`, not via a bespoke named `def` |
|  4 | ChatGPT MCP                      | (standard-form + generality + history prompt; then short retry)                                        | n/a  | —                   | **tool down** — Codex `exec` failed this session; compensated by extra WebSearch (#1–3) + grep (Phase 5 [D]) + the settled sibling reports (`rel₄.md`, `rel₄_abs.md`, `perm.md`) |
|  5 | Local references                 | `ls projects/NagellLutz/.mathlib-quality/references/` ; `refs/NagellLutz/`                              | n/a  | —                   | no `references/` dir under this project's `.mathlib-quality/` (only `overview/`); `refs/` symlink absent. Recorded n/a |
|  6 | nLab                             | "elliptic divisibility sequence" / "elliptic net"                                                      | n/a  | —                   | nLab has no EDS / elliptic-net page; certainly none for a tuple-input adapter (a recurrence on `ℤ → R`, not categorical) |
|  7 | nCatLab                          | —                                                                                                      | n/a  | —                   | not categorical |
|  8 | Stacks Project                   | —                                                                                                      | n/a  | —                   | not a scheme-theoretic statement (an integer-index relation packaging) |
|  9 | MathOverflow / Math.SE           | "permutation acting on the arguments of a symmetric function tuple form"                                | n/a  | —                   | the "uncurry to let a permutation act" move is folklore in typed formalization; no canonical reference, and no mathematical notion of `relFin4` as distinct from `rel₄` |
| 10 | recent arXiv (≤5 yrs)            | covered by #2 → arXiv:2604.05280 (Xu 2026)                                                              | yes  | the `EllSequence`/`addMulSub`/`net`/`rel₄` framework | `relFin4` is part of that paper's Lean infrastructure (the tuple form enabling the `Tuple.sort`/permutation reduction), not a stated result |

The protocol passed: WebSearch ran 3 distinct queries at different generality levels (the specific
tuple-input + `S₄`-symmetry form, the named source `E(a,b,c,d)`, the general "uncurry-for-permutation"
idiom); ChatGPT MCP attempted and recorded `n/a` with the failure mode; local refs, nLab, nCatLab,
Stacks, MO/MSE, arXiv each checked/recorded.

### Literature summary (Phase 3)

Concept identified as: **the tuple-input (uncurried) form of the four-index elliptic relation**, a
pure Lean encoding convenience. The paper-level object is Junyan Xu's **elliptic relation** `E(a,b,c,d)`
(*On Elliptic Sequences over Commutative Rings*, arXiv:2604.05280, 2026), a 4-parameter symmetric
homogeneous quartic that is antisymmetric under transpositions of its four arguments (hence
`S₄`-equivariant up to sign). The paper writes it with **four scalar arguments**; there is **no
mathematical "tuple version"** — `relFin4` is the Lean device that turns those four arguments into one
`Fin 4 → ℤ` so that `Equiv.Perm (Fin 4)` can act by precomposition. The *definition itself* is just
"apply `rel₄` to the four components of `t`".
Sources agree on a standard form: the elliptic relation has four scalar indices; its symmetry is the
content; the tuple repackaging is **not** an independent named object in any source or in mathlib.
Most general standard form: the symmetric four-index relation `E(a,b,c,d)` with its `S₄`-up-to-sign
symmetry (formalized here as `rel₄` + `relFin4_perm`). The uncurried `relFin4` is an implementation
detail of that formalization, never an isolated definition in the literature.
Generality dimensions where the literature varies: only "which relation packaging" (Ward 3-index →
Stange net → Xu's symmetric quartic) and "coefficient domain" (ℤ → field → arbitrary commutative
ring); "scalar args vs. tuple arg" is **not** a mathematical dimension — it is a typed-encoding choice.
Disagreement with the literature: none.

---

### Generality analysis — `EllSequence.relFin4`

Literature-standard form (Phase 3): the four-index elliptic relation `E(a,b,c,d)` (four scalar args),
formalized as `rel₄`. `relFin4` is the uncurried `Fin 4 → ℤ` adapter over it — by construction the
*narrowest possible* packaging (it just re-exposes `rel₄`).

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker/more-general form exists? | Reason it can/can't be weakened or generalised |
|---|------------------------|-------------------|--------------------------|----------------------------------|------------------------------------------------|
| 1 | `[CommRing R]` | comm ring | arbitrary comm ring (Xu) | yes (vacuously) | `relFin4` inherits whatever `rel₄` needs; `CommRing` is the floor `rel₄` lives over. Not a meaningful weakening of *this* adapter |
| 2 | `(W : ℤ → R)` | the sequence | the EDS sequence | no | the object of study; not a generality knob |
| 3 | index tuple `t : Fin 4 → ℤ` | a 4-tuple of integers | four integer indices (rank-1 EDS) | no (for this def) | the whole point is "exactly four indices"; an `n`-ary `Fin n → ℤ` version would be a **different** object (elliptic nets, `rel₆`/`relFin6`, …), not a generalisation of `relFin4` — and `rel₄`'s quartic structure is intrinsically 4-ary |
| 4 | the wrapped function `rel₄ W ·` | the specific quartic | **any** function of four integers (or `Fin 4 → ℤ`) | the generic "uncurry a 4-ary function" pattern | maximal generality is the trivial generic adapter `fun f t ↦ f (t 0) (t 1) (t 2) (t 3)` / `Function.uncurry`-style currying, which mathlib expresses **inline** (`Matrix.cons`, `![…]`, `Function.comp`) and never names. That is not a better mathlib `def` — it is the absence of a `def` |

### Generality verdict (Phase 4b)

The current form is **MAXIMALLY SPECIFIC by design** — it is a thin re-export of `rel₄` with the
arguments tupled. There is no "more general" mathlib-worthy `def` to ship:
- generalising the *arity* (`Fin n → ℤ`) does not generalise `relFin4` — it produces a different
  object (a net / a different `rel`), and `rel₄`'s body is irreducibly 4-ary;
- generalising the *wrapped function* lands on the generic "uncurry a 4-ary function" adapter, which
  mathlib **never names** (it inlines `f (t 0) (t 1) (t 2) (t 3)` or uses `![…]`/`Function.comp`).

So there is **no generalisation worth shipping**. The "more general" form is the *already existing*
generic currying idiom (inline `Matrix.cons`/`Function.comp`), which is precisely how a tuple of
arguments is consumed everywhere in mathlib without a dedicated `def`.
Number of weakening/generalisation opportunities found: **0** that yield a mathlib-worthy declaration
(every candidate lands on the inline currying idiom or on a non-mathlib subject `rel₄`).
Proposed restatement: none.
Cost of restatement: n/a.

### Modern-idiom check (Phase 4c)

| #  | Question | Applies? | Proposed reformulation | Downstream |
|----|----------|----------|------------------------|------------|
| 1 | bundled hyps → typeclasses? | no | — | a `def` with no hypotheses |
| 2 | sequences/metric → filters/topology? | no | — | finite algebraic expression, no limits |
| 3 | construction → universal property? | no | — | not a construction with a UMP; a currying adapter |
| 4 | set+closure → bundled substructure? | no | — | no substructure |
| 5 | vector-space/field-specific → weaker typeclass? | no | — | already over an arbitrary `CommRing`; `R` is otherwise irrelevant |
| 6 | 1-categorical → higher-categorical? | no | — | elementary |
| 7 | concrete adapter `def` → inline currying? | **yes** | drop `relFin4`; write `rel₄ W (t 0) (t 1) (t 2) (t 3)` (or use `![…]` + `Function.comp`) at the one place a permutation must act | this is the **NO-composable** conclusion (inline it), not a YES-but-generalise restatement |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no** (the only "modernisation" is to replace this named adapter with the
already-existing inline currying — i.e. eliminate it, which is the NO-composable conclusion, not a
YES-but-generalise restatement). One-line reason: there is no organisational improvement to make; the
`def` is a zero-content re-export of `rel₄` whose only justification is local readability of the
permutation proof. Keeping it *named in the project* is fine; *upstreaming it as a mathlib `def`* is
not warranted.

---

### Diamond / defeq risk — `EllSequence.relFin4` (Phase 4.5)

Kind is `def`, so a defeq note is in order (light — there are no typeclass instances or structure
projections here):
- `relFin4 W t` is **definitionally** `rel₄ W (t 0) (t 1) (t 2) (t 3)` (the body is exactly that
  expression). There is no new instance, no `structure`, no projection, no coercion, so there is **no
  diamond surface** and no typeclass-search path introduced.
- The only mild defeq friction is the usual `Fin 4`-tuple-vs.-`Function.comp` unfolding (the consumer
  at line 580 does `rw […, relFin4]; simp_rw [Function.comp]` to expose `t (σ i)` as
  `(t ∘ σ) i`) — entirely internal, no impact on any external API. No risk worth flagging.

---

### Mathlib search-status: `EllSequence.relFin4`

[A] Lean-Finder       — n/a: tool not exposed in this environment.
[B] Loogle            — n/a: `lean_loogle` not exposed in this environment.
[C] LeanSearch        — n/a: `lean_leansearch` not exposed in this environment.
[D] Grep mathlib src  `relFin4`, `rel₄`, `addMulSub`, `EllSequence`, `net` over
                      `.lake/packages/mathlib/Mathlib/NumberTheory/EllipticDivisibilitySequence.lean`
                      → **zero relevant hits**: the only matches are `IsEllSequence` (the bare
                      `def`/doc). The mathlib EDS file (rev `d90090f`) contains **only**
                      `IsEllSequence` / `IsDivSequence` / `IsEllDivSequence` / `preNormEDS'` /
                      `preNormEDS` / `complEDS₂` / `normEDS` (verified by listing its `def`/`lemma`
                      heads). It has **no** `EllSequence` namespace, **no** `addMulSub`, `net`, `rel₄`,
                      `relFin4`, `HaveSameParity₄`, and **no** permutation / `Fin 4`-tuple / sorting
                      machinery — and still carries the `normEDS`-is-`IsEllDivSequence` **TODO** that
                      this project discharges. So this file is an in-development *extension* of the
                      mathlib file; `relFin4` lives only in the fork.
[E] Name pattern      grep `relFin4` across the repo → appears **only** in the three forked EDS files
                      (NagellLutz live, NagellLutz `…Original` dead track, HasseWeil aux), identical
                      text. No mathlib occurrence. (A search for any `…Fin4`/`relFin`-style tuple
                      adapter in mathlib's NumberTheory tree returns nothing relevant.)

Searched for both the user's current form (`def relFin4 (t : Fin 4 → ℤ) := rel₄ W (t 0) (t 1) (t 2)
(t 3)`) and the underlying idea ("an uncurried `Fin 4 → ℤ` form of a four-index relation so a
permutation can act"). Neither the subject `rel₄` nor any generic named "tuple-input adapter" exists
in mathlib; mathlib consumes tuples of arguments inline (`Matrix.cons`/`![…]`, `Function.comp`,
`Function.uncurry`).

Concluded: **not in mathlib** — and *cannot* be a standalone mathlib `def`, since its subject `rel₄`
(and `addMulSub`) are not in mathlib, and the generic uncurry-for-permutation pattern is never named.

---

### Call sites — `EllSequence.relFin4` (Phase 6.0)

Internal use count (this NagellLutz live file, excluding the declaring line 530): **3**
(`relFin4_perm` 533, `relFin4_perm'` 544, `rel₄_of_oddRec_evenRec` 580 — all within the same `Perm`
section). All three are *fork-internal*; there is no consumer outside the `rel₄`-permutation machinery.
External-to-file callers in the repo: 2 other files, but both are **copies of the same forked API**
(not independent consumers): the NagellLutz `…Original` dead track and the HasseWeil aux copy.

| Caller file:line | Usage pattern (one-line excerpt) |
|------------------|-----------------------------------|
| `…/EllipticDivisibilitySequence.lean:533` | `theorem relFin4_perm … : relFin4 W (t ∘ σ) = Perm.sign σ • relFin4 W t` — the `S₄`-equivariance statement (the reason `relFin4` exists) |
| `…/EllipticDivisibilitySequence.lean:544` | `lemma relFin4_perm' … : Perm.sign σ • relFin4 W (t ∘ σ) = relFin4 W t` — inverted form |
| `…/EllipticDivisibilitySequence.lean:580` | `rw [← relFin4_perm' neg σ, relFin4]; simp_rw [Function.comp]` — inside `rel₄_of_oddRec_evenRec`, the "sort the four indices descending" (WLOG) step |
| `…/EllipticDivisibilitySequenceOriginal.lean` | identical — **dead** duplicate track (slated for deletion per `05-duplications.md`) |
| `…/HasseWeil/HasseWeil/Auxiliary/EllipticDivisibilitySequence.lean` | identical — third copy of the same fork (sibling vendored copy, not an external consumer) |

**Call-sites signal:** K = 3 internal uses, but all three are within the single `relFin4_perm*` →
`rel₄_of_oddRec_evenRec` permutation reduction; no external (non-fork) consumer; the `def` is *never*
used except as the carrier of the `Perm (Fin 4)` action. It is not standalone API — it is part of the
`rel₄`-permutation micro-API and serves exactly one reduction (sort indices, apply the antitone case).

---

### Composition check (Phase 6)

Can `EllSequence.relFin4` be obtained from mathlib in ≤3 chained calls? Two layers, **both**
NO-composable:

**Layer 1 — given the project's own `rel₄`:** `relFin4` *is* its body, a single application:
```
relFin4 W t  ≡  rel₄ W (t 0) (t 1) (t 2) (t 3)        -- 1 "call" (apply rel₄ to the 4 components)
```
This is a zero-step definitional unfolding: the `def` adds nothing beyond `rel₄`. Wherever a tuple is
in hand, one simply writes `rel₄ W (t 0) (t 1) (t 2) (t 3)` (the consumer even does
`rw [relFin4]; simp_rw [Function.comp]` to get back to `rel₄` on `t ∘ σ`). The generic
uncurry adapter `fun f t ↦ f (t 0) (t 1) (t 2) (t 3)` is the standard mathlib inline idiom
(`Matrix.cons`/`![…]`, `Function.comp`, `Function.uncurry`), never a named mathlib `def`. So **as a
mathlib `def`** it is not warranted: it composes trivially (1 application of an existing function) and
the wrapper is pure local convenience.

**Layer 2 — the deeper reason:** the body mentions `rel₄` (and through it `addMulSub`), which **are
not in mathlib at all**. A `def` whose body is `rel₄ W …` therefore cannot stand alone in mathlib; it
can only ever exist *bundled with* `rel₄` (i.e. as part of upstreaming the whole `EllSequence` API /
arXiv 2604.05280). Within that bundle it is a tuple-currying convenience for the internal
`relFin4_perm` proof — it is **glue**, not an independent target.

Conclusion: **COMPOSABLE** (a 1-application definitional unfolding of `rel₄`; and at the deeper level
its subject is non-mathlib).

---

## Verdict: `EllSequence.relFin4`

**Category:** **NO-composable-from-mathlib**

**Evidence:**
- Literature search (Phase 3): no named result; there is **no mathematical "tuple version"** of the
  elliptic relation. The subject is Xu 2026's elliptic relation `E(a,b,c,d)` (arXiv:2604.05280, four
  scalar args, symmetric up to sign); `relFin4` is the Lean device that uncurries those four arguments
  into a `Fin 4 → ℤ` so `Equiv.Perm (Fin 4)` can act by precomposition — a typed-encoding artifact,
  unnamed in the literature and in mathlib. ChatGPT MCP down → compensated with 3 WebSearch queries +
  grep + the settled sibling reports.
- Generality analysis (Phase 4): MAXIMALLY SPECIFIC by design (a thin re-export of `rel₄`);
  generalising the arity gives a *different* object, generalising the wrapped function gives the
  generic inline currying idiom mathlib never names. No mathlib-worthy generalisation; no modern idiom
  beyond "inline it" (4c). No defeq/diamond surface (4.5).
- Mathlib search (Phase 5): **not in mathlib**, and *cannot* be a standalone `def` —
  `rel₄`/`addMulSub`/`EllSequence`/`relFin4` are absent from mathlib (this file extends mathlib's EDS
  file, which still carries the `normEDS`-is-EDS TODO and has no four-index / tuple / permutation
  layer). The generic uncurry adapter is also never a named mathlib `def`; tuples of args are consumed
  inline (`Matrix.cons`/`Function.comp`).
- Composition check (Phase 6): **COMPOSABLE** — `relFin4 W t` *is* `rel₄ W (t 0) (t 1) (t 2) (t 3)`,
  a single application of an existing function (a zero-step definitional unfolding).

**Rationale.**
`relFin4` is the tuple-currying adapter of the `rel₄`-permutation micro-API: it repackages the
four-index elliptic relation `rel₄ W a b c d` so it takes one tuple `t : Fin 4 → ℤ` instead of four
integers, for the *sole* purpose of letting `σ : Equiv.Perm (Fin 4)` act on the indices by `t ∘ σ`
(which is what `relFin4_perm` exploits to prove `S₄`-equivariance-up-to-sign, and what
`rel₄_of_oddRec_evenRec` uses to sort the indices descending). It is not an independently mathlib-able
`def` for two compounding reasons, exactly mirroring its settled siblings in this directory
(`rel₄_abs`, `rel₄_swap₀₁`, `rel₄_swap₁₂`, all NO-composable). First, its body names `rel₄` (and
through it `addMulSub`), which **do not exist in mathlib** — this file is a forward-port that *extends*
`Mathlib.NumberTheory.EllipticDivisibilitySequence` (which still carries the very `normEDS`-is-an-EDS
TODO this project discharges, and which lacks the `addMulSub`/`net`/`rel₄` machinery from arXiv
2604.05280). A `def` whose body names a non-mathlib definition can only travel *with* that definition,
as part of the larger `EllSequence` upstreaming bundle — never as a standalone PR. Second, even
granting that bundle, `relFin4` is a content-free one-line re-export: its body is literally `rel₄`
applied to the four projections `t 0, t 1, t 2, t 3`. The "uncurry a four-argument function so a
permutation can act on its inputs" pattern is bog-standard typed-formalization idiom that mathlib
expresses **inline** (apply the function to the components, or use `![…]`/`Matrix.cons` +
`Function.comp`/`Function.uncurry`); mathlib does **not** mint a bespoke named `def` for it. There is
no general "tuple-input form of an `n`-ary relation" `def` in mathlib to cite, and none is wanted.

So within the project this `def` is fine and should stay as local glue (3 honest internal uses, all
inside the `relFin4_perm` → `rel₄_of_oddRec_evenRec` permutation reduction; naming it reads better than
threading `rel₄ W (t 0) (t 1) (t 2) (t 3)` and `t ∘ σ` through the `Submonoid.closure_induction`
proof). It simply is **not** a mathlib contribution in its own right: if/when the `EllSequence`/`rel₄`
API is upstreamed (the `rel₄.md` report's YES-add-as-is, **as a unit**, coordinated with the paper's
author), this adapter and its `relFin4_perm`/`relFin4_perm'` lemmas ride along as part of that file's
internal `S₄`-symmetry API; they are not separate mathlib declarations, and `relFin4` itself is a
one-line wrapper. (Even within that bundle, an upstreaming reviewer might well choose to **inline**
`relFin4` and state `relFin4_perm` directly on `rel₄ W (t 0) (t 1) (t 2) (t 3)` / `![…]`, eliminating
the adapter — further confirming it is plumbing, not a headline object.)

**WHY not (refactor-actionable).**
Mathlib has neither the subject (`rel₄`, `addMulSub`) nor any named "tuple-input adapter"; the only
mathlib primitives in the vicinity are the inline currying tools `Matrix.cons`/`![…]`,
`Function.comp`, `Function.uncurry` — and the project already has `rel₄` one screen up (line 103). The
exact value is the one-line body below. No standalone mathlib `def` is needed or possible (the subject
is non-mathlib; the wrapper is content-free).

Mathlib building blocks (only as the generic inline idiom, never a named adapter):
`Function.comp` / `Matrix.cons` (`![…]`) / `Function.uncurry` — the standard ways to feed a
`Fin 4 → ℤ` tuple's components into a four-argument function. The real ingredient is the project's own
`EllSequence.rel₄` (same file, line 103).

Composition sketch (it *is* the body — a single application):
```lean
-- relFin4 W t is definitionally:
example (W : ℤ → R) (t : Fin 4 → ℤ) : R := rel₄ W (t 0) (t 1) (t 2) (t 3)
-- i.e. the generic "apply a 4-ary function to a tuple's components", which mathlib writes inline.
```

Call sites in this project (Phase 6.0): K = 3 (lines 533, 544, 580), all inside the `rel₄`-permutation
machinery; no external (non-fork) consumer.

Refactor plan: **no mathlib action.** Keep `relFin4` as local glue exactly where it is — it is
correctly factored (naming the tuple form keeps `relFin4_perm`'s `Submonoid.closure_induction` proof
and the `Tuple.sort` reduction readable; inlining `rel₄ W (t 0) (t 1) (t 2) (t 3)` everywhere would be
strictly worse *inside this project*). The only "mathlib" consequence is negative: do **not** file a PR
for this `def` in isolation. It is upstream-relevant only as part of the whole `EllSequence` / `rel₄` /
`addMulSub` API (arXiv 2604.05280) — and there it is internal `S₄`-symmetry plumbing (and may even be
inlined by the upstreaming reviewer), not a headline object. The one genuinely actionable cleanup is
the AINTLIB cross-fork **dedup**: the three byte-identical copies (NagellLutz live, NagellLutz
`…Original`, HasseWeil aux) should be collapsed to a single `Common/`-hosted module — a `lane:cleanup`
ticket, not a mathlib PR.

Next action: none toward mathlib. Leave the `def` in place as project-local infrastructure. (The
broader question "should the entire `EllSequence`/`rel₄` extension be upstreamed to
`Mathlib.NumberTheory.EllipticDivisibilitySequence`?" is the separate, BIG decision tracked in the
`rel₄.md` report — run `/mathlibable` on the headline results like `isEllDivSequence_normEDS` /
`rel₄_normEDS` for that, not on `relFin4`.)

---

## Next step

No mathlib action for `relFin4`. It is a one-line tuple-currying adapter (`relFin4 W t := rel₄ W
(t 0) (t 1) (t 2) (t 3)`) over Lean-local definitions (`rel₄`, `addMulSub`) that are not in mathlib;
it composes trivially from `rel₄` (a single application) and exists only to host the `Equiv.Perm
(Fin 4)` action used by `relFin4_perm` / `rel₄_of_oddRec_evenRec`. It is correct, correctly-factored
local glue and should stay in the project. Do not PR it standalone. The only actionable cleanup is
deduplicating the three identical fork copies into a shared `Common/` module (AINTLIB `lane:cleanup`
ticket). Reconsider mathlib inclusion only if the entire `addMulSub`/`rel₄`/`net` apparatus is
upstreamed as a unit (per `rel₄.md`), where this tuple-input form is an internal permutation-proof
helper (and a candidate for inlining at upstreaming time).
