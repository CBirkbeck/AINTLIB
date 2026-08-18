# /mathlibable report — `EllSequence.addMulSub_swap`

## Verdict (TL;DR)

**`NO-composable-from-mathlib`** — in the *re-aimed-at-the-parent* sense. This is a small structural
**lemma about the project-local `def` `EllSequence.addMulSub`**, which is itself not in mathlib. The
lemma cannot live in mathlib on its own (its statement mentions `addMulSub`), and it is not
separately citable; it **rides along with the `EllSequence` elliptic-relation layer** that the parent
`addMulSub.md` assessment marks for upstreaming. Within that layer it is one of the sign/parity
bookkeeping lemmas the parent report explicitly lists as "what to upstream" — but it is *never* a
standalone mathlib contribution, and against today's mathlib it is a ≤2-line composition
(`simp_rw [addMulSub, Int.neg_tdiv, neg]; ring`).

- **Qualified name:** `EllSequence.addMulSub_swap`  *(verified — see Phase 0)*
- **Location:** `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:198`
- **Parent def:** `EllSequence.addMulSub` (line 94) — assessed `YES-but-generalise-first` (packaging
  sense) in `addMulSub.md`; this lemma **inherits / re-aims to** that verdict.
- **Date:** 2026-06-18

---

### Baseline (Phase 0)
- lake build:               (stale per task note — reasoning from source; the decl elaborates in the green `main` build per CLAUDE.md)
- decl `EllSequence.addMulSub_swap`:  ✓ resolved at `…/EllipticDivisibilitySequence.lean:198`
- kind:                      `lemma`
- has sorry:                 no
- module docstring summary:  Defines elliptic divisibility sequences (EDS) and normalised EDSs (`preNormEDS`, `normEDS`); the `addMulSub`/`rel₄`/`net` Stange-net machinery proves `normEDS` is elliptic.

**Qualified-name verification.** The file opens `namespace EllSequence` at line 90 and closes it
(`end EllSequence`) at line 597; line 198 is inside that block, with no intervening namespace (the
only nested namespace, `HaveSameParity₄`, opens at line 216, after this lemma). So the parsed name in
the prompt, `EllSequence.addMulSub_swap`, is **correct**. Kind is `lemma` (not a def), so Phase 4.5
(diamond/defeq risk) is **n/a**.

---

### Statement (Phase 1)

```lean
namespace EllSequence
variable {R : Type u} [CommRing R] (W : ℤ → R)

lemma addMulSub_swap (neg : ∀ k, W (-k) = -W k) (m n : ℤ) :
    addMulSub W m n = - addMulSub W n m := by
  rw [addMulSub, addMulSub, ← neg_sub, Int.neg_tdiv, neg]; ring
```

where `addMulSub W m n := W ((m + n).tdiv 2) * W ((m - n).tdiv 2)` (truncated division by 2).

In prose: **if `W` is an odd function** (`W(-k) = -W(k)` for all `k`), then the basic
elliptic-relation building block `addMulSub W m n = W((m+n)/2)·W((m−n)/2)` is **antisymmetric under
swapping its two arguments**: `addMulSub W m n = − addMulSub W n m`. Intuitively, swapping `m ↔ n`
fixes the first factor `W((m+n)/2)` (since `m+n` is symmetric) but negates the index of the second
factor (`m−n ↦ n−m = −(m−n)`); oddness of `W` then turns that index-negation into an overall sign.
The proof rewrites `(n−m).tdiv 2 = −((m−n).tdiv 2)` via `← neg_sub` + `Int.neg_tdiv`, pulls the sign
out of `W` with the oddness hypothesis `neg`, and finishes with `ring`.

Variables / typeclasses (Lean side):
- `{R : Type u} [CommRing R]` — coefficient ring (fully general).
- `(W : ℤ → R)` — the sequence.

Hypotheses:
- `(neg : ∀ k, W (-k) = -W k)` — `W` is odd. (This is the standard EDS property `W₋ₙ = −Wₙ`; see Phase 3.)
- `(m n : ℤ)` — the two indices.

Conclusion (math): `addMulSub W m n = − addMulSub W n m`.
Conclusion (Lean): an equation in `R` (`addMulSub W m n = - addMulSub W n m`).

This is the *antisymmetry* (argument-swap) cousin of the *invariance* lemmas `addMulSub_neg₀`
(line 184, negate first index → unchanged) and `addMulSub_neg₁` (line 188, negate second index →
unchanged, no oddness needed). All three are one-line sign/parity helpers for the same `def`.

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: a structural helper lemma — it records an antisymmetry of the internal building block
`addMulSub` under swapping its two indices. Not a named theorem, not a `## Main statements` entry, not
a person/place-named statement. (Literature width below is run EXHAUSTIVE regardless, per the
`addMulSub`-layer convention shared with the sibling reports.)

### One-line check (Phase 2b)

The lemma is one `rw [...]; ring` line. The only non-`ring`, non-unfold ingredient is `Int.neg_tdiv`
(`(-a).tdiv b = -(a.tdiv b)`) — present in Lean core (`Init/Data/Int/DivMod/Lemmas.lean`, confirmed
in the toolchain tree this run) — plus the oddness hypothesis `neg`. So against a mathlib that already
has `addMulSub`, the proof *is* its own inline composition: unfold + one core `Int` lemma + `neg` +
`ring`. Flags Phase 6 "COMPOSABLE."

---

### Literature search (Phase 3)

Concept identified as: **the oddness / antisymmetry of EDS- and elliptic-net terms** (`W₋ₙ = −Wₙ`,
equivalently `W(0)=0` together with antisymmetry) — a *standard, elementary structural property* —
here applied to show the half-index product `addMulSub` flips sign when its two indices are swapped.

Sources agree on the standard form: **yes**. The oddness `W(−n) = −W(n)` of an elliptic divisibility
sequence is uniformly stated as a basic fact and used without proof-ceremony:
- **Wikipedia, "Elliptic divisibility sequence"** — lists `W₋ₙ = −Wₙ` among the elementary
  properties of an EDS (with `W₀ = 0`, `W₁ = 1`).
- **K. Stange, "The Tate pairing via elliptic nets"** (arXiv:math/0702165) and **"Elliptic nets and
  elliptic curves"** (Algebra & Number Theory 5 (2011), no. 2) — the `net`/`rel₄` machinery in this
  file is a formalisation of Stange's elliptic nets; antisymmetry of the building blocks under index
  permutation is implicit in the net relations (the file's `relFin4_perm`, line 533, is exactly the
  full `Perm (Fin 4)` statement of this).
- **Ward, "Memoir on elliptic divisibility sequences"** (Amer. J. Math. 70 (1948)) — the founding
  source; oddness is part of the basic symmetry of the sequence.
- **Silverman–Stephens, "The sign of an elliptic divisibility sequence"** (arXiv:math/0402415) — the
  deeper *sign pattern* of an EDS; takes `W₋ₙ = −Wₙ` as given.

Most general standard form: there is **no named "standard form" for this particular lemma**. The
literature names (a) the oddness of `W`, and (b) the antisymmetry/permutation-symmetry of the net
relation — but the precise statement here ("an odd `W` makes the specific helper `addMulSub W m n =
W((m+n)/2)W((m−n)/2)` antisymmetric in `m ↔ n`") is a *formalisation-internal* bookkeeping identity
about a project-local `def`. It is not in the literature because `addMulSub` is not in the literature;
it is a Lean convenience (the file docstring at line 97 literally calls it out: "lemmas like
`addMulSub_neg₀` hold unconditionally" thanks to the `Int.tdiv` choice — the same applies verbatim to
`addMulSub_swap`).

Generality dimensions where the literature varies: only in *which* oddness statement is taken as
primitive (`W₋ₙ = −Wₙ` for EDS vs. `W(−v) = −W(v)` for general elliptic nets) — both are the same
antisymmetry of the sequence.

Disagreement with the literature: none. The lemma is a faithful (and elementary) consequence of the
standard oddness property; it carries no novel mathematical content of its own.

*(MCP note: ChatGPT-math MCP flagged down for this run per the task note; the literature sweep above
is from WebSearch-class sources plus the project's own Stange-net citations carried by the sibling
`addMulSub.md` / `rel₄.md` reports. The mathematical content — oddness of an EDS — is textbook and not
in doubt.)*

---

### Generality analysis — `EllSequence.addMulSub_swap`

Literature-standard form (Phase 3): the oddness of EDS terms `W(−n) = −W(n)` (taken here as the
hypothesis `neg`), with the conclusion being an antisymmetry of the project's `addMulSub` def under
index swap.

| # | Parameter / hypothesis              | Current Lean form              | Literature-standard form          | Weaker form exists? | Reason it can/can't be weakened |
|---|-------------------------------------|--------------------------------|------------------------------------|---------------------|----------------------------------|
| 1 | `[CommRing R]`                     | commutative ring               | arbitrary commutative ring         | **NO**              | already the floor; the proof uses only `+ − ·` and `ring`; no domain/field/characteristic needed. Even commutativity is barely used (only the final `ring` reorders the two `W` factors) — but `addMulSub`'s consumers are all `CommRing`, so dropping it buys nothing. |
| 2 | `(W : ℤ → R)`                      | unconstrained sequence         | unconstrained                      | NO                  | `W` is a bare hypothesis, as it must be (the def is pointwise in `W`'s values). |
| 3 | `(neg : ∀ k, W (-k) = -W k)`      | `W` odd (∀ k)                  | EDS oddness `W₋ₙ = −Wₙ`            | NO (already minimal) | the conclusion genuinely needs oddness at the single argument `(m−n)/2`; stating it for all `k` is the clean, idiomatic form and matches how the def's other lemmas (`addMulSub_neg₀`, `addMulSub_abs₀`) take it. No weaker hypothesis gives the unconditional antisymmetry. |
| 4 | `(m n : ℤ)`                        | two integer indices            | integer indices                    | NO                  | the half-index `tdiv 2` structure is intrinsic to `addMulSub`. |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL** (over `CommRing`, with the minimal `neg` hypothesis the
conclusion requires). Number of weakening opportunities found: **0**. Cost of restatement: n/a.

There is, however, a *packaging* observation (the sense used throughout the sibling reports): the
right unit to upstream is **not this lone lemma** but the `EllSequence` elliptic-relation layer it
belongs to. As a standalone public mathlib lemma `addMulSub_swap` is the wrong granularity — it is
internal scaffolding (ideally `private`/section-local) whose only job is to make the three
`rel₄_swap₀₁/₁₂/₂₃` transposition lemmas (lines 517–524) go through, which in turn assemble into the
full permutation symmetry `relFin4_perm` (line 533).

### Modern-idiom check (Phase 4c)

| #  | Question                                                                 | Applies? | Proposed reformulation | Mathlib downstream |
|----|--------------------------------------------------------------------------|----------|------------------------|--------------------|
|  1 | "let X be a foo" preambles → typeclasses/instances?                       | no       | — (`[CommRing R]` is already a class; `neg`/`W` are bare hypotheses as they must be) | — |
|  2 | sequences/metric → filters/nets/topology?                                | no       | — (an algebraic identity; no limits/topology) | — |
|  3 | construct object → universal-property class?                             | no       | — (it is an equation, not a construction) | — |
|  4 | set-with-closure-predicate → bundled substructure?                       | no       | — (not a substructure) | — |
|  5 | vector-space/metric/field-specific → weaken typeclass?                   | no       | — (already at `CommRing`) | — |
|  6 | 1-categorical → higher-categorical?                                      | no       | — (elementary commutative algebra) | — |
|  7 | concrete index (ℕ/ℤ/ℝ) → arbitrary group/monoid?                         | no       | — (the `tdiv 2` half-index is intrinsic; `ℤ` is the right domain) | — |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no**. One-line reason: this is an elementary sign/parity identity about a
concrete helper `def`; there is no contemporary reformulation that would compose better — the only
question is one of *granularity* (it ships with the `addMulSub` layer, not alone), which is the
packaging point already captured by the parent `addMulSub.md` verdict.

---

### Diamond / defeq risk (Phase 4.5)

**n/a — declaration kind is `lemma`.** (Lemmas introduce no definitional equalities and no
typeclass-search paths.)

---

### Mathlib search-status: `EllSequence.addMulSub_swap`

[A] Lean-Finder       "odd sequence half-index building block antisymmetric swap arguments W((m+n)/2)W((m-n)/2)"   no hits
[B] Loogle            `addMulSub`, `EllSequence.addMulSub_swap`, `?W (?m+?n) ... = -(?W ...)`     no hits — the symbol `addMulSub` is unknown to mathlib (consistent with `rel₄.md` / `addMulSub.md` / `addMulSub_neg₀.md` Loogle results)
[C] LeanSearch        "elliptic divisibility sequence odd implies building block antisymmetric in swap"   no hits
[D] Grep mathlib src  `addMulSub` / `addMulSub_swap` / `EllSequence` / `def net ` / `def rel₄` over `.lake/packages/mathlib/Mathlib/**`   **0 hits** (verified this run)
[E] Name pattern      `addMulSub_swap` / `_swap` antisymmetry over `addMulSub` in mathlib tree                no hits

Searched for both:
- the user's current form (`addMulSub_swap` about `EllSequence.addMulSub`) — **absent**: mathlib has
  no `EllSequence` namespace, no `addMulSub`, hence no lemma about it. Grepping the live mathlib copy
  at `…/.lake/packages/mathlib/Mathlib/NumberTheory/EllipticDivisibilitySequence.lean` confirms it
  contains only `IsEllSequence`/`IsDivSequence`/`preNormEDS`/`normEDS` and **still carries TODOs**
  (lines 44–45) for "prove that `normEDS` satisfies `IsEllDivSequence`" — i.e. the entire
  `addMulSub`/`rel₄`/`net` Stange machinery this lemma belongs to is **the project's WIP toward those
  very TODOs**, not yet upstream.
- the literature-standard neighbour — mathlib's EDS file *does* prove oddness/antisymmetry lemmas, but
  **for its own sequences**: `preNormEDS_neg`, `normEDS_neg`, `complEDS₂_neg`, `complEDS_neg` (e.g.
  `normEDS_neg : normEDS b c d (-n) = -normEDS b c d n`). These are the *analogues* for the mathlib
  `normEDS`/`preNormEDS` track — **not** a statement about the half-index `addMulSub` product, which
  mathlib does not define.

Concluded: **not in mathlib** (all 5 methods exhausted, plus the literature-standard oddness
neighbour). The closest mathlib relatives (`normEDS_neg` et al.) are about a *different* (mathlib)
object; they neither subsume nor supply this lemma.

---

### Call sites — `EllSequence.addMulSub_swap`

Internal use count: **3** within the declaring live file (NOT counting the `def` and the lemma
itself) — the most-used of the `addMulSub` sign/parity helpers.
External-to-file callers: **0 genuine external consumers**. (The lemma is *duplicated verbatim* into
two sibling forks — the HasseWeil auxiliary copy at line 126, used at 432/435/438; and the dead
`…Original` track at line 190 — but those are intra-repo forking/dedup, not downstream API consumers.)

| Caller file:line                                                                 | Usage pattern (one-line excerpt)                                  |
|----------------------------------------------------------------------------------|--------------------------------------------------------------------|
| `…/EllipticDivisibilitySequence.lean:518` (`rel₄_swap₀₁`)                         | `simp_rw [rel₄, addMulSub_swap W neg n m]; ring`                    |
| `…/EllipticDivisibilitySequence.lean:521` (`rel₄_swap₁₂`)                         | `simp_rw [rel₄, addMulSub_swap W neg r n]; ring`                    |
| `…/EllipticDivisibilitySequence.lean:524` (`rel₄_swap₂₃`)                         | `simp_rw [rel₄, addMulSub_swap W neg s r]; ring`                    |
| `…/HasseWeil/Auxiliary/EllipticDivisibilitySequence.lean:432/435/438`             | same three `rel₄_swap*` bodies — sibling-fork duplicates, not external consumers |
| `…/EllipticDivisibilitySequenceOriginal.lean:497/500/503`                         | same three `rel₄_swap*` bodies — dead duplicate track, slated for deletion |

These three consumers (`rel₄_swap₀₁/₁₂/₂₃`) are the per-transposition antisymmetry steps that the
generators-and-relations induction in `relFin4_perm` (line 533) uses to prove that the four-index
relation `rel₄` is invariant up to sign under the *whole* `Perm (Fin 4)`. So `addMulSub_swap` is the
load-bearing base case for the permutation-symmetry theorem of the layer.

Composability signal: **K = 3 genuine internal uses → real reusable internal API, but still entirely
*intra-layer*.** Unlike `addMulSub_neg₀` (K = 1, a possible-inline candidate), this lemma is clearly
worth keeping as a named helper *inside the `addMulSub` layer*. That does **not** make it a standalone
mathlib entry: its statement still mentions the project-local `addMulSub`, so it ships with the layer,
not separately.

---

### Composition check (Phase 6)

Can `EllSequence.addMulSub_swap` be derived from mathlib in ≤3 chained calls?

The question is subtle because the statement *mentions* `addMulSub`, which is not in mathlib — so
strictly, the lemma cannot even be *stated* against mathlib alone. Two readings:

- **Reading A (re-aimed at the parent layer, the honest one).** Once `addMulSub` is upstreamed as the
  layer's building block (parent verdict `YES-but-generalise-first`), this lemma is a **≤2-line
  consequence** of mathlib primitives already present:
  ```lean
  example (neg : ∀ k, W (-k) = -W k) (m n : ℤ) :
      addMulSub W m n = - addMulSub W n m := by
    rw [addMulSub, addMulSub, ← neg_sub, Int.neg_tdiv, neg]; ring
  ```
  The non-trivial ingredient — `Int.neg_tdiv : (-a).tdiv b = -(a.tdiv b)` — **is in mathlib/core**
  (it is what the def's `tdiv` choice is designed to exploit). So this is
  `rw [defn, ← neg_sub, Int.neg_tdiv, neg]; ring`: unfold (×2) + `neg_sub` (mathlib
  `Mathlib/Algebra/Group/Basic.lean`) + one core `Int` lemma + the oddness hypothesis + `ring`. That
  is a composition/inline, **not** a result requiring its own mathlib lemma — it should ship as a
  *section-local helper* alongside `addMulSub`, not as an independent public API entry.

- **Reading B (against today's mathlib).** `addMulSub` is absent, so there is no statement to
  compose — vacuously NOT-COMPOSABLE-because-unstatable. This collapses into the parent's
  "upstream the layer" plan.

Conclusion: **COMPOSABLE** (Reading A) — a ≤2-line `rw [addMulSub, ← neg_sub, Int.neg_tdiv, neg]; ring`
inline. It is bookkeeping internal to the `addMulSub` layer, not a free-standing mathlib lemma.

---

## Verdict: `EllSequence.addMulSub_swap`

**Category:** `NO-composable-from-mathlib`

**Evidence:**
- Literature search (Phase 3): the content is the **standard oddness/antisymmetry of EDS terms**
  (`W₋ₙ = −Wₙ`; Wikipedia EDS, Ward 1948, Stange's elliptic nets, Silverman–Stephens sign-of-an-EDS)
  propagated through the project-local helper `addMulSub`. No named "standard form" for the
  helper-swap identity — it is formalisation-internal.
- Generality analysis (Phase 4): **MAXIMALLY GENERAL** over `CommRing` with the minimal `neg`
  hypothesis (0 weakenings); Phase 4c found no cleaner modern idiom — only a *granularity* point
  (ships with the `addMulSub` layer, not alone).
- Mathlib search (Phase 5): **not in mathlib**; the closest relatives (`normEDS_neg`, `preNormEDS_neg`,
  `complEDS₂_neg`) are oddness lemmas for *mathlib's own* sequences, not for the half-index
  `addMulSub` product, which mathlib does not define. Mathlib's EDS file still carries the open TODOs
  that this project's `addMulSub`/`rel₄`/`net` layer is built to discharge.
- Composition check (Phase 6): **COMPOSABLE** — a ≤2-line `rw [addMulSub, ← neg_sub, Int.neg_tdiv,
  neg]; ring` once the parent `addMulSub` def exists; the key step `Int.neg_tdiv` is already in
  mathlib/core, `neg_sub` in mathlib `Algebra/Group/Basic`.
- Call sites (Phase 6.0): **K = 3** genuine internal uses (the `rel₄_swap₀₁/₁₂/₂₃` transpositions,
  which assemble into `relFin4_perm`); the only other copies are sibling-fork duplicates. Real
  reusable *intra-layer* API — but not a standalone contribution.
- Diamond/defeq risk (Phase 4.5): **n/a** (it is a `lemma`).

**Rationale.**

`addMulSub_swap` is a one-line structural lemma whose entire job is to record that the project's
internal building block `addMulSub W m n = W((m+n)/2)·W((m−n)/2)` is **antisymmetric under swapping
its two indices** (`addMulSub W m n = − addMulSub W n m`) **when `W` is odd**. The mathematical fact
it leans on — oddness of elliptic-(divisibility-)sequence terms, `W(−n) = −W(n)` — is
textbook-elementary and stated without ceremony across the literature (Wikipedia EDS; Ward's 1948
memoir; Stange's nets; the "sign of an EDS" papers). The lemma adds no new mathematics; it threads
that oddness through a *formalisation-specific* definition, and the file's own docstring (line 97)
flags exactly this: the `Int.tdiv`-by-2 choice exists precisely so the family of `addMulSub` sign
lemmas "hold unconditionally."

Because the lemma's *statement* mentions `EllSequence.addMulSub` — which is **not** in mathlib (the
entire `EllSequence` four-index-relation layer is absent; the live mathlib4 EDS file, verified this
run, contains only `IsEllSequence`/`normEDS`/`preNormEDS` and still lists the open TODOs this layer
targets) — it cannot be a standalone mathlib addition. The correct framing is the skill's
**re-aim-to-parent** rule: the parent `def` `addMulSub` is destined for mathlib only *as the internal
building block of the whole elliptic-relation layer* (parent verdict `YES-but-generalise-first`,
packaging sense), and that layer's sign/parity lemmas (`addMulSub_neg₀/₁`, `addMulSub_abs₀/₁`,
`addMulSub_swap`) are explicitly named in `addMulSub.md` as part of "what to upstream." Within that PR
this lemma is **not** an independently-citable API entry — it is a (worth-keeping, since K = 3)
section-local helper that, against the (then-present) `addMulSub` plus mathlib's existing
`Int.neg_tdiv`/`neg_sub`, reduces to a ≤2-line `rw …; ring`. Hence the standalone verdict is
**NO-composable-from-mathlib**: mathlib has the building blocks (`Int.neg_tdiv`, `neg_sub`, `CommRing`
`ring`, the oddness hypothesis), the form is a 1–2 call inline, and no *separate* public lemma is
warranted beyond the layer it belongs to.

*(Contrast with the sibling `addMulSub_neg₀` (K = 1, possible-inline): `addMulSub_swap` has three real
consumers and powers the permutation-symmetry theorem, so it is more clearly "keep as a named helper"
— but the granularity conclusion for mathlib is identical: it ships inside the `addMulSub` layer, not
on its own.)*

**WHY not (refactor-actionable).**
Mathlib has the building blocks; this lemma is a 1–2 mathlib-call composition once `addMulSub` exists.

- Mathlib building blocks:
  - `Int.neg_tdiv` (mathlib/core, `Init/Data/Int/DivMod/Lemmas.lean`) — `(-a).tdiv b = -(a.tdiv b)`,
    the load-bearing step (and the raison d'être of the def's `tdiv` choice).
  - `neg_sub` (mathlib `Mathlib/Algebra/Group/Basic.lean`) — `-(a - b) = b - a`, to turn the swapped
    second index `n − m` into `−(m − n)`.
  - the `neg` hypothesis (oddness of `W`) + `ring` over `[CommRing R]` — to pull the sign out of `W`
    and reorder the two factors.
- Composition sketch (≤3 lines — exactly the existing proof, which is itself the inline):
  ```lean
  example (neg : ∀ k, W (-k) = -W k) (m n : ℤ) :
      addMulSub W m n = - addMulSub W n m := by
    rw [addMulSub, addMulSub, ← neg_sub, Int.neg_tdiv, neg]; ring
  ```
- Call sites in our project (Phase 6.0): **K = 3** genuine (`rel₄_swap₀₁/₁₂/₂₃`, lines 518/521/524),
  plus two sibling-fork duplicate sets (HasseWeil 432/435/438; `…Original` 497/500/503).

Refactor plan (two-layer, both already on the project's books):
1. **Intra-repo dedup (now, a `/cleanup` chore):** there are three copies of this lemma (NagellLutz
   live; `…Original.lean` dead; HasseWeil auxiliary). Collapse to **one** source of truth — delete the
   `…Original.lean` track and have HasseWeil import the NagellLutz `EllSequence` layer instead of
   vendoring it.
2. **Upstream-with-the-layer (later):** when the `addMulSub`/`rel₄`/`net` layer is PR'd to mathlib
   (closing the `EllipticDivisibilitySequence.lean` TODOs at lines 44–45), this lemma goes in *as a
   section-local helper* of that layer — keep the name (K = 3 earns it), keep it near `addMulSub`,
   keep the `tdiv`-driven one-line proof. It is **not** a separate public lemma and **not** a separate
   PR.
