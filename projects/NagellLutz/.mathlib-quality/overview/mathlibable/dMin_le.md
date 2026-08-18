# Mathlibability assessment: `EllSequence.dMin_le`

## Verdict

**`NO-composable-from-mathlib`** — a 2-line parity-bookkeeping helper whose statement is *about the
project-local def* `dMin a = if Even a then 0 else 1`. Its sole mathematical content is one
application of mathlib's `Int.negOnePow_eq_one_iff` together with elementary nonnegativity reasoning;
it is not a standard named result and cannot be added to mathlib verbatim (it mentions a local def).

- **Bucket:** `NO-composable-from-mathlib`
- **Qualified name:** `EllSequence.dMin_le`
- **One-line rationale:** Wrapper over local `dMin`; content = `Int.negOnePow_eq_one_iff` + `0 ≤ b ⇒ b = 0 ∨ 1 ≤ b`. ≤ 3 mathlib calls.

---

## 1. Exact statement and proof (from source)

File: `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:406`
Namespace: `EllSequence` (opened L90, closed L597), so the true qualified name is
**`EllSequence.dMin_le`**.

```lean
/- L381-382 -/
/-- The minimal possible fourth index in the four-index elliptic relation given the first index. -/
def dMin (a : ℤ) : ℤ := if Even a then 0 else 1

/- L406-408 -/
lemma dMin_le {a b : ℤ} (same : a.negOnePow = b.negOnePow) (h : 0 ≤ b) : dMin a ≤ b := by
  rw [dMin]; split_ifs with odd
  exacts [h, h.lt_of_ne (by rintro rfl; exact odd (a.negOnePow_eq_one_iff.mp same))]
```

Reading: `negOnePow n = (-1 : ℤˣ) ^ n`, so `a.negOnePow = b.negOnePow` means `a` and `b` have the
**same parity**. The lemma says: if `a`, `b` share a parity and `b ≥ 0`, then `dMin a ≤ b`, i.e.

- `a` even ⇒ `dMin a = 0 ≤ b` (immediate from `h`);
- `a` odd ⇒ `dMin a = 1`, and since `b ≥ 0` it suffices that `b ≠ 0`; if `b = 0` then
  `a.negOnePow = (0).negOnePow = 1`, so `negOnePow_eq_one_iff` forces `Even a`, contradicting the
  odd branch. Hence `0 < b`, i.e. `1 ≤ b`.

Mathematically: "the least nonnegative integer of the same parity as `a` is `≤` any nonnegative
integer of that parity." Pure parity arithmetic.

### Role in the development
`dMin a` / `cMin a = dMin a + 2` package the **base case of the strong induction** (`rel₄_of_min₂`,
L457) that proves the four-index elliptic relation `rel₄`. `dMin_le` is the small order fact that
lets the induction conclude `dMin a ≤ d` for the actual minimal valid fourth index `d` (any
nonnegative `d` of the right parity is `≥ dMin a`). It is consumed locally inside the `Rel₄OfValid`
machinery; it is not exported as a `## Main statement`.

---

## 2. Literature search

- **WebSearch** ("elliptic divisibility sequence minimal index parity division polynomial recurrence
  base case"): the EDS sources (Ward; Shipsey; Stange; Silverman; eprint 2008/444; arXiv 1108.3051,
  1909.12654) use **"minimal index"** exclusively for **Mazur's theorem** — the least `N` with
  `W_N = 0`, `N ∈ {2,…,10,12}`. That is a deep result about rank-of-apparition / zeros of the
  sequence, **entirely unrelated** to `if Even a then 0 else 1` (the smallest nonnegative integer of
  a given parity). No source names "minimal nonnegative integer of given parity" as a concept.
- **ChatGPT MCP:** unavailable (Codex backend down, as the task warned). Compensated with the
  WebSearch above plus a direct grep of the mathlib source tree (§3), which is more authoritative
  than the search index for an existence check.

**Conclusion:** `dMin` and `dMin_le` are **formalization-internal bookkeeping**, not standard named
mathematics. There is no literature "most general form" to target.

---

## 3. Mathlib search (five-method, source-level)

The dedicated `lean_loogle` / `lean_leansearch` index tools were not surfaced in this environment, so
the search was done against the **actual pinned mathlib source tree**
(`.lake/packages/mathlib/`), which directly answers the existence question.

1. **Name grep** — `grep -rln "dMin\|cMin\|Rel₄OfValid\|HaveSameParity\|negOnePow_eq_one_iff"` over
   `Mathlib/`:
   - `Mathlib/Algebra/Ring/NegOnePow.lean` — only because it *defines* `negOnePow_eq_one_iff` (the
     lemma we reuse); contains no `dMin`.
   - `Mathlib/Data/Ordmap/Ordset.lean`, `Ordnode.lean`, `Invariants.lean` — `dMin`/`findMin'` there
     is the **ordered-map minimum key**, a wholly different concept (data structures), not EDS.
   - No EDS `dMin`/`cMin`/`Rel₄OfValid` anywhere.
2. **Mathlib EDS file** — `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean` (David Angdinata's
   original, which this project forks/extends): grep for
   `dMin|cMin|Rel₄OfValid|negOnePow|rel₄|HaveSameParity` returns **nothing**. The whole
   `dMin/cMin/Rel₄OfValid/rel₄/rel₆/HaveSameParity₄` apparatus is **new project work**, absent from
   mathlib. So this decl is *not* an already-upstreamed duplicate.
3. **DivisionPolynomial files** — `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/`
   (`Basic.lean`, the project's forked track) contain no parity-index helper of this kind.
4. **Statement-shape search** — there is no mathlib lemma of the form "same parity + nonneg ⇒
   `(if Even a then 0 else 1) ≤ b`"; such a lemma would never be stated because it bundles a bespoke
   indicator. The closest *primitives* are all present (see §4).
5. **Companion assessments** — sibling reports `cMin.md` and `negOnePow_cMin_eq_dMin.md` in this same
   directory already classified the `dMin`/`cMin` family as project-local proof-engineering
   (`NO-composable-from-mathlib`), consistent with this verdict.

**Conclusion:** mathlib does **not** have `dMin_le` or any generalization of it; nor does it have the
`dMin` it is phrased over.

---

## 4. Generality analysis

The statement is **strictly less general than its own ingredients** would allow, because it is welded
to the local def `dMin`. Stripping `dMin` away, the "maximally general" content is just:

> for `a b : ℤ` with `a.negOnePow = b.negOnePow` and `0 ≤ b`, one has `(if Even a then 0 else 1) ≤ b`.

That is already the whole truth — there is no domain to generalize to (it is intrinsically about
`ℤ`-parity and the literals `0,1`; a general ordered additive group has neither `Even` nor a
canonical `1` to compare against), and no literature concept to align with (§2). So there is **no
"generalise-first"** action: the only thing one could do is delete the `dMin` wrapper, at which point
it stops being a reusable lemma and becomes an inline two-case argument.

---

## 5. Composition check (≤ 3 mathlib calls)

The proof itself is the composition certificate. Discharging the (only nontrivial) odd branch:

1. `Int.negOnePow_eq_one_iff` — `n.negOnePow = 1 ↔ Even n` (mathlib,
   `Mathlib/Algebra/Ring/NegOnePow.lean:63`), applied to turn `a.negOnePow = (0).negOnePow = 1` into
   `Even a` for the contradiction. *[call 1]*
2. `LE.le.lt_of_ne` / nonnegativity: from `0 ≤ b` and `b ≠ 0` get `0 < b`, i.e. `1 ≤ b` over `ℤ`
   (`Int.lt_iff_add_one_le` / order primitives). *[call 2]*
3. The even branch is literally the hypothesis `h : 0 ≤ b`. *[no real call]*

So **≤ 3 mathlib lemmas** reconstruct it directly — and indeed the source proof is exactly this,
two `exacts` after a `split_ifs`. This is the definition of `NO-composable-from-mathlib`.

---

## 6. Decision

| Criterion | Finding |
|---|---|
| Standard named result in literature? | **No** — internal bookkeeping; "minimal index" in EDS means Mazur's zero-index, unrelated. |
| Already in mathlib (this or general form)? | **No** — `dMin`/`cMin`/`Rel₄OfValid` are new project work; mathlib EDS/DivisionPolynomial files lack them. |
| Statement addable to mathlib verbatim? | **No** — it references the project-local def `EllSequence.dMin`. |
| More general form worth upstreaming? | **No** — content is intrinsically `ℤ`-parity + literals `0,1`; nothing to generalize. |
| Composable from ≤ 3 mathlib calls? | **Yes** — `Int.negOnePow_eq_one_iff` + `0 ≤ b ⇒ 1 ≤ b ∨ b = 0`; exactly the source proof. |

**Final bucket: `NO-composable-from-mathlib`.**

A 2-line, parity-driven order helper that exists only to feed the local `dMin`/`cMin` base-case
induction. It is not standard mathematics, it cannot be added to mathlib as stated (local def in the
signature), and its mathematical substance is a ≤ 3-call composition of existing mathlib primitives
(chiefly `Int.negOnePow_eq_one_iff`). It should stay project-local. (If the surrounding `Rel₄OfValid`
EDS-relation machinery is ever upstreamed wholesale, `dMin_le` rides along as a private helper — but
it is never an independent mathlib contribution.)
