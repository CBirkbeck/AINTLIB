# Mathlibable assessment — `normEDS_two_three_two`

**Verdict: NO-mathlib-has-it** (precisely: *NO — it is upstream mathlib-author code, in-flight via
mathlib4 PR #13782; not a standalone AINTLIB contribution candidate*)

- **Qualified name:** `normEDS_two_three_two` (top-level — no enclosing namespace)
- **Location:** `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:1234`
- **Date:** 2026-06-21
- **Assessor run:** `/overview` Step-9 mathlibable, NagellLutz project (re-run; concurs with the
  2026-06-18 report and the `mathlibable_ledger.tsv` row, and adds the explicit PR + arXiv
  provenance the earlier pass left unnamed).

---

## 1. Exact statement and proof (from source)

```lean
omit ellW ellU in
lemma normEDS_two_three_two : normEDS (2 : ℤ) 3 2 = id := by
  apply IsEllSequence.ext IsEllSequence.normEDS isEllSequence_id <;>
    simp only [normEDS_one, normEDS_two, normEDS_three, normEDS_four]
  exacts [mem_nonZeroDivisors_of_ne_zero one_ne_zero,
    mem_nonZeroDivisors_of_ne_zero two_ne_zero, rfl, rfl, rfl, rfl]
```

**Qualified name VERIFIED.** Namespace stack at line 1234: the last `namespace` opened before this
point is `namespace IsEllSequence` (l.643), closed at `end IsEllSequence` (l.702). The lemma sits
inside `section NormEDS` (l.881) and an inner anonymous `section` (l.1203) carrying only
`variable`/`open` — sections do not contribute to the qualified name. So the fully-qualified name is
plainly **`normEDS_two_three_two`** (no prefix). `omit ellW ellU in` strips the section's
`IsEllSequence` hypotheses; the lemma is unconditional.

**What it says.** Over `R = ℤ`, the *normalised* elliptic divisibility sequence with seed parameters
`(b, c, d) = (2, 3, 2)` is exactly the identity sequence `id : ℤ → ℤ`, i.e. `normEDS 2 3 2 n = n`
for all `n ∈ ℤ`. This is the canonical degenerate ("singular") EDS — Ward's trivial sequence
`…,-2,-1,0,1,2,3,…`.

**Why it is true.** A normalised EDS is pinned down by its first four terms via mathlib's
`normEDS_one/two/three/four`: `normEDS b c d 1 = 1`, `normEDS b c d 2 = b`, `normEDS b c d 3 = c`,
`normEDS b c d 4 = d * b`. At `(b,c,d)=(2,3,2)`: `W 1 = 1, W 2 = 2, W 3 = 3, W 4 = 2·2 = 4` —
agreeing with `id` on `1,2,3,4`. The proof invokes the **project** uniqueness lemma
`IsEllSequence.ext` (l.1217): two elliptic sequences agreeing on terms 1–4, with `W 1` and `W 2`
non-zero-divisors, are equal. Side goals: `normEDS 2 3 2` is an elliptic sequence
(`IsEllSequence.normEDS`), `id` is one (`isEllSequence_id`), `1, 2 ∈ ℤ⁰`
(`mem_nonZeroDivisors_of_ne_zero`), and the four term-equalities (`rfl` after `simp`).

**Role in the project.** Evaluation bridge that makes the universal (generic-coefficient) EDS
usable. Consumers: `universalNormEDS_ne_zero` (l.1250) and `compl₂EDS_two_three_two` (l.1241) in the
same file; the parallel HasseWeil fork (`HasseWeil/Auxiliary/EllipticDivisibilitySequence.lean:709`,
byte-identical statement and proof; `…/DivisionPolynomial.lean:192`); and `LutzNagell/ZSMul.lean:116`.

---

## 2. Mathlib search — five methods, exhaustive

**Is it in mathlib? No. And neither is the API (`IsEllSequence.ext`, `universalNormEDS`) it is
stated and proved over.**

1. **Direct source read.** Pinned mathlib (rev `09b373db6e24`, toolchain `v4.32.0-rc1`):
   `.lake/packages/mathlib/Mathlib/NumberTheory/EllipticDivisibilitySequence.lean` is the **547-line**
   upstream version. Full `grep -nE '^(lemma|theorem|def|noncomputable def|...)'` listing of that
   file: it has `IsEllSequence`, `IsDivSequence`, `IsEllDivSequence`, `isEllSequence_id`,
   `preNormEDS'/preNormEDS`, `complEDS₂`, `normEDS`,
   `normEDS_zero/one/two/three/four/neg/ofNat`, `normEDS_even/odd`, `normEDS_mul_complEDS₂`,
   `normEDS_dvd_normEDS_two_mul`, `complEDS'/complEDS`, the `normEDSRec` recursors, and the `map_*`
   homomorphism lemmas. It does **NOT** contain `normEDS_two_three_two`, `IsEllSequence.ext`, any
   uniqueness/extensionality lemma, `IsEllSequence.normEDS`, `IsEllDivSequence.eq_normEDS`, or
   `universalNormEDS`. The project file is a **1672-line fork** adding exactly that missing surface
   (same "Copyright (c) 2024 David Kurniadi Angdinata" header).
2. **Exhaustive repo-wide grep over `.lake/packages/mathlib/Mathlib/`** for `two_three_two`,
   `normEDS_id`, `normEDS .* = id`, `preNormEDS_id`, `IsEllSequence\.ext` — **zero hits**. No `= id`
   equation for any EDS anywhere in mathlib (NumberTheory + AlgebraicGeometry/EllipticCurve/
   DivisionPolynomial both checked).
3. **Published mathlib4 docs** (`mathlib4_docs/.../EllipticDivisibilitySequence.html`, current HEAD,
   ≥ pinned rev): confirms `complEDS`/`normEDS_*`/`isEllSequence_id` are present but
   `IsEllSequence.ext`, `normEDS_two_three_two`, `universalNormEDS`, `compl₂EDS`, and any
   extensionality lemma are **absent**. So even the latest published mathlib lacks this.
4. **Name/shape search.** (`leansearch`/`loogle` index not reachable in this env; substituted by the
   authoritative source + docs reads above, which dominate the index for a present/absent question.)
   No `normEDS … = id`, no `IsEllSequence`-ext-shaped lemma. `isEllSequence_id` exists but only
   asserts `id` *is* an elliptic sequence — it does not identify it with any `normEDS`.
5. **Consumer/duplication check.** The only other copy in the whole repo is the HasseWeil fork (same
   author lineage), identical statement+proof — an *internal* duplication of the same
   pending-upstream lemma, not an independent mathlib candidate.

---

## 3. Literature search

- **Ward, *Memoir on Elliptic Divisibility Sequences*** (the file's cited reference) and the
  Wikipedia/EDS literature: the identity sequence `W(n)=n` is the standard **degenerate/singular**
  EDS ("up to equivalence a singular sequence is either the trivial sequence `W_n = n` or a Lucas
  sequence"). For the normalised framework it has `W₁=1, W₂=2, W₃=3, W₄=4`, forcing `(b,c,d)=(2,3,2)`.
  Universally treated as a *worked example / boundary case*, never a named numbered theorem.
- **arXiv 2604.05280, *On Elliptic Sequences over Commutative Rings*** — the modern source behind
  this formalisation. It develops the elementary, purely algebraic theory of elliptic sequences over
  commutative rings (uniqueness from initial terms, the universal/generic sequence) and states
  explicitly that *"this work was motivated by a pursuit of an elementary, purely algebraic proof for
  formalization in Lean (joint work with David Kurniadi Angdinata) and most results are included in
  the pull request to Lean's Mathlib, in the file `EllipticDivisibilitySequence.lean`."* It links
  directly to **`leanprover-community/mathlib4/pull/13782`**. There the `(2,3,2)` specialisation is a
  **computational instance**, not a standalone named theorem; the load-bearing general result is the
  extensionality/uniqueness theorem (the project's `IsEllSequence.ext`).

**Conclusion of literature pass:** the *mathematics* of the surrounding API (uniqueness over
commutative rings, the universal sequence) is genuinely mathlib-worthy and is exactly what PR #13782
delivers — but `normEDS_two_three_two` itself is a one-line evaluation corollary, not a literature
theorem.

---

## 4. Generality analysis

There is **no weaker/more-general form to lift this to**: the statement is the maximally-specific
numerical instance `(b,c,d)=(2,3,2)`, with target literally `id : ℤ → ℤ`. Its honest generalisation
is precisely the uniqueness lemma `IsEllSequence.ext` (general `R`, general first four terms), of
which this is the `(W₁,b,c,d)=(1,2,3,2)` corollary — and that general lemma is already the project's,
headed to mathlib via PR #13782. So "generalise first" does not apply: the general statement already
exists upstream-bound; this is its intended ℤ specialisation, kept because it is the convenient
bridge the later `universalNormEDS` arguments call.

---

## 5. Composition check — can ≤3 mathlib calls give it?

**No, not from *current* mathlib.** The proof's single non-trivial step is `IsEllSequence.ext`
(determinacy of an elliptic sequence by its first four terms when `W 1, W 2 ∈ R⁰`), which is **not in
mathlib**. Without it, proving `normEDS 2 3 2 = id` means `funext` + `Int.negInduction` + a
`normEDSRec` strong induction reconciling the even/odd EDS recurrences against `id` — re-deriving the
entire content of `IsEllSequence.ext` (~30+ lines), far beyond a 3-call composition. The remaining
ingredients (`normEDS_one..four`, `isEllSequence_id`, `IsEllSequence.normEDS`,
`mem_nonZeroDivisors_of_ne_zero`) *are* in mathlib (except `IsEllSequence.normEDS`, also fork-only),
but the linchpin is not. Hence **not** `NO-composable-from-mathlib` on present mathlib. (Once PR
#13782 lands and `IsEllSequence.ext` is upstream, this becomes a literal 1-line `apply` — which is
why it travels *with* that PR rather than as an independent submission.)

---

## 6. Five-bucket verdict

**NO-mathlib-has-it** — in the precise sense: *this is upstream mathlib-author code (David Kurniadi
Angdinata, the original mathlib EDS author), forked here from the in-flight
`leanprover-community/mathlib4` PR #13782 documented in arXiv 2604.05280.* It is not an AINTLIB
original to evaluate for inclusion; it is a forward-port of pending upstream content. The correct
dedup action is **track the PR and drop the fork (in both NagellLutz and HasseWeil) once it merges**,
not "submit to mathlib."

Why not the neighbours:
- **NOT YES-add-as-is / YES-but-generalise-first** — submitting it would duplicate its own author's
  open PR; and its honest generalisation (`IsEllSequence.ext`) is already in that PR.
- **NOT NO-composable-from-mathlib** — *current* mathlib cannot reach it in ≤3 calls; the required
  `IsEllSequence.ext` is itself not yet upstream.
- **NOT BORDERLINE** — the provenance (author + arXiv→PR #13782 link) and the exhaustive
  source/docs reads make the situation unambiguous.

*(Note for a human: the genuinely upstream-worthy unit is the **uniqueness layer** —
`IsEllSequence.ext` / `IsEllDivSequence.eq_normEDS` — which closes mathlib's existing TODO;
`normEDS_two_three_two` is just its convenient ℤ-instance. Track PR #13782 rather than this leaf.)*

Concurs with the prior 2026-06-18 report and the `mathlibable_ledger.tsv` row
(`normEDS_two_three_two → NO-mathlib-has-it`).
