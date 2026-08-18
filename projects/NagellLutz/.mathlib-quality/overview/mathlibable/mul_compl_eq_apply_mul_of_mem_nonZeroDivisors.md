# Mathlibable assessment — `IsEllSequence.mul_compl_eq_apply_mul_of_mem_nonZeroDivisors`

**Project:** NagellLutz (Nagell–Lutz; elliptic curves; division polynomials; elliptic divisibility sequences)
**File:** `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:1296` (decl line; `omit`/doc-comment start at 1291–1295)
**Date:** 2026-06-21
**Mathlib pin checked:** `09b373db6e24` (leanprover/lean4 v4.32.0-rc1) — current as of today.

**Verdict: `YES-but-generalise-first`**

> The content — the division-free identity `W(m) · compl(m,n) = W(nm)` for an arbitrary
> elliptic sequence over a commutative ring, the engine behind `W(m) ∣ W(nm)` — is wanted by
> mathlib: it discharges a standing in-file TODO and is the published result Xu, *On Elliptic
> Sequences over Commutative Rings* (arXiv:2604.05280, 2026), §6. But it must NOT be merged
> verbatim: it is phrased over the fork-local `EllSequence.compl`/`compl'`, which **duplicate**
> mathlib's already-present `complEDS`/`complEDS'`, and its `mem` (non-zero-divisor) hypothesis is —
> by the lemma's own docstring — **redundant**. Reconcile with the upstream `complEDS` API and drop
> `mem` before landing.

---

## 1. The declaration (verified)

- **Verified qualified name:** `IsEllSequence.mul_compl_eq_apply_mul_of_mem_nonZeroDivisors`.
  Declared with an explicit `IsEllSequence.` prefix at line 1296; the only enclosing scopes are
  anonymous `section`s plus `section Divisibility` / `section Complement` (no `namespace
  IsEllSequence` is open here), so the full name is exactly this. The base name in the ticket
  (`mul_compl_eq_apply_mul_of_mem_nonZeroDivisors`) and the parsed guess both check out.

**Statement, with the ambient `variable`/`include` context (lines 1205–1296):**

```lean
variable {R : Type u} [CommRing R] (W : ℤ → R)
  (ellW : IsEllSequence W)              -- W is an elliptic sequence
  (one : W 1 ∈ R⁰) (two : W 2 ∈ R⁰)    -- first two terms are non-zero-divisors
  (W₁ compl₂ : ℤ → R)
  (h₁ : ∀ m, W 1 * W₁ m = W m)          -- W₁ represents  W(m)/W(1)
  (h₂ : ∀ m, W m * compl₂ m = W (2 * m))-- compl₂ represents W(2m)/W(m)
  (m n : ℤ)

/-- If `W` is an elliptic sequence whose first two terms are not zero divisors,
the sequence constructed above indeed gives `W(n*m)` when multiplied by `W(m)`.
The condition `mem` is actually redundant because `W` is a multiple of a normalised EDS
by the other assumptions, so we can conclude using `normEDS_mul_compl` below. -/
lemma IsEllSequence.mul_compl_eq_apply_mul_of_mem_nonZeroDivisors (mem : W m ∈ R⁰) :
    W m * compl W₁ compl₂ m n = W (n * m) := by
  induction n using Int.negInduction with
  | nat n =>
    refine n.strong_induction_on fun n ih ↦ ?_
    -- n = 0, 1 are base cases (compl' 0 = 0, compl' 1 = 1);
    -- for n ≥ 2 split parity:
    --   even n: pull out compl₂ via h₂ and one recursive ih;
    --   odd  n: multiply by the non-zero-divisor  W m · W 1 ^ 2,
    --           apply the elliptic relation `ellW ((k+1+1)m) ((k+1)m) 1`,
    --           rewrite with h₁ and two ih's, then `mul_cancel_right_mem_nonZeroDivisors`.
  | neg hn n => rw [neg_mul, ellW.neg one two, compl_neg, mul_neg, hn n]
```

`EllSequence.compl`/`compl'` (lines 1085–1099) are the fork's division-free construction of
`W(nm)/W(m)` from two abstract auxiliary sequences `W₁ ≈ W(·)/W(1)` and `compl₂ ≈ W(2·)/W(·)`. This
lemma is the **payoff theorem** justifying that construction: multiplying it back by `W(m)` recovers
`W(nm)` exactly, hence `W(m) ∣ W(nm)`.

**Where it sits in the dependency chain (its reason to exist):**
`mul_compl_eq_apply_mul_of_mem_nonZeroDivisors`
→ `normEDS_mul_complEDS_of_mem` (1323, specialises `W := normEDS b c d`)
→ `normEDS_mul_complEDS` (1338, kills `mem` via the universal-EDS / `aeval` domain trick)
→ `normEDS_mul_complEDS_div` (1349) and the EDS divisibility theorems
(`IsEllSequence.eq_normEDS_of_dvd` 1271, `IsEllDivSequence.eq_normEDS` 1280).
It is an internal engine, not a leaf — it is consumed only inside this file.

---

## 2. Literature search

**Originating source — direct hit.** Junyan Xu, **"On Elliptic Sequences over Commutative Rings"**,
arXiv:2604.05280 (v1, 8 Apr 2026). §6 (Thm 6.1 / 6.2) defines, for an elliptic sequence `W` over a
commutative ring, exactly this division-free "complement" sequence representing `W(nm)/W(m)`, and
proves the identity `W(m) · compl(m,n) = W(nm)` under regularity (non-zero-divisor) hypotheses on the
low terms. The paper explicitly links its statements to the mathlib `EllipticDivisibilitySequence`
Lean code (`normEDS`, `preNormEDS`, …). So this project's file is the **formalization track for that
paper**, and the target lemma is the Lean statement of (the engine of) Thm 6.1/6.2. This is exactly
the "literature-standard form": maximal-generality (arbitrary commutative ring `R`, arbitrary
`IsEllSequence W`), which is what the paper proves.

**Classical background.** Over `ℤ` this is the Ward/Shipsey "non-linear recurrence ⇒ divisibility"
property of EDS (`n ∣ N ⟹ W_n ∣ W_N`): Wikipedia "Elliptic divisibility sequence"; Ward (1948);
Shipsey thesis (2001); Silverman et al. The commutative-ring, non-zero-divisor refinement (needed
because one cannot divide) is the Xu paper's contribution and is precisely what the `R⁰` hypotheses
encode. No competing, more-general published form exists — "elliptic sequence over a commutative
ring with regular low terms" is already the top of the generality ladder.

*(WebSearch surfaced the Xu paper and the mathlib module; the mathlib4-docs page and the local
mathlib checkout were used as the authoritative index for the pinned version. ChatGPT MCP not needed
— the literature is unambiguous.)*

---

## 3. Mathlib search (five methods)

Authoritative index = the pinned checkout
`.lake/packages/mathlib/Mathlib/NumberTheory/EllipticDivisibilitySequence.lean` (`09b373db`,
2026-06-21), cross-checked against the online `mathlib4_docs` for the same module.

| Method | Query | Result |
|---|---|---|
| grep name | `mul_compl_eq_apply`, `mul_compl`, `nonZeroDivisor.*compl` in mathlib | **absent** |
| grep statement | `complEDS … * … = … (n * m)` general product identity | **absent** (only the `₂` doubling case) |
| grep API family | all `compl*` decls in upstream | `complEDS₂`, `complEDS'`, `complEDS`, their `_zero/_one/_neg/_even/_odd`, `complEDSRec'/Rec`, `map_compl*` — **all specialised to `normEDS`**; **no abstract `IsEllSequence` complement** |
| docs page | mathlib4_docs module listing | confirms the same list; **no** `mul_compl`, **no** abstract-sequence / `nonZeroDivisors` complement lemma |
| TODO scan | module docstring | two open TODOs: *"prove that `normEDS` satisfies `IsEllDivSequence`"* and *"prove that a normalised sequence satisfying `IsEllDivSequence` can be given by `normEDS`"* — **this lemma is the engine for the second** |

What mathlib **does** have: the **doubling** special case
`normEDS_mul_complEDS₂ : normEDS b c d k * complEDS₂ b c d k = normEDS b c d (2 * k)` (the `n = 2`
instance), plus the `complEDS` definition and its even/odd unfolds and recursors. What it is
**missing**: (a) any general `normEDS b c d m * complEDS b c d m n = normEDS b c d (n * m)`, and
(b) the abstract `IsEllSequence`-level statement — which is the target. **Not in mathlib.** → rules
out `NO-mathlib-has-it`.

---

## 4. Generality analysis

The lemma is already at the literature ceiling on the parameters that matter:
- `R` an arbitrary `CommRing` (not `ℤ`, not a domain);
- `W` an arbitrary `IsEllSequence` (not just `normEDS`);
- `W₁`, `compl₂` arbitrary sequences satisfying only the two abstraction equations `h₁`, `h₂`;
- hypotheses are the minimal regularity `W 1, W 2 ∈ R⁰`.

This matches Xu §6 exactly. There is no *mathematical* weakening left to do. The "generalise-first"
flag is therefore **not** about weakening hypotheses for their own sake, but about two packaging
defects that block a verbatim merge:

1. **Fork-local duplication.** It is stated via `EllSequence.compl`/`compl'`, the fork's parallel
   complement construction, which **duplicates mathlib's existing `complEDS`/`complEDS'`**. For
   mathlib the result must be (re)stated against — or bridged to — the upstream `complEDS` API; the
   abstract `IsEllSequence` engine and the `normEDS`-level corollary should land as a coherent pair,
   not by importing a second copy of `complEDS`.
2. **Redundant `mem` hypothesis.** The docstring itself says `mem : W m ∈ R⁰` "is actually
   redundant because `W` is a multiple of a normalised EDS by the other assumptions." The clean
   mathlib statement drops `mem` — which needs the structural result `IsDivSequence (normEDS …)` /
   the `W = W₁ • normEDS …` decomposition (`IsEllDivSequence.eq_normEDS`), i.e. the very TODO this
   feeds. So the de-`mem`'d form should land alongside that structural theorem.

Both are real, bounded pre-merge edits → `YES-but-generalise-first`, not `YES-add-as-is`.
(Contrast the sibling `normEDS_mul_complEDS` at line 1338, assessed `YES-add-as-is`: it is *already*
phrased in `normEDS`/`complEDS` terms and `mem`-free, so it lands cleanly. This lemma carries the
abstraction-layer and `mem` baggage that that one has already shed.)

---

## 5. Composition check (≤3 mathlib calls?)

No. The proof is an irreducible strong induction over the EDS recursion:
`Int.negInduction` → `Nat.strong_induction_on` → parity split, with the odd branch invoking the
defining elliptic relation `ellW (… ) (…) 1`, two independent recursive hypotheses, the abstraction
equations `h₁`/`h₂`, and a non-zero-divisor cancellation
(`mul_cancel_right_mem_nonZeroDivisors`) — ~23 lines. This lemma is the thing *other* results
compose from (it is what makes `normEDS_mul_complEDS` a one-liner); it is not itself a ≤3-call
composition of mathlib primitives. → rules out `NO-composable-from-mathlib`.

---

## 6. Axioms / soundness

Standard EDS recursion proof; no nonstandard axioms expected (`propext`, `Classical.choice`,
`Quot.sound` only). Local build is stale, so not re-checked here; this does not affect the verdict.

---

## 7. Five-bucket verdict

| Bucket | Applies? |
|---|---|
| YES-add-as-is | **No** — phrased over fork-local `compl`/`compl'` that duplicate mathlib's `complEDS`, and carries a redundant `mem` hypothesis. |
| **YES-but-generalise-first** | **Yes** — content fills a documented mathlib TODO and is Xu §6 (arXiv:2604.05280); already maximally general mathematically, but must be reconciled with upstream `complEDS` and shed `mem` before landing (ideally together with `IsDivSequence (normEDS …)` / `isEllDivSequence_normEDS`). |
| NO-mathlib-has-it | No — verified absent in pinned mathlib and in mathlib4-docs; only the `n = 2` doubling case exists. |
| NO-composable-from-mathlib | No — irreducible induction over the EDS relation, not a ≤3-call composition; it is the engine others compose from. |
| BORDERLINE-needs-human | No — the mathlib-wanted direction is unambiguous (named TODO + published paper that cites the module); only the packaging is a bounded edit, not a judgement requiring a human. |

**Final: `YES-but-generalise-first`.**

**Qualified name:** `IsEllSequence.mul_compl_eq_apply_mul_of_mem_nonZeroDivisors`

---

## Sources
- Junyan Xu, *On Elliptic Sequences over Commutative Rings*, arXiv:2604.05280 (2026), §6 (Thm 6.1/6.2).
- `Mathlib.NumberTheory.EllipticDivisibilitySequence` — pinned `09b373db` and
  https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/EllipticDivisibilitySequence.html
  (module docstring TODOs; `complEDS₂`/`complEDS'`/`complEDS` API; `normEDS_mul_complEDS₂`).
- *Elliptic divisibility sequence* — Wikipedia (Ward/Shipsey divisibility property background).
