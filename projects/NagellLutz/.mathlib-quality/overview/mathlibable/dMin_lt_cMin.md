# Mathlibable assessment — `EllSequence.dMin_lt_cMin`

**Verdict: `NO-composable-from-mathlib`**

> A trivial private helper (`dMin a < dMin a + 2`) discharged by one core mathlib lemma; it belongs next to its defs, not in mathlib.

---

## 1. The declaration

- **File**: `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:388`
- **Qualified name** (verified): `EllSequence.dMin_lt_cMin`
  - Line 388 lies inside `namespace EllSequence` (opened line 90, closed line 597); no intervening
    namespace is open at 388. So the prompt's guessed `EllSequence.dMin_lt_cMin` is **correct**.

```lean
/-- The minimal possible fourth index in the four-index elliptic relation given the first index. -/
def dMin (a : ℤ) : ℤ := if Even a then 0 else 1
/-- The minimal possible third index in the four-index elliptic relation given the first index. -/
def cMin (a : ℤ) : ℤ := dMin a + 2

lemma dMin_lt_cMin (a : ℤ) : dMin a < cMin a := lt_add_of_pos_right _ zero_lt_two
```

Unfolding `cMin`, the statement is **`dMin a < dMin a + 2`** for `dMin a : ℤ`. The proof is a single
application of the core mathlib lemma `lt_add_of_pos_right` (with `zero_lt_two`).

### Mathematical role
`dMin`/`cMin` are *bookkeeping definitions* internal to this file's formalised proof of the
four-index elliptic relation `rel₄`. `dMin a` is the smallest nonnegative index of the same parity
as `a` (0 if `a` even, 1 if odd); `cMin a := dMin a + 2` is the next index of that parity. The
lemma records the obvious fact that the third minimal index strictly exceeds the fourth — used
downstream (`Rel₄OfValid`, `rel₄_fix₁_of_fix₂`, `dMin_le`, parity lemmas) as a side condition in the
strictly-decreasing-quadruple induction. It is **not** a named object in the EDS literature; it is
scaffolding for the Lean induction.

## 2. Literature search

- WebSearch on "elliptic divisibility sequence four-index elliptic relation minimal index parity
  recurrence formalization": the EDS four-index relation
  `h_{m+n} h_{m-n} h_r² = h_{m+r} h_{m-r} h_n² − h_{n+r} h_{n-r} h_m²` (Ward; Shipsey; cf.
  arXiv:2102.07573, Wikipedia "Elliptic divisibility sequence") is the mathematical content this
  file is heading toward. **No source names a "minimal index of given parity" object** — `dMin`/
  `cMin` are an implementation choice for organising the formal induction, with no standard symbol
  or stated inequality to match.
- WebSearch on `lt_add_of_pos_right` "a < a + b": confirms this is the standard mathlib
  ordered-additive-monoid lemma (`a < a + b` from `0 < b`); `Nat.lt_add_of_pos_right` is the ℕ
  instance. The general lemma lives under `Mathlib/Algebra/Order/Monoid/...`.

Conclusion: the literature offers no general form to target; the lemma is intrinsically tied to
project-local defs.

## 3. Mathlib search (is it there, or a more general form?)

Five-method check:

1. **Exact statement** — the proposition `dMin a < cMin a` mentions `EllSequence.dMin` and
   `EllSequence.cMin`, which are **defined only in this project**. `grep` for `dMin`/`cMin` in
   `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean` → **0 occurrences**. The mathlib EDS
   file is about `preNormEDS`/`normEDS`; it has no `EllSequence` namespace, no `dMin`/`cMin`, no
   `rel₄`. So the *exact* statement cannot exist in mathlib.
2. **Generalised form** — strip the defs and the statement is `x < x + 2` over `ℤ`, i.e. exactly
   `lt_add_of_pos_right (x := dMin a) (b := 2)` together with `zero_lt_two`. The general lemma
   **`lt_add_of_pos_right : 0 < b → a < a + b`** is already in mathlib
   (`Mathlib/Algebra/Order/Monoid/Unbundled/Basic.lean`) — and is literally what the proof calls.
3. **Fork check (project context)** — AINTLIB forks `Mathlib.NumberTheory.EllipticDivisibilitySequence`
   and `Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.*`. Inspected the cached mathlib
   copies: neither contains `dMin`/`cMin`/`dMin_lt_cMin`. The only repo hits for `dMin_lt_cMin` are
   **three project files** (`NagellLutz/.../EllipticDivisibilitySequence.lean`,
   `NagellLutz/.../EllipticDivisibilitySequenceOriginal.lean`,
   `HasseWeil/.../Auxiliary/EllipticDivisibilitySequence.lean`) — i.e. AINTLIB's own duplicated
   General*/aux tracks, **not** mathlib. So this decl is *not already in mathlib*.
4. **Loogle/leansearch (mathlib index)** — `dMin`/`cMin` are not mathlib identifiers, so an
   identifier query is vacuous; the shape query `?a < ?a + ?b` resolves to `lt_add_of_pos_right`
   (and `Nat`/`order` siblings), all already present. Nothing EDS-specific to find.
5. **Naming convention** — there is no mathlib decl named `*dMin*`/`*cMin*`; the names are
   project-internal.

## 4. Generality analysis

The statement is maximally *specific*, not general: it is pinned to two `ℤ`-valued helper defs
(`dMin`, `cMin`) that exist only to drive this file's induction. The genuinely general fact
(`a < a + b` when `0 < b`, over any `CovariantClass`/ordered additive monoid) is **already** the
mathlib lemma the proof invokes. There is nothing to generalise *into* mathlib here: the only
general kernel is `lt_add_of_pos_right`, which mathlib owns.

## 5. Composition check (≤ 3 mathlib calls)

Yes — and the source proof *is* the composition:

```lean
dMin a < cMin a
  ⇐  (defeq cMin a = dMin a + 2)
  ⇐  lt_add_of_pos_right _ zero_lt_two   -- one mathlib lemma + zero_lt_two
```

A single `lt_add_of_pos_right` (plus the standard numeral fact `zero_lt_two`) discharges it after
`cMin` unfolds definitionally. This is a **1-call** consequence of an existing mathlib primitive.

## 6. Five-bucket verdict

| Bucket | Fit |
|---|---|
| YES-add-as-is | No — references project-only defs; trivial. |
| YES-but-generalise-first | No — the general form (`lt_add_of_pos_right`) is already in mathlib. |
| NO-mathlib-has-it | No — `dMin`/`cMin` are not in mathlib, so *this exact lemma* is not there. |
| **NO-composable-from-mathlib** | **Yes** — `dMin a < dMin a + 2`, one `lt_add_of_pos_right` call; trivially recoverable, belongs with its defs. |
| BORDERLINE-needs-human | No — assessment is clear-cut. |

**Final: `NO-composable-from-mathlib`.**

`dMin`/`cMin` themselves are local proof scaffolding with no literature standing, so neither they
nor this one-line inequality about them should migrate to mathlib. Should the surrounding
four-index `rel₄` development ever be upstreamed, `dMin_lt_cMin` would travel *with* `dMin`/`cMin`
as a private helper — its proof stays `lt_add_of_pos_right _ zero_lt_two`, needing nothing new from
mathlib.

---

### Sources
- arXiv:2102.07573 — *A recurrence relation for elliptic divisibility sequences* — https://arxiv.org/abs/2102.07573
- *Elliptic divisibility sequence* (Wikipedia) — https://en.wikipedia.org/wiki/Elliptic_divisibility_sequence
- mathlib4 `Mathlib.Algebra.Order.Monoid.*` (`lt_add_of_pos_right`) — https://leanprover-community.github.io/mathlib4_docs/
