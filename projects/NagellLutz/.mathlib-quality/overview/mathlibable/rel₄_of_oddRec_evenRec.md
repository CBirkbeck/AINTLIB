# Mathlibable assessment: `EllSequence.rel₄_of_oddRec_evenRec`

**Verdict: YES-add-as-is** (it is already in its mathlib-target form; see caveat — it should be
upstreamed as part of its coherent `EllSequence`/`rel₄` development, not in isolation).

- **Qualified name:** `EllSequence.rel₄_of_oddRec_evenRec`
- **Location:** `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:570`
- **Date:** 2026-06-18

---

## 1. The declaration

```lean
namespace EllSequence
variable {R : Type u} [CommRing R] (W : ℤ → R)
open scoped nonZeroDivisors
-- (within a section with hypotheses on W)
variable (neg : ∀ k, W (-k) = -W k) (zero : W 0 = 0)
  (one : W 1 ∈ R⁰) (two : W 2 ∈ R⁰)
  (oddRec : ∀ m ≥ 2, OddRec W m) (evenRec : ∀ m ≥ 3, EvenRec W m)

/-- The four-index `rel₄` relations follow from
the single-index `oddRec` and `evenRec` recursive relations. -/
theorem rel₄_of_oddRec_evenRec {a b c d : ℤ} (same : HaveSameParity₄ a b c d) :
    rel₄ W a b c d = 0
```

where (all in the same file, all NEW relative to mathlib):

- `addMulSub W m n := W ((m+n).tdiv 2) * W ((m-n).tdiv 2)` — the basic building block.
- `rel₄ W a b c d := addMulSub W a b * addMulSub W c d − addMulSub W a c * addMulSub W b d
   + addMulSub W a d * addMulSub W b c` — the **4-index, permutation-(anti)symmetric quartic
  elliptic relation** (the central object of the development; `relFin4_perm` proves the
  signed `S₄`-symmetry).
- `OddRec W m :  W(2m+1)·W(1)³ = W(m+2)·W(m)³ − W(m−1)·W(m+1)³`
- `EvenRec W m : W(2m)·W(2)·W(1)² = W(m)·(W(m−1)²·W(m+2) − W(m−2)·W(m+1)²)`
- `HaveSameParity₄ a b c d` — the four indices share a common parity (`negOnePow` equalities).

**Mathematical content.** From the *single-index* even/odd recurrences (`oddRec`, `evenRec`) and the
non-zero-divisor hypotheses `W 1, W 2 ∈ R⁰`, the *full* symmetric 4-index elliptic relation `rel₄`
holds for every same-parity quadruple. This is the engine theorem of the file: it is consumed
immediately by `IsEllSequence.of_oddRec_evenRec` (line 591), which specializes `d = 0` (`rel₃_iff₄`)
to conclude `IsEllSequence W` — i.e. *the even–odd recurrence implies the elliptic relation*.

**Proof shape (≈17 lines).** WLOG-reduce to nonnegative indices (`rel₄_abs`), sort them descending
into a strictly-decreasing tuple via `Tuple.sort`/`Fin.revPerm` using the signed permutation
invariance `relFin4_perm'`, dispatch the degenerate equal-adjacent cases via
`rel₄_same₀₁/₁₂/₂₃`, and finish with `rel₄_of_anti_oddRec_evenRec` (the strictly-antitone case,
itself a ~60-line strong induction at line 477). It depends on a long bespoke API; it is in no sense
a one-liner.

---

## 2. Literature search

- **Junyan Xu, "On Elliptic Sequences over Commutative Rings", arXiv:2604.05280 (April 2026).**
  This is the *companion paper* for exactly this development. It defines elliptic sequences over a
  commutative ring via "a 4-parameter, highly symmetric family of homogeneous quartic relations"
  (= `rel₄` / `relFin4` here), and proves "standard EDSs are elliptic … using intricate implications
  among elliptic relations, without relying on the complex-analytic theory of Weierstrass functions"
  (= the `oddRec`/`evenRec` ⟹ `rel₄` ⟹ `IsEllSequence` chain that this theorem anchors). The paper
  references the mathlib `NumberTheory.EllipticDivisibilitySequence` module and mathlib PRs.
- M. Ward, *Memoir on Elliptic Divisibility Sequences* — classical source cited in the file header;
  the even–odd recurrence and the non-zero-divisor conditions on the first terms are the standard
  formulation (cf. arXiv:2102.07573 "A recurrence relation for EDS", and Stange's
  *Formulary for elliptic divisibility sequences and elliptic nets*).
- K. Stange, *Elliptic nets and elliptic curves* (arXiv:0710.1316) — the `net` definition in the
  file (line 115) is the Stange elliptic-net relation; `net_eq_rel₄` relates it to `rel₄`.

Conclusion: the statement is **literature-standard mathematics**, in its most general (commutative
ring, minimal `R⁰` hypotheses) form, and is the formalized counterpart of a just-published paper.

## 3. Mathlib search (five methods)

Target file in mathlib: `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean`.

- **Bundled snapshot** (pin `d90090f647ca`, `.lake/packages/mathlib/…`, 547 lines): contains only the
  classic API — `IsEllSequence`, `IsDivSequence`, `IsEllDivSequence`, `preNormEDS('/)`, `normEDS`,
  `complEDS(₂/'/)`, the `map_*` lemmas. **No** `EllSequence` namespace, `addMulSub`, `rel₄`, `net`,
  `relFin4`, `HaveSameParity₄`, `OddRec`, `EvenRec`, `Rel₃`, or `rel₄_of_oddRec_evenRec`.
  (`grep` over the file returns nothing for any of these names.)
- **Live upstream docs** (leanprover-community.github.io/mathlib4_docs, fetched 2026-06-18): same —
  the module exposes only the `normEDS`-centric API; none of the `rel₄`/`OddRec`/`EvenRec`/`net`
  names exist. So this machinery is **not (yet) in mathlib**, neither in the pin nor at HEAD.
- name / loogle / leansearch / moogle: the symmetric `rel₄`-style relation and the
  "`oddRec`+`evenRec` ⟹ elliptic" implication do not appear under any mathlib name.

**This is a genuine gap in current mathlib**, being actively filled by the author (Junyan Xu) — the
file header attributes the original EDS file to David Kurniadi Angdinata, and this is a refactor/
extension of it.

## 4. Generality analysis

Already maximal:
- `R` an arbitrary `CommRing` (no field, domain, or characteristic assumption).
- `W : ℤ → R` abstract; hypotheses are exactly the minimal literature ones — odd (`neg`), `W 0 = 0`,
  the two single-index recurrences, and `W 1, W 2 ∈ R⁰` (non-zero-divisors, *not* units / not
  invertible — strictly weaker, and the correct generality per the paper and Ward).
- Conclusion is the strongest symmetric form (`rel₄`, all of `S₄` up to sign), of which the
  classical `Rel₃`/`IsEllSequence` is the `d = 0` specialization.

No mechanical weakening applies; "YES-but-generalise-first" is not warranted.

## 5. Composition check (≤3 mathlib calls?)

No. There is **no** mathlib primitive expressing `rel₄` or the even–odd recurrences, so it cannot be
assembled from a bounded number of existing mathlib lemmas. The proof rests on a purpose-built tower:
`rel₄_of_anti_oddRec_evenRec` (strong induction, ~60 lines), `relFin4_perm`/`relFin4_perm'`,
`rel₄_abs`, `rel₄_same₀₁/₁₂/₂₃`, `HaveSameParity₄.abs`/`.perm`, plus `Tuple.sort`. This is a multi-
hundred-line development, not a composition.

## 6. Verdict

**YES-add-as-is.** The theorem is literature-standard (it formalizes the central implication of
arXiv:2604.05280), stated at maximal generality over an arbitrary commutative ring with the minimal
non-zero-divisor hypotheses, is absent from current mathlib (pin and HEAD), and is not composable
from mathlib primitives. It is in exactly its mathlib-target form.

**Caveat / routing note.** It is not a free-standing lemma: it is one node of a single coherent
`EllSequence`/`rel₄` development authored by a core mathlib contributor with a companion paper, and
should be upstreamed **as that unit** (the whole `rel₄`/`net`/`OddRec`/`EvenRec` refactor of
`Mathlib.NumberTheory.EllipticDivisibilitySequence`), not cherry-picked. Within AINTLIB this is a
deliberate fork of that file; the right action is to track the upstream PR rather than re-derive.
Confidence the *theorem itself* belongs in mathlib: very high. The only reason it is not simply
"NO-mathlib-has-it" is that the upstreaming PR has not yet landed.

### Sources
- https://arxiv.org/abs/2604.05280 — Junyan Xu, *On Elliptic Sequences over Commutative Rings* (2026)
- https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/EllipticDivisibilitySequence.html
- https://arxiv.org/pdf/2102.07573 — *A recurrence relation for elliptic divisibility sequences*
- https://math.colorado.edu/~kstange/papers/edsformulary.pdf — Stange, EDS/elliptic-net formulary
- https://arxiv.org/abs/0710.1316 — Stange, *Elliptic nets and elliptic curves*
