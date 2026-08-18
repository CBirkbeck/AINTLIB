# Mathlibable assessment — `rel₄_normEDS`

**Verdict: BORDERLINE-needs-human**

- **Qualified name:** `rel₄_normEDS` (root namespace — no enclosing `namespace`)
- **Source:** `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:1473`
- **Date:** 2026-06-21 (revises the 2026-06-18 pass; same verdict, refined evidence)

## 1. The declaration

```lean
omit ellW ellU in
lemma rel₄_normEDS (p q r s : ℤ) (same : HaveSameParity₄ p q r s) :
    rel₄ (normEDS b c d) p q r s = 0 := by
  rw [same.rel₄_eq_net, net_normEDS]
```

Context: `variable {R : Type u} [CommRing R] (b c d : R)`. So the statement is over an **arbitrary
commutative ring** `R`, with integer indices `p q r s` and a same-parity hypothesis.

### Qualified-name verification
The file opens `namespace EllSequence` at L90 but closes it at L597 (`end EllSequence`), then does
`open EllSequence` at L599. All intermediate namespaces (`EllSequence` L1079–1112, L1356–1431;
`HaveSameParity₄` L216–297; `IsEllSequence` L643–702) are balanced and closed before L1473. Line
1473 sits inside `section NormEDS` (L881) with **no active namespace**. Hence the true qualified
name is the bare `rel₄_normEDS` — the parsed name is correct. (Note: the overview index pointed at
L1468; the lemma's actual signature line is **1473** — `net_normEDS` is at L1465.)

### What it says, mathematically
`rel₄ W a b c d := addMulSub W a b * addMulSub W c d − addMulSub W a c * addMulSub W b d
+ addMulSub W a d * addMulSub W b c`, where `addMulSub W m n = W((m+n)/2)·W((m−n)/2)`. This is the
**symmetric three-pairing form of Ward's elliptic relation**
`W(m+n)W(m−n)W(r)² + W(r+m)W(r−m)W(n)² + W(n+r)W(n−r)W(m)² = 0` (the literature's standard
symmetric EDS recurrence), written so that **all four indices** permute freely. `HaveSameParity₄`
asserts the four indices share a parity (`negOnePow` equal pairwise).

So `rel₄_normEDS` is: *the canonical normalised EDS `normEDS b c d` satisfies the symmetric
four-index elliptic relation for any four same-parity integer indices.* This is a same-parity
repackaging of the parity-free `net_normEDS`.

### Proof / dependency depth
One-line proof `rw [same.rel₄_eq_net, net_normEDS]`, but both rewrites are project-local and rest on
a deep development:
- `HaveSameParity₄.rel₄_eq_net` (L222) — rewrites the symmetric `rel₄` as Stange's `net` (which
  needs no parity hypothesis).
- `net_normEDS` (L1465) — the net of `normEDS` vanishes; proved via the universal MvPolynomial EDS
  (`universalNormEDS`, L1186) and `IsEllSequence.normEDS.net`, which in turn comes from
  `IsEllSequence.net` (L694) → `IsEllSequence.rel₄` (L690) → `rel₄_of_oddRec_evenRec` (L570) — a
  multi-hundred-line argument (`rel₄_of_min₂`, `rel₄_of_anti_oddRec_evenRec`, `rel₄_transf`, the
  `transf`/`avg₄` machinery).

## 2. Literature search

- **Ward, *Memoir on Elliptic Divisibility Sequences*** (the file's cited reference): defines EDS by
  the elliptic recurrence; the symmetric three-pairing identity is the standard equivalent form.
- **K. Stange, *Elliptic nets and elliptic curves* (arXiv:0710.1316)**: the `net` relation here is
  Stange's elliptic-net relation (rank-1 case = EDS); the file's `net` docstring explicitly says it
  is "the defining property of Stange's elliptic nets" (signs/order tweaked to make symmetry
  unconditional and avoid char-3 issues).
- **On Elliptic Sequences over Commutative Rings (arXiv:2604.05280)**: EDS over a general
  `CommRing`; acknowledges D. K. Angdinata (this file's author) for the division-polynomial
  motivation — this is the `[CommRing R]` generality used here.
- Wikipedia *Elliptic divisibility sequence* gives the symmetric form
  `W_{n+m}W_{n−m}W_r² + W_{m+r}W_{m−r}W_n² + W_{r+n}W_{r−n}W_m² = 0`.

Conclusion: the objects (`rel₄` = symmetric Ward relation, `net` = Stange net) and the claim
(`normEDS` satisfies them) are **textbook-standard EDS theory**. Nothing exotic.

## 3. Mathlib search (five methods)

Searched the pinned mathlib copy (`09b373db6e247a35cfa5e44578c09a20e7c97271`) under
`.lake/packages/mathlib/Mathlib/` (grep, leansearch, loogle, file read, dep scan):

| Object | In mathlib? |
|---|---|
| `normEDS`, `preNormEDS`, `complEDS₂`, `normEDS_*` lemmas | **Yes** — `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean` |
| `rel₄` (symmetric 4-index relation) | **No** (grep over whole tree: 0 hits) |
| `net` (Stange net relation) | **No** |
| `HaveSameParity₄`, `addMulSub` | **No** |
| `net_normEDS` / `rel₄_normEDS` | **No** |
| `IsEllSequence (normEDS …)` / `IsEllDivSequence (normEDS …)` | **No** — it is an explicit **TODO** |

Decisive evidence — the mathlib EDS file (547 lines, ends at the `Map` section) header (L44–45)
still lists as open TODOs:
> `* TODO: prove that normEDS satisfies IsEllDivSequence.`
> `* TODO: prove that a normalised sequence satisfying IsEllDivSequence can be given by normEDS.`

`Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/` defines `ψ` via `normEDS` and
re-exports `normEDS_*`, but has **no** four-index relation, no `net`, no `rel₄`. So mathlib currently
has the *definition* of the normalised EDS but **not the proof that it is elliptic** — and
`rel₄_normEDS` is a (specialized, same-parity) lemma inside that missing proof.

**This decl is NOT in mathlib, and no more-general form is in mathlib.** This file is an extended
*fork* of the upstream mathlib EDS file (same author, same Copyright header, superset module doc)
being developed toward closing that TODO. (It is also duplicated *within this repo* —
`projects/HasseWeil/HasseWeil/Auxiliary/EllipticDivisibilitySequence.lean` has a near-identical fork
with `rel₄`, `net`, `HaveSameParity₄`, `net_normEDS` — but that fork stops at `net_normEDS` and has
**no** `rel₄_normEDS`. So even the in-repo twin doesn't expose this exact lemma; it is specific to
NagellLutz.)

## 4. Generality analysis

Already maximal:
- Base ring is an arbitrary `CommRing R` — `normEDS` is defined for any commutative ring and the
  relation is a polynomial identity, so there is no weaker typeclass to drop to.
- The `same : HaveSameParity₄ p q r s` hypothesis is **necessary**: the *symmetric* `rel₄` (all four
  indices permutable) only vanishes for same-parity indices. The parity-free statement is exactly
  `net_normEDS` (already a separate lemma, L1465). So `rel₄_normEDS` is the same-parity packaging of
  `net_normEDS`; the hypothesis cannot be removed without changing the object.

Nothing to weaken. There is no "more general literature form" — this already is the general form.
Hence this is **not** YES-but-generalise (generalisation is not the blocker).

## 5. Composition check (≤3 calls)

Two readings, both pointing away from a clean YES-add-as-is:

- **From *current* mathlib:** **No** — mathlib supplies none of the building blocks (`rel₄`, `net`,
  `HaveSameParity₄`, `net_normEDS`, the entire `IsEllSequence.normEDS` chain are absent). You cannot
  reconstruct this from today's mathlib primitives in any number of steps; the prerequisite
  "`normEDS` is elliptic" does not yet exist upstream. This is why the bucket is not the clean
  `NO-composable-from-mathlib`.
- **From its own siblings (once they upstream):** **Yes, trivially** — the proof is literally
  `net_normEDS` ∘ `rel₄_eq_net`, and the same conclusion is available directly as
  `IsEllSequence.normEDS.rel₄ one two same` (general `IsEllSequence.rel₄` at L690, specialized to
  `normEDS`). So *relative to the development it belongs to*, `rel₄_normEDS` is a ≤2-call corollary.

## 6. Usage / role evidence (new this pass)

Repo-wide consumer scan:
- `grep "rel₄_normEDS"` across all `*.lean` → **only its own definition line. Zero downstream
  consumers** anywhere in the repo.
- By contrast `net_normEDS` IS consumed: `HasseWeil/.../DivisionPolynomial.lean:219`,
  `NagellLutz/.../ZSMul.lean:140` (both `rw [ψᵤ_eq_normEDS]; apply net_normEDS`), and
  `invar_normEDS` (L1481). The codebase uses the **`net` form** on `normEDS`, never the `rel₄` form.

So as it stands `rel₄_normEDS` is an **unused, same-parity restatement** of the load-bearing
`net_normEDS`. The genuine, upstream-worthy content is the *development around it*:
`IsEllSequence.normEDS` (L1211 — closes the TODO), the **general** `IsEllSequence.net` /
`IsEllSequence.rel₄` (L694 / L690), `net_normEDS` (L1465), and the `IsEllDivSequence (normEDS …)`
packaging (`IsEllDivSequence.normEDS`, L1444).

## 7. Verdict — BORDERLINE-needs-human

The **mathematics is mathlib-worthy** (standard, absent upstream, maximally general, closes a
documented TODO). But `rel₄_normEDS` **as an isolated declaration** is the wrong granularity to port,
and the resolution is a human design/dedup call rather than a mechanical one:

1. **It is an internal, currently-unused wrapper, not the natural API.** `normEDS`'s ellipticity is
   far more naturally exposed in mathlib as `IsEllSequence (normEDS b c d)` /
   `IsEllDivSequence (normEDS b c d)` — the literal TODO targets, which this file proves (L1211,
   L1444). `rel₄_normEDS` is a same-parity restatement of `net_normEDS` with no consumers; in a
   mathlib PR it would, at most, ride along as a private/supporting lemma — likely it would simply
   not be added (callers use `net_normEDS` or `IsEllSequence.rel₄` directly).

2. **The supporting vocabulary is project-specific design.** `rel₄` (symmetric 4-index) and
   `HaveSameParity₄` were deliberately introduced *instead of* the 3-index `net`/`Rel₃` precisely to
   make permutation symmetry unconditional and dodge char-3 peculiarities (per the docstrings). Which
   of `rel₄` vs `net` vs the `IsEllSequence` predicate becomes the mathlib-facing API is a design
   decision that determines whether `rel₄_normEDS` survives as a named lemma at all.

3. **In-repo duplication must be resolved first.** NagellLutz and HasseWeil carry two near-identical
   forks of this entire file. Upstreaming should consolidate them (and reconcile with mathlib's
   existing `DivisionPolynomial` API) before fixing the exact lemma set — exactly the cross-project
   call flagged in the project context.

Why not the neighbouring buckets:
- **not NO-mathlib-has-it** — mathlib lacks it and every prerequisite.
- **not NO-composable-from-mathlib** — *current* mathlib has none of the primitives, so it is not
  composable from existing mathlib (the composition is from this project's own not-yet-upstreamed
  siblings). The "trivially composable" property only holds *internally*, which is an argument about
  packaging, not about mathlib already covering it.
- **not YES-add-as-is** — wrong granularity, unused, fork-duplicated; the natural public object is
  the `IsEllSequence`/`IsEllDivSequence` interface, not this lemma.
- **not YES-but-generalise** — already maximally general.

The blocker is a **human packaging/interface/dedup decision** about how the "`normEDS` is an EDS"
development enters mathlib and whether this specific lemma is on its public surface.

### Recommendation to the human
Upstream the **development as a unit** (close the `IsEllDivSequence (normEDS …)` TODO), choosing the
public API — almost certainly `IsEllSequence (normEDS b c d)` / `IsEllDivSequence (normEDS b c d)`,
plus `net_normEDS` (which downstream code actually uses). Decide there whether
`rel₄`/`net`/`HaveSameParity₄` and `rel₄_normEDS` are exposed or kept private; given it has zero
consumers, `rel₄_normEDS` is the most likely to be dropped or made private. First consolidate the
NagellLutz + HasseWeil forks and reconcile with `AlgebraicGeometry/EllipticCurve/DivisionPolynomial`.

## Sources
- Ward, *Memoir on Elliptic Divisibility Sequences* (file's cited reference).
- K. Stange, *Elliptic nets and elliptic curves*, arXiv:0710.1316.
- *On Elliptic Sequences over Commutative Rings*, arXiv:2604.05280.
- *Elliptic divisibility sequence*, Wikipedia (symmetric three-pairing recurrence).
- `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean` (TODO lines 44–45; `normEDS` def).
- `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/` (`ψ` via `normEDS`).
- `projects/HasseWeil/HasseWeil/Auxiliary/EllipticDivisibilitySequence.lean` (in-repo twin fork).
