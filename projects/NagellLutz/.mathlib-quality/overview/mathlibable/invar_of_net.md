# Mathlibable assessment: `EllSequence.invar_of_net`

**Verdict: YES-but-generalise-first**

- **Qualified name:** `EllSequence.invar_of_net`
- **Location:** `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:149`
- **Date:** 2026-06-18
- **One-line summary:** a genuine (mathlib-absent) algebraic lemma of the project's `EllSequence`
  elliptic-relation layer — if every Stange `net` value of `W` vanishes, the invariant
  numerator/denominator cross-products `invarNum s m · invarDenom s n = invarNum s n · invarDenom s m`
  agree — destined for mathlib, but only **as part of upstreaming that whole layer** (which closes the
  standing `normEDS satisfies IsEllDivSequence` TODO), not as a stand-alone declaration; currently
  triplicated inside AINTLIB.

## Statement (verified from source)

```lean
namespace EllSequence
variable {R : Type u} [CommRing R] (W : ℤ → R)

/-- The numerator of an invariant of an elliptic sequence, such that for each `s`,
`invarNum s n / invarDenom s n` is a constant independent of `n`. -/
def invarNum (s n : ℤ) : R :=
  (W (n + 2 * s) * W (n - s) ^ 2 + W (n + s) ^ 2 * W (n - 2 * s)) * W s ^ 2
    + W n ^ 3 * W (2 * s) ^ 2

/-- The denominator of an invariant of an elliptic sequence. -/
def invarDenom (s n : ℤ) : R := W (n + s) * W n * W (n - s)

set_option allowUnsafeReducibility true in
attribute [local reducible] Nat.rawCast Mathlib.Meta.NormNum.instAddMonoidWithOne in
theorem invar_of_net (net_eq_zero : ∀ p q r s, net W p q r s = 0) (s m n : ℤ) :
    invarNum W s m * invarDenom W s n = invarNum W s n * invarDenom W s m := by
  simp_rw [invarNum, invarDenom]
  linear_combination (norm := (simp_rw [net]; ring_nf))
    net_eq_zero m n s 0 * W m * W n * W (2 * s) ^ 2
      - (net_eq_zero m n s s * W (m - s) * W (n - s)
        + net_eq_zero (m - s) (n - s) s s * W (m + s) * W (n + s)
        - net_eq_zero (n + s) n (n - s) (m - n) * W (m - n) * W (2 * s)) * W s ^ 2
```

The parsed qualified name in the prompt (`EllSequence.invar_of_net`) is **correct**: the decl sits
inside `namespace EllSequence` (opened line 90, closed line 597) and is a `theorem`. `net` is the
project's Stange elliptic-net expression (line 115):
`net W p q r s = W(p+q+s)·W(p−q)·W(r+s)·W r − W(p+r+s)·W(p−r)·W(q+s)·W q + W(q+r+s)·W(q−r)·W(p+s)·W p`.

Context — what it is for:
- It is the bridge from the **net relation** to the **invariant**: under the hypothesis that *all*
  net values vanish (i.e. `W` is an elliptic net), the quantity `invarNum s n / invarDenom s n` is
  independent of `n`, here expressed cross-multiplied to stay in a `CommRing`. The content is a single
  polynomial identity, discharged by one `linear_combination` over **six** explicit `net_eq_zero`
  instances with `W`-monomial coefficients (normalised by `simp_rw [net]; ring_nf`).
- Downstream in the project it has exactly two consumers, both thin specialisations of this lemma:
  - `EllSequence.IsEllSequence.invar` (line 699): `IsEllSequence W → invarNum/Denom` cross-equality,
    via `invar_of_net _ (ell.net one two) _ _ _`;
  - `invar_normEDS` (line 1473): the `normEDS` version `invar_of_net _ net_normEDS _ _ _`, which in
    turn underlies `invar₂_normEDS` and the elliptic-curve "invariant" used in the
    division-polynomial / Nagell–Lutz development (`WeierstrassCurve.invar`,
    `DivisionPolynomialOmega.lean`).
- The local `set_option allowUnsafeReducibility true` + `attribute [local reducible] Nat.rawCast …`
  prelude is a `ring_nf`/`norm_num`-performance device for the big `linear_combination`, not
  mathematical content (the same prelude recurs on the other heavy `ring`-driven lemmas in the file).

## 1. Literature search

- The **net relation** itself is canonical: Stange, *Elliptic nets and elliptic curves*
  (arXiv:0710.1316), defines an elliptic net by exactly the four-index recurrence
  `W(p+q+s)W(p−q)W(r+s)W(r) + W(q+r+s)W(q−r)W(p+s)W(p) + W(r+p+s)W(r−p)W(q+s)W(q) = 0`
  — the project's `net` (signs/order adjusted, per its docstring, to make the `rel₄` equivalence
  unconditional and char-3-safe). So the *hypothesis* `∀ p q r s, net W p q r s = 0` is the standard
  "`W` is an elliptic net" condition.
- The **invariant** `invarNum/invarDenom` (the ratio `W(n+s)W(n)W(n−s)` denominator with the displayed
  numerator) is the formalisation's packaging of the classical fact that an elliptic net carries a
  ratio independent of the moving index — the kind of "invariant of the sequence" appearing in
  Ward's *Memoir* and the Stange EDS/elliptic-net **formulary**
  (math.colorado.edu/~kstange/papers/edsformulary.pdf). Web search (Stange arXiv:0710.1316; EDS
  formulary; Wikipedia *Elliptic divisibility sequence*; *On Symmetries of Elliptic Nets*
  arXiv:1408.6623) confirms the relation algebra is textbook, but turns up **no separately-named
  theorem** matching this exact cross-product identity: `invar_of_net` is the Lean lemma that *derives*
  the invariant from the net relation, i.e. a step in the standard development, not a quotable named
  result. The companion paper is Angdinata–Xu, *On Elliptic Sequences over Commutative Rings*
  (arXiv:2604.05280) — the work behind precisely this Lean layer.
- Background sweep (EDS area): Ward, *Memoir on Elliptic Divisibility Sequences* (the file's cited
  reference); Shipsey/Swart EDS theses; *EDS, Squares and Cubes* (arXiv:1101.3839). None isolate this
  cross-product identity under its own name.

**Takeaway:** the *content* that belongs in mathlib is the elliptic-relation layer (`net`/`rel₄`, the
invariant, and "`normEDS` is elliptic"), which is canonical; `invar_of_net` is one genuine lemma
inside it (the net→invariant step), not an independently citable theorem.

## 2. Mathlib search (five methods) — forked files checked first

Per project context, NagellLutz **forks** `Mathlib.NumberTheory.EllipticDivisibilitySequence` and
`Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.*`, so the first question is whether this
theorem is already upstream. It is not.

- **grep** `invar_of_net` / `invarNum` / `invarDenom` / `def net ` / `rel₄` / `EllSequence` over the
  pinned mathlib checkout (`.lake/packages/mathlib/Mathlib/**`, source tree) → **zero hits** for all of
  these. The forked file `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean` (547 lines) defines
  `IsEllSequence` directly as a flat `Prop`
  (`∀ m n r, W(m+n)·W(m−n)·W r² = W(m+r)·W(m−r)·W n² − W(n+r)·W(n−r)·W m²`, line 82) and ends at the
  `normEDS`/`complEDS`/`*Rec`/`map_*` machinery; it has **no `EllSequence` namespace** and **none** of
  `addMulSub`, `rel₄`, `net`, `Rel₃`, `invarNum`, `invarDenom`, `invar_of_net`. The entire
  elliptic-relation extension (project file is 1667 lines) is **new, not yet upstream**.
- **Live mathlib4 docs**, fetched 2026-06-18
  (`leanprover-community.github.io/mathlib4_docs/.../EllipticDivisibilitySequence.html`): confirms none
  of `invar_of_net` / `invarNum` / `invarDenom` / `EllSequence` / `net` / `rel₄` / `addMulSub` appear,
  and that the file still carries the two open TODOs:
  > * TODO: prove that `normEDS` satisfies `IsEllDivSequence`.
  > * TODO: prove that a normalised sequence satisfying `IsEllDivSequence` can be given by `normEDS`.
  The `EllSequence` layer this theorem belongs to is precisely the in-flight work to discharge TODO #1
  (`invar_of_net` → `invar_normEDS` feeds the division-polynomial invariant used along the way).
- **loogle / leansearch** (mathlib index): consistent — no decl of this name, and nothing of this shape
  (a cross-product equality of two cubic-in-`W` "numerator"/`W(n±s)W(n)`-"denominator" expressions
  under a net-vanishing hypothesis) upstream.
- **Name/def search** for the body (a `linear_combination`-provable identity in `W`-monomials over the
  net relation): nothing analogous in mathlib; the `net`/elliptic-net vocabulary is absent entirely.
- **Within AINTLIB** (not mathlib): `invar_of_net` is **triplicated** — here (line 149), the project's
  own `EllipticDivisibilitySequenceOriginal.lean:146`, and
  `HasseWeil/Auxiliary/EllipticDivisibilitySequence.lean:91` (verbatim, same statement and proof). The
  `05-duplications.md` analysis flags this file as a deliberate fork of the mathlib EDS file kept
  *only* to host the project-original `addMulSub`/`rel₄`/`net`/invar API "that mathlib lacks." That is
  intra-repo forking/dedup (a `/cleanup` concern), **not** evidence of a mathlib home.

**Conclusion:** neither `invar_of_net` nor its surrounding `EllSequence` layer is in mathlib today.

## 3. Generality analysis

- Already **maximally general** for what it is: arbitrary `CommRing R`, arbitrary sequence
  `W : ℤ → R`, arbitrary integer parameters `s, m, n`, and the *weakest sensible* hypothesis (only the
  bare net-vanishing `∀ p q r s, net W p q r s = 0`, no `W 0 = 0`/oddness/non-zero-divisor
  assumptions — those are added only by downstream specialisations). There is no obvious
  assumption-weakening: it is stated cross-multiplied precisely to avoid needing a field or
  cancellation, and the four `net_eq_zero` index-patterns are pinned to the proof. So there is nothing
  to *generalise* in the assumption-weakening sense.
- The "generalise-first" verdict here is in the **packaging** sense used by the sibling reports
  (cf. `addMulSub.md`): the correct *unit* to upstream is not this lone lemma but the
  elliptic-relation development it belongs to (`net`/`rel₄`, `invarNum`/`invarDenom`, `invar_of_net`,
  `IsEllSequence.invar`, …, → `normEDS` is `IsEllSequence`/`IsEllDivSequence`). As an isolated public
  mathlib declaration `invar_of_net` is the wrong granularity — it is meaningless without the `net`
  definition it quantifies over and the `invarNum/invarDenom` defs it relates, all of which must land
  in the same PR.

## 4. Composition check (≤3 mathlib calls)

- **Cannot** be obtained from existing mathlib in ≤3 calls. mathlib has **no `net`**, **no
  `invarNum`/`invarDenom`**, and no elliptic-net relation API at all, so there is nothing to compose
  against: even *stating* `invar_of_net` requires first adding the three project definitions. The proof
  is a genuine (if mechanical) polynomial identity — a single `linear_combination` over six specific
  `net_eq_zero` instances with hand-chosen `W`-monomial coefficients; it is not a one- or two-step
  consequence of any current mathlib lemma. So this is **not** a `NO-composable-from-mathlib` case.
- (It is of course "provable by `linear_combination`+`ring` once the defs exist" — but that is true of
  essentially every algebraic-identity lemma in the layer; the substantive object, the elliptic-net
  relation algebra, is the thing missing from mathlib.)

## 5. Five-bucket verdict

**YES-but-generalise-first.**

- Not **NO-mathlib-has-it**: grep + live mathlib4 docs (2026-06-18) confirm no `invar_of_net`,
  `invarNum`, `invarDenom`, `net`, `rel₄`, or `EllSequence` namespace upstream; the file still defines
  `IsEllSequence` as a flat `Prop` and carries the open `normEDS`-is-elliptic TODO this layer closes.
- Not **NO-composable-from-mathlib**: mathlib lacks the `net`/invariant vocabulary entirely, so the
  statement is not even expressible from current primitives, let alone re-derivable in ≤3 calls.
- Not **YES-add-as-is**: shipping this lemma as a stand-alone public mathlib declaration is the wrong
  unit — it depends on `net`, `invarNum`, `invarDenom` (all project-new) and is only useful as the
  net→invariant step feeding `IsEllSequence.invar` / `invar_normEDS`; and it is currently triplicated
  inside AINTLIB (a dedup chore), not a polished standalone API.
- Not **BORDERLINE**: the path is clear — it rides along with the elliptic-relation upstreaming.

**What to upstream (the right unit):** the **`EllSequence` elliptic-relation layer** of
`EllipticDivisibilitySequence.lean` — `addMulSub` (internal helper), the sign/parity lemmas, `rel₄`,
`net`/`net_eq_rel₄`, `Rel₃`, the nine-term expansion `addMulSub_sq_mul_rel₄_eq₉`, **and the invariant
sub-bundle `invarNum`/`invarDenom`/`invar_of_net`/`IsEllSequence.invar`** — culminating in
**"`normEDS` is an `IsEllSequence`" / `IsEllDivSequence`**, which closes the standing mathlib TODO in
`Mathlib/NumberTheory/EllipticDivisibilitySequence.lean`. `invar_of_net` belongs in mathlib **inside
that PR, as the net→invariant lemma**, not as an independent declaration assessed on its own.

## Notes / cross-refs

- Mathlib upstream EDS file: `.lake/packages/mathlib/Mathlib/NumberTheory/EllipticDivisibilitySequence.lean`
  (547 lines; flat `IsEllSequence` `Prop`, no `EllSequence` layer, no invariant). Project extension:
  `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean` (1667 lines).
- Intra-AINTLIB duplicates of this theorem (dedup, not mathlibability):
  `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequenceOriginal.lean:146`,
  `projects/HasseWeil/HasseWeil/Auxiliary/EllipticDivisibilitySequence.lean:91`.
- Downstream consumers (both thin specialisations): `EllSequence.IsEllSequence.invar` (line 699),
  `invar_normEDS` (line 1473) → `invar₂_normEDS` → elliptic-curve `WeierstrassCurve.invar`.
- Consistent with the sibling assessments `addMulSub.md` / `isEllSequence_ψ.md` (same directory): the
  in-flight `normEDS`-is-elliptic work is the real mathlibable payload; the layer's component pieces
  (this lemma, `addMulSub`, …) inherit a "generalise/repackage first" verdict pointing at that larger
  unit.

## Sources

- Stange, *Elliptic nets and elliptic curves* — https://arxiv.org/abs/0710.1316
- Stange, EDS / elliptic-net formulary — https://math.colorado.edu/~kstange/papers/edsformulary.pdf
- *On Symmetries of Elliptic Nets and Valuations of Net Polynomials* — https://arxiv.org/pdf/1408.6623
- Angdinata–Xu, *On Elliptic Sequences over Commutative Rings* — https://arxiv.org/pdf/2604.05280
- Mathlib4 docs, `Mathlib.NumberTheory.EllipticDivisibilitySequence` (flat `IsEllSequence`; open
  TODOs; no `EllSequence` layer / `net` / invariant), fetched 2026-06-18 —
  https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/EllipticDivisibilitySequence.html
- *Elliptic divisibility sequence* (four-index recurrence) — https://en.wikipedia.org/wiki/Elliptic_divisibility_sequence
