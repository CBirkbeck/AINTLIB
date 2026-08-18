# /mathlibable report — `IsEllSequence.invar`

## Verdict: YES-but-generalise-first

One-line: not in mathlib (this apparatus closes the standing `normEDS satisfies IsEllDivSequence`
TODO); upstream the general `invar_of_net` + `net`/`invarNum`/`invarDenom` bundle, not this lone
specialized wrapper.

> NB on naming/disambiguation: this report is for the **`invarNum`/`invarDenom`** lemma at
> `EllipticDivisibilitySequence.lean:699`, inside `namespace IsEllSequence`. Its true qualified name
> is **`IsEllSequence.invar`** (verified below). It is a *different declaration* from
> `WeierstrassCurve.invar` (the polynomial `6X²+b₂X+b₄` in `DivisionPolynomialOmega.lean:48`), which
> is covered by the sibling `invar.md`. The two are unrelated; this file is written under the
> disambiguated name so it does not clobber that report.

---

### Baseline (Phase 0)
- lake build:               not run (local build stale per task brief; reasoned from source).
- decl resolved at:         `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:699`.
- kind:                     `lemma` (no `sorry`).
- enclosing namespace:      `namespace IsEllSequence` (opened line 643, closed `end IsEllSequence`
                            line 702). The earlier `namespace EllSequence` (line 90) is already
                            closed at line 597, and there is **no** `WeierstrassCurve` namespace in
                            this file. With `def _root_.IsEllSequence` at line 135, the
                            fully-qualified name is unambiguously **`IsEllSequence.invar`**.

---

### Statement (Phase 1)

```lean
namespace IsEllSequence
variable (ell : IsEllSequence W)      -- include ell
...
variable (one : W 1 ∈ R⁰) (two : W 2 ∈ R⁰)   -- include one two
...
lemma invar (s m n : ℤ) :
    invarNum W s m * invarDenom W s n = invarNum W s n * invarDenom W s m :=
  invar_of_net _ (ell.net one two) _ _ _
```

Ambient: `variable {R : Type u} [CommRing R] (W : ℤ → R)`, `open scoped nonZeroDivisors`.

Hypotheses: `ell : IsEllSequence W` (W is an elliptic sequence:
`∀ m n r, W(m+n)W(m−n)W(r)² = W(m+r)W(m−r)W(n)² − W(n+r)W(n−r)W(m)²`); `W 1, W 2 ∈ R⁰`
(first two terms are non-zero-divisors).

Local supporting defs (`EllipticDivisibilitySequence.lean`):
- `invarNum W s n := (W(n+2s)·W(n−s)² + W(n+s)²·W(n−2s))·W(s)² + W(n)³·W(2s)²`   (line 140)
- `invarDenom W s n := W(n+s)·W(n)·W(n−s)`                                        (line 145)
- `net W p q r s := W(p+q+s)W(p−q)W(r+s)W(r) − W(p+r+s)W(p−r)W(q+s)W(q) + W(q+r+s)W(q−r)W(p+s)W(p)`
  (line 115) — Stange's elliptic-net relation (sign/term-order tweaked vs. Stange to make the
  equivalence with the elliptic relation unconditional).
- `invar_of_net (net_eq_zero : ∀ p q r s, net W p q r s = 0) (s m n)` (line 149) — the **general**
  theorem: same conclusion for *any* `W` whose `net` vanishes identically, with no elliptic / no
  non-zero-divisor hypotheses.

#### Mathematical content
For an elliptic sequence `W`, the ratio `invarNum W s n / invarDenom W s n` is **independent of the
index `n`** (for each fixed shift `s`); the lemma states this cross-multiplied to stay division-free
over a general commutative ring. This is the classical "invariant" of an elliptic divisibility
sequence (it encodes the Weierstrass curve invariants `b₂, b₄, …`), constant precisely because `W`
satisfies the elliptic-net relation. `invar` itself is a **one-line corollary**: it plugs the
elliptic-sequence net proof `ell.net one two` into the general engine `invar_of_net`.

---

### Literature search (Phase 2)
- **Ward**, *Memoir on Elliptic Divisibility Sequences* — the file's cited reference; origin of EDS
  invariant/recurrence theory.
- **Stange**, *Elliptic nets and elliptic curves*, [arXiv:0710.1316](https://arxiv.org/abs/0710.1316)
  — source of the `net` relation used here.
- **"On Elliptic Sequences over Commutative Rings"**,
  [arXiv:2604.05280](https://arxiv.org/abs/2604.05280) (2026) — the direct foundation this fork
  formalizes: defines elliptic sequences over **commutative rings** via a 4-parameter family of
  homogeneous quartic "elliptic relations", classifies them, and **proves standard EDSs satisfy the
  elliptic relations by purely algebraic methods** (no Weierstrass ℘-analysis), as the algebraic
  basis for division polynomials. Matches the `[CommRing R]` / `nonZeroDivisors` / `rel₄` / `net`
  setup exactly. The invariant ratio is a standard tool inside this development.

Conclusion: genuine, citable, classical EDS mathematics — not an ad-hoc helper.

---

### Mathlib five-method search (Phase 2b) — is it there, or a more general form?

Mathlib's own `Mathlib.NumberTheory.EllipticDivisibilitySequence` is the file this project **forks**.

1. **Live mathlib4 docs** (fetched June 2026,
   `.../Mathlib/NumberTheory/EllipticDivisibilitySequence.html`): enumerated **all 70 declarations**.
   **None** of `invar`, `invarNum`, `invarDenom`, `net`, `rel₄`, `addMulSub`, `Rel₃`, `invar_of_net`,
   `isEllDivSequence_normEDS` appear. The page still carries the open
   **`TODO: prove that normEDS satisfies IsEllDivSequence`**.
2. **Local cached mathlib source** (`~/.cache/lean-lsp-mcp/loogle/repo`, rev `3ea6690`, v4.27.0-rc1;
   project pins `d90090f` / v4.31.0-rc2): `grep` of the EDS file for
   `invar|net|invarNum|invarDenom|rel₄|addMulSub|Stange` → **zero matches**. The mathlib file ends at
   `map_complEDS`; it has the *definitions* (`IsEllSequence`, `normEDS`, `complEDS`, …) but **none**
   of the proof apparatus the fork adds to discharge the TODO.
3. **DivisionPolynomial files** (`AlgebraicGeometry/EllipticCurve/DivisionPolynomial/{Basic,Degree}.lean`):
   consume `normEDS`/`preNormEDS`; no `invar`/`net` invariant lemma.
4. **WebSearch** for the invariant-ratio result under any name — surfaced only the primary literature,
   no mathlib decl.
5. (`lean_loogle`/`lean_leansearch` index tools were not exposed in this environment; the live-docs
   enumeration + source grep + web search are jointly conclusive.)

**Result: mathlib does NOT have this lemma, nor any more-general form.** The whole
`net`/`invar`/`invarNum`/`invarDenom`/`rel₄` machinery is new in the fork — exactly the upstream gap
(the standing TODO) it was written to fill.

---

### Generality analysis (Phase 3)
- The **maximally-general statement already lives in this file** as `invar_of_net` — it holds for an
  arbitrary `W : ℤ → R` over any `CommRing R` whose `net` vanishes identically, with **no** elliptic
  and **no** non-zero-divisor hypotheses. That is the right mathlib-level form.
- `IsEllSequence.invar` is the **specialization** packaging `invar_of_net` with the elliptic-sequence
  hypotheses (`ell`, `one`, `two`) via `ell.net one two`. As standalone API it is a thin convenience
  wrapper; its hypotheses (`W 1, W 2 ∈ R⁰`) are exactly those that make the net relation hold for an
  elliptic sequence.
- So it is not mechanically over-specialized in a fixable way — it is already the natural user-facing
  form of a more general lemma that is itself present. Nothing to weaken in `invar` beyond noting the
  heavy lifting is (and should remain) in `invar_of_net`.

---

### Composition check (Phase 4) — ≤ 3 mathlib calls?
**No** — the building blocks (`net`, `invarNum`, `invarDenom`, `invar_of_net`) **do not exist in
mathlib at all**, so there is nothing upstream to compose. Within the fork it *is* a 1-call corollary
of `invar_of_net`, but that is project-internal, not a mathlib primitive — so it does not count as
"composable from mathlib".

---

### Verdict (Phase 5): YES-but-generalise-first

Correct, classical, well-sourced EDS mathematics that mathlib genuinely lacks (it closes the
long-standing `normEDS satisfies IsEllDivSequence` TODO). It should go to mathlib — but **not as this
lone specialized wrapper**. The mathlibable unit is the *bundle*:

- `net` (Stange's relation), `invarNum`, `invarDenom`, and the general `invar_of_net` (the real,
  hypothesis-light theorem), with `IsEllSequence.invar` as the thin specialization on top; and
- ideally contributed as the body that proves the upstream TODO (`isEllDivSequence_normEDS`), the
  destination this machinery serves.

"Generalise first" here = lead with `invar_of_net` (general, assumption-minimal) and ship the
supporting defs alongside, rather than upstreaming the bare `IsEllSequence.invar` corollary in
isolation.

Explicitly **not** `NO-mathlib-has-it` (verified absent on live docs + source grep) and **not**
`NO-composable-from-mathlib` (the primitives are absent upstream).

#### Evidence index
- Source: `EllipticDivisibilitySequence.lean:699` (`invar`), `:149` (`invar_of_net`),
  `:140`/`:145` (`invarNum`/`invarDenom`), `:115` (`net`); namespace `IsEllSequence` `643`–`702`,
  `def _root_.IsEllSequence` `:135`.
- Live mathlib docs (June 2026): 70 decls, apparatus absent, TODO open.
- Cached mathlib grep (`3ea6690`): zero matches for the apparatus.
- Literature: arXiv:0710.1316 (Stange), arXiv:2604.05280 (elliptic sequences over commutative rings),
  Ward's Memoir.
