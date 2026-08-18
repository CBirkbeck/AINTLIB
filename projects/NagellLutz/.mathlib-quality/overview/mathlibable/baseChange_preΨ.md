# /mathlibable report — `WeierstrassCurve.baseChange_preΨ`

**Verdict: NO-mathlib-has-it** (identical lemma, identical namespace, identical proof — the project file is an explicit fork-copy of the mathlib source).

---

### Baseline (Phase 0)
- lake build:               not run (build stale per task; reasoning from source — decl elaborates in the upstream mathlib copy it is verbatim duplicated from)
- decl `WeierstrassCurve.baseChange_preΨ`: ✓ resolved at `projects/NagellLutz/LutzNagell/DivisionPolynomial.lean:491`
- kind:                      lemma
- has sorry:                 no
- module docstring summary:  "This is a copy of `Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic` that imports `LutzNagell.EllipticDivisibilitySequence` instead of the mathlib version, to avoid name conflicts (both define `normEDS`, `complEDS`, etc.). See the original file for full documentation."

The qualified name is confirmed `WeierstrassCurve.baseChange_preΨ`: the file opens `namespace WeierstrassCurve` (line 27) and closes `end WeierstrassCurve` (line 511); the lemma sits inside `section BaseChange`.

---

### Statement (Phase 1)

`WeierstrassCurve.baseChange_preΨ` states: for a Weierstrass curve `W` over a commutative ring `R`,
and a tower `R → S → A → B` of commutative rings with an `S`-algebra homomorphism `f : A →ₐ[S] B`,
the `n`-th auxiliary ("pre") division polynomial `preΨ n` of the base change of `W` to `B` equals the
image, under the polynomial map induced by `f`, of `preΨ n` of the base change of `W` to `A`:

  `(W.baseChange B).preΨ n = ((W.baseChange A).preΨ n).map f`   (for all `n : ℤ`).

In words: forming the auxiliary division polynomial commutes with base change along an algebra
homomorphism. The `preΨ n` are the univariate auxiliary polynomials of an elliptic divisibility
sequence whose products with powers of `ψ₂` give the genuine division polynomials `ψ n`.

Variables / typeclasses (Lean side):
- `{R} [CommRing R]`, `(W : WeierstrassCurve R)` — the base curve.
- `{S} [CommRing S]`, `[Algebra R S]` — intermediate base ring.
- `{A} [CommRing A] [Algebra R A] [Algebra S A] [IsScalarTower R S A]` — source of the algebra map.
- `{B} [CommRing B] [Algebra R B] [Algebra S B] [IsScalarTower R S B]` — target.
- `(f : A →ₐ[S] B)` — the `S`-algebra homomorphism along which we base-change.
- `(n : ℤ)` — index of the division polynomial.

Hypotheses: none beyond the typeclass tower.

Conclusion (math): `preΨ` commutes with base change.
Conclusion (Lean): `(W.baseChange B).preΨ n = ((W.baseChange A).preΨ n).map f`.

Proof body: `rw [← map_preΨ, map_baseChange]` — two rewrites, reducing the base-change statement to
the already-established `map`-compatibility lemma `map_preΨ` plus `map_baseChange` (which identifies
base change as a particular `WeierstrassCurve.map`).

---

### Size classification (Phase 2a)

Verdict: SMALL
Reason: a naturality/compatibility helper lemma (base change commutes with `preΨ`), one of a uniform
family (`baseChange_ψ₂`, `baseChange_Ψ₃`, `baseChange_preΨ₄`, `baseChange_preΨ'`, `baseChange_ΨSq`,
`baseChange_Ψ`, `baseChange_Φ`, `baseChange_ψ`, `baseChange_φ`) — not a named theorem, not a new
structure, not a project main result.

### One-line check (Phase 2b)

n/a — kind is `lemma`, not `def`/`abbrev`/`structure`. (Proof is a 2-rewrite one-liner, but the
one-line *definition* check does not apply to lemmas.)

---

### Literature search (Phase 3)

Short-circuit justification: this is not an open literature question. The project file's own module
docstring declares the lemma a **verbatim copy** of a specific mathlib file, and Phase 5 located the
byte-for-byte original in the current mathlib pin (same namespace, same signature, same proof). When
the decl under assessment is a fork-copy of an existing mathlib lemma, the literature-standardisation
question is moot — the relevant authority is mathlib itself, already consulted. A full 9-channel
literature sweep on "division polynomials commute with base change" would only re-derive what the
mathlib source already encodes. Recorded for completeness:

| # | Channel | Query | Hit? | Standard form | Notes |
|---|---------|-------|------|---------------|-------|
| 1 | Mathlib source (authoritative) | `baseChange_preΨ` in `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean` | yes | identical lemma, line 568 | the canonical source the project copied |
| 2 | Literature (concept) | Silverman, *Arithmetic of Elliptic Curves*, Exercise 3.7 — division polynomials | yes | division polynomials are polynomial in the curve coefficients ⇒ commute with any ring hom of coefficients | naturality is immediate from the polynomial formulas; not a named theorem |
| 3–10 | WebSearch / ChatGPT MCP / nLab / Stacks / nCatLab / MathOverflow / arXiv | n/a | — | — | not run: fork-copy of an extant mathlib lemma; literature-standardisation question is moot (see justification above) |

### Literature summary (Phase 3)

Concept identified as: base-change/naturality compatibility of (auxiliary) elliptic division
polynomials. The underlying mathematics (division polynomials are universal polynomials in `b₂,b₄,b₆,b₈`,
hence commute with any homomorphism of the coefficient ring) is classical and standard; the Lean
*lemma* packaging it is David Angdinata's mathlib API. Mathlib already states it at the natural
generality (arbitrary algebra map in a scalar tower).

---

### Generality analysis (Phase 4)

The current Lean form is **identical** to the mathlib form — same typeclass tower
(`[Algebra R S]`, `{A} [CommRing A] … [IsScalarTower R S A]`, `{B} … [IsScalarTower R S B]`,
`f : A →ₐ[S] B`), same `(n : ℤ)`, same conclusion. There is nothing to weaken or generalise
relative to mathlib: it *is* the mathlib statement, copied.

| # | Parameter / hypothesis | Current Lean form | Mathlib form | Weaker form? | Note |
|---|------------------------|-------------------|--------------|--------------|------|
| 1 | scalar tower `R→S→A→B`, `f : A →ₐ[S] B` | algebra hom in a tower | identical | NO | already mathlib's chosen generality |
| 2 | `(n : ℤ)` | integer index | identical | NO | matches mathlib |

### Generality verdict (Phase 4b)

The current form is: identical to mathlib (neither narrower nor more general).
Weakening opportunities: 0.

### Modern-idiom check (Phase 4c)

Modern idiom available: no. The lemma already uses the contemporary mathlib idiom — base change via
`AlgHom` in an `IsScalarTower`, reduced to `WeierstrassCurve.map` through `map_baseChange`. It is
the mathlib idiom verbatim; there is no further modernisation to make.

---

### Mathlib search-status: `WeierstrassCurve.baseChange_preΨ`

[A] Lean-Finder       n/a (build/index stale) — superseded by direct grep hit below
[B] Loogle            n/a — superseded by direct grep hit below
[C] LeanSearch        n/a — superseded by direct grep hit below
[D] Grep mathlib src  `baseChange_preΨ`, `map_preΨ`, `map_baseChange`, `def preΨ` → **HITS**
[E] Name pattern      `baseChange_preΨ` in `WeierstrassCurve` namespace → **HIT**

Direct hits in the current mathlib pin
(`/Users/mcu22seu/Documents/GitHub/aintlib-main/.lake/packages/mathlib/Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean`):

- `WeierstrassCurve.baseChange_preΨ` — **line 568**, namespace `WeierstrassCurve` (file `namespace WeierstrassCurve` @104, `end` @588), `section BaseChange` @546:
  ```
  lemma baseChange_preΨ (n : ℤ) : (W⁄B).preΨ n = ((W⁄A).preΨ n).map f := by
    rw [← map_preΨ, map_baseChange]
  ```
  `W⁄B` / `W⁄A` are mathlib's scoped `notation3` for `W.baseChange B` / `W.baseChange A`; modulo this
  notation the statement and proof are **character-identical** to the project's lines 491–492. The
  whole surrounding variable block (line 552) — `variable [Algebra R S] {A : Type u} [CommRing A]
  [Algebra R A] [Algebra S A] [IsScalarTower R S A] {B : Type v} [CommRing B] [Algebra R B]
  [Algebra S B] [IsScalarTower R S B] (f : A →ₐ[S] B)` — matches the project's line 473–474 verbatim.
- Supporting decls also present upstream: `def preΨ (n : ℤ)` @194, `map_preΨ` @518, `map_baseChange`
  (referenced by the proof, defined earlier in the file). All in `WeierstrassCurve`.

Concluded: **found in mathlib as `WeierstrassCurve.baseChange_preΨ`; identical form** (same namespace,
same signature, same proof). The entire `section BaseChange` of the project file is a 1:1 duplicate of
mathlib's `section BaseChange`.

---

### Call sites — `WeierstrassCurve.baseChange_preΨ`

Internal use count: **0** (within the NagellLutz project, excluding the declaring file).
External-to-file callers: 0.

Grep for `baseChange_preΨ` across the whole repo (`--include="*.lean" --exclude-dir=".lake"`) returns
only sibling declarations inside the declaring file itself (`baseChange_Ψ₂Sq`, `baseChange_Ψ₃`,
`baseChange_preΨ₄`, `baseChange_preΨ'`, `baseChange_preΨ`, `baseChange_ΨSq`, `baseChange_Ψ` — i.e.,
the substring matches of neighbouring lemmas). No consumer anywhere uses `baseChange_preΨ`.

Inline-derivation grep: (none) — nobody re-derives the statement either; the lemma is simply
unused-and-duplicated.

Signal: K = 0 internal uses, no inline re-derivation, AND the lemma is a verbatim copy of an existing
mathlib lemma ⇒ the copy carries no project-specific content. (It exists only because the file had to
be forked wholesale to swap the `EllipticDivisibilitySequence` import and dodge the `normEDS` name
clash; this particular lemma was carried along, not authored.)

---

### Composition check (Phase 6)

Not needed for the verdict (mathlib has the lemma outright), but trivially: the statement is exactly
`WeierstrassCurve.baseChange_preΨ` from mathlib — a 0-step "composition" (use the mathlib lemma
directly). Were one to re-derive it, mathlib's own one-liner `rw [← map_preΨ, map_baseChange]` does it
in ≤3 calls from `WeierstrassCurve.map_preΨ` and `WeierstrassCurve.map_baseChange`.

Conclusion: the form is supplied directly by mathlib.

---

## Verdict: `WeierstrassCurve.baseChange_preΨ`

**Category:** NO-mathlib-has-it

**Evidence:**
- Literature search (Phase 3): the project's own docstring declares the file a copy of
  `Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic`; mathematics is classical
  naturality of division polynomials.
- Generality analysis (Phase 4): current form is *identical* to mathlib's (0 weakenings, no
  modern-idiom gap).
- Mathlib search (Phase 5): found in mathlib as `WeierstrassCurve.baseChange_preΨ`,
  `…/DivisionPolynomial/Basic.lean:568`, same namespace, identical statement and proof.
- Composition check (Phase 6): supplied directly by the mathlib lemma.

**Rationale:**

Mathlib already contains `WeierstrassCurve.baseChange_preΨ` verbatim — same `WeierstrassCurve`
namespace, the same `(n : ℤ) : (W.baseChange B).preΨ n = ((W.baseChange A).preΨ n).map f` statement
(written `W⁄B` / `W⁄A` via mathlib's base-change notation), and the same two-rewrite proof
`rw [← map_preΨ, map_baseChange]`. The NagellLutz copy is not an independent re-derivation but an
explicit fork: the module docstring (lines 12–16) states the file is "a copy of
`Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic`" re-imported against the project's
local `EllipticDivisibilitySequence` purely to avoid the `normEDS` / `complEDS` name conflict. The
entire `section BaseChange` (and indeed the file) is duplicated 1:1 from upstream. This decl
contributes nothing mathlib is missing.

**WHY not (refactor-actionable):**

Mathlib has it outright (`WeierstrassCurve.baseChange_preΨ`), so there is nothing to upstream. The
project copy exists only as collateral of forking the whole `DivisionPolynomial.Basic` file to swap
one import. The real fix is structural, not per-lemma: the duplication should be resolved at the file
level once the local-vs-mathlib `EllipticDivisibilitySequence` name clash is reconciled (e.g., by
namespacing the project's EDS or by upstreaming/aligning it), after which the project can drop its
fork of `DivisionPolynomial.Basic` entirely and `import
Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic`. Removing only `baseChange_preΨ` in
isolation is neither possible nor useful while the rest of the forked file remains.

Existing mathlib decl:  `WeierstrassCurve.baseChange_preΨ`
Located at:             `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean:568`
Our form follows in ≤1 line (it *is* the mathlib lemma):
```lean
example (W : WeierstrassCurve R) [Algebra R S] {A : Type u} [CommRing A] [Algebra R A] [Algebra S A]
    [IsScalarTower R S A] {B : Type v} [CommRing B] [Algebra R B] [Algebra S B] [IsScalarTower R S B]
    (f : A →ₐ[S] B) (n : ℤ) :
    (W.baseChange B).preΨ n = ((W.baseChange A).preΨ n).map f :=
  WeierstrassCurve.baseChange_preΨ f n
```
Call sites in our project (Phase 6.0): K = 0.
Refactor plan: there are no call sites to redirect. The lemma is dead-and-duplicated. The correct
action is the file-level de-fork above: reconcile the project's `EllipticDivisibilitySequence`
namespace with mathlib's, then delete the project's `LutzNagell/DivisionPolynomial.lean` copy of
`section BaseChange` (and ideally the whole file) and import the mathlib originals. This is a
consolidation/dedup ticket on `main`, not a mathlib PR.

Next action: file a dedup/cleanup ticket — drop the forked `DivisionPolynomial.Basic` copy (this
lemma included) in favour of importing mathlib once the EDS name conflict is resolved. Do **not** open
a mathlib PR; mathlib already has this lemma.
