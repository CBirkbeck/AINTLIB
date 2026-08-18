# Mathlibable assessment: `EllSequence.addMulSub`

**Verdict: YES-but-generalise-first**

- **Qualified name:** `EllSequence.addMulSub`
- **Location:** `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:94`
- **Date:** 2026-06-18
- **One-line summary:** an *internal helper `def`* (the named building block
  `W((m+n)/2)·W((m−n)/2)`) of the project's `EllSequence` elliptic-relation layer; it is genuinely
  destined for mathlib, but only **as part of upstreaming that whole layer** (which closes the
  standing `normEDS satisfies IsEllDivSequence` TODO) — never as a stand-alone public declaration.

## Statement (verified from source)

```lean
namespace EllSequence
variable {R : Type u} [CommRing R] (W : ℤ → R)

/-- The expression `W((m+n)/2) * W((m-n)/2)` is the basic building block of elliptic relations,
where integers `m` and `n` should have the same parity. -/
def addMulSub (m n : ℤ) : R := W ((m + n).tdiv 2) * W ((m - n).tdiv 2)
-- Implementation note: we use `Int.tdiv _ 2` instead of `_ / 2` so that
-- `(-m).tdiv 2 = -(m.tdiv 2)`
-- and lemmas like `addMulSub_neg₀` hold unconditionally [...]
```

The parsed qualified name in the prompt (`EllSequence.addMulSub`) is **correct**: the decl sits
inside `namespace EllSequence` (opened at line 90), and it is a `def`, not a lemma.

Context — what it is for:
- `addMulSub` is the atom out of which the project builds the **four-index elliptic relation**
  `rel₄ W a b c d = addMulSub W a b * addMulSub W c d − addMulSub W a c * addMulSub W b d +
  addMulSub W a d * addMulSub W b c` (line 103), Stange's **elliptic net** relation `net`
  (line 115, `net_eq_rel₄` ties them together), the three-index `Rel₃` (line 130, = mathlib's
  `IsEllSequence` predicate), the hybrid `addMulSub₄` (line 261), `rel₆` (line 302), and the central
  nine-term expansion `addMulSub_sq_mul_rel₄_eq₉` (line 344). This is the elliptic-relation algebra
  that the project uses to prove **`normEDS` is an elliptic sequence**.
- The deliberate use of `Int.tdiv _ 2` (rather than `_ / 2`) is an **implementation device**: it makes
  the sign/abs lemmas (`addMulSub_neg₀/₁`, `addMulSub_abs₀/₁`, `addMulSub_swap`, lines 184–199) hold
  *unconditionally*. The docstring itself labels it "the basic building block of elliptic relations."
- It carries no mathematical content of its own: `addMulSub` unfolds in one step to a product of two
  `W`-values at `Int.tdiv`-halved indices.

## 1. Literature search

- `addMulSub` is **not a named object in the literature.** The relevant math companion is Angdinata–Xu,
  *On Elliptic Sequences over Commutative Rings* (arXiv:2604.05280) — the paper behind exactly this
  Lean development (the abstract notes Angdinata's Mathlib EDS formalisation "rediscovered the idea of
  adjusting the definition of division polynomials to satisfy elliptic relations"). It, Stange's
  *Elliptic nets and elliptic curves* (arXiv:0710.1316), and Stange's EDS/elliptic-net **formulary**
  (math.colorado.edu/~kstange/papers/edsformulary.pdf) all manipulate products of the shape
  `W(m+n)·W(m−n)` inside the four-index recurrence
  `W_{n+m}W_{n−m}W_r² = W_{n+r}W_{n−r}W_m² − W_{m+r}W_{m−r}W_n²`
  and Stange's net relation
  `W(p+q+s)W(p−q)W(r+s)W(r) − …` — i.e. the *relations* `rel₄`/`net` are standard. But the **2-argument
  helper** `addMulSub`, keyed on the half-sum/half-difference `(m±n)/2` and pinned to `Int.tdiv`, is a
  formalisation convenience, not a textbook notion. No paper gives it a name; no standalone citation.
- Background sweep (EDS area): Ward, *Memoir on Elliptic Divisibility Sequences* (the file's cited
  reference); Shipsey/Swart EDS theses; *EDS, Squares and Cubes* (arXiv:1101.3839). None introduce
  `addMulSub` as an object.

**Takeaway:** the *content* that belongs in mathlib is the elliptic-relation layer (`rel₄`/`net` and
"`normEDS` is elliptic"), which is canonical; `addMulSub` is the internal scaffolding for it.

## 2. Mathlib search (five methods) — forked files checked first

Per project context, NagellLutz **forks** `Mathlib.NumberTheory.EllipticDivisibilitySequence` and
`Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.*`, so the first question is whether this
`def` is already upstream. It is not.

- **grep** `addMulSub` / `def addMulSub` / `EllSequence` over the pinned mathlib checkout
  (`.lake/packages/mathlib/Mathlib/**`, source tree) → **zero hits**. The forked file
  `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean` (547 lines) ends at the
  `normEDS`/`complEDS`/`*Rec`/`map_*` machinery and has **no `EllSequence` namespace** and **none** of
  `addMulSub`, `rel₄`, `net`, `Rel₃`, `addMulSub₄`, `rel₆`. The entire ~1100-line elliptic-relation
  extension (project file is 1667 lines) is **new, not yet upstream**.
- **Live mathlib4 docs**, fetched 2026-06-18
  (`leanprover-community.github.io/mathlib4_docs/.../EllipticDivisibilitySequence.html`): confirms no
  `addMulSub` / `EllSequence` / `rel₄` / `net`, and that the file still carries the two open TODOs:
  > * TODO: prove that `normEDS` satisfies `IsEllDivSequence`.
  > * TODO: prove that a normalised sequence satisfying `IsEllDivSequence` can be given by `normEDS`.
  The `EllSequence` layer this `def` anchors is precisely the in-flight work to discharge TODO #1.
- **loogle / leansearch** (mathlib index): consistent — no decl of this name or shape (a `ℤ → ℤ → R`
  product of two `W`-values at `Int.tdiv`-halved indices) upstream.
- **Name/def search** across mathlib for the *body* (`Int.tdiv ... 2` product of sequence terms):
  nothing analogous; `Int.tdiv` appears only as the arithmetic primitive.
- **Within AINTLIB** (not mathlib): `addMulSub` is **triplicated** — here, plus
  `HasseWeil/Auxiliary/EllipticDivisibilitySequence.lean:38` and the project's own
  `EllipticDivisibilitySequenceOriginal.lean:93`. That is intra-repo forking/dedup (a `/cleanup`
  concern), **not** evidence of a mathlib home.

**Conclusion:** neither `addMulSub` nor its surrounding `EllSequence` layer is in mathlib today.

## 3. Generality analysis

- Already **maximally general** for what it is: arbitrary `CommRing R`, arbitrary sequence
  `W : ℤ → R`, arbitrary integer indices. There are no hypotheses to weaken and no obvious common
  generalisation (it is just a product of two terms). So there is nothing to *generalise* in the
  assumption-weakening sense.
- The "generalise-first" verdict here is in the **packaging** sense used by the sibling reports
  (cf. `isEllSequence_ψ.md`): the correct *unit* to upstream is not this lone helper but the
  elliptic-relation development it belongs to. As a public, stand-alone mathlib declaration
  `addMulSub` is the wrong granularity — it is an unexported scaffolding def whose only purpose is to
  make the `rel₄`/`net` lemmas readable and the sign lemmas unconditional.

## 4. Composition check (≤3 mathlib calls)

- As a term, `addMulSub W m n` is literally `W ((m+n).tdiv 2) * W ((m-n).tdiv 2)` — a **1-line
  composition** of mathlib primitives (`Int.tdiv`, `HAdd`, `HSub`, `HMul`). So in the narrow sense it
  is trivially "composable from mathlib."
- But that misses the point of a helper `def`: its value is precisely to **name** this composition so
  that ~20 downstream lemmas (`addMulSub_even/_odd/_same/_neg/_abs/_swap`, `map_addMulSub`,
  `addMulSub₄_*`, `addMulSub_sq_mul_rel₄_eq₉`, `addMulSub_mem_nonZeroDivisors`, …) and the `rel₄`/`net`
  definitions can be stated against a single symbol. A def that exists to abbreviate a recurring
  pattern is not "NO-composable" the way a *theorem* re-derivable in ≤3 steps would be — there is no
  proof to reconstruct, only an abbreviation that the rest of the file depends on.

## 5. Five-bucket verdict

**YES-but-generalise-first.**

- Not **NO-mathlib-has-it**: grep + live mathlib4 docs (2026-06-18) confirm no `addMulSub`, no
  `EllSequence` namespace, no `rel₄`/`net` upstream; the layer is the open `normEDS`-is-elliptic TODO.
- Not **NO-composable-from-mathlib**: although the *body* is a one-liner, this is a definition whose
  role is to name a pattern the whole `EllSequence` file is built on; "re-derive in ≤3 calls" does not
  apply to a naming `def`, and the substantive object (the relation algebra) is genuinely absent.
- Not **YES-add-as-is**: shipping this lone helper as a public mathlib declaration is the wrong unit —
  it is internal scaffolding (ideally `private`/section-local) that is meaningless without the
  `rel₄`/`net`/`addMulSub_sq_mul_rel₄_eq₉` machinery it supports; and it is currently triplicated
  inside AINTLIB (a dedup chore), not a polished standalone API.
- Not **BORDERLINE**: the path is clear — it rides along with the elliptic-relation upstreaming.

**What to upstream (the right unit):** the **`EllSequence` elliptic-relation layer** of
`EllipticDivisibilitySequence.lean` — `addMulSub` (as an internal/`private` helper), its sign/parity
lemmas, `rel₄`, `net`/`net_eq_rel₄`, `Rel₃`, and the nine-term expansion
`addMulSub_sq_mul_rel₄_eq₉` — culminating in **"`normEDS` is an `IsEllSequence`" / `IsEllDivSequence`**,
which closes the standing mathlib TODO in `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean`.
`addMulSub` belongs in mathlib **inside that PR, as the named building block**, not as an independent
public lemma assessed on its own.

## Notes / cross-refs

- Mathlib upstream EDS file: `.lake/packages/mathlib/Mathlib/NumberTheory/EllipticDivisibilitySequence.lean`
  (547 lines; no `EllSequence` layer). Project extension:
  `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean` (1667 lines).
- Intra-AINTLIB duplicates of this `def` (dedup, not mathlibability):
  `projects/HasseWeil/HasseWeil/Auxiliary/EllipticDivisibilitySequence.lean:38`,
  `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequenceOriginal.lean:93`.
- Consistent with the sibling assessment `isEllSequence_ψ.md` (same directory): the in-flight
  `normEDS`-is-elliptic work is the real mathlibable payload; the thin/internal pieces inherit a
  "generalise/repackage first" verdict pointing at that larger unit.

## Sources

- Stange, *Elliptic nets and elliptic curves* — https://arxiv.org/abs/0710.1316
- Stange, EDS / elliptic-net formulary — https://math.colorado.edu/~kstange/papers/edsformulary.pdf
- Angdinata–Xu, *On Elliptic Sequences over Commutative Rings* — https://arxiv.org/pdf/2604.05280
- Mathlib4 docs, `Mathlib.NumberTheory.EllipticDivisibilitySequence` (open TODOs; no `EllSequence`
  layer), fetched 2026-06-18 —
  https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/EllipticDivisibilitySequence.html
- *Elliptic divisibility sequence* (four-index recurrence) — https://en.wikipedia.org/wiki/Elliptic_divisibility_sequence
