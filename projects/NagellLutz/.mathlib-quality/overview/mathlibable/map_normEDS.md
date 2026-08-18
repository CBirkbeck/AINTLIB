# /mathlibable report — `map_normEDS`

> Step-9 mathlibable assessment, NagellLutz project (Nagell–Lutz; elliptic curves;
> division polynomials; elliptic divisibility sequences). Reasoned from source (local
> build stale; mathlib source read directly from `.lake/packages/mathlib`). Read-only on `.lean`.

## Verdict: NO-mathlib-has-it

Mathlib **already contains this exact lemma**, with the identical statement, the same name,
and the same top-level scope, in the very file this project forks:
`Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:530` (carrying `@[simp]`).

## Declaration

- **Qualified name:** `map_normEDS` (VERIFIED — sits in the bare `section Map` at file scope;
  the enclosing `namespace EllSequence` closed at line 1112 and `section Complement` at 1114,
  and `section`s do not qualify names, so the fully-qualified name is simply `map_normEDS`).
- **Location:** `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:1134`
- **Kind:** lemma. **Has sorry:** no.
- **Statement (project):**
  ```
  variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]
  variable {F} [FunLike F R S] [RingHomClass F R S] (f : F)
  variable {b c d : R}

  lemma map_normEDS (n : ℤ) : f (normEDS b c d n) = normEDS (f b) (f c) (f d) n := by
    rw [normEDS, map_mul, map_preNormEDS, map_pow, apply_ite f, map_one, normEDS]
  ```
- **Meaning:** a ring homomorphism `f` commutes with the normalised-EDS construction —
  i.e. `normEDS` is natural/functorial in its coefficient ring. Pushing the parameters
  `b, c, d` through `f` and then forming the EDS agrees with forming `normEDS b c d n`
  and applying `f` termwise.

## Step 1 — Literature search

Not a named mathematical theorem. This is the *functoriality / base-change* (ring-hom
compatibility) lemma for a specific mathlib-internal object, the normalised elliptic
divisibility sequence `normEDS`. Such `map_<construction>` naturality lemmas are pure
formalisation plumbing and have no standalone presence in the mathematical literature; a
literature sweep cannot surface a "theorem" here. The underlying object (normalised EDS /
division polynomials) traces to M. Ward, *Memoir on Elliptic Divisibility Sequences*
(cited in both file headers), but the naturality statement itself is a Lean-API artefact.
No `--exhaustive` sweep is warranted for a decl of this kind.

## Step 2 — Mathlib search (decisive: exact hit)

- **File:** `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean`, present in the pinned
  mathlib (`.lake/packages/mathlib/Mathlib/NumberTheory/EllipticDivisibilitySequence.lean`).
- **Mathlib declaration (lines 507, 529–531):**
  ```
  variable {S : Type v} [CommRing S] (f : R →+* S)   -- line 507

  @[simp]
  lemma map_normEDS (n : ℤ) : f (normEDS b c d n) = normEDS (f b) (f c) (f d) n := by
    simp [normEDS, apply_ite f]
  ```
- **Same name, same statement, same scope** (top-level, in `section Map`), and marked `@[simp]`.
- The underlying definition is **character-for-character identical** in both files:
  `def normEDS (n : ℤ) : R := preNormEDS (b ^ 4) c d n * if Even n then b else 1`
  (project line 890; mathlib line 289).
- The whole project file is a **verbatim fork** of the mathlib file by the **same author**
  (David Kurniadi Angdinata — identical Apache copyright header on both). The companion
  `map_*` lemmas line up 1:1: project `map_preNormEDS'`/`map_preNormEDS`/`map_compl₂EDS`/
  `map_complEDS` ↔ mathlib lines 510/522/526/544 of the same file.

Search methods exercised: filesystem grep of `.lake/packages/mathlib` on name **and**
statement (exact match), direct read of the mathlib EDS source, and structural diff of the
`normEDS` definition and the `f` variable bindings. All converge on a single exact hit.

## Step 3 — Generality analysis

The only delta between the two versions is the type of the ring-map argument:

| | type of `f` | accepts |
|---|---|---|
| **mathlib** (line 530) | `f : R →+* S` (concrete bundled ring hom) | `RingHom` |
| **project** (line 1134) | `(f : F)` with `[FunLike F R S] [RingHomClass F R S]` | any `RingHomClass` type (`RingHom`, `AlgHom`, `RingEquiv`, …) directly |

So the project statement is *marginally* more general (stated against the `RingHomClass`
bundle rather than the concrete `R →+* S`). This is a small, mechanical, well-understood
difference — and mathlib **deliberately** states most of its `map_*` lemmas with the
concrete `→+*` form, leaving callers to coerce. It is not new mathematics and does not
warrant a new declaration. If the bundled form is desired, the correct action is an in-place
tweak to mathlib's existing `map_normEDS` (swap `R →+* S` for a `RingHomClass` variable),
not adding the fork. The project's form also follows from mathlib's in ≤1 line (apply the
coercion `f : R →+* S` induced by `RingHomClass`).

## Step 4 — Composition check

For completeness (an exact hit already settles the verdict): the lemma reduces to a short
`rw`/`simp` over existing mathlib API — `map_mul`, `map_preNormEDS`, `map_pow`, `apply_ite`,
`map_one`, plus the `normEDS` definitional unfold (mathlib's own proof is the one-liner
`simp [normEDS, apply_ite f]`). So it is additionally composable in ≤3 mathlib calls once
`map_preNormEDS` is available. Both "mathlib already has it" and "composable from mathlib"
hold; the former dominates.

## Step 5 — Verdict

**NO-mathlib-has-it.** `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:530` already
provides `map_normEDS` with the identical statement over the character-identical `normEDS`
definition, as `@[simp]`. The project lemma is a verbatim fork whose sole difference is
stating `f` via `RingHomClass` instead of the concrete `R →+* S` — a minor style/generality
nuance to be folded into mathlib's existing lemma if wanted, never a reason to add a new decl.

### Note for the consolidation effort
This entire project file (`LutzNagell/EllipticDivisibilitySequence.lean`) duplicates
`Mathlib/NumberTheory/EllipticDivisibilitySequence.lean`. The right move is to **drop the
fork and import mathlib's version** (optionally upstreaming the `RingHomClass`-vs-`→+*`
generalisation as a one-line change to mathlib's `map_normEDS` and its sibling `map_*`
lemmas), rather than assessing any of these `map_*` lemmas as individual mathlib candidates.
