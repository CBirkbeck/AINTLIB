# /mathlibable report — `WeierstrassCurve.map_ψ₂`

## Verdict: **NO-mathlib-has-it**

The declaration is a **byte-for-byte verbatim copy** of an existing mathlib lemma.
The file's own module docstring says so explicitly. This is a forked-from-mathlib
declaration, not a new contribution.

---

### Baseline (Phase 0)
- lake build:               not re-run (stale per task note); decl reasoned from source
- decl `WeierstrassCurve.map_ψ₂`:  resolved at `projects/NagellLutz/LutzNagell/DivisionPolynomial.lean:421`
- kind:                     lemma (`@[simp]`)
- has sorry:                no
- qualified name (VERIFIED): `WeierstrassCurve.map_ψ₂` — confirmed: file is `namespace WeierstrassCurve` (line 27), no inner namespace, base name `map_ψ₂`. The parsed guess was correct.
- module docstring summary: "This is a copy of `Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic` that imports `LutzNagell.EllipticDivisibilitySequence` instead of the mathlib version, to avoid name conflicts (both define `normEDS`, `complEDS`, etc.). See the original file for full documentation."

### Statement (Phase 1)

`WeierstrassCurve.map_ψ₂` states: for a Weierstrass curve `W` over a commutative
ring `R` and a ring homomorphism `f : R →+* S`, the 2-division polynomial of the
base-changed curve `W.map f` equals the image of `W`'s 2-division polynomial under
the induced map on the bivariate polynomial ring `R[X][Y] → S[X][Y]`. In symbols,
`(W.map f).ψ₂ = (W.ψ₂).map (mapRingHom f)`.

It is a naturality / compatibility-with-base-change `@[simp]` lemma for `ψ₂`.

- Lean parameters: `{R S} [CommRing R] [CommRing S] (W : WeierstrassCurve R) (f : R →+* S)`.
- Conclusion (Lean): `(W.map f).ψ₂ = W.ψ₂.map (mapRingHom f)`.
- Proof: `by simp_rw [ψ₂, Affine.map_polynomialY]` (since `ψ₂ := W.toAffine.polynomialY`, this is naturality of `polynomialY`).

### Size classification (Phase 2a)

Verdict: SMALL — a one-line naturality `@[simp]` glue lemma, not a named theorem,
not a new structure, not a `## Main results` entry.

### One-line check (Phase 2b)

n/a — kind is `lemma`, not `def`/`abbrev`/`structure`. (For the record the proof is
a single `simp_rw`; it is a glue/naturality lemma.)

### Phases 3–4 / 4.5 (literature / generality / diamond) — SHORT-CIRCUITED, justified

The `mathlibable` workflow's verdict gate for **NO-mathlib-has-it** requires only a
Phase 5 mathlib hit cited by qualified name plus a ≤1-line follow. When the project
declaration is a **verbatim copy of an existing mathlib lemma** — identical
namespace, identical signature, identical typeclass context, identical proof, and
the file says it is a copy — the literature-standard-form and generality questions
are already answered by mathlib itself (mathlib *is* the standard form here, authored
by David Kurniadi Angdinata as part of the division-polynomial API). Running the
nine-channel literature sweep would not change the verdict and the task explicitly
flagged this fork scenario ("this decl may ALREADY be in mathlib — check those
mathlib files first").

Recorded for completeness:
- Literature concept: the 2-division polynomial `ψ₂` (a.k.a. `Ψ₂`) of a Weierstrass
  curve and its base-change naturality. Standard in Silverman, *The Arithmetic of
  Elliptic Curves*, and in the EDS literature (Ward; Shipsey). Generality (commutative
  ring `R`, arbitrary ring hom `f`) is already the maximally general form — mathlib
  states it over `CommRing` with a bare `RingHom`, which is exactly the literature-
  general setting.
- Generality verdict: MAXIMALLY GENERAL (matches mathlib verbatim; nothing to weaken).
- Modern-idiom (4c): no change — this is already the contemporary mathlib idiom (it
  IS the mathlib lemma).
- Diamond/defeq (4.5): n/a — kind is `lemma`.

### Mathlib search-status (Phase 5)

```
[A] Lean-Finder       n/a (index stale locally)        —
[B] Loogle            n/a (index stale locally)        —
[C] LeanSearch        n/a (index stale locally)        —
[D] Grep mathlib src  "map_ψ₂" over .lake/.../Mathlib/  HIT (exactly one source hit)
[E] Name pattern      "lemma map_ψ₂"                    HIT
```

Grep result (authoritative — the local mathlib checkout is the ground truth):

- `.lake/packages/mathlib/Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean:498`
  ```
  @[simp]
  lemma map_ψ₂ : (W.map f).ψ₂ = W.ψ₂.map (mapRingHom f) := by
    simp_rw [ψ₂, Affine.map_polynomialY]
  ```
  in `namespace WeierstrassCurve` (line 104), under
  `variable {R : Type r} {S : Type s} [CommRing R] [CommRing S] (W : WeierstrassCurve R)`
  (line 106) and `variable (f : R →+* S)` (line 495).

Byte-comparison of the two definitions (mathlib L498–499 vs project L421–422):
**IDENTICAL** (statement + proof), verified via `diff`.

Concluded: **found in mathlib as `WeierstrassCurve.map_ψ₂`; identical form**
(same fully-qualified name, signature, typeclasses, attribute, and proof term).

### Call sites (Phase 6.0)

Internal use count (NagellLutz project, excluding the declaring file): 2
- `projects/NagellLutz/LutzNagell/DivisionPolynomialOmega.lean:113` — `... map_ψ₂, map_Ψ₃, map_preΨ₄, ...` (simp set in a base-change rewrite)
- `projects/NagellLutz/LutzNagell/ZSMul.lean:89` — `simp_rw [polyEval_apply, ← map_ψ₂, map_specialize]`

Plus one in-file use: `DivisionPolynomial.lean:477` — `rw [← map_ψ₂, map_baseChange]`
(identical to mathlib's own internal use at `Basic.lean:554`).

Note: `HasseWeil/Auxiliary/DivisionPolynomial.lean:140,164` also reference `map_ψ₂`,
but resolve against *that* project's own separate copy, not this NagellLutz decl.

Inline-derivation grep: the lemma is used as named API (real consumers), but those
consumers would resolve equally against mathlib's `WeierstrassCurve.map_ψ₂` — the
names and signatures coincide exactly.

### Composition check (Phase 6)

Trivially COMPOSABLE but moot: it is literally the same lemma. No composition needed —
mathlib already provides the identical `@[simp]` lemma.

---

## Verdict: `WeierstrassCurve.map_ψ₂`

**Category:** NO-mathlib-has-it

**Evidence:**
- Mathlib search (Phase 5): found in mathlib as `WeierstrassCurve.map_ψ₂` at
  `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean:498`;
  identical statement, typeclasses, `@[simp]` attribute, and proof (`diff` = identical).
- Generality (Phase 4): MAXIMALLY GENERAL — it equals the mathlib form verbatim.
- Composition (Phase 6): n/a — same lemma.
- Provenance: the project file's module docstring (line 12) states it is "a copy of
  `Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic`".

**Rationale:**

`WeierstrassCurve.map_ψ₂` is not a candidate for upstreaming because mathlib already
contains the exact lemma — same fully-qualified name, same `CommRing`/`RingHom`
context, same `@[simp]` attribute, same `by simp_rw [ψ₂, Affine.map_polynomialY]`
proof. The NagellLutz copy exists for one mechanical reason, stated in its own header:
it re-imports `LutzNagell.EllipticDivisibilitySequence` in place of
`Mathlib.NumberTheory.EllipticDivisibilitySequence` to dodge a name clash (both define
`normEDS`, `complEDS`, etc.). The fork is an *engineering workaround for a naming
collision in a forked EDS file*, not a mathematical contribution. Mathlib needs nothing
from this declaration.

**WHY not (refactor-actionable):**
Mathlib has it identically as `WeierstrassCurve.map_ψ₂`. The project decl follows in
0 lines — it *is* the mathlib lemma:
```lean
example {R S} [CommRing R] [CommRing S] (W : WeierstrassCurve R) (f : R →+* S) :
    (W.map f).ψ₂ = W.ψ₂.map (Polynomial.mapRingHom f) := WeierstrassCurve.map_ψ₂
```

Existing mathlib decl:  `WeierstrassCurve.map_ψ₂`
Located at:             `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean:498`
Call sites in our project (Phase 6.0):  K = 2 external (DivisionPolynomialOmega.lean:113, ZSMul.lean:89) + 1 in-file (DivisionPolynomial.lean:477).

**Refactor plan.** This decl cannot be deleted in isolation — it is one lemma in a
whole forked file (`LutzNagell/DivisionPolynomial.lean`) whose entire reason to exist
is the EDS-namespace clash. The correct refactor is at the *file/project* grain, not
the single-lemma grain:
1. Resolve the upstream cause: reconcile `LutzNagell.EllipticDivisibilitySequence`
   with `Mathlib.NumberTheory.EllipticDivisibilitySequence` (the `normEDS`/`complEDS`
   duplication the header cites). The project's own `General*/PID*` dedup tracks are
   the place for this.
2. Once the EDS fork is gone, drop the forked `DivisionPolynomial.lean` entirely and
   `import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic`.
3. The 3 call sites (`DivisionPolynomialOmega.lean:113`, `ZSMul.lean:89`,
   `DivisionPolynomial.lean:477`) then resolve against mathlib's `map_ψ₂` with no
   edit — the name, signature, and `@[simp]` behaviour are identical, so the simp
   sets and `rw [← map_ψ₂, …]` calls are unchanged.

**Next action:** do NOT open a mathlib PR. Track this under the project's
fork-deduplication effort: eliminate the EDS namespace clash, then delete the forked
`DivisionPolynomial.lean` so all of `map_ψ₂`, `map_Ψ₃`, `map_preΨ₄`, … come from
mathlib directly. This single lemma is just one symptom of the whole-file fork.

---

## Next step

Do not open a mathlib PR. Resolve the `LutzNagell.EllipticDivisibilitySequence` vs.
`Mathlib.NumberTheory.EllipticDivisibilitySequence` naming clash (the project's
dedup track), then delete the forked `LutzNagell/DivisionPolynomial.lean` and import
mathlib's `DivisionPolynomial.Basic` directly; the 3 in-project call sites need no
change because mathlib's `WeierstrassCurve.map_ψ₂` is identical.
