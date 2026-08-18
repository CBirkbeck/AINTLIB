# /mathlibable report — `WeierstrassCurve.Affine.CoordinateRing.mk_ψ₂_sq`

**Verdict: `NO-mathlib-has-it`** — the declaration is a byte-for-byte fork of an existing mathlib lemma (`Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean:128`): same fully-qualified name, same statement, same `simp [C_Ψ₂Sq]` proof, same author. The project module's own header says so explicitly; Phase 5 confirms an exact statement/proof match. The verdict resolves at Phase 0 / Phase 5 without needing the literature sweep.

---

### Baseline (Phase 0)
- lake build:               not run (local build is stale per task brief; reasoned from source — the decl elaborates verbatim in mathlib, see Phase 5)
- decl `WeierstrassCurve.Affine.CoordinateRing.mk_ψ₂_sq`: ✓ resolved at `projects/NagellLutz/LutzNagell/DivisionPolynomial.lean:51`
- kind:                      lemma
- has sorry:                 no
- module docstring summary:  "This is a copy of `Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic` that imports `LutzNagell.EllipticDivisibilitySequence` instead of the mathlib version, to avoid name conflicts (both define `normEDS`, `complEDS`, etc.). See the original file for full documentation."

Qualified-name verification: the file opens `namespace WeierstrassCurve` at line 27 with no intervening `end` before line 51, and line 51 declares `lemma Affine.CoordinateRing.mk_ψ₂_sq`. Concatenating the open namespace with the declared base name gives `WeierstrassCurve.Affine.CoordinateRing.mk_ψ₂_sq` — confirming the prompt's parsed name. The project file's header (lines 12-16) declares the whole module to be a copy of the mathlib file, forked only to swap one import — that alone settles the mathlibable question; the remaining phases confirm it.

---

### Statement (Phase 1)

`WeierstrassCurve.Affine.CoordinateRing.mk_ψ₂_sq` is a lemma stating that, in the affine coordinate ring `R[X][Y]/⟨W.polynomial⟩` of a Weierstrass curve `W` over a commutative ring `R`, the image under the quotient map `mk` of the *square* of the 2-division polynomial `ψ₂` equals the image of the constant-extended univariate polynomial `Ψ₂Sq`:

$$\overline{\psi_2}^{\,2} = \overline{C(\Psi_2\mathrm{Sq})} \quad\text{in } R[X][Y]/\langle f_W\rangle$$

where `ψ₂ = W.toAffine.polynomialY` (the formal `∂/∂Y` of the curve equation), `Ψ₂Sq = 4X³ + b₂X² + 2b₄X + b₆ ∈ R[X]`, and `mk = WeierstrassCurve.Affine.CoordinateRing.mk : R[X][Y] →+* W.CoordinateRing` is the canonical quotient (`AdjoinRoot`) ring homomorphism. It is the in-the-coordinate-ring shadow of the polynomial identity `C_Ψ₂Sq` (`C Ψ₂Sq = ψ₂² − 4·f_W`): passing to the quotient by `f_W = W.toAffine.polynomial` kills the `4·f_W` term, leaving `ψ₂² ≡ Ψ₂Sq`. This is the standard textbook 2-torsion relation `ψ₂² = 4x³ + b₂x² + 2b₄x + b₆` on the curve.

Variables / typeclasses (Lean side):
- `{R : Type r} [CommRing R]` — the base ring.
- `(W : WeierstrassCurve R)` — the Weierstrass curve.

Hypotheses: none beyond the above.

Conclusion (math): `mk(ψ₂)² = mk(C Ψ₂Sq)` in `W.CoordinateRing`.
Conclusion (Lean): `mk W W.ψ₂ ^ 2 = mk W (C W.Ψ₂Sq)`.

---

### Size classification (Phase 2a)

Verdict: SMALL
Reason: a helper identity in the division-polynomial API, pushing the polynomial congruence `C_Ψ₂Sq` into the coordinate ring; not a named theorem, not a project main result, not a new structure.

(Note: literature width is normally EXHAUSTIVE. Here it is moot — see Phase 3 override — because the declaration is a verbatim fork of an existing mathlib declaration, so the standard-form / generality question is already settled by the fact that the *source is mathlib*.)

### One-line check (Phase 2b)

Body line count: 1 substantive line (`simp [C_Ψ₂Sq]`).
One-liner verdict: n/a (kind is lemma, not def). Check skipped.

---

### Literature search (Phase 3) — OVERRIDE

The standard nine-channel exhaustive protocol is deliberately **short-circuited**, and this is justified rather than a skip: the target is a **verbatim copy of an existing mathlib declaration** (proven in Phase 5 — same namespace, same statement, same proof, same surrounding `Ψ₂Sq`/`ψ₂`/`mk` definitions at mathlib `DivisionPolynomial/Basic.lean:128`). The literature phase exists to establish the standard mathematical form and its maximal generality so we can judge a *novel* contribution. When the declaration's own module docstring states it is a copy of a specific mathlib file, and Phase 5 confirms an exact match, the standard-form question is answered definitively: the form already vetted and merged into mathlib *is* the reference form. No literature channel could move a `NO-mathlib-has-it` verdict to any other bucket.

Concept identified as: the relation `ψ₂² ≡ Ψ₂Sq` modulo the curve relation — i.e. `ψ₂² = 4x³ + b₂x² + 2b₄x + b₆` on a Weierstrass curve — in the theory of division polynomials of elliptic / Weierstrass curves (the Angdinata mathlib formalisation; cf. standard references — Silverman, *The Arithmetic of Elliptic Curves*, Ch. III, §3.2; Washington, *Elliptic Curves: Number Theory and Cryptography*, §3.2, on division polynomials and 2-torsion). The mathematics is entirely standard and mathlib has formalised it.

---

### Generality analysis (Phase 4)

Literature-standard form: an identity over an arbitrary commutative ring `R` — the most general setting in which the Weierstrass model, its division polynomials, and its coordinate ring are defined.

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason |
|---|---|---|---|---|---|
| 1 | `[CommRing R]` | commutative ring | commutative ring | NO | already maximal — division polynomials and the coordinate ring `AdjoinRoot W.polynomial` are defined over any `CommRing`; mathlib uses the identical typeclass. |

Generality verdict (Phase 4b): MAXIMALLY GENERAL. The project form is identical to the mathlib form over `[CommRing R]`; nothing to weaken. K = 0 weakening opportunities.

Modern-idiom check (Phase 4c): no modernisation move available — the declaration is already the mathlib-idiomatic form (it is literally the mathlib declaration, authored by the mathlib author). Every row is `no`: this is a concrete polynomial-image identity over a commutative ring, with no typeclass / filter / universal-property / substructure / categorical / index axis to abstract that mathlib has not already chosen.

### Diamond / defeq risk (Phase 4.5)

n/a — declaration kind is `lemma` (introduces no definitional equalities or typeclass-search paths).

---

### Mathlib search-status: `WeierstrassCurve.Affine.CoordinateRing.mk_ψ₂_sq` (Phase 5)

[A] Lean-Finder       — n/a: direct source match already found, dispositive.
[B] Loogle            — n/a: direct source match already found, dispositive.
[C] LeanSearch        — n/a: direct source match already found, dispositive.
[D] Grep mathlib src  `grep -rn "mk_ψ₂_sq" .lake/.../mathlib/Mathlib/` → **HIT**: `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean:128` (the definition), plus four downstream uses at `Basic.lean:351, 454, 501` (inside `mk_Ψ_sq`, `mk_ψ`, `mk_φ`).
[E] Name pattern      qualified name `WeierstrassCurve.Affine.CoordinateRing.mk_ψ₂_sq` → HIT at the same location (file is inside `namespace WeierstrassCurve`; lemma base name `Affine.CoordinateRing.mk_ψ₂_sq`).

Searched for both the user's current form and the literature-standard form — they are the same form, and both are present.

Direct comparison (project `DivisionPolynomial.lean:51-52` vs mathlib `Basic.lean:128-129`) — byte-identical:

```
-- mathlib Basic.lean:128-129
lemma Affine.CoordinateRing.mk_ψ₂_sq : mk W W.ψ₂ ^ 2 = mk W (C W.Ψ₂Sq) := by
  simp [C_Ψ₂Sq]
```
```
-- project DivisionPolynomial.lean:51-52
lemma Affine.CoordinateRing.mk_ψ₂_sq : mk W W.ψ₂ ^ 2 = mk W (C W.Ψ₂Sq) := by
  simp [C_Ψ₂Sq]
```

Every ingredient is mathlib's own, and each is itself byte-identical between the two files, so the two statements denote the same objects:
- `WeierstrassCurve.ψ₂` = `W.toAffine.polynomialY` — mathlib `Basic.lean:113`.
- `WeierstrassCurve.Ψ₂Sq` = `C 4 * X^3 + C W.b₂ * X^2 + C (2*W.b₄) * X + C W.b₆` — mathlib `Basic.lean:117`.
- `WeierstrassCurve.C_Ψ₂Sq` (the simp lemma driving the proof) — mathlib `Basic.lean:120`.
- the quotient map `WeierstrassCurve.Affine.CoordinateRing.mk : R[X][Y] →+* W.CoordinateRing` — mathlib `Affine/Point.lean:118` (an `AdjoinRoot.mk` of `W.polynomial`).

Copyright header is preserved unchanged: both files credit David Kurniadi Angdinata — the project file is a literal copy of the mathlib original by its own author.

Concluded: **found in mathlib as `WeierstrassCurve.Affine.CoordinateRing.mk_ψ₂_sq`; identical form** (at `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean:128`).

---

### Composition check (Phase 6)

#### Call sites — `WeierstrassCurve.Affine.CoordinateRing.mk_ψ₂_sq`

Internal use count (inside the declaring file): 3 — `DivisionPolynomial.lean:262, 362, 408` (in the proofs of `mk_Ψ_sq`, `mk_ψ`, `mk_φ` — the same downstream consumers as in mathlib).
External-to-file callers: **2 distinct files** (the duplicated PID / General tracks):

| Caller file:line | Usage pattern (one-line excerpt) |
|---|---|
| `projects/NagellLutz/LutzNagell/LutzNagellTheorem/PIDPrimeOrder.lean:187` | `… (Affine.CoordinateRing.mk_ψ₂_sq (W := curveK R K W))` |
| `projects/NagellLutz/LutzNagell/LutzNagellTheorem/GeneralPrimeOrder.lean:179` | `… (Affine.CoordinateRing.mk_ψ₂_sq (W := curveQ W))` |

Both external consumers reference the **project's local copy** by the unqualified `Affine.CoordinateRing.mk_ψ₂_sq` (it is the only one in scope, because the project does not import the mathlib module). They are *not* evidence of novelty: they would resolve verbatim against the mathlib declaration of the same fully-qualified name the instant the fork were dropped and the mathlib module imported (identical signature, no call-site edits beyond the import swap).

The project does **not** import `Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic` (confirmed: zero `import Mathlib.*DivisionPolynomial` lines under `projects/NagellLutz/`). It re-implements the entire file locally to swap `normEDS`/`complEDS` for the `LutzNagell.EllipticDivisibilitySequence` versions and dodge the name clash. So the mathlib `mk_ψ₂_sq` is invisible to this project not because the lemma is novel but because the *whole module* was forked.

Composition: n/a — mathlib does not merely have building blocks, it has the **exact declaration**. No composition needed.

Conclusion: moot — the result is already in mathlib verbatim.

---

## Verdict: `WeierstrassCurve.Affine.CoordinateRing.mk_ψ₂_sq`

**Category:** NO-mathlib-has-it

**Evidence:**
- Literature search (Phase 3): override — declaration is a verbatim fork of a merged mathlib decl, so the standard form is settled by mathlib itself.
- Generality analysis (Phase 4): MAXIMALLY GENERAL; identical to the mathlib form over `[CommRing R]`; no modernisation available.
- Mathlib search (Phase 5): found in mathlib as `WeierstrassCurve.Affine.CoordinateRing.mk_ψ₂_sq`; identical form; `DivisionPolynomial/Basic.lean:128`.
- Composition check (Phase 6): moot — exact declaration present in mathlib; 2 external call sites both pointing at the local copy of an identically-named mathlib lemma; project does not import the mathlib module.

**Rationale:**

This declaration is a byte-for-byte copy of `WeierstrassCurve.Affine.CoordinateRing.mk_ψ₂_sq` from `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean:128` — same namespace, same `[CommRing R] (W : WeierstrassCurve R)` signature, same statement `mk W W.ψ₂ ^ 2 = mk W (C W.Ψ₂Sq)`, same one-line `simp [C_Ψ₂Sq]` proof, and the `ψ₂` / `Ψ₂Sq` / `C_Ψ₂Sq` / `mk` it depends on are themselves identical between the two files (all mathlib's own). The project's own module docstring (lines 12-16) states outright that the file is "a copy of `Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic`" forked solely so it can import `LutzNagell.EllipticDivisibilitySequence` instead of mathlib's EDS module and thereby avoid the `normEDS`/`complEDS` name collisions. The copyright header even preserves the original mathlib author. The result is therefore not a mathlib candidate — it *is* mathlib, re-typed.

**WHY not (refactor-actionable):**
Mathlib already has this exact lemma. The reason it is duplicated locally is structural, not mathematical: the entire `DivisionPolynomial` module was forked to break a name clash with the project's local `EllipticDivisibilitySequence` (which itself shadows `Mathlib.NumberTheory.EllipticDivisibilitySequence`). So the right fix is not at the single-declaration grain — it is to retire the whole fork.

Existing mathlib decl:        `WeierstrassCurve.Affine.CoordinateRing.mk_ψ₂_sq`
Located at:                   `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean:128`
Our form follows in ≤1 line:  it *is* the mathlib statement verbatim — `example : mk W W.ψ₂ ^ 2 = mk W (C W.Ψ₂Sq) := W.Affine.CoordinateRing.mk_ψ₂_sq` once the mathlib module is imported and the EDS name clash is resolved.

Call sites in our project (from Phase 6): 3 inside the declaring file (lines 262, 362, 408); K = 2 outside it (`PIDPrimeOrder.lean:187`, `GeneralPrimeOrder.lean:179`), both pointing at the local copy of an identically-named mathlib lemma.

Refactor plan (project-level — the correct grain for a forked file):
1. Resolve the root cause of the fork: the local `LutzNagell.EllipticDivisibilitySequence` shadows `Mathlib.NumberTheory.EllipticDivisibilitySequence`. Either (a) upstream the project's EDS extensions into mathlib's EDS module / a non-conflicting namespace, or (b) `open`-qualify so both can coexist. This is the blocker that forced the `DivisionPolynomial` copy in the first place.
2. Once the EDS clash is gone, **delete the entire `projects/NagellLutz/LutzNagell/DivisionPolynomial.lean` fork** and replace it with `import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic`. All of `mk_ψ₂_sq`, `ψ₂`, `Ψ₂Sq`, `C_Ψ₂Sq`, `preΨ`, `ΨSq`, `Ψ`, `Φ`, `ψ`, `φ`, `mk_Ψ_sq`, `mk_ψ`, `mk_φ`, and the `map_*`/`baseChange_*` lemmas come back from mathlib unchanged.
3. The 3 in-file uses (lines 262, 362, 408) disappear with the fork; the 2 external consumers (`PIDPrimeOrder.lean:187`, `GeneralPrimeOrder.lean:179`) reference `Affine.CoordinateRing.mk_ψ₂_sq` by name and resolve against the mathlib declaration of the same name (identical signature, so no call-site edits beyond the import swap).

Because this is one decl inside a wholesale fork, the actionable unit is "drop the fork after fixing the EDS name conflict," not "rewrite one `simp` line." The same `NO-mathlib-has-it` verdict applies to every other public declaration in this file (cf. the sibling reports `C_Ψ₂Sq.md`, and the ledger rows for `mk_Ψ_sq` / `mk_ψ` / `mk_φ`).

**Next action:** do not contribute to mathlib (it is already there). Project-side, file/track a ticket to retire the `LutzNagell/DivisionPolynomial.lean` fork by resolving the `EllipticDivisibilitySequence` name conflict and re-importing the mathlib module; then delete this duplicate.

---

## Next step

This declaration is already in mathlib verbatim — no PR. Project-side, retire the forked `DivisionPolynomial.lean` once the `EllipticDivisibilitySequence` name clash that motivated the fork is resolved, then re-import `Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic`.
