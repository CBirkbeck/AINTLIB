# /mathlibable report — `WeierstrassCurve.C_Ψ₂Sq`

**Verdict: `NO-mathlib-has-it`** — the declaration is a byte-for-byte fork of an existing mathlib lemma (`Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean:120`). The project module's own header says so explicitly; Phase 5 confirms an exact statement/proof match. The verdict resolves at Phase 0/Phase 5 without needing the literature sweep.

---

### Baseline (Phase 0)
- lake build:               not run (local build is stale per task brief; reasoned from source — the decl elaborates verbatim in mathlib, see Phase 5)
- decl `WeierstrassCurve.C_Ψ₂Sq`: ✓ resolved at `projects/NagellLutz/LutzNagell/DivisionPolynomial.lean:43`
- kind:                      lemma
- has sorry:                 no
- module docstring summary:  "This is a copy of `Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic` that imports `LutzNagell.EllipticDivisibilitySequence` instead of the mathlib version, to avoid name conflicts (both define `normEDS`, `complEDS`, etc.). See the original file for full documentation."

Qualified name confirmed `WeierstrassCurve.C_Ψ₂Sq`: the file opens `namespace WeierstrassCurve` at line 27 with no intervening `end`, and line 43 declares `lemma C_Ψ₂Sq`. The project file's header (lines 12-16) declares the whole module to be a copy of the mathlib file, forked only to swap one import — that alone settles the mathlibable question; the remaining phases confirm it.

---

### Statement (Phase 1)

`WeierstrassCurve.C_Ψ₂Sq` is a lemma stating that, for a Weierstrass curve `W` over a commutative ring `R`, the constant-coefficient embedding into `R[X][Y]` of the univariate polynomial `Ψ₂Sq` equals the square of the 2-division polynomial `ψ₂` minus four times the curve's defining bivariate polynomial:

$$C(\Psi_2\mathrm{Sq}) = \psi_2^2 - 4\,f_W$$

where `Ψ₂Sq = 4X³ + b₂X² + 2b₄X + b₆`, `ψ₂ = W.toAffine.polynomialY` (the formal `∂/∂Y` of the curve equation), and `f_W = W.toAffine.polynomial` is the Weierstrass cubic `Y² + a₁XY + a₃Y − (X³ + a₂X² + a₄X + a₆)`. The identity packages the standard congruence `ψ₂² ≡ Ψ₂Sq (mod f_W)` — i.e. the genuinely-squared 2-division polynomial is congruent to the univariate `Ψ₂Sq` modulo the curve relation — as an exact equation in `R[X][Y]`.

Variables / typeclasses (Lean side):
- `{R : Type r} [CommRing R]` — the base ring.
- `(W : WeierstrassCurve R)` — the Weierstrass curve.

Hypotheses: none beyond the above.

Conclusion (math): `C(Ψ₂Sq) = ψ₂² − 4·f_W` in `R[X][Y]`.
Conclusion (Lean): `C W.Ψ₂Sq = W.ψ₂ ^ 2 - 4 * W.toAffine.polynomial`.

---

### Size classification (Phase 2a)

Verdict: SMALL
Reason: a helper identity in the division-polynomial API relating `Ψ₂Sq` to `ψ₂²` via the curve relation; not a named theorem, not a project main result, not a new structure.

(Note: literature width is normally EXHAUSTIVE. Here it is moot — see Phase 3 override — because the declaration is a verbatim fork of an existing mathlib declaration, so the standard-form / generality question is already settled by the fact that the *source is mathlib*.)

### One-line check (Phase 2b)

Body line count: 3 substantive lines (`rw [...]`, `C_simp`, `ring1`).
One-liner verdict: n/a (kind is lemma, not def). Check skipped.

---

### Literature search (Phase 3) — OVERRIDE

The standard nine-channel exhaustive protocol is deliberately **short-circuited**, and this is justified rather than a skip: the target is a **verbatim copy of an existing mathlib declaration** (proven in Phase 5 — same namespace, same statement, same proof, same surrounding `Ψ₂Sq`/`ψ₂` definitions at mathlib `DivisionPolynomial/Basic.lean:120`). The literature phase exists to establish the standard mathematical form and its maximal generality so we can judge a *novel* contribution. When the declaration's own module docstring states it is a copy of a specific mathlib file, and Phase 5 confirms an exact match, the standard-form question is answered definitively: the form already vetted and merged into mathlib *is* the reference form. No literature channel could move a `NO-mathlib-has-it` verdict to any other bucket.

Concept identified as: the relation `ψ₂² ≡ Ψ₂Sq (mod f_W)` in the theory of division polynomials of elliptic / Weierstrass curves (the Angdinata mathlib formalisation; cf. standard references — Silverman, *The Arithmetic of Elliptic Curves*, Ch. III; Washington, *Elliptic Curves*, on division polynomials). The mathematics is entirely standard and mathlib has formalised it.

---

### Generality analysis (Phase 4)

Literature-standard form: an identity over an arbitrary commutative ring `R` — the most general setting in which the Weierstrass model and its division polynomials are defined.

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason |
|---|---|---|---|---|---|
| 1 | `[CommRing R]` | commutative ring | commutative ring | NO | already maximal — division polynomials are defined over any `CommRing`; mathlib uses the identical typeclass. |

Generality verdict (Phase 4b): MAXIMALLY GENERAL. The project form is identical to the mathlib form over `[CommRing R]`; nothing to weaken. K = 0 weakening opportunities.

Modern-idiom check (Phase 4c): no modernisation move available — the declaration is already the mathlib-idiomatic form (it is literally the mathlib declaration). Every row is `no`: this is a concrete polynomial identity over a commutative ring, with no typeclass / filter / universal-property / substructure / categorical / index axis to abstract that mathlib has not already chosen.

### Diamond / defeq risk (Phase 4.5)

n/a — declaration kind is `lemma` (introduces no definitional equalities or typeclass-search paths).

---

### Mathlib search-status: `WeierstrassCurve.C_Ψ₂Sq` (Phase 5)

[A] Lean-Finder       — n/a: direct source match already found, dispositive.
[B] Loogle            — n/a: direct source match already found, dispositive.
[C] LeanSearch        — n/a: direct source match already found, dispositive.
[D] Grep mathlib src  `grep -rn "C_Ψ₂Sq" .lake/packages/mathlib/Mathlib/` → **HIT**: `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean:120`.
[E] Name pattern      qualified name `WeierstrassCurve.C_Ψ₂Sq` → HIT at the same location (file is inside `namespace WeierstrassCurve`).

Searched for both the user's current form and the literature-standard form — they are the same form, and both are present.

Direct comparison (project `DivisionPolynomial.lean:39-43` vs mathlib `Basic.lean:116-123`) — byte-identical:

```
-- mathlib Basic.lean:116-123
/-- The univariate polynomial `Ψ₂Sq` congruent to `ψ₂²`. -/
noncomputable def Ψ₂Sq : R[X] :=
  C 4 * X ^ 3 + C W.b₂ * X ^ 2 + C (2 * W.b₄) * X + C W.b₆

lemma C_Ψ₂Sq : C W.Ψ₂Sq = W.ψ₂ ^ 2 - 4 * W.toAffine.polynomial := by
  rw [Ψ₂Sq, ψ₂, b₂, b₄, b₆, Affine.polynomialY, Affine.polynomial]
  C_simp
  ring1
```

The referenced `Ψ₂Sq` and `ψ₂` definitions are *also* byte-identical between the two files, so the two `C_Ψ₂Sq` statements denote the same objects. Statement, proof, and dependencies all match.

Concluded: **found in mathlib as `WeierstrassCurve.C_Ψ₂Sq`; identical form** (at `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean:120`).

---

### Composition check (Phase 6)

#### Call sites — `WeierstrassCurve.C_Ψ₂Sq`

Internal use count (outside the declaring file): **0**.
External-to-file callers: 0 distinct files.

| Caller file:line | Usage pattern (one-line excerpt) |
|---|---|
| `projects/NagellLutz/LutzNagell/DivisionPolynomial.lean:49` | `simp [C_Ψ₂Sq]` (declaring file — not counted) |
| `projects/NagellLutz/LutzNagell/DivisionPolynomial.lean:52` | `simp [C_Ψ₂Sq]` (declaring file) |
| `projects/NagellLutz/LutzNagell/DivisionPolynomial.lean:259` | `... <;> rw [C_Ψ₂Sq] <;> ring1` (declaring file) |

All three uses live in the declaring file itself; no consumer outside `DivisionPolynomial.lean` references it. The project does **not** import `Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic` (it re-implements the entire file locally to swap `normEDS`/`complEDS` for the `LutzNagell.EllipticDivisibilitySequence` versions and dodge the name clash). So the mathlib `C_Ψ₂Sq` is invisible to this project not because the lemma is novel but because the *whole module* was forked.

Inline-derivation grep: the identity is re-derived nowhere else; it is used as-is within the fork.

Composition: n/a — mathlib does not merely have building blocks, it has the **exact declaration**. No composition needed.

Conclusion: moot — the result is already in mathlib verbatim.

---

## Verdict: `WeierstrassCurve.C_Ψ₂Sq`

**Category:** NO-mathlib-has-it

**Evidence:**
- Literature search (Phase 3): override — declaration is a verbatim fork of a merged mathlib decl, so the standard form is settled by mathlib itself.
- Generality analysis (Phase 4): MAXIMALLY GENERAL; identical to the mathlib form over `[CommRing R]`; no modernisation available.
- Mathlib search (Phase 5): found in mathlib as `WeierstrassCurve.C_Ψ₂Sq`; identical form; `DivisionPolynomial/Basic.lean:120`.
- Composition check (Phase 6): moot — exact declaration present in mathlib; 0 external call sites; project does not import the mathlib module.

**Rationale:**

This declaration is a byte-for-byte copy of `WeierstrassCurve.C_Ψ₂Sq` from `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean:120` — same namespace, same `[CommRing R] (W : WeierstrassCurve R)` signature, same statement `C W.Ψ₂Sq = W.ψ₂ ^ 2 - 4 * W.toAffine.polynomial`, same three-line `rw … / C_simp / ring1` proof, and the `Ψ₂Sq`/`ψ₂` definitions it depends on are themselves identical between the two files. The project's own module docstring (lines 12-16) states outright that the file is "a copy of `Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic`" forked solely so it can import `LutzNagell.EllipticDivisibilitySequence` instead of mathlib's EDS module and thereby avoid the `normEDS`/`complEDS` name collisions. The result is therefore not a mathlib candidate — it *is* mathlib, re-typed.

**WHY not (refactor-actionable):**
Mathlib already has this exact lemma. The reason it is duplicated locally is structural, not mathematical: the entire `DivisionPolynomial` module was forked to break a name clash with the project's local `EllipticDivisibilitySequence` (which itself shadows `Mathlib.NumberTheory.EllipticDivisibilitySequence`). So the right fix is not at the single-declaration grain — it is to retire the whole fork.

Existing mathlib decl:        `WeierstrassCurve.C_Ψ₂Sq`
Located at:                   `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean:120`
Our form follows in ≤1 line:  it *is* the mathlib statement verbatim — `example : C W.Ψ₂Sq = W.ψ₂ ^ 2 - 4 * W.toAffine.polynomial := W.C_Ψ₂Sq` once the mathlib module is imported and the EDS name clash is resolved.

Call sites in our project (from Phase 6.0): K = 0 outside the declaring file; 3 inside it (lines 49, 52, 259).

Refactor plan (project-level — the correct grain for a forked file):
1. Resolve the root cause of the fork: the local `LutzNagell.EllipticDivisibilitySequence` shadows `Mathlib.NumberTheory.EllipticDivisibilitySequence`. Either (a) upstream the project's EDS extensions into mathlib's EDS module / a non-conflicting namespace, or (b) `open`-qualify so both can coexist. This is the blocker that forced the `DivisionPolynomial` copy in the first place.
2. Once the EDS clash is gone, **delete the entire `projects/NagellLutz/LutzNagell/DivisionPolynomial.lean` fork** and replace it with `import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic`. All of `C_Ψ₂Sq`, `Ψ₂Sq`, `ψ₂`, `preΨ`, `ΨSq`, `Ψ`, `Φ`, `ψ`, `φ`, and the `map_*`/`baseChange_*` lemmas come back from mathlib unchanged.
3. The 3 in-file uses (lines 49, 52, 259) disappear with the fork; downstream NagellLutz files that referenced these resolve against the mathlib declarations of the same name (identical signatures, so no call-site edits beyond the import swap).

Because this is one decl inside a wholesale fork, the actionable unit is "drop the fork after fixing the EDS name conflict," not "rewrite three `simp`/`rw` lines." The same `NO-mathlib-has-it` verdict applies to every other public declaration in this file.

**Next action:** do not contribute to mathlib (it is already there). Project-side, file/track a ticket to retire the `LutzNagell/DivisionPolynomial.lean` fork by resolving the `EllipticDivisibilitySequence` name conflict and re-importing the mathlib module; then delete this duplicate.

---

## Next step

This declaration is already in mathlib verbatim — no PR. Project-side, retire the forked `DivisionPolynomial.lean` once the `EllipticDivisibilitySequence` name clash that motivated the fork is resolved, then re-import `Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic`.
