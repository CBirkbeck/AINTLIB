# T-W7.0c (lane P1) — Bosma–Lenstra second addition law: derived + certified (2026-07-07)

**Status: CAS layer COMPLETE; Lean file not yet written.** Everything a worker needs to write
`ModularCurves/EllipticCurve/AdditionLaw.lean` mechanically is in this directory.

## What was established

Mathlib's `WeierstrassCurve.Projective.addX/addY/addZ` **is** B–L law (1) (the law of the line
`Z = 0`), up to the global sign `law1_printed = −(addX, addY, addZ)` — verified exactly,
term-by-term. So lane P1 only needs law (2) (the line `Y = 0`, the law that covers the diagonal);
mathlib's `dblXYZ` is unary and is NOT a substitute.

Law (2) was **derived, not transcribed**: solved exactly (mod-p interpolation over the
weight-graded (2,2)-monomial basis, then integer lift) from the paper's own anchor
`law2_i = s*(Y/Z)·law1_i` (B–L p. 237), with `s*(X/Z), s*(Y/Z), κ, μ, f, g` (p. 236) validated
numerically against an independent chord–tangent implementation. Result certified by the exact
ideal identity `d³Z₁Z₂·law2_i ≡ N_Y·law1_i mod (F₁, F₂)` and by end-to-end numeric group-law
checks (generic pairs + diagonal doubling). Term counts: X 56, Y 74, Z 43; |coeff| ≤ 12.

## Files (all polynomial text in mathlib-Lean syntax, `P x`/`Q z`/`W'.a₁` conventions)

- `dblAddX.txt`, `dblAddY.txt`, `dblAddZ.txt` — the law-2 triple (suggested Lean names;
  "the addition law that extends doubling"). Bidegree (2,2), bihomogeneous.
- `cof_MXY_P/Q.txt`, `cof_MXZ_P/Q.txt`, `cof_MYZ_P/Q.txt` — cofactors (A, B) for the three
  cross-law minors, e.g. `addX·dblAddY − addY·dblAddX = A·(eqn P) + B·(eqn Q)` — i.e.
  `linear_combination A * hP + B * hQ` after `rw [equation_iff]`. Sizes 45–110 terms (Y-first
  reduction; the X-first ones are ~2× bigger). These give T-W7.0c(c3) per coordinate.
- `cof_diag_dblAdd{X,Y,Z}.txt` — cofactors E with `dblAdd_(P,P) − dbl_(P) = E·(eqn P)`:
  **the diagonal of law 2 IS mathlib's `dblXYZ`, sign +1**, with 3–13-term cofactors.
- `cof_I1_P/Q.txt` — cofactors for `equation_addXYZ` (law 1 lands on the curve, over ANY ring;
  absent from mathlib, which only has the field-level route). 422/584 terms — big but plausibly
  within default heartbeats; test before committing to it.
- `law2_derived.json` — machine-readable law 2 (exponent vector `X1 Y1 Z1 X2 Y2 Z2 a1 a2 a3 a4 a6`
  → coefficient).
- `derive_law2.py` — regenerates and re-verifies everything (path to mathlib's
  `Projective/Formula.lean` is hardcoded at the top; adjust after big refactors). Also computes
  the two certificates NOT stored here (too big, regenerable):
  - **I2** `F(law2) ∈ (F₁,F₂)` (on-curve for law 2, = c5): cofactors ≈ 3.9–7.8k terms in every
    reduction order tried; the raw expansion of `F(law2)` is 20 254 monomials. **A single
    `linear_combination` is NOT viable under the no-`maxHeartbeats` bar.** Route options, in
    recommended order: (1) the generic-point engine — once P2's 0e/0f land, `Equation (dblAdd…)`
    over the integral universal atlas follows from the field case at η (mathlib's
    `nonsingular_add` route), then instantiates to every ring with Δ inverted (all downstream
    uses carry `[W.IsElliptic]`); (2) chart-local saturated forms; (3) a chunked certificate.
  - anchor cofactors (61–238 terms) if one prefers to state the anchor identity in Lean.

## Extra structure worth stating in the Lean file (all verified)

- O-columns: `dblAdd_i((0,Y₁,0), Q) = Y₁² · (row_i of (a₁Qx + Qy + a₃Qz)·(Qx,Qy,Qz))`, i.e. the
  left-O column is the common scalar `(a₁ Q x + Q y + a₃ Q z)`(-weighted) times `Q`;
  `dblAdd_i(P, (0,Y₂,0)) = Y₂² · (P x·P y, P y², P y·P z)_i = Y₂²·P y·(P x, P y, P z)_i`. Both
  compute `O + Q = Q`, `P + O = P` projectively, no curve hypothesis needed — plain `ring`.
- Scaling: `dblAdd (u•P) (v•Q) = (uv)²·dblAdd P Q` (bidegree; plain `ring` per coordinate).
- law 2 is NOT symmetric as a polynomial triple (only projectively, via the minors).
- Covering (c2 core, field case): if `P ≈ Q` then `dblAddXYZ P Q = u²·dblXYZ Q ≠ 0` for
  nonsingular Q (smul + diagonal + mathlib's dbl-nonvanishing pieces); if `¬(P ≈ Q)` mathlib's
  `addZ_ne_zero_of_X_ne` / `addU_ne_zero_of_Y_ne` give a nonvanishing law-1 coordinate.

## Paper-fidelity note (for `tw7-source-quotes.md` discipline)

One line of the printed `X₃⁽²⁾` (B–L p. 237) reads, in the derived (true) polynomial, as
`− a₃a₄(2X₁Z₂ + X₂Z₁)X₂Z₁`; an eyeball transcription had misread it as
`+ a₃a₄(X₁Z₂ − 2X₂Z₁)X₂Z₁`. The derivation is order-of-magnitude overdetermined (exact anchor
identity + 25 fresh random end-to-end samples), so the stored polynomials are authoritative
independently of anyone's reading of the printed page.
