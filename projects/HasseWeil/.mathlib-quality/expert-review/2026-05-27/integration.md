# Reply integration — round 4 (2026-05-27)

Reply received from the arithmetic-geometry reviewer on 2026-05-27.
Brief: ./brief.md · Reply: ./reply.md

## Interpretation summary

| # | Reviewer point | Maps to | Type | Confidence |
|---|----------------|---------|------|------------|
| 1 | **Use Route B** (base-change to K̄, descend) — shortest remaining path since the alg-closed fibre count is proved | Q1 | direct answer | high |
| 2 | Route C correct but formalization-heavy: its surjectivity IS the kernel-degree theorem (or quotient E/G / finite étale torsor); good long-term III.4 infra, not fastest now | Q1/Q3 | direct answer | high |
| 3 | Route A stays abandoned — bottoms out in the same geometric-kernel fact | Q4 | confirms | high |
| 4 | **L5 via the coordinate fixed-point lemma `a^q=a ⟺ a∈F_q`** (X^q−X has q distinct roots in K̄), then point-level cases O/affine — NOT Lang's theorem (overkill; only need fixed-locus, not surjectivity) | Q2 | direct answer + method | high |
| 5 | Architecture: MUST split alg-closed fibre count from finite-field count by an explicit descent; do not hide L5 under an alg-closed-base hypothesis | Q4/§5 | confirms hazard | high |
| 6 | Concrete 4-step plan with Lean target signatures | implementation | new guidance | high |
| 7 | Wording correction: "#ker = deg" is the *theorem being proved* (over K̄ via the proved fibre count), not "already available" | meta (brief wording) | unprompted correction | high |

## Decision

**Route B confirmed.** Route C parked as long-term III.4 infrastructure (its `deg = #ker` step is the
deep theorem). Route A (Sinf/ramification over F_q, `Sinf_exists_kernelPoint_of_primeOver`) **stays
abandoned** — do not invest further.

## Work plan applied (the reviewer's 4 steps, mapped to the decomposition leaves)

- **Step 1 = L5a** `frobenius_fixed_iff_mem_baseField` — field lemma `a^q = a ⟺ a ∈ range(K→K̄)`,
  via `X^q − X` root count (q distinct roots; derivative −1 ⟹ separable). Elementary; likely shipped
  or near-shipped in mathlib (`FiniteField` / `Polynomial.roots` of `X^q − X`).
- **Step 2 = L5b** `point_fixed_by_frobenius_iff_base_point` — point fixed-locus descent on E_{K̄},
  cases P=O and affine (x,y); reduces to Step 1 coordinatewise.
- **Step 3 = L3** `baseChange_oneSubFrobenius_eq` — concrete `(1−π)_K̄ = 1 − Frob_q` on the
  base-changed curve (point-map + pullback compatibility if isogeny-equality is too strong). The
  current construction gap; kept separate from the descent per the architecture rule.
- **Step 4 = glue** compose Steps 2+3 with the already-proved alg-closed fibre count
  `#ker((1−π)_K̄) = deg((1−π)_K̄)` ⟹ `#ker((1−π)_K̄) = #E(F_q)`, and with degree base-change
  invariance ⟹ `deg(1−π) = #E(F_q)` ⟹ V.1.3.
- **Architecture fix**: re-wire the integration lemma so the alg-closed fibre count (over E_{K̄}) and
  the finite-field point count (over E/F_q) sit on opposite sides of the descent — not in one
  mutually-exclusive `[IsAlgClosed] ∧ [Fintype Point]` hypothesis package, and on the genuine `1−π`
  (not the placeholder).

## Wording correction recorded (point 7)

Going forward, state V.1.3 as: "Over K̄, the proved separable fibre theorem gives
`#ker((1−π)_K̄) = deg((1−π)_K̄)`; the remaining finite-field step is identifying that kernel with
E(F_q)." Do not phrase `#ker = deg` as already-available over the finite field.

## Open questions remaining

None — all four questions answered directly and decisively.
