# Inventory: PadicLFunctions/Interpolation/GenBernoulliComplex.lean

File: `/Users/mcu22seu/Documents/GitHub/aintlib-main/projects/PadicLFunctions/PadicLFunctions/Interpolation/GenBernoulliComplex.lean`

Namespace: `PadicLFunctions` (opens `DirichletCharacter`).

Imports (mathlib): `Mathlib.NumberTheory.LSeries.DirichletContinuation`, `Mathlib.NumberTheory.LSeries.HurwitzZetaValues`.
Imports (project): `PadicLFunctions.Interpolation.GenBernoulli`, `PadicLFunctions.Interpolation.Sawtooth`.

---

### theorem LFunction_neg_nat
- Type: `{N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (k : ℕ) : LFunction χ (-(k : ℂ)) = -(χ.genBernoulli (k + 1)) / (k + 1)`
- What: The analytically-continued Dirichlet L-function of a complex Dirichlet character `χ` mod `N`, evaluated at the negative integer `-k`, equals `-B_{k+1,χ}/(k+1)` where `B_{k+1,χ}` is the generalised Bernoulli number (`χ.genBernoulli (k+1)`). This is the §5 complex bridge identifying mathlib's L-function with the generalised Bernoulli values used by the p-adic statements (classical Washington Thm 4.2).
- How: Case split on whether `N = 1`. Level one: rewrites `χ = 1` (`DirichletCharacter.level_one`), reduces `LFunction` to `riemannZeta` (`LFunction_modOne_eq`), and uses `riemannZeta_neg_nat_eq_bernoulli'` together with `genBernoulli_one` plus algebra-map/cast manipulation. Level `N > 1`: expands `LFunction`/`ZMod.LFunction` into a sum of Hurwitz zeta values, and for each nonzero `j` uses `hurwitzZeta_neg_nat_of_mem_Ioo` (the Sawtooth boundary value valid on the open interval `(0,1)`) to write each term via the evaluated Bernoulli polynomial; the term at `j = 0` vanishes because `χ(0) = 0` (`χ.map_nonunit not_isUnit_zero`). Then rewrites the generalised Bernoulli number as a `ZMod` sum (`genBernoulli_eq_zmod_sum`) and matches term-by-term via `eq_div_iff` and `field_simp`.
- Hypotheses: `N` a natural number with `NeZero N` (so `N ≥ 1`); `χ` a complex-valued Dirichlet character mod `N`; `k` a natural number. The level-`N>1` branch additionally derives `Fact (1 < N)`, the vanishing `χ(0) = 0`, and positivity `0 < (N : ℝ)`; each nonzero residue `j` gives `0 < j.val/N < 1`.
- Uses from project: `genBernoulli_one`, `genBernoulli_eq_zmod_sum`, `hurwitzZeta_neg_nat_of_mem_Ioo`.
- Used by: unused in file
- Visibility: public
- Lines: 33–73 (decl spans 35–73); proof length ~38 lines (lines 36–73)
- Notes: long(30-50) — proof is roughly 38 lines, under 50 so no /decompose-proof required but flagged. No `set_option`, `sorry`, or `TODO`.

---

## File Summary

- Total declarations: 1 (defs: 0 / lemmas+theorems: 1 / instances: 0).
- Key API (used by ≥3 in file): none (single declaration; nothing is cross-referenced internally).
- Unused in file: `LFunction_neg_nat` (it is the file's only, terminal, export — no internal consumer).
- Declarations with `sorry`: none.
- `set_option`: none.
- Proofs >50 lines: none (0).
- Proofs 30–50 lines: 1 — `LFunction_neg_nat` (~38 lines).
