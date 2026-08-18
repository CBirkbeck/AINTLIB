# Inventory: PadicLFunctions/Interpolation/GenBernoulli.lean

File path: `/Users/mcu22seu/Documents/GitHub/aintlib-main/projects/PadicLFunctions/PadicLFunctions/Interpolation/GenBernoulli.lean`

Namespace `PadicLFunctions`. File-level variables: `{L : Type*} [Field L] [CharZero L] {N : ℕ} [NeZero N]`.

---

### def DirichletCharacter.genBernoulli
- Type: `noncomputable def _root_.DirichletCharacter.genBernoulli (χ : DirichletCharacter L N) (k : ℕ) : L`
- What: The generalised Bernoulli number `B_{k,χ} = N^{k−1} ∑_{a=1}^{N} χ(a)·B_k(a/N)` of a Dirichlet character `χ` mod `N` valued in a characteristic-zero field `L`, given in the Bernoulli-polynomial (Washington §4.1, Prop 4.1) form.
- How: Direct definition; `(N:L)^((k:ℤ)−1)` times a `Finset.range N` sum of `χ(a+1)` against `Polynomial.eval ((a+1)/N) ((Polynomial.bernoulli k).map (algebraMap ℚ L))`. The `a`-range `range N` corresponds to indices `1..N` via the `a+1` shift.
- Hypotheses: `χ` a Dirichlet character mod `N` over a char-zero field; `k : ℕ`. Ambient `[Field L] [CharZero L] [NeZero N]`.
- Uses from project: []
- Used by: `LvalNeg`, `genBernoulli_one`, `genBernoulli_eq_zmod_sum`, `genBernoulli_eq_zero`, `genBernoulliPowerSeries_mul`
- Visibility: public (in `_root_.DirichletCharacter` namespace)
- Lines: 35–43 (def body 39–43, ~4 lines)
- Notes: none

### def LvalNeg
- Type: `noncomputable def LvalNeg (χ : DirichletCharacter L N) (k : ℕ) : L := -(χ.genBernoulli (k + 1)) / (k + 1)`
- What: The negative-integer L-value `L(χ,−k)` in its p-adic incarnation, defined as `−B_{k+1,χ}/(k+1)` (Washington Thm 4.2).
- How: Direct definition in terms of `genBernoulli (k+1)`.
- Hypotheses: `χ` a Dirichlet character mod `N`; `k : ℕ`.
- Uses from project: [`DirichletCharacter.genBernoulli`]
- Used by: unused in file
- Visibility: public
- Lines: 45–48 (body 1 line)
- Notes: none

### theorem genBernoulli_one
- Type: `theorem genBernoulli_one (k : ℕ) : (1 : DirichletCharacter L 1).genBernoulli k = (bernoulli' k : ℚ) • (1 : L)`
- What: At the trivial character mod 1, `B_{k,χ}` equals the `bernoulli'` number, since `B_k(1) = bernoulli' k`; this makes `LvalNeg` agree with §4's `zetaNeg`-route value `ζ(−k) = −B'_{k+1}/(k+1)`.
- How: Unfolds `genBernoulli`, collapses the singleton `range 1` sum, then rewrites via `Polynomial.eval_one_map` and `Polynomial.bernoulli_eval_one` (the identity `B_k(1) = bernoulli' k`), finishing with `Algebra.smul_def`.
- Hypotheses: `k : ℕ`; level `N = 1` with the trivial character.
- Uses from project: [`DirichletCharacter.genBernoulli`]
- Used by: `genBernoulli_eq_zero`
- Visibility: public
- Lines: 50–57 (proof ~3 lines)
- Notes: none

### theorem genBernoulli_eq_zmod_sum
- Type: `theorem genBernoulli_eq_zmod_sum [Fact (1 < N)] (χ : DirichletCharacter L N) (k : ℕ) : χ.genBernoulli k = (N:L)^((k:ℤ)−1) * ∑ b : ZMod N, χ b * Polynomial.eval ((b.val:L)/(N:L)) ((Polynomial.bernoulli k).map (algebraMap ℚ L))`
- What: For `N > 1`, the defining `1..N`-range sum of `genBernoulli` equals the `ZMod N`-indexed sum over all residues `b`, the boundary term `a+1 = N` vanishing through `χ(0) = 0`.
- How: Reindexes the `range N` sum along the injection `a ↦ (a+1 : ZMod N)` (proved injective via `ZMod.natCast_eq_natCast_iff'` and case analysis on `a+1 = N`), rewrites `univ` as the image (`Finset.eq_univ_of_card`, `card_image_of_injOn`, `ZMod.card`), then matches summands using `ZMod.val_natCast_of_lt` and `push_cast`/`ring_nf`; the `a+1 = N` boundary uses `ZMod.natCast_self` and `χ.map_nonunit`.
- Hypotheses: `[Fact (1 < N)]` (i.e. `N > 1`); `χ` mod `N`; `k : ℕ`.
- Uses from project: [`DirichletCharacter.genBernoulli`]
- Used by: `genBernoulli_eq_zero`
- Visibility: public
- Lines: 59–96 (proof ~26 lines)
- Notes: none

### theorem genBernoulli_eq_zero
- Type: `theorem genBernoulli_eq_zero (χ : DirichletCharacter L N) {k : ℕ} (h : χ (-1) ≠ (-1:L)^k) (hk : χ ≠ 1 ∨ k ≠ 1) : χ.genBernoulli k = 0`
- What: Parity-vanishing: `B_{k,χ} = 0` whenever `χ(−1) ≠ (−1)^k`, excluding only the degenerate trivial-character `k = 1` case; this is the `p`-adic shadow of `L(χ,−k) = 0` when `χ(−1)(−1)^k = 1`.
- How: Splits on `N = 1` vs `N ≥ 2`. Level-one case: `DirichletCharacter.level_one` forces `χ = 1`, deduces `k` odd, and applies `genBernoulli_one` with `bernoulli'_eq_zero_of_odd`. Main case sets up the `ZMod N` sum `T` and proves `T = (χ(−1)·(−1)^k)·T` via the negation bijection `Equiv.neg (ZMod N)` and the reflection identity `Polynomial.bernoulli_eval_one_sub` (mapped through `algebraMap`, lemma `hrefl`), using `ZMod.val_neg_of_ne_zero`; then `χ(−1)·(−1)^k = −1` gives `2·T = 0`, so `T = 0` by `two_ne_zero`, and `genBernoulli_eq_zmod_sum` closes it.
- Hypotheses: `χ` mod `N`; `χ(−1) ≠ (−1)^k`; and `χ ≠ 1` or `k ≠ 1`.
- Uses from project: [`DirichletCharacter.genBernoulli`, `genBernoulli_one`, `genBernoulli_eq_zmod_sum`]
- Used by: unused in file
- Visibility: public
- Lines: 98–168 (proof 107→168, ~62 lines)
- Notes: OVER-50 (needs /decompose-proof) — proof body ~62 lines.

### theorem genBernoulliPowerSeries_mul
- Type (abbrev): `theorem genBernoulliPowerSeries_mul (χ : DirichletCharacter L N) : (PowerSeries.mk fun k => χ.genBernoulli k * (k.factorial:L)⁻¹) * (rescale (N:L) (exp L) − 1) = ∑ a ∈ range N, χ (a+1) • (X * rescale ((a:L)+1) (exp L))`
- What: The cleared-denominator generating-function characterisation of `B_{k,χ}`: `(∑_k B_{k,χ} t^k/k!)·(e^{Nt}−1) = ∑_{a=1}^{N} χ(a)·t·e^{at}` in `L⟦t⟧` (Washington §4.1 defining identity), the §5 analogue of mathlib's `bernoulliPowerSeries_mul_exp_sub_one`.
- How: Cancels `C (N:L)` (nonzero via constant coefficient, `mul_left_cancel₀`). Per-`a` lemma `hper` rescales `Polynomial.bernoulli_generating_function` by `N` (using `rescale_rescale`, `rescale_X`, `div_mul_cancel₀`). Lemma `hkey` rewrites `C N · (∑ B_{k,χ}…)` coefficientwise via `coeff_C_mul`, `coeff_rescale`, `genBernoulli` and the `zpow_sub_one₀` split `N^k = N·N^{k−1}`, matching with `Polynomial.aeval_def`/`eval_map`. A `calc` chain then distributes the multiplication over the sum (`Finset.sum_mul`, `smul_mul_assoc`, `mul_smul_comm`) and substitutes `hper`.
- Hypotheses: `χ` a Dirichlet character mod `N`; ambient `[Field L] [CharZero L] [NeZero N]`.
- Uses from project: [`DirichletCharacter.genBernoulli`]
- Used by: unused in file
- Visibility: public (in `section generatingFunction`, `open PowerSeries`)
- Lines: 174–243 (proof 184→243, ~60 lines)
- Notes: OVER-50 (needs /decompose-proof) — proof body ~60 lines.

### theorem prod_primitiveRoot_mul_sub_one
- Type: `theorem prod_primitiveRoot_mul_sub_one {R : Type*} [CommRing R] [IsDomain R] {ζ : R} {M : ℕ} (hM : Odd M) (hζ : IsPrimitiveRoot ζ M) (Y : R) : ∏ c ∈ range M, (ζ^c * Y − 1) = Y^M − 1`
- What: The cyclotomic product identity `∏_{c<M} (ζ^c·Y − 1) = Y^M − 1` for `ζ` a primitive `M`-th root of unity and **odd** `M`, used to clear denominators of `F_{χ,a}` at `Y = 1+X`, `M = p^n` with `p` odd.
- How: Starts from `X_pow_sub_C_eq_prod hζ` (the factorisation `X^M − Y^M = ∏ (X − ζ^c Y)`), evaluates at `X = 1` (`congrArg (Polynomial.eval 1)`, then `eval_prod`/`eval_sub`/`eval_pow`/`eval_C`), rewrites each factor `ζ^c·Y − 1 = −(1 − ζ^c·Y)`, pulls out the sign with `Finset.prod_neg` and `card_range`, and uses oddness via `hM.neg_one_pow` to finish with `ring`. (Statement corrected from the skeleton's false unconditional form — even `M` fails at `M=2`.)
- Hypotheses: `R` a domain; `ζ` a primitive `M`-th root of unity; `M` odd; `Y : R`.
- Uses from project: []
- Used by: unused in file
- Visibility: public (in `section generatingFunction`)
- Lines: 245–261 (proof ~9 lines)
- Notes: none

---

## File Summary

- **Total declarations: 6** — defs: 2 (`DirichletCharacter.genBernoulli`, `LvalNeg`); lemmas/theorems: 4 (`genBernoulli_one`, `genBernoulli_eq_zmod_sum`, `genBernoulli_eq_zero`, `genBernoulliPowerSeries_mul`, `prod_primitiveRoot_mul_sub_one` — note this is 5 theorems, total decls 7); instances: 0.
  - Correction: **Total declarations: 7** — 2 defs + 5 theorems + 0 instances.
- **Key API (used by ≥3 decls in file):** `DirichletCharacter.genBernoulli` (used by all 5 other decls + `LvalNeg`).
- **Unused (within file):** `LvalNeg`, `genBernoulli_eq_zero`, `genBernoulliPowerSeries_mul`, `prod_primitiveRoot_mul_sub_one` (these are the file's exported API, consumed elsewhere in the project).
- **Decls with `sorry`:** none.
- **`set_option`:** none.
- **TODO/admit:** none.
- **Proofs >50 lines (OVER-50):** 2 — `genBernoulli_eq_zero` (~62 lines), `genBernoulliPowerSeries_mul` (~60 lines).
- **Proofs 30–50 lines:** 0 (`genBernoulli_eq_zmod_sum` is ~26 lines, below threshold).
