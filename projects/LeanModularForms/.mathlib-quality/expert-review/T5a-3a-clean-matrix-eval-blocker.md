# T5a-3a-clean — Expert Review Brief

## Summary

This brief asks for help completing `descendCosetList_action_upper_tri_clean` in `LeanModularForms/SMOObligations.lean` (line ~1117). The mathematical content is straightforward; the blocker is a Lean 4 / Mathlib technique around matrix-literal evaluation under `simp`.

## Mathematical content

For `γ' ∈ Γ_0(N/p)` with `p² ∣ N` (so `p ∣ (N/p)` and `p ∣ γ'_{1,0}`), we want to show that the matrix action

`[1, m; 0, p] · γ' = α · [1, m'; 0, p]` in `GL_2(ℝ)`

admits an explicit witness `(m' : Fin p, α ∈ Γ_0(N))`.

**Construction** (essentially Miyake p. 144 "direct calculation"; the explicit Möbius formula is derived):

Let `A, B, C, D` be the entries of `γ'`. From `p ∣ C`, we have `AD ≡ 1 mod p`, so `A` is a unit mod p.

* `m' := A⁻¹ · (B + m·D) mod p`, as `Fin p`.
* `α := !![A + m·C, α01; p·C, D - C·m']` where `α01 = (B + m·D - (A + m·C)·m') / p`. This is an integer because `p ∣ (B + m·D - A·m')` (by the Möbius equation) and `p ∣ C`.
* `α ∈ Γ_0(N)`: the bottom-left entry is `p·C = N·(C/(N/p))`, divisible by N.
* `det α = 1`: direct algebraic expansion using `AD - BC = 1` and `p · α01 = B + m·D - (A + m·C)·m'`.

## Reference cascade

* **Miyake** (*Modular Forms*, 2006), Lemma 4.5.11, p. 143–144: states the coset decomposition `Γ_0(pN) [1,0;0,p] Γ_0(N) = ⊔_v Γ_0(pN) [1,0;0,p] γ_v` with the `γ_v` described modulo `p`. The "direct calculation" producing the σ-permutation (our T5a-3a-clean) is implicit; **not spelled out**.
* **Diamond–Shurman** (*A First Course in Modular Forms*), §5.2 (p. 168–172): introduces `T_p` via the same matrix `α = [1, 0; 0, p]` with orbit reps `β_j = [1, j; 0, p]` (eq. 5.2). But DS works in the same-level Γ_1(N) context (Prop 5.2.1 / 5.2.2), going directly from the matrix reps to the **slash action and Fourier coefficients**. They **skip** the matrix-level action of `γ ∈ Γ_0(N)` on the `β_j` reps; the σ-permutation is implicit in their later argument via q-expansions, not derived as a matrix identity.

So **neither source explicitly performs the matrix calculation we need**. It's a 6-line computation any reader can do, but neither Miyake nor DS writes it down.

## Lean 4 status

All construction parts compile cleanly (full source preserved in the commit history; see lines ~1145–1290 of an earlier file revision):

- `m'` definition + h_moebius (A·m' ≡ B + m·D mod p): ✓
- `h_int_div` (p | B + m·D - (A + m·C)·m'): ✓
- α matrix + `h_det_α = 1`: ✓
- `h_α_in_Γ0` (α ∈ Γ_0(N)): ✓
- The 4 helper lemmas `hα_NN : (α : Matrix _ _ ℤ) i j = ...`: ✓

The blocker is the final matrix equation in `GL_2(ℝ)`.

## The Lean blocker

After unfolding via:
```lean
apply Units.ext
rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul,
    Matrix.GeneralLinearGroup.val_mkOfDetNeZero, ...,
    Matrix.SpecialLinearGroup.mapGL_coe_matrix, ...]
ext i j
fin_cases i <;> fin_cases j <;>
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Fin.isValue,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.head_fin_const, Matrix.SpecialLinearGroup.map_apply_coe,
    RingHom.mapMatrix_apply, Matrix.map_apply,
    Matrix.of_apply, Matrix.cons_val', Matrix.empty_val',
    Matrix.cons_val_fin_one]
```

the goal at (0, 0) is:
```
Matrix.vecCons 1 (fun i ↦ 0) ⟨0, ⋯⟩ * (algebraMap ℤ ℝ) (↑γ' 0 ⟨0, ⋯⟩) +
    Matrix.vecCons (↑↑m) (fun i ↦ ↑p) ⟨0, ⋯⟩ * (algebraMap ℤ ℝ) (↑γ' 1 ⟨0, ⋯⟩) =
  (algebraMap ℤ ℝ) (↑α ⟨0, ⋯⟩ 0) * ![1, ↑↑m'] ⟨0, ⋯⟩ +
  (algebraMap ℤ ℝ) (↑α ⟨0, ⋯⟩ 1) * ![0, ↑p] ⟨0, ⋯⟩
```

The fragments `Matrix.vecCons 1 (fun i ↦ 0) ⟨0, ⋯⟩` should reduce to `1` (and the others to `0`, `m`, `p`, etc.) but `simp only` with the cons-val lemmas **does not fire** on the `⟨0, ⋯⟩` form (a `Fin 2` value constructed via `Fin.mk`). All four entries fail closure for the same reason.

## Specific Lean question

What is the correct tactic sequence to reduce `Matrix.vecCons a v ⟨0, h⟩` (where `⟨0, h⟩ : Fin (n+1)`) to `a`, and `Matrix.vecCons a v ⟨k+1, h⟩` to `v ⟨k, _⟩`, under `simp only`?

Approaches we've tried:
- `simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.head_fin_const, Matrix.cons_val', Matrix.empty_val', Matrix.cons_val_fin_one]` — no progress on `⟨0, _⟩` form.
- `decide` — not applicable.
- Adding `Matrix.of_apply` — no change.
- Casting Fin indices first: `simp only [show (⟨0, _⟩ : Fin 2) = 0 from rfl]` — depends on `⟨0, _⟩` being recognized as `0` first.

Alternative strategies we're considering:
- Bypass `!![...]` syntax entirely; build the matrix with explicit `Matrix.of` + `Fin.cons` and prove a custom lemma for entry evaluation.
- Use `Matrix.ext` differently to avoid the `Units.ext + .val + ext i j` chain.
- Find an existing mathlib idiom for "entry-wise verification of 2x2 matrix product in GL₂ via mapGL" — the project's `T_p_lower_upper_shift` (HeckeT_n.lean:948) does something similar but in `GL (Fin 2) ℚ`, not `GL (Fin 2) ℝ`, and uses different cons-val lemmas.

## What would unblock

A single tactic line (or small sequence) that closes goals of the form:
```
Matrix.vecCons a (fun i ↦ b) ⟨0, h⟩ * x + Matrix.vecCons a' (fun i ↦ b') ⟨0, h'⟩ * y = ...
```
by reducing the `vecCons _ _ ⟨0, _⟩` to the appropriate scalar.

Once this is solved, all four entry-equations close via `push_cast; ring` (3 entries trivially, 1 entry with `linarith [hα01']`).

## Closing

This block is the smallest concrete Lean technique question we couldn't resolve. The mathematical answer is clear (Miyake p.144 + 6 lines of algebra); we need help with the Lean simp idiom for `Matrix.vecCons` indexed by `Fin.mk` values.
