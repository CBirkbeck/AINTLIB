# T-III-4-020: `[m] ∘ [n] = [m·n]` as isogenies

**Status**: PARTIAL (T-III-4-020a landed; m=1 case fully closed)
**Silverman**: III.4.2 (multiplication-by-m composition)
**Module**: target `HasseWeil/EC/MulByIntComp.lean` (new); base-case
at `HasseWeil/EC/MulByIntBaseCase.lean`
**Owner**: (unassigned)
**Estimated lines**: 300-500
**Difficulty**: hard
**Stream**: C

## Depends on
- `mulByInt_pullback_x`, `mulByInt_pullback_y` (already proved in
  `HasseWeil/OmegaPullbackCoeff.lean`)
- Base-case identities `mulByInt_x_one`, `mulByInt_y_one`,
  `mulByInt_pullback_x_one`, `mulByInt_pullback_y_one`
  (`HasseWeil/EC/MulByIntBaseCase.lean`, landed 2026-04-20 by worker-J)

## Blocks
- T-III-6-006 (`[m]̂ = [m]`) — via `isogDual_mulByInt_of_comp`
- T-III-6-003, T-III-6-007, T-III-6-008 indirectly (dual chain consumption)
- Simplification of multi-step Hasse bound derivations

## Statement
For an elliptic curve `E` over a field `F` and integers `m, n : ℤ` with
`m, n, m·n ≠ 0`,
`(mulByInt E m).comp (mulByInt E n) = mulByInt E (m * n)`
as isogenies (i.e., both `pullback` and `toAddMonoidHom` components match).

## Acceptance criteria

```lean
namespace HasseWeil

theorem mulByInt_comp_eq_mul
    {F : Type*} [Field F] [DecidableEq F]
    (W : Affine F) [W.IsElliptic] (m n : ℤ)
    (hm : m ≠ 0) (hn : n ≠ 0) (hmn : m * n ≠ 0) :
    (mulByInt W m).comp (mulByInt W n) = mulByInt W (m * n)

end HasseWeil
```

## Decomposition plan

### T-III-4-020a: `[1] = id_isogeny`

Prove `(mulByInt W.toAffine 1).pullback = AlgHom.id F W.toAffine.FunctionField`.
Combined with `mulByInt_apply` giving `(mulByInt W 1).toAddMonoidHom = id`,
this gives `mulByInt W 1 = { pullback := AlgHom.id, toAddMonoidHom := id }`.

**Approach**:
1. Use `IsLocalization.ringHom_ext` on the `FractionRing` structure of
   `K(E) = Frac(CoordinateRing)` — reduces to agreement on `algebraMap R KE`.
2. Use `AdjoinRoot.algHom_ext` on `R = AdjoinRoot W.polynomial` — reduces to
   agreement on the x-generator `algebraMap (Poly F) R X` and the root
   (y-generator).
3. Each reduced equality is exactly `mulByInt_pullback_x_one` /
   `mulByInt_pullback_y_one` (already proved).

**Estimated lines**: 50-100.

### T-III-4-020b: Division polynomial composition law

The key identity: for the x-coordinate,
`Φ_m(x_n) · ψ_n² = Φ_{m·n}(x) · ψ_m(x_n)²`
in `K(E)` (with `x_n = mulByInt_x W n`, `ψ_m` evaluated via the x-substitution).

This is the composition formula `[m](·[n]·) = [m·n]` at the x-coordinate level,
expressed algebraically. Corresponding identity for y-coordinate via `ω_n` and
`ψ_n³`.

**Approach**: Silverman III.4.2's algebraic derivation. Ingredients:
- Explicit recursions for ψ_n, φ_n
- Weierstrass relation on `K(E)` to simplify
- The point-level fact that both sides represent `[m·n]·P` for generic `P`.

**Estimated lines**: 200-400 (substantial algebraic identity).

### T-III-4-020c: Integration

With T-III-4-020a (base case) and T-III-4-020b (composition formula), prove
the full `mulByInt_comp_eq_mul` by reducing AlgHom equality to agreement on
x-generator and y-generator, then invoking the composition formula.

**Estimated lines**: 50-100.

## Notes

The witness form `isogDual_mulByInt_of_comp` in `HasseWeil/DualIsogeny.lean:159`
consumes `h_comp : (mulByInt E n).comp (mulByInt E n) = mulByInt E ((mulByInt E n).degree : ℤ)`.
Once `mulByInt_comp_eq_mul` lands, `h_comp` is discharged (noting
`(mulByInt E n).degree = (n²).toNat = n² | n ≠ 0` via `mulByInt_degree` + `sq_nonneg`),
and T-III-6-006's `[m]̂ = [m]` follows.

The base-case lemmas `mulByInt_x_one`, `mulByInt_y_one`,
`mulByInt_pullback_x_one`, `mulByInt_pullback_y_one` are already available
and sufficient for T-III-4-020a.

## Progress log

- 2026-04-20 [worker-J] Created ticket. Landed four base-case lemmas in
  new `HasseWeil/EC/MulByIntBaseCase.lean` (~75 lines, axiom-hygienic)
  ready for T-III-4-020a. Full `mulByInt_comp_eq_mul` requires closing
  T-III-4-020a (~100 lines) and T-III-4-020b (~300 lines) — out of scope
  for a single session.
- 2026-04-20 [worker-J] **T-III-4-020a DONE**: `mulByInt_one_pullback_eq_id`
  proved via `AlgHom.coe_ringHom_injective` + `IsLocalization.ringHom_ext` +
  `AdjoinRoot.ringHom_ext` + `Polynomial.ringHom_ext`, each reduced subgoal
  discharged by the base-case pullback lemmas. Plus
  `mulByInt_one_comp_mulByInt_one` (`[1] ∘ [1] = [1]`) and
  `mulByInt_one_comp_eq_mulByInt_degree` (the `h_comp` hypothesis of
  `isogDual_mulByInt_of_comp` for n=1). All axiom-hygienic. The m=1 case
  of T-III-4-020 is now fully closed; general m and T-III-4-020b remain.
- 2026-04-20 [worker-J] **Added `mulByInt_pullback_unique`** (uniqueness
  framework for T-III-4-020b). Any F-algebra endomorphism of `K(E)` that
  sends `x_gen → mulByInt_x W n` and `y_gen → mulByInt_y W n` equals
  `(mulByInt W.toAffine n).pullback`. Proved via the same
  `AlgHom.coe_ringHom_injective` → `IsLocalization.ringHom_ext` →
  `AdjoinRoot.ringHom_ext` → `Polynomial.ringHom_ext` reduction chain,
  leaves handled by AlgHom commutes + per-generator hypotheses. Axiom-hygienic.
- 2026-04-20 [worker-J] **Substitution infrastructure landed** for
  T-III-4-020b. Four new axiom-clean lemmas in `MulByIntBaseCase.lean`:
  * `algHom_apply_polynomial` — for any F-AlgHom `f : K(E) → K(E)` and
    `p ∈ F[X]`, `f(algebraMap p) = eval₂ (algebraMap F) (f x) p`.
  * `mulByInt_pullback_Φ_ff` — `(mulByInt W m).pullback (Φ_ff W n) =
    eval₂ (algebraMap F) (mulByInt_x W m) (W.Φ n)`.
  * `mulByInt_pullback_ΨSq_ff` — analogous for `ΨSq_ff`.
  * `mulByInt_pullback_mulByInt_x` — `(mulByInt W m).pullback (mulByInt_x W n) =
    eval₂ (mulByInt_x W m) (W.Φ n) / eval₂ (mulByInt_x W m) (W.ΨSq n)`.

  These reduce T-III-4-020b to the **division polynomial composition identity**:
    `(W.Φ n).eval₂ (mulByInt_x W m) · (W.ΨSq (m·n)).eval₂ (x_gen) =
     (W.Φ (m·n)).eval₂ (x_gen) · (W.ΨSq n).eval₂ (mulByInt_x W m)`
  (and analogous for y-coordinate via ω, ψ³). This is the core algebraic
  theorem of Silverman III.4.2, not yet in mathlib; formalizing it still
  requires ~300-500 lines of induction on n combined with the Weierstrass
  relation and addition formula.
- 2026-04-20 [worker-J] **Dedicated session on T-III-4-020b** — created
  new `HasseWeil/EC/MulByIntComp.lean` (~200 lines) with:
  * `mulByInt_comp_mulByInt_one_right` — `[m] ∘ [1] = [m]` ✓
  * `mulByInt_one_comp_mulByInt_left` — `[1] ∘ [m] = [m]` ✓
  * `mulByInt_comp_toAddMonoidHom` — point-level `[m]∘[n] = [m*n]` ✓
  * `mulByInt_comp_eq_mul_of_pullback_witness` — pullback-level witness form
  * `mulByInt_comp_eq_mul_of_generator_witness` — generator-level witness form
    (uses `mulByInt_pullback_unique` to collapse to agreement on x_gen/y_gen)
  * `mulByInt_x_neg` — `mulByInt_x W (-n) = mulByInt_x W n` (from
    `W.Φ_neg, W.ΨSq_neg`) ✓
  * `mulByInt_pullback_x_neg_one` — `[-1].pullback sends x_gen to x_gen` ✓
  * `mulByInt_comp_pullback_x_neg_one` — **concrete instance** of
    T-III-4-020b: x-coord composition identity `(mulByInt W (-1)).pullback
    ((mulByInt W n).pullback (x_gen)) = mulByInt_x W (n·-1)` ✓

  All axiom-hygienic. The x-coord composition identity for the `[-1]·n` case
  is now CLOSED unconditionally, giving a concrete example of how the general
  identity would be proved. General case still requires the division
  polynomial composition formula (~300-500 lines). **Remains OPEN** but with
  substantial framework.
