# T-IV-2-011: Formal group inverse series

**Status**: DONE (definition, basic coefficient lemmas, and functional
equation `F(T, i(T)) = 0` all complete)
**Silverman**: IV.2 (existence of inverse for formal group laws)
**Module**: `HasseWeil/FormalGroup/Inverse.lean`
**Owner**: worker-G (via subagent)
**Estimated lines**: 200 (~660 delivered total: 200 for definition + 460 for
functional equation)
**Difficulty**: medium (definition easy; full identity mirrors
`subst_compInverse_eq_X` in Logarithm.lean)
**Stream**: D

## Depends on
- T-IV-2-001 (FormalGroup definition) — DONE
- `HasseWeil.FG.fAdd`, `HasseWeil.FG.coeff_one_fAdd` — DONE
- `HasseWeil.FG.FormalGroup.coeff_10`, `coeff_01` — DONE

## Blocks
- T-IV-3-001 (F(M) abelian group structure — needs inverse for `[−1]`)
- Any downstream use of `−P` in the formal group (e.g., `[m]` for negative
  `m` extending to `ℤ`)

## Statement (Silverman IV.2, existence of inverse)
For a formal group law `F(X, Y) ∈ R[[X, Y]]` there exists a unique power
series `i(T) ∈ R[[T]]` with `constantCoeff i = 0` and `F(T, i(T)) = 0`. Its
linear coefficient is `-1`.

## Acceptance criteria (DONE in this PR)

```lean
namespace HasseWeil.FormalGroup

noncomputable def FormalGroup.inverseTrunc (F : FormalGroup R) : ℕ → PowerSeries R
noncomputable def FormalGroup.inverseCoeff (F : FormalGroup R) : ℕ → R
noncomputable def FormalGroup.inverse (F : FormalGroup R) : PowerSeries R

@[simp] theorem FormalGroup.inverse_constantCoeff (F : FormalGroup R) :
    @PowerSeries.constantCoeff R _ F.inverse = 0

@[simp] theorem FormalGroup.inverse_coeff_zero (F : FormalGroup R) :
    PowerSeries.coeff 0 F.inverse = 0

@[simp] theorem FormalGroup.inverse_coeff_one (F : FormalGroup R) :
    PowerSeries.coeff 1 F.inverse = -1

end HasseWeil.FormalGroup
```

## Full functional equation acceptance criteria (DONE)

```lean
theorem FormalGroup.fAdd_X_inverse_eq_zero (F : FormalGroup R) :
    HasseWeil.FG.fAdd F PowerSeries.X F.inverse = 0
```

**Strategy realised**: mirror the four-step argument of
`subst_compInverse_eq_X` in `HasseWeil/FormalGroup/Logarithm.lean`:

1. **Polynomial-tail decomposition of `inverseTrunc`** (DONE: see
   `coeff_inverseTrunc_succ_of_le`, `coeff_inverseTrunc_of_le`).
2. **Bivariate substitution stabilisation** (DONE: see
   `FormalGroup.coeff_fAdd_X_eq_of_coeff_eq`): if two power series agree up
   to degree `n`, then `fAdd F X -` of each agrees up to degree `n`. This
   is a bivariate analogue of `coeff_subst_eq_of_coeff_eq`, requiring a
   fresh computation using `MvPowerSeries.coeff_subst`. ~70 lines.
3. **Monomial-addition step** (DONE: see
   `FormalGroup.coeff_fAdd_X_add_monomial`): adding `C c * X^(n+1)` to the
   second argument shifts `coeff (n+1)` of `fAdd F X` by exactly `c` — the
   "+c" comes from `coeff_01 F = 1`. ~220 lines including a reusable
   `coeff_add_monomial_pow_stable` helper for stability of `(g + C c X^(n+1))^d`
   at low degrees.
4. **Core invariant** (DONE: see
   `FormalGroup.inverseTrunc_fAdd_coeff_eq_zero`): by induction,
   `coeff k (fAdd F X (inverseTrunc F n)) = 0` for every `k ≤ n`. Uses
   `fAdd_zero_right` for the base case and steps 2–3 for the inductive
   step. ~45 lines.
5. **Conclusion** (DONE: see
   `FormalGroup.fAdd_X_inverse_eq_zero`): extensional on `coeff k`,
   applying step 2 to reduce to `inverseTrunc F k` at degree `k` and then
   invoking step 4. ~20 lines.

## Key lemmas added in this PR

- `FormalGroup.coeff_fAdd_X_eq_of_coeff_eq` — bivariate substitution
  stabilisation for `fAdd F X -`.
- `FormalGroup.coeff_fAdd_X_add_monomial` — monomial-addition identity
  realising the unit-axiom `coeff_01 F = 1`.
- `FormalGroup.inverseTrunc_fAdd_coeff_eq_zero` — the core invariant.
- `FormalGroup.fAdd_X_inverse_eq_zero` — the defining identity of the
  formal inverse (**the target theorem**).

Supporting private helpers added:
- `coeff_X_pow_mul_pow_eq_of_coeff_eq` — stabilisation at the monomial
  level `X^a * g^b`.
- `coeff_add_monomial_pow_stable` — `(g + C c X^(n+1))^d` agrees with
  `g^d` below degree `n+1`.
- `coeff_X_pow_mul_add_monomial_pow` — combines the two preceding
  observations.

## Notes
- Definition mirrors `compInvTrunc` in `Logarithm.lean` very closely; the
  only difference is that the correction makes `fAdd F X -` vanish (zero)
  rather than equalling `X` (as for the compositional inverse).
- Now imports `Logarithm.lean` to reuse `coeff_add_monomial_pow_eq`,
  `monomial_pow_eq`, `coeff_pow_eq_of_coeff_eq`, `coeff_pow_eq_zero_of_gt`,
  `monomial_constantCoeff_zero` from the compositional-inverse proof.
- Axiom-clean: `propext, Classical.choice, Quot.sound` only (verified with
  `#print axioms FormalGroup.fAdd_X_inverse_eq_zero`).

## Progress log
- 2026-04-17 [worker-G/subagent-deep] Created
  `HasseWeil/FormalGroup/Inverse.lean` (~200 lines): `inverseTrunc`,
  `inverseCoeff`, `inverse` definitions; basic lemmas
  `inverse_constantCoeff`, `inverse_coeff_zero`, `inverse_coeff_one`;
  structural lemmas `coeff_inverseTrunc_succ_of_le`,
  `coeff_inverseTrunc_of_le`, `inverseTrunc_constantCoeff`,
  `inverseTrunc_hasSubst`, `inverse_hasSubst`. Full functional equation
  `F(T, i(T)) = 0` deferred.
  Imported via `HasseWeil.lean`. `lake build HasseWeil.FormalGroup.Inverse`
  passes clean. Axiom-clean.
- 2026-04-17 [worker-G/subagent-deep] Completed T-IV-2-011: added functional
  equation `FormalGroup.fAdd_X_inverse_eq_zero` and all supporting lemmas
  (~460 new lines). The proof closely mirrors `subst_compInverse_eq_X`
  from `Logarithm.lean` but requires a fresh bivariate stabilisation
  argument for `fAdd F X -`. `lake build` passes clean. Axiom-clean
  (`propext`, `Classical.choice`, `Quot.sound` only).
