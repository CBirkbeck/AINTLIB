# T-IV-5-003: torsion-free R: log_F : F → Ĝ_a iso

**Status**: DONE (general `LogPreservesAdd` closed 2026-04-20 via Silverman
IV.4.2 translation invariance; axiom-clean)
**Silverman**: IV.5.2
**Module**: `HasseWeil/FormalGroup/Logarithm.lean`
**Owner**: worker-S4
**Estimated lines**: 50 (actual: ~425 including helpers)
**Difficulty**: medium
**Stream**: D

## Depends on
- T-IV-5-001 (log_F)
- T-IV-5-002 (exp_F)
- T-IV-2-003 (Ĝ_a)

## Blocks
- T-IV-5-004 (torsion-free ⇒ commutative)
- T-IV-6-005 (log iso for large M^r)

## Statement (Silverman IV.5.2)
For a torsion-free `ℤ`-algebra `R`, the formal logarithm `log_F : F → Ĝ_a` is
an isomorphism of formal groups, with inverse `exp_F`.

## Acceptance criteria

```lean
namespace HasseWeil.FormalGroup

theorem FormalGroup.log_isHom (F : FormalGroup R) [NoZeroSMulDivisors ℤ R] [Module ℚ R] :
    F.log.subst F.formal = (additiveFormalGroup R).formal.subst (F.log, F.log)

def FormalGroup.logIso (F : FormalGroup R) [NoZeroSMulDivisors ℤ R] [Module ℚ R] :
    FormalGroupHom F (additiveFormalGroup R)

end HasseWeil.FormalGroup
```

## Notes
- Why we need ℚ-algebra (or just torsion-free + take rationalization): to define
  `b_n / (n+1)`. In char 0, `n+1` is invertible.

## Progress log
- 2026-04-18T00:10Z [worker-G/subagent] Core technical identity
  `subst_compInverse_eq_X : PowerSeries.subst (compInverse f) f = X`
  (for `constantCoeff f = 0` and `coeff 1 f = 1`) is now proved in
  `HasseWeil/FormalGroup/Logarithm.lean`. This completes the "structural
  direction" of the logarithm-inverse: `log_F ∘ exp_F = X`.
  What remains:
  * The `preserves_add` direction: showing `log_F` is a homomorphism
    (`F(X, Y) → X + Y` after log). This needs the chain-rule / Taylor
    expansion argument of Silverman IV.5 (b_n identity).
  * Packaging as a `FormalGroupHom` (log) together with the inverse
    pairing.
- 2026-04-20 [worker-G/subagent]
  Attempted to fill the `preserves_add` direction for T-IV-5-003. The full
  proof requires substantial infrastructure that has not been ported.
  Added the following scaffolding and partial results:
  * `FormalGroup.LogPreservesAdd F` — the `preserves_add` identity for `log_F`
    stated as a `Prop`: `log_F(F(X, Y)) = log_F(X) + log_F(Y)`.
  * `FormalGroup.constantCoeff_log_subst` — constant coefficient of
    `subst F.toSeries F.log` is zero.
  * `FormalGroup.constantCoeff_log_subst_X_add` — constant coefficient of
    `subst (X 0) F.log + subst (X 1) F.log` is zero.
  * `FormalGroup.logPreservesAdd_constantCoeff` — constant-coefficient case
    of `LogPreservesAdd` (both sides agree on the constant term).
  * `FormalGroup.log_additiveFormalGroup` — for `Ĝ_a`, `log = X`.
  * `FormalGroup.additiveFormalGroup_logPreservesAdd` — trivial case of
    `LogPreservesAdd` for `F = additiveFormalGroup R`.
  * `FormalGroup.logHomOfLogPreservesAdd` — given a hypothesis
    `LogPreservesAdd F`, packages `log_F` as a
    `FormalGroupHom F (additiveFormalGroup R)`. This is the bridge from
    `LogPreservesAdd F` (the target identity) to the formal-group
    homomorphism structure, completing the "packaging" part of the
    acceptance criterion.
  * `FormalGroup.additiveFormalGroup_logHom` — the packaged log hom for
    `Ĝ_a`, i.e., the identity as a formal group hom on `Ĝ_a`.
  Build: `lake build HasseWeil.FormalGroup.Logarithm` passes.
  Axioms: only standard (`propext`, `Classical.choice`, `Quot.sound`).
  Obstacle: the full `LogPreservesAdd F` for general `F` requires
  Silverman Prop. IV.4.2 translation invariance
  `ω_F(F(T, S)) · F_T(T, S) = ω_F(T)`. This bivariate translation-invariance
  identity for the normalized invariant differential is not yet in the
  codebase and is itself a substantial result (cf. `T-IV-4-002`,
  `Differential.lean`). Once `ω_F` translation invariance is proved,
  `LogPreservesAdd F` follows by differentiating
  `log_F(F(X, Y)) - log_F(X) - log_F(Y)` with respect to `X` and using
  `log_F' = ω_F` + translation invariance + `log_F(0) = 0`.
  Status remains **PARTIAL**.
- 2026-04-20 [worker-S4] **DONE**. Closed `FormalGroup.logPreservesAdd` for
  general `F` using the newly-delivered Silverman IV.4.2
  (`FormalGroup.invariantDiff_translation`). Proof strategy:
  * New lemma `FormalGroup.pderiv_log : pderiv () F.log = F.invariantDiff`
    (univariate derivative of log equals the invariant differential; cancels
    the `(n+1)⁻¹` from `log_coeff_succ` via `Module ℚ R` torsion-freeness).
  * `pderiv_PowerSeries_subst` (chain rule specialisation for
    `PowerSeries.subst` via `MvPowerSeries.pderiv_subst`).
  * `pderiv_LogPreservesAdd_LHS` and `_RHS`: both have derivative
    `subst (X 0) F.invariantDiff` after applying the chain rule and IV.4.2.
  * `subst_zero_LogPreservesAdd_LHS` and `_RHS`: substituting `X 0 ↦ 0`
    gives `subst (X 1) F.log` on both sides (LHS uses `F.runit`; RHS uses
    `PowerSeries_subst_zero_of_constantCoeff_zero` + `log_constantCoeff`).
  * Uniqueness (`eq_zero_of_pderiv_zero_and_const_zero`): a bivariate series
    with zero derivative in variable 0 and zero coefficients at
    `single 1 b` is the zero series. Uses `IsAddTorsionFree.of_module_rat`
    to cancel `nsmul`.
  * `coeff_subst_zero_X1_at_single_1`: the `subst ![0, X 1]` operation
    preserves coefficients at `single 1 b` (direct finsum computation).
  Build: `lake build HasseWeil` passes. Axioms: `[propext, Classical.choice,
  Quot.sound]` only. Lines added: ~425 in `Logarithm.lean`. No new imports
  beyond `Mathlib.Algebra.Module.Rat` (for `IsAddTorsionFree.of_module_rat`).
  Status: **DONE**.
