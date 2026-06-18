# T-IV-5-001: log_F(T) = ∫ ω(T)

**Status**: REVIEW
**Silverman**: IV.5 (definition)
**Module**: `HasseWeil/FormalGroup/Logarithm.lean`
**Owner**: worker-G
**Checked out at**: 2026-04-17T18:45Z
**Estimated lines**: 60
**Difficulty**: medium
**Stream**: D

## Depends on
- T-IV-4-003 (normalized differential)
- (R must be ℚ-algebra, or characteristic 0)

## Blocks
- T-IV-5-002 (exp_F)
- T-IV-5-003 (log iso to Ĝ_a)

## Statement (Silverman IV.5 def)
Let `R` be a torsion-free `ℤ`-algebra (e.g., `ℚ`-algebra). Define
`log_F(T) := ∫₀^T ω_F(s) ds = T + (b₂/2) T² + (b₃/3) T³ + ...`,
where `ω_F(T) = (1 + b₁ T + b₂ T² + ...) dT` is the normalized differential.

## Acceptance criteria

```lean
namespace HasseWeil.FormalGroup

/-- The formal logarithm of a formal group (in characteristic 0).
    Reference: Silverman IV.5. -/
noncomputable def FormalGroup.log (F : FormalGroup R) [Module ℚ R] :
    PowerSeries R

theorem FormalGroup.log_coeff (F : FormalGroup R) [Module ℚ R] (n : ℕ) :
    (F.log.coeff R (n + 1)) = ((F.normalizedDifferential.toSeries.coeff R n) : ℚ) / (n + 1)

end HasseWeil.FormalGroup
```

## Progress log
- 2026-04-17T18:45Z [worker-G] Checkout. Plan: define `FormalGroup.log` under
  `[Module ℚ R]` by the explicit coefficient formula
  `coeff (n+1) (log F) = ((n+1 : ℚ)⁻¹) • coeff n ω_F` (integral of the
  normalized invariant differential ω_F = F_X(0,T)⁻¹).
- 2026-04-17T19:00Z [worker-G] DONE. New file `HasseWeil/FormalGroup/Logarithm.lean`
  (~90 lines) provides:
  * `FormalGroup.log F : PowerSeries R` under `[Module ℚ R]`
  * `FormalGroup.log_coeff_succ`, `log_coeff_zero`, `log_constantCoeff`,
    `log_coeff_one` — all with `@[simp]` where appropriate.
  Definition matches the ticket's acceptance statement (simplified away the
  cast to ℚ in the denominator — we smul by the ℚ-scalar `(n+1 : ℚ)⁻¹` which
  cleanly lives in the `Module ℚ R` API).
  Axiom-clean: `propext, Classical.choice, Quot.sound` only.
  Full `lake build` passes.
