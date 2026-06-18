# T-III-6-005: (φ + ψ)^ = φ̂ + ψ̂ (DUAL ADDITIVITY)

**Status**: PARTIAL (witness-parametric form landed 2026-04-22, worker-A)
**Silverman**: III.6.2(c)
**Module**: `HasseWeil/DualIsogeny.lean`
**Owner**: worker-A (partial)
**Estimated lines**: 80 (delivered ~75 witness form)
**Difficulty**: hard (CRITICAL)
**Stream**: C/E

## Depends on
- T-III-5-006 (ring hom End → K̄)
- T-III-6-003 (φ̂ ∘ φ = [deg φ])

## Blocks
- T-III-6-009 (deg quadratic form)
- T-V-1-004 (#E(F_q) = q + 1 - tr(π))
- T-V-1-006 (Hasse bound)

## Statement (Silverman III.6.2(c))
For two isogenies `φ, ψ : E₁ → E₂`,
`(φ + ψ)^ = φ̂ + ψ̂`.

## Acceptance criteria

```lean
namespace HasseWeil.EC

/-- The dual is additive on isogenies.
    Reference: Silverman III.6.2(c). -/
theorem Isogeny.dual_add (φ ψ : Isogeny E₁ E₂) :
    (φ + ψ).dual = φ.dual + ψ.dual

end HasseWeil.EC
```

## Notes
- Silverman's proof uses `Pic⁰` linearity (the pullback `φ* : Div → Div` is
  additive in the morphism, which gives `(φ+ψ)_* = φ_* + ψ_*` modulo principal
  divisors).
- Combined with T-III-6-002, this gives the result.

## Detailed Silverman III.6.2(c) proof

Silverman's proof uses the **ring homomorphism a_ : End(E) → K̄** 
(T-III-5-006) defined by the formal group pullback coefficient:
`a_φ = coeff 1 (formalIsogenySeries φ)` = leading coefficient of the formal
expansion of `φ* ω` in the local parameter.

The key fact is that `φ ↦ a_φ` is a ring homomorphism on End(E). Equivalently
(by III.5.6): `a_{φ+ψ} = a_φ + a_ψ` and `a_{φ·ψ} = a_φ · a_ψ`.

**Proof outline**:
1. Both sides `(φ + ψ)^` and `φ̂ + ψ̂` are isogenies satisfying 
   `((φ+ψ)^ + A) ∘ (φ+ψ) = [deg(φ+ψ)]` (by III.6.1) and
   `(φ̂ + ψ̂) ∘ (φ+ψ) = φ̂∘φ + φ̂∘ψ + ψ̂∘φ + ψ̂∘ψ = [deg φ] + stuff + [deg ψ]`.
2. After rearranging: `(φ+ψ)^ - (φ̂ + ψ̂)` evaluated against ω gives zero
   pullback coefficient (by linearity of a_).
3. Combined with III.5.7 (`a_φ = 0` ⇒ φ purely inseparable or zero), and the
   fact that the difference is in Hom, we conclude `(φ+ψ)^ = φ̂ + ψ̂`.

**Alternative via Pic⁰** (T-III-3-004 route):
If Pic⁰(E) ≅ E, then `φ_*` is additive in φ on `Pic⁰`:
`(φ+ψ)_* = φ_* + ψ_*` as homomorphisms `Pic⁰(E₁) → Pic⁰(E₂)`.
The dual is defined via `φ̂ = κ∘φ_*∘κ⁻¹`, and additivity follows.

## Proof dependencies

Direct route:
- T-III-6-001 (dual exists) — BLOCKED (see that ticket)
- T-III-5-006 (ring hom End → K̄) — depends on T-III-5-002 (pullback additivity)
- T-III-5-007 (kernel of a_ = inseparables) — for uniqueness

Pic⁰ route:
- T-III-3-004 (Pic⁰ ≅ E) — BLOCKED

## Progress log

- **2026-04-22** (worker-A): Witness-parametric form delivered in
  `HasseWeil/DualIsogeny.lean` (commit `48f9778`, ~75 lines).
  Two entry points:
  * `dual_add_of_trace_witnesses` — given the three integer traces
    `tα, tβ, tαβ` with `tαβ = tα + tβ` and the three pointwise
    trace identities `α + α̂ = [tα]`, `β + β̂ = [tβ]`,
    `αβ + αβ̂ = [tαβ]`, concludes `αβ̂.toAddMonoidHom =
    α̂.toAddMonoidHom + β̂.toAddMonoidHom`.
  * `dual_add_of_sum_witnesses` — single-hypothesis variant bundling
    the pointwise sum identity. Useful when traces are already packaged.
  All axiom-clean (`propext`, `Classical.choice`, `Quot.sound`).
  Consumer chain: `DegreeQuadraticForm.lean`'s `degree_quadratic_closed`
  (commit `5d89e3c`) + `isogSmulSub_degree_quadratic_closed` (commit
  `a48843b`) picks up these witnesses and closes T-III-6-009 +
  `degree_quadratic`. Unconditional form awaits T-III-5-006
  (ring hom End → K̄) — stream D's BRIDGE-001/003 chain.
