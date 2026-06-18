# T-III-5-002: (φ + ψ)* ω = φ* ω + ψ* ω

**Status**: OPEN
**Silverman**: III.5.2
**Module**: `HasseWeil/EC/InvariantDiff.lean`
**Owner**: (unassigned)
**Estimated lines**: 200
**Difficulty**: very hard (CRITICAL)
**Stream**: B/E

## Depends on
- T-III-5-001 (translation invariance)
- T-IV-BRIDGE-003 (formal addition law) — preferred path
- (Alternative: T-II-3-011 + III.3 divisor argument, more complex)

## Blocks
- T-III-5-003 ([m]*ω = mω)
- T-III-5-006 (ring hom End → K̄)
- T-III-6-005 (dual additivity)
- T-V-1-006 (Hasse bound positivity)

## Statement (Silverman III.5.2)
For any two isogenies `φ, ψ : E₁ → E₂`,
`(φ + ψ)* ω = φ* ω + ψ* ω`.

## Acceptance criteria

```lean
namespace HasseWeil.EC

/-- Pullback of the invariant differential along isogenies is additive.
    Reference: Silverman III.5.2. -/
theorem Isogeny.pullback_invariantDifferential_add
    (φ ψ : Isogeny E₁ E₂) :
    (φ + ψ).pullback E₂.invariantDifferential =
      φ.pullback E₂.invariantDifferential + ψ.pullback E₂.invariantDifferential

end HasseWeil.EC
```

## Notes
- This is THE main step in establishing that `α ↦ a_α` (T-III-5-006) is a ring
  homomorphism, which underlies the positive definiteness of degree (T-III-6-009)
  and ultimately the Hasse bound.
- Plan: avoid the III.3 divisor proof (which uses RR in places). Use the
  formal-group bridge:
  1. The formal group `F = Ê` of `E` has formal addition `F(z₁, z₂) ∈ ℤ[a_i][[z₁,z₂]]`.
  2. For an isogeny `α : E₁ → E₂`, the formal series `f_α(T)` satisfies
     `f_{α+β}(T) = F_2(f_α(T), f_β(T))` (where `F_2 = F` is the formal addition
     of `E_2`).
  3. The pullback `α* ω = f_α'(0) · ω` (T-IV-4-005 chain rule on formal groups).
  4. By the formal addition law, `f_{α+β}'(0) = f_α'(0) + f_β'(0)`.
- This requires the bridge to be in place (T-IV-BRIDGE-001..004).

## Progress log
