# T-III-4-004: Hom(E₁, E₂) is torsion-free

**Status**: PARTIAL (substance via degree form; typeclass form blocked on Zero/SMul instances)
**Silverman**: III.4.2(b)
**Module**: `HasseWeil/Basic.lean`
**Owner**: worker-A
**Checked out at**: 2026-04-10
**Estimated lines**: 40
**Difficulty**: medium
**Stream**: C

## Depends on
- T-III-4-003 ([m] ≠ 0 for m ≠ 0)

## Blocks
- T-III-4-005 (End E integral domain)

## Statement (Silverman III.4.2(b))
The abelian group `Hom(E₁, E₂)` of isogenies is torsion-free.

## Acceptance criteria

```lean
namespace HasseWeil.EC

/-- Hom(E₁, E₂) is torsion-free.
    Reference: Silverman III.4.2(b). -/
instance WeierstrassCurve.Hom.torsion_free (E₁ E₂ : WeierstrassCurve F)
    [Fact (E₁.Δ ≠ 0)] [Fact (E₂.Δ ≠ 0)] :
    NoZeroSMulDivisors ℤ (Isogeny E₁ E₂)

end HasseWeil.EC
```

## Notes
- Proof: if `m · φ = 0` for `m ≠ 0`, then `[m] ∘ φ = 0`. Since `[m] ≠ 0` and the
  composition of nonzero isogenies is nonzero (image is nontrivial), `φ = 0`.

## Progress log
- 2026-04-10 [worker-A] PARTIAL. Added the **substance** of "Hom(E₁,E₂) is
  torsion-free" to `HasseWeil/Basic.lean` in degree form:
  - `Isogeny.zsmul`: ℤ-action `m • φ = [m]_{E₂} ∘ φ`.
  - `Isogeny.zsmul_toAddMonoidHom`: point-map simp lemma.
  - `Isogeny.zsmul_apply`: `(m • φ)(P) = m • (φ P)`.
  - `Isogeny.zsmul_degree`: degree formula `= φ.degree * mulByInt(m).degree`.
  - `Isogeny.zsmul_degree_pos`: **torsion-free substance** — if φ.degree > 0
    and m ≠ 0, then (m • φ).degree > 0.
  - All five declarations axiom-clean (propext, Classical.choice, Quot.sound only).
  - Full `lake build` succeeds (2763 jobs), 0 new sorries.
  - Status: PARTIAL — the literal typeclass `NoZeroSMulDivisors ℤ (Isogeny W₁ W₂)`
    remains blocked on adding `Zero`/`SMul ℤ` instances to `Isogeny`, which requires
    either (a) a junk-valued zero isogeny (breaks `degree 0 = 0` since pullback
    gives finrank 1), or (b) the full Weierstrass addition law as an algebra
    endomorphism of K(E) (T-III-4-009 → T-III-4-016).
