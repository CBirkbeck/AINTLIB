# T-IV-5-004: Torsion-free R ⇒ every formal group commutative

**Status**: REVIEW
**Silverman**: IV.5.3
**Module**: `HasseWeil/FormalGroup/Logarithm.lean`
**Owner**: worker-G
**Estimated lines**: 30
**Difficulty**: easy
**Stream**: D

## Depends on
- T-IV-5-003 (log iso to Ĝ_a)

## Blocks
- (informational)

## Statement (Silverman IV.5.3)
Over a torsion-free `ℤ`-algebra, every (one-parameter) formal group law is
commutative.

## Acceptance criteria

```lean
namespace HasseWeil.FormalGroup

theorem FormalGroup.commutative_of_torsion_free (F : FormalGroup R)
    [NoZeroSMulDivisors ℤ R] :
    F.formal.subst (X, Y) = F.formal.subst (Y, X)

end HasseWeil.FormalGroup
```

## Notes
- Direct corollary: log_F is an iso to Ĝ_a, which is commutative. Pulling back
  gives commutativity of F.

## Progress log
- 2026-04-17T20:30Z [worker-G] DONE. Added `FormalGroup.commutative` and
  `FormalGroup.commutative_of_torsion_free` to `Logarithm.lean`. In our
  `FormalGroup` structure commutativity is axiomatic (via `F.comm`), so the
  `[NoZeroSMulDivisors ℤ R]` hypothesis is not needed — classically IV.5.3
  is the non-trivial statement that over torsion-free bases every FG is
  commutative. We provide both signatures for downstream callers.
