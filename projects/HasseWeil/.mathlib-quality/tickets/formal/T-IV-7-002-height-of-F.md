# T-IV-7-002: height(F) := height([p])

**Status**: REVIEW
**Silverman**: IV.7 def
**Module**: `HasseWeil/FormalGroup/Height.lean`
**Owner**: worker-G
**Checked out at**: 2026-04-17T19:05Z
**Estimated lines**: 30
**Difficulty**: easy
**Stream**: D

## Depends on
- T-IV-7-001 (height of hom)
- T-IV-2-006 ([m] formal endo)

## Blocks
- T-IV-7-003 (height applications)

## Statement (Silverman IV.7 def)
For a formal group `F` over a ring of characteristic `p`, the **height** of `F`
is `h(F) := h([p]) = h(F.mulByInt p)`.

## Acceptance criteria

```lean
namespace HasseWeil.FormalGroup

noncomputable def FormalGroup.height (F : FormalGroup R)
    (p : ℕ) (hp : p.Prime) [CharP R p] : ℕ ⊕ {⊤} :=
  (F.mulByInt p).height p hp

end HasseWeil.FormalGroup
```

## Progress log
- 2026-04-17T19:20Z [worker-G] DONE jointly with T-IV-7-001. In
  `HasseWeil/FormalGroup/Height.lean`:
  `noncomputable def FormalGroup.height (F : FormalGroup R) (p : ℕ) : ℕ∞`
  is defined as `(F.mulByNatHom p).height p`, matching the ticket's
  acceptance criterion.
  `FormalGroup.height_eq` provides the unfolding lemma.
