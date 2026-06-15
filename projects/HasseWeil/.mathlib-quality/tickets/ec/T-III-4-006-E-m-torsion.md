# T-III-4-006: E[m] m-torsion subgroup

**Status**: DONE (definition + mem_iff; finiteness tracked in T-III-4-011)
**Silverman**: III.4 def
**Module**: `HasseWeil/Basic.lean` → `HasseWeil/EC/Isogeny.lean`
**Owner**: worker-C
**Checked out at**: 2026-04-08
**Estimated lines**: 40
**Difficulty**: easy
**Stream**: C

## Depends on
- T-III-4-003 ([m] : E → E)
- T-III-4-011 (ker is finite)

## Blocks
- T-III-6-010 (E[m] structure)

## Statement (Silverman III.4 def)
The **m-torsion subgroup** of `E` is `E[m] := ker [m] = { P ∈ E : [m]P = O }`.

## Acceptance criteria

```lean
namespace HasseWeil.EC

/-- The m-torsion subgroup of an elliptic curve. -/
def WeierstrassCurve.torsionSubgroup (E : WeierstrassCurve F) [Fact (E.Δ ≠ 0)] (m : ℤ) :
    AddSubgroup E.toAffine.Point :=
  AddMonoidHom.ker (E.mulByInt m).toAddHom

scoped notation E"["m"]" => WeierstrassCurve.torsionSubgroup E m

end HasseWeil.EC
```

## Notes
- Used in dual isogeny analysis (`ker φ ⊂ E[deg φ]` for any isogeny φ).

## Progress log
- 2026-04-08 [worker-C] REVIEW. Added `HasseWeil.torsionSubgroup` to
  `HasseWeil/Basic.lean`:
  ```
  noncomputable def torsionSubgroup (W : Affine F) [W.IsElliptic] (m : ℤ) :
      AddSubgroup W.Point := (mulByInt W m).toAddMonoidHom.ker
  scoped notation:max E"["m"]" => HasseWeil.torsionSubgroup E m
  @[simp] theorem mem_torsionSubgroup ... : P ∈ W[m] ↔ m • P = 0
  ```
  Build clean. Status: REVIEW. Finiteness of `E[m]` requires T-III-4-011 (ker
  is finite for nonzero isogeny), which depends on substantive new work; I left
  finiteness as a separate downstream concern.
- 2026-04-10 [worker-A] Verified: `#print axioms` on `torsionSubgroup` and
  `mem_torsionSubgroup` shows only standard axioms. No sorryAx. Full `lake build`
  clean. Finiteness correctly deferred to T-III-4-011. Status: DONE.
