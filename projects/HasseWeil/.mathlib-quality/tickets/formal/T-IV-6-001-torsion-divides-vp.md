# T-IV-6-001: Torsion order divides power of v(p)

**Status**: DONE (delivered 2026-04-20 as `FormalGroup.EvalGroup.addOrderOf_isPowOf_residueChar`)
**Silverman**: IV.6.1
**Module**: `HasseWeil/FormalGroup/Associated.lean` (in-place with T-IV-3-007)
**Owner**: worker-I
**Estimated lines**: 60 (delivered ~35)
**Difficulty**: medium
**Stream**: D

## Depends on
- T-IV-3-007 (torsion p-power)
- (DVR setup)

## Blocks
- T-IV-6-002 (Z_p example)

## Statement (Silverman IV.6.1)
Let `R` be a complete DVR with residue characteristic `p`. Then for any formal
group `F` over `R`, every torsion element of `F(M)` has order dividing some
power of `p`.

## Acceptance criteria

```lean
namespace HasseWeil.FormalGroup

theorem FormalGroup.dvr_torsion_pPower
    (F : FormalGroup R) [IsDiscreteValuationRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    (p : ℕ) (hp : p.Prime) [CharP (IsLocalRing.ResidueField R) p]
    (x : F.evalGroup) (hx : IsAddTorsion x) :
    ∃ k : ℕ, addOrderOf x ∣ p^k

end HasseWeil.FormalGroup
```

## Notes
- This refines T-IV-3-007 to the DVR case.

## Progress log

- **2026-04-20** — DONE. Delivered as a specialization of T-IV-3-007 (which
  provides the general theorem with an abstract `hR : ∀ m, ¬ p ∣ m → IsUnit (m : R)`
  hypothesis). Instantiating `hR` for a complete local ring with
  `[CharP (IsLocalRing.ResidueField R) p]` is a short derivation via
  `IsLocalRing.notMem_maximalIdeal` + `CharP.cast_eq_zero_iff`:

  ```lean
  theorem FormalGroup.EvalGroup.addOrderOf_isPowOf_residueChar
      (F : FormalGroup R) (hAdic : IsAdic (IsLocalRing.maximalIdeal R))
      (p : ℕ) (hp : p.Prime) [CharP (IsLocalRing.ResidueField R) p]
      (x : F.EvalGroup hAdic) (hx : IsOfFinAddOrder x) :
      ∃ k : ℕ, addOrderOf x = p ^ k
  ```

  Plus helper `isUnit_natCast_of_not_dvd_residueChar` (the content-bearing
  local-ring + charP computation). The `IsDiscreteValuationRing R` hypothesis
  from the original acceptance spec is **not** needed — only
  `IsLocalRing` + residue-characteristic. The theorem applies to any complete
  local ring whose residue field has characteristic `p`, including DVRs as a
  special case.

  ~35 lines added. Axiom-clean (`propext, Classical.choice, Quot.sound`).
  Full build passes.
