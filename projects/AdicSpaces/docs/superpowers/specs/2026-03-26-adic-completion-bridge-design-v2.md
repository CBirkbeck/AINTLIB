# AdicCompletion Bridge API — Design Spec v2

## Revision reason

v1 had a fundamental mismatch: `I^n • ⊤ = ⊤` on the ambient Tate
localization `R = Localization.Away s` (because `I` contains the
topologically nilpotent unit `π`, which is a unit in `R`, so
`π^n R = R`). The ambient `AdicCompletion I R` collapses to zero.

v2 corrects this by completing the **subring** `R⁺ = locSubring`
(where `J^n • ⊤ = J^n` since R⁺ is a module over itself), then
localizing at the Tate unit.

## Corrected architecture

### Step 1: Bridge on R⁺

```
Completion(R⁺, J-adic topology) ≃+* AdicCompletion(J, R⁺)
```

where `R⁺ = locSubring`, `J = locIdeal`. This is the valid bridge:
on `R⁺` as a module over itself, `J^n • ⊤ = J^n`, so the adic
filtration matches the neighborhood filtration exactly.

**Method:** Same `AbstractCompletion.compareEquiv` approach as v1,
but applied to `R⁺` instead of `R`.

### Step 2: Localize the completion

```
presheafValue D ≃+* AdicCompletion(J, R⁺)[1/π]
```

or equivalently, via the existing TopologyComparison isomorphism:

```
A⟨X⟩/(1-sX) ≃+* AdicCompletion(J, R⁺)[1/π]
```

The ambient completion `presheafValue D = Completion(R)` is obtained
from the completed subring `Completion(R⁺)` by adjoining `1/π`
(the already-invertible Tate unit). The lemmas `locNhd_leftMul` and
`locNhd_invS_step` are used here to show the ambient completion is
the localization of the subring completion.

### Step 3: Transfer + localize

- `AdicCompletion.map_injective` on R⁺-modules (Mathlib, sorry-free)
- `AdicCompletion.map_exact` on R⁺-modules (Mathlib, sorry-free)
- `AdicCompletion.flat_of_isNoetherian` on R⁺ (Mathlib, sorry-free)
- Localization preserves these properties (Mathlib: `Localization.flat`, etc.)

### Step 4: IsSheafy

The completed Laurent cover sequence is exact (by Step 3 transfer),
giving `productRestriction` injective, giving `IsSheafy`.

## Key insight

The locSubring R⁺ is the correct object to complete because:
- `J^n` on R⁺ matches the neighborhood filtration (no mismatch)
- R⁺ is noetherian (Hilbert basis: f.g. algebra over noetherian A₀)
- The Tate unit π is in R⁺ (or at least π acts on R⁺)
- The ambient ring is R = R⁺[1/π] (localization at π)
- So `Completion(R) = Completion(R⁺)[1/π]`

## File structure (revised)

| File | Responsibility |
|------|---------------|
| `Adic spaces/AdicCompletionBridge.lean` | Bridge on R⁺: `Completion(R⁺) ≃+* AdicCompletion(J, R⁺)` |
| `Adic spaces/CompletionLocalization.lean` | Step 2: `presheafValue ≃ Completion(R⁺)[1/π]` |
| `Adic spaces/AdicCompletionTransfer.lean` | Transfer + localize: exactness/flatness for presheafValue |
| `Adic spaces/StructureSheaf.lean` | IsSheafy assembly |

## Theorem stack (revised)

```
-- Layer 1: Bridge on R⁺ (AdicCompletionBridge.lean)
1. smul_top_eq_self          -- J^n • ⊤ = J^n for R⁺ as module over itself
2. quotientEquiv             -- R⁺/J^n ≃ R⁺/(J^n • ⊤) (trivial from 1)
3. quotientEquiv_natural     -- commutes with transition maps
4. adicCompletionUniformSpace -- projective limit uniformity on AdicCompletion J R⁺
5. isUniformInducing_of      -- AdicCompletion.of is uniform inducing
6. denseRange_of             -- AdicCompletion.of has dense range
7. adicAbstractCompletion    -- AbstractCompletion instance
8. adicCompletionEquiv       -- Completion(R⁺) ≃ᵤ AdicCompletion(J, R⁺)
9. adicCompletionRingEquiv   -- ring isomorphism

-- Layer 2: Localization (CompletionLocalization.lean)
10. completion_localization  -- Completion(R)[1/π] or Completion(R⁺[1/π]) ≃ presheafValue
11. presheafValue_as_localized_completion -- full identification

-- Layer 3: Transfer (AdicCompletionTransfer.lean)
12. completion_map_injective  -- on R⁺-modules
13. completion_map_exact      -- on R⁺-modules
14. completion_flat           -- Completion(R⁺) flat over R⁺
15. presheafValue_flat        -- presheafValue flat over A (via localization)

-- Layer 4: Assembly (StructureSheaf.lean)
16. separation_via_flatness   -- IsSheafy from faithful flatness
```

## Estimated size

- Layer 1 (bridge on R⁺): ~250-350 lines
- Layer 2 (localization): ~150-250 lines
- Layer 3 (transfer): ~100-150 lines
- Layer 4 (assembly): ~100-150 lines
- Total: ~600-900 lines
