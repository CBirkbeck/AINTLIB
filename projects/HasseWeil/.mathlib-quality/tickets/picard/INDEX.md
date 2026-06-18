# Picard / III.4.8 Ticket Index

Tickets to discharge the universal Silverman III.4.8 (`AddHomProperty` for
arbitrary `Isogeny.AG`) via the **Pic⁰ route**. See `PLAN.md` for full
context.

## Status legend

`O` = OPEN | `C` = CHECKED-OUT | `P` = IN-PROGRESS | `B` = BLOCKED |
`R` = REVIEW | `D` = DONE

## Tickets

### Phase A — `σ : ProjectiveDiv⁰(E) → E` (sum of points)

| ID | Status | Owner | Title | Lines | File |
|---|---|---|---|---|---|
| [T-PIC-A-001](T-PIC-A-001-sigma-sum-of-points.md) | **D** | session | `σ : ProjectiveDiv⁰(E) → E` (sum-of-points using group law) | 80 | PicZero.lean |
| [T-PIC-A-002](T-PIC-A-002-sigma-vanishes-on-principal.md) | **expanded into 4 sub-tickets** | — | `σ` vanishes on principal divisors (parent) | (see sub) | PicZero.lean |
| [T-PIC-A-002a](T-PIC-A-002a-line-case.md) | O | — | General line case: `σ(div(y - g(x))) = 0` (chord/tangent) | ~200 | PicZeroLineCase.lean (NEW) |
| [T-PIC-A-002b](T-PIC-A-002b-vertical-line-case.md) | **D** | session | Vertical-line case: `σ(div(x - α)) = 0` | 80 | PicZero.lean |
| [T-PIC-A-002c](T-PIC-A-002c-factorization.md) | O | — | Factorization of `K(E)*` into lines + verticals + units | ~200 | PicZero.lean |
| [T-PIC-A-002d](T-PIC-A-002d-assembly.md) | O | — | Final assembly via multiplicativity | ~50 | PicZero.lean |
| [T-PIC-A-003](T-PIC-A-003-sigma-bar-on-pic.md) | **D** | session | `σ̄ : Pic⁰(E) → E` (witness-parametric: `picZeroSumOfWitness`) | 25 | EC/IsogenyAG/HomProperty.lean |
| [T-PIC-A-004](T-PIC-A-004-sigma-bar-group-hom.md) | **D** | session | `σ̄` group hom (free from `picZeroSumOfWitness` being `→+`) | 0 | EC/IsogenyAG/HomProperty.lean |

### Phase B — `κ : E → Pic⁰(E)` (canonical map)

| ID | Status | Owner | Title | Lines | File |
|---|---|---|---|---|---|
| [T-PIC-B-001](T-PIC-B-001-kappa-canonical.md) | **D** | session | `κ : E → Pic⁰(E), P ↦ class of (P)−(O)` | 60 | PicZero.lean |
| [T-PIC-B-002](T-PIC-B-002-kappa-zero.md) | **D** | session | `κ(O) = 0` in `Pic⁰(E)` | 20 | PicZero.lean |
| [T-PIC-B-003](T-PIC-B-003-sigma-bar-comp-kappa-id.md) | **R** | session | `σ̄ ∘ κ = id` — divisor-level form delivered as `projectiveDivisorSum_kappaDivisor`; Pic⁰-level needs A-003 | 15 (divisor-level) | PicZero.lean |

### Phase C — Pushforward on `Pic⁰` for an isogeny

| ID | Status | Owner | Title | Lines | File |
|---|---|---|---|---|---|
| [T-PIC-C-001](T-PIC-C-001-pushforward-divisor.md) | **D** | session | `pushforwardDivisor`: divisor-level pushforward via `toPointMap` | 50 | PicZeroPushforward.lean |
| [T-PIC-C-002](T-PIC-C-002-pushforward-degree.md) | **D** | session | Pushforward of `Div⁰` lands in `Div⁰` (preserves degree) | 35 | PicZeroPushforward.lean |
| [T-PIC-C-003](T-PIC-C-003-pushforward-principal.md) | **expanded into 4 sub-tickets** | — | `φ_*(div g) = div(N(g))` (parent) | (see sub) | PicZeroPushforward.lean |
| [T-PIC-C-003a](T-PIC-C-003a-ord-multiplicity-bridge.md) | O | — | Bridge: `ord_P f = multiplicity (maxIdeal P) (f)` | ~100 | PicZeroPushforward.lean |
| [T-PIC-C-003b](T-PIC-C-003b-norm-divisor-affine.md) | O | — | Norm-divisor identity at affine points (uses worker-I infra) | ~150 | PicZeroPushforward.lean |
| [T-PIC-C-003c](T-PIC-C-003c-norm-divisor-infinity.md) | O | — | Norm-divisor identity at infinity | ~50 | PicZeroPushforward.lean |
| [T-PIC-C-003d](T-PIC-C-003d-assembly.md) | O | — | Assembly: `pushforwardProjectiveDivisor (div g) = div (N g)` | ~30 | PicZeroPushforward.lean |
| [T-PIC-C-004](T-PIC-C-004-pushforward-pic-group-hom.md) | **D** | session | `φ_∗ : Pic⁰(E₁) → Pic⁰(E₂)` group hom (witness-parametric: `pushforwardPicZeroOfWitness`) | 25 | EC/IsogenyAG/HomProperty.lean |
| **BONUS** | **D** | session | `pushforwardProjectiveDivisor_kappaDivisor` — divisor-level diagram commute | 15 | PicZeroPushforward.lean |

### Phase D — Diagram commute

| ID | Status | Owner | Title | Lines | File |
|---|---|---|---|---|---|
| [T-PIC-D-001](T-PIC-D-001-diagram-commute.md) | **D** | session | `κ_E₂ ∘ φ_pt = φ_∗ ∘ κ_E₁` (witness-parametric: `picZeroOfPoint_pushforwardPicZero`) | 10 | EC/IsogenyAG/HomProperty.lean |

### Phase E — Witness-parametric universal theorem

| ID | Status | Owner | Title | Lines | File |
|---|---|---|---|---|---|
| [T-PIC-E-001](T-PIC-E-001-witness-parametric-universal.md) | **D** | session | **`AddHomProperty_of_picZero_witnesses`** — universal `AddHomProperty` parametrized by 4 witnesses | 50 | EC/IsogenyAG/HomProperty.lean |

### Phase F — Closure via worker-K's T-III-3-003

| ID | Status | Owner | Title | Lines | File | Depends on |
|---|---|---|---|---|---|---|
| [T-PIC-F-001](T-PIC-F-001-kappa-comp-sigma-bar-id.md) | **expanded into 3 sub-tickets** | — | `κ ∘ σ̄ = id` (parent) | (see sub) | PicZero.lean | (see sub) |
| [T-PIC-F-001a](T-PIC-F-001a-existence.md) | O | — | Existence: `∀ D ∈ Div⁰, ∃ P, D ~ (P) − (O)` (inductive, no R-R) | ~120 | PicZero.lean | T-PIC-A-002a |
| [T-PIC-F-001b](T-PIC-F-001b-uniqueness.md) | B | — | Uniqueness: `(P) ~ (Q) ⟹ P = Q` — only for σ̄-iso, NOT for B-4-003 | ~30 | PicZero.lean | T-III-3-003 (worker-K) |
| [T-PIC-F-001c](T-PIC-F-001c-assembly.md) | O | — | Assembly: `κ ∘ σ̄ = id` at Pic⁰ level (B-003 + F-001a, no F-001b!) | ~50 | PicZero.lean + HomProperty.lean | F-001a, A-002, B-003 (DONE) |
| [T-PIC-F-002](T-PIC-F-002-pic-zero-iso-equiv.md) | B | — | σ̄ as `MulEquiv` (full bijection package); needs F-001b — NOT for B-4-003 | ~40 | PicZero.lean | F-001b |
| [T-PIC-F-003](T-PIC-F-003-universal-add-hom-property.md) | (subsumed by G-006) | — | B-4-003 over `[IsAlgClosed F]` only — superseded by Phase G unconditional version | — | — | — |

### Phase G — Galois Descent (NEW — for unconditional B-4-003 over arbitrary F)

| ID | Status | Owner | Title | Lines | File | Depends on |
|---|---|---|---|---|---|---|
| [T-PIC-G-001](T-PIC-G-001-curvemap-basechange.md) | O | — | `CurveMap.baseChange` along F → L | ~80 | Curves/CurveMap.lean (extension) | BaseChange.lean (DONE) |
| [T-PIC-G-002](T-PIC-G-002-isogeny-basechange.md) | O | — | `Isogeny.AG.baseChange` | ~30 | EC/IsogenyAG/BaseChange.lean (NEW) | G-001 |
| [T-PIC-G-003](T-PIC-G-003-coordhom-basechange.md) | O | — | `CoordHom.baseChange` | ~50 | EC/IsogenyAG/BaseChange.lean | G-001, G-002 |
| [T-PIC-G-004](T-PIC-G-004-topointmap-basechange.md) | O | — | `toPointMap_baseChange` compatibility square | ~80 | EC/IsogenyAG/BaseChange.lean | G-002, G-003 |
| [T-PIC-G-005](T-PIC-G-005-descent-lemma.md) | O | — | `AddHomProperty.of_baseChange` descent lemma | ~40 | EC/IsogenyAG/BaseChange.lean | G-004 |
| [T-PIC-G-006](T-PIC-G-006-unconditional-b4003.md) | O | — | **`AddHomProperty_universal`** — B-4-003 over arbitrary F (no `[IsAlgClosed F]`) | ~20 | EC/IsogenyAG/HomProperty.lean | A-002d + C-003d + F-001c + G-005 |

## Statistics

### Original (witness-parametric framework)

| Phase | Tickets | Lines | Status |
|---|---|---|---|
| A (1-4) | 4 | ~250 | All DONE except A-002 |
| B (1-3) | 3 | ~120 | All DONE |
| C (1-4) | 4 | ~340 | C-003 OPEN, rest DONE |
| D | 1 | ~30 | DONE |
| E | 1 | ~40 | DONE |
| F | 3 | ~70 | All blocked or expanded |

### Witnesses sub-tickets (NEW, for unconditional B-4-003)

| Sub-piece | Tickets | Lines |
|---|---|---|
| A-002 sub-tickets (a/b/c/d) | 4 (1 done) | ~530 |
| C-003 sub-tickets (a/b/c/d) | 4 | ~330 |
| F-001 sub-tickets (a/c) for B-4-003 | 2 | ~170 |
| F-001b (optional, for σ̄-iso only) | 1 | ~30 |
| **Subtotal: witnesses for B-4-003 over [IsAlgClosed F]** | **10** | **~1030** |
| **Phase G — Galois descent (drops `[IsAlgClosed F]`)** | **6** | **~300** |
| **Total for unconditional B-4-003 over arbitrary F** | **16** | **~1330** |

**Worker-K dependency for B-4-003**: NONE (revised — F-001b is no longer
on the critical path).
**Worker-I dependency**: read-only consumption of `NormValuation.lean`
(721 LOC of bridge infrastructure already shipped).
**`[IsAlgClosed F]` regression**: AVOIDED via Phase G. Final B-4-003 is
over arbitrary F. Critical for Hasse over F_q (Frobenius lives over F_q).

See [WITNESSES_PLAN.md](WITNESSES_PLAN.md) for the full feasibility
analysis, sub-ticket breakdown, and execution sequencing.

## Cleanup checkpoints

| ID | When |
|---|---|
| `CLEANUP-PIC-1` | After Phase A complete (PicZero.lean partial) |
| `CLEANUP-PIC-2` | After Phase B complete (PicZero.lean full Phase A+B) |
| `CLEANUP-PIC-3` | After Phase C complete (PicZeroPushforward.lean) |
| `CLEANUP-PIC-4` | Final: after F-003 lands (or after E-001 if F is gated) |
| `CLEANUP-W-1` | After A-002 fully closed (witnesses sub-piece) |
| `CLEANUP-W-2` | After C-003 fully closed (witnesses sub-piece) |
| `CLEANUP-W-3` | After F-001a + F-001c fully closed |
| `CLEANUP-W-4` | Final: B-4-003 unconditional, drop `_witnesses` from API names |

## Parallel opportunities

### Original Pic⁰ route (now mostly complete)

- **A-001** must run first (defines σ).
- After A-001: A-002 and B-001 can run in parallel.
- After A-002 + A-001: A-003.
- After A-003: A-004.
- B-002, B-003 can run after B-001 completes.
- C-001 through C-004 are a serial chain, run independently of A/B.
- D-001 needs A-004, B-003, C-004 done.
- E-001 needs D-001 done.

Up to **3 workers** can productively parallelize at peak (Phase A, Phase B,
Phase C in different files).

### Witnesses-execution opportunities (NEW)

For unconditional B-4-003 over arbitrary F, four workers can execute
independently:

- **Worker α** on Piece 1 (A-002): A-002a → A-002c → A-002d. Touches
  `PicZero.lean`, `PicZeroLineCase.lean` (NEW).
- **Worker β** on Piece 2 (C-003): C-003a → C-003b → C-003c → C-003d.
  Touches `PicZeroPushforward.lean`, consumes worker-I's
  `NormValuation.lean` read-only.
- **Worker γ** on Piece 3 (F-001a → F-001c): waits for α's A-002a, then
  shares `PicZero.lean` with α.
- **Worker δ** on Phase G (G-001 → G-005): touches new
  `EC/IsogenyAG/BaseChange.lean` and `Curves/CurveMap.lean`. **Fully
  independent** of α/β/γ — can start immediately.

After all four pieces: G-006 is a ~20-line final assembly producing
`AddHomProperty_universal` over arbitrary F.

## Cross-references

- `PLAN.md` — full architecture document.
- Worker-K tickets: `tickets/curves/T-II-3-009-deg-div-zero.md`,
  `tickets/ec/T-III-3-003-P-Q-equiv-implies-eq.md`.
- Existing infra: `HasseWeil/Curves/Divisors.lean`,
  `HasseWeil/Curves/ProjectiveDivisor.lean`,
  `HasseWeil/EC/IsogenyAG.lean`.
