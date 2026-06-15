# Sheafiness (Wedhorn 8.28b) — feasibility / obstruction map

*Produced 2026-06-14 by direct `lean_verify` axiom-tracing + elaborated-signature
inspection (not memory). `wedhorn.txt` is absent on this machine; keystone
characterisations marked “(memory)” are unverified against the source.*

## Headline

`ValuationSpectrum.isSheafy_of_stronglyNoetherian_828b` (WedhornCechAcyclicity:13433)
is fully wired and `:= ⟨embedding, gluing⟩`. Everything off the three leaves below is
verified sorry-free. The headline carries `sorryAx` solely through these three.

```
IsSheafy A
├── embedding  = cor_8_32_productRestrictionSub_isEmbedding   (RelativePieceKeystone:1633)
│   ├── isInducing  = cor_8_32_productRestrictionSub_isInducing
│   │                  └─► productRestrictionSub_isInducing_tate   ◄── LEAF B (bare sorry)
│   └── injective   = cor_8_32_productRestrictionSub_injective
│                      └─► faithfully-flat ─► per-step flat + fold
│                          └─► prop_8_30_imagePiece_wholeSpace_flat ◄── LEAF A (RPK:1360)
└── gluing     = lemma_8_34_gluing
    └─► every_rational_cover_is_OXAcyclic ─► imageCover_isOXAcyclic
        └─► every_rational_cover_is_OXAcyclic_whole_space ─► wedhorn_lemma_834
            ├─► …_part_i_laurent_acyclic   (sorry)  ◄── LEAF C-i
            └─► …_part_ii_unit_gen_…       (sorry)  ◄── LEAF C-ii
```

## The three leaves

### LEAF A — separation / flatness  `prop_8_30_imagePiece_wholeSpace_flat`
Whole-space flatness `B → 𝒪_B(im E)` over `B := presheafValue D` (Wedhorn Remark 7.55).
The wrapper `prop_8_30_remark755_chain` (the "we may assume X=V" reduction via the 8.16
keystone `relativePiece_equiv`) is **proven**; the per-step engine
`prop_8_30_basic_laurent_step_flat` is **verified sorry-free**.

**Obstruction (VERIFIED, this is the key finding):** the Remark-7.55 chain must be folded
*over `B`*. Both the per-step engine and the fold (`restrictionMap_flat_trans`) require
`[HasLocLiftPowerBounded A]` on their ambient ring (the linter confirms it is *used*, not
spurious; `restrictionMapHom` is built from the loc-lift). Folding over `B` therefore needs
`[HasLocLiftPowerBounded B]` — but the only instance `HasLocLiftPowerBounded.tate` demands
`[IsDomain B]` (false for a completion; CLAUDE.md-forbidden) **and** `[CompatiblePlusSubring B]`
(false-in-general for a completion) and itself carries sorries. So leaf A is **gated by
keystone K1** (faithful `HasLocLiftPowerBounded` on completions). The docstring's "only the
geometric chain-object is missing" omits this gap.

### LEAF B — inducing / topological  `productRestrictionSub_isInducing_tate` (StructureSheaf:1389)
A **bare `sorry`** with clean signature: `IsInducing (productRestrictionSub A C)`. This is the
"sheaf of *complete topological* rings" strictness content = **keystone K3** (Prop 6.18
Banach open-mapping). Not yet wired to the OMT core at all.

### LEAF C — gluing / acyclicity  `wedhorn_lemma_834` (parts i & ii)
Both `…_part_i_laurent_acyclic` (Laurent-cover acyclicity, A.3(3) induction) and
`…_part_ii_unit_gen_via_dominating` (dominating-unit σ-walk) carry `sorryAx`. Diffuse:
the actual `sorry` bodies live in **keystone K4** (the Čech engine —
`TateAcyclicityResiduals.lean` ×9, `LaurentRefinementAcyclic.lean`:160). No single deep
keystone; a combinatorial/geometric grind.

## Shared keystones

| Key | What | Form today | Gates | Tractability |
|----|------|-----------|-------|--------------|
| **K1** | faithful `HasLocLiftPowerBounded (presheafValue D)` | only case-(a) (`HasLocLiftPowerBounded.tate`, needs `IsDomain`+`CompatiblePlusSubring`, with sorries) | LEAF A | deep; = K1u + K1pb below |
| **K1u** | unit field `isUnit_canonicalMap_s` faithful | via `isUnit_canonicalMap_s_of_huber` → K2 | K1 | follows from K2 |
| **K1pb** | power-bounded field faithful | `tate_locLift_divByS_isPowerBounded_completion_obligation` (PI:1169) — **case-(a) only**, bare sorry; Wedhorn 7.18/7.41 | K1 | needs faithful re-statement (drop `IsDomain`/`CompatiblePlusSubring`) + proof |
| **K2** | Nullstellensatz / Spa-point on a maximal ideal (Prop 7.51) | `exists_spa_point_supp_eq_maxIdeal_of_complete` (Presheaf:2710) — **FAITHFUL form**, bare sorry, no `IsDomain`/`CompatiblePlusSubring` | K1u | **most tractable**: concrete construction (trivial valuation on the complete non-arch residue field `A/𝔪` lifts to Spa) |
| **K3** | Prop 6.18 Banach-OMT inducing bridge | σ-compact-free OMT core landed (memory); residual = inducing-wire + "Pettis-lift" | LEAF B | risky: Pettis-lift flagged "verified-missing in Wedhorn 6.16 / BGR — Bourbaki territory" (memory) — the *missing-infrastructure* red flag |
| **K4** | Čech acyclicity engine | 10 residuals (Laurent-tree induction + σ-walk) | LEAF C | grind, no single keystone; mirrors A.3/7.54 machinery already mostly built |

## Dependency graph (keystone level)

```
LEAF A ──► K1 ──┬─► K1u ──► K2   [FAITHFUL, tractable — foundational win]
                └─► K1pb        [needs faithful re-statement, 7.18/7.41]
LEAF B ──► K3   [OMT core landed; Pettis-lift residual = missing-infra risk]
LEAF C ──► K4   [diffuse Čech grind: Laurent induction + dominating-unit σ-walk]
```

## Reading

- The **separation spine (A ← K1 ← {K1u←K2, K1pb})** is the cleanest *mathematically*:
  every node has a concrete Wedhorn route, and **K2 is the most isolated/tractable single
  sorry in the entire tree** — discharging it (trivial valuation on the residue field) is a
  self-contained win that unblocks K1u.
- **Leaf B / K3** carries the only flagged *missing-infrastructure* risk (Pettis-lift,
  Bourbaki territory) — the exact thing CLAUDE.md says to stop and re-examine before building.
- **Leaf C / K4** is the most *total work* (10 residuals) but the *shallowest* per-residual
  (combinatorial), with no deep keystone.

## Suggested order

1. **K2** (Nullstellensatz/Prop 7.51) — isolated, tractable, foundational; unblocks K1u.
2. **K1pb** faithful power-bounded — completes K1 with K2 in hand.
3. **K1 → LEAF A** — fold the Remark 7.55 chain now that `HasLocLiftPowerBounded B` exists.
4. Then **LEAF C / K4** (grind) and **LEAF B / K3** (assess Pettis-lift feasibility first;
   it may need a genuine mathlib contribution).
