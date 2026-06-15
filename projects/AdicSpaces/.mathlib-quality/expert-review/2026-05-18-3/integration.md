# Reply integration — 2026-05-18-3 (Session 25)

Reply received: 2026-05-18.
Brief: ./brief.md
Reply: ./reply.md
Status: ALL 8 changes applied per user "apply all" directive.

## Interpretation summary

Reviewer answered all 5 questions decisively:
- **Q-S24.1**: YES — Ex 6.38 + noeth A_0 ⇒ noeth ring of def for O_X(D). Write `presheafValue_pairOfDefinition_isNoetherian`.
- **Q-S24.2**: YES — Path α correct. Wedhorn 8.31 honestly needs noeth A_0; "noeth Tate" in Huber/Wedhorn-style is shorthand for it. Don't try abstract noetherianity.
- **Q-S24.3**: IsDomain is proof artifact. Wedhorn 8.34 works for non-domain via unit-ratio in O(V_j) (not domain cancellation in A). Remove IsDomain from FINAL theorem (A3); F4/A1/A2 may keep as narrower variants.
- **Q-S24.4**: YES — add [CompleteSpace A] (with uniformity bundle) to A3 and the Wedhorn-clean chain.
- **Q-S24.META**: proof-hypothesis ledger (4 columns); audit by mathematical pattern, not just syntax; 5 taint patterns listed.

## Changes applied

### Signature changes
| # | Change | File |
|---|--------|------|
| 1 | Added `[UniformSpace A] [IsUniformAddGroup A] [CompleteSpace A]` to A3 | StructureSheaf.lean |
| 2 | Same uniformity bundle on A1 (`isSheafy_*_flat`) | StructureSheaf.lean |
| 3 | Same on A2 (`isSheafy_*_flat_of_topo_inducing`) | StructureSheaf.lean |
| 4 | Same on B5' (`hSpa_surj_cover_level`) | StructureSheaf.lean |
| 5 | Same on C1 (`prop_8_30_flat_clean`) | StructureSheaf.lean |
| 6 | Same on C2 (`cor_8_32_clean`) | StructureSheaf.lean |
| 7 | Same on AuditCleanWrappers `_proof` variants | AuditCleanWrappers.lean |
| 8 | Same on `isSheafy_*_flat_of_wedhorn_tree_existence` (EmbeddingTopo consumer) | EmbeddingTopo.lean |
| 9 | Same on `isSheafyComplete` (downstream consumer) | TateAcyclicityResiduals.lean |

**IsDomain**: kept on A1, A2 (narrower variants per reviewer; `rationalCovering_hasSeparation` consumes it in empty-cover edge case). Removed from A3 (already was — A3 is the final Wedhorn-clean target, no IsDomain). F4 keeps IsDomain temporarily per reviewer's "narrower-helper" guidance.

### New infrastructure

| # | New lemma | File |
|---|-----------|------|
| 10 | `presheafValue_pairOfDefinition_isNoetherian (P) [IsNoetherianRing P.A₀] (D₀)` — noeth ring of def for `O_X(D)` from noeth `A_0`. Sorry-bodied with concrete discharge plan (Hilbert basis + Stacks 0316). | PresheafTateStructure.lean |

This is the **high-leverage unblocker** per the round-3 reply: with this lemma, the parametric noeth-pair hypothesis on `A` propagates cleanly to every `presheafValue D` along the chain. Without it, Path α was discharge-infeasible at the per-cover-piece level.

### Memory / methodology updates

| # | Memory | What |
|---|--------|------|
| 11 | `feedback_taint_graph.md` updated | added "taint by mathematical pattern" section + 5 patterns: (1) strong-noeth-⇒-noeth-A_0, (2) single-restriction-injective/surj, (3) completed-loc-is-algebraic-IsLocalization, (4) S ⊆ A spanning A, (5) domain cancellation in ratio splits |
| 12 | `feedback_proof_hypothesis_ledger.md` (new) | 4-column ledger template per the round-3 Q-S24.META reply |

### Decomposition + session record

| # | Update | File |
|---|--------|------|
| 13 | Session 25 update with reviewer verdicts + applied changes | decomposition.md |
| 14 | This integration.md + state.md flip to "reply received: true" | session folder |

## Sorry-count delta (in-scope IsSheafy chain)

**~52 → ~53** (+1 for the new `presheafValue_pairOfDefinition_isNoetherian` lemma; net signature changes are non-counting).

## Build status

`lake build` clean after 3 rounds of fix-and-rebuild:
1. Initial parametric uniformity addition → broke EmbeddingTopo:2157 (A2 consumer)
2. Added uniformity to EmbeddingTopo's `_of_wedhorn_tree_existence` → broke TateAcyclicityResiduals:2380 (`isSheafyComplete`)
3. Added uniformity to `isSheafyComplete` → clean

## Verdict shifts (per leaf)

| Leaf | Pre | Post |
|------|-----|------|
| A3 | Path α parametric, no CompleteSpace | + `[UniformSpace+IsUniformAddGroup+CompleteSpace]` |
| A1/A2 | Path α parametric, IsDomain kept | + uniformity bundle; IsDomain still present as narrower-variant artifact |
| B5'/C1/C2 | Path α parametric | + uniformity bundle |
| F4 | IsDomain | unchanged (narrower-helper status per reviewer) |
| F5 | sorry-bodied non-domain target | unchanged (still the aspirational target) |
| `presheafValue_pairOfDefinition_isNoetherian` | did not exist | ✓ stated, sorry'd, with discharge plan |

## Changes rejected by user

None.

## Open questions remaining

None — reviewer answered all 5 round-3 questions. Path α is now soundly architected per the reviewer's recommendations.

## Decisions recorded

1. **Path α + CompleteSpace + parametric noeth pair** is the project's binding architecture.
2. **IsDomain stays on narrower variants** (A1, A2, F4) as proof artifacts; absent from A3 (final theorem).
3. **`presheafValue_pairOfDefinition_isNoetherian`** is the canonical Ex-6.38-propagation lemma; will be invoked in every C1/C2/B5' proof at the per-cover-piece level.
4. **Proof-hypothesis ledger** is binding for future decompose passes.
5. **Taint patterns** (5 listed) are mandatory cross-check during future audits.

## Recommendation for next session

Discharge `presheafValue_pairOfDefinition_isNoetherian` (~30-50 LOC). This is the single highest-leverage unblocker — once done, the parametric chain has a clean propagation through Ex 6.38, and C1/C2/B5' can be tackled with all hypotheses in scope.

After that: priority order per round-2 reviewer:
1. C1 (prop_8_30_flat_clean) — assembly via existing TateAlgebra wrappers
2. C2 (cor_8_32_clean) — needs combinator in TateAcyclicityFinalAssembly downstream
3. F4 (ratio tree) — assembly of F7-F10
4. I1 (Stacks 023N descent) — mathlib `Module.Flat.tensorEqLocusEquiv`
5. C3 (Spa-presheafValue equivalence) — Wedhorn 8.2 + Spa.comap framework
