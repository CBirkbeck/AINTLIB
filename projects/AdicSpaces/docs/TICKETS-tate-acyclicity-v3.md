# Tate Acyclicity v3 — Completing the Non-Discrete Case

**Master goal:** Prove Wedhorn Theorem 8.28(b) for non-discrete strongly
noetherian Tate rings: `O_X` is a sheaf of complete topological rings.

**Constraint:** No `sorry` or `axiom`.

**Based on:** ChatGPT Pro review (2026-04-02), correcting the approach from v2.

---

## 2026-04-30 Expert Review Addendum — T089/T110 Witness Residual

Current Control Tower tickets `T111`/`T112` own the remaining T089 residual:
`locLift_preimage_jfull_witness_existence`, after commit `68e4dbb` reduced
`locLift_preimage_target_witness_existence` to that smaller private lemma.

External review assessment:
- The reduction is mathematically sound, and the residual has the correct
  orientation: target smallness of `algebraMap (α * e^k)` should produce a
  source-depth representative for `α`, modulo the target localization kernel.
- The radical relation `e * D₀.s = D.s^N` is the right denominator-comparison
  input. It should not force extra global hypotheses in the final Tate
  acyclicity theorem.
- The main risk is over-rigid packaging: linear loss in `k` is expected, but
  the exact coefficient `D₀.hopen.choose` should only be used if it is already
  the established one-division-by-`D₀.s` cost. Otherwise first prove a version
  with a derived local constant `c_lift`, then specialize/discharge it locally.
- The clean algebraic core should be formulated modulo
  `K_D := RingHom.ker (algebraMap A (Localization.Away D.s))`:
  target-smallness of `α * e^k` implies `α` is congruent modulo `K_D` to an
  element of source depth `I^(n + k*c)`.
- Prove the saturation first in the noetherian source ring-of-definition /
  finitely generated rational-localization algebra, or for `α ∈ D₀.P.A₀`;
  extend to arbitrary `α : A` only afterward by clearing Tate denominators.
  Do not treat the whole Tate ring `A` as a finite `D₀.P.A₀`-module.
- If arbitrary `D₀ D : RationalLocData A` is stronger than downstream needs,
  specialize to data from a common rational-containment situation over the
  same ambient Tate setup rather than adding final theorem hypotheses.

No extra hypotheses should be added to `ValuationSpectrum.tateAcyclicity`,
Part 2, or the final acyclicity theorem. Any helper hypotheses introduced in
this lane must be discharged from the existing Tate/rational-containment data.

---

## Key Architectural Decisions (from review)

### Notation
- `π ∈ A₀` = topologically nilpotent unit, `I = πA₀` = ideal of definition.
- `g ∈ A` = denominator of rational subset `R(T/g)`.
- `D = A₀[T/g]` = ring of definition of `A[1/g]`, `J = ID = πD`.

### The bridge formula
```
O_X(R(T/g)) ≅_top (AdicCompletion_J D)[1/π]
```
`AdicCompletion_J D` is the **ring of definition** of the completed localization;
the full section ring requires inverting the Tate unit `π`.

### No T-topology needed
For strongly noetherian Tate rings, Example 6.38 identifies presheaf values
with ordinary Tate-algebra quotients:
- `O_X(R(f/1)) = A⟨ζ⟩/(f-ζ)` (quotient topology from complete Tate algebra)
- `O_X(R(1/f)) = A⟨η⟩/(1-fη)`

### Strictness via Banach open mapping, NOT adic completion exactness
The rings in the Laurent sequence are NOT f.g. `A₀`-modules, so
`AdicCompletion.map_exact` does not apply to the raw sequence.
Instead: prove algebraic exactness of the already-completed Row 3,
then get strictness from Banach/open mapping (Wedhorn Thm 6.16).

Mathlib has `IsModuleTopology.isOpenMap_of_surjective` (no completeness
needed) and `MonoidHom.isOpenMap_of_sigmaCompact` (BaireSpace route).
Check which applies to our completed Tate rings.

---

## What's Already Done (reusable from v1/v2)

| What | File | Status |
|------|------|--------|
| Cech complex + refinement | CechCohomology.lean | DONE (0 sorry) |
| Tate algebra defs + flatness | TateAlgebra.lean | DONE (0 sorry) |
| Laurent cover algebraic exactness (discrete) | LaurentCoverExact.lean | DONE (0 sorry) |
| Flatness results | FlatnessResults.lean | DONE (0 sorry) |
| Algebraic presheaf identification | PresheafIdentification.lean | DONE (0 sorry) |
| Noetherian Tate module topology (Prop 6.18) | NoetherianTateModules.lean | DONE (0 sorry) |
| Completion preserves strict exact seqs | CompletionExact.lean | DONE (0 sorry) |
| Discrete acyclicity theorem | TateAcyclicity.lean | DONE (0 sorry) |
| AdicCompletion bridge (partial) | AdicCompletionBridge.lean | PARTIAL |

---

## Tracker

| Ticket | Status | Agent | Started | Completed | Notes |
|--------|--------|-------|---------|-----------|-------|
| T1 | DONE | claude-opus | 2026-04-02 | 2026-04-03 | 0 sorry. General Row 3 exactness: lambdaMap_surjective (diagonal sums), deltaMap_gen_surjective, ker_deltaMap (3x3 diagram chase), row3_exact. |
| T2 | DONE | claude | 2026-04-02 | 2026-04-02 | Bridge: completionLocSubringEquiv + range theorem |
| T3 | DONE | claude | 2026-04-02 | 2026-04-02 | OpenMapping.lean: filtration-open + strict exact package |
| T4 | DONE | claude | 2026-04-02 | 2026-04-03 | 0 sorry. Deleted false IsInducing/IsUniformInducing. Remark 6.37 proved. tateQuotientToPresheafHom_continuous via J-adic eval + IsQuotientMap. hJ_eval hypothesis for caller. |
| T5 | **REWORK NEEDED** | claude | 2026-04-02 | — | ⚠️ `locLift_preimage_locNhd` is **FALSE** (counterexample from reviewer 2026-04-03). The entire `restrictionMapHom_isInducing` chain is wrong. Replaced by strict exactness of Laurent row (see `docs/TICKETS-axiom-clean.md`). |
| T6 | **REWORK NEEDED** | claude | 2026-04-02 | — | ⚠️ `isSheafy_ofStronglyNoetherianTate_flat` depends on `sorryAx` through the false T5 chain. Needs refactoring to use strict exactness route. See `docs/TICKETS-axiom-clean.md` R1-R3. |

## Dependency Graph

```
WAVE 1 (parallel):
  T1 (algebraic exactness)     T2 (bridge)      T3 (open mapping)
       │                           │                  │
       │                           ↓                  │
       │                    T4 (topo identification)   │
       │                     (OPTIONAL for T5)         │
       └───────────────────────────┼──────────────────┘
                                   ↓
WAVE 2:                     T5 (strictness)
                                   │
                                   ↓
WAVE 3:                     T6 (assembly)
```

**Wave 1:** T1, T2, T3 can all run in parallel.
**Wave 2:** T5 needs T1 + T3 (critical path). T4 is optional (nice-to-have for
  IsModuleTopology route, but T5 can use filtration route from T3 directly).
**Critical path change:** T-topology approach for T4 abandoned — product topology
  is too coarse for completeness/eval continuity. New approach uses J-adic completion
  + Tate algebra quotients (Example 6.38) per reviewer feedback.
**Wave 3:** T6 needs T5.
**Wave 3:** T6 needs T5.

---

## TICKET T1: Generalize Algebraic Exactness to Non-Discrete

**Status:** NOT STARTED
**Estimated:** ~200 lines (modifications)
**Blocks:** T5
**Depends on:** None
**Files:** `LaurentCoverExact.lean`, `TateAcyclicity.lean`

### Task

Remove `[DiscreteTopology A]` hypotheses from the Laurent cover exactness
proofs. The 3×3 diagram chase is purely algebraic and works for general
restricted power series rings.

### What to do

1. Audit all theorems in `LaurentCoverExact.lean` for `[DiscreteTopology A]`.
2. For each, determine if the proof actually uses discreteness or if it works
   for general `[NonarchimedeanRing A] [CompleteSpace A]`.
3. The key results to generalize:
   - `lambdaMap_surjective` : Row 2 surjectivity (coefficient decomposition)
   - `ker_lambdaMap_eq_range_iotaHom` : Row 2 exactness at middle
   - `epsilonHom_injective` → `epsilonHom_gen_injective` (already general)
   - `deltaMap_surjective` : Row 3 surjectivity
   - `laurentCover_exact` : Full exactness
4. The coefficient comparison arguments work identically for restricted power
   series — truncation preserves the restricted property.
5. Similarly audit `TateAcyclicity.lean` for discrete-only assumptions.

### Key insight

The 3×3 diagram objects in the non-discrete case are:
- Row 2: `A⟨ζ⟩ × A⟨η⟩ → A⟨ζ,ζ⁻¹⟩` (complete Tate rings)
- Row 3: `B₁ × B₂ → B₁₂` (quotients of complete rings by closed ideals)

Row 3 IS the completed sequence. No separate completion step is needed.
The algebraic exactness of Row 3 follows from the diagram chase.

### Acceptance criteria

- All Laurent cover exactness theorems work without `[DiscreteTopology A]`
- `lake env lean "Adic spaces/LaurentCoverExact.lean"` compiles
- 0 sorry

---

## TICKET T2: Completion-Localization Bridge

**Status:** NOT STARTED
**Estimated:** ~300 lines
**Blocks:** T4
**Depends on:** None
**Files:** `AdicCompletionBridge.lean` (extend), possibly new file

### Task

Prove the fundamental bridge isomorphism:
```
UniformSpace.Completion(A[1/g], locTopology) ≅ (AdicCompletion_J D)[1/π]
```
where `D = A₀[T/g]`, `J = πD`, `π` = topologically nilpotent unit.

### Proof outline (from reviewer)

**Step A — Algebraic identity: `A[1/g] = D[1/π]`**

1. `A = A₀[1/π]` (Tate ring decomposition: `A₀` is ring of definition,
   `π` is topologically nilpotent unit).
2. `D = A₀[T/g] ⊂ A[1/g]` (ring of definition of localization).
3. `D[1/π] ⊇ A[1/g]`: Since `A = A₀[1/π]`, every `a/g^n ∈ A[1/g]` can
   be written with `a = a₀/π^k`, so `a/g^n = a₀/(π^k · g^n) ∈ D[1/π]`.
4. `D[1/π] ⊆ A[1/g]`: Since `T·A = A` in the Tate case, choose `aₜ ∈ A`
   with `∑ aₜ t = 1`. After clearing `π`-denominators, `π^N/g ∈ D` for
   some `N`, hence `1/g ∈ D[1/π]`, so `A[1/g] ⊆ D[1/π]`.
5. Therefore `A[1/g] = D[1/π]`.

**Step B — Topological identity**

The localization topology on `A[1/g]` has `D` as open ring of definition
with ideal of definition `J = πD`. The topology on `D[1/π]` generated by
the `J`-adic topology on `D` coincides with the localization topology.

**Step C — Completion**

Completing `D[1/π]` with the topology from Step B gives `D̂[1/π]` where
`D̂ = AdicCompletion_J D`. The universal property of completion gives the
isomorphism with `UniformSpace.Completion(A[1/g])`.

### Lean strategy

- Use `AdicCompletionBridge.lean` (already has `UniformSpace.Completion R ≃+*
  AdicCompletion I R` when topology is `I`-adic).
- Extend to the case where `R = D[1/π]` with topology from `J`-adic on `D`.
- Key Mathlib tools: `AbstractCompletion.compareEquiv`,
  `AdicCompletion.map_surjective`.

### Acceptance criteria

- Bridge isomorphism proved as `RingEquiv`
- Connected to `presheafValue D` from `Presheaf.lean`
- `lake env lean` compiles, 0 sorry

---

## TICKET T3: Banach Open Mapping for Complete Tate Modules

**Status:** NOT STARTED
**Estimated:** ~150 lines
**Blocks:** T5
**Depends on:** None
**Files:** `NoetherianTateModules.lean` (extend) or new file

### Task

Establish that surjective continuous `A`-linear maps between completed
rational localizations are open (Wedhorn Thm 6.16). This gives strictness.

### What to check first

1. **`IsModuleTopology.isOpenMap_of_surjective`** in Mathlib: if the target
   carries `moduleTopology`, then surjective linear maps are automatically
   open. Check if our completed Tate algebras carry `IsModuleTopology`.
   If yes, this is immediate — no Baire category needed.

2. **`MonoidHom.isOpenMap_of_sigmaCompact`** in Mathlib: for `SigmaCompactSpace`
   source mapping onto `BaireSpace + T2` target. Complete metrizable spaces
   are both `SigmaCompactSpace` and `BaireSpace`. Check if our spaces
   satisfy these instances.

3. If neither applies directly, prove the result for our specific case:
   - Completed rational localizations are complete nonarchimedean topological
     rings with countable fundamental system of neighborhoods.
   - Use: `IsCountablyGenerated (nhds 0)` + `CompleteSpace` + surjective
     continuous group hom → open.

### The key application

For the Laurent cover, `δ : B₁ × B₂ → B₁₂` is surjective and continuous.
By open mapping, `δ` is open, hence strict. Then:
- `ker δ` is closed in `B₁ × B₂`, hence complete.
- `ε : A → ker δ` is a continuous bijection.
- Since `A` is complete and `ker δ` is T₂, `ε` is a topological embedding.

### Acceptance criteria

- Open mapping theorem stated and proved for our completed Tate rings
- Applied to get `δ` open and `ε` embedding
- 0 sorry

---

## TICKET T4: Topological Identification via Tate Quotients (Example 6.38)

**Status:** IN PROGRESS (reworked) — **see architecture warning below**
**Estimated:** ~250 lines
**Blocks:** nothing (T5/R2 can bypass via strict exactness route)
**Depends on:** T2
**Files:** `TopologyComparison.lean`, `TateAlgebraWedhorn.lean`

### ⚠️ ARCHITECTURE WARNING (2026-04-03)

**`locLift_preimage_locNhd` is FALSE.** Individual restriction maps between
completed localizations are NOT topological embeddings. The counterexample
(from reviewer): `A = Q_p⟨X⟩`, `U = R({p,X}/p)`. See `docs/TICKETS-axiom-clean.md`.

**Impact on T4:**
- T4's `locToQuotientOneSubfX_gen_isInducing` sorry suffers from the SAME issue.
  The "induced ≤ D.topology" direction (Artin-Rees estimate) is false for the
  same reason: rational localization changes the ring of definition and can make
  elements topologically smaller.
- T4's topological identification is still MATHEMATICALLY CORRECT — the quotient
  `A⟨X⟩/(1-sX)` IS homeomorphic to `presheafValue D`. But the proof cannot go
  through `IsInducing` of the restriction map.
- The correct approach for the topological identification is:
  1. Both sides are completions of the same algebraic localization.
  2. The universal property of completion gives the isomorphism.
  3. Completeness of the quotient comes from J-adic completeness (Remark 6.37),
     NOT from the restriction being inducing.

**T4 is NO LONGER ON THE CRITICAL PATH.** The sheaf condition is now proved via
strict exactness of the Laurent row (R2 in `docs/TICKETS-axiom-clean.md`), which
uses T1 (algebraic exactness, done) + T3 (open mapping, done). T4 is nice-to-have
for connecting presheaf values to Tate algebra quotients, but not blocking.

**If you are working on T4:** Focus on the completeness/adic side (steps 1-4 below),
NOT on the inducing property. The `locToQuotientOneSubfX_gen_isInducing` sorry
should be DELETED or weakened to just forward continuity.

### Task

Prove the topological ring isomorphisms (Wedhorn Example 6.38):
```
presheafValue D ≅_top A⟨ζ⟩/(f-ζ)       for R(f/1)
presheafValue D ≅_top A⟨η⟩/(1-fη)      for R(1/f)
```

### Architecture decision (2026-04-02, updated 2026-04-03)

**The T-topology approach is WRONG for completeness/eval continuity.**
The T-topology (`tateTopologyT`) is induced from `∏ A` via `scaleIncl` — this
is the PRODUCT topology, which only constrains finitely many coefficients at a
time. Consequences:
- `tateAlgebra_tTopology_completeSpace` is FALSE (c₀ not closed in product)
- `evalHomBounded_continuous` is FALSE as stated (eval needs all coordinates)
- The quotient T-topology is NOT complete

**Correct approach (Wedhorn Example 6.38 + Remark 6.37):**
1. For strongly noetherian A, A⟨X⟩ is noetherian and carries the J-adic topology
   (which COINCIDES with the T-topology by Prop 6.18, but completeness comes from
   the adic side, not the product side).
2. In a noetherian Tate ring, every ideal is closed (Remark 6.37: Krull intersection
   + Artin-Rees). So `(f-ζ)` and `(1-fη)` are closed.
3. Quotient of J-adically complete by closed ideal → complete.
4. The bridge `O_X(R(T/g)) ≅ (AdicCompletion_J D)[1/π]` (T2) connects to presheafValue.

**Key notation (per reviewer):**
- `π ∈ A₀` = topologically nilpotent unit, `I = πA₀`
- `g ∈ A` = denominator of rational subset `R(T/g)`
- `D = A₀[T/g]` = ring of definition of `A[1/g]`, `J = ID = πD`
- `presheafValue D ≅ (AdicCompletion_J D)[1/π]` (NOT just AdicCompletion_J D)

### What already exists (reusable)

- `oneSubsX_not_zero_divisor` — proved, sorry-free
- `quotientTTopology_t0Space` — proved (conditional on closedness)
- `locToQuotientOneSubfX_gen_continuous` — proved, sorry-free
- `locToQuotientOneSubfX_gen_denseRange` — proved, sorry-free
- `presheafValueTateQuotientEquiv` — conditional RingEquiv (needs hcs, ht0, hcont)
- Algebraic isomorphisms: `quotientFSubXEquiv`, `quotientOneSubfXEquiv` (discrete)

### What needs to be proved (corrected approach)

1. **Noetherian Tate → ideals closed** (Remark 6.37): via Krull intersection + Artin-Rees
2. **A⟨X⟩ J-adically complete**: via identification with AdicCompletion_J(A₀[X])
3. **T-topology = J-adic on A⟨X⟩** (Prop 6.18): for strongly noetherian
4. **Quotient complete**: from (2) + (1) + quotient of complete by closed
5. **Discharge `presheafValueTateQuotientEquiv` hypotheses**: using (3)+(4)
6. **DELETE `locToQuotientOneSubfX_gen_isInducing`**: FALSE (same issue as S1)

### Acceptance criteria

- Topological ring isomorphisms proved (not just algebraic)
- Connected to existing `presheafValue` API
- Sorries have correct proof routes documented
- T5 is NOT blocked (can use filtration route independently)

---

## TICKET T5: Strictness and Topological Embedding

**Status:** NOT STARTED
**Estimated:** ~200 lines
**Blocks:** T6
**Depends on:** T1, T3, T4
**Files:** `LaurentCoverExact.lean` (extend), `TateAcyclicity.lean`

### Task

Combine algebraic exactness (T1) with open mapping (T3) and topological
identification (T4) to prove the full topological sheaf condition.

### Sub-parts

**5.1 — Laurent cover strict exactness:**
```
0 → A →ε B₁ × B₂ →δ B₁₂ → 0   (topologically exact)
```
- `δ` surjective (algebraic, from T1) + continuous + open (T3) → strict.
- `ker δ = im ε` (algebraic, from T1).
- `ker δ` closed in `B₁ × B₂` → complete.
- `ε` is continuous bijection onto `ker δ` → open (by T3 or completeness).
- Therefore `ε` is a topological embedding.

**5.2 — Product restriction is embedding:**
Transfer via topological identification (T4):
- `productRestriction : presheafValue C.base → ∏ presheafValue D`
  is a topological embedding.

**5.3 — Gluing:**
If `f ∈ ∏ presheafValue D` is compatible, it lies in the image of
`productRestriction`. Use algebraic exactness + closedness of image.

### Acceptance criteria

- `isEmbedding_productRestriction` proved
- `gluing` proved
- Connected to `IsSheafyTopRing` from `StructureSheaf.lean`
- 0 sorry

---

## TICKET T6: Assembly — Theorem 8.28(b)

**Status:** NOT STARTED
**Estimated:** ~150 lines
**Blocks:** None (final)
**Depends on:** T5
**Files:** `TateAcyclicity.lean`, `StructureSheaf.lean`, `Adic spaces.lean`

### Task

Package everything into the final `IsSheafyTopRing` instance.

### Steps

1. Define `IsStronglyNoetherianTate` if not already done (Wedhorn Def 6.36).
2. Prove rational localizations preserve strongly noetherian (Example 6.38).
3. Prove `IsSheafyTopRing A` for strongly noetherian Tate rings:
   ```lean
   instance IsStronglyNoetherianTate.isSheafyTopRing : IsSheafyTopRing A where
     isEmbedding_productRestriction := ... -- from T5
     gluing := ...                         -- from T5
   ```
4. Remove quarantined sorries in `StructureSheaf.lean` that are superseded.
5. Update imports in `Adic spaces.lean`.
6. Full `lake build` verification.

### Acceptance criteria

- `IsSheafyTopRing` instance for strongly noetherian Tate rings
- All quarantined sorries in StructureSheaf.lean resolved or removed
- Full project builds with 0 sorry in the acyclicity chain
- `lake build` passes

---

## Summary

| Ticket | Lines | Depends on | Parallel with | Difficulty |
|--------|-------|------------|---------------|------------|
| **T1** | ~200 | None | T2, T3 | Medium |
| **T2** | ~300 | None | T1, T3 | **Hard** |
| **T3** | ~150 | None | T1, T2 | Medium |
| **T4** | ~250 | T2 | — | Hard |
| **T5** | ~200 | T1, T3, T4 | — | Hard |
| **T6** | ~150 | T5 | — | Medium |
| **Total** | **~1250** | | | |

**Wave 1 (3 agents):** T1 + T2 + T3
**Wave 2 (1-2 agents):** T4, then T5
**Wave 3 (1 agent):** T6
