# Adversarial decompose audit (round 2) — post-Session-25 state

*Session 26, 2026-05-18. Goal: stress-test the IsSheafy chain AFTER Path α + CompleteSpace + new noeth-pair-propagation lemma. Apply the new proof-hypothesis ledger + taint-pattern methodology from the round-3 reviewer reply.*

*Scope: critical path A3 → leaves. Apply 4-column ledger to each leaf on the path.*

---

## RED FLAGS (round 2)

### Red flag #1 — `productRestrictionSub_isInducing_tate` (B6) is the IsDomain leak

**Current B6 signature** (StructureSheaf.lean:1356):
```
B6 : [IsTateRing A] [IsNoetherianRing A] [IsStronglyNoetherian A] [T2Space A]
     [NonarchimedeanRing A]
     (C : RationalCovering A) :
     Topology.IsInducing (productRestrictionSub A C)
```

**No IsDomain. No `(P, [IsNoetherianRing P.A₀])`. No CompleteSpace.**

**Discharge route (per project plan)**: B6 = Lane C single-step closer (done) + F4 (refinement tree).

**F4 signature** (TateAcyclicityResiduals.lean:1830):
```
F4 : [IsTateRing A] [IsNoetherianRing A] [IsStronglyNoetherian A] [T2Space A]
     [NonarchimedeanRing A] [IsDomain A] [DecidableEq A]
     (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
     (C : RationalCovering A) : ...
```

**Proof-hypothesis ledger for B6**:

| Column | Content |
|--------|---------|
| Statement hypotheses | strong noeth Tate + T2 + NonarchimedeanRing |
| Source hypotheses (Wedhorn 8.34) | strong noeth Tate + T·A=A |
| Proof-route hypotheses (via F4) | strong noeth Tate + T2 + NonarchimedeanRing + **IsDomain** + **DecidableEq** + **(P, IsNoetherianRing P.A₀)** |
| Downstream hypotheses (consumers of B6) | A3 (no IsDomain), A1/A2 (yes IsDomain) |

**Mismatch: 3 hypotheses in column 3 not in column 1** (IsDomain, DecidableEq, (P, noeth A_0)).

This is exactly the bug the new ledger methodology was designed to catch. The mismatch was hidden because B6's body is `sorry` — Lean doesn't type-check the body's hypotheses against the signature unless we try to fill it.

**Resolution required** (one of):
- (a) Add `[IsDomain A] [DecidableEq A] (P : PairOfDefinition A) [IsNoetherianRing P.A₀]` to B6's signature. Cascades to A3 (which doesn't have them). Either A3 also adds them (but reviewer said remove IsDomain from final) or A3 gets a different discharge route.
- (b) Refactor F4 to be IsDomain-free (per Q-S24.3 the math allows it; the project's machinery uses domain cancellation in ratio splits = taint pattern #5).
- (c) Replace B6's intended F4-discharge with F5 (the IsDomain-free target) — but F5 is itself sorry and has worse problems (Red Flag #3 below).

### Red flag #2 — `presheafValue_pairOfDefinition_isNoetherian` depends on a mathlib gap

The new lemma (just added Session 25):
```
presheafValue_pairOfDefinition_isNoetherian
  (P : PairOfDefinition A) [IsNoetherianRing P.A₀] (D₀ : RationalLocData A)
  [IsNoetherianRing (locSubring D₀.P D₀.T D₀.s)] :
  IsNoetherianRing ↥(presheafValue_pairOfDefinition_concrete P D₀).A₀
```

Discharge plan in docstring: "Hilbert basis + Stacks 0316 (`AdicCompletion.isNoetherianRing`)".

**Mathlib audit result**: mathlib has `AdicCompletion.flat_of_isNoetherian` (flatness of completion over noeth ring) and `AdicCompletion.map_exact` (exactness, = Stacks 00MA) but **NOT** `AdicCompletion.isNoetherianRing` (= Stacks 0316).

**Therefore the discharge plan for `presheafValue_pairOfDefinition_isNoetherian` is blocked on a mathlib gap that estimated at ~150 LOC (per existing T-MATHLIB-STACKS-00MA ticket).**

This is the **same** mathlib gap as E3 (`_sub_lemma_L5_1_2_adicCompletion_noetherian` in WedhornStronglyNoetherian.lean). The Session-25 lemma essentially re-discovered the same gap under a different name.

**Resolution required**:
- (a) Discharge the underlying mathlib gap (`AdicCompletion.isNoetherianRing` = ~150 LOC including supporting `IsAdic`-API). Then both `presheafValue_pairOfDefinition_isNoetherian` and E3 become provable.
- (b) Take `[IsNoetherianRing (presheafValue_ringOfDef D₀)]` as an additional hypothesis (parameterise around the gap). Cascades into A3 / C1 / C2.

### Red flag #3 — F5's discharge plan references the DELETED B2

F5 (`exists_wedhorn_ratio_laurent_refinement_tree_realized_clean`) docstring at TateAcyclicityResiduals.lean:1850–1862 says:

> Discharge plan:
> * `(P)` + `[IsNoetherianRing P.A₀]`: derive via `IsTateRing.principalPair A` + `isNoetherianRing_principalPair_A₀_of_stronglyNoetherianTate` (StructureSheaf.lean, audit pass-2).
> * `[IsDomain A]`: NOT derivable from strong-noeth Tate in general.
> * Fix: replace with audit pass-3 `laurentCover_exact_general`.

**Problem**: `isNoetherianRing_principalPair_A₀_of_stronglyNoetherianTate` was **DELETED in Session 21** as false. F5's discharge plan is referencing a deleted lemma.

**Taint pattern hit**: pattern #1 (`strong noeth A ⇒ noeth A_0`) — exactly the pattern the round-3 reviewer warned about.

**Resolution required**:
- F5 should be restated to take `(P, [IsNoetherianRing P.A₀])` parametrically (per Path α).
- Its docstring needs updating to remove the reference to the deleted lemma.
- The "[IsDomain A]: NOT derivable" gap remains — F5 either keeps IsDomain or needs the F4-machinery IsDomain-free refactor.

### Red flag #4 — A3's discharge through B6 has no IsDomain-free route

Following the chain backward from A3:
- A3 (no IsDomain) ← B6 + B7 + B8 + IsSheafy combinator
- B6 ← F4 (has IsDomain) OR F5 (has discharge problems per #3)
- Lane C single-step closer (the other B6 ingredient) is done — sorry-free — let me re-verify it doesn't sneak in IsDomain... actually it might via the project's `RatioLaurentTree` / ratio-split machinery, which is intrinsically domain-flavoured per Q-S24.3.

**Net**: A3 cannot be discharged through any existing project route without IsDomain. The reviewer's prescription "remove IsDomain from final target" requires either:

- (a) Refactor the entire F-chain (F4, F7–F10) + Lane C ratio-split machinery to be IsDomain-free. Per Q-S24.3 reviewer reply, this means switching to "ratios of units in `O(V_j)`" instead of domain cancellation. **Substantial new infrastructure** (~200–300 LOC).
- (b) Add IsDomain back to A3 and admit Path α produces "Wedhorn 8.28(a)(b) for domain strongly noeth Tate" — narrower than the reviewer wanted but matches existing infrastructure.

### Red flag #5 — C2's import-cycle resolution still not architected

C2 (`cor_8_32_clean`) body has comment:
> Cannot delegate to `productRestriction_faithfullyFlat_tate_of_hSpa_points` because that lives in `Cor832.lean` which imports this file (cycle). Discharge requires writing a fresh combinator in TateAcyclicityFinalAssembly that consumes hSpa_surj_cover_level (cover-level form) + C1's flatness.

That fresh combinator does NOT exist. TateAcyclicityFinalAssembly.lean currently has 0 sorries — meaning it has none of the planned C2 assembly.

When the worker picks up C2, they'll find they need to:
1. First write the combinator in TateAcyclicityFinalAssembly (~80–100 LOC)
2. Wire C2 to invoke it
3. Verify the chain works

**Resolution required**: pre-write the combinator skeleton (~30 LOC of signature + `sorry` body) so the worker has a clear target.

### Red flag #6 — Topological typeclass cascade for `presheafValue D`

C1 / C2 / B5' / A3 now have `[UniformSpace A] [IsUniformAddGroup A] [CompleteSpace A]`. But to invoke these at the `presheafValue D` level (e.g., for the Ex-6.38 propagation), we need:
- `[UniformSpace (presheafValue D)]`
- `[IsUniformAddGroup (presheafValue D)]`
- `[CompleteSpace (presheafValue D)]`

**Are these derivable from the corresponding hypotheses on A?**

- `presheafValue D = UniformSpace.Completion (Localization.Away D.s, localization-topology)`. Completion of UniformSpace gives a UniformSpace. ✓
- `IsUniformAddGroup` on Completion of UAG: mathlib has `UniformSpace.Completion.isUniformAddGroup` or similar. ✓ probably
- `CompleteSpace` of Completion: ✓ by definition (`UniformSpace.Completion.completeSpace`)

So the propagation should be automatic via instance synthesis. But **none of these instances are currently exposed on `presheafValue D` in the project** (I haven't seen them in the files I've read). When the worker tries to apply C1 at the `presheafValue D` level, they may get instance synthesis failures.

**Resolution required**: verify (or write) the typeclass instances for `presheafValue D` (Uniform Space, IsUniformAddGroup, CompleteSpace) propagate from the corresponding instances on A.

### Red flag #7 — The new noeth-pair-propagation lemma requires `[IsNoetherianRing (locSubring D₀.P D₀.T D₀.s)]`

The new lemma's signature:
```
(P : PairOfDefinition A) [IsNoetherianRing P.A₀]
(D₀ : RationalLocData A) [IsNoetherianRing (locSubring D₀.P D₀.T D₀.s)]
```

The second typeclass `[IsNoetherianRing (locSubring D₀.P D₀.T D₀.s)]` is non-trivial. `locSubring` is a subring of `Localization.Away D₀.s` constructed inside the project. Its noetherianity is presumably another instance we need.

**Is this instance derivable from `[IsNoetherianRing P.A₀]`?** Per the standard story: `locSubring` = subring of Localization.Away generated by `A_0[T/s]`-images. Noetherianity follows from finite-type-over-noeth + Hilbert basis — same Stacks 0316 dance.

So Red Flag #7 is a precondition of Red Flag #2 — we need `[IsNoetherianRing (locSubring ...)]` to use the new lemma, and that itself probably needs the same mathlib gap.

**Resolution required**: either supply `[IsNoetherianRing (locSubring ...)]` as additional hypothesis on every C1/C2/B5'/A3 call (cascading), or write the project-internal infrastructure to derive it (which loops back to Red Flag #2).

---

## Taint-pattern audit

Per the round-3 reviewer's 5 taint patterns, the remaining IsSheafy chain leaves should be cross-checked. Quick scan:

| Pattern | Hit by |
|---------|--------|
| (1) strong-noeth A ⇒ noeth A_0 | F5 docstring (Red Flag #3) |
| (2) single-restriction injective/surjective | G1/G2 deleted; check if any leaf still computes "single restriction is X" — none surfaced in this pass |
| (3) completed loc is algebraic IsLocalization | `restrictionMap_isLocalization` deleted; check if any leaf re-derives "Spec of completed loc = Spec of localization" — none surfaced |
| (4) S ⊆ A spanning A | F1/F2/F3 still have this form (legacy quarantined). Restated F2 is relative-over-O(C.base) but not yet propagated to F1/F3/F4. |
| (5) domain cancellation in ratio splits | F4 + Lane C ratio-split machinery + the `RatioLaurentTree` infrastructure all use this (Red Flags #1 + #4) |

---

## Net assessment

The Session-25 changes improved the architecture but introduced THREE new gaps:
1. **B6 IsDomain leak** (statement-vs-proof mismatch surfaced by the new ledger)
2. **Stacks 0316 mathlib gap** as a hard prerequisite of `presheafValue_pairOfDefinition_isNoetherian`
3. **F5 discharge plan references deleted lemma**

Plus three pre-existing gaps that the reviewer's verdict highlighted as still-open:
4. C2 import-cycle combinator not pre-written
5. Topological typeclass cascade for `presheafValue D` not verified
6. `locSubring` noetherianity is a sub-prerequisite

When work starts on the priority targets:

- **C1 (`prop_8_30_flat_clean`)** — will hit Red Flag #6 (need `[UniformSpace (presheafValue D)]` etc.) and Red Flag #7 (`locSubring` noetherianity) on first attempt. Each is a sub-ticket.
- **C2 (`cor_8_32_clean`)** — will hit Red Flag #5 (need combinator first).
- **F4 / F5** — will hit Red Flag #1 (IsDomain leak), Red Flag #3 (F5 discharge plan invalid).
- **`presheafValue_pairOfDefinition_isNoetherian`** — will hit Red Flag #2 (Stacks 0316 gap = ~150 LOC mathlib work). Not actually a quick-win; it's a multi-session project.

---

## Recommended user decisions

### D1: IsDomain on A3 — bite the bullet

Add `[IsDomain A]` to A3 (and to the full Wedhorn-clean chain B5'/C1/C2). Per Q-S24.3 the math allows IsDomain-free, but the project's existing infrastructure (F4 + Lane C ratio-splits) uses it, and refactoring the ratio-split machinery is ~200-300 LOC of new work that's NOT on the IsSheafy critical path.

**Alternative**: keep A3 IsDomain-free as aspirational, and accept that the project's INSTANCE / DISCHARGEABLE versions are the IsDomain ones (A1, A2).

### D2: Stacks 0316 as a separate mathlib-side project

`presheafValue_pairOfDefinition_isNoetherian` is **NOT** a quick win — it has a ~150 LOC mathlib prerequisite. Either:
- (a) Treat it as a multi-session project (write the mathlib gap, then close the project lemma)
- (b) Parameterise around it: take `[IsNoetherianRing (presheafValue_ringOfDef D)]` as additional hypothesis on every C1/C2/B5'/A3 call.

(b) keeps the project moving without waiting for mathlib work; (a) is the honest mathlib-faithful path.

### D3: F5 needs restatement

Update F5 to take `(P, [IsNoetherianRing P.A₀])` parametrically. Remove the docstring reference to the deleted B2.

### D4: Pre-write C2's downstream combinator skeleton

In TateAcyclicityFinalAssembly.lean, add a sorry-bodied `cor_8_32_via_downstream_combinator` taking C1 + hSpa_surj_cover_level as hypotheses. Then C2's body delegates to it (via import-cycle-breaker).

### D5: Verify `presheafValue D` topological instances

Add a small section in PresheafTateStructure or a new file: provide `[UniformSpace (presheafValue D)]`, `[IsUniformAddGroup (presheafValue D)]`, `[CompleteSpace (presheafValue D)]` instances derived from the corresponding instances on A.

---

## What this enables when work starts

After applying D1–D5:
- C1 ticket can pick up cleanly: all typeclasses synthesise, F4-via-IsDomain available, discharge plan executable.
- F4 ticket can pick up cleanly: signature matches reality.
- `presheafValue_pairOfDefinition_isNoetherian` becomes either (a) a sub-project or (b) parameterised away — either is a clean decision.

**Without D1–D5**: workers will hit instance-synthesis failures and need to redo the architecture decisions made in this audit during implementation. That's the "unexpected blockage" the user wanted to prevent.
