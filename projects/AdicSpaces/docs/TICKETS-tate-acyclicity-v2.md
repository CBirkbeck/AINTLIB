# Tate Acyclicity v2 — Tickets for the NON-DISCRETE Case

**Master goal:** Prove Wedhorn Theorem 8.28(b) for **non-discrete** strongly
noetherian Tate rings: `O_X` is a sheaf of complete topological rings.

**Constraint:** No `sorry` or `axiom`.

---

## Completed infrastructure (reusable from v1 + gaps)

| What | File | Status |
|------|------|--------|
| Cech complex + d∘d=0 | CechCohomology.lean | DONE (general) |
| Cech refinement + basis-sheaf | CechCohomology.lean | DONE (general) |
| Noetherian Tate module topology (Prop 6.18) | NoetherianTateModules.lean | DONE (general) |
| TateAlgebra definitions (Laurent, etc.) | TateAlgebra.lean | DONE (general algebraic defs) |
| Product topology on A⟨X⟩ | TateAlgebraTopology.lean | DONE (but WRONG for eval maps) |
| I-adic topology on A₀⟨X⟩ | TateAlgebraTopology.lean | DONE (G1) |
| Completion preserves strict exact seqs | CompletionExact.lean | DONE (G3) |
| Algebraic presheaf identification | PresheafIdentification.lean | DONE (G2 algebraic) |
| Discrete flatness + Laurent exactness | TateAlgebra + FlatnessResults + LaurentCoverExact | DONE (discrete only) |

## Key design issue (from reviewer)

The product topology on `TateAlgebra A` makes `X^n → 0`. A continuous map
`TateAlgebra A → presheafValue D` sending `X ↦ 1/f` would force `(1/f)^n → 0`,
i.e., `1/f` topologically nilpotent. This is NOT correct for `R(1/f)`.

**Resolution:** For algebraic results (flatness, kernel identification), topology
doesn't matter. For topological results (continuity, strict exactness), need
Wedhorn's T-topology (Definition 5.48) on a separate object. Split accordingly:
- R-2B, R-3: use algebraic identification (unblocked NOW)
- R-4, R-5: need correct topology (separate ticket G2-topo)

---

## Agent Coordination Protocol

Same rules as v1. Update tracker before starting, commit claim, update when done.

## Tracker

| Ticket | Status | Agent | Started | Completed | Notes |
|--------|--------|-------|---------|-----------|-------|
| G1 | DONE | claude-main | 2026-03-23 | 2026-03-23 | I-adic on A₀⟨X⟩ |
| G2-alg | DONE | claude-main | 2026-03-23 | 2026-03-23 | Algebraic identification |
| G2-topo | IN PROGRESS | claude-main | 2026-03-24 | — | Plan: docs/plans/2026-03-24-G2-topo-plan.md |
| G3 | DONE | claude-opus | 2026-03-23 | 2026-03-23 | Completion exact seqs |
| R-2B | DONE | claude-main | 2026-03-23 | 2026-03-24 | tateAlgebra_flat proved (0 sorry) |
| R-3 | DONE | claude-main | 2026-03-24 | 2026-03-24 | Lemma 8.31(2) all proved (0 sorry) |
| R-4 | NOT STARTED | — | — | — | Lemma 8.33 strict. Depends: R-2B, R-3, G2-topo, G3 |
| R-5 | NOT STARTED | — | — | — | Assembly. Depends: R-3, R-4, TICKET-1B |

## Dependency Graph

```
G2-alg (DONE) ──→ R-2B (Lemma 8.31) ──→ R-3 (Prop 8.30)
                                              │
G2-topo + G3 (DONE) ────────────────→ R-4 (Lemma 8.33 strict)
                                              │
                            R-3 + R-4 ──→ R-5 (assembly)
```

**R-2B and R-3 are UNBLOCKED** (only need G2-alg which is done).
R-4 needs G2-topo (the correct topological model).

---

## TICKET-R-2B: Lemma 8.31 — Non-Discrete Tate Algebra Flatness

**Status:** NOT STARTED
**Estimated:** ~300 lines
**Blocks:** R-3
**Depends on:** G2-alg (DONE)
**File:** `Adic spaces/TateAlgebra.lean` (add non-discrete section)

### What to prove

Same theorems as the discrete versions, but without `[DiscreteTopology A]`.
The proofs use the ALGEBRAIC identification from G2-alg.

**Lemma 8.31(1): A⟨X⟩ is faithfully flat over A.**
- Already have `noeth_zero_of_mul_shift` (general, no discrete needed)
- Already have `evalZeroHom_surjective` (general)
- Need: `μ_M : M ⊗_A A⟨X⟩ → M⟨X⟩` bijective (Remark 8.29)
- Then flat via tensor criterion, faithful via `A⟨X⟩/(X) ≅ A`

**Lemma 8.31(2): A⟨X⟩/(f-X) and A⟨X⟩/(1-fX) are flat over A.**
- Already have regularity of `f-X` and `1-fX` (general)
- Use: quotient by regular element of a flat algebra is flat
  (general algebra: `A⟨X⟩` flat + regular element → quotient flat)

### Key: what's already general in TateAlgebra.lean

- `mul_fSubX_regular` (~line 939): `f-X` is a non-zero-divisor (needs `[IsNoetherianRing A]` only)
- `mul_oneSubfX_regular` (~line 986): `1-fX` is a non-zero-divisor
- `noeth_zero_of_mul_shift` (~line 540): ascending chain argument
- `ker_evalZeroHom` (~line 530): kernel of eval at 0 = (X)

### What's missing

- `M⟨X⟩` definition and `μ_M` (Remark 8.29) — can be defined using product topology
- Flatness criterion: flat algebra + quotient by regular element → flat quotient
  (check mathlib: `Module.Flat.of_quotient_by_regular` or similar)
- Faithful flatness: `A⟨X⟩/(X) ≅ A` + flat → faithful

---

## TICKET-R-3: Prop 8.30 + Cor 8.32 — Non-Discrete Restriction Flatness

**Status:** NOT STARTED
**Estimated:** ~200 lines
**Blocks:** R-4, R-5
**Depends on:** R-2B, G2-alg (DONE)
**File:** `Adic spaces/FlatnessResults.lean` (add non-discrete section)

### What to prove

**Prop 8.30:** For rational U ⊆ V ⊆ Spa A, `O_X(V) → O_X(U)` is flat.
- WLOG V = X, A complete
- Use Wedhorn Remark 7.55: decompose into R(f/1) and R(1/f) steps
- `presheafValue D ≅ A⟨X⟩/(f-X)` or `A⟨X⟩/(1-fX)` ALGEBRAICALLY (from G2-alg)
- Flat by R-2B (Lemma 8.31(2))

**Cor 8.32:** Product restriction `A → ∏ O_X(U_i)` is faithfully flat.
- Flat: finite products of flat algebras are flat (already proved: `Module.Flat.pi`)
- Faithful: induced map on spectra surjective (covering condition)

### Key bridge

The algebraic isomorphism `presheafValue D ≃+* TateAlgebra A ⧸ (1-fX)` from
G2-alg allows transferring flatness: `TateAlgebra A ⧸ (1-fX)` is flat by R-2B,
and flatness transfers along ring isomorphisms.

---

## TICKET-G2-topo: Correct Topological Model for Evaluation (FUTURE)

**Status:** NOT STARTED
**Estimated:** ~300 lines
**Blocks:** R-4
**File:** `Adic spaces/TateAlgebraWedhorn.lean` (new)

### Context

The product topology on `TateAlgebra A` is WRONG for evaluation maps
(X^n → 0 forces invS topologically nilpotent). Need Wedhorn's T-topology
(Definition 5.48, Remark 5.47).

### What to build

1. Define `TateAlgebraT A T` with Wedhorn's T-topology where neighborhoods
   are `{∑ aᵥ Xᵥ : aᵥ ∈ Tᵥ U}` for open subgroups U of A
2. Prove `A[X]_T` is dense (Prop 5.49(1))
3. Prove `A⟨X⟩_T` = completion of `A[X]_T` (Prop 5.49(3))
4. The evaluation `ev: A[X]_T → A_f` is continuous (1/f power-bounded)
5. Extend via `IsDenseInducing.extendRingHom` to `A⟨X⟩_T → presheafValue D`
6. Identify kernel = (1-fX), surjective
7. Topological ring isomorphism `A⟨X⟩_T/(1-fX) ≃ₜ presheafValue D`

### Mathlib tools

- `IsDenseInducing.extendRingHom` for dense extension
- `HasSum.mul_of_nonarchimedean` for Cauchy products
- `NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero` for convergence

---

## TICKET-R-4: Lemma 8.33 Strict Laurent Cover Exactness (FUTURE)

**Status:** NOT STARTED
**Estimated:** ~350 lines
**Blocks:** R-5
**Depends on:** R-2B, R-3, G2-topo, G3
**File:** `Adic spaces/LaurentCoverExact.lean` (add non-discrete section)

### Needs G2-topo

The 3×3 diagram chase requires all maps to be **strict** (continuous + open
onto image). This needs the correct topology from G2-topo, not the product
topology. The algebraic exactness is the same as the discrete case; the
topological upgrade uses Prop 6.18(2) from NoetherianTateModules.lean.

---

## TICKET-R-5: Assembly — Lemma 8.34 + Theorem 8.28(b) (FUTURE)

**Status:** NOT STARTED
**Estimated:** ~250 lines
**Blocks:** None (final)
**Depends on:** TICKET-1B, R-3, R-4
**File:** `Adic spaces/TateAcyclicity.lean` (rewrite)

### Output

```lean
instance IsStronglyNoetherianTate.isSheafyTopRing : IsSheafyTopRing A where
  isEmbedding_productRestriction := ...  -- from R-4
  gluing := ...                          -- from R-4 + R-3
```

---

## Summary

| Ticket | Lines | Depends on | Status | Difficulty |
|--------|-------|------------|--------|------------|
| **R-2B** | ~300 | G2-alg (DONE) | **UNBLOCKED** | Hard |
| **R-3** | ~200 | R-2B, G2-alg | **UNBLOCKED after R-2B** | Medium |
| G2-topo | ~300 | G1 (DONE) | Future | Very Hard |
| R-4 | ~350 | R-2B, R-3, G2-topo, G3 | Future (needs G2-topo) | Very Hard |
| R-5 | ~250 | 1B, R-3, R-4 | Future (needs R-4) | Medium |

**Immediate action:** R-2B and R-3 are unblocked. R-4 and R-5 await G2-topo.
