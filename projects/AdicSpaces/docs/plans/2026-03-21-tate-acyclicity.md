# Tate Acyclicity (Wedhorn Theorem 8.28(b)) Implementation Plan

> **For agentic workers:** REQUIRED: Use superpowers:subagent-driven-development
> (if subagents available) or superpowers:executing-plans to implement this plan.
> Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Prove that strongly noetherian Tate rings are sheafy (Wedhorn Thm 8.28(b)),
including the completed vs decompleted exactness machinery.

**Architecture:** Build Čech cohomology from scratch (not in mathlib), then follow
Wedhorn's proof chain: Tate algebra flatness → faithfully flat product restriction
→ 2-element Laurent cover exactness (the completed/decompleted diagram chase)
→ general acyclicity by induction.

**Tech Stack:** Lean 4 v4.29.0-rc3, Mathlib v4.29.0-rc3. Key mathlib deps:
`Module.Flat`, `RingHom.faithfullyFlat`, `IsNoetherian`, `ShortComplex.Exact`,
`UniformSpace.Completion`, `Localization.Away`.

**Constraint:** No `sorry` or `axiom` — everything must be fully proved.

---

## Proof Outline (Wedhorn pp.80-85)

**Theorem 8.28(b):** Let `A` be a strongly noetherian Tate affinoid ring. Then
`O_X` is a sheaf of complete topological rings on `X = Spa(A, A⁺)`.

**Proof chain:**
1. WLOG `A` is complete (Remark 8.18)
2. Every open cover has a rational refinement; every rational cover refines to
   a "standard cover" (Lemma 7.54) — reduce to standard covers
3. Standard covers are O_X-acyclic (Lemma 8.34)
4. Acyclicity on a basis ⟹ sheaf (Prop A.4)

**Lemma 8.34** (acyclicity of standard covers) uses:
- Lemma 8.33 (2-element Laurent cover exactness — **the completed/decompleted argument**)
- Prop A.3 (Čech refinement)
- Induction on covers

**Lemma 8.33** (the core) uses:
- Prop 8.30 (restriction maps are flat)
- Cor 8.32 (product restriction is faithfully flat)
- Remark 8.29 (Tate algebra module theory: M⟨X⟩ ≅ M ⊗_A A⟨X⟩)
- Lemma 8.31 (A⟨X⟩ faithfully flat, A⟨X⟩/(f-X) and A⟨X⟩/(1-fX) flat)
- A diagram chase with 3 exact rows and 3 exact columns

---

## File Structure

| File | Responsibility | New/Modify | Est. Lines |
|------|---------------|------------|------------|
| `CechCohomology.lean` | Čech complex, acyclicity, Prop A.3, A.4 | New | ~400 |
| `TateAlgebra.lean` | A⟨X⟩ module theory, Remark 8.29 | New | ~300 |
| `FlatnessResults.lean` | Prop 8.30, Lemma 8.31, Cor 8.32 | New | ~350 |
| `LaurentCoverExact.lean` | Lemma 8.33 (completed/decompleted) | New | ~400 |
| `TateAcyclicity.lean` | Lemma 8.34, Theorem 8.28(b) assembly | New | ~250 |
| `Adic spaces.lean` | Root import file | Modify | +5 |
| `StructureSheaf.lean` | Add `IsSheafy` instance | Modify | +10 |

**Total: ~1700 new lines across 5 new files**

---

## Task Breakdown

### Task 1: Čech Cohomology Infrastructure (~400 lines, 2-3 sessions)

**File: `Adic spaces/CechCohomology.lean`**

Build the Čech complex and acyclicity theory from Wedhorn Appendix A (pp.104-106).
No mathlib Čech infrastructure exists, so this is from scratch.

**Definitions to formalize:**
- `CechCochain`: q-cochains `Č^q(U, F) := ∏_{(i₀,...,i_q)} F(U_{i₀...i_q})`
- `CechCochainAlt`: alternating q-cochains `Č^q_a(U, F)`
- `cechDifferential`: differential `d^q : Č^q → Č^{q+1}`
- `AugmentedCechComplex`: `0 → F(U) →ε Č⁰(U,F) → Č¹(U,F) → ...`
- `IsAcyclic`: covering U is F-acyclic (augmented complex is exact)

**Key theorems to prove:**
- `d_comp_d_eq_zero`: d^q ∘ d^{q-1} = 0 (Appendix A basic property)
- `alt_inclusion_quasi_iso`: `Č^q_a ↪ Č^q` is a quasi-isomorphism (Appendix A)
- **Prop A.3(1)**: If V refines U and both are acyclic on all intersections,
  then U is acyclic iff V is acyclic
- **Prop A.3(2)**: If V refines U, then U acyclic iff V acyclic
- **Prop A.3(3)**: U × V is acyclic iff U is acyclic
- **Prop A.4**: Sheaf on a basis = sheaf on the space (+ acyclicity on basis
  ⟹ Ȟ^q = H^q for q ≥ 1)

**Approach:** Work concretely with `Fin`-indexed covers and product types rather
than abstract category theory. The presheaf F is our `presheafValue` from
Presheaf.lean. Covers are `RationalCovering` or a simpler `FiniteCover` type.

**Files:**
- Create: `Adic spaces/CechCohomology.lean`
- Reference: `Adic spaces/Presheaf.lean` (presheafValue, restrictionMap)
- Reference: `Adic spaces/RationalSubsets.lean` (rational open sets)

- [ ] **Step 1:** Define `FiniteCover` (simpler than `RationalCovering` — just indexed opens)
- [ ] **Step 2:** Define `CechCochain` as product over index tuples
- [ ] **Step 3:** Define `cechDifferential` with alternating signs
- [ ] **Step 4:** Prove `d_comp_d_eq_zero`
- [ ] **Step 5:** Define alternating cochains `CechCochainAlt`
- [ ] **Step 6:** Define `AugmentedCechComplex` (with augmentation ε)
- [ ] **Step 7:** Define `IsAcyclic` (exactness of augmented complex)
- [ ] **Step 8:** Prove Prop A.3(2) (refinement preserves acyclicity)
- [ ] **Step 9:** Prove Prop A.3(3) (product covers)
- [ ] **Step 10:** Prove Prop A.4 (sheaf on basis implies sheaf)
- [ ] **Step 11:** Commit

**Dependencies:** None (foundational module).

---

### Task 2: Tate Algebra Module Theory (~300 lines, 2 sessions)

**File: `Adic spaces/TateAlgebra.lean`**

Formalize Remark 8.29 of Wedhorn: for a complete noetherian Tate ring A and
a finitely generated A-module M, define M⟨X⟩ and prove
`μ_M : M ⊗_A A⟨X⟩ → M⟨X⟩` is bijective.

**Key definitions:**
- `tateAlgebra A`: the restricted power series ring `A⟨X⟩` (already partially
  in `RestrictedPowerSeries.lean`)
- `tateModule M`: the module `M⟨X⟩` of restricted power series with
  coefficients in M
- `tateModuleMap M`: the natural map `μ_M : M ⊗_A A⟨X⟩ → M⟨X⟩`

**Key theorems:**
- `tateModuleMap_bijective`: `μ_M` is bijective when A is noetherian
  (Remark 8.29). Proof: 5-lemma from presentation `A^n → A^m → M → 0`.
- `tateAlgebra_faithfullyFlat`: A⟨X⟩ is faithfully flat over A (Lemma 8.31(1)).
  Proof: faithful because A⟨X⟩/XA⟨X⟩ ≅ A; flat from noetherian + presentation.
- `tateAlgebra_quotient_flat`: A⟨X⟩/(f-X) and A⟨X⟩/(1-fX) are flat over A
  (Lemma 8.31(2)). Proof: for every f.g. A-module M, multiplication by g on
  M⟨X⟩ is injective (noetherian argument using (+) relations).

**Files:**
- Create: `Adic spaces/TateAlgebra.lean`
- Reference: `Adic spaces/RestrictedPowerSeries.lean` (existing definitions)
- Mathlib: `Module.Flat`, `RingHom.faithfullyFlat`, `IsNoetherian`,
  `TensorProduct`, `Presentation`

- [ ] **Step 1:** Define `tateModule M` (M-valued restricted power series)
- [ ] **Step 2:** Define `tateModuleMap` (μ_M : M ⊗ A⟨X⟩ → M⟨X⟩)
- [ ] **Step 3:** Prove `tateModuleMap_bijective` for free modules (base case)
- [ ] **Step 4:** Prove `tateModuleMap_bijective` for f.g. modules (5-lemma)
- [ ] **Step 5:** Prove `tateAlgebra_faithfullyFlat` (Lemma 8.31(1))
- [ ] **Step 6:** Prove Lemma 8.31(2) injectivity lemma (noetherian argument)
- [ ] **Step 7:** Prove `tateAlgebra_quotient_flat` (Lemma 8.31(2))
- [ ] **Step 8:** Commit

**Dependencies:** RestrictedPowerSeries.lean (existing), mathlib flatness API.

---

### Task 3: Flatness of Restriction Maps (~350 lines, 2 sessions)

**File: `Adic spaces/FlatnessResults.lean`**

Formalize Prop 8.30 and Cor 8.32 of Wedhorn.

**Prop 8.30:** For a strongly noetherian Tate affinoid ring (A, A⁺) and rational
subsets U ⊆ V ⊆ Spa A, the restriction map O_X(V) → O_X(U) is flat.

**Proof sketch (Wedhorn):**
- WLOG V = X and A complete
- U is either R(f/1) or R(1/f) for some f ∈ A
- O_X(R(f/1)) = Â⟨X⟩/(f-X) and O_X(R(1/f)) = Â⟨X⟩/(1-fX)
- These are flat over A by Lemma 8.31(2)

**Cor 8.32:** The product restriction O_X(X) → ∏ O_X(U_i) is faithfully flat
(and in particular injective).

**Proof:** By Lemma 8.31(1), A⟨X⟩ is faithfully flat, and the product map
factors through it.

**Files:**
- Create: `Adic spaces/FlatnessResults.lean`
- Reference: `Adic spaces/TateAlgebra.lean` (Lemma 8.31)
- Reference: `Adic spaces/Presheaf.lean` (presheafValue, restrictionMap)
- Mathlib: `Module.Flat`, `RingHom.faithfullyFlat`

- [ ] **Step 1:** State Prop 8.30 (restriction maps flat)
- [ ] **Step 2:** Prove the R(f/1) case using Lemma 8.31(2)
- [ ] **Step 3:** Prove the R(1/f) case using Lemma 8.31(2)
- [ ] **Step 4:** Assemble general Prop 8.30
- [ ] **Step 5:** Prove Cor 8.32 (product restriction faithfully flat)
- [ ] **Step 6:** Commit

**Dependencies:** Task 2 (TateAlgebra.lean).

---

### Task 4: 2-Element Laurent Cover Exactness (~400 lines, 3 sessions)

**File: `Adic spaces/LaurentCoverExact.lean`**

This is the **core** of the proof — Lemma 8.33 of Wedhorn. It proves exactness
of the augmented Čech complex for the 2-element cover {R(f/1), R(1/f)}, using
the completed vs decompleted diagram chase.

**Setup (Wedhorn p.83):**
- f ∈ A, X = Spa A
- U₁ = R(f/1) = {x : x(f) ≤ 1}, U₂ = R(1/f) = {x : x(f) ≥ 1}
- O_X(U₁) = Â⟨ζ⟩/(f-ζ), O_X(U₂) = Â⟨η⟩/(1-fη)
- O_X(U₁ ∩ U₂) = Â⟨ζ, ζ⁻¹⟩/(f-ζ) = A⟨ζ, ζ⁻¹⟩

**The augmented Čech complex:**
`0 → O_X(X) →ε O_X(U₁) × O_X(U₂) →δ O_X(U₁ ∩ U₂) → 0`

**The diagram (equation 8.2.1 + surrounding):**
```
                    0                     0
                    ↓                     ↓
(f-ζ)A⟨ζ⟩ × (1-fη)A⟨η⟩  →λ'→  (f-ζ)A⟨ζ,ζ⁻¹⟩  → 0
                    ↓                     ↓
0 → A  →ι→  A⟨ζ⟩ × A⟨η⟩      →λ→   A⟨ζ,ζ⁻¹⟩
                    ↓                     ↓
0 → A  →ε→  O_X(U₁) × O_X(U₂) →δ→  O_X(U₁∩U₂)  → 0
                    ↓                     ↓
                    0                     0
```

**Proof strategy:**
1. Columns are exact (by definition of O_X(U_i) as quotients)
2. First row: λ' is surjective (from the identity
   A⟨ζ,ζ⁻¹⟩ = A⟨ζ⟩ + ζ⁻¹A⟨ζ⁻¹⟩)
3. Second row: λ surjective and ker(λ) = im(ι) (the key algebraic identity:
   `0 = λ(∑ aₖζᵏ, ∑ bₖηᵏ)` iff `aₖ = bₖ = 0` for k > 0 and `a₀ = b₀`)
4. By diagram chase (snake lemma/5-lemma), third row is exact
5. **This gives the "decompleted" exactness** — the sequence before completion
6. Since the maps in rows 1 and 2 are continuous and open (Prop 6.18(2)),
   the completed sequence (row 3) is also exact

**This is the completed vs decompleted argument:** we prove exactness of the
algebraic (uncompleted) Čech complex, then pass to the topological completion.

**Files:**
- Create: `Adic spaces/LaurentCoverExact.lean`
- Reference: `Adic spaces/TateAlgebra.lean` (A⟨X⟩ properties)
- Reference: `Adic spaces/FlatnessResults.lean` (flatness)
- Reference: `Adic spaces/CechCohomology.lean` (IsAcyclic)
- Reference: `Adic spaces/Presheaf.lean` (presheafValue)

- [ ] **Step 1:** Define the Laurent algebra A⟨ζ, ζ⁻¹⟩
- [ ] **Step 2:** Prove A⟨ζ, ζ⁻¹⟩ = A⟨ζ⟩ + ζ⁻¹·A⟨ζ⁻¹⟩ (decomposition)
- [ ] **Step 3:** Construct map λ : A⟨ζ⟩ × A⟨η⟩ → A⟨ζ, ζ⁻¹⟩
- [ ] **Step 4:** Prove λ is surjective
- [ ] **Step 5:** Prove ker(λ) = im(ι) (the key algebraic identity)
- [ ] **Step 6:** Prove first row exact (λ' surjective)
- [ ] **Step 7:** Construct the 3×3 diagram with exact columns
- [ ] **Step 8:** Prove second row exact (from Steps 4-5)
- [ ] **Step 9:** Diagram chase: deduce third row exact (decompleted exactness)
- [ ] **Step 10:** Prove maps are open (Prop 6.18(2) — continuous and open maps
  between noetherian Tate algebra quotients)
- [ ] **Step 11:** Deduce completed exactness (row 3 = completion of row 2)
- [ ] **Step 12:** Package as `laurentCover_isAcyclic` (Lemma 8.33)
- [ ] **Step 13:** Commit

**Dependencies:** Tasks 1, 2, 3.

---

### Task 5: General Acyclicity and Assembly (~250 lines, 1-2 sessions)

**File: `Adic spaces/TateAcyclicity.lean`**

Prove Lemma 8.34 (standard covers are O_X-acyclic) and assemble
Theorem 8.28(b).

**Lemma 8.34:** Let A be a complete strongly noetherian Tate ring and U a
rational cover generated by T ⊂ A with T·A = A. Then U is O_X-acyclic.

**Proof (Wedhorn p.84):**
- (i) For f ∈ A, the cover U_f = {R(f/1), R(1/f)} is acyclic (Lemma 8.33).
  For any rational subset U = R(T/s), the restriction U_f|_U is acyclic
  by the same argument applied to O_X(U) (which is again a strongly
  noetherian Tate ring by Example 6.38).
- (ii) Laurent covers (generated by units) refine to Laurent covers where
  U|_{V_j} is generated by units for all j.
- (iii) Every rational cover has a Laurent cover refinement.
- (iv) Combine (i)-(iii) with Prop A.3 to get acyclicity.

**Theorem 8.28(b):** Standard covers are acyclic (Lemma 8.34) + Prop A.4
(sheaf on basis) ⟹ IsSheafyTopRing.

**Files:**
- Create: `Adic spaces/TateAcyclicity.lean`
- Modify: `Adic spaces/StructureSheaf.lean` (add IsSheafy instance)
- Modify: `Adic spaces.lean` (add imports)
- Reference: `Adic spaces/LaurentCoverExact.lean` (Lemma 8.33)
- Reference: `Adic spaces/CechCohomology.lean` (IsAcyclic, Prop A.3, A.4)

- [ ] **Step 1:** Define `IsStronglyNoetherian` (a Tate ring whose ring of
  definition is noetherian, and remains so after topologically finite type
  base change)
- [ ] **Step 2:** Prove rational localizations of strongly noetherian Tate rings
  are strongly noetherian (Example 6.38 / Lemma 2.13 of Zavyalov)
- [ ] **Step 3:** Define Laurent covers and prove they are acyclic (from Lemma 8.33)
- [ ] **Step 4:** Prove Laurent cover refinement (Lemma 8.34(ii)-(iii))
- [ ] **Step 5:** Prove Lemma 8.34 (standard covers acyclic) by induction
- [ ] **Step 6:** Prove `IsStronglyNoetherian.isSheafyTopRing` (Theorem 8.28(b))
  using Lemma 8.34 + Prop A.4
- [ ] **Step 7:** Add `IsSheafy` instance to StructureSheaf.lean
- [ ] **Step 8:** Add imports to `Adic spaces.lean`
- [ ] **Step 9:** Full build verification
- [ ] **Step 10:** Commit

**Dependencies:** Tasks 1, 4.

---

## Dependency Graph

```
Task 1: CechCohomology ─────────────────────────────┐
                                                      │
Task 2: TateAlgebra ──→ Task 3: FlatnessResults ──→ Task 4: LaurentCoverExact
                                                      │
                                                      ↓
                                                Task 5: Assembly
```

Tasks 1 and 2 can run in parallel. Task 3 depends on 2. Task 4 depends on 1+2+3.
Task 5 depends on 1+4.

---

## Critical Mathematical Details

### The completed vs decompleted exactness argument (Lemma 8.33)

This is the heart of the proof. The key insight:

**Decompleted level:** The sequence `0 → A →ι A⟨ζ⟩ × A⟨η⟩ →λ A⟨ζ,ζ⁻¹⟩ → 0`
is exact by direct algebraic computation (writing power series as sums of
positive and negative parts).

**Completed level:** The sequence `0 → A →ε O_X(U₁) × O_X(U₂) →δ O_X(U₁∩U₂) → 0`
is the quotient of the middle row by the first row (which consists of the
defining ideals `(f-ζ)A⟨ζ⟩` and `(1-fη)A⟨η⟩`).

**The passage:** Since A is noetherian and the maps ι, λ are continuous and
open (Prop 6.18(2) — surjective maps between noetherian A-modules with the
canonical topology are open), the completed sequence inherits exactness.
This uses that completion preserves short exact sequences of topological
modules when the maps are strict (= continuous + open onto image).

### Prop 6.18(2) (open mapping theorem for Tate algebras)

For a **noetherian** Tate ring A and finitely generated A-modules M, N:
any surjective A-linear map u : M → N (with canonical topologies from
Prop 6.18(1)) is open.

**This needs to be formalized** — it's essentially the open mapping theorem
for I-adic modules over noetherian rings, which follows from the
Artin-Rees lemma.

### Artin-Rees Lemma

Mathlib has `Ideal.mem_iInf_smul_pow_eq_bot_iff` and related Krull intersection
results, but the Artin-Rees lemma itself (`∃ c, I^n M ∩ N ⊆ I^{n-c} N` for
f.g. submodules N ⊆ M over noetherian rings) needs to be checked.

---

## Risk Assessment

| Risk | Severity | Mitigation |
|------|----------|------------|
| Artin-Rees not in mathlib | High | Check; if missing, prove (~50 lines) |
| Laurent algebra A⟨ζ,ζ⁻¹⟩ construction | Medium | Use `MvPowerSeries` or define directly |
| Diagram chase formalization | Medium | Use mathlib's `ShortComplex.Exact` |
| Open mapping for Tate modules | High | Need Prop 6.18(2); derives from Artin-Rees |
| Completion preserving exact sequences | High | Need strict morphism theory |
| `RestrictedPowerSeries.lean` maturity | Medium | May need extension |

---

## Estimated Effort

| Task | Lines | Sessions | Difficulty |
|------|-------|----------|------------|
| 1: CechCohomology | ~400 | 2-3 | Medium |
| 2: TateAlgebra | ~300 | 2 | Hard |
| 3: FlatnessResults | ~350 | 2 | Hard |
| 4: LaurentCoverExact | ~400 | 3 | **Very Hard** |
| 5: Assembly | ~250 | 1-2 | Medium |
| **Total** | **~1700** | **10-13** | |

---

## Session Plan

| Session | Tasks | Goal |
|---------|-------|------|
| 1-2 | Task 1 (partial) | Čech complex defs + differential |
| 3 | Task 1 (complete) + Task 2 (start) | Prop A.3, A.4 + tateModule defs |
| 4-5 | Task 2 | Remark 8.29 + Lemma 8.31 |
| 6-7 | Task 3 | Prop 8.30 + Cor 8.32 |
| 8-9 | Task 4 (partial) | Laurent algebra + decompleted exactness |
| 10 | Task 4 (complete) | Completed exactness (open mapping + completion) |
| 11-12 | Task 5 | Lemma 8.34 + Theorem 8.28(b) assembly |
| 13 | Cleanup | Style, lint, decomposition |

---

## Prerequisite Infrastructure to Verify

Before starting, verify these mathlib APIs exist:

1. `Module.Flat` — flat modules ✓
2. `RingHom.faithfullyFlat` — faithfully flat ✓
3. `IsNoetherian` / `IsNoetherianRing` — ✓
4. `TensorProduct` — ✓
5. `Ideal.artinRees` or equivalent — **CHECK**
6. `ShortComplex.Exact` — ✓
7. `UniformSpace.Completion.map` preserving properties — partially ✓
8. Strict morphisms / open mapping — **CHECK if `IsOpenMap` + completion API exists**
