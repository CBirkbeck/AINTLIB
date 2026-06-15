# Plan: Sheafiness of Strongly Rigid-Noetherian Huber Pairs (Zavyalov)

## Reference

Bogdan Zavyalov, *Sheafiness of Strongly Rigid-Noetherian Huber Pairs*, arXiv:2102.02776v2.

**Main Theorem (Thm 3.5 = Thm 1.1):** Let `(A, A⁺)` be a strongly rigid-noetherian
Huber pair. Then `O_X` is a sheaf of topological rings on `X = Spa(A, A⁺)`.
Furthermore, `H^i(U, O_X) = 0` for any rational subdomain `U ⊂ X` and `i ≥ 1`.

This answers Scottish Book Problem 31 (David Hansen).

---

## What We Already Have

| Component | File | Status |
|-----------|------|--------|
| `PairOfDefinition`, `IsHuberRing`, `IsTateRing` | HuberRings.lean | Complete |
| `IsSheafy`, `IsSheafyTopRing` (definitions) | StructureSheaf.lean | Defined, discrete case proved |
| `presheafValue`, `restrictionMap` | Presheaf.lean | Complete, continuous |
| `RationalCovering`, `productRestriction` | Presheaf.lean, StructureSheaf.lean | Complete |
| Rational subsets, openness, finite intersections | RationalSubsets.lean | Complete |
| Localization topology on `A_s` | LocalizationTopology.lean | Complete |
| `CompleteTopCommRingCat` | CompleteTopCommRingCat.lean | Complete |
| Affinoid rings, `PlusSubring` | AffinoidRings.lean, AdicSpectrum.lean | Complete |

**Critical gap:** `IsSheafy` / `IsSheafyTopRing` only proved for `[DiscreteTopology A]`.

---

## What Zavyalov's Paper Requires

### Definitions to formalize (Section 2)

1. **Restricted power series** `A₀⟨X₁,...,X_d⟩` (the `I`-adic completion of `A₀[X₁,...,X_d]`)
2. **Topologically universally rigid-noetherian** (Def 2.8):
   `(A₀, I)` is top. univ. rigid-noetherian if `Spec A₀⟨X₁,...,X_d⟩` is noetherian
   outside `V(I · A₀⟨X₁,...,X_d⟩)` for every `d ≥ 0`.
3. **Strongly rigid-noetherian** Huber ring (Def 2.8):
   `A` admits a pair of definition `(A₀, I)` that is top. univ. rigid-noetherian.
4. **Pseudo-adhesive** / **universally pseudo-adhesive** pair `(A, I)` (Def 2.14):
   `Spec A` noetherian outside `V(I)` and finite `A`-modules have bounded `I`-torsion.
5. **FP-approximated** sheaves/modules (Def A.1):
   Weak isomorphism from finitely presented, with kernel/cokernel killed by `I^n`.
6. **Strict** morphism of topological groups (Def 3.3).
7. **Standard covering** of `Spa(A, A⁺)` (Def 3.2).

### Key lemmas (Section 2)

| Ref | Statement | Dependencies | Difficulty |
|-----|-----------|--------------|------------|
| 2.10 | Def independent of choice of `(A₀, I)` | Huber ring theory | Medium |
| 2.11 | Complete analytic = strongly rigid-noetherian | Kedlaya [Ked17] | Medium |
| 2.12 | Complete microbial valuation ring → s.r.n. for TFT algebras | [Bos14] | Medium |
| 2.13 | Rational localizations preserve s.r.n. | Completion, surjection | Medium |
| 2.16 | Complete top. univ. r.n. → universally pseudo-adhesive | [FK18] | **Axiomatize** |

### Key lemmas (Section 3 — the proof)

| Ref | Statement | Dependencies | Difficulty |
|-----|-----------|--------------|------------|
| 3.1 | Open covering refines to standard covering | [Hub94] Lemma 2.6 | Easy |
| Step 0 | Reduce to `A` complete | Completion isomorphism | Easy |
| Step 1 | Reduce to `C•_aug` exact with strict differentials | Čech–derived spectral seq | Medium |
| Step 2 | "Decompleted" `C_aug` is exact | Projective schemes, [Bon98] | **Hard** |
| Step 3 | Differentials `d^i : C^i_aug → ker d^{i+1}` are open | Ring of definition embedding | Hard |
| Step 4 | Differentials `δ^i : K^i → ker δ^{i+1}` are open | FP-approximation (Appendix A) | **Very hard** |
| Claim 1 | `g: P → S` is isomorphism away from `V(I)` | [Hub93] Lemma 3.7 | Medium |
| Claim 2 | `I^c · H^{i+1}(P, I^k O_P) = 0` | Theorem A.5 + Lemma A.2 | Hard |

### Appendix A — FP-approximated sheaves

| Ref | Statement | Dependencies | Difficulty |
|-----|-----------|--------------|------------|
| A.2 | FP-approximated → bounded I^∞-torsion | Definition | Easy |
| A.3 | FP-approx closed under sub/quotient/kernels | [FK18] | Medium |
| A.4 | Closed immersion preserves FP-approx | A.3(1) | Easy |
| A.5 | `H^i(X, F)` is FP-approximated for projective `X` | Induction on `P^n_R` | **Very hard** |
| A.9 | `I`-adic topology restricts to submodules | [FK18] for f.g., extension | Medium |
| A.10 | `I^m F ∩ G ⊂ I^n G` for FP-approx F | A.9 | Easy |
| A.11 | Natural `I`-topology = filtration topology | A.10 | Medium |
| A.12 | Weak isomorphism preserves topology | A.11 | Easy |
| A.13 | Natural `I`-topology = `I`-adic on projective schemes | A.12, induction on generators | **Hard** |

---

## Phased Implementation Plan

### Phase 0: Definitions (~200 lines, 1 session)

**File: `Adic spaces/StronglyNoetherian.lean`**

```lean
-- Restricted power series (I-adic completion of A₀[X₁,...,X_d])
def restrictedPowerSeries (A₀ : Type*) [CommRing A₀] (I : Ideal A₀)
    (d : ℕ) : Type _ := ...

-- Definition 2.8: Topologically universally rigid-noetherian
def IsTopUnivRigidNoetherian (A₀ : Subring A) (I : Ideal A₀) : Prop :=
  ∀ d : ℕ, IsNoetherianOutside (I.map (algebraMap ...))
    (restrictedPowerSeries A₀ I d)

-- Definition 2.8: Strongly rigid-noetherian Huber ring
class IsStronglyRigidNoetherian (A : Type*) [CommRing A]
    [TopologicalSpace A] [IsHuberRing A] : Prop where
  exists_rigidNoetherian_pair : ∃ P : PairOfDefinition A,
    IsTopUnivRigidNoetherian P.A₀ P.I
```

**Decision point:** `restrictedPowerSeries` can be defined as:
- (a) `AdicCompletion I (MvPolynomial (Fin d) A₀)` using mathlib's `AdicCompletion`, or
- (b) A subtype of `MvPowerSeries (Fin d) A₀` with convergence condition, or
- (c) Axiomatized for now with key properties stated.

**Recommendation:** Use (a) if mathlib's `AdicCompletion` is mature enough; otherwise (c).

**Also define:**
```lean
-- Definition 2.14: Pseudo-adhesive
class IsPseudoAdhesive (A₀ : Type*) [CommRing A₀] (I : Ideal A₀) : Prop where
  noetherian_outside : IsNoetherianOutside I A₀
  bounded_torsion : ∀ (M : Type*) [AddCommGroup M] [Module A₀ M]
    [Module.Finite A₀ M], ∃ n, ∀ x ∈ M, (∀ k, I ^ k • x = 0) → I ^ n • x = 0

-- Definition 3.3: Strict morphism
def IsStrictMorphism [TopologicalSpace α] [TopologicalSpace β]
    [AddGroup α] [AddGroup β] (φ : α →+ β) : Prop :=
  Continuous φ ∧ IsOpen (Set.range φ)  -- continuous + open on image
```

### Phase 1: Stability of strongly rigid-noetherian (~250 lines, 1 session)

**File: `Adic spaces/StronglyNoetherian.lean` (continued)**

1. **Lemma 2.10**: Independence of choice of `(A₀, I)`.
2. **Lemma 2.13**: Completed rational localizations `A⟨f₁/s,...,fₙ/s⟩` are
   strongly rigid-noetherian if `A` is.
   - This connects to our existing `presheafValue` and `RationalLocData`.
   - Proof: the completed ring of definition `A₀⟨f₁/s,...,fₙ/s⟩` surjects from
     `A₀⟨X₁,...,Xₙ⟩`, so noetherianness outside `V(I)` is inherited.

3. **Theorem 2.16** (FK18): Complete top. univ. rigid-noetherian ⟹ universally
   pseudo-adhesive.
   - **Axiomatize this** as `sorry` — the proof is in Fujiwara-Kato's book (1000+ pages)
     and formalizing it is a separate project.

### Phase 2: Čech complex infrastructure (~300 lines, 1-2 sessions)

**File: `Adic spaces/CechComplex.lean`**

Build the Čech complex for standard coverings of `Spa(A, A⁺)`.

```lean
-- Standard covering: X = ∪ X(f₀/fᵢ,...,fₙ/fᵢ) for f₀,...,fₙ generating A
structure StandardCovering (A : Type*) [CommRing A] [TopologicalSpace A]
    [PlusSubring A] where
  elts : Fin (n + 1) → A
  generates : Ideal.span (Set.range elts) = ⊤

-- Augmented Čech complex terms
-- C^i_aug = ∏_{j₀<...<jᵢ} A⟨F/f_{j₀},...,F/f_{jᵢ}⟩
def cechTerm (cov : StandardCovering A) (i : ℕ) : Type _ := ...

-- Differentials
def cechDifferential (cov : StandardCovering A) (i : ℕ) :
    cechTerm cov i →+* cechTerm cov (i + 1) := ...

-- "Decompleted" version (before I-adic completion)
def cechTermDecompleted (cov : StandardCovering A) (i : ℕ) : Type _ := ...
```

**Key property to prove:** The completed Čech complex equals the completion of
the decompleted one: `Ĉ^i_aug(U, O_X) ≅ (C^i_aug)^∧`.

### Phase 3: Step 2 — Exactness of decompleted complex (~300 lines, 2 sessions)

**File: `Adic spaces/CechExactness.lean`**

This is the algebraic geometry core. We need:

1. Define `S = Spec A₀`, `U = Spec A`, `P = Proj ⊕ J^m`, `P' = Proj ⊕ (JA)^m`
2. Prove the commutative square `P' →p→ U`, `P →g→ S` with `s: U → P`, `j: U → S`
3. Show `R^i s_* O_U = 0` for `i > 0` (since `j = g ∘ s` is affine and `g` separated)
4. Compute `H^i(P, s_* O_U) = H^i(U, O_U)` and `H⁰(P, s_* O_U) = A`
5. Compute via Čech on affine cover `{D_+(f_j)}` of `P`

**External dependencies (axiomatize):**
- [Bon98, Lemma 2]: Ĉ^i_aug(U, O_X) ≅ Ĉ^•_aug completed → exact with strict
  differentials iff `C^•_aug` exact with strict differentials
- Quasi-coherent sheaf theory on projective schemes
- Higher pushforward computations

### Phase 4: Steps 3-4 — Openness of differentials (~400 lines, 2-3 sessions)

**File: `Adic spaces/StrictDifferentials.lean`**

**Step 3:** Show `d^i_C : C^i_aug → ker d^{i+1}_C` are open.
- Identify ring of definition in `C^i_aug` as `A₀[F/f_{j₀},...,F/f_{jᵢ}]`
- Show the inclusion `A₀[F/f_{j₀},...] → A(F/f_{j₀},...)` is open
- Use that `{I^m K^i}` is a fundamental system of neighborhoods

**Step 4:** Show `δ^i : K^i → ker δ^{i+1}` are open.
- This requires the FP-approximation theory (Appendix A)
- Key: `H^{i+1}(P, I^k O_P)` is FP-approximated (Thm A.5)
- And `I^c · H^{i+1}(P, I^k O_P) = 0` for some `c` (Claim 2)
- Uses Thm A.13: natural I-topology = I-adic topology

**File: `Adic spaces/FPApproximated.lean`** (~300 lines)

```lean
-- Definition A.1: Weak isomorphism
def IsWeakIsomorphism [CommRing R] (I : Ideal R) {M N : Type*}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (φ : M →ₗ[R] N) : Prop :=
  ∃ n, I ^ n • LinearMap.ker φ = ⊥ ∧ I ^ n • LinearMap.range φ.coker = ⊥

-- Definition A.1: FP-approximated
def IsFPApproximated [CommRing R] (I : Ideal R) (M : Type*)
    [AddCommGroup M] [Module R M] : Prop :=
  ∃ (N : Type*) (_ : AddCommGroup N) (_ : Module R N) (_ : Module.FinitePresentation R N)
    (φ : N →ₗ[R] M), IsWeakIsomorphism I φ

-- Theorem A.5 (axiomatize initially)
axiom cohomology_fp_approximated : ...

-- Theorem A.13 (axiomatize initially)
axiom natural_I_topology_eq_adic : ...
```

### Phase 5: Assembly (~100 lines, 1 session)

**File: `Adic spaces/StronglyNoetherianSheafy.lean`**

```lean
-- Theorem 3.5 / Theorem 1.1 of Zavyalov
theorem IsStronglyRigidNoetherian.isSheafy
    [IsStronglyRigidNoetherian A] [PlusSubring A]
    [HasRestrictionMaps A] : IsSheafyTopRing A where
  embedding := ...   -- from Step 3-4 (strictness of differentials)
  gluing := ...      -- from Step 2 (exactness of Čech complex)
```

---

## Dependency Graph

```
Phase 0: Definitions
  ├── restrictedPowerSeries
  ├── IsTopUnivRigidNoetherian
  ├── IsStronglyRigidNoetherian
  ├── IsPseudoAdhesive
  └── IsStrictMorphism
       │
Phase 1: Stability
  ├── independence_of_pair (Lem 2.10)
  ├── rational_loc_strongly_noetherian (Lem 2.13)
  └── pseudo_adhesive_of_rigid_noetherian (Thm 2.16) [AXIOM]
       │
Phase 2: Čech complex
  ├── StandardCovering
  ├── cechTerm, cechDifferential
  ├── cechTermDecompleted
  └── completed_eq_completion
       │
Phase 3: Exactness ←── Phase 2
  ├── projective_scheme_setup (P, P', U, S)
  ├── higher_pushforward_vanishing
  ├── cech_decompleted_exact
  └── bonnet_lemma [AXIOM or PROVE]
       │
Phase 4: Openness ←── Phase 1, Phase 3
  ├── FPApproximated (Appendix A definitions)
  ├── cohomology_fp_approximated (Thm A.5) [AXIOM]
  ├── natural_topology_eq_adic (Thm A.13) [AXIOM]
  ├── differentials_C_open (Step 3)
  └── differentials_delta_open (Step 4)
       │
Phase 5: Assembly ←── Phase 3, Phase 4
  └── IsStronglyRigidNoetherian.isSheafy (Thm 3.5)
```

---

## Axioms to Introduce (Fill Later)

These are deep results from algebraic geometry books that should be axiomatized
initially and filled as separate projects:

1. **Thm 2.16** [FK18, Thm 0.8.4.8]: Complete top. univ. rigid-noetherian ⟹
   universally pseudo-adhesive.
2. **[Bon98, Lemma 2]**: Completed Čech complex exact with strict differentials
   iff decompleted version is.
3. **Thm A.5**: Cohomology of FP-approximated sheaves on projective schemes
   is FP-approximated.
4. **Thm A.13**: Natural I-topology = I-adic topology for FP-approximated sheaves
   on projective schemes.
5. **[Hub93, Lemma 3.7]**: `(A₀)_f → A_f` is an isomorphism for `f ∈ I`.

---

## Estimated Effort

| Phase | Lines | Sessions | Blocking? |
|-------|-------|----------|-----------|
| 0: Definitions | ~200 | 1 | No |
| 1: Stability | ~250 | 1 | Needs Phase 0 |
| 2: Čech complex | ~300 | 1-2 | Needs existing presheaf infrastructure |
| 3: Exactness | ~300 | 2 | Needs Phase 2 + axioms |
| 4: Openness | ~400 | 2-3 | Needs Phase 1, 3 + axioms |
| 5: Assembly | ~100 | 1 | Needs Phase 3, 4 |
| **Total** | **~1550** | **8-10** | |

---

## Session Plan

| Session | Goal | Deliverable |
|---------|------|-------------|
| 1 | Phase 0: all definitions | `StronglyNoetherian.lean` with definitions |
| 2 | Phase 1: stability lemmas | Lemma 2.10, 2.13, axiom for 2.16 |
| 3 | Phase 2a: Čech complex types | `CechComplex.lean` with terms + differentials |
| 4 | Phase 2b: completion relationship | Completed = completion of decompleted |
| 5 | Phase 3: decompleted exactness | Scheme setup + exactness (with axioms) |
| 6 | Phase 4a: FP-approximated defs | `FPApproximated.lean` + axioms A.5, A.13 |
| 7 | Phase 4b: Step 3 openness | Differentials of C are open |
| 8 | Phase 4c: Step 4 openness | Differentials of δ are open |
| 9 | Phase 5: assembly | `StronglyNoetherianSheafy.lean` with main theorem |
| 10 | Cleanup + axiom audit | Polish, verify, update STATUS.md |

---

## Risk Assessment

**High risk:**
- Restricted power series definition: mathlib's `AdicCompletion` may not compose
  well with `MvPolynomial`. May need custom definition.
- Čech complex: no existing Čech cohomology in mathlib for our topology setup.
  Need to build from scratch.
- Projective scheme arguments (Step 2): may need substantial algebraic geometry
  that doesn't exist in mathlib.

**Medium risk:**
- FP-approximation theory: the appendix is self-contained but long.
  Axiomatizing the main results is safe.
- Ring of definition for rational localizations: connecting our `locSubring`
  to the abstract ring of definition.

**Low risk:**
- Definitions (Phase 0): straightforward formalization.
- Assembly (Phase 5): just composing proved/axiomatized pieces.
- Standard covering reduction (Lemma 3.1): adapts directly from our
  `RationalCovering` infrastructure.

---

## Decision Log

| Decision | Choice | Rationale |
|----------|--------|-----------|
| Restricted power series | Use `AdicCompletion` if possible, else axiomatize | Avoid reinventing completion machinery |
| Thm 2.16 (FK18) | Axiomatize | 1000+ page book, separate project |
| Thm A.5, A.13 | Axiomatize | Deep algebraic geometry, separate project |
| Bonnet's lemma | Axiomatize | Functional analysis result |
| `IsNoetherianOutside` | Define as `∀ f ∉ V(I), IsNoetherian (A_f)` | Matches Zavyalov's usage |
| Čech complex | Build from scratch | No suitable mathlib API |
