# Plan: Corollary 8.40 — Adic Morphisms (Sorry-Free)

> Target: Wedhorn, Corollary 8.40, §8.4
> Date: 2026-03-11

## Goal

**Corollary 8.40:** Let `f : X → Y` be an adic morphism of adic spaces. Then for
all open affinoid subspaces `U ⊆ X` and `V ⊆ Y` with `f(U) ⊆ V`, the ring
homomorphism `O_Y(V) → O_X(U)` induced by `f` is adic.

## Full Proof Chain (no sorries)

```
Cor 8.40
  ├── Prop 8.39(1): f adic ⟹ f(X_a) ⊆ Y_a
  │     └── Reduces to affinoid case (Remark 8.37(2))
  │           └── Lemma 7.46(1): φ adic ⟹ Spa(φ)(X_a) ⊆ Y_a
  └── Lemma 7.46(2): B complete + f(X_a) ⊆ Y_a ⟹ φ adic
        └── Lemma 7.45: non-open prime of complete affinoid ⟹ ∃ analytic point
              ├── IsLocalRing.exists_factor_valuationRing  [Mathlib]
              ├── Convex subgroups + coarsening            [NEW: §7.1]
              └── IsAdicComplete.le_jacobson_bot            [Mathlib]
```

## Existing Infrastructure (DO NOT duplicate)

| Lemma | File:Line | What it gives us |
|-------|-----------|------------------|
| `suppFun_comap` | ValuationSpectrum:346 | `supp(comap φ v) = φ⁻¹(supp v)` — **KEY for 7.46** |
| `comap_isContinuous` | ContinuousValuations:120 | comap preserves continuity |
| `spaComap` | AdicSpectrum:293 | Continuous map `Spa B → Spa A` |
| `comap_mem_spa` | AdicSpectrum:277 | comap preserves Spa membership |
| `IsAnalytic` | AnalyticPoints:35 | `¬IsOpen (v.supp : Set A)` |
| `IsTateRing.isAnalytic` | AnalyticPoints:45 | All Tate ring points are analytic |
| `PairOfDefinition` | HuberRings:56 | Open subring A₀ with ideal of definition I |
| `ideal_isOpen_iff_...` | OpenIdeals:73 | Characterizes open ideals via nilradical |
| `exists_mem_spa_supp_eq_of_prime` | AdicSpectrum:224 | ∃ v ∈ Spa with given support (**discrete only**) |
| `VPreHom` / `VObj` | StructureSheaf:459+ | Morphisms/objects of 𝒱^pre |

**Key Mathlib lemmas:**

| Lemma | Module | What it gives us |
|-------|--------|------------------|
| `IsLocalRing.exists_factor_valuationRing` | `Mathlib.RingTheory.Valuation.LocalSubring` | ∃ valuation ring of K dominating local ring R |
| `IsAdicComplete.le_jacobson_bot` | `Mathlib.RingTheory.AdicCompletion.Basic` | I ≤ Jac(0) for I-adically complete rings |
| `Ideal.radical_eq_sInf` | `Mathlib.RingTheory.Ideal.Operations` | radical = ⨅ primes containing I |
| `Ideal.exists_le_maximal` | `Mathlib.RingTheory.Ideal.Maximal` | ∃ maximal ideal containing I |
| `Ideal.IsPrime.radical_le_iff` | `Mathlib.RingTheory.Ideal.Operations` | rad(I) ≤ 𝔭 iff I ≤ 𝔭 for prime 𝔭 |
| `Valuation.RankOne` | `Mathlib.RingTheory.Valuation.RankOne` | Rank-1 valuations (embed into ℝ≥0) |
| `Valuation.extendToLocalization` | `Mathlib.RingTheory.Valuation.ExtendToLocalization` | Extend valuation to localization |

## File Organization

| New content | File | §Wedhorn | Est. lines |
|------------|------|----------|------------|
| Convex subgroups of ordered groups | `OrderedGroupConvex.lean` (new) | §7.1 | ~120 |
| Valuation coarsening + retraction | `ValuationCoarsening.lean` (new) | §7.1 | ~180 |
| Lemma 7.45 (analytic point construction) | `AnalyticPoints.lean` (extend) | §7.4 | +120 |
| `IsAdicHom` (Def 6.23) + API | `HuberRings.lean` (extend) | §6.5 | +60 |
| Lemma 7.46, Def 8.38, Prop 8.39, Cor 8.40 | `AdicMorphisms.lean` (new) | §7.5, §8.4 | ~280 |
| **Total** | | | **~760** |

---

## Phase 1: Convex Subgroups (§7.1 infrastructure)

### File: `OrderedGroupConvex.lean` (~120 lines)

Pure order-theory on linearly ordered commutative groups. Potentially upstreamable to Mathlib.

**Definitions:**
```lean
/-- A convex subgroup of a linearly ordered commutative group. -/
structure ConvexSubgroup (Γ : Type*) [OrderedCommGroup Γ] extends Subgroup Γ where
  convex' : ∀ {a b c}, a ∈ carrier → c ∈ carrier → a ≤ b → b ≤ c → b ∈ carrier
```

**Key results:**
- Convex subgroups form a totally ordered lattice
- Quotient `Γ / H` by convex subgroup `H` inherits a linear order
- `Γ / H` is a linearly ordered comm. group with zero (where `H ↦ 0`)
- The projection `Γ → Γ / H` is order-preserving
- An element `γ < 1` with `γ ∉ H` satisfies `π(γ) < 1` in `Γ / H`
- If `γ ∈ H` and `γ < 1`, then `π(γ) = 1` (mapped to identity coset)

**Mathlib status:** No `ConvexSubgroup` type exists. Related: `Subgroup`, `OrdConnected`,
`MulArchimedeanClass`. We need to build this from scratch.

### File: `ValuationCoarsening.lean` (~180 lines)

Coarsening of valuations by convex subgroups. This is the "retraction" from §7.1.

**Definitions:**
```lean
/-- Coarsening of a valuation by a convex subgroup of its value group.
Given v : R → Γ₀ and H a convex subgroup of Γ, the coarsened valuation is
the composition R →ᵥ Γ₀ →π (Γ/H)₀. (§7.1 of Wedhorn) -/
def Valuation.coarsen (v : Valuation R Γ₀) (H : ConvexSubgroup Γ) :
    Valuation R (Γ ⧸ H)₀

/-- The smallest convex subgroup of Γ_v containing all v(a) for a ∈ I \ supp(v).
This is cΓ_v(I) from Definition 7.3 of Wedhorn. -/
def Valuation.convexSubgroupOfIdeal (v : Valuation R Γ₀) (I : Ideal R) :
    ConvexSubgroup Γ
```

**Key results:**
- `coarsen` preserves support: `(v.coarsen H).supp = v.supp`
- `coarsen` preserves ≤ 1: if `v a ≤ 1` then `(v.coarsen H) a ≤ 1`
- **Continuity theorem:** If `v.convexSubgroupOfIdeal I = ⊤` (the full group), then
  `v` is continuous w.r.t. the `I`-adic topology. In general, `v.coarsen H` where
  `H` is chosen below `convexSubgroupOfIdeal` gives a continuous valuation.
- For `a ∈ I \ supp(v)` with `v(a) ∉ H`: `(v.coarsen H)(a) < 1`
- Cofinal property: in `Γ / H`, the values `{(v.coarsen H)(a)^n : a ∈ I, n ∈ ℕ}`
  are cofinal for 0, ensuring continuity w.r.t. the `I`-adic topology.

---

## Phase 2: Lemma 7.45 (Analytic Point Construction)

### File: `AnalyticPoints.lean` (extend, +120 lines)

**Lemma 7.45 (Wedhorn):** Let `(A, A⁺)` be a complete affinoid ring. Let `𝔭` be a
non-open prime ideal of `A`. Then there exists an analytic point `x ∈ Spa A` with
`supp x ⊇ 𝔭`.

**Proof strategy (direct, no microbial/vertical generalization needed):**

1. Let `(A₀, I)` = pair of definition. Set `𝔭₀ = 𝔭 ∩ A₀`.
   Since `𝔭` is not open, `I ⊄ 𝔭₀` (by `ideal_isOpen_iff_topologicalNilradical_le_radical`).

2. Let `𝔪` = maximal ideal of `A₀` containing `𝔭₀`.
   Since `A₀` is `I`-adically complete, `I ≤ Jac(A₀)`, so `I ⊆ 𝔪`.
   (Uses `IsAdicComplete.le_jacobson_bot` from Mathlib.)
   In particular `𝔭₀ ⊊ 𝔪`.

3. Let `K = Frac(A/𝔭)`. The composition
   `(A₀/𝔭₀)_{𝔪/𝔭₀} → Frac(A₀/𝔭₀) → K`
   gives a ring hom from a local domain to a field.

4. By `IsLocalRing.exists_factor_valuationRing`, there exists a valuation subring
   `V` of `K` such that `(A₀/𝔭₀)_{𝔪/𝔭₀}` maps into `V` via a local ring hom.
   Let `w` be the valuation on `K` corresponding to `V`.

5. Properties of `w`:
   - `w(ā) ≤ 1` for all `a ∈ A₀` (since `A₀/𝔭₀ ⊆ V`)
   - `w(ā) < 1` for all `a ∈ 𝔪 \ 𝔭₀` (since these map to the max. ideal of V)
   - In particular, `w(ā) < 1` for all `a ∈ I \ 𝔭₀` (since `I ⊆ 𝔪`)

6. **Coarsen for continuity:** Choose `H` = largest convex subgroup of `Γ_w` such that
   `w(I \ 𝔭₀) ∩ H = ∅`. The coarsened valuation `w' = w.coarsen H` has:
   - `supp(w') = supp(w)` (support preserved)
   - `w'(ā) < 1` for `a ∈ I \ 𝔭₀` (these values are outside `H`)
   - `w'` is continuous w.r.t. the `I`-adic topology on `A₀` (cofinal property)

7. Compose: `v : A → A/𝔭 → K →^{w'} (Γ_w/H) ∪ {0}`.
   This is a valuation on `A` with:
   - `supp(v) = 𝔭`
   - `v(a) ≤ 1` for `a ∈ A₀` (and hence `a ∈ A⁺ ⊆ A₀`)
   - `v` is continuous: `{a ∈ A : v(a) ≤ γ}` is open for all `γ`, because
     `{a ∈ A₀ : v(a) ≤ γ}` is open in `A₀` (by I-adic continuity) and `A₀` is
     open in `A`, so the ultrametric inequality gives openness in `A`.

8. Therefore `v ∈ Spa A A⁺` (continuous + bounded on A⁺) and `v` is analytic
   (supp(v) = 𝔭 is non-open).

**Dependencies from Phase 1:** `Valuation.coarsen`, `ConvexSubgroup`, cofinal property.

**Mathlib dependencies:**
- `IsLocalRing.exists_factor_valuationRing`
- `IsAdicComplete.le_jacobson_bot`
- `Ideal.exists_le_maximal`
- `FractionRing`, `Localization.AtPrime`

---

## Phase 3: Adic Homomorphisms

### File: `HuberRings.lean` (extend, +60 lines)

**Definition 6.23 (Adic ring homomorphism):**

```lean
/-- A ring hom φ : A →+* B between f-adic rings is *adic* if ∃ pairs of
definition (A₀, I) of A and (B₀, J) of B with φ(A₀) ⊆ B₀ and the ideals
φ(I)·B₀ and J have the same radical in B₀ (Definition 6.23 of Wedhorn). -/
def IsAdicHom [IsHuberRing A] [IsHuberRing B] (φ : A →+* B) : Prop :=
  ∃ (PA : PairOfDefinition A) (PB : PairOfDefinition B),
    (∀ a ∈ PA.A₀, φ a ∈ PB.A₀) ∧
    (Ideal.map (φ.comp PA.A₀.subtype |>.codRestrict PB.A₀ _) PA.I).radical = PB.I.radical
```

The "same radical" formulation is cleanest; equivalently, `φ(I)·B₀` is an ideal of
definition of `B₀`.

**API lemmas:**
- `IsAdicHom.continuous` : adic ⟹ continuous (since ideal of def. generates topology)
- `isAdicHom_of_discreteTopology` : discrete A ⟹ φ adic (Example 6.24, I = 0)
- `IsTateRing.isAdicHom_of_continuous` : Tate A + continuous φ ⟹ φ adic (Prop 6.25)
- `IsAdicHom.not_adic_iff` : characterization via radical containment failure
  (for the contrapositive in 7.46(2))

---

## Phase 4: Lemma 7.46 + Adic Morphisms + Corollary 8.40

### File: `AdicMorphisms.lean` (new, ~280 lines)

#### Lemma 7.46(1): Non-analytic preservation (~30 lines)

```lean
/-- Lemma 7.46(1), first part: Spa(φ) sends non-analytic to non-analytic. -/
theorem spaComap_nonAnalytic {φ : A →+* B} (hφ : Continuous φ)
    {v : Spv B} (hv : ¬IsAnalytic v) : ¬IsAnalytic (comap φ v)
```

**Proof:** `suppFun_comap` gives `supp(comap φ v) = φ⁻¹(supp v)`. If `supp v` is
open and `φ` is continuous, then `φ⁻¹(supp v)` is open. QED.

#### Lemma 7.46(1): Adic ⟹ analytic preservation (~60 lines)

```lean
/-- Lemma 7.46(1), second part: If φ is adic, Spa(φ) preserves analytic points. -/
theorem spaComap_analytic_of_isAdicHom [IsHuberRing A] [IsHuberRing B]
    {φ : A →+* B} (hφ : IsAdicHom φ) {v : Spv B}
    (hv : v ∈ Spa B B⁺) (ha : IsAnalytic v) : IsAnalytic (comap φ v)
```

**Proof:** Contrapositive. If `supp(comap φ v) = φ⁻¹(supp v)` is open in A, then
since φ is adic, the topological nilradical of A maps into the nilradical of the
support ideal. Using the adic property (same radical), this forces `supp v` to
contain an ideal of definition of B, making it open. Contradiction.

#### Lemma 7.46(2): Converse (~80 lines)

```lean
/-- Lemma 7.46(2): If B is complete and Spa(φ) preserves analytic points,
then φ is adic. -/
theorem isAdicHom_of_spaComap_analytic [IsHuberRing A] [IsHuberRing B]
    [CompleteSpace B] {φ : A →+* B} (hφ : Continuous φ)
    (h : ∀ v ∈ Spa B B⁺, IsAnalytic v → IsAnalytic (comap φ v)) :
    IsAdicHom φ
```

**Proof (contrapositive):**
1. Assume `¬IsAdicHom φ`. Choose pairs `(A₀, I)`, `(B₀, J)` with `φ(A₀) ⊆ B₀`,
   `φ(I) ⊆ J`, but `rad(φ(I)·B₀) ≠ rad(J)`.
2. Since `rad(J) ⊄ rad(φ(I)·B₀)`, by `Ideal.radical_eq_sInf` there exists a prime
   `𝔭` of `B₀` with `φ(I)·B₀ ⊆ 𝔭` but `J ⊄ 𝔭`. Hence `𝔭` is non-open (since
   `J ⊄ 𝔭` means `𝔭` doesn't contain an ideal of definition).
3. Extend `𝔭` to a prime `𝔮` of `B` (the preimage of `𝔭` under `B → B₀` or
   find a prime of `B` lying over `𝔭`).
4. By **Lemma 7.45**, `∃ v ∈ Spa B` analytic with `supp v ⊇ 𝔮 ⊇ 𝔭`.
5. Then `supp(comap φ v) = φ⁻¹(supp v) ⊇ φ⁻¹(𝔭) ⊇ I`.
6. Since `supp(comap φ v) ⊇ I`, it is open (using `ideal_isOpen_iff_...`).
7. So `comap φ v` is non-analytic, contradicting hypothesis.

#### Definition 8.38: Adic Morphisms (~30 lines)

```lean
/-- A morphism f : X → Y of adic spaces is *adic* if for every x ∈ X, ∃ open
affinoid neighborhoods U ∋ x, V ∋ f(x) with f(U) ⊆ V such that the induced
ring hom O_Y(V) → O_X(U) is adic (Definition 8.38 of Wedhorn). -/
def IsAdicMorphism [AdicSpace X] [AdicSpace Y] (f : X → Y) : Prop := ...
```

The exact formalization depends on the `AdicSpace` structure from StructureSheaf.lean.
Open affinoid subspaces are represented via the existing `AffinoidAdicSpace` structure.

#### Proposition 8.39 (~50 lines)

```lean
/-- Prop 8.39(1): f is adic iff f sends analytic points to analytic points. -/
theorem isAdicMorphism_iff_analytic ...

/-- Prop 8.39(2): Any morphism of adic spaces sends non-analytic to non-analytic. -/
theorem morphism_nonAnalytic ...
```

**Proof of 8.39:** By Remark 8.37(2), reduce to affiniod case where X = Spa B,
Y = Spa A. Then apply Lemma 7.46(1).

#### Corollary 8.40 (~30 lines)

```lean
/-- Cor 8.40: For an adic morphism, ALL induced ring maps on open affinoid
subspaces are adic (not just the witnessing ones from Def 8.38). -/
theorem IsAdicMorphism.ringHom_isAdic (hf : IsAdicMorphism f)
    {U V} (hUV : f '' U ⊆ V) : IsAdicHom (inducedRingHom f V U)
```

**Proof:** By 8.39(1), `f(U_a) ⊆ V_a`. Since `O_X(U)` is complete (presheaf
values are completions), Lemma 7.46(2) gives `IsAdicHom`. QED.

---

## Implementation Order

| Phase | Step | Content | File | Est. lines | Depends on |
|-------|------|---------|------|-----------|------------|
| **1** | 1.1 | Convex subgroups of ordered groups | `OrderedGroupConvex.lean` | 120 | — |
| **1** | 1.2 | Valuation coarsening + retraction | `ValuationCoarsening.lean` | 180 | 1.1 |
| **2** | 2.1 | Lemma 7.45 (analytic point construction) | `AnalyticPoints.lean` | +120 | 1.2, Mathlib |
| **3** | 3.1 | `IsAdicHom` definition + API | `HuberRings.lean` | +60 | — |
| **4** | 4.1 | Lemma 7.46(1): non-analytic preservation | `AdicMorphisms.lean` | 30 | — |
| **4** | 4.2 | Lemma 7.46(1): adic ⟹ analytic | `AdicMorphisms.lean` | 60 | 3.1 |
| **4** | 4.3 | Lemma 7.46(2): converse | `AdicMorphisms.lean` | 80 | 2.1, 3.1 |
| **4** | 4.4 | Def 8.38, Prop 8.39, Cor 8.40 | `AdicMorphisms.lean` | 110 | 4.1-4.3 |
| | | **Total** | | **~760** | |

Phases 1-2 can be developed independently of Phase 3. Phase 4 depends on both.

## Risk Assessment

| Risk | Mitigation |
|------|-----------|
| Convex subgroup quotient order is subtle | Stick to multiplicative groups; follow Mathlib conventions for ordered groups |
| `IsLocalRing.exists_factor_valuationRing` may need adaptation | It returns a `ValuationSubring` of K; we need to extract the `Valuation` and compose with A → K |
| Coarsening might change continuity in unexpected ways | The cofinal property is the key invariant; prove it as a standalone lemma |
| `IsAdicMorphism` formalization depends on `AdicSpace` category | Can define it concretely for `VPreHom` which already exists |
| Extending prime from B₀ to B in 7.46(2) proof | Use `Ideal.comap` of B₀ ↪ B; the preimage of 𝔭 under inclusion is the right prime |
| I-adic completeness of A₀ needed for step 2 | Already encoded in `PairOfDefinition`; may need to connect to `IsAdicComplete` |

## What NOT to build

- ~~Microbial valuations~~ — Not needed; coarsening gives continuity directly
- ~~Vertical generalizations to height 1~~ — Not needed; we don't require rank 1
- ~~Extension from A₀ to A~~ — Not needed; compose A → A/𝔭 → K directly
- ~~Full Section 7.1 retraction~~ — Only need the coarsening by one convex subgroup
