# Plan: S3 — Nullstellensatz refinement (Wedhorn Cor 7.32 + Zavyalov §2.3)

**Target sorry**: `Adic spaces/StandardCover.lean:274`
**Statement**: For a rational covering `C` with nonempty base rational open, produce `S : Finset A` satisfying `refines_cover`, `refines_contain`, `refines_span_top`.

**Mathematical content**: Wedhorn Lemma 8.34(ii) combined with Zavyalov §2.3 construction. Requires Wedhorn Corollary 7.32 (dominating unit extraction).

## Dependency chain

```
S3 (StandardCover:274)
 └─── T-NULL-1: Cor 7.32 (dominating unit)    — 100-150 lines
       └─── T-NULL-0: Spa compactness          — 150-300 lines
 └─── T-NULL-2..5: Zavyalov §2.3 construction — 150-250 lines
```

Total: ~400-700 new lines across ~8 sub-tickets.

## Phase 0: Spa compactness (PREREQUISITE)

### T-NULL-0a: Spv compactness (quasi-compactness of full valuation spectrum)

**Result**: `CompactSpace (Spv A)` or `IsCompact (univ : Set (Spv A))` for any commutative ring `A`.

**Wedhorn reference**: Prop 4.8.

**Proof strategy** (Huber's theorem):
- `Spv A` with its topology is homeomorphic to a proconstructible subspace of `{0, 1}^{A × A}` (via characteristic functions of `basicOpen f s`).
- `{0, 1}^{A × A}` is compact (Tychonoff).
- Proconstructible subspaces of compact spaces are compact.

**Alternative simpler proof** (if available in mathlib):
- Check if `Spv A ≃` some prime spectrum of valuation monoid — if so, use `PrimeSpectrum.compactSpace` / Krull.

**Estimate**: 100-200 lines.

### T-NULL-0b: Spa A A⁺ is closed in Spv A

**Result**: `IsClosed (Spa A A⁺ : Set (Spv A))` for a pair `(A, A⁺)`.

**Proof**: `Spa A A⁺ = ∩_{f ∈ A⁺} {v | v(f) ≤ 1}` — intersection of closed sets (each `{v | v(f) ≤ 1}` is closed as complement of basic open `{v | v(1) ≤ v(f) ∧ v(f) ≠ 0}`... need to think).

Actually the continuity condition `IsContinuous v` needs checking too.

**Estimate**: 50-100 lines.

### T-NULL-0c: CompactSpace (Spa A A⁺)

**Result**: `CompactSpace ↥(Spa A A⁺)` or `IsCompact (Spa A A⁺ : Set (Spv A))`.

Derived from T-NULL-0a + T-NULL-0b: closed subspace of compact is compact.

**Estimate**: 20-50 lines.

## Phase 1: Wedhorn Corollary 7.32 (dominating unit)

### T-NULL-1: exists_dominating_unit

**Statement** (Wedhorn Cor 7.32):
```lean
theorem exists_dominating_unit [IsHuberRing A] [IsTateRing A] {A⁺ : Subring A}
    (hAplus : IsOpen (A⁺ : Set A)) (T : Finset A)
    (hT : ∀ v ∈ Spa A A⁺, ∃ t ∈ T, v t ≠ 0) :
    ∃ s : A, IsUnit s ∧ ∀ v ∈ Spa A A⁺, ∃ t ∈ T, v.vle s t ∧ v s ≠ 0 ∧ v t ≠ 0
```

**Proof** (Wedhorn p. 62):
1. For each v, since T has no common zero, some `t_v ∈ T` has `v(t_v) ≠ 0`.
2. The sets `{v : v(t) ≠ 0}` for `t ∈ T` form an open cover of `Spa A A⁺`.
3. By T-NULL-0c (compactness), finite refinement via Wedhorn 7.31.
4. Use Prop 7.52 + topological nilpotents to extract unit.

**Estimate**: 100-150 lines.

## Phase 2: Zavyalov §2.3 candidate family

### T-NULL-2: Define refinement family

For a rational cover `C` and each Spa point `v ∈ rationalOpen C.base.T C.base.s`:
- There exists `D ∈ C.covers` with `v ∈ rationalOpen D.T D.s`.
- For that `D`, `v(t) ≤ v(D.s)` for `t ∈ D.T` and `v(D.s) ≠ 0`.

Define candidate test elements `{s⁻¹ · t : t ∈ D.T, D ∈ C.covers}` for a suitable unit `s`.

**Estimate**: 40-80 lines.

### T-NULL-3: Prove `refines_cover`

For each `v`, pick the cover piece `D ∈ C.covers` and show `v` is in `rationalOpen (insert (s⁻¹ · t) C.base.T) C.base.s` for the chosen `t`.

Uses: T-NULL-1 provides `s` with `v(s) < v(t)` for some `t` (chosen from `D.T`).

**Estimate**: 50-80 lines.

### T-NULL-4: Prove `refines_contain`

For each `f = s⁻¹ · t` (with `t ∈ D.T, D ∈ C.covers`): show `rationalOpen (insert f C.base.T) C.base.s ⊆ rationalOpen D.T D.s`.

Mathematical content: `v(f) ≤ v(C.base.s) ≤ something` + `v(t) ≤ v(s) * v(C.base.s)` via the chosen dominating s.

**Estimate**: 40-70 lines.

### T-NULL-5: Prove `refines_span_top`

`Ideal.span (S : Set A) = ⊤` for `S = {s⁻¹ · t : t ∈ ∪ D.T}`.

Uses: `(∪ D.T) · A ⊇ unit ideal` (since C covers Spa A).

**Estimate**: 30-50 lines.

## Phase 3: Final assembly

### T-NULL-6: Close the sorry

Combine T-NULL-2 through T-NULL-5 to produce the required `S` and close the sorry at StandardCover.lean:274.

**Estimate**: 20-40 lines.

## Execution order

**Phase 0 (must be first)**: T-NULL-0a → T-NULL-0b → T-NULL-0c

**Phase 1 (after Phase 0)**: T-NULL-1 (single task, uses 0c)

**Phase 2 (after Phase 1)**: T-NULL-2 → T-NULL-3, T-NULL-4, T-NULL-5 in parallel

**Phase 3**: T-NULL-6 (assembly)

## Risk factors

- **High**: Spa compactness — the Huber proof (via proconstructible/Tychonoff) is substantial Lean work.
- **Medium**: Cor 7.32 — once compactness is available, the proof is ~Wedhorn-direct but needs careful valuation arithmetic.
- **Medium**: Zavyalov construction — we have the scaffolding (`refines_*` predicates), but the concrete algebra requires care.

## Incremental approach this session

Given the scope (~400-700 lines), we'll make partial progress. Priorities:

1. **Start T-NULL-0a (Spv compactness)** — foundational piece.
2. **Dispatch an agent** to explore the mathlib landscape for existing compactness lemmas on valuation-like spaces (e.g., `PrimeSpectrum.compactSpace`, `Profinite`, `Stone` duality).
3. If mathlib provides close infrastructure, port the bridge. Else, write Huber's proof.

## Alternative route

**Option**: if Spa compactness is too expensive, consider whether Cor 7.32 can be replaced by a WEAKER but sufficient result for just our specific use case (finite rational cover, specific `T = C.covers ↦ D.T`). This might allow proof-by-induction on cover size instead of compactness.

Worth investigating before committing to Huber's full proof.
