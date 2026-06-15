# Laurent Refinement Implementation Plan

> **For agentic workers:** REQUIRED: Use superpowers:subagent-driven-development (if subagents available) or superpowers:executing-plans to implement this plan. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Fill the last IsSheafy sorry by proving every rational covering has injective product restriction, via Laurent covers + concrete refinement.

**Architecture:** Two new files. `RationalRefinement.lean` defines concrete refinement between rational coverings and proves refinement preserves separation (using existing `restrictionMap_comp`). `LaurentRefinement.lean` constructs Laurent covers as rational coverings, proves they have separation, builds product covers, and proves Lemma 8.34 (every rational covering is refined by a Laurent product).

**Tech Stack:** Lean 4 v4.29.0-rc3, Mathlib v4.29.0-rc3

---

## File Structure

```
Create: Adic spaces/RationalRefinement.lean   (~70 lines)
Create: Adic spaces/LaurentRefinement.lean     (~350 lines)
Modify: Adic spaces/StructureSheaf.lean        (replace sorry with proof)
Modify: Adic spaces.lean                       (add imports)
```

Existing (no changes needed):
- `Presheaf.lean` — has `restrictionMap_comp`, `restrictionMap_id`, `RationalCovering`, `productRestriction`
- `LaurentCoverExact.lean` — has `epsilonHom_gen_injective`
- `TopologyComparison.lean` — has `presheafValueTateQuotientEquiv`

---

### Task 1: RationalRefinement structure + separation transfer

**Files:**
- Create: `Adic spaces/RationalRefinement.lean`
- Modify: `Adic spaces.lean` (add import)

- [ ] **Step 1: Create file with header + RationalRefinement structure**

```lean
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».Presheaf

/-!
# Concrete Refinement for Rational Coverings

A `RationalRefinement V U` witnesses that covering `V` refines covering `U`
(same base, each V-piece inside some U-piece). Combined with `restrictionMap_comp`,
this yields `separation_of_finer_rational`: if V has separation (injective product
restriction), so does U.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn2019adic], Proposition A.3
-/

namespace ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A] [PlusSubring A]
  [IsTopologicalRing A] [HasRestrictionMaps A]

/-- A refinement of rational coverings: `V` refines `U` (same base, each
V-piece is contained in some U-piece via the map `τ`). -/
structure RationalRefinement (V U : RationalCovering A) where
  base_eq : V.base = U.base
  τ : { D // D ∈ V.covers } → { E // E ∈ U.covers }
  hτ : ∀ d : { D // D ∈ V.covers },
    rationalOpen d.1.T d.1.s ⊆ rationalOpen (τ d).1.T (τ d).1.s
```

- [ ] **Step 2: Prove separation_of_finer_rational**

```lean
/-- Refinement preserves separation: if V refines U and V has injective
product restriction, then U has injective product restriction.

Proof: if `res_{base→E}(x) = res_{base→E}(y)` for all U-pieces E, then
by `restrictionMap_comp`, `res_{base→D}(x) = res_{base→D}(y)` for all
V-pieces D (since each D ⊆ some E). By V-separation, x = y. -/
theorem separation_of_finer_rational (V U : RationalCovering A)
    (r : RationalRefinement V U)
    (hV : Function.Injective (productRestriction A V)) :
    Function.Injective (productRestriction A U) := by
  intro x y hxy
  apply hV
  ext D hD
  -- D ∈ V.covers, τ(D) ∈ U.covers, rationalOpen D ⊆ rationalOpen τ(D)
  let ⟨E, hE⟩ := r.τ ⟨D, hD⟩
  -- restrictionMap base D = restrictionMap τ(D) D ∘ restrictionMap base τ(D)
  -- Use restrictionMap_comp from Presheaf.lean
  have hbase : V.base = U.base := r.base_eq
  have hDE := r.hτ ⟨D, hD⟩
  have hBE := U.hsubset E hE
  -- res_{base→D}(x) = res_{E→D}(res_{base→E}(x))
  --                   = res_{E→D}(res_{base→E}(y))  (by hxy at E)
  --                   = res_{base→D}(y)
  -- Use restrictionMap_comp and the hypothesis hxy
  sorry -- Fill with restrictionMap_comp application
```

The sorry above is a placeholder for the exact proof term. The proof strategy
is clear: apply `restrictionMap_comp` to factor the V-restriction through the
U-restriction, then use the `hxy` hypothesis.

**Implementation note:** The exact proof will need careful `hbase ▸` rewrites
to match the base data. Check `restrictionMap_comp` signature in Presheaf.lean:352.

- [ ] **Step 3: Add import to root file**

Add `import «Adic spaces».RationalRefinement` to `Adic spaces.lean`.

- [ ] **Step 4: Verify compilation**

```bash
lake env lean "Adic spaces/RationalRefinement.lean"
```
Expected: compiles with at most 1 sorry (the separation proof body).

- [ ] **Step 5: Fill the sorry in separation_of_finer_rational**

Complete the proof using `restrictionMap_comp` + `hxy` + base_eq rewriting.

- [ ] **Step 6: Verify 0 sorry**

```bash
lake env lean "Adic spaces/RationalRefinement.lean"
```
Expected: compiles with 0 sorry warnings.

- [ ] **Step 7: Commit**

```bash
git add "Adic spaces/RationalRefinement.lean" "Adic spaces.lean"
git commit -m "RationalRefinement: concrete refinement preserves separation (0 sorry)"
```

---

### Task 2: Laurent cover as RationalCovering

**Files:**
- Create: `Adic spaces/LaurentRefinement.lean` (first section)
- Modify: `Adic spaces.lean` (add import)

- [ ] **Step 1: Create file with header + Laurent datum constructors**

```lean
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».RationalRefinement
import «Adic spaces».LaurentCoverExact
import «Adic spaces».TopologyComparison

/-!
# Laurent Covers as Rational Coverings

Constructs the 2-element Laurent covering `{R(T∪{f}/s), R(T∪{s}·{s,f}/s·f)}`
for element `f` within base `D₀`, proves it covers `rationalOpen D₀`.

## Main definitions

* `laurentPlusDatum` : the "plus half" R(T∪{f}/s)
* `laurentMinusDatum` : the "minus half" R(T₀/s₀) ∩ R({s₀}/f)
* `laurentCovering` : the 2-element `RationalCovering`

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn2019adic], Lemma 8.33, 8.34
-/

namespace ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A] [PlusSubring A]
  [IsTopologicalRing A] [HasRestrictionMaps A]
```

- [ ] **Step 2: Define laurentPlusDatum**

The "plus half" `{v ∈ R(T₀/s₀) : v(f) ≤ v(s₀)}` = `R(T₀ ∪ {f} / s₀)`:

```lean
/-- The "plus half" of the Laurent cover at `f` within base `D₀`:
`R(T₀ ∪ {f} / s₀) = {v ∈ R(D₀) : v(f) ≤ v(s₀)}`. -/
noncomputable def laurentPlusDatum (D₀ : RationalLocData A) (f : A) :
    RationalLocData A where
  P := D₀.P
  T := D₀.T ∪ {f}
  s := D₀.s
  hopen := sorry -- adapt D₀.hopen: same P, same s, larger T
```

- [ ] **Step 3: Define laurentMinusDatum**

The "minus half" needs more care. Use `rationalOpen_inter` to express
`R(T₀/s₀) ∩ R({s₀}/f)` as a single rational open.

```lean
/-- The "minus half" of the Laurent cover at `f` within base `D₀`:
`{v ∈ R(D₀) : v(s₀) ≤ v(f)}`. Expressed as the intersection
`R(T₀ ∪ {s₀} / s₀) ∩ R({s₀, f} / f)` via `rationalOpen_inter`. -/
noncomputable def laurentMinusDatum (D₀ : RationalLocData A) (f : A) :
    RationalLocData A where
  P := D₀.P
  T := (D₀.T ∪ {D₀.s}) * {D₀.s, f}
  s := D₀.s * f
  hopen := sorry -- needs divByS properties + locSubring closure
```

- [ ] **Step 4: Prove covering lemmas**

```lean
theorem laurentPlus_subset (D₀ : RationalLocData A) (f : A) :
    rationalOpen (laurentPlusDatum D₀ f).T (laurentPlusDatum D₀ f).s ⊆
      rationalOpen D₀.T D₀.s := sorry

theorem laurentMinus_subset (D₀ : RationalLocData A) (f : A) :
    rationalOpen (laurentMinusDatum D₀ f).T (laurentMinusDatum D₀ f).s ⊆
      rationalOpen D₀.T D₀.s := sorry

theorem laurentCover_covers (D₀ : RationalLocData A) (f : A) :
    ∀ v ∈ rationalOpen D₀.T D₀.s,
      v ∈ rationalOpen (laurentPlusDatum D₀ f).T (laurentPlusDatum D₀ f).s ∨
      v ∈ rationalOpen (laurentMinusDatum D₀ f).T (laurentMinusDatum D₀ f).s :=
  sorry -- trichotomy: v(f) ≤ v(s₀) ∨ v(s₀) ≤ v(f)
```

- [ ] **Step 5: Assemble laurentCovering**

```lean
/-- The 2-element Laurent covering of `D₀` at element `f`. -/
noncomputable def laurentCovering (D₀ : RationalLocData A) (f : A) :
    RationalCovering A where
  base := D₀
  covers := {laurentPlusDatum D₀ f, laurentMinusDatum D₀ f}
  hsubset := by
    intro D hD
    simp only [Finset.mem_insert, Finset.mem_singleton] at hD
    rcases hD with rfl | rfl
    · exact laurentPlus_subset D₀ f
    · exact laurentMinus_subset D₀ f
  hcover := by
    intro v hv
    rcases laurentCover_covers D₀ f v hv with h | h
    · exact ⟨_, Finset.mem_insert_self _ _, h⟩
    · exact ⟨_, Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton_self _)), h⟩
```

- [ ] **Step 6: Add import and verify**

Add `import «Adic spaces».LaurentRefinement` to `Adic spaces.lean`.

```bash
lake env lean "Adic spaces/LaurentRefinement.lean"
```

- [ ] **Step 7: Fill the covering/subset sorries**

These are set-theoretic arguments about `rationalOpen`. The plus-subset is
trivial (larger T ⊆ same base). The minus-subset uses `rationalOpen_inter`.
The cover uses valuation trichotomy.

- [ ] **Step 8: Fill the hopen sorries**

These require showing the `locSubring` closure condition for the new
rational data. For laurentPlusDatum: same s, larger T — the existing
hopen for D₀ extends (monotonicity of locSubring in T). For
laurentMinusDatum: needs divByS properties for the product denominator.

- [ ] **Step 9: Commit**

```bash
git add "Adic spaces/LaurentRefinement.lean" "Adic spaces.lean"
git commit -m "LaurentRefinement: Laurent covering construction"
```

---

### Task 3: Laurent separation + Lemma 7.54

**Files:**
- Modify: `Adic spaces/LaurentRefinement.lean`

- [ ] **Step 1: Prove Lemma 7.54 (rational decomposition)**

```lean
/-- **Lemma 7.54**: `R({t₁,...,tₙ}/s) = ⋂ᵢ R({tᵢ}/s)`.
A rational subset is the intersection of its "basic" components. -/
theorem rationalOpen_eq_iInter (T : Finset A) (s : A) :
    rationalOpen T s = ⋂ t ∈ T, rationalOpen {t} s := by
  ext v
  simp only [Set.mem_iInter, Set.mem_setOf_eq, rationalOpen,
    Finset.mem_singleton, forall_eq]
  constructor
  · intro ⟨hspa, hvle, hvs⟩ t ht
    exact ⟨hspa, fun t' ht' => by rw [Finset.mem_singleton.mp ht']; exact hvle t ht, hvs⟩
  · intro h
    sorry -- assemble from individual pieces
```

- [ ] **Step 2: Laurent separation for the whole-ring base**

Connect `epsilonHom_gen_injective` to `productRestriction` for the case
where the base is the whole ring. This is the key bridge.

```lean
/-- For a 2-element Laurent cover of the whole ring, the product restriction
is injective. Transfers `epsilonHom_gen_injective` via TopologyComparison. -/
theorem laurentCovering_injective_of_whole
    [IsTateRing A] [IsNoetherianRing A] [IsDomain A] [T2Space A]
    [NonarchimedeanRing A] [FirstCountableTopology A]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (D₀ : RationalLocData A) (f : A) (hf : ¬IsUnit f)
    -- TopologyComparison hypotheses bundled:
    ... :
    Function.Injective (productRestriction A (laurentCovering D₀ f)) := by
  sorry -- Connect epsilonHom_gen_injective to productRestriction
        -- via presheafValueTateQuotientEquiv
```

**Implementation note:** This is the hardest proof. The bridge needs:
1. The TopologyComparison isomorphisms for D₀ and both Laurent halves
2. Showing the transferred product map equals epsilonHom_gen (or a variant)
3. Applying epsilonHom_gen_injective

- [ ] **Step 3: Commit intermediate progress**

```bash
git commit -am "LaurentRefinement: Lemma 7.54 + Laurent separation stub"
```

---

### Task 4: Lemma 8.34 + assembly

**Files:**
- Modify: `Adic spaces/LaurentRefinement.lean`
- Modify: `Adic spaces/StructureSheaf.lean` (replace sorry)

- [ ] **Step 1: Construct product of Laurent covers**

```lean
/-- Product of Laurent covers: given elements `fs`, construct the
covering by all 2^n intersections of Laurent halves. -/
noncomputable def laurentProduct (D₀ : RationalLocData A) :
    List A → RationalCovering A
  | [] => trivialCovering D₀
  | f :: fs => crossProduct (laurentCovering D₀ f) (laurentProduct D₀ fs)
```

Where `trivialCovering` is the 1-element covering {D₀} and `crossProduct`
forms pairwise intersections.

- [ ] **Step 2: Prove product separation (inductive)**

```lean
theorem laurentProduct_injective ... (fs : List A)
    (hfs : ∀ f ∈ fs, ¬IsUnit f) :
    Function.Injective (productRestriction A (laurentProduct D₀ fs)) := by
  induction fs with
  | nil => exact trivialCovering_injective D₀
  | cons f fs ih =>
    -- crossProduct of Laurent(f) and laurentProduct(fs)
    -- Use Laurent separation for f + inductive hypothesis for fs
    sorry
```

- [ ] **Step 3: Prove Lemma 8.34 (Laurent refinement exists)**

```lean
/-- **Lemma 8.34**: every rational covering is refined by a product of
Laurent covers. -/
theorem exists_laurentProduct_refinement (C : RationalCovering A) :
    ∃ fs : List A,
      RationalRefinement (laurentProduct C.base fs) C := by
  sorry -- Take fs = list of D.s for D ∈ C.covers
        -- Each Laurent product piece sits inside some C-piece
```

- [ ] **Step 4: Assembly in LaurentRefinement.lean**

```lean
/-- Every rational covering has injective product restriction
(Theorem 8.28, separation component). -/
theorem productRestriction_injective_of_laurent
    [IsTateRing A] [IsNoetherianRing A] [IsDomain A] ...
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (C : RationalCovering A) :
    Function.Injective (productRestriction A C) :=
  let ⟨fs, r⟩ := exists_laurentProduct_refinement C
  separation_of_finer_rational _ _ r (laurentProduct_injective ... fs ...)
```

- [ ] **Step 5: Replace sorry in StructureSheaf.lean**

Replace:
```lean
theorem productRestriction_injective_of_laurentRefinement ... := by
  sorry
```
With:
```lean
theorem productRestriction_injective_of_laurentRefinement ... :=
  productRestriction_injective_of_laurent A P C
```

- [ ] **Step 6: Verify with lean_verify**

Check `isSheafy_ofStronglyNoetherianTate_flat` has no `sorryAx`.

- [ ] **Step 7: Final commit**

```bash
git add "Adic spaces/LaurentRefinement.lean" "Adic spaces/StructureSheaf.lean"
git commit -m "IsSheafy: strongly noetherian Tate rings are sheafy (0 sorry)"
```
