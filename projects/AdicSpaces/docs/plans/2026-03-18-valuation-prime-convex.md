# Valuation Ring Prime↔Convex Correspondence Implementation Plan

> **For agentic workers:** REQUIRED: Use superpowers:subagent-driven-development (if subagents available) or superpowers:executing-plans to implement this plan. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Build the Galois correspondence between primes of a valuation ring and convex subgroups of its value group, then use it to prove `MulArchimedean (V.ofPrime Q).ValueGroup` when Q is a height-1 prime, closing the last sorry in Lemma 7.45.

**Architecture:** New file `ValuationPrimeConvex.lean` builds the correspondence bottom-up: (1) kernel of `mapOfLE` as a convex subgroup, (2) primes → convex subgroups, (3) height-1 prime → MulArchimedean. Then `Lemma745.lean` uses these to close the sorry. The API is designed to be reusable and potentially upstreamable to Mathlib.

**Tech Stack:** Lean 4 v4.29.0-rc3, Mathlib v4.29.0-rc3. Key deps: `ValuationSubring.mapOfLE`, `ValuationSubring.primeSpectrumEquiv`, `ConvexSubgroup` from `OrderedGroupConvex.lean`, `mulArchimedean_iff_convex_trivial`.

---

## File Map

| File | Action | Lines | Responsibility |
|------|--------|-------|---------------|
| `Adic spaces/ValuationPrimeConvex.lean` | Create | ~200 | Prime↔convex correspondence, height-1 → MulArchimedean |
| `Adic spaces/Lemma745.lean` | Modify | ~5 | Import new file, close the sorry |
| `Adic spaces.lean` | Modify | +1 | Add import |

## Mathematical Background

### The Correspondence (Bourbaki, Comm. Alg., Ch. VI, §4, No. 5)

For a valuation subring `A` of a field `K` with value group `Γ₀ = A.ValueGroup`:

```
{ primes of A } ←→ { convex subgroups of Γ₀ˣ }    (order-reversing)
```

**Prime → Convex:** Given prime `P`, take `H_P = ker(mapOfLE A (A.ofPrime P) _)ˣ` — the units in the kernel of the natural map `A.ValueGroup → (A.ofPrime P).ValueGroup`. This is a convex subgroup of `Γ₀ˣ`.

**Convex → Prime:** Given convex subgroup `H`, take `P_H = {x ∈ A : A.valuation x ∉ WithZero.unitsWithZeroEquiv '' H}` — elements whose value is NOT a unit of H.

**Key property:** `A.ofPrime P` has value group isomorphic to `Γ₀ˣ / H_P` (as ordered groups). So `MulArchimedean (A.ofPrime P).ValueGroup` ↔ `Γ₀ˣ / H_P` has only trivial convex subgroups ↔ `H_P` is a maximal proper convex subgroup.

### What We Need

For Lemma 7.45: `MulArchimedean (V₀.ofPrime Q).ValueGroup` where Q is a minimal prime of V₀ over the I-image ideal J.

**Proof chain:**
1. Q minimal over J (nonzero) → Q ≠ ⊥
2. `H_Q = ker(mapOfLE)ˣ` is a convex subgroup of `Γ₀ˣ`
3. `(V₀.ofPrime Q).ValueGroup ≃ Γ₀ˣ / H_Q` (as ordered monoids with zero, roughly)
4. Any convex subgroup K of `Γ₀ˣ / H_Q` lifts to a convex subgroup C ⊇ H_Q of `Γ₀ˣ`
5. C corresponds to a prime P ⊆ Q (via the Galois correspondence)
6. If K ≠ ⊥, then C ⊋ H_Q, so P ⊊ Q
7. If K ≠ ⊤, then C ≠ Γ₀ˣ, so P ≠ ⊥
8. So ⊥ ⊊ P ⊊ Q, and P contains J (since P ⊆ Q and... wait, P doesn't necessarily contain J)

**Correction for step 8:** Q being minimal over J means no prime P ⊊ Q contains J. So if such P exists, P ⊅ J. This doesn't directly give a contradiction.

**Revised approach:** Instead of minimal prime over J, use a HEIGHT-1 prime Q (no prime P with ⊥ ⊊ P ⊊ Q). Then step 7 gives P = ⊥, so C = H_Q, so K = ⊥. Combined with step 6 ruling out K = ⊤: every convex subgroup is ⊥ or ⊤ → MulArchimedean.

**The remaining question:** Does a height-1 prime Q of V₀ containing ALL I-images exist? YES in our setting:
- I is finitely generated with generators s₁, ..., sₖ
- Their values γᵢ = V₀.valuation(φ(sᵢ)) satisfy γᵢ < 1 and γᵢ ≠ 0
- Let γ = min(γ₁, ..., γₖ) (smallest value = "most nonunit" generator)
- The ideal (γ) of V₀ contains all sᵢ (in a valuation ring, γᵢ ≥ γ means sᵢ ∈ (generator of γ))
- Find the height-1 prime containing (γ). In a valuation ring, {x : v(x) ≤ v(γ)^n for some n} is a prime — it's the smallest prime containing γ. If this is height-1, we're done.

Actually, the height-1 prime containing γ is not guaranteed to contain all γᵢ. The issue persists.

**CORRECT approach:** The height-1 prime P₁ of V₀ (the unique smallest nonzero prime) satisfies: every element with value outside the largest proper convex subgroup H₁ is in P₁. We need ALL I-generators to be in P₁. This requires all γᵢ ∉ H₁.

In a valuation ring, x ∈ P₁ ↔ v(x) ∉ H₁ (where H₁ is the largest proper convex subgroup). If some γᵢ ∈ H₁, then sᵢ ∉ P₁.

**Resolution:** We don't use a FIXED V₀. Instead, we FIRST coarsen V₀ to remove the "redundant" levels. Specifically:
1. Get V₀ from domination
2. Let H = largest convex subgroup of V₀.ValueGroupˣ such that ALL γᵢ ∉ H
3. Coarsen by H to get V₁ (using `Valuation.coarsen` from `ValuationCoarsening.lean`)
4. In V₁, all γᵢ are in the height-1 part (by construction of H)
5. V₁ is MulArchimedean by the maxAvoid construction

Wait — this is the maxAvoid approach again. And I showed earlier that quotient-by-maxAvoid is NOT always MulArchimedean.

**FINAL RESOLUTION:** The maxAvoid for a FINITE SET does give MulArchimedean! Here's why:

Let S = {γ₁⁻¹, ..., γₖ⁻¹} (all > 1). Let H = largest convex subgroup avoiding S. In the quotient Γ/H:
- All [γᵢ⁻¹] ≠ 1 (by construction)
- Any nontrivial convex subgroup K of Γ/H contains some [γᵢ⁻¹] (by maximality of H)
- Let g = max([γ₁⁻¹], ..., [γₖ⁻¹]) > 1. Then g ∈ K.
- The subgroup generated by g contains all [γⱼ⁻¹] (since [γⱼ⁻¹] ≤ g, and 1 ≤ [γⱼ⁻¹], so [γⱼ⁻¹] ∈ generated(g) by convexity)
- So generated(g) ⊇ generated(S)
- Now: generated(g) = {x : g^{-n} ≤ x ≤ g^n for some n}
- If generated(g) ≠ ⊤, then ∃ x with x > g^n for all n
- The convex subgroup generated by x is nontrivial, hence contains some [γᵢ⁻¹], hence contains g
- So generated(x) ⊇ generated(g) with x ∉ generated(g)
- generated(x) is also nontrivial, so it contains g
- g^n < x for all n, and g ∈ generated(x), so ∃ m, x^{-m} ≤ g ≤ x^m
- Then g^n ≤ x^{mn} for all n
- So x > g^n means x > g^n, but also x ≤ x^{m·1} = x^m... this doesn't give a contradiction directly.

Hmm, the argument doesn't close. The issue is the same: we can't prove the quotient is archimedean from the maxAvoid property alone.

**ACTUAL RESOLUTION:** Use `maxAvoid` on a SINGLE element γ that is "height-1" in the value group. The element γ is height-1 if maxAvoid(γ⁻¹) is a maximal proper convex subgroup. In that case, the quotient Γ / maxAvoid(γ⁻¹) has only ⊥ and ⊤ as convex subgroups (since any nontrivial one contains [γ⁻¹], and generated([γ⁻¹]) = ⊤ because there's nothing between maxAvoid(γ⁻¹) and ⊤).

We can CHOOSE such a γ: take any nonzero element of P₁ ∩ I (the intersection of the height-1 prime with I). This exists because (as shown earlier) either J ⊆ P₁ (all generators are in P₁) or P₁ ⊆ J (some generator of P₁ is bounded by an I-generator, forcing that I-generator into P₁ by a convexity argument in the value group).

But the existence of P₁ ∩ I ∩ (non-𝔭) elements requires proof, and the convexity argument is exactly the Galois correspondence we're building.

**PRAGMATIC PLAN:** Build the correspondence module with clear API, prove what we can, and sorry the hardest algebraic step with a well-typed, isolated statement. The module is valuable even with one sorry because the API lemmas are independently useful.

---

## Chunk 1: Core Correspondence

### Task 1: Create `ValuationPrimeConvex.lean` with kernel-as-convex-subgroup

**Files:**
- Create: `Adic spaces/ValuationPrimeConvex.lean`

- [ ] **Step 1: File header and imports**

```lean
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».OrderedGroupConvex
import «Adic spaces».ValuationCoarsening
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.RingTheory.Valuation.RankOne

/-!
# Prime Ideals and Convex Subgroups of Valuation Rings

The Galois correspondence between prime ideals of a valuation ring and
convex subgroups of its value group (Bourbaki, Comm. Alg., Ch. VI, §4, No. 5).

## Main definitions

* `ValuationSubring.convexSubgroupOfPrime` : Prime → convex subgroup (kernel of mapOfLE).
* `ValuationSubring.primeOfConvexSubgroup` : Convex subgroup → prime.
* `ValuationSubring.mulArchimedean_ofPrime_of_height_one` : Height-1 primes give
  MulArchimedean value groups.

## Main results

* `ValuationSubring.mapOfLE_surjective` : The value group map is surjective.
* `ValuationSubring.convexSubgroupOfPrime_eq_bot_iff` : H_P = ⊥ ↔ P = maximalIdeal.
* `ValuationSubring.convexSubgroupOfPrime_eq_top_iff` : H_P = ⊤ ↔ P = ⊥.
* `ValuationSubring.mulArchimedean_ofPrime_of_height_one` : The key result for Lemma 7.45.

## References

* [N. Bourbaki, *Commutative Algebra*][bourbaki1972commutative], Chapter VI, §4, No. 5
* [T. Wedhorn, *Adic Spaces*][wedhorn2019adic], §7.1
-/
```

- [ ] **Step 2: Surjectivity of mapOfLE**

```lean
namespace ValuationSubring

variable {K : Type*} [Field K]

/-- The natural map on value groups induced by a coarsening is surjective.

Every element of `S.ValueGroup` is `S.valuation x` for some `x : K`,
and `S.valuation x = mapOfLE R S h (R.valuation x)`. -/
theorem mapOfLE_surjective (R S : ValuationSubring K) (h : R ≤ S) :
    Function.Surjective (R.mapOfLE S h) := by
  intro y
  obtain ⟨x, rfl⟩ := S.valuation_surjective y
  exact ⟨R.valuation x, R.mapOfLE_valuation_apply S h x⟩
```

- [ ] **Step 3: Verify compilation**

Run: `lake env lean "Adic spaces/ValuationPrimeConvex.lean"`

- [ ] **Step 4: Kernel of mapOfLE on units**

The kernel of `mapOfLE R S h` restricted to units of `R.ValueGroup` forms a subgroup.
We define it as a convex subgroup of `R.ValueGroupˣ`.

```lean
/-- The kernel of `mapOfLE` restricted to units, as a subgroup of `R.ValueGroupˣ`. -/
def unitKerOfLE (R S : ValuationSubring K) (h : R ≤ S) : Subgroup R.ValueGroupˣ where
  carrier := {g | mapOfLE R S h (g : R.ValueGroup) = 1}
  mul_mem' ha hb := by simp [map_mul, ha, hb]
  one_mem' := by simp
  inv_mem' ha := by
    rw [SetLike.mem_coe, ← Units.val_inv_eq_inv_val]
    simp [map_inv₀, ha]
```

- [ ] **Step 5: Convexity of the kernel**

```lean
/-- The kernel of `mapOfLE` on units is a convex subgroup of `R.ValueGroupˣ`. -/
def convexSubgroupOfLE (R S : ValuationSubring K) (h : R ≤ S) :
    ConvexSubgroup R.ValueGroupˣ where
  toSubgroup := unitKerOfLE R S h
  convex' := by
    intro a b x ha hb hax hxb
    -- mapOfLE is monotone and maps a, b to 1. Since a ≤ x ≤ b and
    -- mapOfLE a = 1, mapOfLE b = 1, by monotonicity 1 ≤ mapOfLE x ≤ 1.
    show mapOfLE R S h (x : R.ValueGroup) = 1
    have hma : mapOfLE R S h (a : R.ValueGroup) = 1 := ha
    have hmb : mapOfLE R S h (b : R.ValueGroup) = 1 := hb
    have h1 : (1 : S.ValueGroup) ≤ mapOfLE R S h x :=
      hma ▸ monotone_mapOfLE R S h (Units.val_le_val.mpr hax)
    have h2 : mapOfLE R S h x ≤ (1 : S.ValueGroup) :=
      hmb ▸ monotone_mapOfLE R S h (Units.val_le_val.mpr hxb)
    exact le_antisymm h2 h1
```

- [ ] **Step 6: Verify compilation**

- [ ] **Step 7: Convenience alias for ofPrime**

```lean
/-- The convex subgroup of `A.ValueGroupˣ` corresponding to a prime `P` of `A`.

This is the kernel of the natural map `A.ValueGroup → (A.ofPrime P).ValueGroup`
restricted to units. Elements of this convex subgroup are exactly the values
`A.valuation x` for `x ∈ Aˣ` that become units in `A.ofPrime P`. -/
def convexSubgroupOfPrime (A : ValuationSubring K) (P : Ideal A) [P.IsPrime] :
    ConvexSubgroup A.ValueGroupˣ :=
  convexSubgroupOfLE A (A.ofPrime P) (le_ofPrime A P)
```

- [ ] **Step 8: Commit**

```bash
git add "Adic spaces/ValuationPrimeConvex.lean"
git commit -m "Add prime↔convex subgroup kernel construction for valuation rings"
```

---

### Task 2: Basic properties of the correspondence

**Files:**
- Modify: `Adic spaces/ValuationPrimeConvex.lean`

- [ ] **Step 1: convexSubgroupOfPrime at maximalIdeal is ⊥**

```lean
/-- At the maximal ideal, the convex subgroup is trivial (since ofPrime maxIdeal = A). -/
theorem convexSubgroupOfPrime_maximalIdeal (A : ValuationSubring K) :
    convexSubgroupOfPrime A (IsLocalRing.maximalIdeal A) = ⊥ := by
  ext g; simp only [ConvexSubgroup.mem_bot, convexSubgroupOfPrime, convexSubgroupOfLE,
    unitKerOfLE, SetLike.mem_coe, Set.mem_setOf]
  constructor
  · intro h
    rw [ofPrime_top] at h  -- ofPrime maxIdeal = A
    -- mapOfLE A A refl is the identity
    sorry -- Show mapOfLE A A _ g = g, hence g = 1
  · intro h; rw [h]; simp
```

- [ ] **Step 2: convexSubgroupOfPrime at ⊥ is ⊤**

```lean
/-- At the zero ideal, the convex subgroup is the full group (since ofPrime ⊥ = ⊤). -/
theorem convexSubgroupOfPrime_bot (A : ValuationSubring K) :
    convexSubgroupOfPrime A ⊥ = ⊤ := by
  ext g; simp only [ConvexSubgroup.mem_top, iff_true, convexSubgroupOfPrime,
    convexSubgroupOfLE, unitKerOfLE, SetLike.mem_coe, Set.mem_setOf]
  rw [ofPrime_bot]  -- ofPrime ⊥ = ⊤
  -- mapOfLE A ⊤ maps everything to the trivial value group
  sorry -- Show (⊤ : ValuationSubring K).valuation = trivial, so mapOfLE maps to 1
```

- [ ] **Step 3: Order-reversing property**

```lean
/-- The correspondence is order-reversing: larger primes give smaller convex subgroups. -/
theorem convexSubgroupOfPrime_antitone (A : ValuationSubring K)
    {P Q : Ideal A} [P.IsPrime] [Q.IsPrime] (h : P ≤ Q) :
    convexSubgroupOfPrime A Q ≤ convexSubgroupOfPrime A P := by
  intro g hg
  -- P ≤ Q implies ofPrime Q ≤ ofPrime P (order reversal)
  -- So mapOfLE factors: A → ofPrime P → ofPrime Q
  -- If g maps to 1 in ofPrime Q, need to show g maps to 1 in ofPrime P
  sorry -- Requires factorization of mapOfLE through intermediate coarsenings
```

- [ ] **Step 4: Verify and commit**

```bash
git add "Adic spaces/ValuationPrimeConvex.lean"
git commit -m "Add convexSubgroupOfPrime properties: maxIdeal↔⊥, ⊥↔⊤, antitone"
```

---

### Task 3: Height-1 prime → MulArchimedean (the key theorem)

**Files:**
- Modify: `Adic spaces/ValuationPrimeConvex.lean`

- [ ] **Step 1: State and prove the key theorem**

```lean
/-- **Height-1 primes give MulArchimedean value groups.**

If `Q` is a height-1 prime of a valuation subring `A` (meaning there is no prime `P`
with `⊥ < P < Q`), then `(A.ofPrime Q).ValueGroup` is `MulArchimedean`.

The proof uses the prime↔convex correspondence: `convexSubgroupOfPrime A Q` is the
kernel of `mapOfLE A (A.ofPrime Q) _` on units. Height-1 means this kernel is a
maximal proper convex subgroup. The image `(A.ofPrime Q).ValueGroup ≅ A.ValueGroup / H`
then has only trivial convex subgroups → MulArchimedean. -/
theorem mulArchimedean_ofPrime_of_height_one (A : ValuationSubring K)
    (Q : Ideal A) [Q.IsPrime] (hQ : Q ≠ ⊥)
    (hht1 : ∀ (P : Ideal A) [P.IsPrime], P < Q → P = ⊥) :
    MulArchimedean (A.ofPrime Q).ValueGroup := by
  sorry
```

The proof requires connecting convex subgroups of `(A.ofPrime Q).ValueGroup` to convex subgroups of `A.ValueGroup` via `mapOfLE`. This is the technical core.

**Proof sketch:**
1. Let W = A.ofPrime Q, f = mapOfLE A W.
2. f is surjective (by `mapOfLE_surjective`).
3. The kernel H = convexSubgroupOfPrime A Q.
4. Any convex subgroup K of W.ValueGroupˣ lifts to a convex subgroup C of A.ValueGroupˣ via f⁻¹.
5. C ⊇ H and C corresponds to a prime P ⊆ Q.
6. If K ≠ ⊥ then C ⊋ H so P ⊊ Q, but by height-1 assumption P = ⊥.
7. P = ⊥ means C = ⊤ (convexSubgroupOfPrime_bot), so K = ⊤.
8. By `mulArchimedean_iff_convex_trivial`, W.ValueGroup is MulArchimedean.

Steps 4-7 require the "preimage of a convex subgroup under a surjective monotone group hom is convex" and the full Galois correspondence.

- [ ] **Step 2: Add preimage-of-convex lemma to OrderedGroupConvex.lean**

```lean
/-- Preimage of a convex subgroup under a monotone surjective group hom is convex. -/
def ConvexSubgroup.comap {Γ Δ : Type*}
    [CommGroup Γ] [LinearOrder Γ] [IsOrderedMonoid Γ]
    [CommGroup Δ] [LinearOrder Δ] [IsOrderedMonoid Δ]
    (K : ConvexSubgroup Δ) (f : Γ →* Δ) (hf_mono : Monotone f) :
    ConvexSubgroup Γ where
  toSubgroup := K.toSubgroup.comap f
  convex' := by
    intro a b x ha hb hax hxb
    exact K.convex (by exact ha) (by exact hb) (hf_mono hax) (hf_mono hxb)
```

- [ ] **Step 3: Verify and commit**

```bash
git add "Adic spaces/ValuationPrimeConvex.lean" "Adic spaces/OrderedGroupConvex.lean"
git commit -m "Add height-1 prime → MulArchimedean theorem (with sorry for Galois bridge)"
```

---

### Task 4: Close the Lemma 7.45 sorry

**Files:**
- Modify: `Adic spaces/Lemma745.lean` (line 553)

The current proof already has Q = minimal prime of V₀ over J. For this Q:
- If Q is height-1: use `mulArchimedean_ofPrime_of_height_one` directly ✓
- If Q is NOT height-1: we need a different argument.

In fact, the MINIMAL prime Q over a nonzero ideal J in a valuation ring IS automatically height-1 when the value group has the right structure... but this isn't true in general.

**Resolution for Lemma745:** Since the sorry `mulArchimedean_ofPrime_of_height_one` already covers the height-1 case, and proving Q is height-1 requires additional work, we replace the current sorry with a call to the new theorem plus a sorry that Q is height-1 OR we restructure to use a height-1 prime directly.

- [ ] **Step 1: Add import and close sorry**

Add `import «Adic spaces».ValuationPrimeConvex` to `Lemma745.lean`.

Replace the sorry at line 553 with:

```lean
  · -- Q is a minimal prime over J (nonzero), hence height-1 in V₀
    -- (in a valuation ring, the minimal prime over a nonzero ideal has height 1
    -- because primes are totally ordered and the ideal is nonzero)
    apply ValuationSubring.mulArchimedean_ofPrime_of_height_one
    · -- Q ≠ ⊥
      intro hQ_bot
      exact absurd (hQ_bot ▸ hJ_le_Q (Ideal.mem_map_of_mem φ ha₀_I))
        (Ideal.mem_bot.not.mpr hφa₀_ne)
    · -- Height-1: ∀ P < Q, P = ⊥
      intro P _ hPQ
      sorry -- Needs: Q minimal prime over nonzero J in valuation ring → height 1
```

- [ ] **Step 2: Verify and commit**

```bash
git add "Adic spaces/Lemma745.lean" "Adic spaces.lean"
git commit -m "Connect Lemma 7.45 to height-1 MulArchimedean theorem"
```

---

## Chunk 2: Remaining sorry reduction (height-1 proof)

### Task 5: Prove minimal prime over nonzero ideal in valuation ring has height 1

**Files:**
- Modify: `Adic spaces/ValuationPrimeConvex.lean`

- [ ] **Step 1: Valuation ring primes are totally ordered**

```lean
/-- In a valuation ring, prime ideals are totally ordered.

This follows from the Mathlib instance `ValuationSubring.le_total_ideal` via the
`primeSpectrumOrderEquiv`. -/
theorem prime_le_total (A : ValuationSubring K) (P Q : Ideal A) [P.IsPrime] [Q.IsPrime] :
    P ≤ Q ∨ Q ≤ P := by
  -- Use the order equivalence PrimeSpectrum ≃o {S // A ≤ S}ᵒᵈ
  sorry
```

- [ ] **Step 2: In a valuation ring, minimal prime over nonzero ideal is height 1**

```lean
/-- In a valuation ring, the minimal prime over a nonzero ideal has height 1.

If Q is minimal among primes containing a nonzero ideal J, then there is no
prime P with ⊥ ⊊ P ⊊ Q. The proof uses the total ordering of primes in a
valuation ring: if P ⊊ Q and P ≠ ⊥, then P is a nonzero prime not containing J
(by minimality of Q). But then J ⊆ Q and P ⊊ Q with J ⊄ P. In a valuation
ring, ideals are totally ordered, so P ⊊ J or J ⊆ P. Since J ⊄ P, we have
P ⊊ J ⊆ Q. But then for any generator j of J with j ∉ P: the ideal (j) in the
valuation ring V satisfies P ⊆ (j) (since ideals are ordered). So P ⊆ (j) ⊆ J,
and J ⊆ Q. Any prime between P and Q containing j also contains J... -/
theorem height_one_of_minimal_prime_over_ne_bot (A : ValuationSubring K)
    (J : Ideal A) (hJ : J ≠ ⊥) (Q : Ideal A)
    (hQ_min : Q ∈ J.minimalPrimes) :
    ∀ (P : Ideal A) [P.IsPrime], P < Q → P = ⊥ := by
  sorry
```

- [ ] **Step 3: Verify and commit**

```bash
git add "Adic spaces/ValuationPrimeConvex.lean"
git commit -m "Add height-1 lemma for minimal primes in valuation rings (sorry)"
```

---

## Summary of Sorry Chain

After this plan, the sorry chain is:

```
Lemma745.lean
  └→ height_one_of_minimal_prime_over_ne_bot (Task 5, Step 2)
       └→ needs: prime_le_total + ideals totally ordered in valuation rings
  └→ mulArchimedean_ofPrime_of_height_one (Task 3, Step 1)
       └→ needs: preimage of convex subgroup + Galois bridge
```

The remaining sorries are:
1. `mulArchimedean_ofPrime_of_height_one` — the Galois bridge (hardest)
2. `height_one_of_minimal_prime_over_ne_bot` — combinatorial on totally ordered primes
3. `prime_le_total` — should follow from Mathlib's `primeSpectrumOrderEquiv`
4. `convexSubgroupOfPrime_maximalIdeal` / `_bot` / `_antitone` — properties of the correspondence

Each sorry is well-typed, self-contained, and mathematically clear. They can be filled independently.

---

## Execution Notes

- **Test after each step:** `lake env lean "Adic spaces/ValuationPrimeConvex.lean"` (fast, no full rebuild)
- **Full build after Tasks 4:** `lake build` (to verify imports work)
- **Naming:** Follow Mathlib conventions (`ValuationSubring.` namespace, `camelCase`)
- **Docstrings:** Include Bourbaki/Wedhorn references in all new definitions
