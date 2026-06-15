# Rank-1 Domination: Closing the Last Sorry

> **For agentic workers:** REQUIRED: Use superpowers:subagent-driven-development (if subagents available) or superpowers:executing-plans to implement this plan. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Fill the last sorry in `exists_mulArchimedean_valuationSubring_of_prime` (Lemma745.lean:762), producing a rank-1 (MulArchimedean) valuation subring dominating a local subring with I-images as nonunits.

**Architecture:** Two approaches analyzed. Approach (ii) is recommended — it follows Wedhorn's proof exactly and requires less new infrastructure.

---

## The Sorry

```lean
∃ V : ValuationSubring (FractionRing (A ⧸ 𝔭)),
    (P.toFractionQuotient 𝔭).range ≤ V.toSubring ∧
    ... ⊆ V.nonunits ∧
    MulArchimedean V.ValueGroup
```

We need V with (1) range containment, (2) I-nonunits, (3) MulArchimedean.

---

## Approach (i): Rank-1 Zorn (Bourbaki CA VI §8 No.6)

**Idea:** Apply Zorn's lemma to the set of local subrings of K = Frac(A/𝔭) that:
- Contain the image of A₀
- Have maximal ideal containing I-images
- Have "rank ≤ 1" property (no proper convex subgroup of the value group separates 1 from the I-images)

**Pros:** Self-contained, no dependence on localization theory.
**Cons:** Controlling the rank under Zorn unions is hard. Need to show the union of a chain of "rank-1-like" local subrings preserves the rank property. Approximately 100-150 lines.

---

## Approach (ii): Chevalley Extension (Wedhorn 7.44) — RECOMMENDED

**Idea:** Follow Wedhorn's actual proof:
1. Get v₀ on A from domination (arbitrary rank)
2. Apply `restrictToConvex` to v₀|_{A₀} with `H_gen = convexGenerated(u₀⁻¹)` → get `v_r` on A₀ (rank 1, continuous, cofinal PROVED)
3. Extend `v_r` from A₀ to A using the localization isomorphism (A₀)_𝔮 ≅ A_𝔭

### Key mathematical input: Lemma 7.44(1)

For B = A₀ (open subring), 𝔭 non-open prime of A, 𝔮 = 𝔭 ∩ A₀:
**B_𝔮 → A_𝔭 is an isomorphism.**

Proof (from Wedhorn): Since 𝔮 is non-open in A₀, ∃ s ∈ A₀^{oo} (topologically nilpotent) with s ∉ 𝔮. Since A₀ is open: for any a ∈ A, ∃ n with s^n · a ∈ A₀ (because x ↦ x·a is continuous and s^n → 0 ∈ A₀). So A_s = (A₀)_s (same localization). Since 𝔮 ⊂ (s)^c: the localization at 𝔮 factors through A_s.

### Extension construction

For a ∈ A: pick s ∈ I \ 𝔭 (exists from non-openness), n with s^n · a ∈ A₀. Define:
```
v(a) = v_r(s^n · a) / v_r(s)^n
```
where v_r = restrictToConvex(v₀|_{A₀}, H_gen).

### What needs to be proved

1. **Well-definedness:** v(a) is independent of the choice of n (and s).
2. **Valuation axioms:** v(0) = 0, v(1) = 1, v(ab) = v(a)v(b), v(a+b) ≤ max(v(a), v(b)).
3. **Extension:** v|_{A₀} = v_r.
4. **Continuity:** v is continuous on A.
   - From Lemma 7.44(2): v continuous iff v|_{A₀} = v_r continuous. And v_r IS continuous (cofinal property, ALREADY PROVED).
   - The proof: {a ∈ A : v(a) < γ} ⊇ {b ∈ A₀ : v_r(b) < γ}, which is open in A₀, hence in A. An additive subgroup containing an open set is open.
5. **Support:** supp(v) ⊇ 𝔭.
6. **A⁺ bound:** v(f) ≤ 1 for f ∈ A⁺ (from A⁺ ⊆ A₀ and v_r ≤ 1 on A₀).
7. **Spa membership:** v ∈ Spa A A⁺.

### File structure

| File | Action | Lines | Content |
|------|--------|-------|---------|
| `Adic spaces/Lemma745.lean` | Modify | +80 | Extension construction + proof |

### Task breakdown

#### Task 1: The element s ∈ I \ 𝔭

We already have `P.exists_mem_I_not_mem_of_not_isOpen h𝔭` which gives `a₀ ∈ I` with `a₀ ∉ 𝔭`. Use s = P.A₀.subtype a₀.

#### Task 2: The "s^n · a ∈ A₀" property

For a ∈ A: show ∃ n, s^n · a ∈ A₀. This uses:
- s is topologically nilpotent (s ∈ I ⊆ A₀^{oo} since I-adic complete implies I ⊆ Jacobson radical)
- A₀ is open in A
- Multiplication is continuous

In Lean: `IsTopologicallyNilpotent s` gives `s^n → 0`. Since A₀ is open (contains a neighborhood of 0): eventually `s^n ∈ {x : x · a ∈ A₀}` which is open (preimage of A₀ under continuous map x ↦ x·a).

**Actually:** we might not need this in full generality. For the Spa point, we can use the EXISTING `exists_mulArchimedean_valuationSubring_of_prime` API: we just need to fill the sorry by producing V.

#### Task 3: Construct V directly

Instead of constructing v on A and then taking V = v.valuationSubring, we can construct V directly:

V = v_r.valuationSubring (as a valuation subring of... hmm, v_r is on A₀ not on K).

Actually, the simplest construction:

**V = the valuation subring of K corresponding to the valuation v on K defined by the extension.**

But defining v on K requires the extension construction.

#### Alternative: Bypass the extension entirely

The theorem `exists_mulArchimedean_valuationSubring_of_prime` asks for V : ValuationSubring K. We can construct V WITHOUT defining a valuation on A first:

1. Get V₀ from domination (valuation subring of K)
2. H_gen = convexGenerated(u₀⁻¹) in V₀.ValueGroupˣ
3. P_H = primeOfConvexSubgroup V₀ H_gen (from ValuationPrimeConvex.lean)
4. V = V₀.ofPrime P_H

V₀.ofPrime P_H has:
- V₀ ≤ V₀.ofPrime P_H (range containment ✓)
- I-images ∈ P_H iff unit(value) ∉ H_gen. For I-generators with value ≤ u₀:
  the unit might or might not be in H_gen.

**THIS IS THE SAME ISSUE AS BEFORE.** The I-generators with value STRICTLY LESS than u₀ might be in H_gen (bounded by powers of u₀⁻¹) or not (if at a different "level").

For generators with value u_i ≤ u₀ < 1:
- u_i ∈ H_gen = convexGenerated(u₀⁻¹) iff ∃ n, u₀^n ≤ u_i ≤ u₀^{-n}
- Upper bound: u_i ≤ 1 ≤ u₀^{-1}. ✓
- Lower bound: u₀^n ≤ u_i for some n. Since u_i ≤ u₀ = u₀^1, need u₀^n ≤ u_i for n ≥ 1.
  u₀^2 < u₀ (since u₀ < 1). If u_i ≥ u₀^2: take n = 2. ✓
  If u_i < u₀^2: try n = 3. u₀^3 < u₀^2. If u_i ≥ u₀^3: ✓
  Continue: u_i ≥ u₀^n for some n iff u_i is not "infinitesimally below u₀".

In a rank-1 value group: u₀^n → 0, so u_i ≥ u₀^n for large n. ✓
In a rank-≥2 value group: u₀^n might not → 0. u_i could be "below all u₀^n" at a different level. ✗

**CONCLUSION:** The sorry CANNOT be filled without producing a rank-1 V₀ from scratch. The current Mathlib infrastructure only provides arbitrary-rank V₀.

---

## Resolution Path

The cleanest resolution: **formalize Lemma 7.44(2)** (continuity extension from open subring to full ring) and **Lemma 7.44(3)** (bijection of analytic continuous valuations). Then:

1. Apply `restrictToConvex` to get continuous v_r on A₀ (DONE, cofinal proved)
2. By 7.44(3): ∃! v on A with v|_{A₀} = v_r
3. v is continuous (by 7.44(2))
4. v ∈ Spa A
5. Take V = v.valuationSubring → MulArchimedean by construction of v_r

### Estimated effort

| Component | Lines | Difficulty |
|-----------|-------|-----------|
| Lemma 7.44(1): localization isomorphism | 40 | Hard |
| Lemma 7.44(2): continuity extension | 25 | Medium |
| Lemma 7.44(3): analytic valuation bijection | 15 | Medium |
| Extension construction (v from v_r) | 50 | Hard |
| Close the sorry | 20 | Easy (assembly) |
| **Total** | **~150** | |

### Prerequisites from Mathlib
- Localization at a prime: `Localization.AtPrime`
- Open subring properties
- Topologically nilpotent element outside a prime (from IsAdicComplete)
- `AddSubgroup.isOpen_of_mem_nhds` (open subgroup contains neighborhood)
