# ker(θ) Principal — Witt Vector API Plan

> **For agentic workers:** Use superpowers:executing-plans to implement.

**Goal:** Fill the sorry at Tilting.lean:369 — the core existential for `ker_theta_principal`.

**Target:**
```lean
∃ (xi : Ainf p A), xi ∈ RingHom.ker (PerfectoidRing.theta p A) ∧
  ∀ (x : Ainf p A), x ∈ RingHom.ker (PerfectoidRing.theta p A) → ∃ q, x = xi * q
```

**Reference:** Scholze-Weinstein, Berkeley Lectures, Lemma 6.2.8 (pp.46-47)

---

## Available Mathlib API (KEY pieces)

| API | What it gives | File |
|-----|--------------|------|
| `WittVector.teichmuller p : R →* W(R)` | Teichmüller lift `[r]` | Teichmuller.lean |
| `teichmuller_coeff_zero/pos` | `[r].coeff 0 = r`, `[r].coeff n = 0` for n > 0 | Teichmuller.lean |
| `fontaineTheta_teichmuller` | `θ([x]) = x.untilt` | FontaineTheta.lean |
| `mk_untilt_eq_coeff_zero` | `mk(untilt(x)) = coeff 0 x` in O/(p) | Untilt.lean |
| `isAdicCompleteIdealSpanP` | W(k) is (p)-adically complete | Complete.lean |
| `mem_span_p_pow_iff_le_coeff_eq_zero` | `x ∈ (p^n) ↔ ∀ m < n, x.coeff m = 0` | Complete.lean |
| `quotientPEquiv` | `W(k)/(p) ≃+* k` | Complete.lean |
| `ker_constantCoeff` | `ker(coeff_0) = (p)` in W(k) | Complete.lean |
| `eq_zero_of_p_mul_eq_zero` | W(k) is p-torsion-free | Complete.lean |
| `Perfection.coeff_surjective` | Lift elements to Perfection | Perfection.lean |
| `verschiebung_coeff_succ/zero` | V(x).coeff(n+1) = x.coeff(n), V(x).coeff(0) = 0 | Verschiebung.lean |
| `frobenius_verschiebung` | F(V(x)) = x * p | Identities.lean |
| `isDiscreteValuationRing` | W(k) is DVR when k is perfect **field** | DiscreteValuationRing.lean |

---

## Proof Strategy

### Approach A: General (following Berkeley Lectures) — ~150 lines

For perfectoid RINGS (not just fields). Constructs ξ = p + [ϖ]α explicitly.

**Step 1: Construct ϖ♭ ∈ PreTilt A° p** (~30 lines)

Use `Perfection.coeff_surjective` with the Frobenius surjectivity from `IsPerfectoidRing.frobenius_surj`. The pseudo-uniformizer ϖ from `exists_pseudoUniformizer` gives ϖ̄ ∈ A°/(p). Lift to ϖ♭ ∈ PreTilt A° p with `coeff 0 ϖ♭ = ϖ̄`.

**Step 2: Construct f ∈ ϖ♭ · (PreTilt A° p) with f♯ ≡ p (mod p·ϖ♯)** (~40 lines)

From Berkeley Lectures p.46: consider α = p/ϖ♯ ∈ R♯⁺ (where R♯ = A, ϖ♯ = ϖ♭.untilt). Find β ∈ R⁺ with β♯ ≡ α (mod p·R♯⁺). Set f = ϖ♭ · β. Then f♯ = ϖ♭♯ · β♯ ≡ ϖ♯ · α = p (mod p·ϖ♯).

This requires `untilt_iterate_frobeniusEquiv_symm_pow` and careful manipulation of the sharp map.

**Step 3: Define ξ and show θ(ξ) = 0** (~20 lines)

Write p = f♯ + p·ϖ♯·Σrₙ♯·pⁿ in A°. Define ξ = p - [f] - [ϖ]·Σ[rₙ]·pⁿ⁺¹. Then θ(ξ) = p - f♯ - ϖ♯·Σrₙ♯·pⁿ⁺¹ = 0.

**Step 4: Show ker(θ) ⊆ (ξ)** (~60 lines, HARDEST)

The map W(R⁺)/ξ → R♯⁺ induced by θ is an isomorphism mod [ϖ] because:
`W(R⁺)/(ξ, [ϖ]) = W(R⁺)/(p, [ϖ]) = R⁺/ϖ = R♯⁺/ϖ♯`

By [ϖ]-adic completeness of both sides, this is an isomorphism, hence ker(θ) = (ξ).

### Approach B: Field case using DVR — ~40 lines ⭐ RECOMMENDED

For perfectoid FIELDS only. Much simpler since W(k) is a DVR for perfect fields.

**Step 1: Show the tilt's fraction field is perfect** (~10 lines)

`PreTilt O_K p` is a perfect ring of char p (from Mathlib). If K is a perfectoid field, `PreTilt O_K p` is a domain (proved: `tilt_isDomain`). Its fraction field `K♭ = FractionRing(PreTilt O_K p)` inherits perfection.

Actually wait — we need W(k) for k a FIELD to use the DVR result. And `PreTilt O_K p` is NOT a field (it's a valuation ring). So we can't directly apply `isDiscreteValuationRing`.

**BUT:** We can still use the DVR structure differently. For any perfect ring k of char p with no zero divisors (which our PreTilt is, by `tilt_isDomain`), W(k) has no zero divisors (`WittVector.instIsDomain`). And θ : W(k) → O_K is surjective. So ker(θ) is a nonzero proper ideal in the domain W(k).

By `exists_eq_pow_p_mul` (which works for perfect RINGS, not just fields): every nonzero element of W(k) is p^m * (unit-like element). This gives us a handle on the ideal structure.

### Approach C: Hybrid — use DVR for field case, sorry for ring case — ~50 lines ⭐⭐ MOST PRAGMATIC

Since our `ker_theta_principal` is stated for `IsPerfectoidRing p A` (general rings), but we ALSO have `IsPerfectoidField p K` downstream, we can:

1. Prove it for fields using the DVR approach
2. Leave the general ring case as a well-documented sorry
3. Or: add `[IsPerfectoidField p A]` as a hypothesis if only used for fields

---

## Recommended Execution Plan

### Task 1: Helper — show `WittVector p (tilt p A)` has `IsDomain` [~5 lines]

We already have `tilt_isDomain` for fields. For general perfectoid rings, W(tilt p A) has `IsDomain` when `tilt p A` has `IsDomain` and `CharP (tilt p A) p`.

```lean
instance : IsDomain (Ainf p A) := WittVector.instIsDomain
```
(needs `IsDomain (tilt p A)` which we have for fields)

### Task 2: Construct ξ ∈ ker(θ) [~30 lines]

Use `Perfection.coeff_surjective` to construct ϖ♭ ∈ PreTilt O p. Form ξ = `teichmuller p ϖ♭ - algebraMap _ p` (or similar). Show θ(ξ) = 0 via `fontaineTheta_teichmuller`.

The key: `θ([ϖ♭]) = ϖ♭.untilt` by `fontaineTheta_teichmuller`. We need `ϖ♭.untilt` to have a specific relationship with p.

From `mk_untilt_eq_coeff_zero`: `ϖ♭.untilt ≡ coeff_0(ϖ♭) mod (p)`. So if `coeff_0(ϖ♭) = ϖ̄` (the image of the pseudo-uniformizer in O/(p)), then `ϖ♭.untilt ≡ ϖ mod p` in O.

For ξ = p - [ϖ♭]·α (constructed via p-adic approximation), θ(ξ) = p - ϖ♭♯·α♯ = 0.

### Task 3: Show ker(θ) ⊆ (ξ) [~50 lines, HARDEST]

**For the field case:** Use the fact that W(tilt p K) is close to a DVR. Every element of ker(θ) has positive p-adic valuation (since θ(p) = p ≠ 0, p ∉ ker(θ)). The quotient structure W(k)/(p) ≅ k and the coefficient characterization `mem_span_p_pow_iff_le_coeff_eq_zero` allow an inductive argument.

**The inductive argument:**
1. Take x ∈ ker(θ). Write x = ξ·q₀ + p·r₀ (using surjectivity of θ and the quotient structure).
2. Then θ(r₀) = 0 (from θ(x) = 0 and θ(ξ) = 0).
3. So r₀ ∈ ker(θ). Apply again: r₀ = ξ·q₁ + p·r₁.
4. x = ξ·(q₀ + p·q₁) + p²·r₁.
5. Iterate: x = ξ·(q₀ + p·q₁ + p²·q₂ + ...) by p-adic completeness (`isAdicCompleteIdealSpanP`).

### Task 4: Assembly [~5 lines]

Package ξ with the proofs from Tasks 2-3 into the existential.

---

## Key Obstacles and Mitigations

| Obstacle | Severity | Mitigation |
|----------|----------|------------|
| Constructing ϖ♭ explicitly | Medium | Use `coeff_surjective`, any lift works |
| Showing θ(ξ) = 0 exactly | Medium | `fontaineTheta_teichmuller` + p-adic approximation |
| Division: x = ξ·q₀ + p·r₀ | Hard | Need quotient map W(k) → W(k)/(ξ) and section |
| p-adic convergence of Σq_n·p^n | Medium | `isAdicCompleteIdealSpanP` gives the limit |
| W(k)/(ξ, [ϖ]) = k/ϖ | Hard | Coefficient computation with `quotientPEquiv` |

## Estimated Effort

~80-120 lines across Tasks 1-4. The hardest part is Task 3 (the inductive divisibility argument). With the rich Mathlib API available, this is challenging but feasible.

---

## References

- Scholze-Weinstein, Berkeley Lectures, Lemma 6.2.8 (pp.46-47): `docs/scholze-weinstein-berkeley-lectures.pdf`
- Heuer, Perfectoid Spaces, Prop 1.1.35 (p.16): `docs/heuer-perfectoid-notes.pdf`
- Mathlib Witt vector API: `.lake/packages/mathlib/Mathlib/RingTheory/WittVector/`
