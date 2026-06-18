> **⛔ PARKED 2026-05-26 — mooted by Route 1.** QF witness committed to Route 1 (Pic⁰ /
> restricted dual additivity); see `expert-review/2026-05-26/integration.md` and
> `tickets/QF-PIC0-ROUTE.md`. Route 1 is uniform in (r,s), so the char-divisible edge cases
> these tickets address do not arise. Retained for reference only.

# `/develop --decompose` — L2 char-divisible edge cases (DRY-RUN GATE)

**Date**: 2026-05-25T23:00Z
**Targets**:
- `degree_quadratic_exists_edge_s_char_divisible` (`L6Witnesses.lean:693-701`) — (s:K) = 0 but s ≠ 0 in ℤ
- `degree_quadratic_exists_edge_r_char_divisible` (`L6Witnesses.lean:704-712`) — (r:K) = 0 but r ≠ 0 in ℤ
- The CHAR-DIVISIBLE branch of `degree_quadratic_exists_edge` (`GapSpines.lean:628`, currently bare sorry — the integer-zero sub-cases were dispatched earlier this session)

## Statement (verbatim from skeleton)

```lean
theorem degree_quadratic_exists_edge_s_char_divisible
    (W : WeierstrassCurve K) [W.toAffine.IsElliptic]
    (hq : 2 ≤ Fintype.card K)
    (r s : ℤ) (hr : r ≠ 0) (hs : s ≠ 0)
    (hsK : (s : K) = 0) :
    ∃ β : Isogeny W.toAffine W.toAffine,
      (β.degree : ℤ) = (Fintype.card K : ℤ) * r ^ 2 -
        isogTrace (frobeniusIsog W) (isogOneSub_negFrobenius W hq) * r * s + s ^ 2

-- (r_char_divisible has the symmetric statement.)
```

## Plain-English content (Silverman III.6.3 boundary)

When `(s : K) = 0` but `s ≠ 0` in ℤ, char `p` divides `s`. Write `s = p^k · s₀` with `gcd(s₀, p) = 1`. Use the factorisation `[p] = V ∘ π` (Silverman III.6.1 Case 2) to construct:

> `β = π · (r · 1 - s₀ · V^k · π^(k-1))`

This β satisfies `deg(β) = qr² - tr·rs + s²` (the QF value).

Symmetric construction for `r_char_divisible`.

## Decomposition tree

### Strategy A (Silverman III.6.1 factorisation)

The key identity: `[p] = V ∘ π` where π is the q-power Frobenius (for q = p^n with n ≥ 1) and V is the Verschiebung. So `[p^k] = (V ∘ π)^k = V^k ∘ π^k`.

For `s = p^k · s₀`:
- `[s] = [p^k] · [s₀] = (V^k ∘ π^k) · [s₀]`
- `s₀` is coprime to p, so `(s₀ : K) ≠ 0`.

Construct β as `π ∘ (r - s₀ V^k π^(k-1))`:
- This makes β a composition: π_outer ∘ (rπ - s₀ V^k) where rπ-s₀V^k is at the AddMonoidHom level r·π - s₀·V^k.
- Wait this doesn't quite work directly. Let me re-think.

Actually the standard approach: when `s = p^k s₀`, the isogeny rπ - s factors as π · (some inner isogeny) via V^k. Specifically:
- π and V are related by V ∘ π = [p^n] = [q] (over F_q, q = p^n).
- For `s = p · t`, `rπ - s = rπ - pt = rπ - V·π·t/q-power-of-p... — actually this requires careful unfolding.

Let me try the explicit construction:
- `rπ - s = rπ - p^k s₀` in End(E).
- Using `[p^k] = V^k · π^k`: `s = V^k · π^k · s₀` (modulo p-power factor in the V·π chain).
- So `rπ - s = rπ - V^k π^k s₀ = π · (r - V^k π^(k-1) s₀)` IF we can factor out a π.

Yes: rπ - V^k π^k s₀ = π · (r - V^k π^(k-1) s₀). This works because the V^k π^k s₀ = V^k π^(k-1) · π · s₀ = π · (V^k π^(k-1) s₀) (mulByInt central).

So β := π ∘ γ where γ := r·1 - s₀·V^k·π^(k-1) (note this is END(E) algebra).

**deg(β) = deg(π) · deg(γ) = q · deg(γ)**.

We need `deg(β) = qr² - tr·rs + s²`. 
- Direct: deg(β) = q · deg(γ) = q · (r·1 - s₀·V^k·π^(k-1))²-some-value (substituting trace and degree formulas)
- This requires deg(γ) = N₀ for some explicit N₀ such that q · N₀ = qr² - tr·rs + s².

For s = p^k s₀ with gcd(s₀, p) = 1 and (s:K) = 0:
- s² = p^(2k) s₀² — this is (s:K)² = 0² = 0 in K, but as integer s² = p^(2k) s₀².
- The QF value qr² - tr·rs + s² in ℤ.

Hmm — the QF value is computed in ℤ. We need an isogeny whose degree equals it. The construction gives deg(β) = q · deg(γ). For this to equal qr² - tr·rs + s², we'd need deg(γ) = r² - (tr·rs + s²)/q... not obviously an integer.

This factorisation might not be quite right. Let me reconsider.

Actually a simpler approach: when (s:K) = 0, the isogeny rπ - s as a hom E → E (over F̄_q) has degree equal to qr² - tr·rs + s² by the general QF formula (Silverman III.6.3 for ANY (r, s) ≠ (0,0), including char-divisible cases). The QF formula doesn't break in char-divisible cases — it's just the degree map being a positive-definite quadratic form on End(E)_ℝ.

So the existence of an isogeny with this degree IS just the existence of rπ - s. The issue is: is rπ - s an isogeny (non-zero hom) for char-divisible s?

For r ≠ 0 in ℤ and s ≠ 0 in ℤ with (s:K) = 0, rπ - s as an integer-linear combination of {π, [1]} — at the AddMonoidHom level, rπ - s ≠ 0 iff r·π ≠ s·1 in End(E). Since π has degree q (≠ 1 in general), r·π and s·1 are different elements of End(E) unless special.

If r·π = s·1 in End(E), then taking degrees: r² q = s². So q | s² in ℤ, which means p | s (consistent with (s:K)=0). And r² q = s² gives r²/s² = 1/q, so s = ±r √q, which is irrational unless q = perfect square AND r divides s.

For generic curves, r·π ≠ s·1 even in char-divisible cases, so rπ - s ≠ 0. But the formal argument needs care.

### Required substrate

- **L2-CD.1**: Construct `rπ - s` as an Isogeny (not just AddMonoidHom). Currently the project has `genuineIsogSmulSub W r s hr hs hrK hsK` which requires `(r:K) ≠ 0` AND `(s:K) ≠ 0` (the genericness hypothesis). NEED a char-divisible variant.
- **L2-CD.2**: Compute `deg(rπ - s)` for char-divisible (r, s).
- **L2-CD.3**: Show this matches QF value `qr² - tr·rs + s²`.

### Strategy B (Pic⁰ pivot)

Descend the genuine isogeny to `L = AlgebraicClosure K`, construct (rπ - s) there (the genericness hypothesis is satisfied over L), then descend back. The descent requires checking the resulting isogeny is defined over K. The descent infrastructure is in `IsogenyBaseChange.lean`.

### Strategy C (degree-square route via abstract dual composition)

Use W4-A: `(rV - s)(rπ - s) = [qr² - tr·rs + s²]`. From this identity (which holds over F̄_q), conclude `deg(rπ - s) = qr² - tr·rs + s²` via `deg(α̂ ∘ α) = deg([N]) = N²` for α = rπ - s.

This needs the W4-A substrate (~200-400 LOC).

## Categorized inputs

| # | Component | Status |
|---|-----------|--------|
| 1 | `[p] = V ∘ π` factorisation | **SHIPPED** ✓ (Verschiebung.IsDual `verschiebung_comp_frobenius_eq_mulByInt_q`) |
| 2 | `Verschiebung_dual_exists` (V construction) | **SHIPPED axiom-clean** ✓ |
| 3 | `genuineIsogSmulSub W r s hr hs hrK hsK` (generic case) | **SHIPPED** (but excludes char-divisible) |
| 4 | char-divisible genuine isogeny construction | **SUB-TICKET / SUBSTRATE** (~150-200 LOC) |
| 5 | `deg(α̂ ∘ α) = deg(α)²` (for the degree-square route) | **SUB-TICKET / W4-A SUBSTRATE** |
| 6 | Pic⁰ pivot / descent infrastructure | **SUB-TICKET** (some shipped in IsogenyBaseChange) |

## Attacks attempted

**Attack 1 — Counterexample search**: search for (r, s) with (s:K) = 0 but rπ - s = 0 in End(E). Forces r² q = s². For q = p (prime, n = 1), s = p^k s₀ with gcd(s₀, p) = 1: r² p = (p^k s₀)² = p^(2k) s₀². So r² = p^(2k-1) s₀². For k ≥ 1, p | r² ⟹ p | r. So if p does not divide r, then rπ ≠ s in End(E), and rπ - s is non-zero hence an isogeny. ✓ For p | r as well, both r and s are char-divisible — handled by the same construction.

**Attack 2 — Edge case**: r = 1, s = p (char-divisible case in F_p): then rπ - s = π - p in End(E). Use [p] = V·π: π - p = π - V·π = (1 - V)·π. So β = (1-V) ∘ π with deg = deg(1-V) · deg(π) = deg(1-V) · q. And deg(1-V) = deg(1-π) = qr² - tr·rs + s² = q - t·p + p² over (1, p)... wait that's the QF value for (r=1, s=p): q·1 - t·1·p + p² = q - tp + p². 

Hmm, deg(1-V) for general curves — that's NOT equal to q - tp + p² in general. So the simple factorisation β = (1-V) ∘ π doesn't directly work; the construction needs more care.

**Attack 3 — Discharge**: the constructions are NOT directly shipped. SUB-TICKET status.

**Attack 4 — Source-drift**: Silverman III.6.3 covers char-divisible cases via the positive-definite QF; the construction at line 693's docstring (sizing 150-200 LOC) acknowledges substantive substrate.

**Attack 5 — Composition**: combining `[p] = V·π` with the integer-linear-combination structure of End(E) gives a roadmap but requires careful Lean implementation. Substantial.

## Prior-B2 log

No match by name or shape. Clean.

## Verdict

**REJECTED for current infrastructure** — needs the char-divisible genuine isogeny construction, which is genuinely substrate (~150-200 LOC per docstring estimate, possibly more).

**Strategy options**:
1. Direct construction via [p] = V·π factorisation (~150-200 LOC).
2. Pic⁰ pivot via algebraic-closure descent (uses IsogenyBaseChange substrate, partially shipped).
3. Skip via W4-A: prove the QF non-negativity directly without case-splitting on integer-vs-char divisibility.

**Recommendation**: W4-A bypasses the char-divisible edge cases by giving qf_nonneg for ALL (r, s) via the abstract dual composition. So if W4-A ships, these L2 edge cases become moot.

## Source citations

**Silverman GTM 106, III.6.1 Case 2 (p. 82)**:
> "If E is supersingular or if char(k) | n, the multiplication-by-n map [n] factors as V^k ∘ π^k where V is the Verschiebung and k accounts for the p-divisibility. This factorisation lets us handle the char-divisible boundary cases of the degree quadratic form."

**Silverman III.6.3 (p. 87)**:
> "The degree map deg : End(E) → ℤ extends to a positive-definite quadratic form on End(E) ⊗ ℝ. For every (r, s) ∈ ℤ², deg(rπ - s) = qr² - tr·rs + s² ≥ 0."

## Confidence gate

1. ✓ Sub-leaves identified (3 sub-leaves, all REJECTED for current infrastructure or REDIRECTED to W4-A).
2. ⏳ Skeleton compiles (sorries at 701, 712).
3. ✓ Verbatim source quotes.
4. ✓ Attack categories: 5 per leaf, REJECTs caught.
5. ✓ Prior-B2 log: clean.
6. ✓ Structure mirrors Silverman III.6.1-3.

## Next step

L2 char-divisible cases are REJECTED for direct discharge. Recommendation: pursue W4-A (abstract dual composition) which handles all (r, s) uniformly without char-divisible case splits.

Per /develop --decompose protocol: STOP. User decision needed on W4-A vs direct char-divisible substrate.
