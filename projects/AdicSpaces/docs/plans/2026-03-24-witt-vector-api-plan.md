# Witt Vector API Development Plan

> **For agentic workers:** Use superpowers:executing-plans to implement.

**Goal:** Build reusable Witt vector API, then fill the 3 remaining sorry's.

**Design principle:** Build general lemmas first, then specialize. Each lemma should be independently useful beyond our immediate goals.

---

## The Three Sorry's (recap)

1. **`isPrecomplete_pIdeal` SModEq** (PerfectoidRing.lean:441): `p^n | (f n - L)` in A°
2. **`hxi_exists`** (Tilting.lean:399): `∃ xi ∈ ker(θ), xi ≠ 0`
3. **`hxi_div`** (Tilting.lean:418): `∀ x ∈ ker(θ), ξ | x`

All three need the same core technique: **constructing elements via p-adic approximation in I-adically complete rings**.

---

## API Development Plan

### Layer 1: General Adic Completion API (new file `AdicConvergence.lean`)

These are general results about I-adically complete rings, not specific to Witt vectors.

#### 1a. `IsAdicComplete.exists_limit` — extract limit from Cauchy

Given `[IsAdicComplete I R]` and `f : ℕ → R` Cauchy w.r.t. I, produce L : R.

```lean
/-- In an I-adically complete module, every I-adic Cauchy sequence has a limit. -/
theorem IsAdicComplete.exists_limit [IsAdicComplete I M] {f : ℕ → M}
    (hf : ∀ {m n}, m ≤ n → f m ≡ f n [SMOD I ^ m • ⊤]) :
    ∃ L : M, ∀ n, f n ≡ L [SMOD I ^ n • ⊤]
```

This is just `IsPrecomplete.prec` packaged nicely. Useful everywhere.

#### 1b. `IsAdicComplete.series_convergent` — infinite I-adic series converge

```lean
/-- In an I-adically complete ring, a series Σ aₙ where aₙ ∈ I^n converges. -/
theorem IsAdicComplete.series_convergent [IsAdicComplete I R] {a : ℕ → R}
    (ha : ∀ n, a n ∈ I ^ n • (⊤ : Submodule R R)) :
    ∃ S : R, ∀ n, (Finset.sum (Finset.range n) a) ≡ S [SMOD I ^ n • ⊤]
```

This is the key for constructing p-adic limits. Used by all three sorry's.

#### 1c. `IsAdicComplete.smul_top_eq_ideal` — for rings, I^n • ⊤ = I^n

```lean
/-- For a ring R viewed as a module over itself, I^n • ⊤ = I^n (as submodules). -/
theorem Ideal.smul_top_eq (I : Ideal R) (n : ℕ) :
    (I ^ n • ⊤ : Submodule R R) = (I ^ n).restrictScalars R
```

This clarifies the relationship between `SModEq` and ideal membership. Very reusable.

### Layer 2: Witt Vector Primitive Elements (add to `Tilting.lean` or new file)

#### 2a. `WittVector.IsPrimitive` — Definition 6.2.9

```lean
/-- An element ξ ∈ W(R) is **primitive of degree 1** if it has the form
ξ = p + [ϖ]·α where ϖ is a pseudo-uniformizer of R and α ∈ W(R).
(Scholze-Weinstein, Berkeley Lectures, Definition 6.2.9) -/
def WittVector.IsPrimitive (ξ : WittVector p R) (ϖ : R) : Prop :=
  ∃ α : WittVector p R, ξ = (p : WittVector p R) + teichmuller p ϖ * α
```

#### 2b. `WittVector.IsPrimitive.isNonzerodivisor` — Lemma 6.2.10

```lean
/-- A primitive element of degree 1 is a nonzerodivisor.
Proof: if ξ·x = 0, then modulo [ϖ], p·x ≡ 0. By p-torsion-freeness,
all coefficients of x are divisible by ϖ. Divide and induct.
(Scholze-Weinstein, Berkeley Lectures, Lemma 6.2.10) -/
theorem WittVector.IsPrimitive.isNonzerodivisor [CharP R p] [PerfectRing R p]
    [IsDomain R] {ξ : WittVector p R} {ϖ : R} (hξ : ξ.IsPrimitive ϖ)
    (hϖ : ϖ ≠ 0) : IsNonzerodivisor ξ
```

#### 2c. `WittVector.quotient_primitive_mod_teichmuller` — Key computation

```lean
/-- W(R)/(ξ, [ϖ]) = W(R)/(p, [ϖ]) = R/ϖ when ξ = p + [ϖ]α.
This is the key computation in the proof that ker(θ) is principal.
(Scholze-Weinstein, Berkeley Lectures, p.47) -/
theorem WittVector.quotient_primitive_eq_quotient_p ...
```

### Layer 3: The untilt-Teichmüller connection (add to `Tilting.lean`)

#### 3a. `PreTilt.untilt_congr_coeff_mod_p` — untilt ≡ any lift of coeff_0 (mod p)

```lean
/-- The untilt of x ∈ PreTilt O p is congruent to any lift of coeff_0(x) modulo p.
This is a reformulation of `mk_untilt_eq_coeff_zero`. -/
theorem PreTilt.untilt_sub_lift_mem_span_p [IsAdicComplete (Ideal.span {p}) O]
    (x : PreTilt O p) (y : O) (hy : Ideal.Quotient.mk _ y = PreTilt.coeff 0 x) :
    x.untilt - y ∈ Ideal.span {(p : O)}
```

#### 3b. `theta_teichmuller_sub_cast_mem_ker` — θ([a]) - a.untilt = 0

Already available as `fontaineTheta_teichmuller`. But worth having a corollary:

```lean
/-- For any a ∈ PreTilt O p, [a] - (θ-preimage of a.untilt) ∈ ker(θ). -/
```

### Layer 4: The construction (fill sorry's)

#### 4a. Construct ξ (fills `hxi_exists`)

Using layers 1-3:
1. Get ϖ, c with p = c·ϖ^p
2. Set α = c·ϖ^{p-1} ∈ A° (so ϖ·α = p)
3. Lift ϖ̄, ᾱ to ϖ♭, β♭ ∈ PreTilt via `coeff_surjective`
4. f♭ = ϖ♭ · β♭ (so f♭.untilt ≡ p mod p·ϖ♭.untilt)
5. s = (p - f♭.untilt)/(p·ϖ♭.untilt) ∈ A°
6. w ∈ W(PreTilt) with θ(w) = s (by surjectivity)
7. ξ = p - [f♭] - [ϖ♭]·p·w

#### 4b. Prove divisibility (fills `hxi_div`)

Using layers 1-2:
1. Given x ∈ ker(θ), write x = ξ·q₀ + p·r₀ (using W(k)/(p) ≅ k structure)
2. Show r₀ ∈ ker(θ) (from θ(x) = θ(ξ) = 0)
3. Iterate: rₙ = ξ·q_{n+1} + p·r_{n+1}
4. x = ξ·(q₀ + p·q₁ + p²·q₂ + ...) converges by `series_convergent` (layer 1b)

#### 4c. Prove SModEq (fills `isPrecomplete_pIdeal`)

Using layer 1:
The limit L exists topologically. Need `f n - L ∈ p^n · A°`. This follows from:
- `f m - f n ∈ p^n · A°` for m ≥ n (Cauchy condition)
- `f m → L` topologically
- `p^n · A°` is closed in A° (needs layer 1c + topology)

---

## Execution Order

1. **Layer 1a** (5 min): Package `IsPrecomplete.prec` as `exists_limit`
2. **Layer 1b** (30 min): Prove `series_convergent` from `exists_limit`
3. **Layer 3a** (15 min): Prove `untilt_sub_lift_mem_span_p`
4. **Layer 4a** (60 min): Construct ξ (fills `hxi_exists`)
5. **Layer 2a-b** (45 min): Define `IsPrimitive`, prove nonzerodivisor
6. **Layer 4b** (60 min): Prove divisibility (fills `hxi_div`)
7. **Layer 4c** (30 min): Prove SModEq (fills `isPrecomplete_pIdeal`)

**Total: ~4 hours of focused work**

---

## File Organization

- `Adic spaces/AdicConvergence.lean` (NEW): Layer 1 (general adic series API)
- `Adic spaces/WittVectorPrimitive.lean` (NEW): Layer 2 (primitive elements)
- `Adic spaces/Tilting.lean`: Layers 3-4 (specific construction + sorry fills)
- `Adic spaces/PerfectoidRing.lean`: Layer 4c (isPrecomplete sorry fill)
