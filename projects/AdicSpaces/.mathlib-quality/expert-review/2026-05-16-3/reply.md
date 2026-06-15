# Reviewer reply — ChatGPT Pro (round 22) — 2026-05-16

## Assessment

For a **sorry-free final theorem**, the correct path is **(a)**: build the no-`hArch` compactness infrastructure, at least locally enough to prove compactness of rational opens / rational halfspaces.

For engineering progress, you may use a temporary private TODO lemma, but it should **state the no-`hArch` compactness conclusion**, not add `hArch` to the public or private theorem shape. In Lean, a private lemma with an `hArch` hypothesis cannot be used to prove a no-`hArch` theorem unless you can supply `hArch`; privacy does not hide hypotheses. So the legitimate temporary compromise is:

```lean
private theorem isCompact_rationalOpen_noHArch_TODO ... : IsCompact ... := by
  sorry
```

not:

```lean
private theorem isCompact_rationalOpen_with_hArch ... (hArch : ...) : IsCompact ...
```

used inside a no-`hArch` theorem.

`hArch` is an artifact of the current Boolean-product proof of compactness, not a genuine hypothesis in Wedhorn 8.28(b). Higher-rank valuations are part of the adic spectrum, and Tate acyclicity is not restricted to rank-one or multiplicatively archimedean value groups.

## Mathematical idea

### Q1. Recommended path

Do **(a)** for the eventual proof. For short-term proof development, use the private no-`hArch` TODO lemma as scaffolding, but do not propagate `hArch`.

The current Boolean-product method fails for exactly the reason you found: continuity/cofinality is not a closed finitary condition in the naive topology on `{0,1}^{A×A}`. Wedhorn avoids this by changing the ambient spectral space to `Spv(A,I)`. So the compactness theorem you need is not a small patch to the old Boolean closed-image proof; it is the Wedhorn `Spv(A,I)` compactness/spectral-space construction, or a local version of it.

A useful compromise is:

```lean
-- local, no hArch, eventually proved by Spv(A,I)
theorem isCompact_rationalOpen_inter_vle_noHArch
    (L : RationalLocData A) (g h : A) :
    IsCompact {v ∈ rationalOpen L.T L.s | v.vle g h}
```

Use this as the P3 input while building `Spv(A,I)` separately.

### Q2. The microbial case in Wedhorn 7.10

The `cΓ_v = Γ_v` case does **not** say the whole value group is multiplicatively archimedean. It gives a way to prove the needed cofinality of `v(a)` for `a ∈ I` using boundedness in the ring.

The argument is:

Given `a ∈ I` and `γ ∈ Γ_v`, choose `t ∈ A` such that

```text
v(t) ≠ 0
v(t)⁻¹ ≤ γ.
```

This uses `cΓ_v = Γ_v`: the characteristic subgroup is all of the value group, so values of elements of `A` are sufficiently cofinal to find such a `t`.

Because `{t}` is bounded in the f-adic ring, and `I` is an ideal of definition, there exists `n` such that

```text
t * a^n ∈ I.
```

The hypothesis `v(x) < 1` for all `x ∈ I` gives

```text
v(t * a^n) < 1.
```

Thus

```text
v(a)^n < v(t)⁻¹ ≤ γ.
```

So powers of `v(a)` are cofinal. This is not the same as a global `MulArchimedean` assumption. The element `t` is chosen depending on `γ`.

### Q3. Project-specific cofinality criterion

Yes: a criterion like

```lean
Valuation.isContinuous_of_ideal_pow_lt
```

is the right way to avoid `exists_pow_lt_zero`.

For `v ∈ Spv(A,I·A)` and `v(a) < 1` for all `a ∈ I`, prove:

```text
∀ γ > 0, ∃ n, ∀ x ∈ I^n, v(x) < γ.
```

Using finite generation of `I`, choose generators `x₁,…,x_r`.

For each generator `x_i`, Wedhorn 7.10 gives cofinality:

```text
∀ γ > 0, ∃ N_i, v(x_i)^{N_i} < γ.
```

Let `N` be large enough, for example `N = r * max_i N_i`. Every degree-`N` monomial in the `x_i` contains some `x_i` with exponent at least `N_i`. Since the other generators lie in `I ⊆ A₀ ⊆ A⁺`, their values are `≤ 1`; hence the monomial has value `< γ`. A general element of `I^N` is an `A₀`-linear combination of such monomials, and coefficients from `A₀ ⊆ A⁺` have value `≤ 1`, so the nonarchimedean inequality gives `< γ`.

This is the algebraic heart of the continuity proof and avoids a rank-one argument.

### Q4. Mathlib / spectral structure route

Do not start by upstreaming `PrespectralSpace (Spv A)` or `QuasiSober (Spv A)`. This is very project-specific and depends on how your `Spv`, `Spa`, valuations, and rational-open basis are encoded.

Instead, build the Wedhorn-specific object in the project first:

1. Define the cofinality condition / `Spv(A,I)` predicate, using Wedhorn Lemma 7.4's equivalent characterization:

   ```text
   v ∈ Spv(A,I) iff
     (∀ a ∈ I, v(a) is cofinal in Γ_v) ∨ cΓ_v = Γ_v.
   ```

2. Define the refined topology on `Spv(A,I)` with basis:

   ```text
   Spv(A,I)(T/s)
   ```

   for finite `T` with `√I ⊆ √(T·A)`.

3. Prove basic rational subsets are quasi-compact/open constructible in this topology.

4. Prove continuity criterion:

   ```text
   Cont(A) = {v ∈ Spv(A,I) | ∀ a ∈ I, v(a) < 1}.
   ```

5. Prove Spa is pro-constructible / spectral / compact inside `Spv(A,I)`.

6. Derive the lemma actually needed:

   ```lean
   isCompact_rationalOpen_inter_vle_noHArch
   ```

Only after this is stable should you consider extracting general spectral-space instances for Mathlib.

## Lean-facing next steps

The shortest sound path is:

1. Add a private TODO theorem with the **no-`hArch` conclusion** to unblock P3 work:

   ```lean
   private theorem isCompact_rationalOpen_inter_vle_noHArch_TODO ... :
       IsCompact {v ∈ rationalOpen L.T L.s | v.vle g h} := by
     sorry
   ```

2. Continue the domination lemma and P3 using that theorem.

3. In parallel, create a separate `SpvAI` / `SpaCompactNoHArch` track:

   * `CofinalValue` definition,
   * `SpvAI` predicate/type,
   * rational basis,
   * Wedhorn 7.10 continuity criterion,
   * compactness of rational opens.

4. Replace the TODO lemma with the real no-`hArch` theorem when that track is complete.

Do **not** thread `hArch` through P3/P4/P8 or final Tate acyclicity.

## Risks or missing facts

The main risk is believing a private `hArch` theorem can be used without propagating `hArch`. It cannot, unless it is a `sorry`/axiom proving a no-`hArch` statement.

The second risk is attempting to repair the Boolean-product closed-image proof directly. The continuity condition is not closed in that topology; Wedhorn's refined `Spv(A,I)` is the right fix.

The third risk is trying to upstream spectral instances too early. The project needs a local Wedhorn object first.

## Manager message to worker

Use the temporary private TODO compromise only in this form:

```lean
private theorem isCompact_rationalOpen_inter_vle_noHArch_TODO ... :
  IsCompact {v ∈ rationalOpen L.T L.s | v.vle g h} := by
  sorry
```

Do **not** add `hArch` as a hypothesis, even privately, if the result is meant to prove a no-`hArch` theorem. Lean will not hide that hypothesis.

The real proof track is Wedhorn's `Spv(A,I)` construction. Build it separately:

```text
cofinality condition → Spv(A,I) → rational basis → 7.10 continuity criterion
→ Spa compactness/rational-open compactness without hArch.
```

For the continuity part, use the project's `Valuation.isContinuous_of_ideal_pow_lt`; discharge it via Wedhorn's microbial/non-microbial argument and finite generation of `I`, not via `MulArchimedean`.

For now, unblock P3 with a no-`hArch` TODO lemma, continue the domination construction, and schedule the `Spv(A,I)` compactness track as the replacement proof.
