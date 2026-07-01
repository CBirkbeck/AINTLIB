# Development Plan: Shimura Prop 3.34 — Gamma0MapUnits Preservation

**Date**: 2026-04-17
**Goal**: Unblock `heckeRingHomCharSpace N k χ` for arbitrary χ by proving that Γ₀(N)'s nebentypus character is preserved under conjugation by `rep D ∈ Δ₀(N)`.

## Mathematical statement

For `g ∈ Δ₀(N)` and `h ∈ Γ₀(N)` such that `g⁻¹ · h · g ∈ (Gamma0_pair N).H` (= `Γ₀(N).map (mapGL ℚ)`), we have:
```
Gamma0MapUnits (g⁻¹ · h · g) = Gamma0MapUnits h
```

More precisely, the Lean statement:
```lean
theorem Gamma0MapUnits_preserved_under_conjugation
    {N : ℕ} [NeZero N] (g : (Gamma0_pair N).Δ) (h : ↥(Gamma0 N))
    (h_conj : ((g : GL _ ℚ)⁻¹ * (mapGL ℚ (h : SL(2,ℤ))) * (g : GL _ ℚ)) ∈
      (Gamma0 N).map (mapGL ℚ))
    (h' : ↥(Gamma0 N))
    (h'_spec : (mapGL ℚ (h' : SL(2,ℤ)) : GL _ ℚ) =
      (g : GL _ ℚ)⁻¹ * (mapGL ℚ (h : SL(2,ℤ))) * (g : GL _ ℚ)) :
    Gamma0MapUnits h' = Gamma0MapUnits h
```

(Exact form to be finalized against existing types.)

## Why this is true (Shimura's approach)

For `g = [[a, b], [Nc, d]] ∈ Δ₀(N)` with `gcd(a, N) = 1`:
- Working mod N: `g̃ = [[a, b], [0, d]]` where `a` is a unit mod N.
- For `h = [[α, β], [Nγ, δ]] ∈ Γ₀(N)` with `αδ ≡ 1 (mod N)`:
- Direct matrix computation shows `(g⁻¹ h g)₁₁ ≡ δ (mod N)` **when the conjugate is integer**.

Key technical fact: `(g⁻¹ h g)₁₁ · det(g) = N·ab·γ + ad·δ - N·b·c·α - N·c·d·β` (rationals).
Mod N: this reduces to `ad·δ`. So `(g⁻¹ h g)₁₁ · det(g) ≡ ad·δ (mod N)`.

If `det(g)` is invertible mod N — which happens iff `gcd(det g, N) = 1` iff `gcd(d, N) = 1` given `gcd(a, N) = 1` — then `(g⁻¹ h g)₁₁ ≡ δ (mod N)`, so Gamma0MapUnits is preserved.

**CAVEAT**: When `gcd(d, N) > 1` (bad-prime case), the argument above doesn't work directly. However, if the conjugate IS in Γ₀(N), it has det 1, so `(g⁻¹ h g)₁₁ · 1 = δ (mod N)` via a different angle: use the fact that `det(g⁻¹ h g) = det(h) = 1`, combined with `(g⁻¹hg)_{1,0} ≡ 0 (mod N)` (Γ₀(N) condition), to back out the (1,1) entry.

Actually the cleanest argument: `g⁻¹ h g ∈ Γ₀(N)` means its (1,1) entry is `δ'` with `α' δ' ≡ 1 (mod N)` (since det = 1 and lower-left ≡ 0). We just need `α' ≡ α (mod N)`.

Parallel computation for (0,0) entry: `(g⁻¹ h g)_{0,0} · det(g) ≡ ad·α (mod N)`. So the same logic applies to top-left.

## Strategy

### Two-case approach

**Good-prime case** (`gcd(det g, N) = 1`): direct mod-N matrix computation. ~100 LOC.

**Bad-prime case** (`gcd(det g, N) > 1`): use that `g⁻¹ h g ∈ Γ₀(N)` forces `det(g⁻¹ h g) = 1`, so the (0,0) and (1,1) entries are multiplicatively inverse mod N. Combined with lower-left ≡ 0, the (0,0) and (1,1) characters are determined by each other. Show consistency via a separate mod-N computation.

Alternative: bypass the bad-prime case by restricting to coprime-det D's (which covers the Hecke operators we care about: `T_p` for `gcd(p, N) = 1`).

### Unified proof via `Matrix.conjugation_fin_two_entry_mod`

Best: a single lemma about 2x2 matrix conjugation entries mod N, parameterized by the appropriate conditions.

## Files structure

- `LeanModularForms/HeckeRIngs/GL2/Prop334.lean` (new) — the preservation theorem + helpers
- Then update `LeanModularForms/HeckeRIngs/GL2/HeckeRingHomCharSpace_General.lean` or create `HeckeRingHomCharSpace_ChiNonzero.lean` to use it.

## Mathlib inventory

| Concept | Mathlib Status | Our Action |
|---|---|---|
| `Gamma0MapUnits` | Ours (GL2/Gamma1Pair.lean:252) | USE directly |
| `(ZMod N)ˣ` arithmetic | `Mathlib.Data.ZMod.Basic` | USE directly |
| 2x2 matrix inversion formulas | `Mathlib.LinearAlgebra.Matrix.Adjugate` | USE via `Matrix.adjugate` / `fin_two` lemmas |
| Integer conjugation | Not in mathlib as a lemma | DEFINE — this is the core contribution |

## Dependency graph

```
P334-A: Precise statement + matrix form   → P334-B: Good-prime case proof
                                          → P334-C: Bad-prime case proof (or skip)
P334-A → P334-D: Full theorem combining B + C
P334-D → P334-E: Lift to heckeSlash_gen preservation
P334-E → P334-F: Build heckeRingHomCharSpace for arbitrary χ
P334-F → P334-G: Refactor heckeT_p_all_comm_distinct via char decomp + ring hom
```

## Budget

Estimated: 600-1000 LOC across 3-5 files. Likely 2-3 sessions.

## References

- Shimura, *Introduction to the Arithmetic Theory of Automorphic Functions*, §3.4.
- Existing: `heckeSlash_gen_slash_invariant` in `HeckeActionGeneral.lean:462-499` — the existing proof template we're generalizing.
- Existing: `heckeT_p_comm_diamondOp` in `HeckeT_p.lean:1194` — the T_p-specific instance we're extending.
