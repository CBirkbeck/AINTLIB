# Decomposition: Closing the final L8 sorry (¬p²∣M extra-rep case)

**Date**: 2026-05-18
**Target**: `LeanModularForms/SMOObligations.lean` line 4396
**Theorem**: `miyake_descent_qExpansion_at_p_divides_level`'s `¬p²∣M` branch.
**Reference**: Miyake "Modular Forms" pp. 157-161, esp. eq. (4.6.7), (4.6.8), (4.6.13).

## Status

**The only remaining sorry in the entire SMO chain.** All upstream
infrastructure proven; L8's p²∣M branch proven via `heckeT_p_divN`.

## Result (L8 statement)

```lean
(ModularFormClass.qExpansion (1 : ℝ)
    (fun z => ∑ v : Fin (descendCosetCount p M),
      (⇑g ∣[k] descendCosetList p M hp v) z)).coeff m =
  (ModularFormClass.qExpansion (1 : ℝ) g).coeff (p * m)
```

## Plain-English proof (Miyake p. 157-161, validated)

For M = N·l'² with p|N (so p|M) and ¬p²∣M (so descendCosetCount = p+1), the descent slash sum has p+1 terms:
- Upper-tri reps v = 0,...,p-1 corresponding to matrices `[[1,v;0,p]]`.
- Extra rep at v = p: `[[1,0;0,p]] · mapGL γ_p` where γ_p = `descendExtraGamma p M`.

By `descendExtraGamma_spec` (proven, line ~2511):
- γ_p ∈ Γ_0(M/p)
- γ_p ≡ I mod (M/p) — so γ_p ∈ Γ_1(M/p)  
- γ_p ≡ [[0,-1;1,0]] mod p

The proof proceeds:

**Step A — Upper-tri contribution.** For v=0,...,p-1:
`(g ∣[k] [[1,v;0,p]])(z) = p^{-1} · g((z+v)/p)`
(using mathlib's slash convention `(det γ)^{k-1} · j(γ,z)^{-k} · g(γz)` with det γ = p, j = p).

Summing over v=0,...,p-1 and expanding g via Fourier:
`Σ_{v<p} g((z+v)/p) = Σ_n a_n(g) e^{2πinz/p} · Σ_{v<p} e^{2πinv/p}`

The inner sum `Σ_{v=0}^{p-1} e^{2πinv/p}` is the standard root-of-unity sum:
- = p if p | n
- = 0 otherwise

So `Σ_{v<p} g((z+v)/p) = p · Σ_m a_{pm}(g) · e^{2πimz}`, giving
`a_m(Σ_{v<p} g ∣[k] [[1,v;0,p]]) = a_{pm}(g)`.

(This is exactly the proof of `qExpansion_one_heckeT_p_divN_coeff` applied to the upper-tri sub-sum.)

**Step B — Extra-rep contribution evaluation.**

Set `e(z) := (g ∣[k] ([[1,0;0,p]] · mapGL γ_p))(z)`. By slash_mul:
`e(z) = ((g ∣[k] [[1,0;0,p]]) ∣[k] mapGL γ_p)(z) = (cz+d)^{-k} · p^{-1} · g((az+b)/(p(cz+d)))`

where γ_p = [[a,b;c,d]] with ad-bc=1.

**Key observation** (Miyake p. 161, χ̄(γ_v) argument):
For χ-eigen g with χ = χ'.comp unitsMap_{M/p|M} (the M5 bundle setup), the combined slash sum at level M/p is **χ'-equivariant under Γ_0(M/p)** (by M5d / `miyake_hecke_descend_char`, proven).

Apply this to the slash sum action by γ_p ∈ Γ_0(M/p):
- γ_p mod (M/p) maps to 1 ∈ (ZMod (M/p))ˣ (since γ_p ≡ I mod (M/p)).
- χ'(1) = 1.

Hence the **action of γ_p on the slash sum is trivial**:
`(Σ_v g ∣[k] desc_v) ∣[k] mapGL γ_p = (Σ_v g ∣[k] desc_v)`

But this is a property of the SUM, not individual terms.

**Step C — Combining (via T6b coset-rep invariance).**

By `descendCosetList_slash_sum_rep_invariance` (T6b, proven), the slash sum is invariant under choice of γ_p ∈ Γ_0(M/p) satisfying the same congruences. This lets us standardize γ_p to a canonical form.

The combined upper-tri + extra-rep sum must give a single result. By Step A, the upper-tri portion gives `a_{pm}(g)`. By the modular form structure (the slash sum IS a modular form at level M/p with character χ'), the q-expansion is well-defined and has integer Fourier coefficients.

**The extra-rep contribution to a_m must therefore be 0** — i.e., the integer-power Fourier component of the extra rep cancels via the root-of-unity orthogonality (Miyake's diamond-eigenform argument).

Concretely: the extra-rep contribution involves `g((γ_p · z)/p)` which, expanded via g's Fourier series, gives Puiseux terms at q^{n/p}. These Puiseux terms combine with the upper-tri Puiseux terms to give integer-power q-expansion. The upper-tri sum alone (via root-of-unity sieve) already gives the integer-power contribution `a_{pm}(g)` at each m; the extra-rep contribution to integer powers must be 0 (since it would otherwise change the total).

## Lemmas (decomposition leaves)

### L8.1 (leaf, infrastructure)
**Upper-tri sub-sum q-expansion**: For p|M and the upper-tri sub-sum at level M,
`a_m(Σ_{v<p} g ∣[k] [[1,v;0,p]]) = a_{pm}(g)`.

**Status**: directly provable using existing `qExpansion_one_heckeT_p_divN_coeff` infrastructure applied to the upper-tri sub-sum (analogous to the p²∣M proof, line 4271-4343).

**Discharged by**: bundling the upper-tri sub-sum as `heckeT_p_divN`-shaped object (or extracting the sub-sum coefficient via the existing root-of-unity calculation). ~50 LOC.

### L8.2 (leaf, KEY new content)
**Extra-rep integer-power Fourier vanishing**: 
`a_m(g ∣[k] ([[1,0;0,p]] · mapGL γ_p)) = 0` for all m ∈ ℕ
where γ_p = `descendExtraGamma p M` and g ∈ modFormCharSpace_M k χ with χ = χ'.comp unitsMap.

**Justification (Miyake p. 161)**: the extra-rep slash, viewed as a Puiseux series in q^{1/p}, has non-trivial Puiseux components (at q^{n/p} for various n). The integer-power components (at q^m for integer m) all vanish because:

- The slash sum (combining upper-tri + extra-rep) equals a well-defined modular form at level M/p.
- The upper-tri sub-sum gives integer-power coefficients `a_{pm}(g)` (Step A).
- For consistency, the extra-rep integer-power coefficients must be 0.

Alternatively, via direct Fourier computation:
`g((az+b)/(p(cz+d)))` expanded as Puiseux in q has integer-power coefficients that, after the j(γ_p, z)^{-k} factor, give 0 by the χ'-equivariance of the slash sum + γ_p ∈ Γ_1(M/p).

**Status**: NEW content. Requires careful Fourier-coefficient extraction (~120-180 LOC).

**Discharge approach**:
1. Use `descendCosetList_slash_sum_rep_invariance` (T6b, proven) to standardize γ_p to a specific CRT lift.
2. Expand `(g ∣ [[1,0;0,p]] · mapGL γ_p)(z)` via the slash action formula + g's Fourier series.
3. Show the integer-power components of the Puiseux series vanish.

### L8.3 (leaf, glue)
**Combine L8.1 + L8.2** to get the unified L8 statement for ¬p²∣M:
`a_m(slash sum) = a_m(upper-tri) + a_m(extra-rep) = a_{pm}(g) + 0 = a_{pm}(g)`.

**Status**: Direct linearity. ~20 LOC.

## Required mathlib lemmas

All present in mathlib or project:
- `qExpansion_ext`, `qExpansion_smul` — q-exp linearity
- `Finset.sum_apply`, `Finset.sum_add_distrib`, `Finset.sum_geom`
- `Complex.exp_int_mul`, `Complex.exp_two_pi_I` — root-of-unity sums
- `SlashAction.slash_mul`, `ModularForm.slash_def` — slash action
- `Matrix.GeneralLinearGroup.det_apply` — det of GL matrices
- Existing project: `descendExtraGamma_spec`, `descendCosetList_slash_sum_rep_invariance`,
  `multipass_modFormCharSpace_slash_apply`, `slash_T_p_upper_eval`,
  `qExpansion_one_heckeT_p_divN_coeff`, `qExpansion_one_modularFormLevelRaise_coeff` (dual).

## Generality decisions

- Statement parametric in χ, χ', hχ_eq, hgχ — matches Miyake's "primes of (l, N/m_χ)" restriction.
- `[NeZero (M/p)]` instance — required for ModularForm Γ_1(M/p).
- The lemma works for ALL primes p|M with the χ-factoring; the p²∣M vs ¬p²∣M case split is internal.

## Tickets

### [T-L8-1] Upper-tri sub-sum q-expansion (L8.1)

- **Status**: open
- **File**: SMOObligations.lean (just before L8, ~line 4250)
- **Depends on**: none (uses existing `qExpansion_one_heckeT_p_divN_coeff` infrastructure)
- **Parallel**: yes
- **Type**: private lemma
- **Statement**:
```lean
private lemma miyake_descent_upper_tri_qExpansion
    {M : ℕ} [NeZero M] (p : ℕ) [NeZero p] (hp : p.Prime) (hpM : p ∣ M)
    {k : ℤ}
    (g : ModularForm ((Gamma1 M).map (mapGL ℝ)) k) (m : ℕ) :
    (ModularFormClass.qExpansion (1 : ℝ)
        (fun z => ∑ v : Fin p, (⇑g ∣[k] glMap (T_p_upper p hp.pos v.val)) z)).coeff m =
      (ModularFormClass.qExpansion (1 : ℝ) g).coeff (p * m) := by
  sorry
```
- **Proof sketch** (per Miyake p. 157, "(f|^{N'} T(p))" computation):
  1. Use `qExpansion_one_heckeT_p_divN_coeff` directly: the upper-tri sum IS `heckeT_p_ut k p hp.pos (⇑g)`.
  2. Bundle `heckeT_p_ut` as the modular form `heckeT_p_divN k p hp hpM_not_coprime g` (where `¬ Nat.Coprime p M` from `hp ∣ M`).
  3. Apply `qExpansion_one_heckeT_p_divN_coeff` to get `a_m(...) = a_{pm}(g)`.
- **Mathlib lemmas**: `qExpansion_one_heckeT_p_divN_coeff`, `Fin.sum_univ_eq_sum_range`.
- **Sources**: Miyake p. 157 (Lemma 4.6.5 proof, U_p case).

### [T-L8-2] Extra-rep integer-power vanishing (L8.2)

- **Status**: open
- **File**: SMOObligations.lean (just before L8)
- **Depends on**: T-L8-1 (for shape understanding, though independent proof)
- **Parallel**: independent
- **Type**: private lemma
- **Statement**:
```lean
private lemma miyake_descent_extra_rep_qExpansion_vanishes
    {M : ℕ} [NeZero M] (p : ℕ) [NeZero p] (hp : p.Prime) (hpM : p ∣ M) 
    (hp_sq : ¬ p ^ 2 ∣ M) [NeZero (M / p)]
    {k : ℤ}
    (χ : (ZMod M)ˣ →* ℂˣ)
    (χ' : (ZMod (M / p))ˣ →* ℂˣ)
    (hχ_eq : χ = χ'.comp (ZMod.unitsMap (Nat.div_dvd_of_dvd hpM)))
    (g : ModularForm ((Gamma1 M).map (mapGL ℝ)) k)
    (hgχ : g ∈ modFormCharSpace k χ) (m : ℕ) :
    (ModularFormClass.qExpansion (1 : ℝ)
        (fun z => (⇑g ∣[k] (Matrix.GeneralLinearGroup.mkOfDetNeZero
          !![(1 : ℝ), 0; 0, (p : ℝ)] _ * 
          mapGL ℝ (descendExtraGamma p M))) z)).coeff m = 0 := by
  sorry
```
- **Proof sketch** (per Miyake p. 161, Step (4.6.8)):
  1. Use `descendCosetList_slash_sum_rep_invariance` (T6b, proven) to standardize γ_p.
  2. Apply `slash_mul`: `g ∣ ([[1,0;0,p]] · mapGL γ_p) = (g ∣ [[1,0;0,p]]) ∣ mapGL γ_p`.
  3. Compute `(g ∣ [[1,0;0,p]])(z) = p^{-1} · g(z/p)` via mathlib's slash convention.
  4. Apply `((g ∣ [[1,0;0,p]]) ∣ mapGL γ_p)(z) = j(γ_p,z)^{-k} · p^{-1} · g((γ_p · z)/p)`.
  5. Expand g via Fourier: `g(w) = Σ_n a_n(g) e^{2πinw}`. 
  6. The expression becomes `Σ_n a_n(g) · e^{2πin(γ_p·z)/p} · j(γ_p,z)^{-k} · p^{-1}`.
  7. For integer power q^m extraction: the Puiseux components at q^{n/p} for n NOT a multiple of p contribute 0 at integer powers. The remaining (p|n, n=pm') contributes... 
  8. By the χ'-equivariance of the COMBINED slash sum and the fact that the upper-tri sum already saturates `a_{pm}(g)`, the extra-rep's integer-power contribution must be 0 (consistency).
- **Mathlib lemmas**: `descendCosetList_slash_sum_rep_invariance`, `SlashAction.slash_mul`, `Complex.exp_int_mul`, `Fin.sum_geom`.
- **Sources**: Miyake p. 161 eq. (4.6.8) — the χ̄(γ_v) cancellation; the diamond-eigenform consistency argument.

### [T-L8-3] Assemble L8 ¬p²∣M case from L8.1 + L8.2

- **Status**: open
- **File**: SMOObligations.lean line 4344-4396 (replace sorry)
- **Depends on**: T-L8-1, T-L8-2
- **Parallel**: no
- **Type**: proof completion
- **Statement**: close the sorry at line 4396 in `miyake_descent_qExpansion_at_p_divides_level`'s ¬p²∣M case.
- **Proof sketch**:
  1. `descendCosetCount p M = p + 1` from `simp [descendCosetCount, hp_sq]`.
  2. Split `∑ v : Fin (p+1)` into upper-tri (v < p, via Fin.sum_univ_castSucc) + extra rep (v = p).
  3. For upper-tri sum: identify with `glMap (T_p_upper p hp.pos v.val)` (via the dif_pos branch of descendCosetList), then apply T-L8-1.
  4. For extra rep: identify with `mkOfDetNeZero · mapGL γ_p` (via dif_neg branch), then apply T-L8-2 (gives 0).
  5. Combine: `a_m(total) = a_m(upper-tri) + a_m(extra) = a_{pm}(g) + 0 = a_{pm}(g)`. ✓
- **Mathlib lemmas**: `Fin.sum_univ_castSucc`, `Finset.sum_add_distrib`, q-expansion linearity.
- **Sources**: Miyake p. 161 (combining the upper-tri + extra-rep contributions).

## Risk assessment

**T-L8-1**: Low risk. Direct application of existing infrastructure (~50 LOC).

**T-L8-2**: **Highest risk**. The Fourier-coefficient extraction at integer powers requires care. Steps 7-8 of the sketch are the genuine math; may require novel infrastructure (Puiseux/integer-power orthogonality, or a re-framing via M5d).

Alternative approach for T-L8-2: instead of direct Fourier computation, use the **M5 bundle's char preservation** indirectly: the slash sum at level M is a χ'-eigen form at level M/p (modulo normalization), and its q-expansion is given by the M5b formula for V_p-lifted forms. For arbitrary g, the "non-V_p-lifted" part contributes 0 because the descent operator vanishes on it. This is essentially the `non_factoring_slash_sum_vanishes` argument applied to the non-V_p part of g.

**T-L8-3**: Low risk. Pure assembly (~30 LOC).

## Estimated effort

- T-L8-1: 50 LOC, ~1 hour.
- T-L8-2: 150-200 LOC, **the hard part**, may need multiple iterations.
- T-L8-3: 30 LOC, ~30 min.

Total: ~250 LOC, focused on T-L8-2.

## Approval needed

Confirm this plan? If yes, hand off to `/beastmode` to execute T-L8-1 first (easy win, validates the approach), then T-L8-2 (the hard part), then T-L8-3 (assembly).
