# Reviewer reply — received 2026-05-11

## Assessment

The overall architecture is sound, but the current dependency graph overstates one dependency and understates one mathematical risk.

The **Γ₀(N)-pivot is correct** for the algebraic Hecke-ring story. A naïve Γ₁(N) abstract Hecke ring cannot give the right `T_p` on character spaces without encoding the diamond/nebentypus correction, because `diag(1,p)` and `diag(p,1)` are distinct Γ₁(N)-double cosets unless `p ≡ 1 mod N`. For commutativity and Shimura-style Hecke algebra results, Γ₀(N) is the right level.

The **general-χ abstract ring homomorphism should be parked**, not forced. If the current abstract action uses `Quotient.out` representatives, it is not the right object for nontrivial characters. The explicit `T_p` with the diamond-twisted lower summand is mathematically correct and should remain the main character-space operator. A future cleanup could define a character-twisted Hecke correspondence action, but POST-1 is not on the SMO critical path.

The **T_p Petersson adjoint is indeed a major critical blocker**, but it should be reframed one level higher. The project should not keep proving ad hoc per-matrix or per-tile identities. The right theorem boundary is a general finite-index Hecke-correspondence adjoint theorem: finite-index subgroup tiling plus single-slash adjoint implies the double-coset operator adjoint. Then specialize to `T_p`.

However, **T205-d is not the only critical blocker for the whole project**. Miyake's Main Lemma should not depend on T207 if it is proved by Miyake's sieve/conductor argument. The brief's proposed POST-4 proof via spectral decomposition and a claim that newforms have `a_n = 0` for `(n,N)>1` is mathematically unsafe: newforms can have nonzero bad-prime coefficients. The Main Lemma route should be finished directly using the existing sieve/conductor/support infrastructure, not by waiting for the spectral theorem.

Similarly, **POST-5 / analytic nonzero prime eigenvalue is not necessary for Miyake finite-exception SMO** if Miyake 4.6.8 is available. Agreement outside a finite set of primes gives agreement of coefficients whose indices are coprime to the product of the level and exceptional primes; the Main Lemma is designed exactly to handle that sparse support. The L-function track is valuable, but it should be parallel, not on the core Miyake-SMO critical path.

So the corrected near-term critical tracks are:

1. **Adjoint/spectral track:** T205-d finite-index Hecke-correspondence adjoint → T207 simultaneous eigenbasis/newspace machinery.
2. **Main Lemma track:** finish Miyake 4.6.8 assembly directly from sieve/conductor/support decomposition; do not wait for T207 unless a specific later old/new orthogonality consumer needs it.
3. **SMO assembly:** use Main Lemma plus newform/primitive decomposition and uniqueness.
4. **L-function track:** continue independently for Euler products and stronger analytic consequences, but do not make finite-exception SMO depend on it unless the project deliberately chooses an analytic proof route.

## Mathematical idea

The clean adjoint theorem is not a special identity for the `p+1` matrices. It is the standard Hecke correspondence adjoint statement.

Let `Γ = Γ₁(N)` and let `α ∈ GL₂⁺(ℚ)` be in the commensurator of `Γ`. Put, depending on the orientation of the existing coset API,

```
K = Γ ∩ α⁻¹ Γ α
```

or the corresponding conjugate-intersection subgroup. If `D` is a fundamental domain for `Γ`, and `R` is a finite transversal for `K \ Γ` or `Γ / K`, then the finite union

```
⋃ r ∈ R, r • D
```

is a fundamental domain for `K`. Applying `α` transports it to a fundamental domain for the conjugate subgroup. Then the single-slash change-of-variables identity gives

```
⟨ ∑ f|α_i, g ⟩_Γ = ⟨ f, ∑ g|α_i^* ⟩_Γ
```

where `{α_i}` and `{α_i^*}` are compatible representatives for the two adjoint double cosets.

This is the structural theorem Diamond–Shurman's proof is using. The explicit `T_p` adjoint then becomes a specialization:

* start with the double coset of `diag(1,p)`;
* apply the adjugate, giving `diag(p,1)`;
* identify the adjugate-side operator with the diamond-shifted `T_p` using the already proved triple-product identity and diamond unitarity.

This avoids the false per-summand "tile balance" approach. Individual Hecke representatives do not balance in isolation; the correspondence balances as a finite aggregate.

For Phase 8, the faithful Miyake idea is also aggregate/sieve-based, not spectral. If `h = f - g` has coefficients vanishing for all indices coprime to a product `L` of the level and exceptional primes, Miyake 4.6.8 decomposes `h` as an old/lower-level combination supported at primes dividing `gcd(L, N / conductor χ)`. Newness/primitive orthogonality then kills the difference. This proof does not require a nonzero eigenvalue outside a finite set.

## Lean-facing next steps

Create or refocus the current T205 ticket around two theorem boundaries.

**First theorem boundary**: finite-index fundamental-domain tiling.

```lean
/-- If `K ≤ Γ` has finite index and `D` is a fundamental domain for `Γ`,
then the finite union over a transversal for `K \ Γ` is a fundamental domain for `K`. -/
theorem isFundamentalDomain_iUnion_smul_of_finiteIndex
    (hK : K ≤ Γ)
    (R : Finset G)
    (hR : IsLeftTransversal K Γ R)
    (hD : MeasureTheory.IsFundamentalDomain Γ D μ) :
    MeasureTheory.IsFundamentalDomain K (⋃ r ∈ R, r • D) μ
```

This should also expose the AE-disjointness, null-measurability, and integrability-transfer corollaries needed by Petersson sums.

**Second theorem boundary**: Hecke-correspondence adjoint.

```lean
/-- Petersson adjoint for a finite double-coset correspondence. -/
theorem petN_doubleCoset_adjoint
    (α : GL (Fin 2) ℚ)
    (hα : α ∈ commensurator Γ)
    (R : Finset (GL (Fin 2) ℚ))
    (Rstar : Finset (GL (Fin 2) ℚ))
    (hR : IsDoubleCosetRepFamily Γ α R)
    (hRstar : IsAdjugateRepFamily Γ α R Rstar)
    (f g : CuspForm Γ k) :
    petN (∑ r ∈ R, slash r f) g =
      petN f (∑ rstar ∈ Rstar, slash rstar g)
```

Then specialize to `α = diag(1, p)`:

```lean
theorem petN_heckeT_p_diamond_shift_core
    (hp : p.Prime) (hpN : Nat.Coprime p N) :
    petN (heckeT_p f) g = petN (diamond p f) (heckeT_p g)
```

using the explicit `T_p` formula, triple-product identity, and diamond unitarity.

For T207, use Mathlib's commuting-family eigenspace API. The right condition on the operators is normal/semisimple plus pairwise commutativity. On a χ-space, the adjoint formula becomes scalar-diamond action, so check the scalar unit/normality statement carefully.

For Phase 8, create a separate Main Lemma assembly ticket that does **not** depend on T207 unless a concrete lemma forces it. Acceptance criterion:

```lean
theorem mainLemma
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (h : ∀ n : ℕ, Nat.Coprime n N →
      (ModularFormClass.qExpansion (1 : ℝ) f).coeff n = 0) :
    f ∈ cuspFormsOld N k
```

should be proved from the existing Miyake-style conductor/sieve/support machinery. Do not use the false assertion that newforms vanish at bad-index coefficients.

**Park these for now:**
* POST-1 general-χ abstract ring homomorphism;
* reverse support decomposition via trace;
* full Atkin–Lehner involution;
* L-function nonvanishing as a blocker for finite-exception SMO.

Keep POST-3 running only as a parallel analytic project, not as the core route to Miyake 4.6.12.

## Risks or missing facts

1. **Biggest hidden mathematical risk:** the claim in the brief that newforms have coefficients `a_n = 0` for `(n,N)>1`. That is false in general. Bad-prime coefficients of newforms are subtle and often nonzero. Any proof of `mainLemma` or SMO relying on that should be rejected.

2. **Scalar normalization in the adjoint theorem.** With slash convention `(f|k α)(τ) = det(α)^(k-1) (cτ+d)^(-k) f(ατ)`, the adjugate `α*` is not interchangeable with `α⁻¹` without tracking scalar action. Reuse the single-slash adjoint theorem rather than recomputing scalars informally.

3. **Don't use a normalizer lemma for a non-normalizing matrix.** Hecke representatives like `diag(1,p)` do not normalize `Γ₁(N)`. The correct subgroup is an intersection `Γ ∩ α⁻¹Γα`, not `Γ` itself.

4. **Don't force abstract general-χ via Quotient.out.** Representative-dependent χ-factors are real; this is not a Lean nuisance. The explicit operator with diamond twist is mathematically the correct operator.

5. **Don't overgeneralize the FD-transport lemma.** Project only needs finite-index subgroups of congruence subgroups acting on ℍ with hyperbolic measure. Prove the narrow theorem first.

6. **Status accounting.** Several "done" theorems are conditional or sorry-backed through `mainLemma` or T205-d. The board should distinguish "consumer wrapper compiles" from "foundational theorem proved."

7. **Final theorem formulation across different levels/characters.** If `f` and `g` have levels `N₁` and `N₂`, "same χ" must be expressed through a common primitive/conductor character or compatible induced characters at the common level.

## Manager message to worker

Refocus T205-d on the Hecke-correspondence adjoint theorem. Do not keep proving per-representative tile identities; those are the wrong granularity.

Two-step API:
1. Finite-index FD-transport lemma (narrowest usable form): `K ≤ Γ₁(N)` finite-index, `D` a Γ₁(N)-FD, then ⋃_{r ∈ R} r • D is a K-FD, with AE-disjointness/measurability/integrability corollaries for Petersson sums.
2. Hecke-correspondence adjoint: for `α ∈ GL₂⁺(ℚ) ∩ Comm(Γ₁(N))`, the finite double-coset slash operator's Petersson adjoint is the adjugate double-coset operator.

Then specialize to `α = diag(1,p)` to close `petN_heckeT_p_diamond_shift_core` via explicit T_p + triple-product identity + diamond unitarity.

Do not spend this pass on POST-1, trace operators, reverse support decomposition, or L-function nonvanishing.

Separately, create a Main Lemma assembly ticket using existing Miyake sieve/conductor/support machinery — NOT depending on T207 unless a precise missing lemma proves the dependency is unavoidable. Remove the FALSE newform coefficient assertion.

For T207, once T205-d lands, use Mathlib commuting-family eigenspace API.

Board cleanup: POST-1 and reverse support decomposition → architectural cleanup, not critical path. POST-3/POST-5 → parallel analytic work, not required for Miyake finite-exception SMO.
