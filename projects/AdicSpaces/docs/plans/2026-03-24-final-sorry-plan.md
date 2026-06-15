# Final Sorry: berkeley_6_2_8 — Comprehensive Plan

## Key Mathematical Insight

**PreTilt.coeff 0 is INJECTIVE on tilt p A** (because tilt p A is a
perfect ring, hence reduced; and coeff_0 on a perfection of a ring has
trivial kernel when the perfection is reduced).

This means: for any `x ∈ ker(θ)`, the equation `θ([x.coeff 0]) + p·θ(x') = 0`
gives `(x.coeff 0).untilt ∈ (p)`, hence `PreTilt.coeff 0 (x.coeff 0) = 0`
(by mk_untilt_eq_coeff_zero), hence `x.coeff 0 = 0` (by injectivity).

**Consequence:** `ker(θ) ⊆ ker(constantCoeff) = (p)`.

## The Proof Strategy

Since every x ∈ ker(θ) has x.coeff 0 = 0 (i.e., x ∈ (p)):

**If p is a non-zerodivisor in A°:** Then for x = p·y ∈ ker(θ),
p·θ(y) = 0 implies θ(y) = 0. So y ∈ ker(θ). By induction, x ∈ (p^n)
for all n, hence x = 0 by Hausdorffness. So ker(θ) = ⊥, contradicting
hker. Therefore this case doesn't arise.

**If p is a zerodivisor in A°:** The Berkeley Lectures construction
provides ξ = p + [ϖ]α (primitive, with ξ.coeff 0 = ϖ·(α.coeff 0) ≠ 0).
Since ξ ∈ ker(θ) and ξ.coeff 0 ≠ 0, this CONTRADICTS the result above
(that all kernel elements have coeff 0 = 0).

Wait — this means ker(θ) ≠ ⊥ implies there EXISTS a kernel element with
coeff 0 ≠ 0, which contradicts the injectivity argument. Unless the
injectivity argument has a flaw.

## Re-examining the Injectivity Argument

For x ∈ ker(θ): θ(x) = 0. Write x = [x.coeff 0] + p·x'.
Then θ([x.coeff 0]) + p·θ(x') = 0.
So θ([x.coeff 0]) = -p·θ(x').

θ([x.coeff 0]) = (x.coeff 0).untilt (by fontaineTheta_teichmuller).

mk((x.coeff 0).untilt) = PreTilt.coeff 0 (x.coeff 0) (by mk_untilt_eq_coeff_zero).

From θ([x.coeff 0]) = -p·θ(x'): mk(θ([x.coeff 0])) = mk(-p·θ(x')) = 0 in A°/(p).

So PreTilt.coeff 0 (x.coeff 0) = 0 in A°/(p).

Now: does PreTilt.coeff 0 (x.coeff 0) = 0 imply x.coeff 0 = 0 in tilt p A?

tilt p A = Perfection(A°/(p)). An element a ∈ Perfection(R) has a = (a_0, a_1, ...)
with a_{n+1}^p = a_n. PreTilt.coeff 0 (a) = a_0.

If a_0 = 0: a_1^p = 0. In Perfection(R), a_1 is also a "coherent" element.
a_1^p = 0 means a_1 is nilpotent. But Perfection(R) is a PERFECT ring,
hence reduced (no nonzero nilpotents). So a_1 = 0. By induction, a = 0.

**This argument IS correct.** So PreTilt.coeff 0 IS injective on Perfection(R).

## Conclusion

ker(θ) ⊆ (p) in W(tilt p A). Combined with Hausdorffness and
p-adic completeness, the iteration x = p·y₁ = p²·y₂ = ...
converges to x = p^∞ · (something) = 0 by Hausdorffness.

But this contradicts ker(θ) ≠ ⊥!

Unless p·θ(y) = 0 does NOT imply θ(y) = 0, i.e., p is a
zerodivisor in A°. In that case, y ∉ ker(θ), and the iteration
stops at x = p · y₁ where y₁ ∉ ker(θ).

**THE KEY:** The division step with q = 0, r = y₁ gives
x = ξ · 0 + p · y₁. But y₁ ∉ ker(θ), so this DOESN'T satisfy
the division step requirement (r ∈ ker(θ)).

For the division step to work, we need ξ to "absorb" the p-torsion.
The primitive element ξ = p + [ϖ]α does this: ξ ≡ [ϖ·α₀] (mod p),
so in W(k)/(p) ≅ k, the division x.coeff 0 / ξ.coeff 0 uses the
TILT structure, not the untilt A° structure.

## The ACTUAL Proof (Revised)

The Berkeley Lectures proof does NOT use the division step directly.
It uses the QUOTIENT COMPUTATION:

W(R⁺)/(ξ, [ϖ]) = W(R⁺)/(p, [ϖ]) = R⁺/ϖ = R♯⁺/ϖ♯

And then [ϖ]-adic completeness + Nakayama.

For our formalization: we CAN'T use `ker_of_primitive_and_division`
for this (it needs the division step which requires p-torsion-freeness
in A°). We need a DIFFERENT approach — the quotient computation.

## CORRECTION: PreTilt.coeff 0 is NOT injective

The earlier claim that "PreTilt.coeff 0 is injective" was WRONG.
The perfection of a ring with nilpotents (like A°/(p)) has nonzero
elements with 0-th component zero. Example: (0, ϖ̄, b₂, ...) where
ϖ̄^p = 0 in A°/(p) and b₂^p = ϖ̄ (exists by Frobenius surjectivity).

This means ker(θ) is NOT necessarily contained in (p), and the
full Berkeley construction of the primitive element IS needed.

## REVISED PLAN: Full Berkeley Construction

### Part A: Construct ξ ∈ ker(θ) with ξ.coeff 0 ≠ 0

1. Get ϖ, c with p = c · ϖ^p from `exists_pseudoUniformizer`
2. Lift ϖ̄ to varpi_flat ∈ PreTilt via `coeff_surjective`
3. Lift c to c' ∈ Ainf via `theta_surjective`
4. Form α₀ = c' · [varpi_flat]^p
5. θ(α₀) = c · (varpi_flat.untilt)^p
6. varpi_flat.untilt ≡ ⟨ϖ,_⟩ (mod p) by `mk_untilt_eq_coeff_zero`
7. c · (varpi_flat.untilt)^p ≡ c · ⟨ϖ,_⟩^p = p (mod p) by binomial
8. So θ(α₀) - p ∈ (p). Get err with θ(α₀) = p + p · err.
9. Lift err to w₁ via theta_surjective.
10. ξ = α₀ - p - p · w₁. θ(ξ) = 0. ξ.coeff 0 = α₀.coeff 0 ≠ 0.

### Part B: Division step for ξ

For x ∈ ker(θ), write x = [x.coeff 0] + p · x'.
Need: x.coeff 0 = ξ.coeff 0 · q₀ in tilt p A (for some q₀).
Then x - ξ · [q₀] ∈ (p), giving the division.

The divisibility x.coeff 0 / ξ.coeff 0 uses the STRUCTURE of
ξ.coeff 0 = c'.coeff 0 · varpi_flat^p in tilt p A. Since
varpi_flat has PreTilt.coeff 0 = ϖ̄ (a pseudo-uniformizer of k),
varpi_flat^p has PreTilt.coeff 0 = ϖ̄^p = 0. So ξ.coeff 0 has
its 0-th Perfection component = 0.

For x ∈ ker(θ): similarly x.coeff 0 has 0-th component = 0.
Both are in the kernel of PreTilt.coeff 0 : tilt p A → A°/(p).

The kernel of PreTilt.coeff 0 on a Perfection is the image of
the inverse Frobenius: ker(coeff_0) = F⁻¹(Perfection(R)).
Since ξ.coeff 0 = c'.coeff 0 · varpi_flat^p and varpi_flat is
a pseudo-uniformizer of tilt p A, the element ξ.coeff 0 has
a specific divisibility structure in this kernel.

**This is the hardest part.** It requires understanding the ideal
structure of tilt p A in terms of the pseudo-uniformizer.

### Part C: Apply ker_of_primitive_and_division (PROVED)

Once Parts A and B are done, the sorry is filled.
