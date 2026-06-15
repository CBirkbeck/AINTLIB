# Reviewer reply — round 19 (received 2026-05-31)

*Reviewer note: some older uploads expired; relying on the current Round 19 file and visible prior snippets.*

## Verdict

Route 2A is still the right path. The three remaining dependencies are real, but they are **bounded and local** compared with returning to dual additivity / theorem-of-the-square in characteristic p. Status is much stronger than round 18: the determinant reduction and much of the Weil-pairing/divisor foundation are already axiom-clean, and the bound is reduced to the three concrete sub-dependencies in §8 plus the torsion fibre witness.

Recommended order:
1. First close #E[ℓ]=ℓ² using a general function-field/separable-isogeny fibre-count theorem, not an affine coordinate-ring map.
2. Then finish the pairing definition using constant-ratio functions, avoiding pointwise evaluation as much as possible.
3. Then prove the separable adjoint using picDual, not the unfinished genuine isogDual.
4. Then DET-DEG and the matrix/integer-separation endgame should be mostly formal algebra.

Would not switch back to Route 1, and would not upgrade to a full Tate-module route unless the finite-level pairing proof gets unexpectedly stuck.

## Q1 — Cleanest route to #E[ℓ]=ℓ²

Use option (a): a function-field / separable-isogeny fibre-count theorem for [ℓ] over K̄. The affine map R→R route is dead ([ℓ]^*x=Φ_ℓ(x)/Ψ_ℓ(x)² has poles at affine ℓ-torsion; a coordinate-ring witness R→R cannot exist except for special maps like Frobenius with polynomial coordinate pullback).

Clean theorem: [ℓ] separable, deg[ℓ]=ℓ² ⟹ #ker[ℓ](K̄)=ℓ². Since ℓ≠p, [ℓ] is separable via [ℓ]^*ω=ℓω≠0 (axiom-clean Th 5.6).

Least painful formal target — a reusable theorem:
  card_kernel_eq_degree_of_separable_isogeny (φ : Isogeny E₁ E₂) (hsep : φ.IsSeparable) : Fintype.card φ.kernel = φ.degree
or at least
  card_fiber_eq_degree_of_separable_isogeny (φ) (hsep) (Q : E₂.Point) : Fintype.card {P // φ P = Q} = φ.degree
Then apply to φ=[ℓ], Q=O. This is Silverman III.4.10(c); reuse the embeddings-as-translations strategy already used for Leaf 2 — much better than recovering #E[ℓ] from the x-line.

Why not the x-line: x∘[ℓ]:E→P¹ has degree 2ℓ², identifies P with −P; counting fibres introduces quotient-by-±1, ramification at 2-torsion, behaviour at O. Formally much messier.

After cardinality: every element of E[ℓ] killed by ℓ; ℓ prime ⟹ E[ℓ] is an F_ℓ-vector space; cardinality ℓ² ⟹ dimension 2. So E[ℓ]≅(ℤ/ℓ)².

## Q2 — Is the full pointwise Weil pairing the soundest path?

Yes, but define it in the constant-ratio form rather than literal pointwise evaluation. Given g_T with the required divisor, prove div(τ_S^* g_T)=div(g_T); then (τ_S^* g_T)/g_T has trivial divisor, hence is a nonzero constant; define e_ℓ(S,T) to be that constant. Uses only: (1) translation automorphism on K(E); (2) divisor transport under translation; (3) "divisor zero ⟹ constant". Theorem 5.5 is already close (parametric on the translation-invariance witness).

For §8.2: do NOT first build a broad pointwise evaluation API. Build:
  div_translate (S : E[ℓ]) (g : K(E)ˣ) : divisorOf (τ_S^* g) = translateDivisor S (divisorOf g)
and the special case div_translate_eq_self_for_gT (S T : E[ℓ]) : divisorOf (τ_S^* g_T) = divisorOf g_T.
Then define e_ℓ(S,T) as the constant quotient. Pointwise evaluation can be added later as convenience, not as foundation. This should make §8.2 smaller than it looks.

Materially shorter path avoiding the pairing: none seen. The determinant-degree congruence IS the symplectic-scaling statement e_ℓ(φv₁,φv₂)=e_ℓ(v₁,v₂)^{deg φ}. A cohomological avatar would be harder in Lean without étale cohomology / Picard functors. The divisor-theoretic Weil pairing is the most concrete path.

## Q3 — Separable adjoint: can picDual replace genuine isogDual?

Yes, for the separable part. For separable φ the divisor pullback of a point is multiplicity-free: φ^*((T)−(O))=Σ_{φP=T}(P)−Σ_{φP=O}(P). picDual=σ∘φ^* on divisor classes, with picDual∘φ=[deg φ], and for separable φ the σ-bridge is automatic. That is exactly what the adjoint needs. The adjoint e_ℓ(φS,T)=e_ℓ(S,φ̂T) can be proved with φ̂ interpreted as picDual φ, provided: (1) picDual φ is a group hom E→E; (2) maps E[ℓ]→E[ℓ]; (3) the divisor-class identity defining picDual agrees with the divisor used in the pairing proof; (4) picDual∘φ=[deg φ]. You do NOT need a separately constructed genuine function-field comorphism for φ̂ in III.8.2 — the pairing adjoint is a statement about action on points/torsion and divisor classes; Silverman's proof is Picard-divisor in nature.

Scope restriction: clean for SEPARABLE φ. That is why Route 2A's separable-factorisation rescue is valuable: apply to the separable factor λ, handle the inseparable Frobenius factor by Galois/Frobenius action. Doing the adjoint directly for inseparable rπ−s would reintroduce the σ-bridge/inseparable-pullback problem.

Recommended theorem:
  weilPairing_adjoint_separable_picDual (φ) (hsep : φ.IsSeparable) (S : E₁[ℓ]) (T : E₂[ℓ]) : eℓ (φ S) T = eℓ S (picDual φ T)
Then use picDual φ in DET-DEG for separable φ. Can later prove picDual=isogDual if desired, but it should not block the pairing proof.

## Q4 — Is Route 2A still right?

Yes. The three sub-dependencies are genuine but none is a warning sign. Returning to Route 1 reopens dual additivity in char p / theorem-of-square / the full genuine dual of rπ−s (the hard wall). A full Tate-module route is unnecessary: finite level for all ℓ≠p suffices, and the finite-level reduction is in place; ℓ-adic would add inverse limits / ℤ_ℓ-modules / topological algebra without removing the torsion/pairing/adjoint lemmas.

Attack order: (1) §8.1 #E[ℓ]=ℓ² (foundational — without it determinant language is awkward; via the general separable-isogeny fibre theorem; creates reusable infra); (2) §8.2 pairing definition via constant quotient (reuse local-ring/valuation translation work); (3) §8.3 separable adjoint with picDual. This minimises circularity: adjoint depends on pairing def; DET-DEG depends on adjoint; Hasse depends on DET-DEG.

## Cautions

1. "Positive definite" vs "nonnegative": the form may be semidefinite in degenerate scalar-collapse cases. For Hasse you only need qr²−trs+s²≥0. Use "nonnegative"/"positive semidefinite" in comments unless all nontrivial zeroes are ruled out.
2. Pairing values in μ_ℓ: if e_ℓ is a constant quotient in K̄ˣ, still prove e_ℓ(S,T)^ℓ=1 (already in Th 5.5; keep as a core output of PAIRING-DEF/PROPS).
3. Nondegeneracy: often the most delicate part; uses functions with prescribed divisors + Abel–Jacobi/Pic⁰. Give it its own ticket rather than folding into bilinearity.
4. Integer separation: be explicit. D:=deg(rπ−s)−(qr²−trs+s²); if D≠0 only finitely many primes divide D; choose ℓ≠p not dividing D, contradiction. Avoids ℓ-adic machinery.

## Final answers

Q1. General separable-isogeny fibre-count over K̄: [ℓ] separable, deg[ℓ]=ℓ² ⟹ #E[ℓ]=ℓ². Not affine R→R; avoid the x-line.
Q2. Divisor-theoretic Weil pairing, defined by the constant quotient (τ_S^*g_T)/g_T, not pointwise evaluation first.
Q3. Yes, use picDual for the separable adjoint; needs only Picard-level dual action + multiplicity-free pullback, not the genuine isogeny dual as a function-field map.
Q4. Route 2A is soundest. Attack §8.1 → §8.2 → §8.3. Don't return to Route 1; don't upgrade to full Tate modules unless the finite-level pairing stalls.
