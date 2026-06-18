# Reviewer reply — round 21 (2026-06-03)

## Verdict
There **is** a cheaper route than the ≈1000-line closed-point addition-formula specialisation:
**prove generic translation covariance `hgcomm` + use the formal/local linear coefficient at O + transport by translations.**

Do NOT re-run the `[ℓ]` division-polynomial proof for `1−π`/`rπ−s`. The `[ℓ]` proof needed a closed-point coordinate-specialisation because it evaluated explicit rational coordinate functions at points. For the Frobenius pencil there is a structural route: these are group endomorphisms whose local formal action at any point is obtained from their action at O by translation. That collapses `hproj` for all separable pencil members to a local one-variable statement.

Next target:
```
hgcomm + formal_linear_coeff_nonzero ⇒ hproj
```
where for φ = rπ−s the formal linear coefficient is −s; for 1−π it is 1.

## Q1 — Can hproj reuse translation transport + decomposition of 1−π?
Yes. Do NOT decompose globally through the addition morphism m:E×E→E and prove closed-point specialisation of X_add. Use local group-homomorphism structure. For a group endomorphism φ, translate P and φ(P) to O; then τ_{−φ(P)}∘φ∘τ_P is the same formal endomorphism as φ at O, because φ(P+R)−φ(P)=φ(R). For 1−π: (1−π)(P+R)−(1−π)(P)=R−π(R). For rπ−s: r·π(R)−s·R. So everything reduces to the formal expansion at the identity: 1̂−π(T)=T+O(T²) (T minus a Frobenius term of order q), and r̂π−s(T)=−sT+O(T²) when p∤s. If p∤s the local map has a unit linear term ⇒ ramification index 1 ⇒ order transport ord_P(φ^*h)=ord_{φ(P)}(h).

Suggested: `hproj_of_hgcomm_and_unit_formal_linear_coeff (φ)(hgcomm)(hlin : formalLinearCoeff φ ≠ 0) : ∀ P h, ord_P(φ.pullback h)=ord_(φ P) h`, then `formalLinearCoeff(1−π)=1`, `formalLinearCoeff(rπ−s)=−s`. Uses existing translation-order machinery (§6.6), not closed-point evaluation. Needs only: (1) covariance with translations; (2) formal expansion at O; (3) a DVR lemma: a local hom sending a uniformizer to a unit times a uniformizer preserves orders.

## Q2 — hsurj directly from the function-field extension?
Not without a compatibility theorem. Lying-over for K(E)/φ^*K(E) gives a place above the pulled-back place — surjectivity for the geometric morphism of the comorphism. To conclude ∃P, φ_*(P)=Q for the abstract point-map field you must identify the abstract point map with the geometric point map of the comorphism — the same compatibility. So hsurj and hproj should be proved together, with hproj the real compatibility theorem. Once hproj holds: take a place above Q by lying-over; use hproj/place compatibility to show its image under the abstract point map is Q; obtain a preimage.

## Q3 — Is hgcomm cheap?
Yes, relative to hproj — prioritise it first. For 1−π and rπ−s, hgcomm is the homomorphism property φ(P+S)=φ(P)+φ(S), contravariantly τ_S^*∘φ^*=φ^*∘τ_{φ(S)}^*. A generic-point identity, not a closed-point specialisation: uses Frobenius is a homomorphism, multiplication maps are homomorphisms, addition/translation associativity, and that the comorphism is genuinely the generic addition/rational formula. No valuations or finite fibres. If it is NOT cheap, the addition-pullback API is too formula-bound and should be reorganised around generic-point functoriality.

## Q4 — One object or per-facet?
Build ONE object, but make it local/formal, not global-coordinate-heavy. Don't prove hproj/hsurj/hgcomm separately — same compatibility in different forms. Structure `LocalGeometricRealization φ`: `hgcomm`, `formal_linear_coeff ≠ 0`, `local_at_O : ord_O(φ.pullback t)=1` (or derive from formal coeff). Then `hproj` and `hsurj` as theorems. hgcomm ⇒ translation reduction to O; local coeff at O ⇒ unramifiedness/order preservation; lying-over + order compatibility ⇒ surjectivity; pairing covariance is a corollary. This is the geometric-realisation bridge you wanted, avoiding the X_add specialisation bottleneck.

## Q5 — Scaling without per-place transport?
For the full determinant-degree theorem, no. Special calc: for 1−π, bilinearity + Frobenius/Galois + π+V=[t] can show e_ℓ((1−π)S,(1−π)T)=e_ℓ(S,T)^{q+1−t} directly; since q+1−t=#E=deg(1−π), this gives the scaling for 1−π WITHOUT hproj for 1−π. Generally for rπ−s, bilinearity gives e_ℓ((rπ−s)S,(rπ−s)T)=e_ℓ(S,T)^{qr²−trs+s²} (given the adjoint/Galois relation for π) — recovers the matrix determinant exponent. But this does NOT identify the exponent with deg(rπ−s); the missing step is exactly qr²−trs+s²=deg(rπ−s)≥0. So the direct expansion avoids bookkeeping for 1−π but does not close Hasse for general (r,s). Use it for 1−π if it reduces dependencies; don't expect it to replace hproj for the general pencil.

## Recommended execution plan
1. Prove hgcomm first (generic group-law identity, cheapest).
2. Prove the local formal lemma `hgcomm + formalLinearCoeff φ ≠ 0 ⇒ hproj` (or `ord_O(φ.pullback t)=1`) for 1−π and rπ−s (p∤s), transport to all P.
3. Derive hsurj (finite extension/lying-over + hproj to identify the place with a point mapping to Q).
4. Feed the round-20 bridge to discharge covariance, divisor transport, #ker=deg.

## Final answers
Q1. Yes — generic translation covariance + formal local behaviour at O, transported by translations. Don't rederive closed-point X_add.
Q2. Function-field lying-over still needs compatibility to identify the abstract point-map image; prove hsurj and hproj together, hproj the core.
Q3. hgcomm cheap, attempt first — generic-point group-homomorphism identity, not a valuation theorem.
Q4. Build one local/geometric-realisation object; once it supplies hgcomm + unit local linear coeff, hproj and hsurj are bookkeeping.
Q5. Direct bilinear/Galois expansion proves the scaling exponent for 1−π (and Q(r,s) formally), but does not identify Q(r,s) with the degree; for the general pencil geometric compatibility remains necessary.
