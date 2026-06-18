# Reviewer reply — round 20 (2026-06-03)

## Verdict
Stay with Route 2A. The residue is a representation/interface problem, not a new mathematical obstruction. Next move = **(A)**: build a small bridge from the abstract two-field isogenies to the existing geometric isogeny/fibre machinery, then reuse III.4.10/III.8.2. Do NOT rebuild all pencil isogenies geometrically unless the bridge becomes painful.

## Q1 — bridge once or rebuild geometrically?
Use **A now**; treat as first step toward eventually eliminating the two-field design (a design smell). B (full geometric rebuild) is too expensive now (risks disturbing the determinant reduction). Add a bridge structure `GeometricRealization φ`/`IsGenuine φ` carrying `geom : GeometricIsogeny` + `pullback_eq` + `pointMap_eq`. Prove once: `realized_surjective_of_separable`, `realized_translation_covariance`, `realized_divisor_transport`. Instantiate for 1−π, rπ−s, and any separable factor λ.

## Q2 — can separable scaling avoid surjectivity + divisor transport?
Partly. Can reduce dependence on point-map surjectivity, and phrase degree-mult with `deg φ` not `#ker φ`. CANNOT eliminate divisor transport, covariance, or point-map/comorphism compatibility — the pairing statement mixes `φS`, `τ_{φS}`, and `φ^*`, so the proof must know they belong to the same morphism. Restate `separable_scaling_of_genuine (hφ : IsGenuine φ) (hsep) : eℓ(φS)(φT)=eℓ S T ^ φ.degree`, hiding surjectivity/transport/covariance inside; caller's only new input is `IsGenuine φ`.

## Q3 — degree multiplication from comorphism alone?
YES, if phrased with `deg φ` not `#ker φ`. `deg(φ^*D)=deg(φ)·deg(D)` is a function-field/ramification theorem (Σ e·f = [K(E):φ^*K(E)]) — needs only the comorphism field extension + divisor pullback through valuations/places, NOT the point-map. Prove `degree_pullbackDivisor_eq_degree_mul (φ)(D) : degree(φ.pullbackDivisor D) = φ.degree * degree D` from the comorphism side. Then for separable maps rewrite `deg φ = #ker φ` only when a point-map theorem needs it. The current divisor-pushforward dual "consumes point-map surjectivity to know φ^* multiplies degrees by #ker" — WRONG dependency direction; replace by `degree_pullback = φ.degree * degree` from comorphism, then use `φ.degree = card kernel` only when needed.

## Q4 — Frobenius factor: Galois-equivariance or factorisation?
For the q-Frobenius π, use **Galois-equivariance** `e_ℓ(S^σ,T^σ)=e_ℓ(S,T)^σ` with σ(a)=a^q. Fewer prerequisites than relative-Frobenius factorisation (avoids twist bookkeeping). Constant-ratio proof: (1) Frobenius transports divisors `div(g_T^σ)=σ(div g_T)`; (2) pairing independence from choice of g_T; (3) translation commutes with Frobenius `σ∘τ_S=τ_{σS}∘σ`; (4) therefore `τ_{σS}^* g_{σT}/g_{σT} = (τ_S^* g_T/g_T)^σ`. The F^e factorisation version is a corollary/separate generalisation, only for arbitrary inseparable pencil members.

## Q5 — Route 2A still right? A or B next?
Yes, Route 2A. Spend next effort on **A: the point-functor/geometric-realisation bridge**, not B. A is one reusable compatibility layer that discharges the current residue for every pencil member; B (geometric rebuild) is long-term cleanup after the bound closes. Immediate milestone: `GeometricRealization` structure + `separable_scaling_witnesses_of_geometricRealization (hφ)(hsep) : Surjective φ.toAddMonoidHom ∧ TranslationCovariant φ ∧ DivisorTransport φ`, instantiated for 1−π, rπ−s, λ.

## Caution
Define the bridge at the right level: NOT merely agreement on closed points — need compatibility with the comorphism. Include BOTH `pointMap_eq` AND `pullback_eq`; prove covariance/transport by transporting from the geometric isogeny through both.
