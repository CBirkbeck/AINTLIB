# Reviewer reply — round 22 (2026-06-03)

## Verdict
Use **R1** — the cleanest route now. With the listed ingredients, surjectivity is exactly the standard "places above a place exist" theorem + the already-proved `hproj`. No deeper geometry hidden.
`lying-over for K(E)/φ*K(E)  +  point–place bijection  +  hproj  ⟹  φ_* : E(K̄)→E(K̄) surjective.`
**KEY:** phrase the lifted object as an EXTENSION OF THE PLACE/VALUATION `v_Q`, NOT a coordinate-ring prime of an affine model — this avoids the CoordHom obstruction completely.

## Q1 — precise R1 sequence
Let `L = K̄(E)` (source = target, same curve), `φ* : L ↪ L` the comorphism, `M = φ*(L) ⊂ L`. For a target point `Q`, let `v_Q` be its place of the target `L`. Transport `v_Q` to a place `v_Q^φ` of `M` via the iso `L ≅ M, g ↦ φ*g` (so `v_Q^φ(φ*g) = v_Q(g)`). Since `L/M` is finite, lying-over: every place of `M` extends to a place `w` of `L`; choose `w` extending `v_Q^φ`. Point–place bijection over K̄: `w = v_P` for a unique `P`. Because `w` lies over `v_Q^φ`, for all `g`, `v_P(φ*g)` has the same valuation ring/sign as `v_Q(g)`. Now `hproj`: `v_P(φ*g) = v_{φ_*P}(g)`. So `v_{φ_*P} = v_Q`; by injectivity of point–place, `φ_*P = Q`.

Missing lemmas: (A) `exists_place_over_of_finite_extension (v : Place M) : ∃ w : Place L, w.restrict M = v` (or via valuation rings / height-one primes of the integral closure); (B) `place_lies_over_target_iff_via_hproj (hproj) (P Q) : place_P liesOver transported_place_Q ↔ φ_*P = Q` — `hproj` does exactly this identification; no extra geometric step beyond point–place injectivity.

**Normalisation warning:** an extension may restrict as `w|_M = e·v_Q^φ` (ramification), not literally `v_Q^φ` — fine. You do NOT need exact valuation-value equality for lying-over; only equality of valuation rings / maximal ideals / sign: `w(φ*g)>0 ⟺ v_Q(g)>0`. Then `hproj` gives `v_{φP}(g)>0 ⟺ v_Q(g)>0`, so the places are equal. State the proof at the level of VALUATION-RING equality, not normalised integer `ord`.

## Q2 — R4 = R1 in scheme language
Yes. "Image closed, nonconstant, hence all of E" is the scheme-theoretic version of "for every target place `v_Q`, a source place lies above it" = lying-over for places/valuation rings of a finite morphism. Do NOT formalise the Zariski-image (R4); formalise the function-field version `finite_functionField_map_surjective_on_places`, combine with `hproj`. Smallest reusable lemma; also helps `rπ−s` + separable factors.

## Q3 — is surjectivity necessary for the dual?
For the CURRENT global divisor-pushforward dual `δ(Q)=σ(φ*((Q)−(O)))`: YES. If `φ_*^{-1}(Q)=∅` then `φ*(Q)=0`, so `deg(φ*((Q)−(O))) = 0 − #ker ≠ 0` — not degree-0, δ not defined on all of E (exactly your found failure). So for a global `δ:E→E` with the fibre-pullback definition, surjectivity is not optional.
BUT narrower scaling-only bypass: for `e_ℓ(φS,φT)=e_ℓ(S,T)^{#ker}`, the 2nd argument `φT` is automatically in the image; `φ^{-1}(φT)=T+ker φ` (group-hom property only). So `φ*((φT)−(O)) = Σ_{R∈ker}((T+R)−(R))`, degree 0, sum `#ker·T`. An image-restricted adjoint-on-image theorem avoids defining `δ(Q)` for arbitrary Q — may suffice for the scaling. But your current abstract scaling consumes a global δ; if changing it is cheap this avoids surjectivity entirely; if wired around global δ, R1 is less disruptive. RECOMMENDATION: R1 is close — prove surjectivity; keep the image-restricted trick in reserve if lying-over formalisation becomes large.

## Q4 — smallest reusable lemma
Two lemmas, function-field/place-level (NOT elliptic-curve-first):
- **Lemma A (lying-over for places):** `exists_place_over {M L} [Field M][Field L][Algebra M L][FiniteDimensional M L] (v : Place M) : ∃ w : Place L, w.LiesOver v` — pure commutative algebra / valuation theory (or via `HeightOneSpectrum` of the integral closure: `∃ P, P liesOver p`).
- **Lemma B (place map from genuine isogeny + hproj):** `pointMap_eq_of_place_liesOver (hproj) (hLie : placeOf P LiesOver transportedPlaceOf Q) : φ.pointMap P = Q` (forward implication is all surjectivity needs).
- **Lemma C (surjectivity):** `surjective_of_finite_comorphism_and_hproj (hfinite : FiniteDimensional φ.pullback.range K(E)) (hproj) : Function.Surjective φ.pointMap`.
The bridge for every separable pencil member.

## Practical Lean advice
- AVOID affine coordinate rings (the place Q=O + poles of 1−π keep causing pain). Work with: function fields; valuation rings/places; height-one spectra of normal projective models. The point–place bijection over K̄ is the correct interface.
- Use VALUATION RINGS not normalised integer valuations for lying-over: easier to show `m_w ∩ M = m_v` than integer `ord` equality; then point–place bijection. Define a place by its valuation ring `O_v={f:v(f)≥0}`, `m_v={f:v(f)>0}`; lying-over = `m_w ∩ M = m_v`; `hproj` turns that into geometric place equality.
- Separate exact equality (hproj: `ord_P(φ*g)=ord_{φP}(g)`) from sign equality (lying-over: valuation-ring equivalence). Use exact equality only after choosing P; don't demand the lifted valuation be normalised so restriction is exact.

## Final answers
Q1. R1: transport v_Q to φ*K(E); lying-over → source place w; point–place → w=v_P; hproj → restricted place is v_{φP}; compare with v_Q; conclude φP=Q.
Q2. R4 = R1 in scheme language; formalise the function-field/valuation lying-over, not a Zariski image.
Q3. For the current global fibre-pullback dual, surjectivity is necessary; but an image-restricted scaling proof can avoid global surjectivity (φ^{-1}(φT)=T+ker φ) — fallback if R1 grows large.
Q4. Least infra = finite-extension lying-over for places + hproj-identification; package as `surjective_of_finite_comorphism_and_hproj`, reuse for every separable pencil member.
