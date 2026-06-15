# Reviewer reply — round 10 (2026-05-29)

Congratulations on Leaf 2 — the embeddings/torsor route is exactly the right function-field-first way. Materially changes the posture: skeleton has only Leaf 1 left.

## Correction (separability landscape is cleaner than the brief said)
For β = rπ−s, the invariant-differential multiplier is a_β = r·a_π − s·a_1 = 0 − s = −s. So (β≠0) **β is separable ⟺ p∤s**. If p∤s it is separable = finite étale; the Frobenius term does NOT by itself make it non-étale once a_β≠0. (Does not weaken the concern: you still need all (r,s) incl. p∣s, where the inseparable degree matters. Just: the landscape is cleaner.)

## Q1 — Route A or B? → ROUTE A, NARROWED.
Route B (Weil pairing/Tate module) starts ~from zero: needs E[ℓⁿ]≅(ℤ/ℓⁿ)², Weil pairing, e_N(αP,αQ)=e_N(P,Q)^{deg α}, det(α|E[N])≡deg α (mod N), Frobenius-trace comparison, congruence→integer lift — none present. Route A reuses the shipped V, Vπ=[q], π+V=[t], point-map composition, Wall C, separability/differential, valuation work. So Route A is lighter in THIS project. But do NOT phrase it as "build all of VII.2". Narrowed target:
1. construct rV−s as a genuine degree-bearing isogeny;
2. prove genuine-isogeny EXTENSIONALITY to upgrade the shipped point-map identity to a comorphism identity;
3. use Wall C.
Far less than a full formal-group/reduction theory. Minimal target: β=rπ−s, β^∨=rV−s with genuine comorphisms, β^∨∘β=[N], N=qr²−trs+s². Point-map version + Wall C already in place; remaining gap = comorphism-level duality/double-Vieta.

## Q2 — Is Wall A the crux, or a soft upgrade?
Wall A is genuinely the crux ONLY for the addIsog construction path. There is NO purely formal "point-map dual ⟹ comorphism dual" upgrade unless both sides are already known genuine morphisms.
- **What extensionality CAN do**: if you have a genuine isogeny δ whose point-map is rV−s, then "genuine isogenies are determined by their geometric point-map" upgrades the shipped point-map identity (rV−s)(rπ−s)=[N] to the comorphism identity δ*∘β*=[N]*. This could ELIMINATE much/all of Wall B. (It also collapses π+V=[t], the composition, etc. to pullback identities — but only for genuine isogenies.) Worth proving (cross-cutting shortcut).
- **What it CANNOT do**: create the genuine δ in the first place. If rV−s is only a point-map / raw object without a proven comorphism, extensionality has nothing to compare. Same lesson as the placeholder cleanup. ⟹ **extensionality can replace Wall B, but NOT Wall A.**
- **Alternative to Wall A**: a factorisation/descent (ker β ⊆ ker[N] ⟹ [N] factors through β, giving δ∘β=[N]) = Silverman III.4.11/4.12, essentially another route to duality — elegant but not a cheap rigidity lemma.
Best strategy: (1) formal-group/local arguments to make rV−s genuine; (2) genuine-isogeny extensionality to avoid explicit double-Vieta; (3) Wall C.

## Q3 — Third route avoiding deg(rπ−s)=N? → NO lightweight one.
Leaf 2 gives #E=q+1−t (identifies t) but does NOT bound it; you still need positivity = the QF≥0. Parallelogram law for degree = essentially bilinearity of the degree pairing = normally from duals/Rosati/Weil-pairing, not a simpler primitive. {1,π,V} + point-map Vπ=[q], π+V=[t] do NOT force deg of every rπ−s (degree is a function of the comorphism, not the point-map). Point-count route: deg(rπ−s)=#ker(rπ−s) only for separable (p∤s), replaces by an opaque two-parameter torsion kernel size + still needs the inseparable case — not cheaper. Stepanov/Weil-pairing are genuine third routes but big new developments. **No evident cheap route avoiding deg(rπ−s)=N.**

## Recommended plan (narrow Route A)
1. **Minimal Wall A** (not exact order): `rV−s ≠ 0 ⟹ ord_O((rV−s)*x) < 0` (nonconstancy/transcendence for the addition-pullback construction). State exact pole order separately only if needed later.
2. **Extensionality lemma**: `genuine_isogeny_ext_of_geometric_pointMap_eq (φ ψ : Isogeny E E) (hφ : φ.IsGenuine) (hψ : ψ.IsGenuine) (hpt : ∀ P : E(Kbar), φ P = ψ P) : φ.pullback = ψ.pullback`. Use to upgrade the shipped (rV−s)(rπ−s)=[N] to the comorphism identity, avoiding the huge explicit double-Vieta.
3. **Wall C** to finish.
Keep Route B as fallback only (too much missing). Do NOT chase Q3 unless pivoting to Stepanov (prototype separately; don't delay the current path hoping for an inequality trick from Leaf 2 — there likely is none).

## Final answers
Q1: Route A lighter given shipped assets; Route B starts from too little.
Q2: Wall A is the crux for constructing rV−s via addIsog; extensionality can eliminate Wall B but only after rV−s is genuine; cannot replace Wall A.
Q3: No cheap third route; Leaf 2 gives t but no bound; parallelogram/Cauchy–Schwarz need the same bilinear-degree content; kernel counts for rπ−s opaque + inseparable; Stepanov/Weil-pairing big.
Meta: Commit to narrow Route A — formal-neighbourhood/genuineness for rV−s, then genuine-isogeny extensionality, then Wall C.
