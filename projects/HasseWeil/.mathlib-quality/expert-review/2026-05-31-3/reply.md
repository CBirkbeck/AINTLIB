# Reviewer reply — round 15 (2026-05-31)

## Verdict
Build the divisor route, but keep it **narrow**:
1. define divisor pullback on projective divisors over K̄ from the actual fibre/ramification formula;
2. prove one pulled-back theorem-of-the-square lemma, preferably the scalar-specialised form
   (α+[n])*κ(Q) ∼ α*κ(Q) + [n]*κ(Q);
3. use it to get ŵ(rπ−s) = rV − s.

Do NOT complete the ℤ[π]-conjugation shortcut unless willing to import a different
positivity/determinant theorem. As stated it is circular: identifying conjugate with dual
requires exactly the degree-norm formula being proved.

## Q1 — Divisor pullback (concrete, not opaque)
Over K̄, for a nonconstant isogeny α : E → E':
  α*((Q)) = Σ_{α(P)=Q} e_α(P)·(P),   with e_α(P) = deg_i(α) (constant on fibres),
so α*((Q)) = deg_i(α)·Σ_{P∈α⁻¹(Q)} (P); extend ℤ-linearly.
Lean shape: `ProjectiveDivisor.pullback (α) : ProjectiveDivisor E' →+ ProjectiveDivisor E`,
with `pullback_single` (point formula) verified against the shipped ideal factorisation
(definition = fibre sum on projective points; verification = matches ideal extension).
Minimal lemmas: (1) linearity; (2) pullback of point divisors; (3) deg(α*D)=deg α·deg D;
(4) degree-zero preservation; (5) principal compat α*(div f)=div(f∘α) — may defer full
principal-compat and only prove the special TOS principal divisor for the Hasse target.
Edge cases: the zero map is NOT finite / not the same function-field pullback; split zero
cases. For rπ−s: r=0 or s=0 via shipped partial duals; rπ−s=0 via zero branch; main branch
via nonzero-isogeny pullback.

## Q2 — Minimal proof of σ(Δ_Q)=O (= pulled-back theorem of the square)
The one addition-formula identity is, on E×E with m,p₁,p₂ : E×E → E:
  m*((Q)−(O)) − p₁*((Q)−(O)) − p₂*((Q)−(O)) ∼ 0.
Pull back along (α₁,α₂) : E → E×E to get
  (α₁+α₂)*κ(Q) − α₁*κ(Q) − α₂*κ(Q) ∼ 0,  κ(Q)=(Q)−(O).
To avoid an E×E API, STATE this pulled-back form directly:
  `theorem_of_square_pullback (α₁ α₂) (Q) : IsPrincipal((α₁+α₂)*κQ − α₁*κQ − α₂*κQ)`,
and for Hasse specialise to `theorem_of_square_pullback_mulByInt (α) (n) (Q)` then α=rπ, n=−s.
- Route (b) σ via partial duals (σ(α*((Q)−(O)))=α̂(Q)) is CIRCULAR: computing σ((α₁+α₂)*κQ)
  needs ŵ(α₁+α₂), the very theorem.
- Pure fibre sums fail: (α₁+α₂)⁻¹(Q) is NOT assembled fibrewise from the fibres of α₁,α₂.
- Two proof routes for the pulled-back identity: (1) expose as a TOS primitive; (2) prove
  directly with Miller/chord-tangent functions (recommended if Miller machinery is strong),
  but state the public result as theorem-of-square-on-pullbacks.

## Q3 — ℤ[π]-conjugation shortcut: CIRCULAR
For α=rπ−s want ŵα = [tr α]−α = rV−s. Cayley–Hamilton gives ([tr α]−α)α=[N], but the dual is
characterised by ŵα·α=[deg α]; comparing requires N=deg α — the target QF identity itself.
From α'α=[N] (α'=[tr α]−α) you get deg α'·deg α=N²; even with deg α'=deg α you only get
deg α=|N| — the sign N≥0 is the Hasse inequality in disguise, unobtainable from this algebra.
Warning: calling ℤ[π]≅ℤ[T]/(T²−tT+q) "imaginary quadratic" already imports t²−4q≤0 = the bound.
Non-circular completion needs an independent determinant/norm theorem (Weil pairing / Tate
determinant deg α=det(α|T_ℓE), theorem-of-square, intersection positivity, or Stepanov) — each
at least as heavy as TOS. So: circular unless supplemented by an independent degree/norm theorem.

## Q4 — Scope, estimate, build order
Bounded if specialised; large only if building full product-divisor theory. Build order:
- Step 1: state over K̄; split zero/scalar edge cases first.
- Step 2: define `ProjectiveDivisor.pullback` by fibre sums w/ ramification mult; prove
  pullback_single, linearity, degree formula, degree-zero, maybe principal-compat. = (I).
- Step 3: prove `theorem_of_square_pullback_mulByInt` directly (Miller), NO general E×E API. = (II).
- Step 4: convert to Pic⁰: (α+[n])*[κQ]=α*[κQ]+[n]*[κQ]; since E≅Pic⁰ and κ(Q) generate,
  ŵ(α+[n])=ŵα+[n].
- Step 5: specialise ŵ(rπ)=rV, ŵ[−s]=[−s] ⇒ ŵ(rπ−s)=rV−s; existing QF wiring closes.
Estimate: pullback 150–300; degree/principal 100–250; TOS scalar 250–600; Pic⁰+specialise
100–200. Total ~600–1300 LOC (a full E×E API would be 1500–3000+; avoid). Not rebuilding
intersection theory if scalar-specialised and pulled-back; keep product divisors non-public.

## Recommended final targets
  `pic0_pullback_add_mulByInt (α) (n) : pullbackPic0 (α+[n]) = pullbackPic0 α + pullbackPic0 [n]`
  `dual_add_mulByInt (α) (n) : dual (α+[n]) = dual α + [n]`
  `dual_rFrob_sub_s (r s) : dual (r•π − [s]) = r•V − [s]`
The narrowest honest, non-circular route.
