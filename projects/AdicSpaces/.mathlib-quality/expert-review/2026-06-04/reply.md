# Reviewer reply — Lemma 7.54 (2026-06-04)

## Verdict
Clean self-contained route to 7.54 in the Tate case, close to Huber [Hu3] Lemma 2.6.
Two-stage: (1) refine by finitely many NORMALISED rational subsets W_i=R(T_i/s_i) with
1∈T_i and s_i∈T_i; (2) Huber product trick: P={∏tᵢ : tᵢ∈Tᵢ}, S={∏tᵢ : tᵢ∈Tᵢ, and tᵢ=sᵢ
for ≥1 i}; then (R(S/s))_{s∈S} is the T-generated refinement.

Tate de-risk: replace Huber's [H1,2.6.ii] local-normalisation by Wedhorn Cor 7.32 (given
x∈R(T/s), choose top-nilp unit π with |π(x)|<|s(x)|, shrink to numerator set containing 1).

Recommended: rational basis + Cor 7.32 normalisation + finite subcover + Huber product trick
+ Cor 7.53. No need to formalise all of [Hu3].

## Q1 (elementary route) — YES. Steps:
Step1 (normalised nbhds): x∈V_j → R(T/s)⊆V_j; Cor 7.32 on {x} gives unit π, |π(x)|<|s(x)|;
set s':=sπ⁻¹, T':={1,s'}∪{π⁻¹t:t∈T}. Then x∈R(T'/s'), R(T'/s')⊆R(T/s)⊆V_j, 1∈T', s'∈T'.
Quasi-compact → finite subcover W_i=R(T_i/s_i)⊆V_{j(i)}, 1,s_i∈T_i.
Step2 (product): P={∏tᵢ}, S={∏tᵢ : tᵢ=sᵢ some i}.
Step3 (product identity): R(P/(t₁⋯tₙ)) = ⋂ᵢ R(Tᵢ/tᵢ). [proof: cancel nonzero factors]
Step4 (S-cover covers X): each 1∈Tᵢ → Tᵢ generates A → (R(Tᵢ/t))_{t∈Tᵢ} covers (Cor 7.53);
for x, pick i₀ with x∈R(T_{i₀}/s_{i₀}), set t_{i₀}=s_{i₀}, others t_i with x∈R(Tᵢ/tᵢ);
p=∏tᵢ∈S, x∈R(P/p) by product identity. So X=⋃_{s∈S}R(P/s).
Step5 (S·A=A): R(P/s) cover → no common zero → Cor 7.53 → S·A=A.
Step6 (R(P/s)=R(S/s) for s∈S): S⊆P gives ⊇; converse via picking s'∈S with x∈R(P/s'),
v(s')≤v(s), v(p)≤v(s') ∀p∈P, so v(p)≤v(s), x∈R(P/s).
Step7 (refinement): s=∏tᵢ∈S, pick i with tᵢ=sᵢ; R(P/s)⊆R(Tᵢ/sᵢ)=W_i⊆V_{j(i)}; R(S/s)=R(P/s)
⊆V_{j(i)}. Output S={f₀..fₙ}, S·A=A, R(S/fᵢ)⊆V_j.

## Q2 (avoid 7.54?) — NO, don't avoid; prove it. Avoid only the FULL [Hu3] generality; Tate
Cor 7.32 replaces Huber's local normalisation. A "Laurent refinement" alternative is stronger
and harder.

## Q3 ([Hu3] 2.6 skeleton) — exactly the above. Lean split:
exists_finite_normalized_rational_refinement (finite R(Tᵢ/sᵢ), 1∈Tᵢ, sᵢ∈Tᵢ, ⊆ cover member)
product_rationalOpen_eq_iInter (R(P/∏tᵢ)=⋂ᵢR(Tᵢ/tᵢ))
product_distinguished_cover (⋃_{s∈S}R(P/s)=Spa A)
span_top_of_distinguished_products (S·A=A via Cor 7.53)
rationalOpen_product_eq_distinguished (R(P/s)=R(S/s) for s∈S)
lemma_754

## Q4 (absolute vs relative) — ABSOLUTE over Spa A suffices at the top (apply once to the cover
of X). 8.34 used relatively after restriction (apply same absolute lemma to O_X(U), transport
via Spa O_X(U) ≅ U). Lean: lemma_754_absolute (A) + lemma_754_relative (D) [apply absolute to
presheafValue D + transport].

## Secondary
- Cor 7.32 enough for the normalisation; no full characteristic-subgroup argument.
- 8.34(ii) dominating unit IS Cor 7.32 (Y quasi-compact, s≠0 on Y → unit π, |π|<|s| on Y).
- 8.33 / A.3(3): formalisation work, not uncertainty — keep current plan.

## Manager message: implement in 2 stages (normalised refinement via Cor 7.32 + product trick).
Absolute over Spa A suffices; add relative wrapper over presheafValue D later.
Ref: Huber, A generalization of formal schemes…, [Hu3] Lemma 2.6.
