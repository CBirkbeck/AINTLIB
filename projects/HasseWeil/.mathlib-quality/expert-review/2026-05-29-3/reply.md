# Reviewer reply — round 9 (2026-05-29)

## Executive verdict
Pivot Leaf 2 to a function-field / translation-embedding proof (R2), but implement it as an EMBEDDINGS-CLASSIFICATION theorem, NOT "prove IsGalois first". Prove:
  Hom_{(1−π)*K(E)}(K(E), Ω) ≅ ker(1−π) = E(F_q)   (Ω = alg closure of M := (1−π)*K(E))
Since L/M is finite separable, #Hom_M(L,Ω) = [L:M] = deg(1−π). So deg(1−π) = #E(F_q). Normality follows AFTER (all embeddings land back in K(E) as translations) — do not prove it first.

## Q1 — Is R2 right?
Yes, with a warning. Standard: for a separable isogeny φ:E1→E2, translations by ker φ identify ker φ with Gal(K(E1)/φ*K(E2)). For γ=1−π, ker is K-rational (ker(1−π)(K̄)=E(F_q)), so each k gives a K-auto τ_k* : K(E)≃_K K(E) fixing γ*K(E) (since γ(P+k)=γ(P)+γ(k)=γ(P)). WARNING: normality is NOT automatic from kernel K-rationality — that only gives γ*K(E) ⊆ K(E)^{ker γ}; equality (= translations account for ALL embeddings) is exactly #ker=deg, circular if proved by cardinality. So: (1) construct translations as autos fixing γ*K(E); (2) classify ALL embeddings over γ*K(E) as these translations; (3) count by finite separability. Derive IsGalois AFTER, not before.

## Q2 — Embeddings route without a generic-fibre theorem (RECOMMENDED)
L=K(E), M=γ*K(E)⊆L. γ=1−π separable ⟹ L/M finite separable ⟹ #Hom_M(L,Ω)=[L:M]=deg γ. Classify: let P_gen=(x,y), x,y∈L. For σ:L→Ω over M, Q_σ=(σx,σy)∈E(Ω); σ fixes M=γ*K(E) ⟹ fixes γ*x,γ*y ⟹ γ(Q_σ)=γ(P_gen) ⟹ T_σ:=Q_σ−P_gen ∈ ker γ = E(F_q) ⟹ σ = τ_{T_σ}*. Conversely each T∈E(F_q) gives an embedding via τ_T*. So Hom_M(L,Ω) ≅ E(F_q), hence deg γ = [L:M] = #Hom_M(L,Ω) = #E(F_q). This is the #ker=deg theorem. No generic fibre, no CoordHom, no upfront normality. Lean target: `(L →ₐ[M] Ω) ≃ (isogOneSub_negFrobenius W hq).kernel`, or `Function.Bijective (fun T : γ.kernel => (translationAlgEquiv T).restrictScalars M)`.

## Q3 — If R1: lightest CoordHom-free fibre theorem
Same embeddings argument in geometric language: finite separable L/M ⟹ geometric generic fibre has [L:M] points (= M-embeddings L→Ω); then translation invariance of fibres moves the generic count to the O-fibre. Still needs a projective morphism/fibre interface (places, projective points, evaluation) — essentially the missing generic-fibre theorem. For γ=1−π the direct embeddings-as-translations proof is narrower and cheaper.

## Meta — Is R2 the real content?
Yes. The two previous routes hit the same wall because they used a theorem designed for affine coordinate-ring maps, but 1−π is a projective morphism whose pullback of affine x has poles at affine kernel points — so NO CoordHom exists, over K or K̄. The function-field replacement is: finite separable extension + classify embeddings by translations. Avoids the false affine-regularity requirement entirely.

## Implementation plan (R2, 5 steps)
1. translationAlgEquiv (T : W.toAffine.Point) : K(E) ≃ₐ[K] K(E) — via addition formulas + inverse τ_{−T} (projective auto; function-field formulas suffice, no global affine CoordHom). + group hom: translationAlgEquiv (T1+T2) = (translationAlgEquiv T2).trans (translationAlgEquiv T1) (contravariant).
2. translation fixes γ*K(E): for T∈ker γ, τ_T*(γ*f)=γ*f.
3. translation embeddings distinct (injective in T).
4. classify arbitrary M-embeddings σ as translations: Q_σ=(σx,σy), γ(Q_σ)=γ(P_gen), Q_σ−P_gen∈ker γ=E(F_q), σ=τ_{T_σ}*. (THE core theorem.)
5. count: #(L→_M Ω)=[L:M] (finite separable), conclude deg γ = #ker γ = #E(F_q). Avoids IsGalois as prerequisite.

## Traps
1. Generic point over M vs L: P_gen lives over L; after σ:L→Ω, Q_σ over Ω; interpret Q_σ−P_gen over a common extension (use the σ-inclusion for P_gen).
2. Addition formulas at exceptional cases: use projective point/group-law API, not affine slopes.
3. Kernel over Ω = E(F_q): reuse the fixed-field coordinate lemma (a^q=a ⟺ a∈F_q) in any alg-closed extension containing K.
4. Separability: L/M finite separable from 1−π separable — make it an explicit input.
5. Aut vs Hom: count embeddings into an alg closure FIRST; don't count automorphisms until normality proven (avoids circular normality).

## One-line answers
Q1: R2 standard+appropriate; normality NOT automatic — prove embeddings-are-translations, then normality follows.
Q2: No route avoids both generic fibres and translations; best avoids generic fibres AND normality by counting finite-separable embeddings and classifying as translations.
Q3: CoordHom-free fibre theorem buildable from embeddings, but heavier than the direct translation-embedding classification for this map.
Meta: Yes — the real Leaf 2 content is the translation-automorphism / embedding classification; state it as embeddings classification, not upfront IsGalois.
