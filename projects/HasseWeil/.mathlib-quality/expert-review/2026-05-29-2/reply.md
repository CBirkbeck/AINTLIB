# Reviewer reply — round 8 (2026-05-29)

## Short answer
Use **base change to F̄_q** and apply the separable-isogeny fibre-count theorem THERE (Silverman III.4.10a). Do NOT prove the K-level residue-degree (f_P=1) statement first unless the closed-point dictionary is needed elsewhere.

Confirms the correction: for the composite f = (1−π)*x : E → P¹, the places lie over the ∞-place of K(x) and kernel points have e=2 (x has a double pole at O). "separable ⇒ e_P=1" applies to the isogeny 1−π : E→E, NOT to the degree-2 composite x∘(1−π). The clean route:
deg(1−π) = deg((1−π)_K̄) = #ker((1−π)_K̄) = #E(F_q). Avoids residue degrees entirely.

## Q1 (closed-point ↔ Frobenius-orbit dictionary)
Correct IF you stay at K-level. Statement: a closed point P of E/F_q of residue degree d ↔ a Frobenius orbit of size d in E(F̄_q); all geometric points over P fixed by q-Frobenius ⟹ orbit size 1 ⟹ d=1. For 1−π: (1−π)(Q)=O ⟺ Q=π(Q), so every geometric point in the fibre is Frobenius-fixed ⟹ every closed point has residue degree 1. BUT formalising the dictionary (place residue field κ(v)=F_{q^d}; embeddings κ(v)↪F̄_q give geometric points; q-Frobenius transitive with orbit size d; all-fixed ⟹ d=1) is a real mini-development. Do NOT make it primary unless needed elsewhere.

## Q2 (base change to F̄_q — RECOMMENDED)
Work over K̄=F̄_q; residue degrees disappear. #(1−π)_K̄⁻¹(O) = deg_s((1−π)_K̄); separable ⟹ deg_s = deg; degree invariant under base change ⟹ = deg(1−π). Identify the fibre: (1−π)_K̄(P)=O ⟺ P=π(P) ⟺ P∈E(F_q) (coordinate-wise x^q=x, y^q=y ⟺ x,y∈F_q).

Formal plan (4 lemmas):
- `degree_oneSubFrob_eq_baseChange_degree`: deg(1−π) = deg((1−π).baseChange K̄)
- `oneSubFrob_baseChange_isSeparable`: ((1−π).baseChange K̄).IsSeparable
- `algClosed_fiber_card_eq_sepDegree`: #{P : (W.baseChange K̄).Point // ((1−π).baseChange K̄).toPointMap P = 0} = ((1−π).baseChange K̄).sepDegree
- `oneSubFrob_baseChange_fiber_eq_base_points`: {P // fibre} ≃ W.toAffine.Point
Key fixed-field lemma: `frobenius_fixed_iff_mem_baseField (a : K̄) : a ^ card K = a ↔ ∃ b : K, algebraMap K K̄ b = a` (elementary: X^q−X has exactly the q elements of K as roots). Over K̄ all geometric residue fields are K̄, so f_P=1 vanishes as an issue.

## Q3 (Silverman statement)
III.4.10(a) via II.2.6(b): for an isogeny φ:E1→E2, every fibre has deg_s φ geometric points (II.2.6b generic fibre = deg_s; translation gives bijection between fibres; so every fibre; separable ⟹ deg_s=deg). Stated over alg-closed field (or after base change) — that's why no residue-degree step appears (counted geometrically). For 1−π: #ker(1−π)=deg_s(1−π)=deg(1−π); finite-field part: ker(1−π)(K̄)=E(F_q). Clean Silverman-faithful plan: base change to K̄; apply III.4.10a to (1−π)_K̄; identify kernel with E(F_q); descend degree.

## On the shipped pointCount ≤ deg(1−π)
Keep it as a sanity check (consistent with the composite x∘(1−π) contributing 2 at each rational kernel point: 2#E(F_q) ≤ 2 deg). But do NOT force the rest through the K(f)-place-count framework — the reverse direction ("no extra non-rational closed points in the pole fibre") is awkward at K-level, clean geometrically. Base change avoids it.

## Minimal Lean implementation path
1. `fixed_by_card_frobenius_iff_mem_range (a : AlgebraicClosure K) : a ^ card K = a ↔ ∃ b : K, algebraMap K (AlgebraicClosure K) b = a`
2. `baseChange_point_fixed_by_frobenius_iff (P : (W.baseChange (AlgebraicClosure K)).Point) : frobenius_q_point P = P ↔ ∃ P0 : W.toAffine.Point, includePoint P0 = P` (cases P=O / affine, lemma 1 on coords)
3. `baseChange_oneSubFrobenius_pointMap` (or just the fibre-over-O form: `…toPointMap P = 0 ↔ frobenius_q_point P = P`)
4. compose with alg-closed fibre count ⟹ `sepDegree_oneSubFrob_eq_pointCount`.

## Final recommendation (one sentence)
Prove #ker((1−π)_K̄)=deg(1−π) over K̄, then ker((1−π)_K̄)=E(F_q) by the coordinate fixed-field lemma (a^q=a ⟺ a∈F_q). Base-change route is cleanest and closest to Silverman III.4.10(a); the K-level residue-degree route is correct but needs the closed-point/orbit dictionary (not the shortest path).
