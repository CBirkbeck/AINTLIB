# Reviewer reply — round 13 (2026-05-31)

## Executive verdict
Do NOT jump to the Weil pairing first. The lightest route, given what you have built, is to prove **dual additivity through Pic⁰ functoriality / theorem of the square**, specialised to the Frobenius plane: `ŵ(rπ−s)=rV−s`. The Ex 3.31 Weil-pairing proof is valid char-p but not the smallest formalisation (needs torsion structure, nondegenerate pairings, a full ℓⁿ-tower / Tate-module injection). You already have E≅Pic⁰, divisor/class-group functoriality, full-degree push-pull, and the partial duals π̂=V, [n]^=[n], (rπ)^=rV. The missing theorem is exactly the additivity of pullback on Pic⁰:
  (φ+ψ)*|_Pic⁰ = φ*|_Pic⁰ + ψ*|_Pic⁰  (theorem of the square/cube in EC form, characteristic-free).

## Q1 — Is the Weil pairing the lightest? NO.
The char-p obstruction is not that dual additivity is Weil-pairing-dependent; it's that ONE particular divisor/function proof over an imperfect function field fails. The char-free conceptual proof: for an abelian variety, the dual is additive because pullback of line bundles in Pic⁰ satisfies the theorem of the square `(f+g)*L ≅ f*L ⊗ g*L` for L∈Pic⁰; for EC this is ŵ(f+g)=f̂+ĝ, works in all characteristics.
**On base-change (careful!):** don't rely on "perfect closure fixes everything" (function fields stay transcendental/imperfect in char p; a constructed rational function f over a huge field doesn't descend automatically). Safer: (1) prove the line-bundle theorem of the square over an algebraically closed field using your Pic⁰/class-group machinery; (2) apply after a faithful base extension if needed; (3) descend EQUALITY OF MORPHISMS / isogeny point maps (checkable after faithfully-flat field extension), NOT a constructed function. Prove an equality IN Pic⁰ or of morphisms after base change.
Verdict: the Weil pairing is not the only char-p route; the lighter route for your codebase is theorem-of-square / Pic⁰-pullback additivity. The obstruction is a proof-method issue, not a deeper char-p failure.

## Q2 — Single instance, more lightly? YES.
Target the scalar-additivity lemma (narrower than full additivity):
  dual_add_mulByInt (α : End E) (n : ℤ) : dual (α + mulByInt n) = dual α + mulByInt n
then specialise α=rπ, n=−s. At the Pic⁰ level the right theorem is:
  pic0_pullback_add (φ ψ) : pullbackOnPic0 (φ+ψ) = pullbackOnPic0 φ + pullbackOnPic0 ψ
or the scalar-specialised `pic0_pullback_add_mulByInt (φ) (n)`. Since ŵα = κ⁻¹∘α*∘κ, this gives ŵ(α+[n])=α̂+[n] immediately.
**Theorem of the cube in your class-group formulation:** in line-bundle language `m*L ≅ p₁*L⊗p₂*L` on E×E for L∈Pic⁰(E), m:E×E→E addition; pulling back along (φ,ψ):E→E×E gives `(φ+ψ)*L≅φ*L⊗ψ*L`. In class-group language: `[(φ+ψ)*D]=[φ*D]+[ψ*D]` in Pic⁰ for degree-0 D. The clean theorem lives on E×E; if you have no product-curve/divisor infrastructure, prove the SPECIALISED pullback theorem for maps out of E directly:
  divisorClass_pullback_add (φ ψ) (D : Div0 E) : classOf((φ+ψ)*D) = classOf(φ*D) + classOf(ψ*D)
This is the theorem of the square pulled back to E, avoiding a full product-curve API. Try this BEFORE the Weil pairing.

## Q3 — If Weil pairing required, how much? Substantial.
Minimal route: one auxiliary ℓ≠p (ℓ=2 if p≠2, ℓ=3 if p=2); develop E[ℓⁿ]≅(ℤ/ℓⁿ)² for ALL n; define e_{ℓⁿ}; prove bilinear/alternating/nondegenerate + dual compatibility e(φP,Q)=e(P,φ̂Q); then for φ+ψ + nondegeneracy + Hom→End(T_ℓ) injectivity. NOT tiny (500–1500 lines). Division polynomials give torsion cardinalities but NOT the pairing/functoriality/Tate injectivity. **One m is NOT enough** (a nonzero isogeny can kill a finite subgroup; need all ℓⁿ / the Tate module). More expensive than the theorem-of-square identity.

## Q4 — Avoid dual additivity entirely? No.
Cayley-Hamilton π²−[t]π+[q]=0 + point identities (π+V=[t], Vπ=[q]) do NOT determine deg(rπ−s) unless you know rV−s is the dual of rπ−s (or have a determinant-degree theorem). The composition (rV−s)(rπ−s)=[N] only gives deg·deg=N² (no sign, no value). No cheap endgame; still need (1) Pic⁰ dual additivity / theorem of square, (2) Weil pairing / Tate determinant, or (3) Stepanov (a different proof). Given your assets, (1) is lightest.

## Recommended next target
ONE new critical theorem, not a Weil-pairing branch:
  Pic0.pullback_add_on_endomorphisms (φ ψ) : pullbackPic0 (φ+ψ) = pullbackPic0 φ + pullbackPic0 ψ
or scalar-specialised `Pic0.pullback_add_mulByInt (φ) (n)`. Then:
  dual_add_mulByInt (φ) (n) : dual (φ+[n]) = dual φ + [n]
  dual_rFrob_sub_s : dual (r•π − [s]) = r•V − [s]
This is exactly the residual and should close the Hasse QF branch. If `Pic0.pullback_add...` demands product-line-bundle machinery, prove the pulled-back form directly for maps E→E.

## Final answers
Q1: Weil pairing NOT lightest; theorem-of-square / Pic⁰ pullback additivity is the natural next target, works in char p.
Q2: Yes — scalar-specialised Pic⁰ pullback additivity ŵ(rπ−s)=rV−s; lighter than full Weil pairing and than full arbitrary additivity.
Q3: If Weil pairing: one ℓ≠p but the full ℓⁿ tower / Tate injection; one m insufficient; substantial.
Q4: Cayley-Hamilton + point-level don't avoid the degree-norm formula; still need dual additivity or determinant-degree.
