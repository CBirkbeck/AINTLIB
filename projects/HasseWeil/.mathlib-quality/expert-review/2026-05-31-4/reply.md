# Reviewer reply — round 16 (2026-05-31)

## Verdict (nuanced)
The round-16 concern is **substantially correct**: Silverman's specific bivariate proof of III.6.2(c),
as written, does NOT become valid merely by replacing the constant field with F̄ — the field used is
K(E₁)=F̄(x₁,y₁), still imperfect in char p (x₁^{1/p}∉F̄(x₁,y₁)). So the "F̄ is perfect" fix does NOT
discharge the footnote. BUT this does NOT make dual additivity "Weil-pairing-only": the theorem of the
square/cube is characteristic-free in the Picard-functor / line-bundle setting. What fails is the
particular elementary divisor-FUNCTION proof, which relies on prior EC results over a perfect base then
changes base to the imperfect K(E₁).
⇒ If using the divisor/TOS route in char p, prove it as a genuine Picard/pulled-back-TOS lemma, NOT by
replaying Silverman's p.83–84 bivariate function-field proof verbatim. Given the infra gaps, Weil/Tate
may now be more PREDICTABLE, but not necessarily shorter.

## Q1 — char-free over F̄? As written, NO.
Reading of footnote is right; replacing K by F̄ does not make K(E₁) perfect. HOWEVER the failure is NOT
the valuation identity ord_{P₁}(f)=e_φ(P₁) itself — valuation pullback formulas ARE valid in inseparable
extensions; inseparability is precisely measured by ramification indices and absorbed into e_φ(P). The
problem is that Silverman's proof invokes prior EC/divisor results over the new base K(E₁) whose setup
assumed a perfect base. So: bivariate proof not directly reusable over F̄ (K(E₁) imperfect); but the
THEOREM is char-free if proved through Picard/line-bundle machinery (or the Weil pairing). Not
"char-p-only via Weil"; rather "Silverman's elementary bivariate proof is char-0/perfect-base-only as
written; the char-free replacement is theorem-of-square/Picard, or the Weil pairing."

## Q2 — Weil/Tate now more mechanical? More LINEAR/isolated, not obviously shorter.
Divisor route now has two real gaps: (1) two isogeny notions unbridged; (2) no usable finite-fibre
apparatus for Σ_{αP=Q}e_α(P)(P), and e_α(P)=deg_i α not yet a usable lemma. So it's no longer the
600–1300 LOC target — closer to a medium Picard/fibre development. Weil/Tate has a clearer dependency
list (E[ℓⁿ]≅(ℤ/ℓⁿ)², Weil pairing e_{ℓⁿ}, bilinear+nondegenerate, e(φP,Q)=e(P,φ̂Q), equality on all ℓⁿ
⇒ equal endos). Division polys present but E[ℓⁿ]≅(ℤ/ℓⁿ)² and the pairing ABSENT — still substantial.
ONE finite m insufficient; need all ℓⁿ / Tate injectivity. ⇒ Treat Weil/Tate as a parallel/fallback;
not automatically lighter. If E[ℓⁿ]≅(ℤ/ℓⁿ)² is quick, Weil may become preferable; else pulled-back TOS
stays competitive.

## Q3 — Frobenius-specific shortcut? Still NO non-circular one.
V π=πV=[q], π+V=[t] give the candidate conjugate rV−s, but identifying [rt−2s]−(rπ−s) as the DUAL needs
N=deg(rπ−s) (the QF identity). Settled circular (Cor 6.3 uses III.6.2c). π*=q-power Frobenius
computation would amount to proving rV−s satisfies the universal dual property for rπ−s ⇒ again needs the
signed degree/determinant. Formal group detects separability/local leading terms but not the global norm
on ℤ[π] without big height/kernel theory. The Frobenius structure gives the candidate, not the proof.

## Q4 — divisor route: AVOID a public fibre-sum API. Prove the pulled-back TOS directly.
Target: `theorem_of_square_pullback_mulByInt (α)(n)(Q) : IsPrincipal((α+[n])*((Q)−(O)) − α*((Q)−(O)) −
[n]*((Q)−(O)))` or the Pic⁰ form `pullbackPic0 (α+[n]) = pullbackPic0 α + pullbackPic0 [n]`. Internally
use Miller/chord-tangent functions + Abel, NOT a public finite-fibre API — prove only the instance
needed. A genuine fibre-sum def forces finite fibres + ramification mult + e_α=deg_i + bridging both
isogeny notions + pullback of point divisors (all the missing/parametric pieces).
MINIMAL BRIDGE (one, not a refactor): `pullbackDivisor_eq_of_pointMap_eq (α β)(h: ∀P, α.pointMap P =
β.pointMap P) : α.pullbackDivisor = β.pullbackDivisor`, or narrower
`pullback_kappa_eq_of_pointMap_eq : α*((Q)−(O)) = β*((Q)−(O))`.
INTERNAL PROOF: the divisor-form TOS for the addition map on E×E,
`m*((Q)−(O)) − p₁*((Q)−(O)) − p₂*((Q)−(O)) ∼ 0`, pulled back along (α,[n]); to avoid an E×E API,
construct the rational function directly from the addition formula. Keeps it bounded.

## Strategic recommendation
- Do NOT rely on "F̄ fixes perfectness" (round-16 correction is right).
- Do NOT declare TOS impossible in char p (char-free in the right Picard framework; only Silverman's
  particular proof isn't).
- Route 1 (Picard/TOS, pulled-back + scalar-specialised over F̄): target (α+[n])*=α*+[n]* on Pic⁰; do
  NOT replay Silverman's bivariate proof. RECOMMENDED given shipped Pic⁰/Miller.
- Route 2 (Weil/Tate): target e_{ℓⁿ}((φ+ψ)P,Q)=e_{ℓⁿ}(P,(φ̂+ψ̂)Q) ∀n + nondegeneracy/Tate injectivity.
  More modular, larger if no Weil pairing.
- RECOMMENDATION: still try Route 1 in the scalar-specialised pulled-back form, with a STRICT CHECKPOINT
  — if you cannot formulate+prove the pulled-back TOS WITHOUT full fibre theory in one focused slice,
  switch to Weil/Tate. Do NOT sink more work into Silverman's bivariate proof over K(E₁) as written.
