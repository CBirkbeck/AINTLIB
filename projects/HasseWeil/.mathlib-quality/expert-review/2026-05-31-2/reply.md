# Reviewer reply — round 14 (2026-05-31)

## Verdict
Yes: move hmul to F̄ in DIVISOR/Pic⁰ form, NOT ideal-extension over 𝔽_q. CORRECTION: "deg 0 + sum O ⟹ principal" needs the FULL Abel theorem / Pic⁰ iso (D∈Div⁰ ∧ σ(D)=O ⟺ D principal), NOT merely injectivity of κ:E→Pic⁰ (injectivity only gives (P)-(O) principal ⟹ P=O). If DivZeroReduce/Abel proves the full statement, the target is sound; if only Point.toClass injectivity, NOT enough.

## Q1 — divisor/point form over F̄ right? YES.
Target: [(α₁+α₂)*D]=[α₁*D]+[α₂*D] in Pic⁰(E_F̄) for D∈Div⁰. Over F̄ all fibre points rational ⟹ divisor sums expressible in the group. BUT the proof still has theorem-of-the-square content (it's the theorem of square pulled back along (α₁,α₂):E→E×E) — NOT just (α₁+α₂)(P)=α₁(P)+α₂(P). That point-map identity alone does NOT give a fibre bijection.

## Q2 — sums-to-O immediate? NO (the main subtlety).
σ(α*((Q)-(O)))=α̂(Q) (dual transported through κ), so σ(Δ_Q)=ŵ(α₁+α₂)(Q)−ŵ(α₁)(Q)−ŵ(α₂)(Q). Proving σ(Δ_Q)=O is EQUIVALENT to the dual additivity itself — theorem of the square, not a trivial fibre calc. Fibres of a sum of homs are NOT built fibrewise from separate fibres. Minimal lemma = the PULLED-BACK theorem of the square (α₁+α₂)*L≅α₁*L⊗α₂*L for L∈Pic⁰:
  theorem_of_square_pulled_back (α₁ α₂)(D:Div0 E_Kbar) : IsPrincipal((α₁+α₂)*D − α₁*D − α₂*D)
Narrow to scalar: theorem_of_square_pulled_back_mulByInt (α)(n)(D) : IsPrincipal((α+[n])*D − α*D − [n]*D), specialise α=rπ, n=−s. Self-contained without E×E AS A STATEMENT, but the PROOF still has theorem-of-square content — formalise via explicit EC divisor identities / Miller functions + existing Abel/DivZeroReduce, NOT a one-line group-law consequence; don't expose E×E as public API.

## Q3 — descent? Probably NOT needed.
If the consumer works over E(F̄) + degree base-change invariance deg(β_F̄)=deg(β), then ŵ(rπ−s)=rV−s as geometric point maps ⟹ [deg(rπ−s)]=[N] on E(F̄) ⟹ deg=N (geometric injectivity of [m]). Need degree base-change invariance, NOT descent of the theorem-of-square identity. Stay geometric over F̄. (If you DO want 𝔽_q-morphism equality: f*=g* ⟺ (f_F̄)*=(g_F̄)* under faithfully-flat 𝔽_q→F̄ — but avoid unless needed.)

## Q4 — κ group-iso shortcut? NO.
α↦κ⁻¹∘α*∘κ is contravariantly functorial under COMPOSITION, but (α₁+α₂)*=α₁*+α₂* on Pic⁰ is an ADDITIONAL theorem (= theorem of the square). κ(P+Q)=κ(P)+κ(Q) does NOT imply (α₁+α₂)*κ(Q)=α₁*κ(Q)+α₂*κ(Q). Best shortcut = the scalar-specialised theorem (α+[n])*L≅α*L⊗[n]*L ⟹ ŵ(α+[n])=α̂+[n] ⟹ ŵ(rπ−s)=rV−s.

## Recommended next formal target
  Pic0.pullback_add_mulByInt_Kbar (α)(n)(D:Div0 E_Kbar) : classOf((α+[n])*D)=classOf(α*D)+classOf([n]*D)
  → dual_add_mulByInt_Kbar (α)(n) : dual(α+[n])=dual α+[n]
  → dual_rFrob_sub_s_Kbar (r s) : dual(r•π−[s])=r•V−[s]
Narrower than full arbitrary dual additivity; avoids Weil pairing.

## Final answers
Q1: divisor/Pic⁰ over F̄ right (not ideal classMap over 𝔽_q); need FULL Abel (kernel-of-sum), not just κ injectivity.
Q2: sums-to-O NOT immediate; it's theorem-of-square content; avoid E×E API by proving the pulled-back form directly on E (specialise to α+[n]).
Q3: no descent if consumer over E(F̄) + degree base-change invariance; else faithfully-flat descent.
Q4: κ group-iso not enough; missing = additivity of Pic⁰ pullback (theorem of square); lightest = scalar-specialised.
