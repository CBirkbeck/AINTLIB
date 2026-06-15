# Expert-review session state — round 15

- Generated: 2026-05-31
- Audience: same senior arithmetic-geometry reviewer as rounds 1–14
- Goal of brief: build-planning — whole generic bound reduced to ONE predicate (DualAdd = dual additivity III.6.2c); two precise missing ingredients (I) divisor pullback α* on ProjectiveDivisor, (II) addition-formula fibre linkage (σ(Δ_Q)=O). Confirm cleanest build + whether a slicker route (ℤ[π] conjugation) exists.
- Scope: Leaf 1 endgame; DualAdd
- Reply received: true (2026-05-31)
- Reply integrated: true (2026-05-31) — VERDICT: build the narrow divisor route (Steps 2–5);
  Q3 ℤ[π]-conjugation shortcut is CIRCULAR (don't pursue); confirmed vs Silverman III.6.2c + Cor 6.3.

## Questions (§4)
| # | Question |
|---|----------|
| Q1 | Cleanest divisor pullback α* on ProjectiveDivisor: from the shipped ideal factorisation α*(𝔪_Q)=∏𝔪_P^{e_P} (α*((Q)):=Σ_{αP=Q}e_P(P) over F̄), or a primitive ProjectiveDivisor op + degree/κ-compat? Which keeps the TOS proof shortest? |
| Q2 | Minimal proof of σ(Δ_Q)=O (Δ_Q principal) over F̄, avoiding E×E: (a) explicit Miller/chord-tangent f with div f=Δ_Q from the addition formula, (b) σ(Δ_Q) directly via σ(α*((Q)-(O)))=α̂(Q) + a fibre-sum identity, (c) other? What's the ONE addition-formula divisor identity? |
| Q3 | ℤ[π]-conjugation shortcut: non-circular proof of α̂=[tr α]−α on ℤ[π] (⟹ DualAdd, additive for free) from Cayley-Hamilton + α̂α=[deg α] + something pinning deg α WITHOUT assuming deg=N? Or provably circular ⟹ divisor build unavoidable? |
| Q4 | Scope/order: is (I)+(II) a BOUNDED build on the Miller/κ-divisor machinery (estimate?), or does it rebuild intersection/divisor theory? Cleanest build order? |

## Shipped non-circular
E≅Pic⁰, Pic⁰ dual + α̂α=[deg], hnat (imperfect-field relNorm=comap), π̂=V, ŵ(rπ)=rV (non-circular, deg(rπ)=r²q known), [n]^=[n], Miller machinery (miller_hypothesis_holds_allChar) + κ-divisor additivity, DualAdd⟺σ(Δ_Q)=O certification, Cayley-Hamilton (rπ−s)²−[rt−2s](rπ−s)+[N]=0.

## Missing ingredients
(I) ProjectiveDivisor pullback α* (only pushforward + κ exist); (II) addition-formula fibre linkage σ(Δ_Q)=O. Both char-free over F̄, both absent. Cannot shortcut via group law / uniqueness / image-side TOS / Weil pairing (verified).

## References
Silverman III.6.1-6.3 (dual, III.6.2(b) pullback-as-divisor, III.6.2(c) char-0 additivity p.84, Ex 3.31 char-p Weil-pairing — avoided), III.3.4/3.5 (E≅Pic⁰, Abel), III.4.10 (e=deg_i), Ex 3.32 (Cayley-Hamilton). Project: Curves/{Miller,EffectiveSumReduce,ProjectiveDivisor,Divisors}, AdditionPullback/*, Pic0/*.
