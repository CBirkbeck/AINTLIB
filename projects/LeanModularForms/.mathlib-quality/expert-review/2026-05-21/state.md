# Expert-review session state

- Generated: 2026-05-21
- Audience: AI mathematical reviewer, no repo/file access — pure mathematics
- Goal of brief: strategic guidance on the refactor + the construction blocker (landing the Hecke-ring → endomorphism map in the nebentypus χ-eigenspaces)
- Scope: the Hecke-ring → endomorphism-algebra construction and its extension to arbitrary nebentypus χ; SMO only as downstream consumer
- Reply received: true (date: 2026-05-21)
- Reply integrated: true (date: 2026-05-21) — verdict: twisted-action transport route; see integration.md

## Questions in the brief

| # | Question (verbatim from §9 of the brief) |
|---|------------------------------------------|
| Q1 | How to structure the refactor: cleanest way to organise "Hecke operators as the image of a ring hom into End(M_k(Γ₁(N),χ))"? Source = 𝕋(Γ₀(N)) with nebentypus twist, or a genuine Γ₁(N) Hecke ring? Bridge T_n = Φ_χ(T(D_n)) coset-by-coset or via generators-and-relations / universal property? |
| Q2 | How to land the map in the χ-spaces (blocker 8.1): cleanest route to (T(D)f)|_k γ = χ(d_γ)·T(D)f for general χ? Is the DS Prop 5.2.1 representative-permutation/determinant-character argument the right one, with pitfalls at p∣N? Or avoid it by identifying the holomorphic part of V_χ with M_k(Γ₁(N),χ) and transporting the function-level hom (Result 5.4)? |
| Q3 | Generality of the source ring: is it correct/standard that the SAME commutative 𝕋(Γ₀(N)) acts on every χ-eigenspace simultaneously (χ entering only via the action, not the ring)? Any subtlety forcing a χ-dependent or Γ₁(N)-level algebra? |
| Q4 | Operators at bad primes p∣N (U_p): does the equivariance argument and homomorphism property go through uniformly for these double cosets, or do they need separate handling? |
| Q5 | Is "ring hom 𝕋(Γ₀(N)) → End(M_k(Γ₁(N),χ))" the right primary abstraction to build newform/multiplicity-one theory on, or would the reviewer organise the Hecke action differently (one big algebra on ⊕_χ; or 𝕋 on M_k(Γ₁(N)) with nebentypus decomposition derived after)? |

## Ticket-board snapshot at brief time

No formal `/develop` ticket board for this refactor yet. Informal milestone plan (4 stages):
1. Construct Φ_χ : 𝕋(Γ₀(N)) →+* End(M_k(Γ₁(N),χ)) for general χ  [THIS MILESTONE; blocked on §8.1]
2. Bridge: prove concrete T_n = Φ_χ(T(D_n)) (general n, general χ, incl. p∣N)
3. Collapse: re-derive operator commutativity/multiplicativity as ring corollaries
4. Consume: route eigenform theory + strong multiplicity one through Φ_χ

Existing infrastructure (the parallel "islands"): abstract Hecke ring 𝕋(Γ₀(N)) is CommRing (anti-involution); ring homs exist for level-1 SL₂, Γ₀(N), and trivial-χ on Γ₁(N) (heckeRingHomCharSpaceOne); a general-χ ring hom exists into a raw function submodule (twistedHeckeRingHomFunction) but not into M_k(Γ₁(N),χ). Concrete operators (heckeT_n, heckeT_n_cusp, heckeT_p_all) prove their own commutativity/multiplicativity directly (coset combinatorics), never via the ring — the two tracks are unconnected by design.

## Stuck points (from §8 of brief)

1. (8.1) Nebentypus equivariance (T(D)f)|_k γ = χ(d_γ)·T(D)f for general χ — the only remaining math content; modularity packaging takes it as a hypothesis and is proven; χ=1 case proven; ~1-2 weeks of coset-permutation matrix bookkeeping for general χ.
2. (8.2) Right organising principle: Γ₀(N)-with-twist vs Γ₁(N) ring; prove 8.1 directly vs transport function-level hom; uniform handling of U_p at p∣N.

## Reference list (from §2.2 of brief)

- [Shimura 1971] Introduction to the Arithmetic Theory of Automorphic Functions — §3.4, Props 3.8, 3.30, 3.35
- [Diamond–Shurman 2005] A First Course in Modular Forms, GTM 228 — §5.2, Prop 5.2.1
- [Miyake 1989] Modular Forms — §4.5, §4.6
