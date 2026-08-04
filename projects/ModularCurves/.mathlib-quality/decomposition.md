# Decomposition — the Weil pairing `e_N` over an arbitrary base (DS4)

**Status: Phase 1e Step 1 (read the source's full proof) — DONE, and it invalidates the
route the project has been pursuing.**

## The source

Katz–Mazur, *Arithmetic Moduli of Elliptic Curves* (Annals of Math. Studies 108, PUP 1985),
**§2.8 "Pairings", book pp. 87–91** (`refs/ModularCurves/katz-mazur-arithmetic-moduli-FULL.pdf`,
PDF pp. 98–102). Cross-reference given by KM: Oda, pp. 66–67 (KM's pairing is *the opposite* of
Oda's); the `Pic ≅ H¹(K^×)` input is cited to [K-5] §5, esp. 5.2, pp. 186–187.

## What KM actually does (verbatim quotes)

**(2.8.1)** — the setting is an *arbitrary* base, and the pairing is for an arbitrary isogeny:

> "For any N-isogeny π (always understood to mean: finite locally free of rank N) between
> elliptic curves over an **arbitrary base** S, with dual N-isogeny π^t, … there is a canonical
> bilinear pairing of finite locally-free commutative S-group-schemes
>   Ker π × Ker π^t → μ_N ⊂ 𝔾_m."

**(2.8.1.5–2.8.1.7, p. 88)** — the construction. Let `K_E^×  ⊂ O_E^×` be the subsheaf of
invertible functions on `E` taking the value 1 along the zero-section. Then:

> "we have a natural isomorphism  Pic(E/S) ≅ H¹(E, K_E^×),  while  H⁰(E, K_E^×) = {1}."

> "By Abel's theorem (cf. 2.1), we may interpret a point P′ ∈ (Ker π^t)(S) as an element 𝓛 of
> Pic⁰(E′/S) which lies in the kernel of π^* … In terms of a normalized cocycle … f_{i,j} ∈
> Γ(U_i ∩ U_j, K_{E′}^×), the triviality of π^*(𝓛) in Pic(E/S) means that the normalized cocycle
> representing π^*(𝓛) … f_{i,j} ∘ π … may be written **uniquely** in the form f_{i,j} ∘ π = h_i/h_j,
> with functions h_i ∈ Γ(π^{-1}(U_i), K_E^×)."

**(p. 89)** — and then the pairing is *evaluation of those functions at the point*:

> "Now view P ∈ (Ker π)(S) ⊂ E(S) as an S-morphism S → E. Over the open covering of S given by the
> open sets P^{-1}(π^{-1}U_i), we have the invertible functions h_i ∘ P, which, in view of the
> relations f_{i,j} ∈ K^×, h_i/h_j = f_{i,j} ∘ π, πP = 0, **patch together to define a global
> section** “h(P)” ∈ Γ(S, O_S^×) = 𝔾_m(S). One then defines ⟨P, P′⟩_π = “h(P)”.
> One verifies easily that this construction defines a bilinear pairing
> (Ker π)(S) × (Ker π^t)(S) → 𝔾_m(S). **Because (Ker π)(S) is killed by N, the pairing lands in
> μ_N(S).**"

**(2.8.5, p. 90)** — `e_N` is the self-dual case:

> "If we apply the discussion 2.8.1.2 to the N²-isogeny “multiplication by N”, which is self-dual
> (2.6.2.1), we obtain the “e_N-pairing”  E[N] × E[N] → μ_N,  (P,Q) ↦ ⟨P,Q⟩_N = e_N(P,Q), which
> (by 2.8.3) is an alternating autoduality of E[N]."

**(2.8.2)** — Cartier duality appears only as a **consequence**:

> "According to the fundamental Cartier–Nishi duality theory (cf. [Oda]), this pairing defines an
> isomorphism of S-group-schemes  Ker(π^t) ≅ Hom_{S-gp}(Ker π, 𝔾_m)."

## Three corrections this forces

**(1) Route β is invented, not transcribed.** KM never trivialises `E[N]` over a cover, never uses
a level structure, never writes a determinant formula `ζ^{det(v|w)}`, and never descends along an
fppf cover to build `e_N`. The determinant formula is a *computation of* `e_N` after the fact
(and is how `e_N` interacts with `GL₂`), not a construction of it. Everything this session built
downstream of `nonempty_weilPairing_of_localData` is scaffolding for a route with **no source**.
This is precisely the failure mode `/develop`'s source-faithfulness rule exists to prevent, and it
was not caught because Phase 1e Step 1 — *read the source's proof* — had never been run for DS4.

**(2) Cartier duality is NOT needed.** The board and
`memory/ds4-weil-pairing-bottom.md` both assert the general-`N` case is gated on "Cartier duality
for finite flat group schemes (API gap AG-CD)", a multi-week/month development. **False.** KM's
construction *produces* the pairing and gets Cartier–Nishi duality as a corollary (2.8.2). The
construction's inputs are: `Pic(E/S) ≅ H¹(E, K_E^×)` with `H⁰(E, K_E^×) = {1}`; Abel's theorem
(KM 2.1) to see `Ker(π^t)(S)` inside `Pic⁰(E′/S)`; the unique factorisation `f_{i,j}∘π = h_i/h_j`;
and patching `h_i ∘ P` into a global unit.

**(3) The register's arbitrary-`N`, arbitrary-`S` statement is correct and reachable.** My advice to
the user — that the register is gratuitously general and should carry `NIsInvertible S N` — rested
on the false premise in (2). **Withdraw it.** KM's construction is base-agnostic and needs no
invertibility, which is exactly why KM can use it at bad primes.

## Where the tree already has KM's ingredients

`ModularCurves/Picard/` is a substantial development of invertible sheaves *by trivialising cover
and normalized transition cocycle* — `InvertibleSheafCocycle.lean` has
`trivializationTransitionUnit`, `_self`, `_symm`, `_trans`, `_restrict`,
`trivializingCoverTransitionUnitOn`, `trivializingCoverTransitionUnit_cocycle`,
and `InvertibleSheafGlueEffectivity.lean` / `InvertibleSheafFiniteAffineCover.lean`
(`IsInvertible.exists_finite_affine_trivializingCover`). That is the `H¹(E, K^×)`-with-normalized-
cocycles machinery KM's proof runs on. It was built for `Pic⁰` and the Hasse bound, and it is
pointing at exactly the right target.

## Next (Phase 1e Steps 2–6) — NOT yet done

Transcribe KM 2.8.1's proof into an ordered lemma list mirroring *its* structure:
`K_E^×`-sheaf → `Pic ≅ H¹(K^×)` + `H⁰ = 1` → Abel (KM 2.1) → unique `h_i/h_j` factorisation →
patching `h_i ∘ P` → bilinearity → lands in `μ_N` → self-dual case gives `e_N` → alternating
(2.8.3, via Oda) → isotropy (2.8.7). Then Steps 2.5 (Lean skeleton), 3 (verbatim quotes per leaf —
several are already above), 4 (provability against `Picard/`), 4.5 (adversarial), 4.6 (b2 log),
5 (gate), 6 (this file).
