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

## Second opinion (ChatGPT gpt-5.6-sol, max effort) — corroborates, and corrects one claim

**Corroborated.** Route β is not the standard construction. KM §2.8 and **Oda §1 Thm 1.1 / Cor 1.3**
both construct the pairing from rigidified line bundles and Čech cocycles, descending *line bundles
along the isogeny* — not a determinant formula along a level cover. And
**Deligne–Rapoport IV.3.20 runs the opposite way**: it calls `e_n` "well known" and then *uses* it to
send a level structure to a primitive root of unity via the determinant. So the determinant formula is
standard as a *calculation*, and as the way to extract the cyclotomic component of a level structure —
never as the construction.

**Correction to claim (2) above — I overstated it.** KM's *construction* needs no Cartier duality, which
is right; but KM does invoke **Cartier–Nishi duality for perfectness** (2.8.2). So: not needed to build
`e_N`, needed for nondegeneracy in general. In the `N`-invertible case it can be avoided: define only
the finite-étale internal dual `G^♯ = Hom_{ℤ/N}(G, μ_N)` and check alternation/perfectness after
geometric base change using the field theorem — "merely Cartier duality restricted to finite local
systems". *The expensive part for Lean is instead the relative Picard/Poincaré infrastructure.*

**Refinement of the circularity diagnosis.** Alternating bilinear `L × L → μ_N` for `L = E[N]`
correspond to `Hom(∧²L, μ_N)`, and in a basis are determined by `ζ = e(b(e₁), b(e₂))` with
`e(b(v),b(w)) = ζ^{det(v,w)}` — the transition rule being exactly (★). Hence:
* solutions of (★) ↔ arbitrary alternating pairings;
* **literal existence of a solution is NOT equivalent to the Weil pairing — `ζ = 1` always satisfies
  (★) and gives the trivial pairing.** (This is precisely the "architectural correction" found
  independently earlier in this session: `nonempty_weilPairing_of_cover_of_values` is satisfiable with
  `ζ = 1`. Independent corroboration.)
* with **primitivity in every geometric fibre**, (★) ⟺ an isomorphism `∧²E[N] ≅ μ_N`, i.e. a *perfect*
  alternating pairing;
* even that is not the *canonical* one — perfect pairings differ by a locally constant element of
  `(ℤ/N)^×`, and a normalisation at one fibre pins it down. The relevant torsor is under
  `(ℤ/N)^×` (it is `Isom(ℤ/N, μ_N)`), not under `μ_N`.
* In monodromy language the missing statement is `det ρ_{E,N} = χ_N`, which is normally *deduced* from
  the Weil pairing.

Verdict quoted: "Do not spend 1100 lines proving the level-cover ζ-cocycle merely as a 'reduction';
that cocycle is the missing symplectic orientation in disguise."

## THE CHEAP ROUTE (new, and recommended for the ℚ-case)

For a **fixed irreducible, geometrically unibranch** base `S` (normal integral suffices) with generic
point `η = Spec K`:

> **Stacks Project, Lemma 58.10.7 ([Tag 0BQI](https://stacks.math.columbia.edu/tag/0BQI))** — if `S` is
> irreducible and geometrically unibranch then `FÉt(S) → FÉt(K)` is **fully faithful**; i.e. for finite
> étale `X, Y` over `S`, `Hom_S(X,Y) ≅ Hom_K(X_η, Y_η)`.

No Noetherian or Nagata hypothesis. *Not* essentially surjective — but we do not need that: `E[N]²` and
`μ_{N,S}` already exist over `S`; only a **morphism between their generic fibres** is being extended.
Connectedness alone is insufficient (irreducible nodal curve: monodromy at the node's branches is
invisible generically) — geometric unibranchness is the precise hypothesis.

The route:
1. over `K̄`: the pointwise pairing is a morphism (finite étale `K̄`-schemes are finite disjoint unions
   of points) — **this is exactly what the tree already has**;
2. Galois equivariance ⟹ a `G_K`-equivariant map of finite `G_K`-sets ⟹ a `K`-morphism
   `e_{N,K} : E_K[N]² → μ_{N,K}` — **also already in the tree** (`fieldWeilPairingHom` and the
   finite-étale descent engine);
3. full faithfulness (0BQI) extends it **uniquely** to `e_{N,S} : E[N]² → μ_{N,S}`;
4. bilinearity, alternation, antisymmetry and the isogeny identities are *equalities of morphisms* of
   finite étale `S`-schemes; they hold generically, so **faithfulness** gives them over `S`;
5. **nondegeneracy at every geometric point**, not just generically: `Φ : E[N] → Hom(E[N], μ_N)` has
   both sides finite étale of rank `N²`; the generic inverse extends by 0BQI and the composites are
   identities because they are generically, so `Φ` is an isomorphism over `S`. (Equivalently: the
   isomorphism locus is open and closed, and contains `η`.)

Two caveats, both recorded as they were given:
* **isogeny functoriality** between two *different* curves still needs the field-level adjointness
  theorem; the determinant law alone does not give it;
* this constructs the pairing for a **fixed** normal integral `S`. Base change *from that `S`* is by
  pullback; comparing with a separately-constructed pairing on a general `T` needs extra naturality.
  **So this route does not, by itself, discharge the register as stated (arbitrary `S`).**

**Mathlib status**: `CommAlgCat.FiniteEtale`, `FiniteEtale.baseChange`, `FiniteEtale.fiber`,
`FiniteEtale.equivOfIsSepClosed` (`Mathlib/RingTheory/Etale/Finite.lean`) exist; **no packaged
generic-fibre full-faithfulness theorem**. For an affine formalisation the proof is the standard
integrally-closed argument, with `IsIntegrallyClosed.algebraMap_eq_of_integral` among the ingredients.

## Recommendation of record

* **arbitrary `S`** (what the register demands): follow **KM 2.8 / Oda §1** — rigidified line bundles
  and Čech cocycles. Expensive in Lean because of the relative Picard/Poincaré infrastructure, but the
  tree's `ModularCurves/Picard/` normalized-cocycle development is aimed at exactly this.
* **normal integral `S` over ℚ**: the generic-fibre + 0BQI route, which reuses the field pairing and the
  descent engine already proved. Cheapest by far.
* **abandon** the level-cover ζ-cocycle as a reduction.
