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

## Step 2 — ordered lemma list for the CHEAP route (normal integral `S` over ℚ)

Transcribing the route's structure, with each leaf's status against the tree and mathlib.

```
R: e_N over a normal integral base S/ℚ, with bilinearity, alternation, nondegeneracy
   Source: Stacks 0BQI for the extension step; Silverman AEC III.8 + KM 2.8.5 for the field pairing.

  L1  the pairing over K̄                        → LEAF, DONE  (fieldWeilPairing + its API)
  L2  descent K̄ → K by Galois equivariance      → LEAF, DONE  (fieldWeilPairingHom, _spec, _unique)
  L3  FÉt(S) → FÉt(K) is fully faithful          → **API GAP** (Stacks Lemma 58.10.7, Tag 0BQI)
      L3.1 affine case: A integrally closed domain, Frac A = K, B C finite étale A-algebras
             ⟹ Hom_A(B,C) ≅ Hom_K(B⊗K, C⊗K)
           L3.1a faithfulness: B → B⊗K injective (B torsion-free over A)     → easy
           L3.1b fullness: a K-map carries B into C because **C is integrally
                 closed in C⊗K** — the "standard integrally-closed argument"  → see L3.2
      L3.2 finite étale over an integrally closed domain is integrally closed → **the real gap**
  L4  extend e_{N,K} to e_{N,S}                  → one line given L3
  L5  bilinearity / alternation / antisymmetry   → one line each: equalities of morphisms of
                                                    finite étale S-schemes, true generically,
                                                    transported by faithfulness
  L6  nondegeneracy at EVERY geometric point     → Φ : E[N] → Hom(E[N], μ_N) is generically iso;
                                                    extend the inverse by L3; composites are
                                                    identities because they are generically
```

**So the cheap route has exactly one API gap, L3.2**, and it is the statement my own memory already
flagged: *mathlib has no normality/regularity ascent along étale.* Verified again just now — no
`IsIntegrallyClosed` results anywhere in `Mathlib/RingTheory/Etale/`, `Smooth/`, or `Unramified/`, and
no `Morphisms/Normal.lean` under `AlgebraicGeometry/`.

**But note the target-specific instance may be much cheaper than the general lemma.** L3.1b only needs
`C` integrally closed for the *two* algebras actually in play:
* `C = A[x]/(xᴺ − 1)` — the coordinate ring of `μ_{N,S}`, with `N` invertible;
* `C = ` the coordinate ring of `E[N]` over an affine chart.
For the first, `A[x]/(xᴺ−1)` with `N` invertible in a normal `A` decomposes over the divisors of `N`
and might be handled directly. **Attack this before attempting general étale-normality ascent** — the
general lemma is a mathlib-scale project, the instance may not be.

### Comparison of the two routes, as decomposed

| | arbitrary `S` (register as stated) | normal integral `S`/ℚ (cheap route) |
|---|---|---|
| source | KM 2.8.1 / Oda §1 Thm 1.1 | Stacks 0BQI + Silverman III.8 |
| construction | rigidified line bundles + Čech cocycles | extend the generic-fibre morphism |
| already proved in tree | `Picard/` normalized cocycles (aimed at it) | L1, L2 — *the whole field side* |
| API gaps | relative Picard/Poincaré; Cartier–Nishi for perfectness (finite-étale dual only if `N` invertible) | **one**: L3.2 étale-normality ascent (or its two instances) |
| discharges the register? | yes | **no** — fixed `S` only |

### Status of Phase 1e
Steps 1 and 2 done (this file). **Steps 2.5–6 not done**: no Lean skeleton yet, no per-leaf adversarial
pass, no `b2_log` consultation, gate not run. The route-β tickets on the board are now known to be
unsourced and should be retired before any skeleton is written — that is a `/develop --continue`
action, not a `--decompose` one.

## Step 4 (partial) — L3.2 attacked, and the recommendation FLIPS

Attack on the "target-specific instance is cheaper" hope: for `N` invertible in a normal `A`,
`x^N − 1` factors into the `Φ_d`, `d | N`, which are pairwise coprime **only** because `N` is
invertible, so `A[x]/(x^N−1) ≅ ∏_{d | N} A[ζ_d]`. Integral closedness of the product reduces to that of
each `A[ζ_d] = A[x]/Φ_d(x)` — a finite free `A`-algebra, étale because `N` is invertible. So the
instance reduces to: *`A` normal and `A → A[ζ_d]` étale ⟹ `A[ζ_d]` normal.* **That is the general
étale-normality ascent again, not a cheaper special case.** The hope is dead; L3.2 is irreducible at
this level and is a mathlib-scale theorem (Stacks 025P / 033C territory).

**Therefore the recommendation flips.** The "cheap" route's single gap is a normality-ascent theorem
absent from mathlib; the KM/Oda route's gaps are relative Picard/Poincaré infrastructure — expensive,
but *the tree is already building exactly that* in `ModularCurves/Picard/` (normalized transition
cocycles, glue effectivity, finite affine trivialising covers), and it is the **sourced** route, and it
is the only one that discharges the register as stated (arbitrary `S`, arbitrary `N`).

## Phase 1e status — the confidence gate has NOT passed

| Step | Status |
|---|---|
| 1 — read the source's full proof | **done** (KM 2.8, pp. 87–91, verbatim quotes above) |
| 2 — ordered lemma list mirroring the source | **done** for both routes |
| 2.5 — Lean skeleton, `:= by sorry`, `lake build` green | **not done** |
| 3 — verbatim quote + Lean↔source paragraph per leaf | partial (quotes for KM 2.8.1's steps; none for the KM tree's leaves, which Step 2 has not yet enumerated) |
| 4 — provability per leaf | partial (L3.2 attacked and rejected as "cheap") |
| 4.5 — adversarial pass, ≥3 attacks per leaf | **not done** |
| 4.6 — prior-B2 log consultation | **not done** |
| 5 — gate | **NOT PASSED** |
| 6 — artifact | this file |

**No tickets may be created from this pass.** What it has established is a redirect, not a plan:
* route β is unsourced — retire its tickets (`/develop --continue`);
* the generic-fibre route is blocked on one mathlib-scale theorem;
* the KM 2.8 / Oda route is the sourced one, discharges the register as stated, and its infrastructure
  is what `Picard/` is already for.

**Next `--decompose` pass should transcribe KM 2.8.1 itself** into the Step-2 lemma list — the
`K_E^×` sheaf, `Pic ≅ H¹(K^×)` with `H⁰ = 1`, Abel (KM 2.1), the unique `h_i/h_j` factorisation,
the patching of `h_i ∘ P` — and check each leaf against `ModularCurves/Picard/`.

## Step 2 (KM route) — checked against `Picard/`, and the answer is that IT IS ALREADY BUILT

The instruction at the end of the last block was "transcribe KM 2.8.1 into the Step-2 lemma list and
check each leaf against `Picard/`". Doing that produces a finding that dominates everything above.

`Picard/SelfAdjointN.lean` (505 lines) is **exactly this transcription, already written**. Its module
docstring opens: *"The decisive input for the Katz–Mazur / GME construction of the relative Weil
pairing"*, and it is labelled **DS4 Gap A**. It proves, for `κ_T(Q) = [𝒪(Q − 0)]` and `m_N = [N]`:

| decl | content | status |
|---|---|---|
| `kappa`, `sectionCls`, `zeroCls` | the Abel map `E(T) → Pic(E_T)` | proved |
| `kappa_mem_ker` | lands in `picRel = Ker(0^*)` | proved |
| `kappa_add`, `kappa_nsmul`, `kappa_zsmul` | `κ` is a group hom (Abel / KM 2.1) | proved |
| `picMap_mulByHom_kappa_pow` | `(★)` `m_N^* κ(Q) = κ(Q)^N` | proved from the leaf |
| **`picMap_mulByHom_kappa_eq_one`** | **`(★′)` `[N]Q = 0 ⟹ m_N^* κ(Q) = 1`** | **proved from the leaf** |

`(★′)` is precisely the input KM 2.8.1 constructs `e_N` from: it is what supplies the function
`f_Q` on `E_T` with `div f_Q = m_N^*(Q) − m_N^*(0)`, whose evaluation on `E[N]` is the pairing.

**The whole file rests on ONE classical leaf** (`:= by sorry`, line 267):

    exists_invertible_tensor_idealModule_add :
      ∃ N, IsInvertible N ∧ Nonempty (I(D_Q) ⊗ I(D_{Q'}) ≅ (I(D_{Q+Q'}) ⊗ I(D_0)) ⊗ π^* N)

— the **relative theorem of the square**, Silverman III.3.5 sheafified. The second sorry (line 488,
`exists_pic_map_snd_picMap_mulByHom_kappa`) is documented in-file as *"NOT AN INDEPENDENT LEAF —
formal consequence of leaf (i)"*, discharged by building the normalized Poincaré bundle `𝒫` and its
symmetry `τ^*𝒫 ≅ 𝒫` (from `m ∘ τ = m`). Its route is written out in the docstring.

The leaf's route is written out too, and it already survives the attacks I would have run:
1. universal pair `B = C ×_U C` over the universal smooth cubic — **reduced**, in fact integral;
2. fibrewise triviality of the rigidified discrepancy `Δ^rig` from the *field* theorem
   `HasseWeil.Pic0.RouteCTheoremOfSquareDiv.kappaDivisor_add_linEquiv` (proved, any characteristic);
3. reduced seesaw ⟹ `Δ^rig ≅ f_B^* M`, then `0^*` gives `M ≅ 𝒪_B`;
4. base-change down to arbitrary, **possibly non-reduced**, `T`.
Two alternatives are recorded as *rejected with reasons*: arbitrary-base fibrewise seesaw is **false**
(the `k[ε]/(ε²)` counterexample — this is [[seesaw-needs-reduced-base]]), and the explicit Weierstrass
line-and-vertical function needs the degenerate loci as closed subschemes. Two feeders are proved
(`_of_tensor_iso`, `Modules.nonempty_iso_of_tensorObj_unitObj`), and the remaining bricks are named
**(A)** the chart-local exact iso and **(B)** the normalized-glue descent assembly.

### Verdict of the decompose pass

| route | leaves outstanding | generality | status |
|---|---|---|---|
| β (level-cover determinant descent) | — | invertible `N` | **unsourced — dead** |
| generic fibre + Stacks 0BQI | 1, **mathlib-scale** (étale-normality ascent) | normal integral `S` only | dominated |
| **KM 2.8 / GME via `Picard/`** | **1 classical** (rel. thm of the square) + 1 bookkeeping | **arbitrary `S`, arbitrary `N`** | **take this** |

The KM route is the sourced one, the general one, *and* the one with the fewest outstanding leaves —
and 95% of it is already in the tree with the leaf isolated and its route written.

### The meta-finding (third instance this window)

This is [[grep-the-conclusion-not-the-inputs]] at the level of **routes**, not lemmas. The tree already
contained the answer, in a file whose docstring names DS4 and Katz–Mazur explicitly. I built route β
and costed a "cheap route" without ever grepping `Picard/` for the conclusion `[N]^* κ(Q)`. The rule
needs extending: **before choosing a route, grep the tree for the route's characteristic conclusion,
not just for the target theorem's statement.** A 505-line file named after the route's key property
will not surface from greps for `weilPairing`.

---

# `/develop --decompose` — adversarial rounds, 2026-08-05

Run at the user's instruction after a run of avoidable errors. Disposition: **red team**. Target: the
`[KM-SEESAW]` sub-tree (`ForMathlib/Seesaw.lean`) and the parent leaf it serves,
`exists_invertible_tensor_idealModule_add` (`Picard/SelfAdjointN.lean:267`).

## Round 1 — the Seesaw sub-tree

### Attack 5 (discharge) — PASSED, all ten citations real

Every name the file's route cites, re-verified with **full** grep output (the earlier `head -1` that
produced a false "stale citations" report is the reason this is spelled out):

| cited | location | ✓ |
|---|---|---|
| `HomologicalComplex.baseChangeKernelZeroLinearEquiv` | `ForMathlib/LowDegreeFiniteProjectiveReplacement.lean:164` | ✓ |
| `orderedBaseCechComplexBaseChangeIso` | `ForMathlib/AffineModuleCechBaseChange.lean:1037` | ✓ |
| `kernelZeroLinearEquivOfHom` | `ForMathlib/CochainComplexKernel.lean:41` | ✓ |
| `baseSectionsIsoKernelOrderedBaseCechDifferential` | `ForMathlib/SchemeModuleOrderedBaseCechZero.lean:256` | ✓ |
| `baseCechKernelOrderedBaseChangeLinearEquiv` | `ForMathlib/SchemeModuleOrderedBaseCechZero.lean:161` | ✓ |
| `orderedBaseCechObject_flat_of_isInvertible` | `ForMathlib/SchemeModuleOrderedBaseCech.lean:357` | ✓ |
| `IsInvertible.exists_finiteAffineBaseCech_flat` | `Picard/InvertibleSheafBaseCechFlat.lean:23` | ✓ |
| `nonempty_unitObj_iso_of_normalized_glue` | `Picard/RigidDescent.lean:65` | ✓ |
| `LinearMap.finrank_ker_baseChange_eq` | `ForMathlib/BaseChangeKerCoker.lean:586` | ✓ |
| `affineFieldFactor_residue_isScalarTower` | `ForMathlib/AffineFieldPointTower.lean:94` | ✓ (relocated today) |

### Attack 2 (edge-case instantiation) on the descent leaf — **SUCCEEDED. Leaf was FALSE.**

`exists_pullback_iso_of_kernel_finrank` assumed only `hrank`: `finrank K (ker (d⁰ ⊗ K)) = 1` at every
field-valued point, i.e. `h⁰(X_s, M_s) = 1`. Instantiate at `S = Spec k`, `X = E` an elliptic curve,
`M = 𝒪_E(P)` with `P ≠ 0` rational. Riemann–Roch at genus `1`, `deg = 1 > 2g-2 = 0`: `h¹ = 0`,
`h⁰ = deg + 1 - g = 1`, stable under field extension — so `hrank` holds. The conclusion would give
`M ≅ π^* N` with `N` invertible on `Spec k`, hence `𝒪_E(P) ≅ 𝒪_E`, false (degrees `1` vs `0`). The counit
`π^*π_*𝒪_E(P) → 𝒪_E(P)` is the inclusion `𝒪_E → 𝒪_E(P)`: injective, **not** surjective.

**Diagnosis.** Stacks 0EX7 assumes `ℰ|_{X_s} ≅ 𝒪^{⊕ r_s}` — *geometric* triviality. I replaced it by its
*numerical* consequence `h⁰ = 1`, which loses the fact that the generator of `Γ(X_s, M_s)` is nowhere
vanishing — exactly what makes the counit surjective. **Fixed**: the descent leaf is now
`exists_pullback_iso_of_kernel_finrank_of_fibre_trivial`, carrying `hrank` *and* `hfib`, with the two
roles spelled out in its docstring (`hrank` ⟹ local freeness of `π_*M`, needing `IsReduced`; `hfib` ⟹
surjectivity of the counit). Logged in `b2_log.jsonl`. Build green; the parent still assembles, now
feeding `hfib` to both children.

### Attack 3 (hypothesis strength) on the rank leaf — flaw found, non-fatal

`orderedBaseCech_residueField_kernel_finrank_of_fibre_trivial` carries `[Flat π]`, `[IsProper π]`,
`[LocallyOfFinitePresentation π]`, `[IsNoetherian X]`. None appears to be used: `Γ(X_s, 𝒪) = κ(s)` comes
from `hπ` alone (instantiate `UniversallyOConnected` at `T = Spec κ(s)`, `U = ⊤` — that *is* the
statement), and the base-change iso needs only `M.IsQuasicoherent`, from `hM`. **Over-specified.** Kept
as-is for source-faithfulness to 0EX7's hypothesis set; recorded so a later `/generalise` can strip them.

### Attack 4 (source drift) on both leaves — **the structural finding of this round**

0EX7's own proof goes through Stacks 0BDP and derived-category machinery. My two leaves go through Čech
kernel ranks. **They are therefore invented, not transcribed** — precisely what the source-faithfulness
rule warns against — and *both* invented leaves have now turned out false (`KM-SEESAW-1` on exactness,
`KM-SEESAW-2′` on the rank). Rule 4 of that section says two false leaves means the source proves it a
different, easier way, or that the result is not the one needed. That is now an open question referred to
the second opinion (below), not a settled plan.

## Round 2 — the parent leaf, and whether the seesaw is on the critical path

### Attack 1 (counterexample search) / grep-the-conclusion — no cube material exists

`theorem.*cube` returns 74 raw hits and **zero** relevant declarations: all are `sCubeCoord₀/₁/₂`,
`root_cube_eq`, `exists_unit_sq_cube` (Weierstrass coordinate algebra) and `atlasCubeCover` (an
unrelated index set). No `theoremOfCube`, no `cubeBundle`, no `Poincare`/`poincareBundle`, no
`theoremOfSquare`. The field-level square exists only as `tos_divisor`, `tos_toClass`,
`tos_pullback_principal_of_{dual_additive_at,sigma_eq_zero}` (`HasseWeil/Pic0/`). **So the cube route is
a from-scratch build**, and the earlier "the KM route is 95% done" framing covers `(★)`/`(★′)` only —
*not* the leaf beneath them.

### Consistency check that did pass

The leaf's `π^* N'` correction term is consistent with the field-level `tos_divisor` having none: over a
field `Pic(k) = 0`, so no correction term is expressible there. The relative statement needs one exactly
because `Pic(T) ≠ 0`. Shapes agree.

### Referred to the second opinion (not settled by me)

`SelfAdjointN.lean:236` asserts an **exact** tensor iso is false, by "restricting along the constant zero
section would force a degree-`2` bundle to agree with a degree-`4` one" for the family `E × E ⟶ E` with
`Q = Q' = ` the diagonal. I could not verify this argument to my own satisfaction, and the leaf's *shape*
(with or without `π^* N'`) depends on it. Asked as Q2 of the second opinion, together with: whether the
cube instantiation at `X = Y = Z = E_T` genuinely satisfies 0BF4's hypotheses (2)/(3)/(4) and yields the
`π^* N'` form (Q1); whether the cube needs the seesaw at all, given 0BF4's proof cites 37.33.1/4/7 and
**not** 37.33.2 (Q3); whether a route avoids both (Q4); whether 0BF4 is valid over **non-reduced** bases,
since the leaf must apply over arbitrary `T` while 0EX7 demands reducedness (Q5); and whether any
standard reference states the relative square in the `π^* N'` form for transcription (Q6).

## Step 4.6 — prior-B2 log consultation (16 entries)

No name- or shape-match for the current leaves other than my own two entries from this session. But the
log has a **dominant failure shape** across the project, and it is the one that bit me twice today:

> 7 of the 14 substantive entries (`T-A4`, `T-E5`, `T-H4`, `T-H6`×2, `T-E5f`, `T-G3a-SUB3`) are
> **hypothesis loss in transcription** — a statement that drops or weakens a hypothesis the source
> maintains (`IsUnit (2 : R)`; "relatively representable"; global vs. local orbits; bare presheaf vs.
> sheaf). `KM-SEESAW-1` and `KM-SEESAW-2′` are the same shape at one remove: substituting a
> *cohomological/numerical* consequence for a *geometric* hypothesis.

**Actionable rule for this project**: when a leaf replaces a source hypothesis with something derived
from it, that substitution is the first thing to attack. In both of today's cases one edge-case
instantiation (genus-1 `H¹ ≠ 0`; `𝒪(P)` of degree 1) killed the leaf immediately.

## Round 3 — second opinion (gpt-5.6-sol, max effort), and the primary-source verification that settles it

### First: the reviewer's headline objection does NOT apply to the code — my question was defective

The review opens with a "preliminary fatal issue": that `κ_raw(Q) = 𝒪(D_Q) ⊗ 𝒪(D_0)^{-1}` does not land in
`ker(0^*)`, so `kappa_mem_ker` and `(★)` would both be false. Its counterexample is correct *for the raw
class*: with `T = C`, `E_T = C × C → C`, `Q(t) = (t,t)`, one gets `0^*κ_raw(Q) ≅ 𝒪_C([0])`, of degree `1`.

**But the tree does not use the raw class.** Verified directly:
* `kappa E hsm t Q := (sectionToPicRel …).1` (`Picard/SelfAdjointN.lean:173`);
* `kappa_eq_picRelProj` (`:222`) — `kappa = picRelProj (sectionCls Q * zeroCls⁻¹)`;
* `picRelProj` (`Picard/RelativePic.lean:81`) is exactly `x ↦ x * (f_T^*(0_T^* x))⁻¹`, and
  `picRel := (Pic.map (baseChangeZero …)).ker` (`:57`);
* so `kappa_mem_ker` (`:230`) is true **by construction** — it is `MonoidHom.mem_ker.mp (…).2`.

That is precisely the `κ⁰ = κ_raw ⊗ f^*(0^*κ_raw)^{-1}` normalisation the review prescribes as the fix.
**I wrote the question with the normalisation dropped**, so the reviewer correctly attacked what I wrote
rather than what the tree does. Recorded because the same slip in a docstring would mislead the next
reader: `SelfAdjointN.lean`'s `κ_T(Q) = [𝒪(Q − 0)]` shorthand reads as the raw class and is not.

### Findings that DO survive against the code

| # | finding | status |
|---|---|---|
| 1 | the 7-term cube I proposed is wrong — needs an 8th factor `p_{E³}^*(e^*A)^{-1}`, or `A^{rig} = A ⊗ f^*(e^*A)^{-1}`, else 0BF4's hypothesis (2) fails since `e^*𝒪(D_0) ≅ ω^{-1}` | **my plan was wrong** |
| 2 | 0BF4 hypothesis (4) — `Z` connected — **fails for arbitrary `T`**; must reuse 0BF4's *proof* (the triviality locus is open-and-closed and meets the zero section on every component) rather than instantiate its statement | **my plan was wrong** |
| 3 | pulling back along `(Q,Q',0) : T → E_T³` yields a bundle on `T`, not an iso on `E_T`; the correct map is `u ↦ (u, −Q, −Q')` | **my plan was wrong** |
| 4 | **0EX7 is not used in 0BF4's proof** (chain: 0BDP → 0BF0 → 0BF3 + Künneth/base-change) | confirms Q3's suspicion |
| 5 | the `ℓ/v` line-and-vertical route cannot work globally — a global `ℓ/v` would make `(P)+(Q)−(P+Q)−(0)` principal, i.e. give the exact iso already disproved | agrees with `SelfAdjointN`'s own rejection |
| 6 | my degree-`2`-vs-`4` argument is **valid**, but its stated *reason* is not what the counterexample shows: in the constant family the normal bundle is **trivial**; `0^*I(D_Q)^{⊗2}` has degree `−2` and `0^*I(D_{2Q}) ≅ 𝒪(−[2]^*[0])` degree `−4`. `SelfAdjointN.lean:236`'s "the normal bundle is generally nontrivial" is a *different* (also true) point | docstring reason to correct |
| 7 | **Katz–Mazur Theorem 2.1.2 states the leaf verbatim for arbitrary `S`** | **the answer — verified below** |
| 8 | a Picard-*class* equality does not yield a pairing; normalized isomorphisms + base-change compatibility + cubical cocycle/symmetry are a separate coherence leaf | real, and consistent with `SelfAdjointN`'s "rigidification trap" note |

### The primary-source verification — KM 2.1.2, book p. 63 (`refs/…/katz-mazur-arithmetic-moduli-FULL.pdf` p. 74)

(2.1.1) fixes the notation: `I(P)` is "the ideal sheaf of `P` viewed as an effective Cartier divisor of
degree one in `E`", and `I⁻¹(P)` the inverse ideal sheaf. Then, verbatim:

> "**THEOREM 2.1.2 (Abel).** There exists a unique structure of commutative group-scheme on `E/S` such
> that for any `S`-scheme `T`, and any three points `P, Q, R` in `E(T) = E_T(T)`, we have
> `P + Q = R`
> if and only if there exists an invertible sheaf `ℒ₀` on `T` and an isomorphism of invertible sheaves on
> `E_T`
> `I⁻¹(P) ⊗ I⁻¹(Q) ⊗ I(0) ≃ I⁻¹(R) ⊗ f_T^*(ℒ₀)`."

**Lean ↔ source match.** Put `R = P + Q` and invert: `I(P) ⊗ I(Q) ≅ I(P+Q) ⊗ I(0) ⊗ f_T^*(ℒ₀^{-1})`.
That **is** `exists_invertible_tensor_idealModule_add` (`Picard/SelfAdjointN.lean:267`) with `N' = ℒ₀^{-1}`
— same four ideal sheaves, same `f^*`-correction, arbitrary `S`, no reducedness, no invertibility of `N`.
The leaf is a **transcription**, not a derivation.

### KM's proof (book pp. 64–66) — and why it needs neither the cube nor the seesaw

1. Reduce to: `E(T) → Pic^{(1)}(E_T/T)`, `P ↦ [I⁻¹(P)]`, is **bijective**, where `Pic^{(1)}` is
   fibrewise-degree-one invertible sheaves modulo `ℒ ∼ ℒ ⊗ f_T^*ℒ₀`. Given bijectivity, `I⁻¹(P) ⊗ I⁻¹(Q) ⊗
   I(0)` is fibrewise degree one, hence of the form `I⁻¹(R) ⊗ f^*ℒ₀` for a **unique** `R` — which both
   defines the group law and proves the theorem.
2. Zariski-local on `S`, using `f_*(𝒪_E) = 𝒪_S` — **this is the tree's `UniversallyOConnected`**.
3. Finite presentation reduces to `S` affine **noetherian**.
4. The crux: for `ℒ` fibre-by-fibre of degree one, `f_*ℒ` is invertible and of formation compatible with
   arbitrary base change, and `R¹f_*ℒ = 0`. KM's reason: `R¹f_*` is compatible with base change (`f`
   proper and flat) and over an algebraically closed field `H¹(E, ℒ) = 0` because `deg ℒ = 1 > 2g − 2 = 0`;
   then Nakayama. Cites **[Mum 4, p. 53]** (Mumford, *Abelian Varieties*) for "`R¹f_*ℒ = 0` ⟹ `f_*ℒ`
   locally free and base-change compatible".
5. Pick an `𝒪_S`-basis `ℓ` of `f_*ℒ` Zariski-locally; `(ℒ, ℓ)` defines an effective Cartier divisor.

**The decisive structural point.** KM needs `H¹ = 0`, and it *has* it — because the sheaves in play are
**fibrewise degree one**, where `deg > 2g − 2`. Nothing here is a seesaw, and nothing needs the base
reduced. That is exactly why KM 2.1.2 is stated over an arbitrary `S`.

**Consequence: `ForMathlib/Seesaw.lean` is off the critical path.** 0EX7 is used neither by 0BF4 (per the
review) nor by KM 2.1.2 (per the source). Its two remaining leaves need not be proved for DS4. And the
reducedness / universal-pair / reduced-seesaw apparatus in `SelfAdjointN.lean`'s route sections is
likewise unnecessary — it was solving a problem (`H¹ ≠ 0` for degree-zero sheaves) that KM sidesteps by
never leaving degree one.

**And the tree already has KM's step 4, for exactly the right sheaf.**
`FibrewiseElliptic.sectionPoleSheafPower_residueField_orderedBaseCech_exactAt_succ`
(`EllipticCurve/PoleSheafBaseCechHigher.lean:295`) gives positive-degree Čech exactness for `𝒪(n[0])`
under `hn : 1 ≤ n` — i.e. `H¹ = 0` in exactly the degree-`≥ 1` range KM uses — and
`…_field_orderedBaseCech_kernel_finrank` (`:360`) gives `h⁰ = n`, so `h⁰ = 1` at `n = 1`. The `hn : 1 ≤ n`
that made those results *useless* for the seesaw is precisely what makes them *right* for KM 2.1.2.

### Verdict of the three rounds

The route is **KM 2.1.2, transcribed**, and the tree is much closer to it than to anything I planned:
`UniversallyOConnected` (step 2) ✓ proved; Noetherian approximation (step 3) ✓ in `Picard/InvertibleSheaf
NoetherianSmoothStage.lean`; `H¹ = 0` and `h⁰ = 1` for degree-one sheaves (step 4) ✓ in
`PoleSheafBaseCechHigher.lean`; effective-Cartier-divisor-from-a-section (step 5) ✓ in
`EllipticCurve/PoleSheaf.lean`. What is genuinely missing is the **bijectivity of
`E(T) → Pic^{(1)}(E_T/T)`** — one internal node with the four steps above as its children — plus finding 8's
coherence leaf.

**Do not** build: the cube, the seesaw, the universal-pair/reduced-seesaw route, or the `ℓ/v` route.

---

# Rounds 4–6 — the KM 2.1.2 tree, transcribed from the source's own proof

## Round 4, Step 1 — KM's FULL proof, read to the end (book pp. 63–67 = pdf 74–78)

The proof does not stop where I stopped last round. Its complete structure, with pages:

**Reduction (p. 64).** Show `E(T) → Pic^{(1)}(E_T/T)`, `P ↦ [I⁻¹(P)]`, is **bijective**, where `Pic^{(1)}`
is "the set of isomorphism classes of invertible sheaves `ℒ` on `E_T` which are fiber-by-fiber of degree
one, modulo the equivalence relation `ℒ ∼ ℒ ⊗ f_T^*(ℒ₀)`". Given bijectivity: `I⁻¹(P) ⊗ I⁻¹(Q) ⊗ I(0)` is
fibre-by-fibre of degree one, hence isomorphic to `I⁻¹(R) ⊗ f^*(ℒ₀)` for a **unique** `R ∈ E(T)` — "therefore
the group-law is unique", and it exists by composing with the bijection `Pic^{(1)} → Pic^{(0)}`,
`ℒ ↦ ℒ ⊗ I(0)`.

**Then bijectivity, in five steps** (replacing `E/S` by `E_T/T` reduces to `T = S`):

* **(p. 65)** The question is *Zariski-local on `S`*: given `ℒ, ℒ'`, an affine open cover `{U_i}`,
  invertible `ℒ_{0,i}` on `U_i`, and isomorphisms `φ_i : ℒ ≅ ℒ' ⊗ f^*(ℒ_{0,i})` over `f⁻¹(U_i)`, there is a
  global `ℒ₀` and `φ : ℒ ≅ ℒ' ⊗ f^*(ℒ₀)`. Because `f_*(𝒪_E) = 𝒪_S`, one has `f_*f^*(ℒ_{0,i}) = ℒ_{0,i}`; the
  `φ_i` show `f_*(ℒ^{-1} ⊗ ℒ')` and `f_*(ℒ ⊗ (ℒ')^{-1})` are mutually inverse invertible sheaves; naming the
  second `ℒ₀` and putting `ℒ'' = ℒ' ⊗ f^*(ℒ₀)` gives `f_*(ℒ^{-1} ⊗ ℒ'') = 𝒪_S = f_*(ℒ ⊗ (ℒ'')^{-1})`, "under
  which the unit section `1 ∈ Γ(S, 𝒪_S)` is the required isomorphism `ℒ ≅ ℒ''`".
* **(p. 66)** Reduce to `S` affine, then — "because `E/S` is of finite presentation" — to `S` affine
  **noetherian** ("even a finitely generated `ℤ`-algebra if we like").
* **(p. 66)** For `ℒ` fibre-by-fibre of degree one: `f_*ℒ` is invertible, of formation compatible with
  arbitrary base change, and `R¹f_*ℒ = 0`. KM: *"It suffices to prove that `R¹f_*ℒ = 0`, for then
  [Mum 4, p. 53] `f_*ℒ` is automatically locally free and of formation compatible with arbitrary change of
  base, so necessarily of rank one because this is obviously so over an algebraically closed field. Now
  `R¹f_*ℒ = 0` because it is of formation compatible with arbitrary change of base (being an `R¹f_*` for
  `f` proper and flat) and because over an algebraically closed field, `H¹(E, ℒ) = 0` for
  `degree(ℒ) > 2g−2 = 0`. As `R¹f_*ℒ` is a coherent sheaf on `S` with all fibers zero, it vanishes by
  Nakayama's lemma."*
* **(pp. 66–67)** `f_*ℒ` invertible ⟹ Zariski-locally pick an `𝒪_S`-basis `ℓ`; then `(ℒ, ℓ)` defines an
  effective Cartier divisor, i.e. `0 → 𝒪 --ℓ--> ℒ → ℒ/𝒪 → 0` with `ℒ/𝒪` flat over `S`. This "amounts to the
  statement that the map of invertible sheaves `𝒪 --ℓ--> ℒ` on `E` is injective, and remains so after any
  base change `T → S`. For this we are reduced to the case `S = Spec(k)` with `k` a field, and
  `ℓ ∈ H⁰(E, ℒ)` a `k`-basis, so non-zero, in which case the assertion is obvious."
* **(p. 67)** The divisor is fibre-by-fibre of degree one, and *"by (1.2.7), any effective Cartier divisor
  of degree one is a section `P ∈ E(S)`"*. Finally *"one verifies easily that the two maps … are inverse
  isomorphisms. Q.E.D."*

## Round 4, Step 2 — the tree, mirroring those pages

```
R  exists_invertible_tensor_idealModule_add          KM 2.1.2, p. 63  ← the leaf in SelfAdjointN:267
   └ L0 (internal) E(T) ≃ Pic⁽¹⁾(E_T/T)              KM pp. 64–67
       ├ L1 Zariski-descent of the f^*-equivalence   p. 65   ← f_*𝒪_E = 𝒪_S
       ├ L2 reduction to an affine noetherian base   p. 66   ← finite presentation
       ├ L3 R¹f_*ℒ = 0 for fibrewise-degree-1 ℒ      p. 66   ← base-change compat + H¹=0 + Nakayama
       ├ L4 f_*ℒ invertible & base-change compatible p. 66   ← Mumford AV p. 53   **API GAP**
       ├ L5 𝒪 --ℓ--> ℒ injective, universally        pp. 66–67 ← reduce to a field, ℓ ≠ 0
       ├ L6 (ℒ,ℓ) is an effective Cartier divisor    pp. 66–67
       ├ L7 degree-one effective Cartier divisor = a section   KM (1.2.7)
       └ L8 the two maps are mutually inverse        p. 67 ("one verifies easily")
   └ L9 (internal) bijectivity ⟹ the theorem          p. 64
       └ L10 Pic⁽¹⁾ → Pic⁽⁰⁾, ℒ ↦ ℒ ⊗ I(0), is a bijection   p. 64
```

Depth 2, eight leaves under `L0`. Every leaf has a page in KM. **This is a transcription** — contrast the
two invented Seesaw leaves, both of which were false.

## Round 5, Step 4 — provability per leaf, checked against the tree

| leaf | status |
|---|---|
| L1 | **project** — `locallyWeierstrass_pushforward_O_eq_O` (`EllipticCurve/PoleFiltration.lean:3000`), packaged as `UniversallyOConnected` (`EllipticCurve/Rigidity.lean:54`). The descent argument itself is elementary given it. |
| L2 | **project** — Noetherian approximation in `Picard/InvertibleSheafNoetherianSmoothStage.lean:257` and `ForMathlib/NoethApprox.lean` |
| L3 | **partial** — the tree has the Čech form for `𝒪(n[0])`, `n ≥ 1` (`PoleSheafBaseCechHigher.lean:295`), *not* for a general fibrewise-degree-one `ℒ` |
| **L4** | **API GAP** — nothing in tree or mathlib. This is the real gap. |
| L5 | gap, but KM calls it obvious after reducing to a field |
| L6 | **partial** — `RelEffCartierDiv.sectionDivisor*` and `sectionDivisor_degree` (`LevelStructure/CartierDivisor.lean:186`) give the *forward* direction |
| L7 | **citation to verify** — KM (1.2.7); the converse direction, not yet located in the tree |
| L8 | gap, elementary |

### The API gap, named precisely, with its source verified

**Mumford, *Abelian Varieties*, p. 53, Corollary 3** — read at `refs/…/mumford-abelian-varieties.pdf`
p. 64, verbatim:

> "**COROLLARY 3.** Let `X, Y, f` and `ℱ` be as above (*unlike Corollary 2, `Y` need not be reduced*).
> Assume for some `p` that `H^p(X_y, ℱ_y) = (0)`, all `y ∈ Y`. Then the natural map
> `R^{p-1}f_*(ℱ) ⊗_{𝒪_Y} k(y) → H^{p-1}(X_y, ℱ_y)` is an isomorphism for all `y ∈ Y`."

**This settles the reducedness question against the source of the citation.** Mumford's *Lemma 1* (p. 51)
— "if `Y` is **reduced** and `dim[ℱ ⊗ k(y)] = r` for all `y`, then `ℱ` is locally free of rank `r`" — is the
reduced-base statement, and it is exactly where my `k[ε]/(ε²)` counterexample lives. But **Corollary 3
carries an explicit parenthetical that `Y` need not be reduced**, and local freeness of `f_*` comes from
the `K^•`-splitting argument on p. 52, not from Lemma 1. So KM 2.1.2 genuinely holds over an arbitrary,
possibly non-reduced `S` — which is why KM states it that way, and why **every reducedness hypothesis I
introduced this session was an artifact of my own route, not of the mathematics.**

## Round 6 — adversarial pass

### L3 — attacks
* **[1] Counterexample.** The obvious attack is the one that killed `KM-SEESAW-1`: `H¹(E, 𝒪) = k ≠ 0` at
  genus 1. It does **not** apply — L3's `ℒ` is fibrewise degree **one**, and `deg = 1 > 2g−2 = 0` gives
  `H¹ = 0`. The degree-zero case, where the attack bites, never occurs in KM's route.
* **[2] Edge cases.** `g = 1` is the only genus in play, so the bound `deg > 2g−2` reads `deg > 0`; degree
  exactly `1` is the boundary and satisfies it strictly. Non-reduced `S`: covered — Mumford Cor. 3 states
  it. Empty `S`: vacuous.
* **[3] Hypothesis strength.** `f` proper **and** flat are both used (base-change compatibility of
  `R¹f_*`); coherence of `R¹f_*ℒ` is what lets Nakayama conclude from vanishing fibres. Dropping fibrewise
  degree one breaks it immediately (previous bullet). No hidden reducedness.
* **[4] Source drift.** The Lean statement would read "`R¹f_*ℒ = 0` for `ℒ` fibrewise of degree one on a
  proper flat `E/S`", which is KM p. 66's sentence verbatim. No drift.
* **Verdict: SURVIVED.**

### L4 — attacks
* **[1] Counterexample.** Local freeness of a pushforward with constant fibre dimension is false over a
  non-reduced base *in general* (Mumford Lemma 1 needs `Y` reduced; `k[ε]/(ε²)` realises the failure). The
  attack fails **here** only because L4's hypothesis is `R¹f_*ℒ = 0`, not "constant fibre dimension" — and
  Corollary 3 is explicitly reduced-free. **This is the same distinction I collapsed in `KM-SEESAW-2′`;
  the leaf must be stated from `R¹ = 0`, never from a dimension count.**
* **[2] Edge cases.** `p = 1` is the case used; `p = 0` is vacuous. Rank one comes from the fibre value
  over an algebraically closed field.
* **[3] Hypothesis strength.** `Y` reduced must **not** be added — adding it would silently reintroduce the
  restriction KM's statement avoids and would make the leaf inapplicable over the non-reduced bases the
  register needs.
* **[5] Discharge.** Nothing in mathlib (three searches last round: `leansearch`, `local_search
  "cohomologyBaseChange"`, `loogle` on `IsProper → pushforward` — all empty) and nothing in the tree. A
  genuine API gap needing its own sub-tree.
* **Verdict: leaf is well-stated; discharge is an API GAP.**

### L0 (internal) — composition attack
Could L1–L8 all hold and `E(T) ≃ Pic⁽¹⁾` fail? The composition is KM's own: L1 makes the claim
Zariski-local, L2 makes it noetherian-affine, L3+L4 construct `f_*ℒ` as an invertible sheaf, L5+L6 turn a
local basis of it into an effective Cartier divisor, L7 turns that divisor into a section, L8 checks the
two constructions invert one another. The one place a gap could hide is L8 ("one verifies easily"), which
is where the *`ℒ₀`-equivalence* must be shown to be respected in both directions — KM does not spell it
out. Flagged as the node most likely to expand.

## Gate (Step 5) — which conditions hold

| # | condition | verdict |
|---|---|---|
| 1 | every leaf discharged or an explicit API gap | **partial** — L5, L7, L8 not yet located; L4 is a named gap |
| 2 | Lean skeleton compiles | **not done** for this tree (the Seesaw skeleton is now off-path) |
| 3 | verbatim source quote per leaf | **yes for R, L0's five steps, L3, L4**; L7 needs KM (1.2.7) read |
| 4 | adversarial pass on every leaf/node | **done for L3, L4, L0**; not for L1, L2, L5–L8, L9, L10 |
| 5 | prior-B2 log checked | **yes** — and both prior B2s are *avoided* by this tree, since KM never leaves degree one |
| 6 | tree mirrors the source's structure | **yes** — every node cites a KM page |
| 7 | single-conclusion leaves | yes as decomposed |

**Gate NOT passed.** But the tree is now a transcription with a page per node, the one real API gap is
named and sourced (Mumford AV p. 53 Cor. 3), and the two false-leaf traps are understood well enough that
the attack on L4 caught the same collapse *before* it was written this time.

---

# Rounds 7–9

## Round 7 — L7's source secured (KM Lemma 1.2.7, book p. 11 = pdf 22)

The converse half, verbatim:

> "Conversely, if `D` is an effective Cartier divisor in `C/S`, proper over `S` of degree one, then we have
> a diagram `D ↪ C → S` in which the diagonal arrow is an isomorphism (because locally on `S`, say
> `S = Spec(R)`, it turns the affine ring of `D` into an `R`-algebra which is an invertible `R`-module,
> i.e., into `R` itself). Q.E.D."

**Lean ↔ source match.** L7 asserts: a `RelEffCartierDiv π` proper over `S` with fibre degree `1`
everywhere is `sectionDivisor π z hz` for some section `z`. The quote gives exactly that, and gives the
proof in one sentence — `Γ(D)` is an invertible `R`-module, hence free of rank one, hence `D ≅ S`. A
genuine leaf, and a cheap one.

**Attacks.** [1] No contradicting statement in the tree; the *forward* direction is `sectionDivisor_degree`
(`LevelStructure/CartierDivisor.lean:186`) and agrees. [2] Edge cases: degree `0` (`D = ∅`) and degree
`≥ 2` are excluded by hypothesis and would both make the diagonal non-iso, so the hypothesis is not
over-specified. [3] Properness over `S` is needed — without it `Γ(D)` need not be finite locally free.
[4] No drift. **SURVIVED.**

## Round 8 — Step 2.5 attempted, and it is BLOCKED on two missing definitions

The skeleton cannot be written yet. Checked, not assumed:

| vocabulary the tree needs for the KM tree | status |
|---|---|
| `RelEffCartierDiv.degree D s` | **exists** — `LevelStructure/CartierDivisor.lean:108` |
| fibrewise degree of an *invertible sheaf* | **absent** — only prose mentions of "fibrewise" |
| `Pic⁽¹⁾(E_T/T)` = fibrewise-degree-one classes modulo `f_T^*` | **absent** — the notion does not exist |
| `R¹f_*` / higher pushforward | **absent entirely** |
| KM 1.2.7's converse (degree-one divisor ⟹ section) | **absent** |

So gate condition 2 is blocked behind **two prerequisite definitions** (fibrewise degree of an invertible
sheaf; `Pic⁽¹⁾`), which are themselves an API-design step, not leaves.

**But `R¹f_*` is not needed.** The tree's Čech formulation expresses L3 and L4 without any derived functor:
L3 becomes "the base-Čech complex is exact at position 1 after base change to each residue field" — which
is literally `PoleSheafBaseCechHigher`'s `exactAt_succ` shape, already proved for `𝒪(n[0])`, `n ≥ 1` — and
L4 becomes "`ker d⁰` is invertible", the `kernel_finrank` shape. This is why the Čech layer exists: it is
the derived-functor-free surrogate, and the degree-one restriction that made it useless for a seesaw is
exactly the range KM works in.

## Round 9 — a structural simplification the source's own framing hides

KM proves *full bijectivity* of `E(T) → Pic⁽¹⁾` because KM is **constructing the group law** — 2.1.2 says
"there exists a unique structure of commutative group-scheme … such that …". **The tree already has the
group law**: `(E.baseChange t).Point (𝟙 T)` carries `AddCommGroup`, and `kappa`/`kappa_add`/`kappa_nsmul`
are proved against it.

So the leaf `R` is not "construct the group law". It is: **the tree's existing group law agrees with the
Abel/Picard one on the specific sheaf `I⁻¹(P) ⊗ I⁻¹(Q) ⊗ I(0)`.** That needs the Abel map's injectivity
plus a surjectivity statement *only for that sheaf*, not the full `Pic⁽¹⁾` bijection — and it is why the
leaf can be stated (as it already is in `SelfAdjointN.lean:267`) with no mention of `Pic⁽¹⁾` at all.

**This cuts L0's eight leaves down to what R actually consumes**: L3 + L4 for that sheaf (Čech form,
partially present), L5 + L6 + L7 to turn the resulting basis into a section, and an identification of that
section with `P + Q` in the tree's group law. L1, L2, L8, L10 and the `Pic⁽¹⁾` definition are needed only
for KM's *uniqueness* claim, which the tree does not need.

**Caution recorded.** This is a deviation from the source's structure — exactly the move that produced two
false leaves earlier this session. It is admissible here only because the omitted parts are KM's
*construction of a group law the tree already has*, not steps of the isomorphism argument. The next round
must verify that claim by checking how the tree's group law was in fact constructed; if it was built from
a Weierstrass chart, then "the two group laws agree" is itself a theorem needing its own decomposition,
and this simplification is premature.

## Gate after nine rounds

| # | condition | verdict |
|---|---|---|
| 1 | leaves discharged or explicit API gap | **partial** — L4 named + sourced; L5/L8 unlocated; L3 partial |
| 2 | skeleton compiles | **BLOCKED** — needs the two prerequisite definitions above |
| 3 | verbatim quote per leaf | R ✓, L0's five steps ✓, L3 ✓, L4 ✓, **L7 ✓ (this round)** |
| 4 | adversarial pass | L3, L4, L0, **L7** done; L1/L2/L5/L6/L8/L9/L10 not |
| 5 | prior-B2 log | ✓ — both prior B2s are structurally avoided, since KM stays in degree one |
| 6 | mirrors the source | ✓ for rounds 4–7; **round 9's simplification deliberately departs from it and is flagged, not adopted** |
| 7 | single-conclusion | ✓ |

**Still not passed**, and the binding blocker is now precise: two definitions (fibrewise degree of an
invertible sheaf, `Pic⁽¹⁾`) must be designed before any skeleton exists, unless round 9's simplification
survives its verification — in which case neither definition is needed.

---

# Round 10 — the verification round 9 required, and it terminates the pass

Round 9 flagged a simplification and made it conditional on one check: **how was the tree's group law
actually constructed?** Answer, verified in `EllipticCurve/GroupLaw.lean`:

```lean
structure EllipticCurve (S : Scheme.{u}) extends EllipticCurveGeom S where
  grp : GrpObj (Over.mk π)                    -- the group-object structure, as DATA
  comm : letI := grp; IsCommMonObj (Over.mk π)
  one_eq_zero : …                              -- the unit is the zero section
```

and `pointAddCommGroup` (`:124`) is transported from that carried field via `Hom.commGroup`. **The group
law is a hypothesis, not a theorem.**

**So round 9's simplification FAILS.** "The tree's group law agrees with the Abel one" is not a shortcut
around `L0` — it *is* `abelEnrichment_unique`, and both it and `abelEnrichment_exists` are already stated
in the tree, at `GroupLaw.lean:80` and `:84`, as `:= by sorry`, labelled **T-A6b / T-A6c, "deferred purity
project"**. Those are two of the 114 project sorries.

## The tree had already produced this decomposition, under expert review, and fenced it

`GroupLaw.lean`'s module docstring, verbatim:

> "**The deferred canonicity ("purity/comparison") project** — `abelEnrichment_exists` /
> `abelEnrichment_unique` below — proves every `EllipticCurveGeom` admits a unique such enrichment, via
> Abel's theorem `E(T) ≅ Pic⁰(E_T/T)` (KM 2.1.2). Its named black boxes, **fixed once and not allowed to
> grow (reviewer's list, Q3)**: `coherent-base-change` (`π_*O_E ≅ O_S` compatibly with base change);
> `relative-duality-genus-one` (`R¹π_*O_E` a line bundle, base-change compatible); `relative-Picard`
> (representability of `Pic_{E/S}`, `Pic⁰_{E/S}`, rigidified variants); `Poincare` (Poincaré bundle);
> `Abel-isomorphism` (`E ≅ Pic⁰_{E/S}` carrying zero to `O_E`, base-change compatible);
> `group-law-from-Abel` (induced structure; uniqueness).
> **⧗KM-gate: KM 2.1–2.3 are on the do-not-formalize-from-memory list.**"

That list is my tree, item for item:

| reviewer's black box | my leaf |
|---|---|
| `coherent-base-change` | L1's input (`UniversallyOConnected`, already proved) |
| `relative-duality-genus-one` | **L3 + L4** — the API gap I named and sourced to Mumford AV p. 53 |
| `relative-Picard` (incl. rigidified) | the **`Pic⁽¹⁾` definition** round 8 found missing |
| `Poincare` | `SelfAdjointN.lean:488`'s route |
| `Abel-isomorphism` `E ≅ Pic⁰_{E/S}` | **L0** |
| `group-law-from-Abel` | L8 + L9 |

**Rounds 4–9 re-derived, from the source, a decomposition the project had already produced under expert
review (2026-07-05, Q1/Q3) and deliberately deferred.** This is the fourth "the tree already had it" of
this session — after `fullLevelHom_baseChange`, `WP-D3a-FACTOR`'s two halves, and `Picard/SelfAdjointN`
being the KM route — and it is the largest: not one lemma, but the whole tree.

The finding is *not* that the decomposition is wrong. Rounds 4–9 arrived independently at the reviewer's
list, from KM's own pages, which is corroboration. The finding is that **it lands inside a fence**, and
that the fence carries an explicit gate against exactly this work.

## Terminal state of the pass

Further `--decompose` rounds would re-derive fenced content. The decomposition is as good as it can get
without a scoping decision, and that decision is not a decomposition question:

* **Option A — open the fence.** Work the `abelEnrichment` project as scoped by the reviewer. The tree
  starts with `coherent-base-change` done and `relative-duality-genus-one` reduced to Mumford AV p. 53
  Cor. 3 (verified reduced-free), and the Čech layer is the derived-functor-free surrogate for it. This is
  the sourced, correct, expensive route, and it discharges DS4's register as stated.
* **Option B — reach the leaf from outside the fence.** No such route survived nine rounds: route β is
  unsourced, the generic-fibre route is mathlib-scale and reaches only normal integral bases, the cube
  needs the same relative-Picard machinery, the seesaw is not on the path, and the `ℓ/v` route cannot work
  globally (a global `ℓ/v` would make `(P)+(Q)−(P+Q)−(0)` principal, which is false).

**Recommendation: Option A**, entered explicitly rather than by drift — the `⧗KM-gate` exists precisely to
prevent drifting into it. Note the gate says "do-not-formalize-**from-memory**"; rounds 4–9 worked from the
primary sources (KM pp. 11, 63–67; Mumford pp. 51–53), with the pages quoted verbatim above, which is what
the gate asks for.
