# Decomposition — the last two `sorry`s of `ModularCurve/YRho.lean`

`/develop --decompose`, 2026-07-26. Adversarial. **No tickets created.**

Two corrections to the status I reported before re-reading the sources. Both came from
the binding rule *"never use memory or a prior summary as the source of a statement or a
route"* — my summary was wrong on both counts.

---

# CORRECTION 1 — the pairing's source is GME 2.6.4, not KM 2.8, and it is already
# transcribed *with proofs*

`decomposition-gme2.md` §"Chain C" carries the construction, marked
**"T-C1's construction of record; KM-gate LIFTED"**. Transcribed steps (pp. 152–153):

> - C.1 splitting: `Pic(E′) = Pic(E′/S) ⊕ Pic(S)` via `0^*`; choose L in each class with `0^*L = O_S`.
> - C.2 the pairing: for isogeny `π : E → E′` of degree N, `L ∈ Ker(π^*)`: `π^*L` trivialised by
>   `(π⁻¹Uᵢ, fᵢ∘π)`; ratios `hᵢ = (fᵢ∘π)/(fⱼ∘π)`-corrected units glue: for `P ∈ Ker(π)`, `hᵢ∘P`
>   glue to `h(P) ∈ 𝔾_m(S)`; `⟨P, L⟩ := h(P)` bilinear; lands in μ_N; key-lemma ⟹ morphism
>   `Ker(π) × Ker(ᵗπ) → μ_N`.
> - C.3 classical formula over k̄ (the NORMALISATION ANCHOR): `div f = N([0]−[P])`, … — LITERALLY
>   Silverman III.8's function-theoretic pairing ⟹ fibrewise comparison with HasseWeil's
>   `weilPairing` is the definitional match.
> - C.4 nondegeneracy (p. 153).
> - C.5 antisymmetry; `⟨,⟩` identifies `Ker(ᵗπ)` with the Cartier dual of `Ker(π)`; adjointness.
> - Lean mapping: `weilPairing` (DS4) := C.2 applied to `π = [N]` (`ᵗ[N] = [N]` by B8).

# CORRECTION 2 — relative Pic⁰ is NOT missing; this project has it, sorry-free

I told you route (d) "needs relative Pic⁰ and autoduality, neither of which exists in
Mathlib". True of mathlib — but **false of this project**. `projects/ModularCurves/ModularCurves/Picard/`
has **zero `sorry`s** and contains:

| declaration | file | what it is |
|---|---|---|
| `Scheme.Modules.picRel` | `Picard/RelativePic.lean:57` | `Pic_{E/S}` as `Ker(0^*) ≤ Pic(E ×_S T)` — GME's C.1 splitting, *as the definition* |
| `Scheme.Modules.picRelFunctor` | `Picard/RelativePic.lean:30` | `Pic_{E/S}` as a contravariant functor |
| `picRelProj` | `Picard/RelativePic.lean:82` | the projection onto the kernel model |
| `sectionToPicRel` | `Picard/DivisorClass.lean:72` | **the GME (2.16) map `E(T) → Pic_{E/S}(T)`**, `P ↦ I(P)⁻¹ ⊗ I(0)` |
| `sectionToPicRel_zero` | `Picard/DivisorClass.lean:90` | it is pointed |
| `picClass`, `idealModule`, `isInvertible_idealModule` | `Picard/…` | the divisor→class machinery |

So the autoduality *map* `E → Pic⁰_{E/S}` is built. What is explicitly deferred is that it
is an **isomorphism** — `RelativePic.lean:24`: *"the isomorphism `E ≅ Pic⁰` ((2.16)
proper) … explicitly deferred"*.

**Revised assessment of Gap A: this is not a from-scratch chapter. It is a
partly-built chain with one named missing theorem (autoduality) plus the C.2 construction.**

---

# Gap A — the DS4 relative Weil pairing

## A.0 A statement finding that must be settled first (B2-adjacent)

```lean
noncomputable def weilPairing (N : ℕ) [NeZero N] :
    pullback (E.torsionπ N) (E.torsionπ N) ⟶ muN S N := sorry
```

There is **no hypothesis that `N` is invertible on `S`**. As stated, the register demands
the pairing when `char k ∣ N`, where `μ_N` is infinitesimal, `E[N]` is not étale, and the
whole Galois/geometric-fibre apparatus is unavailable. GME's C.2 does construct it in that
generality (it is a Picard-theoretic construction, not an étale one), so the statement is
*true* — but every consumer in this project is over a **ℚ-scheme** (`EllObj (CommRingCat.of ℚ)`),
so `N` is automatically invertible.

**Decision needed from the owner:** keep the general statement (and pay for C.2 in full
generality), or add `[NIsInvertible S N]` (and unlock the much cheaper étale routes). I
recommend adding the hypothesis; it costs nothing downstream. Recorded, not acted on.

## A.1 Decomposition (mirrors GME Chain C)

- **A-L1** `picRel_pullback_ker` — `Ker(π^*) ≤ Pic(E)` for `π : E → E'` an isogeny.
  Discharged from project: `Pic.map` + `picRel` exist (`RelativePic.lean`). *Leaf.*
- **A-L2** `trivialisation_of_mem_ker_pullback` — for `L ∈ Ker(π^*)`, a cover `Uᵢ` and
  `fᵢ` trivialising `π^*L`. Source: C.2 first clause. Discharged from project:
  `IsInvertible` is *defined* as "trivialised by some open cover"
  (`Picard/InvertibleSheaf.lean`). *Leaf.*
- **A-L3** `weilCocycle_glue` — the corrected ratios `hᵢ` glue to `h(P) ∈ 𝔾_m(S)` for
  `P ∈ Ker(π)`, normalised by `(fᵢ∘0)/(fⱼ∘0) = 1`. Source: C.2, the "computation".
  **Internal** — this is the substance of the construction; sub-decomposition needed
  (cocycle identity, normalisation at the zero section, descent of the glued unit).
- **A-L4** `weilPairing_bilinear`, `_pow_eq_one` (lands in `μ_N`). Source: C.2 last clause.
- **A-L5** `dualIsogeny_self_of_mulByN` — `ᵗ[N] = [N]`. Source: "B8". **Needs autoduality.**
- **A-L6** `autoduality` — `E ≅ Pic⁰_{E/S}` via `sectionToPicRel`. Source: GME (2.16)
  proper. **API GAP, explicitly deferred in `RelativePic.lean:24`.** This is the single
  genuinely missing theorem of Gap A.
- **A-L7** the nine register specs, via C.3 (fibrewise comparison with HasseWeil's
  `weilPairing`, "the definitional match") + C.4 (nondegeneracy) + C.5 (antisymmetry).
  **The M1c work landed this session is exactly the C.3 fibrewise anchor**: it gives the
  pairing over any perfect field agreeing with Silverman III.8, which is what C.3 needs.

## A.2 Attacks

- **[1] Composition attack on A-L6 → A-L5.** Could autoduality hold and `ᵗ[N] = [N]` fail?
  No: `ᵗ[N]` is `[N]` on `Pic⁰` because `[N]^*` is multiplication by `N` on `Pic⁰`, and
  autoduality intertwines. But this needs `[N]^* = N` on `Pic⁰`, which is *not* in the
  transcription — **flagged as a missing sub-leaf of A-L5**.
- **[2] Hypothesis attack on A.0.** Is `N` invertible really available at every consumer?
  Checked: `rhoProblem` is over `EllObj (CommRingCat.of ℚ)`, and `WeilPairing/Basic.lean`'s
  register is used only through `weilPairingEval` in `RhoLevelStructure`. Yes.
- **[3] Discharge attack on A-L1/A-L2.** Verified `picRel` (`RelativePic.lean:57`),
  `picRelProj` (`:82`), `sectionToPicRel` (`DivisorClass.lean:72`), `isInvertible_idealModule`
  all exist and `grep sorry projects/…/Picard/` returns **0**.
- **[4] Source-drift attack.** The transcription says C.2 gives `Ker(π) × Ker(ᵗπ) → μ_N`,
  whereas DS4 wants `E[N] ×_S E[N] → μ_N`. These agree **only after A-L5/A-L6**. So the
  route genuinely depends on autoduality; there is no shortcut. Recorded honestly.

---

# Gap B — geometric irreducibility, and the GAGA question

## B.0 The verbatim source (KM Cor. 10.9.2 proof, p. 303, transcribed in `decomposition-km10.md`)

> "By the connectedness theorem, for the connectedness it suffices to show that its
> geometric generic fiber is connected, i.e., to study the situation after the base change
> `Z[ζ_N,1/N] ↪ ℂ` … To show that the smooth ℂ-curve `M̄(𝒫)⊗ℂ` is connected, it suffices to
> show that the complement of the finitely many cusps, `M(𝒫)⊗ℂ`, is connected. But this is
> standard, because the underlying complex manifold to `M(𝒫)⊗ℂ` is isomorphic to the
> quotient of the upper half plane by the subgroup `Γ̃ ⊂ SL(2,ℤ)` …"

and KM §10.1 p. 287 admits the route is transcendental:

> "(2) the *transcendental* description of our moduli spaces as quotients of the upper-half
> plane, (a description which we have up to now avoided), used in the proof of 10.9.2"

## B.1 **We do NOT need GAGA. The plan overstated the requirement.**

The old L5 said "a ℂ-scheme is connected iff its analytification is connected (GAGA)".
Only **one direction** is needed, and it is the *easy* one:

* the analytic topology on `X(ℂ)` is **finer** than the Zariski topology;
* a continuous image of a connected space is connected, so
  **`X(ℂ)` analytically connected ⟹ `X(ℂ)` Zariski-connected**;
* `X` is finite type over `ℂ`, hence Jacobson, so closed points are **dense** and every
  nonempty open contains one; therefore a clopen decomposition of the scheme `X` would
  induce one of `X(ℂ)`. So Zariski-connected closed points ⟹ `X` connected.

No coherent-sheaf comparison, no GAGA, no analytification *functor* — just: the analytic
topology refines the Zariski topology, plus density of closed points.

**Furthermore L3 can be weakened.** We do not need an isomorphism of Riemann surfaces. We
need only a **continuous surjection `ℍ ↠ Y(ℂ)_an`**; then `ℍ` connected does the rest. So
the minimal analytic input is:

- **B-L3′** a continuous map `ℍ → Y(ℂ)_an`, `τ ↦ (ℂ/(ℤ+ℤτ), standard level structure)`;
- **B-L3″** its **surjectivity** — i.e. every complex elliptic curve with the given level
  structure is `ℂ/Λ`. This is the uniformisation theorem for complex elliptic curves, and
  it is the real remaining weight (mathlib does not have it).

## B.2 Revised decomposition

- **B-L1** smooth + connected ⟹ irreducible. **DONE** (`irreducibleSpace_of_connectedSpace_of_smooth`, this session).
- **B-L2** connectedness insensitive to `ℚ̄ ↪ ℂ`. Standard (geometric connectedness is
  insensitive to extension of algebraically closed fields). *Still an API gap, but small.*
- **B-L4** `ℍ/Γ̃` connected. **DONE** (`connectedSpace_quotient_orbitRel`).
- **B-L5′** (replaces the GAGA leaf) analytic-topology-refines-Zariski + Jacobson density.
  **Newly identified as cheap.** Needs: the analytic topology on `X(ℂ)` for finite-type `X`
  (constructible affine-locally without an analytification functor), and
  `Jacobson` ⟹ closed points dense (mathlib has `IsJacobsonRing`).
- **B-L3′/B-L3″** the uniformisation. **The remaining real gap.**

## B.3 Attacks

- **[1] Attack on B.1's claim.** Is the analytic topology really finer? Yes — Zariski
  opens are complements of zero sets of polynomials, which are analytically open. Is
  "closed points dense" enough? Yes for Jacobson schemes; `Y` is finite type over a field.
  Could `Y(ℂ)` be empty while `Y` is nonempty? No — `ℂ` algebraically closed + Nullstellensatz.
- **[2] Attack on the weakening of L3.** Does a continuous surjection really suffice? Yes:
  connectedness only needs surjectivity + continuity, not injectivity or holomorphy. But
  **surjectivity is the uniformisation theorem** — the weakening moves the weight, it does
  not remove it. Honest.
- **[3] Attack on B-L2.** Is it really cheap? Geometric connectedness is insensitive to
  algebraically-closed extension, but the Lean statement needs the base-change comparison
  of connected components. Flagged as *small but not free*.
- **[4] Alternative-route attack (Route C, algebraic).** Could we avoid analysis entirely
  via Igusa — monodromy `π₁(M_{1,1}) ↠ SL₂(ℤ/N)`? The transcription already records:
  *"that argument is NOT in KM and would be its own development."* And it needs the étale
  `π₁` of a scheme, which mathlib does not have (`PreGaloisCategory` appears nowhere in
  `Mathlib/AlgebraicGeometry/`). **Heavier than the analytic route, not lighter.**

---

# Feasibility summary

| gap | status | remaining genuinely-missing theorem |
|---|---|---|
| A | partly built; Picard layer sorry-free | **autoduality `E ≅ Pic⁰_{E/S}`** (GME 2.16 proper) + the C.2 cocycle construction + `[N]^* = N` on `Pic⁰` |
| B | two of four leaves done | **uniformisation of complex elliptic curves** (`ℍ ↠ Y(ℂ)` surjective) + the analytic topology on `X(ℂ)` |

Gap B's GAGA requirement was **overstated** and is withdrawn. Gap A's "relative Pic⁰ does
not exist" was **wrong** — it exists here and is sorry-free.

---

# ChatGPT (gpt-5.6-sol, max effort) review — Gap A's route is REPLACED

Every mathlib citation it gave was verified to exist with the stated type before being
recorded below (8/8).

## A1 — my objection to local-determinant descent is confirmed, and sharpened

> "A perfect alternating pairing `e : L × L → μ_N` is equivalent to an isomorphism
> `λ_e : ⋀²_{ℤ/N} L ≅ μ_N`. Under a change of basis `g ∈ GL₂(ℤ/N)`, the determinant
> trivialization of `⋀²L` changes by `det(g)` … Supplying that compatibility is precisely
> supplying `λ_e`. … So the descent itself is formal. What is nonformal is the orientation
> `det(E[N]) ≃ μ_N`. For elliptic curves that orientation comes from the canonical
> principal polarization/autoduality."

It identified this distinction *already present in our code*: `detFun_gl2Both`
(`CharZeroDescent.lean:68`) proves the form is multiplied by `det g`; `detConstMor_sl2`
(`:149`) gets invariance only on `SL₂`; `weilPairingCharZero` (`:193`) "correctly descends
a supplied local pairing satisfying the cocycle condition; **it does not manufacture that
cocycle**." Verified: that is exactly its signature — `ζ'` and `hcocyc` are hypotheses.

## A2 — the recommended route is a refinement of (c), NOT the Pic⁰ route (d)

Cost ranking given (cheapest first):

1. **Generic extension on the existing level-3 atlas, then descend.**
2. Generic extension on the universal Weierstrass atlas `ℤ[1/N, a₁..a₆, Δ⁻¹]` (if all
   `ℤ[1/N]`-bases are wanted; avoids level 3 not being étale in char 3).
3. The restricted Katz–Mazur rigidified-line-bundle construction.
4. **Full relative Pic⁰ / Poincaré bundle / autoduality** ← the route I had planned.
5. Building the scheme-theoretic étale π₁.

So my GME/Pic⁰ plan is ranked **fourth**. The plan above is superseded by:

### The one new lemma the cheap route needs

> Let `R` be a normal domain with fraction field `K`, and `B, C` finite étale `R`-algebras.
> Then `Hom_{R-alg}(C, B) → Hom_{K-alg}(C ⊗ K, B ⊗ K)` is **bijective**.
>
> Existence: an element of `C` is integral over `R`, so its image in `B_K` is integral over
> `B`; `B` is normal and integrally closed in its total ring of fractions, so the image lies
> in `B`. Uniqueness: `B ↪ B_K`.

Elementary (half a page). **Verified absent from mathlib**: no "étale over normal ⟹ normal"
(`grep` over `Mathlib/RingTheory/` returns nothing) and no generic-fibre fully-faithfulness
in `Etale/Finite.lean` (only `equivOfIsSepClosed`). Available ingredients: `IsIntegrallyClosed`,
`IsIntegralClosure`, `Algebra.IsIntegral`, `CommAlgCat.FiniteEtale`, `FiniteEtale.baseChange`
(both verified).

### Revised ticket decomposition for Gap A

1. field-extension and elliptic-**isomorphism** naturality of the existing field pairing
   (note: *more* than the Galois-equivariance we have — this is deferred leaf **H** from
   `decomposition-m1c.md`, now on the critical path rather than optional);
2. fully faithful generic fibre for finite étale algebras over a normal base (the lemma above);
3. extension of `exists_weilPairingHom_of_field` from the generic point to the universal
   level-3 family (its components are normal integral, the atlas being regular);
4. `GL₂(ℤ/3)`-invariance by generic uniqueness — this *manufactures the cocycle* that
   `weilPairingCharZero` needs, closing the circularity of route (a);
5. descent (`weilPairingCharZero`), then the laws, nondegeneracy and base change — each an
   equality of morphisms of finite étale schemes, hence provable on generic fibres and
   propagated by the same uniqueness.

**This reuses everything landed this session**: `exists_weilPairingHom_of_field` supplies
step 3's input, and `e3ModuliRing_isStandardSmoothOfRelativeDimension` gives the atlas its
regularity.

## B — GAGA withdrawn, and the mathlib lemmas are all present

> "Full GAGA is not mathematically necessary. … if `X = U ⊔ V` were a nontrivial Zariski
> clopen decomposition, then `U(ℂ)` and `V(ℂ)` would be nonempty by the Nullstellensatz and
> would be analytically clopen."

Verified present (all 6): `AlgebraicGeometry.pointEquivClosedPoint` (ℂ-points ≃ closed
points, for `LocallyOfFiniteType` over an algebraically closed field),
`LocallyOfFiniteType.jacobsonSpace`, `closure_closedPoints`, `DenseRange.preconnectedSpace`,
`Function.Surjective.connectedSpace`, `Scheme.Hom.surjective`.

Minimal analytic package, in order of weight:

1. **complex uniformization of elliptic curves** ← the only large item;
2. `SL₂(ℤ) ↠ SL₂(ℤ/N)` (elementary);
3. continuity of `ℍ → Y(ℂ)`;
4. the analytic-connected ⟹ Zariski-connected bridge (cheap, lemmas above).

Also: `Y_ℂ → Y_ℚ̄` is surjective and continuous, so B-L2 is `Scheme.Hom.surjective` +
`Function.Surjective.connectedSpace` — cheaper than I recorded.

## Two dead ends closed off

* **Cusps alone cannot work.** "The Tate curve alone supplies only one transvection,
  conjugate to `T = [[1,1],[0,1]]`. Many proper subgroups contain such a transvection." A
  purely algebraic proof needs a *second, transverse* degeneration, or tame inertia at
  `j = 0, 1728`, or a Legendre-family calculation, or Igusa curves mod `p`. "Probably heavier
  than the analytic proof … an algebraic replacement for the π₁-comparison theorem, rather
  than a shortcut around it."
* **Counting cannot work.** "A trivial torsor `B × G → B` over a connected base has the
  correct number of points in every geometric fibre, and `G` acts transitively on that fibre
  and on the set of components, but the total space has `|G|` components." This kills B3
  outright.

## Verdict: attack Gap A first

"It blocks the actual moduli construction, is reusable throughout the project, and admits a
bounded algebraic route exploiting most of what you already proved." Gap B: "explicitly
avoid a GAGA project" — do the small one-way bridge first, leaving complex uniformization as
the only genuinely large input.

---

# Second ChatGPT pass, told about the existing Picard/divisor layers — the ranking moves,
# and **one of my claims above is FALSE**

## CORRECTION 3 (mine) — "`sectionToPicRel` is an isomorphism" is not merely deferred, it is FALSE

A.1's leaf **A-L6** above says the missing theorem is `autoduality : E ≅ Pic⁰_{E/S}` via
`sectionToPicRel`. That statement, *with `picRel = Ker(0*)` as the codomain*, is false:

> "Over a field `k`, `Pic(k) = 0`, so `Ker(0* : Pic(E) → Pic(k)) = Pic(E)`, which contains
> every degree component. The map `Q ↦ 𝒪(Q − 0)` hits only the degree-zero component.
> Consequently, with the current codomain, the statement `sectionToPicRel is an
> isomorphism` is **false**. Abel's theorem would say that it is an isomorphism onto a
> degree-zero subfunctor."

`RelativePic.lean:24` is careful about this — it defers *both* "the degree-0 subfunctor" and
"Abel's isomorphism". My A-L6 collapsed the two and named the false one. **A-L6 is
withdrawn.**

Good news: the construction does not need it. "Katz–Mazur's construction works on the
kernel of pullback inside the full rigidified Picard group. Your second argument comes
specifically from `κ(Q)`, so no degree-zero representability is needed."

## The decisive input is (★′), not autoduality

Write `κ_T(Q) = [𝒪(Q − 0)]` (= `sectionToPicRel`) and `m_N = [N]_{E_T}`. The reusable form is

> **(★)** `m_N^* κ_T(Q) = κ_T([N]Q)`, i.e. in Lean
> `Pic.map m_N (sectionToPicRel … Q) = sectionToPicRel … ([N]Q)`

and for the **construction alone** the strictly weaker form suffices:

> **(★′)** `Q ∈ E[N](T) ⟹ m_N^* κ_T(Q) = 1`.

> "Neither follows merely from the existing `Pic`, `picRel`, or divisor APIs. It is the
> specialized theorem-of-the-square / principal-polarization content hidden in the slogan
> '`[N]` is self-dual'."

**Relevant existing work found (verified present):** `projects/HasseWeil/HasseWeil/Pic0/`
is an entire theorem-of-the-square / PicDual development — `PicDual.lean`,
`PicDualAdditivityReduction.lean`, `PicDualClassMapMultiplicativity.lean`,
`TheoremOfSquareDivisorForm.lean`, `PicDualPullbackTheoremOfSquare.lean` (whose header
pins its own residual as the dual-additivity point identity). It is *field/Weierstrass-divisor*
level, so it does not supply the relative sheafified `(★′)`, but it is the closest existing
material and should be read before attacking it.

## Revised ranking (cheapest first, for "construct the pairing when `N` is invertible")

1. Level-3 atlas extension/descent — "still the shortest, lowest-risk route **if** the
   finite-étale rigidity machinery is ready".
2. **Hybrid: restricted Katz–Mazur construction + fibre rigidity — "now a very close
   competitor, and probably the best reusable architecture".**
3. Pure Katz–Mazur (all properties intrinsically, arbitrary base).
4. Universal Weierstrass extension.
5. Full Pic⁰ / Poincaré / autoduality.
6. Étale fundamental group.

> "Route (3) is now competitive and probably cheaper than route (2), but I would not yet
> declare it cheaper than route (1). **If `(★′)` can be proved in a contained ticket, the
> hybrid route likely becomes the best choice.**"

## The hybrid architecture (recommended)

```
restricted self-adjointness (★′)
  → normalized trivialization of [N]^* L_Q
  → character E[N] → 𝔾_m
  → e(P,Q)^N = 1
  → E[N] ×_S E[N] → μ_N
  → finite-étale fibre rigidity for the remaining identities
```

Construction package, with what we already have:

1. **Object-level rigidified lift.** `picRel` is a subgroup of *isomorphism classes*; KM
   needs an actual sheaf `L_Q` with an actual rigidification `ρ_Q : 0^*L_Q ≅ 𝒪_T`. The
   natural lift of `picRelProj` is `L ↦ L ⊗ f^*(0^*L)⁻¹` with its canonical zero-section
   rigidification — **construct this before passing to `Skeleton`**.
2. **(★′)** — the one substantive new theorem.
3. **Unique normalized trivialization** `α_Q : [N]^*L_Q ≅ 𝒪_{E_T}` agreeing with `ρ_Q` at
   zero; any two differ by a global unit equal to 1 at zero. **We already have exactly this
   uniqueness input**: `EllipticCurveGeom.universallyOConnected` (`EllipticCurve/Rigidity.lean:57`,
   **PROVEN**, from `locallyWeierstrass_pushforward_O_eq_O`) gives KM's `H⁰(E_T, 𝒪^×) = {1}`.
4. **The character.** For `P ∈ E[N](T)`, translation `t_P` preserves `[N]`; compare
   `t_P^* α_Q` with `α_Q`; the ratio is a global unit on `E_T`, hence comes from a unique
   unit of `T`. (*"This translation formulation is safer than saying merely 'evaluate at P'"*.)
5. **Independence + base change.** Needs `sectionToPicRel` to be a *natural transformation*
   — it is currently only a function with `sectionToPicRel_zero`. `sectionDivisor_baseChange`
   is the geometric input; a `picClass`/ideal-module pullback compatibility theorem is still
   required.
6. **`μ_N`-valuedness.** Left bilinearity from the kernel translation action, then
   `e(P,Q)^N = e([N]P, Q) = e(0,Q) = 1`. Use `muNPointsEquiv` + `_natural`/`_mul`/`_pow`.
   **Right** bilinearity intrinsically needs the weaker Abel fragment
   `κ(Q+Q') = κ(Q) ⊗ κ(Q')` — in the hybrid route, get it from fibre rigidity instead.

**Lean optimisation offered:** work only over `T = E[N]` with the universal torsion section,
then evaluate over `E[N] ×_S E[N]`. That produces the scheme morphism directly via
`yonedaEquiv` and avoids building a fully natural pairing on every `T`. **Representability
of `picRel` is not required.**

## Two traps to respect

* **Rigidification.** `Pic` goes through `Skeleton`, so an equality of classes gives only a
  `Nonempty` isomorphism (`toSkeleton_eq_toSkeleton_iff`), never a canonical one; arbitrary
  choices will not be functorial. Build the pairing on genuine rigidified sheaves, prove
  invariance under rigidified isomorphism, *then* descend to classes.
* **Order of operations in the hybrid.** Prove `μ_N`-valuedness **before** invoking fibre
  rigidity: "generic-fibre equality for maps into `𝔾_m` does not control nilpotent
  deviations; maps between finite étale schemes are rigid."

## Scope limit to state plainly

The hybrid proves the hard properties **only where `N` is invertible**. In characteristic
dividing `N`, geometric points do not detect a finite flat group scheme and the field
theorem does not apply; scheme-theoretic perfectness there genuinely needs Cartier–Nishi.
Also, even with `N` invertible, "nondegenerate on geometric fibres" and "`E[N] ≅ E[N]^D`"
are different Lean statements — the latter needs a usable Cartier-dual object. **This is a
second, independent reason to add `[NIsInvertible S N]` to the register (A.0).**

## Divisor/norm route: improved, still not cheapest

`RelEffCartierDiv` "removes a major preliminary layer and makes the divisor route
credible". But: **"incidence loci do not supply a moving lemma"** — they say where supports
meet, not how to find a linearly equivalent divisor with disjoint support. Still missing:
non-effective/principal relative divisors, relative rational functions with prescribed
divisors, moving/existence after an fppf cover, sheafified finite-locally-free norms with
base change, evaluation on finite flat divisors, and **family Weil reciprocity — "the
dominant mathematical cost"**.
