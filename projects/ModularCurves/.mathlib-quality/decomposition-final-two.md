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
