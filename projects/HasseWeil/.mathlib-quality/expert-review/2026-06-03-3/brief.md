# Review brief (round 22) — Hasse bound via the finite-level Weil pairing (Route 2A): the surjectivity blocker

*Prepared 2026-06-03 for the same senior arithmetic-geometry reviewer as rounds 1–21.
Self-contained, but focused: this is a **single-blocker** brief. Following your round-21
"formal-local" guidance we have now built essentially all of the geometric content for the
separable pencil member `1 − π` over `K̄` — the per-place order transport (`hproj`), via the
addition-formula closed-point specialisation and an invariant-differential proof of
unramifiedness (`e = 1`), plus the function-field base-change transports. The entire
unconditional Hasse bound is now blocked on **one** elementary-but-stubborn fact:
**surjectivity of a nonconstant isogeny on `K̄`-points** (Silverman III.4.10(a)). We want
your read on the cleanest route to it in our framework.*

---

## 0. Orientation

Goal: `|#E(𝔽_q) − q − 1| ≤ 2√q`, `E/𝔽_q`, `q = p^r`, via Route 2A (finite-level Weil
pairing). The bound is **machine-checked to reduce** to three per-`ℓ` "scaling" identities
on `E[ℓ]` for the Frobenius pencil `{π, 1−π, rπ−s}` over `K̄`, for all primes `ℓ ≠ p`:
`e_ℓ(ψS, ψT) = e_ℓ(S,T)^{deg ψ}`. The separable members (`1−π`, `rπ−s`) go through a
divisor-theoretic dual; the inseparable `π` through Galois equivariance. All the pairing
theory, the determinant reduction, and the integer-separation endgame are done and
axiom-clean. The separable scaling for `1−π` is now reduced — after this session's work — to
**exactly one** missing geometric input, described in §5–§6.

## 1. The one blocker

> **Surjectivity (Silverman III.4.10(a)).** *The point map of `1 − π` on `K̄`-points,
> `E(K̄) → E(K̄)`, `P ↦ P − π(P)` (`π` the `q`-power Frobenius), is surjective. Likewise for
> `rπ − s` with `p ∤ s`.*

Mathematically this is elementary: `1 − π` is a **nonconstant isogeny** of elliptic curves
(its degree is `#E(𝔽_q) > 0`), hence a finite morphism of smooth projective curves, hence
surjective on closed points. The difficulty is **entirely** in our formalisation framework,
where an isogeny is represented by two *independent* pieces of data (a function-field
comorphism and a point-map), and bridging them at this last step is what we are unsure how to
do cleanly. Everything else is in place.

## 2. Setting and conventions

- `K = 𝔽_q`, `K̄` an algebraic closure; `E/K` an elliptic curve, `K(E)` its function field.
- `π : E → E` the `q`-power Frobenius; `[m]` multiplication by `m`; `E[ℓ] ≅ (ℤ/ℓ)²` for `ℓ≠p`.
- A **place** of `E` (over `K̄`) = a height-one prime of the integral coordinate ring of `E`,
  equivalently a discrete valuation on `K(E)` trivial on `K̄`; `ord_P` the associated
  valuation. We have a **proven bijection** between the closed (`K̄`-rational, smooth) points
  of `E` and these places (over `K̄`): every place is `P ↦ (the valuation at P)` for a unique
  smooth point `P`. Call this the **point–place bijection**; it is established and
  axiom-clean.
- **Our notion of "isogeny" (this is the crux).** An isogeny `φ` is a pair of *independent*
  data: a **comorphism** `φ^* : K(E) → K(E)` (a field embedding fixing `K̄`) and a **point
  map** `φ_* : E(K̄) → E(K̄)` (a group homomorphism). For `1 − π` both are genuine — `φ^*` is
  the group-law addition rational function for `P ↦ P + (−πP)`, and `φ_* = \mathrm{id} − π_*`
  — but the predicate linking them ("for every `g ∈ K(E)` and place `P`,
  `ord_P(φ^* g) = ord_{φ_*(P)}(g)`") is not free in our framework. We call this linking
  predicate **order-transport** (`hproj`); see §5.

## 3. References

- **[Silverman]** *The Arithmetic of Elliptic Curves*, 2nd ed., GTM 106: **II.2.6/2.7**
  (finite-morphism fibre counts), **III.4.10** ((a) `#φ⁻¹(Q) = deg_s φ` for all but finitely
  many `Q`, hence surjectivity; (c) separable ⟹ unramified, `#ker φ = deg φ`), **III.5.1–5.2**
  (`τ^*ω = ω`, `(φ+ψ)^*ω = φ^*ω + ψ^*ω`), **III.6.1–6.2** (dual isogeny + additivity),
  **III.8** (Weil pairing), **V.1.1** (Hasse).
- **Prior replies (this conversation), most relevant:** round 16 — the trace-relation /
  theorem-of-the-square route to `deg(rπ−s)` is circular in char `p`; round 19 — realise the
  separable dual as the Picard/divisor dual (no coordinate-ring comorphism needed); round 20
  — make the scaling surjectivity-light (done), and build a single "geometric realisation"
  compatibility layer; round 21 — `hproj` via the **formal-local** route (translate to the
  origin; unit linear coefficient ⟹ `e = 1`), and (Q2) "once `hproj` holds, get surjectivity
  by lying-over for the finite comorphism extension + the point–place identification."

## 4. What is built and machine-checked (axiom-clean: `propext, Classical.choice, Quot.sound`)

- **The pairing** `e_ℓ` as the constant ratio `τ_S^* g_T / g_T`, with bilinearity,
  alternation, `μ_ℓ`-membership, nondegeneracy.
- **The reduction** "Hasse `⟸` the three per-`ℓ` scalings", and "scaling `⟸` an abstract dual
  `δ` with `δ∘φ = [#ker φ]`" (surjectivity-light, per round 20).
- **The dual relation** `δ∘φ = [#ker φ]` for the divisor-pushforward dual, automatic via the
  σ-bridge (multiplicity-free fibre pullback), CoordHom-free.
- **For `1 − π` over `K̄`, the per-place order transport `hproj`** — the round-21 programme,
  now carried out:
  - the **addition-formula closed-point specialisation**: evaluating the comorphism
    `(1−π)^*` of the group-law addition map at a closed point `P` gives the coordinates of
    `(1−π)·P` (handling secant, tangent/doubling, and 2-torsion-image sub-cases);
  - **`e = 1` (unramifiedness) via the invariant differential**: since `(1−π)^*ω = 1·ω ≠ 0`
    (the differential is nonvanishing), the comorphism sends a uniformiser to a uniformiser —
    this is a *general* lemma for any separable isogeny (it avoids the division-polynomial
    Wronskian the `[ℓ]` case needed);
  - the **function-field base-change transports** (the invariant-differential coefficient and
    the order-at-infinity transport under `K → K̄`), discharged from the completed
    function-field base-change.
- **The point–place bijection** over `K̄` (§2), and the **degree identity** `deg(1−π) =
  #E(𝔽_q)`.

So the abstract scaling's hypotheses for `1−π` are met **except** the construction of the
dual `δ`, which is where surjectivity enters (§5).

## 5. Why surjectivity is the remaining gap

The abstract scaling consumes a group endomorphism `δ : E → E` with `δ∘φ = [#ker φ]`. We
realise `δ` as the **divisor-pushforward dual**: on a degree-0 divisor class `[(Q)−(O)]`,
`δ(Q) := σ(φ^*((Q)−(O)))`, where `φ^*` is the multiplicity-free fibre pullback
`(Q) ↦ Σ_{φ_*(P)=Q}(P)` and `σ` is the Abel–Jacobi sum. For this to be a well-defined group
homomorphism `E → E` we need `φ^*` to send degree-0 divisors to degree-0 divisors, i.e.
`deg(φ^*(D)) = #ker φ · deg D`. With the fibre-pullback definition, `deg(φ^*((Q))) = #φ_*^{-1}(Q)`,
which equals `#ker φ` **iff the fibre over `Q` is nonempty**, i.e. iff `φ_*` is **surjective**.
(We verified the apparent shortcut "build `δ` additively from `hproj` alone, bypassing
degree-0 preservation" is unsound: on the image points it gives `[#ker]`, but on
*non-image* points the fibre is empty and additivity fails by a `σ(\ker φ)` defect.)

Equivalently, this is Silverman's `deg(φ^*D) = deg φ · deg D` — a function-field/ramification
fact. Round 21 (Q3) suggested getting it from the comorphism side (`Σ e_w f_w =
[K(E) : φ^*K(E)]`), which would avoid surjectivity; but in our setup the only divisor
pullback that is wired to the dual is the **point-map fibre** version, and the comorphism-side
`Σ e f` theorem we have is stated through the *coordinate-ring* extension, which does **not
exist** for `1−π` (its comorphism has poles at the affine points of `ker(1−π)`, so it is not
a map of coordinate rings — only of function fields). So we are pushed back to needing
`φ_*` surjective.

## 6. Routes to surjectivity we have considered, and where each stalls

**(R1) Lying-over for the comorphism extension + the point–place bijection (round-21 Q2).**
The comorphism `φ^* : K(E) → K(E)` realises `K(E)` as a finite extension of the subfield
`φ^* K(E)`, of degree `deg(1−π)`. Given `Q ∈ E(K̄)`, take its place `v_Q`; restrict to a
place of `φ^*K(E) ≅ K(E)`; **lift** it (lying-over for the finite extension) to a place `w` of
`K(E)`; by the point–place bijection `w` is the place at some point `P`; by order-transport
(`hproj`, which we now have) `w` lies over `v_Q` iff `ord(·)` matches iff `φ_*(P) = Q`. This
*looks* complete — and the point–place bijection it needs is proven — but we have not managed
to assemble it: the friction is connecting the **abstract finite field extension**
`φ^*K(E) ⊆ K(E)` and its ring-theoretic lying-over (in mathlib, lying-over lives at the level
of prime ideals of the integral closure) to our **geometric places** and the **point map**
`φ_*`, in a way that turns the lifted prime into the *specific* point `P` with `φ_*(P) = Q`.
This is the same "geometric point ↔ ring-theoretic place" seam that has blocked us elsewhere
(it is exactly the residue-field/inertia step that gates one core lemma of our
infinity-place degree theory).

**(R2) Via the dual: `φ ∘ φ̂ = [deg φ]`.** If we had a `φ̂` with `φ_* ∘ φ̂_* = [deg φ]`, then
`[deg φ]` surjective (which we have, over `K̄`) would give `φ_*` surjective. But our
divisor-pushforward dual yields `δ_* ∘ φ_* = [#ker]` — the **other** composition order — and
the genuine two-sided dual `(1−V)(1−π) = [#E]` is itself unproven here (it needs the dual
additivity `(1−π)^{\wedge} = 1 − π̂`, which is the char-`p` "theorem of the square" wall from
round 16).

**(R3) Division-polynomial coordinates (as for `[m]`).** For `[m]` we proved surjectivity
from the explicit `[m]·P = (φ_m/ψ_m², …)` formula. `1−π` has no such global coordinate
formula (it is the addition map twisted by Frobenius); its comorphism is the addition rational
function, for which we have closed-point specialisation but no surjectivity-giving global form.

**(R4) Image is closed ⟹ all of `E`.** The image of `φ_*` is a subgroup; a *nonconstant*
isogeny has infinite image; an infinite "algebraic" subgroup of the 1-dimensional `E` is all
of `E`. This is the cleanest classical argument, but it needs the image to be Zariski-closed /
the "a proper closed subgroup of a curve is finite" fact, which our point-map–based framework
does not currently express (we have points and places, not the scheme-theoretic image).

## 7. Questions

> **Q1 (the main one).** What is the cleanest route to **surjectivity of a nonconstant
> isogeny on `K̄`-points** in a framework that has: (i) a proven bijection between closed
> `K̄`-points of `E` and the height-one places of `K(E)`; (ii) the comorphism `φ^* : K(E) →
> K(E)` as a finite field extension of known degree; (iii) the per-place order-transport
> `ord_P(φ^* g) = ord_{φ_*(P)}(g)` (`hproj`)? Is route **(R1)** (lying-over + point–place
> bijection + `hproj`) the right one, and if so, what is the precise sequence of standard
> facts that turns "a prime of `K(E)` lying over the place at `Q`" into "a point `P` with
> `φ_*(P) = Q`"? In particular, does `hproj` already *give* the identification (so the only
> missing ingredient is ring-theoretic lying-over for `φ^*K(E) ⊆ K(E)`), or is there a
> genuine extra step?

> **Q2.** Is there a way to make route **(R4)** ("image closed ⟹ surjective") precise using
> only function-field / valuation data — e.g. "the set of places of `K(E)` whose restriction
> to `φ^*K(E)` is a *given* place is nonempty and finite" — so that we never need the
> scheme-theoretic image, only places and `hproj`? This feels close to (R1); is it the same?

> **Q3 (sanity on necessity).** Given our **point-map fibre** divisor pullback, the dual `δ`
> genuinely needs `deg(φ^* D) = #ker · deg D`, which needs surjectivity (§5). Is there a
> formulation of the divisor-pushforward dual `δ` (with `δ∘φ = [#ker]`) that is **provably a
> group homomorphism without** surjectivity — e.g. defining `δ` only on the *principal*-plus-
> *image* part it actually needs for the scaling — or is surjectivity genuinely unavoidable
> for any construction of `δ`? (We found the naive "additive from `hproj`" attempt unsound,
> §5; is there a non-naive one?)

> **Q4 (fallback).** If surjectivity in this framework really requires building a small amount
> of new infrastructure (a function-field lying-over bridge, or a Zariski-closed-image
> notion), which is the **least** infrastructure — i.e. what is the smallest reusable lemma
> we should formalise once, that discharges surjectivity for every separable pencil member
> (`1−π`, `rπ−s`, and any separable factor)?

## 8. Status summary

| Component | Status |
|---|---|
| Pairing (`e_ℓ`): bilinear/alternating/nondegenerate | done, axiom-clean |
| Hasse `⟸` 3 scalings; scaling `⟸` dual `δ` with `δ∘φ=[#ker]` (surjectivity-light) | done |
| `δ∘φ=[#ker]` via σ-bridge | done |
| `1−π` order transport `hproj` (addition-formula specialisation + `e=1` via differential + base-change transports) | done |
| point–place bijection over `K̄`; `deg(1−π)=#E(𝔽_q)` | done |
| **dual `δ` well-defined (needs `deg(φ^*D)=#ker·deg D`)** | **blocked on surjectivity** |
| **surjectivity of `1−π`, `rπ−s` on `K̄`-points (III.4.10a)** | **the one open input — §6** |
| Frobenius factor `π` scaling (Galois route) | not yet assembled (independent; expected routine) |
| `rπ−s` scaling | reuses the `1−π` machinery (built generically) + its own surjectivity |

Everything except the bottom block is built. The bottom block is one classical fact —
surjectivity of a nonconstant isogeny over `K̄` — whose only obstacle is the geometric-point
↔ function-field-place seam in our representation.

## 9. Document metadata
- Project: Hasse bound for `E/𝔽_q` via the finite-level Weil pairing (Route 2A), Lean 4 / Mathlib.
- Brief: round 22, 2026-06-03. Continues rounds 1–21.
- Build status: the reduction + pairing chain are in the compiling root build, axiom-clean; the
  `1−π` geometric work is built but being repaired/wired after a mathlib-version drift.
- Core ask: §7 — the cleanest route to surjectivity of a nonconstant isogeny on `K̄`-points,
  given a proven point↔place bijection, the comorphism as a finite extension, and per-place
  order-transport.
