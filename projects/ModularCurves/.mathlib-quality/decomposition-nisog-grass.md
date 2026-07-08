# /develop --decompose — [STREAM-FP] stretch (ii): [NISOG-GRASS], the relative Grassmannian scheme

*fable-FP, 2026-07-08 (same session as [A711-FP]/[FP-B]/[KM-FMT-FLAT]; see
`decomposition-a711-fp.md`, `decomposition-fmt-flat.md`). Gate ledger entry
(decomposition-nisog.md §4): "relative Grassmannian of quotients (scheme) | mathlib gap
(only `RingTheory/Grassmannian`); ForMathlib-scale". Consumer: [L15]
`exists_nIsogSpace` (NIsogeny.lean:401, sorried; KM 6.5.1) → [L27] Γ₀ classifier (M6).
Discipline: v10.8 (this artifact) / v10.24 (waved skeletons, opaque interfaces) /
v10.35b (internal only).*

## What the gate is, and the route of record

**Target**: represent mathlib's `Module.Grassmannian.functor` by a scheme — the relative
Grassmannian `Grass(k, M)` of rank-`k` locally free QUOTIENTS of a module, over a base
ring `R` (KM's ambient space at `M = 𝓕 = π_*O_{E[N]}`, `k = N`, rank `n = N²`).

**Route of record = Stacks 089T = mathlib's own TODO ladder.** Two independent sources
agree on the architecture:

1. **Stacks Tag 089T = Lemma 27.22.1** (fetched 2026-07-08, verbatim): *"Let 0 < k < n.
   The functor G(k, n) of (27.22.0.1) is representable by a scheme."* Proof shape (as
   fetched): *(1) the functor is a Zariski sheaf; (2) subfunctors F_i for each
   (n−k)-element subset i, consisting of surjections where a canonical map s_i is
   surjective; (3) each F_i ≅ "S ↦ Γ(S, O_S^{k(n−k)})", representable by affine space
   𝔸^{k(n−k)}_ℤ; (4) F_i ⊂ F representable by open immersions, via Nakayama; (5) every
   element of F(S) is Zariski-locally in some F_i.* Representability then follows from
   the Schemes-26.15.4 criterion (Zariski sheaf + open cover by representable
   subfunctors).
2. **Mathlib's `RingTheory/Grassmannian.lean` module-doc TODO** (pin, verbatim):
   *"Define `chart x` indexed by `x : Fin k → M` as a subtype consisting of those
   `N ∈ G(k, A ⊗[R] M; A)` such that the composition `R^k → M → M⧸N` is an isomorphism.
   Define `chartFunctor x` to turn `chart x` into a subfunctor of
   `Module.Grassmannian.functor`. This will correspond to an affine open chart in the
   Grassmannian. … Representability of `Module.Grassmannian.functor R M k`."*

We build mathlib's ladder (charts indexed by tuples `x : Fin k → M` — strictly more
flexible than Stacks' subsets, and upstream-aligned), in waves. The KM consumer
instantiates `M := 𝓕`, and its bi-ideal locus is then Useful-Lemma-type vanishing inside
the ambient scheme (L15's own post-gate work, NOT this charter's).

**Existing substrate verified on the pin**: `Module.Grassmannian` (structure: submodule
with finite, projective, `rankAtStalk = k` quotient; Stacks 089R), `Grassmannian.map` /
`functor` (base-change functor `CommAlgCat R ⥤ Type`), `baseChangeMkQEquiv`;
`rankAtStalk_eq_of_equiv` / `rankAtStalk_eq_finrank_of_free` / `rankAtStalk_pi`
(FreeLocus.lean); `LinearMap.quotKerEquivOfSurjective`; project Proj suite
(`ProjectiveSpaceChart` etc. — NOT needed on this route: chart-gluing, no Plücker) and
glue machinery (mathlib `Scheme.GlueData` + `GluingOneHypercover.sheafValGluedMk`).

## KM source (banked verbatim — cited, not re-fetched)

KM 6.5.1 (print p. 165), banked at NIsogeny.lean:397–400 and artifact §1/6.5: *"a
subgroup `G ⊆ E[N]` of the type being sought is nothing other than a locally free
rank-`N` quotient `𝓕 ↠ 𝔥` … such that the kernel `𝒦 ⊆ 𝓕` is a bi-ideal … Therefore
`[N-Isog]` is relatively represented by a closed subscheme of the Grassmannian of all
rank-`N` quotients of `𝓕`"*. The finiteness clause of L15 (fibre counts, connected-étale
splitting) is flagged [BB-DIFF]-adjacent in the NISOG artifact and stays OUT of this
gate.

## Ordered leaf ladder (waves; wave-1 skeleton ships now)

**Wave 1 — the chart algebra (pure CommAlg, zero gates, provable NOW).** New file
`ForMathlib/GrassmannianChart.lean`:

- **[GR-A0]** `Module.Grassmannian.IsChartAt (x : Fin k → M) (N : G(k, M; R)) : Prop` —
  the composite `(Fin k → R) →ₗ[R] M →ₗ[R] M ⧸ N` (coordinates along `x`, then quotient)
  is bijective. *Match*: mathlib-TODO's "the composition `R^k → M → M⧸N` is an
  isomorphism"; Stacks 089T's "s_i is surjective" (finite free of equal rank: surjective
  ⟺ iso, but we state bijective per the TODO).
- **[GR-A1]** `chartEquivRetraction`: `{N // IsChartAt x N} ≃ {φ : M →ₗ[R] (Fin k → R) //
  ∀ i, φ (x i) = Pi.single i 1}` — a chart-member is the same thing as a retraction of
  `x`. Forward: `φ = (iso)⁻¹ ∘ mkQ`; backward: `N = ker φ` (quotient ≅ `Fin k → R` via
  `quotKerEquivOfSurjective`, so finite + projective + `rankAtStalk = k` by
  `rankAtStalk_eq_of_equiv` + `rankAtStalk_eq_finrank_of_free`). *Match*: Stacks 089T
  step (3) — the chart is an affine-space worth of data; the retraction formulation is
  the coordinate-free matrix.
- **[GR-A2]** `isChartAt_map`: base change along `A → B` (mathlib's `Grassmannian.map`)
  preserves charts at `1 ⊗ₜ x`. Route: the B-composite is the base change of the
  A-composite modulo `baseChangeMkQEquiv`; bijectivity transports along
  `LinearEquiv.baseChange`. *Match*: 089T step (4)'s base-change stability.
- **[GR-B]** `retractionEquivMatrix` (`M = Fin n → R`, `x = Pi.single (ι i) 1` for an
  embedding `ι : Fin k ↪ Fin n`): retractions of `x` ≃ `{j // j ∉ Set.range ι} → (Fin k
  → R)` — a `φ` is freely determined by its values on the complementary coordinates.
  *Match*: 089T step (3), "F_i ≅ S ↦ Γ(S, O_S^{⊕k(n−k)})" at the point-set level; the
  functorial upgrade is [GR-B2].

**Wave 2 — chart functors + covering (algebra, statements pinned when wave 1's
interface is proven; v10.24 opaque-interface decision recorded)**:
- **[GR-B2]** naturality of [GR-B] in the algebra: `chartFunctor (ι) ≅` the affine-space
  functor `A ↦ (Fin k × {j ∉ range ι} → A)`, corepresented by
  `MvPolynomial (Fin k × …) R`.
- **[GR-C]** Zariski-local covering (089T step 5): every `N ∈ G(k, A ⊗ (Fin n → R); A)`
  lies in some coordinate chart after localizing at an element outside any given prime
  (Nakayama: the quotient is free at `p`; a spanning k-subset of the images of the `e_j`
  exists at `p` and spreads to a basic open).
- **[GR-D]** openness of the chart condition (089T step 4): for fixed `N`, `{p |
  IsChartAt holds at p}` is open — surjectivity locus of a map onto a finite projective
  module (cokernel-vanishing openness, Nakayama).

**Wave 3 — the scheme (glue) + T-points**:
- **[GR-E]** transition data between coordinate charts on the matrix rings (localize at
  the relevant minor determinant; cocycle identity) — the det/adjugate algebra.
- **[GR-F]** `grassmannianScheme R k n : Scheme` + `⟶ Spec R` via `Scheme.GlueData` over
  the `Fin k ↪ Fin n` chart atlas.
- **[GR-G]** the T-point classification (top-level statement of the gate): morphisms
  `T ⟶ grassmannianScheme R k n` over `Spec R` ≃ rank-`k` locally free quotients of
  `O_T^n` — via open covers of `T` + [GR-C]/[GR-B2]. The `exists_nIsogSpace` consumer
  then needs the locally-free-sheaf relativization **[GR-H]** (glue over an affine cover
  of `S`; registered, deferred — KM's `𝓕` is Zariski-locally free of rank `N²`).

Wave-2/3 statements are deliberately NOT skeletonned yet: their signatures depend on
wave 1's proven interface (retraction vs. matrix normal forms; glue-data index choice).
This is the v10.24(b) call — pin heavy definitions together with their opaque
interfaces, not before. The artifact is the binding record of the ladder; the board
carries the wave-1 tickets now and wave-2/3 tickets at each wave boundary.

## Adversarial blocks (wave-1 leaves, ≥3 each)

### [GR-A0]/[GR-A1]
1. **"Chart should be surjectivity, not bijectivity"** (Stacks says s_i surjective): for
   a rank-k finite projective quotient and a free rank-k source, surjective ⟹ iso
   (surjective endo-rank argument); mathlib's TODO says "isomorphism"; we define via
   `Bijective` and can add the `surjective_iff` bridge when wave 2 needs it. No
   statement risk — the two cuts agree on the locus.
2. **Instance-carrying subtype trap**: members of `G(k, M; R)` carry instances
   (`finite_quotient` etc.); constructing the backward direction needs those instances
   ON `M ⧸ ker φ` — provided via `quotKerEquivOfSurjective` transport
   (`Module.Finite.equiv`, `Projective.of_equiv`?? verify names; fallback: `.of_surjective`
   forms). Roundtrip `Subtype.ext` needs only the submodule equality (`Grassmannian.ext`).
3. **`Fintype.linearCombination` name risk**: the `(Fin k → R) →ₗ[R] M` "coordinates
   along x" map may be `Fintype.linearCombination R x` or need assembling from
   `Finsupp.linearCombination ∘ (Finsupp.equivFunOnFinite)`; verify at build; a private
   `def coordMap` isolates the choice (opaque-interface, v10.24).
4. **`Pi.single i 1` vs `LinearMap.single`/std basis mismatch**: state retraction
   condition with `Pi.single i 1` (defeq to `Pi.basisFun` vectors); bridging simp lemmas
   exist (`Pi.basisFun_apply`).

### [GR-A2]
1. **Which map is "base change"**: mathlib's `Grassmannian.map` goes through
   `baseChangeMkQ : B ⊗[R] M →ₗ[B] B ⊗[A] ((A ⊗[R] M) ⧸ N)` — NOT literally
   `LinearMap.baseChange` of the composite; the proof must go through
   `baseChangeMkQEquiv` + a `⊗`-associativity square. Budget a diagram chase; if
   elaboration crawls, split the square into private lemmas (v10.24(a)).
2. **Tower vs plain algebra**: `map` needs `[Algebra A B] [IsScalarTower R A B]` — the
   statement carries exactly mathlib's variable set (checked against the pin).
3. **`1 ⊗ₜ x` chart tuple**: over `A` the chart tuple is `fun i => (1 : A) ⊗ₜ[R] x i`;
   over `B` it must be `(1 : B) ⊗ₜ[R] x i` NOT `algebraMap A B 1 ⊗ …` — the
   `IsScalarTower` square makes these agree; a `simp`-level identification, recorded.

### [GR-B]
1. **Complement indexing**: `{j // j ∉ Set.range ι}` vs `Finset` complement — subtype
   form composes with `Pi` bases cleanly (`Equiv.piEquivPiSubtypeProd`-family); DecEq on
   `Fin n` gives decidability of membership in `Set.range ι` (`Fintype` on range).
2. **"φ freely determined"**: the equiv is `φ ↦ φ ∘ single` on complement coordinates;
   inverse assembles a linear map from prescribed values on ALL basis vectors
   (`Pi.basisFun.constr`); the retraction constraint pins the `range ι` block to the
   identity — surjectivity of the assembled φ is NOT needed for the equiv itself.
3. **n < k degenerate case**: `ι : Fin k ↪ Fin n` forces `k ≤ n`; no hypothesis needed —
   the embedding carries it. `k = 0`: both sides singleton (φ = 0 map into `Fin 0 → R`);
   fine.

## Skeleton & status

Wave-1 skeleton: `ForMathlib/GrassmannianChart.lean` — [GR-A0] def + [GR-A1]/[GR-A2]/
[GR-B] `:= by sorry`/`:= sorry`, must build green as its own target. Root registration
deferred (standing sweep-hazard note). Execution order: A1 → B → A2.

## Board

Wave-1 leaves boarded §v10.44c (claimed fable-FP). Wave-2/3 leaves live in this artifact;
boarded at each wave boundary per the v10.24 decision above.
