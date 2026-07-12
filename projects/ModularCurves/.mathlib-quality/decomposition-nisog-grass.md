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

**Wave 2.5 — presentation normalization (pinned at the wave-3 boundary, 2026-07-08T22:30Z;
kills the `A ⊗[R] (Fin n → R)` vs `(Fin n → A)` friction for the entire glue phase)**:
- **[GR-T1]** `Grassmannian.congr (e : M ≃ₗ[R] M') : G(k, M; R) ≃ G(k, M'; R)` — transport
  of Grassmannian elements along a module equivalence (submodule `Submodule.map`, quotient
  instances via the induced quotient equivalence), with `IsChartAt`-compatibility
  (`isChartAt_congr : IsChartAt x N ↔ IsChartAt (e ∘ x) (congr e N)`). Upstream-shaped
  (mathlib's Grassmannian file has no congr).
- **[GR-T2]** the pi-normalization at `e := piScalarRight`: chart-compatible passage
  `G(k, A ⊗[R] (Fin n → R); A) ≃ G(k, (Fin n → A); A)` matching the wave-1 matrix leaf's
  presentation; the covering theorem [GR-C] transports along it.

**Wave-3 packaging decision (2026-07-08T22:35Z, binding for the glue phase)**: all wave-3
work happens in the NORMALIZED presentation `G(k, (Fin n → A); A)` — the functor map is
`normMap (f : A →ₐ[R] B) := congr (piScalarRight …) ∘ map f ∘ congr (piScalarRight …).symm`
(equivalently: transport mathlib's `Grassmannian.map` once along [GR-T2]); charts are the
coordinate tuples `fun i => Pi.single (ι i) 1`, matrices are
`chartMatrix : {j // j ∉ Set.range ι} → Fin k → A` via wave-1's
`chartEquivRetraction ≫ retractionEquivMatrix`. Tensors never appear downstream of this
seam. Leaves: **[GR-B2n]** = `normMap` + `isChartAt_normMap` + `chartMatrix` +
`chartMatrix_normMap` (naturality: entrywise `f`).

**[GR-E] transition design (pinned 2026-07-09T08:30Z, against the proven wave-1/2.5
interface; execution in NEW `ForMathlib/GrassmannianTransition.lean` to keep the chart
file single-writer)**:
- Setting: `ι ι' : Fin k ↪ Fin n`; `N` in the ι-chart with retraction `φ` (the
  `chartMatrix` data). The ι'-tuple's images under `φ` assemble the **transition
  matrix** `T : Matrix (Fin k) (Fin k) A`, `T i₁ i₂ := φ (Pi.single (ι' i₂) 1) i₁` —
  entries are `chartMatrix`-entries when `ι' i₂ ∉ range ι` and Kronecker deltas when
  `ι' i₂ = ι i` (the retraction condition pins those columns).
- **[GR-E1]** `chartTransitionMatrix` (def, from `chartMatrix` + the dichotomy on
  `ι' i₂ ∈ range ι`) + its two computation lemmas (delta-column / matrix-column).
- **[GR-E2]** the overlap criterion: `IsChartAt (ι'-tuple) N ↔ IsUnit (chartTransitionMatrix …).det`
  — proof: quotient-composite₂ = (Matrix.toLin' T) ≫ composite₁-iso, so bijective ⟺ `T`
  invertible ⟺ `IsUnit T.det` (`Matrix.isUnit_iff_isUnit_det` / `LinearMap.isUnit_det…`;
  the factorization is a `Basis.ext` check on singles via `retraction_comp_coordMap`).
- **[GR-E3]** coordinate transition: over the overlap, the ι'-matrix of `N` =
  (adjugate/det-inverse formula) in the ι-matrix — extracted as the RING-map statement
  `MvPolynomial ({j ∉ range ι'} × Fin k) R →+* Localization.Away (transitionDet ι ι')`
  on the generic matrix ring (`transitionDet ι ι' := (chartTransitionMatrix of the
  generic matrix).det : MvPolynomial ({j ∉ range ι} × Fin k) R`), with the spec lemma
  tying it to [GR-E2]'s pointwise transition. This is the glue datum for [GR-F].
- **[GR-E4]** cocycle on triple overlaps (localized ring maps compose per the pointwise
  spec — prove POINTWISE first via chartMatrix-uniqueness, lift by `IsLocalization`
  epi-ness/`ringHom_ext`).
- Attack notes: (1) all statements at a GENERIC element `N` with hypotheses `IsChartAt`
  — never applied to `normMap`-terms (memory: normMap-poisoning); (2) matrix-vs-function
  seams via `Matrix.toLin'`/`Matrix.mulVec` with `Pi.basisFun`-ext everywhere; (3) the
  generic-matrix ring statements are pure `MvPolynomial`/`Matrix` algebra — zero
  Grassmannian dependence — so [GR-E3/E4]'s ring layer is dispatchable independently of
  [GR-E1/E2].

**[GR-SPEC] the ringHom↔chartMatrix bridge (pinned 2026-07-09T09:40Z; the last algebra
before [GR-F])**: for `N` in both charts (`h : IsChartAt ι`, `h' : IsChartAt ι'` over
`A`): (i) `evalAt h : ChartRing R ι →+* A` := `aeval (p ↦ chartMatrix n ι N h p.1 p.2)`
(precisely: the `MvPolynomial.aeval`/`eval₂Hom` at the chart matrix); (ii) bridge lemma
`evalAt_matrix : (Transition.matrix ι ι').map (evalAt h) = transitionMatrixAt ι ι' N h`
(entrywise: `column`-dichotomy vs the pointwise retraction values — delta columns match
by the retraction property, variable columns by `aeval_X`); (iii) hence
`IsUnit (evalAt h (Transition.det ι ι'))` from [GR-E2]+h' (`RingHom.map_det` transport);
(iv) `evalAwayAt h h' : Localization.Away (Transition.det ι ι') →+* A` :=
`IsLocalization.Away.lift` of (iii); (v) **the SPEC**:
`(evalAwayAt h h').comp (Transition.ringHom ι ι') = evalAt h'` — two ring maps out of
`MvPolynomial`, ext on generators (`MvPolynomial.ringHom_ext`); at `X (j', i')` the
claim is `(transitionMatrixAt⁻¹ *ᵥ pointwise-column j') i' = chartMatrix n ι' N h' j' i'`
— prove via `chartMatrix_eq_of_retraction` (the composite `toLin' T⁻¹ ∘ (ι-retraction)`
is a retraction of the ι'-tuple killing `N.toSubmodule`; same shape as the naturality
proof). [GR-E4]'s cocycle then LIVES inside [GR-F]'s `Scheme.GlueData` t-composition
condition, verified pointwise through [GR-SPEC] — no standalone generic-ring cocycle
statement needed (design decision; kills the triple-localization bookkeeping).

**[GR-F] GlueData architecture (pinned 2026-07-09T23:00Z, after the E4 inverse-pair)**:
mathlib `Scheme.GlueData` (CategoryTheory.GlueData fields J/U/V/f/t/t_id/t'/t_fac/cocycle):
- `J := Fin k ↪ Fin n` · `U ι := Spec (ChartRing R ι)` · `V (ι,ι') := Spec (Away (det ι ι'))`
  — note `matrix ι ι = 1` so `det ι ι = 1` and `V(ι,ι) ≅ U ι` as required;
- `f ι ι' := Spec.map (algebraMap …)` — open immersion by the `IsOpenImmersion`-of-
  localization instance;
- `t ι ι' := Spec.map (ringHomAway ι ι')` (contravariance puts my `Away(det ι'ι) →+*
  Away(det ιι')` in the right direction); `t_id` ⟸ **[GR-F-tid]** `ringHomAway ι ι = id`
  (matrix ι ι = 1 ⟹ ringHom ι ι = algebraMap ⟹ lift = id by `IsLocalization` ext);
- `t' i j k := pullback.lift` of the two legs; `pullback (f i j) (f i k)` ≅ Spec of the
  double localization (`pullbackSpecIso`); **the crux [GR-F3]**: the leg
  `P(ι;ι',ι'') ⟶ V(ι',ι'')` needs the ring map `Away (det ι' ι'') →+* D(ι;ι',ι'')`
  (double localization) — exists because the `ringHom ι ι''`-image of `det ι' ι''`
  becomes a unit once `det ι ι'` is ALSO inverted: the generic composite-matrix identity
  `(matrix ι' ι'').map (into-double) = Minv(ιι')-image * matrixAway(ιι'')-image`-form
  (proof by the master column identity `ringHom_comp_column`, two applications);
- `t_fac` by `pullback.lift_snd/fst`; `cocycle` by `pullback.hom_ext` + both projections
  reduced to ring-level composites, closed by [GR-E4]'s inverse-pair + [GR-F3] +
  `IsLocalization.ringHom_ext`² on the double localizations. No tensor-algebra of Aways
  needed anywhere (all maps built by universal properties, never by explicit tensors).
- **t'-leg refinement (2026-07-10, post-F3)**: with `D := Away(det ιι') ⊗[ChartRing ι]
  Away(det ιι'')` (the `pullbackSpecIso` presentation), set `base₁ : ChartRing ι' →+* D
  := includeLeftRingHom ∘ ringHom ι ι'`. Then: leg from `Away(det ι'ι)` :=
  `Away.lift base₁` at `det ι'ι` — unit by [GR-F1] `isUnit_ringHom_det` mapped along
  includeLeft; leg from `Away(det ι'ι'')` := `Away.lift base₁` at `det ι'ι''` — unit by
  [GR-F3] `isUnit_map_ringHom_det_triple` with `g := includeLeftRingHom`, whose `hg`
  (embedded `det ιι''` is a unit in D) holds by the BASE-ELEMENT SLIDE:
  `algebraMap(d'') ⊗ₜ 1 = 1 ⊗ₜ algebraMap(d'')` in `S ⊗[A] T` for `d'' ∈ A`, and the
  right side is `includeRight` of a unit of `Away(det ιι'')`. The two legs share `base₁`
  so `Algebra.TensorProduct.lift`-compatibility over `ChartRing ι'` is definitional
  (commutativity of images is trivial in the commutative D). t'-scheme :=
  `(pullbackSpecIso ι-side).hom ≫ Spec.map (ofHom t'ring) ≫ (pullbackSpecIso ι'-side).inv`.

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
