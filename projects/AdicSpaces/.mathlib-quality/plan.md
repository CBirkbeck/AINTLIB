# Development Plan: Finite-jet pinching — a uniform, sheafy, non-noetherian domain that is not stably uniform

**Campaign 4** (started 2026-07-16). Supersedes nothing — the Wedhorn-828b campaign is complete
(`plan-wedhorn828-archived-2026-07-16.md`); this campaign **consumes** its main theorem.

## Goal

Formalise the construction and headline properties of the finite-jet pinching algebra 𝔄 from
**[FJP]** = *"Finite-jet pinching: a uniform strongly sheafy domain which is not stably uniform"*
(Anonymous, 16 July 2026, 27 pp. — local file `refs/AdicSpaces/sheafyring.pdf`; **never commit
the PDF**). §7 (derived/condensed) is explicitly OUT of scope per the owner.

With `F : Type* [Field F]`, `K := LaurentSeries F` (the project's standard complete discretely
valued base field, `ExampleLaurentSeries.lean`), and the rings defined in the Construction layer
below, the targets are, in priority order:

```lean
-- (1) PRIORITY — Theorem 5.3 of [FJP]
theorem FiniteJet.isSheafy : ValuationSpectrum.IsSheafy (𝓐 F)

-- (2) Proposition 2.3 of [FJP]
theorem FiniteJet.isUniform : TopologicalRing.IsUniform (𝓐 F)
instance FiniteJet.isDomain : IsDomain (𝓐 F)

-- (3) Proposition 2.4 of [FJP]
theorem FiniteJet.not_noetherian : ¬ IsNoetherianRing (𝓐 F)

-- (4) Corollary 3.2 of [FJP]  (via Prop 3.1: 𝓐⟨W/ϖ⟩ ≅ K⟨X,Q⟩/(Q²))
theorem FiniteJet.not_stablyUniform : ¬ TopologicalRing.IsStablyUniform (𝓐 F)

-- (5) STRETCH — Corollary 5.5 of [FJP] (strong sheafiness); ticketed M7, not on the critical path
```

`IsSheafy`, `IsUniform`, `IsStablyUniform` are the project's own classes
(`StructureSheaf.lean:386`, `Uniform.lean:43/50`), so (1)–(4) formalise exactly the paper's
Theorem 1.3 (minus "strongly", which is the stretch) **in the vocabulary the 828b campaign
already established**. The owner's instruction: *prioritise sheafiness, and check the paper's
proofs very carefully for mistakes* — hence the decomposition (`decomposition.md`) runs the full
adversarial discipline and two independent referee passes on the paper were commissioned before
ticketing (verdicts recorded in `decomposition.md` §0).

## References

- **[FJP]** the paper itself — sole mathematical source; every leaf carries a verbatim quote.
- **[BV]** Buzzard–Verberkmoes, *Stably uniform affinoids are sheafy* (J. reine angew. Math. 740
  (2018)) — background only; [FJP] §1 translates its bounded-denominator language.
- **[HK]** Hansen–Kedlaya, *Sheafiness criteria for Huber rings* (2025-04-23 version) — Remark
  3.16 is the question [FJP] answers; not needed for any proof.
- **[Wedhorn]** via the completed 828b campaign: we do **not** re-read Wedhorn; we consume
  `isSheafy_of_stronglyNoetherian_828b`.
- Mathlib: `AdicCompletion.flat_of_isNoetherian` (Stacks 00MB is IN mathlib),
  `RingTheory.LocalProperties.Submodule` (localisation-detects-⊥/⊤),
  `ContinuousLinearMap.exists_preimage_norm_le` (Banach OMT with constants),
  `DualNumber`/`TrivSqZeroExt`, `AddMonoidAlgebra` (`IsDomain R[A]` under `UniqueProds`).

## What we consume from the completed campaigns (all verified to exist; file:decl in survey)

| Piece | Where | Used for |
|---|---|---|
| `isSheafy_of_stronglyNoetherian_828b` (bundle: `CommRing, TopologicalSpace, PlusSubring, IsTateRing, IsStronglyNoetherian, T2Space, IsRingOfIntegralElements A⁺, CompleteSpace(right unif.)` — **no `IsDomain`**) | `WedhornCechAcyclicity.lean:13373` | `IsSheafy` for the three comparison vertices 𝓑, 𝓒, 𝓓 (𝓑, 𝓓 are non-reduced — the bundle permits this) |
| `IsSheafy` class (embedding + gluing over `RationalCovering`/`IsRational`) | `StructureSheaf.lean:386` | statement target for 𝓐 |
| `sectionEqualizer_isClosed`, `isInducing_of_closedRange_of_topNilpUnit` (σ-compact-free OMT) | `StructureSheaf.lean:297`, WCA | the embedding field for 𝓐, mirroring the 828b assembly at WCA:13388 |
| `spaComap` / `comap_mem_spa` (contravariant Spa functoriality on points) | `AdicSpectrum.lean:256–274` | coverage transfer to the vertices |
| Vendored Gauss stack: `MvPowerSeries.Restricted R c`, `PowerSeries.Restricted R c`, norms, `isCompleteSpace`, `finSuccEquiv` isometry, `isAbsoluteValue` | `Vendored/Coram*.lean` | 𝓒 := `Restricted 𝓛 1`; norm multiplicativity; completeness |
| Disc-example instance pattern + `exists_flatten'`, `congrBase`, `restrictedGaussEquiv` | `ExampleUnitDisc.lean` | strong noetherianity of vertices by flattening to `K`; norm/topology bridge |
| `IsStronglyNoetherian K`, `IsTateRing K`, `NormedField K`, `CompleteSpace K`, pods | `ExampleLaurentSeries.lean`, `ExampleUnitDisc.lean` | the base field package |
| `IsTateRing.quotient`, `PairOfDefinition.quotient` | `QuotientTate.lean` | (fallback only; the chosen models avoid quotient topologies) |
| `IsStrictMap`/`IsStrictLinearMap`, module-topology OMT (Wedhorn 6.18) | `NoetherianTateModules.lean` | strictness in the graph–Koszul lemma |
| `Ideal.isClosed_of_le_jacobson` (Krull-based closedness) | `IdealClosedness.lean` | closedness of graph ideals at noetherian level |
| `TopologicalRing.IsUniform`, `IsStablyUniform`, `powerBoundedSubring` | `Uniform.lean`, `Bounded.lean` | statements (2), (4) |
| `RationalLocData`, `presheafValue`, `restrictionMap`, `HasLocLiftPowerBounded` | `Presheaf.lean` | the localisation vocabulary |

**V0 verification gate (first ticket):** `lean_verify` on `isSheafy_of_stronglyNoetherian_828b`
and `isSheafy_unitDisc`. The board (2026-06-09) recorded `sorryAx` with 4 leaves; commits
43f1b763f/d1e20127e (July) claim the disc chain is now axiom-clean; file-level greps still show
sorries in `WedhornCechAcyclicity.lean`(9)/`Cor832.lean`(18)/`FaithfulLocLift.lean`(16) which are
believed off the dependency cone. **Nothing in this campaign is DONE-flagged until V0 confirms
the consumed theorem is sorry-free on its cone.** If V0 fails, the failing leaves become
prerequisite tickets (they were 4 known leaves in June; the delta work is bounded).

## Design decisions (1d) — the construction layer

**DD1 (base field).** Fix `K := LaurentSeries F` as in the disc example. [FJP] works over an
abstract complete discretely valued k; the paper's discreteness is load-bearing (noetherian k°,
attained norms, residue arguments), and `K` is the project's canonical such field with the whole
instance stack already proven. Generalisation to abstract discretely-valued normed fields is a
post-campaign cleanup, not scope.

**DD2 (the Laurent ring 𝓛 = K⟨W,W⁻¹⟩ — the one genuinely new analysis object).** New type
`RestrictedLaurent K`: ℤ-indexed restricted series `{f : ℤ → K // Tendsto (‖f ·‖) cofinite (𝓝 0)}`
with convolution product (tsum; needs `CompleteSpace K`) and sup norm (attained; discrete value
group). API: `NormedCommRing`, `IsUltrametricDist`, `CompleteSpace`, norm-multiplicativity
(min-index achiever argument, mirroring `CoramMvRestrictedNorm.isAbsoluteValue`), monomials
`single a c`, the unit `Wu : (RestrictedLaurent K)ˣ` with `‖Wu‖ = ‖Wu⁻¹‖ = 1`, coefficient
functionals (norm-1), density of Laurent polynomials, `nonnegSubring` (support ⊆ ℕ) and the
norm-preserving iso `nonnegEquiv : nonnegSubring ≃+* PowerSeries.Restricted K 1`.
*Rejected alternative*: `LaurentTateAlgebra K = K⟨X,Y⟩/(XY−1)` (exists algebraically,
`TateAlgebra.lean:177`) as the primary carrier — it has no norm, and the whole §2–§3 analysis
is coefficientwise; the series model is the paper's own working description ((1.8) and Prop 2.3).
The affinoid presentation is kept as a **theorem** (surjection `K⟨W,V,Z…⟩ ↠ 𝓛⟨Z…⟩`, DD5).

**DD3 (jet vertices as dual numbers — kills two survey gaps).** There is no quotient-norm API in
the project, and none is needed:
- `𝓑 := DualNumber (PowerSeries.Restricted K 1)` (= K⟨W⟩[Q]/(Q²) with max norm),
- `𝓓 := DualNumber (RestrictedLaurent K)` (= 𝓒/(Q²) with max norm),
with a new small `NormedCommRing (DualNumber R)` instance layer (max norm; submultiplicative by
the ultrametric inequality; complete as a product). The paper's quotient-norm computations
(Lemma 2.2's `‖f₀+Qf₁‖ = max`) become definitional. The presentations 𝓑 ≅ K⟨W,Q⟩/(Q²),
𝓓 ≅ 𝓒/(Q²) are theorems used only where needed (noetherianity via DD5; the truncation map).

**DD4 (𝓒 and 𝓐).** `𝓒 := PowerSeries.Restricted (RestrictedLaurent K) 1` — the vendored
univariate stack over base 𝓛 gives ring, norm, ultrametric, completeness for free.
`ρC : 𝓒 →+* 𝓓` is 2-jet truncation `c ↦ (coeff 0 c, coeff 1 c)` (norm-1, strict, with the
norm-1 section (a,b) ↦ a + Qb). **𝓐 is NOT a new type**: it is the *closed subring*
`𝓐 := {c ∈ 𝓒 | coeff 0 c ∈ nonnegSubring ∧ coeff 1 c ∈ nonnegSubring}` (paper (1.7)/(1.8):
support `S = {(a,b) : b ≤ 1 → a ≥ 0}`), with the subring norm. The Milnor square is then a set
of *theorems*: `jB : 𝓐 →+* 𝓑` (truncate, corestrict), `ιC : 𝓐 →+* 𝓒` (inclusion, isometric),
`ρB : 𝓑 →+* 𝓓` (componentwise `nonneg ↪ 𝓛`), and the strict exact row
`0 → 𝓐 → 𝓑 ⊕ 𝓒 → 𝓓 → 0` with **all constants = 1** ([FJP] (2.1b): κ = ρ = 1). No
fiber-product type, no pullback API. Rejected: a `TrivSqZeroExt`-style pullback structure — the
subring model is the paper's own Lemma 2.2 and makes §2 coefficientwise.

**DD5 (noetherianity flow).** Everything reduces to `IsStronglyNoetherian K` (have) through two
engines: (i) *flattening*: `𝓒⟨Z₁..Zₙ⟩ ≅ 𝓛⟨Q,Z₁..Zₙ⟩` and `DualNumber R⟨Z⟩ ≅ DualNumber (R⟨Z⟩)`
(coefficientwise isos, vendored `exists_flatten'` pattern); (ii) *presentation*: a **surjective**
bounded hom `K⟨W,V,Z₁..Zₙ⟩ ↠ 𝓛⟨Z₁..Zₙ⟩` (eval W↦Wu, V↦Wu⁻¹; surjectivity via the explicit
norm-preserving monomial section — no kernel identification needed, quotient-of-noetherian
suffices), plus `DualNumber S` noetherian for noetherian S (quotient of S[Q]). The integral
pods (`𝓑₀ = DualNumber (unit ball)` etc.) are noetherian via `k°⟨…⟩` noetherian
(AdicCompletion route: mathlib `AdicCompletion` + Noetherian; bridge via project
`AdicCompletionBridge.lean` where usable). **Never** via "noeth Tate ⇒ strongly noeth" or
"strongly noeth ⇒ noeth A₀" (both in the B2 log as false).

**DD6 (graph–Koszul without Koszul complexes).** Mathlib has no Koszul complex; [FJP] Lemma 4.2
is consumed only in exterior degrees ≤ 2 ((4.7)/(4.8)). State it concretely:
`d₁ : (P_E)^m → P_E`, `u ↦ Σ uᵢ(gTᵢ−fᵢ)` and `d₂ : ({p : Fin m × Fin m // p.1 < p.2} → P_E) → (P_E)^m`,
`v ↦ fun j => Σ_{i<j} vᵢⱼrᵢ − Σ_{j<k} vⱼₖrₖ` (the paper's sign convention on ordered pairs; no
exterior algebra). The three payloads, for E affinoid with noetherian pod:
(a) `I_E := range d₁` closed and `d₁` strict-with-constant;
(b) `ker d₁ = range d₂` with lifting constant (m = 1: `gT−f` is a nonzerodivisor — degenerate case
proved separately);
(c) both transported to `P_E = E⟨T⟩` from the polynomial level by flat base change
(`AdicCompletion.flat_of_isNoetherian` + localisation), where the polynomial level is proved by
the two-case prime-local argument (coordinate-sequence syzygy induction — elementary — + unit
scaling + translation + `Submodule.eq_top_of_localization_maximal`). Strictness constants via
`ContinuousLinearMap.exists_preimage_norm_le` on the closed images (Banach OMT), with closedness
from the noetherian module theory (`NoetherianTateModules.lean` + f.g.-submodule completeness).

**DD7 (transfer target and the functoriality mini-layer).** The paper's §5 is re-targeted at the
project's `IsSheafy` (rational coverings only — the paper's "all opens via (5.9)" tail is NOT
needed). New layer, for `φ : 𝓐 →+* E` bounded into each vertex:
`RationalLocData.map φ` (pod ↦ concrete vertex pod; `hopen` via the generic span-⊤/principal-pod
lemma), `presheafValueMap : presheafValue D →+* presheafValue (D.map φ)`
(`IsLocalization.Away.map` + locTopology continuity + `Completion.map`), naturality with
`restrictionMap` (`IsLocalization.ringHom_ext` + completion-extension uniqueness), intersection
data, and the **graph bridge** `presheafValue D ≃+* P_E ⧸ I_E` (topological; both directions via
universal properties; `I_E` closed supplied by DD6 for vertices and by Lemma 4.3 for 𝓐 —
the `IsUnit (canonicalMap s)` input needed on the 𝓐 side is the D′=D case, which is trivially
true in `Localization.Away`). **`HasLocLiftPowerBounded 𝓐`** (required by the `IsSheafy`
statement; the existing discharger is noetherian-bound) is derived componentwise through the
Milnor iso from the vertices' instances — dependency-ordered so no circularity:
graph bridges → Milnor iso at every datum → `HasLocLiftPowerBounded 𝓐` → `restrictionMap`
vocabulary for 𝓐 → transfer.

**DD8 (statement shapes).** One conclusion per declaration throughout (gate 7): the paper's
Theorem 1.3 is five separate declarations; Prop 2.1's four claims are four lemmas; (5.2)'s four
plus-ring computations are four lemmas; etc.

## File structure (new files; flat, matching project convention)

| File | Contents | [FJP] |
|---|---|---|
| `Adic spaces/RestrictedLaurent.lean` | DD2: 𝓛 core | §1 conventions, Prop 2.3 (norm) |
| `Adic spaces/JetDualNumberNorm.lean` | DD3: normed `DualNumber R` layer | §1.4–(1.5) |
| `Adic spaces/FiniteJetRings.lean` | 𝓑 𝓒 𝓓 𝓐, maps, Milnor row, instance stacks | Def 1.2, Prop 2.1, Lemma 2.2, (2.1a–b), (5.1)–(5.2) |
| `Adic spaces/FiniteJetUniformDomain.lean` | uniform, domain, 𝓐° = 𝓐₀, not-noetherian | Prop 2.3, 2.4 |
| `Adic spaces/FiniteJetNoetherianVertices.lean` | DD5 + `IsSheafy` for 𝓑 𝓒 𝓓 via 828b | Prop 2.1 (strong noeth), Thm 5.3 (input) |
| `Adic spaces/FiniteJetGraphKoszul.lean` | DD6 | Lemma 4.2 |
| `Adic spaces/FiniteJetStrictLocalization.lean` | Tate extension, ideal pullback, quotient lemma, strict Milnor localisation | Lemmas 4.1, 4.3, 4.4, Prop 4.5, (4.21a–b) |
| `Adic spaces/FiniteJetFunctoriality.lean` | DD7 mini-layer + graph bridges + `HasLocLiftPowerBounded 𝓐` | Lemma 1.1, Lemma 4.6, Lemma 5.1 |
| `Adic spaces/FiniteJetSheafTransfer.lean` | gluing + embedding transfer → `IsSheafy 𝓐` | Lemma 5.2, Thm 5.3 |
| `Adic spaces/FiniteJetChart.lean` | 𝓐⟨W/ϖ⟩ ≅ 𝓑, non-uniformity, ¬stably-uniform | Prop 3.1, Cor 3.2 |
| `Adic spaces/FiniteJetMain.lean` | headline assembly (5 declarations) | Thm 1.3 |

## Dependency graph / milestones (M2′ is parallel to M3–M6; sheafiness chain is the spine)

```
M0 V0-verify ─┬─ M1 RestrictedLaurent + DualNumber norm + rings + Milnor row (files 1–3)
              │        │
              │        ├── M2 vertices strongly-noetherian + IsSheafy 𝓑𝓒𝓓 (file 5)
              │        ├── M2′ uniform + domain + ¬noetherian (file 4)   [parallel track]
              │        └── M3 graph–Koszul (file 6)
              │                 │
              │                 └── M4 strict localisation (file 7)
              │                          │
              │                          └── M5 functoriality + bridges + HasLocLift 𝓐 (file 8)
              │                                   │
              │                                   ├── M6 sheaf transfer → IsSheafy 𝓐 (file 9)  ★ PRIORITY
              │                                   └── M5′ chart + ¬stably-uniform (file 10)
              └──────────────────────────────────────── M-FINAL assembly (file 11) ← M6, M2′, M5′
                                                        M7 (stretch) strong sheafiness
```

## Mathlib inventory (headline items; full per-leaf citations in `decomposition.md`)

| Concept | Status | Action |
|---|---|---|
| Koszul complex | **absent** | DD6 concrete degrees ≤ 2; never build the complex |
| Flatness of adic completion (00MB) | `AdicCompletion.flat_of_isNoetherian` | USE |
| Regular sequences | `RingTheory.Sequence.IsRegular` | only the coordinate case, proved directly |
| Local-global for submodules | `Submodule.eq_(bot|top)_of_localization_maximal` | USE |
| Banach OMT with constant | `ContinuousLinearMap.exists_preimage_norm_le` | USE |
| `DualNumber`/`TrivSqZeroExt` | present (no norm) | small normed layer (DD3) |
| `AddMonoidAlgebra` domain (`UniqueProds`) | present | residue-reduction route for 𝓛-multiplicativity (or achiever route; leaf picks) |
| ℤ-indexed restricted series | **absent** (also absent in project) | DD2 new |

## Generality decisions

- Concrete base `K = LaurentSeries F` (DD1); `F` an arbitrary field — everything is
  `variable (F : Type*) [Field F]`.
- The strict-localisation layer (M3–M4) is stated for an **abstract strict Milnor square of
  normed Tate K-algebras with noetherian-pod affinoid vertices** where that is free (it nearly
  always is — the paper's §4 is already abstract), so the finite-jet square is one instance and
  §6's d ≥ 2 family (out of scope) would be another.
- Norm-first: all four rings are normed; topological-ring statements are derived through the
  established norm/topology bridge pattern (`ExampleUnitDisc.lean` §Bridge), never by re-deriving
  topology from pods.

## Risk register (each has a mitigation ticket)

1. **V0**: consumed 828b theorem not axiom-clean → prerequisite tickets (bounded: 4 known leaves).
2. **Vendored univariate multiplicativity over base 𝓛** — exact hypothesis shape of
   `Restricted.gaussNorm_mul_eq_mul` unverified → if it mismatches, prove 𝓒-multiplicativity
   directly by the ℤ×ℕ-lex achiever argument (leaf provided).
3. **`hopen` for pushed data** — believed generic for span-⊤ data over principal pods (proof
   sketch in decomposition); if the generic lemma fails, prove per-vertex concretely.
4. **Graph bridge for 𝓐** (Lemma 1.1 both-directions) is the most delicate glue; it is isolated
   in M5 with its own sub-decomposition and does not block M2′.
5. **`IsRingOfIntegralElements 𝓑⁺/𝓓⁺`** — the plus rings are *unbounded* (paper (5.2)); the
   class permits this (`AffinoidRings.lean:47` has no boundedness field) — verified at
   decomposition time, leaf records it.

## Ticket board

`tickets.md` (same directory) — created from the decomposition's verified leaves, with the
cleanup cadence (per-file every 3 proof tickets + final per-file + pre-milestone
`/cleanup-all` + `CLEANUP-FINAL`). Workers run via `/beastmode`.
