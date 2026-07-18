# Decomposition — Manin ideal-triangle fundamental-domain infrastructure (ES-4, `k ≥ 2`)

**Target.** `exists_manin_fundDomain_boundary_period`
(`HeckeRIngs/GL2/ModularSymbols/PeterssonStokes.lean` ~:2458), the lone residual `sorry`
of the integral Eichler–Shimura `k ≥ 2` substrate:

```lean
theorem exists_manin_fundDomain_boundary_period (hk : 2 ≤ k)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    ∃ (D : Set UpperHalfPlane) (_ : IsFundamentalDomain (imageGamma1_PSL N) D μ_hyp)
      (B : PairedBoundary N) (P : SymPow ℤ (k - 2).toNat) (c : ℂ),
      (∫ τ in D, petersson k ⇑f ⇑g τ ∂μ_hyp) +
          ((-1 : ℂ) ^ (k - 2).toNat) • ∫ τ in D, petersson k ⇑g ⇑f τ ∂μ_hyp =
        c * rawPairing f (B.boundaryDivisor ⊗ₜ P)
```

The model-change half (`symmetrised_petersson_fundDomain_eq`) is **proven**: for *any*
`imageGamma1_PSL N`-fundamental domain `D`, the symmetrised area integral over the Siegel coset
tiling `Gamma1_fundDomain_PSL N` equals the one over `D` (free, via `IsFundamentalDomain.setIntegral_eq`
+ `petersson_imageGamma1_PSL_invariant`). What remains is the **genuine geometric core**: produce a
`D` whose boundary is a `Γ₁(N)`-paired cycle of rational-cusp geodesic edges, and identify its area
integral with `c · rawPairing f (∂D ⊗ P)` via region-Stokes over ideal triangles.

---

## 1. mathlib survey (exact decls)

### `Mathlib/NumberTheory/Modular.lean`  (`ModularGroup` FD theory)
| decl | provides |
|---|---|
| `ModularGroup.fd` (`𝒟`), `ModularGroup.fdo` (`𝒟ᵒ`) | the standard closed/open SL₂ℤ FD: `{ |Re|≤½ ∧ 1≤‖z‖ }` resp. strict |
| `coe_fd`, `coe_fdo` | `(↑)''𝒟 = {0<im ∧ 1≤‖z‖ ∧ |re|≤½}`, the **arc-`|z|=1` + verticals-`|re|=½`** region |
| `exists_smul_mem_fd (z)` | every `z` moves into `𝒟` by some `g : SL(2,ℤ)` (a.e.-cover input) |
| `eq_one_or_neg_one_of_mem_fdo_mem_fdo`, `c_eq_zero`, `eq_smul_self_of_mem_fdo_mem_fdo` | the disjointness core (`g•𝒟ᵒ ∩ 𝒟ᵒ ≠ ∅ ⟹ g = ±1`) |
| `fd_eq_closure_fdo`, `fdo_eq_interior_fd`, `isClosed_fd`, `isOpen_fdo` | topological glue |
| `truncatedFundamentalDomain (y)`, `isCompact_truncatedFundamentalDomain` | the **capped** FD `{τ ∈ 𝒟 ∧ im ≤ y}`, compact |
| `ρ_mem_fd`, `I_mem_fd`, `ρ` (`ModularGroup.ρ`) | the corners `ρ = e^{2πi/3}`, `I` |
| `S`, `T`, `coe_T_zpow_smul_eq`, `g_eq_of_c_eq_one`, `exists_eq_T_zpow_of_c_eq_zero` | generator reduction |

**There is NO `IsFundamentalDomain` instance in `Modular.lean`** — mathlib never proves `𝒟`/`𝒟ᵒ` is
an `IsFundamentalDomain` for the measure-theoretic action. (Confirmed: `grep IsFundamentalDomain
Mathlib/NumberTheory/` is empty.) The project supplies it itself (see §2, `isFundamentalDomain_fdo_PSL`).

### `Mathlib/MeasureTheory/Group/FundamentalDomain.lean`  (`IsFundamentalDomain` API)
| decl | provides |
|---|---|
| `IsFundamentalDomain` (structure) | `nullMeasurableSet ∧ ae_covers ∧ aedisjoint` |
| `IsFundamentalDomain.mk'` / `mk''` / `mk_of_measure_univ_le` | constructors (unique-`g`, a.e.-cover, finite-measure) |
| `IsFundamentalDomain.setIntegral_eq` | **the model change** — two FDs of same group give equal set-integrals of an invariant fn (already used by `symmetrised_petersson_fundDomain_eq`) |
| `.image_of_equiv`, `.preimage_of_equiv`, `.smul`, `.smul_of_comm` | transport along equivs / group elts |
| `.integral_eq_tsum_of_ac`, `.setIntegral_eq_tsum` | unfold an integral as a coset tsum |
| `.measure_eq_card_smul_of_smul_ae_eq_self` | measure of invariant set |
| `fundamentalInterior` / `fundamentalFrontier`, `pairwise_disjoint_fundamentalInterior` | interior/frontier split |

**There is NO `IsFundamentalDomain.union`/`.iUnion` combinator that glues several FDs of the *same*
group into one** (only the *subgroup*-tiling direction; see §2). This is the crux for shortcut (b).

### `Mathlib/NumberTheory/ModularForms/Cusps.lean`  (cusps)
| decl | provides |
|---|---|
| `OnePoint.exists_mem_SL2` (here on `OnePoint ℚ`/`ℝ`) | every cusp `= g • ∞` for some `g : SL(2,ℤ)` (transitivity) |
| `Cusps.IsCusp`, `isCusp_SL2Z_iff'` | `c` is an SL₂ℤ-cusp iff `c = mapGL ℝ g • ∞` |
| `Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z`, `CuspOrbits`, `surjective_cosetToCuspOrbit` | cusp orbits ↔ cosets |
| `strictWidthInfty`, `widthInfty`, `…_pos` | cusp widths (parabolic structure) |

### `Mathlib/Analysis/Complex/UpperHalfPlane/Metric.lean`  (hyperbolic geometry)
| decl | provides |
|---|---|
| `UpperHalfPlane.dist_eq`, `cosh_dist`, `tanh_half_dist` | the hyperbolic metric |
| `isometry_vertical_line (a)` | vertical lines are geodesics (isometric image of `ℝ`) |
| `image_coe_ball/closedBall/sphere` | hyperbolic balls = Euclidean balls (recentred) |
| `center z r` | hyperbolic centre |

**mathlib has NO geodesic-segment object** (no `geodesic`, no `[a,b]`-as-set in ℍ). Vertical lines
are the only geodesics named, via `isometry_vertical_line`. Möbius-arc geodesics between finite cusps
are not built. ⇒ (M1) "geodesic edge as a region/curve" has no mathlib foothold; but see §4 — the
*project already sidesteps this*: `cuspValue` is the vertical-ray integral, and the only contour ever
formed is the 5-segment `fdBoundaryFun` of the standard `fd`.

---

## 2. Project infra survey (exact decls)

### `Modularforms/PSL2Action.lean`
- **`isFundamentalDomain_fdo_PSL : IsFundamentalDomain PSL(2,ℤ) (fdo) μ_hyp`** — the project's
  hand-built FD for the standard open domain. `ae_covers` from `exists_smul_mem_fd` + null boundary
  (`hyperbolicMeasure_fd_boundary`); `aedisjoint` from `fdo_PSL_pairwise_disjoint`
  (`eq_smul_self_of_mem_fdo_mem_fdo`). **This is the only FD foundation in the whole project.**

### `Modularforms/PeterssonLevelN.lean`
- **`IsFundamentalDomain.subgroup_iUnion_out_smul`** (general): if `s` is a `G`-FD and `H ≤ G`, then
  `⋃_{q:G⧸H} (q.out)⁻¹ • s` is an `H`-FD. **The engine that builds every level-`N` FD from `fdo`.**
- **`IsFundamentalDomain.iUnion_smul_of_transversal`** — same, with an *arbitrary* complete transversal
  `r : ι → G` (`e : ι ≃ G⧸H`, `e i = ⟦(r i)⁻¹⟧`). **THE reusable tool for (M2)**: lets the geometric
  Manin coset reps replace the canonical `.out` reps.
- `IsFundamentalDomain.smul_of_eq_conjAct`, `.aedisjoint_smul_of_mul_inv_mem` — translate/conjugate FDs.
- `imageGamma1_PSL N := (Gamma1 N).map (mk' center)`; `Gamma1_fundDomain_PSL N := ⋃_q (q.out)⁻¹ • fdo`;
  `isFundamentalDomain_Gamma1_PSL` (= `.subgroup_iUnion_out_smul (imageGamma1_PSL N)`).
- `setIntegral_Gamma1_fundDomain_PSL_eq_sum`, `setIntegral_smul_eq` (`∫_{δ•S} h = ∫_S h(δ•·)`),
  `sum_SL_tile_eq_fiberwise_PSL_tile`, `setIntegral_SL_tile_eq_PSL_tile`,
  `hyperbolicMeasure_Gamma1_fundDomain_PSL_lt_top`, `integrableOn_petersson_Gamma1_fundDomain_PSL`.

### `ModularSymbols/FundamentalDomainBoundary.lean`  (the combinatorial boundary, all PROVEN)
- `OrientedCuspEdge` (`tail head : ℙ¹ℚ`), `edgeDivisor e = divDiff head tail`, `reverse`, `smul`,
  `edgeDivisor_reverse`, `edgeDivisor_smul` (= `div0Rep γ`).
- **`PairedBoundary N`** (structure): finite `ι`, `edge : ι → OrientedCuspEdge`, fixed-point-free
  involution `pair`, side-pairing `γ : ι → Gamma1 N`, relation `edge (pair i) = (edge i).reverse.smul (γ i)`.
- `boundaryDivisor B := ∑ i, edgeDivisor (edge i)`.
- **`rawPairing_edgeDivisor_eq_sub`** : `rawPairing f (∂e ⊗ P) = cuspValue f P (head e) − cuspValue f P (tail e)`
  — the edge period IS an endpoint-potential difference (THE bridge geometry→period).
- `edgePotential`, `edgePotential_chain_sum`, `edgePotentialSum_cycle_eq_zero` (abstract telescoping).
- **`two_smul_rawPairing_boundaryDivisor`** : `2 • rawPairing f (∂F ⊗ P) = ∑ᵢ (edge period − cocycle period)`
  — the paired-edge collapse, period level.
- `rawPairing_cocycle_summand`, `two_smul_boundaryDivisor_eq_cocycle_sum`.
- `exists_SL2Z_smul_eq_cusp` (cusp transitivity), `OrientedCuspEdge.exists_SL2Z_smul_tail_eq_head`.

### `ModularSymbols/PeterssonStokes.lean`  (region-Stokes, all PROVEN except the target + an internal sorry)
- **`tile_stokes_fd`** : for `g : ModularForm`, primitive `Fp` of `periodForm g P`, antiholo factor `a`,
  height `H>1`: `∃ Ibdry`, area integral of the exact 2-form over the **capped standard `fd`-tile**
  `{0<im ∧ 1<‖z‖² ∧ |re|<½ ∧ im<H}` `=` negated 5-segment contour integral over `fdBoundaryFun H`.
  *(Internally rests on `region_stokes_eq_neg_contour`, which has its own residual sorry — the
  Type-II ∂ₓ arc-strip split. Not on our critical path but co-located.)*
- `petersson_binomial_periodForm` / `petersson_binomial_complex` — the Sym-weight binomial bridge:
  Petersson integrand `= (2i)^{-(k-2)} Σⱼ C(k-2,j)(−1)^… periodForm g (symMon j)·conj(periodForm f (symMon …))`,
  each summand of `tile_stokes_fd` shape.
- `symMon`, `evalSym1_symMon`, `periodForm_symMon_apply`, `periodForm_hasDerivAt_and_continuousOn_deriv`.
- **`exists_tile_boundary_periodForm_term`** — per-binomial-term `tile_stokes_fd` (PROVEN).
- `petersson_imageGamma1_PSL_invariant`, **`symmetrised_petersson_fundDomain_eq`** (model change, PROVEN).
- `exists_pairedBoundary_fundDomain_petersson_eq` — the Siegel-domain twin of our target (delegates to it
  via the model change); `exists_pairedBoundary_periodPairingA_eq` (final assembly into `petN`).

### `ModularSymbols/PeriodInvariant.lean`  (cusp-edge period analysis, all PROVEN except 1 isolated input)
- **`Complex.isExactOn_upperHalf`** : holomorphic on `{0<im}` ⟹ has a global primitive (ball exhaustion).
- `periodForm f P`, `differentiableOn_periodForm`, `periodForm_norm_le` (cusp decay bound),
  `tendsto_horizontal_cap`, `tendsto_uniform_horizontal_cap`.
- `hasDerivAt_periodForm_primitive_vertical` / `_horizontal` — FTC for the primitive along verticals/horizontals.
- `botVal`, **`cuspValue_eq_top_sub_botVal`** : `cuspValue f P c = L − (botVal at finite cusp / L at ∞)`.
- `cuspToInftyIntegral_eq_top_sub_bot`, `tendsto_primitive_vertical_nhdsGT_zero`,
  `exists_tendsto_primitive_vertical_atTop`.
- `mob γ`, `periodForm_mob`, `hasDerivAt_primitive_mob`, `periodForm_mob_general`,
  `hasDerivAt_primitive_mob_general` (Möbius change-of-variables for the primitive, general `SL(2,ℤ)`).
- **`cuspBoundary_mob_naturality`** — the σ-conjugate cap argument (μ≡0); the one isolated analytic
  input (already absorbed in `PeriodInvariant`), giving `cuspValue_symRep_gamma`, `cuspDiff_const`,
  `isPeriodInvariant_all`. **Note: this proves the cusp-edge period is well-defined & Γ-covariant.**
- `cuspValue` is **defined** (`PeriodMap.lean:538`) as `cuspToInftyIntegral` = vertical-ray integral
  from cusp `q` to `i∞` (`0` at `∞`). `rawPairing f (D ⊗ P) = Σ_c D(c)·cuspValue f P c` (`PeriodMap.lean:623`).

### `ModularSymbols/FinitelyManyCusps.lean`
- `isPretransitive_SL2Z_projQQ` (SL₂ℤ transitive on `ℙ¹ℚ`), `instFiniteCuspsGamma1`.

---

## 3. Leaf decomposition

Two viable routes. **Route A (Manin FD, the literal target spelling)** builds a genuinely new ideal-
triangle `D`. **Route B (Siegel pass-through, the recommended one)** observes the target is *logically
equivalent* to `exists_pairedBoundary_fundDomain_petersson_eq` (already in the file) and only needs the
Siegel boundary period identity — no new `IsFundamentalDomain`. The decomposition lists Route A leaves
(the literal request) and flags where Route B short-circuits each.

### Build-order overview

```
            ┌─────────────────────────────────────────────────────────────┐
            │  (M0) area-integral → per-tile capped contour reduction      │  ← shared, hardest analytic glue
            └───────────────┬─────────────────────────────────────────────┘
   Route A                  │                         Route B (recommended)
   ┌────────────────────────┴───────────┐            ┌───────────────────────────┐
 (M1) ideal triangle T₀ + geodesic edges │          (B5) reuse Siegel D_N, build  │
 (M2) D = ⋃ γᵢ•T₀  +  IsFundamentalDomain │               PairedBoundary B from    │
 (M3) region-Stokes over a cusp triangle  │               the fd-tile side pairing  │
 (M4) PairedBoundary from T₀ side-pairing │          (B-period) M0 + cusp-edge id   │
 (M5) assembly → rawPairing f (∂D ⊗ P)    │               → rawPairing             │
   └────────────────────────┬─────────────┘            └───────────────────────────┘
                            ▼
        exists_manin_fundDomain_boundary_period
```

### (M0) Area-integral → boundary-period reduction  [the real long pole — RESEARCH]
**Statement (sketch).** For `f g` cusp forms `k ≥ 2`, the symmetrised area integral over a FD `D`
equals `c · rawPairing f (∂D ⊗ P)`, where the LHS is rewritten — via the binomial bridge
(`petersson_binomial_periodForm`) per coset tile, then `tile_stokes_fd` per binomial term — into a sum
of capped 5-segment contour integrals, whose `H → ∞` limit (cusp decay kills the top cap;
`tendsto_horizontal_cap`) plus the `Γ₁(N)`-side-pairing telescoping of interior edges
(`two_smul_rawPairing_boundaryDivisor`, `setIntegral_Gamma1_smul_eq`) collapses to the surviving outer
edges' FTC potentials = `cuspValue` differences (`hasDerivAt_periodForm_primitive_vertical`,
`cuspValue_eq_top_sub_botVal`).
**Foundation.** `tile_stokes_fd`, `petersson_binomial_periodForm`, `exists_tile_boundary_periodForm_term`,
`setIntegral_Gamma1_fundDomain_PSL_eq_sum`, `two_smul_rawPairing_boundaryDivisor`,
`cuspValue_eq_top_sub_botVal`, `tendsto_horizontal_cap` — **all proven**; the composite gluing them is not.
**Classification: RESEARCH.** This is precisely the residual the file's docstring (PeterssonStokes:2364)
calls "the research-scale long pole of ES-4": the μ_hyp↔planar measure conversion *on each translated
tile* (`tile_stokes_fd` is stated for the *standard* tile only), the `H→∞` cap limit, the coset
telescoping, and the **Manin↔Siegel model change** matching FTC edge potentials to `cuspValue`.
**LOC: 600–1200.**  **Biggest risk:** the interior-edge cancellation. Adjacent translated tiles
`(qᵢ.out)⁻¹•fdo` and `(qⱼ.out)⁻¹•fdo` share a 5-segment-arc boundary piece traversed in *opposite*
orientation; proving these cancel pairwise (so only the outer cusp edges survive) is the heart of the
side-pairing argument and has no mathlib analogue. *(Route B inherits M0 verbatim — it is unavoidable.)*

### (M1) The ideal triangle `T₀` + its geodesic edges  [API-GAP]
**Statement (sketch).** `def idealTriangle : Set ℍ` = the region bounded by three cusp-geodesics
(e.g. verticals `Re = 0`, `Re = 1` and the arc `|z − ½| = ½` joining `0,1`, with ideal vertex `∞`), and
its three `OrientedCuspEdge`s `{∞,0}, {0,1}, {1,∞}`. Prove it is measurable, has finite hyperbolic
measure, and its `(↑)`-image is a `regionBetween`-style set.
**Foundation.** `Modular.fd`/`coe_fd` (the standard `fd` IS half such a triangle — see (b)),
`isometry_vertical_line`, `regionBetweenX`, `mem_regionBetweenX` (PeriodInvariant region machinery).
**Classification: API-GAP.** No geodesic-segment object in mathlib, but the triangle is just an explicit
inequality region (verticals + one circle), expressible exactly as in `coe_fd`/`fdSet_image_eq_regionBetween`.
The edges as `OrientedCuspEdge` already exist (combinatorial). **LOC: 150–300.**  **Risk:** choosing the
triangle so that its `IsFundamentalDomain` is *founded* — see (b): take `T₀ = fd ∪ S•fd` so it is exactly
2 copies of `𝒟`.

### (M2) `D = ⋃ γᵢ • T₀`  +  `IsFundamentalDomain (imageGamma1_PSL N) D μ_hyp`  [API-GAP, given (b)]
**Statement (sketch).** With `T₀` an SL₂ℤ-FD-equivalent ideal triangle and a complete transversal
`r : ι → PSL(2,ℤ)` of `imageGamma1_PSL N`, set `D = ⋃ i, r i • T₀` and prove `IsFundamentalDomain`.
**Foundation.** `IsFundamentalDomain.iUnion_smul_of_transversal` (PeterssonLevelN) — *exactly this shape*.
Needs `IsFundamentalDomain PSL(2,ℤ) T₀ μ_hyp` as input.
**Classification: API-GAP if (b) holds, else RESEARCH.** The subgroup-tiling engine exists; the only
missing input is `IsFundamentalDomain PSL(2,ℤ) T₀`. Via (b) (T₀ = 2 standard 𝒟's) this is *founded* from
`isFundamentalDomain_fdo_PSL`. **LOC: 200–400** (the 2-copies FD lemma + the transversal tiling).
**Risk:** mathlib has no "union of two FDs of the same group is a FD". Must hand-build it (M2′ below).

  - **(M2′) `T₀ = 𝒟ᵒ ∪ S•𝒟ᵒ` is a PSL FD — the (b) shortcut as a lemma.**  `IsFundamentalDomain.mk''`:
    `ae_covers` from `exists_smul_mem_fd` (every point reaches `𝒟`, hence `T₀`); `aedisjoint` from the
    standard `g•𝒟ᵒ ∩ 𝒟ᵒ ⟹ g=±1` disjointness (`eq_smul_self_of_mem_fdo_mem_fdo`) plus the single fact
    `S ∉ Stab` so the two halves don't double-count under `PSL`. **Founded-but-laborious. LOC 150–300.**

### (M3) Region-Stokes over a single ideal (cusp-vertex) triangle  [FOUNDED for capped, RESEARCH for vertex]
**Statement (sketch).** The area integral of `−2i·periodForm g P·conj(a)` over `T₀ ∩ {im<H}` equals the
negated contour integral over `∂(capped T₀)`; then `H → ∞`.
**Foundation.** `tile_stokes_fd` is *literally* this for the standard `fd`-tile (a cusp triangle with
ideal vertex `∞`, arc + verticals + cap). `tendsto_horizontal_cap` kills the cap.
**Classification: the CAPPED case is FOUNDED** — `tile_stokes_fd` already does region-Stokes over the
non-compact-when-uncapped `fd` tile, capping at `H`; the answer to (c) is *the cusp vertex is NOT a new
obstruction*, the capping + cusp-decay limit is exactly the existing mechanism. The `H→∞` limit is part
of M0. **LOC: 0 new if T₀ is built from `fd` translates (reuse `tile_stokes_fd` per piece); else 200–400.**
**Risk:** if T₀ is a *single* triangle not aligned to `fd` (its arc is `|z−½|=½`, not `|z|=1`), the
5-segment `fdBoundaryFun` doesn't match and `tile_stokes_fd` must be re-proven for the new arc/vertical
geometry — a full copy of the (already-sorry-bearing) `region_stokes_eq_neg_contour`. **Mitigation: build
T₀ from `fd`-translates so `tile_stokes_fd` applies verbatim.**

### (M4) `PairedBoundary B` from the triangulation's side pairing  [API-GAP]
**Statement (sketch).** From the transversal `{γᵢ}` and the triangle edges, produce the `PairedBoundary N`
record: index set, the side-pairing involution matching outer edges, and the side-pairing `Γ₁(N)`-elements.
**Foundation.** `PairedBoundary` structure + `OrientedCuspEdge` + `exists_SL2Z_smul_eq_cusp` (cusp
transitivity) + the side-pairing generators of `Γ₁(N)`.
**Classification: API-GAP (combinatorial, founded by `PairedBoundary`).** The structure exists; the
content is constructing a *concrete* paired boundary realising `∂D`. **LOC: 200–400.**
**Risk:** producing the fixed-point-free involution `pair` and verifying `edge (pair i) = γᵢ • reverse (edge i)`
for the actual coset reps — a genuine but bounded modular-symbols combinatorics task.
*(Route B builds B from the fd-tile coset structure of `Gamma1_fundDomain_PSL`; same work.)*

### (M5) Assembly  [FOUNDED]
**Statement (sketch).** Combine (M0)–(M4): instantiate `D`, `hD` (from M2), `B` (from M4), `P` (a
binomial coefficient bundle from `symMon`), `c` (the `(2i)^{-(k-2)}/2 · fibre-count` scalar), and chain
the area integral = boundary period (M0) with `two_smul_rawPairing_boundaryDivisor` (M4-side).
**Foundation.** `two_smul_rawPairing_boundaryDivisor`, `rawPairing_edgeDivisor_eq_sub` — proven.
**Classification: FOUNDED.** Pure plumbing once M0–M4 land. **LOC: 80–200.**  **Risk:** the factor-2
from the involution (`two_smul_…`) must be absorbed into `c` cleanly; minor.

---

## 4. Key questions — concrete answers

### (a) Does mathlib's `IsFundamentalDomain` + `ModularGroup` FD theory give a usable path to (M2)?
**Partly — the tiling engine yes, the base FD no.** mathlib gives `IsFundamentalDomain.mk'/mk''`,
`setIntegral_eq`, `image_of_equiv`, `smul`, but **(i) no `IsFundamentalDomain` for `𝒟`/`𝒟ᵒ`** (the
project supplies `isFundamentalDomain_fdo_PSL` itself from `exists_smul_mem_fd` + the disjointness
lemmas), and **(ii) no `union`/`iUnion` combinator gluing several same-group FDs into one**. The
*subgroup*-tiling direction (`⋃_{G⧸H}`) IS available and is exactly the project's
`IsFundamentalDomain.iUnion_smul_of_transversal` — that closes the `D = ⋃ γᵢ • T₀` step **provided
`IsFundamentalDomain PSL(2,ℤ) T₀` is in hand**. So (M2) reduces to "is T₀ a PSL-FD?", which is (b).

### (b) The "ideal triangle = 2 × standard 𝒟" shortcut — does it make (M2) FOUNDED?
**Yes, this is the decisive simplification, and it makes (M2) FOUNDED-but-laborious (not RESEARCH).**
The standard `𝒟` is exactly *half* an ideal triangle: `𝒟 = {|re|≤½, |z|≥1}` is the region with ideal
vertex `∞` and two finite "corners" `ρ, ρ+1` on the arc. Reflecting across the imaginary axis (i.e.
adjoining `S•𝒟`, since `S : z ↦ −1/z` maps the arc to itself and folds the two halves) yields a domain
with ideal vertices — the classical fact "`𝒟 ∪ S𝒟` is a hyperbolic ideal triangle with vertices
`0, ∞, ρ`". Concretely:
  - Take **`T₀ := 𝒟ᵒ ∪ S • 𝒟ᵒ`** (or any 2-coset union). Since `{1, S}` (mod `±I`) are coset
    representatives of `PSL(2,ℤ) ⧸ ⟨S⟩`... — *more precisely*, `T₀` is a FD for the **index-? subgroup**;
    the clean statement is: `T₀` is a fundamental domain for the action of `PSL(2,ℤ)` only after we view
    it as `⋃` over a 2-element set that is NOT a subgroup. The honest route is **(M2′)**: prove
    `IsFundamentalDomain PSL(2,ℤ) T₀ μ_hyp` directly via `mk''`, using
    `ae_covers` = (`exists_smul_mem_fd` lands in `𝒟 ⊆ T₀`) and `aedisjoint` from the standard `𝒟ᵒ`
    disjointness (`eq_smul_self_of_mem_fdo_mem_fdo` / `fdo_PSL_pairwise_disjoint`) — `T₀` over-covers by
    a measure-zero set and the two halves `𝒟ᵒ`, `S•𝒟ᵒ` are `PSL`-translates so they tile correctly.
  - **Why FOUNDED:** every ingredient (`exists_smul_mem_fd`, the `𝒟ᵒ` disjointness, null boundary
    `hyperbolicMeasure_fd_boundary`, `mk''`) is already proven in mathlib + the project. No new analysis.
  - **Caveat making it "laborious" not "free":** `T₀` as 2 copies of `𝒟ᵒ` is a FD for **`PSL(2,ℤ)`
    itself** only if the two halves are genuinely a single FD — but two copies of a FD is a FD for an
    *index-2 subgroup*, not the whole group. **The correct reading of shortcut (b)** is therefore:
    *do NOT use T₀ as a PSL-FD directly.* Instead use it to make **(M3) region-Stokes founded** (T₀ is 2
    `fd`-pieces ⟹ `tile_stokes_fd` applies to each half verbatim, giving the cusp-edge contour for free),
    while the FD structure (M2) is obtained by the **subgroup tiling of `fd` itself**
    (`iUnion_smul_of_transversal`) and `D`'s *boundary* is re-expressed as cusp edges. **Net: (b) makes
    (M3) FOUNDED (no new arc geometry) and (M1) trivial; (M2) stays the `iUnion_smul_of_transversal`
    tiling of `fd` (founded). The genuine gap is M0, untouched by (b).**

### (c) Can `tile_stokes_fd`'s Type-I/II `regionBetween` machinery handle a cusp-vertex ideal triangle?
**Yes — the non-compactness at the cusp vertex is NOT a new obstruction.** `tile_stokes_fd` *already*
operates on the standard `fd`-tile, which is a cusp triangle with ideal vertex `∞`; it handles the
non-compactness by **capping at height `H`** (`{… ∧ im < H}`) and the `H → ∞` limit is supplied
separately by cusp decay (`tendsto_horizontal_cap`, `periodForm_norm_le`). The `regionBetween`
machinery (Type-I `region_yhalf`, Type-II `region_xhalf_typeII`, the 5-segment `fdBoundaryFun` split)
is written for the arc-`|z|=1` + verticals-`|re|=½` geometry. **So: a cusp triangle aligned to `fd`
(arc `|z|=1`) is fully founded; a cusp triangle with a *different* arc (e.g. `|z−½|=½` for vertices
`0,1`) would need a fresh copy of the 5-segment/`regionBetween` analysis** (≈ the still-sorry
`region_stokes_eq_neg_contour`). **Decisive recommendation:** build `D` from `fd`-translates (the Siegel
tiling) so `tile_stokes_fd` applies verbatim; reformulate `∂D` combinatorially as cusp edges via
`PairedBoundary` — this is exactly Route B and what `exists_pairedBoundary_fundDomain_petersson_eq`
already sets up.

### (d) Realistic total LOC + single biggest risk leaf.
**Total LOC: ≈ 1100–2400** (M0 dominates at 600–1200; M2/M2′ 350–700; M1 150–300; M4 200–400; M3 0–400
depending on alignment; M5 80–200). **Single biggest risk: (M0)** — specifically the **interior-edge
pairwise cancellation** of adjacent translated `fd`-tiles (the side-pairing telescoping turning a sum of
per-tile capped contours into the surviving outer cusp-edge potentials). It has no mathlib foothold, it
is the part the project has repeatedly flagged as the "research-scale long pole", and it is unavoidable
on *both* routes. Everything else is founded-but-laborious.

---

## 5. Recommended build order & verdict

**Recommended route: B (Siegel pass-through), NOT a literal new Manin FD.**
The target is logically equivalent to the already-present `exists_pairedBoundary_fundDomain_petersson_eq`
(which delegates *to the target* via `symmetrised_petersson_fundDomain_eq`). Rather than build a brand-new
ideal-triangle `D` (M1+M2+M2′+M3-fresh), **take `D := Gamma1_fundDomain_PSL N`** — already an
`imageGamma1_PSL N`-FD (`isFundamentalDomain_Gamma1_PSL`) — and spend all effort on the boundary-period
identity (M0 + M4 + M5). This is FOUNDED for the FD existence, and isolates the work onto the one genuine
gap (M0). The "Manin ideal-triangle" language in the docstring is a *mathematical motivation* for why the
boundary collapses to cusp edges; it need not be a separate Lean object.

**Attack first:** **(M4) `PairedBoundary` from the `fd`-tile coset structure** — it is bounded
combinatorics, fully founded by the `PairedBoundary` structure + cusp transitivity, and produces the `B`
that M0/M5 consume; landing it de-risks the interface and lets M0 be developed against a concrete `B`.
Then **(M0)** as the main multi-week push, decomposed into its own sub-leaves (per-tile capped contour →
interior-edge cancellation → H→∞ → FTC-potential = cuspValue). Then **(M5)** plumbing.

**If the literal Manin `D` is mandated:** do (M2) via `iUnion_smul_of_transversal` over `fd`
(founded), (M1)/(M3) reuse `tile_stokes_fd` per `fd`-piece (founded via answer (b)/(c)), and the work
again concentrates in M0.

**Feasibility verdict.** This is **genuinely multi-week, NOT a bounded few-leaf build** — but it is **one
true gap (M0), not several walls**. The FD existence (M2), the region-Stokes per tile (M3), the binomial
bridge, the cusp-edge period = `cuspValue` difference (M4-bridge `rawPairing_edgeDivisor_eq_sub`), the
paired-edge collapse (M5), and even the deep cusp-boundary naturality (`cuspBoundary_mob_naturality`) are
**all already proven or founded-but-laborious**. The single research-scale obstruction is **M0's
interior-edge side-pairing cancellation + Manin↔Siegel potential matching** — the integral Eichler–Shimura
geodesic-period assembly (Shimura §8.2 (8.2.22)), which has no mathlib foothold. No *additional* mathlib
gap exists beyond it: there is no missing geodesic API blocker (answer (c)), no missing FD-union blocker
(answer (b) reroutes via subgroup tiling). **Bounded-but-large where founded; one deep wall at M0.**
