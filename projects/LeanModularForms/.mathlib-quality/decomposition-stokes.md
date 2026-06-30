# Decomposition — Shimura (8.2.22), the lone `k ≥ 2` Eichler–Shimura wall

**Phase 1e ADVERSARIAL methodical decomposition.** `/develop --decompose`, AINTLIB monorepo,
`dev/leanmodularforms`. Working dir `/Users/mcu22seu/Documents/GitHub/AINTLIB`.

**Target sorry.** `interior_edges_cancel_sum`
(`projects/LeanModularForms/LeanModularForms/HeckeRIngs/GL2/ModularSymbols/PeterssonStokes.lean:2705`),
the single `:= by … sorry` whose `sorryAx` the whole `k ≥ 2` substrate traces to. It is the engine of
`maninFD_interior_edges_cancel` → `maninArea_eq_boundary_period` (= "Shimura (8.2.22)" per the prior
agents) → `exists_pairedBoundary_periodPairingA_eq` → `periodPairingA_eq_boundary_period` →
`periodMap'_injective`.

**Build baseline.** `lake build …PeterssonStokes` is GREEN (3401 jobs, exit 0); the only `sorry`
warning is `:2705`. (One unrelated `unusedSectionVars` linter warning on `tile_area_eq_slashed_stdfdo`.)

> **HEADLINE VERDICT (decisive).** The prior four agents' route is an **invented detour**. Shimura's
> actual proof of (8.2.22) is **NOT** "area = a specific Manin-boundary-divisor period via
> interior-edge cancellation over a coset tiling + a Manin↔Siegel model change." Shimura proves
> (8.2.22) by **one** Stokes/Green application on a **single** fundamental domain `F`, expanding `∂F`
> by the standard side-pairing `∂F = Σ_λ (S_λ − a_λ S_λ)` and re-grouping the two halves of each
> paired edge with the **group-1-cocycle relation (8.1.3) `u(a⁻¹) = −a⁻¹·u(a)`**. The result is a
> cohomological cocycle pairing `A(f,g) = Σ_λ ᵗu(a_λ⁻¹) W ∫_{S_λ} dg` — a finite ℂ-combination of
> the *f-cocycle values* `u_f(a_λ⁻¹)`. **mathlib v4.31 HAS the cocycle machinery** (`cocycles₁`,
> `H1`, and verbatim (8.1.3) as `groupCohomology.cocycles₁_map_inv`), and the project ALREADY models
> `X = Div⁰⊗Sym` as a `Representation ℤ SL(2,ℤ)` (`fullModSymRep`/`modSymRep`) with the f-cocycle
> covariance PROVEN (`cuspValue_symRep_gamma`/`cuspDiff_const`/`isPeriodInvariant_all`, sorry-free).
> **Closing (8.2.22) along Shimura's actual route is FOUNDED**; the residual genuinely-missing piece
> is much narrower than the agents claimed and, on the *loose* shape the sole consumer needs, is
> arguably already proven (see §6, the "short-circuit").

---

## Step 1 — Shimura's ACTUAL proof of (8.2.22), in prose (with page locators)

Source: Shimura, *Introduction to the Arithmetic Theory of Automorphic Functions* (1971). §8.1
"Cohomology groups of Fuchsian groups" (book pp. 222–229) and §8.2 "The correspondence between cusp
forms and cohomology classes" (book pp. 229–236). PDF (287 pp.) front-matter offset ≈ +2; the (8.2.x)
block is at extracted-text lines ~11007–11172. All quotes below are from `pdftotext -layout` (OCR is
imperfect; I reproduce the mathematical content, noting OCR artifacts).

**Setup (book p. 232–233, (8.2.12)–(8.2.18)).** Fix a Fuchsian group `Γ` of the first kind, a rep
`ψ` (here trivial / scalar), `n ≥ 0`, weight `k = n+2`. For `f ∈ S_{n+2}(Γ,ψ)`:
- **(8.2.12)** `𝔡(f) = f·ᵗ[z,1]ⁿ dz` — the vector differential form (for `n=0`, `𝔡(f)=f dz`).
- **(8.2.13)** `W = P ⊗ Sₙ`, `X(α) = ψ(α) ⊗ ρₙ(α)`; `X` is the rep on `X = ℝʳ⊗ℝⁿ⁺¹` (the "module").
- **(8.2.14)** `ᵗX(α) W X(α) = W`; **(8.2.15)** `𝔡(f)∘α = X(α)·𝔡(f)`; **(8.2.16)** taking real
  parts, `Re(𝔡(f))∘α = X(α)·Re(𝔡(f))`.
- **(8.2.17)** the ℝ-bilinear form `A(f,g) = ∫_{Γ\𝔥} ᵗRe(𝔡(f)) ∧ W·Re(𝔡(g))`.
- **(8.2.18a)** `A(f,g) = (2i)^{n+1}·[(f,g) + (−1)ⁿ(g,f)]` (relates `A` to the Petersson product);
  **(8.2.18c)** `A(f, iⁿ·g) = 2ⁿ·Re((f,g))`. "Therefore `A(f,g)` is non-degenerate."

**The cocycle `t`/`u` (book p. 233, the `F(z)` construction).** Fix `z₀ ∈ 𝔥`. For `f ∈ S_{n+2}`,
put `F(z) = ∫_{z₀}^z 𝔡(f) + v` (any fixed `v ∈ X`); `F` is path-independent since `𝔡(f)` is
holomorphic. By (8.2.15), `F(α(z)) = X(α)F(z) + t(α)` where
`t(α) = ∫_{z₀}^{α(z₀)} 𝔡(f) + v − X(α)v`. Hence **`t(αβ) = t(α) + X(α)t(β)`, so `t ∈ Z¹(Γ,X_ℂ)`**.
Taking `Re(𝔡(f))` instead gives **(8.2.19)** `f̃(z) = ∫_{z₀}^z Re(𝔡(f)) + a`, and **(8.2.20)**
`f̃(α(z)) = X(α)f̃(z) + u(α)` with `u ∈ Z¹(Γ,X)`. "the cohomology class of `u` is uniquely
determined by `f`, and independent of the choice of `z₀`." Define `ϖ(f) =` the cohomology class of
`u`. (This is the period map; Theorem 8.4 is that `ϖ` is an isomorphism `S_{n+2}(Γ,ψ) ≅ H¹_P(Γ,X)`.)

**The proof of (8.2.22) (book pp. 234–235).** Verbatim (OCR, cleaned):

> "Let `f` and `g` be elements of `S_{n+2}(Γ,ψ)`. Define `f̃` and `u` as in (8.2.19) and (8.2.20).
> Similarly, put `g̃(z) = ∫_{z₀}^z Re(𝔡(g)) + b` … with `g̃(α(z)) = X(α)g̃(z) + v(α)` **(8.2.21)**
> with `v ∈ Z¹(Γ,X)`. Since `df̃ = Re(𝔡(f))` and `dg̃ = Re(𝔡(g))`, we have
> `A(f,g) = ∫_{Γ\𝔥} ᵗdf̃ ∧ W dg̃`."

> "Take a fundamental domain `F` for `Γ\𝔥` constructed in the proof of Th. 2.20. **Here we do not
> take small circles around cusps and elliptic points** as considered there. Since
> `d(ᵗf̃ W dg̃) = ᵗdf̃ ∧ W dg̃`, we have [`A(f,g) = ∫_{∂F} ᵗf̃ W dg̃`] where `∂F` is the boundary of
> `F`."

> "As is observed in the proof of Th. 2.20, we have `∂F = Σ_λ [S_λ − a_λ(S_λ)]`, with 1-simplexes
> `S_λ` and elements `a_λ` of `Γ`, so that
> `A(f,g) = Σ_λ [∫_{S_λ} ᵗf̃ W dg̃ − ∫_{a_λ(S_λ)} ᵗf̃ W dg̃]`."

> "By virtue of (8.2.20), (8.2.21), and (8.2.14),
> `∫_{a_λ(S_λ)} ᵗf̃ W dg̃ = ∫_{S_λ} ᵗ(f̃∘a_λ) W d(g̃∘a_λ) = ∫_{S_λ} ᵗf̃ W dg̃ + ∫_{S_λ} ᵗu(a_λ) W X(a_λ) dg̃`,
> hence, by (8.1.3) and (8.2.14),
> **(8.2.22)** `A(f,g) = Σ_λ ᵗu(a_λ⁻¹) W ∫_{S_λ} dg̃`."

> "Now suppose that `ϖ(f) = 0`. Then, **choosing the constant vector `a` of (8.2.19) suitably, we may
> put `u = 0`**. Then (8.2.22) implies `A(f,g) = 0`, for every `g ∈ S_{n+2}(Γ,ψ)`. Since `A(f,g)` is
> non-degenerate, `f` must be 0. This proves that the map `ϖ` is injective."

The boundary input (Th. 2.20 proof, book pp. 42–43; extracted lines ~2329–2380), verbatim:

> "the boundary `∂H` … can be written in the form **(1)** `∂H = Σ_{λ=1}^n (S_λ − τ_λ(S_λ)) + Σ_μ T_μ`
> … Here the `T_μ` are the curves corresponding to the small circles, the `S_λ` correspond to the
> 'sides', and `τ_λ` is a certain element of `Γ` for each `λ`. The interior of `H`, when each `T_μ`
> is shrunk to a point, is certainly a fundamental domain for `Γ`."

So in §8.2 (no small circles), `∂F = Σ_λ (S_λ − a_λ S_λ)` exactly. The `a_λ` are the **side-pairing
transformations** (they pair each side `S_λ` with another side `a_λ S_λ` of the same polygon).

**The exact algebra of the key step (book p. 235), expanded.**
`∫_{a_λ S_λ} ᵗf̃ W dg̃`. Substitute `w = a_λ z` (so the integral over `a_λ S_λ` becomes one over
`S_λ` of the pulled-back integrand). Using `f̃∘a_λ = X(a_λ)f̃ + u(a_λ)` (8.2.20), `dg̃∘a_λ =`
`d(X(a_λ)g̃ + v(a_λ)) = X(a_λ) dg̃` (8.2.21, `v` constant), and `ᵗ(X(a_λ)f̃) W X(a_λ) = ᵗf̃ W`
(8.2.14):
`∫_{a_λ S_λ} ᵗf̃ W dg̃ = ∫_{S_λ} ᵗf̃ W dg̃ + ∫_{S_λ} ᵗu(a_λ) W X(a_λ) dg̃`.
Hence each bracket in the boundary sum is `−∫_{S_λ} ᵗu(a_λ) W X(a_λ) dg̃`. Finally **(8.1.3)**
`u(a⁻¹) = −a⁻¹·u(a)` — i.e. `ᵗu(a_λ⁻¹) W = −ᵗu(a_λ) W X(a_λ)` (using (8.2.14) to move `W X(a_λ)`) —
rewrites this as `+ᵗu(a_λ⁻¹) W ∫_{S_λ} dg̃`, giving (8.2.22).

**Cross-references (cleanest proof = Shimura's).**
- **Diamond–Shurman §5.4** ("Modular Symbols", *A First Course in Modular Forms*): models `A(f,g)`
  via the pairing of the period homomorphism against `H₁(X(Γ),cusps;ℂ)`; it is the *homology* dual of
  the same cocycle statement (the modular-symbol `{α,β}` boundary pairs with the cocycle). Slightly
  more machinery (relative homology); Shimura's cocycle route is leaner.
- **Miyake §4.5** (Thm 4.5.x, period map): same `Z¹(Γ,X)` cohomological framework as Shimura;
  Eichler–Shimura isomorphism. Confirms Shimura's `Z¹` route is the textbook standard.

**The cleanest substrate = Shimura's exact route**, because (i) it needs only ONE Stokes call on ONE
fundamental domain (not a coset tiling with interior-edge bookkeeping), and (ii) its only "boundary
combinatorics" is the standard side-pairing `∂F = Σ(S_λ − a_λ S_λ)` + the *algebraic* cocycle
relation (8.1.3), for which mathlib has a verbatim lemma.

---

## Step 2 — MATCH/DIFFER vs the prior agents' route

| | **Shimura's actual (8.2.22)** | **Prior agents' route (the sorry)** |
|---|---|---|
| Domain | single FD `F` (Th. 2.20 polygon) | **coset tiling** `⋃_q (q.out)⁻¹•fdo` of the SL₂(ℤ) `fdo` |
| Stokes | **one** application `∫_F d(ᵗf̃ W dg̃) = ∫_{∂F} …` | per-tile `tile_stokes_fd` on each `fdo`, summed |
| Boundary | `∂F = Σ_λ(S_λ − a_λ S_λ)` (side-pairing) | per-tile 5-segment `fdBoundaryFun` contours, claim **interior edges cancel** across tiles |
| Re-grouping | algebraic **cocycle (8.1.3)** `u(a⁻¹)=−a⁻¹u(a)` | **"Manin↔Siegel model change"** matching arcs/∞-caps to rational-cusp geodesics |
| f-side data | `u_f(a_λ⁻¹)` cocycle values, killed by `ϖ(f)=0` ⇒ `u=0` | `rawPairing f(maninPairedBoundary.boundaryDivisor⊗P)`, killed by `periodMap' f=0` |
| Output shape | `Σ_λ ᵗu(a_λ⁻¹) W ∫_{S_λ}dg̃` (finite cocycle pairing) | `c · rawPairing f(∂F⊗P)` (**single** concrete-Manin period) |

**DIFFERS substantially.** The agents' "interior-edge cancellation over a coset tiling" and
"Manin↔Siegel model change" are **NOT in Shimura**. Shimura never tiles `Γ\𝔥` by SL₂(ℤ) copies of
`fdo`; he uses the `Γ`-FD `F` directly, and his only "cancellation" is the *paired-side* re-grouping
on the single `∂F`, made trivial by the cocycle identity. The agents reproduced the
*Diamond–Shurman-flavoured* "Manin symbol" picture and bolted on a coset-tiling Stokes that creates a
spurious interior-edge-matching problem (the genuinely research-scale `sorry`). Shimura's route has
no such object.

Where the project DOES match Shimura: the *downstream* consumer
`periodPairingA_eq_boundary_period`/`periodPairingA_eq_zero_of_periodMap'_zero`/`periodMap'_injective`
mirrors Shimura's injectivity argument **exactly** (express `A(f,g)` as a finite combination of
*periods of f*, then `ϖ(f)=0` kills every term). And the proven `cuspValue_symRep_gamma` /
`cuspDiff_const` / `isPeriodInvariant_all` are precisely Shimura's `u_f` cocycle covariance + the
"`u` is well-defined up to coboundary" + the (8.2.20) covariance — all sorry-free.

---

## Step 3 — Leaf decomposition mirroring Shimura's structure

Shimura's proof has exactly these leaves. I classify each FOUNDED / API-GAP / RESEARCH against
**mathlib v4.31** (`.lake/packages/mathlib/`) and **AINTLIB** (cited by `file:decl`, all verified
present; sorry-status noted).

### L0 — `A(f,g) = ∫_{Γ\𝔥} ᵗdf̃ ∧ W dg̃` (the area integral is the Petersson combination)
**Quote.** "Since `df̃ = Re(𝔡(f))` and `dg̃ = Re(𝔡(g))`, we have `A(f,g) = ∫_{Γ\𝔥} ᵗdf̃ ∧ W dg̃`."
plus (8.2.18a) `A(f,g) = (2i)^{n+1}[(f,g)+(−1)ⁿ(g,f)]`.
**Lean ↔ source.** `periodPairingA f g := petN f g + (-1)ⁿ • petN g f`
(`PeriodInjective.lean:69`) is Shimura's `A` modulo the harmless scalar `(2i)^{n+1}` (the docstring
:64–67 says so). The "= area integral over a FD" is
`petN_eq_setIntegral_Gamma1_fundDomain_PSL` + `symmArea_eq_symm_stdTile_sum`.
**Status: FOUNDED.** `symmArea_eq_symm_stdTile_sum` (`PeterssonStokes.lean:2528`, sorry-free) and
`petN_eq_setIntegral_Gamma1_fundDomain_PSL` proven; `Gamma1_fundDomain_PSL` +
`isFundamentalDomain_Gamma1_PSL` (`PeterssonLevelN.lean:390,396`) verified.

### L1 — exactness `d(ᵗf̃ W dg̃) = ᵗdf̃ ∧ W dg̃` (the integrand is an exact 2-form)
**Quote.** "Since `d(ᵗf̃ W dg̃) = ᵗdf̃ ∧ W dg̃`, we have [`A = ∫_{∂F} ᵗf̃ W dg̃`]."
**Lean ↔ source.** `f̃` = holomorphic primitive of `Re(𝔡(f))`; the project's primitive is `F` from
`Complex.isExactOn_upperHalf (differentiableOn_periodForm f Q)` (`PeriodInvariant.lean:87`, Morera on
balls glued, sorry-free). The "exact 2-form / planar-divergence decomposition" is
`holAntihol_eq_divergence` (`PeterssonStokes.lean:47,115`, **sorry-free**, L1).
**Status: FOUNDED.** mathlib divergence theorem
`MeasureTheory.integral2_divergence_prod_of_hasFDerivAt` (`DivergenceTheorem.lean:551`) on `ℝ×ℝ`
rectangles is what the per-rectangle Stokes already consumes.

### L2 — single Stokes `∫_F (exact 2-form) = ∫_{∂F} (1-form)`
**Quote.** "Take a fundamental domain `F` … Since `d(ᵗf̃ W dg̃)=ᵗdf̃∧W dg̃`, we have
`A = ∫_{∂F} ᵗf̃ W dg̃`."
**Lean ↔ source.** Region-Stokes for the period 1-form over `fdo`, capped at height `H`, is
`tile_stokes_fd` (`PeterssonStokes.lean:2149`, **PROVEN**) applied per binomial term
(`exists_tile_boundary_periodForm_term` :2310), with the top cap → 0 as `H→∞`
(`tendsto_horizontal_cap`, `periodForm_norm_le`, `PeriodInvariant.lean:375,338`, sorry-free) — cusp
decay kills the ∞-cap, which is Shimura's "no small circles, but the cusp/∞ ends contribute 0".
**Status: FOUNDED** for the *per-domain* Stokes. The 5-segment `fdBoundaryFun` boundary of the
SL₂(ℤ) `fdo` is the concrete `∂F`. (mathlib has UpperHalfPlane.Metric `Analysis/Complex/
UpperHalfPlane/Metric.lean` so geodesic sides are reachable, but the project uses the explicit
arc+verticals contour, not abstract geodesics — adequate, per the existing `coe_fd` survey.)

### L3 — the boundary expansion `∂F = Σ_λ (S_λ − a_λ S_λ)` (side-pairing)
**Quote (Th. 2.20).** "`∂H = Σ_λ (S_λ − τ_λ(S_λ)) + Σ_μ T_μ` … `τ_λ` is a certain element of `Γ`
… The interior of `H`, when each `T_μ` is shrunk to a point, is … a fundamental domain for `Γ`."
**Lean ↔ source.** This is the project's `PairedBoundary N` object
(`FundamentalDomainBoundary.lean`): a finite family of oriented cusp edges with a fixed-point-free
involution `pair` and side-pairing `γ : ι → Γ₁(N)` realising `edge(pair i) = γ i • reverse(edge i)`
— **exactly** Shimura's `S_λ ↔ a_λ S_λ` pairing. The concrete witness `maninPairedBoundary N`
(`PeterssonStokes.lean:2466`, sorry-free) is a 2-edge paired cycle with `γ = maninSidePairing N`.
**Status:** the *abstract* paired-boundary algebra is **FOUNDED** (`PairedBoundary`,
`edgePotentialSum_cycle_eq_zero` :117, `rawPairing_edgeDivisor_eq_sub` :191, all sorry-free). What is
**API-GAP / RESEARCH** is the *geometric* claim that `∂(Gamma1_fundDomain_PSL N)` literally equals a
specific such cycle of *rational-cusp geodesics* — mathlib has **no cusps, no modular-curve boundary,
no `∂F = Σ(S_λ − a_λ S_λ)` for a congruence FD**. (Th. 2.20 itself is NOT in mathlib: there is no
`IsFundamentalDomain` polygon-with-paired-sides; mathlib's `Modular.lean` has `fd`/`fdo` but no FD
*instance* and no side-pairing — confirmed in the maninFD survey.)
**This is the single hardest leaf** — see §5.

### L4 — paired-side re-grouping via the cocycle (8.1.3)
**Quote.** "`∫_{a_λ S_λ} ᵗf̃ W dg̃ = ∫_{S_λ} ᵗf̃ W dg̃ + ∫_{S_λ} ᵗu(a_λ) W X(a_λ) dg̃`, hence, by
(8.1.3) and (8.2.14), `A(f,g) = Σ_λ ᵗu(a_λ⁻¹) W ∫_{S_λ} dg̃`." with **(8.1.3)** `u(a⁻¹) = −a⁻¹ u(a)`.
**Lean ↔ source.** Two sub-facts:
  - **(8.2.20)/(8.2.21) covariance** `f̃∘a = X(a)f̃ + u(a)`, `dg̃∘a = X(a)dg̃`: the project's
    `cuspValue_symRep_gamma` (`PeriodInvariant.lean:1802`, **sorry-free**) is exactly
    `cuspValue f (symRep γ P)(γ•c) = cuspValue f P c + T` — i.e. the cusp-potential transforms by
    `X(γ)` up to the additive constant `T = u_f(γ)`. `cuspDiff f γ P c := cuspValue f (symRep γ P)(γc)
    − cuspValue f P c` (`:195`) IS Shimura's `u_f(γ)` (a constant in `c`, by `cuspDiff_const` :1843).
  - **(8.1.3)** `u(a⁻¹) = −a⁻¹u(a)`: **mathlib v4.31** `groupCohomology.cocycles₁_map_inv`
    (`RepresentationTheory/Homological/GroupCohomology/LowDegree.lean:311`):
    `A.ρ g (f g⁻¹) = -f g` — **verbatim (8.1.3)** for `A : Rep k G`, `f ∈ cocycles₁ A`. The cocycle
    identity (8.1.1) is `mem_cocycles₁_iff` (`:303`): `f(gh) = A.ρ g (f h) + f g`.
**Status: FOUNDED.** The covariance is proven in-project; the (8.1.3) algebra is a one-line mathlib
lemma on `cocycles₁`, and the module `X = Div⁰⊗Sym` is **already a `Representation ℤ SL(2,ℤ)**` in
the project (`ModuleM.lean:48` `fullModSymRep`, `modSymRep`), so `cocycles₁ (Rep.ofRepresentation
(modSymRep …))` / `H1` apply directly. The project's `rawPairing_modSymRep_sub`
(`PeriodInvariant.lean:202`) + `isPeriodInvariant_all` (`:1856`) already prove the cocycle descends
(`Γ₁(N)`-invariance of `rawPairing f`), which is the "`u` well-defined up to coboundary" half.

### L5 — injectivity: `ϖ(f)=0 ⇒ u=0 ⇒ A(f,·)=0 ⇒ f=0` by non-degeneracy
**Quote.** "Now suppose that `ϖ(f)=0`. Then … we may put `u=0`. Then (8.2.22) implies `A(f,g)=0`,
for every `g`. Since `A(f,g)` is non-degenerate, `f` must be 0."
**Lean ↔ source.** `periodPairingA_eq_zero_of_periodMap'_zero` (`PeriodInjective.lean:134`) +
`periodPairingA_twist_self` (8.2.18c, `:78`) + `petN_definite` ⇒ `periodMap'_injective` (`:164`).
The non-degeneracy `A(f, iⁿf) = 2iⁿ(f,f)` is (8.2.18c).
**Status: FOUNDED** (all sorry-free) — *given* L0–L4. The f-side kill is
`rawPairing_eq_zero_of_periodMap'_zero` (`:94`): `periodMap' f = 0 ⇒ rawPairing f x = 0` for **every**
`x ∈ Div⁰⊗Sym`. This is exactly "`u_f = 0` ⇒ every term `ᵗu_f(a_λ⁻¹)W∫dg̃` vanishes".

---

## Step 4 — Per-leaf adversarial attacks (≥3 per nontrivial leaf)

### L0 / L1 / L2 (the analytic backbone) — already sorry-free; attacks on consumption
- **Discharge-verification.** `tile_stokes_fd` (:2149), `holAntihol_eq_divergence` (:115),
  `isExactOn_upperHalf` (:87), `tendsto_horizontal_cap` (:375) all grep-located as `theorem …`
  (not `sorry`); the file builds green with the lone `:2705` sorry. ✔ exist + sorry-free.
- **Source-drift.** Shimura caps at small circles `T_μ` and shrinks them; the project caps at finite
  height `H` and sends `H→∞`. Equivalent: both isolate the cusp/elliptic ends. The elliptic-point
  `T_μ` for SL₂(ℤ) (`ρ`, `i`) contribute 0 because the integrand `ᵗf̃ W dg̃` is *smooth* there (no
  pole; cusp forms vanish at cusps, are finite at interior points). ✔ no drift.
- **Edge case `n=0` (k=2).** Shimura: "`If n=0, 𝔡(f)=f dz`." `tile_stokes_fd` binomial sum has the
  single term `j=0`; `SymPow ℤ 0` is 1-dim. The proven machinery already handles `(k-2).toNat = 0`.
  ✔ (`hk : 2 ≤ k` matches Shimura's `n ≥ 0`.)
- **Hypothesis-strength.** Could a non-cusp modular form break the cap? Yes — `tendsto_horizontal_cap`
  needs cusp decay (`periodForm_norm_le` uses `CuspFormClass`). The target is stated for `CuspForm`. ✔
  hypotheses are exactly Shimura's `S_{n+2}`.

### L3 (the boundary expansion `∂F = Σ(S_λ − a_λ S_λ)`) — THE hard leaf
- **Counterexample search.** Is the *abstract* `PairedBoundary` telescoping vacuous? No:
  `edgePotentialSum_cycle_eq_zero` requires a *closed* chain; `maninPairedBoundary` has the genuine
  nonzero boundary symbol `(1−g₀)∂e₀` with `g₀ = maninSidePairing N ≠ 1` (`:2464`), so the
  side-pairing is not the vacuous `γ=1` reverse-pairing. ✔ not a `boundaryDivisor=0` cheat.
- **Source-drift (the decisive attack).** The agents demand `∂F` = the *specific* `maninPairedBoundary`
  divisor and a *single* `c·rawPairing f(∂F⊗P)`. Shimura demands only `∂F = Σ_λ(S_λ−a_λ S_λ)` for
  *whatever* sides/side-pairings the FD polygon has (the `a_λ` are "certain elements of `Γ`", not a
  named symbol), yielding a *finite sum* `Σ_λ ᵗu(a_λ⁻¹)W∫_{S_λ}dg̃`. **The agents over-specified the
  shape**, creating the "Manin↔Siegel model change" obligation (matching SL₂(ℤ)-`fdo` arcs to
  rational-cusp geodesics) that Shimura never incurs. ✔ confirmed invented.
- **mathlib-foothold probe.** Does mathlib have ANY `∂F` for a congruence FD?
  `find … -iname "*cusp*"`, `grep cusp/geodesic` over `NumberTheory/ModularForms/` + `Modular.lean`:
  **NO modular curve, NO cusp set as boundary, NO simplicial `∂F`, NO Th. 2.20.** `Modular.lean` has
  `fd`/`fdo`/`coe_fd` (the arc+verticals region) but **no `IsFundamentalDomain` instance and no
  side-pairing**. UpperHalfPlane.Metric exists (geodesics reachable) but unconnected to FD boundary.
  ⇒ realizing L3 *geometrically* (an honest `∂(Gamma1_fundDomain_PSL N) = Σ(S_λ−a_λ S_λ)` with
  `S_λ` literal geodesic 1-simplices) is **RESEARCH** — it is Th. 2.20 + the congruence side-pairing,
  absent from mathlib. **This is the single hardest leaf.**
- **Hypothesis-strength / can L3 be bypassed?** YES — see §6. The *consumer* never inspects `S_λ`
  geometrically; it only needs `A(f,g) = Σ cᵢ rawPairing f(yᵢ)` with `yᵢ ∈ Div⁰⊗Sym`. The
  `yᵢ` can be taken to be the *cocycle defects* `divDiff(γ_λ•c)c`, whose periods are `cuspDiff f γ_λ`
  — already proven `c`-constant. So L3's geometric content is needed only to identify *which*
  `a_λ`/`γ_λ` appear, and the *injectivity* consumer is indifferent to that. (See the short-circuit.)

### L4 (cocycle re-grouping) — compositional attack on the (8.1.3) step
- **Discharge-verification.** `cocycles₁_map_inv` read verbatim
  (`LowDegree.lean:311`: `A.ρ g (f g⁻¹) = -f g`); `mem_cocycles₁_iff` (`:303`). ✔ exist, exact type.
- **Type-match.** `cocycles₁` lives on `A : Rep k G` (a `Representation` packaged as a `ModuleCat`
  object). The project's `modSymRep N m` is a bare `Representation ℤ SL(2,ℤ)` (`ModuleM.lean`).
  Bridging `Representation → Rep` is `Rep.ofRepresentation`/`Rep.of` (mathlib
  `RepresentationTheory/Rep/Basic.lean`). ✔ founded bridge (a definitional repackage).
- **Source-drift on `u_f`.** Is the project's `cuspDiff f γ` really the cohomology cocycle `u_f(γ)`?
  Shimura: `u(α) = f̃(α z) − X(α)f̃(z)` (a constant in `z`). Project: `cuspDiff f γ P c =
  cuspValue f(symRep γ P)(γc) − cuspValue f P c`, proven independent of `c` (`cuspDiff_const`) and
  equal to the additive constant `T` of `cuspValue_symRep_gamma`. The `cuspValue` is the
  endpoint potential `f̃` at the cusp `c`; so `cuspDiff` = `f̃(γc) − [transform of f̃](c)` = `u_f(γ)`.
  ✔ faithful. The cocycle identity `u_f(γδ)=u_f(γ)+X(γ)u_f(δ)` is the only unproven algebraic fact —
  but it follows from `cuspValue_symRep_gamma` applied twice (composition of the two contour shifts),
  i.e. it is API-GAP not RESEARCH.
- **Edge case.** `X(a)` real (Shimura notes "Since `X(α)` is real"): the project works over ℤ-rep
  `symRep ℤ`, cast to ℂ — real coefficients, matches.

### L5 (injectivity) — attacks on the non-degeneracy
- **Discharge-verification.** `periodPairingA_twist_self` (:78), `periodMap'_petN_self` (:149),
  `periodMap'_injective` (:164), `petN_definite` consumed — all `theorem …`, build green. ✔
- **Counterexample.** Could `A(f, iⁿf)=0` with `f≠0`? Only if `petN f f = 0`, impossible for `f≠0`
  by positive-definiteness (`petN_definite`). ✔ non-degeneracy genuine. `2iⁿ ≠ 0`. ✔
- **Source-drift.** Shimura's `A(f,iⁿg)=2ⁿRe((f,g))` vs project's `A(f,iⁿf)=2iⁿ(f,f)` — the harmless
  `iⁿ` repackaging is documented (`:72–77`); `Re((f,f))=(f,f)≥0`. ✔

---

## Step 4.5 — Attacks on the internal-node compositions

- **L0∘L1∘L2 (area→boundary).** The composition is exactly `periodPairingA_eq_boundary_period`'s
  intended body. Risk: the per-tile Stokes (`tile_stokes_fd`, on the SL₂(ℤ) `fdo`) is glued over a
  *coset tiling* — that gluing is `symmArea_eq_symm_stdTile_sum` (proven) but the *boundary*
  re-assembly across tiles is the invented L3'. **Shimura avoids the tiling**: one Stokes on the
  `Γ₁(N)`-FD `F`. ⇒ the cleanest composition skips `slashed_stdfdo_sum_eq_symmArea` /
  `interior_edges_cancel_sum` entirely and runs L1/L2 on `F = Gamma1_fundDomain_PSL N` once. The
  obstacle: that needs `∂(Gamma1_fundDomain_PSL N)` as a paired-edge cycle (L3, the hard leaf) — but
  see §6: even that is unnecessary for the *consumer*.
- **L3∘L4 (boundary→cocycle pairing).** Shimura's `Σ_λ` is finite because the FD polygon has finitely
  many sides. The project's `Gamma1_fundDomain_PSL N = ⋃_q (q.out)⁻¹•fdo` is a finite union over the
  *finite* coset space `PSL(2,ℤ)⧸imageGamma1_PSL N` (`FinitelyManyCusps.lean`), so finiteness ✔. The
  side-pairing `a_λ ∈ Γ₁(N)` are the coset-gluing maps; their cocycle values `u_f(a_λ⁻¹)` are
  `cuspDiff f a_λ⁻¹` — proven `c`-constant and well-defined. ✔ composition sound.
- **L4∘L5 (cocycle pairing→injectivity).** `A(f,g)=Σ_λ ᵗu_f(a_λ⁻¹)W∫_{S_λ}dg̃`; if `u_f=0` (cohomology
  class trivial, i.e. `periodMap' f=0`) every term dies. The project's
  `rawPairing_eq_zero_of_periodMap'_zero` kills `rawPairing f` on ALL of `Div⁰⊗Sym`, which dominates
  any finite combination of such terms. ✔ — and this is precisely why the *loose* output shape (any
  finite `Σ cᵢ rawPairing f(yᵢ)`) suffices, not the concrete-Manin single period.

---

## 5. The single hardest leaf + its mathlib foothold

**Hardest leaf: L3** — "`∂F = Σ_λ(S_λ − a_λ S_λ)` as a genuine paired cycle of rational-cusp geodesic
1-simplices for a congruence fundamental domain" (Shimura's Th. 2.20 + congruence side-pairing).

**mathlib foothold for L3?**
- *As stated (geometric).* **NONE.** No modular curve, no cusp boundary, no `IsFundamentalDomain`
  polygon, no side-pairing, no Th. 2.20. (Verified by exhaustive `find`/`grep` over
  `NumberTheory/ModularForms/`, `Modular.lean`, `UpperHalfPlane/*`.) `Modular.lean` gives only the
  *region* `fd`/`coe_fd`; `UpperHalfPlane/Metric.lean` gives geodesics but no FD-boundary tie-in.
- *Group-cohomology foothold (the relevant one).* mathlib **HAS** the abstraction L3 ultimately feeds:
  `groupCohomology` with `cocycles₁`/`coboundaries₁`/`H1` (`LowDegree.lean`), `LongExactSequence`,
  `Functoriality`, `Hilbert90`, `FiniteCyclic`. The cocycle identity (8.1.1) = `mem_cocycles₁_iff`,
  the inverse relation (8.1.3) = `cocycles₁_map_inv`. So the *target* of L3+L4 — "express `A(f,g)` via
  a 1-cocycle of `Γ` valued in the `Representation` `X`" — is fully founded. What's missing is only the
  *geometric realization* connecting the FD boundary to that cocycle, and even that is bypassed (§6).
- *Divergence-theorem foothold for the Stokes (L2).* mathlib `integral2_divergence_prod_of_hasFDerivAt`
  (`DivergenceTheorem.lean:551`) on `ℝ×ℝ` rectangles, and `CurveIntegral/Poincare.lean`
  (`curveIntegral_add_curveIntegral_eq_of_…`) for closed-1-form curve integrals — both present; the
  former already powers `tile_stokes_fd`. There is **no** divergence theorem on a quotient
  manifold-with-corners / `IsFundamentalDomain` boundary; the project (correctly) reduces to
  rectangles per tile.

---

## 6. The short-circuit (decisive feasibility finding)

**The sole real consumer is `periodMap'_injective`, via `periodPairingA_eq_boundary_period`, whose
existential is the LOOSE shape**
```lean
∃ (n : ℕ) (coeff : Fin n → ℂ) (y : Fin n → Div0 ℤ ⊗[ℤ] SymPow ℤ (k-2).toNat),
  periodPairingA f g = ∑ i, coeff i * rawPairing f (y i)        -- PeriodInjective.lean:118–121
```
(verified: `grep` shows **NO** consumer of `exists_pairedBoundary_periodPairingA_eq` or
`periodPairingA_eq_boundary_period` outside the three files; the only use is `:137` feeding
injectivity). The current proof *over-specifies* by routing through the concrete `maninPairedBoundary
N` and a **single** `c·rawPairing f(∂F⊗P)` term — which is what forces `interior_edges_cancel_sum`'s
"interior-edge cancellation + Manin↔Siegel model change."

**Two ways the loose shape is reachable WITHOUT the geometric L3:**

1. **Shimura's actual route (recommended).** Run L1/L2 once on the single FD `F = Gamma1_fundDomain
   _PSL N` (it IS a fundamental domain: `isFundamentalDomain_Gamma1_PSL`). By L4, the boundary
   re-grouping gives `A(f,g) = Σ_λ [cocycle term]` where each f-factor is `u_f(a_λ) = cuspDiff f a_λ`,
   and `cuspDiff f γ` is the period `rawPairing f (divDiff(γ•c)c ⊗ Q)` for the cocycle-defect divisor
   `divDiff(γ•c)c ∈ Div⁰` (this is `rawPairing_modSymRep_sub` / `cuspDiff` packaged as a `rawPairing`
   of a degree-0 divisor — `cuspDiff_const` makes it `c`-independent so it lands as a genuine
   `Div⁰⊗Sym` element). Set `yᵢ = (divDiff(a_i•c)c) ⊗ Qᵢ`, `coeffᵢ =` the `∫_{S_i}dg̃` weights. ⇒ the
   loose existential, FOUNDED on proven `cuspValue_symRep_gamma`/`cuspDiff_const`/`rawPairing
   _modSymRep_sub`. The *only* genuinely new step is the bookkeeping that the per-tile boundary
   contributions assemble into `Σ_λ`-of-cocycle-terms — i.e. L3's combinatorics — but at the **period
   (ℂ) level**, where it is the proven `edgePotentialSum_cycle_eq_zero` telescoping, NOT the geometric
   geodesic identification.

2. **The trivial short-circuit (if only injectivity is wanted).** `periodPairingA_eq_zero_of_period
   Map'_zero` needs `A(f,g)=0` *only when `periodMap' f = 0`*. By `rawPairing_eq_zero_of_periodMap'
   _zero`, in that regime `rawPairing f` annihilates ALL of `Div⁰⊗Sym`. So `A(f,g)`, which by L0
   equals an area integral that L1/L2/L4 express as `Σ_λ ᵗu_f(a_λ⁻¹)W∫_{S_λ}dg̃` — a finite
   combination of `rawPairing f`-values — is `0`. The *existence* of such a finite combination (with
   `yᵢ ∈ Div⁰⊗Sym`) is all that is consumed; the *concrete identity* of the `yᵢ`/`a_λ` is never
   inspected downstream. This is exactly Shimura's "we may put `u=0`, then (8.2.22) implies
   `A(f,g)=0`."

**Net.** The over-specified geometric wall (`interior_edges_cancel_sum`) is **not** Shimura's proof
and **not** what the consumer needs. Re-targeting `periodPairingA_eq_boundary_period` onto the loose
shape via Shimura's cocycle route removes the "Manin↔Siegel model change" obligation. The residual
genuinely-new content shrinks to **L4's cocycle-composition identity** (`u_f(γδ)=u_f(γ)+X(γ)u_f(δ)`,
an API-GAP provable from `cuspValue_symRep_gamma` applied twice) plus the **period-level telescoping**
that the finite per-side `Σ_λ` assembles (FOUNDED on `edgePotentialSum_cycle_eq_zero`). The hard
geometric L3 (literal geodesic `∂F`) is **needed only if one insists on the concrete `maninPaired
Boundary` shape** — which nothing downstream requires.

---

## Feasibility verdict

> **Closing Shimura (8.2.22) — as the project actually consumes it (`periodMap'_injective` via the
> loose-shape `periodPairingA_eq_boundary_period`) — is FOUNDED on available mathlib v4.31 + AINTLIB,
> via the COHOMOLOGICAL COCYCLE route, NOT the geometric coset-tiling route the prior agents took.**

- **Route:** Shimura's single-FD Stokes (L1/L2 = proven `holAntihol_eq_divergence`/`tile_stokes_fd`/
  `isExactOn_upperHalf`/`tendsto_horizontal_cap`) + paired-side re-grouping by the **group-1-cocycle
  identity (8.1.3) = mathlib `cocycles₁_map_inv`** on the project's existing `Representation`
  `modSymRep` (`ModuleM.lean`), with the f-cocycle `u_f = cuspDiff` and its covariance ALREADY proven
  (`cuspValue_symRep_gamma`/`cuspDiff_const`/`isPeriodInvariant_all`, sorry-free), and the f-side kill
  `rawPairing_eq_zero_of_periodMap'_zero` (sorry-free).
- **Single hardest leaf:** L3 (`∂F = Σ(S_λ−a_λ S_λ)` as literal rational-cusp geodesics for a
  congruence FD = Shimura Th. 2.20 + side-pairing). **mathlib foothold for it: NONE geometrically**
  (no modular curve / cusps / FD boundary / side-pairing); but mathlib **does** have the
  group-cohomology target (`cocycles₁`/`H1`/(8.1.3)) and the rectangle divergence theorem it reduces
  to. **And L3 is NOT on the critical path for the consumer** — the loose existential is satisfiable
  by the cocycle route without identifying geodesic sides (§6).
- **Genuinely-new work** (if pursued): (a) `Rep.ofRepresentation (modSymRep …)` bridge + invoke
  `cocycles₁_map_inv` [API-GAP, ~lines]; (b) cocycle-composition `u_f(γδ)=u_f(γ)+X(γ)u_f(δ)` from
  `cuspValue_symRep_gamma`×2 [API-GAP]; (c) period-level assembly `A(f,g)=Σ_λ cocycle-terms` via
  `edgePotentialSum_cycle_eq_zero` over the finite coset side-pairing [FOUNDED bookkeeping]. The
  RESEARCH-scale geometric L3 is **avoidable**.

## Recommended build order (cleanest = Shimura's)

1. **Re-target, don't extend.** Replace the body of `periodPairingA_eq_boundary_period` (or add a
   sibling `periodPairingA_eq_cocycle_sum`) to produce the loose `Σ cᵢ rawPairing f(yᵢ)` with
   `yᵢ = (divDiff(a_i•c)c)⊗Qᵢ` (cocycle-defect divisors), bypassing
   `exists_pairedBoundary_periodPairingA_eq`. Do NOT touch the proven `interior_edges_cancel_sum`
   itself (it then becomes *dead* and can be dropped on `main` by the cleanup fleet).
2. **Bridge** `modSymRep N m : Representation ℤ SL(2,ℤ)` to `Rep ℤ SL(2,ℤ)` and expose
   `u_f := cuspDiff f · ∈ cocycles₁`; prove the cocycle identity from `cuspValue_symRep_gamma`.
3. **Assemble** `A(f,g)` over the *single* FD `Gamma1_fundDomain_PSL N`: L1/L2 (proven) →
   boundary contour → group by side-pairing (`PairedBoundary` is the carrier; periods telescope by
   `edgePotentialSum_cycle_eq_zero`) → finite `Σ_λ ᵗu_f(a_λ⁻¹)W·[g-weight]`.
4. **Injectivity** is then unchanged (`periodMap'_petN_self`/`periodMap'_injective`, proven).

**Optional skeleton:** not written — the cleanest realization re-targets an existing (sorry-free!)
lemma onto its already-declared loose existential, rather than introducing new leaves; and the
instructions forbid editing the proven files. The new leaves (a)/(b)/(c) belong in a fresh file
(e.g. `ModularSymbols/Cocycle822.lean`) when the worker starts — their statements are dictated by
§3 L4 and §6 route 1 and are all FOUNDED/API-GAP.
