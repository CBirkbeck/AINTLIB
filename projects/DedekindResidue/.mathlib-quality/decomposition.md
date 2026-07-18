# Decomposition — DedekindResidue (Theorem 1 spine)

Source: Belabas–Friedman, *Computing the residue of the Dedekind zeta function*
(arXiv:1305.0035), `refs/ANCF/1305.0035.pdf`. This first pass captures the **paper's own
proof structure** for Theorem 1 and flags the three results the paper *cites without
proof* as deep sub-projects (SP1/SP2/SP3), each to be decomposed from its own reference
in a focused `/develop --decompose` pass.

## Skeleton location (builds clean; `lake build DedekindResidue.MainTheorem` ✓, 4 sorries)

- `DedekindResidue/AuxiliaryFunction.lean` — `gAux` (eq 6), `auxF` (eqs 11–12) — **sorry-free**
- `DedekindResidue/CompletedZeta/FunctionalEquation.lean` — `completedDedekindZeta`,
  `completedDedekindZeta_one_sub` — **stubs (SP1)**
- `DedekindResidue/CompletedZeta/GRH.lean` — `GeneralizedRiemannHypothesis` — **sorry-free**
- `DedekindResidue/MainTheorem.lean` — `bSum` (stub), `fK` (sorry-free modulo `bSum`),
  `belabas_friedman_thm1` (stub statement)

## Result R: `belabas_friedman_thm1` (Theorem 1)

### Source statement (verbatim, p. 2)
> "Let K be a number field of degree n > 1, let κ_K be the residue of the Dedekind zeta
> ζ_K(s) at s = 1, and let Δ_K be the absolute value of the discriminant of K. Assume GRH,
> i.e. that ζ_K(s) ≠ 0 and ζ_ℚ(s) ≠ 0 whenever Re(s) > 1/2. Then, for any real X ≥ 69, the
> difference |log κ_K − f_K(X)| is bounded above by
> (2.324 log Δ_K)/(√X log(3X)) · ((1 + 3.88/log(X/9))(1 + 2/√(log Δ_K))² + 4.26(n−1)/(√X log Δ_K))."

Lean ↔ source: `belabas_friedman_thm1` asserts exactly this, with `κ_K =
NumberField.dedekindZeta_residue K`, `Δ_K = |NumberField.discr K|`, `n = Module.finrank ℚ K`,
`GRH` = `GeneralizedRiemannHypothesis K` (the `ζ_K` side) `+ RiemannHypothesis` (the `ζ_ℚ`
side). Both are hypotheses, not axioms.

### Plain-English proof (paper, "Proof of Theorem 1", pp. 10–12)
Apply **Lemma 4** with `k = ℚ`, `a := log 9`, `T := log X` (the hypothesis `0 < a < T`
holds as `X > 9`). A short calculation gives `1/g(T) − 1/g(T−a) = 2√X log(3X)/3` (eq 20)
and `A(T) − A(T−a) = B_K(X) − B_K(X/9)`, so `f_K(X)` appears. Lemma 4 then bounds
`(2√X log(3X)/3)|log κ_K − f_K(X)|` by `c_{a,T} ∑_ρ^{K+ℚ} 1/(¼+γ_ρ²) + (n_K−n_ℚ)a
e^{−(T−a)/2} β(T−a)` (eq 21). The zero-sum over `ζ_ℚ` is classical (`= 0.023095…`); the
zero-sum over `ζ_K` is bounded by **Lemma 5** (Landau–Stark) using `σ = 1 + (log Δ_K)^{−1/2}`,
giving `(√(log Δ_K) + 2)²`. Collecting constants (`X ≥ 68.1`, `β(log(X/9)) < 1`) yields the
three numerical constants `3/2(1+log9/4) < 2.324`, `6/(1+log9/4) < 3.88`,
`3log9/(1+log9/4) < 4.26`.

### Dependency tree (mirrors the paper)

- **R** `belabas_friedman_thm1` (Thm 1, pp. 10–12)
  - **L4** `lemma4` — the "`T` and `T−a`" trick (Lemma 4, eqs 14–17, pp. 7–9). *Internal.*
    Source proof uses the mean value theorem on `sin(γT)`, the decreasing integrals
    `q(T)`, `q̃(T)` (eq 17), and the decreasing `β(U)`. Uses GRH (`γ_ρ ∈ ℝ`).
    - **L3** `lemma3` — explicit formula applied to `F_{s,X}` (Lemma 3, eq 13, pp. 5–7).
      *Internal.* Valid for `Re s > 1` by the explicit formula; continued to `Re s > ½`
      by analytic continuation (GRH gives `γ² + h² ≠ 0`).
      - **L2** `fourier_auxF` — Fourier transform `F̂_{s,X}` (Lemma 2, eq 8, pp. 5–6).
        Leaf-ish: elementary calculus (two integrations by parts, eq 7) once `auxF` and
        the Fourier integral are in place. → depends on `auxF` (done) + mathlib Fourier.
      - **AG-SP2** the Weil–Poitou **explicit formula** (eqs 1, 3, p. 3). **API GAP.**
      - **[Euler product]** `−ζ'_K/ζ_K = Σ Λ_K` for `Re s > 1` → **Chebotarev**
        `NumberFieldEulerProduct` (leaf, project).
    - **AG-SP3** **Stark's formula** (Lemma 5, eq 19, pp. 8–11): `Σ_ρ 1/(σ−ρ) =
      ½log Δ_K + 1/(σ−1) + 1/σ − ½ d_{K,σ}`, and `Σ_ρ (¼+γ_ρ²)^{−1} = O(log Δ_K)`.
      **API GAP.**
  - **[classical ζ_ℚ zero sum]** `Σ_ρ (¼+γ_ρ²)^{−1} = C/2 + 1 − log(4π)/2 = .023095…`
    (p. 11, Davenport §12) → mathlib `RiemannHypothesis` + Riemann-ζ zeros (leaf).
  - **[bridge]** `fK`, `bSum` (`f_K`, `B_K`, p. 2) — project defs; `Residue.lean` ties the
    bound to `log(h_K R_K)` via `dedekindZeta_residue`.

### API gaps — each needs its own reference-driven sub-decomposition

- **SP1** (foundation, under L3/L4/SP2/SP3): general-`K` completed `ζ_K`, meromorphic
  continuation, functional equation `Λ_K(s)=Λ_K(1−s)`, Hadamard product / zero set.
  Not in mathlib (only ℚ, Dirichlet-L; cyclotomic in FltRegularBernoulli). **Route
  (chosen):** mirror mathlib `AbstractFuncEq`/`RiemannZeta` + FltRegularBernoulli
  cyclotomic, via the theta function over the Minkowski ideal lattice + Poisson
  summation. Skeleton stubs: `completedDedekindZeta`, `completedDedekindZeta_one_sub`.
- **SP2** the Weil–Poitou explicit formula (AG-SP2). Depends on SP1. **Route:**
  Poitou (Numdam) / Lang *ANT* Ch. XVII / Iwaniec–Kowalski §5 — contour integral of
  `−Λ'_K/Λ_K` against a test function.
- **SP3** Stark's formula (19) + Landau–Stark bound (AG-SP3). Depends on SP1 (log-derivative
  of the FE + Hadamard product). **Route:** Stark 1974 eq (9); Landau §180.

### Notes on faithfulness
- The paper's proof of Theorem 1 is self-contained **given** the explicit formula (SP2),
  Stark's formula (SP3) and the analytic substrate (SP1); it does not prove those. Per the
  source-faithfulness rule, SP1/SP2/SP3 are decomposed from *their own* references, not
  invented from this paper. Their per-leaf trees (with verbatim quotes + adversarial passes)
  are authored in their focused passes.
- L2 (`fourier_auxF`) is the one spine leaf dischargeable now from mathlib (Fourier +
  `auxF`); it is the natural first Tier-3 target once SP-independent.

---

# SP1 decomposition — completed ζ_K + functional equation (route study, 2026-07-01)

**Verified facts (mathlib + AINTLIB, this pin):**
- Riemann model: `completedRiemannZeta_one_sub` rests on `jacobiTheta₂_functional_equation`
  (`MLB/NumberTheory/ModularForms/JacobiTheta/TwoVariable.lean:469`, via 1-D Poisson) fed
  through `WeakFEPair`/`StrongFEPair` (`MLB/NumberTheory/LSeries/AbstractFuncEq.lean:81,100`).
- Dirichlet model: `DirichletCharacter.IsPrimitive.completedLFunction_one_sub`
  (`DirichletContinuation.lean:284`) + `rootNumber` (`:272`).
- Cyclotomic precedent (abelian): `completedDedekindZetaCyclotomic = completedRiemannZeta ·
  ∏_{χ≠1} completedLFunction χ` (FltRegularBernoulli `CompletedDedekindZeta.lean:55`); its FE
  (`:66`, sorry-free) is a **half-FE** carrying `∏ rootNumber χ`, not the clean `Λ(1−s)=Λ(s)`.
- Chebotarev `dedekindZeta_eq_prod_artinDirichletSeries` (`ZetaProduct.lean:2769`): abelian
  factorisation as a **naked Dirichlet series** (Re s>1) — no Gamma factors, no completion, no FE.
- **NOT FOUND anywhere:** n-dimensional / lattice Poisson summation; multivariate Gaussian
  theta transformation; Epstein / ideal-lattice theta; Artin L-functions; the
  conductor–discriminant identity `|d_K| = ∏ cond(χ)`.

## Two routes to the ζ_K functional equation

**Route T (Hecke theta — the only route valid for GENERAL K).** Θ_K(t) over the Minkowski
ideal lattice → transformation law by n-dim Poisson → Mellin → `completedDedekindZeta` → FE,
summed over the ideal class group. **Blocked on three missing mathlib foundations, each a
deep sub-project:**
- **AG-P** n-dimensional / lattice Poisson summation (only 1-D `Real.tsum_eq_tsum_fourier` exists).
- **AG-Θ** multivariate Gaussian Fourier self-duality + the ideal-lattice theta transformation.
- **AG-E** the ideal-lattice theta / Epstein-type zeta and its sum over `ClassGroup 𝓞_K`.
Depth: each is comparable to a mathlib PR of its own; AG-P underpins AG-Θ underpins AG-E.

**Route A (abelian factorisation — only valid for ABELIAN K).** For abelian `K/ℚ`,
`ζ_K = ∏_χ L(χ,s)` over the characters `χ` of `Gal(K/ℚ)` (Dirichlet characters via class field
theory). Define `completedDedekindZeta K := ∏_χ completedLFunction χ`; the FE follows from the
per-character `completedLFunction_one_sub`. **Reachable now**, but with two real sub-gaps:
- **AG-W** `∏_χ rootNumber χ = 1` (Artin root number of the regular representation) — needed to
  turn the half-FE into the clean `Λ_K(1−s) = Λ_K(s)`. Not in mathlib; a theorem in its own right.
- **AG-CD** conductor–discriminant `|d_K| = ∏_χ cond(χ)` — needed to identify the conductor in
  `completedDedekindZeta` with `|discr K|`. Not in mathlib.

## Leaf decomposition (Route A, abelian-first — the reachable near-term target)

`CompletedZeta/` (abelian scope; general `K` deferred to Route T):
- **S1.1** `completedDedekindZeta` (abelian) `:= completedRiemannZeta · ∏_{χ≠1} completedLFunction χ`
  → mirrors FltRegularBernoulli `:55` (leaf, project-precedent).
- **S1.2** meromorphic continuation + poles at `0,1`; residue at `1` `= dedekindZeta_residue K`
  → from `completedLFunction` analyticity + the `ζ_K = ∏ L(χ)` value at `s=1` (Chebotarev
  `dedekindZeta_eq_prod_artinDirichletSeries`) (internal; needs the abelian dictionary
  `Gal(K/ℚ)`-char ↔ Dirichlet-char, itself partly in Chebotarev `ZetaProduct`).
- **S1.3** half-FE `∏_χ completedLFunction_one_sub` → mirrors FltRegularBernoulli `:66` (leaf-ish).
- **AG-W** `∏_χ rootNumber χ = 1` → **deep gap** (own sub-decomposition).
- **AG-CD** `|d_K| = ∏_χ cond(χ)` → **deep gap** (own sub-decomposition).
- **S1.4** clean FE `completedDedekindZeta_one_sub` from S1.3 + AG-W + AG-CD (internal).
- **S1.5** Hadamard product / zero set / `∑_ρ` convergence → from the product of the
  `completedLFunction` Hadamard products (internal; per-factor order-1 growth).

`GammaFactor.lean`: `Γℝ`, `Γℂ` and the archimedean-factor bookkeeping → mathlib Deligne (leaf).

## Honest assessment

The **general-K** ζ_K functional equation is blocked on three foundational analytic pieces
absent from mathlib (n-dim Poisson, multivariate theta, ideal-lattice/Epstein theta) — Route T
is a multi-foundation effort, each piece a project on its own. The **abelian-K** case (Route A)
is reachable by reusing mathlib's Dirichlet-L completions, but still requires two genuine new
theorems (AG-W root-number product, AG-CD conductor–discriminant). There is no shortcut to
general K: the Artin-L route is equally absent from mathlib. This is the true bottom of the
project and the point where the general-vs-abelian scope must be reconciled with the effort
budget.

## Decision (2026-07-01): build the general theta stack (Route T)

The project owner chose the **general-K theta route** over abelian-first. SP1 is therefore
decomposed as the theta stack, bottom-up. Grounded against mathlib at this pin:

**Exists (reuse):** `ZLattice` + `ZLattice.covolume` + `Zspan.fundamentalDomain`
(`Algebra/Module/ZLattice/{Basic,Covolume}.lean`); `VectorFourier.fourierIntegral` on a f.d.
inner-product space (`Analysis/Fourier/FourierTransform.lean`); Gaussian Fourier transform +
integral (`Analysis/SpecialFunctions/Gaussian/{FourierTransform,GaussianIntegral}.lean`);
Fourier inversion (`Analysis/Fourier/Inversion.lean`); the Minkowski ideal lattice + fundamental
cone / unit action (`NumberField/CanonicalEmbedding/{Basic,FundamentalCone,NormLeOne}.lean`,
with `covolume` tied to `√|discr|`); 1-D `jacobiTheta` as the model to generalise.

**Missing (build, in order):**
- **AG-P** — *n-dimensional Poisson summation* over a `ZLattice` (dual lattice + covolume
  factor). mathlib has only 1-D `Real.tsum_eq_tsum_fourier`; **no dual lattice** in `ZLattice/`.
  Self-contained real analysis — **the concrete starting brick.** Sub-tree: (P.1) dual lattice
  of a `ZLattice`; (P.2) Poisson on `ℤⁿ` (iterate 1-D / torus Fourier series); (P.3) transport
  to a general lattice via a linear change of variables + covolume.
- **AG-Θ** — the *lattice Gaussian theta* `Θ_L(t)=∑_{x∈L} e^{-πt‖x‖²}` and its transformation
  law `Θ_L(1/t)=t^{n/2}·covol-factor·Θ_{L*}(t)`, from AG-P + n-dim Gaussian self-duality
  (assemble from the 1-D `Gaussian/FourierTransform`).
- **AG-E** — the *Hecke construction*: the ideal-lattice theta, integrated over a fundamental
  domain of the unit action (`FundamentalCone`) and summed over `ClassGroup 𝓞_K`, Mellin → the
  gamma factors `Γℝ^{r₁}Γℂ^{r₂}` and `completedDedekindZeta`; the FE from AG-Θ. **Deepest node;
  needs a reference** (Tate's thesis / Lang *ANT* XIII–XIV / Neukirch VII §5 — a PDF into `refs/`).

**Then (from AG-E):** S1.4 clean FE `completedDedekindZeta_one_sub`; S1.2 continuation + poles
tied to `dedekindZeta_residue`; S1.5 Hadamard product / zero set (`γ_ρ ∈ ℝ` under GRH).

**Immediate next action:** `/develop --decompose` scoped to **AG-P** (n-dim Poisson) — a
self-contained real-analysis pass, no external reference needed — then build it via `/beastmode`.
Acquire the AG-E reference in parallel.

## AG-P decomposition — n-dimensional Poisson summation (grounded 2026-07-01)

**Source (to generalise):** mathlib's 1-D Poisson `Real.tsum_eq_tsum_fourier`
(`Analysis/Fourier/PoissonSummation.lean:102`), proved via the periodization's Fourier
coefficients `Real.fourierCoeff_tsum_comp_add` (`:51`) on `AddCircle 1`. The d-dimensional
torus analogue of that machinery **already exists**: `Analysis/Fourier/AddCircleMulti.lean`
— `mFourier`/`mFourierBasis` (`HilbertBasis (d→ℤ) ℂ L²(UnitAddTorus d)`, `:265`),
`mFourierCoeff` (`:246`), L²/uniform convergence (`hasSum_mFourier_series_L2 :285`), and the
box↔torus measure equivalence (`measurePreserving_equivPiIoc :168`, `integral_preimage :193`).
So AG-P mirrors the 1-D proof, swapping `AddCircle` → `UnitAddTorus d` via `AddCircleMulti`.

**Target statement:** for a full `ZLattice L` in a finite-dim real inner-product space `V`
(dual `L*`, covolume `covol L`) and a Schwartz (or suitably-decaying) `f : V → ℂ`,
`∑_{x∈L} f x = (covol L)⁻¹ · ∑_{y∈L*} 𝓕f y`.

**Leaves (bottom-up):**
- **P.1** `ZLattice.dual` — the dual lattice `L* = {y | ∀ x∈L, ⟪x,y⟫ ∈ ℤ}` and its basic API
  (it is a `ZLattice`; `covol L* = (covol L)⁻¹`; double-dual). **Gap** — nothing in `ZLattice/`
  (`fundamentalDomain` exists at `Basic.lean:92`, no `dual`). Sub-leaves: dual as a `Submodule`
  over `ℤ`; `IsZLattice` instance; covolume-inverse (from `ZLattice.covolume` + the dual basis).
- **P.2** `poissonSummation_zspan` — Poisson for the standard lattice `ℤⁿ ⊂ (ι → ℝ)`:
  generalise `Real.fourierCoeff_tsum_comp_add` → the periodization `x ↦ ∑_{n∈ℤⁿ} f(x+n)` on
  `UnitAddTorus ι`, expand in `mFourierBasis`, evaluate the coefficients as `𝓕f` at integer
  points. Discharged by: `AddCircleMulti` (`mFourierCoeff`, `hasSum_mFourier_series_L2` +
  the continuous-summable uniform-convergence variant) + `VectorFourier.fourierIntegral`
  (`FourierTransform.lean`). **Internal** — the analytic heart; sub-decompose against the
  1-D proof's structure.
- **P.3** `poissonSummation_zlattice` — transport P.2 to a general `ZLattice L` via the
  linear equiv `L ≅ ℤⁿ` (a `Basis` of `L`), change of variables in `𝓕`, picking up the
  `covol L` Jacobian and mapping `ℤⁿ`'s dual to `L*`. Discharged by: `ZLattice.covolume`,
  `Zspan.basis`, `VectorFourier` change-of-variables. **Internal.**

**Feasibility:** grounded — every analytic ingredient (multivariate torus Fourier series,
n-dim Fourier transform, lattice covolume) exists; the only genuinely new piece is the dual
lattice (P.1), which is elementary linear algebra over `ℤ`. No external reference needed.
AG-P is a clean, self-contained, mathlib-worthy sub-project — the right first brick.

**Note (generality):** AG-P → AG-Θ → AG-E is what makes `completedDedekindZeta` + FE hold for
**every** number field, hence GRH and Theorem 1 general (not abelian-only). The abelian
`ζ_K = ∏ L(χ)` route would cap the whole result at abelian extensions; the theta stack is the
price of the paper's full generality.
