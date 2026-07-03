# Ticket Board — DedekindResidue

## Summary
- Bottom-up (SP1 → SP2/SP3 → Tier 3). The three deep sub-projects are **epics**: each
  expands into leaf tickets via its own `/develop --decompose` pass (needs its reference).
- Concrete near-term (SP-independent, actionable now): T001, T002, T003, T-ADM, T-BV.
- Tier-3 spine (T010–T014): blocked on the epics.
- Done ✓: T001 (bSum), T002 (auxF API + measurability) — build green, axiom-clean.
- Open near-term: 3 (T003 Lemma 2, T-ADM, T-BV) · Epics needing decomposition: 3 (SP1 w/ 8 sub-epics, SP2, SP3) · Blocked (tier-3 spine): 5
- Expert-review adjustments folded in (2026-07-01): +SP1-AC, +SP1-N, +T-ADM, +T-BV; AGP
  Gaussian-first; AGE sealed unit-domain API; GRH dual-form. See `expert-review/2026-07-01/`.

---

## Epics (need their own `/develop --decompose` pass before leaf tickets exist)

### [SP1] Completed ζ_K + FE + Hadamard + analytic control — the general theta stack
- **Status**: **DONE** (2026-07-03: `exists_isCompletedDedekindZeta` + FE + A0–A6 analytic control; see decomposition-sp1ac.md + HANDOVER) · **Files**: `CompletedZeta/*.lean`
- **Type**: epic (foundation) · **Depends on**: N → AG-P → AG-Θ → AG-E → FE → AC · **Blocks**: SP2, SP3, T010+
- **Route confirmed (expert review 2026-07-01)**: general-K **Hecke theta route**, NOT Tate
  (adelic substrate too large) and NOT abelian (validation-only). Implement as a
  **Hecke-classical proof with Tate-style normalisation discipline**. Narrowed next milestone
  (review): (a) reusable lattice/Poisson/theta layer → (b) a *sealed* Hecke partial-zeta
  theorem → (c) `Λ_K` with **all constants fixed**. See `decomposition.md`. Sub-epics, bottom-up:

  - **[SP1-N] normalisation** (`Normalisation.lean`) — **DO EARLY** (review Q5, archimedean
    constants). Pin the `Γℝ/Γℂ` convention (`Γℂ(s)=2(2π)^{-s}Γ(s)`), state the residue constant
    of `Λ_K` with the **`2^{r₂}` factor explicit**, and write conversion lemmas *now* so no
    downstream constant chase silently drifts by a hidden `2^{r₂}`/`π^{r₂}`/`√Δ_K`.
  - **[SP1-AGP] n-dim Poisson summation** over a `ZLattice` — **START HERE** (self-contained;
    no external reference). **Gaussian-class first, full-Schwartz deferred (review Q2).** Leaves
    in order: (P.1) **dual lattice** of a `ZLattice` + covolume identities [gap — none in
    mathlib]; (P.2) Poisson on `ℤⁿ` *for the Gaussian class* [from 1-D `Real.tsum_eq_tsum_fourier`
    / torus Fourier]; (P.3) transport to a general full lattice + covolume factor
    [`ZLattice.covolume`, `VectorFourier.fourierIntegral`]. (P.opt) general Schwartz-class
    Poisson — **optional, off the critical path**, only if cheaply reusable. **Next action**:
    `/develop --decompose` scoped to SP1-AGP.
    - **P.1 DONE ✓✓ (2026-07-01, `CompletedZeta/DualLattice.lean`, build green + axiom-clean
      `{propext, Classical.choice, Quot.sound}`)**: `dualZLattice` (via `innerₗ` +
      `LinearMap.BilinForm.dualSubmodule`), `mem_dualZLattice`, `innerₗ_nondegenerate`, the
      structural lever `dualZLattice_eq_span` (`L♯ = span ℤ (dual basis)`), the
      `instDiscreteTopologyDualZLattice` + `instIsZLatticeDualZLattice` instances (free from
      `dualZLattice_eq_span` + `ZSpan.span_top`), the measure fact
      `volumeReal_fundamentalDomain_orthonormal` (`vol.real(FD b₀)=1`), AND the covolume
      reciprocal `covolume_dualZLattice_mul` (`covolume L♯ · covolume L = 1`). NB `Basis` is now
      `Module.Basis`; `⟪x,y⟫` (no `_ℝ` subscript) via `open scoped RealInnerProductSpace`.
    - **[SP1-AGP-COVOL] covolume reciprocal — DONE ✓✓** (2026-07-01): `covolume_dualZLattice_mul`.
      Proof exactly as sketched: (1) `ZLattice.covolume_eq_det_mul_measureReal (μ := volume)` with
      `b₀ := (EuclideanSpace.basisFun ι ℝ).toBasis` (reindex `chooseBasis` to `ι` via
      `Fintype.equivOfCardEq` + `finrank_euclideanSpace`); (2) `volumeReal_fundamentalDomain_orthonormal`;
      (3) `Module.Basis.span hlinind` as the dual ℤ-basis (fold post-`dualZLattice_eq_span` goal with
      `← hc, ← hcstar`); (4) `MᵀM* = 1` from `apply_dualBasis_left` (δ_ij) + `OrthonormalBasis.sum_inner_mul_inner`
      Parseval + `real_inner_comm`, then `Module.Basis.det_apply` + `Matrix.det_transpose` + `Matrix.det_mul`.
    - **P.2 leaf (e) sub-decomposition** (2026-07-01, per HANDOVER.md §4; footholds sig-verified):
      (e1) `intEquivSpanBasisFun : (ι→ℤ) ≃ span ℤ (range (Pi.basisFun ℝ ι))` — forward map explicit
      (coe = integer vector, `Equiv.ofBijective`; surjectivity by `Submodule.span_induction`
      "integer coordinates"); (e2) Ioc-box `=ᵐ[volume]` Ico-box (symmDiff ⊆ coordinate-hyperplane
      translates, null via `Measure.addHaar_submodule` + translation invariance); (e3) tiling
      `Integrable f → ∫ f = ∑'_{n:ι→ℤ} ∫_{IocBox} f(x + n)` via `ZSpan.isAddFundamentalDomain
      (Pi.basisFun ℝ ι)` + `IsAddFundamentalDomain.integral_eq_tsum'` (+`lintegral_eq_tsum` variant;
      `VAddInvariantMeasure` via `(inferInstance : … L.toAddSubgroup …)` — Covolume.lean:87 idiom)
      + (e1)-reindex + (e2); (e4) `Integrable (char(π·) • g(toLp·))` from h_norm (box-lintegrals ≤
      sup-norms, `volume IocBox = 1` by `volume_pi_pi`); (e5) `integral_tsum` swap on the box (same
      bounds); (e6) character shift-invariance `mFourier(-m)(π(x+n)) = mFourier(-m)(πx)`;
      (e) `mFourierCoeff_torusPeriodizationFun = 𝓕g(zpoint m)` assembling e1–e6 +
      `UnitAddTorus.mFourierCoeff_eq_integral` + `fourierIntegral_zpoint_eq`; (f) Poisson assembly
      via `hasSum_mFourier_series_apply_of_summable` at `0`.
    - **P.2 DONE ✓✓ (2026-07-01, `CompletedZeta/PoissonSummation.lean`, sorry-free, build green,
      all public decls axiom-clean)**: `tsum_eq_tsum_fourier_zpoint` — n-dim Poisson over `ℤ^ι` —
      fully proven via the sub-decomposition above (e1–e6 + f all landed; key lemma
      `mFourierCoeff_torusPeriodizationFun`). **Next: P.3 transport** to a general lattice
      `L ⊂ EuclideanSpace ℝ ι` (pull back along the lattice-basis linear equiv; covolume factor
      `|det|⁻¹` via `ZLattice.covolume_eq_det_mul_measureReal`; dual lattice on the 𝓕 side via
      `dualZLattice` + `covolume_dualZLattice_mul` from P.1), then AGΘ Gaussian instantiation
      (`fourier_gaussian_innerProductSpace` + `summable_gaussian_zlattice` discharge h_norm/h_sum).
    - **P.3 DONE ✓✓ (2026-07-01, `CompletedZeta/PoissonLattice.lean`, sorry-free, axiom-clean)**:
      `tsum_eq_tsum_fourier_zlattice` — **Poisson over an arbitrary ℤ-lattice**
      `∑'_{v∈L} g(v) = covol(L)⁻¹ • ∑'_{w∈L♯} 𝓕g(w)` — plus the GL Fourier change-of-variables
      `fourier_comp_linearEquiv` (genuinely new vs mathlib's isometry-only case), P3b/c/d
      identification lemmas, and the norm/summability transport helpers. **SP1-AGP is complete.**
      Next epic: **SP1-AGΘ** (`CompletedZeta/ThetaLattice.lean`): (Θ1) sup-norm Gaussian translate
      estimate on compacts; (Θ2) discharge h_norm for `g_t = cexp(-πt‖·‖²)` via
      `summable_gaussian_zlattice`; (Θ3) `𝓕 g_t` via mathlib `fourier_gaussian_innerProductSpace`
      (b := πt ⇒ `𝓕g_t(w) = t^{-n/2} cexp(-π‖w‖²/t)`); (Θ4) the transformation law
      `Θ_L(t) = t^{-n/2} covol(L)⁻¹ Θ_{L♯}(1/t)` for `t > 0` (+ `covolume_dualZLattice_mul` to
      flip L↔L♯).
    - P.3 leaf plan history (2026-07-01, footholds sig-verified): (P3a) `fourier_comp_linearEquiv`:
      `𝓕(g∘T) w = |det T|⁻¹ • 𝓕 g (adjoint T.symm w)` for `T : EuclideanSpace ≃ₗ[ℝ] EuclideanSpace`
      — via `T.toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv`, `integral_map_equiv`,
      `Measure.map_linearMap_addHaar_eq_smul_addHaar` (det ≠ 0 from `LinearEquiv.isUnit_det'`),
      `integral_smul_measure`, `LinearMap.adjoint_inner_right` (real inner, no conj); (P3b) sum-side
      reindex `∑' v : L ↔ ∑' n : ι → ℤ` via `b.repr` + `Finsupp.equivFunOnFinite` + `T (zpoint n) =
      lattice elt with coords n` (`Module.Basis.equiv (basisFun) c (Equiv.refl)`); (P3c) dual-side:
      `adjoint T.symm (zpoint m)` = dual basis of `c` (⟪adj T⁻¹ eᵢ, c j⟫ = δᵢⱼ) ⇒ ranges over
      `dualZLattice L` by P.1's `dualZLattice_eq_span`; (P3d) `|det T| = covolume L` via
      `covolume_eq_det_mul_measureReal` + `volumeReal_fundamentalDomain_orthonormal`; (P3) assemble:
      `∑'_{v∈L} g(v) = covol(L)⁻¹ ∑'_{w∈L♯} 𝓕g(w)` with honest L-side hypotheses (transport
      h_norm/h_sum through T by compact-image + equiv-reindex). File: `CompletedZeta/PoissonLattice.lean`.
    - P.2 history (2026-07-01, `CompletedZeta/PoissonSummation.lean`): file
      created with `zpoint` (ℤ^ι ↪ EuclideanSpace, axiom-clean), `summable_gaussian_zlattice`
      (Gaussian `exp(-a‖x‖²)` summable over any lattice — DONE, axiom-clean: `ZLattice.summable_norm_rpow`
      dominated via `rexp_neg_quadratic_isLittleO_rpow_atTop` + finite sub-level sets from
      `Metric.finite_isBounded_inter_isClosed`). **Remaining P.2**: `tsum_eq_tsum_fourier_zpoint`
      (the Poisson formula, currently `sorry`) via the multivariate torus Fourier series
      `UnitAddTorus.hasSum_mFourier_series_apply_of_summable` + the key new lemma
      `mFourierCoeff_periodization` (`mFourierCoeff (periodization g) m = 𝓕g (zpoint m)`, the
      n-dim analogue of mathlib's `Real.fourierCoeff_tsum_comp_add`). NB torus base is `ι → ℝ`;
      bridge to `EuclideanSpace`/`𝓕` via `PiLp.volume_preserving_toLp` + character factorisation.
  - **[SP1-AGΘ] — DONE ✓✓ (2026-07-01, `CompletedZeta/ThetaLattice.lean`, sorry-free,
    axiom-clean)**: `thetaLattice` (`Θ_L(t) = ∑'_{v∈L} e^{-πt‖v‖²}`), `summable_thetaLattice`,
    `gaussianCM` + `norm_gaussianCM_apply`, `finite_norm_le_zlattice`, Θ1
    `summable_norm_restrict_gaussianCM` (h_norm discharge), Θ3 `fourier_gaussianCM`
    (`𝓕 = t^{-n/2}·(t↦1/t)`), `summable_fourier_gaussianCM` (h_sum discharge),
    `ofReal_thetaLattice`, and **`thetaLattice_transform`:
    `Θ_L(t) = covol(L)⁻¹·t^{-n/2}·Θ_{L♯}(1/t)`** (`t > 0`) — the reviewer's milestone (a)
    "reusable lattice/Poisson/theta layer" is COMPLETE (P.1+P.2+P.3+Θ). Next: **SP1-AGE**
    (Hecke partial theta over ideal classes; reuse mixedEmbedding ideal lattices +
    codifferent-as-dualSubmodule, substrate-api §B/§F; unit domain sealed per review Q2).
  - **[SP1-AGE] decomposition (2026-07-01, recon verified against the pin)** — the GRH-stated
    path: a genuine `completedDedekindZeta` definition replacing the FunctionalEquation.lean
    sorry-def. **Mathlib windfalls found**: `FundamentalCone.idealSet K J` +
    `idealSetEquiv/idealSetEquivNorm` + `card_isPrincipal_norm_eq_mul_torsion` (the sealed
    unit-domain/ideal-counting API the review asked for — ALREADY in mathlib);
    `euclidean.mixedSpace K` (`WithLp 2` product, an inner-product space) with
    `toMixed : ≃L[ℝ] mixedSpace`, `volumePreserving_toMixed(_symm)`, `stdOrthonormalBasis`,
    `euclidean.integerLattice` (via `ZLattice.comap`); `mixedEmbedding.idealLattice` +
    `covolume_idealLattice = N(I)·2^{-r₂}√|Δ|`; `NormLeOne.lean` (cone norm-≤-1 volume);
    mathlib `mellin` machinery (`Analysis/MellinTransform.lean`). **Metric convention pinned
    (Q5)**: the PLAIN L² metric of `euclidean.mixedSpace` (no 2 at complex places) — covolume
    `𝓞_K = 2^{-r₂}√|Δ|` per mathlib; the compensating 2's live in `Γℂ = 2(2π)^{-s}Γ(s)`
    (SP1-N). Leaves, bottom-up:
    - **(AGE-0) DONE ✓✓ (2026-07-01, `ThetaLattice.lean`, sorry-free, axiom-clean)**:
      `weightedThetaLattice_transform` — the multivariable theta
      `∑_{v∈L} e^{-π∑cᵢvᵢ²} = covol(L)⁻¹(∏cᵢ)^{-1/2}∑_{w∈L♯} e^{-π∑cᵢ⁻¹wᵢ²}` for ANY positive
      weights (junk-free statement, bounds derived internally). Stack: `diagScale`
      (+adjoint/det/symm/congr), `weightedGaussianCM` (+structural identity `= gaussianCM 1 ∘
      diagScale √c`), `fourier_weightedGaussianCM` (via P3a), isotropic-comparison convergence
      layer, `ofReal_weightedTheta`. **Next: AGE-1** (euclidean ideal lattices).
    - (AGE-0) original plan [file `ThetaLattice.lean` extension]: for a positive
      self-adjoint `P` (diagonal-in-an-ONB suffices): `∑_{v∈L} e^{-π⟨Pv,v⟩} =
      covol(L)⁻¹·det(P)^{-1/2}·∑_{w∈L♯} e^{-π⟨P⁻¹w,w⟩}` — via `tsum_eq_tsum_fourier_zlattice`
      + `fourier_comp_linearEquiv` (P3a!) at `T = P^{1/2}` + `fourier_gaussianCM`. NEEDED
      because Hecke integrates the multivariable theta `Θ(t_w)` over the unit domain in
      `t`-space — the 1-parameter `thetaLattice_transform` suffices only for unit-rank 0.
    - **(AGE-4') GRH INTERFACE DONE ✓✓ (2026-07-01, sorry-free)**: `FunctionalEquation.lean`
      rebuilt as the characterisation interface (`completedZetaPrefactor`,
      `IsCompletedDedekindZeta`, proven uniqueness `.eqOn`); `GRH.lean` states
      `GeneralizedRiemannHypothesis` in the paper's verbatim `Re > 1/2` form over the
      characterisation. AGE-4's target is now precisely **non-vacuity**:
      `∃ Λ, IsCompletedDedekindZeta K Λ` via the theta-Mellin construction (+ FE of it).
    - **(AGE-1) DONE ✓✓ (2026-07-01, `CompletedZeta/IdealLattice.lean`, sorry-free, axiom-clean)**:
      `euclideanIdealLattice` + `idealZLattice ⊂ EuclideanSpace ℝ (index K)` (double
      `ZLattice.comap` along `euclidean.toMixed` then `(euclidean.stdOrthonormalBasis K).repr.symm`,
      instances via `inferInstanceAs` + upstream comap instances — NB statements need
      `open scoped Classical in`, the subtype Fintypes are classical), `covolume_idealZLattice
      = N(I)·2^{-r₂}·√|Δ_K|` (two `ZLattice.covolume_comap` transports +
      `covolume_idealLattice`), **`idealTheta`** (`Θ_I(t) = thetaLattice (idealZLattice K I) t`)
      and **`idealTheta_transform`** (covolume evaluated). REMAINING CHAIN TO AGE-4
      (non-vacuity of `IsCompletedDedekindZeta`): (AGE-2) identify
      `dualZLattice (idealZLattice K I)` with the ideal lattice of the codifferent twist
      (via the trace-form `dualSubmodule` = codifferent, `Different.lean`; gives the clean
      dual side of `idealTheta_transform`); (AGE-3) the **unit-averaged multivariable theta**:
      `g_I(t) := ∫_{u ∈ [0,1)^{r+s-1}} Θ-weighted(c(t,u)) du` with weights
      `c(t,u)_v = t^{1/n}·exp(⟨log-unit-basis combination⟩_v)` (log-unit basis from
      `NumberField.Units` Dirichlet machinery; box integral — Lebesgue, no surface measure;
      `weightedThetaLattice_transform` gives `g_I(1/t) = (covol,t)-factors·g_{I♯}(t)` after the
      `u ↦ -u` + unit-relabeling change of variables — the unit action permutes the lattice);
      (AGE-4) `Λ := prefactor-normalised ∑_{classes} N(J)^s·mellin(g_J − const)(s/2)` split at 1
      (mirror mathlib `completedRiemannZeta₀`/`WeakFEPair`), prove agreement on `Re s > 1`
      (ideal-counting via `FundamentalCone.idealSetEquivNorm` + per-point Mellin) and
      `s(s-1)Λ` entire ⇒ `∃ Λ, IsCompletedDedekindZeta K Λ` (GRH non-vacuity) + FE.
    - (AGE-1) original plan: `euclideanIdealLattice I := ZLattice.comap ℝ
      (mixedEmbedding.idealLattice K I) (toMixed K).toLinearMap` (mirror
      `euclidean.integerLattice`) + instances + covolume (via `volumePreserving_toMixed`) +
      transport to `EuclideanSpace ℝ (index K)` along `(stdOrthonormalBasis K).repr`
      (LinearIsometryEquiv: lattice/dual/covolume/theta all invariant).
    - **(AGE-2) DONE ✓✓ (2026-07-02, `IdealLattice.lean`, sorry-free, axiom-clean)**:
      `embeddingCoords` (+3 coordinate lemmas), `dualityWeights` `(1; 2,-2)`,
      **`inner_diagScale_embeddingCoords`** (`⟪D·ζb, ζa⟫ = Tr_{K/ℚ}(ba)` — the derived,
      proven pairing dictionary), `dualIdealUnit` + `absNorm_dualIdealUnit`
      (`N(I^∨) = N(I)⁻¹|Δ|⁻¹`), `fracAbsNorm_inv`, `mem_idealZLattice`, supports
      `eq_of_le_of_covolume_eq` (rigidity) + `covolume_zlattice_comap` (`|det|`-scaling,
      in DualLattice.lean), `prod_dualityWeights = (-4)^{r₂}`, `comap_le_dualZLattice`, and
      **`dualZLattice_idealZLattice`**: `(L_I)♯ = (diagScale dualityWeights)-twist of
      L_{I^∨}` — the dual of an ideal lattice IS the twisted codifferent-dual ideal lattice.
      Θ-side corollary ready: `idealTheta_transform`'s dual side is now identified.
      **Next (AGE-3)**: unit-box-averaged multivariable theta.
    - **(AGE-3) brick 1+2 DONE ✓ (2026-07-02, `CompletedZeta/HeckeTheta.lean`, sorry-free,
      axiom-clean)**: `placeWeights`, `sum_placeWeights_embeddingCoords_sq`
      (`∑ᵢcᵢζ(x)ᵢ² = ∑_w c_w·w(x)²`), **`heckeTheta I c`** (the multivariable theta with
      per-place weights), `mulCoords` (+`mulCoords_embeddingCoords`: mult-by-`x` in
      coordinates), `unitMulLatticeEquiv` (unit multiplication permutes the ideal lattice),
      and **`heckeTheta_unit_mul`** (`Θ(w(ε)²·c) = Θ(c)` — the Hecke unit symmetry).
      **Brick 3 DONE ✓ (2026-07-02)**: `dualPlaceWeights` (`c⁻¹` real, `4c⁻¹` complex),
      `placeWeights_dualPlaceWeights`, and **`heckeTheta_inversion`**:
      `Θ_I(c) = covol(L_I)⁻¹·(∏ᵢc)^{-1/2}·Θ_{I^∨}(c^∨)` — Hecke's multivariable theta
      functional equation for ideal lattices (weightedThetaLattice_transform +
      dualZLattice_idealZLattice + comap_equiv reindex, twist absorbed into weights).
      **L1/L2/L3 DONE ✓ (2026-07-02)**: `fullLog` (trace-zero extension, `fullLog_logEmbedding`,
      `fullLog_add`, `sum_fullLog = 0`), **`heckeWeights t u`** (`t^{1/n}·exp(2·fullLog/mult)`,
      positive; equivariance `heckeWeights_add_logEmbedding` ⇒
      `heckeTheta_heckeWeights_periodic` — integrand periodic mod `unitLattice`),
      `prod_heckeWeights_pow_mult` (`∏_w c_w^{mult w} = t`, the norm ray), and **`heckeG I t`**
      (the unit-box-averaged theta, `torsionOrder⁻¹·∫_{FD(unit basis)} Θ_I(c(t,u)) du`).
      **Duality bookkeeping DONE ✓ (2026-07-02)**: `fullLog_neg` + `dualPlaceWeights_heckeWeights`
      (`c^∨(t,u) = (1;4)·c(1/t,-u)` pointwise). **g-INVERSION ROUTE (derived 2026-07-02)**:
      (i) `prod_placeWeights` lemma (`∏_i placeWeights c i = ∏_w c_w^{mult w}`) ⇒ the middle
      factor of `heckeTheta_inversion` at `c(t,u)` is `t^{-1/2}` (norm-ray); (ii) decompose the
      `(1;4)`-factor: log-vector `(0; log 4)` = uniform `(2r₂·log4)/n·𝟙` + trace-zero `v₀`, so
      `(1;4)·c(1/t,-u) = c(4^{2r₂}/t, -u + u₀)` with `u₀ := (v₀-restriction)/2`-shift ⇒
      pointwise-in-`u` integrand inversion; (iii) box absorbs `-u+u₀`: FD-translation invariance
      for `unitLattice`-periodic integrands (`IsAddFundamentalDomain.setIntegral_eq` + translated/
      negated FD is an FD) using `heckeTheta_heckeWeights_periodic` ⇒
      **`heckeG_inversion : g_I(t) = covol(L_I)⁻¹·t^{-1/2}·g_{I^∨}(4^{2r₂}·t⁻¹)`**; (iv)
      integrability estimates (isotropic comparison per `u` + compactness of the box).
      **(i)+(ii)+(iii) ALL DONE ✓ (2026-07-02, commits 3a907b2e/90cb45f2/6de29331)**:
      `prod_placeWeights` + `prod_placeWeights_heckeWeights` (= t); `fullLog_restrict`
      (fullLog onto trace-zero), `dualShift`, `fullLog_dualShift`, `heckeWeights_mul_left`/
      `_add_right`, `ite_mul_heckeWeights`, `dualPlaceWeights_heckeWeights_eq`
      (`c(t,u)^∨ = c(4^{2r₂}t⁻¹, -u+dualShift)`); `setIntegral_fundamentalDomain_comp_neg_add`
      (u ↦ -u+s preimage of ZSpan box is an FD via `preimage_of_equiv`; periodic integrals agree)
      ⇒ **`heckeG_inversion` PROVEN, axiom-clean**. Remaining: (iv), then AGE-4 Mellin.
      **AGE-4 ROUTE (derived 2026-07-02, constants VERIFIED to cancel — target
      `∃ Λ, IsCompletedDedekindZeta K Λ` via mathlib `WeakFEPair`
      (`Mathlib.NumberTheory.LSeries.AbstractFuncEq`), the completedRiemannZeta machinery):**
      1. **`heckeG_smul`**: for `x ∈ K*`, `heckeG (x•I) t = heckeG I (|N(x)|²·t)`. Pieces:
         (a) translation-only FD invariance — derive from `setIntegral_fundamentalDomain_comp_neg_add`
         applied TWICE (`h := f∘neg` is periodic; shift `-s` then `0`), no new measure theory;
         (b) `xShift x : logSpace K` := restriction of `w ↦ mult_w·log(w x) − mult_w·log|Nx|/n`
         (zero-sum via `InfinitePlace.prod_eq_abs_norm` + `Real.log_prod`), `fullLog_xShift`
         mirror of `fullLog_dualShift`; (c) `(w x)² · heckeWeights t u w
         = heckeWeights (|Nx|²·t) (u + xShift x) w` mirror of `ite_mul_heckeWeights`
         (the `(1;4)` case IS the special case `y_w = mult_w·log(1;2)`);
         (d) `heckeTheta (x•I) c = heckeTheta I ((w·x)²·c)` — generalise `unitMulLatticeEquiv`
         to `mulCoords x` for `x ≠ 0`.
      2. **Normalised class theta** `Ĝ_C(x) := heckeG I (N(I)⁻²·β·x)` for any rep `I` of `C`,
         `β := 4^(r₂)/|Δ|` — class-invariant by 1. **Clean Hecke symmetry falls out**:
         `Ĝ_C(1/x) = √x · Ĝ_{C^∨}(x)` — coefficient is EXACTLY 1
         (covol_I⁻¹·N(I)·β^{-1/2} = 2^{r₂}|Δ|^{-1/2}·2^{-r₂}|Δ|^{1/2} = 1, using
         `covolume_idealZLattice = N(I)·2^{-r₂}√|Δ|` and `N(I^∨) = N(I)⁻¹·natAbs(Δ)⁻¹`).
      3. **`f := ∑_{C ∈ ClassGroup} Ĝ_C`** (finite sum; `C ↦ C^∨` a bijection) ⇒
         `f(1/x) = √x·f(x)`: a `WeakFEPair f f (k := 1/2) (ε := 1)` with
         `f₀ = g₀ = h·w⁻¹·vol(unit box)` (the `0 ∈ L` terms). Remaining analytic inputs:
         `hf_int` (LocallyIntegrableOn `Ioi 0`) + `hf_top` (rapid decay of `g_I(t) − g∞`,
         lattice tail estimate from `norm_weightedGaussianCM_le`).
         **STEPS 1–3 + ALL ANALYTIC INPUTS DONE ✓ (2026-07-02/03, `ThetaEstimates.lean` +
         `FEPair.lean`, commits 56e2431e/db7e9bef/a50e5f6d)**: shortest vector, real-Gaussian
         summability, `heckeTheta_eq_one_add` (0-split), `tsum_ite_gaussian_tail`,
         `heckeWeights_ge_of_bounded`, `exists_heckeTheta_dev_bound`,
         `continuousAt_heckeTheta_heckeWeights` (joint, `continuousOn_tsum`),
         `continuousOn_heckeG` (dominated), `unitBoxVol`, `exists_heckeG_dev_bound`,
         `isBigO_exp_neg_rpow`, class transfers, `heckeFConst = h·w⁻¹·vol`,
         `heckeF_sub_const_isBigO`, and **`heckeFEPair : WeakFEPair ℂ` ASSEMBLED** —
         mathlib gives `Λ₀` entire, `Λ` (poles at σ∈{0,1/2}, residues), `hasMellin`
         (Re σ > 1/2), FE `Λ(1/2−σ) = Λ(σ)`.
         **CONSTANT DERIVATION (2026-07-03, paper-verified)**: per class,
         `mellin(Ĝ_C − w⁻¹vol)(s/2) = s_C^{-s/2}·M_I(s/2)`, `s_C = N(I)⁻²β`; unfolding +
         `(t,u) ↦ y_w = c_w(t,u)(wa)²` factorises `M_I(s/2) = κ·Γ(s/2)^{r₁}π^{-r₁s/2}·
         Γ(s)^{r₂}π^{-r₂s}·N(I)^{-s}·∑_{𝔞∈[I⁻¹]}N𝔞^{-s}` (κ = Jacobian const, s-free);
         `s_C^{-s/2} = N(I)^s·β^{-s/2}` kills `N(I)^s`, and `β^{-s/2} = 2^{-r₂s}|Δ|^{s/2}`
         turns `π^{-s}Γ(s)` into `|Δ|^{s/2}·(Γℂ(s)/2)`: **`mellin(f−f₀)(s/2)
         = κ·2^{-r₂}·completedZetaPrefactor(s)·ζ_K(s)` — the adjust is s-INDEPENDENT**, so
         `completedDedekindZeta := (κ·2^{-r₂})⁻¹·P.Λ(s/2)` with `s(s−1)Λ` entire from
         `Λ = Λ₀ − f₀/σ − g₀/(k−σ)` (pole factors `2(s−1)`, `−2s` entire). Remaining Lean
         bricks: (α) mellin scaling `mellin (g∘(s_C·)) σ = s_C^{-σ}·mellin g σ`;
         (β) box-unfolding `w⁻¹∫_box ∑_{L∖0} = ∑_{(I∖0)/units} ∫_{logSpace}` (torsion w
         cancels; `IsAddFundamentalDomain`-unfolding + orbit structure);
         (γ) per-point `(t,u)→y` change of variables ⇒ Γ-product × `|Na|^{-2σ}` (pins κ);
         (δ) counting `∑_{(I∖0)/units}|Na|^{-s} = N(I)^{-s}·∑_{𝔞 integral ∈ [I⁻¹]}N𝔞^{-s}`
         (mathlib `FundamentalCone.idealSetEquivNorm`); (ε) sum over classes = `ζ_K`,
         define `completedDedekindZeta`, prove `IsCompletedDedekindZeta` (Re>1 agreement +
         entirety) ⇒ **`∃ Λ, IsCompletedDedekindZeta K Λ` — GRH non-vacuity**.
         **NAMED TARGET (user-confirmed 2026-07-03): `exists_isCompletedDedekindZeta :
         ∃ Λ : ℂ → ℂ, IsCompletedDedekindZeta K Λ`** — the inhabitation theorem making
         `GeneralizedRiemannHypothesis K` non-vacuous. All hard analytic bricks DONE as of
         045cd9a2 (β unfolding, δ+δ2 counting, γ `lintegral_M0_eq`); remaining is the (ε)
         assembly: ENNReal chain-glue per class → real-σ agreement → toReal/mellin
         identification (`heckeFEPair.hasMellin`) → identity theorem (Re s > 1) → the
         definition + both `IsCompletedDedekindZeta` conditions.
      4. `Λ_K(s) := (const-adjust)·P.Λ (s/2)`: `WeakFEPair.Λ₀` entire + explicit poles at
         `σ ∈ {0, 1/2}` ⇒ `s(s−1)Λ_K` entire ✓ second half of `IsCompletedDedekindZeta`.
      5. **Agreement on Re s > 1** (the big remaining brick): `P.hasMellin` +
         box-unfolding (`IsAddFundamentalDomain.integral_eq_tsum`: ∫_{FD}∑_{lattice} =
         ∑_{orbit reps}∫_{logSpace}; torsion `w` cancels `torsionOrder⁻¹` since `w(ζa)=w(a)`)
         + Fubini + per-point change of variables `(t,u) ↦ y_w = c_w(t,u)·(wa)²` +
         per-place 1-D Gamma integrals (`Γℝ` at real, `Γ(s)π^{-s}` at complex — the
         `2^{s-1}`-vs-`Γℂ` and `β^{s/2}` constants absorbed into the s-dependent
         const-adjust in 4) + ideal counting `∑_{a ∈ I∖0 mod units} |N a|^{-s} =
         N(I)^s·∑_{𝔞 integral, [𝔞]=[I⁻¹]} N𝔞^{-s}` (mathlib
         `FundamentalCone.idealSetEquivNorm`-style) summed over classes = `ζ_K`. Then
      AGE-4 Mellin (constants self-verifying — every identity proven; the `4^{2r₂}`/`2^{-r₂}`
      factors recombine against `covolume_idealZLattice`'s `(2⁻¹)^{r₂}` and `Γℂ`'s `2`).
      ORIGINAL box plan:
      `c(t,u)_w = t^{1/n}·exp(logunits-combination)` + `g_I(t) := ∫_{[0,1)^{r+s-1}} Θ(c(t,u)) du`
      + its inversion (from `weightedThetaLattice_transform` — note `heckeTheta I c` = the
      `weightedGaussianCM (placeWeights c)`-sum over `idealZLattice I` — +
      `dualZLattice_idealZLattice` + `heckeTheta_unit_mul` for the `u ↦ -u` change of variables).
      Then AGE-4 Mellin.
    - (AGE-2) original plan — **theta–ideal dictionary**: `‖x‖²` of a lattice point = `∑_w normAtPlace`-form;
      lattice points of `euclideanIdealLattice I` ↔ elements of `I`; norms via
      `intNorm`/`idealSetEquivNorm`.
    - **(AGE-3) partial theta & cone sums**: the ideal-class partial zeta as a cone-point sum
      (mathlib `idealSetEquivNorm`), Hecke's unit-domain integral representation.
    - **(AGE-4) Mellin**: `partialCompletedZeta` + **`completedDedekindZeta` as a genuine
      `mellin`-integral def** — replaces the sorry-def; `GeneralizedRiemannHypothesis` then
      fully stated (USER PRIORITY). FE from `thetaLattice_transform`/AGE-0 follows as SP1-FE.
  - [SP1-AGΘ] original plan: **lattice Gaussian theta** `Θ_L(t)=∑_{x∈L}e^{-πt‖x‖²}` + transformation law —
    depends on SP1-AGP (Gaussian class) + n-dim Gaussian self-duality (assemble from 1-D
    `Gaussian/FourierTransform`).
  - **[SP1-AGE] Hecke construction** — ideal-lattice theta over `FundamentalCone` (unit action) +
    `ClassGroup 𝓞_K`, Mellin → gamma factors + `completedDedekindZeta` + FE. Deepest; needs a
    reference PDF into `refs/` (Tate's thesis / Lang *ANT* XIII–XIV / Neukirch VII §5).
    **Seal the unit fundamental domain behind a small API (review Q2)**: one theorem
    "sum over nonzero elements of an ideal mod units = partial-zeta / Mellin expression";
    everything downstream sees only that theorem, not the domain geometry.
  - **[SP1-FE] assembly** (`FunctionalEquation.lean`): `completedDedekindZeta_one_sub` (clean FE),
    continuation + poles tied to `dedekindZeta_residue` — replaces the current stubs.
  - **[SP1-AC] analytic control** (`AnalyticControl.lean` + `HadamardProduct.lean`) — **promoted
    to an explicit deliverable (review Q1/Q4); blocks SP2 + SP3.** Leaves: finite order of `Λ_K`;
    vertical-strip growth bounds (for contour shifts); **zeros as a locally-finite multiset /
    indexed type with multiplicity** + lemmas to compare/bound/subtract zero-sums; canonical/
    Hadamard product **and its logarithmic derivative** (usable statement); contour-shift decay
    estimates; the **real-branch-of-log** convention for `log(ζ_K/ζ_k)`, `s>1`. ⚠ zero-sums carry
    a **convergence convention** — do NOT model them as absolutely summable unless proven (review Q5).
  - **[SP1-Γ] `GammaFactor.lean`**: `Γℝ^{r₁}Γℂ^{r₂}` bookkeeping → mathlib Deligne (leaf).
  - **[SP1-GRH] `GRH.lean`** — provide **both** `GRH_Λ K` (zeros of `Λ_K` on the line) and
    `GRH_{>½} K` (zero-free `Re s > ½`), plus the **equivalence lemma** (FE + Euler-product
    nonvanishing on `Re>1` + Γ-factors have no zeros). Use `GRH_{>½}` for Lemma 3, `GRH_Λ` for the
    explicit-formula zero-sum. Replaces the current single-form stub (review Q4).

### [SP2] Weil–Poitou explicit formula
- **Status**: **DONE** (2026-07-03: `weil_explicit_formula` in `ExplicitFormula/WeilAssembly.lean`; see decomposition-sp2.md)
- **Type**: epic · **Depends on**: SP1 · **Blocks**: T004 (Lemma 3)
- **Goal**: the explicit formula (eqs 1, 3): `Σ_ρ F̂(γ_ρ) = −2 Σ_{𝔭,m} (log N𝔭/N𝔭^{m/2})
  F(m log N𝔭) + 4∫F(x)cosh(x/2)dx + F(0)(log Δ_K − n_K C − n_K log 8π − r_K π/2) +
  n_K∫(F(0)−F)/(2 sinh) + r_K∫(F(0)−F)/(2 cosh)`. **Route**: Poitou (Numdam) / Lang *ANT*
  XVII / Iwaniec–Kowalski §5 — contour integral of `−Λ'_K/Λ_K`. Reuse Chebotarev Euler
  product for the prime side. **Next action**: acquire reference, then `/develop --decompose`.
- **Depends on (promoted, review Q1/Q4/Q5)**: SP1-AC (finite order, zero multiset with
  multiplicity, log-derivative, contour-shift estimates) + `[T-ADM]`. ⚠ the zero-sum
  `Σ_ρ F̂(γ_ρ)` carries a **convergence convention** (conditional, not absolute until the
  post-Lemma-3 estimates) — keep that visible in the Lean statement.

### [SP3] Stark's formula + Landau–Stark bound
- **Status**: **DONE** (2026-07-03: hypothesis-discharge suite at `F_{s,X}` (`weil_explicit_formula_auxF`) + `expTest` (`weil_explicit_formula_expTest`, `stark_identity`, `landau_stark_estimate` in `Lemma5.lean`))
- **Type**: epic · **Depends on**: SP1 · **Blocks**: T005 (Lemma 4), T012 (Thm 1)
- **Goal**: eq (19) `Σ_ρ 1/(σ−ρ) = ½log Δ_K + 1/(σ−1) + 1/σ − ½ d_{K,σ}` and Lemma 5
  `Σ_ρ (¼+γ_ρ²)^{−1} = O(log Δ_K)`. **Route**: Stark 1974 eq (9); Landau §180; mathlib
  `digamma`. **Next action**: acquire reference, then `/develop --decompose`.
- **Depends on (promoted, review Q4)**: SP1-AC — Stark's identity is the **log-derivative of
  the canonical/Hadamard product** of `Λ_K`, so it needs finite order + the product + its
  log-derivative, not just meromorphic continuation + FE.

---

## Concrete near-term tickets (actionable now — SP-independent)

### [T001] Define `bSum` (`B_K(X)`) — replace the stub
- **Status**: DONE ✓ (2026-07-01) · **File**: `MainTheorem.lean` · **Depends on**: none · **Parallel**: yes · **Type**: def
- **Outcome**: `bSum` defined via nested `∑ᶠ` over `{p : Ideal (𝓞 K) // p.IsPrime ∧ p ≠ ⊥}`
  and `m : ℕ`, guarded by `0 < m ∧ N𝔭^m < X`; finsum totality ⇒ no finiteness proof needed to
  define. Build green, axiom-clean `{propext, Classical.choice, Quot.sound}`. (`fK` now
  sorry-free too.) Finite-support / `Finset` reformulation deferred to when a proof needs it.
#### Statement
Replace `noncomputable def bSum (K) (X : ℝ) : ℝ := sorry` with Belabas–Friedman's `B_K(X)`
(p. 2): the sum over prime ideals `𝔭 ⊆ 𝓞_K` and integers `m ≥ 1` with `N𝔭^m < X` of
`(log N𝔭 / N𝔭^{m/2}) · (√X·log X / (N𝔭^{m/2}·log N𝔭^m) − 1)`, where `N𝔭 = Ideal.absNorm 𝔭`.
#### Proof sketch (design)
1. Index over `p : {p : Ideal (𝓞 K) // p.IsPrime ∧ p ≠ ⊥}` and `m : ℕ`; summand `0`
   unless `0 < m` and `(absNorm p.1 : ℝ)^m < X`. Set `q := (Ideal.absNorm p.1 : ℝ)`.
2. Summand: `(Real.log q / q ^ ((m:ℝ)/2)) * (Real.sqrt X * Real.log X / (q ^ ((m:ℝ)/2) *
   Real.log (q ^ m)) - 1)` (use `Real.rpow` for `q^{m/2}`; `log N𝔭^m = Real.log (q^m)`).
3. Finiteness: `{𝔭 : absNorm 𝔭 < X}` is finite (`Ideal.finite_setOf_absNorm_le` / the
   Chebotarev prime-ideal finiteness API); express as a `Finset.sum` or a `tsum` with
   finite support so it is well-defined and later manipulable.
#### Mathlib / project lemmas
- `Ideal.absNorm`, `Ideal.finite_setOf_absNorm_le`, `Real.rpow`, prime-ideal API; cross-check
  Chebotarev `NumberFieldEulerProduct` (`idealNormMultiplicity`, prime-power indexing) for
  a reusable index type.
#### Sources
- Belabas–Friedman, arXiv:1305.0035, p. 2 (definition of `B_K`).
#### Generality
- General number field `K`; `X : ℝ`. Real-valued.

### [T002] Basic API for `gAux` / `auxF`
- **Status**: DONE ✓ (2026-07-01) · **File**: `AuxiliaryFunction.lean` · **Depends on**: none · **Parallel**: yes · **Type**: lemma
- **Outcome**: `gAux_neg`, `auxF_neg` (evenness, `@[simp]`), `auxF_of_le` (plateau = 1),
  `auxF_zero` (`X ≥ 1 → F(0)=1`), and `measurable_auxF` (`Measurable.ite` + `fun_prop`; the
  break locus `|t|=log X` is `measurableSet_le`) — the measurability prerequisite T003 needs.
  All build green + axiom-clean `{propext, Classical.choice, Quot.sound}`.
#### Statement
`auxF_of_le` (`|t| ≤ log X → auxF s X t = 1`), `auxF_even` (`auxF s X (-t) = auxF s X t`),
`gAux_even`, `auxF_apply_zero` (`auxF s X 0 = 1` for `X ≥ 1`), and measurability/continuity
of `auxF s X` off `|t| = log X` (needed for the Fourier integral in T003).
#### Proof sketch
Unfold the `if`; `abs_neg`; standard continuity of `Complex.exp`, `Real.log`, division.
#### Mathlib lemmas
- `abs_neg`, `Complex.continuous_exp`, `Continuous.div`, `Real.continuous_log` (off 0).
#### Sources
- Belabas–Friedman eqs (6), (11)–(12).
#### Generality
- `s : ℂ`, `X t : ℝ`.

### [T003] Lemma 2 — Fourier transform of `auxF` (eq 8)
- **Status**: **DONE** (2026-07-02, commits bfeb0694…5878b2cc). `fourier_auxF` (γ≠0, eq 8
  verbatim) + `fourier_auxF_zero` (γ=0 companion, single-FTC route) in `Lemma2.lean`;
  all L2a–L2g bricks landed sorry-free + axiom-clean; supporting API:
  `integrableOn_bounded_mul_exp_div`, `tendsto_exp_div_mul_atTop`,
  `integrableOn_{exp_div,gAux_deriv,gAux_deriv2}_mul_real`, `hasDerivAt_gAux_core/deriv`
  (eq 7), `integral_Ioi_gAux_ibp₁/₂`, `tail_integral_identity`.
  (was: in progress 2026-07-03; paper re-audited verbatim: eq (2) e^{+itγ} no 2π ✓,
  eqs (6)(7)(11)(12) match `gAux`/`auxF` exactly ✓). **γ=0 faithfulness note**: the
  `sin(γT)/γ` term is 0/0 at γ=0 in Lean-total semantics while `F̂(0) = 2T + …` — state
  Lemma 2 for `γ ≠ 0` + a separate `γ = 0` companion (`F̂(0) = 2T + 2(h+1/T)/h² −
  (4/h²)∫_T^∞ f(ht+1)/t²`, the γ→0 limit). **Lean plan**: (L2a) evenness-reduction
  `∫_ℝ F e^{itγ} = 2∫_0^∞ F cos(γt)` (split Iic/Ioi + comp-neg + cexp-pairing);
  (L2b) plateau `2∫_0^T cos = 2 sin(γT)/γ` (integral_cos); (L2c) integrability of
  `g·cos, g'·sin, g''·cos` on `[T,∞)` (exp-decay, Re h > 0, `exp_neg_integrableOn_Ioi`);
  (L2d) derivative facts on `t ≥ T > 0` (`|t| = t`): `HasDerivAt g (−(h+1/t))g` and for
  `g'` (eq 7); (L2e) two improper IBPs (`integral_Ioi_deriv_mul_eq_sub`, boundary → 0);
  (L2f) the tail identity `I(γ²+h²) = −γg(T)sin(γT) + (h+1/T)g(T)cos(γT) − 2∫cos·g(ht+1)/t²`;
  (L2g) assemble with `f = g/g(T)` + the eq-10 algebra `1/γ − γ/(h²+γ²) = h²/(γ(h²+γ²))`. · **File**: `AuxiliaryFunction.lean` · **Depends on**: T002 · **Parallel**: no · **Type**: lemma
#### Statement
`fourier_auxF`: for `Re s > ½`, `X > 1`, `γ ∈ ℝ`, the Fourier transform `F̂_{s,X}(γ)`
equals the closed form of Lemma 2 (eq 8 / the `\widehat{F_{s,X}}` display, p. 6):
`2h² sin(γT)/((h²+γ²)γ) + 2(h+1/T)cos(γT)/(h²+γ²) − (4/(h²+γ²))∫_T^∞ cos(γt) f_{s,X}(t)(ht+1)/t² dt`,
`h = s − ½`, `T = log X`.
#### Proof sketch
Split `F̂ = ∫_{|t|≤T} e^{iγt}dt + ∫_{|t|>T} f_{s,X}(t)e^{iγt}dt`; the first is `2 sin(γT)/γ`;
for the second use `g'_s`, `g''_s` (eq 7) and two integrations by parts (paper eq 8). This
is the one spine leaf provable now (mathlib Fourier + `auxF`), independent of SP1/2/3.
**Review note (Q5)**: not trivial in Lean — mind the even extension, the improper `∫_T^∞`,
the complex parameter `h = s − ½`, and the denominator `h²+γ²` (typing/branch care). Best early
target above the definitions nonetheless.
**NORMALISATION WARNING (paper audit 2026-07-01, eq. (2) verbatim)**: the paper's transform is
`F̂(γ) := ∫_{−∞}^{+∞} F(t)·e^{itγ} dt` — **`e^{+itγ}`, NO `2π`**. Mathlib's `𝓕 f w =
∫ e^{−2πi·t·w} f(t) dt`. Do NOT state Lemma 2 through mathlib's `𝓕`: define the paper's
transform as a plain integral (`∫ t, auxF s X t * Complex.exp (I*t*γ)`), or relate via
`γ = −2πw` with an explicit conversion lemma filed under SP1-N. All explicit-formula terms
(`∑_ρ F̂(γ_ρ)`) use the paper convention.
#### Mathlib lemmas
- `Real.fourierIntegral`, `intervalIntegral.integral_comp`, `integral_cos`, integration-by-parts
  lemmas; `Complex.exp` derivatives.
#### Sources
- Belabas–Friedman, Lemma 2, eqs (7)–(8), pp. 5–6.
#### Generality
- `s : ℂ` with `½ < Re s`; `X : ℝ`, `1 < X`.

### [T-ADM] Admissibility structure for explicit-formula test functions
- **Status**: **DONE** (2026-07-02, commits d8e32d87 + a7eb90bc). `IsAdmissibleTestFn` in
  `ExplicitFormula/TestFunction.lean` — the paper's p.3 hypotheses verbatim (even; ∃ε>0 with
  F·e^{(1/2+ε)x} BV+integrable on [0,∞); (F(0)−F(x))/x BV; jump-average). Discharged for
  `F_{s,X}`: `isAdmissibleTestFn_auxF` in `ExplicitFormula/AuxAdmissible.lean` for
  **Re s > 1** (paper-faithful: Lemma 3 applies the formula at Re s > 1 first, then
  continues analytically), witness ε = (Re s−1)/2; `continuous_auxF` via kink-free
  max-form `auxF_eq_max`. Axiom-clean.
  (was: open · **File**: `ExplicitFormula/TestFunction.lean` · **Depends on**: T-BV · **Parallel**: yes · **Type**: def/structure
#### Statement
A named `structure` (not loose hypotheses) capturing Weil–Poitou admissibility (review Q4):
evenness; bounded variation + integrability of `x ↦ F(x)·e^{(1/2+ε)x}`; bounded variation of
`x ↦ (F(0)−F(x))/x`; the average-of-jump convention at discontinuities. Bundles the side
conditions the explicit formula (SP2) and its application (Lemma 3) quote.
#### Proof sketch (design)
Define once as `structure IsAdmissibleTestFn (F : ℝ → ℂ) : Prop` (or bundled with data);
downstream theorems take `(hF : IsAdmissibleTestFn F)` instead of copying the four conditions.
Provide a constructor from `[T-BV]` (piecewise-C¹) so `F_{s,X}` discharges it cheaply.
#### Sources
- Belabas–Friedman §5 (explicit-formula hypotheses); Poitou 1977. Expert review Q4.
#### Generality
- `F : ℝ → ℂ`; `ε > 0`. Reused verbatim across SP2 + Tier-3.

### [T-BV] Piecewise-C¹-with-integrable-derivative ⇒ bounded variation
- **Status**: **DONE** (2026-07-02, commit d8e32d87). In `ExplicitFormula/TestFunction.lean`:
  `eVariationOn_le_integral_norm_deriv` (variation ≤ ∫‖f′‖ on ord-connected sets, via
  FTC-right + `sum_integral_adjacent_intervals` + `setIntegral_mono_set`),
  `boundedVariationOn_of_deriv_integrable`, `boundedVariationOn_Ici_of_piecewise_deriv`
  (single-kink glue via `eVariationOn.union`). Mathlib has NO variation-vs-∫‖f′‖ lemma
  (only AC ⇒ BV on compact uIcc via `AbsolutelyContinuousOnInterval`) — this is new, and a
  mathlibable candidate. Axiom-clean.
  (was: open · **File**: `ExplicitFormula/TestFunction.lean` (or `Common/`) · **Depends on**: none · **Parallel**: yes · **Type**: lemma
#### Statement
A reusable lemma: a continuous function that is piecewise `C¹` with integrable derivative on
`ℝ` (finitely many break-points) is of bounded variation on every interval, with the expected
`∫|F'|` bound. Instantiated for `F_{s,X}` (break at `|t|=T`) so its admissibility (`[T-ADM]`) is
not re-proved from scratch (review Q5).
#### Proof sketch (design)
Split at the break-points; on each `C¹` piece bound the variation by `∫|F'|` (FTC-2 +
`intervalIntegral`); glue with additivity of `eVariationOn`/`BoundedVariationOn`.
#### Mathlib lemmas
- `BoundedVariationOn`, `eVariationOn`, FTC-2 (`intervalIntegral.integral_deriv_eq_sub`).
#### Sources
- Standard real analysis; motivated by Belabas–Friedman `F_{s,X}` (eqs 11–12). Review Q5.
#### Generality
- `F : ℝ → ℂ` (or `ℝ → ℝ`) piecewise `C¹`. General.

### [CLEANUP-1] `/cleanup` on `AuxiliaryFunction.lean`
- **Status**: superseded (2026-07-03) · **Depends on**: T003 · **Type**: cleanup.
  Cleanup is now the AINTLIB fleet's job **on `main` post-merge** (repo CLAUDE.md:
  producers never clean/golf on dev branches) — do not execute here.

---

## Tier-3 spine — ★ ALL DONE (2026-07-03) ★

- **[T010]** `lemma3` (eq 13) — **DONE** (2026-07-03, `lemma3_display` in `Lemma3.lean`).
- **[T011]** `lemma4` (eq 14) — **DONE** (2026-07-03, `lemma4_sigma_estimate` +
  `lemma4_explicit2` in `Lemma4.lean`; the T-vs-T′ trick landed via `arch_sum_diff_le`).
- **[T012] (milestone)** `belabas_friedman_thm1` — **DONE ★ (2026-07-03, commit d5ea59a3)**:
  `MainTheorem.lean`, sorry-free, axioms = {propext, Classical.choice, Quot.sound}.
  Endgame numerics in `Theorem1.lean` (T012-b N1–N5): `sinh_int_rec/one/two/mono`,
  `cosh_int_nonneg/le/two`, `dSigma_rat_two_eq`, `dSigma_ge` (dLow = 2γ+2log2π−3),
  `ratPrimeIdeal`/`vonMangoldtSum_rat_two_ge` (9-term W-certificate),
  `zeroSumSigma_rat_le` (the ℚ-master numeric), `log_one_add_le_quintic`,
  `beta_bound_core/half`; assembly at `σ = 1+1/√logΔ` with
  `(2σ−1)(logΔ+2/(σ−1)) = (√logΔ+2)²` and `log_three_lt_d9` closing
  `(3/2)(1+log9/4) < 2.324` (margin 5.4e-5), `6log9 < (4/3)·2.324·4.26`.
- **[T013]** `Refinements` (Thm 7, Cor 8) — **Depends on**: T012. *(Later /develop pass.)*
- **[T014]** `Residue` — bridge `|log κ_K − f_K(X)| ≤ …` to `log(h_K R_K)` via
  `dedekindZeta_residue` — **Depends on**: T012.

## Cleanup cadence (to expand as leaf tickets land)
- `[CLEANUP-1]` after T003 (AuxiliaryFunction). Per-file + pre-milestone `[CLEANUP-ALL]`
  before T012 and a final `[CLEANUP-FINAL] /cleanup-all` get inserted as each epic's leaf
  tickets are created.

## Next actions
1. `/beastmode` on **T001** (define `bSum`) and **T002/T003** (auxF API + Lemma 2) — the
   sorry-free, SP-independent near-term work.
2. `/develop --decompose` scoped to **SP1** (the foundation) — mirror mathlib/FltRegularBernoulli.
3. Acquire SP2/SP3 references (Poitou via Numdam; Stark), then their decompose passes.
4. `/blueprint` once SP1 leaf declarations exist (more decls to unformalise).
