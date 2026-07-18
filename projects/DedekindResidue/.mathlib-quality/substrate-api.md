# Substrate API map — mathlib footholds for SP1 (recon 2026-07-01)

Verified against the pin (rev `11b908e5`, v4.32.0-rc1). Paths relative to
`$MB = .lake/packages/mathlib`. This de-risks the SP1 theta-stack build: it records exactly
what to reuse and what must be built. **Bottom line:** the n-dim Gaussian Fourier transform is
*already done*; the **dual lattice** is the one real gap; n-dim Poisson must be assembled from
the multivariate torus Fourier basis.

## A. ℤ-lattices & covolume  — `$MB/Mathlib/Algebra/Module/ZLattice/{Basic,Covolume}.lean`
- No `ZLattice` **type**: a lattice is `L : Submodule ℤ E` + `[DiscreteTopology L] [IsZLattice ℝ L]`.
  `IsZLattice ℝ L` means `span ℝ (L : Set E) = ⊤`. Instance `instIsZLatticeRealSpan`:
  `span ℤ (Set.range b)` is a ZLattice for a real basis `b` — **this makes "dual = span of dual
  basis ⇒ dual is a ZLattice" free.**
- `ZLattice.covolume L (μ := volume) : ℝ`; `covolume_pos`, `covolume_ne_zero`.
- `ZLattice.covolume_eq_det (L : Submodule ℤ (ι → ℝ)) (b : Basis ι ℤ L) :
   covolume L = |(Matrix.of ((↑) ∘ b)).det|` — the det-of-basis-matrix form (key for the reciprocal).
- `covolume_eq_measure_fundamentalDomain`, `covolume_comap` (transport under `ContinuousLinearEquiv`;
  no generic `covolume (map f L) = |det f|·covolume L`).
- Fundamental domain namespace is `ZSpan` (capital S): `ZSpan.fundamentalDomain (b : Basis ι K E)`,
  `ZSpan.isAddFundamentalDomain`, `ZLattice.isAddFundamentalDomain`.
- Basis bridge: `Basis.ofZLatticeBasis (K) (L) (b : Basis ι ℤ L) : Basis ι K E`, with
  `ofZLatticeBasis_span : span ℤ (Set.range (b.ofZLatticeBasis K)) = L`. Generic ℤ-basis via
  `Module.Free.chooseBasis ℤ L` / `IsZLattice.basis`.

## B. Dual lattice — THE GAP  — `$MB/Mathlib/LinearAlgebra/BilinearForm/DualLattice.lean`
- `LinearMap.BilinForm.dualSubmodule (B : BilinForm S M) (N : Submodule R M) : Submodule R M`
  `= { x | ∀ y ∈ N, B x y ∈ (1 : Submodule R S) }` (setup `[CommRing R] [Field S] [Algebra R S]
  [Module R M] [Module S M] [IsScalarTower R S M]`; here `R=ℤ, S=ℝ, M=V`).
- `mem_dualSubmodule : x ∈ B.dualSubmodule N ↔ ∀ y ∈ N, B x y ∈ (1 : Submodule R S)`.
  `(1 : Submodule ℤ ℝ)` = the integers inside ℝ (`Submodule.mem_one`: `∈ 1 ↔ ∃ z:ℤ, z = ·`).
- `dualSubmodule_span_of_basis (hB : B.Nondegenerate) (b : Basis ι S M) :
   B.dualSubmodule (span R (range b)) = span R (range (B.dualBasis hB b))` — **the lever**:
  dual of a lattice = span of the dual basis ⇒ ZLattice via `instIsZLatticeRealSpan`.
- Double-dual identities `dualSubmodule_dualSubmodule_of_basis` (symmetric nondeg. `B`).
- **Missing (must build):** (i) `DiscreteTopology`/`IsZLattice` for the dual (free via the span
  lever); (ii) covolume reciprocal `covolume L♯ · covolume L = 1` (via `dualSubmodule_span_of_basis`
  + `covolume_eq_det` + the dual-basis matrix `= (Bᵀ)⁻¹`, so `det = (det basis)⁻¹`).
- **Worked example to mirror:** the trace-form **codifferent** is a `dualSubmodule` in
  `$MB/Mathlib/RingTheory/DedekindDomain/Different.lean` and
  `$MB/Mathlib/NumberTheory/NumberField/Discriminant/Different.lean` (ties it to `discr`). This
  is the number-field dual lattice for the Hecke step (AGE) — reuse, don't reinvent.
- Inner product as a bilinear form: `bilinFormOfRealInner` is **deprecated → use `innerₗ`**
  (`$MB/Mathlib/Analysis/InnerProductSpace/Basic.lean`); `sesqFormOfInner → innerₛₗ`.

## C. Poisson summation — `$MB/Mathlib/Analysis/Fourier/PoissonSummation.lean`
- **Only 1-D**: `Real.tsum_eq_tsum_fourier {f : C(ℝ,ℂ)} (h_norm) (h_sum) (x) :
   ∑' n:ℤ, f (x+n) = ∑' n:ℤ, 𝓕 f n * fourier n x`; `…_of_rpow_decay`; `SchwartzMap.tsum_eq_tsum_fourier`.
  (`…_fourierIntegral` names are deprecated aliases.)
- **No n-dim / lattice Poisson exists.** Build it (see E).

## D. Gaussian Fourier — n-dim ALREADY EXISTS (windfall)
`$MB/Mathlib/Analysis/SpecialFunctions/Gaussian/FourierTransform.lean`, `namespace GaussianFourier`:
- `fourier_gaussian_innerProductSpace (hb : 0 < b.re) (w : V) :
   𝓕 (fun v:V ↦ cexp (-b*‖v‖^2)) w = (π/b)^(finrank ℝ V/2 : ℂ) * cexp (-π^2*‖w‖^2/b)`
  on any `[NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]`. Plus
  `fourier_gaussian_innerProductSpace'` (linear/inner term), `integral_cexp_neg_mul_sq_norm`,
  integrability lemmas. **The analytic core of the theta transformation is done.**
- 1-D: `fourierIntegral_gaussian`, `fourier_gaussian_pi(')`.
- Poisson-for-Gaussian building blocks: `$MB/…/Gaussian/PoissonSummation.lean`
  `Complex.tsum_exp_neg_mul_int_sq`, `Real.tsum_exp_neg_mul_int_sq`; Jacobi theta in
  `$MB/Mathlib/NumberTheory/ModularForms/JacobiTheta/` (1-D lattice sums).

## E. Multivariate torus Fourier — `$MB/Mathlib/Analysis/Fourier/AddCircleMulti.lean`
`namespace UnitAddTorus`, `UnitAddTorus d := d → UnitAddCircle` (`[Fintype d]`):
- `mFourier (n : d→ℤ) : C(UnitAddTorus d, ℂ)`; `mFourierCoeff f n := ∫ t, mFourier (-n) t • f t`.
- `mFourierBasis : HilbertBasis (d→ℤ) ℂ L²(UnitAddTorus d)` (Parseval; `orthonormal_mFourier`).
- **The Poisson lever:** `hasSum_mFourier_series_apply_of_summable
   (h : Summable (mFourierCoeff f)) (x) : HasSum (fun i ↦ mFourierCoeff f i • mFourier i x) (f x)`
  for continuous `f`. → build n-dim Poisson by periodizing `f : (Fin n→ℝ)→ℂ` to the torus and
  applying this, mirroring 1-D `PoissonSummation.lean`.

## F. Number field embedding, invariants, zeta
- `NumberField.mixedEmbedding : K →+* mixedSpace K`; `mixedEmbedding.integerLattice K`,
  `idealLattice K I` — both carry `IsZLattice ℝ`; `latticeBasis`; euclidean repackaging
  `euclidean.integerLattice`. (`$MB/…/CanonicalEmbedding/Basic.lean`.)
- **`mixedEmbedding.covolume_integerLattice : covolume (integerLattice K) = (2⁻¹)^{r₂}·√|discr K|`**,
  `covolume_idealLattice = absNorm I · (2⁻¹)^{r₂}·√|discr K|`
  (`$MB/…/NumberField/Discriminant/Basic.lean`). ← the √discr covolume, done.
- `mixedEmbedding.fundamentalCone : Set (mixedSpace K)` (lowercase; unit action) +
  `measurableSet_fundamentalCone`, `exists_unit_smul_mem`, `unit_smul_mem_iff_mem_torsion`
  (`$MB/…/CanonicalEmbedding/FundamentalCone.lean`). This is the sealed unit-domain the review wants.
- `NumberField.dedekindZeta s := LSeries (fun n ↦ Nat.card {I // absNorm I = n}) s` (L-series only:
  no continuation / FE / completion in mathlib); `dedekindZeta_residue`,
  `tendsto_sub_one_mul_dedekindZeta_nhdsGT`. `Ideal.absNorm`, `classNumber`, `ClassGroup`.
- `Complex.Gammaℝ s = π^(-s/2)·Γ(s/2)`, `Complex.Gammaℂ s = 2·(2π)^(-s)·Γ(s)`
  (`$MB/…/Gamma/Deligne.lean`); `completedRiemannZeta`, `completedRiemannZeta_one_sub`,
  `completedRiemannZeta_residue_one` (`$MB/…/LSeries/RiemannZeta.lean`).
- **No `completedDedekindZeta` anywhere** except our sorried stub — SP1 is genuinely new.

## Immediate build order (SP1-AGP)
1. **P.1 dual lattice** (`CompletedZeta/DualLattice.lean`): define via `innerₗ`+`dualSubmodule`;
   ZLattice instance free via `dualSubmodule_span_of_basis`+`instIsZLatticeRealSpan`; covolume
   reciprocal via `covolume_eq_det` + dual-basis determinant.
2. **P.2 n-dim Poisson (Gaussian class)**: periodize + `hasSum_mFourier_series_apply_of_summable`.
3. **P.3 transport** to a general lattice + covolume factor.
Then **AGΘ** lattice Gaussian theta = P.2/P.3 ⊕ `fourier_gaussian_innerProductSpace` (done).
