# HANDOVER — DedekindResidue (Belabas–Friedman residue formalisation)

*Written 2026-07-01 so that any Claude account (or human) can take over mid-stream. Read this
first, then `plan.md` → `tickets.md` → `substrate-api.md` in this directory. Keep this file
updated at every commit checkpoint.*

## 0. TL;DR for a fresh session

```
cd /Users/mcu22seu/Documents/GitHub/aintlib-dedekind    # worktree, branch dev/dedekind-residue
lake exe cache get                                       # only if mathlib oleans missing
lake build DedekindResidue.CompletedZeta.PoissonSummation
```

**UPDATE 2026-07-02 (later — AGE nearly assembled).** AGE-0 ✓, AGE-1 ✓, **AGE-2 ✓**
(`dualZLattice_idealZLattice`: the dual of an ideal lattice is the `diagScale dualityWeights`
(conj∘double) twist of the trace-dual ideal lattice; pairing dictionary
`inner_diagScale_embeddingCoords` = `Tr_{K/ℚ}(ba)`; rigidity `eq_of_le_of_covolume_eq` +
`covolume_zlattice_comap` in DualLattice.lean). **AGE-3 nearly done** (`HeckeTheta.lean`):
`heckeTheta I c` (multivariable, per-place weights), `heckeTheta_unit_mul` (unit symmetry),
**`heckeTheta_inversion`** (`Θ_I(c) = covol⁻¹(∏c)^{-1/2}Θ_{I^∨}(c^∨)`, `c^∨ = (c⁻¹; 4c⁻¹)`),
`heckeWeights t u = t^{1/n}exp(2·fullLog(u)/mult)` (equivariance + periodicity + norm-ray
`∏c_w^{mult}=t`), and **`heckeG I t`** (unit-box-averaged theta). REMAINING: g-inversion
(pointwise `heckeTheta_inversion` under the box integral + `u ↦ -u` change of variables;
watch the `4^{r₂}` place-type factor: `dualPlaceWeights (heckeWeights t u) =
(1 real; 4 complex)·heckeWeights t⁻¹ (-u)` pointwise — verify and absorb into constants),
integrability estimates for `heckeG`, then **AGE-4**: `Λ := completedZetaPrefactor-normalised
∑_{classes} N(J)^s-weighted mellin(heckeG_J − const)` split at 1, agreement on `Re s > 1` via
`FundamentalCone.idealSetEquivNorm` counting + `prod_heckeWeights_pow_mult` (the per-point
Mellin gives `N(𝔞)^{-s}·Γ-factors`), `s(s-1)Λ` entire ⇒ `∃ Λ, IsCompletedDedekindZeta K Λ`
(GRH non-vacuity) + FE from the g-inversion.

**UPDATE 2026-07-02 (earlier — AGE-4 chain progressing).** AGE-0 ✓ (multivariable theta), AGE-1 ✓
(`IdealLattice.lean`: `euclideanIdealLattice`, `idealZLattice`, `covolume_idealZLattice`,
`idealTheta` + `idealTheta_transform`). Remaining chain to GRH non-vacuity is in the SP1-AGE
ticket (AGE-2/3/4). **AGE-2 WARNING (archimedean-constant trap, review Q5)**: with our PLAIN
L² metric on `euclidean.mixedSpace`, `⟪σx, σy⟫ = ∑_real x_v y_v + ∑_complex Re(x_w·conj(y_w))`
which is NOT the trace form `Tr_{K/ℚ}(xy)` at complex places (factor 2 + conjugation) — so
`dualZLattice (idealZLattice K I)` is a *scaled/conjugated* codifferent lattice, not verbatim
`(I·𝔡)⁻¹`. Derive the exact dictionary from the pairing computation BEFORE stating AGE-2;
cross-check against `Different.lean`'s `FractionalIdeal.dual` (trace-form convention) and
record the conversion in `Normalisation.lean`.

**UPDATE 2026-07-01 (GRH properly stated — user directive executed).** The project now has
**exactly one `sorry`: `belabas_friedman_thm1` itself** (the target theorem). The sorried
`completedDedekindZeta` definition is GONE, replaced by the characterisation architecture in
`FunctionalEquation.lean`: `completedZetaPrefactor` (genuine), `IsCompletedDedekindZeta K Λ`
(agrees with `prefactor·ζ_K` on `Re s > 1` where the L-series is honest, and `s(s-1)Λ`
entire) with the PROVEN uniqueness `IsCompletedDedekindZeta.eqOn` (identity theorem; values
at the poles `0,1` are junk by nature and excluded). `GRH.lean` now states
`GeneralizedRiemannHypothesis K` in the paper's verbatim form: every such `Λ` is nonvanishing
on `Re s > 1/2` off the pole `s = 1`. Genuine, junk-free, no placeholders. **Non-vacuity**
(∃ Λ, IsCompletedDedekindZeta K Λ) is Hecke's theorem = the AGE-4 target: the constructed
theta-Mellin `Λ` will inhabit the predicate and the FE `Λ(1-s)=Λ(s)` is proven of it.
Rule going forward (user): NO sorried definitions, no `True`-placeholders, ever.

**UPDATE 2026-07-01 (earlier): SP1-N DONE + AGE STARTED, AGE-0 DONE.** `Normalisation.lean`
(gammaFactor, paper-Fourier bridge `paperFourierIntegral_eq_fourierIntegral`) and the
**multivariable theta transformation `weightedThetaLattice_transform`** (AGE-0, the engine for
nontrivial unit rank) are proven, axiom-clean, pushed. The AGE decomposition (AGE-0..4, with
mathlib windfalls `FundamentalCone.idealSet`/`idealSetEquivNorm`, `euclidean.mixedSpace`,
`covolume_idealLattice`, `mellin`) is in the SP1-AGE ticket. Frontier: **AGE-1** — euclidean
ideal lattices (`ZLattice.comap` of `mixedEmbedding.idealLattice` along `toMixed`, then
transport along `(euclidean.stdOrthonormalBasis K).repr` to `EuclideanSpace ℝ (index K)`).
Goal: genuine `completedDedekindZeta` (AGE-4) so GRH is fully stated — the user's priority.

**UPDATE 2026-07-01 (earlier): SP1-AGΘ DONE.** `ThetaLattice.lean`
(sorry-free, axiom-clean) proves **`thetaLattice_transform`:
`Θ_L(t) = covol(L)⁻¹·t^{-n/2}·Θ_{L♯}(1/t)`** — the full lattice/Poisson/theta layer
(reviewer milestone (a)) is complete. Frontier: **SP1-AGE** — Hecke partial theta over ideal
classes (ideal lattices via `mixedEmbedding.idealLattice`/`latticeBasis`, codifferent =
`dualSubmodule` of the trace form for the dual side, unit fundamental domain sealed behind a
small API per review Q2). Also do **SP1-N** (normalisation file) early — the paper's Fourier
convention (`e^{+itγ}`, no 2π) vs mathlib's `𝓕` is recorded in the T003 ticket.

**UPDATE 2026-07-01 (earlier): P.3 DONE — SP1-AGP COMPLETE.** `PoissonLattice.lean`
(sorry-free, axiom-clean) has `tsum_eq_tsum_fourier_zlattice` (Poisson over an arbitrary
ℤ-lattice, covolume factor + dual lattice) and `fourier_comp_linearEquiv` (GL change of
variables for 𝓕). Frontier: **SP1-AGΘ** — Gaussian theta + transformation law; leaf plan in
the SP1-AGP ticket ("Next epic: SP1-AGΘ"). Everything below about P.2 is history.

**UPDATE 2026-07-01 (earlier): P.2 IS DONE.** `tsum_eq_tsum_fourier_zpoint` (n-dim Poisson over
`ℤ^ι`) is fully proven, sorry-free, axiom-clean — `PoissonSummation.lean` builds with zero
warnings. The §4 leaf plan below was executed exactly as written (all of e1–e6 + f landed).
The live frontier is now **P.3 (transport to a general lattice)** then **AGΘ (Gaussian theta +
transformation law)** — see the SP1-AGP ticket in `tickets.md` for the P.3 sketch: pull the
`ℤ^ι` formula back along the lattice-basis linear equiv (`Module.Basis.ofZLatticeBasis` +
`LinearEquiv` change of variables in `𝓕`, covolume factor via
`ZLattice.covolume_eq_det_mul_measureReal`), dual side via `dualZLattice` +
`covolume_dualZLattice_mul` (P.1, done); then instantiate at the Gaussian
(`fourier_gaussian_innerProductSpace` is already in mathlib;
`summable_gaussian_zlattice` discharges the convergence hypotheses).
Work in `/beastmode` style; plan any new gaps in `/develop` style (ticket per leaf, verbatim
source justification, verified mathlib lemma names).

## 1. What the project is

Formalise **Belabas–Friedman, "Computing the residue of the Dedekind zeta function"
(arXiv:1305.0035), Theorem 1** in Lean 4 / mathlib, inside the AINTLIB monorepo:

> Under GRH, `|log κ_K − f_K(X)| ≤ B(X, d_K, disc K)` (explicit bound), where
> `κ_K = Res_{s=1} ζ_K` (mathlib: `NumberField.dedekindZeta_residue K`) and `f_K(X)` is the
> prime-power sum built from the test function `F_{s,X}` (our `auxF` / `bSum` / `fK`).

**Binding constraints (user-set, non-negotiable):**
- **GRH is the SOLE hypothesis** — a `Prop` argument threaded through statements, **never an
  `axiom`**. Everything else genuinely proven.
- **General number fields** (not abelian-only).
- **Axiom bar**: every public declaration must have `#print axioms` ⊆
  `{propext, Classical.choice, Quot.sound}`.
- **No empty structures / junk witnesses / vacuous instances** — no placeholder constructions
  that make statements trivially true. Definitions must be the genuine mathematical objects.
  (mathlib-standard junk values inside total functions, e.g. `tsum = 0` when not summable, are
  fine — theorems must carry the real summability/integrability hypotheses.)
- **Faithful to the literature**: proofs mirror the paper / standard references; don't invent
  decompositions (quote-or-delete discipline from `/develop`). **Standing instruction
  (user, 2026-07-01): consult the references REGULARLY** — re-read the source before/after
  every statement-level definition; audit for drift, wrong statements, junk hypotheses.
  The paper is NOT on disk (`refs/DedekindResidue/` doesn't exist) — fetch arXiv:1305.0035
  via the alphaXiv MCP (`answer_pdf_queries` on `https://arxiv.org/pdf/1305.0035`).

**Literature audit 2026-07-01 (full paper text fetched and cross-checked):**
- `gAux` ✓ = eq. (6); `auxF` ✓ = eqs. (11)–(12); Theorem-1 statement ✓ verbatim constants
  (2.324, 3.88, 4.26, `(1+2/√log Δ)²`, `X ≥ 69`, `n > 1`, GRH(ζ_K) ∧ RH(ζ_ℚ)).
- **DRIFT CAUGHT AND FIXED**: the paper's `B_K(X)` is the *relative* sum `∑^{K−ℚ}` ("the sum
  for k is subtracted from the corresponding sum for K", p. 2) — our `bSum` was the K-sum
  only. Fixed by adding `bSumRel K X := bSum K X - bSum ℚ X` and redefining `fK` over it.
- **CONVENTION TRAP RECORDED** (T003 ticket): paper's Fourier transform (eq. 2) is
  `∫ F(t)e^{+itγ}dt` — no `2π`, opposite sign vs mathlib's `𝓕`. Lemma 2 must be stated in
  the paper's convention (plain integral), with any 𝓕-bridge filed under SP1-N.
- AGΘ target cross-checked: `Θ_L(t) = covol(L)⁻¹ t^{−n/2} Θ_{L♯}(1/t)` (standard lattice
  theta inversion, Neukirch ANT VII §3 shape) is forced by our proven Poisson +
  mathlib's `fourier_gaussian_innerProductSpace` at `b = πt`; self-consistency: applying it
  twice returns `Θ_L` via `covolume_dualZLattice_mul` (P.1).

**Confirmed route for the ζ_K functional equation** (expert review, 2026-07-01, reply in
`expert-review/2026-07-01/`): the classical **Hecke theta stack** —
(P) n-dim Poisson (Gaussian class first) → (Θ) lattice Gaussian theta + transformation law →
(H) Hecke partial theta over ideal classes, unit domain sealed behind a small API →
(FE) completed `Λ_K` + functional equation, Tate-normalisation discipline for constants.
**NOT** Tate adelic. Abelian case only as a validation harness, never as substrate.
mathlib has **no** completed Dedekind zeta / FE (checked 2026-07-01: `NumberTheory/NumberField/
DedekindZeta.lean` is L-series + residue only) — SP1 is genuinely new.

## 2. Where everything lives

- **Worktree**: `/Users/mcu22seu/Documents/GitHub/aintlib-dedekind`, branch
  **`dev/dedekind-residue`**, sharing `.git` with the main checkout
  `/Users/mcu22seu/Documents/GitHub/AINTLIB` (which stays on `main`). Remote:
  `https://github.com/CBirkbeck/AINTLIB.git`. From another machine: clone + checkout the branch.
- **Project**: `projects/DedekindResidue/` — library `DedekindResidue`, Lean **module system**
  (`module` header, `public import`, `@[expose] public section`), no copyright headers by
  AINTLIB convention.
- **Pin**: mathlib rev `11b908e5cdd9`, toolchain `v4.32.0-rc1` (moves with the central daily
  bump on `main`; rebase only at stable points, never mid-proof).
- **Process artifacts** (this directory, dev-branch only, never merged to `main`):
  `plan.md` (strategy + sub-epics), `tickets.md` (**the live board** — statuses are kept
  current), `substrate-api.md` (verified mathlib foothold map, sections A–F),
  `decomposition.md` (decompose pass), `expert-review/2026-07-01/{brief,reply,state}.md`,
  `beastmode_active` (session sentinel — **do not commit**).
- **Paper**: `refs/DedekindResidue/` via the gitignored `refs` symlink (local-only, never
  committed). `REVIEW_BRIEF.md` in the project root is the self-contained math briefing.
- **Verify recipe** (no lean MCP on this setup): build the fully-qualified module
  (`lake build DedekindResidue.CompletedZeta.<Mod>`), then axiom-check via a scratch file:
  `import DedekindResidue...; #print axioms <FQN>` run with `lake env lean <file>`.
  Never put `2>/dev/null` next to `lake`/`lean` (repo guardrail blocks it; use `2>&1`).

## 3. State of the code (2026-07-01, all committed on `dev/dedekind-residue`)

| File | Status |
|---|---|
| `Basic.lean` | residue/`dedekindZeta` re-exports + conventions. Sorry-free. |
| `AuxiliaryFunction.lean` | `gAux`, `auxF` + evenness/plateau/measurability API (**T002 done**, axiom-clean). |
| `MainTheorem.lean` | `bSum` (**T001 done**), `fK` sorry-free; `belabas_friedman_thm1` = the single target `sorry`. |
| `CompletedZeta/DualLattice.lean` | **P.1 COMPLETE, axiom-clean**: `dualZLattice`, `mem_dualZLattice`, `innerₗ_nondegenerate`, `dualZLattice_eq_span`, `DiscreteTopology`/`IsZLattice` instances, `volumeReal_fundamentalDomain_orthonormal`, **`covolume_dualZLattice_mul`** (`covol L♯ · covol L = 1`). |
| `CompletedZeta/PoissonSummation.lean` | **P.2 IN PROGRESS**. Done + axiom-clean: `zpoint`, `zpoint_add`, `summable_gaussian_zlattice`, `mFourier_neg_coe`, `periodization` + `periodization_add_zpoint`, `fourierIntegral_zpoint_eq` (the `𝓕` bridge). Remaining: **`tsum_eq_tsum_fourier_zpoint` (`sorry` ~line 155)** — plan in §4. |
| `CompletedZeta/FunctionalEquation.lean` | `completedDedekindZeta` + FE statements, both `sorry` (SP1-FE — blocked on AGP/AGΘ/AGE). |
| `CompletedZeta/GRH.lean` | GRH predicates (dual form `GRH_Λ` / `GRH_{>1/2}` per review Q4). Definitions only. |

Ticket board: SP1 sub-epics `N / AGP / AGΘ / AGE / FE / AC / Γ / GRH` (+`T-ADM`, `T-BV`);
current epic **SP1-AGP** (P.1 ✓, P.2 live, P.3 transport pending). Then AGΘ (theta = P.2/P.3 ⊕
`fourier_gaussian_innerProductSpace`, which mathlib already has), then AGE (Hecke; reuse the
codifferent-as-`dualSubmodule` from `RingTheory/DedekindDomain/Different.lean` — see
`substrate-api.md` §B), then FE/AC/GRH, then SP2 (zeros/Hadamard), SP3 (explicit formula ⇒ Thm 1).

## 4. Live frontier: `tsum_eq_tsum_fourier_zpoint` — verified leaf plan

Goal (statement already in the file, mirrors mathlib's 1-D `Real.tsum_eq_tsum_fourier`):
for continuous `g : C(EuclideanSpace ℝ ι, ℂ)` with `h_norm` (per-compact summability of
translate norms) and `h_sum` (summability of `𝓕g` at lattice points),
`∑'_{n:ι→ℤ} g (zpoint n) = ∑'_m 𝓕 g (zpoint m)`.

Engine: torus Fourier series (`UnitAddTorus`, mathlib `Analysis/Fourier/AddCircleMulti.lean`).
All footholds below **verified against the pin on 2026-07-01** (exact signatures checked):

- **(c) Periodization as a `C(·,·)`-tsum.** `P := ∑' n : ι → ℤ, g.comp (ContinuousMap.addRight
  (zpoint n))` in `C(EuclideanSpace ℝ ι, ℂ)`. Summable from `h_norm` via
  `ContinuousMap.summable_of_locally_summable_norm` (needs `LocallyCompactSpace` domain — OK,
  finite-dim). Pointwise `P x = periodization g x` via `ContinuousMap.tsum_apply`.
- **(d) Torus lift.** `π : (ι → ℝ) → UnitAddTorus ι := fun x i => ↑(x i)` is an open quotient
  map: `IsOpenQuotientMap.piMap (fun _ => QuotientAddGroup.isOpenQuotientMap_mk)`. Define
  `G : C(UnitAddTorus ι, ℂ)` on points by `q ↦ P (toLp (fun i => (AddCircle.equivIoc 1 0 (q i)
  : ℝ)))` (genuine Ioc-representatives — NOT a junk section). Descent identity `G (π x) = P
  (toLp x)` from the **proven** kernel/well-definedness argument (scratch compiled clean
  2026-07-01, paste-ready):

  ```lean
  -- q x = q y ⟹ x − y ∈ ℤ^ι, hence periodization agrees (uses periodization_add_zpoint)
  have hi : ∀ i, ∃ n : ℤ, x i - y i = n := fun i => by
    have h2 := congrFun h i
    rw [QuotientAddGroup.eq, AddSubgroup.mem_zmultiples_iff] at h2
    obtain ⟨n, hn⟩ := h2
    exact ⟨-n, by simp only [zsmul_eq_mul, mul_one] at hn; push_cast; linarith⟩
  choose k hk using hi
  have hxy : x = y + (fun i => (k i : ℝ)) := funext fun i => by
    have := hk i; simp only [Pi.add_apply]; linarith
  have hadd : (WithLp.equiv 2 (ι→ℝ)).symm (y + fun i => (k i:ℝ))
      = (WithLp.equiv 2 (ι→ℝ)).symm y + zpoint k := by
    ext i
    simp only [zpoint, PiLp.add_apply, Pi.add_apply, WithLp.equiv_symm_apply, WithLp.ofLp_toLp]
  rw [hxy, hadd, periodization_add_zpoint]
  ```

  Continuity of `G`: `G ∘ π = P ∘ toLp` is continuous; conclude via
  `(IsOpenQuotientMap...).isQuotientMap.continuous_iff`.
- **(e) THE key lemma — `mFourierCoeff_periodization`**: `mFourierCoeff ⇑G m = 𝓕 ⇑g (zpoint m)`
  (n-dim analogue of mathlib's `Real.fourierCoeff_tsum_comp_add`; mirror that proof's calc
  chain — read it at `Mathlib/Analysis/Fourier/PoissonSummation.lean:51`). Steps:
  1. `UnitAddTorus.mFourierCoeff_eq_integral` (with `a := fun _ => 0`) → integral over the
     Ioc-box `{x | ∀ i, x i ∈ Ioc 0 1}`.
  2. Insert descent identity; swap `∑'`/`∫` on the box (`h_norm` at the compact closed box;
     1-D used `intervalIntegral.tsum_intervalIntegral_eq_of_summable_norm` — n-dim: dominated
     convergence / `integral_tsum` with the norm bound).
  3. Character shift-invariance: `mFourier (-m) (π (x + zpoint n)) = mFourier (-m) (π x)`
     (each coordinate shifts by an integer; via `mFourier_neg_coe` or `AddCircle.coe_add_int`).
  4. Reassemble `∑'_n ∫_box (translate n) = ∫_{ι→ℝ}` via
     `ZSpan.isAddFundamentalDomain (Pi.basisFun ℝ ι) volume` +
     `IsAddFundamentalDomain.integral_eq_tsum'` (verified sig: needs `Integrable f`; yields
     `∫ f = ∑' g, ∫_s f (-g +ᵥ x)`). **Watch**: ZSpan fundamental domain is the **Ico**-box,
     torus side is the **Ioc**-box — reconcile a.e. (coordinate hyperplanes are null;
     `Measure.pi`-null boundary). Integrability of the full integrand from `h_norm` summed
     (as in 1-D `integrable_of_summable_norm_Icc` — may need an n-dim analogue lemma).
  5. Finish with `fourierIntegral_zpoint_eq` (already proven in-file).
- **(f) Assembly.** `UnitAddTorus.hasSum_mFourier_series_apply_of_summable` (needs
  `Summable (mFourierCoeff ⇑G)` ⟸ (e) + `h_sum`) evaluated at `x = 0`; `mFourier m 0 = 1`
  (`fourier_eval_zero` productised); LHS `G 0 = P 0 = periodization g 0 = ∑' n, g (zpoint n)`
  (needs `zpoint`-of-`0` + `zero_add`). Conclude `tsum_eq` from `HasSum`.

After (f): **P.3** (transport `ℤ^ι → general L` by the lattice-basis linear equiv, covolume
factor via `ZLattice.covolume`; see ticket) — then **AGΘ** (theta transformation:
`fourier_gaussian_innerProductSpace` is already in mathlib, so Θ = Poisson + that lemma +
`covolume_dualZLattice_mul`).

## 5. Session-earned gotchas (will bite again)

- **Module system**: bare `Basis` unknown → `Module.Basis` (same for `Module.Basis.addHaar_self`,
  `.toMatrix_apply`, `.det_apply`).
- **Inner-product notation**: `open scoped RealInnerProductSpace` exports `⟪x, y⟫` (NO `_ℝ`
  suffix — `⟪·,·⟫_ℝ` is a mathlib-file-local notation, not importable).
- **`omit [inst] in` goes BEFORE the docstring**, else "unexpected token 'omit'".
- `ZLattice.covolume_eq_det_mul_measureReal (L) (μ := autoParam) (b) (b₀)`: `L` explicit, `μ`
  autoParam. In `rw`, pass named `(μ := volume) (b := …) (b₀ := …)`; after rewriting a carrier
  equality (e.g. `dualZLattice_eq_span`), re-fold `set`-variables with `rw [← hc, ← hcstar]`
  before the covolume rewrite pattern can match.
- **EuclideanSpace coordinates**: `ext i; simp only [zpoint, PiLp.add_apply, Pi.add_apply,
  WithLp.equiv_symm_apply, WithLp.ofLp_toLp]` is the working idiom.
- **Torus kernel**: `QuotientAddGroup.eq` + `AddSubgroup.mem_zmultiples_iff` (NOT
  `AddCircle.coe_eq_coe_iff_of_mem_Ioc`, which demands Ioc membership).
- `fourier_eq'` is namespaced: **`Real.fourier_eq'`**.
- After `integral_congr_ae` the integrand is a beta-redex — `dsimp only` before `rw` can match.
- `ring` cannot rewrite inside `cexp` — `congr 1` down to the exponent first. Sum-order
  mismatches (`∑ xᵢmᵢ` vs `∑ mᵢxᵢ`): `Finset.sum_congr rfl (fun i _ => mul_comm _ _)`.
- `Metric.finite_isBounded_inter_isClosed (discrete) (bounded) (closed) : (K ∩ s).Finite` —
  bounded set FIRST in the intersection.
- 1-D Poisson template lives at `Mathlib/Analysis/Fourier/PoissonSummation.lean:51` — mirror it.

## 6. Working conventions

- `/develop` to plan (every new leaf gets: statement, sketch, verified mathlib lemma names,
  source citation), `/beastmode` to execute (sentinel `beastmode_active`; spawn sub-tickets for
  gaps; never stop on "hard").
- Commit per green increment on `dev/dedekind-residue`; commit message style is in `git log`.
  Trailer: `Co-Authored-By: Claude <model> <noreply@anthropic.com>`.
- Producers don't clean/golf/restyle (fleet does that on `main` post-merge). Leave the
  ticket-board statuses current — the next session resumes from `tickets.md` + this file.

## 2026-07-02 — AGE-3 COMPLETE (`heckeG_inversion` proven); AGE-4 route derived, constants verified

**State**: whole project builds green; single `sorry` = `belabas_friedman_thm1`; all else
axiom-clean. Branch pushed through the `heckeG_inversion` + ticket commits.

**Landed today** (all in `CompletedZeta/HeckeTheta.lean`):
- `prod_placeWeights` / `prod_placeWeights_heckeWeights` (coordinate product = t).
- `fullLog_restrict` (fullLog onto the trace-zero hyperplane), `dualShift`,
  `fullLog_dualShift`, `heckeWeights_mul_left`/`_add_right`, `ite_mul_heckeWeights`,
  `dualPlaceWeights_heckeWeights_eq` — `c(t,u)^∨ = c(4^{2r₂}t⁻¹, -u+dualShift)`.
- `setIntegral_fundamentalDomain_comp_neg_add` — ∫ over a ZSpan box of a lattice-periodic
  f is invariant under `u ↦ -u+s` (preimage FD via `IsAddFundamentalDomain.preimage_of_equiv`,
  then `setIntegral_eq`; needed `VAddInvariantMeasure` transported from `.toAddSubgroup`
  via `inferInstanceAs`, and `Submodule.vadd_def`).
- **`heckeG_inversion : g_I(t) = covol(L_I)⁻¹·(√t)⁻¹·g_{I^∨}(4^{2r₂}·t⁻¹)`** — the
  Mellin-ready inversion.

**AGE-4 route (fully derived, see SP1-AGE ticket for detail)**: normalise
`Ĝ_C(x) := heckeG I (N(I)⁻²·β·x)`, `β := 4^{r₂}/|Δ|` — class-invariant via the new target
`heckeG_smul : heckeG (x•I) t = heckeG I (|Nx|²t)`; then `Ĝ_C(1/x) = √x·Ĝ_{C^∨}(x)` with
coefficient EXACTLY 1 (verified: covol_I⁻¹·N(I)·β^{-1/2} = 1). Sum over the class group ⇒
`f(1/x) = √x f(x)` ⇒ mathlib `WeakFEPair f f (1/2) 1` (AbstractFuncEq, the
completedRiemannZeta machinery) gives Λ₀ entire + poles ⇒ `s(s−1)Λ` entire. Agreement on
Re>1 via `P.hasMellin` + box-unfolding + per-place Gamma integrals + `idealSetEquivNorm`
counting; s-dependent constants absorbed by a `C₁·C₂^s` adjust (harmless for both
`IsCompletedDedekindZeta` conditions). **Next bricks in order**: (1a) translation-only FD
invariance (apply the neg lemma twice); (1b) `xShift`+`fullLog_xShift` (mirror dualShift,
zero-sum via `InfinitePlace.prod_eq_abs_norm`); (1c) `sq_mul_heckeWeights` (mirror
`ite_mul_heckeWeights`); (1d) `heckeTheta_smul` (generalise `unitMulLatticeEquiv` to
`mulCoords x`, `x ≠ 0`); then `heckeG_smul`, `Ĝ`, the FE-pair, integrability, decay,
Mellin agreement.

## 2026-07-03 — heckeFEPair ASSEMBLED (WeakFEPair complete); Mellin agreement is the last gap

**State**: green, single sorry = `belabas_friedman_thm1`, all axiom-clean, pushed through
`a50e5f6d`. New files: `CompletedZeta/ClassTheta.lean` (normalised class theta Ĝ_C, the
coefficient-1 symmetry `heckeGClass_inversion`, total theta `heckeF` + `heckeF_inversion`),
`CompletedZeta/ThetaEstimates.lean` (shortest vector, Gaussian tails, 0-split, weight lower
bounds, joint continuity, `continuousOn_heckeG`, `unitBoxVol`, `exists_heckeG_dev_bound`),
`CompletedZeta/FEPair.lean` (**`heckeFEPair : WeakFEPair ℂ`** — f = g = heckeF, k = 1/2,
ε = 1, f₀ = g₀ = `heckeFConst` = h·w⁻¹·vol; `isBigO_exp_neg_rpow` + transfers).

**What mathlib now gives for free** (`Mathlib.NumberTheory.LSeries.AbstractFuncEq`):
`(heckeFEPair K).Λ₀` entire, `.Λ` with poles exactly at σ ∈ {0, 1/2} + residues,
`.hasMellin` on Re σ > 1/2, `.functional_equation : Λ(1/2−σ) = Λ(σ)`.

**Verified constant derivation** (in SP1-AGE ticket, step-by-step): the final agreement is
`mellin (heckeF − heckeFConst) (s/2) = κ·2^{-r₂}·completedZetaPrefactor K s·ζ_K(s)` with κ
the (t,u)→y Jacobian constant — **s-independent** (β = 4^{r₂}/|Δ| kills every s-dependent
mismatch: `s_C^{-s/2} = N(I)^s·2^{-r₂s}|Δ|^{s/2}`, the `N(I)^s` cancels the counting side,
`2^{-r₂s}` turns `π^{-s}Γ(s)` into `Γℂ(s)/2`, `|Δ|^{s/2}` is the prefactor's power). So
`completedDedekindZeta := (κ·2^{-r₂})⁻¹·(heckeFEPair K).Λ (s/2)`, and `s(s−1)Λ_K` entire
falls out of `Λ = Λ₀ − f₀/σ − ε g₀/(k−σ)` (pole terms → entire `−2(s−1)f₀`, `+2s g₀`).

**Remaining Lean bricks to `∃ Λ, IsCompletedDedekindZeta K Λ`** (order): (α) Mellin scaling
`mellin (g∘(c·)) σ = c^{-σ}·mellin g σ` (mathlib `mellin_comp_mul_left`? verify);
(β) box-unfolding `w⁻¹∫_box ∑_{L_I∖0} = ∑_{(I∖0)/units}∫_{logSpace}` (torsion-w cancellation;
`IsAddFundamentalDomain` unfolding + `heckeTheta_unit_mul` orbit structure);
(γ) per-orbit `(t,u) → y` change of variables ⇒ `κ·Γ(σ)^{r₁}π^{-r₁σ}Γ(2σ)^{r₂}π^{-2r₂σ}·|Na|^{-2σ}`
(pins κ; the Jacobian is the regulator-style determinant of
`(τ,u) ↦ τ/n + 2·fullLog(u)_w/mult_w`); (δ) `∑_{(I∖0)/units}|Na|^{-s} = N(I)^{-s}·∑_{𝔞∈[I⁻¹]}N𝔞^{-s}`
(mathlib `FundamentalCone.idealSetEquivNorm`); (ε) sum over classes, define
`completedDedekindZeta`, prove both `IsCompletedDedekindZeta` conditions, conclude existence.
(β)+(γ) are the two big ones — both fully specified above.
