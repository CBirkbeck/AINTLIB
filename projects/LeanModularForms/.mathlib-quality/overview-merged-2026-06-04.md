# Merged-Codebase Overview — 2026-06-04

**Branch:** `hecke-ring` · **Total LOC:** 81,989 · **Files:** 217 · **Build:** clean ·
**Sorries:** 1 permitted (`Newforms/MainLemma.lean:152`) + 1 flag-and-document
(`GLn/PolynomialRing.lean:877`, `evalHom_injective` general case) · **`maxHeartbeats`
overrides:** 0 · **Custom axioms:** 0.

The valence-formula + generalized-residue-theorem + HW-3.3 chain was just merged
from `feat/mathlib-prs` (commit `b3dbd99`, mathlib-v4.30 drift cleaned in `067fd49`).
This is the first project-wide audit after the merge.

---

## 1. Executive Summary

The merge dropped two large, **disjoint** subtrees into the same project:

| Subtree | LOC | Files | Top API |
|---|---|---|---|
| `LeanModularForms/HeckeRIngs/` + `SMOObligations/` + `Eigenforms/` | 41,317 | 81 | `strongMultiplicityOne_constMul`, `heckeT_p_adjoint`, `exists_simultaneous_eigenform_basis` |
| `LeanModularForms/ForMathlib/` | 36,212 | 118 | `valence_formula_textbook`, `hw_3_3_clean_full_mero` |
| `LeanModularForms/Modularforms/` | 4,220 | 17 | dim-formula transport, Petersson, q-expansion-slash |
| `LeanModularForms/SMOObligations.lean` (root) + `LeanModularForms.lean` | 240 | 2 | aggregation |

Critically, **no Lean import crosses the two subtrees in either direction**:

```
grep "LeanModularForms\\.ForMathlib" LeanModularForms/HeckeRIngs/ ...  →  empty
grep "LeanModularForms\\.HeckeRIngs\\|...\\.SMOObligations\\|...\\.Eigenforms"
     LeanModularForms/ForMathlib/                                       →  empty
```

The two halves share **only** mathlib infrastructure (`UpperHalfPlane`,
`ModularForm`, `qExpansion`, `cuspFunction`, `𝒮ℒ`, `Gamma 1`, `ModularGroup.S/T`,
`ModularGroup.fd` notation `𝒟`). Both halves are otherwise independent
mathematical universes glued at the root file `LeanModularForms.lean`.

This is *good* for compilation isolation but means **all duplication is at the
mathematical/conceptual layer, not at the import layer** — and there is real
duplication of CPV / piecewise-C¹-path infrastructure *inside* `ForMathlib/`,
inherited from the iterative redevelopment that produced the final chain.

### Top reduction opportunities (ranked by impact)

| # | Opportunity | Where | Est. LOC delta | Risk |
|---|---|---|---|---|
| 1 | Retire the **primed CPV chain** (`cauchyPrincipalValue'`, `cauchyPrincipalValueOn`, `generalizedWindingNumber'`, `fdBoundary_H` on `[0,5]`) by rebasing the `ValenceFormula/PVChain/` files onto `[0,1]` + `HasCauchyPV(On)` | `ClassicalCPV.lean`, `FDBoundaryReparametrization.lean`, `ResidueSideBridge.lean`, `ValenceFormulaBridged.lean`, half of `ValenceFormula/PVChain/` | **−2,000 to −2,500** | Medium — change of variables in long FTC telescopes; need to preserve axiom-cleanness of `valence_formula_textbook` |
| 2 | Unify the **PwC1 path structures**: drop `ClassicalCPV.PiecewiseC1Curve`/`PiecewiseC1Immersion` in favour of `PiecewiseC1Path` + `ClosedPwC1*` | `ClassicalCPV.lean` (delete most of it), `PaperPwC1Immersion.lean`, callers | **−400 to −700** | Low/medium — `ClassicalCPV` has only 192 LOC; the 62 use-sites need conversion |
| 3 | **`Newforms.lean` already imports `Modularforms/DimensionFormulas`** for `FiniteDimensional`. The valence formula provides a stronger orbit-counting result. Bridge `valence_formula_textbook` → `dimension_level_one` as a corollary, then optionally replace the inductive-via-Δ proof in mathlib's `DimensionFormula.lean` with the orbifold one (PR'd upstream — *not* a project-internal reduction, but listed because it is the single most natural mathlib PR coming out of this merge) | bridge file under `ForMathlib/` + mathlib PR | **+50** locally, **0** net once upstreamed | Low |
| 4 | Collapse the **three top-50-LOC headline wrappers** (`ValenceFormulaFinal.lean` ↔ `ValenceFormulaBridged.lean` ↔ `ResidueSide.lean`) once item 1 lands — the `…BridgedFM/…Final/…OrbitFinsumFM` triple-rephrase becomes one theorem | `ForMathlib/Valence*.lean` | **−250** | Low |
| 5 | Inline-and-delete `ForMathlib/Residue.lean` (40 lines, defines `residue` via `limUnder` of circle integrals; mathlib has all parts but no top-level name — could become a *PR* instead of a project lemma) | `ForMathlib/Residue.lean`, `ResidueCircleIntegral.lean` | **−120** | Low |

**Total estimated reduction from items 1+2+4+5: ≈ 2,800–3,500 LOC (≈ 3.4–4.3 %).**

There are *no* large cross-subtree duplications. The merge is structurally clean.

---

## 2. Cross-Subtree Duplication (SMO/Hecke ↔ ForMathlib)

### 2.1 Verdict: **near-zero direct duplication**

Every candidate flagged by the question is actually shared via mathlib, not duplicated:

| Concept | ForMathlib uses | HeckeRIngs/Modularforms uses | Verdict |
|---|---|---|---|
| Fundamental domain | mathlib `ModularGroup.fd` (notation `𝒟`) directly (`EllipticPoints.lean:20` comment confirms) | mathlib `𝒟` and the open version `𝒟ᵒ` (in `PSL2Action.lean`, `PeterssonLevelN.lean`) | shared upstream — no project duplication |
| Modular form coercion to `ℂ → ℂ` | `ModularInvariance.lean:30 abbrev modularFormCompOfComplex := f ∘ UpperHalfPlane.ofComplex` | direct `UpperHalfPlane.ofComplex` use in `Modularforms/DimGenCongLevels/NormTransfer.lean:31`; bare `f` coercion elsewhere | one tiny `abbrev` only on the ForMathlib side; not duplicated |
| q-expansion | mathlib `UpperHalfPlane.qExpansion`, `cuspFunction`, `Periodic.qParam` directly | same | no duplication |
| Cusp form predicate | mathlib `ModularForm.IsCuspForm` (no local definition needed) | `Modularforms/IsCuspForm.lean:34` thin wrapper around mathlib's `IsCuspForm` (kept for SL-side names) | wrapper acknowledged in its own docstring — keep |
| Order at cusp | `EllipticPoints.lean:97 orderAtCusp' f := (qExpansion 1 f).order.toNat` | no analogue (other subtrees do not need vanishing order at the cusp explicitly — they use `qExpansion.coeff` and Sturm bounds) | unique to ForMathlib |
| Order at a point of ℍ | `EllipticPoints.lean:93 orderOfVanishingAt' f z := (meromorphicOrderAt …).untop₀` | none | unique to ForMathlib |
| Modular orbits on ℍ | `Orbits.lean:57 abbrev OrbitFM := MulAction.orbitRel.Quotient SL(2, ℤ) ℍ` | nowhere (SMO/Hecke uses cosets of congruence subgroups, not full SL₂(ℤ) orbits) | unique to ForMathlib |
| Elliptic points `i`, `ρ` | `EllipticPoints.lean:29, 32, 41` | nowhere (SMO/Hecke arithmetic does not name the elliptic points) | unique to ForMathlib |
| FD boundary as a parametrized curve | `FDBoundary.lean:48 fdBoundaryFun`, `FDBoundaryH.lean fdBoundary_H` (the two parametrizations — see §3.1) | nowhere (SMO/Hecke does not contour-integrate) | unique to ForMathlib |
| Petersson inner product | nowhere | `Modularforms/PeterssonInnerProduct.lean`, `PeterssonLevelN.lean`, `PeterssonInner.lean` | unique to Modularforms/Hecke (consumed by Hecke adjoint chain) |

The `FM` suffix used throughout `Orbits.lean`, `OrbitPairing.lean`, `CanonicalReps.lean`
(e.g. `vAdd_one_mem_fd_of_left_vertFM`) is a *naming convention* indicating "ForMathlib
target", not a parallel to an SL-side or PSL-side namesake — `grep` confirms zero
non-`FM` versions exist anywhere.

### 2.2 Bridge: dimension formula ↔ valence formula

Mathlib has `ModularForm.dimension_level_one` (in
`Mathlib/NumberTheory/ModularForms/LevelOne/DimensionFormula.lean:249`) proved
**inductively via `CuspForm.discriminantEquiv`** (division by Δ + induction on weight),
*not* via the valence formula. The project's `Modularforms/DimensionFormulas.lean`
is a thin transport wrapper around mathlib's theorem (project uses `Γ(1)`-indexed
spaces; mathlib uses `𝒮ℒ`-indexed spaces; `mcast`-based linear equivalences bridge them).

`HeckeRIngs/GL2/Newforms/Basic.lean:13` and `HeckeRIngs/GL2/Newforms.lean:20` import
this file purely for `FiniteDimensional` instances — they do not need the orbifold
count, only the fact that the spaces are finite-dimensional.

**The valence formula does not currently feed any SMO/Hecke result.** It exists
only as the headline `valence_formula_textbook`. The natural connection:

```
valence_formula_textbook  ⟹  ord_∞(f) + ord_i(f)/2 + ord_ρ(f)/3 + Σ ord_q(f) = k/12
                          ⟹  Sturm-type bounds for level 1 (already in mathlib)
                          ⟹  dimension_level_one  (already in mathlib, but via Δ)
```

A **direct upstream-quality contribution** would be to derive `dimension_level_one`
from `valence_formula_textbook` and PR the orbifold-counting proof to mathlib as an
alternative. This is **not a project-internal LOC reduction** but it is the single
most natural use of the merged result.

---

## 3. Internal ForMathlib Duplication

This is where the real opportunities live. The 118 files in `ForMathlib/` are the
result of multiple iterative redevelopments, and three layers of API survive in parallel.

### 3.1 Pairwise duplication table

| Decl A | Decl B (and C) | Same statement? | Same proof structure? | Verdict |
|---|---|---|---|---|
| `ClassicalCPV.cauchyPrincipalValue'` (`ℝ→ℂ`, `[a,b]`, `limUnder`) | `CauchyPrincipalValue.HasCauchyPV` (`PiecewiseC1Path`, `[0,1]`, `Tendsto`) and `GeneralizedResidueTheory/Residue.cauchyPrincipalValueOn` (`ℝ→ℂ`, `[a,b]`, `limUnder`) | Same CPV concept | No — A and C use `limUnder` ⇒ junk on failure; B uses `Tendsto` ⇒ API-rich | **UNIFY onto B** (HasCauchyPV is the API-rich primary; 151 use-sites vs A's 53) |
| `ClassicalCPV.generalizedWindingNumber'` (`limUnder`, `[a,b]`) | `GeneralizedWindingNumber.HasGeneralizedWindingNumber` + `generalizedWindingNumber` (Tendsto, wraps `HasCauchyPV`) | Same winding-number concept | A: junk-on-failure; B: predicate + value with `.eq` projection | **UNIFY onto B** (B is in `GeneralizedWindingNumber.lean:62`; A is legacy) |
| `CauchyPrincipalValue.cpvIntegrandOn` line 119 | `GeneralizedResidueTheory/Residue.cauchyPrincipalValueIntegrandOn` line 38 | **Literally identical** body (`if ∃ s ∈ S, ‖γ t - s‖ ≤ ε then 0 else f (γ t) * deriv γ t`) | identical | **DEDUP** — the GeneralizedResidueTheory version is the older internal name; rename to the primary or delete |
| `ClassicalCPV.PiecewiseC1Curve` + `PiecewiseC1Immersion` (`ℝ → E` with `[a,b]`) | `PiecewiseC1Path` + `PwC1Immersion` (in `PiecewiseC1Path.lean`, wraps `Path`, on `[0,1]`) + `PaperPwC1Immersion.ClosedPwC1Curve` + `ClosedPwC1Immersion` (wraps `PiecewiseC1Path`, closed loops, on `[0,1]`) | Three independent structures for the same concept | No — different intervals, different bases | **UNIFY onto `PiecewiseC1Path` / `ClosedPwC1*`** (721 + 86 use-sites; A has 62) |
| `FDBoundary.fdBoundaryFun H : ℝ → ℂ` parametrized on `[0, 1]` | `FDBoundary*.fdBoundary_H H : ℝ → ℂ` parametrized on `[0, 5]` | Same FD boundary curve | Different param | **UNIFY onto `[0,1]`** — eliminates `FDBoundaryReparametrization.lean` entirely |
| `ForMathlib/ResidueSide.lean:60 cpv_residue_side_forMathlib` (header file pulling from `ValenceFormula/PVChain/Assembly{,/ResidueSide}.lean`) + `ForMathlib/ResidueSideBridge.lean:41 cpv_residue_side_HasCauchyPVOn` (post-bridge into HasCauchyPVOn) | Same residue-side limit identity, two different API endings | first uses the primed CPV; second uses HasCauchyPVOn; bridged via `hasCauchyPVOn_of_cauchyPVOn'_tendsto` | yes | **COLLAPSE** once item 1 (single CPV API) lands |
| `ForMathlib/ValenceFormula.lean` (307 LOC) ↔ `ForMathlib/ValenceFormulaBridged.lean` (161 LOC) ↔ `ForMathlib/ValenceFormulaFinal.lean` (70 LOC) | Three façades; the Final one re-states using `ordOrbitQ`/`NonEllOrbitFM`; the Bridged one provides `…_unconditional_FM` and the `…_orbit_finsum_FM` re-pack; the original `ValenceFormula.lean` is the pre-bridge Finset-form proof | The deepest one (`…_unconditional_mkD` inside `ValenceFormula.lean`) requires residue/modular side Tendsto hypotheses; the Bridged file discharges them; the Final file restates with the orbit finsum | layered | **CONSOLIDATE** — once item 1 lands, the three become one theorem with one statement |
| `ForMathlib/CoreIdentityProof.lean:407 valence_formula_orbit_sum_of_pvChain` (95-line proof) | `ForMathlib/PVChainProof.lean:125 valence_formula_of_two_sides_Hgt1` | Combine the two sides into the valence identity; CoreIdentityProof does the orbit-sum decomposition; PVChainProof does the height-bounded form | no | both load-bearing — keep |
| `ForMathlib/Orbits.lean ordOrbitFM` ↔ `ForMathlib/OrbitPairing.lean *FM` family ↔ `ForMathlib/CanonicalReps.lean repCanon` | Each plays a distinct role: Orbits = quotient + finiteness; OrbitPairing = T- and S-translates for vertical/arc identification; CanonicalReps = choice of representatives for the textbook form | no overlap | keep all three but **drop the `FM` suffix** project-wide (commit `7b0a76a` already removed 65 such suffixes; the remaining ~50 in `OrbitPairing.lean`, `Orbits.lean`, `CanonicalReps.lean` are leftover from the merge) |
| `ForMathlib/Residue.lean residue` (uses `limUnder ∘ circleIntegral`) | mathlib has `MeromorphicAt.order` but no top-level `residue` — see §4.4 below | unique | mostly mathlib-portable | **PR upstream** then delete |

### 3.2 Files that vanish if §3.1 items 1-2 land

- `ClassicalCPV.lean` (192 LOC) — the three flagged decls plus the legacy
  `PiecewiseC1Curve`/`PiecewiseC1Immersion` structures account for ~80% of the file.
- `FDBoundaryReparametrization.lean` (221 LOC) — exists *solely* to bridge `[0,5]` ↔ `[0,1]`.
- `ResidueSideBridge.lean` (67 LOC) — exists *solely* to convert `cauchyPVOn'` → `HasCauchyPVOn`.
- `ValenceFormulaBridged.lean` (161 LOC) → collapses into the Final file.
- Possibly half of `ValenceFormula/PVChain/Helpers.lean` (342 LOC), `ResidueSideInfra.lean`
  (600 LOC), `Assembly.lean` (684 LOC), `Assembly/ResidueSide.lean` (399 LOC) — the
  parts that use `cauchyPrincipalValueIntegrandOn` and `[0,5]` parametrization.

That is **~1,800 LOC of pure plumbing** plus another **~1,500 LOC of mechanical
reparam edits** = total **~3,300 LOC** of net deletion potential.

---

## 4. Mathlib v4.30 Redo Candidates in ForMathlib

The cleanup commit `067fd49` ("ForMathlib v4.30.0 drift: cusp wrappers + deprecation
cleanup") already absorbed the obvious changes (`CuspFormSubmodule`, `LevelOne.Basic`,
`CongruenceSubgroups`). After re-auditing the chain against mathlib v4.30:

### 4.1 Things already correctly using new mathlib

| ForMathlib decl | What it uses | Status |
|---|---|---|
| `EllipticPoints.orderAtCusp'` | `UpperHalfPlane.qExpansion`, `.order.toNat` | ✓ |
| `Orbits.G_analyticAtFM` | `SlashInvariantFormClass.eq_cuspFunction`, `analyticAt_cuspFunction_zero` | ✓ |
| `ModularInvariance.cuspFunction_eventually_ne_zero` | `ModularFormClass.analyticAt_cuspFunction_zero`, `eq_cuspFunction` | ✓ |
| `Seg5CuspIntegral.hasFPowerSeries_cuspFunction_SL` | mathlib `HasFPowerSeriesOnBall`, `qExpansionFormalMultilinearSeries`, `hasSum_qExpansion` | ✓ |
| `EllipticPoints` headers import `Mathlib.NumberTheory.ModularForms.LevelOne.Basic` directly | uses `𝒮ℒ`-compatible API path | ✓ |

### 4.2 Things in ForMathlib that mathlib v4.30 likely now supersedes

| ForMathlib | Mathlib v4.30 candidate | Status |
|---|---|---|
| `ForMathlib/Residue.lean:39 residue` (40 LOC file) | **No mathlib `residue` exists** at the analytic level (only `RingTheory.ResidueField`); but every piece is there — `MeromorphicAt`, `meromorphicOrderAt`, `circleIntegral`. The natural target lemma `residue f z₀ = meromorphicOrderAt.coeff` does exist piecewise. | **PR upstream** as `MeromorphicAt.residue` |
| `ForMathlib/Residue.HasSimplePoleAt` predicate (decomposes `f = c/(z-z₀) + g` near `z₀`) | mathlib has `MeromorphicAt.order_eq_negOne_iff` + `meromorphicAt_principalPart_iff`, but not a `HasSimplePoleAt` predicate | **PR upstream** |
| `ForMathlib/EllipticPoints.orderOfVanishingAt'` (extends `f : ℍ → ℂ` to `ℂ → ℂ` via `if 0 < w.im then f ⟨w,h⟩ else 0`) | The `if 0 < w.im` lift agrees with `f ∘ UpperHalfPlane.ofComplex` on the open upper half plane (see `UpperHalfPlane.ofComplex_apply_of_im_pos`). Could be redefined as `meromorphicOrderAt (f ∘ UpperHalfPlane.ofComplex) (z:ℂ)`, eliminating the dependent `if h : 0 < w.im` and unblocking simp lemmas via `comp_ofComplex` | **REFACTOR** — small lift; would enable `MeromorphicOn` lemmas to fire directly |
| `ForMathlib/ModularInvariance.modularFormCompOfComplex` (`abbrev f ∘ UpperHalfPlane.ofComplex`) | already a thin abbrev | keep as-is (it is good practice) |
| `ForMathlib/AtImInfty.eventually_atImInfty` (in `Modularforms/AtImInfty.lean`) | docstring already says "candidates for upstreaming to `Mathlib.Analysis.Complex.UpperHalfPlane.FunctionsBoundedAtInfty`" | **PR upstream** |
| `ForMathlib/AtImInfty.qExpansion_ext2` | same docstring tag — needs `FunLike` for raw `ℍ → ℂ` (also provided locally) | **PR upstream alongside the FunLike instance** |
| `Modularforms/AtImInfty.instance : FunLike (ℍ → ℂ) ℍ ℂ` | mathlib does not have this — but tagging it `@[simp]` and exposing it lets later `cuspFunction`-extensionality dispatch by `DFunLike.ext` | **PR upstream** as an instance with the `FunLike` API |

### 4.3 Hand-rolled patterns that mathlib v4.30 could simplify

A spot check across `ForMathlib/`:

- 37 uses of `Filter.limUnder` survive (compared to 151 uses of `HasCauchyPV`,
  which is `Tendsto`-based). Most of the `limUnder` uses are in: `Residue.lean`,
  `ResidueCircleIntegral.lean`, `ClassicalCPV.lean`, `GeneralizedResidueTheory/Residue.lean`,
  `GeneralizedResidueTheory/Homotopy/Integrality.lean`. All of these would benefit
  from `Tendsto`-first restatements paired with `.limUnder_eq` value-projection
  lemmas (the pattern already used by `HasCauchyPV.cauchyPV_eq` and
  `HasGeneralizedWindingNumber.eq`).

- The pattern `if h : 0 < w.im then f ⟨w, h⟩ else 0` appears in
  `EllipticPoints.orderOfVanishingAt'`. With mathlib's `UpperHalfPlane.ofComplex`
  (`Mathlib/Analysis/Complex/UpperHalfPlane/Topology.lean:144`) the same content
  can be expressed without dependent-`if` as `f ∘ UpperHalfPlane.ofComplex`.

- The four `Modularforms/PSL2Action.lean` results (`isFundamentalDomain_fdo_PSL`
  and related) are essentially the "PSL₂(ℤ) acts on ℍ with `𝒟ᵒ` as a fundamental
  domain" identity. Mathlib v4.30 has the SL₂(ℤ) version (`ModularGroup.fd`)
  but does **not** have the explicit PSL₂(ℤ)-as-quotient-acting-on-ℍ packaged
  yet. The 724-LOC `PSL2Action.lean` is a substantial mathlib PR candidate.

### 4.4 Things to *not* touch

- `Modularforms/IsCuspForm.lean` (36 lines) is intentionally a thin wrapper
  around `ModularForm.IsCuspForm`, documented as such. Keep.
- `Modularforms/DimensionFormulas.lean` (151 lines) is intentionally a transport
  wrapper around `ModularForm.dimension_level_one`. Keep.
- `ValenceFormulaFinal.lean` (70 lines) is the user-facing axiom-clean façade;
  even after the consolidation in §3.2 it should keep its own line for readability
  and for `lean_verify` smoke tests.

---

## 5. Architectural Unification Opportunities

### 5.1 Single CPV API across the project

After §3.2, every `ForMathlib/` file should consume CPV through one and only one
predicate, `HasCauchyPV`/`HasCauchyPVOn` (CPV exists with value `L` ⇔ the
ε-truncated integral tends to `L` as `ε → 0⁺`). The pattern

```
predicate :   HasCauchyPV f γ z₀ L
value      :   cauchyPV f γ z₀
bridge     :   HasCauchyPV.cauchyPV_eq : HasCauchyPV f γ z₀ L → cauchyPV f γ z₀ = L
```

is already the right design at `CauchyPrincipalValue.lean:79, 85, 90`. Replicate
this pattern for `residue`, `generalizedWindingNumber`, and any future analytic
predicate.

### 5.2 Single piecewise-C¹ path family

After §3.1 row 4, every closed piecewise-C¹ path should be either a
`PiecewiseC1Path x x` (open path, both endpoints the same) or a
`ClosedPwC1Curve x` / `ClosedPwC1Immersion x` (with the closure-baked-in `extends`)
— never the raw `PiecewiseC1Curve` from `ClassicalCPV.lean`. The `ClosedPwC1`
hierarchy already has the right API (`continuous`, `deriv_extend_intervalIntegrable`,
`lipschitzOnWith_piece`, etc., all in `PaperPwC1Immersion.lean:78-506`).

### 5.3 Drop the `FM` suffix consistently

Commit `7b0a76a` already removed 65 `FM` suffixes. ~50 remain in `Orbits.lean`
(every public name: `orbFM`, `OrbitFM`, `ordOrbitFM`, `oiFM`, `orhoFM`,
`NonEllOrbitFM`, `s₀FM`, `s₀FM_mem_fd`, `s₀FM_complete`, `finite_zeros_in_fdFM`,
`ord_smul_eqFM`, `ordOrbit_mkFM`, `orb_rho_plus_one_eq_orb_rhoFM`, etc.), in
`OrbitPairing.lean` (all 20+ names), and in `CanonicalReps.lean`. None of these
have non-`FM` counterparts. Mechanical rename, zero LOC change, much better
readability.

### 5.4 Bridge file: valence formula → Sturm bound → dimension formula

A 30-line file deriving `dimension_level_one` from `valence_formula_textbook`
makes the connection explicit and removes the temptation (for downstream users)
to import the entire ForMathlib chain just for the rank-1 result. It also seeds
the upstream mathlib PR for the orbifold-counting proof.

---

## 6. Long-Proof Catalog (>50 lines)

Total proofs >50 lines: **80** (200+ lines: 5; 100-199 lines: 22; 50-99 lines: 53).
Top 30:

```
LOC  File:line  Decl name
---  --------  ---------
304  LeanModularForms/ForMathlib/HungerbuhlerWasem/MultiCrossingCPV.lean:929        perCrossing_higherOrder_window_integral_tendsto_corner
232  LeanModularForms/ForMathlib/HungerbuhlerWasem/LocalCutoffs.lean:747            perCrossing_window_integral_tendsto_exact
214  LeanModularForms/ForMathlib/ValenceFormula/WindingWeights/I.lean:402           ftc_logDeriv_telescope_i
207  LeanModularForms/ForMathlib/HungerbuhlerWasem/MultiCrossingCPV.lean:722        cpv_higherOrder_tendsto_along_sorted_corner
204  LeanModularForms/ForMathlib/GeneralizedResidueTheory/PVInfrastructure/SingularAnnulus.lean:279   singular_annulus_bound_explicit
191  LeanModularForms/SMOObligations/Lemma4_6_14.lean:341                           miyake_4_6_14_delta_slash_sum_coeff_zero
174  LeanModularForms/ForMathlib/HungerbuhlerWasem/LaurentExtraction.lean:400        mero_f_minus_total_eventuallyEq_analytic
169  LeanModularForms/ForMathlib/HungerbuhlerWasem/MultiPoleDCT.lean:200             hasCauchyPVOn_polarPart_of_hasCauchyPV_multipole
167  LeanModularForms/ForMathlib/ValenceFormula/OnCurvePV/EndpointCorner.lean:335    cpv_at_corner
159  LeanModularForms/ForMathlib/GeneralizedResidueTheory/PVInfrastructure/UniformStepBound.lean:28   pv_step_bound_ratio_two_uniform
155  LeanModularForms/ForMathlib/HungerbuhlerWasem/LocalCutoffs.lean:196             exists_left_cutoff_local
148  LeanModularForms/ForMathlib/ValenceFormula/WindingWeights/RhoPlusOne.lean:318   ftc_logDeriv_telescope_rho_plus_one
145  LeanModularForms/ForMathlib/HungerbuhlerWasem/Crossing.lean:246                 cpv_polarPart_at_uncrossed_pole
138  LeanModularForms/ForMathlib/ValenceFormula/WindingWeights/Rho.lean:245           ftc_logDeriv_telescope_rho
133  LeanModularForms/ForMathlib/ValenceFormula/OnCurvePV/EndpointCorner.lean:169     cpv_at_endpoint
132  LeanModularForms/ForMathlib/ValenceFormula/PVChain/Assembly/ResidueSide.lean:268 cpv_residue_side_tendsto
126  LeanModularForms/ForMathlib/HungerbuhlerWasem/MultiCrossingCPV.lean:244          cpv_tendsto_along_sorted_corner
125  LeanModularForms/ForMathlib/WindingInteger.lean:318                              exists_continuous_arg_lift_with_partition
114  LeanModularForms/HeckeRIngs/GL2/Unified/CuspNebentypusSpace.lean:72              heckeT_n_cusp_charRestrict_commute_from_mulFormula
113  LeanModularForms/ForMathlib/HungerbuhlerWasem/MultiCrossingCPV.lean:1233         hasCauchyPVOn_multiCrossing_higherOrder_corner
111  LeanModularForms/ForMathlib/GeneralizedResidueTheory/OnCurvePV/Basic.lean:26     pv_limit_via_dyadic
111  LeanModularForms/ForMathlib/ValenceFormula/PVChain/ArcContribution.lean:253      arc_cpv_integral_S_identity
109  LeanModularForms/ForMathlib/ValenceFormula/OnCurvePV/Main.lean:507               cpv_exists_generic_seg5_normSq_one
106  LeanModularForms/ForMathlib/HungerbuhlerWasem/MultiCrossingCPV.lean:1368         cpv_polarPart_at_multiCrossed_pole_under_condB_corner
105  LeanModularForms/ForMathlib/ValenceFormula/WindingWeights/RhoPlusOne.lean:566    pv_integral_at_rho_plus_one_tendsto
104  LeanModularForms/ForMathlib/HungerbuhlerWasem/LaurentExtraction.lean:93          residue_of_laurent_expansion
102  LeanModularForms/HeckeRIngs/AbstractHeckeRing/Associativity.lean:638             smul_assoc_singles
 99  LeanModularForms/ForMathlib/GeneralizedResidueTheory/PVInfrastructure/AnnulusBounds.lean:273    annulus_symmDiff_measure_bound
 97  LeanModularForms/ForMathlib/WindingWeightProofs.lean:204                          fdBoundaryFun_seg5_dist_rhoPlusOne_lower
 97  LeanModularForms/ForMathlib/HungerbuhlerWasem/MultiCrossingCPV.lean:466           hasCauchyPV_inv_sub_multiCrossing_corner
```

(The remaining 50 proofs in the 50-99 line range cluster heavily in
`HungerbuhlerWasem/`, `ValenceFormula/`, `SMOObligations/`, and the per-prime
`HeckeRIngs/GL2/` chain — all genuine multi-stage arguments, all candidates
for `/decompose-proof` after the structural consolidation lands.)

The HungerbuhlerWasem `perCrossing_*` family (304-LOC and 232-LOC) and the
`*_telescope_i/rho/rho_plus_one` triple (214, 148, 138) are the natural top-3
targets for `/decompose-proof`. Each is a single FTC + estimate +
dominated-convergence + take-the-limit chain that splits cleanly into 3-4 lemmas.

---

## 7. Top 10 Biggest Files

```
LOC   File
----  ----
1937  LeanModularForms/HeckeRIngs/GL2/HeckeT_n.lean
1801  LeanModularForms/HeckeRIngs/GL2/AdjointTheory/FDTransport.lean
1607  LeanModularForms/HeckeRIngs/GLn/CongruenceHecke/Surjectivity.lean
1537  LeanModularForms/ForMathlib/HungerbuhlerWasem/MultiCrossingCPV.lean
1524  LeanModularForms/HeckeRIngs/GL2/AdjointTheory/DeltaBSystem.lean
1424  LeanModularForms/HeckeRIngs/GL2/Unified/NebentypusHeckeRingHom.lean
1367  LeanModularForms/SMOObligations/SquarefreeDecomp.lean
1284  LeanModularForms/SMOObligations/StrongMultiplicityOneFull.lean
1249  LeanModularForms/HeckeRIngs/GL2/Unified/TwistedHeckeRing.lean
1115  LeanModularForms/SMOObligations/DescentCosets.lean
```

The ForMathlib half's largest file (`HungerbuhlerWasem/MultiCrossingCPV.lean` at
1537) ranks 4th project-wide; the SMO/Hecke half dominates the top of the list
because Hecke-operator manipulations on q-expansions, coset representatives, and
double-coset decompositions produce intrinsically heavy combinatorial files.

The candidates for `/split-file` (mathlib threshold = 1500 lines) are:

- `HeckeRIngs/GL2/HeckeT_n.lean` (1937 LOC) — already candidate, contains the
  full Hecke-operator algebra plus q-expansion identities.
- `HeckeRIngs/GL2/AdjointTheory/FDTransport.lean` (1801 LOC) — fundamental-domain
  transport machinery for the adjoint trace formula.
- `HeckeRIngs/GLn/CongruenceHecke/Surjectivity.lean` (1607 LOC) — surjectivity of
  the congruence-Hecke map.
- `ForMathlib/HungerbuhlerWasem/MultiCrossingCPV.lean` (1537 LOC) — the
  multi-crossing CPV existence chain that culminates in the discharge of HW 3.3.
- `HeckeRIngs/GL2/AdjointTheory/DeltaBSystem.lean` (1524 LOC) — the
  Δ-and-B-system algebra underpinning the trace identity.

Notes:
- The 6 protected headlines all live in files **below** the split threshold:
  `ValenceFormulaFinal.lean` (70), `HW33Clean.lean` (82), `AdjointTheory/ConcreteFamily.lean`
  (697), `AdjointTheoryPetersson.lean` (847), `StrongMultiplicityOneFull.lean` (1284).
  None are at risk during a split.

---

## 8. Reduction Plan (concrete tickets)

Each ticket here is independent — they can be executed in any order, although the
order below maximises cumulative LOC delta and minimises rework.

### Ticket A — single CPV predicate

- **A1**. Audit every `cauchyPrincipalValueIntegrandOn` use-site under
  `LeanModularForms/ForMathlib/GeneralizedResidueTheory/Residue.lean` and
  `Residue/GeneralizedTheoremBase.lean`. Rename to `cpvIntegrandOn`
  (the `CauchyPrincipalValue` primary). Delete the duplicate definition at
  `GeneralizedResidueTheory/Residue.lean:38`.  Δ ≈ −15 LOC, but unblocks A2.
- **A2**. Replace `cauchyPrincipalValueOn` (uses `limUnder`) with the
  `Tendsto`-based existence proposition `HasCauchyPVOn` plus a value lemma
  `HasCauchyPVOn.cauchyPVOn_eq`. Δ ≈ −60 LOC in `Residue.lean` + cascade.
- **A3**. Audit every `cauchyPrincipalValue'` and `generalizedWindingNumber'`
  use-site (53 total, mostly in `ValenceFormula/PVChain/*` and `Boundary/*`).
  Convert each statement and its callers to `HasCauchyPV` / `generalizedWindingNumber`.
  Δ ≈ −1,500 LOC (most of the cascade is mechanical because the `Tendsto`-based
  forms compose with mathlib `Filter.Tendsto.{comp,add,smul,…}` natively).
- **A4**. Delete `ClassicalCPV.lean` (the `'`-primed defs go away with A3; the
  legacy `PiecewiseC1Curve` / `PiecewiseC1Immersion` structures go away with
  Ticket B). Δ ≈ −192 LOC.

### Ticket B — single piecewise-C¹ path family

- **B1**. Replace the ~60 use-sites of `PiecewiseC1Curve` with `PiecewiseC1Path` +
  closure hypothesis, or with `ClosedPwC1Curve` directly. Δ ≈ −0 LOC at use-sites
  (mostly type changes), but enables B2.
- **B2**. Delete `PiecewiseC1Curve` and `PiecewiseC1Immersion` from
  `ClassicalCPV.lean`. Combined with A4, this empties `ClassicalCPV.lean`. Δ ≈ −80 LOC.

### Ticket C — single boundary parametrization

- **C1**. Replace every use of `fdBoundary_H H : ℝ → ℂ` on `[0,5]` with
  `fdBoundaryFun H : ℝ → ℂ` on `[0,1]` (or vice-versa — `[0,1]` is preferred
  since it aligns with mathlib's `Path.extend` convention). The change of
  variable is `u = 5 t` and propagates through every FTC telescope. Δ ≈ −300 LOC
  cumulatively (eliminates the `cauchyPVOn'_tendsto_of_hasCauchyPVOn` bridge
  plus the implied integral-change-of-variable boilerplate).
- **C2**. Delete `FDBoundaryReparametrization.lean`. Δ ≈ −221 LOC.
- **C3**. Delete `ResidueSideBridge.lean`. Δ ≈ −67 LOC.

### Ticket D — collapse the three valence-formula façade layers

- **D1**. Once tickets A and C land, merge `ValenceFormulaBridged.lean` into
  `ValenceFormulaFinal.lean`. Δ ≈ −90 LOC (the `…_unconditional_mkD` step becomes
  inline after the CPV layer is uniform).
- **D2**. Optionally rename `ValenceFormulaFinal` →  the original `ValenceFormula`
  name and delete the legacy `ValenceFormula.lean` (307 LOC) which becomes a redundant
  proof of the same theorem; this is the final cleanup once D1 is reviewed.

### Ticket E — `FM` suffix removal

- **E1**. `Orbits.lean`: rename `OrbitFM` → `Orbit`, `orbFM` → `orb`,
  `ordOrbitFM` → `ordOrbit`, `oiFM` → `oI`, `orhoFM` → `oRho`, `NonEllOrbitFM` →
  `NonEllOrbit`, etc. Mechanical search-replace. Δ ≈ −0 LOC, +readability.
- **E2**. `OrbitPairing.lean`, `CanonicalReps.lean`: same. Mechanical.

### Ticket F — bridge file: valence → dimension

- **F1**. Create `ForMathlib/DimensionFormulaFromValence.lean` (~30 LOC) deriving
  `ModularForm.dimension_level_one` from `valence_formula_textbook`. Δ ≈ +30 LOC.
- **F2**. Submit the orbifold-counting proof of `dimension_level_one` as an
  upstream mathlib PR. (Out of project scope, but completes the loop.)

### Ticket G — mathlib upstream PRs (extractive)

- **G1**. PR `MeromorphicAt.residue` (extract from `ForMathlib/Residue.lean` —
  ~40 LOC of definitions + circle-integral characterisation). On merge, delete
  `ForMathlib/Residue.lean` and `ForMathlib/ResidueCircleIntegral.lean` (78 LOC).
  Δ ≈ −120 LOC locally (post-merge).
- **G2**. PR the two `UpperHalfPlane.atImInfty` helper lemmas
  (`Filter.eventually_atImInfty`, `qExpansion_ext2`) and the `FunLike (ℍ → ℂ)` instance
  from `Modularforms/AtImInfty.lean`. Δ ≈ −20 LOC.
- **G3**. PR the PSL₂(ℤ) action package from `Modularforms/PSL2Action.lean`
  (`isFundamentalDomain_fdo_PSL` and the surrounding API). This is a substantial
  PR (~200-400 LOC depending on the exact subset chosen) but a natural
  generalisation of `ModularGroup.fd`. Δ ≈ −250 LOC locally (post-merge).

### Ticket H — `/decompose-proof` on the longest proofs

- **H1**. `perCrossing_higherOrder_window_integral_tendsto_corner` (304 LOC) in
  `HungerbuhlerWasem/MultiCrossingCPV.lean:929` — split into 4-5 named auxiliaries.
- **H2**. `perCrossing_window_integral_tendsto_exact` (232 LOC) in
  `HungerbuhlerWasem/LocalCutoffs.lean:747` — same.
- **H3**. The FTC-telescope triple (`ftc_logDeriv_telescope_{i,rho,rho_plus_one}`)
  in `ValenceFormula/WindingWeights/` — extract a shared `ftc_logDeriv_telescope_axis`
  parametric helper, eliminate the per-axis variant bodies. Estimated Δ ≈ −300 LOC.

### Ticket I — `/split-file` on files >1500 lines

- **I1**. `HeckeRIngs/GL2/HeckeT_n.lean` (1937 LOC).
- **I2**. `HeckeRIngs/GL2/AdjointTheory/FDTransport.lean` (1801 LOC).
- **I3**. `HeckeRIngs/GLn/CongruenceHecke/Surjectivity.lean` (1607 LOC).
- **I4**. `ForMathlib/HungerbuhlerWasem/MultiCrossingCPV.lean` (1537 LOC).
- **I5**. `HeckeRIngs/GL2/AdjointTheory/DeltaBSystem.lean` (1524 LOC).
  (No LOC change; structural improvement only.)

### Ticket J — `evalHom_injective` general case

- **J1**. `LeanModularForms/HeckeRIngs/GLn/PolynomialRing.lean:877` contains a
  documented sorry for the general-`n` case of `evalHom_injective`. This is *not*
  the permitted sorry (the permitted one is at `Newforms/MainLemma.lean:152`).
  Either (a) discharge it, or (b) restrict the theorem statement to `n ∈ {1, 2}`,
  or (c) explicitly flag it in the project status as a second permitted sorry.

### Ticket K — `OrbitFM` etc. naming hygiene

Already captured in Ticket E.

### Ticket L — `set_option`/`maxHeartbeats` audit

The audit found **zero** `set_option maxHeartbeats` or `synthInstance.maxHeartbeats`
overrides anywhere in the project. This is a notable quality result and aligns with
the project memory note "maxHeartbeats overrides forbidden". Nothing to do; mark as
clean.

### Ticket M — verify the 6 axiom-clean headlines after structural changes

After each of Tickets A-D lands, re-run `lean_verify` on each of the six protected
headlines:
1. `HeckeRing.GL2.strongMultiplicityOne_constMul`
2. `HeckeRing.GL2.strongMultiplicityOne_axiom_clean`
3. `HeckeRing.GL2.heckeT_p_adjoint`
4. `HeckeRing.GL2.exists_simultaneous_eigenform_basis`
5. `valence_formula_textbook`
6. `LeanModularForms.hw_3_3_clean_full_mero`

All must remain `[propext, Classical.choice, Quot.sound]`.

### Summary table

| Ticket | Δ LOC | Risk | Order |
|--------|-------|------|-------|
| A — single CPV | −1,750 | Medium | 1 |
| B — single PwC1 family | −80 | Low | 2 (after A) |
| C — single boundary param | −600 | Medium | 3 (after A) |
| D — collapse façades | −400 | Low | 4 (after A, C) |
| E — `FM` suffix removal | 0 | None | any |
| F — valence→dim bridge | +30 | None | any |
| G — upstream PRs | (long-term) | None locally | any |
| H — `/decompose-proof` | −300 | Low | any |
| I — `/split-file` | 0 | None | any |
| J — `evalHom_injective` general | TBD | Math-research | any |
| L — `set_option` audit | done | n/a | done |
| **Cumulative project Δ** | **≈ −3,100 LOC (≈ 3.8 %)** | | |

---

## Appendix: Headline File Map

```
ValenceFormulaFinal.lean (70 LOC)
└── ValenceFormulaBridged.lean (161 LOC)        [uses HasCauchyPVOn directly]
    └── FDWindingDataFullSeg1Seg4.lean
    └── ResidueSideBridge.lean (67 LOC)         [bridge layer — disappears in Tickets A+C]
        └── ResidueSide.lean (101 LOC)          [pulls from ValenceFormula/PVChain/]
        └── FDBoundaryReparametrization.lean (221 LOC) [disappears in Ticket C]
            └── ClassicalCPV.lean (192 LOC)      [disappears in Tickets A+B]

HW33Clean.lean (82 LOC)
└── HungerbuhlerWasem/MultiCrossingCPV.lean (1537 LOC)
    └── HungerbuhlerWasem/{LocalCutoffs, Crossing, LaurentExtraction, MultiPoleDCT, ...}

StrongMultiplicityOneFull.lean (1284 LOC)
└── DescentCosets, Lemma4_6_14, Lemma4_6_8, Miyake465, MiyakeDescend, LevelCommute, SquarefreeDecomp

heckeT_p_adjoint  in  AdjointTheory/ConcreteFamily.lean (697 LOC)
exists_simultaneous_eigenform_basis  in  AdjointTheoryPetersson.lean (847 LOC)
└── AdjointTheory/{FDTransport, DeltaBSystem, SummandAdjoint, ConcreteFamily}
```
