# Step 5 — Moral Duplication Detection: PadicLFunctions

Scope: find declarations that are *morally the same* and should be unified, both
**within the project** and **vs mathlib**. Two structural leads were investigated
in depth: the `Measure/` vs `MeasureR/` parallel tracks, and the `X` vs `XComplex`
pairs.

Search basis: project inventory (`.mathlib-quality/overview/inventory/*.md`) + the
Lean sources + `WebSearch "mathlib4 <concept>"`. No local build, so no
`lean_local_search`/`lean_goal`; mathlib facts are from the docs + the
"Formalizing zeta and L-functions in Lean" paper (arXiv:2503.00959) and
`Mathlib.NumberTheory.Padics.MahlerBasis`.

---

## Headline verdicts

- **Measure vs MeasureR: KEEP BOTH (special-case), do NOT merge into one file.**
  `MeasureR` is the coefficient-general `R := integerRing K` version; `Measure` is
  the `R := ℤ_p` instance. They are *not* dead duplicates — `MeasureR` already
  **reuses** the entire space-side topology layer from `Measure` (it imports and
  cites `PadicMeasure.unitsValCM`, `isClopen_units`, `isClopen_pZp`, `unitsHomeo`,
  `shiftDiv`, `digit`, `mulCM`, `unitsMulCM₂`, `mul_choose_eq`, `mem_pZp_of_mul`,
  `mul_shiftDiv_of_mem`, `shiftDiv_mul`, `fwdDiff_iter_mahler_zero`,
  `exists_locallyConstant_norm_sub_le'`), and the two tracks are bridged by the
  `baseChange : Λ(ℤ_p) →+* Λ_R(ℤ_p)` ring hom (`MeasureR/BaseChange.lean`). What is
  duplicated is only the *measure-valued* layer (the `→ₗ`/`→+*` structures
  parametrised by the coefficient ring), because `ℤ_p` and `integerRing K` are
  genuinely different carrier types and Lean cannot share the bundled maps for
  free without a typeclass refactor. The biggest available win is **collapsing the
  `ℤ_p` track to `R := ℤ_p` specialisations of the `MeasureR` track** (or, less
  invasively, golfing the duplicated proofs to *cite* the general one). See the
  "Measure/MeasureR action list" below.
- **\*Complex pairs: KEEP BOTH.** Each `XComplex` file is a deliberately
  **quarantined complex-analysis bridge** that proves the project's
  self-contained, char-zero/p-adic object (`genBernoulli`, `zetaNeg`, `LvalNeg`,
  `rjwEisenstein`, …) equals mathlib's transcendental `LFunction` / `riemannZeta` /
  `HurwitzZeta`. They share a *definition* but the `Complex` theorem is a genuinely
  different statement (an analytic-continuation identity). Isolation keeps the
  p-adic chain free of `Mathlib.NumberTheory.LSeries.*` imports — a feature, not
  redundancy. No shared *lemma* is duplicated across an `X`/`XComplex` boundary.
- **vs mathlib: NO file is a duplicate of mathlib.** mathlib supplies the
  primitives the project builds on (`mahler`, `hasSum_mahler`, `fwdDiff`,
  `LFunction`, `riemannZeta_neg_nat_eq_bernoulli`, `hurwitzZeta_neg_nat`,
  `gaussSum`, `bernoulli`) but has **no** p-adic-measure / Iwasawa-algebra /
  Mahler-transform layer and **no** `genBernoulli`. Two decls are *upstreamable*
  (mathlib-PR candidates), not mathlib dups: `exists_locallyConstant_norm_sub_le'`
  and `DirichletCharacter.genBernoulli` (+ its API).

Counts: **UNIFY (intra-project): 1 hard + ~12 special-case collapses across the 6
Measure⇄MeasureR file-pairs. DUP-OF-MATHLIB: 0. mathlib-PR candidates: 2.
keep-both: the 4 \*Complex pairs + the 3 MeasureR-only files.**

---

## REQUIRED pairwise table

`Same statement?` = same up to the coefficient-ring substitution `ℤ_p ↔ integerRing K`
(or, for mathlib rows, same mathematical content). `Same proof?` = same tactic
skeleton.

### A. Measure ⇄ MeasureR — file-pair: Basic

| Decl A (Measure/PadicMeasure) | Decl B (MeasureR) | Same statement? | Same proof? | Verdict |
|---|---|---|---|---|
| `PadicMeasure` (abbrev) | `MeasureR` (abbrev) | yes (`ℤ_p`→`integerRing K`) | n/a (abbrev) | special-case (B generalises A) |
| `dirac` | `dirac` | yes | yes (`rfl` fields) | special-case |
| `dirac_apply` | `dirac_apply` | yes | yes (`rfl`) | special-case |
| `compRight` | `compRight` | yes | yes (`ext; simp`) | special-case |
| `compRight_apply` | `compRight_apply` | yes | yes (`rfl`) | special-case |
| `pushforward` | `pushforward` | yes | yes (`rfl`) | special-case |
| `pushforward_apply` | `pushforward_apply` | yes | yes (`rfl`) | special-case |
| `pushforward_dirac` | `pushforward_dirac` | yes | yes (`rfl`) | special-case |
| `norm_apply_le` | `norm_apply_le` | yes (operator norm ≤ 1) | ~yes (max-on argument; A uses `valuation`/`p^n` scaling, B uses `f x₀ • g`) | special-case (proofs differ slightly; A is the `ℤ_p`-specific norm computation) |
| `continuous` | `continuous` | yes | yes (`LipschitzWith 1`) | special-case |
| `exists_locallyConstant_norm_sub_le` (in Measure/Basic) | — (B reuses `PadicMeasure.exists_locallyConstant_norm_sub_le'`) | A is `ℤ_p`-valued; the general `E`-valued `'` version lives in Measure/Fubini | — | see Fubini row: the general lemma already serves both |
| `ext_locallyConstant` | `ext_locallyConstant` | yes | yes (both call `…exists_locallyConstant_norm_sub_le'` + `norm_add_le_max`) | special-case — **B already imports A's helper** |
| — | `charFnCM`, `charFnCM_apply` | B-only (clopen indicator over `R`); A uses `LocallyConstant.charFn` inline | — | keep-both (minor: could add `charFnCM` to the `ℤ_p` layer too) |

### B. Measure ⇄ MeasureR — file-pair: MahlerTransform

| Decl A | Decl B | Same statement? | Same proof? | Verdict |
|---|---|---|---|---|
| `mahlerCoeff` / `mahler n` use | `mahlerCM` (`algebraMap ∘ mahler n`) | A integrand is `mahler n`; B pushes it through `algebraMap ℤ_p→R` | — | special-case (B = A base-changed; see `algCM_mahler : algCM K (mahler n) = mahlerCM` which makes this *literally `rfl`*) |
| `mahlerTransform` | `mahlerTransform` | yes | yes (`PowerSeries.mk`) | special-case |
| `coeff_mahlerTransform` | `coeff_mahlerTransform` | yes | yes (`simp`) | special-case |
| `mahlerTransformₗ` | `mahlerTransformₗ` | yes | yes | special-case |
| `apply_eq_tsum` | `apply_eq_tsum` | yes | yes (`hasSum_mahler`+`HasSum.map`) | special-case |
| `mahlerTransform_dirac` | `mahlerTransform_dirac` | yes (B has extra `PowerSeries.map`) | yes (coeff `ext`) | special-case |
| `mahlerTransform_injective` | `mahlerTransform_injective` | yes | yes (`apply_eq_tsum`+`tsum_congr`) | special-case |
| `summable_fwdDiff_mul` | `summable_fwdDiff_mul` | yes (norm ≤ 1 of coeffs) | yes (`squeeze_zero`) | special-case |
| `ofPowerSeries` | `ofPowerSeries` | yes | yes | special-case |
| `fwdDiff_iter_mahler_zero` | `fwdDiff_iter_mahlerCM_zero` | B = A transported via `algebraMap` | B **calls** `PadicMeasure.fwdDiff_iter_mahler_zero` | special-case — **B already reuses A** |
| `mahlerTransform_ofPowerSeries` | `mahlerTransform_ofPowerSeries` | yes | yes (Kronecker collapse) | special-case |
| `mahlerLinearEquiv` (+`_apply`,`_symm_apply`) | `mahlerLinearEquiv` (+`_apply`,`_symm_apply`) | yes | yes | special-case |
| — | `mahlerTerm_eq`, `mahlerTransform_smul`, `mahlerTransform_sub` | B-only convenience | — | keep-both |

### C. Measure ⇄ MeasureR — file-pair: Convolution

| Decl A | Decl B | Same statement? | Same proof? | Verdict |
|---|---|---|---|---|
| `Mul`, `One` instances | `Mul`, `One` instances | yes | yes (transport via `mahlerLinearEquiv`) | special-case |
| `mul_def`, `one_def` | `mul_def`, `one_def` | yes | yes (`rfl`) | special-case |
| `mahlerTransform_mul`/`_one`/`_add`/`_zero` | same four | yes | yes | special-case |
| `CommRing` instance | `CommRing` instance | yes | yes (8 fields via `mahlerTransform_injective`) | special-case |
| `mahlerRingEquiv` | `mahlerRingEquiv` | yes (RJW Thm 3.20) | yes | special-case |
| `convInner` / `convInner_apply` | `convInner` / `convInner_apply` | yes | yes | special-case |
| `mul_apply` | `mul_apply` | yes (convolution formula, Chu–Vandermonde) | yes (`Ring.add_choose_eq`) | special-case |
| `dirac_mul_dirac` | `dirac_mul_dirac` | yes | yes (`binomialSeries_add`) | special-case |

### D. Measure ⇄ MeasureR — file-pair: Fubini

| Decl A | Decl B | Same statement? | Same proof? | Verdict |
|---|---|---|---|---|
| `innerInt` (+ 5 `innerInt_*` simp lemmas) | `innerInt` (+ same 5) | yes | yes | special-case |
| `exists_locallyConstant_norm_sub_le'` (general `E`-valued) | — (none) | **B reuses A** (`MeasureR/Fubini.integral_swap` calls `PadicMeasure.exists_locallyConstant_norm_sub_le'`) | — | **NOT duplicated** — single general lemma, already shared; mathlib-PR candidate |
| `integral_swap` | `integral_swap` | yes (Fubini) | yes (ε-approx, `charFn` fibres, `dist_triangle_max`) | special-case — both ~100+ line proofs, the largest duplicated cost |

### E. Measure ⇄ MeasureR — file-pair: Toolbox

| Decl A | Decl B | Same statement? | Same proof? | Verdict |
|---|---|---|---|---|
| `cmul` / `cmul_apply` | `cmul` / `cmul_apply` | yes | yes | special-case |
| `del` / `coeff_del` | `del` / `coeff_del` | yes | yes | special-case |
| `mahlerTransform_cmul_X` | `mahlerTransform_cmul_X` | yes (RJW Lem 3.24) | yes; **B reuses `PadicMeasure.mul_choose_eq`** | special-case |
| `powCM` / `powCM_apply` | `powCM` / `powCM_apply` | yes (B via `algebraMap`) | yes | special-case |
| `apply_powCM` | `apply_powCM` | yes (RJW Cor 3.25) | yes | special-case |
| `res` / `IsSupportedOn` | `res` / `IsSupportedOn` | yes | yes | special-case |
| `sigma`, `phi` | `sigma`, `phi` | yes | yes; **B reuses `PadicMeasure.mulCM`** | special-case |
| `psi` | `psi` | yes | yes; **B reuses `PadicMeasure.isClopen_pZp`, `shiftDiv`** | special-case |
| `psi_phi`, `phi_psi`, `res_units_eq` | same | yes | yes; **B reuses `mem_pZp_of_mul`, `mul_shiftDiv_of_mem`, `shiftDiv_mul`, `isClopen_units`** | special-case |
| `isSupportedOn_units_iff_psi_eq_zero` | same | yes (RJW Cor 3.32) | yes | special-case |
| `mahlerTransform_pushforward_mulCM`, `mahlerTransform_sigma`, `mahlerTransform_phi`, `binomialSeries_mul_nat`, `mul_choose_eq` | — (A-only) | A-only (substitution-into-binomial-series machinery) | — | keep-both (A is reused by B) |
| `digit`, `shiftDiv`, `shiftDiv_mul`, `isClopen_pZp`, `mem_pZp_of_mul`, `mul_shiftDiv_of_mem`, `isClopen_units`, `setOf_isUnit_eq`, `sub_digit_mem_span`, `shiftDiv_mem` | — (A-only) | A-only **space-side** gadgets | — | keep-both — **these are the shared base B imports; correct design** |
| — | `psi_add`/`_smul`/`_zero`/`_sum`/`_dirac_zero`/`_dirac_of_isUnit`, `phi_apply_powCM`, `psi_phi_mul` | B-only `ψ`-linearity API + projection formula | — | keep-both (B needs these for §5; A could gain `psi_sub` symmetry but no dup) |
| `isClopen_units` (`heq` block) | `setOf_isUnit_eq` | **identical statement+proof, intra-file** | **identical** | **UNIFY (hard) — see #1 below** |

### F. Measure ⇄ MeasureR — file-pair: UnitsZp

| Decl A | Decl B | Same statement? | Same proof? | Verdict |
|---|---|---|---|---|
| `unitsValCM`, `unitsHomeo`, `isClosed_range_embedProduct`, `CompactSpace ℤ_pˣ`, 2×`TotallyDisconnectedSpace` | — (A-only) | A-only space-side gadgets | — | keep-both — **B imports these, no dup** |
| `extendByZero` | `extendByZero` | yes | yes (clopen-units continuity) | special-case |
| `extendByZero_coe_unit` | `extendByZero_coe_unit` | yes | yes | special-case |
| `iota` | `iota` | yes (pushforward along `unitsValCM`) | yes; **B reuses `PadicMeasure.unitsValCM`** | special-case |
| `extendByZero_comp_val` | `extendByZero_comp_val` | yes | yes | special-case |
| `iota_injective` | `iota_injective` | yes | yes | special-case |
| `res_iota` | `res_iota` | yes | yes; **B reuses `isClopen_units`** | special-case |
| `extendByZero_comp_unitsVal` | `extendByZero_comp_unitsVal` | yes | yes | special-case |
| `mem_range_iota_iff` | `mem_range_iota_iff` | yes (RJW Rem 3.33) | yes | special-case |

### G. MeasureR-only files (no Measure twin)

| File | Status | Verdict |
|---|---|---|
| `MeasureR/BaseChange.lean` (`baseChange`, `algCM`, `baseChange_algCM`, `baseChange_cmul`, `baseChange_res`, …) | the **bridge** `Λ(ℤ_p)→Λ_R(ℤ_p)`; pure glue between the two tracks | keep — *this is the artifact that makes "keep both" coherent* |
| `MeasureR/UnitsRing.lean` (`unitsConv`, `deg`, `Mul/One/CommRing` on `MeasureR K ℤ_pˣ`) | units-convolution ring; the `ℤ_p` track never built `Λ(ℤ_pˣ)` as a ring | keep-both (no Measure counterpart) |
| `MeasureR/FormalPsi.lean` (`phiSeries`, `psiSeries`, digit decomp, `seriesEval`, `Eqphipsi`) | formal-power-series avatar of `ψ`; consumed by `ValuesAtOne`, `Coleman/NormOperator` | keep (no Measure counterpart) |
| `Measure/PseudoMeasure.lean` (1061 lines) | the **`ℤ_p`-only** pseudo-measure layer; consumed by `KubotaLeopoldt/MuA`, `Iwasawa/PlusPart` | keep (no MeasureR counterpart) |

### H. `X` ⇄ `XComplex` pairs

| Decl A (X) | Decl B (XComplex) | Same statement? | Same proof? | Verdict |
|---|---|---|---|---|
| `DirichletCharacter.genBernoulli` (def, field `L`) | `LFunction_neg_nat` (GenBernoulliComplex) | **no** — A defines `B_{k,χ}`; B proves `LFunction χ (−k) = −B_{k+1,χ}/(k+1)` | no | keep-both (B *consumes* A's def + `genBernoulli_eq_zmod_sum` + `hurwitzZeta_neg_nat_of_mem_Ioo`) |
| `zetaNeg` (def, `ℚ`) | `zetaNeg_eq_riemannZeta` (ZetaValuesComplex) | **no** — A is a `ℚ` def; B proves `(zetaNeg k : ℂ) = riemannZeta (−k)` | no | keep-both (deliberate complex-analysis quarantine) |
| `ValuesAtOne.*` (`LpFunction_one`, p-adic `L_p(θ,1)`, over `K`) | `ValuesAtOneComplex.*` (`LFunction_one_eq`, classical `L(θ,1)`) | **no** — distinct objects (p-adic vs complex value); RJW Thm 6.1(ii) vs 6.1(i) | no | keep-both — **both needed for the interpolation theorem** |
| `EisensteinFamily.*` (p-adic Eisenstein family / measure side) | `EisensteinComplex.*` (`stabilisedEisenstein`, q-expansion, `Γ₀(p)`-modularity) | **no** — complex modular-form realisation vs p-adic family | no | keep-both |

No lemma is duplicated *across* an `X`/`XComplex` boundary; the only shared symbol
is the def (`genBernoulli`, `zetaNeg`) which the Complex side correctly imports
rather than re-states.

### I. vs mathlib

| Project decl | mathlib | Same statement? | Same proof? | Verdict |
|---|---|---|---|---|
| `PadicMeasure` / `MeasureR` and the whole measure/Iwasawa-algebra/Mahler-transform layer | — (mathlib has `MahlerBasis`: `mahler`, `hasSum_mahler`, `fwdDiff`; **no** measure/Iwasawa layer) | no | no | **NOT a dup** — builds on mathlib primitives |
| `exists_locallyConstant_norm_sub_le'` (Measure/Fubini; general ultrametric `E`) | mathlib `exists_locallyConstant_norm_sub_le` (ℤ_p only) | generalises it | similar | **mathlib-PR candidate** (already flagged in docstring) — keep, upstream |
| `DirichletCharacter.genBernoulli` + `genBernoulli_eq_zero`, `genBernoulliPowerSeries_mul` | — (mathlib has `bernoulli`, `bernoulli'`, `bernoulliPowerSeries_mul_exp_sub_one`, but **no** generalised `B_{k,χ}`) | no | n/a | **mathlib-PR candidate**, not a dup |
| `zetaNeg` / `zetaNeg_eq_riemannZeta` | mathlib `riemannZeta_neg_nat_eq_bernoulli` | B *re-expresses* a mathlib fact in project terms | uses it | keep (thin project wrapper; not worth upstreaming) |
| `LFunction_neg_nat`, `LFunction_one_eq`, `gaussSum_mul_coprime` | mathlib `LFunction`, `hurwitzZeta_neg_nat`, `gaussSum*` | project-specific corollaries | consume mathlib | keep (genuine new results / not in mathlib) |

---

## Prose action list

### 1. UNIFY (hard, intra-file) — `setOf_isUnit_eq` vs `isClopen_units`
In `PadicLFunctions/Measure/Toolbox.lean`, `setOf_isUnit_eq` (lines 410–416) is a
**byte-for-byte copy** of the `heq` block inside `isClopen_units` (lines 403–406):
both prove `{x : ℤ_[p] | IsUnit x} = {x | ‖x‖ < 1}ᶜ` with the identical
`ext x; simp only […]; exact ⟨fun h => h.ge, fun h => le_antisymm (PadicInt.norm_le_one x) h⟩`.
**Action:** keep `setOf_isUnit_eq` as the named lemma and rewrite `isClopen_units`
as `by rw [setOf_isUnit_eq]; exact (isClopen_pZp p).compl`. (Also note
`setOf_isUnit_eq` carries a copy-pasted wrong docstring — it is captioned
"`Res_{ℤ_p^×} = 1 − φ∘ψ` … RJW 1152–1154", which belongs to `res_units_eq`.)
This is the one unconditional, no-risk dedup.

### 2. Collapse the `ℤ_p` Measure track onto `R := ℤ_p` of MeasureR (the big structural call)
The 6 file-pairs (Basic, MahlerTransform, Convolution, Fubini, Toolbox, UnitsZp)
re-prove the *same measure-valued API* twice. The `MeasureR` track is strictly
more general (`integerRing K ⊇ ℤ_p` as the `K := ℚ_p` instance, where
`integerRing ℚ_p ≅ ℤ_p`). Three options, in increasing ambition:
  - **(a) Minimal, safe:** golf each duplicated `ℤ_p` proof to *cite* its general
    twin where a `rfl`/defeq bridge exists. The inventory already shows several
    cross-track reuses work (`fwdDiff_iter_mahlerCM_zero` calls
    `PadicMeasure.fwdDiff_iter_mahler_zero`; `MeasureR` Toolbox/UnitsZp call the
    `PadicMeasure` space-side gadgets; both `ext_locallyConstant`s share
    `exists_locallyConstant_norm_sub_le'`). The duplicated *measure-layer* proofs
    (norm_apply_le, integral_swap ~100 lines, mul_apply ~36–41 lines, the CommRing
    instances) are the costly ones to keep in sync.
  - **(b) Medium:** define the `ℤ_p` API as `abbrev`/`def` wrappers around the
    `MeasureR ℚ_p` instances via the `integerRing ℚ_p ≅ ℤ_p` identification, deleting
    the duplicated proofs. Risk: the carrier `ℤ_p` vs `integerRing ℚ_p` defeq gap may
    force `RingEquiv` transport at every `simp`/`rfl` site downstream (`PseudoMeasure`,
    `Coleman`, `KubotaLeopoldt`, `Iwasawa` all build on `PadicMeasure`).
  - **(c) Maximal:** delete `Measure/{Basic,MahlerTransform,Convolution,Fubini,
    Toolbox,UnitsZp}` and repoint downstream to `MeasureR (K := ℚ_p)`. This is a
    large refactor touching `PseudoMeasure` (1061 lines) and every `PadicMeasure.*`
    consumer; **do NOT auto-apply — needs human sign-off** (it changes the public
    API surface the producer relies on, and the `ℤ_p`-specific `norm_apply_le`
    proof is genuinely simpler than the general one). Recommend (a) now, file (b)/(c)
    as a tracked decision.

**Recommendation:** keep both tracks (special-case), do (a), and flag (b)/(c) for
the producer. The presence of `baseChange` shows the author already chose the
"two tracks + explicit bridge" design intentionally.

### 3. Upstream the two mathlib-PR candidates (not dups, but they leave the project)
  - `Measure/Fubini.exists_locallyConstant_norm_sub_le'` — generalises mathlib's
    `exists_locallyConstant_norm_sub_le` from `ℤ_p` to any ultrametric seminormed
    `E`; already self-flagged. PR to `Mathlib.Topology.LocallyConstant.*`.
  - `DirichletCharacter.genBernoulli` + `genBernoulli_eq_zmod_sum` +
    `genBernoulliPowerSeries_mul` + `genBernoulli_eq_zero` — generalised Bernoulli
    numbers are absent from mathlib (confirmed via arXiv:2503.00959 zeta/L-function
    formalization survey). Strong PR candidate to `Mathlib.NumberTheory.Bernoulli`.
  Until upstreamed, these are correct project code, **not** intra-project dups.

### 4. \*Complex pairs — keep all four, no action
`GenBernoulli`/`GenBernoulliComplex`, `ZetaValues`/`ZetaValuesComplex`,
`ValuesAtOne`/`ValuesAtOneComplex`, `EisensteinFamily`/`EisensteinComplex` are p-adic
vs complex-analytic versions, **both required** for the interpolation statement
(the complex side pins the special L-values that the p-adic measure interpolates).
The `Complex` files are an import firewall (no `LSeries`/`riemannZeta` in the p-adic
chain). No shared lemma is duplicated; the only shared symbols are defs the Complex
side imports. Leave as is.

### 5. Minor consistency nits (optional, low value)
  - `charFnCM` (clopen indicator over `R`) exists only in the `MeasureR` Basic
    layer; the `ℤ_p` track uses mathlib `LocallyConstant.charFn` inline. Harmless;
    adding a `ℤ_p` `charFnCM` would only matter under action #2(c).
  - `psi_sub` exists on both tracks but `psi_add`/`_smul`/`_zero`/`_sum` are
    `MeasureR`-only. Not a dup; if the `ℤ_p` track ever needs them, lift from the
    general proofs rather than re-deriving.

---

## Top 5 (priority order)

1. **`setOf_isUnit_eq` ⇄ `isClopen_units` (Measure/Toolbox)** — hard intra-file
   duplicate (identical statement + proof); UNIFY now, also fix the wrong docstring.
2. **Measure ⇄ MeasureR measure-layer** — ~12 special-case re-derivations across 6
   file-pairs; the *largest* duplicated cost is the twin `integral_swap` (~100 lines
   each) and the twin `CommRing`/`mul_apply` proofs. Decide (a)/(b)/(c) — recommend
   (a) + producer sign-off; this is the project's dominant structural redundancy.
3. **`exists_locallyConstant_norm_sub_le'`** — single general lemma already shared
   across both tracks (not duplicated); upstream to mathlib.
4. **`DirichletCharacter.genBernoulli` (+API)** — generalised Bernoulli numbers
   missing from mathlib; upstream candidate, not a dup.
5. **\*Complex quarantine pairs** — confirm keep-both; document that the
   `X`/`XComplex` split is an intentional import firewall so future cleaners do not
   try to merge them.

---

Output path:
`/Users/mcu22seu/Documents/GitHub/aintlib-main/projects/PadicLFunctions/.mathlib-quality/overview/analysis/05-duplications.md`
