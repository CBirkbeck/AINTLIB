# PadicLFunctions — Steps 7+8: API Design + Junk Identification

Scope: p-adic measures (`Measure/`, `MeasureR/`), Mahler/Amice transform, convolution
(Iwasawa-algebra) ring, generalised-Bernoulli / Kubota–Leopoldt L-function machinery,
pseudo-measures, and the IwasawaProof / ResidueZeta / ValuesAtOne downstream. Read-only over the
inventory + source; no local build.

Two headline structural facts drive most findings:

- **`integerRing L` is the norm-unit-ball `Subring L`** (`{x | ‖x‖ ≤ 1}`), *not* a mathlib valuation
  subring, and there is a bespoke `Algebra ℤ_[p] (integerRing L)`. For `L = ℚ_[p]`,
  `integerRing ℚ_[p]` is **iso but not defeq** to `ℤ_[p]` (distinct mathlib type). So the
  `MeasureR` (coefficient-general, over `integerRing K`) track does **not** specialise to the
  `Measure` (`ℤ_[p]`-coefficient) track by plugging `K = ℚ_[p]`; you would land on `integerRing ℚ_[p]`,
  needing a transport across the iso.
- **`MeasureR/` is the strict generalisation** of `Measure/` and already **re-uses** the `ℤ_p`-layer's
  *space-side* scaffolding (`PadicMeasure.unitsValCM`, `isClopen_units`, `isClopen_pZp`, `shiftDiv`,
  `digit`, `mulCM`, `mahler`-zero deltas, `exists_locallyConstant_norm_sub_le'`). It re-derives only the
  *algebraic* API (Mahler transform, convolution ring, Fubini, ψ/φ toolbox). Both tracks are **live**
  downstream (see §B0), so neither can simply be deleted — but the algebraic duplication is the single
  biggest cleanup lever and is **redundant-on-unify** (§B0).

---

## A. API Improvements

### A1. Extract the operator `∂ = (1+T)·d/dT` once, project-wide (highest impact)

`(1 + PowerSeries.X) * F.derivativeFun` is the single most-repeated expression in the project. It is:
- a named `def` **three** times: `Measure.Toolbox.del` (`ℤ_[p]`), `MeasureR.Toolbox.del` (`integerRing K`),
  `KubotaLeopoldt.MuA.delQ` (`ℚ_[p]`); and
- written **inline ≳40 times** across `ResidueZeta` (≈9×), `ValuesAtOne` (≈9×), `IwasawaProof/LogDerivative`
  (≈12×), `IwasawaProof/GaloisAction`, `IwasawaProof/FundamentalSequence`, `IwasawaProof/Equivariance`,
  `Coleman/Map`, `Coleman/ColContinuity`, `Interpolation/TameConductor`, `MeasureR/FormalPsi`.

**Proposal:** one polymorphic `PadicLFunctions.delOp {R} [CommRing R] (F : PowerSeries R) := (1 + X) * F.derivativeFun`
in `Coefficients` (or a new `Common/PowerSeriesDeriv.lean`), with its coefficient lemma
`coeff_delOp` (currently `coeff_del` is proven privately in *both* `Measure.Toolbox` and `MeasureR.Toolbox`),
`map_delOp` (the "`map f` commutes with `∂`" lemma is reproven in `MuA.map_del`, `ValuesAtOne` ll.326–327,
`ResidueZeta` ll.671–672 — at least 3×), and the commutation `one_add_mul_derivative_phiSeries`
(`∂φ = p·φ∂`, currently `FormalPsi`-only). `del`, `delQ` then become one-line specialisations or are deleted.
This removes 3 def-duplicates + ~3 `coeff_del`/`map_del` duplicates and de-noises ~40 inline call-sites.

### A2. `mahlerTransform` (anti-)homomorphism lemmas are scattered re-proofs of `map_*`

`mahlerTransformₗ` / `mahlerLinearEquiv` / `mahlerRingEquiv` are bundled (anti)homs, so additivity /
scalar / subtraction / sum / mul of the *unbundled* `mahlerTransform` should come from `map_add`,
`map_smul`, `map_sub`, `map_sum`, `map_mul` of the bundle. Instead:
- `mahlerTransform_sub`, `mahlerTransform_smul` are **independently restated** in `KubotaLeopoldt.MuA`
  (ll.108–116) *and* `MeasureR.MahlerTransform` (ll.196–207) — all are one-liners `map_sub/​map_smul (… ₗ)`.
- `mahlerTransform_add` / `_zero` are restated in both `Measure.Convolution` and `MeasureR.Convolution`.
- a `private mahlerTransform_sum` (just `map_sum (…ₗ)`) is duplicated in `MeasureR/FormalPsi` (l.434) and
  `IwasawaProof/FundamentalSequence` (l.67).

**Proposal:** provide the `@[simp]` set `mahlerTransform_add/_sub/_smul/_zero/_sum/_mul` **once per track**
next to the `…ₗ`/`…RingEquiv` definition, each proved by the corresponding `map_*`, and delete the MuA /
FormalPsi / FundamentalSequence restatements (they are `REPLACE`d in §B). A measure-algebra `simp`-normal
form ("push `mahlerTransform` through every ring/​module op") would also shorten the `CommRing` instance
proofs (each currently lists the lemmas by hand).

### A3. ψ is additive/​linear "for free" but restated as 5–6 lemmas in three places

`psi` underlies a `LinearMap`, so `psi_add/_sub/_smul/_zero/_sum` are all `LinearMap.ext` + `…_apply`
one-liners. They are written out **three times**: `KubotaLeopoldt.MuA` (ll.415–429), `MeasureR.Toolbox`
(ll.235–259), `Measure.Toolbox` (`psi_sub`, l.441). If `psi`/`phi` were packaged as the `…ₗ` `LinearMap`
they already (almost) are — e.g. expose `psiₗ : MeasureR K X →ₗ MeasureR K X` — these five collapse to
`map_add`/`map_sub`/`map_smul`/`map_zero`/`map_sum` and the per-file copies vanish. Same remark for
`psi_dirac_of_isUnit`, restated in `MuA` (l.405) and `MeasureR.Toolbox` (l.289).

### A4. Missing `RingHom`/`MonoidHom` bundling of `dirac` and the moment maps

- `dirac _ · : X → Measure` is multiplicative on monoids (`dirac_mul_dirac` / `units_dirac_mul_dirac` /
  `conv_dirac_mul_dirac`), additive-to-Dirac under pushforward (`pushforward_dirac`), and unit-preserving
  (`one_def = dirac 0`). Bundling `diracMonoidHom : G →* (Measure …)ˣ`-style (or at least a `MonoidHom` into
  the multiplicative monoid) would let `[a]·[b] = [a+b]` and the telescoping sums in `MuA.psi_muA`,
  `Coleman`, `PseudoMeasure.single_sub_one_mem_span` be `map_mul`/`map_pow`/`map_prod` instead of bespoke
  inductions.
- The moment evaluation `μ ↦ μ (powCM k)` recurs (`apply_powCM`, `phi_apply_powCM`,
  `muA_apply_powCM`, `units_mul_apply_unitsPowCM`); a bundled "k-th moment" additive hom would give
  `phi_apply_powCM` / additivity of moments by `map_*`.

### A5. `baseChange` is the one explicit `Measure ↔ MeasureR` bridge — make it the *only* bridge and complete it

`MeasureR/BaseChange.lean` already gives `baseChange : PadicMeasure p ℤ_[p] →+* MeasureR K ℤ_[p]` with
`baseChange_dirac`, `baseChange_algCM`, `baseChange_cmul`, `baseChange_res`, `mahlerTransform_baseChange`.
This is exactly the API that should let every `ℤ_p`-track *result* be transported to the `MeasureR`-track
(and vice-versa for the `ℚ_p`/`integerRing ℚ_p` iso) instead of re-proving it. Gaps that, if filled, would
let downstream stop re-deriving: `baseChange_pushforward` / `baseChange_sigma` / `baseChange_phi` /
`baseChange_psi` (naturality with the toolbox operators beyond `cmul`/`res`), and `baseChange_mul`
(it is a `RingHom`, so `map_mul` already gives this — just expose it as `@[simp]`). With these,
`MeasureR.Toolbox.psi_phi_mul` could be `baseChange`-transported from `MuA.psi_phi_mul` (§B), etc.

### A6. Promote the three flagged density/​compactness lemmas to mathlib (or to `Common/`)

`Measure/Basic` and `Measure/Fubini` already carry **"PR candidate for mathlib"** docstrings on:
- `exists_locallyConstant_norm_sub_le'` (`Fubini` l.69) — density of locally-constant maps for an
  *arbitrary* ultrametric `SeminormedAddCommGroup` target (generalises mathlib's `ℤ_[p]`-only version);
- `LocallyConstant.exists_eq_comp_toZModPow` (`Basic` l.188) — locally-constant on `ℤ_[p]` factors through
  a finite `toZModPow` quotient;
- `CompactSpace ℤ_[p]ˣ` (+ the two `TotallyDisconnectedSpace` instances, `UnitsZp` ll.20–57) — "Not in
  mathlib (verified absent)".

These are general topology with **no project content** and are imported across both tracks. They belong in
mathlib; failing that, hoist to `Common/` so both tracks share one copy (the `ℤ_p`-track copy is already the
shared one — keep it, don't fork).

### A7. Missing `@[simp]`/instances (small, local)

- `Measure.UnitsZp` proves `CompactSpace ℤ_[p]ˣ` etc. as instances but they are listed "unused in file";
  confirm they are actually *found by TC search* downstream (they should be — flagged only to ensure the
  `instance` attribute is present, which the inventory confirms).
- `mahlerTransform_one/_zero/_add/_mul`, `dirac_mul_dirac`, `psi_phi`, `mahlerTransform_smul/_sub` are
  `@[simp]` in one track but the **MuA** restatements duplicate the simp lemmas at the same key — once §B
  removes them, ensure the surviving (general) ones stay `@[simp]`.
- `convInner_apply`, `innerInt_apply`, `charFnCM_apply`, `algCM_apply` are `@[simp]` `rfl`-unfolders — good;
  no gap. `seriesEval_mul` carries `set_option maxHeartbeats 1000000` — a `/decompose-proof` of the
  Cauchy-product step would likely let that be dropped.

### A8. Proof-decomposition backlog (statement-preserving; feeds `/decompose-proof`, not strictly "API")

OVER-50 proofs the inventory already flags (collected here as they block clean re-use): `integral_swap`
(both tracks, ~102–108 ln), `mahlerTransform_pushforward_mulCM` (~57), `CommRing`/`unitsConv CommRing`
instances (`Measure.Convolution`, `PseudoMeasure`, `MeasureR.UnitsRing`, ~55–56), `levelMap` (~89),
`augmentationIdeal_eq_span` (~112), `eq_zero_of_forall_unitsPowCM_eq_zero` (~87), `psi_muA` (~91),
`X_mul_subst_exp_Fa` (~64), `mahlerTransform_phi` (FormalPsi, ~66), `sum_seriesEval_mahlerK` (~87),
plus ResidueZeta/ValuesAtOne/IwasawaProof long proofs. The Chu–Vandermonde block inside `mul_apply`
(both tracks) is the same extractable helper twice.

---

## B. Junk / Removable

Convention: **KEEP** = terminal public export (consumed cross-file or a headline RJW result), leave alone.
**REMOVE** = genuinely dead. **INLINE** = ≤3-mathlib-call wrapper → fold into caller. **REPLACE** = duplicates
mathlib or an existing project decl → delete and reuse. **UNIFY** = redundant-on-Measure/MeasureR-unify
(tracked separately from the dedup pass to avoid double-counting).

### B0. The Measure/ vs MeasureR/ parallel track (UNIFY — flag, do not delete yet)

Per-file the two tracks are **near-isomorphic** (decl-for-decl):

| concept | `Measure/` (ℤ_p) | `MeasureR/` (integerRing K) |
|---|---|---|
| measure type | `PadicMeasure` | `MeasureR` |
| `dirac/compRight/pushforward/(+apply)` | Basic | Basic |
| `norm_apply_le/continuous/ext_locallyConstant` | Basic | Basic |
| Mahler `mahlerCoeff/mahlerTransform(ₗ)/ofPowerSeries/mahlerLinearEquiv` (+ dirac/inj/coeff) | MahlerTransform | MahlerTransform (`mahlerCM`) |
| convolution `Mul/One/CommRing/mahlerRingEquiv/convInner/mul_apply/dirac_mul_dirac` | Convolution | Convolution |
| Fubini `innerInt(+algebra lemmas)/integral_swap` | Fubini | Fubini |
| toolbox `cmul/del/powCM/res/sigma/phi/psi/φψ/ψφ/res_units/isSupported…` | Toolbox | Toolbox |
| units `extendByZero/iota/iota_injective/res_iota/mem_range_iota_iff` | UnitsZp | UnitsZp |

`MeasureR/` is the strict generalisation (set `R = ℤ_[p]`). Because the two tracks have **disjoint live
downstreams** — `Measure/`→ KubotaLeopoldt.MuA, Interpolation.Characters, Iwasawa.PlusPart,
Measure.PseudoMeasure; `MeasureR/`→ Coleman.NormOperator, Interpolation.{Twist,NonTame,TameConductor,
LpFunction}, ValuesAtOne, ResidueZeta, IwasawaProof.FundamentalSequence — **a delete-one-track refactor is
out of scope for cleanup** (it changes statements / needs new transport API). Recommend instead:

1. Pick `MeasureR` as the canonical algebraic layer.
2. Re-express the `Measure/` (`ℤ_p`) algebraic API as `MeasureR`-over-`ℚ_p` **transported through
   `baseChange` / the `integerRing ℚ_[p] ≃ ℤ_[p]` iso** (A5), so the `ℤ_p` lemmas become corollaries rather
   than copies. This is a **dev-ticket-sized** unification, not a fleet cleanup; flag it as such.
3. Keep the *space-side* `ℤ_p` scaffolding shared (already is).

Estimated redundant-on-unify surface: the entire `Measure/{MahlerTransform,Convolution,Fubini,Toolbox,
UnitsZp}` algebraic content (~70 decls) becomes derivable. **Not double-counted** in B1–B5 below.

### B1. REPLACE — `mahlerTransform_sub` / `mahlerTransform_smul` / `mahlerTransform_sum` (bundle-map duplicates)

- `KubotaLeopoldt.MuA.mahlerTransform_sub` (ll.108–111) and `…_smul` (ll.113–116): bodies are literally
  `map_sub (mahlerTransformₗ p) …` / `map_smul …`. **REPLACE** with the `Measure.MahlerTransform` simp lemmas
  (add them there per A2) or inline `map_sub`/`map_smul`. Dead-on-arrival as separate decls.
- `MeasureR.MahlerTransform.mahlerTransform_smul/_sub` (ll.196–207): genuinely the `MeasureR`-track simp
  lemmas — **KEEP** (terminal, `@[simp]`), but note they are the *template* the MuA copies should reuse.
- `MeasureR/FormalPsi.mahlerTransform_sum` (private, l.434) and
  `IwasawaProof/FundamentalSequence.mahlerTransform_sum` (private, l.67): both are `map_sum (…ₗ)`. **REPLACE**
  with a single `@[simp] mahlerTransform_sum` exposed next to `mahlerTransformₗ` (A2); delete both privates.

### B2. REPLACE/UNIFY — `psi_phi_mul` proved twice (~36–38 ln each)

`KubotaLeopoldt.MuA.psi_phi_mul` (ll.360–395, ℤ_p) and `MeasureR.Toolbox.psi_phi_mul` (ll.304–342,
integerRing K) are the **same projection-formula proof** (`ψ(φ(ν)·μ) = ν·ψ(μ)`) carried out independently,
each ~37 lines hinging on `convInner_apply` + `mul_shiftDiv_of_mem` + the ultrametric split. Under the
B0 unification the ℤ_p one is a `baseChange`-corollary of the `MeasureR` one. Until then: **KEEP both**
(each is consumed in its track) but mark as a **UNIFY** pair (one is redundant-on-unify) and a
`/decompose-proof` candidate that should share the extracted "indicator vanishes off `pℤ_p`" helper.

### B3. REPLACE — `psi_*` algebra lemmas (ψ is a LinearMap)

`MuA.{psi_zero,psi_add,psi_smul,psi_sum}` (ll.415–429), `MeasureR.Toolbox.{psi_sub,psi_add,psi_smul,psi_zero,
psi_sum}` (ll.235–259), `Measure.Toolbox.psi_sub` (l.441): all `LinearMap.ext`+`…_apply` boilerplate. After
A3 (expose `psiₗ`), **REPLACE** every one of these with `map_add/_sub/_smul/_zero/_sum`. If `psiₗ` is not
introduced, at minimum **deduplicate**: the ℤ_p set (`MuA`) and the `MeasureR` set (`Toolbox`) should not
*also* be split across `Measure.Toolbox`/`MeasureR.Toolbox` — keep one home per track. `psi_dirac_of_isUnit`
(MuA l.405 vs MeasureR.Toolbox l.289) likewise: keep one per track, REPLACE the other under B0.

### B4. INLINE — trivial `…_def` / `…_apply` `rfl`-restatements that are used 0–1×

These are `rfl` unfolders flagged "unused in file" with no recorded cross-file consumer in the inventory;
where a downstream `simp` can unfold the `def` directly they are removable, else fold into the single caller:

- `Measure.PseudoMeasure`: `conv_mul_def`, `conv_one_def`, `units_mul_def`, `dirac_sub_one_mem_nonZeroDivisors'`
  (l.1034, pure `:= dirac_sub_one_mem_nonZeroDivisors …` delegation) — **INLINE/REMOVE** the delegation;
  `conv_mul_apply`/`units_mul_apply` are `@[simp]` and used → KEEP.
- `MeasureR.UnitsRing`: `units_mul_def`, `units_one_def` (ll.44–53) "unused in file" — INLINE if no external
  use; `units_mul_apply` is `@[simp]` → KEEP.
- `Measure.Basic`/`MeasureR.Basic`: `dirac_apply`, `compRight_apply`, `pushforward_apply`, `pushforward_dirac`
  are `@[simp]` `rfl` — **KEEP** (standard simp-normal-form API even if no in-file user).

### B5. REPLACE — `setOf_isUnit_eq` duplicates the `heq` step inside `isClopen_units`

`Measure.Toolbox.setOf_isUnit_eq` (ll.410–416) reproduces verbatim the sub-proof inside
`isClopen_units` (ll.401–408) and is "unused in file". Either **REPLACE** `isClopen_units`'s inline `heq`
with a call to `setOf_isUnit_eq` (promoting it to genuine shared API) or **REMOVE** `setOf_isUnit_eq` if no
downstream consumer materialises. (Inventory flags this exact dedup.)

### B6. REMOVE/verify — `constantCoeff_iterate_derivativeFun`

`KubotaLeopoldt.MuA.constantCoeff_iterate_derivativeFun` (ll.220–228) is explicitly noted "appears unused in
this file" and has **no recorded cross-file consumer** (the file uses the `delQ` variant
`constantCoeff_iterate_delQ` instead). Candidate **REMOVE** — but verify no external import first
(it is a clean, general `PowerSeries` fact, so it may instead be a **mathlib PR candidate**; if kept, hoist).

### B7. KEEP — terminal public exports (do NOT touch)

The large "unused in file" populations in `Measure.PseudoMeasure`, `MeasureR.{FormalPsi,UnitsRing,Toolbox}`,
`Coefficients`, and the Mahler/Convolution files are **public API consumed cross-file**, confirmed by the
grep of downstream namespace use (KubotaLeopoldt, Interpolation, Coleman, Iwasawa, IwasawaProof, ResidueZeta,
ValuesAtOne all reference `PadicMeasure.*` / `MeasureR.*`). Explicit KEEP list (headline RJW results):
`mahlerRingEquiv`/`mahlerLinearEquiv` (Thm 3.20), `mul_apply` (convolution formula, Rem 3.11),
`dirac_mul_dirac`/`units_dirac_mul_dirac`, `integral_swap` (Fubini), `iota_injective`/`mem_range_iota_iff`
(Rem 3.33), `isSupportedOn_units_iff_psi_eq_zero` (Cor 3.32), the whole pseudo-measure block
(`IsPseudoMeasure`, `isPseudoMeasure_iff_exists`, `augmentationIdeal_eq_span`, `exists_topological_generator`,
`eq_zero_of_forall_unitsPowCM_eq_zero`, `dirac_sub_one_mem_nonZeroDivisors`, Lem 3.36/3.38), `muA` +
`muA_apply_powCM` + `res_units_muA_apply_powCM` (Prop 4.5/4.6/4.8), `psi_muA` (Lem 4.7),
`existsUnique_digits`/`mahlerTransform_psi`/`sum_seriesEval_mahlerK` (W6b realised `Eqphipsi`),
`phiSeries_formalLog`/`formalLog` (T618), `baseChange*` (the bridge), and the `Coefficients` `integerRing`
namespace + the `IsPrimitiveRoot.*` root-of-unity lemmas (W2/W3). All KEEP.

### B8. INLINE candidates among wrappers (≤3 mathlib calls)

- `Measure.Toolbox.mahlerTransform_sigma` (term-mode 1-liner `= mahlerTransform_pushforward_mulCM …`) and
  `mahlerTransform_phi` (~3 ln) — KEEP (named RJW formulas, terminal) but note they are thin specialisations.
- `MeasureR.UnitsRing.deg` `map_one'/map_zero'/map_add' := rfl` — fine; the `map_mul'` field is the real
  content. KEEP.
- `Measure.PseudoMeasure.unitsConv`/`unitsMulCM₂` are `abbrev`s over `conv`/`mulCM₂` — KEEP (they specialise
  a general-monoid construction to `ℤ_[p]ˣ` while preserving the downstream API name verbatim, per the file's
  §11 generalisation note).

---

## C. Counts

- **API suggestions: 8** (A1 delOp unification; A2 mahlerTransform map-bundle simp set; A3 psiₗ bundling;
  A4 dirac/moment hom bundling; A5 complete+route-through `baseChange`; A6 promote 3 mathlib-candidate
  topology lemmas; A7 simp/instance hygiene; A8 decompose-proof backlog).
- **Junk / removable items: ~9 actionable groups** — REPLACE: B1 (`mahlerTransform_sub/_smul/_sum` dups),
  B3 (`psi_*` LinearMap boilerplate, ~11 decls across 3 files), B5 (`setOf_isUnit_eq`); INLINE: B4
  (`…_def`/​delegations, ~6 decls), B8 (thin wrappers, mostly KEEP); REMOVE-after-verify: B6
  (`constantCoeff_iterate_derivativeFun`); UNIFY-flag (not deleted now): B0 (whole Measure-algebraic track,
  ~70 decls redundant-on-unify), B2 (`psi_phi_mul` pair).
- **Genuine junk** (dead/duplicate, safe to REMOVE/REPLACE/INLINE now): ≈ **20 decls** — the MuA
  `mahlerTransform_sub/_smul` (2) + the two private `mahlerTransform_sum` (2) + the duplicated `psi_*`
  algebra lemmas that collapse to `map_*` (~11) + `setOf_isUnit_eq` (1) + the `…_def`/delegation inlines
  (~4) + `constantCoeff_iterate_derivativeFun` (1, pending external-use check).
- **False-positive "unused in file"** (flagged unused by the inventory but are real cross-file public
  exports → KEEP): the **large majority**, ≈ **120+ decls** — essentially every `@[simp]` `…_apply`, every
  headline RJW theorem, the pseudo-measure / digit-decomposition / Bernoulli endpoints, the `Coefficients`
  `integerRing`/root-of-unity API, and the `baseChange` bridge (B7).
- **Redundant-on-unify** (separate axis, not counted as junk): ≈ **70 decls** = the `Measure/` algebraic
  layer recoverable from `MeasureR` + `baseChange` (B0), plus the `psi_phi_mul` ℤ_p copy (B2).

## D. Top 5

1. **A1 — extract `∂ = (1+T)d/dT` once.** Kills 3 `def` duplicates (`del`/`del`/`delQ`) + ~3 `coeff_del`/
   `map_del` reproofs and de-noises ~40 inline `(1+X)*derivativeFun` call-sites across 10 files. Biggest
   readability win, low risk.
2. **B0/A5 — unify the Measure/MeasureR algebraic tracks via `baseChange`.** ~70 decls become corollaries.
   Dev-ticket-sized (statement-touching, needs the `integerRing ℚ_[p] ≃ ℤ_[p]` transport + `baseChange`
   naturality completions), so flag for the owning producer — not a fleet cleanup.
3. **A2+B1 — one `mahlerTransform` map-bundle simp set per track.** Deletes the MuA `_sub/_smul` and both
   private `_sum` duplicates; shortens every `CommRing`/transport proof that hand-lists them.
4. **A3+B3 — bundle `psiₗ`/`phiₗ` and delete the ~11 `psi_*` boilerplate lemmas** spread over `MuA`,
   `MeasureR.Toolbox`, `Measure.Toolbox`.
5. **A6 — PR the 3 already-flagged general lemmas to mathlib** (`exists_locallyConstant_norm_sub_le'`,
   `LocallyConstant.exists_eq_comp_toZModPow`, `CompactSpace ℤ_[p]ˣ` + totally-disconnected instances);
   removes project-maintenance burden and is pure general topology.

Output: `/Users/mcu22seu/Documents/GitHub/aintlib-main/projects/PadicLFunctions/.mathlib-quality/overview/analysis/07-api-and-junk.md`
