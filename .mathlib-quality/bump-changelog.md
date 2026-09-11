# Bump changelog analysis — 2026-09-11

- **Range:** mathlib `e4b72ca0d01c` → `63025c440a76` (550 commits), in two steps on one branch:
  `e4b72ca0d01c` → `8acb872c311a` (2026-09-01, PR #8577, 259 commits — repaired but never built)
  and `8acb872c311a` → `63025c440a76` (2026-09-11, 291 commits).
- **Toolchain:** `leanprover/lean4:v4.34.0-rc2`, unchanged — pin-only bump.
- **Why stacked:** #8577 stalled on its worker's "no local build" gate with the freeze (#8576) up.
  Its repairs (Denumerable import move, `absNorm` `[Infinite S]` local instances, #43027 and
  `deriv_log` renames) are kept verbatim and were audited: the `absNorm` fix is a `local instance`
  after the binders, so the four statements are byte-identical.
- **Sources:** `git log`/`git diff` over the pinned checkout in `.lake/packages/mathlib`
  (authoritative for the range), upstream PR descriptions via the GitHub API, and a full-tree
  `lake build` of `bump-targets.txt` under an RSS watchdog.
- **Coverage:** full tree = 11 library roots + 2 orphan modules (`bump-targets.txt`).

## Whole-branch audit (against `origin/main`, before merge)

- 23 commits; 127 files changed, 516 insertions(+), 536 deletions(-).
- **No added lines contain** `sorry`, `admit`, `axiom`, `maxHeartbeats`, `synthInstance.maxHeartbeats` or `maxRecDepth`.
- **Removed declaration headers:** exactly one, the upstreamed duplicate
  `Algebra.IsStandardSmoothOfRelativeDimension.mvPolynomial` (#39709, identical binders).
- **Added declaration headers:** only `local instance`s — 4× `instInfiniteOfModuleFreeInt` (#42787, from #8577)
  and 7× the restored `CommRing ((R ⋙ forget₂ _ RingCat).obj X)` (#43193; in `WeilPairing/LineVertical`,
  `EllipticCurve/PoleSheafBaseSectionsMul` and `…MulFiltration` the category binder is named `D` to avoid
  clashing with a file-level `C`).
- Repo-wide `sorry` token count (projects + Common): 1023 on `origin/main`, 1023 on the branch.

## Pre-build screens (no breakage)

- All 1096 `Mathlib.*` modules AINTLIB imports still resolve. New deprecated shims (warnings only):
  `Mathlib.Data.Complex.Basic` → `Mathlib.Basic.Complex.Basic`, `Mathlib.Data.Real.Basic` →
  `Mathlib.Basic.Real.Basic` (both since 2026-08-27; 3 + 1 importers).
- ~~No deprecated alias that AINTLIB uses was deleted in the range.~~ **Wrong — screening gap.** The
  pre-build scan only looked at `8acb872c..63025c44` and only matched `alias` on a line *after*
  `@[deprecated]`; mathlib writes `@[deprecated (since := …)] alias X := Y` on one line. #43178
  (`738f2ab17a`, delete February-2026 deprecations) removed `CategoryTheory.inv_hom_id_apply` (→
  `Iso.inv_hom_id_apply`), used by ModularCurves `WeilPairing/FieldComparisonBridge`, which surfaced only in
  round 5. Rescan over the full `e4b72ca0..63025c44` range with single-line matching: 133 deprecated
  aliases deleted; classifying every AINTLIB occurrence (qualified `CategoryTheory.X`, bare `X` not
  preceded by a qualifier) against the round logs, the #8574 exclusion list and the orphan list leaves
  exactly **one** real use — `FieldComparisonBridge` — no further latent breakage.

## Broken names / APIs → mappings

### Build rounds (full tree, RSS watchdog 24 GB/process)

| round | errors | failed modules | notes |
|---|---|---|---|
| r1 | 154 | 42 | pin commit only; lower bound — dependents of failures unbuilt |
| r2 | 81 | 23 | after the 42-file repair; 1272 further modules built OK, all failures in newly-reached modules; 0 watchdog kills |
| r3 | 83 | 17 | after round-2 repairs (23 files, 3 commits); 2869 further modules built OK; 0 watchdog kills; first kernel deterministic timeout (HasseWeil `HasseBound/PoleDivisorFallback` :2412, toolchain unchanged → mathlib-induced) |
| r4 | 47 | 8 | after round-3 repairs (17 files, 4 commits); 3306 further modules built OK; 0 watchdog kills; no timeouts |
| r5 | 24 | 10 | after round-4 repairs (8 files, 3 commits); 3482 further modules built OK; 0 watchdog kills; no timeouts |
| r6 | 29 | 4 | after round-5 repairs (10 files, 1 commit); 3621 further modules built OK; 0 watchdog kills; no timeouts; last failure (`EllipticCurve/PoleSheaf`, 104 s) surfaced only in the final jobs |
| r7 | 24 | 4 | after round-6 repairs (4 files, 3 commits); 3583 further modules built OK; 0 watchdog kills; no timeouts. A first r7 launch was stopped right after starting so that the late `PoleSheaf` fix could land before it; last two failures (`WeilPairing/LineVertical`, `EllipticCurve/PullbackTensorSection`) were `PoleSheaf` dependents reached only in the final jobs |
| r8 | 17 | 2 | after round-7 repairs (4 files, 3 commits); 3615 further modules built OK; 0 watchdog kills; two `whnf` timeouts, both cascades of a missing M6 instance (cleared without any budget) |
| r9 | 3 | 2 | after round-8 repairs (2 files, 1 commit); 0 watchdog kills; no timeouts |
| r10 | **0** | **0** | **green** — `lake build` of the full tree exits 0 (2026-09-11T17:30:35Z); 3620 modules (re)built in this round; 0 watchdog kills |

Round-2 failures were almost entirely the round-1 root causes resurfacing in newly-reached modules
(M1 ×9, M3 ×4, M5 derivative cluster, M6 `Monoidal.tensorObj_map_tmul`, M8, `mapDomain_apply`), which
confirms the learning that a build's error list is a lower bound.

- **M1 — mathlib #43481** `TensorProduct.inductionOn` is now the `@[induction_eliminator]` with only
  `tmul`/`add`; `TensorProduct.induction_on` (with `zero`) is deprecated. Same for
  `IsTensorProduct.inductionOn` / `IsBaseChange.inductionOn`. Symptom: `Invalid alternative name
  'zero'` (30×, 11 files: ModularCurves `ForMathlib/{AmitsurDescent, CoactionCharpoly,
  LocalFlatnessCriterion, InvariantBaseChange, NormBaseChange, CoinvariantsBaseChange,
  FiniteFibrewiseFlat, StandardSmoothStalkDVR, CochainComplexFlatBaseChangeExact, SemilocalBasis}`,
  LeanModularForms `ModularSymbols/ModuleMFinite`). Fix: delete the `| zero =>` alternative (and its
  body). Verified: the 30 deleted lines are exactly the 30 error locations — `| zero =>` cases of
  other eliminators (`Submodule.span_induction`, `Nat`/`Fin`) are untouched. The deprecated
  `TensorProduct.induction_on` keeps its `zero` argument but is no longer `@[elab_as_elim]` (only
  `inductionOn` carries `@[elab_as_elim, induction_eliminator]`), so explicit applications fail even
  though the name still resolves — `refine TensorProduct.induction_on t ?_ ?_ ?_` →
  `refine TensorProduct.inductionOn t ?_ ?_` with the zero bullet removed (`AdicSpaces/AdicCompletionBridge`
  round 1; `AdicSpaces/Wedhorn828` :258 round 3, where the motive stayed `?m`).
- **M3 — mathlib #41427** (`631b214f7c`) `MvPolynomial.coeff` deleted with no deprecation (so dot
  notation resolves to `AddMonoidAlgebra.coeff`). `MvPolynomial.coeff m p` → `p.coeff m` (arguments
  swap; result is a bundled `Finsupp`). `rw [MvPolynomial.coeff, AddMonoidAlgebra.coeff_ofCoeff]`
  → `rw [AddMonoidAlgebra.coeff_ofCoeff]`.
- **M5 — mathlib #43334** (`3c2928f164`) `PowerSeries.derivative` / `MvPowerSeries.pderiv` made the
  ring `R` implicit: `PowerSeries.derivative R f` → `PowerSeries.derivative f`, `d⁄dX R f` →
  `d⁄dX f`. Symptoms: "argument R has type Type but is expected to have type PowerSeries
  (PowerSeries R)", `HAdd ℕ ?⟦X⟧`. Statement-level respellings (argument dropped only, verified by
  word-diff — 26/26 removals directly follow `derivative`/`d⁄dX`): HasseWeil
  `coeff_derivative_mul_dX_eq_sum`, `coeff_10_lhs`, `FormalGroup.dX_at_zero_chain`,
  `FormalGroup.invariantDiff_chain`, `formalSlopeBiv_diag_const`, `formalSlopeBiv_diag_X`,
  `formalSlopeBiv_diag`; PadicLFunctions `derivativeFun_eq` (private); BernoulliRegular
  `deriv_log_mul_one_add_X`, `subst_deriv_log_mul_one_add`.
- **M6 — mathlib #43193** (`7974e751be`) presheaf monoidal structure moved to
  `PresheafOfModulesOfCommRing` (an `abbrev` for `PresheafOfModules (R ⋙ forget₂ _ _)`):
  `PresheafOfModules.Monoidal.tensorObj_map_tmul` → `PresheafOfModulesOfCommRing.Monoidal.tensorObj_map_tmul`;
  `Monoidal.tensorHom_app` → `PresheafOfModulesOfCommRing.tensorHom_app`, now stated with
  `Hom.app'` so `erw` on `.app` no longer matches (dropped; `ModuleCat.MonoidalCategory.tensorHom_tmul`
  suffices). The global `CommRing ((R ⋙ forget₂ CommRingCat RingCat).obj X)` instance was deleted —
  restored as a `local instance` (`inferInstanceAs (CommRing (R.obj X))`) in
  `ModularCurves/ForMathlib/SheafOfModulesMonoidal.lean`; tensor products are now over `S.obj X`, so
  scalars in `TensorProduct.smul_tmul'`/`tmul_smul` need `(show ↑(S.obj (op W)) from r')`.
- **M2 — mathlib #39692** (`a78f66ab84`, `₀` naming convention) the ordered-semiring
  `Finset.prod_le_prod (h0) (h1)` is now `Finset.prod_le_prod₀` and `Finset.prod_le_one (h0) (h1)` is
  `Finset.prod_le_one₀`; the unprimed names now carry the former primed monoid versions (primed kept
  as deprecated aliases). DANGEROUS for a blind sed — sites already on the monoid form still compile.
  Symptom: `Function expected at Finset.prod_le_one fun i x ↦ ?m` / `failed to synthesize Zero ?m`.
  Sites: CebotarevDensity `ZetaProduct` :175, :1206; DedekindResidue `AnalyticControl` :2633, :2643;
  PadicLFunctions `Coefficients` :254.
- **M4 — mathlib #41544** (`b38bb28cde`) `Polynomial.coeff : R[X] → ℕ →₀ R`. Using `coeff` as a
  two-argument function breaks: `apply_ite₂ coeff` → `apply_ite₂ (coeff · ·)` (upstream's own fix in
  `DivisionPolynomial/Degree.lean`) — LutzNagell `DivisionPolynomialDegree` :223, :225, :339, :412, :413.
- **M7 — mathlib #42787** (`52d7ff78d7`) `Ideal.absNorm` needs `[Infinite S]`. For `𝓞 K` the bridge
  `CharZero.infinite` lives in `Mathlib.Algebra.CharZero.Infinite`, which is not in every
  `NumberField.Basic` closure: `public import Mathlib.Algebra.CharZero.Infinite` in BernoulliRegular
  `Furtwaengler/PthSymbolNoncanonical`. (Generic `[Module.Free ℤ R]` rings: local instance, from #8577.)
- **mathlib #43661** (`1f5affdb20`) `MulEquiv.Monoid.End` → `MulEquiv.monoidEnd (M)` with `M` now
  explicit — the deprecated alias points at the new signature, so implicit-argument uses break;
  `MulEquiv.Monoid.End_apply` deleted without alias → `MulEquiv.monoidEnd_apply_apply`;
  `monoidEndToAdditive` → `MulEquiv.monoidEnd`, `addMonoidEndToMultiplicative` /
  `MulEquiv.AddMonoid.End` → `MulEquiv.addMonoidEnd`. FltRegular `Hilbert92` :268 (statement of
  `isTors'`: `MulEquiv.Monoid.End` → `MulEquiv.monoidEnd _`, same function), :285, :531.
- **`Finsupp.mapDomain_apply`** now has the general statement `mapDomain f x b = x.sum …`; the
  injective form is `Finsupp.mapDomain_apply_of_injective` (mapDomain rework around #43610,
  `2e52d79f8a`) — FltRegular `Hilbert92` :113.
- **mathlib #39709** (`bc6c657ea8`) upstreamed `Algebra.IsStandardSmoothOfRelativeDimension.mvPolynomial`
  (`[Finite ι]`, `ι : Type`, explicit `R ι`, relative dimension `Nat.card ι`) plus instances
  `…mvPolynomial_fin` and `IsStandardSmooth.mvPolynomial`. The identically-bound local copy in
  ModularCurves `ForMathlib/PolynomialStandardSmooth` clashed (`already declared`) and was removed;
  no other AINTLIB users. Helpers `SubmersivePresentation.mvPolynomialFree{,_dimension}` are now
  unused — for `lane:cleanup`.
- **Instance-inference drift (no rename, upstream cause not isolated):**
  - `MvPolynomial σ (st …) ⧸ J` for an `abbrev st := MvPolynomial _ R ⧸ I` no longer synthesizes
    `HasQuotient` (nested `CommRing (st …) ≟ CommRing (?R ⧸ ?I)` fails although `CommRing (st …)`
    resolves alone; repro kept in the session scratchpad). Fix inside the proof: state the `have`
    through the file's generic abbrev `D.spreadStage` (FinitePresentationDescent :3308).
  - `IsTorsionFree S T` via `FaithfulSMul.to_isTorsionFree` times out in a heavy context →
    `haveI : IsTorsionFree S T := FaithfulSMul.to_isTorsionFree S T` (Vendored/RiemannRoch/SeparableRelNorm).
  - `CommRingCat.ofHom φ.toRingHom` on a tensor product needs `(R := …) (S := …)` (NoethApprox :271);
    an `algebraMap` tensor-product `rfl` → `Algebra.TensorProduct.algebraMap_apply _` (FinitePresentationDescent :406).
- **M6, round 2:** `ModularCurves/Picard/Evaluation.evPre` built its `app` component as
  `ModuleCat.ofHom (TensorProduct.lift (LinearMap.mk₂ ((X.sheaf.obj ⋙ forget₂ _ _).obj U) …))` with a
  hand-made `SMulCommClass`; after #43193 the tensor is over `X.sheaf.obj.obj U` while the unit's
  carrier is spelled via `forget₂`, so `Module` search failed and smul unification timed out (5
  `Unknown identifier evPre` cascades). Fix: `ModuleCat.MonoidalCategory.tensorLift (R := X.sheaf.obj.obj U)
  (M₃ := (𝟙_ …).obj U)` with the same five components — `tensorLift` unfolds to `ofHom (lift (mk₂ …))`;
  `evPre`'s signature is byte-identical. `ForMathlib/PullbackTensorMonoidal` got the same local
  `CommRing` instance and namespace fix as `SheafOfModulesMonoidal`; `WeilPairing/TensorSection`
  retyped scalars to `show ↑(T.sheaf.obj.obj (op U)) from r`.
- **M8 — mathlib #43382** (`c692832859`) `DoubleCoset` iff lemmas take implicit arguments:
  `(DoubleCoset.eq P.H P.H _ _).mp` → `DoubleCoset.eq.mp`.
- **mathlib #43414** (`795fd41661`) `Ideal.isMaximal_of_isIntegral_of_isMaximal_comap` now takes an
  explicit `f : R →+* S`; the `[Algebra R S] [Algebra.IsIntegral R S]` form is
  `Ideal.isMaximal_of_isIntegral_of_isMaximal_under` (same `(I) (hI)` arguments). Same PR:
  `Ideal.exists_ideal_over_prime_of_isIntegral_of_isDomain` now concludes `Q.under R = P` instead of
  `Q.comap (algebraMap R S) = P` — a downstream `hB_under ▸ h` failed with `invalid ▸ notation`;
  restated inside the proof via `B.under (𝓞 K)` and `Ideal.mem_under` (BernoulliRegular
  `DworkDescentAtomicPredicates` :690, round 2).
  `Ideal.exists_ideal_over_prime_of_isIntegral` likewise yields `Ideal.under (𝓞 L) 𝔓 = 𝔮`: a
  `rw [Ideal.map_le_iff_le_comap, h𝔓comap]` stopped matching → `rw [Ideal.map_le_iff_le_comap];
  exact h𝔓comap.ge` (`under` unfolds to the `comap`) — CebotarevDensity `Abelian` :646, round 2.
  Also in #43414: `Ideal.isMaximal_comap_of_isIntegral_of_isMaximal` takes an explicit `(f : R →+* S)
  (hf : f.IsIntegral)`; the instance form is `Ideal.isMaximal_under_of_isIntegral_of_isMaximal` (symptom:
  "argument n has type Ideal B but is expected to have type R →+* B"), wrapped in
  `show (Ideal.comap (algebraMap _ B) n).IsMaximal from …` where a later rewrite needs `comap`; and
  `Ideal.exists_ideal_over_prime_of_isIntegral` takes `hIP : I.under R ≤ P` (insert a `show` with the
  comap form; `rw [Ideal.under]` fails since `under` is an abbrev) — ModularCurves
  `ForMathlib/CoinvariantsPoints` :49, :598, :699, :701.
- **Rewrite drift on tensor products, round 2 (no rename; possibly #40081 removing
  `Subalgebra.module'`, unconfirmed):** `rw [Algebra.smul_def]`, `neg_pow`, `neg_mul_neg` fail to find
  a present pattern until the carrier is named — `Algebra.smul_def (A := …)`, `neg_pow (R := …)`,
  `neg_mul_neg (α := …)` (HopfGaloisBootstrap :105, :240; CoinvariantsPoints). In
  `CoinvariantsPoints.pow_card_mem_range_algebraMap_of_mem_coinvariants` the `htransport` step
  (`congr 1; …; exact mulMatrix_map …`) then hit the 200000-heartbeat limit on coercion checks;
  restructured to `rw [coactionCharpoly, coactionCharpoly, ← hg, coactionBaseChange_naturality …,
  mulMatrix_map]; exact Matrix.charpoly_map _ _` (≈5 s) — no budget raised. These errors were masked
  in the round-2 log behind the file's `| zero` failures: per-file error lists undercount too, not just
  the module list.
- **Round 9:** M6 local `CommRing` instance in ModularCurves `EllipticCurve/PoleSheafBaseSectionsMulFiltration`
  (:274); M5 in PadicLFunctions `Coleman/ColContinuity` (:628) — the `show … = PowerSeries.derivative ℤ_[p] G`
  lemma passed to `simp only` failed to elaborate, surfacing as "`simp` made no progress".
- **Round 8:** M5 `PowerSeries.derivative ℤ_[p] B` / `… ℤ_[p] g` → ring dropped (PadicLFunctions
  `IwasawaProof/FundamentalSequence` :547, :621 — a re-derivation of the `GaloisAction` helper fixed in round 7).
  ModularCurves `EllipticCurve/PoleSheafBaseSectionsMul`: M6 local `CommRing` instance; its two `whnf`
  deterministic timeouts on `.hom.map_smul` (:205, :356) were cascades of the missing instance and vanished
  with it — no budget.
- **Round 7:** `convert … using 2` closes the goal → dead `exact CuspForm.coe_add f g` / `rfl` removed
  (LeanModularForms `Eigenforms/AtkinLehner` :95, :104); M5 `PowerSeries.derivative ℤ_[p] B` →
  `PowerSeries.derivative B` (PadicLFunctions `IwasawaProof/GaloisAction` :1074, cascade at :1069).
  Last jobs (the `PoleSheaf` dependents, first compile on this pin): ModularCurves `WeilPairing/LineVertical`
  — M6 local `CommRing` instance (8 synthesis failures + an `rfl` cascade) and two TensorProduct `| zero`
  cases, the second masked until the instance was back (each deletion checked to sit in an
  `induction … with` block whose siblings include `| tmul`); `EllipticCurve/PullbackTensorSection
  .tensorSection_smul_left` :885 — M6 scalar ring, `smul_tmul' (show ↑(X.sheaf.obj.obj (.op U)) from aa)`.
- **Round 6 (3 modules):**
  - `convert … using n` now closes the goal → dead trailing `simp only […]` / `simp […]` removed
    (LeanModularForms `GL2/HeckeActionGeneral` :303–304; PadicLFunctions `Iwasawa/LocalUnits.isClosed_K` :315–316).
  - M5 in PadicLFunctions `IwasawaProof/LogDerivative` (23 errors, 7 masked until the first pass): besides
    `d⁄dX ℤ_[p] x` / `d⁄dX (ZMod p) x` / `(PowerSeries.derivative ℤ_[p])`, two spellings a space-anchored
    rewrite misses — bare `derivative (ZMod p)` under `open PowerSeries` (in `map_zero`/`map_sum`/`map_sub`
    → `derivative (R := ZMod p)`) and `PowerSeries.derivative (ZMod p)` followed by a line break. Rings with
    brackets (`ℤ_[p]`, `(ZMod p)`) also defeat a naive `[A-Za-z]+` inventory grep.
  - ModularCurves `EllipticCurve/PoleSheaf` (reached only in round 6's final jobs; an `evPre` user, but the
    round-2 `tensorLift` body was not implicated): a dead `· rfl` after `convert … using 1` (:708);
    M6 `PresheafOfModules.Monoidal.tensorObj_map_tmul` → `PresheafOfModulesOfCommRing.Monoidal.tensorObj_map_tmul`
    (:2326) and `PresheafOfModules.leftUnitor_hom_app` → `PresheafOfModulesOfCommRing.leftUnitor_hom_app`
    (:5812, same arguments, now stated with `Hom.app'`, defeq to the surrounding `.app`). Round 7 was
    stopped right after it started, so a single rebuild covers `PoleSheaf` and its dependents.
- **Round 5 (10 modules):**
  - **mathlib #43573** (`403547feec`, `multiplicity` junk value `0`): `multiplicity_eq_zero`, `multiplicity_ne_zero`,
    `dvd_iff_multiplicity_pos`, `multiplicity_pos_of_dvd`, `emultiplicity_pos_iff`,
    `emultiplicity_eq_zero_iff_multiplicity_eq_zero` now take an explicit `FiniteMultiplicity a b`;
    `rw [multiplicity_eq_zero]; exact hcop` left that side goal → `exact multiplicity_eq_zero_of_not_dvd hcop`
    (new in the same PR) — BernoulliRegular `FLT37/LehmerVandiver/CaseI/AntiRadicalNotPthPower` :711, :722.
    Also `multiplicity_eq_one_of_not_finiteMultiplicity` → `multiplicity_eq_zero_of_not_finiteMultiplicity`;
    `multiplicity_zero`, `multiplicity_self` now give `0`.
  - **mathlib #43150** (`b89e536fa9`, `ENat.toNat` lemmas moved to `Data/ENat/Basic`): the simp lemma
    `ENat.toNat_eq_iff_eq_natCast` now fires in `norm_num`, so `norm_num at hint` already yields the goal
    `addVal … = 8`; the `omega`-based `.toNat` tail is dead → `exact hint` (BernoulliRegular
    `FLT37/PadicL/LogCoeffPiOrder` :241).
  - **#43178** deleted alias: `CategoryTheory.inv_hom_id_apply` → `CategoryTheory.Iso.inv_hom_id_apply`
    (ModularCurves `WeilPairing/FieldComparisonBridge` :256).
  - Mechanical: M1 zero cases (HasseWeil `Isogeny/BaseChange/Concrete` ×3, ModularCurves
    `GroupScheme/NIsogeny` ×4 — `Submodule.span_induction` at :1238 untouched); deprecated `induction_on`
    without `@[elab_as_elim]` (`Picard/IdealModuleMul` :254, where `⟨0, ?_⟩` had no expected type); M3
    (`GLn/CongruenceHecke/Surjectivity` :629–635); M6 `monoidalCategory` (`ForMathlib/PullbackCompMonoidal`
    :882); M5 (`FLT37/Eichler/ArtinHasse/ArtinHasseLogCoeffRecurrence` — 11 drops incl. the statement of
    `derivative_logOf_gAH_mul_self`; PadicLFunctions `ResidueZeta` `map_sub`/`map_nsmul
    (PowerSeries.derivative (R := K))`).
- **M6, round 4:** `PresheafOfModules.monoidalCategory` → `PresheafOfModulesOfCommRing.monoidalCategory`
  (ModularCurves `ForMathlib/PresheafPullbackCompMonoidal`). `Picard/PicComparison`: local `CommRing`
  instance, `tensorObj_map_tmul` namespace (3 sites), and in `bijective_evPre_app_of_triv`
  `ModuleCat.ofHom (R := X.sheaf.obj.obj (op W))` plus a `letI` `Module` on the `forget₂`-spelled unit
  carrier. 6 of its 12 errors were cascades. The two type mismatches naming `evPre.app` came from that
  unelaborated `let k`, not from round 2's `tensorLift` body for `evPre`: the unchanged
  `exact hL.apply_symm_apply c` still unfolds through `tensorLift`.
- **Round 4, misc:** `Finset.prod_lt_prod` (ordered semiring, `0 < f i` hypothesis) → `prod_lt_prod₀`
  (#39692; LeanModularForms `GLn/CongruenceHecke/Presentation.prod_removePrime_lt` :79). HasseWeil
  `HasseBound/PoleDivisorTwoTorsion` :119: `add_le_add (le_refl _) h_A_ge` no longer unifies
  `((2 : ℤ) : WithTop ℤ)` with `↑1 + ↑1` (still `rfl` as a term, fails at reducible-and-instances
  transparency) → `rw [show ((2 : ℤ) : WithTop ℤ) = ↑(1 : ℤ) + ↑(1 : ℤ) by norm_cast]` first. Likely
  #42628 (`to_dual` in `Algebra/Order/Ring/WithTop`: instance renames, swap-covariance instances to
  priority 10), unconfirmed; #42622 (`WithBot`/`WithTop` LE defeq) checked and ruled out.
- **M5, round 4:** BernoulliRegular `CyclotomicUnits/KummerLogFormal`,
  `FLT37/Eichler/ArtinHasse/ArtinHasse37CoefficientClosedForm`; HasseWeil `Isogeny/OmegaCoeffViaFormalGroup`;
  PadicLFunctions `ValuesAtOne` — 48 ring arguments dropped (word-diff verified), `(d⁄dX K) (…)` →
  `d⁄dX (…)`, `map_sub (PowerSeries.derivative (R := K))`. `LaurentSeries.derivative F` keeps its
  explicit ring (untouched). Statement respellings (argument drop only):
  `derivative_logOf_formalExpNormalizedMinusOne_mul_self`,
  `X_mul_derivative_logOf_formalExpNormalizedMinusOne`, `derivative_E37`, `coeff_derivative_L37_of_le`,
  `laurent_derivative_ofPowerSeries`.
- **Kernel deterministic timeout, round 3 (toolchain unchanged → mathlib-induced; trigger
  unconfirmed — candidates #40156 `DivisionSemiring.toSemiring` priority, #40081 `Subalgebra.module'`
  removal, #43620 `AlgEquiv` coercion `macro_inline`):**
  `HasseWeil.Conditional.bridgeA_intermediateField_adjoin_eq_fractionRing_finrank`
  (`HasseBound/PoleDivisorFallback` :2412; `(kernel) unknown constant` cascade in
  `finrank_gamma_pullback_x_eq_projectiveDivisorOf_sum`). Bisected by replacing proof blocks with
  `sorry` in a scratch copy: the whole cost was `have h_e1_symm_val : ∀ x, (e1.symm x).val = x.val :=
  fun x ↦ rfl` for `e1 := IntermediateField.equivOfEq h_adj_eq` between `adjoin K {f}` and
  `adjoin K {f⁻¹}` — the kernel `rfl` unfolds across the two subfield carriers. `fun x ↦ by simp [e1]`
  routes through the `equivOfEq` lemmas: 88 s / 11 GB timeout → 13 s / 4.5 GB. One proof line; no
  heartbeat budget. The `backward.isDefEq.respectTransparency.types false` option on that theorem is
  unrelated and still required (the `calc` needs it for `Trans`). Same `fun x ↦ rfl` at :2793 still
  passes — watch it next bump.
- **Round 3, ModularCurves:** `ForMathlib/PullbackTensorGeneral` — M6 local `CommRing` instance +
  namespace (18 errors, one root). `LevelStructure/CartierDivisor` — 3 zero cases. `ForMathlib/HopfGaloisTheorem`
  — 7 zero cases, behind which 13 masked errors surfaced:
  - **Subalgebra-carrier unification blowup (likely #40081, unconfirmed):** lemmas taking `[CommRing R]`
    applied at a `Subalgebra` carrier (`IsLocalRing.of_surjective'`, `.of_surjective`) gave "Application
    type mismatch … ⇑?m" or whnf timeouts comparing `Subalgebra.toCommSemiring` with
    `CommRing.toCommSemiring ?inst` → pass `(S := coinvariants …)` or wrap the argument in `by exact`
    (instances first); `backward.isDefEq.respectTransparency false` does not help. No budget raised.
  - **`Algebra.smul_def` drift:** on `leftHasSMul` → `erw [Algebra.smul_def (R := …) (A := …)]`; subalgebra
    smul → `Algebra.smul_def (A := …), Subalgebra.smul_def, smul_eq_mul`.
  - `basisOverScalarsOfBasisOverCoinvariants` (a `def`): proof arguments inside its body changed; type
    byte-identical (hash-checked).
  `EllipticCurve/PoleFiltration` — bare `map_zero` matched the bundled `p.coeff 0` → named `algebraMap`.
  `Vendored/RiemannRoch/EllipticCurve/Instances.isSeparable` — typeclass timeout on
  `Algebra k⟮X⟯ ↥(⊤ : IntermediateField …)` → `letI := IntermediateField.algebra' _`.
- **Round 3, misc:** further `MvPolynomial.coeff` respellings inside proofs (AdicSpaces `Wedhorn828`
  :2118–2503, existing 15 `sorry`s untouched; LeanModularForms `GLn/PolynomialRing` :351–368, :907–911);
  `isMaximal_comap_of_isIntegral_of_isMaximal` → `isMaximal_under_of_isIntegral_of_isMaximal`
  (HasseWeil `NormConormIntegralClosure` :264, :2031); `convert … using 1` closes the goal
  (LeanModularForms `GL2/HeckeAction` :178).
- **M5, round 3:** PadicLFunctions `PadicExp`, `Interpolation/TameConductor`; HasseWeil
  `Foundation/ChordExpansion`, `FormalGroup/CharP`; BernoulliRegular `CyclotomicUnits/PadicLogSetup`,
  `DworkFactorization/FiniteArtinHasseFormal` — 38 ring arguments dropped (word-diff verified), plus
  `congrArg (d⁄dX F)` → `congrArg (PowerSeries.derivative (R := F))`. Statement respellings (argument
  drop only): `PadicExp.oneAddX_mul_derivative_log`, `ChordExpansion.derivative_formalW_key` (private),
  `ChordExpansion.subst_derivative_formalW_key`, `CharP.coeff_eq_zero_of_derivative_eq_zero_charP`
  (private). Also `prod_le_prod₀` (PadicExp :756), a now-no-progress `simp only` removed, and the
  `under` fix mirrored into `FlexibleDworkDescentAtomicPredicates` :433.
- **M3/M4 side effects, round 2:** `MvPolynomial.coeff_zero` is now the Finsupp equality
  `(0 : MvPolynomial σ R).coeff = 0`, so `rw [..., MvPolynomial.coeff_zero]` no longer closes
  `0 = 0 β` by `rfl` → append `Finsupp.zero_apply` (AdicSpaces `AdicCompletionNoetherian` :582, :586;
  its existing 9 `sorry` occurrences untouched); `(∑ …).coeff α₀` needs a type ascription to elaborate
  (:1276). With `coeff` bundled, a bare `map_one` matched `p.coeff 1` and failed on
  `OneHomClass (ℕ →₀ F) ℕ F` → `map_one (algebraMap F KE)` (HasseWeil `AdditionPullback` :314).
- **M5, round 2:** further derivative-argument drops in PadicLFunctions `MeasureR/FormalPsi`,
  `KubotaLeopoldt/MuA` (proof-only), BernoulliRegular `ArtinHasseSeriesDworkIdentity` (statement
  respellings in private `artinHasseExpSeries_derivative`, `derivative_rescale_exp_rat`,
  `eq_rescale_exp_of_derivative_eq_smul`) and HasseWeil `FormalGroupHom.invariantDifferential_chain`.
  Unapplied uses need the ring named: `(PowerSeries.derivative K).map_smul` →
  `(PowerSeries.derivative (R := K)).map_smul`. Word-diff audit: every changed token is a dropped ring
  argument, the `(R := K)` naming, or the `comap`→`under` swap above.
- **Tactic/simp-set drift (no rename):** `convert … using 1` now closes `(fun t ↦ -(f t)) = -f`
  itself (delete follow-up `funext` bullet); `simp [Real.pi_ne_zero]` needs `Real.pi_pos`;
  a full `simp` in `DieudonneDworkCriterion` now normalises `C ↑((k+1).choose k)` (→ `simp only
  [term, hsub, pow_one]`); `simp` now rewrites `Submodule.subtype ⟨x, hx⟩` for a subalgebra element
  to `Subalgebra.val` rather than the bare coercion, so a `simpa … using hx g` in
  `InvariantBaseChange.exact_subtype_invariantsDelta` became `show g • x - x = 0; exact
  sub_eq_zero.mpr (hx g)`.
- **Unification-cost regression (no rename):** `SemilocalBasis.exists_mem_forall_fibreEval_notMem_span`
  hit a `whnf` heartbeat timeout (kernel `unknown constant` cascade at :303) unifying the implicit
  `[∀ j, AddCommGroup (T j)]` / `[∀ j, Module R (T j)]` families of
  `exists_one_tmul_baseChange_ne_zero` against instances on let-bound quotients `T j`. Fixed without
  raising any budget by passing the instance families explicitly (`@… (fun _ => inferInstance)
  (fun _ => inferInstance)`). Upstream cause not isolated.


## Outcome

Full tree green on round 10: all 11 library roots + 2 orphan modules build with zero errors on mathlib `63025c440a76` / Lean `v4.34.0-rc2`, with no statement changed (spelling-only respellings listed above), no `sorry`/`admit`/`axiom` and no heartbeat budget added. The #8574 ModularCurves exclusions and the 189 undocumented orphan ModularCurves modules predate this bump and remain unbuilt.
