# Step 6 — Generalization Analysis: PadicLFunctions

Scope: p-adic measures, Iwasawa algebras, generalised Bernoulli numbers. Central
angle: the **`MeasureR/` track is the general-ring-`R` (`R := integerRing K`, the
unit ball of a complete ultrametric normed `ℚ_p`-algebra `K`) version of the
`Measure/` track (over `ℤ_p`)**. The two tracks are near-verbatim duplicates;
`Measure/` is the special case `K = ℚ_p`, `R = ℤ_p` of `MeasureR/`. Below, each
candidate has: **Current** statement, what the **proof only uses**, **Literature**
standard generality, **Mathlib** API, proposed **Action** (signature), and
**Difficulty**.

Read-only reasoning (no local build). Literature anchor: RJW *An introduction to
p-adic L-functions* (arXiv:2309.15692) §3, whose Rem 3.33 already states the theory
"for any profinite abelian `G`"; the Iwasawa-algebra literature defines
`Λ_G = 𝒪[[G]]` for **any profinite abelian `G`** and **any complete (p-adic)
coefficient ring `𝒪`** (Springer, *Iwasawa Algebras and p-adic Measures*).

---

## TIER A — the `Measure` (ℤ_p) ⊂ `MeasureR` (R) duplication

The single biggest generalisation finding: **almost every declaration in
`Measure/*.lean` is the `R = ℤ_p` instance of the corresponding declaration in
`MeasureR/*.lean`**, re-proved by copy-paste. The file headers say so explicitly
(`MeasureR/Convolution.lean`: "exactly as in the `ℤ_p`-layer
`PadicLFunctions/Measure/Convolution.lean`"; `MeasureR/Fubini.lean`: "Proved
exactly as in the `ℤ_p`-layer"). The stated reason for the split (`Measure/Basic.lean`
docstring) is pragmatic: `ℤ_[p]` is *definitionally but not syntactically* the unit
ball of `ℚ_[p]`, and §4 (`KubotaLeopoldt/*`) is built on the concrete `PadicMeasure`
spelling. That is a real friction cost, but it does not change the mathematical fact
that the `ℤ_p` results are special cases — and several of them can be **derived** from
the `R`-layer rather than re-proved, or unified once a defeq bridge `ℤ_[p] ≃
integerRing ℚ_[p]` is in place.

### 1. `PadicMeasure` is `MeasureR ℚ_[p]` (the whole `Measure/Basic` API)
- **Current** (`Measure/Basic.lean`): `abbrev PadicMeasure (X) := C(X, ℤ_[p]) →ₗ[ℤ_[p]] ℤ_[p]`, with `dirac`, `compRight`, `pushforward`, `norm_apply_le`, `continuous`, `ext_locallyConstant` all over `ℤ_[p]`. (`MeasureR/Basic.lean`): `abbrev MeasureR K X := C(X, integerRing K) →ₗ[integerRing K] integerRing K` with the identical 12-decl API.
- **Proof only uses**: for `norm_apply_le`/`continuous`/`ext_locallyConstant` the `MeasureR` proofs use only: `K` is an ultrametric normed field, `integerRing K` is its unit ball, the sup-norm is attained on a compact `X`, and a nonzero `f` can be divided by a scalar of maximal norm keeping values integral. The `ℤ_p` proofs do **exactly** the same with `f = p^n • g` (special case: maximal-norm scalar is a power of `p`). Nothing in the `ℤ_p` proofs needs `ℤ_[p]` over `integerRing ℚ_[p]`.
- **Literature**: measures = continuous dual of `C(X, 𝒪)` for any compact `X` and any complete DVR / p-adic ring `𝒪` (RJW Def 3.6; Springer §3). `ℤ_p` is just `𝒪 = ℤ_p`.
- **Mathlib**: `LocallyConstant.charFn` is already value-ring-parametric (used by both). `IsUltrametricDist`, `WeakDual` exist. No mathlib obstruction.
- **Action**: Establish a defeq/`RingEquiv` bridge `ℤ_[p] ≃+* integerRing ℚ_[p]` (W-bridge already referenced in tickets), then either (a) make `PadicMeasure p X := MeasureR ℚ_[p] X` a `def`/`abbrev` and *derive* `Measure/Basic`'s lemmas from `MeasureR/Basic`, or (b) keep both but mark the `ℤ_p` versions `@[deprecated]`-toward-`MeasureR`. Mechanical win: delete the duplicated `norm_apply_le`/`continuous`/`ext_locallyConstant` proofs.
- **Difficulty**: **Med** (the friction is the §4 dependence on the `PadicMeasure` spelling, not the math; a defeq bridge is delicate but the tickets note it was deferred deliberately, not because it is impossible).

### 2. `exists_locallyConstant_norm_sub_le'` — already general, but is the engine of BOTH tracks and is mathlib-bound
- **Current** (`Measure/Fubini.lean`, lines 70–115): `theorem exists_locallyConstant_norm_sub_le' [CompactSpace X] {E} [SeminormedAddCommGroup E] [IsUltrametricDist E] (f : C(X, E)) {ε} (hε : 0 < ε) : ∃ Φ : LocallyConstant X E, ∀ x, ‖f x - Φ x‖ ≤ ε`. Its own docstring: "Generalises `exists_locallyConstant_norm_sub_le`… PR candidate for mathlib."
- **Proof only uses**: compactness of `X`, and that in an ultrametric `E` closed balls are clopen (`IsUltrametricDist.isOpen_closedBall`) — no `ℤ_p`, no completeness, no algebra. **This is already maximally general.**
- **Literature**: density of locally constant functions in `C(X, E)` for compact totally-disconnected `X` (here packaged via clopen ε-balls in `E`); standard.
- **Mathlib**: `LocallyConstant`, `IsUltrametricDist.isOpen_closedBall`, `IsCompact.elim_finite_subcover` all present. The `ℤ_p`-specific `exists_locallyConstant_norm_sub_le` is the strictly weaker mathlib lemma this supersedes.
- **Action**: **PR to mathlib as-is** (it is already in the maximally-general form and both `Measure/Fubini` and `MeasureR/Fubini` consume it — `MeasureR/Basic.ext_locallyConstant` and both `integral_swap`s depend on `PadicMeasure.exists_locallyConstant_norm_sub_le'`). No signature change needed; this is a "lift to mathlib" not a "generalise" — but it eliminates a cross-track dependency cleanly. Consider also stating the `WeakDual`/density corollary.
- **Difficulty**: **Low** (statement is final; only namespacing + mathlib polish).

### 3. `integral_swap` (Fubini) — re-proved verbatim in both tracks (~100 lines each)
- **Current**: `Measure/Fubini.integral_swap` (~108-line proof) and `MeasureR/Fubini.integral_swap` (~102-line proof) prove the identical statement `μ (innerInt ν F) = ν (innerInt μ (F ∘ swap))`, one over `ℤ_[p]`, one over `R = integerRing K`, by the **same** ε-approximation argument (`exists_locallyConstant_norm_sub_le'`, finite-sum collapse, `‖μ‖,‖ν‖ ≤ 1` via `norm_apply_le`, ultrametric triangle).
- **Proof only uses**: `‖μ‖,‖ν‖ ≤ 1` (i.e. `norm_apply_le`), the general approximation lemma, and the ultrametric inequality on the **coefficient ring**. Identical hypotheses. The only difference is the coefficient ring symbol.
- **Literature**: Fubini for `𝒪`-valued measures on compact spaces, any complete ultrametric `𝒪` (RJW Rem 3.11, "one checks").
- **Mathlib**: nothing missing; `ContinuousMap.curry`/`uncurry`, `LocallyConstant.charFn` parametric.
- **Action**: Prove **one** `integral_swap` over a general coefficient ring (the `MeasureR` version already is that, modulo `R = integerRing K`); derive the `ℤ_p` version from it via the bridge of #1, OR factor the shared body into a `Common/` lemma quantified over `[SeminormedCommRing R] [IsUltrametricDist R]` with `‖μ f‖ ≤ ‖f‖` as a hypothesis. Removes ~100 duplicated proof lines.
- **Difficulty**: **Med** (depends on the #1 bridge or a `norm_apply_le`-as-hypothesis refactor; the proof itself is done).

### 4. The Mahler transform equivalence `ℳ(ℤ_p, R) ≃ R⟦T⟧` — duplicated `mahlerTransform` API
- **Current**: `Measure/MahlerTransform.lean` (`mahlerCoeff`, `mahlerTransform`, `mahlerLinearEquiv : PadicMeasure ≃ₗ ℤ_p⟦T⟧`, `mahlerTransform_injective`, `ofPowerSeries`, …) and `MeasureR/MahlerTransform.lean` (`mahlerCM`, `mahlerTransform`, `mahlerLinearEquiv : MeasureR K ℤ_[p] ≃ₗ R⟦T⟧`, …) are the same 13–17 decls, ℤ_p vs `R`. `MeasureR` even imports `PadicMeasure.fwdDiff_iter_mahler_zero` (it reuses the `ℤ_p` Kronecker-delta lemma, transporting through `algebraMap`).
- **Proof only uses**: Mahler's theorem `PadicInt.hasSum_mahler` for `f : C(ℤ_[p], R)` (mathlib provides it for any complete ultrametric `R`-target via `fwdDiff_tendsto_zero`), summability from integrality (`‖coeff‖ ≤ 1`), and `algebraMap` commuting with finite forward differences. The `R`-layer is the genuinely general statement; the `ℤ_p`-layer is `R = ℤ_p`.
- **Literature**: Amice/Mahler transform `ℳ(ℤ_p, 𝒪) ≅ 𝒪⟦T⟧`, RJW Thm 3.20, any complete `𝒪`.
- **Mathlib**: `PadicInt.hasSum_mahler`, `PadicInt.fwdDiff_tendsto_zero`, `PowerSeries.Binomial` all present and already used.
- **Action**: Keep `MeasureR/MahlerTransform` as the primary; derive `Measure/MahlerTransform`'s `mahlerTransform_injective`, `mahlerLinearEquiv` from it via the bridge (#1). The `fwdDiff_iter_mahler_zero` over `ℤ_p` is the only genuinely-`ℤ_p` lemma and should stay (it is the base of the transport).
- **Difficulty**: **Med** (same bridge dependency).

### 5. `Toolbox` operators (`cmul, del, res, sigma, phi, psi, σ_a`) — duplicated, but the `R`-layer already drops instances via `omit`
- **Current**: `Measure/Toolbox.lean` (34 decls over ℤ_p) and `MeasureR/Toolbox.lean` (26 decls over `R`) re-define `cmul`, `del = (1+T)d/dT`, `res`, `IsSupportedOn`, `sigma`, `phi`, `psi`, and prove `psi_phi`, `phi_psi`, `res_units_eq` (= Eq 3.10), `isSupportedOn_units_iff_psi_eq_zero` (= Cor 3.32) in both. The space-side gadgets (`digit`, `shiftDiv`, `mulCM`, `isClopen_pZp`, `isClopen_units`) live **only** in `Measure/Toolbox` and are *reused* by `MeasureR/Toolbox` — good, that part is already shared.
- **Proof only uses**: `MeasureR/Toolbox`'s lemmas almost all carry `omit [CompleteSpace K] [NormedAlgebra ℚ_[p] K]` (e.g. `psi_sub`, `psi_add`, `psi_zero`, `cmul_apply`, `res_units_eq`) — the inventory shows the authors *already discovered* these need only the normed-field-with-ultrametric structure of `R`, not the algebra/completeness. That is direct evidence the `R`-layer is the right generality and the `ℤ_p`-layer is redundant.
- **Literature**: §3.5 toolbox over any complete `𝒪`.
- **Mathlib**: `LinearMap.mulLeft`, `PowerSeries.derivativeFun`, `LocallyConstant.charFn` parametric.
- **Action**: After #1's bridge, derive the `ℤ_p` `del`/`cmul`/`res`/`phi`/`psi` operator lemmas (especially `psi_phi`, `phi_psi`, `res_units_eq`, `isSupportedOn_units_iff_psi_eq_zero`) from the `MeasureR` versions. The `del` operator and `coeff_del` are coefficient-ring-agnostic already (only need `CommRing`), so those two are pure duplication that can be unified into `Common/` today with no bridge.
- **Difficulty**: **Med** (operators), **Low** (the `del`/`coeff_del` power-series-only pair → `Common/`).

---

## TIER B — generality the `R`-layer itself still under-reaches

### 6. `unitsConv` / `Λ_R(ℤ_p^×)` `CommRing` is hardcoded to `ℤ_[p]ˣ` while the ℤ_p analogue is already general-`G`
- **Current**: `MeasureR/UnitsRing.lean` defines `unitsConv (μ ν : MeasureR K ℤ_[p]ˣ)`, `Mul/One/CommRing (MeasureR K ℤ_[p]ˣ)`, `units_dirac_mul_dirac`, `deg : MeasureR K ℤ_[p]ˣ →+* R` — **all fixed to `G = ℤ_[p]ˣ`**. By contrast `Measure/PseudoMeasure.lean` was *already generalised in place* (its own comment: "generalised… from its original hardcoded `G = ℤ_[p]ˣ` by the §11 pass (R11.5)") to **`variable (G) [TopologicalSpace G] [CommMonoid G] [ContinuousMul G] [CompactSpace G]`**, giving `conv`, `mulCM₂`, `Mul/One/CommRing (PadicMeasure p G)`, `deg` for any compact commutative topological monoid.
- **Proof only uses**: `unitsConv`/its `CommRing` use only: `innerInt`, `integral_swap` (Fubini, for `mul_comm`), the triple-integral for `mul_assoc`, `dirac` at `1`, and `unitsMulCM₂ : C(G×G, G)` (= multiplication). **Nothing uses that `G = ℤ_p^×` specifically** — `unitsMulCM₂` is just `mulCM₂ G` for `G = ℤ_[p]ˣ`. The general-`G` ℤ_p proof in `PseudoMeasure` is the template.
- **Literature**: `Λ_𝒪(G)` for any profinite abelian `G` (RJW Rem 3.33 "for any profinite abelian `G`"; Springer). Specialising to `ℤ_p^×` is unnecessary.
- **Mathlib**: `ContinuousMul`, `CompactSpace`, `CommMonoid` classes present; `Measure/PseudoMeasure` proves it is achievable.
- **Action**: **Mirror the `PseudoMeasure` generalisation into `MeasureR`**: introduce `variable (G) [TopologicalSpace G] [CommMonoid G] [ContinuousMul G] [CompactSpace G]`, define `MeasureR.conv`, `MeasureR.mulCM₂ G`, `instance CommRing (MeasureR K G)`, `MeasureR.deg : MeasureR K G →+* R`; recover the `ℤ_[p]ˣ`-named versions as `abbrev`/specialisations preserving downstream statements verbatim (exactly the recipe `PseudoMeasure` used). This is the **single most asymmetric gap**: the ℤ_p track is general-`G`, the `R` track is not.
- **Difficulty**: **Med** (the proof template already exists in `PseudoMeasure`; mechanical port + the `omit`s the inventory shows are safe).

### 7. `iota : Λ_R(ℤ_p^×) → Λ_R(ℤ_p)` and `mem_range_iota_iff` — hardcoded to the inclusion `ℤ_p^× ↪ ℤ_p`
- **Current**: `MeasureR/UnitsZp.lean` (and `Measure/UnitsZp.lean`): `iota := pushforward (unitsValCM)`, `iota_injective`, `extendByZero`, `res_iota`, `mem_range_iota_iff : μ ∈ range iota ↔ psi μ = 0`. All fixed to the units→`ℤ_p` inclusion.
- **Proof only uses**: `iota_injective` and `extendByZero` use only that the source embeds as a **clopen** subset of the target (via `isClopen_units`, `unitsHomeo`) and extension-by-zero is continuous there. That is the general "pushforward along a closed/clopen embedding of profinite spaces is injective, with image = measures supported on the sub-clopen" statement.
- **Literature**: for any clopen `U ⊆ G`, `Λ_𝒪(U) ↪ Λ_𝒪(G)` with image `{μ : Res_U μ = μ}` (RJW Rem 3.33 in the abstract form).
- **Mathlib**: `Topology.IsClopen`, `IsEmbedding`, `LocallyConstant.charFn` parametric.
- **Action**: Generalise `extendByZero`/`iota`/`res_iota`/`mem_range_iota_iff` to an arbitrary clopen inclusion `j : U ↪ X` (or at least keep ℤ_p^×↪ℤ_p but factor the clopen-embedding core). Lower priority than #6 but the same flavour. The `mem_range_iota_iff = ker ψ` characterisation is inherently ℤ_p^×-flavoured (it references `ψ`), so the *units* instance should remain; only `iota_injective`/`extendByZero` are worth abstracting.
- **Difficulty**: **Med**.

### 8. `mahlerTransform_pushforward_mulCM` / `sigma`,`phi` substitution — the substitution formula is coefficient-general
- **Current** (`Measure/Toolbox.lean`, ~57-line OVER-50 proof): `mahlerTransform (pushforward (mulCM c) μ) = subst (binomialSeries c - 1) (mahlerTransform μ)`, over ℤ_p; no `R`-analogue exists in `MeasureR/Toolbox` (the `R`-track derives `phi` via `FormalPsi.mahlerTransform_phi` instead).
- **Proof only uses**: the binomial-series identities (`binomialSeries_mul_nat`, `binomialSeries_coeff`, `binomialSeries_constantCoeff`), `coeff_subst'`, and the density-equalizer `PadicInt.denseRange_natCast.equalizer`. The coefficient ring enters only through `mahlerTransform`'s codomain `R⟦T⟧`; the identity is `algebraMap`-natural.
- **Literature**: RJW §3.5.5 Eq (3.9), any `𝒪`.
- **Mathlib**: `PowerSeries.subst`, `coeff_subst'`, `PowerSeries.Binomial`, `PadicInt.denseRange_natCast` all present.
- **Action**: State the substitution formula once over `R` and recover ℤ_p; or at minimum note that `MeasureR/FormalPsi.mahlerTransform_phi` (66-line OVER-50) and `Measure/Toolbox.mahlerTransform_pushforward_mulCM` (57-line OVER-50) prove overlapping substitution facts in different generalities and should share a core. (Cross-references the decompose-proof lane.)
- **Difficulty**: **High** (two large proofs in different shapes; unifying needs care, and `FormalPsi` adds the digit-decomposition machinery).

---

## TIER C — Bernoulli / coefficient-ring statements

### 9. `genBernoulli`, `LvalNeg`, `genBernoulli_eq_zero`, `genBernoulliPowerSeries_mul` — already over a general field, but could be a general `ℚ`-algebra
- **Current** (`Interpolation/GenBernoulli.lean`): `variable {L : Type*} [Field L] [CharZero L]`. `DirichletCharacter.genBernoulli (χ : DirichletCharacter L N) (k) : L := (N:L)^(k-1) * ∑ ... eval (...) ((bernoulli k).map (algebraMap ℚ L))`. This is **already field-generic** (not pinned to `ℚ_p`/`ℤ_p`) — good.
- **Proof only uses**: `genBernoulli` itself needs only a `ℚ`-algebra structure (it lands in the image of `algebraMap ℚ L`) and `CharZero` for the `N^{k-1}` and `1/(k+1)` divisions. `Field` is stronger than necessary for the *definition* and for `genBernoulliPowerSeries_mul` (which is a power-series identity); `genBernoulli_eq_zero` uses `2 ≠ 0` and the negation bijection, which need a domain, not a field. The reflection `bernoulli_eval_one_sub` is mathlib-general.
- **Literature**: generalised Bernoulli `B_{k,χ}` defined for `χ` valued in any characteristic-zero `ℚ`-algebra (Washington §4.1); `Field` is the convenient but not minimal class.
- **Mathlib**: `Polynomial.bernoulli`, `bernoulli_eval_one_sub`, `DirichletCharacter`, `algebraMap ℚ L` — all present. mathlib has **no** generalised-Bernoulli-of-a-Dirichlet-character API, so this whole cluster is a mathlib-gap candidate (separate from generalisation).
- **Action**: Weaken `[Field L] [CharZero L]` → `[CommRing L] [Algebra ℚ L]` (which forces `CharZero` and supplies the needed inverses, since `ℚ ↪ L`) for `genBernoulli`/`LvalNeg`/`genBernoulliPowerSeries_mul`; keep `Field`/domain only where genuinely used (`genBernoulli_eq_zero` needs `IsDomain` for `2•T = 0 ⇒ T = 0`). Try the mechanical `Algebra ℚ L` weakening first.
- **Difficulty**: **Low** (mechanical assumption-weakening; `[Algebra ℚ L]` is the literature-standard class and most of the file already routes through `algebraMap ℚ L`).

### 10. `prod_primitiveRoot_mul_sub_one` — already maximally general (noted for completeness)
- **Current**: `{R} [CommRing R] [IsDomain R] {ζ} {M} (hM : Odd M) (hζ : IsPrimitiveRoot ζ M) (Y : R) : ∏_{c<M} (ζ^c Y − 1) = Y^M − 1`. Already domain-generic, not p-adic.
- **Proof only uses**: `X_pow_sub_C_eq_prod`, oddness; `IsDomain` essential.
- **Literature**: cyclotomic product identity over any domain.
- **Mathlib**: candidate to PR as a standalone `IsPrimitiveRoot` lemma (mathlib has the factorisation but maybe not this evaluated-at-1 odd-`M` corollary).
- **Action**: No generalisation needed; flag as a **mathlib-PR** candidate (out of scope for this step, route to `/mathlibable`).
- **Difficulty**: **Low** (no change; PR only).

### 11. `Coefficients.lean` root-of-unity bounds — already aggressively `omit`-generalised
- **Current**: `IsPrimitiveRoot.norm_sub_one_lt`, `norm_pow_sub_one_eq_one`, `norm_natCast_eq_one_of_not_dvd`, `tendsto_pow_sub_one` — stated for any ultrametric normed `ℚ_p`-algebra field `L`, with `omit [CompleteSpace L]` / `omit [NormedAlgebra ℚ_[p] L]` peeling unused instances. `integerRing`, `ballIdeal`, the algebra/ultrametric/complete instances are all parametric in `L`.
- **Proof only uses**: the inventory shows the authors already minimised the instance footprint per-lemma (e.g. `norm_pow_sub_one_eq_one` omits `NormedAlgebra` and `CompleteSpace`). `integerRing L = {‖·‖ ≤ 1}` is defined using only the ultrametric norm.
- **Literature**: these are the standard W2/W3 nonarchimedean root-of-unity estimates over any complete DVR's fraction field.
- **Mathlib**: `IsPrimitiveRoot`, `IsUltrametricDist`, `Padic.norm_p` present.
- **Action**: Already near-optimal. One residual: `norm_natCast_self_lt_one` and `norm_natCast_eq_one_of_not_dvd` are stated over a `ℚ_p`-algebra but only use `‖(n:L)‖` via `algebraMap ℚ_p`; if `L` is a general complete nonarch. field with residue char `p` they still hold — but the `ℚ_p`-algebra hypothesis is the natural project-wide ambient, so leave as is. **No action** beyond confirming the `omit`s are exhaustive (a `/generalise` mechanical pass).
- **Difficulty**: **Low** (verification / mechanical `omit` audit only).

---

## File-level: `MeasureR/FormalPsi.lean` `seriesEval` / `phiSeries` cluster

`phiSeries`, `IsDigitDecomp`, `hasSubst_one_add_X_pow_sub_one`, `coeff_substSeries_pow_eq_zero`, etc. are **already** stated over a general `CommRing R` (with `omit [Fact p.Prime]` where the prime is unused), and only the *digit-uniqueness* results (`existsUnique_digits`, `psiSeries_phi`, `psiSeries_add`, `psiSeries_C_mul`) specialise to `integerRing K` — **correctly**, because the docstring records that uniqueness is FALSE over a `CommRing` where `p` is invertible (a genuine mathematical obstruction, not laziness). So this file is already at the right generality boundary; **no generalisation action** (any attempt to widen `existsUnique_digits` past `integerRing K` would be unsound). Flag only as a positive: the `phiSeries`/substitution/summability infrastructure (`seriesEval_mul`, `seriesEval_add`, `summable_*`) is reusable mathlib-quality power-series API that is *not* p-adic-specific and could feed a future mathlib `PowerSeries` substitution-evaluation file.

---

## Summary table

| # | Candidate | Direction | Difficulty |
|---|-----------|-----------|------------|
| 1 | `PadicMeasure` = `MeasureR ℚ_p` (Basic API) | ℤ_p ⊂ R, derive/dedup | Med |
| 2 | `exists_locallyConstant_norm_sub_le'` | already general → mathlib PR | Low |
| 3 | `integral_swap` (Fubini) ×2 | unify over general coeff ring | Med |
| 4 | `mahlerTransform`/`mahlerLinearEquiv` ×2 | derive ℤ_p from R | Med |
| 5 | `Toolbox` operators (`del`/`coeff_del` first) | dedup; `del` → `Common/` now | Low/Med |
| 6 | `unitsConv`/`CommRing (MeasureR K ℤ_p^×)` → general `G` | port `PseudoMeasure` R11.5 to R | Med |
| 7 | `iota`/`extendByZero` → general clopen embedding | abstract inclusion | Med |
| 8 | `mahlerTransform_pushforward_mulCM` subst formula | coeff-general; unify w/ FormalPsi | High |
| 9 | `genBernoulli` cluster `[Field]`→`[Algebra ℚ L]` | weaken assumptions | Low |
| 10 | `prod_primitiveRoot_mul_sub_one` | already general → mathlib PR | Low |
| 11 | `Coefficients` root-of-unity bounds | already `omit`-minimal → audit | Low |

**Count: 11 candidates.** Low: 5 (#2, #5-partial, #9, #10, #11) · Med: 5 (#1, #3, #4, #6, #7) · High: 1 (#8). (#5 spans Low for `del`/`coeff_del`, Med for the operators.)

**Top 5 (highest leverage):**
1. **#6** — port the `PseudoMeasure` general-`G` convolution ring into `MeasureR` (the one place where the ℤ_p track is *more* general than the R track; template already exists).
2. **#2** — PR `exists_locallyConstant_norm_sub_le'` to mathlib (already final form, the shared engine of both Fubini proofs; self-documented PR candidate).
3. **#1** — bridge `ℤ_[p] ≃+* integerRing ℚ_[p]` and collapse the `Measure/Basic` ⊂ `MeasureR/Basic` duplication (unlocks #3, #4, #5).
4. **#9** — weaken `genBernoulli`'s `[Field L] [CharZero L]` to `[CommRing L] [Algebra ℚ L]` (mechanical, literature-standard).
5. **#3** — unify the two ~100-line `integral_swap` Fubini proofs over a general coefficient ring.

**Cross-cutting note:** the dominant theme is *intra-project duplication via under-generalisation of the coefficient ring* — `Measure/*` is the `R = ℤ_p` shadow of `MeasureR/*`, re-proved rather than derived. The `PseudoMeasure` file proves (#6) that the abstract-`G` direction is also tractable and was already taken on the ℤ_p side; bringing `MeasureR` to the same `(G, 𝒪)`-generality as the literature's `Λ_𝒪(G)` is the coherent end-state.

Output path: `/Users/mcu22seu/Documents/GitHub/aintlib-main/projects/PadicLFunctions/.mathlib-quality/overview/analysis/06-generalization.md`
