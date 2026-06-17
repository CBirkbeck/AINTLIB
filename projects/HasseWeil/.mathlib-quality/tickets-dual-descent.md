# Ticket Board — DUAL-DESCENT (the dual isogeny over the base field / isogeny symmetry)

*Companion to `plan-dual-descent.md` (read it first — Silverman route, mathlib inventory, the
finite-level descent decision, and the honest feasibility verdict). Created 2026-06-17, dev/hasse-weil.*

Conventions (BINDING):
- Worktree `/Users/mcu22seu/Documents/GitHub/aintlib-hasse`, project `projects/HasseWeil/`, build
  `lake build HasseWeil` (iterate with `lake build HasseWeil.EC.IsogenyAG.DualDescent`). NEVER
  `2>/dev/null` next to lake/lean (guardrail) — use `2>&1`. `sorry` allowed on this dev branch.
- REUSE don't duplicate (the HAVE pieces in the plan's inventory — cite them, don't rebuild).
- Don't clean/golf/bump — math only.
- New code lands in `HasseWeil/EC/IsogenyAG/DualDescent.lean` (Galois action + descent + assembly)
  unless a sub-leaf is naturally a Curves/* lemma.

## Summary
- 4 phases (DUAL-Q1 … DUAL-Q4) + 1 final cleanup. DUAL-Q2 is the deep crux (API gap; may go
  `/expert-review`). Headline deliverable: `universalDualWitness_of_charZero`.
- Dependency order: Q1 → Q2 → Q3 (Q3 needs Q1's Galois action) → Q4 (needs Q2+Q3) → discharge gate.

---

### [DUAL-Q1] Galois action on the base-changed function field + fixed field = F(E)
- **Status**: open | **File**: `HasseWeil/EC/IsogenyAG/DualDescent.lean` | **Depends on**: none | **Type**: def + lemmas

#### Statement (shape; finite Galois `L/F` or `K̄ = AlgebraicClosure F`)
```
-- (a) tensor identification — REUSE functionField_baseChange_tensorEquiv (CurveMapBaseChange.lean:645)
-- (b) the Galois action: σ : L ≃ₐ[F] L  induces  galAct σ : L(E_L) ≃ₐ[F] L(E_L)
def galActFunctionField (E : Affine F) [E.IsElliptic] (σ : L ≃ₐ[F] L) :
    (E.baseChange L).FunctionField ≃ₐ[F] (E.baseChange L).FunctionField
-- (c) fixed field
theorem fixedField_galAct_eq (E : Affine F) [E.IsElliptic] :
    -- the subfield of L(E_L) fixed by all galActFunctionField σ  =  image of F(E)
    ... = (algebraMap F(E) → L(E_L)).range  -- (shape)
```

#### Proof sketch
1. (a) `L(E_L) ≅ L ⊗_F F(E)` via the project's `functionField_baseChange_tensorEquiv`
   (CurveMapBaseChange.lean:645) — E geometrically integral over the perfect F makes F(E)/F regular,
   so the tensor is a field. REUSE; don't rebuild.
2. (b) `galAct σ := transport of (Algebra.TensorProduct.map σ.toAlgHom (AlgHom.id))` along the
   equiv. API lemmas: `galAct_id`, `galAct_mul σ τ` (it's a group action), `galAct` fixes the
   `F(E)`-factor.
3. (c) fixed field: `(L ⊗_F F(E))^{Gal(L/F)} = F(E)` — Galois descent of the tensor. Route via
   mathlib `RingTheory/Flat/FaithfullyFlat/Descent.lean` + finite-Galois `fixedField`
   (`(L)^{Gal(L/F)} = F` for `L/F` finite Galois, `IsGalois.fixedField_top`-flavored) tensored with
   `F(E)`. This is the one non-trivial leaf of Q1.

#### Sources
Silverman III.4.10b (the translation/Galois mechanism, p.73 — here the *base-field* Galois, not the
kernel Galois); standard Galois descent (Bourbaki / Stacks `0CDQ`). mathlib `FaithfullyFlat/Descent`.

#### Generality
`L/F` finite Galois, or `K̄ = AlgebraicClosure F`; `F` perfect (char 0 target). State for finite
Galois `L` (the finite-level descent decision) so mathlib's `[FiniteDimensional F L] [IsGalois F L]`
machinery applies.

---

### [DUAL-Q2] ★ CRUX (API GAP) — descent of a curve morphism along finite Galois L/F
- **Status**: open | **File**: `HasseWeil/EC/IsogenyAG/DualDescent.lean` | **Depends on**: DUAL-Q1 | **Type**: theorem (DEEP; REVIEW-PENDING allowed; candidate `/expert-review`)

#### Statement (shape)
```
-- A Gal(L/F)-equivariant L-algebra hom between base-changed function fields descends to an
-- F-algebra hom, and (with the basepoint condition) to an EC.Isogeny over F.
theorem descend_curveMap {E₁ E₂ : Affine F} [E₁.IsElliptic] [E₂.IsElliptic]
    (ξ : CurveMap (E₂.baseChange L)-pkg (E₁.baseChange L)-pkg)
    (hequiv : ∀ σ : L ≃ₐ[F] L, galAct σ ∘ ξ.pullback = ξ.pullback ∘ galAct σ) :
    EC.Isogeny E₂ E₁         -- (shape; the descended isogeny over F)
-- + round-trip: (descend_curveMap ξ hequiv).baseChange L  ≈  ξ
```

#### Proof sketch
1. `ξ.pullback : L(E₁_L) → L(E₂_L)` is `Gal(L/F)`-equivariant (hequiv) ⟹ it maps the fixed field
   `F(E₁)` (Q1c) into the fixed field `F(E₂)` ⟹ restricts to `φ̂* : F(E₂) → F(E₁)` an F-algebra hom.
2. `φ̂*` is nonconstant (transcendence degree preserved — it's a restriction of a field hom that's
   injective on the function field) ⟹ a `CurveMap` over F via II.2.4b (the project's
   CurveMap-from-pullback; basepoint via `reflects_ordAtInfty`, RamificationInfty.lean:132, HAVE).
3. Round-trip: base-changing the descended `φ̂*` back to L recovers `ξ.pullback` (faithfully-flat:
   `id ⊗ φ̂*` on `L ⊗_F F(E₂) = L(E₂_L)` is `ξ.pullback`), because both are L-linear and agree on
   the F(E₂)-generators. mathlib `FaithfullyFlat/Descent` for uniqueness of the descent.

#### Sources
Silverman footnote 1 p.83 (the implicit perfect-field descent); II.2.4b (p.20, field-inclusion ⟹
map, "general K" clause); standard Galois/faithfully-flat descent (Stacks `0CDR`/`0CDQ`).

#### Generality / HONEST NOTE
**This is the deep API gap** — `CurveMap` Galois descent does not exist in the project and is only
partially supported by mathlib. Expect multi-hundred LOC. If the round-trip (3) or the
CurveMap-from-restricted-pullback (2) resists, REVIEW-PENDING the sub-leaf and file an
`/expert-review` question ("cleanest finite-Galois descent of a function-field morphism to a
`CurveMap`, given mathlib's faithfully-flat descent + finite-Galois fixedField"). A scaffold with the
statement + sorries is a valid landing point on this dev branch.

---

### [DUAL-Q3] φ̂_K̄ is Galois-equivariant (from uniqueness)
- **Status**: open | **File**: `HasseWeil/EC/IsogenyAG/DualDescent.lean` | **Depends on**: DUAL-Q1 | **Type**: theorem

#### Statement (shape)
```
theorem dual_baseChange_galEquiv {E₁ E₂ : Affine F} [E₁.IsElliptic] [E₂.IsElliptic]
    (φ : EC.Isogeny E₁ E₂) (φ̂L : the K̄/L dual of φ.baseChange) (σ : L ≃ₐ[F] L) :
    galAct σ (φ̂L.pullback) = φ̂L.pullback     -- equivariance (shape)
```

#### Proof sketch
1. `φ̂L ∘ φ_L = [m]_L` (defining property of the dual over L/K̄, HAVE).
2. Apply `galAct σ`: since `φ`, `[m]` are F-rational, `φ_L` and `[m]_L` are σ-fixed; so
   `(galAct σ φ̂L) ∘ φ_L = [m]_L` too.
3. Uniqueness of the dual over L/K̄ (`compose_right_cancel` / II.2.3 cancellation, CanonicalDual.lean,
   HAVE) ⟹ `galAct σ φ̂L = φ̂L`. — Leaf composing HAVE pieces + Q1's action.

#### Sources
Silverman III.6.1a uniqueness (p.81, *"(φ̂−φ̂′)∘φ=[0] ⟹ φ̂=φ̂′ by II.2.3"*).

---

### [DUAL-Q4] ★ MILESTONE — assemble `universalDualWitness_of_charZero` + discharge the label gate
- **Status**: REDUCED to 1 named residual (`rationalRangeIncl_of_separable`); REVIEW-PENDING — see Progress | **File**: `HasseWeil/EC/IsogenyAG/DualDescent.lean` (+ edit `IsogenyClassLabel.lean`) | **Depends on**: DUAL-Q2, DUAL-Q3 | **Type**: theorem

#### Statement
```
theorem universalDualWitness_of_charZero (F : Type*) [Field F] [DecidableEq F] [CharZero F] :
    UniversalDualWitness F
-- corollary: IsIsogenous is symmetric over a char-0 field; and the un-gated label lemmas:
theorem IsogenyClassTable.index_unique_charZero ...   -- IsogenyClassLabel without the hw hypothesis
```

#### Proof sketch
1. Fix `φ : EC.Isogeny E₁ E₂` over F. `K̄ = AlgebraicClosure F`. char 0 ⟹ `φ` separable.
2. Base-change: `φ_K̄ := baseChangeIsogeny φ` (HAVE) with its CoordHom (`baseChangeCoordHom`, HAVE)
   ⟹ `PullbackEvaluation` (`pullbackEvaluation_of_coordHom`, HAVE).
3. `φ̂_K̄ := exists_dual_of_pullbackEvaluation_general …` over K̄ (HAVE; the
   `OneSubPullbackEvaluation.lean:374` pattern). [φ̂ defined over a finite Galois `L/F` — extract.]
4. DUAL-Q3 ⟹ `φ̂_K̄`/`φ̂_L` is `Gal(L/F)`-equivariant.
5. DUAL-Q2 `descend_curveMap` ⟹ `φ̂ : EC.Isogeny E₂ E₁` over F, with `φ̂ ∘ φ = [m]` (round-trip +
   base-change faithfulness).
6. Package as `HasDualWitness φ` (ν = [m], `hincl` from `φ̂`'s existence, `hbase` HAVE) ⟹
   `Nonempty φ.HasDualWitness` for arbitrary φ ⟹ `UniversalDualWitness F`.
7. Discharge the gate: `IsIsogenous.symm_of (universalDualWitness_of_charZero F)`; replace the `hw`
   hypothesis in `IsogenyClassLabel.index_unique`/`classLetter_eq_of_isogenous` with char-0
   corollaries (no carried witness).

#### Sources
Silverman III.6.1 (existence, pp.81–82). Assembly of all the above.

#### Generality
`[CharZero F]` headline; a `[PerfectField F]` + separable-φ variant is the natural generalization.

#### Progress (2026-06-17, worker `dev/hasse-weil`) — REVIEW-PENDING
The headline `rationalDualCompose_of_charZero` (and hence `universalDualWitness_of_charZero`) is now a
**thin assembly over ONE precisely-named residual**, not a monolithic `sorry`. Build GREEN
(`HasseWeil` 8822 jobs); `hasse_bound_unconditional` stays axiom-clean
`[propext, Classical.choice, Quot.sound]`; `universalDualWitness_of_charZero` shows
`[propext, sorryAx, Classical.choice, Quot.sound]` (the one residual only).

**PROVED (axiom-clean) new lemmas in `DualDescent.lean`:**
- `isSeparable_of_charZero` — char-0 ⟹ `φ.IsSeparable` (EC↔Algebra bridge
  `Isogeny.isSeparable_iff_algebra_isSeparable` + `CurveMap.isAlgebraic_toAlgebra` +
  `charZero_of_injective_algebraMap`; then `Algebra.IsAlgebraic.isIntegral` /
  `Algebra.IsSeparable.of_integral` instances). Axiom-clean (verified).
- `rationalDualCompose_of_hasMulByIntDualWitness` — the **formal compose payoff**: from an
  `F`-rational `HasMulByIntDualWitness φ n hn`, `(mulByIntDual w).compose φ = mulByInt W₁ hn`, via
  `dualOfWitness_comp_pullback` (`(φ̂∘φ)* = [n]*`) + `mulByInt_pullback` + `Isogeny.ext_toCurveMap`.
  Inline of the un-imported `Isogeny.mulByIntDual_compose`. Axiom-clean (verified).
- `hasMulByIntDualWitness_of_rangeIncl` — the **basepoint leaf**: builds the full `[deg φ]`-witness
  from just the range inclusion, via `hbase_of_reflects` + `mulByIntBasepoint_holds` +
  `reflects_ordAtInfty`. (degree positivity = `Isogeny.degree_pos'`.)
- `rationalReverseCompose_of_separable`, `rationalDualCompose_of_charZero` — thin assemblies.

**THE ONE RESIDUAL** (`rationalRangeIncl_of_separable`, `private sorry`):
```
(mulByInt_pullbackAlgHom W₁ (φ.degree : ℤ) _).range ≤ φ.toCurveMap.pullback.range
```
i.e. `Im([deg φ]*) ⊆ Im(φ*)` over `F`, for a separable `φ : E₁ → E₂`. This is the genuine Silverman
III.6.1 core. Its missing inputs (all verified absent from project + mathlib):
1. **General two-curve base-change of an isogeny.** `EC.Isogeny.baseChangeIsogeny`
   (`EC/IsogenyAG/BaseChange.lean:407`) is **endomorphism-only** (`W.baseChange L → W.baseChange L`);
   ticket step 2's "`baseChangeIsogeny φ` (HAVE)" is **WRONG for a general `φ : E₁ → E₂`**. Needs
   `baseChangeXgen`/`baseChangeCoordHom` generalized to distinct source/target curves. MISSING.
2. **Field of definition** (the deep mathlib gap). The K̄-dual from
   `exists_dual_of_pullbackEvaluation_general` lives over the *infinite* `AlgebraicClosure F`; descent
   (`descendIsogeny`) needs it over a *finite* Galois `L/F`. No mathlib lemma "a morphism over
   `AlgebraicClosure F` is defined over a finite (Galois) subextension" in the project's elementary
   function-field framework. `Mathlib.AlgebraicGeometry.SpreadingOut` is scheme-theoretic and not
   bridged. MISSING (genuine stop-loss).
3. **Full base-changed-pullback equivariance** (Q3 residual). `descendIsogeny` needs the K̄-dual's
   pullback `Gal(L/F)`-equivariant on **all** of `F(C_L)`; `galEquivariant_baseChange_on_image`
   covers only the image of `F(E)` (the easy half). MISSING.

Once (1)–(3) land, the round-trip (`functionFieldMap_comp_descendPullback` + injectivity +
mulByInt/compose base-change faithfulness) transports the K̄ range inclusion to the F level.

---

### [CLEANUP-DUAL-FINAL] /cleanup on DualDescent.lean
- **Status**: open | **Depends on**: DUAL-Q4 | **Type**: cleanup
- After the arc lands (even partially), tidy `DualDescent.lean`; per AINTLIB, real `/cleanup` happens
  on `main` after the PR, so this is a light dev-branch pass only.

---

## Notes
- **Finite-level descent** (plan's key decision): extract the finite Galois `L/F` over which `φ̂_K̄`
  is defined; run Q1–Q3 over `L/F` (finite `Gal(L/F)`, mathlib `[IsGalois F L] [FiniteDimensional F L]`),
  not over the infinite `Gal(K̄/F)`.
- **Alternative considered and rejected** (less tractable): field-general `#ker=deg` + field-general
  `hgcomm` — both are deep K̄-only residuals with no descent path; the audit ranked descent above them.
- **Skeleton**: `DualDescent.lean` holds `universalDualWitness_of_charZero` (+ the gate corollaries)
  as `sorry` now (elaborates against existing types); Q1/Q2/Q3 internals are filled as the arc
  proceeds. DUAL-Q2's deep sub-leaves may remain `sorry`/REVIEW-PENDING.
