# CHARTER-A-CMP scoping pass + leaf plan (beastmode-A, 2026-07-11)

FIRST ACT per v10.141: scope the three consumers of the merged [OWNER-FLW] characterization +
the PoleSheaf heartbeat debt; board the leaf plan. Read/diff only; verify-before-work applied
(the map_id/T-A3 lesson — several "consumers" are already partly wired).

## The characterization API (merged, `EllipticCurve/Comparison.lean` — my held file)

For a globally-presented Weierstrass model `projModel W`:
- `locallyWeierstrass_projModel W [W.IsElliptic]` (:243) — elliptic ⟹ LW.
- `isElliptic_of_fibrewiseElliptic_projModel W (h : FibrewiseElliptic …)` (:300) — fibrewise ⟹ elliptic
  (**consumes my `pointedIso_exists_variableChange`** = T-W7.1b).
- `locallyWeierstrass_projModel_iff_isElliptic W` (:414), `fibrewiseElliptic_iff_locallyWeierstrass_projModel W` (:427).
- ⚠ **Scope limit (docstring, :424):** these are for a family *already supplied with one global
  Weierstrass equation*. "The unresolved general comparison is precisely the construction of such an
  equation Zariski-locally from an abstract smooth proper family." So the *chartless* consumers need a
  local-Weierstrass-equation construction, THEN the characterization chart-wise.

## Consumer inventory (verify-before-work — genuine open leaves in **bold**)

### [CMP-a5] — FP4's chartless [a5] core: `locallyWeierstrass_quotientπ` (EngineDescent.lean:633, **SORRY**)
- The route-(a) engine (`exists_ellipticCurveGeom_quotient`, :674) is **sorry-free modulo this one leaf**.
  `isProper_of_locallyWeierstrass` (:571) and `smoothOfRelativeDimension_of_locallyWeierstrass` (:599,
  **already wired to `projModel_smooth`** = T-A3, WeierstrassModel:1814) both consume a `LocallyWeierstrass`
  witness and are PROVEN. So the entire [a5] gap is: `[Finite G] [IsAffine X]` free action ⟹ the quotient
  `π' : E/G ⟶ X/G` is `LocallyWeierstrass`.
- **Bridge:** Zariski-locally on `X/G`, exhibit a global Weierstrass equation for `E/G` (from the
  quotient's fibrewise-elliptic + smooth-proper-genus-1 structure), i.e. locally `E/G ≅ projModel W`,
  then `fibrewiseElliptic_iff_locallyWeierstrass_projModel`. This is exactly the "chartless" step the
  characterization docstring flags as the remaining work; **compat-hypotheses are recorded by FP4** —
  locate them at execution (their `LocalModelData`/`PresentedCurve`-style pins).
- **Placement/seam:** the leaf lives in `EngineDescent.lean` (fable-P4's file). Build the bridge as a
  standalone lemma in a **new `EllipticCurve/ComparisonConsumers.lean`** (mine, imports Comparison), then
  fable-P4 consumes it to close `locallyWeierstrass_quotientπ` — coordinate on the board (no shared edit).
- **Value:** HIGHEST — closing this flips FP4's KM 4.7 engine fully axiom-clean. Foundational for [CMP-YFGEOM].

### [CMP-Mell] — the `M_ell^W` eso-upgrade (MellWeierstrass.lean / MellWStack.lean)
- `presentationFunctor_essSurj (E : PresentedCurve S)` (:638) is **already PROVEN** (for *presented* curves,
  via `E.pres_*`). So the eso-upgrade is a **broader** statement — essential surjectivity onto *abstract*
  elliptic curves (every `W.IsElliptic` presents), which the characterization (`locallyWeierstrass_projModel_iff_isElliptic`)
  now makes in-tree substance (PIC0's old off-limits item). **Leaf: locate/state the abstract-curve eso**
  (likely a `MellWStack` statement, not yet in-tree) and discharge via the iff. Medium; needs the exact
  target located at execution (flagged — do not assume it's a fresh sorry).

### [CMP-YFGEOM] — NEW-Y1's general form: `exists_representing_smooth_affine` (YFullRoute.lean, **SORRY**)
- The [YF-GEOM] geometric computation (KM Cor 4.7.1): SOME representing object with `Smooth ∧ IsAffineHom`
  structure map. Consumes the engine (proper+smooth from LW, via [CMP-a5]) + the characterization.
- **Depends on [CMP-a5]** (the engine's LW→smooth+proper chain). **Seam with NEW-Y1** (YFullRoute is theirs,
  CHARTER-YFULL): I provide the general-form bridge lemma; they assemble in YFullRoute. Board the seam.

### [CMP-DEBT] — PoleSheaf heartbeat debt (PoleSheaf.lean, 9 registered raises)
- 5× `maxHeartbeats 800000` (:261, :484, :655, :692, :845) + 4× `maxHeartbeats 1200000` (:1227, :1396,
  :1490, :1635). `/buzz-decompose` one raise at a time, **no statement changes**, `#print axioms` unchanged.
- Independent of the three consumers; interleave as cooldown. Order: the four 1200k raises first (heaviest
  debt), then the 800k. Each: extract the heartbeat-heavy sub-term to its own lemma (its own budget).

### [CMP-DEBT] execution log (beastmode-A)
The 9 raises + their guarded decls (all whnf-heavy sheaf-of-modules `change`/`simp only` chains):
`idealModuleAppIdealIso_coe` (:265, 800k), `…_coe_map_localIdealElement` (:489, 800k),
`localIdealGeneratorHom_chartBasicOpen_formula` (:660, 800k) / `…_bijective` (:695, 800k),
`localIdealGeneratorHom_comp_restrictIdealModuleToUnit` (:848, 800k), `pullbackUnitIso_comp` (:1228, 1200k),
`pullbackLocalIdealGeneratorIso_hom_comp_toUnit` (:1397, 1200k), `idealModuleBaseChangeHom_isIso_on_affine`
(:1493, 1200k), `idealModuleBaseChangeHom_isIso` (:1637, 1200k).
- **Raise 1/9 `idealModuleAppIdealIso_coe`:** ⚠ NOT stale (removing the raise → `whnf` timeout at 200k),
  and profiling exceeds 120 s — genuine giant-composite whnf (unfolding `idealModuleAppIdealIso`/
  `idealModule`/`idealModuleRaw`). Needs the faith-infra opacity split under the no-statement-change
  constraint: extract the post-`simp only` kernel-iso computation (`change`+`rw` chain →
  `PreservesKernel.iso_hom`/`kernelComparison_comp_ι`/`rfl`) into a private helper with its own budget,
  possibly a 4-way split (800k/200k = 4×).
- **★ STALENESS SCAN RESULT (all 9 tested in one `lake build`): 7 of 9 raises are BUMP-STALE.** Removing
  all 9 → only **2** genuine `whnf` timeouts (200k): `idealModuleAppIdealIso_coe` (was 800k) and
  `pullbackLocalIdealGeneratorIso_hom_comp_toUnit` (was 1200k); the other errors were "unknown constant"
  cascades downstream of those two. Confirmed: build **GREEN (3099 jobs, 0 heartbeat errors)** with the 7
  stale raises removed and only the 2 genuine ones kept. **7/9 of the heartbeat debt eliminated, no
  statement changes** (removing a `maxHeartbeats` budget annotation cannot affect axioms). Banked.
- **REMAINING (2/9):** `idealModuleAppIdealIso_coe` (800k) + `pullbackLocalIdealGeneratorIso_hom_comp_toUnit`
  (1200k) — genuine giant-composite whnf; profiling >120 s. Surgical multi-way extraction of the post-`simp`
  kernel-iso computation into own-budget private helpers (faith-infra pattern), one at a time.
- **Surgery-1 attempt finding (banked for fresh-context resume):** extracting the kernel-comp tail at the
  `change`-to-`ofEq` boundary FAILS — the tail needs `x` in the *evaluated-sheaf* type
  `(evaluation).obj (idealModule f)`, but the helper receives it as `Γ(idealModule f, U)`; the type
  normalization is supplied precisely by the setup's `simp only [idealModule, idealModuleRaw]`, so the
  split can't cross that boundary cleanly (error: `x` type mismatch, `Functor.obj ?m (kernel ?m)`). The
  correct refactor states the helper with `x` in the post-`simp` evaluated type (or splits at the
  `simp only`/`change A` boundary instead, isolating the sheafification-unfold sink). A fresh-context
  surgical pass, low-leverage (2 of 9). File reverted to the committed 7×-win green state.

## Leaf plan (ordered; T-W7a closer-backup interrupt outranks all)

1. **[CMP-a5]** `locallyWeierstrass_quotientπ` bridge (new `ComparisonConsumers.lean` + FP4 seam) — foundational.
2. **[CMP-YFGEOM]** general-form bridge (after [CMP-a5]; NEW-Y1 seam).
3. **[CMP-Mell]** abstract-curve eso (independent; locate target first).
4. **[CMP-DEBT]** PoleSheaf 9 raises via /buzz-decompose (cooldown/interleave).

## Coordination boundaries (holder's stream — I own Comparison.lean; consumers are other lanes' files)
- EngineDescent.lean = **fable-P4**; YFullRoute.lean = **NEW-Y1**; MellW* = **PIC0/holder**. Wire via
  standalone bridge lemmas in my own `ComparisonConsumers.lean` that they import — minimise cross-lane edits;
  board each seam at session start. verify-before-work each target's live sorry-state before touching.
