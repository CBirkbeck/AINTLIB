/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.Moduli.EngineDescent
import ModularCurves.Moduli.EngineMouthCharts

/-!
# Route (a): the geometric core `exists_localModel_core_at` and the quotient assembly

This module is split off from `Moduli/EngineDescent.lean` on purpose.  Discharging the Stage-3
`hpres` obligation inside `exists_localModel_core_at` consumes the semilocal chart-gluing theorem
`MouthCharts.exists_invariant_away_presentation` (`Moduli/EngineMouthCharts.lean`), whose import
transitively pulls in `EllipticCurve/InvariantDifferential`'s enriched instance set.  Importing
that set into `EngineDescent` regresses two heavy Weierstrass-model proofs there
(`exists_coboundary_spread_away`, `exists_localModel_core_of_presentation`) to 200000-heartbeat
`isDefEq`/`whnf` timeouts (measured 2026-07-21).

Those two proofs therefore stay in `EngineDescent` (which does **not** import `EngineMouthCharts`),
and the *consumers* — the geometric core `exists_localModel_core_at` and the route-(a) quotient
assembly downstream of it — live here, where `EngineMouthCharts` is imported and the `hpres`
obligation is closed by `exact MouthCharts.exists_invariant_away_presentation G p`.  The
lower-layer lemmas the moved declarations consume remain in `EngineDescent` (un-privated where a
cross-file reference now requires it).  Nothing in this file does heavy scheme-term `isDefEq`, so
it elaborates without regression.
-/

universe u

open CategoryTheory Limits AlgebraicGeometry

namespace ModularCurves.RouteA

open WeierstrassCurve
open scoped Pointwise

variable {G : Type u} [Group G] {X : Scheme.{u}} {C : EllipticCurveGeom X}
  {σ : SchemeAction G X} {σE : SchemeAction G C.E}

/-! #### The `[a5]` reduction: splitting off the section-pair gap

`locallyWeierstrass_quotientπ` below quantifies over a pair `(π', zero')` carrying the descent
compatibilities `hπ'c`/`hzero'c` tying it to the descended structure maps (the board's v10.94
owed statement fix — for a wild pair the statement is FALSE, see the deleted `[a5-pair]`
counterexample in the git history). `locallyWeierstrass_quotientπ_of_compat` is the true,
board-owned `[a5]` content. Its engine consumption is now PROVEN in full generality
(`lw_chart_at_of_localModel`, no global model needed); the ONE residual leaf is the geometric
core `exists_localModel_core_at` — the a5-P-loc semilocal gluing — from which the full localized
model package `exists_localModel_package_at` is assembled (`descendFixedAway`). The empty-base
case and the assembly are proven. -/

open WeierstrassCurve in
/-- **([a5-P-loc], the geometric core — THE residual leaf, board-owned)** At every prime `s` of
`Aᴳ = Γ(X,⊤)ᴳ` there is an invariant `a ∉ s` over whose basic open the curve acquires a global
Weierstrass model compatible with the `G`-action: the model `W₀R / A_a`, with `projModel W₀R`
presented as the restriction of `E` along `Spec A_a ⟶ Spec A ≅ X` (`ρR`/the pullback
square/the zero-leg), the `VariableChange` cocycle `CvcR / A_a` presenting the geometric action
through `ρR` (T-W7.1b at the `A_a`-level), and the coboundary `E` splitting `CvcR` over `A_a`
(`CvcR g = E * (g • E)⁻¹`).

This is the whole geometric content. `exists_localModel_package_at` peels off the Hilbert-90
descended model `W₁ / (Aᴳ)_a` for free (`E⁻¹ • W₀R` is `G`-invariant, so `descendFixedAway`
descends it), and `lw_chart_at_of_localModel` then consumes the full package and lands the
`LocallyWeierstrass` chart at `s` (see `locallyWeierstrass_quotientπ_of_compat` below).

With a *global* model the core is immediate (`W₀R := W₀.map (algebraMap _ _)`,
`ρR := projModelBaseChange ≫ φ.inv`, `CvcR g := (Cvc g).map _`, `E` from `exists_coboundary` —
this is how `locallyWeierstrass_quotientπ_of_globalModel` specializes), but in general a global
model is obstructed by the class of `ω` in `Pic Γ(X,⊤)`, and the core must be produced
semilocally:

Proof state (KM 2.2.5–2.2.6 + the a5-P-loc board; Stages per board v10.339/v10.340/v10.343):
* **Stages 1–2 (PROVEN, in-body).** The free base action `hfreeA`, and the semilocalization at
  `s`: `S = s.primeCompl.map (algebraMap Aᴳ A)`, the localized action on `L := Localization S`
  (`localizationInvariant`), `Lᴳ` LOCAL (`isLocalRing_fixedPoints_of_isLocalization`), freeness
  `hfreeL` (`isFreeAlgebraAction_of_isLocalization`).
* **Stage 3 (THE RESIDUAL — the `hpres` sorry).** Produce the presentation at an invariant
  basic open: `a₁ ∉ s`, an elliptic `W₀R₁ / A_{a₁}` and `ρR₁ : projModel W₀R₁ ⟶ E` with the
  pullback square against `Spec A_{a₁} → Spec A ≅ X` and the zero-leg. Route: the fibre of
  `Spec A → Spec Aᴳ` over `s` is one finite `G`-orbit (`invariantsπ_apply_eq_iff` +
  `invariantsπ_surjective`, CITE not re-prove); extract per-point charts from `C.localModel`
  via `EllipticCurveGeom.atlas` / `WeierstrassAtlasData` / `LocalPresentation` and shrink to
  basic opens `D(f_i)` covering `Spec L`; normalize the chart-transition `u`-components to `1`
  by the **semilocal unit-cocycle split**
  (`SemilocalUnitSplit.exists_units_eq_mul_of_span_eq_top`,
  ForMathlib/SemilocalUnitCocycleSplit — the ω/`OmegaBasis` bridge of residual (i) is BYPASSED;
  the file is sorry-free and axiom-clean) so the chart-difference
  cocycle `InvariantDifferential.transVC` lands in the nilpotent translation group
  `T = {(1,r,s,t)}`; split that chart-Čech cocycle by the partition-of-unity affine-Čech
  vanishing (`IsLocalizedModule.exists_sub_liftOfLE_eq_of_span_eq_top`,
  ForMathlib/AffineCechH1 n-cover form — residual (ii) CLOSED, axiom-clean); correct the
  charts (`pointedIso_hom_of_transVC_eq_one`), glue the coefficients
  (structure-sheaf sheaf condition) to `W₀L / L` and spread them to a single `a₁ ∉ s`; glue the
  presentation `ρR₁` natively over `A_{a₁}` (`Scheme.OpenCover.glueMorphisms` +
  `glueMorphisms_hf_of_agree`; legs by `isPullback_projModelBaseChange` and
  `projModelZero_baseChange`) — F's direct-over-`A_a` route, board v10.339 finding 2 (NO EGA IV
  §8 morphism-spreading).
* **Stages 4–5 (PROVEN — `exists_localModel_core_of_presentation`).** Stage 4
  (`exists_cocycle_hρact_of_presentation`) turns the presentation into the cocycle
  `CvcR`/`hCvcR`/`hρact`; Stage 5 (`exists_coboundary_spread_away`) splits it over `L`
  (`exists_coboundary`, `Lᴳ` local) and spreads the coboundary `E` to `D(aF)`, `a₁ ∣ aF`;
  the model/presentation/cocycle shrink `D(a₁) → D(aF)` by base change
  (`actLoc_baseChange` for `hρact`). So the ONE residual gap is exactly Stage 3 (`hpres`). -/
private theorem exists_localModel_core_at [Finite G] [IsAffine X]
    (hact : IsCurveAction σ C σE)
    (hfreeX : ∀ γ : G, γ ≠ 1 → ∀ (T : Scheme.{u}) (t : T ⟶ X), t ≫ σ.hom γ = t → IsEmpty T) :
    letI := σ.gammaMulSemiringAction (isStableOpen_top σ)
    ∀ _s : ↥(Spec (CommRingCat.of (FixedPoints.subalgebra ℤ ↑Γ(X, ⊤) G))),
    ∃ (a : FixedPoints.subring ↑Γ(X, ⊤) G) (_ : a ∉ _s.asIdeal)
      (W₀R : WeierstrassCurve (Localization.Away ((a : ↑Γ(X, ⊤))))),
      W₀R.IsElliptic ∧
      ∃ ρR : projModel W₀R ⟶ C.E,
        IsPullback (projModelπ W₀R) ρR
          (Spec.map (CommRingCat.ofHom (algebraMap ↑Γ(X, ⊤)
            (Localization.Away ((a : ↑Γ(X, ⊤))))))) (C.π ≫ X.isoSpec.hom) ∧
        projModelZero W₀R ≫ ρR
          = Spec.map (CommRingCat.ofHom (algebraMap ↑Γ(X, ⊤)
              (Localization.Away ((a : ↑Γ(X, ⊤)))))) ≫ X.isoSpec.inv ≫ C.zero ∧
        ∃ (CvcR : G → VariableChange (Localization.Away ((a : ↑Γ(X, ⊤)))))
          (hCvcR : ∀ g, CvcR g
            • (W₀R.map (MulSemiringAction.awayHom (fun g' : G => a.2 g') g)) = W₀R),
          (∀ g, (eqToHom (congrArg projModel (hCvcR g).symm)
              ≫ (projModelVCIso (CvcR g)
                  (W₀R.map (MulSemiringAction.awayHom (fun g' : G => a.2 g') g))).hom
              ≫ projModelBaseChange (MulSemiringAction.awayHom
                  (fun g' : G => a.2 g') g) W₀R) ≫ ρR = ρR ≫ σE.hom g) ∧
          ∃ (E : VariableChange (Localization.Away ((a : ↑Γ(X, ⊤))))),
            ∀ g : G, CvcR g
              = E * (E.map (MulSemiringAction.awayHom (fun g' : G => a.2 g') g))⁻¹ := by
  letI := σ.gammaMulSemiringAction (isStableOpen_top σ)
  intro s
  classical
  -- ### Stages 1–2 (the `a`-independent semilocalization at `s`) — BANKED, sorry-free.
  -- Route input: the base `G`-action on `A := Γ(X,⊤)` is free.
  have hfreeA : IsFreeAlgebraAction G ℤ ↑Γ(X, ⊤) :=
    σ.isFreeAlgebraAction_of_free (isStableOpen_top σ) (isAffineOpen_top X) hfreeX
  -- The prime of the fixed subring below `s` (`FixedPoints.subring`/`subalgebra` carriers are
  -- defeq, cf. mathlib `RingTheory/Invariant/Basic`), transported to `Rᴳ = FixedPoints.subring`.
  set p : Ideal (FixedPoints.subring ↑Γ(X, ⊤) G) := s.asIdeal with hpdef
  haveI : p.IsPrime := s.isPrime
  -- Part 1 of `exists_away_invariant_descent` (WeierstrassInvariantLocal:363–371): semilocalize
  -- `A` at `s`.  `S = image of (Aᴳ \ p)`; `Localization S` carries the localized `G`-action
  -- (`localizationInvariant`), is nontrivial, its fixed subring `(Aᴳ)_p` is a LOCAL ring
  -- (`isLocalRing_fixedPoints_of_isLocalization`), and the action stays free
  -- (`isFreeAlgebraAction_of_isLocalization`).
  set S : Submonoid ↑Γ(X, ⊤) :=
    p.primeCompl.map (algebraMap (FixedPoints.subring ↑Γ(X, ⊤) G) ↑Γ(X, ⊤)) with hSdef
  have hS : ∀ (g : G), ∀ x ∈ S, g • x = x := primeComplImage_fixed p
  letI actL : MulSemiringAction G (Localization S) := MulSemiringAction.localizationInvariant hS
  have hcomp : ∀ (g : G) (r : ↑Γ(X, ⊤)),
      g • (algebraMap ↑Γ(X, ⊤) (Localization S) r)
        = algebraMap ↑Γ(X, ⊤) (Localization S) (g • r) :=
    fun g r => MulSemiringAction.locHom_algebraMap hS g r
  haveI : Nontrivial (Localization S) := nontrivial_localization_primeComplImage p
  -- `Lᴳ = (Aᴳ)_p` is LOCAL; the localized action stays free.  (No type ascription: mirrors
  -- WeierstrassInvariantLocal:370–371 to avoid the `Algebra ℤ (Localization S)` diamond.)
  haveI := isLocalRing_fixedPoints_of_isLocalization p hcomp
  have hfreeL := isFreeAlgebraAction_of_isLocalization hcomp hfreeA
  -- ### Stage 3 (THE CRUX — the ONE residual): the localized presentation.  Over the semilocal
  -- `L := Localization S` above, glue a global Weierstrass model `W₀L / L` presenting the
  -- base-changed curve, then spread the finitely many ring coefficients + the corrected chart
  -- isos to a basic open `D(a₁)`, `a₁ ∉ p`, and glue `ρR₁` NATIVELY over `A_{a₁}` (board
  -- v10.339 finding 2 — no EGA IV §8).
  --
  -- **Stages 3a–3b are DONE, AXIOM-CLEAN — `Moduli/EngineMouthCharts.lean` (T-E4D session
  -- 2026-07-21).**  The single package theorem
  --   `MouthCharts.exists_cover_transVC_coboundary (C := C) S`
  -- yields, for any `[Finite (MaximalSpectrum (Localization S))]` (supplied by
  --   `MouthCharts.finite_maximalSpectrum_localization G p` — no `letI` needed, the
  --   statement does not mention the action):
  -- a finite basic-open chart cover `f : ι → A`, pointed Weierstrass charts
  -- `P i : LocalPresentation C ⟨X.basicOpen (f i), _⟩` from the atlas, the span condition
  -- `Ideal.span (range (algebraMap A L ∘ f)) = ⊤` (the `D(fᵢ)` cover `Spec L`), and a
  -- per-chart `VariableChange` cochain `D i / L[1/fᵢ]` whose coboundary is the chart
  -- transition cocycle pushed into the join-localizations of `L`:
  --   `(transVC of restricted charts).map (sectionsToLoc …) = (D i) * (D j)⁻¹`.
  -- Under the hood (all axiom-clean): the chart extraction
  -- `MouthCharts.exists_presentation_cover_span_top` (one chart per maximal of the semilocal
  -- `L`), the section-level Čech law `MouthCharts.transVC_restrict_trans`, the vocabulary
  -- bridge `MouthCharts.sectionsToLoc`/`vc_map_sectionsToLoc_factor`, and the layerwise
  -- `VariableChange`-Čech splitting engine
  -- `SemilocalUnitSplit.exists_variableChange_eq_mul_of_span_eq_top`
  -- (ForMathlib/SemilocalVariableChangeSplit: `u`-layer via `Pic(semilocal) = 0`
  -- [`exists_units_eq_mul_of_span_eq_top`], then the abelian `(r,s)`- and central `t`-layers
  -- via the n-cover affine-Čech `H¹` vanishing [`exists_sub_resLoc_eq_of_span_eq_top`]).
  --
  -- **Stage 3c-α is DONE, AXIOM-CLEAN (T-E4D session 2026-07-21):**
  --   `MouthCharts.exists_cover_glued_model (C := C) S` — the corrected charts GLUE to a
  --   global Weierstrass model `W₀L / L`: cover `f`/`P`, pairwise units `hU`, correction
  --   cochain `D i / L[1/fᵢ]`, `W₀L` with `IsUnit W₀L.Δ`, the per-chart identity
  --   `W₀L = D i • (P i).W` over `L[1/fᵢ]` (through `sectionsToLoc`), and the corrected
  --   coboundary `transVC = (D i)⁻¹ * (D j)` on overlaps.  Engine: the NEW affine Čech
  --   `H⁰` sheaf condition (`ForMathlib/AffineCechH0.lean`:
  --   `exists_algebraMap_eq_of_span_eq_top` / `isUnit_of_span_eq_top` /
  --   `exists_weierstrassCurve_map_eq_of_span_eq_top`, all clean — glued sections via the
  --   trivial-cocycle `gluedSubmodule` + `isLocalizedModule_gluedProj` + mathlib
  --   `bijective_of_isLocalized_span`).
  -- **The `hpres`-SHAPED frontier theorem now EXISTS:**
  --   `MouthCharts.exists_invariant_away_presentation G p`
  --   (`Moduli/EngineMouthCharts.lean`) states THIS `hpres` verbatim — over any
  --   `[Finite G] [MulSemiringAction G Γ(X,⊤)]` and prime `p` of the fixed subring — and
  --   consumes Stages 1–2 + 3a–3c-α in its body; its single `sorry` is the pure Stage
  --   3c-β/γ residual (β: invariant-denominator spread, Part-2 pattern; γ: native glue
  --   over `D(a₁)` via `glueMorphisms` + `isPullback_of_iSup_eq_top`), with the full
  --   β1/β2/γ1–γ4 recipe in its continuation comment (incl. the localization-tower
  --   clearing calculus: mathlib `IsLocalization.localization_localization_isLocalization`
  --   + `isLocalization_of_submonoid_le`).  Already banked clean beyond α: the span-witness
  --   spread `exists_invariant_span_away` (wired into the frontier body), the cover lemma
  --   `basicOpen_le_iSup_basicOpen_mul`, and the corrected-chart transition factorization
  --   `transVC_ofVC_restrict_pair` (the γ1 group-law core).
  -- **Wiring note (import architecture):** `EngineMouthCharts` is a SEPARATE file because
  -- importing `EllipticCurve/InvariantDifferential` (the `LocalPresentation` calculus) into
  -- THIS file blows the elaboration budget of `exists_localModel_core_of_presentation`
  -- (heartbeat regressions from the enriched instance set — measured 2026-07-21).  When
  -- 3c-β/γ closes there, replace THIS `sorry` by
  --   `exact MouthCharts.exists_invariant_away_presentation G p`
  -- after adding the import — decomposing/`/buzz`-splitting the two slow proofs of THIS
  -- file FIRST (`exists_coboundary_spread_away`, `exists_localModel_core_of_presentation`).
  -- Proof-engineering findings (measured this session): NEVER rw/simp on concrete
  -- localization-tower or `Γ(X,·)`-typed curve terms (whnf blows the 200k budget even for
  -- `simpa only [map_a₁]`) — hoist EVERY algebraic step as a variable-ring barrier lemma
  -- and only APPLY it at the concrete types (`corrected_map_eq`, `smul_map_of_smul`,
  -- `cob_inv_reshape`, `exists_weierstrassCurve_map_eq_of_span_eq_top` are the models);
  -- scheme-point membership through `Spec Γ(X,⊤)` must use term-mode
  -- `(PrimeSpectrum.mem_basicOpen _ _).mp/.mpr` (rw fails on the carrier coercion).
  -- Gotcha (measured): `FixedPoints.subalgebra ℤ (Localization …) G` does NOT
  -- elaborate at a concrete localization (`OreLocalization` `SMul ℤ` diamond) — never spell
  -- it; use the generic-`L` lemmas (`finite_maximalSpectrum_of_isLocalRing_fixedPoints`).
  -- Stages 4–5 are DONE: `exists_localModel_core_of_presentation` (Stage-4 consumption +
  -- `exists_coboundary_spread_away` + the `D(a₁) → D(aF)` shrink) closes the core from `hpres`.
  have hpres : ∃ (a₁ : FixedPoints.subring ↑Γ(X, ⊤) G) (_ : a₁ ∉ p)
      (W₀R₁ : WeierstrassCurve (Localization.Away ((a₁ : ↑Γ(X, ⊤))))),
      W₀R₁.IsElliptic ∧
      ∃ ρR₁ : projModel W₀R₁ ⟶ C.E,
        IsPullback (projModelπ W₀R₁) ρR₁
          (Spec.map (CommRingCat.ofHom (algebraMap ↑Γ(X, ⊤)
            (Localization.Away ((a₁ : ↑Γ(X, ⊤))))))) (C.π ≫ X.isoSpec.hom) ∧
        projModelZero W₀R₁ ≫ ρR₁
          = Spec.map (CommRingCat.ofHom (algebraMap ↑Γ(X, ⊤)
              (Localization.Away ((a₁ : ↑Γ(X, ⊤)))))) ≫ X.isoSpec.inv ≫ C.zero := by
    exact MouthCharts.exists_invariant_away_presentation G p
  obtain ⟨a₁, ha₁, W₀R₁, hell₁, ρR₁, hρsq₁, hρzero₁⟩ := hpres
  exact exists_localModel_core_of_presentation hact hfreeX s a₁ ha₁ W₀R₁ hell₁ ρR₁ hρsq₁
    hρzero₁

open WeierstrassCurve in
/-- **([a5-P-loc], the localized model package — assembled from the geometric core)** The full
localized model package consumed by `lw_chart_at_of_localModel`. It is obtained from the
geometric core `exists_localModel_core_at` — which supplies the localized model `W₀R / A_a`, its
presentation `ρR` (pullback square + zero-leg), the geometric `VariableChange` cocycle `CvcR` with
its action-compatibility `hρact`, and the coboundary `E` splitting `CvcR` over `A_a` — by peeling
off the descended model `W₁ / (Aᴳ)_a`:

`E⁻¹ • W₀R` is `G`-invariant (from `hCvcR` and the coboundary `CvcR g = E * (g • E)⁻¹`), so it
descends along `fixedAwayMap a : (Aᴳ)_a ⟶ A_a` to `W₁` by `descendFixedAway`, and the coboundary
identity is the required `hcob` verbatim. This isolates the whole geometric content into the single
residual sub-leaf `exists_localModel_core_at`.

**[a2-M] consumer note (un-privated v10.329):** exposed (was `private`) so the engine mouth's
`exists_orbit_isAffineOpen` (`Moduli/EngineMouth.lean`, route-1) can consume the localized global
model `W₀R / A_a` and its open-immersion presentation `ρR` at the invariant prime below `π(e)`.
It still carries `sorryAx` transitively through `exists_localModel_core_at` (the a5-P-loc deep
geometric core); that propagation is expected. -/
theorem exists_localModel_package_at [Finite G] [IsAffine X]
    (hact : IsCurveAction σ C σE)
    (hfreeX : ∀ γ : G, γ ≠ 1 → ∀ (T : Scheme.{u}) (t : T ⟶ X), t ≫ σ.hom γ = t → IsEmpty T) :
    letI := σ.gammaMulSemiringAction (isStableOpen_top σ)
    ∀ _s : ↥(Spec (CommRingCat.of (FixedPoints.subalgebra ℤ ↑Γ(X, ⊤) G))),
    ∃ (a : FixedPoints.subring ↑Γ(X, ⊤) G) (_ : a ∉ _s.asIdeal)
      (W₀R : WeierstrassCurve (Localization.Away ((a : ↑Γ(X, ⊤))))),
      W₀R.IsElliptic ∧
      ∃ ρR : projModel W₀R ⟶ C.E,
        IsPullback (projModelπ W₀R) ρR
          (Spec.map (CommRingCat.ofHom (algebraMap ↑Γ(X, ⊤)
            (Localization.Away ((a : ↑Γ(X, ⊤))))))) (C.π ≫ X.isoSpec.hom) ∧
        projModelZero W₀R ≫ ρR
          = Spec.map (CommRingCat.ofHom (algebraMap ↑Γ(X, ⊤)
              (Localization.Away ((a : ↑Γ(X, ⊤)))))) ≫ X.isoSpec.inv ≫ C.zero ∧
        ∃ (CvcR : G → VariableChange (Localization.Away ((a : ↑Γ(X, ⊤)))))
          (hCvcR : ∀ g, CvcR g
            • (W₀R.map (MulSemiringAction.awayHom (fun g' : G => a.2 g') g)) = W₀R),
          (∀ g, (eqToHom (congrArg projModel (hCvcR g).symm)
              ≫ (projModelVCIso (CvcR g)
                  (W₀R.map (MulSemiringAction.awayHom (fun g' : G => a.2 g') g))).hom
              ≫ projModelBaseChange (MulSemiringAction.awayHom
                  (fun g' : G => a.2 g') g) W₀R) ≫ ρR = ρR ≫ σE.hom g) ∧
          ∃ (W₁ : WeierstrassCurve (Localization.Away a))
            (E : VariableChange (Localization.Away ((a : ↑Γ(X, ⊤))))),
            W₁.map (fixedAwayMap a) = E⁻¹ • W₀R ∧
            ∀ g : G, CvcR g
              = E * (E.map (MulSemiringAction.awayHom (fun g' : G => a.2 g') g))⁻¹ := by
  letI := σ.gammaMulSemiringAction (isStableOpen_top σ)
  intro s
  obtain ⟨a, hap, W₀R, hW₀R, ρR, hρsq, hρzero, CvcR, hCvcR, hρact, E, hEcob⟩ :=
    exists_localModel_core_at hact hfreeX s
  -- `E⁻¹ • W₀R` is `G`-invariant, using the coboundary identity and the model's invariance
  have hInv : ∀ g : G,
      (E⁻¹ • W₀R).map (MulSemiringAction.awayHom (fun g' : G => a.2 g') g) = E⁻¹ • W₀R := by
    intro g
    rw [← map_variableChange,
      show E⁻¹.map (MulSemiringAction.awayHom (fun g' : G => a.2 g') g)
          = (E.map (MulSemiringAction.awayHom (fun g' : G => a.2 g') g))⁻¹ from
            map_inv (VariableChange.mapHom _) E,
      show (E.map (MulSemiringAction.awayHom (fun g' : G => a.2 g') g))⁻¹ = E⁻¹ * CvcR g from by
          rw [hEcob g, inv_mul_cancel_left],
      mul_smul, hCvcR g]
  -- descend the invariant model along `fixedAwayMap` to `(Aᴳ)_a`
  obtain ⟨W₁, hW₁⟩ := descendFixedAway a (E⁻¹ • W₀R) hInv
  exact ⟨a, hap, W₀R, hW₀R, ρR, hρsq, hρzero, CvcR, hCvcR, hρact, W₁, E, hW₁, hEcob⟩

/-- The invariants map `Spec A ⟶ Spec Aᴳ` pulls the basic open `D(a)` of an invariant `a`
back to `D((a : A))` — the two are literally defeq as sets (both cut out by `a`). -/
private theorem invariantsπ_preimage_basicOpen {A : Type u} [CommRing A] [MulSemiringAction G A]
    (a : FixedPoints.subring A G) :
    invariantsπ G A ℤ ⁻¹ᵁ (PrimeSpectrum.basicOpen a)
      = (PrimeSpectrum.basicOpen ((a : A)) : (Spec (CommRingCat.of A)).Opens) :=
  TopologicalSpace.Opens.ext rfl

open WeierstrassCurve.Projective HomogeneousIdeal WeierstrassCurve in
attribute [local instance] MvPolynomial.gradedAlgebra in
set_option maxHeartbeats 800000 in
/-- **([a2-M], route-1 — the orbit-in-an-affine-open input, DISCHARGED)** Every `G`-orbit of an
`IsCurveAction` lift `σE` on the total space of a geometric elliptic curve `C/X` over an affine
base with a free `σ`-action lies in an affine open of `E`. This is the geometric heart consumed by
the engine mouth's `exists_orbit_isAffineOpen` (`Moduli/EngineMouth.lean`), replacing KM's silent
appeal to quasi-projectivity (Stacks 01ZY).

Proof (the a5-P-loc package, route 1): at the invariant prime `s := invariantsπ(π(e))` below
`x := π(e)`, `exists_localModel_package_at` supplies an invariant `a ∉ s`, a global elliptic model
`W₀R / Spec A_a`, and a presentation `ρR : projModel W₀R ⟶ E` whose `IsPullback` square against the
basic-open localization `iAA : Spec A_a ⟶ Spec A ≅ X` makes `ρR` an open immersion onto
`π⁻¹(D(a))` (`MorphismProperty.of_isPullback` + `Scheme.Hom.opensRange_pullbackSnd`). The basic
open `D((a:A))` is `G`-stable — `a` is invariant, so `invariantsπ` is constant on the base orbit
(`specSMul_invariantsπ`) — hence the whole orbit of `e` maps into `D(a)`
(`invariantsπ_preimage_basicOpen`, `horbitDa`). The two `projModel` charts push forward along `ρR`
to affine opens of `E` (`IsAffineOpen.image_of_isOpenImmersion` on
`Proj.isAffineOpen_basicOpen`), and the `orbit_mem_isAffineOpen_of_charts` dichotomy runs inside
`π⁻¹(D(a))`: the orbit is either entirely on the zero section (Y-chart, via
`projModelZero_preimage_yChart` and the package's zero-leg `hρzero`) or entirely off it (Z-chart,
via `mem_range_zero_of_not_mem_zChart` + `mem_range_zero_of_smul_mem`).

Carries `sorryAx` transitively through `exists_localModel_package_at` → `exists_localModel_core_at`
(the a5-P-loc deep geometric core) and nothing else. -/
theorem exists_orbit_isAffineOpen_of_curveAction [Finite G] [IsAffine X]
    (hact : IsCurveAction σ C σE)
    (hfreeX : ∀ γ : G, γ ≠ 1 → ∀ (T : Scheme.{u}) (t : T ⟶ X), t ≫ σ.hom γ = t → IsEmpty T)
    (e : C.E) :
    ∃ U : (C.E).Opens, IsAffineOpen U ∧ ∀ γ : G, (σE.hom γ).base e ∈ U := by
  classical
  letI := σ.gammaMulSemiringAction (isStableOpen_top σ)
  -- the invariant prime below `x := π(e)`, and the localized global model there
  set s₀ : ↥(Spec (CommRingCat.of (FixedPoints.subalgebra ℤ ↑Γ(X, ⊤) G))) :=
    (X.isoSpec.hom ≫ invariantsπ G ↑Γ(X, ⊤) ℤ).base (C.π.base e) with hs₀
  obtain ⟨a, hap, W₀R, hW₀R, ρR, hρsq, hρzero, CvcR, hCvcR, hρact, W₁, Ecob, hW₁, hcob⟩ :=
    exists_localModel_package_at hact hfreeX s₀
  -- the localization map `iAA : Spec A_a ⟶ Spec A`, open immersion with range `D(a)`
  set iAA : Spec (CommRingCat.of (Localization.Away ((a : ↑Γ(X, ⊤)))))
      ⟶ Spec (CommRingCat.of (↑Γ(X, ⊤))) :=
    Spec.map (CommRingCat.ofHom (algebraMap ↑Γ(X, ⊤) (Localization.Away ((a : ↑Γ(X, ⊤))))))
    with hiAA
  haveI hiAAoi : IsOpenImmersion iAA := IsOpenImmersion.of_isLocalization ((a : ↑Γ(X, ⊤)))
  have hiAArange : iAA.opensRange = (PrimeSpectrum.basicOpen ((a : ↑Γ(X, ⊤))) :
      (Spec (CommRingCat.of (↑Γ(X, ⊤)))).Opens) := by
    ext1
    exact PrimeSpectrum.localization_away_comap_range _ ((a : ↑Γ(X, ⊤)))
  -- `ρR` is an open immersion (base change of `iAA`)
  haveI hρRoi : IsOpenImmersion ρR :=
    MorphismProperty.of_isPullback (P := @IsOpenImmersion) hρsq hiAAoi
  -- the two `projModel` charts (`Y`-chart, `Z`-chart)
  set chartY : (projModel W₀R).Opens := Proj.basicOpen (quotientGrading (projIdeal W₀R))
    ((quotientGradingHom (projIdeal W₀R)) (MvPolynomial.X 1)) with hchartY
  set chartZ : (projModel W₀R).Opens := Proj.basicOpen (quotientGrading (projIdeal W₀R))
    ((quotientGradingHom (projIdeal W₀R)) (MvPolynomial.X 2)) with hchartZ
  have hchartYaff : IsAffineOpen chartY :=
    Proj.isAffineOpen_basicOpen _ _ (mk_X_mem_quotientGrading_one W₀R 1) one_pos
  have hchartZaff : IsAffineOpen chartZ :=
    Proj.isAffineOpen_basicOpen _ _ (mk_X_mem_quotientGrading_one W₀R 2) one_pos
  -- image-along-open-immersion membership helper
  have hmemimg : ∀ (V : (projModel W₀R).Opens) (p : projModel W₀R) (c : C.E),
      p ∈ V → ρR.base p = c → c ∈ ρR ''ᵁ V := by
    intro V p c hpV hpc
    subst hpc
    show ρR.base p ∈ (↑(ρR ''ᵁ V) : Set ↥C.E)
    rw [Scheme.Hom.coe_image]
    exact ⟨p, hpV, rfl⟩
  -- the invariants-quotient map fixes the base orbit
  have hqfix : ∀ γ : G, σ.hom γ ≫ X.isoSpec.hom ≫ invariantsπ G ↑Γ(X, ⊤) ℤ
      = X.isoSpec.hom ≫ invariantsπ G ↑Γ(X, ⊤) ℤ := by
    intro γ
    rw [← Category.assoc, hom_isoSpec_toRingHom σ γ, Category.assoc,
      show Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom G ↑Γ(X, ⊤) γ))
          = specSMul γ from rfl, specSMul_invariantsπ]
  have hcompfix : ∀ γ : G, σE.hom γ ≫ C.π ≫ X.isoSpec.hom ≫ invariantsπ G ↑Γ(X, ⊤) ℤ
      = C.π ≫ X.isoSpec.hom ≫ invariantsπ G ↑Γ(X, ⊤) ℤ := by
    intro γ
    rw [← Category.assoc (σE.hom γ), hact.π_equivariant γ, Category.assoc, hqfix γ]
  -- the bridge `D((a:A)) = invariantsπ ⁻¹ D(a)`
  have hbridge := invariantsπ_preimage_basicOpen (G := G) (A := ↑Γ(X, ⊤)) a
  -- KEY: every base-orbit point of `x` lies in `D(a)`
  have horbitDa : ∀ γ : G,
      (C.π ≫ X.isoSpec.hom).base ((σE.hom γ).base e) ∈ iAA.opensRange := by
    have hs := (PrimeSpectrum.mem_basicOpen a _).mpr hap
    rw [hs₀] at hs
    intro γ
    rw [hiAArange, ← hbridge]
    show (invariantsπ G ↑Γ(X, ⊤) ℤ).base ((C.π ≫ X.isoSpec.hom).base ((σE.hom γ).base e))
      ∈ PrimeSpectrum.basicOpen a
    have hfix := congrArg (fun m : C.E ⟶ _ => m.base e) (hcompfix γ)
    simp only [Scheme.Hom.comp_apply] at hfix hs ⊢
    rw [hfix]
    exact hs
  -- pointwise lift into `projModel W₀R` for points over `D(a)`
  have hlift : ∀ c : C.E, (C.π ≫ X.isoSpec.hom).base c ∈ iAA.opensRange →
      ∃ p : projModel W₀R, ρR.base p = c := by
    intro c hc
    have hc' : c ∈ (pullback.snd iAA (C.π ≫ X.isoSpec.hom)).opensRange := by
      rw [Scheme.Hom.opensRange_pullbackSnd]; exact hc
    obtain ⟨p', hp'⟩ := Scheme.Hom.mem_opensRange.mp hc'
    have hii : hρsq.isoPullback.hom.base (hρsq.isoPullback.inv.base p') = p' := by
      rw [← Scheme.Hom.comp_apply, hρsq.isoPullback.inv_hom_id]; simp
    refine ⟨hρsq.isoPullback.inv.base p', ?_⟩
    have hcong := congrArg (fun m : projModel W₀R ⟶ C.E => m.base (hρsq.isoPullback.inv.base p'))
      hρsq.isoPullback_hom_snd
    rw [Scheme.Hom.comp_apply] at hcong
    rw [← hcong, hii]
    exact hp'
  -- dichotomy on whether `e` is on the zero section
  by_cases he : e ∈ Set.range C.zero.base
  · -- orbit entirely on the zero section: it lands in the `Y`-chart image
    refine ⟨ρR ''ᵁ chartY, hchartYaff.image_of_isOpenImmersion ρR, fun γ => ?_⟩
    obtain ⟨x', hx'⟩ := mem_range_zero_of_smul hact γ he
    have hx'π : C.π.base ((σE.hom γ).base e) = x' := by
      rw [← hx', ← Scheme.Hom.comp_apply, C.zero_π]; simp
    have hmemrange : X.isoSpec.hom.base x' ∈ iAA.opensRange := by
      have h := horbitDa γ
      rw [Scheme.Hom.comp_apply, hx'π] at h
      exact h
    obtain ⟨w, hw⟩ := Scheme.Hom.mem_opensRange.mp hmemrange
    refine hmemimg chartY ((projModelZero W₀R).base w) ((σE.hom γ).base e) ?_ ?_
    · have hmem : w ∈ projModelZero W₀R ⁻¹ᵁ chartY := by
        rw [hchartY, projModelZero_preimage_yChart W₀R]; trivial
      exact hmem
    · have hz : (projModelZero W₀R ≫ ρR).base w = (iAA ≫ X.isoSpec.inv ≫ C.zero).base w := by
        rw [hρzero]
      rw [Scheme.Hom.comp_apply] at hz
      rw [hz, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hw]
      have hinv : X.isoSpec.inv.base (X.isoSpec.hom.base x') = x' := by
        rw [← Scheme.Hom.comp_apply, X.isoSpec.hom_inv_id]; simp
      rw [hinv, hx']
  · -- orbit entirely off the zero section: it lands in the `Z`-chart image
    refine ⟨ρR ''ᵁ chartZ, hchartZaff.image_of_isOpenImmersion ρR, fun γ => ?_⟩
    have he' : (σE.hom γ).base e ∉ Set.range C.zero.base :=
      fun h => he (mem_range_zero_of_smul_mem hact γ h)
    obtain ⟨p, hp⟩ := hlift ((σE.hom γ).base e) (horbitDa γ)
    refine hmemimg chartZ p ((σE.hom γ).base e) ?_ hp
    by_contra hpZ
    obtain ⟨w, hw⟩ := mem_range_zero_of_not_mem_zChart (W := W₀R) (p := p)
      (by rw [hchartZ] at hpZ; exact hpZ)
    apply he'
    refine ⟨X.isoSpec.inv.base (iAA.base w), ?_⟩
    have hz : (projModelZero W₀R ≫ ρR).base w = (iAA ≫ X.isoSpec.inv ≫ C.zero).base w := by
      rw [hρzero]
    rw [Scheme.Hom.comp_apply, hw, hp, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply] at hz
    exact hz.symm

/-- **([a5-compat], the true half — ENGINE PROVEN; residual = the localized model package)**
`locallyWeierstrass_quotientπ` for a section pair carrying the descent compatibilities
`hπ'c`/`hzero'c` of `exists_quotient_π_zero` — the shape the board's owed `[a5]` statement fix
arrives at.

PROVEN via the localized Phase-A engine: per point `s` of `X/G ≅ Spec Aᴳ`
(`exists_quotientIsoSpec_top`), the localized model package `exists_localModel_package_at`
(now assembled from the geometric core `exists_localModel_core_at` — the ONE residual sorry, the
a5-P-loc semilocal gluing, see its docstring for the boarded proof) feeds
`lw_chart_at_of_localModel`, which lands the chart at `s`; `lw_of_baseIso`
transports back along `qiso`. This is the general (`C.localModel`-only) route: `hVtop`
trivialises the **base** atlas `V` only — a global model upstairs is genuinely obstructed
(the class of `ω` in `Pic Γ(X,⊤)`), which is why the model data enters localized at an
invariant basic open `D(a)`, `a ∉ s`. -/
private theorem locallyWeierstrass_quotientπ_of_compat [Finite G] [IsAffine X]
    [IsAffineHom (Limits.pullback.diagonal (Limits.terminal.from X))]
    [IsAffineHom (Limits.pullback.diagonal (Limits.terminal.from C.E))]
    (hact : IsCurveAction σ C σE)
    (V : X → X.Opens) (hVs : ∀ x, σ.IsStableOpen (V x)) (hVa : ∀ x, IsAffineOpen (V x))
    (hVmem : ∀ x, x ∈ V x) (hVtop : ∀ x, V x = ⊤)
    (VE : C.E → (C.E).Opens) (hVEs : ∀ e, σE.IsStableOpen (VE e))
    (hVEa : ∀ e, IsAffineOpen (VE e)) (hVEmem : ∀ e, e ∈ VE e)
    (hfree : ∀ γ : G, γ ≠ 1 → ∀ (T : Scheme.{u}) (t : T ⟶ X), t ≫ σ.hom γ = t → IsEmpty T)
    (hX : Nonempty ↥X)
    (π' : σE.quotient VE hVEs hVEa ⟶ σ.quotient V hVs hVa)
    (zero' : σ.quotient V hVs hVa ⟶ σE.quotient VE hVEs hVEa)
    (hz : zero' ≫ π' = 𝟙 (σ.quotient V hVs hVa))
    (hπ'c : σE.quotientπ VE hVEs hVEa hVEmem ≫ π' = C.π ≫ σ.quotientπ V hVs hVa hVmem)
    (hzero'c : σ.quotientπ V hVs hVa hVmem ≫ zero'
      = C.zero ≫ σE.quotientπ VE hVEs hVEa hVEmem) :
    LocallyWeierstrass π' zero' hz := by
  classical
  cases nonempty_fintype G
  obtain ⟨x₀⟩ := hX
  letI := σ.gammaMulSemiringAction (isStableOpen_top σ)
  obtain ⟨qiso, hqiso⟩ := σ.exists_quotientIsoSpec_top V hVs hVa hVmem hVtop x₀
  have hz'' : (qiso.inv ≫ zero') ≫ (π' ≫ qiso.hom) = 𝟙 _ := by
    rw [Category.assoc, ← Category.assoc zero', hz, Category.id_comp, Iso.inv_hom_id]
  -- the freeness over Γ(X,⊤), upstairs and on the fibre product
  have hfreeA : IsFreeAlgebraAction G ℤ ↑Γ(X, ⊤) :=
    σ.isFreeAlgebraAction_of_free (isStableOpen_top σ) (isAffineOpen_top X) hfree
  have hfreeE := discharge_freeE σ σE hact hfree
  -- the Spec-side local model, per point from the localized model package
  have hspec : LocallyWeierstrass (π' ≫ qiso.hom) (qiso.inv ≫ zero') hz'' := by
    intro s
    obtain ⟨a, hap, W₀R, hW₀R, ρR, hρsq, hρzero, CvcR, hCvcR, hρact, W₁, E, hW₁, hcob⟩ :=
      exists_localModel_package_at hact hfree s
    exact lw_chart_at_of_localModel (π' ≫ qiso.hom) (qiso.inv ≫ zero') hz''
      (σE.quotientπ VE hVEs hVEa hVEmem) (C.π ≫ X.isoSpec.hom) (X.isoSpec.inv ≫ C.zero)
      (isPullback_transport_corner
        (isPullback_quotientπ hact V hVs hVa hVmem hVtop VE hVEs hVEa hVEmem hfree π' hπ'c)
        X.isoSpec qiso rfl rfl hqiso)
      (zeroSq_transport hzero'c hqiso)
      σE.hom (σE.hom_quotientπ VE hVEs hVEa hVEmem)
      (discharge_hlift' VE hVEs hVEa hVEmem hfreeE)
      (discharge_hepi VE hVEs hVEa hVEmem hfreeE)
      (fppf_invariantsπ (G := G) (B := ↑Γ(X, ⊤)) hfreeA).1
      (fppf_invariantsπ (G := G) (B := ↑Γ(X, ⊤)) hfreeA).2.1
      (fppf_invariantsπ (G := G) (B := ↑Γ(X, ⊤)) hfreeA).2.2
      s a hap W₀R hW₀R ρR hρsq hρzero CvcR hCvcR hρact W₁ E hW₁ hcob
  exact lw_of_baseIso π' zero' hz qiso hspec

/-- **([a5], the descended Weierstrass model — LEAF; STATEMENT FIX EXECUTED v10.324-FIN)** The
quotient curve `E/G ⟶ X/G` admits a Zariski-local Weierstrass model, for the section pair
COMPATIBLE with the quotient charts (`hπ'c`/`hzero'c` — the v10.94 owed interface fix; the
unconstrained form was FALSE, see the deleted `[a5-pair]` counterexample in the git history:
twist the canonical pair by a split endomorphism of `Spec ℚ[x₁,x₂,…]`).

Plan (terminating in a proof; the one genuinely new-math leaf of route (a)): the universal curve
upstairs has a global model `E = projModel W` (in the bootstrap `E` is pulled back from T-E15's
explicit `ℰ₃`), and each `γ ∈ G` acts on it by a `VariableChange` `C_γ = (u_γ, r_γ, s_γ, t_γ)`
(**T-W7.1b** = `pointedIso_exists_variableChange`, now DONE). Splitting the cocycle:
* the additive part `(r, s, t) ∈ Z¹(G, A⁺)` is a coboundary by `exists_sub_smul_eq_of_isCocycle`
  (additive Hilbert 90, PROVEN);
* the multiplicative part `u ∈ Z¹(G, Aˣ)` is **Zariski-locally** a coboundary by
  `exists_unit_smul_eq_of_isLocalRing` ([A711-DESC], PROVEN).
So over a Zariski neighbourhood of each prime of `Aᴳ`, a variable change makes `W` `G`-invariant,
and the invariant model descends to give the local Weierstrass model of `E/G`. -/
theorem locallyWeierstrass_quotientπ [Finite G] [IsAffine X]
    [IsAffineHom (Limits.pullback.diagonal (Limits.terminal.from X))]
    [IsAffineHom (Limits.pullback.diagonal (Limits.terminal.from C.E))]
    (hact : IsCurveAction σ C σE)
    (V : X → X.Opens) (hVs : ∀ x, σ.IsStableOpen (V x)) (hVa : ∀ x, IsAffineOpen (V x))
    (hVmem : ∀ x, x ∈ V x) (hVtop : ∀ x, V x = ⊤)
    (VE : C.E → (C.E).Opens) (hVEs : ∀ e, σE.IsStableOpen (VE e))
    (hVEa : ∀ e, IsAffineOpen (VE e)) (hVEmem : ∀ e, e ∈ VE e)
    (hfree : ∀ γ : G, γ ≠ 1 → ∀ (T : Scheme.{u}) (t : T ⟶ X), t ≫ σ.hom γ = t → IsEmpty T)
    (π' : σE.quotient VE hVEs hVEa ⟶ σ.quotient V hVs hVa)
    (zero' : σ.quotient V hVs hVa ⟶ σE.quotient VE hVEs hVEa)
    (hz : zero' ≫ π' = 𝟙 (σ.quotient V hVs hVa))
    (hπ'c : σE.quotientπ VE hVEs hVEa hVEmem ≫ π' = C.π ≫ σ.quotientπ V hVs hVa hVmem)
    (hzero'c : σ.quotientπ V hVs hVa hVmem ≫ zero'
      = C.zero ≫ σE.quotientπ VE hVEs hVEa hVEmem) :
    LocallyWeierstrass π' zero' hz := by
  rcases isEmpty_or_nonempty (↥X) with hX | hX
  · intro s
    obtain ⟨x, -⟩ := σ.quotientπ_surjective V hVs hVa hVmem s
    exact (hX.false x).elim
  · exact locallyWeierstrass_quotientπ_of_compat hact V hVs hVa hVmem hVtop
      VE hVEs hVEa hVEmem hfree hX π' zero' hz hπ'c hzero'c

/-- **([a3]–[a5], the route-(a) descent theorem — ASSEMBLED)** Let `G` act freely on an affine
scheme `X`, and let the action lift to a geometric elliptic curve `C/X` (an `IsCurveAction`) with
an orbit-in-affine-open chart datum. Then the quotient `E/G` carries a geometric elliptic curve
structure over `X/G`, and the square

    E ──────▶ E/G
    │           │
    π           π'
    ▼           ▼
    X ──────▶ X/G

is **cartesian** and compatible with the zero sections — precisely an `Ell/R`-morphism, which is
what the KM engine consumes.

**This assembly is sorry-free.** It consumes exactly:
* `exists_quotient_π_zero` (PROVEN) — the descended `π'`, `zero'` and `zero' ≫ π' = 𝟙`;
* `locallyWeierstrass_quotientπ` (leaf `[a5]`, gated on nothing — T-W7.1b is DONE) — the local
  Weierstrass model of the quotient curve;
* `isProper_of_locallyWeierstrass` (PROVEN) and `smoothOfRelativeDimension_of_locallyWeierstrass`
  (leaf, waits on T-A3) — `proper` and `smooth` from that model;
* `isPullback_quotientπ` (PROVEN modulo the affine chart square `isPullback_chart`) — the
  cartesian square.

So the KM 4.7 ⇐-engine's geometric core is **structurally complete**: the two residual sorries are
the isolated affine computations `isPullback_chart` (Galois descent of `Γ(W)`) and
`locallyWeierstrass_quotientπ`/`smoothOfRelativeDimension_of_locallyWeierstrass` ([a5] + T-A3). -/
theorem exists_ellipticCurveGeom_quotient [Finite G] [IsAffine X]
    [IsAffineHom (Limits.pullback.diagonal (Limits.terminal.from X))]
    [IsAffineHom (Limits.pullback.diagonal (Limits.terminal.from C.E))]
    (hact : IsCurveAction σ C σE)
    (V : X → X.Opens) (hVs : ∀ x, σ.IsStableOpen (V x)) (hVa : ∀ x, IsAffineOpen (V x))
    (hVmem : ∀ x, x ∈ V x) (hVtop : ∀ x, V x = ⊤)
    (hfree : ∀ γ : G, γ ≠ 1 → ∀ (T : Scheme.{u}) (t : T ⟶ X),
      t ≫ σ.hom γ = t → IsEmpty T)
    (horbit : ∀ e : C.E, ∃ U : (C.E).Opens, IsAffineOpen U ∧
      ∀ γ : G, (σE.hom γ).base e ∈ U) :
    ∃ (C' : EllipticCurveGeom (σ.quotient V hVs hVa)) (q : C.E ⟶ C'.E),
      IsPullback q C.π C'.π (σ.quotientπ V hVs hVa hVmem) ∧
        C.zero ≫ q = σ.quotientπ V hVs hVa hVmem ≫ C'.zero := by
  -- the `G`-stable affine atlas of `E` (from the orbit chart datum)
  choose VE hVEs hVEa hVEmem using
    fun e => exists_isStableOpen_isAffineOpen_of_orbit horbit e
  -- descend `π` and the zero section
  obtain ⟨π', zero', hπ', hzero', hzπ'⟩ :=
    exists_quotient_π_zero hact V hVs hVa hVmem VE hVEs hVEa hVEmem
  -- the descended local Weierstrass model, and proper/smooth from it
  have hlw := locallyWeierstrass_quotientπ hact V hVs hVa hVmem hVtop VE hVEs hVEa hVEmem hfree
    π' zero' hzπ' hπ' hzero'
  haveI hproper : IsProper π' := isProper_of_locallyWeierstrass hlw
  haveI hsmooth : SmoothOfRelativeDimension 1 π' :=
    smoothOfRelativeDimension_of_locallyWeierstrass hlw
  -- assemble the geometric elliptic curve on `E/G`
  refine ⟨{ E := σE.quotient VE hVEs hVEa, π := π', zero := zero', zero_π := hzπ'
            smooth := hsmooth, proper := hproper, localModel := hlw },
    σE.quotientπ VE hVEs hVEa hVEmem, ?_, ?_⟩
  · exact isPullback_quotientπ hact V hVs hVa hVmem hVtop VE hVEs hVEa hVEmem hfree π' hπ'
  · exact hzero'.symm


/-- **([a3]–[a5] ASSEMBLED, global-model form — the KM 4.7 ⇐-engine, Phase A)** Let `G` act
freely on an affine `X`, lifted to a geometric elliptic curve `C/X` carrying a compatible global
Weierstrass model `φ : C.E ≅ projModel W₀` (as the intended applications do — Hesse/Legendre).
Then `E/G` carries a geometric elliptic curve structure over `X/G`, cartesian over `X → X/G` and
compatible with the zero sections — precisely the `Ell/R`-morphism the KM engine consumes.
The orbit-in-affine-open datum is *derived* from the global model
(`exists_charts_of_globalModel`), and the local Weierstrass model of the quotient is
`locallyWeierstrass_quotientπ_of_globalModel` ([a5], PROVEN). Smoothness routes through
`smoothOfRelativeDimension_of_locallyWeierstrass` (T-A3, the one open leaf, owner beastmode-A). -/
theorem exists_ellipticCurveGeom_quotient_of_globalModel [Finite G] [IsAffine X]
    [IsAffineHom (Limits.pullback.diagonal (Limits.terminal.from X))]
    [IsAffineHom (Limits.pullback.diagonal (Limits.terminal.from C.E))]
    (hact : IsCurveAction σ C σE)
    (V : X → X.Opens) (hVs : ∀ x, σ.IsStableOpen (V x)) (hVa : ∀ x, IsAffineOpen (V x))
    (hVmem : ∀ x, x ∈ V x) (hVtop : ∀ x, V x = ⊤)
    (hfreeX : ∀ γ : G, γ ≠ 1 → ∀ (T : Scheme.{u}) (t : T ⟶ X), t ≫ σ.hom γ = t → IsEmpty T)
    (W₀ : WeierstrassCurve Γ(X, ⊤)) (φ : C.E ≅ projModel W₀) (hW₀ : W₀.IsElliptic)
    (hπφ : φ.hom ≫ projModelπ W₀ = C.π ≫ X.isoSpec.hom)
    (hzeroφ : C.zero ≫ φ.hom = X.isoSpec.hom ≫ projModelZero W₀) :
    ∃ (C' : EllipticCurveGeom (σ.quotient V hVs hVa)) (q : C.E ⟶ C'.E),
      IsPullback q C.π C'.π (σ.quotientπ V hVs hVa hVmem) ∧
        C.zero ≫ q = σ.quotientπ V hVs hVa hVmem ≫ C'.zero ∧
        ∀ γ : G, σE.hom γ ≫ q = q := by
  -- the `G`-stable affine atlas of `E`, derived from the global model
  have horbit : ∀ e : C.E, ∃ U : (C.E).Opens, IsAffineOpen U ∧
      ∀ γ : G, (σE.hom γ).base e ∈ U := by
    obtain ⟨U₀, U₁, h0, h1, hz0, hz1⟩ := exists_charts_of_globalModel φ
      (Scheme.homeoOfIso X.isoSpec).surjective hzeroφ
    exact fun e => orbit_mem_isAffineOpen_of_charts hact h0 h1 hz0 hz1 e
  choose VE hVEs hVEa hVEmem using
    fun e => exists_isStableOpen_isAffineOpen_of_orbit horbit e
  -- descend `π` and the zero section
  obtain ⟨π', zero', hπ', hzero', hzπ'⟩ :=
    exists_quotient_π_zero hact V hVs hVa hVmem VE hVEs hVEa hVEmem
  -- the descended local Weierstrass model ([a5], PROVEN), and proper/smooth from it
  have hlw := locallyWeierstrass_quotientπ_of_globalModel hact V hVs hVa hVmem hVtop
    VE hVEs hVEa hVEmem hfreeX W₀ φ hW₀ hπφ hzeroφ π' zero' hzπ' hπ' hzero'
  haveI hproper : IsProper π' := isProper_of_locallyWeierstrass hlw
  haveI hsmooth : SmoothOfRelativeDimension 1 π' :=
    smoothOfRelativeDimension_of_locallyWeierstrass hlw
  refine ⟨{ E := σE.quotient VE hVEs hVEa, π := π', zero := zero', zero_π := hzπ',
            smooth := hsmooth, proper := hproper, localModel := hlw },
    σE.quotientπ VE hVEs hVEa hVEmem, ?_, hzero'.symm, ?_⟩
  · exact isPullback_quotientπ hact V hVs hVa hVmem hVtop VE hVEs hVEa hVEmem hfreeX π' hπ'
  · exact fun γ => σE.hom_quotientπ VE hVEs hVEa hVEmem γ


end ModularCurves.RouteA
