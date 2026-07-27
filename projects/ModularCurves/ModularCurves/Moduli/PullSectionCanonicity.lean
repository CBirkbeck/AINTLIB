/-
Copyright (c) 2026 The AINTLIB Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AINTLIB Authors
-/
import ModularCurves.Moduli.PullSectionAdd
import ModularCurves.EllipticCurve.RigiditySpreadingOut
import ModularCurves.EllipticCurve.RecordGroupUnique
import ModularCurves.LevelStructure.IsoTransport
import ModularCurves.EllipticCurve.TorsionFibre

/-!
# The T-E4 transport, reduced to the single canonicity primitive (Y1-D2)

`Moduli.PullSectionAdd` proves section-pullback additivity (`transportSection_add`,
`pullSection_add_of_isLocallyNoetherian`) over **locally noetherian** bases only, because it
invokes `isMonHom_of_one_comp_eq'` (GIT Cor 6.4, T-W7.7) — which currently carries
`[IsLocallyNoetherian S]`. The whole T-E4 family (unrestricted `pullSection_add`, the
`Γ₁`/`Γ(N)` naive functor-law memberships, and the Y₁(N) transport `Y1-D2`) inherits that
noetherian restriction — but **only through that one call**.

This file isolates the dependency. Reading `transportSection_add`'s proof, the base's
noetherianness is used **exclusively** to produce the group-homomorphism equation `h64` for
the comparison isomorphism `curveIsoPullbackOver`; everything downstream is noetherian-free
group algebra. So:

* `transportSection_add_of_isMonHom` (proved in `Moduli/PullSectionAdd.lean`, next to the
  noetherian specialisation that consumes it) takes that group-hom equation as a
  **hypothesis** and proves transport additivity **sorry-free, over an arbitrary base**.
  This is the single "one transport proof" that closes the whole family; this file supplies
  the hypothesis from the finite-presentation route.

The hypothesis is supplied three ways, all feeding the *same* lemma:
* `isMonHom_of_one_comp_eq'` (`Rigidity.lean`, noetherian) — recovers the existing
  `pullSection_add_of_isLocallyNoetherian`;
* `isMonHom_of_one_comp_eq'_of_finitePresentation` (`RigiditySpreadingOut.lean`, **route (a)**,
  T-W7.8) — gives the arbitrary-base result the moment route (a) lands;
* the explicit base-change-natural group law (**route (c)**, c5β's endgame `mulModelHom` →
  `T-W7a`) — same, the moment the endgame lands.

So the entire T-E4 family is now **collapsed to the single primitive
`isMonHom_of_one_comp_eq'_of_finitePresentation`** (arbitrary-base GIT Cor 6.4), which lands
via route (a) or route (c).

## Holder wiring note (T-E4-family, [Y1-D2])

The standalone lemmas here (all over an **arbitrary** base) let the holders close their
parked/`sorry`'d transport gates. Every one bottoms out at the *single* primitive
`isMonHom_of_one_comp_eq'_of_finitePresentation`, so all go axiom-clean the moment route (a)
(this repo's `RigiditySpreadingOut.lean`) *or* route (c) (c5β's endgame `T-W7a`) lands.

* **`Moduli/Representability.lean` holder** — `EllHom.pullSection_add` (the parked `:= by sorry`,
  ~L207): replace with `EllHom.pullSection_add_of_finitePresentation R f P Q`. The two functor-law
  memberships `gammaOneNaiveProblem.map` / `gammaFullNaiveProblem.map` (~L214/L229) then close: the
  `(N : ℤ) • P = 0` killing clause transports by `pullSection_add_of_finitePresentation` +
  `pullSection_zsmul_of_finitePresentation`; the fibrewise `Point.pull` clauses transport barehanded
  (pull commutes with `pullSection`, no group data). `pullSection_zsmul` (GammaHRepresentability,
  and hence `pullAlong_glSmul`/GH) can drop its `pullSection_add` hypothesis onto the FP version.
* **`ModularCurve/YOneAssembly.lean` ([Y1-D2], NEW-Y1)** — `isNaiveGammaOne_pullSection_iff` closes
  the same way: the killing clause via the two FP `pullSection` lemmas above; the fibrewise clauses
  (`(N:ℤ) • Point.pull … = 0`, exact-order-`N`) barehanded via pull/`pullSection` compatibility. Do
  **not** shared-edit — this note is the coordination; assemble in your own file/PR.
* **Coordination (attack-1, no duplication):** the canonicity transport is proved *once* — here, in
  `transportSection_add_of_isMonHom` (sorry-free) — and everything above consumes it. Do not
  re-derive the group-iso transport in the holder files.

## References

* Loeffler, §3.3/§3.7/§3.8 (the `Ell/R`-presheaf functor laws).
* Katz–Mazur, 2.1.2 / 3.2 (canonicity of the group law; naive level structures).
-/

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
  MonObj

universe u

namespace ModularCurves

/-- **(KM-W0, full-level iso-leg)** The Drinfeld full-level condition transports along a
pointed multiplication-compatible isomorphism of elliptic curves: if `(P, Q)` is a Drinfeld
`Γ(N)`-structure on `E`, so is `(pointMapOfHom e.hom P, pointMapOfHom e.hom Q)` on `E'`. The
killing clauses transport by the additive equivalence `pointAddEquiv`; the divisor clause by
`sectionsDivisor_pointMap_ideal` (the image family is the transported family, via additivity)
composed with `torsionIdeal_eq_comap`. Companion to `Section.HasExactOrder.pointMap`, for the
pair / `E[N]` (`Γ(N)`) condition. -/
lemma isFullLevel_pointMap {S : Scheme.{u}} {E E' : EllipticCurve S}
    (e : E.asOver ≅ E'.asOver)
    (hη : η[E.asOver] ≫ e.hom = η[E'.asOver])
    (hμ : μ[E.asOver] ≫ e.hom = MonoidalCategory.tensorHom e.hom e.hom ≫ μ[E'.asOver])
    {N : ℕ} [NeZero N] {P Q : E.Section} (h : E.IsFullLevel N P Q) :
    E'.IsFullLevel N (EllipticCurve.pointMapOfHom e.hom P)
      (EllipticCurve.pointMapOfHom e.hom Q) := by
  obtain ⟨⟨hPk, hQk⟩, hdiv⟩ := h
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [show ((N : ℤ) • EllipticCurve.pointMapOfHom e.hom P)
        = EllipticCurve.pointMapOfHom e.hom ((N : ℤ) • P) from
        (map_zsmul (EllipticCurve.pointAddEquiv e hμ (𝟙 S)) (N : ℤ) P).symm, hPk]
    exact map_zero (EllipticCurve.pointAddEquiv e hμ (𝟙 S))
  · rw [show ((N : ℤ) • EllipticCurve.pointMapOfHom e.hom Q)
        = EllipticCurve.pointMapOfHom e.hom ((N : ℤ) • Q) from
        (map_zsmul (EllipticCurve.pointAddEquiv e hμ (𝟙 S)) (N : ℤ) Q).symm, hQk]
    exact map_zero (EllipticCurve.pointAddEquiv e hμ (𝟙 S))
  · have hfam : (fun i : Fin (N ^ 2) =>
          ((((i : ℕ) % N : ℕ) : ℤ) • EllipticCurve.pointMapOfHom e.hom P
            + ((((i : ℕ) / N : ℕ) : ℤ) • EllipticCurve.pointMapOfHom e.hom Q) :
            E'.Point (𝟙 S)))
        = fun i : Fin (N ^ 2) => EllipticCurve.pointMapOfHom e.hom
            ((((((i : ℕ) % N : ℕ) : ℤ) • P + ((((i : ℕ) / N : ℕ) : ℤ) • Q)) :
              E.Point (𝟙 S))) := by
      funext i
      rw [EllipticCurve.pointMapOfHom_add e.hom hμ]
      congr 1
      · exact (map_zsmul (EllipticCurve.pointAddEquiv e hμ (𝟙 S)) _ P).symm
      · exact (map_zsmul (EllipticCurve.pointAddEquiv e hμ (𝟙 S)) _ Q).symm
    show (RelEffCartierDiv.sectionsDivisor E'.π _).ideal = E'.torsionIdeal N
    rw [hfam, EllipticCurve.sectionsDivisor_pointMap_ideal, hdiv,
      EllipticCurve.torsionIdeal_eq_comap e hη hμ]

/-- **(KM-W0, full-level base-change divisor leg)** The divisor of a family of sections is
natural in the base: base-changing `Σᵢ [Pᵢ]` along `t : T ⟶ S` gives the divisor of the
pulled family `Σᵢ [asSection (pull Pᵢ)]` on the base-changed curve. General-family analogue
of `Section.orderDivisor_baseChange`; each factor is `RelEffCartierDiv.ker_sectionBaseChange`
(the RHS family is already `asSection ∘ pull`, so no additivity bridge is needed). -/
theorem sectionsDivisor_baseChange {S : Scheme.{u}} (E : EllipticCurve S) {n : ℕ}
    (P : Fin n → E.Point (𝟙 S)) {T : Scheme.{u}} (t : T ⟶ S) :
    (RelEffCartierDiv.sectionsDivisor E.π P).baseChange t =
      RelEffCartierDiv.sectionsDivisor (E.baseChange t).π
        (fun i => EllipticCurve.Point.asSection E t (EllipticCurve.Point.pull E t (P i))) := by
  have hpos : IsSeparated E.π ∧ SmoothOfRelativeDimension 1 E.π :=
    ⟨inferInstance, E.smooth⟩
  have hpos' : IsSeparated (E.baseChange t).π ∧
      SmoothOfRelativeDimension 1 (E.baseChange t).π :=
    ⟨inferInstance, (E.baseChange t).smooth⟩
  apply RelEffCartierDiv.ext
  have hL : ((RelEffCartierDiv.sectionsDivisor E.π P).baseChange t).ideal =
      (∏ i, Scheme.Hom.ker (P i).1).comap (Limits.pullback.fst E.π t) := by
    rw [RelEffCartierDiv.baseChange_ideal]
    congr 1
    rw [RelEffCartierDiv.sectionsDivisor, dif_pos hpos]
  have hR : (RelEffCartierDiv.sectionsDivisor (E.baseChange t).π
        (fun i => EllipticCurve.Point.asSection E t
          (EllipticCurve.Point.pull E t (P i)))).ideal =
      ∏ i, Scheme.Hom.ker
        (EllipticCurve.Point.asSection E t (EllipticCurve.Point.pull E t (P i))).1 := by
    rw [RelEffCartierDiv.sectionsDivisor, dif_pos hpos']
  rw [hL, hR, Scheme.IdealSheafData.comap_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  exact (RelEffCartierDiv.ker_sectionBaseChange (P i).1 (P i).2 t).symm

/-- **(KM-W0, full-level base-change torsion-ideal leg)** The `N`-torsion ideal sheaf
`E[N] = (torsionι N).ker` commutes with base change: on `E ×_S T` it is the scheme-theoretic
preimage of `E[N]` along the first projection `pullback.fst E.π s`. Public reconstruction of
the private `fullLevelLocusAux_torsionIdeal_baseChange` (Incidence, unreachable here): the
`torsionι`-square is a pullback — obtained by cancelling the base pullback square out of the
`torsionπ`-square `torsion_baseChange_isPullback` via `IsPullback.of_bot` — and the kernel of a
base-changed closed immersion is the comap of the kernel (`ker_fst_of_isClosedImmersion` +
`ker_comp_of_isIso`, the same finish used by `RelEffCartierDiv.baseChange_ideal`). -/
theorem torsionIdeal_baseChange {S : Scheme.{u}} (E : EllipticCurve S) (N : ℕ)
    {T : Scheme.{u}} (s : T ⟶ S) :
    (E.baseChange s).torsionIdeal N =
      (E.torsionIdeal N).comap (Limits.pullback.fst E.π s) := by
  haveI := E.torsionι_isClosedImmersion N
  have hι : IsPullback (E.torsionBaseChangeHom N s) ((E.baseChange s).torsionι N)
      (E.torsionι N) (Limits.pullback.fst E.π s) := by
    refine IsPullback.of_bot ?_ (E.torsionBaseChangeHom_torsionι N s)
      (IsPullback.of_hasPullback E.π s)
    have hbc := E.torsion_baseChange_isPullback N s
    rw [← E.torsionι_π N, ← (E.baseChange s).torsionι_π N] at hbc
    exact hbc
  show ((E.baseChange s).torsionι N).ker
      = ((E.torsionι N).ker).comap (Limits.pullback.fst E.π s)
  rw [← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion (E.torsionι N)
        (Limits.pullback.fst E.π s),
    ← hι.flip.isoPullback_hom_fst]
  exact Scheme.Hom.ker_comp_of_isIso _ _

namespace EllHom

variable (R : CommRingCat.{u}) {X Y : EllObj R} (f : X ⟶ Y)

/-- **(T-E4a, the one transport proof — sorry-free, arbitrary base)** Transport of sections
along the pointed comparison isomorphism is additive, **given** that the comparison morphism
`curveIsoPullbackOver` is a homomorphism of the two independent group structures (the
equation `h64`). This is the noetherian-free core of `transportSection_add`: the base's
noetherianness in that lemma is used *only* to produce `h64` (via `isMonHom_of_one_comp_eq'`).
Supplying `h64` from the arbitrary-base canonicity (route (a)/(c)) removes the restriction. -/
lemma transportSection_add_of_isMonHom
    (h64 : μ[X.curve.asOver] ≫ curveIsoPullbackOver R f
        = MonoidalCategory.tensorHom (curveIsoPullbackOver R f) (curveIsoPullbackOver R f)
          ≫ μ[(Y.curve.baseChange f.baseHom).asOver])
    (s s' : X.curve.Section) :
    transportSection R f (s + s')
      = transportSection R f s + transportSection R f s' := by
  have h64l : (μ[X.curve.asOver]).left ≫ (curveIsoPullback R f).hom
      = (MonoidalCategory.tensorHom (curveIsoPullbackOver R f)
          (curveIsoPullbackOver R f)).left
        ≫ (μ[(Y.curve.baseChange f.baseHom).asOver]).left :=
    ((Over.comp_left _ _ _ _ _).symm.trans (congrArg CommaMorphism.left h64)).trans
      (Over.comp_left _ _ _ _ _)
  have hcs : X.curve.pointEquivOverHom (𝟙 X.base) s ≫ curveIsoPullbackOver R f
      = (Y.curve.baseChange f.baseHom).pointEquivOverHom (𝟙 X.base)
          (transportSection R f s) :=
    Over.OverMorphism.ext rfl
  have hcs' : X.curve.pointEquivOverHom (𝟙 X.base) s' ≫ curveIsoPullbackOver R f
      = (Y.curve.baseChange f.baseHom).pointEquivOverHom (𝟙 X.base)
          (transportSection R f s') :=
    Over.OverMorphism.ext rfl
  refine Subtype.ext ?_
  have hx : (s + s').1
      = (lift (X.curve.pointEquivOverHom (𝟙 X.base) s)
          (X.curve.pointEquivOverHom (𝟙 X.base) s')).left
        ≫ (μ[X.curve.asOver]).left :=
    (congrArg CommaMorphism.left (X.curve.pointEquivOverHom_add (𝟙 X.base) s s')).trans
      (Over.comp_left _ _ _ _ _)
  have hR : (transportSection R f s + transportSection R f s').1
      = (lift ((Y.curve.baseChange f.baseHom).pointEquivOverHom (𝟙 X.base)
            (transportSection R f s))
          ((Y.curve.baseChange f.baseHom).pointEquivOverHom (𝟙 X.base)
            (transportSection R f s'))).left
        ≫ (μ[(Y.curve.baseChange f.baseHom).asOver]).left :=
    (congrArg CommaMorphism.left
      ((Y.curve.baseChange f.baseHom).pointEquivOverHom_add (𝟙 X.base) _ _)).trans
      (Over.comp_left _ _ _ _ _)
  show (s + s').1 ≫ (curveIsoPullback R f).hom = _
  rw [hR]
  exact (congrArg (· ≫ (curveIsoPullback R f).hom) hx).trans <|
    (Category.assoc _ _ _).trans <|
    (congrArg ((lift (X.curve.pointEquivOverHom (𝟙 X.base) s)
        (X.curve.pointEquivOverHom (𝟙 X.base) s')).left ≫ ·) h64l).trans <|
    (Category.assoc _ _ _).symm.trans <|
    (congrArg (· ≫ (μ[(Y.curve.baseChange f.baseHom).asOver]).left)
      ((Over.comp_left _ _ _ _ _).symm.trans
        (congrArg CommaMorphism.left
          ((lift_map _ _ _ _).trans
            (congrArg₂ lift hcs hcs')))))

/-- The comparison morphism is unit-compatible (noetherian-free). Extracted from
`transportSection_add`'s internal `hη`. -/
lemma curveIsoPullbackOver_one :
    η[X.curve.asOver] ≫ curveIsoPullbackOver R f
      = η[(Y.curve.baseChange f.baseHom).asOver] := by
  apply Over.OverMorphism.ext
  show (η[X.curve.asOver] : _ ⟶ X.curve.asOver).left ≫ (curveIsoPullback R f).hom = _
  exact (congrArg (· ≫ (curveIsoPullback R f).hom) X.curve.one_eq_zero).trans <|
    (Category.assoc _ _ _).trans <|
    (congrArg ((𝟙_ (Over X.base)).hom ≫ ·) (zero_curveIsoPullback R f)).trans <|
    (Y.curve.baseChange f.baseHom).one_eq_zero.symm

/-- **(T-E4a over an arbitrary base — now unconditional)**
Transport additivity, with the group-hom equation supplied by the arbitrary-base
records-level canonicity primitive `isMonHom_of_pointedIso_records`
(`RecordGroupUnique.lean`): the pointed comparison isomorphism onto the pullback is
automatically a homomorphism of the two group structures, so no finite-presentation or
noetherian hypothesis on the base is needed. (The name is retained for its consumers; the
finite-presentation route (a), `isMonHom_of_one_comp_eq'_of_finitePresentation`, is no
longer used here.) -/
theorem transportSection_add_of_finitePresentation (s s' : X.curve.Section) :
    transportSection R f (s + s')
      = transportSection R f s + transportSection R f s' :=
  transportSection_add_of_isMonHom R f
    (isMonHom_of_pointedIso_records X.curve (Y.curve.baseChange f.baseHom)
      (Over.isoMk (curveIsoPullback R f) f.isPullback.isoPullback_hom_snd)
      (curveIsoPullbackOver_one R f)) s s'

/-- **(T-E4a, `pullSection_add` over an arbitrary base)** Section-pullback is additive over an
arbitrary base — the unrestricted statement, modulo the single route (a)/(c) canonicity
primitive. Same proof as `pullSection_add_of_isLocallyNoetherian` but routed through
`transportSection_add_of_finitePresentation`, so the only remaining dependency is the
arbitrary-base GIT Cor 6.4 (not `[IsLocallyNoetherian]`). -/
theorem pullSection_add_of_finitePresentation (P Q : Y.curve.Section) :
    pullSection R f (P + Q)
      = pullSection R f P + pullSection R f Q := by
  apply transportSection_injective R f
  rw [transportSection_add_of_finitePresentation]
  apply (EllipticCurve.Point.baseChangeEquiv Y.curve f.baseHom (𝟙 X.base)).injective
  rw [map_add, dict_transportSection_pullSection, dict_transportSection_pullSection,
    dict_transportSection_pullSection, EllipticCurve.Point.pull_add]

/-- **(T-E4a, `pullSection_zsmul` over an arbitrary base)** `ℤ`-linearity of section-pullback
over an arbitrary base, from `pullSection_add_of_finitePresentation` via `map_zsmul`. Mirrors
`EllHom.pullSection_zsmul` (which assumes the noetherian/parked `pullSection_add`). Transports
the `(N : ℤ) • P = 0` killing clause of `IsNaiveGammaOne`/`IsNaiveFullLevel`. -/
theorem pullSection_zsmul_of_finitePresentation (n : ℤ) (P : Y.curve.Section) :
    pullSection R f (n • P) = n • pullSection R f P :=
  map_zsmul (AddMonoidHom.mk' (pullSection R f)
    (pullSection_add_of_finitePresentation R f)) n P

/-- **(KM-W0 transport leaf — Drinfeld exact order pulls back along `Ell/R`-morphisms)**
If a section `P` of `Y.curve` has Drinfeld exact order `N`, so does its pullback
`pullSection f P` along `f : X ⟶ Y`. Two legs: base change of the exact-order divisor
(`Section.HasExactOrder.baseChange`) to `Y.curve.baseChange f.baseHom`, then transport
across the cartesian comparison isomorphism `curveIsoPullback`
(`Section.HasExactOrder.pointMap`, whose group-hom hypothesis is supplied by the
arbitrary-base records canonicity primitive `isMonHom_of_pointedIso_records`). This is the
`IsGammaOne` functoriality clause (KM 3.2) for the Drinfeld `[Γ₁(N)]` moduli problem over
an arbitrary base — the substrate that discharges `gammaOneDrinfeldProblem.map`. -/
theorem hasExactOrder_pullSection {P : Y.curve.Section} {N : ℕ} [NeZero N]
    (h : P.HasExactOrder Y.curve N) :
    (EllHom.pullSection R f P).HasExactOrder X.curve N := by
  -- the cartesian comparison iso  X.curve.asOver ≅ (Y.curve.baseChange f.baseHom).asOver
  let eA : X.curve.asOver ≅ (Y.curve.baseChange f.baseHom).asOver :=
    Over.isoMk (curveIsoPullback R f) f.isPullback.isoPullback_hom_snd
  -- unit-compatibility of `eA.symm`, feeding the records canonicity primitive
  have hη_symm :
      η[(Y.curve.baseChange f.baseHom).asOver] ≫ eA.symm.hom = η[X.curve.asOver] := by
    rw [Iso.symm_hom, Iso.comp_inv_eq]
    exact (curveIsoPullbackOver_one R f).symm
  have hμ_symm := isMonHom_of_pointedIso_records (Y.curve.baseChange f.baseHom) X.curve
    eA.symm hη_symm
  -- base-change leg, then iso leg
  have hbc := EllipticCurve.Section.HasExactOrder.baseChange Y.curve h f.baseHom
  have htrans := EllipticCurve.Section.HasExactOrder.pointMap eA.symm hμ_symm hbc
  -- dictionary: the transported base-changed section is exactly `pullSection f P`
  have hAS : EllipticCurve.Point.asSection Y.curve f.baseHom
        (EllipticCurve.Point.pull Y.curve f.baseHom P)
      = transportSection R f (EllHom.pullSection R f P) := by
    refine Subtype.ext ?_
    rw [transportSection_pullSection, EllipticCurve.Point.asSection_coe]
    rfl
  have hkey : EllipticCurve.pointMapOfHom eA.symm.hom
      (EllipticCurve.Point.asSection Y.curve f.baseHom
        (EllipticCurve.Point.pull Y.curve f.baseHom P))
      = EllHom.pullSection R f P := by
    rw [hAS]
    -- `transportSection R f Q` is defeq `pointMapOfHom eA.hom Q` (both are `Q.1 ≫ eA.hom.left`,
    -- as `eA.hom.left ≡ (curveIsoPullback R f).hom`); staying in `eA.hom.left`/`eA.inv.left`
    -- avoids the `pullback`-vs-`baseChange.E` typing friction.
    show EllipticCurve.pointMapOfHom eA.symm.hom
        (EllipticCurve.pointMapOfHom eA.hom (EllHom.pullSection R f P))
      = EllHom.pullSection R f P
    rw [Iso.symm_hom]
    refine Subtype.ext ?_
    exact (Category.assoc _ _ _).trans
      ((congrArg (fun m => (EllHom.pullSection R f P).1 ≫ m)
          (EllipticCurve.iso_hom_left_inv_left eA)).trans (Category.comp_id _))
  rw [hkey] at htrans
  exact htrans

/-- **(KM-W0 transport leaf — Drinfeld full level pulls back along `Ell/R`-morphisms)**
If `(P, Q)` is a Drinfeld `Γ(N)`-structure on `Y.curve`, so is `(pullSection f P,
pullSection f Q)` on `X.curve`. This is the `IsFullLevel` functoriality clause (KM 3.1/3.2)
for the Drinfeld `[Γ(N)]` moduli problem over an arbitrary base — the substrate that
discharges `gammaFullDrinfeldProblem.map`. Direct (no `IsFullLevel` base-change intermediate):
the killing clauses transport by `ℤ`-linearity of `pullSection`; the divisor clause combines
the `N²`-section family into `pullSection f (aP + bQ)` (`pullSection_add`/`_zsmul`), applies the
dictionary `pullSection f s = pointMapOfHom eA.symm.hom (asSection (pull s))`, then runs the
base-change ⧸ iso legs (`sectionsDivisor_pointMap_ideal`, `sectionsDivisor_baseChange`,
`RelEffCartierDiv.baseChange_ideal`, `torsionIdeal_eq_comap`, `torsionIdeal_baseChange`). The
group-hom hypothesis on `eA.symm` is the arbitrary-base records primitive
`isMonHom_of_pointedIso_records`. -/
theorem isFullLevel_pullSection {P Q : Y.curve.Section} {N : ℕ} [NeZero N]
    (h : Y.curve.IsFullLevel N P Q) :
    X.curve.IsFullLevel N (EllHom.pullSection R f P) (EllHom.pullSection R f Q) := by
  obtain ⟨⟨hPk, hQk⟩, hdiv⟩ := h
  -- `pullSection` as an additive homomorphism (killing clauses + family combination)
  let φ : Y.curve.Section →+ X.curve.Section :=
    AddMonoidHom.mk' (EllHom.pullSection R f) (pullSection_add_of_finitePresentation R f)
  -- the cartesian comparison iso and its records-supplied group-hom equation
  let eA : X.curve.asOver ≅ (Y.curve.baseChange f.baseHom).asOver :=
    Over.isoMk (curveIsoPullback R f) f.isPullback.isoPullback_hom_snd
  have hη_symm :
      η[(Y.curve.baseChange f.baseHom).asOver] ≫ eA.symm.hom = η[X.curve.asOver] := by
    rw [Iso.symm_hom, Iso.comp_inv_eq]
    exact (curveIsoPullbackOver_one R f).symm
  have hμ_symm := isMonHom_of_pointedIso_records (Y.curve.baseChange f.baseHom) X.curve
    eA.symm hη_symm
  -- dictionary: `pullSection` factors as base-change-then-iso (the `hAS`/`hkey` of
  -- `hasExactOrder_pullSection`, generalised over the section)
  have hdict : ∀ s : Y.curve.Section,
      EllipticCurve.pointMapOfHom eA.symm.hom
        (EllipticCurve.Point.asSection Y.curve f.baseHom
          (EllipticCurve.Point.pull Y.curve f.baseHom s))
      = EllHom.pullSection R f s := by
    intro s
    have hAS : EllipticCurve.Point.asSection Y.curve f.baseHom
          (EllipticCurve.Point.pull Y.curve f.baseHom s)
        = transportSection R f (EllHom.pullSection R f s) := by
      refine Subtype.ext ?_
      rw [transportSection_pullSection, EllipticCurve.Point.asSection_coe]
      rfl
    rw [hAS]
    show EllipticCurve.pointMapOfHom eA.symm.hom
        (EllipticCurve.pointMapOfHom eA.hom (EllHom.pullSection R f s))
      = EllHom.pullSection R f s
    rw [Iso.symm_hom]
    refine Subtype.ext ?_
    exact (Category.assoc _ _ _).trans
      ((congrArg (fun m => (EllHom.pullSection R f s).1 ≫ m)
          (EllipticCurve.iso_hom_left_inv_left eA)).trans (Category.comp_id _))
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [show ((N : ℤ) • EllHom.pullSection R f P) = φ ((N : ℤ) • P) from
        (map_zsmul φ (N : ℤ) P).symm, hPk]
    exact map_zero φ
  · rw [show ((N : ℤ) • EllHom.pullSection R f Q) = φ ((N : ℤ) • Q) from
        (map_zsmul φ (N : ℤ) Q).symm, hQk]
    exact map_zero φ
  · have hfam : (fun i : Fin (N ^ 2) =>
          (((i : ℕ) % N : ℕ) : ℤ) • EllHom.pullSection R f P
            + (((i : ℕ) / N : ℕ) : ℤ) • EllHom.pullSection R f Q)
        = fun i : Fin (N ^ 2) => EllipticCurve.pointMapOfHom eA.symm.hom
            (EllipticCurve.Point.asSection Y.curve f.baseHom
              (EllipticCurve.Point.pull Y.curve f.baseHom
                ((((i : ℕ) % N : ℕ) : ℤ) • P + (((i : ℕ) / N : ℕ) : ℤ) • Q))) := by
      funext i
      rw [← pullSection_zsmul_of_finitePresentation R f,
        ← pullSection_zsmul_of_finitePresentation R f,
        ← pullSection_add_of_finitePresentation R f, ← hdict]
    show (RelEffCartierDiv.sectionsDivisor X.curve.π _).ideal = X.curve.torsionIdeal N
    rw [hfam, EllipticCurve.sectionsDivisor_pointMap_ideal eA.symm,
      ← sectionsDivisor_baseChange, RelEffCartierDiv.baseChange_ideal, hdiv,
      EllipticCurve.torsionIdeal_eq_comap eA.symm hη_symm hμ_symm, torsionIdeal_baseChange]

end EllHom

end ModularCurves
