/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.Moduli.GammaHRepresentability
import ModularCurves.Moduli.QuotientRepresentability

/-!
# The Γ_H MASTER assembly (KM 4.7.0 applied to `P_H`) — interface

`Y_H` as a fine moduli scheme: the quotient problem `P_H = [Γ(N)]/H` (GHC1,
`gammaH_relativelyRepresentable`) fed to the [B3]/FP4 representability engine
(`representable_of_rigid_of_torsor_of_globalModel`, KM SCHOLIE 4.7.0 route (a)) with the
full-level problem as the auxiliary rigidifier.

**Interface-first** (fleet norm, v10.154 precedent): every input the engine needs is a
NAMED HYPOTHESIS here, so the seams are visible pins:

* `qpd` — GHC1's output (`gammaH_relativelyRepresentable`; sorryAx currently via [GH1]
  `gammaHAut` + [GHA3] `levelSpaceΓπ_etale` only);
* `hQrep` — representability of the full-level problem = the Y(N) MASTER
  (STREAM-YN's (C); consume by name when it lands);
* `htors` — the full-group torsor datum on the level scheme (c5β's
  `glSchemeSmul`/L4-seam layer; KM axiom 2 "δ_{E/S} is a finite étale G-torsor");
* `hrig` — rigidity of `P_H` (the classical `N ≥ 3` + `H`-condition; the geometric
  bridge `QuotientProblemData.rigid_of_geom_free` reduces it to orbit-freeness of
  `Aut(E)` on `H`-orbits over geometric points);
* `hQaff`/`hPaff`/`hmodel` — the engine's affineness/Weierstrass-model clauses
  (KM's standing "affine over (Ell)" hypotheses).

The assembly itself is pure: relative representability of `P_H` is repackaged from
`qpd.relRep` and everything else is the engine.
-/

universe u

open CategoryTheory AlgebraicGeometry

namespace ModularCurves

variable (R : CommRingCat.{u})

/-- **[Γ_H MASTER, interface] (KM 4.7.0 for `P_H`; Loeffler 3.8.2 upgraded to a fine
scheme)** — the quotient problem `P_H` is representable, given the engine's pin-set: the
Y(N) representability (`hQrep`, STREAM-YN), the full-group torsor datum (`htors`, c5β's
layer), rigidity of `P_H` (`hrig`), and the affineness/global-model clauses. The
representing object is KM's `𝕸(P_H, δ)/G`, i.e. `Y_H(N)`. -/
theorem gammaH_representable (N : ℕ) [NeZero N]
    (H : Subgroup (Matrix.GeneralLinearGroup (Fin 2) (ZMod N)))
    (qpd : ModuliProblem.QuotientProblemData (gammaHAut R N H))
    {G : Type u} [Group G] [Finite G] (φfull : G →* Aut (gammaFullNaiveProblem R N))
    (hQrep : (gammaFullNaiveProblem R N).Representable)
    (htors : ∀ X : EllObj R, Nonempty (ModuliProblem.TorsorData φfull X))
    (hrig : qpd.prob.Rigid)
    (hQaff : ∀ {Xδ : EllObj R}, (gammaFullNaiveProblem R N).RepresentableBy Xδ →
      IsAffine Xδ.base)
    (hPaff : ∀ (X : EllObj R) (dP : ModuliProblem.RelRepData qpd.prob X), IsAffine dP.Z)
    (hmodel : ∀ {Xδ : EllObj R} [IsAffine Xδ.base],
      (gammaFullNaiveProblem R N).RepresentableBy Xδ →
      ∃ (WQ : WeierstrassCurve ↑Γ(Xδ.base, ⊤)) (φQ : Xδ.curve.E ≅ projModel WQ),
        WQ.IsElliptic ∧
        φQ.hom ≫ projModelπ WQ = Xδ.curve.π ≫ Xδ.base.isoSpec.hom ∧
        Xδ.curve.zero ≫ φQ.hom = Xδ.base.isoSpec.hom ≫ projModelZero WQ) :
    qpd.prob.Representable :=
  ModuliProblem.representable_of_rigid_of_torsor_of_globalModel qpd.prob
    (gammaFullNaiveProblem R N) φfull hQrep
    ((ModuliProblem.relativelyRepresentable_iff_nonempty_relRepData qpd.prob).mpr
      (fun X => ⟨(qpd.relRep X).choose⟩))
    htors hrig hQaff hPaff hmodel

end ModularCurves
