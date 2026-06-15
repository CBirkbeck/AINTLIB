/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import HasseWeil.WeilPairing.PencilComapWitnesses
import HasseWeil.WeilPairing.OneSubComapConcrete
import HasseWeil.WeilPairing.OneSubWitnesses
import HasseWeil.EC.KernelCountGeneral
import HasseWeil.EC.IsogenyAG.CovarianceDischarge
import HasseWeil.EC.IsogenyAG.DualGaloisClosed

/-!
# The `PullbackEvaluation` witness for the arithmetic `1 − π` over `K̄`, and its payoffs

This file wires the **Hasse-era** `1 − π` residue pipeline (the closed leaf-2 machinery of
`OneSubAffineResidues` / `OneSubInftyResidues` / `WallAGeometricRealization`) into the **general**
dual/count theory (`WeilPairing/GenericCovarianceGeneral.lean`, `EC/KernelCountGeneral.lean`,
`EC/IsogenyAG/{DualGaloisClosed, CanonicalDual, CovarianceDischarge}.lean`), connecting the new
class machinery back to the original Hasse-bound objects.

## The object

`β := oneSubFrobeniusIsogBaseChange W p r K̄ (oneSubFrobeniusPullback_L W K̄ hq)` — the **concrete
base-changed `(1 − π)_{K̄}`** (`WeilPairing/OneSubScaling.lean` / `IsogenyBaseChangeConcrete.lean`):
stored point map *definitionally* `id − π̄` (`π̄ = frobeniusHomBaseChange`, the `q`-power Frobenius
on `E_{K̄}`), stored pullback the function-field base change of
`(isogOneSub_negFrobenius W hq).pullback`.
This is the incarnation all the committed residue lemmas are stated for.

## Deliverable 1 — the witness (`pullbackEvaluation_oneSub`)

`PullbackEvaluation (W.baseChange K̄) β (oneSubBad …)` with

  `oneSubBad = {P | (id − π̄) P = O}` — **exactly the kernel** `E(𝔽_q)` (Frobenius fixed points),

finite because `ker(1 − π)_{K̄}` is the image of the *finite* `E(𝔽_q)` under the base-change
inclusion (`oneSubFrobeniusIsogBaseChange_finiteKer`).  **No doubling / 2-torsion excisions are
needed**: at every affine image the two generator residues come *uniformly* from the
transport-to-`O` engine `isog_resid_at_affine_of_hgcomm_hinfty` (`PencilComapWitnesses.lean`), fed

* `hgcomm` = `mapTranslateGenericPoint_oneSub_canonical` (Wall A, `WallAGeometricRealization.lean`),
* `hinfty` = `inftyOrdTransport_oneSub` (the `-2`/`-3` infinity orders, `OneSubInftyResidues.lean`),

both committed axiom-clean.  (The historical case-split forms `oneSub_two_residues_nondoubling` /
`oneSub_two_residues_doubling` are subsumed and not used.)

## Deliverable 2 — the payoffs (all over `K̄ = AlgebraicClosure K`)

* **(a) `card_kernel_eq_degree_oneSub`** — `#ker(1 − π)_{K̄} = deg(1 − π)_{K̄}`, instantiating the
  general separable count `card_kernel_eq_degree_of_separable` (Silverman III.4.10c, ROUTE-W).
  Separability is the `ω`-coefficient value transport
  `omegaPullbackCoeff (1 − π)_{K̄} = 1 ≠ 0` (`OneSubComapConcrete.lean`).
* **(b) the V.1.3 reproof** — `degree_oneSub_eq_pointCount` : `deg(1 − π)_{K̄} = #E(𝔽_q)`,
  from (a) + the fixed-point count `oneSubFrobeniusIsogBaseChange_nat_card_ker_eq_pointCount`.
  Composing with the degree base-change
  `oneSubFrobeniusIsogBaseChange_degree_eq_of_finrankBaseChange`
  gives a **new, independent proof of the `K`-level Silverman V.1.3**
  (`isogOneSub_negFrobenius_degree_eq_pointCount_general`): the Hasse-era proof
  (`GapSpines.isogOneSub_negFrobenius_degree_eq_pointCount`) went through the
  embeddings-classification `sepDeg γ = #ker γ` over `K`; this one goes through the general
  localized-dictionary/torsor count over `K̄`.  The two derivations now coexist, proving the same
  statement.
* **(c) the dual** — `oneSubECIsogeny` (the `EC.Isogeny` incarnation, basepoint condition from
  `inftyOrdTransport_oneSub`), `dualGaloisData_oneSub` (every Galois witness a theorem),
  `exists_dual_oneSub`, the **covariance for the class** `oneSub_mulByIntPullbackCovariant`
  (`CovarianceDischarge`), and the **canonical dual** `oneSubCanonicalDual` with the full
  Silverman III.6.1/III.6.2 packaging: `φ̂ ∘ φ = [deg φ]` (`oneSubCanonicalDual_compose`),
  `φ ∘ φ̂ = [deg φ]` (`oneSub_compose_canonicalDual`), `∃!` (`oneSub_existsUnique_dual`),
  `deg φ̂ = deg φ = #E(𝔽_q)` (`oneSubCanonicalDual_degree_eq_pointCount`), and the double dual
  `φ̂̂ = φ` (`oneSub_canonicalDual_canonicalDual`) — **everything unconditional**.
* **(d)** `oneSub_normal` / `oneSub_hdesc` — `h_normal`/`hdesc` for `1 − π`, free from
  `normal_of_separable_general` / `hdesc_of_separable_general`.

## Stretch — the pencil `rπ − s` (`p ∤ r'`, `p ∤ s'`)

The wiring is uniform: `pullbackEvaluation_pencil` with `pencilBad` = the kernel, residues from the
committed `pencil_two_residues` (the same transport-to-`O` engine, axiom-clean), finiteness from
`pencilIsogBaseChange_finiteKer`; payoff `card_kernel_eq_degree_pencil` from the unconditional
`pencilIsogBaseChange_isSeparable`.

## Landmine notes

* **`W_smooth W'` vs `⟨W'.toAffine⟩`**: `PullbackEvaluation`/`EvaluatesTo` are stated through
  `W_smooth`, the residue lemmas through the literal anonymous constructor.  They are
  *definitionally*
  equal (`W_smooth W = ⟨W.toAffine⟩` is `rfl`), so `exact` bridges them — but `rw` does **not**;
  every goal below is first `show`-normalised into a single spelling before rewriting.
* **`DecidableEq (AlgebraicClosure K)`**: supplied as the local `Classical.decEq _`, the same closed
  term every `OneSub*`/`Pencil*` file uses — the `Isogeny` *types* embed this instance, so a
  different instance would make the committed lemmas inapplicable.
* **`Isogeny.kernel β` vs `β.toAddMonoidHom.ker`**: definitionally equal (`kernel` is a one-line
  `def`); the count lemmas of `OneSubWitnesses.lean` are stated for `.toAddMonoidHom.ker` and are
  consumed here through the defeq at `have`-binding time, not by `rw`.
* **`(oneSubECIsogeny …).degree = β.degree` is `rfl`**: the `EC` curve-map degree and the Basic
  isogeny degree are the *same* `Module.finrank` over the same pullback-induced algebra (the
  `toCurveMap` is `Isogeny.endCurveMap`, whose `pullback` projection is `rfl`).  This is what lets
  the canonical-dual witness live at the canonical index `deg φE` with no transport.
* **`νPb` reduction**: `(dualGaloisData_oneSub …).νPb` reduces (through two `def`s and
  Prop-`have`s) to `(mulByInt W' (β.degree : ℤ)).pullback`, which is `dif_neg` away from
  `mulByInt_pullbackAlgHom` — the established `dualMulByInt_compose_mulByInt` trick.  This step is
  `whnf`-heavy (the witness terms are large); it carries a scoped `maxHeartbeats` bump.

## References

* Silverman, *The Arithmetic of Elliptic Curves*, III.4.10(c), III.5.5, III.6.1–III.6.2, V.1.3.
-/

open WeierstrassCurve HasseWeil.Curves

namespace HasseWeil.WeilPairing

open HasseWeil IsogenyBaseChangeConcrete

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.style.longLine false

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
variable (W : WeierstrassCurve K) [W.toAffine.IsElliptic] [Fintype W.toAffine.Point]
variable (p r : ℕ) [Fact p.Prime] [CharP K p] [Fact (Fintype.card K = p ^ r)]

noncomputable local instance instDecEqACPbEval : DecidableEq (AlgebraicClosure K) :=
  Classical.decEq _

variable [(W.baseChange (AlgebraicClosure K)).toAffine.IsElliptic]

/-! ### Deliverable 1 — the cofinite pullback-evaluation witness for `(1 − π)_{K̄}` -/

/-- **The excluded set for the `(1 − π)_{K̄}` witness: exactly the kernel** — the smooth points
whose image under `id − π̄` is `O`, i.e. (via the linchpin `ker(id − π̄) = E(𝔽_q)`) the geometric
Frobenius fixed points.  These are precisely the affine points where `(1 − π)^* x_gen` has poles,
so they *must* be excluded; nothing else is (the transport-to-`O` residue engine needs no
doubling or 2-torsion excisions). -/
def oneSubBad (hq : 2 ≤ Fintype.card K) :
    Set ((W_smooth (W.baseChange (AlgebraicClosure K))).SmoothPoint) :=
  {P | (oneSubFrobeniusIsogBaseChange W p r (AlgebraicClosure K)
      (oneSubFrobeniusPullback_L W (AlgebraicClosure K) hq)).toAddMonoidHom
      P.toAffinePoint = 0}

/-- **`oneSubBad` is finite** (Silverman V.1.1): the bad set injects into the kernel of
`(1 − π)_{K̄}` via the (injective) `toAffinePoint`, and the kernel is the image of the finite
`E(𝔽_q)` under the base-change inclusion (`oneSubFrobeniusIsogBaseChange_finiteKer`). -/
theorem oneSubBad_finite (hq : 2 ≤ Fintype.card K) : (oneSubBad W p r hq).Finite := by
  haveI hker : Finite (oneSubFrobeniusIsogBaseChange W p r (AlgebraicClosure K)
      (oneSubFrobeniusPullback_L W (AlgebraicClosure K) hq)).toAddMonoidHom.ker :=
    oneSubFrobeniusIsogBaseChange_finiteKer W p r _
  have hset : (((oneSubFrobeniusIsogBaseChange W p r (AlgebraicClosure K)
      (oneSubFrobeniusPullback_L W (AlgebraicClosure K) hq)).toAddMonoidHom.ker :
      AddSubgroup (W.baseChange (AlgebraicClosure K)).toAffine.Point) :
      Set (W.baseChange (AlgebraicClosure K)).toAffine.Point).Finite :=
    Set.toFinite _
  refine Set.Finite.subset (hset.preimage (Set.injOn_of_injective
    (smoothPoint_toAffinePoint_injective (W.baseChange (AlgebraicClosure K))))) ?_
  intro P hP
  exact Set.mem_preimage.mpr (AddMonoidHom.mem_ker.mpr hP)

/-- **DELIVERABLE 1 — the cofinite pullback-evaluation witness for `(1 − π)_{K̄}`**
(`WeilPairing/GenericCovarianceGeneral.lean` shape): at every smooth point `P` outside the kernel,
the stored point map lands at an affine point `(x', y')` and the pulled-back generators evaluate
there — `v_P((1 − π)^* x_gen − x') < 1` and the `y`-analogue.

The two `EvaluatesTo` facts are the committed Hasse-era residues, obtained *uniformly* (no
secant/tangent/2-torsion case split) from the transport-to-`O` engine
`isog_resid_at_affine_of_hgcomm_hinfty` fed the Wall A canonical generic-point covariance
`mapTranslateGenericPoint_oneSub_canonical` and the infinity order-transport
`inftyOrdTransport_oneSub` (both axiom-clean). -/
theorem pullbackEvaluation_oneSub (hq : 2 ≤ Fintype.card K) :
    PullbackEvaluation (W.baseChange (AlgebraicClosure K))
      (oneSubFrobeniusIsogBaseChange W p r (AlgebraicClosure K)
        (oneSubFrobeniusPullback_L W (AlgebraicClosure K) hq))
      (oneSubBad W p r hq) := by
  intro P hP
  rcases himg : (oneSubFrobeniusIsogBaseChange W p r (AlgebraicClosure K)
      (oneSubFrobeniusPullback_L W (AlgebraicClosure K) hq)).toAddMonoidHom
      P.toAffinePoint with _ | ⟨x', y', h'⟩
  · exact absurd himg hP
  · obtain ⟨hx, hy⟩ := isog_resid_at_affine_of_hgcomm_hinfty W
      (oneSubFrobeniusIsogBaseChange W p r (AlgebraicClosure K)
        (oneSubFrobeniusPullback_L W (AlgebraicClosure K) hq))
      (mapTranslateGenericPoint_oneSub_canonical W p r hq)
      (inftyOrdTransport_oneSub W p r hq) P h' himg
    -- `rcases himg :` rewrote the goal's occurrence of the image to `some x' y' h'`,
    -- so the equation component is `rfl`
    exact ⟨x', y', h', rfl, hx, hy⟩

/-! ### Deliverable 2(a) — `#ker(1 − π)_{K̄} = deg(1 − π)_{K̄}` from the general theory -/

/-- **Separability of `(1 − π)_{K̄}`** (Silverman III.5.5): from the `ω`-coefficient VALUE
transport `omegaPullbackCoeff (1 − π)_{K̄} = 1 ≠ 0` (`OneSubComapConcrete.lean`) through the
T-II-4-004 criterion `isSeparable_iff_omegaPullbackCoeff_ne_zero`. -/
theorem oneSubFrobeniusIsogBaseChange_isSeparable (hq : 2 ≤ Fintype.card K) :
    (oneSubFrobeniusIsogBaseChange W p r (AlgebraicClosure K)
      (oneSubFrobeniusPullback_L W (AlgebraicClosure K) hq)).IsSeparable :=
  (isSeparable_iff_omegaPullbackCoeff_ne_zero (W.baseChange (AlgebraicClosure K))
    (oneSubFrobeniusIsogBaseChange W p r (AlgebraicClosure K)
      (oneSubFrobeniusPullback_L W (AlgebraicClosure K) hq))).mpr
    (omegaPullbackCoeff_oneSubFrobeniusIsogBaseChange_ne_zero W p r hq)

/-- **PAYOFF (a) — `#ker(1 − π)_{K̄} = deg(1 − π)_{K̄}`** (Silverman III.4.10c): the W-3b general
separable count `card_kernel_eq_degree_of_separable` (`EC/KernelCountGeneral.lean`) instantiated at
the concrete `(1 − π)_{K̄}` through the new witness.  No `CoordHom`, no carried Galois data. -/
theorem card_kernel_eq_degree_oneSub (hq : 2 ≤ Fintype.card K) :
    Nat.card (oneSubFrobeniusIsogBaseChange W p r (AlgebraicClosure K)
        (oneSubFrobeniusPullback_L W (AlgebraicClosure K) hq)).kernel =
      (oneSubFrobeniusIsogBaseChange W p r (AlgebraicClosure K)
        (oneSubFrobeniusPullback_L W (AlgebraicClosure K) hq)).degree :=
  card_kernel_eq_degree_of_separable (W.baseChange (AlgebraicClosure K))
    (oneSubFrobeniusIsogBaseChange W p r (AlgebraicClosure K)
      (oneSubFrobeniusPullback_L W (AlgebraicClosure K) hq))
    (oneSubFrobeniusIsogBaseChange_isSeparable W p r hq)
    (oneSubBad_finite W p r hq) (pullbackEvaluation_oneSub W p r hq)

/-! ### Deliverable 2(b) — the V.1.3 reproof through the general theory -/

/-- **PAYOFF (b) — the K̄-level Silverman V.1.3 through the general theory**:
`deg(1 − π)_{K̄} = #E(𝔽_q)`.  Composition of the general count (a) with the proved fixed-point
count `#ker(1 − π)_{K̄} = pointCount W` (`oneSubFrobeniusIsogBaseChange_nat_card_ker_eq_pointCount`,
the geometric-Frobenius fixed-locus identification).

This derivation is **independent** of the Hasse-era V.1.3 route: it never touches the K-level
embeddings-classification `sepDeg γ = #ker γ` (`GapSpines`), going instead through the
localized-dictionary / kernel-torsor count over `K̄`. -/
theorem degree_oneSub_eq_pointCount (hq : 2 ≤ Fintype.card K) :
    (oneSubFrobeniusIsogBaseChange W p r (AlgebraicClosure K)
        (oneSubFrobeniusPullback_L W (AlgebraicClosure K) hq)).degree =
      pointCount W.toAffine := by
  have h1 : Nat.card (oneSubFrobeniusIsogBaseChange W p r (AlgebraicClosure K)
        (oneSubFrobeniusPullback_L W (AlgebraicClosure K) hq)).kernel =
      pointCount W.toAffine :=
    oneSubFrobeniusIsogBaseChange_nat_card_ker_eq_pointCount W p r _
  exact (card_kernel_eq_degree_oneSub W p r hq).symm.trans h1

include p r in
/-- **PAYOFF (b′) — the K-level Silverman V.1.3, reproved**: `deg(1 − π) = #E(𝔽_q)` over the
*finite field* `K` itself, via degree base-change
(`oneSubFrobeniusIsogBaseChange_degree_eq_of_finrankBaseChange`, the tensor-finrank transport) and
the new K̄-level identity.  The same statement as the Hasse-era
`GapSpines.isogOneSub_negFrobenius_degree_eq_pointCount`, by a now-independent proof — the two
derivations agree (they prove the literal same proposition). -/
theorem isogOneSub_negFrobenius_degree_eq_pointCount_general (hq : 2 ≤ Fintype.card K) :
    (isogOneSub_negFrobenius W hq).degree = pointCount W.toAffine :=
  (oneSubFrobeniusIsogBaseChange_degree_eq_of_finrankBaseChange W p r
      (AlgebraicClosure K) hq).symm.trans
    (degree_oneSub_eq_pointCount W p r hq)

/-! ### Deliverable 2(d) — `h_normal` / `hdesc` for `(1 − π)_{K̄}`, free -/

/-- **PAYOFF (d) — `h_normal` for `(1 − π)_{K̄}`** (Silverman III.4.10c): the function-field
extension `K(E_{K̄}) / (1 − π)^* K(E_{K̄})` is normal — a theorem via
`normal_of_separable_general`. -/
theorem oneSub_normal (hq : 2 ≤ Fintype.card K) :
    letI := (oneSubFrobeniusIsogBaseChange W p r (AlgebraicClosure K)
      (oneSubFrobeniusPullback_L W (AlgebraicClosure K) hq)).toAlgebra
    Normal (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField
      (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField :=
  normal_of_separable_general (W.baseChange (AlgebraicClosure K))
    (oneSubFrobeniusIsogBaseChange W p r (AlgebraicClosure K)
      (oneSubFrobeniusPullback_L W (AlgebraicClosure K) hq))
    (oneSubFrobeniusIsogBaseChange_isSeparable W p r hq)
    (oneSubBad_finite W p r hq) (pullbackEvaluation_oneSub W p r hq)

/-- **PAYOFF (d) — `hdesc` for `(1 − π)_{K̄}`** (Silverman III.4.10c, the generic-point translation
torsor): every automorphism of `K(E_{K̄})` over the pullback image translates the generic point by
a rational kernel point — a theorem via `hdesc_of_separable_general`. -/
theorem oneSub_hdesc (hq : 2 ≤ Fintype.card K) :
    ∀ σ : (@AlgEquiv (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField
        (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField
        (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField _ _ _
        (oneSubFrobeniusIsogBaseChange W p r (AlgebraicClosure K)
          (oneSubFrobeniusPullback_L W (AlgebraicClosure K) hq)).toAlgebra
        (oneSubFrobeniusIsogBaseChange W p r (AlgebraicClosure K)
          (oneSubFrobeniusPullback_L W (AlgebraicClosure K) hq)).toAlgebra),
      ∃ k : (W.baseChange (AlgebraicClosure K)).toAffine.Point,
        k ∈ (oneSubFrobeniusIsogBaseChange W p r (AlgebraicClosure K)
          (oneSubFrobeniusPullback_L W (AlgebraicClosure K) hq)).kernel ∧
        liftPointToKE (W.baseChange (AlgebraicClosure K)) k =
          genericPointAct (W.baseChange (AlgebraicClosure K))
            (oneSubFrobeniusIsogBaseChange W p r (AlgebraicClosure K)
              (oneSubFrobeniusPullback_L W (AlgebraicClosure K) hq)) σ -
            genericPoint (W.baseChange (AlgebraicClosure K)) :=
  hdesc_of_separable_general (W.baseChange (AlgebraicClosure K))
    (oneSubFrobeniusIsogBaseChange W p r (AlgebraicClosure K)
      (oneSubFrobeniusPullback_L W (AlgebraicClosure K) hq))
    (oneSubFrobeniusIsogBaseChange_isSeparable W p r hq)
    (oneSubBad_finite W p r hq) (pullbackEvaluation_oneSub W p r hq)

/-! ### Deliverable 2(c) — the dual: the `EC.Isogeny` incarnation and the class machinery -/

/-- **`(1 − π)_{K̄}` as an `EC.Isogeny`** — the algebro-geometric incarnation the dual machinery
consumes: the curve map is `Isogeny.endCurveMap` of the Basic isogeny (same pullback, `rfl`), and
the basepoint condition (`pullback_ordAtInfty_nonneg`, "the morphism is defined at `O`") is derived
from the committed infinity order-transport `inftyOrdTransport_oneSub` (`ord_∞((1 − π)^* f) =
ord_∞ f`, in particular regularity is preserved). -/
noncomputable def oneSubECIsogeny (hq : 2 ≤ Fintype.card K) :
    EC.Isogeny (W.baseChange (AlgebraicClosure K)).toAffine
      (W.baseChange (AlgebraicClosure K)).toAffine where
  toCurveMap := (oneSubFrobeniusIsogBaseChange W p r (AlgebraicClosure K)
      (oneSubFrobeniusPullback_L W (AlgebraicClosure K) hq)).endCurveMap
      (W.baseChange (AlgebraicClosure K))
  pullback_ordAtInfty_nonneg := by
    intro f hf
    change 0 ≤ (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ :
        SmoothPlaneCurve (AlgebraicClosure K)).ordAtInfty
      ((oneSubFrobeniusIsogBaseChange W p r (AlgebraicClosure K)
        (oneSubFrobeniusPullback_L W (AlgebraicClosure K) hq)).pullback f)
    rcases eq_or_ne f 0 with rfl | hf0
    · rw [map_zero,
        ((⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ :
          SmoothPlaneCurve (AlgebraicClosure K)).ordAtInfty_eq_top_iff
          (0 : (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField)).mpr rfl]
      exact le_top
    · have hpb0 : (oneSubFrobeniusIsogBaseChange W p r (AlgebraicClosure K)
          (oneSubFrobeniusPullback_L W (AlgebraicClosure K) hq)).pullback f ≠ 0 :=
        fun h0 => hf0 ((oneSubFrobeniusIsogBaseChange W p r (AlgebraicClosure K)
          (oneSubFrobeniusPullback_L W (AlgebraicClosure K) hq)).pullback_injective
          (h0.trans (map_zero _).symm))
      have htr : ((⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ :
            SmoothPlaneCurve (AlgebraicClosure K)).ordAtInfty
            ((oneSubFrobeniusIsogBaseChange W p r (AlgebraicClosure K)
              (oneSubFrobeniusPullback_L W (AlgebraicClosure K) hq)).pullback f)).untopD 0 =
          ((⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ :
            SmoothPlaneCurve (AlgebraicClosure K)).ordAtInfty f).untopD 0 :=
        inftyOrdTransport_oneSub W p r hq f
      obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp
        (((⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ :
          SmoothPlaneCurve (AlgebraicClosure K)).ordAtInfty_eq_top_iff f).not.mpr hf0)
      obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp
        (((⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ :
          SmoothPlaneCurve (AlgebraicClosure K)).ordAtInfty_eq_top_iff _).not.mpr hpb0)
      rw [← hm, ← hn, WithTop.untopD_coe, WithTop.untopD_coe] at htr
      rw [← hn] at hf
      rw [← hm]
      exact_mod_cast htr ▸ hf

/-- The `EC` incarnation has the same pullback as the Basic one — definitionally. -/
theorem oneSubECIsogeny_pullback (hq : 2 ≤ Fintype.card K) :
    (oneSubECIsogeny W p r hq).toCurveMap.pullback =
      (oneSubFrobeniusIsogBaseChange W p r (AlgebraicClosure K)
        (oneSubFrobeniusPullback_L W (AlgebraicClosure K) hq)).pullback := rfl

/-- The `EC` curve-map degree agrees with the Basic isogeny degree — definitionally (the same
`Module.finrank` over the same pullback-induced algebra). -/
theorem oneSubECIsogeny_degree (hq : 2 ≤ Fintype.card K) :
    (oneSubECIsogeny W p r hq).degree =
      (oneSubFrobeniusIsogBaseChange W p r (AlgebraicClosure K)
        (oneSubFrobeniusPullback_L W (AlgebraicClosure K) hq)).degree := rfl

/-- `deg (oneSubECIsogeny) = #E(𝔽_q)` — the V.1.3 identity transported to the `EC` incarnation. -/
theorem oneSubECIsogeny_degree_eq_pointCount (hq : 2 ≤ Fintype.card K) :
    (oneSubECIsogeny W p r hq).degree = pointCount W.toAffine :=
  (oneSubECIsogeny_degree W p r hq).trans (degree_oneSub_eq_pointCount W p r hq)

/-- **PAYOFF (c) — `DualGaloisData` for `(1 − π)_{K̄}`, fully unconditional** (Silverman
III.4.10–4.11, III.6.1): the general-class assembler `dualGaloisData_of_pullbackEvaluation_general`
applied verbatim — `h_pb` is `rfl`, separability and the witness are the theorems above, and
`h_normal`/`hdesc`/`hν`/`#ker = deg` are all *derived* by the class machinery. -/
noncomputable def dualGaloisData_oneSub (hq : 2 ≤ Fintype.card K) :
    EC.Isogeny.DualGaloisData (oneSubECIsogeny W p r hq) :=
  dualGaloisData_of_pullbackEvaluation_general (W.baseChange (AlgebraicClosure K))
    (oneSubECIsogeny W p r hq)
    (oneSubFrobeniusIsogBaseChange W p r (AlgebraicClosure K)
      (oneSubFrobeniusPullback_L W (AlgebraicClosure K) hq))
    rfl (oneSubFrobeniusIsogBaseChange_isSeparable W p r hq)
    (oneSubBad_finite W p r hq) (pullbackEvaluation_oneSub W p r hq)

include p r in
/-- **PAYOFF (c) — `exists_dual` for `(1 − π)_{K̄}`** (Silverman III.6.1): the reverse isogeny
exists, with no carried witnesses. -/
theorem exists_dual_oneSub (hq : 2 ≤ Fintype.card K) :
    Nonempty (EC.Isogeny (W.baseChange (AlgebraicClosure K)).toAffine
      (W.baseChange (AlgebraicClosure K)).toAffine) :=
  exists_dual_of_pullbackEvaluation_general (W.baseChange (AlgebraicClosure K))
    (oneSubECIsogeny W p r hq)
    (oneSubFrobeniusIsogBaseChange W p r (AlgebraicClosure K)
      (oneSubFrobeniusPullback_L W (AlgebraicClosure K) hq))
    rfl (oneSubFrobeniusIsogBaseChange_isSeparable W p r hq)
    (oneSubBad_finite W p r hq) (pullbackEvaluation_oneSub W p r hq)

/-- **PAYOFF (c) — the `[n]`-pullback covariance for `(1 − π)_{K̄}`, every `n ≠ 0` at once**
(Silverman III.4.8 for the class): `CovarianceDischarge`'s
`mulByIntPullbackCovariant_of_pullbackEvaluation` applied verbatim. -/
theorem oneSub_mulByIntPullbackCovariant (hq : 2 ≤ Fintype.card K) (n : ℤ) (hn : n ≠ 0) :
    (oneSubECIsogeny W p r hq).MulByIntPullbackCovariant n hn :=
  EC.Isogeny.mulByIntPullbackCovariant_of_pullbackEvaluation (oneSubECIsogeny W p r hq)
    (oneSubFrobeniusIsogBaseChange W p r (AlgebraicClosure K)
      (oneSubFrobeniusPullback_L W (AlgebraicClosure K) hq))
    rfl (oneSubBad_finite W p r hq) (pullbackEvaluation_oneSub W p r hq) n hn

set_option maxHeartbeats 1600000 in
-- unfolding `(dualGaloisData_oneSub …).νPb` through the class assemblers (whose arguments are
-- the large witness terms) is `whnf`-heavy, exactly as in `dualMulByInt_compose_mulByInt`
/-- **The deep III.6.1 range inclusion for `(1 − π)_{K̄}` at the canonical index**:
`Im([deg]^*) ⊆ Im((1 − π)^*)`.  Extracted from the Galois data (`DualGaloisData.hincl` = the
III.4.11 fixed-field argument), with `νPb = ([deg])^*` converted to `mulByInt_pullbackAlgHom` by
`dif_neg` and the index transported along the definitional `deg φE = deg β`. -/
theorem oneSub_mulByInt_deg_rangeIncl (hq : 2 ≤ Fintype.card K) :
    (HasseWeil.mulByInt_pullbackAlgHom (W.baseChange (AlgebraicClosure K)).toAffine
        (((oneSubECIsogeny W p r hq).degree : ℤ))
        (oneSubECIsogeny W p r hq).intDegree_ne_zero).range ≤
      (oneSubECIsogeny W p r hq).toCurveMap.pullback.range := by
  have h := (dualGaloisData_oneSub W p r hq).hincl
  have hν : (dualGaloisData_oneSub W p r hq).νPb =
      HasseWeil.mulByInt_pullbackAlgHom (W.baseChange (AlgebraicClosure K)).toAffine
        (((oneSubECIsogeny W p r hq).degree : ℤ))
        (oneSubECIsogeny W p r hq).intDegree_ne_zero :=
    dif_neg (oneSubECIsogeny W p r hq).intDegree_ne_zero
  rwa [hν] at h

/-- **PAYOFF (c) — the canonical-dual witness for `(1 − π)_{K̄}`, a theorem** (Silverman III.6.1's
exact bookkeeping at `n = deg`): the range inclusion is the Galois-data extraction above, and the
basepoint condition follows from the `[n]`-basepoint theorem (`mulByIntBasepoint_holds`) plus the
unconditional `∞`-regularity reflection (`EC.Isogeny.reflects_ordAtInfty`). -/
noncomputable def oneSubHasCanonicalDualWitness (hq : 2 ≤ Fintype.card K) :
    (oneSubECIsogeny W p r hq).HasCanonicalDualWitness where
  hincl := oneSub_mulByInt_deg_rangeIncl W p r hq
  hbase := EC.Isogeny.hbase_of_reflects (oneSubECIsogeny W p r hq) _
    (oneSub_mulByInt_deg_rangeIncl W p r hq)
    (EC.mulByIntBasepoint_holds (W.baseChange (AlgebraicClosure K)).toAffine
      (oneSubECIsogeny W p r hq).intDegree_ne_zero)
    (fun g hg => EC.Isogeny.reflects_ordAtInfty (oneSubECIsogeny W p r hq) g hg)

/-- **PAYOFF (c) — THE canonical dual of `(1 − π)_{K̄}`** (Silverman III.6.1): `((1 − π)_{K̄})^`,
fully unconditional. -/
noncomputable def oneSubCanonicalDual (hq : 2 ≤ Fintype.card K) :
    EC.Isogeny (W.baseChange (AlgebraicClosure K)).toAffine
      (W.baseChange (AlgebraicClosure K)).toAffine :=
  (oneSubECIsogeny W p r hq).canonicalDual (oneSubHasCanonicalDualWitness W p r hq)

/-- **The defining composition** `((1 − π)^) ∘ (1 − π) = [deg(1 − π)]` (Silverman III.6.1). -/
theorem oneSubCanonicalDual_compose (hq : 2 ≤ Fintype.card K) :
    (oneSubCanonicalDual W p r hq).compose (oneSubECIsogeny W p r hq) =
      EC.Isogeny.mulByInt (W.baseChange (AlgebraicClosure K)).toAffine
        (oneSubECIsogeny W p r hq).intDegree_ne_zero :=
  (oneSubECIsogeny W p r hq).canonicalDual_compose (oneSubHasCanonicalDualWitness W p r hq)

/-- **The `∃!` of the dual** (Silverman III.6.1(a)): exactly one reverse isogeny composes with
`(1 − π)_{K̄}` to `[deg(1 − π)]`. -/
theorem oneSub_existsUnique_dual (hq : 2 ≤ Fintype.card K) :
    ∃! ψ : EC.Isogeny (W.baseChange (AlgebraicClosure K)).toAffine
        (W.baseChange (AlgebraicClosure K)).toAffine,
      ψ.compose (oneSubECIsogeny W p r hq) =
        EC.Isogeny.mulByInt (W.baseChange (AlgebraicClosure K)).toAffine
          (oneSubECIsogeny W p r hq).intDegree_ne_zero :=
  (oneSubECIsogeny W p r hq).existsUnique_dual (oneSubHasCanonicalDualWitness W p r hq)

/-- **The second composition** `(1 − π) ∘ ((1 − π)^) = [deg(1 − π)]` (Silverman III.6.2(a)) — the
covariance hypothesis is discharged by the class machinery (`CovarianceDischarge`). -/
theorem oneSub_compose_canonicalDual (hq : 2 ≤ Fintype.card K) :
    (oneSubECIsogeny W p r hq).compose (oneSubCanonicalDual W p r hq) =
      EC.Isogeny.mulByInt (W.baseChange (AlgebraicClosure K)).toAffine
        (oneSubECIsogeny W p r hq).intDegree_ne_zero :=
  EC.Isogeny.compose_canonicalDual_of_pullbackEvaluation (oneSubECIsogeny W p r hq)
    (oneSubFrobeniusIsogBaseChange W p r (AlgebraicClosure K)
      (oneSubFrobeniusPullback_L W (AlgebraicClosure K) hq))
    rfl (oneSubBad_finite W p r hq) (pullbackEvaluation_oneSub W p r hq)
    (oneSubHasCanonicalDualWitness W p r hq)

/-- **`deg((1 − π)^) = deg(1 − π) = #E(𝔽_q)`** (Silverman III.6.2(d) + V.1.3): the canonical dual
of `(1 − π)_{K̄}` also has degree the point count. -/
theorem oneSubCanonicalDual_degree_eq_pointCount (hq : 2 ≤ Fintype.card K) :
    (oneSubCanonicalDual W p r hq).degree = pointCount W.toAffine :=
  ((oneSubECIsogeny W p r hq).canonicalDual_degree
      (oneSubHasCanonicalDualWitness W p r hq)).trans
    (oneSubECIsogeny_degree_eq_pointCount W p r hq)

/-- **The double dual `((1 − π)^)^ = (1 − π)`** (Silverman III.6.2(e)) — every hypothesis beyond
the witness is discharged by the class machinery. -/
theorem oneSub_canonicalDual_canonicalDual (hq : 2 ≤ Fintype.card K) :
    (oneSubCanonicalDual W p r hq).canonicalDual
        ((oneSubECIsogeny W p r hq).canonicalDual_hasCanonicalDualWitness
          (oneSubHasCanonicalDualWitness W p r hq)
          ((oneSubECIsogeny W p r hq).mulByIntPullbackCovariant_of_pullbackEvaluation
            (oneSubFrobeniusIsogBaseChange W p r (AlgebraicClosure K)
              (oneSubFrobeniusPullback_L W (AlgebraicClosure K) hq))
            rfl (oneSubBad_finite W p r hq) (pullbackEvaluation_oneSub W p r hq) _
            (oneSubECIsogeny W p r hq).intDegree_ne_zero)) =
      oneSubECIsogeny W p r hq :=
  EC.Isogeny.canonicalDual_canonicalDual_of_pullbackEvaluation (oneSubECIsogeny W p r hq)
    (oneSubFrobeniusIsogBaseChange W p r (AlgebraicClosure K)
      (oneSubFrobeniusPullback_L W (AlgebraicClosure K) hq))
    rfl (oneSubBad_finite W p r hq) (pullbackEvaluation_oneSub W p r hq)
    (oneSubHasCanonicalDualWitness W p r hq)

/-! ### Stretch — the same witness for the pencil `(rπ − s)_{K̄}` (`p ∤ r'`, `p ∤ s'`) -/

/-- **The excluded set for the `(rπ − s)_{K̄}` witness: exactly the kernel.** -/
def pencilBad (r' s' : ℤ) (hr : r' ≠ 0) (hs : s' ≠ 0)
    (hrK : (r' : K) ≠ 0) (hsK : (s' : K) ≠ 0) :
    Set ((W_smooth (W.baseChange (AlgebraicClosure K))).SmoothPoint) :=
  {P | (pencilIsogBaseChange W p r (AlgebraicClosure K) r' s'
      (pencilBaseChangePullback W (AlgebraicClosure K) r' s' hr hs hrK hsK)).toAddMonoidHom
      P.toAffinePoint = 0}

/-- **`pencilBad` is finite** — via the trace-free kernel finiteness
`pencilIsogBaseChange_finiteKer`. -/
theorem pencilBad_finite (r' s' : ℤ) (hr : r' ≠ 0) (hs : s' ≠ 0)
    (hrK : (r' : K) ≠ 0) (hsK : (s' : K) ≠ 0) :
    (pencilBad W p r r' s' hr hs hrK hsK).Finite := by
  haveI hker : Finite (pencilIsogBaseChange W p r (AlgebraicClosure K) r' s'
      (pencilBaseChangePullback W (AlgebraicClosure K) r' s' hr hs hrK hsK)).toAddMonoidHom.ker :=
    pencilIsogBaseChange_finiteKer W p r r' s' hr hs hrK hsK
  have hset : (((pencilIsogBaseChange W p r (AlgebraicClosure K) r' s'
      (pencilBaseChangePullback W (AlgebraicClosure K) r' s' hr hs hrK hsK)).toAddMonoidHom.ker :
      AddSubgroup (W.baseChange (AlgebraicClosure K)).toAffine.Point) :
      Set (W.baseChange (AlgebraicClosure K)).toAffine.Point).Finite :=
    Set.toFinite _
  refine Set.Finite.subset (hset.preimage (Set.injOn_of_injective
    (smoothPoint_toAffinePoint_injective (W.baseChange (AlgebraicClosure K))))) ?_
  intro P hP
  exact Set.mem_preimage.mpr (AddMonoidHom.mem_ker.mpr hP)

/-- **STRETCH — the cofinite pullback-evaluation witness for `(rπ − s)_{K̄}`** (`p ∤ r'`,
`p ∤ s'`): the wiring is uniform with `1 − π` — the residues at every affine image are the
committed `pencil_two_residues` (the same transport-to-`O` engine, axiom-clean), and the excluded
set is exactly the kernel. -/
theorem pullbackEvaluation_pencil (r' s' : ℤ) (hr : r' ≠ 0) (hs : s' ≠ 0)
    (hrK : (r' : K) ≠ 0) (hsK : (s' : K) ≠ 0) :
    PullbackEvaluation (W.baseChange (AlgebraicClosure K))
      (pencilIsogBaseChange W p r (AlgebraicClosure K) r' s'
        (pencilBaseChangePullback W (AlgebraicClosure K) r' s' hr hs hrK hsK))
      (pencilBad W p r r' s' hr hs hrK hsK) := by
  intro P hP
  rcases himg : (pencilIsogBaseChange W p r (AlgebraicClosure K) r' s'
      (pencilBaseChangePullback W (AlgebraicClosure K) r' s' hr hs hrK hsK)).toAddMonoidHom
      P.toAffinePoint with _ | ⟨x', y', h'⟩
  · exact absurd himg hP
  · obtain ⟨hx, hy⟩ := pencil_two_residues W p r r' s' hr hs hrK hsK P h' himg
    -- the goal's image occurrence was rewritten by `rcases himg :`, so the equation is `rfl`
    exact ⟨x', y', h', rfl, hx, hy⟩

/-- **STRETCH payoff — `#ker(rπ − s)_{K̄} = deg(rπ − s)_{K̄}`** (Silverman III.4.10c) for `p ∤ r'`,
`p ∤ s'`: the general separable count at the pencil, with the unconditional separability
`pencilIsogBaseChange_isSeparable`. -/
theorem card_kernel_eq_degree_pencil (r' s' : ℤ) (hr : r' ≠ 0) (hs : s' ≠ 0)
    (hrK : (r' : K) ≠ 0) (hsK : (s' : K) ≠ 0) :
    Nat.card (pencilIsogBaseChange W p r (AlgebraicClosure K) r' s'
        (pencilBaseChangePullback W (AlgebraicClosure K) r' s' hr hs hrK hsK)).kernel =
      (pencilIsogBaseChange W p r (AlgebraicClosure K) r' s'
        (pencilBaseChangePullback W (AlgebraicClosure K) r' s' hr hs hrK hsK)).degree :=
  card_kernel_eq_degree_of_separable (W.baseChange (AlgebraicClosure K))
    (pencilIsogBaseChange W p r (AlgebraicClosure K) r' s'
      (pencilBaseChangePullback W (AlgebraicClosure K) r' s' hr hs hrK hsK))
    (pencilIsogBaseChange_isSeparable W p r (AlgebraicClosure K) r' s' hr hs hrK hsK)
    (pencilBad_finite W p r r' s' hr hs hrK hsK)
    (pullbackEvaluation_pencil W p r r' s' hr hs hrK hsK)

end HasseWeil.WeilPairing
