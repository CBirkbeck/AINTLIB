/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».FarguesFontaine.CurveObject
import «Adic spaces».StronglyNoetherianTransport
import «Adic spaces».WedhornCechAcyclicity
import «Adic spaces».StructurePresheafBundled
import «Adic spaces».SpaParameterPerturbation
import «Adic spaces».RelativePieceKeystone

/-!
# X-ADIC-1: the adic Fargues–Fontaine curve as an `AdicSpacePresentation`

The topological-chart layer of PLAN-GATE-3's local-isomorphism property:
every curve point has an open neighbourhood homeomorphic to the adic
spectrum of an affinoid adic presentation. This file builds
(A1) the wandering-image homeomorphism `↥W ≃ₜ ↥(xImage W)`, and
(A3-core) strong noetherianity of the window chart rings; the affinoid
packaging and the pointwise assembly follow.
-/

open TopologicalRing ValuationSpectrum WittVector NNReal TopologicalSpace Topology CategoryTheory Opposite

set_option linter.overlappingInstances false

noncomputable section

namespace FarguesFontaine

variable (p : ℕ) [Fact (Nat.Prime p)]
variable (F : Type*) [Field F] [TopologicalSpace F] [IsTopologicalRing F]
  [UniformSpace F] [NonarchimedeanRing F] [IsPerfectoidField p F] [CharP F p]
variable (ϖ : PseudoUniformizer F)


/-- **Injectivity of the projection on wandering opens** (X-ADIC-1 A1): on an
open with pairwise-disjoint Frobenius translates, the quotient map is
injective. -/
theorem yTopToCurve_injOn_of_disjoint_translates {W : Opens ↥(yTop p F ϖ)}
    (hdis : ∀ k : ℤ, k ≠ 0 →
      Disjoint (((Opens.map (yFrobTop p F ϖ k)).obj W
          : Opens ↥(yTop p F ϖ)) : Set ↥(yTop p F ϖ))
        ((W : Opens ↥(yTop p F ϖ)) : Set ↥(yTop p F ϖ)))
    {w w' : ↥(yTop p F ϖ)} (hw : w ∈ W) (hw' : w' ∈ W)
    (h : yTopToCurve p F ϖ w = yTopToCurve p F ϖ w') : w = w' := by
  have hrel : yTopToY p F ϖ w ∈ MulAction.orbit (Multiplicative ℤ)
      (yTopToY p F ϖ w') :=
    MulAction.orbitRel_apply.mp (Quotient.eq''.mp h)
  obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp hrel
  set k : ℤ := -(Multiplicative.toAdd g) with hkdef
  have hkey : yTopToY p F ϖ (yFrobTop p F ϖ k w') = yTopToY p F ϖ w := by
    rw [yTopToY_yFrobTop p F ϖ k w', hkdef, neg_neg, ofAdd_toAdd]
    exact hg
  have hween : yFrobTop p F ϖ k w' = w := (yTopToY_bijective p F ϖ).1 hkey
  rcases eq_or_ne k 0 with hk0 | hk0
  · rw [hk0, yFrobTop_zero p F ϖ w'] at hween
    exact hween.symm
  · exfalso
    have hmem : w' ∈ ((Opens.map (yFrobTop p F ϖ k)).obj W
        : Set ↥(yTop p F ϖ)) := by
      show yFrobTop p F ϖ k w' ∈ (W : Set ↥(yTop p F ϖ))
      rw [hween]
      exact hw
    exact Set.disjoint_left.mp (hdis k hk0) hmem hw'

/-- The projection-onto-image equivalence on a wandering open. -/
noncomputable def xImageEquiv {W : Opens ↥(yTop p F ϖ)}
    (hdis : ∀ k : ℤ, k ≠ 0 →
      Disjoint (((Opens.map (yFrobTop p F ϖ k)).obj W
          : Opens ↥(yTop p F ϖ)) : Set ↥(yTop p F ϖ))
        ((W : Opens ↥(yTop p F ϖ)) : Set ↥(yTop p F ϖ))) :
    ↥(W : Set ↥(yTop p F ϖ)) ≃ ↥((xImage p F ϖ W) : Set (Curve p F ϖ)) where
  toFun w := ⟨yTopToCurve p F ϖ w.1, ⟨w.1, w.2, rfl⟩⟩
  invFun x := ⟨x.2.choose, x.2.choose_spec.1⟩
  left_inv w := by
    refine Subtype.ext ?_
    exact yTopToCurve_injOn_of_disjoint_translates p F ϖ hdis
      (⟨yTopToCurve p F ϖ w.1, ⟨w.1, w.2, rfl⟩⟩
        : ↥((xImage p F ϖ W) : Set (Curve p F ϖ))).2.choose_spec.1 w.2
      (⟨yTopToCurve p F ϖ w.1, ⟨w.1, w.2, rfl⟩⟩
        : ↥((xImage p F ϖ W) : Set (Curve p F ϖ))).2.choose_spec.2
  right_inv x := Subtype.ext x.2.choose_spec.2

/-- **The wandering-image homeomorphism** (X-ADIC-1 A1): on a wandering open
the curve projection restricts to a homeomorphism onto its open image. -/
noncomputable def xImageHomeo {W : Opens ↥(yTop p F ϖ)}
    (hdis : ∀ k : ℤ, k ≠ 0 →
      Disjoint (((Opens.map (yFrobTop p F ϖ k)).obj W
          : Opens ↥(yTop p F ϖ)) : Set ↥(yTop p F ϖ))
        ((W : Opens ↥(yTop p F ϖ)) : Set ↥(yTop p F ϖ))) :
    ↥(W : Set ↥(yTop p F ϖ)) ≃ₜ ↥((xImage p F ϖ W) : Set (Curve p F ϖ)) := by
  refine Equiv.toHomeomorphOfContinuousOpen (xImageEquiv p F ϖ hdis) ?_ ?_
  · exact Continuous.subtype_mk
      ((continuous_yTopToCurve p F ϖ).comp continuous_subtype_val) _
  · intro O hO
    obtain ⟨U, hU, rfl⟩ := isOpen_induced_iff.mp hO
    have himg : (xImageEquiv p F ϖ hdis) '' (Subtype.val ⁻¹' U)
        = Subtype.val ⁻¹' (yTopToCurve p F ϖ ''
            (U ∩ (W : Set ↥(yTop p F ϖ)))) := by
      ext x
      constructor
      · rintro ⟨w, hwU, rfl⟩
        exact ⟨w.1, ⟨hwU, w.2⟩, rfl⟩
      · rintro ⟨w, ⟨hwU, hwW⟩, hwx⟩
        refine ⟨⟨w, hwW⟩, hwU, ?_⟩
        exact Subtype.ext hwx
    rw [himg]
    refine (IsOpen.preimage continuous_subtype_val ?_)
    exact (isOpenQuotientMap_yTopToCurve p F ϖ).isOpenMap _
      (hU.inter W.2)


/-- **The window chart rings are strongly noetherian** (X-ADIC-1 A3 core,
Kedlaya Theorem 4.10 transported to the chart presheaf value): the mirror of
`isSheafy_canonical_window` at the strong-noetherianity predicate. -/
theorem isStronglyNoetherian_canonical_window (n : ℤ) :
    IsStronglyNoetherian (presheafValue
      (chartData p F (windowUnif p F ϖ n) 1 1 p 1)) := by
  have hp : 1 < p := one_lt_p p
  have hρ₁0 := vpi_pos p F (windowUnif p F ϖ n)
  have hρ₁1 := perfectoidValuation_toOF_lt_one p F (windowUnif p F ϖ n)
  have hρ₂0 := rhoRight_pos p F (windowUnif p F ϖ n) p 1
  have hρ₂1 := rhoRight_lt_one p F (windowUnif p F ϖ n) p 1 (by omega) one_pos
  have h12 : perfectoidValuation p F
      ((PseudoUniformizer.toOF F (windowUnif p F ϖ n) : OF F) : F)
      ≤ rhoRight p F (windowUnif p F ϖ n) p 1 :=
    vpi_le_rho2_of_exact p F (windowUnif p F ϖ n) (hρ₁1 := hρ₁1)
      p 1 (by omega) one_pos (by omega) rfl (window_hexact2 p F ϖ n)
  have hexact' : perfectoidValuation p F
      ((PseudoUniformizer.toOF F (windowUnif p F ϖ n) : OF F) : F) ^ (1 * 1)
      = perfectoidValuation p F
        ((PseudoUniformizer.toOF F (windowUnif p F ϖ n) : OF F) : F) := by
    rw [one_mul, pow_one]
  have hbb : wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1
      (BIProd p F (windowUnif p F ϖ n) hρ₁0 hρ₁1 hρ₂0 hρ₂1
        (teichPowOverP p F (windowUnif p F ϖ n)
          ((PseudoUniformizer.toOF F (windowUnif p F ϖ n)) ^ 1) 1)) ≤ 1 := by
    refine wI_teichPowOverP_le_one p F (windowUnif p F ϖ n) h12 ?_
    rw [perfectoidValuation_pow_toOF p F (windowUnif p F ϖ n)]
    exact le_of_eq hexact'
  have hSN : IsStronglyNoetherian
      ↥(BISub p F (windowUnif p F ϖ n) hρ₁0 hρ₁1 hρ₂0 hρ₂1) :=
    isStronglyNoetherian_BISub p F (windowUnif p F ϖ n) h12 1 1
      (BIProd_mem_BISub p F (windowUnif p F ϖ n) _) hbb hexact'
  exact (ValuationSpectrum.isStronglyNoetherian_congr
    ((presheafChartRingEquivBISub p F (windowUnif p F ϖ n)
      (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1) (hρ₂0 := hρ₂0) (hρ₂1 := hρ₂1)
      p 1 (by omega) one_pos (by omega) rfl (window_hexact2 p F ϖ n)).symm)
    (presheafChartRingEquivBISub_symm_continuous p F (windowUnif p F ϖ n)
      (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1) (hρ₂0 := hρ₂0) (hρ₂1 := hρ₂1)
      p 1 (by omega) one_pos (by omega) rfl (window_hexact2 p F ϖ n))
    (presheafChartRingEquivBISub_continuous p F (windowUnif p F ϖ n)
      (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1) (hρ₂0 := hρ₂0) (hρ₂1 := hρ₂1)
      p 1 (by omega) one_pos (by omega) rfl (window_hexact2 p F ϖ n))).mp hSN

/-- The `n`-th window chart ring (abbreviation for the X-ADIC-1 assembly). -/
noncomputable abbrev windowChartRing (n : ℤ) :=
  presheafValue (chartData p F (windowUnif p F ϖ n) 1 1 p 1)

noncomputable local instance (n : ℤ) : IsTateRing (windowChartRing p F ϖ n) :=
  isTateRing_bigWindowChart p F (windowUnif p F ϖ n)

noncomputable local instance (n : ℤ) :
    IsStronglyNoetherian (windowChartRing p F ϖ n) :=
  isStronglyNoetherian_canonical_window p F ϖ n

noncomputable local instance (n : ℤ) :
    IsNoetherianRing (windowChartRing p F ϖ n) :=
  IsStronglyNoetherian.isNoetherianRing _

/-- **The affinoid presentation of a rational subdomain of a window chart**
(X-ADIC-1 A3): the value ring of any rational datum over a window chart ring
is a sheafy complete Tate ring, hence an affinoid adic presentation. -/
noncomputable def windowSubAffinoid (n : ℤ)
    (D' : RationalLocData (windowChartRing p F ϖ n)) :
    ValuationSpectrum.AffinoidAdicPresentation :=
  letI : IsTateRing (presheafValue D') := presheafValue_isTateRing_concrete D'
  letI : IsStronglyNoetherian (presheafValue D') :=
    presheafValue_isStronglyNoetherian_faithful D'
  letI : @CompleteSpace (presheafValue D')
      (IsTopologicalAddGroup.rightUniformSpace (presheafValue D')) :=
    completeSpace_right_presheafValue D'
  letI : ValuationSpectrum.IsSheafy (presheafValue D') :=
    ValuationSpectrum.isSheafy_of_stronglyNoetherian_828b
  ValuationSpectrum.AffinoidAdicPresentation.ofIsSheafy (presheafValue D')

noncomputable local instance : DecidableEq (Ainf p F) := Classical.decEq _

/-- **The `ℤ`-unified window chart homeomorphism**: for every `n : ℤ`, the
adic spectrum of the `n`-th window chart ring is the `n`-th Big-window trace
(the `ℕ`- and negative-side chart homeomorphisms, aligned with the
`windowUnif`-uniformizer). -/
noncomputable def spaChartHomeoWindow (hp : 1 < p) : ∀ n : ℤ,
    ↥(Spa (windowChartRing p F ϖ n) (ringPlus (windowChartRing p F ϖ n)))
      ≃ₜ ↥(bigWindow p F ϖ n ∩ Spa (Ainf p F) (ringPlus (Ainf p F)))
  | .ofNat k => spaChartHomeoBigWindow p F ϖ k hp
  | .negSucc m => spaChartHomeoBigWindowNeg p F ϖ (m + 1) hp

/-- The Big-window trace is open in the `𝒴`-carrier (the `Spa`-side
membership is automatic on `yTop`, so the trace is a finite intersection of
basic-open traces). -/
theorem isOpen_yTop_windowTrace (n : ℤ) :
    IsOpen {z : ↥(yTop p F ϖ) |
      ((ySpaPoint p F ϖ z : ↥(Spa (Ainf p F) (ringPlus (Ainf p F))))
        : Spv (Ainf p F)) ∈ bigWindow p F ϖ n} := by
  rw [show bigWindow p F ϖ n
      = rationalOpen (chartData p F (windowUnif p F ϖ n) 1 1 p 1).T
          (chartData p F (windowUnif p F ϖ n) 1 1 p 1).s from
    bigWindow_eq_rationalOpen_windowUnif p F ϖ n]
  set T := (chartData p F (windowUnif p F ϖ n) 1 1 p 1).T with hT
  set s := (chartData p F (windowUnif p F ϖ n) 1 1 p 1).s with hs
  have hTne : T.Nonempty := by
    rw [hT]
    exact ⟨(p : Ainf p F) ^ (p + 1),
      Finset.mem_insert_self _ {teichPi p F (windowUnif p F ϖ n) ^ (1 + 1)}⟩
  have hset : {z : ↥(yTop p F ϖ) |
      ((ySpaPoint p F ϖ z : ↥(Spa (Ainf p F) (ringPlus (Ainf p F))))
        : Spv (Ainf p F)) ∈ rationalOpen T s}
      = {z : ↥(yTop p F ϖ) |
          ((ySpaPoint p F ϖ z : ↥(Spa (Ainf p F) (ringPlus (Ainf p F))))
            : Spv (Ainf p F)) ∈ ⋂ t ∈ (T : Set (Ainf p F)), basicOpen t s} := by
    ext z
    constructor
    · rintro ⟨-, hT', hs'⟩
      exact Set.mem_iInter₂.mpr fun t ht => ⟨hT' t ht, hs'⟩
    · intro hz
      have hzSpa : ((ySpaPoint p F ϖ z
          : ↥(Spa (Ainf p F) (ringPlus (Ainf p F)))) : Spv (Ainf p F))
          ∈ Spa (Ainf p F) (ringPlus (Ainf p F)) :=
        (ySpaPoint p F ϖ z).2
      obtain ⟨t₀, ht₀⟩ := hTne
      have h₀ := Set.mem_iInter₂.mp hz
      exact ⟨hzSpa, fun t ht => (h₀ t ht).1, (h₀ t₀ ht₀).2⟩
  rw [hset]
  have hcont : Continuous (fun z : ↥(yTop p F ϖ) =>
      ((ySpaPoint p F ϖ z : ↥(Spa (Ainf p F) (ringPlus (Ainf p F))))
        : Spv (Ainf p F))) :=
    continuous_subtype_val.comp continuous_subtype_val
  refine IsOpen.preimage hcont ?_
  refine Set.Finite.isOpen_biInter (Finset.finite_toSet T) ?_
  intro t _
  exact isOpen_basicOpen t s


/-- Adding the denominator to the numerator set does not change a rational
subset (`v(s) ≤ v(s)` always). -/
theorem rationalOpen_insert_self {B : Type*} [CommRing B] [TopologicalSpace B]
    [PlusSubring B] [DecidableEq B] (T : Finset B) (s : B) :
    rationalOpen (insert s T) s = rationalOpen T s := by
  ext v
  constructor
  · rintro ⟨hv, hT, hs⟩
    exact ⟨hv, fun t ht => hT t (Finset.mem_insert_of_mem ht), hs⟩
  · rintro ⟨hv, hT, hs⟩
    refine ⟨hv, fun t ht => ?_, hs⟩
    rcases Finset.mem_insert.mp ht with rfl | ht'
    · exact ValuationSpectrum.vle_refl t
    · exact hT t ht'

/-- Membership in `Y` from membership in a Big window. -/
theorem mem_Y_of_mem_bigWindow (hp : 1 < p) {v : Spv (Ainf p F)} (n : ℤ)
    (hv : v ∈ bigWindow p F ϖ n) : v ∈ Y p F ϖ := by
  rw [Y_eq_iUnion_bigWindow p F ϖ hp]
  exact Set.mem_iUnion.mpr ⟨n, hv⟩

/-- **Basic opens form a basis of `Spv B`**, packaged the way callers need it: a point of
an open `Q` lies in a finite intersection of basic opens that is itself inside `Q`. The
family is returned as a `Finset` of sets together with a choice of numerator/denominator
pair realising each member — exactly the shape
`exists_spanning_presentation_of_mem_basicOpens` consumes. -/
private theorem exists_finset_basicOpen_mem_subset {B : Type*} [CommRing B]
    {Q : Set (Spv B)} (hQ : IsOpen Q) {w : Spv B} (hw : w ∈ Q) :
    ∃ (fam : Finset (Set (Spv B))) (FG : Set (Spv B) → B × B),
      (∀ e ∈ fam, w ∈ basicOpen (FG e).1 (FG e).2) ∧
      (⋂ e ∈ fam, basicOpen (FG e).1 (FG e).2) ⊆ Q := by
  classical
  have hbasis := TopologicalSpace.isTopologicalBasis_of_subbasis
    (t := (instTopologicalSpace : TopologicalSpace (Spv B)))
    (s := {U : Set (Spv B) | ∃ f s, U = basicOpen f s}) rfl
  obtain ⟨t, ht, hwt, htQ⟩ := hbasis.exists_subset_of_mem_open hw hQ
  obtain ⟨fam₀, ⟨hfam₀_fin, hfam₀_sub⟩, rfl⟩ := ht
  have hFG : ∀ e : Set (Spv B), ∃ q : B × B, e ∈ fam₀ → e = basicOpen q.1 q.2 := by
    intro e
    by_cases he : e ∈ fam₀
    · obtain ⟨f, s, hfs⟩ := hfam₀_sub he
      exact ⟨(f, s), fun _ => hfs⟩
    · exact ⟨(0, 0), fun h => absurd h he⟩
  choose FG hFGspec using hFG
  refine ⟨hfam₀_fin.toFinset, FG, fun e he => ?_, fun v hv => htQ fun e he₀ => ?_⟩
  · have he₀ : e ∈ fam₀ := hfam₀_fin.mem_toFinset.mp he
    rw [← hFGspec e he₀]
    exact hwt e he₀
  · rw [hFGspec e he₀]
    exact Set.mem_iInter₂.mp hv e (hfam₀_fin.mem_toFinset.mpr he₀)


/-- The underlying equivalence of `windowTraceHomeomorph`: the window chart
homeomorphism transported to the trace of `R` on `Spa B_n`, as a bijection.
Split out so each half stays readable; continuity is proved separately. -/
@[reducible] private def windowTraceEquiv (hp : 1 < p) (n : ℤ)
    (R : Set (Spv (windowChartRing p F ϖ n))) (G₂ : Set (Spv (Ainf p F)))
    (hG₂eq : Subtype.val ⁻¹' G₂ = ⇑(spaChartHomeoWindow p F ϖ hp n) ''
      (Subtype.val ⁻¹' R : Set ↥(Spa (windowChartRing p F ϖ n)
        (ringPlus (windowChartRing p F ϖ n))))) :
    ↥(R ∩ Spa (windowChartRing p F ϖ n) (windowChartRing p F ϖ n)⁺) ≃
      ↥({z : ↥(yTop p F ϖ) |
            ((ySpaPoint p F ϖ z : ↥(Spa (Ainf p F) (ringPlus (Ainf p F))))
              : Spv (Ainf p F)) ∈ G₂}
          ∩ {z : ↥(yTop p F ϖ) |
            ((ySpaPoint p F ϖ z : ↥(Spa (Ainf p F) (ringPlus (Ainf p F))))
              : Spv (Ainf p F)) ∈ bigWindow p F ϖ n}) := by
  set Bn := windowChartRing p F ϖ n with hBn
  set h_n := spaChartHomeoWindow p F ϖ hp n with hhn
  set RT : Set ↥(Spa Bn (ringPlus Bn)) := Subtype.val ⁻¹' R with hRT
  have hIM' : ⇑h_n '' RT = ⇑h_n.symm ⁻¹' RT := h_n.toEquiv.image_eq_preimage_symm RT
  refine Equiv.mk
    (fun r => ⟨⟨⟨((h_n ⟨(r : Spv Bn), r.2.2⟩
        : ↥(bigWindow p F ϖ n ∩ Spa (Ainf p F) (ringPlus (Ainf p F)))) : Spv (Ainf p F)),
        (h_n ⟨(r : Spv Bn), r.2.2⟩).2.2⟩,
        mem_Y_of_mem_bigWindow p F ϖ hp n (h_n ⟨(r : Spv Bn), r.2.2⟩).2.1⟩,
      (Set.ext_iff.mp hG₂eq (h_n ⟨(r : Spv Bn), r.2.2⟩)).mpr
        (Set.mem_image_of_mem _ (show (⟨(r : Spv Bn), r.2.2⟩
          : ↥(Spa Bn (ringPlus Bn))) ∈ RT from r.2.1)),
      (h_n ⟨(r : Spv Bn), r.2.2⟩).2.1⟩)
    (fun z => ⟨((h_n.symm ⟨((ySpaPoint p F ϖ z.1
        : ↥(Spa (Ainf p F) (ringPlus (Ainf p F)))) : Spv (Ainf p F)),
        z.2.2, (ySpaPoint p F ϖ z.1).2⟩
        : ↥(Spa Bn (ringPlus Bn))) : Spv Bn),
      (show h_n.symm ⟨_, z.2.2, (ySpaPoint p F ϖ z.1).2⟩ ∈ RT by
        have h1 : (⟨((ySpaPoint p F ϖ z.1
            : ↥(Spa (Ainf p F) (ringPlus (Ainf p F)))) : Spv (Ainf p F)),
            z.2.2, (ySpaPoint p F ϖ z.1).2⟩
            : ↥(bigWindow p F ϖ n ∩ Spa (Ainf p F) (ringPlus (Ainf p F)))) ∈ ⇑h_n '' RT :=
          (Set.ext_iff.mp hG₂eq _).mp z.2.1
        rw [hIM'] at h1
        exact h1),
      (h_n.symm ⟨_, z.2.2, (ySpaPoint p F ϖ z.1).2⟩).2⟩)
      (fun r => ?_) (fun z => ?_)
  · -- left inverse
    refine Subtype.ext ?_
    have key : ∀ (m : ↥(bigWindow p F ϖ n ∩ Spa (Ainf p F) (ringPlus (Ainf p F)))),
        m = h_n ⟨(r : Spv Bn), r.2.2⟩ →
        ((h_n.symm m : ↥(Spa Bn (ringPlus Bn))) : Spv Bn) = (r : Spv Bn) := by
      intro m hm
      rw [hm, h_n.symm_apply_apply]
    exact key _ (Subtype.ext rfl)
  · -- right inverse
    refine Subtype.ext (Subtype.ext (Subtype.ext ?_))
    set mz : ↥(bigWindow p F ϖ n ∩ Spa (Ainf p F) (ringPlus (Ainf p F))) :=
      ⟨((ySpaPoint p F ϖ z.1 : ↥(Spa (Ainf p F) (ringPlus (Ainf p F)))) : Spv (Ainf p F)),
        z.2.2, (ySpaPoint p F ϖ z.1).2⟩ with hmzdef
    have h1 : (⟨((h_n.symm mz : ↥(Spa Bn (ringPlus Bn))) : Spv Bn),
        (h_n.symm mz).2⟩ : ↥(Spa Bn (ringPlus Bn))) = h_n.symm mz := Subtype.ext rfl
    exact (congrArg (fun w : ↥(Spa Bn (ringPlus Bn)) =>
        ((h_n w : ↥(bigWindow p F ϖ n
          ∩ Spa (Ainf p F) (ringPlus (Ainf p F)))) : Spv (Ainf p F))) h1).trans
      (congrArg (fun m : ↥(bigWindow p F ϖ n
          ∩ Spa (Ainf p F) (ringPlus (Ainf p F))) => (m : Spv (Ainf p F)))
        (h_n.apply_symm_apply mz))

/-- **The window-trace homeomorphism** — the second leg of the chart comparison. The
chart homeomorphism `h_n = spaChartHomeoWindow` carries the rational open `R` on
`Spa B_n` across to the neighbourhood that `G₂` cuts out on the `𝒴`-carrier; `hG₂eq`
says exactly that `G₂` lifts the `h_n`-image of `R`'s trace. Both sides are subtypes of
nested subtypes, so all four components are written out, but the content is only that
`h_n` and `h_n.symm` are mutually inverse and continuous. -/
private def windowTraceHomeomorph (hp : 1 < p) (n : ℤ)
    (R : Set (Spv (windowChartRing p F ϖ n))) (G₂ : Set (Spv (Ainf p F)))
    (hG₂eq : Subtype.val ⁻¹' G₂ = ⇑(spaChartHomeoWindow p F ϖ hp n) ''
      (Subtype.val ⁻¹' R : Set ↥(Spa (windowChartRing p F ϖ n)
        (ringPlus (windowChartRing p F ϖ n))))) :
    ↥(R ∩ Spa (windowChartRing p F ϖ n) (windowChartRing p F ϖ n)⁺) ≃ₜ
      ↥({z : ↥(yTop p F ϖ) |
            ((ySpaPoint p F ϖ z : ↥(Spa (Ainf p F) (ringPlus (Ainf p F))))
              : Spv (Ainf p F)) ∈ G₂}
          ∩ {z : ↥(yTop p F ϖ) |
            ((ySpaPoint p F ϖ z : ↥(Spa (Ainf p F) (ringPlus (Ainf p F))))
              : Spv (Ainf p F)) ∈ bigWindow p F ϖ n}) := by
  set h_n := spaChartHomeoWindow p F ϖ hp n with hhn
  refine Homeomorph.mk (windowTraceEquiv p F ϖ hp n R G₂ hG₂eq) ?_ ?_
  · -- continuity, forward
    refine Continuous.subtype_mk (Continuous.subtype_mk (Continuous.subtype_mk ?_ _) _) _
    exact continuous_subtype_val.comp (h_n.continuous.comp
      (Continuous.subtype_mk continuous_subtype_val _))
  · -- continuity, backward
    refine Continuous.subtype_mk ?_ _
    refine continuous_subtype_val.comp (h_n.symm.continuous.comp ?_)
    refine Continuous.subtype_mk ?_ _
    exact continuous_subtype_val.comp (continuous_subtype_val.comp continuous_subtype_val)

/-- **Rational opens over a window chart are a neighbourhood basis of `Spa B_n`.** Given
a point `w₀` and an open `Q ⊆ Spv B_n` containing it, there is a rational localisation
datum `D'` over the window chart whose rational open contains `w₀` and lies inside `Q`.

The datum is assembled from a finite family of basic opens around `w₀`
(`exists_finset_basicOpen_mem_subset`), which
`exists_spanning_presentation_of_mem_basicOpens` converts into a single spanning
presentation; `genPieceDatum` then turns that presentation into the datum. -/
private theorem exists_rationalLocData_mem_subset (n : ℤ)
    {Q : Set (Spv (windowChartRing p F ϖ n))} (hQ : IsOpen Q)
    (w₀ : ↥(Spa (windowChartRing p F ϖ n) (ringPlus (windowChartRing p F ϖ n))))
    (hw₀Q : (w₀ : Spv (windowChartRing p F ϖ n)) ∈ Q) :
    ∃ D' : RationalLocData (windowChartRing p F ϖ n),
      (w₀ : Spv (windowChartRing p F ϖ n)) ∈ rationalOpen D'.T D'.s ∧
      ∀ v : Spv (windowChartRing p F ϖ n), v ∈ rationalOpen D'.T D'.s → v ∈ Q := by
  classical
  set Bn := windowChartRing p F ϖ n with hBn
  haveI : IsTateRing Bn := isTateRing_bigWindowChart p F (windowUnif p F ϖ n)
  obtain ⟨fam, FG, hmem, hfamQ⟩ := exists_finset_basicOpen_mem_subset hQ hw₀Q
  obtain ⟨uB, huB⟩ := IsTateRing.exists_topologicallyNilpotent_unit (A := Bn)
  obtain ⟨f, g, hspan, hwmem, hsub⟩ :=
    exists_spanning_presentation_of_mem_basicOpens (B := Bn)
      (ϖ := (uB : Bn)) uB.isUnit huB w₀.2
      (fam := fam) (F := fun e => (FG e).1) (G := fun e => (FG e).2) hmem
  set T' : Finset Bn := insert g ((insert none (fam.image some)).image f) with hT'
  set D' : RationalLocData Bn := genPieceDatum
    (presheafValue_concretePair (chartData p F (windowUnif p F ϖ n) 1 1 p 1))
    T' g hspan with hD'
  -- the datum's rational set agrees with the indexed one, so both claims transfer
  have hReq : rationalOpen D'.T D'.s ∩ Spa Bn Bn⁺
      = indexedRationalSet Bn (insert none (fam.image some)) f g := by
    rw [indexedRationalSet_eq_rationalOpen]
    rw [show D'.T = T' from rfl, show D'.s = g from rfl, hT',
      rationalOpen_insert_self]
  have hw₀R : (w₀ : Spv Bn) ∈ rationalOpen D'.T D'.s := by
    have h1 : (w₀ : Spv Bn) ∈ rationalOpen D'.T D'.s ∩ Spa Bn Bn⁺ := by
      rw [hReq]
      exact hwmem
    exact h1.1
  exact ⟨D', hw₀R, fun v hv =>
    hfamQ (hsub (by rw [← hReq]; exact ⟨hv, rationalOpen_subset_spa hv⟩))⟩

/-- **The chart-side trace of a neighbourhood.** An open `O₂ ⊆ Spv A_inf` pulls back
along the window chart homeomorphism to an open of `Spv B_n`, characterised pointwise on
`Spa B_n`. This is the only thing callers need from the pullback — the intermediate
subtype-level opens never escape. -/
private theorem exists_isOpen_chart_trace (hp : 1 < p) (n : ℤ)
    {O₂ : Set (Spv (Ainf p F))} (hO₂ : IsOpen O₂) :
    ∃ Q : Set (Spv (windowChartRing p F ϖ n)), IsOpen Q ∧
      ∀ r : ↥(Spa (windowChartRing p F ϖ n) (ringPlus (windowChartRing p F ϖ n))),
        (r : Spv (windowChartRing p F ϖ n)) ∈ Q ↔
          ((spaChartHomeoWindow p F ϖ hp n r : ↥(bigWindow p F ϖ n
            ∩ Spa (Ainf p F) (ringPlus (Ainf p F)))) : Spv (Ainf p F)) ∈ O₂ := by
  have hPMopen : IsOpen {m : ↥(bigWindow p F ϖ n
      ∩ Spa (Ainf p F) (ringPlus (Ainf p F))) | (m : Spv (Ainf p F)) ∈ O₂} :=
    IsOpen.preimage continuous_subtype_val hO₂
  have hPopen : IsOpen (spaChartHomeoWindow p F ϖ hp n ⁻¹'
      {m | (m : Spv (Ainf p F)) ∈ O₂}) :=
    IsOpen.preimage (spaChartHomeoWindow p F ϖ hp n).continuous hPMopen
  obtain ⟨Q, hQ, hQeq⟩ := isOpen_induced_iff.mp hPopen
  exact ⟨Q, hQ, fun r => Set.ext_iff.mp hQeq r⟩

/-- **The window neighbourhood cut out by a chart-side open.** For `G₂ ⊆ Spv A_inf` open,
this is the set of carrier points whose underlying valuation lies in `G₂` *and* in the
`n`-th big window. Intersecting with the window is what makes the chart homeomorphism
applicable; `G₂` alone would not be contained in a single chart. -/
private def windowNbhd (n : ℤ) {G₂ : Set (Spv (Ainf p F))} (hG₂ : IsOpen G₂) :
    Opens ↥(yTop p F ϖ) :=
  ⟨{z : ↥(yTop p F ϖ) |
      ((ySpaPoint p F ϖ z : ↥(Spa (Ainf p F) (ringPlus (Ainf p F))))
        : Spv (Ainf p F)) ∈ G₂}
    ∩ {z : ↥(yTop p F ϖ) |
      ((ySpaPoint p F ϖ z : ↥(Spa (Ainf p F) (ringPlus (Ainf p F))))
        : Spv (Ainf p F)) ∈ bigWindow p F ϖ n},
   IsOpen.inter
     (IsOpen.preimage (continuous_subtype_val.comp continuous_subtype_val) hG₂)
     (isOpen_yTop_windowTrace p F ϖ n)⟩

/-- **The window neighbourhood sits inside `O`.** A carrier point of the neighbourhood has
its valuation in `G₂`, hence in the `h_n`-image of the rational trace; that preimage point
lies in `R`, which is contained in the chart-side trace `Q` of `O`. -/
private theorem windowNbhd_le (hp : 1 < p) (n : ℤ)
    {R : Set (Spv (windowChartRing p F ϖ n))} {G₂ : Set (Spv (Ainf p F))} (hG₂ : IsOpen G₂)
    (hGrel : Subtype.val ⁻¹' G₂ = ⇑(spaChartHomeoWindow p F ϖ hp n) ''
      (Subtype.val ⁻¹' R : Set ↥(Spa (windowChartRing p F ϖ n)
        (ringPlus (windowChartRing p F ϖ n)))))
    (O : Opens ↥(yTop p F ϖ)) {O₂ : Set (Spv (Ainf p F))}
    (hOmem : ∀ z : ↥(yTop p F ϖ), z ∈ O ↔
      ((ySpaPoint p F ϖ z : ↥(Spa (Ainf p F) (ringPlus (Ainf p F))))
        : Spv (Ainf p F)) ∈ O₂)
    {Q : Set (Spv (windowChartRing p F ϖ n))}
    (hQmem : ∀ r : ↥(Spa (windowChartRing p F ϖ n)
        (ringPlus (windowChartRing p F ϖ n))),
      (r : Spv (windowChartRing p F ϖ n)) ∈ Q ↔
        ((spaChartHomeoWindow p F ϖ hp n r : ↥(bigWindow p F ϖ n
          ∩ Spa (Ainf p F) (ringPlus (Ainf p F)))) : Spv (Ainf p F)) ∈ O₂)
    (hRsub : ∀ v : Spv (windowChartRing p F ϖ n), v ∈ R → v ∈ Q) :
    windowNbhd p F ϖ n hG₂ ≤ O := by
  intro z hz
  obtain ⟨hzG₂, hzbw⟩ := hz
  obtain ⟨r, hrRT, hrmz⟩ := (Set.ext_iff.mp hGrel
    (⟨((ySpaPoint p F ϖ z : ↥(Spa (Ainf p F) (ringPlus (Ainf p F))))
      : Spv (Ainf p F)), hzbw, (ySpaPoint p F ϖ z).2⟩ :
      ↥(bigWindow p F ϖ n ∩ Spa (Ainf p F) (ringPlus (Ainf p F))))).mp hzG₂
  refine (hOmem z).mpr ?_
  have h2 : ((spaChartHomeoWindow p F ϖ hp n r : ↥(bigWindow p F ϖ n
      ∩ Spa (Ainf p F) (ringPlus (Ainf p F)))) : Spv (Ainf p F)) ∈ O₂ :=
    (hQmem r).mp (hRsub _ hrRT)
  rwa [hrmz] at h2

/-- **The rational trace cuts out a good neighbourhood.** Given a rational datum `D'` over
the window chart whose rational open contains the chart-image of `y` and lies inside the
chart-side trace `Q` of `O`, the image of that rational open on the `𝒴`-carrier is an open
neighbourhood of `y` inside `O`, homeomorphic to `Spa` of the datum.

The homeomorphism is two legs: `spaPresheafValueHomeomorphRationalOpen'` identifies
`Spa(𝒪(D'))` with the rational open, and `windowTraceHomeomorph` carries that across the
window chart. -/
private theorem exists_windowNbhd_spec (hp : 1 < p) (n : ℤ) (y : ↥(yTop p F ϖ))
    (hbw : ((ySpaPoint p F ϖ y : ↥(Spa (Ainf p F) (ringPlus (Ainf p F))))
      : Spv (Ainf p F)) ∈ bigWindow p F ϖ n)
    (O : Opens ↥(yTop p F ϖ)) {O₂ : Set (Spv (Ainf p F))}
    (hOmem : ∀ z : ↥(yTop p F ϖ), z ∈ O ↔
      ((ySpaPoint p F ϖ z : ↥(Spa (Ainf p F) (ringPlus (Ainf p F))))
        : Spv (Ainf p F)) ∈ O₂)
    {Q : Set (Spv (windowChartRing p F ϖ n))}
    (hQmem : ∀ r : ↥(Spa (windowChartRing p F ϖ n)
        (ringPlus (windowChartRing p F ϖ n))),
      (r : Spv (windowChartRing p F ϖ n)) ∈ Q ↔
        ((spaChartHomeoWindow p F ϖ hp n r : ↥(bigWindow p F ϖ n
          ∩ Spa (Ainf p F) (ringPlus (Ainf p F)))) : Spv (Ainf p F)) ∈ O₂)
    (D' : RationalLocData (windowChartRing p F ϖ n))
    (hw₀R : (((spaChartHomeoWindow p F ϖ hp n).symm
        ⟨((ySpaPoint p F ϖ y : ↥(Spa (Ainf p F) (ringPlus (Ainf p F))))
          : Spv (Ainf p F)), hbw, (ySpaPoint p F ϖ y).2⟩
        : ↥(Spa (windowChartRing p F ϖ n) (ringPlus (windowChartRing p F ϖ n))))
      : Spv (windowChartRing p F ϖ n)) ∈ rationalOpen D'.T D'.s)
    (hRsub : ∀ v : Spv (windowChartRing p F ϖ n),
      v ∈ rationalOpen D'.T D'.s → v ∈ Q) :
    ∃ V : Opens ↥(yTop p F ϖ), y ∈ V ∧ V ≤ O ∧
      Nonempty (↥(Spa (presheafValue D') (ringPlus (presheafValue D')))
        ≃ₜ ↥((V : Set ↥(yTop p F ϖ)))) := by
  classical
  set Bn := windowChartRing p F ϖ n with hBn
  haveI : IsTateRing Bn := isTateRing_bigWindowChart p F (windowUnif p F ϖ n)
  haveI : IsRingOfIntegralElements ((Ainf p F)⁺ : Subring (Ainf p F)) :=
    isAffinoidRing_Ainf p F
  set h_n := spaChartHomeoWindow p F ϖ hp n with hhn
  set m₀ : ↥(bigWindow p F ϖ n ∩ Spa (Ainf p F) (ringPlus (Ainf p F))) :=
    ⟨((ySpaPoint p F ϖ y : ↥(Spa (Ainf p F) (ringPlus (Ainf p F))))
        : Spv (Ainf p F)), hbw, (ySpaPoint p F ϖ y).2⟩ with hm₀
  set w₀ := h_n.symm m₀ with hw₀
  -- the window-side image of the rational trace
  set RT : Set ↥(Spa Bn (ringPlus Bn)) :=
    Subtype.val ⁻¹' rationalOpen D'.T D'.s with hRT
  have hRTopen : IsOpen RT := (rationalOpens D'.T D'.s).2
  set IM : Set ↥(bigWindow p F ϖ n
      ∩ Spa (Ainf p F) (ringPlus (Ainf p F))) := h_n '' RT with hIM
  have hIMopen : IsOpen IM := h_n.isOpenMap RT hRTopen
  obtain ⟨G₂, hG₂, hG₂eq⟩ := isOpen_induced_iff.mp hIMopen
  -- the neighbourhood on the 𝒴-carrier
  refine ⟨windowNbhd p F ϖ n hG₂, ?_, ?_, ?_⟩
  · -- y ∈ V
    have hm₀IM : m₀ ∈ IM := by
      have h1 : m₀ = h_n w₀ := (h_n.apply_symm_apply m₀).symm
      rw [h1, hIM]
      exact Set.mem_image_of_mem _ hw₀R
    have hm₀G₂ : (m₀ : Spv (Ainf p F)) ∈ G₂ :=
      (Set.ext_iff.mp hG₂eq m₀).mpr hm₀IM
    exact ⟨hm₀G₂, hbw⟩
  · -- V ≤ O
    exact windowNbhd_le p F ϖ hp n hG₂ (by rw [hG₂eq, hIM, hRT]) O hOmem hQmem hRsub
  · -- the homeomorphism
    haveI : IsHuberRing Bn :=
      (isTateRing_bigWindowChart p F (windowUnif p F ϖ n)).toIsHuberRing
    haveI : IsTateRing (presheafValue D') := presheafValue_isTateRing_concrete D'
    set e₁ := spaPresheafValueHomeomorphRationalOpen' D'
      (IsTateRing.exists_topologicallyNilpotent_unit
        (A := presheafValue D')).choose
      (IsTateRing.exists_topologicallyNilpotent_unit
        (A := presheafValue D')).choose_spec with he₁
    -- the second leg: the rational trace is carried onto `V`
    refine ⟨e₁.trans (windowTraceHomeomorph p F ϖ hp n (rationalOpen D'.T D'.s) G₂
      (by rw [hG₂eq, hIM, hRT]))⟩

/-- **Opens of the `𝒴`-carrier come from opens of `Spv A_inf`.** The carrier sits inside
`Spa(A_inf, A_inf⁺)` which sits inside `Spv A_inf`, so an open of the carrier is cut out
by an open of `Spv A_inf` — this peels both induced topologies in one step, which is what
callers actually need (the intermediate `Spa`-level open is never used). -/
private theorem exists_isOpen_mem_yTop_iff (O : Opens ↥(yTop p F ϖ)) :
    ∃ O₂ : Set (Spv (Ainf p F)), IsOpen O₂ ∧ ∀ z : ↥(yTop p F ϖ), z ∈ O ↔
      ((ySpaPoint p F ϖ z : ↥(Spa (Ainf p F) (ringPlus (Ainf p F))))
        : Spv (Ainf p F)) ∈ O₂ := by
  obtain ⟨O₁, hO₁, hO₁eq⟩ := isOpen_induced_iff.mp O.2
  obtain ⟨O₂, hO₂, hO₂eq⟩ := isOpen_induced_iff.mp hO₁
  refine ⟨O₂, hO₂, fun z => ⟨fun hz => ?_, fun hz => ?_⟩⟩
  · exact (Set.ext_iff.mp hO₂eq (ySpaPoint p F ϖ z)).mpr ((Set.ext_iff.mp hO₁eq z).mpr hz)
  · exact (Set.ext_iff.mp hO₁eq z).mp ((Set.ext_iff.mp hO₂eq (ySpaPoint p F ϖ z)).mp hz)


/-- **The rational-neighbourhood selection** (X-ADIC-1 A2): every open
neighbourhood of a point of the `𝒴`-carrier contains an open neighbourhood
homeomorphic to the adic spectrum of a rational-subdatum value ring over a
window chart. -/
theorem exists_window_subdatum_nbhd (hp : 1 < p) (y : ↥(yTop p F ϖ))
    (O : Opens ↥(yTop p F ϖ)) (hyO : y ∈ O) :
    ∃ (n : ℤ) (D' : RationalLocData (windowChartRing p F ϖ n))
      (V : Opens ↥(yTop p F ϖ)), y ∈ V ∧ V ≤ O ∧
      Nonempty (↥(Spa (presheafValue D') (ringPlus (presheafValue D')))
        ≃ₜ ↥((V : Set ↥(yTop p F ϖ)))) := by
  classical
  -- the window containing the point
  have hyY : ((ySpaPoint p F ϖ y : ↥(Spa (Ainf p F) (ringPlus (Ainf p F))))
      : Spv (Ainf p F)) ∈ Y p F ϖ := ySpaPoint_mem_Y p F ϖ y
  rw [Y_eq_iUnion_bigWindow p F ϖ hp] at hyY
  obtain ⟨n, hbw⟩ := Set.mem_iUnion.mp hyY
  refine ⟨n, ?_⟩
  set Bn := windowChartRing p F ϖ n with hBn
  haveI : IsTateRing Bn := isTateRing_bigWindowChart p F (windowUnif p F ϖ n)
  haveI : IsRingOfIntegralElements ((Ainf p F)⁺ : Subring (Ainf p F)) :=
    isAffinoidRing_Ainf p F
  set h_n := spaChartHomeoWindow p F ϖ hp n with hhn
  -- the M_n-point and the chart-side point
  set m₀ : ↥(bigWindow p F ϖ n ∩ Spa (Ainf p F) (ringPlus (Ainf p F))) :=
    ⟨((ySpaPoint p F ϖ y : ↥(Spa (Ainf p F) (ringPlus (Ainf p F))))
        : Spv (Ainf p F)), hbw, (ySpaPoint p F ϖ y).2⟩ with hm₀
  set w₀ := h_n.symm m₀ with hw₀
  -- lift `O` to an `Spv`-open through both induced topologies
  obtain ⟨O₂, hO₂, hOmem⟩ := exists_isOpen_mem_yTop_iff p F ϖ O
  -- pull `O₂` back to an open of `Spv B_n`, and locate `w₀` in it
  obtain ⟨Q, hQ, hQmem⟩ := exists_isOpen_chart_trace p F ϖ hp n hO₂
  have hw₀Q : (w₀ : Spv Bn) ∈ Q := (hQmem w₀).mpr (by
    rw [hw₀, h_n.apply_symm_apply]
    exact (hOmem y).mp hyO)
  -- a rational datum over the window chart, cutting out a neighbourhood inside `Q`
  obtain ⟨D', hw₀R, hRsub⟩ := exists_rationalLocData_mem_subset p F ϖ n hQ w₀ hw₀Q
  refine ⟨D', ?_⟩
  exact exists_windowNbhd_spec p F ϖ hp n y hbw O hOmem hQmem D' hw₀R hRsub


/-- **THE ADIC FARGUES–FONTAINE CURVE IS LOCALLY AFFINOID** (X-ADIC-1, the
capstone): the curve, as a topological space, is an `AdicSpacePresentation` —
every point has an open neighbourhood homeomorphic to the adic spectrum of an
affinoid adic presentation (a sheafy complete strongly noetherian Tate ring:
a rational localization of a window chart ring). -/
noncomputable def curveAdicSpacePresentation :
    ValuationSpectrum.AdicSpacePresentation where
  carrier := Curve p F ϖ
  isLocallyAffinoid := by
    intro x
    have hp : 1 < p := one_lt_p p
    -- the fiber point and a wandering neighbourhood
    set y := fiberPoint p F ϖ x with hy
    obtain ⟨W₀, hyW₀, hdis₀⟩ := exists_disjoint_translates p F ϖ y
    -- the rational-subdatum neighbourhood inside it
    obtain ⟨n, D', V, hyV, hVW₀, ⟨e⟩⟩ :=
      exists_window_subdatum_nbhd p F ϖ hp y W₀ hyW₀
    -- V inherits the disjoint-translate property
    have hdisV : ∀ k : ℤ, k ≠ 0 →
        Disjoint (((Opens.map (yFrobTop p F ϖ k)).obj V
            : Opens ↥(yTop p F ϖ)) : Set ↥(yTop p F ϖ))
          ((V : Opens ↥(yTop p F ϖ)) : Set ↥(yTop p F ϖ)) := by
      intro k hk
      refine (hdis₀ k hk).mono ?_ ?_
      · intro z hz
        exact hVW₀ (hz : z ∈ (Opens.map (yFrobTop p F ϖ k)).obj V)
      · exact fun z hz => hVW₀ hz
    -- the open image neighbourhood on the curve
    refine ⟨xImage p F ϖ V, ⟨y, hyV, yTopToCurve_fiberPoint p F ϖ x⟩,
      windowSubAffinoid p F ϖ n D', ?_⟩
    -- the homeomorphism chain
    exact ⟨(xImageHomeo p F ϖ hdisV).symm.trans e.symm⟩


/-- **𝒴 is locally affinoid** (ID3d, the `Y`-level carrier presentation):
every point of the punctured-spectrum space `𝒴` has an open neighbourhood
homeomorphic to the adic spectrum of a sheafy strongly noetherian complete
Tate ring — a rational localization of a big-window chart ring. -/
noncomputable def yAdicSpacePresentation :
    ValuationSpectrum.AdicSpacePresentation where
  carrier := ↥(yTop p F ϖ)
  isLocallyAffinoid := by
    intro y
    obtain ⟨n, D', V, hyV, _, ⟨e⟩⟩ :=
      exists_window_subdatum_nbhd p F ϖ (one_lt_p p) y ⊤ trivial
    exact ⟨V, hyV, windowSubAffinoid p F ϖ n D', ⟨e.symm⟩⟩

end FarguesFontaine

end
