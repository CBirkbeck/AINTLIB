import «Adic spaces».FarguesFontaine.CurveObject
import «Adic spaces».StronglyNoetherianTransport
import «Adic spaces».WedhornCechAcyclicity
import «Adic spaces».StructurePresheafBundled

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

end FarguesFontaine

end
