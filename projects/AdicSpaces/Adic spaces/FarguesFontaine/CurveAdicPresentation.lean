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
  -- lift `O` to an Spv-open through the double subtype
  obtain ⟨O₁, hO₁, hO₁eq⟩ := isOpen_induced_iff.mp O.2
  obtain ⟨O₂, hO₂, hO₂eq⟩ := isOpen_induced_iff.mp hO₁
  have hOmem : ∀ z : ↥(yTop p F ϖ), z ∈ O ↔
      ((ySpaPoint p F ϖ z : ↥(Spa (Ainf p F) (ringPlus (Ainf p F))))
        : Spv (Ainf p F)) ∈ O₂ := by
    intro z
    constructor
    · intro hz
      have h1 : z ∈ Subtype.val ⁻¹' O₁ :=
        (Set.ext_iff.mp hO₁eq z).mpr hz
      have h2 : ySpaPoint p F ϖ z ∈ Subtype.val ⁻¹' O₂ :=
        (Set.ext_iff.mp hO₂eq (ySpaPoint p F ϖ z)).mpr h1
      exact h2
    · intro hz
      have h1 : ySpaPoint p F ϖ z ∈ O₁ :=
        (Set.ext_iff.mp hO₂eq (ySpaPoint p F ϖ z)).mp hz
      exact (Set.ext_iff.mp hO₁eq z).mp h1
  -- the chart-side open around `w₀`
  have hPMopen : IsOpen {m : ↥(bigWindow p F ϖ n
      ∩ Spa (Ainf p F) (ringPlus (Ainf p F))) | (m : Spv (Ainf p F)) ∈ O₂} :=
    IsOpen.preimage continuous_subtype_val hO₂
  have hPopen : IsOpen (h_n ⁻¹' {m | (m : Spv (Ainf p F)) ∈ O₂}) :=
    IsOpen.preimage h_n.continuous hPMopen
  have hw₀P : w₀ ∈ h_n ⁻¹' {m | (m : Spv (Ainf p F)) ∈ O₂} := by
    show (h_n w₀ : Spv (Ainf p F)) ∈ O₂
    rw [hw₀, h_n.apply_symm_apply]
    exact (hOmem y).mp hyO
  -- lift to an Spv(B_n)-open
  obtain ⟨Q, hQ, hQeq⟩ := isOpen_induced_iff.mp hPopen
  have hw₀Q : (w₀ : Spv Bn) ∈ Q :=
    (Set.ext_iff.mp hQeq w₀).mpr hw₀P
  -- the basic-open basis of Spv(B_n)
  have hbasis := TopologicalSpace.isTopologicalBasis_of_subbasis
    (t := (instTopologicalSpace : TopologicalSpace (Spv Bn)))
    (s := {U : Set (Spv Bn) | ∃ f s, U = basicOpen f s}) rfl
  obtain ⟨t, ht, hwt, htQ⟩ := hbasis.exists_subset_of_mem_open hw₀Q hQ
  obtain ⟨fam₀, ⟨hfam₀_fin, hfam₀_sub⟩, rfl⟩ := ht
  have hFG : ∀ e : Set (Spv Bn), ∃ q : Bn × Bn, e ∈ fam₀ →
      e = basicOpen q.1 q.2 := by
    intro e
    by_cases he : e ∈ fam₀
    · obtain ⟨f, s, hfs⟩ := hfam₀_sub he
      exact ⟨(f, s), fun _ => hfs⟩
    · exact ⟨(0, 0), fun h => absurd h he⟩
  choose FG hFGspec using hFG
  set fam : Finset (Set (Spv Bn)) := hfam₀_fin.toFinset with hfam
  have hmem : ∀ e ∈ fam, (w₀ : Spv Bn) ∈ basicOpen (FG e).1 (FG e).2 := by
    intro e he
    have he₀ : e ∈ fam₀ := by
      rwa [hfam, Set.Finite.mem_toFinset] at he
    rw [← hFGspec e he₀]
    exact hwt e he₀
  -- the spanning presentation
  obtain ⟨uB, huB⟩ := IsTateRing.exists_topologicallyNilpotent_unit (A := Bn)
  obtain ⟨f, g, hspan, hwmem, hsub⟩ :=
    exists_spanning_presentation_of_mem_basicOpens (B := Bn)
      (ϖ := (uB : Bn)) uB.isUnit huB w₀.2
      (fam := fam) (F := fun e => (FG e).1) (G := fun e => (FG e).2) hmem
  -- the rational datum over the window chart
  set T' : Finset Bn := insert g ((insert none (fam.image some)).image f)
    with hT'
  set D' : RationalLocData Bn := genPieceDatum
    (presheafValue_concretePair (chartData p F (windowUnif p F ϖ n) 1 1 p 1))
    T' g hspan with hD'
  refine ⟨D', ?_⟩
  -- the rational set agrees with the indexed one
  have hReq : rationalOpen D'.T D'.s ∩ Spa Bn Bn⁺
      = indexedRationalSet Bn (insert none (fam.image some)) f g := by
    rw [indexedRationalSet_eq_rationalOpen]
    rw [show D'.T = T' from rfl, show D'.s = g from rfl, hT',
      rationalOpen_insert_self]
  -- membership of the base point in the rational set
  have hw₀R : (w₀ : Spv Bn) ∈ rationalOpen D'.T D'.s := by
    have h1 : (w₀ : Spv Bn) ∈ rationalOpen D'.T D'.s ∩ Spa Bn Bn⁺ := by
      rw [hReq]
      exact hwmem
    exact h1.1
  -- the rational set is contained in the O₂-side
  have hRsub : ∀ v : Spv Bn, v ∈ rationalOpen D'.T D'.s → v ∈ Q := by
    intro v hv
    have h1 : v ∈ indexedRationalSet Bn (insert none (fam.image some)) f g := by
      rw [← hReq]
      exact ⟨hv, rationalOpen_subset_spa hv⟩
    have h2 := hsub h1
    refine htQ ?_
    intro e he₀
    have he : e ∈ fam := by
      rw [hfam, Set.Finite.mem_toFinset]
      exact he₀
    rw [hFGspec e he₀]
    exact Set.mem_iInter₂.mp h2 e he
  -- the window-side image of the rational trace
  set RT : Set ↥(Spa Bn (ringPlus Bn)) :=
    Subtype.val ⁻¹' rationalOpen D'.T D'.s with hRT
  have hRTopen : IsOpen RT := (rationalOpens D'.T D'.s).2
  set IM : Set ↥(bigWindow p F ϖ n
      ∩ Spa (Ainf p F) (ringPlus (Ainf p F))) := h_n '' RT with hIM
  have hIMopen : IsOpen IM := h_n.isOpenMap RT hRTopen
  obtain ⟨G₂, hG₂, hG₂eq⟩ := isOpen_induced_iff.mp hIMopen
  -- the neighbourhood on the 𝒴-carrier
  refine ⟨⟨{z : ↥(yTop p F ϖ) |
      ((ySpaPoint p F ϖ z : ↥(Spa (Ainf p F) (ringPlus (Ainf p F))))
        : Spv (Ainf p F)) ∈ G₂}
      ∩ {z : ↥(yTop p F ϖ) |
        ((ySpaPoint p F ϖ z : ↥(Spa (Ainf p F) (ringPlus (Ainf p F))))
          : Spv (Ainf p F)) ∈ bigWindow p F ϖ n},
    IsOpen.inter
      (IsOpen.preimage
        (continuous_subtype_val.comp continuous_subtype_val) hG₂)
      (isOpen_yTop_windowTrace p F ϖ n)⟩, ?_, ?_, ?_⟩
  · -- y ∈ V
    have hm₀IM : m₀ ∈ IM := by
      have h1 : m₀ = h_n w₀ := (h_n.apply_symm_apply m₀).symm
      rw [h1, hIM]
      exact Set.mem_image_of_mem _ hw₀R
    have hm₀G₂ : (m₀ : Spv (Ainf p F)) ∈ G₂ :=
      (Set.ext_iff.mp hG₂eq m₀).mpr hm₀IM
    exact ⟨hm₀G₂, hbw⟩
  · -- V ≤ O
    intro z hz
    obtain ⟨hzG₂, hzbw⟩ := hz
    set mz : ↥(bigWindow p F ϖ n
        ∩ Spa (Ainf p F) (ringPlus (Ainf p F))) :=
      ⟨((ySpaPoint p F ϖ z : ↥(Spa (Ainf p F) (ringPlus (Ainf p F))))
        : Spv (Ainf p F)), hzbw, (ySpaPoint p F ϖ z).2⟩ with hmz
    have hmzIM : mz ∈ IM := (Set.ext_iff.mp hG₂eq mz).mp hzG₂
    have hmzO₂ : (mz : Spv (Ainf p F)) ∈ O₂ := by
      rw [hIM] at hmzIM
      obtain ⟨r, hrRT, hrmz⟩ := hmzIM
      have hrP : r ∈ h_n ⁻¹' {m | (m : Spv (Ainf p F)) ∈ O₂} :=
        (Set.ext_iff.mp hQeq r).mp (hRsub _ hrRT)
      have h2 : (h_n r : Spv (Ainf p F)) ∈ O₂ := hrP
      rwa [hrmz] at h2
    exact (hOmem z).mpr hmzO₂
  · -- the homeomorphism
    haveI : IsHuberRing Bn :=
      (isTateRing_bigWindowChart p F (windowUnif p F ϖ n)).toIsHuberRing
    haveI : IsTateRing (presheafValue D') := presheafValue_isTateRing_concrete D'
    have hIM' : IM = ⇑h_n.symm ⁻¹' RT := by
      rw [hIM]
      exact h_n.toEquiv.image_eq_preimage_symm RT
    set e₁ := spaPresheafValueHomeomorphRationalOpen' D'
      (IsTateRing.exists_topologicallyNilpotent_unit
        (A := presheafValue D')).choose
      (IsTateRing.exists_topologicallyNilpotent_unit
        (A := presheafValue D')).choose_spec with he₁
    -- the second leg: the rational trace is carried onto `V`
    refine ⟨e₁.trans (Homeomorph.mk (Equiv.mk
      (fun r => ⟨⟨⟨((h_n ⟨(r : Spv Bn), r.2.2⟩
          : ↥(bigWindow p F ϖ n
            ∩ Spa (Ainf p F) (ringPlus (Ainf p F)))) : Spv (Ainf p F)),
          (h_n ⟨(r : Spv Bn), r.2.2⟩).2.2⟩,
          mem_Y_of_mem_bigWindow p F ϖ hp n
            (h_n ⟨(r : Spv Bn), r.2.2⟩).2.1⟩,
        (Set.ext_iff.mp hG₂eq (h_n ⟨(r : Spv Bn), r.2.2⟩)).mpr
          (Set.mem_image_of_mem _ (show (⟨(r : Spv Bn), r.2.2⟩
            : ↥(Spa Bn (ringPlus Bn))) ∈ RT from r.2.1)),
        (h_n ⟨(r : Spv Bn), r.2.2⟩).2.1⟩)
      (fun z => ⟨((h_n.symm ⟨((ySpaPoint p F ϖ z.1
          : ↥(Spa (Ainf p F) (ringPlus (Ainf p F)))) : Spv (Ainf p F)),
          z.2.2, (ySpaPoint p F ϖ z.1).2⟩
          : ↥(Spa Bn (ringPlus Bn))) : Spv Bn),
        (show h_n.symm ⟨_, z.2.2, (ySpaPoint p F ϖ z.1).2⟩ ∈ RT from by
          have h1 : (⟨((ySpaPoint p F ϖ z.1
              : ↥(Spa (Ainf p F) (ringPlus (Ainf p F)))) : Spv (Ainf p F)),
              z.2.2, (ySpaPoint p F ϖ z.1).2⟩
              : ↥(bigWindow p F ϖ n
                ∩ Spa (Ainf p F) (ringPlus (Ainf p F)))) ∈ IM :=
            (Set.ext_iff.mp hG₂eq _).mp z.2.1
          rw [hIM'] at h1
          exact h1),
        (h_n.symm ⟨_, z.2.2, (ySpaPoint p F ϖ z.1).2⟩).2⟩)
      (fun r => ?_) (fun z => ?_)) ?_ ?_)⟩
    · -- left inverse
      refine Subtype.ext ?_
      have key : ∀ (m : ↥(bigWindow p F ϖ n
            ∩ Spa (Ainf p F) (ringPlus (Ainf p F)))),
          m = h_n ⟨(r : Spv Bn), r.2.2⟩ →
          ((h_n.symm m : ↥(Spa Bn (ringPlus Bn))) : Spv Bn) = (r : Spv Bn) := by
        intro m hm
        rw [hm, h_n.symm_apply_apply]
      exact key _ (Subtype.ext rfl)
    · -- right inverse
      refine Subtype.ext (Subtype.ext (Subtype.ext ?_))
      set mz : ↥(bigWindow p F ϖ n
          ∩ Spa (Ainf p F) (ringPlus (Ainf p F))) :=
        ⟨((ySpaPoint p F ϖ z.1
          : ↥(Spa (Ainf p F) (ringPlus (Ainf p F)))) : Spv (Ainf p F)),
          z.2.2, (ySpaPoint p F ϖ z.1).2⟩ with hmzdef
      have h1 : (⟨((h_n.symm mz : ↥(Spa Bn (ringPlus Bn))) : Spv Bn),
          (h_n.symm mz).2⟩ : ↥(Spa Bn (ringPlus Bn))) = h_n.symm mz :=
        Subtype.ext rfl
      exact (congrArg (fun w : ↥(Spa Bn (ringPlus Bn)) =>
          ((h_n w : ↥(bigWindow p F ϖ n
            ∩ Spa (Ainf p F) (ringPlus (Ainf p F)))) : Spv (Ainf p F))) h1).trans
        (congrArg (fun m : ↥(bigWindow p F ϖ n
            ∩ Spa (Ainf p F) (ringPlus (Ainf p F))) => (m : Spv (Ainf p F)))
          (h_n.apply_symm_apply mz))
    · -- continuity, forward
      refine Continuous.subtype_mk (Continuous.subtype_mk
        (Continuous.subtype_mk ?_ _) _) _
      exact continuous_subtype_val.comp (h_n.continuous.comp
        (Continuous.subtype_mk continuous_subtype_val _))
    · -- continuity, backward
      refine Continuous.subtype_mk ?_ _
      refine continuous_subtype_val.comp (h_n.symm.continuous.comp ?_)
      refine Continuous.subtype_mk ?_ _
      exact continuous_subtype_val.comp
        (continuous_subtype_val.comp continuous_subtype_val)


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

end FarguesFontaine

end
