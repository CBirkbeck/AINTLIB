/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».FarguesFontaine.ChartSpa
import «Adic spaces».FarguesFontaine.ChartBIQ

/-!
# The chart-rational index layer of `𝒴` (E-track, E1)

The enlarged basis for the Y-structure sheaf: indices are valid rational
data over the Big-window chart rings `B_n` (uniform over the window sign
through `windowUnif`), with traces on the valuation spectrum through the
chart homeomorphisms. See the board's E-track plan (E1–E6).
-/

open TopologicalRing ValuationSpectrum WittVector NNReal

set_option linter.overlappingInstances false

noncomputable section

namespace FarguesFontaine

variable (p : ℕ) [Fact (Nat.Prime p)]
variable (F : Type*) [Field F] [TopologicalSpace F] [IsTopologicalRing F]
  [UniformSpace F] [NonarchimedeanRing F] [IsPerfectoidField p F] [CharP F p]
variable (ϖ : PseudoUniformizer F)

/-- One-is-less-than-`p` for the ambient prime. -/
theorem one_lt_p : 1 < p := Nat.Prime.one_lt (Fact.out : Nat.Prime p)

/-- **The window uniformizer**: the `p^n`-th Frobenius root for `n ≥ 0`, the
`p^{|n|}`-th power for `n < 0`. -/
def windowUnif : ℤ → PseudoUniformizer F
  | .ofNat k => PseudoUniformizer.frobRoot p F ϖ k
  | .negSucc m => PseudoUniformizer.pPow F ϖ (p ^ (m + 1))
      (pow_pos (Nat.Prime.pos (Fact.out : Nat.Prime p)) (m + 1))

/-- **The window chart ring** `B_n`: the presheaf value of the Big-window
datum in the window uniformizer. -/
def windowRing (n : ℤ) : Type _ :=
  presheafValue (chartData p F (windowUnif p F ϖ n) 1 1 p 1)

noncomputable instance (n : ℤ) : CommRing (windowRing p F ϖ n) :=
  inferInstanceAs (CommRing (presheafValue
    (chartData p F (windowUnif p F ϖ n) 1 1 p 1)))

noncomputable instance (n : ℤ) : TopologicalSpace (windowRing p F ϖ n) :=
  inferInstanceAs (TopologicalSpace (presheafValue
    (chartData p F (windowUnif p F ϖ n) 1 1 p 1)))

instance (n : ℤ) : IsTopologicalRing (windowRing p F ϖ n) :=
  inferInstanceAs (IsTopologicalRing (presheafValue
    (chartData p F (windowUnif p F ϖ n) 1 1 p 1)))

noncomputable instance (n : ℤ) : PlusSubring (windowRing p F ϖ n) :=
  inferInstanceAs (PlusSubring (presheafValue
    (chartData p F (windowUnif p F ϖ n) 1 1 p 1)))

instance (n : ℤ) : IsTateRing (windowRing p F ϖ n) :=
  isTateRing_bigWindowChart p F (windowUnif p F ϖ n)

instance (n : ℤ) : IsHuberRing (windowRing p F ϖ n) :=
  IsTateRing.toIsHuberRing

/-- **A chart-rational index**: a window number together with a valid
rational datum over its chart ring. (A `Σ`-encoding: a `structure` with
this dependent field sends the kernel through the `presheafValue`
unfolding and deterministically times out.) -/
def ChartRatIdx : Type _ :=
  Σ n : ℤ, {D : RationalLocData (windowRing p F ϖ n) // D.IsRational}

namespace ChartRatIdx

/-- The window number. -/
def n (i : ChartRatIdx p F ϖ) : ℤ := i.1

/-- The rational datum. -/
def D (i : ChartRatIdx p F ϖ) : RationalLocData (windowRing p F ϖ (i.n p F ϖ)) :=
  i.2.1

/-- Validity of the datum. -/
theorem isRational (i : ChartRatIdx p F ϖ) : (i.D p F ϖ).IsRational :=
  i.2.2

/-- The rational open of a chart-rational index inside the window's `Spa`. -/
def spaSet (i : ChartRatIdx p F ϖ) :
    Set ↥(Spa (windowRing p F ϖ (i.n p F ϖ))
      (ringPlus (windowRing p F ϖ (i.n p F ϖ)))) :=
  spaOpen (i.D p F ϖ)

/-- **The trace of a chart-rational index on the valuation spectrum**:
the image of its rational open under the window chart homeomorphism
(dispatched per window sign at the set level). -/
def trace (i : ChartRatIdx p F ϖ) : Set (Spv (Ainf p F)) :=
  match i with
  | ⟨.ofNat k, D, hD⟩ =>
      Subtype.val '' (spaChartHomeoBigWindow p F ϖ k (one_lt_p p) ''
        (spaSet p F ϖ ⟨.ofNat k, D, hD⟩))
  | ⟨.negSucc m, D, hD⟩ =>
      Subtype.val '' (spaChartHomeoBigWindowNeg p F ϖ (m + 1) (one_lt_p p) ''
        (spaSet p F ϖ ⟨.negSucc m, D, hD⟩))

end ChartRatIdx

/-- **Chart-rational traces land inside `Y`.** -/
theorem ChartRatIdx.trace_subset_Y (i : ChartRatIdx p F ϖ) :
    ChartRatIdx.trace p F ϖ i ⊆ Y p F ϖ := by
  have hcov := Y_eq_iUnion_bigWindow p F ϖ (one_lt_p p)
  obtain ⟨n, DhD⟩ := i
  match n with
  | .ofNat k =>
    rintro v ⟨w, ⟨u, -, rfl⟩, rfl⟩
    have hw : ((spaChartHomeoBigWindow p F ϖ k (one_lt_p p) u
        : ↥(bigWindow p F ϖ (k : ℤ)
          ∩ Spa (Ainf p F) (ringPlus (Ainf p F)))) : Spv (Ainf p F))
        ∈ bigWindow p F ϖ (k : ℤ)
          ∩ Spa (Ainf p F) (ringPlus (Ainf p F)) :=
      (spaChartHomeoBigWindow p F ϖ k (one_lt_p p) u).2
    rw [hcov]
    exact Set.mem_iUnion.mpr ⟨(k : ℤ), hw.1⟩
  | .negSucc m =>
    rintro v ⟨w, ⟨u, -, rfl⟩, rfl⟩
    have hw : ((spaChartHomeoBigWindowNeg p F ϖ (m + 1) (one_lt_p p) u
        : ↥(bigWindow p F ϖ (-((m + 1 : ℕ) : ℤ))
          ∩ Spa (Ainf p F) (ringPlus (Ainf p F)))) : Spv (Ainf p F))
        ∈ bigWindow p F ϖ (-((m + 1 : ℕ) : ℤ))
          ∩ Spa (Ainf p F) (ringPlus (Ainf p F)) :=
      (spaChartHomeoBigWindowNeg p F ϖ (m + 1) (one_lt_p p) u).2
    rw [hcov]
    exact Set.mem_iUnion.mpr ⟨(-((m + 1 : ℕ) : ℤ)), hw.1⟩

end FarguesFontaine

end
