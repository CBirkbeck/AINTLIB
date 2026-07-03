/-
DedekindResidue: the ℚ-side facts for the relative (K/ℚ) Lemma 4.

Belabas–Friedman's Lemma 4 is applied at `k = ℚ`, so the σ-display must be
instantiated at the rationals: `ζ_ℚ` is the Riemann zeta on `Re s > 1` (there is one
ideal of `ℤ` per positive norm), the completed Riemann zeta is a completed Dedekind
zeta for `ℚ` (so mathlib's `RiemannHypothesis` transfers to our
`GeneralizedRiemannHypothesis ℚ`), and `κ_ℚ = 1`.
-/
module

public import Mathlib
public import DedekindResidue.CompletedZeta.GRH

@[expose] public section

namespace DedekindResidue

open NumberField

/-- `ℤ⧸(n)` has `n` elements, so the principal ideal `(n)` has absolute norm `n`. -/
theorem absNorm_span_natCast (n : ℕ) :
    Ideal.absNorm (Ideal.span {(n : ℤ)}) = n := by
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  rw [Nat.card_congr (Int.quotientSpanEquivZMod n).toEquiv]
  exact Nat.card_zmod n

/-- **There is exactly one ideal of `ℤ` of each positive norm.** -/
theorem card_int_ideal_absNorm_eq (n : ℕ) :
    Nat.card {J : Ideal ℤ // Ideal.absNorm J = n} = 1 := by
  rw [Nat.card_eq_one_iff_unique]
  constructor
  · -- uniqueness: `ℤ` is a PID and the generator is pinned up to sign by the norm
    refine ⟨fun ⟨J₁, hJ₁⟩ ⟨J₂, hJ₂⟩ => ?_⟩
    obtain ⟨g₁, rfl⟩ := (IsPrincipalIdealRing.principal J₁).principal
    obtain ⟨g₂, rfl⟩ := (IsPrincipalIdealRing.principal J₂).principal
    have e₁ : (Submodule.span ℤ {g₁} : Ideal ℤ) = Ideal.span {g₁} := rfl
    have e₂ : (Submodule.span ℤ {g₂} : Ideal ℤ) = Ideal.span {g₂} := rfl
    have h₁ : Ideal.span ({g₁} : Set ℤ) = Ideal.span {(g₁.natAbs : ℤ)} :=
      (Int.span_natAbs g₁).symm
    have h₂ : Ideal.span ({g₂} : Set ℤ) = Ideal.span {(g₂.natAbs : ℤ)} :=
      (Int.span_natAbs g₂).symm
    have hn₁ : g₁.natAbs = n := by
      rw [e₁, h₁, absNorm_span_natCast] at hJ₁
      exact hJ₁
    have hn₂ : g₂.natAbs = n := by
      rw [e₂, h₂, absNorm_span_natCast] at hJ₂
      exact hJ₂
    refine Subtype.ext ?_
    show (Submodule.span ℤ {g₁} : Ideal ℤ) = Submodule.span ℤ {g₂}
    rw [e₁, e₂, h₁, h₂, hn₁, hn₂]
  · exact ⟨⟨Ideal.span {(n : ℤ)}, absNorm_span_natCast n⟩⟩

/-- The absolute ideal norm is invariant under a ring isomorphism (the quotients are
isomorphic). -/
theorem absNorm_map_ringEquiv {R S : Type*} [CommRing R] [CommRing S]
    [IsDedekindDomain R] [IsDedekindDomain S]
    [Module.Free ℤ R] [Module.Finite ℤ R]
    [Module.Free ℤ S] [Module.Finite ℤ S] (e : R ≃+* S) (I : Ideal R) :
    Ideal.absNorm (I.map (e : R →+* S)) = Ideal.absNorm I := by
  rw [Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply,
    Submodule.cardQuot_apply]
  exact (Nat.card_congr (Ideal.quotientEquiv I (I.map (e : R →+* S)) e rfl).toEquiv).symm

/-- **There is exactly one ideal of `𝓞 ℚ` of each norm** (transport along
`𝓞 ℚ ≃+* ℤ`). -/
theorem card_rat_ideal_absNorm_eq (n : ℕ) :
    Nat.card {I : Ideal (𝓞 ℚ) // Ideal.absNorm I = n} = 1 := by
  have e := Rat.ringOfIntegersEquiv
  have hEquiv : {I : Ideal (𝓞 ℚ) // Ideal.absNorm I = n}
      ≃ {J : Ideal ℤ // Ideal.absNorm J = n} :=
    { toFun := fun I => ⟨I.1.map (e : 𝓞 ℚ →+* ℤ), by
        rw [absNorm_map_ringEquiv]
        exact I.2⟩
      invFun := fun J => ⟨J.1.map (e.symm : ℤ →+* 𝓞 ℚ), by
        rw [absNorm_map_ringEquiv]
        exact J.2⟩
      left_inv := fun I => Subtype.ext (Ideal.map_of_equiv e)
      right_inv := fun J => by
        refine Subtype.ext ?_
        have h1 := Ideal.map_of_equiv (I := J.1) e.symm
        rw [RingEquiv.symm_symm] at h1
        exact h1 }
  rw [Nat.card_congr hEquiv]
  exact card_int_ideal_absNorm_eq n

/-- **`ζ_ℚ` is the Riemann zeta function** on `Re s > 1`. -/
theorem dedekindZeta_rat_eq_riemannZeta {s : ℂ} (hs : 1 < s.re) :
    NumberField.dedekindZeta ℚ s = riemannZeta s := by
  rw [NumberField.dedekindZeta, ← LSeries_one_eq_riemannZeta hs]
  refine LSeries_congr (fun {n} _hn => ?_) s
  rw [card_rat_ideal_absNorm_eq n]
  simp


end DedekindResidue

end
