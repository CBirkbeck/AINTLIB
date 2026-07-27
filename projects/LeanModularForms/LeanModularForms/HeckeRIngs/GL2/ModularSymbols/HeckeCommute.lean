/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanModularForms contributors
-/
import LeanModularForms.HeckeRIngs.GL2.ModularSymbols.HeckeSymbol
import LeanModularForms.HeckeRIngs.GL2.ModularSymbols.HeckeFinite

/-!
# Commutativity of the modular-symbol Hecke and diamond operators

The integral modular-symbol Hecke algebra is commutative.  Concretely the operators
`heckeSymb N k n` (`T_n`/`U_p`) and `diamondSymb N k d` (`⟨d⟩`) on `𝕄 N k` pairwise commute:

* `diamondSymb_commute` — `⟨d⟩` and `⟨e⟩` commute (abelian `(ZMod N)ˣ`);
* `heckeSymb_diamondSymb_commute` — `T_n` and `⟨d⟩` commute;
* `heckeSymb_commute` — `T_m` and `T_n` commute.

These feed the `hComm` hypothesis of `heckeAlgℤ_finite_of_period` (in `HeckeFinite.lean`), packaged
as `hComm_genM : Pairwise (Commute on genM N k)`.

## Strategy

Everything is built from the single-matrix tensor action `actMat` on `Div0 ℤ ⊗ SymPow ℤ m`, which is
a *covariant monoid action* (`actMat_mul`).  At the level of the tensor module the operators are
sums of `actMat M` over the Heilbronn coset matrices, and `𝕄.mk` absorbs the action of `Γ₁(N)`.
The proof mirrors the classical Hecke commutativity: at distinct primes the upper-triangular coset
matrices satisfy the CRT product identity `upperMat p b * upperMat q c = upperMat (pq) (c + b q)`,
so the double sums reindex; at the diamond level the representatives multiply commutatively modulo
`Γ₁(N)`.
-/

namespace HeckeRing.GL2.ModularSymbols

open scoped MatrixGroups TensorProduct
open Representation Matrix.SpecialLinearGroup HeckeRing.GL2 CongruenceSubgroup

variable {N : ℕ}

/-! ## Diamond operators: well-definedness and composition -/

/-- `diamondSymbAux` depends only on the image `Gamma0MapUnits γ`: if two `Γ₀(N)`-elements have the
same image unit, their descended actions on `𝕄 N k` agree.  (The ratio lies in `Γ₁(N)`, which acts
trivially on coinvariants.) -/
theorem diamondSymbAux_eq_of_Gamma0MapUnits_eq [NeZero N] (k : ℤ) (γ₁ γ₂ : ↥(Gamma0 N))
    (heq : Gamma0MapUnits γ₁ = Gamma0MapUnits γ₂) :
    diamondSymbAux k γ₁ = diamondSymbAux k γ₂ := by
  refine Coinvariants.hom_ext ?_
  refine LinearMap.ext fun x => ?_
  -- `diamondSymbAux k γᵢ (mk x) = mk (fullModSymRep γᵢ x)`
  show diamondSymbAux k γ₁ (𝕄.mk N k x) = diamondSymbAux k γ₂ (𝕄.mk N k x)
  rw [diamondSymbAux_mk, diamondSymbAux_mk]
  -- `γ₁ = (γ₁ γ₂⁻¹) γ₂`, with `γ₁ γ₂⁻¹ ∈ Γ₁(N)`.
  have hmem : (γ₁ : SL(2, ℤ)) * (γ₂ : SL(2, ℤ))⁻¹ ∈ Gamma1 N := by
    have hg0 : ((γ₁ : SL(2, ℤ)) * (γ₂ : SL(2, ℤ))⁻¹) ∈ Gamma0 N :=
      (Gamma0 N).mul_mem γ₁.property ((Gamma0 N).inv_mem γ₂.property)
    refine mem_gamma1_of_gamma0MapUnits_one ⟨_, hg0⟩ ?_
    have hsplit : Gamma0MapUnits (⟨(γ₁ : SL(2, ℤ)) * (γ₂ : SL(2, ℤ))⁻¹, hg0⟩ : ↥(Gamma0 N))
        = Gamma0MapUnits γ₁ * (Gamma0MapUnits γ₂)⁻¹ := by
      rw [← map_inv, ← map_mul]; rfl
    rw [hsplit, heq, mul_inv_cancel]
  have hfac : (γ₁ : SL(2, ℤ)) = ((γ₁ : SL(2, ℤ)) * (γ₂ : SL(2, ℤ))⁻¹) * (γ₂ : SL(2, ℤ)) := by
    rw [inv_mul_cancel_right]
  rw [hfac, map_mul, Module.End.mul_apply]
  exact Representation.Coinvariants.mk_self_apply (modSymRep N (k - 2).toNat) ⟨_, hmem⟩ _

/-- `diamondSymb` equals `diamondSymbAux` on any representative with the correct image. -/
theorem diamondSymb_eq_diamondSymbAux [NeZero N] (k : ℤ) (d : (ZMod N)ˣ) (γ : ↥(Gamma0 N))
    (hγ : Gamma0MapUnits γ = d) : diamondSymb N k d = diamondSymbAux k γ :=
  diamondSymbAux_eq_of_Gamma0MapUnits_eq k _ γ
    (by rw [(Gamma0MapUnits_surjective d).choose_spec, hγ])

/-- The diamond operators compose: `⟨d * e⟩ = ⟨d⟩ ∘ ⟨e⟩`. -/
theorem diamondSymb_mul [NeZero N] (k : ℤ) (d e : (ZMod N)ˣ) :
    diamondSymb N k (d * e) = diamondSymb N k d ∘ₗ diamondSymb N k e := by
  obtain ⟨γd, hγd⟩ := Gamma0MapUnits_surjective (N := N) d
  obtain ⟨γe, hγe⟩ := Gamma0MapUnits_surjective (N := N) e
  rw [diamondSymb_eq_diamondSymbAux k (d * e) (γd * γe) (by rw [map_mul, hγd, hγe]),
    diamondSymb_eq_diamondSymbAux k d γd hγd, diamondSymb_eq_diamondSymbAux k e γe hγe]
  refine Coinvariants.hom_ext ?_
  refine LinearMap.ext fun x => ?_
  show diamondSymbAux k (γd * γe) (𝕄.mk N k x)
    = diamondSymbAux k γd (diamondSymbAux k γe (𝕄.mk N k x))
  rw [diamondSymbAux_mk, diamondSymbAux_mk, diamondSymbAux_mk]
  rw [Submonoid.coe_mul, map_mul, Module.End.mul_apply]

/-- The diamond operator at `1` is the identity. -/
@[simp]
theorem diamondSymb_one [NeZero N] (k : ℤ) :
    diamondSymb N k 1 = (1 : Module.End ℤ (𝕄 N k)) := by
  rw [diamondSymb_eq_diamondSymbAux k 1 1 (map_one _)]
  refine Coinvariants.hom_ext ?_
  refine LinearMap.ext fun x => ?_
  show diamondSymbAux k 1 (𝕄.mk N k x) = (1 : Module.End ℤ (𝕄 N k)) (𝕄.mk N k x)
  rw [diamondSymbAux_mk]
  simp only [OneMemClass.coe_one, map_one, Module.End.one_apply]

/-! ## A `Γ₀(N)`-coset descent for the diamond commutation -/

/-- `𝕄.mk` absorbs the difference between two `Γ₀(N)`-representatives with the same image: if
`τ γ⁻¹ ∈ Γ₁(N)`, then `mk (fullModSymRep τ y) = mk (fullModSymRep γ y)`. -/
theorem mk_fullModSymRep_eq_of_gamma0MapUnits_eq [NeZero N] (k : ℤ) (γ τ : ↥(Gamma0 N))
    (heq : Gamma0MapUnits τ = Gamma0MapUnits γ) (y : Div0 ℤ ⊗[ℤ] SymPow ℤ (k - 2).toNat) :
    𝕄.mk N k (fullModSymRep ℤ (k - 2).toNat (τ : SL(2, ℤ)) y)
      = 𝕄.mk N k (fullModSymRep ℤ (k - 2).toNat (γ : SL(2, ℤ)) y) := by
  have hmem : (τ : SL(2, ℤ)) * (γ : SL(2, ℤ))⁻¹ ∈ Gamma1 N :=
    mul_inv_mem_Gamma1_of_Gamma0Map_eq τ γ (Units.ext_iff.mp heq)
  have hfac : (τ : SL(2, ℤ)) = ((τ : SL(2, ℤ)) * (γ : SL(2, ℤ))⁻¹) * (γ : SL(2, ℤ)) := by
    rw [inv_mul_cancel_right]
  rw [hfac, map_mul, Module.End.mul_apply]
  exact Representation.Coinvariants.mk_self_apply (modSymRep N (k - 2).toNat) ⟨_, hmem⟩ _

/-- **`Γ₀(N)`-coset descent.**  If `A · γ = τ · B` (integer matrices) with `γ, τ ∈ Γ₀(N)` having the
same diamond image `Gamma0MapUnits`, then the coinvariant class `mk (actMat A (ρ_γ x))` equals
`mk (ρ_γ (actMat B x))`.  This is the diamond version of `mk_actMat_coset` (where the conjugating
element was required to lie in `Γ₁(N)`): now it may lie in `Γ₀(N)`, provided it has the *same*
diamond image as `γ` (so `mk` still sees them as equal). -/
theorem mk_actMat_coset_gamma0 [NeZero N] {A B : Matrix (Fin 2) (Fin 2) ℤ} (hA : A.det ≠ 0)
    (hB : B.det ≠ 0) (k : ℤ) (γ τ : ↥(Gamma0 N))
    (heq : Gamma0MapUnits τ = Gamma0MapUnits γ)
    (hmat : A * ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)
      = ((τ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * B)
    (x : Div0 ℤ ⊗[ℤ] SymPow ℤ (k - 2).toNat) :
    𝕄.mk N k (actMat A hA (k - 2).toNat (fullModSymRep ℤ (k - 2).toNat (γ : SL(2, ℤ)) x))
      = 𝕄.mk N k (fullModSymRep ℤ (k - 2).toNat (γ : SL(2, ℤ))
          (actMat B hB (k - 2).toNat x)) := by
  rw [actMat_comp_fullModSymRep hA hB (k - 2).toNat (γ : SL(2, ℤ)) (τ : SL(2, ℤ)) hmat x]
  exact mk_fullModSymRep_eq_of_gamma0MapUnits_eq k γ τ heq _

/-- The conjugating element `τ` from `upperMat_mul_sl` lies in `Γ₀(N)` with the *same* diamond image
as `σ`, whenever `σ ∈ Γ₀(N)` (so `σ₁₀ ≡ 0` mod `N`).  The witnessing entries are exactly those
returned by `upperMat_mul_sl`. -/
theorem upperMat_mul_sl_tau_gamma0 [NeZero N] {p : ℕ} (_hp : Nat.Prime p)
    (σ : ↥(Gamma0 N)) {τ : SL(2, ℤ)} {j₀ j₁ : ℕ}
    (_hτ00 : (τ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 =
        ((σ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 0
          + ↑j₀ * ((σ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0)
    (hτ10 : (τ : Matrix (Fin 2) (Fin 2) ℤ) 1 0
        = ↑p * ((σ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0)
    (hτ11 : (τ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 =
        ((σ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 1
          - ((σ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0 * ↑j₁) :
    ∃ hτ : τ ∈ Gamma0 N, Gamma0MapUnits (⟨τ, hτ⟩ : ↥(Gamma0 N)) = Gamma0MapUnits σ := by
  have hσ10 : (((σ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ZMod N) = 0 :=
    (Gamma0_mem (N := N)).mp σ.property
  have hτ_g0 : τ ∈ Gamma0 N := by
    rw [Gamma0_mem]
    show ((τ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ZMod N) = 0
    rw [hτ10]; push_cast; rw [hσ10, mul_zero]
  refine ⟨hτ_g0, Units.ext ?_⟩
  simp only [Gamma0MapUnits_val, Gamma0Map, MonoidHom.coe_mk, OneHom.coe_mk]
  show ((τ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ZMod N)
    = (((σ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ZMod N)
  rw [hτ11]; push_cast; rw [hσ10, zero_mul, sub_zero]

/-- For `σ ∈ Γ₀(N)` and `p ∣ N`, every value `σ₀₀ + b·σ₁₀` is coprime to `p` (`σ₀₀` is a unit
mod `N` hence mod `p`, and `σ₁₀ ≡ 0` mod `p`). -/
theorem not_dvd_gamma0_divN [NeZero N] {p : ℕ} (hp : Nat.Prime p) (hpN : ¬Nat.Coprime p N)
    (σ : ↥(Gamma0 N)) (b : ℕ) :
    ¬(p : ℤ) ∣ (((σ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 0
      + ↑b * ((σ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0) := by
  haveI : Fact p.Prime := ⟨hp⟩
  set M := ((σ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) with hM
  have hdet_M : M.det = 1 := by exact_mod_cast (σ : SL(2, ℤ)).prop
  have hp_dvd_N : (p : ℤ) ∣ (N : ℤ) := by
    rw [Int.natCast_dvd_natCast]; by_contra h; exact hpN (hp.coprime_iff_not_dvd.mpr h)
  have hσ_g0 := (Gamma0_mem (N := N)).mp σ.property
  have hp_dvd_σ10 : (p : ℤ) ∣ M 1 0 :=
    hp_dvd_N.trans <| by rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]; exact_mod_cast hσ_g0
  have hσ00_ne : ((M 0 0 : ℤ) : ZMod p) ≠ 0 := by
    intro h00
    have h10 : ((M 1 0 : ℤ) : ZMod p) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hp_dvd_σ10
    have hdet_zmod : ((M 0 0 * M 1 1 - M 0 1 * M 1 0 : ℤ) : ZMod p) = 1 := by
      rw [Matrix.det_fin_two] at hdet_M; simp [hdet_M]
    rw [show ((M 0 0 * M 1 1 - M 0 1 * M 1 0 : ℤ) : ZMod p) =
      ((M 0 0 : ℤ) : ZMod p) * ((M 1 1 : ℤ) : ZMod p)
        - ((M 0 1 : ℤ) : ZMod p) * ((M 1 0 : ℤ) : ZMod p) by push_cast; ring,
      h00, h10, zero_mul, mul_zero, sub_zero] at hdet_zmod
    exact zero_ne_one hdet_zmod
  intro hdvd
  have hz : ((M 0 0 + ↑b * M 1 0 : ℤ) : ZMod p) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hdvd
  have h10 : ((M 1 0 : ℤ) : ZMod p) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hp_dvd_σ10
  rw [show ((M 0 0 + ↑b * M 1 0 : ℤ) : ZMod p) =
    ((M 0 0 : ℤ) : ZMod p) + ((b : ℤ) : ZMod p) * ((M 1 0 : ℤ) : ZMod p) by push_cast; ring,
    h10, mul_zero, add_zero] at hz
  exact hσ00_ne hz

/-- The `𝕄.mk`-level coset descent for one upper representative under a `Γ₀(N)` element: the
diamond-twisted version of `mk_actMat_upperMat_comp_fullModSymRep`. -/
theorem mk_actMat_upperMat_comp_fullModSymRep_gamma0 [NeZero N] {p : ℕ} (hp : 0 < p) (k : ℤ)
    (γ τ : ↥(Gamma0 N)) (heq : Gamma0MapUnits τ = Gamma0MapUnits γ) (b b' : ℕ)
    (hmat : upperMat p b * ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)
      = ((τ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * upperMat p b')
    (x : Div0 ℤ ⊗[ℤ] SymPow ℤ (k - 2).toNat) :
    𝕄.mk N k (actMat (upperMat p b) (upperMat_det_ne_zero hp b) (k - 2).toNat
        (fullModSymRep ℤ (k - 2).toNat (γ : SL(2, ℤ)) x))
      = 𝕄.mk N k (fullModSymRep ℤ (k - 2).toNat (γ : SL(2, ℤ))
          (actMat (upperMat p b') (upperMat_det_ne_zero hp b') (k - 2).toNat x)) :=
  mk_actMat_coset_gamma0 (upperMat_det_ne_zero hp b) (upperMat_det_ne_zero hp b') k γ τ heq hmat x

/-- **`U_p` (`p ∣ N`) commutes with the diamond at the tensor level.**  For `γ ∈ Γ₀(N)` and `p ∣ N`,
the upper-triangular sum operator and `fullModSymRep γ` commute modulo `Γ₁(N)`-coinvariants: the
coset representatives are permuted, each up to a left `Γ₀(N)`-factor with the *same* diamond image
as `γ`. -/
theorem mk_upperOp_fullModSymRep_gamma0_divN [NeZero N] {p : ℕ} (hp : Nat.Prime p)
    (hpN : ¬Nat.Coprime p N) (k : ℤ) (γ : ↥(Gamma0 N))
    (x : Div0 ℤ ⊗[ℤ] SymPow ℤ (k - 2).toNat) :
    𝕄.mk N k (upperOp p hp.pos (k - 2).toNat
        (fullModSymRep ℤ (k - 2).toNat (γ : SL(2, ℤ)) x))
      = 𝕄.mk N k (fullModSymRep ℤ (k - 2).toNat (γ : SL(2, ℤ))
          (upperOp p hp.pos (k - 2).toNat x)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  -- Distribute `mk` over the LHS sum and `mk ∘ ρ_γ` over the RHS sum (via the *composite* linear
  -- map, to avoid the tensor-product module-instance diamond).
  have hlhs : 𝕄.mk N k ((upperOp p hp.pos (k - 2).toNat)
        (fullModSymRep ℤ (k - 2).toNat (γ : SL(2, ℤ)) x))
      = ∑ b ∈ Finset.range p, 𝕄.mk N k ((actMat (upperMat p b) (upperMat_det_ne_zero hp.pos b)
          (k - 2).toNat) (fullModSymRep ℤ (k - 2).toNat (γ : SL(2, ℤ)) x)) := by
    rw [upperOp_apply]; exact _root_.map_sum (𝕄.mk N k) _ _
  have hrhs : 𝕄.mk N k ((fullModSymRep ℤ (k - 2).toNat (γ : SL(2, ℤ)))
        ((upperOp p hp.pos (k - 2).toNat) x))
      = ∑ b ∈ Finset.range p, 𝕄.mk N k ((fullModSymRep ℤ (k - 2).toNat (γ : SL(2, ℤ)))
          ((actMat (upperMat p b) (upperMat_det_ne_zero hp.pos b) (k - 2).toNat) x)) := by
    rw [upperOp_apply]
    exact _root_.map_sum ((𝕄.mk N k).comp (fullModSymRep ℤ (k - 2).toNat (γ : SL(2, ℤ)))) _ _
  rw [hlhs, hrhs, ← Fin.sum_univ_eq_sum_range, ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_equiv
    (Equiv.ofBijective _ (moebiusFin'_bijective_of_gamma1 hp (γ : SL(2, ℤ))))
    (fun _ => ⟨fun _ => Finset.mem_univ _, fun _ => Finset.mem_univ _⟩) (fun b _ => ?_)
  rw [Equiv.ofBijective_apply]
  obtain ⟨τ, hmat, hτ00, hτ10, hτ11⟩ := upperMat_mul_sl hp (γ : SL(2, ℤ)) b
    (not_dvd_gamma0_divN hp hpN γ b.val)
  obtain ⟨hτ_g0, hτ_eq⟩ := upperMat_mul_sl_tau_gamma0 hp γ hτ00 hτ10 hτ11
  exact mk_actMat_upperMat_comp_fullModSymRep_gamma0 hp.pos k γ ⟨τ, hτ_g0⟩ hτ_eq
    b.val (moebiusFin' p hp ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) b).val hmat x

/-! ## `Γ₀(N)` coset identities at good primes (diamond-tracking versions) -/

/-- **Lower → upper (case `p ∤ σ₁₀`), `Γ₀(N)` version.**  For `σ ∈ Γ₀(N)`, `p ∤ N`, the
diamond-twisted lower representative maps under right multiplication by `σ` to an upper
representative, up to a left `Γ₀(N)`-factor *with the same diamond image as `σ`*. -/
theorem lowerDiamondMat_mul_sl_gamma0 {p : ℕ} [NeZero N] [Fact p.Prime] (hp : Nat.Prime p)
    (hpN : Nat.Coprime p N) (σ : ↥(Gamma0 N))
    (hσ10 : ¬(p : ℤ) ∣ ((σ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0) :
    ∃ (γ' : SL(2, ℤ)) (hγ' : γ' ∈ Gamma0 N),
      Gamma0MapUnits ⟨γ', hγ'⟩ = Gamma0MapUnits σ ∧
      lowerDiamondMat (N := N) hpN * ((σ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)
        = (γ' : Matrix (Fin 2) (Fin 2) ℤ) * upperMat p
            ((((((σ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ZMod p)
              * ((((σ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℤ) : ZMod p)⁻¹).val) := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  set M := ((σ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) with hM
  have hdet : M 0 0 * M 1 1 - M 0 1 * M 1 0 = 1 := by
    have := (σ : SL(2, ℤ)).prop; rw [Matrix.det_fin_two] at this; exact this
  have hσ_mem0 := (Gamma0_mem (N := N)).mp σ.property
  have h10_ne : ((M 1 0 : ℤ) : ZMod p) ≠ 0 :=
    fun h => hσ10 ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h)
  set j' := (((M 1 1 : ℤ) : ZMod p) * ((M 1 0 : ℤ) : ZMod p)⁻¹).val with hj'
  obtain ⟨q, hq⟩ := hb_dvd_sub_mul_inv_val (M 1 1) (M 1 0) h10_ne
  rw [← hj'] at hq
  set τl : Matrix (Fin 2) (Fin 2) ℤ := !![↑p * M 0 0, M 0 1 - M 0 0 * ↑j'; M 1 0, q] with hτl
  set τ : SL(2, ℤ) := ⟨τl, hb_lower_tau_det hdet p (↑j') q hq⟩ with hτ
  have hτ_g0 : τ ∈ Gamma0 N := by
    rw [Gamma0_mem]; show ((M 1 0 : ℤ) : ZMod N) = 0; exact hσ_mem0
  have hprod_g0 : ((diamondRep (N := N) hpN : SL(2, ℤ)) * τ) ∈ Gamma0 N :=
    (Gamma0 N).mul_mem (diamondRep (N := N) hpN).property hτ_g0
  refine ⟨(diamondRep (N := N) hpN : SL(2, ℤ)) * τ, hprod_g0, ?_, ?_⟩
  · -- `Gamma0MapUnits (γ_p * τ) = Gamma0MapUnits σ`
    have hτ_unit : Gamma0MapUnits ⟨τ, hτ_g0⟩
        = (ZMod.unitOfCoprime p hpN)⁻¹ * Gamma0MapUnits σ := by
      rw [eq_inv_mul_iff_mul_eq]; ext
      simp only [Gamma0MapUnits_val, Gamma0Map, MonoidHom.coe_mk, OneHom.coe_mk,
        ZMod.coe_unitOfCoprime, Units.val_mul]
      show ((p : ℕ) : ZMod N) * ((q : ℤ) : ZMod N) = (M 1 1 : ZMod N)
      rw [← Int.cast_natCast (R := ZMod N) p, ← Int.cast_mul, ← hq]
      push_cast; rw [hσ_mem0, zero_mul, sub_zero]
    have hsplit : Gamma0MapUnits (⟨(diamondRep (N := N) hpN : SL(2, ℤ)) * τ, hprod_g0⟩ :
          ↥(Gamma0 N))
        = Gamma0MapUnits (diamondRep (N := N) hpN) * Gamma0MapUnits ⟨τ, hτ_g0⟩ := by
      rw [← map_mul]; rfl
    rw [hsplit, diamondRep_spec, hτ_unit, ← mul_assoc, mul_inv_cancel, one_mul]
  · -- the matrix identity `lowerDiamondMat * M = (γ_p * τ) * upper(j')`
    show lowerDiamondMat (N := N) hpN * M
      = (((diamondRep (N := N) hpN : SL(2, ℤ)) * τ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)
        * upperMat p j'
    rw [lowerDiamondMat, Matrix.SpecialLinearGroup.coe_mul, mul_assoc, mul_assoc]
    congr 1
    show lowerMat p * M = (τ : Matrix (Fin 2) (Fin 2) ℤ) * upperMat p j'
    rw [hτ]
    show lowerMat p * M = τl * upperMat p j'
    have hM11 : M 1 1 = M 1 0 * (j' : ℤ) + q * ↑p := by linarith [hq]
    have e00 : (lowerMat p * M) 0 0 = (τl * upperMat p j') 0 0 := by
      simp only [hτl, lowerMat, upperMat, Matrix.mul_apply, Fin.sum_univ_two, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.of_apply]; ring
    have e01 : (lowerMat p * M) 0 1 = (τl * upperMat p j') 0 1 := by
      simp only [hτl, lowerMat, upperMat, Matrix.mul_apply, Fin.sum_univ_two, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.of_apply]; ring
    have e10 : (lowerMat p * M) 1 0 = (τl * upperMat p j') 1 0 := by
      simp only [hτl, lowerMat, upperMat, Matrix.mul_apply, Fin.sum_univ_two, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.of_apply]; ring
    have e11 : (lowerMat p * M) 1 1 = (τl * upperMat p j') 1 1 := by
      simp only [hτl, lowerMat, upperMat, Matrix.mul_apply, Fin.sum_univ_two, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.of_apply]
      rw [hM11]; ring
    ext i j; fin_cases i <;> fin_cases j
    · exact e00
    · exact e01
    · exact e10
    · exact e11

/-- **Upper → lower (case `p ∤ σ₁₀`, special index `b₀`), `Γ₀(N)` version.**  For `σ ∈ Γ₀(N)`,
`p ∤ N`, if `p ∣ σ₀₀ + b₀·σ₁₀` then `upper(b₀)·σ` maps to the diamond-twisted lower representative,
up to a left `Γ₀(N)`-factor with the same diamond image as `σ`. -/
theorem upperMat_mul_sl_to_lower_gamma0 {p : ℕ} [NeZero N] [Fact p.Prime] (_hp : Nat.Prime p)
    (hpN : Nat.Coprime p N) (σ : ↥(Gamma0 N)) (b₀ : ℕ)
    (hb₀ : (p : ℤ) ∣ (((σ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 0 +
      ↑b₀ * ((σ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0)) :
    ∃ (γ' : SL(2, ℤ)) (hγ' : γ' ∈ Gamma0 N),
      Gamma0MapUnits ⟨γ', hγ'⟩ = Gamma0MapUnits σ ∧
      upperMat p b₀ * ((σ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)
        = (γ' : Matrix (Fin 2) (Fin 2) ℤ) * lowerDiamondMat (N := N) hpN := by
  set M := ((σ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) with hM
  have hdet : M 0 0 * M 1 1 - M 0 1 * M 1 0 = 1 := by
    have := (σ : SL(2, ℤ)).prop; rw [Matrix.det_fin_two] at this; exact this
  have hσ_mem0 := (Gamma0_mem (N := N)).mp σ.property
  obtain ⟨a, ha⟩ := hb₀
  have ha' : M 0 0 + ↑b₀ * M 1 0 = a * ↑p := by rw [ha, mul_comm]
  set τu : Matrix (Fin 2) (Fin 2) ℤ := !![a, M 0 1 + ↑b₀ * M 1 1; M 1 0, ↑p * M 1 1] with hτu
  set τ : SL(2, ℤ) := ⟨τu, hb_upper_div_tau_det hdet p a ↑b₀ ha'⟩ with hτ
  have hτ_g0 : τ ∈ Gamma0 N := by
    rw [Gamma0_mem]; show ((M 1 0 : ℤ) : ZMod N) = 0; exact hσ_mem0
  have hinv_g0 : ((diamondRep (N := N) hpN : SL(2, ℤ))⁻¹) ∈ Gamma0 N :=
    (Gamma0 N).inv_mem (diamondRep (N := N) hpN).property
  have hprod_g0 : (τ * (diamondRep (N := N) hpN : SL(2, ℤ))⁻¹) ∈ Gamma0 N :=
    (Gamma0 N).mul_mem hτ_g0 hinv_g0
  refine ⟨τ * (diamondRep (N := N) hpN : SL(2, ℤ))⁻¹, hprod_g0, ?_, ?_⟩
  · -- `Gamma0MapUnits (τ * γ_p⁻¹) = Gamma0MapUnits σ`
    have hτ_unit : Gamma0MapUnits ⟨τ, hτ_g0⟩ = ZMod.unitOfCoprime p hpN * Gamma0MapUnits σ := by
      ext
      simp only [Gamma0MapUnits_val, Gamma0Map, MonoidHom.coe_mk, OneHom.coe_mk,
        ZMod.coe_unitOfCoprime, Units.val_mul]
      show ((↑p * M 1 1 : ℤ) : ZMod N) = ((p : ℕ) : ZMod N) * (M 1 1 : ZMod N)
      push_cast; ring
    have hsplit : Gamma0MapUnits (⟨τ * (diamondRep (N := N) hpN : SL(2, ℤ))⁻¹, hprod_g0⟩ :
          ↥(Gamma0 N))
        = Gamma0MapUnits ⟨τ, hτ_g0⟩ * Gamma0MapUnits ⟨(diamondRep (N := N) hpN : SL(2, ℤ))⁻¹,
            hinv_g0⟩ := by
      rw [← map_mul]; rfl
    have hinv_unit : Gamma0MapUnits ⟨(diamondRep (N := N) hpN : SL(2, ℤ))⁻¹, hinv_g0⟩
        = (ZMod.unitOfCoprime p hpN)⁻¹ := by
      have : Gamma0MapUnits ⟨(diamondRep (N := N) hpN : SL(2, ℤ))⁻¹, hinv_g0⟩
          = (Gamma0MapUnits (diamondRep (N := N) hpN))⁻¹ := by rw [← map_inv]; rfl
      rw [this, diamondRep_spec]
    rw [hsplit, hτ_unit, hinv_unit, mul_right_comm, mul_inv_cancel, one_mul]
  · -- matrix identity: `upper(b₀) * M = (τ * γ_p⁻¹) * lowerDiamondMat`
    have hM00 : M 0 0 + ↑b₀ * M 1 0 = a * ↑p := ha'
    have htriv : (τ * (diamondRep (N := N) hpN : SL(2, ℤ))⁻¹) *
        (diamondRep (N := N) hpN : SL(2, ℤ)) = τ := by
      rw [mul_assoc, inv_mul_cancel, mul_one]
    have hcoe : ((τ * (diamondRep (N := N) hpN : SL(2, ℤ))⁻¹ : SL(2, ℤ)) :
          Matrix (Fin 2) (Fin 2) ℤ) * lowerDiamondMat (N := N) hpN
        = (τ : Matrix (Fin 2) (Fin 2) ℤ) * lowerMat p := by
      rw [lowerDiamondMat, diamondMat, ← mul_assoc, ← Matrix.SpecialLinearGroup.coe_mul, htriv]
    rw [hcoe]
    show upperMat p b₀ * M = τu * lowerMat p
    have e00 : (upperMat p b₀ * M) 0 0 = (τu * lowerMat p) 0 0 := by
      simp only [hτu, upperMat, lowerMat, Matrix.mul_apply, Fin.sum_univ_two,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.of_apply]
      linear_combination hM00
    have e01 : (upperMat p b₀ * M) 0 1 = (τu * lowerMat p) 0 1 := by
      simp only [hτu, upperMat, lowerMat, Matrix.mul_apply, Fin.sum_univ_two,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.of_apply]; ring
    have e10 : (upperMat p b₀ * M) 1 0 = (τu * lowerMat p) 1 0 := by
      simp only [hτu, upperMat, lowerMat, Matrix.mul_apply, Fin.sum_univ_two,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.of_apply]; ring
    have e11 : (upperMat p b₀ * M) 1 1 = (τu * lowerMat p) 1 1 := by
      simp only [hτu, upperMat, lowerMat, Matrix.mul_apply, Fin.sum_univ_two,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.of_apply]; ring
    ext i j; fin_cases i <;> fin_cases j
    · exact e00
    · exact e01
    · exact e10
    · exact e11

/-- **Lower → lower (case `p ∣ σ₁₀`), `Γ₀(N)` version.**  For `σ ∈ Γ₀(N)`, `p ∤ N`, if `p ∣ σ₁₀`
then the diamond-twisted lower representative is fixed (up to a left `Γ₀(N)`-factor with the same
diamond image as `σ`) by right multiplication by `σ`. -/
theorem lowerDiamondMat_mul_sl_fixed_gamma0 {p : ℕ} [NeZero N] (_hp : Nat.Prime p)
    (hpN : Nat.Coprime p N) (σ : ↥(Gamma0 N))
    (hσ10 : (p : ℤ) ∣ ((σ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0) :
    ∃ (γ' : SL(2, ℤ)) (hγ' : γ' ∈ Gamma0 N),
      Gamma0MapUnits ⟨γ', hγ'⟩ = Gamma0MapUnits σ ∧
      lowerDiamondMat (N := N) hpN * ((σ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)
        = (γ' : Matrix (Fin 2) (Fin 2) ℤ) * lowerDiamondMat (N := N) hpN := by
  set M := ((σ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) with hM
  have hdet : M 0 0 * M 1 1 - M 0 1 * M 1 0 = 1 := by
    have := (σ : SL(2, ℤ)).prop; rw [Matrix.det_fin_two] at this; exact this
  have hσ_mem0 := (Gamma0_mem (N := N)).mp σ.property
  obtain ⟨c, hc⟩ := hσ10  -- M 1 0 = p * c
  set τl : Matrix (Fin 2) (Fin 2) ℤ := !![M 0 0, ↑p * M 0 1; c, M 1 1] with hτl
  have hτl_det : τl.det = 1 := by
    rw [hτl, Matrix.det_fin_two_of]
    have hh : M 1 0 = ↑p * c := hc
    linear_combination hdet + M 0 1 * hh
  set τ : SL(2, ℤ) := ⟨τl, hτl_det⟩ with hτ
  have hcN : (N : ℤ) ∣ c := by
    have hM10N : (N : ℤ) ∣ M 1 0 := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, hM]; exact_mod_cast hσ_mem0
    have hpN' : IsCoprime (p : ℤ) (N : ℤ) := by
      rw [Int.isCoprime_iff_gcd_eq_one]; exact_mod_cast hpN
    exact IsCoprime.dvd_of_dvd_mul_left hpN'.symm (hc ▸ hM10N)
  have hτ_g0 : τ ∈ Gamma0 N := by
    rw [Gamma0_mem]
    show ((τl 1 0 : ℤ) : ZMod N) = 0
    simp only [hτl, Matrix.cons_val_zero, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hcN
  have hτ_eq : Gamma0MapUnits ⟨τ, hτ_g0⟩ = Gamma0MapUnits σ := by
    ext
    simp only [Gamma0MapUnits_val, Gamma0Map, MonoidHom.coe_mk, OneHom.coe_mk]
    congr 1
  -- γ' := γ_p * τ * γ_p⁻¹ ∈ Γ₀(N) with the same image as σ
  have hg' : ((diamondRep (N := N) hpN : SL(2, ℤ)) * (τ : SL(2, ℤ))
      * (diamondRep (N := N) hpN : SL(2, ℤ))⁻¹) ∈ Gamma0 N :=
    (Gamma0 N).mul_mem ((Gamma0 N).mul_mem (diamondRep (N := N) hpN).property hτ_g0)
      ((Gamma0 N).inv_mem (diamondRep (N := N) hpN).property)
  refine ⟨(diamondRep (N := N) hpN : SL(2, ℤ)) * (τ : SL(2, ℤ))
      * (diamondRep (N := N) hpN : SL(2, ℤ))⁻¹, hg', ?_, ?_⟩
  · -- `Gamma0MapUnits γ' = Gamma0MapUnits σ` (conjugation in the abelian group `(ZMod N)ˣ`)
    have hsplit : Gamma0MapUnits (⟨(diamondRep (N := N) hpN : SL(2, ℤ)) * (τ : SL(2, ℤ))
          * (diamondRep (N := N) hpN : SL(2, ℤ))⁻¹, hg'⟩ : ↥(Gamma0 N))
        = Gamma0MapUnits (diamondRep (N := N) hpN) * Gamma0MapUnits ⟨τ, hτ_g0⟩
          * (Gamma0MapUnits (diamondRep (N := N) hpN))⁻¹ := by
      rw [← map_inv, ← map_mul, ← map_mul]; rfl
    rw [hsplit, hτ_eq, mul_right_comm, mul_inv_cancel, one_mul]
  · -- `lowerDiamond * M = γ' * lowerDiamond`
    have hlowerτ : lowerMat p * M = (τ : Matrix (Fin 2) (Fin 2) ℤ) * lowerMat p := by
      have e00 : (lowerMat p * M) 0 0 = (τl * lowerMat p) 0 0 := by
        simp only [hτl, lowerMat, Matrix.mul_apply, Fin.sum_univ_two, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.of_apply]; ring
      have e01 : (lowerMat p * M) 0 1 = (τl * lowerMat p) 0 1 := by
        simp only [hτl, lowerMat, Matrix.mul_apply, Fin.sum_univ_two, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.of_apply]; ring
      have e10 : (lowerMat p * M) 1 0 = (τl * lowerMat p) 1 0 := by
        simp only [hτl, lowerMat, Matrix.mul_apply, Fin.sum_univ_two, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.of_apply]
        rw [hc]; ring
      have e11 : (lowerMat p * M) 1 1 = (τl * lowerMat p) 1 1 := by
        simp only [hτl, lowerMat, Matrix.mul_apply, Fin.sum_univ_two, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.of_apply]; ring
      ext i j; fin_cases i <;> fin_cases j
      · exact e00
      · exact e01
      · exact e10
      · exact e11
    have hcancel : ((diamondRep (N := N) hpN : SL(2, ℤ)) * (τ : SL(2, ℤ))
          * (diamondRep (N := N) hpN : SL(2, ℤ))⁻¹) * (diamondRep (N := N) hpN : SL(2, ℤ))
        = (diamondRep (N := N) hpN : SL(2, ℤ)) * (τ : SL(2, ℤ)) := by
      rw [mul_assoc, inv_mul_cancel, mul_one]
    have hrhs : (((diamondRep (N := N) hpN : SL(2, ℤ)) * (τ : SL(2, ℤ))
          * (diamondRep (N := N) hpN : SL(2, ℤ))⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)
        * lowerDiamondMat (N := N) hpN
        = (((diamondRep (N := N) hpN : SL(2, ℤ)) * (τ : SL(2, ℤ)) : SL(2, ℤ)) :
            Matrix (Fin 2) (Fin 2) ℤ) * lowerMat p := by
      rw [lowerDiamondMat, diamondMat, ← mul_assoc, ← Matrix.SpecialLinearGroup.coe_mul, hcancel]
    rw [show lowerDiamondMat (N := N) hpN * M
        = ((diamondRep (N := N) hpN : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)
          * (lowerMat p * M) by rw [lowerDiamondMat, diamondMat, mul_assoc], hlowerτ, hrhs,
      Matrix.SpecialLinearGroup.coe_mul, mul_assoc]

/-- Generic distribution of a linear map `f` over `tpOp x`: `f (tpOp x)` expands into `∑ f (actMat
upper x) + f (actMat lower x)`.  Distributing `f` over the operator sum is stated explicitly to pin
the tensor module instance (avoiding the `AddCommGroup.toIntModule`/`TensorProduct.instModule`
diamond that blocks a bare `map_add`/`map_sum` rewrite). -/
theorem map_tpOp_apply_eq [NeZero N] {p : ℕ} (hp : Nat.Prime p) (hpN : Nat.Coprime p N) (m : ℕ)
    {W : Type*} [AddCommGroup W] [Module ℤ W] (f : (Div0 ℤ ⊗[ℤ] SymPow ℤ m) →ₗ[ℤ] W)
    (x : Div0 ℤ ⊗[ℤ] SymPow ℤ m) :
    f (tpOp hp.pos hpN m x)
      = (∑ b : Fin p, f (actMat (upperMat p b.val) (upperMat_det_ne_zero hp.pos b.val) m x))
        + f (actMat (lowerDiamondMat (N := N) hpN)
            (lowerDiamondMat_det_ne_zero hp.pos hpN) m x) := by
  have hel : tpOp hp.pos hpN m x
      = (∑ b : Fin p, actMat (upperMat p b.val) (upperMat_det_ne_zero hp.pos b.val) m x)
        + actMat (lowerDiamondMat (N := N) hpN) (lowerDiamondMat_det_ne_zero hp.pos hpN) m x := by
    rw [tpOp, LinearMap.add_apply, upperOp_apply, ← Fin.sum_univ_eq_sum_range]
  rw [hel, map_add, map_sum]

/-- Expansion of `mk (tpOp (ρ_γ x))` into the `p` upper terms plus the lower-diamond term. -/
theorem mk_tpOp_fullModSymRep_eq_left [NeZero N] {p : ℕ} (hp : Nat.Prime p)
    (hpN : Nat.Coprime p N) (k : ℤ) (γ : ↥(Gamma0 N))
    (x : Div0 ℤ ⊗[ℤ] SymPow ℤ (k - 2).toNat) :
    𝕄.mk N k (tpOp hp.pos hpN (k - 2).toNat (fullModSymRep ℤ (k - 2).toNat (γ : SL(2, ℤ)) x))
      = (∑ b : Fin p, 𝕄.mk N k (actMat (upperMat p b.val) (upperMat_det_ne_zero hp.pos b.val)
            (k - 2).toNat (fullModSymRep ℤ (k - 2).toNat (γ : SL(2, ℤ)) x)))
        + 𝕄.mk N k (actMat (lowerDiamondMat (N := N) hpN)
            (lowerDiamondMat_det_ne_zero hp.pos hpN) (k - 2).toNat
            (fullModSymRep ℤ (k - 2).toNat (γ : SL(2, ℤ)) x)) :=
  map_tpOp_apply_eq hp hpN _ (𝕄.mk N k) _

/-- Expansion of `mk (ρ_γ (tpOp x))` into the `p` upper terms plus the lower-diamond term, via the
composite linear map `mk ∘ ρ_γ`. -/
theorem mk_tpOp_fullModSymRep_eq_right [NeZero N] {p : ℕ} (hp : Nat.Prime p)
    (hpN : Nat.Coprime p N) (k : ℤ) (γ : ↥(Gamma0 N))
    (x : Div0 ℤ ⊗[ℤ] SymPow ℤ (k - 2).toNat) :
    𝕄.mk N k (fullModSymRep ℤ (k - 2).toNat (γ : SL(2, ℤ))
        (tpOp hp.pos hpN (k - 2).toNat x))
      = (∑ b : Fin p, 𝕄.mk N k (fullModSymRep ℤ (k - 2).toNat (γ : SL(2, ℤ))
            (actMat (upperMat p b.val) (upperMat_det_ne_zero hp.pos b.val) (k - 2).toNat x)))
        + 𝕄.mk N k (fullModSymRep ℤ (k - 2).toNat (γ : SL(2, ℤ))
            (actMat (lowerDiamondMat (N := N) hpN)
              (lowerDiamondMat_det_ne_zero hp.pos hpN) (k - 2).toNat x)) :=
  map_tpOp_apply_eq hp hpN _
    ((𝕄.mk N k).comp (fullModSymRep ℤ (k - 2).toNat (γ : SL(2, ℤ)))) _

/-- The per-coset upper descent under a `Γ₀(N)` element when the index `b` is *not* the special one
(`p ∤ σ₀₀ + b·σ₁₀`): `upper(b)·γ` maps to `upper(moebius b)` up to a left `Γ₀(N)`-factor with the
same diamond image. -/
theorem mk_upperClass_gamma0_of_not_dvd [NeZero N] {p : ℕ} [Fact p.Prime] (hp : Nat.Prime p)
    (k : ℤ) (γ : ↥(Gamma0 N)) (x : Div0 ℤ ⊗[ℤ] SymPow ℤ (k - 2).toNat) (b : Fin p)
    (hA : ¬(p : ℤ) ∣ (((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 0
      + ↑b.val * ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0)) :
    𝕄.mk N k (actMat (upperMat p b.val) (upperMat_det_ne_zero hp.pos b.val) (k - 2).toNat
        (fullModSymRep ℤ (k - 2).toNat (γ : SL(2, ℤ)) x))
      = 𝕄.mk N k (fullModSymRep ℤ (k - 2).toNat (γ : SL(2, ℤ))
          (actMat (upperMat p (moebiusFin' p hp ((γ : SL(2, ℤ)) :
              Matrix (Fin 2) (Fin 2) ℤ) b).val)
            (upperMat_det_ne_zero hp.pos _) (k - 2).toNat x)) := by
  obtain ⟨τ, hmat, hτ00, hτ10, hτ11⟩ := upperMat_mul_sl hp (γ : SL(2, ℤ)) b hA
  obtain ⟨hτ_g0, hτ_eq⟩ := upperMat_mul_sl_tau_gamma0 hp γ hτ00 hτ10 hτ11
  exact mk_actMat_upperMat_comp_fullModSymRep_gamma0 hp.pos k γ ⟨τ, hτ_g0⟩ hτ_eq
    b.val (moebiusFin' p hp ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) b).val hmat x

/-- **`T_p` (`p ∤ N`) diamond commutation, case `p ∣ σ₁₀`.** -/
theorem mk_tpOp_fullModSymRep_gamma0_dvd [NeZero N] {p : ℕ} (hp : Nat.Prime p)
    (hpN : Nat.Coprime p N) (k : ℤ) (γ : ↥(Gamma0 N))
    (x : Div0 ℤ ⊗[ℤ] SymPow ℤ (k - 2).toNat)
    (hσ10 : (p : ℤ) ∣ ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0) :
    𝕄.mk N k (tpOp hp.pos hpN (k - 2).toNat (fullModSymRep ℤ (k - 2).toNat (γ : SL(2, ℤ)) x))
      = 𝕄.mk N k (fullModSymRep ℤ (k - 2).toNat (γ : SL(2, ℤ))
          (tpOp hp.pos hpN (k - 2).toNat x)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  set M := ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) with hM
  have hdet2 : M 0 0 * M 1 1 - M 0 1 * M 1 0 = 1 := by
    rw [← Matrix.det_fin_two]; exact_mod_cast (γ : SL(2, ℤ)).prop
  rw [mk_tpOp_fullModSymRep_eq_left hp hpN k γ x, mk_tpOp_fullModSymRep_eq_right hp hpN k γ x]
  -- lower term fixed
  have hLeq : 𝕄.mk N k (actMat (lowerDiamondMat (N := N) hpN)
        (lowerDiamondMat_det_ne_zero hp.pos hpN) (k - 2).toNat
        (fullModSymRep ℤ (k - 2).toNat (γ : SL(2, ℤ)) x))
      = 𝕄.mk N k (fullModSymRep ℤ (k - 2).toNat (γ : SL(2, ℤ))
          (actMat (lowerDiamondMat (N := N) hpN)
            (lowerDiamondMat_det_ne_zero hp.pos hpN) (k - 2).toNat x)) := by
    obtain ⟨γ', hγ'0, hγ'_eq, hmat⟩ := lowerDiamondMat_mul_sl_fixed_gamma0 hp hpN γ hσ10
    exact mk_actMat_coset_gamma0 _ _ k γ ⟨γ', hγ'0⟩ hγ'_eq hmat x
  rw [hLeq, add_left_inj]
  -- uppers permute via moebius
  refine Finset.sum_equiv (Equiv.ofBijective _ (moebiusFin'_bijective_of_gamma1 hp (γ : SL(2, ℤ))))
    (fun _ => ⟨fun _ => Finset.mem_univ _, fun _ => Finset.mem_univ _⟩) (fun b _ => ?_)
  rw [Equiv.ofBijective_apply]
  exact mk_upperClass_gamma0_of_not_dvd hp k γ x b
    (hb_not_dvd_topLeft_add_of_dvd_botLeft hp M hdet2 hσ10 _)

/-- **`T_p` (`p ∤ N`) diamond commutation, case `p ∤ σ₁₀`.** -/
theorem mk_tpOp_fullModSymRep_gamma0_not_dvd [NeZero N] {p : ℕ} (hp : Nat.Prime p)
    (hpN : Nat.Coprime p N) (k : ℤ) (γ : ↥(Gamma0 N))
    (x : Div0 ℤ ⊗[ℤ] SymPow ℤ (k - 2).toNat)
    (hσ10 : ¬(p : ℤ) ∣ ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0) :
    𝕄.mk N k (tpOp hp.pos hpN (k - 2).toNat (fullModSymRep ℤ (k - 2).toNat (γ : SL(2, ℤ)) x))
      = 𝕄.mk N k (fullModSymRep ℤ (k - 2).toNat (γ : SL(2, ℤ))
          (tpOp hp.pos hpN (k - 2).toNat x)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  set M := ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) with hM
  have hdet_M : M.det = 1 := by exact_mod_cast (γ : SL(2, ℤ)).prop
  rw [mk_tpOp_fullModSymRep_eq_left hp hpN k γ x, mk_tpOp_fullModSymRep_eq_right hp hpN k γ x]
  set L := 𝕄.mk N k (fullModSymRep ℤ (k - 2).toNat (γ : SL(2, ℤ))
      (actMat (lowerDiamondMat (N := N) hpN)
        (lowerDiamondMat_det_ne_zero hp.pos hpN) (k - 2).toNat x)) with hL
  set upR : Fin p → 𝕄 N k := fun b =>
    𝕄.mk N k (fullModSymRep ℤ (k - 2).toNat (γ : SL(2, ℤ))
      (actMat (upperMat p b.val) (upperMat_det_ne_zero hp.pos b.val) (k - 2).toNat x)) with hupR
  have h10_ne : ((M 1 0 : ℤ) : ZMod p) ≠ 0 :=
    fun h => hσ10 ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h)
  set b₀ : Fin p := ⟨(-(M 0 0 : ZMod p) * ((M 1 0 : ℤ) : ZMod p)⁻¹).val, ZMod.val_lt _⟩ with hb₀_def
  have hb₀ : (p : ℤ) ∣ (M 0 0 + ↑b₀.val * M 1 0) :=
    hb_dvd_topLeft_add_canonicalIndex hp M h10_ne
  have hbij : Function.Bijective (moebiusFin' p hp M) := moebiusFin'_bijective_of_gamma1 hp _
  -- lower → upper(moebius b₀)
  have hLσ_eq : 𝕄.mk N k (actMat (lowerDiamondMat (N := N) hpN)
        (lowerDiamondMat_det_ne_zero hp.pos hpN) (k - 2).toNat
        (fullModSymRep ℤ (k - 2).toNat (γ : SL(2, ℤ)) x))
      = upR (moebiusFin' p hp M b₀) := by
    obtain ⟨γL, hγL0, hγL_eq, hmatL⟩ := lowerDiamondMat_mul_sl_gamma0 hp hpN γ hσ10
    have hmoeb_b₀ : (moebiusFin' p hp M b₀).val
        = (((M 1 1 : ℤ) : ZMod p) * ((M 1 0 : ℤ) : ZMod p)⁻¹).val := by
      simp only [moebiusFin', if_pos ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hb₀)]
    show 𝕄.mk N k (actMat (lowerDiamondMat (N := N) hpN)
        (lowerDiamondMat_det_ne_zero hp.pos hpN) (k - 2).toNat
        (fullModSymRep ℤ (k - 2).toNat (γ : SL(2, ℤ)) x))
      = 𝕄.mk N k (fullModSymRep ℤ (k - 2).toNat (γ : SL(2, ℤ))
          (actMat (upperMat p (moebiusFin' p hp M b₀).val)
            (upperMat_det_ne_zero hp.pos _) (k - 2).toNat x))
    rw [hmoeb_b₀]
    exact mk_actMat_coset_gamma0 _ _ k γ ⟨γL, hγL0⟩ hγL_eq hmatL x
  rw [hLσ_eq]
  -- per-term: each upper class on the left = if special then L else upR(moebius b)
  have hper : ∀ b : Fin p,
      𝕄.mk N k (actMat (upperMat p b.val) (upperMat_det_ne_zero hp.pos b.val) (k - 2).toNat
        (fullModSymRep ℤ (k - 2).toNat (γ : SL(2, ℤ)) x))
        = if b = b₀ then L else upR (moebiusFin' p hp M b) := by
    intro b
    split_ifs with hbb
    · subst hbb
      rw [hL]
      obtain ⟨γ', hγ'0, hγ'_eq, hmat⟩ := upperMat_mul_sl_to_lower_gamma0 hp hpN γ b₀.val hb₀
      exact mk_actMat_coset_gamma0 _ _ k γ ⟨γ', hγ'0⟩ hγ'_eq hmat x
    · exact mk_upperClass_gamma0_of_not_dvd hp k γ x b
        ((hb_dvd_topLeft_add_iff_eq_canonicalIndex hp M hdet_M b₀ hb₀ b).not.mpr hbb)
  rw [show (∑ b : Fin p, 𝕄.mk N k (actMat (upperMat p b.val)
      (upperMat_det_ne_zero hp.pos b.val) (k - 2).toNat
      (fullModSymRep ℤ (k - 2).toNat (γ : SL(2, ℤ)) x)))
        = ∑ b : Fin p, if b = b₀ then L else upR (moebiusFin' p hp M b)
      from Finset.sum_congr rfl (fun b _ => hper b)]
  exact hb_sum_ite_swap_eq upR L (moebiusFin' p hp M) hbij b₀ (P := fun b => b = b₀)
    (fun _ => Iff.rfl)

/-- **`T_p` (`p ∤ N`) commutes with the diamond at the tensor level.**  For `γ ∈ Γ₀(N)` and `p ∤ N`,
the `T_p` operator `tpOp` (upper sum + diamond-twisted lower) and `fullModSymRep γ` commute modulo
`Γ₁(N)`-coinvariants: the `p + 1` coset representatives are permuted, each up to a left
`Γ₀(N)`-factor with the *same* diamond image as `γ`. -/
theorem mk_tpOp_fullModSymRep_gamma0 [NeZero N] {p : ℕ} (hp : Nat.Prime p)
    (hpN : Nat.Coprime p N) (k : ℤ) (γ : ↥(Gamma0 N))
    (x : Div0 ℤ ⊗[ℤ] SymPow ℤ (k - 2).toNat) :
    𝕄.mk N k (tpOp hp.pos hpN (k - 2).toNat (fullModSymRep ℤ (k - 2).toNat (γ : SL(2, ℤ)) x))
      = 𝕄.mk N k (fullModSymRep ℤ (k - 2).toNat (γ : SL(2, ℤ))
          (tpOp hp.pos hpN (k - 2).toNat x)) := by
  by_cases hσ10 : (p : ℤ) ∣ ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0
  · exact mk_tpOp_fullModSymRep_gamma0_dvd hp hpN k γ x hσ10
  · exact mk_tpOp_fullModSymRep_gamma0_not_dvd hp hpN k γ x hσ10

/-! ## `T_p`/`U_p` commute with the diamond operators -/

/-- The prime Hecke operator `heckeSymb_p_all p` (`T_p` at good primes, `U_p` at bad primes)
commutes with every diamond operator `⟨d⟩`. -/
theorem heckeSymb_p_all_commute_diamondSymb [NeZero N] (k : ℤ) {p : ℕ} (hp : Nat.Prime p)
    (d : (ZMod N)ˣ) :
    Commute (heckeSymb_p_all N k p hp) (diamondSymb N k d) := by
  obtain ⟨γ, hγ⟩ := Gamma0MapUnits_surjective (N := N) d
  rw [diamondSymb_eq_diamondSymbAux k d γ hγ]
  show heckeSymb_p_all N k p hp * diamondSymbAux k γ = diamondSymbAux k γ * heckeSymb_p_all N k p hp
  rw [Module.End.mul_eq_comp, Module.End.mul_eq_comp]
  refine Coinvariants.hom_ext (LinearMap.ext fun x => ?_)
  show heckeSymb_p_all N k p hp (diamondSymbAux k γ (𝕄.mk N k x))
    = diamondSymbAux k γ (heckeSymb_p_all N k p hp (𝕄.mk N k x))
  rw [diamondSymbAux_mk]
  unfold heckeSymb_p_all
  by_cases hpN : Nat.Coprime p N
  · rw [dif_pos hpN, tpSymb_mk, tpSymb_mk, diamondSymbAux_mk]
    exact mk_tpOp_fullModSymRep_gamma0 hp hpN k γ x
  · rw [dif_neg hpN, upperSymb_mk, upperSymb_mk, diamondSymbAux_mk]
    exact mk_upperOp_fullModSymRep_gamma0_divN hp hpN k γ x

/-! ## Diamond-diamond commutativity -/

/-- The diamond operators pairwise commute: `⟨d⟩ ⟨e⟩ = ⟨e⟩ ⟨d⟩`, since `(ZMod N)ˣ` is abelian. -/
theorem diamondSymb_commute (N : ℕ) [NeZero N] (k : ℤ) (d e : (ZMod N)ˣ) :
    Commute (diamondSymb N k d) (diamondSymb N k e) := by
  show diamondSymb N k d * diamondSymb N k e = diamondSymb N k e * diamondSymb N k d
  rw [Module.End.mul_eq_comp, Module.End.mul_eq_comp, ← diamondSymb_mul, ← diamondSymb_mul,
    mul_comm]

/-- The extended diamond `diamondSymb_n n` (`⟨n⟩` when `(n, N) = 1`, else `0`) commutes with every
diamond operator. -/
theorem diamondSymb_n_commute_diamondSymb [NeZero N] (k : ℤ) (n : ℕ) (d : (ZMod N)ˣ) :
    Commute (diamondSymb_n N k n) (diamondSymb N k d) := by
  unfold diamondSymb_n
  by_cases h : Nat.Coprime n N
  · rw [dif_pos h]; exact diamondSymb_commute N k _ d
  · rw [dif_neg h]; exact Commute.zero_left _

/-- The prime Hecke operator commutes with every extended diamond `diamondSymb_n`. -/
theorem heckeSymb_p_all_commute_diamondSymb_n [NeZero N] (k : ℤ) {p : ℕ} (hp : Nat.Prime p)
    (n : ℕ) : Commute (heckeSymb_p_all N k p hp) (diamondSymb_n N k n) := by
  unfold diamondSymb_n
  by_cases h : Nat.Coprime n N
  · rw [dif_pos h]; exact heckeSymb_p_all_commute_diamondSymb k hp _
  · rw [dif_neg h]; exact Commute.zero_right _

/-- The extended diamonds `diamondSymb_n` pairwise commute. -/
theorem diamondSymb_n_commute [NeZero N] (k : ℤ) (m n : ℕ) :
    Commute (diamondSymb_n N k m) (diamondSymb_n N k n) := by
  unfold diamondSymb_n
  by_cases hm : Nat.Coprime m N
  · rw [dif_pos hm]; exact diamondSymb_n_commute_diamondSymb k n _ |>.symm
  · rw [dif_neg hm]; exact Commute.zero_left _

/-! ## Hecke-Hecke commutativity: the cross-prime atom -/

/-- The integer coset-matrix product identity: `upperMat p b · upperMat q c = upperMat (pq)
(c + b q)`. -/
theorem upperMat_mul_upperMat (p q b c : ℕ) :
    upperMat p b * upperMat q c = upperMat (p * q) (c + b * q) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [upperMat, Matrix.mul_apply, Fin.sum_univ_two]

/-- Composition distributes over a finite sum of linear maps on the left. -/
theorem linearMap_sum_comp {M₀ : Type*} [AddCommGroup M₀] [Module ℤ M₀] (g : M₀ →ₗ[ℤ] M₀)
    (s : Finset ℕ) (f : ℕ → M₀ →ₗ[ℤ] M₀) : (∑ i ∈ s, f i) ∘ₗ g = ∑ i ∈ s, (f i ∘ₗ g) := by
  ext x; simp [LinearMap.sum_apply, Finset.sum_apply]

/-- Composition distributes over a finite sum of linear maps on the right. -/
theorem linearMap_comp_sum {M₀ : Type*} [AddCommGroup M₀] [Module ℤ M₀] (g : M₀ →ₗ[ℤ] M₀)
    (s : Finset ℕ) (f : ℕ → M₀ →ₗ[ℤ] M₀) : g ∘ₗ (∑ i ∈ s, f i) = ∑ i ∈ s, (g ∘ₗ f i) := by
  ext x; simp [LinearMap.sum_apply, map_sum]

/-- The CRT bijection on `Fin`-products: `∑_{b<p} ∑_{c<q} f (c + b q) = ∑_{j < pq} f j`. -/
theorem crt_fin_sum {α : Type*} [AddCommMonoid α] {p q : ℕ} (hq : 0 < q) (f : ℕ → α) :
    (∑ b ∈ Finset.range p, ∑ c ∈ Finset.range q, f (c + b * q)) =
      ∑ j ∈ Finset.range (p * q), f j := by
  rw [← Finset.sum_product']
  refine Finset.sum_nbij (fun bc => bc.2 + bc.1 * q) ?_ ?_ ?_ ?_
  · intro ⟨b, c⟩ hbc
    simp only [Finset.mem_product, Finset.mem_range] at hbc ⊢
    obtain ⟨hb, hc⟩ := hbc; nlinarith
  · intro ⟨b₁, c₁⟩ hbc₁ ⟨b₂, c₂⟩ hbc₂ h
    simp only [Finset.mem_coe, Finset.mem_product, Finset.mem_range] at hbc₁ hbc₂
    simp only at h
    have hc₁ : c₁ < q := hbc₁.2
    have hc₂ : c₂ < q := hbc₂.2
    have hbeq : b₁ = b₂ := by
      rcases Nat.lt_trichotomy b₁ b₂ with hlt | heq | hgt
      · exfalso; nlinarith
      · exact heq
      · exfalso; nlinarith
    subst hbeq; simp only [Prod.mk.injEq, true_and]; omega
  · intro j hj
    simp only [Set.mem_image, Finset.mem_coe, Finset.mem_product, Finset.mem_range] at hj ⊢
    refine ⟨(j / q, j % q), ⟨Nat.div_lt_of_lt_mul (mul_comm p q ▸ hj), Nat.mod_lt j hq⟩, ?_⟩
    show j % q + j / q * q = j
    rw [mul_comm]; exact Nat.mod_add_div j q
  · intro _ _; rfl

/-- **Cross-prime `U`-operator commutativity (tensor level).**  For positive `p, q`, the
upper-triangular sum operators reindex (by the CRT) to the single sum `∑_{j < pq} actMat (upperMat
(pq) j)`. -/
theorem upperOp_comp_upperOp {p q : ℕ} (hp : 0 < p) (hq : 0 < q) (m : ℕ) :
    upperOp p hp m ∘ₗ upperOp q hq m
      = ∑ j ∈ Finset.range (p * q), actMat (upperMat (p * q) j)
          (upperMat_det_ne_zero (mul_pos hp hq) j) m := by
  rw [upperOp, linearMap_sum_comp]
  have key : ∀ b ∈ Finset.range p,
      (actMat (upperMat p b) (upperMat_det_ne_zero hp b) m) ∘ₗ upperOp q hq m
        = ∑ c ∈ Finset.range q, actMat (upperMat (p * q) (c + b * q))
            (upperMat_det_ne_zero (mul_pos hp hq) (c + b * q)) m := by
    intro b _
    rw [upperOp, linearMap_comp_sum]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    rw [← actMat_mul, actMat_congr (upperMat_mul_upperMat p q b c) _ _ m]
  rw [Finset.sum_congr rfl key, ← crt_fin_sum hq
    (fun j => actMat (upperMat (p * q) j) (upperMat_det_ne_zero (mul_pos hp hq) j) m)]

/-- Element-level CRT for the `U`-operators: `upperOp p (upperOp q x)` equals the symmetric sum
`∑_{j < pq} actMat (upperMat (pq) j) x`. -/
theorem upperOp_apply_upperOp [NeZero N] {p q : ℕ} (hp : 0 < p) (hq : 0 < q) (m : ℕ)
    (x : Div0 ℤ ⊗[ℤ] SymPow ℤ m) :
    upperOp p hp m (upperOp q hq m x)
      = ∑ j ∈ Finset.range (p * q), actMat (upperMat (p * q) j)
          (upperMat_det_ne_zero (mul_pos hp hq) j) m x := by
  have := LinearMap.congr_fun (upperOp_comp_upperOp hp hq m) x
  rwa [LinearMap.comp_apply, LinearMap.coe_sum, Finset.sum_apply] at this

/-- **`U_p`/`U_q` commute** (`p, q ∣ N`).  Both compositions reindex by the CRT to the same sum of
upper Heilbronn classes of determinant `pq`. -/
theorem upperSymb_commute [NeZero N] (k : ℤ) {p q : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hpN : ¬Nat.Coprime p N) (hqN : ¬Nat.Coprime q N) :
    Commute (upperSymb hp hpN k) (upperSymb hq hqN k) := by
  show upperSymb hp hpN k * upperSymb hq hqN k = upperSymb hq hqN k * upperSymb hp hpN k
  rw [Module.End.mul_eq_comp, Module.End.mul_eq_comp]
  refine Coinvariants.hom_ext (LinearMap.ext fun x => ?_)
  show upperSymb hp hpN k (upperSymb hq hqN k (𝕄.mk N k x))
    = upperSymb hq hqN k (upperSymb hp hpN k (𝕄.mk N k x))
  rw [upperSymb_mk, upperSymb_mk, upperSymb_mk, upperSymb_mk,
    upperOp_apply_upperOp (N := N) hp.pos hq.pos, upperOp_apply_upperOp (N := N) hq.pos hp.pos,
    _root_.map_sum (𝕄.mk N k), _root_.map_sum (𝕄.mk N k)]
  -- the two `∑` differ only by `pq ↔ qp`; reindex by the identity
  refine Finset.sum_nbij' id id (fun j hj => by simp_all [mul_comm q p])
    (fun j hj => by simp_all [mul_comm q p]) (fun _ _ => rfl) (fun _ _ => rfl) (fun j _ => ?_)
  show 𝕄.mk N k (actMat (upperMat (p * q) j) (upperMat_det_ne_zero (mul_pos hp.pos hq.pos) j)
        (k - 2).toNat x)
    = 𝕄.mk N k (actMat (upperMat (q * p) j) (upperMat_det_ne_zero (mul_pos hq.pos hp.pos) j)
        (k - 2).toNat x)
  exact congrArg (𝕄.mk N k) (LinearMap.congr_fun
    (actMat_congr (by rw [mul_comm p q]) (upperMat_det_ne_zero (mul_pos hp.pos hq.pos) j)
      (upperMat_det_ne_zero (mul_pos hq.pos hp.pos) j) (k - 2).toNat) x)

/-! ## Cross-prime atom with a good prime: the shift identity and four-block reorganisation

For a good prime the operator `tpSymb` carries the diamond-twisted lower Heilbronn representative.
The cross-prime products `tpSymb p ∘ tpSymb q` (and the mixed `tpSymb`/`upperSymb` products) are
reorganised by:
* the **integer shift identity** `lowerMat q · upperMat p b = shift(qb/p) · (upperMat p (qb%p) ·
  lowerMat q)` with `shift ∈ Γ₁(N)` (`lowerMat_mul_upperMat`), giving the cross-term reindexing
  `b ↦ qb%p`;
* the diamonds pulled out via the (already proven) `mk_tpOp_fullModSymRep_gamma0`;
* the bare lowers commuting (`lowerMat_mul_comm`) and the diamonds commuting modulo `Γ₁(N)`. -/

/-- The integer shift matrix `[[1, m], [0, 1]]` as an `SL(2, ℤ)` element. -/
noncomputable def shiftSL (m : ℤ) : SL(2, ℤ) :=
  ⟨!![1, m; 0, 1], by simp [Matrix.det_fin_two_of]⟩

/-- The shift matrix lies in `Γ₁(N)` (it is unipotent upper-triangular). -/
theorem shiftSL_mem_Gamma1 (m : ℤ) : (shiftSL m : SL(2, ℤ)) ∈ Gamma1 N := by
  rw [Gamma1_mem]; refine ⟨?_, ?_, ?_⟩ <;> simp [shiftSL]

/-- **Shift identity (integer level).** For the bare lower matrix of `q` and the upper matrix of
`p` at index `b`: `lowerMat q · upperMat p b = shift(q·b/p) · (upperMat p (q·b%p) · lowerMat q)`.
The `(0,1)` entry is the load-bearing one (`q·b = q·b%p + (q·b/p)·p`). -/
theorem lowerMat_mul_upperMat (p q b : ℕ) :
    lowerMat q * upperMat p b
      = (shiftSL (↑(q * b / p)) : Matrix (Fin 2) (Fin 2) ℤ)
          * (upperMat p (q * b % p) * lowerMat q) := by
  have h3 : (q : ℤ) * ↑b = (↑q * ↑b) % ↑p + (↑q * ↑b) / ↑p * ↑p := by
    have := Int.emod_add_mul_ediv ((q : ℤ) * b) p; linarith
  have e00 : (lowerMat q * upperMat p b) 0 0
      = ((shiftSL (↑(q * b / p)) : Matrix (Fin 2) (Fin 2) ℤ)
          * (upperMat p (q * b % p) * lowerMat q)) 0 0 := by
    simp [shiftSL, lowerMat, upperMat, Matrix.mul_apply, Fin.sum_univ_two]
  have e01 : (lowerMat q * upperMat p b) 0 1
      = ((shiftSL (↑(q * b / p)) : Matrix (Fin 2) (Fin 2) ℤ)
          * (upperMat p (q * b % p) * lowerMat q)) 0 1 := by
    simp only [shiftSL, lowerMat, upperMat, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.SpecialLinearGroup.coe_mk, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.of_apply,
      Matrix.cons_val']
    push_cast
    linarith [h3]
  have e10 : (lowerMat q * upperMat p b) 1 0
      = ((shiftSL (↑(q * b / p)) : Matrix (Fin 2) (Fin 2) ℤ)
          * (upperMat p (q * b % p) * lowerMat q)) 1 0 := by
    simp [shiftSL, lowerMat, upperMat, Matrix.mul_apply, Fin.sum_univ_two]
  have e11 : (lowerMat q * upperMat p b) 1 1
      = ((shiftSL (↑(q * b / p)) : Matrix (Fin 2) (Fin 2) ℤ)
          * (upperMat p (q * b % p) * lowerMat q)) 1 1 := by
    simp [shiftSL, lowerMat, upperMat, Matrix.mul_apply, Fin.sum_univ_two]
  ext i j; fin_cases i <;> fin_cases j
  · exact e00
  · exact e01
  · exact e10
  · exact e11

/-- The bare lower coset matrices commute: `lowerMat p · lowerMat q = lowerMat q · lowerMat p`
(they are diagonal). -/
theorem lowerMat_mul_comm (p q : ℕ) : lowerMat p * lowerMat q = lowerMat q * lowerMat p := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [lowerMat, Matrix.mul_apply, Fin.sum_univ_two, mul_comm]

/-- `actMat (lowerDiamondMat r) = ρ_{γ_r} ∘ actMat (lowerMat r)`: split the diamond representative
`γ_r` (an `SL(2, ℤ)` element) off the diamond-twisted lower coset matrix. -/
theorem actMat_lowerDiamondMat_eq [NeZero N] {r : ℕ} (hr : 0 < r) (hrN : Nat.Coprime r N) (m : ℕ)
    (x : Div0 ℤ ⊗[ℤ] SymPow ℤ m) :
    actMat (lowerDiamondMat (N := N) hrN) (lowerDiamondMat_det_ne_zero hr hrN) m x
      = fullModSymRep ℤ m (diamondRep (N := N) hrN : SL(2, ℤ))
          (actMat (lowerMat r) (lowerMat_det_ne_zero hr) m x) := by
  have hmat : lowerDiamondMat (N := N) hrN
      = ((diamondRep (N := N) hrN : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * lowerMat r := rfl
  rw [actMat_congr hmat (lowerDiamondMat_det_ne_zero hr hrN)
    (det_mul_ne_zero (sl_det_ne_zero _) (lowerMat_det_ne_zero hr)) m, actMat_mul,
    LinearMap.comp_apply]
  exact LinearMap.congr_fun (actMat_eq_fullModSymRep (diamondRep (N := N) hrN : SL(2, ℤ)) m)
    (actMat (lowerMat r) (lowerMat_det_ne_zero hr) m x)

/-- **Per-term shift descent.** For primes `p, q` and `γ ∈ Γ₀(N)`, the `mk ∘ ρ_γ` class of
`L_p ∘ U_{q,c}` (bare lower of `p`, upper of `q` at index `c`) equals that of `U_{q, pc%q} ∘ L_p`:
the shift factor lies in `Γ₁(N)` and is absorbed by `mk ∘ ρ_γ` (via
`mk_fullModSymRep_gamma0_comp_modSymRep`). -/
theorem mk_gamma0_lowerMat_upperMat_term [NeZero N] {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    (k : ℤ) (γ : ↥(Gamma0 N)) (c : ℕ) (x : Div0 ℤ ⊗[ℤ] SymPow ℤ (k - 2).toNat) :
    𝕄.mk N k (fullModSymRep ℤ (k - 2).toNat (γ : SL(2, ℤ))
        (actMat (lowerMat p) (lowerMat_det_ne_zero hp) (k - 2).toNat
          (actMat (upperMat q c) (upperMat_det_ne_zero hq c) (k - 2).toNat x)))
      = 𝕄.mk N k (fullModSymRep ℤ (k - 2).toNat (γ : SL(2, ℤ))
          (actMat (upperMat q (p * c % q)) (upperMat_det_ne_zero hq _) (k - 2).toNat
            (actMat (lowerMat p) (lowerMat_det_ne_zero hp) (k - 2).toNat x))) := by
  -- combine the two `actMat`s on the LHS into a single matrix product, then apply the shift id
  rw [← LinearMap.comp_apply (actMat (lowerMat p) _ _), ← actMat_mul,
    actMat_congr (lowerMat_mul_upperMat q p c) _
      (det_mul_ne_zero (sl_det_ne_zero _)
        (det_mul_ne_zero (upperMat_det_ne_zero hq _) (lowerMat_det_ne_zero hp))) (k - 2).toNat,
    actMat_mul, LinearMap.comp_apply, actMat_mul, LinearMap.comp_apply,
    actMat_eq_fullModSymRep (shiftSL _) (k - 2).toNat]
  -- absorb the shift (∈ Γ₁) through `mk ∘ ρ_γ`
  · exact LinearMap.congr_fun
      (mk_fullModSymRep_gamma0_comp_modSymRep (N := N) k γ ⟨shiftSL _, shiftSL_mem_Gamma1 _⟩)
      (actMat (upperMat q (p * c % q)) (upperMat_det_ne_zero hq _) (k - 2).toNat
        (actMat (lowerMat p) (lowerMat_det_ne_zero hp) (k - 2).toNat x))
  · exact sl_det_ne_zero _
  · exact det_mul_ne_zero (upperMat_det_ne_zero hq _) (lowerMat_det_ne_zero hp)

/-- **Cross-prime shift-reindex (`mk ∘ ρ_γ` level).** For distinct primes `p, q` (`Coprime p q`)
and `γ ∈ Γ₀(N)`, the bare lower of `p` commutes with the upper-sum operator of `q` modulo `Γ₁(N)`
(inside `ρ_γ`): `mk(ρ_γ(L_p (U_q x))) = mk(ρ_γ(U_q (L_p x)))`.  The `q` coset representatives are
reindexed by the bijection `c ↦ p·c%q` on `Fin q`. -/
theorem mk_gamma0_lowerMat_upperOp_comm [NeZero N] {p q : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hpq : Nat.Coprime p q) (k : ℤ) (γ : ↥(Gamma0 N))
    (x : Div0 ℤ ⊗[ℤ] SymPow ℤ (k - 2).toNat) :
    𝕄.mk N k (fullModSymRep ℤ (k - 2).toNat (γ : SL(2, ℤ))
        (actMat (lowerMat p) (lowerMat_det_ne_zero hp.pos) (k - 2).toNat
          (upperOp q hq.pos (k - 2).toNat x)))
      = 𝕄.mk N k (fullModSymRep ℤ (k - 2).toNat (γ : SL(2, ℤ))
          (upperOp q hq.pos (k - 2).toNat
            (actMat (lowerMat p) (lowerMat_det_ne_zero hp.pos) (k - 2).toNat x))) := by
  -- expand both `upperOp q` sums and distribute `mk ∘ ρ_γ ∘ L_p` (LHS) / `mk ∘ ρ_γ` (RHS)
  set Lp := fun y => actMat (lowerMat p) (lowerMat_det_ne_zero hp.pos) (k - 2).toNat y with hLp
  have hLHS : 𝕄.mk N k (fullModSymRep ℤ (k - 2).toNat (γ : SL(2, ℤ)) (Lp
        (upperOp q hq.pos (k - 2).toNat x)))
      = ∑ c ∈ Finset.range q, 𝕄.mk N k (fullModSymRep ℤ (k - 2).toNat (γ : SL(2, ℤ))
          (Lp (actMat (upperMat q c) (upperMat_det_ne_zero hq.pos c) (k - 2).toNat x))) := by
    rw [upperOp_apply]
    exact _root_.map_sum (((𝕄.mk N k).comp (fullModSymRep ℤ (k - 2).toNat (γ : SL(2, ℤ)))).comp
      (actMat (lowerMat p) (lowerMat_det_ne_zero hp.pos) (k - 2).toNat)) _ _
  have hRHS : 𝕄.mk N k (fullModSymRep ℤ (k - 2).toNat (γ : SL(2, ℤ))
        (upperOp q hq.pos (k - 2).toNat (Lp x)))
      = ∑ c ∈ Finset.range q, 𝕄.mk N k (fullModSymRep ℤ (k - 2).toNat (γ : SL(2, ℤ))
          (actMat (upperMat q c) (upperMat_det_ne_zero hq.pos c) (k - 2).toNat (Lp x))) := by
    rw [upperOp_apply]
    exact _root_.map_sum ((𝕄.mk N k).comp (fullModSymRep ℤ (k - 2).toNat (γ : SL(2, ℤ)))) _ _
  rw [hLHS, hRHS]
  -- per term: `c ↦ p*c%q` reindex bijection on `Finset.range q`
  haveI : NeZero q := ⟨hq.ne_zero⟩
  have hqp : Nat.Coprime q p := hpq.symm
  refine Finset.sum_nbij (fun c ↦ p * c % q)
    (fun c _ ↦ Finset.mem_range.mpr (Nat.mod_lt _ hq.pos))
    (fun c₁ hc₁ c₂ hc₂ he ↦ ?_) (fun c hc ↦ ?_) (fun c _ ↦ ?_)
  · simp only [Finset.mem_coe, Finset.mem_range] at hc₁ hc₂
    simp only at he
    have hmod : p * c₁ ≡ p * c₂ [MOD q] := by rwa [Nat.ModEq]
    have hcc : c₁ ≡ c₂ [MOD q] := Nat.ModEq.cancel_left_of_coprime hqp hmod
    rwa [Nat.ModEq, Nat.mod_eq_of_lt hc₁, Nat.mod_eq_of_lt hc₂] at hcc
  · -- surjectivity: every `c < q` is hit
    simp only [Finset.mem_coe, Finset.mem_range, Set.mem_image] at hc ⊢
    have hp_unit : IsUnit ((p : ZMod q)) := (ZMod.isUnit_iff_coprime p q).mpr hpq
    obtain ⟨u, hu⟩ := hp_unit
    set c_zmod := u⁻¹ * (c : ZMod q) with hc_zmod
    refine ⟨c_zmod.val, ⟨ZMod.val_lt _, ?_⟩⟩
    have key : (p : ZMod q) * c_zmod = (c : ZMod q) := by
      simp only [hc_zmod, ← hu, Units.mul_inv_cancel_left]
    rw [show p * c_zmod.val % q = (((p * c_zmod.val : ℕ) : ZMod q)).val from
      (ZMod.val_natCast q _).symm]
    simp only [Nat.cast_mul, ZMod.natCast_zmod_val]
    rw [key, ZMod.val_cast_of_lt hc]
  · -- the per-term equality (shift descent), with `c ↦ p*c%q`
    exact mk_gamma0_lowerMat_upperMat_term hp.pos hq.pos k γ c x

/-- Pointwise unfolding of `tpOp`: the upper sum plus the diamond-twisted bare lower. -/
theorem tpOp_apply [NeZero N] {p : ℕ} (hp : 0 < p) (hpN : Nat.Coprime p N) (m : ℕ)
    (y : Div0 ℤ ⊗[ℤ] SymPow ℤ m) :
    tpOp hp hpN m y = upperOp p hp m y
      + actMat (lowerDiamondMat (N := N) hpN) (lowerDiamondMat_det_ne_zero hp hpN) m y := by
  rw [tpOp, LinearMap.add_apply]

/-- **Four-block expansion** of `mk(tpOp p (tpOp q x))` for good primes `p, q`: into the
upper-upper block `mk(U_p (U_q x))`, the two cross blocks `mk(ρ_{γp}(L_p (U_q x)))` and
`mk(ρ_{γq}(U_p (L_q x)))`, and the lower-lower block `mk(ρ_{γq}(ρ_{γp}(L_p (L_q x))))` (the inner
diamond pulled out via `mk_tpOp_fullModSymRep_gamma0`). -/
theorem mk_tpOp_tpOp_expand [NeZero N] {p q : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hpN : Nat.Coprime p N) (hqN : Nat.Coprime q N) (k : ℤ)
    (x : Div0 ℤ ⊗[ℤ] SymPow ℤ (k - 2).toNat) :
    𝕄.mk N k (tpOp hp.pos hpN (k - 2).toNat (tpOp hq.pos hqN (k - 2).toNat x))
      = 𝕄.mk N k (upperOp p hp.pos (k - 2).toNat (upperOp q hq.pos (k - 2).toNat x))
        + 𝕄.mk N k (fullModSymRep ℤ (k - 2).toNat (diamondRep (N := N) hpN : SL(2, ℤ))
            (actMat (lowerMat p) (lowerMat_det_ne_zero hp.pos) (k - 2).toNat
              (upperOp q hq.pos (k - 2).toNat x)))
        + 𝕄.mk N k (fullModSymRep ℤ (k - 2).toNat (diamondRep (N := N) hqN : SL(2, ℤ))
            (upperOp p hp.pos (k - 2).toNat
              (actMat (lowerMat q) (lowerMat_det_ne_zero hq.pos) (k - 2).toNat x)))
        + 𝕄.mk N k (fullModSymRep ℤ (k - 2).toNat (diamondRep (N := N) hqN : SL(2, ℤ))
            (fullModSymRep ℤ (k - 2).toNat (diamondRep (N := N) hpN : SL(2, ℤ))
              (actMat (lowerMat p) (lowerMat_det_ne_zero hp.pos) (k - 2).toNat
                (actMat (lowerMat q) (lowerMat_det_ne_zero hq.pos) (k - 2).toNat x)))) := by
  -- helper: `mk(tpOp p y) = mk(U_p y) + mk(ρ_{γp}(L_p y))`
  -- (push `mk` in to dodge the tensor diamond)
  have hmkp : ∀ (y : Div0 ℤ ⊗[ℤ] SymPow ℤ (k - 2).toNat),
      𝕄.mk N k (tpOp hp.pos hpN (k - 2).toNat y)
        = 𝕄.mk N k (upperOp p hp.pos (k - 2).toNat y)
          + 𝕄.mk N k (fullModSymRep ℤ (k - 2).toNat (diamondRep (N := N) hpN : SL(2, ℤ))
              (actMat (lowerMat p) (lowerMat_det_ne_zero hp.pos) (k - 2).toNat y)) :=
    fun y => by rw [tpOp_apply, map_add, actMat_lowerDiamondMat_eq hp.pos hpN]
  -- `mk(tpOp p (tpOp q x))`: expand the inner `tpOp q x` and apply the composite map `mk ∘ tpOp p`
  have hstep1 : 𝕄.mk N k (tpOp hp.pos hpN (k - 2).toNat (tpOp hq.pos hqN (k - 2).toNat x))
      = 𝕄.mk N k (tpOp hp.pos hpN (k - 2).toNat (upperOp q hq.pos (k - 2).toNat x))
        + 𝕄.mk N k (tpOp hp.pos hpN (k - 2).toNat
            (actMat (lowerDiamondMat (N := N) hqN) (lowerDiamondMat_det_ne_zero hq.pos hqN)
              (k - 2).toNat x)) := by
    rw [tpOp_apply (p := q)]
    exact _root_.map_add ((𝕄.mk N k).comp (tpOp hp.pos hpN (k - 2).toNat)) _ _
  rw [hstep1]
  -- first summand `mk(tpOp p (U_q x))` = A + B
  rw [hmkp (upperOp q hq.pos (k - 2).toNat x)]
  -- second summand: convert `actMat(lowerDiamond_q) x = ρ_{γq}(L_q x)`, then pull out the diamond
  rw [actMat_lowerDiamondMat_eq hq.pos hqN,
    mk_tpOp_fullModSymRep_gamma0 hp hpN k (diamondRep (N := N) hqN)
      (actMat (lowerMat q) (lowerMat_det_ne_zero hq.pos) (k - 2).toNat x)]
  -- expand `tpOp p (L_q x)` under `ρ_{γq}` via the composite map `mk ∘ ρ_{γq}` (clean `+` in `𝕄`)
  have hstep2 : 𝕄.mk N k (fullModSymRep ℤ (k - 2).toNat (diamondRep (N := N) hqN : SL(2, ℤ))
        (tpOp hp.pos hpN (k - 2).toNat
          (actMat (lowerMat q) (lowerMat_det_ne_zero hq.pos) (k - 2).toNat x)))
      = 𝕄.mk N k (fullModSymRep ℤ (k - 2).toNat (diamondRep (N := N) hqN : SL(2, ℤ))
          (upperOp p hp.pos (k - 2).toNat
            (actMat (lowerMat q) (lowerMat_det_ne_zero hq.pos) (k - 2).toNat x)))
        + 𝕄.mk N k (fullModSymRep ℤ (k - 2).toNat (diamondRep (N := N) hqN : SL(2, ℤ))
            (actMat (lowerDiamondMat (N := N) hpN) (lowerDiamondMat_det_ne_zero hp.pos hpN)
              (k - 2).toNat
              (actMat (lowerMat q) (lowerMat_det_ne_zero hq.pos) (k - 2).toNat x))) := by
    rw [tpOp_apply]
    exact _root_.map_add ((𝕄.mk N k).comp
      (fullModSymRep ℤ (k - 2).toNat (diamondRep (N := N) hqN : SL(2, ℤ)))) _ _
  rw [hstep2, actMat_lowerDiamondMat_eq hp.pos hpN]
  abel

/-- **Upper-upper block is symmetric.** `mk(U_p (U_q x)) = mk(U_q (U_p x))` (both reindex by the CRT
to `∑_{j < pq}`). -/
theorem mk_upperOp_upperOp_comm [NeZero N] {p q : ℕ} (hp : 0 < p) (hq : 0 < q) (k : ℤ)
    (x : Div0 ℤ ⊗[ℤ] SymPow ℤ (k - 2).toNat) :
    𝕄.mk N k (upperOp p hp (k - 2).toNat (upperOp q hq (k - 2).toNat x))
      = 𝕄.mk N k (upperOp q hq (k - 2).toNat (upperOp p hp (k - 2).toNat x)) := by
  rw [upperOp_apply_upperOp (N := N) hp hq, upperOp_apply_upperOp (N := N) hq hp,
    _root_.map_sum (𝕄.mk N k), _root_.map_sum (𝕄.mk N k)]
  refine Finset.sum_nbij' id id (fun j hj => by simp_all [mul_comm q p])
    (fun j hj => by simp_all [mul_comm q p]) (fun _ _ => rfl) (fun _ _ => rfl) (fun j _ => ?_)
  exact congrArg (𝕄.mk N k) (LinearMap.congr_fun
    (actMat_congr (by rw [mul_comm p q]) (upperMat_det_ne_zero (mul_pos hp hq) j)
      (upperMat_det_ne_zero (mul_pos hq hp) j) (k - 2).toNat) x)

/-- **Lower-lower block is symmetric.** `mk(ρ_{γq}(ρ_{γp}(L_p (L_q x)))) = mk(ρ_{γp}(ρ_{γq}(L_q (L_p
x))))`: the bare lowers commute (`lowerMat_mul_comm`) and the diamonds commute modulo `Γ₁(N)`
(`(ZMod N)ˣ` is abelian). -/
theorem mk_lowerDiamond_lowerDiamond_comm [NeZero N] {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    (hpN : Nat.Coprime p N) (hqN : Nat.Coprime q N) (k : ℤ)
    (x : Div0 ℤ ⊗[ℤ] SymPow ℤ (k - 2).toNat) :
    𝕄.mk N k (fullModSymRep ℤ (k - 2).toNat (diamondRep (N := N) hqN : SL(2, ℤ))
        (fullModSymRep ℤ (k - 2).toNat (diamondRep (N := N) hpN : SL(2, ℤ))
          (actMat (lowerMat p) (lowerMat_det_ne_zero hp) (k - 2).toNat
            (actMat (lowerMat q) (lowerMat_det_ne_zero hq) (k - 2).toNat x))))
      = 𝕄.mk N k (fullModSymRep ℤ (k - 2).toNat (diamondRep (N := N) hpN : SL(2, ℤ))
          (fullModSymRep ℤ (k - 2).toNat (diamondRep (N := N) hqN : SL(2, ℤ))
            (actMat (lowerMat q) (lowerMat_det_ne_zero hq) (k - 2).toNat
              (actMat (lowerMat p) (lowerMat_det_ne_zero hp) (k - 2).toNat x)))) := by
  -- rewrite each side into `mk(ρ_{γ·γ'}(actMat(lowerMat q * lowerMat p) x))` form
  have hcombine : ∀ (γ γ' : ↥(Gamma0 N)) (A B : Matrix (Fin 2) (Fin 2) ℤ) (hA : A.det ≠ 0)
      (hB : B.det ≠ 0) (hAB : A * B = lowerMat q * lowerMat p),
      𝕄.mk N k (fullModSymRep ℤ (k - 2).toNat (γ : SL(2, ℤ))
          (fullModSymRep ℤ (k - 2).toNat (γ' : SL(2, ℤ))
            (actMat A hA (k - 2).toNat (actMat B hB (k - 2).toNat x))))
        = 𝕄.mk N k (fullModSymRep ℤ (k - 2).toNat ((γ * γ' : ↥(Gamma0 N)) : SL(2, ℤ))
            (actMat (lowerMat q * lowerMat p)
              (det_mul_ne_zero (lowerMat_det_ne_zero hq) (lowerMat_det_ne_zero hp)) (k - 2).toNat
              x)) := by
    intro γ γ' A B hA hB hAB
    rw [← LinearMap.comp_apply (actMat A hA _), ← actMat_mul,
      actMat_congr hAB (det_mul_ne_zero hA hB)
        (det_mul_ne_zero (lowerMat_det_ne_zero hq) (lowerMat_det_ne_zero hp)) (k - 2).toNat,
      ← Module.End.mul_apply (fullModSymRep ℤ (k - 2).toNat (γ : SL(2, ℤ))), ← map_mul]
    rfl
  rw [hcombine (diamondRep (N := N) hqN) (diamondRep (N := N) hpN) (lowerMat p) (lowerMat q)
    (lowerMat_det_ne_zero hp) (lowerMat_det_ne_zero hq) (lowerMat_mul_comm p q),
    hcombine (diamondRep (N := N) hpN) (diamondRep (N := N) hqN) (lowerMat q) (lowerMat p)
    (lowerMat_det_ne_zero hq) (lowerMat_det_ne_zero hp) rfl]
  -- now both sides have the same bare-lower matrix; diamonds commute (abelian image)
  refine mk_fullModSymRep_eq_of_gamma0MapUnits_eq k
    (diamondRep (N := N) hpN * diamondRep (N := N) hqN)
    (diamondRep (N := N) hqN * diamondRep (N := N) hpN) ?_ _
  rw [map_mul, map_mul, mul_comm]

/-- **Good-good cross-prime Hecke commutativity.** `tpSymb p` and `tpSymb q` commute for good
primes `p, q`.  For `p = q` they coincide; for distinct primes the four-block reorganisation
matches the upper-upper, cross, and lower-lower blocks. -/
theorem tpSymb_commute [NeZero N] (k : ℤ) {p q : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hpN : Nat.Coprime p N) (hqN : Nat.Coprime q N) :
    Commute (tpSymb hp hpN k) (tpSymb hq hqN k) := by
  rcases eq_or_ne p q with hpq | hpq
  · subst hpq
    -- `hp = hq` and `hpN = hqN` are equalities of `Prop`-witnesses, so the operators coincide
    have heq : tpSymb hp hpN k = tpSymb hq hqN k := rfl
    rw [heq]
  · have hpqc : Nat.Coprime p q := (Nat.coprime_primes hp hq).mpr hpq
    show tpSymb hp hpN k * tpSymb hq hqN k = tpSymb hq hqN k * tpSymb hp hpN k
    rw [Module.End.mul_eq_comp, Module.End.mul_eq_comp]
    refine Coinvariants.hom_ext (LinearMap.ext fun x => ?_)
    show tpSymb hp hpN k (tpSymb hq hqN k (𝕄.mk N k x))
      = tpSymb hq hqN k (tpSymb hp hpN k (𝕄.mk N k x))
    rw [tpSymb_mk, tpSymb_mk, tpSymb_mk, tpSymb_mk,
      mk_tpOp_tpOp_expand hp hq hpN hqN, mk_tpOp_tpOp_expand hq hp hqN hpN,
      mk_upperOp_upperOp_comm hp.pos hq.pos,
      mk_gamma0_lowerMat_upperOp_comm hp hq hpqc k (diamondRep (N := N) hpN),
      ← mk_gamma0_lowerMat_upperOp_comm hq hp hpqc.symm k (diamondRep (N := N) hqN),
      mk_lowerDiamond_lowerDiamond_comm hp.pos hq.pos hpN hqN]
    abel

/-- **Mixed cross-prime Hecke commutativity.** For a good prime `p` (`Coprime p N`) and a bad prime
`q` (`q ∣ N`), `tpSymb p` and `upperSymb q` commute.  The upper-upper block is symmetric, and the
single cross/lower term matches via the shift-reindex `mk_gamma0_lowerMat_upperOp_comm` after
pulling
`U_q` (bad) past the diamond via `mk_upperOp_fullModSymRep_gamma0_divN`. -/
theorem tpSymb_upperSymb_commute [NeZero N] (k : ℤ) {p q : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hpN : Nat.Coprime p N) (hqN : ¬Nat.Coprime q N) :
    Commute (tpSymb hp hpN k) (upperSymb hq hqN k) := by
  have hpq : p ≠ q := fun h => hqN (h ▸ hpN)
  have hpqc : Nat.Coprime p q := (Nat.coprime_primes hp hq).mpr hpq
  show tpSymb hp hpN k * upperSymb hq hqN k = upperSymb hq hqN k * tpSymb hp hpN k
  rw [Module.End.mul_eq_comp, Module.End.mul_eq_comp]
  refine Coinvariants.hom_ext (LinearMap.ext fun x => ?_)
  show tpSymb hp hpN k (upperSymb hq hqN k (𝕄.mk N k x))
    = upperSymb hq hqN k (tpSymb hp hpN k (𝕄.mk N k x))
  rw [tpSymb_mk, upperSymb_mk, upperSymb_mk, tpSymb_mk]
  -- LHS: mk(tpOp p (U_q x)) = A + B
  have hLHS : 𝕄.mk N k (tpOp hp.pos hpN (k - 2).toNat (upperOp q hq.pos (k - 2).toNat x))
      = 𝕄.mk N k (upperOp p hp.pos (k - 2).toNat (upperOp q hq.pos (k - 2).toNat x))
        + 𝕄.mk N k (fullModSymRep ℤ (k - 2).toNat (diamondRep (N := N) hpN : SL(2, ℤ))
            (actMat (lowerMat p) (lowerMat_det_ne_zero hp.pos) (k - 2).toNat
              (upperOp q hq.pos (k - 2).toNat x))) := by
    rw [tpOp_apply, map_add, actMat_lowerDiamondMat_eq hp.pos hpN]
  -- RHS: mk(U_q (tpOp p x)) = A' + mk(U_q (lowerDiamond_p x))
  have hRHS : 𝕄.mk N k (upperOp q hq.pos (k - 2).toNat (tpOp hp.pos hpN (k - 2).toNat x))
      = 𝕄.mk N k (upperOp q hq.pos (k - 2).toNat (upperOp p hp.pos (k - 2).toNat x))
        + 𝕄.mk N k (upperOp q hq.pos (k - 2).toNat
            (actMat (lowerDiamondMat (N := N) hpN) (lowerDiamondMat_det_ne_zero hp.pos hpN)
              (k - 2).toNat x)) := by
    rw [tpOp_apply]
    exact _root_.map_add ((𝕄.mk N k).comp (upperOp q hq.pos (k - 2).toNat)) _ _
  rw [hLHS, hRHS, mk_upperOp_upperOp_comm hp.pos hq.pos,
    actMat_lowerDiamondMat_eq hp.pos hpN,
    mk_upperOp_fullModSymRep_gamma0_divN hq hqN k (diamondRep (N := N) hpN),
    mk_gamma0_lowerMat_upperOp_comm hp hq hpqc k (diamondRep (N := N) hpN)]

/-- **Cross-prime Hecke commutativity.**  For primes `p, q`, the operators `heckeSymb_p_all p` and
`heckeSymb_p_all q` commute.

* `p ∤ N`, `q ∤ N` (both `T`-operators): `tpSymb_commute`.
* exactly one good prime (mixed `tpSymb`/`upperSymb`): `tpSymb_upperSymb_commute` (and its `symm`).
* `p ∣ N`, `q ∣ N` (both `U`-operators): `upperSymb_commute`. -/
theorem heckeSymb_p_all_commute [NeZero N] (k : ℤ) {p q : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q) :
    Commute (heckeSymb_p_all N k p hp) (heckeSymb_p_all N k q hq) := by
  unfold heckeSymb_p_all
  by_cases hpN : Nat.Coprime p N <;> by_cases hqN : Nat.Coprime q N
  · rw [dif_pos hpN, dif_pos hqN]
    exact tpSymb_commute k hp hq hpN hqN
  · rw [dif_pos hpN, dif_neg hqN]
    exact tpSymb_upperSymb_commute k hp hq hpN hqN
  · rw [dif_neg hpN, dif_pos hqN]
    exact (tpSymb_upperSymb_commute k hq hp hqN hpN).symm
  · rw [dif_neg hpN, dif_neg hqN]
    exact upperSymb_commute k hp hq hpN hqN

/-! ## Centralizer induction: everything commuting with the atoms commutes with `heckeSymb` -/

/-- If `C` commutes with `heckeSymb_p_all p` and with `diamondSymb_n p`, then it commutes with every
prime-power Hecke operator `heckeSymbPpow p r`.  (Strong induction on `r` via the Diamond–Shurman
recurrence, whose ingredients are exactly `heckeSymb_p_all p` and `diamondSymb_n p`.) -/
theorem commute_heckeSymbPpow [NeZero N] (k : ℤ) {p : ℕ} (hp : Nat.Prime p)
    (C : Module.End ℤ (𝕄 N k)) (hA : Commute C (heckeSymb_p_all N k p hp))
    (hD : Commute C (diamondSymb_n N k p)) : ∀ r, Commute C (heckeSymbPpow N k p hp r)
  | 0 => by rw [heckeSymbPpow_zero]; exact Commute.one_right C
  | 1 => by rw [heckeSymbPpow_one]; exact hA
  | (r + 2) => by
    rw [heckeSymbPpow_succ_succ]
    exact (hA.mul_right (commute_heckeSymbPpow k hp C hA hD (r + 1))).sub_right
      ((hD.mul_right (commute_heckeSymbPpow k hp C hA hD r)).smul_right _)

/-- If `C` commutes with every prime Hecke operator `heckeSymb_p_all p` and every extended diamond
`diamondSymb_n p`, then it commutes with `heckeSymb_aux m` for every `m`.  (Strong induction on `m`
via the `minFac`-peeling, whose factors are prime-power Hecke operators.) -/
theorem commute_heckeSymb_aux [NeZero N] (k : ℤ) (C : Module.End ℤ (𝕄 N k))
    (hA : ∀ {p : ℕ} (hp : Nat.Prime p), Commute C (heckeSymb_p_all N k p hp))
    (hD : ∀ p : ℕ, Commute C (diamondSymb_n N k p)) :
    ∀ m, Commute C (heckeSymb_aux N k m)
  | m => by
    rw [heckeSymb_aux]
    by_cases h : m ≤ 1
    · rw [dif_pos h]; exact Commute.one_right C
    · rw [dif_neg h]
      have hp := Nat.minFac_prime (by omega : m ≠ 1)
      have hlt : m / m.minFac ^ m.factorization m.minFac < m :=
        Nat.div_lt_self (by omega) (Nat.one_lt_pow
          (hp.factorization_pos_of_dvd (by omega) (Nat.minFac_dvd m)).ne' hp.one_lt)
      exact (commute_heckeSymbPpow k hp C (hA hp) (hD _) _).mul_right
        (commute_heckeSymb_aux k C hA hD _)

/-- A prime Hecke operator commutes with `heckeSymb_aux m` for every `m`. -/
theorem heckeSymb_p_all_commute_heckeSymb_aux [NeZero N] (k : ℤ) {q : ℕ} (hq : Nat.Prime q)
    (m : ℕ) : Commute (heckeSymb_p_all N k q hq) (heckeSymb_aux N k m) :=
  commute_heckeSymb_aux k (heckeSymb_p_all N k q hq)
    (fun hp => heckeSymb_p_all_commute k hq hp)
    (fun n => heckeSymb_p_all_commute_diamondSymb_n k hq n)
    m

/-- An extended diamond `diamondSymb_n q` commutes with `heckeSymb_aux m` for every `m`. -/
theorem diamondSymb_n_commute_heckeSymb_aux [NeZero N] (k : ℤ) (q m : ℕ) :
    Commute (diamondSymb_n N k q) (heckeSymb_aux N k m) :=
  commute_heckeSymb_aux k (diamondSymb_n N k q)
    (fun hp => (heckeSymb_p_all_commute_diamondSymb_n k hp q).symm)
    (fun n => diamondSymb_n_commute k q n) m

/-- A diamond `⟨d⟩` commutes with `heckeSymb_aux m` for every `m`. -/
theorem diamondSymb_commute_heckeSymb_aux [NeZero N] (k : ℤ) (d : (ZMod N)ˣ) (m : ℕ) :
    Commute (diamondSymb N k d) (heckeSymb_aux N k m) :=
  commute_heckeSymb_aux k (diamondSymb N k d)
    (fun hp => (heckeSymb_p_all_commute_diamondSymb k hp d).symm)
    (fun n => (diamondSymb_n_commute_diamondSymb k n d).symm) m

/-! ## The three pairwise-commutativity theorems -/

/-- **`T_m` and `T_n` commute** on `𝕄 N k` (`Hecke–Hecke commutativity`). -/
theorem heckeSymb_commute (N : ℕ) [NeZero N] (k : ℤ) (m n : ℕ) [NeZero m] [NeZero n] :
    Commute (heckeSymb N k m) (heckeSymb N k n) :=
  commute_heckeSymb_aux k (heckeSymb_aux N k m)
    (fun hp => (heckeSymb_p_all_commute_heckeSymb_aux k hp m).symm)
    (fun q => (diamondSymb_n_commute_heckeSymb_aux k q m).symm) n

/-- **`T_n` and `⟨d⟩` commute** on `𝕄 N k` (`Hecke–diamond commutativity`). -/
theorem heckeSymb_diamondSymb_commute (N : ℕ) [NeZero N] (k : ℤ) (n : ℕ) [NeZero n]
    (d : (ZMod N)ˣ) : Commute (heckeSymb N k n) (diamondSymb N k d) :=
  (diamondSymb_commute_heckeSymb_aux k d n).symm

/-! ## The packaged `Pairwise (Commute on genM)` form -/

/-- The pairwise commutativity of all symbol-side Hecke and diamond generators, packaged exactly as
the `hComm` hypothesis consumed by `heckeAlgℤ_finite_of_period` (`HeckeFinite.lean`): the generators
`genM = Sum.elim (fun n : ℕ+ => heckeSymb N k n.val) (fun d => diamondSymb N k d)` pairwise
commute. -/
theorem hComm_genM (N : ℕ) [NeZero N] (k : ℤ) :
    Pairwise fun i j => Commute (genM N k i) (genM N k j) := by
  intro i j _
  cases i with
  | inl m =>
    cases j with
    | inl n =>
      haveI : NeZero m.val := ⟨m.ne_zero⟩
      haveI : NeZero n.val := ⟨n.ne_zero⟩
      exact heckeSymb_commute N k m.val n.val
    | inr e => exact heckeSymb_diamondSymb_commute N k m.val e
  | inr d =>
    cases j with
    | inl n =>
      haveI : NeZero n.val := ⟨n.ne_zero⟩
      exact (heckeSymb_diamondSymb_commute N k n.val d).symm
    | inr e => exact diamondSymb_commute N k d e

end HeckeRing.GL2.ModularSymbols
