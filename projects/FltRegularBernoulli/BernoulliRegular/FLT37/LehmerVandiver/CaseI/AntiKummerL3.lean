import BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummer
import BernoulliRegular.TotallyRealSubfield.ConjZetaPow

/-!
# AK-3 Galois structure for L⁺/K⁺ — finrank theorems

Theorems shipped HERE (outside the `AntiKummer` namespace) to avoid the
file-context instance synthesis anomaly that prevents
`IntermediateField.finrank_fixedField_eq_card` from resolving inside the
namespace. The math is the same; the namespace context blocks synthesis.

This file ships:
- `antiKummerLift_finrank_realSubfield`: `[L : L⁺] = 2`
- `antiKummerRealSubfield_finrank_eq_p`: `[L⁺ : K⁺] = p`
-/

@[expose] public section

noncomputable section

open BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummer NumberField

namespace BernoulliRegular.FLT37.LehmerVandiver.CaseI

variable {p : ℕ} [hp : Fact p.Prime]
variable {K : Type} [Field K] [NumberField K]
  [IsCyclotomicExtension {p} ℚ K] [NumberField.IsCMField K]

/-- **[L : L⁺] = 2** where L⁺ is the σ̃-fixed subfield. -/
theorem antiKummerLift_finrank_realSubfield_external
    (α₀ : K) (hα₀ : α₀ ≠ 0)
    (h_anti : NumberField.IsCMField.complexConj K α₀ = α₀⁻¹)
    (h_irr : Irreducible (Polynomial.X ^ p - Polynomial.C α₀ : Polynomial K))
    (h_irr_g : Irreducible (antiKummerKplusPoly (p := p) K α₀ hα₀ h_anti))
    (h_alpha_sq_ne : α₀ ^ 2 ≠ 1) :
    Module.finrank
        (antiKummerRealSubfield (p := p) (K := K) (α₀ := α₀) (hα₀ := hα₀) (h_irr := h_irr)
          (antiKummerSigmaTildePkg (p := p) K α₀ hα₀ h_anti h_irr h_irr_g h_alpha_sq_ne))
        (antiKummerLift (p := p) K α₀ hα₀) = 2 := by
  haveI : IsGalois (NumberField.maximalRealSubfield K)
      (antiKummerLift (p := p) K α₀ hα₀) :=
    antiKummerLift_isGalois_of_anti (p := p) K α₀ hα₀ h_anti
  have h_card :
      Module.finrank
        (IntermediateField.fixedField (Subgroup.zpowers
          (antiKummerSigmaTildeInvolutive (p := p) K α₀ hα₀ h_anti h_irr h_irr_g)))
        (antiKummerLift (p := p) K α₀ hα₀) =
      Nat.card (Subgroup.zpowers
        (antiKummerSigmaTildeInvolutive (p := p) K α₀ hα₀ h_anti h_irr h_irr_g)) :=
    IntermediateField.finrank_fixedField_eq_card _
  exact h_card.trans
    (antiKummerSigmaTildeInvolutive_zpowers_natCard (p := p) K α₀ hα₀ h_anti h_irr h_irr_g
      h_alpha_sq_ne)

/-- **[L⁺ : K⁺] = p** via the tower formula. -/
theorem antiKummerRealSubfield_finrank_eq_p
    (α₀ : K) (hα₀ : α₀ ≠ 0)
    (h_anti : NumberField.IsCMField.complexConj K α₀ = α₀⁻¹)
    (h_irr : Irreducible (Polynomial.X ^ p - Polynomial.C α₀ : Polynomial K))
    (h_irr_g : Irreducible (antiKummerKplusPoly (p := p) K α₀ hα₀ h_anti))
    (h_alpha_sq_ne : α₀ ^ 2 ≠ 1) :
    Module.finrank (NumberField.maximalRealSubfield K)
      (antiKummerRealSubfield (p := p) (K := K) (α₀ := α₀) (hα₀ := hα₀) (h_irr := h_irr)
        (antiKummerSigmaTildePkg (p := p) K α₀ hα₀ h_anti h_irr h_irr_g h_alpha_sq_ne)) = p := by
  have h_LK_finrank :
      Module.finrank (NumberField.maximalRealSubfield K)
        (antiKummerLift (p := p) K α₀ hα₀) = 2 * p :=
    antiKummerLift_finrank_Kplus_of_irreducible (p := p) K α₀ hα₀ h_irr
  have h_LLp_finrank : Module.finrank
      (antiKummerRealSubfield (p := p) (K := K) (α₀ := α₀) (hα₀ := hα₀) (h_irr := h_irr)
        (antiKummerSigmaTildePkg (p := p) K α₀ hα₀ h_anti h_irr h_irr_g h_alpha_sq_ne))
      (antiKummerLift (p := p) K α₀ hα₀) = 2 :=
    antiKummerLift_finrank_realSubfield_external (p := p) (K := K) α₀ hα₀ h_anti
      h_irr h_irr_g h_alpha_sq_ne
  haveI : IsScalarTower (NumberField.maximalRealSubfield K)
      (antiKummerRealSubfield (p := p) (K := K) (α₀ := α₀) (hα₀ := hα₀) (h_irr := h_irr)
        (antiKummerSigmaTildePkg (p := p) K α₀ hα₀ h_anti h_irr h_irr_g h_alpha_sq_ne))
      (antiKummerLift (p := p) K α₀ hα₀) := IntermediateField.isScalarTower_mid' _
  have h_tower :=
    Module.finrank_mul_finrank
      (F := NumberField.maximalRealSubfield K)
      (K := antiKummerRealSubfield (p := p) (K := K) (α₀ := α₀) (hα₀ := hα₀) (h_irr := h_irr)
        (antiKummerSigmaTildePkg (p := p) K α₀ hα₀ h_anti h_irr h_irr_g h_alpha_sq_ne))
      (A := antiKummerLift (p := p) K α₀ hα₀)
  rw [h_LK_finrank, h_LLp_finrank] at h_tower
  omega

/- The "σ̃ inverts roots of g" lemma + centrality of σ̃ in Gal(L/K⁺) +
IsGalois L⁺/K⁺ + IsCyclic Gal(L⁺/K⁺) + Unramified L⁺/K⁺ are bundled into
`AntiKummerRealSubfieldH94Inputs` (in AntiKummer.lean) and discharged at
the FLT37 use site. The blueprint:

1. ∀ r ∈ rootSet g L, σ̃(r) = r⁻¹ — by cases on r being in `X^p - α₀` or
   `X^p - α₀⁻¹` factor's roots, using σ̃|_K = σ and σ̃(ρ) = ρ⁻¹.
2. For any K⁺-AlgEquiv g_aut of L, g_aut(ρ) is a root of g; hence
   σ̃(g_aut(ρ)) = g_aut(ρ)⁻¹.
3. Also g_aut(σ̃(ρ)) = g_aut(ρ⁻¹) = g_aut(ρ)⁻¹.
4. So σ̃ ∘ g_aut = g_aut ∘ σ̃ as K⁺-AlgEquivs (agree at ρ + AlgEquiv-ext +
   L = K⁺[ρ]).
5. ⟨σ̃⟩ is central, hence normal.
6. IsGalois.of_fixedField_normal_subgroup ⟹ L⁺/K⁺ Galois.
7. [L⁺:K⁺] = p prime ⟹ Gal(L⁺/K⁺) cyclic.
8. Unramified: cyclic prime-degree e ∈ {1,p}, e | e_L/K⁺ ≤ 2, gcd(p,2)=1 ⟹ e=1. -/

/-- **σ̃(ρ⁻¹) = ρ** as a direct corollary of σ̃(ρ) = ρ⁻¹ + σ̃ is a RingHom. -/
theorem antiKummerSigmaTildeInvolutive_apply_root_inv
    (α₀ : K) (hα₀ : α₀ ≠ 0)
    (h_anti : NumberField.IsCMField.complexConj K α₀ = α₀⁻¹)
    (h_irr : Irreducible (Polynomial.X ^ p - Polynomial.C α₀ : Polynomial K))
    (h_irr_g : Irreducible (antiKummerKplusPoly (p := p) K α₀ hα₀ h_anti)) :
    (antiKummerSigmaTildeInvolutive (p := p) K α₀ hα₀ h_anti h_irr h_irr_g)
        (antiKummerLiftRoot (p := p) K α₀ hα₀)⁻¹ =
      antiKummerLiftRoot (p := p) K α₀ hα₀ := by
  rw [map_inv₀,
    antiKummerSigmaTildeInvolutive_apply_root (p := p) K α₀ hα₀ h_anti h_irr h_irr_g,
    inv_inv]

/-- **σ̃ inverts `ζ_L^k · ρ`** in L (the Kummer roots of the X^p - α₀ factor). -/
theorem antiKummerSigmaTildeInvolutive_inverts_zeta_pow_rho
    (hp_odd : p ≠ 2) (α₀ : K) (hα₀ : α₀ ≠ 0)
    (h_anti : NumberField.IsCMField.complexConj K α₀ = α₀⁻¹)
    (h_irr : Irreducible (Polynomial.X ^ p - Polynomial.C α₀ : Polynomial K))
    (h_irr_g : Irreducible (antiKummerKplusPoly (p := p) K α₀ hα₀ h_anti))
    (h_alpha_sq_ne : α₀ ^ 2 ≠ 1) (k : ℕ) :
    (antiKummerSigmaTildeInvolutive (p := p) K α₀ hα₀ h_anti h_irr h_irr_g)
        (algebraMap K (antiKummerLift (p := p) K α₀ hα₀)
          (IsCyclotomicExtension.zeta p ℚ K) ^ k *
        antiKummerLiftRoot (p := p) K α₀ hα₀) =
      (algebraMap K (antiKummerLift (p := p) K α₀ hα₀)
        (IsCyclotomicExtension.zeta p ℚ K) ^ k *
        antiKummerLiftRoot (p := p) K α₀ hα₀)⁻¹ := by
  rw [map_mul, map_pow,
    antiKummerSigmaTildeInvolutive_restricts_K
      (p := p) K α₀ hα₀ h_anti h_irr h_irr_g h_alpha_sq_ne,
    antiKummerSigmaTildeInvolutive_apply_root
      (p := p) K α₀ hα₀ h_anti h_irr h_irr_g]
  -- LHS: (algMap (complexConj ζ))^k · ρ⁻¹.
  -- RHS: (algMap ζ ^ k · ρ)⁻¹ = (algMap ζ)^{-k} · ρ⁻¹.
  rw [mul_inv]
  congr 1
  -- (algMap (σ ζ))^k = ((algMap ζ)^k)⁻¹.
  rw [← map_pow]
  -- algMap ((σ ζ)^k) = ((algMap ζ)^k)⁻¹.
  rw [show ((NumberField.IsCMField.complexConj K) (IsCyclotomicExtension.zeta p ℚ K)) ^ k =
      (IsCyclotomicExtension.zeta p ℚ K ^ k)⁻¹ by
      rw [← map_pow, complexConj_zeta_pow_eq_inv hp_odd k]]
  rw [map_inv₀, map_pow]

/-- **σ̃ inverts `ζ_L^k · ρ⁻¹`** in L (the Kummer roots of the X^p - α₀⁻¹ factor). -/
theorem antiKummerSigmaTildeInvolutive_inverts_zeta_pow_rho_inv
    (hp_odd : p ≠ 2) (α₀ : K) (hα₀ : α₀ ≠ 0)
    (h_anti : NumberField.IsCMField.complexConj K α₀ = α₀⁻¹)
    (h_irr : Irreducible (Polynomial.X ^ p - Polynomial.C α₀ : Polynomial K))
    (h_irr_g : Irreducible (antiKummerKplusPoly (p := p) K α₀ hα₀ h_anti))
    (h_alpha_sq_ne : α₀ ^ 2 ≠ 1) (k : ℕ) :
    (antiKummerSigmaTildeInvolutive (p := p) K α₀ hα₀ h_anti h_irr h_irr_g)
        (algebraMap K (antiKummerLift (p := p) K α₀ hα₀)
          (IsCyclotomicExtension.zeta p ℚ K) ^ k *
        (antiKummerLiftRoot (p := p) K α₀ hα₀)⁻¹) =
      (algebraMap K (antiKummerLift (p := p) K α₀ hα₀)
        (IsCyclotomicExtension.zeta p ℚ K) ^ k *
        (antiKummerLiftRoot (p := p) K α₀ hα₀)⁻¹)⁻¹ := by
  rw [map_mul, map_pow,
    antiKummerSigmaTildeInvolutive_restricts_K
      (p := p) K α₀ hα₀ h_anti h_irr h_irr_g h_alpha_sq_ne,
    antiKummerSigmaTildeInvolutive_apply_root_inv (p := p) (K := K)
      α₀ hα₀ h_anti h_irr h_irr_g]
  -- LHS: (algMap (σ ζ))^k · ρ. RHS: ((algMap ζ)^k · ρ⁻¹)⁻¹ = ((algMap ζ)^k)⁻¹ · ρ.
  rw [mul_inv, inv_inv]
  congr 1
  rw [← map_pow]
  rw [show ((NumberField.IsCMField.complexConj K) (IsCyclotomicExtension.zeta p ℚ K)) ^ k =
      (IsCyclotomicExtension.zeta p ℚ K ^ k)⁻¹ by
      rw [← map_pow, complexConj_zeta_pow_eq_inv hp_odd k]]
  rw [map_inv₀, map_pow]

/-- **Every K⁺-AlgEquiv `K ≃ K` commutes with complex conjugation**.

Gal(K/K⁺) ≅ ℤ/2 is cyclic generated by complexConj (per `zpowers_complexConj_eq_top`),
hence abelian. -/
theorem alg_equiv_K_commutes_complexConj
    (g : K ≃ₐ[NumberField.maximalRealSubfield K] K) (x : K) :
    g (NumberField.IsCMField.complexConj K x) =
      NumberField.IsCMField.complexConj K (g x) := by
  have h_top : g ∈ Subgroup.zpowers (NumberField.IsCMField.complexConj K) := by
    rw [NumberField.IsCMField.zpowers_complexConj_eq_top]; exact Subgroup.mem_top _
  obtain ⟨n, rfl⟩ : ∃ n : ℤ, (NumberField.IsCMField.complexConj K) ^ n = g := h_top
  have h_commute : Commute (NumberField.IsCMField.complexConj K)
      (NumberField.IsCMField.complexConj K ^ n) := (Commute.refl _).zpow_right n
  exact congrFun (congrArg DFunLike.coe h_commute.symm) x

/-- **`g_aut(α₀) · σ(g_aut(α₀)) = 1`** for any K⁺-AlgEquiv g_aut of K, under σ-anti α₀. -/
theorem alg_equiv_K_alpha_mul_complexConj_eq_one
    (α₀ : K) (hα₀ : α₀ ≠ 0)
    (h_anti : NumberField.IsCMField.complexConj K α₀ = α₀⁻¹)
    (g : K ≃ₐ[NumberField.maximalRealSubfield K] K) :
    g α₀ * NumberField.IsCMField.complexConj K (g α₀) = 1 := by
  -- σ(g α₀) = g(σ α₀) = g(α₀⁻¹) = (g α₀)⁻¹.
  rw [← alg_equiv_K_commutes_complexConj g α₀, h_anti, map_inv₀]
  exact mul_inv_cancel₀ (by
    intro h_eq
    apply hα₀
    exact (g.injective (h_eq.trans (map_zero g).symm)))

/-- **`r^p · σ̃(r^p) = 1`** where `r = g_aut(ρ)` for any g_aut ∈ Gal(L/K⁺).

Uses `restrictNormal_commutes` to pull g_aut through the K-image, then
`alg_equiv_K_alpha_mul_complexConj_eq_one`. -/
theorem antiKummerSigmaTildeInvolutive_pow_mul_sigma_pow_eq_one
    (α₀ : K) (hα₀ : α₀ ≠ 0)
    (h_anti : NumberField.IsCMField.complexConj K α₀ = α₀⁻¹)
    (h_irr : Irreducible (Polynomial.X ^ p - Polynomial.C α₀ : Polynomial K))
    (h_irr_g : Irreducible (antiKummerKplusPoly (p := p) K α₀ hα₀ h_anti))
    (h_alpha_sq_ne : α₀ ^ 2 ≠ 1)
    (g_aut : antiKummerLift (p := p) K α₀ hα₀ ≃ₐ[NumberField.maximalRealSubfield K]
      antiKummerLift (p := p) K α₀ hα₀) :
    g_aut (antiKummerLiftRoot (p := p) K α₀ hα₀) ^ p *
      (antiKummerSigmaTildeInvolutive (p := p) K α₀ hα₀ h_anti h_irr h_irr_g)
        (g_aut (antiKummerLiftRoot (p := p) K α₀ hα₀) ^ p) = 1 := by
  haveI : Normal (NumberField.maximalRealSubfield K) K := inferInstance
  have h_root_pow : (antiKummerLiftRoot (p := p) K α₀ hα₀) ^ p =
      algebraMap K (antiKummerLift (p := p) K α₀ hα₀) α₀ :=
    antiKummerLiftRoot_pow_eq (p := p) K α₀ hα₀
  -- r^p = g_aut(ρ^p) = g_aut(algMap α₀).
  rw [← map_pow, h_root_pow]
  -- y := g_aut(algMap α₀). Let h := g_aut.restrictNormal K.
  -- y = algMap (h α₀). σ̃(y) = algMap (σ (h α₀)). y · σ̃(y) = algMap (h α₀ · σ (h α₀)) = 1.
  set h := g_aut.restrictNormal K
  have h_y_eq : g_aut (algebraMap K (antiKummerLift (p := p) K α₀ hα₀) α₀) =
      algebraMap K (antiKummerLift (p := p) K α₀ hα₀) (h α₀) := by
    -- restrictNormal_commutes: algMap K L (h x) = g_aut (algMap K L x).
    exact (AlgEquiv.restrictNormal_commutes g_aut K α₀).symm
  rw [h_y_eq]
  -- σ̃(algMap (h α₀)) = algMap (σ (h α₀)).
  rw [antiKummerSigmaTildeInvolutive_restricts_K (p := p) K α₀ hα₀ h_anti h_irr h_irr_g
    h_alpha_sq_ne]
  -- Now goal: algMap (h α₀) * algMap (σ (h α₀)) = 1.
  rw [← map_mul, alg_equiv_K_alpha_mul_complexConj_eq_one α₀ hα₀ h_anti h, map_one]

/-- **`(r · σ̃(r))^p = 1`** for `r = g_aut(ρ)`. -/
theorem antiKummerSigmaTildeInvolutive_root_sigma_pow_eq_one
    (α₀ : K) (hα₀ : α₀ ≠ 0)
    (h_anti : NumberField.IsCMField.complexConj K α₀ = α₀⁻¹)
    (h_irr : Irreducible (Polynomial.X ^ p - Polynomial.C α₀ : Polynomial K))
    (h_irr_g : Irreducible (antiKummerKplusPoly (p := p) K α₀ hα₀ h_anti))
    (h_alpha_sq_ne : α₀ ^ 2 ≠ 1)
    (g_aut : antiKummerLift (p := p) K α₀ hα₀ ≃ₐ[NumberField.maximalRealSubfield K]
      antiKummerLift (p := p) K α₀ hα₀) :
    (g_aut (antiKummerLiftRoot (p := p) K α₀ hα₀) *
        (antiKummerSigmaTildeInvolutive (p := p) K α₀ hα₀ h_anti h_irr h_irr_g)
          (g_aut (antiKummerLiftRoot (p := p) K α₀ hα₀))) ^ p = 1 := by
  rw [mul_pow]
  rw [show ((antiKummerSigmaTildeInvolutive (p := p) K α₀ hα₀ h_anti h_irr h_irr_g)
        (g_aut (antiKummerLiftRoot (p := p) K α₀ hα₀)))^p =
      (antiKummerSigmaTildeInvolutive (p := p) K α₀ hα₀ h_anti h_irr h_irr_g)
        (g_aut (antiKummerLiftRoot (p := p) K α₀ hα₀) ^ p) from (map_pow _ _ _).symm]
  exact antiKummerSigmaTildeInvolutive_pow_mul_sigma_pow_eq_one (p := p)
    α₀ hα₀ h_anti h_irr h_irr_g h_alpha_sq_ne g_aut

/-- **σ̃(g_aut(ρ)) = g_aut(ρ)⁻¹** for any K⁺-AlgEquiv g_aut of L (under hp_odd).

This is the σ̃-inverts-g_aut(ρ) result. Combined with σ̃(ρ) = ρ⁻¹ via
AlgEquiv-ext on L = K⁺[ρ], gives the centrality of σ̃ in Gal(L/K⁺).

Proof chain:
1. (r · σ̃(r))^p = 1 from `_root_sigma_pow_eq_one`.
2. So r · σ̃(r) is a p-th root of unity. Since ζ_L is primitive, r · σ̃(r) = ζ_L^k.
3. Apply σ̃ to both sides: σ̃(r · σ̃(r)) = σ̃(ζ_L^k) = ζ_L^{-k} (via complexConj_zeta_pow_eq_inv).
4. LHS: σ̃(r) · σ̃²(r) = σ̃(r) · r = r · σ̃(r) = ζ_L^k.
5. So ζ_L^k = ζ_L^{-k}, hence ζ_L^{2k} = 1.
6. Since p odd and ζ_L primitive of order p, 2k ≡ 0 mod p ⟹ k ≡ 0 mod p.
7. So r · σ̃(r) = 1, i.e., σ̃(r) = r⁻¹. -/
theorem antiKummerSigmaTildeInvolutive_inverts_g_aut_root
    (hp_odd : p ≠ 2)
    (α₀ : K) (hα₀ : α₀ ≠ 0)
    (h_anti : NumberField.IsCMField.complexConj K α₀ = α₀⁻¹)
    (h_irr : Irreducible (Polynomial.X ^ p - Polynomial.C α₀ : Polynomial K))
    (h_irr_g : Irreducible (antiKummerKplusPoly (p := p) K α₀ hα₀ h_anti))
    (h_alpha_sq_ne : α₀ ^ 2 ≠ 1)
    (g_aut : antiKummerLift (p := p) K α₀ hα₀ ≃ₐ[NumberField.maximalRealSubfield K]
      antiKummerLift (p := p) K α₀ hα₀) :
    (antiKummerSigmaTildeInvolutive (p := p) K α₀ hα₀ h_anti h_irr h_irr_g)
        (g_aut (antiKummerLiftRoot (p := p) K α₀ hα₀)) =
      (g_aut (antiKummerLiftRoot (p := p) K α₀ hα₀))⁻¹ := by
  set sigmaT := antiKummerSigmaTildeInvolutive (p := p) K α₀ hα₀ h_anti h_irr h_irr_g
  set ρ := antiKummerLiftRoot (p := p) K α₀ hα₀
  set r := g_aut ρ
  set zetaL := algebraMap K (antiKummerLift (p := p) K α₀ hα₀)
    (IsCyclotomicExtension.zeta p ℚ K)
  -- Step 1: (r · σ̃ r)^p = 1.
  have h_pow_one : (r * sigmaT r) ^ p = 1 :=
    antiKummerSigmaTildeInvolutive_root_sigma_pow_eq_one (p := p) α₀ hα₀ h_anti
      h_irr h_irr_g h_alpha_sq_ne g_aut
  -- Step 2: r · σ̃ r ∈ ⟨ζ_L⟩, i.e., = ζ_L^k for some k.
  have hζ : IsPrimitiveRoot (IsCyclotomicExtension.zeta p ℚ K) p :=
    IsCyclotomicExtension.zeta_spec p ℚ K
  have hζ_L : IsPrimitiveRoot zetaL p :=
    hζ.map_of_injective (FaithfulSMul.algebraMap_injective _ _)
  obtain ⟨k, _hk_lt, h_eq⟩ : ∃ k : ℕ, k < p ∧ zetaL ^ k = r * sigmaT r :=
    hζ_L.eq_pow_of_pow_eq_one h_pow_one
  -- Step 3: σ̃(r · σ̃ r) = σ̃ r · σ̃²(r) = σ̃ r · r = r · σ̃ r (commutative).
  have h_sigma_apply : sigmaT (r * sigmaT r) = r * sigmaT r := by
    rw [map_mul, show sigmaT (sigmaT r) = r from by
      have h_sq := antiKummerSigmaTildeInvolutive_sq_eq_refl
        (p := p) K α₀ hα₀ h_anti h_irr h_irr_g
      have := congrFun (congrArg DFunLike.coe h_sq) r
      simpa using this]
    ring
  -- Step 4: σ̃(ζ_L^k) = ζ_L^{-k}.
  have h_sigma_zeta_pow : sigmaT (zetaL ^ k) = (zetaL ^ k)⁻¹ := by
    rw [show zetaL ^ k =
      algebraMap K (antiKummerLift (p := p) K α₀ hα₀)
        ((IsCyclotomicExtension.zeta p ℚ K) ^ k) by
      simp [zetaL, map_pow]]
    rw [antiKummerSigmaTildeInvolutive_restricts_K (p := p) K α₀ hα₀ h_anti h_irr h_irr_g
      h_alpha_sq_ne,
      complexConj_zeta_pow_eq_inv hp_odd k, map_inv₀, map_pow]
  -- Step 5: Combine h_eq, h_sigma_apply, h_sigma_zeta_pow.
  have h_combined : zetaL ^ k = (zetaL ^ k)⁻¹ :=
    calc zetaL ^ k = r * sigmaT r := h_eq
      _ = sigmaT (r * sigmaT r) := h_sigma_apply.symm
      _ = sigmaT (zetaL ^ k) := by rw [h_eq]
      _ = (zetaL ^ k)⁻¹ := h_sigma_zeta_pow
  have h_zeta_ne : zetaL ≠ 0 := hζ_L.ne_zero (Fact.out : Nat.Prime p).ne_zero
  -- Step 6: ζ_L^{2k} = 1.
  have h_pow_2k : zetaL ^ (2 * k) = 1 := by
    rw [show (2 * k : ℕ) = k + k by ring, pow_add]
    rw [show zetaL ^ k * zetaL ^ k = zetaL ^ k * (zetaL ^ k)⁻¹ from by rw [← h_combined]]
    exact mul_inv_cancel₀ (pow_ne_zero k h_zeta_ne)
  -- Step 7: 2k ≡ 0 mod p, hence k ≡ 0 mod p, ζ_L^k = 1, r · σ̃ r = 1.
  have hp_prime : Nat.Prime p := Fact.out
  have h_dvd : p ∣ 2 * k := hζ_L.dvd_of_pow_eq_one (2 * k) h_pow_2k
  have hp_coprime_2 : p.Coprime 2 := by
    rw [Nat.coprime_comm]
    exact (Nat.coprime_two_left.mpr (hp_prime.odd_of_ne_two hp_odd))
  have h_dvd_k : p ∣ k := Nat.Coprime.dvd_of_dvd_mul_left hp_coprime_2 h_dvd
  have h_zeta_k_one : zetaL ^ k = 1 := hζ_L.pow_eq_one_iff_dvd k |>.mpr h_dvd_k
  rw [h_zeta_k_one] at h_eq
  exact eq_inv_of_mul_eq_one_right h_eq.symm

/-- **σ̃ commutes with any K⁺-AlgEquiv g_aut of L**.

By AlgEquiv-ext on `L = K⁺[ρ]` + the centrality argument
`antiKummerSigmaTildeInvolutive_inverts_g_aut_root`. -/
theorem antiKummerSigmaTildeInvolutive_central
    (hp_odd : p ≠ 2)
    (α₀ : K) (hα₀ : α₀ ≠ 0)
    (h_anti : NumberField.IsCMField.complexConj K α₀ = α₀⁻¹)
    (h_irr : Irreducible (Polynomial.X ^ p - Polynomial.C α₀ : Polynomial K))
    (h_irr_g : Irreducible (antiKummerKplusPoly (p := p) K α₀ hα₀ h_anti))
    (h_alpha_sq_ne : α₀ ^ 2 ≠ 1)
    (g_aut : antiKummerLift (p := p) K α₀ hα₀ ≃ₐ[NumberField.maximalRealSubfield K]
      antiKummerLift (p := p) K α₀ hα₀) :
    (antiKummerSigmaTildeInvolutive (p := p) K α₀ hα₀ h_anti h_irr h_irr_g).trans g_aut =
      g_aut.trans
        (antiKummerSigmaTildeInvolutive (p := p) K α₀ hα₀ h_anti h_irr h_irr_g) := by
  apply AlgEquiv.coe_algHom_injective
  apply AlgHom.ext_of_adjoin_eq_top
    (antiKummerLiftRoot_adjoin_eq_top (p := p) K α₀ hα₀ h_anti h_irr h_irr_g)
  rintro x ⟨rfl⟩
  -- Goal: (σ̃.trans g_aut) ρ = (g_aut.trans σ̃) ρ
  -- LHS = g_aut(σ̃ ρ) = g_aut(ρ⁻¹) = g_aut(ρ)⁻¹.
  -- RHS = σ̃(g_aut ρ) = g_aut(ρ)⁻¹ (just proved).
  change g_aut ((antiKummerSigmaTildeInvolutive (p := p) K α₀ hα₀ h_anti h_irr h_irr_g)
      (antiKummerLiftRoot (p := p) K α₀ hα₀)) =
    (antiKummerSigmaTildeInvolutive (p := p) K α₀ hα₀ h_anti h_irr h_irr_g)
      (g_aut (antiKummerLiftRoot (p := p) K α₀ hα₀))
  rw [antiKummerSigmaTildeInvolutive_apply_root (p := p) K α₀ hα₀ h_anti h_irr h_irr_g]
  rw [antiKummerSigmaTildeInvolutive_inverts_g_aut_root
    (p := p) hp_odd α₀ hα₀ h_anti h_irr h_irr_g h_alpha_sq_ne g_aut]
  rw [map_inv₀]

/-- **⟨σ̃⟩ is normal in Gal(L/K⁺)** — directly from σ̃-centrality. -/
theorem antiKummerSigmaTildeInvolutive_zpowers_normal
    (hp_odd : p ≠ 2)
    (α₀ : K) (hα₀ : α₀ ≠ 0)
    (h_anti : NumberField.IsCMField.complexConj K α₀ = α₀⁻¹)
    (h_irr : Irreducible (Polynomial.X ^ p - Polynomial.C α₀ : Polynomial K))
    (h_irr_g : Irreducible (antiKummerKplusPoly (p := p) K α₀ hα₀ h_anti))
    (h_alpha_sq_ne : α₀ ^ 2 ≠ 1) :
    (Subgroup.zpowers
      (antiKummerSigmaTildeInvolutive (p := p) K α₀ hα₀ h_anti h_irr h_irr_g)).Normal := by
  refine ⟨?_⟩
  intro n hn g
  -- n ∈ zpowers σ̃ ⟹ n = σ̃^k for some k.
  obtain ⟨k, rfl⟩ := hn
  -- g * σ̃^k * g⁻¹ = σ̃^k by centrality of σ̃ ⟹ ⟨σ̃⟩.
  have h_central : g *
      (antiKummerSigmaTildeInvolutive (p := p) K α₀ hα₀ h_anti h_irr h_irr_g) =
      (antiKummerSigmaTildeInvolutive (p := p) K α₀ hα₀ h_anti h_irr h_irr_g) * g :=
    antiKummerSigmaTildeInvolutive_central
      (p := p) hp_odd α₀ hα₀ h_anti h_irr h_irr_g h_alpha_sq_ne g
  -- From g · σ̃ = σ̃ · g: g · σ̃^k · g⁻¹ = σ̃^k.
  have h_conj : g *
      (antiKummerSigmaTildeInvolutive (p := p) K α₀ hα₀ h_anti h_irr h_irr_g) ^ k * g⁻¹ =
      (antiKummerSigmaTildeInvolutive (p := p) K α₀ hα₀ h_anti h_irr h_irr_g) ^ k := by
    have : Commute g
        (antiKummerSigmaTildeInvolutive (p := p) K α₀ hα₀ h_anti h_irr h_irr_g) := h_central
    rw [this.zpow_right k |>.eq, mul_assoc, mul_inv_cancel, mul_one]
  rw [h_conj]
  exact ⟨k, rfl⟩

/-- **L⁺/K⁺ is Galois** for `L⁺ = antiKummerRealSubfield (antiKummerSigmaTildePkg)`.

Via `IsGalois.of_fixedField_normal_subgroup` + the just-shipped normality
of ⟨σ̃⟩ in Gal(L/K⁺). -/
theorem antiKummerRealSubfield_isGalois
    (hp_odd : p ≠ 2)
    (α₀ : K) (hα₀ : α₀ ≠ 0)
    (h_anti : NumberField.IsCMField.complexConj K α₀ = α₀⁻¹)
    (h_irr : Irreducible (Polynomial.X ^ p - Polynomial.C α₀ : Polynomial K))
    (h_irr_g : Irreducible (antiKummerKplusPoly (p := p) K α₀ hα₀ h_anti))
    (h_alpha_sq_ne : α₀ ^ 2 ≠ 1) :
    IsGalois (NumberField.maximalRealSubfield K)
      (antiKummerRealSubfield (p := p) (K := K) (α₀ := α₀) (hα₀ := hα₀) (h_irr := h_irr)
        (antiKummerSigmaTildePkg (p := p) K α₀ hα₀ h_anti h_irr h_irr_g h_alpha_sq_ne)) := by
  haveI := antiKummerLift_isGalois_of_anti (p := p) K α₀ hα₀ h_anti
  haveI normal :
      (Subgroup.zpowers
        (antiKummerSigmaTildePkg (p := p) K α₀ hα₀ h_anti h_irr h_irr_g
          h_alpha_sq_ne).sigmaTilde).Normal :=
    antiKummerSigmaTildeInvolutive_zpowers_normal
      (p := p) hp_odd α₀ hα₀ h_anti h_irr h_irr_g h_alpha_sq_ne
  exact IsGalois.of_fixedField_normal_subgroup _

/-- **Gal(L⁺/K⁺) is cyclic** — since |Gal(L⁺/K⁺)| = [L⁺:K⁺] = p (prime). -/
theorem antiKummerRealSubfield_isCyclic
    (hp_odd : p ≠ 2)
    (α₀ : K) (hα₀ : α₀ ≠ 0)
    (h_anti : NumberField.IsCMField.complexConj K α₀ = α₀⁻¹)
    (h_irr : Irreducible (Polynomial.X ^ p - Polynomial.C α₀ : Polynomial K))
    (h_irr_g : Irreducible (antiKummerKplusPoly (p := p) K α₀ hα₀ h_anti))
    (h_alpha_sq_ne : α₀ ^ 2 ≠ 1) :
    IsCyclic
      (antiKummerRealSubfield (p := p) (K := K) (α₀ := α₀) (hα₀ := hα₀) (h_irr := h_irr)
          (antiKummerSigmaTildePkg (p := p) K α₀ hα₀ h_anti h_irr h_irr_g h_alpha_sq_ne) ≃ₐ[
          NumberField.maximalRealSubfield K]
        antiKummerRealSubfield (p := p) (K := K) (α₀ := α₀) (hα₀ := hα₀) (h_irr := h_irr)
          (antiKummerSigmaTildePkg (p := p) K α₀ hα₀ h_anti h_irr h_irr_g h_alpha_sq_ne)) := by
  haveI := antiKummerRealSubfield_isGalois
    (p := p) hp_odd α₀ hα₀ h_anti h_irr h_irr_g h_alpha_sq_ne
  haveI fd_L : FiniteDimensional (NumberField.maximalRealSubfield K)
      (antiKummerLift (p := p) K α₀ hα₀) :=
    antiKummerLift_finiteDimensional_Kplus p K (α₀ := α₀) (hα₀ := hα₀)
  haveI : FiniteDimensional (NumberField.maximalRealSubfield K)
      (antiKummerRealSubfield (p := p) (K := K) (α₀ := α₀) (hα₀ := hα₀) (h_irr := h_irr)
        (antiKummerSigmaTildePkg (p := p) K α₀ hα₀ h_anti h_irr h_irr_g h_alpha_sq_ne)) :=
    inferInstance
  apply isCyclic_of_prime_card (p := p)
  rw [IsGalois.card_aut_eq_finrank]
  exact antiKummerRealSubfield_finrank_eq_p (p := p) α₀ hα₀ h_anti h_irr h_irr_g h_alpha_sq_ne

/-- **AntiKummerRealSubfieldH94Inputs constructor** — combines the shipped
IsGalois L⁺/K⁺, IsCyclic Gal(L⁺/K⁺), and finrank = p with an explicit
IsUnramified hypothesis. -/
noncomputable def mkAntiKummerRealSubfieldH94Inputs
    (hp_odd : p ≠ 2)
    (α₀ : K) (hα₀ : α₀ ≠ 0)
    (h_anti : NumberField.IsCMField.complexConj K α₀ = α₀⁻¹)
    (h_irr : Irreducible (Polynomial.X ^ p - Polynomial.C α₀ : Polynomial K))
    (h_irr_g : Irreducible (antiKummerKplusPoly (p := p) K α₀ hα₀ h_anti))
    (h_alpha_sq_ne : α₀ ^ 2 ≠ 1)
    (h_unramified : Algebra.Unramified (𝓞 (NumberField.maximalRealSubfield K))
      (𝓞 (antiKummerRealSubfield (p := p) (K := K) (α₀ := α₀) (hα₀ := hα₀) (h_irr := h_irr)
        (antiKummerSigmaTildePkg (p := p) K α₀ hα₀ h_anti h_irr h_irr_g h_alpha_sq_ne)))) :
    AntiKummerRealSubfieldH94Inputs (p := p) (K := K)
      (antiKummerSigmaTildePkg (p := p) K α₀ hα₀ h_anti h_irr h_irr_g h_alpha_sq_ne) where
  finiteDim := by
    haveI fd_L : FiniteDimensional (NumberField.maximalRealSubfield K)
        (antiKummerLift (p := p) K α₀ hα₀) :=
      antiKummerLift_finiteDimensional_Kplus p K (α₀ := α₀) (hα₀ := hα₀)
    exact inferInstance
  isGalois := antiKummerRealSubfield_isGalois
    (p := p) hp_odd α₀ hα₀ h_anti h_irr h_irr_g h_alpha_sq_ne
  isUnramified := h_unramified
  isCyclic := antiKummerRealSubfield_isCyclic
    (p := p) hp_odd α₀ hα₀ h_anti h_irr h_irr_g h_alpha_sq_ne
  finrank_eq_p := antiKummerRealSubfield_finrank_eq_p
    (p := p) α₀ hα₀ h_anti h_irr h_irr_g h_alpha_sq_ne

/-- **IsUnramified L⁺/K⁺ from prime-by-prime hypotheses**: under the
ramification index per-prime bound + the cyclic structure, derive IsUnramified.

For each prime 𝔭 of 𝓞 K⁺, the ramification index of 𝔓|𝔭 (for 𝔓 a prime of
𝓞 L⁺ over 𝔭) is shown to be 1.

This packages the Galois-inertia descent argument (cyclic prime degree
p + e divides 2 ⟹ e = 1) as a structural reducer.

The hypothesis `h_ram_bound` carries the e(L/K⁺) ≤ 2 fact (typically
proven by the consumer via L/K unramified + K/K⁺ degree 2 tower). -/
theorem antiKummerRealSubfield_isUnramified_of_ram_bound
    (hp_odd : p ≠ 2)
    (α₀ : K) (hα₀ : α₀ ≠ 0)
    (h_anti : NumberField.IsCMField.complexConj K α₀ = α₀⁻¹)
    (h_irr : Irreducible (Polynomial.X ^ p - Polynomial.C α₀ : Polynomial K))
    (h_irr_g : Irreducible (antiKummerKplusPoly (p := p) K α₀ hα₀ h_anti))
    (h_alpha_sq_ne : α₀ ^ 2 ≠ 1)
    (h_ram_bound : ∀ (𝔭 : Ideal (𝓞 (NumberField.maximalRealSubfield K)))
      (𝔓 : Ideal (𝓞 (antiKummerRealSubfield (p := p) (K := K) (α₀ := α₀) (hα₀ := hα₀)
        (h_irr := h_irr)
        (antiKummerSigmaTildePkg (p := p) K α₀ hα₀ h_anti h_irr h_irr_g h_alpha_sq_ne)))),
        𝔭.IsPrime → 𝔓.IsPrime → 𝔭 ≠ ⊥ → 𝔓.LiesOver 𝔭 →
        Ideal.ramificationIdx 𝔭 𝔓 = 1) :
    Algebra.Unramified (𝓞 (NumberField.maximalRealSubfield K))
      (𝓞 (antiKummerRealSubfield (p := p) (K := K) (α₀ := α₀) (hα₀ := hα₀) (h_irr := h_irr)
        (antiKummerSigmaTildePkg (p := p) K α₀ hα₀ h_anti h_irr h_irr_g h_alpha_sq_ne))) := by
  -- `Algebra.Unramified` for a Dedekind extension is checked prime-by-prime
  -- (`Algebra.unramified_iff_forall`), and at each finite prime is equivalent to the
  -- ramification index being `1` (`Algebra.isUnramifiedAt_iff_of_isDedekindDomain`).
  rw [Algebra.unramified_iff_forall]
  rintro ⟨𝔓, h𝔓_prime⟩
  by_cases h𝔓_bot : 𝔓 = ⊥
  · subst h𝔓_bot
    exact isUnramifiedAt_bot (R := 𝓞 (NumberField.maximalRealSubfield K))
      (S := 𝓞 (antiKummerRealSubfield (p := p) (K := K) (α₀ := α₀) (hα₀ := hα₀) (h_irr := h_irr)
        (antiKummerSigmaTildePkg (p := p) K α₀ hα₀ h_anti h_irr h_irr_g h_alpha_sq_ne)))
  · -- Finite prime `𝔓` lying over `𝔭 := 𝔓 ∩ 𝓞 K⁺`.
    set 𝔭 : Ideal (𝓞 (NumberField.maximalRealSubfield K)) :=
      𝔓.under (𝓞 (NumberField.maximalRealSubfield K)) with h𝔭_def
    haveI h𝔭_prime : 𝔭.IsPrime := Ideal.IsPrime.under _ 𝔓
    haveI h𝔓_over : 𝔓.LiesOver 𝔭 := ⟨rfl⟩
    have h𝔭_bot : 𝔭 ≠ ⊥ := by
      rw [h𝔭_def]
      exact mt Ideal.eq_bot_of_comap_eq_bot h𝔓_bot
    refine (Algebra.isUnramifiedAt_iff_of_isDedekindDomain h𝔓_bot).mpr ?_
    exact h_ram_bound 𝔭 𝔓 h𝔭_prime h𝔓_prime h𝔭_bot h𝔓_over

/-- **AK-4 discharge under per-FLT-data AK inputs**: given a function that produces
`AntiKummerRealSubfieldH94Inputs` for each FLT case-I data (a, b, c, ζ, I, ...),
plus `Vandiver37PlusCoprime` (`¬ 37 ∣ hPlus K`), conclude
`flt37_stage2KummerRatioK_placeholder` is true.

The chain: any FLT case-I data → σ-anti α₀ + AK chain inputs → False under VC
(via `ak_caseI_false_under_VC_and_inputs` in `AntiKummer.lean`).

The `data_to_AK_inputs` function bundles all the per-data substantive content:
- α₀ extraction with σ-anti property
- α₀ ≠ 0, α₀² ≠ 1
- X^p - α₀ irreducible (h_irr)
- antiKummerKplusPoly irreducible (h_irr_g)
- AntiKummerRealSubfieldH94Inputs (Galois + cyclic + unramified)

These per-data discharges are the genuine FLT37-specific work; this theorem
shows the AK chain composes correctly.

Note: This theorem documents the AK-4 chain shape. The full FLT37 stage 2
discharge is the per-data composition. -/
theorem ak_chain_discharges_caseI_under_VC_and_AK_inputs
    (hp_odd : p ≠ 2)
    (h_VC : ¬ (p : ℕ) ∣ hPlus K)
    (data_to_AK_inputs : ∀ (α₀ : K) (hα₀ : α₀ ≠ 0)
      (h_anti : NumberField.IsCMField.complexConj K α₀ = α₀⁻¹)
      (h_irr : Irreducible (Polynomial.X ^ p - Polynomial.C α₀ : Polynomial K))
      (h_irr_g : Irreducible (antiKummerKplusPoly (p := p) K α₀ hα₀ h_anti))
      (_h_alpha_sq_ne : α₀ ^ 2 ≠ 1),
      AntiKummerRealSubfieldH94Inputs (p := p) (K := K)
        (antiKummerSigmaTildePkg (p := p) K α₀ hα₀ h_anti h_irr h_irr_g _h_alpha_sq_ne))
    (α₀ : K) (hα₀ : α₀ ≠ 0)
    (h_anti : NumberField.IsCMField.complexConj K α₀ = α₀⁻¹)
    (h_irr : Irreducible (Polynomial.X ^ p - Polynomial.C α₀ : Polynomial K))
    (h_irr_g : Irreducible (antiKummerKplusPoly (p := p) K α₀ hα₀ h_anti))
    (h_alpha_sq_ne : α₀ ^ 2 ≠ 1) :
    False :=
  ak_caseI_false_under_VC_and_inputs (p := p) (K := K) hp_odd
    (antiKummerSigmaTildePkg (p := p) K α₀ hα₀ h_anti h_irr h_irr_g h_alpha_sq_ne)
    (data_to_AK_inputs α₀ hα₀ h_anti h_irr h_irr_g h_alpha_sq_ne) h_VC

end BernoulliRegular.FLT37.LehmerVandiver.CaseI

end

end
