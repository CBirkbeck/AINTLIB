/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».FarguesFontaine.IntervalRing

/-!
# `A^r` inside the interval ring (Kedlaya §4, towards the presentations)

Kedlaya's Lemma *"Robba localizations"* (the third displayed isomorphism of
[kedlaya-noetherian-ff], §4) presents an interval ring as a quotient of a **radius-one**
Tate algebra over `A^r`,

  `A^r{T}/(pT - [z̄ⁿ]) ≅ B^{I}`,  `I = [-n⁻¹ log_c p, r]`,  `c = |z̄|`,

and Theorem *"strongly noetherian Robba2"* deduces from it that `B^I` is strongly
noetherian. Since the Tate algebra there has radius one, our Theorem 3.2
(`isStronglyNoetherian_ArSub`) applies verbatim; see decision AD-9 on the campaign board.

This file supplies the first ingredient: the **`A^r`-algebra structure on `B^I`**. The
point is that on `A_inf[1/[ϖ]]` — but *not* on `Bloc`, where `p` is inverted — the Gauss
value is monotone in the radius, so the smaller-radius map extends continuously to `A^r`
and `z ↦ (resAr z, z)` is a ring map `A^{ρ₂} → B^{[ρ₁,ρ₂]}`.

## Main definitions

* `FarguesFontaine.AlocToBloc` : the canonical map `A_inf[1/[ϖ]] → A_inf[1/(p[ϖ])]`.
* `FarguesFontaine.resAr` : the restriction `A^{ρ₂} → hatK ρ₁` for `ρ₁ ≤ ρ₂`.
* `FarguesFontaine.ArToBI` : the ring map `A^{ρ₂} → B^{[ρ₁,ρ₂]}`, `z ↦ (resAr z, z)`.

## Main results

* `FarguesFontaine.wAloc_mono_radius` : monotonicity of the Gauss value in the radius.
* `FarguesFontaine.tendsto_resAr` : the restriction is the limit of the approximants.
* `FarguesFontaine.ArToBI_injective` : `A^{ρ₂}` embeds in `B^{[ρ₁,ρ₂]}`.
* `FarguesFontaine.wI_ArToBI` : on `A^r` the interval norm is the `ρ₂`-value.
* `FarguesFontaine.wI_teichPowOverP_le_one` : the Tate variable `[z̄ⁿ]/p` is
  power-bounded exactly under Kedlaya's left-endpoint condition `|z̄|ⁿ ≤ ρ₁`.
* `FarguesFontaine.exists_eval_series` : a restricted series over `A^r` evaluated at a
  power-bounded element of `B^I` converges.
* `FarguesFontaine.tendsto_cauchy_product` : the partial sums of the Cauchy product
  converge to the product of the limits — multiplicativity of evaluation.
* `FarguesFontaine.evalArHom` : **evaluation as a ring homomorphism** `A^r⟨T⟩ →+* B^I`
  at any power-bounded element of `B^I` — Kedlaya's case-3 presentation map.
* `FarguesFontaine.sliceSeries`, `FarguesFontaine.sliceSeries_mul` : slicing a
  `(k+1)`-variable series into one-variable slices turns a product into the finite Cauchy
  product of slices — the reduction of the `k`-variable evaluation to the one-variable one
  (route (a) of AD-10).
* `FarguesFontaine.BISub_le_topologicalClosure_evalRange` : the image of the presentation
  map is **dense** in `B^I` (it contains the whole of `Bloc`).
* `FarguesFontaine.evalArMvHom` : **the `k`-variable presentation map**
  `A^r⟨T, T₁,…,T_k⟩ →+* B^I⟨T₁,…,T_k⟩`, whose surjectivity is what will make `B^I`
  strongly noetherian.

## Sources

* [Kedlaya, *Noetherian properties of Fargues–Fontaine curves*][kedlaya-noetherian-ff], §4.
-/

open TopologicalRing ValuationSpectrum WittVector NNReal

universe u

noncomputable section

namespace FarguesFontaine

variable (p : ℕ) [Fact (Nat.Prime p)]
variable (F : Type u) [Field F] [TopologicalSpace F] [IsTopologicalRing F]
  [UniformSpace F] [NonarchimedeanRing F] [IsPerfectoidField p F] [CharP F p]
variable (ϖ : PseudoUniformizer F)

/-- **Gauss terms are monotone in the radius** (all exponents are nonnegative). -/
theorem gaussTermF_mono_radius {ρ₁ ρ₂ : NNReal} (h12 : ρ₁ ≤ ρ₂) (x : WittVector p F)
    (n : ℕ) : gaussTermF p F ρ₁ x n ≤ gaussTermF p F ρ₂ x n := by
  rw [gaussTermF, gaussTermF]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ zero_le h12 n) zero_le

/-- **The Gauss value on `A_inf[1/[ϖ]]` is monotone in the radius**: at a smaller
radius an integral Witt series is smaller. This is what makes the restriction
`A^{ρ₂} → hatK ρ₁` continuous (and is false on `Bloc`, where `p` is inverted). -/
theorem wAloc_mono_radius {ρ₁ ρ₂ : NNReal} (hρ₁0 : 0 < ρ₁) (hρ₁1 : ρ₁ < 1)
    (hρ₂0 : 0 < ρ₂) (hρ₂1 : ρ₂ < 1) (h12 : ρ₁ ≤ ρ₂) (u : Aloc p F ϖ) :
    wAloc p F ϖ hρ₁0 hρ₁1 u ≤ wAloc p F ϖ hρ₂0 hρ₂1 u := by
  rw [← gaussValueF_alocToWittF p F ϖ hρ₁0 hρ₁1, ← gaussValueF_alocToWittF p F ϖ hρ₂0 hρ₂1,
    gaussValueF, gaussValueF]
  exact ciSup_mono (bddAbove_gaussTermF_alocToWittF p F ϖ hρ₂0 hρ₂1 u)
    (fun n => gaussTermF_mono_radius p F h12 _ n)

/-- The endpoint images of an `Aloc`-element compare in the same way. -/
theorem valued_AlocToHatK_mono {ρ₁ ρ₂ : NNReal} {hρ₁0 : 0 < ρ₁} {hρ₁1 : ρ₁ < 1}
    {hρ₂0 : 0 < ρ₂} {hρ₂1 : ρ₂ < 1} (h12 : ρ₁ ≤ ρ₂) (u : Aloc p F ϖ) :
    Valued.v (AlocToHatK p F ϖ hρ₁0 hρ₁1 u) ≤ Valued.v (AlocToHatK p F ϖ hρ₂0 hρ₂1 u) := by
  rw [valued_AlocToHatK, valued_AlocToHatK]
  exact wAloc_mono_radius p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 h12 u

/-- **Pairs of approximants of a point of `A^r` are eventually close.** -/
theorem eventually_pair_valued_le {ρ : NNReal} {hρ0 : 0 < ρ} {hρ1 : ρ < 1}
    (z : hatK p F hρ0 hρ1) {ε : NNReal} (hε : 0 < ε) :
    ∀ᶠ q in (Filter.comap (AlocToHatK p F ϖ hρ0 hρ1) (nhds z)) ×ˢ
        (Filter.comap (AlocToHatK p F ϖ hρ0 hρ1) (nhds z)),
      Valued.v (AlocToHatK p F ϖ hρ0 hρ1 (q.2 - q.1)) ≤ ε := by
  have hball : {w : hatK p F hρ0 hρ1 | Valued.v (w - z) ≤ ε} ∈ nhds z :=
    valued_ball_mem_nhds p F z hε
  refine Filter.mem_of_superset (Filter.prod_mem_prod
    (Filter.preimage_mem_comap hball) (Filter.preimage_mem_comap hball)) ?_
  rintro ⟨x, y⟩ ⟨hx, hy⟩
  have hx' : Valued.v (AlocToHatK p F ϖ hρ0 hρ1 x - z) ≤ ε := hx
  have hy' : Valued.v (AlocToHatK p F ϖ hρ0 hρ1 y - z) ≤ ε := hy
  show Valued.v (AlocToHatK p F ϖ hρ0 hρ1 (y - x)) ≤ ε
  rw [map_sub, ← sub_sub_sub_cancel_right (AlocToHatK p F ϖ hρ0 hρ1 y)
    (AlocToHatK p F ϖ hρ0 hρ1 x) z]
  exact le_trans (Valuation.map_sub _ _ _) (max_le hy' hx')

/-- **The restriction of `A^r` to a smaller radius**, defined as the limit of the
smaller-radius images along the approximant filter. -/
def resAr {ρ₁ ρ₂ : NNReal} (hρ₁0 : 0 < ρ₁) (hρ₁1 : ρ₁ < 1) (hρ₂0 : 0 < ρ₂)
    (hρ₂1 : ρ₂ < 1) (z : hatK p F hρ₂0 hρ₂1) : hatK p F hρ₁0 hρ₁1 :=
  Filter.limUnder (Filter.comap (AlocToHatK p F ϖ hρ₂0 hρ₂1) (nhds z))
    (fun u => AlocToHatK p F ϖ hρ₁0 hρ₁1 u)

/-- **The restriction map is the limit of the approximants.** -/
theorem tendsto_resAr {ρ₁ ρ₂ : NNReal} {hρ₁0 : 0 < ρ₁} {hρ₁1 : ρ₁ < 1}
    {hρ₂0 : 0 < ρ₂} {hρ₂1 : ρ₂ < 1} (h12 : ρ₁ ≤ ρ₂) {z : hatK p F hρ₂0 hρ₂1}
    (hz : z ∈ ArSub p F ϖ hρ₂0 hρ₂1) :
    Filter.Tendsto (fun u => AlocToHatK p F ϖ hρ₁0 hρ₁1 u)
      (Filter.comap (AlocToHatK p F ϖ hρ₂0 hρ₂1) (nhds z))
      (nhds (resAr p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 z)) := by
  haveI hne := neBot_comap_of_mem_ArSub p F ϖ hz
  set L := Filter.comap (AlocToHatK p F ϖ hρ₂0 hρ₂1) (nhds z) with hL
  set g : Aloc p F ϖ → hatK p F hρ₁0 hρ₁1 :=
    fun u => AlocToHatK p F ϖ hρ₁0 hρ₁1 u with hg
  have hcauchy : Cauchy (Filter.map g L) := by
    refine ⟨hne.map _, ?_⟩
    rw [Filter.prod_map_map_eq]
    intro V hV
    obtain ⟨γ, -, hγV⟩ :=
      (Valued.hasBasis_uniformity (hatK p F hρ₁0 hρ₁1) NNReal).mem_iff.mp hV
    obtain ⟨ε, hε0, hεγ⟩ := exists_nnreal_lt_gamma p F γ
    have hpairs := eventually_pair_valued_le p F ϖ z hε0
    rw [← hL] at hpairs
    rw [Filter.mem_map]
    refine Filter.mem_of_superset hpairs ?_
    rintro ⟨x, y⟩ hxy
    refine hγV ?_
    refine hεγ (g y - g x) ?_
    have hstep : Valued.v (AlocToHatK p F ϖ hρ₁0 hρ₁1 (y - x))
        ≤ Valued.v (AlocToHatK p F ϖ hρ₂0 hρ₂1 (y - x)) :=
      valued_AlocToHatK_mono p F ϖ h12 (y - x)
    rw [hg]
    simp only
    rw [← map_sub]
    exact le_trans hstep hxy
  obtain ⟨w, hw⟩ := CompleteSpace.complete hcauchy
  have hty : Filter.Tendsto g L (nhds w) := hw
  have heq : resAr p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 z = w := hty.limUnder_eq
  rw [heq]
  exact hty


/-- The canonical map `Aloc = A_inf[1/[ϖ]] → Bloc = A_inf[1/(p[ϖ])]`. -/
def AlocToBloc : Aloc p F ϖ →+* Bloc p F ϖ :=
  IsLocalization.lift (M := Submonoid.powers (teichPi p F ϖ))
    (g := algebraMap (Ainf p F) (Bloc p F ϖ))
    (by
      rintro ⟨y, k, rfl⟩
      rw [map_pow]
      exact (isUnit_teichPi_image p F ϖ).pow k)

@[simp]
theorem AlocToBloc_algebraMap (x : Ainf p F) :
    AlocToBloc p F ϖ (algebraMap (Ainf p F) (Aloc p F ϖ) x)
      = algebraMap (Ainf p F) (Bloc p F ϖ) x :=
  IsLocalization.lift_eq _ _

/-- The endpoint maps are compatible with `Aloc → Bloc`. -/
theorem BlocToHatK_AlocToBloc {ρ : NNReal} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (u : Aloc p F ϖ) :
    BlocToHatK p F ϖ hρ0 hρ1 (AlocToBloc p F ϖ u) = AlocToHatK p F ϖ hρ0 hρ1 u := by
  have hext : (BlocToHatK p F ϖ hρ0 hρ1).comp (AlocToBloc p F ϖ)
      = AlocToHatK p F ϖ hρ0 hρ1 := by
    refine IsLocalization.ringHom_ext (Submonoid.powers (teichPi p F ϖ)) ?_
    ext x
    simp only [RingHom.coe_comp, Function.comp_apply, AlocToBloc_algebraMap]
    rw [show BlocToHatK p F ϖ hρ0 hρ1 (algebraMap (Ainf p F) (Bloc p F ϖ) x)
        = toHatK p F hρ0 hρ1 x from IsLocalization.lift_eq _ _,
      show AlocToHatK p F ϖ hρ0 hρ1 (algebraMap (Ainf p F) (Aloc p F ϖ) x)
        = toHatK p F hρ0 hρ1 x from IsLocalization.lift_eq _ _]
  exact congrFun (congrArg (fun f : Aloc p F ϖ →+* hatK p F hρ0 hρ1 => (f : Aloc p F ϖ → _))
    hext) u


/-- Approximants of a sum are sums of approximants (filter form). -/
theorem map_add_comap_le_Ar {ρ : NNReal} {hρ0 : 0 < ρ} {hρ1 : ρ < 1}
    (z z' : hatK p F hρ0 hρ1) :
    Filter.map (fun q : Aloc p F ϖ × Aloc p F ϖ => q.1 + q.2)
        ((Filter.comap (AlocToHatK p F ϖ hρ0 hρ1) (nhds z)) ×ˢ
          (Filter.comap (AlocToHatK p F ϖ hρ0 hρ1) (nhds z')))
      ≤ Filter.comap (AlocToHatK p F ϖ hρ0 hρ1) (nhds (z + z')) := by
  rw [← Filter.map_le_iff_le_comap, Filter.map_map]
  have h1 : Filter.Tendsto (fun q : Aloc p F ϖ × Aloc p F ϖ =>
      AlocToHatK p F ϖ hρ0 hρ1 q.1)
      ((Filter.comap (AlocToHatK p F ϖ hρ0 hρ1) (nhds z)) ×ˢ
        (Filter.comap (AlocToHatK p F ϖ hρ0 hρ1) (nhds z'))) (nhds z) :=
    Filter.tendsto_comap.comp Filter.tendsto_fst
  have h2 : Filter.Tendsto (fun q : Aloc p F ϖ × Aloc p F ϖ =>
      AlocToHatK p F ϖ hρ0 hρ1 q.2)
      ((Filter.comap (AlocToHatK p F ϖ hρ0 hρ1) (nhds z)) ×ˢ
        (Filter.comap (AlocToHatK p F ϖ hρ0 hρ1) (nhds z'))) (nhds z') :=
    Filter.tendsto_comap.comp Filter.tendsto_snd
  have hsum := h1.add h2
  have hcongr : (AlocToHatK p F ϖ hρ0 hρ1)
        ∘ (fun q : Aloc p F ϖ × Aloc p F ϖ => q.1 + q.2)
      = fun q : Aloc p F ϖ × Aloc p F ϖ =>
        AlocToHatK p F ϖ hρ0 hρ1 q.1 + AlocToHatK p F ϖ hρ0 hρ1 q.2 := by
    funext q
    exact map_add _ _ _
  rw [hcongr]
  exact hsum

/-- Approximants of a product are products of approximants (filter form). -/
theorem map_mul_comap_le_Ar {ρ : NNReal} {hρ0 : 0 < ρ} {hρ1 : ρ < 1}
    (z z' : hatK p F hρ0 hρ1) :
    Filter.map (fun q : Aloc p F ϖ × Aloc p F ϖ => q.1 * q.2)
        ((Filter.comap (AlocToHatK p F ϖ hρ0 hρ1) (nhds z)) ×ˢ
          (Filter.comap (AlocToHatK p F ϖ hρ0 hρ1) (nhds z')))
      ≤ Filter.comap (AlocToHatK p F ϖ hρ0 hρ1) (nhds (z * z')) := by
  rw [← Filter.map_le_iff_le_comap, Filter.map_map]
  have h1 : Filter.Tendsto (fun q : Aloc p F ϖ × Aloc p F ϖ =>
      AlocToHatK p F ϖ hρ0 hρ1 q.1)
      ((Filter.comap (AlocToHatK p F ϖ hρ0 hρ1) (nhds z)) ×ˢ
        (Filter.comap (AlocToHatK p F ϖ hρ0 hρ1) (nhds z'))) (nhds z) :=
    Filter.tendsto_comap.comp Filter.tendsto_fst
  have h2 : Filter.Tendsto (fun q : Aloc p F ϖ × Aloc p F ϖ =>
      AlocToHatK p F ϖ hρ0 hρ1 q.2)
      ((Filter.comap (AlocToHatK p F ϖ hρ0 hρ1) (nhds z)) ×ˢ
        (Filter.comap (AlocToHatK p F ϖ hρ0 hρ1) (nhds z'))) (nhds z') :=
    Filter.tendsto_comap.comp Filter.tendsto_snd
  have hmul := h1.mul h2
  have hcongr : (AlocToHatK p F ϖ hρ0 hρ1)
        ∘ (fun q : Aloc p F ϖ × Aloc p F ϖ => q.1 * q.2)
      = fun q : Aloc p F ϖ × Aloc p F ϖ =>
        AlocToHatK p F ϖ hρ0 hρ1 q.1 * AlocToHatK p F ϖ hρ0 hρ1 q.2 := by
    funext q
    exact map_mul _ _ _
  rw [hcongr]
  exact hmul

/-- The `Aloc`-image lies in `A^r`. -/
theorem AlocToHatK_mem_ArSub {ρ : NNReal} {hρ0 : 0 < ρ} {hρ1 : ρ < 1} (u : Aloc p F ϖ) :
    AlocToHatK p F ϖ hρ0 hρ1 u ∈ ArSub p F ϖ hρ0 hρ1 :=
  Subring.le_topologicalClosure _ ⟨u, rfl⟩

/-- **The restriction map extends the smaller-radius map** on `Aloc`-images. -/
theorem resAr_AlocToHatK {ρ₁ ρ₂ : NNReal} {hρ₁0 : 0 < ρ₁} {hρ₁1 : ρ₁ < 1}
    {hρ₂0 : 0 < ρ₂} {hρ₂1 : ρ₂ < 1} (h12 : ρ₁ ≤ ρ₂) (u : Aloc p F ϖ) :
    resAr p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 (AlocToHatK p F ϖ hρ₂0 hρ₂1 u)
      = AlocToHatK p F ϖ hρ₁0 hρ₁1 u := by
  have hmem := AlocToHatK_mem_ArSub p F ϖ (hρ0 := hρ₂0) (hρ1 := hρ₂1) u
  haveI hne := neBot_comap_of_mem_ArSub p F ϖ hmem
  have hlim := tendsto_resAr p F ϖ (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1) h12 hmem
  have hlim2 : Filter.Tendsto (fun y => AlocToHatK p F ϖ hρ₁0 hρ₁1 y)
      (Filter.comap (AlocToHatK p F ϖ hρ₂0 hρ₂1)
        (nhds (AlocToHatK p F ϖ hρ₂0 hρ₂1 u)))
      (nhds (AlocToHatK p F ϖ hρ₁0 hρ₁1 u)) := by
    rw [Filter.tendsto_def]
    intro U hU
    obtain ⟨γ, hγ⟩ := (Valued.mem_nhds (R := hatK p F hρ₁0 hρ₁1)).mp hU
    obtain ⟨ε, hε0, hεγ⟩ := exists_nnreal_lt_gamma p F γ
    refine Filter.mem_of_superset
      (Filter.preimage_mem_comap (valued_ball_mem_nhds p F
        (AlocToHatK p F ϖ hρ₂0 hρ₂1 u) hε0)) ?_
    intro y hy
    have hy' : Valued.v (AlocToHatK p F ϖ hρ₂0 hρ₂1 y
      - AlocToHatK p F ϖ hρ₂0 hρ₂1 u) ≤ ε := hy
    refine hγ ?_
    refine hεγ _ ?_
    rw [← map_sub] at hy' ⊢
    exact le_trans (valued_AlocToHatK_mono p F ϖ h12 (y - u)) hy'
  exact tendsto_nhds_unique hlim hlim2

/-- **The restriction map is additive.** -/
theorem resAr_add {ρ₁ ρ₂ : NNReal} {hρ₁0 : 0 < ρ₁} {hρ₁1 : ρ₁ < 1}
    {hρ₂0 : 0 < ρ₂} {hρ₂1 : ρ₂ < 1} (h12 : ρ₁ ≤ ρ₂) {z z' : hatK p F hρ₂0 hρ₂1}
    (hz : z ∈ ArSub p F ϖ hρ₂0 hρ₂1) (hz' : z' ∈ ArSub p F ϖ hρ₂0 hρ₂1) :
    resAr p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 (z + z')
      = resAr p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 z + resAr p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 z' := by
  haveI hne := neBot_comap_of_mem_ArSub p F ϖ hz
  haveI hne' := neBot_comap_of_mem_ArSub p F ϖ hz'
  have h1 := tendsto_resAr p F ϖ (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1) h12 hz
  have h2 := tendsto_resAr p F ϖ (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1) h12 hz'
  have hsum := tendsto_resAr p F ϖ (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1) h12 (add_mem hz hz')
  have ha := (h1.comp Filter.tendsto_fst).add (h2.comp Filter.tendsto_snd)
  have hb := hsum.comp (map_add_comap_le_Ar p F ϖ z z')
  have hcongr : (fun y => AlocToHatK p F ϖ hρ₁0 hρ₁1 y)
        ∘ (fun q : Aloc p F ϖ × Aloc p F ϖ => q.1 + q.2)
      = fun q : Aloc p F ϖ × Aloc p F ϖ =>
        AlocToHatK p F ϖ hρ₁0 hρ₁1 q.1 + AlocToHatK p F ϖ hρ₁0 hρ₁1 q.2 := by
    funext q
    exact map_add _ _ _
  rw [hcongr] at hb
  exact tendsto_nhds_unique hb ha

/-- **The restriction map is multiplicative.** -/
theorem resAr_mul {ρ₁ ρ₂ : NNReal} {hρ₁0 : 0 < ρ₁} {hρ₁1 : ρ₁ < 1}
    {hρ₂0 : 0 < ρ₂} {hρ₂1 : ρ₂ < 1} (h12 : ρ₁ ≤ ρ₂) {z z' : hatK p F hρ₂0 hρ₂1}
    (hz : z ∈ ArSub p F ϖ hρ₂0 hρ₂1) (hz' : z' ∈ ArSub p F ϖ hρ₂0 hρ₂1) :
    resAr p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 (z * z')
      = resAr p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 z * resAr p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 z' := by
  haveI hne := neBot_comap_of_mem_ArSub p F ϖ hz
  haveI hne' := neBot_comap_of_mem_ArSub p F ϖ hz'
  have h1 := tendsto_resAr p F ϖ (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1) h12 hz
  have h2 := tendsto_resAr p F ϖ (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1) h12 hz'
  have hprod := tendsto_resAr p F ϖ (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1) h12 (mul_mem hz hz')
  have ha := (h1.comp Filter.tendsto_fst).mul (h2.comp Filter.tendsto_snd)
  have hb := hprod.comp (map_mul_comap_le_Ar p F ϖ z z')
  have hcongr : (fun y => AlocToHatK p F ϖ hρ₁0 hρ₁1 y)
        ∘ (fun q : Aloc p F ϖ × Aloc p F ϖ => q.1 * q.2)
      = fun q : Aloc p F ϖ × Aloc p F ϖ =>
        AlocToHatK p F ϖ hρ₁0 hρ₁1 q.1 * AlocToHatK p F ϖ hρ₁0 hρ₁1 q.2 := by
    funext q
    exact map_mul _ _ _
  rw [hcongr] at hb
  exact tendsto_nhds_unique hb ha

/-- **The graph of the restriction lands in the interval ring**: for `z ∈ A^{ρ₂}` the
pair `(resAr z, z)` lies in `B^{[ρ₁,ρ₂]}`. -/
theorem resAr_pair_mem {ρ₁ ρ₂ : NNReal} {hρ₁0 : 0 < ρ₁} {hρ₁1 : ρ₁ < 1}
    {hρ₂0 : 0 < ρ₂} {hρ₂1 : ρ₂ < 1} (h12 : ρ₁ ≤ ρ₂) {z : hatK p F hρ₂0 hρ₂1}
    (hz : z ∈ ArSub p F ϖ hρ₂0 hρ₂1) :
    (resAr p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 z, z) ∈ BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 := by
  haveI hne := neBot_comap_of_mem_ArSub p F ϖ hz
  have h1 := tendsto_resAr p F ϖ (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1) h12 hz
  have h2 : Filter.Tendsto (fun u => AlocToHatK p F ϖ hρ₂0 hρ₂1 u)
      (Filter.comap (AlocToHatK p F ϖ hρ₂0 hρ₂1) (nhds z)) (nhds z) :=
    Filter.tendsto_comap
  have hpair : Filter.Tendsto (fun u => (AlocToHatK p F ϖ hρ₁0 hρ₁1 u,
        AlocToHatK p F ϖ hρ₂0 hρ₂1 u))
      (Filter.comap (AlocToHatK p F ϖ hρ₂0 hρ₂1) (nhds z))
      (nhds (resAr p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 z, z)) :=
    Filter.Tendsto.prodMk_nhds h1 h2
  have hmem : ∀ᶠ u in Filter.comap (AlocToHatK p F ϖ hρ₂0 hρ₂1) (nhds z),
      (AlocToHatK p F ϖ hρ₁0 hρ₁1 u, AlocToHatK p F ϖ hρ₂0 hρ₂1 u)
        ∈ (Set.range (BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)) := by
    refine Filter.Eventually.of_forall fun u => ⟨AlocToBloc p F ϖ u, ?_⟩
    refine Prod.ext ?_ ?_
    · exact BlocToHatK_AlocToBloc p F ϖ hρ₁0 hρ₁1 u
    · exact BlocToHatK_AlocToBloc p F ϖ hρ₂0 hρ₂1 u
  exact mem_closure_of_tendsto hpair hmem


/-- **`A^{ρ₂}` sits inside the interval ring `B^{[ρ₁,ρ₂]}`** as the graph of the
restriction map: `z ↦ (resAr z, z)`. This is the `A^r`-algebra structure on `B^I`
that Kedlaya's presentations (Lemma "Robba localizations") use. -/
def ArToBI {ρ₁ ρ₂ : NNReal} {hρ₁0 : 0 < ρ₁} {hρ₁1 : ρ₁ < 1} {hρ₂0 : 0 < ρ₂}
    {hρ₂1 : ρ₂ < 1} (h12 : ρ₁ ≤ ρ₂) :
    ↥(ArSub p F ϖ hρ₂0 hρ₂1) →+* ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1) where
  toFun z := ⟨(resAr p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 (z : hatK p F hρ₂0 hρ₂1),
    (z : hatK p F hρ₂0 hρ₂1)), resAr_pair_mem p F ϖ h12 z.2⟩
  map_one' := by
    refine Subtype.ext (Prod.ext ?_ rfl)
    show resAr p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 (1 : hatK p F hρ₂0 hρ₂1) = 1
    rw [show (1 : hatK p F hρ₂0 hρ₂1) = AlocToHatK p F ϖ hρ₂0 hρ₂1 1 from (map_one _).symm,
      resAr_AlocToHatK p F ϖ (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1) h12, map_one]
  map_mul' := fun z z' => by
    refine Subtype.ext (Prod.ext ?_ rfl)
    exact resAr_mul p F ϖ (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1) h12 z.2 z'.2
  map_zero' := by
    refine Subtype.ext (Prod.ext ?_ rfl)
    show resAr p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 (0 : hatK p F hρ₂0 hρ₂1) = 0
    rw [show (0 : hatK p F hρ₂0 hρ₂1) = AlocToHatK p F ϖ hρ₂0 hρ₂1 0 from (map_zero _).symm,
      resAr_AlocToHatK p F ϖ (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1) h12, map_zero]
  map_add' := fun z z' => by
    refine Subtype.ext (Prod.ext ?_ rfl)
    exact resAr_add p F ϖ (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1) h12 z.2 z'.2

@[simp]
theorem ArToBI_snd {ρ₁ ρ₂ : NNReal} {hρ₁0 : 0 < ρ₁} {hρ₁1 : ρ₁ < 1} {hρ₂0 : 0 < ρ₂}
    {hρ₂1 : ρ₂ < 1} (h12 : ρ₁ ≤ ρ₂) (z : ↥(ArSub p F ϖ hρ₂0 hρ₂1)) :
    ((ArToBI p F ϖ (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1) h12 z :
        ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)) :
        (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)).2
      = (z : hatK p F hρ₂0 hρ₂1) := rfl

/-- The inclusion of `A^{ρ₂}` in the interval ring is injective. -/
theorem ArToBI_injective {ρ₁ ρ₂ : NNReal} {hρ₁0 : 0 < ρ₁} {hρ₁1 : ρ₁ < 1}
    {hρ₂0 : 0 < ρ₂} {hρ₂1 : ρ₂ < 1} (h12 : ρ₁ ≤ ρ₂) :
    Function.Injective (ArToBI p F ϖ (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1)
      (hρ₂0 := hρ₂0) (hρ₂1 := hρ₂1) h12) := by
  intro z z' hzz
  refine Subtype.ext ?_
  have h := congrArg (fun w : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1) =>
    ((w : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)).2)) hzz
  exact h

/-- **The restriction is contracting**: the smaller-radius value of an element of `A^r`
is at most its value. -/
theorem valued_resAr_le {ρ₁ ρ₂ : NNReal} {hρ₁0 : 0 < ρ₁} {hρ₁1 : ρ₁ < 1}
    {hρ₂0 : 0 < ρ₂} {hρ₂1 : ρ₂ < 1} (h12 : ρ₁ ≤ ρ₂) {z : hatK p F hρ₂0 hρ₂1}
    (hz : z ∈ ArSub p F ϖ hρ₂0 hρ₂1) :
    Valued.v (resAr p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 z) ≤ Valued.v z := by
  haveI hne := neBot_comap_of_mem_ArSub p F ϖ hz
  have hkey : ∀ ε : NNReal, 0 < ε →
      Valued.v (resAr p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 z) ≤ max (Valued.v z) ε := by
    intro ε hε
    have hlim := tendsto_resAr p F ϖ (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1) h12 hz
    have hev : ∀ᶠ u in Filter.comap (AlocToHatK p F ϖ hρ₂0 hρ₂1) (nhds z),
        AlocToHatK p F ϖ hρ₁0 hρ₁1 u
          ∈ {w : hatK p F hρ₁0 hρ₁1 | Valued.v w ≤ max (Valued.v z) ε} := by
      refine Filter.mem_of_superset
        (Filter.preimage_mem_comap (valued_ball_mem_nhds p F z hε)) ?_
      intro u hu
      have hu' : Valued.v (AlocToHatK p F ϖ hρ₂0 hρ₂1 u - z) ≤ ε := hu
      have h2 : Valued.v (AlocToHatK p F ϖ hρ₂0 hρ₂1 u) ≤ max (Valued.v z) ε := by
        have hsplit : AlocToHatK p F ϖ hρ₂0 hρ₂1 u
            = z + (AlocToHatK p F ϖ hρ₂0 hρ₂1 u - z) := by ring
        rw [hsplit]
        exact le_trans (Valuation.map_add _ _ _) (max_le_max (le_refl _) hu')
      exact le_trans (valued_AlocToHatK_mono p F ϖ h12 u) h2
    exact (isClosed_valued_ball p F (lt_of_lt_of_le hε (le_max_right _ _))).mem_of_tendsto
      hlim hev
  by_contra hcon
  push Not at hcon
  obtain ⟨ε, hε1, hε2⟩ := exists_between hcon
  have := hkey ε (lt_of_le_of_lt zero_le hε1)
  rw [max_eq_right hε1.le] at this
  exact absurd this (not_le.mpr hε2)

/-- **The interval norm of an element of `A^r`** is its `ρ₂`-value. -/
theorem wI_ArToBI {ρ₁ ρ₂ : NNReal} {hρ₁0 : 0 < ρ₁} {hρ₁1 : ρ₁ < 1} {hρ₂0 : 0 < ρ₂}
    {hρ₂1 : ρ₂ < 1} (h12 : ρ₁ ≤ ρ₂) (z : ↥(ArSub p F ϖ hρ₂0 hρ₂1)) :
    wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1 ((ArToBI p F ϖ (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1) h12 z :
        ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)) :
        (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1))
      = Valued.v (z : hatK p F hρ₂0 hρ₂1) := by
  show max (Valued.v (resAr p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 (z : hatK p F hρ₂0 hρ₂1)))
      (Valued.v (z : hatK p F hρ₂0 hρ₂1)) = _
  exact max_eq_right (valued_resAr_le p F ϖ h12 z.2)


/-- **The image of Kedlaya's Tate variable**: the element `[z̄ⁿ]/p` of `Bloc`, which the
case-3 presentation `A^r{T}/(pT - [z̄ⁿ]) ≅ B^I` sends `T` to. -/
def teichPowOverP (zb : OF F) (n : ℕ) : Bloc p F ϖ :=
  algebraMap (Ainf p F) (Bloc p F ϖ) (WittVector.teichmuller p zb ^ n)
    * ↑(isUnit_p_image p F ϖ).unit⁻¹

/-- The Gauss value of `[z̄ⁿ]/p` at radius `ρ` is `|z̄|ⁿ/ρ`. -/
theorem wLoc_teichPowOverP {ρ : NNReal} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (zb : OF F) (n : ℕ) :
    wLoc p F ϖ hρ0 hρ1 (teichPowOverP p F ϖ zb n)
      = (perfectoidValuation p F (zb : F)) ^ n / ρ := by
  rw [teichPowOverP, Valuation.map_mul, wLoc_algebraMap, wLoc_p_inv,
    ← map_pow (WittVector.teichmuller p), gaussValue_teichmuller p F hρ1.le]
  rw [show ((zb ^ n : OF F) : F) = (zb : F) ^ n from by push_cast; rfl, map_pow]
  exact (div_eq_mul_inv _ _).symm

/-- The interval norm of `[z̄ⁿ]/p` is `|z̄|ⁿ/ρ₁` (the smaller radius dominates). -/
theorem wI_teichPowOverP {ρ₁ ρ₂ : NNReal} {hρ₁0 : 0 < ρ₁} {hρ₁1 : ρ₁ < 1} {hρ₂0 : 0 < ρ₂}
    {hρ₂1 : ρ₂ < 1} (h12 : ρ₁ ≤ ρ₂) (zb : OF F) (n : ℕ) :
    wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1
        (BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 (teichPowOverP p F ϖ zb n))
      = (perfectoidValuation p F (zb : F)) ^ n / ρ₁ := by
  rw [wI_BIProd, valued_BlocToHatK, valued_BlocToHatK, wLoc_teichPowOverP,
    wLoc_teichPowOverP]
  refine max_eq_left (div_le_div_of_nonneg_left zero_le hρ₁0 h12)

/-- **Power-boundedness of the Tate variable** is exactly Kedlaya's left-endpoint
condition `ρ₁ ≥ |z̄|ⁿ` (in his coordinates, `s ≥ -n⁻¹ log_c p`). -/
theorem wI_teichPowOverP_le_one {ρ₁ ρ₂ : NNReal} {hρ₁0 : 0 < ρ₁} {hρ₁1 : ρ₁ < 1}
    {hρ₂0 : 0 < ρ₂} {hρ₂1 : ρ₂ < 1} (h12 : ρ₁ ≤ ρ₂) {zb : OF F} {n : ℕ}
    (hzb : (perfectoidValuation p F (zb : F)) ^ n ≤ ρ₁) :
    wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1
        (BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 (teichPowOverP p F ϖ zb n)) ≤ 1 := by
  rw [wI_teichPowOverP p F ϖ h12]
  exact div_le_one_of_le₀ hzb zero_le

/-- The Tate variable as an element of `B^I`. -/
def teichPowOverPElt {ρ₁ ρ₂ : NNReal} (hρ₁0 : 0 < ρ₁) (hρ₁1 : ρ₁ < 1) (hρ₂0 : 0 < ρ₂)
    (hρ₂1 : ρ₂ < 1) (zb : OF F) (n : ℕ) : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1) :=
  ⟨BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 (teichPowOverP p F ϖ zb n),
    BIProd_mem_BISub p F ϖ _⟩

/-- **The interval norm of a finite sum** is at most the largest term norm. -/
theorem wI_sum_le {ρ₁ ρ₂ : NNReal} {hρ₁0 : 0 < ρ₁} {hρ₁1 : ρ₁ < 1} {hρ₂0 : 0 < ρ₂}
    {hρ₂1 : ρ₂ < 1} {ι : Type*} (s : Finset ι)
    (f : ι → (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)) {c : NNReal}
    (hf : ∀ i ∈ s, wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1 (f i) ≤ c) :
    wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1 (∑ i ∈ s, f i) ≤ c := by
  classical
  induction s using Finset.induction with
  | empty =>
      rw [Finset.sum_empty, wI_zero p F]
      exact zero_le
  | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      refine le_trans (wI_add_le p F _ _) (max_le ?_ ?_)
      · exact hf a (Finset.mem_insert_self a s)
      · exact ih fun i hi => hf i (Finset.mem_insert_of_mem hi)

/-- **Evaluation of a restricted series over `A^r` at a power-bounded element of `B^I`
converges.** The bound is `wI(a_l · bˡ) ≤ v_{ρ₂}(a_l)`, which tends to `0` precisely
because the series is restricted. -/
theorem exists_eval_series {ρ₁ ρ₂ : NNReal} {hρ₁0 : 0 < ρ₁} {hρ₁1 : ρ₁ < 1}
    {hρ₂0 : 0 < ρ₂} {hρ₂1 : ρ₂ < 1} (h12 : ρ₁ ≤ ρ₂)
    (a : ℕ → ↥(ArSub p F ϖ hρ₂0 hρ₂1))
    (ha : Filter.Tendsto (fun l => Valued.v (a l : hatK p F hρ₂0 hρ₂1))
      Filter.atTop (nhds 0))
    {b : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)}
    (hbmem : b ∈ BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)
    (hb : wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1 b ≤ 1) :
    ∃ S : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1),
      S ∈ BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1
      ∧ Filter.Tendsto (fun n => ∑ l ∈ Finset.range n,
          ((ArToBI p F ϖ (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1) h12 (a l) :
            ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)) :
            (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)) * b ^ l)
        Filter.atTop (nhds S) := by
  refine exists_BI_series_limit p F ϖ (u := fun l =>
    ((ArToBI p F ϖ (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1) h12 (a l) :
      ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)) :
      (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)) * b ^ l)
    (fun l => mul_mem (ArToBI p F ϖ (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1) h12 (a l)).2
      (pow_mem hbmem l))
    (C := fun l => Valued.v (a l : hatK p F hρ₂0 hρ₂1)) (fun l => ?_) ha
  refine le_trans (wI_mul_le p F _ _) ?_
  rw [wI_ArToBI p F ϖ h12]
  calc Valued.v (a l : hatK p F hρ₂0 hρ₂1)
        * wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1 (b ^ l)
      ≤ Valued.v (a l : hatK p F hρ₂0 hρ₂1) * 1 := by
        refine mul_le_mul_of_nonneg_left ?_ zero_le
        rw [wI_pow p F]
        exact pow_le_one₀ zero_le hb
    _ = Valued.v (a l : hatK p F hρ₂0 hρ₂1) := mul_one _


/-- The antidiagonals below `N` tile the sub-`N` triangle of the square. -/
theorem biUnion_antidiagonal_eq (N : ℕ) :
    ((Finset.range N).biUnion (fun l => Finset.antidiagonal l))
      = (Finset.range N ×ˢ Finset.range N).filter (fun q : ℕ × ℕ => q.1 + q.2 < N) := by
  ext q
  simp only [Finset.mem_biUnion, Finset.mem_range, Finset.mem_antidiagonal,
    Finset.mem_filter, Finset.mem_product]
  constructor
  · rintro ⟨l, hl, rfl⟩
    exact ⟨⟨lt_of_le_of_lt (Nat.le_add_right _ _) hl,
      lt_of_le_of_lt (Nat.le_add_left _ _) hl⟩, hl⟩
  · rintro ⟨-, hlt⟩
    exact ⟨q.1 + q.2, hlt, rfl⟩

/-- **The Cauchy-product estimate**: the product of two partial sums differs from the
partial sum of the Cauchy product by a term of interval norm at most `ε·M`, provided the
two coefficient families are bounded by `M` and are `≤ ε` beyond `N₀`, and `N ≥ 2N₀`.
(Every missing index pair `(i,j)` has `i + j ≥ N`, hence `max i j ≥ N₀`.) -/
theorem wI_partial_cauchy_diff {ρ₁ ρ₂ : NNReal} {hρ₁0 : 0 < ρ₁} {hρ₁1 : ρ₁ < 1}
    {hρ₂0 : 0 < ρ₂} {hρ₂1 : ρ₂ < 1}
    {b : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)}
    (hb : wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1 b ≤ 1)
    (A A' : ℕ → (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1))
    {N₀ N : ℕ} (hN : 2 * N₀ ≤ N) {ε M : NNReal}
    (hA : ∀ i, wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1 (A i) ≤ M)
    (hA' : ∀ j, wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1 (A' j) ≤ M)
    (hAε : ∀ i, N₀ ≤ i → wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1 (A i) ≤ ε)
    (hA'ε : ∀ j, N₀ ≤ j → wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1 (A' j) ≤ ε) :
    wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1
        ((∑ i ∈ Finset.range N, A i * b ^ i) * (∑ j ∈ Finset.range N, A' j * b ^ j)
          - ∑ l ∈ Finset.range N,
            (∑ q ∈ Finset.antidiagonal l, A q.1 * A' q.2) * b ^ l)
      ≤ ε * M := by
  classical
  set g : ℕ × ℕ → (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1) :=
    fun q => A q.1 * A' q.2 * b ^ (q.1 + q.2) with hg
  have hprod : (∑ i ∈ Finset.range N, A i * b ^ i)
      * (∑ j ∈ Finset.range N, A' j * b ^ j)
      = ∑ q ∈ Finset.range N ×ˢ Finset.range N, g q := by
    rw [Finset.sum_product, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hg]
    simp only
    rw [pow_add]
    ring
  have hcauchy : (∑ l ∈ Finset.range N,
        (∑ q ∈ Finset.antidiagonal l, A q.1 * A' q.2) * b ^ l)
      = ∑ q ∈ (Finset.range N ×ˢ Finset.range N).filter
          (fun q : ℕ × ℕ => q.1 + q.2 < N), g q := by
    rw [← biUnion_antidiagonal_eq]
    rw [Finset.sum_biUnion]
    · refine Finset.sum_congr rfl fun l _ => ?_
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun q hq => ?_
      have hql : q.1 + q.2 = l := Finset.mem_antidiagonal.mp hq
      rw [hg]
      simp only
      rw [hql]
    · intro x hx y hy hxy
      simp only [Finset.disjoint_left, Finset.mem_antidiagonal]
      intro q hq hq'
      exact hxy (hq.symm.trans hq')
  have hsub : (Finset.range N ×ˢ Finset.range N).filter
      (fun q : ℕ × ℕ => q.1 + q.2 < N) ⊆ Finset.range N ×ˢ Finset.range N :=
    Finset.filter_subset _ _
  rw [hprod, hcauchy, ← Finset.sum_sdiff_eq_sub hsub]
  refine wI_sum_le p F _ g ?_
  intro q hq
  rw [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_product, Finset.mem_range,
    Finset.mem_range] at hq
  obtain ⟨⟨hq1, hq2⟩, hqbig⟩ := hq
  have hge : N ≤ q.1 + q.2 := by
    by_contra hlt
    exact hqbig ⟨⟨hq1, hq2⟩, Nat.not_le.mp hlt⟩
  have hmax : N₀ ≤ q.1 ∨ N₀ ≤ q.2 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨h1, h2⟩ := hcon
    omega
  have hterm : wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1 (g q)
      ≤ wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1 (A q.1) * wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1 (A' q.2) := by
    rw [hg]
    simp only
    refine le_trans (wI_mul_le p F _ _) ?_
    calc wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1 (A q.1 * A' q.2)
          * wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1 (b ^ (q.1 + q.2))
        ≤ wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1 (A q.1 * A' q.2) * 1 := by
          refine mul_le_mul_of_nonneg_left ?_ zero_le
          rw [wI_pow p F]
          exact pow_le_one₀ zero_le hb
      _ = wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1 (A q.1 * A' q.2) := mul_one _
      _ ≤ _ := wI_mul_le p F _ _
  refine le_trans hterm ?_
  rcases hmax with h | h
  · exact mul_le_mul (hAε q.1 h) (hA' q.2) zero_le zero_le
  · rw [mul_comm ε M]
    exact mul_le_mul (hA q.1) (hA'ε q.2 h) zero_le zero_le


/-- Interval-norm convergence to `0` is convergence to `0`. -/
theorem tendsto_zero_of_wI_tendsto_zero {ρ₁ ρ₂ : NNReal} {hρ₁0 : 0 < ρ₁} {hρ₁1 : ρ₁ < 1}
    {hρ₂0 : 0 < ρ₂} {hρ₂1 : ρ₂ < 1}
    {x : ℕ → (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)}
    (h : Filter.Tendsto (fun n => wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1 (x n))
      Filter.atTop (nhds 0)) :
    Filter.Tendsto x Filter.atTop (nhds 0) := by
  rw [Filter.tendsto_def]
  intro U hU
  obtain ⟨ε, hε, hεU⟩ := exists_wI_ball_subset p F (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1)
    (hρ₂0 := hρ₂0) (hρ₂1 := hρ₂1) hU
  have hev : ∀ᶠ n in Filter.atTop, wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1 (x n) ≤ ε :=
    h.eventually_le_const hε
  exact Filter.mem_of_superset hev fun n hn => hεU hn

/-- A null family is bounded. -/
theorem exists_bound_of_wI_tendsto_zero {ρ₁ ρ₂ : NNReal} {hρ₁0 : 0 < ρ₁} {hρ₁1 : ρ₁ < 1}
    {hρ₂0 : 0 < ρ₂} {hρ₂1 : ρ₂ < 1}
    {A : ℕ → (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)}
    (h : Filter.Tendsto (fun i => wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1 (A i))
      Filter.atTop (nhds 0)) :
    ∃ M : NNReal, ∀ i, wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1 (A i) ≤ M := by
  obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.mp (h.eventually_le_const zero_lt_one)
  refine ⟨max 1 ((Finset.range N₁).sup
    (fun i => wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1 (A i))), fun i => ?_⟩
  rcases le_or_gt N₁ i with hi | hi
  · exact le_trans (hN₁ i hi) (le_max_left _ _)
  · exact le_trans (Finset.le_sup (f := fun i => wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1 (A i))
      (Finset.mem_range.mpr hi)) (le_max_right _ _)

/-- **The Cauchy product converges to the product of the limits** — multiplicativity of
evaluation, in the form used to build the presentation map `A^r{T} → B^I`. -/
theorem tendsto_cauchy_product {ρ₁ ρ₂ : NNReal} {hρ₁0 : 0 < ρ₁} {hρ₁1 : ρ₁ < 1}
    {hρ₂0 : 0 < ρ₂} {hρ₂1 : ρ₂ < 1}
    {b : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)}
    (hb : wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1 b ≤ 1)
    (A A' : ℕ → (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1))
    (hA0 : Filter.Tendsto (fun i => wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1 (A i))
      Filter.atTop (nhds 0))
    (hA'0 : Filter.Tendsto (fun j => wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1 (A' j))
      Filter.atTop (nhds 0))
    {S S' : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)}
    (hS : Filter.Tendsto (fun n => ∑ i ∈ Finset.range n, A i * b ^ i)
      Filter.atTop (nhds S))
    (hS' : Filter.Tendsto (fun n => ∑ j ∈ Finset.range n, A' j * b ^ j)
      Filter.atTop (nhds S')) :
    Filter.Tendsto (fun n => ∑ l ∈ Finset.range n,
        (∑ q ∈ Finset.antidiagonal l, A q.1 * A' q.2) * b ^ l)
      Filter.atTop (nhds (S * S')) := by
  obtain ⟨M, hM⟩ := exists_bound_of_wI_tendsto_zero p F hA0
  obtain ⟨M', hM'⟩ := exists_bound_of_wI_tendsto_zero p F hA'0
  set MM : NNReal := max M M' with hMM
  have hMA : ∀ i, wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1 (A i) ≤ MM :=
    fun i => le_trans (hM i) (le_max_left _ _)
  have hMA' : ∀ j, wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1 (A' j) ≤ MM :=
    fun j => le_trans (hM' j) (le_max_right _ _)
  have hdiff : Filter.Tendsto (fun n =>
      (∑ i ∈ Finset.range n, A i * b ^ i) * (∑ j ∈ Finset.range n, A' j * b ^ j)
        - ∑ l ∈ Finset.range n,
          (∑ q ∈ Finset.antidiagonal l, A q.1 * A' q.2) * b ^ l)
      Filter.atTop (nhds 0) := by
    refine tendsto_zero_of_wI_tendsto_zero p F ?_
    refine tendsto_order.mpr ⟨fun c hc => absurd hc (not_lt.mpr zero_le), fun δ hδ => ?_⟩
    rw [Filter.eventually_atTop]
    rcases eq_or_lt_of_le (zero_le : (0 : NNReal) ≤ MM) with hMM0 | hMM0
    · refine ⟨0, fun n _ => ?_⟩
      have hAz : ∀ i, wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1 (A i) ≤ 0 := by
        intro i
        rw [hMM0]
        exact hMA i
      have hA'z : ∀ j, wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1 (A' j) ≤ 0 := by
        intro j
        rw [hMM0]
        exact hMA' j
      refine lt_of_le_of_lt (wI_partial_cauchy_diff p F hb A A' (N₀ := 0) (N := n)
        (by omega) hMA hMA' (fun i _ => hAz i) (fun j _ => hA'z j)) ?_
      rw [zero_mul]
      exact hδ
    · have hδ2 : (0 : NNReal) < δ / 2 := half_pos hδ
      obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.mp
        (hA0.eventually_le_const (div_pos hδ2 hMM0))
      obtain ⟨N₂, hN₂⟩ := Filter.eventually_atTop.mp
        (hA'0.eventually_le_const (div_pos hδ2 hMM0))
      refine ⟨2 * max N₁ N₂, fun n hn => ?_⟩
      refine lt_of_le_of_lt (wI_partial_cauchy_diff p F hb A A' (N₀ := max N₁ N₂)
        (N := n) hn hMA hMA'
        (fun i hi => hN₁ i (le_trans (le_max_left _ _) hi))
        (fun j hj => hN₂ j (le_trans (le_max_right _ _) hj))) ?_
      calc δ / 2 / MM * MM = δ / 2 := div_mul_cancel₀ _ hMM0.ne'
        _ < δ := NNReal.half_lt_self hδ.ne'

  have hPS := hS.mul hS'
  have hkey : Filter.Tendsto (fun n => ((∑ i ∈ Finset.range n, A i * b ^ i)
        * (∑ j ∈ Finset.range n, A' j * b ^ j))
      - ((∑ i ∈ Finset.range n, A i * b ^ i) * (∑ j ∈ Finset.range n, A' j * b ^ j)
        - ∑ l ∈ Finset.range n,
          (∑ q ∈ Finset.antidiagonal l, A q.1 * A' q.2) * b ^ l))
      Filter.atTop (nhds (S * S' - 0)) := hPS.sub hdiff
  rw [sub_zero] at hkey
  refine hkey.congr fun n => ?_
  exact sub_sub_cancel _ _

/-- The coefficient sequence of a one-variable power series. -/
def coeffSeq {A : Type*} [CommRing A] (f : MvPowerSeries (Fin 1) A) (n : ℕ) : A :=
  MvPowerSeries.coeff (Finsupp.single (0 : Fin 1) n) f

/-- The reindexing behind `coeffSeq`: every exponent in `Fin 1 →₀ ℕ` is a
`Finsupp.single 0 n`. Combined with `Function.Surjective.iSup_comp` this turns any
supremum over one-variable exponents into a supremum over `ℕ`. -/
theorem surjective_single_fin_one :
    Function.Surjective (fun n : ℕ => Finsupp.single (0 : Fin 1) n) := fun s =>
  ⟨s 0, Finsupp.ext fun i => by
    rw [Subsingleton.elim i (0 : Fin 1), Finsupp.single_eq_same]⟩

@[simp]
theorem coeffSeq_zero {A : Type*} [CommRing A] (n : ℕ) :
    coeffSeq (0 : MvPowerSeries (Fin 1) A) n = 0 := by
  rw [coeffSeq, map_zero]

theorem coeffSeq_add {A : Type*} [CommRing A] (f g : MvPowerSeries (Fin 1) A) (n : ℕ) :
    coeffSeq (f + g) n = coeffSeq f n + coeffSeq g n := by
  rw [coeffSeq, coeffSeq, coeffSeq, map_add]

theorem coeffSeq_one {A : Type*} [CommRing A] (n : ℕ) :
    coeffSeq (1 : MvPowerSeries (Fin 1) A) n = if n = 0 then 1 else 0 := by
  rw [coeffSeq, MvPowerSeries.coeff_one]
  by_cases h : n = 0
  · subst h
    simp
  · rw [if_neg h, if_neg]
    intro hcon
    exact h (Finsupp.single_eq_zero.mp hcon)

theorem coeffSeq_mul {A : Type*} [CommRing A] (f g : MvPowerSeries (Fin 1) A) (n : ℕ) :
    coeffSeq (f * g) n
      = ∑ q ∈ Finset.antidiagonal n, coeffSeq f q.1 * coeffSeq g q.2 := by
  classical
  rw [coeffSeq, MvPowerSeries.coeff_mul, Finsupp.antidiagonal_single, Finset.sum_map]
  rfl

/-- A restricted one-variable series over `A^r` has null coefficient values. -/
theorem tendsto_valued_coeffSeq {ρ : NNReal} {hρ0 : 0 < ρ} {hρ1 : ρ < 1}
    {f : MvPowerSeries (Fin 1) ↥(ArSub p F ϖ hρ0 hρ1)}
    (hf : MvPowerSeries.IsRestricted f) :
    Filter.Tendsto (fun n => Valued.v ((coeffSeq f n : ↥(ArSub p F ϖ hρ0 hρ1))
      : hatK p F hρ0 hρ1)) Filter.atTop (nhds 0) := by
  refine tendsto_order.mpr ⟨fun c hc => absurd hc (not_lt.mpr zero_le), fun δ hδ => ?_⟩
  have hfin := (isRestricted_iff_valued p F ϖ f).mp hf (δ / 2) (half_pos hδ)
  have hpre : ((fun n : ℕ => (Finsupp.single (0 : Fin 1) n)) ⁻¹'
      {s : Fin 1 →₀ ℕ | δ / 2 < Valued.v ((MvPowerSeries.coeff s f
        : ↥(ArSub p F ϖ hρ0 hρ1)) : hatK p F hρ0 hρ1)}).Finite :=
    hfin.preimage ((Finsupp.single_injective (0 : Fin 1)).injOn)
  obtain ⟨N, hN⟩ := hpre.bddAbove
  rw [Filter.eventually_atTop]
  refine ⟨N + 1, fun n hn => ?_⟩
  have hnot : n ∉ ((fun n : ℕ => (Finsupp.single (0 : Fin 1) n)) ⁻¹'
      {s : Fin 1 →₀ ℕ | δ / 2 < Valued.v ((MvPowerSeries.coeff s f
        : ↥(ArSub p F ϖ hρ0 hρ1)) : hatK p F hρ0 hρ1)}) := by
    intro hmem
    have := hN hmem
    omega
  exact lt_of_le_of_lt (not_lt.mp hnot) (NNReal.half_lt_self hδ.ne')


variable {ρ₁ ρ₂ : NNReal} {hρ₁0 : 0 < ρ₁} {hρ₁1 : ρ₁ < 1} {hρ₂0 : 0 < ρ₂} {hρ₂1 : ρ₂ < 1}

/-- The term of the evaluation series. -/
def evalTerm (h12 : ρ₁ ≤ ρ₂) (b : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1))
    (f : MvPowerSeries (Fin 1) ↥(ArSub p F ϖ hρ₂0 hρ₂1)) (l : ℕ) :
    (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1) :=
  ((ArToBI p F ϖ (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1) h12 (coeffSeq f l) :
    ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)) :
    (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)) * b ^ l

/-- **The value of a restricted series over `A^r` at a power-bounded element of `B^I`.** -/
def evalAr (h12 : ρ₁ ≤ ρ₂) {b : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)}
    (hbmem : b ∈ BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)
    (hb : wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1 b ≤ 1)
    (f : ↥(restrictedMvPowerSeriesSubring 1 ↥(ArSub p F ϖ hρ₂0 hρ₂1))) :
    (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1) :=
  (exists_eval_series p F ϖ h12 (coeffSeq (f : MvPowerSeries (Fin 1)
    ↥(ArSub p F ϖ hρ₂0 hρ₂1))) (tendsto_valued_coeffSeq p F ϖ f.2) hbmem hb).choose

theorem evalAr_mem (h12 : ρ₁ ≤ ρ₂) {b : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)}
    (hbmem : b ∈ BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)
    (hb : wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1 b ≤ 1)
    (f : ↥(restrictedMvPowerSeriesSubring 1 ↥(ArSub p F ϖ hρ₂0 hρ₂1))) :
    evalAr p F ϖ h12 hbmem hb f ∈ BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 :=
  (exists_eval_series p F ϖ h12 (coeffSeq (f : MvPowerSeries (Fin 1)
    ↥(ArSub p F ϖ hρ₂0 hρ₂1))) (tendsto_valued_coeffSeq p F ϖ f.2) hbmem hb).choose_spec.1

theorem tendsto_evalAr (h12 : ρ₁ ≤ ρ₂)
    {b : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)}
    (hbmem : b ∈ BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)
    (hb : wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1 b ≤ 1)
    (f : ↥(restrictedMvPowerSeriesSubring 1 ↥(ArSub p F ϖ hρ₂0 hρ₂1))) :
    Filter.Tendsto (fun n => ∑ l ∈ Finset.range n,
        evalTerm p F ϖ h12 b (f : MvPowerSeries (Fin 1) ↥(ArSub p F ϖ hρ₂0 hρ₂1)) l)
      Filter.atTop (nhds (evalAr p F ϖ h12 hbmem hb f)) :=
  (exists_eval_series p F ϖ h12 (coeffSeq (f : MvPowerSeries (Fin 1)
    ↥(ArSub p F ϖ hρ₂0 hρ₂1))) (tendsto_valued_coeffSeq p F ϖ f.2) hbmem hb).choose_spec.2

/-- The evaluation terms have null interval norm. -/
theorem tendsto_wI_evalTerm (h12 : ρ₁ ≤ ρ₂)
    {f : MvPowerSeries (Fin 1) ↥(ArSub p F ϖ hρ₂0 hρ₂1)}
    (hf : MvPowerSeries.IsRestricted f) :
    Filter.Tendsto (fun l => wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1
        ((ArToBI p F ϖ (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1) h12 (coeffSeq f l) :
          ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)) :
          (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)))
      Filter.atTop (nhds 0) := by
  refine (tendsto_valued_coeffSeq p F ϖ hf).congr fun l => ?_
  exact (wI_ArToBI p F ϖ h12 (coeffSeq f l)).symm


/-- Additivity of the inclusion, as a plain equation (avoids typeclass search on the
nested subring types). -/
theorem ArToBI_add {ρ₁ ρ₂ : NNReal} {hρ₁0 : 0 < ρ₁} {hρ₁1 : ρ₁ < 1} {hρ₂0 : 0 < ρ₂}
    {hρ₂1 : ρ₂ < 1} (h12 : ρ₁ ≤ ρ₂) (a a' : ↥(ArSub p F ϖ hρ₂0 hρ₂1)) :
    ArToBI p F ϖ (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1) h12 (a + a')
      = ArToBI p F ϖ (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1) h12 a
        + ArToBI p F ϖ (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1) h12 a' :=
  (ArToBI p F ϖ (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1) h12).map_add a a'

/-- Multiplicativity of the inclusion, as a plain equation. -/
theorem ArToBI_mul {ρ₁ ρ₂ : NNReal} {hρ₁0 : 0 < ρ₁} {hρ₁1 : ρ₁ < 1} {hρ₂0 : 0 < ρ₂}
    {hρ₂1 : ρ₂ < 1} (h12 : ρ₁ ≤ ρ₂) (a a' : ↥(ArSub p F ϖ hρ₂0 hρ₂1)) :
    ArToBI p F ϖ (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1) h12 (a * a')
      = ArToBI p F ϖ (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1) h12 a
        * ArToBI p F ϖ (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1) h12 a' :=
  (ArToBI p F ϖ (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1) h12).map_mul a a'

/-- The inclusion commutes with finite sums (proved by induction, so no
`AddMonoidHomClass` search is needed on the nested subring types). -/
theorem ArToBI_sum {ρ₁ ρ₂ : NNReal} {hρ₁0 : 0 < ρ₁} {hρ₁1 : ρ₁ < 1} {hρ₂0 : 0 < ρ₂}
    {hρ₂1 : ρ₂ < 1} (h12 : ρ₁ ≤ ρ₂) {ι : Type*} (s : Finset ι)
    (a : ι → ↥(ArSub p F ϖ hρ₂0 hρ₂1)) :
    ArToBI p F ϖ (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1) h12 (∑ i ∈ s, a i)
      = ∑ i ∈ s, ArToBI p F ϖ (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1) h12 (a i) := by
  classical
  induction s using Finset.induction with
  | empty =>
      rw [Finset.sum_empty, Finset.sum_empty]
      exact (ArToBI p F ϖ (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1) h12).map_zero
  | insert i s hi ih =>
      have hsplit : ArToBI p F ϖ (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1) h12
            (a i + ∑ j ∈ s, a j)
          = ArToBI p F ϖ (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1) h12 (a i)
            + ArToBI p F ϖ (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1) h12 (∑ j ∈ s, a j) :=
        ArToBI_add p F ϖ h12 (a i) (∑ j ∈ s, a j)
      rw [Finset.sum_insert hi, Finset.sum_insert hi, hsplit, ih]

/-- Evaluation is additive. -/
theorem evalAr_add (h12 : ρ₁ ≤ ρ₂) {b : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)}
    (hbmem : b ∈ BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)
    (hb : wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1 b ≤ 1)
    (f g : ↥(restrictedMvPowerSeriesSubring 1 ↥(ArSub p F ϖ hρ₂0 hρ₂1))) :
    evalAr p F ϖ h12 hbmem hb (f + g)
      = evalAr p F ϖ h12 hbmem hb f + evalAr p F ϖ h12 hbmem hb g := by
  refine tendsto_nhds_unique (tendsto_evalAr p F ϖ h12 hbmem hb (f + g)) ?_
  refine ((tendsto_evalAr p F ϖ h12 hbmem hb f).add
    (tendsto_evalAr p F ϖ h12 hbmem hb g)).congr fun n => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [evalTerm, evalTerm, evalTerm, ← add_mul]
  congr 1
  have hc : coeffSeq ((f + g : ↥(restrictedMvPowerSeriesSubring 1
        ↥(ArSub p F ϖ hρ₂0 hρ₂1))) : MvPowerSeries (Fin 1) ↥(ArSub p F ϖ hρ₂0 hρ₂1)) l
      = coeffSeq (f : MvPowerSeries (Fin 1) ↥(ArSub p F ϖ hρ₂0 hρ₂1)) l
        + coeffSeq (g : MvPowerSeries (Fin 1) ↥(ArSub p F ϖ hρ₂0 hρ₂1)) l :=
    coeffSeq_add _ _ _
  rw [hc, ArToBI_add p F ϖ (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1) h12]
  rfl

/-- **Evaluation is multiplicative** — the Cauchy-product estimate in action. -/
theorem evalAr_mul (h12 : ρ₁ ≤ ρ₂) {b : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)}
    (hbmem : b ∈ BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)
    (hb : wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1 b ≤ 1)
    (f g : ↥(restrictedMvPowerSeriesSubring 1 ↥(ArSub p F ϖ hρ₂0 hρ₂1))) :
    evalAr p F ϖ h12 hbmem hb (f * g)
      = evalAr p F ϖ h12 hbmem hb f * evalAr p F ϖ h12 hbmem hb g := by
  refine tendsto_nhds_unique (tendsto_evalAr p F ϖ h12 hbmem hb (f * g)) ?_
  have hcp := tendsto_cauchy_product p F hb
    (fun i => ((ArToBI p F ϖ (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1) h12
      (coeffSeq (f : MvPowerSeries (Fin 1) ↥(ArSub p F ϖ hρ₂0 hρ₂1)) i) :
      ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)) :
      (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)))
    (fun j => ((ArToBI p F ϖ (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1) h12
      (coeffSeq (g : MvPowerSeries (Fin 1) ↥(ArSub p F ϖ hρ₂0 hρ₂1)) j) :
      ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)) :
      (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)))
    (tendsto_wI_evalTerm p F ϖ h12 f.2) (tendsto_wI_evalTerm p F ϖ h12 g.2)
    (tendsto_evalAr p F ϖ h12 hbmem hb f) (tendsto_evalAr p F ϖ h12 hbmem hb g)
  refine hcp.congr fun n => ?_
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [evalTerm]
  congr 1
  have hc : coeffSeq ((f * g : ↥(restrictedMvPowerSeriesSubring 1
        ↥(ArSub p F ϖ hρ₂0 hρ₂1))) : MvPowerSeries (Fin 1) ↥(ArSub p F ϖ hρ₂0 hρ₂1)) l
      = ∑ q ∈ Finset.antidiagonal l,
          coeffSeq (f : MvPowerSeries (Fin 1) ↥(ArSub p F ϖ hρ₂0 hρ₂1)) q.1
          * coeffSeq (g : MvPowerSeries (Fin 1) ↥(ArSub p F ϖ hρ₂0 hρ₂1)) q.2 :=
    coeffSeq_mul _ _ _
  rw [hc, ArToBI_sum p F ϖ (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1) h12,
    AddSubmonoidClass.coe_finsetSum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [ArToBI_mul p F ϖ (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1) h12]
  rfl

/-- Evaluation sends `1` to `1`. -/
theorem evalAr_one (h12 : ρ₁ ≤ ρ₂) {b : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)}
    (hbmem : b ∈ BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)
    (hb : wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1 b ≤ 1) :
    evalAr p F ϖ h12 hbmem hb 1 = 1 := by
  refine tendsto_nhds_unique (tendsto_evalAr p F ϖ h12 hbmem hb 1) ?_
  refine tendsto_const_nhds.congr' ?_
  rw [Filter.EventuallyEq, Filter.eventually_atTop]
  refine ⟨1, fun n hn => ?_⟩
  have hterms : ∀ l ∈ Finset.range n,
      evalTerm p F ϖ h12 b (1 : MvPowerSeries (Fin 1) ↥(ArSub p F ϖ hρ₂0 hρ₂1)) l
        = if l = 0 then 1 else 0 := by
    intro l _
    rw [evalTerm, coeffSeq_one]
    by_cases hl : l = 0
    · subst hl
      rw [if_pos rfl, if_pos rfl, map_one, pow_zero, mul_one]
      rfl
    · rw [if_neg hl, if_neg hl, map_zero]
      show (0 : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)) * b ^ l = 0
      rw [zero_mul]
  show (1 : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1))
      = ∑ l ∈ Finset.range n,
        evalTerm p F ϖ h12 b (1 : MvPowerSeries (Fin 1) ↥(ArSub p F ϖ hρ₂0 hρ₂1)) l
  rw [Finset.sum_congr rfl hterms, Finset.sum_ite_eq' (Finset.range n) 0
    (fun _ => (1 : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)))]
  rw [if_pos (Finset.mem_range.mpr hn)]

/-- Evaluation sends `0` to `0`. -/
theorem evalAr_zero (h12 : ρ₁ ≤ ρ₂) {b : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)}
    (hbmem : b ∈ BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)
    (hb : wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1 b ≤ 1) :
    evalAr p F ϖ h12 hbmem hb 0 = 0 := by
  refine tendsto_nhds_unique (tendsto_evalAr p F ϖ h12 hbmem hb 0) ?_
  refine tendsto_const_nhds.congr fun n => ?_
  refine (Finset.sum_eq_zero fun l _ => ?_).symm
  rw [evalTerm]
  rw [show coeffSeq ((0 : ↥(restrictedMvPowerSeriesSubring 1
        ↥(ArSub p F ϖ hρ₂0 hρ₂1))) : MvPowerSeries (Fin 1) ↥(ArSub p F ϖ hρ₂0 hρ₂1)) l
      = 0 from coeffSeq_zero l, map_zero]
  show (0 : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)) * b ^ l = 0
  rw [zero_mul]

/-- **Evaluation at a power-bounded element of `B^I`, as a ring homomorphism**
`A^r⟨T⟩ →+* B^I` — Kedlaya's case-3 presentation map. -/
def evalArHom (h12 : ρ₁ ≤ ρ₂) {b : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)}
    (hbmem : b ∈ BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)
    (hb : wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1 b ≤ 1) :
    ↥(restrictedMvPowerSeriesSubring 1 ↥(ArSub p F ϖ hρ₂0 hρ₂1))
      →+* ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1) where
  toFun f := ⟨evalAr p F ϖ h12 hbmem hb f, evalAr_mem p F ϖ h12 hbmem hb f⟩
  map_one' := Subtype.ext (evalAr_one p F ϖ h12 hbmem hb)
  map_mul' := fun f g => Subtype.ext (evalAr_mul p F ϖ h12 hbmem hb f g)
  map_zero' := Subtype.ext (evalAr_zero p F ϖ h12 hbmem hb)
  map_add' := fun f g => Subtype.ext (evalAr_add p F ϖ h12 hbmem hb f g)

/-- `Finsupp.cons` is additive. -/
theorem cons_add {k : ℕ} (a₁ a₂ : ℕ) (b₁ b₂ : Fin k →₀ ℕ) :
    Finsupp.cons (a₁ + a₂) (b₁ + b₂)
      = Finsupp.cons a₁ b₁ + Finsupp.cons a₂ b₂ := by
  ext i
  refine Fin.cases ?_ ?_ i
  · simp only [Finsupp.cons_zero, Finsupp.add_apply, Finsupp.cons_zero]
  · intro j
    simp only [Finsupp.cons_succ, Finsupp.add_apply, Finsupp.cons_succ]

/-- `Finsupp.tail` is additive. -/
theorem tail_add {k : ℕ} (x y : Fin (k + 1) →₀ ℕ) :
    Finsupp.tail (x + y) = Finsupp.tail x + Finsupp.tail y := by
  ext i
  simp only [Finsupp.tail_apply, Finsupp.add_apply, Finsupp.tail_apply]

/-- **The antidiagonal of a `cons` splits**: pairs summing to `cons n I` are exactly the
pairs obtained by consing a pair summing to `n` onto a pair summing to `I`. -/
theorem antidiagonal_cons {k : ℕ} (n : ℕ) (I : Fin k →₀ ℕ) :
    Finset.antidiagonal (Finsupp.cons n I)
      = ((Finset.antidiagonal n) ×ˢ (Finset.antidiagonal I)).map
        ⟨fun q => (Finsupp.cons q.1.1 q.2.1, Finsupp.cons q.1.2 q.2.2), by
          rintro ⟨⟨a₁, a₂⟩, b₁, b₂⟩ ⟨⟨a₁', a₂'⟩, b₁', b₂'⟩ hq
          obtain ⟨h1, h2⟩ := Prod.mk.injEq .. ▸ hq
          obtain ⟨ha1, hb1⟩ := Finsupp.cons_injective2 h1
          obtain ⟨ha2, hb2⟩ := Finsupp.cons_injective2 h2
          simp only [Prod.mk.injEq]
          exact ⟨⟨ha1, ha2⟩, hb1, hb2⟩⟩ := by
  ext q
  simp only [Finset.mem_antidiagonal, Finset.mem_map, Finset.mem_product
    ]
  constructor
  · intro hq
    refine ⟨((q.1 0, q.2 0), (Finsupp.tail q.1, Finsupp.tail q.2)), ⟨?_, ?_⟩, ?_⟩
    · show q.1 0 + q.2 0 = n
      have := congrArg (fun m : Fin (k + 1) →₀ ℕ => m 0) hq
      simpa only [Finsupp.add_apply, Finsupp.cons_zero] using this
    · show Finsupp.tail q.1 + Finsupp.tail q.2 = I
      rw [← tail_add, hq, Finsupp.tail_cons]
    · refine Prod.ext ?_ ?_
      · exact Finsupp.cons_tail q.1
      · exact Finsupp.cons_tail q.2
  · rintro ⟨⟨a, b⟩, ⟨ha, hb⟩, rfl⟩
    show Finsupp.cons a.1 b.1 + Finsupp.cons a.2 b.2 = Finsupp.cons n I
    rw [← cons_add, ha, hb]


/-- A one-variable series is determined by its coefficient sequence. -/
theorem coeffSeq_ext {A : Type*} [CommRing A] {f g : MvPowerSeries (Fin 1) A}
    (h : ∀ n, coeffSeq f n = coeffSeq g n) : f = g := by
  ext m
  have hm : m = Finsupp.single (0 : Fin 1) (m 0) := by
    refine Finsupp.ext fun i => ?_
    rw [Subsingleton.elim i (0 : Fin 1), Finsupp.single_eq_same]
  rw [hm]
  exact h (m 0)

/-- **The slice of a `(k+1)`-variable series**: the one-variable series in the first
variable obtained by fixing the multi-index `I` in the remaining ones. -/
def sliceSeries {k : ℕ} {A : Type*} [CommRing A] (f : MvPowerSeries (Fin (k + 1)) A)
    (I : Fin k →₀ ℕ) : MvPowerSeries (Fin 1) A :=
  fun m => MvPowerSeries.coeff (Finsupp.cons (m 0) I) f

@[simp]
theorem coeffSeq_sliceSeries {k : ℕ} {A : Type*} [CommRing A]
    (f : MvPowerSeries (Fin (k + 1)) A) (I : Fin k →₀ ℕ) (n : ℕ) :
    coeffSeq (sliceSeries f I) n = MvPowerSeries.coeff (Finsupp.cons n I) f := by
  show MvPowerSeries.coeff (Finsupp.cons ((Finsupp.single (0 : Fin 1) n) 0) I) f
      = MvPowerSeries.coeff (Finsupp.cons n I) f
  rw [Finsupp.single_eq_same]

theorem sliceSeries_add {k : ℕ} {A : Type*} [CommRing A]
    (f g : MvPowerSeries (Fin (k + 1)) A) (I : Fin k →₀ ℕ) :
    sliceSeries (f + g) I = sliceSeries f I + sliceSeries g I := by
  refine coeffSeq_ext fun n => ?_
  rw [coeffSeq_sliceSeries, coeffSeq_add, coeffSeq_sliceSeries, coeffSeq_sliceSeries,
    map_add]

theorem sliceSeries_one {k : ℕ} {A : Type*} [CommRing A] (I : Fin k →₀ ℕ) :
    sliceSeries (1 : MvPowerSeries (Fin (k + 1)) A) I
      = if I = 0 then 1 else 0 := by
  refine coeffSeq_ext fun n => ?_
  rw [coeffSeq_sliceSeries, MvPowerSeries.coeff_one]
  by_cases hI : I = 0
  · subst hI
    rw [if_pos rfl, coeffSeq_one]
    by_cases hn : n = 0
    · subst hn
      rw [if_pos rfl, if_pos (Finsupp.cons_zero_zero)]
    · rw [if_neg hn, if_neg]
      exact Finsupp.cons_ne_zero_of_left (by simpa using hn)
  · rw [if_neg hI, coeffSeq_zero, if_neg]
    exact Finsupp.cons_ne_zero_of_right hI

theorem sliceSeries_zero {k : ℕ} {A : Type*} [CommRing A] (I : Fin k →₀ ℕ) :
    sliceSeries (0 : MvPowerSeries (Fin (k + 1)) A) I = 0 := by
  refine coeffSeq_ext fun n => ?_
  rw [coeffSeq_sliceSeries, map_zero, coeffSeq_zero]

/-- **Slicing turns a product into the finite Cauchy product of slices** — the identity
that reduces the `k`-variable evaluation to the one-variable one. -/
theorem sliceSeries_mul {k : ℕ} {A : Type*} [CommRing A]
    (f g : MvPowerSeries (Fin (k + 1)) A) (I : Fin k →₀ ℕ) :
    sliceSeries (f * g) I
      = ∑ q ∈ Finset.antidiagonal I, sliceSeries f q.1 * sliceSeries g q.2 := by
  classical
  refine coeffSeq_ext fun n => ?_
  rw [coeffSeq_sliceSeries, MvPowerSeries.coeff_mul, antidiagonal_cons, Finset.sum_map,
    Finset.sum_product_right]
  have hcoeff : coeffSeq (∑ q ∈ Finset.antidiagonal I,
        sliceSeries f q.1 * sliceSeries g q.2) n
      = ∑ q ∈ Finset.antidiagonal I,
        coeffSeq (sliceSeries f q.1 * sliceSeries g q.2) n := by
    show MvPowerSeries.coeff (Finsupp.single (0 : Fin 1) n)
        (∑ q ∈ Finset.antidiagonal I, sliceSeries f q.1 * sliceSeries g q.2)
      = ∑ q ∈ Finset.antidiagonal I,
        MvPowerSeries.coeff (Finsupp.single (0 : Fin 1) n)
          (sliceSeries f q.1 * sliceSeries g q.2)
    exact map_sum _ _ _
  rw [hcoeff]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [coeffSeq_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [coeffSeq_sliceSeries, coeffSeq_sliceSeries]
  rfl

/-- **Evaluation is norm-decreasing**: if every coefficient has value at most `ε`, so does
the value of the series. -/
theorem wI_evalAr_le (h12 : ρ₁ ≤ ρ₂)
    {b : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)}
    (hbmem : b ∈ BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)
    (hb : wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1 b ≤ 1)
    (f : ↥(restrictedMvPowerSeriesSubring 1 ↥(ArSub p F ϖ hρ₂0 hρ₂1)))
    {ε : NNReal} (hε : 0 < ε)
    (hf : ∀ l, Valued.v ((coeffSeq (f : MvPowerSeries (Fin 1)
      ↥(ArSub p F ϖ hρ₂0 hρ₂1)) l : ↥(ArSub p F ϖ hρ₂0 hρ₂1))
      : hatK p F hρ₂0 hρ₂1) ≤ ε) :
    wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1 (evalAr p F ϖ h12 hbmem hb f) ≤ ε := by
  refine (isClosed_wI_ball p F hε).mem_of_tendsto (tendsto_evalAr p F ϖ h12 hbmem hb f)
    (Filter.Eventually.of_forall fun n => ?_)
  refine wI_sum_le p F _ _ (fun l _ => ?_)
  rw [evalTerm]
  refine le_trans (wI_mul_le p F _ _) ?_
  rw [wI_ArToBI p F ϖ h12]
  calc Valued.v ((coeffSeq (f : MvPowerSeries (Fin 1) ↥(ArSub p F ϖ hρ₂0 hρ₂1)) l
        : ↥(ArSub p F ϖ hρ₂0 hρ₂1)) : hatK p F hρ₂0 hρ₂1)
        * wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1 (b ^ l)
      ≤ ε * 1 := by
        refine mul_le_mul (hf l) ?_ zero_le zero_le
        rw [wI_pow p F]
        exact pow_le_one₀ zero_le hb
    _ = ε := mul_one ε

/-- Each slice of a restricted `(k+1)`-variable series is restricted. -/
theorem isRestricted_sliceSeries {k : ℕ}
    {f : MvPowerSeries (Fin (k + 1)) ↥(ArSub p F ϖ hρ₂0 hρ₂1)}
    (hf : MvPowerSeries.IsRestricted f) (I : Fin k →₀ ℕ) :
    MvPowerSeries.IsRestricted (sliceSeries f I) := by
  rw [isRestricted_iff_valued]
  intro ε hε
  have hfin := (isRestricted_iff_valued p F ϖ f).mp hf ε hε
  have hmap : {s : Fin 1 →₀ ℕ | ε < Valued.v ((MvPowerSeries.coeff s (sliceSeries f I)
      : ↥(ArSub p F ϖ hρ₂0 hρ₂1)) : hatK p F hρ₂0 hρ₂1)}
      ⊆ (fun s : Fin 1 →₀ ℕ => Finsupp.cons (s 0) I) ⁻¹'
        {m : Fin (k + 1) →₀ ℕ | ε < Valued.v ((MvPowerSeries.coeff m f
          : ↥(ArSub p F ϖ hρ₂0 hρ₂1)) : hatK p F hρ₂0 hρ₂1)} := by
    intro s hs
    exact hs
  refine Set.Finite.subset ?_ hmap
  refine hfin.preimage ?_
  intro s _ t _ hst
  refine Finsupp.ext fun i => ?_
  rw [Subsingleton.elim i (0 : Fin 1)]
  exact (Finsupp.cons_injective2 hst).1


/-- The interval-norm criterion for restrictedness over `B^I`. -/
theorem isRestricted_of_wI {k : ℕ}
    {c : MvPowerSeries (Fin k) ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)}
    (h : ∀ ε : NNReal, 0 < ε → {I : Fin k →₀ ℕ | ε < wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1
      ((MvPowerSeries.coeff I c : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
        : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1))}.Finite) :
    MvPowerSeries.IsRestricted c := by
  intro U hU
  obtain ⟨V, hV, hVU⟩ := (mem_nhds_subtype
    (BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 : Set ((hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)))
    (0 : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)) U).mp hU
  obtain ⟨ε, hε, hεV⟩ := exists_wI_ball_subset p F (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1)
    (hρ₂0 := hρ₂0) (hρ₂1 := hρ₂1) hV
  rw [Filter.mem_map, Filter.mem_cofinite]
  refine Set.Finite.subset (h ε hε) fun I hI => ?_
  by_contra hcon
  refine hI ?_
  have hle : wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1
      ((MvPowerSeries.coeff I c : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
        : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)) ≤ ε := not_lt.mp hcon
  exact hVU (hεV hle)

/-- Additivity of the bundled evaluation map (from the product-level lemma, so no class
search on the nested subring types). -/
theorem evalArHom_add (h12 : ρ₁ ≤ ρ₂)
    {b : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)}
    (hbmem : b ∈ BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)
    (hb : wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1 b ≤ 1)
    (f g : ↥(restrictedMvPowerSeriesSubring 1 ↥(ArSub p F ϖ hρ₂0 hρ₂1))) :
    evalArHom p F ϖ h12 hbmem hb (f + g)
      = evalArHom p F ϖ h12 hbmem hb f + evalArHom p F ϖ h12 hbmem hb g :=
  Subtype.ext (evalAr_add p F ϖ h12 hbmem hb f g)

/-- Multiplicativity of the bundled evaluation map. -/
theorem evalArHom_mul (h12 : ρ₁ ≤ ρ₂)
    {b : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)}
    (hbmem : b ∈ BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)
    (hb : wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1 b ≤ 1)
    (f g : ↥(restrictedMvPowerSeriesSubring 1 ↥(ArSub p F ϖ hρ₂0 hρ₂1))) :
    evalArHom p F ϖ h12 hbmem hb (f * g)
      = evalArHom p F ϖ h12 hbmem hb f * evalArHom p F ϖ h12 hbmem hb g :=
  Subtype.ext (evalAr_mul p F ϖ h12 hbmem hb f g)

/-- The bundled evaluation map sends `1` to `1`. -/
theorem evalArHom_one (h12 : ρ₁ ≤ ρ₂)
    {b : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)}
    (hbmem : b ∈ BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)
    (hb : wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1 b ≤ 1) :
    evalArHom p F ϖ h12 hbmem hb 1 = 1 :=
  Subtype.ext (evalAr_one p F ϖ h12 hbmem hb)

/-- The bundled evaluation map sends `0` to `0`. -/
theorem evalArHom_zero (h12 : ρ₁ ≤ ρ₂)
    {b : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)}
    (hbmem : b ∈ BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)
    (hb : wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1 b ≤ 1) :
    evalArHom p F ϖ h12 hbmem hb 0 = 0 :=
  Subtype.ext (evalAr_zero p F ϖ h12 hbmem hb)

/-- The `T`-slice of a restricted `(k+1)`-variable series, as an element of the
one-variable restricted series ring. Naming the bundled element keeps it opaque in later
goals, which is what keeps the ring-hom proofs below cheap. -/
def sliceElt {ρ : NNReal} {hρ0 : 0 < ρ} {hρ1 : ρ < 1} {k : ℕ}
    (f : ↥(restrictedMvPowerSeriesSubring (k + 1) ↥(ArSub p F ϖ hρ0 hρ1)))
    (I : Fin k →₀ ℕ) :
    ↥(restrictedMvPowerSeriesSubring 1 ↥(ArSub p F ϖ hρ0 hρ1)) :=
  ⟨sliceSeries (f : MvPowerSeries (Fin (k + 1)) ↥(ArSub p F ϖ hρ0 hρ1)) I,
    isRestricted_sliceSeries p F ϖ f.2 I⟩

@[simp]
theorem coeffSeq_sliceElt {ρ : NNReal} {hρ0 : 0 < ρ} {hρ1 : ρ < 1} {k : ℕ}
    (f : ↥(restrictedMvPowerSeriesSubring (k + 1) ↥(ArSub p F ϖ hρ0 hρ1)))
    (I : Fin k →₀ ℕ) (n : ℕ) :
    coeffSeq ((sliceElt p F ϖ f I : ↥(restrictedMvPowerSeriesSubring 1
        ↥(ArSub p F ϖ hρ0 hρ1))) : MvPowerSeries (Fin 1) ↥(ArSub p F ϖ hρ0 hρ1)) n
      = MvPowerSeries.coeff (Finsupp.cons n I)
        (f : MvPowerSeries (Fin (k + 1)) ↥(ArSub p F ϖ hρ0 hρ1)) :=
  coeffSeq_sliceSeries _ I n

/-- The slice of a sum. -/
theorem sliceElt_add {ρ : NNReal} {hρ0 : 0 < ρ} {hρ1 : ρ < 1} {k : ℕ}
    (f g : ↥(restrictedMvPowerSeriesSubring (k + 1) ↥(ArSub p F ϖ hρ0 hρ1)))
    (I : Fin k →₀ ℕ) :
    sliceElt p F ϖ (f + g) I = sliceElt p F ϖ f I + sliceElt p F ϖ g I :=
  Subtype.ext (sliceSeries_add _ _ I)

/-- The slice of `0`. -/
theorem sliceElt_zero {ρ : NNReal} {hρ0 : 0 < ρ} {hρ1 : ρ < 1} {k : ℕ}
    (I : Fin k →₀ ℕ) :
    sliceElt p F ϖ (0 : ↥(restrictedMvPowerSeriesSubring (k + 1)
      ↥(ArSub p F ϖ hρ0 hρ1))) I = 0 :=
  Subtype.ext (by
    show sliceSeries ((0 : ↥(restrictedMvPowerSeriesSubring (k + 1)
        ↥(ArSub p F ϖ hρ0 hρ1))) : MvPowerSeries (Fin (k + 1))
        ↥(ArSub p F ϖ hρ0 hρ1)) I
      = ((0 : ↥(restrictedMvPowerSeriesSubring 1 ↥(ArSub p F ϖ hρ0 hρ1)))
        : MvPowerSeries (Fin 1) ↥(ArSub p F ϖ hρ0 hρ1))
    rw [ZeroMemClass.coe_zero, sliceSeries_zero, ZeroMemClass.coe_zero])

/-- The slice of `1`. -/
theorem sliceElt_one {ρ : NNReal} {hρ0 : 0 < ρ} {hρ1 : ρ < 1} {k : ℕ}
    (I : Fin k →₀ ℕ) :
    sliceElt p F ϖ (1 : ↥(restrictedMvPowerSeriesSubring (k + 1)
      ↥(ArSub p F ϖ hρ0 hρ1))) I = if I = 0 then 1 else 0 :=
  Subtype.ext (by
    show sliceSeries ((1 : ↥(restrictedMvPowerSeriesSubring (k + 1)
        ↥(ArSub p F ϖ hρ0 hρ1))) : MvPowerSeries (Fin (k + 1))
        ↥(ArSub p F ϖ hρ0 hρ1)) I
      = ((if I = 0 then 1 else 0 : ↥(restrictedMvPowerSeriesSubring 1
        ↥(ArSub p F ϖ hρ0 hρ1))) : MvPowerSeries (Fin 1) ↥(ArSub p F ϖ hρ0 hρ1))
    rw [OneMemClass.coe_one, sliceSeries_one]
    by_cases hI : I = 0
    · rw [if_pos hI, if_pos hI, OneMemClass.coe_one]
    · rw [if_neg hI, if_neg hI, ZeroMemClass.coe_zero])

/-- The slice of a product is the finite Cauchy product of slices. -/
theorem sliceElt_mul {ρ : NNReal} {hρ0 : 0 < ρ} {hρ1 : ρ < 1} {k : ℕ}
    (f g : ↥(restrictedMvPowerSeriesSubring (k + 1) ↥(ArSub p F ϖ hρ0 hρ1)))
    (I : Fin k →₀ ℕ) :
    sliceElt p F ϖ (f * g) I
      = ∑ q ∈ Finset.antidiagonal I, sliceElt p F ϖ f q.1 * sliceElt p F ϖ g q.2 :=
  Subtype.ext (by
    show sliceSeries ((f * g : ↥(restrictedMvPowerSeriesSubring (k + 1)
        ↥(ArSub p F ϖ hρ0 hρ1))) : MvPowerSeries (Fin (k + 1))
        ↥(ArSub p F ϖ hρ0 hρ1)) I
      = ((∑ q ∈ Finset.antidiagonal I, sliceElt p F ϖ f q.1 * sliceElt p F ϖ g q.2
        : ↥(restrictedMvPowerSeriesSubring 1 ↥(ArSub p F ϖ hρ0 hρ1)))
        : MvPowerSeries (Fin 1) ↥(ArSub p F ϖ hρ0 hρ1))
    rw [AddSubmonoidClass.coe_finsetSum]
    exact sliceSeries_mul _ _ I)

/-- **The `k`-variable presentation map**, coefficientwise: slice, then evaluate. -/
def evalArMvFun (h12 : ρ₁ ≤ ρ₂)
    {b : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)}
    (hbmem : b ∈ BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)
    (hb : wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1 b ≤ 1) {k : ℕ}
    (f : ↥(restrictedMvPowerSeriesSubring (k + 1) ↥(ArSub p F ϖ hρ₂0 hρ₂1))) :
    MvPowerSeries (Fin k) ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1) :=
  fun I => evalArHom p F ϖ h12 hbmem hb (sliceElt p F ϖ f I)

@[simp]
theorem evalArMvFun_apply (h12 : ρ₁ ≤ ρ₂)
    {b : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)}
    (hbmem : b ∈ BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)
    (hb : wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1 b ≤ 1) {k : ℕ}
    (f : ↥(restrictedMvPowerSeriesSubring (k + 1) ↥(ArSub p F ϖ hρ₂0 hρ₂1)))
    (I : Fin k →₀ ℕ) :
    evalArMvFun p F ϖ h12 hbmem hb f I
      = evalArHom p F ϖ h12 hbmem hb (sliceElt p F ϖ f I) := rfl

/-- Evaluation commutes with finite sums, at the level of the ambient product (where the
ring operations are cheap). -/
theorem evalAr_sum (h12 : ρ₁ ≤ ρ₂)
    {b : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)}
    (hbmem : b ∈ BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)
    (hb : wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1 b ≤ 1) {ι : Type*} (s : Finset ι)
    (f : ι → ↥(restrictedMvPowerSeriesSubring 1 ↥(ArSub p F ϖ hρ₂0 hρ₂1))) :
    evalAr p F ϖ h12 hbmem hb (∑ i ∈ s, f i)
      = ∑ i ∈ s, evalAr p F ϖ h12 hbmem hb (f i) := by
  refine Finset.cons_induction ?_ ?_ s
  · rw [Finset.sum_empty, Finset.sum_empty]
    exact evalAr_zero p F ϖ h12 hbmem hb
  · intro a t ha ih
    rw [Finset.sum_cons, Finset.sum_cons,
      evalAr_add p F ϖ h12 hbmem hb (f a) (∑ i ∈ t, f i), ih]

/-- The bundled evaluation map commutes with finite sums. -/
theorem evalArHom_sum (h12 : ρ₁ ≤ ρ₂)
    {b : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)}
    (hbmem : b ∈ BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)
    (hb : wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1 b ≤ 1) {ι : Type*} (s : Finset ι)
    (f : ι → ↥(restrictedMvPowerSeriesSubring 1 ↥(ArSub p F ϖ hρ₂0 hρ₂1))) :
    evalArHom p F ϖ h12 hbmem hb (∑ i ∈ s, f i)
      = ∑ i ∈ s, evalArHom p F ϖ h12 hbmem hb (f i) := by
  refine Subtype.ext ?_
  show evalAr p F ϖ h12 hbmem hb (∑ i ∈ s, f i)
    = ((∑ i ∈ s, evalArHom p F ϖ h12 hbmem hb (f i)
      : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
      : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1))
  rw [AddSubmonoidClass.coe_finsetSum, evalAr_sum p F ϖ h12 hbmem hb s f]
  rfl

/-- The `k`-variable presentation map lands in the restricted series over `B^I`. -/
theorem isRestricted_evalArMvFun (h12 : ρ₁ ≤ ρ₂)
    {b : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)}
    (hbmem : b ∈ BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)
    (hb : wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1 b ≤ 1) {k : ℕ}
    (f : ↥(restrictedMvPowerSeriesSubring (k + 1) ↥(ArSub p F ϖ hρ₂0 hρ₂1))) :
    MvPowerSeries.IsRestricted (evalArMvFun p F ϖ h12 hbmem hb f) := by
  refine isRestricted_of_wI p F ϖ fun ε hε => ?_
  have hfin := (isRestricted_iff_valued p F ϖ
    (f : MvPowerSeries (Fin (k + 1)) ↥(ArSub p F ϖ hρ₂0 hρ₂1))).mp f.2 ε hε
  refine Set.Finite.subset (hfin.image Finsupp.tail) fun I hI => ?_
  have hIlt : ε < wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1
      ((evalArMvFun p F ϖ h12 hbmem hb f I :
        ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
        : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)) := hI
  by_contra hcon
  refine absurd hIlt (not_lt.mpr ?_)
  refine wI_evalAr_le p F ϖ h12 hbmem hb (sliceElt p F ϖ f I) hε fun l => ?_
  by_contra hcoefflt
  refine hcon ⟨Finsupp.cons l I, ?_, Finsupp.tail_cons l I⟩
  show ε < Valued.v ((MvPowerSeries.coeff (Finsupp.cons l I)
    (f : MvPowerSeries (Fin (k + 1)) ↥(ArSub p F ϖ hρ₂0 hρ₂1))
      : ↥(ArSub p F ϖ hρ₂0 hρ₂1)) : hatK p F hρ₂0 hρ₂1)
  have := not_le.mp hcoefflt
  rwa [coeffSeq_sliceElt] at this


/-- The `k`-variable map is additive. -/
theorem evalArMvFun_add (h12 : ρ₁ ≤ ρ₂)
    {b : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)}
    (hbmem : b ∈ BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)
    (hb : wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1 b ≤ 1) {k : ℕ}
    (f g : ↥(restrictedMvPowerSeriesSubring (k + 1) ↥(ArSub p F ϖ hρ₂0 hρ₂1))) :
    evalArMvFun p F ϖ h12 hbmem hb (f + g)
      = evalArMvFun p F ϖ h12 hbmem hb f + evalArMvFun p F ϖ h12 hbmem hb g := by
  funext I
  show evalArHom p F ϖ h12 hbmem hb (sliceElt p F ϖ (f + g) I)
    = evalArHom p F ϖ h12 hbmem hb (sliceElt p F ϖ f I)
      + evalArHom p F ϖ h12 hbmem hb (sliceElt p F ϖ g I)
  rw [sliceElt_add,
    evalArHom_add p F ϖ h12 hbmem hb (sliceElt p F ϖ f I) (sliceElt p F ϖ g I)]

/-- The `k`-variable map sends `0` to `0`. -/
theorem evalArMvFun_zero (h12 : ρ₁ ≤ ρ₂)
    {b : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)}
    (hbmem : b ∈ BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)
    (hb : wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1 b ≤ 1) {k : ℕ} :
    evalArMvFun p F ϖ h12 hbmem hb
        (0 : ↥(restrictedMvPowerSeriesSubring (k + 1) ↥(ArSub p F ϖ hρ₂0 hρ₂1)))
      = 0 := by
  funext I
  show evalArHom p F ϖ h12 hbmem hb (sliceElt p F ϖ
      (0 : ↥(restrictedMvPowerSeriesSubring (k + 1) ↥(ArSub p F ϖ hρ₂0 hρ₂1))) I)
    = (0 : MvPowerSeries (Fin k) ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)) I
  rw [sliceElt_zero, evalArHom_zero p F ϖ h12 hbmem hb]
  rfl

/-- The `k`-variable map sends `1` to `1`. -/
theorem evalArMvFun_one (h12 : ρ₁ ≤ ρ₂)
    {b : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)}
    (hbmem : b ∈ BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)
    (hb : wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1 b ≤ 1) {k : ℕ} :
    evalArMvFun p F ϖ h12 hbmem hb
        (1 : ↥(restrictedMvPowerSeriesSubring (k + 1) ↥(ArSub p F ϖ hρ₂0 hρ₂1)))
      = 1 := by
  funext I
  show evalArHom p F ϖ h12 hbmem hb (sliceElt p F ϖ
      (1 : ↥(restrictedMvPowerSeriesSubring (k + 1) ↥(ArSub p F ϖ hρ₂0 hρ₂1))) I)
    = MvPowerSeries.coeff I (1 : MvPowerSeries (Fin k)
      ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
  rw [MvPowerSeries.coeff_one]
  by_cases hI : I = 0
  · have hslice : sliceElt p F ϖ
        (1 : ↥(restrictedMvPowerSeriesSubring (k + 1) ↥(ArSub p F ϖ hρ₂0 hρ₂1))) I
        = 1 := by rw [sliceElt_one, if_pos hI]
    rw [if_pos hI]
    exact (congrArg (evalArHom p F ϖ h12 hbmem hb) hslice).trans
      (evalArHom_one p F ϖ h12 hbmem hb)
  · have hslice : sliceElt p F ϖ
        (1 : ↥(restrictedMvPowerSeriesSubring (k + 1) ↥(ArSub p F ϖ hρ₂0 hρ₂1))) I
        = 0 := by rw [sliceElt_one, if_neg hI]
    rw [if_neg hI]
    exact (congrArg (evalArHom p F ϖ h12 hbmem hb) hslice).trans
      (evalArHom_zero p F ϖ h12 hbmem hb)

/-- The `k`-variable map is multiplicative. -/
theorem evalArMvFun_mul (h12 : ρ₁ ≤ ρ₂)
    {b : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)}
    (hbmem : b ∈ BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)
    (hb : wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1 b ≤ 1) {k : ℕ}
    (f g : ↥(restrictedMvPowerSeriesSubring (k + 1) ↥(ArSub p F ϖ hρ₂0 hρ₂1))) :
    evalArMvFun p F ϖ h12 hbmem hb (f * g)
      = evalArMvFun p F ϖ h12 hbmem hb f * evalArMvFun p F ϖ h12 hbmem hb g := by
  classical
  funext I
  show evalArHom p F ϖ h12 hbmem hb (sliceElt p F ϖ (f * g) I)
    = MvPowerSeries.coeff I ((evalArMvFun p F ϖ h12 hbmem hb f)
      * (evalArMvFun p F ϖ h12 hbmem hb g))
  rw [sliceElt_mul, evalArHom_sum p F ϖ h12 hbmem hb, MvPowerSeries.coeff_mul]
  refine Finset.sum_congr rfl fun q _ => ?_
  exact evalArHom_mul p F ϖ h12 hbmem hb (sliceElt p F ϖ f q.1) (sliceElt p F ϖ g q.2)

/-- **The `k`-variable presentation map** `A^r⟨T, T₁,…,T_k⟩ →+* B^I⟨T₁,…,T_k⟩`: slice in
the `T`-direction, evaluate each slice at the power-bounded element `b`. Multiplicativity
is `sliceElt_mul` plus the ring-hom property of the one-variable `evalArHom`. -/
def evalArMvHom (h12 : ρ₁ ≤ ρ₂)
    {b : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)}
    (hbmem : b ∈ BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)
    (hb : wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1 b ≤ 1) {k : ℕ} :
    ↥(restrictedMvPowerSeriesSubring (k + 1) ↥(ArSub p F ϖ hρ₂0 hρ₂1))
      →+* ↥(restrictedMvPowerSeriesSubring k
        ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)) where
  toFun f := ⟨evalArMvFun p F ϖ h12 hbmem hb f,
    isRestricted_evalArMvFun p F ϖ h12 hbmem hb f⟩
  map_add' := fun f g => Subtype.ext (evalArMvFun_add p F ϖ h12 hbmem hb f g)
  map_zero' := Subtype.ext (evalArMvFun_zero p F ϖ h12 hbmem hb)
  map_one' := Subtype.ext (evalArMvFun_one p F ϖ h12 hbmem hb)
  map_mul' := fun f g => Subtype.ext (evalArMvFun_mul p F ϖ h12 hbmem hb f g)

/-- **Evaluation of a monomial**: `a·Tˡ ↦ a·bˡ`. -/
theorem evalAr_monomial (h12 : ρ₁ ≤ ρ₂)
    {b : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)}
    (hbmem : b ∈ BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)
    (hb : wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1 b ≤ 1) (l : ℕ)
    (a : ↥(ArSub p F ϖ hρ₂0 hρ₂1))
    (hres : MvPowerSeries.IsRestricted
      (MvPowerSeries.monomial (Finsupp.single (0 : Fin 1) l) a)) :
    evalAr p F ϖ h12 hbmem hb ⟨_, hres⟩
      = ((ArToBI p F ϖ (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1) h12 a :
        ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)) :
        (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)) * b ^ l := by
  classical
  refine tendsto_nhds_unique (tendsto_evalAr p F ϖ h12 hbmem hb ⟨_, hres⟩) ?_
  refine tendsto_const_nhds.congr' ?_
  rw [Filter.EventuallyEq, Filter.eventually_atTop]
  refine ⟨l + 1, fun n hn => ?_⟩
  have hterm : ∀ m ∈ Finset.range n,
      evalTerm p F ϖ h12 b
          (MvPowerSeries.monomial (Finsupp.single (0 : Fin 1) l)
            (a : ↥(ArSub p F ϖ hρ₂0 hρ₂1))) m
        = if m = l then ((ArToBI p F ϖ (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1) h12 a :
            ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)) :
            (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)) * b ^ l else 0 := by
    intro m _
    rw [evalTerm]
    have hcoeff : coeffSeq (MvPowerSeries.monomial (Finsupp.single (0 : Fin 1) l)
        (a : ↥(ArSub p F ϖ hρ₂0 hρ₂1))) m = if m = l then a else 0 := by
      rw [coeffSeq, MvPowerSeries.coeff_monomial]
      by_cases hm : m = l
      · subst hm
        rw [if_pos rfl, if_pos rfl]
      · rw [if_neg hm, if_neg]
        intro hcon
        exact hm ((Finsupp.single_injective (0 : Fin 1)) hcon)
    rw [hcoeff]
    by_cases hm : m = l
    · subst hm
      rw [if_pos rfl, if_pos rfl]
    · rw [if_neg hm, if_neg hm, map_zero]
      show (0 : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)) * b ^ m = 0
      rw [zero_mul]
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq' (Finset.range n) l
    (fun _ => ((ArToBI p F ϖ (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1) h12 a :
      ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)) :
      (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)) * b ^ l),
    if_pos (Finset.mem_range.mpr (by omega))]

/-- **On the dense layer the inclusion `A^r ↪ B^I` is the diagonal map**: for `u ∈ Aloc`,
the pair `(resAr, id)` of its `A^r`-image is the `Bloc`-image of `u`. -/
theorem ArToBI_AlocToHatK (h12 : ρ₁ ≤ ρ₂) (u : Aloc p F ϖ) :
    ((ArToBI p F ϖ (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1) h12
        ⟨AlocToHatK p F ϖ hρ₂0 hρ₂1 u, AlocToHatK_mem_ArSub p F ϖ u⟩ :
        ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)) :
        (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1))
      = BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 (AlocToBloc p F ϖ u) := by
  refine Prod.ext ?_ ?_
  · show resAr p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 (AlocToHatK p F ϖ hρ₂0 hρ₂1 u)
      = BlocToHatK p F ϖ hρ₁0 hρ₁1 (AlocToBloc p F ϖ u)
    rw [resAr_AlocToHatK p F ϖ (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1) h12,
      BlocToHatK_AlocToBloc p F ϖ hρ₁0 hρ₁1]
  · show AlocToHatK p F ϖ hρ₂0 hρ₂1 u
      = BlocToHatK p F ϖ hρ₂0 hρ₂1 (AlocToBloc p F ϖ u)
    rw [BlocToHatK_AlocToBloc p F ϖ hρ₂0 hρ₂1]

/-- The inverse of `[ϖ]` inside `Aloc = A_inf[1/[ϖ]]`. -/
def teichPiInvAloc : Aloc p F ϖ :=
  ↑(IsLocalization.map_units (M := Submonoid.powers (teichPi p F ϖ)) (Aloc p F ϖ)
    (⟨teichPi p F ϖ, Submonoid.mem_powers _⟩)).unit⁻¹

theorem teichPiInvAloc_mul :
    algebraMap (Ainf p F) (Aloc p F ϖ) (teichPi p F ϖ) * teichPiInvAloc p F ϖ = 1 := by
  have h := (IsLocalization.map_units (M := Submonoid.powers (teichPi p F ϖ))
    (Aloc p F ϖ) (⟨teichPi p F ϖ, Submonoid.mem_powers _⟩)).unit.mul_inv
  rwa [(IsLocalization.map_units (M := Submonoid.powers (teichPi p F ϖ))
    (Aloc p F ϖ) (⟨teichPi p F ϖ, Submonoid.mem_powers _⟩)).unit_spec] at h


theorem AlocToBloc_teichPiInv_mul (k : ℕ) :
    AlocToBloc p F ϖ (teichPiInvAloc p F ϖ ^ k)
      * algebraMap (Ainf p F) (Bloc p F ϖ) (teichPi p F ϖ ^ k) = 1 := by
  have hone : AlocToBloc p F ϖ (teichPiInvAloc p F ϖ)
      * algebraMap (Ainf p F) (Bloc p F ϖ) (teichPi p F ϖ) = 1 := by
    have h := congrArg (AlocToBloc p F ϖ) (teichPiInvAloc_mul p F ϖ)
    rw [map_mul, AlocToBloc_algebraMap, map_one] at h
    rw [mul_comm]
    exact h
  rw [map_pow, map_pow, ← mul_pow, hone, one_pow]

/-- **The presentation map hits `1/p`**: with Kedlaya's Tate variable taken at a power of
the pseudo-uniformizer (`z̄ = ϖʲ`, which is the case AD-9 selects), the monomial
`[ϖ]^{-jn}·T` evaluates to the image of `p⁻¹`. Together with the constants (the image of
`Aloc`, which already inverts `[ϖ]`) this puts the whole dense subring `Bloc` in the image
of `evalAr`. -/
theorem exists_evalAr_eq_pInv (h12 : ρ₁ ≤ ρ₂) (j n : ℕ)
    (hbmem : BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1
        (teichPowOverP p F ϖ ((PseudoUniformizer.toOF F ϖ) ^ j) n)
      ∈ BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)
    (hb : wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1 (BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1
      (teichPowOverP p F ϖ ((PseudoUniformizer.toOF F ϖ) ^ j) n)) ≤ 1) :
    ∃ f, evalAr p F ϖ h12 hbmem hb f
      = BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 ↑(isUnit_p_image p F ϖ).unit⁻¹ := by
  refine ⟨⟨MvPowerSeries.monomial (Finsupp.single (0 : Fin 1) 1)
      (⟨AlocToHatK p F ϖ hρ₂0 hρ₂1 (teichPiInvAloc p F ϖ ^ (j * n)),
        AlocToHatK_mem_ArSub p F ϖ _⟩ : ↥(ArSub p F ϖ hρ₂0 hρ₂1)),
      isRestricted_monomial p F ϖ _⟩, ?_⟩
  rw [evalAr_monomial p F ϖ h12 hbmem hb 1 _, ArToBI_AlocToHatK p F ϖ h12, pow_one,
    ← map_mul]
  congr 1
  have hteich : WittVector.teichmuller p ((PseudoUniformizer.toOF F ϖ) ^ j) ^ n
      = teichPi p F ϖ ^ (j * n) := by
    rw [map_pow, ← pow_mul, teichPi]
  rw [teichPowOverP, hteich, ← mul_assoc, AlocToBloc_teichPiInv_mul, one_mul]

/-- The image of the presentation map, as a subring of the ambient product. -/
def evalRange (h12 : ρ₁ ≤ ρ₂)
    {b : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)}
    (hbmem : b ∈ BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)
    (hb : wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1 b ≤ 1) :
    Subring ((hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)) :=
  ((BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1).subtype.comp
    (evalArHom p F ϖ h12 hbmem hb)).range

theorem mem_evalRange_iff (h12 : ρ₁ ≤ ρ₂)
    {b : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)}
    (hbmem : b ∈ BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)
    (hb : wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1 b ≤ 1)
    {z : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)} :
    z ∈ evalRange p F ϖ h12 hbmem hb ↔ ∃ f, evalAr p F ϖ h12 hbmem hb f = z :=
  Iff.rfl

/-- Constants are in the image. -/
theorem BIProd_AlocToBloc_mem_evalRange (h12 : ρ₁ ≤ ρ₂)
    {b : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)}
    (hbmem : b ∈ BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)
    (hb : wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1 b ≤ 1) (u : Aloc p F ϖ) :
    BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 (AlocToBloc p F ϖ u)
      ∈ evalRange p F ϖ h12 hbmem hb := by
  rw [mem_evalRange_iff]
  refine ⟨⟨MvPowerSeries.monomial (Finsupp.single (0 : Fin 1) 0)
      (⟨AlocToHatK p F ϖ hρ₂0 hρ₂1 u, AlocToHatK_mem_ArSub p F ϖ u⟩
        : ↥(ArSub p F ϖ hρ₂0 hρ₂1)), isRestricted_monomial p F ϖ _⟩, ?_⟩
  rw [evalAr_monomial p F ϖ h12 hbmem hb 0 _, ArToBI_AlocToHatK p F ϖ h12, pow_zero,
    mul_one]

/-- **The dense subring `Bloc` lies in the image of the presentation map.** -/
theorem BIProd_mem_evalRange (h12 : ρ₁ ≤ ρ₂) (j n : ℕ)
    (hbmem : BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1
        (teichPowOverP p F ϖ ((PseudoUniformizer.toOF F ϖ) ^ j) n)
      ∈ BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)
    (hb : wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1 (BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1
      (teichPowOverP p F ϖ ((PseudoUniformizer.toOF F ϖ) ^ j) n)) ≤ 1)
    (x : Bloc p F ϖ) :
    BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 x ∈ evalRange p F ϖ h12 hbmem hb := by
  -- the inverse of `p·[ϖ]` splits as `p⁻¹ · [ϖ]⁻¹`
  set vp : Bloc p F ϖ := ↑(isUnit_p_image p F ϖ).unit⁻¹ with hvp
  set vt : Bloc p F ϖ := AlocToBloc p F ϖ (teichPiInvAloc p F ϖ) with hvt
  have hvpmul : algebraMap (Ainf p F) (Bloc p F ϖ) (p : Ainf p F) * vp = 1 := by
    have h := (isUnit_p_image p F ϖ).unit.mul_inv
    rwa [(isUnit_p_image p F ϖ).unit_spec] at h
  have hvtmul : algebraMap (Ainf p F) (Bloc p F ϖ) (teichPi p F ϖ) * vt = 1 := by
    have h := congrArg (AlocToBloc p F ϖ) (teichPiInvAloc_mul p F ϖ)
    rwa [map_mul, AlocToBloc_algebraMap, map_one] at h
  have hsplit : ∀ k : ℕ, algebraMap (Ainf p F) (Bloc p F ϖ)
      (((p : Ainf p F) * teichPi p F ϖ) ^ k) * (vp * vt) ^ k = 1 := by
    intro k
    rw [map_pow, map_mul, ← mul_pow]
    rw [show algebraMap (Ainf p F) (Bloc p F ϖ) (p : Ainf p F)
        * algebraMap (Ainf p F) (Bloc p F ϖ) (teichPi p F ϖ) * (vp * vt)
        = (algebraMap (Ainf p F) (Bloc p F ϖ) (p : Ainf p F) * vp)
          * (algebraMap (Ainf p F) (Bloc p F ϖ) (teichPi p F ϖ) * vt) from by ring,
      hvpmul, hvtmul, mul_one, one_pow]
  obtain ⟨⟨a, y⟩, hxy⟩ := IsLocalization.surj
    (M := Submonoid.powers ((p : Ainf p F) * teichPi p F ϖ)) x
  obtain ⟨k, hk⟩ := y.2
  have hx : x = algebraMap (Ainf p F) (Bloc p F ϖ) a * (vp * vt) ^ k := by
    have hxy' : x * algebraMap (Ainf p F) (Bloc p F ϖ)
        (((p : Ainf p F) * teichPi p F ϖ) ^ k)
      = algebraMap (Ainf p F) (Bloc p F ϖ) a := by
      have hyk : ((p : Ainf p F) * teichPi p F ϖ) ^ k = (y : Ainf p F) := hk
      rw [hyk]
      exact hxy
    calc x = x * (algebraMap (Ainf p F) (Bloc p F ϖ)
            (((p : Ainf p F) * teichPi p F ϖ) ^ k) * (vp * vt) ^ k) := by
          rw [hsplit k, mul_one]
      _ = (x * algebraMap (Ainf p F) (Bloc p F ϖ)
            (((p : Ainf p F) * teichPi p F ϖ) ^ k)) * (vp * vt) ^ k := by ring
      _ = algebraMap (Ainf p F) (Bloc p F ϖ) a * (vp * vt) ^ k := by rw [hxy']
  rw [hx, map_mul, map_pow, map_mul]
  refine mul_mem ?_ (pow_mem (mul_mem ?_ ?_) k)
  · have := BIProd_AlocToBloc_mem_evalRange p F ϖ h12 hbmem hb
      (algebraMap (Ainf p F) (Aloc p F ϖ) a)
    rwa [AlocToBloc_algebraMap] at this
  · rw [hvp, mem_evalRange_iff]
    exact exists_evalAr_eq_pInv p F ϖ h12 j n hbmem hb
  · exact BIProd_AlocToBloc_mem_evalRange p F ϖ h12 hbmem hb (teichPiInvAloc p F ϖ)


/-- **The image of the presentation map is dense in `B^I`**: its closure contains the whole
interval ring. (Kedlaya's surjectivity statement is this together with the strictness
estimate, which gives closedness of the image.) -/
theorem BISub_le_topologicalClosure_evalRange (h12 : ρ₁ ≤ ρ₂) (j n : ℕ)
    (hbmem : BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1
        (teichPowOverP p F ϖ ((PseudoUniformizer.toOF F ϖ) ^ j) n)
      ∈ BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)
    (hb : wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1 (BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1
      (teichPowOverP p F ϖ ((PseudoUniformizer.toOF F ϖ) ^ j) n)) ≤ 1) :
    BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1
      ≤ (evalRange p F ϖ h12 hbmem hb).topologicalClosure := by
  intro z hz
  have hz' : z ∈ closure ((BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1).range
    : Set ((hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1))) := hz
  refine closure_mono ?_ hz'
  rintro w ⟨x, rfl⟩
  exact BIProd_mem_evalRange p F ϖ h12 j n hbmem hb x

/-- The Gauss value of `[ϖ]⁻¹` is `|ϖ|⁻¹`. -/
theorem wAloc_teichPiInvAloc {ρ : NNReal} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    wAloc p F ϖ hρ0 hρ1 (teichPiInvAloc p F ϖ)
      = (perfectoidValuation p F ((PseudoUniformizer.toOF F ϖ : OF F) : F))⁻¹ := by
  have hmul := congrArg (wAloc p F ϖ hρ0 hρ1) (teichPiInvAloc_mul p F ϖ)
  have hteich : gaussValue p F ρ (teichPi p F ϖ)
      = perfectoidValuation p F ((PseudoUniformizer.toOF F ϖ : OF F) : F) :=
    gaussValue_teichmuller p F hρ1.le (PseudoUniformizer.toOF F ϖ)
  rw [Valuation.map_mul, wAloc_algebraMap, map_one, hteich] at hmul
  have hne : perfectoidValuation p F ((PseudoUniformizer.toOF F ϖ : OF F) : F) ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hmul
    exact zero_ne_one hmul
  field_simp at hmul ⊢
  exact hmul

/-- The value of `[ϖ]^{-k}` in `A^r`. -/
theorem valued_teichPiInv_pow {ρ : NNReal} {hρ0 : 0 < ρ} {hρ1 : ρ < 1} (k : ℕ) :
    Valued.v (AlocToHatK p F ϖ hρ0 hρ1 (teichPiInvAloc p F ϖ ^ k))
      = ((perfectoidValuation p F ((PseudoUniformizer.toOF F ϖ : OF F) : F))⁻¹) ^ k := by
  rw [valued_AlocToHatK, map_pow, wAloc_teichPiInvAloc]


/-- **The norm-exact lift of `p^{-i}`** (the heart of Kedlaya's strictness estimate in the
AD-9 case): the monomial `[ϖ]^{-jni}·Tⁱ` evaluates to the image of `p^{-i}` and has Gauss
norm `|ϖ|^{-jni}`, which is `ρ₁^{-i}` exactly when the left endpoint is on the nose. -/
theorem exists_evalAr_eq_pInv_pow (h12 : ρ₁ ≤ ρ₂) (j n : ℕ)
    (hbmem : BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1
        (teichPowOverP p F ϖ ((PseudoUniformizer.toOF F ϖ) ^ j) n)
      ∈ BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)
    (hb : wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1 (BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1
      (teichPowOverP p F ϖ ((PseudoUniformizer.toOF F ϖ) ^ j) n)) ≤ 1) (i : ℕ) :
    ∃ f : ↥(restrictedMvPowerSeriesSubring 1 ↥(ArSub p F ϖ hρ₂0 hρ₂1)),
      evalAr p F ϖ h12 hbmem hb f
          = BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 (↑(isUnit_p_image p F ϖ).unit⁻¹ ^ i)
        ∧ gaussNormRPS p F ϖ hρ₂0 hρ₂1
            (f : MvPowerSeries (Fin 1) ↥(ArSub p F ϖ hρ₂0 hρ₂1))
          = ((perfectoidValuation p F
            ((PseudoUniformizer.toOF F ϖ : OF F) : F))⁻¹) ^ (j * n * i) := by
  refine ⟨⟨MvPowerSeries.monomial (Finsupp.single (0 : Fin 1) i)
      (⟨AlocToHatK p F ϖ hρ₂0 hρ₂1 (teichPiInvAloc p F ϖ ^ (j * n * i)),
        AlocToHatK_mem_ArSub p F ϖ _⟩ : ↥(ArSub p F ϖ hρ₂0 hρ₂1)),
      isRestricted_monomial p F ϖ _⟩, ?_, ?_⟩
  · rw [evalAr_monomial p F ϖ h12 hbmem hb i _, ArToBI_AlocToHatK p F ϖ h12,
      ← map_pow, ← map_mul]
    congr 1
    have hteich : WittVector.teichmuller p ((PseudoUniformizer.toOF F ϖ) ^ j) ^ n
        = teichPi p F ϖ ^ (j * n) := by
      rw [map_pow, ← pow_mul]
      rfl
    rw [teichPowOverP, hteich, mul_pow, ← map_pow, ← pow_mul, ← mul_assoc,
      AlocToBloc_teichPiInv_mul, one_mul]
  · rw [gaussNormRPS_monomial, valued_teichPiInv_pow]

/-- Multiplying the `[ϖ]`-power image by the inverse power gives `1`. -/
theorem teichPiInvAloc_pow_mul (m : ℕ) :
    algebraMap (Ainf p F) (Aloc p F ϖ) (teichPi p F ϖ ^ m)
      * teichPiInvAloc p F ϖ ^ m = 1 := by
  rw [map_pow, ← mul_pow, teichPiInvAloc_mul, one_pow]

/-- **The `Aloc` head split**: every `u ∈ Aloc` is a head `t` plus `p` times another
element of `Aloc`, where the head's Gauss value is radius-independent and bounded by
`u`'s value at every radius. -/
theorem exists_aloc_head_split (u : Aloc p F ϖ) :
    ∃ t w : Aloc p F ϖ, u = t + (p : Aloc p F ϖ) * w
      ∧ ∀ (ρ σ : NNReal) (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hσ0 : 0 < σ) (hσ1 : σ < 1),
          wAloc p F ϖ hρ0 hρ1 t ≤ wAloc p F ϖ hσ0 hσ1 u := by
  obtain ⟨⟨D, y⟩, hDy⟩ := IsLocalization.surj (M := Submonoid.powers (teichPi p F ϖ)) u
  obtain ⟨m, hm⟩ := y.2
  obtain ⟨D', hD', -⟩ := exists_head_split p F D
  have hu : u = algebraMap (Ainf p F) (Aloc p F ϖ) D * teichPiInvAloc p F ϖ ^ m := by
    have h1 : u * algebraMap (Ainf p F) (Aloc p F ϖ) (teichPi p F ϖ ^ m)
        = algebraMap (Ainf p F) (Aloc p F ϖ) D := by
      rw [show teichPi p F ϖ ^ m = (y : Ainf p F) from hm]; exact hDy
    calc u = u * (algebraMap (Ainf p F) (Aloc p F ϖ) (teichPi p F ϖ ^ m)
          * teichPiInvAloc p F ϖ ^ m) := by
          rw [teichPiInvAloc_pow_mul, mul_one]
      _ = (u * algebraMap (Ainf p F) (Aloc p F ϖ) (teichPi p F ϖ ^ m))
          * teichPiInvAloc p F ϖ ^ m := by ring
      _ = algebraMap (Ainf p F) (Aloc p F ϖ) D * teichPiInvAloc p F ϖ ^ m := by rw [h1]
  refine ⟨algebraMap (Ainf p F) (Aloc p F ϖ)
      (WittVector.teichmuller p (teichCoeff p F D 0)) * teichPiInvAloc p F ϖ ^ m,
    algebraMap (Ainf p F) (Aloc p F ϖ) D' * teichPiInvAloc p F ϖ ^ m, ?_, ?_⟩
  · rw [hu]
    conv_lhs => rw [hD']
    rw [map_add, map_mul, map_natCast]
    ring
  · intro ρ σ hρ0 hρ1 hσ0 hσ1
    have ht : wAloc p F ϖ hρ0 hρ1 (algebraMap (Ainf p F) (Aloc p F ϖ)
        (WittVector.teichmuller p (teichCoeff p F D 0)) * teichPiInvAloc p F ϖ ^ m)
        = perfectoidValuation p F ((teichCoeff p F D 0 : OF F) : F)
          * ((perfectoidValuation p F
            ((PseudoUniformizer.toOF F ϖ : OF F) : F))⁻¹) ^ m := by
      rw [Valuation.map_mul, Valuation.map_pow, wAloc_algebraMap,
        gaussValue_teichmuller p F hρ1.le, wAloc_teichPiInvAloc p F ϖ hρ0 hρ1]
    have hus : wAloc p F ϖ hσ0 hσ1 u
        = gaussValue p F σ D
          * ((perfectoidValuation p F
            ((PseudoUniformizer.toOF F ϖ : OF F) : F))⁻¹) ^ m := by
      rw [hu, Valuation.map_mul, Valuation.map_pow, wAloc_algebraMap,
        wAloc_teichPiInvAloc p F ϖ hσ0 hσ1]
    rw [ht, hus]
    refine mul_le_mul_of_nonneg_right ?_ zero_le
    have h0 := gaussTerm_le_gaussValue p F hσ1.le D 0
    rwa [gaussTerm, pow_zero, one_mul] at h0


/-- The `Bloc`-side Gauss value restricts to `wAloc` on `Aloc`-images. -/
theorem wLoc_AlocToBloc {ρ : NNReal} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (u : Aloc p F ϖ) :
    wLoc p F ϖ hρ0 hρ1 (AlocToBloc p F ϖ u) = wAloc p F ϖ hρ0 hρ1 u := by
  rw [← valued_BlocToHatK, BlocToHatK_AlocToBloc p F ϖ hρ0 hρ1, valued_AlocToHatK]

/-- The interval norm of `u·p⁻ᵏ` for `u ∈ Aloc`: the max of the two rescaled values. -/
theorem wI_BIProd_aloc_pInv_pow (k : ℕ) (u : Aloc p F ϖ) :
    wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1 (BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1
        (AlocToBloc p F ϖ u * ↑(isUnit_p_image p F ϖ).unit⁻¹ ^ k))
      = max (wAloc p F ϖ hρ₁0 hρ₁1 u * (ρ₁⁻¹) ^ k)
        (wAloc p F ϖ hρ₂0 hρ₂1 u * (ρ₂⁻¹) ^ k) := by
  rw [wI_BIProd, valued_BlocToHatK, valued_BlocToHatK, Valuation.map_mul,
    Valuation.map_mul, Valuation.map_pow, Valuation.map_pow,
    wLoc_p_inv p F ϖ hρ₁0 hρ₁1, wLoc_p_inv p F ϖ hρ₂0 hρ₂1,
    wLoc_AlocToBloc p F ϖ hρ₁0 hρ₁1, wLoc_AlocToBloc p F ϖ hρ₂0 hρ₂1]

/-- **Evaluation of the exact monomial lift**: `t·[ϖ]^{-jni}·Tⁱ` evaluates to
`t·p^{-i}` (the `AD-9` cancellation `[ϖ]^{jn}/p = ` Tate variable). -/
theorem evalAr_teichMonomial (h12 : ρ₁ ≤ ρ₂) (j n : ℕ)
    (hbmem : BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1
        (teichPowOverP p F ϖ ((PseudoUniformizer.toOF F ϖ) ^ j) n)
      ∈ BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)
    (hb : wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1 (BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1
      (teichPowOverP p F ϖ ((PseudoUniformizer.toOF F ϖ) ^ j) n)) ≤ 1)
    (t : Aloc p F ϖ) (i : ℕ) :
    evalAr p F ϖ h12 hbmem hb
        ⟨MvPowerSeries.monomial (Finsupp.single (0 : Fin 1) i)
          (⟨AlocToHatK p F ϖ hρ₂0 hρ₂1 (t * teichPiInvAloc p F ϖ ^ (j * n * i)),
            AlocToHatK_mem_ArSub p F ϖ _⟩ : ↥(ArSub p F ϖ hρ₂0 hρ₂1)),
          isRestricted_monomial p F ϖ _⟩
      = BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1
          (AlocToBloc p F ϖ t * ↑(isUnit_p_image p F ϖ).unit⁻¹ ^ i) := by
  rw [evalAr_monomial p F ϖ h12 hbmem hb i _, ArToBI_AlocToHatK p F ϖ h12,
    ← map_pow, ← map_mul]
  congr 1
  have hteich : WittVector.teichmuller p ((PseudoUniformizer.toOF F ϖ) ^ j) ^ n
      = teichPi p F ϖ ^ (j * n) := by
    rw [map_pow, ← pow_mul]
    rfl
  rw [teichPowOverP, hteich, mul_pow, ← map_pow, ← pow_mul, map_mul]
  calc AlocToBloc p F ϖ t * AlocToBloc p F ϖ (teichPiInvAloc p F ϖ ^ (j * n * i))
      * (algebraMap (Ainf p F) (Bloc p F ϖ) (teichPi p F ϖ ^ (j * n * i))
        * ↑(isUnit_p_image p F ϖ).unit⁻¹ ^ i)
      = AlocToBloc p F ϖ t
        * (AlocToBloc p F ϖ (teichPiInvAloc p F ϖ ^ (j * n * i))
          * algebraMap (Ainf p F) (Bloc p F ϖ) (teichPi p F ϖ ^ (j * n * i)))
        * ↑(isUnit_p_image p F ϖ).unit⁻¹ ^ i := by ring
    _ = AlocToBloc p F ϖ t * ↑(isUnit_p_image p F ϖ).unit⁻¹ ^ i := by
        rw [AlocToBloc_teichPiInv_mul, mul_one]

/-- **The Gauss norm of the exact monomial lift** is the value of its coefficient. -/
theorem gaussNormRPS_teichMonomial (t : Aloc p F ϖ) (i l : ℕ) :
    gaussNormRPS p F ϖ hρ₂0 hρ₂1
        (MvPowerSeries.monomial (Finsupp.single (0 : Fin 1) i)
          (⟨AlocToHatK p F ϖ hρ₂0 hρ₂1 (t * teichPiInvAloc p F ϖ ^ l),
            AlocToHatK_mem_ArSub p F ϖ _⟩ : ↥(ArSub p F ϖ hρ₂0 hρ₂1)))
      = wAloc p F ϖ hρ₂0 hρ₂1 t
        * ((perfectoidValuation p F
          ((PseudoUniformizer.toOF F ϖ : OF F) : F))⁻¹) ^ l := by
  rw [gaussNormRPS_monomial, valued_AlocToHatK, Valuation.map_mul, Valuation.map_pow,
    wAloc_teichPiInvAloc p F ϖ hρ₂0 hρ₂1]

/-- **The norm-controlled lift on the dense layer** (Kedlaya's strictness estimate,
AD-9 exact form): every `u·p⁻ᵏ` with `u ∈ Aloc` has an `evalAr`-preimage whose Gauss
norm is at most its interval norm. -/
theorem exists_evalAr_lift_aloc (h12 : ρ₁ ≤ ρ₂) (j n : ℕ)
    (hbmem : BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1
        (teichPowOverP p F ϖ ((PseudoUniformizer.toOF F ϖ) ^ j) n)
      ∈ BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)
    (hb : wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1 (BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1
      (teichPowOverP p F ϖ ((PseudoUniformizer.toOF F ϖ) ^ j) n)) ≤ 1)
    (hexact : perfectoidValuation p F
      ((PseudoUniformizer.toOF F ϖ : OF F) : F) ^ (j * n) = ρ₁)
    (k : ℕ) (u : Aloc p F ϖ) :
    ∃ f : ↥(restrictedMvPowerSeriesSubring 1 ↥(ArSub p F ϖ hρ₂0 hρ₂1)),
      evalAr p F ϖ h12 hbmem hb f
          = BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1
            (AlocToBloc p F ϖ u * ↑(isUnit_p_image p F ϖ).unit⁻¹ ^ k)
        ∧ gaussNormRPS p F ϖ hρ₂0 hρ₂1
            (f : MvPowerSeries (Fin 1) ↥(ArSub p F ϖ hρ₂0 hρ₂1))
          ≤ wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1 (BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1
              (AlocToBloc p F ϖ u * ↑(isUnit_p_image p F ϖ).unit⁻¹ ^ k)) := by
  induction k generalizing u with
  | zero =>
    refine ⟨⟨MvPowerSeries.monomial (Finsupp.single (0 : Fin 1) 0)
        (⟨AlocToHatK p F ϖ hρ₂0 hρ₂1 (u * teichPiInvAloc p F ϖ ^ (j * n * 0)),
          AlocToHatK_mem_ArSub p F ϖ _⟩ : ↥(ArSub p F ϖ hρ₂0 hρ₂1)),
        isRestricted_monomial p F ϖ _⟩,
      evalAr_teichMonomial p F ϖ h12 j n hbmem hb u 0, ?_⟩
    rw [gaussNormRPS_teichMonomial p F ϖ u 0 (j * n * 0),
      wI_BIProd_aloc_pInv_pow p F ϖ 0 u]
    simp only [Nat.mul_zero, pow_zero, mul_one]
    exact le_max_right _ _
  | succ k ih =>
    obtain ⟨t, w, hsplit, hbound⟩ := exists_aloc_head_split p F ϖ u
    obtain ⟨g, hg_eval, hg_norm⟩ := ih w
    refine ⟨⟨MvPowerSeries.monomial (Finsupp.single (0 : Fin 1) (k + 1))
        (⟨AlocToHatK p F ϖ hρ₂0 hρ₂1 (t * teichPiInvAloc p F ϖ ^ (j * n * (k + 1))),
          AlocToHatK_mem_ArSub p F ϖ _⟩ : ↥(ArSub p F ϖ hρ₂0 hρ₂1)),
        isRestricted_monomial p F ϖ _⟩ + g, ?_, ?_⟩
    · rw [evalAr_add p F ϖ h12 hbmem hb,
        evalAr_teichMonomial p F ϖ h12 j n hbmem hb t (k + 1), hg_eval, ← map_add]
      congr 1
      have hvp := (isUnit_p_image p F ϖ).unit.mul_inv
      have hcoe : (↑(isUnit_p_image p F ϖ).unit : Bloc p F ϖ)
          = AlocToBloc p F ϖ ((p : Aloc p F ϖ)) := by
        rw [(isUnit_p_image p F ϖ).unit_spec, map_natCast, map_natCast]
      rw [hcoe] at hvp
      rw [hsplit, map_add, map_mul, pow_succ]
      linear_combination (-(AlocToBloc p F ϖ w
        * (↑(isUnit_p_image p F ϖ).unit⁻¹ : Bloc p F ϖ) ^ k)) * hvp
    · refine le_trans (gaussNormRPS_add_le p F ϖ (isRestricted_monomial p F ϖ _) g.2)
        (max_le ?_ ?_)
      · rw [gaussNormRPS_teichMonomial p F ϖ t (k + 1) (j * n * (k + 1)),
          wI_BIProd_aloc_pInv_pow p F ϖ (k + 1) u]
        refine le_max_of_le_left ?_
        have hpow : ((perfectoidValuation p F
            ((PseudoUniformizer.toOF F ϖ : OF F) : F))⁻¹) ^ (j * n * (k + 1))
            = (ρ₁⁻¹) ^ (k + 1) := by
          rw [← hexact, ← inv_pow, ← pow_mul]
        rw [hpow]
        exact mul_le_mul_of_nonneg_right (hbound ρ₂ ρ₁ hρ₂0 hρ₂1 hρ₁0 hρ₁1) zero_le
      · refine le_trans hg_norm ?_
        rw [wI_BIProd_aloc_pInv_pow p F ϖ k w,
          wI_BIProd_aloc_pInv_pow p F ϖ (k + 1) u]
        have key : ∀ (ρ : NNReal) (hρ0 : 0 < ρ) (hρ1 : ρ < 1),
            wAloc p F ϖ hρ0 hρ1 w * (ρ⁻¹) ^ k
              ≤ wAloc p F ϖ hρ0 hρ1 u * (ρ⁻¹) ^ (k + 1) := by
          intro ρ hρ0 hρ1
          have hpw : ρ * wAloc p F ϖ hρ0 hρ1 w ≤ wAloc p F ϖ hρ0 hρ1 u := by
            have h1 : wAloc p F ϖ hρ0 hρ1 ((p : Aloc p F ϖ) * w)
                = ρ * wAloc p F ϖ hρ0 hρ1 w := by
              have h2 := wAloc_p_pow_mul p F ϖ hρ0 hρ1 1 w
              rwa [pow_one, pow_one] at h2
            have h3 : (p : Aloc p F ϖ) * w = u - t := by rw [hsplit]; ring
            rw [h3] at h1
            rw [← h1]
            calc wAloc p F ϖ hρ0 hρ1 (u - t)
                ≤ max (wAloc p F ϖ hρ0 hρ1 u) (wAloc p F ϖ hρ0 hρ1 t) :=
                  Valuation.map_sub _ _ _
              _ ≤ wAloc p F ϖ hρ0 hρ1 u :=
                  max_le le_rfl (hbound ρ ρ hρ0 hρ1 hρ0 hρ1)
          have hcancel : ρ * ρ⁻¹ = 1 := mul_inv_cancel₀ hρ0.ne'
          calc wAloc p F ϖ hρ0 hρ1 w * (ρ⁻¹) ^ k
              = (ρ * ρ⁻¹) * (wAloc p F ϖ hρ0 hρ1 w * (ρ⁻¹) ^ k) := by
                rw [hcancel, one_mul]
            _ = (ρ * wAloc p F ϖ hρ0 hρ1 w) * ((ρ⁻¹) ^ k * ρ⁻¹) := by ring
            _ = (ρ * wAloc p F ϖ hρ0 hρ1 w) * (ρ⁻¹) ^ (k + 1) := by rw [pow_succ]
            _ ≤ wAloc p F ϖ hρ0 hρ1 u * (ρ⁻¹) ^ (k + 1) :=
                mul_le_mul_of_nonneg_right hpw zero_le
        exact max_le_max (key ρ₁ hρ₁0 hρ₁1) (key ρ₂ hρ₂0 hρ₂1)

/-- **The norm-controlled lift of every `Bloc` element** — Kedlaya's estimate
(4.9.1) with constant `1` (the AD-9 exact case). -/
theorem exists_evalAr_lift_bloc (h12 : ρ₁ ≤ ρ₂) (j n : ℕ)
    (hbmem : BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1
        (teichPowOverP p F ϖ ((PseudoUniformizer.toOF F ϖ) ^ j) n)
      ∈ BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)
    (hb : wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1 (BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1
      (teichPowOverP p F ϖ ((PseudoUniformizer.toOF F ϖ) ^ j) n)) ≤ 1)
    (hexact : perfectoidValuation p F
      ((PseudoUniformizer.toOF F ϖ : OF F) : F) ^ (j * n) = ρ₁)
    (x : Bloc p F ϖ) :
    ∃ f : ↥(restrictedMvPowerSeriesSubring 1 ↥(ArSub p F ϖ hρ₂0 hρ₂1)),
      evalAr p F ϖ h12 hbmem hb f = BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 x
        ∧ gaussNormRPS p F ϖ hρ₂0 hρ₂1
            (f : MvPowerSeries (Fin 1) ↥(ArSub p F ϖ hρ₂0 hρ₂1))
          ≤ wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1
              (BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 x) := by
  set vp : Bloc p F ϖ := ↑(isUnit_p_image p F ϖ).unit⁻¹ with hvp
  set vt : Bloc p F ϖ := AlocToBloc p F ϖ (teichPiInvAloc p F ϖ) with hvt
  have hvpmul : algebraMap (Ainf p F) (Bloc p F ϖ) (p : Ainf p F) * vp = 1 := by
    have h := (isUnit_p_image p F ϖ).unit.mul_inv
    rwa [(isUnit_p_image p F ϖ).unit_spec] at h
  have hvtmul : algebraMap (Ainf p F) (Bloc p F ϖ) (teichPi p F ϖ) * vt = 1 := by
    have h := congrArg (AlocToBloc p F ϖ) (teichPiInvAloc_mul p F ϖ)
    rwa [map_mul, AlocToBloc_algebraMap, map_one] at h
  have hsplit : ∀ k : ℕ, algebraMap (Ainf p F) (Bloc p F ϖ)
      (((p : Ainf p F) * teichPi p F ϖ) ^ k) * (vp * vt) ^ k = 1 := by
    intro k
    rw [map_pow, map_mul, ← mul_pow]
    rw [show algebraMap (Ainf p F) (Bloc p F ϖ) (p : Ainf p F)
        * algebraMap (Ainf p F) (Bloc p F ϖ) (teichPi p F ϖ) * (vp * vt)
        = (algebraMap (Ainf p F) (Bloc p F ϖ) (p : Ainf p F) * vp)
          * (algebraMap (Ainf p F) (Bloc p F ϖ) (teichPi p F ϖ) * vt) from by ring,
      hvpmul, hvtmul, mul_one, one_pow]
  obtain ⟨⟨a, y⟩, hxy⟩ := IsLocalization.surj
    (M := Submonoid.powers ((p : Ainf p F) * teichPi p F ϖ)) x
  obtain ⟨k, hk⟩ := y.2
  have hx0 : x = algebraMap (Ainf p F) (Bloc p F ϖ) a * (vp * vt) ^ k := by
    have hxy' : x * algebraMap (Ainf p F) (Bloc p F ϖ)
        (((p : Ainf p F) * teichPi p F ϖ) ^ k)
      = algebraMap (Ainf p F) (Bloc p F ϖ) a := by
      have hyk : ((p : Ainf p F) * teichPi p F ϖ) ^ k = (y : Ainf p F) := hk
      rw [hyk]
      exact hxy
    calc x = x * (algebraMap (Ainf p F) (Bloc p F ϖ)
            (((p : Ainf p F) * teichPi p F ϖ) ^ k) * (vp * vt) ^ k) := by
          rw [hsplit k, mul_one]
      _ = (x * algebraMap (Ainf p F) (Bloc p F ϖ)
            (((p : Ainf p F) * teichPi p F ϖ) ^ k)) * (vp * vt) ^ k := by ring
      _ = algebraMap (Ainf p F) (Bloc p F ϖ) a * (vp * vt) ^ k := by rw [hxy']
  have hx : x = AlocToBloc p F ϖ (algebraMap (Ainf p F) (Aloc p F ϖ) a
      * teichPiInvAloc p F ϖ ^ k) * vp ^ k := by
    calc x = algebraMap (Ainf p F) (Bloc p F ϖ) a * (vp * vt) ^ k := hx0
      _ = algebraMap (Ainf p F) (Bloc p F ϖ) a * vt ^ k * vp ^ k := by
          rw [mul_pow]; ring
      _ = AlocToBloc p F ϖ (algebraMap (Ainf p F) (Aloc p F ϖ) a
            * teichPiInvAloc p F ϖ ^ k) * vp ^ k := by
          rw [map_mul, AlocToBloc_algebraMap, map_pow]
  rw [hx]
  exact exists_evalAr_lift_aloc p F ϖ h12 j n hbmem hb hexact k _

/-- **Density extraction**: every element of `B^I` is within `ε` of a `Bloc`-image. -/
theorem exists_BIProd_approx {z : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)}
    (hz : z ∈ BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1) {ε : NNReal} (hε : 0 < ε) :
    ∃ x : Bloc p F ϖ, wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1
      (z - BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 x) ≤ ε := by
  have hz' : z ∈ closure ((BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1).range
      : Set ((hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1))) := hz
  rw [mem_closure_iff_nhds] at hz'
  obtain ⟨w, hwball, x, hwx⟩ := hz' _ (wI_ball_mem_nhds p F z hε)
  refine ⟨x, ?_⟩
  rw [hwx]
  have hswap : z - w = -(w - z) := by ring
  rw [hswap, wI_neg]
  exact hwball

/-- **Abstract successive-approximation chain**: from a one-step improvement engine,
a full correction sequence with its residual sequence. Stated over opaque types so
the recursion never unfolds against heavy concrete types (PERF-1). -/
theorem exists_chain {α : Type*} {β : Type*} (S : α → Prop) (ν : α → NNReal)
    (μ : β → NNReal) (sub : α → β → α) (c : ℕ → NNReal) (z : α)
    (hz : S z) (hzc : ν z ≤ c 0)
    (hstep : ∀ m r, S r → ν r ≤ c m →
      ∃ f : β, μ f ≤ c m ∧ S (sub r f) ∧ ν (sub r f) ≤ c (m + 1)) :
    ∃ (u : ℕ → β) (r : ℕ → α), r 0 = z ∧ (∀ m, r (m + 1) = sub (r m) (u m))
      ∧ (∀ m, μ (u m) ≤ c m) ∧ (∀ m, S (r m)) ∧ (∀ m, ν (r m) ≤ c m) := by
  choose F hμ hS hν using hstep
  let R : ∀ m : ℕ, {r : α // S r ∧ ν r ≤ c m} :=
    fun m => Nat.rec (motive := fun k => {r : α // S r ∧ ν r ≤ c k})
      ⟨z, hz, hzc⟩
      (fun k rk => ⟨sub rk.1 (F k rk.1 rk.2.1 rk.2.2),
        hS k rk.1 rk.2.1 rk.2.2, hν k rk.1 rk.2.1 rk.2.2⟩) m
  exact ⟨fun m => F m (R m).1 (R m).2.1 (R m).2.2, fun m => (R m).1, rfl,
    fun m => rfl, fun m => hμ m (R m).1 (R m).2.1 (R m).2.2,
    fun m => (R m).2.1, fun m => (R m).2.2⟩

/-- One step of the residual estimate: if the residual after partial sum `SS` is at
most `ε` and the correction `V` has Gauss norm at most `ε`, the residual after
`SS + V` is at most `ε`. -/
theorem wI_z_sub_evalAr_add_le (h12 : ρ₁ ≤ ρ₂)
    {b : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)}
    (hbmem : b ∈ BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)
    (hb : wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1 b ≤ 1)
    (z : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1))
    (SS V : ↥(restrictedMvPowerSeriesSubring 1 ↥(ArSub p F ϖ hρ₂0 hρ₂1)))
    {ε : NNReal} (hε : 0 < ε)
    (h1 : wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1 (z - evalAr p F ϖ h12 hbmem hb SS) ≤ ε)
    (h2 : gaussNormRPS p F ϖ hρ₂0 hρ₂1
      (V : MvPowerSeries (Fin 1) ↥(ArSub p F ϖ hρ₂0 hρ₂1)) ≤ ε) :
    wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1 (z - evalAr p F ϖ h12 hbmem hb (SS + V)) ≤ ε := by
  have hVle : wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1 (evalAr p F ϖ h12 hbmem hb V) ≤ ε := by
    refine wI_evalAr_le p F ϖ h12 hbmem hb V hε (fun l => ?_)
    exact le_trans (valued_coeff_le_gaussNormRPS p F ϖ V.2 _) h2
  have hsplit : z - evalAr p F ϖ h12 hbmem hb (SS + V)
      = (z - evalAr p F ϖ h12 hbmem hb SS)
        + -(evalAr p F ϖ h12 hbmem hb V) := by
    rw [evalAr_add p F ϖ h12 hbmem hb]
    ring
  calc wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1 (z - evalAr p F ϖ h12 hbmem hb (SS + V))
      = wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1 ((z - evalAr p F ϖ h12 hbmem hb SS)
          + -(evalAr p F ϖ h12 hbmem hb V)) := by rw [hsplit]
    _ ≤ max (wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1 (z - evalAr p F ϖ h12 hbmem hb SS))
        (wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1 (-(evalAr p F ϖ h12 hbmem hb V))) :=
      wI_add_le p F _ _
    _ = max (wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1 (z - evalAr p F ϖ h12 hbmem hb SS))
        (wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1 (evalAr p F ϖ h12 hbmem hb V)) := by
      rw [wI_neg]
    _ ≤ ε := max_le h1 hVle

/-- From a geometric correction sequence, the limit series is an exact
`evalAr`-preimage with Gauss norm at most `W`. -/
theorem exists_evalAr_eq_of_correction (h12 : ρ₁ ≤ ρ₂)
    {b : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)}
    (hbmem : b ∈ BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)
    (hb : wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1 b ≤ 1)
    (z : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)) {W : NNReal} (hW : 0 < W)
    (u : ℕ → ↥(restrictedMvPowerSeriesSubring 1 ↥(ArSub p F ϖ hρ₂0 hρ₂1)))
    (hCbnd : ∀ l, gaussNormRPS p F ϖ hρ₂0 hρ₂1
      ((u l : ↥(restrictedMvPowerSeriesSubring 1 ↥(ArSub p F ϖ hρ₂0 hρ₂1)))
        : MvPowerSeries (Fin 1) ↥(ArSub p F ϖ hρ₂0 hρ₂1)) ≤ W * (2⁻¹ : NNReal) ^ l)
    (hres : ∀ m, wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1
      (z - evalAr p F ϖ h12 hbmem hb (∑ l ∈ Finset.range m, u l))
        ≤ W * (2⁻¹ : NNReal) ^ m) :
    ∃ U : ↥(restrictedMvPowerSeriesSubring 1 ↥(ArSub p F ϖ hρ₂0 hρ₂1)),
      evalAr p F ϖ h12 hbmem hb U = z
        ∧ gaussNormRPS p F ϖ hρ₂0 hρ₂1
            (U : MvPowerSeries (Fin 1) ↥(ArSub p F ϖ hρ₂0 hρ₂1)) ≤ W := by
  have hhalf1 : ((2 : NNReal)⁻¹) ≤ 1 := by norm_num
  have hhalf0 : (0 : NNReal) < 2⁻¹ := by norm_num
  have hC0 : Filter.Tendsto (fun l : ℕ => W * (2⁻¹ : NNReal) ^ l)
      Filter.atTop (nhds 0) := by
    have h1 : Filter.Tendsto (fun l : ℕ => ((2 : NNReal)⁻¹) ^ l)
        Filter.atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num)
    have h2 := h1.const_mul W
    rwa [mul_zero] at h2
  obtain ⟨U, hU⟩ := exists_rps_series_limit p F ϖ hCbnd hC0
  have hcancel : ∀ a c : ↥(restrictedMvPowerSeriesSubring 1
      ↥(ArSub p F ϖ hρ₂0 hρ₂1)), c + (a - c) = a := fun a c => by abel
  have hUnorm : gaussNormRPS p F ϖ hρ₂0 hρ₂1
      ((U : ↥(restrictedMvPowerSeriesSubring 1 ↥(ArSub p F ϖ hρ₂0 hρ₂1)))
        : MvPowerSeries (Fin 1) ↥(ArSub p F ϖ hρ₂0 hρ₂1)) ≤ W := by
    have h0 := hU 0 W hW (fun l _ => by
      calc W * (2⁻¹ : NNReal) ^ l ≤ W * 1 :=
          mul_le_mul_of_nonneg_left (pow_le_one₀ zero_le hhalf1) zero_le
        _ = W := mul_one W)
    rwa [Finset.sum_range_zero, sub_zero] at h0
  have hdiff : ∀ m : ℕ, wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1
      (z - evalAr p F ϖ h12 hbmem hb U) ≤ W * (2⁻¹ : NNReal) ^ m := by
    intro m
    have hε : (0 : NNReal) < W * (2⁻¹ : NNReal) ^ m :=
      mul_pos hW (pow_pos hhalf0 _)
    have htail := hU m (W * (2⁻¹ : NNReal) ^ m) hε (fun l hl =>
      mul_le_mul_of_nonneg_left
        (pow_le_pow_of_le_one zero_le hhalf1 hl) zero_le)
    have h := wI_z_sub_evalAr_add_le p F ϖ h12 hbmem hb z
      (∑ l ∈ Finset.range m, u l) (U - ∑ l ∈ Finset.range m, u l) hε
      (hres m) htail
    rwa [hcancel] at h
  have hle0 : wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1
      (z - evalAr p F ϖ h12 hbmem hb U) ≤ 0 :=
    ge_of_tendsto hC0 (Filter.Eventually.of_forall hdiff)
  have h0 : wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1
      (z - evalAr p F ϖ h12 hbmem hb U) = 0 := le_antisymm hle0 zero_le
  exact ⟨U, (sub_eq_zero.mp ((wI_eq_zero_iff p F _).mp h0)).symm, hUnorm⟩

/-- The single correction step behind `exists_correction_sequence`: any `BISub`-element
bounded by `W · 2⁻ᵐ` admits a lift `f` whose Gauss norm is within that bound and which
improves the bound to `W · 2⁻⁽ᵐ⁺¹⁾`.

Extracted from `exists_correction_sequence`, where it was the dominant `have` (38 lines
of a 62-line body). The two `norm_num` facts about `2⁻¹` that it used are re-proved here
rather than threaded in as hypotheses. -/
private theorem exists_correction_step_of_wI_le (h12 : ρ₁ ≤ ρ₂) (j n : ℕ)
    (hbmem : BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1
        (teichPowOverP p F ϖ ((PseudoUniformizer.toOF F ϖ) ^ j) n)
      ∈ BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)
    (hb : wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1 (BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1
      (teichPowOverP p F ϖ ((PseudoUniformizer.toOF F ϖ) ^ j) n)) ≤ 1)
    (hexact : perfectoidValuation p F
      ((PseudoUniformizer.toOF F ϖ : OF F) : F) ^ (j * n) = ρ₁)
    {W : NNReal} (hW : 0 < W) :
    ∀ (m : ℕ) (r : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)),
      r ∈ BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 →
      wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1 r ≤ W * (2⁻¹ : NNReal) ^ m →
      ∃ f : ↥(restrictedMvPowerSeriesSubring 1 ↥(ArSub p F ϖ hρ₂0 hρ₂1)),
      gaussNormRPS p F ϖ hρ₂0 hρ₂1
      (f : MvPowerSeries (Fin 1) ↥(ArSub p F ϖ hρ₂0 hρ₂1))
      ≤ W * (2⁻¹ : NNReal) ^ m
      ∧ (r - evalAr p F ϖ h12 hbmem hb f) ∈ BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1
      ∧ wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1 (r - evalAr p F ϖ h12 hbmem hb f)
      ≤ W * (2⁻¹ : NNReal) ^ (m + 1) := by
  have hhalf1 : ((2 : NNReal)⁻¹) ≤ 1 := by norm_num
  have hhalf0 : (0 : NNReal) < 2⁻¹ := by norm_num
  intro m r hrmem hrbnd
  have hε : (0 : NNReal) < W * (2⁻¹ : NNReal) ^ (m + 1) :=
    mul_pos hW (pow_pos hhalf0 _)
  obtain ⟨x, hxapp⟩ := exists_BIProd_approx p F ϖ hrmem hε
  obtain ⟨f, hfeval, hfnorm⟩ :=
    exists_evalAr_lift_bloc p F ϖ h12 j n hbmem hb hexact x
  have hxle : wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1
      (BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 x) ≤ W * (2⁻¹ : NNReal) ^ m := by
    have hrw : BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 x
        = r + -(r - BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 x) := by ring
    calc wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1 (BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 x)
        = wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1
          (r + -(r - BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 x)) := by rw [← hrw]
      _ ≤ max (wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1 r)
          (wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1
            (-(r - BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 x))) := wI_add_le p F _ _
      _ = max (wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1 r)
          (wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1
            (r - BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 x)) := by rw [wI_neg]
      _ ≤ W * (2⁻¹ : NNReal) ^ m := by
          refine max_le hrbnd (le_trans hxapp ?_)
          exact mul_le_mul_of_nonneg_left
            (pow_le_pow_of_le_one zero_le hhalf1 (Nat.le_succ m)) zero_le
  refine ⟨f, le_trans hfnorm hxle, ?_, ?_⟩
  · rw [hfeval]
    exact sub_mem hrmem (BIProd_mem_BISub p F ϖ x)
  · rw [hfeval]
    exact hxapp

/-- **The correction sequence**: successive approximation of an element of `B^I` by
values of the presentation map, each round shrinking the residual by `2⁻¹` with
Gauss-norm control (the engine behind closedness of the image). -/
theorem exists_correction_sequence (h12 : ρ₁ ≤ ρ₂) (j n : ℕ)
    (hbmem : BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1
        (teichPowOverP p F ϖ ((PseudoUniformizer.toOF F ϖ) ^ j) n)
      ∈ BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)
    (hb : wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1 (BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1
      (teichPowOverP p F ϖ ((PseudoUniformizer.toOF F ϖ) ^ j) n)) ≤ 1)
    (hexact : perfectoidValuation p F
      ((PseudoUniformizer.toOF F ϖ : OF F) : F) ^ (j * n) = ρ₁)
    {z : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)}
    (hz : z ∈ BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)
    {W : NNReal} (hW : 0 < W)
    (hzW : wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1 z ≤ W) :
    ∃ u : ℕ → ↥(restrictedMvPowerSeriesSubring 1 ↥(ArSub p F ϖ hρ₂0 hρ₂1)),
      (∀ l, gaussNormRPS p F ϖ hρ₂0 hρ₂1
        ((u l : ↥(restrictedMvPowerSeriesSubring 1 ↥(ArSub p F ϖ hρ₂0 hρ₂1)))
          : MvPowerSeries (Fin 1) ↥(ArSub p F ϖ hρ₂0 hρ₂1)) ≤ W * (2⁻¹ : NNReal) ^ l)
      ∧ ∀ m, wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1
          (z - evalAr p F ϖ h12 hbmem hb (∑ l ∈ Finset.range m, u l))
            ≤ W * (2⁻¹ : NNReal) ^ m := by
  have hstep : ∀ (m : ℕ) (r : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)),
      r ∈ BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 →
      wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1 r ≤ W * (2⁻¹ : NNReal) ^ m →
      ∃ f : ↥(restrictedMvPowerSeriesSubring 1 ↥(ArSub p F ϖ hρ₂0 hρ₂1)),
      gaussNormRPS p F ϖ hρ₂0 hρ₂1
      (f : MvPowerSeries (Fin 1) ↥(ArSub p F ϖ hρ₂0 hρ₂1))
      ≤ W * (2⁻¹ : NNReal) ^ m
      ∧ (r - evalAr p F ϖ h12 hbmem hb f) ∈ BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1
      ∧ wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1 (r - evalAr p F ϖ h12 hbmem hb f)
      ≤ W * (2⁻¹ : NNReal) ^ (m + 1) :=
    exists_correction_step_of_wI_le p F ϖ h12 j n hbmem hb hexact hW
  obtain ⟨u, r, hr0, hrrec, hCbnd, hrmem, hrbnd⟩ :=
    exists_chain (fun w => w ∈ BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)
      (wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1)
      (fun f : ↥(restrictedMvPowerSeriesSubring 1 ↥(ArSub p F ϖ hρ₂0 hρ₂1)) =>
        gaussNormRPS p F ϖ hρ₂0 hρ₂1
          (f : MvPowerSeries (Fin 1) ↥(ArSub p F ϖ hρ₂0 hρ₂1)))
      (fun w f => w - evalAr p F ϖ h12 hbmem hb f)
      (fun m => W * (2⁻¹ : NNReal) ^ m) z hz
      (by rw [pow_zero, mul_one]; exact hzW) hstep
  have hpartial : ∀ m, r m
      = z - evalAr p F ϖ h12 hbmem hb (∑ l ∈ Finset.range m, u l) := by
    intro m
    induction m with
    | zero =>
      rw [hr0, Finset.sum_range_zero, evalAr_zero p F ϖ h12 hbmem hb, sub_zero]
    | succ m ih =>
      rw [hrrec m, ih, Finset.sum_range_succ, evalAr_add p F ϖ h12 hbmem hb,
        sub_sub]
  refine ⟨u, hCbnd, fun m => ?_⟩
  rw [← hpartial m]
  exact hrbnd m

/-- **Strict surjectivity onto `B^I`** (Kedlaya, Lemma "Robba localizations", case 3,
surjectivity): every element of the interval ring is the value of a restricted series
over `A^r` whose Gauss norm is at most its interval norm. -/
theorem exists_evalAr_eq_of_mem_BISub (h12 : ρ₁ ≤ ρ₂) (j n : ℕ)
    (hbmem : BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1
        (teichPowOverP p F ϖ ((PseudoUniformizer.toOF F ϖ) ^ j) n)
      ∈ BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)
    (hb : wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1 (BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1
      (teichPowOverP p F ϖ ((PseudoUniformizer.toOF F ϖ) ^ j) n)) ≤ 1)
    (hexact : perfectoidValuation p F
      ((PseudoUniformizer.toOF F ϖ : OF F) : F) ^ (j * n) = ρ₁)
    {z : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)}
    (hz : z ∈ BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1) :
    ∃ f : ↥(restrictedMvPowerSeriesSubring 1 ↥(ArSub p F ϖ hρ₂0 hρ₂1)),
      evalAr p F ϖ h12 hbmem hb f = z
        ∧ gaussNormRPS p F ϖ hρ₂0 hρ₂1
            (f : MvPowerSeries (Fin 1) ↥(ArSub p F ϖ hρ₂0 hρ₂1))
          ≤ wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1 z := by
  rcases eq_or_ne (wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1 z) 0 with hW0 | hWne
  · refine ⟨0, ?_, ?_⟩
    · rw [evalAr_zero p F ϖ h12 hbmem hb]
      exact ((wI_eq_zero_iff p F z).mp hW0).symm
    · have hgz : gaussNormRPS p F ϖ hρ₂0 hρ₂1
          ((0 : ↥(restrictedMvPowerSeriesSubring 1 ↥(ArSub p F ϖ hρ₂0 hρ₂1)))
            : MvPowerSeries (Fin 1) ↥(ArSub p F ϖ hρ₂0 hρ₂1)) = 0 := by
        rw [gaussNormRPS]
        refine le_antisymm (ciSup_le fun s => ?_) zero_le
        rw [ZeroMemClass.coe_zero, map_zero, ZeroMemClass.coe_zero,
          Valuation.map_zero]
      rw [hgz]
      exact zero_le
  · have hW : 0 < wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1 z := pos_iff_ne_zero.mpr hWne
    obtain ⟨u, hCbnd, hres⟩ := exists_correction_sequence p F ϖ h12 j n hbmem hb
      hexact hz hW le_rfl
    exact exists_evalAr_eq_of_correction p F ϖ h12 hbmem hb z hW u hCbnd hres

/-- **The univariate presentation map is surjective** (T911, one-variable case). -/
theorem surjective_evalArHom (h12 : ρ₁ ≤ ρ₂) (j n : ℕ)
    (hbmem : BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1
        (teichPowOverP p F ϖ ((PseudoUniformizer.toOF F ϖ) ^ j) n)
      ∈ BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)
    (hb : wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1 (BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1
      (teichPowOverP p F ϖ ((PseudoUniformizer.toOF F ϖ) ^ j) n)) ≤ 1)
    (hexact : perfectoidValuation p F
      ((PseudoUniformizer.toOF F ϖ : OF F) : F) ^ (j * n) = ρ₁) :
    Function.Surjective (evalArHom p F ϖ h12 hbmem hb) := by
  rintro ⟨z, hz⟩
  obtain ⟨f, hfeval, -⟩ :=
    exists_evalAr_eq_of_mem_BISub p F ϖ h12 j n hbmem hb hexact hz
  exact ⟨f, Subtype.ext hfeval⟩

/-- Restrictedness over `B^I` forces the interval norms of the coefficients to be
cofinitely small (the converse of `isRestricted_of_wI`). -/
theorem wI_finite_of_isRestricted {k : ℕ}
    {c : MvPowerSeries (Fin k) ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)}
    (hc : MvPowerSeries.IsRestricted c) {ε : NNReal} (hε : 0 < ε) :
    {I : Fin k →₀ ℕ | ε < wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1
      ((MvPowerSeries.coeff I c : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
        : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1))}.Finite := by
  have hball : {w : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1) |
      wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1 w ≤ ε} ∈ nhds
        (0 : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)) := by
    have h := wI_ball_mem_nhds p F
      (0 : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)) hε
    simpa using h
  have hU : (Subtype.val ⁻¹' {w : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1) |
      wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1 w ≤ ε})
      ∈ nhds (0 : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)) :=
    continuous_subtype_val.continuousAt.preimage_mem_nhds hball
  have hUev : ∀ᶠ y in nhds (0 : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)),
      wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1
        ((y : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
          : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)) ≤ ε := hU
  have hev := hc.eventually hUev
  have hfin := Filter.eventually_cofinite.mp hev
  simpa only [not_le] using hfin

/-- The coefficientwise-lifted series is restricted (the assembly step of the
`k`-variable surjectivity, hoisted to its own lemma per PERF-1). -/
theorem isRestricted_liftAssembly {k : ℕ}
    (fI : (Fin k →₀ ℕ) → ↥(restrictedMvPowerSeriesSubring 1 ↥(ArSub p F ϖ hρ₂0 hρ₂1)))
    (g : ↥(restrictedMvPowerSeriesSubring k ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)))
    (hfInorm : ∀ I, gaussNormRPS p F ϖ hρ₂0 hρ₂1
      ((fI I : ↥(restrictedMvPowerSeriesSubring 1 ↥(ArSub p F ϖ hρ₂0 hρ₂1)))
        : MvPowerSeries (Fin 1) ↥(ArSub p F ϖ hρ₂0 hρ₂1))
      ≤ wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1
        ((MvPowerSeries.coeff I (g : MvPowerSeries (Fin k)
          ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
          : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
          : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1))) :
    MvPowerSeries.IsRestricted (fun s => coeffSeq
      ((fI (Finsupp.tail s) : ↥(restrictedMvPowerSeriesSubring 1
        ↥(ArSub p F ϖ hρ₂0 hρ₂1)))
        : MvPowerSeries (Fin 1) ↥(ArSub p F ϖ hρ₂0 hρ₂1)) (s 0)
      : MvPowerSeries (Fin (k + 1)) ↥(ArSub p F ϖ hρ₂0 hρ₂1)) := by
  set G : MvPowerSeries (Fin (k + 1)) ↥(ArSub p F ϖ hρ₂0 hρ₂1) :=
    fun s => coeffSeq ((fI (Finsupp.tail s)
      : ↥(restrictedMvPowerSeriesSubring 1 ↥(ArSub p F ϖ hρ₂0 hρ₂1)))
      : MvPowerSeries (Fin 1) ↥(ArSub p F ϖ hρ₂0 hρ₂1)) (s 0) with hGdef
  rw [isRestricted_iff_valued]
  intro ε hε
  have hT : {I : Fin k →₀ ℕ | ε < wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1
      ((MvPowerSeries.coeff I (g : MvPowerSeries (Fin k)
        ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
        : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
        : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1))}.Finite :=
    wI_finite_of_isRestricted p F ϖ g.2 hε
  have hL : ∀ I : Fin k →₀ ℕ, {l : ℕ | ε < Valued.v
      ((coeffSeq ((fI I : ↥(restrictedMvPowerSeriesSubring 1
        ↥(ArSub p F ϖ hρ₂0 hρ₂1)))
        : MvPowerSeries (Fin 1) ↥(ArSub p F ϖ hρ₂0 hρ₂1)) l
        : ↥(ArSub p F ϖ hρ₂0 hρ₂1)) : hatK p F hρ₂0 hρ₂1)}.Finite := by
    intro I
    have hfin := (isRestricted_iff_valued p F ϖ
      ((fI I : ↥(restrictedMvPowerSeriesSubring 1 ↥(ArSub p F ϖ hρ₂0 hρ₂1)))
        : MvPowerSeries (Fin 1) ↥(ArSub p F ϖ hρ₂0 hρ₂1))).mp (fI I).2 ε hε
    have hpre : {l : ℕ | ε < Valued.v
        ((coeffSeq ((fI I : ↥(restrictedMvPowerSeriesSubring 1
          ↥(ArSub p F ϖ hρ₂0 hρ₂1)))
          : MvPowerSeries (Fin 1) ↥(ArSub p F ϖ hρ₂0 hρ₂1)) l
          : ↥(ArSub p F ϖ hρ₂0 hρ₂1)) : hatK p F hρ₂0 hρ₂1)}
        = (fun l : ℕ => Finsupp.single (0 : Fin 1) l) ⁻¹'
          {s : Fin 1 →₀ ℕ | ε < Valued.v ((MvPowerSeries.coeff s
            ((fI I : ↥(restrictedMvPowerSeriesSubring 1
              ↥(ArSub p F ϖ hρ₂0 hρ₂1)))
              : MvPowerSeries (Fin 1) ↥(ArSub p F ϖ hρ₂0 hρ₂1))
            : ↥(ArSub p F ϖ hρ₂0 hρ₂1)) : hatK p F hρ₂0 hρ₂1)} := rfl
    rw [hpre]
    exact Set.Finite.preimage
      (Set.injOn_of_injective (Finsupp.single_injective (0 : Fin 1))) hfin
  refine Set.Finite.subset ((hT.biUnion (fun I _ => (hL I).image
    (fun l => Finsupp.cons l I)))) fun s hs => ?_
  have hsv : ε < Valued.v ((G s : ↥(ArSub p F ϖ hρ₂0 hρ₂1))
      : hatK p F hρ₂0 hρ₂1) := hs
  have hGle : Valued.v ((G s : ↥(ArSub p F ϖ hρ₂0 hρ₂1)) : hatK p F hρ₂0 hρ₂1)
      ≤ wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1
        ((MvPowerSeries.coeff (Finsupp.tail s) (g : MvPowerSeries (Fin k)
          ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
          : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
          : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)) :=
    le_trans (valued_coeff_le_gaussNormRPS p F ϖ (fI (Finsupp.tail s)).2 _)
      (hfInorm (Finsupp.tail s))
  refine Set.mem_biUnion (lt_of_lt_of_le hsv hGle) ?_
  refine ⟨s 0, hsv, ?_⟩
  exact Finsupp.cons_tail s

/-- **The `k`-variable presentation map is surjective** — the restricted-series
functor applied to the strict surjection (T911b's instance): lift each coefficient
with Gauss-norm control and reassemble. -/
theorem surjective_evalArMvHom (h12 : ρ₁ ≤ ρ₂) (j n : ℕ)
    (hbmem : BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1
        (teichPowOverP p F ϖ ((PseudoUniformizer.toOF F ϖ) ^ j) n)
      ∈ BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)
    (hb : wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1 (BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1
      (teichPowOverP p F ϖ ((PseudoUniformizer.toOF F ϖ) ^ j) n)) ≤ 1)
    (hexact : perfectoidValuation p F
      ((PseudoUniformizer.toOF F ϖ : OF F) : F) ^ (j * n) = ρ₁) {k : ℕ} :
    Function.Surjective (evalArMvHom p F ϖ h12 hbmem hb (k := k)) := by
  intro g
  choose fI hfIeval hfInorm using fun I : Fin k →₀ ℕ =>
    exists_evalAr_eq_of_mem_BISub p F ϖ h12 j n hbmem hb hexact
      (MvPowerSeries.coeff I (g : MvPowerSeries (Fin k)
        ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))).2
  have hGres := isRestricted_liftAssembly p F ϖ fI g hfInorm
  refine ⟨⟨_, hGres⟩, ?_⟩
  apply Subtype.ext
  funext I
  have hslice : sliceElt p F ϖ ⟨_, hGres⟩ I = fI I := by
    apply Subtype.ext
    apply coeffSeq_ext
    intro l
    rw [coeffSeq_sliceElt]
    show coeffSeq ((fI (Finsupp.tail (Finsupp.cons l I))
        : ↥(restrictedMvPowerSeriesSubring 1 ↥(ArSub p F ϖ hρ₂0 hρ₂1)))
        : MvPowerSeries (Fin 1) ↥(ArSub p F ϖ hρ₂0 hρ₂1)) ((Finsupp.cons l I) 0)
      = coeffSeq ((fI I : ↥(restrictedMvPowerSeriesSubring 1
          ↥(ArSub p F ϖ hρ₂0 hρ₂1)))
        : MvPowerSeries (Fin 1) ↥(ArSub p F ϖ hρ₂0 hρ₂1)) l
    rw [Finsupp.tail_cons, Finsupp.cons_zero]
  show evalArMvFun p F ϖ h12 hbmem hb ⟨_, hGres⟩ I
    = (g : MvPowerSeries (Fin k) ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)) I
  rw [evalArMvFun_apply, hslice]
  exact Subtype.ext (hfIeval I)

end FarguesFontaine

end
