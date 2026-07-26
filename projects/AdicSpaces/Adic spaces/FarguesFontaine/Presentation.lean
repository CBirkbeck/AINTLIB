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

set_option maxHeartbeats 1000000 in
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

set_option maxHeartbeats 1000000 in
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

set_option maxHeartbeats 1000000 in
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

set_option maxHeartbeats 1000000 in
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

set_option maxHeartbeats 1000000 in
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


set_option maxHeartbeats 1000000 in
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

set_option maxHeartbeats 1000000 in
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

set_option maxHeartbeats 1000000 in
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

set_option maxHeartbeats 1000000 in
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


set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
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
  rw [hc, map_add (ArToBI p F ϖ (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1) (hρ₂0 := hρ₂0) (hρ₂1 := hρ₂1) h12)]
  rfl

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
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
  rw [hc, map_sum (ArToBI p F ϖ (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1) (hρ₂0 := hρ₂0) (hρ₂1 := hρ₂1) h12)]
  rw [AddSubmonoidClass.coe_finset_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [map_mul (ArToBI p F ϖ (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1) (hρ₂0 := hρ₂0) (hρ₂1 := hρ₂1) h12)]
  rfl

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
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

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
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
  map_zero' := Subtype.ext (by
    refine tendsto_nhds_unique (tendsto_evalAr p F ϖ h12 hbmem hb 0) ?_
    refine tendsto_const_nhds.congr fun n => ?_
    refine (Finset.sum_eq_zero fun l _ => ?_).symm
    rw [evalTerm]
    rw [show coeffSeq ((0 : ↥(restrictedMvPowerSeriesSubring 1
          ↥(ArSub p F ϖ hρ₂0 hρ₂1))) : MvPowerSeries (Fin 1) ↥(ArSub p F ϖ hρ₂0 hρ₂1)) l
        = 0 from coeffSeq_zero l, map_zero]
    show (0 : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)) * b ^ l = 0
    rw [zero_mul])
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
  simp only [Finset.mem_antidiagonal, Finset.mem_map, Finset.mem_product,
    Function.Embedding.coeFn_mk]
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

set_option maxHeartbeats 1000000 in
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

end FarguesFontaine

end
