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

end FarguesFontaine

end
