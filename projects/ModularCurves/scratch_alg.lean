import ModularCurves.Moduli.EngineMouthCharts

universe u
open AlgebraicGeometry CategoryTheory WeierstrassCurve SemilocalUnitSplit
open ModularCurves ModularCurves.MouthCharts

namespace ModularCurves
namespace MouthCharts

variable {X : Scheme.{u}} {C : EllipticCurveGeom X}

/-- Generic: composition of two `Scheme.resLE` restriction maps is the direct one. -/
theorem resLE_comp_resLE [IsAffine X] {g₁ g₂ g₃ : ↑Γ(X, ⊤)}
    (h12 : X.basicOpen g₂ ≤ X.basicOpen g₁) (h23 : X.basicOpen g₃ ≤ X.basicOpen g₂) :
    (Scheme.resLE h23).comp (Scheme.resLE h12) = Scheme.resLE (h23.trans h12) := by
  haveI := (isAffineOpen_top X).isLocalization_basicOpen g₁
  apply IsLocalization.ringHom_ext (Submonoid.powers g₁)
  ext x
  simp only [RingHom.coe_comp, Function.comp_apply]
  rw [resLE_algebraMap, resLE_algebraMap, resLE_algebraMap]

set_option maxHeartbeats 4000000 in
set_option backward.isDefEq.respectTransparency false in
theorem test_spread (G : Type*) [Group G] [IsAffine X]
    [MulSemiringAction G ↑Γ(X, ⊤)] (S' : Submonoid ↑Γ(X, ⊤))
    (p : Ideal (FixedPoints.subring ↑Γ(X, ⊤) G)) [p.IsPrime]
    (hpreS : ∀ s : S', ∃ k : FixedPoints.subring ↑Γ(X, ⊤) G,
      k ∉ p ∧ algebraMap (FixedPoints.subring ↑Γ(X, ⊤) G) ↑Γ(X, ⊤) k = (s : ↑Γ(X, ⊤)))
    (hmemS : ∀ k : FixedPoints.subring ↑Γ(X, ⊤) G, k ∉ p → ((k : ↑Γ(X, ⊤))) ∈ S')
    {ι : Type u} [Fintype ι] (f : ι → ↑Γ(X, ⊤))
    (P : ∀ i, LocalPresentation C ⟨X.basicOpen (f i), (isAffineOpen_top X).basicOpen (f i)⟩)
    (k₀ : FixedPoints.subring ↑Γ(X, ⊤) G) (hk₀ : k₀ ∉ p)
    (hspanA : ∀ a : FixedPoints.subring ↑Γ(X, ⊤) G, k₀ ∣ a →
      Ideal.span (Set.range fun i =>
        algebraMap ↑Γ(X, ⊤) (Localization.Away ((a : ↑Γ(X, ⊤)))) (f i)) = ⊤)
    (hU : ∀ i j, IsUnit (algebraMap (Localization S')
      (Localization
        (Submonoid.powers (algebraMap ↑Γ(X, ⊤) (Localization S') (f i))
          ⊔ Submonoid.powers (algebraMap ↑Γ(X, ⊤) (Localization S') (f j))))
      (algebraMap ↑Γ(X, ⊤) (Localization S') (f i * f j))))
    (D : ∀ i, VariableChange (Localization
      (Submonoid.powers (algebraMap ↑Γ(X, ⊤) (Localization S') (f i)))))
    (W₀L : WeierstrassCurve (Localization S'))
    (hΔ : IsUnit W₀L.Δ)
    (hglue : ∀ i, W₀L.map (algebraMap (Localization S')
        (Localization (Submonoid.powers (algebraMap ↑Γ(X, ⊤) (Localization S') (f i)))))
      = D i • ((P i).W.map (sectionsToLoc S' (f i)
          (Submonoid.powers (algebraMap ↑Γ(X, ⊤) (Localization S') (f i)))
          (isUnit_algebraMap_powers_self
            (algebraMap ↑Γ(X, ⊤) (Localization S') (f i))))))
    (hcobInv : ∀ i j,
      (((P i).restrict (V' := ⟨X.basicOpen (f i * f j),
            (isAffineOpen_top X).basicOpen (f i * f j)⟩)
          (basicOpen_mul_le_left (f i) (f j))).transVC
        ((P j).restrict (basicOpen_mul_le_right (f i) (f j)))).map
          (sectionsToLoc S' (f i * f j) _ (hU i j))
      = ((D i).map (resLoc
            (Submonoid.powers (algebraMap ↑Γ(X, ⊤) (Localization S') (f i)))
            (Submonoid.powers (algebraMap ↑Γ(X, ⊤) (Localization S') (f i))
              ⊔ Submonoid.powers (algebraMap ↑Γ(X, ⊤) (Localization S') (f j)))
            le_sup_left))⁻¹
        * (D j).map (resLoc
            (Submonoid.powers (algebraMap ↑Γ(X, ⊤) (Localization S') (f j)))
            (Submonoid.powers (algebraMap ↑Γ(X, ⊤) (Localization S') (f i))
              ⊔ Submonoid.powers (algebraMap ↑Γ(X, ⊤) (Localization S') (f j)))
            le_sup_right)) :
    ∃ (a₁ : FixedPoints.subring ↑Γ(X, ⊤) G) (_ : a₁ ∉ p)
      (W₀R₁ : WeierstrassCurve (Localization.Away ((a₁ : ↑Γ(X, ⊤)))))
      (DA : ∀ i, VariableChange ↑Γ(X, X.basicOpen (((a₁ : ↑Γ(X, ⊤))) * f i))),
      IsUnit W₀R₁.Δ ∧
      Ideal.span (Set.range fun i =>
        algebraMap ↑Γ(X, ⊤) (Localization.Away ((a₁ : ↑Γ(X, ⊤)))) (f i)) = ⊤ ∧
      (∀ i, DA i • ((P i).W.map (Scheme.resLE
          (basicOpen_mul_le_right ((a₁ : ↑Γ(X, ⊤))) (f i))))
        = W₀R₁.map (awayToSections ((a₁ : ↑Γ(X, ⊤))) (f i))) ∧
      (∀ i j,
        ((P i).restrict (V' := ⟨X.basicOpen ((((a₁ : ↑Γ(X, ⊤))) * f i)
              * (((a₁ : ↑Γ(X, ⊤))) * f j)),
            (isAffineOpen_top X).basicOpen ((((a₁ : ↑Γ(X, ⊤))) * f i)
              * (((a₁ : ↑Γ(X, ⊤))) * f j))⟩)
          ((basicOpen_mul_le_left (((a₁ : ↑Γ(X, ⊤))) * f i) (((a₁ : ↑Γ(X, ⊤))) * f j)).trans
            (basicOpen_mul_le_right ((a₁ : ↑Γ(X, ⊤))) (f i)))).transVC
        ((P j).restrict
          ((basicOpen_mul_le_right (((a₁ : ↑Γ(X, ⊤))) * f i) (((a₁ : ↑Γ(X, ⊤))) * f j)).trans
            (basicOpen_mul_le_right ((a₁ : ↑Γ(X, ⊤))) (f j))))
        = ((DA i).map (Scheme.resLE
            (basicOpen_mul_le_left (((a₁ : ↑Γ(X, ⊤))) * f i) (((a₁ : ↑Γ(X, ⊤))) * f j))))⁻¹
          * (DA j).map (Scheme.resLE
            (basicOpen_mul_le_right (((a₁ : ↑Γ(X, ⊤))) * f i)
              (((a₁ : ↑Γ(X, ⊤))) * f j)))) := by
  classical
  choose pre hpre_mem hpre_eq using hpreS
  have hmulmem : ∀ {x y : FixedPoints.subring ↑Γ(X, ⊤) G}, x ∉ p → y ∉ p → x * y ∉ p :=
    fun hx hy => p.primeCompl.mul_mem hx hy
  have hDsp : ∀ i, ∃ s : S', ∀ {g : ↑Γ(X, ⊤)}, g ∈ S' →
      ∀ (B : Type u) [CommRing B] [Algebra ↑Γ(X, ⊤) B]
        [IsLocalization.Away (g * f i) B]
        (ψ : B →+* Localization
          (Submonoid.powers (algebraMap ↑Γ(X, ⊤) (Localization S') (f i)))),
        (∀ a : ↑Γ(X, ⊤), ψ (algebraMap ↑Γ(X, ⊤) B a)
          = algebraMap (Localization S')
              (Localization
                (Submonoid.powers (algebraMap ↑Γ(X, ⊤) (Localization S') (f i))))
              (algebraMap ↑Γ(X, ⊤) (Localization S') a)) →
        IsUnit (algebraMap ↑Γ(X, ⊤) B ((s : ↑Γ(X, ⊤)))) →
        ∃ DB : VariableChange B, DB.map ψ = D i :=
    fun i => exists_variableChange_sections_preimage S' (f i) (D i)
  choose sVC hsVC using hDsp
  obtain ⟨⟨b₁, s₁⟩, hb₁⟩ := IsLocalization.surj S' W₀L.a₁
  obtain ⟨⟨b₂, s₂⟩, hb₂⟩ := IsLocalization.surj S' W₀L.a₂
  obtain ⟨⟨b₃, s₃⟩, hb₃⟩ := IsLocalization.surj S' W₀L.a₃
  obtain ⟨⟨b₄, s₄⟩, hb₄⟩ := IsLocalization.surj S' W₀L.a₄
  obtain ⟨⟨b₆, s₆⟩, hb₆⟩ := IsLocalization.surj S' W₀L.a₆
  obtain ⟨v, hv⟩ := hΔ.exists_right_inv
  obtain ⟨⟨bΔ, sΔ⟩, hbΔ⟩ := IsLocalization.surj S' v
  set sPre : S' := ((((((s₁ * s₂) * s₃) * s₄) * s₆) * sΔ) * ∏ i, sVC i) with hsPre
  set a₀ : FixedPoints.subring ↑Γ(X, ⊤) G := k₀ * pre sPre with ha₀def
  have ha₀ : a₀ ∉ p := hmulmem hk₀ (hpre_mem sPre)
  have ha₀S : ((a₀ : ↑Γ(X, ⊤))) ∈ S' := hmemS a₀ ha₀
  have hpre_dvd_a₀ : ((pre sPre : ↑Γ(X, ⊤))) ∣ ((a₀ : ↑Γ(X, ⊤))) := by
    show ((pre sPre : ↑Γ(X, ⊤))) ∣ ((k₀ : ↑Γ(X, ⊤)) * ((pre sPre : ↑Γ(X, ⊤))))
    exact dvd_mul_left _ _
  have hsPre_dvd : ((sPre : ↑Γ(X, ⊤))) ∣ ((a₀ : ↑Γ(X, ⊤))) := by
    rw [← hpre_eq sPre]
    exact hpre_dvd_a₀
  have hdvdS : ∀ t : S', t ∣ sPre → ((t : ↑Γ(X, ⊤))) ∣ ((a₀ : ↑Γ(X, ⊤))) := fun t ht =>
    dvd_trans (map_dvd S'.subtype ht) hsPre_dvd
  have hdvd₁ : ((s₁ : ↑Γ(X, ⊤))) ∣ ((a₀ : ↑Γ(X, ⊤))) := hdvdS s₁
    ((((((dvd_mul_right s₁ s₂).mul_right s₃).mul_right s₄).mul_right s₆).mul_right
      sΔ).mul_right _)
  have hdvd₂ : ((s₂ : ↑Γ(X, ⊤))) ∣ ((a₀ : ↑Γ(X, ⊤))) := hdvdS s₂
    ((((((dvd_mul_left s₂ s₁).mul_right s₃).mul_right s₄).mul_right s₆).mul_right
      sΔ).mul_right _)
  have hdvd₃ : ((s₃ : ↑Γ(X, ⊤))) ∣ ((a₀ : ↑Γ(X, ⊤))) := hdvdS s₃
    (((((dvd_mul_left s₃ (s₁ * s₂)).mul_right s₄).mul_right s₆).mul_right sΔ).mul_right _)
  have hdvd₄ : ((s₄ : ↑Γ(X, ⊤))) ∣ ((a₀ : ↑Γ(X, ⊤))) := hdvdS s₄
    ((((dvd_mul_left s₄ ((s₁ * s₂) * s₃)).mul_right s₆).mul_right sΔ).mul_right _)
  have hdvd₆ : ((s₆ : ↑Γ(X, ⊤))) ∣ ((a₀ : ↑Γ(X, ⊤))) := hdvdS s₆
    (((dvd_mul_left s₆ (((s₁ * s₂) * s₃) * s₄)).mul_right sΔ).mul_right _)
  have hdvdΔ : ((sΔ : ↑Γ(X, ⊤))) ∣ ((a₀ : ↑Γ(X, ⊤))) := hdvdS sΔ
    ((dvd_mul_left sΔ ((((s₁ * s₂) * s₃) * s₄) * s₆)).mul_right _)
  have hdvdVC : ∀ i, ((sVC i : ↑Γ(X, ⊤))) ∣ ((a₀ : ↑Γ(X, ⊤))) := fun i => hdvdS (sVC i)
    ((Finset.dvd_prod_of_mem sVC (Finset.mem_univ i)).mul_left _)
  have hk₀dvda₀ : k₀ ∣ a₀ := ⟨pre sPre, ha₀def⟩
  clear_value a₀
  clear ha₀def hdvdS hsPre_dvd hpre_dvd_a₀ hsPre sPre
  -- ============================================================
  -- LAYER 1: data at level a₀
  -- ============================================================
  set j₀ : Localization.Away ((a₀ : ↑Γ(X, ⊤))) →+* Localization S' :=
    awayToLocalization S' ha₀S with hj₀def
  have hj₀alg : ∀ x : ↑Γ(X, ⊤),
      j₀ (algebraMap ↑Γ(X, ⊤) (Localization.Away ((a₀ : ↑Γ(X, ⊤)))) x)
        = algebraMap ↑Γ(X, ⊤) (Localization S') x :=
    fun x => awayToLocalization_algebraMap S' ha₀S x
  have hu₁ : IsUnit (algebraMap ↑Γ(X, ⊤) (Localization.Away ((a₀ : ↑Γ(X, ⊤)))) (s₁ : ↑Γ(X, ⊤))) :=
    isUnit_algebraMap_away hdvd₁
  have hu₂ : IsUnit (algebraMap ↑Γ(X, ⊤) (Localization.Away ((a₀ : ↑Γ(X, ⊤)))) (s₂ : ↑Γ(X, ⊤))) :=
    isUnit_algebraMap_away hdvd₂
  have hu₃ : IsUnit (algebraMap ↑Γ(X, ⊤) (Localization.Away ((a₀ : ↑Γ(X, ⊤)))) (s₃ : ↑Γ(X, ⊤))) :=
    isUnit_algebraMap_away hdvd₃
  have hu₄ : IsUnit (algebraMap ↑Γ(X, ⊤) (Localization.Away ((a₀ : ↑Γ(X, ⊤)))) (s₄ : ↑Γ(X, ⊤))) :=
    isUnit_algebraMap_away hdvd₄
  have hu₆ : IsUnit (algebraMap ↑Γ(X, ⊤) (Localization.Away ((a₀ : ↑Γ(X, ⊤)))) (s₆ : ↑Γ(X, ⊤))) :=
    isUnit_algebraMap_away hdvd₆
  have huΔ : IsUnit (algebraMap ↑Γ(X, ⊤) (Localization.Away ((a₀ : ↑Γ(X, ⊤)))) (sΔ : ↑Γ(X, ⊤))) :=
    isUnit_algebraMap_away hdvdΔ
  set W₀R₀ : WeierstrassCurve (Localization.Away ((a₀ : ↑Γ(X, ⊤)))) :=
    ⟨algebraMap _ _ (b₁ : ↑Γ(X, ⊤)) * ↑hu₁.unit⁻¹,
     algebraMap _ _ (b₂ : ↑Γ(X, ⊤)) * ↑hu₂.unit⁻¹,
     algebraMap _ _ (b₃ : ↑Γ(X, ⊤)) * ↑hu₃.unit⁻¹,
     algebraMap _ _ (b₄ : ↑Γ(X, ⊤)) * ↑hu₄.unit⁻¹,
     algebraMap _ _ (b₆ : ↑Γ(X, ⊤)) * ↑hu₆.unit⁻¹⟩ with hW₀R₀def
  have hW₀R₀ : W₀R₀.map j₀ = W₀L := by
    refine WeierstrassCurve.ext ?_ ?_ ?_ ?_ ?_
    · show j₀ (algebraMap _ _ (b₁ : ↑Γ(X, ⊤)) * ↑hu₁.unit⁻¹) = W₀L.a₁
      rw [map_mul_isUnit_inv_eq_mk' j₀ hu₁ (hj₀alg b₁) (hj₀alg (s₁ : ↑Γ(X, ⊤)))]
      exact (IsLocalization.eq_mk'_iff_mul_eq.mpr hb₁).symm
    · show j₀ (algebraMap _ _ (b₂ : ↑Γ(X, ⊤)) * ↑hu₂.unit⁻¹) = W₀L.a₂
      rw [map_mul_isUnit_inv_eq_mk' j₀ hu₂ (hj₀alg b₂) (hj₀alg (s₂ : ↑Γ(X, ⊤)))]
      exact (IsLocalization.eq_mk'_iff_mul_eq.mpr hb₂).symm
    · show j₀ (algebraMap _ _ (b₃ : ↑Γ(X, ⊤)) * ↑hu₃.unit⁻¹) = W₀L.a₃
      rw [map_mul_isUnit_inv_eq_mk' j₀ hu₃ (hj₀alg b₃) (hj₀alg (s₃ : ↑Γ(X, ⊤)))]
      exact (IsLocalization.eq_mk'_iff_mul_eq.mpr hb₃).symm
    · show j₀ (algebraMap _ _ (b₄ : ↑Γ(X, ⊤)) * ↑hu₄.unit⁻¹) = W₀L.a₄
      rw [map_mul_isUnit_inv_eq_mk' j₀ hu₄ (hj₀alg b₄) (hj₀alg (s₄ : ↑Γ(X, ⊤)))]
      exact (IsLocalization.eq_mk'_iff_mul_eq.mpr hb₄).symm
    · show j₀ (algebraMap _ _ (b₆ : ↑Γ(X, ⊤)) * ↑hu₆.unit⁻¹) = W₀L.a₆
      rw [map_mul_isUnit_inv_eq_mk' j₀ hu₆ (hj₀alg b₆) (hj₀alg (s₆ : ↑Γ(X, ⊤)))]
      exact (IsLocalization.eq_mk'_iff_mul_eq.mpr hb₆).symm
  set vR₀ : Localization.Away ((a₀ : ↑Γ(X, ⊤))) :=
    algebraMap _ _ (bΔ : ↑Γ(X, ⊤)) * ↑huΔ.unit⁻¹ with hvR₀def
  have hvR₀ : j₀ vR₀ = v := by
    rw [hvR₀def, map_mul_isUnit_inv_eq_mk' j₀ huΔ (hj₀alg bΔ) (hj₀alg (sΔ : ↑Γ(X, ⊤)))]
    exact (IsLocalization.eq_mk'_iff_mul_eq.mpr hbΔ).symm
  have hΔ01 : j₀ W₀R₀.Δ = W₀L.Δ := by
    have h := congrArg WeierstrassCurve.Δ hW₀R₀
    rwa [WeierstrassCurve.map_Δ] at h
  have hunitΔ : j₀ (W₀R₀.Δ * vR₀) = j₀ 1 := by
    rw [map_mul, hΔ01, hvR₀, map_one]; exact hv
  obtain ⟨cΔ, hcΔ⟩ := exists_mem_mul_eq_of_away_map_eq S' (g := (a₀ : ↑Γ(X, ⊤)))
    (B := Localization.Away ((a₀ : ↑Γ(X, ⊤)))) j₀ hj₀alg hunitΔ
  have hψunit : ∀ i, IsUnit (algebraMap (Localization S')
      (Localization (Submonoid.powers (algebraMap ↑Γ(X, ⊤) (Localization S') (f i))))
      (algebraMap ↑Γ(X, ⊤) (Localization S') ((a₀ : ↑Γ(X, ⊤)) * f i))) := by
    intro i
    rw [map_mul, map_mul]
    exact ((IsLocalization.map_units (Localization S')
        (⟨(a₀ : ↑Γ(X, ⊤)), ha₀S⟩ : S')).map
        (algebraMap (Localization S') _)).mul (isUnit_algebraMap_powers_self _)
  have hDA₀ : ∀ i, ∃ DB : VariableChange ↑Γ(X, X.basicOpen ((a₀ : ↑Γ(X, ⊤)) * f i)),
      DB.map (sectionsToLoc S' ((a₀ : ↑Γ(X, ⊤)) * f i) _ (hψunit i)) = D i := by
    intro i
    haveI := (isAffineOpen_top X).isLocalization_basicOpen ((a₀ : ↑Γ(X, ⊤)) * f i)
    refine hsVC i ha₀S _ (sectionsToLoc S' ((a₀ : ↑Γ(X, ⊤)) * f i) _ (hψunit i))
      (fun a => sectionsToLoc_algebraMap S' ((a₀ : ↑Γ(X, ⊤)) * f i) _ (hψunit i) a) ?_
    exact isUnit_algebraMap_of_isLocalizationAway_dvd _ ((a₀ : ↑Γ(X, ⊤)) * f i)
      ((hdvdVC i).trans (dvd_mul_right _ _))
  choose DA₀ hDA₀eq using hDA₀
  -- glue clearing at level a₀
  have hglue₀ : ∀ i, ∃ s : S',
      algebraMap ↑Γ(X, ⊤) _ (s : ↑Γ(X, ⊤))
          * ((DA₀ i) • ((P i).W.map (Scheme.resLE
              (basicOpen_mul_le_right (a₀ : ↑Γ(X, ⊤)) (f i))))).a₁
        = algebraMap ↑Γ(X, ⊤) _ (s : ↑Γ(X, ⊤))
          * (W₀R₀.map (awayToSections (a₀ : ↑Γ(X, ⊤)) (f i))).a₁
      ∧ algebraMap ↑Γ(X, ⊤) _ (s : ↑Γ(X, ⊤))
          * ((DA₀ i) • ((P i).W.map (Scheme.resLE
              (basicOpen_mul_le_right (a₀ : ↑Γ(X, ⊤)) (f i))))).a₂
        = algebraMap ↑Γ(X, ⊤) _ (s : ↑Γ(X, ⊤))
          * (W₀R₀.map (awayToSections (a₀ : ↑Γ(X, ⊤)) (f i))).a₂
      ∧ algebraMap ↑Γ(X, ⊤) _ (s : ↑Γ(X, ⊤))
          * ((DA₀ i) • ((P i).W.map (Scheme.resLE
              (basicOpen_mul_le_right (a₀ : ↑Γ(X, ⊤)) (f i))))).a₃
        = algebraMap ↑Γ(X, ⊤) _ (s : ↑Γ(X, ⊤))
          * (W₀R₀.map (awayToSections (a₀ : ↑Γ(X, ⊤)) (f i))).a₃
      ∧ algebraMap ↑Γ(X, ⊤) _ (s : ↑Γ(X, ⊤))
          * ((DA₀ i) • ((P i).W.map (Scheme.resLE
              (basicOpen_mul_le_right (a₀ : ↑Γ(X, ⊤)) (f i))))).a₄
        = algebraMap ↑Γ(X, ⊤) _ (s : ↑Γ(X, ⊤))
          * (W₀R₀.map (awayToSections (a₀ : ↑Γ(X, ⊤)) (f i))).a₄
      ∧ algebraMap ↑Γ(X, ⊤) _ (s : ↑Γ(X, ⊤))
          * ((DA₀ i) • ((P i).W.map (Scheme.resLE
              (basicOpen_mul_le_right (a₀ : ↑Γ(X, ⊤)) (f i))))).a₆
        = algebraMap ↑Γ(X, ⊤) _ (s : ↑Γ(X, ⊤))
          * (W₀R₀.map (awayToSections (a₀ : ↑Γ(X, ⊤)) (f i))).a₆ := by
    intro i
    haveI := (isAffineOpen_top X).isLocalization_basicOpen ((a₀ : ↑Γ(X, ⊤)) * f i)
    have hcompᵢ : (sectionsToLoc S' ((a₀ : ↑Γ(X, ⊤)) * f i) _ (hψunit i)).comp
          (awayToSections (a₀ : ↑Γ(X, ⊤)) (f i))
        = (algebraMap (Localization S')
            (Localization (Submonoid.powers
              (algebraMap ↑Γ(X, ⊤) (Localization S') (f i))))).comp j₀ := by
      apply IsLocalization.ringHom_ext (Submonoid.powers (a₀ : ↑Γ(X, ⊤)))
      ext x
      simp only [RingHom.coe_comp, Function.comp_apply, awayToSections_algebraMap,
        sectionsToLoc_algebraMap, hj₀alg]
    have hLHS : ((DA₀ i) • ((P i).W.map (Scheme.resLE
            (basicOpen_mul_le_right (a₀ : ↑Γ(X, ⊤)) (f i))))).map
          (sectionsToLoc S' ((a₀ : ↑Γ(X, ⊤)) * f i) _ (hψunit i))
        = D i • ((P i).W.map (sectionsToLoc S' (f i) _
            (isUnit_algebraMap_powers_self (algebraMap ↑Γ(X, ⊤) (Localization S') (f i))))) := by
      rw [← WeierstrassCurve.map_variableChange, hDA₀eq i, WeierstrassCurve.map_map,
        sectionsToLoc_comp_resLE S' (f i) ((a₀ : ↑Γ(X, ⊤)) * f i)
          (basicOpen_mul_le_right (a₀ : ↑Γ(X, ⊤)) (f i)) _
          (isUnit_algebraMap_powers_self _) (hψunit i)]
    have hRHS : (W₀R₀.map (awayToSections (a₀ : ↑Γ(X, ⊤)) (f i))).map
          (sectionsToLoc S' ((a₀ : ↑Γ(X, ⊤)) * f i) _ (hψunit i))
        = W₀L.map (algebraMap (Localization S')
            (Localization (Submonoid.powers
              (algebraMap ↑Γ(X, ⊤) (Localization S') (f i))))) := by
      rw [WeierstrassCurve.map_map, hcompᵢ, ← WeierstrassCurve.map_map, hW₀R₀]
    have hWeq : ((DA₀ i) • ((P i).W.map (Scheme.resLE
          (basicOpen_mul_le_right (a₀ : ↑Γ(X, ⊤)) (f i))))).map
            (sectionsToLoc S' ((a₀ : ↑Γ(X, ⊤)) * f i) _ (hψunit i))
        = (W₀R₀.map (awayToSections (a₀ : ↑Γ(X, ⊤)) (f i))).map
            (sectionsToLoc S' ((a₀ : ↑Γ(X, ⊤)) * f i) _ (hψunit i)) := by
      rw [hLHS, hRHS]; exact (hglue i).symm
    exact exists_mem_clear_weierstrassCurve S' (g := (a₀ : ↑Γ(X, ⊤))) (f := f i) ha₀S _
      (sectionsToLoc S' ((a₀ : ↑Γ(X, ⊤)) * f i) _ (hψunit i))
      (fun a => sectionsToLoc_algebraMap S' ((a₀ : ↑Γ(X, ⊤)) * f i) _ (hψunit i) a) hWeq
  choose sGlue hsG1 hsG2 hsG3 hsG4 hsG6 using hglue₀
  -- overlap-open inclusions at level a₀
  have hWij : ∀ i j, X.basicOpen ((a₀ : ↑Γ(X, ⊤)) * (f i * f j)) ≤ X.basicOpen (f i * f j) :=
    fun i j => basicOpen_le_basicOpen_of_dvd (dvd_mul_left (f i * f j) (a₀ : ↑Γ(X, ⊤)))
  have hleAi : ∀ i j, X.basicOpen ((a₀ : ↑Γ(X, ⊤)) * (f i * f j))
      ≤ X.basicOpen ((a₀ : ↑Γ(X, ⊤)) * f i) :=
    fun i j => basicOpen_le_basicOpen_of_dvd ⟨f j, by ring⟩
  have hleAj : ∀ i j, X.basicOpen ((a₀ : ↑Γ(X, ⊤)) * (f i * f j))
      ≤ X.basicOpen ((a₀ : ↑Γ(X, ⊤)) * f j) :=
    fun i j => basicOpen_le_basicOpen_of_dvd ⟨f i, by ring⟩
  -- transVC clearing at level a₀
  have htriv₀ : ∀ i j, ∃ c : S',
      algebraMap ↑Γ(X, ⊤) _ (c : ↑Γ(X, ⊤))
          * ((((P i).restrict (V' := ⟨X.basicOpen ((a₀ : ↑Γ(X, ⊤)) * (f i * f j)),
              (isAffineOpen_top X).basicOpen ((a₀ : ↑Γ(X, ⊤)) * (f i * f j))⟩)
              ((hWij i j).trans (basicOpen_mul_le_left (f i) (f j)))).transVC
              ((P j).restrict ((hWij i j).trans (basicOpen_mul_le_right (f i) (f j))))).u
            : ↑Γ(X, X.basicOpen ((a₀ : ↑Γ(X, ⊤)) * (f i * f j))))
        = algebraMap ↑Γ(X, ⊤) _ (c : ↑Γ(X, ⊤))
          * ((((DA₀ i).map (Scheme.resLE (hleAi i j)))⁻¹
              * (DA₀ j).map (Scheme.resLE (hleAj i j))).u
            : ↑Γ(X, X.basicOpen ((a₀ : ↑Γ(X, ⊤)) * (f i * f j))))
      ∧ algebraMap ↑Γ(X, ⊤) _ (c : ↑Γ(X, ⊤))
          * (((P i).restrict (V' := ⟨X.basicOpen ((a₀ : ↑Γ(X, ⊤)) * (f i * f j)),
              (isAffineOpen_top X).basicOpen ((a₀ : ↑Γ(X, ⊤)) * (f i * f j))⟩)
              ((hWij i j).trans (basicOpen_mul_le_left (f i) (f j)))).transVC
              ((P j).restrict ((hWij i j).trans (basicOpen_mul_le_right (f i) (f j))))).r
        = algebraMap ↑Γ(X, ⊤) _ (c : ↑Γ(X, ⊤))
          * (((DA₀ i).map (Scheme.resLE (hleAi i j)))⁻¹
              * (DA₀ j).map (Scheme.resLE (hleAj i j))).r
      ∧ algebraMap ↑Γ(X, ⊤) _ (c : ↑Γ(X, ⊤))
          * (((P i).restrict (V' := ⟨X.basicOpen ((a₀ : ↑Γ(X, ⊤)) * (f i * f j)),
              (isAffineOpen_top X).basicOpen ((a₀ : ↑Γ(X, ⊤)) * (f i * f j))⟩)
              ((hWij i j).trans (basicOpen_mul_le_left (f i) (f j)))).transVC
              ((P j).restrict ((hWij i j).trans (basicOpen_mul_le_right (f i) (f j))))).s
        = algebraMap ↑Γ(X, ⊤) _ (c : ↑Γ(X, ⊤))
          * (((DA₀ i).map (Scheme.resLE (hleAi i j)))⁻¹
              * (DA₀ j).map (Scheme.resLE (hleAj i j))).s
      ∧ algebraMap ↑Γ(X, ⊤) _ (c : ↑Γ(X, ⊤))
          * (((P i).restrict (V' := ⟨X.basicOpen ((a₀ : ↑Γ(X, ⊤)) * (f i * f j)),
              (isAffineOpen_top X).basicOpen ((a₀ : ↑Γ(X, ⊤)) * (f i * f j))⟩)
              ((hWij i j).trans (basicOpen_mul_le_left (f i) (f j)))).transVC
              ((P j).restrict ((hWij i j).trans (basicOpen_mul_le_right (f i) (f j))))).t
        = algebraMap ↑Γ(X, ⊤) _ (c : ↑Γ(X, ⊤))
          * (((DA₀ i).map (Scheme.resLE (hleAi i j)))⁻¹
              * (DA₀ j).map (Scheme.resLE (hleAj i j))).t := by
    intro i j
    haveI := (isAffineOpen_top X).isLocalization_basicOpen ((a₀ : ↑Γ(X, ⊤)) * (f i * f j))
    have hJ2 : IsUnit (algebraMap (Localization S')
        (Localization (Submonoid.powers (algebraMap ↑Γ(X, ⊤) (Localization S') (f i))
          ⊔ Submonoid.powers (algebraMap ↑Γ(X, ⊤) (Localization S') (f j))))
        (algebraMap ↑Γ(X, ⊤) (Localization S') ((a₀ : ↑Γ(X, ⊤)) * (f i * f j)))) := by
      rw [map_mul, map_mul]
      exact ((IsLocalization.map_units (Localization S')
          (⟨(a₀ : ↑Γ(X, ⊤)), ha₀S⟩ : S')).map (algebraMap (Localization S') _)).mul (hU i j)
    set ψ₂ := sectionsToLoc S' ((a₀ : ↑Γ(X, ⊤)) * (f i * f j)) _ hJ2 with hψ₂def
    have hcomp2 : ψ₂.comp (Scheme.resLE (hWij i j))
        = sectionsToLoc S' (f i * f j) _ (hU i j) := by
      apply IsLocalization.ringHom_ext (Submonoid.powers (f i * f j))
      ext x
      simp only [RingHom.coe_comp, Function.comp_apply, resLE_algebraMap,
        sectionsToLoc_algebraMap, hψ₂def]
    have hcompDAi : ψ₂.comp (Scheme.resLE (hleAi i j))
        = (resLoc (Submonoid.powers (algebraMap ↑Γ(X, ⊤) (Localization S') (f i)))
            (Submonoid.powers (algebraMap ↑Γ(X, ⊤) (Localization S') (f i))
              ⊔ Submonoid.powers (algebraMap ↑Γ(X, ⊤) (Localization S') (f j))) le_sup_left).comp
          (sectionsToLoc S' ((a₀ : ↑Γ(X, ⊤)) * f i) _ (hψunit i)) := by
      haveI := (isAffineOpen_top X).isLocalization_basicOpen ((a₀ : ↑Γ(X, ⊤)) * f i)
      apply IsLocalization.ringHom_ext (Submonoid.powers ((a₀ : ↑Γ(X, ⊤)) * f i))
      ext x
      simp only [RingHom.coe_comp, Function.comp_apply, resLE_algebraMap,
        sectionsToLoc_algebraMap, resLoc_algebraMap, hψ₂def]
    have hcompDAj : ψ₂.comp (Scheme.resLE (hleAj i j))
        = (resLoc (Submonoid.powers (algebraMap ↑Γ(X, ⊤) (Localization S') (f j)))
            (Submonoid.powers (algebraMap ↑Γ(X, ⊤) (Localization S') (f i))
              ⊔ Submonoid.powers (algebraMap ↑Γ(X, ⊤) (Localization S') (f j))) le_sup_right).comp
          (sectionsToLoc S' ((a₀ : ↑Γ(X, ⊤)) * f j) _ (hψunit j)) := by
      haveI := (isAffineOpen_top X).isLocalization_basicOpen ((a₀ : ↑Γ(X, ⊤)) * f j)
      apply IsLocalization.ringHom_ext (Submonoid.powers ((a₀ : ↑Γ(X, ⊤)) * f j))
      ext x
      simp only [RingHom.coe_comp, Function.comp_apply, resLE_algebraMap,
        sectionsToLoc_algebraMap, resLoc_algebraMap, hψ₂def]
    have hT1 : (((P i).restrict (V' := ⟨X.basicOpen ((a₀ : ↑Γ(X, ⊤)) * (f i * f j)),
              (isAffineOpen_top X).basicOpen ((a₀ : ↑Γ(X, ⊤)) * (f i * f j))⟩)
              ((hWij i j).trans (basicOpen_mul_le_left (f i) (f j)))).transVC
          ((P j).restrict ((hWij i j).trans (basicOpen_mul_le_right (f i) (f j))))).map ψ₂
        = (((P i).restrict (V' := ⟨X.basicOpen (f i * f j),
              (isAffineOpen_top X).basicOpen (f i * f j)⟩)
              (basicOpen_mul_le_left (f i) (f j))).transVC
            ((P j).restrict (basicOpen_mul_le_right (f i) (f j)))).map
              (sectionsToLoc S' (f i * f j) _ (hU i j)) := by
      rw [← transVC_restrict_map_resLE (P i) (P j)
        (VAB := ⟨X.basicOpen (f i * f j), (isAffineOpen_top X).basicOpen (f i * f j)⟩)
        (W' := ⟨X.basicOpen ((a₀ : ↑Γ(X, ⊤)) * (f i * f j)),
          (isAffineOpen_top X).basicOpen ((a₀ : ↑Γ(X, ⊤)) * (f i * f j))⟩)
        (basicOpen_mul_le_left (f i) (f j))
        (basicOpen_mul_le_right (f i) (f j)) (hWij i j), VariableChange.map_map, hcomp2]
    have hT2 : ((((DA₀ i).map (Scheme.resLE (hleAi i j)))⁻¹
          * (DA₀ j).map (Scheme.resLE (hleAj i j))).map ψ₂)
        = ((D i).map (resLoc
              (Submonoid.powers (algebraMap ↑Γ(X, ⊤) (Localization S') (f i)))
              (Submonoid.powers (algebraMap ↑Γ(X, ⊤) (Localization S') (f i))
                ⊔ Submonoid.powers (algebraMap ↑Γ(X, ⊤) (Localization S') (f j)))
              le_sup_left))⁻¹
          * (D j).map (resLoc
              (Submonoid.powers (algebraMap ↑Γ(X, ⊤) (Localization S') (f j)))
              (Submonoid.powers (algebraMap ↑Γ(X, ⊤) (Localization S') (f i))
                ⊔ Submonoid.powers (algebraMap ↑Γ(X, ⊤) (Localization S') (f j)))
              le_sup_right) := by
      rw [vc_map_inv_mul, VariableChange.map_map, VariableChange.map_map, hcompDAi, hcompDAj,
        ← VariableChange.map_map, ← VariableChange.map_map, hDA₀eq i, hDA₀eq j]
    exact exists_mem_clear_variableChange₂ S' (g := (a₀ : ↑Γ(X, ⊤))) (f₁ := f i) (f₂ := f j)
      ha₀S _ ψ₂ (fun a => sectionsToLoc_algebraMap S' ((a₀ : ↑Γ(X, ⊤)) * (f i * f j)) _ hJ2 a)
      (hT1.trans ((hcobInv i j).trans hT2.symm))
  choose cT hcTu hcTr hcTs hcTt using htriv₀
  -- ============================================================
  -- LAYER 4: fold multipliers, descend to a₁, assemble
  -- ============================================================
  set cAll : S' := (cΔ * ∏ i, sGlue i) * ∏ q : ι × ι, cT q.1 q.2 with hcAlldef
  have hcΔdvd : (cΔ : ↑Γ(X, ⊤)) ∣ (cAll : ↑Γ(X, ⊤)) :=
    map_dvd S'.subtype ((dvd_mul_right cΔ _).mul_right _)
  have hsGdvd : ∀ i, (sGlue i : ↑Γ(X, ⊤)) ∣ (cAll : ↑Γ(X, ⊤)) := fun i =>
    map_dvd S'.subtype
      (((Finset.dvd_prod_of_mem sGlue (Finset.mem_univ i)).mul_left cΔ).mul_right _)
  have hcTdvd : ∀ i j, (cT i j : ↑Γ(X, ⊤)) ∣ (cAll : ↑Γ(X, ⊤)) := fun i j =>
    map_dvd S'.subtype
      ((Finset.dvd_prod_of_mem (fun q : ι × ι => cT q.1 q.2) (Finset.mem_univ (i, j))).mul_left _)
  set a₁ : FixedPoints.subring ↑Γ(X, ⊤) G := a₀ * pre cAll with ha₁def
  have ha₁ : a₁ ∉ p := hmulmem ha₀ (hpre_mem cAll)
  have ha₁coe : (a₁ : ↑Γ(X, ⊤)) = (a₀ : ↑Γ(X, ⊤)) * (pre cAll : ↑Γ(X, ⊤)) := by
    rw [ha₁def]; push_cast; ring
  have hcAllcoe : (pre cAll : ↑Γ(X, ⊤)) = (cAll : ↑Γ(X, ⊤)) := hpre_eq cAll
  have ha₀dvda₁ : (a₀ : ↑Γ(X, ⊤)) ∣ (a₁ : ↑Γ(X, ⊤)) := ⟨(pre cAll : ↑Γ(X, ⊤)), ha₁coe⟩
  have hcAlldvda₁ : (cAll : ↑Γ(X, ⊤)) ∣ (a₁ : ↑Γ(X, ⊤)) :=
    ⟨(a₀ : ↑Γ(X, ⊤)), by rw [ha₁coe, hcAllcoe]; ring⟩
  have hk₀dvda₁ : k₀ ∣ a₁ := hk₀dvda₀.trans ⟨pre cAll, ha₁def⟩
  have hDAle : ∀ i, X.basicOpen ((a₁ : ↑Γ(X, ⊤)) * f i) ≤ X.basicOpen ((a₀ : ↑Γ(X, ⊤)) * f i) :=
    fun i => basicOpen_le_basicOpen_of_dvd ⟨(pre cAll : ↑Γ(X, ⊤)), by rw [ha₁coe]; ring⟩
  set fR : Localization.Away ((a₀ : ↑Γ(X, ⊤))) →+* Localization.Away ((a₁ : ↑Γ(X, ⊤))) :=
    awayMapDvd ha₀dvda₁ with hfRdef
  refine ⟨a₁, ha₁, W₀R₀.map fR, fun i => (DA₀ i).map (Scheme.resLE (hDAle i)), ?_, ?_, ?_, ?_⟩
  · -- IsUnit (W₀R₀.map fR).Δ
    refine IsUnit.of_mul_eq_one (fR vR₀) ?_
    have hcΔcAll : algebraMap ↑Γ(X, ⊤) (Localization.Away ((a₀ : ↑Γ(X, ⊤)))) (cAll : ↑Γ(X, ⊤))
          * (W₀R₀.Δ * vR₀)
        = algebraMap ↑Γ(X, ⊤) (Localization.Away ((a₀ : ↑Γ(X, ⊤)))) (cAll : ↑Γ(X, ⊤)) * 1 :=
      mul_eq_mul_of_dvd (map_dvd _ hcΔdvd) hcΔ
    have hUcAllAway : IsUnit (fR (algebraMap ↑Γ(X, ⊤)
        (Localization.Away ((a₀ : ↑Γ(X, ⊤)))) (cAll : ↑Γ(X, ⊤)))) := by
      rw [hfRdef, awayMapDvd_algebraMap]
      exact isUnit_algebraMap_away hcAlldvda₁
    have h := map_eq_of_isUnit_mul_eq fR hUcAllAway hcΔcAll
    rw [map_mul, map_one] at h
    rw [WeierstrassCurve.map_Δ]
    exact h
  · exact hspanA a₁ hk₀dvda₁
  · -- glue at a₁
    intro i
    have hUcAll_i : IsUnit (algebraMap ↑Γ(X, ⊤)
        ↑Γ(X, X.basicOpen ((a₁ : ↑Γ(X, ⊤)) * f i)) (cAll : ↑Γ(X, ⊤))) := by
      haveI := (isAffineOpen_top X).isLocalization_basicOpen ((a₁ : ↑Γ(X, ⊤)) * f i)
      exact isUnit_algebraMap_of_isLocalizationAway_dvd _ ((a₁ : ↑Γ(X, ⊤)) * f i)
        (hcAlldvda₁.trans (dvd_mul_right _ _))
    have hup : ∀ (w₁ w₂ : ↑Γ(X, X.basicOpen ((a₀ : ↑Γ(X, ⊤)) * f i))),
        algebraMap ↑Γ(X, ⊤) _ (sGlue i : ↑Γ(X, ⊤)) * w₁
          = algebraMap ↑Γ(X, ⊤) _ (sGlue i : ↑Γ(X, ⊤)) * w₂ →
        algebraMap ↑Γ(X, ⊤) _ (cAll : ↑Γ(X, ⊤)) * w₁
          = algebraMap ↑Γ(X, ⊤) _ (cAll : ↑Γ(X, ⊤)) * w₂ :=
      fun w₁ w₂ h => mul_eq_mul_of_dvd (map_dvd _ (hsGdvd i)) h
    have hmapeq := weierstrassCurve_map_eq_of_mul_eq (Scheme.resLE (hDAle i))
      (u := algebraMap ↑Γ(X, ⊤) _ (cAll : ↑Γ(X, ⊤)))
      (show IsUnit (Scheme.resLE (hDAle i)
        (algebraMap ↑Γ(X, ⊤) _ (cAll : ↑Γ(X, ⊤)))) by rw [resLE_algebraMap]; exact hUcAll_i)
      (hup _ _ (hsG1 i)) (hup _ _ (hsG2 i)) (hup _ _ (hsG3 i)) (hup _ _ (hsG4 i)) (hup _ _ (hsG6 i))
    have hcompRHS : (Scheme.resLE (hDAle i)).comp (awayToSections (a₀ : ↑Γ(X, ⊤)) (f i))
        = (awayToSections (a₁ : ↑Γ(X, ⊤)) (f i)).comp fR := by
      apply IsLocalization.ringHom_ext (Submonoid.powers (a₀ : ↑Γ(X, ⊤)))
      ext x
      simp only [RingHom.coe_comp, Function.comp_apply, awayToSections_algebraMap,
        resLE_algebraMap, hfRdef, awayMapDvd_algebraMap]
    rw [← WeierstrassCurve.map_variableChange, WeierstrassCurve.map_map,
      resLE_comp_resLE (basicOpen_mul_le_right (a₀ : ↑Γ(X, ⊤)) (f i)) (hDAle i),
      WeierstrassCurve.map_map, hcompRHS, ← WeierstrassCurve.map_map] at hmapeq
    exact hmapeq
  · -- transVC-triviality at a₁
    intro i j
    have hle₂ : X.basicOpen (((a₁ : ↑Γ(X, ⊤)) * f i) * ((a₁ : ↑Γ(X, ⊤)) * f j))
        ≤ X.basicOpen ((a₀ : ↑Γ(X, ⊤)) * (f i * f j)) :=
      basicOpen_le_basicOpen_of_dvd
        ⟨(a₀ : ↑Γ(X, ⊤)) * ((pre cAll : ↑Γ(X, ⊤)) * (pre cAll : ↑Γ(X, ⊤))), by rw [ha₁coe]; ring⟩
    have hUcAll_ij : IsUnit (algebraMap ↑Γ(X, ⊤)
        ↑Γ(X, X.basicOpen (((a₁ : ↑Γ(X, ⊤)) * f i) * ((a₁ : ↑Γ(X, ⊤)) * f j)))
        (cAll : ↑Γ(X, ⊤))) := by
      haveI := (isAffineOpen_top X).isLocalization_basicOpen
        (((a₁ : ↑Γ(X, ⊤)) * f i) * ((a₁ : ↑Γ(X, ⊤)) * f j))
      exact isUnit_algebraMap_of_isLocalizationAway_dvd _
        (((a₁ : ↑Γ(X, ⊤)) * f i) * ((a₁ : ↑Γ(X, ⊤)) * f j))
        (hcAlldvda₁.trans ((dvd_mul_right (a₁ : ↑Γ(X, ⊤)) (f i)).mul_right _))
    have hup : ∀ (w₁ w₂ : ↑Γ(X, X.basicOpen ((a₀ : ↑Γ(X, ⊤)) * (f i * f j)))),
        algebraMap ↑Γ(X, ⊤) _ (cT i j : ↑Γ(X, ⊤)) * w₁
          = algebraMap ↑Γ(X, ⊤) _ (cT i j : ↑Γ(X, ⊤)) * w₂ →
        algebraMap ↑Γ(X, ⊤) _ (cAll : ↑Γ(X, ⊤)) * w₁
          = algebraMap ↑Γ(X, ⊤) _ (cAll : ↑Γ(X, ⊤)) * w₂ :=
      fun w₁ w₂ h => mul_eq_mul_of_dvd (map_dvd _ (hcTdvd i j)) h
    have hmapeq := variableChange_map_eq_of_mul_eq (Scheme.resLE hle₂)
      (u := algebraMap ↑Γ(X, ⊤) _ (cAll : ↑Γ(X, ⊤)))
      (show IsUnit (Scheme.resLE hle₂
        (algebraMap ↑Γ(X, ⊤) _ (cAll : ↑Γ(X, ⊤)))) by rw [resLE_algebraMap]; exact hUcAll_ij)
      (hup _ _ (hcTu i j)) (hup _ _ (hcTr i j)) (hup _ _ (hcTs i j)) (hup _ _ (hcTt i j))
    rw [← transVC_restrict_map_resLE (P i) (P j)
      (VAB := ⟨X.basicOpen ((a₀ : ↑Γ(X, ⊤)) * (f i * f j)),
        (isAffineOpen_top X).basicOpen ((a₀ : ↑Γ(X, ⊤)) * (f i * f j))⟩)
      (W' := ⟨X.basicOpen (((a₁ : ↑Γ(X, ⊤)) * f i) * ((a₁ : ↑Γ(X, ⊤)) * f j)),
        (isAffineOpen_top X).basicOpen (((a₁ : ↑Γ(X, ⊤)) * f i) * ((a₁ : ↑Γ(X, ⊤)) * f j))⟩)
      ((hWij i j).trans (basicOpen_mul_le_left (f i) (f j)))
      ((hWij i j).trans (basicOpen_mul_le_right (f i) (f j))) hle₂,
      VariableChange.map_map, VariableChange.map_map,
      resLE_comp_resLE (hDAle i) (basicOpen_mul_le_left ((a₁ : ↑Γ(X, ⊤)) * f i)
        ((a₁ : ↑Γ(X, ⊤)) * f j)),
      resLE_comp_resLE (hDAle j) (basicOpen_mul_le_right ((a₁ : ↑Γ(X, ⊤)) * f i)
        ((a₁ : ↑Γ(X, ⊤)) * f j))]
    rw [vc_map_inv_mul, VariableChange.map_map, VariableChange.map_map,
      resLE_comp_resLE (hleAi i j) hle₂, resLE_comp_resLE (hleAj i j) hle₂] at hmapeq
    exact hmapeq
