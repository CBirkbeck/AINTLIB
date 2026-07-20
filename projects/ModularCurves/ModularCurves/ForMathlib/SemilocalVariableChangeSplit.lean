/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project
-/
import ModularCurves.ForMathlib.SemilocalUnitCocycleSplit

/-!
# Semilocal splitting of `VariableChange`-valued Čech `1`-cocycles on a finite basic cover

Let `R` be a commutative ring and `f : ι → R` a finite family generating the unit ideal, so the
basic opens `D(fᵢ)` cover `Spec R`.  A **`VariableChange`-valued Čech `1`-cocycle** for this
cover is a family `T i j` of Weierstrass variable changes over the pairwise-overlap
localizations `R[1/fᵢ, 1/fⱼ]` satisfying `T i i = 1` and the cocycle law
`T i j * T j k = T i k` on triple overlaps.  This is exactly the transition datum of a family
of pointed Weierstrass charts of an elliptic curve over `Spec R` (KM 2.2.5): `T i j` compares
the `i`-th and `j`-th charts over `D(fᵢ) ∩ D(fⱼ)`.

**Main result** (`exists_variableChange_eq_mul_of_span_eq_top`): if `R` is **semilocal**
(`Finite (MaximalSpectrum R)`), every such cocycle *splits* as a coboundary: there are
variable changes `D i` over `R[1/fᵢ]` with `T i j = (D i) * (D j)⁻¹` on overlaps.  A consumer
normalizing Weierstrass charts rescales the `i`-th chart by `D i`; the corrected transitions
are `1`, so the corrected chart curves and chart isomorphisms glue to a global Weierstrass
model over `Spec R`.

The proof filters the cocycle through the lower central series of the variable-change group
(the `u`-layer, then the abelian `(r,s)`-layer, then the central `t`-layer), splitting one
layer at a time and conjugating the cocycle by the resulting cochain:

1. **`u`-layer**: `(i, j) ↦ (T i j).u` is a unit-valued Čech cocycle; it splits over the
   semilocal `R` by `SemilocalUnitSplit.exists_units_eq_mul_of_span_eq_top`
   (`Pic R = 0` in effective Čech form).  Conjugating by `⟨vᵢ, 0, 0, 0⟩` lands the cocycle
   in the subgroup `{u = 1}`.
2. **`(r,s)`-layer**: on `{u = 1}` the `r`- and `s`-components are *additive* Čech cocycles;
   they split by the finite-cover affine Čech `H¹` vanishing
   (`SemilocalUnitSplit.exists_sub_resLoc_eq_of_span_eq_top`, no semilocality needed).
   Conjugating by `⟨1, aᵢ, bᵢ, 0⟩` lands the cocycle in the central `{u = 1, r = s = 0}`.
3. **`t`-layer**: on the centre the `t`-component is an additive Čech cocycle; it splits by
   the same `H¹` vanishing, and conjugating by `⟨1, 0, 0, cᵢ⟩` trivializes the cocycle.

Everything is stated over the join submonoids `Submonoid.powers fᵢ ⊔ Submonoid.powers fⱼ`
in the `SemilocalUnitSplit.resLoc` vocabulary (as in `ForMathlib/SemilocalUnitCocycleSplit`);
the bridges `isLocalizedModule_sup_of_powers_mul` / `…_sup_sup_of_powers_mul`
(`ForMathlib/AffineCechH1`) re-express `Localization.Away (fᵢ * fⱼ)` data in this form.
-/

open WeierstrassCurve

namespace SemilocalUnitSplit

/-! ### Component arithmetic of variable changes -/

section ComponentLemmas

variable {A : Type*} [CommRing A] {B : Type*} [CommRing B]

/-- `map` along a ring hom is multiplicative (the `mapHom` law, in `map` form). -/
private theorem vc_map_mul (φ : A →+* B) (X Y : VariableChange A) :
    (X * Y).map φ = X.map φ * Y.map φ :=
  map_mul (VariableChange.mapHom φ) X Y

/-- `map` along a ring hom preserves inversion. -/
private theorem vc_map_inv (φ : A →+* B) (X : VariableChange A) :
    (X⁻¹).map φ = (X.map φ)⁻¹ :=
  map_inv (VariableChange.mapHom φ) X

private theorem vc_mul_u (X Y : VariableChange A) : (X * Y).u = X.u * Y.u := rfl

private theorem vc_mul_r (X Y : VariableChange A) :
    (X * Y).r = X.r * (Y.u : A) ^ 2 + Y.r := rfl

private theorem vc_mul_s (X Y : VariableChange A) :
    (X * Y).s = (Y.u : A) * X.s + Y.s := rfl

private theorem vc_mul_t (X Y : VariableChange A) :
    (X * Y).t = X.t * (Y.u : A) ^ 3 + X.r * Y.s * (Y.u : A) ^ 2 + Y.t := rfl

private theorem vc_inv_u (X : VariableChange A) : (X⁻¹).u = X.u⁻¹ := rfl

/-- `map` of a `u = 1` variable change, in constructor form. -/
private theorem vc_map_mk_one (φ : A →+* B) (r s t : A) :
    (⟨1, r, s, t⟩ : VariableChange A).map φ = ⟨1, φ r, φ s, φ t⟩ := by
  refine VariableChange.ext ?_ rfl rfl rfl
  show Units.map φ.toMonoidHom 1 = 1
  exact map_one _

/-- The conjugation formula in the unipotent part: for `X` with `X.u = 1`,
`⟨1, a₁, b₁, t₁⟩⁻¹ * X * ⟨1, a₂, b₂, t₂⟩` is again unipotent, with explicit components. -/
private theorem vc_mk_one_conj (X : VariableChange A) (hXu : X.u = 1)
    (a₁ b₁ t₁ a₂ b₂ t₂ : A) :
    (⟨1, a₁, b₁, t₁⟩ : VariableChange A)⁻¹ * X * ⟨1, a₂, b₂, t₂⟩
      = ⟨1, X.r - a₁ + a₂, X.s - b₁ + b₂,
          X.t - t₁ + t₂ + a₁ * b₁ - a₁ * X.s + (X.r - a₁) * b₂⟩ := by
  obtain ⟨u, r, s, t⟩ := X
  obtain rfl : u = 1 := hXu
  rw [VariableChange.inv_def, VariableChange.mul_def, VariableChange.mul_def]
  refine VariableChange.ext (by simp) ?_ ?_ ?_ <;>
    simp only [inv_one, Units.val_one, one_pow, one_mul, mul_one] <;> ring

/-- Congruence in the unipotent constructor slots. -/
private theorem vc_mk_one_congr {r s t r' s' t' : A} (h₁ : r = r') (h₂ : s = s')
    (h₃ : t = t') : (⟨1, r, s, t⟩ : VariableChange A) = ⟨1, r', s', t'⟩ := by
  rw [h₁, h₂, h₃]

end ComponentLemmas

variable {R : Type*} [CommRing R] {ι : Type*} (f : ι → R)

/-! ### Conjugation of a pairwise family by a per-chart cochain -/

section Conj

variable (T : ∀ i j,
    VariableChange (Localization (Submonoid.powers (f i) ⊔ Submonoid.powers (f j))))

/-- Conjugation of a pairwise `VariableChange` family by a per-chart cochain `D`:
`(vcConj f T D) i j = (D i)⁻¹ * T i j * D j` on the `(i, j)` overlap.  This is the effect on
transition data of rescaling the `i`-th chart by `D i`; it preserves the two cocycle laws and
composes contravariantly in `D`. -/
private noncomputable def vcConj
    (D : ∀ i, VariableChange (Localization (Submonoid.powers (f i)))) : ∀ i j,
    VariableChange (Localization (Submonoid.powers (f i) ⊔ Submonoid.powers (f j))) :=
  fun i j =>
    ((D i).map (resLoc (Submonoid.powers (f i))
        (Submonoid.powers (f i) ⊔ Submonoid.powers (f j)) le_sup_left))⁻¹
      * T i j
      * (D j).map (resLoc (Submonoid.powers (f j))
          (Submonoid.powers (f i) ⊔ Submonoid.powers (f j)) le_sup_right)

/-- Conjugation preserves the diagonal normalization. -/
private theorem vcConj_diag (hdiag : ∀ i, T i i = 1)
    (D : ∀ i, VariableChange (Localization (Submonoid.powers (f i)))) (i : ι) :
    vcConj f T D i i = 1 := by
  show ((D i).map (resLoc (Submonoid.powers (f i))
        (Submonoid.powers (f i) ⊔ Submonoid.powers (f i)) le_sup_left))⁻¹
      * T i i
      * (D i).map (resLoc (Submonoid.powers (f i))
          (Submonoid.powers (f i) ⊔ Submonoid.powers (f i)) le_sup_right) = 1
  rw [hdiag i, mul_one]
  exact inv_mul_cancel _

/-- Double restriction of a mapped variable change collapses along `resLoc_resLoc`
(any inclusion proof may be supplied for the composite). -/
private theorem vc_map_resLoc_resLoc (S₁ S₂ S₃ : Submonoid R) (h₁ : S₁ ≤ S₂) (h₂ : S₂ ≤ S₃)
    (h₃ : S₁ ≤ S₃) (D : VariableChange (Localization S₁)) :
    (D.map (resLoc S₁ S₂ h₁)).map (resLoc S₂ S₃ h₂) = D.map (resLoc S₁ S₃ h₃) := by
  rw [VariableChange.map_map]
  exact congrArg D.map (RingHom.ext fun x => resLoc_resLoc S₁ S₂ S₃ h₁ h₂ h₃ x)

/-- Conjugation preserves the Čech cocycle law. -/
private theorem vcConj_coc
    (hcoc : ∀ i j k,
      (T i j).map (resLoc (Submonoid.powers (f i) ⊔ Submonoid.powers (f j))
          (Submonoid.powers (f i) ⊔ Submonoid.powers (f j) ⊔ Submonoid.powers (f k))
          le_sup_left)
        * (T j k).map (resLoc (Submonoid.powers (f j) ⊔ Submonoid.powers (f k))
            (Submonoid.powers (f i) ⊔ Submonoid.powers (f j) ⊔ Submonoid.powers (f k))
            (sup_le (le_sup_of_le_left le_sup_right) le_sup_right))
      = (T i k).map (resLoc (Submonoid.powers (f i) ⊔ Submonoid.powers (f k))
          (Submonoid.powers (f i) ⊔ Submonoid.powers (f j) ⊔ Submonoid.powers (f k))
          (sup_le (le_sup_of_le_left le_sup_left) le_sup_right)))
    (D : ∀ i, VariableChange (Localization (Submonoid.powers (f i)))) :
    ∀ i j k,
      (vcConj f T D i j).map (resLoc (Submonoid.powers (f i) ⊔ Submonoid.powers (f j))
          (Submonoid.powers (f i) ⊔ Submonoid.powers (f j) ⊔ Submonoid.powers (f k))
          le_sup_left)
        * (vcConj f T D j k).map (resLoc (Submonoid.powers (f j) ⊔ Submonoid.powers (f k))
            (Submonoid.powers (f i) ⊔ Submonoid.powers (f j) ⊔ Submonoid.powers (f k))
            (sup_le (le_sup_of_le_left le_sup_right) le_sup_right))
      = (vcConj f T D i k).map (resLoc (Submonoid.powers (f i) ⊔ Submonoid.powers (f k))
          (Submonoid.powers (f i) ⊔ Submonoid.powers (f j) ⊔ Submonoid.powers (f k))
          (sup_le (le_sup_of_le_left le_sup_left) le_sup_right)) := by
  intro i j k
  show (((D i).map (resLoc _ _ le_sup_left))⁻¹ * T i j
        * (D j).map (resLoc _ _ le_sup_right)).map (resLoc _ _ le_sup_left)
      * (((D j).map (resLoc _ _ le_sup_left))⁻¹ * T j k
          * (D k).map (resLoc _ _ le_sup_right)).map
        (resLoc _ _ (sup_le (le_sup_of_le_left le_sup_right) le_sup_right))
    = (((D i).map (resLoc _ _ le_sup_left))⁻¹ * T i k
        * (D k).map (resLoc _ _ le_sup_right)).map
      (resLoc _ _ (sup_le (le_sup_of_le_left le_sup_left) le_sup_right))
  simp only [vc_map_mul, vc_map_inv]
  rw [vc_map_resLoc_resLoc (Submonoid.powers (f i))
      (Submonoid.powers (f i) ⊔ Submonoid.powers (f j))
      (Submonoid.powers (f i) ⊔ Submonoid.powers (f j) ⊔ Submonoid.powers (f k))
      le_sup_left le_sup_left (le_sup_left.trans le_sup_left) (D i),
    vc_map_resLoc_resLoc (Submonoid.powers (f j))
      (Submonoid.powers (f i) ⊔ Submonoid.powers (f j))
      (Submonoid.powers (f i) ⊔ Submonoid.powers (f j) ⊔ Submonoid.powers (f k))
      le_sup_right le_sup_left (le_sup_right.trans le_sup_left) (D j),
    vc_map_resLoc_resLoc (Submonoid.powers (f j))
      (Submonoid.powers (f j) ⊔ Submonoid.powers (f k))
      (Submonoid.powers (f i) ⊔ Submonoid.powers (f j) ⊔ Submonoid.powers (f k))
      le_sup_left (sup_le (le_sup_of_le_left le_sup_right) le_sup_right)
      (le_sup_right.trans le_sup_left) (D j),
    vc_map_resLoc_resLoc (Submonoid.powers (f k))
      (Submonoid.powers (f j) ⊔ Submonoid.powers (f k))
      (Submonoid.powers (f i) ⊔ Submonoid.powers (f j) ⊔ Submonoid.powers (f k))
      le_sup_right (sup_le (le_sup_of_le_left le_sup_right) le_sup_right) le_sup_right (D k),
    vc_map_resLoc_resLoc (Submonoid.powers (f i))
      (Submonoid.powers (f i) ⊔ Submonoid.powers (f k))
      (Submonoid.powers (f i) ⊔ Submonoid.powers (f j) ⊔ Submonoid.powers (f k))
      le_sup_left (sup_le (le_sup_of_le_left le_sup_left) le_sup_right)
      (le_sup_left.trans le_sup_left) (D i),
    vc_map_resLoc_resLoc (Submonoid.powers (f k))
      (Submonoid.powers (f i) ⊔ Submonoid.powers (f k))
      (Submonoid.powers (f i) ⊔ Submonoid.powers (f j) ⊔ Submonoid.powers (f k))
      le_sup_right (sup_le (le_sup_of_le_left le_sup_left) le_sup_right) le_sup_right (D k),
    ← hcoc i j k]
  simp only [mul_assoc, mul_inv_cancel_left]

/-- Conjugation composes contravariantly in the cochain. -/
private theorem vcConj_vcConj
    (D D' : ∀ i, VariableChange (Localization (Submonoid.powers (f i)))) (i j : ι) :
    vcConj f (vcConj f T D) D' i j = vcConj f T (fun i => D i * D' i) i j := by
  show ((D' i).map (resLoc _ _ le_sup_left))⁻¹
      * (((D i).map (resLoc _ _ le_sup_left))⁻¹ * T i j
          * (D j).map (resLoc _ _ le_sup_right))
      * (D' j).map (resLoc _ _ le_sup_right)
    = ((D i * D' i).map (resLoc _ _ le_sup_left))⁻¹ * T i j
      * (D j * D' j).map (resLoc _ _ le_sup_right)
  rw [vc_map_mul, vc_map_mul, mul_inv_rev]
  simp only [mul_assoc]

/-- If the conjugated family is trivial, the original family is the coboundary of the
cochain. -/
private theorem eq_of_vcConj_eq_one
    (D : ∀ i, VariableChange (Localization (Submonoid.powers (f i))))
    (h : ∀ i j, vcConj f T D i j = 1) : ∀ i j,
    T i j = (D i).map (resLoc (Submonoid.powers (f i))
        (Submonoid.powers (f i) ⊔ Submonoid.powers (f j)) le_sup_left)
      * ((D j).map (resLoc (Submonoid.powers (f j))
          (Submonoid.powers (f i) ⊔ Submonoid.powers (f j)) le_sup_right))⁻¹ := by
  intro i j
  have h1 : ((D i).map (resLoc (Submonoid.powers (f i))
        (Submonoid.powers (f i) ⊔ Submonoid.powers (f j)) le_sup_left))⁻¹
      * T i j
      * (D j).map (resLoc (Submonoid.powers (f j))
          (Submonoid.powers (f i) ⊔ Submonoid.powers (f j)) le_sup_right) = 1 := h i j
  rw [mul_eq_one_iff_eq_inv, inv_mul_eq_iff_eq_mul] at h1
  exact h1

end Conj

/-! ### The main theorem: `VariableChange` Čech `1`-cocycles split over a semilocal ring -/

/-- **Semilocal splitting of a `VariableChange`-valued Čech `1`-cocycle on a finite basic
cover.**  Over a semilocal ring `R` (`Finite (MaximalSpectrum R)`), a normalized
`VariableChange`-valued Čech `1`-cocycle `T` on a finite basic cover `{D(fᵢ)}` — the
transition datum of a family of pointed Weierstrass charts over the cover — splits as a
coboundary: there are variable changes `D i` over `R[1/fᵢ]` with `T i j = (D i) * (D j)⁻¹`
on every pairwise overlap.

Layer by layer: the `u`-cocycle splits since `Pic R = 0` for semilocal `R`
(`exists_units_eq_mul_of_span_eq_top`); after normalizing `u = 1` the `r`- and `s`-cocycles
are additive and split by the affine Čech `H¹` vanishing
(`exists_sub_resLoc_eq_of_span_eq_top`); after the `(r,s)`-correction the residual central
`t`-cocycle is additive and splits likewise.  A consumer rescales the `i`-th Weierstrass
chart by `D i`; the corrected transitions are `1`, so the corrected charts glue. -/
theorem exists_variableChange_eq_mul_of_span_eq_top [Fintype ι]
    [Finite (MaximalSpectrum R)] (hf : Ideal.span (Set.range f) = ⊤)
    (T : ∀ i j,
      VariableChange (Localization (Submonoid.powers (f i) ⊔ Submonoid.powers (f j))))
    (hdiag : ∀ i, T i i = 1)
    (hcoc : ∀ i j k,
      (T i j).map (resLoc (Submonoid.powers (f i) ⊔ Submonoid.powers (f j))
          (Submonoid.powers (f i) ⊔ Submonoid.powers (f j) ⊔ Submonoid.powers (f k))
          le_sup_left)
        * (T j k).map (resLoc (Submonoid.powers (f j) ⊔ Submonoid.powers (f k))
            (Submonoid.powers (f i) ⊔ Submonoid.powers (f j) ⊔ Submonoid.powers (f k))
            (sup_le (le_sup_of_le_left le_sup_right) le_sup_right))
      = (T i k).map (resLoc (Submonoid.powers (f i) ⊔ Submonoid.powers (f k))
          (Submonoid.powers (f i) ⊔ Submonoid.powers (f j) ⊔ Submonoid.powers (f k))
          (sup_le (le_sup_of_le_left le_sup_left) le_sup_right))) :
    ∃ D : ∀ i, VariableChange (Localization (Submonoid.powers (f i))),
      ∀ i j, T i j
        = (D i).map (resLoc (Submonoid.powers (f i))
            (Submonoid.powers (f i) ⊔ Submonoid.powers (f j)) le_sup_left)
          * ((D j).map (resLoc (Submonoid.powers (f j))
              (Submonoid.powers (f i) ⊔ Submonoid.powers (f j)) le_sup_right))⁻¹ := by
  classical
  -- ### Step 1: split the unit layer (`Pic R = 0` for semilocal `R`)
  obtain ⟨v, hv⟩ := exists_units_eq_mul_of_span_eq_top f (fun i j => (T i j).u) hf
    (fun i => by rw [hdiag i]; rfl)
    (fun i j k => by
      have h := congrArg (fun z => (VariableChange.u z).val) (hcoc i j k)
      simpa only [vc_mul_u, Units.val_mul, VariableChange.map_u, Units.coe_map,
        MonoidHom.coe_coe] using h)
  -- conjugate by the unit cochain: the corrected cocycle has `u = 1`
  have hT1coc := vcConj_coc f T hcoc (fun i => ⟨v i, 0, 0, 0⟩)
  set T1 := vcConj f T (fun i => ⟨v i, 0, 0, 0⟩) with hT1def
  have hT1u : ∀ i j, (T1 i j).u = 1 := by
    intro i j
    show (((⟨v i, 0, 0, 0⟩ : VariableChange (Localization (Submonoid.powers (f i)))).map
          (resLoc _ _ le_sup_left))⁻¹ * T i j
        * (⟨v j, 0, 0, 0⟩ : VariableChange (Localization (Submonoid.powers (f j)))).map
          (resLoc _ _ le_sup_right)).u = 1
    rw [vc_mul_u, vc_mul_u, vc_inv_u,
      show ((⟨v i, 0, 0, 0⟩ : VariableChange (Localization (Submonoid.powers (f i)))).map
          (resLoc _ _ le_sup_left)).u
        = (T i j).u * ((⟨v j, 0, 0, 0⟩ : VariableChange
            (Localization (Submonoid.powers (f j)))).map (resLoc _ _ le_sup_right)).u from
        Units.ext (by
          simpa only [VariableChange.map_u, Units.coe_map, Units.val_mul,
            MonoidHom.coe_coe] using hv i j)]
    group
  -- ### Step 2: split the abelian `(r, s)`-layer
  obtain ⟨a, ha⟩ := exists_sub_resLoc_eq_of_span_eq_top f hf (fun i j => (T1 i j).r)
    (fun i j k => by
      have h := congrArg VariableChange.r (hT1coc i j k)
      rw [vc_mul_r] at h
      simpa only [VariableChange.map_r, VariableChange.map_u, hT1u, map_one, Units.val_one,
        one_pow, mul_one] using h)
  obtain ⟨b, hb⟩ := exists_sub_resLoc_eq_of_span_eq_top f hf (fun i j => (T1 i j).s)
    (fun i j k => by
      have h := congrArg VariableChange.s (hT1coc i j k)
      rw [vc_mul_s] at h
      simpa only [VariableChange.map_s, VariableChange.map_u, hT1u, map_one, Units.val_one,
        one_mul] using h)
  -- conjugate by the `(r, s)` cochain: the corrected cocycle is central, `⟨1, 0, 0, τ⟩`
  have hT2coc := vcConj_coc f T1 hT1coc (fun i => ⟨1, a i, b i, 0⟩)
  set T2 := vcConj f T1 (fun i => ⟨1, a i, b i, 0⟩) with hT2def
  have hT2eq : ∀ i j, T2 i j = ⟨1, 0, 0,
      (T1 i j).t + resLoc _ _ le_sup_left (a i) * resLoc _ _ le_sup_left (b i)
        - resLoc _ _ le_sup_left (a i) * (T1 i j).s
        + ((T1 i j).r - resLoc _ _ le_sup_left (a i)) * resLoc _ _ le_sup_right (b j)⟩ := by
    intro i j
    show ((⟨1, a i, b i, 0⟩ : VariableChange (Localization (Submonoid.powers (f i)))).map
          (resLoc _ _ le_sup_left))⁻¹ * T1 i j
        * (⟨1, a j, b j, 0⟩ : VariableChange (Localization (Submonoid.powers (f j)))).map
          (resLoc _ _ le_sup_right) = _
    rw [vc_map_mk_one, vc_map_mk_one, vc_mk_one_conj (T1 i j) (hT1u i j)]
    exact vc_mk_one_congr (by rw [ha i j]; ring) (by rw [hb i j]; ring)
      (by simp only [map_zero]; ring)
  have hT2u : ∀ i j, (T2 i j).u = 1 := fun i j => by rw [hT2eq i j]
  have hT2r : ∀ i j, (T2 i j).r = 0 := fun i j => by rw [hT2eq i j]
  have hT2s : ∀ i j, (T2 i j).s = 0 := fun i j => by rw [hT2eq i j]
  -- ### Step 3: split the central `t`-layer
  obtain ⟨c, hc⟩ := exists_sub_resLoc_eq_of_span_eq_top f hf (fun i j => (T2 i j).t)
    (fun i j k => by
      have h := congrArg VariableChange.t (hT2coc i j k)
      rw [vc_mul_t] at h
      simpa only [VariableChange.map_t, VariableChange.map_r, VariableChange.map_s,
        VariableChange.map_u, hT2u, hT2r, hT2s, map_one, map_zero, Units.val_one, one_pow,
        mul_one, zero_mul, mul_zero, add_zero, zero_add] using h)
  -- conjugate by the `t` cochain: the cocycle is trivial
  have hT3 : ∀ i j, vcConj f T2 (fun i => ⟨1, 0, 0, c i⟩) i j = 1 := by
    intro i j
    show ((⟨1, 0, 0, c i⟩ : VariableChange (Localization (Submonoid.powers (f i)))).map
          (resLoc _ _ le_sup_left))⁻¹ * T2 i j
        * (⟨1, 0, 0, c j⟩ : VariableChange (Localization (Submonoid.powers (f j)))).map
          (resLoc _ _ le_sup_right) = 1
    rw [vc_map_mk_one, vc_map_mk_one, vc_mk_one_conj (T2 i j) (hT2u i j),
      VariableChange.one_def]
    exact vc_mk_one_congr (by rw [hT2r i j]; simp) (by rw [hT2s i j]; simp)
      (by rw [hc i j, hT2r i j, hT2s i j]; simp only [map_zero]; ring)
  -- ### assemble the three cochains
  refine ⟨fun i => (⟨v i, 0, 0, 0⟩ : VariableChange (Localization (Submonoid.powers (f i))))
    * ((⟨1, a i, b i, 0⟩ : VariableChange (Localization (Submonoid.powers (f i))))
      * ⟨1, 0, 0, c i⟩), eq_of_vcConj_eq_one f T _ ?_⟩
  intro i j
  calc vcConj f T (fun i => (⟨v i, 0, 0, 0⟩ : VariableChange
        (Localization (Submonoid.powers (f i))))
        * ((⟨1, a i, b i, 0⟩ : VariableChange (Localization (Submonoid.powers (f i))))
          * ⟨1, 0, 0, c i⟩)) i j
      = vcConj f T (fun i => ((⟨v i, 0, 0, 0⟩ : VariableChange
          (Localization (Submonoid.powers (f i))))
          * ⟨1, a i, b i, 0⟩) * ⟨1, 0, 0, c i⟩) i j :=
        congrArg (fun D => vcConj f T D i j) (funext fun i => (mul_assoc _ _ _).symm)
    _ = vcConj f (vcConj f T (fun i => (⟨v i, 0, 0, 0⟩ : VariableChange
          (Localization (Submonoid.powers (f i)))) * ⟨1, a i, b i, 0⟩))
        (fun i => ⟨1, 0, 0, c i⟩) i j :=
        (vcConj_vcConj f T _ _ i j).symm
    _ = vcConj f (vcConj f (vcConj f T (fun i => ⟨v i, 0, 0, 0⟩))
          (fun i => ⟨1, a i, b i, 0⟩)) (fun i => ⟨1, 0, 0, c i⟩) i j := by
        refine congrArg (fun T' => vcConj f T' (fun i => (⟨1, 0, 0, c i⟩ : VariableChange
          (Localization (Submonoid.powers (f i))))) i j) ?_
        funext i' j'
        exact (vcConj_vcConj f T _ _ i' j').symm
    _ = vcConj f T2 (fun i => ⟨1, 0, 0, c i⟩) i j := by rw [← hT1def, ← hT2def]
    _ = 1 := hT3 i j
