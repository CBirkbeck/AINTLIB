/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project
-/
import ModularCurves.ForMathlib.AffineCechH1

/-!
# Semilocal splitting of unit-valued Čech `1`-cocycles on a finite basic cover

Let `R` be a commutative ring and `f : ι → R` a finite family generating the unit ideal, so the
basic opens `D(fᵢ)` cover `Spec R`.  A **unit-valued Čech `1`-cocycle** for this cover is a family
of units `u i j` of the pairwise-overlap localizations `R[1/fᵢ, 1/fⱼ]` satisfying the cocycle law
`u i j * u j k = u i k` on triple overlaps.  Such a cocycle is precisely the gluing datum of a line
bundle on `Spec R`, and its class is the corresponding element of `Pic (Spec R) = Pic R`.

**Main result** (`exists_units_eq_mul_inv_of_span_eq_top`): if `R` is **semilocal**
(`Finite (MaximalSpectrum R)`) every such cocycle *splits*: there are units `v i` of `R[1/fᵢ]` with
`u i j = v i / v j` on overlaps.  This is `H¹(Spec R, 𝒪ˣ) = Pic R = 0` for semilocal `R`, in the
concrete Čech form consumed by Weierstrass-chart normalization arguments (make the `u`-components
of chart-transition variable changes equal to `1` by rescaling the charts — KM 2.2.5 run
semilocally, where `Pic` vanishes).

The proof is the standard one, made effective:

1. (`gluedSubmodule`) Glue the rank-one free pieces along `u` inside `∏ᵢ R[1/fᵢ]`:
   the submodule of families `x` with `xᵢ = u i j · xⱼ` on overlaps — the module of global
   sections of the line bundle defined by `u`.
2. (`isLocalizedModule_gluedProj`) **Quasi-coherence of the glued sections**: the projection
   `gluedSubmodule → R[1/fᵢ₀]` is the localization of the glued module at `powers fᵢ₀`.  This is
   the affine `H⁰`-extension argument by partition of unity, using the power denominator-clearing
   and torsion-killing toolkit of `ForMathlib/AffineCechH1`.
3. Hence the glued module is finite (`Module.Finite.of_isLocalized_maximal`), flat
   (`Module.flat_of_isLocalized_maximal`) and of fibre rank one at every maximal ideal, so it is
   **free** by Stacks 02M9 (`Module.free_of_flat_of_finrank_eq`) over the semilocal `R`; a basis
   vector has unit components, and its components are the splitting `v`.

Everything is stated over the join submonoids `powers fᵢ ⊔ powers fⱼ` (as in
`ForMathlib/AffineCechH1`); the bridges `isLocalizedModule_sup_of_powers_mul` /
`…_sup_sup_of_powers_mul` re-express `Localization.Away (fᵢ * fⱼ)` data in this form.
-/

open IsLocalizedModule TensorProduct

namespace SemilocalUnitSplit

variable {R : Type*} [CommRing R]

/-- The algebra localization map is a localized-module map (the ring-to-module dictionary). -/
theorem isLocalizedModule_algebraLinearMap (S : Submonoid R) :
    IsLocalizedModule S (Algebra.linearMap R (Localization S)) :=
  isLocalizedModule_iff_isLocalization.mpr inferInstance

attribute [local instance] isLocalizedModule_algebraLinearMap

/-- Ring-level and module-level localization fractions agree. -/
theorem mk'_ring_eq_mk'_module (S : Submonoid R) (x : R) (s : S) :
    IsLocalization.mk' (Localization S) x s
      = IsLocalizedModule.mk' (Algebra.linearMap R (Localization S)) x s := by
  rw [IsLocalization.mk'_eq_iff_eq_mul, mul_comm, ← Algebra.smul_def, ← Submonoid.smul_def,
    IsLocalizedModule.mk'_cancel']
  rfl

/-! ### The canonical restriction maps between localizations at nested submonoids -/

/-- The canonical ring map `R[S₁⁻¹] →+* R[S₂⁻¹]` for `S₁ ≤ S₂` — restriction of functions
along an inclusion of basic opens. -/
noncomputable def resLoc (S₁ S₂ : Submonoid R) (h : S₁ ≤ S₂) :
    Localization S₁ →+* Localization S₂ :=
  IsLocalization.map _ (RingHom.id R) (show S₁ ≤ S₂.comap (RingHom.id R) from h)

theorem resLoc_algebraMap (S₁ S₂ : Submonoid R) (h : S₁ ≤ S₂) (r : R) :
    resLoc S₁ S₂ h (algebraMap R (Localization S₁) r) = algebraMap R (Localization S₂) r := by
  simp [resLoc, IsLocalization.map_eq]

theorem resLoc_smul (S₁ S₂ : Submonoid R) (h : S₁ ≤ S₂) (r : R) (x : Localization S₁) :
    resLoc S₁ S₂ h (r • x) = r • resLoc S₁ S₂ h x := by
  rw [Algebra.smul_def, map_mul, resLoc_algebraMap, ← Algebra.smul_def]

/-- The module-theoretic incarnation of `resLoc`: it is the `IsLocalizedModule.liftOfLE`
comparison of the two algebra localizations.  This is the bridge along which the
`AffineCechH1` toolkit applies to `resLoc`. -/
theorem resLoc_eq_liftOfLE (S₁ S₂ : Submonoid R) (h : S₁ ≤ S₂) (x : Localization S₁) :
    resLoc S₁ S₂ h x
      = liftOfLE S₁ S₂ h (Algebra.linearMap R (Localization S₁))
          (Algebra.linearMap R (Localization S₂)) x := by
  obtain ⟨y, s, rfl⟩ := IsLocalization.exists_mk'_eq (M := S₁) x
  have hL : resLoc S₁ S₂ h (IsLocalization.mk' (Localization S₁) y s)
      = IsLocalization.mk' (Localization S₂) y ⟨(s : R), h s.2⟩ := by
    simp only [resLoc]
    rw [IsLocalization.map_mk']
    rfl
  rw [hL, mk'_ring_eq_mk'_module S₁, liftOfLE_mk', ← mk'_ring_eq_mk'_module]

/-- Composition of restrictions is restriction (any inclusion proof may be used). -/
theorem resLoc_resLoc (S₁ S₂ S₃ : Submonoid R) (h₁ : S₁ ≤ S₂) (h₂ : S₂ ≤ S₃) (h₃ : S₁ ≤ S₃)
    (x : Localization S₁) :
    resLoc S₂ S₃ h₂ (resLoc S₁ S₂ h₁ x) = resLoc S₁ S₃ h₃ x := by
  rw [resLoc_eq_liftOfLE, resLoc_eq_liftOfLE, resLoc_eq_liftOfLE, liftOfLE_liftOfLE]

/-- Restriction to a localization on which the larger submonoid already acts invertibly is
injective. -/
theorem resLoc_injective (S₁ S₂ : Submonoid R) (h : S₁ ≤ S₂)
    (hu : ∀ s ∈ S₂, IsUnit (algebraMap R (Localization S₁) s)) :
    Function.Injective (resLoc S₁ S₂ h) := by
  intro x y hxy
  obtain ⟨x, s, rfl⟩ := IsLocalization.exists_mk'_eq (M := S₁) x
  obtain ⟨y, t, rfl⟩ := IsLocalization.exists_mk'_eq (M := S₁) y
  rw [resLoc, IsLocalization.map_mk', IsLocalization.map_mk',
    IsLocalization.mk'_eq_iff_eq] at hxy
  obtain ⟨c, hc⟩ := (IsLocalization.eq_iff_exists S₂ (Localization S₂)).mp hxy
  rw [IsLocalization.mk'_eq_iff_eq]
  apply (hu c c.2).mul_left_cancel
  rw [← map_mul, ← map_mul]
  exact congrArg (algebraMap R (Localization S₁)) hc

/-! ### Fibre plumbing: `(R⧸I) ⊗ X` via pure tensors, kernels, and power-clearing -/

section QuotientFibre

/-- Cancellation of a unit scalar. -/
theorem smul_cancel_of_isUnit {A : Type*} [CommRing A] {V : Type*} [AddCommGroup V]
    [Module A V] {c : A} (hc : IsUnit c) {z : V} (h : c • z = 0) : z = 0 := by
  obtain ⟨u, rfl⟩ := hc
  calc z = (((u⁻¹ : Aˣ) : A) * ((u : Aˣ) : A)) • z := by rw [Units.inv_mul, one_smul]
    _ = ((u⁻¹ : Aˣ) : A) • ((u : Aˣ) : A) • z := by rw [mul_smul]
    _ = 0 := by rw [h, smul_zero]

/-- Every element of `(R⧸I) ⊗[R] X` is a pure tensor `1 ⊗ x` (the scalars surject from `R`). -/
theorem exists_one_tmul (I : Ideal R) {X : Type*} [AddCommGroup X] [Module R X]
    (z : (R ⧸ I) ⊗[R] X) : ∃ x : X, z = 1 ⊗ₜ[R] x := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, (TensorProduct.tmul_zero _ _).symm⟩
  | tmul c x =>
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective c
    refine ⟨r • x, ?_⟩
    rw [← TensorProduct.smul_tmul, ← Algebra.algebraMap_eq_smul_one,
      Ideal.Quotient.algebraMap_eq]
  | add z₁ z₂ h₁ h₂ =>
    obtain ⟨x₁, rfl⟩ := h₁
    obtain ⟨x₂, rfl⟩ := h₂
    exact ⟨x₁ + x₂, (TensorProduct.tmul_add _ _ _).symm⟩

/-- The `R`-action on `(R⧸I) ⊗[R] X` inside a pure tensor is the residue scalar action. -/
theorem one_tmul_smul (I : Ideal R) {X : Type*} [AddCommGroup X] [Module R X]
    (r : R) (x : X) :
    (1 ⊗ₜ[R] (r • x) : (R ⧸ I) ⊗[R] X) = Ideal.Quotient.mk I r • (1 ⊗ₜ[R] x) := by
  rw [TensorProduct.tmul_smul, ← Ideal.Quotient.algebraMap_eq, IsScalarTower.algebraMap_smul]

/-- The kernel of `x ↦ 1 ⊗ x` into `(R⧸I) ⊗[R] X` is `I • ⊤`
(`quotTensorEquivQuotSMul` in membership form). -/
theorem one_tmul_eq_zero_iff (I : Ideal R) {X : Type*} [AddCommGroup X] [Module R X]
    (x : X) : (1 ⊗ₜ[R] x : (R ⧸ I) ⊗[R] X) = 0 ↔ x ∈ I • (⊤ : Submodule R X) := by
  rw [← (quotTensorEquivQuotSMul X I).map_eq_zero_iff,
    TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul, Submodule.Quotient.mk_eq_zero]

/-- **Power-clearing in `I • ⊤` along a localization**: a member of `I • ⊤` of the localized
module is, after multiplication by a denominator, the image of a member of `I • ⊤` upstairs. -/
theorem exists_smul_eq_of_mem_smul_top {M M' : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup M'] [Module R M'] (S : Submonoid R) (l : M →ₗ[R] M') [IsLocalizedModule S l]
    (I : Ideal R) {x : M'} (hx : x ∈ I • (⊤ : Submodule R M')) :
    ∃ (s : R) (_ : s ∈ S) (m : M), m ∈ I • (⊤ : Submodule R M) ∧ s • x = l m := by
  refine Submodule.smul_induction_on hx ?_ ?_
  · intro r hr n _
    obtain ⟨⟨m, s⟩, hms⟩ := IsLocalizedModule.surj S l n
    rw [Submonoid.smul_def] at hms
    refine ⟨(s : R), s.2, r • m, Submodule.smul_mem_smul hr Submodule.mem_top, ?_⟩
    rw [map_smul, ← hms, smul_comm]
  · rintro x y ⟨s, hs, m, hm, hsm⟩ ⟨t, ht, n, hn, htn⟩
    refine ⟨s * t, mul_mem hs ht, t • m + s • n,
      Submodule.add_mem _ (Submodule.smul_mem _ _ hm) (Submodule.smul_mem _ _ hn), ?_⟩
    rw [map_add, map_smul, map_smul, ← hsm, ← htn, smul_add, mul_smul, mul_smul,
      smul_comm s t x]

end QuotientFibre

/-! ### The additive Čech split in the `resLoc` vocabulary (the `3b` entry point) -/

section AdditiveResLoc

/-- **Ring-form of the finite-cover affine Čech `H¹` vanishing**, in the `resLoc` vocabulary of
this file: an additive Čech `1`-cocycle valued in the pairwise-overlap localizations splits as a
coboundary `c i j = a i - a j`.  Thin wrapper of
`IsLocalizedModule.exists_sub_liftOfLE_eq_of_span_eq_top` along `resLoc_eq_liftOfLE`; this is
the form the nilpotent-layer chart-Čech splits (`r`, `s`, then central `t`) consume. -/
theorem exists_sub_resLoc_eq_of_span_eq_top {ι : Type*} [Fintype ι] (f : ι → R)
    (hf : Ideal.span (Set.range f) = ⊤)
    (c : ∀ i j, Localization (Submonoid.powers (f i) ⊔ Submonoid.powers (f j)))
    (hcoc : ∀ i j k,
      resLoc (Submonoid.powers (f i) ⊔ Submonoid.powers (f j))
          (Submonoid.powers (f i) ⊔ Submonoid.powers (f j) ⊔ Submonoid.powers (f k))
          le_sup_left (c i j)
        + resLoc (Submonoid.powers (f j) ⊔ Submonoid.powers (f k))
            (Submonoid.powers (f i) ⊔ Submonoid.powers (f j) ⊔ Submonoid.powers (f k))
            (sup_le (le_sup_of_le_left le_sup_right) le_sup_right) (c j k)
      = resLoc (Submonoid.powers (f i) ⊔ Submonoid.powers (f k))
          (Submonoid.powers (f i) ⊔ Submonoid.powers (f j) ⊔ Submonoid.powers (f k))
          (sup_le (le_sup_of_le_left le_sup_left) le_sup_right) (c i k)) :
    ∃ a : ∀ i, Localization (Submonoid.powers (f i)),
      ∀ i j, c i j
        = resLoc (Submonoid.powers (f i))
            (Submonoid.powers (f i) ⊔ Submonoid.powers (f j)) le_sup_left (a i)
          - resLoc (Submonoid.powers (f j))
              (Submonoid.powers (f i) ⊔ Submonoid.powers (f j)) le_sup_right (a j) := by
  obtain ⟨a, ha⟩ := IsLocalizedModule.exists_sub_liftOfLE_eq_of_span_eq_top f
    (fun i => Algebra.linearMap R (Localization (Submonoid.powers (f i))))
    (fun i j => Algebra.linearMap R
      (Localization (Submonoid.powers (f i) ⊔ Submonoid.powers (f j))))
    (fun i j k => Algebra.linearMap R
      (Localization (Submonoid.powers (f i) ⊔ Submonoid.powers (f j)
        ⊔ Submonoid.powers (f k))))
    hf c (fun i j k => by
      rw [← resLoc_eq_liftOfLE, ← resLoc_eq_liftOfLE, ← resLoc_eq_liftOfLE]
      exact hcoc i j k)
  exact ⟨a, fun i j => by rw [ha i j, ← resLoc_eq_liftOfLE, ← resLoc_eq_liftOfLE]⟩

end AdditiveResLoc

/-! ### The glued module of a unit cocycle -/

section Glued

variable {ι : Type*} (f : ι → R)
  (u : ∀ i j : ι,
    (Localization (Submonoid.powers (f i) ⊔ Submonoid.powers (f j)))ˣ)

/-- **The module of global sections of the line bundle glued from the unit cocycle `u`**:
families over the cover matching along `u` on pairwise overlaps. -/
noncomputable def gluedSubmodule :
    Submodule R (∀ i, Localization (Submonoid.powers (f i))) where
  carrier := {x | ∀ i j,
    resLoc (Submonoid.powers (f i)) (Submonoid.powers (f i) ⊔ Submonoid.powers (f j))
      le_sup_left (x i)
    = (u i j).val
        * resLoc (Submonoid.powers (f j)) (Submonoid.powers (f i) ⊔ Submonoid.powers (f j))
            le_sup_right (x j)}
  add_mem' {a b} ha hb i j := by
    rw [Pi.add_apply, Pi.add_apply, map_add, map_add, mul_add, ha i j, hb i j]
  zero_mem' i j := by rw [Pi.zero_apply, Pi.zero_apply, map_zero, map_zero, mul_zero]
  smul_mem' r x hx i j := by
    rw [Pi.smul_apply, Pi.smul_apply, resLoc_smul, resLoc_smul, hx i j, mul_smul_comm]

theorem mem_gluedSubmodule_iff {x : ∀ i, Localization (Submonoid.powers (f i))} :
    x ∈ gluedSubmodule f u ↔ ∀ i j,
      resLoc (Submonoid.powers (f i)) (Submonoid.powers (f i) ⊔ Submonoid.powers (f j))
        le_sup_left (x i)
      = (u i j).val
          * resLoc (Submonoid.powers (f j))
              (Submonoid.powers (f i) ⊔ Submonoid.powers (f j)) le_sup_right (x j) :=
  Iff.rfl

/-- The component projection of the glued module. -/
noncomputable def gluedProj (i₀ : ι) :
    gluedSubmodule f u →ₗ[R] Localization (Submonoid.powers (f i₀)) :=
  (LinearMap.proj i₀).comp (gluedSubmodule f u).subtype

@[simp] theorem gluedProj_apply (i₀ : ι) (x : gluedSubmodule f u) :
    gluedProj f u i₀ x = x.1 i₀ :=
  rfl

/-- Every element of the join `powers g ⊔ powers g` acts invertibly on `Localization (powers g)`
(both factors of a `mem_sup` decomposition do). -/
theorem isUnit_algebraMap_of_mem_sup_self (g : R) {s : R}
    (hs : s ∈ Submonoid.powers g ⊔ Submonoid.powers g) :
    IsUnit (algebraMap R (Localization (Submonoid.powers g)) s) := by
  obtain ⟨a, ha, b, hb, rfl⟩ := Submonoid.mem_sup.mp hs
  rw [map_mul]
  exact (IsLocalization.map_units (Localization (Submonoid.powers g)) ⟨a, ha⟩).mul
    (IsLocalization.map_units (Localization (Submonoid.powers g)) ⟨b, hb⟩)

/-- **Quasi-coherence of the glued sections (the affine `H⁰` lemma).**  For a finite family `f`
generating the unit ideal and a normalized unit cocycle `u` on the basic cover `{D(fᵢ)}`, the
component projection `gluedSubmodule → R[1/fᵢ₀]` is the localization of the glued module at
`powers fᵢ₀`.  Surjectivity-after-clearing is the partition-of-unity extension argument;
injectivity-torsion is componentwise power-killing. -/
theorem isLocalizedModule_gluedProj [Fintype ι]
    (hone : ∀ i, u i i = 1)
    (hcoc : ∀ i j k,
      resLoc (Submonoid.powers (f i) ⊔ Submonoid.powers (f j))
          (Submonoid.powers (f i) ⊔ Submonoid.powers (f j) ⊔ Submonoid.powers (f k))
          le_sup_left (u i j).val
        * resLoc (Submonoid.powers (f j) ⊔ Submonoid.powers (f k))
            (Submonoid.powers (f i) ⊔ Submonoid.powers (f j) ⊔ Submonoid.powers (f k))
            (sup_le (le_sup_of_le_left le_sup_right) le_sup_right) (u j k).val
      = resLoc (Submonoid.powers (f i) ⊔ Submonoid.powers (f k))
          (Submonoid.powers (f i) ⊔ Submonoid.powers (f j) ⊔ Submonoid.powers (f k))
          (sup_le (le_sup_of_le_left le_sup_left) le_sup_right) (u i k).val)
    (i₀ : ι) :
    IsLocalizedModule (Submonoid.powers (f i₀)) (gluedProj f u i₀) := by
  classical
  constructor
  · -- `map_units`: `powers fᵢ₀` acts invertibly on the target localization
    exact fun s => IsLocalizedModule.map_units
      (Algebra.linearMap R (Localization (Submonoid.powers (f i₀)))) s
  · -- `surj`: the partition-of-unity `H⁰`-extension argument
    intro y
    -- the transported candidate components on the `(j, i₀)` overlaps
    set w : ∀ j, Localization (Submonoid.powers (f j) ⊔ Submonoid.powers (f i₀)) :=
      fun j => (u j i₀).val
        * resLoc (Submonoid.powers (f i₀))
            (Submonoid.powers (f j) ⊔ Submonoid.powers (f i₀)) le_sup_right y with hw
    -- Step A: clear the `i₀`-denominator of every `w j` at one uniform power `N`
    have hA : ∀ j, ∃ (n : ℕ) (b : Localization (Submonoid.powers (f j))),
        resLoc (Submonoid.powers (f j))
          (Submonoid.powers (f j) ⊔ Submonoid.powers (f i₀)) le_sup_left b
        = f i₀ ^ n • w j := by
      intro j
      obtain ⟨n, b, hb⟩ := exists_liftOfLE_eq_pow_smul (Submonoid.powers (f j)) (f i₀)
        (Algebra.linearMap R (Localization (Submonoid.powers (f j))))
        (Algebra.linearMap R
          (Localization (Submonoid.powers (f j) ⊔ Submonoid.powers (f i₀)))) (w j)
      exact ⟨n, b, by rw [resLoc_eq_liftOfLE]; exact hb⟩
    choose n₀ b₀ hb₀ using hA
    set N : ℕ := Finset.univ.sup n₀ with hN
    have hn₀N : ∀ j, n₀ j ≤ N := fun j => Finset.le_sup (Finset.mem_univ j)
    have hBex : ∀ j, ∃ b : Localization (Submonoid.powers (f j)),
        resLoc (Submonoid.powers (f j))
          (Submonoid.powers (f j) ⊔ Submonoid.powers (f i₀)) le_sup_left b
        = f i₀ ^ N • w j := fun j =>
      ⟨f i₀ ^ (N - n₀ j) • b₀ j, by
        rw [resLoc_smul, hb₀ j, smul_smul, ← pow_add, Nat.sub_add_cancel (hn₀N j)]⟩
    choose B hB using hBex
    -- Step B: the pair defects die in the triple localization (cocycle law), hence are
    -- killed by one uniform power `M` of `fᵢ₀`
    have h1 : ∀ j k,
        resLoc (Submonoid.powers (f j) ⊔ Submonoid.powers (f k))
          (Submonoid.powers (f j) ⊔ Submonoid.powers (f k) ⊔ Submonoid.powers (f i₀))
          le_sup_left
          (resLoc (Submonoid.powers (f j))
            (Submonoid.powers (f j) ⊔ Submonoid.powers (f k)) le_sup_left (B j))
        = f i₀ ^ N •
            (resLoc (Submonoid.powers (f j) ⊔ Submonoid.powers (f i₀))
                (Submonoid.powers (f j) ⊔ Submonoid.powers (f k) ⊔ Submonoid.powers (f i₀))
                (sup_le (le_sup_of_le_left le_sup_left) le_sup_right) (u j i₀).val
              * resLoc (Submonoid.powers (f i₀))
                  (Submonoid.powers (f j) ⊔ Submonoid.powers (f k) ⊔ Submonoid.powers (f i₀))
                  le_sup_right y) := by
      intro j k
      rw [resLoc_resLoc _ _ _ le_sup_left le_sup_left (le_sup_of_le_left le_sup_left) (B j),
        ← resLoc_resLoc (Submonoid.powers (f j))
          (Submonoid.powers (f j) ⊔ Submonoid.powers (f i₀))
          (Submonoid.powers (f j) ⊔ Submonoid.powers (f k) ⊔ Submonoid.powers (f i₀))
          le_sup_left (sup_le (le_sup_of_le_left le_sup_left) le_sup_right)
          (le_sup_of_le_left le_sup_left) (B j),
        hB j, resLoc_smul, hw]
      rw [map_mul,
        resLoc_resLoc (Submonoid.powers (f i₀))
          (Submonoid.powers (f j) ⊔ Submonoid.powers (f i₀))
          (Submonoid.powers (f j) ⊔ Submonoid.powers (f k) ⊔ Submonoid.powers (f i₀))
          le_sup_right (sup_le (le_sup_of_le_left le_sup_left) le_sup_right) le_sup_right y]
    have h2 : ∀ j k,
        resLoc (Submonoid.powers (f j) ⊔ Submonoid.powers (f k))
          (Submonoid.powers (f j) ⊔ Submonoid.powers (f k) ⊔ Submonoid.powers (f i₀))
          le_sup_left
          (resLoc (Submonoid.powers (f k))
            (Submonoid.powers (f j) ⊔ Submonoid.powers (f k)) le_sup_right (B k))
        = f i₀ ^ N •
            (resLoc (Submonoid.powers (f k) ⊔ Submonoid.powers (f i₀))
                (Submonoid.powers (f j) ⊔ Submonoid.powers (f k) ⊔ Submonoid.powers (f i₀))
                (sup_le (le_sup_of_le_left le_sup_right) le_sup_right) (u k i₀).val
              * resLoc (Submonoid.powers (f i₀))
                  (Submonoid.powers (f j) ⊔ Submonoid.powers (f k) ⊔ Submonoid.powers (f i₀))
                  le_sup_right y) := by
      intro j k
      rw [resLoc_resLoc _ _ _ le_sup_right le_sup_left (le_sup_of_le_left le_sup_right) (B k),
        ← resLoc_resLoc (Submonoid.powers (f k))
          (Submonoid.powers (f k) ⊔ Submonoid.powers (f i₀))
          (Submonoid.powers (f j) ⊔ Submonoid.powers (f k) ⊔ Submonoid.powers (f i₀))
          le_sup_left (sup_le (le_sup_of_le_left le_sup_right) le_sup_right)
          (le_sup_of_le_left le_sup_right) (B k),
        hB k, resLoc_smul, hw]
      rw [map_mul,
        resLoc_resLoc (Submonoid.powers (f i₀))
          (Submonoid.powers (f k) ⊔ Submonoid.powers (f i₀))
          (Submonoid.powers (f j) ⊔ Submonoid.powers (f k) ⊔ Submonoid.powers (f i₀))
          le_sup_right (sup_le (le_sup_of_le_left le_sup_right) le_sup_right) le_sup_right y]
    have hdie : ∀ j k,
        resLoc (Submonoid.powers (f j) ⊔ Submonoid.powers (f k))
          (Submonoid.powers (f j) ⊔ Submonoid.powers (f k) ⊔ Submonoid.powers (f i₀))
          le_sup_left
          (resLoc (Submonoid.powers (f j))
              (Submonoid.powers (f j) ⊔ Submonoid.powers (f k)) le_sup_left (B j)
            - (u j k).val
              * resLoc (Submonoid.powers (f k))
                  (Submonoid.powers (f j) ⊔ Submonoid.powers (f k)) le_sup_right (B k))
        = 0 := by
      intro j k
      rw [map_sub, map_mul, h1 j k, h2 j k, mul_smul_comm, ← smul_sub, ← mul_assoc,
        hcoc j k i₀, sub_self, smul_zero]
    have hkill : ∀ j k, ∃ m : ℕ, f i₀ ^ m •
        (resLoc (Submonoid.powers (f j))
            (Submonoid.powers (f j) ⊔ Submonoid.powers (f k)) le_sup_left (B j)
          - (u j k).val
            * resLoc (Submonoid.powers (f k))
                (Submonoid.powers (f j) ⊔ Submonoid.powers (f k)) le_sup_right (B k)) = 0 := by
      intro j k
      refine exists_pow_smul_eq_zero_of_liftOfLE_eq_zero
        (Submonoid.powers (f j) ⊔ Submonoid.powers (f k)) (f i₀)
        (Algebra.linearMap R
          (Localization (Submonoid.powers (f j) ⊔ Submonoid.powers (f k))))
        (Algebra.linearMap R (Localization
          (Submonoid.powers (f j) ⊔ Submonoid.powers (f k) ⊔ Submonoid.powers (f i₀)))) ?_
      rw [← resLoc_eq_liftOfLE]
      exact hdie j k
    choose m₀ hm₀ using hkill
    set M : ℕ := Finset.univ.sup (fun p : ι × ι => m₀ p.1 p.2) with hM
    have hm₀M : ∀ j k, m₀ j k ≤ M := fun j k =>
      Finset.le_sup (f := fun p : ι × ι => m₀ p.1 p.2) (Finset.mem_univ (j, k))
    have hMkill : ∀ j k, f i₀ ^ M •
        (resLoc (Submonoid.powers (f j))
            (Submonoid.powers (f j) ⊔ Submonoid.powers (f k)) le_sup_left (B j)
          - (u j k).val
            * resLoc (Submonoid.powers (f k))
                (Submonoid.powers (f j) ⊔ Submonoid.powers (f k)) le_sup_right (B k)) = 0 := by
      intro j k
      rw [show f i₀ ^ M = f i₀ ^ (M - m₀ j k) * f i₀ ^ (m₀ j k) by
          rw [← pow_add, Nat.sub_add_cancel (hm₀M j k)],
        mul_smul, hm₀ j k, smul_zero]
    -- Step C: the corrected family is a global section extending `y` up to `fᵢ₀ ^ (M + N)`
    have hxmem : (fun j => f i₀ ^ M • B j) ∈ gluedSubmodule f u := by
      intro j k
      show resLoc (Submonoid.powers (f j))
          (Submonoid.powers (f j) ⊔ Submonoid.powers (f k)) le_sup_left (f i₀ ^ M • B j)
        = (u j k).val
            * resLoc (Submonoid.powers (f k))
                (Submonoid.powers (f j) ⊔ Submonoid.powers (f k)) le_sup_right
                (f i₀ ^ M • B k)
      rw [resLoc_smul, resLoc_smul, mul_smul_comm]
      have h := hMkill j k
      rw [smul_sub, sub_eq_zero] at h
      exact h
    have hBi₀ : B i₀ = f i₀ ^ N • y := by
      apply resLoc_injective (Submonoid.powers (f i₀))
        (Submonoid.powers (f i₀) ⊔ Submonoid.powers (f i₀)) le_sup_left
        (fun s hs => isUnit_algebraMap_of_mem_sup_self (f i₀) hs)
      rw [hB i₀, resLoc_smul, hw]
      simp only [hone i₀, Units.val_one, one_mul]
    refine ⟨⟨⟨_, hxmem⟩, ⟨f i₀ ^ (M + N), ⟨M + N, rfl⟩⟩⟩, ?_⟩
    simp only [gluedProj_apply, Submonoid.smul_def]
    show f i₀ ^ (M + N) • y = f i₀ ^ M • B i₀
    rw [hBi₀, smul_smul, ← pow_add]
  · -- `exists_of_eq`: componentwise power-torsion of a section vanishing at `i₀`
    intro x₁ x₂ hx
    have hz : ∀ j, ∃ n : ℕ, f i₀ ^ n • (x₁.1 j - x₂.1 j) = 0 := by
      intro j
      refine exists_pow_smul_eq_zero_of_liftOfLE_eq_zero
        (Submonoid.powers (f j)) (f i₀)
        (Algebra.linearMap R (Localization (Submonoid.powers (f j))))
        (Algebra.linearMap R
          (Localization (Submonoid.powers (f j) ⊔ Submonoid.powers (f i₀)))) ?_
      rw [← resLoc_eq_liftOfLE, map_sub, x₁.2 j i₀, x₂.2 j i₀,
        show x₁.1 i₀ = x₂.1 i₀ from hx, sub_self]
    choose n₁ hn₁ using hz
    refine ⟨⟨f i₀ ^ Finset.univ.sup n₁, ⟨Finset.univ.sup n₁, rfl⟩⟩, ?_⟩
    apply Subtype.ext
    funext j
    have hle : n₁ j ≤ Finset.univ.sup n₁ := Finset.le_sup (Finset.mem_univ j)
    have hkillj : f i₀ ^ Finset.univ.sup n₁ • (x₁.1 j - x₂.1 j) = 0 := by
      rw [show Finset.univ.sup n₁ = Finset.univ.sup n₁ - n₁ j + n₁ j from
          (Nat.sub_add_cancel hle).symm,
        pow_add, mul_smul, hn₁ j, smul_zero]
    rw [smul_sub, sub_eq_zero] at hkillj
    simpa only [Submonoid.smul_def, SetLike.val_smul, Pi.smul_apply] using hkillj

/-! ### The semilocal finale: the glued module is free of rank one, and the cocycle splits -/

/-- A covering family avoids any proper ideal at some index. -/
theorem exists_notMem_of_span_eq_top (hf : Ideal.span (Set.range f) = ⊤) {P : Ideal R}
    (hP : P ≠ ⊤) : ∃ i, f i ∉ P := by
  by_contra h
  push Not at h
  refine hP (top_le_iff.mp ?_)
  rw [← hf]
  refine Ideal.span_le.mpr ?_
  rintro x ⟨i, rfl⟩
  exact h i

/-- Powers of an element outside a prime lie in its complement submonoid. -/
theorem powers_le_primeCompl {P : Ideal R} [P.IsPrime] {a : R} (ha : a ∉ P) :
    Submonoid.powers a ≤ P.primeCompl := by
  rintro x ⟨n, rfl⟩
  exact fun hx => ha (Ideal.IsPrime.mem_of_pow_mem ‹P.IsPrime› n hx)

/-- The Stacks 02M9 fibre-rank input for the glued module: at a maximal ideal `P` with chart
witness `f i ∉ P`, the fibre `(R⧸P) ⊗ gluedSubmodule` is one-dimensional.

The base change of the localization `gluedProj f u i` along `R → R⧸P` is bijective —
surjectivity from `IsLocalizedModule.surj` plus invertibility of the image of `fᵢ` in the field
`R⧸P`, injectivity from the `I • ⊤` power-clearing (`exists_smul_eq_of_mem_smul_top`) and
`IsLocalizedModule.exists_of_eq`-torsion — and `(R⧸P) ⊗ Lᵢ` is spanned by the nonzero vector
`1 ⊗ 1` (the classical `κ(P) ⊗ R_f ≅ κ(P)` for `f ∉ P`). -/
theorem finrank_quotient_tensor_gluedSubmodule [Fintype ι]
    (hone : ∀ i, u i i = 1)
    (hcoc : ∀ i j k,
      resLoc (Submonoid.powers (f i) ⊔ Submonoid.powers (f j))
          (Submonoid.powers (f i) ⊔ Submonoid.powers (f j) ⊔ Submonoid.powers (f k))
          le_sup_left (u i j).val
        * resLoc (Submonoid.powers (f j) ⊔ Submonoid.powers (f k))
            (Submonoid.powers (f i) ⊔ Submonoid.powers (f j) ⊔ Submonoid.powers (f k))
            (sup_le (le_sup_of_le_left le_sup_right) le_sup_right) (u j k).val
      = resLoc (Submonoid.powers (f i) ⊔ Submonoid.powers (f k))
          (Submonoid.powers (f i) ⊔ Submonoid.powers (f j) ⊔ Submonoid.powers (f k))
          (sup_le (le_sup_of_le_left le_sup_left) le_sup_right) (u i k).val)
    (P : Ideal R) [P.IsMaximal] (i : ι) (hi : f i ∉ P) :
    Module.finrank (R ⧸ P) ((R ⧸ P) ⊗[R] (gluedSubmodule f u)) = 1 := by
  classical
  letI := Ideal.Quotient.field P
  haveI := isLocalizedModule_gluedProj f u hone hcoc i
  -- powers of `fᵢ` are units mod `P`
  have hmkunit : ∀ s ∈ Submonoid.powers (f i), IsUnit (Ideal.Quotient.mk P s) := by
    rintro s ⟨n, rfl⟩
    refine isUnit_iff_ne_zero.mpr fun h0 => hi ?_
    exact (Ideal.IsMaximal.isPrime ‹P.IsMaximal›).mem_of_pow_mem n
      (Ideal.Quotient.eq_zero_iff_mem.mp h0)
  -- `⊗ κ(P)` of the localization `gluedProj i` is bijective
  have hsurj : Function.Surjective (LinearMap.baseChange (R ⧸ P) (gluedProj f u i)) := by
    intro z
    obtain ⟨y, rfl⟩ := exists_one_tmul P z
    obtain ⟨⟨m, s⟩, hms⟩ := IsLocalizedModule.surj (Submonoid.powers (f i)) (gluedProj f u i) y
    rw [Submonoid.smul_def] at hms
    obtain ⟨c, hc⟩ := (hmkunit (s : R) s.2).exists_left_inv
    refine ⟨c • (1 ⊗ₜ[R] m), ?_⟩
    have hmap : (LinearMap.baseChange (R ⧸ P) (gluedProj f u i)) (c • (1 ⊗ₜ[R] m))
        = c • (LinearMap.baseChange (R ⧸ P) (gluedProj f u i)) (1 ⊗ₜ[R] m) :=
      (LinearMap.baseChange (R ⧸ P) (gluedProj f u i)).map_smul c (1 ⊗ₜ[R] m)
    rw [hmap, LinearMap.baseChange_tmul, ← hms, one_tmul_smul, smul_smul, hc, one_smul]
  have hinj : Function.Injective (LinearMap.baseChange (R ⧸ P) (gluedProj f u i)) := by
    refine (injective_iff_map_eq_zero _).mpr fun z hz => ?_
    obtain ⟨m, rfl⟩ := exists_one_tmul P z
    rw [LinearMap.baseChange_tmul, one_tmul_eq_zero_iff] at hz
    obtain ⟨s, hsS, m', hm', hsm'⟩ := exists_smul_eq_of_mem_smul_top
      (Submonoid.powers (f i)) (gluedProj f u i) P hz
    rw [← map_smul] at hsm'
    obtain ⟨t, ht⟩ := IsLocalizedModule.exists_of_eq (S := Submonoid.powers (f i)) hsm'
    simp only [Submonoid.smul_def] at ht
    rw [smul_smul] at ht
    have hmem : ((t : R) * s) • m ∈ P • (⊤ : Submodule R (gluedSubmodule f u)) := by
      rw [ht]
      exact Submodule.smul_mem _ _ hm'
    have h0 : (Ideal.Quotient.mk P ((t : R) * s))
        • (1 ⊗ₜ[R] m : (R ⧸ P) ⊗[R] (gluedSubmodule f u)) = 0 := by
      rw [← one_tmul_smul]
      exact (one_tmul_eq_zero_iff P _).mpr hmem
    exact smul_cancel_of_isUnit (hmkunit _ (mul_mem t.2 hsS)) h0
  -- `κ(P) ⊗ Lᵢ` is one-dimensional: `1 ⊗ 1` is a basis vector
  have hv : (1 ⊗ₜ[R] (1 : Localization (Submonoid.powers (f i)))
      : (R ⧸ P) ⊗[R] Localization (Submonoid.powers (f i))) ≠ 0 := by
    intro h0
    rw [one_tmul_eq_zero_iff] at h0
    obtain ⟨s, hsS, r', hr', hsr'⟩ := exists_smul_eq_of_mem_smul_top
      (Submonoid.powers (f i))
      (Algebra.linearMap R (Localization (Submonoid.powers (f i)))) P h0
    rw [Algebra.linearMap_apply, ← Algebra.algebraMap_eq_smul_one] at hsr'
    obtain ⟨t, ht⟩ := (IsLocalization.eq_iff_exists (Submonoid.powers (f i))
      (Localization (Submonoid.powers (f i)))).mp hsr'
    have hr'P : r' ∈ P := by
      refine Submodule.smul_induction_on hr' (fun r hr n _ => ?_)
        (fun a b ha hb => P.add_mem ha hb)
      rw [smul_eq_mul]
      exact Ideal.mul_mem_right n P hr
    have htsP : (t : R) * s ∈ P := ht ▸ Ideal.mul_mem_left P (t : R) hr'P
    have := hmkunit _ (mul_mem t.2 hsS)
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr htsP] at this
    exact this.ne_zero rfl
  have hψsurj : Function.Surjective (LinearMap.toSpanSingleton (R ⧸ P)
      ((R ⧸ P) ⊗[R] Localization (Submonoid.powers (f i))) (1 ⊗ₜ[R] 1)) := by
    intro z
    obtain ⟨y, rfl⟩ := exists_one_tmul P z
    obtain ⟨⟨r, s⟩, hrs⟩ := IsLocalizedModule.surj (Submonoid.powers (f i))
      (Algebra.linearMap R (Localization (Submonoid.powers (f i)))) y
    rw [Submonoid.smul_def, Algebra.linearMap_apply] at hrs
    obtain ⟨c, hc⟩ := (hmkunit (s : R) s.2).exists_left_inv
    refine ⟨c * Ideal.Quotient.mk P r, ?_⟩
    rw [LinearMap.toSpanSingleton_apply, mul_smul, ← one_tmul_smul,
      ← Algebra.algebraMap_eq_smul_one, ← hrs, one_tmul_smul, smul_smul, hc, one_smul]
  have hψinj : Function.Injective (LinearMap.toSpanSingleton (R ⧸ P)
      ((R ⧸ P) ⊗[R] Localization (Submonoid.powers (f i))) (1 ⊗ₜ[R] 1)) := by
    refine (injective_iff_map_eq_zero _).mpr fun c hc0 => ?_
    by_contra hne
    rw [LinearMap.toSpanSingleton_apply] at hc0
    exact hv (smul_cancel_of_isUnit (isUnit_iff_ne_zero.mpr hne) hc0)
  -- assemble the two equivalences and compute the rank
  have E := LinearEquiv.ofBijective
    (LinearMap.baseChange (R ⧸ P) (gluedProj f u i)) ⟨hinj, hsurj⟩
  have E' := LinearEquiv.ofBijective
    (LinearMap.toSpanSingleton (R ⧸ P)
      ((R ⧸ P) ⊗[R] Localization (Submonoid.powers (f i))) (1 ⊗ₜ[R] 1)) ⟨hψinj, hψsurj⟩
  rw [E.finrank_eq, ← E'.finrank_eq, Module.finrank_self]

/-- **The glued module of a normalized unit cocycle over a semilocal ring is free of rank
one.**  Finiteness and flatness are checked at the finitely many maximal ideals through the
quasi-coherence isomorphisms `(gluedSubmodule)ₚ ≅ Rₚ`, and Stacks 02M9
(`Module.nonempty_basis_of_flat_of_finrank_eq`) produces the rank-one basis. -/
theorem nonempty_basis_gluedSubmodule [Fintype ι] [Finite (MaximalSpectrum R)]
    (hf : Ideal.span (Set.range f) = ⊤)
    (hone : ∀ i, u i i = 1)
    (hcoc : ∀ i j k,
      resLoc (Submonoid.powers (f i) ⊔ Submonoid.powers (f j))
          (Submonoid.powers (f i) ⊔ Submonoid.powers (f j) ⊔ Submonoid.powers (f k))
          le_sup_left (u i j).val
        * resLoc (Submonoid.powers (f j) ⊔ Submonoid.powers (f k))
            (Submonoid.powers (f i) ⊔ Submonoid.powers (f j) ⊔ Submonoid.powers (f k))
            (sup_le (le_sup_of_le_left le_sup_right) le_sup_right) (u j k).val
      = resLoc (Submonoid.powers (f i) ⊔ Submonoid.powers (f k))
          (Submonoid.powers (f i) ⊔ Submonoid.powers (f j) ⊔ Submonoid.powers (f k))
          (sup_le (le_sup_of_le_left le_sup_left) le_sup_right) (u i k).val) :
    Nonempty (Module.Basis (Fin 1) R (gluedSubmodule f u)) := by
  classical
  -- the per-maximal quasi-coherence isomorphism `(gluedSubmodule)ₚ ≅ Rₚ`
  have key : ∀ (P : Ideal R) [P.IsMaximal],
      Nonempty ((LocalizedModule P.primeCompl (gluedSubmodule f u)) ≃ₗ[R]
        Localization P.primeCompl) := by
    intro P hP
    obtain ⟨i, hi⟩ := exists_notMem_of_span_eq_top f hf hP.ne_top
    have hle : Submonoid.powers (f i) ≤ P.primeCompl := powers_le_primeCompl hi
    haveI := isLocalizedModule_gluedProj f u hone hcoc i
    exact ⟨(IsLocalizedModule.iso P.primeCompl
        (liftOfLE (Submonoid.powers (f i)) P.primeCompl hle (gluedProj f u i)
          (LocalizedModule.mkLinearMap P.primeCompl (gluedSubmodule f u)))).symm ≪≫ₗ
      IsLocalizedModule.iso P.primeCompl
        (liftOfLE (Submonoid.powers (f i)) P.primeCompl hle
          (Algebra.linearMap R (Localization (Submonoid.powers (f i))))
          (Algebra.linearMap R (Localization P.primeCompl)))⟩
  haveI hfin : Module.Finite R (gluedSubmodule f u) := by
    refine Module.Finite.of_localized_maximal _ fun P hP => ?_
    obtain ⟨e⟩ := key P
    exact Module.Finite.equiv
      (LinearEquiv.extendScalarsOfIsLocalization P.primeCompl
        (Localization P.primeCompl) e).symm
  haveI hflat : Module.Flat R (gluedSubmodule f u) := by
    refine Module.flat_of_localized_maximal _ fun P hP => ?_
    obtain ⟨e⟩ := key P
    exact Module.Flat.of_linearEquiv e
  refine Module.nonempty_basis_of_flat_of_finrank_eq _ _ 1 fun P => ?_
  obtain ⟨i, hi⟩ := exists_notMem_of_span_eq_top f hf P.2.ne_top
  exact finrank_quotient_tensor_gluedSubmodule f u hone hcoc P.1 i hi

/-- **Semilocal splitting of a unit-valued Čech `1`-cocycle on a finite basic cover.**

Over a semilocal ring `R` (`Finite (MaximalSpectrum R)`), a normalized unit cocycle `u` on a
finite basic cover `{D(fᵢ)}` splits: there are units `v i` of `R[1/fᵢ]` whose coboundary is `u`,
in the form `v i = u i j * v j` on every pairwise overlap.  (Equivalently `u i j = vᵢ/vⱼ` —
this is `Pic R = 0` for semilocal `R`, in effective Čech form.)  A consumer normalizing
Weierstrass-chart transitions rescales the `i`-th chart by `v i` and the transition `u`-components
become `1`. -/
theorem exists_units_eq_mul_of_span_eq_top [Fintype ι] [Finite (MaximalSpectrum R)]
    (hf : Ideal.span (Set.range f) = ⊤)
    (hone : ∀ i, u i i = 1)
    (hcoc : ∀ i j k,
      resLoc (Submonoid.powers (f i) ⊔ Submonoid.powers (f j))
          (Submonoid.powers (f i) ⊔ Submonoid.powers (f j) ⊔ Submonoid.powers (f k))
          le_sup_left (u i j).val
        * resLoc (Submonoid.powers (f j) ⊔ Submonoid.powers (f k))
            (Submonoid.powers (f i) ⊔ Submonoid.powers (f j) ⊔ Submonoid.powers (f k))
            (sup_le (le_sup_of_le_left le_sup_right) le_sup_right) (u j k).val
      = resLoc (Submonoid.powers (f i) ⊔ Submonoid.powers (f k))
          (Submonoid.powers (f i) ⊔ Submonoid.powers (f j) ⊔ Submonoid.powers (f k))
          (sup_le (le_sup_of_le_left le_sup_left) le_sup_right) (u i k).val) :
    ∃ v : ∀ i, (Localization (Submonoid.powers (f i)))ˣ,
      ∀ i j,
        resLoc (Submonoid.powers (f i)) (Submonoid.powers (f i) ⊔ Submonoid.powers (f j))
          le_sup_left (v i).val
        = (u i j).val
            * resLoc (Submonoid.powers (f j))
                (Submonoid.powers (f i) ⊔ Submonoid.powers (f j)) le_sup_right (v j).val := by
  classical
  obtain ⟨b⟩ := nonempty_basis_gluedSubmodule f u hf hone hcoc
  set σ : gluedSubmodule f u := b 0 with hσ
  -- each component of the basis vector is a unit: it is a rank-one basis of the localization
  have hunit : ∀ i, IsUnit (σ.1 i) := by
    intro i
    haveI := isLocalizedModule_gluedProj f u hone hcoc i
    set b' : Module.Basis (Fin 1) (Localization (Submonoid.powers (f i)))
        (Localization (Submonoid.powers (f i))) :=
      b.ofIsLocalizedModule (Localization (Submonoid.powers (f i)))
        (Submonoid.powers (f i)) (gluedProj f u i) with hb'
    have hb'0 : b' 0 = σ.1 i := by
      rw [hb', Module.Basis.ofIsLocalizedModule_apply, gluedProj_apply, hσ]
    have hrepr : b'.repr 1 0 • b' 0 = 1 := by
      simpa [Fin.sum_univ_one] using b'.sum_repr 1
    rw [hb'0, smul_eq_mul] at hrepr
    exact IsUnit.of_mul_eq_one _ ((mul_comm _ _).trans hrepr)
  refine ⟨fun i => (hunit i).unit, fun i j => ?_⟩
  have hmem := σ.2 i j
  simpa only [IsUnit.unit_spec] using hmem

end Glued

end SemilocalUnitSplit
