/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanModularForms contributors
-/
import LeanModularForms.HeckeRIngs.GL2.ModularSymbols.CoefficientSystem
import LeanModularForms.HeckeRIngs.GL2.ModularSymbols.ModuleM
import LeanModularForms.HeckeRIngs.GL2.ModularSymbols.SL2Generation
import LeanModularForms.HeckeRIngs.GL2.ModularSymbols.CoinvariantsFinite
import LeanModularForms.HeckeRIngs.GL2.ModularSymbols.FinitelyManyCusps

/-!
# Finiteness of the integral modular-symbol module `𝕄 N k`

This file proves the central ES-1 finiteness statement: the integral modular-symbol module
`HeckeRing.GL2.ModularSymbols.𝕄 N k` is a finite `ℤ`-module.

The argument is a Manin-style finite-generation reduction.  The module is the `Γ₁(N)`-coinvariants
of the tensor representation `Div0 ℤ ⊗[ℤ] SymPow ℤ (k - 2)`.  By
`Representation.Coinvariants.finite_of_span_orbit_top` (in `CoinvariantsFinite.lean`) it suffices to
exhibit a *finite* set whose `Γ₁(N)`-orbit spans the whole tensor module over `ℤ`.

The proof has two layers:

* **Layer (i)** (`Div0` is orbit-spanned): a finite set `S_Div : Finset (Div0 ℤ)` whose
  `Γ₁(N)`-orbit
  spans `Div0 ℤ`.  This is the crux — it uses the finitely-many-cusps fact
  (`instFiniteCuspsGamma1`) to pick orbit representatives, the augmentation-kernel-as-differences
  description of `Div0`, finite generation of `Γ₁(N)` (`SL2Generation.lean`), and a telescoping
  `Subgroup.closure_induction` to move each within-orbit difference into the target span.

* **Layer (ii)** (untwist to the tensor): `SymPow ℤ m` is `ℤ`-finite with a monomial spanning set,
  and tensoring with it and untwisting the diagonal action reduces the spanning of
  `Div0 ⊗ SymPow` to layer (i).

## Main result

* `HeckeRing.GL2.ModularSymbols.instModuleFiniteModularSymbols` :
  `Module.Finite ℤ (𝕄 N k)`.
-/

namespace HeckeRing.GL2.ModularSymbols

open scoped MatrixGroups TensorProduct
open MvPolynomial

universe u

/-- Notation for the projective line `ℙ¹(ℚ)`, the cusps. -/
local notation "ℙ¹ℚ" => Projectivization ℚ (Fin 2 → ℚ)

/-! ## The bridge between `div0Rep` and the cusp action -/

/-- The `SL(2, ℤ)`-action on `ℙ¹(ℚ)` used in `FinitelyManyCusps.lean` agrees with the action by
the rational matrix `SpecialLinearGroup.map (Int.castRingHom ℚ) g` that underlies `div0Rep`. -/
theorem smul_projQQ_eq (g : SL(2, ℤ)) (x : ℙ¹ℚ) :
    g • x = (Matrix.SpecialLinearGroup.map (Int.castRingHom ℚ) g) • x :=
  rfl

/-- A formal difference `(x) - (y)` of two cusps has augmentation `0`, hence lies in `Div0 ℤ`. -/
theorem single_sub_single_mem_div0 (x y : ℙ¹ℚ) :
    (MonoidAlgebra.single x (1 : ℤ) - MonoidAlgebra.single y 1) ∈ Div0 ℤ := by
  rw [LinearMap.mem_ker]
  simp [MonoidAlgebra.coeff_single]

/-- The `Div0 ℤ` element `(x) - (y)`. -/
noncomputable def divDiff (x y : ℙ¹ℚ) : Div0 ℤ :=
  ⟨MonoidAlgebra.single x 1 - MonoidAlgebra.single y 1, single_sub_single_mem_div0 x y⟩

@[simp]
theorem divDiff_val (x y : ℙ¹ℚ) :
    ((divDiff x y : MonoidAlgebra ℤ ℙ¹ℚ)).coeff = Finsupp.single x 1 - Finsupp.single y 1 := by
  simp [divDiff, MonoidAlgebra.coeff_single]

@[simp]
theorem divDiff_self (x : ℙ¹ℚ) : divDiff x x = 0 := by
  apply Subtype.ext; simp [divDiff]

/-- Telescoping: `(x) - (z) = ((x) - (y)) + ((y) - (z))`. -/
theorem divDiff_add_divDiff (x y z : ℙ¹ℚ) :
    divDiff x y + divDiff y z = divDiff x z := by
  apply Subtype.ext
  simp only [AddMemClass.coe_add, divDiff]
  abel

/-- Antisymmetry: `(x) - (y) = -((y) - (x))`. -/
theorem divDiff_swap (x y : ℙ¹ℚ) : divDiff x y = -divDiff y x := by
  apply Subtype.ext
  simp only [NegMemClass.coe_neg, divDiff]
  abel

/-- **The `div0Rep`/cusp-action bridge.**  The representation `div0Rep ℤ g` sends the difference
`(x) - (y)` to `(g • x) - (g • y)`, where `g • ·` is the cusp action of `FinitelyManyCusps.lean`. -/
@[simp]
theorem div0Rep_divDiff (g : SL(2, ℤ)) (x y : ℙ¹ℚ) :
    div0Rep ℤ g (divDiff x y) = divDiff (g • x) (g • y) := by
  apply Subtype.ext
  apply MonoidAlgebra.coeff_injective
  rw [div0Rep_apply, divDiff_val, divDiff_val, ← Finsupp.mapDomain.addMonoidHom_apply, map_sub,
    Finsupp.mapDomain.addMonoidHom_apply, Finsupp.mapDomain.addMonoidHom_apply,
    Finsupp.mapDomain_single, Finsupp.mapDomain_single]
  rfl

/-- The `div0Rep`/cusp-action bridge, phrased for `g : Γ₁(N)` and its subgroup action on cusps. -/
theorem div0Rep_divDiff_gamma1 {N : ℕ} [NeZero N] (g : CongruenceSubgroup.Gamma1 N) (x y : ℙ¹ℚ) :
    div0Rep ℤ g.1 (divDiff x y) = divDiff (g • x) (g • y) := by
  rw [div0Rep_divDiff]
  rfl

/-! ## Layer (i): `Div0 ℤ` is spanned by differences -/

/-- **Augmentation kernel as differences.**  Fixing a basepoint `x₀ : ℙ¹ℚ`, the whole degree-0
divisor module `Div0 ℤ` is spanned over `ℤ` by the differences `(x) - (x₀)`. -/
theorem span_divDiff_basepoint (x₀ : ℙ¹ℚ) :
    Submodule.span ℤ (Set.range fun x : ℙ¹ℚ => divDiff x x₀) = ⊤ := by
  refine top_unique fun D _ => ?_
  -- The underlying finsupp of `D`, obtained via the `MonoidAlgebra` coefficient field.
  set Dc : ℙ¹ℚ →₀ ℤ := (D : MonoidAlgebra ℤ ℙ¹ℚ).coeff with hDc
  -- `D` equals `∑_{x ∈ supp} (D x) • ((x) - (x₀))`, the value of `linearCombination` at `D.val`.
  have key : D = Finsupp.linearCombination ℤ (fun x : ℙ¹ℚ => divDiff x x₀) Dc := by
    apply Subtype.ext
    apply MonoidAlgebra.coeff_injective
    -- Push the `Div0`-coercion through `linearCombination`, landing on the underlying finsupp.
    rw [show ((Finsupp.linearCombination ℤ (fun x : ℙ¹ℚ => divDiff x x₀) Dc :
          Div0 ℤ) : MonoidAlgebra ℤ ℙ¹ℚ).coeff
        = ((MonoidAlgebra.coeffLinearEquiv ℤ).toLinearMap ∘ₗ (Div0 ℤ).subtype)
            (Finsupp.linearCombination ℤ (fun x : ℙ¹ℚ => divDiff x x₀) Dc) from rfl,
      Finsupp.apply_linearCombination]
    simp only [Function.comp_def, LinearMap.comp_apply, Submodule.coe_subtype,
      LinearEquiv.coe_coe, MonoidAlgebra.coeffLinearEquiv_apply, divDiff_val]
    simp only [Finsupp.linearCombination_apply, smul_sub]
    rw [Finsupp.sum_sub]
    -- The first sum reconstructs `D.val = ∑ c_x • single x 1`.
    conv_lhs => rw [← hDc, ← Finsupp.sum_single Dc]
    simp only [Finsupp.smul_single, smul_eq_mul, mul_one]
    -- The second sum `∑_x single x₀ (D x) = single x₀ (∑ D x) = single x₀ 0 = 0`.
    have haug : (Dc.sum fun _ c => c) = 0 := by
      have := D.2
      rw [LinearMap.mem_ker, LinearMap.comp_apply, LinearEquiv.coe_coe,
        MonoidAlgebra.coeffLinearEquiv_apply, Finsupp.linearCombination_apply] at this
      simpa [hDc] using this
    have hsum : (Dc.sum fun _ c => Finsupp.single x₀ c) = 0 := by
      rw [← Finsupp.single_sum, haug, Finsupp.single_zero]
    rw [hsum, sub_zero]
  rw [key, Finsupp.linearCombination_apply]
  refine Submodule.sum_mem _ fun x _ => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
  exact ⟨x, rfl⟩

/-- A finite transversal of the `Γ₁(N)`-orbits on `ℙ¹(ℚ)`: a `Finset` of cusps meeting every orbit.
This uses the finitely-many-cusps fact `instFiniteCuspsGamma1`. -/
noncomputable def orbitReps (N : ℕ) [NeZero N] : Finset ℙ¹ℚ := by
  classical
  haveI := Fintype.ofFinite
    (MulAction.orbitRel.Quotient (CongruenceSubgroup.Gamma1 N) ℙ¹ℚ)
  exact (Finset.univ :
      Finset (MulAction.orbitRel.Quotient (CongruenceSubgroup.Gamma1 N) ℙ¹ℚ)).image Quotient.out

/-- Every cusp lies in the `Γ₁(N)`-orbit of a representative in `orbitReps N`. -/
theorem exists_mem_orbitReps (N : ℕ) [NeZero N] (x : ℙ¹ℚ) :
    ∃ c ∈ orbitReps N, ∃ g : CongruenceSubgroup.Gamma1 N, g • c = x := by
  classical
  set q : MulAction.orbitRel.Quotient (CongruenceSubgroup.Gamma1 N) ℙ¹ℚ :=
    Quotient.mk'' x with hq
  refine ⟨q.out, ?_, ?_⟩
  · simp only [orbitReps, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨q, rfl⟩
  · have hmem : x ∈ q.orbit := by
      rw [MulAction.orbitRel.Quotient.mem_orbit, hq]
    rw [MulAction.orbitRel.Quotient.orbit_eq_orbit_out _ Quotient.out_eq',
      MulAction.mem_orbit_iff] at hmem
    exact hmem

/-! ### The telescoping induction -/

variable {N : ℕ} [NeZero N]

/-- **Telescoping induction (the crux of Layer (i)).**  Let `T` be a `Γ₁(N)`-stable submodule of
`Div0 ℤ` (stability via `div0Rep`), `gens` a set of group elements, and suppose `T` contains every
"one-step" difference `(s • c) - (c)` for `s ∈ gens` and `c` a representative.  Then `T` contains
every within-orbit difference `(g • c) - (c)` for `g` in the subgroup generated by `gens`.  The
proof is the standard cocycle telescoping, carried out by `Subgroup.closure_induction`. -/
theorem divDiff_mem_of_closure (T : Submodule ℤ (Div0 ℤ))
    (hstable : ∀ (h : CongruenceSubgroup.Gamma1 N), ∀ v ∈ T, div0Rep ℤ h.1 v ∈ T)
    (gens : Set (CongruenceSubgroup.Gamma1 N)) (c : ℙ¹ℚ) (hc : c ∈ orbitReps N)
    (hgen : ∀ s ∈ gens, ∀ c ∈ orbitReps N, divDiff (s • c) c ∈ T)
    {g : CongruenceSubgroup.Gamma1 N} (hg : g ∈ Subgroup.closure gens) :
    divDiff (g • c) c ∈ T := by
  induction hg using Subgroup.closure_induction with
  | mem s hs => exact hgen s hs c hc
  | one => rw [one_smul, divDiff_self]; exact T.zero_mem
  | mul g₁ g₂ _ _ ih₁ ih₂ =>
      -- `(g₁g₂ • c) - c = div0Rep g₁ ((g₂•c) - c) + ((g₁•c) - c)`.
      have hstep : divDiff ((g₁ * g₂) • c) c
          = div0Rep ℤ g₁.1 (divDiff (g₂ • c) c) + divDiff (g₁ • c) c := by
        rw [div0Rep_divDiff_gamma1, mul_smul, divDiff_add_divDiff]
      rw [hstep]
      exact T.add_mem (hstable g₁ _ ih₂) ih₁
  | inv g₁ _ ih₁ =>
      -- `(g₁⁻¹ • c) - c = - div0Rep g₁⁻¹ ((g₁•c) - c)`.
      have hstep : divDiff (g₁⁻¹ • c) c
          = -div0Rep ℤ g₁⁻¹.1 (divDiff (g₁ • c) c) := by
        rw [div0Rep_divDiff_gamma1, ← mul_smul, inv_mul_cancel, one_smul, divDiff_swap]
      rw [hstep]
      exact T.neg_mem (hstable g₁⁻¹ _ ih₁)

/-! ### Assembling Layer (i) -/

open Classical in
/-- A finite generating `Finset` for the `Γ₁(N)`-orbit-span of `Div0 ℤ`.  It combines the
representative-to-basepoint differences with the one-step generator differences. -/
noncomputable def divGenSet (gens : Finset (CongruenceSubgroup.Gamma1 N)) (c₀ : ℙ¹ℚ) :
    Finset (Div0 ℤ) :=
  ((orbitReps N).image fun c => divDiff c c₀) ∪
    ((gens ×ˢ orbitReps N).image fun p => divDiff (p.1 • p.2) p.2)

/-- **Layer (i): `Div0 ℤ` is orbit-spanned over `ℤ[Γ₁(N)]`.**  There is a finite set `S_Div` of
degree-0 divisors whose `Γ₁(N)`-orbit spans the whole of `Div0 ℤ` over `ℤ`. -/
theorem exists_div0_orbit_span :
    ∃ S_Div : Finset (Div0 ℤ),
      Submodule.span ℤ {v : Div0 ℤ |
        ∃ g : CongruenceSubgroup.Gamma1 N, ∃ d ∈ S_Div, div0Rep ℤ g.1 d = v} = ⊤ := by
  classical
  -- A finite generating set for `Γ₁(N)`.
  obtain ⟨gens, hgens⟩ :=
    (Group.fg_def.mp inferInstance : (⊤ : Subgroup (CongruenceSubgroup.Gamma1 N)).FG)
  -- A basepoint representative.
  obtain ⟨x₀⟩ := (inferInstance : Nonempty ℙ¹ℚ)
  obtain ⟨c₀, hc₀reps, -⟩ := exists_mem_orbitReps N x₀
  refine ⟨divGenSet gens c₀, ?_⟩
  set T : Submodule ℤ (Div0 ℤ) := Submodule.span ℤ {v : Div0 ℤ |
      ∃ g : CongruenceSubgroup.Gamma1 N, ∃ d ∈ divGenSet gens c₀, div0Rep ℤ g.1 d = v} with hT
  -- `T` is `Γ₁(N)`-stable: applying `div0Rep h` to a spanning element gives another one.
  have hstable : ∀ (h : CongruenceSubgroup.Gamma1 N), ∀ v ∈ T, div0Rep ℤ h.1 v ∈ T := by
    intro h v hv
    rw [hT] at hv ⊢
    induction hv using Submodule.span_induction with
    | mem w hw =>
        obtain ⟨g, d, hd, rfl⟩ := hw
        refine Submodule.subset_span ⟨h * g, d, hd, ?_⟩
        rw [Subgroup.coe_mul, map_mul, Module.End.mul_apply]
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add a b _ _ ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb
    | smul r a _ ha => rw [map_smul]; exact Submodule.smul_mem _ _ ha
  -- Each spanning element of `divGenSet` belongs to `T` (take `g = 1`).
  have hsubset : ∀ d ∈ divGenSet gens c₀, d ∈ T := by
    intro d hd
    refine Submodule.subset_span ⟨1, d, hd, ?_⟩
    simp only [OneMemClass.coe_one, map_one, Module.End.one_apply]
  -- One-step generators `(s • c) - (c)` lie in `T` (for representatives `c`).
  have hgen : ∀ s ∈ (gens : Set (CongruenceSubgroup.Gamma1 N)), ∀ c ∈ orbitReps N,
      divDiff (s • c) c ∈ T := by
    intro s hs c hc
    refine hsubset _ ?_
    rw [divGenSet, Finset.mem_union]
    exact Or.inr (Finset.mem_image.2 ⟨(s, c), Finset.mem_product.2 ⟨hs, hc⟩, rfl⟩)
  -- Each `(x) - (c₀)` is in `T`, hence the basepoint span (which is `⊤`) is contained in `T`.
  have hkey : ∀ x : ℙ¹ℚ, divDiff x c₀ ∈ T := by
    intro x
    obtain ⟨c, hcreps, g, rfl⟩ := exists_mem_orbitReps N x
    rw [← divDiff_add_divDiff (g • c) c c₀]
    refine Submodule.add_mem _ ?_ ?_
    · exact divDiff_mem_of_closure T hstable (↑gens) c hcreps hgen
        (hgens ▸ Subgroup.mem_top g)
    · refine hsubset _ ?_
      rw [divGenSet, Finset.mem_union]
      exact Or.inl (Finset.mem_image.2 ⟨c, hcreps, rfl⟩)
  -- Conclude: the basepoint differences span `⊤`, and they all lie in `T`.
  refine top_unique ?_
  rw [← span_divDiff_basepoint c₀, Submodule.span_le]
  rintro _ ⟨x, rfl⟩
  exact hkey x

/-! ## Layer (ii): finiteness of `SymPow` and the untwist -/

/-- `SymPow R m` (degree-`m` homogeneous polynomials in two variables) is finitely generated:
it is the span of the finitely many degree-`m` monomials. -/
theorem symPow_fg (R : Type u) [CommRing R] (m : ℕ) : (SymPow R m).FG :=
  MvPolynomial.homogeneousSubmodule_fg (Fin 2) R m

instance instModuleFiniteSymPow (R : Type u) [CommRing R] (m : ℕ) :
    Module.Finite R (SymPow R m) :=
  Module.Finite.iff_fg.mpr (symPow_fg R m)

/-- `symRep` cancels its own inverse: `symRep g (symRep g⁻¹ x) = x`. -/
theorem symRep_apply_symRep_inv (m : ℕ) (g : SL(2, ℤ)) (x : SymPow ℤ m) :
    symRep ℤ m g (symRep ℤ m g⁻¹ x) = x := by
  rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one]
  rfl

/-- **The untwist identity.**  A twisted tensor `(div0Rep g d) ⊗ₜ x` is the image under the
restricted representation `modSymRep` of the untwisted tensor `d ⊗ₜ (symRep g⁻¹ x)`.  This is what
lets us pull the (infinite) `Div0`-orbit back to the action on the finite tensor module. -/
theorem untwist (m : ℕ) (g : CongruenceSubgroup.Gamma1 N) (d : Div0 ℤ) (x : SymPow ℤ m) :
    (div0Rep ℤ g.1 d) ⊗ₜ[ℤ] x = modSymRep N m g (d ⊗ₜ[ℤ] symRep ℤ m g.1⁻¹ x) := by
  have h1 : modSymRep N m g (d ⊗ₜ[ℤ] symRep ℤ m g.1⁻¹ x)
      = (div0Rep ℤ g.1 d) ⊗ₜ[ℤ] (symRep ℤ m g.1 (symRep ℤ m g.1⁻¹ x)) := rfl
  rw [h1, symRep_apply_symRep_inv]

/-! ## The finiteness theorem -/

/-- **ES-1.**  The integral modular-symbol module `𝕄 N k` is a finite `ℤ`-module.

The proof combines Layer (i) (`exists_div0_orbit_span`: `Div0 ℤ` is orbit-spanned over `ℤ[Γ₁(N)]`)
with Layer (ii) (`Module.Finite ℤ (SymPow ℤ m)` plus the `untwist` identity) to produce a finite set
whose `Γ₁(N)`-orbit spans the tensor module `Div0 ℤ ⊗[ℤ] SymPow ℤ (k - 2)`, then applies
`Representation.Coinvariants.finite_of_span_orbit_top`. -/
instance instModuleFiniteModularSymbols (N : ℕ) [NeZero N] (k : ℤ) :
    Module.Finite ℤ (𝕄 N k) := by
  classical
  set m := (k - 2).toNat with hm
  -- Layer (i): the finite orbit-spanning set for `Div0`.
  obtain ⟨S_Div, hSdiv⟩ := exists_div0_orbit_span (N := N)
  -- Layer (ii): a finite top-spanning set `B` for `SymPow`.
  obtain ⟨B, hB⟩ := (Module.finite_def.mp (instModuleFiniteSymPow ℤ m) :
    (⊤ : Submodule ℤ (SymPow ℤ m)).FG)
  -- The candidate orbit-generating set for the tensor module.
  set S : Finset (Div0 ℤ ⊗[ℤ] SymPow ℤ m) :=
    (S_Div ×ˢ B).image (fun p => p.1 ⊗ₜ[ℤ] p.2) with hS_def
  -- It suffices to span the tensor module by the `Γ₁(N)`-orbit of `S`.
  refine Representation.Coinvariants.finite_of_span_orbit_top (modSymRep N m) S ?_
  set orbitSpan : Submodule ℤ (Div0 ℤ ⊗[ℤ] SymPow ℤ m) := Submodule.span ℤ
    {v | ∃ g : CongruenceSubgroup.Gamma1 N, ∃ s ∈ S, modSymRep N m g s = v} with horb
  -- A tensor `d ⊗ x` with `d` a Layer-(i) generator lies in `orbitSpan`.
  have hgen_tmul : ∀ (g : CongruenceSubgroup.Gamma1 N), ∀ dⱼ ∈ S_Div, ∀ x : SymPow ℤ m,
      (div0Rep ℤ g.1 dⱼ) ⊗ₜ[ℤ] x ∈ orbitSpan := by
    intro g dⱼ hdⱼ x
    -- Untwist: the twisted tensor is `modSymRep g` applied to `dⱼ ⊗ (symRep g⁻¹ x)`.
    rw [untwist]
    -- The linear map `y ↦ modSymRep g (dⱼ ⊗ y)`; its comap of `orbitSpan` contains `B`, so all `y`.
    let h : SymPow ℤ m →ₗ[ℤ] Div0 ℤ ⊗[ℤ] SymPow ℤ m :=
      (modSymRep N m g).comp (TensorProduct.mk ℤ (Div0 ℤ) (SymPow ℤ m) dⱼ)
    have hhy : h (symRep ℤ m g.1⁻¹ x) = modSymRep N m g (dⱼ ⊗ₜ[ℤ] symRep ℤ m g.1⁻¹ x) := rfl
    rw [← hhy]
    have hle : Submodule.span ℤ (↑B : Set (SymPow ℤ m)) ≤ Submodule.comap h orbitSpan := by
      rw [Submodule.span_le]
      intro b hb
      refine Submodule.mem_comap.mpr (Submodule.subset_span ⟨g, dⱼ ⊗ₜ[ℤ] b, ?_, rfl⟩)
      rw [hS_def, Finset.mem_image]
      exact ⟨(dⱼ, b), Finset.mem_product.2 ⟨hdⱼ, hb⟩, rfl⟩
    rw [hB] at hle
    exact Submodule.mem_comap.mp (hle Submodule.mem_top)
  -- For every `x`, the set of `d` with `d ⊗ x ∈ orbitSpan` is all of `Div0` (by Layer (i)).
  have hdx : ∀ (d : Div0 ℤ) (x : SymPow ℤ m), d ⊗ₜ[ℤ] x ∈ orbitSpan := by
    intro d x
    -- The preimage `{d | d ⊗ x ∈ orbitSpan}` is the comap of `orbitSpan` along `· ↦ · ⊗ x`.
    let f : Div0 ℤ →ₗ[ℤ] Div0 ℤ ⊗[ℤ] SymPow ℤ m :=
      (TensorProduct.mk ℤ (Div0 ℤ) (SymPow ℤ m)).flip x
    have hfd : f d = d ⊗ₜ[ℤ] x := rfl
    rw [← hfd]
    -- It contains the Layer-(i) spanning set, hence is all of `Div0`.
    have hle : Submodule.span ℤ {v : Div0 ℤ |
        ∃ g : CongruenceSubgroup.Gamma1 N, ∃ dⱼ ∈ S_Div, div0Rep ℤ g.1 dⱼ = v}
        ≤ Submodule.comap f orbitSpan := by
      rw [Submodule.span_le]
      rintro _ ⟨g, dⱼ, hdⱼ, rfl⟩
      exact hgen_tmul g dⱼ hdⱼ x
    rw [hSdiv] at hle
    exact Submodule.mem_comap.mp (hle Submodule.mem_top)
  -- Conclude by simple-tensor induction (instance-clean, avoids `span_tmul_eq_top`).
  refine top_unique fun t _ => ?_
  induction t with
  | zero => exact Submodule.zero_mem _
  | tmul d x => exact hdx d x
  | add a b ha hb => exact Submodule.add_mem _ (ha trivial) (hb trivial)

end HeckeRing.GL2.ModularSymbols
