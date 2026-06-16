/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».StructureSheaf
import «Adic spaces».Example638
import «Adic spaces».TateAlgebra
import «Adic spaces».Cor832
import «Adic spaces».MvTateAlgebraTopology

/-!
# Wedhorn Theorem 8.28(b): strongly noetherian Tate ⇒ sheafy — clean top-down skeleton

This file states the proof of Wedhorn's Theorem 8.28(b) **top-down**, following the textbook
exactly. Every lemma is stated as Wedhorn states it, with a `sorry` body, and the lemmas are
composed to prove `IsSheafy A`. Each `sorry` is then to be discharged by recursively reading
Wedhorn and stating its sub-lemmas the same way.

## Wedhorn's proof structure (Adic Spaces, §8.2, pp. 81–84)

```
Theorem 8.28(b)  IsSheafy A                     [A strongly noetherian Tate, complete]
  ├─ Prop A.4    acyclic on rational covers ⇒ sheaf
  └─ Lemma 8.34  rational cover gen by T (T·A = A) is O_X-acyclic
      ├─ Lemma 8.33  the 2-element Laurent cover {R(f/1), R(1/f)} is O_X-acyclic
      │   ├─ Cor 8.32   O_X(X) → ∏ O_X(Uᵢ) is faithfully flat (⇒ ε injective)
      │   │   └─ Lemma 8.31  A⟨X⟩ faithfully flat / A⟨X⟩/(f−X), A⟨X⟩/(1−fX) flat over A
      │   │       └─ Remark 8.29  M ⊗_A A⟨X⟩ ≅ M⟨X⟩      [via Prop 6.18, PROVEN: BanachOMT]
      │   └─ Example 6.38 / 6.39  O_X(U) = A⟨X⟩/(closed ideal)   [Example638.lean]
      └─ Prop A.3 (1)(2)(3)  Čech refinement / Laurent-cover induction
```

In Lean, `IsSheafy A` (`StructureSheaf.lean`) is the pair `(embedding, gluing)` on every
`RationalCovering`. Cor 8.32 supplies `embedding` (faithful flatness ⇒ the product
restriction is injective; the topological inducing is the Banach-OMT input, `BanachOMT.lean`).
Lemma 8.34 supplies `gluing`.

## References
* [T. Wedhorn, *Adic Spaces*][wedhorn2019adic], Theorem 8.28, Lemmas 8.31/8.33/8.34,
  Cor 8.32, Remark 8.29, Prop A.3/A.4.
-/

namespace ValuationSpectrum

universe u

variable {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [PlusSubring A] [IsHuberRing A] [HasLocLiftPowerBounded A]

section Wedhorn828

variable [IsTateRing A] [IsNoetherianRing A] [IsStronglyNoetherian A] [T2Space A]
  [NonarchimedeanRing A] [CompatiblePlusSubring A]
  [letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A; CompleteSpace A]

section Helpers831

omit [PlusSubring A] [HasLocLiftPowerBounded A] [IsStronglyNoetherian A] [NonarchimedeanRing A]
  [CompatiblePlusSubring A] in
/-- **Wedhorn Prop 6.18(1), Hausdorff half** (p. 50, `wedhorn.txt:4076`): a finitely
generated `A`-module `M`, with its module topology, over a complete noetherian Tate ring `A`,
is Hausdorff (`T2`).

INFRASTRUCTURE companion of `CompleteSpace.of_isModuleTopology_finite`: present `M` as an open
quotient `Aⁿ ⧠ M`; the kernel of `ν : Aⁿ ↠ M` is finitely generated (`Aⁿ` noetherian) hence
closed (`fg_topologicalClosure_isClosed`, BGR §3.7.2/1), so `Aⁿ ⧸ ker ν ≅ M` is `T2`, and the
canonical homeomorphism transports `T2` to `M`.

Faithful: `[CompleteSpace A]`, `[IsNoetherianRing A]`, `[IsTateRing A]` only — no ring of
definition `A₀`, and no `[IsLinearTopology A A]` (the latter is unsatisfiable for a Tate ring;
the `A°`-layer obligations it used to feed are now discharged via `[NonarchimedeanRing A]`). -/
private theorem t2Space_of_moduleTopology_finite (M : Type u) [AddCommGroup M] [Module A M]
    [TopologicalSpace M] [IsModuleTopology A M] [Module.Finite A M] :
    T2Space M := by
  letI uA : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A
  haveI : IsUniformAddGroup A := isUniformAddGroup_of_addCommGroup
  haveI : (uniformity A).IsCountablyGenerated := IsUniformAddGroup.uniformity_countably_generated
  haveI : IsTopologicalAddGroup M := IsModuleTopology.topologicalAddGroup A M
  haveI : ContinuousSMul A M := inferInstance
  -- Present `M` as an open quotient of `Aⁿ`.
  obtain ⟨n, ν, hν⟩ := Module.Finite.exists_fin' A M
  have hν_cont : Continuous ⇑ν := IsModuleTopology.continuous_linearMap_of_finite ν
  have hν_open : IsOpenMap ⇑ν := IsModuleTopology.isOpenMap_of_surjective_of_finite ν hν
  -- `ker ν` is finitely generated (`Aⁿ` noetherian), so its closure is finitely generated.
  haveI hnoeth : IsNoetherian A (Fin n → A) := inferInstance
  have hker_clos_fg : Module.Finite A ((LinearMap.ker ν).topologicalClosure) :=
    Module.Finite.of_fg (hnoeth.noetherian _)
  -- Hence `ker ν` is closed (BGR §3.7.2/1).
  have hker_closed : IsClosed ((LinearMap.ker ν) : Set (Fin n → A)) :=
    fg_topologicalClosure_isClosed (LinearMap.ker ν) hker_clos_fg
  haveI hkc : IsClosed ((ν.toAddMonoidHom.ker : AddSubgroup (Fin n → A)) :
      Set (Fin n → A)) := hker_closed
  haveI : T2Space ((Fin n → A) ⧸ ν.toAddMonoidHom.ker) := inferInstance
  -- The canonical add-equiv `Aⁿ ⧸ ker ν ≃+ M` is a homeomorphism.
  let e : ((Fin n → A) ⧸ ν.toAddMonoidHom.ker) ≃+ M :=
    QuotientAddGroup.quotientKerEquivOfSurjective ν.toAddMonoidHom hν
  have hq_surj : Function.Surjective ⇑(QuotientAddGroup.mk' ν.toAddMonoidHom.ker) :=
    QuotientAddGroup.mk'_surjective _
  have hq_cont : Continuous ⇑(QuotientAddGroup.mk' ν.toAddMonoidHom.ker) := continuous_quot_mk
  have he_mk : ⇑e ∘ ⇑(QuotientAddGroup.mk' ν.toAddMonoidHom.ker) = ⇑ν := by ext x; rfl
  have he_cont : Continuous ⇑e := by
    rw [continuous_def]
    intro U hU
    have hpre : ⇑(QuotientAddGroup.mk' ν.toAddMonoidHom.ker) ⁻¹' (⇑e ⁻¹' U) = ⇑ν ⁻¹' U := by
      rw [← Set.preimage_comp, he_mk]
    have hopen : IsOpen (⇑(QuotientAddGroup.mk' ν.toAddMonoidHom.ker) ⁻¹' (⇑e ⁻¹' U)) := by
      rw [hpre]; exact hU.preimage hν_cont
    exact (QuotientAddGroup.isOpenQuotientMap_mk
      (N := ν.toAddMonoidHom.ker)).isQuotientMap.isOpen_preimage.mp hopen
  have he_open : IsOpenMap ⇑e := by
    intro U hU
    have himg : ⇑e '' U = ⇑ν '' (⇑(QuotientAddGroup.mk' ν.toAddMonoidHom.ker) ⁻¹' U) := by
      rw [← he_mk, Set.image_comp, Set.image_preimage_eq U hq_surj]
    rw [himg]; exact hν_open _ (hU.preimage hq_cont)
  -- Transport `T2` along the homeomorphism `Aⁿ ⧸ ker ν ≃ₜ M`.
  exact (e.toEquiv.toHomeomorphOfContinuousOpen he_cont he_open).t2Space

omit [PlusSubring A] [HasLocLiftPowerBounded A] [IsStronglyNoetherian A]
  [CompatiblePlusSubring A] in
/-- Bundle the module-topology instances on a finitely generated `A`-module `M`. -/
private theorem muMap_bijective_of_finite (M : Type u) [AddCommGroup M] [Module A M]
    [Module.Finite A M] :
    letI : TopologicalSpace M := moduleTopology A M
    haveI : IsModuleTopology A M := ⟨rfl⟩
    haveI : IsTopologicalAddGroup M := IsModuleTopology.topologicalAddGroup A M
    haveI : ContinuousSMul A M := inferInstance
    Function.Bijective (muMap (A := A) (M := M)) := by
  letI : TopologicalSpace M := moduleTopology A M
  haveI : IsModuleTopology A M := ⟨rfl⟩
  haveI : IsTopologicalAddGroup M := IsModuleTopology.topologicalAddGroup A M
  haveI : ContinuousSMul A M := inferInstance
  haveI : ContinuousConstSMul A M := inferInstance
  haveI : T2Space M := t2Space_of_moduleTopology_finite (A := A) M
  exact ⟨muMap_injective, muMap_surjective⟩

omit [PlusSubring A] [HasLocLiftPowerBounded A] [IsStronglyNoetherian A]
  [CompatiblePlusSubring A] in
/-- **Remark 8.29 ⟹ flatness criterion input**: for an injective `A`-linear map `i : N → M`
between finitely generated `A`-modules, the base change `i ⊗ id : N ⊗ A⟨X⟩ → M ⊗ A⟨X⟩` is
injective.

Proof: equip `N, M` with their module topologies; `μ_N : N ⊗ A⟨X⟩ ≅ N⟨X⟩` and
`μ_M : M ⊗ A⟨X⟩ ≅ M⟨X⟩` are isomorphisms (`muMap_bijective_of_finite`); the naturality square
`μ_M ∘ (i ⊗ id) = i⟨X⟩ ∘ μ_N` commutes (`muMap_naturality`); and `i⟨X⟩ = restrictedModule.map i`
is injective (`restrictedModule_map_injective`, as `i` is injective and continuous). Hence
`i ⊗ id = μ_M⁻¹ ∘ i⟨X⟩ ∘ μ_N` is a composite of injective maps. -/
private theorem tensorTate_map_injective
    {N : Type u} [AddCommGroup N] [Module A N] [Module.Finite A N]
    {M : Type u} [AddCommGroup M] [Module A M] [Module.Finite A M]
    (i : N →ₗ[A] M) (hi : Function.Injective i) :
    Function.Injective (TensorProduct.map i (LinearMap.id (R := A) (M := ↥(TateAlgebra A)))) := by
  letI : TopologicalSpace N := moduleTopology A N
  haveI : IsModuleTopology A N := ⟨rfl⟩
  haveI : IsTopologicalAddGroup N := IsModuleTopology.topologicalAddGroup A N
  haveI : ContinuousSMul A N := inferInstance
  haveI : ContinuousConstSMul A N := inferInstance
  letI : TopologicalSpace M := moduleTopology A M
  haveI : IsModuleTopology A M := ⟨rfl⟩
  haveI : IsTopologicalAddGroup M := IsModuleTopology.topologicalAddGroup A M
  haveI : ContinuousSMul A M := inferInstance
  haveI : ContinuousConstSMul A M := inferInstance
  -- `i` is continuous (linear out of the module topology).
  have hi_cont : Continuous i := IsModuleTopology.continuous_linearMap_of_finite i
  -- `μ_N` is injective; `i⟨X⟩` is injective.
  have hμN_inj : Function.Injective (muMap (A := A) (M := N)) :=
    (muMap_bijective_of_finite N).1
  have hiX_inj : Function.Injective (restrictedModule.map (A := A) i hi_cont) :=
    restrictedModule_map_injective i hi_cont hi
  -- Naturality: `i⟨X⟩ ∘ μ_N = μ_M ∘ (i ⊗ id)`.
  have hnat := muMap_naturality (A := A) i hi_cont
  -- `μ_M ∘ (i ⊗ id)` is injective (since `i⟨X⟩ ∘ μ_N` is).
  have hcomp_inj : Function.Injective
      ((muMap (A := A) (M := M)).comp
        (TensorProduct.map i (LinearMap.id (R := A) (M := ↥(TateAlgebra A))))) := by
    rw [← hnat, LinearMap.coe_comp]
    exact hiX_inj.comp hμN_inj
  -- `μ_M ∘ (i ⊗ id)` injective ⟹ `i ⊗ id` injective.
  have : Function.Injective ⇑((muMap (A := A) (M := M)).comp
      (TensorProduct.map i (LinearMap.id (R := A) (M := ↥(TateAlgebra A))))) := hcomp_inj
  rw [LinearMap.coe_comp] at this
  exact this.of_comp

omit [PlusSubring A] [HasLocLiftPowerBounded A] [IsStronglyNoetherian A]
  [CompatiblePlusSubring A] in
/-- **Lemma 8.31(1), flatness half** (Wedhorn p. 82, `wedhorn.txt:4106`): `A⟨X⟩` is **flat**
over a complete noetherian Tate ring `A`.

Faithful route via Remark 8.29 (no ring of definition `A₀`): by the finitely-generated-ideal
flatness criterion `Module.Flat.iff_rTensor_injective`, it suffices that for every finitely
generated ideal `I ⊆ A` the base change `I ⊗ A⟨X⟩ → A ⊗ A⟨X⟩` is injective. `I` and `A` are
finitely generated `A`-modules (`A` noetherian), so this is `tensorTate_map_injective` applied
to the injective inclusion `Submodule.subtype I`. -/
private theorem tateAlgebra_flat_faithful : Module.Flat A ↥(TateAlgebra A) := by
  rw [Module.Flat.iff_rTensor_injective]
  intro I hI
  haveI : Module.Finite A ↥I := Module.Finite.of_fg hI
  rw [LinearMap.rTensor_def]
  exact tensorTate_map_injective (Submodule.subtype I) (Submodule.injective_subtype I)

omit [PlusSubring A] [HasLocLiftPowerBounded A] [IsStronglyNoetherian A]
  [CompatiblePlusSubring A] in
/-- **Faithful `mem_ideal_map_of_forall_coeff_mem`** (Lemma 8.31(2) input, no ring of
definition `A₀`): if every coefficient of `h ∈ A⟨X⟩` lies in the ideal `I`, then
`h ∈ I · A⟨X⟩`.

This is the reverse direction of `forall_coeff_mem_of_mem_ideal_map` and the only step of the
`f − X`/`1 − fX` saturation that needs more than the ascending-chain lemma. Wedhorn's case-(a)
proof routes through Artin–Rees over a ring of definition; the faithful (case-(b)) route uses
Remark 8.29 instead: writing `q : A ↠ A/I`, the kernel of `q⟨X⟩ : A⟨X⟩ → (A/I)⟨X⟩` is exactly
`{h : ∀ n, coeff n h ∈ I}`, and the `μ`-naturality square together with the bijectivity of
`μ_A`, `μ_{A/I}` (`muMap_bijective_of_finite`, both `A` and `A/I` finitely generated) and the
tensor-quotient kernel identity `(rTensor q).ker = (rTensor I.subtype).range` (`rTensor_mkQ`)
identifies that kernel with `I · A⟨X⟩`. -/
private theorem mem_idealMap_of_forall_coeff_mem (I : Ideal A) (h : ↥(TateAlgebra A))
    (hcoeffs : ∀ n, TateAlgebra.coeff n h ∈ I) :
    h ∈ Ideal.map (algebraMap A ↥(TateAlgebra A)) I := by
  classical
  -- `A ⧸ I` carries its quotient topology, which is the module topology (`A ⧸ I` is f.g.).
  set q : A →ₗ[A] (A ⧸ I) := (Submodule.mkQ I) with hq_def
  haveI : T2Space (A ⧸ I) := t2Space_of_moduleTopology_finite (A := A) (A ⧸ I)
  have hq_cont : Continuous q := IsModuleTopology.continuous_linearMap_of_finite q
  -- `μ_A`, `μ_{A/I}` are bijective.
  have hμA_bij : Function.Bijective (muMap (A := A) (M := A)) :=
    ⟨muMap_injective, muMap_surjective⟩
  have hμQ_bij : Function.Bijective (muMap (A := A) (M := A ⧸ I)) :=
    ⟨muMap_injective, muMap_surjective⟩
  -- View `h` as a restricted `A`-valued series `h'` (same coefficients).
  set h' : ↥(restrictedModule A A) := restrictedModuleA_equiv.symm h with hh'_def
  have hh'_val : ∀ s, (h' : ↥(restrictedModule A A)).val s = h.val s := fun _ => rfl
  -- `q⟨X⟩ h' = 0` (every coefficient `h.val s ∈ I`).
  have hqXh' : restrictedModule.map (A := A) q hq_cont h' = 0 := by
    apply Subtype.ext; funext s
    change q (h'.val s) = (0 : A ⧸ I)
    rw [hh'_val, hq_def]
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    rw [TateAlgebra.eq_toIndex s]; exact hcoeffs (s 0)
  -- `t := μ_A⁻¹ h'`.
  obtain ⟨t, ht⟩ := hμA_bij.surjective h'
  -- `(q ⊗ id) t ∈ ker μ_{A/I}` (naturality + `μ_A t = h'`), hence `(q ⊗ id) t = 0`.
  have hqt_zero : (TensorProduct.map q (LinearMap.id (R := A) (M := ↥(TateAlgebra A)))) t = 0 := by
    apply hμQ_bij.injective
    rw [map_zero]
    have hnat := muMap_naturality (A := A) q hq_cont
    have := LinearMap.congr_fun hnat t
    simp only [LinearMap.comp_apply] at this
    rw [← this, ht, hqXh']
  -- `t ∈ ker (rTensor A⟨X⟩ q) = range (rTensor A⟨X⟩ I.subtype)`.
  have ht_ker : t ∈ LinearMap.ker (LinearMap.rTensor ↥(TateAlgebra A) (Submodule.mkQ I)) := by
    rw [LinearMap.mem_ker, LinearMap.rTensor_def]; exact hqt_zero
  rw [rTensor_mkQ] at ht_ker
  obtain ⟨u, hu⟩ := ht_ker
  -- Transport: `h = restrictedModuleA_equiv (μ_A t)`, and `μ_A ((I.subtype ⊗ id) u) ∈ I·A⟨X⟩`.
  have hh_eq : h = restrictedModuleA_equiv (muMap (A := A) (M := A) t) := by
    rw [ht]; exact (restrictedModuleA_equiv.apply_symm_apply h).symm
  rw [hh_eq, ← hu, LinearMap.rTensor_def]
  -- The map `i₀ ⊗ p ↦ algebraMap ↑i₀ * p` lands in `Ideal.map I`.
  -- Reduce to pure tensors via the tensor-product universal property.
  refine TensorProduct.induction_on u (by simp) (fun i₀ p => ?_)
    (fun a b ha hb => by rw [map_add, map_add, map_add]; exact Ideal.add_mem _ ha hb)
  -- Generator case: `μ_A ((I.subtype ⊗ id) (i₀ ⊗ p)) = i₀ • (coeffs of p)`,
  -- which through `restrictedModuleA_equiv` is `algebraMap ↑i₀ * p`.
  simp only [TensorProduct.map_tmul, LinearMap.id_coe, id_eq, Submodule.subtype_apply]
  have hval : ∀ s, (restrictedModuleA_equiv (muMap (A := A) (M := A)
      ((i₀ : A) ⊗ₜ[A] p))).val s = (i₀ : A) * p.val s := by
    intro s
    change (muMap (A := A) (M := A) ((i₀ : A) ⊗ₜ[A] p)).val s = (i₀ : A) * p.val s
    simp only [muMap, TensorProduct.lift.tmul, LinearMap.mk₂_apply]
    rw [smul_eq_mul, mul_comm]
  have : restrictedModuleA_equiv (muMap (A := A) (M := A) ((i₀ : A) ⊗ₜ[A] p)) =
      algebraMap A ↥(TateAlgebra A) (i₀ : A) * p := by
    apply TateAlgebra.ext; intro n
    rw [TateAlgebra.coeff_algebraMap_mul]
    change (restrictedModuleA_equiv (muMap (A := A) (M := A) ((i₀ : A) ⊗ₜ[A] p))).val
      (TateAlgebra.toIndex n) = (i₀ : A) * TateAlgebra.coeff n p
    rw [hval]; rfl
  rw [this]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ i₀.2)

omit [PlusSubring A] [HasLocLiftPowerBounded A] [IsStronglyNoetherian A]
  [CompatiblePlusSubring A] in
/-- **Faithful saturation of `f − X`** (Lemma 8.31(2) input, no ring of definition `A₀`): the
extended ideal `I · A⟨X⟩` is `(f − X)`-saturated.

This mirrors `TateAlgebra.fSubX_saturated` (whose only non-faithful step is the final
`mem_ideal_map_of_forall_coeff_mem`): the coefficient equations from `(f − X) · h ∈ I · A⟨X⟩`
feed the ascending-chain lemma `noeth_mem_ideal_of_mul_shift` to force every coefficient of `h`
into `I`, and the faithful `mem_idealMap_of_forall_coeff_mem` concludes `h ∈ I · A⟨X⟩`. -/
private theorem fSubX_saturated_faithful (f : A) (I : Ideal A) (h : ↥(TateAlgebra A))
    (hmem : (algebraMap A ↥(TateAlgebra A) f - TateAlgebra.X) * h ∈
      Ideal.map (algebraMap A ↥(TateAlgebra A)) I) :
    h ∈ Ideal.map (algebraMap A ↥(TateAlgebra A)) I := by
  have hcoeffs_prod : ∀ n, TateAlgebra.coeff n ((algebraMap A _ f - TateAlgebra.X) * h) ∈ I :=
    TateAlgebra.forall_coeff_mem_of_mem_ideal_map I _ hmem
  have hcoeff_eq : ∀ n,
      f * TateAlgebra.coeff n h - TateAlgebra.coeff n (TateAlgebra.X * h) ∈ I := by
    intro n
    have h1 := hcoeffs_prod n
    rw [sub_mul, TateAlgebra.coeff_sub, TateAlgebra.coeff_algebraMap_mul] at h1
    exact h1
  have h0 : f * TateAlgebra.coeff 0 h ∈ I := by
    have := hcoeff_eq 0; rwa [TateAlgebra.coeff_zero_X_mul, sub_zero] at this
  have hstep : ∀ n, TateAlgebra.coeff n h - f * TateAlgebra.coeff (n + 1) h ∈ I := by
    intro n
    have h1 := hcoeff_eq (n + 1); rw [TateAlgebra.coeff_succ_X_mul] at h1
    have : -(f * TateAlgebra.coeff (n + 1) h - TateAlgebra.coeff n h) ∈ I := I.neg_mem h1
    rwa [neg_sub] at this
  have hcoeff0 : TateAlgebra.coeff 0 h ∈ I :=
    noeth_mem_ideal_of_mul_shift f I (fun n => TateAlgebra.coeff n h) h0 hstep
  have hall : ∀ n, TateAlgebra.coeff n h ∈ I := by
    intro n; induction n with
    | zero => exact hcoeff0
    | succ n ih =>
      have hf_succ : f * TateAlgebra.coeff (n + 1) h ∈ I := by
        have := I.sub_mem ih (hstep n); rwa [sub_sub_cancel] at this
      exact noeth_mem_ideal_of_mul_shift f I (fun k => TateAlgebra.coeff (n + 1 + k) h)
        (by simp only [Nat.add_zero]; exact hf_succ)
        (fun k => by
          change TateAlgebra.coeff (n + 1 + k) h - f * TateAlgebra.coeff (n + 1 + (k + 1)) h ∈ I
          rw [show n + 1 + (k + 1) = (n + 1 + k) + 1 from by omega]
          exact hstep (n + 1 + k))
  exact mem_idealMap_of_forall_coeff_mem I h hall

omit [PlusSubring A] [HasLocLiftPowerBounded A] [IsStronglyNoetherian A]
  [CompatiblePlusSubring A] in
/-- **Faithful saturation of `1 − f·X`** (Lemma 8.31(2) input, no ring of definition `A₀`):
the extended ideal `I · A⟨X⟩` is `(1 − f·X)`-saturated.

Mirrors `TateAlgebra.oneSubfX_saturated`, replacing its final non-faithful step with
`mem_idealMap_of_forall_coeff_mem`. -/
private theorem oneSubfX_saturated_faithful (f : A) (I : Ideal A) (h : ↥(TateAlgebra A))
    (hmem : (1 - algebraMap A ↥(TateAlgebra A) f * TateAlgebra.X) * h ∈
      Ideal.map (algebraMap A ↥(TateAlgebra A)) I) :
    h ∈ Ideal.map (algebraMap A ↥(TateAlgebra A)) I := by
  have hcoeffs_prod :
      ∀ n, TateAlgebra.coeff n ((1 - algebraMap A _ f * TateAlgebra.X) * h) ∈ I :=
    TateAlgebra.forall_coeff_mem_of_mem_ideal_map I _ hmem
  have hcoeff_eq : ∀ n,
      TateAlgebra.coeff n h - f * TateAlgebra.coeff n (TateAlgebra.X * h) ∈ I := by
    intro n
    have h1 := hcoeffs_prod n
    rw [sub_mul, one_mul, mul_assoc, TateAlgebra.coeff_sub,
      TateAlgebra.coeff_algebraMap_mul] at h1
    exact h1
  have h0 : TateAlgebra.coeff 0 h ∈ I := by
    have := hcoeff_eq 0; rwa [TateAlgebra.coeff_zero_X_mul, mul_zero, sub_zero] at this
  have hstep : ∀ n, TateAlgebra.coeff (n + 1) h - f * TateAlgebra.coeff n h ∈ I := by
    intro n; have := hcoeff_eq (n + 1); rwa [TateAlgebra.coeff_succ_X_mul] at this
  have hall : ∀ n, TateAlgebra.coeff n h ∈ I := by
    intro n; induction n with
    | zero => exact h0
    | succ n ih =>
      have hfn : f * TateAlgebra.coeff n h ∈ I := I.mul_mem_left f ih
      have hdiff : TateAlgebra.coeff (n + 1) h - f * TateAlgebra.coeff n h ∈ I := hstep n
      have hsplit : TateAlgebra.coeff (n + 1) h =
          f * TateAlgebra.coeff n h
            + (TateAlgebra.coeff (n + 1) h - f * TateAlgebra.coeff n h) := by ring
      rw [hsplit]; exact I.add_mem hfn hdiff
  exact mem_idealMap_of_forall_coeff_mem I h hall

end Helpers831

/-! ## Faithful Example-6.38 base (Step 1 of Prop 8.30) — `presheafValue D ≃+* A⟨X⟩/(1−sX)`

The repository's `presheafValueCanonicalQuotientEquiv` (TopologyComparison.lean) identifies
`presheafValue D` with the canonical-topology quotient `A⟨X⟩/(1−sX)`, but it threads
`hnoeth : IsNoetherianRing ↥(pairSubring (IsTateRing.principalPair A))` — i.e. noetherianness of
the **ring of definition** `A₀⟨X⟩` of the Tate algebra. That is the Wedhorn case-(a) /
`ℂ_p`-FALSE hypothesis (a strongly-noetherian Tate ring such as `ℂ_p` has a non-noetherian ring of
definition), so it must not be used to discharge the case-(b) `prop_8_30` helpers.

The faithful route uses only `[IsStronglyNoetherian A]`: then `TateAlgebra A = A⟨X⟩` is itself a
**noetherian** complete Tate ring (`IsStronglyNoetherian.isNoetherianRing_restricted 1`,
`TateAlgebraTopology.lean:961`), so by **Wedhorn Prop 6.17** (`wedhorn_6_17_ideal`,
`WedhornBanachTheorem.lean:821`, sorry-free, keystone-unblocked this session via
`fg_topologicalClosure_isClosed` / BGR §3.7.2/1) EVERY ideal of `A⟨X⟩` is closed — in particular
the principal ideal `oneSubfXIdeal D.s = (1 − sX)`. Closedness of the ideal is the only input the
existing quotient-completeness / quotient-Hausdorffness lemmas need; supplying it faithfully lets us
rebuild the forward completion map and the equivalence with the `[IsStronglyNoetherian A]` bundle
only — no `pairSubring`-noetherianness anywhere. -/

section FaithfulExample638Base

open TateAlgebra UniformSpace

omit [PlusSubring A] [HasLocLiftPowerBounded A] [IsNoetherianRing A] [IsStronglyNoetherian A]
  [CompatiblePlusSubring A] in
/-- **Faithful Prop 6.17 for `A⟨X⟩`** (Wedhorn Prop 6.17, `wedhorn.txt`, via
`wedhorn_6_17_ideal`): every ideal of `A⟨X⟩` is closed under the canonical Tate topology, using
only `[IsStronglyNoetherian A]` (which makes `A⟨X⟩` noetherian) — **no** `pairSubring`/`A₀⟨X⟩`
noetherianness. This is the faithful (case-(b)) replacement for `tateAlgebra_isClosed_ideal`, which
routes through `Wedhorn.isClosed_ideal_of_noetherian` with `[IsNoetherianRing P.A₀]` (case (a)).

`hA_complete` re-surfaces the ambient `[CompleteSpace A]` (under the right-uniform structure) — the
section bundle's completeness — as an explicit argument, matching the project idiom of the
unfaithful sibling `tateAlgebra_isClosed_ideal`. -/
private theorem tateAlgebra_isClosed_ideal_faithful [IsStronglyNoetherian A]
    (hA_complete : @CompleteSpace A (IsTopologicalAddGroup.rightUniformSpace A))
    (J : Ideal ↥(TateAlgebra A)) :
    IsClosed (J : Set ↥(TateAlgebra A)) := by
  letI uT : UniformSpace ↥(TateAlgebra A) := instUniformSpaceTateAlgebra
  haveI hua : @IsUniformAddGroup _ uT _ := instIsUniformAddGroupTateAlgebra
  haveI hCS : @CompleteSpace _ uT := tateAlgebraTopology'_completeSpace (A := A) hA_complete
  haveI hcg : (@uniformity _ uT).IsCountablyGenerated := by
    haveI hcgn : (@nhds _ instTopologicalSpaceTateAlgebra
        (0 : ↥(TateAlgebra A))).IsCountablyGenerated :=
      tateAlgBasis'.hasBasis_nhds_zero.isCountablyGenerated
    exact @IsUniformAddGroup.uniformity_countably_generated _ uT _ _ (by convert hcgn)
  haveI hT2 : @T2Space _ uT.toTopologicalSpace := instT2SpaceTateAlgebra
  haveI hTR : @IsTopologicalRing _ uT.toTopologicalSpace _ := instIsTopologicalRingTateAlgebra
  haveI hTate : @IsTateRing _ _ uT.toTopologicalSpace := tateAlgebra_isTateRing
  -- A⟨X⟩ is noetherian (A strongly noetherian), so Prop 6.17 closes every ideal. Route through the
  -- FAITHFUL, sorry-free §3.7.2/1 engine `fg_topologicalClosure_isClosed` directly (NOT the iff
  -- `wedhorn_6_17_ideal`, whose REVERSE direction carries a `sorryAx` we never use) — mirroring the
  -- multivariate `MvTateAlgebra.mvTate_isClosed_ideal`.
  haveI : @ContinuousSMul ↥(TateAlgebra A) ↥(TateAlgebra A) _ _ uT.toTopologicalSpace :=
    ⟨continuous_mul⟩
  haveI hnoeth : IsNoetherianRing ↥(TateAlgebra A) := inferInstance
  have hfin : Module.Finite ↥(TateAlgebra A) (Submodule.topologicalClosure J) :=
    Module.Finite.iff_fg.mpr (isNoetherian_def.mp hnoeth _)
  exact ValuationSpectrum.fg_topologicalClosure_isClosed J hfin

omit [PlusSubring A] [HasLocLiftPowerBounded A] [IsNoetherianRing A] [IsStronglyNoetherian A]
  [CompatiblePlusSubring A] in
/-- **Faithful: the principal ideal `(1 − sX)` is closed in `A⟨X⟩`** — specialisation of
`tateAlgebra_isClosed_ideal_faithful` to `oneSubfXIdeal s`, the faithful (case-(b)) replacement for
`oneSubfXIdeal_isClosed` (which carries the `pairSubring`-noetherianness `hnoeth`). -/
private theorem oneSubfXIdeal_isClosed_faithful [IsStronglyNoetherian A]
    (hA_complete : @CompleteSpace A (IsTopologicalAddGroup.rightUniformSpace A)) (s : A) :
    IsClosed ((oneSubfXIdeal s : Ideal ↥(TateAlgebra A)) : Set ↥(TateAlgebra A)) :=
  tateAlgebra_isClosed_ideal_faithful hA_complete (oneSubfXIdeal s)

omit [PlusSubring A] [HasLocLiftPowerBounded A] [IsNoetherianRing A] [IsStronglyNoetherian A]
  [CompatiblePlusSubring A] in
/-- **Faithful: the quotient `A⟨X⟩/(1 − sX)` is T2** — faithful (case-(b)) replacement for
`quotient_oneSubfXIdeal_t2Space`, via the faithful closed-ideal `oneSubfXIdeal_isClosed_faithful`
(no `pairSubring`-noetherianness). -/
private theorem quotient_oneSubfXIdeal_t2Space_faithful [IsStronglyNoetherian A]
    (hA_complete : @CompleteSpace A (IsTopologicalAddGroup.rightUniformSpace A)) (s : A) :
    T2Space (↥(TateAlgebra A) ⧸ oneSubfXIdeal s) := by
  haveI : IsClosed ((oneSubfXIdeal s).toAddSubgroup : Set ↥(TateAlgebra A)) :=
    oneSubfXIdeal_isClosed_faithful hA_complete s
  infer_instance

omit [PlusSubring A] [HasLocLiftPowerBounded A] [IsNoetherianRing A] [IsStronglyNoetherian A]
  [CompatiblePlusSubring A] in
/-- **Faithful: the quotient `A⟨X⟩/(1 − sX)` is complete** under the canonical quotient topology —
faithful (case-(b)) replacement for `quotient_oneSubfXIdeal_completeSpace`. `A⟨X⟩` is complete
(`tateAlgebraTopology'_completeSpace`) and first-countable; `(1 − sX)` is closed by the faithful
`oneSubfXIdeal_isClosed_faithful`; `QuotientAddGroup.completeSpace_right'` (Bourbaki IX.3.1 Prop 4)
then gives completeness — **no** `pairSubring`-noetherianness. -/
private theorem quotient_oneSubfXIdeal_completeSpace_faithful [IsStronglyNoetherian A]
    (hA_complete : @CompleteSpace A (IsTopologicalAddGroup.rightUniformSpace A)) (s : A) :
    @CompleteSpace (↥(TateAlgebra A) ⧸ oneSubfXIdeal s)
      (quotientOneSubfXIdealUniformSpace s) := by
  letI τ : TopologicalSpace ↥(TateAlgebra A) := instTopologicalSpaceTateAlgebra
  haveI _hring : IsTopologicalRing ↥(TateAlgebra A) := instIsTopologicalRingTateAlgebra
  haveI haddgrp : IsTopologicalAddGroup ↥(TateAlgebra A) :=
    IsTopologicalRing.to_topologicalAddGroup
  haveI : FirstCountableTopology ↥(TateAlgebra A) := instFirstCountableTopologyTateAlgebra
  haveI hCS : @CompleteSpace ↥(TateAlgebra A)
      (IsTopologicalAddGroup.rightUniformSpace ↥(TateAlgebra A)) :=
    tateAlgebraTopology'_completeSpace hA_complete
  haveI : IsClosed ((oneSubfXIdeal s).toAddSubgroup : Set ↥(TateAlgebra A)) :=
    oneSubfXIdeal_isClosed_faithful hA_complete s
  exact @QuotientAddGroup.completeSpace_right' ↥(TateAlgebra A) _ τ haddgrp ‹_›
    (oneSubfXIdeal s).toAddSubgroup inferInstance hCS

omit [PlusSubring A] [HasLocLiftPowerBounded A] [IsNoetherianRing A] [CompatiblePlusSubring A] in
/-- **Faithful: the fSubX quotient `A⟨X⟩/(b − X)` is T2** — the fSubX analogue of
`quotient_oneSubfXIdeal_t2Space_faithful`, via the faithful general closed-ideal
`tateAlgebra_isClosed_ideal_faithful` applied to `plusFSubXIdeal A b` (no `pairSubring`-noeth). -/
private theorem quotient_plusFSubXIdeal_t2Space_faithful [IsStronglyNoetherian A]
    (hA_complete : @CompleteSpace A (IsTopologicalAddGroup.rightUniformSpace A)) (b : A) :
    @T2Space (↥(TateAlgebra A) ⧸ plusFSubXIdeal A b) (quotientPlusFSubXIdealTopology A b) := by
  haveI : IsClosed ((plusFSubXIdeal A b).toAddSubgroup : Set ↥(TateAlgebra A)) :=
    tateAlgebra_isClosed_ideal_faithful hA_complete (plusFSubXIdeal A b)
  letI : TopologicalSpace (↥(TateAlgebra A) ⧸ plusFSubXIdeal A b) :=
    quotientPlusFSubXIdealTopology A b
  haveI : IsTopologicalAddGroup (↥(TateAlgebra A) ⧸ plusFSubXIdeal A b) :=
    quotientPlusFSubXIdealTopology_isTopologicalAddGroup A b
  infer_instance

omit [PlusSubring A] [HasLocLiftPowerBounded A] [IsNoetherianRing A] [CompatiblePlusSubring A] in
/-- **Faithful: the fSubX quotient `A⟨X⟩/(b − X)` is complete** under the canonical quotient
topology — fSubX analogue of `quotient_oneSubfXIdeal_completeSpace_faithful`, via the faithful
general closed-ideal `tateAlgebra_isClosed_ideal_faithful` (no `pairSubring`-noeth). -/
private theorem quotient_plusFSubXIdeal_completeSpace_faithful [IsStronglyNoetherian A]
    (hA_complete : @CompleteSpace A (IsTopologicalAddGroup.rightUniformSpace A)) (b : A) :
    @CompleteSpace (↥(TateAlgebra A) ⧸ plusFSubXIdeal A b)
      (quotientPlusFSubXIdealUniformSpace A b) := by
  letI τ : TopologicalSpace ↥(TateAlgebra A) := instTopologicalSpaceTateAlgebra
  haveI _hring : IsTopologicalRing ↥(TateAlgebra A) := instIsTopologicalRingTateAlgebra
  haveI haddgrp : IsTopologicalAddGroup ↥(TateAlgebra A) :=
    IsTopologicalRing.to_topologicalAddGroup
  haveI : FirstCountableTopology ↥(TateAlgebra A) := instFirstCountableTopologyTateAlgebra
  haveI hCS : @CompleteSpace ↥(TateAlgebra A)
      (IsTopologicalAddGroup.rightUniformSpace ↥(TateAlgebra A)) :=
    tateAlgebraTopology'_completeSpace hA_complete
  haveI : IsClosed ((plusFSubXIdeal A b).toAddSubgroup : Set ↥(TateAlgebra A)) :=
    tateAlgebra_isClosed_ideal_faithful hA_complete (plusFSubXIdeal A b)
  exact @QuotientAddGroup.completeSpace_right' ↥(TateAlgebra A) _ τ haddgrp ‹_›
    (plusFSubXIdeal A b).toAddSubgroup inferInstance hCS

omit [PlusSubring A] [IsHuberRing A] [HasLocLiftPowerBounded A] [CompatiblePlusSubring A] in
/-- **Faithful forward completion map** `presheafValue D →+* A⟨X⟩/(1−sX)` — faithful (case-(b))
replacement for `presheafValueToCanonicalQuotient`, which threads `hnoeth`. The localization
generator map `locToQuotientOneSubfX_gen D.s : Localization.Away D.s → A⟨X⟩/(1−sX)` extends to the
completion `presheafValue D` because the target is complete (`quotient_oneSubfXIdeal_completeSpace_faithful`)
and Hausdorff (`quotient_oneSubfXIdeal_t2Space_faithful`), both supplied faithfully from
`[IsStronglyNoetherian A]` + `hA_complete`. -/
private noncomputable def presheafValueToCanonicalQuotient_faithful [IsStronglyNoetherian A]
    (D : RationalLocData A)
    (hA_complete : @CompleteSpace A (IsTopologicalAddGroup.rightUniformSpace A))
    (hT_pb : ∀ t ∈ D.T, TopologicalRing.IsPowerBounded t) :
    presheafValue D →+* (↥(TateAlgebra A) ⧸ oneSubfXIdeal D.s) := by
  letI : UniformSpace (Localization.Away D.s) := D.uniformSpace
  letI : IsTopologicalRing (Localization.Away D.s) := D.isTopologicalRing
  letI : IsUniformAddGroup (Localization.Away D.s) := D.isUniformAddGroup
  letI : TopologicalSpace (↥(TateAlgebra A) ⧸ oneSubfXIdeal D.s) :=
    quotientOneSubfXIdealTopology D.s
  letI : IsTopologicalRing (↥(TateAlgebra A) ⧸ oneSubfXIdeal D.s) :=
    quotientOneSubfXIdealTopology_isTopologicalRing D.s
  letI : IsTopologicalAddGroup (↥(TateAlgebra A) ⧸ oneSubfXIdeal D.s) :=
    quotientOneSubfXIdealTopology_isTopologicalAddGroup D.s
  letI : UniformSpace (↥(TateAlgebra A) ⧸ oneSubfXIdeal D.s) :=
    quotientOneSubfXIdealUniformSpace D.s
  letI : IsUniformAddGroup (↥(TateAlgebra A) ⧸ oneSubfXIdeal D.s) :=
    quotientOneSubfXIdeal_isUniformAddGroup D.s
  haveI : CompleteSpace (↥(TateAlgebra A) ⧸ oneSubfXIdeal D.s) :=
    quotient_oneSubfXIdeal_completeSpace_faithful hA_complete D.s
  haveI hT2Q : @T2Space _ (quotientOneSubfXIdealTopology D.s) :=
    quotient_oneSubfXIdeal_t2Space_faithful hA_complete D.s
  haveI hT0Q : @T0Space _ (quotientOneSubfXIdealTopology D.s) :=
    @T1Space.t0Space _ (quotientOneSubfXIdealTopology D.s) (T2Space.t1Space)
  exact @UniformSpace.Completion.extensionHom _ _ _ _ _ _
    (quotientOneSubfXIdealUniformSpace D.s) _
    (quotientOneSubfXIdeal_isUniformAddGroup D.s)
    (quotientOneSubfXIdealTopology_isTopologicalRing D.s)
    (locToQuotientOneSubfX_gen D.s)
    (locToQuotientOneSubfX_gen_continuous_canonical D hT_pb)
    (quotient_oneSubfXIdeal_completeSpace_faithful hA_complete D.s)
    hT0Q

omit [PlusSubring A] [HasLocLiftPowerBounded A] [CompatiblePlusSubring A] in
/-- The faithful forward map sends `coeRingHom a` to `locToQuotientOneSubfX_gen D.s a` — faithful
analogue of `presheafValueToCanonicalQuotient_coe`. -/
private theorem presheafValueToCanonicalQuotient_faithful_coe [IsStronglyNoetherian A]
    (D : RationalLocData A)
    (hA_complete : @CompleteSpace A (IsTopologicalAddGroup.rightUniformSpace A))
    (hT_pb : ∀ t ∈ D.T, TopologicalRing.IsPowerBounded t)
    (a : Localization.Away D.s) :
    presheafValueToCanonicalQuotient_faithful D hA_complete hT_pb (D.coeRingHom a) =
      locToQuotientOneSubfX_gen D.s a := by
  letI : UniformSpace (Localization.Away D.s) := D.uniformSpace
  letI : IsTopologicalRing (Localization.Away D.s) := D.isTopologicalRing
  letI : IsUniformAddGroup (Localization.Away D.s) := D.isUniformAddGroup
  letI : TopologicalSpace (↥(TateAlgebra A) ⧸ oneSubfXIdeal D.s) :=
    quotientOneSubfXIdealTopology D.s
  letI : IsTopologicalRing (↥(TateAlgebra A) ⧸ oneSubfXIdeal D.s) :=
    quotientOneSubfXIdealTopology_isTopologicalRing D.s
  letI : IsTopologicalAddGroup (↥(TateAlgebra A) ⧸ oneSubfXIdeal D.s) :=
    quotientOneSubfXIdealTopology_isTopologicalAddGroup D.s
  letI : UniformSpace (↥(TateAlgebra A) ⧸ oneSubfXIdeal D.s) :=
    quotientOneSubfXIdealUniformSpace D.s
  letI : IsUniformAddGroup (↥(TateAlgebra A) ⧸ oneSubfXIdeal D.s) :=
    quotientOneSubfXIdeal_isUniformAddGroup D.s
  haveI : CompleteSpace (↥(TateAlgebra A) ⧸ oneSubfXIdeal D.s) :=
    quotient_oneSubfXIdeal_completeSpace_faithful hA_complete D.s
  haveI hT2Q : @T2Space _ (quotientOneSubfXIdealTopology D.s) :=
    quotient_oneSubfXIdeal_t2Space_faithful hA_complete D.s
  haveI hT0Q : @T0Space _ (quotientOneSubfXIdealTopology D.s) :=
    @T1Space.t0Space _ (quotientOneSubfXIdealTopology D.s) (T2Space.t1Space)
  exact @UniformSpace.Completion.extensionHom_coe _ _ _ _ _ _
    (quotientOneSubfXIdealUniformSpace D.s) _
    (quotientOneSubfXIdeal_isUniformAddGroup D.s)
    (quotientOneSubfXIdealTopology_isTopologicalRing D.s)
    (locToQuotientOneSubfX_gen D.s)
    (locToQuotientOneSubfX_gen_continuous_canonical D hT_pb)
    (quotient_oneSubfXIdeal_completeSpace_faithful hA_complete D.s)
    hT0Q a

omit [PlusSubring A] [HasLocLiftPowerBounded A] [CompatiblePlusSubring A] in
/-- Faithful continuity of the forward map (`Completion.continuous_extension`), no `hnoeth`. -/
private theorem presheafValueToCanonicalQuotient_faithful_continuous [IsStronglyNoetherian A]
    (D : RationalLocData A)
    (hA_complete : @CompleteSpace A (IsTopologicalAddGroup.rightUniformSpace A))
    (hT_pb : ∀ t ∈ D.T, TopologicalRing.IsPowerBounded t) :
    @Continuous _ _ (inferInstance : TopologicalSpace (presheafValue D))
      (quotientOneSubfXIdealTopology D.s)
      (presheafValueToCanonicalQuotient_faithful D hA_complete hT_pb) :=
  @UniformSpace.Completion.continuous_extension _ D.uniformSpace _
    (quotientOneSubfXIdealUniformSpace D.s)
    (↑(locToQuotientOneSubfX_gen D.s))
    (quotient_oneSubfXIdeal_completeSpace_faithful hA_complete D.s)

omit [PlusSubring A] [HasLocLiftPowerBounded A] [CompatiblePlusSubring A] in
/-- Faithful round-trip `backward ∘ forward = id` on `presheafValue D` — faithful analogue of
`tateQuotientToPresheaf_comp_presheafToCanonicalQuotient`. -/
private theorem tateQuotientToPresheaf_comp_faithful [IsStronglyNoetherian A]
    (D : RationalLocData A)
    (hb : TopologicalRing.IsPowerBounded (invS D))
    (hA_complete : @CompleteSpace A (IsTopologicalAddGroup.rightUniformSpace A))
    (hT_pb : ∀ t ∈ D.T, TopologicalRing.IsPowerBounded t)
    (x : presheafValue D) :
    tateQuotientToPresheafHom D hb
      (presheafValueToCanonicalQuotient_faithful D hA_complete hT_pb x) = x := by
  letI : UniformSpace (Localization.Away D.s) := D.uniformSpace
  letI : IsTopologicalRing (Localization.Away D.s) := D.isTopologicalRing
  letI : IsUniformAddGroup (Localization.Away D.s) := D.isUniformAddGroup
  letI τC : TopologicalSpace (↥(TateAlgebra A) ⧸ oneSubfXIdeal D.s) :=
    quotientOneSubfXIdealTopology D.s
  letI : UniformSpace (↥(TateAlgebra A) ⧸ oneSubfXIdeal D.s) :=
    quotientOneSubfXIdealUniformSpace D.s
  have hcont_ext := presheafValueToCanonicalQuotient_faithful_continuous D hA_complete hT_pb
  refine @UniformSpace.Completion.ext' _ D.uniformSpace
    (presheafValue D) _ _ _ _
    ((tateQuotientToPresheafHom_continuous_of_tate D hb).comp hcont_ext)
    continuous_id ?_ x
  intro a
  simp only [Function.comp, id]
  change tateQuotientToPresheafHom D hb
    (presheafValueToCanonicalQuotient_faithful D hA_complete hT_pb (D.coeRingHom a)) =
    D.coeRingHom a
  rw [presheafValueToCanonicalQuotient_faithful_coe D hA_complete hT_pb a,
    tateQuotient_roundtrip_apply D hb a, locLiftToPresheaf_eq_coeRingHom D]

omit [HasLocLiftPowerBounded A] [CompatiblePlusSubring A] in
/-- Faithful round-trip `forward ∘ backward = id` on `A⟨X⟩/(1−sX)` — faithful analogue of
`presheafToCanonicalQuotient_comp_tateQuotientToPresheaf`. -/
private theorem presheafToCanonicalQuotient_comp_faithful [IsStronglyNoetherian A]
    (D : RationalLocData A)
    (hb : TopologicalRing.IsPowerBounded (invS D))
    (hA_complete : @CompleteSpace A (IsTopologicalAddGroup.rightUniformSpace A))
    (hT_pb : ∀ t ∈ D.T, TopologicalRing.IsPowerBounded t)
    (q : ↥(TateAlgebra A) ⧸ oneSubfXIdeal D.s) :
    presheafValueToCanonicalQuotient_faithful D hA_complete hT_pb
      (tateQuotientToPresheafHom D hb q) = q := by
  letI : UniformSpace (Localization.Away D.s) := D.uniformSpace
  letI : IsTopologicalRing (Localization.Away D.s) := D.isTopologicalRing
  letI : IsUniformAddGroup (Localization.Away D.s) := D.isUniformAddGroup
  letI τC : TopologicalSpace (↥(TateAlgebra A) ⧸ oneSubfXIdeal D.s) :=
    quotientOneSubfXIdealTopology D.s
  letI : UniformSpace (↥(TateAlgebra A) ⧸ oneSubfXIdeal D.s) :=
    quotientOneSubfXIdealUniformSpace D.s
  letI : IsTopologicalRing (↥(TateAlgebra A) ⧸ oneSubfXIdeal D.s) :=
    quotientOneSubfXIdealTopology_isTopologicalRing D.s
  letI : IsTopologicalAddGroup (↥(TateAlgebra A) ⧸ oneSubfXIdeal D.s) :=
    quotientOneSubfXIdealTopology_isTopologicalAddGroup D.s
  letI : IsUniformAddGroup (↥(TateAlgebra A) ⧸ oneSubfXIdeal D.s) :=
    quotientOneSubfXIdeal_isUniformAddGroup D.s
  haveI hT2 : @T2Space _ τC := quotient_oneSubfXIdeal_t2Space_faithful hA_complete D.s
  haveI : @CompleteSpace _ (quotientOneSubfXIdealUniformSpace D.s) :=
    quotient_oneSubfXIdeal_completeSpace_faithful hA_complete D.s
  have hdense := locToQuotientOneSubfX_gen_denseRange_canonical D.s
  have hagree : ∀ (a : Localization.Away D.s),
      presheafValueToCanonicalQuotient_faithful D hA_complete hT_pb
        (tateQuotientToPresheafHom D hb (locToQuotientOneSubfX_gen D.s a)) =
        locToQuotientOneSubfX_gen D.s a := by
    intro a
    rw [tateQuotient_roundtrip_apply D hb a, locLiftToPresheaf_eq_coeRingHom D,
      presheafValueToCanonicalQuotient_faithful_coe D hA_complete hT_pb a]
  have hcont_ext := presheafValueToCanonicalQuotient_faithful_continuous D hA_complete hT_pb
  have h_eq : (fun q ↦ presheafValueToCanonicalQuotient_faithful D hA_complete hT_pb
      (tateQuotientToPresheafHom D hb q)) = (fun q ↦ q) :=
    hdense.equalizer
      (hcont_ext.comp (tateQuotientToPresheafHom_continuous_of_tate D hb))
      continuous_id (funext hagree)
  exact congr_fun h_eq q

omit [PlusSubring A] [IsHuberRing A] [HasLocLiftPowerBounded A] [CompatiblePlusSubring A] in
/-- **Faithful Example-6.38 ring iso** `presheafValue D ≃+* A⟨X⟩/(1−sX)` (Wedhorn Example 6.38) —
faithful (case-(b)) analogue of `presheafValueCanonicalQuotientEquiv`, built from the faithful
forward map and round-trips with the `[IsStronglyNoetherian A]` bundle only (no `hnoeth`).

Bundle-light (no `PlusSubring`/`IsHuberRing`/`HasLocLiftPowerBounded`/`CompatiblePlusSubring`) so it
is instantiable at the base `B := presheafValue D` (used by the faithful Example 6.38/6.39 bridges
of `WedhornCechAcyclicity.lean`). -/
noncomputable def presheafValueCanonicalQuotientEquiv_faithful [IsStronglyNoetherian A]
    (D : RationalLocData A)
    (hb : TopologicalRing.IsPowerBounded (invS D))
    (hA_complete : @CompleteSpace A (IsTopologicalAddGroup.rightUniformSpace A))
    (hT_pb : ∀ t ∈ D.T, TopologicalRing.IsPowerBounded t) :
    presheafValue D ≃+* (↥(TateAlgebra A) ⧸ oneSubfXIdeal D.s) where
  toFun := presheafValueToCanonicalQuotient_faithful D hA_complete hT_pb
  invFun := tateQuotientToPresheafHom D hb
  left_inv := tateQuotientToPresheaf_comp_faithful D hb hA_complete hT_pb
  right_inv := presheafToCanonicalQuotient_comp_faithful D hb hA_complete hT_pb
  map_mul' := map_mul _
  map_add' := map_add _

omit [HasLocLiftPowerBounded A] [CompatiblePlusSubring A] in
/-- **Faithful canonical-map intertwining**: the faithful Example-6.38 ring iso sends
`canonicalMap a` to `mk(algebraMap a)`, i.e. it intertwines the `A`-algebra structure on
`presheafValue D` (via `D.canonicalMap`) with the `A`-algebra structure on `A⟨X⟩/(1−sX)`
(via `mk ∘ algebraMap`). Faithful (case-(b)) analogue of
`presheafValueCanonicalQuotientEquiv_canonicalMap`: `canonicalMap a = coeRingHom(algebraMap a)`,
and the forward map sends `coeRingHom(algebraMap a)` to `locToQuotientOneSubfX_gen D.s (algebraMap
a) = mk(algebraMap a)` (`presheafValueToCanonicalQuotient_faithful_coe` +
`locToQuotientOneSubfX_gen_algebraMap`). -/
theorem presheafValueCanonicalQuotientEquiv_faithful_canonicalMap [IsStronglyNoetherian A]
    (D : RationalLocData A)
    (hb : TopologicalRing.IsPowerBounded (invS D))
    (hA_complete : @CompleteSpace A (IsTopologicalAddGroup.rightUniformSpace A))
    (hT_pb : ∀ t ∈ D.T, TopologicalRing.IsPowerBounded t) (a : A) :
    presheafValueCanonicalQuotientEquiv_faithful D hb hA_complete hT_pb (D.canonicalMap a) =
      (Ideal.Quotient.mk (oneSubfXIdeal D.s)) (algebraMap A ↥(TateAlgebra A) a) := by
  change presheafValueToCanonicalQuotient_faithful D hA_complete hT_pb (D.canonicalMap a) = _
  -- `D.canonicalMap a = D.coeRingHom (algebraMap a)`.
  rw [show D.canonicalMap a = D.coeRingHom (algebraMap A (Localization.Away D.s) a) from rfl,
    presheafValueToCanonicalQuotient_faithful_coe D hA_complete hT_pb,
    locToQuotientOneSubfX_gen_algebraMap]

/-! ### Faithful noetherianness of `presheafValue D` (Step 1, noetherian part)

The whole-space base `presheafValue (globalLocData P) = 𝒪_X(X)` is noetherian by the faithful
Example 6.38 equivalence `presheafValueCanonicalQuotientEquiv_faithful`: `globalLocData P` has
`T = {1}`, `s = 1`, so `invS = 1` is power-bounded (`invS_isPowerBounded_of_one_mem_T`, `1 ∈ {1}`)
and every `t ∈ {1}` is power-bounded — hence `presheafValue (globalLocData P) ≃+* A⟨X⟩/(1 − X)`, a
quotient of the noetherian (strong-noetherian `A`) ring `A⟨X⟩`. This whole-space (`hb`-available)
case is sorry-free (modulo the upstream Prop-6.17-forward `sorryAx`, see below).

⚠️ The general-`D` case does NOT reduce to this base by localization: the would-be fact
"`presheafValue D = IsLocalization.Away (canonicalMap s) (presheafValue 𝒪_X(X))`" rests on
`restrictionMapHom_surj`, which is **deprecated as FALSE IN GENERAL** (PresheafTateStructure.lean:
"RETIRED — false in general; ... range(σ) closed fails", 2026-05-23). Wedhorn's `𝒪_X(R(T/s))` for a
general rational subset is *not* `𝒪_X(X)[1/s]`; the `T`-conditions genuinely change the ring. The
faithful general-`D` route is the **multivariate** Example 6.38 `presheafValue D ≃ A⟨X₁..Xₙ⟩/a`
(with `Xᵢ ↦ tᵢ/s`, which ARE power-bounded), a quotient of the noetherian `A⟨X₁..Xₙ⟩` — repo gap. -/

/-- **Faithful: the whole-space value `𝒪_X(X) = presheafValue (globalLocData P)` is noetherian.**
Via `presheafValueCanonicalQuotientEquiv_faithful`: `globalLocData P` has `T = {1}`, `s = 1`, so the
faithful Example 6.38 iso gives `presheafValue (globalLocData P) ≃+* A⟨X⟩/(1 − X)`, a quotient of
the noetherian `A⟨X⟩` (`[IsStronglyNoetherian A]`). Honest case-(b) noetherianness for the whole
space, with NO `pairSubring`/`A₀⟨X⟩` noetherianness and NO Bourbaki noeth-`A₀` completion. -/
private theorem presheafValue_globalLocData_isNoetherianRing (P : PairOfDefinition A) :
    IsNoetherianRing (presheafValue (globalLocData P)) := by
  letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A
  haveI hAc : @CompleteSpace A (IsTopologicalAddGroup.rightUniformSpace A) := ‹_›
  -- `invS (globalLocData P)` is power-bounded since `1 ∈ {1} = (globalLocData P).T`.
  have hb : TopologicalRing.IsPowerBounded (invS (globalLocData P)) := by
    rw [invS_eq_coeRingHom_divByS_one]
    exact CompletionLocalization.invS_isPowerBounded_of_one_mem_T
      (globalLocData P) (Finset.mem_singleton_self 1)
  -- Every `t ∈ (globalLocData P).T = {1}` is power-bounded.
  have hT_pb : ∀ t ∈ (globalLocData P).T, TopologicalRing.IsPowerBounded t := by
    intro t ht
    rw [show (globalLocData P).T = {1} from rfl, Finset.mem_singleton] at ht
    rw [ht]; exact TopologicalRing.isPowerBounded_one
  -- Transport noetherianness across the faithful Example 6.38 equiv.
  exact isNoetherianRing_of_ringEquiv _
    (presheafValueCanonicalQuotientEquiv_faithful (globalLocData P) hb hAc hT_pb).symm

end FaithfulExample638Base

/-! ## Lemma 8.31 — flatness of `A⟨X⟩` and its Laurent quotients

> **Lemma 8.31.** Let `A` be a noetherian complete Tate ring.
> (1) The ring `A⟨X⟩` is faithfully flat over `A`.
> (2) For all `f ∈ A` the rings `A⟨X⟩/(f − X)` and `A⟨X⟩/(1 − fX)` are flat over `A`.

Wedhorn's proof uses **Remark 8.29** (`M ⊗_A A⟨X⟩ ≅ M⟨X⟩` for finitely generated `M`,
which rests on Prop 6.18 — proven in `BanachOMT.lean`) plus the explicit injectivity
computations for `1 − fX` and `f − X`. -/

omit [PlusSubring A] [HasLocLiftPowerBounded A] [IsStronglyNoetherian A]
  [CompatiblePlusSubring A] in
/-- **Lemma 8.31(1)** (Wedhorn p. 82, `wedhorn.txt:4106`): `A⟨X⟩` is faithfully flat over `A`,
for `A` a **noetherian** complete Tate ring. Wedhorn's proof: flatness from Remark 8.29
(`TateAlgebra.muMap_injective` — `i ⊗ id : N ⊗ A⟨X⟩ → M ⊗ A⟨X⟩` is injective whenever
`i : N ↪ M`), and the faithful half from the prime `q = {Σ aᵥ Xᵥ : a₀ ∈ p}` lying over each
prime `p` (`q ∩ A = p`).

**Faithfulness:** stated with `[IsNoetherianRing A]` (the Tate ring, = strongly-noeth at `k = 0`)
only. The noeth-`A₀` route `TateAlgebra.faithfullyFlat_general P` is the Wedhorn **case (a)**
argument (Artin–Rees over a ring of definition) and **must not** be used to discharge the
case-(b) target. See `.mathlib-quality/decomposition.md` §LEAF A2 (2026-06-02). -/
theorem lemma_8_31_tateAlgebra_faithfullyFlat :
    Module.FaithfullyFlat A ↥(TateAlgebra A) := by
  haveI : Module.Flat A ↥(TateAlgebra A) := tateAlgebra_flat_faithful
  exact Module.FaithfullyFlat.of_comap_surjective
    TateAlgebra.PrimeSpectrum_comap_algebraMap_surjective

omit [PlusSubring A] [HasLocLiftPowerBounded A] [IsStronglyNoetherian A]
  [CompatiblePlusSubring A] in
/-- **Lemma 8.31(2), minus shape** (Wedhorn p. 82, `wedhorn.txt:4108`): `A⟨X⟩/(1 − fX)` is flat
over `A`. Wedhorn's proof: the multiplication `w_{1-fX} : M⟨X⟩ → M⟨X⟩` is injective (easy check),
so by the claim at `:4116` `A⟨X⟩/(1 − fX)` is flat. **Faithful: `[IsNoetherianRing A]` only**
(the noeth-`A₀` route `TateAlgebra.flat_quotient_oneSubfX_general P` is case (a)). -/
theorem lemma_8_31_oneSubfX_flat (f : A) :
    Module.Flat A (↥(TateAlgebra A) ⧸
      Ideal.span {1 - algebraMap A ↥(TateAlgebra A) f * TateAlgebra.X}) := by
  haveI : Module.Flat A ↥(TateAlgebra A) := tateAlgebra_flat_faithful
  exact Module.Flat.quotient_of_flat_of_saturated
    (TateAlgebra.mul_oneSubfX_regular f)
    (fun I s hmem => oneSubfX_saturated_faithful f I s hmem)

omit [HasLocLiftPowerBounded A] [CompatiblePlusSubring A] in
/-- **Faithful Prop 8.30 base step (Steps 2–4 over the base, the LaurentNormalized core)**
(Wedhorn Prop 8.30 + Lemma 8.31, `wedhorn.txt:4099`–`4108`).

For a complete strongly noetherian Tate ring `A` and a rational locale `D` over `A` whose
generators (`invS D` and every `t ∈ D.T`) are power-bounded, `presheafValue D` is **flat** over `A`
along `D.canonicalMap`.

This is the FAITHFUL (case-(b)) replacement for `presheafValue_flat_of_canonical`: it routes
through the faithful Example-6.38 iso `presheafValueCanonicalQuotientEquiv_faithful`
(`presheafValue D ≃+* A⟨X⟩/(1−sX)`, `[IsStronglyNoetherian A]`-only, NO `pairSubring`/`A₀⟨X⟩`
noetherianness) and the faithful Lemma 8.31(2) `lemma_8_31_oneSubfX_flat` (`[IsNoetherianRing A]`,
derived from `[IsStronglyNoetherian A]` at `k = 0`). The case-(a) route
`presheafValue_flat_of_canonical → flat_quotient_oneSubfX_general P` (needs `[IsNoetherianRing P.A₀]`,
ℂ_p-false) is avoided entirely.

The power-boundedness hypotheses `hb`/`hT_pb` are exactly those Wedhorn's reduction guarantees: for a
basic-Laurent subset `R(1/f)` (`s = f`, `1 ∈ T = {1}`) one has `invS = 1/s` power-bounded via `1 ∈ T`
(`invS_isPowerBounded_of_one_mem_T`) and `1 ∈ T = {1}` power-bounded; more generally any
LaurentNormalized datum supplies both.

Its only flatness input is `lemma_8_31_oneSubfX_flat` (case (b), `[IsNoetherianRing A]`); it never
touches the case-(a) `flat_quotient_oneSubfX_general P` (which needs `[IsNoetherianRing P.A₀]` and is
ℂ_p-false). The body uses only the faithful Example-6.38 iso `presheafValueCanonicalQuotientEquiv_faithful`
+ its `canonicalMap` intertwining + `Module.Flat.of_linearEquiv` — no `A⁺`/Huber/loc-lift content. See
`prop_8_30_relative_laurent_flat` for how this engine is meant to feed the (still-missing) relative
reduction object. -/
-- de-privatised 2026-06-11: consumed by `prop_8_30_basic_laurent_step_flat`,
-- relocated to `RelativePieceKeystone.lean` (across the file boundary).
theorem presheafValue_flat_of_canonical_faithful [IsStronglyNoetherian A]
    (D : RationalLocData A)
    (hb : TopologicalRing.IsPowerBounded (invS D))
    (hA_complete : @CompleteSpace A (IsTopologicalAddGroup.rightUniformSpace A))
    (hT_pb : ∀ t ∈ D.T, TopologicalRing.IsPowerBounded t) :
    @Module.Flat A (presheafValue D) _ _ (RingHom.toModule D.canonicalMap) := by
  -- The faithful Lemma 8.31(2): `A⟨X⟩/(1 − sX)` is flat over `A` (`[IsNoetherianRing A]` only).
  haveI hflat_quot : Module.Flat A (↥(TateAlgebra A) ⧸ oneSubfXIdeal D.s) :=
    lemma_8_31_oneSubfX_flat (A := A) D.s
  let e := presheafValueCanonicalQuotientEquiv_faithful D hb hA_complete hT_pb
  change @Module.Flat A (presheafValue D) _ _ (RingHom.toModule D.canonicalMap)
  letI : Module A (presheafValue D) := RingHom.toModule D.canonicalMap
  -- The faithful equiv intertwines the two `A`-module structures (`canonicalMap` ↔ `mk∘algebraMap`).
  have he_smul : ∀ (a : A) (x : presheafValue D), e (a • x) = a • e x := by
    intro a x
    change e (D.canonicalMap a * x) =
      (Ideal.Quotient.mk (oneSubfXIdeal D.s)) (algebraMap A ↥(TateAlgebra A) a) * e x
    rw [e.map_mul]; congr 1
    exact presheafValueCanonicalQuotientEquiv_faithful_canonicalMap D hb hA_complete hT_pb a
  exact @Module.Flat.of_linearEquiv A (↥(TateAlgebra A) ⧸ oneSubfXIdeal D.s) (presheafValue D)
    _ _ _ _ _ hflat_quot
    { toLinearMap := { toFun := e, map_add' := e.map_add, map_smul' := he_smul }
      invFun := e.symm
      left_inv := e.symm_apply_apply
      right_inv := e.apply_symm_apply }

omit [PlusSubring A] [HasLocLiftPowerBounded A] [IsStronglyNoetherian A]
  [CompatiblePlusSubring A] in
/-- **Lemma 8.31(2), plus shape** (Wedhorn p. 82, `wedhorn.txt:4108`): `A⟨X⟩/(f − X)` is flat
over `A`. Wedhorn's proof: for `u = Σ mᵥ Xᵥ` with `(f − X)u = 0` one gets `f m₀ = 0`,
`f mᵥ = mᵥ₋₁`; as `M` is noetherian the submodule `M′ = ⟨mᵥ⟩` is finitely generated, forcing
`M′ = 0`, so `w_{f-X}` is injective and the quotient is flat. **Faithful: `[IsNoetherianRing A]`
only** (the noeth use is "`M` noetherian"; the noeth-`A₀` route
`TateAlgebra.flat_quotient_fSubX_general P` is case (a)). -/
theorem lemma_8_31_fSubX_flat (f : A) :
    Module.Flat A (↥(TateAlgebra A) ⧸
      Ideal.span {algebraMap A ↥(TateAlgebra A) f - TateAlgebra.X}) := by
  haveI : Module.Flat A ↥(TateAlgebra A) := tateAlgebra_flat_faithful
  exact Module.Flat.quotient_of_flat_of_saturated
    (TateAlgebra.mul_fSubX_regular f)
    (fun I s hmem => fSubX_saturated_faithful f I s hmem)

/-! ## Corollary 8.32 — the product restriction is faithfully flat (⇒ injective)

> **Corollary 8.32.** Let `A` be a strongly noetherian Tate affinoid ring, `X = Spa A`, and
> `(Uᵢ)` a finite rational covering of `X`. Then `O_X(X) → ∏ᵢ O_X(Uᵢ)`, `f ↦ (f|Uᵢ)`, is
> faithfully flat (and in particular injective).

By Example 6.38 each `O_X(Uᵢ)` is a Laurent quotient `O_X(X)⟨X⟩/(…)`, so flatness of each
factor is **Lemma 8.31(2)** over the base `O_X(X)`; faithful flatness of the product follows
because the cover is jointly surjective on Spa (prime-surjectivity). -/
/-! ### Proposition 8.30 — faithful decomposition (Example 6.38 + Remark 7.55 + Lemma 8.31)

Wedhorn's proof of Prop 8.30 (p. 81, `wedhorn.txt:4095`) is, verbatim:

> "By Example 6.38, `O_X(V)` is again a strongly noetherian Tate ring. Thus we may assume
> `X = V` and `A` complete. By Remark 7.55 we may assume `U` is `U₁ = R(f/1) = {x(f) ≤ 1}`
> or `U₂ = R(1/f) = {x(f) ≥ 1}` for some `f ∈ A`. In Example 6.38 we have seen
> `O_X(U₁) = Â⟨X⟩/(f−X)` and `O_X(U₂) = Â⟨X⟩/(1−fX)`. Thus it suffices to show Lemma 8.31."

The faithful Lean skeleton mirrors this exactly. Write `B := presheafValue D = O_X(V)`.

* **Step 1 (Example 6.38, the base).** `B` is again a *complete strongly noetherian Tate*
  ring. In Lean this means `B` carries the instance bundle that `lemma_8_31_*` consume:
  `IsTateRing B`, `IsNoetherianRing B`, `IsLinearTopology B B` (the remaining members
  — `IsTopologicalRing`, `T2Space`, `NonarchimedeanRing`, `CompleteSpace`, `PlusSubring`
  — are already plain instances on `presheafValue D`, and `IsHuberRing B` /
  `HasLocLiftPowerBounded B` / `IsStronglyNoetherian B` are *derived* from those three plus
  `isStronglyNoetherian_of_isNoetherianRing_isTateRing`). These three are isolated as the
  faithful helpers `presheafValue_isTateRing_faithful`, `presheafValue_isNoetherianRing_faithful`,
  `presheafValue_isLinearTopology_faithful` below. They are FAITHFUL: parameterised only by
  `D` and the ambient strongly-noetherian-Tate `A`-bundle — **no** `PairOfDefinition A`, **no**
  `[IsNoetherianRing P.A₀]`. (The repo's existing `presheafValue_isTateRing` /
  `presheafValue_isNoetherianRing_of_…` route through a noetherian ring of definition `A₀`,
  which is the Wedhorn case-(a) / `ℂ_p`-false defect and must not be used here.)

* **Steps 2–4 (Remark 7.55 + Example 6.38 over `B` + Lemma 8.31).** With `B` strongly
  noetherian Tate and complete, reduce `U ⊆ V` to a basic Laurent shape `R(f̄/1)` /
  `R(1/f̄)` over `B` (Remark 7.55), identify `O_X(U)` as the Laurent quotient
  `B⟨X⟩/(f̄−X)` resp. `B⟨X⟩/(1−f̄X)` *as a `B`-algebra* (Example 6.38 over the base `B`),
  and conclude flatness by `lemma_8_31_fSubX_flat` / `lemma_8_31_oneSubfX_flat` over `B`,
  transported across the `B`-algebra iso by `Module.Flat.of_linearEquiv`. This is isolated
  as the faithful helper `prop_8_30_flat_of_faithful_base` below. -/

omit [CompatiblePlusSubring A] in
/-- **Step 1 of Prop 8.30 — Example 6.38, Tate part** (Wedhorn p. 81, `wedhorn.txt:4095`:
"`O_X(V)` is again a strongly noetherian Tate ring"). The presheaf value `B := presheafValue D`
of a rational locale over a strongly noetherian Tate ring is again a **Tate** ring.

FAITHFUL: depends only on the ambient `A`-bundle and `D` — **no** `PairOfDefinition A`, **no**
`[IsNoetherianRing P.A₀]`. (The repo's `presheafValue_isTateRing` routes through a noetherian
ring of definition `P.A₀`, the Wedhorn case-(a) / `ℂ_p`-false hypothesis; this faithful version
avoids it entirely.)

RESOLVED FAITHFULLY: `IsTateRing = IsHuberRing + topologically-nilpotent unit`. The Tate unit is
`presheafValue_topNilUnit` (sorry-free, `[IsTateRing A]` only). The `PairOfDefinition`
(`presheafValue_ringOfDef D`, `presheafValue_idealOfDef D`, `presheafValue_ringOfDef_isOpen D`,
`presheafValue_idealOfDef_fg D`, `presheafValue_isAdic D`) is built from sub-lemmas that are each
parameterised by `D` ALONE — none consumes `[IsNoetherianRing P.A₀]` (the `(P, [noeth P.A₀])`
carried by `presheafValue_pairOfDefinition_concrete` are pure threading artifacts never invoked in
its body). Hence the Huber structure is faithful and no noeth-`A₀` enters. -/
theorem presheafValue_isTateRing_faithful
    [IsTateRing A] [IsNoetherianRing A] (D : RationalLocData A) :
    IsTateRing (presheafValue D) where
  exists_pairOfDefinition :=
    ⟨{ A₀ := presheafValue_ringOfDef D
       I := presheafValue_idealOfDef D
       isOpen := presheafValue_ringOfDef_isOpen D
       fg := presheafValue_idealOfDef_fg D
       isAdic := presheafValue_isAdic D }⟩
  exists_topologicallyNilpotent_unit := presheafValue_topNilUnit D

/-! ## Multivariate restricted-power-series evaluation (Example 6.38 engine)

The `Fin n` generalization of `evalHomBounded`/`evalHomBounded₂` (`TateAlgebraWedhorn.lean`):
given a continuous ring hom `g : A →+* B` into a complete nonarchimedean ring `B` and a tuple
`b : Fin n → B` of power-bounded elements, the evaluation
`A⟨X₁,…,Xₙ⟩ →+* B`, `Σ aᵥ Xᵛ ↦ Σ aᵥ ∏ᵢ bᵢ^(vᵢ)`, is a ring homomorphism (multivariate
nonarchimedean Cauchy product), and it sends `algebraMap a ↦ g a` and `Xᵢ ↦ bᵢ`.

INFRASTRUCTURE (not in Wedhorn at this granularity): a general-`n` lift of the existing
`Fin 1`/`Fin 2` machinery; mirrors `evalHomBounded₂` line for line. -/

section MvEvalHom

variable {R S : Type*} [CommRing R] [TopologicalSpace R] [NonarchimedeanRing R]
  [CommRing S] [UniformSpace S] [IsUniformAddGroup S] [IsTopologicalRing S]
  [NonarchimedeanRing S] [CompleteSpace S] [T0Space S]

/-- The `v`-th term of the `n`-variate evaluation series:
`g(coeff_v h) · ∏ᵢ bᵢ^(v i)`. -/
noncomputable def mvEvalTerm {n : ℕ} (g : R →+* S) (b : Fin n → S)
    (h : ↥(restrictedMvPowerSeriesSubring n R)) (v : Fin n →₀ ℕ) : S :=
  g (MvPowerSeries.coeff v h.val) * ∏ i, b i ^ (v i)

omit [IsUniformAddGroup S] [NonarchimedeanRing S] [CompleteSpace S] [T0Space S] in
/-- The range of `v ↦ ∏_{i ∈ s} bᵢ^(v i)` over `Fin n →₀ ℕ` is bounded whenever each `bᵢ` is
power-bounded, for any finite index set `s`. Proved by `Finset.induction`, reducing to
`IsBounded.mul` (the product set `range (bₐ ^ ·) * (previous range)`). -/
private theorem mvRangeProdOn_isBounded {n : ℕ} (b : Fin n → S)
    (hb : ∀ i, TopologicalRing.IsBounded (Set.range (b i ^ · : ℕ → S)))
    (s : Finset (Fin n)) :
    TopologicalRing.IsBounded
      (Set.range (fun v : Fin n →₀ ℕ => ∏ i ∈ s, b i ^ (v i))) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using TopologicalRing.isBounded_singleton (1 : S)
  | insert a s ha ih =>
      -- range over `insert a s` ⊆ range(bₐ ^ ·) * range over `s`.
      refine ((hb a).mul ih).subset ?_
      rintro _ ⟨v, rfl⟩
      change ∏ i ∈ insert a s, b i ^ (v i) ∈ _
      rw [Finset.prod_insert ha]
      exact Set.mul_mem_mul ⟨v a, rfl⟩ ⟨v, rfl⟩

omit [IsUniformAddGroup S] [NonarchimedeanRing S] [CompleteSpace S] [T0Space S] in
/-- The range of `v ↦ ∏ᵢ bᵢ^(v i)` over `Fin n →₀ ℕ` is bounded whenever each `bᵢ` is
power-bounded. The full-`univ` case of `mvRangeProdOn_isBounded`. -/
private theorem mvRangeProd_isBounded {n : ℕ} (b : Fin n → S)
    (hb : ∀ i, TopologicalRing.IsBounded (Set.range (b i ^ · : ℕ → S))) :
    TopologicalRing.IsBounded
      (Set.range (fun v : Fin n →₀ ℕ => ∏ i, b i ^ (v i))) :=
  mvRangeProdOn_isBounded b hb Finset.univ

omit [IsUniformAddGroup S] [NonarchimedeanRing S] [CompleteSpace S] [T0Space S] in
/-- The `n`-variate evaluation terms tend to `0` along the cofinite filter on `Fin n →₀ ℕ`.
Uses continuity of `g` (the coefficients form a null family) and boundedness of the product
power range. Mirrors `evalTerm₂_tendsto_zero`. -/
theorem mvEvalTerm_tendsto_zero {n : ℕ} (g : R →+* S) (hg : Continuous g) (b : Fin n → S)
    (hb : ∀ i, TopologicalRing.IsBounded (Set.range (b i ^ · : ℕ → S)))
    (h : ↥(restrictedMvPowerSeriesSubring n R)) :
    Filter.Tendsto (mvEvalTerm g b h) Filter.cofinite (nhds 0) := by
  have hc : Filter.Tendsto (fun v : Fin n →₀ ℕ => g (MvPowerSeries.coeff v h.val))
      Filter.cofinite (nhds 0) :=
    map_zero g ▸ hg.continuousAt.tendsto.comp h.prop
  have hd := mvRangeProd_isBounded b hb
  intro U hU
  obtain ⟨V, hV, hSV⟩ := hd U hU
  have hcV := hc hV
  rw [Filter.mem_map] at hcV ⊢
  refine Filter.mem_of_superset hcV (fun v (hv : _ ∈ V) => ?_)
  change g (MvPowerSeries.coeff v h.val) * (∏ i, b i ^ (v i)) ∈ U
  rw [mul_comm]
  exact hSV (Set.mul_mem_mul ⟨v, rfl⟩ hv)

omit [T0Space S] in
/-- The `n`-variate eval terms are summable in a complete nonarchimedean ring. -/
theorem mvEvalTerm_summable {n : ℕ} (g : R →+* S) (hg : Continuous g) (b : Fin n → S)
    (hb : ∀ i, TopologicalRing.IsBounded (Set.range (b i ^ · : ℕ → S)))
    (h : ↥(restrictedMvPowerSeriesSubring n R)) :
    Summable (mvEvalTerm g b h) :=
  NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
    (mvEvalTerm_tendsto_zero g hg b hb h)

omit [IsUniformAddGroup S] [NonarchimedeanRing S] [CompleteSpace S] [T0Space S] in
/-- Multivariate convolution: `coeff_v (f · h) = ∑_{p+q=v} coeff_p f · coeff_q h`,
directly from `MvPowerSeries.coeff_mul`. -/
private theorem mvCoeff_mul_antidiag {n : ℕ} (f h : ↥(restrictedMvPowerSeriesSubring n R))
    (v : Fin n →₀ ℕ) :
    MvPowerSeries.coeff v ((f * h : ↥(restrictedMvPowerSeriesSubring n R)).val) =
      ∑ p ∈ Finset.antidiagonal v,
        MvPowerSeries.coeff p.1 f.val * MvPowerSeries.coeff p.2 h.val := by
  rw [Subring.coe_mul, MvPowerSeries.coeff_mul]

/-- **Multivariate evaluation ring homomorphism** `A⟨X₁,…,Xₙ⟩ →+* B` at a tuple `b : Fin n → B`
of power-bounded elements, sending `h = Σ aᵥ Xᵛ ↦ Σ aᵥ ∏ᵢ bᵢ^(v i)`.

`map_mul'` uses the nonarchimedean Cauchy product
(`Summable.tsum_mul_tsum_eq_tsum_sum_antidiagonal` over `Fin n →₀ ℕ`) and the multivariate
convolution formula. The `Fin n` generalization of `evalHomBounded`/`evalHomBounded₂`. -/
noncomputable def mvEvalHomBounded {n : ℕ} (g : R →+* S) (hg : Continuous g) (b : Fin n → S)
    (hb : ∀ i, TopologicalRing.IsBounded (Set.range (b i ^ · : ℕ → S))) :
    ↥(restrictedMvPowerSeriesSubring n R) →+* S where
  toFun h := ∑' v, mvEvalTerm g b h v
  map_zero' := by
    simp only [mvEvalTerm, ZeroMemClass.coe_zero, map_zero, zero_mul]
    exact tsum_zero
  map_one' := by
    rw [tsum_eq_single 0]
    · simp only [mvEvalTerm, OneMemClass.coe_one, Finsupp.coe_zero, Pi.zero_apply,
        pow_zero, Finset.prod_const_one, mul_one]
      classical
      rw [MvPowerSeries.coeff_one, if_pos rfl, map_one]
    · intro v hv
      simp only [mvEvalTerm, OneMemClass.coe_one]
      classical
      rw [MvPowerSeries.coeff_one, if_neg hv, map_zero, zero_mul]
  map_add' f h := by
    have hterm : ∀ v, mvEvalTerm g b (f + h) v =
        mvEvalTerm g b f v + mvEvalTerm g b h v := fun v => by
      simp only [mvEvalTerm, Subring.coe_add, map_add, add_mul]
    conv_lhs => arg 1; ext v; rw [hterm v]
    exact (mvEvalTerm_summable g hg b hb f).tsum_add (mvEvalTerm_summable g hg b hb h)
  map_mul' f h := by
    rw [Summable.tsum_mul_tsum_eq_tsum_sum_antidiagonal
      (mvEvalTerm_summable g hg b hb f) (mvEvalTerm_summable g hg b hb h)
      ((mvEvalTerm_summable g hg b hb f).mul_of_nonarchimedean
        (mvEvalTerm_summable g hg b hb h))]
    congr 1
    ext v
    simp only [mvEvalTerm, mvCoeff_mul_antidiag, map_sum, map_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun ⟨p, q⟩ hpq => ?_)
    have hpq_add : p + q = v := Finset.mem_antidiagonal.mp hpq
    have hprod : (∏ i, b i ^ (p i)) * (∏ i, b i ^ (q i)) = ∏ i, b i ^ (v i) := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl (fun i _ => ?_)
      rw [← pow_add, ← Finsupp.add_apply, hpq_add]
    calc g (MvPowerSeries.coeff p f.val) * g (MvPowerSeries.coeff q h.val) *
            ∏ i, b i ^ (v i)
        = (g (MvPowerSeries.coeff p f.val) * ∏ i, b i ^ (p i)) *
            (g (MvPowerSeries.coeff q h.val) * ∏ i, b i ^ (q i)) := by
          rw [← hprod]; ring
      _ = _ := rfl

/-- `mvEvalHomBounded` sends `algebraMap a ↦ g a`. -/
theorem mvEvalHomBounded_algebraMap {n : ℕ} (g : R →+* S) (hg : Continuous g) (b : Fin n → S)
    (hb : ∀ i, TopologicalRing.IsBounded (Set.range (b i ^ · : ℕ → S))) (a : R) :
    mvEvalHomBounded g hg b hb
      (algebraMap R ↥(restrictedMvPowerSeriesSubring n R) a) = g a := by
  change ∑' v, mvEvalTerm g b (algebraMap R ↥(restrictedMvPowerSeriesSubring n R) a) v = g a
  rw [tsum_eq_single 0]
  · simp only [mvEvalTerm, Finsupp.coe_zero, Pi.zero_apply, pow_zero, Finset.prod_const_one,
      mul_one]
    change g ((MvPowerSeries.coeff 0) (MvPowerSeries.C (σ := Fin n) a)) = g a
    classical
    rw [MvPowerSeries.coeff_C, if_pos rfl]
  · intro v hv
    simp only [mvEvalTerm]
    have hcoeff : (MvPowerSeries.coeff (R := R) v)
        ((algebraMap R ↥(restrictedMvPowerSeriesSubring n R) a).val) = 0 := by
      change (MvPowerSeries.coeff (R := R) v) (MvPowerSeries.C (σ := Fin n) a) = 0
      classical
      rw [MvPowerSeries.coeff_C, if_neg hv]
    rw [hcoeff, map_zero, zero_mul]

/-- `mvEvalHomBounded` sends the `j`-th variable `Xⱼ ↦ bⱼ`. -/
theorem mvEvalHomBounded_X {n : ℕ} (g : R →+* S) (hg : Continuous g) (b : Fin n → S)
    (hb : ∀ i, TopologicalRing.IsBounded (Set.range (b i ^ · : ℕ → S))) (j : Fin n) :
    mvEvalHomBounded g hg b hb
      ⟨MvPowerSeries.X j, MvPowerSeries.X_isRestricted j⟩ = b j := by
  change ∑' v, mvEvalTerm g b (⟨MvPowerSeries.X j, MvPowerSeries.X_isRestricted j⟩ :
    ↥(restrictedMvPowerSeriesSubring n R)) v = b j
  classical
  rw [tsum_eq_single (Finsupp.single j 1)]
  · simp only [mvEvalTerm]
    rw [show (MvPowerSeries.coeff (R := R) (Finsupp.single j 1)) (MvPowerSeries.X j) = 1 by
          rw [MvPowerSeries.coeff_X, if_pos rfl], map_one, one_mul]
    rw [Finset.prod_eq_single j]
    · rw [Finsupp.single_eq_same, pow_one]
    · intro i _ hij
      rw [Finsupp.single_apply, if_neg (by exact fun h => hij h.symm), pow_zero]
    · intro hj; exact absurd (Finset.mem_univ j) hj
  · intro v hv
    simp only [mvEvalTerm]
    have hcoeff : (MvPowerSeries.coeff (R := R) v) (MvPowerSeries.X (σ := Fin n) j) = 0 := by
      rw [MvPowerSeries.coeff_X]; exact if_neg hv
    rw [hcoeff, map_zero, zero_mul]

-- INFRASTRUCTURE (not in Wedhorn): in a topological additive group, a summable family all of
-- whose terms lie in an *open* additive subgroup `G` has its sum in `G`. Open subgroups are
-- clopen (`AddSubgroup.isClosed_of_isOpen`); `HasSum` is the limit of the finite partial sums,
-- each in `G` by `AddSubgroup.sum_mem`, so the sum lies in the closed `G` by `IsClosed.mem_of_tendsto`.
private theorem tsum_mem_of_isOpen_addSubgroup {G₀ : Type*} [AddCommGroup G₀]
    [TopologicalSpace G₀] [IsTopologicalAddGroup G₀] {ι : Type*} {f : ι → G₀}
    (hf : Summable f) {G : AddSubgroup G₀} (hG : IsOpen (G : Set G₀))
    (hmem : ∀ i, f i ∈ G) : ∑' i, f i ∈ G := by
  have hclosed : IsClosed (G : Set G₀) := AddSubgroup.isClosed_of_isOpen G hG
  refine hclosed.mem_of_tendsto hf.hasSum (Filter.Eventually.of_forall ?_)
  intro s
  exact G.sum_mem (fun i _ => hmem i)

/-- **`mvEvalHomBounded` is continuous** (generic), for the canonical Tate topology on the source
`R⟨X₁,…,Xₙ⟩` and any nonarchimedean complete target `S`, given a continuous base map `g` and a
power-bounded tuple `b`. The `Fin n` generalization of the `example638_evalHom_continuous` technique:
continuity at `0` (additive-group hom) + nonarchimedean reduction to an open subgroup `W`, absorbing
the bounded product-power range into `W`, so `mvTateAlgNhd n P k` maps into `W`. Used both for
`example638_evalHom` (the `Â⟨T/s⟩` case) and the relative strong-noetherian surjection. -/
theorem mvEvalHomBounded_continuous [IsTateRing R] {n : ℕ}
    (g : R →+* S) (hg : Continuous g) (b : Fin n → S)
    (hb : ∀ i, TopologicalRing.IsBounded (Set.range (b i ^ · : ℕ → S))) :
    @Continuous _ _ (MvTateAlgebra.mvTateAlgebraTopology' n) _ (mvEvalHomBounded g hg b hb) := by
  classical
  letI τC : TopologicalSpace ↥(restrictedMvPowerSeriesSubring n R) :=
    MvTateAlgebra.mvTateAlgebraTopology' n
  haveI hringC : @IsTopologicalRing _ τC _ :=
    MvTateAlgebra.mvTateAlgebraTopology'_isTopologicalRing n
  haveI haddC : @IsTopologicalAddGroup _ τC _ := IsTopologicalRing.to_topologicalAddGroup
  haveI hNA : NonarchimedeanRing S := inferInstance
  refine continuous_of_continuousAt_zero (mvEvalHomBounded g hg b hb) ?_
  rw [ContinuousAt, map_zero, Filter.tendsto_def]
  intro Sset hS
  obtain ⟨W, hWS⟩ := NonarchimedeanRing.is_nonarchimedean Sset hS
  have hRbdd : TopologicalRing.IsBounded
      (Set.range (fun v : Fin n →₀ ℕ => ∏ i, b i ^ (v i))) :=
    mvRangeProd_isBounded b hb
  obtain ⟨V, hV, hVR⟩ := hRbdd (W : Set S) (W.isOpen.mem_nhds W.zero_mem)
  let P := (IsTateRing.principalPair R).toPairOfDefinition
  have hpre : g ⁻¹' V ∈ nhds (0 : R) :=
    hg.continuousAt.preimage_mem_nhds (by rwa [map_zero])
  obtain ⟨k, -, hk⟩ := P.hasBasis_nhds_zero.mem_iff.mp hpre
  refine Filter.mem_of_superset
    ((MvTateAlgebra.mvTateAlgBasis' n).hasBasis_nhds_zero.mem_of_mem (i := k) trivial) ?_
  intro h hh
  apply hWS
  change (∑' v, mvEvalTerm g b h v) ∈ (W : Set _)
  refine tsum_mem_of_isOpen_addSubgroup (mvEvalTerm_summable g hg b hb h) W.isOpen (fun v => ?_)
  change mvEvalTerm g b h v ∈ W
  obtain ⟨bb, hbI, hbeq⟩ := MvTateAlgebra.mvTateAlgNhd_coeff_mem n P k hh v
  have hcoeffV : g (MvPowerSeries.coeff v h.val) ∈ V := by
    rw [← hbeq]; exact hk ⟨bb, hbI, rfl⟩
  apply hVR
  rw [show mvEvalTerm g b h v =
      (∏ i, b i ^ (v i)) * g (MvPowerSeries.coeff v h.val) from by
    rw [mvEvalTerm]; ring]
  exact Set.mul_mem_mul ⟨v, rfl⟩ hcoeffV

end MvEvalHom

omit [CompatiblePlusSubring A] in
set_option linter.unusedSectionVars false in
/-- The `i`-th rational generator `tᵢ/s ∈ presheafValue D` (`i : Fin D.T.card`):
the image under `D.coeRingHom` of `divByS (i-th element of D.T) D.s`. -/
noncomputable def example638_genTuple [IsTateRing A] [IsNoetherianRing A]
    (D : RationalLocData A) : Fin D.T.card → presheafValue D :=
  fun i => D.coeRingHom (divByS (↑(D.T.equivFin.symm i) : A) D.s)

omit [CompatiblePlusSubring A] in
set_option linter.unusedSectionVars false in
/-- Each rational generator `tᵢ/s` is power-bounded in `presheafValue D`: its powers lie in
the image of the bounded ring of definition `locSubring`
(`CompletionLocalization.coeRingHom_image_locSubring_isBounded`). Inlines the pure argument of
`relativeRationalLocData_generators_powerBounded` (no `LaurentNormalized`/`E` side conditions). -/
theorem example638_genTuple_isBounded [IsTateRing A] [IsNoetherianRing A]
    (D : RationalLocData A) (i : Fin D.T.card) :
    TopologicalRing.IsBounded
      (Set.range (example638_genTuple D i ^ · : ℕ → presheafValue D)) := by
  have hmem : divByS (↑(D.T.equivFin.symm i) : A) D.s ∈ locSubring D.P D.T D.s :=
    divByS_mem_locSubring D.P D.T D.s (D.T.equivFin.symm i).2
  have hbdd := CompletionLocalization.coeRingHom_image_locSubring_isBounded D
  apply hbdd.subset
  rintro _ ⟨n, rfl⟩
  exact ⟨(divByS (↑(D.T.equivFin.symm i) : A) D.s) ^ n, pow_mem hmem n, by
    rw [map_pow]; rfl⟩

omit [CompatiblePlusSubring A] in
set_option linter.unusedSectionVars false in
/-- The multivariate Example-6.38 evaluation hom
`C = A⟨X₁,…,Xₙ⟩ →+* presheafValue D`, `Xᵢ ↦ tᵢ/s`, `a ↦ canonicalMap a`
(`n = D.T.card`). Built from the general `mvEvalHomBounded` at the power-bounded rational
generators `example638_genTuple`. -/
noncomputable def example638_evalHom [IsTateRing A] [IsNoetherianRing A]
    (D : RationalLocData A) :
    (restrictedMvPowerSeriesSubring D.T.card A) →+* presheafValue D :=
  mvEvalHomBounded D.canonicalMap (canonicalMap_continuous D)
    (example638_genTuple D) (example638_genTuple_isBounded D)

omit [CompatiblePlusSubring A] in
set_option linter.unusedSectionVars false in
/-- `example638_evalHom` sends the constant series `algebraMap a ↦ canonicalMap a`. -/
theorem example638_evalHom_algebraMap [IsTateRing A] [IsNoetherianRing A]
    (D : RationalLocData A) (a : A) :
    example638_evalHom D (algebraMap A _ a) = D.canonicalMap a :=
  mvEvalHomBounded_algebraMap _ _ _ _ a

omit [CompatiblePlusSubring A] in
set_option linter.unusedSectionVars false in
/-- `example638_evalHom` sends the `j`-th variable `Xⱼ ↦ tⱼ/s` (the `j`-th rational generator). -/
theorem example638_evalHom_X [IsTateRing A] [IsNoetherianRing A]
    (D : RationalLocData A) (j : Fin D.T.card) :
    example638_evalHom D ⟨MvPowerSeries.X j, MvPowerSeries.X_isRestricted j⟩ =
      example638_genTuple D j :=
  mvEvalHomBounded_X _ _ _ _ j

omit [CompatiblePlusSubring A] in
set_option linter.unusedSectionVars false in
/-- **Density helper (faithful):** every `D.coeRingHom`-image of an element of the ring of
definition `locSubring D.P D.T D.s = A₀[t/s]` lies in the range of `example638_evalHom D`.

The two generating families of `locSubring` (Wedhorn §8.1) both lie in the range:
`algebraMap A₀`-images go to `D.canonicalMap a = example638_evalHom (algebraMap a)`
(`example638_evalHom_algebraMap`), and `divByS t D.s` (for `t ∈ D.T`) goes to the rational
generator `tᵢ/s = example638_evalHom Xᵢ` (`example638_evalHom_X` at the index
`D.T.equivFin ⟨t, _⟩`). Closure under the ring operations is automatic since the range of a ring
hom is a subring (`Subring.closure_induction`). NO topology on `A⟨X₁..Xₙ⟩` is used. -/
private theorem coeRingHom_locSubring_mem_range [IsTateRing A] [IsNoetherianRing A]
    (D : RationalLocData A) {x : Localization.Away D.s}
    (hx : x ∈ locSubring D.P D.T D.s) :
    D.coeRingHom x ∈ (example638_evalHom D).range := by
  classical
  refine Subring.closure_induction
    (p := fun x _ => D.coeRingHom x ∈ (example638_evalHom D).range)
    ?_ ?_ ?_ ?_ ?_ ?_ hx
  · -- generators: `algebraMap A₀` images and `divByS t s` for `t ∈ D.T`.
    rintro _ (⟨a, -, rfl⟩ | ⟨⟨t, ht⟩, rfl⟩)
    · -- `coeRingHom (algebraMap a) = canonicalMap a = example638_evalHom (algebraMap a)`.
      refine ⟨algebraMap A _ a, ?_⟩
      erw [example638_evalHom_algebraMap]; rfl
    · -- `coeRingHom (divByS t s) = example638_genTuple (equivFin ⟨t, ht⟩) = evalHom Xⱼ`.
      refine ⟨⟨MvPowerSeries.X (D.T.equivFin ⟨t, ht⟩),
        MvPowerSeries.X_isRestricted _⟩, ?_⟩
      erw [example638_evalHom_X]
      simp only [example638_genTuple, Equiv.symm_apply_apply]
  · -- 0
    exact ⟨0, by rw [map_zero, map_zero]⟩
  · -- 1
    rw [map_one]
    exact (example638_evalHom D).range.one_mem
  · -- add
    rintro x y - - ⟨px, hpx⟩ ⟨py, hpy⟩
    exact ⟨px + py, by rw [map_add, map_add, hpx, hpy]⟩
  · -- neg
    rintro x - ⟨px, hpx⟩
    exact ⟨-px, by rw [map_neg, map_neg, hpx]⟩
  · -- mul
    rintro x y - - ⟨px, hpx⟩ ⟨py, hpy⟩
    exact ⟨px * py, by rw [map_mul, map_mul, hpx, hpy]⟩

omit [CompatiblePlusSubring A] in
set_option linter.unusedSectionVars false in
/-- **`1/s = invS D` lies in the range of `example638_evalHom D`** — the linchpin density fact,
proved faithfully from the **Tate** hypothesis and the rational `hopen` datum (NO topology on
`A⟨X₁..Xₙ⟩`, NO `Σ tᵢ gᵢ = sᵏ` series).

Wedhorn (Example 6.38): `A[M]` is dense in `Â⟨T/s⟩`, where `M = {tᵢ/s}`; this is where `1/s`
enters, since `A` is Tate. Concretely: as `A` is Tate it has a topologically nilpotent unit `u`
(Definition 6.10); some power `uᵐ` lands in the image of `Iᴺ` (the `hopen` depth), so
`uᵐ = ↑b` for `b ∈ Iᴺ ⊆ A₀`. By `hopen`, `divByS (uᵐ) s ∈ locSubring = A₀[t/s]`, hence (via
`coeRingHom_locSubring_mem_range`) `D.coeRingHom (divByS (uᵐ) s) = D.canonicalMap (uᵐ) · invS`
lies in the range. Since `uᵐ` is a **unit** of `A`, `D.canonicalMap (uᵐ)` is invertible with
inverse `D.canonicalMap ((uᵐ)⁻¹) ∈ range`, so
`invS = D.canonicalMap ((uᵐ)⁻¹) · (D.canonicalMap (uᵐ) · invS)` lies in the range. -/
private theorem invS_mem_range [IsTateRing A] [IsNoetherianRing A] (D : RationalLocData A) :
    invS D ∈ (example638_evalHom D).range := by
  obtain ⟨u, hu⟩ := IsTateRing.exists_topologicallyNilpotent_unit (A := A)
  obtain ⟨N, hN⟩ := D.hopen
  -- The image of `Iᴺ` in `A` is a neighbourhood of `0`.
  have hmem : Subtype.val '' ((D.P.I ^ N : Ideal D.P.A₀) : Set D.P.A₀) ∈ nhds (0 : A) :=
    D.P.hasBasis_nhds_zero.mem_of_mem (i := N) trivial
  -- Some power `uᵐ` lands in that neighbourhood.
  obtain ⟨m, b, hbI, hbval⟩ := (hu.eventually hmem).exists
  -- `hbval : ↑b = (↑u)ᵐ`. By `hopen`, `divByS (↑b) s ∈ locSubring`.
  have hdiv : divByS (↑b : A) D.s ∈ locSubring D.P D.T D.s := hN b hbI
  have hrange_w : D.coeRingHom (divByS (↑b : A) D.s) ∈ (example638_evalHom D).range :=
    coeRingHom_locSubring_mem_range D hdiv
  -- `coeRingHom (divByS (↑b) s) = canonicalMap (↑b) · invS`.
  have hdivfac : divByS (↑b : A) D.s =
      algebraMap A (Localization.Away D.s) (↑b : A) * divByS 1 D.s := by
    rw [← IsLocalization.mk'_one (M := Submonoid.powers D.s) (S := Localization.Away D.s) (↑b : A)]
    unfold divByS
    rw [← IsLocalization.mk'_mul, mul_one, one_mul]
  have hcoe : D.coeRingHom (divByS (↑b : A) D.s) = D.canonicalMap (↑b : A) * invS D := by
    rw [hdivfac, map_mul, ← invS_eq_coeRingHom_divByS_one]; rfl
  -- `↑b = uᵐ` is a unit of `A`, so `canonicalMap (↑b)` is a unit; let `c := (↑b)⁻¹`.
  have hbunit : IsUnit (↑b : A) := by rw [hbval]; exact (u ^ m).isUnit
  set ub := hbunit.unit with hub
  -- `canonicalMap (↑ub⁻¹) ∈ range` and `canonicalMap (↑ub⁻¹) · canonicalMap (↑b) = 1`.
  have hinv_range : D.canonicalMap (↑ub⁻¹ : A) ∈ (example638_evalHom D).range :=
    ⟨algebraMap A _ (↑ub⁻¹ : A), example638_evalHom_algebraMap D (↑ub⁻¹ : A)⟩
  -- `invS = canonicalMap (↑ub⁻¹) · (canonicalMap (↑b) · invS)`.
  have hfinal : invS D = D.canonicalMap (↑ub⁻¹ : A) * D.coeRingHom (divByS (↑b : A) D.s) := by
    rw [hcoe, ← mul_assoc, ← map_mul]
    rw [show (↑ub⁻¹ : A) * (↑b : A) = 1 from by
      rw [hub]; exact Units.inv_mul_eq_one.mpr (by rw [IsUnit.unit_spec])]
    rw [map_one, one_mul]
  rw [hfinal]
  exact (example638_evalHom D).range.mul_mem hinv_range hrange_w

set_option linter.unusedSectionVars false in
/-- **The whole dense subring `range D.coeRingHom` lies in `range (example638_evalHom D)`.**
Every element of `Localization.Away D.s` is `a/sᵏ`, whose `coeRingHom`-image is
`D.canonicalMap a · (invS D)ᵏ`; both factors lie in the range (`example638_evalHom_algebraMap`
and `invS_mem_range`), so the product does. NO topology on `A⟨X₁..Xₙ⟩` is used. -/
private theorem coeRingHom_mem_range [IsTateRing A] [IsNoetherianRing A]
    (D : RationalLocData A) (y : Localization.Away D.s) :
    D.coeRingHom y ∈ (example638_evalHom D).range := by
  induction y using Localization.induction_on with
  | H p =>
    obtain ⟨a, sk, hk⟩ := p
    obtain ⟨k, rfl⟩ := hk
    -- `coeRingHom (mk a ⟨sᵏ, _⟩) = canonicalMap a · invSᵏ`.
    have hformula : D.coeRingHom (Localization.mk a ⟨D.s ^ k, k, rfl⟩) =
        D.canonicalMap a * (invS D) ^ k := by
      have key : D.coeRingHom (Localization.mk a ⟨D.s ^ k, k, rfl⟩) *
          (D.canonicalMap D.s) ^ k = D.canonicalMap a := by
        rw [← map_pow]
        change D.coeRingHom _ * D.coeRingHom _ = D.coeRingHom _
        rw [← map_mul]
        congr 1
        rw [← Localization.mk_one_eq_algebraMap, ← Localization.mk_one_eq_algebraMap,
          Localization.mk_mul, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
        exact ⟨1, by simp [mul_comm]⟩
      rw [← key, mul_assoc,
        show (D.canonicalMap D.s) ^ k * (invS D) ^ k = 1 from by
          rw [← mul_pow, canonicalMap_s_mul_invS, one_pow],
        mul_one]
    rw [hformula]
    exact (example638_evalHom D).range.mul_mem
      ⟨algebraMap A _ a, example638_evalHom_algebraMap D a⟩
      ((example638_evalHom D).range.pow_mem (invS_mem_range D) k)

set_option linter.unusedSectionVars false in
/-- **Density of the image (faithful):** `example638_evalHom D` has dense range.
`presheafValue D = Completion (Localization.Away D.s)`, in which `range D.coeRingHom` is dense
(`UniformSpace.Completion.denseRange_coe`); that dense subring is contained in
`range (example638_evalHom D)` (`coeRingHom_mem_range`), so the larger set is dense too. This is
Wedhorn's "`A[M]` dense in `Â⟨T/s⟩`" (Example 6.38). NO topology on `A⟨X₁..Xₙ⟩` is used. -/
private theorem example638_evalHom_denseRange [IsTateRing A] [IsNoetherianRing A]
    (D : RationalLocData A) : DenseRange (example638_evalHom D) := by
  letI : UniformSpace (Localization.Away D.s) := D.uniformSpace
  letI : IsUniformAddGroup (Localization.Away D.s) := D.isUniformAddGroup
  have hdense : DenseRange (D.coeRingHom : Localization.Away D.s → presheafValue D) := by
    change DenseRange (UniformSpace.Completion.coeRingHom :
      Localization.Away D.s → presheafValue D)
    exact UniformSpace.Completion.denseRange_coe
  -- `range coeRingHom ⊆ range example638_evalHom`, so the latter is dense too.
  refine hdense.mono ?_
  rintro _ ⟨y, rfl⟩
  exact coeRingHom_mem_range D y

/-! ### Example 6.38 — the completion-comparison isomorphism `presheafValue D ≃+* C ⧸ ker`

Wedhorn Example 6.38 (p. 56, `wedhorn.txt:2700`–`2707`): "Set `C = Â⟨X⟩`, `a = (t − sᵢXᵢ)`;
`C` noetherian ⟹ `a` closed (Prop 6.17); `A → Â⟨T/s⟩` and `A → C/a` satisfy the same universal
property ⟹ `C/a ≅ Â⟨T/s⟩`." We build the ring iso `presheafValue D ≃+* C ⧸ ker(example638_evalHom D)`
directly, mirroring the `n = 1` template (`presheafValueCanonicalQuotientEquiv_faithful`, this
file), but with the power-bounded multivariate generators `tᵢ/s` (so NO `hb : IsPowerBounded
(invS D)` whole-space hypothesis is needed) and the J-adic Tate topology `mvTateAlgebraTopology'`
from `MvTateAlgebraTopology.lean` (every ideal closed = Prop 6.17, faithful — no noeth-`A₀`). -/


omit [CompatiblePlusSubring A] in
set_option linter.unusedSectionVars false in
/-- **Forward continuity of the Example-6.38 evaluation map** (the "correct approach" of
`TateAlgebraWedhorn.lean:702`): `example638_evalHom D : C = A⟨X₁..Xₙ⟩ → presheafValue D` is
continuous for the **J-adic** Tate topology `mvTateAlgebraTopology' n` (which constrains ALL
coefficients simultaneously, unlike the product T-topology).

Wedhorn Example 6.38: `A[M]` (`M = {tᵢ/s}`) is dense in `Â⟨T/s⟩` and the evaluation is continuous
because `C`'s basic `0`-nbhd `mvTateAlgNhd n P k` (all coefficients in `P.Iᵏ`) maps into a `0`-nbhd
of `presheafValue D`: the product power range `R = {∏(tᵢ/s)^vᵢ}` is **bounded**
(`mvRangeProd_isBounded` via `example638_genTuple_isBounded`), so a `0`-nbhd `V` absorbs it
(`V·R ⊆ W`); `canonicalMap` is continuous, so `canonicalMap '' (P.Iᵏ) ⊆ V` for `k` large; hence
each evaluation term `canonicalMap(coeffᵥ h)·∏(tᵢ/s)^vᵢ ∈ V·R ⊆ W`, and the sum lands in the open
subgroup `W` by `tsum_mem_of_isOpen_addSubgroup`. -/
theorem example638_evalHom_continuous (D : RationalLocData A) :
    @Continuous _ _ (MvTateAlgebra.mvTateAlgebraTopology' D.T.card)
      (inferInstance : TopologicalSpace (presheafValue D)) (example638_evalHom D) := by
  classical
  set n := D.T.card with hn
  letI τC : TopologicalSpace ↥(restrictedMvPowerSeriesSubring n A) :=
    MvTateAlgebra.mvTateAlgebraTopology' n
  haveI hringC : @IsTopologicalRing _ τC _ :=
    MvTateAlgebra.mvTateAlgebraTopology'_isTopologicalRing n
  haveI haddC : @IsTopologicalAddGroup _ τC _ := IsTopologicalRing.to_topologicalAddGroup
  -- `presheafValue D` is a nonarchimedean topological ring.
  haveI hNA : NonarchimedeanRing (presheafValue D) := inferInstance
  -- Reduce to continuity at 0 (additive-group hom).
  refine continuous_of_continuousAt_zero (example638_evalHom D) ?_
  rw [ContinuousAt, map_zero, Filter.tendsto_def]
  intro S hS
  -- WLOG the target `0`-nbhd is an open subgroup `W ⊆ S`.
  obtain ⟨W, hWS⟩ := NonarchimedeanRing.is_nonarchimedean S hS
  -- The product power range `R` is bounded; absorb it into `W`.
  have hRbdd : TopologicalRing.IsBounded
      (Set.range (fun v : Fin n →₀ ℕ => ∏ i, example638_genTuple D i ^ (v i))) :=
    mvRangeProd_isBounded (example638_genTuple D) (example638_genTuple_isBounded D)
  obtain ⟨V, hV, hVR⟩ := hRbdd (W : Set (presheafValue D)) (W.isOpen.mem_nhds W.zero_mem)
  -- `canonicalMap⁻¹ V` is a `0`-nbhd of `A`, so contains `image(P.Iᵏ)` for some `k`.
  let P := (IsTateRing.principalPair A).toPairOfDefinition
  have hpre : (D.canonicalMap) ⁻¹' V ∈ nhds (0 : A) :=
    (canonicalMap_continuous D).continuousAt.preimage_mem_nhds (by rwa [map_zero])
  obtain ⟨k, -, hk⟩ := P.hasBasis_nhds_zero.mem_iff.mp hpre
  -- Target: `mvTateAlgNhd n P k` maps into `S` (via `W`).
  refine Filter.mem_of_superset
    ((MvTateAlgebra.mvTateAlgBasis' n).hasBasis_nhds_zero.mem_of_mem (i := k) trivial) ?_
  intro h hh
  apply hWS
  -- `example638_evalHom D h = ∑' v, mvEvalTerm ...`; each term lies in `W`.
  change (∑' v, mvEvalTerm D.canonicalMap (example638_genTuple D) h v) ∈ (W : Set _)
  refine tsum_mem_of_isOpen_addSubgroup
    (mvEvalTerm_summable D.canonicalMap (canonicalMap_continuous D)
      (example638_genTuple D) (example638_genTuple_isBounded D) h)
    W.isOpen (fun v => ?_)
  -- term `v`: `canonicalMap(coeffᵥ h) · ∏(tᵢ/s)^vᵢ`.
  change mvEvalTerm D.canonicalMap (example638_genTuple D) h v ∈ W
  obtain ⟨b, hbI, hbeq⟩ := MvTateAlgebra.mvTateAlgNhd_coeff_mem n P k hh v
  have hcoeffV : D.canonicalMap (MvPowerSeries.coeff v h.val) ∈ V := by
    rw [← hbeq]
    exact hk ⟨b, hbI, rfl⟩
  -- `term v = ∏(tᵢ/s)^vᵢ · canonicalMap(coeffᵥ h) ∈ R * V ⊆ W`.
  apply hVR
  rw [show mvEvalTerm D.canonicalMap (example638_genTuple D) h v =
      (∏ i, example638_genTuple D i ^ (v i)) *
        D.canonicalMap (MvPowerSeries.coeff v h.val) from by
    rw [mvEvalTerm]; ring]
  exact Set.mul_mem_mul ⟨v, rfl⟩ hcoeffV

omit [CompatiblePlusSubring A] in
/-- The quotient topology on `C ⧸ a` (`C = A⟨X₁..Xₙ⟩` with the J-adic Tate topology
`mvTateAlgebraTopology' n`) for an ideal `a`. -/
@[reducible] noncomputable def mvQuotTopology (n : ℕ)
    (a : Ideal ↥(restrictedMvPowerSeriesSubring n A)) :
    TopologicalSpace (↥(restrictedMvPowerSeriesSubring n A) ⧸ a) :=
  @topologicalRingQuotientTopology _ (MvTateAlgebra.mvTateAlgebraTopology' n) _ a

omit [CompatiblePlusSubring A] in
set_option linter.unusedSectionVars false in
theorem mvQuot_isTopologicalRing (n : ℕ)
    (a : Ideal ↥(restrictedMvPowerSeriesSubring n A)) :
    @IsTopologicalRing (↥(restrictedMvPowerSeriesSubring n A) ⧸ a) (mvQuotTopology n a) _ :=
  @topologicalRing_quotient _ (MvTateAlgebra.mvTateAlgebraTopology' n) _ a
    (MvTateAlgebra.mvTateAlgebraTopology'_isTopologicalRing n)

omit [CompatiblePlusSubring A] in
theorem mvQuot_isTopologicalAddGroup (n : ℕ)
    (a : Ideal ↥(restrictedMvPowerSeriesSubring n A)) :
    @IsTopologicalAddGroup (↥(restrictedMvPowerSeriesSubring n A) ⧸ a) (mvQuotTopology n a) _ :=
  @IsTopologicalRing.to_topologicalAddGroup _ _ (mvQuotTopology n a) (mvQuot_isTopologicalRing n a)

omit [CompatiblePlusSubring A] in
/-- The uniform space on the quotient `C ⧸ a` (right uniformity of the quotient Tate topology). -/
@[reducible] noncomputable def mvQuotUniformSpace (n : ℕ)
    (a : Ideal ↥(restrictedMvPowerSeriesSubring n A)) :
    UniformSpace (↥(restrictedMvPowerSeriesSubring n A) ⧸ a) :=
  @IsTopologicalAddGroup.rightUniformSpace _ _ (mvQuotTopology n a)
    (mvQuot_isTopologicalAddGroup n a)

omit [CompatiblePlusSubring A] in
set_option linter.unusedSectionVars false in
theorem mvQuot_isUniformAddGroup (n : ℕ)
    (a : Ideal ↥(restrictedMvPowerSeriesSubring n A)) :
    @IsUniformAddGroup (↥(restrictedMvPowerSeriesSubring n A) ⧸ a) (mvQuotUniformSpace n a) _ :=
  @isUniformAddGroup_of_addCommGroup _ _ (mvQuotTopology n a) (mvQuot_isTopologicalAddGroup n a)

omit [CompatiblePlusSubring A] in
set_option linter.unusedSectionVars false in
/-- **`C ⧸ a` is complete** (Step 1 of Example 6.38). `C = A⟨X₁..Xₙ⟩` is complete
(`mvTate_completeSpace`) and first-countable (countably-generated uniformity), so Bourbaki IX.3.1
Prop 4 (`QuotientAddGroup.completeSpace_right'`) makes the quotient complete (no closedness needed
for completeness as a uniform space; Hausdorffness is `mvQuot_t2Space`). -/
theorem mvQuot_completeSpace (n : ℕ)
    (a : Ideal ↥(restrictedMvPowerSeriesSubring n A))
    (hA_complete : @CompleteSpace A (IsTopologicalAddGroup.rightUniformSpace A)) :
    @CompleteSpace (↥(restrictedMvPowerSeriesSubring n A) ⧸ a) (mvQuotUniformSpace n a) := by
  letI τ : TopologicalSpace ↥(restrictedMvPowerSeriesSubring n A) :=
    MvTateAlgebra.mvTateAlgebraTopology' n
  haveI _hring : @IsTopologicalRing _ τ _ :=
    MvTateAlgebra.mvTateAlgebraTopology'_isTopologicalRing n
  haveI haddgrp : @IsTopologicalAddGroup _ τ _ := IsTopologicalRing.to_topologicalAddGroup
  letI uC : UniformSpace ↥(restrictedMvPowerSeriesSubring n A) :=
    MvTateAlgebra.mvTateUniformSpace n
  haveI : @IsUniformAddGroup _ uC _ := MvTateAlgebra.mvTate_isUniformAddGroup n
  haveI : (@uniformity _ uC).IsCountablyGenerated :=
    MvTateAlgebra.mvTate_uniformity_isCountablyGenerated n
  haveI : @FirstCountableTopology _ τ := UniformSpace.firstCountableTopology _
  haveI hCS : @CompleteSpace _ uC := MvTateAlgebra.mvTate_completeSpace n hA_complete
  exact @QuotientAddGroup.completeSpace_right' ↥(restrictedMvPowerSeriesSubring n A) _ τ haddgrp
    ‹_› a.toAddSubgroup inferInstance hCS

omit [CompatiblePlusSubring A] in
set_option linter.unusedSectionVars false in
/-- **`C ⧸ a` is T2** (Step 1 of Example 6.38), when `a` is closed — quotient of a topological
group by a closed normal subgroup. -/
theorem mvQuot_t2Space (n : ℕ)
    (a : Ideal ↥(restrictedMvPowerSeriesSubring n A))
    (ha : @IsClosed _ (MvTateAlgebra.mvTateAlgebraTopology' n)
      (a : Set ↥(restrictedMvPowerSeriesSubring n A))) :
    @T2Space (↥(restrictedMvPowerSeriesSubring n A) ⧸ a) (mvQuotTopology n a) := by
  letI τ : TopologicalSpace ↥(restrictedMvPowerSeriesSubring n A) :=
    MvTateAlgebra.mvTateAlgebraTopology' n
  haveI _hring : @IsTopologicalRing _ τ _ :=
    MvTateAlgebra.mvTateAlgebraTopology'_isTopologicalRing n
  haveI haddgrp : @IsTopologicalAddGroup _ τ _ := IsTopologicalRing.to_topologicalAddGroup
  haveI hac : @IsClosed _ τ (a.toAddSubgroup : Set ↥(restrictedMvPowerSeriesSubring n A)) := ha
  letI : TopologicalSpace (↥(restrictedMvPowerSeriesSubring n A) ⧸ a) := mvQuotTopology n a
  haveI : @IsTopologicalAddGroup _ (mvQuotTopology n a) _ := mvQuot_isTopologicalAddGroup n a
  haveI _h3 : @T3Space _ (mvQuotTopology n a) :=
    @QuotientAddGroup.instT3Space _ τ _ haddgrp a.toAddSubgroup inferInstance hac
  infer_instance

/-! #### Step 2 — the forward map `ē : C ⧸ ker → presheafValue D` -/

omit [CompatiblePlusSubring A] in
set_option linter.unusedSectionVars false in
/-- **The injective factorisation `ē : C ⧸ ker(example638_evalHom D) → presheafValue D`**
(Wedhorn Example 6.38: `C/a ↪ Â⟨T/s⟩`). Since `a = ker`, `RingHom.kerLift` factors
`example638_evalHom D` through the quotient and is automatically injective
(`RingHom.kerLift_injective`). -/
private noncomputable def example638_kerLift [IsTateRing A] [IsNoetherianRing A]
    (D : RationalLocData A) :
    (↥(restrictedMvPowerSeriesSubring D.T.card A) ⧸ RingHom.ker (example638_evalHom D)) →+*
      presheafValue D :=
  (example638_evalHom D).kerLift

omit [CompatiblePlusSubring A] in
set_option linter.unusedSectionVars false in
/-- `ē ∘ mk = example638_evalHom D` (`RingHom.kerLift_mk`). -/
private theorem example638_kerLift_mk [IsTateRing A] [IsNoetherianRing A]
    (D : RationalLocData A) (h : ↥(restrictedMvPowerSeriesSubring D.T.card A)) :
    example638_kerLift D (Ideal.Quotient.mk _ h) = example638_evalHom D h :=
  (example638_evalHom D).kerLift_mk h

omit [CompatiblePlusSubring A] in
set_option linter.unusedSectionVars false in
/-- `ē` is injective. -/
private theorem example638_kerLift_injective [IsTateRing A] [IsNoetherianRing A]
    (D : RationalLocData A) : Function.Injective (example638_kerLift D) :=
  (example638_evalHom D).kerLift_injective

omit [CompatiblePlusSubring A] in
set_option linter.unusedSectionVars false in
/-- **`ē` is continuous** for the quotient Tate topology on `C ⧸ ker`. The Example-6.38 evaluation
`example638_evalHom D` is continuous (`example638_evalHom_continuous`); `ē` is its factorisation
through the (open) quotient map `mk`, which is a quotient map, so `ē` is continuous by the universal
property of the quotient topology. -/
private theorem example638_kerLift_continuous (D : RationalLocData A) :
    @Continuous _ _ (mvQuotTopology D.T.card (RingHom.ker (example638_evalHom D)))
      (inferInstance : TopologicalSpace (presheafValue D)) (example638_kerLift D) := by
  set n := D.T.card with hn
  set a := RingHom.ker (example638_evalHom D) with ha
  letI τ : TopologicalSpace ↥(restrictedMvPowerSeriesSubring n A) :=
    MvTateAlgebra.mvTateAlgebraTopology' n
  haveI _hring : @IsTopologicalRing _ τ _ :=
    MvTateAlgebra.mvTateAlgebraTopology'_isTopologicalRing n
  letI τQ : TopologicalSpace (↥(restrictedMvPowerSeriesSubring n A) ⧸ a) := mvQuotTopology n a
  -- The quotient map `mk` is a quotient map; `ē ∘ mk = example638_evalHom` is continuous.
  rw [show (mvQuotTopology n a) = TopologicalSpace.coinduced (Ideal.Quotient.mk a) τ from rfl]
  rw [continuous_coinduced_dom]
  have : (example638_kerLift D) ∘ (Ideal.Quotient.mk a) = example638_evalHom D := by
    funext h; exact example638_kerLift_mk D h
  rw [this]
  exact example638_evalHom_continuous D

omit [CompatiblePlusSubring A] in
set_option linter.unusedSectionVars false in
/-- **`s` maps to a unit in `C ⧸ ker(example638_evalHom D)`** (the linchpin for inverting the
backward map). `ē(mk(algebraMap s)) = canonicalMap s`, which is a unit of `presheafValue D` with
inverse `invS = 1/s`; and `invS ∈ range(example638_evalHom D)` (`invS_mem_range`), say
`invS = example638_evalHom D c = ē(mk c)`. Then `ē(mk c · mk(algebraMap s)) = invS · canonicalMap s
= 1 = ē 1`, so by injectivity of `ē` the element `mk c` is the inverse of `mk(algebraMap s)`. -/
private theorem example638_isUnit_mk_s [IsTateRing A] [IsNoetherianRing A]
    (D : RationalLocData A) :
    IsUnit (Ideal.Quotient.mk (RingHom.ker (example638_evalHom D))
      (algebraMap A (restrictedMvPowerSeriesSubring D.T.card A) D.s)) := by
  obtain ⟨c, hc⟩ := invS_mem_range D
  rw [isUnit_iff_exists_inv]
  refine ⟨Ideal.Quotient.mk _ c, ?_⟩
  apply example638_kerLift_injective D
  rw [map_one, map_mul, example638_kerLift_mk, example638_kerLift_mk,
    example638_evalHom_algebraMap]
  -- `ē(mk c) = example638_evalHom c = invS`; goal: `canonicalMap s · invS = 1`.
  erw [hc]
  exact canonicalMap_s_mul_invS D

/-! #### Step 3 — the backward map `presheafValue D → C ⧸ ker` -/

omit [CompatiblePlusSubring A] in
set_option linter.unusedSectionVars false in
/-- **The localization lift `ψ : Localization.Away D.s → C ⧸ ker(example638_evalHom D)`** sending
`s ↦ unit` (Example 6.38, the algebraic core of the backward map). By the universal property of
localization (`IsLocalization.Away.lift`), using that `mk(algebraMap s)` is a unit
(`example638_isUnit_mk_s`). -/
private noncomputable def example638_locToQuot [IsTateRing A] [IsNoetherianRing A]
    (D : RationalLocData A) :
    Localization.Away D.s →+*
      (↥(restrictedMvPowerSeriesSubring D.T.card A) ⧸ RingHom.ker (example638_evalHom D)) :=
  IsLocalization.Away.lift (x := D.s)
    (g := (Ideal.Quotient.mk (RingHom.ker (example638_evalHom D))).comp
      (algebraMap A (restrictedMvPowerSeriesSubring D.T.card A)))
    (example638_isUnit_mk_s D)

omit [CompatiblePlusSubring A] in
set_option linter.unusedSectionVars false in
/-- `ψ` sends `algebraMap a ↦ mk(algebraMap a)`. -/
private theorem example638_locToQuot_algebraMap [IsTateRing A] [IsNoetherianRing A]
    (D : RationalLocData A) (a : A) :
    example638_locToQuot D (algebraMap A (Localization.Away D.s) a) =
      Ideal.Quotient.mk _ (algebraMap A (restrictedMvPowerSeriesSubring D.T.card A) a) := by
  rw [example638_locToQuot, IsLocalization.Away.lift_eq]
  rfl

omit [CompatiblePlusSubring A] in
set_option linter.unusedSectionVars false in
/-- **`ē ∘ ψ = coeRingHom`** (the round-trip on the localization), where `ē = example638_kerLift`.
Both are ring homs `Localization.Away D.s → presheafValue D` agreeing on `algebraMap`
(`ē(ψ(algebraMap a)) = ē(mk(algebraMap a)) = canonicalMap a = coeRingHom(algebraMap a)`), so they
agree everywhere by uniqueness of the localization lift. -/
private theorem example638_kerLift_comp_locToQuot [IsTateRing A] [IsNoetherianRing A]
    (D : RationalLocData A) :
    (example638_kerLift D).comp (example638_locToQuot D) = D.coeRingHom := by
  apply IsLocalization.ringHom_ext (Submonoid.powers D.s)
  ext a
  rw [RingHom.comp_assoc]
  simp only [RingHom.comp_apply]
  rw [example638_locToQuot_algebraMap, example638_kerLift_mk, example638_evalHom_algebraMap]
  rw [RationalLocData.canonicalMap, RationalLocData.coeRingHom]
  rfl

omit [CompatiblePlusSubring A] in
set_option linter.unusedSectionVars false in
/-- Pointwise form of `ē ∘ ψ = coeRingHom`. -/
private theorem example638_kerLift_locToQuot_apply [IsTateRing A] [IsNoetherianRing A]
    (D : RationalLocData A) (a : Localization.Away D.s) :
    example638_kerLift D (example638_locToQuot D a) = D.coeRingHom a :=
  RingHom.congr_fun (example638_kerLift_comp_locToQuot D) a

-- INFRASTRUCTURE (not in Wedhorn): an open continuous ring hom maps power-bounded elements to
-- power-bounded elements. (`{g(x)ⁿ} = g '' {xⁿ}`; for a `0`-nbhd `U`, `g⁻¹U` is a `0`-nbhd
-- absorbing `{xⁿ}` into some `V`, and `g '' V` is a `0`-nbhd with `{g(x)ⁿ} · g''V ⊆ U`.)
omit [CompatiblePlusSubring A] in
theorem isPowerBounded_map_of_isOpenMap {R S : Type*} [CommRing R] [TopologicalSpace R]
    [CommRing S] [TopologicalSpace S] [IsTopologicalRing S] (g : R →+* S) (hg : Continuous g)
    (hopen : IsOpenMap g) {x : R} (hx : TopologicalRing.IsPowerBounded x) :
    TopologicalRing.IsPowerBounded (g x) := by
  intro U hU
  have hUpre : g ⁻¹' U ∈ nhds (0 : R) := by
    have := hg.continuousAt (x := (0 : R)); rw [ContinuousAt, map_zero] at this; exact this hU
  obtain ⟨V, hV, hSV⟩ := hx (g ⁻¹' U) hUpre
  refine ⟨g '' V, by simpa using hopen.image_mem_nhds hV, ?_⟩
  rintro _ ⟨_, ⟨k, rfl⟩, _, ⟨w, hw, rfl⟩, rfl⟩
  -- `g(x)^k · g(w) = g(x^k · w) ∈ g(range(x^·) · V) ⊆ g(g⁻¹U) ⊆ U`.
  simp only
  rw [← map_pow, ← map_mul]
  have : x ^ k * w ∈ g ⁻¹' U := hSV (Set.mul_mem_mul ⟨k, rfl⟩ hw)
  simpa using this

omit [CompatiblePlusSubring A] in
/-- **`C ⧸ a` is nonarchimedean** for the quotient Tate topology — quotient of the nonarchimedean
`C = A⟨X₁..Xₙ⟩` (`mvTate_nonarchimedean`) by an ideal, via the open quotient map
(`QuotientRing.isOpenMap_coe`). -/
theorem mvQuot_nonarchimedean (n : ℕ)
    (a : Ideal ↥(restrictedMvPowerSeriesSubring n A)) :
    @NonarchimedeanRing (↥(restrictedMvPowerSeriesSubring n A) ⧸ a) _ (mvQuotTopology n a) := by
  letI τ : TopologicalSpace ↥(restrictedMvPowerSeriesSubring n A) :=
    MvTateAlgebra.mvTateAlgebraTopology' n
  haveI _hring : @IsTopologicalRing _ τ _ :=
    MvTateAlgebra.mvTateAlgebraTopology'_isTopologicalRing n
  haveI hNA : @NonarchimedeanRing _ _ τ := MvTateAlgebra.mvTate_nonarchimedean n
  letI τQ : TopologicalSpace (↥(restrictedMvPowerSeriesSubring n A) ⧸ a) := mvQuotTopology n a
  haveI : @IsTopologicalRing _ τQ _ := mvQuot_isTopologicalRing n a
  constructor
  intro U hU
  have hcont : @Continuous _ _ τ τQ (Ideal.Quotient.mk a) := continuous_quotient_mk'
  have hU' : (Ideal.Quotient.mk a) ⁻¹' (U : Set _) ∈ @nhds _ τ (0 : _) :=
    hcont.continuousAt.preimage_mem_nhds hU
  obtain ⟨V, hVU⟩ := @NonarchimedeanRing.is_nonarchimedean _ _ τ hNA _ hU'
  exact ⟨{
    toAddSubgroup := V.toAddSubgroup.map (Ideal.Quotient.mk a).toAddMonoidHom
    isOpen' := @QuotientRing.isOpenMap_coe _ τ _ a _hring _ V.isOpen
  }, fun x hx => by obtain ⟨y, hy, rfl⟩ := hx; exact hVU hy⟩

omit [CompatiblePlusSubring A] in
set_option linter.unusedSectionVars false in
/-- `ψ(tᵢ/s) = mk(Xᵢ)`: the localization lift sends the rational generator `tᵢ/s` to the class of
the `i`-th variable. From injectivity of `ē`: `ē(ψ(tᵢ/s)) = coeRingHom(tᵢ/s) = tᵢ/s` (by
`example638_kerLift_locToQuot_apply`) and `ē(mk Xᵢ) = example638_evalHom Xᵢ = tᵢ/s` (by
`example638_kerLift_mk` + `example638_evalHom_X`). -/
private theorem example638_locToQuot_divByS [IsTateRing A] [IsNoetherianRing A]
    (D : RationalLocData A) (i : Fin D.T.card) :
    example638_locToQuot D (divByS (↑(D.T.equivFin.symm i) : A) D.s) =
      Ideal.Quotient.mk _ (⟨MvPowerSeries.X i, MvPowerSeries.X_isRestricted i⟩ :
        ↥(restrictedMvPowerSeriesSubring D.T.card A)) := by
  apply example638_kerLift_injective D
  rw [example638_kerLift_locToQuot_apply, example638_kerLift_mk, example638_evalHom_X]
  -- both sides = `tᵢ/s = coeRingHom(divByS ..) = example638_genTuple D i`.
  rw [example638_genTuple]

omit [CompatiblePlusSubring A] in
/-- **Continuity of the localization lift `ψ`** for the localization topology `D.topology` on
`Localization.Away D.s` and the quotient Tate topology on `C ⧸ ker` (Wedhorn Example 6.38: `A[M]`
dense in `Â⟨T/s⟩`, multivariate analogue of `locToQuotientOneSubfX_gen_continuous_canonical`).

The localization `0`-nbhd `locNhd k = image((I·D)^k)` maps into the `C ⧸ ker` `0`-nbhd
`mk(mvTateAlgNhd k)`: `ψ` carries the ring of definition `locSubring = A₀[t/s]` into
`mk(A₀⟨X⟩) = mk(mvPairSubring)` (via `ψ(algebraMap a₀) = mk(algebraMap a₀)` and `ψ(tᵢ/s) = mk(Xᵢ)`,
the latter from injectivity of `ē` since `ē(mk Xᵢ) = tᵢ/s = ē(ψ(tᵢ/s))`), and the ideal of
definition `locIdeal = I·D` into `mk(mvPairIdeal) = mk(I·A₀⟨X⟩)`; raising to the `k`-th power,
`ψ(locNhd k) ⊆ mk(mvTateAlgNhd k)`. Since `mk` is an open map, `mk(mvTateAlgNhd k)` is a `0`-nbhd. -/
private theorem example638_locToQuot_continuous (D : RationalLocData A) :
    @Continuous _ _ D.topology (mvQuotTopology D.T.card (RingHom.ker (example638_evalHom D)))
      (example638_locToQuot D) := by
  set n := D.T.card with hn
  set a := RingHom.ker (example638_evalHom D) with ha
  -- Install the quotient Tate topology + ring/nonarch instances on `B := C ⧸ a`.
  letI τC : TopologicalSpace ↥(restrictedMvPowerSeriesSubring n A) :=
    MvTateAlgebra.mvTateAlgebraTopology' n
  haveI _hringC : @IsTopologicalRing _ τC _ :=
    MvTateAlgebra.mvTateAlgebraTopology'_isTopologicalRing n
  letI τQ : TopologicalSpace (↥(restrictedMvPowerSeriesSubring n A) ⧸ a) := mvQuotTopology n a
  haveI hringQ : @IsTopologicalRing _ τQ _ := mvQuot_isTopologicalRing n a
  haveI hNAQ : @NonarchimedeanRing _ _ τQ := mvQuot_nonarchimedean n a
  -- `D.topology = locTopology D.P D.T D.s D.hopen` (reducible). Apply the lift criterion.
  change @Continuous _ _ (locTopology D.P D.T D.s D.hopen) τQ (example638_locToQuot D)
  refine locTopology_continuous_lift D.P D.T D.s D.hopen (example638_locToQuot D) ?_ ?_
  · -- (a) `ψ ∘ algebraMap = mk ∘ algebraMap_C` is continuous.
    have heq : (example638_locToQuot D).comp (algebraMap A (Localization.Away D.s)) =
        (Ideal.Quotient.mk a).comp
          (algebraMap A (restrictedMvPowerSeriesSubring n A)) := by
      ext x
      simp only [RingHom.comp_apply]
      rw [example638_locToQuot_algebraMap]
    rw [heq]
    exact (continuous_quotient_mk'.comp (MvTateAlgebra.mvTateAlgebra_algebraMap_continuous n))
  · -- (b) `ψ(divByS t s) = mk(Xᵢ)` is power-bounded in `C ⧸ a`.
    intro t ht
    -- Rewrite `t` as the `D.T.equivFin`-indexed generator and apply `example638_locToQuot_divByS`.
    set i := D.T.equivFin ⟨t, ht⟩ with hi
    have htval : t = (↑(D.T.equivFin.symm i) : A) := by
      rw [hi, Equiv.symm_apply_apply]
    rw [htval, example638_locToQuot_divByS D i]
    -- `Xᵢ` is power-bounded in `C` (it lies in the ring of definition `mvPairSubring`); the open
    -- continuous quotient map `mk` then makes `mk Xᵢ` power-bounded in `C ⧸ a`.
    have hXi_mem : (⟨MvPowerSeries.X i, MvPowerSeries.X_isRestricted i⟩ :
        ↥(restrictedMvPowerSeriesSubring n A)) ∈
        MvTateAlgebra.mvPairSubring n (IsTateRing.principalPair A).toPairOfDefinition := by
      classical
      intro l
      change MvPowerSeries.coeff l (MvPowerSeries.X i) ∈ _
      rw [MvPowerSeries.coeff_X]
      split
      · exact (IsTateRing.principalPair A).toPairOfDefinition.A₀.one_mem
      · exact (IsTateRing.principalPair A).toPairOfDefinition.A₀.zero_mem
    have hXi_pb : @TopologicalRing.IsPowerBounded _ _ τC
        (⟨MvPowerSeries.X i, MvPowerSeries.X_isRestricted i⟩ :
          ↥(restrictedMvPowerSeriesSubring n A)) :=
      (MvTateAlgebra.mvTateAlgebra_pairOfDefinition n).mem_powerBoundedSubring hXi_mem
    -- Transport power-boundedness through the open continuous quotient map `mk`.
    exact @isPowerBounded_map_of_isOpenMap _ _ _ τC _ τQ hringQ (Ideal.Quotient.mk a)
      continuous_quotient_mk' (@QuotientRing.isOpenMap_coe _ τC _ a _hringC) _ hXi_pb

omit [CompatiblePlusSubring A] in
/-- The backward map `presheafValue D →+* C ⧸ ker(example638_evalHom D)`, extending the continuous
localization lift `ψ` to the completion `presheafValue D` (target complete + Hausdorff from
`mvQuot_completeSpace` / `mvQuot_t2Space`, using `ker` closed by Prop 6.17). -/
private noncomputable def example638_quotBackward (D : RationalLocData A)
    (hA_complete : @CompleteSpace A (IsTopologicalAddGroup.rightUniformSpace A))
    (hker : @IsClosed _ (MvTateAlgebra.mvTateAlgebraTopology' D.T.card)
      ((RingHom.ker (example638_evalHom D) :
        Ideal ↥(restrictedMvPowerSeriesSubring D.T.card A)) :
        Set ↥(restrictedMvPowerSeriesSubring D.T.card A))) :
    presheafValue D →+*
      (↥(restrictedMvPowerSeriesSubring D.T.card A) ⧸ RingHom.ker (example638_evalHom D)) := by
  set n := D.T.card
  set a := RingHom.ker (example638_evalHom D)
  letI : UniformSpace (Localization.Away D.s) := D.uniformSpace
  letI : IsTopologicalRing (Localization.Away D.s) := D.isTopologicalRing
  letI : IsUniformAddGroup (Localization.Away D.s) := D.isUniformAddGroup
  letI τQ : TopologicalSpace (↥(restrictedMvPowerSeriesSubring n A) ⧸ a) := mvQuotTopology n a
  letI uQ : UniformSpace (↥(restrictedMvPowerSeriesSubring n A) ⧸ a) := mvQuotUniformSpace n a
  haveI : @IsTopologicalRing _ τQ _ := mvQuot_isTopologicalRing n a
  haveI : @IsUniformAddGroup _ uQ _ := mvQuot_isUniformAddGroup n a
  haveI : @CompleteSpace _ uQ := mvQuot_completeSpace n a hA_complete
  haveI hT2 : @T2Space _ τQ := mvQuot_t2Space n a hker
  haveI : @T0Space _ τQ := @T1Space.t0Space _ τQ (@T2Space.t1Space _ τQ hT2)
  exact @UniformSpace.Completion.extensionHom (Localization.Away D.s) _ D.uniformSpace _ _
    (↥(restrictedMvPowerSeriesSubring n A) ⧸ a) uQ _ (mvQuot_isUniformAddGroup n a)
    (mvQuot_isTopologicalRing n a) (example638_locToQuot D)
    (example638_locToQuot_continuous D) ‹_› ‹_›

omit [CompatiblePlusSubring A] in
set_option linter.unusedSectionVars false in
/-- The backward map agrees with `ψ` on the dense localization image `coeRingHom a`. -/
private theorem example638_quotBackward_coe (D : RationalLocData A)
    (hA_complete : @CompleteSpace A (IsTopologicalAddGroup.rightUniformSpace A))
    (hker : @IsClosed _ (MvTateAlgebra.mvTateAlgebraTopology' D.T.card)
      ((RingHom.ker (example638_evalHom D) :
        Ideal ↥(restrictedMvPowerSeriesSubring D.T.card A)) :
        Set ↥(restrictedMvPowerSeriesSubring D.T.card A)))
    (a : Localization.Away D.s) :
    example638_quotBackward D hA_complete hker (D.coeRingHom a) = example638_locToQuot D a := by
  set n := D.T.card
  set ak := RingHom.ker (example638_evalHom D)
  letI : UniformSpace (Localization.Away D.s) := D.uniformSpace
  letI : IsTopologicalRing (Localization.Away D.s) := D.isTopologicalRing
  letI : IsUniformAddGroup (Localization.Away D.s) := D.isUniformAddGroup
  letI τQ : TopologicalSpace (↥(restrictedMvPowerSeriesSubring n A) ⧸ ak) :=
    mvQuotTopology n ak
  letI uQ : UniformSpace (↥(restrictedMvPowerSeriesSubring n A) ⧸ ak) := mvQuotUniformSpace n ak
  haveI : @IsTopologicalRing _ τQ _ := mvQuot_isTopologicalRing n ak
  haveI : @IsUniformAddGroup _ uQ _ := mvQuot_isUniformAddGroup n ak
  haveI : @CompleteSpace _ uQ := mvQuot_completeSpace n ak hA_complete
  haveI hT2 : @T2Space _ τQ := mvQuot_t2Space n ak hker
  haveI : @T0Space _ τQ := @T1Space.t0Space _ τQ (@T2Space.t1Space _ τQ hT2)
  exact @UniformSpace.Completion.extensionHom_coe (Localization.Away D.s) _ D.uniformSpace _ _
    (↥(restrictedMvPowerSeriesSubring n A) ⧸ ak) uQ _ (mvQuot_isUniformAddGroup n ak)
    (mvQuot_isTopologicalRing n ak) (example638_locToQuot D)
    (example638_locToQuot_continuous D) ‹_› ‹_› a

omit [CompatiblePlusSubring A] in
set_option linter.unusedSectionVars false in
/-- Continuity of the backward map (`Completion.continuous_extension`). -/
private theorem example638_quotBackward_continuous (D : RationalLocData A)
    (hA_complete : @CompleteSpace A (IsTopologicalAddGroup.rightUniformSpace A))
    (hker : @IsClosed _ (MvTateAlgebra.mvTateAlgebraTopology' D.T.card)
      ((RingHom.ker (example638_evalHom D) :
        Ideal ↥(restrictedMvPowerSeriesSubring D.T.card A)) :
        Set ↥(restrictedMvPowerSeriesSubring D.T.card A))) :
    @Continuous _ _ (inferInstance : TopologicalSpace (presheafValue D))
      (mvQuotTopology D.T.card (RingHom.ker (example638_evalHom D)))
      (example638_quotBackward D hA_complete hker) := by
  set n := D.T.card
  set ak := RingHom.ker (example638_evalHom D)
  letI uQ : UniformSpace (↥(restrictedMvPowerSeriesSubring n A) ⧸ ak) := mvQuotUniformSpace n ak
  haveI : @CompleteSpace _ uQ := mvQuot_completeSpace n ak hA_complete
  exact @UniformSpace.Completion.continuous_extension (Localization.Away D.s) D.uniformSpace _ uQ
    (↑(example638_locToQuot D)) ‹_›

omit [CompatiblePlusSubring A] in
/-- **Round-trip `ē ∘ backward = id` on `presheafValue D`** (Wedhorn Example 6.38). Both
`ē ∘ backward` and `id` are continuous (`example638_kerLift_continuous`, `example638_quotBackward_continuous`)
and agree on the dense image `coeRingHom a`: `ē(backward(coeRingHom a)) = ē(ψ a) = coeRingHom a`
(`example638_quotBackward_coe` + `example638_kerLift_locToQuot_apply`). By `Completion.ext'` they
agree everywhere — so `ē` is **surjective** (every `x = ē(backward x)`). -/
private theorem example638_kerLift_comp_backward (D : RationalLocData A)
    (hA_complete : @CompleteSpace A (IsTopologicalAddGroup.rightUniformSpace A))
    (hker : @IsClosed _ (MvTateAlgebra.mvTateAlgebraTopology' D.T.card)
      ((RingHom.ker (example638_evalHom D) :
        Ideal ↥(restrictedMvPowerSeriesSubring D.T.card A)) :
        Set ↥(restrictedMvPowerSeriesSubring D.T.card A)))
    (x : presheafValue D) :
    example638_kerLift D (example638_quotBackward D hA_complete hker x) = x := by
  set n := D.T.card
  set ak := RingHom.ker (example638_evalHom D)
  letI : UniformSpace (Localization.Away D.s) := D.uniformSpace
  letI : IsTopologicalRing (Localization.Away D.s) := D.isTopologicalRing
  letI : IsUniformAddGroup (Localization.Away D.s) := D.isUniformAddGroup
  letI τQ : TopologicalSpace (↥(restrictedMvPowerSeriesSubring n A) ⧸ ak) :=
    mvQuotTopology n ak
  -- `ē ∘ backward` is continuous; agree with `id` on the dense image of `coeRingHom`.
  have hcont : @Continuous (presheafValue D) (presheafValue D) _ _
      (fun x => example638_kerLift D (example638_quotBackward D hA_complete hker x)) :=
    (example638_kerLift_continuous D).comp (example638_quotBackward_continuous D hA_complete hker)
  refine @UniformSpace.Completion.ext' (Localization.Away D.s) D.uniformSpace
    (presheafValue D) _ _ _ _ hcont continuous_id ?_ x
  intro a
  simp only [Function.comp, id]
  change example638_kerLift D (example638_quotBackward D hA_complete hker (D.coeRingHom a)) =
    D.coeRingHom a
  rw [example638_quotBackward_coe D hA_complete hker a, example638_kerLift_locToQuot_apply]

omit [CompatiblePlusSubring A] in
set_option linter.unusedSectionVars false in
/-- **Example 6.38 surjectivity** (Wedhorn p. 56, `wedhorn.txt:2693`–`2707`). The multivariate
evaluation `example638_evalHom : A⟨X₁,…,Xₙ⟩ → presheafValue D`, `Xᵢ ↦ tᵢ/s`, is **surjective** onto
`presheafValue D = Â⟨T/s⟩`.

Proved via the **completion-comparison isomorphism** (Wedhorn's "`Â⟨T/s⟩ = C/a`"): `ker` is closed
by Prop 6.17 (`MvTateAlgebra.mvTate_isClosed_ideal`, faithful — no noeth-`A₀`), so `C ⧸ ker` is
complete + Hausdorff; the backward completion-extension `presheafValue D → C ⧸ ker` is a right
inverse of the injective factorisation `ē : C ⧸ ker ↪ presheafValue D`
(`example638_kerLift_comp_backward`), so `ē` is surjective; since
`example638_evalHom = ē ∘ (Ideal.Quotient.mk ker)` and `mk` is surjective, so is
`example638_evalHom`. -/
theorem example638_evalHom_surjective [IsTateRing A] [IsNoetherianRing A] [IsStronglyNoetherian A]
    (D : RationalLocData A) : Function.Surjective (example638_evalHom D) := by
  letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A
  haveI hAc : @CompleteSpace A (IsTopologicalAddGroup.rightUniformSpace A) := ‹_›
  -- Prop 6.17: `ker(example638_evalHom D)` is closed in `C = A⟨X₁..Xₙ⟩`.
  have hker : @IsClosed _ (MvTateAlgebra.mvTateAlgebraTopology' D.T.card)
      ((RingHom.ker (example638_evalHom D) :
        Ideal ↥(restrictedMvPowerSeriesSubring D.T.card A)) :
        Set ↥(restrictedMvPowerSeriesSubring D.T.card A)) :=
    MvTateAlgebra.mvTate_isClosed_ideal D.T.card hAc (RingHom.ker (example638_evalHom D))
  -- `ē` is surjective (right-inverted by the backward map).
  have hē_surj : Function.Surjective (example638_kerLift D) := fun x =>
    ⟨example638_quotBackward D hAc hker x, example638_kerLift_comp_backward D hAc hker x⟩
  -- `example638_evalHom = ē ∘ mk`, both surjective.
  intro y
  obtain ⟨q, hq⟩ := hē_surj y
  obtain ⟨h, rfl⟩ := Ideal.Quotient.mk_surjective q
  exact ⟨h, by rw [← example638_kerLift_mk]; exact hq⟩

set_option linter.unusedSectionVars false in
omit [CompatiblePlusSubring A] in
/-- **PROVEN — Example 6.38, multivariate presentation** (Wedhorn p. 56,
`wedhorn.txt:2693`–`2707`). For a strongly noetherian Tate ring `A` and a rational locale
`D = R(T/s)` with `|D.T| = n`, the canonical ring homomorphism

  `C := A⟨X₁, …, Xₙ⟩ = restrictedMvPowerSeriesSubring n A  ⟶  presheafValue D = Â⟨T/s⟩`,
  `Xᵢ ↦ tᵢ/s`

is **surjective** (Wedhorn: `Â⟨T/s⟩ = C/a`, `a = (t − s·Xₜ)` — a *quotient* of `C`, so the
composite `C ↠ C/a ≅ presheafValue D` is onto). This is the **minimal** Example-6.38 content
needed for faithful noetherianness: it does NOT require the full ring iso, only the surjection,
because `IsNoetherianRing` transfers along surjections from a noetherian source
(`isNoetherianRing_of_surjective`), and `C = restrictedMvPowerSeriesSubring n A` is noetherian by
`IsStronglyNoetherian.isNoetherianRing_restricted n` (NO `pairSubring`/`A₀⟨X⟩` noetherianness, NO
noeth-`A₀` — the faithful case-(b) source of noetherianness).

**This is PROVEN** — `#print axioms` clean (`{propext, Classical.choice, Quot.sound}`, verified
2026-06-05). The general `Fin n` evaluation map IS in the repo: `mvEvalHomBounded` (`Wedhorn828:996`,
any continuous base map `g : R →+* S` + bounded tuple `b : Fin n → S`), instantiated as
`example638_evalHom` (`Xᵢ ↦ tᵢ/s`). Its surjectivity onto the completion `presheafValue D` is
`example638_evalHom_surjective`, via the completion-comparison route: Prop 6.17
(`MvTateAlgebra.mvTate_isClosed_ideal`, faithful — no noeth-`A₀`) closes `ker`, so `C ⧸ ker` is
complete + Hausdorff, and the backward completion-extension `example638_quotBackward` right-inverts
the injective factorisation `ē : C ⧸ ker ↪ presheafValue D`. NOTE: an earlier version of this
docstring wrongly described this as a "documented repo gap / genuinely absent" — it had since been
built and is sorry-free, so `presheafValue` noetherianness (`presheafValue_isNoetherianRing_faithful`)
is genuinely complete. (The general-`Fin n` summability + nonarchimedean Cauchy product live in the
`mvEvalHomBounded` development; this lemma just packages the surjection.)

**Why the univariate equiv does not suffice.** `presheafValueCanonicalQuotientEquiv_faithful`
models `presheafValue D ≃+* A⟨X⟩/(1 − sX)` with `X ↦ invS = 1/s`, which needs `invS` power-bounded
(`hb`); that holds only for `1 ∈ T`-type data (e.g. the whole space, discharged in
`presheafValue_globalLocData_isNoetherianRing`), NOT for a general `R(T/s)` where `1/s` is not
power-bounded. The Wedhorn-faithful presentation for general `D` is the multivariate one above with
`Xᵢ ↦ tᵢ/s` (power-bounded on the rational subset). Reducing general `D` to the whole space by
localization is invalid (`restrictionMapHom_surj`, deprecated FALSE-in-general,
`PresheafTateStructure.lean`). -/
private theorem example638_multivariate_surjection
    [IsTateRing A] [IsNoetherianRing A] [IsStronglyNoetherian A] (D : RationalLocData A) :
    ∃ φ : (restrictedMvPowerSeriesSubring D.T.card A) →+* presheafValue D,
      Function.Surjective φ :=
  ⟨example638_evalHom D, example638_evalHom_surjective D⟩

omit [CompatiblePlusSubring A] in
/-- **Step 1 of Prop 8.30 — Example 6.38, noetherian part** (Wedhorn p. 81, `wedhorn.txt:4099`).
`B := presheafValue D` is a **noetherian** ring. FAITHFUL: depends only on the ambient `A`-bundle
and `D` — **no** `PairOfDefinition A`, **no** `[IsNoetherianRing P.A₀]`.

Body is sorry-free: noetherianness is transferred along the multivariate Example-6.38 surjection
`C = A⟨X₁..Xₙ⟩ ↠ presheafValue D` (`isNoetherianRing_of_surjective`) from the noetherian source
`C = restrictedMvPowerSeriesSubring D.T.card A` (`IsStronglyNoetherian.isNoetherianRing_restricted`,
case (b)). The single genuine residual — the surjection itself — is isolated in
`example638_multivariate_surjection`; see its docstring for the precise repo gap (the general
`Fin n` restricted-power-series evaluation map, present only for `Fin 1`/`Fin 2`). -/
private theorem presheafValue_isNoetherianRing_residual
    [IsTateRing A] [IsNoetherianRing A] [IsStronglyNoetherian A] (D : RationalLocData A) :
    IsNoetherianRing (presheafValue D) := by
  -- The source `C = A⟨X₁..Xₙ⟩` is noetherian (case-(b): strongly noetherian `A`).
  haveI hC : IsNoetherianRing (restrictedMvPowerSeriesSubring D.T.card A) :=
    IsStronglyNoetherian.isNoetherianRing_restricted (A := A) D.T.card
  -- Example 6.38 (multivariate): `C ↠ presheafValue D` with `Xᵢ ↦ tᵢ/s` (now sorry-free via the
  -- completion-comparison iso). Noetherianness transfers along this surjection from `C`.
  obtain ⟨φ, hφ⟩ := example638_multivariate_surjection D
  exact isNoetherianRing_of_surjective _ _ φ hφ

omit [CompatiblePlusSubring A] in
theorem presheafValue_isNoetherianRing_faithful
    [IsTateRing A] [IsNoetherianRing A] [IsStronglyNoetherian A] (D : RationalLocData A) :
    IsNoetherianRing (presheafValue D) :=
  presheafValue_isNoetherianRing_residual D

-- Large unified proof: the relative Example-6.38 surjection bundles three nonarchimedean
-- nbhd-basis chases (`hUnitS`, `hi_dense`, `hf_unif`) over the heavy reducible quotient-Tate
-- uniform structures on `γ = C ⧸ ker Ψ`; the cumulative `isDefEq`/`whnf` cost exceeds the default
-- heartbeat budget even though each step is elementary.
set_option maxHeartbeats 1600000 in
omit [CompatiblePlusSubring A] in
/-- **Relative Example 6.38 surjection** (the genuine residual for strong-noetherian propagation).
For `n = |D.T|` and any `m : ℕ`, the `(n+m)`-variable restricted power series over `A` surject
onto the `m`-variable restricted power series over `B := presheafValue D`, via `Xᵢ ↦ tᵢ/s` (`i < n`)
and `Xₙ₊ⱼ ↦ Yⱼ` (the free polydisc variables). This is the relative analogue of
`example638_evalHom_surjective` with target `B⟨Y₁..Yₘ⟩ = restrictedMvPowerSeriesSubring m B` instead
of `B`. The *map* `φ` is straightforward (`mvEvalHomBounded` at `n+m` variables; the source
`restrictedMvPowerSeriesSubring (n+m) A` is noetherian directly from `A`'s strong-noetherianity, NO
Fubini). **The content is the SURJECTIVITY**, proved via the backward (right-inverse) map. Since the
relative target `B⟨Y⟩ = restrictedMvPowerSeriesSubring m B` is NOT presented as a
`UniformSpace.Completion`, the `example638_*` template's `UniformSpace.Completion.extensionHom`
does not directly apply; instead the backward map is built with `IsDenseInducing.extendRingHom`.
Concretely: `ker Ψ` is closed (Prop 6.17 over strongly-noetherian `A`), so `γ := source ⧸ ker Ψ`
is a complete Hausdorff topological ring; the polynomial ring `U := (Localization.Away D.s)[Y]`
maps densely into `B⟨Y⟩` by `iU` (coefficients via `coeRingHom`, the `Yⱼ` to the unit-disc
variables) and into `γ` by `fU` (coefficients via the localization lift `ψγ`, the `Yⱼ` to
`mk(Zₙ₊ⱼ)`); giving `U` the pullback uniformity makes `iU` uniform-inducing, `fU` is uniformly
continuous, and `IsDenseInducing.extendRingHom` extends `fU` to `backward : B⟨Y⟩ →+* γ`. The
round-trip `kerLift Ψ ∘ backward = id` (they agree on the dense `range iU` and are continuous)
right-inverts the injective `kerLift Ψ`, so `Ψ` is surjective. This realises the FAITHFUL Wedhorn
route — `A → B` is topologically of finite type and t.f.t. over strongly-noetherian is
strongly-noetherian (Remark 6.37(1) + Example 6.32(2), Wedhorn §6.6/§6.7) — *directly* at the
`(n+m)`-variable target (the source `restrictedMvPowerSeriesSubring (n+m) A` is noetherian straight
from `A`'s strong-noetherianity, NO Fubini, NO Prop 6.33 composition). Axiom-clean (no `sorry`).
Wedhorn Example 6.38, p. 56
(`wedhorn.txt:2693`–`2707`), the "in particular ... again strongly noetherian" clause. -/
private theorem presheafValue_mvRestricted_surjection
    [IsTateRing A] [IsNoetherianRing A] [IsStronglyNoetherian A]
    (D : RationalLocData A) (m : ℕ) :
    ∃ φ : (restrictedMvPowerSeriesSubring (D.T.card + m) A) →+*
            (restrictedMvPowerSeriesSubring m (presheafValue D)),
      Function.Surjective φ := by
  classical
  haveI hTate : IsTateRing (presheafValue D) := presheafValue_isTateRing_faithful D
  haveI hT2 : T2Space (presheafValue D) := inferInstance
  have hComplete : @CompleteSpace (presheafValue D)
      (IsTopologicalAddGroup.rightUniformSpace (presheafValue D)) :=
    presheafValue_completeSpace_rightUniformSpace D
  letI τT : TopologicalSpace (restrictedMvPowerSeriesSubring m (presheafValue D)) :=
    MvTateAlgebra.mvTateAlgebraTopology' m
  haveI hringT : IsTopologicalRing (restrictedMvPowerSeriesSubring m (presheafValue D)) :=
    MvTateAlgebra.mvTateAlgebraTopology'_isTopologicalRing m
  letI uT : UniformSpace (restrictedMvPowerSeriesSubring m (presheafValue D)) :=
    MvTateAlgebra.mvTateUniformSpace m
  haveI : IsUniformAddGroup (restrictedMvPowerSeriesSubring m (presheafValue D)) :=
    MvTateAlgebra.mvTate_isUniformAddGroup m
  haveI : CompleteSpace (restrictedMvPowerSeriesSubring m (presheafValue D)) :=
    MvTateAlgebra.mvTate_completeSpace m hComplete
  haveI : NonarchimedeanRing (restrictedMvPowerSeriesSubring m (presheafValue D)) :=
    MvTateAlgebra.mvTate_nonarchimedean m
  haveI : T2Space (restrictedMvPowerSeriesSubring m (presheafValue D)) :=
    MvTateAlgebra.mvTate_t2Space m
  haveI : T0Space (restrictedMvPowerSeriesSubring m (presheafValue D)) := inferInstance
  -- base map `g = algebraMap ∘ canonicalMap : A → (presheafValue D)⟨Y⟩`, continuous
  let g : A →+* restrictedMvPowerSeriesSubring m (presheafValue D) :=
    (algebraMap (presheafValue D) (restrictedMvPowerSeriesSubring m (presheafValue D))).comp
      D.canonicalMap
  have hg : Continuous g :=
    (MvTateAlgebra.mvTateAlgebra_algebraMap_continuous (A := presheafValue D) m).comp
      (canonicalMap_continuous D)
  -- tuple `b : Fin (n+m) → T`: first `n` are `algebraMap (tᵢ/s)`, last `m` are the variables `Yⱼ`
  let b : Fin (D.T.card + m) → restrictedMvPowerSeriesSubring m (presheafValue D) :=
    Fin.addCases
      (fun i : Fin D.T.card =>
        algebraMap (presheafValue D) (restrictedMvPowerSeriesSubring m (presheafValue D))
          (example638_genTuple D i))
      (fun j : Fin m =>
        (⟨MvPowerSeries.X j, MvPowerSeries.X_isRestricted j⟩ :
          restrictedMvPowerSeriesSubring m (presheafValue D)))
  have hb : ∀ i, TopologicalRing.IsBounded
      (Set.range (b i ^ · : ℕ → restrictedMvPowerSeriesSubring m (presheafValue D))) := by
    intro i
    refine Fin.addCases (motive := fun i => TopologicalRing.IsBounded
      (Set.range (b i ^ · : ℕ → restrictedMvPowerSeriesSubring m (presheafValue D)))) ?_ ?_ i
    · intro i'
      have hbi : b (Fin.castAdd m i') =
          algebraMap (presheafValue D) (restrictedMvPowerSeriesSubring m (presheafValue D))
            (example638_genTuple D i') := by simp only [b, Fin.addCases_left]
      rw [hbi]
      refine (MvTateAlgebra.mvTateAlgebra_algebraMap_isBounded (A := presheafValue D) (m := m)
        (example638_genTuple_isBounded D i')).subset ?_
      rintro _ ⟨k, rfl⟩
      exact ⟨example638_genTuple D i' ^ k, ⟨k, rfl⟩, by rw [map_pow]⟩
    · intro j'
      have hbj : b (Fin.natAdd D.T.card j') =
          (⟨MvPowerSeries.X j', MvPowerSeries.X_isRestricted j'⟩ :
            restrictedMvPowerSeriesSubring m (presheafValue D)) := by
        simp only [b, Fin.addCases_right]
      rw [hbj]
      exact MvTateAlgebra.mvPowerSeries_X_isBounded j'
  set Ψ := mvEvalHomBounded g hg b hb with hΨ
  refine ⟨Ψ, ?_⟩
  -- Reduce `Surjective Ψ` to `Surjective Ψ.kerLift` (`Ψ = kerLift ∘ mk`, `mk` surjective).
  suffices hkl : Function.Surjective (RingHom.kerLift Ψ) by
    intro y
    obtain ⟨q, rfl⟩ := hkl y
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective q
    exact ⟨c, (RingHom.kerLift_mk Ψ c).symm⟩
  -- `RingHom.kerLift Ψ : source ⧸ ker → (presheafValue D)⟨Y⟩` is injective; surjectivity is the
  -- relative backward map (AG1b). Foundation: `ker Ψ` is closed (Prop 6.17 over strongly-noeth `A`),
  -- so `source ⧸ ker` is a complete topological ring — the codomain for the extension.
  letI τS : TopologicalSpace (restrictedMvPowerSeriesSubring (D.T.card + m) A) :=
    MvTateAlgebra.mvTateAlgebraTopology' (D.T.card + m)
  haveI hringS : IsTopologicalRing (restrictedMvPowerSeriesSubring (D.T.card + m) A) :=
    MvTateAlgebra.mvTateAlgebraTopology'_isTopologicalRing (D.T.card + m)
  have hA_complete : @CompleteSpace A (IsTopologicalAddGroup.rightUniformSpace A) := ‹_›
  have hker_closed : IsClosed
      ((RingHom.ker Ψ : Ideal (restrictedMvPowerSeriesSubring (D.T.card + m) A)) :
        Set (restrictedMvPowerSeriesSubring (D.T.card + m) A)) :=
    MvTateAlgebra.mvTate_isClosed_ideal (D.T.card + m) hA_complete (RingHom.ker Ψ)
  -- γ := source ⧸ ker Ψ, the injective-factorisation codomain; complete + T2 (quotient of the
  -- complete `source` by the closed `ker Ψ`), so it can host the dense extension (backward map).
  letI τQ : TopologicalSpace (restrictedMvPowerSeriesSubring (D.T.card + m) A ⧸ RingHom.ker Ψ) :=
    mvQuotTopology (D.T.card + m) (RingHom.ker Ψ)
  letI uQ : UniformSpace (restrictedMvPowerSeriesSubring (D.T.card + m) A ⧸ RingHom.ker Ψ) :=
    mvQuotUniformSpace (D.T.card + m) (RingHom.ker Ψ)
  haveI hringQ : @IsTopologicalRing _ τQ _ :=
    mvQuot_isTopologicalRing (D.T.card + m) (RingHom.ker Ψ)
  haveI : @IsUniformAddGroup _ uQ _ :=
    mvQuot_isUniformAddGroup (D.T.card + m) (RingHom.ker Ψ)
  haveI : @CompleteSpace _ uQ :=
    mvQuot_completeSpace (D.T.card + m) (RingHom.ker Ψ) hA_complete
  haveI hT2Q : @T2Space _ τQ := mvQuot_t2Space (D.T.card + m) (RingHom.ker Ψ) hker_closed
  haveI : @T0Space _ τQ := @T1Space.t0Space _ τQ (@T2Space.t1Space _ τQ hT2Q)
  -- `ē := kerLift Ψ : γ → T` is the injective factorisation; we right-invert it.
  set ē : (restrictedMvPowerSeriesSubring (D.T.card + m) A ⧸ RingHom.ker Ψ) →+*
      restrictedMvPowerSeriesSubring m (presheafValue D) := RingHom.kerLift Ψ with hē
  -- **The dense subring** `U := (Localization.Away D.s)[Y₁..Yₘ]` (polynomials in the unit-disc
  -- variables with localization coefficients), mapping to both `T` (densely, via `i`) and `γ`
  -- (via `f`); the backward map extends `f` along the dense embedding `i`.
  -- `mk_s` is a unit in `γ`, so the localization lift `ψ : Loc → γ` exists.
  have hUnitS : IsUnit ((Ideal.Quotient.mk (RingHom.ker Ψ)).comp
      (algebraMap A (restrictedMvPowerSeriesSubring (D.T.card + m) A)) D.s) := by
    -- Install the source-ring (`A⟨X₁..Xₙ₊ₘ⟩`) uniform/complete/nonarch/T0 instances so that
    -- `mvEvalHomBounded` can build the variable-inclusion `ι`.
    letI uS : UniformSpace (restrictedMvPowerSeriesSubring (D.T.card + m) A) :=
      MvTateAlgebra.mvTateUniformSpace (D.T.card + m)
    haveI : IsUniformAddGroup (restrictedMvPowerSeriesSubring (D.T.card + m) A) :=
      MvTateAlgebra.mvTate_isUniformAddGroup (D.T.card + m)
    haveI : CompleteSpace (restrictedMvPowerSeriesSubring (D.T.card + m) A) :=
      MvTateAlgebra.mvTate_completeSpace (D.T.card + m) hA_complete
    haveI : NonarchimedeanRing (restrictedMvPowerSeriesSubring (D.T.card + m) A) :=
      MvTateAlgebra.mvTate_nonarchimedean (D.T.card + m)
    haveI : T2Space (restrictedMvPowerSeriesSubring (D.T.card + m) A) :=
      MvTateAlgebra.mvTate_t2Space (D.T.card + m)
    haveI : T0Space (restrictedMvPowerSeriesSubring (D.T.card + m) A) := inferInstance
    -- `ι : A⟨X₁..Xₙ⟩ → A⟨X₁..Xₙ₊ₘ⟩`, `Xᵢ ↦ X (castAdd m i)`, `algebraMap a ↦ algebraMap a`.
    let bι : Fin D.T.card → restrictedMvPowerSeriesSubring (D.T.card + m) A :=
      fun i => ⟨MvPowerSeries.X (Fin.castAdd m i), MvPowerSeries.X_isRestricted _⟩
    have hbι : ∀ i, TopologicalRing.IsBounded
        (Set.range (bι i ^ · : ℕ → restrictedMvPowerSeriesSubring (D.T.card + m) A)) :=
      fun i => MvTateAlgebra.mvPowerSeries_X_isBounded (Fin.castAdd m i)
    let ι : restrictedMvPowerSeriesSubring D.T.card A →+*
        restrictedMvPowerSeriesSubring (D.T.card + m) A :=
      mvEvalHomBounded (algebraMap A (restrictedMvPowerSeriesSubring (D.T.card + m) A))
        (MvTateAlgebra.mvTateAlgebra_algebraMap_continuous (D.T.card + m)) bι hbι
    -- `algebraMap _ T ∘ example638_evalHom D = Ψ ∘ ι` POINTWISE (push the continuous additive maps
    -- through the single evaluation `tsum`, termwise — NO Fubini).
    have hkey : ∀ h : restrictedMvPowerSeriesSubring D.T.card A,
        algebraMap (presheafValue D) (restrictedMvPowerSeriesSubring m (presheafValue D))
            (example638_evalHom D h) = Ψ (ι h) := by
      intro h
      -- LHS: push `algebraMap _ T` through the `example638_evalHom` tsum.
      have hL : algebraMap (presheafValue D) (restrictedMvPowerSeriesSubring m (presheafValue D))
            (example638_evalHom D h) =
          ∑' v, algebraMap (presheafValue D) (restrictedMvPowerSeriesSubring m (presheafValue D))
            (mvEvalTerm D.canonicalMap (example638_genTuple D) h v) := by
        change algebraMap (presheafValue D) (restrictedMvPowerSeriesSubring m (presheafValue D))
          (∑' v, mvEvalTerm D.canonicalMap (example638_genTuple D) h v) = _
        exact (mvEvalTerm_summable D.canonicalMap (canonicalMap_continuous D)
          (example638_genTuple D) (example638_genTuple_isBounded D) h).map_tsum
          (algebraMap (presheafValue D) (restrictedMvPowerSeriesSubring m (presheafValue D)))
          (MvTateAlgebra.mvTateAlgebra_algebraMap_continuous (A := presheafValue D) m)
      -- RHS: push `Ψ` through the `ι` tsum.
      have hR : Ψ (ι h) =
          ∑' v, Ψ (mvEvalTerm (algebraMap A (restrictedMvPowerSeriesSubring (D.T.card + m) A))
            bι h v) := by
        change Ψ (∑' v, mvEvalTerm
          (algebraMap A (restrictedMvPowerSeriesSubring (D.T.card + m) A)) bι h v) = _
        exact (mvEvalTerm_summable
          (algebraMap A (restrictedMvPowerSeriesSubring (D.T.card + m) A))
          (MvTateAlgebra.mvTateAlgebra_algebraMap_continuous (D.T.card + m)) bι hbι h).map_tsum
          Ψ (by rw [hΨ]; exact mvEvalHomBounded_continuous g hg b hb)
      rw [hL, hR]
      -- termwise equality of the two evaluation series.
      refine tsum_congr (fun v => ?_)
      -- LHS term: `algebraMap _ T (canonicalMap(coeffᵥ) · ∏ (tᵢ/s)^vᵢ)`.
      rw [mvEvalTerm, mvEvalTerm, map_mul, map_prod]
      rw [map_mul]
      -- generators on `Ψ`: `Ψ(algebraMap a) = g a`, `Ψ(bι i) = b (castAdd i)`.
      rw [show Ψ (algebraMap A (restrictedMvPowerSeriesSubring (D.T.card + m) A)
          (MvPowerSeries.coeff v h.val)) = g (MvPowerSeries.coeff v h.val) from by
        rw [hΨ]; exact mvEvalHomBounded_algebraMap g hg b hb (MvPowerSeries.coeff v h.val)]
      -- `g a = algebraMap _ T (canonicalMap a)`.
      rw [show g (MvPowerSeries.coeff v h.val) =
          algebraMap (presheafValue D) (restrictedMvPowerSeriesSubring m (presheafValue D))
            (D.canonicalMap (MvPowerSeries.coeff v h.val)) from rfl]
      congr 1
      rw [map_prod]
      refine Finset.prod_congr rfl (fun i _ => ?_)
      rw [map_pow, map_pow]
      congr 1
      -- `Ψ(bι i) = b (castAdd i) = algebraMap _ T (example638_genTuple D i)`.
      rw [show Ψ (bι i) = b (Fin.castAdd m i) from by
        rw [hΨ]; exact mvEvalHomBounded_X g hg b hb (Fin.castAdd m i)]
      simp only [b, Fin.addCases_left]
    -- Finish like `example638_isUnit_mk_s`: `invS D = example638_evalHom D c`, so
    -- `algebraMap _ T (invS D) = Ψ (ι c) ∈ range Ψ`; the inverse of `mk(alg s)` is `mk(ι c)`.
    obtain ⟨c, hc⟩ := invS_mem_range D
    rw [isUnit_iff_exists_inv]
    refine ⟨Ideal.Quotient.mk (RingHom.ker Ψ) (ι c), ?_⟩
    apply RingHom.kerLift_injective Ψ
    rw [map_one, map_mul, RingHom.comp_apply]
    rw [show RingHom.kerLift Ψ (Ideal.Quotient.mk (RingHom.ker Ψ)
        ((algebraMap A (restrictedMvPowerSeriesSubring (D.T.card + m) A)) D.s)) =
        Ψ ((algebraMap A (restrictedMvPowerSeriesSubring (D.T.card + m) A)) D.s) from
      RingHom.kerLift_mk Ψ _]
    rw [show RingHom.kerLift Ψ (Ideal.Quotient.mk (RingHom.ker Ψ) (ι c)) = Ψ (ι c) from
      RingHom.kerLift_mk Ψ _]
    rw [← hkey c]; erw [hc]
    -- `Ψ(algebraMap s) = g s = algebraMap _ T (canonicalMap s)`; goal:
    -- `algebraMap _ T (canonicalMap s) · algebraMap _ T (invS D) = 1`.
    rw [show Ψ ((algebraMap A (restrictedMvPowerSeriesSubring (D.T.card + m) A)) D.s) =
        algebraMap (presheafValue D) (restrictedMvPowerSeriesSubring m (presheafValue D))
          (D.canonicalMap D.s) from by
      rw [hΨ]; exact mvEvalHomBounded_algebraMap g hg b hb D.s]
    rw [← map_mul, canonicalMap_s_mul_invS, map_one]
  -- `ψ : Loc → γ`, the localization lift (mirror of `example638_locToQuot`).
  let ψγ : Localization.Away D.s →+*
      (restrictedMvPowerSeriesSubring (D.T.card + m) A ⧸ RingHom.ker Ψ) :=
    IsLocalization.Away.lift (x := D.s)
      (g := (Ideal.Quotient.mk (RingHom.ker Ψ)).comp
        (algebraMap A (restrictedMvPowerSeriesSubring (D.T.card + m) A))) hUnitS
  -- `i : U → T`: coefficients via `coeRingHom` into `presheafValue D` then constant series; the
  -- `Yⱼ` to the unit-disc variables. `f : U → γ`: coefficients via `ψγ`; the `Yⱼ` to `mk(Z_{n+j})`.
  let iU : MvPolynomial (Fin m) (Localization.Away D.s) →+*
      restrictedMvPowerSeriesSubring m (presheafValue D) :=
    MvPolynomial.eval₂Hom
      ((algebraMap (presheafValue D) (restrictedMvPowerSeriesSubring m (presheafValue D))).comp
        D.coeRingHom)
      (fun j => (⟨MvPowerSeries.X j, MvPowerSeries.X_isRestricted j⟩ :
        restrictedMvPowerSeriesSubring m (presheafValue D)))
  let fU : MvPolynomial (Fin m) (Localization.Away D.s) →+*
      (restrictedMvPowerSeriesSubring (D.T.card + m) A ⧸ RingHom.ker Ψ) :=
    MvPolynomial.eval₂Hom ψγ
      (fun j => Ideal.Quotient.mk (RingHom.ker Ψ)
        (⟨MvPowerSeries.X (Fin.natAdd D.T.card j), MvPowerSeries.X_isRestricted _⟩ :
          restrictedMvPowerSeriesSubring (D.T.card + m) A))
  -- characterizing equations for the let-bound evaluation homs (make them rewritable).
  have hiU_C : ∀ c : Localization.Away D.s, iU (MvPolynomial.C c) =
      (algebraMap (presheafValue D) (restrictedMvPowerSeriesSubring m (presheafValue D))).comp
        D.coeRingHom c := fun c => MvPolynomial.eval₂Hom_C _ _ c
  have hiU_X : ∀ j, iU (MvPolynomial.X j) =
      (⟨MvPowerSeries.X j, MvPowerSeries.X_isRestricted j⟩ :
        restrictedMvPowerSeriesSubring m (presheafValue D)) := fun j => MvPolynomial.eval₂Hom_X' _ _ j
  have hfU_C : ∀ c : Localization.Away D.s, fU (MvPolynomial.C c) = ψγ c :=
    fun c => MvPolynomial.eval₂Hom_C _ _ c
  have hfU_X : ∀ j, fU (MvPolynomial.X j) =
      Ideal.Quotient.mk (RingHom.ker Ψ)
        (⟨MvPowerSeries.X (Fin.natAdd D.T.card j), MvPowerSeries.X_isRestricted _⟩ :
          restrictedMvPowerSeriesSubring (D.T.card + m) A) := fun j => MvPolynomial.eval₂Hom_X' _ _ j
  -- give `U` the pullback uniformity along `iU`, making `iU` uniform-inducing.
  letI uU : UniformSpace (MvPolynomial (Fin m) (Localization.Away D.s)) :=
    UniformSpace.comap iU uT
  have hi_ind : IsUniformInducing iU := ⟨rfl⟩
  have hi_dense : DenseRange iU := by
    classical
    -- `R := closure(range iU)`, a closed subring of `T`. We show `R = ⊤` by exhibiting that it
    -- contains the (dense) box-supported polynomials.
    set R : Subring (restrictedMvPowerSeriesSubring m (presheafValue D)) :=
      iU.range.topologicalClosure with hR
    have hiU_le : iU.range ≤ R := Subring.le_topologicalClosure _
    -- Step 1: every constant series `algebraMap _ T x` (x : presheafValue D) lies in `R`, because
    -- `range coeRingHom` is dense in `presheafValue D`, `algebraMap _ T` is continuous, and
    -- `algebraMap _ T (coeRingHom c) = iU (C c) ∈ R`.
    have hconst : ∀ x : presheafValue D,
        algebraMap (presheafValue D) (restrictedMvPowerSeriesSubring m (presheafValue D)) x ∈ R :=
        by
      have hcont : Continuous
          (algebraMap (presheafValue D) (restrictedMvPowerSeriesSubring m (presheafValue D))) :=
        MvTateAlgebra.mvTateAlgebra_algebraMap_continuous (A := presheafValue D) m
      -- the preimage subring `R.comap (algebraMap _ T)` is closed and contains `range coeRingHom`.
      have hclosed : IsClosed
          ((algebraMap (presheafValue D) (restrictedMvPowerSeriesSubring m (presheafValue D)) ⁻¹'
            (R : Set _)) : Set (presheafValue D)) :=
        (Subring.isClosed_topologicalClosure _).preimage hcont
      have hdense : DenseRange (D.coeRingHom : Localization.Away D.s → presheafValue D) := by
        letI : UniformSpace (Localization.Away D.s) := D.uniformSpace
        letI : IsUniformAddGroup (Localization.Away D.s) := D.isUniformAddGroup
        change DenseRange (UniformSpace.Completion.coeRingHom :
          Localization.Away D.s → presheafValue D)
        exact UniformSpace.Completion.denseRange_coe
      intro x
      -- `x ∈ closure(range coeRingHom)`; the preimage set is closed, contains `range coeRingHom`.
      have hx_cl : x ∈ closure (Set.range (D.coeRingHom)) := hdense x
      have hsub : Set.range (D.coeRingHom) ⊆
          algebraMap (presheafValue D) (restrictedMvPowerSeriesSubring m (presheafValue D)) ⁻¹'
            (R : Set _) := by
        rintro _ ⟨c, rfl⟩
        change algebraMap (presheafValue D) (restrictedMvPowerSeriesSubring m (presheafValue D))
          (D.coeRingHom c) ∈ R
        exact hiU_le ⟨MvPolynomial.C c, by rw [hiU_C c]; rfl⟩
      exact hclosed.closure_subset_iff.mpr hsub hx_cl
    -- Step 2: each variable `⟨Xⱼ, _⟩` lies in `R` (`= iU (X j) ∈ range iU ≤ R`).
    have hX : ∀ j : Fin m, (⟨MvPowerSeries.X j, MvPowerSeries.X_isRestricted j⟩ :
        restrictedMvPowerSeriesSubring m (presheafValue D)) ∈ R :=
      fun j => hiU_le ⟨MvPolynomial.X j, hiU_X j⟩
    -- Step 3: each box-supported polynomial `g` lies in `R`, via the finite monomial decomposition
    -- `g = ∑_{v ∈ box} (algebraMap _ T (g.val v)) · ∏ⱼ ⟨Xⱼ,_⟩^(vⱼ)` (`R` is a subring).
    have hbox : ∀ g : restrictedMvPowerSeriesSubring m (presheafValue D),
        (∃ N, ∀ l : Fin m →₀ ℕ, (∃ i, N ≤ l i) → g.val l = 0) →
        g ∈ R := by
      rintro g ⟨N, hN⟩
      -- the finite box index set `{l | ∀ i, l i < N}`.
      set box : Finset (Fin m →₀ ℕ) :=
        (Finset.univ : Finset (Fin m → Fin N)).image
          (fun f => Finsupp.equivFunOnFinite.symm (fun i => (f i : ℕ))) with hbox_def
      -- membership: `l ∈ box ↔ ∀ i, l i < N`.
      have hmem_box : ∀ l : Fin m →₀ ℕ, l ∈ box ↔ ∀ i, l i < N := by
        intro l
        simp only [hbox_def, Finset.mem_image, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨f, rfl⟩ i
          exact (f i).2
        · intro hlt
          exact ⟨fun i => ⟨l i, hlt i⟩, by ext i; simp [Finsupp.equivFunOnFinite]⟩
      -- the monomial summand `term v = algebraMap _ T (g.val v) · ∏ⱼ ⟨Xⱼ,_⟩^(vⱼ) ∈ T`.
      set term : (Fin m →₀ ℕ) → restrictedMvPowerSeriesSubring m (presheafValue D) :=
        fun v => algebraMap (presheafValue D) (restrictedMvPowerSeriesSubring m (presheafValue D))
            (g.val v) *
          ∏ j : Fin m, (⟨MvPowerSeries.X j, MvPowerSeries.X_isRestricted j⟩ :
            restrictedMvPowerSeriesSubring m (presheafValue D)) ^ (v j) with hterm_def
      -- `(term v).val = monomial v (g.val v)`.
      have hterm_val : ∀ v, (term v).val = MvPowerSeries.monomial v (g.val v) := by
        intro v
        rw [hterm_def]
        simp only
        rw [Subring.coe_mul, MvPowerSeries.monomial_eq']
        have hprod : (↑(∏ j : Fin m, (⟨MvPowerSeries.X j, MvPowerSeries.X_isRestricted j⟩ :
              restrictedMvPowerSeriesSubring m (presheafValue D)) ^ (v j)) :
              MvPowerSeries (Fin m) (presheafValue D)) =
            v.prod fun s e => MvPowerSeries.X s ^ e := by
          rw [SubmonoidClass.coe_finset_prod, Finsupp.prod_fintype]
          · refine Finset.prod_congr rfl (fun j _ => ?_)
            rw [SubmonoidClass.coe_pow]
          · intro j; rw [pow_zero]
        have hC : (↑(algebraMap (presheafValue D)
              (restrictedMvPowerSeriesSubring m (presheafValue D)) (g.val v)) :
              MvPowerSeries (Fin m) (presheafValue D)) = MvPowerSeries.C (g.val v) :=
          MvPowerSeries.algebraMap_apply
        rw [hC, hprod]
      -- each `term v ∈ R` (constant ∈ R, variables ∈ R, `R` a subring).
      have hterm_mem : ∀ v, term v ∈ R := fun v =>
        R.mul_mem (hconst (g.val v)) (Subring.prod_mem _ (fun j _ => R.pow_mem (hX j) (v j)))
      -- `g = ∑_{v ∈ box} term v` in the restricted subring (coefficient-wise check, going through
      -- the `MvPolynomial` coe ring hom so `map_sum` lands on a `RingHom`).
      have hg_sum : g = ∑ v ∈ box, term v := by
        apply Subtype.ext
        rw [AddSubmonoidClass.coe_finset_sum]
        simp only [hterm_val]
        -- `∑ v∈box, monomial v (g.val v) = ↑(∑ v∈box, MvPolynomial.monomial v (g.val v))`.
        rw [show (∑ v ∈ box, MvPowerSeries.monomial v (g.val v) :
              MvPowerSeries (Fin m) (presheafValue D)) =
            MvPolynomial.coeToMvPowerSeries.ringHom
              (∑ v ∈ box, MvPolynomial.monomial v (g.val v)) from by
          rw [map_sum]
          refine Finset.sum_congr rfl (fun v _ => ?_)
          rw [MvPolynomial.coeToMvPowerSeries.ringHom_apply, MvPolynomial.coe_monomial]]
        rw [MvPolynomial.coeToMvPowerSeries.ringHom_apply]
        ext w
        rw [MvPolynomial.coeff_coe, show MvPowerSeries.coeff w g.val = g.val w from
          MvPowerSeries.coeff_apply g.val w]
        rw [show MvPolynomial.coeff w (∑ v ∈ box, MvPolynomial.monomial v (g.val v)) =
            ∑ v ∈ box, MvPolynomial.coeff w (MvPolynomial.monomial v (g.val v)) from
          MvPolynomial.coeff_sum _ _ _]
        by_cases hw : ∀ i, w i < N
        · rw [Finset.sum_eq_single w]
          · rw [MvPolynomial.coeff_monomial, if_pos rfl]
          · intro v _ hvw
            rw [MvPolynomial.coeff_monomial, if_neg hvw]
          · intro hw_notin
            exact absurd ((hmem_box w).mpr hw) hw_notin
        · -- `w` outside the box: `g.val w = 0` and every monomial term vanishes at `w`.
          push_neg at hw
          obtain ⟨i, hi⟩ := hw
          rw [hN w ⟨i, hi⟩]
          symm
          refine Finset.sum_eq_zero (fun v hv => ?_)
          rw [MvPolynomial.coeff_monomial, if_neg]
          intro hwv
          exact absurd ((hmem_box v).mp hv i) (by rw [hwv]; omega)
      rw [hg_sum]
      exact Subring.sum_mem _ (fun v _ => hterm_mem v)
    -- Conclude: the dense box-polynomials are ⊆ `R = closure(range iU)`, so `closure(range iU)`
    -- contains a dense set, hence `= univ`; thus `DenseRange iU`.
    rw [denseRange_iff_closure_range]
    refine Set.eq_univ_of_univ_subset ?_
    rw [← (MvTateAlgebra.mvTateAlgebra_polynomials_dense (A := presheafValue D) m).closure_eq]
    refine closure_minimal (fun g hg => ?_) isClosed_closure
    exact hbox g hg
  have hf_unif : UniformContinuous fU := by
    classical
    -- `uU = comap iU uT` is a uniform add group (pullback of the uniform add group `uT`).
    haveI huug : @IsUniformAddGroup (MvPolynomial (Fin m) (Localization.Away D.s)) uU _ :=
      IsUniformAddGroup.comap iU
    haveI hNAQ : @NonarchimedeanRing _ _ τQ := mvQuot_nonarchimedean (D.T.card + m) (RingHom.ker Ψ)
    haveI hUQ : @IsUniformAddGroup _ uQ _ := mvQuot_isUniformAddGroup (D.T.card + m) (RingHom.ker Ψ)
    -- `P_T = principal pair of `presheafValue D``, `P_S = principal pair of `A``.
    set P_T := (IsTateRing.principalPair (presheafValue D)).toPairOfDefinition with hP_T
    -- (i) `ψγ : Loc → γ` is continuous (relative analogue of `example638_locToQuot_continuous`).
    have hψγ_cont : @Continuous _ _ D.topology τQ ψγ := by
      change @Continuous _ _ (locTopology D.P D.T D.s D.hopen) τQ ψγ
      refine locTopology_continuous_lift D.P D.T D.s D.hopen ψγ ?_ ?_
      · -- (a) `ψγ ∘ algebraMap A = mk ∘ algebraMap A source` is continuous.
        have heq : ψγ.comp (algebraMap A (Localization.Away D.s)) =
            (Ideal.Quotient.mk (RingHom.ker Ψ)).comp
              (algebraMap A (restrictedMvPowerSeriesSubring (D.T.card + m) A)) := by
          ext a
          simp only [RingHom.comp_apply, ψγ, IsLocalization.Away.lift_eq]
        rw [heq]
        exact (continuous_quotient_mk'.comp
          (MvTateAlgebra.mvTateAlgebra_algebraMap_continuous (D.T.card + m)))
      · -- (b) `ψγ(tᵢ/s) = mk(X (castAdd i))` is power-bounded in `γ`.
        intro t ht
        set i := D.T.equivFin ⟨t, ht⟩ with hi
        -- `ē ∘ ψγ = algebraMap _ T ∘ coeRingHom` (round-trip on the localization, inlined).
        have hψ_round' : (RingHom.kerLift Ψ).comp ψγ =
            (algebraMap (presheafValue D) (restrictedMvPowerSeriesSubring m (presheafValue D))).comp
              D.coeRingHom := by
          apply IsLocalization.ringHom_ext (Submonoid.powers D.s)
          ext a
          simp only [RingHom.comp_apply, ψγ, IsLocalization.Away.lift_eq, RingHom.kerLift_mk,
            hΨ, mvEvalHomBounded_algebraMap, g, RationalLocData.canonicalMap]
        -- `ψγ(divByS t s) = mk(X (castAdd i))`, from injectivity of `ē = kerLift Ψ`.
        have hψγval : ψγ (divByS (↑(D.T.equivFin.symm i) : A) D.s) =
            Ideal.Quotient.mk (RingHom.ker Ψ)
              (⟨MvPowerSeries.X (Fin.castAdd m i), MvPowerSeries.X_isRestricted _⟩ :
                restrictedMvPowerSeriesSubring (D.T.card + m) A) := by
          apply RingHom.kerLift_injective Ψ
          rw [show RingHom.kerLift Ψ (ψγ (divByS (↑(D.T.equivFin.symm i) : A) D.s)) =
              ((algebraMap (presheafValue D)
                  (restrictedMvPowerSeriesSubring m (presheafValue D))).comp D.coeRingHom)
                (divByS (↑(D.T.equivFin.symm i) : A) D.s) from
            RingHom.congr_fun hψ_round' (divByS (↑(D.T.equivFin.symm i) : A) D.s)]
          rw [show RingHom.kerLift Ψ (Ideal.Quotient.mk (RingHom.ker Ψ)
              (⟨MvPowerSeries.X (Fin.castAdd m i), MvPowerSeries.X_isRestricted _⟩ :
                restrictedMvPowerSeriesSubring (D.T.card + m) A)) =
              Ψ (⟨MvPowerSeries.X (Fin.castAdd m i), MvPowerSeries.X_isRestricted _⟩ :
                restrictedMvPowerSeriesSubring (D.T.card + m) A) from RingHom.kerLift_mk Ψ _]
          rw [hΨ, mvEvalHomBounded_X]
          -- both `= algebraMap _ T (genTuple i) = b (castAdd i)`.
          rw [show b (Fin.castAdd m i) =
              algebraMap (presheafValue D) (restrictedMvPowerSeriesSubring m (presheafValue D))
                (example638_genTuple D i) from by simp only [b, Fin.addCases_left]]
          rw [RingHom.comp_apply, example638_genTuple]
        have htval : t = (↑(D.T.equivFin.symm i) : A) := by rw [hi, Equiv.symm_apply_apply]
        rw [htval, hψγval]
        -- `X (castAdd i)` ∈ pair-subring of source ⟹ power-bounded ⟹ `mk` power-bounded.
        have hXi_mem : (⟨MvPowerSeries.X (Fin.castAdd m i), MvPowerSeries.X_isRestricted _⟩ :
            restrictedMvPowerSeriesSubring (D.T.card + m) A) ∈
            MvTateAlgebra.mvPairSubring (D.T.card + m)
              (IsTateRing.principalPair A).toPairOfDefinition := by
          intro l
          change MvPowerSeries.coeff l (MvPowerSeries.X (Fin.castAdd m i)) ∈ _
          rw [MvPowerSeries.coeff_X]
          split
          · exact (IsTateRing.principalPair A).toPairOfDefinition.A₀.one_mem
          · exact (IsTateRing.principalPair A).toPairOfDefinition.A₀.zero_mem
        have hXi_pb : @TopologicalRing.IsPowerBounded _ _ τS
            (⟨MvPowerSeries.X (Fin.castAdd m i), MvPowerSeries.X_isRestricted _⟩ :
              restrictedMvPowerSeriesSubring (D.T.card + m) A) :=
          (MvTateAlgebra.mvTateAlgebra_pairOfDefinition (D.T.card + m)).mem_powerBoundedSubring
            hXi_mem
        exact @isPowerBounded_map_of_isOpenMap _ _ _ τS _ τQ hringQ
          (Ideal.Quotient.mk (RingHom.ker Ψ)) continuous_quotient_mk'
          (@QuotientRing.isOpenMap_coe _ τS _ (RingHom.ker Ψ) hringS) _ hXi_pb
    -- (ii) `iU p`'s coefficient at `v` is `coeRingHom (coeff_v p)` (`iU = coe ∘ map coeRingHom`).
    have hiU_coeff : ∀ (p : MvPolynomial (Fin m) (Localization.Away D.s)) (v : Fin m →₀ ℕ),
        MvPowerSeries.coeff v (iU p).val = D.coeRingHom (MvPolynomial.coeff v p) := by
      -- `(iU p).val = ↑(MvPolynomial.map coeRingHom p)` (coe to power series), coeff-wise.
      have hiU_val : ∀ p : MvPolynomial (Fin m) (Localization.Away D.s),
          (iU p).val = (↑(MvPolynomial.map D.coeRingHom p) :
            MvPowerSeries (Fin m) (presheafValue D)) := by
        have hiU_eq : (restrictedMvPowerSeriesSubring m (presheafValue D)).subtype.comp iU =
            (MvPolynomial.coeToMvPowerSeries.ringHom).comp (MvPolynomial.map D.coeRingHom) := by
          refine MvPolynomial.ringHom_ext (fun c => ?_) (fun j => ?_)
          · rw [RingHom.comp_apply, RingHom.comp_apply, hiU_C c]
            change (algebraMap (presheafValue D) (MvPowerSeries (Fin m) (presheafValue D)))
              (D.coeRingHom c) = _
            rw [MvPolynomial.coeToMvPowerSeries.ringHom_apply, MvPolynomial.map_C,
              MvPolynomial.coe_C, MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self_apply]
          · rw [RingHom.comp_apply, RingHom.comp_apply, hiU_X j]
            change (MvPowerSeries.X j : MvPowerSeries (Fin m) (presheafValue D)) = _
            rw [MvPolynomial.coeToMvPowerSeries.ringHom_apply, MvPolynomial.map_X,
              MvPolynomial.coe_X]
        intro p
        have hp := RingHom.congr_fun hiU_eq p
        simpa only [RingHom.comp_apply, MvPolynomial.coeToMvPowerSeries.ringHom_apply,
          Subring.coe_subtype] using hp
      intro p v
      rw [hiU_val p, MvPolynomial.coeff_coe, MvPolynomial.coeff_map]
    -- (iii) each `fU (X j) = mk (Z_{n+j})` is power-bounded in `γ`, so the product-power range is.
    have hfUX_pb : ∀ j : Fin m, @TopologicalRing.IsPowerBounded _ _ τQ (fU (MvPolynomial.X j)) := by
      intro j
      rw [hfU_X j]
      have hZ_mem : (⟨MvPowerSeries.X (Fin.natAdd D.T.card j), MvPowerSeries.X_isRestricted _⟩ :
          restrictedMvPowerSeriesSubring (D.T.card + m) A) ∈
          MvTateAlgebra.mvPairSubring (D.T.card + m)
            (IsTateRing.principalPair A).toPairOfDefinition := by
        intro l
        change MvPowerSeries.coeff l (MvPowerSeries.X (Fin.natAdd D.T.card j)) ∈ _
        rw [MvPowerSeries.coeff_X]
        split
        · exact (IsTateRing.principalPair A).toPairOfDefinition.A₀.one_mem
        · exact (IsTateRing.principalPair A).toPairOfDefinition.A₀.zero_mem
      have hZ_pb : @TopologicalRing.IsPowerBounded _ _ τS
          (⟨MvPowerSeries.X (Fin.natAdd D.T.card j), MvPowerSeries.X_isRestricted _⟩ :
            restrictedMvPowerSeriesSubring (D.T.card + m) A) :=
        (MvTateAlgebra.mvTateAlgebra_pairOfDefinition (D.T.card + m)).mem_powerBoundedSubring hZ_mem
      exact @isPowerBounded_map_of_isOpenMap _ _ _ τS _ τQ hringQ
        (Ideal.Quotient.mk (RingHom.ker Ψ)) continuous_quotient_mk'
        (@QuotientRing.isOpenMap_coe _ τS _ (RingHom.ker Ψ) hringS) _ hZ_pb
    have hRbdd : @TopologicalRing.IsBounded _ _ τQ
        (Set.range (fun v : Fin m →₀ ℕ => ∏ j, fU (MvPolynomial.X j) ^ (v j))) :=
      mvRangeProd_isBounded (fun j => fU (MvPolynomial.X j)) hfUX_pb
    -- Reduce to continuity of `fU` at `0` (additive-group hom).
    refine @uniformContinuous_of_continuousAt_zero _ _ uU _ huug _ uQ _ hUQ _ _ fU ?_
    -- `ContinuousAt fU 0`: `Tendsto fU (nhds 0) (nhds 0)`; source `nhds 0 = comap iU (nhds 0)`.
    have hnhds0 : @nhds _ (uU.toTopologicalSpace)
        (0 : MvPolynomial (Fin m) (Localization.Away D.s)) =
        Filter.comap iU (@nhds _ τT (0 : restrictedMvPowerSeriesSubring m (presheafValue D))) := by
      have := hi_ind.isInducing.nhds_eq_comap
        (0 : MvPolynomial (Fin m) (Localization.Away D.s))
      rw [this, map_zero]
    rw [ContinuousAt, map_zero, Filter.tendsto_def]
    intro V hV
    rw [hnhds0, Filter.mem_comap]
    -- `V` is a `γ`-`0`-nbhd; take an open subgroup `Vg ⊆ V` (γ nonarchimedean).
    obtain ⟨Vg, hVgV⟩ := @NonarchimedeanRing.is_nonarchimedean _ _ τQ hNAQ V hV
    -- absorb the bounded product-power range `R_γ` into `Vg`: `R_γ · V' ⊆ Vg`.
    obtain ⟨V', hV', hV'R⟩ := hRbdd (Vg : Set _) (Vg.isOpen.mem_nhds Vg.zero_mem)
    -- `ψγ⁻¹ V'` is a `Loc`-`0`-nbhd; via `coeRingHom` inducing, pull back to `presheafValue D`.
    letI tLoc : TopologicalSpace (Localization.Away D.s) := D.topology
    have hψpre : ψγ ⁻¹' V' ∈ @nhds _ tLoc (0 : Localization.Away D.s) :=
      (hψγ_cont.continuousAt (x := (0 : Localization.Away D.s))).preimage_mem_nhds
        (by rw [map_zero]; exact hV')
    -- `coeRingHom` is uniform-inducing (completion coe) ⟹ `Loc`-topology = comap of `presheafValue`.
    have hcoe_ind : @Topology.IsInducing _ _ tLoc _ (D.coeRingHom) := by
      letI : UniformSpace (Localization.Away D.s) := D.uniformSpace
      letI : IsUniformAddGroup (Localization.Away D.s) := D.isUniformAddGroup
      exact (UniformSpace.Completion.isUniformInducing_coe (Localization.Away D.s)).isInducing
    have hcoe_nhds : @nhds _ tLoc (0 : Localization.Away D.s) =
        Filter.comap D.coeRingHom (@nhds _ _ (0 : presheafValue D)) := by
      have := hcoe_ind.nhds_eq_comap (0 : Localization.Away D.s)
      rw [this, map_zero]
    rw [hcoe_nhds, Filter.mem_comap] at hψpre
    obtain ⟨O, hO, hO_sub⟩ := hψpre
    -- choose `k` with `image(P_T.I^k) ⊆ O` (basic `0`-nbhds of `presheafValue D`).
    obtain ⟨k, -, hk⟩ := P_T.hasBasis_nhds_zero.mem_iff.mp hO
    refine ⟨(MvTateAlgebra.mvTateAlgNhd m P_T k : Set _),
      (MvTateAlgebra.mvTateAlgBasis' m).hasBasis_nhds_zero.mem_of_mem (i := k) trivial, ?_⟩
    -- `iU p ∈ mvTateAlgNhd m P_T k` ⟹ `fU p ∈ Vg ⊆ V`.
    intro p hp
    rw [Set.mem_preimage]
    apply hVgV
    -- expand `fU p = ∑_{v ∈ supp p} ψγ(coeff_v p) · ∏ⱼ (fU Xⱼ)^(vⱼ)`.
    rw [show fU p = ∑ v ∈ p.support, ψγ (MvPolynomial.coeff v p) *
        ∏ j, fU (MvPolynomial.X j) ^ (v j) from by
      have hfe : fU p = MvPolynomial.eval₂ ψγ (fun j => fU (MvPolynomial.X j)) p := by
        have hvar : (fun j => fU (MvPolynomial.X j)) =
            (fun j => Ideal.Quotient.mk (RingHom.ker Ψ)
              (⟨MvPowerSeries.X (Fin.natAdd D.T.card j), MvPowerSeries.X_isRestricted _⟩ :
                restrictedMvPowerSeriesSubring (D.T.card + m) A)) := funext hfU_X
        rw [hvar]
        change (fU p : _) = _
        rw [show ⇑fU = MvPolynomial.eval₂ ψγ
          (fun j => Ideal.Quotient.mk (RingHom.ker Ψ)
            (⟨MvPowerSeries.X (Fin.natAdd D.T.card j), MvPowerSeries.X_isRestricted _⟩ :
              restrictedMvPowerSeriesSubring (D.T.card + m) A)) from
          MvPolynomial.coe_eval₂Hom _ _]
      rw [hfe, MvPolynomial.eval₂_eq']]
    -- each term lies in `Vg` (open subgroup), so the sum does.
    refine AddSubgroup.sum_mem _ (fun v hv => ?_)
    -- `coeff_v(iU p) = coeRingHom(coeff_v p) ∈ image(P_T.I^k) ⊆ O`, so `coeff_v p ∈ ψγ⁻¹ V'`.
    have hcoeffO : D.coeRingHom (MvPolynomial.coeff v p) ∈ O := by
      apply hk
      obtain ⟨bb, hbI, hbeq⟩ := MvTateAlgebra.mvTateAlgNhd_coeff_mem m P_T k hp v
      rw [← hiU_coeff p v, ← hbeq]
      exact ⟨bb, hbI, rfl⟩
    have hψV' : ψγ (MvPolynomial.coeff v p) ∈ V' := hO_sub hcoeffO
    -- term `= (∏ⱼ (fU Xⱼ)^vⱼ) · ψγ(coeff_v p) ∈ R_γ · V' ⊆ Vg`.
    rw [mul_comm]
    exact hV'R (Set.mul_mem_mul ⟨v, rfl⟩ hψV')
  -- round-trip on the dense subring: `ē ∘ f = i` as ring homs `U → T`.
  have hround_U : (ē.comp fU) = iU := by
    -- on the localization coefficients, `ē ∘ ψγ = const ∘ coeRingHom` (relative loc round-trip)
    have hψ_round : ē.comp ψγ =
        (algebraMap (presheafValue D) (restrictedMvPowerSeriesSubring m (presheafValue D))).comp
          D.coeRingHom := by
      apply IsLocalization.ringHom_ext (Submonoid.powers D.s)
      ext a
      simp only [RingHom.comp_apply, ψγ, IsLocalization.Away.lift_eq, hē, RingHom.kerLift_mk,
        hΨ, mvEvalHomBounded_algebraMap, g, RationalLocData.canonicalMap]
    refine MvPolynomial.ringHom_ext (fun c => ?_) (fun j => ?_)
    · rw [RingHom.comp_apply, hfU_C, hiU_C]
      exact RingHom.congr_fun hψ_round c
    · rw [RingHom.comp_apply, hfU_X, hiU_X, hē, RingHom.kerLift_mk, hΨ, mvEvalHomBounded_X]
      simp only [b, Fin.addCases_right]
  -- the backward map `T → γ`, extending `f` along the dense uniform embedding `i`.
  set backward : restrictedMvPowerSeriesSubring m (presheafValue D) →+*
      (restrictedMvPowerSeriesSubring (D.T.card + m) A ⧸ RingHom.ker Ψ) :=
    IsDenseInducing.extendRingHom hi_ind hi_dense hf_unif with hbackward
  -- `ē ∘ backward = id`: both continuous, and agree on the dense range of `iU`
  -- (`ē(backward(iU u)) = ē(fU u) = iU u`), so they coincide; hence `ē` is surjective.
  have hround : (ē.comp backward) = RingHom.id _ := by
    -- `ē` is continuous: it factors `Ψ` (continuous) through the open quotient map `mk`.
    have hē_cont : @Continuous _ _ τQ τT ⇑ē := by
      rw [hē]
      show @Continuous _ _ (mvQuotTopology (D.T.card + m) (RingHom.ker Ψ)) τT ⇑Ψ.kerLift
      rw [show (mvQuotTopology (D.T.card + m) (RingHom.ker Ψ)) =
            TopologicalSpace.coinduced (Ideal.Quotient.mk (RingHom.ker Ψ)) τS from rfl,
          continuous_coinduced_dom]
      have hcomp : (⇑Ψ.kerLift) ∘ (Ideal.Quotient.mk (RingHom.ker Ψ)) = ⇑Ψ := by
        funext h; exact RingHom.kerLift_mk Ψ h
      rw [hcomp, hΨ]
      exact mvEvalHomBounded_continuous g hg b hb
    -- `backward` is continuous: the uniform dense extension of the uniformly continuous `fU`.
    have hbc : Continuous (⇑backward) :=
      (uniformContinuous_uniformly_extend hi_ind hi_dense hf_unif).continuous
    -- `backward ∘ iU = fU` on the dense subring (`extend_eq`).
    have hag : ∀ u, backward (iU u) = fU u :=
      fun u => (hi_ind.isDenseInducing hi_dense).extend_eq hf_unif.continuous u
    -- `ē ∘ backward` and `id` are continuous and agree on the dense `range iU`, hence equal.
    have hfun : (⇑ē ∘ ⇑backward) =
        (id : restrictedMvPowerSeriesSubring m (presheafValue D) → _) :=
      DenseRange.equalizer hi_dense (hē_cont.comp hbc) continuous_id (by
        funext u
        show ē (backward (iU u)) = iU u
        rw [hag u]
        exact RingHom.congr_fun hround_U u)
    refine RingHom.ext fun x => ?_
    have hx := congr_fun hfun x
    simpa using hx
  intro y
  exact ⟨backward y, by
    have := RingHom.congr_fun hround y
    simpa using this⟩

omit [CompatiblePlusSubring A] in
/-- **Example 6.38, strong-noetherian propagation** (Wedhorn p. 56: "In particular, `Â⟨T/s⟩` is
again strongly noetherian"). FAITHFUL: `A` strongly noetherian ⟹ `presheafValue D` strongly
noetherian, with NO noetherian ring of definition. **This REPLACES the false
`isStronglyNoetherian_of_isNoetherianRing_isTateRing`** (the bare "noetherian + Tate ⟹ strongly
noetherian", a B2 defect — reviewer-confirmed false 2026-06-05, Wedhorn Remark 6.37 is one-way) on
the Prop 8.30 flatness path. Each `restrictedMvPowerSeriesSubring m (presheafValue D)` is a
surjective image of the noetherian `restrictedMvPowerSeriesSubring (|D.T|+m) A` — noetherian by
`A`'s *strong* noetherianity (`IsStronglyNoetherian.isNoetherianRing_restricted`), NOT by
ring-noetherianity of `presheafValue D` — via `presheafValue_mvRestricted_surjection`. The single
residual is that relative surjection; this assembly is otherwise sorry-free. -/
theorem presheafValue_isStronglyNoetherian_faithful
    [IsTateRing A] [IsNoetherianRing A] [IsStronglyNoetherian A] (D : RationalLocData A) :
    IsStronglyNoetherian (presheafValue D) := by
  refine ⟨fun m => ?_⟩
  haveI : IsNoetherianRing (restrictedMvPowerSeriesSubring (D.T.card + m) A) :=
    IsStronglyNoetherian.isNoetherianRing_restricted (A := A) (D.T.card + m)
  obtain ⟨φ, hφ⟩ := presheafValue_mvRestricted_surjection D m
  exact isNoetherianRing_of_surjective _ _ φ hφ

-- REMOVED (2026-06-03): `presheafValue_isLinearTopology_{residual,faithful}` asserted
-- `IsLinearTopology (presheafValue D)`, which is FALSE for a Tate ring (no proper open ideals,
-- since a topologically nilpotent unit puts a unit in every open ideal). After the A°-layer
-- migration (`IsLinearTopology A A` → `NonarchimedeanAddGroup`, Wedhorn Prop 5.30), `lemma_8_31_*`
-- over the base `B := presheafValue D` no longer require `[IsLinearTopology B B]`, so this false
-- obligation is gone — `prop_8_30_flat_of_faithful_base` now needs only the Tate + noetherian
-- instances on `B`.

/-! ### Prop 8.30 — historical decomposition notes (superseded below)

**GENUINE RESIDUAL — the Remark-7.55 relative reduction object for Prop 8.30**
(Wedhorn p. 81, `wedhorn.txt:4100`–`4104`, and Remark 7.55, `wedhorn.txt:3504`–`3517`).

NOTE (this session): the obstruction-1 verdict below ("the engine needs `[PlusSubring B]`") was
EMPIRICALLY REFUTED. The engine `presheafValue_flat_of_canonical_faithful` was `omit`-cleaned of
`[CompatiblePlusSubring A]` and `[HasLocLiftPowerBounded A]` (and its round-trip helpers along with
it): it needs only `[IsStronglyNoetherian B]` + `[IsHuberRing B]` + `[PlusSubring B]`, ALL available
at `B := presheafValue E` — so it is now directly instantiable at the base with NO false
`CompatiblePlusSubring B` class (that class is false-in-general for a completion, as
`RationalLocData.P` ranges over arbitrary pairs). The faithful per-step flat engine
`prop_8_30_basic_laurent_step_flat` is now written with sorry-free flat-transport logic (it carries
`sorryAx` only through the pre-existing upstream Wedhorn-6.18 `isStronglyNoetherian` residual). The
sole remaining NEW residual is the geometric chain `prop_8_30_remark755_chain`. See those
declarations' docstrings for the corrected, current account.

`B := presheafValue D = O_X(V)` is a complete strongly noetherian Tate ring (Step 1), supplied
here as the explicit FAITHFUL instance bundle: `IsTateRing B`, `IsNoetherianRing B`,
`NonarchimedeanRing B`, `T2Space B`, `IsHuberRing B`, `IsStronglyNoetherian B` — all derived from
`hTate`/`hNoeth` and the plain `presheafValue` instances, with NO `PairOfDefinition`, NO
`[IsNoetherianRing P.A₀]`.

Wedhorn: "By Remark 7.55 we may assume `U` is `U₁ = R(f/1)` or `U₂ = R(1/f)` for some `f ∈ B`.
In Example 6.38 we have seen `O_X(U₁) = B̂⟨X⟩/(f−X)` and `O_X(U₂) = B̂⟨X⟩/(1−fX)`." Remark 7.55
(`wedhorn.txt:3517`) is a **chain** `Spa B ⊇ X₀ ⊇ X₁ ⊇ ⋯ ⊇ Xₙ = U`: `X₀ = {1 ≤ x(s/u)}` for a
dominating unit `u ∈ B×` (Cor 7.32, `cor_7_32_dominating_unit`), and `Xᵢ = {x(tᵢ/s) ≤ 1}` adds one
generator. Flatness of `O_X(V) → O_X(U)` is the **composite** of the basic-Laurent restrictions.

**Discharged engine (this session).** The *per-step flatness* engine is now FAITHFULLY present and
sorry-free:
* `lemma_8_31_oneSubfX_flat`/`lemma_8_31_fSubX_flat` — `B⟨X⟩/(1−fX)`, `B⟨X⟩/(f−X)` flat over `B`
  (case (b), `[IsNoetherianRing B]` only, NO noeth-`A₀`).
* `presheafValueCanonicalQuotientEquiv_faithful` (+ `_canonicalMap`) — the faithful Example-6.38 iso
  `O_X(W) ≃+* B⟨X⟩/(1−sX)` intertwining `canonicalMap`, `[IsStronglyNoetherian B]` only.
* `presheafValue_flat_of_canonical_faithful` — assembles the two into `Module.Flat B (O_X(W))` along
  `canonicalMap` for any LaurentNormalized `W` (the FAITHFUL replacement for the case-(a)
  `presheafValue_flat_of_canonical → flat_quotient_oneSubfX_general P`, which needs
  `[IsNoetherianRing P.A₀]` and is ℂ_p-false; that route is NOT used).

**DONE this session — the relative apparatus is now noeth-`A₀`-free.** The repo's relative-Example-6.38
machinery (`relativeRationalLocData_laurentNormalized`, `relativeLaurentNormalized_equiv`,
`relativeLaurentNormalized_equiv_intertwine`, and the whole forward/backward hom chain in
`RelativeRationalLocData.lean`) has been **retyped** to drop the dead case-(a) plumbing
`(P : PairOfDefinition A) [IsNoetherianRing P.A₀]` and `[IsNoetherianRing (locSubring E.P E.T E.s)]`,
re-routing the relative pair through the faithful `presheafValue_concretePair`/
`presheafValue_isTateRing_concrete` (`PresheafTateStructure.lean`, defeq to the entangled
`presheafValue_pairOfDefinition_concrete P E` by proof irrelevance). So
`relativeLaurentNormalized_equiv D D' h : presheafValue D' ≃+* presheafValue X̄'` (with
`X̄' := relativeRationalLocData_laurentNormalized D D' h : RationalLocData B`,
`LaurentNormalized D'` hypothesis) and its `restrictionMapHom`-intertwining are now available with
**NO** noeth-`A₀`. The whole project builds green after this retype.

**TWO genuine obstructions remain**, both isolated here as the single named residual:

1. **The faithful Example-6.38 iso `presheafValueCanonicalQuotientEquiv_faithful` (and hence the flat
   engine `presheafValue_flat_of_canonical_faithful`) is NOT instantiable at the base
   `B := presheafValue D`**, because it genuinely depends on `[PlusSubring A]` (the `A⁺`-structure),
   which `B` does not carry (its only global instances are
   `CommRing/TopologicalSpace/UniformSpace/IsTopologicalRing/CompleteSpace/T0Space`,
   `Presheaf.lean:220`–`247`). The dependence is **real, not superficial threading**: the iso's
   round-trip fields (`tateQuotientToPresheaf_comp_faithful` / `presheafToCanonicalQuotient_comp_faithful`)
   invoke `locToQuotientOneSubfX_gen_denseRange_canonical` — the Example-6.38 **density** of `A[M]`
   (`M = {tᵢ/s}`) in `Â⟨T/s⟩` — whose proof fundamentally uses the `+`-subring structure
   (`[PlusSubring A]`). *Verified this session:* (a) the forward-map continuity lemmas
   `locToQuotientOneSubfX_gen_divByS`, `locToQuotientOneSubfX_gen_continuous_canonical`
   (`TopologyComparison.lean`) were successfully `omit`-cleaned of `[PlusSubring A] [IsHuberRing A]`
   (they genuinely don't use them — a small faithful improvement landed this session); but (b)
   `omit [PlusSubring A]` on the round-trip helpers fails at the `locToQuotientOneSubfX_gen_denseRange_canonical`
   call (`failed to synthesize PlusSubring A`). [`IsHuberRing B` is *not* the blocker — it is available
   in this context via `hTate.toIsHuberRing` — and `HasLocLiftPowerBounded B` is not needed by the engine;
   the genuine wall is `[PlusSubring B]` through density.] Closing this requires either omit-cleaning the
   Example-6.38 **density** chain of `[PlusSubring A]` (`locToQuotientOneSubfX_gen_denseRange_canonical`
   and its `TopologyComparison`/`PresheafIdentification` dependencies — substantial, since density of
   `A[M]` is where `A⁺` enters), or constructing a faithful `[PlusSubring (presheafValue D)]` instance
   (the canonical `A⁺` on a completion of a localization — not currently in the repo).

2. **The Remark-7.55 chain decomposition** (arbitrary `D' ⊆ D` into a chain `V = X₀ ⊇ X₁ ⊇ ⋯ ⊇ Xₙ
   = U` of LaurentNormalized basic-Laurent steps over intermediate bases, composed by
   `Module.Flat.trans`) is not yet a usable theorem in the repo. A faithful single-step lemma — for
   LaurentNormalized `D'`, via the (now noeth-`A₀`-free) `relativeLaurentNormalized_equiv` + the flat
   engine of obstruction 1 (over `B`) + `Module.Flat.of_linearEquiv`, with `hb`/`hT_pb` from
   `invS_isPowerBounded_of_one_mem_T` / `canonicalMap_isPowerBounded_of_mem_A₀` — is **not yet
   written** (it is blocked on obstruction 1); it would discharge each chain step, after which the
   chain reduction folds the steps by `Module.Flat.trans`. `cor_7_32_dominating_unit`
   (`WedhornCechAcyclicity.lean:1305`, sorry-free) supplies the `X₀` dominating unit, but the
   inductive `Xᵢ`-chain object + the per-step ambient-↔-relative intertwining bookkeeping for an
   arbitrary `D'` is the missing geometric content.

(Note: `prop_8_30_flat_clean` in `StructureSheaf.lean` has this exact signature but is OFF-LIMITS:
it routes through `restrictionMap_isLocalization` = the RETIRED `restrictionMapHom_surj`,
FALSE-in-general, plus a FALSE noeth-`A₀` `sorry`.) -/

/-! ## Prop 8.30 per-step engine + Remark-7.55 chain + Cor 8.32 — RELOCATED (2026-06-11)

`prop_8_30_basic_laurent_step_flat`, `prop_8_30_remark755_chain` (+ consumers
`prop_8_30_relative_laurent_flat`, `prop_8_30_flat_of_faithful_base`,
`prop_8_30_restriction_flat`) and the Cor 8.32 block now live in
`RelativePieceKeystone.lean`: the Remark-7.55 chain is discharged there through the
8.16-keystone `relativePiece_equiv` (general-piece base change), which is defined
downstream of this file. -/


/-! ## Lemma 8.33 — the 2-element Laurent cover is `O_X`-acyclic

> **Lemma 8.33.** Let `A` be a strongly noetherian Tate affinoid ring, `f ∈ A`,
> `U₁ = {x : x(f) ≤ 1}`, `U₂ = {x : x(f) ≥ 1}`. Then the augmented Čech complex
> `0 → O_X(X) → O_X(U₁) × O_X(U₂) → O_X(U₁ ∩ U₂) → 0` is exact.

Via the explicit identifications (Examples 6.38, 6.39)
`O_X(U₁) = A⟨ζ⟩/(f−ζ)`, `O_X(U₂) = A⟨η⟩/(1−fη)`, `O_X(U₁∩U₂) = A⟨ζ,ζ⁻¹⟩/(f−ζ)`,
and the `λ`/`λ'`/`ι` diagram chase (injectivity of `ε` from Cor 8.32; surjectivity of `λ`,
`λ'`; `im ι = ker λ`). Stated here as the `IsSheafy` content (separation + gluing) for the
2-element Laurent cover `Uf`. -/
-- DELETED 2026-06-09 (`/develop --decompose` L-DEFECT): the former
-- `lemma_8_33_laurent_cover_gluing` here carried an `(hC : True)` placeholder (which pinned
-- nothing — it claimed gluing for an arbitrary `C` mislabelled "the Laurent cover `U_f`"), was
-- referenced nowhere, and duplicated the genuine Lemma 8.33 content that lives in
-- `WedhornCechAcyclicity.lean` (`laurentRationalCover`, `laurentProdCoverOf_isOXAcyclic`, the
-- `isOXAcyclic` engine). The faithful gluing route for `lemma_8_34_gluing` is the `O_X`-acyclicity
-- chain there (Wedhorn 8.34 (i)–(iv) + Prop A.3 + Cor 7.32 + Lemma 7.54), not a disconnected
-- gluing-form stub. See `.mathlib-quality/decomposition-gluing.md`.

/-! ## Lemma 8.34 (gluing) + Theorem 8.28(b) — RELOCATED (2026-06-11)

`lemma_8_34_gluing` and the headline assembly `isSheafy_of_stronglyNoetherian_828b`
now live at the end of `WedhornCechAcyclicity.lean`: the gluing leaf is DISCHARGED
there from the proven general-base acyclicity `every_rational_cover_is_OXAcyclic`
(Wedhorn 7.54 + 8.34(i)–(iv) + Prop A.3 + the R2-transport via Prop 8.16), and the
import direction (`WedhornCechAcyclicity` imports this file for the Cor-8.32
embedding half) forces the assembly to live there. -/


/-! ### Example 6.38 explicit kernel — relocated from `WedhornCechAcyclicity`

The faithful `R(f/1)`/`R(1/f)` quotient isomorphisms `presheafValue (unitDatum P b) ≃+*
A⟨ζ⟩/(b − ζ)` (and the minus form) — Wedhorn Example 6.38/6.39. Moved up from
`WedhornCechAcyclicity` so the upstream Remark-7.55 per-step flatness engine in
`RelativePieceKeystone` can consume them. All dependencies (`example638_evalHom*`,
`mvQuot*`) live in this file or `MvTateAlgebraTopology`. -/

omit [CompatiblePlusSubring A] in
set_option linter.unusedSectionVars false in
/-- For the plus-half `unitDatum P b` (`T = {b}`, `s = 1`), the unique rational
generator is `b/1 = canonicalMap b`. -/
theorem unitDatum_genTuple_eq [IsTateRing A] [IsNoetherianRing A]
    (P : PairOfDefinition A) (b : A) (i : Fin (unitDatum P b).T.card) :
    example638_genTuple (unitDatum P b) i = (unitDatum P b).canonicalMap b := by
  have hval : ((((unitDatum P b).T.equivFin.symm i) :
      ((unitDatum P b).T : Finset A)) : A) = b :=
    Finset.mem_singleton.mp ((unitDatum P b).T.equivFin.symm i).2
  show (unitDatum P b).coeRingHom (divByS _ (unitDatum P b).s) = _
  rw [hval]
  show (unitDatum P b).coeRingHom (divByS b 1) = _
  rw [divByS_eq_algebraMap]
  rfl

omit [CompatiblePlusSubring A] in
set_option linter.unusedSectionVars false in
/-- For the minus-half `coUnitDatum P b` (`T = {1}`, `s = b`), the unique rational
generator is `1/b`. -/
theorem coUnitDatum_genTuple_eq [IsTateRing A] [IsNoetherianRing A]
    (P : PairOfDefinition A) (b : A) (i : Fin (coUnitDatum P b).T.card) :
    example638_genTuple (coUnitDatum P b) i =
      (coUnitDatum P b).coeRingHom (divByS 1 b) := by
  have hval : ((((coUnitDatum P b).T.equivFin.symm i) :
      ((coUnitDatum P b).T : Finset A)) : A) = 1 :=
    Finset.mem_singleton.mp ((coUnitDatum P b).T.equivFin.symm i).2
  show (coUnitDatum P b).coeRingHom (divByS _ (coUnitDatum P b).s) = _
  rw [hval]
  rfl

omit [CompatiblePlusSubring A] in
set_option linter.unusedSectionVars false in
/-- `⊇` of (8.2.1)-plus: the generator `algebraMap b − ζ` is killed by the
evaluation (`ζ ↦ b/1 = canonicalMap b`, `example638_evalHom_X` +
`unitDatum_genTuple_eq`). -/
theorem unitDatum_span_le_ker
    [IsTateRing A] [IsNoetherianRing A] [IsStronglyNoetherian A] [T2Space A]
    [NonarchimedeanRing A] [HasLocLiftPowerBounded A]
    [letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A;
      CompleteSpace A]
    (P : PairOfDefinition A) (b : A) :
    Ideal.span {algebraMap A ↥(TateAlgebra A) b - TateAlgebra.X} ≤
      RingHom.ker (example638_evalHom (unitDatum P b)) := by
  rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker]
  erw [map_sub, example638_evalHom_algebraMap,
    example638_evalHom_X (unitDatum P b) ((0 : Fin 1) : Fin (unitDatum P b).T.card),
    unitDatum_genTuple_eq]
  exact sub_self _

omit [CompatiblePlusSubring A] in
set_option linter.unusedSectionVars false in
/-- `⊇` of (8.2.1)-minus: the generator `1 − algebraMap b · η` is killed by the
evaluation (`η ↦ 1/b`, and `b · (1/b) = 1` in the localization). -/
theorem coUnitDatum_span_le_ker
    [IsTateRing A] [IsNoetherianRing A] [IsStronglyNoetherian A] [T2Space A]
    [NonarchimedeanRing A] [HasLocLiftPowerBounded A]
    [letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A;
      CompleteSpace A]
    (P : PairOfDefinition A) (b : A) :
    Ideal.span {1 - algebraMap A ↥(TateAlgebra A) b * TateAlgebra.X} ≤
      RingHom.ker (example638_evalHom (coUnitDatum P b)) := by
  rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker]
  erw [map_sub, map_one, map_mul, example638_evalHom_algebraMap,
    example638_evalHom_X (coUnitDatum P b) ((0 : Fin 1) : Fin (coUnitDatum P b).T.card),
    coUnitDatum_genTuple_eq]
  -- `canonicalMap b · (1/b) = (b/1)·(1/b) = b/b = 1` in the localization image.
  have hmul : (coUnitDatum P b).canonicalMap b *
      (coUnitDatum P b).coeRingHom (divByS 1 b) = 1 := by
    show (coUnitDatum P b).coeRingHom (algebraMap A (Localization.Away b) b) *
        (coUnitDatum P b).coeRingHom (divByS 1 b) = 1
    rw [← map_mul, ← map_one (coUnitDatum P b).coeRingHom]
    congr 1
    unfold divByS
    exact (IsLocalization.mk'_spec' (Localization.Away b) 1
      ⟨b, Submonoid.mem_powers b⟩).trans (map_one _)
  rw [hmul, sub_self]

omit [CompatiblePlusSubring A] in
set_option maxHeartbeats 1000000 in
set_option linter.unusedSectionVars false in
/-- `⊆` of (8.2.1)-plus — the completion comparison. The quotient
`A⟨ζ⟩ ⧸ (b − ζ)` is complete Hausdorff (the principal ideal is closed by Prop 6.17
over the strongly noetherian base); the localization `A[1/s] = A[1/1]` lifts to it
continuously (`s = 1` is trivially a unit mod the ideal); the lift extends to the
completion `presheafValue (unitDatum P b)` (`UniformSpace.Completion.extensionHom`);
and the extension factors `mk` through `example638_evalHom` on the dense polynomial
subring (`mvPolynomialToTate_denseRange`). Hence `evalHom h = 0 ⟹ mk h = 0`. -/
theorem unitDatum_ker_le_span
    [IsTateRing A] [IsNoetherianRing A] [IsStronglyNoetherian A] [T2Space A]
    [NonarchimedeanRing A] [HasLocLiftPowerBounded A]
    [letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A;
      CompleteSpace A]
    (P : PairOfDefinition A) (b : A) :
    RingHom.ker (example638_evalHom (unitDatum P b)) ≤
      Ideal.span {algebraMap A ↥(TateAlgebra A) b - TateAlgebra.X} := by
  classical
  set D := unitDatum P b with hD
  set aI : Ideal ↥(restrictedMvPowerSeriesSubring 1 A) :=
    Ideal.span {algebraMap A ↥(TateAlgebra A) b - TateAlgebra.X} with haI
  -- source instances
  letI τC : TopologicalSpace ↥(restrictedMvPowerSeriesSubring 1 A) :=
    MvTateAlgebra.mvTateAlgebraTopology' 1
  haveI hringC : IsTopologicalRing ↥(restrictedMvPowerSeriesSubring 1 A) :=
    MvTateAlgebra.mvTateAlgebraTopology'_isTopologicalRing 1
  have hA_complete : @CompleteSpace A (IsTopologicalAddGroup.rightUniformSpace A) := ‹_›
  have haI_closed : IsClosed (aI : Set ↥(restrictedMvPowerSeriesSubring 1 A)) :=
    MvTateAlgebra.mvTate_isClosed_ideal 1 hA_complete aI
  -- quotient instances (complete Hausdorff topological ring)
  letI τQ : TopologicalSpace (↥(restrictedMvPowerSeriesSubring 1 A) ⧸ aI) :=
    mvQuotTopology 1 aI
  letI uQ : UniformSpace (↥(restrictedMvPowerSeriesSubring 1 A) ⧸ aI) :=
    mvQuotUniformSpace 1 aI
  haveI hringQ : @IsTopologicalRing _ τQ _ := mvQuot_isTopologicalRing 1 aI
  haveI : @IsUniformAddGroup _ uQ _ := mvQuot_isUniformAddGroup 1 aI
  haveI : @CompleteSpace _ uQ := mvQuot_completeSpace 1 aI hA_complete
  haveI hT2Q : @T2Space _ τQ := mvQuot_t2Space 1 aI haI_closed
  haveI : @T0Space _ τQ := @T1Space.t0Space _ τQ (@T2Space.t1Space _ τQ hT2Q)
  haveI hNAQ : @NonarchimedeanRing _ _ τQ := mvQuot_nonarchimedean 1 aI
  -- the localization lift `ψ` (the denominator `D.s = 1` is trivially a unit)
  have hUnit1 : IsUnit ((Ideal.Quotient.mk aI).comp
      (algebraMap A ↥(restrictedMvPowerSeriesSubring 1 A)) D.s) := by
    show IsUnit ((Ideal.Quotient.mk aI).comp
      (algebraMap A ↥(restrictedMvPowerSeriesSubring 1 A)) 1)
    rw [map_one]; exact isUnit_one
  set ψ : Localization.Away D.s →+* (↥(restrictedMvPowerSeriesSubring 1 A) ⧸ aI) :=
    IsLocalization.Away.lift (x := D.s)
      (g := (Ideal.Quotient.mk aI).comp
        (algebraMap A ↥(restrictedMvPowerSeriesSubring 1 A))) hUnit1 with hψ
  have hψ_alg : ∀ x : A, ψ (algebraMap A (Localization.Away D.s) x) =
      Ideal.Quotient.mk aI (algebraMap A ↥(restrictedMvPowerSeriesSubring 1 A) x) := by
    intro x
    rw [hψ, IsLocalization.Away.lift_eq]
    rfl
  -- the key congruence: `mk (algebraMap b) = mk ζ` modulo the principal ideal
  have hmk_bX : Ideal.Quotient.mk aI (algebraMap A ↥(restrictedMvPowerSeriesSubring 1 A) b) =
      Ideal.Quotient.mk aI (⟨MvPowerSeries.X (0 : Fin 1), MvPowerSeries.X_isRestricted 0⟩ :
        ↥(restrictedMvPowerSeriesSubring 1 A)) := by
    rw [Ideal.Quotient.eq]
    exact Ideal.subset_span (Set.mem_singleton _)
  -- `ψ` is continuous for the localization topology
  have hψ_cont : @Continuous _ _ D.topology τQ ψ := by
    change @Continuous _ _ (locTopology D.P D.T D.s D.hopen) τQ ψ
    refine locTopology_continuous_lift D.P D.T D.s D.hopen ψ ?_ ?_
    · have heq : ψ.comp (algebraMap A (Localization.Away D.s)) =
          (Ideal.Quotient.mk aI).comp
            (algebraMap A ↥(restrictedMvPowerSeriesSubring 1 A)) := by
        ext x; exact hψ_alg x
      rw [heq]
      exact continuous_quotient_mk'.comp
        (MvTateAlgebra.mvTateAlgebra_algebraMap_continuous (A := A) 1)
    · intro t ht
      rw [show (D.T : Finset A) = {b} from rfl, Finset.mem_singleton] at ht
      subst ht
      have h1 : ψ (divByS t D.s) = Ideal.Quotient.mk aI
          (⟨MvPowerSeries.X (0 : Fin 1), MvPowerSeries.X_isRestricted 0⟩ :
            ↥(restrictedMvPowerSeriesSubring 1 A)) := by
        erw [divByS_eq_algebraMap, hψ_alg]
        exact hmk_bX
      rw [h1]
      exact isPowerBounded_map_of_isOpenMap (Ideal.Quotient.mk aI)
        continuous_quotient_mk' (@QuotientRing.isOpenMap_coe _ τC _ aI hringC)
        (MvTateAlgebra.mvPowerSeries_X_isBounded (0 : Fin 1))
  -- Opaquify the evaluation as a `Fin 1`-typed hom `Φ`: the `D.T.card ≡ 1` defeq is
  -- paid ONCE here; every later composite is then cheaply `Fin 1`-typed (leaving the
  -- evaluation at the `D.T.card`-type makes each `RingHom.comp` unification re-pay
  -- the structural defeq and blow up `whnf`).
  obtain ⟨Φ, hΦ_cont, hΦ_alg, hΦ_X, hΦ_ker⟩ :
      ∃ Φ : ↥(restrictedMvPowerSeriesSubring 1 A) →+* presheafValue D,
        @Continuous _ _ τC _ ⇑Φ ∧
        (∀ x : A, Φ (algebraMap A ↥(restrictedMvPowerSeriesSubring 1 A) x) =
          D.canonicalMap x) ∧
        (Φ (⟨MvPowerSeries.X (0 : Fin 1), MvPowerSeries.X_isRestricted 0⟩ :
            ↥(restrictedMvPowerSeriesSubring 1 A)) =
          D.coeRingHom (algebraMap A (Localization.Away D.s) b)) ∧
        RingHom.ker (example638_evalHom D) = RingHom.ker Φ := by
    refine ⟨example638_evalHom D, example638_evalHom_continuous D,
      fun x => example638_evalHom_algebraMap D x, ?_, rfl⟩
    erw [example638_evalHom_X D ((0 : Fin 1) : Fin D.T.card), unitDatum_genTuple_eq]
    rfl
  -- extend to the completion, then make the extension OPAQUE (an existential
  -- `obtain` yields a fresh `β` carrying only the two facts the rest needs —
  -- unfolding the `extensionHom` term in every later unification blows up `whnf`)
  letI : UniformSpace (Localization.Away D.s) := D.uniformSpace
  letI : IsTopologicalRing (Localization.Away D.s) := D.isTopologicalRing
  letI : IsUniformAddGroup (Localization.Away D.s) := D.isUniformAddGroup
  obtain ⟨β, hβ_coe, hβ_cont⟩ :
      ∃ β : presheafValue D →+* (↥(restrictedMvPowerSeriesSubring 1 A) ⧸ aI),
        (∀ y : Localization.Away D.s, β (D.coeRingHom y) = ψ y) ∧
          @Continuous _ _ _ τQ ⇑β := by
    refine ⟨@UniformSpace.Completion.extensionHom (Localization.Away D.s) _ D.uniformSpace _ _
      (↥(restrictedMvPowerSeriesSubring 1 A) ⧸ aI) uQ _ (mvQuot_isUniformAddGroup 1 aI)
      (mvQuot_isTopologicalRing 1 aI) ψ hψ_cont ‹_› ‹_›, fun y => ?_, ?_⟩
    · exact @UniformSpace.Completion.extensionHom_coe (Localization.Away D.s) _ D.uniformSpace
        _ _ (↥(restrictedMvPowerSeriesSubring 1 A) ⧸ aI) uQ _ (mvQuot_isUniformAddGroup 1 aI)
        (mvQuot_isTopologicalRing 1 aI) ψ hψ_cont ‹_› ‹_› y
    · exact @UniformSpace.Completion.continuous_extension (Localization.Away D.s)
        D.uniformSpace _ uQ (⇑ψ) ‹_›
  -- `β ∘ Φ = mk` (continuous ring homs agreeing on the dense polynomials)
  have hext : (⇑β ∘ ⇑Φ :
      ↥(restrictedMvPowerSeriesSubring 1 A) → _) = ⇑(Ideal.Quotient.mk aI) := by
    refine Continuous.ext_on
      (MvTateAlgebra.mvPolynomialToTate_denseRange (A := A) 1)
      (hβ_cont.comp hΦ_cont) continuous_quotient_mk' ?_
    rintro _ ⟨p, rfl⟩
    have hcomp : ((β.comp Φ).comp
        (MvTateAlgebra.mvPolynomialToTate (A := A) 1)) =
        (Ideal.Quotient.mk aI).comp (MvTateAlgebra.mvPolynomialToTate (A := A) 1) := by
      refine MvPolynomial.ringHom_ext (fun c => ?_) (fun j => ?_)
      · simp only [RingHom.comp_apply, MvTateAlgebra.mvPolynomialToTate_C]
        rw [hΦ_alg]
        show β (D.coeRingHom (algebraMap A (Localization.Away D.s) c)) = _
        rw [hβ_coe, hψ_alg]
      · simp only [RingHom.comp_apply, MvTateAlgebra.mvPolynomialToTate_X]
        have hj : j = 0 := Subsingleton.elim j 0
        subst hj
        rw [hΦ_X, hβ_coe, hψ_alg, hmk_bX]
    exact RingHom.congr_fun hcomp p
  -- conclude: `Φ h = 0 ⟹ mk h = 0 ⟹ h ∈ span`
  rw [hΦ_ker]
  intro h hh
  have hh' : Φ h = 0 := hh
  have hfun := congrFun hext h
  simp only [Function.comp_apply, hh', map_zero] at hfun
  exact Ideal.Quotient.eq_zero_iff_mem.mp hfun.symm

omit [CompatiblePlusSubring A] in
set_option maxHeartbeats 1000000 in
set_option linter.unusedSectionVars false in
/-- `⊆` of (8.2.1)-minus — the completion comparison, mirror of
`unitDatum_ker_le_span`. Here `s = b` and the lift exists because `b` is a unit
modulo `(1 − bη)` (with inverse `η`). -/
theorem coUnitDatum_ker_le_span
    [IsTateRing A] [IsNoetherianRing A] [IsStronglyNoetherian A] [T2Space A]
    [NonarchimedeanRing A] [HasLocLiftPowerBounded A]
    [letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A;
      CompleteSpace A]
    (P : PairOfDefinition A) (b : A) :
    RingHom.ker (example638_evalHom (coUnitDatum P b)) ≤
      Ideal.span {1 - algebraMap A ↥(TateAlgebra A) b * TateAlgebra.X} := by
  classical
  set D := coUnitDatum P b with hD
  set aI : Ideal ↥(restrictedMvPowerSeriesSubring 1 A) :=
    Ideal.span {1 - algebraMap A ↥(TateAlgebra A) b * TateAlgebra.X} with haI
  letI τC : TopologicalSpace ↥(restrictedMvPowerSeriesSubring 1 A) :=
    MvTateAlgebra.mvTateAlgebraTopology' 1
  haveI hringC : IsTopologicalRing ↥(restrictedMvPowerSeriesSubring 1 A) :=
    MvTateAlgebra.mvTateAlgebraTopology'_isTopologicalRing 1
  have hA_complete : @CompleteSpace A (IsTopologicalAddGroup.rightUniformSpace A) := ‹_›
  have haI_closed : IsClosed (aI : Set ↥(restrictedMvPowerSeriesSubring 1 A)) :=
    MvTateAlgebra.mvTate_isClosed_ideal 1 hA_complete aI
  letI τQ : TopologicalSpace (↥(restrictedMvPowerSeriesSubring 1 A) ⧸ aI) :=
    mvQuotTopology 1 aI
  letI uQ : UniformSpace (↥(restrictedMvPowerSeriesSubring 1 A) ⧸ aI) :=
    mvQuotUniformSpace 1 aI
  haveI hringQ : @IsTopologicalRing _ τQ _ := mvQuot_isTopologicalRing 1 aI
  haveI : @IsUniformAddGroup _ uQ _ := mvQuot_isUniformAddGroup 1 aI
  haveI : @CompleteSpace _ uQ := mvQuot_completeSpace 1 aI hA_complete
  haveI hT2Q : @T2Space _ τQ := mvQuot_t2Space 1 aI haI_closed
  haveI : @T0Space _ τQ := @T1Space.t0Space _ τQ (@T2Space.t1Space _ τQ hT2Q)
  haveI hNAQ : @NonarchimedeanRing _ _ τQ := mvQuot_nonarchimedean 1 aI
  -- `mk (algebraMap b) · mk η = 1` modulo `(1 − bη)`
  have hmkX_mul : Ideal.Quotient.mk aI
        (algebraMap A ↥(restrictedMvPowerSeriesSubring 1 A) b) *
      Ideal.Quotient.mk aI
        (⟨MvPowerSeries.X (0 : Fin 1), MvPowerSeries.X_isRestricted 0⟩ :
          ↥(restrictedMvPowerSeriesSubring 1 A)) = 1 := by
    rw [← map_mul, show (1 : ↥(restrictedMvPowerSeriesSubring 1 A) ⧸ aI) =
      Ideal.Quotient.mk aI 1 from (map_one _).symm, Ideal.Quotient.eq]
    have hgen : (1 - algebraMap A ↥(restrictedMvPowerSeriesSubring 1 A) b *
        (⟨MvPowerSeries.X (0 : Fin 1), MvPowerSeries.X_isRestricted 0⟩ :
          ↥(restrictedMvPowerSeriesSubring 1 A))) ∈ aI :=
      Ideal.subset_span (Set.mem_singleton _)
    have hneg := aI.neg_mem hgen
    rwa [neg_sub] at hneg
  -- the localization lift `ψ` (`D.s = b` is a unit mod `(1 − bη)`)
  have hUnitb : IsUnit ((Ideal.Quotient.mk aI).comp
      (algebraMap A ↥(restrictedMvPowerSeriesSubring 1 A)) D.s) := by
    rw [isUnit_iff_exists_inv]
    exact ⟨Ideal.Quotient.mk aI
      (⟨MvPowerSeries.X (0 : Fin 1), MvPowerSeries.X_isRestricted 0⟩ :
        ↥(restrictedMvPowerSeriesSubring 1 A)), hmkX_mul⟩
  set ψ : Localization.Away D.s →+* (↥(restrictedMvPowerSeriesSubring 1 A) ⧸ aI) :=
    IsLocalization.Away.lift (x := D.s)
      (g := (Ideal.Quotient.mk aI).comp
        (algebraMap A ↥(restrictedMvPowerSeriesSubring 1 A))) hUnitb with hψ
  have hψ_alg : ∀ x : A, ψ (algebraMap A (Localization.Away D.s) x) =
      Ideal.Quotient.mk aI (algebraMap A ↥(restrictedMvPowerSeriesSubring 1 A) x) := by
    intro x
    rw [hψ, IsLocalization.Away.lift_eq]
    rfl
  -- `ψ (1/b) = mk η` (cancel the unit `mk (algebraMap b)`)
  have hψ_div : ψ (divByS (1 : A) D.s) = Ideal.Quotient.mk aI
      (⟨MvPowerSeries.X (0 : Fin 1), MvPowerSeries.X_isRestricted 0⟩ :
        ↥(restrictedMvPowerSeriesSubring 1 A)) := by
    have hloc : algebraMap A (Localization.Away D.s) b * divByS (1 : A) D.s = 1 := by
      erw [show divByS (1 : A) D.s = IsLocalization.mk' (Localization.Away b) (1 : A)
        (⟨b, Submonoid.mem_powers b⟩ : Submonoid.powers b) from rfl]
      exact (IsLocalization.mk'_spec' (Localization.Away b) 1
        ⟨b, Submonoid.mem_powers b⟩).trans (map_one _)
    have h1 : ψ (algebraMap A (Localization.Away D.s) b) * ψ (divByS (1 : A) D.s) = 1 := by
      rw [← map_mul, hloc, map_one]
    rw [hψ_alg] at h1
    have hu : IsUnit (Ideal.Quotient.mk aI
        (algebraMap A ↥(restrictedMvPowerSeriesSubring 1 A) b)) :=
      isUnit_iff_exists_inv.mpr ⟨_, hmkX_mul⟩
    exact hu.mul_left_cancel (h1.trans hmkX_mul.symm)
  -- `ψ` is continuous for the localization topology
  have hψ_cont : @Continuous _ _ D.topology τQ ψ := by
    change @Continuous _ _ (locTopology D.P D.T D.s D.hopen) τQ ψ
    refine locTopology_continuous_lift D.P D.T D.s D.hopen ψ ?_ ?_
    · have heq : ψ.comp (algebraMap A (Localization.Away D.s)) =
          (Ideal.Quotient.mk aI).comp
            (algebraMap A ↥(restrictedMvPowerSeriesSubring 1 A)) := by
        ext x; exact hψ_alg x
      rw [heq]
      exact continuous_quotient_mk'.comp
        (MvTateAlgebra.mvTateAlgebra_algebraMap_continuous (A := A) 1)
    · intro t ht
      rw [show (D.T : Finset A) = {1} from rfl, Finset.mem_singleton] at ht
      subst ht
      rw [hψ_div]
      exact isPowerBounded_map_of_isOpenMap (Ideal.Quotient.mk aI)
        continuous_quotient_mk' (@QuotientRing.isOpenMap_coe _ τC _ aI hringC)
        (MvTateAlgebra.mvPowerSeries_X_isBounded (0 : Fin 1))
  -- opaquify the evaluation (pay the `D.T.card ≡ 1` defeq once)
  obtain ⟨Φ, hΦ_cont, hΦ_alg, hΦ_X, hΦ_ker⟩ :
      ∃ Φ : ↥(restrictedMvPowerSeriesSubring 1 A) →+* presheafValue D,
        @Continuous _ _ τC _ ⇑Φ ∧
        (∀ x : A, Φ (algebraMap A ↥(restrictedMvPowerSeriesSubring 1 A) x) =
          D.canonicalMap x) ∧
        (Φ (⟨MvPowerSeries.X (0 : Fin 1), MvPowerSeries.X_isRestricted 0⟩ :
            ↥(restrictedMvPowerSeriesSubring 1 A)) =
          D.coeRingHom (divByS (1 : A) D.s)) ∧
        RingHom.ker (example638_evalHom (coUnitDatum P b)) = RingHom.ker Φ := by
    refine ⟨example638_evalHom D, example638_evalHom_continuous D,
      fun x => example638_evalHom_algebraMap D x, ?_, rfl⟩
    erw [example638_evalHom_X D ((0 : Fin 1) : Fin D.T.card), coUnitDatum_genTuple_eq]
    rfl
  -- extend to the completion, opaquely
  letI : UniformSpace (Localization.Away D.s) := D.uniformSpace
  letI : IsTopologicalRing (Localization.Away D.s) := D.isTopologicalRing
  letI : IsUniformAddGroup (Localization.Away D.s) := D.isUniformAddGroup
  obtain ⟨β, hβ_coe, hβ_cont⟩ :
      ∃ β : presheafValue D →+* (↥(restrictedMvPowerSeriesSubring 1 A) ⧸ aI),
        (∀ y : Localization.Away D.s, β (D.coeRingHom y) = ψ y) ∧
          @Continuous _ _ _ τQ ⇑β := by
    refine ⟨@UniformSpace.Completion.extensionHom (Localization.Away D.s) _ D.uniformSpace _ _
      (↥(restrictedMvPowerSeriesSubring 1 A) ⧸ aI) uQ _ (mvQuot_isUniformAddGroup 1 aI)
      (mvQuot_isTopologicalRing 1 aI) ψ hψ_cont ‹_› ‹_›, fun y => ?_, ?_⟩
    · exact @UniformSpace.Completion.extensionHom_coe (Localization.Away D.s) _ D.uniformSpace
        _ _ (↥(restrictedMvPowerSeriesSubring 1 A) ⧸ aI) uQ _ (mvQuot_isUniformAddGroup 1 aI)
        (mvQuot_isTopologicalRing 1 aI) ψ hψ_cont ‹_› ‹_› y
    · exact @UniformSpace.Completion.continuous_extension (Localization.Away D.s)
        D.uniformSpace _ uQ (⇑ψ) ‹_›
  -- `β ∘ Φ = mk` on the dense polynomials
  have hext : (⇑β ∘ ⇑Φ :
      ↥(restrictedMvPowerSeriesSubring 1 A) → _) = ⇑(Ideal.Quotient.mk aI) := by
    refine Continuous.ext_on
      (MvTateAlgebra.mvPolynomialToTate_denseRange (A := A) 1)
      (hβ_cont.comp hΦ_cont) continuous_quotient_mk' ?_
    rintro _ ⟨p, rfl⟩
    have hcomp : ((β.comp Φ).comp
        (MvTateAlgebra.mvPolynomialToTate (A := A) 1)) =
        (Ideal.Quotient.mk aI).comp (MvTateAlgebra.mvPolynomialToTate (A := A) 1) := by
      refine MvPolynomial.ringHom_ext (fun c => ?_) (fun j => ?_)
      · simp only [RingHom.comp_apply, MvTateAlgebra.mvPolynomialToTate_C]
        rw [hΦ_alg]
        show β (D.coeRingHom (algebraMap A (Localization.Away D.s) c)) = _
        rw [hβ_coe, hψ_alg]
      · simp only [RingHom.comp_apply, MvTateAlgebra.mvPolynomialToTate_X]
        have hj : j = 0 := Subsingleton.elim j 0
        subst hj
        rw [hΦ_X, hβ_coe, hψ_div]
    exact RingHom.congr_fun hcomp p
  -- conclude
  rw [hΦ_ker]
  intro h hh
  have hh2 : Φ h = 0 := hh
  have hfun := congrFun hext h
  simp only [Function.comp_apply, hh2, map_zero] at hfun
  exact Ideal.Quotient.eq_zero_iff_mem.mp hfun.symm

omit [CompatiblePlusSubring A] in
set_option linter.unusedSectionVars false in
/-- **Wedhorn (8.2.1)-plus, explicit kernel**: `ker(evalHom) = (b − ζ)` for the
plus-half `R(b/1)`. -/
theorem unitDatum_ker_eq_span
    [IsTateRing A] [IsNoetherianRing A] [IsStronglyNoetherian A] [T2Space A]
    [NonarchimedeanRing A] [HasLocLiftPowerBounded A]
    [letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A;
      CompleteSpace A]
    (P : PairOfDefinition A) (b : A) :
    RingHom.ker (example638_evalHom (unitDatum P b)) =
      Ideal.span {algebraMap A ↥(TateAlgebra A) b - TateAlgebra.X} :=
  le_antisymm (unitDatum_ker_le_span P b) (unitDatum_span_le_ker P b)

omit [CompatiblePlusSubring A] in
set_option linter.unusedSectionVars false in
/-- **Wedhorn (8.2.1)-minus, explicit kernel**: `ker(evalHom) = (1 − bη)` for the
minus-half `R(1/b)`. -/
theorem coUnitDatum_ker_eq_span
    [IsTateRing A] [IsNoetherianRing A] [IsStronglyNoetherian A] [T2Space A]
    [NonarchimedeanRing A] [HasLocLiftPowerBounded A]
    [letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A;
      CompleteSpace A]
    (P : PairOfDefinition A) (b : A) :
    RingHom.ker (example638_evalHom (coUnitDatum P b)) =
      Ideal.span {1 - algebraMap A ↥(TateAlgebra A) b * TateAlgebra.X} :=
  le_antisymm (coUnitDatum_ker_le_span P b) (coUnitDatum_span_le_ker P b)

omit [CompatiblePlusSubring A] in
set_option linter.unusedSectionVars false in
/-- **Wedhorn Example 6.38, plus form (any strongly noetherian Tate base)**:
`O_X(R(b/1)) ≃+* A⟨ζ⟩/(b − ζ)` — surjectivity (`example638_evalHom_surjective`)
plus the explicit kernel (`unitDatum_ker_eq_span`). -/
noncomputable def unitDatum_quotEquiv
    [IsTateRing A] [IsNoetherianRing A] [IsStronglyNoetherian A] [T2Space A]
    [NonarchimedeanRing A] [HasLocLiftPowerBounded A]
    [letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A;
      CompleteSpace A]
    (P : PairOfDefinition A) (b : A) :
    presheafValue (unitDatum P b) ≃+*
      (↥(TateAlgebra A) ⧸ Ideal.span {algebraMap A ↥(TateAlgebra A) b - TateAlgebra.X}) :=
  ((RingHom.quotientKerEquivOfSurjective
      (example638_evalHom_surjective (unitDatum P b))).symm).trans
    (Ideal.quotEquivOfEq (unitDatum_ker_eq_span P b))

omit [CompatiblePlusSubring A] in
set_option linter.unusedSectionVars false in
/-- **Wedhorn Example 6.39, minus form (any strongly noetherian Tate base)**:
`O_X(R(1/b)) ≃+* A⟨η⟩/(1 − bη)`. -/
noncomputable def coUnitDatum_quotEquiv
    [IsTateRing A] [IsNoetherianRing A] [IsStronglyNoetherian A] [T2Space A]
    [NonarchimedeanRing A] [HasLocLiftPowerBounded A]
    [letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A;
      CompleteSpace A]
    (P : PairOfDefinition A) (b : A) :
    presheafValue (coUnitDatum P b) ≃+*
      (↥(TateAlgebra A) ⧸ Ideal.span {1 - algebraMap A ↥(TateAlgebra A) b * TateAlgebra.X}) :=
  ((RingHom.quotientKerEquivOfSurjective
      (example638_evalHom_surjective (coUnitDatum P b))).symm).trans
    (Ideal.quotEquivOfEq (coUnitDatum_ker_eq_span P b))

omit [CompatiblePlusSubring A] in
set_option linter.unusedSectionVars false in
/-- The plus equivalence sends `canonicalMap x` to the constant class
`mk (algebraMap x)`. -/
theorem unitDatum_quotEquiv_canonicalMap
    [IsTateRing A] [IsNoetherianRing A] [IsStronglyNoetherian A] [T2Space A]
    [NonarchimedeanRing A] [HasLocLiftPowerBounded A]
    [letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A;
      CompleteSpace A]
    (P : PairOfDefinition A) (b : A) (x : A) :
    unitDatum_quotEquiv P b ((unitDatum P b).canonicalMap x) =
      Ideal.Quotient.mk _ (algebraMap A ↥(TateAlgebra A) x) := by
  have h1 : (unitDatum P b).canonicalMap x =
      example638_evalHom (unitDatum P b)
        (algebraMap A ↥(restrictedMvPowerSeriesSubring 1 A) x) :=
    (example638_evalHom_algebraMap _ x).symm
  have h2 : (RingHom.quotientKerEquivOfSurjective
      (example638_evalHom_surjective (unitDatum P b))).symm
        (example638_evalHom (unitDatum P b)
          (algebraMap A ↥(restrictedMvPowerSeriesSubring 1 A) x)) =
      Ideal.Quotient.mk (RingHom.ker (example638_evalHom (unitDatum P b)))
        (algebraMap A ↥(restrictedMvPowerSeriesSubring 1 A) x) := by
    rw [RingEquiv.symm_apply_eq]
    rfl
  show (Ideal.quotEquivOfEq (unitDatum_ker_eq_span P b))
      ((RingHom.quotientKerEquivOfSurjective
        (example638_evalHom_surjective (unitDatum P b))).symm
          ((unitDatum P b).canonicalMap x)) = _
  rw [h1, h2]
  erw [Ideal.quotEquivOfEq_mk]

omit [CompatiblePlusSubring A] in
set_option linter.unusedSectionVars false in
/-- The minus equivalence sends `canonicalMap x` to the constant class
`mk (algebraMap x)`. -/
theorem coUnitDatum_quotEquiv_canonicalMap
    [IsTateRing A] [IsNoetherianRing A] [IsStronglyNoetherian A] [T2Space A]
    [NonarchimedeanRing A] [HasLocLiftPowerBounded A]
    [letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A;
      CompleteSpace A]
    (P : PairOfDefinition A) (b : A) (x : A) :
    coUnitDatum_quotEquiv P b ((coUnitDatum P b).canonicalMap x) =
      Ideal.Quotient.mk _ (algebraMap A ↥(TateAlgebra A) x) := by
  have h1 : (coUnitDatum P b).canonicalMap x =
      example638_evalHom (coUnitDatum P b)
        (algebraMap A ↥(restrictedMvPowerSeriesSubring 1 A) x) :=
    (example638_evalHom_algebraMap _ x).symm
  have h2 : (RingHom.quotientKerEquivOfSurjective
      (example638_evalHom_surjective (coUnitDatum P b))).symm
        (example638_evalHom (coUnitDatum P b)
          (algebraMap A ↥(restrictedMvPowerSeriesSubring 1 A) x)) =
      Ideal.Quotient.mk (RingHom.ker (example638_evalHom (coUnitDatum P b)))
        (algebraMap A ↥(restrictedMvPowerSeriesSubring 1 A) x) := by
    rw [RingEquiv.symm_apply_eq]
    rfl
  show (Ideal.quotEquivOfEq (coUnitDatum_ker_eq_span P b))
      ((RingHom.quotientKerEquivOfSurjective
        (example638_evalHom_surjective (coUnitDatum P b))).symm
          ((coUnitDatum P b).canonicalMap x)) = _
  rw [h1, h2]
  erw [Ideal.quotEquivOfEq_mk]

end Wedhorn828

end ValuationSpectrum
