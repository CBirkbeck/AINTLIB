import PadicLFunctions.Iwasawa.StructureTheory.CharIdeal
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.DirectSum.Module
import Mathlib.RingTheory.Idempotents
import Mathlib.Algebra.Algebra.RestrictScalars

/-!
# Equivariant isotypic decomposition and `Ch_{Λ(𝒢)}`  (S13-S5)

For the Galois group `𝒢 = H × Γ'` with `H = μ_{p-1}` of order prime to `p` and
`Γ' ≅ ℤ_p`, the group Iwasawa algebra splits as `Λ(𝒢) ≅ 𝒪_L[H] ⊗_{𝒪_L} Λ`
(realised here as `Λ[H] = MonoidAlgebra Λ H`).  Because `|H|` is invertible in
`𝒪_L` (prime to `p`), the orthogonal idempotents `e_ω = |H|⁻¹ Σ_a ω⁻¹(a)[a]`,
indexed by the characters `ω : H → 𝒪_L^×`, split every `Λ(𝒢)`-module into its
isotypic components `M = ⨁_ω M^{(ω)}`, each finitely generated and torsion over
`Λ`.  The equivariant characteristic ideal is `Ch_{Λ(𝒢)}(M) = ⨁_ω Ch_Λ(M^{(ω)})`.
(RJW TeX 3659–3676; CS06, Appendix A.1, lemma.)

**Field-extension caveat** (RJW TeX 3664): the character values `ω(a)` may force a
finite extension of `L`; the idempotents live over `𝒪_L` only after extending so
that `μ_{|H|} ⊆ 𝒪_L`.  We index characters by `H →* 𝒪ˣ` and assume the needed
roots of unity are present in `𝒪`.

## Main declarations

* `Iwasawa.IwasawaAlgebraGroup 𝒪 H` (notation `Λ⟦H⟧`): the group Iwasawa algebra
  `Λ(𝒢) = Λ[H]`.
* `Iwasawa.isotypicIdempotent`: the orthogonal idempotent `e_ω ∈ Λ(𝒢)` of a
  character (RJW TeX 3661).
* `Iwasawa.isotypicComponent` / `Iwasawa.isInternal_isotypicComponent`: the
  `ω`-components and the internal direct-sum decomposition `M = ⨁_ω M^{(ω)}`.
* `Iwasawa.charIdealGroup`: the equivariant characteristic ideal
  `Ch_{Λ(𝒢)}(M) = ⨁_ω Ch_Λ(M^{(ω)})`.
-/

noncomputable section

open DirectSum

namespace Iwasawa

variable (𝒪 : Type*) [CommRing 𝒪] (H : Type*) [CommGroup H] [Fintype H]

local notation "Λ" => IwasawaAlgebra 𝒪

/-- The **group Iwasawa algebra** `Λ(𝒢) = Λ[H] = MonoidAlgebra Λ H` for
`𝒢 = H × Γ'`.  Canonically `Λ(𝒢) ≅ 𝒪[H] ⊗_𝒪 Λ` (RJW TeX 3659). -/
abbrev IwasawaAlgebraGroup : Type _ := MonoidAlgebra (IwasawaAlgebra 𝒪) H

@[inherit_doc] scoped notation "Λ⟦" H "⟧" => IwasawaAlgebraGroup _ H

local notation "Λ𝒢" => IwasawaAlgebraGroup 𝒪 H

/-- The **isotypic idempotent** `e_ω = |H|⁻¹ Σ_{a ∈ H} ω⁻¹(a)·[a] ∈ Λ(𝒢)` attached
to a character `ω : H → 𝒪^×`.  Well-defined since `|H|` is invertible in `𝒪`
(prime-to-`p`).  (RJW TeX 3661.) -/
noncomputable def isotypicIdempotent [Invertible (Fintype.card H : 𝒪)] (ω : H →* 𝒪ˣ) : Λ𝒢 :=
  ∑ a : H, MonoidAlgebra.single a
    (algebraMap 𝒪 (IwasawaAlgebra 𝒪) (⅟(Fintype.card H : 𝒪) * ((ω a)⁻¹ : 𝒪ˣ)))

/-- **Orthogonality relation for characters** (the crux of idempotent orthogonality): the
sum over a finite abelian group `H` of a *nontrivial* character `χ : H →* 𝒪ˣ` (valued in the
units of a domain `𝒪`) vanishes.  Proof: pick `b` with `χ b ≠ 1`; reindexing `a ↦ b·a`
gives `χ(b)·Σ = Σ`, so `(χ(b) − 1)·Σ = 0`, and `χ(b) − 1 ≠ 0` in the domain forces `Σ = 0`. -/
theorem charSum_eq_zero [IsDomain 𝒪] {χ : H →* 𝒪ˣ} (hχ : χ ≠ 1) :
    ∑ a : H, ((χ a : 𝒪)) = 0 := by
  obtain ⟨b, hb⟩ : ∃ b, χ b ≠ 1 := by
    by_contra h; push_neg at h; exact hχ (MonoidHom.ext h)
  have hreindex : ∑ a : H, ((χ (b * a) : 𝒪)) = ∑ a : H, ((χ a : 𝒪)) :=
    Equiv.sum_comp (Equiv.mulLeft b) (fun a => ((χ a : 𝒪)))
  have key : ((χ b : 𝒪) - 1) * (∑ a : H, (χ a : 𝒪)) = 0 := by
    rw [sub_mul, one_mul, Finset.mul_sum]
    have hstep : ∑ a : H, (χ b : 𝒪) * (χ a : 𝒪) = ∑ a : H, ((χ a : 𝒪)) := by
      rw [← hreindex]; refine Finset.sum_congr rfl fun a _ => ?_
      rw [map_mul, Units.val_mul]
    rw [hstep, sub_self]
  rcases mul_eq_zero.mp key with h | h
  · rw [sub_eq_zero] at h
    exact absurd (Units.val_eq_one.mp h) hb
  · exact h

/-- **The convolution product of two isotypic idempotents.**  Expanding
`e_ω·e_ψ = Σ_a Σ_b [ab]·(N⁻¹ω(a)⁻¹)(N⁻¹ψ(b)⁻¹)`, reindexing `b ↦ a⁻¹g` and using
`ψ(a⁻¹g)⁻¹ = ψ(a)ψ(g)⁻¹` collects the coefficient of `[g]` into
`N⁻²·ψ(g)⁻¹·Σ_a ω(a)⁻¹ψ(a)`.  The character-sum `Σ_a ω(a)⁻¹ψ(a)` is `N` when `ψ = ω`
(idempotency) and `0` when `ψ ≠ ω` (orthogonality, via `charSum_eq_zero`). -/
theorem isotypicIdempotent_mul [Invertible (Fintype.card H : 𝒪)] (ω ψ : H →* 𝒪ˣ) :
    isotypicIdempotent 𝒪 H ω * isotypicIdempotent 𝒪 H ψ
      = ∑ g : H, MonoidAlgebra.single g (algebraMap 𝒪 (IwasawaAlgebra 𝒪)
          (⅟(Fintype.card H : 𝒪) * ⅟(Fintype.card H : 𝒪) * (((ψ g)⁻¹ : 𝒪ˣ) : 𝒪)
            * ∑ a : H, ((((ω a)⁻¹ : 𝒪ˣ) : 𝒪) * (((ψ a) : 𝒪ˣ) : 𝒪)))) := by
  unfold isotypicIdempotent
  rw [Finset.sum_mul_sum]
  simp_rw [MonoidAlgebra.single_mul_single]
  have hreindex : ∀ a : H,
      (∑ b : H, MonoidAlgebra.single (a * b)
        ((algebraMap 𝒪 Λ) (⅟(Fintype.card H : 𝒪) * ((ω a)⁻¹ : 𝒪ˣ))
          * (algebraMap 𝒪 Λ) (⅟(Fintype.card H : 𝒪) * ((ψ b)⁻¹ : 𝒪ˣ))))
      = ∑ g : H, MonoidAlgebra.single g
        ((algebraMap 𝒪 Λ) (⅟(Fintype.card H : 𝒪) * ((ω a)⁻¹ : 𝒪ˣ))
          * (algebraMap 𝒪 Λ) (⅟(Fintype.card H : 𝒪) * ((ψ (a⁻¹ * g))⁻¹ : 𝒪ˣ))) := by
    intro a
    rw [← Equiv.sum_comp (Equiv.mulLeft a) (fun g : H => MonoidAlgebra.single g
        ((algebraMap 𝒪 Λ) (⅟(Fintype.card H : 𝒪) * ((ω a)⁻¹ : 𝒪ˣ))
          * (algebraMap 𝒪 Λ) (⅟(Fintype.card H : 𝒪) * ((ψ (a⁻¹ * g))⁻¹ : 𝒪ˣ))))]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp only [Equiv.coe_mulLeft, inv_mul_cancel_left]
  simp_rw [hreindex]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [show (∑ a : H, MonoidAlgebra.single g
        ((algebraMap 𝒪 Λ) (⅟(Fintype.card H : 𝒪) * ((ω a)⁻¹ : 𝒪ˣ))
          * (algebraMap 𝒪 Λ) (⅟(Fintype.card H : 𝒪) * ((ψ (a⁻¹ * g))⁻¹ : 𝒪ˣ))))
      = Finsupp.singleAddHom g (∑ a : H,
        ((algebraMap 𝒪 Λ) (⅟(Fintype.card H : 𝒪) * ((ω a)⁻¹ : 𝒪ˣ))
          * (algebraMap 𝒪 Λ) (⅟(Fintype.card H : 𝒪) * ((ψ (a⁻¹ * g))⁻¹ : 𝒪ˣ))))
      from (map_sum (Finsupp.singleAddHom g) _ _).symm]
  rw [Finsupp.singleAddHom_apply]
  congr 1
  simp_rw [← map_mul]
  rw [← map_sum]
  congr 1
  have hkey : ∀ x : H, ((ψ (x⁻¹ * g))⁻¹ : 𝒪ˣ) = ψ x * (ψ g)⁻¹ := by
    intro x
    rw [map_mul, map_inv, mul_inv, inv_inv, mul_comm]
  simp_rw [hkey, Units.val_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  ring

/-- The idempotents `e_ω` are genuine idempotents: `e_ω² = e_ω`. -/
theorem isIdempotentElem_isotypicIdempotent [Invertible (Fintype.card H : 𝒪)]
    (ω : H →* 𝒪ˣ) : IsIdempotentElem (isotypicIdempotent 𝒪 H ω) := by
  rw [IsIdempotentElem, isotypicIdempotent_mul]
  have hsum : (∑ a : H, (((ω a)⁻¹ : 𝒪ˣ) : 𝒪) * (((ω a) : 𝒪ˣ) : 𝒪)) = (Fintype.card H : 𝒪) := by
    simp_rw [Units.inv_mul]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  rw [hsum]
  unfold isotypicIdempotent
  refine Finset.sum_congr rfl fun g _ => ?_
  congr 2
  rw [show ⅟(Fintype.card H : 𝒪) * ⅟(Fintype.card H : 𝒪) * (((ω g)⁻¹ : 𝒪ˣ) : 𝒪)
        * (Fintype.card H : 𝒪)
      = ⅟(Fintype.card H : 𝒪) * (((ω g)⁻¹ : 𝒪ˣ) : 𝒪)
        * (⅟(Fintype.card H : 𝒪) * (Fintype.card H : 𝒪)) by ring,
    invOf_mul_self, mul_one]

/-- Orthogonality of the isotypic idempotents: `e_ω · e_ψ = 0` for `ω ≠ ψ` (over a domain
`𝒪`, where `charSum_eq_zero` applies to the nontrivial character `ω⁻¹·ψ`). -/
theorem isotypicIdempotent_orthogonal [IsDomain 𝒪] [Invertible (Fintype.card H : 𝒪)]
    {ω ψ : H →* 𝒪ˣ} (h : ω ≠ ψ) :
    isotypicIdempotent 𝒪 H ω * isotypicIdempotent 𝒪 H ψ = 0 := by
  have hχ : (ω⁻¹ * ψ : H →* 𝒪ˣ) ≠ 1 := by
    intro hc
    apply h
    have : (ω⁻¹ * ψ : H →* 𝒪ˣ) = 1 ↔ ω = ψ := inv_mul_eq_one
    exact this.mp hc
  have hinner : (∑ a : H, (((ω a)⁻¹ : 𝒪ˣ) : 𝒪) * (((ψ a) : 𝒪ˣ) : 𝒪)) = 0 := by
    have hzero := charSum_eq_zero 𝒪 H hχ
    rw [← hzero]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [MonoidHom.mul_apply, MonoidHom.inv_apply, Units.val_mul]
  rw [isotypicIdempotent_mul]
  refine Finset.sum_eq_zero fun g _ => ?_
  rw [hinner, mul_zero, map_zero, MonoidAlgebra.single_zero]

/-- The **`ω`-isotypic component** `M^{(ω)} = e_ω · M` of a `Λ(𝒢)`-module — the image of
multiplication by the idempotent `e_ω` (a `Λ(𝒢)`-linear map, as `Λ(𝒢)` is commutative). -/
noncomputable def isotypicComponent [Invertible (Fintype.card H : 𝒪)] (ω : H →* 𝒪ˣ)
    (M : Type*) [AddCommGroup M] [Module (IwasawaAlgebraGroup 𝒪 H) M] :
    Submodule (IwasawaAlgebraGroup 𝒪 H) M :=
  LinearMap.range (LinearMap.lsmul (IwasawaAlgebraGroup 𝒪 H) M (isotypicIdempotent 𝒪 H ω))

/-- **Complete orthogonal idempotents decompose any module.**  A finite family `e : ι → R`
of complete orthogonal idempotents in a commutative ring `R` (`∑ eᵢ = 1`, `eᵢ²=eᵢ`,
`eᵢeⱼ=0` for `i≠j`) makes every `R`-module `M` the internal direct sum of the images
`eᵢ·M = range (eᵢ • ·)`.  Mathlib has the ring-level `CompleteOrthogonalIdempotents`
(and `R ≅ ∏ R/(1-eᵢ)`) but not this module-decomposition consequence. -/
theorem isInternal_range_lsmul_of_completeOrthogonalIdempotents
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    {ι : Type*} [Fintype ι] [DecidableEq ι] {e : ι → R}
    (he : CompleteOrthogonalIdempotents e) :
    DirectSum.IsInternal (fun i => LinearMap.range (LinearMap.lsmul R M (e i))) := by
  have hself : ∀ i, ∀ x ∈ LinearMap.range (LinearMap.lsmul R M (e i)), e i • x = x := by
    intro i x hx
    obtain ⟨y, rfl⟩ := hx
    rw [LinearMap.lsmul_apply, ← mul_smul, he.idem i]
  have hkill : ∀ i j, i ≠ j →
      ∀ x ∈ LinearMap.range (LinearMap.lsmul R M (e j)), e i • x = 0 := by
    intro i j hij x hx
    obtain ⟨y, rfl⟩ := hx
    rw [LinearMap.lsmul_apply, ← mul_smul, he.ortho hij, zero_smul]
  rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
  refine ⟨?_, ?_⟩
  · rw [iSupIndep_def]
    intro i
    rw [Submodule.disjoint_def]
    intro x hxi hxsup
    have h1 : e i • x = x := hself i x hxi
    have hker : (⨆ (j) (_ : j ≠ i), LinearMap.range (LinearMap.lsmul R M (e j)))
        ≤ LinearMap.ker (LinearMap.lsmul R M (e i)) := by
      refine iSup_le fun j => iSup_le fun hj => ?_
      intro z hz
      rw [LinearMap.mem_ker, LinearMap.lsmul_apply]
      exact hkill i j (Ne.symm hj) z hz
    have h2 : e i • x = 0 := by
      have hx0 := hker hxsup
      rwa [LinearMap.mem_ker, LinearMap.lsmul_apply] at hx0
    exact h1.symm.trans h2
  · rw [eq_top_iff]
    intro m _
    have hm : (∑ i, e i • m) = m := by rw [← Finset.sum_smul, he.complete, one_smul]
    rw [← hm]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.mem_iSup_of_mem i (LinearMap.mem_range.mpr ⟨m, rfl⟩)

/-- **The equivariant isotypic decomposition** `M = ⨁_ω M^{(ω)}` (RJW TeX 3662–3666; CS06 A.1):
the isotypic components give an internal direct-sum decomposition of any `Λ(𝒢)`-module.
The hypothesis `hcomplete : ∑_ω e_ω = 1` is RJW's *"after extending `L` by adjoining the
values of `ω`"* (TeX 3665) — i.e. `μ_{|H|} ⊆ 𝒪`, so the character family `H →* 𝒪ˣ` is
complete; without it the decomposition is false (e.g. `𝒪 = ℚ`, `H = ℤ/3`). -/
theorem isInternal_isotypicComponent [IsDomain 𝒪] [Invertible (Fintype.card H : 𝒪)]
    [Fintype (H →* 𝒪ˣ)] [DecidableEq (H →* 𝒪ˣ)]
    (hcomplete : ∑ ω : H →* 𝒪ˣ, isotypicIdempotent 𝒪 H ω = 1)
    (M : Type*) [AddCommGroup M] [Module (IwasawaAlgebraGroup 𝒪 H) M] :
    DirectSum.IsInternal (fun ω : H →* 𝒪ˣ => isotypicComponent 𝒪 H ω M) :=
  isInternal_range_lsmul_of_completeOrthogonalIdempotents
    { idem := fun ω => isIdempotentElem_isotypicIdempotent 𝒪 H ω
      ortho := fun _ _ hne => isotypicIdempotent_orthogonal 𝒪 H hne
      complete := hcomplete }

/-- The **ω-augmentation** ring hom `Λ(𝒢) = Λ[H] →+* Λ`, `[a] ↦ ω(a)` (character values
mapped into `Λ` via `𝒪 → Λ`).  It is the projection onto the ω-component of the splitting
`Λ(𝒢) ≅ ∏_ω Λ`: it sends `e_ω ↦ 1` and `e_ψ ↦ 0` for `ψ ≠ ω`. -/
noncomputable def charAugmentation (ω : H →* 𝒪ˣ) :
    IwasawaAlgebraGroup 𝒪 H →+* IwasawaAlgebra 𝒪 :=
  (MonoidAlgebra.lift (IwasawaAlgebra 𝒪) (IwasawaAlgebra 𝒪) H
    ((algebraMap 𝒪 (IwasawaAlgebra 𝒪)).toMonoidHom.comp
      ((Units.coeHom 𝒪).comp ω))).toRingHom

@[simp] theorem charAugmentation_single (ω : H →* 𝒪ˣ) (a : H) (c : IwasawaAlgebra 𝒪) :
    charAugmentation 𝒪 H ω (MonoidAlgebra.single a c)
      = c * algebraMap 𝒪 (IwasawaAlgebra 𝒪) ((ω a : 𝒪)) := by
  rw [charAugmentation, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, MonoidAlgebra.lift_single]
  simp [smul_eq_mul]

/-- On `Λ(𝒢)`, right-multiplication by `e_ω` factors through the ω-augmentation:
`s · e_ω = φ_ω(s) · e_ω` (because `[a]·e_ω = ω(a)·e_ω`).  Consequently `Λ(𝒢)` acts on the
ω-component through `φ_ω : Λ(𝒢) → Λ`. -/
theorem mul_isotypicIdempotent [Invertible (Fintype.card H : 𝒪)] (ω : H →* 𝒪ˣ)
    (s : IwasawaAlgebraGroup 𝒪 H) :
    s * isotypicIdempotent 𝒪 H ω
      = algebraMap (IwasawaAlgebra 𝒪) (IwasawaAlgebraGroup 𝒪 H) (charAugmentation 𝒪 H ω s)
        * isotypicIdempotent 𝒪 H ω := by
  sorry

/-- The idempotent `e_ω` is nonzero — its ω-augmentation is `1`. -/
theorem isotypicIdempotent_ne_zero [Invertible (Fintype.card H : 𝒪)] (ω : H →* 𝒪ˣ) :
    isotypicIdempotent 𝒪 H ω ≠ 0 := by
  sorry

/-- Each isotypic component `M^{(ω)}` is **torsion over `Λ`** (RJW TeX 3669): the `Λ(𝒢)`-action
factors through `φ_ω`, and a non-zero-divisor `s` with `s•x = 0` has `φ_ω(s) ≠ 0` (else
`s·e_ω = 0` with `e_ω ≠ 0`), so `φ_ω(s)` is a nonzero `Λ`-annihilator of `x`. -/
theorem isotypicComponent_isTorsion_Λ [Invertible (Fintype.card H : 𝒪)] (ω : H →* 𝒪ˣ)
    (M : Type*) [AddCommGroup M] [Module (IwasawaAlgebraGroup 𝒪 H) M]
    (hM : Module.IsTorsion (IwasawaAlgebraGroup 𝒪 H) M) :
    Module.IsTorsion (IwasawaAlgebra 𝒪)
      (RestrictScalars (IwasawaAlgebra 𝒪) (IwasawaAlgebraGroup 𝒪 H)
        ↥(isotypicComponent 𝒪 H ω M)) := by
  sorry

/-- Each isotypic component `M^{(ω)}` is **finitely generated over `Λ`** (RJW TeX 3669):
`M` is f.g. over `Λ(𝒢)`, which is module-finite over the Noetherian `Λ`, so `M` is f.g. over
`Λ`, and a `Λ`-submodule of it is f.g. since `Λ` is Noetherian. -/
theorem isotypicComponent_finite_Λ [Invertible (Fintype.card H : 𝒪)] [IsNoetherianRing 𝒪]
    (ω : H →* 𝒪ˣ) (M : Type*) [AddCommGroup M] [Module (IwasawaAlgebraGroup 𝒪 H) M]
    [Module.Finite (IwasawaAlgebraGroup 𝒪 H) M] :
    Module.Finite (IwasawaAlgebra 𝒪)
      (RestrictScalars (IwasawaAlgebra 𝒪) (IwasawaAlgebraGroup 𝒪 H)
        ↥(isotypicComponent 𝒪 H ω M)) := by
  sorry

/-- The **`Λ`-characteristic ideal of the ω-component** `Ch_Λ(M^{(ω)}) ⊆ Λ` (S13-S4 applied to
the finitely generated torsion `Λ`-module `M^{(ω)}`). -/
noncomputable def charIdealComponent [Invertible (Fintype.card H : 𝒪)] [IsNoetherianRing 𝒪]
    (ω : H →* 𝒪ˣ) (M : Type*) [AddCommGroup M] [Module (IwasawaAlgebraGroup 𝒪 H) M]
    [Module.Finite (IwasawaAlgebraGroup 𝒪 H) M]
    (hM : Module.IsTorsion (IwasawaAlgebraGroup 𝒪 H) M) :
    Ideal (IwasawaAlgebra 𝒪) := by
  letI inst : Module (IwasawaAlgebra 𝒪) (RestrictScalars (IwasawaAlgebra 𝒪)
      (IwasawaAlgebraGroup 𝒪 H) ↥(isotypicComponent 𝒪 H ω M)) := inferInstance
  exact @charIdeal 𝒪 _ _ _ inst (isotypicComponent_finite_Λ 𝒪 H ω M)
    (isotypicComponent_isTorsion_Λ 𝒪 H ω M hM)

/-- The **equivariant characteristic ideal** `Ch_{Λ(𝒢)}(M) = ⨁_ω Ch_Λ(M^{(ω)})`
(RJW TeX 3672–3676): under `Λ(𝒢) ≅ ∏_ω Λ` this is the product of the component characteristic
ideals `Ch_Λ(M^{(ω)})` (S13-S4), realised as `⨅_ω φ_ω⁻¹(Ch_Λ(M^{(ω)}))`. -/
noncomputable def charIdealGroup [Invertible (Fintype.card H : 𝒪)] [IsNoetherianRing 𝒪]
    (M : Type*) [AddCommGroup M] [Module (IwasawaAlgebraGroup 𝒪 H) M]
    [Module.Finite (IwasawaAlgebraGroup 𝒪 H) M]
    (hM : Module.IsTorsion (IwasawaAlgebraGroup 𝒪 H) M) :
    Ideal (IwasawaAlgebraGroup 𝒪 H) :=
  ⨅ ω : H →* 𝒪ˣ, Ideal.comap (charAugmentation 𝒪 H ω) (charIdealComponent 𝒪 H ω M hM)

end Iwasawa
