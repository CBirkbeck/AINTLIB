/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.LevelStructure.ExactOrder
import ModularCurves.GroupScheme.DeligneOrder

/-!
# Prime-power factorization of Drinfeld exact order (KM 1.7.2 / 3.5.1, Γ₁-instance)

**[KM-W0-(iv)] skeleton** (`/develop --decompose`, 2026-07-16; quotes in
`.mathlib-quality/decomposition-km-integral.md` §[KM-W0]).

KM Lemma 3.5.1 (verbatim, print p. 101): *"Suppose that `N = AB` with `A` and `B`
relatively prime. Then for any elliptic curve `E/S`, we have functorial isomorphisms
`Γ₁(N)-Str(E/S) ≅ Γ₁(A)-Str(E/S) × Γ₁(B)-Str(E/S)"*, explicitly (print p. 102):
*"for `Γ₁(N)`: point `P` of exact order `N` ↦ points `BP`, `AP` of exact orders `A, B`"*.
The underlying geometric content is KM Proposition 1.7.2 (print pp. 26–31): a
homomorphism `φ : A₁ × A₂ → C(S)` is an `A`-structure iff both restrictions `φᵢ` are
`Aᵢ`-structures; its proof splits the generated subgroup `G ≅ G[N₁] ×_S G[N₂]`,
computes ranks geometrically, and localizes on `S` over the coprime cover
`{N₁ invertible} ∪ {N₂ invertible}`.

The skeleton keeps the repo's divisor encoding (`Section.HasExactOrder`,
KM 1.4.1): no `φ`-homomorphism vocabulary is introduced — for the cyclic group
`ℤ/N` a homomorphism *is* its value at `1` (KM 1.5.2).
-/

open AlgebraicGeometry CategoryTheory Limits

universe u

namespace ModularCurves

variable {S : Scheme.{u}} (E : EllipticCurve S)

/-- Factoring through a monomorphism is Zariski-local on the source: a morphism `q : T ⟶ Y`
factors through `ι : W ⟶ Y` as soon as its restrictions to the members of an open cover of
`T` do. (The local factorizations agree on overlaps by `cancel_mono`, hence glue.) -/
private lemma exists_factor_of_openCover {T W Y : Scheme.{u}} (𝒱 : T.OpenCover)
    (ι : W ⟶ Y) [Mono ι] (q : T ⟶ Y)
    (hloc : ∀ i : 𝒱.I₀, ∃ hi : 𝒱.X i ⟶ W, hi ≫ ι = 𝒱.f i ≫ q) :
    ∃ h : T ⟶ W, h ≫ ι = q := by
  choose hi hhi using hloc
  have hcomp : ∀ i j : 𝒱.I₀,
      pullback.fst (𝒱.f i) (𝒱.f j) ≫ hi i = pullback.snd (𝒱.f i) (𝒱.f j) ≫ hi j := by
    intro i j
    rw [← cancel_mono ι, Category.assoc, Category.assoc, hhi, hhi, ← Category.assoc,
      ← Category.assoc, pullback.condition]
  exact ⟨𝒱.glueMorphisms hi hcomp, 𝒱.hom_ext _ _ fun i => by
    rw [← Category.assoc, Scheme.Cover.ι_glueMorphisms, hhi]⟩

namespace RelEffCartierDiv

/-- **[W0-F3-reindex]** `Σᵢ [Pᵢ]` is invariant under reindexing the family of sections:
the defining ideal is a product over the index set (KM 1.2, the sum of the `[Pᵢ]` as
Cartier divisors), and products are permutation-invariant. -/
theorem sectionsDivisor_congr {C : Scheme.{u}} {π : C ⟶ S} {n : ℕ}
    (P Q : Fin n → { z : S ⟶ C // z ≫ π = 𝟙 S }) (e : Fin n ≃ Fin n)
    (h : ∀ i, P i = Q (e i)) :
    sectionsDivisor π P = sectionsDivisor π Q := by
  apply RelEffCartierDiv.ext
  by_cases hπ : IsSeparated π ∧ SmoothOfRelativeDimension 1 π
  · rw [sectionsDivisor, sectionsDivisor, dif_pos hπ, dif_pos hπ]
    exact Fintype.prod_equiv e _ _ fun i => by rw [h i]
  · rw [sectionsDivisor, sectionsDivisor, dif_neg hπ, dif_neg hπ]

/-- **[W0-F3-loc] (KM 1.7.2's silent localization step)** Being a subgroup divisor is
Zariski-local on the base: if the pullbacks of a relative effective Cartier divisor
`D` in `E/S` to the members of an open cover of `S` are subgroups, `D` is a subgroup.
KM (print p. 31, verbatim): *"Because `N = N₁N₂` with `N₁` and `N₂` relatively prime,
we may, by localizing on `S`, suppose that one of `N₁, N₂`, say `N₁`, is invertible
on `S`."* — the step that makes this reduction legitimate for the `IsSubgroup`
conclusion. -/
theorem isSubgroup_of_openCover (D : RelEffCartierDiv E.π)
    (𝒰 : S.OpenCover) (h : ∀ i : 𝒰.I₀,
      ∀ ⦃T : Scheme.{u}⦄ (g : T ⟶ S), (∃ gi : T ⟶ 𝒰.X i, gi ≫ 𝒰.f i = g) →
        ∃ H : AddSubgroup (E.Point g),
          ∀ P : E.Point g, P ∈ H ↔ ∃ h : T ⟶ D.ideal.subscheme,
            h ≫ D.ideal.subschemeι = P.1) :
    D.IsSubgroup E := by
  intro T g
  -- the pulled-back cover of `T`, indexed by `𝒰.I₀`
  let 𝒱 : T.OpenCover := Scheme.Cover.mkOfCovers 𝒰.I₀
    (fun i => pullback g (𝒰.f i)) (fun i => pullback.fst g (𝒰.f i))
    (fun t => by
      obtain ⟨y, hy⟩ := 𝒰.covers (g t)
      obtain ⟨z, hz1, _⟩ := Scheme.Pullback.exists_preimage_pullback t y hy.symm
      exact ⟨𝒰.idx (g t), z, hz1⟩)
    (fun i => inferInstance)
  -- the local subgroup structures over the cover
  have hloc := fun i : 𝒰.I₀ => h i (pullback.fst g (𝒰.f i) ≫ g)
    ⟨pullback.snd g (𝒰.f i), pullback.condition.symm⟩
  choose Hloc hHloc using hloc
  -- gluing engine: a point factoring locally on the cover factors globally
  have key : ∀ P : E.Point g,
      (∀ i : 𝒰.I₀, ∃ hi : pullback g (𝒰.f i) ⟶ D.ideal.subscheme,
        hi ≫ D.ideal.subschemeι = pullback.fst g (𝒰.f i) ≫ P.1) →
      ∃ hh : T ⟶ D.ideal.subscheme, hh ≫ D.ideal.subschemeι = P.1 :=
    fun P hP => exists_factor_of_openCover 𝒱 D.ideal.subschemeι P.1 hP
  -- local membership of a restricted point, from a global factoring
  have hmem : ∀ (i : 𝒰.I₀) (P : E.Point g),
      (∃ hh : T ⟶ D.ideal.subscheme, hh ≫ D.ideal.subschemeι = P.1) →
      EllipticCurve.Point.restrict E (pullback.fst g (𝒰.f i)) P ∈ Hloc i := by
    intro i P hhP
    obtain ⟨hh, hhh⟩ := hhP
    exact (hHloc i _).mpr ⟨pullback.fst g (𝒰.f i) ≫ hh, by
      rw [Category.assoc, hhh]; rfl⟩
  -- restriction of a negative
  have hneg : ∀ (i : 𝒰.I₀) (P : E.Point g),
      EllipticCurve.Point.restrict E (pullback.fst g (𝒰.f i)) (-P)
        = -EllipticCurve.Point.restrict E (pullback.fst g (𝒰.f i)) P := by
    intro i P
    refine eq_neg_of_add_eq_zero_left ?_
    rw [← EllipticCurve.Point.restrict_add, neg_add_cancel,
      EllipticCurve.Point.restrict_zero]
  refine ⟨{ carrier := setOf fun P : E.Point g =>
              ∃ hh : T ⟶ D.ideal.subscheme, hh ≫ D.ideal.subschemeι = P.1
            zero_mem' := key 0 fun i =>
              (hHloc i (EllipticCurve.Point.restrict E (pullback.fst g (𝒰.f i)) 0)).mp
                (by rw [EllipticCurve.Point.restrict_zero]; exact (Hloc i).zero_mem)
            add_mem' := fun {P Q} hP hQ => key (P + Q) fun i =>
              (hHloc i (EllipticCurve.Point.restrict E (pullback.fst g (𝒰.f i)) (P + Q))).mp
                (by rw [EllipticCurve.Point.restrict_add]
                    exact (Hloc i).add_mem (hmem i P hP) (hmem i Q hQ))
            neg_mem' := fun {P} hP => key (-P) fun i =>
              (hHloc i (EllipticCurve.Point.restrict E (pullback.fst g (𝒰.f i)) (-P))).mp
                (by rw [hneg]; exact (Hloc i).neg_mem (hmem i P hP)) },
    fun P => Iff.rfl⟩

end RelEffCartierDiv

/-- Multiplication respects congruence on a killed point: if `N • P = 0` and
`a ≡ b (mod N)` then `a • P = b • P`. (KM 1.4.2's consequence used throughout 1.7.2's
multiplier bookkeeping.) -/
private theorem zsmul_congr_of_kill {G : Type*} [AddCommGroup G] {N : ℤ} {P : G}
    (hkill : N • P = 0) {a b : ℤ} (hab : a % N = b % N) : a • P = b • P := by
  obtain ⟨t, ht⟩ := Int.ModEq.dvd (show Int.ModEq N a b from hab)
  have hb : b = a + N * t := by linarith
  rw [hb, add_zsmul, mul_comm, mul_smul, hkill, smul_zero, add_zero]

/-- **[W0-F3-crt-map]** The KM (3.5.1.3) index map on `Fin (M·K)`: the pair `(a₁, a₂)`
(read off through `finProdFinEquiv`) goes to the residue of the combined multiplier
`(a₁+1)·K + (a₂+1)·M`, shifted to the `1..MK` window of `orderDivisor`. -/
private def crtIndex (M K : ℕ) [NeZero M] [NeZero K] (j : Fin (M * K)) : Fin (M * K) :=
  ⟨((((finProdFinEquiv.symm j).1 : ℕ) + 1) * K + (((finProdFinEquiv.symm j).2 : ℕ) + 1) * M - 1)
      % (M * K),
    Nat.mod_lt _ (Nat.pos_of_ne_zero (Nat.mul_ne_zero (NeZero.ne M) (NeZero.ne K)))⟩

/-- **[W0-F3-crt-inj]** The KM index map is injective — CRT uniqueness: congruence of the
combined multipliers mod `M·K` forces componentwise equality (cancel the coprime unit,
then compare in the fundamental window). -/
private theorem crtIndex_injective (M K : ℕ) [NeZero M] [NeZero K]
    (hMK : Nat.Coprime M K) : Function.Injective (crtIndex M K) := by
  intro j j' hjj
  set a₁ := ((finProdFinEquiv.symm j).1 : ℕ) with ha₁
  set a₂ := ((finProdFinEquiv.symm j).2 : ℕ) with ha₂
  set b₁ := ((finProdFinEquiv.symm j').1 : ℕ) with hb₁
  set b₂ := ((finProdFinEquiv.symm j').2 : ℕ) with hb₂
  have hm1 : 1 ≤ (a₁ + 1) * K + (a₂ + 1) * M :=
    le_trans (Nat.one_le_iff_ne_zero.mpr
      (Nat.mul_ne_zero (Nat.succ_ne_zero a₁) (NeZero.ne K))) (Nat.le_add_right _ _)
  have hm1' : 1 ≤ (b₁ + 1) * K + (b₂ + 1) * M :=
    le_trans (Nat.one_le_iff_ne_zero.mpr
      (Nat.mul_ne_zero (Nat.succ_ne_zero b₁) (NeZero.ne K))) (Nat.le_add_right _ _)
  -- the combined multipliers agree mod `M·K`
  have hmod : ((a₁ + 1) * K + (a₂ + 1) * M - 1) % (M * K)
      = ((b₁ + 1) * K + (b₂ + 1) * M - 1) % (M * K) := congrArg Fin.val hjj
  have hMEq : (a₁ + 1) * K + (a₂ + 1) * M ≡ (b₁ + 1) * K + (b₂ + 1) * M [MOD M * K] := by
    have h := Nat.ModEq.add_right 1
      (hmod : (a₁ + 1) * K + (a₂ + 1) * M - 1 ≡ (b₁ + 1) * K + (b₂ + 1) * M - 1 [MOD M * K])
    rwa [Nat.sub_add_cancel hm1, Nat.sub_add_cancel hm1'] at h
  -- first component: reduce mod `M`, cancel the coprime `K`
  have hcomp₁ : a₁ = b₁ := by
    have hdM : (a₁ + 1) * K ≡ (b₁ + 1) * K [MOD M] := by
      have h0 := hMEq.of_dvd (dvd_mul_right M K)
      have e₁ : (a₁ + 1) * K + (a₂ + 1) * M ≡ (a₁ + 1) * K + 0 [MOD M] :=
        (Nat.ModEq.refl _).add (Nat.modEq_zero_iff_dvd.mpr (dvd_mul_left M (a₂ + 1)))
      have e₂ : (b₁ + 1) * K + (b₂ + 1) * M ≡ (b₁ + 1) * K + 0 [MOD M] :=
        (Nat.ModEq.refl _).add (Nat.modEq_zero_iff_dvd.mpr (dvd_mul_left M (b₂ + 1)))
      simpa using (e₁.symm.trans h0).trans e₂
    have h2 : a₁ + 1 ≡ b₁ + 1 [MOD M] :=
      Nat.ModEq.cancel_right_of_coprime (hMK : Nat.gcd M K = 1) hdM
    have h3 : a₁ ≡ b₁ [MOD M] := Nat.ModEq.add_right_cancel' 1 h2
    rw [Nat.ModEq, Nat.mod_eq_of_lt (finProdFinEquiv.symm j).1.isLt,
      Nat.mod_eq_of_lt (finProdFinEquiv.symm j').1.isLt] at h3
    exact h3
  -- second component: reduce mod `K`, cancel the coprime `M`
  have hcomp₂ : a₂ = b₂ := by
    have hdK : (a₂ + 1) * M ≡ (b₂ + 1) * M [MOD K] := by
      have h0 := hMEq.of_dvd (dvd_mul_left K M)
      have e₁ : (a₁ + 1) * K + (a₂ + 1) * M ≡ 0 + (a₂ + 1) * M [MOD K] :=
        Nat.ModEq.add (Nat.modEq_zero_iff_dvd.mpr (dvd_mul_left K (a₁ + 1)))
          (Nat.ModEq.refl _)
      have e₂ : (b₁ + 1) * K + (b₂ + 1) * M ≡ 0 + (b₂ + 1) * M [MOD K] :=
        Nat.ModEq.add (Nat.modEq_zero_iff_dvd.mpr (dvd_mul_left K (b₁ + 1)))
          (Nat.ModEq.refl _)
      simpa using (e₁.symm.trans h0).trans e₂
    have h2 : a₂ + 1 ≡ b₂ + 1 [MOD K] :=
      Nat.ModEq.cancel_right_of_coprime (hMK.symm : Nat.gcd K M = 1) hdK
    have h3 : a₂ ≡ b₂ [MOD K] := Nat.ModEq.add_right_cancel' 1 h2
    rw [Nat.ModEq, Nat.mod_eq_of_lt (finProdFinEquiv.symm j).2.isLt,
      Nat.mod_eq_of_lt (finProdFinEquiv.symm j').2.isLt] at h3
    exact h3
  -- reassemble
  have : finProdFinEquiv.symm j = finProdFinEquiv.symm j' :=
    Prod.ext (Fin.ext hcomp₁) (Fin.ext hcomp₂)
  exact finProdFinEquiv.symm.injective this

/-- **[W0-F3-crt]** KM 1.7.1/3.5.1's decomposition of the order divisor: for a killed
point `P` and coprime `M, K`, the degree-`MK` divisor `[P] + [2P] + ⋯ + [MK·P]` is the
sum over pairs of the combined multiples — the Cartier-divisor form of
*"G = Σ_{a₁,a₂} [φ(a₁) + φ(a₂)]"* (KM print p. 31), with `φ(a₁) = a₁·(KP)`,
`φ(a₂) = a₂·(MP)` per (3.5.1.3). -/
theorem Section.orderDivisor_mul_crt (P : E.Section) (M K : ℕ) [NeZero M] [NeZero K]
    (hMK : Nat.Coprime M K)
    (hkill : ((M * K : ℕ) : ℤ) • P = (0 : E.Point (𝟙 S))) :
    RelEffCartierDiv.sectionsDivisor E.π (fun j : Fin (M * K) =>
        ((((((finProdFinEquiv.symm j).1 : ℕ) + 1) * K
          + (((finProdFinEquiv.symm j).2 : ℕ) + 1) * M : ℕ) : ℤ) • P : E.Point (𝟙 S)))
      = P.orderDivisor E (M * K) := by
  haveI : NeZero (M * K) := ⟨Nat.mul_ne_zero (NeZero.ne M) (NeZero.ne K)⟩
  refine RelEffCartierDiv.sectionsDivisor_congr _ _
    (Equiv.ofBijective _ ((Finite.injective_iff_bijective).mp (crtIndex_injective M K hMK)))
    fun j => ?_
  -- pointwise: the multipliers agree mod `M·K` on the killed point
  set a₁ := ((finProdFinEquiv.symm j).1 : ℕ) with ha₁
  set a₂ := ((finProdFinEquiv.symm j).2 : ℕ) with ha₂
  have hm1 : 1 ≤ (a₁ + 1) * K + (a₂ + 1) * M :=
    le_trans (Nat.one_le_iff_ne_zero.mpr
      (Nat.mul_ne_zero (Nat.succ_ne_zero a₁) (NeZero.ne K))) (Nat.le_add_right _ _)
  show _ • P = ((((crtIndex M K j : ℕ) : ℤ) + 1) • P : E.Point (𝟙 S))
  refine zsmul_congr_of_kill hkill ?_
  have hval : ((crtIndex M K j : ℕ) : ℤ)
      = (((a₁ + 1) * K + (a₂ + 1) * M - 1 : ℕ) : ℤ) % ((M : ℤ) * K) := by
    simp only [crtIndex, ← ha₁, ← ha₂]
    push_cast
    rfl
  rw [hval]
  have hcast : (((a₁ + 1) * K + (a₂ + 1) * M - 1 : ℕ) : ℤ)
      = ((a₁ + 1) * K + (a₂ + 1) * M : ℕ) - 1 := by
    push_cast [Nat.cast_sub hm1]
    ring
  rw [hcast]
  have h1 : (((((a₁ + 1) * K + (a₂ + 1) * M : ℕ) : ℤ) - 1) % ((M : ℤ) * K))
      ≡ (((a₁ + 1) * K + (a₂ + 1) * M : ℕ) : ℤ) - 1 [ZMOD ((M : ℤ) * K)] :=
    Int.emod_emod_of_dvd _ dvd_rfl
  have h2 := h1.add_right 1
  rw [sub_add_cancel] at h2
  exact h2.symm

/-- Pushforward along an isomorphism agrees with pullback along its inverse: for
`e : C ≅ C`, `I.map e.hom = I.comap e.inv`. (The comap-map Galois connection restricts
to an order isomorphism along an iso; both adjoints are then the same inverse image.) -/
theorem _root_.AlgebraicGeometry.Scheme.IdealSheafData.map_hom_eq_comap_inv
    {C : Scheme.{u}} (e : C ≅ C) (I : C.IdealSheafData) :
    I.map e.hom = I.comap e.inv := by
  have hid₁ : ∀ J : C.IdealSheafData, (J.comap e.inv).comap e.hom = J := by
    intro J
    rw [← Scheme.IdealSheafData.comap_comp, Iso.hom_inv_id,
      Scheme.IdealSheafData.comap_id]
  have hid₂ : ∀ J : C.IdealSheafData, (J.comap e.hom).comap e.inv = J := by
    intro J
    rw [← Scheme.IdealSheafData.comap_comp, Iso.inv_hom_id,
      Scheme.IdealSheafData.comap_id]
  refine le_antisymm ?_ ?_
  · have h1 : (I.map e.hom).comap e.hom ≤ I :=
      Scheme.IdealSheafData.comap_map_le I e.hom
    have h2 : ((I.map e.hom).comap e.hom).comap e.inv ≤ I.comap e.inv :=
      Scheme.IdealSheafData.comap_mono (f := e.inv) h1
    rwa [hid₂] at h2
  · have h1 : (I.comap e.inv).comap e.hom ≤ I := le_of_eq (hid₁ I)
    exact Scheme.IdealSheafData.le_map_iff_comap_le.mpr h1

/-- **[W0-F3-pts] (KM 1.5.1.2's tautology)** Each constituent section factors through the
sections divisor: `Pₐ` is a point *of* `Σᵢ [Pᵢ]`. The defining ideal `∏ᵢ ker (Pᵢ)` is
contained in `ker (Pₐ)`, so the kernel-image factorization `toImage` composed with the
ideal-monotone `inclusion` lands in the divisor subscheme. -/
theorem RelEffCartierDiv.factors_sectionsDivisor {C : Scheme.{u}} {π : C ⟶ S} {n : ℕ}
    (Ps : Fin n → { z : S ⟶ C // z ≫ π = 𝟙 S })
    (hπ : IsSeparated π ∧ SmoothOfRelativeDimension 1 π) (a : Fin n) :
    ∃ h : S ⟶ (RelEffCartierDiv.sectionsDivisor π Ps).ideal.subscheme,
      h ≫ (RelEffCartierDiv.sectionsDivisor π Ps).ideal.subschemeι = (Ps a).1 := by
  have hle : (RelEffCartierDiv.sectionsDivisor π Ps).ideal ≤ Scheme.Hom.ker (Ps a).1 := by
    rw [RelEffCartierDiv.sectionsDivisor, dif_pos hπ]
    intro V
    have h1 : (∏ i, Scheme.Hom.ker (Ps i).1 : C.IdealSheafData).ideal
        = ∏ i, (Scheme.IdealSheafData.idealMonoidHom C) (Scheme.Hom.ker (Ps i).1) :=
      map_prod (Scheme.IdealSheafData.idealMonoidHom C) _ Finset.univ
    have hprod : ((∏ i, Scheme.Hom.ker (Ps i).1 : C.IdealSheafData)).ideal V
        = ∏ i, (Scheme.Hom.ker (Ps i).1).ideal V := by
      rw [show ((∏ i, Scheme.Hom.ker (Ps i).1 : C.IdealSheafData)).ideal V
          = ((∏ i, Scheme.Hom.ker (Ps i).1 : C.IdealSheafData).ideal) V from rfl, h1,
        Finset.prod_apply]
      rfl
    rw [hprod]
    exact le_trans Ideal.prod_le_inf (Finset.inf_le (Finset.mem_univ a))
  exact ⟨(Ps a).1.toImage ≫ Scheme.IdealSheafData.inclusion hle, by
    rw [Category.assoc, Scheme.IdealSheafData.inclusion_subschemeι,
      Scheme.Hom.toImage_imageι]⟩

/-- **[W0-1.4.2] (KM Lemma 1.4.2)** Verbatim: *"If `P ∈ C(S)` has 'exact order N', then
`NP = 0`. Proof. Any finite locally free commutative group-scheme of rank `N` is known
to be killed by `N` (cf. [Oort–Tate]). Therefore every section, in particular `P`, of
the effective Cartier divisor `Σ [aP]` is killed by `N`."* — assembled from the register
box BB-DELIGNE (`smul_eq_zero_of_factors`) at the first constituent section
(`factors_sectionsDivisor`) and the degree spec (KM 1.2.2). -/
theorem Section.HasExactOrder.smul_eq_zero {P : E.Section} {N : ℕ} [NeZero N]
    (h : P.HasExactOrder E N) : (N : ℤ) • P = (0 : E.Point (𝟙 S)) := by
  have hdeg : ∀ s : S, (P.orderDivisor E N).degree s = N := fun s =>
    RelEffCartierDiv.sectionsDivisor_degree E.π E.smooth _ s
  obtain ⟨w, hw⟩ := RelEffCartierDiv.factors_sectionsDivisor
    (fun a : Fin N => ((((a : ℕ) : ℤ) + 1) • P : E.Point (𝟙 S)))
    ⟨inferInstance, E.smooth⟩ ⟨0, Nat.pos_of_ne_zero (NeZero.ne N)⟩
  have h1 : ((((⟨0, Nat.pos_of_ne_zero (NeZero.ne N)⟩ : Fin N) : ℕ) : ℤ) + 1) • P
      = (P : E.Point (𝟙 S)) := by simp
  exact RelEffCartierDiv.IsSubgroup.smul_eq_zero_of_factors E h hdeg (𝟙 S) P
    ⟨w, hw.trans (congrArg Subtype.val h1)⟩

/-- **[W0-F3-coprime-kill] (KM print p. 30)** A point killed by two coprime integers is
zero — KM: *"As both `Pₖ` and `φ(a₂)ₖ` are killed by `N₂`, while `φ(a₁)` is killed by
`N₁`, this is impossible unless `φ(a₁) = 0`."* Bezout in the point group. -/
theorem Point.eq_zero_of_killed_coprime {T : Scheme.{u}} {g : T ⟶ S} (Q : E.Point g)
    (M K : ℕ) (hMK : Nat.Coprime M K) (hM : (M : ℤ) • Q = 0) (hK : (K : ℤ) • Q = 0) :
    Q = 0 := by
  obtain ⟨u, v, huv⟩ : ∃ u v : ℤ, u * M + v * K = 1 := by
    refine ⟨Nat.gcdA M K, Nat.gcdB M K, ?_⟩
    have := Nat.gcd_eq_gcd_ab M K
    rw [hMK] at this
    push_cast at this ⊢
    linarith
  calc Q = (1 : ℤ) • Q := (one_zsmul Q).symm
    _ = (u * M + v * K : ℤ) • Q := by rw [huv]
    _ = u • ((M : ℤ) • Q) + v • ((K : ℤ) • Q) := by
        rw [add_zsmul, mul_smul, mul_smul]
    _ = 0 := by rw [hM, hK, smul_zero, smul_zero, add_zero]

/-- **[W0-F3] (KM 1.7.2, `ℤ/N`-instance — the factorization core)** For coprime
`M, K ≥ 1`, a point `P ∈ E(S)` has Drinfeld exact order `M·K` iff `K·P` has exact
order `M` and `M·P` has exact order `K`.

KM 1.7.2 (print p. 26, verbatim): *"Then a homomorphism `φ : A → C(S)` is an
`A`-structure on `C/S` if and only if the two homomorphisms `φᵢ : Aᵢ → C(S)`,
`i = 1, 2`, are each `Aᵢ`-structures"* — instantiated at `A = ℤ/MK ≅ ℤ/M × ℤ/K`
(KM 1.7.1), where `φ = ⟨P⟩` restricts on the two factors to `⟨K·P⟩` and `⟨M·P⟩`
(the idempotent decomposition (3.5.1.3): `g ↦ (Bg, Ag)`).

Proof route (KM print pp. 27–31, transcribed in the decomposition artifact):
forward — split `G ≅ G[M] ×_S G[K]` (BB-DELIGNE `smul_eq_zero_of_factors` + the
coprime idempotent projector), force ranks geometrically, localize over the coprime
cover (`isSubgroup_of_openCover`), read distinctness on the étale factor (1.5.3
(3)⟹(1)), and run the translation-union argument `G = ∐ₐ Trans(φ(a₁))*(D₂)` for the
other factor; converse — `G₁ ×_S G₂ ↪ C` by the coprime-rank sum immersion, its
image divisor is `Σ [φ(a)]` by disjointness of translates. -/
theorem Section.hasExactOrder_mul_iff (P : E.Section) (M K : ℕ) [NeZero M] [NeZero K]
    (hMK : Nat.Coprime M K) :
    haveI : NeZero (M * K) := ⟨Nat.mul_ne_zero (NeZero.ne M) (NeZero.ne K)⟩
    P.HasExactOrder E (M * K) ↔
      ((K : ℤ) • P).HasExactOrder E M ∧ ((M : ℤ) • P).HasExactOrder E K := by sorry

/-- **[W0-F4] (KM 3.5.1, Γ₁-line)** The canonical factorization equivalence on
Drinfeld `Γ₁`-structures for a coprime splitting `N = M·K`:
`P ↦ (K·P, M·P)` (KM's choice (3.5.1.3), *"for `Γ₁(N)`: point `P` of exact order `N`
↦ points `BP, AP` of exact orders `A, B`"*), with inverse the CRT-weighted sum
`(P₁, P₂) ↦ K'·K·P₁ + M'·M·P₂`-normalised recombination (KM: the two structures
recombine because *"the second is `(A+B)` times the first"*, the first being the
inverse of the sum map (3.5.1.2)). Functorial in `S` (KM 3.5.1: *"functorial
isomorphisms"*) — naturality is recorded by `gammaOneStrFactorEquiv_fst/snd` and
consumed at the moduli-problem level in a later wave increment. -/
noncomputable def gammaOneStrFactorEquiv (M K : ℕ) [NeZero M] [NeZero K]
    (hMK : Nat.Coprime M K) :
    haveI : NeZero (M * K) := ⟨Nat.mul_ne_zero (NeZero.ne M) (NeZero.ne K)⟩
    { P : E.Section // P.HasExactOrder E (M * K) } ≃
      ({ P : E.Section // P.HasExactOrder E M } ×
        { P : E.Section // P.HasExactOrder E K }) := sorry

/-- **[W0-F4-fst]** The first component of the factorization equivalence is `K·P`
(KM 3.5.1's explicit `Γ₁`-line, first output `BP`). -/
theorem gammaOneStrFactorEquiv_fst (M K : ℕ) [NeZero M] [NeZero K]
    (hMK : Nat.Coprime M K)
    (P : { P : E.Section // haveI : NeZero (M * K) :=
      ⟨Nat.mul_ne_zero (NeZero.ne M) (NeZero.ne K)⟩; P.HasExactOrder E (M * K) }) :
    ((gammaOneStrFactorEquiv E M K hMK) P).1.1 = (K : ℤ) • P.1 := by sorry

/-- **[W0-F4-snd]** The second component of the factorization equivalence is `M·P`
(KM 3.5.1's explicit `Γ₁`-line, second output `AP`). -/
theorem gammaOneStrFactorEquiv_snd (M K : ℕ) [NeZero M] [NeZero K]
    (hMK : Nat.Coprime M K)
    (P : { P : E.Section // haveI : NeZero (M * K) :=
      ⟨Nat.mul_ne_zero (NeZero.ne M) (NeZero.ne K)⟩; P.HasExactOrder E (M * K) }) :
    ((gammaOneStrFactorEquiv E M K hMK) P).2.1 = (M : ℤ) • P.1 := by sorry

end ModularCurves
