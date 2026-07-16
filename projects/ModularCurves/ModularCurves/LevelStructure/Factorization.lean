/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.LevelStructure.ExactOrder
import ModularCurves.GroupScheme.DeligneOrder
import ModularCurves.GroupScheme.CartierDivisorMapIso
import ModularCurves.GroupScheme.TranslationBySection
import ModularCurves.LevelStructure.IsoTransport
import ModularCurves.EllipticCurve.EndomorphismDegree

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

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory

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

/-- Pointwise formula for pushforward along an isomorphism: sections of the moved ideal
are the inverse images of sections over the preimage affine open. -/
theorem _root_.AlgebraicGeometry.Scheme.IdealSheafData.map_hom_apply
    {C : Scheme.{u}} (e : C ≅ C) (I : C.IdealSheafData) (U : C.affineOpens) :
    (I.map e.hom).ideal U
      = Ideal.comap (e.hom.app U.1).hom
          (I.ideal ⟨e.hom ⁻¹ᵁ U.1, U.2.preimage e.hom⟩) := by
  rw [Scheme.IdealSheafData.map, Scheme.Hom.ker_apply, Scheme.Hom.comp_app]
  erw [CommRingCat.hom_comp]
  rw [← RingHom.comap_ker]
  exact congrArg (Ideal.comap (e.hom.app U.1).hom)
    (Scheme.IdealSheafData.ker_subschemeι_app I
      (⟨e.hom ⁻¹ᵁ U.1, U.2.preimage e.hom⟩ : C.affineOpens))

/-- Pushforward along an isomorphism is multiplicative on ideal sheaves (pointwise it is
inverse image along the section ring isomorphisms, i.e. direct image along the inverse). -/
theorem _root_.AlgebraicGeometry.Scheme.IdealSheafData.map_hom_mul
    {C : Scheme.{u}} (e : C ≅ C) (I J : C.IdealSheafData) :
    (I * J).map e.hom = I.map e.hom * J.map e.hom := by
  ext U
  haveI : IsIso (e.hom.app U.1) := inferInstance
  set φ := (asIso (e.hom.app U.1)).commRingCatIsoToRingEquiv with hφ
  have hco : ∀ A : Ideal Γ(C, e.hom ⁻¹ᵁ U.1),
      Ideal.comap (e.hom.app U.1).hom A = Ideal.map (φ.symm : _ →+* _) A := by
    intro A
    exact (Ideal.map_symm φ).symm
  simp only [Scheme.IdealSheafData.map_hom_apply e, Scheme.IdealSheafData.ideal_mul,
    Pi.mul_apply, hco, Ideal.map_mul]

/-- **[W0-F3-shift] (the `Trans(x)*` engine, KM print p. 30)** Translating a sections
divisor along an `S`-automorphism of the curve gives the divisor of the translated
sections: `Trans(φ)*(Σᵢ [Pᵢ]) = Σᵢ [φ(Pᵢ)]`. KM: *"G = Σ_{a₁} Trans(φ(a₁))*(D₂)"* —
this is the lemma that turns that display into divisor arithmetic. -/
theorem RelEffCartierDiv.mapIso_sectionsDivisor {C : Scheme.{u}} {π : C ⟶ S} {n : ℕ}
    (Ps : Fin n → { z : S ⟶ C // z ≫ π = 𝟙 S }) (e : C ≅ C) (he : e.hom ≫ π = π) :
    RelEffCartierDiv.mapIso e he (RelEffCartierDiv.sectionsDivisor π Ps)
      = RelEffCartierDiv.sectionsDivisor π
          (fun i => ⟨(Ps i).1 ≫ e.hom, by rw [Category.assoc, he, (Ps i).2]⟩) := by
  apply RelEffCartierDiv.ext
  rw [RelEffCartierDiv.mapIso_ideal, ← Scheme.IdealSheafData.map_hom_eq_comap_inv]
  by_cases hπ : IsSeparated π ∧ SmoothOfRelativeDimension 1 π
  · rw [RelEffCartierDiv.sectionsDivisor, RelEffCartierDiv.sectionsDivisor,
      dif_pos hπ, dif_pos hπ]
    have hmapHom : ∀ J : C.IdealSheafData × C.IdealSheafData,
        (J.1 * J.2).map e.hom = J.1.map e.hom * J.2.map e.hom :=
      fun J => Scheme.IdealSheafData.map_hom_mul e J.1 J.2
    let μ : C.IdealSheafData →* C.IdealSheafData :=
      { toFun := fun J => J.map e.hom
        map_one' := by
          rw [Scheme.IdealSheafData.one_eq_top, Scheme.IdealSheafData.map_top]
        map_mul' := fun I J => Scheme.IdealSheafData.map_hom_mul e I J }
    have := map_prod μ (fun i => Scheme.Hom.ker (Ps i).1) Finset.univ
    simp only [μ, MonoidHom.coe_mk, OneHom.coe_mk] at this
    rw [this]
    exact Finset.prod_congr rfl fun i _ =>
      (Scheme.Hom.ker_comp (Ps i).1 e.hom).symm
  · rw [RelEffCartierDiv.sectionsDivisor, RelEffCartierDiv.sectionsDivisor,
      dif_neg hπ, dif_neg hπ, Scheme.IdealSheafData.map_top]

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

/-- **[W0-F3-transpt] (KM print p. 30's `Trans(φ(a₁))` on points)** Transporting a point
through translation-by-`x` adds the pulled section: `Trans(x)(Q) = Q + x|_T`. With
`mapIso_sectionsDivisor`/`sectionsDivisor_pointMap_ideal` this reads KM's translated
divisor `Trans(φ(a₁))*(D₂)` on `T`-points. -/
theorem pointMapOfHom_translateBy (x : 𝟙_ (CategoryTheory.Over S) ⟶ E.asOver)
    {T : Scheme.{u}} {g : T ⟶ S} (Q : E.Point g) :
    EllipticCurve.pointMapOfHom (E.translateBy x) Q
      = Q + (E.pointEquivOverHom g).symm
          (CategoryTheory.CartesianMonoidalCategory.toUnit (CategoryTheory.Over.mk g) ≫ x) := by
  letI : CommGroup (CategoryTheory.Over.mk g ⟶ E.asOver) := CategoryTheory.Hom.commGroup
  refine (E.pointEquivOverHom g).injective ?_
  rw [EllipticCurve.pointEquivOverHom_add, Equiv.apply_symm_apply]
  have hnat : (E.pointEquivOverHom g) (EllipticCurve.pointMapOfHom (E.translateBy x) Q)
      = (E.pointEquivOverHom g) Q ≫ E.translateBy x := by
    apply CategoryTheory.Over.OverMorphism.ext
    rw [CategoryTheory.Over.comp_left]
    rfl
  rw [hnat, EllipticCurve.translateBy_def, MonObj.comp_mul, Category.comp_id]
  congr 1
  rw [EllipticCurve.constPt, ← Category.assoc]
  congr 1
  exact CategoryTheory.CartesianMonoidalCategory.toUnit_unique _ _

/-- **[F3-crt-pts] (KM 3.5.1.1–3.5.1.3)** An abelian group killed by coprime `M·K`
splits into its `M`- and `K`-torsion parts via KM's second isomorphism `g ↦ (Kg, Mg)`,
with Bezout inverse `(g₁, g₂) ↦ v•g₁ + u•g₂` (`uM + vK = 1`). KM (verbatim, p. 101):
*"we have two distinct canonical isomorphisms (3.5.1.1) `G ⟶ G[A] × G[B]` … the second
is `g ↦ (Bg, Ag)`."* -/
noncomputable def killedCoprimeSplitEquiv {G : Type*} [AddCommGroup G] (M K : ℕ)
    (hMK : Nat.Coprime M K) (hkill : ∀ g : G, ((M * K : ℕ) : ℤ) • g = 0) :
    G ≃ { g : G // (M : ℤ) • g = 0 } × { g : G // (K : ℤ) • g = 0 } := by
  set u : ℤ := Nat.gcdA M K with hu
  set v : ℤ := Nat.gcdB M K with hv
  have huv : u * M + v * K = 1 := by
    have h := Nat.gcd_eq_gcd_ab M K
    rw [hMK] at h
    rw [hu, hv]
    push_cast at h ⊢
    linarith
  refine
    { toFun := fun g => (⟨(K : ℤ) • g, ?_⟩, ⟨(M : ℤ) • g, ?_⟩)
      invFun := fun p => v • (p.1 : G) + u • (p.2 : G)
      left_inv := fun g => ?_
      right_inv := fun p => ?_ }
  · rw [← mul_smul, show ((M : ℤ)) * K = ((M * K : ℕ) : ℤ) by push_cast; ring, hkill]
  · rw [← mul_smul, show ((K : ℤ)) * M = ((M * K : ℕ) : ℤ) by push_cast; ring, hkill]
  · -- v•(K•g) + u•(M•g) = (vK + uM)•g = g
    show v • ((K : ℤ) • g) + u • ((M : ℤ) • g) = g
    rw [← mul_smul, ← mul_smul, ← add_smul, show v * K + u * M = 1 by linarith, one_smul]
  · -- roundtrip on pairs
    obtain ⟨⟨g₁, hg₁⟩, ⟨g₂, hg₂⟩⟩ := p
    refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
    · show (K : ℤ) • (v • g₁ + u • g₂) = g₁
      rw [smul_add, ← mul_smul, ← mul_smul,
        show (K : ℤ) * v = 1 - u * M by linarith,
        show (K : ℤ) * u = u * K by ring,
        sub_smul, one_smul, mul_smul, mul_smul, hg₁, hg₂]
      simp
    · show (M : ℤ) • (v • g₁ + u • g₂) = g₂
      rw [smul_add, ← mul_smul, ← mul_smul,
        show (M : ℤ) * v = v * M by ring,
        show (M : ℤ) * u = 1 - v * K by linarith,
        sub_smul, one_smul, mul_smul, mul_smul, hg₁, hg₂]
      simp

/-- **[F3-univ] (the universal-point trick — KM p. 27's projector, scheme level)** For a
subgroup divisor `D` and any `c : ℤ`, multiplication by `c` restricts to an endomorphism
of the divisor subscheme: the inclusion `ι` is itself a `T`-point of `E` (`T` the
subscheme) lying in the subgroup `H(T)`, hence so is `c • ι`, whose underlying morphism
is `ι ≫ [c]` — and its membership witness IS the restriction. No descent or Yoneda
machinery: the subgroup structure on points does all the work. -/
theorem RelEffCartierDiv.IsSubgroup.exists_smul_restrict {D : RelEffCartierDiv E.π}
    (hD : D.IsSubgroup E) (c : ℤ) :
    ∃ w : D.ideal.subscheme ⟶ D.ideal.subscheme,
      w ≫ D.ideal.subschemeι = D.ideal.subschemeι ≫ E.mulByHom c := by
  obtain ⟨H, hH⟩ := hD (D.ideal.subschemeι ≫ E.π)
  -- the universal point: the inclusion itself
  set ι₀ : E.Point (D.ideal.subschemeι ≫ E.π) := ⟨D.ideal.subschemeι, rfl⟩ with hι₀
  have hmem : ι₀ ∈ H := (hH ι₀).mpr ⟨𝟙 _, Category.id_comp _⟩
  have hsmul : c • ι₀ ∈ H := AddSubgroup.zsmul_mem H hmem c
  obtain ⟨w, hw⟩ := (hH (c • ι₀)).mp hsmul
  refine ⟨w, hw.trans ?_⟩
  exact E.point_smul_eq_comp_mulBy _ c ι₀

/-- **[F3-idem] (KM p. 27's projector is idempotent)** On a subgroup divisor of constant
degree `N`, the restriction of `[c]` for `c² ≡ c (mod N)` is an idempotent endomorphism
of the divisor subscheme: the boundary square identifies `w ∘ w` and `w` against the
monomorphism `ι` through `[c] ∘ [c] = [c²]` and the killed-point congruence. KM (p. 27,
verbatim): *"G[N₁] is a direct factor of G, corresponding to the S-projector on G,
P₁ + P₂ ↦ P₁."* -/
theorem RelEffCartierDiv.IsSubgroup.exists_smul_restrict_idem {D : RelEffCartierDiv E.π}
    (hD : D.IsSubgroup E) {N : ℕ} [NeZero N] (hdeg : ∀ s : S, D.degree s = N)
    {c : ℤ} (hc : (c * c) % (N : ℤ) = c % (N : ℤ)) :
    ∃ w : D.ideal.subscheme ⟶ D.ideal.subscheme,
      (w ≫ D.ideal.subschemeι = D.ideal.subschemeι ≫ E.mulByHom c) ∧ w ≫ w = w := by
  obtain ⟨H, hH⟩ := hD (D.ideal.subschemeι ≫ E.π)
  set ι₀ : E.Point (D.ideal.subschemeι ≫ E.π) := ⟨D.ideal.subschemeι, rfl⟩ with hι₀
  have hmem : ι₀ ∈ H := (hH ι₀).mpr ⟨𝟙 _, Category.id_comp _⟩
  obtain ⟨w, hw⟩ := (hH (c • ι₀)).mp (AddSubgroup.zsmul_mem H hmem c)
  have hkill : ((N : ℕ) : ℤ) • ι₀ = 0 :=
    RelEffCartierDiv.IsSubgroup.smul_eq_zero_of_factors E hD hdeg _ ι₀
      ⟨𝟙 _, Category.id_comp _⟩
  have hcsq : (c * c) • ι₀ = c • ι₀ := zsmul_congr_of_kill hkill hc
  have hbd : w ≫ D.ideal.subschemeι = D.ideal.subschemeι ≫ E.mulByHom c :=
    hw.trans (E.point_smul_eq_comp_mulBy _ c ι₀)
  refine ⟨w, hbd, ?_⟩
  have hmbh : E.mulByHom c ≫ E.mulByHom c = E.mulByHom (c * c) := by
    show (CategoryTheory.Over.forget S).map (E.mulBy c)
          ≫ (CategoryTheory.Over.forget S).map (E.mulBy c)
        = (CategoryTheory.Over.forget S).map (E.mulBy (c * c))
    rw [← Functor.map_comp, E.mulBy_comp]
  rw [← cancel_mono D.ideal.subschemeι, Category.assoc, hbd, ← Category.assoc, hbd,
    Category.assoc, hmbh]
  calc D.ideal.subschemeι ≫ E.mulByHom (c * c)
      = ((c * c) • ι₀).1 := (E.point_smul_eq_comp_mulBy _ (c * c) ι₀).symm
    _ = (c • ι₀).1 := congrArg Subtype.val hcsq
    _ = w ≫ D.ideal.subschemeι := hw.symm
    _ = D.ideal.subschemeι ≫ E.mulByHom c := hbd

/-- **[F3-ker] (route a′, brick 1)** The `c`-kernel of a divisor subscheme: the pullback
of `[c]` restricted to the subscheme against the zero section — `Ker([c] : G → E)` as a
scheme. Imitates the `E.torsion` kernel-pullback pattern (T-B6). -/
noncomputable def RelEffCartierDiv.smulKernel (D : RelEffCartierDiv E.π) (c : ℤ) : Scheme :=
  pullback (D.ideal.subschemeι ≫ E.mulByHom c) E.zero

/-- The structure morphism of the `c`-kernel over the base. -/
noncomputable def RelEffCartierDiv.smulKernelπ (D : RelEffCartierDiv E.π) (c : ℤ) :
    D.smulKernel E c ⟶ S :=
  pullback.snd _ _

/-- The inclusion of the `c`-kernel into the divisor subscheme. -/
noncomputable def RelEffCartierDiv.smulKernelι (D : RelEffCartierDiv E.π) (c : ℤ) :
    D.smulKernel E c ⟶ D.ideal.subscheme :=
  pullback.fst _ _

/-- **[F3-ker-of]** A `T`-point of the `c`-kernel over `t` yields a `c`-killed point of
`E` factoring through the divisor. -/
theorem RelEffCartierDiv.smulKernel_point {D : RelEffCartierDiv E.π} {c : ℤ}
    {T : Scheme.{u}} {t : T ⟶ S} (h : T ⟶ D.smulKernel E c)
    (hh : h ≫ D.smulKernelπ E c = t) :
    ∃ Q : E.Point t, (c • Q = 0) ∧
      ∃ w : T ⟶ D.ideal.subscheme, w ≫ D.ideal.subschemeι = Q.1 := by
  have hcond : D.smulKernelι E c ≫ D.ideal.subschemeι ≫ E.mulByHom c
      = D.smulKernelπ E c ≫ E.zero := by
    rw [RelEffCartierDiv.smulKernelι, RelEffCartierDiv.smulKernelπ, ← Category.assoc]
    exact pullback.condition (f := D.ideal.subschemeι ≫ E.mulByHom c) (g := E.zero)
  have hbase : D.smulKernelι E c ≫ D.ideal.subschemeι ≫ E.π = D.smulKernelπ E c := by
    have h2 := congrArg (· ≫ E.π) hcond
    simp only [Category.assoc, E.mulByHom_π, E.zero_π, Category.comp_id] at h2
    exact h2
  refine ⟨⟨h ≫ D.smulKernelι E c ≫ D.ideal.subschemeι, ?_⟩, ?_,
    ⟨h ≫ D.smulKernelι E c, by rw [Category.assoc]⟩⟩
  · rw [Category.assoc, Category.assoc, hbase, hh]
  · apply Subtype.ext
    rw [E.point_smul_eq_comp_mulBy, E.point_zero_val]
    show (h ≫ D.smulKernelι E c ≫ D.ideal.subschemeι) ≫ E.mulByHom c = t ≫ E.zero
    rw [Category.assoc, Category.assoc]
    rw [show D.smulKernelι E c ≫ D.ideal.subschemeι ≫ E.mulByHom c
        = D.smulKernelπ E c ≫ E.zero from hcond, ← Category.assoc, hh]

/-- **[F3-ker-to]** Conversely, a `c`-killed point factoring through the divisor lifts
to the `c`-kernel (pullback universal property). -/
theorem RelEffCartierDiv.exists_smulKernel_lift {D : RelEffCartierDiv E.π} {c : ℤ}
    {T : Scheme.{u}} {t : T ⟶ S} (Q : E.Point t) (hQ : c • Q = 0)
    (w : T ⟶ D.ideal.subscheme) (hw : w ≫ D.ideal.subschemeι = Q.1) :
    ∃ h : T ⟶ D.smulKernel E c,
      h ≫ D.smulKernelι E c = w ∧ h ≫ D.smulKernelπ E c = t := by
  have hkill : (Q : T ⟶ E.E) ≫ E.mulByHom c = t ≫ E.zero := by
    have hval := congrArg Subtype.val hQ
    rw [E.point_smul_eq_comp_mulBy] at hval
    rw [hval]
    exact E.point_zero_val t
  have hagree : w ≫ (D.ideal.subschemeι ≫ E.mulByHom c) = t ≫ E.zero := by
    rw [← Category.assoc, hw]
    exact hkill
  exact ⟨pullback.lift w t hagree, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩

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
