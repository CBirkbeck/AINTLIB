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
import ModularCurves.EllipticCurve.MulByHomFlatFibre
import ModularCurves.ForMathlib.FlatOfRetract
import ModularCurves.ForMathlib.FinrankPullbackComp
import ModularCurves.ForMathlib.EtaleSectionsCount

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

/-- **[F3-castBase]** Transport of the point group along an equality of base
morphisms (the `𝟙 ≫ g = g` bookkeeping equiv for base-change round-trips). -/
noncomputable def _root_.ModularCurves.EllipticCurve.Point.castBase
    {S : Scheme.{u}} (E : EllipticCurve S) {T : Scheme.{u}} {g₁ g₂ : T ⟶ S}
    (h : g₁ = g₂) : E.Point g₁ ≃+ E.Point g₂ := by
  subst h
  exact AddEquiv.refl _

@[simp]
lemma _root_.ModularCurves.EllipticCurve.Point.castBase_coe
    {S : Scheme.{u}} (E : EllipticCurve S) {T : Scheme.{u}} {g₁ g₂ : T ⟶ S}
    (h : g₁ = g₂) (x : E.Point g₁) :
    (EllipticCurve.Point.castBase E h x).1 = x.1 := by
  subst h
  rfl

/-- **[F3-fibre-instance]** Finiteness of `[n]` descends to base-changed curves: the
`[n]`-square is cartesian (`isPullback_mulByHom_baseChange`) and `IsFinite` is stable
under base change. -/
theorem _root_.ModularCurves.EllipticCurve.isFinite_mulByHom_baseChange
    {S : Scheme.{u}} (E : EllipticCurve S) {T : Scheme.{u}} (g : T ⟶ S) (n : ℤ)
    [hfin : IsFinite (E.mulByHom n)] : IsFinite ((E.baseChange g).mulByHom n) :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (P := @IsFinite) (ModularCurves.isPullback_mulByHom_baseChange E g n).flip hfin

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

/-- **[F3-cauchy] (the De-Ga IV 5.3-9 dodge)** Every prime dividing the order of a
finite abelian group killed by `M` divides `M` — Cauchy's theorem. Replaces KM's
citation *"the rank of `G[N₁]` divides a power of `N₁` (cf. [De-Ga IV, §3, 5.3-9])"*
on the étale locus. -/
theorem prime_dvd_of_killed {G : Type*} [AddCommGroup G] [Finite G] (M : ℕ)
    (hkill : ∀ g : G, (M : ℤ) • g = 0) {p : ℕ} (hp : p.Prime)
    (hdvd : p ∣ Nat.card G) : p ∣ M := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := Multiplicative G) p
    (show p ∣ Nat.card (Multiplicative G) from hdvd)
  have h2 : addOrderOf (Multiplicative.toAdd x) ∣ M := by
    rw [addOrderOf_dvd_iff_nsmul_eq_zero]
    have := hkill (Multiplicative.toAdd x)
    rwa [natCast_zsmul] at this
  have h3 : addOrderOf (Multiplicative.toAdd x) = p := by
    rw [← orderOf_ofAdd_eq_addOrderOf]
    exact hx
  rwa [h3] at h2

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

/-- The kernel inclusion composed with the divisor inclusion lies over the kernel's
structure morphism. -/
theorem RelEffCartierDiv.smulKernelι_subschemeι_π (D : RelEffCartierDiv E.π) (c : ℤ) :
    D.smulKernelι E c ≫ D.ideal.subschemeι ≫ E.π = D.smulKernelπ E c := by
  have hcond : D.smulKernelι E c ≫ D.ideal.subschemeι ≫ E.mulByHom c
      = D.smulKernelπ E c ≫ E.zero := by
    rw [RelEffCartierDiv.smulKernelι, RelEffCartierDiv.smulKernelπ, ← Category.assoc]
    exact pullback.condition (f := D.ideal.subschemeι ≫ E.mulByHom c) (g := E.zero)
  have h2 := congrArg (· ≫ E.π) hcond
  simp only [Category.assoc, E.mulByHom_π, E.zero_π, Category.comp_id] at h2
  exact h2

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

/-- **[F3-toKer] (KM (3.5.1.3)'s components at scheme level)** On a degree-`N` subgroup
divisor with `N` killing the multiplier product, scaling the universal point by `c`
lands in the `c'`-kernel whenever `c' * c ≡ 0 (mod N)`: this produces the projection
`G ⟶ Ker([c'] : G → E)` over `S`. Instantiated at `(c, c') = (K, M)` and `(M, K)` these
are the two components of KM's product decomposition. -/
theorem RelEffCartierDiv.IsSubgroup.exists_toSmulKernel {D : RelEffCartierDiv E.π}
    (hD : D.IsSubgroup E) {N : ℕ} [NeZero N] (hdeg : ∀ s : S, D.degree s = N)
    {c c' : ℤ} (hcc : (c' * c) % (N : ℤ) = 0) :
    ∃ φ : D.ideal.subscheme ⟶ D.smulKernel E c',
      φ ≫ D.smulKernelπ E c' = D.ideal.subschemeι ≫ E.π ∧
      φ ≫ D.smulKernelι E c' ≫ D.ideal.subschemeι
        = D.ideal.subschemeι ≫ E.mulByHom c := by
  obtain ⟨H, hH⟩ := hD (D.ideal.subschemeι ≫ E.π)
  set ι₀ : E.Point (D.ideal.subschemeι ≫ E.π) := ⟨D.ideal.subschemeι, rfl⟩ with hι₀
  have hmem : ι₀ ∈ H := (hH ι₀).mpr ⟨𝟙 _, Category.id_comp _⟩
  have hkill : ((N : ℕ) : ℤ) • ι₀ = 0 :=
    RelEffCartierDiv.IsSubgroup.smul_eq_zero_of_factors E hD hdeg _ ι₀
      ⟨𝟙 _, Category.id_comp _⟩
  -- the scaled universal point is c'-killed
  have hckill : c' • (c • ι₀) = 0 := by
    rw [← mul_smul]
    calc (c' * c) • ι₀ = (0 : ℤ) • ι₀ := zsmul_congr_of_kill hkill (by
        rw [hcc, Int.zero_emod])
      _ = 0 := zero_zsmul ι₀
  obtain ⟨w, hw⟩ := (hH (c • ι₀)).mp (AddSubgroup.zsmul_mem H hmem c)
  obtain ⟨φ, hφι, hφπ⟩ := RelEffCartierDiv.exists_smulKernel_lift E (c • ι₀) hckill w hw
  refine ⟨φ, hφπ, ?_⟩
  rw [← Category.assoc, hφι, hw]
  exact E.point_smul_eq_comp_mulBy _ c ι₀

/-- **[F3-combMap] (KM (3.5.1.2)'s sum map, ℤ-weighted)** Any ℤ-combination of the two
kernel-inclusion points over the fibre product of kernels lies in the subgroup `H`; its
membership witness is a scheme morphism `Ker[c₁] ×_S Ker[c₂] ⟶ G`. At `(1,1)` this is
KM's sum map (p. 31); at the Bezout weights `(v,u)` it inverts the (3.5.1.3) product
map (KM: *"the second is `(A+B)` times the first"*). -/
theorem RelEffCartierDiv.IsSubgroup.exists_combMap {D : RelEffCartierDiv E.π}
    (hD : D.IsSubgroup E) (c₁ c₂ a b : ℤ) :
    ∃ σ : pullback (D.smulKernelπ E c₁) (D.smulKernelπ E c₂) ⟶ D.ideal.subscheme,
      σ ≫ D.ideal.subschemeι
        = ((a • (⟨pullback.fst (D.smulKernelπ E c₁) (D.smulKernelπ E c₂)
              ≫ D.smulKernelι E c₁ ≫ D.ideal.subschemeι, by
                rw [Category.assoc, Category.assoc,
                  RelEffCartierDiv.smulKernelι_subschemeι_π]⟩ :
            E.Point (pullback.fst (D.smulKernelπ E c₁) (D.smulKernelπ E c₂)
              ≫ D.smulKernelπ E c₁))
          + b • (⟨pullback.snd (D.smulKernelπ E c₁) (D.smulKernelπ E c₂)
              ≫ D.smulKernelι E c₂ ≫ D.ideal.subschemeι, by
                rw [Category.assoc, Category.assoc,
                  RelEffCartierDiv.smulKernelι_subschemeι_π, ← pullback.condition]⟩ :
            E.Point (pullback.fst (D.smulKernelπ E c₁) (D.smulKernelπ E c₂)
              ≫ D.smulKernelπ E c₁))) :
          E.Point _).1 := by
  obtain ⟨H, hH⟩ := hD (pullback.fst (D.smulKernelπ E c₁) (D.smulKernelπ E c₂)
    ≫ D.smulKernelπ E c₁)
  refine (hH _).mp (H.add_mem (H.zsmul_mem ?_ a) (H.zsmul_mem ?_ b))
  · exact (hH _).mpr ⟨pullback.fst _ _ ≫ D.smulKernelι E c₁, by
      rw [Category.assoc]⟩
  · exact (hH _).mpr ⟨pullback.snd _ _ ≫ D.smulKernelι E c₂, by
      rw [Category.assoc]⟩

section ProductDecomposition

variable {D : RelEffCartierDiv E.π} (hD : D.IsSubgroup E) {N : ℕ} [NeZero N]

/-- **[F3-prod-toM]** The chosen `(3.5.1.3)`-projection `G ⟶ Ker[c']` (data form of
`exists_toSmulKernel`). -/
noncomputable def RelEffCartierDiv.IsSubgroup.toSmulKernel
    (hdeg : ∀ s : S, D.degree s = N) {c c' : ℤ} (hcc : (c' * c) % (N : ℤ) = 0) :
    D.ideal.subscheme ⟶ D.smulKernel E c' :=
  (RelEffCartierDiv.IsSubgroup.exists_toSmulKernel E hD hdeg hcc).choose

theorem RelEffCartierDiv.IsSubgroup.toSmulKernel_π
    (hdeg : ∀ s : S, D.degree s = N) {c c' : ℤ} (hcc : (c' * c) % (N : ℤ) = 0) :
    RelEffCartierDiv.IsSubgroup.toSmulKernel E hD hdeg hcc ≫ D.smulKernelπ E c'
      = D.ideal.subschemeι ≫ E.π :=
  (RelEffCartierDiv.IsSubgroup.exists_toSmulKernel E hD hdeg hcc).choose_spec.1

theorem RelEffCartierDiv.IsSubgroup.toSmulKernel_ι
    (hdeg : ∀ s : S, D.degree s = N) {c c' : ℤ} (hcc : (c' * c) % (N : ℤ) = 0) :
    RelEffCartierDiv.IsSubgroup.toSmulKernel E hD hdeg hcc ≫ D.smulKernelι E c'
        ≫ D.ideal.subschemeι
      = D.ideal.subschemeι ≫ E.mulByHom c :=
  (RelEffCartierDiv.IsSubgroup.exists_toSmulKernel E hD hdeg hcc).choose_spec.2

/-- **[F3-prodMap]** KM's product decomposition map `G ⟶ Ker[M] ×_S Ker[K]`,
components the `(3.5.1.3)`-projections `(K·, M·)`. -/
noncomputable def RelEffCartierDiv.IsSubgroup.prodMap
    (hdeg : ∀ s : S, D.degree s = N) {c₁ c₂ : ℤ}
    (h₁ : (c₁ * c₂) % (N : ℤ) = 0) (h₂ : (c₂ * c₁) % (N : ℤ) = 0) :
    D.ideal.subscheme ⟶ pullback (D.smulKernelπ E c₁) (D.smulKernelπ E c₂) :=
  pullback.lift (RelEffCartierDiv.IsSubgroup.toSmulKernel E hD hdeg h₁)
    (RelEffCartierDiv.IsSubgroup.toSmulKernel E hD hdeg h₂)
    ((RelEffCartierDiv.IsSubgroup.toSmulKernel_π E hD hdeg h₁).trans
      (RelEffCartierDiv.IsSubgroup.toSmulKernel_π E hD hdeg h₂).symm)

/-- **[F3-combMap-def]** The chosen ℤ-weighted combination map
`Ker[c₁] ×_S Ker[c₂] ⟶ G` (data form of `exists_combMap`). -/
noncomputable def RelEffCartierDiv.IsSubgroup.combMap (c₁ c₂ a b : ℤ) :
    pullback (D.smulKernelπ E c₁) (D.smulKernelπ E c₂) ⟶ D.ideal.subscheme :=
  (RelEffCartierDiv.IsSubgroup.exists_combMap E hD c₁ c₂ a b).choose

theorem RelEffCartierDiv.IsSubgroup.combMap_ι (c₁ c₂ a b : ℤ) :
    RelEffCartierDiv.IsSubgroup.combMap E hD c₁ c₂ a b ≫ D.ideal.subschemeι
      = ((a • (⟨pullback.fst (D.smulKernelπ E c₁) (D.smulKernelπ E c₂)
            ≫ D.smulKernelι E c₁ ≫ D.ideal.subschemeι, by
              rw [Category.assoc, Category.assoc,
                RelEffCartierDiv.smulKernelι_subschemeι_π]⟩ :
          E.Point (pullback.fst (D.smulKernelπ E c₁) (D.smulKernelπ E c₂)
            ≫ D.smulKernelπ E c₁))
        + b • (⟨pullback.snd (D.smulKernelπ E c₁) (D.smulKernelπ E c₂)
            ≫ D.smulKernelι E c₂ ≫ D.ideal.subschemeι, by
              rw [Category.assoc, Category.assoc,
                RelEffCartierDiv.smulKernelι_subschemeι_π, ← pullback.condition]⟩ :
          E.Point (pullback.fst (D.smulKernelπ E c₁) (D.smulKernelπ E c₂)
            ≫ D.smulKernelπ E c₁))) :
        E.Point _).1 :=
  (RelEffCartierDiv.IsSubgroup.exists_combMap E hD c₁ c₂ a b).choose_spec

/-- **[F3-R1] (KM p. 27's roundtrip, easy direction)** The Bezout-weighted combination
retracts the product decomposition: `prodMap ≫ combMap(v, u) ≫ ι = ι`. Pure point
arithmetic at the uniform base `G`: the restricted kernel points are the `K`- and
`M`-scalings of the universal point, and `vK + uM = 1`. -/
theorem RelEffCartierDiv.IsSubgroup.prodMap_combMap_ι (M K : ℕ) [NeZero M] [NeZero K]
    (hMK : Nat.Coprime M K) [NeZero (M * K)]
    (hdeg : ∀ s : S, D.degree s = M * K)
    (h₁ : ((M : ℤ) * K) % ((M * K : ℕ) : ℤ) = 0) (h₂ : ((K : ℤ) * M) % ((M * K : ℕ) : ℤ) = 0) :
    RelEffCartierDiv.IsSubgroup.prodMap E hD hdeg h₁ h₂
        ≫ RelEffCartierDiv.IsSubgroup.combMap E hD (M : ℤ) (K : ℤ)
            (Nat.gcdB M K) (Nat.gcdA M K)
        ≫ D.ideal.subschemeι
      = D.ideal.subschemeι := by
  set u : ℤ := Nat.gcdA M K with hu
  set v : ℤ := Nat.gcdB M K with hv
  have huv : u * M + v * K = 1 := by
    have h := Nat.gcd_eq_gcd_ab M K
    rw [hMK] at h
    rw [hu, hv]
    push_cast at h ⊢
    linarith
  set P := RelEffCartierDiv.IsSubgroup.prodMap E hD hdeg h₁ h₂ with hPdef
  have hσ := RelEffCartierDiv.IsSubgroup.combMap_ι E hD (M : ℤ) (K : ℤ) v u
  rw [hσ]
  -- switch to point arithmetic at the base pulled along P
  set Q₁ : E.Point (pullback.fst (D.smulKernelπ E (M : ℤ)) (D.smulKernelπ E (K : ℤ))
      ≫ D.smulKernelπ E (M : ℤ)) :=
    ⟨pullback.fst _ _ ≫ D.smulKernelι E (M : ℤ) ≫ D.ideal.subschemeι, by
      rw [Category.assoc, Category.assoc, RelEffCartierDiv.smulKernelι_subschemeι_π]⟩
  set Q₂ : E.Point (pullback.fst (D.smulKernelπ E (M : ℤ)) (D.smulKernelπ E (K : ℤ))
      ≫ D.smulKernelπ E (M : ℤ)) :=
    ⟨pullback.snd _ _ ≫ D.smulKernelι E (K : ℤ) ≫ D.ideal.subschemeι, by
      rw [Category.assoc, Category.assoc, RelEffCartierDiv.smulKernelι_subschemeι_π,
        ← pullback.condition]⟩
  show P ≫ (v • Q₁ + u • Q₂).1 = D.ideal.subschemeι
  -- the universal point at the pulled base
  have hbase : D.ideal.subschemeι ≫ E.π
      = P ≫ pullback.fst (D.smulKernelπ E (M : ℤ)) (D.smulKernelπ E (K : ℤ))
        ≫ D.smulKernelπ E (M : ℤ) := by
    rw [← Category.assoc, hPdef, RelEffCartierDiv.IsSubgroup.prodMap, pullback.lift_fst,
      RelEffCartierDiv.IsSubgroup.toSmulKernel_π]
  set ι₀' : E.Point (P ≫ pullback.fst (D.smulKernelπ E (M : ℤ))
      (D.smulKernelπ E (K : ℤ)) ≫ D.smulKernelπ E (M : ℤ)) :=
    ⟨D.ideal.subschemeι, hbase⟩ with hι₀'
  -- the restriction AddMonoidHom
  have hrestr : ∀ (R₁ R₂ : E.Point (pullback.fst (D.smulKernelπ E (M : ℤ))
      (D.smulKernelπ E (K : ℤ)) ≫ D.smulKernelπ E (M : ℤ))) (m n : ℤ),
      EllipticCurve.Point.restrict E P (m • R₁ + n • R₂)
        = m • EllipticCurve.Point.restrict E P R₁
          + n • EllipticCurve.Point.restrict E P R₂ := by
    intro R₁ R₂ m n
    let ρ : E.Point (pullback.fst (D.smulKernelπ E (M : ℤ)) (D.smulKernelπ E (K : ℤ))
          ≫ D.smulKernelπ E (M : ℤ))
        →+ E.Point (P ≫ pullback.fst (D.smulKernelπ E (M : ℤ)) (D.smulKernelπ E (K : ℤ))
          ≫ D.smulKernelπ E (M : ℤ)) :=
      AddMonoidHom.mk' (EllipticCurve.Point.restrict E P)
        (fun R R' => EllipticCurve.Point.restrict_add E P R R')
    show ρ (m • R₁ + n • R₂) = m • ρ R₁ + n • ρ R₂
    rw [map_add, map_zsmul, map_zsmul]
  -- identify the restricted kernel points with scalings of the universal point
  have hR₁ : EllipticCurve.Point.restrict E P Q₁ = (K : ℤ) • ι₀' := by
    apply Subtype.ext
    show P ≫ Q₁.1 = ((K : ℤ) • ι₀').1
    rw [E.point_smul_eq_comp_mulBy]
    show P ≫ pullback.fst _ _ ≫ D.smulKernelι E (M : ℤ) ≫ D.ideal.subschemeι
      = D.ideal.subschemeι ≫ E.mulByHom (K : ℤ)
    rw [← Category.assoc, hPdef, RelEffCartierDiv.IsSubgroup.prodMap, pullback.lift_fst,
      ← RelEffCartierDiv.IsSubgroup.toSmulKernel_ι E hD hdeg h₁]
  have hR₂ : EllipticCurve.Point.restrict E P Q₂ = (M : ℤ) • ι₀' := by
    apply Subtype.ext
    show P ≫ Q₂.1 = ((M : ℤ) • ι₀').1
    rw [E.point_smul_eq_comp_mulBy]
    show P ≫ pullback.snd _ _ ≫ D.smulKernelι E (K : ℤ) ≫ D.ideal.subschemeι
      = D.ideal.subschemeι ≫ E.mulByHom (M : ℤ)
    rw [← Category.assoc, hPdef, RelEffCartierDiv.IsSubgroup.prodMap, pullback.lift_snd,
      ← RelEffCartierDiv.IsSubgroup.toSmulKernel_ι E hD hdeg h₂]
  -- assemble
  have hfinal : EllipticCurve.Point.restrict E P (v • Q₁ + u • Q₂) = ι₀' := by
    rw [hrestr, hR₁, hR₂, ← mul_smul, ← mul_smul, ← add_smul,
      show v * K + u * M = 1 by linarith, one_smul]
  have hval := congrArg Subtype.val hfinal
  exact hval

/-- **[F3-R2] (KM p. 27's roundtrip, kernel direction)** The product decomposition
splits the Bezout combination on each kernel factor: composing back into the `M`-kernel
recovers the first projection, at the level of the underlying `G`-valued morphisms.
(`combMap ≫ prodMap = 𝟙` then follows by `pullback.hom_ext` once both kernel legs are
matched; this lemma is the `fst`-leg computation.) -/
theorem RelEffCartierDiv.IsSubgroup.combMap_prodMap_fst_ι (M K : ℕ) [NeZero M] [NeZero K]
    (hMK : Nat.Coprime M K) [NeZero (M * K)]
    (hdeg : ∀ s : S, D.degree s = M * K)
    (h₁ : ((M : ℤ) * K) % ((M * K : ℕ) : ℤ) = 0) (h₂ : ((K : ℤ) * M) % ((M * K : ℕ) : ℤ) = 0) :
    RelEffCartierDiv.IsSubgroup.combMap E hD (M : ℤ) (K : ℤ) (Nat.gcdB M K) (Nat.gcdA M K)
        ≫ RelEffCartierDiv.IsSubgroup.toSmulKernel E hD hdeg h₁
        ≫ D.smulKernelι E (M : ℤ) ≫ D.ideal.subschemeι
      = pullback.fst (D.smulKernelπ E (M : ℤ)) (D.smulKernelπ E (K : ℤ))
          ≫ D.smulKernelι E (M : ℤ) ≫ D.ideal.subschemeι := by
  set u : ℤ := Nat.gcdA M K with hu
  set v : ℤ := Nat.gcdB M K with hv
  have huv : u * M + v * K = 1 := by
    have h := Nat.gcd_eq_gcd_ab M K
    rw [hMK] at h
    rw [hu, hv]
    push_cast at h ⊢
    linarith
  set σ := RelEffCartierDiv.IsSubgroup.combMap E hD (M : ℤ) (K : ℤ) v u with hσdef
  -- the σ-point: σ ≫ ι = (v•Q₁ + u•Q₂).1
  have hσι := RelEffCartierDiv.IsSubgroup.combMap_ι E hD (M : ℤ) (K : ℤ) v u
  -- boundary of the K-scaling composite
  rw [RelEffCartierDiv.IsSubgroup.toSmulKernel_ι E hD hdeg h₁, ← Category.assoc, hσι]
  -- goal: (v•Q₁+u•Q₂).1 ≫ [K] = fst ≫ ι' ≫ ι  (up to assoc)
  set Q₁ : E.Point (pullback.fst (D.smulKernelπ E (M : ℤ)) (D.smulKernelπ E (K : ℤ))
      ≫ D.smulKernelπ E (M : ℤ)) :=
    ⟨pullback.fst _ _ ≫ D.smulKernelι E (M : ℤ) ≫ D.ideal.subschemeι, by
      rw [Category.assoc, Category.assoc, RelEffCartierDiv.smulKernelι_subschemeι_π]⟩
    with hQ₁
  set Q₂ : E.Point (pullback.fst (D.smulKernelπ E (M : ℤ)) (D.smulKernelπ E (K : ℤ))
      ≫ D.smulKernelπ E (M : ℤ)) :=
    ⟨pullback.snd _ _ ≫ D.smulKernelι E (K : ℤ) ≫ D.ideal.subschemeι, by
      rw [Category.assoc, Category.assoc, RelEffCartierDiv.smulKernelι_subschemeι_π,
        ← pullback.condition]⟩ with hQ₂
  show ((v • Q₁ + u • Q₂ : E.Point _)).1 ≫ E.mulByHom (K : ℤ) = Q₁.1
  -- point form of the boundary
  rw [← E.point_smul_eq_comp_mulBy]
  -- kernel killed-facts
  have hkill₁ : (M : ℤ) • Q₁ = 0 := by
    apply Subtype.ext
    rw [E.point_smul_eq_comp_mulBy, E.point_zero_val]
    show (pullback.fst _ _ ≫ D.smulKernelι E (M : ℤ) ≫ D.ideal.subschemeι)
        ≫ E.mulByHom (M : ℤ) = _ ≫ E.zero
    rw [Category.assoc, Category.assoc,
      show D.smulKernelι E (M : ℤ) ≫ D.ideal.subschemeι ≫ E.mulByHom (M : ℤ)
        = D.smulKernelπ E (M : ℤ) ≫ E.zero from by
          rw [RelEffCartierDiv.smulKernelι, RelEffCartierDiv.smulKernelπ, ← Category.assoc]
          exact pullback.condition (f := D.ideal.subschemeι ≫ E.mulByHom (M : ℤ))
            (g := E.zero),
      ← Category.assoc]
  have hkill₂ : (K : ℤ) • Q₂ = 0 := by
    apply Subtype.ext
    rw [E.point_smul_eq_comp_mulBy, E.point_zero_val]
    show (pullback.snd _ _ ≫ D.smulKernelι E (K : ℤ) ≫ D.ideal.subschemeι)
        ≫ E.mulByHom (K : ℤ) = _ ≫ E.zero
    rw [Category.assoc, Category.assoc,
      show D.smulKernelι E (K : ℤ) ≫ D.ideal.subschemeι ≫ E.mulByHom (K : ℤ)
        = D.smulKernelπ E (K : ℤ) ≫ E.zero from by
          rw [RelEffCartierDiv.smulKernelι, RelEffCartierDiv.smulKernelπ, ← Category.assoc]
          exact pullback.condition (f := D.ideal.subschemeι ≫ E.mulByHom (K : ℤ))
            (g := E.zero),
      ← Category.assoc, ← pullback.condition, Category.assoc]
  -- the crt arithmetic: K•(v•Q₁ + u•Q₂) = Q₁
  have harith : (K : ℤ) • (v • Q₁ + u • Q₂) = Q₁ := by
    rw [smul_add, ← mul_smul, ← mul_smul,
      show (K : ℤ) * v = 1 - u * M by linarith,
      show (K : ℤ) * u = u * K by ring,
      sub_smul, one_smul, mul_smul, mul_smul, hkill₁, hkill₂]
    simp
  rw [harith]

/-- **[F3-R2-snd]** Mirror of `combMap_prodMap_fst_ι`: the `M`-scaling of the Bezout
combination recovers the second kernel leg. -/
theorem RelEffCartierDiv.IsSubgroup.combMap_prodMap_snd_ι (M K : ℕ) [NeZero M] [NeZero K]
    (hMK : Nat.Coprime M K) [NeZero (M * K)]
    (hdeg : ∀ s : S, D.degree s = M * K)
    (h₂ : ((K : ℤ) * M) % ((M * K : ℕ) : ℤ) = 0) :
    RelEffCartierDiv.IsSubgroup.combMap E hD (M : ℤ) (K : ℤ) (Nat.gcdB M K) (Nat.gcdA M K)
        ≫ RelEffCartierDiv.IsSubgroup.toSmulKernel E hD hdeg h₂
        ≫ D.smulKernelι E (K : ℤ) ≫ D.ideal.subschemeι
      = pullback.snd (D.smulKernelπ E (M : ℤ)) (D.smulKernelπ E (K : ℤ))
          ≫ D.smulKernelι E (K : ℤ) ≫ D.ideal.subschemeι := by
  set u : ℤ := Nat.gcdA M K with hu
  set v : ℤ := Nat.gcdB M K with hv
  have huv : u * M + v * K = 1 := by
    have h := Nat.gcd_eq_gcd_ab M K
    rw [hMK] at h
    rw [hu, hv]
    push_cast at h ⊢
    linarith
  set σ := RelEffCartierDiv.IsSubgroup.combMap E hD (M : ℤ) (K : ℤ) v u with hσdef
  have hσι := RelEffCartierDiv.IsSubgroup.combMap_ι E hD (M : ℤ) (K : ℤ) v u
  rw [RelEffCartierDiv.IsSubgroup.toSmulKernel_ι E hD hdeg h₂, ← Category.assoc, hσι]
  set Q₁ : E.Point (pullback.fst (D.smulKernelπ E (M : ℤ)) (D.smulKernelπ E (K : ℤ))
      ≫ D.smulKernelπ E (M : ℤ)) :=
    ⟨pullback.fst _ _ ≫ D.smulKernelι E (M : ℤ) ≫ D.ideal.subschemeι, by
      rw [Category.assoc, Category.assoc, RelEffCartierDiv.smulKernelι_subschemeι_π]⟩
    with hQ₁
  set Q₂ : E.Point (pullback.fst (D.smulKernelπ E (M : ℤ)) (D.smulKernelπ E (K : ℤ))
      ≫ D.smulKernelπ E (M : ℤ)) :=
    ⟨pullback.snd _ _ ≫ D.smulKernelι E (K : ℤ) ≫ D.ideal.subschemeι, by
      rw [Category.assoc, Category.assoc, RelEffCartierDiv.smulKernelι_subschemeι_π,
        ← pullback.condition]⟩ with hQ₂
  show ((v • Q₁ + u • Q₂ : E.Point _)).1 ≫ E.mulByHom (M : ℤ) = Q₂.1
  rw [← E.point_smul_eq_comp_mulBy]
  have hkill₁ : (M : ℤ) • Q₁ = 0 := by
    apply Subtype.ext
    rw [E.point_smul_eq_comp_mulBy, E.point_zero_val]
    show (pullback.fst _ _ ≫ D.smulKernelι E (M : ℤ) ≫ D.ideal.subschemeι)
        ≫ E.mulByHom (M : ℤ) = _ ≫ E.zero
    rw [Category.assoc, Category.assoc,
      show D.smulKernelι E (M : ℤ) ≫ D.ideal.subschemeι ≫ E.mulByHom (M : ℤ)
        = D.smulKernelπ E (M : ℤ) ≫ E.zero from by
          rw [RelEffCartierDiv.smulKernelι, RelEffCartierDiv.smulKernelπ, ← Category.assoc]
          exact pullback.condition (f := D.ideal.subschemeι ≫ E.mulByHom (M : ℤ))
            (g := E.zero),
      ← Category.assoc]
  have hkill₂ : (K : ℤ) • Q₂ = 0 := by
    apply Subtype.ext
    rw [E.point_smul_eq_comp_mulBy, E.point_zero_val]
    show (pullback.snd _ _ ≫ D.smulKernelι E (K : ℤ) ≫ D.ideal.subschemeι)
        ≫ E.mulByHom (K : ℤ) = _ ≫ E.zero
    rw [Category.assoc, Category.assoc,
      show D.smulKernelι E (K : ℤ) ≫ D.ideal.subschemeι ≫ E.mulByHom (K : ℤ)
        = D.smulKernelπ E (K : ℤ) ≫ E.zero from by
          rw [RelEffCartierDiv.smulKernelι, RelEffCartierDiv.smulKernelπ, ← Category.assoc]
          exact pullback.condition (f := D.ideal.subschemeι ≫ E.mulByHom (K : ℤ))
            (g := E.zero),
      ← Category.assoc, ← pullback.condition, Category.assoc]
  have harith : (M : ℤ) • (v • Q₁ + u • Q₂) = Q₂ := by
    rw [smul_add, ← mul_smul, ← mul_smul,
      show (M : ℤ) * v = v * M by ring,
      show (M : ℤ) * u = 1 - v * K by linarith,
      sub_smul, one_smul, mul_smul, mul_smul, hkill₁, hkill₂]
    simp
  rw [harith]

/-- **[F3-R2] (KM p. 27: the product decomposition is split by the combination)**
`combMap(v,u) ≫ prodMap = 𝟙` — assembled from the two leg computations by
`pullback.hom_ext` (outer product, then each kernel), with the base legs given by the
combination point's own over-`S` property. Together with [F3-R1] this makes
`G ≅ Ker[M] ×_S Ker[K]` — KM's *"canonical product decomposition"*. -/
theorem RelEffCartierDiv.IsSubgroup.combMap_prodMap (M K : ℕ) [NeZero M] [NeZero K]
    (hMK : Nat.Coprime M K) [NeZero (M * K)]
    (hdeg : ∀ s : S, D.degree s = M * K)
    (h₁ : ((M : ℤ) * K) % ((M * K : ℕ) : ℤ) = 0) (h₂ : ((K : ℤ) * M) % ((M * K : ℕ) : ℤ) = 0) :
    RelEffCartierDiv.IsSubgroup.combMap E hD (M : ℤ) (K : ℤ) (Nat.gcdB M K) (Nat.gcdA M K)
        ≫ RelEffCartierDiv.IsSubgroup.prodMap E hD hdeg h₁ h₂
      = 𝟙 _ := by
  obtain ⟨W, hW⟩ : ∃ W : E.Point (pullback.fst (D.smulKernelπ E (M : ℤ))
      (D.smulKernelπ E (K : ℤ)) ≫ D.smulKernelπ E (M : ℤ)),
      RelEffCartierDiv.IsSubgroup.combMap E hD (M : ℤ) (K : ℤ)
        (Nat.gcdB M K) (Nat.gcdA M K) ≫ D.ideal.subschemeι = W.1 :=
    ⟨_, RelEffCartierDiv.IsSubgroup.combMap_ι E hD (M : ℤ) (K : ℤ) _ _⟩
  have hσπ : RelEffCartierDiv.IsSubgroup.combMap E hD (M : ℤ) (K : ℤ)
        (Nat.gcdB M K) (Nat.gcdA M K) ≫ D.ideal.subschemeι ≫ E.π
      = pullback.fst (D.smulKernelπ E (M : ℤ)) (D.smulKernelπ E (K : ℤ))
        ≫ D.smulKernelπ E (M : ℤ) := by
    rw [← Category.assoc, hW]
    exact W.2
  apply pullback.hom_ext
  · rw [Category.assoc, RelEffCartierDiv.IsSubgroup.prodMap, pullback.lift_fst,
      Category.id_comp]
    apply pullback.hom_ext
    · have hfst := RelEffCartierDiv.IsSubgroup.combMap_prodMap_fst_ι E hD M K hMK hdeg h₁ h₂
      rw [← cancel_mono (D.ideal.subschemeι)]
      show (RelEffCartierDiv.IsSubgroup.combMap E hD (M : ℤ) (K : ℤ)
            (Nat.gcdB M K) (Nat.gcdA M K)
          ≫ RelEffCartierDiv.IsSubgroup.toSmulKernel E hD hdeg h₁)
          ≫ D.smulKernelι E (M : ℤ) ≫ D.ideal.subschemeι
        = pullback.fst (D.smulKernelπ E (M : ℤ)) (D.smulKernelπ E (K : ℤ))
          ≫ D.smulKernelι E (M : ℤ) ≫ D.ideal.subschemeι
      simpa only [Category.assoc] using hfst
    · show (RelEffCartierDiv.IsSubgroup.combMap E hD (M : ℤ) (K : ℤ)
            (Nat.gcdB M K) (Nat.gcdA M K)
          ≫ RelEffCartierDiv.IsSubgroup.toSmulKernel E hD hdeg h₁)
          ≫ D.smulKernelπ E (M : ℤ)
        = pullback.fst _ _ ≫ D.smulKernelπ E (M : ℤ)
      rw [Category.assoc, RelEffCartierDiv.IsSubgroup.toSmulKernel_π]
      exact hσπ
  · rw [Category.assoc, RelEffCartierDiv.IsSubgroup.prodMap, pullback.lift_snd,
      Category.id_comp]
    apply pullback.hom_ext
    · have hsnd := RelEffCartierDiv.IsSubgroup.combMap_prodMap_snd_ι E hD M K hMK hdeg h₂
      rw [← cancel_mono (D.ideal.subschemeι)]
      show (RelEffCartierDiv.IsSubgroup.combMap E hD (M : ℤ) (K : ℤ)
            (Nat.gcdB M K) (Nat.gcdA M K)
          ≫ RelEffCartierDiv.IsSubgroup.toSmulKernel E hD hdeg h₂)
          ≫ D.smulKernelι E (K : ℤ) ≫ D.ideal.subschemeι
        = pullback.snd (D.smulKernelπ E (M : ℤ)) (D.smulKernelπ E (K : ℤ))
          ≫ D.smulKernelι E (K : ℤ) ≫ D.ideal.subschemeι
      simpa only [Category.assoc] using hsnd
    · show (RelEffCartierDiv.IsSubgroup.combMap E hD (M : ℤ) (K : ℤ)
            (Nat.gcdB M K) (Nat.gcdA M K)
          ≫ RelEffCartierDiv.IsSubgroup.toSmulKernel E hD hdeg h₂)
          ≫ D.smulKernelπ E (K : ℤ)
        = pullback.snd _ _ ≫ D.smulKernelπ E (K : ℤ)
      rw [Category.assoc, RelEffCartierDiv.IsSubgroup.toSmulKernel_π]
      rw [hσπ]
      exact pullback.condition

include hD in
/-- **[F3-zero]** The zero section lifts to every kernel of a subgroup divisor: `0` is
in `H` and killed by everything, so `exists_smulKernel_lift` applies. Provides the
section making each kernel a retract of the product (the flat-by-retract chain). -/
theorem RelEffCartierDiv.IsSubgroup.exists_zero_smulKernel (c : ℤ) :
    ∃ z₀ : S ⟶ D.smulKernel E c, z₀ ≫ D.smulKernelπ E c = 𝟙 S := by
  obtain ⟨H, hH⟩ := hD (𝟙 S)
  obtain ⟨w, hw⟩ := (hH 0).mp H.zero_mem
  obtain ⟨z₀, _, hπ⟩ := RelEffCartierDiv.exists_smulKernel_lift E (0 : E.Point (𝟙 S))
    (smul_zero c) w hw
  exact ⟨z₀, hπ⟩

include hD in
/-- **[F3-sect]** Each kernel is a retract of the product: the section pairs the
identity with the zero-lift through the other kernel. -/
theorem RelEffCartierDiv.IsSubgroup.exists_smulKernel_section (c₁ c₂ : ℤ) :
    ∃ s : D.smulKernel E c₁ ⟶ pullback (D.smulKernelπ E c₁) (D.smulKernelπ E c₂),
      s ≫ pullback.fst (D.smulKernelπ E c₁) (D.smulKernelπ E c₂) = 𝟙 _ := by
  obtain ⟨z₀, hz₀⟩ := RelEffCartierDiv.IsSubgroup.exists_zero_smulKernel E hD c₂
  refine ⟨pullback.lift (𝟙 _) (D.smulKernelπ E c₁ ≫ z₀) ?_, pullback.lift_fst _ _ _⟩
  rw [Category.id_comp, Category.assoc, hz₀, Category.comp_id]

include hD in
/-- **[F3-retract] (KM p. 27's flatness input, scheme form)** Each kernel of a
coprime-degree subgroup divisor is a retract of the divisor subscheme over `S`:
`i := section ≫ combMap`, `r := prodMap ≫ fst`, split by [F3-R2] + [F3-sect]. The
flat/finite/lfp transport along this retract is the remaining ForMathlib gap. -/
theorem RelEffCartierDiv.IsSubgroup.exists_smulKernel_retract (M K : ℕ)
    [NeZero M] [NeZero K] (hMK : Nat.Coprime M K) [NeZero (M * K)]
    (hdeg : ∀ s : S, D.degree s = M * K)
    (h₁ : ((M : ℤ) * K) % ((M * K : ℕ) : ℤ) = 0)
    (h₂ : ((K : ℤ) * M) % ((M * K : ℕ) : ℤ) = 0) :
    ∃ (i : D.smulKernel E (M : ℤ) ⟶ D.ideal.subscheme)
      (r : D.ideal.subscheme ⟶ D.smulKernel E (M : ℤ)), i ≫ r = 𝟙 _ := by
  obtain ⟨s, hs⟩ := RelEffCartierDiv.IsSubgroup.exists_smulKernel_section E hD
    (M : ℤ) (K : ℤ)
  refine ⟨s ≫ RelEffCartierDiv.IsSubgroup.combMap E hD (M : ℤ) (K : ℤ)
      (Nat.gcdB M K) (Nat.gcdA M K),
    RelEffCartierDiv.IsSubgroup.prodMap E hD hdeg h₁ h₂
      ≫ pullback.fst (D.smulKernelπ E (M : ℤ)) (D.smulKernelπ E (K : ℤ)), ?_⟩
  rw [Category.assoc, ← Category.assoc (RelEffCartierDiv.IsSubgroup.combMap E hD _ _ _ _),
    RelEffCartierDiv.IsSubgroup.combMap_prodMap E hD M K hMK hdeg h₁ h₂,
    Category.id_comp]
  exact hs

/-- **[F3-count-equiv]** Sections of the `c`-kernel over `t` are exactly the `c`-killed
points of `E` over `t` factoring through the divisor (the functor of points of
`Ker([c] : G → E)`). The inverse extracts the factoring witness by choice; the
monomorphism `subschemeι` forces it back to the canonical one. -/
noncomputable def RelEffCartierDiv.smulKernelPointsEquiv (D : RelEffCartierDiv E.π)
    (c : ℤ) {T : Scheme.{u}} (t : T ⟶ S) :
    { h : T ⟶ D.smulKernel E c // h ≫ D.smulKernelπ E c = t }
      ≃ { Q : E.Point t // c • Q = 0 ∧
          ∃ w : T ⟶ D.ideal.subscheme, w ≫ D.ideal.subschemeι = Q.1 } where
  toFun h := ⟨⟨h.1 ≫ D.smulKernelι E c ≫ D.ideal.subschemeι, by
      rw [Category.assoc, Category.assoc, RelEffCartierDiv.smulKernelι_subschemeι_π, h.2]⟩,
    by
      apply Subtype.ext
      rw [E.point_smul_eq_comp_mulBy, E.point_zero_val]
      show (h.1 ≫ D.smulKernelι E c ≫ D.ideal.subschemeι) ≫ E.mulByHom c = t ≫ E.zero
      rw [Category.assoc, Category.assoc,
        show D.smulKernelι E c ≫ D.ideal.subschemeι ≫ E.mulByHom c
          = D.smulKernelπ E c ≫ E.zero from by
            rw [RelEffCartierDiv.smulKernelι, RelEffCartierDiv.smulKernelπ, ← Category.assoc]
            exact pullback.condition (f := D.ideal.subschemeι ≫ E.mulByHom c) (g := E.zero),
        ← Category.assoc, h.2],
    ⟨h.1 ≫ D.smulKernelι E c, by rw [Category.assoc]⟩⟩
  invFun Q := ⟨pullback.lift Q.2.2.choose t (by
      rw [← Category.assoc, Q.2.2.choose_spec]
      have hval := congrArg Subtype.val Q.2.1
      rw [E.point_smul_eq_comp_mulBy] at hval
      rw [hval]
      exact E.point_zero_val t), pullback.lift_snd _ _ _⟩
  left_inv h := by
    apply Subtype.ext
    apply pullback.hom_ext
    · show _ ≫ pullback.fst _ _ = _
      rw [pullback.lift_fst]
      rw [← cancel_mono (D.ideal.subschemeι)]
      rw [Exists.choose_spec (p := fun w : _ ⟶ D.ideal.subscheme
        => w ≫ D.ideal.subschemeι = _)]
      rfl
    · show _ ≫ pullback.snd _ _ = _
      rw [pullback.lift_snd]
      exact h.2.symm
  right_inv Q := by
    apply Subtype.ext
    apply Subtype.ext
    show (pullback.lift _ t _ ≫ D.smulKernelι E c) ≫ D.ideal.subschemeι = Q.1.1
    rw [show pullback.lift _ t _ ≫ D.smulKernelι E c = _ from pullback.lift_fst _ _ _,
      Q.2.2.choose_spec]

include hD in
/-- **[F3-kerflat] (KM p. 27: "so flat over S")** The `M`-kernel of a coprime-degree
subgroup divisor is flat over the base: it is a retract of the divisor subscheme
(v10.279's chain), and flatness descends along retracts (`Flat.of_retract_over`). -/
theorem RelEffCartierDiv.IsSubgroup.smulKernelπ_flat (M K : ℕ) [NeZero M] [NeZero K]
    (hMK : Nat.Coprime M K) [NeZero (M * K)]
    (hdeg : ∀ s : S, D.degree s = M * K)
    (h₁ : ((M : ℤ) * K) % ((M * K : ℕ) : ℤ) = 0)
    (h₂ : ((K : ℤ) * M) % ((M * K : ℕ) : ℤ) = 0) :
    Flat (D.smulKernelπ E (M : ℤ)) := by
  haveI hGflat : Flat (D.ideal.subschemeι ≫ E.π) := D.flat
  obtain ⟨s, hs⟩ := RelEffCartierDiv.IsSubgroup.exists_smulKernel_section E hD
    (M : ℤ) (K : ℤ)
  obtain ⟨W, hW⟩ : ∃ W : E.Point (pullback.fst (D.smulKernelπ E (M : ℤ))
      (D.smulKernelπ E (K : ℤ)) ≫ D.smulKernelπ E (M : ℤ)),
      RelEffCartierDiv.IsSubgroup.combMap E hD (M : ℤ) (K : ℤ)
        (Nat.gcdB M K) (Nat.gcdA M K) ≫ D.ideal.subschemeι = W.1 :=
    ⟨_, RelEffCartierDiv.IsSubgroup.combMap_ι E hD (M : ℤ) (K : ℤ) _ _⟩
  refine ModularCurves.Flat.of_retract_over
    (f := D.smulKernelπ E (M : ℤ)) (g := D.ideal.subschemeι ≫ E.π)
    (i := s ≫ RelEffCartierDiv.IsSubgroup.combMap E hD (M : ℤ) (K : ℤ)
      (Nat.gcdB M K) (Nat.gcdA M K))
    (r := RelEffCartierDiv.IsSubgroup.prodMap E hD hdeg h₁ h₂
      ≫ pullback.fst (D.smulKernelπ E (M : ℤ)) (D.smulKernelπ E (K : ℤ)))
    ?_ ?_ ?_
  · -- i ≫ r = 𝟙
    rw [Category.assoc, ← Category.assoc
      (RelEffCartierDiv.IsSubgroup.combMap E hD (M : ℤ) (K : ℤ) _ _),
      RelEffCartierDiv.IsSubgroup.combMap_prodMap E hD M K hMK hdeg h₁ h₂,
      Category.id_comp]
    exact hs
  · -- i ≫ (ι ≫ π) = smulKernelπ
    rw [Category.assoc, ← Category.assoc
      (RelEffCartierDiv.IsSubgroup.combMap E hD (M : ℤ) (K : ℤ) _ _), hW]
    have hbase := W.2
    rw [show (W : _ ⟶ E.E) ≫ E.π
        = pullback.fst (D.smulKernelπ E (M : ℤ)) (D.smulKernelπ E (K : ℤ))
          ≫ D.smulKernelπ E (M : ℤ) from hbase]
    rw [← Category.assoc, hs, Category.id_comp]
  · -- r ≫ smulKernelπ = ι ≫ π
    rw [RelEffCartierDiv.IsSubgroup.prodMap, pullback.lift_fst]
    exact RelEffCartierDiv.IsSubgroup.toSmulKernel_π E hD hdeg h₁

/-- **[F3-kerfin]** The `c`-kernel is finite over `S`: it is the base change of the
finite `ι ≫ [c]` (closed immersion into the finite `[c]`) along the zero section. -/
theorem RelEffCartierDiv.smulKernelπ_isFinite (D : RelEffCartierDiv E.π) (c : ℤ)
    [IsFinite (E.mulByHom c)] : IsFinite (D.smulKernelπ E c) := by
  haveI hfin : IsFinite (D.ideal.subschemeι ≫ E.mulByHom c) := inferInstance
  rw [RelEffCartierDiv.smulKernelπ]
  exact MorphismProperty.pullback_snd (P := @IsFinite) _ _ hfin

/-- **[F3-etale] (KM p. 28: "G[N₁] is finite etale over S, of rank N₁" — étale part)**
When `M` is invertible on `S`, the `M`-kernel of a divisor is étale over `S` given its
flatness: it sits as a closed subscheme of the étale `E[M]` (pasting of kernel
pullbacks), so it is formally unramified, and flat + finite presentation assemble
étaleness. -/
theorem RelEffCartierDiv.smulKernelπ_etale (D : RelEffCartierDiv E.π) (M : ℕ) [NeZero M]
    (hinv : NIsInvertible S M) (hflat : Flat (D.smulKernelπ E (M : ℤ))) :
    Etale (D.smulKernelπ E (M : ℤ)) := by
  -- the two kernel pullback squares
  have t : IsPullback (E.torsionπ M) (E.torsionι M) E.zero (E.mulByHom M) :=
    (IsPullback.of_hasPullback (E.mulByHom (M : ℕ)) E.zero).flip
  have sq : IsPullback (D.smulKernelπ E (M : ℤ)) (D.smulKernelι E (M : ℤ)) E.zero
      (D.ideal.subschemeι ≫ E.mulByHom (M : ℤ)) :=
    (IsPullback.of_hasPullback (D.ideal.subschemeι ≫ E.mulByHom (M : ℤ)) E.zero).flip
  -- paste: the left square exhibits the kernel as a closed subscheme of E[M]
  have hsq : IsPullback
      (t.lift (D.smulKernelπ E (M : ℤ)) (D.smulKernelι E (M : ℤ) ≫ D.ideal.subschemeι)
        (by rw [sq.w, Category.assoc]))
      (D.smulKernelι E (M : ℤ)) (E.torsionι M) D.ideal.subschemeι :=
    IsPullback.of_right' sq t
  set j := t.lift (D.smulKernelπ E (M : ℤ))
    (D.smulKernelι E (M : ℤ) ≫ D.ideal.subschemeι) (by rw [sq.w, Category.assoc]) with hj
  haveI hjci : IsClosedImmersion j :=
    MorphismProperty.of_isPullback (P := @IsClosedImmersion) hsq.flip inferInstance
  -- the composite identity
  have hcomp : j ≫ E.torsionπ M = D.smulKernelπ E (M : ℤ) := t.lift_fst _ _ _
  -- assemble étaleness
  haveI hτ : Etale (E.torsionπ M) := E.torsionπ_etale M hinv
  rw [← hcomp]
  haveI : LocallyOfFinitePresentation (j ≫ E.torsionπ M) := by
    rw [hcomp]
    haveI : LocallyOfFinitePresentation
        (D.ideal.subschemeι ≫ E.mulByHom (M : ℤ)) := by
      haveI h1 : LocallyOfFinitePresentation (E.mulByHom (M : ℤ)) := by
        have := E.mulByHom_locallyOfFinitePresentation M
        exact this
      haveI h2 : LocallyOfFinitePresentation (D.ideal.subschemeι ≫ E.π) := D.lfp
      haveI hι : LocallyOfFinitePresentation (D.ideal.subschemeι) :=
        LocallyOfFinitePresentation.of_comp_of_locallyOfFiniteType h2 inferInstance
      exact MorphismProperty.comp_mem _ _ _ hι h1
    rw [RelEffCartierDiv.smulKernelπ]
    exact MorphismProperty.pullback_snd (P := @LocallyOfFinitePresentation) _ _ this
  haveI : FormallyUnramified (j ≫ E.torsionπ M) := by
    haveI h1 : FormallyUnramified j := inferInstance
    haveI h2 : FormallyUnramified (E.torsionπ M) := inferInstance
    exact MorphismProperty.comp_mem _ j (E.torsionπ M) h1 h2
  haveI : Flat (j ≫ E.torsionπ M) := by rw [hcomp]; exact hflat
  exact Etale.of_formallyUnramified_of_flat (j ≫ E.torsionπ M)

include hD in
/-- **[F3-R1-id]** The retraction in identity form: `prodMap ≫ combMap = 𝟙 G`
(cancel the mono `ι` against [F3-R1]). -/
theorem RelEffCartierDiv.IsSubgroup.prodMap_combMap (M K : ℕ) [NeZero M] [NeZero K]
    (hMK : Nat.Coprime M K) [NeZero (M * K)]
    (hdeg : ∀ s : S, D.degree s = M * K)
    (h₁ : ((M : ℤ) * K) % ((M * K : ℕ) : ℤ) = 0)
    (h₂ : ((K : ℤ) * M) % ((M * K : ℕ) : ℤ) = 0) :
    RelEffCartierDiv.IsSubgroup.prodMap E hD hdeg h₁ h₂
        ≫ RelEffCartierDiv.IsSubgroup.combMap E hD (M : ℤ) (K : ℤ)
            (Nat.gcdB M K) (Nat.gcdA M K)
      = 𝟙 _ := by
  rw [← cancel_mono D.ideal.subschemeι, Category.assoc,
    RelEffCartierDiv.IsSubgroup.prodMap_combMap_ι E hD M K hMK hdeg h₁ h₂,
    Category.id_comp]

/-- **[F3-prodIso]** KM's canonical product decomposition as an isomorphism:
`G ≅ Ker[M] ×_S Ker[K]`. -/
noncomputable def RelEffCartierDiv.IsSubgroup.prodIso (M K : ℕ) [NeZero M] [NeZero K]
    (hMK : Nat.Coprime M K) [NeZero (M * K)]
    (hdeg : ∀ s : S, D.degree s = M * K)
    (h₁ : ((M : ℤ) * K) % ((M * K : ℕ) : ℤ) = 0)
    (h₂ : ((K : ℤ) * M) % ((M * K : ℕ) : ℤ) = 0) :
    D.ideal.subscheme ≅ pullback (D.smulKernelπ E (M : ℤ)) (D.smulKernelπ E (K : ℤ)) where
  hom := RelEffCartierDiv.IsSubgroup.prodMap E hD hdeg h₁ h₂
  inv := RelEffCartierDiv.IsSubgroup.combMap E hD (M : ℤ) (K : ℤ)
    (Nat.gcdB M K) (Nat.gcdA M K)
  hom_inv_id := RelEffCartierDiv.IsSubgroup.prodMap_combMap E hD M K hMK hdeg h₁ h₂
  inv_hom_id := RelEffCartierDiv.IsSubgroup.combMap_prodMap E hD M K hMK hdeg h₁ h₂

include hD in
/-- **[F3-degtrans]** The divisor degree transports to the product's structure
morphism through the decomposition. -/
theorem RelEffCartierDiv.IsSubgroup.finrank_prod_struct (M K : ℕ) [NeZero M] [NeZero K]
    (hMK : Nat.Coprime M K) [NeZero (M * K)]
    [IsFinite (E.mulByHom (M : ℤ))] [IsFinite (E.mulByHom (K : ℤ))]
    (hdeg : ∀ s : S, D.degree s = M * K)
    (h₁ : ((M : ℤ) * K) % ((M * K : ℕ) : ℤ) = 0)
    (h₂ : ((K : ℤ) * M) % ((M * K : ℕ) : ℤ) = 0) (s : S) :
    (pullback.fst (D.smulKernelπ E (M : ℤ)) (D.smulKernelπ E (K : ℤ))
        ≫ D.smulKernelπ E (M : ℤ)).finrank s = M * K := by
  haveI : IsIso (RelEffCartierDiv.IsSubgroup.prodMap E hD hdeg h₁ h₂) :=
    (RelEffCartierDiv.IsSubgroup.prodIso E hD M K hMK hdeg h₁ h₂).isIso_hom
  -- finite flat structure of the product's structure morphism
  haveI hMflat : Flat (D.smulKernelπ E (M : ℤ)) :=
    RelEffCartierDiv.IsSubgroup.smulKernelπ_flat E hD M K hMK hdeg h₁ h₂
  haveI hKflat : Flat (D.smulKernelπ E (K : ℤ)) :=
    RelEffCartierDiv.IsSubgroup.smulKernelπ_flat E hD K M hMK.symm
      (fun s => by rw [hdeg s, Nat.mul_comm])
      (by rwa [Nat.mul_comm M K] at h₂) (by rwa [Nat.mul_comm M K] at h₁)
  haveI hMfin : IsFinite (D.smulKernelπ E (M : ℤ)) :=
    RelEffCartierDiv.smulKernelπ_isFinite E D (M : ℤ)
  haveI hKfin : IsFinite (D.smulKernelπ E (K : ℤ)) :=
    RelEffCartierDiv.smulKernelπ_isFinite E D (K : ℤ)
  haveI hfstflat : Flat (pullback.fst (D.smulKernelπ E (M : ℤ))
      (D.smulKernelπ E (K : ℤ))) :=
    MorphismProperty.pullback_fst (P := @Flat) _ _ hKflat
  haveI hfstfin : IsFinite (pullback.fst (D.smulKernelπ E (M : ℤ))
      (D.smulKernelπ E (K : ℤ))) :=
    MorphismProperty.pullback_fst (P := @IsFinite) _ _ hKfin
  haveI hPflat : Flat (pullback.fst (D.smulKernelπ E (M : ℤ))
      (D.smulKernelπ E (K : ℤ)) ≫ D.smulKernelπ E (M : ℤ)) :=
    MorphismProperty.comp_mem _ _ _ hfstflat hMflat
  haveI hPfin : IsFinite (pullback.fst (D.smulKernelπ E (M : ℤ))
      (D.smulKernelπ E (K : ℤ)) ≫ D.smulKernelπ E (M : ℤ)) :=
    MorphismProperty.comp_mem _ _ _ hfstfin hMfin
  have htrans := Scheme.Hom.finrank_comp_left_of_isIso
    (RelEffCartierDiv.IsSubgroup.prodMap E hD hdeg h₁ h₂)
    (pullback.fst (D.smulKernelπ E (M : ℤ)) (D.smulKernelπ E (K : ℤ))
      ≫ D.smulKernelπ E (M : ℤ))
  have hstruct : RelEffCartierDiv.IsSubgroup.prodMap E hD hdeg h₁ h₂
      ≫ pullback.fst (D.smulKernelπ E (M : ℤ)) (D.smulKernelπ E (K : ℤ))
        ≫ D.smulKernelπ E (M : ℤ)
      = D.ideal.subschemeι ≫ E.π := by
    rw [← Category.assoc, RelEffCartierDiv.IsSubgroup.prodMap, pullback.lift_fst,
      RelEffCartierDiv.IsSubgroup.toSmulKernel_π]
  calc (pullback.fst (D.smulKernelπ E (M : ℤ)) (D.smulKernelπ E (K : ℤ))
        ≫ D.smulKernelπ E (M : ℤ)).finrank s
      = (RelEffCartierDiv.IsSubgroup.prodMap E hD hdeg h₁ h₂
          ≫ pullback.fst (D.smulKernelπ E (M : ℤ)) (D.smulKernelπ E (K : ℤ))
          ≫ D.smulKernelπ E (M : ℤ)).finrank s := by rw [htrans]
    _ = (D.ideal.subschemeι ≫ E.π).finrank s := by rw [hstruct]
    _ = M * K := hdeg s

include hD in
/-- **[F3-degmul] (KM p. 28: "rank(G[N₁])·rank(G[N₂]) = rank(G) = N₁N₂")** The degree
of the divisor multiplies over the kernel product: `deg Z_M · deg Z_K = M·K` at every
base point — the product iso transports the divisor degree ([F3-degtrans]) and the
fibre-product rank formula splits it (`finrank_pullback_comp_fst`). -/
theorem RelEffCartierDiv.IsSubgroup.degree_eq_smulKernel_mul (M K : ℕ)
    [NeZero M] [NeZero K] (hMK : Nat.Coprime M K) [NeZero (M * K)]
    [IsFinite (E.mulByHom (M : ℤ))] [IsFinite (E.mulByHom (K : ℤ))]
    (hdeg : ∀ s : S, D.degree s = M * K)
    (h₁ : ((M : ℤ) * K) % ((M * K : ℕ) : ℤ) = 0)
    (h₂ : ((K : ℤ) * M) % ((M * K : ℕ) : ℤ) = 0) (s : S) :
    (D.smulKernelπ E (M : ℤ)).finrank s * (D.smulKernelπ E (K : ℤ)).finrank s
      = M * K := by
  haveI hMflat : Flat (D.smulKernelπ E (M : ℤ)) :=
    RelEffCartierDiv.IsSubgroup.smulKernelπ_flat E hD M K hMK hdeg h₁ h₂
  haveI hKflat : Flat (D.smulKernelπ E (K : ℤ)) :=
    RelEffCartierDiv.IsSubgroup.smulKernelπ_flat E hD K M hMK.symm
      (fun s => by rw [hdeg s, Nat.mul_comm])
      (by rwa [Nat.mul_comm M K] at h₂) (by rwa [Nat.mul_comm M K] at h₁)
  haveI hMfin : IsFinite (D.smulKernelπ E (M : ℤ)) :=
    RelEffCartierDiv.smulKernelπ_isFinite E D (M : ℤ)
  haveI hKfin : IsFinite (D.smulKernelπ E (K : ℤ)) :=
    RelEffCartierDiv.smulKernelπ_isFinite E D (K : ℤ)
  rw [← ModularCurves.finrank_pullback_comp_fst (D.smulKernelπ E (M : ℤ))
    (D.smulKernelπ E (K : ℤ)) s]
  exact RelEffCartierDiv.IsSubgroup.finrank_prod_struct E hD M K hMK hdeg h₁ h₂ s

/-- **[F3-mp] (contract — KM 1.7.2 forward, first conjunct)** If `P` has exact order
`M·K` with `M, K` coprime, then `K•P` has exact order `M`. Route (v10.282 map):
étale + count + Cauchy + degmul + distinctness on `S[1/M]`, 1.5.3 (3)⟹(1), glue by
`isSubgroup_of_openCover` over the coprime cover. -/
theorem Section.HasExactOrder.smul_hasExactOrder {P : E.Section} (M K : ℕ)
    [NeZero M] [NeZero K] (hMK : Nat.Coprime M K) [NeZero (M * K)]
    (h : P.HasExactOrder E (M * K)) :
    ((K : ℤ) • P).HasExactOrder E M := by sorry

end ProductDecomposition

/-- **[F3-count] (KM p. 28: "G(k) contains precisely N₁ distinct points killed by N₁",
the counting half)** Over a separably closed field, the `c`-killed points of the divisor
number exactly the kernel's degree: the kernel's functor of points
(`smulKernelPointsEquiv`) + the étale section count. -/
theorem RelEffCartierDiv.card_killed_points {k : Type u} [Field k] [IsSepClosed k]
    {E : EllipticCurve (Spec (CommRingCat.of k))}
    (D : RelEffCartierDiv E.π) (c : ℤ)
    [IsFinite (D.smulKernelπ E c)] [Etale (D.smulKernelπ E c)]
    (x₀ : ↑(Spec (CommRingCat.of k))) :
    Nat.card { Q : E.Point (𝟙 (Spec (CommRingCat.of k))) // c • Q = 0 ∧
        ∃ w : Spec (CommRingCat.of k) ⟶ D.ideal.subscheme,
          w ≫ D.ideal.subschemeι = Q.1 }
      = (D.smulKernelπ E c).finrank x₀ := by
  rw [← ModularCurves.natCard_sections_eq_finrank (D.smulKernelπ E c) x₀]
  exact Nat.card_congr (RelEffCartierDiv.smulKernelPointsEquiv E D c
    (𝟙 (Spec (CommRingCat.of k)))).symm

/-- **[F3-squeeze] (KM p. 28: "the product formula for ranks forces rank(G[N₁]) = N₁")**
Over a separably closed field with `M` and `K` invertible, the `M`-kernel of a
coprime-degree-`M·K` subgroup divisor has degree exactly `M`: the killed-point count
is an `M`-killed abelian group (Cauchy bounds its prime support), the degrees multiply
to `M·K`, and coprimality forces the split. -/
theorem RelEffCartierDiv.IsSubgroup.smulKernelπ_finrank_eq {k : Type u} [Field k]
    [IsSepClosed k] {E : EllipticCurve (Spec (CommRingCat.of k))}
    {D : RelEffCartierDiv E.π} (hD : D.IsSubgroup E) (M K : ℕ)
    [NeZero M] [NeZero K] (hMK : Nat.Coprime M K) [NeZero (M * K)]
    [IsFinite (E.mulByHom (M : ℤ))] [IsFinite (E.mulByHom (K : ℤ))]
    (hinvM : NIsInvertible (Spec (CommRingCat.of k)) M)
    (hinvK : NIsInvertible (Spec (CommRingCat.of k)) K)
    (hdeg : ∀ s, D.degree s = M * K)
    (h₁ : ((M : ℤ) * K) % ((M * K : ℕ) : ℤ) = 0)
    (h₂ : ((K : ℤ) * M) % ((M * K : ℕ) : ℤ) = 0)
    (x₀ : ↑(Spec (CommRingCat.of k))) :
    (D.smulKernelπ E (M : ℤ)).finrank x₀ = M := by
  -- the finite flat étale instances
  haveI hMflat : Flat (D.smulKernelπ E (M : ℤ)) :=
    RelEffCartierDiv.IsSubgroup.smulKernelπ_flat E hD M K hMK hdeg h₁ h₂
  haveI hKflat : Flat (D.smulKernelπ E (K : ℤ)) :=
    RelEffCartierDiv.IsSubgroup.smulKernelπ_flat E hD K M hMK.symm
      (fun s => by rw [hdeg s, Nat.mul_comm])
      (by rwa [Nat.mul_comm M K] at h₂) (by rwa [Nat.mul_comm M K] at h₁)
  haveI hMfin : IsFinite (D.smulKernelπ E (M : ℤ)) :=
    RelEffCartierDiv.smulKernelπ_isFinite E D (M : ℤ)
  haveI hKfin : IsFinite (D.smulKernelπ E (K : ℤ)) :=
    RelEffCartierDiv.smulKernelπ_isFinite E D (K : ℤ)
  haveI hMet : Etale (D.smulKernelπ E (M : ℤ)) :=
    RelEffCartierDiv.smulKernelπ_etale E D M hinvM hMflat
  haveI hKet : Etale (D.smulKernelπ E (K : ℤ)) :=
    RelEffCartierDiv.smulKernelπ_etale E D K hinvK hKflat
  -- notation
  set nM := (D.smulKernelπ E (M : ℤ)).finrank x₀ with hnM
  set nK := (D.smulKernelπ E (K : ℤ)).finrank x₀ with hnK
  have hprod : nM * nK = M * K :=
    RelEffCartierDiv.IsSubgroup.degree_eq_smulKernel_mul E hD M K hMK hdeg h₁ h₂ x₀
  have hMpos : 0 < nM := by
    rcases Nat.eq_zero_or_pos nM with h0 | h
    · exfalso
      rw [h0, Nat.zero_mul] at hprod
      exact (Nat.mul_ne_zero (NeZero.ne M) (NeZero.ne K)) hprod.symm
    · exact h
  have hKpos : 0 < nK := by
    rcases Nat.eq_zero_or_pos nK with h0 | h
    · exfalso
      rw [h0, Nat.mul_zero] at hprod
      exact (Nat.mul_ne_zero (NeZero.ne M) (NeZero.ne K)) hprod.symm
    · exact h
  -- the killed points as a group; Cauchy bounds the prime support of nM
  obtain ⟨H, hH⟩ := hD (𝟙 (Spec (CommRingCat.of k)))
  have hcardM : Nat.card { Q : E.Point (𝟙 (Spec (CommRingCat.of k))) //
      (M : ℤ) • Q = 0 ∧ ∃ w : Spec (CommRingCat.of k) ⟶ D.ideal.subscheme,
        w ≫ D.ideal.subschemeι = Q.1 } = nM :=
    RelEffCartierDiv.card_killed_points D (M : ℤ) x₀
  have hdvdM : ∀ p : ℕ, p.Prime → p ∣ nM → p ∣ M := by
    intro p hp hpn
    let A : AddSubgroup (E.Point (𝟙 (Spec (CommRingCat.of k)))) :=
      { carrier := { Q | (M : ℤ) • Q = 0 ∧ ∃ w : Spec (CommRingCat.of k)
            ⟶ D.ideal.subscheme, w ≫ D.ideal.subschemeι = Q.1 }
        zero_mem' := ⟨smul_zero _, (hH 0).mp H.zero_mem⟩
        add_mem' := fun {P Q} hP hQ => ⟨by rw [smul_add, hP.1, hQ.1, add_zero],
          (hH _).mp (H.add_mem ((hH P).mpr hP.2) ((hH Q).mpr hQ.2))⟩
        neg_mem' := fun {P} hP => ⟨by rw [smul_neg, hP.1, neg_zero],
          (hH _).mp (H.neg_mem ((hH P).mpr hP.2))⟩ }
    have hcardA : Nat.card A = nM := hcardM
    haveI hFin : Finite A := by
      have hpos : 0 < Nat.card A := by rw [hcardA]; exact hMpos
      exact (Nat.card_pos_iff.mp hpos).2
    refine prime_dvd_of_killed M (fun g => ?_) hp (by rw [hcardA]; exact hpn)
    have hg : (M : ℤ) • (g : E.Point (𝟙 (Spec (CommRingCat.of k)))) = 0 := g.2.1
    exact Subtype.ext hg
  have hcardK : Nat.card { Q : E.Point (𝟙 (Spec (CommRingCat.of k))) //
      (K : ℤ) • Q = 0 ∧ ∃ w : Spec (CommRingCat.of k) ⟶ D.ideal.subscheme,
        w ≫ D.ideal.subschemeι = Q.1 } = nK :=
    RelEffCartierDiv.card_killed_points D (K : ℤ) x₀
  have hdvdK : ∀ p : ℕ, p.Prime → p ∣ nK → p ∣ K := by
    intro p hp hpn
    let A : AddSubgroup (E.Point (𝟙 (Spec (CommRingCat.of k)))) :=
      { carrier := { Q | (K : ℤ) • Q = 0 ∧ ∃ w : Spec (CommRingCat.of k)
            ⟶ D.ideal.subscheme, w ≫ D.ideal.subschemeι = Q.1 }
        zero_mem' := ⟨smul_zero _, (hH 0).mp H.zero_mem⟩
        add_mem' := fun {P Q} hP hQ => ⟨by rw [smul_add, hP.1, hQ.1, add_zero],
          (hH _).mp (H.add_mem ((hH P).mpr hP.2) ((hH Q).mpr hQ.2))⟩
        neg_mem' := fun {P} hP => ⟨by rw [smul_neg, hP.1, neg_zero],
          (hH _).mp (H.neg_mem ((hH P).mpr hP.2))⟩ }
    have hcardA : Nat.card A = nK := hcardK
    haveI hFin : Finite A := by
      have hpos : 0 < Nat.card A := by rw [hcardA]; exact hKpos
      exact (Nat.card_pos_iff.mp hpos).2
    refine prime_dvd_of_killed K (fun g => ?_) hp (by rw [hcardA]; exact hpn)
    have hg : (K : ℤ) • (g : E.Point (𝟙 (Spec (CommRingCat.of k)))) = 0 := g.2.1
    exact Subtype.ext hg
  -- coprimality forces the split
  have hcopMK : Nat.Coprime nM K := by
    by_contra hcon
    obtain ⟨p, hp, hpM, hpK⟩ := Nat.Prime.not_coprime_iff_dvd.mp hcon
    exact Nat.Prime.one_lt hp |>.ne'
      (Nat.eq_one_of_dvd_coprimes hMK (hdvdM p hp hpM) hpK)
  have hdvdMM : nM ∣ M :=
    hcopMK.dvd_of_dvd_mul_right ⟨nK, hprod.symm⟩
  have hcopKM : Nat.Coprime nK M := by
    by_contra hcon
    obtain ⟨p, hp, hpK, hpM⟩ := Nat.Prime.not_coprime_iff_dvd.mp hcon
    exact Nat.Prime.one_lt hp |>.ne'
      (Nat.eq_one_of_dvd_coprimes hMK.symm (hdvdK p hp hpK) hpM)
  have hdvdKK : nK ∣ K :=
    hcopKM.dvd_of_dvd_mul_right ⟨nM, by
      rw [Nat.mul_comm K M, Nat.mul_comm nK nM]; exact hprod.symm⟩
  -- the divisor product forces equality
  obtain ⟨a, ha⟩ := hdvdMM
  obtain ⟨b, hb⟩ := hdvdKK
  have hab : a * b = 1 := by
    have h1 : (nM * nK) * (a * b) = (nM * nK) * 1 := by
      rw [Nat.mul_one]
      calc nM * nK * (a * b) = (nM * a) * (nK * b) := by ring
        _ = M * K := by rw [← ha, ← hb]
        _ = nM * nK := hprod.symm
    exact Nat.eq_of_mul_eq_mul_left (Nat.mul_pos hMpos hKpos) h1
  have ha1 : a = 1 := Nat.eq_one_of_mul_eq_one_left (m := b) (by rwa [Nat.mul_comm] at hab)
  rw [ha, ha1, Nat.mul_one]

/-- **Register box `BB-DEGA` (KM p. 28's rank citation, Deligne–Gabriel [DG] IV 5.3-9 /
[Oort–Tate])**: a finite locally free (commutative group) scheme KILLED by `c` has rank
supported on the primes of `c`. Instantiated for the divisor kernel `Z_c`: every point
of `Z_c` is `c`-killed (`smulKernel_point`), so its fibre rank shares no prime outside
`c`. This is the counterpart of `BB-DELIGNE` (rank kills) that KM's 1.7.1 rank-forcing
uses on the NON-étale factor — over the locus `S[1/M]` only the `M`-kernel is étale,
and the `K`-side support bound is genuinely this classical input. -/
theorem RelEffCartierDiv.IsSubgroup.prime_dvd_smulKernel_finrank {k : Type u} [Field k]
    [IsSepClosed k] {E : EllipticCurve (Spec (CommRingCat.of k))}
    {D : RelEffCartierDiv E.π} (hD : D.IsSubgroup E) (c : ℕ) [NeZero c]
    (x₀ : ↑(Spec (CommRingCat.of k)))
    (p : ℕ) (hp : p.Prime) (hdvd : p ∣ (D.smulKernelπ E (c : ℤ)).finrank x₀) :
    p ∣ c := by sorry

/-- **[F3-squeeze-locus] (KM p. 28's rank forcing, `M`-invertible-only form)** Over a
separably closed field where only `M` is invertible (the geometric points of `S[1/M]`
— the residue characteristic may divide `K`): the `M`-kernel of a coprime-degree-`M·K`
subgroup divisor still has degree exactly `M`. The étale count + Cauchy runs on the
`M`-side as in `smulKernelπ_finrank_eq`; the `K`-side prime support comes from the
`BB-DEGA` register box instead of an étale count. -/
theorem RelEffCartierDiv.IsSubgroup.smulKernelπ_finrank_eq_of_M_invertible {k : Type u}
    [Field k] [IsSepClosed k] {E : EllipticCurve (Spec (CommRingCat.of k))}
    {D : RelEffCartierDiv E.π} (hD : D.IsSubgroup E) (M K : ℕ)
    [NeZero M] [NeZero K] (hMK : Nat.Coprime M K) [NeZero (M * K)]
    [IsFinite (E.mulByHom (M : ℤ))] [IsFinite (E.mulByHom (K : ℤ))]
    (hinvM : NIsInvertible (Spec (CommRingCat.of k)) M)
    (hdeg : ∀ s, D.degree s = M * K)
    (h₁ : ((M : ℤ) * K) % ((M * K : ℕ) : ℤ) = 0)
    (h₂ : ((K : ℤ) * M) % ((M * K : ℕ) : ℤ) = 0)
    (x₀ : ↑(Spec (CommRingCat.of k))) :
    (D.smulKernelπ E (M : ℤ)).finrank x₀ = M := by
  haveI hMflat : Flat (D.smulKernelπ E (M : ℤ)) :=
    RelEffCartierDiv.IsSubgroup.smulKernelπ_flat E hD M K hMK hdeg h₁ h₂
  haveI hKflat : Flat (D.smulKernelπ E (K : ℤ)) :=
    RelEffCartierDiv.IsSubgroup.smulKernelπ_flat E hD K M hMK.symm
      (fun s => by rw [hdeg s, Nat.mul_comm])
      (by rwa [Nat.mul_comm M K] at h₂) (by rwa [Nat.mul_comm M K] at h₁)
  haveI hMfin : IsFinite (D.smulKernelπ E (M : ℤ)) :=
    RelEffCartierDiv.smulKernelπ_isFinite E D (M : ℤ)
  haveI hKfin : IsFinite (D.smulKernelπ E (K : ℤ)) :=
    RelEffCartierDiv.smulKernelπ_isFinite E D (K : ℤ)
  haveI hMet : Etale (D.smulKernelπ E (M : ℤ)) :=
    RelEffCartierDiv.smulKernelπ_etale E D M hinvM hMflat
  set nM := (D.smulKernelπ E (M : ℤ)).finrank x₀ with hnM
  set nK := (D.smulKernelπ E (K : ℤ)).finrank x₀ with hnK
  have hprod : nM * nK = M * K :=
    RelEffCartierDiv.IsSubgroup.degree_eq_smulKernel_mul E hD M K hMK hdeg h₁ h₂ x₀
  have hMpos : 0 < nM := by
    rcases Nat.eq_zero_or_pos nM with h0 | h
    · exfalso
      rw [h0, Nat.zero_mul] at hprod
      exact (Nat.mul_ne_zero (NeZero.ne M) (NeZero.ne K)) hprod.symm
    · exact h
  -- the M-killed points as a group; Cauchy bounds the prime support of nM
  obtain ⟨H, hH⟩ := hD (𝟙 (Spec (CommRingCat.of k)))
  have hcardM : Nat.card { Q : E.Point (𝟙 (Spec (CommRingCat.of k))) //
      (M : ℤ) • Q = 0 ∧ ∃ w : Spec (CommRingCat.of k) ⟶ D.ideal.subscheme,
        w ≫ D.ideal.subschemeι = Q.1 } = nM :=
    RelEffCartierDiv.card_killed_points D (M : ℤ) x₀
  have hdvdM : ∀ p : ℕ, p.Prime → p ∣ nM → p ∣ M := by
    intro p hp hpn
    let A : AddSubgroup (E.Point (𝟙 (Spec (CommRingCat.of k)))) :=
      { carrier := { Q | (M : ℤ) • Q = 0 ∧ ∃ w : Spec (CommRingCat.of k)
            ⟶ D.ideal.subscheme, w ≫ D.ideal.subschemeι = Q.1 }
        zero_mem' := ⟨smul_zero _, (hH 0).mp H.zero_mem⟩
        add_mem' := fun {P Q} hP hQ => ⟨by rw [smul_add, hP.1, hQ.1, add_zero],
          (hH _).mp (H.add_mem ((hH P).mpr hP.2) ((hH Q).mpr hQ.2))⟩
        neg_mem' := fun {P} hP => ⟨by rw [smul_neg, hP.1, neg_zero],
          (hH _).mp (H.neg_mem ((hH P).mpr hP.2))⟩ }
    have hcardA : Nat.card A = nM := hcardM
    haveI hFin : Finite A := by
      have hpos : 0 < Nat.card A := by rw [hcardA]; exact hMpos
      exact (Nat.card_pos_iff.mp hpos).2
    refine prime_dvd_of_killed M (fun g => ?_) hp (by rw [hcardA]; exact hpn)
    have hg : (M : ℤ) • (g : E.Point (𝟙 (Spec (CommRingCat.of k)))) = 0 := g.2.1
    exact Subtype.ext hg
  -- the K-side support bound: the BB-DEGA register box (no étale count available)
  have hdvdK : ∀ p : ℕ, p.Prime → p ∣ nK → p ∣ K := fun p hp hpn =>
    RelEffCartierDiv.IsSubgroup.prime_dvd_smulKernel_finrank hD K x₀ p hp hpn
  -- coprimality forces the split (verbatim the both-étale squeeze endgame)
  have hcopMK : Nat.Coprime nM K := by
    by_contra hcon
    obtain ⟨p, hp, hpM, hpK⟩ := Nat.Prime.not_coprime_iff_dvd.mp hcon
    exact Nat.Prime.one_lt hp |>.ne'
      (Nat.eq_one_of_dvd_coprimes hMK (hdvdM p hp hpM) hpK)
  have hdvdMM : nM ∣ M :=
    hcopMK.dvd_of_dvd_mul_right ⟨nK, hprod.symm⟩
  have hcopKM : Nat.Coprime nK M := by
    by_contra hcon
    obtain ⟨p, hp, hpK, hpM⟩ := Nat.Prime.not_coprime_iff_dvd.mp hcon
    exact Nat.Prime.one_lt hp |>.ne'
      (Nat.eq_one_of_dvd_coprimes hMK.symm (hdvdK p hp hpK) hpM)
  have hdvdKK : nK ∣ K :=
    hcopKM.dvd_of_dvd_mul_right ⟨nM, by
      rw [Nat.mul_comm K M, Nat.mul_comm nK nM]; exact hprod.symm⟩
  obtain ⟨a, ha⟩ := hdvdMM
  obtain ⟨b, hb⟩ := hdvdKK
  have hKpos : 0 < nK := by
    rcases Nat.eq_zero_or_pos nK with h0 | h
    · exfalso
      rw [h0, Nat.mul_zero] at hprod
      exact (Nat.mul_ne_zero (NeZero.ne M) (NeZero.ne K)) hprod.symm
    · exact h
  have hab : a * b = 1 := by
    have h1 : (nM * nK) * (a * b) = (nM * nK) * 1 := by
      rw [Nat.mul_one]
      calc nM * nK * (a * b) = (nM * a) * (nK * b) := by ring
        _ = M * K := by rw [← ha, ← hb]
        _ = nM * nK := hprod.symm
    exact Nat.eq_of_mul_eq_mul_left (Nat.mul_pos hMpos hKpos) h1
  have ha1 : a = 1 := Nat.eq_one_of_mul_eq_one_left (m := b) (by rwa [Nat.mul_comm] at hab)
  rw [ha, ha1, Nat.mul_one]

/-- **[F3-distinct-arith] (the cyclic arithmetic of KM p. 29's counting)** In any
additive group: if `M ∣ ord x`, `ord x ∣ M·K`, and `M, K` are coprime, then `K·x` has
order exactly `M`. (`ord x = M·e` with `e ∣ K`; `ord(K·x) = M·e / gcd(M·e, K)` and the
coprime cancellation gives `gcd(M·e, K) = e`.) -/
theorem addOrderOf_nsmul_eq_of_coprime {G : Type u} [AddGroup G] (x : G) (M K : ℕ)
    [NeZero M] [NeZero K] (hMK : Nat.Coprime M K)
    (hM : M ∣ addOrderOf x) (hdvd : addOrderOf x ∣ M * K) :
    addOrderOf (K • x) = M := by
  obtain ⟨e, he⟩ := hM
  have heK : e ∣ K := by
    have h1 : M * e ∣ M * K := he ▸ hdvd
    exact (Nat.mul_dvd_mul_iff_left (Nat.pos_of_ne_zero (NeZero.ne M))).mp h1
  have hgcd : Nat.gcd (addOrderOf x) K = e := by
    rw [he, hMK.gcd_mul_left_cancel e]
    exact Nat.gcd_eq_left heK
  rw [addOrderOf_nsmul' x (NeZero.ne K), hgcd, he]
  have he0 : e ≠ 0 := by
    rintro rfl
    have h0 : addOrderOf x = 0 := by rw [he, Nat.mul_zero]
    rw [h0] at hdvd
    exact NeZero.ne (M * K) (Nat.eq_zero_of_zero_dvd hdvd)
  exact Nat.mul_div_cancel _ (Nat.pos_of_ne_zero he0)

/-- **[F3-exhaust-1]** A point factoring through a divisor bounds the divisor's ideal
by the point's kernel (step 1 of the exhaustion argument). -/
theorem RelEffCartierDiv.ideal_le_ker_of_factors {C : Scheme.{u}} {π : C ⟶ S}
    (D : RelEffCartierDiv π) {T : Scheme.{u}} {q : T ⟶ C}
    (hfac : ∃ w : T ⟶ D.ideal.subscheme, w ≫ D.ideal.subschemeι = q) :
    D.ideal ≤ q.ker := by
  obtain ⟨w, hw⟩ := hfac
  calc D.ideal = (D.ideal.subschemeι).ker :=
        (Scheme.IdealSheafData.ker_subschemeι (I := D.ideal)).symm
    _ ≤ (w ≫ D.ideal.subschemeι).ker := Scheme.Hom.le_ker_comp w _
    _ = q.ker := by rw [hw]

/-- **[F3-exhaust-2] (KM p. 29's prime avoidance)** Over a field, a point whose kernel
bounds a sections-divisor ideal has its kernel above ONE section's kernel, at any affine
open containing the point's image: the point's kernel ideal there is prime (the sections
over the one-point base form a domain), and primes detect factors of products. -/
theorem RelEffCartierDiv.exists_section_ker_le {k : Type u} [Field k]
    {C : Scheme.{u}} {π : C ⟶ Spec (CommRingCat.of k)} {n : ℕ}
    (Ps : Fin n → { z : Spec (CommRingCat.of k) ⟶ C // z ≫ π = 𝟙 _ })
    (hπ : IsSeparated π ∧ SmoothOfRelativeDimension 1 π)
    (q : Spec (CommRingCat.of k) ⟶ C)
    (hker : (RelEffCartierDiv.sectionsDivisor π Ps).ideal ≤ q.ker)
    (V : C.affineOpens) (hqV : q (default : ↑(Spec (CommRingCat.of k))) ∈ V.1) :
    ∃ j, (Scheme.Hom.ker (Ps j).1).ideal V ≤ (q.ker).ideal V := by
  -- the point's kernel ideal at V is prime
  haveI hQC : QuasiCompact q := ⟨fun U _ _ => (Set.toFinite _).isCompact⟩
  have hpre : q ⁻¹ᵁ V.1 = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hx : x = default := Unique.eq_default x
    rw [hx]
    exact hqV
  haveI hdom : IsDomain ↑Γ(Spec (CommRingCat.of k), q ⁻¹ᵁ V.1) := by
    rw [hpre]
    exact MulEquiv.isDomain k
      (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv.toMulEquiv
  have hkerV : (q.ker).ideal V = RingHom.ker ((q.app V.1).hom) := Scheme.Hom.ker_apply q V
  haveI hprime : ((q.ker).ideal V).IsPrime := by
    rw [hkerV]
    exact RingHom.ker_isPrime _
  -- the divisor ideal at V is the product of the section kernels
  have hDV : (RelEffCartierDiv.sectionsDivisor π Ps).ideal.ideal V
      = ∏ i, (Scheme.Hom.ker (Ps i).1).ideal V := by
    rw [show (RelEffCartierDiv.sectionsDivisor π Ps).ideal
        = ∏ i, Scheme.Hom.ker (Ps i).1 from by
      rw [RelEffCartierDiv.sectionsDivisor, dif_pos hπ]]
    have h1 : (∏ i, Scheme.Hom.ker (Ps i).1 : C.IdealSheafData).ideal
        = ∏ i, (Scheme.IdealSheafData.idealMonoidHom C) (Scheme.Hom.ker (Ps i).1) :=
      map_prod (Scheme.IdealSheafData.idealMonoidHom C) _ Finset.univ
    rw [show ((∏ i, Scheme.Hom.ker (Ps i).1 : C.IdealSheafData)).ideal V
        = ((∏ i, Scheme.Hom.ker (Ps i).1 : C.IdealSheafData).ideal) V from rfl, h1,
      Finset.prod_apply]
    rfl
  -- prime avoidance
  have hle : ∏ i, (Scheme.Hom.ker (Ps i).1).ideal V ≤ (q.ker).ideal V := by
    rw [← hDV]
    exact hker V
  obtain ⟨j, _, hj⟩ := (Ideal.IsPrime.prod_le hprime).mp hle
  exact ⟨j, hj⟩

/-- **[F3-exhaust-3] (the field-point rigidity)** Two `k`-algebra maps to `k` with nested
kernels are EQUAL: `a - φ(a)·1` lies in `ker φ ⊆ ker ψ`, so `ψ(a) = φ(a)`. The pure
core of KM p. 29's "the point IS one of the sections". -/
theorem algHom_eq_of_ker_le {k A : Type u} [Field k] [CommRing A] [Algebra k A]
    (φ ψ : A →ₐ[k] k) (h : RingHom.ker (φ : A →+* k) ≤ RingHom.ker (ψ : A →+* k)) :
    φ = ψ := by
  ext a
  have hmem : a - algebraMap k A (φ a) ∈ RingHom.ker (φ : A →+* k) := by
    rw [RingHom.mem_ker, map_sub]
    have hc : (φ : A →+* k) (algebraMap k A (φ a)) = φ a := by
      have := φ.commutes (φ a)
      simpa using this
    rw [hc]
    exact sub_self _
  have hthis := h hmem
  rw [RingHom.mem_ker, map_sub] at hthis
  have hc2 : (ψ : A →+* k) (algebraMap k A (φ a)) = φ a := by
    have := ψ.commutes (φ a)
    simpa using this
  rw [hc2] at hthis
  exact (sub_eq_zero.mp hthis).symm

section FieldExhaust

variable {k : Type u} [Field k] {C : Scheme.{u}}

/-- **[F3-exhaust-4a]** Evaluation of a `Spec k`-point at an affine open containing its
image, as a ring map to `k` (cast-free: `appLE` into the global sections of the point,
then the `ΓSpec` isomorphism). -/
noncomputable def pointEval (z : Spec (CommRingCat.of k) ⟶ C) (V : C.affineOpens)
    (he : ⊤ ≤ z ⁻¹ᵁ V.1) : ↑Γ(C, V.1) →+* k :=
  ((Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom).comp ((z.appLE V.1 ⊤ he).hom)

/-- **[F3-exhaust-4b]** The kernel of the evaluation is the point's kernel ideal at `V`. -/
theorem ker_pointEval (z : Spec (CommRingCat.of k) ⟶ C) (V : C.affineOpens)
    (he : ⊤ ≤ z ⁻¹ᵁ V.1) [QuasiCompact z] :
    RingHom.ker (pointEval z V he) = (z.ker).ideal V := by
  rw [pointEval, RingHom.ker_comp_of_injective _
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of k)).hom).injective]
  have hIso : IsIso (homOfLE he) :=
    ⟨homOfLE le_top, rfl, rfl⟩
  have hinj : Function.Injective
      (((Spec (CommRingCat.of k)).presheaf.map (homOfLE he).op).hom) := by
    haveI : IsIso ((Spec (CommRingCat.of k)).presheaf.map (homOfLE he).op) :=
      inferInstance
    exact (ConcreteCategory.bijective_of_isIso _).injective
  rw [show z.appLE V.1 ⊤ he
      = z.app V.1 ≫ (Spec (CommRingCat.of k)).presheaf.map (homOfLE he).op from rfl]
  rw [CommRingCat.hom_comp, RingHom.ker_comp_of_injective _ hinj]
  exact (Scheme.Hom.ker_apply z V).symm

/-- **[F3-exhaust-4c]** Two `Spec k`-points with image in the same affine open and equal
evaluations there are EQUAL: lift through the open, cancel the immersion's app-iso and
the restriction iso, and conclude by affine hom-extensionality. -/
theorem pointEval_injective (z₁ z₂ : Spec (CommRingCat.of k) ⟶ C) (V : C.affineOpens)
    (he₁ : ⊤ ≤ z₁ ⁻¹ᵁ V.1) (he₂ : ⊤ ≤ z₂ ⁻¹ᵁ V.1)
    (heval : pointEval z₁ V he₁ = pointEval z₂ V he₂) : z₁ = z₂ := by
  -- the lifts through V
  have hr₁ : Set.range z₁.base ⊆ Set.range V.1.ι.base := by
    intro x hx
    obtain ⟨y, rfl⟩ := hx
    have : y ∈ z₁ ⁻¹ᵁ V.1 := he₁ trivial
    rw [Scheme.Opens.range_ι]
    exact this
  have hr₂ : Set.range z₂.base ⊆ Set.range V.1.ι.base := by
    intro x hx
    obtain ⟨y, rfl⟩ := hx
    have : y ∈ z₂ ⁻¹ᵁ V.1 := he₂ trivial
    rw [Scheme.Opens.range_ι]
    exact this
  set q₁ := IsOpenImmersion.lift V.1.ι z₁ hr₁ with hq₁
  set q₂ := IsOpenImmersion.lift V.1.ι z₂ hr₂ with hq₂
  have hf₁ : q₁ ≫ V.1.ι = z₁ := IsOpenImmersion.lift_fac _ _ hr₁
  have hf₂ : q₂ ≫ V.1.ι = z₂ := IsOpenImmersion.lift_fac _ _ hr₂
  -- from evaluation equality to appLE equality
  have hLE : z₁.appLE V.1 ⊤ he₁ = z₂.appLE V.1 ⊤ he₂ := by
    have hinj : Function.Injective
        ((Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom) :=
      (ConcreteCategory.bijective_of_isIso _).injective
    ext a
    exact hinj (DFunLike.congr_fun heval a)
  -- decompose through the lifts and cancel the immersion's app-iso
  haveI hVi : IsIso (V.1.ι.app V.1) :=
    V.1.ι.isIso_app V.1 (by rw [Scheme.Opens.opensRange_ι])
  have hLE' : q₁.appLE (V.1.ι ⁻¹ᵁ V.1) ⊤ (by simp [Scheme.Opens.ι_preimage_self])
      = q₂.appLE (V.1.ι ⁻¹ᵁ V.1) ⊤ (by simp [Scheme.Opens.ι_preimage_self]) := by
    have hgen : ∀ (q : Spec (CommRingCat.of k) ⟶ ↑V.1) (z : Spec (CommRingCat.of k) ⟶ C)
        (hz : q ≫ V.1.ι = z) (he : ⊤ ≤ z ⁻¹ᵁ V.1),
        z.appLE V.1 ⊤ he = V.1.ι.app V.1 ≫ q.appLE (V.1.ι ⁻¹ᵁ V.1) ⊤
          (by simp [Scheme.Opens.ι_preimage_self]) := by
      rintro q z rfl he
      exact Scheme.Hom.comp_appLE q V.1.ι V.1 ⊤ he
    have h₁ := hgen q₁ z₁ hf₁ he₁
    have h₂ := hgen q₂ z₂ hf₂ he₂
    have := h₁.symm.trans (hLE.trans h₂)
    exact (cancel_epi (V.1.ι.app V.1)).mp this
  -- recover the appTops
  have hTop : q₁.appTop = q₂.appTop := by
    have hmap : ∀ (q : Spec (CommRingCat.of k) ⟶ ↑V.1),
        (↑V.1 : Scheme).presheaf.map
            (homOfLE (le_top : V.1.ι ⁻¹ᵁ V.1 ≤ ⊤)).op
          ≫ q.appLE (V.1.ι ⁻¹ᵁ V.1) ⊤ (by simp [Scheme.Opens.ι_preimage_self])
        = q.appLE ⊤ ⊤ (by simp) := by
      intro q
      exact Scheme.Hom.map_appLE q _ _
    have hcomb : q₁.appLE ⊤ ⊤ (by simp) = q₂.appLE ⊤ ⊤ (by simp) := by
      rw [← hmap q₁, ← hmap q₂, hLE']
    have hTT : ∀ (q : Spec (CommRingCat.of k) ⟶ ↑V.1)
        (e : (⊤ : (Spec (CommRingCat.of k)).Opens) ≤ q ⁻¹ᵁ (⊤ : (↑V.1 : Scheme).Opens)),
        q.appLE ⊤ ⊤ e = q.appTop := by
      intro q e
      rw [Scheme.Hom.appLE]
      rw [show homOfLE e = 𝟙 (⊤ : (Spec (CommRingCat.of k)).Opens) from rfl]
      simp [Scheme.Hom.appTop]
    rw [← hTT q₁ (by simp), ← hTT q₂ (by simp)]
    exact hcomb
  -- affine extensionality and descent to C
  haveI : IsAffine (↑V.1 : Scheme) := V.2
  have hq : q₁ = q₂ := ext_of_isAffine hTop
  rw [← hf₁, ← hf₂, hq]

/-- **[F3-exhaust-4d]** For a SECTION `z` of `π : C ⟶ Spec k`, the evaluation `pointEval z`
splits the `k`-algebra structure map `π` induces on `Γ(C, V)`: the composite
`k → Γ(Spec k, ⊤) → Γ(C, V) → Γ(Spec k, ⊤) → k` is the identity (`appLE_comp_appLE`
folds the middle to `(z ≫ π).appLE = (𝟙).appLE = 𝟙`). -/
theorem pointEval_structure {π : C ⟶ Spec (CommRingCat.of k)}
    (z : Spec (CommRingCat.of k) ⟶ C) (hz : z ≫ π = 𝟙 _) (V : C.affineOpens)
    (he : ⊤ ≤ z ⁻¹ᵁ V.1) (hVle : V.1 ≤ π ⁻¹ᵁ ⊤) (c : k) :
    pointEval z V he
      ((π.appLE ⊤ V.1 hVle).hom ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom c)) = c := by
  have hfold : ∀ (w : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of k))
      (hw : w = z ≫ π) (e : ⊤ ≤ w ⁻¹ᵁ ⊤),
      w.appLE ⊤ ⊤ e = π.appLE ⊤ V.1 hVle ≫ z.appLE V.1 ⊤ he := by
    rintro w rfl e
    exact (Scheme.Hom.appLE_comp_appLE z π ⊤ V.1 ⊤ hVle he).symm
  have hid : Scheme.Hom.appLE (𝟙 (Spec (CommRingCat.of k))) ⊤ ⊤ (by simp)
      = π.appLE ⊤ V.1 hVle ≫ z.appLE V.1 ⊤ he := hfold _ hz.symm _
  have hone : Scheme.Hom.appLE (𝟙 (Spec (CommRingCat.of k))) ⊤ ⊤ (by simp)
      = 𝟙 Γ(Spec (CommRingCat.of k), ⊤) := by
    rw [Scheme.Hom.appLE, Scheme.Hom.id_app]
    simp
  have hcollapse := hone.symm.trans hid
  have happ := congrArg (fun m => (Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom
    ((CommRingCat.Hom.hom m) ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom c))) hcollapse
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_id,
    RingHom.id_apply] at happ
  have hio : (Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom
      ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom c) = c := by
    have := (Scheme.ΓSpecIso (CommRingCat.of k)).inv_hom_id
    have h2 := congrArg (fun m => (CommRingCat.Hom.hom m) c) this
    simpa using h2
  rw [pointEval]
  rw [RingHom.comp_apply]
  rw [← happ, hio]

/-- **[F3-exhaust-4e-aux]** A `Spec k`-point whose kernel ideal at `V` is proper has its
(unique) image point inside `V` — otherwise the preimage is empty and the kernel is
everything. -/
theorem mem_of_ker_ideal_ne_top (z : Spec (CommRingCat.of k) ⟶ C) (V : C.affineOpens)
    (h : (z.ker).ideal V ≠ ⊤) : z (default : ↑(Spec (CommRingCat.of k))) ∈ V.1 := by
  by_contra hmem
  apply h
  haveI hQC : QuasiCompact z := ⟨fun U _ _ => (Set.toFinite _).isCompact⟩
  have hpre : z ⁻¹ᵁ V.1 = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have := Unique.eq_default x
    subst this
    exact absurd hx hmem
  rw [Scheme.Hom.ker_apply z V]
  rw [Ideal.eq_top_iff_one, RingHom.mem_ker]
  have hsub : Subsingleton ↑Γ(Spec (CommRingCat.of k), z ⁻¹ᵁ V.1) := by
    rw [hpre]
    infer_instance
  exact Subsingleton.elim _ _

/-- **[F3-exhaust] (KM p. 29, the exhaustion argument — ASSEMBLED)** Over a field, a
point of `C` factoring through the sections-divisor `∏ ker(Pᵢ)` IS one of the sections:
its kernel bounds the divisor ideal (exhaust-1), prime avoidance picks a section whose
kernel it dominates at an affine chart (exhaust-2), field rigidity upgrades kernel
domination of `k`-algebra characters to equality (exhaust-3), and the evaluation
dictionary (exhaust-4a–d) transports this back to equality of morphisms. -/
theorem RelEffCartierDiv.point_eq_section_of_factors
    {π : C ⟶ Spec (CommRingCat.of k)} {n : ℕ}
    (Ps : Fin n → { z : Spec (CommRingCat.of k) ⟶ C // z ≫ π = 𝟙 _ })
    (hπ : IsSeparated π ∧ SmoothOfRelativeDimension 1 π)
    (q : Spec (CommRingCat.of k) ⟶ C) (hq : q ≫ π = 𝟙 _)
    (hfac : ∃ w, w ≫ (RelEffCartierDiv.sectionsDivisor π Ps).ideal.subschemeι = q)
    (V : C.affineOpens) (hqV : q (default : ↑(Spec (CommRingCat.of k))) ∈ V.1) :
    ∃ j, q = (Ps j).1 := by
  haveI hQCq : QuasiCompact q := ⟨fun U _ _ => (Set.toFinite _).isCompact⟩
  -- exhaust-1 + exhaust-2: a section whose kernel ideal at V the point's dominates
  have hker : (RelEffCartierDiv.sectionsDivisor π Ps).ideal ≤ q.ker :=
    RelEffCartierDiv.ideal_le_ker_of_factors _ hfac
  obtain ⟨j, hj⟩ := RelEffCartierDiv.exists_section_ker_le Ps hπ q hker V hqV
  -- evaluation characters
  have heq : ⊤ ≤ q ⁻¹ᵁ V.1 := by
    intro x _
    have := Unique.eq_default x
    subst this
    exact hqV
  -- the point's kernel ideal at V is proper (prime), so the section also lands in V
  haveI hdom : IsDomain ↑Γ(Spec (CommRingCat.of k), q ⁻¹ᵁ V.1) := by
    rw [top_le_iff.mp heq]
    exact MulEquiv.isDomain k
      (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv.toMulEquiv
  have hprime : ((q.ker).ideal V).IsPrime := by
    rw [Scheme.Hom.ker_apply q V]
    exact RingHom.ker_isPrime _
  have hPjV : (Ps j).1 (default : ↑(Spec (CommRingCat.of k))) ∈ V.1 :=
    mem_of_ker_ideal_ne_top (Ps j).1 V
      (fun htop => hprime.ne_top (top_le_iff.mp (htop ▸ hj)))
  have heP : ⊤ ≤ (Ps j).1 ⁻¹ᵁ V.1 := by
    intro x _
    have := Unique.eq_default x
    subst this
    exact hPjV
  haveI hQCP : QuasiCompact (Ps j).1 := ⟨fun U _ _ => (Set.toFinite _).isCompact⟩
  -- the k-algebra structure via π
  letI : Algebra k ↑Γ(C, V.1) :=
    ((π.appLE ⊤ V.1 le_top).hom.comp
      ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom)).toAlgebra
  let φP : ↑Γ(C, V.1) →ₐ[k] k :=
    { toRingHom := pointEval (Ps j).1 V heP
      commutes' := fun c => pointEval_structure (Ps j).1 (Ps j).2 V heP le_top c }
  let φq : ↑Γ(C, V.1) →ₐ[k] k :=
    { toRingHom := pointEval q V heq
      commutes' := fun c => pointEval_structure q hq V heq le_top c }
  -- kernel domination transports to the characters; rigidity closes
  have hkerle : RingHom.ker (φP : ↑Γ(C, V.1) →+* k) ≤ RingHom.ker (φq : ↑Γ(C, V.1) →+* k) := by
    show RingHom.ker (pointEval (Ps j).1 V heP) ≤ RingHom.ker (pointEval q V heq)
    rw [ker_pointEval, ker_pointEval]
    exact hj
  have hφ : φP = φq := algHom_eq_of_ker_le φP φq hkerle
  have hEval : pointEval (Ps j).1 V heP = pointEval q V heq :=
    congrArg AlgHom.toRingHom hφ
  exact ⟨j, (pointEval_injective (Ps j).1 q V heP heq hEval).symm⟩

end FieldExhaust

/-- **[F3-census] (KM p. 29: "G(k) contains precisely N₁ points killed by N₁" meets
the exhaustion)** Over a separably closed field with `M` invertible: if `P` has exact
order `M·K` (coprime), then `M` divides the honest point-order of `P`. The `M`-killed
factoring points form a group of order exactly `M` (locus squeeze + étale count); the
exhaustion pins every one of them inside the cyclic group `⟨P⟩`; Lagrange concludes. -/
theorem Section.HasExactOrder.M_dvd_addOrderOf {k : Type u} [Field k] [IsSepClosed k]
    {E : EllipticCurve (Spec (CommRingCat.of k))} {P : E.Section} (M K : ℕ)
    [NeZero M] [NeZero K] (hMK : Nat.Coprime M K) [NeZero (M * K)]
    [IsFinite (E.mulByHom (M : ℤ))] [IsFinite (E.mulByHom (K : ℤ))]
    (hinvM : NIsInvertible (Spec (CommRingCat.of k)) M)
    (h : P.HasExactOrder E (M * K)) :
    M ∣ addOrderOf P := by
  classical
  have hpos : IsSeparated E.π ∧ SmoothOfRelativeDimension 1 E.π :=
    ⟨inferInstance, E.smooth⟩
  have hdeg : ∀ s, (P.orderDivisor E (M * K)).degree s = M * K := fun s =>
    RelEffCartierDiv.sectionsDivisor_degree E.π E.smooth _ s
  have hkillP : ((M * K : ℕ) : ℤ) • P = 0 := h.smul_eq_zero E
  have h₁ : ((M : ℤ) * K) % ((M * K : ℕ) : ℤ) = 0 := by
    push_cast
    exact Int.emod_self
  have h₂ : ((K : ℤ) * M) % ((M * K : ℕ) : ℤ) = 0 := by
    push_cast
    rw [Int.mul_comm]
    exact Int.emod_self
  have hD : (P.orderDivisor E (M * K)).IsSubgroup E := h
  -- the finite flat étale instance scaffold for the M-kernel
  haveI hMflat : Flat ((P.orderDivisor E (M * K)).smulKernelπ E (M : ℤ)) :=
    RelEffCartierDiv.IsSubgroup.smulKernelπ_flat E hD M K hMK hdeg h₁ h₂
  haveI hMfin : IsFinite ((P.orderDivisor E (M * K)).smulKernelπ E (M : ℤ)) :=
    RelEffCartierDiv.smulKernelπ_isFinite E _ (M : ℤ)
  haveI hMet : Etale ((P.orderDivisor E (M * K)).smulKernelπ E (M : ℤ)) :=
    RelEffCartierDiv.smulKernelπ_etale E _ M hinvM hMflat
  -- the M-killed factoring points number exactly M
  have hsq : ((P.orderDivisor E (M * K)).smulKernelπ E (M : ℤ)).finrank
      (default : ↑(Spec (CommRingCat.of k))) = M :=
    RelEffCartierDiv.IsSubgroup.smulKernelπ_finrank_eq_of_M_invertible hD M K hMK
      hinvM hdeg h₁ h₂ _
  have hcard : Nat.card { Q : E.Point (𝟙 (Spec (CommRingCat.of k))) //
      (M : ℤ) • Q = 0 ∧ ∃ w : Spec (CommRingCat.of k)
        ⟶ (P.orderDivisor E (M * K)).ideal.subscheme,
          w ≫ (P.orderDivisor E (M * K)).ideal.subschemeι = Q.1 } = M := by
    rw [RelEffCartierDiv.card_killed_points _ (M : ℤ) default, hsq]
  -- the group structure on them
  obtain ⟨H, hH⟩ := hD (𝟙 (Spec (CommRingCat.of k)))
  let A : AddSubgroup (E.Point (𝟙 (Spec (CommRingCat.of k)))) :=
    { carrier := { Q | (M : ℤ) • Q = 0 ∧ ∃ w : Spec (CommRingCat.of k)
          ⟶ (P.orderDivisor E (M * K)).ideal.subscheme,
            w ≫ (P.orderDivisor E (M * K)).ideal.subschemeι = Q.1 }
      zero_mem' := ⟨smul_zero _, (hH 0).mp H.zero_mem⟩
      add_mem' := fun {P₁ Q₁} hP hQ => ⟨by rw [smul_add, hP.1, hQ.1, add_zero],
        (hH _).mp (H.add_mem ((hH P₁).mpr hP.2) ((hH Q₁).mpr hQ.2))⟩
      neg_mem' := fun {P₁} hP => ⟨by rw [smul_neg, hP.1, neg_zero],
        (hH _).mp (H.neg_mem ((hH P₁).mpr hP.2))⟩ }
  have hcardA : Nat.card A = M := hcard
  -- the exhaustion pins A inside ⟨P⟩
  have hsub : A ≤ AddSubgroup.zmultiples P := by
    rintro Q ⟨-, hfac⟩
    obtain ⟨-, ⟨V, hV, rfl⟩, hxV, -⟩ :=
      E.E.isBasis_affineOpens.exists_subset_of_mem_open
        (Set.mem_univ (Q.1 (default : ↑(Spec (CommRingCat.of k))))) isOpen_univ
    obtain ⟨j, hj⟩ := RelEffCartierDiv.point_eq_section_of_factors (π := E.π)
      (fun a : Fin (M * K) => ((((a : ℕ) : ℤ) + 1) • P : E.Point (𝟙 _)))
      hpos Q.1 Q.2
      (by
        rw [show (RelEffCartierDiv.sectionsDivisor E.π
            (fun a : Fin (M * K) => ((((a : ℕ) : ℤ) + 1) • P : E.Point (𝟙 _))))
          = P.orderDivisor E (M * K) from rfl]
        exact hfac)
      ⟨V, hV⟩ hxV
    exact ⟨(((j : ℕ) : ℤ) + 1), (Subtype.ext hj).symm⟩
  -- Lagrange in the finite cyclic group ⟨P⟩
  have hford : IsOfFinAddOrder P := by
    rw [isOfFinAddOrder_iff_nsmul_eq_zero]
    exact ⟨M * K, Nat.pos_of_ne_zero (NeZero.ne _), by
      rw [← natCast_zsmul]; exact hkillP⟩
  haveI hfin : Finite (AddSubgroup.zmultiples P) := hford.finite_zmultiples
  have hdvd : Nat.card A ∣ Nat.card (AddSubgroup.zmultiples P) :=
    AddSubgroup.card_dvd_of_le hsub
  rwa [hcardA, Nat.card_zmultiples] at hdvd

/-- **[F3-distinct] (KM 1.5.3's condition (3) at the geometric points of `S[1/M]`)**
Over a separably closed field with `M` invertible: if `P` has exact order `M·K`
(coprime), the nonzero multiples `a·(K·P)`, `0 < a < M`, are all nonzero — i.e. `K·P`
has honest point-order exactly `M` (census + cyclic arithmetic). -/
theorem Section.HasExactOrder.smul_nsmul_ne_zero {k : Type u} [Field k] [IsSepClosed k]
    {E : EllipticCurve (Spec (CommRingCat.of k))} {P : E.Section} (M K : ℕ)
    [NeZero M] [NeZero K] (hMK : Nat.Coprime M K) [NeZero (M * K)]
    [IsFinite (E.mulByHom (M : ℤ))] [IsFinite (E.mulByHom (K : ℤ))]
    (hinvM : NIsInvertible (Spec (CommRingCat.of k)) M)
    (h : P.HasExactOrder E (M * K)) :
    ∀ a : ℕ, 0 < a → a < M → (a : ℤ) • ((K : ℤ) • P) ≠ 0 := by
  have hdvdMK : addOrderOf P ∣ M * K := by
    apply addOrderOf_dvd_of_nsmul_eq_zero
    have := h.smul_eq_zero E
    rwa [natCast_zsmul] at this
  have hMdvd : M ∣ addOrderOf P :=
    Section.HasExactOrder.M_dvd_addOrderOf M K hMK hinvM h
  have hord : addOrderOf (K • P) = M :=
    addOrderOf_nsmul_eq_of_coprime P M K hMK hMdvd hdvdMK
  intro a ha0 haM hcon
  have hzsmul : a • (K • P) = 0 := by
    have h2 := hcon
    rw [natCast_zsmul, natCast_zsmul] at h2
    exact h2
  have hdvda : addOrderOf (K • P) ∣ a := addOrderOf_dvd_of_nsmul_eq_zero hzsmul
  rw [hord] at hdvda
  exact absurd haM (Nat.not_lt.mpr (Nat.le_of_dvd ha0 hdvda))


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
