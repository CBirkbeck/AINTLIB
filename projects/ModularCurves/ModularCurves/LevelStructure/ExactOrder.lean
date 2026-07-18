/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.LevelStructure.CartierDivisor
import ModularCurves.EllipticCurve.Torsion
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# Points of exact order N (Drinfeld / KM 1.4)

The delicate definition this project exists to get right. Transcribed from KM 1.4
(verbatim source with proofs in hand — preview, book pp. 15–19):

* KM 1.3.6: an effective Cartier divisor `D` in a smooth group-curve `C/S`, proper over
  `S`, **is a subgroup** "if for every `S`-scheme `T` the subset `D(T)` of the group `C(T)`
  is in fact a sub-group".
* KM 1.4.1: "We say that a point `P ∈ C(S)` has **'exact order N'** if the effective
  Cartier divisor `D` in `C/S` of degree `N` defined by `D := [P] + [2P] + ⋯ + [NP]` is a
  subgroup of `C/S`."
* KM 1.4.2: exact order `N` ⇒ `NP = 0` (via: a finite locally free commutative group
  scheme of rank `N` is killed by `N`, KM cite [Oort–Tate] — black-box register item
  BB-DELIGNE).
* Caution 1.4.3: over an `𝔽_p`-scheme the zero section has "exact order `pⁿ`" for every
  `n` (it generates `Ker(Fⁿ)`) — "a given point can have many different 'exact orders'".
* KM 1.4.4: for `N` invertible on `S`, exact order `N` ⇔ geometric-fibrewise the `N`
  points `{a P}` are pairwise distinct ⇔ `Σₐ [aP]` is finite étale over `S` ⇔ the map
  `ℤ/Nℤ → C`, `1 ↦ P`, is a closed immersion onto `Σₐ [aP]`.

This is precisely the subtlety flagged for `Y₁(N)`: "what it means to be a point of exact
order `N` … is slightly delicate over schemes, even if `N` is invertible on the base."
The naive fibrewise notion is recovered — as a *theorem* — exactly when `N` is invertible.
-/

open AlgebraicGeometry CategoryTheory Limits

attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory
  CategoryTheory.Over.braidedCategory

universe u

namespace ModularCurves

namespace EllipticCurve

variable {S : Scheme.{u}} (E : EllipticCurve S)

/-- A section of `E/S`, i.e. a point `P ∈ E(S)`. -/
abbrev Section := E.Point (𝟙 S)

/-- Pull a point back along `t : T ⟶ S` (restriction of a section to a `T`-point). -/
def Point.pull {T : Scheme.{u}} (t : T ⟶ S) (P : E.Section) : E.Point t :=
  ⟨t ≫ P.1, by rw [Category.assoc, P.2, Category.comp_id]⟩

/-- Pulling points back along `t : T ⟶ S` is compatible with integer scalars: both
sides are `≫ [a]` by `point_smul_eq_comp_mulBy`. -/
theorem Point.pull_zsmul {T : Scheme.{u}} (t : T ⟶ S) (a : ℤ) (P : E.Section) :
    Point.pull E t (a • P) = a • Point.pull E t P := by
  refine Subtype.ext ?_
  show t ≫ ((a • P : E.Point (𝟙 S)) : S ⟶ E.E) = ((a • Point.pull E t P : E.Point t) :
    T ⟶ E.E)
  rw [point_smul_eq_comp_mulBy, point_smul_eq_comp_mulBy, ← Category.assoc]
  rfl

/-- Pulling points back along `t` is additive: `pull` is a group homomorphism (it is
precomposition on the same curve, so distributes over the point group — no canonicity
needed, unlike `EllHom.pullSection` between different curves). -/
theorem Point.pull_add {T : Scheme.{u}} (t : T ⟶ S) (P Q : E.Section) :
    Point.pull E t (P + Q) = Point.pull E t P + Point.pull E t Q := by
  letI : CommGroup (Over.mk t ⟶ E.asOver) := Hom.commGroup
  letI : CommGroup (Over.mk (𝟙 S) ⟶ E.asOver) := Hom.commGroup
  refine (E.pointEquivOverHom t).injective ?_
  have hw : t ≫ (Over.mk (𝟙 S)).hom = (Over.mk t).hom := by
    simp
  have corr : ∀ R : E.Section, (E.pointEquivOverHom t) (Point.pull E t R) =
      (Over.homMk t hw : Over.mk t ⟶ Over.mk (𝟙 S)) ≫
        (E.pointEquivOverHom (𝟙 S) R) := by
    intro R
    apply Over.OverMorphism.ext
    rw [Over.comp_left]
    rfl
  rw [pointEquivOverHom_add, corr, corr, corr, pointEquivOverHom_add,
    MonObj.comp_mul]

/-- Pulling back the zero point gives zero. -/
theorem Point.pull_zero {T : Scheme.{u}} (t : T ⟶ S) :
    Point.pull E t (0 : E.Section) = 0 := by
  have h := Point.pull_zsmul E t 0 0
  rwa [zero_smul, zero_smul] at h

/-- **KM 1.3.6**: a relative effective Cartier divisor `D` in `E/S` *is a subgroup* if for
every `T ⟶ S` the subset of `E(T)` consisting of points factoring through `D` is a
subgroup of `E(T)`: it contains `0`, and is stable under addition and negation. -/
def _root_.ModularCurves.RelEffCartierDiv.IsSubgroup (D : RelEffCartierDiv E.π) : Prop :=
  ∀ ⦃T : Scheme.{u}⦄ (g : T ⟶ S),
    ∃ H : AddSubgroup (E.Point g),
      ∀ P : E.Point g, P ∈ H ↔ ∃ h : T ⟶ D.ideal.subscheme, h ≫ D.ideal.subschemeι = P.1

/-- The divisor `[P] + [2P] + ⋯ + [NP]` of KM 1.4.1 (via DS4a). -/
noncomputable def Section.orderDivisor (P : E.Section) (N : ℕ) : RelEffCartierDiv E.π :=
  RelEffCartierDiv.sectionsDivisor E.π
    (fun a : Fin N ↦ ((((a : ℕ) : ℤ) + 1) • P : E.Point (𝟙 S)))

/-- **KM 1.4.1 — a point of exact order `N`** (Drinfeld): `P ∈ E(S)` has exact order `N`
if the degree-`N` relative effective Cartier divisor `[P] + [2P] + ⋯ + [NP]` is a subgroup
of `E/S`. -/
def Section.HasExactOrder (P : E.Section) (N : ℕ) [NeZero N] : Prop :=
  (P.orderDivisor E N).IsSubgroup E

/-- **Register box `BB-DELIGNE` (KM 1.4.2, cite [Oort–Tate])**, in the project's
subgroup-divisor encoding: a subgroup divisor of constant degree `N` is killed by `N`
— every point factoring through it is annihilated by `N`. KM (verbatim): *"a finite
locally free commutative group scheme of rank `N` is killed by `N`"*. -/
theorem _root_.ModularCurves.RelEffCartierDiv.IsSubgroup.smul_eq_zero_of_factors
    {D : RelEffCartierDiv E.π} (hD : D.IsSubgroup E) {N : ℕ} [NeZero N]
    (hdeg : ∀ s : S, D.degree s = N) {T : Scheme.{u}} (g : T ⟶ S) (Q : E.Point g)
    (hQ : ∃ h : T ⟶ D.ideal.subscheme, h ≫ D.ideal.subschemeι = Q.1) :
    (N : ℤ) • Q = 0 := by sorry

/-- **(T-D6a-ii, L3 — KM 1.4.4 (1)⟹(2) divisor side)** The order divisor is natural in
the base: base-changing `[P] + ⋯ + [NP]` along `t : T ⟶ S` gives the order divisor of
the pulled section on the base-changed curve. -/
theorem Section.orderDivisor_baseChange (P : E.Section) (N : ℕ) {T : Scheme.{u}}
    (t : T ⟶ S) :
    (P.orderDivisor E N).baseChange t =
      Section.orderDivisor (E.baseChange t)
        (Point.asSection E t (Point.pull E t P)) N := by
  have hpos : IsSeparated E.π ∧ SmoothOfRelativeDimension 1 E.π :=
    ⟨inferInstance, E.smooth⟩
  have hpos' : IsSeparated (E.baseChange t).π ∧
      SmoothOfRelativeDimension 1 (E.baseChange t).π :=
    ⟨inferInstance, (E.baseChange t).smooth⟩
  apply RelEffCartierDiv.ext
  have hL : ((P.orderDivisor E N).baseChange t).ideal =
      (∏ a : Fin N, Scheme.Hom.ker
        (((((a : ℕ) : ℤ) + 1) • P : E.Point (𝟙 S))).1).comap
        (Limits.pullback.fst E.π t) := by
    rw [RelEffCartierDiv.baseChange_ideal]
    congr 1
    rw [Section.orderDivisor, RelEffCartierDiv.sectionsDivisor, dif_pos hpos]
  have hR : (Section.orderDivisor (E.baseChange t)
      (Point.asSection E t (Point.pull E t P)) N).ideal =
      ∏ a : Fin N, Scheme.Hom.ker
        (((((a : ℕ) : ℤ) + 1) • Point.asSection E t (Point.pull E t P) :
          (E.baseChange t).Point (𝟙 T))).1 := by
    rw [Section.orderDivisor, RelEffCartierDiv.sectionsDivisor, dif_pos hpos']
  rw [hL, hR, Scheme.IdealSheafData.comap_prod]
  refine Finset.prod_congr rfl fun a _ ↦ ?_
  have hsec : ((((a : ℕ) : ℤ) + 1) • Point.asSection E t (Point.pull E t P) :
      (E.baseChange t).Point (𝟙 T)) =
      Point.asSection E t (Point.pull E t ((((a : ℕ) : ℤ) + 1) • P)) :=
    ((Point.asSection_zsmul E t (((a : ℕ) : ℤ) + 1) (Point.pull E t P)).symm).trans
      (congrArg (Point.asSection E t)
        (Point.pull_zsmul E t ((((a : ℕ) : ℤ) + 1)) P).symm)
  have hker := RelEffCartierDiv.ker_sectionBaseChange
    (((((a : ℕ) : ℤ) + 1) • P : E.Point (𝟙 S))).1
    (((((a : ℕ) : ℤ) + 1) • P : E.Point (𝟙 S))).2 t
  exact ((congrArg (fun Q : (E.baseChange t).Point (𝟙 T) ↦
    Scheme.Hom.ker Q.1) hsec).trans hker).symm

/-- **(T-D6a-ii, L4 — KM 1.3.6 base-change stability)** Being a subgroup divisor is stable
under base change: if `D` is a subgroup of `E/S`, then `D` base-changed along `t : T ⟶ S`
is a subgroup of `E ×_S T / T`. The point-group transport is `Point.baseChangeEquiv`; the
factoring correspondence is `exists_factor_comap_iff` (the `comapIso` dictionary). -/
theorem _root_.ModularCurves.RelEffCartierDiv.IsSubgroup.baseChange
    {D : RelEffCartierDiv E.π} (hD : D.IsSubgroup E) {T : Scheme.{u}} (t : T ⟶ S) :
    (D.baseChange t).IsSubgroup (E.baseChange t) := by
  intro T' g'
  obtain ⟨H, hH⟩ := hD (g' ≫ t)
  refine ⟨H.comap (Point.baseChangeEquiv E t g').toAddMonoidHom, fun Q ↦ ?_⟩
  rw [AddSubgroup.mem_comap, AddEquiv.coe_toAddMonoidHom, hH,
    Point.baseChangeEquiv_apply_coe, RelEffCartierDiv.baseChange_ideal]
  exact (AlgebraicGeometry.Scheme.IdealSheafData.exists_factor_comap_iff D.ideal
    (Limits.pullback.fst E.π t) Q.1).symm

/-- **(T-D6a-ii, headline — KM 1.4.4 (1)⟹(2))** Exact order is preserved by base change:
if `P ∈ E(S)` has exact order `N`, its restriction to any `T ⟶ S` has exact order `N` on
the base-changed curve. -/
theorem Section.HasExactOrder.baseChange {P : E.Section} {N : ℕ} [NeZero N]
    (h : P.HasExactOrder E N) {T : Scheme.{u}} (t : T ⟶ S) :
    Section.HasExactOrder (E.baseChange t)
      (Point.asSection E t (Point.pull E t P)) N := by
  show (Section.orderDivisor (E.baseChange t)
    (Point.asSection E t (Point.pull E t P)) N).IsSubgroup (E.baseChange t)
  rw [← Section.orderDivisor_baseChange]
  exact RelEffCartierDiv.IsSubgroup.baseChange E (D := P.orderDivisor E N) h t

/-- **(T-D5 = KM 1.4.2)** Exact order `N` implies `N • P = 0`. Black box BB-DELIGNE: a
finite locally free commutative group scheme of rank `N` is killed by `N` (KM cite
[Oort–Tate]). -/
theorem Section.HasExactOrder.smul_eq_zero {P : E.Section} {N : ℕ} [NeZero N]
    (h : P.HasExactOrder E N) : (N : ℤ) • P = 0 := by
  have hsep : IsSeparated E.π := inferInstance
  have hpos : IsSeparated E.π ∧ SmoothOfRelativeDimension 1 E.π := ⟨hsep, E.smooth⟩
  have hdeg : ∀ s, (P.orderDivisor E N).degree s = N := fun s ↦
    RelEffCartierDiv.sectionsDivisor_degree E.π E.smooth _ s
  refine RelEffCartierDiv.IsSubgroup.smul_eq_zero_of_factors E h hdeg (𝟙 S) P ?_
  have hideal : (P.orderDivisor E N).ideal =
      ∏ a : Fin N, Scheme.Hom.ker (((((a : ℕ) : ℤ) + 1) • P : E.Point (𝟙 S))).1 := by
    rw [Section.orderDivisor, RelEffCartierDiv.sectionsDivisor, dif_pos hpos]
  have h0 : (((((0 : Fin N) : ℕ) : ℤ) + 1) • P : E.Point (𝟙 S)) = P := by
    simp
  have hle : (P.orderDivisor E N).ideal ≤ Scheme.Hom.ker P.1 := by
    rw [hideal]
    have hle0 : (∏ a : Fin N,
        Scheme.Hom.ker (((((a : ℕ) : ℤ) + 1) • P : E.Point (𝟙 S))).1) ≤
        Scheme.Hom.ker (((((0 : Fin N) : ℕ) : ℤ) + 1) • P : E.Point (𝟙 S)).1 := by
      intro U
      have hprod : (∏ a : Fin N,
          Scheme.Hom.ker (((((a : ℕ) : ℤ) + 1) • P : E.Point (𝟙 S))).1).ideal =
          ∏ a : Fin N,
            (Scheme.Hom.ker (((((a : ℕ) : ℤ) + 1) • P : E.Point (𝟙 S))).1).ideal :=
        map_prod (Scheme.IdealSheafData.idealMonoidHom E.E) _ _
      calc (∏ a : Fin N,
          Scheme.Hom.ker (((((a : ℕ) : ℤ) + 1) • P : E.Point (𝟙 S))).1).ideal U
          = ∏ a : Fin N, (Scheme.Hom.ker
              (((((a : ℕ) : ℤ) + 1) • P : E.Point (𝟙 S))).1).ideal U := by
            rw [hprod]
            exact Finset.prod_apply U Finset.univ _
        _ ≤ _ :=
          Ideal.prod_le_inf.trans (Finset.inf_le (Finset.mem_univ (0 : Fin N)))
    rw [h0] at hle0
    exact hle0
  have hPc : IsClosedImmersion P.1 := by
    have h1 : IsClosedImmersion (P.1 ≫ E.π) := by
      rw [P.2]
      infer_instance
    exact IsClosedImmersion.of_comp P.1 E.π
  refine ⟨P.1.toImage ≫ Scheme.IdealSheafData.inclusion hle, ?_⟩
  rw [Category.assoc, Scheme.IdealSheafData.inclusion_subschemeι]
  exact P.1.toImage_imageι

/-- **Register box `T-D6b` (KM 1.4.4, (2)⟹(3) at a geometric point)**: over an
algebraically closed field the subgroup divisor of rank `N` is, for `N` invertible,
finite étale, hence consists of `N` distinct points, which by the divisor equality
`G = Σ [aP]` are exactly the multiples — so no proper multiple vanishes. KM
(verbatim): *"G is automatically finite etale over k of rank N. Therefore as a
Cartier divisor in C_k, G consists of a uniquely determined set of N distinct
points."* Discharge route (re-assessed 2026-07-08, p0): the base-change linchpin
`comap_mul` is now PROVEN (`ForMathlib/IdealSheafComapMul.lean`, T-D6a-i,
sorry-free over arbitrary schemes), but two layers still gate this box —
(a) the base-change *assembly* identifying `(orderDivisor P N).baseChange t` with
`orderDivisor (pull P) N` over `E ×_S k` = T-D6a-ii (in progress, beastmode-A's tail);
(b) the genuinely-absent étale core — a finite locally free rank-`N` group scheme over
a field with `N` invertible is finite étale (BB-DIFF / the flf-discriminant criterion,
KM (3)⟺(4)), and finite étale over an algebraically closed `k` yields `N` distinct
reduced geometric points.

RE-ASSESSMENT 2026-07-08 (beastmode-A, post T-D6a-ii; SHARPER ROUTE — NOT CARTIER):
the (1)⟹(2) half is now DISCHARGEABLE by `Section.HasExactOrder.baseChange` (proven
today: exact order is base-change stable), reducing this box to the pure field-level
(2)⟹(3). Crucially, (2)⟹(3) does NOT need Cartier's theorem in general: over the
*algebraically closed* fibre `k̄` the argument is elementary given the project's
already-proven `Torsionπ.etale` (T-B5′: `E[N] ⟶ S` finite étale when `N`
invertible). Route: (a) the subgroup-divisor subscheme `G` is killed by `N`
(`IsSubgroup.smul_eq_zero_of_factors`, proven) ⟹ `G` factors through `E[N]`; (b) `E[N]`
finite étale over `k̄` ⟹ `E[N] ≅ Spec(k̄^{N²})`; (c) a closed subscheme of `Spec(k̄^n)`
is a quotient `k̄^n/I ≅ k̄^m`, hence REDUCED — so `G` (length `N`) is `N` distinct
reduced points; (d) `G = Σ_{b} [bP]` ⟹ the `b·P` are distinct ⟹ no proper multiple
vanishes. MISSING (bounded, not Cartier): the divisor-`G` ↔ closed-subscheme bridge, the
`closed-in-étale-over-k̄ ⟹ reduced` lemma (comm-alg over `k̄^n`), and length↔point-count
(project has `ForMathlib/EtaleSectionsCount` + `TorsionFibre.torsionPointsEquiv` as
substrate). Kept `state: open` (bounded field-level development, deferred while
integrator duty stands); this is the concrete attack route. -/
theorem Section.HasExactOrder.pull_nsmul_ne_zero {P : E.Section} {N : ℕ} [NeZero N]
    (hN : NIsInvertible S N) (hkill : (N : ℤ) • P = 0) (h : P.HasExactOrder E N)
    (k : Type u) [Field k] [IsAlgClosed k] (t : Spec (.of k) ⟶ S)
    {a : ℕ} (ha0 : 0 < a) (haN : a < N) :
    (a : ℤ) • Point.pull E t P ≠ 0 := by sorry

/-- **Register box `T-D6c` (KM 1.4.4, (3)⟹(1) via (4))**: if on every geometric point
the multiples `aP`, `a = 1, …, N` are distinct, then the divisor `Σ [aP]` is finite
étale over `S` (discriminant invertible fibrewise ⟹ invertible) and the subgroup
property follows. KM (verbatim): *"It is finite etale over S if and only if its
discriminant … is invertible on S. This holds if and only if for all geometric
points Spec(k) → S, the Cartier divisor D_k … is finite etale over k"*. -/
theorem Section.hasExactOrder_of_geometric {P : E.Section} {N : ℕ} [NeZero N]
    (hN : NIsInvertible S N) (hkill : (N : ℤ) • P = 0)
    (h : ∀ (k : Type u) [Field k] [IsAlgClosed k] (t : Spec (.of k) ⟶ S),
      ∀ a : ℕ, 0 < a → a < N → (a : ℤ) • Point.pull E t P ≠ 0) :
    P.HasExactOrder E N := by sorry

/-- **(T-D6 = KM 1.4.4, (1) ⇔ (3))** For a point `P` killed by `N` (KM's standing
hypothesis; the `ℚ̄[ε]` counterexample of the 2026-07-06 adversarial pass shows it is
required) and `N` invertible on `S`: `P` has exact order `N` iff on every geometric
point the induced point has exact order `N` in the usual sense. Derived from the
`T-D6b`/`T-D6c` register boxes; the killing conjunct is `Point.pull_zsmul` + `hkill`. -/
theorem Section.hasExactOrder_iff_geometric {P : E.Section} {N : ℕ} [NeZero N]
    (hN : NIsInvertible S N) (hkill : (N : ℤ) • P = 0) :
    P.HasExactOrder E N ↔
      ∀ (k : Type u) [Field k] [IsAlgClosed k] (t : Spec (.of k) ⟶ S),
        (N : ℤ) • Point.pull E t P = 0 ∧
        ∀ a : ℕ, 0 < a → a < N → (a : ℤ) • Point.pull E t P ≠ 0 := by
  constructor
  · intro h k _ _ t
    refine ⟨?_, fun a ha0 haN ↦ h.pull_nsmul_ne_zero E hN hkill k t ha0 haN⟩
    rw [← Point.pull_zsmul, hkill, Point.pull_zero]
  · intro h
    exact Section.hasExactOrder_of_geometric E hN hkill fun k _ _ t ↦ (h k t).2

/-- **Register box `T-D7-bridge` (KM 1.4.4, (3)⟺(4))**: the divisor `Σ [aP]` is finite
étale over `S` iff on every geometric point the multiples are distinct. KM (verbatim):
*"It is finite etale over S if and only if its discriminant (determinant of the matrix
tr(eᵢeⱼ)…) is invertible on S. This holds if and only if for all geometric points
Spec(k) → S, the Cartier divisor D_k = Σ [aP_k] is finite etale over k, i.e., if and
only if (3) holds."* Discharge: trace-form/discriminant theory for the finite locally
free `orderDivisor` (T-B4 rank input) + fibre comparison. -/
theorem Section.orderDivisor_etale_iff_geometric {P : E.Section} {N : ℕ} [NeZero N]
    (hN : NIsInvertible S N) (hkill : (N : ℤ) • P = 0) :
    Etale ((P.orderDivisor E N).ideal.subschemeι ≫ E.π) ↔
      ∀ (k : Type u) [Field k] [IsAlgClosed k] (t : Spec (.of k) ⟶ S),
        ∀ a : ℕ, 0 < a → a < N → (a : ℤ) • Point.pull E t P ≠ 0 := by sorry

/-- **(T-D7 = KM 1.4.4, (1) ⇔ (4))** For a point `P` killed by `N` and `N` invertible
on `S`: `P` has exact order `N` iff the divisor `Σₐ [aP]` is finite étale over `S`.
Derived from T-D6 and the `T-D7-bridge` box. Register theorem (no code consumer): the étale
characterisation of exact order, kept as a trust-anchor. -/
theorem Section.hasExactOrder_iff_etale {P : E.Section} {N : ℕ} [NeZero N]
    (hN : NIsInvertible S N) (hkill : (N : ℤ) • P = 0) :
    P.HasExactOrder E N ↔
      Etale ((P.orderDivisor E N).ideal.subschemeι ≫ E.π) := by
  rw [Section.hasExactOrder_iff_geometric E hN hkill,
    Section.orderDivisor_etale_iff_geometric E hN hkill]
  constructor
  · intro h k _ _ t a ha0 haN
    exact (h k t).2 a ha0 haN
  · intro h k _ _ t
    refine ⟨?_, h k t⟩
    rw [← Point.pull_zsmul, hkill, Point.pull_zero]

end EllipticCurve

end ModularCurves
