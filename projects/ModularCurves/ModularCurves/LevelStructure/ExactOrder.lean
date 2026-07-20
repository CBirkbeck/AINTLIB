import ModularCurves.LevelStructure.CartierDivisor
import ModularCurves.EllipticCurve.Torsion
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.LinearAlgebra.TensorProduct.Basis

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
    (fun a : Fin N => ((((a : ℕ) : ℤ) + 1) • P : E.Point (𝟙 S)))

/-- **KM 1.4.1 — a point of exact order `N`** (Drinfeld): `P ∈ E(S)` has exact order `N`
if the degree-`N` relative effective Cartier divisor `[P] + [2P] + ⋯ + [NP]` is a subgroup
of `E/S`. -/
def Section.HasExactOrder (P : E.Section) (N : ℕ) [NeZero N] : Prop :=
  (P.orderDivisor E N).IsSubgroup E

/-- **Register box `BB-DELIGNE` (KM 1.4.2, cite [Oort–Tate])**, in the project's
subgroup-divisor encoding: a subgroup divisor of constant degree `N` is killed by `N`
— every point factoring through it is annihilated by `N`. KM (verbatim): *"a finite
locally free commutative group scheme of rank `N` is killed by `N`"*.

STATEMENT-PROTECTED (T-E4F1, board v10.343): this general-base form is the future
over-`ℤ` project (DeligneOrder Layer-B L1/L5/L6). All invertible-`N` consumers are
rerouted to the PROVEN `smul_eq_zero_of_factors_of_invertible`
(`LevelStructure/ExactOrderInvertible.lean`). -/
theorem _root_.ModularCurves.RelEffCartierDiv.IsSubgroup.smul_eq_zero_of_factors
    {D : RelEffCartierDiv E.π} (hD : D.IsSubgroup E) {N : ℕ} [NeZero N]
    (hdeg : ∀ s : S, D.degree s = N) {T : Scheme.{u}} (g : T ⟶ S) (Q : E.Point g)
    (hQ : ∃ h : T ⟶ D.ideal.subscheme, h ≫ D.ideal.subschemeι = Q.1) :
    (N : ℤ) • Q = 0 := by sorry

/-- `IdealSheafData.ideal` as a monoid homomorphism (products of ideal sheaves are
computed pointwise). -/
noncomputable def _root_.AlgebraicGeometry.Scheme.IdealSheafData.idealMonoidHom
    (X : Scheme.{u}) :
    X.IdealSheafData →* (∀ U : X.affineOpens, Ideal Γ(X, U.1)) where
  toFun := Scheme.IdealSheafData.ideal
  map_one' := by
    funext U
    simp [Scheme.IdealSheafData.one_eq_top, Scheme.IdealSheafData.ideal_top,
      Ideal.one_eq_top]
  map_mul' I J := Scheme.IdealSheafData.ideal_mul I J

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
  refine Finset.prod_congr rfl fun a _ => ?_
  have hsec : ((((a : ℕ) : ℤ) + 1) • Point.asSection E t (Point.pull E t P) :
      (E.baseChange t).Point (𝟙 T)) =
      Point.asSection E t (Point.pull E t ((((a : ℕ) : ℤ) + 1) • P)) :=
    ((Point.asSection_zsmul E t (((a : ℕ) : ℤ) + 1) (Point.pull E t P)).symm).trans
      (congrArg (Point.asSection E t)
        (Point.pull_zsmul E t ((((a : ℕ) : ℤ) + 1)) P).symm)
  have hker := RelEffCartierDiv.ker_sectionBaseChange
    (((((a : ℕ) : ℤ) + 1) • P : E.Point (𝟙 S))).1
    (((((a : ℕ) : ℤ) + 1) • P : E.Point (𝟙 S))).2 t
  exact ((congrArg (fun Q : (E.baseChange t).Point (𝟙 T) =>
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
  refine ⟨H.comap (Point.baseChangeEquiv E t g').toAddMonoidHom, fun Q => ?_⟩
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
  haveI hsep : IsSeparated E.π := inferInstance
  have hpos : IsSeparated E.π ∧ SmoothOfRelativeDimension 1 E.π := ⟨hsep, E.smooth⟩
  have hdeg : ∀ s, (P.orderDivisor E N).degree s = N := fun s =>
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
  haveI hPc : IsClosedImmersion P.1 := by
    have h1 : IsClosedImmersion (P.1 ≫ E.π) := by
      rw [P.2]
      infer_instance
    exact IsClosedImmersion.of_comp P.1 E.π
  refine ⟨P.1.toImage ≫ Scheme.IdealSheafData.inclusion hle, ?_⟩
  rw [Category.assoc, Scheme.IdealSheafData.inclusion_subschemeι]
  exact P.1.toImage_imageι

section JetAlgebra

/-! ### Private jet/binomial machinery for `T-D6b` (KM 1.4.4, (2)⟹(3))

The field-level core of the T-D6b box.  Over a field `k`, the local ring of the order
divisor at the origin is a *jet ring* `B ⧸ (f^lam) ≅ k[X]/(X^lam)` (`jetModel` below,
built on the coefficient-peeling lemma `jetAux_coeff_zero`); a subgroup structure on the
divisor then induces a comultiplication-type element `F ∈ k[X]/(X^lam) ⊗ k[X]/(X^lam)`
whose counit collapses are `x` and whose `lam`-th power vanishes — and the **binomial
core** `jetCore_binomial` shows this forces `(lam : k) = 0` (the coefficient of
`x ⊗ x^{lam-1}` in `F^lam = ((1⊗x) + G)^lam`, `G` of bidegree `≥ (1,·)`, is `lam`).
All declarations here are `private` implementation details of
`Section.HasExactOrder.pull_nsmul_ne_zero`. -/

open Polynomial
open scoped TensorProduct

variable {k : Type u} [Field k] {B : Type u} [CommRing B] [Algebra k B]

/-- Coefficient-peeling: if a polynomial expression `∑_{i<n} v i • f^i` in a
nonzerodivisor `f` generating the kernel of the `k`-point `χ` lies in `(f^n)`, all
coefficients vanish. -/
private theorem jetAux_coeff_zero (χ : B →ₐ[k] k) {f : B}
    (hf : f ∈ nonZeroDivisors B) (hker : RingHom.ker (χ : B →+* k) = Ideal.span {f}) :
    ∀ (n : ℕ) (v : ℕ → k),
      (∑ i ∈ Finset.range n, v i • f ^ i) ∈ Ideal.span {f ^ n} → ∀ i < n, v i = 0 := by
  have hχf : χ f = 0 := by
    have : f ∈ RingHom.ker (χ : B →+* k) := hker ▸ Ideal.subset_span rfl
    exact this
  intro n
  induction n with
  | zero => intro v _ i hi; omega
  | succ n ih =>
    intro v hv i hi
    -- split the sum as `v 0 • 1 + f * w`
    have hsplit : (∑ i ∈ Finset.range (n + 1), v i • f ^ i)
        = v 0 • (1 : B) + f * ∑ i ∈ Finset.range n, v (i + 1) • f ^ i := by
      rw [Finset.sum_range_succ' (fun i => v i • f ^ i), Finset.mul_sum]
      simp only [pow_zero, pow_succ]
      rw [add_comm]
      congr 1
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [mul_smul_comm, mul_comm f (f ^ j)]
    -- first: `v 0 = 0` by applying `χ`
    have hker_pow : Ideal.span {f ^ (n + 1)} ≤ RingHom.ker (χ : B →+* k) := by
      rw [Ideal.span_le, Set.singleton_subset_iff]
      simp [RingHom.mem_ker, map_pow, hχf]
    have hχv : χ (∑ i ∈ Finset.range (n + 1), v i • f ^ i) = 0 := hker_pow hv
    rw [hsplit, map_add, map_mul, hχf, zero_mul, add_zero, map_smul, map_one,
      smul_eq_mul, mul_one] at hχv
    -- hence `f * w ∈ (f^(n+1))`, cancel `f`
    have hfw : f * (∑ i ∈ Finset.range n, v (i + 1) • f ^ i) ∈ Ideal.span {f ^ (n + 1)} := by
      have := hv
      rw [hsplit, hχv, zero_smul, zero_add] at this
      exact this
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hfw
    have hcan : (∑ i ∈ Finset.range n, v (i + 1) • f ^ i) = c * f ^ n := by
      have h1 : f * (c * f ^ n) = f * (∑ i ∈ Finset.range n, v (i + 1) • f ^ i) := by
        rw [← hc, pow_succ]; ring
      exact ((mul_cancel_left_mem_nonZeroDivisors hf).mp h1).symm
    have hw : (∑ i ∈ Finset.range n, v (i + 1) • f ^ i) ∈ Ideal.span {f ^ n} :=
      hcan ▸ Ideal.mem_span_singleton'.mpr ⟨c, rfl⟩
    rcases i with - | j
    · exact hχv
    · exact ih (fun i => v (i + 1)) hw j (by omega)

/-- Division with remainder along `χ`: every element of `B` is a polynomial in `f`
modulo `(f^n)`. -/
private theorem jetAux_exists_poly (χ : B →ₐ[k] k) {f : B}
    (hker : RingHom.ker (χ : B →+* k) = Ideal.span {f}) (n : ℕ) (b : B) :
    ∃ p : Polynomial k, b - Polynomial.aeval f p ∈ Ideal.span {f ^ n} := by
  induction n with
  | zero => exact ⟨0, by simp [Ideal.span_singleton_one]⟩
  | succ n ih =>
    obtain ⟨p, hp⟩ := ih
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hp
    have hcχ : c - algebraMap k B (χ c) ∈ RingHom.ker (χ : B →+* k) := by
      simp [RingHom.mem_ker, map_sub]
    rw [hker] at hcχ
    obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.mp hcχ
    refine ⟨p + Polynomial.C (χ c) * Polynomial.X ^ n, ?_⟩
    rw [Ideal.mem_span_singleton']
    refine ⟨d, ?_⟩
    have : b - Polynomial.aeval f p = c * f ^ n := hc.symm
    rw [map_add, map_mul, Polynomial.aeval_C, map_pow, Polynomial.aeval_X]
    have hexp : b - (Polynomial.aeval f p + algebraMap k B (χ c) * f ^ n)
        = (c - algebraMap k B (χ c)) * f ^ n := by
      rw [sub_mul, ← this]; ring
    rw [hexp, ← hd, pow_succ]; ring

/-- The `k`-point of the jet ring `B ⧸ (f^lam)` induced by `χ`. -/
private def jetRes (χ : B →ₐ[k] k) {f : B}
    (hker : RingHom.ker (χ : B →+* k) = Ideal.span {f}) {lam : ℕ} (hlam : 1 ≤ lam)
    {I : Ideal B} (hI : I = Ideal.span {f ^ lam}) : (B ⧸ I) →ₐ[k] k :=
  Ideal.Quotient.liftₐ I χ (by
    intro a ha
    rw [hI, Ideal.mem_span_singleton'] at ha
    obtain ⟨c, rfl⟩ := ha
    have hχf : χ f = 0 := by
      have : f ∈ RingHom.ker (χ : B →+* k) := hker ▸ Ideal.subset_span rfl
      exact this
    rw [map_mul, map_pow, hχf, zero_pow (by omega), mul_zero])

private theorem jetRes_mk (χ : B →ₐ[k] k) {f : B}
    (hker : RingHom.ker (χ : B →+* k) = Ideal.span {f}) {lam : ℕ} (hlam : 1 ≤ lam)
    {I : Ideal B} (hI : I = Ideal.span {f ^ lam}) (b : B) :
    jetRes χ hker hlam hI (Ideal.Quotient.mk I b) = χ b := rfl

private theorem jetAux_aeval_mk {I : Ideal B} (f : B) (p : Polynomial k) :
    Polynomial.aeval (Ideal.Quotient.mk I f) p
      = Ideal.Quotient.mk I (Polynomial.aeval f p) := by
  have := Polynomial.aeval_algHom_apply (Ideal.Quotient.mkₐ k I) f p
  simpa [Ideal.Quotient.mkₐ_eq_mk] using this

private theorem jetAux_eval₂_ofId {A : Type u} [CommRing A] [Algebra k A] (x : A)
    (p : Polynomial k) :
    Polynomial.eval₂ (↑(Algebra.ofId k A) : k →+* A) x p = Polynomial.aeval x p := by
  rw [Polynomial.aeval_def]
  rfl

/-- The jet comparison hom `k[X]/(X^lam) → B ⧸ (f^lam)`, `X ↦ f`. -/
private noncomputable def jetHom (f : B) {lam : ℕ} {I : Ideal B}
    (hI : I = Ideal.span {f ^ lam}) :
    AdjoinRoot (Polynomial.X ^ lam : Polynomial k) →ₐ[k] (B ⧸ I) :=
  AdjoinRoot.liftAlgHom _ (Algebra.ofId k (B ⧸ I)) (Ideal.Quotient.mk I f) (by
    rw [jetAux_eval₂_ofId, map_pow, Polynomial.aeval_X, ← map_pow,
      Ideal.Quotient.eq_zero_iff_mem, hI]
    exact Ideal.subset_span rfl)

private theorem jetHom_mk (f : B) {lam : ℕ} {I : Ideal B}
    (hI : I = Ideal.span {f ^ lam}) (p : Polynomial k) :
    jetHom f hI (AdjoinRoot.mk (Polynomial.X ^ lam : Polynomial k) p)
      = Ideal.Quotient.mk I (Polynomial.aeval f p) := by
  rw [jetHom, AdjoinRoot.liftAlgHom_mk, jetAux_eval₂_ofId, jetAux_aeval_mk]

private theorem jetHom_root (f : B) {lam : ℕ} {I : Ideal B}
    (hI : I = Ideal.span {f ^ lam}) :
    jetHom f hI (AdjoinRoot.root (Polynomial.X ^ lam : Polynomial k))
      = Ideal.Quotient.mk I f := by
  rw [jetHom, AdjoinRoot.liftAlgHom_root]

private theorem jetHom_bijective (χ : B →ₐ[k] k) {f : B}
    (hf : f ∈ nonZeroDivisors B) (hker : RingHom.ker (χ : B →+* k) = Ideal.span {f})
    {lam : ℕ} (hlam : 1 ≤ lam) {I : Ideal B} (hI : I = Ideal.span {f ^ lam}) :
    Function.Bijective (jetHom (k := k) f hI) := by
  constructor
  · -- injectivity
    intro x y hxy
    obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective x
    obtain ⟨q, rfl⟩ := AdjoinRoot.mk_surjective y
    rw [jetHom_mk, jetHom_mk, ← sub_eq_zero, ← map_sub, ← map_sub,
      Ideal.Quotient.eq_zero_iff_mem] at hxy
    rw [← sub_eq_zero, ← map_sub, AdjoinRoot.mk_eq_zero]
    set r := p - q with hr
    -- reduce `r` mod `X^lam`; the remainder also evaluates into `I`
    set s := r %ₘ Polynomial.X ^ lam with hs
    have hdm := Polynomial.modByMonic_add_div r (Polynomial.X ^ lam)
    have hsr : Polynomial.aeval f s ∈ I := by
      have heq : Polynomial.aeval f s = Polynomial.aeval f r
          - f ^ lam * Polynomial.aeval f (r /ₘ Polynomial.X ^ lam) := by
        have h2 := congrArg (Polynomial.aeval f) hdm
        rw [map_add, map_mul, map_pow, Polynomial.aeval_X] at h2
        rw [← h2]; ring
      rw [heq]
      exact I.sub_mem hxy (hI ▸ Ideal.mem_span_singleton'.mpr ⟨_, mul_comm _ _⟩)
    -- degree bound for the remainder
    have hdeg : s.natDegree < lam := by
      rcases eq_or_ne s 0 with h0 | h0
      · rw [h0]
        simp only [Polynomial.natDegree_zero]
        omega
      · rw [Polynomial.natDegree_lt_iff_degree_lt h0]
        simpa [Polynomial.degree_X_pow] using
          Polynomial.degree_modByMonic_lt r (Polynomial.monic_X_pow (R := k) (n := lam))
    -- all coefficients of the remainder vanish
    have hcoeff : ∀ i < lam, s.coeff i = 0 := by
      have hsum : Polynomial.aeval f s = ∑ i ∈ Finset.range lam, s.coeff i • f ^ i :=
        Polynomial.aeval_eq_sum_range' hdeg f
      exact jetAux_coeff_zero χ hf hker lam (fun i => s.coeff i)
        (by rw [← hsum, ← hI]; exact hsr)
    have hs0 : s = 0 := by
      ext i
      rcases lt_or_ge i lam with hi | hi
      · simpa using hcoeff i hi
      · simpa using Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_lt_of_le hdeg hi)
    exact (Polynomial.modByMonic_eq_zero_iff_dvd
      (Polynomial.monic_X_pow (R := k) (n := lam))).mp hs0
  · -- surjectivity
    intro b
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
    obtain ⟨p, hp⟩ := jetAux_exists_poly χ hker lam b
    refine ⟨AdjoinRoot.mk (Polynomial.X ^ lam : Polynomial k) p, ?_⟩
    rw [jetHom_mk]
    have h1 : Ideal.Quotient.mk I (b - Polynomial.aeval f p) = 0 := by
      rw [Ideal.Quotient.eq_zero_iff_mem, hI]; exact hI ▸ hp
    rw [map_sub, sub_eq_zero] at h1
    exact h1.symm

/-- The jet model: the quotient `B ⧸ (f^lam)` is the truncated polynomial ring
`k[X]/(X^lam)`, via `X ↦ f`. -/
private noncomputable def jetModel (χ : B →ₐ[k] k) {f : B}
    (hf : f ∈ nonZeroDivisors B) (hker : RingHom.ker (χ : B →+* k) = Ideal.span {f})
    {lam : ℕ} (hlam : 1 ≤ lam) {I : Ideal B} (hI : I = Ideal.span {f ^ lam}) :
    AdjoinRoot (Polynomial.X ^ lam : Polynomial k) ≃ₐ[k] (B ⧸ I) :=
  AlgEquiv.ofBijective (jetHom f hI) (jetHom_bijective χ hf hker hlam hI)

private theorem jetModel_apply (χ : B →ₐ[k] k) {f : B}
    (hf : f ∈ nonZeroDivisors B) (hker : RingHom.ker (χ : B →+* k) = Ideal.span {f})
    {lam : ℕ} (hlam : 1 ≤ lam) {I : Ideal B} (hI : I = Ideal.span {f ^ lam})
    (x : AdjoinRoot (Polynomial.X ^ lam : Polynomial k)) :
    jetModel χ hf hker hlam hI x = jetHom f hI x := rfl

private theorem jetModel_root (χ : B →ₐ[k] k) {f : B}
    (hf : f ∈ nonZeroDivisors B) (hker : RingHom.ker (χ : B →+* k) = Ideal.span {f})
    {lam : ℕ} (hlam : 1 ≤ lam) {I : Ideal B} (hI : I = Ideal.span {f ^ lam}) :
    jetModel χ hf hker hlam hI (AdjoinRoot.root (Polynomial.X ^ lam : Polynomial k))
      = Ideal.Quotient.mk I f := by
  rw [jetModel_apply, jetHom_root]

/-- The evaluation-at-zero point of the truncated polynomial ring `k[X]/(X^lam)`. -/
private noncomputable def jetEps (k : Type u) [Field k] (lam : ℕ) [NeZero lam] :
    AdjoinRoot (Polynomial.X ^ lam : Polynomial k) →ₐ[k] k :=
  AdjoinRoot.liftAlgHom _ (Algebra.ofId k k) 0 (by
    rw [jetAux_eval₂_ofId, map_pow, Polynomial.aeval_X, zero_pow (NeZero.ne lam)])

private theorem jetEps_root (k : Type u) [Field k] (lam : ℕ) [NeZero lam] :
    jetEps k lam (AdjoinRoot.root _) = 0 := by
  rw [jetEps, AdjoinRoot.liftAlgHom_root]

/-- **The binomial core.** In `R₀ ⊗ R₀` for `R₀ = k[X]/(X^lam)`, `lam ≥ 2`: an element
`F` with both counit-collapses equal to `x = X mod X^lam` and with `F ^ lam = 0` forces
`(lam : k) = 0`. (This is the co-group obstruction: `F ≡ x⊗1 + 1⊗x` modulo bidegree
`≥ (1,1)`, and the coefficient of `x ⊗ x^{lam-1}` in `F^lam` is `lam`.) -/
private theorem jetCore_binomial {k : Type u} [Field k] {lam : ℕ} [NeZero lam]
    (hlam : 2 ≤ lam)
    (F : (AdjoinRoot (Polynomial.X ^ lam : Polynomial k)) ⊗[k]
      (AdjoinRoot (Polynomial.X ^ lam : Polynomial k)))
    (h1 : Algebra.TensorProduct.productMap
        (AlgHom.id k (AdjoinRoot (Polynomial.X ^ lam : Polynomial k)))
        ((Algebra.ofId k (AdjoinRoot (Polynomial.X ^ lam : Polynomial k))).comp
          (jetEps k lam)) F = AdjoinRoot.root _)
    (h2 : Algebra.TensorProduct.productMap
        ((Algebra.ofId k (AdjoinRoot (Polynomial.X ^ lam : Polynomial k))).comp
          (jetEps k lam))
        (AlgHom.id k (AdjoinRoot (Polynomial.X ^ lam : Polynomial k))) F
        = AdjoinRoot.root _)
    (hpow : F ^ lam = 0) : (lam : k) = 0 := by
  set R0 := AdjoinRoot (Polynomial.X ^ lam : Polynomial k) with hR0
  set x0 : R0 := AdjoinRoot.root _ with hx0
  set ε : R0 →ₐ[k] k := jetEps k lam with hε
  -- the power basis, reindexed to `Fin lam`
  have hmon : (Polynomial.X ^ lam : Polynomial k).Monic := Polynomial.monic_X_pow lam
  set pb := AdjoinRoot.powerBasis' hmon with hpb
  have hdim : pb.dim = lam := by
    rw [hpb, AdjoinRoot.powerBasis'_dim, Polynomial.natDegree_X_pow]
  set bR : Module.Basis (Fin lam) k R0 := pb.basis.reindex (finCongr hdim) with hbR
  have bR_apply : ∀ i : Fin lam, bR i = x0 ^ (i : ℕ) := by
    intro i
    rw [hbR, Module.Basis.reindex_apply, PowerBasis.coe_basis]
    have hgen : pb.gen = x0 := by rw [hpb, hx0]; exact AdjoinRoot.powerBasis'_gen hmon
    rw [hgen]
    congr 1
  -- root powers at and beyond `lam` vanish
  have hxlam : x0 ^ lam = 0 := by
    have h := AdjoinRoot.eval₂_root (Polynomial.X ^ lam : Polynomial k)
    rwa [Polynomial.eval₂_X_pow] at h
  have hxge : ∀ n, lam ≤ n → x0 ^ n = 0 := by
    intro n hn
    rw [show n = lam + (n - lam) by omega, pow_add, hxlam, zero_mul]
  -- ε on root powers
  have hεpow : ∀ j : ℕ, ε (x0 ^ j) = if j = 0 then 1 else 0 := by
    intro j
    rw [map_pow, hε, hx0, jetEps_root]
    rcases eq_or_ne j 0 with rfl | hj
    · simp
    · simp [zero_pow hj, hj]
  -- the tensor basis
  set bT : Module.Basis (Fin lam × Fin lam) k (R0 ⊗[k] R0) := bR.tensorProduct bR with hbT
  have bT_apply : ∀ p : Fin lam × Fin lam,
      bT p = (x0 ^ (p.1 : ℕ)) ⊗ₜ[k] (x0 ^ (p.2 : ℕ)) := by
    rintro ⟨i, j⟩
    rw [hbT, Module.Basis.tensorProduct_apply, bR_apply, bR_apply]
  -- distinguished indices
  have h0lt : 0 < lam := by omega
  have h1lt : 1 < lam := by omega
  set i0 : Fin lam := ⟨0, h0lt⟩ with hi0
  set i1 : Fin lam := ⟨1, h1lt⟩ with hi1
  set iL : Fin lam := ⟨lam - 1, by omega⟩ with hiL
  have hi0i1 : i0 ≠ i1 := by
    intro h
    exact absurd (congrArg Fin.val h) (by simp [hi0, hi1])
  -- the two collapse maps
  set φ₁ := Algebra.TensorProduct.productMap (AlgHom.id k R0)
    ((Algebra.ofId k R0).comp ε) with hφ₁
  set φ₂ := Algebra.TensorProduct.productMap ((Algebra.ofId k R0).comp ε)
    (AlgHom.id k R0) with hφ₂
  -- coordinates of the collapse maps on the tensor basis
  have hφ₁b : ∀ p : Fin lam × Fin lam,
      φ₁ (bT p) = if p.2 = i0 then x0 ^ (p.1 : ℕ) else 0 := by
    rintro ⟨i, j⟩
    rw [bT_apply, hφ₁, Algebra.TensorProduct.productMap_apply_tmul]
    simp only [AlgHom.coe_id, id_eq, AlgHom.coe_comp, Function.comp_apply]
    rw [hεpow]
    rcases eq_or_ne j i0 with rfl | hj
    · rw [if_pos rfl, if_pos rfl, map_one, mul_one]
    · have hj' : (j : ℕ) ≠ 0 := fun h => hj (Fin.ext h)
      rw [if_neg hj', if_neg hj, map_zero, mul_zero]
  have hφ₂b : ∀ p : Fin lam × Fin lam,
      φ₂ (bT p) = if p.1 = i0 then x0 ^ (p.2 : ℕ) else 0 := by
    rintro ⟨i, j⟩
    rw [bT_apply, hφ₂, Algebra.TensorProduct.productMap_apply_tmul]
    simp only [AlgHom.coe_id, id_eq, AlgHom.coe_comp, Function.comp_apply]
    rw [hεpow]
    rcases eq_or_ne i i0 with rfl | hi
    · rw [if_pos rfl, if_pos rfl, map_one, one_mul]
    · have hi' : (i : ℕ) ≠ 0 := fun h => hi (Fin.ext h)
      rw [if_neg hi', if_neg hi, map_zero, zero_mul]
  have hx0b : x0 = bR i1 := by rw [bR_apply, hi1, pow_one]
  -- component-wise (projection-free) variants for use after destructuring
  have bT_apply' : ∀ i j : Fin lam, bT (i, j) = (x0 ^ (i : ℕ)) ⊗ₜ[k] (x0 ^ (j : ℕ)) :=
    fun i j => bT_apply (i, j)
  have hφ₁b' : ∀ i j : Fin lam, φ₁ (bT (i, j)) = if j = i0 then x0 ^ (i : ℕ) else 0 :=
    fun i j => hφ₁b (i, j)
  have hφ₂b' : ∀ i j : Fin lam, φ₂ (bT (i, j)) = if i = i0 then x0 ^ (j : ℕ) else 0 :=
    fun i j => hφ₂b (i, j)
  -- coordinate extraction: `repr F (i, 0) = δ_{i,1}` and `repr F (0, j) = δ_{j,1}`
  have key1 : ∀ i : Fin lam, bT.repr F (i, i0) = if i = i1 then 1 else 0 := by
    intro i
    have hcomp : (bR.coord i).comp φ₁.toLinearMap = bT.coord (i, i0) := by
      apply bT.ext
      rintro ⟨i', j'⟩
      simp only [LinearMap.coe_comp, Function.comp_apply, AlgHom.toLinearMap_apply,
        Module.Basis.coord_apply]
      rw [hφ₁b' i' j', Module.Basis.repr_self_apply]
      rcases eq_or_ne j' i0 with rfl | hj'
      · rw [if_pos rfl, ← bR_apply i', Module.Basis.repr_self_apply]
        rcases eq_or_ne i' i with rfl | hii
        · rw [if_pos rfl, if_pos rfl]
        · rw [if_neg hii, if_neg (show ¬((i', i0) = (i, i0)) by
            simp [Prod.ext_iff, hii])]
      · rw [if_neg hj', map_zero, Finsupp.coe_zero, Pi.zero_apply,
          if_neg (show ¬((i', j') = (i, i0)) by simp [Prod.ext_iff, hj'])]
    have := congrArg (fun L : (R0 ⊗[k] R0) →ₗ[k] k => L F) hcomp
    simp only [LinearMap.coe_comp, Function.comp_apply, AlgHom.toLinearMap_apply,
      Module.Basis.coord_apply] at this
    rw [← this, h1, hx0b, Module.Basis.repr_self_apply]
    rcases eq_or_ne i i1 with rfl | hii
    · rfl
    · rw [if_neg (Ne.symm hii), if_neg hii]
  have key2 : ∀ j : Fin lam, bT.repr F (i0, j) = if j = i1 then 1 else 0 := by
    intro j
    have hcomp : (bR.coord j).comp φ₂.toLinearMap = bT.coord (i0, j) := by
      apply bT.ext
      rintro ⟨i', j'⟩
      simp only [LinearMap.coe_comp, Function.comp_apply, AlgHom.toLinearMap_apply,
        Module.Basis.coord_apply]
      rw [hφ₂b' i' j', Module.Basis.repr_self_apply]
      rcases eq_or_ne i' i0 with rfl | hi'
      · rw [if_pos rfl, ← bR_apply j', Module.Basis.repr_self_apply]
        rcases eq_or_ne j' j with rfl | hjj
        · rw [if_pos rfl, if_pos rfl]
        · rw [if_neg hjj, if_neg (show ¬((i0, j') = (i0, j)) by
            simp [Prod.ext_iff, hjj])]
      · rw [if_neg hi', map_zero, Finsupp.coe_zero, Pi.zero_apply,
          if_neg (show ¬((i', j') = (i0, j)) by simp [Prod.ext_iff, hi'])]
    have := congrArg (fun L : (R0 ⊗[k] R0) →ₗ[k] k => L F) hcomp
    simp only [LinearMap.coe_comp, Function.comp_apply, AlgHom.toLinearMap_apply,
      Module.Basis.coord_apply] at this
    rw [← this, h2, hx0b, Module.Basis.repr_self_apply]
    rcases eq_or_ne j i1 with rfl | hjj
    · rfl
    · rw [if_neg (Ne.symm hjj), if_neg hjj]
  -- the "first-coordinate ≥ c" filtration
  set V : ℕ → Submodule k (R0 ⊗[k] R0) :=
    fun c => Submodule.span k (bT '' {p | c ≤ (p.1 : ℕ)}) with hV
  have memV_of : ∀ (c : ℕ) (y : R0 ⊗[k] R0),
      (∀ p : Fin lam × Fin lam, (p.1 : ℕ) < c → bT.repr y p = 0) → y ∈ V c := by
    intro c y hy
    have hexp : (∑ p : Fin lam × Fin lam, bT.repr y p • bT p) = y := bT.sum_repr y
    rw [← hexp]
    refine Submodule.sum_mem _ fun p _ => ?_
    rcases lt_or_ge (p.1 : ℕ) c with hp | hp
    · rw [hy p hp, zero_smul]
      exact Submodule.zero_mem _
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨p, hp, rfl⟩)
  have reprV : ∀ (c : ℕ) (y : R0 ⊗[k] R0), y ∈ V c →
      ∀ p : Fin lam × Fin lam, (p.1 : ℕ) < c → bT.repr y p = 0 := by
    intro c y hy
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hy
    · rintro _ ⟨q, hq, rfl⟩ p hp
      rw [bT.repr_self, Finsupp.single_apply]
      have : q ≠ p := by
        intro h
        subst h
        exact absurd hq (by simpa using hp)
      simp [this]
    · intro p _
      simp
    · intro y z _ _ hy hz p hp
      rw [map_add, Finsupp.add_apply, hy p hp, hz p hp, add_zero]
    · intro a y _ hy p hp
      rw [map_smul, Finsupp.smul_apply, hy p hp, smul_zero]
  -- multiplicativity, monotonicity, and powers of the filtration
  have hVmul : ∀ (a b : ℕ) (y z : R0 ⊗[k] R0), y ∈ V a → z ∈ V b → y * z ∈ V (a + b) := by
    intro a b y z hy hz
    have hle : Submodule.span k (bT '' {p | a ≤ (p.1 : ℕ)}) *
        Submodule.span k (bT '' {p | b ≤ (p.1 : ℕ)}) ≤
        Submodule.span k (bT '' {p | a + b ≤ (p.1 : ℕ)}) := by
      rw [Submodule.span_mul_span]
      refine Submodule.span_le.mpr ?_
      rintro w ⟨_, ⟨p, hp, rfl⟩, _, ⟨q, hq, rfl⟩, rfl⟩
      show bT p * bT q ∈ Submodule.span k (bT '' {p | a + b ≤ (p.1 : ℕ)})
      rw [bT_apply, bT_apply, Algebra.TensorProduct.tmul_mul_tmul, ← pow_add, ← pow_add]
      rcases le_or_gt lam ((p.1 : ℕ) + (q.1 : ℕ)) with hbig | hsmall
      · rw [hxge _ hbig, TensorProduct.zero_tmul]
        exact Submodule.zero_mem _
      rcases le_or_gt lam ((p.2 : ℕ) + (q.2 : ℕ)) with hbig2 | hsmall2
      · rw [hxge _ hbig2, TensorProduct.tmul_zero]
        exact Submodule.zero_mem _
      refine Submodule.subset_span ⟨(⟨(p.1 : ℕ) + (q.1 : ℕ), hsmall⟩,
        ⟨(p.2 : ℕ) + (q.2 : ℕ), hsmall2⟩), ?_, ?_⟩
      · simp only [Set.mem_setOf_eq] at hp hq ⊢
        omega
      · rw [bT_apply]
    exact hle (Submodule.mul_mem_mul hy hz)
  have hVtop : ∀ y : R0 ⊗[k] R0, y ∈ V 0 := fun y => memV_of 0 y (fun p hp => by omega)
  have hVmono : ∀ {c c' : ℕ}, c' ≤ c → V c ≤ V c' := by
    intro c c' hcc
    exact Submodule.span_mono (Set.image_mono (fun p hp => le_trans hcc hp))
  have hGpow : ∀ (G : R0 ⊗[k] R0), G ∈ V 1 → ∀ n : ℕ, G ^ n ∈ V n := by
    intro G hG n
    induction n with
    | zero => simpa using hVtop 1
    | succ n ih =>
      rw [pow_succ]
      exact hVmul n 1 (G ^ n) G ih hG
  -- decompose `F = (1 ⊗ x) + G` with `G` in the first-degree-≥-1 part
  set G := F - bT (i0, i1) with hG
  have hGmem : G ∈ V 1 := by
    refine memV_of 1 G fun p hp => ?_
    obtain ⟨pi, pj⟩ := p
    have hp1 : pi = i0 := Fin.ext (Nat.lt_one_iff.mp hp)
    subst hp1
    rw [hG, map_sub, Finsupp.sub_apply, key2 pj, Module.Basis.repr_self_apply]
    rcases eq_or_ne pj i1 with rfl | hj
    · rw [if_pos rfl, if_pos rfl, sub_self]
    · rw [if_neg hj, if_neg (show ¬((i0, i1) = (i0, pj)) by
        simp [Prod.ext_iff, Ne.symm hj]), sub_zero]
  -- ==== the binomial extraction ====
  -- the coefficient functional at `x ⊗ x^{lam-1}`
  set cf : (R0 ⊗[k] R0) →ₗ[k] k := bT.coord (i1, iL) with hcf
  -- `u := 1 ⊗ x`, and its `lam-1`-st power `1 ⊗ x^{lam-1}`
  have hu : bT (i0, i1) = (1 : R0) ⊗ₜ[k] x0 := by
    rw [bT_apply' i0 i1]
    show (x0 ^ (0 : ℕ)) ⊗ₜ[k] (x0 ^ (1 : ℕ)) = _
    rw [pow_zero, pow_one]
  have huL : bT (i0, i1) ^ (lam - 1) = bT (i0, iL) := by
    have e0 : (i0 : ℕ) = 0 := by rw [hi0]
    have eL : (iL : ℕ) = lam - 1 := by rw [hiL]
    rw [hu, Algebra.TensorProduct.tmul_pow, one_pow, bT_apply' i0 iL, e0, eL, pow_zero]
  -- multiplication by `1 ⊗ x^{lam-1}` on the tensor basis
  have hmulL : ∀ a b : Fin lam,
      bT (i0, iL) * bT (a, b) = if b = i0 then bT (a, iL) else 0 := by
    intro a b
    rw [bT_apply' i0 iL, bT_apply' a b, Algebra.TensorProduct.tmul_mul_tmul,
      ← pow_add, ← pow_add]
    rcases eq_or_ne b i0 with rfl | hb
    · rw [if_pos rfl, bT_apply' a iL]
      show (x0 ^ ((0 : ℕ) + (a : ℕ))) ⊗ₜ[k] (x0 ^ (lam - 1 + (0 : ℕ))) = _
      rw [Nat.zero_add, Nat.add_zero]
    · rw [if_neg hb]
      have hb' : 1 ≤ (b : ℕ) := Nat.one_le_iff_ne_zero.mpr (fun h => hb (Fin.ext h))
      have hge : lam ≤ (iL : ℕ) + (b : ℕ) := by
        show lam ≤ lam - 1 + (b : ℕ)
        omega
      rw [hxge _ hge, TensorProduct.tmul_zero]
  -- the key coefficient: `cf ((1⊗x)^(lam-1) * G) = 1`
  have hterm_key : cf (bT (i0, i1) ^ (lam - 1) * G) = 1 := by
    have hexpand : (∑ p : Fin lam × Fin lam, bT.repr G p • bT p) = G := bT.sum_repr G
    rw [huL, ← hexpand, Finset.mul_sum]
    have hsum : ∀ p : Fin lam × Fin lam,
        bT (i0, iL) * (bT.repr G p • bT p) = bT.repr G p • (bT (i0, iL) * bT p) :=
      fun p => mul_smul_comm _ _ _
    rw [Finset.sum_congr rfl fun p _ => hsum p, map_sum]
    have hval : ∀ p : Fin lam × Fin lam,
        cf (bT.repr G p • (bT (i0, iL) * bT p)) =
          (if p = (i1, i0) then bT.repr G p else 0) := by
      rintro ⟨a, b⟩
      rw [hmulL a b]
      rcases eq_or_ne b i0 with rfl | hb
      · rw [if_pos rfl, map_smul, hcf, Module.Basis.coord_apply,
          Module.Basis.repr_self_apply]
        rcases eq_or_ne a i1 with rfl | ha
        · rw [if_pos rfl, if_pos rfl, smul_eq_mul, mul_one]
        · rw [if_neg (show ¬((a, iL) = (i1, iL)) by simp [Prod.ext_iff, ha]),
            if_neg (show ¬(((a : Fin lam), i0) = (i1, i0)) by
              simp [Prod.ext_iff, ha]), smul_zero]
      · rw [if_neg hb, smul_zero, map_zero,
          if_neg (show ¬(((a : Fin lam), b) = (i1, i0)) by simp [Prod.ext_iff, hb])]
    rw [Finset.sum_congr rfl fun p _ => hval p,
      Finset.sum_ite_eq_of_mem' Finset.univ ((i1, i0) : Fin lam × Fin lam)
        (fun p => bT.repr G p) (Finset.mem_univ _)]
    rw [hG, map_sub, Finsupp.sub_apply, key1 i1, if_pos rfl,
      Module.Basis.repr_self_apply,
      if_neg (show ¬((i0, i1) = (i1, i0)) by simp [Prod.ext_iff, hi0i1]), sub_zero]
  -- terms of the binomial expansion with `G`-degree ≥ 2 have no `x ⊗ x^{lam-1}` part
  have hterm_hi : ∀ m : ℕ, m + 2 ≤ lam →
      cf (bT (i0, i1) ^ m * G ^ (lam - m) * ((lam.choose m : ℕ) : R0 ⊗[k] R0)) = 0 := by
    intro m hm
    have hmem : bT (i0, i1) ^ m * G ^ (lam - m) * ((lam.choose m : ℕ) : R0 ⊗[k] R0) ∈
        V (0 + (lam - m) + 0) :=
      hVmul _ 0 _ _ (hVmul 0 _ _ _ (hVtop _) (hGpow G hGmem _)) (hVtop _)
    have h2mem : bT (i0, i1) ^ m * G ^ (lam - m) * ((lam.choose m : ℕ) : R0 ⊗[k] R0) ∈
        V 2 := hVmono (by omega) hmem
    have := reprV 2 _ h2mem (i1, iL) (by show (1 : ℕ) < 2; omega)
    rw [hcf, Module.Basis.coord_apply]
    exact this
  -- assembly: apply `cf` to `0 = F^lam = ((1⊗x) + G)^lam`
  have hFdecomp : F = bT (i0, i1) + G := by rw [hG]; ring
  have h0 : (0 : k) = cf (F ^ lam) := by rw [hpow, map_zero]
  rw [hFdecomp, add_pow, map_sum] at h0
  have hsingle : (∑ m ∈ Finset.range (lam + 1),
      cf (bT (i0, i1) ^ m * G ^ (lam - m) * ((lam.choose m : ℕ) : R0 ⊗[k] R0)))
      = (lam : k) := by
    have hz : ∀ m ∈ Finset.range (lam + 1), m ≠ lam - 1 →
        cf (bT (i0, i1) ^ m * G ^ (lam - m) * ((lam.choose m : ℕ) : R0 ⊗[k] R0))
          = 0 := by
      intro m hm hne
      rcases eq_or_ne m lam with heq | hml
      · have hulam : bT (i0, i1) ^ lam = 0 := by
          rw [hu, Algebra.TensorProduct.tmul_pow, one_pow, hxlam,
            TensorProduct.tmul_zero]
        rw [heq, Nat.sub_self, pow_zero, mul_one, hulam, zero_mul, map_zero]
      · have hm2 : m + 2 ≤ lam := by
          have := Finset.mem_range.mp hm
          omega
        exact hterm_hi m hm2
    rw [Finset.sum_eq_single_of_mem (lam - 1)
      (Finset.mem_range.mpr (by omega)) hz]
    have hsub : lam - (lam - 1) = 1 := by omega
    have hC : lam.choose (lam - 1) = lam := by
      have h := Nat.choose_symm (show lam - 1 ≤ lam by omega)
      rw [show lam - (lam - 1) = 1 by omega] at h
      rw [← h, Nat.choose_one_right]
    have hcast : bT (i0, i1) ^ (lam - 1) * G ^ (lam - (lam - 1)) *
        ((lam.choose (lam - 1) : ℕ) : R0 ⊗[k] R0)
        = (lam.choose (lam - 1) : ℕ) • (bT (i0, i1) ^ (lam - 1) * G) := by
      rw [hsub, pow_one, nsmul_eq_mul]
      ring
    rw [hcast, map_nsmul, hterm_key, nsmul_eq_mul, mul_one, hC]
  rw [hsingle] at h0
  exact h0.symm
end JetAlgebra

open scoped TensorProduct

/-- **Geometry→algebra bridge for the `T-D6b` register box (KM 1.4.4, (2)⟹(3)) — the
sole remaining geometric gap.** Suppose the exact-order-`N` point `P` acquires a proper
relation `a • P_k = 0` (`0 < a < N`) over an algebraically closed fibre `k` with `N`
invertible. Then the order divisor `D_k = Σ_{b=1}^N [bP_k]` fails to be reduced: it has a
fat point of some length `lam ≥ 2`, and by homogeneity of the subgroup scheme (all local
lengths agree under translation) `lam ∣ N`. The local ring of `D_k` at that fat point is
the jet ring `𝒪/(f^lam) ≅ k[X]/(X^lam)` (`jetModel`), on which the subgroup comultiplication
restricts to an element `F ∈ k[X]/(X^lam) ⊗ k[X]/(X^lam)` whose two counit-collapses are the
root `x = X mod X^lam` (co-unit axioms) and which satisfies `F^lam = 0` (image of `x^lam = 0`
under the comultiplication algebra map). Feeding this jet data to `jetCore_binomial` yields
`(lam : k) = 0`, and with `lam ∣ N` this contradicts `N`'s invertibility — this is how
`Section.HasExactOrder.pull_nsmul_ne_zero` closes.

DISCHARGE RECIPE (the residual scheme-theory, staged into named sub-steps):
  (1) `P_k := Point.pull E t P` has exact order `N` over `Spec k` — from
      `Section.HasExactOrder.baseChange` (already proven) + `Section.orderDivisor_baseChange`.
  (2) `a • P_k = 0` with `0 < a < N` ⟹ the sections `{b • P_k : 1 ≤ b ≤ N}` are NOT
      pairwise distinct, so the effective divisor `D_k` is non-reduced at some geometric
      point; localise the structure sheaf there.
  (3) `E_k` is a smooth curve over the field `k`, so its local ring `𝒪` at that point is a
      DVR with uniformiser `f`; the ideal of `D_k` is `(f^lam)` with `lam ≥ 2` the local
      multiplicity. Use `jetModel χ hf hker hlam hI : k[X]/(X^lam) ≃ₐ[k] 𝒪/(f^lam)`.
  (4) Homogeneity: `D_k` is killed by `N` (`RelEffCartierDiv.IsSubgroup.smul_eq_zero_of_factors`,
      the `BB-DELIGNE` box) hence a subgroup scheme; translation by its `k`-points is a scheme
      automorphism permuting the local lengths transitively, so every point has length `lam`
      and `N = (#points) · lam`, giving `lam ∣ N`.
  (5) Transport the subgroup comultiplication `D_k → D_k ×_k D_k` through `jetModel ⊗ jetModel`
      to obtain `F`, and read off the two counit-collapse identities (`h1`/`h2`) from the
      co-unit axioms and `F^lam = 0` from `x^lam = 0`.
The pure-algebra endpoint (5)→conclusion is `jetCore_binomial` (PROVEN, above). Substrate
available: `Torsion.torsionπ_etale` (T-B5′), `ForMathlib/EtaleSectionsCount`,
`TorsionFibre.torsionPointsEquiv`.

STATEMENT-PROTECTED (T-E4F2, board v10.343): all invertible-`N` consumers are rerouted
past this jet keystone to `Section.HasExactOrder.pull_nsmul_ne_zero_of_invertible`
(`LevelStructure/ExactOrderInvertible.lean`, the étale/count route of KM 1.4.4(3));
this box remains as the future char-`p`/over-`ℤ` work. -/
private theorem Section.HasExactOrder.pull_nsmul_jetData {P : E.Section} {N : ℕ} [NeZero N]
    (hN : NIsInvertible S N) (hkill : (N : ℤ) • P = 0) (h : P.HasExactOrder E N)
    (k : Type u) [Field k] [IsAlgClosed k] (t : Spec (.of k) ⟶ S)
    {a : ℕ} (ha0 : 0 < a) (haN : a < N) (hzero : (a : ℤ) • Point.pull E t P = 0) :
    ∃ (lam : ℕ) (_ : NeZero lam), 2 ≤ lam ∧ lam ∣ N ∧
      ∃ F : (AdjoinRoot (Polynomial.X ^ lam : Polynomial k)) ⊗[k]
            (AdjoinRoot (Polynomial.X ^ lam : Polynomial k)),
        Algebra.TensorProduct.productMap
            (AlgHom.id k (AdjoinRoot (Polynomial.X ^ lam : Polynomial k)))
            ((Algebra.ofId k (AdjoinRoot (Polynomial.X ^ lam : Polynomial k))).comp
              (jetEps k lam)) F = AdjoinRoot.root _ ∧
        Algebra.TensorProduct.productMap
            ((Algebra.ofId k (AdjoinRoot (Polynomial.X ^ lam : Polynomial k))).comp
              (jetEps k lam))
            (AlgHom.id k (AdjoinRoot (Polynomial.X ^ lam : Polynomial k))) F
              = AdjoinRoot.root _ ∧
        F ^ lam = 0 := by
  sorry

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
already-proven `Torsion.torsionπ_etale` (T-B5′: `E[N] ⟶ S` finite étale when `N`
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
    (a : ℤ) • Point.pull E t P ≠ 0 := by
  intro hzero
  -- Geometry bridge (T-D6b register box): a proper relation `a • P_k = 0` forces a fat
  -- point of length `lam ≥ 2` dividing `N`, whose comultiplication is jet data for the
  -- binomial core.
  obtain ⟨lam, hlz, hlam2, hlamN, F, h1, h2, hpow⟩ :=
    h.pull_nsmul_jetData E hN hkill k t ha0 haN hzero
  -- Pure-algebra endpoint: the binomial core kills `lam` in `k`.
  have hlk : (lam : k) = 0 := jetCore_binomial hlam2 F h1 h2 hpow
  -- `lam ∣ N` propagates the relation to `N`.
  have hNk : (N : k) = 0 := by
    obtain ⟨m, rfl⟩ := hlamN
    rw [Nat.cast_mul, hlk, zero_mul]
  -- ...contradicting invertibility of `N` on the field fibre.
  have hinv : NIsInvertible (Spec (CommRingCat.of k)) N := hN.of_hom t
  simp only [NIsInvertible] at hinv
  have hu := hinv.map (Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom
  rw [map_natCast] at hu
  exact isUnit_iff_ne_zero.mp hu hNk

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
    refine ⟨?_, fun a ha0 haN => h.pull_nsmul_ne_zero E hN hkill k t ha0 haN⟩
    rw [← Point.pull_zsmul, hkill, Point.pull_zero]
  · intro h
    exact Section.hasExactOrder_of_geometric E hN hkill fun k _ _ t => (h k t).2

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
Derived from T-D6 and the `T-D7-bridge` box. -/
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
