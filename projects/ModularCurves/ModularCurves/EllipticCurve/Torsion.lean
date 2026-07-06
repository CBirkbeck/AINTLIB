import ModularCurves.EllipticCurve.GroupLaw
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem

/-!
# Torsion subgroup schemes `E[N]`

For an elliptic curve `E/S` and `N ≥ 1`, the `N`-torsion `E[N]` is the kernel of
`[N] : E ⟶ E`, i.e. the fibre product `E ×_{[N], E, 0} S`. The two headline theorems, both
from KM 2.3 and both black-box targets of workstream B:

* **KM 2.3.1**: `E[N] → S` is finite locally free of rank `N²` (proof: `[N]` is finite
  locally free of degree `N²`, via Hasse's `deg [N] = N²` on fibres + fibrewise flatness
  criterion — see the black-box register).
* **Loeffler Lemma 3.4.2(2)** (verbatim: *"If `E/S` is an elliptic curve and `N ≥` is [sic]
  invertible on `S`, then `[N] : E → E` is smooth. ... The morphism `[N]` multiplies a
  global differential by `N`, so it induces an isomorphism of tangent space. In other
  words, it is an étale morphism"*): when `N` is invertible on `S`, `[N]` is étale, hence
  `E[N] → S` is finite étale of rank `N²`.

The fibrewise structure `E[N](k̄) ≅ (ℤ/N)²` (for `N` invertible, `k̄` algebraically closed)
is Silverman III.6.4(b) and is **already proved in this repository over fields**:
`projects/HasseWeil/HasseWeil/NTorsion/TorsionGeneralN.lean`. The comparison of that result
with the fibres of this scheme-theoretic `E[N]` is ticket `T-B6` (kept out of the skeleton to
avoid the cross-project import in the definitional spine).
-/

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory
  CategoryTheory.Over.braidedCategory

universe u

namespace ModularCurves

namespace EllipticCurve

variable {S : Scheme.{u}} (E : EllipticCurve S)

/-- "`N` is invertible on the scheme `X`": `N` is a unit in the global sections. -/
def _root_.ModularCurves.NIsInvertible (X : Scheme.{u}) (N : ℕ) : Prop :=
  IsUnit (N : Γ(X, ⊤))

/-- The `N`-torsion subscheme `E[N]`: the kernel of `[N]`, as the fibre product
`E ×_{[N], E, 0} S` of `[N] : E ⟶ E` against the zero section.
Source: KM 2.3; Loeffler §3.4. -/
noncomputable def torsion (N : ℕ) : Scheme.{u} :=
  pullback (E.mulByHom N) E.zero

/-- The inclusion `E[N] ⟶ E`. -/
noncomputable def torsionι (N : ℕ) : E.torsion N ⟶ E.E :=
  pullback.fst _ _

/-- The structure morphism `E[N] ⟶ S`. -/
noncomputable def torsionπ (N : ℕ) : E.torsion N ⟶ S :=
  pullback.snd _ _

/-- A `T`-point of `E[N]`, from a point of `E` raw-killed by `N` (i.e. whose composite
with `[N]` is the zero section over the base point). Real construction via the universal
property of the kernel pullback. -/
noncomputable def pointToTorsion {N : ℕ} {T : Scheme.{u}} {g : T ⟶ S} (x : E.Point g)
    (hx : x.1 ≫ E.mulByHom N = g ≫ E.zero) : T ⟶ E.torsion N :=
  pullback.lift x.1 g hx

@[simp]
theorem pointToTorsion_torsionπ {N : ℕ} {T : Scheme.{u}} {g : T ⟶ S} (x : E.Point g)
    (hx : x.1 ≫ E.mulByHom N = g ≫ E.zero) :
    E.pointToTorsion x hx ≫ E.torsionπ N = g :=
  pullback.lift_snd _ _ _

@[simp]
theorem pointToTorsion_torsionι {N : ℕ} {T : Scheme.{u}} {g : T ⟶ S} (x : E.Point g)
    (hx : x.1 ≫ E.mulByHom N = g ≫ E.zero) :
    E.pointToTorsion x hx ≫ E.torsionι N = x.1 :=
  pullback.lift_fst _ _ _

/-- **(T-B3)** `E[N] ⟶ E` is a closed immersion (kernels of group-scheme morphisms against
proper separated bases; the zero section of a separated morphism is a closed immersion). -/
theorem torsionι_isClosedImmersion (N : ℕ) :
    IsClosedImmersion (E.torsionι N) := by
  have h1 : IsClosedImmersion (E.zero ≫ E.π) := by
    rw [E.zero_π]
    infer_instance
  have h2 : IsClosedImmersion E.zero := IsClosedImmersion.of_comp (f := E.zero) (g := E.π)
  exact MorphismProperty.pullback_fst _ _ h2

/-- The torsion inclusion followed by the structure morphism is the torsion structure
morphism. -/
@[reassoc]
theorem torsionι_π (N : ℕ) : E.torsionι N ≫ E.π = E.torsionπ N := by
  show pullback.fst (E.mulByHom N) E.zero ≫ E.π = pullback.snd (E.mulByHom N) E.zero
  calc pullback.fst (E.mulByHom N) E.zero ≫ E.π
      = pullback.fst (E.mulByHom N) E.zero ≫ E.mulByHom N ≫ E.π := by
        rw [E.mulByHom_π]
    _ = (pullback.fst (E.mulByHom N) E.zero ≫ E.mulByHom N) ≫ E.π :=
        (Category.assoc _ _ _).symm
    _ = (pullback.snd (E.mulByHom N) E.zero ≫ E.zero) ≫ E.π := by
        rw [pullback.condition]
    _ = pullback.snd (E.mulByHom N) E.zero ≫ E.zero ≫ E.π := Category.assoc _ _ _
    _ = pullback.snd (E.mulByHom N) E.zero ≫ 𝟙 S := by rw [E.zero_π]
    _ = pullback.snd (E.mulByHom N) E.zero := Category.comp_id _

/-- `[n]` is proper: it is an `S`-endomorphism of the proper `S`-scheme `E`
(cancellation along the separated `π`). KM 2.3.1 proof, first reduction ("Because `E`
is proper over `S`, any `S`-endomorphism of `E` is proper"). -/
instance mulByHom_isProper (n : ℤ) : IsProper (E.mulByHom n) := by
  haveI h : IsProper (E.mulByHom n ≫ E.π) := by
    rw [E.mulByHom_π]
    exact E.proper
  exact IsProper.of_comp (E.mulByHom n) E.π

/-- The zero morphism `[0]` factors through the base: it is `π` followed by the zero
section (the unit of the hom-group is `toUnit ≫ η`, and the unit of the group object
is the zero section by `one_eq_zero`). -/
theorem mulByHom_zero : E.mulByHom 0 = E.π ≫ E.zero := by
  show (E.mulBy 0).left = E.π ≫ E.zero
  have h0 : E.mulBy 0 = toUnit E.asOver ≫ (η[E.asOver] : _ ⟶ E.asOver) := rfl
  have ht : (toUnit E.asOver).left = E.π := by
    have hw := Over.w (toUnit E.asOver)
    simpa using hw
  rw [h0]
  have key : (toUnit E.asOver).left ≫ ((𝟙_ (Over S)).hom ≫ E.zero) = E.π ≫ E.zero :=
    (congrArg (fun q => q ≫ ((𝟙_ (Over S)).hom ≫ E.zero)) ht).trans
      (congrArg (fun q => E.π ≫ q) (Category.id_comp E.zero))
  refine Eq.trans ?_ key
  exact congrArg (fun q => (toUnit E.asOver).left ≫ q) E.one_eq_zero

/-- **Black box `BB-QF` (fibre input of KM 2.3.1)**: `[N]` is (locally) quasi-finite
for `N ≥ 1`. KM 2.3.1 proof: finite fibres are checked geometric fibre by geometric
fibre — on an elliptic curve over an algebraically closed field `[N]` is nonconstant
(for `M` prime to `N·char k` it permutes the `M²`-many `M`-torsion points), and a
nonconstant morphism of proper smooth connected curves has finite fibres. To be
discharged via the fibre-comparison stream (T-B6 + HasseWeil `mulByInt_degree`). -/
theorem mulByHom_locallyQuasiFinite (N : ℕ) [NeZero N] :
    LocallyQuasiFinite (E.mulByHom N) := by sorry

/-- **Black box `BB-FLAT` (flatness input of KM 2.3.1)**: `[N]` is flat for `N ≥ 1`.
KM 2.3.1 proof: via miracle flatness over the universal (regular) Weierstrass base
("any finite morphism between regular schemes of the same dimension is automatically
flat [AK-1, V, 3.6]"); general fibrewise criterion: EGA IV 11.3.10. -/
theorem mulByHom_flat (N : ℕ) [NeZero N] : Flat (E.mulByHom N) := by sorry

/-- **Black box `BB-DEG` (degree input of KM 2.3.1)**: `[N]` has rank `N²` at every
point. KM 2.3.1 proof: the rank is computed at a single geometric point (`E^an ≅ ℂ/L`,
`E[N] = (1/N)L/L ≅ (ℤ/N)²`); algebraic anchor: HasseWeil `mulByInt_degree` via T-B6. -/
theorem mulByHom_finrank (N : ℕ) [NeZero N] (x : E.E) :
    (E.mulByHom N).finrank x = N ^ 2 := by sorry

/-- **(KM 2.3.1, finiteness of `[N]`)** `[N]` is finite: proper + quasi-finite via
Zariski's Main Theorem (`IsFinite.of_isProper_of_locallyQuasiFinite`). -/
theorem mulByHom_isFinite (N : ℕ) [NeZero N] : IsFinite (E.mulByHom N) := by
  haveI := E.mulByHom_locallyQuasiFinite N
  exact IsFinite.of_isProper_of_locallyQuasiFinite _

/-- **(T-B4 = KM 2.3.1)** `E[N] ⟶ S` is finite and flat (finite locally free) — of rank
`N²` by `torsion_rank`. Black-box inputs: `[N]` finite flat of degree `N²` (KM 2.3.1; via
fibrewise `deg [N] = N²`, Silverman III.6.2(d), + the fibrewise flatness criterion,
EGA IV 11.3.10 — register item BB-FLAT). -/
theorem torsionπ_isFinite (N : ℕ) [NeZero N] : IsFinite (E.torsionπ N) := by
  have h := E.mulByHom_isFinite N
  exact MorphismProperty.pullback_snd _ _ h

/-- **(T-B4, flatness half of KM 2.3.1; BB-FLAT/stream FLAT consumer)** `E[N] ⟶ S` is
flat. -/
theorem torsionπ_flat (N : ℕ) : Flat (E.torsionπ N) := by sorry

/-- **(T-B4, rank part of KM 2.3.1)** `E[N]/S` has constant rank `N²`. -/
theorem torsion_rank (N : ℕ) [NeZero N] (s : S) :
    (E.torsionπ N).finrank s = N ^ 2 := by sorry

/-- **(T-B5 = Loeffler 3.4.2(2))** If `N` is invertible on `S`, then `[N] : E ⟶ E` is étale
(it induces multiplication by `N`, an isomorphism, on the invariant differential). -/
theorem mulBy_etale (N : ℕ) (h : NIsInvertible S N) :
    Etale (E.mulByHom N) := by sorry

/-- **(T-B5′)** If `N` is invertible on `S`, then `E[N] ⟶ S` is (finite) étale.
Source: Loeffler §3.4; KM 2.3.5. -/
theorem torsionπ_etale (N : ℕ) (h : NIsInvertible S N) :
    Etale (E.torsionπ N) := by sorry

end EllipticCurve

end ModularCurves
