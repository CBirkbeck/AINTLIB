import ModularCurves.EllipticCurve.GroupLaw
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
import Mathlib.AlgebraicGeometry.Morphisms.Etale

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

open AlgebraicGeometry CategoryTheory Limits

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
    IsClosedImmersion (E.torsionι N) := by sorry

/-- **(T-B4 = KM 2.3.1)** `E[N] ⟶ S` is finite and flat (finite locally free) — of rank
`N²` by `torsion_rank`. Black-box inputs: `[N]` finite flat of degree `N²` (KM 2.3.1; via
fibrewise `deg [N] = N²`, Silverman III.6.2(d), + the fibrewise flatness criterion,
EGA IV 11.3.10 — register item BB-FLAT). -/
theorem torsionπ_isFinite (N : ℕ) [NeZero N] : IsFinite (E.torsionπ N) := by sorry

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
