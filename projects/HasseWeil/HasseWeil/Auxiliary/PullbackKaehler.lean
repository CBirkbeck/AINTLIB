import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.RingTheory.Derivation.Basic

/-!
# Pullback action on Kähler differentials along an algebra endomorphism

For an `R`-algebra `S` and an `R`-algebra endomorphism `f : S →ₐ[R] S`, this file
defines the induced action `f.pullbackKaehler : Ω[S⁄R] →+ Ω[S⁄R]` characterized by
`f.pullbackKaehler (D x) = D (f x)`. It is `R`-linear and `f`-semilinear over `S`.

This is the algebraic formulation of "pullback of differentials along a morphism of
schemes": for `Spec S → Spec S` given by `f`, the pullback on Kähler differentials
acts on `Ω[S⁄R]`.

## Main definitions

* `AlgHom.pullbackKaehler` — the additive map.

## Main theorems

* `pullbackKaehler_D` — `f*(D x) = D(f x)`
* `pullbackKaehler_smul_R` — `R`-linearity (pulls out base ring scalars)
* `pullbackKaehler_smul_S` — `f`-semilinearity (an `S`-scalar is transformed by `f`)
* `pullbackKaehler_comp` — contravariant functoriality
* `pullbackKaehler_id` — sends the identity to the identity

## Implementation

To avoid conflicts with the existing global `Module S Ω[S⁄R]` instance, we use a
wrapper type `TwistedKaehler f` definitionally equal to `Ω[S⁄R]` but carrying a
twisted `S`-module structure (via `Module.compHom` along `f`). With the twisted
structure, `x ↦ KaehlerDifferential.D R S (f x)` becomes a genuine derivation
`Derivation R S (TwistedKaehler f)`, which lifts via the universal property to
`Ω[S⁄R] →ₗ[S] TwistedKaehler f`. We then forget the `S`-linearity (it's twisted)
and keep only the underlying `AddMonoidHom`.
-/

open KaehlerDifferential

namespace AlgHom

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- Wrapper struct for `Ω[S⁄R]` carrying a twisted `S`-module structure where `s ∈ S`
acts as `f s` via the standard action. Used internally to construct
`pullbackKaehler`. The struct wrapper prevents typeclass conflicts with the default
`Module S Ω[S⁄R]` instance. -/
structure TwistedKaehler (f : S →ₐ[R] S) where
  /-- Wrap an element of `Ω[S⁄R]` into the twisted module. -/
  mk' ::
  /-- Underlying differential. -/
  out : Ω[S⁄R]

namespace TwistedKaehler

variable (f : S →ₐ[R] S)

@[ext]
theorem ext {x y : TwistedKaehler f} (h : x.out = y.out) : x = y := by
  cases x; cases y; congr

noncomputable instance : Zero (TwistedKaehler f) := ⟨⟨0⟩⟩
noncomputable instance : Add (TwistedKaehler f) := ⟨fun x y ↦ ⟨x.out + y.out⟩⟩
noncomputable instance : Neg (TwistedKaehler f) := ⟨fun x ↦ ⟨-x.out⟩⟩
noncomputable instance : Sub (TwistedKaehler f) := ⟨fun x y ↦ ⟨x.out - y.out⟩⟩

@[simp] theorem out_zero : (0 : TwistedKaehler f).out = 0 := rfl
@[simp] theorem out_add (x y : TwistedKaehler f) : (x + y).out = x.out + y.out := rfl
@[simp] theorem out_neg (x : TwistedKaehler f) : (-x).out = -x.out := rfl
@[simp] theorem out_sub (x y : TwistedKaehler f) : (x - y).out = x.out - y.out := rfl

noncomputable instance : AddCommGroup (TwistedKaehler f) where
  add_assoc x y z := by ext; simp [add_assoc]
  zero_add x := by ext; simp
  add_zero x := by ext; simp
  add_comm x y := by ext; simp [add_comm]
  neg_add_cancel x := by ext; simp
  sub_eq_add_neg x y := by ext; simp [sub_eq_add_neg]
  zsmul := zsmulRec
  nsmul := nsmulRec

/-- The twisted `S`-action: `s • ω := f s • ω.out`. -/
noncomputable instance instSMul : SMul S (TwistedKaehler f) where
  smul s x := ⟨f s • x.out⟩

@[simp] theorem out_smul_S (s : S) (x : TwistedKaehler f) :
    (s • x).out = f s • x.out := rfl

/-- The twisted `S`-action makes `TwistedKaehler f` an `S`-module. -/
noncomputable instance instModule : Module S (TwistedKaehler f) where
  one_smul x := by ext; simp [out_smul_S, map_one]
  mul_smul s t x := by ext; simp [out_smul_S, map_mul, mul_smul]
  smul_zero s := by ext; simp [out_smul_S]
  smul_add s x y := by ext; simp [out_smul_S, smul_add]
  add_smul s t x := by ext; simp [out_smul_S, map_add, add_smul]
  zero_smul x := by ext; simp [out_smul_S, map_zero]

/-- The R-action on the wrapper: lift the standard R-action through `out`. -/
noncomputable instance instSMulR : SMul R (TwistedKaehler f) where
  smul r x := ⟨r • x.out⟩

@[simp] theorem out_smul_R (r : R) (x : TwistedKaehler f) :
    (r • x : TwistedKaehler f).out = r • x.out := rfl

noncomputable instance : Module R (TwistedKaehler f) where
  one_smul x := by ext; simp [out_smul_R]
  mul_smul r₁ r₂ x := by ext; simp [out_smul_R, mul_smul]
  smul_zero r := by ext; simp [out_smul_R]
  smul_add r x y := by ext; simp [out_smul_R, smul_add]
  add_smul r₁ r₂ x := by ext; simp [out_smul_R, add_smul]
  zero_smul x := by ext; simp [out_smul_R]

/-- The twisted `S`-action factors through `R` correctly. -/
instance : IsScalarTower R S (TwistedKaehler f) := by
  refine ⟨fun r s ω ↦ ?_⟩
  ext
  change f (r • s) • ω.out = r • (f s • ω.out)
  rw [map_smul, smul_assoc]

end TwistedKaehler

/-- The composition `D ∘ f : S → Ω[S⁄R]` (lifted into `TwistedKaehler f`) viewed as a
derivation. The twisted module structure makes Leibniz work. -/
noncomputable def derivationCompHom (f : S →ₐ[R] S) :
    Derivation R S (TwistedKaehler f) where
  toFun x := ⟨KaehlerDifferential.D R S (f x)⟩
  map_add' x y := by ext; simp [map_add, TwistedKaehler.out_add]
  map_smul' r x := by
    ext
    change (KaehlerDifferential.D R S (f (r • x))) = r • (KaehlerDifferential.D R S (f x))
    rw [map_smul, Derivation.map_smul]
  map_one_eq_zero' := by
    ext
    change KaehlerDifferential.D R S (f 1) = (0 : Ω[S⁄R])
    rw [map_one, Derivation.map_one_eq_zero]
  leibniz' x y := by
    ext
    change KaehlerDifferential.D R S (f (x * y)) =
      ((x • ⟨KaehlerDifferential.D R S (f y)⟩ : TwistedKaehler f) +
       (y • ⟨KaehlerDifferential.D R S (f x)⟩ : TwistedKaehler f)).out
    rw [map_mul, Derivation.leibniz, TwistedKaehler.out_add,
      TwistedKaehler.out_smul_S, TwistedKaehler.out_smul_S]

/-- The additive endomorphism of `Ω[S⁄R]` induced by an `R`-algebra endomorphism
`f : S →ₐ[R] S`. Characterised by `f.pullbackKaehler (D x) = D (f x)`. -/
noncomputable def pullbackKaehler (f : S →ₐ[R] S) :
    Ω[S⁄R] →+ Ω[S⁄R] :=
  let lift : Ω[S⁄R] →ₗ[S] TwistedKaehler f := f.derivationCompHom.liftKaehlerDifferential
  { toFun := fun ω ↦ (lift ω).out
    map_zero' := by change (lift 0).out = 0; rw [map_zero]; rfl
    map_add' := fun x y ↦ by change (lift (x + y)).out = (lift x).out + (lift y).out
                              rw [map_add]; rfl }

/-- The pullback of `D x` is `D (f x)`. -/
@[simp]
theorem pullbackKaehler_D (f : S →ₐ[R] S) (x : S) :
    f.pullbackKaehler (KaehlerDifferential.D R S x) =
      KaehlerDifferential.D R S (f x) := by
  change (f.derivationCompHom.liftKaehlerDifferential
        (KaehlerDifferential.D R S x)).out = _
  rw [Derivation.liftKaehlerDifferential_comp_D]
  rfl

/-- The pullback is `R`-linear. -/
theorem pullbackKaehler_smul_R (f : S →ₐ[R] S) (r : R) (ω : Ω[S⁄R]) :
    f.pullbackKaehler (r • ω) = r • f.pullbackKaehler ω := by
  -- pullbackKaehler is the .out of an S-linear map (in the twisted module).
  -- S-linearity gives R-linearity via the scalar tower R → S.
  change (f.derivationCompHom.liftKaehlerDifferential (r • ω)).out =
    r • (f.derivationCompHom.liftKaehlerDifferential ω).out
  rw [LinearMap.map_smul_of_tower]
  rfl

/-- The pullback is `f`-semilinear: an `S`-scalar `s` becomes `f s` after pullback. -/
theorem pullbackKaehler_smul_S (f : S →ₐ[R] S) (s : S) (ω : Ω[S⁄R]) :
    f.pullbackKaehler (s • ω) = f s • f.pullbackKaehler ω := by
  -- The lifted map is S-linear in the twisted action: lift(s • ω) = s •_twisted lift(ω)
  -- = ⟨f s • (lift ω).out⟩, so .out is f s • (lift ω).out.
  change (f.derivationCompHom.liftKaehlerDifferential (s • ω)).out = _
  rw [LinearMap.map_smul]
  rfl

/-- Helper: equality of two `AddMonoidHom`s on `Ω[S⁄R]` follows from agreeing on
`D x` for all `x` and respecting `S`-smul step (whatever the user wants to use). -/
private theorem ext_of_D {f₁ f₂ : Ω[S⁄R] →+ Ω[S⁄R]}
    (h_smul : ∀ (s : S) (ω : Ω[S⁄R]), f₁ ω = f₂ ω → f₁ (s • ω) = f₂ (s • ω))
    (h_D : ∀ x : S, f₁ (KaehlerDifferential.D R S x) =
                    f₂ (KaehlerDifferential.D R S x)) :
    f₁ = f₂ := by
  apply AddMonoidHom.ext
  intro ω
  have hω : ω ∈ Submodule.span S (Set.range (KaehlerDifferential.D R S)) := by
    rw [KaehlerDifferential.span_range_derivation]; exact Submodule.mem_top
  refine Submodule.span_induction (p := fun x _ ↦ f₁ x = f₂ x) ?_ ?_ ?_ ?_ hω
  · rintro _ ⟨x, rfl⟩
    exact h_D x
  · simp
  · intro x y _ _ hx hy
    rw [map_add, map_add, hx, hy]
  · intro s x _ hx
    exact h_smul s x hx

/-- The pullback for the identity algebra hom is the identity. -/
@[simp]
theorem pullbackKaehler_id : (AlgHom.id R S).pullbackKaehler = AddMonoidHom.id _ := by
  refine ext_of_D (fun s ω hω ↦ ?_) (fun x ↦ ?_)
  · change (AlgHom.id R S).pullbackKaehler (s • ω) = s • ω
    rw [pullbackKaehler_smul_S]
    change s • ((AlgHom.id R S).pullbackKaehler ω) = s • ω
    rw [show ((AlgHom.id R S).pullbackKaehler ω) = ω from hω]
  · change (AlgHom.id R S).pullbackKaehler (KaehlerDifferential.D R S x) =
      KaehlerDifferential.D R S x
    rw [pullbackKaehler_D]
    rfl

/-- The pullback respects composition. Note: `AlgHom.comp f g = f ∘ g` (apply `g`
first, then `f`), so the induced pullback on Ω composes in the SAME order:
`(f.comp g).pullbackKaehler = f.pullbackKaehler ∘ g.pullbackKaehler` (apply
`g.pullbackKaehler` first, then `f.pullbackKaehler`). -/
@[simp]
theorem pullbackKaehler_comp (f g : S →ₐ[R] S) :
    (f.comp g).pullbackKaehler =
      f.pullbackKaehler.comp g.pullbackKaehler := by
  refine ext_of_D (fun s ω hω ↦ ?_) (fun x ↦ ?_)
  · rw [pullbackKaehler_smul_S, hω]
    -- Goal: (f.comp g) s • (f.pullbackKaehler.comp g.pullbackKaehler) ω
    --     = (f.pullbackKaehler.comp g.pullbackKaehler) (s • ω)
    change f (g s) • f.pullbackKaehler (g.pullbackKaehler ω) =
      f.pullbackKaehler (g.pullbackKaehler (s • ω))
    rw [pullbackKaehler_smul_S, pullbackKaehler_smul_S]
  · change ((f.comp g).pullbackKaehler) (KaehlerDifferential.D R S x) =
      f.pullbackKaehler (g.pullbackKaehler (KaehlerDifferential.D R S x))
    rw [pullbackKaehler_D, pullbackKaehler_D, pullbackKaehler_D]
    rfl

end AlgHom
