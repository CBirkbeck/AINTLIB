/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.Picard.DivisorClass
import ModularCurves.EllipticCurve.Torsion
import ModularCurves.EllipticCurve.TorsionFibre

/-!
# Restricted self-adjointness of `[N]` on the relative Picard group (DS4 Gap A, `(★)`/`(★′)`)

**Skeleton only — `/develop --decompose` Step 2.5. Not yet proved.**

The decisive input for the Katz–Mazur / GME construction of the relative Weil pairing.
Writing `κ_T(Q) = [𝒪(Q − 0)]` for `sectionToPicRel` and `m_N = [N]` on the base-changed
curve:

* `(★)`  `m_N^* κ_T(Q) = κ_T([N] Q)`     — the reusable form;
* `(★′)` `[N] Q = 0  ⟹  m_N^* κ_T(Q) = 1` — all the *construction* needs.

This is the theorem-of-the-square / principal-polarization content of the slogan "`[N]` is
self-dual". It does **not** follow from the existing `Pic`, `picRel` or `RelEffCartierDiv`
APIs, and it is *not* the same as Abel's theorem: with `picRel = Ker(0^*)` as codomain,
"`sectionToPicRel` is an isomorphism" is **false** (over a field `Pic(k) = 0`, so
`Ker(0^*) = Pic(E)` carries every degree, while `κ` hits only degree zero). Abel is an
isomorphism onto a *degree-zero* subfunctor, and the construction does not need it.

## Closest existing material (field level — read before attacking this)

`projects/HasseWeil/HasseWeil/Pic0/`:
* `TheoremOfSquareDivisorForm.kappaDivisor_add_linEquiv` — `κ(A+B) ∼ κ(A) + κ(B)`, proved
  **unconditionally in any characteristic** (Abel in divisor form, Silverman III.3.5);
* `TheoremOfSquareDivisorForm.tos_divisor`, `tos_toClass` — the theorem of the square;
* `PicDualPullbackTheoremOfSquare.tos_pullback_principal_of_sigma_eq_zero` — the pullback
  form, with its residual pinned to a point identity.

Those are statements about Weierstrass divisors over a field; `(★′)` is the *relative,
sheafified* counterpart, so they give the shape of the argument rather than the argument.

## Note on the rigidification trap

`Pic` is built through `Skeleton`, so an equality of classes yields only a `Nonempty`
isomorphism, never a canonical one. The pairing construction downstream must therefore be
built on genuine **rigidified** invertible sheaves — the lift `L ↦ L ⊗ f^*(0^*L)⁻¹` of
`picRelProj`, carrying its canonical zero-section rigidification — and only descended to
Picard classes at the end. `(★′)` as stated here is the class-level shadow: it is what
supplies *existence* of the trivialization, after which
`EllipticCurveGeom.universallyOConnected` (`EllipticCurve/Rigidity.lean`, proved) makes the
normalized choice unique.
-/

universe u

open CategoryTheory AlgebraicGeometry Limits AlgebraicGeometry.Scheme.Modules

namespace ModularCurves

variable {S : Scheme.{u}} (E : EllipticCurve S) {T : Scheme.{u}}

/-! ## `κ`, on the group of sections

`sectionToPicRel` takes a raw section `(Q, hQ)`. That data is exactly an element of
`(E.baseChange t).Point (𝟙 T)`, which carries mathlib-style `AddCommGroup` structure — so
phrasing `κ` on it gives the group operations for free, and lets `(★′)` be *derived* rather
than assumed. -/

variable (hsm : SmoothOfRelativeDimension 1 E.π) [IsSeparated E.π] (t : T ⟶ S)

/-- `κ_T(Q) = [𝒪(Q − 0)]`, the GME (2.16) class of a section, as an element of
`Pic (E ×_S T)`. -/
noncomputable def kappa (Q : (E.baseChange t).Point (𝟙 T)) :
    Scheme.Pic (pullback E.π t) :=
  (sectionToPicRel E.π E.zero E.zero_π hsm t Q.1 Q.2).1

/-- `sectionToPicRel` depends on the section only through its underlying morphism (the
side condition is a `Prop`). Stated separately so no proof below has to rewrite under a
dependent argument. -/
theorem sectionToPicRel_congr {P P' : T ⟶ pullback E.π t}
    (hP : P ≫ pullback.snd E.π t = 𝟙 T) (hP' : P' ≫ pullback.snd E.π t = 𝟙 T)
    (h : P = P') :
    sectionToPicRel E.π E.zero E.zero_π hsm t P hP =
      sectionToPicRel E.π E.zero E.zero_π hsm t P' hP' := by
  subst h; rfl

/-- `κ` is pointed. Immediate from the proved `sectionToPicRel_zero`. -/
@[simp] theorem kappa_zero : kappa E hsm t 0 = 1 := by
  have h0 : ((0 : (E.baseChange t).Point (𝟙 T)).1 : T ⟶ pullback E.π t) =
      baseChangeZero E.π E.zero E.zero_π t :=
    ((E.baseChange t).point_zero_val (𝟙 T)).trans (Category.id_comp _)
  have hcongr := sectionToPicRel_congr E hsm t
    (0 : (E.baseChange t).Point (𝟙 T)).2 (baseChangeZero_snd E.π E.zero E.zero_π t) h0
  have hz := sectionToPicRel_zero E.π E.zero E.zero_π hsm t
  exact congrArg Subtype.val (hcongr.trans hz)

/-- **(LEAF (i) — Abel, divisor-additivity fragment)** `κ` is a homomorphism.

Field-level template, proved **unconditionally in any characteristic**:
`HasseWeil.Pic0.TheoremOfSquareDivisorForm.kappaDivisor_add_linEquiv`
(`κ(A+B) ∼ κ(A) + κ(B)`, Silverman III.3.5). This is the relative, sheafified counterpart.
It is *strictly weaker* than Abel's isomorphism theorem, which is false with `Ker(0^*)` as
codomain (see the module docstring). -/
theorem kappa_add (Q Q' : (E.baseChange t).Point (𝟙 T)) :
    kappa E hsm t (Q + Q') = kappa E hsm t Q * kappa E hsm t Q' := by
  sorry

/-- `κ` carries `ℕ`-multiples to powers. Derived from `kappa_add` and `kappa_zero`. -/
theorem kappa_nsmul (Q : (E.baseChange t).Point (𝟙 T)) (n : ℕ) :
    kappa E hsm t (n • Q) = kappa E hsm t Q ^ n := by
  induction n with
  | zero => simpa using kappa_zero E hsm t
  | succ n ih => rw [succ_nsmul, kappa_add, ih, pow_succ]

/-- **(LEAF (ii) — theorem of the square)** Pullback along `[N]` is the `N`-th power on the
classes `κ(Q)`.

This is the relative form of "`[N]^* = N` on `Pic⁰`". The classes `κ(Q)` are fibrewise of
degree zero by construction, so no degree function on `picRel` is needed to state it — which
matters, since `Ker(0^*)` is *not* `Pic⁰`. -/
theorem picMap_mulByHom_kappa_pow (N : ℕ) (Q : (E.baseChange t).Point (𝟙 T)) :
    Scheme.Pic.map ((E.baseChange t).mulByHom N) (kappa E hsm t Q) =
      kappa E hsm t Q ^ N := by
  sorry

/-- **(★′ — PROVED from the two leaves)** The pullback along `[N]` of the class of an
`N`-torsion section is trivial:
`[N]^* κ(Q) = κ(Q)^N = κ(N • Q) = κ(0) = 1`.

This is the decisive input for the Katz–Mazur / GME construction of the relative Weil
pairing: it is what supplies a trivialization of `[N]^* L_Q`, which
`EllipticCurveGeom.universallyOConnected` then normalizes uniquely. -/
theorem picMap_mulByHom_kappa_eq_one (N : ℕ) (Q : (E.baseChange t).Point (𝟙 T))
    (hQ : (N : ℤ) • Q = 0) :
    Scheme.Pic.map ((E.baseChange t).mulByHom N) (kappa E hsm t Q) = 1 := by
  have hnat : (N • Q : (E.baseChange t).Point (𝟙 T)) = 0 := by
    rwa [natCast_zsmul] at hQ
  rw [picMap_mulByHom_kappa_pow E hsm t N Q, ← kappa_nsmul E hsm t Q N, hnat]
  exact kappa_zero E hsm t

end ModularCurves
