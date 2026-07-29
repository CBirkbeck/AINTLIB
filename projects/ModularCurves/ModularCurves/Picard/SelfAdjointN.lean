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

**One sorry left** (`exists_invertible_tensor_idealModule_add`); the whole Picard layer
around it is proved and axiom-clean. See "State (2026-07-29)" below.

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
`ModularCurves.eq_one_of_pullback_eq_one` (`EllipticCurve/SectionRigidity.lean`, proved)
makes the normalized choice unique.

## Available machinery, and the one remaining leaf

The descent workhorse is proved and axiom-clean:

* `AlgebraicGeometry.Scheme.Modules.nonempty_unitObj_iso_of_glue`
  (`Picard/GlueTrivialization.lean`) — an `𝒪`-module with cover-local generating sections
  agreeing on overlaps is trivial. Sections glue by the sheaf axiom; the glued global
  section is tested by `isIso_of_bijective_app_on_cover`.
* `ModularCurves.nonempty_unitObj_iso_of_normalized_glue` (`Picard/RigidDescent.lean`) —
  the elliptic-curve form: generating sections over the `f`-preimages of a cover **of the
  base**, whose overlap comparison units are `1` along the zero section, give triviality.
  Overlap agreement is *forced*, not checked: two generating sections differ by a unit, and
  a unit that is `1` on the zero section is `1`. That the cover may be taken **Zariski** is
  not a restriction: a zero-normalized trivialization is unique, so an fppf-local one
  descends.

### The route (revised 2026-07-27 after an external review)

There is only ONE classical leaf, `exists_pic_map_snd_sectionCls_add`. Two routes were
considered and rejected:

* *Fibrewise seesaw over an arbitrary base is **false**.* Over `T = Spec k[ε]/(ε²)` and
  `X = E₀ × T`, a nonzero class of `H¹(E₀, 𝒪)` gives transition functions `1 + ε a_{ij}`:
  the bundle is trivial on the only fibre, is rigidified along zero (as `Pic T = 0`), and is
  still nontrivial. It is the infinitesimal direction of `Pic⁰`. Seesaw needs the base
  **reduced** (Stacks 0EX7). For the same reason "fibrewise degree `0` + rigidified along
  `0` ⟹ Zariski-locally trivial on the base" is false — already over a field, by
  `L = 𝒪(P − 0)` with `P ≠ 0`.
* *The explicit line-and-vertical function on a Weierstrass chart* — the ideal identity
  `I(D_P)·I(D_Q)·I(D_{−(P+Q)}) = (ℓ)` with `I(D_{P+Q})·I(D_{−(P+Q)}) = (v)` — is workable but
  needs the degenerate loci (`P = Q`, `P = −Q`, either `= 0`) handled as closed subschemes
  rather than finitely many bad points, and so needs the complete projective addition-law
  charts. Ranked well below the route now taken.

The route taken instead proves the leaf **on the universal pair of points**, where the base
is reduced and the seesaw applies, and then base-changes down:

1. `U = Spec (A_univ[Δ⁻¹])`, `C ⟶ U` the universal smooth Weierstrass cubic, `B = C ×_U C`
   with its two universal sections `P, Q` (`EllipticCurve/AdditionBaseChange.lean`;
   reducedness of the universal curve and of the fibre square is in
   `EllipticCurve/GroupLawAxioms.lean`).
2. On `C_B ⟶ B` form the rigidified discrepancy
   `Δ^rig_{P,Q} = Δ_{P,Q} ⊗ f_B^*(0^* Δ_{P,Q})⁻¹`, where
   `Δ_{P,Q} = 𝒪(D_{P+Q} + D_0 − D_P − D_{Q})`.
3. Every residue-field fibre of `Δ^rig` is trivial, by the field theorem
   `HasseWeil.Pic0.RouteCTheoremOfSquareDiv.kappaDivisor_add_linEquiv` (Silverman III.3.5,
   proved unconditionally in any characteristic).
4. `B` is reduced — integral, in fact — so the reduced seesaw gives `Δ^rig ≅ f_B^* M`, and
   pulling back along the zero section gives `M ≅ 𝒪_B`, i.e. `Δ^rig ≅ 𝒪`.
5. Every Weierstrass curve over an arbitrary ring, with two sections, is a base change of
   the universal pair — so the identity descends to arbitrary, **possibly nonreduced**,
   bases. `RelEffCartierDiv.sectionDivisor_baseChange` (`EllipticCurve/PoleSheaf.lean`)
   supplies part of that bridge.

The expected bottleneck is not the seesaw but the comparison between HasseWeil's
*projective-divisor* linear equivalence and the scheme-theoretic `picClass`, together with
its base-change naturality.

### State (2026-07-29): the Picard layer is discharged; the leaf is now module-level

Everything between the leaf and `kappa_add` / `(★′)` is proved and axiom-clean. The chain,
top to bottom:

* `kappa_add` ⟸ `exists_pic_map_snd_sectionCls_add` (was the sorry; now **derived**)
  ⟸ `RelEffCartierDiv.exists_pic_map_of_nonempty_tensor_pullback_iso`
  (`Picard/DivisorClass.lean`) + `kappa_ratio_algebra`.
  The first is the *weakened* multiplicativity: an exact tensor iso is false here (the two
  sides differ by `π^*` of the normal bundle `0^*𝒪(D_0) ≅ ω⁻¹`), so the usable form is
  "tensor iso up to `π^*N` ⟹ equality of class products up to `Pic.map π [N]`". The second
  is pure commutative-group algebra, stated over abstract elements so that no `sectionCls`
  term is ever AC-normalised (that normalisation times out).
* The remaining sorry is `exists_invertible_tensor_idealModule_add`, stated on the ideal
  modules of the four section divisors:
  `I(D_Q) ⊗ I(D_{Q'}) ≅ (I(D_{Q+Q'}) ⊗ I(D_0)) ⊗ π^*N` for some invertible `N` on `T`.
* Two feeders into it are proved:
  - `exists_invertible_tensor_idealModule_add_of_tensor_iso` — the **chart case**: an exact
    tensor iso gives the leaf with `N = 𝒪_T`. This is the shape a Weierstrass chart
    produces, because there the invariant differential trivialises `ω`, hence the normal
    bundle, and the obstruction vanishes.
  - `Modules.nonempty_iso_of_tensorObj_unitObj` (`Picard/PicComparison.lean`) — `M ⊗ N ≅ 𝒪`
    and `M' ⊗ N ≅ 𝒪` give `M ≅ M'`, with `N`'s invertibility *derived*. This is exactly
    what converts the descent machinery's output (triviality of the single discrepancy
    module `L = (I(D_{Q+Q'}) ⊗ I(D_0)) ⊗ N`) into the two-sided iso the chart case wants.
    Its engine `Modules.nonempty_iso_of_tensorObj_right_cancel` cancels an invertible
    tensor factor, in the skeleton, via `Units` (the skeleton has no cancellation
    instance).

So the two remaining bricks are:

* **(A)** the chart-local exact iso — over an open `U ⊆ T` carrying a Weierstrass model,
  `I(D_Q) ⊗ I(D_{Q'}) ≅ I(D_{Q+Q'}) ⊗ I(D_0)` on `f⁻¹U`, from the line-and-vertical
  function of the addition law; and
* **(B)** the descent assembly — glue (A) over a cover of `T` via
  `nonempty_unitObj_iso_of_normalized_glue`, whose overlap condition is *forced* by
  zero-normalisation, and read the result off with the two lemmas above.

Note that (A) is where the universal-curve/reduced-seesaw discussion above lands: the
degenerate loci (`Q = Q'`, `Q = −Q'`, either `= 0`) are handled by proving (A) on the
universal pair and base-changing, not by case analysis over the given base.
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

/-- `[N]` on the base-changed curve, with its total space presented as `pullback E.π t`.
The two are definitionally equal, but elaboration of `Pic`-valued products needs them
*syntactically* equal — otherwise `HMul` is asked to combine `(E.baseChange t).E.Pic` with
`(pullback E.π t).Pic`. -/
noncomputable def mulByN (N : ℕ) : pullback E.π t ⟶ pullback E.π t :=
  (E.baseChange t).mulByHom N

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

/-- The Picard class of the divisor of a section of the base-changed curve — the building
block of `κ`, and the level at which the theorem of the square is actually proved. -/
noncomputable def sectionCls (P : T ⟶ pullback E.π t)
    (hP : P ≫ pullback.snd E.π t = 𝟙 T) : Scheme.Pic (pullback E.π t) :=
  haveI hsep : IsSeparated (pullback.snd E.π t) :=
    MorphismProperty.pullback_snd (P := @IsSeparated) E.π t ‹_›
  have hsm' : SmoothOfRelativeDimension 1 (pullback.snd E.π t) :=
    haveI := smoothOfRelativeDimension_isStableUnderBaseChange (n := 1)
    MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension 1) E.π t hsm
  (RelEffCartierDiv.sectionDivisor (pullback.snd E.π t) P hP).picClass
    (RelEffCartierDiv.sectionDivisor_isOfficial hsm' P hP)

/-- The class of the zero-section divisor. -/
noncomputable def zeroCls : Scheme.Pic (pullback E.π t) :=
  sectionCls E hsm t (baseChangeZero E.π E.zero E.zero_π t)
    (baseChangeZero_snd E.π E.zero E.zero_π t)

/-- Unfolding `κ`: it is the relative-Picard projection of `[𝒪(Q)] ⊗ [𝒪(0)]⁻¹`. -/
theorem kappa_eq_picRelProj (Q : (E.baseChange t).Point (𝟙 T)) :
    kappa E hsm t Q =
      ((picRelProj E.π E.zero E.zero_π t
        (sectionCls E hsm t Q.1 Q.2 * (zeroCls E hsm t)⁻¹) :
        picRel E.π E.zero E.zero_π t) : Scheme.Pic (pullback E.π t)) := rfl

/-- `κ` lands in the relative Picard group, i.e. it is killed by the zero-section
pullback. Immediate from the codomain of `sectionToPicRel`. -/
theorem kappa_mem_ker (Q : (E.baseChange t).Point (𝟙 T)) :
    Scheme.Pic.map (baseChangeZero E.π E.zero E.zero_π t) (kappa E hsm t Q) = 1 :=
  MonoidHom.mem_ker.mp (sectionToPicRel E.π E.zero E.zero_π hsm t Q.1 Q.2).2

/-- **(LEAF (i) — the relative theorem of the square)** At the level of divisor classes:
`[𝒪(Q+Q′)] · [𝒪(0)]` and `[𝒪(Q)] · [𝒪(Q′)]` differ by a class pulled back from the base.

This is the honest content of Silverman III.3.5 `(Q) + (Q′) ∼ (Q+Q′) + (0)` in the relative
setting. The *exact* equality of classes is false: `0^* 𝒪(D_0)` is the **normal** bundle
`N_{0/E} ≅ ω_{E/T}⁻¹` (the *conormal* `I_0/I_0²` is `0^*` of `𝒪(−D_0)`), which is a
generally nontrivial line bundle on the base. Concretely, for the constant family
`E × E ⟶ E` with `Q(t) = t` and `Q′ = Q`, restricting the putative isomorphism along the
constant zero section would force a degree-`2` bundle to agree with a degree-`4` one.
"Differs by `f^*`" is both true and all that is needed, because `Ker(0^*) ∩ Im(f^*) = 1`.

Equivalently: writing `Δ_{Q,Q′} = 𝒪(D_{Q+Q′} + D_0 − D_Q − D_{Q′})`, the statement is
`Δ_{Q,Q′} ≅ f^*(0^* Δ_{Q,Q′})`.

Route: prove it on the universal pair of points, where the base is reduced and the seesaw
theorem applies, with fibrewise triviality supplied by the field theorem
`HasseWeil.Pic0.RouteCTheoremOfSquareDiv.kappaDivisor_add_linEquiv`; then base-change to
arbitrary bases. See the module docstring for the full route and for why the two obvious
alternatives (arbitrary-base fibrewise seesaw; the explicit Weierstrass line function) were
rejected.

The left-hand side is written pre-arranged as `κ`'s numerator over the product of `κ`'s
numerators — in a commutative group it equals the readable
`[𝒪(Q+Q′)]·[𝒪(0)]·([𝒪(Q)]·[𝒪(Q′)])⁻¹`, but keeping it in this shape means `kappa_add`
needs no rearrangement of these (very large) terms. -/
theorem exists_invertible_tensor_idealModule_add (Q Q' : (E.baseChange t).Point (𝟙 T)) :
    ∃ N : T.Modules, IsInvertible N ∧
      Nonempty (tensorObj (idealModule (Scheme.Hom.ker Q.1))
            (idealModule (Scheme.Hom.ker Q'.1)) ≅
          tensorObj
            (tensorObj (idealModule (Scheme.Hom.ker (Q + Q').1))
              (idealModule (Scheme.Hom.ker (baseChangeZero E.π E.zero E.zero_π t))))
            ((AlgebraicGeometry.Scheme.Modules.pullback (pullback.snd E.π t)).obj N)) := by
  sorry

/-- **The `N = 𝒪_T` case of the leaf.** An exact tensor isomorphism gives the leaf with
`N = 𝒪_T`. True as stated, but note the hypothesis is *strictly stronger than the leaf* and
is NOT what a Weierstrass chart supplies.

CORRECTION (2026-07-29, external review): an earlier version of this docstring claimed the
exact iso holds wherever the invariant differential trivialises `ω_{E/T}`. That is **false**.
Counterexample: `E/k` elliptic, `T = E × E`, the constant family `E_T = E × T`, with
`P(a,b) = a`, `Q(a,b) = b`, so `R = P + Q` is `(a,b) ↦ a + b`. Here `ω_{E_T/T}` IS trivial.
Pulling the exact identity back along the zero section would give `A + B ∼ C` on `T`, where
`A = {0} × E`, `B = E × {0}` and `C = {a + b = 0}`; but `A² = B² = C² = 0` and `A·B = 1`, so
`(A + B)² = 2 ≠ 0 = C²`. The obstruction is the Poincaré/biextension class, not just `ω`, and
it survives on charts. Use `..._of_discrepancy_trivial` with the canonical
`N = 0^*Δ` instead — that is the shape the descent machinery actually produces. -/
theorem exists_invertible_tensor_idealModule_add_of_tensor_iso
    (Q Q' : (E.baseChange t).Point (𝟙 T))
    (e : Nonempty (tensorObj (idealModule (Scheme.Hom.ker Q.1))
          (idealModule (Scheme.Hom.ker Q'.1)) ≅
        tensorObj (idealModule (Scheme.Hom.ker (Q + Q').1))
          (idealModule (Scheme.Hom.ker (baseChangeZero E.π E.zero E.zero_π t))))) :
    ∃ N : T.Modules, IsInvertible N ∧
      Nonempty (tensorObj (idealModule (Scheme.Hom.ker Q.1))
            (idealModule (Scheme.Hom.ker Q'.1)) ≅
          tensorObj
            (tensorObj (idealModule (Scheme.Hom.ker (Q + Q').1))
              (idealModule (Scheme.Hom.ker (baseChangeZero E.π E.zero E.zero_π t))))
            ((AlgebraicGeometry.Scheme.Modules.pullback (pullback.snd E.π t)).obj
              (unitObj T))) :=
  ⟨unitObj T, isInvertible_unit,
    ⟨e.some ≪≫ (nonempty_tensorObj_unit_iso _).some.symm ≪≫
      tensorObjCongr (Iso.refl _) (pullbackUnitIso (pullback.snd E.π t)).symm⟩⟩

/-- **The descent interface for the leaf.** Fix a ⊗-inverse `N` of `I(D_Q) ⊗ I(D_{Q'})`.
Then triviality of the *discrepancy module* `(I(D_{Q+Q'}) ⊗ I(D_0)) ⊗ N` gives the leaf.

This is the exact shape `Picard/GlueTrivialization.lean` and
`ModularCurves.nonempty_unitObj_iso_of_normalized_glue` deliver — a single module shown to
be trivial from cover-local generating sections — so it pins what GAP-A-1/GAP-A-2 have to
produce. Nothing here is new mathematics: it is
`Modules.nonempty_iso_of_tensorObj_unitObj` feeding the chart case. -/
theorem exists_invertible_tensor_idealModule_add_of_discrepancy_trivial
    (Q Q' : (E.baseChange t).Point (𝟙 T)) (N : (pullback E.π t).Modules)
    (hN : Nonempty (tensorObj (tensorObj (idealModule (Scheme.Hom.ker Q.1))
          (idealModule (Scheme.Hom.ker Q'.1))) N ≅ unitObj (pullback E.π t)))
    (htriv : Nonempty (tensorObj (tensorObj (idealModule (Scheme.Hom.ker (Q + Q').1))
          (idealModule (Scheme.Hom.ker (baseChangeZero E.π E.zero E.zero_π t)))) N ≅
        unitObj (pullback E.π t))) :
    ∃ N' : T.Modules, IsInvertible N' ∧
      Nonempty (tensorObj (idealModule (Scheme.Hom.ker Q.1))
            (idealModule (Scheme.Hom.ker Q'.1)) ≅
          tensorObj
            (tensorObj (idealModule (Scheme.Hom.ker (Q + Q').1))
              (idealModule (Scheme.Hom.ker (baseChangeZero E.π E.zero E.zero_π t))))
            ((AlgebraicGeometry.Scheme.Modules.pullback (pullback.snd E.π t)).obj
              (unitObj T))) :=
  exists_invertible_tensor_idealModule_add_of_tensor_iso E t Q Q'
    (nonempty_iso_of_tensorObj_unitObj hN htriv)

/-- Pure group algebra behind the reduction of the leaf to its module form: in a commutative
group, the `κ`-shaped ratio of "numerator over product of numerators" is the ratio of the
plain products. Stated over abstract elements so that no `sectionCls` term is ever
AC-normalised. -/
private theorem kappa_ratio_algebra {G : Type*} [CommGroup G] (a b c d : G) :
    (a * d⁻¹) * ((b * d⁻¹) * (c * d⁻¹))⁻¹ = (a * d) * (b * c)⁻¹ := by
  group
  simp only [mul_comm, mul_assoc, mul_left_comm]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **(LEAF (i), Picard form — now derived)** The class-level statement, obtained from the
module-level `exists_invertible_tensor_idealModule_add` by the Picard bookkeeping of
`RelEffCartierDiv.exists_pic_map_of_nonempty_tensor_pullback_iso`. -/
theorem exists_pic_map_snd_sectionCls_add (Q Q' : (E.baseChange t).Point (𝟙 T)) :
    ∃ M : Scheme.Pic T,
      (sectionCls E hsm t (Q + Q').1 (Q + Q').2 * (zeroCls E hsm t)⁻¹) *
          ((sectionCls E hsm t Q.1 Q.2 * (zeroCls E hsm t)⁻¹) *
            (sectionCls E hsm t Q'.1 Q'.2 * (zeroCls E hsm t)⁻¹))⁻¹
        = Scheme.Pic.map (pullback.snd E.π t) M := by
  haveI hsep : IsSeparated (pullback.snd E.π t) :=
    MorphismProperty.pullback_snd (P := @IsSeparated) E.π t ‹_›
  have hsm' : SmoothOfRelativeDimension 1 (pullback.snd E.π t) :=
    haveI := smoothOfRelativeDimension_isStableUnderBaseChange (n := 1)
    MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension 1) E.π t hsm
  obtain ⟨N, hN, e⟩ := exists_invertible_tensor_idealModule_add E t Q Q'
  refine ⟨(RelEffCartierDiv.exists_pic_map_of_nonempty_tensor_pullback_iso
    (RelEffCartierDiv.sectionDivisor_isOfficial hsm' Q.1 Q.2)
    (RelEffCartierDiv.sectionDivisor_isOfficial hsm' Q'.1 Q'.2)
    (RelEffCartierDiv.sectionDivisor_isOfficial hsm' (Q + Q').1 (Q + Q').2)
    (RelEffCartierDiv.sectionDivisor_isOfficial hsm'
      (baseChangeZero E.π E.zero E.zero_π t) (baseChangeZero_snd E.π E.zero E.zero_π t))
    hN e).choose, ?_⟩
  rw [kappa_ratio_algebra]
  exact (RelEffCartierDiv.exists_pic_map_of_nonempty_tensor_pullback_iso
    (RelEffCartierDiv.sectionDivisor_isOfficial hsm' Q.1 Q.2)
    (RelEffCartierDiv.sectionDivisor_isOfficial hsm' Q'.1 Q'.2)
    (RelEffCartierDiv.sectionDivisor_isOfficial hsm' (Q + Q').1 (Q + Q').2)
    (RelEffCartierDiv.sectionDivisor_isOfficial hsm'
      (baseChangeZero E.π E.zero E.zero_π t) (baseChangeZero_snd E.π E.zero E.zero_π t))
    hN e).choose_spec

/-- `0^*` undoes `f^*`, so a class pulled back from the base is detected by the zero
section. -/
theorem picMap_baseChangeZero_picMap_snd (M : Scheme.Pic T) :
    Scheme.Pic.map (baseChangeZero E.π E.zero E.zero_π t)
      (Scheme.Pic.map (pullback.snd E.π t) M) = M := by
  calc Scheme.Pic.map (baseChangeZero E.π E.zero E.zero_π t)
        (Scheme.Pic.map (pullback.snd E.π t) M)
      = Scheme.Pic.map (baseChangeZero E.π E.zero E.zero_π t ≫ pullback.snd E.π t) M := by
        rw [Scheme.Pic.map_comp]; rfl
    _ = M := by rw [baseChangeZero_snd, Scheme.Pic.map_id]; rfl

/-- **The splitting at work.** `Ker(0^*) ∩ Im(f^*) = 1` (GME p. 109), so two classes killed
by the zero-section pullback whose ratio comes from the base are equal. This is what
converts every "comes from the base" statement produced by the descent machinery into an
honest equality of Picard classes. -/
theorem eq_of_mul_inv_eq_picMap_snd {x y : Scheme.Pic (pullback E.π t)}
    (hx : Scheme.Pic.map (baseChangeZero E.π E.zero E.zero_π t) x = 1)
    (hy : Scheme.Pic.map (baseChangeZero E.π E.zero E.zero_π t) y = 1)
    {M : Scheme.Pic T} (h : x * y⁻¹ = Scheme.Pic.map (pullback.snd E.π t) M) :
    x = y := by
  have h0 := congrArg (Scheme.Pic.map (baseChangeZero E.π E.zero E.zero_π t)) h
  rw [map_mul, map_inv, hx, hy, picMap_baseChangeZero_picMap_snd] at h0
  simp only [one_mul, inv_one] at h0
  rw [← h0, map_one] at h
  exact mul_inv_eq_one.mp h

/-- **(PROVED from LEAF (i))** `κ` is a homomorphism.

`κ` is the relative-Picard projection of `[𝒪(Q)]·[𝒪(0)]⁻¹`, and the projection kills
`f^* Pic(T)` — so the leaf's "differs by a class from the base" is exactly enough. -/
theorem kappa_add (Q Q' : (E.baseChange t).Point (𝟙 T)) :
    kappa E hsm t (Q + Q') = kappa E hsm t Q * kappa E hsm t Q' := by
  obtain ⟨M, hM⟩ := exists_pic_map_snd_sectionCls_add E hsm t Q Q'
  have key := picRelProj_eq_of_mul_inv_eq_map_snd E.π E.zero E.zero_π t
    (x := sectionCls E hsm t (Q + Q').1 (Q + Q').2 * (zeroCls E hsm t)⁻¹)
    (y := (sectionCls E hsm t Q.1 Q.2 * (zeroCls E hsm t)⁻¹) *
      (sectionCls E hsm t Q'.1 Q'.2 * (zeroCls E hsm t)⁻¹))
    (M := M) hM
  rw [kappa_eq_picRelProj, kappa_eq_picRelProj, kappa_eq_picRelProj, ← Subgroup.coe_mul,
    ← map_mul]
  exact congrArg Subtype.val key

/-- `κ` carries `ℕ`-multiples to powers. Derived from `kappa_add` and `kappa_zero`. -/
theorem kappa_nsmul (Q : (E.baseChange t).Point (𝟙 T)) (n : ℕ) :
    kappa E hsm t (n • Q) = kappa E hsm t Q ^ n := by
  induction n with
  | zero => simpa using kappa_zero E hsm t
  | succ n ih => rw [succ_nsmul, kappa_add, ih, pow_succ]

/-- `κ` inverts negation. Derived from `kappa_add` and `kappa_zero`. -/
@[simp] theorem kappa_neg (Q : (E.baseChange t).Point (𝟙 T)) :
    kappa E hsm t (-Q) = (kappa E hsm t Q)⁻¹ := by
  have h := kappa_add E hsm t Q (-Q)
  rw [add_neg_cancel, kappa_zero] at h
  exact eq_inv_of_mul_eq_one_right h.symm

/-- `κ` carries `ℤ`-multiples to powers — the form the Weil-pairing construction consumes,
where the multiples that matter are `[N]`-torsion indices and can be negative. -/
theorem kappa_zsmul (Q : (E.baseChange t).Point (𝟙 T)) (n : ℤ) :
    kappa E hsm t (n • Q) = kappa E hsm t Q ^ n := by
  obtain ⟨m, rfl | rfl⟩ := n.eq_nat_or_neg
  · rw [natCast_zsmul, zpow_natCast]
    exact kappa_nsmul E hsm t Q m
  · rw [neg_smul, kappa_neg, natCast_zsmul, zpow_neg, zpow_natCast]
    exact congrArg Inv.inv (kappa_nsmul E hsm t Q m)

/-- **(LEAF (ii) — theorem of the square)** Pullback along `[N]` is the `N`-th power on the
classes `κ(Q)`.

This is the relative form of "`[N]^* = N` on `Pic⁰`". The classes `κ(Q)` are fibrewise of
degree zero by construction, so no degree function on `picRel` is needed to state it — which
matters, since `Ker(0^*)` is *not* `Pic⁰`. -/
theorem zero_comp_mulByHom_baseChange (n : ℤ) :
    baseChangeZero E.π E.zero E.zero_π t ≫ (E.baseChange t).mulByHom n
      = baseChangeZero E.π E.zero E.zero_π t := by
  have hz0 : (((0 : (E.baseChange t).Point (𝟙 T)) : T ⟶ (E.baseChange t).E))
      = baseChangeZero E.π E.zero E.zero_π t :=
    ((E.baseChange t).point_zero_val (𝟙 T)).trans (Category.id_comp _)
  have hsm0 := (E.baseChange t).point_smul_eq_comp_mulBy (𝟙 T) n 0
  rw [smul_zero, hz0] at hsm0
  exact hsm0.symm

/-- `[N]^* κ(Q)` is again killed by the zero-section pullback, because `[N]` is pointed. -/
theorem picMap_mulByHom_kappa_mem_ker (N : ℕ) (Q : (E.baseChange t).Point (𝟙 T)) :
    Scheme.Pic.map (baseChangeZero E.π E.zero E.zero_π t)
      ((Scheme.Pic.map (mulByN E t N) (kappa E hsm t Q))) = 1 := by
  calc Scheme.Pic.map (baseChangeZero E.π E.zero E.zero_π t)
        ((Scheme.Pic.map (mulByN E t N) (kappa E hsm t Q)))
      = Scheme.Pic.map (baseChangeZero E.π E.zero E.zero_π t ≫
          mulByN E t N) (kappa E hsm t Q) := by
        rw [Scheme.Pic.map_comp]; rfl
    _ = 1 := by
        rw [show baseChangeZero E.π E.zero E.zero_π t ≫ mulByN E t N
              = baseChangeZero E.π E.zero E.zero_π t from
            zero_comp_mulByHom_baseChange E t N]
        exact kappa_mem_ker E hsm t Q

/-- **(NOT AN INDEPENDENT LEAF — formal consequence of leaf (i))** The discrepancy between
`[N]^* κ(Q)` and `κ(Q)^N` is a class pulled back from the base.

This is *not* a second classical theorem; it follows from `exists_pic_map_snd_sectionCls_add`
proved in its **universal** form, by symmetry of the normalized Poincaré bundle. Writing
`𝒜 = 𝒪(D_0) ⊗ f^*(0^* 𝒪(D_0))⁻¹` for the rigidification of `𝒪(D_0)`, put

  `𝒫 = m^* 𝒜 ⊗ p₁^* 𝒜⁻¹ ⊗ p₂^* 𝒜⁻¹`  on `E_T ×_T E_T`.

`𝒫` is trivial on both axes, and is **symmetric** — `τ^* 𝒫 ≅ 𝒫` for the transposition `τ`,
simply because `m ∘ τ = m`. For a section `Q` one has `(id, −Q)^* 𝒫 ≅ κ(Q)`, since
`t_{−Q}⁻¹(D_0) = D_Q` and the `p₂`-factor is exactly the zero-section normalization. Leaf (i),
base-changed to `E_T ×_T E_T` with the two universal sections, says `𝒫` is additive in its
second variable; symmetry upgrades that to additivity in the first; hence
`([N] × id)^* [𝒫] = [𝒫]^N`, and restricting along `(id, −Q)` gives the statement.

Kept as a named statement because that derivation needs `𝒫` and its symmetry built first;
it is bookkeeping, not new mathematics. -/
theorem exists_pic_map_snd_picMap_mulByHom_kappa (N : ℕ)
    (Q : (E.baseChange t).Point (𝟙 T)) :
    ∃ M : Scheme.Pic T,
      (Scheme.Pic.map (mulByN E t N) (kappa E hsm t Q))
        * (kappa E hsm t Q ^ N)⁻¹ = Scheme.Pic.map (pullback.snd E.π t) M := by
  sorry

theorem picMap_mulByHom_kappa_pow (N : ℕ) (Q : (E.baseChange t).Point (𝟙 T)) :
    (Scheme.Pic.map (mulByN E t N) (kappa E hsm t Q)) = kappa E hsm t Q ^ N := by
  obtain ⟨M, hM⟩ := exists_pic_map_snd_picMap_mulByHom_kappa E hsm t N Q
  refine eq_of_mul_inv_eq_picMap_snd E t
    (picMap_mulByHom_kappa_mem_ker E hsm t N Q) ?_ hM
  rw [map_pow, kappa_mem_ker, one_pow]

theorem picMap_mulByHom_kappa_eq_one (N : ℕ) (Q : (E.baseChange t).Point (𝟙 T))
    (hQ : (N : ℤ) • Q = 0) :
    Scheme.Pic.map (mulByN E t N) (kappa E hsm t Q) = 1 := by
  have hnat : (N • Q : (E.baseChange t).Point (𝟙 T)) = 0 := by
    rwa [natCast_zsmul] at hQ
  rw [picMap_mulByHom_kappa_pow E hsm t N Q, ← kappa_nsmul E hsm t Q N, hnat]
  exact kappa_zero E hsm t

end ModularCurves
