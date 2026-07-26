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
`ModularCurves.eq_one_of_pullback_eq_one` (`EllipticCurve/SectionRigidity.lean`, proved)
makes the normalized choice unique.

## Available machinery for the two leaves (both are now LOCAL ON THE BASE)

The descent workhorse is proved and axiom-clean, so neither leaf needs a global argument:

* `AlgebraicGeometry.Scheme.Modules.nonempty_unitObj_iso_of_glue`
  (`Picard/GlueTrivialization.lean`) — an `𝒪`-module with cover-local generating sections
  agreeing on overlaps is trivial. Sections glue by the sheaf axiom; the glued global
  section is tested by `isIso_of_bijective_app_on_cover`.
* `ModularCurves.nonempty_unitObj_iso_of_normalized_glue` (`Picard/RigidDescent.lean`) —
  the elliptic-curve form: generating sections over the `f`-preimages of a cover **of the
  base**, whose overlap comparison units are `1` along the zero section, give triviality.
  Overlap agreement is *forced*, not checked: two generating sections differ by a unit, and
  a unit that is `1` on the zero section is `1`.

What remains for each leaf is therefore the **local** input: on a Weierstrass chart of the
base, the explicit line-and-vertical function realizing
`(Q) + (Q′) − (Q+Q′) − (0) = div(ℓ/v)` (Silverman III.3.5; the field-level template is
`HasseWeil.Pic0.TheoremOfSquareDivisorForm.kappaDivisor_add_linEquiv`, proved
unconditionally in any characteristic), normalized along the zero section.
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

/-- `κ` lands in the relative Picard group, i.e. it is killed by the zero-section
pullback. Immediate from the codomain of `sectionToPicRel`. -/
theorem kappa_mem_ker (Q : (E.baseChange t).Point (𝟙 T)) :
    Scheme.Pic.map (baseChangeZero E.π E.zero E.zero_π t) (kappa E hsm t Q) = 1 :=
  MonoidHom.mem_ker.mp (sectionToPicRel E.π E.zero E.zero_π hsm t Q.1 Q.2).2

/-- **(LEAF (i) — relative theorem of the square, "comes from the base" form)** The
discrepancy in the additivity of `κ` is a class pulled back from the base.

This is the exact shape the descent machinery produces. `Picard/RigidDescent.lean`'s
`nonempty_unitObj_iso_of_normalized_glue` says: a module with generating sections over the
`f`-preimages of a cover of the base, normalized along the zero section, is trivial — i.e.
the difference bundle, after rigidification, is `f^*` of something. Only that is needed;
the *exact* tensor isomorphism `I(D_Q) ⊗ I(D_{Q′}) ≅ I(D_{Q+Q′}) ⊗ I(D_0)` is **false** in
general, because `I(D_0)` restricted to the zero section is the conormal bundle.

Field-level template, proved unconditionally in any characteristic:
`HasseWeil.Pic0.TheoremOfSquareDivisorForm.kappaDivisor_add_linEquiv` (Silverman III.3.5).
Its proof is valuation-theoretic and does not transport to a base ring; the relative
statement is the ideal identity `I(D_P)·I(D_Q)·I(D_{−(P+Q)}) = (ℓ)` together with
`I(D_{P+Q})·I(D_{−(P+Q)}) = (v)` on a chart where the sections are in general position. -/
theorem exists_pic_map_snd_kappa_add (Q Q' : (E.baseChange t).Point (𝟙 T)) :
    ∃ M : Scheme.Pic T, kappa E hsm t (Q + Q') * (kappa E hsm t Q * kappa E hsm t Q')⁻¹
      = Scheme.Pic.map (pullback.snd E.π t) M := by
  sorry

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

Both sides lie in `Ker(0^*)`, and their ratio comes from the base by
`exists_pic_map_snd_kappa_add`; `eq_of_mul_inv_eq_picMap_snd` then closes it. -/
theorem kappa_add (Q Q' : (E.baseChange t).Point (𝟙 T)) :
    kappa E hsm t (Q + Q') = kappa E hsm t Q * kappa E hsm t Q' := by
  obtain ⟨M, hM⟩ := exists_pic_map_snd_kappa_add E hsm t Q Q'
  refine eq_of_mul_inv_eq_picMap_snd E t (kappa_mem_ker E hsm t (Q + Q')) ?_ hM
  rw [map_mul, kappa_mem_ker, kappa_mem_ker, one_mul]

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

/-- **(LEAF (ii) — relative theorem of the square for `[N]`, "comes from the base" form)**
The discrepancy between `[N]^* κ(Q)` and `κ(Q)^N` is a class pulled back from the base.

As for leaf (i), this is the shape `Picard/RigidDescent.lean` produces, and it is all that
is needed: the exact isomorphism is false, since `[N]^*` of the conormal bundle at the zero
section is not its `N`-th power. -/
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
