/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.Moduli.EllCategory
import ModularCurves.Moduli.GammaH
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.AlgebraicGeometry.Sites.BigZariski
import Mathlib.CategoryTheory.Sites.Descent.IsStack

/-!
# The stack of elliptic curves: descent statements (the "stack bridge")

Loeffler, remark after Def 3.7.1 (verbatim): *"The category `Ell/R` is `Sch/Y` for a `Y`
that does not exist. If the functor `S ↦ {ell. curves/S}` were representable by some
`(Y, E/Y)`, then the objects of `Ell/R` would be just maps `S → Y`. This is the idea of
stacks."*

Per the project's design decision (KM formalism + stack bridge), the working engine is
`Moduli/EllCategory.lean`; this file carries the honest stack-theoretic *statements*:

1. **Torsor descent for rigidified curves** (`levelledCurve_descent_of_torsor`, the
   DEF-2 replacement, 2026-07-05): levelled elliptic curves descend along finite-group
   torsors — the form GME Lemma 2.6.7 actually uses, where Aut-triviality of the level
   makes the cocycle automatic. (The earlier cocycle-free fppf-descent statement was
   FALSE — sextic-twist obstruction — and was removed by the adversarial pass.)
   Source: GME Lemma 2.6.7 (p. 148); SGA 1 VIII via stream DESC.

2. **The pseudofunctor packaging** (`T-E8`, statement deferred): assembling
   `S ↦ (groupoid of elliptic curves over S)` into a `Pseudofunctor` and proving
   `Pseudofunctor.IsStack` for the fppf topology, using mathlib's
   `CategoryTheory.Sites.Descent.IsStack`. Deferred because constructing the
   pseudofunctor (coherence data for pullback composition) is genuine infrastructure —
   ticket `T-E8` — and *no theorem of this project consumes it*; it is the
   promised bridge artifact, not load-bearing for `Y(ρ,p)`.

The fppf Grothendieck topology used below is obtained from mathlib's `fppfPrecoverage`.
-/

open AlgebraicGeometry CategoryTheory Limits

attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory
  CategoryTheory.Over.braidedCategory

universe u

namespace ModularCurves

-- The fppf topology is mathlib's `AlgebraicGeometry.fppfTopology`
-- (`fppfPrecoverage.toGrothendieck`) — do not redefine it here.

/-- **(T-E10 v2, descent of rigidified curves along a finite-group torsor — the form
GME Lemma 2.6.7 actually uses; ADVERSARIAL FIX 2026-07-05, DEF-2)**

The previous cocycle-free fppf statement was rejected by the adversarial pass: a mere
isomorphism of the two pullbacks does NOT make a descent datum effective in general
(sextic-twist obstruction `H¹(G, μ₆) ≠ 0` for `j = 0`); SGA 1 VIII requires the
cocycle. In the rigidified situation the cocycle is automatic ("Since
`Aut_{E/S}(𝐄, φ_N) = {1_E}` … `θ(g) ∘ g^*θ(h) = θ(hg)`", GME p. 148), which is the
form the `Y(N)`-over-ℤ chain consumes:

Let `f : T' ⟶ T`, let `G` be a finite group acting on `T'` over `T` (via `σ`), with
the torsor condition: the canonical map `∐_G T' ⟶ T' ×_T T'`, `(g, t) ↦ (g·t, t)`,
is an isomorphism. Let `(E', L')` be an elliptic curve with (naive) full level-`N`
structure over `T'`, `N ≥ 3` invertible, such that for every `g ∈ G` the `g`-twist
`(E', L')` pulled along `σ g` is isomorphic to `(E', L')` in the levelled groupoid
(mere existence — no compatibility demanded). Then `(E', L')` descends: there is
`(E, L)` over `T` whose pullback along `f` is levelled-isomorphic to `(E', L')`.
General fppf-sheaf effectivity remains `T-E8` (mathlib `DescentData` packaging).
Source: GME Lemma 2.6.7 with proof (p. 148); black box BB-DESC retired to stream
DESC for this form (Galois/torsor case — AINTLIB Galois-descent engines apply). -/
theorem levelledCurve_descent_of_torsor {T T' : Scheme.{u}} (f : T' ⟶ T)
    [Flat f] [LocallyOfFinitePresentation f] [Surjective f]
    (G : Type u) [Group G] [Finite G] (σ : G →* Aut (Over.mk f))
    (htorsor : IsIso ((Limits.Sigma.desc (fun g : G =>
      Limits.pullback.lift (f := f) (g := f) ((σ g).hom.left) (𝟙 T')
        (by rw [Category.id_comp]; exact Over.w (σ g).hom))) :
      (∐ fun _ : G => T') ⟶ Limits.pullback f f))
    (N : ℕ) [NeZero N] (hN : 3 ≤ N) (hinv : IsUnit (N : Γ(T', ⊤)))
    (E' : EllipticCurve T') (L' : E'.FullLevelPt N)
    (hdesc : ∀ g : G, Nonempty
      ((⟨E'.baseChange ((σ g).hom.left), EllipticCurve.FullLevelPt.pullAlong
          ((σ g).hom.left) L'⟩ : Σ E : EllipticCurve T', E.FullLevelPt N) ≅
        ⟨E', L'⟩)) :
    ∃ (E : EllipticCurve T) (L : E.FullLevelPt N), Nonempty
      ((⟨E.baseChange f, EllipticCurve.FullLevelPt.pullAlong f L⟩ :
          Σ E₀ : EllipticCurve T', E₀.FullLevelPt N) ≅ ⟨E', L'⟩) := by sorry

/-- **(stream-DESC, morphism descent along an effective epimorphism — the geometric heart
of fppf gluing.)** If a morphism `ζ' : T' ⟶ Z` coequalizes the kernel pair of `f`
(`pr₁ ≫ ζ' = pr₂ ≫ ζ'`), it factors uniquely through `f`. For an **fppf cover** `f`
(flat + locally of finite presentation + surjective) this hypothesis makes `f` an
effective epimorphism (mathlib's `EffectiveEpi` instance, from subcanonicity of the fppf
topology, `AlgebraicGeometry.Sites.Fpqc`), so maps to any scheme `Z` descend — this is
the "descent of morphisms" half of subcanonicity that `moduliProblem_fppf_descent`
consumes. Source: SGA 1 VIII (fppf covers are effective epis); Stacks 023Q. -/
theorem descend_hom_of_effectiveEpi {T T' Z : Scheme.{u}} (f : T' ⟶ T) [EffectiveEpi f]
    (ζ' : T' ⟶ Z)
    (hcoeq : Limits.pullback.fst f f ≫ ζ' = Limits.pullback.snd f f ≫ ζ') :
    ∃! ζ : T ⟶ Z, f ≫ ζ = ζ' := by
  -- Any pair `g₁, g₂` coequalized by `f` factors through the kernel pair, so `ζ'`
  -- coequalizes it too.
  have h : ∀ {W : Scheme.{u}} (g₁ g₂ : W ⟶ T'), g₁ ≫ f = g₂ ≫ f → g₁ ≫ ζ' = g₂ ≫ ζ' := by
    intro W g₁ g₂ hg
    have hl1 : Limits.pullback.lift g₁ g₂ hg ≫ Limits.pullback.fst f f = g₁ :=
      Limits.pullback.lift_fst _ _ _
    have hl2 : Limits.pullback.lift g₁ g₂ hg ≫ Limits.pullback.snd f f = g₂ :=
      Limits.pullback.lift_snd _ _ _
    calc g₁ ≫ ζ'
        = (Limits.pullback.lift g₁ g₂ hg ≫ Limits.pullback.fst f f) ≫ ζ' := by rw [hl1]
      _ = (Limits.pullback.lift g₁ g₂ hg ≫ Limits.pullback.snd f f) ≫ ζ' := by
          rw [Category.assoc, hcoeq, Category.assoc]
      _ = g₂ ≫ ζ' := by rw [hl2]
  exact ⟨EffectiveEpi.desc f ζ' h, EffectiveEpi.fac f ζ' h,
    fun ζ hζ => EffectiveEpi.uniq f ζ' h ζ hζ⟩

/-- **(T-E11, separatedness half of "the moduli problems are fppf sheaves")** For a
relatively representable moduli problem `P`, sections of `P` are determined fppf-locally:
restriction along an fppf cover `f : T' ⟶ T` is injective on `P`-values. (The gluing half
needs the descent-data vocabulary of `T-E8` and is recorded there.)

SOURCE STATUS (adversarial pass 2026-07-06): PENDING-SOURCE — KM 4.1–4.2 is not in
hand (Ch. 4 outside the preview) and Loeffler 3.8.2 does not state fppf-separatedness;
this is a formal lemma whose proof consumes (i) the `RelativelyRepresentable`
naturality clause and (ii) "fppf covers are epimorphisms of schemes" (subcanonicity,
SGA 1 VIII) — the latter is a mathlib-gap check for stream DESC. -/
theorem moduliProblem_fppf_separated (R : CommRingCat.{u}) (P : ModuliProblem R)
    (hP : P.RelativelyRepresentable) :
    ∀ {T T' : Scheme.{u}} (f : T' ⟶ T), Flat f → LocallyOfFinitePresentation f →
      Surjective f → ∀ (X : EllObj R) (g : T ⟶ X.base)
      (a b : P.obj (Opposite.op (X.pullbackAlong g))),
      P.map (X.pullbackAlongMap g f).op a = P.map (X.pullbackAlongMap g f).op b →
      a = b := by
  intro T T' f hflat hlfp hsurj X g a b hab
  haveI := hflat; haveI := hsurj
  haveI : Epi f := AlgebraicGeometry.Flat.epi_of_flat_of_surjective f
  -- unpack the relative-representability datum for `X`
  obtain ⟨Z, fZ, eqv, hnat⟩ := hP X
  -- transport `a`, `b` back to `Z`-points over `g`
  set ha := (eqv g).symm a
  set hb := (eqv g).symm b
  have haval : eqv g ha = a := (eqv g).apply_symm_apply a
  have hbval : eqv g hb = b := (eqv g).apply_symm_apply b
  -- the restriction of `a` along `f` is `eqv` of the restricted `Z`-point (naturality)
  have hra : P.map (X.pullbackAlongMap g f).op a =
      eqv (f ≫ g) ⟨f ≫ ha.1, by rw [Category.assoc, ha.2]⟩ := by
    rw [← haval, hnat g f ha]
  have hrb : P.map (X.pullbackAlongMap g f).op b =
      eqv (f ≫ g) ⟨f ≫ hb.1, by rw [Category.assoc, hb.2]⟩ := by
    rw [← hbval, hnat g f hb]
  rw [hra, hrb] at hab
  -- `eqv` is injective, so the two restricted `Z`-points agree
  have hsub := (eqv (f ≫ g)).injective hab
  have hfeq : f ≫ ha.1 = f ≫ hb.1 := congrArg Subtype.val hsub
  -- cancel the epi `f`
  have h1 : ha.1 = hb.1 := (cancel_epi f).mp hfeq
  have : ha = hb := Subtype.ext h1
  rw [← haval, ← hbval, this]

/-- **(stream-DESC, gluing half of "the moduli problems are fppf sheaves" — dual to
`moduliProblem_fppf_separated`).** For a relatively-representable moduli problem `P` and an
**fppf cover** `f : T' ⟶ T` (flat + locally of finite presentation + surjective), a
`P`-value `a'` over `T'` whose two pullbacks to the kernel pair `T' ×_T T'` agree descends
to a `P`-value over `T` (restricting back to `a'`). Together with
`moduliProblem_fppf_separated` this says relatively representable moduli problems are fppf
sheaves.

The proof descends the classifying map into the representing scheme `Z` along the effective
epimorphism `f` (mathlib's `EffectiveEpi` instance for fppf covers, via
`descend_hom_of_effectiveEpi`), then transports back through the representing bijection
`eqv`. The cocycle hypothesis carries a `cast` because the two kernel-pair projections agree
only after composing with `f`, so the two restriction targets are propositionally — not
definitionally — equal. Source: SGA 1 VIII; Stacks 023Q (fppf descent of morphisms). -/
theorem moduliProblem_fppf_descent (R : CommRingCat.{u}) (P : ModuliProblem R)
    (hP : P.RelativelyRepresentable) {T T' : Scheme.{u}} (f : T' ⟶ T)
    [Flat f] [LocallyOfFinitePresentation f] [Surjective f]
    (X : EllObj R) (g : T ⟶ X.base)
    (a' : P.obj (Opposite.op (X.pullbackAlong (f ≫ g))))
    (hcocyc : P.map (X.pullbackAlongMap (f ≫ g) (Limits.pullback.fst f f)).op a' =
      cast (congrArg (fun q => P.obj (Opposite.op (X.pullbackAlong q)))
          (show Limits.pullback.snd f f ≫ (f ≫ g) = Limits.pullback.fst f f ≫ (f ≫ g) by
            simp only [← Category.assoc, Limits.pullback.condition]))
        (P.map (X.pullbackAlongMap (f ≫ g) (Limits.pullback.snd f f)).op a')) :
    ∃ a : P.obj (Opposite.op (X.pullbackAlong g)),
      P.map (X.pullbackAlongMap g f).op a = a' := by
  haveI : Epi f := AlgebraicGeometry.Flat.epi_of_flat_of_surjective f
  obtain ⟨Z, fZ, eqv, hnat⟩ := hP X
  set hz := (eqv (f ≫ g)).symm a'
  have hzval : eqv (f ≫ g) hz = a' := (eqv (f ≫ g)).apply_symm_apply a'
  -- Transporting an `eqv`-value between two equal base maps only permutes the (irrelevant)
  -- factorisation proof, so it commutes with the underlying map.
  have transport_eqv : ∀ (q₁ q₂ : Limits.pullback f f ⟶ X.base) (hq : q₂ = q₁)
      (m : Limits.pullback f f ⟶ Z) (pf1 : m ≫ fZ = q₁) (pf2 : m ≫ fZ = q₂),
      cast (congrArg (fun q => P.obj (Opposite.op (X.pullbackAlong q))) hq) (eqv q₂ ⟨m, pf2⟩)
        = eqv q₁ ⟨m, pf1⟩ := by
    intro q₁ q₂ hq m pf1 pf2
    subst hq
    rfl
  -- The classifying map `hz.1 : T' ⟶ Z` coequalizes the kernel pair of `f`.
  have hcoeq : Limits.pullback.fst f f ≫ hz.1 = Limits.pullback.snd f f ≫ hz.1 := by
    have E1 := hnat (f ≫ g) (Limits.pullback.fst f f) hz
    have E2 := hnat (f ≫ g) (Limits.pullback.snd f f) hz
    rw [hzval] at E1 E2
    have key : eqv (Limits.pullback.fst f f ≫ (f ≫ g))
          ⟨Limits.pullback.fst f f ≫ hz.1, by rw [Category.assoc, hz.2]⟩ =
        eqv (Limits.pullback.fst f f ≫ (f ≫ g))
          ⟨Limits.pullback.snd f f ≫ hz.1, by
            rw [Category.assoc, hz.2]
            simp only [← Category.assoc, Limits.pullback.condition]⟩ := by
      rw [E1, hcocyc, ← E2]
      exact transport_eqv (Limits.pullback.fst f f ≫ (f ≫ g))
        (Limits.pullback.snd f f ≫ (f ≫ g))
        (by simp only [← Category.assoc, Limits.pullback.condition]) _ _ _
    exact congrArg Subtype.val ((eqv (Limits.pullback.fst f f ≫ (f ≫ g))).injective key)
  -- Descend the classifying map along the effective epimorphism `f`, then transport back.
  obtain ⟨ζ, hζ, -⟩ := descend_hom_of_effectiveEpi f hz.1 hcoeq
  have hζfZ : ζ ≫ fZ = g := by
    have hfe : f ≫ (ζ ≫ fZ) = f ≫ g := by rw [← Category.assoc, hζ]; exact hz.2
    exact (cancel_epi f).mp hfe
  refine ⟨eqv g ⟨ζ, hζfZ⟩, ?_⟩
  have hkey := hnat g f ⟨ζ, hζfZ⟩
  rw [← hkey]
  have harg : (⟨f ≫ ζ, by rw [Category.assoc, hζfZ]⟩ :
      { h : T' ⟶ Z // h ≫ fZ = f ≫ g }) = hz := Subtype.ext hζ
  exact (congrArg (eqv (f ≫ g)) harg).trans hzval

end ModularCurves
