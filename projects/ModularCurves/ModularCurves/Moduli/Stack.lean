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
import ModularCurves.ForMathlib.BaseChangeAlongCompat

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

/-- **([R-sheaf-P], Zariski 2-chart gluing for relatively representable moduli problems).**
Assembling the two fppf-sheaf halves (`moduliProblem_fppf_separated` +
`moduliProblem_fppf_descent`) into a genuine Zariski recollement statement: for a
relatively representable moduli problem `P`, an `Ell/R`-object `X` and a two-element open
cover `U ⊔ V = ⊤` of `X.base`, a pair of `P`-sections on the two charts that agree on the
scheme-theoretic overlap `U ∩ V` (the fibre product `pullback U.ι V.ι`) glues to a *unique*
`P`-section over `X` (i.e. over `X.pullbackAlong (𝟙 X.base)`, the identity-restriction of
`X`) restricting to the given ones.

The cover is the coproduct `(U : Scheme) ⨿ (V : Scheme) ⟶ X.base` copairing the two open
immersions; it is flat + locally of finite presentation + surjective (an fppf cover), so
the two file lemmas apply: existence is `moduliProblem_fppf_descent` (the cocycle over the
kernel pair `(U⨿V) ×_{X.base} (U⨿V)` is supplied by `hagree` after the extensive
decomposition into the four pieces `U×U, U×V, V×U, V×V`), and uniqueness is
`moduliProblem_fppf_separated`. Source: SGA 1 VIII (fppf covers are effective epis);
Zariski covers are fppf. -/
theorem moduliProblem_zariski_glue (R : CommRingCat.{u}) (P : ModuliProblem R)
    (hP : P.RelativelyRepresentable) (X : EllObj R) (U V : X.base.Opens)
    (hUV : U ⊔ V = ⊤)
    (sU : P.obj (Opposite.op (X.pullbackAlong U.ι)))
    (sV : P.obj (Opposite.op (X.pullbackAlong V.ι)))
    (hagree : P.map (X.pullbackAlongMap U.ι (Limits.pullback.fst U.ι V.ι)).op sU =
      cast (congrArg (fun q => P.obj (Opposite.op (X.pullbackAlong q)))
          (Limits.pullback.condition (f := U.ι) (g := V.ι)).symm)
        (P.map (X.pullbackAlongMap V.ι (Limits.pullback.snd U.ι V.ι)).op sV)) :
    ∃! s : P.obj (Opposite.op (X.pullbackAlong (𝟙 X.base))),
      cast (congrArg (fun q => P.obj (Opposite.op (X.pullbackAlong q))) (Category.comp_id U.ι))
          (P.map (X.pullbackAlongMap (𝟙 X.base) U.ι).op s) = sU ∧
      cast (congrArg (fun q => P.obj (Opposite.op (X.pullbackAlong q))) (Category.comp_id V.ι))
          (P.map (X.pullbackAlongMap (𝟙 X.base) V.ι).op s) = sV := by
  obtain ⟨Z, fZ, eqv, hnat⟩ := hP X
  -- transporting an `eqv`-value between two equal base maps only permutes the (irrelevant)
  -- factorisation proof, so it commutes with the underlying map (cf. `moduliProblem_fppf_descent`)
  have transport_eqv : ∀ {T : Scheme.{u}} (q₁ q₂ : T ⟶ X.base) (hq : q₂ = q₁)
      (m : T ⟶ Z) (pf1 : m ≫ fZ = q₁) (pf2 : m ≫ fZ = q₂),
      cast (congrArg (fun q => P.obj (Opposite.op (X.pullbackAlong q))) hq) (eqv q₂ ⟨m, pf2⟩)
        = eqv q₁ ⟨m, pf1⟩ := by
    intro T q₁ q₂ hq m pf1 pf2
    subst hq
    rfl
  -- classify the two chart sections as lifts into the representing scheme `Z`
  set hU := (eqv U.ι).symm sU with hUdef
  set hV := (eqv V.ι).symm sV with hVdef
  have hUval : eqv U.ι hU = sU := (eqv U.ι).apply_symm_apply sU
  have hVval : eqv V.ι hV = sV := (eqv V.ι).apply_symm_apply sV
  -- the two-element coproduct cover of `X.base` (`true ↦ U`, `false ↦ V`)
  let chart : Bool → Scheme.{u} := fun b => b.casesOn V.toScheme U.toScheme
  let fhom : (b : Bool) → chart b ⟶ X.base := fun b => b.casesOn V.ι U.ι
  let hlift : (b : Bool) → chart b ⟶ Z := fun b => b.casesOn hV.1 hU.1
  have hfhom_true : fhom true = U.ι := rfl
  have hfhom_false : fhom false = V.ι := rfl
  have hlift_true : hlift true = hU.1 := rfl
  have hlift_false : hlift false = hV.1 := rfl
  -- the cover is an fppf cover: flat + locally of finite presentation + surjective
  letI hff_flat : ∀ b, Flat (fhom b) := by
    intro b; cases b with
    | false => exact inferInstanceAs (Flat V.ι)
    | true => exact inferInstanceAs (Flat U.ι)
  letI hff_lfp : ∀ b, LocallyOfFinitePresentation (fhom b) := by
    intro b; cases b with
    | false => exact inferInstanceAs (LocallyOfFinitePresentation V.ι)
    | true => exact inferInstanceAs (LocallyOfFinitePresentation U.ι)
  haveI hFflat : Flat (Limits.Sigma.desc fhom) :=
    IsZariskiLocalAtSource.sigmaDesc hff_flat
  haveI hFlfp : LocallyOfFinitePresentation (Limits.Sigma.desc fhom) :=
    IsZariskiLocalAtSource.sigmaDesc hff_lfp
  haveI hFsurj : Surjective (Limits.Sigma.desc fhom) :=
    Surjective.sigmaDesc_of_union_range_eq_univ (by
      apply Set.eq_univ_of_forall
      intro x
      rw [Set.mem_iUnion]
      have hx : x ∈ (⊤ : X.base.Opens) := trivial
      rw [← hUV] at hx
      rcases hx with hxU | hxV
      · exact ⟨true, by rw [hfhom_true, Scheme.Opens.range_ι]; exact hxU⟩
      · exact ⟨false, by rw [hfhom_false, Scheme.Opens.range_ι]; exact hxV⟩)
  -- overlap agreement, read off `hagree` on the fibre product `U ∩ V = pullback U.ι V.ι`
  have AGREE : Limits.pullback.fst U.ι V.ι ≫ hU.1 = Limits.pullback.snd U.ι V.ι ≫ hV.1 := by
    have E1 := hnat U.ι (Limits.pullback.fst U.ι V.ι) hU
    have E2 := hnat V.ι (Limits.pullback.snd U.ι V.ι) hV
    rw [hUval] at E1
    rw [hVval] at E2
    have key : eqv (Limits.pullback.fst U.ι V.ι ≫ U.ι)
          ⟨Limits.pullback.fst U.ι V.ι ≫ hU.1, by rw [Category.assoc, hU.2]⟩ =
        eqv (Limits.pullback.fst U.ι V.ι ≫ U.ι)
          ⟨Limits.pullback.snd U.ι V.ι ≫ hV.1, by
            rw [Category.assoc, hV.2, ← Limits.pullback.condition]⟩ := by
      rw [E1, hagree, ← E2]
      exact transport_eqv (Limits.pullback.fst U.ι V.ι ≫ U.ι)
        (Limits.pullback.snd U.ι V.ι ≫ V.ι)
        (Limits.pullback.condition (f := U.ι) (g := V.ι)).symm _ _ _
    exact congrArg Subtype.val ((eqv (Limits.pullback.fst U.ι V.ι ≫ U.ι)).injective key)
  -- the classifying map `Sigma.desc hlift` coequalizes the kernel pair of the cover: check on
  -- the four pieces `U×U, U×V, V×U, V×V` via the extensive decomposition of the kernel pair
  have COEQ : Limits.pullback.fst (Limits.Sigma.desc fhom) (Limits.Sigma.desc fhom) ≫
        Limits.Sigma.desc hlift =
      Limits.pullback.snd (Limits.Sigma.desc fhom) (Limits.Sigma.desc fhom) ≫
        Limits.Sigma.desc hlift := by
    have hpb := FinitaryPreExtensive.isPullback_sigmaDesc fhom fhom
    refine (cancel_epi hpb.isoPullback.hom).mp ?_
    rw [← Category.assoc, ← Category.assoc, hpb.isoPullback_hom_fst, hpb.isoPullback_hom_snd]
    refine Limits.Sigma.hom_ext _ _ fun p => ?_
    simp only [Limits.Sigma.ι_desc_assoc, Category.assoc, Limits.Sigma.ι_desc]
    obtain ⟨b1, b2⟩ := p
    cases b1 <;> cases b2 <;>
      simp only [hlift_true, hlift_false]
    · -- V × V (diagonal): `pullback.fst = pullback.snd` since `V.ι` is mono
      rw [show Limits.pullback.fst V.ι V.ι = Limits.pullback.snd V.ι V.ι from
        (cancel_mono V.ι).mp Limits.pullback.condition]
    · -- V × U (cross): from `AGREE` via the pullback symmetry
      refine (cancel_epi (Limits.pullbackSymmetry U.ι V.ι).hom).mp ?_
      rw [Limits.pullbackSymmetry_hom_comp_fst_assoc, Limits.pullbackSymmetry_hom_comp_snd_assoc]
      exact AGREE.symm
    · -- U × V (cross): exactly `AGREE`
      exact AGREE
    · -- U × U (diagonal): `pullback.fst = pullback.snd` since `U.ι` is mono
      rw [show Limits.pullback.fst U.ι U.ι = Limits.pullback.snd U.ι U.ι from
        (cancel_mono U.ι).mp Limits.pullback.condition]
  -- assemble the two chart-lifts into a single classifying lift over the cover
  have hlift_comp_fZ : ∀ b, hlift b ≫ fZ = fhom b := by
    intro b; cases b
    · exact hV.2
    · exact hU.2
  have hz2 : Limits.Sigma.desc hlift ≫ fZ = Limits.Sigma.desc fhom ≫ 𝟙 X.base := by
    rw [Category.comp_id]
    refine Limits.Sigma.hom_ext _ _ fun b => ?_
    simp only [Limits.Sigma.ι_desc_assoc, Limits.Sigma.ι_desc, hlift_comp_fZ]
  have hcocyc : P.map (X.pullbackAlongMap (Limits.Sigma.desc fhom ≫ 𝟙 X.base)
        (Limits.pullback.fst (Limits.Sigma.desc fhom) (Limits.Sigma.desc fhom))).op
        (eqv (Limits.Sigma.desc fhom ≫ 𝟙 X.base) ⟨Limits.Sigma.desc hlift, hz2⟩) =
      cast (congrArg (fun q => P.obj (Opposite.op (X.pullbackAlong q)))
          (show Limits.pullback.snd (Limits.Sigma.desc fhom) (Limits.Sigma.desc fhom) ≫
              (Limits.Sigma.desc fhom ≫ 𝟙 X.base) =
            Limits.pullback.fst (Limits.Sigma.desc fhom) (Limits.Sigma.desc fhom) ≫
              (Limits.Sigma.desc fhom ≫ 𝟙 X.base) by
            simp only [← Category.assoc, Limits.pullback.condition]))
        (P.map (X.pullbackAlongMap (Limits.Sigma.desc fhom ≫ 𝟙 X.base)
          (Limits.pullback.snd (Limits.Sigma.desc fhom) (Limits.Sigma.desc fhom))).op
          (eqv (Limits.Sigma.desc fhom ≫ 𝟙 X.base) ⟨Limits.Sigma.desc hlift, hz2⟩)) := by
    set hz : { h // h ≫ fZ = Limits.Sigma.desc fhom ≫ 𝟙 X.base } :=
      ⟨Limits.Sigma.desc hlift, hz2⟩ with hzdef
    have COEQ2 : Limits.pullback.fst (Limits.Sigma.desc fhom) (Limits.Sigma.desc fhom) ≫ hz.1 =
        Limits.pullback.snd (Limits.Sigma.desc fhom) (Limits.Sigma.desc fhom) ≫ hz.1 := COEQ
    rw [← hnat (Limits.Sigma.desc fhom ≫ 𝟙 X.base)
        (Limits.pullback.fst (Limits.Sigma.desc fhom) (Limits.Sigma.desc fhom)) hz,
      ← hnat (Limits.Sigma.desc fhom ≫ 𝟙 X.base)
        (Limits.pullback.snd (Limits.Sigma.desc fhom) (Limits.Sigma.desc fhom)) hz]
    exact (congrArg (eqv _) (Subtype.ext COEQ2)).trans
      (transport_eqv
        (Limits.pullback.fst (Limits.Sigma.desc fhom) (Limits.Sigma.desc fhom) ≫
          Limits.Sigma.desc fhom ≫ 𝟙 X.base)
        (Limits.pullback.snd (Limits.Sigma.desc fhom) (Limits.Sigma.desc fhom) ≫
          Limits.Sigma.desc fhom ≫ 𝟙 X.base)
        (by simp only [← Category.assoc, Limits.pullback.condition])
        (Limits.pullback.snd (Limits.Sigma.desc fhom) (Limits.Sigma.desc fhom) ≫ hz.1)
        (by rw [Category.assoc, hz.2, ← Category.assoc, ← Category.assoc,
          Limits.pullback.condition])
        (by rw [Category.assoc, hz.2])).symm
  obtain ⟨a, descfac⟩ := moduliProblem_fppf_descent R P hP (Limits.Sigma.desc fhom) X (𝟙 X.base)
    (eqv (Limits.Sigma.desc fhom ≫ 𝟙 X.base) ⟨Limits.Sigma.desc hlift, hz2⟩) hcocyc
  set α := (eqv (𝟙 X.base)).symm a with hαdef
  have haα : eqv (𝟙 X.base) α = a := (eqv (𝟙 X.base)).apply_symm_apply a
  -- restriction of an arbitrary section to a chart, expressed through the representing scheme
  have chartRestrict : ∀ (s : P.obj (Opposite.op (X.pullbackAlong (𝟙 X.base)))) {W : Scheme.{u}}
      (j : W ⟶ X.base),
      cast (congrArg (fun q => P.obj (Opposite.op (X.pullbackAlong q))) (Category.comp_id j))
        (P.map (X.pullbackAlongMap (𝟙 X.base) j).op s) =
      eqv j ⟨j ≫ ((eqv (𝟙 X.base)).symm s).1, by
        rw [Category.assoc, ((eqv (𝟙 X.base)).symm s).2, Category.comp_id]⟩ := by
    intro s W j
    conv_lhs => rw [← (eqv (𝟙 X.base)).apply_symm_apply s,
      ← hnat (𝟙 X.base) j ((eqv (𝟙 X.base)).symm s)]
    exact transport_eqv j (j ≫ 𝟙 X.base) (Category.comp_id j) _ _ _
  -- the base lift of `a` restricts to the two chart lifts on each chart
  have KEY : Limits.Sigma.desc fhom ≫ α.1 = Limits.Sigma.desc hlift := by
    have hnf := hnat (𝟙 X.base) (Limits.Sigma.desc fhom) α
    rw [haα, descfac] at hnf
    exact congrArg Subtype.val ((eqv _).injective hnf)
  have KEYt : U.ι ≫ α.1 = hU.1 := by
    have h := congrArg (fun t => Limits.Sigma.ι chart true ≫ t) KEY
    simpa only [Limits.Sigma.ι_desc_assoc, Limits.Sigma.ι_desc, hfhom_true, hlift_true] using h
  have KEYf : V.ι ≫ α.1 = hV.1 := by
    have h := congrArg (fun t => Limits.Sigma.ι chart false ≫ t) KEY
    simpa only [Limits.Sigma.ι_desc_assoc, Limits.Sigma.ι_desc, hfhom_false, hlift_false] using h
  refine ⟨a, ⟨?_, ?_⟩, ?_⟩
  · rw [chartRestrict a U.ι, ← hUval]
    exact congrArg (eqv U.ι) (Subtype.ext KEYt)
  · rw [chartRestrict a V.ι, ← hVval]
    exact congrArg (eqv V.ι) (Subtype.ext KEYf)
  · rintro y ⟨hyU, hyV⟩
    refine moduliProblem_fppf_separated R P hP (Limits.Sigma.desc fhom) hFflat hFlfp hFsurj
      X (𝟙 X.base) y a ?_
    rw [descfac]
    conv_lhs => rw [← (eqv (𝟙 X.base)).apply_symm_apply y,
      ← hnat (𝟙 X.base) (Limits.Sigma.desc fhom) ((eqv (𝟙 X.base)).symm y)]
    refine congrArg (eqv _) (Subtype.ext ?_)
    refine Limits.Sigma.hom_ext _ _ fun b => ?_
    rw [Limits.Sigma.ι_desc_assoc, Limits.Sigma.ι_desc]
    cases b
    · have hb := (chartRestrict y V.ι).symm.trans hyV
      rw [← hVval] at hb
      have hb' := congrArg Subtype.val ((eqv V.ι).injective hb)
      simpa only [hfhom_false, hlift_false] using hb'
    · have hb := (chartRestrict y U.ι).symm.trans hyU
      rw [← hUval] at hb
      have hb' := congrArg Subtype.val ((eqv U.ι).injective hb)
      simpa only [hfhom_true, hlift_true] using hb'

end ModularCurves
