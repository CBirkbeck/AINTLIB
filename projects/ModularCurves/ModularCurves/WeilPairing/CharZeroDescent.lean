/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.WeilPairing.Basic
import ModularCurves.Moduli.Stack

/-!
# The `T`-relative Weil pairing by fppf descent (T-C0e, `weilPairingCharZero`)

The DS4 Weil pairing of record (`WeilPairing/Basic.lean`, `EllipticCurve.weilPairing`) is the
`S`-morphism `e_N : E[N] ×_S E[N] ⟶ μ_{N,S}`, registered there as a DATA-SORRY. Per the v9
expert review (2026-07-07, §"Weil pairing"), the pairing the moduli functor `Y(ρ̄)` needs is
exactly this `T`-relative morphism over arbitrary `Spec ℚ`-schemes — **not** the field-valued
descent `exists_pairingAlgebraHom_of_galoisEquivariant` of `WeilPairing/EtaleDescent.lean`,
which is only the geometric-fibre (field-base) pairing.

This file supplies the **char-0 construction** of that morphism by the route the review named:
*build the pairing étale-locally on `S` — where the finite-étale `E[N]` trivialises — then
descend it.* The descent half is gate-free and general; the input it consumes is a local pairing
on a trivialising fppf cover together with its gluing (cocycle) datum. Concretely:

* `weilPairingCharZero E N p ζ' hcocyc` descends a morphism `ζ'` — defined on the base change of
  `E[N] ×_S E[N]` along an fppf cover `p : S' ⟶ S` and valued in the fixed target `μ_{N,S}` — to
  a morphism `E[N] ×_S E[N] ⟶ μ_{N,S}` over `S`, using `descend_hom_of_effectiveEpi`
  (`Moduli/Stack.lean`; fppf covers are effective epimorphisms by subcanonicity of the fppf
  topology). The base change of the cover along the structure map `E[N] ×_S E[N] ⟶ S` is again
  fppf (`Flat`/`LocallyOfFinitePresentation`/`Surjective` are stable under base change), so the
  mathlib `EffectiveEpi` instance fires.

**Labelled inputs (the gated content, isolated as hypotheses).** The cover `p` exists because
`E[N]` is finite étale when `N` is invertible (`Torsionπ.etale`, which rests on the T-B5 box
`MulByHom.formallyUnramified`); the local pairing `ζ'` and its cocycle `hcocyc` come from
trivialising `E[N]` (and `μ_N`) on `p` and putting the standard symplectic determinant pairing
there. Constructing those data from the trivialisation is the T-W7-scale step (the point-level
`E[N] ≅ (ℤ/N)²` identification funnels into the group-law/atlas refactor); here they are the
theorem's hypotheses, so the descent — the reviewer's "then descend" half — is discharged
**gate-free**. Supplying `(p, ζ', hcocyc)` from an étale-local full-level trivialisation is what
would discharge the DS4 `weilPairing` sorry over `ℚ`-schemes.

Source: KM 2.8; the descent is SGA 1 VIII / Stacks 023Q (fppf covers are effective epis).
-/

open AlgebraicGeometry CategoryTheory Limits

universe u

namespace ModularCurves

/-! ### The local symplectic determinant model

Gate-free infrastructure for the local pairing that `weilPairingCharZero` descends: the
determinant pairing on the constant `(ℤ/N)²`-scheme, and its GL₂ change-of-basis law
`e(g·v, g·w) = e(v, w) · det g` — the symplectic normalisation pin (v9 review Q6) and the
cocycle that makes the Weil pairing descend (it is invariant precisely on `SL₂`). Nothing here
touches `E[N]` or the torsion boxes; on a cover trivialising `E[N]` to `(ℤ/N)²` and `μ_N` to
`(ℤ/N)`, this is the local pairing fed to `weilPairingCharZero`. -/

/-- The determinant pairing on `(ℤ/N)² = (Fin 2 → ZMod N)`:
`detFun (v, w) = v 0 * w 1 - v 1 * w 0`. The combinatorial local model of the Weil pairing. -/
def detFun (N : ℕ) : (Fin 2 → ZMod N) × (Fin 2 → ZMod N) → ZMod N :=
  fun p => p.1 0 * p.2 1 - p.1 1 * p.2 0

/-- The diagonal GL₂-action on a pair of `(ℤ/N)²`-vectors (change of basis on both entries). -/
def gl2Both (N : ℕ) (g : Matrix (Fin 2) (Fin 2) (ZMod N)) :
    (Fin 2 → ZMod N) × (Fin 2 → ZMod N) → (Fin 2 → ZMod N) × (Fin 2 → ZMod N) :=
  fun p => (g.mulVec p.1, g.mulVec p.2)

/-- **Symplectic law (combinatorial core).** `det(g·v, g·w) = det g · det(v, w)` — the
determinant pairing multiplies by `det g` under a diagonal change of basis. Pure `ZMod`
linear algebra (`Matrix.det_fin_two`). -/
theorem detFun_gl2Both (N : ℕ) (g : Matrix (Fin 2) (Fin 2) (ZMod N))
    (p : (Fin 2 → ZMod N) × (Fin 2 → ZMod N)) :
    detFun N (gl2Both N g p) = g.det * detFun N p := by
  obtain ⟨v, w⟩ := p
  simp only [detFun, gl2Both, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
    Matrix.det_fin_two]
  ring

/-- The determinant pairing is alternating: `e(v, v) = 0` (KM 2.8; Silverman III.8.1(b)). -/
@[simp] theorem detFun_self (N : ℕ) (v : Fin 2 → ZMod N) : detFun N (v, v) = 0 := by
  simp only [detFun]; ring

/-- Antisymmetry: `e(w, v) = - e(v, w)`. -/
theorem detFun_swap (N : ℕ) (v w : Fin 2 → ZMod N) :
    detFun N (w, v) = -detFun N (v, w) := by
  simp only [detFun]; ring

/-- Bilinearity, left slot: `e(v + v', w) = e(v, w) + e(v', w)` (KM 2.8; Silverman III.8.1(a)). -/
theorem detFun_add_left (N : ℕ) (v v' w : Fin 2 → ZMod N) :
    detFun N (v + v', w) = detFun N (v, w) + detFun N (v', w) := by
  simp only [detFun, Pi.add_apply]; ring

/-- Bilinearity, right slot: `e(v, w + w') = e(v, w) + e(v, w')`. -/
theorem detFun_add_right (N : ℕ) (v w w' : Fin 2 → ZMod N) :
    detFun N (v, w + w') = detFun N (v, w) + detFun N (v, w') := by
  simp only [detFun, Pi.add_apply]; ring

section ConstSchemeMap

variable {S : Scheme.{u}}

/-- Functoriality of the constant scheme: a map `f : A → B` of finite index types induces an
`S`-morphism `∐_A S ⟶ ∐_B S` over `S`. -/
noncomputable def constSchemeMap {A B : Type} [Finite A] [Finite B] (f : A → B) :
    constScheme S A ⟶ constScheme S B :=
  Sigma.desc fun a => Sigma.ι (fun _ : B => S) (f a)

/-- Points-level computation rule: `constSchemeMap f` sends the `a`-th copy of `S` to the
`f a`-th copy — i.e. on `T`-points it is `f` applied to the locally constant index function. -/
@[simp] theorem constSchemeMap_ι {A B : Type} [Finite A] [Finite B] (f : A → B) (a : A) :
    Sigma.ι (fun _ : A => S) a ≫ constSchemeMap (S := S) f = Sigma.ι (fun _ : B => S) (f a) := by
  simp only [constSchemeMap, Sigma.ι_desc]

@[simp] theorem constSchemeMap_π {A B : Type} [Finite A] [Finite B] (f : A → B) :
    constSchemeMap (S := S) f ≫ constSchemeπ S B = constSchemeπ S A := by
  refine Sigma.hom_ext _ _ fun a => ?_
  simp only [constSchemeMap, constSchemeπ, Sigma.ι_desc_assoc, Sigma.ι_desc]

theorem constSchemeMap_comp {A B C : Type} [Finite A] [Finite B] [Finite C]
    (f : A → B) (g : B → C) :
    constSchemeMap (S := S) f ≫ constSchemeMap g = constSchemeMap (g ∘ f) := by
  refine Sigma.hom_ext _ _ fun a => ?_
  simp only [constSchemeMap, Sigma.ι_desc_assoc, Sigma.ι_desc, Function.comp_apply]

@[simp] theorem constSchemeMap_id {A : Type} [Finite A] :
    constSchemeMap (S := S) (id : A → A) = 𝟙 (constScheme S A) := by
  refine Sigma.hom_ext _ _ fun a => ?_
  simp only [constSchemeMap, Sigma.ι_desc, id_eq, Category.comp_id]

/-- The local determinant-pairing model as a morphism of constant schemes over `S`, induced by
`detFun`: `(ℤ/N)² × (ℤ/N)²` (constant scheme on the product index) → `(ℤ/N)` (which is `μ_N`
after a splitting). -/
noncomputable def detConstMor (N : ℕ) [NeZero N] :
    constScheme S ((Fin 2 → ZMod N) × (Fin 2 → ZMod N)) ⟶ constScheme S (ZMod N) :=
  constSchemeMap (detFun N)

/-- **Symplectic law of the local model (v9 review Q6 pin), scheme level.** Precomposing the
determinant pairing with the diagonal GL₂-action equals postcomposing with multiplication by
`det g`: `e(g·v, g·w) = e(v, w) · det g`. This is the change-of-trivialisation cocycle that
descends the Weil pairing (invariant on `SL₂`). -/
theorem detConstMor_gl2Both (N : ℕ) [NeZero N] (g : Matrix (Fin 2) (Fin 2) (ZMod N)) :
    constSchemeMap (gl2Both N g) ≫ detConstMor (S := S) N =
      detConstMor (S := S) N ≫ constSchemeMap (· * g.det) := by
  have hfun : detFun N ∘ gl2Both N g = (· * g.det) ∘ detFun N := by
    funext p
    rw [Function.comp_apply, Function.comp_apply, detFun_gl2Both, mul_comm]
  rw [detConstMor, constSchemeMap_comp, constSchemeMap_comp, hfun]

/-- **`SL₂`-invariance of the local model.** When `det g = 1` the determinant pairing is
invariant under the change of basis `g` — the change-of-trivialisation cocycle vanishes, which
is exactly why the Weil pairing descends along an `SL₂`-reduction of the trivialising cover. -/
theorem detConstMor_sl2 (N : ℕ) [NeZero N] (g : Matrix (Fin 2) (Fin 2) (ZMod N))
    (hg : g.det = 1) :
    constSchemeMap (gl2Both N g) ≫ detConstMor (S := S) N = detConstMor (S := S) N := by
  have hid : (fun k : ZMod N => k * g.det) = id := by funext k; rw [hg, mul_one, id_eq]
  rw [detConstMor_gl2Both, hid, constSchemeMap_id, Category.comp_id]

end ConstSchemeMap

section MuNBaseChange

variable {S S' : Scheme.{u}}

/-- Base change of `μ_N` along `g : S' ⟶ S`: the projection `μ_{N,S'} ⟶ μ_{N,S}` exhibiting
`μ_{N,S'}` as `μ_{N,S} ×_S S'`. A named wrapper around the (now public) `isPullback_muN_baseChange`
for use in base-change naturality. -/
noncomputable def muNBaseChange (g : S' ⟶ S) (N : ℕ) : muN S' N ⟶ muN S N :=
  (isPullback_muN_baseChange S S' N g).choose

/-- `μ_{N,S'} ⟶ μ_{N,S}` exhibits `μ_{N,S'}` as the base change `μ_{N,S} ×_S S'`. -/
theorem muNBaseChange_isPullback (g : S' ⟶ S) (N : ℕ) :
    IsPullback (muNBaseChange g N) (muNπ S' N) (muNπ S N) g :=
  (isPullback_muN_baseChange S S' N g).choose_spec

@[reassoc]
theorem muNBaseChange_muNπ (g : S' ⟶ S) (N : ℕ) :
    muNBaseChange g N ≫ muNπ S N = muNπ S' N ≫ g :=
  (muNBaseChange_isPullback g N).w

end MuNBaseChange

namespace EllipticCurve

variable {S : Scheme.{u}} (E : EllipticCurve S)

/-- The structure morphism `E[N] ×_S E[N] ⟶ S` of the Weil-pairing source. -/
noncomputable def torsionSqπ (N : ℕ) : pullback (E.torsionπ N) (E.torsionπ N) ⟶ S :=
  pullback.fst (E.torsionπ N) (E.torsionπ N) ≫ E.torsionπ N

set_option backward.isDefEq.respectTransparency false in
/-- The pullback of a surjective cover along the Weil-pairing source is surjective. Registered
as an instance so the descent proofs below need not re-derive it. -/
private instance surjective_pullback_fst_torsionSqπ (N : ℕ) {S' : Scheme.{u}} (p : S' ⟶ S)
    [Surjective p] : Surjective (pullback.fst (E.torsionSqπ N) p) :=
  MorphismProperty.pullback_fst _ _ ‹Surjective p›

set_option backward.isDefEq.respectTransparency false in
/-- The pullback of a locally-finitely-presented cover along the Weil-pairing source is again
locally of finite presentation. Registered as an instance, as above. -/
private instance lfp_pullback_fst_torsionSqπ (N : ℕ) {S' : Scheme.{u}} (p : S' ⟶ S)
    [LocallyOfFinitePresentation p] :
    LocallyOfFinitePresentation (pullback.fst (E.torsionSqπ N) p) :=
  MorphismProperty.pullback_fst _ _ ‹LocallyOfFinitePresentation p›

/-- **(T-C0e)** The char-0 Weil pairing `E[N] ×_S E[N] ⟶ μ_{N,S}`, constructed by fppf descent
of a local pairing `ζ'` given on the base change of `E[N] ×_S E[N]` along a trivialising fppf
cover `p : S' ⟶ S`. The pulled-back cover `pullback.fst (E.torsionSqπ N) p` is fppf (base change
of `p`), hence an effective epimorphism, so a morphism into the fixed target `μ_{N,S}` that
coequalises its kernel pair (`hcocyc`) descends uniquely. See the module docstring for the
labelled-input convention. -/
noncomputable def weilPairingCharZero (N : ℕ) [NeZero N]
    {S' : Scheme.{u}} (p : S' ⟶ S)
    [Flat p] [LocallyOfFinitePresentation p] [Surjective p]
    (ζ' : pullback (E.torsionSqπ N) p ⟶ muN S N)
    (hcocyc : pullback.fst (pullback.fst (E.torsionSqπ N) p) (pullback.fst (E.torsionSqπ N) p) ≫ ζ'
        = pullback.snd (pullback.fst (E.torsionSqπ N) p) (pullback.fst (E.torsionSqπ N) p) ≫ ζ') :
    pullback (E.torsionπ N) (E.torsionπ N) ⟶ muN S N :=
  (descend_hom_of_effectiveEpi (pullback.fst (E.torsionSqπ N) p) ζ' hcocyc).choose

/-- **(T-C0e spec, restriction)** The char-0 Weil pairing restricts along the trivialising cover
to the local pairing `ζ'` it was descended from. -/
theorem weilPairingCharZero_restrict (N : ℕ) [NeZero N]
    {S' : Scheme.{u}} (p : S' ⟶ S)
    [Flat p] [LocallyOfFinitePresentation p] [Surjective p]
    (ζ' : pullback (E.torsionSqπ N) p ⟶ muN S N)
    (hcocyc : pullback.fst (pullback.fst (E.torsionSqπ N) p) (pullback.fst (E.torsionSqπ N) p) ≫ ζ'
        = pullback.snd (pullback.fst (E.torsionSqπ N) p) (pullback.fst (E.torsionSqπ N) p) ≫ ζ') :
    pullback.fst (E.torsionSqπ N) p ≫ E.weilPairingCharZero N p ζ' hcocyc = ζ' :=
  (descend_hom_of_effectiveEpi (pullback.fst (E.torsionSqπ N) p) ζ' hcocyc).choose_spec.1

/-- **(T-C0e spec, over `S` — cf. `weilPairing_over`)** If the local pairing `ζ'` is a morphism
over `S` (lands in `μ_{N,S}` compatibly with the structure map), then so is the descended pairing:
`e_N` followed by `μ_{N,S} ⟶ S` is the projection `E[N] ×_S E[N] ⟶ S`. -/
theorem weilPairingCharZero_over (N : ℕ) [NeZero N]
    {S' : Scheme.{u}} (p : S' ⟶ S)
    [Flat p] [LocallyOfFinitePresentation p] [Surjective p]
    (ζ' : pullback (E.torsionSqπ N) p ⟶ muN S N)
    (hcocyc : pullback.fst (pullback.fst (E.torsionSqπ N) p) (pullback.fst (E.torsionSqπ N) p) ≫ ζ'
        = pullback.snd (pullback.fst (E.torsionSqπ N) p) (pullback.fst (E.torsionSqπ N) p) ≫ ζ')
    (hover : ζ' ≫ muNπ S N = pullback.fst (E.torsionSqπ N) p ≫ E.torsionSqπ N) :
    E.weilPairingCharZero N p ζ' hcocyc ≫ muNπ S N = E.torsionSqπ N := by
  haveI : Epi (pullback.fst (E.torsionSqπ N) p) := inferInstance
  refine (cancel_epi (pullback.fst (E.torsionSqπ N) p)).mp ?_
  rw [← Category.assoc, E.weilPairingCharZero_restrict N p ζ' hcocyc, hover]

/-- **(T-C0e spec, uniqueness)** The char-0 Weil pairing is the unique morphism into `μ_{N,S}`
whose restriction along the trivialising cover is the local pairing `ζ'`. -/
theorem weilPairingCharZero_unique (N : ℕ) [NeZero N]
    {S' : Scheme.{u}} (p : S' ⟶ S)
    [Flat p] [LocallyOfFinitePresentation p] [Surjective p]
    (ζ' : pullback (E.torsionSqπ N) p ⟶ muN S N)
    (hcocyc : pullback.fst (pullback.fst (E.torsionSqπ N) p) (pullback.fst (E.torsionSqπ N) p) ≫ ζ'
        = pullback.snd (pullback.fst (E.torsionSqπ N) p) (pullback.fst (E.torsionSqπ N) p) ≫ ζ')
    (e : pullback (E.torsionπ N) (E.torsionπ N) ⟶ muN S N)
    (he : pullback.fst (E.torsionSqπ N) p ≫ e = ζ') :
    e = E.weilPairingCharZero N p ζ' hcocyc := by
  exact (descend_hom_of_effectiveEpi (pullback.fst (E.torsionSqπ N) p) ζ' hcocyc).choose_spec.2 e he

/-- The base change of the Weil-pairing source `E[N] ×_S E[N]` along `g : T ⟶ S`: the induced
map `E_T[N] ×_T E_T[N] ⟶ E[N] ×_S E[N]` (from `torsion_baseChange_isPullback` on each factor). -/
noncomputable def weilPairingSourceBaseChange (N : ℕ) {T : Scheme.{u}} (g : T ⟶ S) :
    pullback ((E.baseChange g).torsionπ N) ((E.baseChange g).torsionπ N) ⟶
      pullback (E.torsionπ N) (E.torsionπ N) :=
  pullback.map _ _ _ _ (E.torsionBaseChangeHom N g) (E.torsionBaseChangeHom N g) g
    (E.torsion_baseChange_isPullback N g).w.symm (E.torsion_baseChange_isPullback N g).w.symm

/-- **(T-C0e spec, base-change naturality — review Q4 "compatible with arbitrary base change")**
If the local pairings agree after base change over the cover (`hζ`), then the char-0 Weil pairing
is compatible with base change of `S` along `g`: the pairing for `E_T = E.baseChange g`, followed
by the projection `μ_{N,T} ⟶ μ_{N,S}`, equals the base-changed source followed by the pairing for
`E`. The cover-level hypothesis `hζ` propagates to the scheme level by the effective-epi property,
exactly as `weilPairingCharZero_over` propagates the over-`S` condition. -/
theorem weilPairingCharZero_baseChange (N : ℕ) [NeZero N] {T : Scheme.{u}} (g : T ⟶ S)
    {S' : Scheme.{u}} (p : S' ⟶ S) [Flat p] [LocallyOfFinitePresentation p] [Surjective p]
    (ζ' : pullback (E.torsionSqπ N) p ⟶ muN S N)
    (hcocyc : pullback.fst (pullback.fst (E.torsionSqπ N) p) (pullback.fst (E.torsionSqπ N) p) ≫ ζ'
        = pullback.snd (pullback.fst (E.torsionSqπ N) p) (pullback.fst (E.torsionSqπ N) p) ≫ ζ')
    {S'' : Scheme.{u}} (p_T : S'' ⟶ T)
    [Flat p_T] [LocallyOfFinitePresentation p_T] [Surjective p_T]
    (ζ'_T : pullback ((E.baseChange g).torsionSqπ N) p_T ⟶ muN T N)
    (hcocyc_T :
      pullback.fst (pullback.fst ((E.baseChange g).torsionSqπ N) p_T)
          (pullback.fst ((E.baseChange g).torsionSqπ N) p_T) ≫ ζ'_T
        = pullback.snd (pullback.fst ((E.baseChange g).torsionSqπ N) p_T)
          (pullback.fst ((E.baseChange g).torsionSqπ N) p_T) ≫ ζ'_T)
    (hζ : pullback.fst ((E.baseChange g).torsionSqπ N) p_T ≫
            E.weilPairingSourceBaseChange N g ≫ E.weilPairingCharZero N p ζ' hcocyc
          = ζ'_T ≫ muNBaseChange g N) :
    (E.baseChange g).weilPairingCharZero N p_T ζ'_T hcocyc_T ≫ muNBaseChange g N
      = E.weilPairingSourceBaseChange N g ≫ E.weilPairingCharZero N p ζ' hcocyc := by
  haveI : Epi (pullback.fst ((E.baseChange g).torsionSqπ N) p_T) :=
    AlgebraicGeometry.Flat.epi_of_flat_of_surjective _
  refine (cancel_epi (pullback.fst ((E.baseChange g).torsionSqπ N) p_T)).mp ?_
  rw [← Category.assoc, (E.baseChange g).weilPairingCharZero_restrict N p_T ζ'_T hcocyc_T]
  exact hζ.symm

end EllipticCurve

end ModularCurves
