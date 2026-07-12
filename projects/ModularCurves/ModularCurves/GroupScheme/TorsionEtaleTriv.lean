import ModularCurves.EllipticCurve.Torsion
import ModularCurves.GroupScheme.MuN
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.Flat.Rank

/-!
# T-F1-general — the étale-local trivialisation of `E[N]` (KM 2.3.1)

**Interface pin (CHARTER-C5B-2, owned by c5β; consumed by NEW-Y1's CLOPEN-β descent geometry).**

KM 2.3.1: for `N` invertible on `S`, the group scheme `E[N]` is *finite étale over `S`, locally
for the étale topology on `S` isomorphic to `ℤ/NZ × ℤ/NZ`*. This file states that étale-local
structure as `torsion_etaleLocal_triv`: `E[N]` is trivialised by a surjective étale cover
`p : T ⟶ S`, over which `E[N] ×_S T` is isomorphic (as a `T`-scheme) to the constant scheme
`(ℤ/N)²_T = constScheme T (Fin 2 → ZMod N)`.

The proof (c5β's L2b) goes via the fibrewise-iso ⟹ iso criterion
(`isIso_of_isPullback_of_fppf`) on the finite-étale `torsionπ_etale`; NEW-Y1 codes CLOPEN-β to
this pin meanwhile (v10.154 adjudication).

BOUNDARY: does NOT build the Weil pairing (p2's `[T-C1-KM28]`).
-/

open AlgebraicGeometry CategoryTheory Limits

universe u

namespace ModularCurves

/-- **T-F1 infra (universe-bridged)** — the constant scheme on `Spec T` indexed by a finite
`Type 0` `ι` is `Spec` of the product ring `ι → T`. (Mathlib's `sigmaSpec` iso is pinned to a
`Type u` index; `constScheme`'s index is `Type 0`, so we bridge through `ULift.{u} ι`.) -/
noncomputable def constSchemeSpecIso (T : CommRingCat.{u}) (ι : Type) [Finite ι] :
    constScheme (Spec T) ι ≅ Spec (CommRingCat.of (ι → (T : Type u))) :=
  (Sigma.whiskerEquiv (Equiv.ulift.{u,0}) (fun _ => Iso.refl (Spec T))).symm ≪≫
    asIso (sigmaSpec (fun _ : ULift.{u} ι => T)) ≪≫
    Scheme.Spec.mapIso ((RingEquiv.piCongrLeft' (fun _ : ULift.{u} ι => (T : Type u))
      (Equiv.ulift.{u,0})).toCommRingCatIso).symm.op

/-- `constSchemeSpecIso` is a morphism over the base: it intertwines the constant-scheme
projection `constSchemeπ` with the diagonal ring map `T → (ι → T)`. -/
@[reassoc]
lemma constSchemeSpecIso_hom_π (T : CommRingCat.{u}) (ι : Type) [Finite ι] :
    (constSchemeSpecIso T ι).hom ≫ Spec.map (CommRingCat.ofHom (Pi.constRingHom ι T))
      = constSchemeπ (Spec T) ι := by
  refine Sigma.hom_ext _ _ fun a => ?_
  simp only [constSchemeSpecIso, Iso.trans_hom, Iso.symm_hom, Sigma.whiskerEquiv_inv,
    Functor.mapIso_hom, Iso.op_hom, asIso_hom, Category.assoc, constSchemeπ]
  rw [Sigma.ι_comp_map'_assoc, ι_sigmaSpec_assoc]
  simp only [Sigma.ι_desc, Category.id_comp, eqToHom_refl, Iso.refl_hom,
    Scheme.Spec_map, Quiver.Hom.unop_op]
  rw [← Spec.map_comp, ← Spec.map_comp, ← Spec.map_id]
  congr 1

/-- **T-F1 infra (rank-match)** — a finite-split `T`-algebra of constant rank `n` is
`T`-algebra-isomorphic to `Fin n → T`. The existential rank in `IsFiniteSplit` is pinned to `n`
by the rank hypothesis; the trivial base case `Subsingleton T` is handled directly (both sides
subsingleton). -/
lemma isFiniteSplit_algEquiv_fin_of_rankAtStalk {T A : Type u} [CommRing T] [CommRing A]
    [Algebra T A] [Algebra.IsFiniteSplit T A] {n : ℕ}
    (hn : Module.rankAtStalk (R := T) A = n) :
    Nonempty (A ≃ₐ[T] (Fin n → T)) := by
  obtain ⟨m, ⟨e⟩⟩ := Algebra.IsFiniteSplit.nonempty_algEquiv_fun T A
  rcases subsingleton_or_nontrivial T with hT | hT
  · haveI : Subsingleton (Fin m → T) := inferInstance
    haveI : Subsingleton A := e.injective.subsingleton
    haveI : Subsingleton (Fin n → T) := inferInstance
    exact ⟨AlgEquiv.ofLinearEquiv default (Subsingleton.elim _ _)
      (fun _ _ => Subsingleton.elim _ _)⟩
  · have hmn : m = n := by
      obtain ⟨p⟩ := (inferInstance : Nonempty (PrimeSpectrum T))
      have h1 : Module.rankAtStalk (R := T) A p = Module.rankAtStalk (R := T) (Fin m → T) p :=
        congrFun (Module.rankAtStalk_eq_of_equiv e.toLinearEquiv) p
      rw [hn] at h1
      have h2 : Module.rankAtStalk (R := T) (Fin m → T) p = m := by
        rw [Module.rankAtStalk_pi]; simp [finsum_eq_sum_of_fintype]
      rw [h2] at h1
      exact h1.symm
    subst hmn
    exact ⟨e⟩

namespace EllipticCurve

variable {S : Scheme.{u}} (E : EllipticCurve S)

/-- **T-F1-general (interface — sorried pin)** — the étale-local structure of `E[N]` (KM 2.3.1):
for `N` invertible on `S` there is a surjective étale cover `p : T ⟶ S` over which the base
change `E[N] ×_S T` is `T`-isomorphic to the constant scheme `(ℤ/N)²_T`. NEW-Y1's CLOPEN-β
consumes this as a pin. -/
theorem torsion_etaleLocal_triv (N : ℕ) [NeZero N] (hinv : NIsInvertible S N) :
    ∃ (T : Scheme.{u}) (p : T ⟶ S), Etale p ∧ Surjective p ∧
      Nonempty (Over.mk (pullback.snd (E.torsionπ N) p) ≅
        Over.mk (constSchemeπ T (Fin 2 → ZMod N))) := sorry

end EllipticCurve

end ModularCurves
