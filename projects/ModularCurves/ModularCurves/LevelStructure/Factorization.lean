/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.LevelStructure.ExactOrder
import ModularCurves.GroupScheme.DeligneOrder

/-!
# Prime-power factorization of Drinfeld exact order (KM 1.7.2 / 3.5.1, Γ₁-instance)

**[KM-W0-(iv)] skeleton** (`/develop --decompose`, 2026-07-16; quotes in
`.mathlib-quality/decomposition-km-integral.md` §[KM-W0]).

KM Lemma 3.5.1 (verbatim, print p. 101): *"Suppose that `N = AB` with `A` and `B`
relatively prime. Then for any elliptic curve `E/S`, we have functorial isomorphisms
`Γ₁(N)-Str(E/S) ≅ Γ₁(A)-Str(E/S) × Γ₁(B)-Str(E/S)"*, explicitly (print p. 102):
*"for `Γ₁(N)`: point `P` of exact order `N` ↦ points `BP`, `AP` of exact orders `A, B`"*.
The underlying geometric content is KM Proposition 1.7.2 (print pp. 26–31): a
homomorphism `φ : A₁ × A₂ → C(S)` is an `A`-structure iff both restrictions `φᵢ` are
`Aᵢ`-structures; its proof splits the generated subgroup `G ≅ G[N₁] ×_S G[N₂]`,
computes ranks geometrically, and localizes on `S` over the coprime cover
`{N₁ invertible} ∪ {N₂ invertible}`.

The skeleton keeps the repo's divisor encoding (`Section.HasExactOrder`,
KM 1.4.1): no `φ`-homomorphism vocabulary is introduced — for the cyclic group
`ℤ/N` a homomorphism *is* its value at `1` (KM 1.5.2).
-/

open AlgebraicGeometry CategoryTheory Limits

universe u

namespace ModularCurves

variable {S : Scheme.{u}} (E : EllipticCurve S)

/-- Factoring through a monomorphism is Zariski-local on the source: a morphism `q : T ⟶ Y`
factors through `ι : W ⟶ Y` as soon as its restrictions to the members of an open cover of
`T` do. (The local factorizations agree on overlaps by `cancel_mono`, hence glue.) -/
private lemma exists_factor_of_openCover {T W Y : Scheme.{u}} (𝒱 : T.OpenCover)
    (ι : W ⟶ Y) [Mono ι] (q : T ⟶ Y)
    (hloc : ∀ i : 𝒱.I₀, ∃ hi : 𝒱.X i ⟶ W, hi ≫ ι = 𝒱.f i ≫ q) :
    ∃ h : T ⟶ W, h ≫ ι = q := by
  choose hi hhi using hloc
  have hcomp : ∀ i j : 𝒱.I₀,
      pullback.fst (𝒱.f i) (𝒱.f j) ≫ hi i = pullback.snd (𝒱.f i) (𝒱.f j) ≫ hi j := by
    intro i j
    rw [← cancel_mono ι, Category.assoc, Category.assoc, hhi, hhi, ← Category.assoc,
      ← Category.assoc, pullback.condition]
  exact ⟨𝒱.glueMorphisms hi hcomp, 𝒱.hom_ext _ _ fun i => by
    rw [← Category.assoc, Scheme.Cover.ι_glueMorphisms, hhi]⟩

namespace RelEffCartierDiv

/-- **[W0-F3-loc] (KM 1.7.2's silent localization step)** Being a subgroup divisor is
Zariski-local on the base: if the pullbacks of a relative effective Cartier divisor
`D` in `E/S` to the members of an open cover of `S` are subgroups, `D` is a subgroup.
KM (print p. 31, verbatim): *"Because `N = N₁N₂` with `N₁` and `N₂` relatively prime,
we may, by localizing on `S`, suppose that one of `N₁, N₂`, say `N₁`, is invertible
on `S`."* — the step that makes this reduction legitimate for the `IsSubgroup`
conclusion. -/
theorem isSubgroup_of_openCover (D : RelEffCartierDiv E.π)
    (𝒰 : S.OpenCover) (h : ∀ i : 𝒰.I₀,
      ∀ ⦃T : Scheme.{u}⦄ (g : T ⟶ S), (∃ gi : T ⟶ 𝒰.X i, gi ≫ 𝒰.f i = g) →
        ∃ H : AddSubgroup (E.Point g),
          ∀ P : E.Point g, P ∈ H ↔ ∃ h : T ⟶ D.ideal.subscheme,
            h ≫ D.ideal.subschemeι = P.1) :
    D.IsSubgroup E := by
  intro T g
  -- the pulled-back cover of `T`, indexed by `𝒰.I₀`
  let 𝒱 : T.OpenCover := Scheme.Cover.mkOfCovers 𝒰.I₀
    (fun i => pullback g (𝒰.f i)) (fun i => pullback.fst g (𝒰.f i))
    (fun t => by
      obtain ⟨y, hy⟩ := 𝒰.covers (g t)
      obtain ⟨z, hz1, _⟩ := Scheme.Pullback.exists_preimage_pullback t y hy.symm
      exact ⟨𝒰.idx (g t), z, hz1⟩)
    (fun i => inferInstance)
  -- the local subgroup structures over the cover
  have hloc := fun i : 𝒰.I₀ => h i (pullback.fst g (𝒰.f i) ≫ g)
    ⟨pullback.snd g (𝒰.f i), pullback.condition.symm⟩
  choose Hloc hHloc using hloc
  -- gluing engine: a point factoring locally on the cover factors globally
  have key : ∀ P : E.Point g,
      (∀ i : 𝒰.I₀, ∃ hi : pullback g (𝒰.f i) ⟶ D.ideal.subscheme,
        hi ≫ D.ideal.subschemeι = pullback.fst g (𝒰.f i) ≫ P.1) →
      ∃ hh : T ⟶ D.ideal.subscheme, hh ≫ D.ideal.subschemeι = P.1 :=
    fun P hP => exists_factor_of_openCover 𝒱 D.ideal.subschemeι P.1 hP
  -- local membership of a restricted point, from a global factoring
  have hmem : ∀ (i : 𝒰.I₀) (P : E.Point g),
      (∃ hh : T ⟶ D.ideal.subscheme, hh ≫ D.ideal.subschemeι = P.1) →
      EllipticCurve.Point.restrict E (pullback.fst g (𝒰.f i)) P ∈ Hloc i := by
    intro i P hhP
    obtain ⟨hh, hhh⟩ := hhP
    exact (hHloc i _).mpr ⟨pullback.fst g (𝒰.f i) ≫ hh, by
      rw [Category.assoc, hhh]; rfl⟩
  -- restriction of a negative
  have hneg : ∀ (i : 𝒰.I₀) (P : E.Point g),
      EllipticCurve.Point.restrict E (pullback.fst g (𝒰.f i)) (-P)
        = -EllipticCurve.Point.restrict E (pullback.fst g (𝒰.f i)) P := by
    intro i P
    refine eq_neg_of_add_eq_zero_left ?_
    rw [← EllipticCurve.Point.restrict_add, neg_add_cancel,
      EllipticCurve.Point.restrict_zero]
  refine ⟨{ carrier := setOf fun P : E.Point g =>
              ∃ hh : T ⟶ D.ideal.subscheme, hh ≫ D.ideal.subschemeι = P.1
            zero_mem' := key 0 fun i =>
              (hHloc i (EllipticCurve.Point.restrict E (pullback.fst g (𝒰.f i)) 0)).mp
                (by rw [EllipticCurve.Point.restrict_zero]; exact (Hloc i).zero_mem)
            add_mem' := fun {P Q} hP hQ => key (P + Q) fun i =>
              (hHloc i (EllipticCurve.Point.restrict E (pullback.fst g (𝒰.f i)) (P + Q))).mp
                (by rw [EllipticCurve.Point.restrict_add]
                    exact (Hloc i).add_mem (hmem i P hP) (hmem i Q hQ))
            neg_mem' := fun {P} hP => key (-P) fun i =>
              (hHloc i (EllipticCurve.Point.restrict E (pullback.fst g (𝒰.f i)) (-P))).mp
                (by rw [hneg]; exact (Hloc i).neg_mem (hmem i P hP)) },
    fun P => Iff.rfl⟩

end RelEffCartierDiv

/-- **[W0-F3] (KM 1.7.2, `ℤ/N`-instance — the factorization core)** For coprime
`M, K ≥ 1`, a point `P ∈ E(S)` has Drinfeld exact order `M·K` iff `K·P` has exact
order `M` and `M·P` has exact order `K`.

KM 1.7.2 (print p. 26, verbatim): *"Then a homomorphism `φ : A → C(S)` is an
`A`-structure on `C/S` if and only if the two homomorphisms `φᵢ : Aᵢ → C(S)`,
`i = 1, 2`, are each `Aᵢ`-structures"* — instantiated at `A = ℤ/MK ≅ ℤ/M × ℤ/K`
(KM 1.7.1), where `φ = ⟨P⟩` restricts on the two factors to `⟨K·P⟩` and `⟨M·P⟩`
(the idempotent decomposition (3.5.1.3): `g ↦ (Bg, Ag)`).

Proof route (KM print pp. 27–31, transcribed in the decomposition artifact):
forward — split `G ≅ G[M] ×_S G[K]` (BB-DELIGNE `smul_eq_zero_of_factors` + the
coprime idempotent projector), force ranks geometrically, localize over the coprime
cover (`isSubgroup_of_openCover`), read distinctness on the étale factor (1.5.3
(3)⟹(1)), and run the translation-union argument `G = ∐ₐ Trans(φ(a₁))*(D₂)` for the
other factor; converse — `G₁ ×_S G₂ ↪ C` by the coprime-rank sum immersion, its
image divisor is `Σ [φ(a)]` by disjointness of translates. -/
theorem Section.hasExactOrder_mul_iff (P : E.Section) (M K : ℕ) [NeZero M] [NeZero K]
    (hMK : Nat.Coprime M K) :
    haveI : NeZero (M * K) := ⟨Nat.mul_ne_zero (NeZero.ne M) (NeZero.ne K)⟩
    P.HasExactOrder E (M * K) ↔
      ((K : ℤ) • P).HasExactOrder E M ∧ ((M : ℤ) • P).HasExactOrder E K := by sorry

/-- **[W0-F4] (KM 3.5.1, Γ₁-line)** The canonical factorization equivalence on
Drinfeld `Γ₁`-structures for a coprime splitting `N = M·K`:
`P ↦ (K·P, M·P)` (KM's choice (3.5.1.3), *"for `Γ₁(N)`: point `P` of exact order `N`
↦ points `BP, AP` of exact orders `A, B`"*), with inverse the CRT-weighted sum
`(P₁, P₂) ↦ K'·K·P₁ + M'·M·P₂`-normalised recombination (KM: the two structures
recombine because *"the second is `(A+B)` times the first"*, the first being the
inverse of the sum map (3.5.1.2)). Functorial in `S` (KM 3.5.1: *"functorial
isomorphisms"*) — naturality is recorded by `gammaOneStrFactorEquiv_fst/snd` and
consumed at the moduli-problem level in a later wave increment. -/
noncomputable def gammaOneStrFactorEquiv (M K : ℕ) [NeZero M] [NeZero K]
    (hMK : Nat.Coprime M K) :
    haveI : NeZero (M * K) := ⟨Nat.mul_ne_zero (NeZero.ne M) (NeZero.ne K)⟩
    { P : E.Section // P.HasExactOrder E (M * K) } ≃
      ({ P : E.Section // P.HasExactOrder E M } ×
        { P : E.Section // P.HasExactOrder E K }) := sorry

/-- **[W0-F4-fst]** The first component of the factorization equivalence is `K·P`
(KM 3.5.1's explicit `Γ₁`-line, first output `BP`). -/
theorem gammaOneStrFactorEquiv_fst (M K : ℕ) [NeZero M] [NeZero K]
    (hMK : Nat.Coprime M K)
    (P : { P : E.Section // haveI : NeZero (M * K) :=
      ⟨Nat.mul_ne_zero (NeZero.ne M) (NeZero.ne K)⟩; P.HasExactOrder E (M * K) }) :
    ((gammaOneStrFactorEquiv E M K hMK) P).1.1 = (K : ℤ) • P.1 := by sorry

/-- **[W0-F4-snd]** The second component of the factorization equivalence is `M·P`
(KM 3.5.1's explicit `Γ₁`-line, second output `AP`). -/
theorem gammaOneStrFactorEquiv_snd (M K : ℕ) [NeZero M] [NeZero K]
    (hMK : Nat.Coprime M K)
    (P : { P : E.Section // haveI : NeZero (M * K) :=
      ⟨Nat.mul_ne_zero (NeZero.ne M) (NeZero.ne K)⟩; P.HasExactOrder E (M * K) }) :
    ((gammaOneStrFactorEquiv E M K hMK) P).2.1 = (M : ℤ) • P.1 := by sorry

end ModularCurves
