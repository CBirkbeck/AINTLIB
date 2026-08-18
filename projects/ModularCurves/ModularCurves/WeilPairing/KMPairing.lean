/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.Picard.SelfAdjointN
import ModularCurves.WeilPairing.KMSplitting

/-!
# `E[N](S) = Ker([N]^*)` on the relative Picard group (KM (2.8.1.7), ticket AP-D4)

The first step of the Katz–Mazur construction of the relative Weil pairing (KM (2.8.1), p. 88;
self-duality of `[N]` is KM 2.6.2.1). Writing `κ(Q) = [𝒪(D_Q − D_0)]` (`ModularCurves.kappa`,
`Picard/SelfAdjointN.lean`) for the GME (2.16) class of a section, and `[N]` (`mulByN`) for
multiplication by `N` on the base-changed curve, KM (2.8.1.7) identifies the `N`-torsion
sections with the `N`-torsion of the relative Picard group,

  `E[N](T) = Ker([N]^* : Pic⁰(E_T/T) → Pic⁰(E_T/T))`,

the identification being `κ`. Both sides are realised here inside `Pic (E ×_S T)`:

* `E[N](T)` is `ModularCurves.torsionPoints`, the `N`-torsion `AddSubgroup` of
  `(E.baseChange t).Point (𝟙 T)`;
* `Ker([N]^*)` is `ModularCurves.kerMulByN`, the subgroup `picRel ⊓ Ker([N]^*)` of
  `Pic (E ×_S T)`, where `picRel = Ker(0^*)` is the tree's kernel model of the relative Picard
  group (`Picard/RelativePic.lean`, GME p. 109).

## Why `picRel`, and not a separate `Pic⁰`

The tree has no fibrewise-degree function on `Pic`, so `Pic⁰` is not available as such; but for
`N ≠ 0` no degree hypothesis is needed to *state* the theorem, because the degree constraint is
already contained in `Ker([N]^*)`: on a geometric fibre `[N]` is finite flat of degree `N²`, so
`deg([N]^*L) = N² · deg L`, and `[N]^*L = 1` forces `deg L = 0` as soon as `N ≠ 0`. Intersecting
with `picRel` then pins the zero-section rigidification. So `kerMulByN E t N` *is* `Pic⁰[N]` for
`N ≠ 0`, with no `Pic⁰` API needed.

`N = 0` is genuinely different, and `kerMulByN_zero` records it: `mulByN E t 0 = π ≫ 0`, so
`Ker([0]^*) ⊇ picRel` and `kerMulByN E t 0 = picRel` outright. Since `κ` is **not** surjective
onto `picRel` (already over a field `Ker(0^*) = Pic(E)` carries every degree while `κ` hits only
degree zero — see the `Picard/SelfAdjointN.lean` module docstring), the `⊇` direction is *false*
at `N = 0`. That is why `N ≠ 0` is a hypothesis of `exists_torsionPoint_of_mem_kerMulByN` and not
decoration; `kerMulByN_zero` makes the reason machine-checked.

## Results

* `kappa_mem_kerMulByN`, `image_torsionPoints_subset_kerMulByN` — **the `⊆` direction, proved**.
  It is `(★′)` `picMap_mulByHom_kappa_eq_one` together with `kappa_mem_ker`. This is the half the
  pairing construction consumes: KM p. 88 needs exactly the triviality of `[N]^*ℒ_P` in order to
  write its normalized cocycle as a coboundary, so AP-D5's existence half is unblocked by this
  alone.
* `picMap_mulByN_kappa_eq_one_iff` — **"a torsion section is detected by its class being killed
  by `[N]^*`", proved on sections**: for a section `Q`, `[N]^* κ(Q) = 1 ↔ N • Q = 0`. This is the
  claimed equality of sets restricted along `κ`, and it is the sharpest unconditional-in-`N` form
  available. Its only extra input is `IsKappaInjective`, the *injectivity* half of Abel, taken as
  a named hypothesis.
* `exists_torsionPoint_of_mem_kerMulByN_of_surjective` — **the reduction of `⊇` to plain Abel,
  proved**: injectivity of `κ` plus surjectivity of `κ` onto `kerMulByN E t N` already give `⊇`.
  No further torsion input is needed, because `(★)` `picMap_mulByHom_kappa_pow` converts
  `[N]^* κ(Q) = 1` into `κ(N • Q) = 1` for free. In other words the `N`-torsion content of
  KM (2.8.1.7) is entirely `(★)`/`(★′)`; what is missing is only Abel itself.
* `kappa_image_torsionPoints_eq_kerMulByN_of_forall_exists` — the set equality, **proved**, from
  the `⊇` direction as a hypothesis.
* `exists_torsionPoint_of_mem_kerMulByN` — the `⊇` direction itself. **`sorry` (the single one in
  this file); see its docstring for the precise account of what blocks it.**
* `kappa_image_torsionPoints_eq_kerMulByN` — the headline set equality, unconditional.
  **Inherits that one `sorry` and therefore `sorryAx`** — flagged here and at the declaration.
* `kerMulByN_zero`, `kerMulByN_one`, `kappa_image_torsionPoints_eq_kerMulByN_one` — the two
  degenerate values of `N`, pinning the shape of the statement: the headline equality is
  **false** at `N = 0` and holds unconditionally, `sorry`-free, at `N = 1`.
* `exists_transitionUnit_eq_mul_inv_of_mem_torsionPoints` — **ticket AP-D5, the existence half**,
  `f_{i,j} ∘ [N] = h_i / h_j` (KM p. 88), obtained by feeding the `⊆` direction into the generic
  coboundary machinery of `WeilPairing/KMSplitting.lean`. Proved, and independent of the two
  open declarations below. Supporting: `mulByN_comp_snd`, `mulByN_preimage_preimage`.

## Axiom status

Everything above except the last two declarations is axiom-clean (`propext`, `Classical.choice`,
`Quot.sound`). `exists_torsionPoint_of_mem_kerMulByN` and
`kappa_image_torsionPoints_eq_kerMulByN` depend on `sorryAx`; nothing else in this file does, and
in particular the `⊆` direction and the detection theorem are free of it.
-/

universe u

open CategoryTheory AlgebraicGeometry Limits AlgebraicGeometry.Scheme.Modules

namespace ModularCurves

variable {S : Scheme.{u}} (E : EllipticCurve S) {T : Scheme.{u}}
variable (hsm : SmoothOfRelativeDimension 1 E.π) [IsSeparated E.π] (t : T ⟶ S)

/-! ## The two sides -/

/-- `E[N](T)`, the `N`-torsion subgroup of the `T`-points of the base-changed curve. The
multiple is taken in `ℤ` to match `(★′)` `picMap_mulByHom_kappa_eq_one`, whose torsion
hypothesis is `(N : ℤ) • Q = 0`. -/
def torsionPoints (N : ℕ) : AddSubgroup ((E.baseChange t).Point (𝟙 T)) where
  carrier := {Q | (N : ℤ) • Q = 0}
  zero_mem' := smul_zero _
  add_mem' := by
    intro a b ha hb
    show (N : ℤ) • (a + b) = 0
    rw [smul_add, ha, hb, add_zero]
  neg_mem' := by
    intro a ha
    show (N : ℤ) • (-a) = 0
    rw [smul_neg, ha, neg_zero]

omit [IsSeparated E.π] in
@[simp] theorem mem_torsionPoints {N : ℕ} {Q : (E.baseChange t).Point (𝟙 T)} :
    Q ∈ torsionPoints E t N ↔ (N : ℤ) • Q = 0 := Iff.rfl

/-- `Ker([N]^* : Pic⁰(E_T/T) → Pic⁰(E_T/T))`, realised inside `Pic (E ×_S T)` as the
intersection of the relative Picard group `picRel = Ker(0^*)` with the kernel of pullback along
multiplication by `N`. For `N ≠ 0` the fibre degree of a member is automatically zero (see the
module docstring), so this really is the `N`-torsion of `Pic⁰`. -/
noncomputable def kerMulByN (N : ℕ) : Subgroup (Scheme.Pic (pullback E.π t)) :=
  picRel E.π E.zero E.zero_π t ⊓ (Scheme.Pic.map (mulByN E t N)).ker

omit [IsSeparated E.π] in
theorem mem_kerMulByN {N : ℕ} {L : Scheme.Pic (pullback E.π t)} :
    L ∈ kerMulByN E t N ↔
      Scheme.Pic.map (baseChangeZero E.π E.zero E.zero_π t) L = 1 ∧
        Scheme.Pic.map (mulByN E t N) L = 1 := Iff.rfl

omit [IsSeparated E.π] in
theorem kerMulByN_le_picRel (N : ℕ) :
    kerMulByN E t N ≤ picRel E.π E.zero E.zero_π t := inf_le_left

/-! ## The two degenerate values of `N`

`N = 0` is recorded to justify the `N ≠ 0` hypothesis of the `⊇` direction, `N = 1` because it
pins the shape of the statement: at `N = 1` the headline equality holds unconditionally and
`sorry`-free (`kappa_image_torsionPoints_eq_kerMulByN_one`), at `N = 0` it is false. -/

omit [IsSeparated E.π] in
/-- Multiplication by `0` is the constant map `π ≫ 0` through the zero section. -/
theorem mulByN_zero :
    mulByN E t 0 = pullback.snd E.π t ≫ baseChangeZero E.π E.zero E.zero_π t := by
  have h := (E.baseChange t).point_smul_eq_comp_mulBy (E.baseChange t).π 0
    ⟨𝟙 (E.baseChange t).E, Category.id_comp _⟩
  rw [zero_smul, (E.baseChange t).point_zero_val, Category.id_comp] at h
  exact h.symm

omit [IsSeparated E.π] in
/-- **The `⊇` direction fails at `N = 0`.** `[0]^*` factors through the zero-section pullback,
so it kills all of `picRel` and `kerMulByN E t 0` is the whole relative Picard group — which `κ`
does not surject onto (`Picard/SelfAdjointN.lean` module docstring: over a field `Ker(0^*)` is
all of `Pic(E)`, carrying every degree, while `κ` hits only degree zero). -/
theorem kerMulByN_zero : kerMulByN E t 0 = picRel E.π E.zero E.zero_π t := by
  refine le_antisymm inf_le_left fun L hL => ⟨hL, ?_⟩
  have hzero : Scheme.Pic.map (baseChangeZero E.π E.zero E.zero_π t) L = 1 :=
    MonoidHom.mem_ker.mp hL
  refine MonoidHom.mem_ker.mpr ?_
  calc Scheme.Pic.map (mulByN E t 0) L
      = Scheme.Pic.map (pullback.snd E.π t ≫ baseChangeZero E.π E.zero E.zero_π t) L := by
        rw [mulByN_zero]
    _ = Scheme.Pic.map (pullback.snd E.π t)
          (Scheme.Pic.map (baseChangeZero E.π E.zero E.zero_π t) L) := by
        rw [Scheme.Pic.map_comp]; rfl
    _ = 1 := by rw [hzero, map_one]

omit [IsSeparated E.π] in
/-- Multiplication by `1` is the identity. -/
theorem mulByN_one : mulByN E t 1 = 𝟙 (pullback E.π t) := by
  have h := (E.baseChange t).point_smul_eq_comp_mulBy (E.baseChange t).π 1
    ⟨𝟙 (E.baseChange t).E, Category.id_comp _⟩
  rw [one_smul] at h
  exact (Category.id_comp _).symm.trans h.symm

omit [IsSeparated E.π] in
theorem torsionPoints_one : torsionPoints E t 1 = ⊥ := by
  ext Q
  rw [mem_torsionPoints, Nat.cast_one, one_zsmul, AddSubgroup.mem_bot]

omit [IsSeparated E.π] in
theorem kerMulByN_one : kerMulByN E t 1 = ⊥ := by
  refine le_antisymm (fun L hL => ?_) bot_le
  have h : Scheme.Pic.map (mulByN E t 1) L = 1 := hL.2
  rwa [mulByN_one, Scheme.Pic.map_id] at h

/-! ## The `⊆` direction — KM (2.8.1.7), the half the pairing construction consumes -/

/-- **(`⊆` of KM (2.8.1.7))** The class of an `N`-torsion section is killed by `[N]^*` and by
`0^*`, i.e. lies in `Ker([N]^* : Pic⁰ → Pic⁰)`.

The two components are `(★′)` `picMap_mulByHom_kappa_eq_one` and `kappa_mem_ker`, both proved
and axiom-clean in `Picard/SelfAdjointN.lean`. -/
theorem kappa_mem_kerMulByN (N : ℕ) (Q : (E.baseChange t).Point (𝟙 T))
    (hQ : Q ∈ torsionPoints E t N) : kappa E hsm t Q ∈ kerMulByN E t N :=
  ⟨kappa_mem_ker E hsm t Q, picMap_mulByHom_kappa_eq_one E hsm t N Q hQ⟩

/-- **(`⊆` of KM (2.8.1.7), set form)** `κ (E[N](T)) ⊆ Ker([N]^*)`. -/
theorem image_torsionPoints_subset_kerMulByN (N : ℕ) :
    kappa E hsm t '' (torsionPoints E t N) ⊆
      (kerMulByN E t N : Set (Scheme.Pic (pullback E.π t))) := by
  rintro _ ⟨Q, hQ, rfl⟩
  exact kappa_mem_kerMulByN E hsm t N Q hQ

/-! ## Detection: the equality of sets, restricted along `κ` -/

/-- **Abel injectivity**, isolated as a named hypothesis: a section whose divisor class equals
that of the zero section is the zero section. Equivalently `Function.Injective (kappa E hsm t)`
(`isKappaInjective_iff_injective`), since `κ` is a group homomorphism (`kappa_add`).

This is the injective half of Abel's theorem for `E/S`; over a field it is the genus-one
statement that no nonconstant function has a single simple pole. It is *not* available in the
tree (`EllipticCurve/AbelEquivalence.lean` builds the divisor↔section dictionary but not this),
which is why it appears as a hypothesis rather than as a proved lemma. -/
def IsKappaInjective : Prop :=
  ∀ P : (E.baseChange t).Point (𝟙 T), kappa E hsm t P = 1 → P = 0

theorem isKappaInjective_iff_injective :
    IsKappaInjective E hsm t ↔ Function.Injective (kappa E hsm t) := by
  constructor
  · intro h P P' hPP'
    have hsub : kappa E hsm t (P - P') = 1 := by
      rw [sub_eq_add_neg, kappa_add, kappa_neg, hPP', mul_inv_cancel]
    exact sub_eq_zero.mp (h _ hsub)
  · intro h P hP
    exact h (hP.trans (kappa_zero E hsm t).symm)

/-- **KM (2.8.1.7) on sections: a torsion section is detected by its class being killed by
pullback along multiplication by `N`.** For any `N` (including `N = 0`) and any section `Q`,

  `[N]^* κ(Q) = 1  ↔  N • Q = 0`.

`←` is `(★′)` `picMap_mulByHom_kappa_eq_one`; `→` is `(★)` `picMap_mulByHom_kappa_pow`, which
turns `[N]^* κ(Q) = 1` into `κ(N • Q) = 1`, followed by injectivity of `κ`.

This is the claimed set equality `E[N](T) = Ker([N]^*)` pulled back along `κ`, and it needs no
hypothesis on `N`: the `N = 0` failure of the full statement is a failure of *surjectivity* of
`κ`, not of detection. -/
theorem picMap_mulByN_kappa_eq_one_iff (hinj : IsKappaInjective E hsm t) (N : ℕ)
    (Q : (E.baseChange t).Point (𝟙 T)) :
    Scheme.Pic.map (mulByN E t N) (kappa E hsm t Q) = 1 ↔ Q ∈ torsionPoints E t N := by
  refine ⟨fun h => ?_, picMap_mulByHom_kappa_eq_one E hsm t N Q⟩
  rw [picMap_mulByHom_kappa_pow, ← kappa_nsmul] at h
  rw [mem_torsionPoints, natCast_zsmul]
  exact hinj _ h

/-- **The `⊇` direction reduces to plain Abel.** Given injectivity of `κ` and surjectivity of
`κ` onto `kerMulByN E t N`, the torsion of the produced section is automatic: it is `(★)`.

So KM (2.8.1.7) carries *no* torsion content beyond `(★)`/`(★′)`; the whole of its `⊇` direction
is the bijectivity of the Abel map. -/
theorem exists_torsionPoint_of_mem_kerMulByN_of_surjective (hinj : IsKappaInjective E hsm t)
    (N : ℕ) (hsurj : ∀ L ∈ kerMulByN E t N,
      ∃ Q : (E.baseChange t).Point (𝟙 T), kappa E hsm t Q = L)
    (L : Scheme.Pic (pullback E.π t)) (hL : L ∈ kerMulByN E t N) :
    ∃ Q : (E.baseChange t).Point (𝟙 T), Q ∈ torsionPoints E t N ∧ kappa E hsm t Q = L := by
  obtain ⟨Q, hQ⟩ := hsurj L hL
  refine ⟨Q, ?_, hQ⟩
  rw [← picMap_mulByN_kappa_eq_one_iff E hsm t hinj N Q, hQ]
  exact hL.2

/-- The set equality `E[N](T) = Ker([N]^*)`, from the `⊇` direction as a hypothesis. The `⊆`
direction is supplied by `image_torsionPoints_subset_kerMulByN`, which is proved. -/
theorem kappa_image_torsionPoints_eq_kerMulByN_of_forall_exists (N : ℕ)
    (habel : ∀ L ∈ kerMulByN E t N, ∃ Q : (E.baseChange t).Point (𝟙 T),
      Q ∈ torsionPoints E t N ∧ kappa E hsm t Q = L) :
    kappa E hsm t '' (torsionPoints E t N) =
      (kerMulByN E t N : Set (Scheme.Pic (pullback E.π t))) := by
  refine Set.Subset.antisymm (image_torsionPoints_subset_kerMulByN E hsm t N) fun L hL => ?_
  obtain ⟨Q, hQtors, hQ⟩ := habel L hL
  exact ⟨Q, hQtors, hQ⟩

/-! ## The `⊇` direction — open -/

/-- **(`⊇` of KM (2.8.1.7)) — OPEN, the single `sorry` of this file.** A class killed by `0^*`
and by `[N]^*`, with `N ≠ 0`, is the class of an `N`-torsion section.

`N ≠ 0` is necessary: `kerMulByN_zero` shows `kerMulByN E t 0 = picRel`, onto which `κ` is not
surjective.

**What blocks it.** By `exists_torsionPoint_of_mem_kerMulByN_of_surjective` (proved above) the
statement is exactly *Abel's theorem*, in the two halves

1. **injectivity** — `IsKappaInjective E hsm t`, i.e. `κ(Q) = 1 → Q = 0`. Nothing in the tree
   proves it: `EllipticCurve/AbelEquivalence.lean` sets up the divisor↔section dictionary but
   never the rigidity `D_Q ∼ D_0 ⟹ Q = 0`;
2. **surjectivity onto `kerMulByN E t N`** — for `L` in the kernel, `L ⊗ 𝒪(D_0)` is fibrewise of
   degree one, so `f_*(L ⊗ 𝒪(D_0))` is invertible by cohomology and base change and the
   evaluation map cuts out a relative effective Cartier divisor of degree one; that divisor is
   `D_Q` for a unique section `Q` by `exists_section_of_degree_one`
   (`EllipticCurve/AbelEquivalence.lean`, **proved and axiom-clean**), and `L = κ(Q)` after
   rigidifying. The step that is *not* available is producing the divisor from the class:
   `relEffCartierDiv_of_degreeOne_package` (`AbelEquivalence.lean:971`),
   `exists_relEffCartierDiv_of_degreeOne` (`:994`) and
   `relEffCartierDiv_degree_one_of_degreeOne` (`:1013`) are all `sorry`, as is
   `evalGenerator_mem_nonZeroDivisors` (`:848`). Those are ticket AP-B3/AP2-B2.

   Surjectivity also silently uses the fibre-degree bookkeeping described in the module
   docstring: `deg([N]^*L) = N² · deg L` on geometric fibres, so `[N]^*L = 1` and `N ≠ 0` give
   `deg L = 0` and put `L` in the range of `κ`. The tree has no fibrewise degree function on
   `Pic`, so that too has to be built.

No hypothesis has been weakened to make this statement reachable, and nothing else in this file
depends on it apart from `kappa_image_torsionPoints_eq_kerMulByN`. Consumers that want an
axiom-clean result should use `exists_torsionPoint_of_mem_kerMulByN_of_surjective` and carry the
two Abel halves as hypotheses. -/
theorem exists_torsionPoint_of_mem_kerMulByN (N : ℕ) (hN : N ≠ 0)
    (L : Scheme.Pic (pullback E.π t)) (hL : L ∈ kerMulByN E t N) :
    ∃ Q : (E.baseChange t).Point (𝟙 T), Q ∈ torsionPoints E t N ∧ kappa E hsm t Q = L := by
  sorry

/-- **KM (2.8.1.7)**, `E[N](T) = Ker([N]^* : Pic⁰(E_T/T) → Pic⁰(E_T/T))` via `κ`, for `N ≠ 0`.

**Depends on `sorryAx`**, through `exists_torsionPoint_of_mem_kerMulByN` and only through it. The
`⊆` half, `image_torsionPoints_subset_kerMulByN`, is axiom-clean and is the half KM p. 88 uses. -/
theorem kappa_image_torsionPoints_eq_kerMulByN (N : ℕ) (hN : N ≠ 0) :
    kappa E hsm t '' (torsionPoints E t N) =
      (kerMulByN E t N : Set (Scheme.Pic (pullback E.π t))) :=
  kappa_image_torsionPoints_eq_kerMulByN_of_forall_exists E hsm t N
    (exists_torsionPoint_of_mem_kerMulByN E hsm t N hN)

/-- **The `N = 1` instance of KM (2.8.1.7), unconditional and `sorry`-free.** Both sides are
trivial: `torsionPoints E t 1 = ⊥` and `kerMulByN E t 1 = ⊥` because `[1]` is the identity.

Kept as a consistency check on the shape of `kappa_image_torsionPoints_eq_kerMulByN`: together
with `kerMulByN_zero` (where the statement is false) it pins both ends of the `N` range without
appealing to the open `⊇` direction. -/
theorem kappa_image_torsionPoints_eq_kerMulByN_one :
    kappa E hsm t '' (torsionPoints E t 1) =
      (kerMulByN E t 1 : Set (Scheme.Pic (pullback E.π t))) := by
  rw [torsionPoints_one, kerMulByN_one, AddSubgroup.coe_bot, Subgroup.coe_bot,
    Set.image_singleton, kappa_zero]

/-! ## AP-D5: `f_{i,j} ∘ [N] = h_i / h_j` for the curve

The `⊆` direction proved above is exactly the input of the Katz–Mazur coboundary argument
(KM p. 88): `[N]^* κ(Q) = 1` for an `N`-torsion section `Q` says the pullback of `κ(Q)` along
`[N]` is trivial, so the pulled-back transition cocycle splits. The generic splitting machinery
is `WeilPairing/KMSplitting.lean`; here it is instantiated at `f = [N]` and `L = κ(Q)`.

Nothing in this section touches, or depends on, the two open `⊇`-direction declarations above. -/

omit [IsSeparated E.π] in
/-- `[N]` is a morphism over the base: it commutes with the structure map, so it maps each
`π⁻¹(U)` into itself. This is why KM's `h_i` live on `π⁻¹(U_i)`, the same opens as the
`f_{i,j}`. -/
theorem mulByN_comp_snd (N : ℕ) :
    mulByN E t N ≫ pullback.snd E.π t = pullback.snd E.π t :=
  (E.baseChange t).mulByHom_π (N : ℤ)

omit [IsSeparated E.π] in
/-- The preimage under `[N]` of the preimage of a base open is that same open. -/
theorem mulByN_preimage_preimage (N : ℕ) (V : T.Opens) :
    mulByN E t N ⁻¹ᵁ (pullback.snd E.π t ⁻¹ᵁ V) = pullback.snd E.π t ⁻¹ᵁ V :=
  congrArg (fun m : pullback E.π t ⟶ T => m ⁻¹ᵁ V) (mulByN_comp_snd E t N)

/-- **(AP-D5 EXISTENCE, for the curve — KM p. 88)** Let `Q` be an `N`-torsion section and `M` an
invertible sheaf representing `κ(Q)`, trivialized over opens `W i` with transition units
`f_{i,j}`. Then there are units `h_i` on `[N]⁻¹(W i)` with

  `f_{i,j} ∘ [N] = h_i · h_j⁻¹`   on `[N]⁻¹(W i ⊓ W j)`,

which is Katz–Mazur's factorisation. The whole `N`-dependence enters through `(★′)`
`picMap_mulByHom_kappa_eq_one`, i.e. through the `⊆` direction of AP-D4 proved above; the
splitting itself is `exists_transitionUnit_eq_mul_inv_of_picMap_eq_one`
(`WeilPairing/KMSplitting.lean`). Uniqueness of the `h_i` is `eq_of_div_mem_kUnits`
(`WeilPairing/UnitSheaf.lean`), from AP-D2.

The `W i` must be a trivialising cover of the **curve**. Taking `W i = π⁻¹(U i)` for a cover of
the base makes the hypothesis `e i` unsatisfiable except degenerately, since `κ(Q)` is fibrewise
nontrivial and so is not trivial over the preimage of a base open
(`WeilPairing/KMNormalisation.lean`, "Degenerate cases"). KM's opens over the base appear one step
later, in the patching `AP-D6`: they are the traces `P⁻¹([N]⁻¹(W i))` of an `N`-torsion section
`P`, and *those* do cover the base (`WeilPairing/KMPatching.lean`). `mulByN_preimage_preimage`
records the one thing that is true about base opens — that `[N]` preserves them — but `AP-D6`
does not need it. -/
theorem exists_transitionUnit_eq_mul_inv_of_mem_torsionPoints (N : ℕ)
    (Q : (E.baseChange t).Point (𝟙 T)) (hQ : Q ∈ torsionPoints E t N)
    (M : (pullback E.π t).Modules)
    (hM : letI := Scheme.Modules.monoidalCategory (pullback E.π t)
      (kappa E hsm t Q).val = toSkeleton M)
    {ι : Type*} (W : ι → (pullback E.π t).Opens)
    (e : ∀ i, M.over (W i) ≅
      _root_.SheafOfModules.unit ((pullback E.π t).ringCatSheaf.over (W i))) :
    ∃ h : ∀ i, Γ(pullback E.π t, mulByN E t N ⁻¹ᵁ W i)ˣ, ∀ i j,
      Units.map ((mulByN E t N).app (W i ⊓ W j)).hom.toMonoidHom
          (trivializationTransitionUnit (W i ⊓ W j)
            (SheafOfModules.restrictOverTrivialization (pullback E.π t).ringCatSheaf M (W i) (e i)
              (Over.mk (homOfLE (inf_le_left : W i ⊓ W j ≤ W i))))
            (SheafOfModules.restrictOverTrivialization (pullback E.π t).ringCatSheaf M (W j) (e j)
              (Over.mk (homOfLE (inf_le_right : W i ⊓ W j ≤ W j))))) =
        Units.map ((pullback E.π t).presheaf.map (homOfLE ((mulByN E t N).preimage_mono
              (inf_le_left : W i ⊓ W j ≤ W i))).op).hom.toMonoidHom (h i) *
          (Units.map ((pullback E.π t).presheaf.map (homOfLE ((mulByN E t N).preimage_mono
            (inf_le_right : W i ⊓ W j ≤ W j))).op).hom.toMonoidHom (h j))⁻¹ :=
  exists_transitionUnit_eq_mul_inv_of_picMap_eq_one (mulByN E t N) (kappa E hsm t Q) M hM
    (picMap_mulByHom_kappa_eq_one E hsm t N Q hQ) W e

end ModularCurves
