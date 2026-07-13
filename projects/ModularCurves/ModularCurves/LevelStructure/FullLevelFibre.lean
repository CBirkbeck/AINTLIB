/-
Copyright (c) 2026 The AINTLIB Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AINTLIB Authors
-/
import ModularCurves.LevelStructure.Basic
import ModularCurves.LevelStructure.FibreFullLevel
import ModularCurves.EllipticCurve.MulByHomUnramified

/-!
# The fibre connector for the full-level bridge (T-D8-bridge, steps β/D-glue)

The naive full-level generation condition — *every* `N`-torsion point of the geometric
fibre lies in the closure of the pulled-back `P, Q` — is reshaped, in three steps, into the
group-theoretic distinctness of the `N²` combinations `[a]P + [b]Q` (`comboFamily`):

* `naiveClosure_iff_torsion_filled` — the condition ⟺ the closure fills the entire
  `N`-torsion subgroup `E[N]_t = torsionBy ℤ (E.Point t) N`;
* `closure_top_iff_ambient_eq` — closure `= ⊤` inside `E[N]_t` ⟺ the ambient closure equals
  `E[N]_t`;
* `comboFamily_injective_iff_closure_top` (step D) + `torsion_geometricFibre_rank_two`
  (T-B6, `#E[N]_t = N²`) — distinctness ⟺ closure `= ⊤`.

Composed: the naive generation condition over a geometric point ⟺ the `N²` combinations are
pairwise distinct in the fibre. This is the fibre half of KM 1.4.4; the scheme half
(`sectionsDivisor.ideal = torsionIdeal ⟺ fibrewise distinct`, KM 1.9–1.10) is separate.
-/

open AlgebraicGeometry CategoryTheory

universe u

namespace ModularCurves

/-- **Subgroup closure bridge.** For a pair `a, b` of a subgroup `H`, the ambient closure of
`{a, b}` equals `H` iff the closure of the same pair, viewed *inside* `H`, is all of `H`. -/
theorem closure_pair_eq_iff_closure_top {A : Type*} [AddCommGroup A] (H : AddSubgroup A)
    {a b : A} (ha : a ∈ H) (hb : b ∈ H) :
    AddSubgroup.closure {a, b} = H ↔
      AddSubgroup.closure {(⟨a, ha⟩ : H), ⟨b, hb⟩} = ⊤ := by
  have hmap : AddSubgroup.map H.subtype (AddSubgroup.closure {(⟨a, ha⟩ : H), ⟨b, hb⟩})
      = AddSubgroup.closure {a, b} := by
    rw [AddMonoidHom.map_closure]
    congr 1
    rw [Set.image_insert_eq, Set.image_singleton]
    rfl
  have htop : AddSubgroup.map H.subtype (⊤ : AddSubgroup H) = H := by
    ext x; simp
  constructor
  · intro h
    apply AddSubgroup.map_injective (AddSubgroup.subtype_injective H)
    rw [hmap, htop]; exact h
  · intro h
    rw [← hmap, h]; exact htop

namespace EllipticCurve

variable {S : Scheme.{u}} (E : EllipticCurve S)

/-- The `N`-torsion subgroup of the fibre point group `E.Point t`, as an `AddSubgroup`. -/
noncomputable abbrev fibreTorsion {T : Scheme.{u}} (t : T ⟶ S) (N : ℕ) :
    AddSubgroup (E.Point t) :=
  (Submodule.torsionBy ℤ (E.Point t) (N : ℤ)).toAddSubgroup

variable {E}

lemma mem_fibreTorsion {T : Scheme.{u}} {t : T ⟶ S} {N : ℕ} {x : E.Point t} :
    x ∈ E.fibreTorsion t N ↔ (N : ℤ) • x = 0 := by
  rw [fibreTorsion, Submodule.mem_toAddSubgroup, Submodule.mem_torsionBy_iff]

/-- The pulled-back `N`-killed section lands in the `N`-torsion subgroup of the fibre. -/
lemma pull_mem_fibreTorsion {T : Scheme.{u}} (t : T ⟶ S) {N : ℕ} {P : E.Section}
    (hP : (N : ℤ) • P = 0) : Point.pull E t P ∈ E.fibreTorsion t N :=
  mem_fibreTorsion.mpr <| by rw [← Point.pull_zsmul, hP, Point.pull_zero]

/-- **[Step β, reshaping]** The naive full-level generation condition over a fibre — every
`N`-torsion point lies in the closure of `pull P, pull Q` — holds iff that closure is the
*entire* `N`-torsion subgroup `E[N]_t`. -/
theorem naiveClosure_iff_torsion_filled {T : Scheme.{u}} (t : T ⟶ S) (N : ℕ)
    {P Q : E.Section} (hP : (N : ℤ) • P = 0) (hQ : (N : ℤ) • Q = 0) :
    (∀ x : E.Point t, (N : ℤ) • x = 0 →
        x ∈ AddSubgroup.closure {Point.pull E t P, Point.pull E t Q}) ↔
      AddSubgroup.closure {Point.pull E t P, Point.pull E t Q} = E.fibreTorsion t N := by
  have hsub : AddSubgroup.closure {Point.pull E t P, Point.pull E t Q} ≤
      E.fibreTorsion t N := by
    rw [AddSubgroup.closure_le]
    intro y hy
    rcases (by simpa using hy : y = Point.pull E t P ∨ y = Point.pull E t Q) with rfl | rfl
    · exact pull_mem_fibreTorsion t hP
    · exact pull_mem_fibreTorsion t hQ
  constructor
  · intro hgen
    refine le_antisymm hsub fun x hx => hgen x (mem_fibreTorsion.mp hx)
  · intro heq x hx
    rw [heq]
    exact mem_fibreTorsion.mpr hx

/-- **[Steps β + subgroup bridge, composed]** The naive full-level generation condition over
a fibre ⟺ the pulled `P, Q`, viewed *inside* the `N`-torsion subgroup `E[N]_t`, generate it
(closure `= ⊤`). Route-agnostic: no invertibility / rank input yet. -/
theorem naiveClosure_iff_subgroup_closure_top {T : Scheme.{u}} (t : T ⟶ S) (N : ℕ)
    {P Q : E.Section} (hP : (N : ℤ) • P = 0) (hQ : (N : ℤ) • Q = 0) :
    (∀ x : E.Point t, (N : ℤ) • x = 0 →
        x ∈ AddSubgroup.closure {Point.pull E t P, Point.pull E t Q}) ↔
      AddSubgroup.closure
          {(⟨Point.pull E t P, pull_mem_fibreTorsion t hP⟩ : E.fibreTorsion t N),
            ⟨Point.pull E t Q, pull_mem_fibreTorsion t hQ⟩} = ⊤ :=
  (naiveClosure_iff_torsion_filled t N hP hQ).trans
    (closure_pair_eq_iff_closure_top (E.fibreTorsion t N) _ _)

/-- The `N`-torsion of a geometric fibre in which `N` is invertible is finite (T-B6). -/
lemma finite_fibreTorsion {N : ℕ} [NeZero N] {k : Type u} [Field k] [IsAlgClosed k]
    (t : Spec (CommRingCat.of k) ⟶ S) (hN : (N : k) ≠ 0) : Finite (E.fibreTorsion t N) := by
  obtain ⟨e⟩ := E.torsion_geometricFibre_rank_two N k t hN
  exact Finite.of_equiv _ e.symm.toEquiv

/-- The `N`-torsion of a geometric fibre in which `N` is invertible has exactly `N²`
elements (T-B6, `E[N]_{k̄} ≅ (ℤ/N)²`). -/
lemma natCard_fibreTorsion {N : ℕ} [NeZero N] {k : Type u} [Field k] [IsAlgClosed k]
    (t : Spec (CommRingCat.of k) ⟶ S) (hN : (N : k) ≠ 0) :
    Nat.card (E.fibreTorsion t N) = N ^ 2 := by
  obtain ⟨e⟩ := E.torsion_geometricFibre_rank_two N k t hN
  show Nat.card (Submodule.torsionBy ℤ (E.Point t) (N : ℤ)) = N ^ 2
  rw [Nat.card_congr e.toEquiv, Nat.card_fun, Nat.card_zmod, Nat.card_fin]

/-- `(N : ℤ) • P' = 0` for the packaged torsion element `P' = ⟨pull P, _⟩`. -/
lemma zsmul_pull_subtype_eq_zero {T : Scheme.{u}} (t : T ⟶ S) {N : ℕ} {P : E.Section}
    (hP : (N : ℤ) • P = 0) :
    (N : ℤ) • (⟨Point.pull E t P, pull_mem_fibreTorsion t hP⟩ : E.fibreTorsion t N) = 0 := by
  apply Subtype.ext
  rw [AddSubgroup.coe_zsmul, ZeroMemClass.coe_zero]
  show (N : ℤ) • Point.pull E t P = 0
  rw [← Point.pull_zsmul, hP, Point.pull_zero]

/-- **[Fibre side, complete]** Over a geometric point in which `N` is invertible, the naive
full-level generation condition ⟺ the `N²` combinations `[a]·(pull P) + [b]·(pull Q)` are
pairwise distinct in `E[N]_t`. Composes the reshaping chain with step D
(`comboFamily_injective_iff_closure_top`) and T-B6 (`#E[N]_t = N²`). -/
theorem naive_iff_comboFamily_injective {N : ℕ} [NeZero N] {k : Type u} [Field k]
    [IsAlgClosed k] (t : Spec (CommRingCat.of k) ⟶ S) (hN : (N : k) ≠ 0)
    {P Q : E.Section} (hP : (N : ℤ) • P = 0) (hQ : (N : ℤ) • Q = 0) :
    (∀ x : E.Point t, (N : ℤ) • x = 0 →
        x ∈ AddSubgroup.closure {Point.pull E t P, Point.pull E t Q}) ↔
      Function.Injective (comboFamily N
        (⟨Point.pull E t P, pull_mem_fibreTorsion t hP⟩ : E.fibreTorsion t N)
        ⟨Point.pull E t Q, pull_mem_fibreTorsion t hQ⟩) := by
  haveI := finite_fibreTorsion (E := E) t hN
  rw [naiveClosure_iff_subgroup_closure_top t N hP hQ,
    ← comboFamily_injective_iff_closure_top N _ _ (zsmul_pull_subtype_eq_zero t hP)
      (zsmul_pull_subtype_eq_zero t hQ) (natCard_fibreTorsion t hN)]

variable (E) in
/-- **[YF-⊆ group core].** Over a geometric point where `N` is invertible, if two `N`-torsion
points `A, B` of the fibre generate its whole `N`-torsion, then for coefficients `c, d ∈ [0, N)`
not both zero the combination `[c]A + [d]B` is nonzero. (The `Fin N × Fin N`-indexed
no-vanishing register that `[YF-⊆]` contradicts against a `combPoint = 0` at the geometric
point.) Pigeonhole: the `N²` combinations are surjective onto the `N²`-element torsion, hence
injective, so only the zero-index combination is `0`. -/
theorem comb_ne_zero_of_generates {N : ℕ} [NeZero N] {k : Type u} [Field k] [IsAlgClosed k]
    {γ : Spec (CommRingCat.of k) ⟶ S} (hN : (N : k) ≠ 0) {A B : E.Point γ}
    (hA : (N : ℤ) • A = 0) (hB : (N : ℤ) • B = 0)
    (hgen : ∀ x : E.Point γ, (N : ℤ) • x = 0 → x ∈ AddSubgroup.closure {A, B})
    {c d : ℕ} (hc : c < N) (hd : d < N) (hne : ¬(c = 0 ∧ d = 0)) :
    (c : ℤ) • A + (d : ℤ) • B ≠ 0 := by
  haveI : NeZero (N ^ 2) := ⟨pow_ne_zero 2 (NeZero.ne N)⟩
  have hAmem : A ∈ E.fibreTorsion γ N := mem_fibreTorsion.mpr hA
  have hBmem : B ∈ E.fibreTorsion γ N := mem_fibreTorsion.mpr hB
  -- the generated closure is the entire `N`-torsion subgroup
  have hsub : AddSubgroup.closure {A, B} ≤ E.fibreTorsion γ N := by
    rw [AddSubgroup.closure_le]
    intro y hy
    rcases (by simpa using hy : y = A ∨ y = B) with rfl | rfl
    exacts [hAmem, hBmem]
  have heq : AddSubgroup.closure {A, B} = E.fibreTorsion γ N :=
    le_antisymm hsub fun x hx => hgen x (mem_fibreTorsion.mp hx)
  have htop : AddSubgroup.closure
      {(⟨A, hAmem⟩ : E.fibreTorsion γ N), ⟨B, hBmem⟩} = ⊤ :=
    (closure_pair_eq_iff_closure_top (E.fibreTorsion γ N) hAmem hBmem).mp heq
  haveI := finite_fibreTorsion (E := E) γ hN
  have hcard : Nat.card (E.fibreTorsion γ N) = N ^ 2 := natCard_fibreTorsion γ hN
  have hzsA : (N : ℤ) • (⟨A, hAmem⟩ : E.fibreTorsion γ N) = 0 := by
    apply Subtype.ext; rw [AddSubgroup.coe_zsmul, ZeroMemClass.coe_zero]; exact hA
  have hzsB : (N : ℤ) • (⟨B, hBmem⟩ : E.fibreTorsion γ N) = 0 := by
    apply Subtype.ext; rw [AddSubgroup.coe_zsmul, ZeroMemClass.coe_zero]; exact hB
  -- the index `i = c + d·N < N²` is nonzero
  have hi : c + d * N < N ^ 2 := by
    have hNN : N ≤ N * N := Nat.le_mul_of_pos_left N (Nat.pos_of_ne_zero (NeZero.ne N))
    have h1 : d * N ≤ (N - 1) * N := Nat.mul_le_mul_right N (Nat.le_sub_one_of_lt hd)
    have h2 : (N - 1) * N = N * N - N := Nat.sub_one_mul N N
    rw [pow_two]; omega
  have hidx : (⟨c + d * N, hi⟩ : Fin (N ^ 2)) ≠ 0 := by
    intro hval
    have hval2 : c + d * N = 0 := by
      have h := congrArg Fin.val hval
      simpa using h
    have hc0 : c = 0 := by omega
    have hdN0 : d * N = 0 := by omega
    rcases Nat.mul_eq_zero.mp hdN0 with h | h
    · exact hne ⟨hc0, h⟩
    · exact absurd h (NeZero.ne N)
  have hkey := comboFamily_ne_zero_of_closure_top N (⟨A, hAmem⟩ : E.fibreTorsion γ N)
    ⟨B, hBmem⟩ hzsA hzsB hcard htop hidx
  intro h0
  apply hkey
  apply Subtype.ext
  rw [ZeroMemClass.coe_zero, comboFamily, AddSubgroup.coe_add, AddSubgroup.coe_zsmul,
    AddSubgroup.coe_zsmul]
  show (((c + d * N) % N : ℕ) : ℤ) • A + (((c + d * N) / N : ℕ) : ℤ) • B = 0
  rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hc, Nat.add_mul_div_right _ _
    (Nat.pos_of_ne_zero (NeZero.ne N)), Nat.div_eq_of_lt hc, zero_add]
  exact h0

end EllipticCurve

end ModularCurves
