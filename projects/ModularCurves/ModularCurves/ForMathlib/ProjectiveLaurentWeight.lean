/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project
-/
import ModularCurves.ForMathlib.ProjectiveStandardIntersectionRing

/-!
# Homogeneous Laurent weights on projective coordinate intersections

The Laurent exponents in one affine chart are reindexed by global integer exponent vectors of a
fixed total degree. The local localization condition becomes the requirement that every negative
global exponent occur among the coordinates defining the projective intersection.
-/

namespace MvPolynomial

noncomputable section

universe u

variable {σ : Type u}

/-- Integer exponent vectors of total degree `d`. -/
def HomogeneousLaurentExponent (σ : Type u) (d : ℤ) :=
  {e : σ →₀ ℤ // Finsupp.degree e = d}

namespace HomogeneousLaurentExponent

/-- The coordinates where a homogeneous Laurent exponent is negative. -/
def negativeSupport {d : ℤ} (e : HomogeneousLaurentExponent σ d) : Set σ :=
  {i | e.1 i < 0}

/-- A Laurent exponent is allowed on a coordinate intersection when all its negative coordinates
occur in the tuple defining that intersection. -/
def IsAllowedOn {d : ℤ} (e : HomogeneousLaurentExponent σ d)
    {n : ℕ} (a : Fin (n + 1) → σ) : Prop :=
  e.negativeSupport ⊆ Set.range a

end HomogeneousLaurentExponent

private def coordinateNonanchorEmbedding {n : ℕ} (a : Fin (n + 1) → σ) :
    {j : σ // j ≠ a 0} ↪ σ :=
  Function.Embedding.subtype _

private noncomputable def coordinateLocalToHomogeneousLaurentExponent {n : ℕ}
    (a : Fin (n + 1) → σ) (d : ℤ)
    (e : laurentExponentSubmonoid (coordinateTailExponent a)) :
    HomogeneousLaurentExponent σ d := by
  let f : σ →₀ ℤ :=
    Finsupp.embDomain (coordinateNonanchorEmbedding a) e.1 +
      Finsupp.single (a 0) (d - Finsupp.degree e.1)
  refine ⟨f, ?_⟩
  rw [show f = Finsupp.embDomain (coordinateNonanchorEmbedding a) e.1 +
    Finsupp.single (a 0) (d - Finsupp.degree e.1) by rfl]
  rw [map_add, Finsupp.degree_single]
  have hemb : Finsupp.degree
      (Finsupp.embDomain (coordinateNonanchorEmbedding a) e.1) =
      Finsupp.degree e.1 := by
    change (Finsupp.embDomain (coordinateNonanchorEmbedding a) e.1).sum
      (fun _ z => z) = e.1.sum (fun _ z => z)
    rw [Finsupp.sum_embDomain]
  rw [hemb]
  omega

private theorem coordinateLocalToHomogeneousLaurentExponent_apply_of_ne {n : ℕ}
    (a : Fin (n + 1) → σ) (d : ℤ)
    (e : laurentExponentSubmonoid (coordinateTailExponent a))
    (i : σ) (hi : i ≠ a 0) :
    (coordinateLocalToHomogeneousLaurentExponent a d e).1 i =
      e.1 ⟨i, hi⟩ := by
  change (Finsupp.embDomain (coordinateNonanchorEmbedding a) e.1) i +
    Finsupp.single (a 0) (d - Finsupp.degree e.1) i = e.1 ⟨i, hi⟩
  have hemb := Finsupp.embDomain_apply_self
    (coordinateNonanchorEmbedding a) e.1 ⟨i, hi⟩
  change (Finsupp.embDomain (coordinateNonanchorEmbedding a) e.1) i =
    e.1 ⟨i, hi⟩ at hemb
  rw [hemb]
  simp [hi]

private theorem coordinateLocalToHomogeneousLaurentExponent_apply_anchor {n : ℕ}
    (a : Fin (n + 1) → σ) (d : ℤ)
    (e : laurentExponentSubmonoid (coordinateTailExponent a)) :
    (coordinateLocalToHomogeneousLaurentExponent a d e).1 (a 0) =
      d - Finsupp.degree e.1 := by
  have hnot : a 0 ∉ Set.range (coordinateNonanchorEmbedding a) := by
    rintro ⟨j, hj⟩
    exact j.2 hj
  simp [coordinateLocalToHomogeneousLaurentExponent,
    Finsupp.embDomain_of_notMem_range _ _ _ hnot]

private theorem coordinateLocalToHomogeneousLaurentExponent_allowed {n : ℕ}
    (a : Fin (n + 1) → σ) (d : ℤ)
    (e : laurentExponentSubmonoid (coordinateTailExponent a)) :
    (coordinateLocalToHomogeneousLaurentExponent a d e).IsAllowedOn a := by
  intro i hi
  by_cases hanchor : i = a 0
  · exact ⟨0, hanchor.symm⟩
  · have hlocal : e.1 ⟨i, hanchor⟩ < 0 := by
      rw [← coordinateLocalToHomogeneousLaurentExponent_apply_of_ne a d e i hanchor]
      exact hi
    exact (coordinateTailExponent_ne_zero_iff a ⟨i, hanchor⟩).1 (e.2 _ hlocal)

private noncomputable def coordinateRestrictLaurentExponent {n : ℕ}
    (a : Fin (n + 1) → σ) (e : σ →₀ ℤ) : {j : σ // j ≠ a 0} →₀ ℤ :=
  Finsupp.comapDomain (coordinateNonanchorEmbedding a)
    (Finsupp.erase (a 0) e) (coordinateNonanchorEmbedding a).injective.injOn

@[simp]
private theorem coordinateRestrictLaurentExponent_apply {n : ℕ}
    (a : Fin (n + 1) → σ) (e : σ →₀ ℤ) (j : {j : σ // j ≠ a 0}) :
    coordinateRestrictLaurentExponent a e j = e j.1 := by
  rw [coordinateRestrictLaurentExponent, Finsupp.comapDomain_apply]
  change (Finsupp.erase (a 0) e) j.1 = e j.1
  rw [Finsupp.erase_ne j.2]

private theorem coordinateRestrictLaurentExponent_degree {n : ℕ}
    (a : Fin (n + 1) → σ) (e : σ →₀ ℤ) :
    Finsupp.degree (coordinateRestrictLaurentExponent a e) =
      Finsupp.degree e - e (a 0) := by
  let emb := coordinateNonanchorEmbedding a
  let r := coordinateRestrictLaurentExponent a e
  have hsupp : ↑(Finsupp.erase (a 0) e).support ⊆ Set.range emb := by
    intro i hi
    have hi0 : i ≠ a 0 := by
      intro h
      subst i
      simp at hi
    exact ⟨⟨i, hi0⟩, rfl⟩
  have herase : Finsupp.embDomain emb r = Finsupp.erase (a 0) e := by
    exact Finsupp.embDomain_comapDomain hsupp
  have hdegree : Finsupp.degree (Finsupp.embDomain emb r) = Finsupp.degree r := by
    change (Finsupp.embDomain emb r).sum (fun _ z => z) = r.sum (fun _ z => z)
    rw [Finsupp.sum_embDomain]
  have hsplit := congrArg Finsupp.degree (Finsupp.single_add_erase (a 0) e)
  rw [map_add, Finsupp.degree_single] at hsplit
  rw [← hdegree, herase]
  omega

private noncomputable def coordinateHomogeneousToLocalLaurentExponent {n : ℕ}
    (a : Fin (n + 1) → σ) (d : ℤ)
    (e : {e : HomogeneousLaurentExponent σ d // e.IsAllowedOn a}) :
    laurentExponentSubmonoid (coordinateTailExponent a) := by
  refine ⟨coordinateRestrictLaurentExponent a e.1.1, ?_⟩
  intro j hj
  apply (coordinateTailExponent_ne_zero_iff a j).2
  apply e.2
  simpa [HomogeneousLaurentExponent.negativeSupport] using hj

@[simp]
private theorem coordinateHomogeneousToLocalLaurentExponent_apply {n : ℕ}
    (a : Fin (n + 1) → σ) (d : ℤ)
    (e : {e : HomogeneousLaurentExponent σ d // e.IsAllowedOn a})
    (j : {j : σ // j ≠ a 0}) :
    (coordinateHomogeneousToLocalLaurentExponent a d e).1 j = e.1.1 j.1 := by
  exact coordinateRestrictLaurentExponent_apply a e.1.1 j

/-- Laurent exponents in the affine chart anchored at `a 0` are equivalent to global homogeneous
Laurent exponents whose negative support lies in the coordinate tuple. -/
noncomputable def coordinateLaurentExponentEquiv {n : ℕ}
    (a : Fin (n + 1) → σ) (d : ℤ) :
    laurentExponentSubmonoid (coordinateTailExponent a) ≃
      {e : HomogeneousLaurentExponent σ d // e.IsAllowedOn a} where
  toFun e := ⟨coordinateLocalToHomogeneousLaurentExponent a d e,
    coordinateLocalToHomogeneousLaurentExponent_allowed a d e⟩
  invFun := coordinateHomogeneousToLocalLaurentExponent a d
  left_inv e := by
    apply Subtype.ext
    ext j
    rw [coordinateHomogeneousToLocalLaurentExponent_apply]
    exact coordinateLocalToHomogeneousLaurentExponent_apply_of_ne a d e j.1 j.2
  right_inv e := by
    apply Subtype.ext
    apply Subtype.ext
    ext i
    by_cases hi : i = a 0
    · subst i
      rw [coordinateLocalToHomogeneousLaurentExponent_apply_anchor]
      change d - Finsupp.degree (coordinateRestrictLaurentExponent a e.1.1) =
        e.1.1 (a 0)
      rw [coordinateRestrictLaurentExponent_degree, e.1.2]
      omega
    · rw [coordinateLocalToHomogeneousLaurentExponent_apply_of_ne]
      exact coordinateHomogeneousToLocalLaurentExponent_apply a d e ⟨i, hi⟩

/-- Away from the anchor, the global homogeneous exponent is the original chart exponent. -/
@[simp]
theorem coordinateLaurentExponentEquiv_apply_of_ne {n : ℕ}
    (a : Fin (n + 1) → σ) (d : ℤ)
    (e : laurentExponentSubmonoid (coordinateTailExponent a))
    (i : σ) (hi : i ≠ a 0) :
    (coordinateLaurentExponentEquiv a d e).1.1 i = e.1 ⟨i, hi⟩ :=
  coordinateLocalToHomogeneousLaurentExponent_apply_of_ne a d e i hi

/-- At the anchor, the global exponent is chosen to make the total degree equal to `d`. -/
@[simp]
theorem coordinateLaurentExponentEquiv_apply_anchor {n : ℕ}
    (a : Fin (n + 1) → σ) (d : ℤ)
    (e : laurentExponentSubmonoid (coordinateTailExponent a)) :
    (coordinateLaurentExponentEquiv a d e).1.1 (a 0) =
      d - Finsupp.degree e.1 :=
  coordinateLocalToHomogeneousLaurentExponent_apply_anchor a d e

/-- The inverse homogeneous-to-chart map restricts a global exponent away from the anchor. -/
@[simp]
theorem coordinateLaurentExponentEquiv_symm_apply {n : ℕ}
    (a : Fin (n + 1) → σ) (d : ℤ)
    (e : {e : HomogeneousLaurentExponent σ d // e.IsAllowedOn a})
    (j : {j : σ // j ≠ a 0}) :
    ((coordinateLaurentExponentEquiv a d).symm e).1 j = e.1.1 j.1 :=
  coordinateHomogeneousToLocalLaurentExponent_apply a d e j

end

end MvPolynomial
