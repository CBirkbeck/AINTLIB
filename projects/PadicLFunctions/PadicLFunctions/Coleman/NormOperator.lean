/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import PadicLFunctions.MeasureR.FormalPsi
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.RingTheory.Norm.Basic
import Mathlib.RingTheory.Trace.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.RingTheory.PowerSeries.PiTopology
import Mathlib.Topology.Metrizable.Uniformity
import Mathlib.Data.Finsupp.Encodable

/-!
# The norm operator `𝒩` on `ℤ_p⟦T⟧` via the digit basis

RJW (TeX 2654–2670) introduce the norm operator `𝒩` on `ℤ_p⟦T⟧` as the relative
norm `N_{B/A}` for the degree-`p` extension of rings `A = φ(ℤ_p⟦T⟧) ⊆ ℤ_p⟦T⟧ = B`,
where `φ : G(T) ↦ G((1+T)^p − 1)` is the Frobenius substitution. Concretely
(TeX 2658, "B is free of rank p over A, obtained by adjoining a p-th root of
`(1+T)^p`") the ring `B` is free of rank `p` over the subring `A = φ(B)`, with
basis `1, (1+T), …, (1+T)^{p−1}`: this is exactly the **digit decomposition**
`F = Σ_{i<p} (1+T)^i · φ(F_i)` proven (over `integerRing K`) in
`PadicLFunctions.MeasureR.FormalPsi` (`existsUnique_digits`). We realise the
free `A`-module structure as `Module.compHom` along the φ-ring-hom `phiHom`
(carried by the type synonym `PhiAlg` so the `φ`-module structure does NOT leak
onto `PowerSeries ℤ_[p]`), and set `𝒩 := Algebra.norm` of that free rank-`p`
algebra.

**Replan R10.4** (`.mathlib-quality/decomposition.md`): RJW also give the
product formula `φ(𝒩f) = ∏_{ξ ∈ μ_p} f((1+T)ξ − 1)` (TeX 2666). This is NOT
realisable as a *formal* power-series identity: the substitution
`T ↦ (1+T)ξ − 1` has constant term `ξ − 1`, which is a non-nilpotent unit for
`ξ ≠ 1` (the same `Eqphipsi` obstruction recorded for `psiSeries` in FormalPsi).
So we expose only the determinant characterisation `normOp_eq_det` here; the
evaluated product form (over the tower fields, where `(1+T)ξ − 1` becomes
topologically nilpotent) is the commuting square of ticket T907 (Theorem.lean).

The compactness layer (TeX 2784, "such a subsequence exists, as `ℤ_p⟦T⟧^×` is
compact"; replan R10.6) lives in the final section: `ℤ_p⟦T⟧` is compact and
sequentially compact for the coefficientwise (Pi) topology, the units form a
closed subset, and coefficients are continuous — the inputs for the diagonal
extraction in Coleman's theorem (T910).

Tickets: T906 (norm operator) + T909 (compactness); decomposition R10.4/R10.6.
-/

open PowerSeries

namespace PadicLFunctions

namespace Coleman

variable (p : ℕ) [hp : Fact p.Prime]

/-! ## The digit decomposition over `ℤ_[p]`

`FormalPsi.existsUnique_digits` is stated over `integerRing K` for a
nonarchimedean field `K`. Instantiating `K := ℚ_[p]`, the ring `integerRing ℚ_[p]`
(the norm-unit ball of `ℚ_[p]`) is `ℤ_[p]` repackaged — `PadicInt` IS the ball
subtype `{x : ℚ_[p] // ‖x‖ ≤ 1}`. We transport the decomposition along the
resulting ring isomorphism. -/

/-- The ring isomorphism `ℤ_[p] ≃+* integerRing ℚ_[p]`: both are the norm-unit
ball `{x : ℚ_[p] // ‖x‖ ≤ 1}`, so the algebra map `ℤ_[p] → integerRing ℚ_[p]`
(`Coefficients.lean`) is the identity repackaging and is bijective. -/
noncomputable def padicIntEquivIntegerRing : ℤ_[p] ≃+* integerRing ℚ_[p] :=
  RingEquiv.ofBijective (algebraMap ℤ_[p] (integerRing ℚ_[p]))
    ⟨fun x y hxy =>
        PadicInt.ext (by
          have : ((algebraMap ℤ_[p] (integerRing ℚ_[p]) x : integerRing ℚ_[p]) : ℚ_[p])
              = ((algebraMap ℤ_[p] (integerRing ℚ_[p]) y : integerRing ℚ_[p]) : ℚ_[p]) := by
            rw [hxy]
          exact this),
      fun y => ⟨⟨(y : ℚ_[p]), y.2⟩, Subtype.ext rfl⟩⟩

/-- The digit decomposition over `ℤ_[p]` itself: every `F ∈ ℤ_p⟦T⟧` is uniquely
`Σ_{i<p} (1+T)^i · φ(G_i)`. Transported from `FormalPsi.existsUnique_digits`
(over `integerRing ℚ_[p]`) along `PowerSeries.map padicIntEquivIntegerRing`. -/
theorem existsUnique_digits_padicInt (F : PowerSeries ℤ_[p]) :
    ∃! G : Fin p → PowerSeries ℤ_[p], IsDigitDecomp p F G := by
  set e := padicIntEquivIntegerRing p with he
  -- the forward and backward coefficient maps
  set me : PowerSeries ℤ_[p] →+* PowerSeries (integerRing ℚ_[p]) :=
    PowerSeries.map (e : ℤ_[p] →+* integerRing ℚ_[p]) with hme
  set me' : PowerSeries (integerRing ℚ_[p]) →+* PowerSeries ℤ_[p] :=
    PowerSeries.map (e.symm : integerRing ℚ_[p] →+* ℤ_[p]) with hme'
  have hround : ∀ G : PowerSeries ℤ_[p], me' (me G) = G := fun G =>
    PowerSeries.ext fun n => by
      rw [hme', hme, PowerSeries.coeff_map, PowerSeries.coeff_map]
      exact RingEquiv.symm_apply_apply e _
  obtain ⟨G, hG, hGuniq⟩ := existsUnique_digits p ℚ_[p] (me F)
  refine ⟨fun i => me' (G i), ?_, ?_⟩
  · have := isDigitDecomp_map p (e.symm : integerRing ℚ_[p] →+* ℤ_[p]) hG
    rwa [hround] at this
  · intro H hH
    have hmapH : IsDigitDecomp p (me F) (fun i => me (H i)) := by
      have := isDigitDecomp_map p (e : ℤ_[p] →+* integerRing ℚ_[p]) hH
      simpa [hme] using this
    have := hGuniq (fun i => me (H i)) hmapH
    funext i
    rw [show H i = me' (me (H i)) from (hround (H i)).symm, ← congrFun this i]

/-! ### The formal `ψ` over `ℤ_[p]`

`FormalPsi.psiSeries` (the `0`-th digit) is junk-totalised over a general
`CommRing`, computing honestly exactly where the digit decomposition is unique.
Over `ℤ_[p]` that locus is everything (`existsUnique_digits_padicInt`), so the
`ψ`-linearity facts (`psiSeries_phi`, `psiSeries_add`, `psiSeries_C_mul`) — proven
over `integerRing K` in FormalPsi — transport verbatim. These let `ψ` cancel the
`p^k` in `phi_injective_mod` (part (i)). -/

variable {p}

/-- Over `ℤ_[p]`, `ψ` is the `0`-th digit of any digit decomposition. -/
theorem psiSeries_eq_of_isDigitDecomp_padicInt {F : PowerSeries ℤ_[p]}
    {G : Fin p → PowerSeries ℤ_[p]} (hG : IsDigitDecomp p F G) :
    psiSeries p F = G 0 :=
  psiSeries_eq_of_unique p (existsUnique_digits_padicInt p F) hG

/-- `ψ ∘ φ = id` over `ℤ_[p]`: the digit family of `φ(G)` is `(G, 0, …, 0)`,
so its `0`-th digit is `G`. (FormalPsi `psiSeries_phi`, transported.) -/
theorem psiSeries_phi_padicInt (G : PowerSeries ℤ_[p]) :
    psiSeries p (phiSeries p G) = G := by
  refine psiSeries_eq_of_isDigitDecomp_padicInt (G := fun i => if i = 0 then G else 0) ?_
  change phiSeries p G = ∑ i : Fin p, (1 + PowerSeries.X) ^ (i : ℕ)
      * phiSeries p (if i = 0 then G else 0)
  rw [Finset.sum_eq_single (0 : Fin p)]
  · simp
  · intro i _ hi0
    rw [if_neg hi0, phiSeries_zero, mul_zero]
  · intro h; exact absurd (Finset.mem_univ (0 : Fin p)) h

/-- `ψ` is additive over `ℤ_[p]`. (FormalPsi `psiSeries_add`, transported.) -/
theorem psiSeries_add_padicInt (F G : PowerSeries ℤ_[p]) :
    psiSeries p (F + G) = psiSeries p F + psiSeries p G := by
  obtain ⟨GF, hGF, -⟩ := existsUnique_digits_padicInt p F
  obtain ⟨GG, hGG, -⟩ := existsUnique_digits_padicInt p G
  rw [psiSeries_eq_of_isDigitDecomp_padicInt hGF, psiSeries_eq_of_isDigitDecomp_padicInt hGG]
  refine psiSeries_eq_of_isDigitDecomp_padicInt (G := fun i => GF i + GG i) ?_
  change F + G = ∑ i : Fin p, (1 + PowerSeries.X) ^ (i : ℕ) * phiSeries p (GF i + GG i)
  rw [hGF, hGG, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [phiSeries, phiSeries, phiSeries,
    PowerSeries.subst_add (hasSubst_one_add_X_pow_sub_one p), mul_add]

/-- `ψ(C a · F) = C a · ψ(F)` over `ℤ_[p]`. (FormalPsi `psiSeries_C_mul`,
transported — the form `phi_injective_mod` uses to pull `C(p^k)` through `ψ`.) -/
theorem psiSeries_C_mul_padicInt (a : ℤ_[p]) (F : PowerSeries ℤ_[p]) :
    psiSeries p (PowerSeries.C a * F) = PowerSeries.C a * psiSeries p F := by
  obtain ⟨GF, hGF, -⟩ := existsUnique_digits_padicInt p F
  rw [psiSeries_eq_of_isDigitDecomp_padicInt hGF]
  refine psiSeries_eq_of_isDigitDecomp_padicInt (G := fun i => PowerSeries.C a * GF i) ?_
  change PowerSeries.C a * F = ∑ i : Fin p, (1 + PowerSeries.X) ^ (i : ℕ)
      * phiSeries p (PowerSeries.C a * GF i)
  rw [hGF, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [phiSeries, phiSeries,
    PowerSeries.subst_mul (hasSubst_one_add_X_pow_sub_one p),
    show ((PowerSeries.C a).subst ((1 + PowerSeries.X) ^ p - 1)
        : PowerSeries ℤ_[p]) = PowerSeries.C a from PowerSeries.subst_C a]
  ring

variable (p)

/-! ## The φ-algebra and the digit basis

The norm operator is `Algebra.norm` for the φ-algebra structure on `ℤ_p⟦T⟧`:
the ring `B = ℤ_p⟦T⟧` viewed as an algebra over the subring `A = φ(B)` via the
Frobenius `φ`. We carry this structure on a type synonym `PhiAlg` so the
`φ`-`Algebra` instance does NOT leak onto `PowerSeries ℤ_[p]` (which already has
its standard `ℤ_[p]⟦T⟧`-algebra structure). The free `A`-basis `1, …, (1+T)^{p−1}`
is the digit decomposition `existsUnique_digits_padicInt`. -/

/-- The Frobenius substitution `φ : F ↦ F((1+T)^p − 1)` as a ring homomorphism
(`FormalPsi.phiSeries` packaged via `substAlgHom.toRingHom`). -/
noncomputable def phiHom : PowerSeries ℤ_[p] →+* PowerSeries ℤ_[p] :=
  (PowerSeries.substAlgHom (hasSubst_one_add_X_pow_sub_one (R := ℤ_[p]) p)).toRingHom

@[simp]
theorem phiHom_apply (F : PowerSeries ℤ_[p]) : phiHom p F = phiSeries p F := by
  change (PowerSeries.substAlgHom (hasSubst_one_add_X_pow_sub_one (R := ℤ_[p]) p)) F
      = phiSeries p F
  rw [phiSeries, PowerSeries.coe_substAlgHom]

/-- The type synonym carrying the `φ`-`A`-module/algebra structure on `ℤ_p⟦T⟧`.
`PhiAlg p` is `PowerSeries ℤ_[p]` as a module over `A = φ(ℤ_p⟦T⟧)`; the algebra
map `ℤ_p⟦T⟧ → PhiAlg p` is `φ` (so the structure stays off the bare
`PowerSeries ℤ_[p]`). -/
def PhiAlg : Type := PowerSeries ℤ_[p]

namespace PhiAlg

noncomputable instance : CommRing (PhiAlg p) :=
  inferInstanceAs (CommRing (PowerSeries ℤ_[p]))

/-- The `φ`-algebra structure: `ℤ_p⟦T⟧` acts on `PhiAlg p` through `φ`. -/
noncomputable instance : Algebra (PowerSeries ℤ_[p]) (PhiAlg p) :=
  RingHom.toAlgebra (phiHom p)

/-- The identity repackaging `PhiAlg p ≃+* PowerSeries ℤ_[p]` (same carrier and
`CommRing`); used to move between the module language and `IsDigitDecomp`. -/
noncomputable def toPS : PhiAlg p ≃+* PowerSeries ℤ_[p] := RingEquiv.refl _

variable {p}

@[simp]
theorem toPS_apply (x : PhiAlg p) : toPS p x = x := rfl

@[simp]
theorem toPS_symm_apply (F : PowerSeries ℤ_[p]) : (toPS p).symm F = F := rfl

/-- The image of the `φ`-algebra map: `toPS (algebraMap c) = φ(c)`. -/
theorem toPS_algebraMap (c : PowerSeries ℤ_[p]) :
    toPS p (algebraMap (PowerSeries ℤ_[p]) (PhiAlg p) c) = phiSeries p c := by
  rw [RingHom.algebraMap_toAlgebra]
  exact phiHom_apply p c

/-- The `φ`-`smul` on `PhiAlg p` is multiplication by the `φ`-image. -/
theorem smul_def (c : PowerSeries ℤ_[p]) (x : PhiAlg p) :
    toPS p (c • x) = phiSeries p c * toPS p x := by
  rw [Algebra.smul_def, map_mul, toPS_algebraMap]

end PhiAlg

variable {p}

/-- The `φ`-`A`-linear combination `∑ c i • (1+T)^i` in `PhiAlg p` is exactly the
digit expression `∑ (1+T)^i · φ(c i)`: this bridges the module language of
`Module.Basis.mk` and the predicate `IsDigitDecomp`. -/
theorem sum_smul_one_add_X_pow_eq (c : Fin p → PowerSeries ℤ_[p]) :
    PhiAlg.toPS p (∑ i : Fin p, c i • ((1 + PowerSeries.X) ^ (i : ℕ) : PhiAlg p))
      = ∑ i : Fin p, (1 + PowerSeries.X) ^ (i : ℕ) * phiSeries p (c i) := by
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [PhiAlg.smul_def, PhiAlg.toPS_apply]
  exact mul_comm _ _

variable (p)

/-- W6b/T906: the digit basis `1, (1+T), …, (1+T)^{p−1}` of `ℤ_p⟦T⟧` as a free
module of rank `p` over `A = φ(ℤ_p⟦T⟧)` (`PhiAlg p`). Spanning is the existence
half of `existsUnique_digits_padicInt`, linear independence is its uniqueness
half. (RJW TeX 2658: "`B` is free of rank `p` over `A`, obtained by adjoining a
`p`-th root of `(1+T)^p`".) -/
noncomputable def digitBasis : Module.Basis (Fin p) (PowerSeries ℤ_[p]) (PhiAlg p) :=
  Module.Basis.mk
    (v := fun i => ((1 + PowerSeries.X) ^ (i : ℕ) : PhiAlg p))
    (-- linear independence ← uniqueness of digits
      Fintype.linearIndependent_iffₛ.2 fun f g hfg i => by
        have hf : IsDigitDecomp p
            (PhiAlg.toPS p (∑ j : Fin p, f j • ((1 + PowerSeries.X) ^ (j : ℕ) : PhiAlg p)))
            f := sum_smul_one_add_X_pow_eq f
        have hg : IsDigitDecomp p
            (PhiAlg.toPS p (∑ j : Fin p, g j • ((1 + PowerSeries.X) ^ (j : ℕ) : PhiAlg p)))
            g := sum_smul_one_add_X_pow_eq g
        rw [hfg] at hf
        exact congrFun ((existsUnique_digits_padicInt p _).unique hf hg) i)
    (-- spanning ← existence of digits
      (Submodule.top_le_span_range_iff_forall_exists_fun (PowerSeries ℤ_[p])).2 fun x => by
        obtain ⟨G, hG, -⟩ := existsUnique_digits_padicInt p (PhiAlg.toPS p x)
        refine ⟨G, (PhiAlg.toPS p).injective ?_⟩
        rw [sum_smul_one_add_X_pow_eq G, PhiAlg.toPS_apply]
        exact hG.symm)

@[simp]
theorem digitBasis_apply (i : Fin p) :
    digitBasis p i = ((1 + PowerSeries.X) ^ (i : ℕ) : PhiAlg p) :=
  Module.Basis.mk_apply _ _ i

/-- `PhiAlg p` is a free module over `A = φ(ℤ_p⟦T⟧)` (witnessed by `digitBasis`). -/
instance : Module.Free (PowerSeries ℤ_[p]) (PhiAlg p) :=
  Module.Free.of_basis (digitBasis p)

/-- `PhiAlg p` is module-finite (rank `p`) over `A = φ(ℤ_p⟦T⟧)`. -/
instance : Module.Finite (PowerSeries ℤ_[p]) (PhiAlg p) :=
  Module.Finite.of_basis (digitBasis p)

/-! ## The norm operator `𝒩` -/

variable {p}

/-- W6b/T906: the norm operator `𝒩 : ℤ_p⟦T⟧ → ℤ_p⟦T⟧`, defined as the relative
norm `N_{B/A}` of the free rank-`p` φ-algebra `B = ℤ_p⟦T⟧` over `A = φ(ℤ_p⟦T⟧)`
(`Algebra.norm` along `PhiAlg`). RJW TeX 2654–2660.

The norm lands in the base ring `A`, which (under the φ-iso `A ≅ ℤ_p⟦T⟧`) we
identify with `ℤ_p⟦T⟧`: no `φ⁻¹` is needed here — the source's `φ⁻¹` is an
artifact of viewing `A` as a subring of `B`, whereas `Algebra.norm` already
takes values in the abstract base. -/
noncomputable def normOp (f : PowerSeries ℤ_[p]) : PowerSeries ℤ_[p] :=
  Algebra.norm (PowerSeries ℤ_[p]) ((PhiAlg.toPS p).symm f)

/-- `𝒩` is multiplicative (the relative norm is a monoid hom). RJW TeX 2660. -/
theorem normOp_mul (f g : PowerSeries ℤ_[p]) :
    normOp (f * g) = normOp f * normOp g := by
  simp only [normOp, map_mul]

/-- `𝒩 1 = 1`. -/
@[simp]
theorem normOp_one : normOp (1 : PowerSeries ℤ_[p]) = 1 := by
  unfold normOp; rw [map_one, map_one]

/-- `𝒩` sends units to units (the norm of a unit is a unit). RJW TeX 2660. -/
theorem normOp_isUnit {f : PowerSeries ℤ_[p]} (hf : IsUnit f) : IsUnit (normOp f) :=
  (hf.map (PhiAlg.toPS p).symm).map (Algebra.norm (PowerSeries ℤ_[p]))

/-- The matrix of multiplication-by-`f` in the digit basis (entries in `A`,
identified with `ℤ_p⟦T⟧`). Its determinant is `𝒩f` (`normOp_eq_det`); this is
the determinant characterisation that the evaluation/norm commuting square
(T907) transports through `evalPi`. -/
noncomputable def digitMatrix (f : PowerSeries ℤ_[p]) :
    Matrix (Fin p) (Fin p) (PowerSeries ℤ_[p]) :=
  Algebra.leftMulMatrix (digitBasis p) ((PhiAlg.toPS p).symm f)

/-- W6b/T906 (the determinant characterisation, replan R10.4): `𝒩f` is the
determinant of the multiplication-by-`f` matrix in the digit basis. (The
`μ_p`-product formula `φ(𝒩f) = ∏_ξ f((1+T)ξ−1)` is NOT a formal identity — the
substitution `(1+T)ξ−1` has non-nilpotent constant term for `ξ ≠ 1`; the
evaluated form is the commuting square of T907.) -/
theorem normOp_eq_det (f : PowerSeries ℤ_[p]) :
    normOp f = Matrix.det (digitMatrix f) := by
  unfold normOp digitMatrix
  rw [Algebra.norm_eq_matrix_det (digitBasis p)]

/-! ## Congruence mod `p^k` of power series (T908)

RJW's continuity lemmas (TeX 2726–2756; cf. CS06 Lem 2.3.1) are stated as
congruences `f ≡ g mod p^k` of power series in `ℤ_p⟦T⟧`. We make the idiom
precise as coefficientwise `p^k`-divisibility (`ModEqPow`), give it the basic
equivalence-relation + ring-compatible API, and record the equivalent
`C`-factor form `f − g = C(p^k)·h` (the form that lets `ψ` cancel `p^k` in
part (i)). Replan R10.5. -/

variable (p)

/-- T908: `f ≡ g mod p^k` for power series over `ℤ_[p]` — every coefficient of
`f − g` is divisible by `p^k`. (RJW writes `f ≡ g (mod p^k)`, TeX 2729–2736.) -/
def ModEqPow (k : ℕ) (f g : PowerSeries ℤ_[p]) : Prop :=
  ∀ m, (p : ℤ_[p]) ^ k ∣ PowerSeries.coeff m (f - g)

variable {p}

@[refl]
theorem ModEqPow.refl (k : ℕ) (f : PowerSeries ℤ_[p]) : ModEqPow p k f f := fun m => by
  rw [sub_self, map_zero]; exact dvd_zero _

theorem ModEqPow.symm {k : ℕ} {f g : PowerSeries ℤ_[p]} (h : ModEqPow p k f g) :
    ModEqPow p k g f := fun m => by
  rw [show g - f = -(f - g) from (neg_sub f g).symm, map_neg]; exact (h m).neg_right

theorem ModEqPow.trans {k : ℕ} {f g h : PowerSeries ℤ_[p]} (hfg : ModEqPow p k f g)
    (hgh : ModEqPow p k g h) : ModEqPow p k f h := fun m => by
  rw [show f - h = (f - g) + (g - h) from by ring, map_add]
  exact dvd_add (hfg m) (hgh m)

/-- The `C`-factor form: `f ≡ g mod p^k` iff `f − g = C(p^k)·h` for some `h`.
This is the form RJW's `mod p^k` congruence takes when `ψ`-linearity must
cancel the `p^k` (part (i)). -/
theorem modEqPow_iff_exists_C_mul {k : ℕ} {f g : PowerSeries ℤ_[p]} :
    ModEqPow p k f g ↔ ∃ h, f - g = PowerSeries.C ((p : ℤ_[p]) ^ k) * h := by
  constructor
  · intro hfg
    -- build the quotient series coefficientwise
    choose c hc using hfg
    refine ⟨PowerSeries.mk c, PowerSeries.ext fun m => ?_⟩
    rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_mk, hc m]
  · rintro ⟨h, hh⟩ m
    rw [hh, PowerSeries.coeff_C_mul]
    exact Dvd.intro _ rfl

/-- `ModEqPow` is preserved under multiplication on the right by a common
factor (the multiplicative compatibility, half of the congruence ring API). -/
theorem ModEqPow.mul_right {k : ℕ} {f g : PowerSeries ℤ_[p]} (h : ModEqPow p k f g)
    (c : PowerSeries ℤ_[p]) : ModEqPow p k (f * c) (g * c) := by
  obtain ⟨q, hq⟩ := modEqPow_iff_exists_C_mul.1 h
  exact modEqPow_iff_exists_C_mul.2 ⟨q * c, by rw [← sub_mul, hq, mul_assoc]⟩

/-- Multiplicative compatibility: `f₁ ≡ g₁` and `f₂ ≡ g₂` give `f₁f₂ ≡ g₁g₂`. -/
theorem ModEqPow.mul {k : ℕ} {f₁ g₁ f₂ g₂ : PowerSeries ℤ_[p]}
    (h₁ : ModEqPow p k f₁ g₁) (h₂ : ModEqPow p k f₂ g₂) :
    ModEqPow p k (f₁ * f₂) (g₁ * g₂) := by
  refine (h₁.mul_right f₂).trans ?_
  rw [mul_comm g₁ f₂, mul_comm g₁ g₂]
  exact h₂.mul_right g₁

/-- Powers respect `ModEqPow`: `f ≡ g mod p^k` gives `f^n ≡ g^n mod p^k`. -/
theorem ModEqPow.pow {k : ℕ} {f g : PowerSeries ℤ_[p]} (h : ModEqPow p k f g) :
    ∀ n, ModEqPow p k (f ^ n) (g ^ n)
  | 0 => by simpa using ModEqPow.refl k (1 : PowerSeries ℤ_[p])
  | n + 1 => by rw [pow_succ, pow_succ]; exact (h.pow n).mul h

/-! ## The continuity lemmas (T908, RJW TeX 2726–2756)

RJW's `lem:norm continuity`. Parts (i)/(ii) are "left as an exercise
(cf. CS06 Lem 2.3.1)"; we expand them per the source-gap rule (replan R10.5).
Part (i) uses that `ψ ∘ φ = id` and `ψ` is `ℤ_[p]`-linear: a congruence
`φf ≡ 1 mod p^k` is `φ(f − 1) = C(p^k)·h`, and applying `ψ` cancels — `ψ` carries
`C(p^k)` straight through (`psiSeries_C_mul_padicInt`) and undoes `φ`. -/

/-- `phiSeries` is a ring hom over `ℤ_[p]` (it is `phiHom`), so it fixes `1` and
respects subtraction. -/
theorem phiSeries_sub (f g : PowerSeries ℤ_[p]) :
    phiSeries p (f - g) = phiSeries p f - phiSeries p g := by
  rw [← phiHom_apply, ← phiHom_apply, ← phiHom_apply, map_sub]

theorem phiSeries_one_padicInt : phiSeries p (1 : PowerSeries ℤ_[p]) = 1 := by
  rw [← phiHom_apply, map_one]

/-- T908 (i), RJW TeX 2729: if `φ(f) ≡ 1 mod p^k` then `f ≡ 1 mod p^k`. The
Frobenius `φ` is coefficientwise-injective mod `p^k`. Route: the retraction
`ψ ∘ φ = id` is `ℤ_[p]`-linear, so it cancels the `C(p^k)` factor
(`psiSeries_phi_padicInt` + `psiSeries_C_mul_padicInt`; CS06 Lem 2.3.1). -/
theorem phi_injective_mod {k : ℕ} {f : PowerSeries ℤ_[p]}
    (h : ModEqPow p k (phiSeries p f) 1) : ModEqPow p k f 1 := by
  obtain ⟨q, hq⟩ := modEqPow_iff_exists_C_mul.1 h
  -- `φ(f − 1) = φf − 1 = C(p^k)·q`; apply `ψ`
  have hφ : phiSeries p (f - 1) = PowerSeries.C ((p : ℤ_[p]) ^ k) * q := by
    rw [phiSeries_sub, phiSeries_one_padicInt, hq]
  refine modEqPow_iff_exists_C_mul.2 ⟨psiSeries p q, ?_⟩
  have := congrArg (psiSeries p) hφ
  rwa [psiSeries_phi_padicInt, psiSeries_C_mul_padicInt] at this

/-! ## `𝒩` modulo powers of `p` (T908 (ii)/(iii)/(iv), RJW TeX 2730–2756)

Parts (iii)/(iv) via the determinant characterisation `normOp_eq_det`: `digitMatrix`
is a ring hom, so a unit congruence `f = 1 + C(p^k)·h` gives
`digitMatrix f = 1 + C(p^k) • digitMatrix h`, and the Taylor expansion
`det (1 + r • M) = 1 + (trace M)·r + (…)·r²` (`Matrix.det_one_add_smul`) plus
`p ∣ trace (digitMatrix h)` (the trace identity `Tr = p·φ∘ψ`, RJW TeX 2670) lands
`𝒩 f ≡ 1 mod p^{k+1}`. Part (iv) iterates (iii) `k₁` times on the unit
`𝒩^{k₂−k₁}f·f⁻¹ ≡ 1 mod p` (from (ii)). -/

/-- `digitMatrix` is additive (it is `leftMulMatrix ∘ (toPS).symm`, both additive). -/
theorem digitMatrix_add (f g : PowerSeries ℤ_[p]) :
    digitMatrix (f + g) = digitMatrix f + digitMatrix g := by
  simp only [digitMatrix, map_add]

/-- `digitMatrix` is multiplicative. -/
theorem digitMatrix_mul (f g : PowerSeries ℤ_[p]) :
    digitMatrix (f * g) = digitMatrix f * digitMatrix g := by
  simp only [digitMatrix, map_mul]

/-- `digitMatrix 1 = 1`. -/
@[simp]
theorem digitMatrix_one : digitMatrix (1 : PowerSeries ℤ_[p]) = 1 := by
  unfold digitMatrix; rw [map_one, map_one]

/-- `digitMatrix (C a) = C a • 1` (the scalar matrix): `C a = φ(C a) = algebraMap (C a)`
in `PhiAlg` (φ fixes constants), so `leftMulMatrix` sends it to the scalar
(`AlgHom.commutes`). -/
theorem digitMatrix_C (a : ℤ_[p]) :
    digitMatrix (PowerSeries.C a) = PowerSeries.C a • (1 : Matrix (Fin p) (Fin p)
      (PowerSeries ℤ_[p])) := by
  have hCalg : (PhiAlg.toPS p).symm (PowerSeries.C a)
      = algebraMap (PowerSeries ℤ_[p]) (PhiAlg p) (PowerSeries.C a) := by
    apply (PhiAlg.toPS p).injective
    rw [PhiAlg.toPS_algebraMap, RingEquiv.apply_symm_apply,
      show phiSeries p (PowerSeries.C a) = PowerSeries.C a from by
        rw [phiSeries]; exact PowerSeries.subst_C a]
  unfold digitMatrix
  rw [hCalg, AlgHom.commutes, Algebra.algebraMap_eq_smul_one]

/-- `φ((1+T)^q) = ((1+T)^p)^q`: `φ(1+T) = 1 + ((1+T)^p − 1) = (1+T)^p`, raised to `q`. -/
theorem phiSeries_one_add_X_pow (q : ℕ) :
    phiSeries p ((1 + PowerSeries.X) ^ q : PowerSeries ℤ_[p])
      = ((1 + PowerSeries.X) ^ p) ^ q := by
  have hX : phiHom p (1 + PowerSeries.X) = (1 + PowerSeries.X) ^ p := by
    rw [map_add, map_one]
    have : phiHom p PowerSeries.X = (1 + PowerSeries.X) ^ p - 1 := by
      rw [phiHom_apply, phiSeries, PowerSeries.subst_X (hasSubst_one_add_X_pow_sub_one p)]
    rw [this]; ring
  rw [← phiHom_apply, map_pow, hX]

/-- The digit decomposition of `(1+T)^m`: writing `m = p·(m/p) + m%p`,
`(1+T)^m = (1+T)^{m%p}·φ((1+T)^{m/p})`, so the digit family is `(1+T)^{m/p}` in slot
`m%p` and `0` elsewhere. (The key combinatorial input to the trace computation.) -/
theorem isDigitDecomp_one_add_X_pow (m : ℕ) :
    IsDigitDecomp p ((1 + PowerSeries.X) ^ m : PowerSeries ℤ_[p])
      (fun i => if (i : ℕ) = m % p then (1 + PowerSeries.X) ^ (m / p) else 0) := by
  rw [IsDigitDecomp, Finset.sum_eq_single (⟨m % p, Nat.mod_lt _ hp.out.pos⟩ : Fin p)]
  · rw [if_pos rfl, phiSeries_one_add_X_pow, ← pow_mul, ← pow_add]
    congr 1
    rw [Fin.val_mk]
    exact (Nat.mod_add_div m p).symm
  · intro i _ hine
    rw [if_neg (by simpa using fun h => hine (Fin.ext (by simpa using h))), phiSeries_zero,
      mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- The basis `repr` is the digit family: `(digitBasis).repr x i` is the `i`-th digit
of `toPS x` (the repr coordinates form a digit decomposition, `existsUnique`). -/
theorem digitBasis_repr_eq (x : PhiAlg p) (G : Fin p → PowerSeries ℤ_[p])
    (hG : IsDigitDecomp p (PhiAlg.toPS p x) G) (i : Fin p) :
    (digitBasis p).repr x i = G i := by
  have hrepr : IsDigitDecomp p (PhiAlg.toPS p x) (fun i => (digitBasis p).repr x i) := by
    rw [IsDigitDecomp, ← sum_smul_one_add_X_pow_eq (fun i => (digitBasis p).repr x i)]
    conv_lhs => rw [← (digitBasis p).sum_repr x]
    exact congrArg (PhiAlg.toPS p) (Finset.sum_congr rfl
      (fun i _ => by rw [digitBasis_apply]))
  exact congrFun ((existsUnique_digits_padicInt p _).unique hrepr hG) i

/-- The `Algebra.trace` of the digit-basis element `(1+T)^l` is `p` if `l = 0` else `0`:
multiplication by `(1+T)^l` sends `(1+T)^j ↦ (1+T)^{l+j}`, whose `j`-th digit (the
diagonal entry) is nonzero only when `l ≡ 0 mod p`, i.e. `l = 0` (then it is `1`),
giving trace `Σ_j 1 = p`; for `1 ≤ l < p` the diagonal vanishes. -/
theorem trace_digitBasis (l : Fin p) :
    Algebra.trace (PowerSeries ℤ_[p]) (PhiAlg p) (digitBasis p l)
      = if (l : ℕ) = 0 then (p : PowerSeries ℤ_[p]) else 0 := by
  rw [Algebra.trace_eq_matrix_trace (digitBasis p), Matrix.trace]
  -- diagonal entry at `j`: the `j`-th digit of `(1+T)^{l+j}`
  have hdiag : ∀ j : Fin p, Matrix.diag (Algebra.leftMulMatrix (digitBasis p)
      (digitBasis p l)) j
      = if (l : ℕ) = 0 then (1 : PowerSeries ℤ_[p]) else 0 := by
    intro j
    rw [Matrix.diag_apply, Algebra.leftMulMatrix_eq_repr_mul]
    have hmulb : (digitBasis p l * digitBasis p j : PhiAlg p)
        = (1 + PowerSeries.X) ^ ((l : ℕ) + (j : ℕ)) := by
      rw [digitBasis_apply, digitBasis_apply, ← pow_add]
    have htoPS : PhiAlg.toPS p (digitBasis p l * digitBasis p j)
        = ((1 + PowerSeries.X) ^ ((l : ℕ) + (j : ℕ)) : PowerSeries ℤ_[p]) := by
      rw [hmulb]; rfl
    rw [digitBasis_repr_eq (digitBasis p l * digitBasis p j)
      (fun i => if (i : ℕ) = ((l : ℕ) + (j : ℕ)) % p then
        (1 + PowerSeries.X) ^ (((l : ℕ) + (j : ℕ)) / p) else 0)
      (by rw [htoPS]; exact isDigitDecomp_one_add_X_pow (p := p) ((l : ℕ) + (j : ℕ))) j]
    -- the `j`-th digit: nonzero iff `j = (l+j) % p`, i.e. `l = 0`
    by_cases hl0 : (l : ℕ) = 0
    · rw [if_pos hl0, if_pos (by rw [hl0, zero_add, Nat.mod_eq_of_lt j.2]),
        hl0, zero_add, Nat.div_eq_of_lt j.2, pow_zero]
    · rw [if_neg hl0, if_neg ?_]
      -- `j = (l+j) % p` with `j < p`, `0 < l < p` is impossible
      intro hj
      have hllt := l.2
      have hlpos : 0 < (l : ℕ) := Nat.pos_of_ne_zero hl0
      have hdm := Nat.div_add_mod ((l : ℕ) + (j : ℕ)) p
      rw [← hj] at hdm
      have hdvd : p ∣ (l : ℕ) := ⟨((l : ℕ) + (j : ℕ)) / p, by omega⟩
      exact absurd (Nat.le_of_dvd hlpos hdvd) (by omega)
  rw [Finset.sum_congr rfl (fun j _ => hdiag j)]
  by_cases hl0 : (l : ℕ) = 0
  · simp only [if_pos hl0, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      mul_one]
  · simp only [if_neg hl0, Finset.sum_const_zero]

/-- **The trace identity** (RJW TeX 2670, `ψ = p⁻¹·φ⁻¹∘Tr`, abstract-base form
`Algebra.trace = p·ψ`): `Matrix.trace (digitMatrix h) = p·ψ(h)`. Expand `h` in the
digit basis `h = Σ_l ψ_l·(1+T)^l` (module form), use linearity of the trace and
`trace_digitBasis` (only the `l = 0` term survives, contributing `p·ψ_0 = p·ψ(h)`). -/
theorem trace_digitMatrix (h : PowerSeries ℤ_[p]) :
    Matrix.trace (digitMatrix h) = (p : PowerSeries ℤ_[p]) * psiSeries p h := by
  rw [digitMatrix, ← Algebra.trace_eq_matrix_trace (digitBasis p) ((PhiAlg.toPS p).symm h)]
  -- expand in the basis and use linearity
  conv_lhs => rw [← (digitBasis p).sum_repr ((PhiAlg.toPS p).symm h), map_sum]
  rw [Finset.sum_congr rfl (fun l _ => by
    rw [LinearMap.map_smul, trace_digitBasis l])]
  -- only `l = 0` survives
  rw [Finset.sum_eq_single (0 : Fin p)]
  · rw [Fin.val_zero, if_pos rfl, smul_eq_mul, mul_comm]
    congr 1
    -- `repr_0 = ψ h`
    obtain ⟨G, hG, -⟩ := existsUnique_digits_padicInt p h
    rw [psiSeries_eq_of_isDigitDecomp_padicInt hG,
      digitBasis_repr_eq ((PhiAlg.toPS p).symm h) G (by rwa [RingEquiv.apply_symm_apply])]
  · intro l _ hl0
    rw [if_neg (by simpa using fun h => hl0 (Fin.ext (by simpa using h))), smul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

/-! ### The mod-`p` reduction and the Frobenius identity (for part (ii)) -/

/-- `f ≡ g mod p` iff their reductions agree over `ZMod p` (`PadicInt.toZMod` has
kernel `(p)`, so `p ∣ x ↔ toZMod x = 0`). -/
theorem modEqPow_one_iff_map_toZMod {f g : PowerSeries ℤ_[p]} :
    ModEqPow p 1 f g ↔
      PowerSeries.map (PadicInt.toZMod : ℤ_[p] →+* ZMod p) f
        = PowerSeries.map (PadicInt.toZMod : ℤ_[p] →+* ZMod p) g := by
  rw [PowerSeries.ext_iff]
  refine forall_congr' (fun m => ?_)
  rw [PowerSeries.coeff_map, PowerSeries.coeff_map, ← sub_eq_zero, ← map_sub,
    ← RingHom.mem_ker, PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p,
    Ideal.mem_span_singleton, pow_one, map_sub]

/-- **The Frobenius identity over `𝔽_p⟦T⟧`** (the engine for part (ii)): `φ(ḡ) = ḡ^p`.
Over char `p`, `(1+T)^p − 1 = T^p` (freshman's dream), so `φ = subst(T^p) = expand`,
and `expand ḡ = ḡ^p` (`MvPowerSeries.map_frobenius_expand` + `frobenius (ZMod p) = id`,
`ZMod.frobenius_zmod`). -/
theorem phiSeries_eq_pow_zmod (g : PowerSeries (ZMod p)) :
    phiSeries p g = g ^ p := by
  haveI : CharP (PowerSeries (ZMod p)) p :=
    charP_of_injective_algebraMap' (ZMod p) p
  -- `(1+T)^p − 1 = T^p` over char `p`
  have hsub : ((1 + PowerSeries.X) ^ p - 1 : PowerSeries (ZMod p)) = PowerSeries.X ^ p := by
    rw [add_pow_char, one_pow, add_sub_cancel_left]
  -- `φ g = subst(X^p) g = expand g`
  have hexp : phiSeries p g = PowerSeries.expand p hp.out.pos.ne' g := by
    rw [phiSeries, hsub, PowerSeries.expand_apply]
  rw [hexp]
  -- `expand g = (expand g).map (frobenius (ZMod p) p) = g^p`
  have hfrob : PowerSeries.map (frobenius (ZMod p) p) (PowerSeries.expand p hp.out.pos.ne' g)
      = g ^ p := MvPowerSeries.map_frobenius_expand p hp.out.pos.ne'
  rwa [ZMod.frobenius_zmod, PowerSeries.map_id] at hfrob

/-- `map toZMod` commutes with `φ` (`φ = subst((1+T)^p−1)`, fixed by coefficient maps,
`map_phiSeries`). -/
theorem map_toZMod_phiSeries (f : PowerSeries ℤ_[p]) :
    PowerSeries.map (PadicInt.toZMod : ℤ_[p] →+* ZMod p) (phiSeries p f)
      = phiSeries p (PowerSeries.map (PadicInt.toZMod : ℤ_[p] →+* ZMod p) f) :=
  map_phiSeries p _ f

/-- **Frobenius identity over `ℤ_[p]`** (reduced form, for part (ii)): `f^p ≡ φ(f) mod p`.
Reduce mod `p`: `(f̄)^p = φ(f̄)` (`phiSeries_eq_pow_zmod`) and `map` commutes with `φ`. -/
theorem pow_p_modEq_phiSeries (f : PowerSeries ℤ_[p]) :
    ModEqPow p 1 (f ^ p) (phiSeries p f) := by
  rw [modEqPow_one_iff_map_toZMod, map_pow, map_toZMod_phiSeries, phiSeries_eq_pow_zmod]

/-- The digit family of `C a · F` is `a ·` the digit family of `F` (`φ` is `ℤ_[p]`-linear
on constants, `phiSeries_C_mul`). -/
theorem isDigitDecomp_C_mul (a : ℤ_[p]) {F : PowerSeries ℤ_[p]} {G : Fin p → PowerSeries ℤ_[p]}
    (hG : IsDigitDecomp p F G) :
    IsDigitDecomp p (PowerSeries.C a * F) (fun i => PowerSeries.C a * G i) := by
  rw [IsDigitDecomp, hG, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [phiSeries_C_mul]; ring

/-- **Digit uniqueness mod `p`**: if `Σ_i (1+T)^i φ(c_i) ≡ Σ_i (1+T)^i φ(d_i) mod p^k`
then `c_i ≡ d_i mod p^k` for each `i`. (The difference is `C(p^k)·R`, whose digits are
`C(p^k)·(digits R)`; combine with the `d`-digits and use `ℤ_[p]`-digit uniqueness.) -/
theorem digit_modEq_of_sum_modEq {k : ℕ} {c d : Fin p → PowerSeries ℤ_[p]}
    (h : ModEqPow p k (∑ i : Fin p, (1 + PowerSeries.X) ^ (i : ℕ) * phiSeries p (c i))
      (∑ i : Fin p, (1 + PowerSeries.X) ^ (i : ℕ) * phiSeries p (d i))) (i : Fin p) :
    ModEqPow p k (c i) (d i) := by
  obtain ⟨R, hR⟩ := modEqPow_iff_exists_C_mul.1 h
  -- digit decomposition of `R`
  obtain ⟨GR, hGR, -⟩ := existsUnique_digits_padicInt p R
  -- `Σ (1+T)^i φ(c_i) = Σ (1+T)^i φ(d_i + C(p^k)·GR_i)`
  have hcomb : IsDigitDecomp p (∑ i : Fin p, (1 + PowerSeries.X) ^ (i : ℕ) * phiSeries p (c i))
      (fun i => d i + PowerSeries.C ((p : ℤ_[p]) ^ k) * GR i) := by
    have hCR : IsDigitDecomp p (PowerSeries.C ((p : ℤ_[p]) ^ k) * R)
        (fun i => PowerSeries.C ((p : ℤ_[p]) ^ k) * GR i) := isDigitDecomp_C_mul _ hGR
    rw [IsDigitDecomp]
    have hsumeq : (∑ i : Fin p, (1 + PowerSeries.X) ^ (i : ℕ) * phiSeries p (c i))
        = (∑ i : Fin p, (1 + PowerSeries.X) ^ (i : ℕ) * phiSeries p (d i))
          + PowerSeries.C ((p : ℤ_[p]) ^ k) * R := sub_eq_iff_eq_add'.mp hR
    rw [hsumeq, hCR, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [show phiSeries p (d i + PowerSeries.C ((p : ℤ_[p]) ^ k) * GR i)
        = phiSeries p (d i) + phiSeries p (PowerSeries.C ((p : ℤ_[p]) ^ k) * GR i) from by
      rw [← phiHom_apply, map_add, phiHom_apply, phiHom_apply], mul_add]
  -- `ℤ_[p]`-digit uniqueness: `c_i = d_i + C(p^k)·GR_i`
  have hc : IsDigitDecomp p (∑ i : Fin p, (1 + PowerSeries.X) ^ (i : ℕ) * phiSeries p (c i)) c :=
    rfl
  have huniq := (existsUnique_digits_padicInt p _).unique hc hcomb
  rw [congrFun huniq i]
  refine modEqPow_iff_exists_C_mul.2 ⟨GR i, ?_⟩
  ring

/-- `digitMatrix (f^n) = (digitMatrix f)^n` (ring-hom multiplicativity, `digitMatrix_mul`). -/
theorem digitMatrix_pow (f : PowerSeries ℤ_[p]) (n : ℕ) :
    digitMatrix (f ^ n) = (digitMatrix f) ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, digitMatrix_one]
  | succ m ih => rw [pow_succ, pow_succ, digitMatrix_mul, ih]

/-- The `j`-th column of `digitMatrix f` is the digit family of `f·(1+T)^j`:
`f·(1+T)^j = Σ_i (1+T)^i·φ((digitMatrix f)_{ij})` (unfold `leftMulMatrix` via the basis
`repr`, `sum_smul_one_add_X_pow_eq`). -/
theorem digitMatrix_col_isDigitDecomp (f : PowerSeries ℤ_[p]) (j : Fin p) :
    f * (1 + PowerSeries.X) ^ (j : ℕ)
      = ∑ i : Fin p, (1 + PowerSeries.X) ^ (i : ℕ) * phiSeries p ((digitMatrix f) i j) := by
  have hx : ((PhiAlg.toPS p).symm f * (digitBasis p j) : PhiAlg p)
      = ∑ i : Fin p, ((digitMatrix f) i j) • ((1 + PowerSeries.X) ^ (i : ℕ) : PhiAlg p) := by
    conv_lhs => rw [← (digitBasis p).sum_repr ((PhiAlg.toPS p).symm f * digitBasis p j)]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [digitMatrix, Algebra.leftMulMatrix_eq_repr_mul, digitBasis_apply (i := i)]
  have hxPS := congrArg (PhiAlg.toPS p) hx
  rwa [map_mul, RingEquiv.apply_symm_apply, digitBasis_apply (i := j),
    PhiAlg.toPS_apply, sum_smul_one_add_X_pow_eq] at hxPS

/-- `digitMatrix (1 + C a · h) = 1 + C a • digitMatrix h` (ring-hom additivity +
multiplicativity + `digitMatrix (C a) = C a • 1`). -/
theorem digitMatrix_one_add_C_mul (a : ℤ_[p]) (h : PowerSeries ℤ_[p]) :
    digitMatrix (1 + PowerSeries.C a * h)
      = 1 + PowerSeries.C a • digitMatrix h := by
  rw [digitMatrix_add, digitMatrix_one, digitMatrix_mul, digitMatrix_C, smul_mul_assoc,
    one_mul]

/-- T908 (iii), RJW TeX 2735: for a unit `f ≡ 1 mod p^k` (`k ≥ 1`),
`𝒩 f ≡ 1 mod p^{k+1}`. Determinant route: write `f = 1 + C(p^k)·h`, so
`digitMatrix f = 1 + C(p^k) • digitMatrix h` and (Taylor expansion,
`Matrix.det_one_add_smul`)
`𝒩 f = det = 1 + (trace (digitMatrix h))·C(p^k) + R·C(p^k)²`. The linear term is
`p·ψ(h)·C(p^k) = C(p^{k+1})·ψ(h)` (`trace_digitMatrix`), the quadratic term carries
`C(p^{2k})` with `2k ≥ k+1`; both are `≡ 0 mod p^{k+1}`. (The unit hypothesis is not
needed for this part — it is recorded to match the source's statement grouping.) -/
theorem normOp_modEq_one {k : ℕ} (hk : 1 ≤ k) {f : PowerSeries ℤ_[p]}
    (_hf : IsUnit f) (h : ModEqPow p k f 1) :
    ModEqPow p (k + 1) (normOp f) 1 := by
  obtain ⟨g, hg⟩ := modEqPow_iff_exists_C_mul.1 h
  -- `f = 1 + C(p^k)·g`
  have hfeq : f = 1 + PowerSeries.C ((p : ℤ_[p]) ^ k) * g := by
    rw [← hg]; ring
  -- the determinant Taylor expansion, with `Rev := R.eval (C(p^k))`
  set Rev := (Matrix.det (1 + (Polynomial.X : Polynomial (PowerSeries ℤ_[p]))
    • (digitMatrix g).map Polynomial.C)).divX.divX.eval (PowerSeries.C ((p : ℤ_[p]) ^ k))
    with hRev
  have hdet : normOp f = 1 + Matrix.trace (digitMatrix g) * PowerSeries.C ((p : ℤ_[p]) ^ k)
      + Rev * PowerSeries.C ((p : ℤ_[p]) ^ k) ^ 2 := by
    rw [normOp_eq_det, hfeq, digitMatrix_one_add_C_mul,
      Matrix.det_one_add_smul (PowerSeries.C ((p : ℤ_[p]) ^ k)) (digitMatrix g), hRev]
  -- `trace = C(p)·ψg`, `C(p^k) = C(p^{k-1})·C(p)`, `C(p^{k+1}) = C(p^{k-1})·C(p)²`
  have htr : Matrix.trace (digitMatrix g) = PowerSeries.C (p : ℤ_[p]) * psiSeries p g := by
    rw [trace_digitMatrix, map_natCast]
  have hpk : (p : ℤ_[p]) ^ k = (p : ℤ_[p]) ^ (k - 1) * (p : ℤ_[p]) := by
    rw [← pow_succ]; congr 1; omega
  have hpk1 : (p : ℤ_[p]) ^ (k + 1) = (p : ℤ_[p]) ^ (k - 1) * (p : ℤ_[p]) * (p : ℤ_[p]) := by
    rw [← pow_succ, ← pow_succ]; congr 1; omega
  -- assemble the `C(p^{k+1})` witness
  refine modEqPow_iff_exists_C_mul.2
    ⟨psiSeries p g + Rev * PowerSeries.C ((p : ℤ_[p]) ^ (k - 1)), ?_⟩
  rw [hdet, htr, hpk1, hpk, map_mul, map_mul, map_mul]
  ring

/-- **`digitMatrix (f^p) ≡ diagonal f mod p`** (the key to part (ii)): the column digit
identity for `f^p`, `f^p·(1+T)^j = Σ_i (1+T)^i φ((digitMatrix(f^p))_{ij})`, is `≡ mod p`
to `φ(f)·(1+T)^j = Σ_i (1+T)^i φ(δ_{ij} f)` (since `f^p ≡ φ(f) mod p`,
`pow_p_modEq_phiSeries`); digit uniqueness mod `p` (`digit_modEq_of_sum_modEq`) extracts
the entrywise congruence. -/
theorem digitMatrix_pow_p_modEq_diagonal (f : PowerSeries ℤ_[p]) (i j : Fin p) :
    ModEqPow p 1 ((digitMatrix (f ^ p)) i j) (if i = j then f else 0) := by
  refine digit_modEq_of_sum_modEq (c := fun i => (digitMatrix (f ^ p)) i j)
    (d := fun i => if i = j then f else 0) ?_ i
  -- LHS sum `= f^p·(1+T)^j`; RHS sum `= φ(f)·(1+T)^j`
  rw [← digitMatrix_col_isDigitDecomp, Finset.sum_eq_single j]
  · rw [if_pos rfl, mul_comm ((1 + PowerSeries.X) ^ (j : ℕ)) (phiSeries p f)]
    -- `f^p·(1+T)^j ≡ φ(f)·(1+T)^j mod p`
    exact (pow_p_modEq_phiSeries f).mul_right ((1 + PowerSeries.X) ^ (j : ℕ))
  · intro b _ hbj; rw [if_neg hbj, phiSeries_zero, mul_zero]
  · intro hb; exact absurd (Finset.mem_univ _) hb

set_option synthInstance.maxHeartbeats 400000 in
-- the `RingHom.map_det`/`Matrix.map` chain over `PowerSeries (ZMod p)` matrices drives
-- nested instance synthesis past the default budget
/-- T908 (ii), RJW TeX 2731: `𝒩 f ≡ f mod p`. Determinant route over `𝔽_p`: reducing
`𝒩 f = det (digitMatrix f)` mod `p`, the matrix `M̄` squares to the scalar
`(p-th power) M̄^p = digitMatrix(f^p) ≡ diagonal f̄ mod p`
(`digitMatrix_pow_p_modEq_diagonal`), so `(det M̄)^p = det (diagonal f̄) = f̄^p`; the
Frobenius `x ↦ x^p` is injective on the domain `𝔽_p⟦T⟧`, giving `det M̄ = f̄`, i.e.
`𝒩 f ≡ f mod p`. (This avoids the `μ_p`-product/twisted-circulant computation: a
replan note for R10.5 — the abstract `Algebra.norm` over `𝔽_p` is the `p`-th power for
the purely inseparable degree-`p` step `B̄/φ(B̄)`.) -/
theorem normOp_modEq_self (f : PowerSeries ℤ_[p]) : ModEqPow p 1 (normOp f) f := by
  set ρ := (PadicInt.toZMod : ℤ_[p] →+* ZMod p) with hρ
  set Mr := (PowerSeries.map ρ).mapMatrix (digitMatrix f) with hMr
  -- `map ρ (𝒩 f) = det M̄`
  have hnorm : PowerSeries.map ρ (normOp f) = Matrix.det Mr := by
    rw [normOp_eq_det, hMr, ← RingHom.map_det]
  -- `M̄^p = diagonal (map ρ f)`
  have hpow : Mr ^ p = Matrix.diagonal (fun _ => PowerSeries.map ρ f) := by
    rw [hMr, ← map_pow ((PowerSeries.map ρ).mapMatrix) (digitMatrix f) p, ← digitMatrix_pow]
    ext i j
    rw [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.diagonal_apply]
    by_cases hij : i = j
    · have := digitMatrix_pow_p_modEq_diagonal f i j
      rw [if_pos hij, modEqPow_one_iff_map_toZMod, ← hρ] at this
      rw [if_pos hij, ← this]
    · have := digitMatrix_pow_p_modEq_diagonal f i j
      rw [if_neg hij, modEqPow_one_iff_map_toZMod, ← hρ, map_zero] at this
      rw [if_neg hij, ← this]
  -- `(det M̄)^p = f̄^p`, then Frobenius injective on the domain `𝔽_p⟦T⟧`
  have hdetpow : (Matrix.det Mr) ^ p = (PowerSeries.map ρ f) ^ p := by
    rw [← Matrix.det_pow, hpow, Matrix.det_diagonal, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin]
  have hdet : Matrix.det Mr = PowerSeries.map ρ f := by
    haveI : CharP (PowerSeries (ZMod p)) p := charP_of_injective_algebraMap' (ZMod p) p
    have hfrobinj := frobenius_inj (PowerSeries (ZMod p)) p
    apply hfrobinj
    rw [frobenius_def, frobenius_def, hdetpow]
  rw [modEqPow_one_iff_map_toZMod, ← hρ, hnorm, hdet]

/-! ### Iterating `𝒩` (part (iv)) -/

/-- `ModEqPow` downgrades along `≤` of the exponent (`p^b ∣ p^a` for `b ≤ a`). -/
theorem ModEqPow.of_le {a b : ℕ} (hab : b ≤ a) {f g : PowerSeries ℤ_[p]}
    (h : ModEqPow p a f g) : ModEqPow p b f g := fun m =>
  dvd_trans (pow_dvd_pow _ hab) (h m)

/-- `𝒩` bundled as a monoid hom (`normOp_one`, `normOp_mul`). -/
noncomputable def normOpHom : PowerSeries ℤ_[p] →* PowerSeries ℤ_[p] where
  toFun := normOp
  map_one' := normOp_one
  map_mul' := normOp_mul

@[simp]
theorem normOpHom_apply (f : PowerSeries ℤ_[p]) : normOpHom f = normOp f := rfl

/-- `𝒩^{[n]}` is multiplicative (`normOp_mul` iterated). -/
theorem normOp_iterate_mul (n : ℕ) (f g : PowerSeries ℤ_[p]) :
    normOp^[n] (f * g) = normOp^[n] f * normOp^[n] g := by
  induction n generalizing f g with
  | zero => simp
  | succ m ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply,
      Function.iterate_succ_apply, normOp_mul, ih]

/-- `𝒩^{[n]}` preserves units (iterate of `normOp_isUnit`). -/
theorem normOp_iterate_isUnit {f : PowerSeries ℤ_[p]} (hf : IsUnit f) (n : ℕ) :
    IsUnit (normOp^[n] f) := by
  induction n with
  | zero => simpa using hf
  | succ m ih => rw [Function.iterate_succ_apply']; exact normOp_isUnit ih

/-- `𝒩^{[n]} f ≡ f mod p` for `f` (iterate part (ii) and chain). -/
theorem normOp_iterate_modEq_self (f : PowerSeries ℤ_[p]) (n : ℕ) :
    ModEqPow p 1 (normOp^[n] f) f := by
  induction n with
  | zero => exact ModEqPow.refl _ _
  | succ m ih =>
    rw [Function.iterate_succ_apply']
    exact (normOp_modEq_self (normOp^[m] f)).trans ih

/-- Iterating part (iii): if `g` is a unit with `g ≡ 1 mod p`, then
`𝒩^{[n]} g ≡ 1 mod p^{n+1}`. -/
theorem normOp_iterate_modEq_one {g : PowerSeries ℤ_[p]} (hg : IsUnit g)
    (h : ModEqPow p 1 g 1) (n : ℕ) :
    ModEqPow p (n + 1) (normOp^[n] g) 1 := by
  induction n with
  | zero => simpa using h
  | succ m ih =>
    rw [Function.iterate_succ_apply']
    exact normOp_modEq_one (by omega) (normOp_iterate_isUnit hg m) ih

/-- T908 (iv), RJW TeX 2737: for a unit `f` and `k₁ ≤ k₂`,
`𝒩^{[k₂]} f ≡ 𝒩^{[k₁]} f mod p^{k₁+1}`. From part (ii), the unit
`g := 𝒩^{[k₂−k₁]} f · f⁻¹ ≡ 1 mod p`; iterating part (iii) `k₁` times gives
`𝒩^{[k₁]} g ≡ 1 mod p^{k₁+1}`; unfolding `𝒩^{[k₁]} g = 𝒩^{[k₂]} f · (𝒩^{[k₁]} f)⁻¹`
(`𝒩` multiplicative) and multiplying by `𝒩^{[k₁]} f` finishes. -/
theorem normOp_iterate_modEq {k₁ k₂ : ℕ} (h : k₁ ≤ k₂) {f : PowerSeries ℤ_[p]}
    (hf : IsUnit f) :
    ModEqPow p (k₁ + 1) (normOp^[k₂] f) (normOp^[k₁] f) := by
  -- `g := 𝒩^{k₂−k₁}f · f⁻¹`, a unit `≡ 1 mod p`
  set finv := ((hf.unit⁻¹ : (PowerSeries ℤ_[p])ˣ) : PowerSeries ℤ_[p]) with hfinv
  have hfinv_mul : f * finv = 1 := hf.mul_val_inv
  set g := normOp^[k₂ - k₁] f * finv with hg
  have hgunit : IsUnit g := by
    rw [hg]; exact (normOp_iterate_isUnit hf _).mul (hf.unit⁻¹).isUnit
  have hg1 : ModEqPow p 1 g 1 := by
    rw [hg]
    have hstep : ModEqPow p 1 (normOp^[k₂ - k₁] f * finv) (f * finv) :=
      (normOp_iterate_modEq_self f _).mul_right finv
    rwa [hfinv_mul] at hstep
  -- iterate (iii): `𝒩^{k₁} g ≡ 1 mod p^{k₁+1}`
  have hiter := normOp_iterate_modEq_one hgunit hg1 k₁
  -- `𝒩^{k₁} g = 𝒩^{k₂} f · 𝒩^{k₁} finv`
  rw [hg, normOp_iterate_mul,
    show normOp^[k₁] (normOp^[k₂ - k₁] f) = normOp^[k₂] f from by
      rw [← Function.iterate_add_apply]; congr 1; omega] at hiter
  -- multiply by `𝒩^{k₁} f`; `𝒩^{k₁} f · 𝒩^{k₁} finv = 𝒩^{k₁} 1 = 1`
  have hffinv : normOp^[k₁] f * normOp^[k₁] finv = 1 := by
    rw [← normOp_iterate_mul, hfinv_mul]; simp [Function.iterate_fixed normOp_one]
  have hmul := hiter.mul_right (normOp^[k₁] f)
  rwa [one_mul, mul_assoc, mul_comm (normOp^[k₁] finv) (normOp^[k₁] f), hffinv, mul_one] at hmul

/-! ## Compactness of `ℤ_p⟦T⟧` and sequential extraction (T909)

For the coefficientwise (Pi) topology (`PowerSeries.WithPiTopology`), `ℤ_p⟦T⟧` is
compact (Tychonoff, `ℤ_[p]` compact) and — being a countable product of metric
spaces — sequentially compact. The units form a closed subset and coefficient
maps are continuous: exactly the inputs for the diagonal extraction in Coleman's
theorem (RJW TeX 2784, "such a subsequence exists, as `ℤ_p⟦T⟧^×` is compact";
replan R10.6). -/

open scoped PowerSeries.WithPiTopology

section Compactness

variable (p)

/-- `ℤ_p⟦T⟧` is compact for the coefficientwise topology (Tychonoff: the
underlying space is `(Unit →₀ ℕ) → ℤ_[p]`, a product of the compact `ℤ_[p]`). -/
instance instCompactSpace : CompactSpace (PowerSeries ℤ_[p]) :=
  inferInstanceAs (CompactSpace ((Unit →₀ ℕ) → ℤ_[p]))

/-- `ℤ_p⟦T⟧` is sequentially compact: the coefficient index `Unit →₀ ℕ` is
countable, so the product topology is metrizable, hence first-countable; with
compactness this gives sequential compactness. -/
instance instSeqCompactSpace : SeqCompactSpace (PowerSeries ℤ_[p]) :=
  inferInstanceAs (SeqCompactSpace ((Unit →₀ ℕ) → ℤ_[p]))

variable {p}

/-- T909: every sequence in `ℤ_p⟦T⟧` has a coefficientwise-convergent
subsequence (the extraction feeding T910's diagonal argument). -/
theorem exists_subseq_tendsto (g : ℕ → PowerSeries ℤ_[p]) :
    ∃ (f : PowerSeries ℤ_[p]) (φ : ℕ → ℕ), StrictMono φ ∧
      Filter.Tendsto (g ∘ φ) Filter.atTop (nhds f) :=
  SeqCompactSpace.tendsto_subseq g

/-- T909: coefficient maps are continuous limits — coefficientwise convergence
`gₘ → f` gives `coeff n (gₘ) → coeff n f` for every `n`. (Projection continuity
in the Pi topology; T910's diagonal argument passes limits through coefficients
with this.) -/
theorem tendsto_coeff {g : ℕ → PowerSeries ℤ_[p]} {f : PowerSeries ℤ_[p]}
    (hg : Filter.Tendsto g Filter.atTop (nhds f)) (n : ℕ) :
    Filter.Tendsto (fun m => PowerSeries.coeff n (g m)) Filter.atTop
      (nhds (PowerSeries.coeff n f)) :=
  ((WithPiTopology.continuous_coeff ℤ_[p] n).tendsto f).comp hg

/-- T909: the units of `ℤ_p⟦T⟧` form a closed subset for the coefficientwise
topology. A power series is a unit iff its constant coefficient is a unit in
`ℤ_[p]` (`PowerSeries.isUnit_iff_constantCoeff`), iff that coefficient has norm
`1` (`PadicInt.isUnit_iff`); this is the preimage of the closed set
`{‖·‖ = 1} ⊆ ℝ` under the continuous map `f ↦ ‖constantCoeff f‖`. (Limits of
units along convergent subsequences are units — used in T910.) -/
theorem isClosed_isUnit :
    IsClosed {f : PowerSeries ℤ_[p] | IsUnit f} := by
  have hset : {f : PowerSeries ℤ_[p] | IsUnit f}
      = (fun f => ‖PowerSeries.constantCoeff f‖) ⁻¹' {1} := by
    ext f
    simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_singleton_iff]
    rw [PowerSeries.isUnit_iff_constantCoeff, PadicInt.isUnit_iff]
  rw [hset]
  exact (isClosed_singleton (x := (1 : ℝ))).preimage
    ((WithPiTopology.continuous_constantCoeff ℤ_[p]).norm)

end Compactness

end Coleman

end PadicLFunctions
