module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.ConcreteSetup
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.IntegralBridge
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.KummerFurtwaengler
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.CanonicalResidueRoot
public import Mathlib.NumberTheory.Cyclotomic.Basic

/-!
# Concrete cyclotomic local setup at a prime above ℓ ≠ p

This file is the home for **REF-18c2c5-b** — constructing a
`ConcreteStickelbergerSetup ℓ p k K R'` instance where
`K = ℚ(ζ_p)`, `R' ⊃ K` is a cyclotomic extension containing `ζ_ℓ`,
and the user supplies a prime `Q ⊂ 𝓞 R'` above ℓ.

## Strategy

We provide a CONSTRUCTOR `mkConcreteStickelbergerSetup` taking the
prime `Q` (above ℓ in `𝓞 R'`) as input and assembling all the required
witnesses from mathlib's cyclotomic API:

* `zeta_p` and `zeta_ell` come from
  `IsCyclotomicExtension.exists_isPrimitiveRoot` applied to `R'`.
* `zeta_p_int`, `zeta_ell_int` come from `IsPrimitiveRoot.toInteger`.
* The residue field `k = 𝓞 R' / Q` is the canonical choice; the
  residue map is `Ideal.Quotient.mk Q`.
* `card_k = ℓ ^ f` requires the inertia degree of Q over ℓ.
* The primitive p-th root in k is the image of `zetaPInt` under the
  residue map; primitivity requires `p ∣ #k - 1`.

## Status

Stage 1 (primitive roots in R') — DONE.
Stage 2 (integral lifts in 𝓞 R') — DONE.
Stage 3 (residue field and map) — DONE.
Stage 4 (assembly into the bundle) — REMAINING (still needs `card_k`,
   `hzeta_k`, `hdiv` and the bundle-building tactic).
-/

@[expose] public section

noncomputable section

open scoped NumberField

namespace BernoulliRegular

namespace Furtwaengler

universe u v w

namespace CyclotomicLocalSetup

variable (p ℓ : ℕ) [hp : Fact p.Prime] [hℓ : Fact ℓ.Prime]
variable (K : Type v) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
variable (R' : Type w) [Field R'] [NumberField R'] [Algebra K R']
  [IsScalarTower ℚ K R'] [IsCyclotomicExtension {p, ℓ} ℚ R']

/-! ### Step 1 — choose primitive roots in `R'` -/

/-- A primitive `p`-th root of unity in `R'`. -/
noncomputable def zetaP : R' :=
  (IsCyclotomicExtension.exists_isPrimitiveRoot ℚ R'
    (S := ({p, ℓ} : Set ℕ))
    (Set.mem_insert _ _) (Fact.out : p.Prime).ne_zero).choose

omit hℓ in
theorem zetaP_isPrimitiveRoot : IsPrimitiveRoot (zetaP p ℓ R') p :=
  (IsCyclotomicExtension.exists_isPrimitiveRoot ℚ R'
    (S := ({p, ℓ} : Set ℕ))
    (Set.mem_insert _ _) (Fact.out : p.Prime).ne_zero).choose_spec

/-- A primitive `ℓ`-th root of unity in `R'`. -/
noncomputable def zetaEll : R' :=
  (IsCyclotomicExtension.exists_isPrimitiveRoot ℚ R'
    (S := ({p, ℓ} : Set ℕ))
    (Set.mem_insert_of_mem _ rfl) (Fact.out : ℓ.Prime).ne_zero).choose

omit hp in
theorem zetaEll_isPrimitiveRoot : IsPrimitiveRoot (zetaEll p ℓ R') ℓ :=
  (IsCyclotomicExtension.exists_isPrimitiveRoot ℚ R'
    (S := ({p, ℓ} : Set ℕ))
    (Set.mem_insert_of_mem _ rfl) (Fact.out : ℓ.Prime).ne_zero).choose_spec

/-! ### Step 2 — integral lifts in `𝓞 R'` -/

/-- Integral lift of `zetaP` to `𝓞 R'`. -/
noncomputable def zetaPInt : 𝓞 R' :=
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  (zetaP_isPrimitiveRoot p ℓ R').toInteger

/-- Integral lift of `zetaEll` to `𝓞 R'`. -/
noncomputable def zetaEllInt : 𝓞 R' :=
  haveI : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
  (zetaEll_isPrimitiveRoot p ℓ R').toInteger

omit hℓ in
theorem algebraMap_zetaPInt :
    algebraMap (𝓞 R') R' (zetaPInt p ℓ R') = zetaP p ℓ R' :=
  rfl

omit hp in
theorem algebraMap_zetaEllInt :
    algebraMap (𝓞 R') R' (zetaEllInt p ℓ R') = zetaEll p ℓ R' :=
  rfl

omit hℓ in
theorem zetaPInt_isPrimitiveRoot :
    haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
    IsPrimitiveRoot (zetaPInt p ℓ R') p := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  exact (zetaP_isPrimitiveRoot p ℓ R').toInteger_isPrimitiveRoot

omit hp in
theorem zetaEllInt_isPrimitiveRoot :
    haveI : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
    IsPrimitiveRoot (zetaEllInt p ℓ R') ℓ := by
  haveI : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
  exact (zetaEll_isPrimitiveRoot p ℓ R').toInteger_isPrimitiveRoot

/-- The uniformizer candidate `π = ζ_ℓ - 1`. -/
noncomputable def piEll : 𝓞 R' :=
  zetaEllInt p ℓ R' - 1

/-! ### Step 3 — residue field and map (given prime Q above ℓ)

Given a prime `Q ⊂ 𝓞 R'` containing ℓ, the residue field is
`k = 𝓞 R' / Q` and the residue map is the canonical quotient map.
The Q is supplied by the user; existence is via going-up
(`Ideal.nonempty_primesOver`).
-/

variable (Q : Ideal (𝓞 R')) [Q.IsPrime]

/-- The residue field at Q. -/
abbrev residueField : Type w := 𝓞 R' ⧸ Q

/-- The residue map. -/
noncomputable def residueMap : 𝓞 R' →+* residueField R' Q :=
  Ideal.Quotient.mk Q

omit [NumberField R'] [Q.IsPrime] in
theorem residueMap_surjective : Function.Surjective (residueMap R' Q) :=
  Ideal.Quotient.mk_surjective

omit [NumberField R'] [Q.IsPrime] in
theorem residueMap_ker : RingHom.ker (residueMap R' Q) = Q := Ideal.mk_ker

omit [Q.IsPrime] in
/-- `Q ≠ ⊥` whenever `(ℓ : 𝓞 R') ∈ Q`, since `ℓ ≠ 0`. -/
theorem Q_ne_bot (hQ : (ℓ : 𝓞 R') ∈ Q) : Q ≠ ⊥ := by
  intro hQ_bot
  rw [hQ_bot, Ideal.mem_bot] at hQ
  exact (by exact_mod_cast (Fact.out : ℓ.Prime).ne_zero : (ℓ : 𝓞 R') ≠ 0) hQ

/-- Q is maximal (since prime + non-bot in a Dedekind domain). -/
theorem Q_isMaximal (hQ : (ℓ : 𝓞 R') ∈ Q) : Q.IsMaximal :=
  Ideal.IsPrime.isMaximal inferInstance (Q_ne_bot ℓ R' Q hQ)

/-- The residue field `𝓞 R' / Q` is a Field (assuming hQ). -/
@[reducible]
noncomputable def residueFieldOfHQ (hQ : (ℓ : 𝓞 R') ∈ Q) :
    Field (residueField R' Q) :=
  haveI := Q_isMaximal ℓ R' Q hQ
  Ideal.Quotient.field Q

/-- The residue field `𝓞 R' / Q` is finite. -/
@[reducible]
noncomputable def residueFieldFintype (hQ : (ℓ : 𝓞 R') ∈ Q) :
    Fintype (residueField R' Q) := by
  haveI : NeZero Q := ⟨Q_ne_bot ℓ R' Q hQ⟩
  haveI : Finite (𝓞 R' ⧸ Q) := by
    rw [← Ideal.absNorm_ne_zero_iff]
    exact Ideal.absNorm_ne_zero_of_nonZeroDivisors
      ⟨Q, mem_nonZeroDivisors_iff_ne_zero.mpr (NeZero.ne Q)⟩
  exact Fintype.ofFinite _

/-! ### Step 5 — primitive p-th root in residue field

Apply mathlib's `IsPrimitiveRoot.idealQuotient_mk` to lift `zetaPInt` to
a primitive p-th root in the residue field, given coprimality of
`absNorm Q` with `p`.
-/

omit hℓ in
/-- The image of `zetaPInt` in the residue field is a primitive p-th root,
provided `(absNorm Q).Coprime p`. -/
theorem residueMap_zetaPInt_isPrimitiveRoot
    (_hQ : (ℓ : 𝓞 R') ∈ Q)
    (hcop : (Ideal.absNorm Q).Coprime p) :
    haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
    IsPrimitiveRoot (residueMap R' Q (zetaPInt p ℓ R')) p := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hQ_ne_bot : Q ≠ ⊥ := by
    intro hbot
    have hzero : Ideal.absNorm Q = 0 := Ideal.absNorm_eq_zero_iff.mpr hbot
    rw [hzero] at hcop
    exact (Fact.out : p.Prime).ne_one ((Nat.coprime_zero_left p).mp hcop)
  haveI : NeZero Q := ⟨hQ_ne_bot⟩
  -- absNorm Q ≠ 1: Q ≠ ⊤ (since Q is prime, so proper).
  have habs_ne_one : Ideal.absNorm Q ≠ 1 := by
    intro h
    rw [Ideal.absNorm_eq_one_iff] at h
    exact (inferInstance : Q.IsPrime).ne_top h
  exact (zetaPInt_isPrimitiveRoot p ℓ R').idealQuotient_mk habs_ne_one hcop

/-! ### Step 6 — bundle assembly

We assemble all the pieces into a `ConcreteStickelbergerSetup`. The
key trick: take the `Field` and `Fintype` instances on `residueField R' Q`
as **explicit parameters** so the structure's `[Field k] [Fintype k]`
binder can match. The user constructs them (or uses our defs) before
calling.
-/

/-! Step 1 status: the SCALAR fields (zeta_p, zeta_ell, zeta_p_int,
zeta_ell_int, π, Q, residueMap, hπ, etc.) are constructed above.
The 5 ADDITIONAL fields the structure requires (`zeta_p_int_residue`,
`psi`, `hpsi`, `psiExponent`, `psi_eq_zeta_ell_pow`) require building
the additive character `ψ : k →+ R'` from a trace map. This is
itself ~100 LOC of trace-form infrastructure, deferred. -/

/-! ### Stage 4 — residue field cardinality witness for `k = 𝓞 K ⧸ P`

For the source-side bundle `S : FullTeichDworkSetup ℓ p (𝓞 K ⧸ P) K R'`,
the `card_k` field requires `Fintype.card (𝓞 K ⧸ P) = ℓ ^ f` for some
`f : ℕ`. We derive this from `Ideal.absNorm_eq_pow_inertiaDeg'`, with
`f` the inertia degree of `P` over `(ℓ : ℤ)`. -/

variable {p₀ ℓ₀ : ℕ} [Fact p₀.Prime] [Fact ℓ₀.Prime]
variable {K₀ : Type v} [Field K₀] [NumberField K₀]
  [IsCyclotomicExtension {p₀} ℚ K₀]

omit [NumberField K₀] in
/-- A maximal ideal of `𝓞 K` containing the rational prime `ℓ` lies over
the principal ideal `(ℓ)` of `ℤ`. -/
theorem under_eq_span_of_natCast_mem
    (P : Ideal (𝓞 K₀)) [hP_max : P.IsMaximal]
    (hℓ_in_P : (ℓ₀ : 𝓞 K₀) ∈ P) :
    Ideal.under ℤ P = Ideal.span ({(ℓ₀ : ℤ)} : Set ℤ) := by
  have hℓ_in_comap : (ℓ₀ : ℤ) ∈ Ideal.comap (algebraMap ℤ (𝓞 K₀)) P := by
    rw [Ideal.mem_comap]
    simpa using hℓ_in_P
  have h_span_le : Ideal.span ({(ℓ₀ : ℤ)} : Set ℤ) ≤ Ideal.under ℤ P := by
    rw [Ideal.span_le, Set.singleton_subset_iff]
    exact hℓ_in_comap
  have hℓ_prime_int : Prime ((ℓ₀ : ℤ)) := by
    rw [Int.prime_iff_natAbs_prime]
    simpa using (Fact.out : ℓ₀.Prime)
  have h_span_max : (Ideal.span ({(ℓ₀ : ℤ)} : Set ℤ)).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible hℓ_prime_int.irreducible
  have h_under_ne_top : Ideal.under ℤ P ≠ ⊤ := by
    intro h
    have h_one_mem_under : (1 : ℤ) ∈ Ideal.under ℤ P := h ▸ Submodule.mem_top
    have h_one_mem_comap :
        (1 : ℤ) ∈ Ideal.comap (algebraMap ℤ (𝓞 K₀)) P := by
      simpa [Ideal.under] using h_one_mem_under
    have h_one_mem : (1 : 𝓞 K₀) ∈ P := by
      simpa using h_one_mem_comap
    exact hP_max.ne_top (Ideal.eq_top_of_isUnit_mem _ h_one_mem isUnit_one)
  exact (h_span_max.eq_of_le h_under_ne_top h_span_le).symm

/-- **Stage 4 / `card_k`**: For a maximal `P ⊂ 𝓞 K` containing the
rational prime `ℓ`, the residue-field cardinality is a power of `ℓ`,
with exponent the inertia degree `(span {(ℓ : ℤ)}).inertiaDeg P`. -/
theorem cardResidueField_eq_pow_ell_inertiaDeg
    (P : Ideal (𝓞 K₀)) [hP_max : P.IsMaximal]
    (hℓ_in_P : (ℓ₀ : 𝓞 K₀) ∈ P) :
    Fintype.card (𝓞 K₀ ⧸ P) =
      ℓ₀ ^ ((Ideal.span ({(ℓ₀ : ℤ)} : Set ℤ)).inertiaDeg P) := by
  -- Step 1: (ℓ : ℤ) ∈ comap algebraMap P.
  have hℓ_in_comap : (ℓ₀ : ℤ) ∈ Ideal.comap (algebraMap ℤ (𝓞 K₀)) P := by
    rw [Ideal.mem_comap]
    simpa using hℓ_in_P
  -- Step 2: span {(ℓ : ℤ)} ≤ under ℤ P.
  have h_span_le : Ideal.span ({(ℓ₀ : ℤ)} : Set ℤ) ≤ Ideal.under ℤ P := by
    rw [Ideal.span_le, Set.singleton_subset_iff]
    exact hℓ_in_comap
  -- Step 3: span {(ℓ : ℤ)} is maximal in ℤ (since ℓ is prime).
  have hℓ_prime_int : Prime ((ℓ₀ : ℤ)) := by
    rw [Int.prime_iff_natAbs_prime]
    simpa using (Fact.out : ℓ₀.Prime)
  have h_span_max : (Ideal.span ({(ℓ₀ : ℤ)} : Set ℤ)).IsMaximal := by
    have h_irred : Irreducible ((ℓ₀ : ℤ)) := hℓ_prime_int.irreducible
    exact PrincipalIdealRing.isMaximal_of_irreducible h_irred
  -- Step 4: under ℤ P ≠ ⊤ (since P ≠ ⊤).
  have h_under_ne_top : Ideal.under ℤ P ≠ ⊤ := by
    intro h
    have : (1 : ℤ) ∈ Ideal.under ℤ P := h ▸ Submodule.mem_top
    rw [Ideal.under, Ideal.mem_comap] at this
    have h_one : (1 : 𝓞 K₀) ∈ P := by
      simpa using this
    exact hP_max.ne_top (Ideal.eq_top_of_isUnit_mem _ h_one isUnit_one)
  -- Step 5: span {(ℓ : ℤ)} = under ℤ P.
  have h_eq : Ideal.span ({(ℓ₀ : ℤ)} : Set ℤ) = Ideal.under ℤ P :=
    h_span_max.eq_of_le h_under_ne_top h_span_le
  -- Step 6: P lies over span {(ℓ : ℤ)}.
  have hP_lies : P.LiesOver (Ideal.span ({(ℓ₀ : ℤ)} : Set ℤ)) := ⟨h_eq⟩
  -- Step 7: absNorm = ℓ ^ inertiaDeg.
  have h_absNorm :
      Ideal.absNorm P = ℓ₀ ^ ((Ideal.span ({(ℓ₀ : ℤ)} : Set ℤ)).inertiaDeg P) :=
    Ideal.absNorm_eq_pow_inertiaDeg' P (Fact.out : ℓ₀.Prime)
  -- Step 8: absNorm = card.
  have h_card : Ideal.absNorm P = Fintype.card (𝓞 K₀ ⧸ P) := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
  rw [← h_card, h_absNorm]

/-- **Stage 4 / `card_k` existence form**: For a maximal `P ⊂ 𝓞 K`
containing `ℓ`, there exists `f : ℕ` with `Fintype.card (𝓞 K ⧸ P) = ℓ ^ f`. -/
theorem exists_inertiaDeg_eq_card_residueField
    (P : Ideal (𝓞 K₀)) [P.IsMaximal]
    (hℓ_in_P : (ℓ₀ : 𝓞 K₀) ∈ P) :
    ∃ f : ℕ, Fintype.card (𝓞 K₀ ⧸ P) = ℓ₀ ^ f :=
  ⟨_, cardResidueField_eq_pow_ell_inertiaDeg P hℓ_in_P⟩

/-! ### Stage 4 — `ringChar` of `𝓞 K ⧸ P` -/

omit [NumberField K₀] in
/-- **CharP witness**: `(𝓞 K ⧸ P)` has characteristic `ℓ` when `(ℓ : 𝓞 K) ∈ P`. -/
theorem charP_residueField_of_ell_mem (P : Ideal (𝓞 K₀)) [hP_max : P.IsMaximal]
    (hℓ_in_P : (ℓ₀ : 𝓞 K₀) ∈ P) :
    CharP (𝓞 K₀ ⧸ P) ℓ₀ := by
  letI : Field (𝓞 K₀ ⧸ P) := Ideal.Quotient.field P
  refine ⟨fun n => ?_⟩
  rw [show ((n : 𝓞 K₀ ⧸ P)) = (Ideal.Quotient.mk P) ((n : 𝓞 K₀)) from
    (map_natCast _ _).symm]
  rw [Ideal.Quotient.eq_zero_iff_mem]
  -- (n : 𝓞 K) ∈ P ↔ ℓ ∣ n.
  -- Forward: if (n : 𝓞 K) ∈ P, then in 𝓞 K ⧸ P (a field of char p₀ = ℓ since
  -- (ℓ : 𝓞 K) ∈ P), n becomes 0.
  -- We need a more direct argument: P ∩ ℤ contains ℓ, P ∩ ℤ is prime in ℤ,
  -- so P ∩ ℤ = (ℓ).
  constructor
  · intro h_mem
    -- (n : 𝓞 K) ∈ P. We show ℓ ∣ n.
    -- Use that P.under ℤ = (ℓ) (proven in cardResidueField_eq_pow_ell_inertiaDeg's
    -- hP_lies block). Re-derive here.
    have hℓ_in_comap : (ℓ₀ : ℤ) ∈ Ideal.comap (algebraMap ℤ (𝓞 K₀)) P := by
      rw [Ideal.mem_comap]; simpa using hℓ_in_P
    have h_span_le : Ideal.span ({(ℓ₀ : ℤ)} : Set ℤ) ≤ Ideal.under ℤ P := by
      rw [Ideal.span_le, Set.singleton_subset_iff]; exact hℓ_in_comap
    have hℓ_prime_int : Prime ((ℓ₀ : ℤ)) := by
      rw [Int.prime_iff_natAbs_prime]; simpa using (Fact.out : ℓ₀.Prime)
    have h_span_max : (Ideal.span ({(ℓ₀ : ℤ)} : Set ℤ)).IsMaximal :=
      PrincipalIdealRing.isMaximal_of_irreducible hℓ_prime_int.irreducible
    have h_under_ne_top : Ideal.under ℤ P ≠ ⊤ := by
      intro h
      have : (1 : ℤ) ∈ Ideal.under ℤ P := h ▸ Submodule.mem_top
      rw [Ideal.under, Ideal.mem_comap] at this
      have h_one : (1 : 𝓞 K₀) ∈ P := by
        simpa using this
      exact hP_max.ne_top (Ideal.eq_top_of_isUnit_mem _ h_one isUnit_one)
    have h_eq : Ideal.span ({(ℓ₀ : ℤ)} : Set ℤ) = Ideal.under ℤ P :=
      h_span_max.eq_of_le h_under_ne_top h_span_le
    have hn_in_under : (n : ℤ) ∈ Ideal.under ℤ P := by
      rw [Ideal.under, Ideal.mem_comap]
      push_cast
      exact h_mem
    rw [← h_eq, Ideal.mem_span_singleton] at hn_in_under
    exact_mod_cast hn_in_under
  · intro h_dvd
    obtain ⟨k, rfl⟩ := h_dvd
    push_cast
    exact Ideal.mul_mem_right _ _ hℓ_in_P

omit [NumberField K₀] in
/-- **Stage 4 / `h_ringChar`**: `ringChar (𝓞 K ⧸ P) = ℓ` for maximal
`P ⊂ 𝓞 K` with `(ℓ : 𝓞 K) ∈ P` and `ℓ` prime. -/
theorem ringChar_residueField_eq_ell
    (P : Ideal (𝓞 K₀)) [hP_max : P.IsMaximal]
    (hℓ_in_P : (ℓ₀ : 𝓞 K₀) ∈ P) :
    letI : Field (𝓞 K₀ ⧸ P) := Ideal.Quotient.field P
    ringChar (𝓞 K₀ ⧸ P) = ℓ₀ := by
  letI : Field (𝓞 K₀ ⧸ P) := Ideal.Quotient.field P
  haveI := charP_residueField_of_ell_mem P hℓ_in_P
  exact ringChar.eq (𝓞 K₀ ⧸ P) ℓ₀

/-! ### Stage 4 — `Algebra (ZMod ℓ) (𝓞 K ⧸ P)` instance -/

/-- **Stage 4 / `zmodAlgebra`**: `Algebra (ZMod ℓ) (𝓞 K ⧸ P)` instance,
derived from `CharP (𝓞 K ⧸ P) ℓ` via `ZMod.algebra`. The bundle's
abstract scalar tower expects `ZMod ℓ` to act on the residue field; this
provides the algebra structure for that role. -/
@[reducible]
noncomputable def algebra_zmod_residueField
    (P : Ideal (𝓞 K₀)) [hP_max : P.IsMaximal]
    (hℓ_in_P : (ℓ₀ : 𝓞 K₀) ∈ P) :
    letI : Field (𝓞 K₀ ⧸ P) := Ideal.Quotient.field P
    Algebra (ZMod ℓ₀) (𝓞 K₀ ⧸ P) :=
  letI : Field (𝓞 K₀ ⧸ P) := Ideal.Quotient.field P
  haveI := charP_residueField_of_ell_mem P hℓ_in_P
  ZMod.algebra (𝓞 K₀ ⧸ P) ℓ₀

/-! ### Stage 4 — residueMap construction at a split prime

Building the bundle for `k = 𝓞 K ⧸ P` requires a ring hom
`residueMap : 𝓞 R' →+* (𝓞 K ⧸ P)` with explicit kernel a prime `Q` of
`𝓞 R'` over `P`. This requires `f(Q/P) = 1` (residue degree one), since
otherwise `𝓞 R' ⧸ Q` is a strict extension of `𝓞 K ⧸ P`. We package
the splitting witness as an iso `𝓞 R' ⧸ Q ≃+* 𝓞 K ⧸ P` plus the
under-equality. -/

/-- **residueMap from splitting iso**: given a prime `Q ⊂ 𝓞 R'` with
`Q.under (𝓞 K) = P` and an iso `𝓞 R' ⧸ Q ≃+* 𝓞 K ⧸ P`, define a ring
hom `𝓞 R' →+* (𝓞 K ⧸ P)` factoring through `Q`. -/
noncomputable def residueMap_of_split
    {R' : Type w} [Field R'] [NumberField R'] [Algebra K₀ R']
    (Q : Ideal (𝓞 R')) (P : Ideal (𝓞 K₀))
    (iso : (𝓞 R' ⧸ Q) ≃+* (𝓞 K₀ ⧸ P)) :
    𝓞 R' →+* (𝓞 K₀ ⧸ P) :=
  (iso : (𝓞 R' ⧸ Q) →+* (𝓞 K₀ ⧸ P)).comp (Ideal.Quotient.mk Q)

omit [NumberField K₀] in
/-- **`residueMap_of_split` is surjective** (composition of two surjective
ring homs). -/
theorem residueMap_of_split_surjective {R' : Type w} [Field R'] [NumberField R'] [Algebra K₀ R']
    (Q : Ideal (𝓞 R')) (P : Ideal (𝓞 K₀))
    (iso : (𝓞 R' ⧸ Q) ≃+* (𝓞 K₀ ⧸ P)) :
    Function.Surjective (residueMap_of_split Q P iso) :=
  iso.surjective.comp Ideal.Quotient.mk_surjective

omit [NumberField K₀] in
/-- **Kernel of `residueMap_of_split` equals `Q`**: since the iso has
trivial kernel, the kernel of the composition is the kernel of
`Quotient.mk Q`, which is `Q`. -/
theorem residueMap_of_split_ker {R' : Type w} [Field R'] [NumberField R'] [Algebra K₀ R']
    (Q : Ideal (𝓞 R')) (P : Ideal (𝓞 K₀))
    (iso : (𝓞 R' ⧸ Q) ≃+* (𝓞 K₀ ⧸ P)) :
    RingHom.ker (residueMap_of_split Q P iso) = Q := by
  unfold residueMap_of_split
  ext x
  constructor
  · intro hx
    rw [RingHom.mem_ker, RingHom.coe_comp, Function.comp_apply] at hx
    have h_iso_eq : (iso : (𝓞 R' ⧸ Q) →+* (𝓞 K₀ ⧸ P))
        ((Ideal.Quotient.mk Q) x) = 0 := hx
    have : (Ideal.Quotient.mk Q) x = 0 :=
      iso.injective (h_iso_eq.trans (map_zero _).symm)
    rwa [Ideal.Quotient.eq_zero_iff_mem] at this
  · intro hx
    rw [RingHom.mem_ker, RingHom.coe_comp, Function.comp_apply]
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx, map_zero]

/-! ### Stage 4 — K-algebra compatibility of the splitting iso

For the split-prime construction to identify `S.descentPrime` (= `Q.under (𝓞 K)`)
with `P`, we need the iso `𝓞 R' ⧸ Q ≃+* 𝓞 K ⧸ P` to be K-algebra
compatible — i.e., the iso composed with `Quotient.mk Q ∘ algebraMap`
on the `𝓞 R'` side equals `Quotient.mk P` on the `𝓞 K` side. -/

/-- **K-algebra compatibility predicate**: the iso commutes with the
canonical residue maps on `𝓞 K`. -/
def IsKAlgebraCompatibleSplittingIso
    {R' : Type w} [Field R'] [NumberField R'] [Algebra K₀ R']
    (Q : Ideal (𝓞 R')) (P : Ideal (𝓞 K₀))
    (iso : (𝓞 R' ⧸ Q) ≃+* (𝓞 K₀ ⧸ P)) : Prop :=
  ∀ x : 𝓞 K₀,
    iso ((Ideal.Quotient.mk Q) (algebraMap (𝓞 K₀) (𝓞 R') x)) =
      (Ideal.Quotient.mk P) x

omit [NumberField K₀] in
/-- **`residueMap_of_split` on `algebraMap`**: under K-algebra compat,
the residueMap composed with the algebra map equals the canonical
quotient map on `𝓞 K`. -/
theorem residueMap_of_split_algebraMap {R' : Type w} [Field R'] [NumberField R'] [Algebra K₀ R']
    (Q : Ideal (𝓞 R')) (P : Ideal (𝓞 K₀))
    (iso : (𝓞 R' ⧸ Q) ≃+* (𝓞 K₀ ⧸ P))
    (h_compat : IsKAlgebraCompatibleSplittingIso Q P iso)
    (x : 𝓞 K₀) :
    residueMap_of_split Q P iso (algebraMap (𝓞 K₀) (𝓞 R') x) =
      (Ideal.Quotient.mk P) x := by
  unfold residueMap_of_split
  simp only [RingHom.coe_comp, Function.comp_apply]
  exact h_compat x

omit [NumberField K₀] in
/-- **K-algebra compat ⟹ Q lies over P**. The under-pullback equals `P`. -/
theorem under_eq_P_of_kAlgebraCompat {R' : Type w} [Field R'] [NumberField R'] [Algebra K₀ R']
    (Q : Ideal (𝓞 R')) [_hQ_prime : Q.IsPrime]
    (P : Ideal (𝓞 K₀)) [_hP_max : P.IsMaximal]
    (iso : (𝓞 R' ⧸ Q) ≃+* (𝓞 K₀ ⧸ P))
    (h_compat : IsKAlgebraCompatibleSplittingIso Q P iso) :
    Q.under (𝓞 K₀) = P := by
  ext x
  rw [Ideal.under, Ideal.mem_comap]
  constructor
  · intro hx
    -- algebraMap x ∈ Q  ⟹  Quotient.mk Q (algebraMap x) = 0
    -- ⟹  iso (...) = 0  ⟹  Quotient.mk P x = 0  ⟹  x ∈ P
    have h₁ : (Ideal.Quotient.mk Q) (algebraMap (𝓞 K₀) (𝓞 R') x) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr hx
    have h₂ := h_compat x
    rw [h₁, map_zero] at h₂
    exact Ideal.Quotient.eq_zero_iff_mem.mp h₂.symm
  · intro hx
    -- x ∈ P  ⟹  Quotient.mk P x = 0  ⟹  iso(...) = 0
    -- ⟹  Quotient.mk Q (algebraMap x) = 0  ⟹  algebraMap x ∈ Q
    have h₁ : (Ideal.Quotient.mk P) x = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr hx
    have h₂ := h_compat x
    rw [h₁] at h₂
    have h₃ : (Ideal.Quotient.mk Q) (algebraMap (𝓞 K₀) (𝓞 R') x) = 0 :=
      iso.injective (h₂.trans (map_zero _).symm)
    exact Ideal.Quotient.eq_zero_iff_mem.mp h₃

omit [Fact (Nat.Prime ℓ₀)] [NumberField K₀] in
/-- If `Q` lies over `P`, then rational-prime membership in `P` transports to
the same rational-prime membership in `Q`. -/
theorem natCast_mem_of_under_eq
    {R' : Type w} [Field R'] [NumberField R'] [Algebra K₀ R']
    (P : Ideal (𝓞 K₀)) (Q : Ideal (𝓞 R'))
    (h_lies : Q.under (𝓞 K₀) = P)
    (hℓ_in_P : (ℓ₀ : 𝓞 K₀) ∈ P) :
    (ℓ₀ : 𝓞 R') ∈ Q := by
  have hℓ_in_under : (ℓ₀ : 𝓞 K₀) ∈ Q.under (𝓞 K₀) := by
    simpa [h_lies] using hℓ_in_P
  rw [Ideal.under, Ideal.mem_comap] at hℓ_in_under
  simpa using hℓ_in_under

/-! ### Stage 4 — Canonical K-alg-compat splitting iso under residue degree 1

When `Q.under (𝓞 K) = P` and the canonical induced ring hom
`(𝓞 K ⧸ P) →+* (𝓞 R' ⧸ Q)` is surjective (the `f(Q/P) = 1` condition),
we can construct the canonical iso `(𝓞 R' ⧸ Q) ≃+* (𝓞 K ⧸ P)`. This
iso satisfies `IsKAlgebraCompatibleSplittingIso` automatically. -/

/-- **The canonical induced ring hom from `𝓞 K ⧸ P` to `𝓞 R' ⧸ Q`** when
`Q.under (𝓞 K) = P`. Built via `Ideal.quotientMap` from `algebraMap`. -/
noncomputable def canonicalQuotientMap
    {R' : Type w} [Field R'] [NumberField R'] [Algebra K₀ R']
    (P : Ideal (𝓞 K₀)) (Q : Ideal (𝓞 R'))
    (h_lies : Q.under (𝓞 K₀) = P) :
    (𝓞 K₀ ⧸ P) →+* (𝓞 R' ⧸ Q) :=
  Ideal.quotientMap Q (algebraMap (𝓞 K₀) (𝓞 R')) (le_of_eq h_lies.symm)

omit [NumberField K₀] in
/-- The canonical map sends the equivalence class of `x` to that of
`algebraMap x`. -/
@[simp] theorem canonicalQuotientMap_mk
    {R' : Type w} [Field R'] [NumberField R'] [Algebra K₀ R']
    (P : Ideal (𝓞 K₀)) (Q : Ideal (𝓞 R'))
    (h_lies : Q.under (𝓞 K₀) = P) (x : 𝓞 K₀) :
    canonicalQuotientMap P Q h_lies ((Ideal.Quotient.mk P) x) =
      (Ideal.Quotient.mk Q) (algebraMap (𝓞 K₀) (𝓞 R') x) :=
  Ideal.quotientMap_mk

omit [NumberField K₀] in
/-- Residue degree one gives surjectivity of the canonical quotient map
`𝓞 K / P → 𝓞 R' / Q`. This is the standard split-residue-field condition
needed by `canonicalSplittingIso`. -/
theorem canonicalQuotientMap_surjective_of_inertiaDeg_eq_one
    {R' : Type w} [Field R'] [NumberField R'] [Algebra K₀ R']
    (P : Ideal (𝓞 K₀)) [P.IsMaximal] (Q : Ideal (𝓞 R')) [Q.IsPrime]
    (h_lies : Q.under (𝓞 K₀) = P)
    (h_inertia : P.inertiaDeg Q = 1) :
    Function.Surjective (canonicalQuotientMap P Q h_lies) := by
  letI : Q.LiesOver P := ⟨h_lies.symm⟩
  letI : Algebra (𝓞 K₀ ⧸ P) (𝓞 R' ⧸ Q) :=
    Ideal.Quotient.algebraQuotientOfLEComap (le_of_eq h_lies.symm)
  letI : Field (𝓞 K₀ ⧸ P) := Ideal.Quotient.field P
  have hfin :
      Module.finrank (𝓞 K₀ ⧸ P) (𝓞 R' ⧸ Q) = 1 := by
    simpa [Ideal.inertiaDeg_algebraMap] using h_inertia
  have hQ_ne_top : Q ≠ ⊤ :=
    Ideal.IsPrime.ne_top (I := Q) inferInstance
  haveI : Nontrivial (𝓞 R' ⧸ Q) :=
    Ideal.Quotient.nontrivial_iff.mpr hQ_ne_top
  have hspan :
      ∀ y : 𝓞 R' ⧸ Q, ∃ c : 𝓞 K₀ ⧸ P,
        c • (1 : 𝓞 R' ⧸ Q) = y :=
    (finrank_eq_one_iff_of_nonzero'
      (K := 𝓞 K₀ ⧸ P) (V := 𝓞 R' ⧸ Q)
      (1 : 𝓞 R' ⧸ Q) one_ne_zero).mp hfin
  intro y
  obtain ⟨c, hc⟩ := hspan y
  refine ⟨c, ?_⟩
  change algebraMap (𝓞 K₀ ⧸ P) (𝓞 R' ⧸ Q) c = y
  simpa [Algebra.smul_def] using hc

/-- **Canonical splitting iso under residue degree 1**: when `Q.under = P`
and the canonical map is surjective, build the iso
`(𝓞 R' ⧸ Q) ≃+* (𝓞 K ⧸ P)`. -/
noncomputable def canonicalSplittingIso
    {R' : Type w} [Field R'] [NumberField R'] [Algebra K₀ R']
    (P : Ideal (𝓞 K₀)) [P.IsMaximal] (Q : Ideal (𝓞 R')) [Q.IsPrime]
    (h_lies : Q.under (𝓞 K₀) = P)
    (h_surj : Function.Surjective (canonicalQuotientMap P Q h_lies)) :
    (𝓞 R' ⧸ Q) ≃+* (𝓞 K₀ ⧸ P) :=
  (RingEquiv.ofBijective (canonicalQuotientMap P Q h_lies)
    ⟨Ideal.quotientMap_injective' (le_of_eq h_lies), h_surj⟩).symm

omit [NumberField K₀] in
/-- The canonical splitting iso satisfies `IsKAlgebraCompatibleSplittingIso`. -/
theorem canonicalSplittingIso_isKAlgebraCompatible
    {R' : Type w} [Field R'] [NumberField R'] [Algebra K₀ R']
    (P : Ideal (𝓞 K₀)) [P.IsMaximal] (Q : Ideal (𝓞 R')) [Q.IsPrime]
    (h_lies : Q.under (𝓞 K₀) = P)
    (h_surj : Function.Surjective (canonicalQuotientMap P Q h_lies)) :
    IsKAlgebraCompatibleSplittingIso Q P
      (canonicalSplittingIso P Q h_lies h_surj) := by
  intro x
  -- iso = (RingEquiv.ofBijective canonicalQuotientMap _).symm
  -- iso (Quotient.mk Q (algebraMap x)) = Quotient.mk P x
  -- ⟺ Quotient.mk Q (algebraMap x) = (canonicalQuotientMap) (Quotient.mk P x)
  -- and the RHS = Quotient.mk Q (algebraMap x) by canonicalQuotientMap_mk.
  unfold canonicalSplittingIso
  apply (RingEquiv.ofBijective (canonicalQuotientMap P Q h_lies) _).injective
  rw [RingEquiv.apply_symm_apply]
  exact (canonicalQuotientMap_mk P Q h_lies x).symm

/-- **Stage 4 / `zeta_k`**: a primitive `p`-th root of unity in
`(𝓞 K ⧸ P)ˣ` for the bundle, namely `canonicalResidueZetaP P`. -/
noncomputable def zeta_k_residueField
    (P : Ideal (𝓞 K₀)) [_hP_max : P.IsMaximal]
    (_hP_ne_bot : P ≠ ⊥)
    (_hp_notin_P : (p₀ : 𝓞 K₀) ∉ P) :
    haveI : NeZero p₀ := ⟨(Fact.out : p₀.Prime).ne_zero⟩
    letI : Field (𝓞 K₀ ⧸ P) := Ideal.Quotient.field P
    (𝓞 K₀ ⧸ P)ˣ :=
  haveI : NeZero p₀ := ⟨(Fact.out : p₀.Prime).ne_zero⟩
  BernoulliRegular.Furtwaengler.canonicalResidueZetaP (p := p₀) (K := K₀) P

omit [IsCyclotomicExtension {p₀} ℚ K₀] in
/-- **Stage 4 / `zeta_k`** is a primitive `p`-th root. -/
theorem zeta_k_residueField_isPrimitiveRoot [IsCyclotomicExtension {p₀} ℚ K₀]
    (P : Ideal (𝓞 K₀)) [hP_max : P.IsMaximal]
    (hP_ne_bot : P ≠ ⊥)
    (hp_notin_P : (p₀ : 𝓞 K₀) ∉ P) :
    haveI : NeZero p₀ := ⟨(Fact.out : p₀.Prime).ne_zero⟩
    letI : Field (𝓞 K₀ ⧸ P) := Ideal.Quotient.field P
    IsPrimitiveRoot (zeta_k_residueField P hP_ne_bot hp_notin_P) p₀ := by
  haveI : NeZero p₀ := ⟨(Fact.out : p₀.Prime).ne_zero⟩
  letI : Field (𝓞 K₀ ⧸ P) := Ideal.Quotient.field P
  haveI : P.IsPrime := hP_max.isPrime
  exact BernoulliRegular.Furtwaengler.canonicalResidueZetaP_isPrimitiveRoot
    hP_ne_bot hp_notin_P

omit [IsCyclotomicExtension {p₀} ℚ K₀] in
/-- **Stage 4 / `hdiv`**: For a maximal `P ⊂ 𝓞 K` with `(p : 𝓞 K) ∉ P`
(so `μ_p ⊂ 𝓞 K` injects into `(𝓞 K ⧸ P)ˣ`), `p ∣ #(𝓞 K ⧸ P) - 1`.

This is the bundle's `hdiv` field, derived from
`BernoulliRegular.canonicalResidueZetaP` of order exactly `p`. -/
theorem p_dvd_card_residueField_sub_one [IsCyclotomicExtension {p₀} ℚ K₀]
    (P : Ideal (𝓞 K₀)) [hP_max : P.IsMaximal]
    (hP_ne_bot : P ≠ ⊥)
    (hp_notin_P : (p₀ : 𝓞 K₀) ∉ P) :
    p₀ ∣ Fintype.card (𝓞 K₀ ⧸ P) - 1 := by
  classical
  letI : Field (𝓞 K₀ ⧸ P) := Ideal.Quotient.field P
  haveI : NeZero p₀ := ⟨(Fact.out : p₀.Prime).ne_zero⟩
  haveI : P.IsPrime := hP_max.isPrime
  have horder :
      orderOf
        (BernoulliRegular.Furtwaengler.canonicalResidueZetaP (p := p₀) (K := K₀) P) =
        p₀ :=
    BernoulliRegular.Furtwaengler.canonicalResidueZetaP_orderOf_eq
      (p := p₀) (K := K₀) hP_ne_bot hp_notin_P
  rw [← horder]
  simpa [Fintype.card_units] using
    (orderOf_dvd_card
      (x := BernoulliRegular.Furtwaengler.canonicalResidueZetaP (p := p₀) (K := K₀) P))

end CyclotomicLocalSetup

/-! ## Step 2: applying the abstract Stickelberger theorems

Given a `ConcreteStickelbergerSetup S`, the bundle's `gaussSumInt_mem_Q`
gives `g(χ_q)^p ∈ Q^p` directly. Here we package it for the c.1 chain. -/

section Step2

variable {ℓ p : ℕ} [Fact ℓ.Prime] [Fact p.Prime]
variable {k : Type u} [Field k] [Fintype k]
variable {K : Type v} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
variable {R' : Type w} [Field R'] [NumberField R'] [Algebra K R']
  [IsScalarTower ℚ K R'] [IsCyclotomicExtension {p, ℓ} ℚ R']

variable (S : ConcreteStickelbergerSetup ℓ p k K R')

/-- **Step 2: Stickelberger valuation lower bound at Q.**
For any `1 ≤ a ≤ p-1`, `(g(χ_q^a))^p ∈ Q^p`. -/
theorem gaussSumInt_pow_p_mem_Q_pow
    {a : ℕ} (ha₁ : 1 ≤ a) (ha₂ : a ≤ p - 1) :
    S.gaussSumInt a ^ p ∈ S.Q ^ p :=
  S.gaussSumInt_pow_mem_Q_pow ha₁ ha₂

end Step2

/-! ## Step 3: Galois descent to 𝓞 K

Given the bundle's `S.gaussSumInt a ^ p ∈ S.Q ^ p` for `Q ⊂ 𝓞 R'`,
we use Galois descent of valuations to express the corresponding
ideal-membership in `𝓞 K` at the prime `q = Q.under (𝓞 K)`.

The descent: ramification of `Q` over `q = Q ∩ 𝓞 K` for the cyclotomic
extension `K → R' = K(ζ_ℓ)` is `ℓ - 1` (totally ramified above the
prime ℓ via `ζ_ℓ - 1`). For `x ∈ 𝓞 K`, `v_q(x) = v_Q(x) / (ℓ - 1)`. -/

section Step3

variable {ℓ p : ℕ} [Fact ℓ.Prime] [Fact p.Prime]
variable {K : Type v} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

omit [NumberField K] in
/-- **Step 3: pull the prime back to 𝓞 K.**
For `Q ⊂ 𝓞 R'` and the algebra map `𝓞 K →+* 𝓞 R'`, the prime ideal
`Q.under (𝓞 K)` is a prime of `𝓞 K` lying above `(ℓ : ℤ)`. -/
theorem Q_under_isPrime {R' : Type w} [Field R'] [NumberField R'] [Algebra K R']
    (Q : Ideal (𝓞 R')) [Q.IsPrime] :
    (Q.under (𝓞 K)).IsPrime :=
  Ideal.IsPrime.under (𝓞 K) (P := Q)

omit [Fact (Nat.Prime ℓ)] [NumberField K] in
/-- The pulled-back prime contains ℓ. -/
theorem Q_under_contains_ell {R' : Type w} [Field R'] [NumberField R'] [Algebra K R']
    [IsScalarTower ℤ (𝓞 K) (𝓞 R')]
    (Q : Ideal (𝓞 R')) [Q.IsPrime] (hQ : (ℓ : 𝓞 R') ∈ Q) :
    (ℓ : 𝓞 K) ∈ Q.under (𝓞 K) := by
  rw [show (Q.under (𝓞 K)) = Ideal.comap (algebraMap (𝓞 K) (𝓞 R')) Q from rfl]
  rw [Ideal.mem_comap]
  rw [show (algebraMap (𝓞 K) (𝓞 R') (ℓ : 𝓞 K)) = (ℓ : 𝓞 R') from by push_cast; rfl]
  exact hQ

/-- The pulled-back prime is non-bot. -/
theorem Q_under_ne_bot
    {R' : Type w} [Field R'] [NumberField R'] [Algebra K R']
    [IsScalarTower ℤ (𝓞 K) (𝓞 R')]
    (Q : Ideal (𝓞 R')) [Q.IsPrime] (hQ : (ℓ : 𝓞 R') ∈ Q) :
    Q.under (𝓞 K) ≠ ⊥ := by
  intro hbot
  have h_in_under : (ℓ : 𝓞 K) ∈ Q.under (𝓞 K) :=
    Q_under_contains_ell Q hQ
  rw [hbot, Ideal.mem_bot] at h_in_under
  have : (ℓ : 𝓞 K) ≠ 0 := by exact_mod_cast (Fact.out : ℓ.Prime).ne_zero
  exact this h_in_under

omit [Fact p.Prime] [IsCyclotomicExtension {p} ℚ K] in
/-- The pulled-back prime is in the cyclotomic-conjugates orbit of any
prime above ℓ in `𝓞 K`. (Galois transitivity above a fixed rational
prime.) -/
theorem Q_under_mem_cyclotomicConjugates [Fact p.Prime] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type w} [Field R'] [NumberField R'] [Algebra K R']
    [IsScalarTower ℤ (𝓞 K) (𝓞 R')]
    {q : Ideal (𝓞 K)} [hq : q.IsPrime] (_hq_ne : q ≠ ⊥)
    (hq_above : q.under ℤ = Ideal.span ({(ℓ : ℤ)} : Set ℤ))
    (Q : Ideal (𝓞 R')) [Q.IsPrime] (hQ : (ℓ : 𝓞 R') ∈ Q) :
    haveI : (Q.under (𝓞 K)).IsPrime := Q_under_isPrime Q
    Q.under (𝓞 K) ∈ cyclotomicConjugates (p := p) (K := K) q := by
  haveI : (Q.under (𝓞 K)).IsPrime := Q_under_isPrime Q
  refine mem_cyclotomicConjugates_iff_under_eq.mpr ?_
  -- Goal: (Q.under (𝓞 K)).under ℤ = q.under ℤ.
  -- Both equal `(ℓ)` (Q.under (𝓞 K) lies above ℓ since (ℓ : 𝓞 K) ∈ it; q similarly).
  have h1 : (ℓ : ℤ) ∈ ((Q.under (𝓞 K)).under ℤ) := by
    rw [show (Q.under (𝓞 K)).under ℤ =
        Ideal.comap (algebraMap ℤ (𝓞 K)) (Q.under (𝓞 K)) from rfl]
    rw [Ideal.mem_comap]
    rw [show (algebraMap ℤ (𝓞 K) (ℓ : ℤ)) = (ℓ : 𝓞 K) from by push_cast; rfl]
    exact Q_under_contains_ell Q hQ
  -- Both Q.under (𝓞 K).under ℤ and q.under ℤ are non-zero primes of ℤ
  -- containing (ℓ); both must equal (ℓ).
  haveI : (Q.under (𝓞 K)).LiesOver ((Q.under (𝓞 K)).under ℤ) := ⟨rfl⟩
  have h_under_ne : (Q.under (𝓞 K)).under ℤ ≠ ⊥ := by
    -- (ℓ : ℤ) ≠ 0 and ∈ this ideal.
    intro hbot
    rw [hbot, Ideal.mem_bot] at h1
    have : (ℓ : ℤ) ≠ 0 := by exact_mod_cast (Fact.out : ℓ.Prime).ne_zero
    exact this h1
  haveI : ((Q.under (𝓞 K)).under ℤ).IsPrime := Ideal.IsPrime.under ℤ (P := Q.under (𝓞 K))
  haveI : ((Q.under (𝓞 K)).under ℤ).IsMaximal :=
    Ideal.IsPrime.isMaximal inferInstance h_under_ne
  haveI : (Ideal.span ({(ℓ : ℤ)} : Set ℤ)).IsPrime := by
    rw [Ideal.span_singleton_prime (by exact_mod_cast (Fact.out : ℓ.Prime).ne_zero)]
    exact Nat.prime_iff_prime_int.mp (Fact.out : ℓ.Prime)
  haveI : (Ideal.span ({(ℓ : ℤ)} : Set ℤ)).IsMaximal :=
    Ideal.IsPrime.isMaximal inferInstance (by
      rw [Ne, Ideal.span_singleton_eq_bot]
      exact_mod_cast (Fact.out : ℓ.Prime).ne_zero)
  -- Both are maximal primes of ℤ containing (ℓ). They equal (ℓ).
  -- (ℓ) ⊆ Q.under (𝓞 K).under ℤ since (ℓ : ℤ) ∈ that ideal.
  have h2 : Ideal.span ({(ℓ : ℤ)} : Set ℤ) ≤ (Q.under (𝓞 K)).under ℤ := by
    rw [Ideal.span_le]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    rw [hx]; exact h1
  -- Now both are maximal, so equal.
  have h3 : Ideal.span ({(ℓ : ℤ)} : Set ℤ) = (Q.under (𝓞 K)).under ℤ :=
    Ideal.IsMaximal.eq_of_le inferInstance
      (Ideal.IsMaximal.ne_top inferInstance)
      h2
  rw [← h3, hq_above]

end Step3

/-! ## Bundle-level wrappers

When a `ConcreteStickelbergerSetup S` is supplied, the prime `S.Q ⊂ 𝓞 R'`
above ℓ pulls back to a prime `q_K := S.Q.under (𝓞 K) ⊂ 𝓞 K` above ℓ.
We package the previous step-3 theorems as bundle accessors. -/

namespace ConcreteStickelbergerSetup

variable {ℓ p : ℕ} [Fact ℓ.Prime] [Fact p.Prime]
variable {k : Type u} [Field k] [Fintype k]
variable {K : Type v} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
variable {R' : Type w} [Field R'] [NumberField R'] [Algebra K R']
  [IsScalarTower ℚ K R'] [IsCyclotomicExtension {p, ℓ} ℚ R']
variable [IsScalarTower ℤ (𝓞 K) (𝓞 R')]

variable (S : ConcreteStickelbergerSetup ℓ p k K R')

/-! ### Structural cyclotomic facts on `K → R'`

`IsGalois ℚ R'` comes free from `IsCyclotomicExtension {p, ℓ} ℚ R'`.
By `IsGalois.tower_top_of_isGalois` and the scalar tower `ℚ → K → R'`,
we get `IsGalois K R'`. Similarly, `FiniteDimensional K R'` follows
from the global finite-dimensionality. These are stated as theorems
(not instances) since ℓ, p are ambient and don't appear in the
conclusion. -/

omit [IsScalarTower ℤ (𝓞 K) (𝓞 R')] in
theorem isGalois_K_R'_of_cyclotomic
    (_S : ConcreteStickelbergerSetup ℓ p k K R') : IsGalois K R' := by
  haveI : IsGalois ℚ R' :=
    IsCyclotomicExtension.isGalois ({p, ℓ} : Set ℕ) (K := ℚ) (L := R')
  exact IsGalois.tower_top_of_isGalois ℚ K R'

omit [IsScalarTower ℤ (𝓞 K) (𝓞 R')] in
theorem finiteDimensional_K_R'_of_cyclotomic
    (_S : ConcreteStickelbergerSetup ℓ p k K R') : FiniteDimensional K R' := by
  haveI : FiniteDimensional ℚ R' :=
    IsCyclotomicExtension.finiteDimensional (S := ({p, ℓ} : Set ℕ)) (K := ℚ) R'
  exact Module.Finite.of_restrictScalars_finite ℚ K R'

omit [IsScalarTower ℤ (𝓞 K) (𝓞 R')] in
/-- `FaithfulSMul (𝓞 K) (𝓞 R')` derived from the number-field structure
via `FaithfulSMul.of_field_isFractionRing`. -/
theorem faithfulSMul_OK_OR'_of_cyclotomic (_S : ConcreteStickelbergerSetup ℓ p k K R') :
    FaithfulSMul (𝓞 K) (𝓞 R') :=
  FaithfulSMul.of_field_isFractionRing (𝓞 K) (𝓞 R') K R'

/-- The descent prime in `𝓞 K`: `q_K := S.Q.under (𝓞 K)`. -/
noncomputable def descentPrime : Ideal (𝓞 K) := S.Q.under (𝓞 K)

omit [IsScalarTower ℤ (𝓞 K) (𝓞 R')] in
theorem descentPrime_isPrime : (S.descentPrime).IsPrime := haveI := S.hQ_prime
  Q_under_isPrime (K := K) S.Q

theorem descentPrime_contains_ell : (ℓ : 𝓞 K) ∈ S.descentPrime :=
  haveI := S.hQ_prime
  Q_under_contains_ell (K := K) (ℓ := ℓ) S.Q S.hQ

theorem descentPrime_ne_bot : S.descentPrime ≠ ⊥ :=
  haveI := S.hQ_prime
  Q_under_ne_bot (K := K) (ℓ := ℓ) S.Q S.hQ

/-- Bundle form of the cyclotomic-conjugates orbit membership: for any
prime `q' ⊂ 𝓞 K` above ℓ, `S.descentPrime` is a Galois-conjugate of `q'`. -/
theorem descentPrime_mem_cyclotomicConjugates
    {q' : Ideal (𝓞 K)} [hq' : q'.IsPrime] (hq'_ne : q' ≠ ⊥)
    (hq'_above : q'.under ℤ = Ideal.span ({(ℓ : ℤ)} : Set ℤ)) :
    haveI := S.descentPrime_isPrime
    S.descentPrime ∈ cyclotomicConjugates (p := p) (K := K) q' :=
  haveI := S.hQ_prime
  Q_under_mem_cyclotomicConjugates (K := K) (p := p) (ℓ := ℓ) hq'_ne hq'_above S.Q S.hQ

end ConcreteStickelbergerSetup
end Furtwaengler

end BernoulliRegular
