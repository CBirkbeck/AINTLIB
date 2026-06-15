module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.Stickelberger

/-!
# Stickelberger setup bundle (REF-18c2c1)

The remaining steps of REF-18c2c (q-adic valuation, Galois orbit, prime
factorisation, descent to `𝓞_K`) all share the same ambient data:

* a finite field `k` with `p ∣ #k − 1`,
* a target field `R'` containing both `μ_p` and a primitive additive
  character `ψ_q` on `k`,
* chosen primitive roots of unity in each.

This file packages that data as `StickelbergerSetup`, with accessors
for the residue character and Gauss sum specialised to the bundle.
Downstream sub-subtickets (c2-c5) consume the bundle directly so each
piece of the prime-ideal-level argument can refer to a single object
rather than carrying the same eight or nine implicit arguments.

The bundle is *minimal*: it carries only what the existing algebraic
core (the 22 theorems already proved in `Stickelberger.lean`) needs.
Specifically it requires `IsDomain R'` plus the chosen-root-of-unity
data; full `IsCyclotomicExtension {p, q} ℚ R'` typeclass instances are
*not* required at this layer — they will become relevant only when
REF-18c2c2 begins manipulating prime ideals of `𝓞_{R'}` and needs the
ring-of-integers structure.

## Main definitions

* `BernoulliRegular.Furtwaengler.StickelbergerSetup`: the bundle.
* `BernoulliRegular.Furtwaengler.StickelbergerSetup.residueChar`: the
  residue MulChar specialised to the bundle.
* `BernoulliRegular.Furtwaengler.StickelbergerSetup.gaussSum`: the
  residue Gauss sum specialised to the bundle.
* Accessor lemmas re-exporting REF-18c2c's algebraic core in
  bundle-aware form: `gaussSum_pow_p_eq_prod_jacobiSum`,
  `gaussSum_pow_p_isIntegral`, `gaussSum_pow_p_mem_closure`, etc.
-/

@[expose] public section

noncomputable section

namespace BernoulliRegular

namespace Furtwaengler

variable (p : ℕ) [Fact p.Prime]
variable (k : Type*) [Field k] [Fintype k]
variable (R' : Type*) [CommRing R'] [IsDomain R']

/-- The bundled data driving the Stickelberger prime factorisation argument:
a finite field `k`, a target domain `R'`, primitive `p`-th roots of unity in
both `kˣ` and `R'ˣ`, the divisibility `p ∣ #k − 1`, and a primitive additive
character `ψ_q : k → R'`. The residue character `χ_q` and its Gauss sum
`g(χ_q, ψ_q)` are then determined by the bundle. -/
structure StickelbergerSetup where
  /-- A primitive `p`-th root of unity in the residue field. -/
  zeta_q : kˣ
  /-- Witness of primitivity. -/
  hzeta_q : IsPrimitiveRoot zeta_q p
  /-- The cardinality compatibility condition: `p ∣ #k − 1`. -/
  hdiv : p ∣ Fintype.card k - 1
  /-- A primitive `p`-th root of unity in the target ring. -/
  zeta_R : R'ˣ
  /-- Witness of primitivity. -/
  hzeta_R : IsPrimitiveRoot zeta_R p
  /-- A non-trivial primitive additive character on the residue field. -/
  psi_q : AddChar k R'
  /-- Witness that `ψ_q` is primitive (so `gaussSum_mul_gaussSum_eq_card`
  applies). -/
  hpsi : psi_q.IsPrimitive

namespace StickelbergerSetup

variable {p k R'}
variable (S : StickelbergerSetup p k R')

/-- The residue `MulChar` specialised to the bundle. -/
def residueChar : MulChar k R' :=
  Furtwaengler.residueMulChar S.zeta_q S.hzeta_q S.hdiv S.zeta_R S.hzeta_R

/-- The residue Gauss sum specialised to the bundle. -/
def gaussSum : R' :=
  Furtwaengler.residueGaussSum S.zeta_q S.hzeta_q S.hdiv S.zeta_R S.hzeta_R S.psi_q

omit [IsDomain R'] in
/-- Bundle accessor: `χ_q^p = 1` as a `MulChar`. -/
theorem residueChar_pow_eq_one : S.residueChar ^ p = 1 :=
  Furtwaengler.residueMulChar_pow_eq_one_mulChar
    S.zeta_q S.hzeta_q S.hdiv S.zeta_R S.hzeta_R

omit [IsDomain R'] in
/-- Bundle accessor: `χ_q ≠ 1`. -/
theorem residueChar_ne_one : S.residueChar ≠ 1 :=
  Furtwaengler.residueMulChar_ne_one
    S.zeta_q S.hzeta_q S.hdiv S.zeta_R S.hzeta_R

/-- Bundle accessor: `orderOf χ_q = p`. -/
theorem orderOf_residueChar : orderOf S.residueChar = p :=
  Furtwaengler.orderOf_residueMulChar
    S.zeta_q S.hzeta_q S.hdiv S.zeta_R S.hzeta_R

/-- Bundle accessor: the basic norm relation
`g(χ_q, ψ_q) · g(χ_q⁻¹, ψ_q⁻¹) = #k`. -/
theorem gaussSum_mul_inv_eq_card :
    S.gaussSum * _root_.gaussSum S.residueChar⁻¹ S.psi_q⁻¹ = Fintype.card k :=
  Furtwaengler.residueGaussSum_mul_inv_eq_card
    S.zeta_q S.hzeta_q S.hdiv S.zeta_R S.hzeta_R S.hpsi S.residueChar_ne_one

/-- Bundle accessor: the Jacobi-sum chain identity
`g(χ_q)^p = χ_q(-1) · #k · ∏ J(χ_q, χ_q^i)`. -/
theorem gaussSum_pow_p_eq_prod_jacobiSum :
    S.gaussSum ^ p =
      S.residueChar (-1) * Fintype.card k *
        ∏ i ∈ Finset.Ico 1 (p - 1),
          jacobiSum S.residueChar (S.residueChar ^ i) :=
  Furtwaengler.residueGaussSum_pow_p_eq_prod_jacobiSum
    S.zeta_q S.hzeta_q S.hdiv S.zeta_R S.hzeta_R S.hpsi

/-- Bundle accessor: `g(χ_q)^p` lies in `Subring.closure {ζ_R}`. -/
theorem gaussSum_pow_p_mem_closure :
    S.gaussSum ^ p ∈ Subring.closure {((S.zeta_R : R'ˣ) : R')} :=
  Furtwaengler.residueGaussSum_pow_p_mem_closure
    S.zeta_q S.hzeta_q S.hdiv S.zeta_R S.hzeta_R S.hpsi

/-- Bundle accessor: `g(χ_q)^p` is integral over `ℤ`. -/
theorem gaussSum_pow_p_isIntegral :
    IsIntegral ℤ (S.gaussSum ^ p) :=
  Furtwaengler.residueGaussSum_pow_p_isIntegral
    S.zeta_q S.hzeta_q S.hdiv S.zeta_R S.hzeta_R S.hpsi

/-- Bundle accessor: ideal-form norm
`g(χ_q)^p · g(χ_q^{p-1})^p = (#k)^p`. -/
theorem gaussSum_pow_p_mul_pow_p_sub_one_eq_card_pow :
    S.gaussSum ^ p * (_root_.gaussSum (S.residueChar ^ (p - 1)) S.psi_q) ^ p =
      ((Fintype.card k : R')) ^ p :=
  Furtwaengler.residueGaussSum_pow_p_mul_pow_p_sub_one_eq_card_pow
    S.zeta_q S.hzeta_q S.hdiv S.zeta_R S.hzeta_R S.hpsi

/-- Bundle accessor: q-adic ideal containment (REF-18c2c2 abstract form).
If `ψ_q ≡ 1 (mod I)` on `k`, then `g(χ_q) ∈ I`. -/
theorem gaussSum_mem_ideal {I : Ideal R'} (h : ∀ x : k, S.psi_q x - 1 ∈ I) :
    S.gaussSum ∈ I :=
  Furtwaengler.residueGaussSum_mem_ideal_of_psi_sub_one_mem
    S.zeta_q S.hzeta_q S.hdiv S.zeta_R S.hzeta_R h

omit [IsDomain R'] in
/-- Bundle accessor: Galois orbit of `g(χ_q)` (REF-18c2c3 abstract form).
For any ring hom `σ : R' →+* R'` sending `ζ_R ↦ ζ_R^a`,
`σ(g(χ_q, ψ_q)) = gaussSum (χ_q^a) (σ ∘ ψ_q)`. -/
theorem gaussSum_ringHomComp_pow_eq
    (σ : R' →+* R') (a : ℕ)
    (hσ : σ ((S.zeta_R : R'ˣ) : R') = ((S.zeta_R : R'ˣ) : R') ^ a) :
    σ S.gaussSum =
      _root_.gaussSum (S.residueChar ^ a) (σ.toMonoidHom.compAddChar S.psi_q) :=
  Furtwaengler.residueGaussSum_ringHomComp_pow_eq
    S.zeta_q S.hzeta_q S.hdiv S.zeta_R S.hzeta_R S.psi_q σ a hσ

/-- Bundle accessor: `g(χ_q)^n ∈ I^n` whenever `ψ_q(x) - 1 ∈ I` for all `x`
(REF-18c2c4 Phase A — raised q-adic containment). -/
theorem gaussSum_pow_mem_ideal_pow {I : Ideal R'}
    (h : ∀ x : k, S.psi_q x - 1 ∈ I) (n : ℕ) :
    S.gaussSum ^ n ∈ I ^ n :=
  Furtwaengler.residueGaussSum_pow_mem_ideal_pow
    S.zeta_q S.hzeta_q S.hdiv S.zeta_R S.hzeta_R h n

/-- Bundle accessor: support of `g(χ_q)^p` lies above `#k` (REF-18c2c4
Phase A — no extraneous prime factors). Any prime ideal of `R'` containing
`g(χ_q)^p` must contain `(#k : R')`, hence lies above the rational prime
under the residue field `k`. -/
theorem gaussSum_pow_p_support_above_card
    {P : Ideal R'} [P.IsPrime]
    (hgauss : S.gaussSum ^ p ∈ P) :
    ((Fintype.card k : R')) ∈ P :=
  Furtwaengler.residueGaussSum_pow_p_support_above_card
    S.zeta_q S.hzeta_q S.hdiv S.zeta_R S.hzeta_R S.hpsi hgauss

/-- Bundle accessor: `g(χ_q) ∈ Q` for any prime `Q` above `q` (REF-18c2c4
Phase B — concrete cyclotomic instantiation). When the additive character
has the trace-formula form `ψ_q(x) = ζ^{f(x)}` for some primitive `q`-th
root `ζ ∈ R'` and `(q : R') ∈ Q`, the residue Gauss sum lies in `Q`. -/
theorem gaussSum_mem_ideal_of_q_mem
    {q : ℕ} [Fact q.Prime]
    {ζ : R'} (hζ : IsPrimitiveRoot ζ q)
    (h_psi_pow : ∀ x : k, ∃ n : ℕ, S.psi_q x = ζ ^ n)
    {Q : Ideal R'} [Q.IsPrime] (hQ : (q : R') ∈ Q) :
    S.gaussSum ∈ Q :=
  Furtwaengler.residueGaussSum_mem_ideal_of_psi_pow_form
    S.zeta_q S.hzeta_q S.hdiv S.zeta_R S.hzeta_R hζ h_psi_pow hQ

/-- Bundle accessor: `g(χ_q)^n ∈ Q^n` for any prime `Q` above `q` (REF-18c2c4
Phase B — raised). -/
theorem gaussSum_pow_mem_ideal_pow_of_q_mem
    {q : ℕ} [Fact q.Prime]
    {ζ : R'} (hζ : IsPrimitiveRoot ζ q)
    (h_psi_pow : ∀ x : k, ∃ n : ℕ, S.psi_q x = ζ ^ n)
    {Q : Ideal R'} [Q.IsPrime] (hQ : (q : R') ∈ Q) (n : ℕ) :
    S.gaussSum ^ n ∈ Q ^ n :=
  Furtwaengler.residueGaussSum_pow_mem_ideal_pow_of_psi_pow_form
    S.zeta_q S.hzeta_q S.hdiv S.zeta_R S.hzeta_R hζ h_psi_pow hQ n

/-- Bundle accessor: `g(χ_q)^p` divides `(#k)^p` (REF-18c2c4 Phase A
divisibility precursor). -/
theorem gaussSum_pow_p_dvd_card_pow :
    S.gaussSum ^ p ∣ ((Fintype.card k : R')) ^ p :=
  Furtwaengler.residueGaussSum_pow_p_dvd_card_pow
    S.zeta_q S.hzeta_q S.hdiv S.zeta_R S.hzeta_R S.hpsi

/-- Bundle accessor: q-adic ord = 1 for `g(χ_q)` under non-degeneracy
(REF-18c2c4 Phase B+C synthesis). The conclusion `g ∈ Q ∧ g ∉ Q²` is
equivalent to `ord_Q(g) = 1` in a Dedekind context. -/
theorem gaussSum_qadic_ord_eq_one_under_nondeg
    {q : ℕ} [Fact q.Prime]
    {ζ : R'} (hζ : IsPrimitiveRoot ζ q)
    (f : k → ℕ) (hf : ∀ x : k, S.psi_q x = ζ ^ f x)
    {Q : Ideal R'} [Q.IsPrime] (hQ : (q : R') ∈ Q)
    (h_lead : (ζ - 1) * (∑ x, S.residueChar x * (f x : R')) ∉ Q ^ 2) :
    S.gaussSum ∈ Q ∧ S.gaussSum ∉ Q ^ 2 :=
  Furtwaengler.residueGaussSum_qadic_ord_eq_one_under_nondeg
    S.zeta_q S.hzeta_q S.hdiv S.zeta_R S.hzeta_R hζ f hf hQ h_lead

end StickelbergerSetup

end Furtwaengler

end BernoulliRegular
