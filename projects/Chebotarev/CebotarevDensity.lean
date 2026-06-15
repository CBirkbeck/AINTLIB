module

public import CebotarevDensity.Density
public import CebotarevDensity.CyclotomicNormResidue
public import CebotarevDensity.ForMathlib.CharacterOrthogonality
public import CebotarevDensity.ForMathlib.IdealCongruenceCount
public import CebotarevDensity.ForMathlib.LatticePointCount
public import CebotarevDensity.ForMathlib.LogOneDivSubOne
public import CebotarevDensity.ForMathlib.NormLeOneLipschitz
public import CebotarevDensity.FixedFieldDensity
public import CebotarevDensity.Frobenius
public import CebotarevDensity.ZetaProduct
public import CebotarevDensity.Cyclotomic
public import CebotarevDensity.Abelian
public import CebotarevDensity.Main
public import CebotarevDensity.NumberFieldEulerProduct

/-!
# Chebotarev density theorem

A formalisation of the Chebotarev density theorem in conjugacy-class form
for a finite Galois extension of number fields.

The development follows Sharifi, *Algebraic Number Theory* §7.1–7.2, and
the appendix of Stevenhagen–Lenstra, *Chebotarëv and his density
theorem*; both are included as `docs/algnum.pdf` and `docs/cheb.pdf`.

## Module structure

* `Chebotarev.Density` — Dirichlet density of a set of prime ideals
* `Chebotarev.Frobenius` — decomposition / inertia groups, Frobenius
  element + conjugacy class
* `Chebotarev.ZetaProduct` — `ζ_L = ∏_χ L(χ,·)` for abelian `L/K`
* `Chebotarev.Cyclotomic` — Chebotarev cyclotomic case
* `Chebotarev.Abelian` — Chebotarev abelian case via cyclotomic
  crossing
* `Chebotarev.Main` — the main theorem and corollaries
* `Chebotarev.NumberFieldEulerProduct` — generic Euler-product
  infrastructure for `ζ_K`

## Main result

`Chebotarev.chebotarev_density` (in `Chebotarev.Main`).
-/
