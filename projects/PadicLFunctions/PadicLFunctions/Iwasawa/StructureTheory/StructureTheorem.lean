import PadicLFunctions.Iwasawa.StructureTheory.PseudoIso
import Mathlib.RingTheory.PowerSeries.Ideal

/-!
# The structure theorem for finitely generated Λ-modules  (S13-S3)

Washington, *Introduction to Cyclotomic Fields*, Thm 13.12 (= RJW TeX 3637–3642,
stated there without proof): every finitely generated `Λ = 𝒪⟦T⟧`-module is
pseudo-isomorphic to a canonical sum of a free part and cyclic prime-power parts.

This is the one genuinely deep build of Stage S.  `Λ` is **not** a PID (it has
Krull dimension `2`), so mathlib's PID structure theorem (`Module.equiv_directSum_of_isTorsion`)
does *not* apply directly.  The standard proof — decomposed **at execution** (board
ticket S13-S3 is a cluster) — runs:

* **S3a**: `Λ` is a Noetherian, integrally closed (Krull) regular local domain of
  dimension `2`, hence a UFD.  (mathlib `PowerSeries` over a complete DVR.)
* **S3b**: each height-one prime `𝔭 ⊂ Λ` localises to a DVR `Λ_𝔭` (hence a PID).
* **S3c**: over each `Λ_𝔭`, mathlib's `Module.equiv_directSum_of_isTorsion` gives
  the elementary divisors (the PID structure theorem — *reuse*).
* **S3d**: the pseudo-isomorphism gluing over the finite support of height-one
  primes; the finite kernel/cokernel is the pseudo-null discrepancy.  **This is the
  genuinely new content** — `Λ`-modules are not `⊕`-decomposable on the nose,
  unlike over a PID.

## Main declarations

* `Iwasawa.fg_pseudoIso_canonical`: the structure theorem in clean prime-power
  form — `M ~ Λ^r × ⨁ Λ/(gᵢ^eᵢ)` with each `gᵢ` prime.
* `Iwasawa.fg_pseudoIso_washington`: the refined Washington normal form, separating
  the uniformiser-power factors `Λ/(ϖ^nᵢ)` (the μ-part) from the
  distinguished-irreducible-power factors `Λ/(fⱼ^mⱼ)` (the λ-part), via Weierstrass
  preparation (S13-S1).  This is RJW TeX 3637–3642 / Washington Thm 13.12 verbatim.
* `Iwasawa.iwasawaAlgebra_isNoetherianRing`: foundation stub S3a.
-/

noncomputable section

open DirectSum

namespace Iwasawa

variable (𝒪 : Type*) [CommRing 𝒪]

local notation "Λ" => IwasawaAlgebra 𝒪

/-- **S3a (foundation)**: the Iwasawa algebra `Λ = 𝒪⟦T⟧` is a Noetherian ring (when
`𝒪` is).  Part of the ring-theory input to the structure theorem (`Λ` is in fact a
2-dimensional regular local UFD when `𝒪` is a complete DVR). -/
theorem iwasawaAlgebra_isNoetherianRing [IsNoetherianRing 𝒪] :
    IsNoetherianRing (IwasawaAlgebra 𝒪) :=
  inferInstance

/-- **The structure theorem (clean form), S13-S3 / Washington Thm 13.12.**
Every finitely generated `Λ`-module `M` is pseudo-isomorphic to `Λ^r ⊕ ⨁ᵢ Λ/(gᵢ^eᵢ)`
for a free rank `r` and finitely many cyclic prime-power quotients (`gᵢ` prime in
`Λ`).  For a *torsion* module `r = 0`.  (RJW TeX 3637–3642.) -/
theorem fg_pseudoIso_canonical
    (M : Type*) [AddCommGroup M] [Module (IwasawaAlgebra 𝒪) M]
    [Module.Finite (IwasawaAlgebra 𝒪) M] :
    ∃ (r k : ℕ) (g : Fin k → IwasawaAlgebra 𝒪) (e : Fin k → ℕ),
      (∀ i, Prime (g i)) ∧
      IsPseudoIso 𝒪 M
        ((Fin r → IwasawaAlgebra 𝒪) ×
          ⨁ i : Fin k, IwasawaAlgebra 𝒪 ⧸ Ideal.span {g i ^ e i}) := by
  sorry

variable [IsLocalRing 𝒪]

/-- **The structure theorem (Washington normal form), S13-S3.**
The refinement of `fg_pseudoIso_canonical` via Weierstrass preparation (S13-S1):
every finitely generated `Λ`-module is pseudo-isomorphic to
`Λ^r ⊕ ⨁ᵢ Λ/(ϖ^nᵢ) ⊕ ⨁ⱼ Λ/(fⱼ^mⱼ)`, where `ϖ` is a uniformiser of `𝒪` (the μ-part)
and the `fⱼ` are distinguished irreducible polynomials (the λ-part).  This is RJW
TeX 3637–3642 / Washington, *Cyclotomic Fields*, Thm 13.12, verbatim. -/
theorem fg_pseudoIso_washington (ϖ : 𝒪) (hϖ : Irreducible ϖ)
    (M : Type*) [AddCommGroup M] [Module (IwasawaAlgebra 𝒪) M]
    [Module.Finite (IwasawaAlgebra 𝒪) M] :
    ∃ (r s t : ℕ) (n : Fin s → ℕ) (f : Fin t → Polynomial 𝒪) (m : Fin t → ℕ),
      (∀ j, IsDistinguished 𝒪 (f j) ∧ Irreducible (f j)) ∧
      IsPseudoIso 𝒪 M
        ((Fin r → IwasawaAlgebra 𝒪) ×
          (⨁ i : Fin s, IwasawaAlgebra 𝒪 ⧸
            Ideal.span {(algebraMap 𝒪 (IwasawaAlgebra 𝒪) ϖ) ^ n i}) ×
          (⨁ j : Fin t, IwasawaAlgebra 𝒪 ⧸
            Ideal.span {((f j : IwasawaAlgebra 𝒪)) ^ m j})) := by
  sorry

end Iwasawa
