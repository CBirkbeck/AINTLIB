import PadicLFunctions.IwasawaProof.Galois.Modules
import Mathlib.RingTheory.Nakayama

/-!
# Coinvariants and the Vandiver vanishing  (S13-G, G3 + G-VANDIVER)

The Iwasawa-theoretic core of the Vandiver-prime Main Conjecture (RJW §13.3).

* **G3 (bundled input)** — Washington *Cyclotomic Fields* Prop 13.22 (`(𝒴⁺_∞)_{Γ_n} ≅ 𝒴⁺_n`):
  the control theorem identifying `Γ`-coinvariants of `𝒴⁺_∞` with the finite-level class-group
  module `𝒴⁺_n`.  This is a classical Iwasawa result mathlib does not have; consistent with the
  project architecture (and the expert review 2026-06-18), it is bundled as a *cited input* in
  `VandiverData` — alongside a topological generator `γ−1` of the augmentation ideal of `Γ` and
  the finite generation of `𝒴⁺_∞`.

* **G-VANDIVER (PROVEN)** — RJW Cor Iw1(i): if `p` is a Vandiver prime (`𝒴⁺_1 = 0`) then
  `𝒴⁺_∞ = 0`.  Proof: the coinvariant iso gives `𝒴⁺_∞/(γ−1)𝒴⁺_∞ ≅ 𝒴⁺_1 = 0`, so
  `𝒴⁺_∞ = (γ−1)·𝒴⁺_∞`; since `𝒴⁺_∞` is f.g. and `γ−1` lies in the Jacobson radical of the local
  ring `Λ(𝒢⁺)`, **Nakayama** forces `𝒴⁺_∞ = 0`.

## Main declarations

* `Iwasawa.Galois.VandiverData`: the bundled control-theorem input (coinvariant iso + generator
  + finiteness) over the Galois module `𝒴⁺_∞`.
* `Iwasawa.Galois.VandiverData.yPlus_subsingleton`: the Vandiver vanishing `𝒴⁺_∞ = 0` (Nakayama).
-/

noncomputable section

namespace Iwasawa.Galois

open scoped Pointwise

variable (p : ℕ) [Fact p.Prime]
variable (YPlus : Type*) [AddCommGroup YPlus] [Module (LambdaGPlus p) YPlus]

/-- **Bundled control-theorem data** (G3 input, Washington Prop 13.22).  Records:
* `omega = γ − 1`, a topological generator of the augmentation ideal of `Γ` in `Λ(𝒢⁺)`, lying in
  the Jacobson radical of the local ring `Λ(𝒢⁺)`;
* `coinv`: the coinvariant isomorphism `𝒴⁺_∞/(γ−1)𝒴⁺_∞ ≃ 𝒴⁺_1` (control theorem at the bottom);
* `finite`: `𝒴⁺_∞` is finitely generated over `Λ(𝒢⁺)`.
These are exactly the classical Iwasawa inputs RJW cite at Cor Iw1. -/
structure VandiverData where
  /-- `γ − 1`, a topological generator of the `Γ`-augmentation ideal. -/
  omega : LambdaGPlus p
  /-- `γ − 1` lies in the Jacobson radical of the local ring `Λ(𝒢⁺)`. -/
  omega_mem_jacobson : Ideal.span {omega} ≤ Ideal.jacobson (⊥ : Ideal (LambdaGPlus p))
  /-- **control theorem** (Washington 13.22): the `Γ`-coinvariants of `𝒴⁺_∞` are `𝒴⁺_1`. -/
  coinv : (YPlus ⧸ (Ideal.span {omega} • (⊤ : Submodule (LambdaGPlus p) YPlus))) ≃+ YPlusFin p 1
  /-- `𝒴⁺_∞` is finitely generated over `Λ(𝒢⁺)`. -/
  finite : Module.Finite (LambdaGPlus p) YPlus

namespace VandiverData

variable {p YPlus}

/-- **The Vandiver vanishing** (RJW Cor Iw1(i), G-VANDIVER): if `p` is a Vandiver prime — i.e. the
`p`-part `𝒴⁺_1 = ℤ_p ⊗ Cl(F_1⁺)` of the level-`1` class group vanishes — then `𝒴⁺_∞ = 0`.

Proof: the control iso turns `𝒴⁺_1 = 0` into `𝒴⁺_∞/(γ−1)𝒴⁺_∞ = 0`, i.e. `⊤ = (γ−1)·⊤`; with
`𝒴⁺_∞` finitely generated and `γ−1` in the Jacobson radical, Nakayama gives `⊤ = ⊥`. -/
theorem yPlus_subsingleton (D : VandiverData p YPlus) (hv : Subsingleton (YPlusFin p 1)) :
    Subsingleton YPlus := by
  -- The coinvariant quotient is a subsingleton (transport along `coinv`).
  haveI : Subsingleton (YPlus ⧸ (Ideal.span {D.omega} • (⊤ : Submodule (LambdaGPlus p) YPlus))) :=
    D.coinv.toEquiv.subsingleton
  -- Hence `⊤ ≤ (span {ω}) • ⊤`.
  have htop : (⊤ : Submodule (LambdaGPlus p) YPlus)
      ≤ Ideal.span {D.omega} • (⊤ : Submodule (LambdaGPlus p) YPlus) := by
    rw [← Submodule.comap_subtype_eq_top, ← top_le_iff]
    intro x _
    have hq : Submodule.Quotient.mk
        (p := Ideal.span {D.omega} • (⊤ : Submodule (LambdaGPlus p) YPlus)) x = 0 :=
      Subsingleton.elim _ _
    rwa [Submodule.Quotient.mk_eq_zero] at hq
  -- Nakayama: `⊤` is f.g., `⊤ ≤ I • ⊤`, `I ≤ jacobson ⊥` ⟹ `⊤ = ⊥`.
  haveI := D.finite
  have hfg : (⊤ : Submodule (LambdaGPlus p) YPlus).FG := Module.Finite.fg_top
  have htb : (⊤ : Submodule (LambdaGPlus p) YPlus) = ⊥ :=
    Submodule.eq_bot_of_le_smul_of_le_jacobson_bot _ _ hfg htop D.omega_mem_jacobson
  refine ⟨fun a b => ?_⟩
  have ha : a ∈ (⊤ : Submodule (LambdaGPlus p) YPlus) := Submodule.mem_top
  have hb : b ∈ (⊤ : Submodule (LambdaGPlus p) YPlus) := Submodule.mem_top
  rw [htb, Submodule.mem_bot] at ha hb
  rw [ha, hb]

end VandiverData

end Iwasawa.Galois
