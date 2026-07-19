/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.EllipticCurve.InvariantDifferential
import ModularCurves.ForMathlib.PicSubsingletonFree

/-!
# Over a semilocal base the `ω` line bundle has a global basis

This file is the project-side application of the ring-level heart
`ModularCurves.ForMathlib.PicSubsingletonFree` to the invariant-differential line bundle
`ω_{E/S}` of `EllipticCurve/InvariantDifferential.lean`. It is the mouth-core prerequisite
(i) flagged in `Moduli/EngineDescent.lean` (`exists_localModel_core_at`, Stage 3):

> `Nonempty (OmegaBasis G_L)` from `Subsingleton (Pic L)` (the `ω`-line-bundle ↔ ring-Pic
> bridge over the affine `Spec L`).

## The set-up

For `G : EllipticCurveGeom S`, recall (`InvariantDifferential.lean`):

* `omegaCocycle G : Scheme.UnitCocycle S` — the Weierstrass-atlas transition cocycle;
* `(omegaCocycle G).sections ⊤` — the `Γ(S, ⊤)`-module of **global sections** of `ω_{E/S}`
  (compatible families of chart coordinates), an `AddCommGroup` + `Module Γ(S, ⊤)`;
* `(omegaCocycle G).IsBasis b` — `b` is a **nowhere-vanishing generator** (a unit in every
  chart), and `OmegaBasis G = {b // (omegaCocycle G).IsBasis b}` is the type of such global
  bases.

So `Nonempty (OmegaBasis G)` says the line bundle `ω_{E/S}` is **globally trivial**.

## What is proved here (sorry-free)

* `Module.free_of_finite_maximalSpectrum`, `Module.nonempty_basis_fin_one_of_finite_maximalSpectrum`
  — the semilocal specialisation of `PicSubsingletonFree`: over a ring `R` with finite maximal
  spectrum (a **semilocal** ring), every invertible `R`-module is free with a rank-one basis.
  Pure repackaging of mathlib's `[Finite (MaximalSpectrum R)] : Subsingleton (Pic R)` with the
  wrappers of `PicSubsingletonFree`.

* `OmegaBasis.linearEquiv`, `module_invertible_of_omegaBasis`, `module_free_of_omegaBasis`,
  `OmegaBasis.basisFinOne` — the **converse / necessity** direction, done in full: an
  `OmegaBasis` makes `(omegaCocycle G).sections ⊤` free of rank one and
  `Module.Invertible Γ(S, ⊤)`, via the torsor lemmas `smul_left_injective` /
  `exists_unique_smul_eq`. This confirms `Module.Invertible` is exactly the right module-level
  notion for the `ω` bundle: it is a *consequence* of a global basis, and — over an affine base —
  it is also equivalent to invertibility of the sheaf.

* `nonempty_omegaBasis_of_finite_maximalSpectrum` — the **forward target**, assembled from the
  semilocal ring bridge. The Picard-triviality half (`Finite (MaximalSpectrum) ⟹ Module.Free`)
  is discharged here; the two genuinely affine-geometric inputs are taken as hypotheses:
  `hInv` (`sections ⊤` is `Module.Invertible`) and `hTriv` (a free section module has a
  trivialising global section). Both are instances of the **affine `QCoh ≃ Modules` correspondence
  over `Spec L`** — see the module docstring's "Missing fact" note and `EngineDescent.lean`.

* `nonempty_omegaBasis_of_subsingleton_pic_bridge` — the coarse form matching the board verbatim:
  it reduces `Nonempty (OmegaBasis G)` to a single `Subsingleton (Pic Γ(S, ⊤)) → Nonempty …`
  bridge, supplying the `Subsingleton (Pic)` from the semilocal instance.

## Missing fact (the boarded residual, NOT closed here)

The genuinely open input is the **affine trivialisation bridge**: for `S` affine, the invertible
sheaf `ω_{E/S}` has global sections `(omegaCocycle G).sections ⊤` that form an *invertible*
`Γ(S, ⊤)`-module, and a free such module has a nowhere-vanishing (`IsBasis`) global section. Both
are the affine equivalence `QCoh(Spec R) ≃ R-Mod` restricted to invertibles (mathlib's own
`RingTheory/PicardGroup.lean` records this as a TODO, *"Connect to invertible sheaves on
`Spec R`"*). It is **false** without affineness (e.g. `𝒪(p)` on an elliptic curve has a free
rank-one global-section module over the field `Γ(𝒪) = k` yet no nowhere-vanishing global section),
so it cannot be discharged from `Module.Invertible` + `Finite (MaximalSpectrum)` alone. It is
boarded as residual (i) of `exists_localModel_core_at`.
-/

universe u

open AlgebraicGeometry CategoryTheory
open CommRing (Pic)

/-! ### Ring-level: a semilocal ring has trivial Picard group, so invertible ⟹ free -/

namespace Module

variable (R : Type*) [CommRing R] (M : Type*) [AddCommGroup M] [Module R M]

/-- **Semilocal ⟹ invertible modules are free.** Over a ring `R` with finite maximal spectrum
(a semilocal ring; mathlib's `[Finite (MaximalSpectrum R)] : Subsingleton (Pic R)`), every
invertible `R`-module is free. Thin specialisation of
`Module.free_of_subsingleton_pic`. -/
theorem free_of_finite_maximalSpectrum [Finite (MaximalSpectrum R)] [Module.Invertible R M] :
    Module.Free R M :=
  Module.free_of_subsingleton_pic R M inferInstance

/-- **Semilocal ⟹ invertible modules are isomorphic to the ring.** -/
theorem nonempty_linearEquiv_self_of_finite_maximalSpectrum [Finite (MaximalSpectrum R)]
    [Module.Invertible R M] : Nonempty (M ≃ₗ[R] R) :=
  Module.nonempty_linearEquiv_self_of_subsingleton_pic R M inferInstance

/-- **Semilocal ⟹ invertible modules have a rank-one basis.** The concrete `Basis (Fin 1) R M`
form — a single global basis vector — that the `ω`-triviality mouth-core needs. -/
theorem nonempty_basis_fin_one_of_finite_maximalSpectrum [Finite (MaximalSpectrum R)]
    [Module.Invertible R M] : Nonempty (Basis (Fin 1) R M) :=
  Module.nonempty_basis_fin_one_of_subsingleton_pic R M inferInstance

end Module

namespace ModularCurves

open Scheme

variable {S : Scheme.{u}}

/-! ### Converse (necessity): an `OmegaBasis` makes the section module invertible and free

These are proved in full. They show that `Module.Invertible Γ(S, ⊤) ((omegaCocycle G).sections ⊤)`
is the correct module-level shadow of a global basis of `ω_{E/S}`: a global `OmegaBasis` trivialises
the section module as a free rank-one — hence invertible — module. -/

section Converse

variable {G : EllipticCurveGeom S}

/-- The linear equivalence `Γ(S, ⊤) ≃ₗ (omegaCocycle G).sections ⊤`, `r ↦ r • b`, attached to a
global basis `b` of `ω_{E/S}`. Injectivity is freeness of the torsor action
(`UnitCocycle.smul_left_injective`), surjectivity is its transitivity
(`UnitCocycle.exists_unique_smul_eq`). -/
noncomputable def OmegaBasis.linearEquiv (b : OmegaBasis G) :
    Γ(S, ⊤) ≃ₗ[Γ(S, ⊤)] (omegaCocycle G).sections ⊤ :=
  LinearEquiv.ofBijective (LinearMap.toSpanSingleton Γ(S, ⊤) _ b.1)
    ⟨fun _ _ h => (omegaCocycle G).smul_left_injective b.2 h,
     fun m => ((omegaCocycle G).exists_unique_smul_eq b.2 m).exists⟩

@[simp] theorem OmegaBasis.linearEquiv_apply (b : OmegaBasis G) (r : Γ(S, ⊤)) :
    b.linearEquiv r = r • b.1 :=
  rfl

/-- **The section module of `ω_{E/S}` is `Module.Invertible` whenever a global basis exists.**
(The converse of what the mouth-core needs, but it pins down `Module.Invertible` as the correct
notion: a free rank-one module is invertible.) -/
theorem module_invertible_of_omegaBasis (b : OmegaBasis G) :
    Module.Invertible Γ(S, ⊤) ((omegaCocycle G).sections ⊤) :=
  Module.Invertible.congr b.linearEquiv

/-- The section module of `ω_{E/S}` is free whenever a global basis exists. -/
theorem module_free_of_omegaBasis (b : OmegaBasis G) :
    Module.Free Γ(S, ⊤) ((omegaCocycle G).sections ⊤) :=
  Module.Free.of_equiv b.linearEquiv

/-- The concrete rank-one `Γ(S, ⊤)`-basis of the section module attached to a global basis. -/
noncomputable def OmegaBasis.basisFinOne (b : OmegaBasis G) :
    Module.Basis (Fin 1) Γ(S, ⊤) ((omegaCocycle G).sections ⊤) :=
  (Module.Basis.singleton (Fin 1) Γ(S, ⊤)).map b.linearEquiv

end Converse

/-! ### Forward target: semilocal base ⟹ `Nonempty (OmegaBasis G)`

The ring-theoretic Picard-triviality half is discharged from `Finite (MaximalSpectrum Γ(S, ⊤))`.
The two remaining inputs `hInv`/`hTriv` are the affine `QCoh ≃ Modules` bridge — see the module
docstring and `EngineDescent.lean` residual (i). -/

/-- **Semilocal base ⟹ the `ω` line bundle has a global basis**, modulo the affine trivialisation
bridge. Over a base whose global-section ring `Γ(S, ⊤)` is semilocal
(`Finite (MaximalSpectrum Γ(S, ⊤))`):

* `hInv` — the section module `(omegaCocycle G).sections ⊤` is `Module.Invertible Γ(S, ⊤)` (true for
  affine `S`: an invertible sheaf has an invertible global-section module);
* `hTriv` — a *free* section module has a trivialising (`IsBasis`) global section (true for affine
  `S`: `QCoh` triviality of the sheaf);

then `ω_{E/S}` has a global basis. The Picard-triviality step `Finite (MaximalSpectrum) ⟹ free`
is discharged internally via `Module.free_of_finite_maximalSpectrum`. Both `hInv` and `hTriv` are
the affine `QCoh ≃ Modules` correspondence over `Spec L` (boarded residual (i)). -/
theorem nonempty_omegaBasis_of_finite_maximalSpectrum (G : EllipticCurveGeom S)
    [Finite (MaximalSpectrum Γ(S, ⊤))]
    (hInv : Module.Invertible Γ(S, ⊤) ((omegaCocycle G).sections ⊤))
    (hTriv : Module.Free Γ(S, ⊤) ((omegaCocycle G).sections ⊤) →
        ∃ b : (omegaCocycle G).sections ⊤, (omegaCocycle G).IsBasis b) :
    Nonempty (OmegaBasis G) := by
  haveI := hInv
  obtain ⟨b, hb⟩ := hTriv (Module.free_of_finite_maximalSpectrum Γ(S, ⊤) _)
  exact ⟨⟨b, hb⟩⟩

/-- **The board-verbatim reduction.** `Nonempty (OmegaBasis G)` follows from the single affine
bridge `Subsingleton (Pic Γ(S, ⊤)) → Nonempty (OmegaBasis G)` once the base is semilocal, because
`[Finite (MaximalSpectrum Γ(S, ⊤))]` supplies `Subsingleton (Pic Γ(S, ⊤))` (mathlib). This is the
exact shape of residual (i) in `exists_localModel_core_at`. -/
theorem nonempty_omegaBasis_of_subsingleton_pic_bridge (G : EllipticCurveGeom S)
    [Finite (MaximalSpectrum Γ(S, ⊤))]
    (hbridge : Subsingleton (Pic Γ(S, ⊤)) → Nonempty (OmegaBasis G)) :
    Nonempty (OmegaBasis G) :=
  hbridge inferInstance

end ModularCurves
