#!/usr/bin/env python3
"""Assemble ModularCurves/EllipticCurve/AdditionLaw.lean from the CAS exports in this
directory (T-W7.0c-i increment 1). The .txt files are the source of record; this script
inserts them VERBATIM (no reflow) into the Lean template so that transcription is not a
trust step. Re-run after regenerating the exports with derive_law2.py.

Usage: python3 emit_addition_law.py   (from the repo root)
"""
import pathlib

D = pathlib.Path(__file__).resolve().parent
OUT = D.parent.parent / "ModularCurves" / "EllipticCurve" / "AdditionLaw.lean"


def raw(name: str) -> str:
    return (D / name).read_text().rstrip("\n")


NORM_ALL = "law_simp; ring1"


def minor(tag: str, lemma_name: str, lhs: str, rhs: str, cof_p: str, cof_q: str) -> str:
    return f"""/-- **(T-W7.0c(c3))** The `{tag}` minor of the two addition laws vanishes on the curve:
law 1 and law 2 are projectively proportional wherever both are defined. CAS-certified
cofactors (Y-first reduction; see `scripts/tw7-p1-bosma-lenstra/cof_M{tag}_P.txt`, `_Q.txt`). -/
lemma {lemma_name} {{P Q : Fin 3 → R}}
    (hP : W'.Equation P) (hQ : W'.Equation Q) :
    {lhs} = {rhs} := by
  linear_combination (norm := ({NORM_ALL}))
    (
{raw(cof_p)}
    ) * (equation_iff P).mp hP + (
{raw(cof_q)}
    ) * (equation_iff Q).mp hQ
"""


template = f"""import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Formula
import Mathlib.RingTheory.Jacobson.Ring

/-!
# The second Bosma–Lenstra addition law in projective coordinates (T-W7.0c-i)

Mathlib's `WeierstrassCurve.Projective.addX/addY/addZ` is the Bosma–Lenstra addition law of
the line `Z = 0` (law 1) — exceptional exactly on the diagonal. This file supplies the
**second** law of the complete pair (B–L Thm 2: the law of the line `Y = 0`), `dblAddX/Y/Z`
("the addition law that extends doubling"), and the certified identities linking the two:

* the three cross-law 2×2 minors vanish modulo the two curve equations (the laws are
  projectively proportional on the overlap of their domains) — `…_minor_XY/XZ/YZ`;
* the diagonal of law 2 **is** mathlib's doubling `dblX/dblY/dblZ` — `dblAdd*_self`;
* the `O`-columns: law 2 computes `O + Q = Q` and `P + O = P` with no curve hypothesis;
* bihomogeneity of bidegree `(2, 2)` — `dblAdd*_smul`.

## Provenance (source-of-record: `projects/ModularCurves/scripts/tw7-p1-bosma-lenstra/`)

Law 2 was **derived, not transcribed** — solved exactly from the paper's anchor
`law2ᵢ = s*(Y/Z)·law1ᵢ` (Bosma–Lenstra, *Complete systems of two addition laws for elliptic
curves*, J. Number Theory 53 (1995), p. 237; verbatim quotes with locators in
`.mathlib-quality/tw7-source-quotes.md`) by mod-p interpolation over the graded (2,2)-monomial
basis with integer lift, then certified by the exact ideal identity and 25 end-to-end numeric
group-law checks (`derive_law2.py`). The derivation surfaced a discrepancy against a reading
of the printed `X₃⁽²⁾` on p. 237 — see the warning on `dblAddX`; the derived polynomials are
authoritative independently of anyone's reading of the printed page (the derivation is
overdetermined). Every `linear_combination` cofactor below is kernel-checked here — the CAS
is a search procedure, not a trust step.

The remaining B–L facts are NOT certificates by design (certificate policy, board
T-W7.0c-i): law 2 landing on the curve (c5) and law 1's `equation_addXYZ` route through the
generic-point engine — tickets T-W7.0c-c5α (factorization bridge; skeleton `eq_zero_of_`
`forall_isMaximal_mem` below) and T-W7.0c-c5β (triple → morphism plumbing).
-/

local notation3 "x" => (0 : Fin 3)

local notation3 "y" => (1 : Fin 3)

local notation3 "z" => (2 : Fin 3)

local macro "matrix_simp" : tactic =>
  `(tactic| simp only [Matrix.head_cons, Matrix.tail_cons, Matrix.smul_empty, Matrix.smul_cons,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two])

namespace WeierstrassCurve.Projective

variable {{R : Type*}} [CommRing R] {{W' : Projective R}}

/-! ## The law of the line `Y = 0` -/

variable (W') in
/-- The `X`-coordinate of the second Bosma–Lenstra addition law (the law of the line `Y = 0`),
evaluated at two projective point representatives `P` and `Q`. Its diagonal is `dblX`.
Source: B–L Thm 2 + §5 p. 237 (derived; see the module docstring).

**Paper-fidelity warning — do NOT "correct" this polynomial against the printed page.** In
the printed `X₃⁽²⁾` (B–L p. 237; paper coordinates `P = (X₁:Y₁:Z₁)`, `Q = (X₂:Y₂:Z₂)`), the
`a₃a₄` term is easily (mis)read as `+ a₃a₄·(X₁Z₂ − 2X₂Z₁)·X₂Z₁`. The true term, as derived
and certified here, is `− a₃a₄·(2X₁Z₂ + X₂Z₁)·X₂Z₁` — the two monomials
`- 2 * W'.a₃ * W'.a₄ * P x * P z * Q x * Q z - W'.a₃ * W'.a₄ * P z ^ 2 * Q x ^ 2` below.
The derivation is overdetermined (exact anchor ideal identity `d³Z₁Z₂·law2ᵢ ≡ N_Y·law1ᵢ`
plus 25 independent end-to-end numeric group-law samples; `derive_law2.py`), so the stored
polynomial is authoritative independently of any reading of the page — and the six
kernel-checked certificates in this file would all fail against the misread variant. -/
noncomputable def dblAddX (P Q : Fin 3 → R) : R :=
{raw("dblAddX.txt")}

variable (W') in
/-- The `Y`-coordinate of the second Bosma–Lenstra addition law; diagonal `dblY`.
Source: B–L Thm 2 + §5 p. 237 (derived; see the module docstring). -/
noncomputable def dblAddY (P Q : Fin 3 → R) : R :=
{raw("dblAddY.txt")}

variable (W') in
/-- The `Z`-coordinate of the second Bosma–Lenstra addition law; diagonal `dblZ`.
Source: B–L Thm 2 + §5 p. 237 (derived; see the module docstring). -/
noncomputable def dblAddZ (P Q : Fin 3 → R) : R :=
{raw("dblAddZ.txt")}

variable (W') in
/-- The second Bosma–Lenstra addition law as a point representative. -/
noncomputable def dblAddXYZ (P Q : Fin 3 → R) : Fin 3 → R :=
  ![W'.dblAddX P Q, W'.dblAddY P Q, W'.dblAddZ P Q]

/-- Unfold both addition laws and mathlib's doubling to raw polynomials (for the
`linear_combination` normalization steps below). -/
local macro "law_simp" : tactic =>
  `(tactic| simp only [addX, addY, negAddY, addZ, dblAddX, dblAddY, dblAddZ, dblX, dblY,
    negDblY, dblZ, negY, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons])

/-! ## Bihomogeneity (bidegree `(2, 2)`) -/

lemma dblAddX_smul (P Q : Fin 3 → R) (u v : R) :
    W'.dblAddX (u • P) (v • Q) = (u * v) ^ 2 * W'.dblAddX P Q := by
  simp only [dblAddX, smul_fin3_ext]
  ring1

lemma dblAddY_smul (P Q : Fin 3 → R) (u v : R) :
    W'.dblAddY (u • P) (v • Q) = (u * v) ^ 2 * W'.dblAddY P Q := by
  simp only [dblAddY, smul_fin3_ext]
  ring1

lemma dblAddZ_smul (P Q : Fin 3 → R) (u v : R) :
    W'.dblAddZ (u • P) (v • Q) = (u * v) ^ 2 * W'.dblAddZ P Q := by
  simp only [dblAddZ, smul_fin3_ext]
  ring1

/-! ## The `O`-columns: `O + Q = Q` and `P + O = P`, projectively, with no curve hypothesis -/

lemma dblAddX_zero_left (Y₁ : R) (Q : Fin 3 → R) :
    W'.dblAddX ![0, Y₁, 0] Q = Y₁ ^ 2 * ((W'.a₁ * Q x + Q y + W'.a₃ * Q z) * Q x) := by
  rw [dblAddX]; matrix_simp; ring1

lemma dblAddY_zero_left (Y₁ : R) (Q : Fin 3 → R) :
    W'.dblAddY ![0, Y₁, 0] Q = Y₁ ^ 2 * ((W'.a₁ * Q x + Q y + W'.a₃ * Q z) * Q y) := by
  rw [dblAddY]; matrix_simp; ring1

lemma dblAddZ_zero_left (Y₁ : R) (Q : Fin 3 → R) :
    W'.dblAddZ ![0, Y₁, 0] Q = Y₁ ^ 2 * ((W'.a₁ * Q x + Q y + W'.a₃ * Q z) * Q z) := by
  rw [dblAddZ]; matrix_simp; ring1

lemma dblAddX_zero_right (P : Fin 3 → R) (Y₂ : R) :
    W'.dblAddX P ![0, Y₂, 0] = Y₂ ^ 2 * (P y * P x) := by
  rw [dblAddX]; matrix_simp; ring1

lemma dblAddY_zero_right (P : Fin 3 → R) (Y₂ : R) :
    W'.dblAddY P ![0, Y₂, 0] = Y₂ ^ 2 * (P y * P y) := by
  rw [dblAddY]; matrix_simp; ring1

lemma dblAddZ_zero_right (P : Fin 3 → R) (Y₂ : R) :
    W'.dblAddZ P ![0, Y₂, 0] = Y₂ ^ 2 * (P y * P z) := by
  rw [dblAddZ]; matrix_simp; ring1

/-! ## The diagonal of law 2 is mathlib's doubling -/

/-- **(T-W7.0c(c3), diagonal)** On the curve, the diagonal of the second addition law is
mathlib's `dblX`. CAS-certified cofactor (3–13 terms; `cof_diag_dblAddX.txt`). -/
lemma dblAddX_self {{P : Fin 3 → R}} (hP : W'.Equation P) : W'.dblAddX P P = W'.dblX P := by
  linear_combination (norm := ({NORM_ALL}))
    (
{raw("cof_diag_dblAddX.txt")}
    ) * (equation_iff P).mp hP

/-- **(T-W7.0c(c3), diagonal)** On the curve, the diagonal of the second addition law is
mathlib's `dblY`. CAS-certified cofactor (`cof_diag_dblAddY.txt`). -/
lemma dblAddY_self {{P : Fin 3 → R}} (hP : W'.Equation P) : W'.dblAddY P P = W'.dblY P := by
  linear_combination (norm := ({NORM_ALL}))
    (
{raw("cof_diag_dblAddY.txt")}
    ) * (equation_iff P).mp hP

/-- **(T-W7.0c(c3), diagonal)** On the curve, the diagonal of the second addition law is
mathlib's `dblZ`. CAS-certified cofactor (`cof_diag_dblAddZ.txt`). -/
lemma dblAddZ_self {{P : Fin 3 → R}} (hP : W'.Equation P) : W'.dblAddZ P P = W'.dblZ P := by
  linear_combination (norm := ({NORM_ALL}))
    (
{raw("cof_diag_dblAddZ.txt")}
    ) * (equation_iff P).mp hP

/-- On the curve, the diagonal of the second addition law is mathlib's doubling `dblXYZ`. -/
lemma dblAddXYZ_self {{P : Fin 3 → R}} (hP : W'.Equation P) : W'.dblAddXYZ P P = W'.dblXYZ P := by
  rw [dblAddXYZ, dblAddX_self hP, dblAddY_self hP, dblAddZ_self hP, dblXYZ]

/-! ## The cross-law minors: the two laws are projectively proportional on the curve -/

{minor("XY", "addX_mul_dblAddY", "W'.addX P Q * W'.dblAddY P Q", "W'.addY P Q * W'.dblAddX P Q", "cof_MXY_P.txt", "cof_MXY_Q.txt")}
{minor("XZ", "addX_mul_dblAddZ", "W'.addX P Q * W'.dblAddZ P Q", "W'.addZ P Q * W'.dblAddX P Q", "cof_MXZ_P.txt", "cof_MXZ_Q.txt")}
{minor("YZ", "addY_mul_dblAddZ", "W'.addY P Q * W'.dblAddZ P Q", "W'.addZ P Q * W'.dblAddY P Q", "cof_MYZ_P.txt", "cof_MYZ_Q.txt")}
end Projective

end WeierstrassCurve

/-! ## T-W7.0c-c5α skeleton: the residue-field vanishing principle

The on-curve identity for law 2 (c5) is NOT certified (cofactors ≈ 4–8k terms — over the
no-`maxHeartbeats` bar); per the certificate policy it factors through reducedness: an element
of a reduced Jacobson ring vanishing in every residue field at maximal ideals is zero. This is
the engine of the factorization bridge (board ticket T-W7.0c-c5α); the per-chart vanishing
statements land with c5α itself (they need the `E_U ×_U E_U` chart rings). -/

/-- An element of a reduced Jacobson ring lying in every maximal ideal is zero (equivalently:
vanishing in every residue field kills it). Engine for T-W7.0c-c5α. -/
theorem eq_zero_of_forall_isMaximal_mem {{A : Type*}} [CommRing A] [IsJacobsonRing A]
    [IsReduced A] {{a : A}} (h : ∀ I : Ideal A, I.IsMaximal → a ∈ I) : a = 0 := by
  have hj : a ∈ (⊥ : Ideal A).jacobson := Ideal.mem_sInf.mpr fun _ hJ => h _ hJ.2
  rw [← Ideal.radical_eq_jacobson] at hj
  have hn : a ∈ nilradical A := hj
  rwa [nilradical_eq_zero, Ideal.zero_eq_bot, Ideal.mem_bot] at hn
"""

OUT.write_text(template)
print(f"wrote {{OUT}} ({{len(template.splitlines())}} lines)")
