/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».FiniteJetGraphKoszul

/-!
# Strict localization of the finite-jet Milnor square ([FJP] §4: Lemmas 4.1, 4.3, 4.4, Prop 4.5)

Source: [FJP] §4, "the principal strict-functional-analytic step of the paper. Sheafiness is
not preserved by arbitrary fiber products. What we prove is stronger: under the hypotheses
below, every completed rational localization preserves the pullback strictly and
functorially."

For an indexed open rational datum `(g, f₁, …, f_m)` on 𝓐 (`span ({g} ∪ range f) = ⊤` — in a
Tate ring openness of the ideal is generation of the unit ideal), write
`P_E = E⟨T₁,…,T_m⟩` for `E ∈ {𝓐, 𝓑, 𝓒, 𝓓}` and `I_E = (r₁, …, r_m)` with `r_i = gT_i − f_i`.

* **Lemma 4.1** (Tate extension of a strict pullback): the extended row
  `0 → P_𝓐 → P_𝓑 ⊕ P_𝓒 → P_𝓓 → 0` is strict exact with the same constants (here all 1),
  coefficientwise.
* **Lemma 4.3** (controlled graph-ideal pullback): `I_𝓐 ≅ I_𝓑 ×_{I_𝓓} I_𝓒` boundedly, and
  `I_𝓐` is closed in `P_𝓐` (the `d₂`-correction argument, constants (4.11)–(4.16)).
* **Lemma 4.4** (strict quotient lemma): the normed-group 3×3 lemma.
* **Prop 4.5** (strict Milnor localization): the quotient row
  `0 → 𝓐_α → 𝓑_α ⊕ 𝓒_α → 𝓓_α → 0` of graph quotients `E_α := P_E ⧸ I_E` (complete, since
  the ideals are closed) is exact, the induced map `𝓐_α → 𝓑_α × 𝓒_α` is a topological
  embedding, and `𝓒_α → 𝓓_α` is a continuous open surjection.
-/

open Filter Topology

namespace FiniteJet

open RestrictedLaurent GraphKoszul

namespace StrictLoc

variable (F : Type*) [Field F]

/-- `P_𝓐 = 𝓐⟨T₁,…,T_m⟩` and its three companions. -/
abbrev PA (m : ℕ) : Type _ := GraphKoszul.P (JetA F) m
abbrev PB (m : ℕ) : Type _ := GraphKoszul.P (JetB F) m
abbrev PC (m : ℕ) : Type _ := GraphKoszul.P (JetC F) m
abbrev PD (m : ℕ) : Type _ := GraphKoszul.P (JetD F) m

variable (m : ℕ)

/-- Coefficientwise `jB : P_𝓐 → P_𝓑`. -/
noncomputable def extJB : PA F m →+* PB F m :=
  mapRestricted (jB F) (norm_jB_le F) _

/-- Coefficientwise `ιC : P_𝓐 → P_𝓒`. -/
noncomputable def extIotaC : PA F m →+* PC F m :=
  mapRestricted (iotaC F) (fun a => le_of_eq (norm_iotaC F a)) _

/-- Coefficientwise `ρB : P_𝓑 → P_𝓓`. -/
noncomputable def extRhoB : PB F m →+* PD F m :=
  mapRestricted (rhoB F) (fun b => le_of_eq (norm_rhoB F b)) _

/-- Coefficientwise `ρC : P_𝓒 → P_𝓓`. -/
noncomputable def extRhoC : PC F m →+* PD F m :=
  mapRestricted (rhoC F) (norm_rhoC_le F) _

/-! ### Lemma 4.1 — the extended strict row, constants 1

[FJP] Lemma 4.1 (verbatim): "For every `n ≥ 0`, restricted Tate extension in `n` variables
carries a strict Milnor square to a strict Milnor square. With Gauss norms, the constants κ
and ρ above continue to work." (For the finite-jet square both may be taken equal to one,
[FJP] §4 after (4.2).) -/

theorem ext_square_commutes (p : PA F m) :
    extRhoB F m (extJB F m p) = extRhoC F m (extIotaC F m p) := by sorry

/-- Coefficientwise sectioning: the extended `ρC` is strictly surjective with constant 1. -/
theorem extRhoC_strict_surjective (d : PD F m) :
    ∃ c : PC F m, extRhoC F m c = d ∧ ‖c‖ = ‖d‖ := by sorry

/-- The extended square is cartesian: a compatible pair comes from a unique element of
`P_𝓐` ([FJP] Lemma 4.1: "If `b = ∑ b_ν T^ν` and `c = ∑ c_ν T^ν` have the same image, each
coefficient pair comes from a unique `a_ν ∈ R`"). -/
theorem ext_milnorRow_exact (b : PB F m) (c : PC F m)
    (h : extRhoB F m b = extRhoC F m c) :
    ∃! p : PA F m, extJB F m p = b ∧ extIotaC F m p = c := by sorry

/-- Pullback-norm identity for the extended square (constants 1). -/
theorem ext_max_norm_eq (p : PA F m) :
    max ‖extJB F m p‖ ‖extIotaC F m p‖ = ‖p‖ := by sorry

/-- `P_𝓐 → P_𝓑 ⊕ P_𝓒` is injective (left exactness of the extended row). -/
theorem ext_pair_injective :
    Function.Injective (fun p : PA F m => (extJB F m p, extIotaC F m p)) := by sorry

/-! ### The graph data -/

variable (g : JetA F) (f : Fin m → JetA F)

/-- The graph relations `r_i = gT_i − f_i` in `P_𝓐` ([FJP] (4.6)). -/
noncomputable def rA : Fin m → PA F m := fun i =>
  polyToP (MvPolynomial.C g * MvPolynomial.X i - MvPolynomial.C (f i))

/-- The pushed relations at the vertices. -/
noncomputable def rB : Fin m → PB F m := fun i => extJB F m (rA F m g f i)
noncomputable def rC : Fin m → PC F m := fun i => extIotaC F m (rA F m g f i)
noncomputable def rD : Fin m → PD F m := fun i => extRhoC F m (rC F m g f i)

/-- Graph ideals `I_E = im(d₁) = (r₁, …, r_m)` ([FJP] (4.6)). -/
noncomputable def IA : Ideal (PA F m) := Ideal.span (Set.range (rA F m g f))
noncomputable def IB : Ideal (PB F m) := Ideal.span (Set.range (rB F m g f))
noncomputable def IC : Ideal (PC F m) := Ideal.span (Set.range (rC F m g f))
noncomputable def ID : Ideal (PD F m) := Ideal.span (Set.range (rD F m g f))

/-- The pushed data generate the unit ideal at each vertex ([FJP] §4 after (4.6): "Because
the rational datum is open, its defining ideal contains a power of ϖ. After mapping to each
of the k-algebras B, C, D, the tuple therefore generates the unit ideal"). -/
theorem span_pushed_B (hspan : Ideal.span ({g} ∪ Set.range f) = ⊤) :
    Ideal.span ({jB F g} ∪ Set.range (fun i => jB F (f i))) = ⊤ := by sorry

theorem span_pushed_C (hspan : Ideal.span ({g} ∪ Set.range f) = ⊤) :
    Ideal.span ({iotaC F g} ∪ Set.range (fun i => iotaC F (f i))) = ⊤ := by sorry

theorem span_pushed_D (hspan : Ideal.span ({g} ∪ Set.range f) = ⊤) :
    Ideal.span ({rhoC F (iotaC F g)} ∪
      Set.range (fun i => rhoC F (iotaC F (f i)))) = ⊤ := by sorry

/-! ### Lemma 4.3 — controlled graph-ideal pullback

[FJP] Lemma 4.3 (verbatim): "The canonical algebraic map `I_R → I_B ×_{I_D} I_C` is a
bounded bijection with bounded inverse for the subspace norms. Consequently `I_R` is closed
in `P_R`, the map in (4.9) is a strict isomorphism of Banach spaces, and the difference
sequence `0 → I_R → I_B ⊕ I_C → I_D → 0` is strict exact."  Constants: (4.11)–(4.16). -/

/-- Right strict surjectivity of the ideal row ([FJP] (4.11)). -/
theorem ideal_row_surjective (hspan : Ideal.span ({g} ∪ Set.range f) = ⊤) :
    ∃ Cs : ℝ, 1 ≤ Cs ∧ ∀ y ∈ ID F m g f,
      ∃ xc ∈ IC F m g f, extRhoC F m xc = y ∧ ‖xc‖ ≤ Cs * ‖y‖ := by sorry

/-- The controlled pullback ([FJP] (4.12)–(4.16)): a matching pair of graph-ideal elements
comes from an element of `I_𝓐` with a uniformly bounded representative. This is where the
`d₂`-syzygy correction (`exists_d2_lift` at the 𝓓-vertex) enters. -/
theorem ideal_pullback_controlled (hspan : Ideal.span ({g} ∪ Set.range f) = ⊤) :
    ∃ Cs : ℝ, 1 ≤ Cs ∧
      ∀ xb ∈ IB F m g f, ∀ xc ∈ IC F m g f,
        extRhoB F m xb = extRhoC F m xc →
        ∃ xa ∈ IA F m g f,
          extJB F m xa = xb ∧ extIotaC F m xa = xc ∧ ‖xa‖ ≤ Cs * max ‖xb‖ ‖xc‖ := by sorry

/-- `I_𝓐` is closed in `P_𝓐` ([FJP] Lemma 4.3: "Consequently `I_R` is closed in `P_R`"). -/
theorem isClosed_IA (hspan : Ideal.span ({g} ∪ Set.range f) = ⊤) :
    IsClosed ((IA F m g f : Set (PA F m))) := by sorry

/-! ### Proposition 4.5 — strict Milnor localization

[FJP] Prop 4.5 (verbatim): "Let (4.5) be a strict Milnor square and assume B, C, D are
affinoid k-algebras. For every open rational datum α in R, the canonical square of completed
rational localizations is again a strict Milnor square. Equivalently,
`0 → R_α → B_α ⊕ C_α → D_α → 0` is strict exact, `R_α ≅ B_α ×_{D_α} C_α` is a strict
isomorphism, and `C_α → D_α` is a strict surjection."

Since all four graph ideals are closed ([FJP] (4.21): "the completed graph quotient is
already the Banach quotient `E_α = P_E/I_E`"), we take the plain ring quotients with their
quotient topologies. The strict quotient lemma ([FJP] Lemma 4.4) is consumed inside the
proofs of the statements below; its normed-group bookkeeping is recorded in the campaign
decomposition. -/

/-- `𝓐_α = P_𝓐 ⧸ I_𝓐` and companions, as topological rings with the quotient topology. -/
abbrev locA : Type _ := PA F m ⧸ IA F m g f
abbrev locB : Type _ := PB F m ⧸ IB F m g f
abbrev locC : Type _ := PC F m ⧸ IC F m g f
abbrev locD : Type _ := PD F m ⧸ ID F m g f

/-- The induced maps of the localized square ([FJP] (4.19)). -/
noncomputable def locJB : locA F m g f →+* locB F m g f := by sorry

noncomputable def locIotaC : locA F m g f →+* locC F m g f := by sorry

noncomputable def locRhoB : locB F m g f →+* locD F m g f := by sorry

noncomputable def locRhoC : locC F m g f →+* locD F m g f := by sorry

theorem locJB_mk (p : PA F m) :
    locJB F m g f (Ideal.Quotient.mk (IA F m g f) p) =
      Ideal.Quotient.mk (IB F m g f) (extJB F m p) := by sorry

theorem locIotaC_mk (p : PA F m) :
    locIotaC F m g f (Ideal.Quotient.mk (IA F m g f) p) =
      Ideal.Quotient.mk (IC F m g f) (extIotaC F m p) := by sorry

theorem loc_square_commutes (x : locA F m g f) :
    locRhoB F m g f (locJB F m g f x) = locRhoC F m g f (locIotaC F m g f x) := by sorry

/-- Algebraic exactness of the localized row: the pullback description of `𝓐_α`
([FJP] (4.20)). -/
theorem loc_row_exact (hspan : Ideal.span ({g} ∪ Set.range f) = ⊤)
    (b : locB F m g f) (c : locC F m g f)
    (h : locRhoB F m g f b = locRhoC F m g f c) :
    ∃! x : locA F m g f, locJB F m g f x = b ∧ locIotaC F m g f x = c := by sorry

theorem loc_pair_injective (hspan : Ideal.span ({g} ∪ Set.range f) = ⊤) :
    Function.Injective
      (fun x : locA F m g f => (locJB F m g f x, locIotaC F m g f x)) := by sorry

/-- Topological strictness on the left ([FJP] (4.19)/(4.20)): `𝓐_α` carries the subspace
topology of `𝓑_α × 𝓒_α`. -/
theorem loc_pair_isEmbedding (hspan : Ideal.span ({g} ∪ Set.range f) = ⊤) :
    Topology.IsEmbedding
      (fun x : locA F m g f => (locJB F m g f x, locIotaC F m g f x)) := by sorry

/-- `𝓒_α → 𝓓_α` is a continuous open surjection ([FJP] Prop 4.5: "`C_α → D_α` is a strict
surjection"). -/
theorem locRhoC_surjective (hspan : Ideal.span ({g} ∪ Set.range f) = ⊤) :
    Function.Surjective (locRhoC F m g f) := by sorry

theorem locRhoC_isOpenMap (hspan : Ideal.span ({g} ∪ Set.range f) = ⊤) :
    IsOpenMap (locRhoC F m g f) := by sorry

/-- `𝓐_α` is Hausdorff (quotient by a closed ideal; [FJP] (4.21)). -/
theorem locA_t2 (hspan : Ideal.span ({g} ∪ Set.range f) = ⊤) :
    T2Space (locA F m g f) := by sorry

/-- `𝓐_α` is complete (Banach quotient; [FJP] (4.21): "the completed graph quotient is
already the Banach quotient"). -/
theorem locA_completeSpace (hspan : Ideal.span ({g} ∪ Set.range f) = ⊤) :
    @CompleteSpace (locA F m g f)
      (IsTopologicalAddGroup.rightUniformSpace (locA F m g f)) := by sorry

end StrictLoc

end FiniteJet
