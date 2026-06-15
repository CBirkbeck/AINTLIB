# Tate Acyclicity Chain — Per-Lemma Audit

Triple-checked against Wedhorn (arXiv:1910.05934v1). Proof target:

> **Theorem 8.28(b)** (Wedhorn p.81). Let `A = (A, A⁺)` be an affinoid ring with `A` a strongly noetherian Tate ring. Then `O_X` is a sheaf of complete topological rings on `X = Spa A`, and `H^q(U, O_X) = 0` for all `q ≥ 1` and all rational subsets `U` of `X`.

Plus **Cor 8.35** (stably sheafy upgrade) and **Remark 8.20** (topological-rings sheaf condition).

Status legend: ✅ = stated in Lean ; ⚠️ = needs to be added ; 🔧 = exists but stronger statement needed.

---

## Appendix A — Čech machinery (abstract)

| Wedhorn | Statement | Lean |
|---|---|---|
| A.1 | `F`-acyclic = augmented Čech complex exact | ✅ `CechCohomology.lean:452` (`IsAcyclic`) |
| A.2 | Mutual refinements ⇒ same acyclicity | ⚠️ `mutual_refinement_acyclic_iff` — see signatures file |
| A.3(1) | `V|U_·` acyclic & `U|V_·` acyclic ⇒ (`U` acyclic ⇔ `V` acyclic) | ⚠️ `acyclic_iff_of_mutual_restriction` |
| A.3(2) | `V` refines `U`, `V|U_·` acyclic ⇒ (`U` acyclic ⇔ `V` acyclic) | ⚠️ `acyclic_iff_refinement_under_restriction_acyclic` |
| A.3(3) | `V|U_·` acyclic ⇒ (`U × V` acyclic ⇔ `U` acyclic) | ⚠️ `acyclic_iff_prod_under_restriction_acyclic` |
| A.4 | `B` basis stable under ∩, `F'` U-acyclic for U ⊆ B ⇒ extended `F` is sheaf and `Ȟ^q ≅ H^q` | ⚠️ `isSheaf_of_isAcyclic_on_intersection_stable_basis` |

(The codebase has lots of `CechCohomology.lean` infrastructure: `IsAcyclic.separating`, `IsAcyclic.gluing`, `IsAcyclic.higher_vanishing`, `isAcyclic_of_components`, `single_isSeparating_and_hasGluing`, `prod`/`restrict` etc. — but the **abstract refinement equivalences A.2, A.3(1)–(3), A.4** are not stated as named theorems with the Wedhorn shape. They are needed verbatim.)

---

## §7.1–§7.5 — `Spv(A,I)` infrastructure

| Wedhorn | Statement | Lean |
|---|---|---|
| 7.1 | For convex `H ⊆ Γ_v` with `cΓ_v ⊆ H`: `c := {a ∈ A | v(a) cofinal for H}` is an ideal, `rad(c) = c` | ⚠️ `cofinalityIdeal` (def) + `cofinalityIdeal_isRadical` |
| 7.2 | `v(I) ∩ cΓ_v = ∅` ⇒ exists greatest convex `H` with `v(a)` cofinal for `H` ∀ `a ∈ I`; if `v(I) ≠ {0}` then `H ⊇ cΓ_v` | ⚠️ `exists_greatest_cofinal_convex_subgroup_of_ideal` |
| 7.3 (def) | `cΓ_v(I)` | ✅ `CharacteristicSubgroup.lean` (`cGammaIdeal`) |
| 7.4 | `cΓ_v(I) = Γ_v ↔ v(a) cofinal for Γ_v ∀ a ∈ I ↔ v(a) cofinal for Γ_v ∀ a in generators of √I` | 🔧 *Fragments*: `Spv.cofinalValue_of_isContinuous` (`SpvAI.lean:374`); need full equivalence `cGammaIdeal_eq_top_iff` |
| 7.1.1 (def) | `Spv(A,I) := { v ∈ Spv A | cΓ_v(I) = Γ_v }` | ✅ `SpvAITopology.lean:45` (`SpvAI`) |
| 7.1.2 (def) | retraction `r : Spv A → Spv(A,I)`, `r(v) = v|_{cΓ_v(I)}` | ⚠️ `Spv.retractToSpvAI` (currently `Valuation.restrictIdeal` exists but the typed `Spv → SpvAI` lift isn't stated) |
| 7.5(1) basis | `R = {Spv(A,I)(T/s) | s ∈ A, T ⊆ A finite, I ⊆ √(T·A)}` is closed under finite ∩, basis of QC opens | ✅ Set defined `SpvAITopology.lean:50` ; ∩-stability `SpvAITopology.lean:62`; `R` is QC basis: ⚠️ `SpvAI.rationalSubset_isBasis_of_qcOpens` |
| 7.5(1) spectral | `Spv(A,I)` is a spectral space | ⚠️ `SpvAI.isSpectralSpace` |
| 7.5(2) | `r : Spv A → Spv(A,I)` is continuous spectral | ⚠️ `Spv.retractToSpvAI_continuous`, `Spv.retractToSpvAI_isSpectralMap` |
| 7.5(3) | `v ∈ Spv A, v(I) ≠ 0 ⇒ r(v)(I) ≠ 0` | ⚠️ `Spv.retractToSpvAI_ideal_ne_zero_of_ne_zero` |
| 7.6 (rem) | `Spv(A,I) ↪ Spv A` is not spectral in general | (informational, not used) |

---

## §7.7–§7.12 — `Cont(A)` as constructible subset of `Spv(A,I)`

| Wedhorn | Statement | Lean |
|---|---|---|
| 7.7 (def) | continuous valuation | ✅ `ContinuousValuations.lean` (`Valuation.IsContinuous`) |
| 7.8(1) | `v` continuous ⇔ `v : A → Γ_v∪{0}` continuous as map | ✅ `ContinuousValuations.lean:39` (`isContinuous_iff_units`) |
| 7.8(3) | `v` continuous ⇔ `A_{≤γ}` open ∀ γ ∈ Γ_v | ⚠️ `isContinuous_iff_setOf_le_isOpen` |
| 7.9 (rem) | Continuous ring hom induces `Cont(B) → Cont(A)` | ⚠️ `Cont.functorial` (probably needed only implicitly) |
| 7.10 | `Cont(A) = { v ∈ Spv(A, I·A) | v(a) < 1 ∀ a ∈ I }` | 🔧 Two halves exist as `SpvAI.lean:294` and `SpvAI.lean:374`; need **equality form** `Cont_eq_SpvAI_inter_lt_one` |
| 7.11(1) | `v` continuous ⇔ `v(a)` cofinal for Γ_v ∀ `a ∈ I` | ⚠️ `isContinuous_iff_cofinal_on_idealOfDef` |
| 7.11(2) | `v` continuous, `H ⊊ Γ_v` proper convex, `v(a) ∈ Γ_v/H` cofinal ⇒ `v/H` continuous | ⚠️ `isContinuous_quotient_of_cofinal` |
| 7.12 | `Cont(A)` is closed in `Spv(A,I)`, hence spectral | ⚠️ `Cont.isClosed_in_SpvAI` + `Cont.isSpectralSpace` |

---

## §7.14–§7.22 — affinoid rings

| Wedhorn | Statement | Lean |
|---|---|---|
| 7.14 (def) | ring of integral elements, affinoid ring | ✅ `AffinoidRings.lean` |
| 7.15 | `A°` is largest ring of integral elements | ✅ `Bounded.lean` |
| 7.16 (ex) | `(A, A)` for adic A is affinoid | ✅ |
| 7.17 (ex) | `(K, A(v))` for microbial field K is Tate affinoid | ⚠️ if needed |
| 7.18 | `S_X` pro-constructible; σ/τ bijection between rings of integral elements and pro-constructible subsets `≤ S_A` | ⚠️ `proConstructible_of_subring`, `RingOfIntElements_iff_proConstructible` (used in 7.35 proof) |
| 7.19 | `(A⟨X⟩_T, (A⁺⟨X⟩_T)^int)` is affinoid | ⚠️ `affinoidRing_AlangleX_T` |
| 7.20 | `(A°)⟨X⟩ ⊆ (A⟨X⟩_T)°` | ⚠️ `powerBounded_in_AlangleX` |
| 7.21 (rem) | Universal property of `A → A⟨X⟩_T` | 🔧 `TateAlgebra.evaluation`-style universal property — verify in `TateAlgebra*.lean` |
| 7.22 (rem-def) | quotient affinoid `A/I` | ⚠️ if needed |

---

## §7.23–§7.36 — `Spa(A,A⁺)` topology

| Wedhorn | Statement | Lean |
|---|---|---|
| 7.23 (def) | `Spa A := { v ∈ Cont A | v(f) ≤ 1 ∀ f ∈ A⁺ }` | ✅ `AdicSpectrum.lean` (`Spa`) |
| 7.24 (rem) | `v(a) ≤ 1 ∀ a ∈ A⁺ ⇔ v(a) ≤ 1 ∀ a ∈ Ã` (subring with integral closure A⁺) | ⚠️ `vle_one_AplusInt_iff` (used in 7.18, 7.35 proofs) |
| 7.25 (rem) | every `v ∈ Cont A` has vertical generization in `Spa` | ⚠️ `exists_vertical_generization_in_spa` |
| 7.26 (ex) | discrete case `(A, A⁺)` | ✅ |
| 7.28 (rem-def) | `Spa(φ) : Spa B → Spa A` functorial | ⚠️ `Spa.functorial` |
| 7.29 (def) | rational subsets `R(T/s)` | ✅ `AdicSpectrum.lean` (`rationalOpen`) |
| 7.30(1) | `T·A` open ⇔ `I ⊆ rad(T·A)` for `I = ⟨(A)^{∘∘}⟩` | ⚠️ `isOpen_span_iff_radical_contains_topnilp_ideal` |
| 7.30(2) | Tate: `T·A` open ⇔ `T·A = A` | ⚠️ `isOpen_span_iff_eq_top_of_tate` |
| 7.30(3) | `R(T/s) = R(T∪{s}/s)` | ✅ `RationalSubsets.lean` (`rationalOpen_insert_self` or similar) |
| 7.30(4) | `s ∈ A^×` unit ⇒ `R(T'/s)` always rational; `R(f/1) = {x : |f(x)| ≤ 1}` | ⚠️ `rationalOpen_unit_denominator`, `rationalOpen_singleton_one` ✅ partial in `LaurentRefinement.lean` |
| 7.30(5) | `R(T₁/s₁) ∩ R(T₂/s₂) = R(T₁·T₂/(s₁s₂))` | ✅ partial — `Presheaf.lean` etc.; need `rationalOpen_inter_eq_product` clean statement |
| 7.31 | `X ⊆ Spa A` QC, `|f(x)| ≠ 0` ∀ `x ∈ X` ⇒ ∃ nbhd `I` of 0 with `|a(x)| < |f(x)|` ∀ x ∈ X, a ∈ I | ⚠️ `exists_zero_nbhd_lt_on_qcSubset` |
| 7.32 | Tate, `Y` QC, `|s(y)| ≠ 0` on Y ⇒ ∃ unit `π` with `|π(y)| < |s(y)|` on Y | 🔧 `Cor732.lean:206` (`exists_dominating_unit`) exists with `hArch`; needs no-hArch variant **`exists_dominating_unit_noHArch`** |
| 7.33 (rem) | Tate, `T·A=A`, `x ∈ Spa` with `|t(x)| ≤ |s(x)|` ∀ t ∈ T ⇒ ∃ unit `π` with `|π(x)| ≤ |s(x)|`; gives `R(T/s) = {x : ∀ t ∈ T, |t(x)| ≤ |s(x)|}` | ⚠️ `rationalOpen_eq_setOf_vle_of_tate` |
| 7.34 | Standard rational subset perturbation `R(t₁,…,tₙ/s) = R(t'₁,…,t'ₙ/s')` for `s' ∈ s+J`, `t'_i ∈ t_i+J` | ⚠️ `rationalOpen_perturb` |
| 7.35(1) | `Spa A` is spectral; equals `Cont(A) ∩ ⋂_{a ∈ A⁺} Spv(A,I)(a/1)` | ⚠️ `Spa.isSpectralSpace`, `Spa.eq_Cont_inter_basicOpens` |
| 7.35(2) | Rational subsets form basis of QC opens of Spa, stable under ∩ | ⚠️ `rationalOpen_isBasis_of_qcOpens` |
| 7.36 (cor) | Subset of `Spa A` constructible ⇔ in boolean algebra of rational subsets | ⚠️ |
| 7.37 (ex) | (microbial field example) | (informational) |
| 7.38 | `Spa(A/a) ≅` closed subset of `Spa A` of supp ⊇ a | ⚠️ if needed |

---

## §7.39–§7.43 — analytic points (only used in 8.35-route variants)

| Wedhorn | Statement | Lean |
|---|---|---|
| 7.39 (def) | analytic point | ✅ `AnalyticPoints.lean` |
| 7.40 | analytic point properties (1)–(6) | 🔧 partial in `AnalyticPoints.lean` |
| 7.41 | height 1 analytic ⇒ `v(a) ≤ 1` ∀ a ∈ A° ⇒ ∈ Spa | ⚠️ `analytic_height_one_in_spa` |
| 7.42 | vertical generization of `x ∈ Spa A` is in `Spa A` | ⚠️ `vertical_generization_in_spa` |
| 7.44 | open subring `B ⊆ A` gives `Cont A = g⁻¹(Cont B)` | ⚠️ if needed |
| 7.45 | complete affinoid, non-open prime `p` ⇒ ∃ analytic ht1 `x ∈ Spa A` with supp x ⊇ p | ⚠️ if needed for non-Tate |
| 7.46 | continuous φ properties; adic ⇔ `f(X_a) ⊆ Y_a`; adic ⇒ rational subsets pull back | ⚠️ |

---

## §7.47–§7.55 — cover refinement / completion

| Wedhorn | Statement | Lean |
|---|---|---|
| 7.47 | Completion bijection on open subgroups, preserving A°, A°°, rings of definition, rings of integral elements | ✅ probably in `AdicCompletionBridge.lean` |
| 7.48 | `Spa Â → Spa A` homeomorphism preserving rational subsets | ⚠️ `Spa.completion_isHomeo` |
| 7.49 | `Spa A = ∅` characterizations | ⚠️ if needed (probably not) |
| 7.51 | Complete affinoid, maximal ideal `m` ⊂ A closed; ∃ `v ∈ Spa A` with supp = m | ⚠️ `exists_spa_with_supp_eq_maximal` |
| 7.52(1) | `|f(x)| ≤ 1 ∀ x ∈ Spa A ⇔ f ∈ A⁺` | ⚠️ `vle_one_everywhere_iff_mem_Aplus` |
| 7.52(2) | A complete ⇒ `f` unit ⇔ `|f(x)| ≠ 0 ∀ x ∈ Spa A` | ⚠️ `isUnit_iff_ne_zero_everywhere_complete` |
| 7.53 | A complete affinoid; `T·A = A ⇔ ∀ x ∃ t ∈ T : |t(x)| ≠ 0`; then `(R(T/t))_{t ∈ T}` is open cover | ⚠️ `isOpenCover_of_idealEqTop` |
| **7.54** | A complete; `(V_j)_{j ∈ J}` open cover of Spa A ⇒ ∃ `f_0,...,f_n ∈ A` generating A as ideal s.t. each `R((f_0...f_n)/f_i) ⊆ some V_j` | ⚠️ `exists_idealGeneratedCoverRefinement` ← **CRUCIAL, this is the B-IDEAL-COVER input** |
| 7.55 (rem) | Tate; `T·A` open; `U = {x | x(t_i) ≤ x(s) ≠ 0}` admits unit `u` with `|u| < |s|` on U; gives iterated rational subset chain | ✅ `IteratedRational.lean` |

---

## §8.1–§8.5 — `O_X` presheaf, stalks

| Wedhorn | Statement | Lean |
|---|---|---|
| 8.1.1 (def) | `O_X(R(T/s)) := A⟨T/s⟩` | ✅ `Presheaf.lean` (`presheafValue`) |
| 8.1 (Lem) | Universal property of `A → A⟨T/s⟩` and `Spa(A⟨T/s⟩) → Spa A` | 🔧 partial in `Presheaf.lean` |
| 8.2 | Nested rational `U ⊆ V` ⇒ unique continuous `O_X(V) → O_X(U)`; `Spa A⟨T/s⟩ ≅ R(T/s)` homeomorphism on rational subsets | 🔧 `IteratedRational.lean` + `Presheaf.lean` partial |
| 8.3 (rem) | `X = R(1/1)` ⇒ `O_X(X) = Â` | ✅ |
| 8.4 (rem) | σ-isomorphism for nested rational subsets | ✅ in `Presheaf.lean` |
| 8.5 (rem-def) | Stalks `O_{X,x}`, valuation `v_x` | ✅ `StructureSheaf.lean` partial |
| 8.6 (Prop) | `O_{X,x}` is local, max ideal = supp v_x | ⚠️ `OXx.isLocal_supp_eq_maxIdeal` |
| 8.7 (rem-def) | `V^pre` category | ⚠️ (only needed for 8.10, 8.27) |
| 8.8 (rem-def) | open immersion in `V^pre` | ⚠️ |
| 8.9 (rem-def) | `F` adapted to basis ⇒ sheaf iff sheaf on basis | ⚠️ `isSheaf_iff_isSheaf_on_adapted_basis` |
| 8.10 (rem-def) | pre-adic space | ⚠️ |
| 8.11 (rem) | open subspace of pre-adic is pre-adic | ⚠️ |
| 8.12 (rem) | `{x ∈ U | v_x(f) ≤ v_x(g) ≠ 0}` is open in X | ⚠️ `isOpen_setOf_vle_ne_zero` |
| 8.13 (rem-def) | `O_X^+(U)` | ⚠️ |
| 8.14 (Lem) | Pre-adic morphism criterion via local on `O^+` | ⚠️ |
| 8.15 (Prop) | π-adic completion of `O_{X,x}` = π-adic completion of κ(x)⁺ | ⚠️ **PROJECT-FLAGGED BLOCKER** (`MEMORY.md`: project_issheafy_status; project_T001_completion_route) |
| 8.16 (Prop) | `(O_X(U), O_X⁺(U)) = (A⟨T/s⟩, A⟨T/s⟩⁺)` for `U = R(T/s)` | ✅ `Presheaf.lean` partial |

---

## §8.20–§8.27 — sheafy / adic spaces

| Wedhorn | Statement | Lean |
|---|---|---|
| 8.20 (rem) | `O_X` sheaf of top rings ⇔ `O_X` sheaf of rings ∧ `O_X(U) → ∏ O_X(U_i)` topological embedding | ⚠️ **`isSheaf_of_topological_iff_isSheaf_and_topEmbedding`** ← needed for "complete topological rings" conclusion of 8.28 |
| 8.21 (def) | affinoid adic space | ⚠️ |
| 8.22 (def) | adic space | ⚠️ |
| 8.23 (rem) | adic space properties | ⚠️ |
| 8.24 (rem) | morphisms form a sheaf | (not needed for 8.28) |
| 8.25 (Prop) | adic space morphisms | (not needed for 8.28) |
| 8.26 (def) | A is sheafy | ✅ `StructureSheaf.lean` (`IsSheafy`) |
| 8.27 (rem) | (a) open affinoids sheafy or (b) basis of stably sheafy ⇒ adic | ⚠️ `isAdic_of_basis_stably_sheafy` |

---

## §8.28–§8.35 — Tate acyclicity proper

| Wedhorn | Statement | Lean |
|---|---|---|
| **8.28 (Thm)** | `A` strongly noetherian Tate ⇒ `O_X` sheaf of complete top rings, `H^q(U, O_X) = 0` for q ≥ 1 and U rational | 🔧 `TateAcyclicity.lean:tateAcyclicity` exists with hypotheses + sorries; `StructureSheaf.lean:1105` (`isSheafy_ofStronglyNoetherianTate_flat`) — currently parametric. The clean unconditional statement **`tateAcyclicity_stronglyNoetherianTate`** needs to be stated. |
| 8.29 (rem) | `μ_M : M ⊗_A A⟨X⟩ → M⟨X⟩` bijective for finitely generated M | ⚠️ `NoetherianTateModules.lean` related; need named theorem `mu_M_bijective_for_fg_module` |
| 8.30 (Prop) | rational restriction `O_X(V) → O_X(U)` is flat | ✅ done (#35 `T-RATIONAL-FLAT-GENERAL-CLOSE-CHAIN`) |
| 8.31(1) | `A⟨X⟩` faithfully flat over A | ⚠️ `AlangleX_faithfullyFlat` |
| 8.31(2) | `A⟨X⟩/(f-X)` and `A⟨X⟩/(1-fX)` flat over A | 🔧 `TateAcyclicity.lean:226-228` references `flat_quotient_fSubX`, `flat_quotient_oneSubfX` discrete + general; verify names + general form |
| **8.32 (Cor)** | `A → ∏ O_X(U_i)` faithfully flat for finite rational cover | 🔧 `Cor832.lean:productRestriction_faithfullyFlat_abstract` (line 205) — verify it's stated unconditionally, not parametrically |
| **8.33 (Lem)** | Two-piece Čech `0 → O_X(X) → O_X(U_1)×O_X(U_2) → O_X(U_1∩U_2) → 0` exact for `U_1 = R(f/1), U_2 = R(1/f)` | ✅ `LaurentCoverExact.lean:193` (`laurentCover_exact`) — discrete case. **General case**: need `laurentCover_exact_strongly_noetherian` |
| **8.34 (Lem)** | A complete strongly noeth Tate, `U` rational cover generated by `T` with `T·A=A` ⇒ `U` is `O_X`-acyclic | 🔧 split into P3–P8 board sorries |
| 8.34(i) | Laurent covers are `O_X`-acyclic (induction on 8.33 via Prop A.3(3)) | ⚠️ `laurentCover_isAcyclic` (induction step) |
| 8.34(ii) | T·A=A ⇒ ∃ Laurent cover V s.t. `U|V_j` unit-generated ∀ j | 🔧 P6 (`exists_first_stage_laurent_tree_unit_generated`) — currently blocks on hArch via Cor 7.32; unblocks via 7.32-noHArch |
| 8.34(iii) | Unit-generated rational cover has Laurent refinement | 🔧 P5 (`unitGeneratedCover_has_relative_ratioLaurentRefinement`) — partial closure this session |
| 8.34(iv) | Combine (i)+(ii)+(iii) via Prop A.3(1) | 🔧 P8 (`exists_wedhorn_ratio_laurent_refinement_tree_realized`) |
| **8.35 (Cor)** | A satisfies one of (a)/(b)/(c) ⇒ A stably sheafy | ⚠️ `stronglyNoetherianTate_stably_sheafy` |

---

## Half-space compactness (the no-hArch endpoint, feeds 8.34)

| Lean name | Wedhorn ref | Lean |
|---|---|---|
| `isCompact_rationalOpen_inter_vle_noHArch` | 7.35(2) + 7.30 + 7.32 (intersection of QC-open with closed in spectral space) | 🔧 `SpaCompactNoHArch.lean:186` (sorry, parent of Arc I) |
| `exists_uniform_pow_vle_on_compact` | direct compactness application | ✅ `SpaCompactNoHArch.lean:99` |
| `isClosed_setOf_vle_in_spa` | trivial: closed half-space `{v(g) ≤ v(h)}` is closed | ⚠️ |

---

# Summary

**Bite-size lemmas needed**: ~70 (count of ⚠️ + 🔧 above).

**Distribution by Wedhorn section** (Wedhorn ref → ⚠️ count → 🔧 count):
- App A (Čech machinery): 5⚠️ + 0🔧
- §7.1–7.5 (Spv(A,I)): 8⚠️ + 1🔧
- §7.7–7.12 (Cont): 5⚠️ + 1🔧
- §7.14–7.22 (affinoid rings): 4⚠️ + 0🔧
- §7.23–7.36 (Spa topology): 14⚠️ + 1🔧
- §7.39–7.46 (analytic): 4⚠️ (likely fewer actually needed)
- §7.47–7.55 (covers/completion): 8⚠️ + 0🔧 (incl. 7.54 — CRUCIAL)
- §8.1–8.16 (O_X / stalks): 9⚠️ + 4🔧 (incl. 8.15 — flagged blocker)
- §8.20–8.27 (sheafy/adic): 5⚠️
- §8.28–8.35 (acyclicity proper): 5⚠️ + 6🔧 (the P3–P8 board)

**Already done** (✅): roughly 15 items — primarily the definitional layer (Spa, rationalOpen, IsSheafy, IsAcyclic, Cont, ring of integral elements) plus T-RATIONAL-FLAT-GENERAL (8.30) and the discrete-case Laurent exact (8.33-discrete).

**Project-flagged blockers**:
- Prop 8.15 (π-adic completion of stalk vs κ(x)⁺) — `MEMORY.md` flags this as the IsSheafy faithful-flatness blocker.
- Cor 7.32 needs hArch in current Lean proof — Arc I (above) replaces with no-hArch route via Spv(A,I).

Next deliverable: a Lean file `Adic spaces/TateAcyclicityChain.lean` with every ⚠️ item stated as a sorry'd theorem, organized in proof order, so each can be picked up independently.
