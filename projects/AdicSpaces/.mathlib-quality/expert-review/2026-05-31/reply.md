# Expert reply — Wedhorn 8.28(b) "Proof: Missing" gap (received 2026-05-31)

Audience: senior arithmetic geometer. Re: REVIEW_BRIEF.md (the Prop 6.17/6.18 / Henkel-OMT gap).

## Executive verdict

Routes A and B do **not** together give a faithful replacement for Prop 6.17 / Henkel–Bourbaki OMT
in case (b). Route A may give the **abstract noetherianity** of `O_X(V)` (if the completion-quotient
map is genuinely surjective) but does **not** give the closed-ideal/topological-quotient statements
(G1) needed for Examples 6.38/6.39 and Lemma 8.33. Route B in the generality of arbitrary `f ∈ A` is
"Proposition 6.17 in disguise"; the naive division argument fails for the power-boundedness reason we
found. **For full case (b), some form of the Henkel/Baire OMT or Prop 6.17/6.18 is unavoidable.**
Make progress via case (a) interim + use Route A to isolate noetherianity from closedness. Do not keep
searching for an elementary closedness proof of `(f−ζ)`, `(1−fη)` in the strongly-noetherian case.

## Per-question

- **Q1 (do A+B suffice without OMT?): No.** Route A → only abstract noetherianity (G2); not the closed
  quotient reps (G1). Route B fails for arbitrary `f`. A+B insufficient for case (b).
- **Q2 (bivariate closedness?):** For the full topological statement you need the bivariate
  identification (closedness). BUT it can be **staged**: (1) prove `(f−ζ)` closed in `A⟨ζ⟩`; (2)
  `B := A⟨ζ⟩/(f−ζ)` is complete noetherian Tate; (3) overlap `= B⟨η⟩/(1−fη)`; (4) prove `(1−fη)` closed
  in `B⟨η⟩`. So the *multivariable* Prop 6.17 is not needed as a separate theorem — but the single-var
  6.17/OMT core still is (plus: the intermediate quotient stays in the class where the single-var
  instance applies).
- **Q3 (Route A for Lemma 8.31 base?): Partially.** Route A gives abstract noetherianity of `O_X(V)` —
  one input. But Lemma 8.31's *proof* uses the 6.18/Remark-8.29 finite-module machinery. If our 8.31 is
  proved only via a noetherian ring of definition, Route A doesn't help enough. **Route A pays off only
  if Lemma 8.31 is first made independent of noetherian rings of definition (abstract-ring version).**
- **Q4 (specific-instance OMT lighter?):** Only slightly; you still need almost all the OMT/Nakayama
  machinery. **Prove the general usable module-level form** — `closed_submodule_of_fg_of_noetherian_complete_tate`
  (or a close Henkel/Prop 6.17 formulation) — not a one-off ideal closedness. It pays off for `(f−ζ)`,
  `(1−fη)`, the bivariate ideal, and later finite-module arguments. Correction: "`N̂` complete because
  closed-in-complete" is the wrong reading — `N̂` is complete *by construction as a completion*; `N` closed
  follows after proving `N → N̂` is iso onto its image in `M`. No circularity if organized this way.
- **Q5 (case (a) interim?): Yes**, a respectable milestone (covers classical rigid-analytic / discretely-
  valued bases). Lost vs (b): affinoids over non-discretely-valued fields (`ℂₚ`); strongly-noeth Tate
  with non-noetherian rings of definition; full 8.28(b)/8.35(b). Name it honestly
  (`isSheafy_of_complete_tate_with_noetherian_ringOfDefinition`), keep case (b) as a separate tracked goal.
- **Q6 (does 6.17 enter only via 6.38/6.39?): No.** It also enters through **Lemma 8.31 / Remark 8.29**
  (the `M ⊗_A A⟨X⟩ ≅ M⟨X⟩` finite-module/tensor identity is supplied by 6.18). So the analytic core enters:
  (1) closed quotient reps in 6.38/6.39; (2) finite-module topology / tensor identity behind 8.31; (3)
  hence 8.30 + 8.32. Even with Route A's abstract noetherianity, case (b) still needs the 6.18 finite-
  module input to run Lemma 8.31.

## Recommended path

Short-term: (1) ship case (a) if the surrounding proof is in place; (2) use Route A to isolate
noetherianity of `O_X(V)`; (3) stop searching for elementary single-var closedness.
Medium-term: (4) formalize the Henkel/Bourbaki OMT or Prop 6.17/6.18 package, targeting the module-level
`closed_submodule_of_fg_of_noetherian_complete_tate`; (5) upgrade Lemma 8.31 to the abstract complete-
noetherian-Tate version once 6.18 is available; (6) then complete case (b).

## Manager message to worker

Routes A+B not enough for case (b). Route A worth doing (abstract noetherianity of `O_X(V)` as a quotient
of a noetherian Tate algebra) but does not give closed quotient reps nor upgrade Lemma 8.31. Route B: abandon
as an OMT bypass — single-var closedness of `(f−ζ)`, `(1−fη)` for arbitrary `f` is not elementary; the failed
Weierstrass division is the real obstruction. Bivariate overlap reduces to iterated single-var closedness IF
the single-var theorem is available, but still depends on the same core. Choices: (1) ship case (a) now;
(2) for case (b), formalize the OMT / Prop 6.17–6.18 package — the most useful theorem is a module-level
closed-submodule / open-mapping theorem, not a one-off. Do not spend more time on an elementary workaround.
