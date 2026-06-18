# Reply integration — 2026-06-18

Reply received from an Iwasawa-theory specialist on 2026-06-18.
Brief: ./brief.md   Reply: ./reply.md

## Interpretation summary

| Q | Verdict |
|---|---------|
| Q1 (Coleman/Chebotarev shortcut) | NO — kernel = closure of global units IS p-ramified global reciprocity. |
| Q2 (minus-side + Kummer duality) | YES, the genuine bypass; uses direct-limit class groups + reflection + adjoint; reflected ODD components; NOT a Vandiver shortcut (≈ full MC). |
| Q3 (Euler system avoids 𝓜⁺) | YES for the class-group MC; NO for the 𝒳⁺ translation without a bridge. |
| Q4 (intrinsic vs exposition) | The exact sequence is not intrinsic; SOME global bridge is. Vandiver→Wa Cor 13.6 minimal. |
| Q5 (Selmer) | Cleanest architecture, but LARGER now (local Tate duality + Poitou–Tate). |
| Q6 (axiomatise) | YES — but the right boundary is a general/standard CFT statement, derived down to the special case. |

Plus a user-driven refinement after the reply: state the assumption as the **general classical CFT theorem**
(ray-class form), not a cyclotomic-tower specialisation, so a future global-CFT library discharges it by
instantiation. (User choice: ray-class / ideal-theoretic form.)

## Changes applied

- **G2 restructured** into: `[G2-CFT]` (the one axiom — general ray-class Artin reciprocity + existence +
  conductor, arbitrary number fields, in `Common/ClassFieldTheory.lean`); `[G2-RAYSEQ]` (PROVEN, elementary
  ray-class/units/class-group sequence); `[G2-DEDUCE]` (PROVEN from G2-CFT — the cyclotomic CFTunits1 sequence);
  `[G2-LIMIT]` (PROVEN — inverse limit via Mittag–Leffler).
- **G-DEF** updated: `IwasawaGaloisData` carries Galois-theoretic/structural data only; CFT content moved to
  `[G2-CFT]`; `galoisSES` clarified as fundamental-Galois-theory, not CFT.
- **G4** dependency: `G2` → `G2-LIMIT`.
- **`[G2-DISCHARGE]`** added (deferred): instantiate `ClassFieldTheory` from mathlib's future CFT, or via the
  reviewer's route (tower Euler system + Kummer pairing/reflection NSW 11.4.3 / Wa 13.32 + Iwasawa adjoint).
- **S13-E re-scoped**: Euler system proves the class-group MC but needs a bridge to reach 𝒳⁺ ⇒ ingredient of
  `[G2-DISCHARGE]` route (b), not an independent IMC path; not needed for Vandiver.
- **S13-M re-scoped**: absorbed into G-IMC for Vandiver; the full-IMC assembly belongs to route (b).
- **Cluster header** + **plan-G.md** updated with the general-interface decision and added references.

## Decisions recorded but not actioned

- Selmer/Greenberg reformulation (Q5): not pursued at this stage (larger than the CFT black box).
- Full-IMC-without-CFT: deferred as `[G2-DISCHARGE]` route (b); not on the Vandiver critical path.

## References added (plan-G.md)

NSW *Cohomology of Number Fields* Thm 11.4.3; Washington Prop 13.32 (+ Cor 13.6, Ch. 15); Aoki (Gauss-sum
Euler system); Selecta "Fitting ideals of p-ramified Iwasawa modules".

## Net effect

The Stage-G assumed surface is now a **single general classical CFT theorem** (`[G2-CFT]`), with CFTunits1 and
its inverse-limit derived (proven). Forward-compatible: discharge = instantiate the interface against future
mathlib global CFT. Vandiver target unchanged.
