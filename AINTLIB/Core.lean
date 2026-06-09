-- Forces the cited mathlib number-theory declarations into the build so the
-- blueprint's (lean := "Mathlib.NumberTheory.…") references resolve and are
-- auto-tracked as sorry-free. Grows as chapters are authored.
import Mathlib.NumberTheory.LucasLehmer
