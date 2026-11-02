# LAB HOC.0 — higher-computadic promotion register

Issue: `EnidAnderson/BoringLab#110`. User steering (2026-11-02): always
aim for the higher-categorical / higher-computadic "pure composition"
forms; promote BoringLab code from set-theoretic or category-theoretic
shapes to the appropriate computadic forms. The promotion law: new
structures are written FIRST in the pure-composition form (computad +
declared moves on paths / formal sums of paths), with the
set/category-level form as the declared shadow; landed files are never
rewritten in place without review — promotions are additive modules.

## Register (landed rows)

| Structure | From-shape | To-shape (pure composition) | Landed |
|---|---|---|---|
| Sieve membership | `Sieve.arrows : … → Bool` (decidable fragment) | `PropSieve.arrows : … → Prop` + upgrade map `Sieve.toProp` | #70, `Doctrine/PropSieve.lean` |
| Blinding | `Experiment.blind : Bool` (self-reported flag) | `BlindAll` Prop-carrier, `BlindedExperiment` | #73, `Epistemology/Blinding.lean` |
| Doctrine quotient semantics | mathlib `CategoryTheory.Localization` (choice-tainted, Prop-only) | the computad localization = path category quotiented by declared moves (data level, `Doctrine.moveClass`) | #3; promotion rule: never consume chosen categorical data in `def`s |
| Rules of play | games as trees | `gameComputad` + `gameDoctrine` (moves as generators, neutral simplifications as sequents) | #14, `Doctrine/GameDoctrine.lean` |
| Lisp macros | macro table as functions | macros as declared moves between paths (`macroDoctrine`, `callDoctrine`) | #68, `Lisp/Macro.lean`, `Lisp/Expand.lean` |
| L∞ algebras | operations + Jacobi equations | `linfComputad` + relations on formal sums of paths | #109, `Deform/LInf.lean` |
| Deformation problems | functors on artinian rings | deformation doctrine over thickenings; MC locus as localization shadow | #108 (charter, statement layer next) |

## Open promotion rows (named holes)

- `TheoryLink` / theory-element category: the pure-composition form is a
  computad of theory-elements with links as generators — statement layer.
- Regime category (#64): already composition-shaped (level maps + transfer
  terms); the higher form adds 2-cells between regime maps (transfer-term
  homotopies) — named hole.
- Localization statements: keep `Nonempty (Iso …)` Prop-only forms; the
  computad-level shadow is `declared_move_inverted` (data).
