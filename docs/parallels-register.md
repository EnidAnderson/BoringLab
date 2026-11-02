# LAB PARALLELS.0 — the parallels register

Issue: `EnidAnderson/BoringLab#139`. Purpose: record the TRUE stable
connections between related fields of the program as rows with EXPLICIT
structure — the functor / ledger / category / doctrine that realizes the
parallel — graded `proved` / `statement-layer` / `speculative`. Never a
free analogy (anti-crank battery clause 3). A row may be deleted if no
explicit structure realizes it.

## Rows (each names the shared structure and the landed module)

| # | Parallel | Shared structure | Modules | Grade |
|---|---|---|---|---|
| 1 | Rules of play = geometric logic (GL.0 #14) | declared moves between parallel paths = geometric sequents | `Doctrine/GameDoctrine.lean`, `Doctrine/Geometric.lean` | proved (witness + inversion) |
| 2 | Game computads (L-line) ↔ GL doctrines | graded game computads with declared outcome moves | L-line (#100/#111, parallel lane) ↔ `GameDoctrine.lean` | statement-layer (connection row not yet landed) |
| 3 | Typed holes/plugging (PD.1 #15) ↔ sieves/coverages (GL.0.1/0.2 #70/#69) | a plug = a path into a hole; a covering sieve = the certified fills | `Doctrine/PropSieve.lean`, `Doctrine/CdStruct.lean` vs PD.1 (parallel lane) | speculative — record, do not assert |
| 4 | Hyperdoctrine fibers ↔ observables-as-periods (EPI.7 #36/#37) | predicates = endo-paths at the fiber root; prediction map on fiber data | `Doctrine/Geometric.lean` (`Hyperdoctrine`), `Epistemology/LocationMap.lean` | proved at toy level (`nimHyperdoctrine`, `coinLocation`) |
| 5 | Truncation regimes (EPI.8.6 #64) ↔ EPI.8.0 principle (#40) | level-indexed truncations + transfer cocycle | `Epistemology/Regime.lean`, `RegimeCocycle.lean` | proved (cocycle), holes declared |
| 6 | Lisp macro table ↔ doctrine localization ↔ META.0 (#68/#3/#72) | macros = declared moves; localization inverts exactly the macro table; doctrine-of-doctrines 2-layer | `Lisp/Macro.lean`, `Lisp/Expand.lean`, `Doctrine/Localization.lean`, `Doctrine/Meta.lean` | proved (`macroexpand1_move`, `misereQuotient_generator_inverted`, `substMorph`) |
| 7 | L∞ presentations ↔ deformation problems (#109/#108) | brackets `lₙ` = (n,1)-operations; MC equation = the deformation functor's shadow | `Deform/LInf.lean`, `Deform/Deform.lean`, `Deform/BarCobar.lean` | statement-layer; `shuffleSum`/`elemSubst` named holes |
| 8 | Holographic equation ↔ computadic moves (Physics #356, BoringMath) | `boundaryInfo ∘ hologram = bulkInfo` as a declared move | BoringMath `Physics/MotivicHolographicInfo.lean` (parallel lane); guidance ticket BoringMath #350 | speculative until the computadic presentation row lands |
| 9 | Semicategories ↔ computads (#112) | comp-level theorems need no identities; categories = computads + `CatData` | `Doctrine/Semicat.lean`, `Doctrine/Morph.lean` | proved (`comp_assoc`) |
| 10 | Fair-experiment levels ↔ regime levels ↔ process rounds (#28/#64/#29, row for #65(a)) | level-`n` data length = n = rounds counted by the log | `Epistemology/RegimeExperiment.lean` | proved (`listRegime_tracks`, `runOn_log_length`) |
| 11 | Games as hyperdoctrine fibers (GL.0 ↔ L-line) | fiber = `gameDoctrine neutral`, root = zero game, subst = identity | `Doctrine/GameHyperdoctrine.lean` | proved (instance + `neutral_transport`) |
| 12 | Vanishing statements ↔ falsifiability (MI.0.1 #67 ↔ EPI.1.1 #28, row for #65(c)) | `coinMI.vanishing h ↔ falsifiableHyp coinExperiment h` | `Epistemology/MIReflexive.lean` | proved |
| 13 | 2-dimensional ports / properads (#113) | `Port2` (m,n)-pasting; `Computad2` with declared 2-cells; operads = (m,1) | `Doctrine/Computad2.lean` | statement-layer (skeleton, laws proved) |
| 14 | Bar/cobar = path composition (#108) | word computad; concatenation = path composition | `Deform/BarCobar.lean` | proved (`wordPath_append`); `barDifferential` named hole |
| 15 | Unshuffles ↔ Jacobi sums (#109) | `unshuffles`, `jacobiTrees` | `Deform/Jacobi.lean` | proved (combinatorics); bracket assembly named hole |
| 16 | Bayesian ledger ↔ game value process (#167) | `ConservedMassProcess` (value/next/law; conservation law) | `Epistemology/Bayes.lean` (EPI side: `bayesUpdate_conservation` proved; coin toy 3 = 3) ↔ `Games/Trace.lean` (games side: statement-layer — Trace unverified at pin session, do-not-import) | proved (EPI side) / statement-layer (games side) |

## Rules

- Every row names the exact shared structure (never "X is like Y").
- Grades: `proved` (a landed theorem), `statement-layer` (structures
  landed, theorems are named holes), `speculative` (reading only).
- Conservative checking: delete a row that cannot name its structure.
