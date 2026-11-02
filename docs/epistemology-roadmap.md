# Epistemology roadmap — the EPI lane

Home doc for the EPI-line tickets in `EnidAnderson/BoringLab` (lab-tree root:
#2). Companion to `parallels-register.md` (cross-lane rows) and the SCI.0
brief (BoringMath #74 + lab SCI tickets). Status legend: **proved** /
**statement-layer** (structures landed, theorems are named holes) /
**speculative** (notes only) — anti-crank rules of LAB.0/#1 apply: every formal
target has (a) precise structure, (b) a named anchor, (c) a computable or
falsifiable shadow, or it is tagged [O] and parked.

## The truncation-learning seam (EPI.8.x — active)

Learning theory is truncation tracking: the identification-in-the-limit
program is "truncated data, tracked convergence" (#43's scope note). The
level ledger `mindChangesAtLevel` (#43) is the shared instrument.

| Ticket | Content | Module | Status |
|---|---|---|---|
| #43 (EPI.8.3) | truncated learning: level ledger, `TruncatedIdentification` | `Epistemology/TruncatedLearning.lean` | landed (proved: zero/mono/down; toy `#eval`) |
| #163 (EPI.8.4) | locking prefixes; level-ledger stabilization; level-n Gold bound | `Epistemology/Locking.lean` | in-flight (pr/epi-truncation-learning) |
| #164 (EPI.8.5) | sample complexity at level n; witness monotonicity; coin negative result | `Epistemology/SampleComplexity.lean` | in-flight (pr/epi-truncation-learning) |

## Proposed new projects (filed 2026-11, PREP until cut)

| Ticket | Project | Builds on | Grade target |
|---|---|---|---|
| #165 (EPI.9.1) | learning as a limit in the theory-element category | #62, #31, #43 | landed on pr/epi-truncation-learning (`LearningCat.lean`): hypTheory + specialization links proved (incl. negative), identification = limiting cone proved, `theoryElementCategory` instance PROVED (sorry-free), coin toy proved |
| #166 (SCI.0.1.2) | history as a data stream (Tycho→Kepler through the level ledger) | SCI.0.1 #74, #43, EPI.5.1-fix | proved toy, no world-claim |
| #167 (EPI.3.3) | Bayesian mass process = game value process (`ConservedMassProcess` + parallels row 16) | #31, TR.0 #10 | EPI half landed on pr/epi-truncation-learning (`Bayes.lean`: conservation proved, coin toy 3 = 3); games side statement-layer pending Trace verification |
| #168 (EPI.3.4) | description-length complexity in the lab's own Lisp (`Sexpr.size`) | #32, Lisp lane | landed on pr/epi-truncation-learning (`Complexity.lean`): size-Ockham picks the smaller description (proved, big listed first); named hole: general mind-change bound; relativization recorded |
| #169 (L.18.4) | value of information in games (mass moved vs game value) | L.18.2, #28, L.19.3 | toy-proved, negative results first-class |

## Standing rules for this lane

- Prop-valued predicates with a Bool shadow tied by proved lemmas (#31's
  pattern); hypotheses enter as binders/fields, never global axioms (lab law).
- Negative results are first-class deliverables (e.g. #164's loaded-coin
  non-identification witness; OckhamBound's `ockham_pointwise_minimality_fails`).
- Citations: REVIEW(citation) tag anything unpinned; route shared pins through
  BoringMath W5 (#13).
- Depth register and dependency edges live on the lab root tracker #2; line IDs
  here are provisional until the tree owner renumbers.
