/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import BoringLab.Epistemology.FairExperiment

/-!
# EPI.1.3: blinding as a Prop-carrier

Ticket #73 (child of EPI.1.1 #28): the landed `Experiment.blind : Bool` is a
self-reported flag; the actual content of blinding is that the analysis was
constructed before the observation was attached — as a claim, it enters as a
hypothesis-carrier `Prop` field, never as self-reported data (STYLE.D).
This module lands the upgrade as a NEW structure (the landed
`Experiment`/`blindCheck` stay as the decidable shadow):

* `BlindAll` — the blinding content as a `Prop`: the analysis gives the same
  verdict for any two registered hypotheses at EVERY outcome of the fixed
  outcome space (observation-independent — stronger than #28's
  single-observation `blindCheck`);
* `BlindedExperiment` — the experiment with the `Prop`-carrier blinding
  field (the typed trace standing in for "built before observation");
* `BlindedExperiment.blinded_verdict` — proved: at the actual observation,
  the verdict is hypothesis-independent;
* `falsifiableHyp_obs_independent` — proved: the falsifiability predicate
  does not read the observation (invariance under post-hoc observation
  selection — the honest content the Bool flag stood in for);
* the toy: the #28 coin instance, blinding proved outright (`rfl`).

## References
* [Fisher] R. A. Fisher, *The Design of Experiments*, 2nd ed., Oliver & Boyd,
  1935, ch. II (blinding: the analysis must not read the treatment
  identity).
* [Nosek et al.] B. A. Nosek et al., *Science* 348(6242):1422–1425, 2015
  (pre-registration: the analysis plan fixed before data).
* Program register: BoringLab tickets #28 (EPI.1.1, landed) and #73
  (EPI.1.3); the toy is the #28 coin experiment, the program's own.
-/

namespace BoringLab

/-! ## Blinding as a Prop-carrier -/

-- Reference: ticket #73, item (i); [Fisher], ch. II — the analysis does not
-- read hypothesis identity, at ANY outcome of the fixed outcome space
-- (observation-independent, stronger than #28's `blindCheck` at one
-- observation).
/-- **Blinding as a `Prop`-carrier**: the analysis function gives the same
verdict for any two registered hypotheses at every outcome of the fixed
outcome space. -/
def BlindAll {hyp outcome : Type} (hs : List hyp) (os : List outcome)
    (a : hyp → outcome → Bool) : Prop :=
  ∀ o ∈ os, ∀ h1 ∈ hs, ∀ h2 ∈ hs, a h1 o = a h2 o

-- Reference: ticket #73, item (i): the experiment with the Prop-carrier
-- blinding field (the analysis is a phase-two parameter; the blinding claim
-- enters as a typed hypothesis-carrier field, never self-reported data).
/-- A **blinded experiment**: the #28 phase-one/phase-two fields, with
blinding as the `Prop`-carrier field `blindAll` (a typed trace of
"analysis built before observation"). -/
structure BlindedExperiment (hyp outcome : Type) where
  /-- Phase one: the outcome space, fixed before any observation. -/
  outcomes : List outcome
  /-- Phase one: the hypothesis family. -/
  hypotheses : List hyp
  /-- Phase one: the pre-registered prediction table. -/
  predict : hyp → List (ℚ × outcome)
  /-- Phase two: the analysis function (a parameter — built before the
  observation is attached). -/
  analysis : hyp → outcome → Bool
  /-- Phase two: the observation record. -/
  observation : outcome
  /-- The blinding carrier: `BlindAll` over the outcome space. -/
  blindAll : BlindAll hypotheses outcomes analysis

-- Reference: [Barendregt], ch. 2 (eta conversion), as in `Experiment.eta`.
-- REVIEW(citation): pin down the exact section in review.
/-- **Eta conversion for blinded experiments**. -/
theorem BlindedExperiment.eta {hyp outcome : Type} (e : BlindedExperiment hyp outcome) :
    BlindedExperiment.mk e.outcomes e.hypotheses e.predict e.analysis e.observation
      e.blindAll = e := by
  cases e with
  | mk outcomes hypotheses predict analysis observation blindAll => rfl

-- Reference: ticket #73, item (ii) — the blinding theorem: at the actual
-- observation, the verdict is hypothesis-independent (from `blindAll` at the
-- observation, which lies in the outcome space).
/-- **Blinded verdict**: in a blinded experiment whose observation lies in
the outcome space, the analysis gives the same verdict for any two
registered hypotheses. -/
theorem BlindedExperiment.blinded_verdict {hyp outcome : Type}
    (e : BlindedExperiment hyp outcome) (hobs : e.observation ∈ e.outcomes)
    {h1 h2 : hyp} (hh1 : h1 ∈ e.hypotheses) (hh2 : h2 ∈ e.hypotheses) :
    e.analysis h1 e.observation = e.analysis h2 e.observation :=
  e.blindAll e.observation hobs h1 hh1 h2 hh2

-- Reference: ticket #73, item (ii) — proved: #28's `falsifiableHyp` reads
-- only `outcomes`/`predict`/`hypotheses`, never the observation — so it is
-- invariant under post-hoc observation selection (two experiments differing
-- only in the observation record have the same falsifiability predicate).
/-- The falsifiability predicate is independent of the observation record. -/
theorem falsifiableHyp_obs_independent {hyp outcome : Type} [DecidableEq outcome]
    (e e' : Experiment hyp outcome)
    (ho : e.outcomes = e'.outcomes) (_hh : e.hypotheses = e'.hypotheses)
    (hp : e.predict = e'.predict) (h : hyp) :
    Experiment.falsifiableHyp e h = Experiment.falsifiableHyp e' h := by
  have h1 : Experiment.falsifiableHyp e h = falsifiable e.outcomes (e.predict h) := rfl
  have h2 : Experiment.falsifiableHyp e' h = falsifiable e'.outcomes (e'.predict h) := rfl
  exact h1.trans ((congrArg (fun o => falsifiable o (e.predict h)) ho).trans
    ((congrArg (fun p => falsifiable e'.outcomes p) (congrArg (fun f => f h) hp)).trans h2.symm))

/-! ## Toy: the #28 coin experiment, blinded outright -/

-- Reference: ticket #73, toy: the #28 coin analysis reports only whether
-- the observed flip is heads — it never reads the hypothesis — so `BlindAll`
-- holds by `rfl` at every outcome.
/-- The toy blinded coin experiment: the #28 phase-one fields, the coin
analysis, observation `heads`, and the blinding carrier proved outright. -/
def coinBlinded : BlindedExperiment CoinHyp Coin where
  outcomes := coinOutcomes
  hypotheses := coinHypotheses
  predict := coinPredict
  analysis := coinAnalysis
  observation := Coin.heads
  blindAll := fun _ _ _ _ _ _ => rfl

-- Reference: ticket #73, toy: the blinded verdict at the toy observation
-- (from `blinded_verdict` with `Coin.heads ∈ coinOutcomes`).
/-- The toy's blinded verdict: the analysis agrees on `fair` and `loaded`. -/
theorem coinBlinded_verdict :
    coinBlinded.analysis CoinHyp.fair Coin.heads =
      coinBlinded.analysis CoinHyp.loaded Coin.heads :=
  coinBlinded.blinded_verdict List.mem_cons_self List.mem_cons_self
    (List.mem_cons_of_mem CoinHyp.fair (List.mem_cons_of_mem CoinHyp.biased
      List.mem_cons_self))

end BoringLab
