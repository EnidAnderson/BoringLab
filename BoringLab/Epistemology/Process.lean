/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import BoringLab.Epistemology.FairExperiment

/-!
# The scientific process as a computable state machine

Ticket #29 (EPI.1.2), building on the fair-experiment carrier of #28
(EPI.1.1, `BoringLab.Epistemology.FairExperiment`): the scientific cycle
HYPOTHESIS → PREDICTION → FAIR EXPERIMENT → COMPARISON → (UPDATE | FALSIFIED)
as explicit states `SciPhase` and decidable transitions `SciPhase.next`; the
update rule as an explicit Bayesian count-table `bayesUpdate` (the computable
shadow of Bayesian inference — a count ledger, no measure theory, said
honestly); and the meta-science theorem that is provable at this level:
under the fixed update rule a falsified hypothesis never resurrects
(`falsified_never_resurrects` — zero weight is absorbing), with replication
as re-running the machine (`runOn`).

Honesty ledger (item (d) of the ticket): what this model deliberately does
NOT capture is declared here, not sneered at — theory choice among
non-falsified hypotheses, paradigms, and the social process are out of
scope of the state machine (they enter later as the EPI.2/EPI.5 lines).

## References
* [Popper] K. R. Popper, *The Logic of Scientific Discovery*, New York: Basic
  Books, 1959 (English translation of *Logik der Forschung*, 1934), ch. IV
  "Falsifiability" (conjectures and refutations; an observation incompatible
  with the theory refutes it).
* [Lakatos] I. Lakatos, *Falsification and the Methodology of Scientific
  Research Programmes*, 1970 — named here for the honest-absence ledger:
  research programmes are out of scope of this machine.
* [Kolmogorov] A. N. Kolmogorov, *Foundations of the Theory of Probability*,
  2nd English ed., Chelsea, 1956, ch. I, §1 (distributions on finite spaces as
  weight tables — the count-table shadow of the Bayesian update).
* Program register: BoringLab ticket #29 (EPI.1.2); the toy run is item (a)/(c)
  of the acceptance, the program's own.
-/

namespace BoringLab

/-! ## The cycle: phases and decidable transitions -/

-- Reference: program register ticket #29, item (a) — the cycle
-- HYPOTHESIS → PREDICTION → EXPERIMENT → COMPARISON → UPDATE/FALSIFIED as
-- the program's own state-machine reading of [Popper], ch. IV.
-- REVIEW(citation): pin the Popper chapter reference in review.
/-- The phases of one round of the scientific cycle, as data. -/
inductive SciPhase where
  /-- A hypothesis is conjectured. -/
  | hypothesis
  /-- Predictions are pre-registered (phase one of #28). -/
  | prediction
  /-- A fair experiment is run (phase two of #28). -/
  | experiment
  /-- The observation is compared against the prediction table. -/
  | comparison
  /-- The count ledger is updated. -/
  | update
  /-- The current hypothesis is falsified by the observation. -/
  | falsified

-- Reference: ticket #29, item (a) (explicit decidable transitions); the
-- comparison step branches on the decidable refutation flag.
/-- The decidable phase transition of one cycle step: the comparison phase
branches on the refutation flag; the falsified phase is absorbing. -/
def SciPhase.next (refuted : Bool) : SciPhase → SciPhase
  | .hypothesis => .prediction
  | .prediction => .experiment
  | .experiment => .comparison
  | .comparison => match refuted with | true => .falsified | false => .update
  | .update => .hypothesis
  | .falsified => .falsified

-- Reference: computation step of `SciPhase.next`; `rfl` is permitted only in
-- such primitive definitional lemmas.
/-- The falsified phase is absorbing under every transition. -/
theorem SciPhase.next_falsified (refuted : Bool) :
    SciPhase.next refuted .falsified = .falsified := rfl

-- Reference: computation step of `SciPhase.next`.
/-- The comparison phase moves to falsified exactly when the refutation flag
is set. -/
theorem SciPhase.next_comparison_refuted :
    SciPhase.next true .comparison = .falsified := rfl

-- Reference: computation step of `SciPhase.next`.
/-- The comparison phase moves to update when the refutation flag is unset. -/
theorem SciPhase.next_comparison_update :
    SciPhase.next false .comparison = .update := rfl

/-! ## The Bayesian count-table ledger -/

-- Reference: [Kolmogorov], ch. I, §1 (a finite distribution as a weight
-- table); ticket #29, item (b): the count-table update is the computable
-- shadow of Bayesian inference — no measure theory.
-- REVIEW(citation): pin the Kolmogorov page in review.
/-- The weight of a hypothesis in the count-table ledger (an association
list); a hypothesis absent from the list carries weight `0`. -/
def ledgerWeight {hyp : Type} [DecidableEq hyp] : List (hyp × ℚ) → hyp → ℚ
  | [], _ => 0
  | p :: rest, h => if p.1 = h then p.2 else ledgerWeight rest h

-- Reference: computation step of `ledgerWeight` (core `if` on the decidable
-- equality); `rfl` only in this primitive definitional lemma.
/-- The weight of a hypothesis at the head of the ledger, when it matches. -/
theorem ledgerWeight_cons_same {hyp : Type} [DecidableEq hyp] (p : hyp × ℚ)
    (rest : List (hyp × ℚ)) (h : hyp) (he : p.1 = h) :
    ledgerWeight (p :: rest) h = p.2 := by
  show (if p.1 = h then p.2 else ledgerWeight rest h) = p.2
  exact ite_eq_left he

-- Reference: computation step of `ledgerWeight` (core `if` on the decidable
-- equality).
/-- The weight of a hypothesis past a non-matching head of the ledger. -/
theorem ledgerWeight_cons_diff {hyp : Type} [DecidableEq hyp] (p : hyp × ℚ)
    (rest : List (hyp × ℚ)) (h : hyp) (hn : p.1 ≠ h) :
    ledgerWeight (p :: rest) h = ledgerWeight rest h := by
  show (if p.1 = h then p.2 else ledgerWeight rest h) = ledgerWeight rest h
  exact ite_eq_right hn

-- Reference: computation step of `ledgerWeight`.
/-- The weight of any hypothesis in the empty ledger is zero. -/
theorem ledgerWeight_nil {hyp : Type} [DecidableEq hyp] (h : hyp) :
    ledgerWeight ([] : List (hyp × ℚ)) h = 0 := rfl

-- Reference: [Kolmogorov], ch. I, §1 (the likelihood of an observation is
-- the mass the distribution assigns to it); ticket #29, item (b).
-- REVIEW(citation): as on `ledgerWeight`.
/-- The **Bayesian count-table update**: on observation `o`, every
hypothesis's weight is multiplied by the prediction mass of `o` under that
hypothesis (unnormalized — the raw count ledger). -/
def bayesUpdate {hyp outcome : Type} [DecidableEq outcome]
    (predict : hyp → List (ℚ × outcome)) (o : outcome) :
    List (hyp × ℚ) → List (hyp × ℚ)
  | [] => []
  | p :: rest => (p.1, p.2 * tableMass (predict p.1) o) :: bayesUpdate predict o rest

-- Reference: computation step of `bayesUpdate`; `rfl` only in this primitive
-- definitional lemma.
/-- The count-table update on a cons cell. -/
theorem bayesUpdate_cons {hyp outcome : Type} [DecidableEq outcome]
    (predict : hyp → List (ℚ × outcome)) (o : outcome) (p : hyp × ℚ)
    (rest : List (hyp × ℚ)) :
    bayesUpdate predict o (p :: rest) =
      (p.1, p.2 * tableMass (predict p.1) o) :: bayesUpdate predict o rest := rfl

-- Reference: ticket #29, item (c) — the ledger update law: the weight of
-- `h` after the update is its old weight times the likelihood of `o`.
/-- **The count-table update law**: the weight of `h` after a Bayesian update
is its previous weight times the prediction mass of the observation. -/
theorem ledgerWeight_bayesUpdate {hyp outcome : Type} [DecidableEq hyp] [DecidableEq outcome]
    (predict : hyp → List (ℚ × outcome)) (o : outcome) (l : List (hyp × ℚ)) (h : hyp) :
    ledgerWeight (bayesUpdate predict o l) h =
      ledgerWeight l h * tableMass (predict h) o := by
  induction l with
  | nil => exact (zero_mul (tableMass (predict h) o)).symm
  | cons p rest ih =>
      have e1 : bayesUpdate predict o (p :: rest) =
          (p.1, p.2 * tableMass (predict p.1) o) :: bayesUpdate predict o rest := rfl
      cases (inferInstance : Decidable (p.1 = h)) with
      | isTrue he =>
          have hm : tableMass (predict p.1) o = tableMass (predict h) o :=
            congrArg (fun x => tableMass (predict x) o) he
          have hL : ledgerWeight
              ((p.1, p.2 * tableMass (predict p.1) o) :: bayesUpdate predict o rest) h =
              p.2 * tableMass (predict h) o :=
            (ledgerWeight_cons_same (p.1, p.2 * tableMass (predict p.1) o)
              (bayesUpdate predict o rest) h he).trans (congrArg (fun x => p.2 * x) hm)
          have hR : ledgerWeight (p :: rest) h = p.2 := ledgerWeight_cons_same p rest h he
          exact Eq.subst
            (motive := fun l => ledgerWeight l h =
              ledgerWeight (p :: rest) h * tableMass (predict h) o) e1
            (hL.trans (congrArg (fun x => x * tableMass (predict h) o) hR.symm))
      | isFalse hn =>
          have hL : ledgerWeight
              ((p.1, p.2 * tableMass (predict p.1) o) :: bayesUpdate predict o rest) h =
              ledgerWeight (bayesUpdate predict o rest) h :=
            ledgerWeight_cons_diff (p.1, p.2 * tableMass (predict p.1) o)
              (bayesUpdate predict o rest) h hn
          have hR : ledgerWeight (p :: rest) h = ledgerWeight rest h :=
            ledgerWeight_cons_diff p rest h hn
          exact Eq.subst
            (motive := fun l => ledgerWeight l h =
              ledgerWeight (p :: rest) h * tableMass (predict h) o) e1
            ((hL.trans ih).trans
              (congrArg (fun x => x * tableMass (predict h) o) hR).symm)

-- Reference: ticket #29, item (c) — monotonicity of the count ledger:
-- `0 * m = 0` (core `zero_mul`), so zero weight is absorbing.
/-- **Falsified hypotheses never resurrect**: under the fixed update rule, a
hypothesis of weight zero keeps weight zero after any observation. -/
theorem falsified_never_resurrects {hyp outcome : Type} [DecidableEq hyp]
    [DecidableEq outcome] (predict : hyp → List (ℚ × outcome)) (o : outcome)
    (l : List (hyp × ℚ)) (h : hyp) (hz : ledgerWeight l h = 0) :
    ledgerWeight (bayesUpdate predict o l) h = 0 :=
  (ledgerWeight_bayesUpdate predict o l h).trans
    ((congrArg (fun x => x * tableMass (predict h) o) hz).trans
      (zero_mul (tableMass (predict h) o)))

-- Reference: [Popper], ch. IV, §21 (refutation: a possible observation
-- incompatible with the theory); from #28's `tableMass` and `isZeroQ`.
-- REVIEW(citation): as on `Experiment.falsifiableHyp` (#28).
/-- The decidable **refutation test**: the observation `o` has zero prediction
mass under hypothesis `h` — the observation refutes `h`. -/
def refutedBy {hyp outcome : Type} [DecidableEq outcome]
    (predict : hyp → List (ℚ × outcome)) (h : hyp) (o : outcome) : Bool :=
  isZeroQ (tableMass (predict h) o)

-- Reference: from `isZeroQ_eq_true` (#28).
/-- The refutation test is true exactly when the prediction mass is zero. -/
theorem refutedBy_eq_true {hyp outcome : Type} [DecidableEq outcome]
    (predict : hyp → List (ℚ × outcome)) (h : hyp) (o : outcome) :
    refutedBy predict h o = true ↔ tableMass (predict h) o = 0 :=
  isZeroQ_eq_true (tableMass (predict h) o)

/-! ## The state machine -/

-- Reference: ticket #29, item (a): the cycle as a computable state machine.
/-- The state of the scientific process: the current phase, the working
hypothesis, the Bayesian count-table ledger, and the observation log
(the replication record). -/
structure SciState (hyp outcome : Type) where
  /-- The current phase of the cycle. -/
  phase : SciPhase
  /-- The working hypothesis. -/
  current : hyp
  /-- The Bayesian count-table ledger. -/
  ledger : List (hyp × ℚ)
  /-- The observation log (one entry per round run). -/
  log : List outcome

-- Reference: [Barendregt], ch. 2 (eta conversion), as in
-- `BoringLab.Game.eta` and `Experiment.eta`.
-- REVIEW(citation): pin down the exact section in review.
/-- **Eta conversion for process states**: a state equals the state assembled
from its components. -/
theorem SciState.eta {hyp outcome : Type} (s : SciState hyp outcome) :
    SciState.mk s.phase s.current s.ledger s.log = s := by
  cases s with
  | mk phase current ledger log => rfl

-- Reference: ticket #29, items (a)–(c): one round — compare the observation
-- against the prediction table, update the ledger, advance the phase.
/-- **One round of the cycle** at observation `o`: the ledger is updated by
the count-table rule, the observation is logged, and the phase advances
through the (decidable) comparison branch. -/
def SciState.round {hyp outcome : Type} [DecidableEq outcome]
    (predict : hyp → List (ℚ × outcome)) (s : SciState hyp outcome) (o : outcome) :
    SciState hyp outcome :=
  SciState.mk (SciPhase.next (refutedBy predict s.current o) s.phase) s.current
    (bayesUpdate predict o s.ledger) (o :: s.log)

-- Reference: computation step (projection of `SciState.round`); `rfl` only in
-- such primitive definitional lemmas.
/-- The phase of a round is the cycle transition at the refutation flag. -/
theorem SciState.round_phase {hyp outcome : Type} [DecidableEq outcome]
    (predict : hyp → List (ℚ × outcome)) (s : SciState hyp outcome) (o : outcome) :
    (s.round predict o).phase =
      SciPhase.next (refutedBy predict s.current o) s.phase := rfl

-- Reference: computation step (projection of `SciState.round`).
/-- The ledger of a round is the count-table update of the old ledger. -/
theorem SciState.round_ledger {hyp outcome : Type} [DecidableEq outcome]
    (predict : hyp → List (ℚ × outcome)) (s : SciState hyp outcome) (o : outcome) :
    (s.round predict o).ledger = bayesUpdate predict o s.ledger := rfl

-- Reference: computation step (projection of `SciState.round`).
/-- The log of a round is the observation prepended to the old log. -/
theorem SciState.round_log {hyp outcome : Type} [DecidableEq outcome]
    (predict : hyp → List (ℚ × outcome)) (s : SciState hyp outcome) (o : outcome) :
    (s.round predict o).log = o :: s.log := rfl

-- Reference: ticket #29, item (c) — monotonicity at the state level, from
-- `falsified_never_resurrects` via `SciState.round_ledger`.
/-- **Falsified stays falsified at the state level**: if the working hypothesis
has zero weight, one round keeps it at zero weight. -/
theorem SciState.round_falsified_stays_zero {hyp outcome : Type}
    [DecidableEq hyp] [DecidableEq outcome]
    (predict : hyp → List (ℚ × outcome)) (s : SciState hyp outcome) (o : outcome)
    (hz : ledgerWeight s.ledger s.current = 0) :
    ledgerWeight (s.round predict o).ledger s.current = 0 :=
  Eq.subst (motive := fun l => ledgerWeight l s.current = 0)
    (SciState.round_ledger predict s o).symm
    (falsified_never_resurrects predict o s.ledger s.current hz)

-- Reference: ticket #29, item (a) — the falsified phase is absorbing, from
-- `SciPhase.next_falsified` via `SciState.round_phase`.
/-- **The falsified phase is absorbing at the state level**: once falsified,
every further round stays in the falsified phase. -/
theorem SciState.round_falsified_absorbing {hyp outcome : Type} [DecidableEq outcome]
    (predict : hyp → List (ℚ × outcome)) (s : SciState hyp outcome) (o : outcome)
    (hf : s.phase = .falsified) : (s.round predict o).phase = .falsified :=
  (SciState.round_phase predict s o).trans
    (Eq.subst (motive := fun p => SciPhase.next (refutedBy predict s.current o) p = .falsified)
      hf.symm (SciPhase.next_falsified (refutedBy predict s.current o)))

-- Reference: ticket #29, item (c): replication as re-running the machine.
/-- **Replication run**: re-running the machine on a list of observations
(each round a fresh experiment with the same pre-registered table). -/
def runOn {hyp outcome : Type} [DecidableEq outcome]
    (predict : hyp → List (ℚ × outcome)) (s : SciState hyp outcome) :
    List outcome → SciState hyp outcome
  | [] => s
  | o :: os => runOn predict (s.round predict o) os

-- Reference: computation step of `runOn`.
/-- The empty replication run is the identity. -/
theorem runOn_nil {hyp outcome : Type} [DecidableEq outcome]
    (predict : hyp → List (ℚ × outcome)) (s : SciState hyp outcome) :
    runOn predict s [] = s := rfl

-- Reference: computation step of `runOn`.
/-- A replication run on a cons of observations. -/
theorem runOn_cons {hyp outcome : Type} [DecidableEq outcome]
    (predict : hyp → List (ℚ × outcome)) (s : SciState hyp outcome) (o : outcome)
    (os : List outcome) :
    runOn predict s (o :: os) = runOn predict (s.round predict o) os := rfl

/-! ## The uniform initial ledger -/

-- Reference: ticket #29, item (b): the count-table starts uniform (each
-- registered hypothesis at weight one) — the computable shadow of a uniform
-- prior on the bounded family.
/-- The uniform ledger on a hypothesis family: each hypothesis at weight
`1`. -/
def uniformLedger {hyp : Type} (hs : List hyp) : List (hyp × ℚ) :=
  hs.map fun h => (h, 1)

-- Reference: core `List.mem_cons` plus the `ledgerWeight` cons lemmas;
-- induction on the family.
/-- Every hypothesis of the family has weight `1` in the uniform ledger. -/
theorem ledgerWeight_uniform {hyp : Type} [DecidableEq hyp] :
    ∀ (l : List hyp) (h : hyp), h ∈ l → ledgerWeight (uniformLedger l) h = 1
  | [], h, hh => absurd hh List.not_mem_nil
  | x :: rest, h, hh => by
      cases (inferInstance : Decidable (x = h)) with
      | isTrue he => exact ledgerWeight_cons_same (x, (1 : ℚ)) (uniformLedger rest) h he
      | isFalse hn =>
          rcases List.mem_cons.mp hh with he | hr
          · exact absurd he.symm hn
          · exact (ledgerWeight_cons_diff (x, (1 : ℚ)) (uniformLedger rest) h hn).trans
              (ledgerWeight_uniform rest h hr)

/-! ## Toy run: the coin family, two experiment rounds (D.5 witness) -/

-- Reference: ticket #29, acceptance — the state machine runs on a toy case
-- via `#eval`: the #28 coin family, the working hypothesis `loaded`, six
-- rounds cycling the phases; the ledger and log are printed.
/-- The uniform ledger on the toy coin family. -/
def coinLedger : List (CoinHyp × ℚ) := uniformLedger coinHypotheses

-- Reference: ticket #29, toy (a): the initial state — hypothesis phase, the
-- loaded coin as working hypothesis.
/-- The initial state of the toy run. -/
def coinInit : SciState CoinHyp Coin :=
  SciState.mk .hypothesis CoinHyp.loaded coinLedger []

-- Reference: ticket #29, toy (c): two full cycles of observations
-- (heads, tails each cycle) — enough rounds to pass comparison twice.
/-- The toy observation schedule: two rounds of heads-then-tails. -/
def coinSchedule : List Coin :=
  [Coin.heads, Coin.tails, Coin.heads, Coin.tails, Coin.heads, Coin.tails]

-- Reference: ticket #29, toy (c): the replication run.
/-- The final state of the toy run. -/
def coinFinal : SciState CoinHyp Coin := runOn coinPredict coinInit coinSchedule

-- Reference: [Popper], ch. IV, §21; from #28's
-- `coinPredict_loaded_tails_mass` via `refutedBy_eq_true`.
-- REVIEW(citation): as on `refutedBy`.
/-- The loaded coin is refuted by observing tails (zero-mass cell). -/
theorem coin_loaded_refuted_by_tails :
    refutedBy coinPredict CoinHyp.loaded Coin.tails = true :=
  (refutedBy_eq_true coinPredict CoinHyp.loaded Coin.tails).mpr
    coinPredict_loaded_tails_mass

-- Reference: ticket #29, toy (a): printing support — the phase as a name
-- (no `Repr` instance is declared for `SciPhase`).
/-- The name of a phase, for printed toy runs. -/
def SciPhase.name : SciPhase → String
  | .hypothesis => "hypothesis"
  | .prediction => "prediction"
  | .experiment => "experiment"
  | .comparison => "comparison"
  | .update => "update"
  | .falsified => "falsified"

-- Reference: ticket #29, item (a) acceptance: the toy run printed — phase,
-- ledger, log, and per-hypothesis weights and falsifiability.
#eval (coinFinal.phase.name, coinFinal.ledger, coinFinal.log)
#eval coinHypotheses.map fun h =>
  (h, ledgerWeight coinFinal.ledger h, Experiment.falsifiableHyp coinExperiment h,
    refutedBy coinPredict h Coin.tails)

end BoringLab
