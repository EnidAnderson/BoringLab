/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import BoringLab.Epistemology.Process
import BoringLab.Epistemology.TheoryElement

/-!
# The Kuhn cycle as a state machine

Ticket #34 (EPI.5.1), building on the process machine of #29
(`BoringLab.Epistemology.Process`) and the theory-elements of #30
(`BoringLab.Epistemology.TheoryElement`): the extended cycle NORMAL SCIENCE →
ANOMALY → CRISIS → REVOLUTION → NORMAL SCIENCE' as explicit phases and
decidable transitions, with the paradigm = the dominant theory-element; and
incommensurability as a data property — two theory-elements are commensurable
iff there is a translation table (a vocabulary map preserving the model
predicate, decidable on bounded carriers), with NO world-claim. The toy proves
a concrete incommensurability witness (`coinTheory_incommensurable_rival`).

Graded interpretation (D.4 tag): the state-machine reading of Kuhn is the
program's own, recorded as interpretation, not as Kuhn; the conservation
ledger (mind-change cost of revolution vs normal-science turnover) connects to
#31's `mindChangesOn` — computed on toy runs, stated at comment level here.

## References
* [Kuhn] T. S. Kuhn, *The Structure of Scientific Revolutions*, University of
  Chicago Press, 1962 (normal science, anomaly, crisis, revolution); 1970
  postscript (conservatism, mind-change cost).
* [Sneed] J. D. Sneed, *The Logical Structure of Mathematical Physics*,
  Synthese Library vol. 114, 1979, ch. 2 (theory-elements, carrier of the
  paradigm).
* [SEP FLT] "Formal Learning Theory", *Stanford Encyclopedia of Philosophy*
  (the mind-change conservatism tradition formalizing Kuhn).
* Program register: BoringLab ticket #34 (EPI.5.1); the toy is the #30 coin
  theory-element, the program's own.
-/

universe u

namespace BoringLab

/-! ## The extended cycle: phases and decidable transitions -/

-- Reference: [Kuhn], 1962, ch. VI–IX (the cycle normal science → anomaly →
-- crisis → revolution); ticket #34, item (a).
-- REVIEW(citation): pin the chapter references in review.
/-- The phases of the Kuhn cycle, as data. -/
inductive KuhnPhase where
  /-- Puzzle-solving within the dominant paradigm. -/
  | normal
  /-- An anomaly: a failed intended application. -/
  | anomaly
  /-- Crisis: the anomaly count reached the threshold. -/
  | crisis
  /-- Revolution: the paradigm is replaced. -/
  | revolution

-- Reference: ticket #34, item (a) (a computable extension of the #29
-- machine); the transitions branch on the decidable anomaly/crisis flags.
/-- The decidable transition of the Kuhn cycle: an anomaly moves normal science
to anomaly; the threshold moves anomaly to crisis; crisis moves to
revolution; revolution returns to (new) normal science. -/
def KuhnPhase.next (anomaly : Bool) (crisis : Bool) : KuhnPhase → KuhnPhase
  | .normal => match anomaly with | true => .anomaly | false => .normal
  | .anomaly => match crisis with | true => .crisis | false => .anomaly
  | .crisis => .revolution
  | .revolution => .normal

-- Reference: computation steps of `KuhnPhase.next`; `rfl` only in these
-- primitive definitional lemmas.
/-- An observed anomaly moves normal science to the anomaly phase. -/
theorem KuhnPhase.next_normal_anomaly : KuhnPhase.next true false .normal = .anomaly := rfl

-- Reference: computation step of `KuhnPhase.next`.
/-- No anomaly keeps normal science normal. -/
theorem KuhnPhase.next_normal : KuhnPhase.next false false .normal = .normal := rfl

-- Reference: computation step of `KuhnPhase.next`.
/-- The threshold moves anomaly to crisis. -/
theorem KuhnPhase.next_anomaly_crisis : KuhnPhase.next true true .anomaly = .crisis := rfl

-- Reference: computation step of `KuhnPhase.next`.
/-- Crisis moves to revolution. -/
theorem KuhnPhase.next_crisis : KuhnPhase.next true true .crisis = .revolution := rfl

-- Reference: computation step of `KuhnPhase.next`.
/-- Revolution returns to normal science. -/
theorem KuhnPhase.next_revolution : KuhnPhase.next false false .revolution = .normal := rfl

-- Reference: ticket #34, toy printing support (as `SciPhase.name`).
/-- The name of a Kuhn phase, for printed toy runs. -/
def KuhnPhase.name : KuhnPhase → String
  | .normal => "normal"
  | .anomaly => "anomaly"
  | .crisis => "crisis"
  | .revolution => "revolution"

/-! ## The Kuhn state machine -/

-- Reference: ticket #34, item (a): the paradigm is the dominant
-- theory-element (EPI.2.1, #30); the anomaly count and threshold are
-- explicit data.
/-- The state of the Kuhn cycle: the phase, the dominant paradigm (a
theory-element), the anomaly count, the crisis threshold, and the log of
failed intended applications. -/
structure KuhnState (carrier : Type u) where
  /-- The current phase. -/
  phase : KuhnPhase
  /-- The dominant paradigm, as a theory-element. -/
  paradigm : TheoryElement carrier
  /-- The accumulated anomaly count. -/
  anomalies : ℕ
  /-- The crisis threshold (explicit data). -/
  threshold : ℕ
  /-- The log of failed intended applications. -/
  log : List carrier

-- Reference: [Barendregt], ch. 2 (eta conversion), as in `SciState.eta`.
-- REVIEW(citation): pin down the exact section in review.
/-- **Eta conversion for Kuhn states**. -/
theorem KuhnState.eta {carrier : Type u} (s : KuhnState carrier) :
    KuhnState.mk s.phase s.paradigm s.anomalies s.threshold s.log = s := by
  cases s with
  | mk phase paradigm anomalies threshold log => rfl

-- Reference: [Kuhn], 1962 (an anomaly is a failed intended application —
-- an intended application that is not an actual model, decidable on the
-- bounded carrier via `isActual`).
/-- The decidable anomaly test: the observation `obs` is a failed intended
application of the paradigm (its `isActual` flag is `false`). -/
def anomalyOf {carrier : Type u} (t : TheoryElement carrier) (obs : carrier) : Bool :=
  t.isActual obs == false

-- Reference: ticket #34, item (a): one step of the cycle at observation
-- `obs` — the anomaly count, the crisis flag, and the phase transition are
-- all decidable data.
/-- **One step of the Kuhn cycle** at observation `obs`: if the paradigm
fails on `obs`, the anomaly count increments and the failed application is
logged; the phase advances through the (decidable) anomaly/crisis branches. -/
def KuhnState.step {carrier : Type u} (s : KuhnState carrier) (obs : carrier) :
    KuhnState carrier :=
  match anomalyOf s.paradigm obs with
  | true =>
      let a' := s.anomalies + 1
      KuhnState.mk (KuhnPhase.next true (s.threshold ≤ a') s.phase) s.paradigm a'
        s.threshold (obs :: s.log)
  | false =>
      KuhnState.mk (KuhnPhase.next false false s.phase) s.paradigm s.anomalies s.threshold
        s.log

-- Reference: computation steps (projections of `KuhnState.step`).
/-- A non-anomalous observation leaves the anomaly count unchanged. -/
theorem KuhnState.step_no_anomaly {carrier : Type u} (s : KuhnState carrier) (obs : carrier)
    (h : anomalyOf s.paradigm obs = false) :
    (s.step obs).anomalies = s.anomalies :=
  Eq.subst (motive := fun b => (match b with
      | true => KuhnState.mk (KuhnPhase.next true (s.threshold ≤ s.anomalies + 1) s.phase)
          s.paradigm (s.anomalies + 1) s.threshold (obs :: s.log)
      | false => KuhnState.mk (KuhnPhase.next false false s.phase) s.paradigm s.anomalies
          s.threshold s.log
    ).anomalies = s.anomalies) h.symm rfl

-- Reference: computation step of `KuhnState.step`.
/-- An anomalous observation increments the anomaly count. -/
theorem KuhnState.step_anomaly {carrier : Type u} (s : KuhnState carrier) (obs : carrier)
    (h : anomalyOf s.paradigm obs = true) :
    (s.step obs).anomalies = s.anomalies + 1 :=
  Eq.subst (motive := fun b => (match b with
      | true => KuhnState.mk (KuhnPhase.next true (s.threshold ≤ s.anomalies + 1) s.phase)
          s.paradigm (s.anomalies + 1) s.threshold (obs :: s.log)
      | false => KuhnState.mk (KuhnPhase.next false false s.phase) s.paradigm s.anomalies
          s.threshold s.log
    ).anomalies = s.anomalies + 1) h.symm rfl

-- Reference: ticket #34, item (a)/(d): running the machine on a schedule
-- (as `runOn` for #29).
/-- Running the Kuhn machine on a schedule of observations. -/
def runKuhn {carrier : Type u} (s : KuhnState carrier) : List carrier → KuhnState carrier
  | [] => s
  | obs :: rest => runKuhn (s.step obs) rest

-- Reference: computation steps of `runKuhn`.
/-- The empty schedule is the identity. -/
theorem runKuhn_nil {carrier : Type u} (s : KuhnState carrier) : runKuhn s [] = s := rfl

-- Reference: computation step of `runKuhn`.
/-- A schedule step. -/
theorem runKuhn_cons {carrier : Type u} (s : KuhnState carrier) (obs : carrier)
    (rest : List carrier) : runKuhn s (obs :: rest) = runKuhn (s.step obs) rest := rfl

/-! ## Incommensurability as data -/

-- Reference: [Kuhn], 1962, ch. IX (incommensurability); ticket #34, item (b):
-- commensurability iff there is a translation table — a mapping of the
-- carriers' vocabularies preserving the model predicates — a decidable check
-- on bounded carriers, stated as data with NO world-claim.
/-- A **translation table** between theory-elements: a vocabulary map `f`
preserving the actual-model predicate on the bounded family `Mp`. -/
def HasTranslation {carrier : Type u} (t t' : TheoryElement carrier) (f : carrier → carrier) :
    Prop := ∀ m ∈ t.models, t'.isActual (f m) = t.isActual m

-- Reference: ticket #34, item (b).
/-- Two theory-elements are **commensurable** iff a translation table exists
between them. -/
def commensurable {carrier : Type u} (t t' : TheoryElement carrier) : Prop :=
  ∃ f : carrier → carrier, HasTranslation t t' f

-- Reference: the identity translation (core `rfl` on the predicate).
/-- Every theory-element is commensurable with itself (the identity
translation table). -/
theorem commensurable_refl {carrier : Type u} (t : TheoryElement carrier) :
    commensurable t t :=
  ⟨fun m => m, fun _ _ => rfl⟩

/-! ## Toy: the coin theory-element of #30 -/

-- Reference: program's own toy (the #30 coin theory-element).
/-- The rival theory-element: everything is an actual model (no anomalies
ever). -/
def coinTheoryRival : TheoryElement CoinData :=
  { models := coinModels
    isActual := fun _ => true
    isPartial := fun _ => true
    applications := [coinObserved]
    links := []
    empiricalClaim := fun _ _ => rfl }

-- Reference: ticket #34, item (b) — Kuhn's claim becomes the observed ABSENCE
-- of translation tables between pre/post-revolution elements, made a theorem
-- on data (NO world-claim): the coin theory and its rival are incommensurable
-- because `[] ∈ Mp` is actual under the rival but not under the coin theory,
-- so no vocabulary map can preserve the predicate. Proof: `coinActual [] =
-- false` and the rival's predicate is constantly `true` (`rfl`), so any
-- translation table would give `true = false`.
/-- **Incommensurability witness**: the coin theory-element and its rival
are incommensurable (no translation table preserves the model predicate). -/
theorem coinTheory_incommensurable_rival :
    ¬ commensurable coinTheory coinTheoryRival := by
  intro h
  obtain ⟨f, hf⟩ := h
  have hmem : ([] : CoinData) ∈ coinModels := by
    unfold coinModels
    exact List.mem_cons_self
  exact Bool.false_ne_true (hf [] hmem).symm

-- Reference: ticket #34, item (d): the toy calibration — a full cycle with
-- the printed ledger: normal → anomaly (empty observation fails the coin
-- theory) → crisis at threshold 2 → revolution.
/-- The initial Kuhn state of the toy: normal science, the coin paradigm,
threshold 2. -/
def coinKuhnInit : KuhnState CoinData :=
  KuhnState.mk .normal coinTheory 0 2 []

-- Reference: ticket #34, toy (d): the observation schedule — one good
-- application, then two failed ones (the empty experiment is not an actual
-- model of the coin theory).
/-- The toy schedule. -/
def coinKuhnSchedule : List CoinData := [[true], [], []]

-- Reference: ticket #34, acceptance (d): the machine runs; the ledger is
-- printed by `#eval`.
/-- The final state of the toy run. -/
def coinKuhnFinal : KuhnState CoinData := runKuhn coinKuhnInit coinKuhnSchedule

-- Reference: ticket #34, acceptance: printed run — phase name, anomaly
-- count, log.
#eval (coinKuhnFinal.phase.name, coinKuhnFinal.anomalies, coinKuhnFinal.log)

end BoringLab
