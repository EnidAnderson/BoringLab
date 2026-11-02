/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import BoringLab.Epistemology.Process
import Mathlib.Data.Fintype.Basic

/-!
# Identification in the limit: reliability as data

Ticket #31 (EPI.3.1), building on the process machine of #29
(`BoringLab.Epistemology.Process`) and the fair-experiment carrier of #28.
Formal learning theory on bounded carriers, carried by **ℚ-valued
prediction masses** (the #28 prediction tables are the instance) — the
mathematical predicates are `Prop`-valued (`Allowed`, `Compatible`); a
`Bool` shadow (`massAllows`, `compatibleBool`) exists only where the learner
computation needs decidability, and the two are tied by proved lemmas.

* **(a)** a data stream is approximated by finite prefixes (`List datum` —
  the honest constructive reading; the limitation is recorded: the carrier
  is the finite prefixes, not infinite sequences);
* **(b)** `IdentifiesInLimit`: a learner `M : List datum → hyp` converges to
  the true hypothesis on every compatible prefix, uniformly past a bound `N`
  (the uniform reading on the finite carrier — stronger than the per-stream
  reading; limitation recorded);
* **(c)** the falsification/reliability ledger, proved: the Bayesian
  count-table update eliminates a falsified hypothesis permanently
  (`ledgerWeight_runLedger_zero` — once a zero-mass observation has been
  seen, the weight is `0` forever, via #29's
  `falsified_never_resurrects`); singleton families are identifiable
  (`singleton_identifies`); the link to #28's Popper predicate
  (`falsifiable_not_allowed`); and the converse-failure witness
  (`identifiable_not_falsifiable_witness` — an identifiable family
  containing a NON-falsifiable hypothesis: Popper's demarcation vs
  reliability, a theorem-on-data). The general finite-family statement and
  the conservative-method existence are named holes with peeling plans
  (`falsifiable_family_identifiable`, `exists_conservative_method`);
* **(d)** mind changes as data (`mindChangesOn`).

## References
* [Gold] E. M. Gold, "Language identification in the limit", *Information and
  Control* 10(5):447–474, 1967.
* [Putnam] H. Putnam, identification in the limit, 1965 (as cited in the SEP
  entry).
* [Kelly] K. T. Kelly, *The Logic of Reliable Inquiry*, OUP, 1996.
* [SEP FLT] "Formal Learning Theory", *Stanford Encyclopedia of Philosophy*
  (the Kuhn-conservatism connection, Kuhn 1970).
* [Popper] K. R. Popper, *The Logic of Scientific Discovery*, 1959, ch. IV
  (falsifiability — the demarcation predicate of #28).
* Program register: BoringLab ticket #31 (EPI.3.1); the toy is the #28 coin
  prediction tables, the program's own.
-/

namespace BoringLab

/-! ## Masses, allowed data, compatibility — Prop-valued, with a Bool shadow -/

-- Reference: [Kolmogorov], ch. I, §1 (the mass a distribution assigns to a
-- point); the #28 prediction tables `predict : hyp → List (ℚ × outcome)`
-- are the instance, via `tableMass`.
/-- A datum `d` is **allowed** by hypothesis `h` iff its prediction mass under
`h` is nonzero (`Prop`-valued). -/
def Allowed {hyp datum : Type} (mass : hyp → datum → ℚ) (h : hyp) (d : datum) : Prop :=
  mass h d ≠ 0

-- Reference: [Gold], 1967 (a stream is compatible with a hypothesis when
-- every datum in it is allowed); ticket #31, item (a).
/-- A finite prefix is **compatible** with a hypothesis when every datum in
it is allowed (`Prop`-valued). -/
def Compatible {hyp datum : Type} (mass : hyp → datum → ℚ) (h : hyp)
    (p : List datum) : Prop :=
  ∀ d ∈ p, Allowed mass h d

-- Reference: computation shadow (core `ite` on the decidable equality of
-- rationals — the same pattern as #28's `isDistribution`); needed only for
-- the learner's `filter`.
/-- The decidable shadow of `Allowed`: the `Bool` flag for computation. -/
def massAllows {hyp datum : Type} (mass : hyp → datum → ℚ) (h : hyp) (d : datum) : Bool :=
  if mass h d = 0 then false else true

-- Reference: core `ite_eq_left`/`ite_eq_right` on the decidable equality
-- of rationals; the tie between the Prop predicate and its Bool shadow.
/-- The Bool shadow is true exactly when the mass is nonzero. -/
theorem massAllows_eq_true {hyp datum : Type} (mass : hyp → datum → ℚ) (h : hyp)
    (d : datum) : massAllows mass h d = true ↔ Allowed mass h d := by
  refine Iff.intro
    (fun hb h0 => Bool.false_ne_true (Eq.subst (motive := fun x => x = true) (ite_eq_left h0) hb))
    (fun hn => ite_eq_right hn)

-- Reference: `List.all`; computation shadow of `Compatible`.
/-- The decidable shadow of `Compatible`. -/
def compatibleBool {hyp datum : Type} (mass : hyp → datum → ℚ) (h : hyp)
    (p : List datum) : Bool := p.all (massAllows mass h)

-- Reference: core `List.all_eq_true`.
/-- The Bool compatibility flag is true exactly on the all-allowed prefixes. -/
theorem compatibleBool_eq_true {hyp datum : Type} (mass : hyp → datum → ℚ) (h : hyp)
    (p : List datum) :
    compatibleBool mass h p = true ↔ ∀ d ∈ p, massAllows mass h d = true :=
  List.all_eq_true

-- Reference: from `compatibleBool_eq_true` and `massAllows_eq_true`.
/-- The Bool shadow implies the Prop compatibility. -/
theorem Compatible_of_compatibleBool {hyp datum : Type} (mass : hyp → datum → ℚ) (h : hyp)
    (p : List datum) (hb : compatibleBool mass h p = true) : Compatible mass h p :=
  fun d hd => (massAllows_eq_true mass h d).mp (List.all_eq_true.mp hb d hd)

/-! ## Identification in the limit -/

-- Reference: [Gold], 1967 (identification in the limit); ticket #31, item
-- (b) — uniform reading on the finite-prefix carrier (∃ N, all compatible
-- prefixes past N), stronger than the per-stream reading; the limitation is
-- recorded in the module docstring.
-- REVIEW(citation): pin the Gold definition page in review.
/-- A learner `M` **identifies the family** `hs` in the limit (uniform finite
reading): for every true hypothesis `h ∈ hs` there is a bound `N` such that
`M` outputs `h` on every compatible prefix of length at least `N`. -/
def IdentifiesInLimit {hyp datum : Type} (M : List datum → hyp)
    (mass : hyp → datum → ℚ) (hs : List hyp) : Prop :=
  ∀ h ∈ hs, ∃ N : ℕ, ∀ p : List datum, Compatible mass h p → N ≤ p.length → M p = h

-- Reference: [Gold], 1967 (a singleton family is trivially identifiable —
-- the constant learner converges immediately, bound `N = 0`).
/-- **Singleton families are identifiable**: the constant learner converges
at bound `0`. -/
theorem singleton_identifies {hyp datum : Type} (mass : hyp → datum → ℚ) (h : hyp) :
    IdentifiesInLimit (fun _ => h) mass [h] := by
  intro h' hh
  rcases List.mem_cons.mp hh with he | hn
  · exact ⟨0, fun p _ _ => he.symm⟩
  · exact absurd hn List.not_mem_nil

/-! ## The #28 carrier: prediction masses as the mass function -/

-- Reference: #28's `tableMass` (the mass a prediction table assigns to an
-- outcome); the mass function of an experiment.
/-- The mass function of a prediction table. -/
def tableMassOf {hyp outcome : Type} [DecidableEq outcome]
    (predict : hyp → List (ℚ × outcome)) (h : hyp) (o : outcome) : ℚ :=
  tableMass (predict h) o

-- Reference: [Popper], ch. IV, §21, via #28's `falsifiableHyp_eq_true`:
-- a falsifiable hypothesis has a zero-mass outcome — exactly a non-allowed
-- datum (Prop version; the mass is definitionally `tableMass`).
-- REVIEW(citation): as on `Experiment.falsifiableHyp` (#28).
/-- **Falsifiable hypotheses have a non-allowed datum**: #28's Popper
predicate implies the existence of a refuting observation. -/
theorem falsifiable_not_allowed {hyp outcome : Type} [DecidableEq outcome]
    (e : Experiment hyp outcome) (h : hyp)
    (hf : Experiment.falsifiableHyp e h = true) :
    ∃ o : outcome, ¬ Allowed (tableMassOf e.predict) h o := by
  obtain ⟨o, _, hm⟩ := (Experiment.falsifiableHyp_eq_true e h).mp hf
  exact ⟨o, fun hne => hne hm⟩

/-! ## The reliability ledger: the Bayesian update eliminates the falsified -/

-- Reference: #29's `bayesUpdate`, iterated over a schedule of observations
-- (as `runOn` for the state machine).
/-- The **ledger run** over a schedule of observations: fold the count-table
update. -/
def runLedger {hyp outcome : Type} [DecidableEq outcome]
    (predict : hyp → List (ℚ × outcome)) :
    List outcome → List (hyp × ℚ) → List (hyp × ℚ)
  | [], l => l
  | o :: os, l => runLedger predict os (bayesUpdate predict o l)

-- Reference: ticket #31, item (c) — monotonicity iterated: once the weight
-- is zero, every further update keeps it zero (induction on the schedule,
-- each step `falsified_never_resurrects` from #29).
/-- **Zero weight is absorbing under the whole ledger run**: if the weight of
`h'` is zero, it stays zero after any schedule of updates. -/
theorem ledgerWeight_runLedger_stays_zero {hyp outcome : Type} [DecidableEq hyp]
    [DecidableEq outcome] (predict : hyp → List (ℚ × outcome)) (h' : hyp)
    (l : List (hyp × ℚ)) (hz : ledgerWeight l h' = 0) :
    ∀ os : List outcome, ledgerWeight (runLedger predict os l) h' = 0
  | [] => hz
  | o :: os =>
      ledgerWeight_runLedger_stays_zero predict h' (bayesUpdate predict o l)
        (falsified_never_resurrects predict o l h' hz) os

-- Reference: ticket #31, item (c) — the reliability ledger's main theorem:
-- a hypothesis falsified by some observation of the schedule has weight zero
-- after the whole run (the eliminating observation zeroes it, then
-- `ledgerWeight_runLedger_stays_zero` keeps it dead).
/-- **The Bayesian count-table eliminates the falsified, permanently**: if
some observation in the schedule has zero prediction mass under `h'`, then
`h'` has weight `0` after the whole ledger run. -/
theorem ledgerWeight_runLedger_zero {hyp outcome : Type} [DecidableEq hyp]
    [DecidableEq outcome] (predict : hyp → List (ℚ × outcome))
    (p : List outcome) (l : List (hyp × ℚ)) (h' : hyp)
    (h : ∃ o ∈ p, tableMass (predict h') o = 0) :
    ledgerWeight (runLedger predict p l) h' = 0 := by
  induction p generalizing l with
  | nil =>
      rcases h with ⟨o, ho, _⟩
      exact absurd ho List.not_mem_nil
  | cons o os ih =>
      rcases h with ⟨d, hd, hm⟩
      rcases List.mem_cons.mp hd with he | hd'
      · have hupd : ledgerWeight (bayesUpdate predict o l) h' = 0 :=
          (ledgerWeight_bayesUpdate predict o l h').trans
            ((congrArg (fun x => ledgerWeight l h' * x)
                (Eq.subst (motive := fun x => tableMass (predict h') x = 0) he hm)).trans
              (mul_zero (ledgerWeight l h')))
        exact ledgerWeight_runLedger_stays_zero predict h' (bayesUpdate predict o l) hupd os
      · exact ih (bayesUpdate predict o l) ⟨d, hd', hm⟩

/-! ## The elimination learner and mind changes -/

-- Reference: ticket #31, item (c)/(d); [Gold] 1967 (learning by
-- elimination): output the first hypothesis of the family compatible with
-- the prefix (on the Bool shadow), a default when none is.
/-- The **elimination learner**: the first hypothesis of `hs` whose Bool
compatibility flag is true on the prefix `p`, or `default` if none. -/
def elimLearner {hyp datum : Type} (hs : List hyp) (mass : hyp → datum → ℚ)
    (default : hyp) (p : List datum) : hyp :=
  match hs.filter (fun h => compatibleBool mass h p) with
  | [] => default
  | h :: _ => h

-- Reference: computation steps of `elimLearner`; `rfl` only in these
-- primitive definitional lemmas, via `Eq.subst` on the scrutinee equality.
/-- The elimination learner on an empty compatible list returns the
default. -/
theorem elimLearner_nil {hyp datum : Type} (hs : List hyp) (mass : hyp → datum → ℚ)
    (default : hyp) (p : List datum)
    (h : (hs.filter fun h => compatibleBool mass h p) = []) :
    elimLearner hs mass default p = default := by
  exact Eq.subst (motive := fun l => (match l with | [] => default | h :: _ => h) = default)
    h.symm rfl

-- Reference: computation step of `elimLearner`.
/-- The elimination learner on a nonempty compatible list returns its head. -/
theorem elimLearner_cons {hyp datum : Type} (hs : List hyp) (mass : hyp → datum → ℚ)
    (default : hyp) (p : List datum) (h : hyp) (rest : List hyp)
    (he : (hs.filter fun h => compatibleBool mass h p) = h :: rest) :
    elimLearner hs mass default p = h :=
  Eq.subst (motive := fun l => (match l with | [] => default | h :: _ => h) = h) he.symm rfl

-- Reference: [Kelly], 1996 (mind changes along a stream); ticket #31, item
-- (d) — counted on the finite prefixes of a finite schedule (the recorded
-- limitation); the `ite` is the decidable equality of the outputs.
/-- The **mind-change count** of a learner on a finite schedule: the number
of prefix lengths `n` at which the output on `take n` differs from the
output on `take (n+1)`. -/
def mindChangesOn {hyp datum : Type} [DecidableEq hyp] (M : List datum → hyp)
    (s : List datum) : ℕ :=
  ((List.range (s.length + 1)).filter fun n =>
    if M (s.take n) = M (s.take (n + 1)) then false else true).length

-- Reference: ticket #31, item (d) — the conservative method (fewest mind
-- changes) exists on bounded carriers by enumeration over the finitely many
-- output tuples on the prefixes of a fixed schedule.
-- TEMPORARY SORRY: the honest proof has not been instantiated yet.
-- PEELING PLAN: over `[Fintype hyp]`, the outputs on the `s.length + 1`
-- prefixes form a `Fin (s.length+1) → hyp` tuple; `Finset.exists_min_image`
-- on `Finset.univ` picks a minimizing tuple; extend it to a learner `M` off
-- the prefixes by a default; `mindChangesOn` depends only on the tuple.
-- Next named lemmas: `mindChangesOn_eq_of_prefixes`, `prefixes_fintype`.
/-- The **conservative method exists** on bounded carriers: for every finite
schedule there is a learner minimizing the mind-change count on it. -/
theorem exists_conservative_method {hyp datum : Type} [Fintype hyp] [DecidableEq hyp]
    [DecidableEq datum] (s : List datum) :
    ∃ M : List datum → hyp, ∀ M' : List datum → hyp,
      mindChangesOn M s ≤ mindChangesOn M' s := by
  sorry

-- Reference: ticket #31, item (c) — the general finite-family statement.
-- TEMPORARY SORRY: the honest proof has not been instantiated yet.
-- PEELING PLAN: under the per-stream (non-uniform) reading, the elimination
-- learner identifies `h` when every other `h' ∈ hs` is falsified by some
-- datum allowed under `h` (`hsep` below); the finite family eliminates `h'`
-- after finitely many rounds — and `ledgerWeight_runLedger_zero` is the
-- Bayesian form of the same elimination. Next named lemmas:
-- `elimLearner_eventually_const`, `finite_elimination_bound`.
/-- **Falsifiable-only families are identifiable** (separation form): if
every other hypothesis of the finite family is falsified by some datum
allowed under `h`, then some learner identifies `h` in the limit. -/
theorem falsifiable_family_identifiable {hyp datum : Type}
    (mass : hyp → datum → ℚ) (hs : List hyp) (h : hyp) (hh : h ∈ hs)
    (hsep : ∀ h' ∈ hs, h' ≠ h → ∃ d : datum, mass h d ≠ 0 ∧ mass h' d = 0) :
    ∃ M : List datum → hyp, ∃ N : ℕ, ∀ p : List datum,
      Compatible mass h p → N ≤ p.length → M p = h := by
  sorry

/-! ## Toy: the coin prediction tables of #28 -/

-- Reference: ticket #31, acceptance — the toy: the #28 coin family with the
-- ℚ mass function `tableMassOf coinPredict`; the elimination learner run on
-- a schedule, with outputs and mind changes printed.
/-- The coin mass function induced by the #28 prediction table. -/
def coinMass (h : CoinHyp) (c : Coin) : ℚ := tableMassOf coinPredict h c

-- Reference: ticket #31, item (c) — the converse fails: Popper's
-- falsifiability is not necessary for identifiability. The singleton family
-- `{fair}` is identifiable (`singleton_identifies`), while `fair` is NOT
-- falsifiable (#28's `fair_not_falsifiable`).
-- REVIEW(citation): the SEP-noted Popper-vs-reliability subtlety, made a
-- theorem-on-data.
/-- **Converse-failure witness**: an identifiable family containing a
non-falsifiable hypothesis — falsifiability does not characterize
identifiability. -/
theorem identifiable_not_falsifiable_witness :
    IdentifiesInLimit (fun _ => CoinHyp.fair) (tableMassOf coinPredict) [CoinHyp.fair] ∧
      Experiment.falsifiableHyp coinExperiment CoinHyp.fair = false :=
  ⟨singleton_identifies (tableMassOf coinPredict) CoinHyp.fair, fair_not_falsifiable⟩

-- Reference: ticket #31, toy: a two-round schedule (heads then tails) —
-- the loaded coin is eliminated by the tails observation (zero mass).
/-- The toy schedule: heads then tails. -/
def coinStream : List Coin := [Coin.heads, Coin.tails]

-- Reference: ticket #31, toy: the elimination learner's outputs on every
-- prefix of the schedule (the loaded coin is compatible with heads only).
/-- The outputs of the elimination learner on every prefix of the schedule. -/
def coinLearnerOutputs : List (ℕ × CoinHyp) :=
  (List.range (coinStream.length + 1)).map fun n =>
    (n, elimLearner coinHypotheses coinMass CoinHyp.fair (coinStream.take n))

-- Reference: ticket #31, acceptance: `#eval` prints the outputs and the
-- mind-change count.
#eval coinLearnerOutputs
#eval mindChangesOn (elimLearner coinHypotheses coinMass CoinHyp.fair) coinStream

end BoringLab
