/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import Mathlib.Init
import Mathlib.Data.Rat.Init
import Mathlib.Algebra.Field.Rat
import Mathlib.Algebra.GroupWithZero.Units.Basic
import BoringLab.Games.Basic

/-!
# Fair experiments as a typed structure

Ticket #28 (EPI.1.1): the fair experiment as explicit computable data. An
`Experiment` over a hypothesis type `hyp` and an outcome type `outcome` carries
the outcome space and the hypothesis family as lists and the pre-registered
prediction map as an explicit table `hyp → List (ℚ × outcome)` — phase one,
whose fields the constructor takes *before* the observation — followed by the
observation record, the analysis function, and the blinding flag (phase two).
Phase one is also available as the standalone structure `Preregistered`, and
`Experiment.mkBlind` attaches phase two to a pre-registration, setting the
blinding flag to the decidable check `blindCheck` (the analysis does not read
hypothesis identity). Falsifiability is the decidable predicate `falsifiable`:
some cell of the fixed outcome space carries zero prediction mass (Popper's
demarcation). The toy instance (D.5) is a two-phase coin-flip experiment whose
run and falsifiability predicate are printed by `#eval`.

## References
* [Popper] K. R. Popper, *The Logic of Scientific Discovery*, New York: Basic
  Books, 1959 (English translation of *Logik der Forschung*, 1934), ch. IV
  "Falsifiability", §21 (a theory is scientific iff some possible observation
  is incompatible with it).
* [Nosek et al.] B. A. Nosek et al., "Promoting an Open Research Culture",
  *Science* 348(6242):1422–1425, 2015, doi:10.1126/science.aab2374
  (pre-registering predictions before the observation is recorded).
* [Fisher] R. A. Fisher, *The Design of Experiments*, 2nd ed., Oliver & Boyd,
  1935, ch. II (controls and blinding in experimental design).
* [Kolmogorov] A. N. Kolmogorov, *Foundations of the Theory of Probability*,
  2nd English ed., Chelsea, 1956, ch. I, §1 (distributions on finite spaces as
  weight tables).
* [Conway] J. H. Conway, *On Numbers and Games*, 2nd ed., A K Peters, 2000,
  ch. 0 (the games substrate referenced in the referee note).
* Program register: BoringLab ticket #28 (EPI.1.1); the toy instance is item
  (D.5), the program's own.
-/

namespace BoringLab

/-! ## Prediction tables: explicit finite distributions -/

-- Reference: [Kolmogorov], ch. I, §1 (a distribution on a finite space is a
-- table of weights summing to one).
-- REVIEW(citation): pin down the exact page in review.
/-- The total weight of a prediction table: the sum of the first components. -/
def weightsSum {outcome : Type} (t : List (ℚ × outcome)) : ℚ := (t.map Prod.fst).sum

-- Reference: [Kolmogorov], ch. I, §1 (weights of a distribution sum to one).
-- REVIEW(citation): pin down the exact page in review.
/-- **Distribution check**, as decidable data: a prediction table is a
finite outcome distribution iff its weights sum to `1`. -/
def isDistribution {outcome : Type} (t : List (ℚ × outcome)) : Bool :=
  if weightsSum t = 1 then true else false

-- Reference: [Kolmogorov], ch. I, §1; computation step of `isDistribution`
-- via `if_pos`/`if_neg` on the decidable equality of rationals.
-- REVIEW(citation): pin down the exact page in review.
/-- The distribution check is true exactly when the weights sum to one. -/
theorem isDistribution_eq_true {outcome : Type} (t : List (ℚ × outcome)) :
    isDistribution t = true ↔ weightsSum t = 1 := by
  unfold isDistribution
  refine Iff.intro (fun h => ?_) (fun h => ?_)
  · cases (inferInstance : Decidable (weightsSum t = 1)) with
    | isTrue h' => exact h'
    | isFalse h' =>
        exact absurd (Eq.subst (motive := fun x => x = true) (ite_eq_right h') h)
          Bool.false_ne_true
  · exact ite_eq_left h

-- Reference: [Kolmogorov], ch. I, §1 (the mass a distribution assigns to a
-- point is the sum of the weights of its cells).
-- REVIEW(citation): pin down the exact page in review.
/-- The total prediction mass that a table assigns to the outcome `o`: the sum
of the weights of the cells whose second component is `o` (zero if `o` is
absent from the table). -/
def tableMass {outcome : Type} [DecidableEq outcome] (t : List (ℚ × outcome))
    (o : outcome) : ℚ :=
  match t with
  | [] => 0
  | p :: rest => if p.2 = o then p.1 + tableMass rest o else tableMass rest o

-- Reference: computation on the rational zero; core `if_pos`/`if_neg`.
/-- The decidable zero test on rationals. -/
def isZeroQ (q : ℚ) : Bool := if q = 0 then true else false

-- Reference: core `if_pos`/`if_neg` applied to the decidable equality
-- `q = 0`; the step `if ... = true` to `false = true` goes through `Eq.subst`
-- on the named equality `if_neg h'`.
/-- The decidable zero test is true exactly on zero. -/
theorem isZeroQ_eq_true (q : ℚ) : isZeroQ q = true ↔ q = 0 := by
  unfold isZeroQ
  refine Iff.intro (fun h => ?_) (fun h => ?_)
  · cases (inferInstance : Decidable (q = 0)) with
    | isTrue h' => exact h'
    | isFalse h' =>
        exact absurd (Eq.subst (motive := fun x => x = true) (ite_eq_right h') h)
          Bool.false_ne_true
  · exact ite_eq_left h

-- Reference: core `ite_eq_left` on the `DecidableEq` test in `tableMass`.
/-- Computation step of `tableMass` on a cell whose outcome matches. -/
theorem tableMass_cons_same {outcome : Type} [DecidableEq outcome] (p : ℚ × outcome)
    (rest : List (ℚ × outcome)) (o : outcome) (h : p.2 = o) :
    tableMass (p :: rest) o = p.1 + tableMass rest o := ite_eq_left h

-- Reference: core `ite_eq_right` on the `DecidableEq` test in `tableMass`.
/-- Computation step of `tableMass` on a cell whose outcome differs. -/
theorem tableMass_cons_diff {outcome : Type} [DecidableEq outcome] (p : ℚ × outcome)
    (rest : List (ℚ × outcome)) (o : outcome) (h : p.2 ≠ o) :
    tableMass (p :: rest) o = tableMass rest o := ite_eq_right h

-- Reference: definitional (the `[]` branch of `tableMass`).
/-- Computation step of `tableMass` on the empty table. -/
theorem tableMass_nil {outcome : Type} [DecidableEq outcome] (o : outcome) :
    tableMass [] o = 0 := rfl

-- Reference: [Popper], ch. IV, §21 (demarcation: a theory is falsifiable iff
-- some possible observation — a "potential falsifier" — is incompatible with
-- it; in a probabilistic reading, some outcome cell has zero mass).
-- REVIEW(citation): verified against the 1959 edition's index ("falsifiability
-- as a scientific characteristic of a theory ... section 21") via web search;
-- pin the page against the physical text in review.
/-- **Falsifiability** (Popper demarcation), as a decidable predicate: a
prediction table over the outcome space `os` is falsifiable iff some outcome
cell carries zero prediction mass. -/
def falsifiable {outcome : Type} [DecidableEq outcome] (os : List outcome)
    (t : List (ℚ × outcome)) : Bool :=
  os.any fun o => isZeroQ (tableMass t o)

-- Reference: [Popper], ch. IV, §21; from `List.any_eq_true` (core) and
-- `isZeroQ_eq_true`.
-- REVIEW(citation): as on `falsifiable`.
/-- Falsifiability holds exactly when some outcome of the fixed outcome space
has zero prediction mass. -/
theorem falsifiable_eq_true {outcome : Type} [DecidableEq outcome] {os : List outcome}
    {t : List (ℚ × outcome)} :
    falsifiable os t = true ↔ ∃ o, o ∈ os ∧ tableMass t o = 0 := by
  unfold falsifiable
  refine Iff.trans List.any_eq_true ?_
  refine Iff.intro (fun h => ?_) (fun h => ?_)
  · obtain ⟨o, ho, hz⟩ := h
    exact ⟨o, ho, (isZeroQ_eq_true (tableMass t o)).mp hz⟩
  · obtain ⟨o, ho, hz⟩ := h
    exact ⟨o, ho, (isZeroQ_eq_true (tableMass t o)).mpr hz⟩

/-! ## Phase one: pre-registration -/

-- Reference: [Nosek et al.], p. 1422 (pre-registration: the prediction is
-- fixed before the observation is recorded); [Fisher], ch. II.
-- REVIEW(citation): [Nosek et al.] verified bibliographically via web search
-- (Science 348(6242):1422-1425, doi:10.1126/science.aab2374); [Fisher] page
-- to pin in review.
/-- **Pre-registration**, phase one of a fair experiment: the outcome space
`outcomes` (fixed in this phase), the hypothesis family `hypotheses` as data,
and the prediction table `predict` mapping each hypothesis to its outcome
distribution as an explicit `List (ℚ × outcome)`. -/
structure Preregistered (hyp outcome : Type) where
  /-- The outcome space, fixed in phase one. -/
  outcomes : List outcome
  /-- The hypothesis family, as data. -/
  hypotheses : List hyp
  /-- The pre-registered prediction table. -/
  predict : hyp → List (ℚ × outcome)

-- Reference: [Barendregt] H. P. Barendregt, *The Lambda Calculus*, 1984,
-- ch. 2 (eta conversion), as in `BoringLab.Game.eta`.
-- REVIEW(citation): pin down the exact section in review.
/-- **Eta conversion for pre-registrations**: a pre-registration equals the
pre-registration assembled from its components. -/
theorem Preregistered.eta {hyp outcome : Type} (p : Preregistered hyp outcome) :
    Preregistered.mk p.outcomes p.hypotheses p.predict = p := by
  cases p with
  | mk outcomes hypotheses predict => rfl

/-! ## Phase two: the experiment -/

-- Reference: [Nosek et al.] (pre-registration, two-phase: table before
-- observation); [Fisher], ch. II (blinding).
-- REVIEW(citation): as on `Preregistered`.
/-- A **fair experiment** as explicit computable data. The constructor takes
the phase-one fields first — `outcomes`, `hypotheses`, and the prediction
table `predict` — and only then the phase-two fields, so the prediction table
is necessarily built before the observation is attached. Blinding is the Bool
field `blind`, which `Experiment.mkBlind` sets to the decidable check
`blindCheck` on the analysis function. -/
structure Experiment (hyp outcome : Type) where
  /-- Phase one: the outcome space, fixed before any observation. -/
  outcomes : List outcome
  /-- Phase one: the hypothesis family, as data. -/
  hypotheses : List hyp
  /-- Phase one: the pre-registered prediction table, taken before the
  observation. -/
  predict : hyp → List (ℚ × outcome)
  /-- Phase two: the observation record of the run. -/
  observation : outcome
  /-- Phase two: the analysis function; it may receive a hypothesis, so
  blinding is a separate decidable check on it (`blindCheck`). -/
  analysis : hyp → outcome → Bool
  /-- Phase two: the blinding flag. -/
  blind : Bool

-- Reference: [Barendregt], ch. 2 (eta conversion), as in `BoringLab.Game.eta`.
-- REVIEW(citation): pin down the exact section in review.
/-- **Eta conversion for experiments**: an experiment equals the experiment
assembled from its components. -/
theorem Experiment.eta {hyp outcome : Type} (e : Experiment hyp outcome) :
    Experiment.mk e.outcomes e.hypotheses e.predict e.observation e.analysis e.blind = e := by
  cases e with
  | mk outcomes hypotheses predict observation analysis blind => rfl

-- Reference: [Fisher], ch. II (blinding as a property of the analysis, not of
-- the hypothesis); the decidable check `blindCheck` on the registered family.
-- REVIEW(citation): pin down the exact page in review.
/-- **Blinding check**, as decidable data: the analysis function `a`, at the
observation `o`, gives the same verdict for every pair of registered
hypotheses — the data-level statement that the analysis does not read
hypothesis identity. -/
def blindCheck {hyp outcome : Type} (hs : List hyp) (a : hyp → outcome → Bool)
    (o : outcome) : Bool :=
  hs.all fun h => hs.all fun h' => (a h o == a h' o)

-- Reference: core `List.all_eq_true` twice, then `beq_iff_eq` (LawfulBEq Bool).
/-- The blinding check is true exactly when the verdict is independent of
which registered hypothesis is fed to the analysis. -/
theorem blindCheck_eq_true {hyp outcome : Type} {hs : List hyp} {a : hyp → outcome → Bool}
    {o : outcome} (h : blindCheck hs a o = true) {h1 h2 : hyp} (hh1 : h1 ∈ hs)
    (hh2 : h2 ∈ hs) : a h1 o = a h2 o :=
  beq_iff_eq.mp (List.all_eq_true.mp (List.all_eq_true.mp h h1 hh1) h2 hh2)

-- Reference: [Nosek et al.] (pre-registration); program register ticket #28,
-- item (b): attach phase two to a completed phase one, computing the blinding
-- flag from `blindCheck`.
-- REVIEW(citation): program's own construction.
/-- **Two-phase constructor**: attach the observation record and the analysis
function to a pre-registration; the prediction table is carried over from
phase one unchanged, and the blinding flag is set to `blindCheck`. -/
def Experiment.mkBlind {hyp outcome : Type} (pre : Preregistered hyp outcome)
    (observation : outcome) (analysis : hyp → outcome → Bool) : Experiment hyp outcome :=
  Experiment.mk pre.outcomes pre.hypotheses pre.predict observation analysis
    (blindCheck pre.hypotheses analysis observation)

-- Reference: computation step (projection of `Experiment.mkBlind`); `rfl` is
-- permitted only in such primitive computation lemmas.
/-- The two-phase constructor carries the phase-one prediction table over
unchanged. -/
theorem Experiment.mkBlind_predict {hyp outcome : Type} (pre : Preregistered hyp outcome)
    (observation : outcome) (analysis : hyp → outcome → Bool) :
    (Experiment.mkBlind pre observation analysis).predict = pre.predict := rfl

-- Reference: computation step (projection of `Experiment.mkBlind`); the
-- outcome space is fixed in phase one.
/-- The outcome space of the experiment is exactly the phase-one outcome space. -/
theorem Experiment.outcomes_phaseOne {hyp outcome : Type} (pre : Preregistered hyp outcome)
    (observation : outcome) (analysis : hyp → outcome → Bool) :
    (Experiment.mkBlind pre observation analysis).outcomes = pre.outcomes := rfl

-- Reference: computation step (projection of `Experiment.mkBlind`).
/-- The blinding flag of the two-phase constructor is the blinding check. -/
theorem Experiment.mkBlind_blind {hyp outcome : Type} (pre : Preregistered hyp outcome)
    (observation : outcome) (analysis : hyp → outcome → Bool) :
    (Experiment.mkBlind pre observation analysis).blind =
      blindCheck pre.hypotheses analysis observation := rfl

-- Reference: [Fisher], ch. II (blinding); from `Experiment.mkBlind_blind` via
-- `Eq.subst` and `blindCheck_eq_true`.
-- REVIEW(citation): pin down the exact page in review.
/-- **Blinded verdict**: in a two-phase experiment whose blinding flag is true,
the analysis gives the same verdict on the observation for any two registered
hypotheses — the analysis does not read hypothesis identity. -/
theorem Experiment.blinded_of_mkBlind {hyp outcome : Type} (pre : Preregistered hyp outcome)
    (observation : outcome) (analysis : hyp → outcome → Bool)
    (hblind : (Experiment.mkBlind pre observation analysis).blind = true) {h1 h2 : hyp}
    (hh1 : h1 ∈ pre.hypotheses) (hh2 : h2 ∈ pre.hypotheses) :
    analysis h1 observation = analysis h2 observation :=
  blindCheck_eq_true
    ((Experiment.mkBlind_blind pre observation analysis).symm.trans hblind) hh1 hh2

-- Reference: [Popper], ch. IV, §21; program register ticket #28, item (c).
-- REVIEW(citation): as on `falsifiable`.
/-- The falsifiability predicate of a registered hypothesis: some cell of the
fixed outcome space has zero prediction mass under that hypothesis. -/
def Experiment.falsifiableHyp {hyp outcome : Type} [DecidableEq outcome]
    (e : Experiment hyp outcome) (h : hyp) : Bool :=
  falsifiable e.outcomes (e.predict h)

-- Reference: [Popper], ch. IV, §21; from `falsifiable_eq_true`.
-- REVIEW(citation): as on `falsifiable`.
/-- A registered hypothesis is falsifiable exactly when some outcome of the
experiment's fixed outcome space has zero prediction mass under it. -/
theorem Experiment.falsifiableHyp_eq_true {hyp outcome : Type} [DecidableEq outcome]
    (e : Experiment hyp outcome) (h : hyp) :
    Experiment.falsifiableHyp e h = true ↔
      ∃ o, o ∈ e.outcomes ∧ tableMass (e.predict h) o = 0 :=
  falsifiable_eq_true

/-!
### Referee note (REVIEW — not a theorem)

REVIEW(referee): in the program's games dictionary the referee of a
`BoringLab.Game` (`BoringLab.Games.Basic`) rules on the position without
reading the players' identities; the fair experiment mirrors this — the
analysis function should rule on the observation record alone, and
`blindCheck` is the decidable data-level shadow of that rule. K/S/O framing
(foundation audit F13: K/S/O tags as structure, not metaphor): the
pre-registered prediction table is the K-tag, the blinding check the S-tag,
and the observation record the O-tag. Per ticket #28 item (d) this connection
is a review note only; no theorem is stated here.
-/

/-! ## Toy instance (D.5): a two-phase coin-flip experiment -/

-- Reference: program's own toy (ticket #28, item (d')).
-- REVIEW(citation): program's own.
/-- The toy outcome space: a coin flip. -/
inductive Coin where
  | heads : Coin
  | tails : Coin
deriving DecidableEq, Repr

-- Reference: program's own toy (ticket #28, item (d')).
-- REVIEW(citation): program's own.
/-- The toy hypothesis family: a fair coin, a biased coin, and a coin loaded
towards heads. -/
inductive CoinHyp where
  | fair : CoinHyp
  | biased : CoinHyp
  | loaded : CoinHyp
deriving DecidableEq, Repr

-- Reference: program's own toy.
-- REVIEW(citation): program's own.
/-- Phase one, outcome space fixed: heads and tails. -/
def coinOutcomes : List Coin := [Coin.heads, Coin.tails]

-- Reference: program's own toy; tables as in [Kolmogorov], ch. I, §1.
-- REVIEW(citation): program's own.
/-- Phase one, the pre-registered prediction table: fair `1/2`-`1/2`, biased
`2/3`-`1/3`, loaded `1`-`0` (heads-tails). -/
def coinPredict : CoinHyp → List (ℚ × Coin)
  | CoinHyp.fair => [(1/2, Coin.heads), (1/2, Coin.tails)]
  | CoinHyp.biased => [(2/3, Coin.heads), (1/3, Coin.tails)]
  | CoinHyp.loaded => [(1, Coin.heads), (0, Coin.tails)]

-- Reference: program's own toy.
-- REVIEW(citation): program's own.
/-- Phase one, the hypothesis family as data. -/
def coinHypotheses : List CoinHyp := [CoinHyp.fair, CoinHyp.biased, CoinHyp.loaded]

-- Reference: program's own toy.
-- REVIEW(citation): program's own.
/-- Phase one of the toy: the pre-registration. -/
def coinPrereg : Preregistered CoinHyp Coin :=
  Preregistered.mk coinOutcomes coinHypotheses coinPredict

-- Reference: program's own toy; a blind analysis reads only the observation.
-- REVIEW(citation): program's own.
/-- The toy analysis function: report whether the observed flip is heads; it
ignores the hypothesis argument. -/
def coinAnalysis : CoinHyp → Coin → Bool :=
  fun _h o => if o = Coin.heads then true else false

-- Reference: program's own toy (ticket #28, item (d')).
-- REVIEW(citation): program's own.
/-- Phase two of the toy: the observation `heads` attached to the
pre-registration, with the blinding flag computed by `blindCheck`. -/
def coinExperiment : Experiment CoinHyp Coin :=
  Experiment.mkBlind coinPrereg Coin.heads coinAnalysis

-- Reference: computation step on the toy (`rfl` in a primitive computation
-- lemma): `blindCheck` over the three hypotheses is true because the toy
-- analysis ignores its hypothesis argument.
/-- The toy experiment is blind. -/
theorem coinExperiment_blind : coinExperiment.blind = true := rfl

-- Reference: program's own toy; from `Experiment.blinded_of_mkBlind`,
-- `coinExperiment_blind`, and `List.mem_cons_self` / `List.mem_cons_of_mem`.
/-- The toy's blinded verdict: the analysis agrees on `fair` and `loaded`. -/
theorem coin_blinded_verdict :
    coinAnalysis CoinHyp.fair Coin.heads = coinAnalysis CoinHyp.loaded Coin.heads :=
  Experiment.blinded_of_mkBlind coinPrereg Coin.heads coinAnalysis coinExperiment_blind
    List.mem_cons_self
    (List.mem_cons_of_mem CoinHyp.fair
      (List.mem_cons_of_mem CoinHyp.biased List.mem_cons_self))

-- Reference: program's own toy; `tableMass_cons_diff`/`tableMass_cons_same`/
-- `tableMass_nil` + `add_zero` (`Rat.add` is kernel-irreducible at the pin,
-- so `rfl` cannot close these).
/-- The `tails` cell of the loaded coin has mass `0`. -/
theorem coinPredict_loaded_tails_mass :
    tableMass (coinPredict CoinHyp.loaded) Coin.tails = 0 :=
  (tableMass_cons_diff (1, Coin.heads) [(0, Coin.tails)] Coin.tails
    (fun h => Coin.noConfusion h)).trans
    ((tableMass_cons_same (0, Coin.tails) [] Coin.tails rfl).trans
      ((congrArg (fun x => (0, Coin.tails).1 + x) (tableMass_nil Coin.tails)).trans
        (add_zero (0:ℚ))))

-- Reference: program's own toy; as `coinPredict_loaded_tails_mass`.
/-- The `heads` cell of the fair coin has mass `1/2`. -/
theorem coinPredict_fair_heads_mass :
    tableMass (coinPredict CoinHyp.fair) Coin.heads = 1/2 :=
  (tableMass_cons_same (1/2, Coin.heads) [(1/2, Coin.tails)] Coin.heads rfl).trans
    ((congrArg (fun x => (1/2, Coin.heads).1 + x)
        (tableMass_cons_diff (1/2, Coin.tails) [] Coin.heads (fun h => Coin.noConfusion h))).trans
      ((congrArg (fun x => (1/2, Coin.heads).1 + x) (tableMass_nil Coin.heads)).trans
        (add_zero (1/2 : ℚ))))

-- Reference: program's own toy; as `coinPredict_loaded_tails_mass`.
/-- The `tails` cell of the fair coin has mass `1/2`. -/
theorem coinPredict_fair_tails_mass :
    tableMass (coinPredict CoinHyp.fair) Coin.tails = 1/2 :=
  (tableMass_cons_diff (1/2, Coin.heads) [(1/2, Coin.tails)] Coin.tails
    (fun h => Coin.noConfusion h)).trans
    ((tableMass_cons_same (1/2, Coin.tails) [] Coin.tails rfl).trans
      ((congrArg (fun x => (1/2, Coin.tails).1 + x) (tableMass_nil Coin.tails)).trans
        (add_zero (1/2 : ℚ))))

-- Reference: program's own toy; as `coinPredict_loaded_tails_mass`.
/-- The `heads` cell of the biased coin has mass `2/3`. -/
theorem coinPredict_biased_heads_mass :
    tableMass (coinPredict CoinHyp.biased) Coin.heads = 2/3 :=
  (tableMass_cons_same (2/3, Coin.heads) [(1/3, Coin.tails)] Coin.heads rfl).trans
    ((congrArg (fun x => (2/3, Coin.heads).1 + x)
        (tableMass_cons_diff (1/3, Coin.tails) [] Coin.heads (fun h => Coin.noConfusion h))).trans
      ((congrArg (fun x => (2/3, Coin.heads).1 + x) (tableMass_nil Coin.heads)).trans
        (add_zero (2/3 : ℚ))))

-- Reference: program's own toy; as `coinPredict_loaded_tails_mass`.
/-- The `tails` cell of the biased coin has mass `1/3`. -/
theorem coinPredict_biased_tails_mass :
    tableMass (coinPredict CoinHyp.biased) Coin.tails = 1/3 :=
  (tableMass_cons_diff (2/3, Coin.heads) [(1/3, Coin.tails)] Coin.tails
    (fun h => Coin.noConfusion h)).trans
    ((tableMass_cons_same (1/3, Coin.tails) [] Coin.tails rfl).trans
      ((congrArg (fun x => (1/3, Coin.tails).1 + x) (tableMass_nil Coin.tails)).trans
        (add_zero (1/3 : ℚ))))

-- Reference: [Popper], ch. IV, §21; from `falsifiableHyp_eq_true` with the
-- witness `tails` and `coinPredict_loaded_tails_mass`.
-- REVIEW(citation): as on `falsifiable`.
/-- The loaded coin is falsifiable (its `tails` cell has zero mass). -/
theorem loaded_falsifiable :
    Experiment.falsifiableHyp coinExperiment CoinHyp.loaded = true :=
  (Experiment.falsifiableHyp_eq_true coinExperiment CoinHyp.loaded).mpr
    ⟨Coin.tails, List.mem_cons_of_mem Coin.heads (List.mem_cons_self (a := Coin.tails) (l := [])),
      coinPredict_loaded_tails_mass⟩

-- Reference: [Popper], ch. IV, §21; from `falsifiableHyp_eq_true`: any witness
-- cell would have mass `1/2 ≠ 0` (`coinPredict_fair_heads_mass`/`_tails_mass`,
-- `div_ne_zero`).
-- REVIEW(citation): as on `falsifiable`.
/-- The fair coin is not falsifiable (no zero-mass cell). -/
theorem fair_not_falsifiable :
    Experiment.falsifiableHyp coinExperiment CoinHyp.fair = false :=
  Bool.eq_false_iff.mpr (fun h => by
    obtain ⟨o, ho, hm⟩ :=
      (Experiment.falsifiableHyp_eq_true coinExperiment CoinHyp.fair).mp h
    have hne : (1/2 : ℚ) ≠ 0 :=
      div_ne_zero one_ne_zero (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero 1))
    rcases List.mem_cons.mp ho with hok | hot
    · exact hne ((Eq.subst
          (motive := fun x => tableMass (coinExperiment.predict CoinHyp.fair) x = 0) hok hm).symm
        |>.trans coinPredict_fair_heads_mass |>.symm)
    · rcases List.mem_cons.mp hot with hot' | hn
      · exact hne ((Eq.subst
            (motive := fun x => tableMass (coinExperiment.predict CoinHyp.fair) x = 0) hot' hm).symm
          |>.trans coinPredict_fair_tails_mass |>.symm)
      · exact absurd hn List.not_mem_nil)

-- Reference: [Popper], ch. IV, §21; as `fair_not_falsifiable` with
-- `coinPredict_biased_heads_mass` (`2/3 ≠ 0`).
-- REVIEW(citation): as on `falsifiable`.
/-- The biased coin is not falsifiable (no zero-mass cell). -/
theorem biased_not_falsifiable :
    Experiment.falsifiableHyp coinExperiment CoinHyp.biased = false :=
  Bool.eq_false_iff.mpr (fun h => by
    obtain ⟨o, ho, hm⟩ :=
      (Experiment.falsifiableHyp_eq_true coinExperiment CoinHyp.biased).mp h
    have hne : (2/3 : ℚ) ≠ 0 :=
      div_ne_zero (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero 1))
        (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero 2))
    rcases List.mem_cons.mp ho with hok | hot
    · exact hne ((Eq.subst
          (motive := fun x => tableMass (coinExperiment.predict CoinHyp.biased) x = 0) hok hm).symm
        |>.trans coinPredict_biased_heads_mass |>.symm)
    · rcases List.mem_cons.mp hot with hot' | hn
      · -- the `tails` cell has mass `1/3`; same shape as the `heads` case
        have h13 : (1/3 : ℚ) ≠ 0 :=
          div_ne_zero one_ne_zero (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero 2))
        exact h13 ((Eq.subst
            (motive := fun x => tableMass (coinExperiment.predict CoinHyp.biased) x = 0) hot' hm).symm
          |>.trans coinPredict_biased_tails_mass |>.symm)
      · exact absurd hn List.not_mem_nil)

-- Reference: program's own toy (ticket #28, item (d')): print the two-phase
-- run and the falsifiability predicate computed on the three toy hypotheses.
#eval (coinPrereg.outcomes, coinPrereg.hypotheses, coinPrereg.predict CoinHyp.fair)
#eval (coinExperiment.observation, coinExperiment.blind)
#eval coinHypotheses.map fun h =>
  (h, Experiment.falsifiableHyp coinExperiment h, isDistribution (coinPredict h))

end BoringLab
