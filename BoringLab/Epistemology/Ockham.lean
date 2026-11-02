/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import BoringLab.Epistemology.Learning

/-!
# The Ockham shadow: simplicity and mind-change bounds

Ticket #32 (EPI.3.2), building on #31 (`BoringLab.Epistemology.Learning`).
The Ockham-theorem program's shadow on the ℚ-mass carrier:

* **(a)** simplicity as data: an explicit complexity measure
  `complexity : hyp → ℕ`; the instance here is **Popper content** — the
  number of zero-mass cells (`zeroCellCount`) of a prediction table over the
  fixed outcome space, i.e. the number of refuted observations;
* **(b)** the Ockham method (`ockhamLearner`): always conjecture the
  simplest hypothesis consistent with the data prefix — computable on
  bounded families by a min-scan over the finite filtered list;
* **(c)** the mind-change bound on declared toy families is a named hole with
  an enumeration peeling plan (`ockham_min_changes_toy`); the general
  efficiency theorems (Kelly; Genin–Kelly) are statement-layer and deferred,
  named — NOT claimed;
* **(d)** the calibration instance: the two fully falsifiable coin
  hypotheses (`alwaysHeads`, `alwaysTails`) — the Ockham learner's output
  flips exactly once on the schedule `[heads, tails]`
  (`ockham_two_heads`, `ockham_two_heads_tails`, `ockham_two_mind_changes`),
  all closed computations proved by `rfl`, printed by `#eval`.

Honest grading (D.2 naming): bounded shadow, not the general theorem — the
names say so.

## References
* [Kelly 2007] K. T. Kelly, "Ockham's Razor, Empirical Complexity, and
  Truth-finding Efficiency", *Theoretical Computer Science* 383:270–289,
  2007.
* [Genin–Kelly] K. Genin, K. T. Kelly, "A Non-circular Justification of
  Ockham's Razor in Theoretical Inference", 2015; Genin–Kelly on Ockham
  efficiency theories, 2019.
  REVIEW(citation): pin the exact Genin–Kelly titles/venues in review.
* [Popper] K. R. Popper, *The Logic of Scientific Discovery*, 1959, ch. IV
  (content/falsifiability — the zero-cell count).
* Program register: BoringLab ticket #32 (EPI.3.2); the toy is the program's
  own.
-/

namespace BoringLab

/-! ## Simplicity as data; the Ockham method -/

-- Reference: core decidable `Nat.le` (an explicit two-argument minimum; the
-- program's own, avoiding instance-chosen `min`).
/-- The two-argument minimum on `ℕ`, as explicit data. -/
def natMin (a b : ℕ) : ℕ := if a ≤ b then a else b

-- Reference: ticket #32, items (a)/(b): the minimum complexity over a
-- finite list of hypotheses, by a min-scan (recursion on the list).
/-- The **minimum complexity** over a finite list of hypotheses (min-scan);
the empty list carries `0` (the outer `ockhamLearner` handles the empty case
by its default). -/
def minComplexity {hyp : Type} (complexity : hyp → ℕ) : List hyp → ℕ
  | [] => 0
  | [h] => complexity h
  | h :: rest => natMin (complexity h) (minComplexity complexity rest)

-- Reference: ticket #32, item (b); [Kelly 2007] (conjecture the simplest
-- hypothesis consistent with the data): computable on bounded families —
-- filter the family to the compatible hypotheses (Bool shadow), min-scan
-- their complexities, output the first achieving the minimum (default if
-- none).
/-- The **Ockham learner**: the first hypothesis of `hs` compatible with the
prefix `p` whose complexity is minimal among the compatible ones; `default`
if none is compatible. -/
def ockhamLearner {hyp datum : Type} (hs : List hyp) (mass : hyp → datum → ℚ)
    (complexity : hyp → ℕ) (default : hyp) (p : List datum) : hyp :=
  let cands := hs.filter fun h => compatibleBool mass h p
  let m := minComplexity complexity cands
  match cands.filter (fun h => if complexity h = m then true else false) with
  | [] => default
  | h :: _ => h

-- Reference: computation steps of `ockhamLearner` (as `elimLearner_cons`);
-- `rfl` only in these primitive definitional lemmas, via `Eq.subst` on the
-- scrutinee equality.
/-- The Ockham learner on a nonempty min-filter list returns its head. -/
theorem ockhamLearner_cons {hyp datum : Type} (hs : List hyp) (mass : hyp → datum → ℚ)
    (complexity : hyp → ℕ) (default : hyp) (p : List datum) (h : hyp) (rest : List hyp)
    (he : ((hs.filter fun h => compatibleBool mass h p).filter
        fun h =>
          if complexity h = minComplexity complexity (hs.filter fun h => compatibleBool mass h p)
            then true else false) = h :: rest) :
    ockhamLearner hs mass complexity default p = h :=
  Eq.subst (motive := fun l => (match l with | [] => default | h :: _ => h) = h) he.symm rfl

-- Reference: computation step of `ockhamLearner`.
/-- The Ockham learner on an empty min-filter list returns the default. -/
theorem ockhamLearner_nil {hyp datum : Type} (hs : List hyp) (mass : hyp → datum → ℚ)
    (complexity : hyp → ℕ) (default : hyp) (p : List datum)
    (he : ((hs.filter fun h => compatibleBool mass h p).filter
        fun h =>
          if complexity h = minComplexity complexity (hs.filter fun h => compatibleBool mass h p)
            then true else false) = []) :
    ockhamLearner hs mass complexity default p = default :=
  Eq.subst (motive := fun l => (match l with | [] => default | h :: _ => h) = default)
    he.symm rfl

-- Reference: ticket #32, item (c) — the mind-change bound, bounded case.
-- TEMPORARY SORRY: the honest proof has not been instantiated yet.
-- PEELING PLAN: on a fixed schedule `s`, `mindChangesOn M s` depends only on
-- the outputs of `M` at the `s.length + 1` prefixes; enumerate the finitely
-- many output tuples (`exists_conservative_method`'s peeling plan from #31)
-- and check the inequality for `ockhamLearner` by closed computation
-- (`rfl`-peeling per schedule). General efficiency theorems (Kelly 2007;
-- Genin–Kelly) remain statement-layer, deferred, named.
/-- **Ockham minimizes mind changes on the declared toy schedules**: on every
declared schedule, the Ockham learner's mind-change count is minimal among
all learners. -/
theorem ockham_min_changes_toy {hyp datum : Type} [DecidableEq hyp] [DecidableEq datum]
    (hs : List hyp) (mass : hyp → datum → ℚ) (complexity : hyp → ℕ) (default : hyp)
    (schedules : List (List datum)) (s : List datum) (hsSched : s ∈ schedules) :
    ∀ M : List datum → hyp,
      mindChangesOn (ockhamLearner hs mass complexity default) s ≤ mindChangesOn M s := by
  sorry

/-! ## Popper content as the simplicity measure -/

-- Reference: [Popper], ch. IV, §21 — the content of a theory is measured by
-- the observations it rules out; data-level shadow on a prediction table: the
-- number of outcome-space cells of zero mass.
/-- The **zero-cell count** of a prediction table over a fixed outcome space:
the number of refuted outcomes (the Popper content, as a count). -/
def zeroCellCount {hyp outcome : Type} [DecidableEq outcome]
    (predict : hyp → List (ℚ × outcome)) (outcomes : List outcome) (h : hyp) : ℕ :=
  (outcomes.filter fun o => isZeroQ (tableMass (predict h) o)).length

/-! ## Calibration instance: the two falsifiable coin hypotheses -/

-- Reference: program's own calibration instance (ticket #32, item (d)): two
-- maximally falsifiable hypotheses on the #28 coin outcome space.
/-- The two-hypothesis family: "always heads" vs "always tails". -/
inductive TwoHyp where
  | alwaysHeads
  | alwaysTails
deriving DecidableEq, Repr

-- Reference: ticket #32, toy (d); the prediction tables: a point mass on
-- the claimed outcome, zero on the other (the maximally falsifiable
-- distributions on the two-point outcome space).
/-- The prediction tables of the two-hypothesis family. -/
def twoHypPredict : TwoHyp → List (ℚ × Coin)
  | .alwaysHeads => [(1, Coin.heads), (0, Coin.tails)]
  | .alwaysTails => [(0, Coin.heads), (1, Coin.tails)]

-- Reference: ticket #32, toy (d).
/-- The two-hypothesis family as a list. -/
def twoHyps : List TwoHyp := [.alwaysHeads, .alwaysTails]

-- Reference: ticket #32, toy (d): the mass function of the instance.
/-- The mass function of the two-hypothesis instance. -/
def twoMass (h : TwoHyp) (c : Coin) : ℚ := tableMassOf twoHypPredict h c

-- Reference: ticket #32, item (a): the simplicity measure = Popper content
-- (zero-cell count); both hypotheses rule out exactly one outcome.
/-- The simplicity measure of the instance: the zero-cell count. -/
def twoComplexity (h : TwoHyp) : ℕ := zeroCellCount twoHypPredict coinOutcomes h

/-! ### Mass computations of the instance

The closed computations below are peeled step by step: `tableMass` via #28's
`tableMass_cons_same`/`tableMass_cons_diff`/`tableMass_nil`, closing the `ℚ`
arithmetic with `add_zero` (`Rat.add` is kernel-irreducible at the pin, so
these are NOT `rfl`; the pattern is #28's `coinPredict_*_mass`), then
`Eq.subst` into the `Bool` tests, and core `List.filter`/`List.all` steps.
-/

-- Reference: #28's `tableMass_cons_same`/`tableMass_cons_diff`/`tableMass_nil`
-- + `add_zero` on `ℚ`, as in `coinPredict_loaded_tails_mass` (#28).
/-- The mass of `heads` under `alwaysHeads` is `1`. -/
theorem twoMass_alwaysHeads_heads : twoMass .alwaysHeads Coin.heads = 1 :=
  (tableMass_cons_same (1, Coin.heads) [(0, Coin.tails)] Coin.heads rfl).trans
    ((congrArg (fun x => (1, Coin.heads).1 + x)
        (tableMass_cons_diff (0, Coin.tails) [] Coin.heads (fun h => Coin.noConfusion h))).trans
      ((congrArg (fun x => (1, Coin.heads).1 + x) (tableMass_nil Coin.heads)).trans
        (add_zero (1 : ℚ))))

-- Reference: as on `twoMass_alwaysHeads_heads`.
/-- The mass of `tails` under `alwaysHeads` is `0`. -/
theorem twoMass_alwaysHeads_tails : twoMass .alwaysHeads Coin.tails = 0 :=
  (tableMass_cons_diff (1, Coin.heads) [(0, Coin.tails)] Coin.tails
      (fun h => Coin.noConfusion h)).trans
    ((tableMass_cons_same (0, Coin.tails) [] Coin.tails rfl).trans
      ((congrArg (fun x => (0, Coin.tails).1 + x) (tableMass_nil Coin.tails)).trans
        (add_zero (0 : ℚ))))

-- Reference: as on `twoMass_alwaysHeads_heads`.
/-- The mass of `heads` under `alwaysTails` is `0`. -/
theorem twoMass_alwaysTails_heads : twoMass .alwaysTails Coin.heads = 0 :=
  (tableMass_cons_same (0, Coin.heads) [(1, Coin.tails)] Coin.heads rfl).trans
    ((congrArg (fun x => (0, Coin.heads).1 + x)
        (tableMass_cons_diff (1, Coin.tails) [] Coin.heads (fun h => Coin.noConfusion h))).trans
      ((congrArg (fun x => (0, Coin.heads).1 + x) (tableMass_nil Coin.heads)).trans
        (add_zero (0 : ℚ))))

-- Reference: as on `twoMass_alwaysHeads_heads`.
/-- The mass of `tails` under `alwaysTails` is `1`. -/
theorem twoMass_alwaysTails_tails : twoMass .alwaysTails Coin.tails = 1 :=
  (tableMass_cons_diff (0, Coin.heads) [(1, Coin.tails)] Coin.tails
      (fun h => Coin.noConfusion h)).trans
    ((tableMass_cons_same (1, Coin.tails) [] Coin.tails rfl).trans
      ((congrArg (fun x => (1, Coin.tails).1 + x) (tableMass_nil Coin.tails)).trans
        (add_zero (1 : ℚ))))

-- Reference: `massAllows_eq_true` (#31) + `one_ne_zero` on `ℚ`.
/-- The mass flag of `heads` under `alwaysHeads` is `true`. -/
theorem massAllows_alwaysHeads_heads :
    massAllows twoMass .alwaysHeads Coin.heads = true :=
  (massAllows_eq_true twoMass .alwaysHeads Coin.heads).mpr
    (fun h0 => one_ne_zero (twoMass_alwaysHeads_heads.symm.trans h0))

-- Reference: `massAllows_eq_true` (#31) + core `Bool.eq_false_iff`.
/-- The mass flag of `tails` under `alwaysHeads` is `false`. -/
theorem massAllows_alwaysHeads_tails :
    massAllows twoMass .alwaysHeads Coin.tails = false :=
  Bool.eq_false_iff.mpr
    (fun h => (massAllows_eq_true twoMass .alwaysHeads Coin.tails).mp h
      twoMass_alwaysHeads_tails)

-- Reference: as on `massAllows_alwaysHeads_tails`.
/-- The mass flag of `heads` under `alwaysTails` is `false`. -/
theorem massAllows_alwaysTails_heads :
    massAllows twoMass .alwaysTails Coin.heads = false :=
  Bool.eq_false_iff.mpr
    (fun h => (massAllows_eq_true twoMass .alwaysTails Coin.heads).mp h
      twoMass_alwaysTails_heads)

-- Reference: as on `massAllows_alwaysHeads_heads`.
/-- The mass flag of `tails` under `alwaysTails` is `true`. -/
theorem massAllows_alwaysTails_tails :
    massAllows twoMass .alwaysTails Coin.tails = true :=
  (massAllows_eq_true twoMass .alwaysTails Coin.tails).mpr
    (fun h0 => one_ne_zero (twoMass_alwaysTails_tails.symm.trans h0))

-- Reference: computation steps of `compatibleBool` (core `List.all_cons`/
-- `List.all_nil`, definitional).
/-- Compatibility unfolds on a cons prefix. -/
theorem compatibleBool_cons {hyp datum : Type} (mass : hyp → datum → ℚ) (h : hyp)
    (d : datum) (p : List datum) :
    compatibleBool mass h (d :: p) = (massAllows mass h d && compatibleBool mass h p) := rfl

-- Reference: computation step of `compatibleBool` (core `List.all_nil`).
/-- The empty prefix is compatible with every hypothesis. -/
theorem compatibleBool_nil {hyp datum : Type} (mass : hyp → datum → ℚ) (h : hyp) :
    compatibleBool mass h [] = true := rfl

-- Reference: `compatibleBool_cons`/`compatibleBool_nil` + `Eq.subst` of the
-- mass flag.
/-- On `[heads]`, `alwaysHeads` is compatible. -/
theorem compatibleBool_alwaysHeads_heads :
    compatibleBool twoMass .alwaysHeads [Coin.heads] = true :=
  Eq.subst (motive := fun b => (b && true) = true) massAllows_alwaysHeads_heads.symm rfl

-- Reference: as on `compatibleBool_alwaysHeads_heads`.
/-- On `[heads]`, `alwaysTails` is not compatible. -/
theorem compatibleBool_alwaysTails_heads :
    compatibleBool twoMass .alwaysTails [Coin.heads] = false :=
  Eq.subst (motive := fun b => (b && true) = false) massAllows_alwaysTails_heads.symm rfl

-- Reference: as on `compatibleBool_alwaysHeads_heads` (two `Eq.subst` steps).
/-- On `[heads, tails]`, `alwaysHeads` is not compatible (tails refutes it). -/
theorem compatibleBool_alwaysHeads_heads_tails :
    compatibleBool twoMass .alwaysHeads [Coin.heads, Coin.tails] = false := by
  exact Eq.subst
    (motive := fun b => (b && (massAllows twoMass .alwaysHeads Coin.tails && true)) = false)
    massAllows_alwaysHeads_heads.symm
    (Eq.subst (motive := fun c => (true && (c && true)) = false)
      massAllows_alwaysHeads_tails.symm rfl)

-- Reference: as on `compatibleBool_alwaysHeads_heads_tails`.
/-- On `[heads, tails]`, `alwaysTails` is not compatible (heads refutes it). -/
theorem compatibleBool_alwaysTails_heads_tails :
    compatibleBool twoMass .alwaysTails [Coin.heads, Coin.tails] = false := by
  exact Eq.subst
    (motive := fun b => (b && (massAllows twoMass .alwaysTails Coin.tails && true)) = false)
    massAllows_alwaysTails_heads.symm
    (Eq.subst (motive := fun c => (false && (c && true)) = false)
      massAllows_alwaysTails_tails.symm rfl)

-- Reference: core `List.filter_cons_of_pos`/`List.filter_cons_of_neg`/
-- `List.filter_nil` + the compatibility flags above.
/-- On `[heads]`, only `alwaysHeads` of the family is compatible. -/
theorem filter_twoHyps_heads :
    twoHyps.filter (fun h => compatibleBool twoMass h [Coin.heads]) = [TwoHyp.alwaysHeads] :=
  (List.filter_cons_of_pos (p := fun h => compatibleBool twoMass h [Coin.heads])
      (a := TwoHyp.alwaysHeads) (l := [TwoHyp.alwaysTails])
      compatibleBool_alwaysHeads_heads).trans
    ((congrArg (fun l => TwoHyp.alwaysHeads :: l)
        (List.filter_cons_of_neg (p := fun h => compatibleBool twoMass h [Coin.heads])
          (a := TwoHyp.alwaysTails) (l := [])
          (fun h => Bool.false_ne_true (compatibleBool_alwaysTails_heads.symm.trans h)))).trans
      (congrArg (fun l => TwoHyp.alwaysHeads :: l) List.filter_nil))

-- Reference: as on `filter_twoHyps_heads`.
/-- On `[heads, tails]`, neither hypothesis of the family is compatible. -/
theorem filter_twoHyps_heads_tails :
    twoHyps.filter (fun h => compatibleBool twoMass h [Coin.heads, Coin.tails]) = [] :=
  (List.filter_cons_of_neg
      (p := fun h => compatibleBool twoMass h [Coin.heads, Coin.tails])
      (a := TwoHyp.alwaysHeads) (l := [TwoHyp.alwaysTails])
      (fun h => Bool.false_ne_true (compatibleBool_alwaysHeads_heads_tails.symm.trans h))).trans
    ((List.filter_cons_of_neg
        (p := fun h => compatibleBool twoMass h [Coin.heads, Coin.tails])
        (a := TwoHyp.alwaysTails) (l := [])
        (fun h => Bool.false_ne_true (compatibleBool_alwaysTails_heads_tails.symm.trans h))).trans
      List.filter_nil)

-- Reference: as on `filter_twoHyps_heads` + `compatibleBool_nil`.
/-- On the empty prefix, both hypotheses of the family are compatible. -/
theorem filter_twoHyps_nil :
    twoHyps.filter (fun h => compatibleBool twoMass h []) = twoHyps :=
  (List.filter_cons_of_pos (p := fun h => compatibleBool twoMass h [])
      (a := TwoHyp.alwaysHeads) (l := [TwoHyp.alwaysTails])
      (compatibleBool_nil twoMass TwoHyp.alwaysHeads)).trans
    (congrArg (fun l => TwoHyp.alwaysHeads :: l)
      ((List.filter_cons_of_pos (p := fun h => compatibleBool twoMass h [])
          (a := TwoHyp.alwaysTails) (l := []) (compatibleBool_nil twoMass TwoHyp.alwaysTails)).trans
        (congrArg (fun l => TwoHyp.alwaysTails :: l) List.filter_nil)))

-- Reference: `isZeroQ` on `ℚ` literals (definitional) + `Eq.subst` of the mass.
/-- The zero-cell test on `heads` under `alwaysHeads` is `false`. -/
theorem isZeroQ_twoMass_alwaysHeads_heads :
    isZeroQ (twoMass .alwaysHeads Coin.heads) = false :=
  Eq.subst (motive := fun x => isZeroQ x = false) twoMass_alwaysHeads_heads.symm rfl

-- Reference: as on `isZeroQ_twoMass_alwaysHeads_heads`.
/-- The zero-cell test on `tails` under `alwaysHeads` is `true`. -/
theorem isZeroQ_twoMass_alwaysHeads_tails :
    isZeroQ (twoMass .alwaysHeads Coin.tails) = true :=
  Eq.subst (motive := fun x => isZeroQ x = true) twoMass_alwaysHeads_tails.symm rfl

-- Reference: as on `isZeroQ_twoMass_alwaysHeads_heads`.
/-- The zero-cell test on `heads` under `alwaysTails` is `true`. -/
theorem isZeroQ_twoMass_alwaysTails_heads :
    isZeroQ (twoMass .alwaysTails Coin.heads) = true :=
  Eq.subst (motive := fun x => isZeroQ x = true) twoMass_alwaysTails_heads.symm rfl

-- Reference: as on `isZeroQ_twoMass_alwaysHeads_heads`.
/-- The zero-cell test on `tails` under `alwaysTails` is `false`. -/
theorem isZeroQ_twoMass_alwaysTails_tails :
    isZeroQ (twoMass .alwaysTails Coin.tails) = false :=
  Eq.subst (motive := fun x => isZeroQ x = false) twoMass_alwaysTails_tails.symm rfl

-- Reference: `zeroCellCount` (filter over `coinOutcomes`) + the zero-cell
-- flags above + `List.filter_cons_of_neg`/`_of_pos`/`List.filter_nil`.
/-- The Popper content of `alwaysHeads` is `1` (one zero-mass cell). -/
theorem twoComplexity_alwaysHeads : twoComplexity .alwaysHeads = 1 :=
  (congrArg List.length
    ((List.filter_cons_of_neg (p := fun o => isZeroQ (twoMass .alwaysHeads o))
        (a := Coin.heads) (l := [Coin.tails])
        (fun h => Bool.false_ne_true (isZeroQ_twoMass_alwaysHeads_heads.symm.trans h))).trans
      ((List.filter_cons_of_pos (p := fun o => isZeroQ (twoMass .alwaysHeads o))
          (a := Coin.tails) (l := []) isZeroQ_twoMass_alwaysHeads_tails).trans
        (congrArg (fun l => Coin.tails :: l) List.filter_nil)))).trans
    rfl

-- Reference: as on `twoComplexity_alwaysHeads`.
/-- The Popper content of `alwaysTails` is `1` (one zero-mass cell). -/
theorem twoComplexity_alwaysTails : twoComplexity .alwaysTails = 1 :=
  (congrArg List.length
    ((List.filter_cons_of_pos (p := fun o => isZeroQ (twoMass .alwaysTails o))
        (a := Coin.heads) (l := [Coin.tails]) isZeroQ_twoMass_alwaysTails_heads).trans
      (congrArg (fun l => Coin.heads :: l)
        ((List.filter_cons_of_neg (p := fun o => isZeroQ (twoMass .alwaysTails o))
            (a := Coin.tails) (l := [])
            (fun h => Bool.false_ne_true (isZeroQ_twoMass_alwaysTails_tails.symm.trans h))).trans
          List.filter_nil)))).trans
    rfl

-- Reference: computation steps of `minComplexity` on concrete lists
-- (definitional) + `twoComplexity_alwaysHeads`.
/-- The minimum complexity over `[alwaysHeads]` is `1`. -/
theorem minComplexity_singleton_alwaysHeads :
    minComplexity twoComplexity [TwoHyp.alwaysHeads] = 1 :=
  twoComplexity_alwaysHeads

-- Reference: computation step of `minComplexity` (definitional on the
-- concrete family) + `Eq.subst` of the two complexities + `natMin 1 1`
-- (definitional).
/-- The minimum complexity over the two-hypothesis family is `1`. -/
theorem minComplexity_twoHyps : minComplexity twoComplexity twoHyps = 1 := by
  exact Eq.subst (motive := fun n => natMin n (twoComplexity TwoHyp.alwaysTails) = 1)
    twoComplexity_alwaysHeads.symm
    (Eq.subst (motive := fun m => natMin (1 : ℕ) m = 1) twoComplexity_alwaysTails.symm rfl)

-- Reference: `Eq.subst` of the candidate list and of the minimum, then core
-- `List.filter_cons_of_pos`/`List.filter_nil`.
/-- On `[heads]`, the min-filter list is `[alwaysHeads]`. -/
theorem minFilter_twoHyps_heads :
    ((twoHyps.filter fun h => compatibleBool twoMass h [Coin.heads]).filter
      fun h => if twoComplexity h =
        minComplexity twoComplexity (twoHyps.filter fun h => compatibleBool twoMass h [Coin.heads])
        then true else false) = [TwoHyp.alwaysHeads] :=
  Eq.subst (motive := fun l =>
      (l.filter fun h => if twoComplexity h = minComplexity twoComplexity l then true else false)
        = [TwoHyp.alwaysHeads])
    filter_twoHyps_heads.symm
    (Eq.subst (motive := fun n =>
        ([TwoHyp.alwaysHeads].filter fun h => if twoComplexity h = n then true else false)
          = [TwoHyp.alwaysHeads])
      minComplexity_singleton_alwaysHeads.symm
      ((List.filter_cons_of_pos
          (p := fun h => if twoComplexity h = (1 : ℕ) then true else false)
          (a := TwoHyp.alwaysHeads) (l := [])
          (Eq.subst (motive := fun c => (if c = (1 : ℕ) then true else false) = true)
            twoComplexity_alwaysHeads.symm rfl)).trans
        (congrArg (fun l => TwoHyp.alwaysHeads :: l) List.filter_nil)))

-- Reference: `Eq.subst` of the candidate list + core `List.filter_nil`.
/-- On `[heads, tails]`, the min-filter list is empty. -/
theorem minFilter_twoHyps_heads_tails :
    ((twoHyps.filter fun h => compatibleBool twoMass h [Coin.heads, Coin.tails]).filter
      fun h => if twoComplexity h =
        minComplexity twoComplexity
          (twoHyps.filter fun h => compatibleBool twoMass h [Coin.heads, Coin.tails])
        then true else false) = [] :=
  Eq.subst (motive := fun l =>
      (l.filter fun h => if twoComplexity h = minComplexity twoComplexity l then true else false)
        = [])
    filter_twoHyps_heads_tails.symm List.filter_nil

-- Reference: as on `minFilter_twoHyps_heads` (two `filter_cons_of_pos` steps).
/-- On the empty prefix, the min-filter list is the whole family. -/
theorem minFilter_twoHyps_nil :
    ((twoHyps.filter fun h => compatibleBool twoMass h []).filter
      fun h => if twoComplexity h =
        minComplexity twoComplexity (twoHyps.filter fun h => compatibleBool twoMass h [])
        then true else false) = [TwoHyp.alwaysHeads, TwoHyp.alwaysTails] :=
  Eq.subst (motive := fun l =>
      (l.filter fun h => if twoComplexity h = minComplexity twoComplexity l then true else false)
        = [TwoHyp.alwaysHeads, TwoHyp.alwaysTails])
    filter_twoHyps_nil.symm
    (Eq.subst (motive := fun n =>
        (twoHyps.filter fun h => if twoComplexity h = n then true else false)
          = [TwoHyp.alwaysHeads, TwoHyp.alwaysTails])
      minComplexity_twoHyps.symm
      ((List.filter_cons_of_pos
          (p := fun h => if twoComplexity h = (1 : ℕ) then true else false)
          (a := TwoHyp.alwaysHeads) (l := [TwoHyp.alwaysTails])
          (Eq.subst (motive := fun c => (if c = (1 : ℕ) then true else false) = true)
            twoComplexity_alwaysHeads.symm rfl)).trans
        (congrArg (fun l => TwoHyp.alwaysHeads :: l)
          ((List.filter_cons_of_pos
              (p := fun h => if twoComplexity h = (1 : ℕ) then true else false)
              (a := TwoHyp.alwaysTails) (l := [])
              (Eq.subst (motive := fun c => (if c = (1 : ℕ) then true else false) = true)
                twoComplexity_alwaysTails.symm rfl)).trans
            (congrArg (fun l => TwoHyp.alwaysTails :: l) List.filter_nil)))))

-- Reference: ticket #32, acceptance (d): on `[heads]` only `alwaysHeads` is
-- compatible, so the Ockham output is `alwaysHeads` (`ockhamLearner_cons` +
-- `minFilter_twoHyps_heads`).
/-- The Ockham learner outputs `alwaysHeads` on observing heads. -/
theorem ockham_two_heads :
    ockhamLearner twoHyps twoMass twoComplexity .alwaysTails [Coin.heads] = .alwaysHeads :=
  ockhamLearner_cons twoHyps twoMass twoComplexity .alwaysTails [Coin.heads]
    TwoHyp.alwaysHeads [] minFilter_twoHyps_heads

-- Reference: ticket #32, acceptance (d): on `[heads, tails]` both hypotheses
-- are refuted, so the Ockham output is the default `alwaysTails`
-- (`ockhamLearner_nil` + `minFilter_twoHyps_heads_tails`) — the flip.
/-- The Ockham learner flips to `alwaysTails` once tails is observed. -/
theorem ockham_two_heads_tails :
    ockhamLearner twoHyps twoMass twoComplexity .alwaysTails [Coin.heads, Coin.tails]
      = .alwaysTails :=
  ockhamLearner_nil twoHyps twoMass twoComplexity .alwaysTails [Coin.heads, Coin.tails]
    minFilter_twoHyps_heads_tails

-- Reference: ticket #32, toy (d): the empty prefix leaves both compatible and
-- the min-filter keeps the head `alwaysHeads`.
/-- The Ockham learner outputs `alwaysHeads` on the empty prefix. -/
theorem ockham_two_empty :
    ockhamLearner twoHyps twoMass twoComplexity .alwaysTails [] = .alwaysHeads :=
  ockhamLearner_cons twoHyps twoMass twoComplexity .alwaysTails [] TwoHyp.alwaysHeads
    [TwoHyp.alwaysTails] minFilter_twoHyps_nil

-- Reference: ticket #32, acceptance (d): exactly one mind change on the
-- two-round schedule — `mindChangesOn` unfolds (definitional `List.range`/
-- `List.take` on the concrete schedule), the three prefix outputs are
-- `ockham_two_empty`/`ockham_two_heads`/`ockham_two_heads_tails` (substituted
-- by `Eq.subst`), and the filter keeps only `n = 1`.
/-- The Ockham learner makes exactly one mind change on `[heads, tails]`. -/
theorem ockham_two_mind_changes :
    mindChangesOn (ockhamLearner twoHyps twoMass twoComplexity .alwaysTails)
      [Coin.heads, Coin.tails] = 1 := by
  have pred0 : (if (ockhamLearner twoHyps twoMass twoComplexity .alwaysTails)
      (List.take 0 [Coin.heads, Coin.tails]) =
      (ockhamLearner twoHyps twoMass twoComplexity .alwaysTails)
        (List.take (0 + 1) [Coin.heads, Coin.tails]) then false else true) = false :=
    Eq.subst (motive := fun x => (if x = (ockhamLearner twoHyps twoMass twoComplexity
        .alwaysTails) (List.take (0 + 1) [Coin.heads, Coin.tails]) then false else true) = false)
      ockham_two_empty.symm
      (Eq.subst (motive := fun y => (if (TwoHyp.alwaysHeads = y) then false else true) = false)
        ockham_two_heads.symm rfl)
  have pred1 : (if (ockhamLearner twoHyps twoMass twoComplexity .alwaysTails)
      (List.take 1 [Coin.heads, Coin.tails]) =
      (ockhamLearner twoHyps twoMass twoComplexity .alwaysTails)
        (List.take (1 + 1) [Coin.heads, Coin.tails]) then false else true) = true :=
    Eq.subst (motive := fun x => (if x = (ockhamLearner twoHyps twoMass twoComplexity
        .alwaysTails) (List.take (1 + 1) [Coin.heads, Coin.tails]) then false else true) = true)
      ockham_two_heads.symm
      (Eq.subst (motive := fun y => (if (TwoHyp.alwaysHeads = y) then false else true) = true)
        ockham_two_heads_tails.symm rfl)
  have pred2 : (if (ockhamLearner twoHyps twoMass twoComplexity .alwaysTails)
      (List.take 2 [Coin.heads, Coin.tails]) =
      (ockhamLearner twoHyps twoMass twoComplexity .alwaysTails)
        (List.take (2 + 1) [Coin.heads, Coin.tails]) then false else true) = false :=
    Eq.subst (motive := fun x => (if x = (ockhamLearner twoHyps twoMass twoComplexity
        .alwaysTails) (List.take (2 + 1) [Coin.heads, Coin.tails]) then false else true) = false)
      ockham_two_heads_tails.symm
      (Eq.subst (motive := fun y => (if (TwoHyp.alwaysTails = y) then false else true) = false)
        ockham_two_heads_tails.symm rfl)
  exact (congrArg List.length
    ((List.filter_cons_of_neg
        (p := fun n => (if (ockhamLearner twoHyps twoMass twoComplexity .alwaysTails)
            (List.take n [Coin.heads, Coin.tails]) =
          (ockhamLearner twoHyps twoMass twoComplexity .alwaysTails)
            (List.take (n + 1) [Coin.heads, Coin.tails]) then false else true))
        (a := 0) (l := [1, 2]) (fun h => Bool.false_ne_true (pred0.symm.trans h))).trans
      ((List.filter_cons_of_pos
          (p := fun n => (if (ockhamLearner twoHyps twoMass twoComplexity .alwaysTails)
              (List.take n [Coin.heads, Coin.tails]) =
            (ockhamLearner twoHyps twoMass twoComplexity .alwaysTails)
              (List.take (n + 1) [Coin.heads, Coin.tails]) then false else true))
          (a := 1) (l := [2]) pred1).trans
        (congrArg (fun l => (1 : ℕ) :: l)
          ((List.filter_cons_of_neg
              (p := fun n => (if (ockhamLearner twoHyps twoMass twoComplexity .alwaysTails)
                  (List.take n [Coin.heads, Coin.tails]) =
                (ockhamLearner twoHyps twoMass twoComplexity .alwaysTails)
                  (List.take (n + 1) [Coin.heads, Coin.tails]) then false else true))
              (a := 2) (l := []) (fun h => Bool.false_ne_true (pred2.symm.trans h))).trans
            List.filter_nil))))).trans rfl

-- Reference: ticket #32, acceptance: `#eval` prints the Ockham outputs per
-- prefix length and the mind-change count.
/-- The Ockham outputs on every prefix of the two-round schedule. -/
def twoLearnerOutputs : List (ℕ × TwoHyp) :=
  (List.range 3).map fun n =>
    (n, ockhamLearner twoHyps twoMass twoComplexity .alwaysTails
      (([Coin.heads, Coin.tails]).take n))

#eval twoLearnerOutputs
#eval mindChangesOn (ockhamLearner twoHyps twoMass twoComplexity .alwaysTails)
  [Coin.heads, Coin.tails]

end BoringLab
