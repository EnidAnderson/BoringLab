/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import BoringLab.Epistemology.Ockham
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Algebra.Order.Field.Basic

/-!
# Verisimilitude: truthlikeness orderings on the experiment carrier

Ticket #33 (EPI.4.1), building on the #28 experiment carrier and #31/#32
(`BoringLab.Epistemology.{Learning,Ockham}`). Popper's hardest formal
program, on the ℚ-mass carrier, with its history recorded honestly inside
the formalization:

* **(a)** the setting: hypothesis families over the outcome space, a
  designated true hypothesis (as data — the analytic convenience, declared);
* **(b)** truthlikeness orderings as explicit relations: the content ordering
  `contentLE` (inclusion of the allowed-outcome sets — the enumerable
  deductive consequences) and the likeness distance `likenessDist` (the
  sum of absolute mass differences, Niiniluoto-style min-sum shape);
* **(c)** the historical ledger as a data-level fact: the naive content-only
  ordering has the classic Popper/Miller/Tichý failure — a FALSE hypothesis
  whose content strictly exceeds the truth's ranks above the truth
  (`false_content_exceeds_truth`, proved on the declared toy family);
* **(d)** the combined measure axioms checked on bounded families are a
  named hole (the full measure-theoretic program is deferred, named).

## References
* [Popper 1963] K. R. Popper, *Conjectures and Refutations*, 1963, ch. I
  and App. I (verisimilitude; the content ordering).
* [Miller 1974] D. W. Miller, "Popper and the notion of verisimilitude",
  *British Journal for the Philosophy of Science* 25:175–185, 1974;
  [Tichý 1974] P. Tichý, "Problems of entailment-based definitions of
  verisimilitude", *BJPS* 25:125–134, 1974 — the refutation of the naive
  content-only ordering (made a theorem-on-data here).
* [Niiniluoto 1987] I. Niiniluoto, *Truthlikeness*, Synthese Library vol.
  272, 1987 — the min-sum distance measures.
* Program register: BoringLab ticket #33 (EPI.4.1); the toy family is the
  program's own.
-/

namespace BoringLab

/-! ## Content and likeness on the ℚ-mass carrier -/

-- Reference: [Popper 1963], App. I (the content of a theory = the set of
-- observations it rules out — equivalently the set it allows); data-level
-- shadow: the allowed-outcome list of a prediction table.
/-- The **content set** of a hypothesis over a fixed outcome space: the
allowed outcomes (positive-mass cells), as a list. -/
def contentSet {hyp outcome : Type} [DecidableEq outcome]
    (predict : hyp → List (ℚ × outcome)) (outcomes : List outcome) (h : hyp) : List outcome :=
  outcomes.filter (massAllows (tableMassOf predict) h)

-- Reference: [Popper 1963], App. I (h₁ ≤ h₂ in content iff h₁'s content is
-- included in h₂'s — h₂ says at least as much).
/-- The **content ordering** (`Prop`-valued): `h₁ ≤ h₂` iff every outcome
allowed by `h₁` is allowed by `h₂`. -/
def contentLE {hyp outcome : Type} [DecidableEq outcome]
    (predict : hyp → List (ℚ × outcome)) (outcomes : List outcome) (h₁ h₂ : hyp) : Prop :=
  ∀ o ∈ contentSet predict outcomes h₁, o ∈ contentSet predict outcomes h₂

-- Reference: [Niiniluoto 1987] (the min-sum likeness measure: sum of
-- absolute differences of the probability functions over the outcome
-- space); core `|·|` on ℚ and `List.sum`.
/-- The **likeness distance** between a hypothesis and the designated truth:
the sum of `|mass h o − mass hTrue o|` over the fixed outcome space. -/
def likenessDist {hyp outcome : Type} [DecidableEq outcome]
    (predict : hyp → List (ℚ × outcome)) (outcomes : List outcome) (h hTrue : hyp) : ℚ :=
  (outcomes.map fun o => |tableMassOf predict h o - tableMassOf predict hTrue o|).sum

-- Reference: [Niiniluoto 1987] (truthlikeness = closeness to the truth);
-- the induced ordering.
/-- The **verisimilitude ordering** (`Prop`-valued): `h₁ ≤ h₂` iff `h₁` is at
least as close to the designated truth as `h₂` in likeness distance. -/
def verisimilarLE {hyp outcome : Type} [DecidableEq outcome]
    (predict : hyp → List (ℚ × outcome)) (outcomes : List outcome) (hTrue h₁ h₂ : hyp) :
    Prop :=
  likenessDist predict outcomes h₁ hTrue ≤ likenessDist predict outcomes h₂ hTrue

-- Reference: core `le_refl` on ℚ.
/-- The verisimilitude ordering is reflexive. -/
theorem verisimilarLE_refl {hyp outcome : Type} [DecidableEq outcome]
    (predict : hyp → List (ℚ × outcome)) (outcomes : List outcome) (hTrue h : hyp) :
    verisimilarLE predict outcomes hTrue h h := le_refl _

/-! ## The toy family: truth vs a spread false hypothesis -/

-- Reference: program's own toy (ticket #33, item (c)): three hypotheses on
-- the two-point coin outcome space — the designated truth (point mass on
-- heads), a spread false hypothesis (uniform), and the opposite point mass.
/-- The toy verisimilitude family. -/
inductive VHyp where
  | truth
  | spread
  | opposite
deriving DecidableEq, Repr

-- Reference: ticket #33, toy (c): the prediction tables — point mass,
-- uniform, opposite point mass.
/-- The prediction tables of the toy family. -/
def vPredict : VHyp → List (ℚ × Coin)
  | .truth => [(1, Coin.heads), (0, Coin.tails)]
  | .spread => [(1/2, Coin.heads), (1/2, Coin.tails)]
  | .opposite => [(0, Coin.heads), (1, Coin.tails)]

/-! ### Mass computations of the toy family

The closed computations below are peeled step by step: `tableMass` via #28's
`tableMass_cons_same`/`tableMass_cons_diff`/`tableMass_nil`, closing the `ℚ`
arithmetic with `add_zero` (`Rat.add` is kernel-irreducible at the pin, so
these are NOT `rfl`; the pattern is #28's `coinPredict_*_mass` and #32's
`twoMass_*`), then `Eq.subst` into the `Bool` tests and core `List.filter`.
-/

-- Reference: #28's `tableMass_cons_same`/`tableMass_cons_diff`/`tableMass_nil`
-- + `add_zero` on `ℚ`, as in `twoMass_alwaysHeads_heads` (#32).
/-- The mass of `heads` under the truth hypothesis is `1`. -/
theorem vMass_truth_heads : tableMassOf vPredict .truth Coin.heads = 1 :=
  (tableMass_cons_same (1, Coin.heads) [(0, Coin.tails)] Coin.heads rfl).trans
    ((congrArg (fun x => (1, Coin.heads).1 + x)
        (tableMass_cons_diff (0, Coin.tails) [] Coin.heads (fun h => Coin.noConfusion h))).trans
      ((congrArg (fun x => (1, Coin.heads).1 + x) (tableMass_nil Coin.heads)).trans
        (add_zero (1 : ℚ))))

-- Reference: as on `vMass_truth_heads`.
/-- The mass of `tails` under the truth hypothesis is `0`. -/
theorem vMass_truth_tails : tableMassOf vPredict .truth Coin.tails = 0 :=
  (tableMass_cons_diff (1, Coin.heads) [(0, Coin.tails)] Coin.tails
      (fun h => Coin.noConfusion h)).trans
    ((tableMass_cons_same (0, Coin.tails) [] Coin.tails rfl).trans
      ((congrArg (fun x => (0, Coin.tails).1 + x) (tableMass_nil Coin.tails)).trans
        (add_zero (0 : ℚ))))

-- Reference: as on `vMass_truth_heads`.
/-- The mass of `heads` under the spread hypothesis is `1/2`. -/
theorem vMass_spread_heads : tableMassOf vPredict .spread Coin.heads = 1/2 :=
  (tableMass_cons_same (1/2, Coin.heads) [(1/2, Coin.tails)] Coin.heads rfl).trans
    ((congrArg (fun x => (1/2, Coin.heads).1 + x)
        (tableMass_cons_diff (1/2, Coin.tails) [] Coin.heads (fun h => Coin.noConfusion h))).trans
      ((congrArg (fun x => (1/2, Coin.heads).1 + x) (tableMass_nil Coin.heads)).trans
        (add_zero (1/2 : ℚ))))

-- Reference: as on `vMass_truth_heads`.
/-- The mass of `tails` under the spread hypothesis is `1/2`. -/
theorem vMass_spread_tails : tableMassOf vPredict .spread Coin.tails = 1/2 :=
  (tableMass_cons_diff (1/2, Coin.heads) [(1/2, Coin.tails)] Coin.tails
      (fun h => Coin.noConfusion h)).trans
    ((tableMass_cons_same (1/2, Coin.tails) [] Coin.tails rfl).trans
      ((congrArg (fun x => (1/2, Coin.tails).1 + x) (tableMass_nil Coin.tails)).trans
        (add_zero (1/2 : ℚ))))

-- Reference: as on `vMass_truth_heads`.
/-- The mass of `heads` under the opposite hypothesis is `0`. -/
theorem vMass_opposite_heads : tableMassOf vPredict .opposite Coin.heads = 0 :=
  (tableMass_cons_same (0, Coin.heads) [(1, Coin.tails)] Coin.heads rfl).trans
    ((congrArg (fun x => (0, Coin.heads).1 + x)
        (tableMass_cons_diff (1, Coin.tails) [] Coin.heads (fun h => Coin.noConfusion h))).trans
      ((congrArg (fun x => (0, Coin.heads).1 + x) (tableMass_nil Coin.heads)).trans
        (add_zero (0 : ℚ))))

-- Reference: as on `vMass_truth_heads`.
/-- The mass of `tails` under the opposite hypothesis is `1`. -/
theorem vMass_opposite_tails : tableMassOf vPredict .opposite Coin.tails = 1 :=
  (tableMass_cons_diff (0, Coin.heads) [(1, Coin.tails)] Coin.tails
      (fun h => Coin.noConfusion h)).trans
    ((tableMass_cons_same (1, Coin.tails) [] Coin.tails rfl).trans
      ((congrArg (fun x => (1, Coin.tails).1 + x) (tableMass_nil Coin.tails)).trans
        (add_zero (1 : ℚ))))

-- Reference: `massAllows_eq_true` (#31) + `one_ne_zero` on `ℚ`.
/-- The mass flag of `heads` under the truth is `true`. -/
theorem massAllows_truth_heads :
    massAllows (tableMassOf vPredict) .truth Coin.heads = true :=
  (massAllows_eq_true (tableMassOf vPredict) .truth Coin.heads).mpr
    (fun h0 => one_ne_zero (vMass_truth_heads.symm.trans h0))

-- Reference: `massAllows_eq_true` (#31) + core `Bool.eq_false_iff`.
/-- The mass flag of `tails` under the truth is `false`. -/
theorem massAllows_truth_tails :
    massAllows (tableMassOf vPredict) .truth Coin.tails = false :=
  Bool.eq_false_iff.mpr
    (fun h => (massAllows_eq_true (tableMassOf vPredict) .truth Coin.tails).mp h
      vMass_truth_tails)

-- Reference: `massAllows_eq_true` (#31) + `div_ne_zero` on `ℚ` (as in #28's
-- `fair_not_falsifiable`).
/-- The mass flag of `heads` under the spread hypothesis is `true`. -/
theorem massAllows_spread_heads :
    massAllows (tableMassOf vPredict) .spread Coin.heads = true :=
  (massAllows_eq_true (tableMassOf vPredict) .spread Coin.heads).mpr
    (fun h0 => div_ne_zero one_ne_zero (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero 1))
      (vMass_spread_heads.symm.trans h0))

-- Reference: as on `massAllows_spread_heads`.
/-- The mass flag of `tails` under the spread hypothesis is `true`. -/
theorem massAllows_spread_tails :
    massAllows (tableMassOf vPredict) .spread Coin.tails = true :=
  (massAllows_eq_true (tableMassOf vPredict) .spread Coin.tails).mpr
    (fun h0 => div_ne_zero one_ne_zero (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero 1))
      (vMass_spread_tails.symm.trans h0))

-- Reference: as on `massAllows_truth_tails`.
/-- The mass flag of `heads` under the opposite hypothesis is `false`. -/
theorem massAllows_opposite_heads :
    massAllows (tableMassOf vPredict) .opposite Coin.heads = false :=
  Bool.eq_false_iff.mpr
    (fun h => (massAllows_eq_true (tableMassOf vPredict) .opposite Coin.heads).mp h
      vMass_opposite_heads)

-- Reference: as on `massAllows_truth_heads`.
/-- The mass flag of `tails` under the opposite hypothesis is `true`. -/
theorem massAllows_opposite_tails :
    massAllows (tableMassOf vPredict) .opposite Coin.tails = true :=
  (massAllows_eq_true (tableMassOf vPredict) .opposite Coin.tails).mpr
    (fun h0 => one_ne_zero (vMass_opposite_tails.symm.trans h0))

-- Reference: `contentSet` (filter over `coinOutcomes`) + the mass flags +
-- core `List.filter_cons_of_pos`/`List.filter_cons_of_neg`/`List.filter_nil`.
/-- The content set of the truth: only heads is allowed. -/
theorem contentSet_truth : contentSet vPredict coinOutcomes .truth = [Coin.heads] :=
  (List.filter_cons_of_pos (p := fun o => massAllows (tableMassOf vPredict) .truth o)
      (a := Coin.heads) (l := [Coin.tails]) massAllows_truth_heads).trans
    (congrArg (fun l => Coin.heads :: l)
      ((List.filter_cons_of_neg (p := fun o => massAllows (tableMassOf vPredict) .truth o)
          (a := Coin.tails) (l := [])
          (fun h => Bool.false_ne_true (massAllows_truth_tails.symm.trans h))).trans
        List.filter_nil))

-- Reference: as on `contentSet_truth` (both cells allowed).
/-- The content set of the spread hypothesis: both outcomes allowed. -/
theorem contentSet_spread :
    contentSet vPredict coinOutcomes .spread = [Coin.heads, Coin.tails] :=
  (List.filter_cons_of_pos (p := fun o => massAllows (tableMassOf vPredict) .spread o)
      (a := Coin.heads) (l := [Coin.tails]) massAllows_spread_heads).trans
    (congrArg (fun l => Coin.heads :: l)
      ((List.filter_cons_of_pos (p := fun o => massAllows (tableMassOf vPredict) .spread o)
          (a := Coin.tails) (l := []) massAllows_spread_tails).trans
        (congrArg (fun l => Coin.tails :: l) List.filter_nil)))

-- Reference: as on `contentSet_truth`.
/-- The content set of the opposite hypothesis: only tails is allowed. -/
theorem contentSet_opposite : contentSet vPredict coinOutcomes .opposite = [Coin.tails] :=
  (List.filter_cons_of_neg (p := fun o => massAllows (tableMassOf vPredict) .opposite o)
      (a := Coin.heads) (l := [Coin.tails])
      (fun h => Bool.false_ne_true (massAllows_opposite_heads.symm.trans h))).trans
    ((List.filter_cons_of_pos (p := fun o => massAllows (tableMassOf vPredict) .opposite o)
        (a := Coin.tails) (l := []) massAllows_opposite_tails).trans
      (congrArg (fun l => Coin.tails :: l) List.filter_nil))

-- Reference: [Miller 1974], [Tichý 1974] — the classic refutation of the
-- naive content-only ordering, made a theorem-on-data (ticket #33, item
-- (c)): the false spread hypothesis's content STRICTLY exceeds the truth's,
-- so the content ordering ranks a false theory above the truth. Proof:
-- `Eq.subst` of `contentSet_truth`/`contentSet_spread`, then core membership
-- steps.
/-- **The content-only ordering fails** (Popper/Miller/Tichý as data): the
truth's content is included in the false spread hypothesis's content, but
not conversely. -/
theorem false_content_exceeds_truth :
    (∀ o ∈ contentSet vPredict coinOutcomes .truth,
      o ∈ contentSet vPredict coinOutcomes .spread) ∧
    ∃ o ∈ contentSet vPredict coinOutcomes .spread,
      o ∉ contentSet vPredict coinOutcomes .truth := by
  refine ⟨?_, ?_⟩
  · exact Eq.subst
      (motive := fun l => ∀ o ∈ l, o ∈ contentSet vPredict coinOutcomes .spread)
      contentSet_truth.symm
      (Eq.subst (motive := fun l => ∀ o ∈ [Coin.heads], o ∈ l) contentSet_spread.symm
        (fun o ho => by
          rcases List.mem_cons.mp ho with he | hn
          · exact Eq.subst (motive := fun x => x ∈ [Coin.heads, Coin.tails]) he.symm
              List.mem_cons_self
          · exact absurd hn List.not_mem_nil))
  · exact Eq.subst
      (motive := fun l => ∃ o ∈ l, o ∉ contentSet vPredict coinOutcomes .truth)
      contentSet_spread.symm
      (Eq.subst (motive := fun l => ∃ o ∈ [Coin.heads, Coin.tails], o ∉ l)
        contentSet_truth.symm
        ⟨Coin.tails, List.mem_cons_of_mem Coin.heads List.mem_cons_self, fun ho => by
          cases ho with
          | tail _ hbad => cases hbad⟩)

-- Reference: core `List.sum_cons` (the map/sum on a two-element list is
-- definitional).
/-- The sum of a two-element rational list, peeled. -/
theorem sum_pair (a b : ℚ) : ([a, b] : List ℚ).sum = a + (b + 0) :=
  (List.sum_cons (a := a) (l := [b])).trans
    (congrArg (fun x => a + x) (List.sum_cons (a := b) (l := [])))

-- Reference: `sub_self` + `abs_zero` on `ℚ`.
/-- `|a - a| = 0` for a rational `a`. -/
theorem abs_sub_self_rat (a : ℚ) : |a - a| = 0 :=
  (congrArg abs (sub_self a)).trans abs_zero

-- Reference: computation of `likenessDist` on a two-point outcome space:
-- `List.map`/`List.sum` on the concrete list (definitional) + `Eq.subst` of
-- the four cell masses + `sum_pair`.
/-- The likeness distance on a two-point outcome space, peeled. -/
theorem likenessDist_pair {hyp outcome : Type} [DecidableEq outcome]
    (predict : hyp → List (ℚ × outcome)) (h hTrue : hyp) (o₁ o₂ : outcome)
    (a₁ a₂ b₁ b₂ : ℚ)
    (h₁ : tableMassOf predict h o₁ = a₁) (h₂ : tableMassOf predict h o₂ = a₂)
    (h₃ : tableMassOf predict hTrue o₁ = b₁) (h₄ : tableMassOf predict hTrue o₂ = b₂) :
    likenessDist predict [o₁, o₂] h hTrue = |a₁ - b₁| + (|a₂ - b₂| + 0) := by
  exact Eq.subst (motive := fun x =>
      (([|x - tableMassOf predict hTrue o₁|,
          |tableMassOf predict h o₂ - tableMassOf predict hTrue o₂|] : List ℚ)).sum
        = |a₁ - b₁| + (|a₂ - b₂| + 0))
    h₁.symm
    (Eq.subst (motive := fun y =>
        (([|a₁ - y|,
            |tableMassOf predict h o₂ - tableMassOf predict hTrue o₂|] : List ℚ)).sum
          = |a₁ - b₁| + (|a₂ - b₂| + 0))
      h₃.symm
      (Eq.subst (motive := fun x =>
          (([|a₁ - b₁|,
              |x - tableMassOf predict hTrue o₂|] : List ℚ)).sum
            = |a₁ - b₁| + (|a₂ - b₂| + 0))
        h₂.symm
        (Eq.subst (motive := fun y =>
            (([|a₁ - b₁|, |a₂ - y|] : List ℚ)).sum = |a₁ - b₁| + (|a₂ - b₂| + 0))
          h₄.symm
          (sum_pair (|a₁ - b₁|) (|a₂ - b₂|)))))

-- Reference: [Niiniluoto 1987] — the distance measure separates the toy:
-- `likenessDist_pair` + `abs_sub_self_rat` + `zero_add`/`add_zero` on `ℚ`.
/-- The truth is at likeness distance `0` from itself. -/
theorem likenessDist_self : likenessDist vPredict coinOutcomes .truth .truth = 0 := by
  have h := likenessDist_pair vPredict .truth .truth Coin.heads Coin.tails 1 0 1 0
    vMass_truth_heads vMass_truth_tails vMass_truth_heads vMass_truth_tails
  exact h.trans
    ((congrArg (fun x => x + (|(0 : ℚ) - 0| + 0)) (abs_sub_self_rat 1)).trans
      ((congrArg (fun y => (0 : ℚ) + (y + 0)) (abs_sub_self_rat 0)).trans
        ((zero_add ((0 : ℚ) + 0)).trans (add_zero (0 : ℚ)))))

-- Reference: [Niiniluoto 1987] — `likenessDist_pair` + `neg_sub`/`sub_half`/
-- `abs_neg`/`abs_of_pos`/`sub_zero`/`add_zero`/`add_halves` on `ℚ`:
-- `|1/2 - 1| + |1/2 - 0| = 1/2 + 1/2 = 1`.
/-- The spread hypothesis is at likeness distance `1` from the truth. -/
theorem likenessDist_spread : likenessDist vPredict coinOutcomes .spread .truth = 1 := by
  have h := likenessDist_pair vPredict .spread .truth Coin.heads Coin.tails (1/2) (1/2) 1 0
    vMass_spread_heads vMass_spread_tails vMass_truth_heads vMass_truth_tails
  have hpos : (0 : ℚ) < 1/2 := div_pos one_pos (Nat.cast_pos.mpr (Nat.succ_pos 1))
  have e1 : |(1/2 : ℚ) - 1| = 1/2 :=
    ((congrArg abs ((neg_sub (1 : ℚ) (1/2)).symm.trans
        (congrArg (fun x => -x) (sub_half (1 : ℚ))))).trans (abs_neg (1/2 : ℚ))).trans
      (abs_of_pos hpos)
  have e2 : |(1/2 : ℚ) - 0| = 1/2 :=
    (congrArg abs (sub_zero (1/2 : ℚ))).trans (abs_of_pos hpos)
  exact h.trans
    ((congrArg (fun x => x + (|(1/2 : ℚ) - 0| + 0)) e1).trans
      ((congrArg (fun y => (1/2 : ℚ) + (y + 0)) e2).trans
        ((congrArg (fun z => (1/2 : ℚ) + z) (add_zero (1/2 : ℚ))).trans
          (add_halves (1 : ℚ)))))

-- Reference: ticket #33, item (d) — the combined-measure axioms on bounded
-- families (the full measure-theoretic program of [Niiniluoto 1987] is
-- deferred).
-- TEMPORARY SORRY: the honest proof has not been instantiated yet.
-- PEELING PLAN: check the axioms (reflexivity `verisimilarLE_refl` proved
-- above; the distance symmetry and triangle inequality on the bounded
-- family by closed computation per family; the content/likeness comparison
-- rows) as named lemmas `likenessDist_symm`, `likenessDist_triangle` on the
-- toy family, then generalize to arbitrary finite outcome spaces by
-- induction on `outcomes`.
/-- The likeness-distance axioms hold on the bounded toy family (the
measure-theoretic program's shadow). -/
theorem likeness_axioms_toy :
    likenessDist vPredict coinOutcomes .truth .truth = 0 ∧
    likenessDist vPredict coinOutcomes .spread .truth =
      likenessDist vPredict coinOutcomes .truth .spread ∧
    likenessDist vPredict coinOutcomes .opposite .truth = 2 := by
  sorry

-- Reference: ticket #33, acceptance: `#eval` prints the content sets and
-- the likeness distances of the toy family.
#eval (contentSet vPredict coinOutcomes .truth, contentSet vPredict coinOutcomes .spread,
  contentSet vPredict coinOutcomes .opposite)
#eval ([.truth, .spread, .opposite] : List VHyp).map fun h =>
  (h, likenessDist vPredict coinOutcomes h .truth)

end BoringLab
