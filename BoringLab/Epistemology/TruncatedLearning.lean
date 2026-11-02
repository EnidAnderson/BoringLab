/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import BoringLab.Epistemology.Network
import BoringLab.Epistemology.OckhamBound
import BoringLab.Epistemology.TruncatedTheory

/-!
# Truncated learning: prefixes, convergence, and the mind-change ledger at level n

Ticket #43 (EPI.8.3), building on #31's learning theory
(`BoringLab.Epistemology.Learning`) and #42's truncated theory-elements:
the learning-theoretic content of the truncation principle — everything
computed at a fixed level `n`.

* `mindChangesAtLevel` — the mind-change ledger of a learner on a schedule,
  truncated at level `n` (the mind changes on the first `n` observations);
* `mindChangesAtLevel_zero` — proved (`rfl`): no mind changes at level 0;
* `TruncatedIdentification` — identification in the limit restricted to
  prefixes of length at most `n`; `truncatedIdentification_down` — PROVED:
  identification at level `m` restricts to every `n ≤ m` (fewer prefixes,
  same bound);
* `mindChangesAtLevel_mono` — monotonicity of the level ledger — proved
  (the filtered range at level `n` is a sublist of the one at level `m`);
* the toy: the #31 elimination learner on the coin schedule, mind changes
  per level printed by `#eval`.

## References
* [Gold] E. M. Gold, "Language identification in the limit", *Information and
  Control* 10(5):447–474, 1967.
* [Kelly] K. T. Kelly, *The Logic of Reliable Inquiry*, OUP, 1996 (mind
  changes).
* [Bishop–Bridges] E. Bishop, D. Bridges, *Constructive Analysis*, Springer
  1985, ch. 2 (the truncation reading).
* Program register: BoringLab ticket #43 (EPI.8.3); the toy is the #31 coin
  schedule, the program's own.
-/

namespace BoringLab

open scoped List

/-! ## The mind-change ledger at level n -/

-- Reference: ticket #43 — #31's `mindChangesOn` on the schedule truncated
-- at level `n` (the mind-change ledger at level `n`).
/-- The **mind changes at level `n`**: the mind-change count of a learner on
the first `n` observations of the schedule. -/
def mindChangesAtLevel {hyp datum : Type} [DecidableEq hyp] (M : List datum → hyp)
    (s : List datum) (n : ℕ) : ℕ := mindChangesOn M (s.take n)

-- Reference: computation step: at level 0 the schedule `s.take 0` is empty,
-- `List.range 1 = [0]`, and the single comparison `M [] = M []` is `rfl`, so
-- the filtered range is empty (`List.filter_eq_nil_iff`, `ite_eq_left`).
/-- No mind changes at level `0`. -/
theorem mindChangesAtLevel_zero {hyp datum : Type} [DecidableEq hyp]
    (M : List datum → hyp) (s : List datum) : mindChangesAtLevel M s 0 = 0 := by
  have hp : (if M (([] : List datum).take 0) = M (([] : List datum).take (0 + 1)) then false
      else true) = false := ite_eq_left rfl
  have h0 : ∀ n ∈ List.range (([] : List datum).length + 1),
      ¬ (if M (([] : List datum).take n) = M (([] : List datum).take (n + 1)) then false else true)
        = true := by
    intro n hn
    have hn0 : n = 0 := Nat.lt_one_iff.mp (List.mem_range.mp hn)
    subst hn0
    intro ht
    exact Bool.false_ne_true (hp.symm.trans ht)
  have hf : mindChangesOn M [] = 0 :=
    Eq.subst (motive := fun l => l.length = 0) (List.filter_eq_nil_iff.mpr h0).symm rfl
  have e : mindChangesAtLevel M s 0 = mindChangesOn M [] := rfl
  exact e.trans hf

-- Reference: ticket #43 — monotonicity of the level ledger: proved below
-- as `mindChangesAtLevel_mono` (via `changePredAt`, `List.range_sublist`,
-- `List.Sublist.filter`, `List.Sublist.length_le`).
-- Reference: the change predicate of `mindChangesOn` at index `i` on the
-- schedule `s'` (factored out for readability).
/-- The **change predicate** at index `i` on the schedule `s'`. -/
def changePredAt {hyp datum : Type} [DecidableEq hyp] (M : List datum → hyp)
    (s' : List datum) (i : ℕ) : Bool :=
  if M (s'.take i) = M (s'.take (i + 1)) then false else true

-- Reference: ticket #43 — monotonicity of the level ledger, proved: the
-- filtered range at level `n` is a sublist of the one at level `m`
-- (`filter_sublist_of_imp` + `List.range_sublist` + `List.Sublist.filter`),
-- and `List.Sublist.length_le` closes the count. The predicate at level `n`
-- implies the one at level `m`: below `n` the truncated takes agree
-- (`List.take_take` + `Nat.min_eq_left`), and at `a ≥ n` the `n`-level takes
-- are both `s.take n`, so the `n`-level predicate is `false`.
/-- **The level ledger is monotone**: mind changes at level `n ≤ m` are at
most those at level `m` (for `m ≤ s.length`) (proved). -/
theorem mindChangesAtLevel_mono {hyp datum : Type} [DecidableEq hyp]
    (M : List datum → hyp) (s : List datum) {n m : ℕ} (h : n ≤ m) (hm : m ≤ s.length) :
    mindChangesAtLevel M s n ≤ mindChangesAtLevel M s m := by
  have hns : n ≤ s.length := Nat.le_trans h hm
  have hlen_n : (s.take n).length = n :=
    Eq.trans (List.length_take (i := n) (l := s)) (Nat.min_eq_left hns)
  have hlen_m : (s.take m).length = m :=
    Eq.trans (List.length_take (i := m) (l := s)) (Nat.min_eq_left hm)
  have hP : ∀ a : ℕ, changePredAt M (s.take n) a = true →
      changePredAt M (s.take m) a = true := by
    intro a hPa
    unfold changePredAt at hPa
    unfold changePredAt
    rcases Nat.lt_or_ge a n with hlt | hge
    · have e1 : (s.take n).take a = (s.take m).take a :=
        ((List.take_take (i := a) (j := n) (l := s)).trans
          (congrArg (s.take) (Nat.min_eq_left (Nat.le_of_lt hlt)))).trans
        ((List.take_take (i := a) (j := m) (l := s)).trans
          (congrArg (s.take) (Nat.min_eq_left (Nat.le_trans (Nat.le_of_lt hlt) h)))).symm
      have e2 : (s.take n).take (a + 1) = (s.take m).take (a + 1) :=
        ((List.take_take (i := a + 1) (j := n) (l := s)).trans
          (congrArg (s.take) (Nat.min_eq_left (Nat.succ_le_of_lt hlt)))).trans
        ((List.take_take (i := a + 1) (j := m) (l := s)).trans
          (congrArg (s.take) (Nat.min_eq_left
            (Nat.le_trans (Nat.succ_le_of_lt hlt) h)))).symm
      have hd : Decidable (M ((s.take n).take a) = M ((s.take n).take (a + 1))) :=
        inferInstance
      cases hd with
      | isTrue hc =>
          exact (Bool.false_ne_true (hPa.symm.trans (ite_eq_left hc)).symm).elim
      | isFalse hc =>
          have hc' : ¬ (M ((s.take m).take a) = M ((s.take m).take (a + 1))) :=
            fun hcd => hc ((congrArg M e1).trans (hcd.trans (congrArg M e2).symm))
          exact ite_eq_right hc'
    · have e1 : (s.take n).take a = s.take n :=
        (List.take_take (i := a) (j := n) (l := s)).trans
          (congrArg (s.take) (Nat.min_eq_right hge))
      have e2 : (s.take n).take (a + 1) = s.take n :=
        (List.take_take (i := a + 1) (j := n) (l := s)).trans
          (congrArg (s.take) (Nat.min_eq_right (Nat.le_trans hge (Nat.le_succ a))))
      have hc : M ((s.take n).take a) = M ((s.take n).take (a + 1)) :=
        (congrArg M e1).trans (congrArg M e2).symm
      exact (Bool.false_ne_true (hPa.symm.trans (ite_eq_left hc)).symm).elim
  have hsub1 := filter_sublist_of_imp hP (List.range (n + 1))
  have hsub2 : List.Sublist (List.range (n + 1)) (List.range (m + 1)) :=
    List.range_sublist.mpr (Nat.succ_le_succ h)
  have hsub3 : ((List.range (n + 1)).filter (changePredAt M (s.take m))) <+
      ((List.range (m + 1)).filter (changePredAt M (s.take m))) :=
    List.Sublist.filter _ hsub2
  have hsub : ((List.range (n + 1)).filter (changePredAt M (s.take n))) <+
      ((List.range (m + 1)).filter (changePredAt M (s.take m))) := hsub1.trans hsub3
  have e : ((List.range (n + 1)).filter (changePredAt M (s.take n))).length ≤
      ((List.range (m + 1)).filter (changePredAt M (s.take m))).length :=
    List.Sublist.length_le hsub
  show ((List.range ((s.take n).length + 1)).filter (changePredAt M (s.take n))).length ≤
    ((List.range ((s.take m).length + 1)).filter (changePredAt M (s.take m))).length
  exact Eq.subst (motive := fun k =>
      ((List.range (k + 1)).filter (changePredAt M (s.take n))).length ≤
      ((List.range ((s.take m).length + 1)).filter (changePredAt M (s.take m))).length)
    hlen_n.symm
    (Eq.subst (motive := fun k =>
      ((List.range (n + 1)).filter (changePredAt M (s.take n))).length ≤
      ((List.range (k + 1)).filter (changePredAt M (s.take m))).length)
      hlen_m.symm e)

-- Reference: ticket #43; [Gold] 1967 — #31's `IdentifiesInLimit` restricted
-- to prefixes of length at most `n` (convergence at level `n`).
/-- **Truncated identification**: the learner identifies the family on all
compatible prefixes of length at most `n`, past a bound `N`. -/
def TruncatedIdentification {hyp datum : Type} (M : List datum → hyp)
    (mass : hyp → datum → ℚ) (hs : List hyp) (n : ℕ) : Prop :=
  ∀ h ∈ hs, ∃ N : ℕ, ∀ p : List datum, Compatible mass h p → p.length ≤ n →
    N ≤ p.length → M p = h

-- Reference: ticket #43 — proved: identification at level `m` restricts to
-- every `n ≤ m` (the prefix set shrinks; the same bound works, `Nat.le_trans`).
/-- **Truncated identification is downward closed in the level**: level `m`
identification implies level `n` for `n ≤ m`. -/
theorem truncatedIdentification_down {hyp datum : Type} (M : List datum → hyp)
    (mass : hyp → datum → ℚ) (hs : List hyp) {n m : ℕ} (h : n ≤ m)
    (hid : TruncatedIdentification M mass hs m) : TruncatedIdentification M mass hs n := by
  intro h' hh
  obtain ⟨N, hN⟩ := hid h' hh
  exact ⟨N, fun p hp hlen hN' => hN p hp (Nat.le_trans hlen h) hN'⟩

/-! ## Toy: the coin elimination learner, per level -/

-- Reference: ticket #43, toy: #31's elimination learner on the coin
-- schedule; the level ledger printed.
/-- The mind-change ledger of the coin elimination learner at each level. -/
def coinLevelLedger : List (ℕ × ℕ) :=
  (List.range 4).map fun n =>
    (n, mindChangesAtLevel (elimLearner coinHypotheses coinMass CoinHyp.fair) coinStream n)

-- Reference: ticket #43, acceptance: `#eval` prints the level ledger.
#eval coinLevelLedger

end BoringLab
