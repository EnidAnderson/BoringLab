/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import BoringLab.Epistemology.Network
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
* `mindChangesAtLevel_mono` — monotonicity of the level ledger — named hole
  with a peeling plan (sublist of the filtered ranges);
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

-- Reference: ticket #43 — monotonicity of the level ledger.
-- TEMPORARY SORRY: the honest proof has not been instantiated yet.
-- PEELING PLAN: `mindChangesAtLevel M s n = mindChangesOn M (s.take n)` and
-- `s.take n` is a prefix of `s` for `n ≤ s.length`; the filtered range of
-- the prefix is a sublist of the filtered range of the whole (via
-- `List.range` monotonicity + `List.filter_sublist`), and `List.Sublist`
-- gives the length bound. Next named lemmas: `range_sublist`,
-- `filter_sublist`, `mindChangesOn_sublist`.
/-- **The level ledger is monotone**: mind changes at level `n ≤ m` are at
most those at level `m` (for `m ≤ s.length`). -/
theorem mindChangesAtLevel_mono {hyp datum : Type} [DecidableEq hyp]
    (M : List datum → hyp) (s : List datum) {n m : ℕ} (h : n ≤ m) (hm : m ≤ s.length) :
    mindChangesAtLevel M s n ≤ mindChangesAtLevel M s m := by
  sorry

/-! ## Identification truncated at level n -/

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
