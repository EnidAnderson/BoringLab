/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import BoringLab.Epistemology.TruncatedLearning

/-!
# The level ledger is monotone: peeling `mindChangesAtLevel_mono`

Ticket #43 (EPI.8.3), completing the named hole
`mindChangesAtLevel_mono` in `BoringLab.Epistemology.TruncatedLearning`
(kept there as the declared hole; the proof lands here as
`mindChangesAtLevel_mono_full`):

* `range_sublist_of_le` — `List.range` is monotone under `≤`, as a
  `Sublist` (induction via `List.range_succ`);
* `take_length_of_le`, `take_take_le` — prefix arithmetic
  (`List.length_take`, `List.take_take`, `Nat.min_eq_left`/`_right`);
* `mindChangesAtLevel_mono_full` — **proved**: the mind-change count on
  `s.take n` is at most that on `s.take m` for `n ≤ m ≤ s.length`. The last
  comparison at level `n` is equal-output (both takes are `s.take n`), so
  the level-`n` filter is the filter over `range n`; below level `n` the
  two level predicates agree pointwise; and `range n <+ range (m+1)`, so
  `List.Sublist.filter` + `List.Sublist.length_le` close the bound.

## References
* [Kelly] K. T. Kelly, *The Logic of Reliable Inquiry*, OUP, 1996 (mind
  changes along prefixes — the truncation reading).
* Program register: BoringLab ticket #43 (EPI.8.3).
-/

namespace BoringLab

open scoped List

/-! ## Prefix and range arithmetic -/

-- Reference: `List.range` monotonicity as a `Sublist`; induction on `m`
-- via `List.range_succ` and `List.Sublist.append`.
/-- **`List.range` is monotone**: `n ≤ m` gives `range n <+ range m`. -/
theorem range_sublist_of_le {n m : ℕ} (h : n ≤ m) : List.range n <+ List.range m := by
  induction m with
  | zero =>
      have hn : n = 0 := Nat.eq_zero_of_le_zero h
      exact Eq.subst (motive := fun k => List.range k <+ List.range 0) hn.symm
        (List.Sublist.refl (List.range 0))
  | succ m ih =>
      rcases Nat.le_iff_lt_or_eq.mp h with h' | h'
      · have happ : List.range m ++ [] <+ List.range m ++ [m] :=
          List.Sublist.append (List.Sublist.refl (List.range m)) (List.nil_sublist [m])
        have h1 : List.range m ++ [] = List.range m := List.append_nil _
        have h2 : List.range m ++ [m] = List.range (m + 1) := (List.range_succ (n := m)).symm
        have happ' : List.range m <+ List.range m ++ [m] :=
          Eq.subst (motive := fun l => l <+ List.range m ++ [m]) h1 happ
        have hstep : List.range m <+ List.range (m + 1) :=
          Eq.subst (motive := fun l => List.range m <+ l) h2 happ'
        exact (ih (Nat.le_of_lt_succ h')).trans hstep
      · exact Eq.subst (motive := fun k => List.range k <+ List.range (m + 1)) h'.symm
          (List.Sublist.refl (List.range (m + 1)))

-- Reference: `List.length_take` + `Nat.min_eq_left`.
/-- The length of a prefix of length `n ≤ s.length` is `n`. -/
theorem take_length_of_le {α : Type} (s : List α) {n : ℕ} (h : n ≤ s.length) :
    (s.take n).length = n :=
  (List.length_take (i := n) (l := s)).trans (Nat.min_eq_left h)

-- Reference: `List.take_take` + `Nat.min_eq_right`.
/-- A prefix of a prefix: `(s.take n).take k = s.take k` for `k ≤ n`. -/
theorem take_take_le {α : Type} (s : List α) {n k : ℕ} (h : k ≤ n) :
    (s.take n).take k = s.take k :=
  (List.take_take (i := k) (j := n) (l := s)).trans
        (congrArg (fun i => s.take i) (Nat.min_eq_left h))

/-! ## The level ledger is monotone -/

-- Reference: ticket #43 — the peeling of `mindChangesAtLevel_mono`, proved.
/-- **The level ledger is monotone** (full proof): mind changes at level
`n ≤ m ≤ s.length` are at most those at level `m`. -/
theorem mindChangesAtLevel_mono_full {hyp datum : Type} [DecidableEq hyp]
    (M : List datum → hyp) (s : List datum) {n m : ℕ} (h : n ≤ m) (hm : m ≤ s.length) :
    mindChangesAtLevel M s n ≤ mindChangesAtLevel M s m := by
  have hns : n ≤ s.length := Nat.le_trans h hm
  have hlen_n : (s.take n).length = n := take_length_of_le s hns
  have hlen_m : (s.take m).length = m := take_length_of_le s hm
  -- the last comparison at level n is equal-output: both takes are s.take n
  have hlast : (if M ((s.take n).take n) = M ((s.take n).take (n + 1)) then false else true)
      = false := by
    have h1 : (s.take n).take n = s.take n := take_take_le s (Nat.le_refl n)
    have h2 : (s.take n).take (n + 1) = s.take n :=
      (List.take_take (i := n + 1) (j := n) (l := s)).trans
        (congrArg (fun i => s.take i) (Nat.min_eq_right (Nat.le_succ n)))
    exact Eq.subst
      (motive := fun a =>
        (if M a = M ((s.take n).take (n + 1)) then false else true) = false)
      h1.symm (Eq.subst
        (motive := fun b => (if M (s.take n) = M b then false else true) = false) h2.symm
        (ite_eq_left rfl))
  -- pointwise agreement of the two level predicates below level n
  have hpoint : ∀ k ∈ List.range n,
      (if M ((s.take n).take k) = M ((s.take n).take (k + 1)) then false else true) =
      (if M ((s.take m).take k) = M ((s.take m).take (k + 1)) then false else true) := by
    intro k hk
    have hk' : k < n := List.mem_range.mp hk
    have hkn : k ≤ n := Nat.le_of_lt hk'
    have hkn1 : k + 1 ≤ n := Nat.succ_le_of_lt hk'
    have hkm : k ≤ m := Nat.le_trans hkn h
    have hkm1 : k + 1 ≤ m := Nat.le_trans hkn1 h
    have e1 : (s.take n).take k = (s.take m).take k :=
      (take_take_le s hkn).trans (take_take_le s hkm).symm
    have e2 : (s.take n).take (k + 1) = (s.take m).take (k + 1) :=
      (take_take_le s hkn1).trans (take_take_le s hkm1).symm
    exact Eq.subst
      (motive := fun a =>
        (if M a = M ((s.take n).take (k + 1)) then false else true) =
          (if M ((s.take m).take k) = M ((s.take m).take (k + 1)) then false else true))
      e1.symm
      (Eq.subst
        (motive := fun b =>
          (if M ((s.take m).take k) = M b then false else true) =
            (if M ((s.take m).take k) = M ((s.take m).take (k + 1)) then false else true))
        e2.symm rfl)
  -- split off the last (dropped) comparison at level n
  have hsplit : (List.range (n + 1)).filter
      (fun k =>
          if M ((s.take n).take k) = M ((s.take n).take (k + 1)) then false else true) =
      (List.range n).filter
        (fun k =>
          if M ((s.take n).take k) = M ((s.take n).take (k + 1)) then false else true) := by
    have hr : List.range (n + 1) = List.range n ++ [n] := List.range_succ (n := n)
    have hneg : ¬ (if M ((s.take n).take n) = M ((s.take n).take (n + 1)) then false else true)
        = true := fun hc => Bool.false_ne_true (hlast.symm.trans hc)
    have hfl : (List.range n ++ [n]).filter
        (fun k =>
          if M ((s.take n).take k) = M ((s.take n).take (k + 1)) then false else true) =
        (List.range n).filter
          (fun k => if M ((s.take n).take k) = M ((s.take n).take (k + 1)) then false
            else true) :=
      (List.filter_append (p := fun k => if M ((s.take n).take k) =
          M ((s.take n).take (k + 1)) then false else true) (List.range n) [n]).trans
        ((congrArg (fun l => (List.range n).filter
            (fun k => if M ((s.take n).take k) = M ((s.take n).take (k + 1)) then false
              else true) ++ l)
          ((List.filter_cons_of_neg (p := fun k => if M ((s.take n).take k) =
              M ((s.take n).take (k + 1)) then false else true) (a := n) (l := []) hneg).trans
            (List.filter_nil (p := fun k => if M ((s.take n).take k) =
              M ((s.take n).take (k + 1)) then false else true)))).trans
          (List.append_nil _))
    exact Eq.subst (motive := fun l => l.filter
        (fun k =>
          if M ((s.take n).take k) = M ((s.take n).take (k + 1)) then false else true) =
        (List.range n).filter
          (fun k => if M ((s.take n).take k) = M ((s.take n).take (k + 1)) then false
            else true)) hr.symm hfl
  -- assemble: transport the take-lengths, split, congr, sublist, length bound
  have e1 : (s.take n).length + 1 = n + 1 := congrArg (· + 1) hlen_n
  have e2 : (s.take m).length + 1 = m + 1 := congrArg (· + 1) hlen_m
  have hsub : List.range n <+ List.range (m + 1) :=
    range_sublist_of_le (Nat.le_trans h (Nat.le_succ m))
  have hcong : (List.range n).filter
      (fun k =>
          if M ((s.take n).take k) = M ((s.take n).take (k + 1)) then false else true) =
      (List.range n).filter
        (fun k =>
          if M ((s.take m).take k) = M ((s.take m).take (k + 1)) then false else true) :=
    List.filter_congr hpoint
  have hle : ((List.range n).filter
      (fun k =>
          if M ((s.take m).take k) = M ((s.take m).take (k + 1)) then false else true)).length ≤
      ((List.range (m + 1)).filter
        (fun k =>
          if M ((s.take m).take k) = M ((s.take m).take (k + 1)) then false else true)).length :=
    List.Sublist.length_le (List.Sublist.filter
      (p := fun k => if M ((s.take m).take k) = M ((s.take m).take (k + 1)) then false else true)
      hsub)
  have hfinal : ((List.range (n + 1)).filter
      (fun k =>
          if M ((s.take n).take k) = M ((s.take n).take (k + 1)) then false else true)).length ≤
      ((List.range (m + 1)).filter
        (fun k =>
          if M ((s.take m).take k) = M ((s.take m).take (k + 1)) then false else true)).length :=
    (le_of_eq (congrArg List.length hsplit)).trans
      ((le_of_eq (congrArg List.length hcong)).trans hle)
  exact Eq.subst (motive := fun a => ((List.range a).filter
      (fun k =>
          if M ((s.take n).take k) = M ((s.take n).take (k + 1)) then false else true)).length ≤
      ((List.range ((s.take m).length + 1)).filter
        (fun k =>
          if M ((s.take m).take k) = M ((s.take m).take (k + 1)) then false else true)).length)
    e1.symm
    (Eq.subst (motive := fun b => ((List.range (n + 1)).filter
        (fun k =>
          if M ((s.take n).take k) = M ((s.take n).take (k + 1)) then false else true)).length ≤
      ((List.range b).filter
        (fun k =>
          if M ((s.take m).take k) = M ((s.take m).take (k + 1)) then false else true)).length)
      e2.symm hfinal)

end BoringLab
