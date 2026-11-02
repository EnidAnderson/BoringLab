/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import BoringLab.Epistemology.Ockham
import Mathlib.Data.List.Basic
import Mathlib.Data.Finset.Card

/-!
# Mind-change bounds for the elimination/Ockham learners

Ticket **#285** (repair of #32's item (c), EPI.3.2): the honest mind-change
content of `BoringLab.Epistemology.Ockham`. Two findings:

* **(a) the true bound** (proved for `elimLearner`): compatibility is
  prefix-monotone, so a mind change at prefix length `n` permanently eliminates
  the current output (`elimLearner_change_elim`); hence distinct mind changes
  output distinct members of `hs`, and
  `mindChangesOn (elimLearner hs mass default) s ≤ hs.length`
  (`elimLearner_mindChanges_le`). The Ockham-learner version
  (`ockhamLearner_mindChanges_le`) is stated with the same peeling plan plus the
  min-complexity stability argument.
* **(b) a counterexample** (proved): the pointwise-minimality statement
  `ockham_min_changes_toy` (Ockham.lean, unproved) is **false as stated** —
  `ockham_pointwise_minimality_fails` exhibits a constant learner (0 mind
  changes, `mindChangesOn_const`) beating the Ockham learner (1 mind change,
  `ockham_two_mind_changes`) on the toy schedule `[heads, tails]`. The repair
  (#285) is Kelly's actual theorem: the bound holds among *identifying*
  learners, not among all learners.

## References
* [Gold] E. M. Gold, "Language identification in the limit", *Information and
  Control* 10(5):447–474, 1967 (elimination; mind changes bounded by family size).
* [Kelly] K. T. Kelly, *The Logic of Reliable Inquiry*, OUP, 1996 (mind-change
  efficiency is relative to identifying learners — the qualifier missing from
  `ockham_min_changes_toy`).
* Program register: BoringLab tickets #31 (EPI.3.1), #32 (EPI.3.2), #285 (repair).
-/

namespace BoringLab

open scoped List

/-! ## Prefix monotonicity of compatibility -/

-- Reference: core `List.take_take` + `Nat.min_eq_left` + `List.take_prefix`.
/-- A shorter `take` is a prefix of a longer `take`. -/
theorem take_prefix_take {α : Type} (s : List α) {n m : ℕ} (h : n ≤ m) :
    s.take n <+: s.take m :=
  Eq.subst (motive := fun l => l <+: s.take m)
    ((List.take_take (i := n) (j := m) (l := s)).trans (congrArg (s.take) (Nat.min_eq_left h)))
    (List.take_prefix n (s.take m))

-- Reference: core `List.all_eq_true`, `List.IsPrefix.mem`; [Gold] 1967
-- (compatibility with a longer prefix implies compatibility with shorter ones).
/-- **Compatibility is prefix-monotone**: if `h` is compatible with `q` and `p`
is a prefix of `q`, then `h` is compatible with `p`. -/
theorem compatibleBool_prefix {hyp datum : Type} (mass : hyp → datum → ℚ) (h : hyp)
    {p q : List datum} (hq : compatibleBool mass h q = true) (hpre : p <+: q) :
    compatibleBool mass h p = true :=
  (List.all_eq_true).mpr fun d hd => (List.all_eq_true.mp hq) d (hpre.mem hd)

-- Reference: core `List.filter_cons`; induction on the list.
/-- Filtering with a stronger predicate gives a sublist of filtering with the
weaker one. -/
theorem filter_sublist_of_imp {α : Type} {p q : α → Bool}
    (h : ∀ a, p a = true → q a = true) :
    ∀ l : List α, List.Sublist (l.filter p) (l.filter q) := by
  intro l
  induction l with
  | nil =>
      exact Eq.subst (motive := fun a => a <+ List.filter q [])
        (List.filter_nil (p := p)).symm
        (Eq.subst (motive := fun b => ([] : List α) <+ b) (List.filter_nil (p := q)).symm
          List.Sublist.slnil)
  | cons a t ih =>
      cases hpa : p a with
      | true =>
          have e1 : (a :: t).filter p = a :: t.filter p :=
            (List.filter_cons (p := p) (x := a) (xs := t)).trans
              (Eq.subst (motive := fun b => (if b then a :: t.filter p else t.filter p)
                  = a :: t.filter p) hpa.symm rfl)
          have e2 : (a :: t).filter q = a :: t.filter q :=
            (List.filter_cons (p := q) (x := a) (xs := t)).trans
              (Eq.subst (motive := fun b => (if b then a :: t.filter q else t.filter q)
                  = a :: t.filter q) (h a hpa).symm rfl)
          exact Eq.subst (motive := fun l => List.Sublist l ((a :: t).filter q)) e1.symm
            (Eq.subst (motive := fun l => List.Sublist (a :: t.filter p) l) e2.symm
              (List.Sublist.cons_cons a ih))
      | false =>
          have e1 : (a :: t).filter p = t.filter p :=
            (List.filter_cons (p := p) (x := a) (xs := t)).trans
              (Eq.subst (motive := fun b => (if b then a :: t.filter p else t.filter p)
                  = t.filter p) hpa.symm rfl)
          cases hqa : q a with
          | true =>
              have e2 : (a :: t).filter q = a :: t.filter q :=
                (List.filter_cons (p := q) (x := a) (xs := t)).trans
                  (Eq.subst (motive := fun b => (if b then a :: t.filter q else t.filter q)
                      = a :: t.filter q) hqa.symm rfl)
              exact Eq.subst (motive := fun l => List.Sublist l ((a :: t).filter q)) e1.symm
                (Eq.subst (motive := fun l => List.Sublist (t.filter p) l) e2.symm
                  (List.Sublist.cons a ih))
          | false =>
              have e2 : (a :: t).filter q = t.filter q :=
                (List.filter_cons (p := q) (x := a) (xs := t)).trans
                  (Eq.subst (motive := fun b => (if b then a :: t.filter q else t.filter q)
                      = t.filter q) hqa.symm rfl)
              exact Eq.subst (motive := fun l => List.Sublist l ((a :: t).filter q)) e1.symm
                (Eq.subst (motive := fun l => List.Sublist (t.filter p) l) e2.symm ih)

/-! ## Mind changes of a constant learner -/

-- Reference: core `List.filter_eq_nil_iff`, `if_pos`, `Bool.false_ne_true`;
-- [Kelly] 1996. The filter condition is `h = h`, so the `ite` is `false` by
-- `if_pos (rfl : h = h)`.
/-- **A constant learner makes no mind changes**. -/
theorem mindChangesOn_const {hyp datum : Type} [DecidableEq hyp] (h : hyp) (s : List datum) :
    mindChangesOn (fun _ => h) s = 0 := by
  have hnil : (List.range (s.length + 1)).filter (fun n =>
      if (fun _ => h) (s.take n) = (fun _ => h) (s.take (n + 1)) then false else true) = [] :=
    List.filter_eq_nil_iff.mpr fun n _ htrue =>
      Bool.false_ne_true ((ite_eq_left (rfl : h = h)).symm.trans htrue)
  exact Eq.subst (motive := fun l => l.length = 0) hnil.symm rfl

/-! ## Stability, elimination, and the bound for the elimination learner -/

-- Reference: core `List.filter_cons` + `elimLearner_nil`/`elimLearner_cons`
-- (Learning.lean); computation step.
/-- If the head hypothesis is incompatible, the elimination learner on `a :: t`
equals the one on `t`. -/
theorem elimLearner_cons_false {hyp datum : Type} (mass : hyp → datum → ℚ)
    (default : hyp) (p : List datum) (a : hyp) (t : List hyp)
    (ha : compatibleBool mass a p = false) :
    elimLearner (a :: t) mass default p = elimLearner t mass default p := by
  have e1 : (a :: t).filter (fun hh => compatibleBool mass hh p)
      = t.filter (fun hh => compatibleBool mass hh p) :=
    (List.filter_cons (p := fun hh => compatibleBool mass hh p) (x := a) (xs := t)).trans
      (Eq.subst (motive := fun b => (if b then a :: t.filter (fun hh => compatibleBool mass hh p)
          else t.filter (fun hh => compatibleBool mass hh p))
          = t.filter (fun hh => compatibleBool mass hh p)) ha.symm rfl)
  cases hft : t.filter (fun hh => compatibleBool mass hh p) with
  | nil =>
      exact (elimLearner_nil (a :: t) mass default p (e1.trans hft)).trans
        (elimLearner_nil t mass default p hft).symm
  | cons c r =>
      exact (elimLearner_cons (a :: t) mass default p c r (e1.trans hft)).trans
        (elimLearner_cons t mass default p c r hft).symm

-- Reference: core `List.filter_cons` + `elimLearner_cons`; computation step.
/-- If the head hypothesis is compatible, the elimination learner outputs it. -/
theorem elimLearner_cons_true {hyp datum : Type} (mass : hyp → datum → ℚ)
    (default : hyp) (p : List datum) (a : hyp) (t : List hyp)
    (ha : compatibleBool mass a p = true) :
    elimLearner (a :: t) mass default p = a :=
  elimLearner_cons (a :: t) mass default p a _
    ((List.filter_cons (p := fun hh => compatibleBool mass hh p) (x := a) (xs := t)).trans
      (Eq.subst (motive := fun b => (if b then a :: t.filter (fun hh => compatibleBool mass hh p)
          else t.filter (fun hh => compatibleBool mass hh p))
          = a :: t.filter (fun hh => compatibleBool mass hh p)) ha.symm rfl))

-- Reference: `elimLearner_cons_false`/`elimLearner_cons_true` + `compatibleBool_prefix`;
-- [Gold] 1967 — elimination is stable under compatible extensions of the data.
/-- **Stability of the elimination learner**: if `h` is output on the prefix `p`
and stays compatible with the longer prefix `q`, then `h` is still output on
`q`. -/
theorem elimLearner_stable {hyp datum : Type}
    (hs : List hyp) (mass : hyp → datum → ℚ) (default : hyp)
    {p q : List datum} (hpre : p <+: q) {h : hyp}
    (hp : elimLearner hs mass default p = h) (hq : compatibleBool mass h q = true) :
    elimLearner hs mass default q = h := by
  induction hs generalizing p q h with
  | nil =>
      have e1 : elimLearner [] mass default p = default := elimLearner_nil [] mass default p rfl
      have e2 : elimLearner [] mass default q = default := elimLearner_nil [] mass default q rfl
      exact e2.trans (hp.symm.trans e1).symm
  | cons a t ih =>
      cases hpa : compatibleBool mass a p with
      | false =>
          have hqa : compatibleBool mass a q = false := by
            cases hqa : compatibleBool mass a q with
            | true =>
                exact absurd (compatibleBool_prefix mass a hqa hpre)
                  fun hp' => Bool.false_ne_true (hpa.symm.trans hp')
            | false => rfl
          have ep : elimLearner (a :: t) mass default p = elimLearner t mass default p :=
            elimLearner_cons_false mass default p a t hpa
          have eq : elimLearner (a :: t) mass default q = elimLearner t mass default q :=
            elimLearner_cons_false mass default q a t hqa
          exact eq.trans (ih hpre (ep.symm.trans hp) hq)
      | true =>
          have ha : elimLearner (a :: t) mass default p = a :=
            elimLearner_cons_true mass default p a t hpa
          have hha : h = a := hp.symm.trans ha
          have hqa : compatibleBool mass a q = true :=
            Eq.subst (motive := fun x => compatibleBool mass x q = true) hha hq
          exact Eq.subst (motive := fun x => elimLearner (a :: t) mass default q = x) hha.symm
            (elimLearner_cons_true mass default q a t hqa)

-- Reference: `elimLearner_cons_false`/`elimLearner_cons_true` + `compatibleBool_prefix`
-- + `take_prefix_take`; [Gold] 1967 — a mind change eliminates the old output.
/-- **A mind change eliminates the old output**: if the elimination learner
changes its mind at prefix length `n`, its output there is incompatible with the
prefix of length `n + 1`. -/
theorem elimLearner_change_elim {hyp datum : Type}
    (hs : List hyp) (mass : hyp → datum → ℚ) (default : hyp) (s : List datum) {n : ℕ}
    (hch : elimLearner hs mass default (s.take n)
      ≠ elimLearner hs mass default (s.take (n + 1))) :
    compatibleBool mass (elimLearner hs mass default (s.take n)) (s.take (n + 1)) = false := by
  induction hs generalizing n with
  | nil =>
      have e1 : elimLearner [] mass default (s.take n) = default :=
        elimLearner_nil [] mass default _ rfl
      have e2 : elimLearner [] mass default (s.take (n + 1)) = default :=
        elimLearner_nil [] mass default _ rfl
      exact absurd (e1.trans e2.symm) hch
  | cons a t ih =>
      cases hpa : compatibleBool mass a (s.take n) with
      | false =>
          have hqa : compatibleBool mass a (s.take (n + 1)) = false := by
            cases hqa : compatibleBool mass a (s.take (n + 1)) with
            | true =>
                exact absurd (compatibleBool_prefix mass a hqa (take_prefix_take s (Nat.le_succ n)))
                  fun hp' => Bool.false_ne_true (hpa.symm.trans hp')
            | false => rfl
          have ep : elimLearner (a :: t) mass default (s.take n)
              = elimLearner t mass default (s.take n) :=
            elimLearner_cons_false mass default _ a t hpa
          have eq : elimLearner (a :: t) mass default (s.take (n + 1))
              = elimLearner t mass default (s.take (n + 1)) :=
            elimLearner_cons_false mass default _ a t hqa
          have hch' : elimLearner t mass default (s.take n)
              ≠ elimLearner t mass default (s.take (n + 1)) :=
            fun heq => hch (ep.trans (heq.trans eq.symm))
          exact Eq.subst (motive := fun x => compatibleBool mass x (s.take (n + 1)) = false)
            ep.symm (ih hch')
      | true =>
          have e : elimLearner (a :: t) mass default (s.take n) = a :=
            elimLearner_cons_true mass default _ a t hpa
          cases hqa : compatibleBool mass a (s.take (n + 1)) with
          | true =>
              have e2 : elimLearner (a :: t) mass default (s.take (n + 1)) = a :=
                elimLearner_cons_true mass default _ a t hqa
              exact absurd (e.trans e2.symm) hch
          | false =>
              exact Eq.subst (motive := fun x => compatibleBool mass x (s.take (n + 1)) = false)
                e.symm hqa

-- Reference: `List.mem_filter`, `elimLearner_cons`/`elimLearner_nil`,
-- `filter_sublist_of_imp`, `take_prefix_take`. At a mind change the filter at `n`
-- is nonempty (else the filter at `n + 1`, a sublist of `[]`, is `[]` and there is
-- no change), so the output is the filter head, a member of `hs`, and compatible.
/-- At a mind-change index the elimination learner outputs a member of `hs`. -/
theorem elimLearner_mem_of_change {hyp datum : Type}
    (hs : List hyp) (mass : hyp → datum → ℚ) (default : hyp) (s : List datum) {n : ℕ}
    (hch : elimLearner hs mass default (s.take n)
      ≠ elimLearner hs mass default (s.take (n + 1))) :
    elimLearner hs mass default (s.take n) ∈ hs := by
  cases hfn : hs.filter (fun hh => compatibleBool mass hh (s.take n)) with
  | nil =>
      have e : elimLearner hs mass default (s.take n) = default :=
        elimLearner_nil hs mass default _ hfn
      have hsub := filter_sublist_of_imp
        (fun hh (h : compatibleBool mass hh (s.take (n + 1)) = true) =>
          compatibleBool_prefix mass hh h (take_prefix_take s (Nat.le_succ n))) hs
      have hlen : (hs.filter fun hh => compatibleBool mass hh (s.take (n + 1))).length = 0 :=
        Nat.le_zero.mp
          ((List.Sublist.length_le hsub).trans (Nat.le_of_eq (congrArg List.length hfn)))
      have hnil : hs.filter (fun hh => compatibleBool mass hh (s.take (n + 1))) = [] :=
        List.length_eq_zero_iff.mp hlen
      have e2 : elimLearner hs mass default (s.take (n + 1)) = default :=
        elimLearner_nil hs mass default _ hnil
      exact absurd (e.trans e2.symm) hch
  | cons c r =>
      have e : elimLearner hs mass default (s.take n) = c :=
        elimLearner_cons hs mass default _ c r hfn
      exact Eq.subst (motive := fun x => x ∈ hs) e.symm
        (List.Sublist.mem
          (Eq.subst (motive := fun l => c ∈ l) hfn.symm (List.mem_cons_self (a := c) (l := r)))
          (List.filter_sublist (l := hs)))

-- Reference: as `elimLearner_mem_of_change`; the output at a mind change is the
-- head of the nonempty filter at `n`, hence compatible with `s.take n`.
/-- At a mind-change index the elimination learner's output is compatible with
the prefix of length `n`. -/
theorem elimLearner_compatible_of_change {hyp datum : Type}
    (hs : List hyp) (mass : hyp → datum → ℚ) (default : hyp) (s : List datum) {n : ℕ}
    (hch : elimLearner hs mass default (s.take n)
      ≠ elimLearner hs mass default (s.take (n + 1))) :
    compatibleBool mass (elimLearner hs mass default (s.take n)) (s.take n) = true := by
  cases hfn : hs.filter (fun hh => compatibleBool mass hh (s.take n)) with
  | nil =>
      have e : elimLearner hs mass default (s.take n) = default :=
        elimLearner_nil hs mass default _ hfn
      have hsub := filter_sublist_of_imp
        (fun hh (h : compatibleBool mass hh (s.take (n + 1)) = true) =>
          compatibleBool_prefix mass hh h (take_prefix_take s (Nat.le_succ n))) hs
      have hlen : (hs.filter fun hh => compatibleBool mass hh (s.take (n + 1))).length = 0 :=
        Nat.le_zero.mp
          ((List.Sublist.length_le hsub).trans (Nat.le_of_eq (congrArg List.length hfn)))
      have hnil : hs.filter (fun hh => compatibleBool mass hh (s.take (n + 1))) = [] :=
        List.length_eq_zero_iff.mp hlen
      have e2 : elimLearner hs mass default (s.take (n + 1)) = default :=
        elimLearner_nil hs mass default _ hnil
      exact absurd (e.trans e2.symm) hch
  | cons c r =>
      have e : elimLearner hs mass default (s.take n) = c :=
        elimLearner_cons hs mass default _ c r hfn
      have hmem : c ∈ hs.filter (fun hh => compatibleBool mass hh (s.take n)) :=
        Eq.subst (motive := fun l => c ∈ l) hfn.symm (List.mem_cons_self (a := c) (l := r))
      rcases List.mem_filter.mp hmem with ⟨_, hc⟩
      exact Eq.subst (motive := fun x => compatibleBool mass x (s.take n) = true) e.symm hc

-- Reference: core `List.mem_filter`, `ite_eq_left`, `Bool.false_ne_true`.
/-- A filtered change index is a genuine mind change. -/
theorem change_of_mem_filter {hyp datum : Type} [DecidableEq hyp] (M : List datum → hyp)
    (s : List datum) {n : ℕ}
    (hn : n ∈ (List.range (s.length + 1)).filter (fun k =>
      if M (s.take k) = M (s.take (k + 1)) then false else true)) :
    M (s.take n) ≠ M (s.take (n + 1)) := by
  rcases List.mem_filter.mp hn with ⟨_, hb⟩
  intro heq
  exact Bool.false_ne_true ((ite_eq_left heq).symm.trans hb)

-- Reference: [Gold] 1967 — mind changes are counted by an injection into the
-- family; core `List.nodup_range`, `List.Nodup.filter`,
-- `List.nodup_map_iff_inj_on`, `List.card_toFinset`, `List.dedup_eq_self`,
-- `List.mem_toFinset`, `List.mem_map`, `Finset.card_le_card`,
-- `List.toFinset_card_le`, `List.length_map`.
/-- **Counting lemma**: if the outputs of `M` at the mind-change indices of `s`
land in `hs` and are pairwise distinct there, then
`mindChangesOn M s ≤ hs.length`. -/
theorem mindChangesOn_le_of_forall {hyp datum : Type} [DecidableEq hyp]
    (M : List datum → hyp) (s : List datum) (hs : List hyp)
    (hmem : ∀ n ∈ (List.range (s.length + 1)).filter
        (fun k => if M (s.take k) = M (s.take (k + 1)) then false else true),
      M (s.take n) ∈ hs)
    (hinj : ∀ n₁ ∈ (List.range (s.length + 1)).filter
        (fun k => if M (s.take k) = M (s.take (k + 1)) then false else true),
      ∀ n₂ ∈ (List.range (s.length + 1)).filter
        (fun k => if M (s.take k) = M (s.take (k + 1)) then false else true),
      M (s.take n₁) = M (s.take n₂) → n₁ = n₂) :
    mindChangesOn M s ≤ hs.length := by
  have hnodup : List.Nodup ((List.range (s.length + 1)).filter fun n =>
      if M (s.take n) = M (s.take (n + 1)) then false else true) :=
    (List.nodup_range).filter _
  have houts_nodup : List.Nodup (List.map (fun n => M (s.take n))
      ((List.range (s.length + 1)).filter fun n =>
        if M (s.take n) = M (s.take (n + 1)) then false else true)) :=
    (List.nodup_map_iff_inj_on hnodup).mpr hinj
  have hcard : (List.toFinset (List.map (fun n => M (s.take n))
        ((List.range (s.length + 1)).filter fun n =>
          if M (s.take n) = M (s.take (n + 1)) then false else true))).card
      = (List.map (fun n => M (s.take n)) ((List.range (s.length + 1)).filter fun n =>
          if M (s.take n) = M (s.take (n + 1)) then false else true)).length :=
    (List.card_toFinset _).trans (congrArg List.length (List.dedup_eq_self.mpr houts_nodup))
  have hsub : List.toFinset (List.map (fun n => M (s.take n))
      ((List.range (s.length + 1)).filter fun n =>
        if M (s.take n) = M (s.take (n + 1)) then false else true)) ⊆ hs.toFinset := by
    intro x hx
    rcases List.mem_toFinset.mp hx with hx'
    rcases List.mem_map.mp hx' with ⟨n, hn, rfl⟩
    exact List.mem_toFinset.mpr (hmem n hn)
  calc ((List.range (s.length + 1)).filter fun n =>
      if M (s.take n) = M (s.take (n + 1)) then false else true).length
      = (List.map (fun n => M (s.take n)) ((List.range (s.length + 1)).filter fun n =>
          if M (s.take n) = M (s.take (n + 1)) then false else true)).length :=
        (List.length_map _).symm
    _ = (List.toFinset (List.map (fun n => M (s.take n)) ((List.range (s.length + 1)).filter
          fun n => if M (s.take n) = M (s.take (n + 1)) then false else true))).card :=
        hcard.symm
    _ ≤ hs.toFinset.card := Finset.card_le_card hsub
    _ ≤ hs.length := List.toFinset_card_le _

-- Reference: [Gold] 1967 — a mind change permanently eliminates the old output
-- (`elimLearner_change_elim`), so distinct mind changes output distinct members
-- of `hs` (`elimLearner_compatible_of_change` + prefix monotonicity); then
-- `mindChangesOn_le_of_forall`.
/-- **The elimination learner makes at most `|hs|` mind changes on any finite
schedule** (proved): distinct mind changes output distinct members of `hs`. -/
theorem elimLearner_mindChanges_le {hyp datum : Type} [DecidableEq hyp]
    (hs : List hyp) (mass : hyp → datum → ℚ) (default : hyp) (s : List datum) :
    mindChangesOn (elimLearner hs mass default) s ≤ hs.length :=
  mindChangesOn_le_of_forall (elimLearner hs mass default) s hs
    (fun n hn => elimLearner_mem_of_change hs mass default s (change_of_mem_filter _ s hn))
    (fun n₁ hn₁ n₂ hn₂ heq => by
      rcases Nat.lt_trichotomy n₁ n₂ with hlt | heq' | hgt
      · have helim : compatibleBool mass (elimLearner hs mass default (s.take n₁))
            (s.take (n₁ + 1)) = false :=
          elimLearner_change_elim hs mass default s (change_of_mem_filter _ s hn₁)
        have hnc : compatibleBool mass (elimLearner hs mass default (s.take n₁)) (s.take n₂)
            = false := by
          cases h : compatibleBool mass (elimLearner hs mass default (s.take n₁))
            (s.take n₂) with
          | true =>
              exact absurd (compatibleBool_prefix _ _ h
                  (take_prefix_take s (Nat.succ_le_of_lt hlt)))
                fun ht => Bool.false_ne_true (helim.symm.trans ht)
          | false => rfl
        have hc2 : compatibleBool mass (elimLearner hs mass default (s.take n₂)) (s.take n₂)
            = true :=
          elimLearner_compatible_of_change hs mass default s (change_of_mem_filter _ s hn₂)
        exact absurd (Eq.subst (motive := fun x => compatibleBool mass x (s.take n₂) = true)
            heq.symm hc2) fun ht => Bool.false_ne_true (hnc.symm.trans ht)
      · exact heq'
      · have helim : compatibleBool mass (elimLearner hs mass default (s.take n₂))
            (s.take (n₂ + 1)) = false :=
          elimLearner_change_elim hs mass default s (change_of_mem_filter _ s hn₂)
        have hnc : compatibleBool mass (elimLearner hs mass default (s.take n₂)) (s.take n₁)
            = false := by
          cases h : compatibleBool mass (elimLearner hs mass default (s.take n₂))
            (s.take n₁) with
          | true =>
              exact absurd (compatibleBool_prefix _ _ h
                  (take_prefix_take s (Nat.succ_le_of_lt hgt)))
                fun ht => Bool.false_ne_true (helim.symm.trans ht)
          | false => rfl
        have hc1 : compatibleBool mass (elimLearner hs mass default (s.take n₁)) (s.take n₁)
            = true :=
          elimLearner_compatible_of_change hs mass default s (change_of_mem_filter _ s hn₁)
        exact absurd (Eq.subst (motive := fun x => compatibleBool mass x (s.take n₁) = true)
            heq hc1) fun ht => Bool.false_ne_true (hnc.symm.trans ht))

/-! ## The same bound for the Ockham learner -/

-- Reference: the definition of `natMin`; core `ite_eq_left`/`ite_eq_right`,
-- `Nat.lt_trichotomy`, `Nat.le_of_lt`, `Nat.le_of_eq`, `Nat.not_le`.
/-- `natMin a b ≤ a` (the min-scan never exceeds an argument). -/
theorem natMin_le_left (a b : ℕ) : natMin a b ≤ a := by
  rcases Nat.lt_trichotomy a b with h | h | h
  · exact Nat.le_of_eq (ite_eq_left (Nat.le_of_lt h))
  · exact Nat.le_of_eq (ite_eq_left (Nat.le_of_eq h))
  · exact (Nat.le_of_eq (ite_eq_right (Nat.not_le.mpr h))).trans (Nat.le_of_lt h)

-- Reference: as `natMin_le_left`.
/-- `natMin a b ≤ b`. -/
theorem natMin_le_right (a b : ℕ) : natMin a b ≤ b := by
  rcases Nat.lt_trichotomy a b with h | h | h
  · exact (Nat.le_of_eq (ite_eq_left (Nat.le_of_lt h))).trans (Nat.le_of_lt h)
  · exact (Nat.le_of_eq (ite_eq_left (Nat.le_of_eq h))).trans (Nat.le_of_eq h)
  · exact Nat.le_of_eq (ite_eq_right (Nat.not_le.mpr h))

-- Reference: as `natMin_le_left`/`natMin_le_right`; core `ite_eq_left`/`ite_eq_right`,
-- `Nat.lt_trichotomy`, `Nat.le_trans`.
/-- `natMin` is monotone in its second argument. -/
theorem natMin_le_natMin_right {x y y' : ℕ} (h : y ≤ y') : natMin x y ≤ natMin x y' := by
  rcases Nat.lt_trichotomy x y with hxy | hxy | hxy
  · have hxy' : x ≤ y' := Nat.le_of_lt (Nat.lt_of_lt_of_le hxy h)
    exact Nat.le_of_eq ((ite_eq_left (Nat.le_of_lt hxy)).trans (ite_eq_left hxy').symm)
  · have hxy' : x ≤ y' := Eq.subst (motive := fun z => z ≤ y') hxy.symm h
    exact Nat.le_of_eq ((ite_eq_left (Nat.le_of_eq hxy)).trans (ite_eq_left hxy').symm)
  · rcases Nat.lt_trichotomy x y' with hxy' | hxy' | hxy'
    · exact ((Nat.le_of_eq (ite_eq_right (Nat.not_le.mpr hxy))).trans (Nat.le_of_lt hxy)).trans
        (Nat.le_of_eq (ite_eq_left (Nat.le_of_lt hxy')).symm)
    · exact ((Nat.le_of_eq (ite_eq_right (Nat.not_le.mpr hxy))).trans (Nat.le_of_lt hxy)).trans
        (Nat.le_of_eq (ite_eq_left (Nat.le_of_eq hxy')).symm)
    · exact (Nat.le_of_eq (ite_eq_right (Nat.not_le.mpr hxy))).trans
        (h.trans (Nat.le_of_eq (ite_eq_right (Nat.not_le.mpr hxy')).symm))

-- Reference: equation lemmas of `minComplexity` (Ockham.lean: `[]`, `[h]`,
-- `h :: rest`); `rfl` only in these primitive definitional lemmas.
/-- The min-scan of the empty list is `0`. -/
theorem minComplexity_nil {hyp : Type} (c : hyp → ℕ) : minComplexity c [] = 0 := rfl

-- Reference: as `minComplexity_nil`.
/-- The min-scan of a singleton is the element's complexity. -/
theorem minComplexity_singleton {hyp : Type} (c : hyp → ℕ) (h : hyp) :
    minComplexity c [h] = c h := rfl

-- Reference: as `minComplexity_nil` (the `h :: rest` branch with `rest`
-- nonempty).
/-- The min-scan of a list of length `≥ 2` is the `natMin` step. -/
theorem minComplexity_cons_cons {hyp : Type} (c : hyp → ℕ) (a b : hyp) (r : List hyp) :
    minComplexity c (a :: b :: r) = natMin (c a) (minComplexity c (b :: r)) := rfl

-- Reference: induction on the list; core `List.mem_cons`, `List.not_mem_nil`;
-- `minComplexity_singleton`, `minComplexity_cons_cons`, `natMin_le_left`,
-- `natMin_le_right`.
/-- The min-scan is bounded above by each member's complexity. -/
theorem minComplexity_le_of_mem {hyp : Type} (c : hyp → ℕ) {l : List hyp} {x : hyp}
    (hx : x ∈ l) : minComplexity c l ≤ c x := by
  induction l with
  | nil => exact absurd hx List.not_mem_nil
  | cons a t ih =>
      have h0 : minComplexity c (a :: t) ≤ c a := by
        cases t with
        | nil => exact Nat.le_of_eq (minComplexity_singleton c a)
        | cons b r =>
            exact Eq.subst (motive := fun m => m ≤ c a)
              (minComplexity_cons_cons c a b r).symm (natMin_le_left _ _)
      rcases List.mem_cons.mp hx with he | hx'
      · exact Eq.subst (motive := fun y => minComplexity c (a :: t) ≤ c y) he.symm h0
      · cases t with
        | nil => exact absurd hx' List.not_mem_nil
        | cons b r =>
            exact Eq.subst (motive := fun m => m ≤ c x)
              (minComplexity_cons_cons c a b r).symm ((natMin_le_right _ _).trans (ih hx'))

-- Reference: the equation lemmas of `minComplexity` (Ockham.lean);
-- core `List.cons_ne_nil`, `Nat.lt_trichotomy`, `ite_eq_left`/`ite_eq_right`.
/-- The min-scan on a nonempty list is attained by a member. -/
theorem minComplexity_mem {hyp : Type} (c : hyp → ℕ) {l : List hyp} (hne : l ≠ []) :
    ∃ x ∈ l, minComplexity c l = c x := by
  cases l with
  | nil => exact absurd rfl hne
  | cons a t =>
      cases t with
      | nil => exact ⟨a, List.mem_cons_self, rfl⟩
      | cons b r =>
          rcases Nat.lt_trichotomy (c a) (minComplexity c (b :: r)) with h | h | h
          · exact ⟨a, List.mem_cons_self, ite_eq_left (Nat.le_of_lt h)⟩
          · exact ⟨a, List.mem_cons_self, ite_eq_left (Nat.le_of_eq h)⟩
          · obtain ⟨x, hx, hxm⟩ := minComplexity_mem c (List.cons_ne_nil b r)
            exact ⟨x, List.mem_cons_of_mem a hx, (ite_eq_right (Nat.not_le.mpr h)).trans hxm⟩

-- Reference: `minComplexity_mem` + `minComplexity_le_of_mem` +
-- `List.Sublist.mem` (a member of a sublist is a member of the list).
-- NOTE (repair): the empty sublist has min-scan `0`, so the inequality
-- `minComplexity c l₁ ≤ minComplexity c l₂` for `l₂ <+ l₁` needs the sublist
-- NONEMPTY (the empty-sublist case is false for `c a > 0`); the statement
-- below carries that hypothesis.
/-- The min-scan over a nonempty sublist is at least the min-scan over the
list. -/
theorem minComplexity_le_of_sublist {hyp : Type} (c : hyp → ℕ) {l₁ l₂ : List hyp}
    (h : l₂ <+ l₁) (hne : l₂ ≠ []) : minComplexity c l₁ ≤ minComplexity c l₂ := by
  obtain ⟨x, hx, hxm⟩ := minComplexity_mem c hne
  exact (minComplexity_le_of_mem c (h.mem hx)).trans (Nat.le_of_eq hxm.symm)

-- Reference: as `minComplexity_nil` (the `h :: rest` equation with `rest`
-- nonempty); computation step, `rfl` allowed here as a primitive definitional lemma.
/-- The min-scan on `a :: t` with `t` nonempty is `natMin (c a) (min-scan of t)`. -/
theorem minComplexity_cons_eq_natMin {hyp : Type} (c : hyp → ℕ) (a : hyp) {t : List hyp}
    (ht : t ≠ []) : minComplexity c (a :: t) = natMin (c a) (minComplexity c t) := by
  cases t with
  | nil => exact absurd rfl ht
  | cons b r => rfl

-- Reference: `congrArg` on the family argument of `ockhamLearner` (Ockham.lean).
/-- Congruence of the Ockham learner in the family list. -/
theorem ockhamLearner_congr {hyp datum : Type} (mass : hyp → datum → ℚ)
    (complexity : hyp → ℕ) (default : hyp) (p : List datum) {hs₁ hs₂ : List hyp}
    (h : hs₁ = hs₂) :
    ockhamLearner hs₁ mass complexity default p = ockhamLearner hs₂ mass complexity default p :=
  congrArg (fun l => ockhamLearner l mass complexity default p) h

-- Reference: zeta-unfolding of the `let`s in `ockhamLearner` + `congrArg` on the
-- match scrutinee.
/-- If two Ockham-learner calls have equal min-filter scrutinees, the outputs
agree. -/
theorem ockhamLearner_eq_of_scrutinee_eq {hyp datum : Type} (mass : hyp → datum → ℚ)
    (complexity : hyp → ℕ) (default : hyp) (p q : List datum) (hs₁ hs₂ : List hyp)
    (h : (hs₁.filter fun hh => compatibleBool mass hh p).filter
        (fun hh => if complexity hh = minComplexity complexity
          (hs₁.filter fun hh => compatibleBool mass hh p) then true else false)
      = (hs₂.filter fun hh => compatibleBool mass hh q).filter
        (fun hh => if complexity hh = minComplexity complexity
          (hs₂.filter fun hh => compatibleBool mass hh q) then true else false)) :
    ockhamLearner hs₁ mass complexity default p = ockhamLearner hs₂ mass complexity default q :=
  congrArg (fun l => match l with | [] => default | h :: _ => h) h

-- Reference: `ockhamLearner_eq_of_scrutinee_eq` + `Eq.subst` on the min-filter
-- scrutinee (the scrutinee is determined by the candidate filter).
/-- If two Ockham-learner calls have equal candidate filters, the outputs agree. -/
theorem ockhamLearner_eq_of_cands_eq {hyp datum : Type} (mass : hyp → datum → ℚ)
    (complexity : hyp → ℕ) (default : hyp) (p q : List datum) (hs₁ hs₂ : List hyp)
    (h : hs₁.filter (fun hh => compatibleBool mass hh p)
      = hs₂.filter (fun hh => compatibleBool mass hh q)) :
    ockhamLearner hs₁ mass complexity default p = ockhamLearner hs₂ mass complexity default q :=
  ockhamLearner_eq_of_scrutinee_eq mass complexity default p q hs₁ hs₂
    (Eq.subst (motive := fun l => l.filter (fun hh => if complexity hh
        = minComplexity complexity l then true else false)
      = (hs₂.filter fun hh => compatibleBool mass hh q).filter
        (fun hh => if complexity hh = minComplexity complexity
          (hs₂.filter fun hh => compatibleBool mass hh q) then true else false)) h.symm rfl)

-- Reference: `List.filter_cons` + `ite_eq_left`/`Eq.subst`; the head of the
-- candidate list is kept by the min-filter exactly when it attains the min.
/-- If the head of `l` attains `minComplexity complexity l`, the min-filter of `l`
has the same head. -/
theorem filter_head_of_head_min {hyp : Type} (complexity : hyp → ℕ) {l : List hyp}
    (a : hyp) (rest : List hyp) (heq : l = a :: rest)
    (hmin : complexity a = minComplexity complexity l) :
    l.filter (fun hh => if complexity hh = minComplexity complexity l then true else false)
      = a :: rest.filter (fun hh => if complexity hh = minComplexity complexity l
        then true else false) :=
  (congrArg (fun m => m.filter (fun hh => if complexity hh = minComplexity complexity l
      then true else false)) heq).trans
    ((List.filter_cons (p := fun hh => if complexity hh = minComplexity complexity l
        then true else false) (x := a) (xs := rest)).trans
      (Eq.subst (motive := fun (b : Bool) => (if b then a :: rest.filter (fun hh => if complexity hh
          = minComplexity complexity l then true else false)
          else rest.filter (fun hh => if complexity hh = minComplexity complexity l
          then true else false))
        = a :: rest.filter (fun hh => if complexity hh = minComplexity complexity l
          then true else false))
        (Eq.subst (motive := fun u => (if complexity a = u then true else false) = true) hmin
          (ite_eq_left rfl)).symm rfl))

-- Reference: as `filter_head_of_head_min`, with `ite_eq_right`; the min of the tail
-- is unchanged when the head does not attain it.
/-- If the head of `l` does not attain `minComplexity complexity l`, the min-filter
of `l` equals the min-filter of the tail. -/
theorem filter_tail_of_head_not_min {hyp : Type} (complexity : hyp → ℕ) {l : List hyp}
    (a : hyp) (rest : List hyp) (heq : l = a :: rest)
    (hmin : complexity a ≠ minComplexity complexity l)
    (hmin' : minComplexity complexity l = minComplexity complexity rest) :
    l.filter (fun hh => if complexity hh = minComplexity complexity l then true else false)
      = rest.filter (fun hh => if complexity hh = minComplexity complexity rest
        then true else false) := by
  have e1 : l.filter (fun hh => if complexity hh = minComplexity complexity l
      then true else false)
      = (a :: rest).filter (fun hh => if complexity hh = minComplexity complexity l
        then true else false) :=
    congrArg (fun m => m.filter (fun hh => if complexity hh = minComplexity complexity l
      then true else false)) heq
  have e2 : (a :: rest).filter (fun hh => if complexity hh = minComplexity complexity l
      then true else false)
      = if (fun hh => if complexity hh = minComplexity complexity l then true else false) a
        then a :: rest.filter (fun hh => if complexity hh = minComplexity complexity l
          then true else false)
        else rest.filter (fun hh => if complexity hh = minComplexity complexity l
          then true else false) :=
    List.filter_cons (p := fun hh => if complexity hh = minComplexity complexity l
      then true else false) (x := a) (xs := rest)
  have e3 : (if (fun hh => if complexity hh = minComplexity complexity l then true else false) a
      then a :: rest.filter (fun hh => if complexity hh = minComplexity complexity l
        then true else false)
      else rest.filter (fun hh => if complexity hh = minComplexity complexity l
        then true else false))
      = rest.filter (fun hh => if complexity hh = minComplexity complexity l
        then true else false) :=
    Eq.subst (motive := fun (b : Bool) => (if b then a :: rest.filter (fun hh => if complexity hh
        = minComplexity complexity l then true else false)
        else rest.filter (fun hh => if complexity hh = minComplexity complexity l
        then true else false))
      = rest.filter (fun hh => if complexity hh = minComplexity complexity l
        then true else false)) (ite_eq_right hmin).symm rfl
  have e4 : rest.filter (fun hh => if complexity hh = minComplexity complexity l
      then true else false)
      = rest.filter (fun hh => if complexity hh = minComplexity complexity rest
        then true else false) :=
    congrArg (fun m => rest.filter (fun hh => if complexity hh = m then true else false)) hmin'
  exact e1.trans (e2.trans (e3.trans e4))

-- Reference: `minComplexity_mem` + `List.mem_filter` + `Eq.subst`; a min-attaining
-- member of a nonempty candidate list survives the min-filter.
/-- If the min-filter at `p` is empty, no hypothesis is compatible with `p`. -/
theorem cands_eq_nil_of_minFilter_eq_nil {hyp datum : Type} (mass : hyp → datum → ℚ)
    (complexity : hyp → ℕ) (p : List datum) (hs : List hyp)
    (h : (hs.filter fun hh => compatibleBool mass hh p).filter
      (fun hh => if complexity hh = minComplexity complexity
        (hs.filter fun hh => compatibleBool mass hh p) then true else false) = []) :
    hs.filter (fun hh => compatibleBool mass hh p) = [] := by
  cases hc : hs.filter (fun hh => compatibleBool mass hh p) with
  | nil => rfl
  | cons c r =>
      obtain ⟨x, hx, hxm⟩ := minComplexity_mem complexity (List.cons_ne_nil c r)
      have hx' : x ∈ hs.filter (fun hh => compatibleBool mass hh p) :=
        Eq.subst (motive := fun l => x ∈ l) hc.symm hx
      have hxm' : minComplexity complexity (hs.filter fun hh => compatibleBool mass hh p)
          = complexity x :=
        Eq.subst (motive := fun l => minComplexity complexity l = complexity x) hc.symm hxm
      have hxsc : x ∈ (hs.filter fun hh => compatibleBool mass hh p).filter
          (fun hh => if complexity hh = minComplexity complexity
            (hs.filter fun hh => compatibleBool mass hh p) then true else false) :=
        List.mem_filter.mpr ⟨hx', Eq.subst (motive := fun u => (if complexity x = u then true
            else false) = true) hxm'.symm (ite_eq_left rfl)⟩
      exact absurd (Eq.subst (motive := fun l => x ∈ l) h hxsc) List.not_mem_nil

-- Reference: `ockhamLearner_cons`/`ockhamLearner_nil` + `List.mem_filter` +
-- `cands_eq_nil_of_minFilter_eq_nil`; the output is the head of the nonempty
-- min-filter, hence a min-attaining member of the candidate list.
/-- If the Ockham learner outputs `h` at `p` and some hypothesis is compatible with
`p`, then `h` is a compatible min-attaining member of the candidate list. -/
theorem ockhamLearner_mem_min_of_cands_ne_nil {hyp datum : Type} (hs : List hyp)
    (mass : hyp → datum → ℚ) (complexity : hyp → ℕ) (default : hyp) (p : List datum)
    (hne : hs.filter (fun hh => compatibleBool mass hh p) ≠ []) {h : hyp}
    (hp : ockhamLearner hs mass complexity default p = h) :
    h ∈ hs.filter (fun hh => compatibleBool mass hh p) ∧
    complexity h = minComplexity complexity (hs.filter fun hh => compatibleBool mass hh p) := by
  cases hsc : (hs.filter fun hh => compatibleBool mass hh p).filter
      (fun hh => if complexity hh = minComplexity complexity
        (hs.filter fun hh => compatibleBool mass hh p) then true else false) with
  | nil =>
      exact absurd (cands_eq_nil_of_minFilter_eq_nil mass complexity p hs hsc) hne
  | cons c r =>
      have e : ockhamLearner hs mass complexity default p = c :=
        ockhamLearner_cons hs mass complexity default p c r hsc
      have hhc : h = c := hp.symm.trans e
      have hmem : c ∈ (hs.filter fun hh => compatibleBool mass hh p).filter
          (fun hh => if complexity hh = minComplexity complexity
            (hs.filter fun hh => compatibleBool mass hh p) then true else false) :=
        Eq.subst (motive := fun l => c ∈ l) hsc.symm (List.mem_cons_self (a := c) (l := r))
      rcases List.mem_filter.mp hmem with ⟨hcands, hcm⟩
      have hcm' : complexity c = minComplexity complexity
          (hs.filter fun hh => compatibleBool mass hh p) := by
        cases hd : Nat.decEq (complexity c) (minComplexity complexity
            (hs.filter fun hh => compatibleBool mass hh p)) with
        | isTrue hceq => exact hceq
        | isFalse hceq =>
            exact absurd hcm fun ht => Bool.false_ne_true ((ite_eq_right hceq).symm.trans ht)
      exact ⟨Eq.subst (motive := fun x => x ∈ hs.filter fun hh => compatibleBool mass hh p)
          hhc.symm hcands,
        Eq.subst (motive := fun u => complexity u = minComplexity complexity
          (hs.filter fun hh => compatibleBool mass hh p)) hhc.symm hcm'⟩
set_option linter.unusedDecidableInType false in
-- Reference: [Kelly] 1996, [Gold] 1967; ticket #285. Mirror of
-- `elimLearner_stable`: induction on `hs` generalizing `p q h`; in the cons case
-- the head `a` either drops from the candidate filter at both prefixes
-- (`compatibleBool_prefix`, `ockhamLearner_eq_of_cands_eq`), or stays and either
-- attains the min at `p` (then `h = a` and the min at `q` is still `complexity a`
-- via `minComplexity_le_of_sublist`, `filter_head_of_head_min`), or is dropped
-- from the min-filter at both prefixes (`filter_tail_of_head_not_min`), so the
-- scrutinee equals the tail's (`ockhamLearner_eq_of_scrutinee_eq`) and `ih` applies.
/-- **Stability of the Ockham learner**: if `h` is output on the prefix `p` and
stays compatible with the longer prefix `q`, then `h` is still output on `q`
(proved). -/
theorem ockhamLearner_stable {hyp datum : Type} [DecidableEq hyp] [DecidableEq datum]
    (hs : List hyp) (mass : hyp → datum → ℚ) (complexity : hyp → ℕ) (default : hyp)
    {p q : List datum} (hpre : p <+: q) {h : hyp}
    (hp : ockhamLearner hs mass complexity default p = h)
    (hq : compatibleBool mass h q = true) :
    ockhamLearner hs mass complexity default q = h := by
  induction hs generalizing p q h with
  | nil =>
      have e1 : ockhamLearner [] mass complexity default p = default :=
        ockhamLearner_nil [] mass complexity default p rfl
      have e2 : ockhamLearner [] mass complexity default q = default :=
        ockhamLearner_nil [] mass complexity default q rfl
      exact e2.trans (hp.symm.trans e1).symm
  | cons a t ih =>
      have ef : ∀ r : List datum, compatibleBool mass a r = false →
          (a :: t).filter (fun hh => compatibleBool mass hh r)
            = t.filter (fun hh => compatibleBool mass hh r) :=
        fun r hr =>
          (List.filter_cons (p := fun hh => compatibleBool mass hh r) (x := a) (xs := t)).trans
            (Eq.subst (motive := fun b => (if b then a :: t.filter (fun hh =>
                compatibleBool mass hh r)
                else t.filter (fun hh => compatibleBool mass hh r))
                = t.filter (fun hh => compatibleBool mass hh r)) hr.symm rfl)
      have et : ∀ r : List datum, compatibleBool mass a r = true →
          (a :: t).filter (fun hh => compatibleBool mass hh r)
            = a :: t.filter (fun hh => compatibleBool mass hh r) :=
        fun r hr =>
          (List.filter_cons (p := fun hh => compatibleBool mass hh r) (x := a) (xs := t)).trans
            (Eq.subst (motive := fun b => (if b then a :: t.filter (fun hh =>
                compatibleBool mass hh r)
                else t.filter (fun hh => compatibleBool mass hh r))
                = a :: t.filter (fun hh => compatibleBool mass hh r)) hr.symm rfl)
      cases hpa : compatibleBool mass a p with
      | false =>
          have hqa : compatibleBool mass a q = false := by
            cases hqa : compatibleBool mass a q with
            | true =>
                exact absurd (compatibleBool_prefix mass a hqa hpre)
                  fun hp' => Bool.false_ne_true (hpa.symm.trans hp')
            | false => rfl
          have ep : ockhamLearner (a :: t) mass complexity default p
              = ockhamLearner t mass complexity default p :=
            ockhamLearner_eq_of_cands_eq mass complexity default p p (a :: t) t (ef p hpa)
          have eq : ockhamLearner (a :: t) mass complexity default q
              = ockhamLearner t mass complexity default q :=
            ockhamLearner_eq_of_cands_eq mass complexity default q q (a :: t) t (ef q hqa)
          exact eq.trans (ih hpre (ep.symm.trans hp) hq)
      | true =>
          cases hqa : compatibleBool mass a q with
          | false =>
              have hna : complexity a ≠ minComplexity complexity
                  ((a :: t).filter fun hh => compatibleBool mass hh p) := by
                intro hkeep
                have ha : ockhamLearner (a :: t) mass complexity default p = a :=
                  ockhamLearner_cons (a :: t) mass complexity default p a _
                    (filter_head_of_head_min complexity a
                      (t.filter fun hh => compatibleBool mass hh p) (et p hpa) hkeep)
                have hha : h = a := hp.symm.trans ha
                exact absurd (Eq.subst (motive := fun x => compatibleBool mass x q = true) hha hq)
                  fun hq' => Bool.false_ne_true (hqa.symm.trans hq')
              have htp : t.filter (fun hh => compatibleBool mass hh p) ≠ [] := by
                intro htp'
                have ecp : (a :: t).filter (fun hh => compatibleBool mass hh p) = [a] :=
                  (et p hpa).trans (congrArg (fun l => a :: l) htp')
                have hmp : minComplexity complexity ((a :: t).filter fun hh =>
                    compatibleBool mass hh p) = complexity a :=
                  Eq.subst (motive := fun l => minComplexity complexity l = complexity a) ecp.symm
                    (minComplexity_singleton complexity a)
                exact hna hmp.symm
              have hmc : minComplexity complexity ((a :: t).filter fun hh =>
                  compatibleBool mass hh p)
                  = natMin (complexity a) (minComplexity complexity
                    (t.filter fun hh => compatibleBool mass hh p)) :=
                Eq.subst (motive := fun l => minComplexity complexity l = natMin (complexity a)
                    (minComplexity complexity (t.filter fun hh => compatibleBool mass hh p)))
                  (et p hpa).symm (minComplexity_cons_eq_natMin complexity a htp)
              have hnle : ¬ (complexity a ≤ minComplexity complexity
                  (t.filter fun hh => compatibleBool mass hh p)) :=
                fun hle => hna (hmc.trans (ite_eq_left hle)).symm
              have hM : minComplexity complexity ((a :: t).filter fun hh =>
                  compatibleBool mass hh p)
                  = minComplexity complexity (t.filter fun hh => compatibleBool mass hh p) :=
                hmc.trans (ite_eq_right hnle)
              have hsc := filter_tail_of_head_not_min complexity a
                (t.filter fun hh => compatibleBool mass hh p) (et p hpa) hna hM
              have ept : ockhamLearner (a :: t) mass complexity default p
                  = ockhamLearner t mass complexity default p :=
                ockhamLearner_eq_of_scrutinee_eq mass complexity default p p (a :: t) t hsc
              have eq : ockhamLearner (a :: t) mass complexity default q
                  = ockhamLearner t mass complexity default q :=
                ockhamLearner_eq_of_cands_eq mass complexity default q q (a :: t) t (ef q hqa)
              exact eq.trans (ih hpre (ept.symm.trans hp) hq)
          | true =>
              cases hd : Nat.decEq (complexity a) (minComplexity complexity
                  ((a :: t).filter fun hh => compatibleBool mass hh p)) with
              | isTrue hkeep =>
                  have ha : ockhamLearner (a :: t) mass complexity default p = a :=
                    ockhamLearner_cons (a :: t) mass complexity default p a _
                      (filter_head_of_head_min complexity a
                        (t.filter fun hh => compatibleBool mass hh p) (et p hpa) hkeep)
                  have hha : h = a := hp.symm.trans ha
                  have hsub : t.filter (fun hh => compatibleBool mass hh q)
                      <+ t.filter (fun hh => compatibleBool mass hh p) :=
                    filter_sublist_of_imp (fun hh (hhq : compatibleBool mass hh q = true) =>
                      compatibleBool_prefix mass hh hhq hpre) t
                  cases htq : t.filter (fun hh => compatibleBool mass hh q) with
                  | nil =>
                      have ecq : (a :: t).filter (fun hh => compatibleBool mass hh q) = [a] :=
                        (et q hqa).trans (congrArg (fun l => a :: l) htq)
                      have hmq : minComplexity complexity
                          ((a :: t).filter fun hh => compatibleBool mass hh q) = complexity a :=
                        Eq.subst (motive := fun l => minComplexity complexity l = complexity a)
                          ecq.symm (minComplexity_singleton complexity a)
                      have hscq := filter_head_of_head_min complexity a
                        (t.filter fun hh => compatibleBool mass hh q) (et q hqa) hmq.symm
                      have hout : ockhamLearner (a :: t) mass complexity default q = a :=
                        ockhamLearner_cons (a :: t) mass complexity default q a _ hscq
                      exact Eq.subst (motive := fun x =>
                          ockhamLearner (a :: t) mass complexity default q = x) hha.symm hout
                  | cons b r =>
                      have hne_q : t.filter (fun hh => compatibleBool mass hh q) ≠ [] :=
                        fun he => List.cons_ne_nil b r (htq.symm.trans he)
                      have htp : t.filter (fun hh => compatibleBool mass hh p) ≠ [] := by
                        intro htp'
                        have hsub' : t.filter (fun hh => compatibleBool mass hh q) <+ [] :=
                          Eq.subst (motive := fun l =>
                            t.filter (fun hh => compatibleBool mass hh q) <+ l) htp' hsub
                        have h0 : List.length ([] : List hyp) = 0 := rfl
                        have hlen : (t.filter fun hh => compatibleBool mass hh q).length = 0 :=
                          Nat.le_zero.mp ((List.Sublist.length_le hsub').trans (Nat.le_of_eq h0))
                        exact hne_q (List.length_eq_zero_iff.mp hlen)
                      have hmc_p : minComplexity complexity
                          ((a :: t).filter fun hh => compatibleBool mass hh p)
                          = natMin (complexity a) (minComplexity complexity
                            (t.filter fun hh => compatibleBool mass hh p)) :=
                        Eq.subst (motive := fun l => minComplexity complexity l
                            = natMin (complexity a) (minComplexity complexity
                              (t.filter fun hh => compatibleBool mass hh p)))
                          (et p hpa).symm (minComplexity_cons_eq_natMin complexity a htp)
                      have hle_tp : complexity a ≤ minComplexity complexity
                          (t.filter fun hh => compatibleBool mass hh p) :=
                        (Nat.le_of_eq (hkeep.trans hmc_p)).trans (natMin_le_right _ _)
                      have hle_tq : complexity a ≤ minComplexity complexity
                          (t.filter fun hh => compatibleBool mass hh q) :=
                        hle_tp.trans (minComplexity_le_of_sublist complexity hsub hne_q)
                      have hmc_q : minComplexity complexity
                          ((a :: t).filter fun hh => compatibleBool mass hh q)
                          = natMin (complexity a) (minComplexity complexity
                            (t.filter fun hh => compatibleBool mass hh q)) :=
                        Eq.subst (motive := fun l => minComplexity complexity l
                            = natMin (complexity a) (minComplexity complexity
                              (t.filter fun hh => compatibleBool mass hh q)))
                          (et q hqa).symm (minComplexity_cons_eq_natMin complexity a hne_q)
                      have hmq : minComplexity complexity
                          ((a :: t).filter fun hh => compatibleBool mass hh q) = complexity a :=
                        hmc_q.trans (ite_eq_left hle_tq)
                      have hscq := filter_head_of_head_min complexity a
                        (t.filter fun hh => compatibleBool mass hh q) (et q hqa) hmq.symm
                      have hout : ockhamLearner (a :: t) mass complexity default q = a :=
                        ockhamLearner_cons (a :: t) mass complexity default q a _ hscq
                      exact Eq.subst (motive := fun x =>
                          ockhamLearner (a :: t) mass complexity default q = x) hha.symm hout
              | isFalse hkeep =>
                  have htp : t.filter (fun hh => compatibleBool mass hh p) ≠ [] := by
                    intro htp'
                    have ecp : (a :: t).filter (fun hh => compatibleBool mass hh p) = [a] :=
                      (et p hpa).trans (congrArg (fun l => a :: l) htp')
                    have hmp : minComplexity complexity ((a :: t).filter fun hh =>
                        compatibleBool mass hh p)
                        = complexity a :=
                      Eq.subst (motive := fun l => minComplexity complexity l = complexity a)
                        ecp.symm (minComplexity_singleton complexity a)
                    exact hkeep hmp.symm
                  have hmc : minComplexity complexity ((a :: t).filter fun hh =>
                      compatibleBool mass hh p)
                      = natMin (complexity a) (minComplexity complexity
                        (t.filter fun hh => compatibleBool mass hh p)) :=
                    Eq.subst (motive := fun l => minComplexity complexity l = natMin (complexity a)
                        (minComplexity complexity (t.filter fun hh => compatibleBool mass hh p)))
                      (et p hpa).symm (minComplexity_cons_eq_natMin complexity a htp)
                  have hnle : ¬ (complexity a ≤ minComplexity complexity
                      (t.filter fun hh => compatibleBool mass hh p)) :=
                    fun hle => hkeep (hmc.trans (ite_eq_left hle)).symm
                  have hM : minComplexity complexity ((a :: t).filter fun hh =>
                      compatibleBool mass hh p)
                      = minComplexity complexity (t.filter fun hh => compatibleBool mass hh p) :=
                    hmc.trans (ite_eq_right hnle)
                  have hsc := filter_tail_of_head_not_min complexity a
                    (t.filter fun hh => compatibleBool mass hh p) (et p hpa) hkeep hM
                  have ept : ockhamLearner (a :: t) mass complexity default p
                      = ockhamLearner t mass complexity default p :=
                    ockhamLearner_eq_of_scrutinee_eq mass complexity default p p (a :: t) t hsc
                  have hpt : ockhamLearner t mass complexity default p = h := ept.symm.trans hp
                  have hmem := ockhamLearner_mem_min_of_cands_ne_nil t mass complexity default p
                    htp hpt
                  have hmemq : h ∈ t.filter (fun hh => compatibleBool mass hh q) :=
                    List.mem_filter.mpr
                      ⟨List.Sublist.mem hmem.1 (List.filter_sublist (l := t)), hq⟩
                  have hne_q : t.filter (fun hh => compatibleBool mass hh q) ≠ [] :=
                    fun he => absurd (Eq.subst (motive := fun l => h ∈ l) he hmemq)
                      List.not_mem_nil
                  have hmemq_C : h ∈ (a :: t).filter (fun hh => compatibleBool mass hh q) :=
                    Eq.subst (motive := fun l => h ∈ l) (et q hqa).symm
                      (List.mem_cons_of_mem a hmemq)
                  have hle_q : minComplexity complexity
                      ((a :: t).filter fun hh => compatibleBool mass hh q) ≤ complexity h :=
                    minComplexity_le_of_mem complexity hmemq_C
                  have hlt : minComplexity complexity (t.filter fun hh => compatibleBool mass hh p)
                      < complexity a :=
                    Nat.not_le.mp hnle
                  have hmc_q : minComplexity complexity
                      ((a :: t).filter fun hh => compatibleBool mass hh q)
                      = natMin (complexity a) (minComplexity complexity
                        (t.filter fun hh => compatibleBool mass hh q)) :=
                    Eq.subst (motive := fun l => minComplexity complexity l = natMin (complexity a)
                        (minComplexity complexity (t.filter fun hh => compatibleBool mass hh q)))
                      (et q hqa).symm (minComplexity_cons_eq_natMin complexity a hne_q)
                  have hna_q : complexity a ≠ minComplexity complexity
                      ((a :: t).filter fun hh => compatibleBool mass hh q) := by
                    intro hkeepq
                    have h4 : complexity a ≤ minComplexity complexity
                        (t.filter fun hh => compatibleBool mass hh p) :=
                      (Nat.le_of_eq hkeepq).trans (hle_q.trans (Nat.le_of_eq hmem.2))
                    exact absurd h4 (Nat.not_le.mpr hlt)
                  have hnle_q : ¬ (complexity a ≤ minComplexity complexity
                      (t.filter fun hh => compatibleBool mass hh q)) :=
                    fun hle => hna_q (hmc_q.trans (ite_eq_left hle)).symm
                  have hM_q : minComplexity complexity
                      ((a :: t).filter fun hh => compatibleBool mass hh q)
                      = minComplexity complexity (t.filter fun hh => compatibleBool mass hh q) :=
                    hmc_q.trans (ite_eq_right hnle_q)
                  have hscq := filter_tail_of_head_not_min complexity a
                    (t.filter fun hh => compatibleBool mass hh q) (et q hqa) hna_q hM_q
                  have eqt : ockhamLearner (a :: t) mass complexity default q
                      = ockhamLearner t mass complexity default q :=
                    ockhamLearner_eq_of_scrutinee_eq mass complexity default q q (a :: t) t hscq
                  exact eqt.trans (ih hpre hpt hq)

set_option linter.unusedDecidableInType false in
-- Reference: [Kelly] 1996, [Gold] 1967; ticket #285; `ockhamLearner_stable` +
-- `take_prefix_take`, mirroring `elimLearner_change_elim`.
/-- **A mind change of the Ockham learner eliminates the old output** (proved). -/
theorem ockhamLearner_change_elim {hyp datum : Type} [DecidableEq hyp] [DecidableEq datum]
    (hs : List hyp) (mass : hyp → datum → ℚ) (complexity : hyp → ℕ) (default : hyp)
    (s : List datum) {n : ℕ}
    (hch : ockhamLearner hs mass complexity default (s.take n)
      ≠ ockhamLearner hs mass complexity default (s.take (n + 1))) :
    compatibleBool mass (ockhamLearner hs mass complexity default (s.take n)) (s.take (n + 1))
      = false := by
  cases hc : compatibleBool mass (ockhamLearner hs mass complexity default (s.take n))
      (s.take (n + 1)) with
  | true =>
      exact absurd (ockhamLearner_stable hs mass complexity default
        (take_prefix_take s (Nat.le_succ n)) rfl hc).symm hch
  | false => rfl

set_option linter.unusedDecidableInType false in
-- Reference: as `elimLearner_mem_of_change`, with `ockhamLearner_nil`/
-- `ockhamLearner_cons`, `filter_sublist_of_imp` and `cands_eq_nil_of_minFilter_eq_nil`.
/-- At a mind-change index the Ockham learner outputs a member of `hs`. -/
theorem ockhamLearner_mem_of_change {hyp datum : Type} [DecidableEq hyp] [DecidableEq datum]
    (hs : List hyp) (mass : hyp → datum → ℚ) (complexity : hyp → ℕ) (default : hyp)
    (s : List datum) {n : ℕ}
    (hch : ockhamLearner hs mass complexity default (s.take n)
      ≠ ockhamLearner hs mass complexity default (s.take (n + 1))) :
    ockhamLearner hs mass complexity default (s.take n) ∈ hs := by
  cases hfn : (hs.filter fun hh => compatibleBool mass hh (s.take n)).filter
      (fun hh => if complexity hh = minComplexity complexity
        (hs.filter fun hh => compatibleBool mass hh (s.take n)) then true else false) with
  | nil =>
      have e : ockhamLearner hs mass complexity default (s.take n) = default :=
        ockhamLearner_nil hs mass complexity default _ hfn
      have hcn : hs.filter (fun hh => compatibleBool mass hh (s.take n)) = [] :=
        cands_eq_nil_of_minFilter_eq_nil mass complexity (s.take n) hs hfn
      have hsub : hs.filter (fun hh => compatibleBool mass hh (s.take (n + 1)))
          <+ hs.filter (fun hh => compatibleBool mass hh (s.take n)) :=
        filter_sublist_of_imp
          (fun hh (hhq : compatibleBool mass hh (s.take (n + 1)) = true) =>
            compatibleBool_prefix mass hh hhq (take_prefix_take s (Nat.le_succ n))) hs
      have hsub' : hs.filter (fun hh => compatibleBool mass hh (s.take (n + 1))) <+ [] :=
        Eq.subst (motive := fun l => hs.filter (fun hh => compatibleBool mass hh (s.take (n + 1)))
          <+ l) hcn hsub
      have h0 : List.length ([] : List hyp) = 0 := rfl
      have hlen : (hs.filter fun hh => compatibleBool mass hh (s.take (n + 1))).length = 0 :=
        Nat.le_zero.mp ((List.Sublist.length_le hsub').trans (Nat.le_of_eq h0))
      have hnil : hs.filter (fun hh => compatibleBool mass hh (s.take (n + 1))) = [] :=
        List.length_eq_zero_iff.mp hlen
      have hsc : (hs.filter fun hh => compatibleBool mass hh (s.take (n + 1))).filter
          (fun hh => if complexity hh = minComplexity complexity
            (hs.filter fun hh => compatibleBool mass hh (s.take (n + 1)))
            then true else false) = [] :=
        Eq.subst (motive := fun l => l.filter (fun hh => if complexity hh =
            minComplexity complexity l
            then true else false) = []) hnil.symm rfl
      have e2 : ockhamLearner hs mass complexity default (s.take (n + 1)) = default :=
        ockhamLearner_nil hs mass complexity default _ hsc
      exact absurd (e.trans e2.symm) hch
  | cons c r =>
      have e : ockhamLearner hs mass complexity default (s.take n) = c :=
        ockhamLearner_cons hs mass complexity default _ c r hfn
      have hmem : c ∈ (hs.filter fun hh => compatibleBool mass hh (s.take n)).filter
          (fun hh => if complexity hh = minComplexity complexity
            (hs.filter fun hh => compatibleBool mass hh (s.take n)) then true else false) :=
        Eq.subst (motive := fun l => c ∈ l) hfn.symm (List.mem_cons_self (a := c) (l := r))
      rcases List.mem_filter.mp hmem with ⟨hcands, _⟩
      rcases List.mem_filter.mp hcands with ⟨hchs, _⟩
      exact Eq.subst (motive := fun x => x ∈ hs) e.symm hchs

set_option linter.unusedDecidableInType false in
-- Reference: as `ockhamLearner_mem_of_change`; the output at a mind change is the
-- head of the nonempty min-filter at `n`, hence compatible with `s.take n`.
/-- At a mind-change index the Ockham learner's output is compatible with the
prefix of length `n`. -/
theorem ockhamLearner_compatible_of_change {hyp datum : Type} [DecidableEq hyp] [DecidableEq datum]
    (hs : List hyp) (mass : hyp → datum → ℚ) (complexity : hyp → ℕ) (default : hyp)
    (s : List datum) {n : ℕ}
    (hch : ockhamLearner hs mass complexity default (s.take n)
      ≠ ockhamLearner hs mass complexity default (s.take (n + 1))) :
    compatibleBool mass (ockhamLearner hs mass complexity default (s.take n)) (s.take n)
      = true := by
  cases hfn : (hs.filter fun hh => compatibleBool mass hh (s.take n)).filter
      (fun hh => if complexity hh = minComplexity complexity
        (hs.filter fun hh => compatibleBool mass hh (s.take n)) then true else false) with
  | nil =>
      have e : ockhamLearner hs mass complexity default (s.take n) = default :=
        ockhamLearner_nil hs mass complexity default _ hfn
      have hcn : hs.filter (fun hh => compatibleBool mass hh (s.take n)) = [] :=
        cands_eq_nil_of_minFilter_eq_nil mass complexity (s.take n) hs hfn
      have hsub : hs.filter (fun hh => compatibleBool mass hh (s.take (n + 1)))
          <+ hs.filter (fun hh => compatibleBool mass hh (s.take n)) :=
        filter_sublist_of_imp
          (fun hh (hhq : compatibleBool mass hh (s.take (n + 1)) = true) =>
            compatibleBool_prefix mass hh hhq (take_prefix_take s (Nat.le_succ n))) hs
      have hsub' : hs.filter (fun hh => compatibleBool mass hh (s.take (n + 1))) <+ [] :=
        Eq.subst (motive := fun l => hs.filter (fun hh => compatibleBool mass hh (s.take (n + 1)))
          <+ l) hcn hsub
      have h0 : List.length ([] : List hyp) = 0 := rfl
      have hlen : (hs.filter fun hh => compatibleBool mass hh (s.take (n + 1))).length = 0 :=
        Nat.le_zero.mp ((List.Sublist.length_le hsub').trans (Nat.le_of_eq h0))
      have hnil : hs.filter (fun hh => compatibleBool mass hh (s.take (n + 1))) = [] :=
        List.length_eq_zero_iff.mp hlen
      have hsc : (hs.filter fun hh => compatibleBool mass hh (s.take (n + 1))).filter
          (fun hh => if complexity hh = minComplexity complexity
            (hs.filter fun hh => compatibleBool mass hh (s.take (n + 1)))
            then true else false) = [] :=
        Eq.subst (motive := fun l => l.filter (fun hh => if complexity hh =
            minComplexity complexity l
            then true else false) = []) hnil.symm rfl
      have e2 : ockhamLearner hs mass complexity default (s.take (n + 1)) = default :=
        ockhamLearner_nil hs mass complexity default _ hsc
      exact absurd (e.trans e2.symm) hch
  | cons c r =>
      have e : ockhamLearner hs mass complexity default (s.take n) = c :=
        ockhamLearner_cons hs mass complexity default _ c r hfn
      have hmem : c ∈ (hs.filter fun hh => compatibleBool mass hh (s.take n)).filter
          (fun hh => if complexity hh = minComplexity complexity
            (hs.filter fun hh => compatibleBool mass hh (s.take n)) then true else false) :=
        Eq.subst (motive := fun l => c ∈ l) hfn.symm (List.mem_cons_self (a := c) (l := r))
      rcases List.mem_filter.mp hmem with ⟨hcands, _⟩
      rcases List.mem_filter.mp hcands with ⟨_, hcomp⟩
      exact Eq.subst (motive := fun x => compatibleBool mass x (s.take n) = true) e.symm hcomp

set_option linter.unusedDecidableInType false in
-- Reference: [Kelly] 1996, [Gold] 1967; ticket #285; `ockhamLearner_change_elim` +
-- `ockhamLearner_mem_of_change` + `ockhamLearner_compatible_of_change` +
-- `mindChangesOn_le_of_forall`, mirroring `elimLearner_mindChanges_le`.
/-- **The Ockham learner makes at most `|hs|` mind changes on any finite
schedule** (proved). -/
theorem ockhamLearner_mindChanges_le {hyp datum : Type} [DecidableEq hyp] [DecidableEq datum]
    (hs : List hyp) (mass : hyp → datum → ℚ) (complexity : hyp → ℕ) (default : hyp)
    (s : List datum) :
    mindChangesOn (ockhamLearner hs mass complexity default) s ≤ hs.length :=
  mindChangesOn_le_of_forall (ockhamLearner hs mass complexity default) s hs
    (fun n hn => ockhamLearner_mem_of_change hs mass complexity default s
      (change_of_mem_filter _ s hn))
    (fun n₁ hn₁ n₂ hn₂ heq => by
      rcases Nat.lt_trichotomy n₁ n₂ with hlt | heq' | hgt
      · have helim : compatibleBool mass (ockhamLearner hs mass complexity default (s.take n₁))
            (s.take (n₁ + 1)) = false :=
          ockhamLearner_change_elim hs mass complexity default s (change_of_mem_filter _ s hn₁)
        have hnc : compatibleBool mass (ockhamLearner hs mass complexity default (s.take n₁))
            (s.take n₂) = false := by
          cases h : compatibleBool mass (ockhamLearner hs mass complexity default (s.take n₁))
              (s.take n₂) with
          | true =>
              exact absurd (compatibleBool_prefix _ _ h
                  (take_prefix_take s (Nat.succ_le_of_lt hlt)))
                fun ht => Bool.false_ne_true (helim.symm.trans ht)
          | false => rfl
        have hc2 : compatibleBool mass (ockhamLearner hs mass complexity default (s.take n₂))
            (s.take n₂) = true :=
          ockhamLearner_compatible_of_change hs mass complexity default s
            (change_of_mem_filter _ s hn₂)
        exact absurd (Eq.subst (motive := fun x => compatibleBool mass x (s.take n₂) = true)
            heq.symm hc2) fun ht => Bool.false_ne_true (hnc.symm.trans ht)
      · exact heq'
      · have helim : compatibleBool mass (ockhamLearner hs mass complexity default (s.take n₂))
            (s.take (n₂ + 1)) = false :=
          ockhamLearner_change_elim hs mass complexity default s (change_of_mem_filter _ s hn₂)
        have hnc : compatibleBool mass (ockhamLearner hs mass complexity default (s.take n₂))
            (s.take n₁) = false := by
          cases h : compatibleBool mass (ockhamLearner hs mass complexity default (s.take n₂))
              (s.take n₁) with
          | true =>
              exact absurd (compatibleBool_prefix _ _ h
                  (take_prefix_take s (Nat.succ_le_of_lt hgt)))
                fun ht => Bool.false_ne_true (helim.symm.trans ht)
          | false => rfl
        have hc1 : compatibleBool mass (ockhamLearner hs mass complexity default (s.take n₁))
            (s.take n₁) = true :=
          ockhamLearner_compatible_of_change hs mass complexity default s
            (change_of_mem_filter _ s hn₁)
        exact absurd (Eq.subst (motive := fun x => compatibleBool mass x (s.take n₁) = true)
            heq hc1) fun ht => Bool.false_ne_true (hnc.symm.trans ht))

/-! ## The pointwise-minimality statement is false as stated -/

-- Reference: `ockham_two_mind_changes` (Ockham.lean, proved) + `mindChangesOn_const`
-- (above); [Kelly] 1996 — efficiency is relative to identifying learners.
/-- **Counterexample to pointwise mind-change minimality**: on the toy schedule
`[heads, tails]` the Ockham learner makes 1 mind change while the constant
learner `fun _ => .alwaysTails` makes 0. Hence `ockham_min_changes_toy`
(Ockham.lean) is false as stated; ticket #285 repairs it. -/
theorem ockham_pointwise_minimality_fails :
    ¬ ∀ M : List Coin → TwoHyp,
      mindChangesOn (ockhamLearner twoHyps twoMass twoComplexity .alwaysTails)
          [Coin.heads, Coin.tails] ≤ mindChangesOn M [Coin.heads, Coin.tails] := by
  intro h
  have h1 := h (fun _ => TwoHyp.alwaysTails)
  have h0 : mindChangesOn (fun _ => TwoHyp.alwaysTails) [Coin.heads, Coin.tails] = 0 :=
    mindChangesOn_const TwoHyp.alwaysTails _
  have hle : (1:ℕ) ≤ mindChangesOn (fun _ => TwoHyp.alwaysTails) [Coin.heads, Coin.tails] :=
    Eq.subst (motive := fun n => n ≤ mindChangesOn (fun _ => TwoHyp.alwaysTails)
      [Coin.heads, Coin.tails]) ockham_two_mind_changes h1
  exact Nat.not_succ_le_zero 0 (Eq.subst (motive := fun n => (1:ℕ) ≤ n) h0 hle)

end BoringLab
