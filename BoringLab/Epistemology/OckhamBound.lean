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
  `ockham_min_changes_toy` (Ockham.lean, sorry) is **false as stated** —
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

-- Reference: [Kelly] 1996, [Gold] 1967; ticket #285 (repair of #32 item (c)).
-- TEMPORARY SORRY with peeling plan.
-- PEELING PLAN (ticket #285): mirror `elimLearner_stable` as
-- `ockhamLearner_stable`: if `h` is output at `p` and compatible at the longer
-- `q`, then `h ∈ cands q`, `cands q <+ cands p` (`filter_sublist_of_imp` +
-- `compatibleBool_prefix`), `minComplexity` over a sublist is `≥`
-- (`minComplexity_le_of_sublist`, from `natMin_le_left`/`natMin_le_right`), and
-- `≤ complexity h` (`minComplexity_le_of_mem`), while `complexity h =
-- minComplexity (cands p)` (the output lies in the min-filter), so the min at
-- `q` equals `complexity h` and `h` is still the first min-filter element at `q`
-- (`ockhamLearner_cons`). Then `ockhamLearner_change_elim`,
-- `ockhamLearner_mem_of_change`, and the count proceed exactly as
-- `elimLearner_change_elim` / `elimLearner_mem_of_change` /
-- `elimLearner_mindChanges_le`.
-- Reference: [Kelly] 1996, [Gold] 1967; ticket #285. TEMPORARY SORRY with plan.
/-- **The Ockham learner makes at most `|hs|` mind changes on any finite
schedule**. TEMPORARY SORRY with peeling plan. -/
theorem ockhamLearner_mindChanges_le {hyp datum : Type} [DecidableEq hyp]
    (hs : List hyp) (mass : hyp → datum → ℚ) (complexity : hyp → ℕ) (default : hyp)
    (s : List datum) :
    mindChangesOn (ockhamLearner hs mass complexity default) s ≤ hs.length := by
  sorry

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
