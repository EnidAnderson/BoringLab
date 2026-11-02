/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import Mathlib

/-!
# The trace semantics, first formal tokens: finite win/lose trees, the play filtration, and the value process

Free-standing substrate for LAB TR.0 (BoringLab #10): finite two-player
win/lose game trees in normal play (positions as nodes, moves as edges, the
cemetery = the terminal leaves), the play filtration as the explicit family of
prefix-observable event algebras, and the minimax value process. The first
theorems are the one-step super- and submartingale inequalities of the capital
process in Boolean form, plus the birthday 0/1 strata proven outright.

The averaged martingale form (expectation over the finite child algebra,
Shafer–Vovk capital-process framework) is parked at depth 1: it needs the
finite-expectation layer, which is the recorded next shard.

## References
* [Conway] J. H. Conway, *On Numbers and Games*, 2nd ed., A K Peters, 2000.
* [Shafer–Vovk] G. Shafer and V. Vovk, *Game-Theoretic Foundations for
  Probability and Finance*, Wiley, 2019 (DOI 10.1002/9781118548035).
* [Doob] J. L. Doob, *Stochastic Processes*, Wiley, 1953.
-/

universe u


-- Reference: standard Bool quantification over a finset (cf. [Doob],
-- Chapter II, finite conditional expectation, Boolean shadow).
/-- Existential `any` over a finset as a computable `Bool` (the `Finset.any`
name does not exist at the pin; this is the explicit replacement, phrased via
the cardinality of the filtered finset so that no `DecidableEq` instance is
needed). -/
def Finset.anyB {α : Type} (s : Finset α) (f : α → Bool) : Bool :=
  0 < (s.filter (fun q => f q = true)).card

-- Reference: standard Bool quantification over a finset.
/-- Universal `all` over a finset as a computable `Bool`. -/
def Finset.allB {α : Type} (s : Finset α) (f : α → Bool) : Bool :=
  (s.filter (fun q => f q = false)).card = 0

-- Reference: standard (unfolding the Bool existential through the filter cardinality).
theorem Finset.anyB_eq_true {α : Type} (s : Finset α) (f : α → Bool) :
    s.anyB f = true ↔ ∃ q ∈ s, f q = true := by
  unfold Finset.anyB
  exact decide_eq_true_iff.trans
    (Finset.card_pos.trans (exists_congr (fun q => Finset.mem_filter)))

-- Reference: standard (unfolding the Bool universal through the filter cardinality).
theorem Finset.allB_eq_true {α : Type} (s : Finset α) (f : α → Bool) :
    s.allB f = true ↔ ∀ q ∈ s, f q = true := by
  unfold Finset.allB
  exact decide_eq_true_iff.trans (Finset.card_eq_zero.trans (Finset.filter_eq_empty_iff.trans
    ⟨fun h q hq => (Bool.not_eq_false (f q)).mp (h hq),
      fun h x hx => (Bool.not_eq_false (f x)).mpr (h x hx)⟩)) -- justification: `decide`, `card = 0`, and filter-empty unfold the definition; what remains is the pointwise statement.

-- Reference: standard (pointwise congruence of the Bool existential).
theorem Finset.anyB_congr {α : Type} {s : Finset α} {f g : α → Bool}
    (h : ∀ q ∈ s, f q = g q) : s.anyB f = s.anyB g := by
  unfold Finset.anyB
  exact congrArg (fun t => (0 < t.card : Bool)) (Finset.filter_congr (fun q hq =>
    Eq.subst (h q hq) (motive := fun b => (f q = true) ↔ (b = true)) Iff.rfl)) -- justification: the two filters agree pointwise, hence have equal cardinality.

-- Reference: standard (pointwise congruence of the Bool universal).
theorem Finset.allB_congr {α : Type} {s : Finset α} {f g : α → Bool}
    (h : ∀ q ∈ s, f q = g q) : s.allB f = s.allB g := by
  unfold Finset.allB
  exact congrArg (fun t => (t.card = 0 : Bool)) (Finset.filter_congr (fun q hq =>
    Eq.subst (h q hq) (motive := fun b => (f q = false) ↔ (b = false)) Iff.rfl)) -- justification: the two filters agree pointwise, hence have equal cardinality.

namespace BoringLab
-- Reference: [Conway], Chapter 0 (positions, moves, normal play).
-- REVIEW(citation): pin the exact chapter in review.
/-- A finite two-player win/lose game tree in normal play: the player to move
at a terminal (cemetery) leaf loses. `turn p = true` means Left moves (and
maximizes Left's win indicator), `turn p = false` means Right moves. -/
structure WinLoseTree where
  pos : Type u
  instFintype : Fintype pos
  instDecEq : DecidableEq pos
  root : pos
  turn : pos → Bool
  terminal : pos → Bool
  moves : pos → Finset pos
  moves_terminal : ∀ p, terminal p = true → moves p = ∅
  moves_nonterminal : ∀ p, terminal p = false → (moves p).Nonempty
  depth : pos → ℕ
  depth_moves : ∀ p q, q ∈ moves p → depth q < depth p

-- Reference: [Conway], Chapter 0 (normal-play convention: no move, lose).
-- REVIEW(citation): pin the exact chapter in review.
/-- Depth-graded minimax value auxiliary: `valueAux t d p` computes the win
indicator at `p` using only children of depth `< d`. Structural recursion on
`d`, so no well-founded machinery is needed. -/
def WinLoseTree.valueAux (t : WinLoseTree) : ℕ → t.pos → Bool
  | 0, p => t.turn p
  | d+1, p =>
    if t.terminal p then t.turn p
    else if t.turn p then (t.moves p).anyB (t.valueAux d)
    else (t.moves p).allB (t.valueAux d)

-- Reference: [Conway], Chapter 0.
/-- Primitive definitional lemma: the depth-0 equation. -/
theorem WinLoseTree.valueAux_zero (t : WinLoseTree) (p : t.pos) :
    t.valueAux 0 p = t.turn p := rfl

-- Reference: [Conway], Chapter 0.
/-- Primitive definitional lemma: the depth-(d+1) equation. -/
theorem WinLoseTree.valueAux_succ (t : WinLoseTree) (d : ℕ) (p : t.pos) :
    t.valueAux (d+1) p =
      if t.terminal p then t.turn p
      else if t.turn p then (t.moves p).anyB (t.valueAux d)
      else (t.moves p).allB (t.valueAux d) := rfl

-- Reference: [Conway], Chapter 0 (cemetery leaves: outcome is the turn).
theorem WinLoseTree.valueAux_terminal (t : WinLoseTree) (d : ℕ) (p : t.pos)
    (h : t.terminal p = true) : t.valueAux d p = t.turn p := by
  cases d with
  | zero => rfl -- primitive definitional lemma.
  | succ d => unfold WinLoseTree.valueAux; exact ite_eq_left h -- justification: take the terminal branch.

-- Reference: [Shafer–Vovk], Chapter 1 (capital process definition).
-- REVIEW(citation): pin the capital-process definition page in review.
/-- The minimax win indicator for Left at `p`: `true` iff Left wins under
optimal play. -/
def WinLoseTree.value (t : WinLoseTree) (p : t.pos) : Bool :=
  t.valueAux (t.depth p) p

-- Reference: [Conway], Chapter 0.
/-- Primitive definitional lemma: the value is `valueAux` at the depth. -/
theorem WinLoseTree.value_eq_valueAux (t : WinLoseTree) (p : t.pos) :
    t.value p = t.valueAux (t.depth p) p := rfl

-- Reference: [Doob], Chapter II (martingale one-step property, Boolean shadow).
-- PEELING PLAN: induction on `d`; the non-terminal case uses `depth_moves`
-- to place every child below `d` (children have depth < depth p ≤ d, and the
-- d = 0 non-terminal case is impossible since it would force a child of
-- depth < 0, excluded by `Nat.not_lt_zero`), then the induction hypothesis
-- identifies `valueAux d q` with `valueAux (depth q) q` pointwise inside
-- `Finset.anyB`/`Finset.allB` via `Finset.anyB_congr`/`Finset.allB_congr`.
/-- Stabilization: above the depth of `p`, `valueAux` no longer changes. -/
theorem WinLoseTree.valueAux_of_le (t : WinLoseTree) : ∀ d p,
    t.depth p ≤ d → t.valueAux d p = t.valueAux (t.depth p) p := by
  intro d
  exact Nat.strongRecOn d
    (motive := fun d => ∀ p, t.depth p ≤ d → t.valueAux d p = t.valueAux (t.depth p) p)
    (fun d ih p h => by
      rcases Nat.eq_zero_or_pos d with rfl | hpos
      · -- d = 0: the depth is 0, both sides are `valueAux 0 p`.
        have h0 : t.depth p = 0 := Nat.eq_zero_of_le_zero h
        exact Eq.subst (motive := fun n => t.valueAux 0 p = t.valueAux n p) h0.symm rfl
      · obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hpos)
        cases ht : t.terminal p with
        | true =>
            -- leaf: both sides are the turn value (`valueAux_terminal`).
            exact (t.valueAux_terminal (k+1) p ht).trans
              (t.valueAux_terminal (t.depth p) p ht).symm
        | false =>
            have hne : ¬t.terminal p := (Bool.not_eq_true _).mpr ht
            -- a non-terminal position has positive depth.
            have hposd : t.depth p ≠ 0 := by
              intro h0
              obtain ⟨q, hq⟩ := t.moves_nonterminal p ht
              exact Nat.not_lt_zero _
                (Eq.subst (motive := fun n => t.depth q < n) h0 (t.depth_moves p q hq))
            obtain ⟨e, he⟩ := Nat.exists_eq_succ_of_ne_zero hposd
            have heqd : e ≤ k := Nat.succ_le_succ_iff.mp
              (Eq.subst (motive := fun n => n ≤ k+1) he h)
            -- every child has depth ≤ e ≤ k, so the induction hypothesis
            -- applies at both cutoffs `k` and `e`.
            have hchild : ∀ q ∈ t.moves p, t.depth q ≤ e ∧ t.depth q ≤ k := by
              intro q hq
              have hlt : t.depth q < e+1 :=
                Eq.subst (motive := fun n => t.depth q < n) he (t.depth_moves p q hq)
              exact ⟨Nat.le_of_lt_succ hlt, (Nat.le_of_lt_succ hlt).trans heqd⟩
            have ihk : ∀ q ∈ t.moves p, t.valueAux k q = t.valueAux (t.depth q) q :=
              fun q hq => ih k (Nat.lt_succ_self k) q (hchild q hq).2
            have ihe : ∀ q ∈ t.moves p, t.valueAux e q = t.valueAux (t.depth q) q :=
              fun q hq => ih e (Nat.lt_of_le_of_lt heqd (Nat.lt_succ_self k)) q (hchild q hq).1
            cases hturn : t.turn p with
            | true =>
                have lhs : t.valueAux (k+1) p = (t.moves p).anyB (t.valueAux k) :=
                  (t.valueAux_succ k p).trans ((ite_eq_right hne).trans (ite_eq_left hturn))
                have rhs : t.valueAux (t.depth p) p = (t.moves p).anyB (t.valueAux e) :=
                  Eq.subst (motive := fun n => t.valueAux n p = (t.moves p).anyB (t.valueAux e))
                    he.symm ((t.valueAux_succ e p).trans
                      ((ite_eq_right hne).trans (ite_eq_left hturn)))
                have c1 : (t.moves p).anyB (t.valueAux k) =
                    (t.moves p).anyB (fun q => t.valueAux (t.depth q) q) := Finset.anyB_congr ihk
                have c2 : (t.moves p).anyB (t.valueAux e) =
                    (t.moves p).anyB (fun q => t.valueAux (t.depth q) q) := Finset.anyB_congr ihe
                exact lhs.trans (c1.trans (c2.symm.trans rhs.symm))
            | false =>
                have hne2 : ¬t.turn p := (Bool.not_eq_true _).mpr hturn
                have lhs : t.valueAux (k+1) p = (t.moves p).allB (t.valueAux k) :=
                  (t.valueAux_succ k p).trans ((ite_eq_right hne).trans (ite_eq_right hne2))
                have rhs : t.valueAux (t.depth p) p = (t.moves p).allB (t.valueAux e) :=
                  Eq.subst (motive := fun n => t.valueAux n p = (t.moves p).allB (t.valueAux e))
                    he.symm ((t.valueAux_succ e p).trans
                      ((ite_eq_right hne).trans (ite_eq_right hne2)))
                have c1 : (t.moves p).allB (t.valueAux k) =
                    (t.moves p).allB (fun q => t.valueAux (t.depth q) q) := Finset.allB_congr ihk
                have c2 : (t.moves p).allB (t.valueAux e) =
                    (t.moves p).allB (fun q => t.valueAux (t.depth q) q) := Finset.allB_congr ihe
                exact lhs.trans (c1.trans (c2.symm.trans rhs.symm)))

-- Reference: [Conway], Chapter 0 (minimax/backward induction).
/-- The defining equation of the value: terminal leaves take the turn value;
Left-to-move nodes take the `anyB` (maximum) of the children; Right-to-move
nodes take the `allB` (minimum). -/
theorem WinLoseTree.value_eq (t : WinLoseTree) (p : t.pos) :
    t.value p =
      if t.terminal p then t.turn p
      else if t.turn p then (t.moves p).anyB t.value
      else (t.moves p).allB t.value := by
  cases ht : t.terminal p with
  | true => exact t.valueAux_terminal (t.depth p) p ht -- justification: leaf value, and `if true` reduces.
  | false =>
    have hne : ¬t.terminal p := (Bool.not_eq_true _).mpr ht -- justification: terminal p = false, so `terminal p = true` is impossible.
    cases hturn : t.turn p with
    | true =>
      show t.value p = (t.moves p).anyB t.value -- justification: non-terminal Left node takes the `anyB` branch.
      unfold WinLoseTree.value
      cases hd : t.depth p with
      | zero =>
        obtain ⟨q, hq⟩ := t.moves_nonterminal p ht
        have hlt : t.depth q < 0 :=
          Eq.subst (motive := fun n => t.depth q < n) hd (t.depth_moves p q hq) -- justification: depth p = 0, so the child would have depth < 0.
        exact absurd hlt (Nat.not_lt_zero _)
      | succ d =>
        exact (t.valueAux_succ d p).trans ((ite_eq_right hne).trans ((ite_eq_left hturn).trans
          (Finset.anyB_congr (fun q hq =>
            t.valueAux_of_le d q (Nat.lt_succ_iff.mp (Eq.subst hd (t.depth_moves p q hq))))))) -- justification: value equation at depth d+1, non-terminal Left node; child depths < depth p, so `valueAux_of_le` applies.
    | false =>
      show t.value p = (t.moves p).allB t.value -- justification: non-terminal Right node takes the `allB` branch.
      unfold WinLoseTree.value
      cases hd : t.depth p with
      | zero =>
        obtain ⟨q, hq⟩ := t.moves_nonterminal p ht
        have hlt : t.depth q < 0 :=
          Eq.subst (motive := fun n => t.depth q < n) hd (t.depth_moves p q hq) -- justification: depth p = 0, so the child would have depth < 0.
        exact absurd hlt (Nat.not_lt_zero _)
      | succ d =>
        exact (t.valueAux_succ d p).trans ((ite_eq_right hne).trans ((ite_eq_right ((Bool.not_eq_true _).mpr hturn)).trans
          (Finset.allB_congr (fun q hq =>
            t.valueAux_of_le d q (Nat.lt_succ_iff.mp (Eq.subst hd (t.depth_moves p q hq))))))) -- justification: value equation at depth d+1, non-terminal Right node; child depths < depth p, so `valueAux_of_le` applies.

-- Reference: [Doob], Chapter II (super/submartingale one-step inequalities).
-- REVIEW(citation): pin the exact section in review.
/-- **One-step supermartingale inequality (Left's capital).** At a Left node,
the value dominates every child value: capital cannot grow past the fair
value on Right's move. -/
theorem WinLoseTree.value_max_of_child (t : WinLoseTree) (p q : t.pos)
    (hq : q ∈ t.moves p) (hturn : t.turn p = true) (hn : t.terminal p = false)
    (hv : t.value q = true) : t.value p = true := by
  exact ((t.value_eq p).trans ((ite_eq_right ((Bool.not_eq_true _).mpr hn)).trans (ite_eq_left hturn))).trans
    ((Finset.anyB_eq_true (t.moves p) t.value).mpr ⟨q, hq, hv⟩) -- justification: value equation, non-terminal Left node, anyB unfolds to an existence.

-- Reference: [Doob], Chapter II (submartingale one-step inequality, dual).
/-- **One-step submartingale inequality (Left's capital).** At a Right node,
Left's win indicator passes down to every child. -/
theorem WinLoseTree.value_min_of_self (t : WinLoseTree) (p q : t.pos)
    (hq : q ∈ t.moves p) (hturn : t.turn p = false) (hn : t.terminal p = false)
    (hv : t.value p = true) : t.value q = true := by
  exact (Finset.allB_eq_true (t.moves p) t.value).mp
    (((t.value_eq p).trans ((ite_eq_right ((Bool.not_eq_true _).mpr hn)).trans
      (ite_eq_right ((Bool.not_eq_true _).mpr hturn)))).symm.trans hv) q hq -- justification: value equation, non-terminal Right node, allB unfolds to a universal.

-- Reference: [Shafer–Vovk], Chapter 1 (a play = a path of the protocol).
-- REVIEW(citation): pin the play definition page in review.
/-- A play prefix: a list starting at the root whose consecutive positions
are moves. -/
def WinLoseTree.IsPlayPrefix (t : WinLoseTree) (l : List t.pos) : Prop :=
  l.head? = some t.root ∧ List.Pairwise (fun a b => b ∈ t.moves a) l

-- Reference: [Shafer–Vovk], Chapter 1 (the growing public record).
-- REVIEW(citation): pin the protocol/filtration discussion page in review.
/-- The play filtration, finite form: an event `P` on play prefixes is
observable at depth `d` iff it depends only on the first `d` positions. -/
def WinLoseTree.measurableAt (t : WinLoseTree) (d : ℕ)
    (P : List t.pos → Prop) : Prop :=
  ∀ l₁ l₂ : List t.pos, l₁.take d = l₂.take d → (P l₁ ↔ P l₂)

-- Reference: [Shafer–Vovk], Chapter 1 (capital process).
/-- The capital (value) process along a play prefix: the minimax value at the
current position. -/
def WinLoseTree.capital (t : WinLoseTree) (l : List t.pos) : Bool :=
  t.value (l.getLastD t.root)

-- Reference: [Shafer–Vovk], Chapter 1 (the capital process is adapted to the
-- filtration).
/-- **Adaptation.** The capital process at depth `d` is observable at depth
`d`: it depends only on the first `d` positions of the play. -/
theorem WinLoseTree.capital_take_measurable (t : WinLoseTree) (d : ℕ) :
    t.measurableAt d (fun l => t.capital (l.take d)) := by
  intro l₁ l₂ h
  show t.capital (l₁.take d) = true ↔ t.capital (l₂.take d) = true -- justification: beta-reduce the event at the two prefixes.
  unfold WinLoseTree.capital
  exact (congrArg (fun l => (t.value (l.getLastD t.root) = true) ↔ (t.value ((l₂.take d).getLastD t.root) = true)) h).mpr Iff.rfl -- justification: prefixes agree on the first d positions, so the truncated capitals agree.

-- Reference: [Conway], Chapter 0 (birthday = depth).
/-- **Birthday 0 stratum:** a position of depth 0 is terminal. -/
theorem WinLoseTree.depth_zero_terminal (t : WinLoseTree) (p : t.pos)
    (h : t.depth p = 0) : t.terminal p = true := by
  cases ht : t.terminal p with
  | true => rfl -- primitive definitional lemma.
  | false =>
    obtain ⟨q, hq⟩ := t.moves_nonterminal p ht
    have hlt : t.depth q < 0 :=
      Eq.subst (motive := fun n => t.depth q < n) h (t.depth_moves p q hq) -- justification: depth p = 0, so the child would have depth < 0.
    exact absurd hlt (Nat.not_lt_zero _)

-- Reference: [Conway], Chapter 0 (one-ply trees).
/-- **Birthday 1 stratum:** at a non-terminal depth-1 node, the value is the
`anyB`/`allB` of the leaf outcomes (the children are terminal). -/
theorem WinLoseTree.value_birthday_one (t : WinLoseTree) (p : t.pos)
    (h : t.depth p = 1) (hn : t.terminal p = false) :
    t.value p =
      if t.turn p then (t.moves p).anyB (fun q => t.turn q)
      else (t.moves p).allB (fun q => t.turn q) := by
  refine ((t.value_eq p).trans (ite_eq_right ((Bool.not_eq_true _).mpr hn))).trans ?_ -- justification: value equation; the terminal branch of the value equation is excluded.
  cases hturn : t.turn p with
  | true =>
    show (t.moves p).anyB t.value = (t.moves p).anyB (fun q => t.turn q) -- justification: Left-to-move node takes the `anyB` branch.
    apply Finset.anyB_congr
    intro q hq
    -- the child has depth q < depth p = 1, hence depth q = 0 (`Nat.lt_one_iff`);
    -- it is a leaf (`depth_zero_terminal`), so its value is its turn.
    have h0 : t.depth q = 0 := Nat.lt_one_iff.mp
      (Eq.subst (motive := fun n => t.depth q < n) h (t.depth_moves p q hq))
    have e1 : t.value q = t.valueAux (t.depth q) q := t.value_eq_valueAux q
    have e2 : t.valueAux (t.depth q) q = t.valueAux 0 q := congrArg (fun n => t.valueAux n q) h0
    exact e1.trans (e2.trans (t.valueAux_zero q))
  | false =>
    show (t.moves p).allB t.value = (t.moves p).allB (fun q => t.turn q) -- justification: Right-to-move node takes the `allB` branch.
    apply Finset.allB_congr
    intro q hq
    -- same as the `true` branch: the child is a depth-0 leaf, value q = turn q.
    have h0 : t.depth q = 0 := Nat.lt_one_iff.mp
      (Eq.subst (motive := fun n => t.depth q < n) h (t.depth_moves p q hq))
    have e1 : t.value q = t.valueAux (t.depth q) q := t.value_eq_valueAux q
    have e2 : t.valueAux (t.depth q) q = t.valueAux 0 q := congrArg (fun n => t.valueAux n q) h0
    exact e1.trans (e2.trans (t.valueAux_zero q))

-- Reference: [Conway], Chapter 0 (two-ply minimax law).
-- REPAIR NOTE: an earlier version of this theorem claimed
-- `value p = anyB (fun q => (moves q).allB (fun r => turn r))` WITHOUT any
-- hypothesis on the children's turns. That statement is FALSE: a depth-2 Left
-- node may have a Left-to-move child `q` (value `q` = `anyB` of grandchild
-- turns, not `allB`), and a depth-0 child `q` is terminal with
-- `value q = turn q` while `allB (moves q) _ = true` on the empty move set.
-- The repaired statement below carries the alternation hypothesis
-- (`halt : ∀ q ∈ moves p, turn q = false`) and handles terminal children
-- through their turn.
-- Reference: [Conway], Chapter 0 (two-ply minimax law).
/-- **Birthday 2 stratum (repaired):** the two-level minimax law at a depth-2
Left node whose children are all Right-to-move — the value is the `anyB` over
children of (the child's terminal turn, or the `allB` over grandchild leaf
outcomes). -/
theorem WinLoseTree.value_birthday_two (t : WinLoseTree) (p : t.pos)
    (h : t.depth p = 2) (hn : t.terminal p = false) (hturn : t.turn p = true)
    (halt : ∀ q ∈ t.moves p, t.turn q = false) :
    t.value p = (t.moves p).anyB (fun q =>
      if t.terminal q then t.turn q else (t.moves q).allB (fun r => t.turn r)) := by
  have hne : ¬t.terminal p := (Bool.not_eq_true _).mpr hn
  have hval : t.value p = (t.moves p).anyB t.value :=
    (t.value_eq p).trans ((ite_eq_right hne).trans (ite_eq_left hturn))
  have hchild : ∀ q ∈ t.moves p, t.value q =
      (if t.terminal q then t.turn q else (t.moves q).allB (fun r => t.turn r)) := by
    intro q hq
    have hlt : t.depth q < 2 :=
      Eq.subst (motive := fun n => t.depth q < n) h (t.depth_moves p q hq)
    have hle : t.depth q ≤ 1 := Nat.lt_succ_iff.mp hlt
    cases htq : t.terminal q with
    | true =>
        show t.value q = t.turn q
        exact (t.value_eq q).trans (ite_eq_left htq)
    | false =>
        show t.value q = (t.moves q).allB (fun r => t.turn r)
        have hne2 : ¬t.terminal q := (Bool.not_eq_true _).mpr htq
        have hne3 : ¬t.turn q := (Bool.not_eq_true _).mpr (halt q hq)
        have hv : t.value q = (t.moves q).allB t.value :=
          (t.value_eq q).trans ((ite_eq_right hne2).trans (ite_eq_right hne3))
        have hgc : ∀ r ∈ t.moves q, t.value r = t.turn r := by
          intro r hr
          have hlt2 : t.depth r < 1 :=
            Nat.lt_of_lt_of_le (t.depth_moves q r hr) hle
          have h0 : t.depth r = 0 := Nat.lt_one_iff.mp hlt2
          exact ((t.value_eq r).trans (ite_eq_left (t.depth_zero_terminal r h0)))
        exact hv.trans (Finset.allB_congr hgc)
  exact hval.trans (Finset.anyB_congr hchild)

end BoringLab
