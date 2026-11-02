/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import BoringLab.Games.Arithmetic
import BoringLab.Games.Misere
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fin.SuccPred
import Mathlib.Init

/-!
# Normal play on the truncated carrier: the general outcome recursion

Lab ticket #82 (L.5.2), general case — every statement is for ALL depths and
ALL truncated games, proved by induction on the depth:

* `finAny_congr`, `finAny_eq_true_iff` — the Boolean existential over
  `Fin l` as a genuine existential, for every `l`;
* `normalOutcome` — the normal-play outcome (last-move-WINS; the player
  unable to move loses), with the disjunctive node equation;
* `normalOutcome_eq_true_iff` — the recursion as an iff, for every node;
* `normalOutcome_neg` — invariance under negation, for every game;
* the normal/misère complementarity at terminal nodes (proved, all depths)
  and its REFUTATION in general by an explicit nimber counterexample
  (`not_normal_eq_not_misere`) — the OckhamBound pattern: the true statement
  proved where it holds, the false general claim refuted by a proved
  witness.

## References
* [Conway] J. H. Conway, *On Numbers and Games*, 2nd ed., A K Peters, 2000,
  ch. 0 (normal play; the recursion `G` is a win for the mover iff some
  option is a loss for its mover).
* [BCG] E. R. Berlekamp, J. H. Conway, R. K. Guy, *Winning Ways*, vol. 1,
  2nd ed., A K Peters, 2001, ch. 13 (misère play; the two conventions).
* [OckhamBound] `BoringLab.Epistemology.OckhamBound` (#285): the anti-crank
  pattern — true bound proved, false-as-stated claim refuted by a proved
  counterexample.
* Program register: ticket #82 (L.5.2); builds on #20 (L.1.1) and #84 (L.5.3).
-/

namespace BoringLab

-- Reference: standard (pointwise congruence of the Boolean existential over
-- `Fin l`), proved by induction on `l` using `finAny_zero`/`finAny_succ`.
/-- **Congruence of `finAny`**: pointwise-equal predicates have equal
`finAny`, for every `l`. -/
theorem finAny_congr : ∀ (l : ℕ) {p q : Fin l → Bool},
    (∀ i, p i = q i) → finAny l p = finAny l q := by
  intro l
  induction l with
  | zero => intro p q _h; exact Eq.trans (finAny_zero p) (finAny_zero q).symm
  | succ k ih =>
    intro p q h
    change (p ⟨k, Nat.lt_succ_self k⟩ || finAny k (fun i => p i.castSucc)) =
      (q ⟨k, Nat.lt_succ_self k⟩ || finAny k (fun i => q i.castSucc))
    exact Eq.trans
      (congrArg (fun b : Bool => b || finAny k (fun i => p i.castSucc))
        (h ⟨k, Nat.lt_succ_self k⟩))
      (congrArg (fun x : Bool => q ⟨k, Nat.lt_succ_self k⟩ || x)
        (ih fun i => h i.castSucc))

-- Reference: standard (the Boolean existential over `Fin l` is an
-- existential), proved by induction on `l` via `Fin.eq_castSucc_or_eq_last`.
/-- **`finAny` is the Boolean existential**: `finAny l p = true` iff some
`i : Fin l` has `p i = true` — for every `l` and `p`. -/
theorem finAny_eq_true_iff : ∀ (l : ℕ) (p : Fin l → Bool),
    finAny l p = true ↔ ∃ i : Fin l, p i = true := by
  intro l
  induction l with
  | zero =>
    intro p
    exact ⟨fun h =>
        (Bool.false_ne_true (Eq.subst (motive := fun X => X = true) (finAny_zero p) h)).elim,
      fun ⟨i, _⟩ => Fin.elim0 i⟩
  | succ k ih =>
    intro p
    have hor : (p ⟨k, Nat.lt_succ_self k⟩ = true ∨
        finAny k (fun i => p i.castSucc) = true) ↔
        ((∃ i : Fin k, p i.castSucc = true) ∨ p ⟨k, Nat.lt_succ_self k⟩ = true) :=
      ⟨fun h => Or.elim h (fun x => Or.inr x)
          (fun x => Or.inl ((ih (fun i => p i.castSucc)).mp x)),
        fun h => Or.elim h (fun x => Or.inr ((ih (fun i => p i.castSucc)).mpr x))
          (fun x => Or.inl x)⟩
    have hcore : (p ⟨k, Nat.lt_succ_self k⟩ || finAny k (fun i => p i.castSucc)) = true ↔
        (∃ i : Fin k, p i.castSucc = true) ∨ p ⟨k, Nat.lt_succ_self k⟩ = true :=
      Bool.or_eq_true_iff.trans hor
    have hsplit : ∀ i : Fin (k + 1),
        (∃ j : Fin k, i = j.castSucc) ∨ i = ⟨k, Nat.lt_succ_self k⟩ :=
      fun i => Fin.eq_castSucc_or_eq_last i
    have hiff : (p ⟨k, Nat.lt_succ_self k⟩ || finAny k (fun i => p i.castSucc)) = true ↔
        ∃ i : Fin (k + 1), p i = true :=
      ⟨fun h => Or.elim (hcore.mp h)
          (fun ⟨j, hj⟩ => ⟨j.castSucc, hj⟩)
          (fun hl => ⟨⟨k, Nat.lt_succ_self k⟩, hl⟩),
        fun ⟨i, hi⟩ => hcore.mpr (Or.elim (hsplit i)
          (fun ⟨j, hj⟩ => Or.inl ⟨j, Eq.trans (congrArg p hj).symm hi⟩)
          (fun hl => Or.inr (Eq.trans (congrArg p hl).symm hi)))⟩
    exact Eq.subst (motive := fun X => X = true ↔ _) (finAny_succ k p).symm hiff

-- Reference: [Conway], ch. 0 (normal play: the player unable to move LOSES;
-- the last mover wins).
-- REVIEW(citation): pin the chapter in review.
/-- The normal-play outcome of a depth-truncated game as computable `Bool`:
`normalOutcome n g = true` iff the player to move at `g` wins under normal
play. Disjunctive form at a node: some option is a loss for its mover; at a
terminal node both `finAny` factors are `false`, so the mover loses. Total
on `TGame n` for every `n`. -/
def normalOutcome : (n : ℕ) → TGame n → Bool
  | 0, g => nomatch g
  | k + 1, TGame.node _ l r moveLeft moveRight =>
    finAny l (fun i => !(normalOutcome k (moveLeft i))) ||
    finAny r (fun j => !(normalOutcome k (moveRight j)))

-- Reference: computation step of `normalOutcome` on a node; `rfl` only in
-- this primitive definitional lemma.
/-- Primitive definitional lemma: the node equation of `normalOutcome`. -/
theorem normalOutcome_node {n l r : ℕ} (moveLeft : Fin l → TGame n)
    (moveRight : Fin r → TGame n) :
    normalOutcome (n + 1) (TGame.node n l r moveLeft moveRight) =
      (finAny l (fun i => !(normalOutcome n (moveLeft i))) ||
      finAny r (fun j => !(normalOutcome n (moveRight j)))) := rfl

-- Reference: [Conway], ch. 0 (a terminal position is a loss for the player
-- to move under normal play); `rfl` only in this primitive definitional
-- lemma.
/-- Primitive definitional lemma: a terminal node is a loss for the player
to move under normal play — for every depth. -/
theorem normalOutcome_node_terminal {n : ℕ} (moveLeft : Fin 0 → TGame n)
    (moveRight : Fin 0 → TGame n) :
    normalOutcome (n + 1) (TGame.node n 0 0 moveLeft moveRight) = false := rfl
-- Reference: standard (Boolean negation computes), by cases on the Bool.
/-- **Boolean negation computes**: `(!b = true) ↔ b = false`, for every `b`. -/
theorem bool_not_eq_true_iff (b : Bool) : (!b = true) ↔ b = false := by
  cases b with
  | false => exact ⟨fun _ => Eq.refl false, fun _ => Eq.refl true⟩
  | true =>
    exact ⟨fun h => (Bool.false_ne_true h).elim,
      fun h => (Bool.false_ne_true h.symm).elim⟩

-- Reference: [Conway], ch. 0 (the disjunctive recursion of normal play):
-- `G` is a win for the mover iff some option is a loss for its mover. General
-- iff-form for EVERY node, from `finAny_eq_true_iff` and `Bool.not_eq_true`.
/-- **The normal-play recursion as an iff, for every node**: the player to
move at `G` wins under normal play iff some left or right option is a loss
for the player to move there. -/
theorem normalOutcome_eq_true_iff {n l r : ℕ} (moveLeft : Fin l → TGame n)
    (moveRight : Fin r → TGame n) :
    normalOutcome (n + 1) (TGame.node n l r moveLeft moveRight) = true ↔
      (∃ i : Fin l, normalOutcome n (moveLeft i) = false) ∨
      (∃ j : Fin r, normalOutcome n (moveRight j) = false) := by
  have hL : (∃ i : Fin l, !(normalOutcome n (moveLeft i)) = true) ↔
      ∃ i : Fin l, normalOutcome n (moveLeft i) = false :=
    ⟨fun ⟨i, h⟩ => ⟨i, (bool_not_eq_true_iff _).mp h⟩,
      fun ⟨i, h⟩ => ⟨i, (bool_not_eq_true_iff _).mpr h⟩⟩
  have hR : (∃ j : Fin r, !(normalOutcome n (moveRight j)) = true) ↔
      ∃ j : Fin r, normalOutcome n (moveRight j) = false :=
    ⟨fun ⟨j, h⟩ => ⟨j, (bool_not_eq_true_iff _).mp h⟩,
      fun ⟨j, h⟩ => ⟨j, (bool_not_eq_true_iff _).mpr h⟩⟩
  have hor1 : (finAny l (fun i => !(normalOutcome n (moveLeft i))) = true ∨
      finAny r (fun j => !(normalOutcome n (moveRight j))) = true) ↔
      ((∃ i : Fin l, !(normalOutcome n (moveLeft i)) = true) ∨
      (∃ j : Fin r, !(normalOutcome n (moveRight j)) = true)) :=
    ⟨fun h => Or.elim h
        (fun x => Or.inl ((finAny_eq_true_iff l _).mp x))
        (fun x => Or.inr ((finAny_eq_true_iff r _).mp x)),
      fun h => Or.elim h
        (fun x => Or.inl ((finAny_eq_true_iff l _).mpr x))
        (fun x => Or.inr ((finAny_eq_true_iff r _).mpr x))⟩
  have hor : ((∃ i : Fin l, !(normalOutcome n (moveLeft i)) = true) ∨
      (∃ j : Fin r, !(normalOutcome n (moveRight j)) = true)) ↔
      ((∃ i : Fin l, normalOutcome n (moveLeft i) = false) ∨
      (∃ j : Fin r, normalOutcome n (moveRight j) = false)) :=
    ⟨fun h => Or.elim h (fun x => Or.inl (hL.mp x)) (fun x => Or.inr (hR.mp x)),
      fun h => Or.elim h (fun x => Or.inl (hL.mpr x)) (fun x => Or.inr (hR.mpr x))⟩
  have hcore : (finAny l (fun i => !(normalOutcome n (moveLeft i))) ||
      finAny r (fun j => !(normalOutcome n (moveRight j)))) = true ↔
      ((∃ i : Fin l, normalOutcome n (moveLeft i) = false) ∨
      (∃ j : Fin r, normalOutcome n (moveRight j) = false)) :=
    Bool.or_eq_true_iff.trans (hor1.trans hor)
  exact Eq.subst (motive := fun X => X = true ↔ _) (normalOutcome_node _ _).symm hcore

-- Reference: [Conway], ch. 0 (negation swaps the players; the normal-play
-- outcome of the mover is unchanged). General: all depths, all games, proved
-- by induction on the depth via `finAny_congr` and `Bool.or_comm`.
/-- **Negation invariance of the normal-play outcome**, for every depth `n`
and every truncated game `g`: `normalOutcome n (neg n g) = normalOutcome n g`. -/
theorem normalOutcome_neg : ∀ (n : ℕ) (g : TGame n),
    normalOutcome n (TGame.neg n g) = normalOutcome n g := by
  intro n
  induction n with
  | zero => intro g; nomatch g
  | succ k ih =>
    intro g
    cases g with
    | node _ l r f g' =>
      change (finAny r (fun j => !(normalOutcome k (TGame.neg k (g' j)))) ||
              finAny l (fun i => !(normalOutcome k (TGame.neg k (f i))))) =
             (finAny l (fun i => !(normalOutcome k (f i))) ||
              finAny r (fun j => !(normalOutcome k (g' j))))
      have e1 : finAny r (fun j => !(normalOutcome k (TGame.neg k (g' j)))) =
          finAny r (fun j => !(normalOutcome k (g' j))) :=
        finAny_congr r (fun j => congrArg Bool.not (ih (g' j)))
      have e2 : finAny l (fun i => !(normalOutcome k (TGame.neg k (f i)))) =
          finAny l (fun i => !(normalOutcome k (f i))) :=
        finAny_congr l (fun i => congrArg Bool.not (ih (f i)))
      exact Eq.trans
        (Eq.trans
          (congrArg (fun X : Bool =>
            X || finAny l (fun i => !(normalOutcome k (TGame.neg k (f i))))) e1)
          (congrArg (fun Y : Bool =>
            finAny r (fun j => !(normalOutcome k (g' j))) || Y) e2))
        (Bool.or_comm _ _)

-- Reference: [Conway], 2nd ed. 2001 / [BCG] vol. 1 ch. 13 (the two conventions
-- at a terminal position: normal play the mover loses, misère the mover
-- wins). Proved for EVERY depth; `rfl` only in this primitive definitional
-- lemma.
/-- **Complementarity at terminal nodes, all depths**: normal play and misère
play give opposite outcomes at every terminal node. -/
theorem normal_misere_complement_terminal {n : ℕ} (moveLeft : Fin 0 → TGame n)
    (moveRight : Fin 0 → TGame n) :
    normalOutcome (n + 1) (TGame.node n 0 0 moveLeft moveRight) =
      !(misereOutcome (n + 1) (TGame.node n 0 0 moveLeft moveRight)) := rfl

-- Reference: [Conway], ch. 4 / [BCG] vol. 1 ch. 2-4 (the nimbers
-- `*0`, `*1 = {*0 | *0}`, `*2 = {*0, *1 | *0, *1}`).
-- REVIEW(citation): pin the nimber chapter in review.
/-- The depth-2 leaf `*0` read at depth 2. -/
def leaf2 : TGame 2 := TGame.node 1 0 0 Fin.elim0 Fin.elim0

-- Reference: as above (`*1 = {*0 | *0}`).
/-- The nimber `*1 = {*0 | *0}` at depth 2. -/
def star1 : TGame 2 := TGame.node 1 1 1 (fun _ => leaf1) (fun _ => leaf1)

-- Reference: as above (`*2 = {*0, *1 | *0, *1}`).
/-- The nimber `*2 = {*0, *1 | *0, *1}` at depth 3: the two options are the
depth-2 leaf and `*1`. -/
def star2 : TGame 3 :=
  TGame.node 2 2 2
    (fun i => Fin.cases (n := 1) (motive := fun _ => TGame 2) leaf2 (fun _ => star1) i)
    (fun i => Fin.cases (n := 1) (motive := fun _ => TGame 2) leaf2 (fun _ => star1) i)

-- Reference: [Conway], ch. 0/4; computation steps, `rfl` only in these
-- primitive definitional lemmas.
/-- `*0` at depth 2 loses for the mover under normal play. -/
theorem normalOutcome_leaf2 : normalOutcome 2 leaf2 = false := rfl

-- Reference: as above (`*1` wins for the mover under normal play: its only
-- option `*0` loses for the next mover).
/-- `*1` wins for the mover under normal play. -/
theorem normalOutcome_star1 : normalOutcome 2 star1 = true := rfl

-- Reference: as above (`*2` wins for the mover under normal play: it moves
-- to `*0`).
/-- `*2` wins for the mover under normal play. -/
theorem normalOutcome_star2 : normalOutcome 3 star2 = true := rfl

-- Reference: [Conway], 2nd ed. 2001 / [BCG] vol. 1 ch. 13 (misère play).
/-- `*1` loses for the mover under misère play (its only move hands the
opponent a terminal win). -/
theorem misereOutcome_star1 : misereOutcome 2 star1 = false := rfl

-- Reference: as above (`*2` wins for the mover under misère play too: it
-- moves to `*1`, a misère loss for the next mover).
/-- `*2` wins for the mover under misère play AS WELL — the two conventions
agree here, so they are not complementary in general. -/
theorem misereOutcome_star2 : misereOutcome 3 star2 = true := rfl

-- Reference: the anti-crank pattern of `BoringLab.Epistemology.OckhamBound`
-- (#285): the true statement is proved where it holds
-- (`normal_misere_complement_terminal`), and the false general claim is
-- REFUTED by a proved counterexample.
/-- **The naive complementarity claim is false in general**: it is NOT the
case that `normalOutcome n g = !(misereOutcome n g)` for all truncated games
— the nimber `*2` is a win for the mover under BOTH conventions (both
outcomes are `true`, and `!true = false`). -/
theorem not_normal_eq_not_misere :
    ¬ ∀ (n : ℕ) (g : TGame n), normalOutcome n g = !(misereOutcome n g) :=
  fun h => (Bool.false_ne_true).symm
    (Eq.subst (motive := fun X => X = false) normalOutcome_star2
      (Eq.subst (motive := fun X => normalOutcome 3 star2 = X)
        (congrArg Bool.not misereOutcome_star2) (h 3 star2)))

end BoringLab
