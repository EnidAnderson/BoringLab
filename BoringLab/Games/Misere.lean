/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import BoringLab.Games.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Init

/-!
# Misère play on depth-truncated partizan games

Lab ticket #20 (L.1.1): depth-truncated partizan games as computable data
(`TGame`), the misère outcome `misereOutcome` under the last-move-loses
convention (the player unable to move wins), a truncation-antimonotonicity
shadow proved by explicit enumeration on a small finite family, and worked
depth-1 / depth-2 examples printed with `#eval`.

The left/right convention is the one of `BoringLab.Games.Basic`: `moveLeft`
collects Left's options and `moveRight` Right's options (Conway's
`G = {G^L | G^R}`).

## References
* [Conway] J. H. Conway, *On Numbers and Games*, 2nd ed., A K Peters, 2001.
* [BCG] E. R. Berlekamp, J. H. Conway, R. K. Guy, *Winning Ways for Your
  Mathematical Plays*, 2nd ed., vol. 1, A K Peters, 2001.
* [Doob] J. L. Doob, *Stochastic Processes*, Wiley, 1953.
-/

namespace BoringLab

-- Reference: [Conway], Chapter 0 (the recursive definition `G = {G^L | G^R}`,
-- depth-graded by the birthday); left/right convention as in `Games/Basic.lean`.
-- REVIEW(citation): pin down the exact chapter and section in review.
/-- A depth-truncated partizan game (computable data, `Type 0`): a position of
depth `n + 1` is a `node` carrying the counts `l` and `r` of left and right
options together with the option families `moveLeft` and `moveRight` into
depth `n`. `TGame 0` has no constructors: every depth-0 position is a leaf. -/
inductive TGame : ℕ → Type
  /-- A node: `l` left options and `r` right options, all of depth `n`. -/
  | node (n : ℕ) (l r : ℕ) (moveLeft : Fin l → TGame n)
      (moveRight : Fin r → TGame n) : TGame (n + 1)

-- Reference: [Conway], Chapter 0 (the definition `G = {G^L | G^R}`); the
-- left/right convention of `BoringLab.Games.Basic` (`Game.moveLeft` collects
-- Left's options, `Game.moveRight` Right's).
-- REVIEW(citation): same citation state as `Games/Basic.lean`.
/-- The forgetful map from depth-truncated games to `Game`: a node's left
options become `Game.moveLeft` and its right options `Game.moveRight`. -/
def TGame.toGame : (n : ℕ) → TGame n → Game.{0}
  | 0, g => nomatch g
  | k + 1, TGame.node _ l r moveLeft moveRight =>
    Game.mk (Fin l) (Fin r)
      (fun i => TGame.toGame k (moveLeft i)) (fun j => TGame.toGame k (moveRight j))

-- Reference: [Conway], Chapter 0.
-- REVIEW(citation): as above.
/-- Primitive definitional lemma: the node equation of `TGame.toGame`. -/
theorem TGame.toGame_node {n l r : ℕ} (moveLeft : Fin l → TGame n)
    (moveRight : Fin r → TGame n) :
    TGame.toGame (n + 1) (TGame.node n l r moveLeft moveRight) =
      Game.mk (Fin l) (Fin r) (fun i => TGame.toGame n (moveLeft i))
        (fun j => TGame.toGame n (moveRight j)) := rfl

-- Reference: standard Boolean existential over a finite index type (cf. [Doob],
-- Chapter II, finite Boolean quantification).
-- REVIEW(citation): folklore; no specific section.
/-- Computable Boolean "any" over `Fin n`, by recursion on `n`. -/
def finAny : (n : ℕ) → (Fin n → Bool) → Bool
  | 0, _ => false
  | k + 1, f => f ⟨k, Nat.lt_succ_self k⟩ || finAny k (fun i => f i.castSucc)

-- Reference: standard (unfolding `finAny` at `0`).
/-- Primitive definitional lemma: `finAny 0 f = false`. -/
theorem finAny_zero (f : Fin 0 → Bool) : finAny 0 f = false := rfl

-- Reference: standard (unfolding `finAny` at `k + 1`).
/-- Primitive definitional lemma: the successor equation of `finAny`. -/
theorem finAny_succ (k : ℕ) (f : Fin (k + 1) → Bool) :
    finAny (k + 1) f =
      (f ⟨k, Nat.lt_succ_self k⟩ || finAny k (fun i => f i.castSucc)) := rfl

-- Reference: [Conway], 2nd ed. 2001, misère play (misère Nim, pp. 136-140);
-- [BCG], vol. 1, ch. 13 (misère play, genus theory). Convention: the last mover
-- loses, i.e. the player unable to move wins.
-- REVIEW(citation): chapter/section not verified against the physical text; the
-- convention itself (last move loses = unable to move wins) was verified against
-- public sources (Wikipedia, "Combinatorial game theory", misère play;
-- T. Plambeck, "Advances in Losing", introduction).
-- Reference: [Conway], 2nd ed. 2001 / [BCG], vol. 1, ch. 13, misère play.
/-- The misère outcome of a depth-truncated game as computable `Bool`:
`misereOutcome n g = true` iff the player to move at `g` wins under misère
play (last-move-loses convention: the player unable to move wins).
Disjunctive form at a node: the player to move wins iff some option is a loss
for the player to move there, i.e. `(∃ i, misereOutcome n (moveLeft i) = false)
∨ (∃ j, misereOutcome n (moveRight j) = false)`, or the position is terminal
(`l = 0` and `r = 0`), in which case the player to move wins. At a depth-0
leaf the player to move wins (the opponent made the last move). -/
def misereOutcome : (n : ℕ) → TGame n → Bool
  | 0, g => nomatch g
  | k + 1, TGame.node _ l r moveLeft moveRight =>
    finAny l (fun i => !(misereOutcome k (moveLeft i))) ||
    (finAny r (fun j => !(misereOutcome k (moveRight j))) || ((l == 0) && (r == 0)))

-- Reference: [Conway], 2nd ed. 2001, misère convention at a leaf (the player
-- unable to move wins).
-- REVIEW(citation): as above.
/-- Primitive definitional lemma (leaf case): at a depth-0 leaf the player to
move wins — the opponent made the last move and loses. -/
theorem misereOutcome_zero (g : TGame 0) : misereOutcome 0 g = true := nomatch g

-- Reference: [Conway], 2nd ed. 2001 / [BCG], vol. 1, ch. 13, misère disjunctive
-- form at a node.
-- REVIEW(citation): as above.
/-- Primitive definitional lemma (node case): the misère outcome of a node is
`finAny l (fun i => !misereOutcome n (moveLeft i)) ∨ (finAny r (fun j =>
!misereOutcome n (moveRight j)) ∨ (l == 0 && r == 0))` — some option loses for
its mover, or the position is terminal. -/
theorem misereOutcome_node {n l r : ℕ} (moveLeft : Fin l → TGame n)
    (moveRight : Fin r → TGame n) :
    misereOutcome (n + 1) (TGame.node n l r moveLeft moveRight) =
      (finAny l (fun i => !(misereOutcome n (moveLeft i))) ||
      (finAny r (fun j => !(misereOutcome n (moveRight j))) || ((l == 0) && (r == 0)))) :=
  rfl

-- Reference: [Conway], 2nd ed. 2001, misère convention at a terminal position.
-- REVIEW(citation): as above.
/-- Primitive definitional lemma (terminal node case): a node with no options
is a win for the player to move under misère play. -/
theorem misereOutcome_node_terminal {n : ℕ} (moveLeft : Fin 0 → TGame n)
    (moveRight : Fin 0 → TGame n) :
    misereOutcome (n + 1) (TGame.node n 0 0 moveLeft moveRight) = true := rfl

-- Reference: [Conway], Chapter 0 (birthday = depth; depth truncations of one
-- fixed game).
-- REVIEW(citation): pin down the exact chapter in review.
/-- The one-move chain: the depth-`(n+1)` truncation of the infinite game in
which Left has exactly one move (to the previous truncation) and Right none. -/
def chain : (n : ℕ) → TGame (n + 1)
  | 0 => TGame.node 0 0 0 Fin.elim0 Fin.elim0
  | k + 1 => TGame.node (k + 1) 1 0 (fun _ => chain k) Fin.elim0

-- Reference: [Conway], 2nd ed. 2001 / [BCG], vol. 1, ch. 13, misère play.
-- REVIEW(citation): as above.
/-- The depth-1 chain is a terminal node: the player to move wins. -/
theorem chain_outcome_zero : misereOutcome 1 (chain 0) = true := rfl

-- Reference: [Conway], 2nd ed. 2001 / [BCG], vol. 1, ch. 13, misère play.
-- REVIEW(citation): as above.
/-- The depth-2 chain loses for the player to move: the only move hands the
opponent a terminal position, which is a win for them under misère play. -/
theorem chain_outcome_one : misereOutcome 2 (chain 1) = false := rfl

-- Reference: [Conway], 2nd ed. 2001 / [BCG], vol. 1, ch. 13, misère play.
-- REVIEW(citation): as above.
/-- The depth-3 chain wins for the player to move. -/
theorem chain_outcome_two : misereOutcome 3 (chain 2) = true := rfl

-- Reference: [Conway], 2nd ed. 2001 / [BCG], vol. 1, ch. 13, misère play.
-- REVIEW(citation): as above.
/-- The depth-4 chain loses for the player to move. -/
theorem chain_outcome_three : misereOutcome 4 (chain 3) = false := rfl

-- Reference: [Conway], Chapter 0 (truncations) and misère play as above.
-- REVIEW(citation): as above.
/-- **Truncation-antimonotonicity shadow — direction proved.** On the one-move
chain family (the depth truncations of one fixed infinite game), extending the
truncation by one ply *negates* the misère outcome: the strict antitone shadow
`misereOutcome (k+2) (chain (k+1)) = !misereOutcome (k+1) (chain k)`, proved
here by explicit enumeration on the fixed finite family `chain 0, chain 1,
chain 2, chain 3` (depths 1-4), each computation step a named `rfl` lemma. -/
theorem trunc_antimonotone_chain_zero :
    misereOutcome 2 (chain 1) = !(misereOutcome 1 (chain 0)) := rfl

-- Reference: [Conway], Chapter 0 (truncations) and misère play as above.
-- REVIEW(citation): as above.
/-- Second enumerated step of the truncation-antimonotonicity shadow. -/
theorem trunc_antimonotone_chain_one :
    misereOutcome 3 (chain 2) = !(misereOutcome 2 (chain 1)) := rfl

-- Reference: [Conway], Chapter 0 (truncations) and misère play as above.
-- REVIEW(citation): as above.
/-- Third enumerated step of the truncation-antimonotonicity shadow. -/
theorem trunc_antimonotone_chain_two :
    misereOutcome 4 (chain 3) = !(misereOutcome 3 (chain 2)) := rfl

-- Reference: [Conway], Chapter 0 (the zero game `0 = {|}`).
-- REVIEW(citation): same citation state as `Games/Basic.lean`.
/-- Worked example: the zero-like leaf — a depth-1 node with no options. -/
def leaf1 : TGame 1 := TGame.node 0 0 0 Fin.elim0 Fin.elim0

-- Reference: [Conway], Chapter 0 (a single left move `G = {0 | }`).
-- REVIEW(citation): as above.
/-- Worked example: a single left move to the leaf (depth 2). -/
def leftMove : TGame 2 := TGame.node 1 1 0 (fun _ => leaf1) Fin.elim0

-- Reference: [Conway], Chapter 0 (a single right move `G = { | 0}`).
-- REVIEW(citation): as above.
/-- Worked example: a single right move to the leaf (depth 2). -/
def rightMove : TGame 2 := TGame.node 1 0 1 Fin.elim0 (fun _ => leaf1)

-- Reference: [Conway], Chapter 0 (one left and one right move, `G = {0 | 0}`).
-- REVIEW(citation): as above.
/-- Worked example: one left and one right move, both to the leaf (depth 2,
2-ply). -/
def bothMoves : TGame 2 := TGame.node 1 1 1 (fun _ => leaf1) (fun _ => leaf1)

-- Reference: [Conway], Chapter 0 (a two-ply tree).
-- REVIEW(citation): as above.
/-- Worked example: a depth-3 tree whose unique left option is the losing
depth-2 `leftMove` — a win for the player to move. -/
def leftToLoss : TGame 3 := TGame.node 2 1 0 (fun _ => leftMove) Fin.elim0

-- Reference: [Conway], 2nd ed. 2001 / [BCG], vol. 1, ch. 13, misère play.
-- REVIEW(citation): as above.
/-- The zero-like leaf is a win for the player to move (terminal, misère). -/
theorem leaf1_outcome : misereOutcome 1 leaf1 = true := rfl

-- Enumeration of the depth-2 truncations whose options are all leaves: each
-- loses for the player to move under misère play (each move hands the
-- opponent a terminal win). Each computation step is a named `rfl` lemma.

-- Reference: [Conway], 2nd ed. 2001 / [BCG], vol. 1, ch. 13, misère play.
-- REVIEW(citation): as above.
/-- The single-left-move depth-2 tree loses for the player to move. -/
theorem leftMove_outcome : misereOutcome 2 leftMove = false := rfl

-- Reference: [Conway], 2nd ed. 2001 / [BCG], vol. 1, ch. 13, misère play.
-- REVIEW(citation): as above.
/-- The single-right-move depth-2 tree loses for the player to move. -/
theorem rightMove_outcome : misereOutcome 2 rightMove = false := rfl

-- Reference: [Conway], 2nd ed. 2001 / [BCG], vol. 1, ch. 13, misère play.
-- REVIEW(citation): as above.
/-- The two-ply depth-2 tree with one left and one right move loses for the
player to move. -/
theorem bothMoves_outcome : misereOutcome 2 bothMoves = false := rfl

-- Reference: [Conway], 2nd ed. 2001 / [BCG], vol. 1, ch. 13, misère play.
-- REVIEW(citation): as above.
/-- The depth-3 tree whose unique left option is a loss for its mover wins for
the player to move. -/
theorem leftToLoss_outcome : misereOutcome 3 leftToLoss = true := rfl

end BoringLab
