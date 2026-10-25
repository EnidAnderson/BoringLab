/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import BoringMath.Foundations.Eta
import Mathlib.Init

/-!
# Partizan games: the basic definition

A partizan game is defined à la Conway by its left and right options,
encoded through the standard indexed-moves form of the recursive
definition `G = {G^L | G^R}`: the indexing types `left` and `right` and the
option functions `moveLeft` and `moveRight`.

## References
* [Conway] J. H. Conway, *On Numbers and Games*, 2nd ed., A K Peters, 2000.
* [Barendregt] H. P. Barendregt, *The Lambda Calculus: Its Syntax and
  Semantics*, North-Holland, 1984.
-/

universe u

namespace BoringLab

-- Reference: [Conway], Chapter 0 (the definition of partizan games).
-- REVIEW(citation): pin down the exact chapter and section in review.
/-- A partizan game in the sense of Conway: a position together with indexed
families of left and right options. The recursive definition
`G = {G^L | G^R}` is encoded by the indexing types `left` and `right` and the
option functions `moveLeft` and `moveRight`. -/
structure Game where
  /-- The indexing type for the left options of the game. -/
  left : Type u
  /-- The indexing type for the right options of the game. -/
  right : Type u
  /-- The left options of the game, indexed by `left`. -/
  moveLeft : left → Game
  /-- The right options of the game, indexed by `right`. -/
  moveRight : right → Game

-- Reference: [Barendregt], Chapter 2 (eta conversion).
-- REVIEW(citation): pin down the exact section in review.
/-- **Eta conversion for games**: every game is equal to the game assembled
from its components. -/
theorem Game.eta (g : Game) :
    Game.mk g.left g.right g.moveLeft g.moveRight = g := by
  cases g with
  | mk left right moveLeft moveRight => rfl

-- Reference: [Barendregt], Chapter 2 (eta conversion).
-- REVIEW(citation): pin down the exact section in review.
/-- **Eta conversion** for functions on games: every function on games is
equal to its eta expansion (`BoringMath.eta` at the type `Game`). -/
theorem Game.eta_fun (f : Game → Nat) : (fun g => f g) = f := BoringMath.eta f

-- Reference: [Conway], Chapter 0 (the zero game `0 = {|}`).
-- REVIEW(citation): pin down the exact chapter and section in review.
/-- The zero game: the game with no left options and no right options. -/
def zero : Game := Game.mk PEmpty PEmpty PEmpty.elim PEmpty.elim

-- Reference: [Conway], Chapter 0 (the game `1 = {0|}`).
-- REVIEW(citation): pin down the exact chapter and section in review.
/-- The game one: the game whose unique left option is the zero game, and
which has no right options. -/
def one : Game := Game.mk PUnit PEmpty (fun _ => zero) PEmpty.elim

-- Reference: [Conway], Chapter 0 (the games `0` and `1` are distinct).
-- REVIEW(citation): pin down the exact chapter and section in review.
/-- The games `zero` and `one` are not equal: their left-indexing types are
`PEmpty` and `PUnit`. -/
theorem zero_ne_one : zero ≠ one :=
  -- Transport `PUnit.unit` along the left-indexing-type identification to
  -- obtain an element of `PEmpty`.
  fun h => PEmpty.elim (cast (congrArg Game.left h).symm PUnit.unit)

end BoringLab
