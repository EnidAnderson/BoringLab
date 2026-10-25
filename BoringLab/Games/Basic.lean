/-
Copyright (c) 2026 Enid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Enid
-/
import BoringMath.Foundations.Eta
import Mathlib.Init

/-!
# Partizan games: the basic definition

This module is the experimental skeleton for combinatorial game theory in
`BoringLab`, and follows the boring style (see the style guide in
`../BoringMath/docs/STYLE.md`).

A partizan game is defined à la Conway by its left and right options. We
use the standard indexed-moves encoding of the recursive definition
`G = {G^L | G^R}`: a `Set`-valued encoding would place the type being
declared to the left of an arrow and is rejected by Lean's kernel as a
non strictly positive definition.

Everything here is proved honestly except where the sorry protocol is
deliberately invoked.

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
from its components. This is the eta law for the structure `Game`. Because
`Game` has dependent fields, this is not a definitional equality for Lean's
kernel, so the proof analyses `g` into its components; the closing `rfl` is
permitted by the style guide because this is a primitive definitional
lemma. -/
theorem Game.eta (g : Game) :
    Game.mk g.left g.right g.moveLeft g.moveRight = g := by
  cases g with
  | mk left right moveLeft moveRight => rfl

-- Reference: [Barendregt], Chapter 2 (eta conversion).
-- REVIEW(citation): pin down the exact section in review.
/-- **Eta conversion** for functions on games: every function on games is
equal to its eta expansion. This is `BoringMath.eta` applied at the type
`Game`, recorded as a named lemma so that eta steps about games are never
taken anonymously. -/
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
/-- The games `zero` and `one` are not equal. -/
theorem zero_ne_one : zero ≠ one := by
  -- TEMPORARY SORRY: the honest proof has not been instantiated yet.
  -- PEELING PLAN: by injectivity of the constructor `Game.mk`, reduce to the
  -- claim that the left-indexing types of `zero` and `one` are distinct
  -- (`PEmpty` vs `PUnit`): transport `PUnit.unit` along such an
  -- identification, obtaining an element of `PEmpty`, and apply
  -- `PEmpty.elim`.
  sorry

end BoringLab
