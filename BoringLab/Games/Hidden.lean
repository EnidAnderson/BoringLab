/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import BoringLab.Games.Basic

/-!
# Face-down choices in games: hidden moves as irreducible "unknowns"

Lab ticket CFSG.GAMES.2 (under #276). A face-down card / hidden token is the
game-theoretic picture of an irreducible choice: Left secretly picks one of a
finite list of cards, then play continues in the chosen card. The game tree
records the cards as Left's options; the *secrecy* is a property of the play
and the referee, not of the tree. This is the gameplay anchor of the
dictionary row "sporadic simple groups ↔ irreducible forms of hidden
choice" (see BoringMath issue #276).

## References
* [Conway] J. H. Conway, *On Numbers and Games*, 2nd ed., A K Peters, 2001,
  ch. 0 (games as alternating play).
* [Rubinstein] A. Rubinstein, "Finite games with imperfect information",
  in *Logic and Algebra* (1999) (fog-of-war games).
* Program register: games-motives dictionary (workspace notes).
-/

namespace BoringLab

-- Reference: [Conway] ch. 0 (a game's left options are its Left moves);
-- [Rubinstein] (the hidden pick is tracked by the referee, not the tree).
/-- A **face-down choice by Left** among `cards`: the game whose left options
are the cards — Left picks one secretly, then play continues in it. -/
def faceDown (cards : List Game) : Game where
  left := Fin cards.length
  right := PEmpty
  moveLeft i := cards.get i
  moveRight p := p.elim

-- Reference: definitional (`List.get` on a singleton).
/-- The single card of a one-card face-down choice is its left option. -/
theorem faceDown_singleton_moveLeft (g : Game) :
    (faceDown [g]).moveLeft ⟨0, Nat.succ_pos 0⟩ = g := rfl

end BoringLab
