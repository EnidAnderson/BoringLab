/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import Mathlib.Init

/-!
# The moduli of game kinds: `GameKind` as data

Lab ticket #147 (L.18.1): the theory of games is a MODULI SPACE of kinds of
games; the clean base is the ruleset-site (#106), and each kind is a variant
(coverage choice) on it. The flags are explicit data (STYLE 2.3). The
poker-vs-chess solver distinction is recorded as computed data:
perfect-information, chance-free, alternating, acyclic kinds have a minimax
value (the #10 TR.0 capital/value process); imperfect/chance kinds have an
equilibrium instead — solvers are NOT implemented here (or anywhere).

## References
* [Osborne-Rubinstein], *A Course in Game Theory*, CUP 1994, ch. 2/6 (the
  taxonomy: information, chance, simultaneous moves, zero-sum).
  REVIEW(citation): pin chapters in review.
* [Myerson] R. B., *Game Theory: Analysis of Conflict*, Harvard UP, 1991.
* [Conway] ONAG ch. 0 (perfect-information alternating CGT).
* Program register: ticket #147 (L.18.1); builds on #88/#106/#10.
-/

namespace BoringLab

-- Reference: [Osborne-Rubinstein], ch. 2 (the standard taxonomy of games).
-- REVIEW(citation): pin the chapter in review.
/-- A **kind of game** in the moduli of game kinds: explicit data flags for
the standard axes. A kind reads as a variant/coverage on the ruleset-site
(#106): changing a flag changes the ruleset's presentation. -/
structure GameKind where
  /-- Perfect information (both players see the whole position). -/
  perfectInfo : Bool
  /-- Chance moves (dice/cards dealt). -/
  chanceMoves : Bool
  /-- Simultaneous moves. -/
  simultaneous : Bool
  /-- Zero-sum (what one wins, the other loses). -/
  zeroSum : Bool
  /-- Loopy: play may cycle (draws possible). -/
  loopy : Bool

-- Reference: [Conway] ONAG ch. 0; the minimax value is the #10 TR.0 value
-- process (Games/Trace.lean, WinLoseTree.value) — computable on bounded trees.
/-- The kinds whose value is MINIMAX-computable: perfect information, no
chance, alternating, acyclic. (Poker-like kinds are not: their 'value' is an
equilibrium — [O]-graded, not formalized; see #147.) -/
def GameKind.minimaxComputable (k : GameKind) : Bool :=
  k.perfectInfo && !k.chanceMoves && !k.simultaneous && !k.loopy

-- Reference: standard (chess/draughts shape: perfect info, alternating,
-- zero-sum, acyclic).
/-- The chess-like kind. -/
def chessLike : GameKind :=
  { perfectInfo := true, chanceMoves := false, simultaneous := false,
    zeroSum := true, loopy := false }

-- Reference: standard (Nim shape: as chess-like but impartial — both players
-- have the same moves; the impartiality flag lives on the ruleset, #88).
/-- The Nim-like kind (perfect-info, impartial, zero-sum, acyclic). -/
def nimLike : GameKind := chessLike

-- Reference: [Osborne-Rubinstein] ch. on imperfect information + chance
-- (poker shape: hidden cards, chance deals).
/-- The poker-like kind: imperfect information with chance moves. -/
def pokerLike : GameKind :=
  { perfectInfo := false, chanceMoves := true, simultaneous := false,
    zeroSum := true, loopy := false }

-- Reference: [BCG] vol. 4 (Go: perfect info, zero-sum, LOOPY via ko — the
-- #98/#95 loopy flagship).
/-- The Go-like kind: perfect info, zero-sum, loopy (ko). -/
def goLike : GameKind :=
  { perfectInfo := true, chanceMoves := false, simultaneous := false,
    zeroSum := true, loopy := true }

-- Reference: computation steps; `rfl` only in these primitive definitional
-- lemmas.
/-- Primitive definitional lemma: chess-like kinds are minimax-computable. -/
theorem chessLike_minimaxComputable : chessLike.minimaxComputable = true := rfl

-- Reference: as above; the poker/chess distinction as computed data.
/-- Primitive definitional lemma: poker-like kinds are NOT minimax-computable
(hidden information + chance: the value is an equilibrium, not a minimax). -/
theorem pokerLike_not_minimaxComputable : pokerLike.minimaxComputable = false := rfl

-- Reference: as above (loopy kinds are not minimax-computable either: the
-- #95 loopy outcome engine applies instead).
/-- Primitive definitional lemma: loopy kinds are not minimax-computable. -/
theorem goLike_not_minimaxComputable : goLike.minimaxComputable = false := rfl

end BoringLab
