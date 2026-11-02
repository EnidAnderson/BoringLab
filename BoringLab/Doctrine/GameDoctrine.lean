/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import BoringLab.Doctrine.Geometric
import BoringLab.Doctrine.Coverage
import BoringLab.Games.Basic

/-!
# The game computad: rules of play as geometric theory over `Game`

The GL.0 reading made concrete on the lab's own game type
(`EnidAnderson/BoringLab#14`: "the hyperdoctrine whose base is scopes and
whose FIBERS ARE GAMES — Conway = values born from well-founded nested scope
trees"):

* `gameComputad` — positions (`Game`) as objects, legal moves as generators
  (a generator is a position plus a left/right option; source = the
  position, target = the option position), port universe `Bool` with `||`
  as the port monoid (the mover's tag: `false` = Left, `true` = Right);
* `gameDoctrine neutral` — the doctrine whose declared moves are the
  `neutral`-related pairs of parallel single-move paths (the certified
  value-neutral simplifications — the sieve content, GL.0);
* `gameDoctrine_generator_inverted` — the falsifiable shadow, derived via
  the A2.0 inversion machinery (as `misereQuotient_generator_inverted`);
* `gameCoverage` — the maximal coverage at every position (the play
  convention as coverage data, as `nimCoverage`).

## References
* [Conway] J. H. Conway, *On Numbers and Games*, 2nd ed., A K Peters, 2000,
  ch. 0 (games as `{G^L | G^R}`; moves to options).
* [Mimram] S. Mimram, arXiv:2312.00429, LMCS 21(3) (2025), Definition 3.5
  (relations between parallel paths = sequents).
* [Gabriel–Zisman] P. Gabriel, M. Zisman, *Calculus of Fractions and
  Homotopy Theory*, LNM 1, Springer, 1967, Chapter I (inversion in the
  localization).
* Program register: ticket #14 (LAB TREE GL.0), items (i)/(iii).
-/

universe u

namespace BoringLab

open CategoryTheory

/-! ## The game computad -/

-- Reference: [Conway], ch. 0 (a move goes from a game to one of its
-- options); the port monoid is `Bool` with `||` (the mover's tag).
-- REVIEW(citation): pin the Conway chapter in review.
/-- The **game computad**: objects are games; a generator is a position
together with one of its options (left via `Sum.inl`, right via
`Sum.inr`); source = the position, target = the option. Ports: the mover's
tag (`false` = Left, `true` = Right) as the left port; the port monoid is
`(Bool, ||, false)`. -/
def gameComputad : Computad.{u+1} where
  port := ULift.{u+1} Bool
  portMul := fun a b => ULift.up (a.down || b.down)
  portOne := ULift.up false
  portMul_assoc := fun a b c => by
    cases a with | up x => cases b with | up y => cases c with | up z =>
      cases x <;> cases y <;> cases z <;> rfl
  portMul_left_one := fun a => by
    cases a with | up x => cases x <;> rfl
  portMul_right_one := fun a => by
    cases a with | up x => cases x <;> rfl
  obj := Game.{u}
  gen := Sigma fun g : Game.{u} => g.left ⊕ g.right
  src := fun m => m.1
  tgt := fun m => match m.2 with
    | Sum.inl l => m.1.moveLeft l
    | Sum.inr r => m.1.moveRight r
  leftPorts := fun m => match m.2 with
    | Sum.inl _ => [ULift.up false]
    | Sum.inr _ => [ULift.up true]
  rightPorts := fun _ => []

-- Reference: [Conway], ch. 0; computation step of `gameComputad.tgt` on a
-- left option; `rfl` only in this primitive definitional lemma.
/-- The target of a left-move generator is the left option. -/
theorem gameComputad_tgt_inl (g : Game.{u}) (l : g.left) :
    gameComputad.tgt ⟨g, Sum.inl l⟩ = g.moveLeft l := rfl

-- Reference: computation step of `gameComputad.tgt` on a right option.
/-- The target of a right-move generator is the right option. -/
theorem gameComputad_tgt_inr (g : Game.{u}) (r : g.right) :
    gameComputad.tgt ⟨g, Sum.inr r⟩ = g.moveRight r := rfl

/-! ## The game doctrine: value-neutral simplifications as sequents -/

-- Reference: ticket #14, item (i) (rules of play as geometric sequents;
-- sieves = certified value-neutral simplifications); the `neutral` relation
-- is explicit data (as `misereQuotient`'s `r`).
/-- The **game doctrine** for a value-neutrality relation `neutral`: the
game computad with declared moves = pairs of parallel single-move paths
whose endpoints are `neutral`-related. -/
def gameDoctrine (neutral : Game.{u} → Game.{u} → Prop) : Doctrine.{u+1} where
  computad := gameComputad
  move := fun {X Y} p q =>
    (∃ g : gameComputad.Hom X Y, p = gameComputad.toPath g) ∧
    (∃ h : gameComputad.Hom X Y, q = gameComputad.toPath h) ∧
    neutral X Y

-- Reference: as `misereQuotient_move_self`; a single-move path moves to
-- itself when the endpoints are neutral.
/-- A single-move path over a `neutral` pair is a declared self-move. -/
theorem gameDoctrine_move_self (neutral : Game.{u} → Game.{u} → Prop) {X Y : Game.{u}}
    (hn : neutral X Y) (g : gameComputad.Hom X Y) :
    (gameDoctrine neutral).move (gameComputad.toPath g) (gameComputad.toPath g) :=
  ⟨⟨g, rfl⟩, ⟨g, rfl⟩, hn⟩

-- Reference: [Gabriel–Zisman], Chapter I, via `Doctrine.moveClass_left` and
-- `MorphismProperty.Q_inverts` (as
-- `misereQuotient_generator_inverted`); ticket #14, item (iii).
/-- **Falsifiable shadow, derived**: in the game-doctrine localization,
every generator path over a `neutral` pair is inverted. -/
theorem gameDoctrine_generator_inverted (neutral : Game.{u} → Game.{u} → Prop)
    {X Y : Game.{u}} (hn : neutral X Y) (g : gameComputad.Hom X Y) :
    IsIso ((gameDoctrine neutral).moveClass.Q.map (gameComputad.toPath g)) :=
  MorphismProperty.Q_inverts (gameDoctrine neutral).moveClass _
    (Doctrine.moveClass_left (gameDoctrine neutral) _ _
      (gameDoctrine_move_self neutral hn g))

-- Reference: ticket #14, item (i): the sequent of a neutral generator via
-- `Doctrine.toSequent`.
/-- The sequent of a value-neutral single move. -/
def gameSequent (neutral : Game.{u} → Game.{u} → Prop) {X Y : Game.{u}}
    (_hn : neutral X Y) (g : gameComputad.Hom X Y) : GeometricSequent gameComputad :=
  Doctrine.toSequent (gameDoctrine neutral) (gameComputad.toPath g) (gameComputad.toPath g)

/-! ## The play convention as coverage -/

-- Reference: ticket #14, item (iv); as `nimCoverage`: the maximal coverage
-- at every position (the play CONVENTION as coverage data on the terminal
-- stratum, recorded at comment level — games have no terminal object).
/-- The **game coverage**: at every position, the covering sieve is the
maximal one. -/
def gameCoverage : Coverage gameComputad := fun X => [Sieve.maximal gameComputad X]

-- Reference: computation step of `gameCoverage`.
/-- The game coverage at `X`. -/
theorem gameCoverage_eq (X : Game.{u}) :
    gameCoverage X = [Sieve.maximal gameComputad X] := rfl

end BoringLab
