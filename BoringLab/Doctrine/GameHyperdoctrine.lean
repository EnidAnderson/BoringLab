/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import BoringLab.Doctrine.GameDoctrine
import BoringLab.Doctrine.NimHyperdoctrine

/-!
# The game hyperdoctrine: fibers are game doctrines

The GL.0 reading completed on the games side (`EnidAnderson/BoringLab#14`:
"the hyperdoctrine whose base is scopes and whose FIBERS ARE GAMES"):
`gameHyperdoctrine neutral` is a fully proved `Hyperdoctrine` instance
over the one-scope base `nimScope`, with fiber = `gameDoctrine neutral` at
every scope, root = the zero game `zero`, substitution = the identity
polygraph morphism (adjunctions proved by `Computad.Morph.mapPath_id`,
exactly as `nimHyperdoctrine`). The declared-move transport along
substitution is derived (`gameHyperdoctrine_neutral_transport`).

## References
* [Lawvere] F. W. Lawvere, *Adjointness in foundations*, Dialectica 23
  (1969), 135–145 (hyperdoctrines; `∃ ⊣ f* ⊣ ∀`).
* [Conway] J. H. Conway, *On Numbers and Games*, 2nd ed., A K Peters, 2000,
  ch. 0 (games; the zero game).
* Program register: ticket #14 (LAB TREE GL.0), items (i)–(iii); the Nim
  instance is `BoringLab.Doctrine.NimHyperdoctrine`.
-/

universe u

namespace BoringLab

/-! ## The instance -/

-- Reference: [Lawvere] 1969; ticket #14 — fiber = the game doctrine at
-- every scope, root = the zero game, substitution = identity morphism;
-- adjunctions by `mapPath_id` (as `nimHyperdoctrine`).
-- REVIEW(citation): pin the exact page of [Lawvere] in review.
/-- The **game hyperdoctrine**: the game doctrine as fiber over the
one-scope base, root `zero`, identity substitution — a fully proved
`Hyperdoctrine` instance (no sorries). -/
def gameHyperdoctrine (neutral : Game.{u} → Game.{u} → Prop) : Hyperdoctrine.{u+1} where
  scope := nimScope
  fiber := fun _ => gameDoctrine neutral
  root := fun _ => zero
  subst := fun _ => Computad.Morph.id gameComputad
  subst_root := fun _ => rfl
  subst_move := fun _g _X _Y p q h =>
    Eq.subst (motive := fun r => (gameDoctrine neutral).move r
        (Computad.Morph.mapPath (Computad.Morph.id gameComputad) q))
      (Computad.Morph.mapPath_id p).symm
      (Eq.subst (motive := fun s => (gameDoctrine neutral).move p s)
        (Computad.Morph.mapPath_id q).symm h)
  existsMap := fun _g φ => φ
  forallMap := fun _g φ => φ
  exists_adj := fun _g φ ψ =>
    Iff.intro
      (fun h => Eq.subst (motive := fun r => (gameDoctrine neutral).move φ r)
        (Computad.Morph.mapPath_id ψ) h)
      (fun h => Eq.subst (motive := fun r => (gameDoctrine neutral).move φ r)
        (Computad.Morph.mapPath_id ψ).symm h)
  forall_adj := fun _g φ ψ =>
    Iff.intro
      (fun h => Eq.subst (motive := fun r => (gameDoctrine neutral).move r φ)
        (Computad.Morph.mapPath_id ψ) h)
      (fun h => Eq.subst (motive := fun r => (gameDoctrine neutral).move r φ)
        (Computad.Morph.mapPath_id ψ).symm h)

-- Reference: ticket #14, items (ii)–(iii): substitution transports the
-- declared neutral moves — from `subst_move` and `gameDoctrine_move_self`.
/-- **Substitution transports the neutral-move sequents** of the game
doctrine (via `subst_move`, identity substitution). -/
theorem gameHyperdoctrine_neutral_transport (neutral : Game.{u} → Game.{u} → Prop)
    {X Y : Game.{u}} (hn : neutral X Y) (g : gameComputad.Hom X Y) :
    (gameDoctrine neutral).move
      ((Computad.Morph.id gameComputad).mapPath (gameComputad.toPath g))
      ((Computad.Morph.id gameComputad).mapPath (gameComputad.toPath g)) :=
  (gameHyperdoctrine neutral).subst_move PUnit.unit _ _
    (gameDoctrine_move_self neutral hn g)

end BoringLab
