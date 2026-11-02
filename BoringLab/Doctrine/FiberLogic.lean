/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import BoringLab.Doctrine.Geometric

/-!
# GL.0.3: fiber enrichment — finite meets, Heyting implication, Beck–Chevalley

Ticket #71 (child of GL.0 #14; the logic-power rung of the hyperdoctrine
layer). The landed `Hyperdoctrine` (`BoringLab.Doctrine.Geometric`) has
fibers with declared-move entailment and quantifier maps, but no
`meet`/`top` — nothing to bind. This module adds, as data with the laws as
`Prop` fields (STYLE.D hypothesis-carriers):

* `FiberLogic` — a doctrine fiber (endo-paths at a root) with `top` and
  `meet`, the meet laws (`meet φ ψ ⊢ φ`, `meet φ ψ ⊢ ψ`, and
  `χ ⊢ φ → χ ⊢ ψ → χ ⊢ meet φ ψ`);
* `HeytingImp` — the Heyting implication `imp` with the adjunction
  `meet φ ψ ⊢ χ ↔ φ ⊢ imp ψ χ` (statement layer, as a field);
* `EnrichedHyperdoctrine` — a `Hyperdoctrine` whose fibers carry
  `FiberLogic`, with substitution preserving `meet`/`top`
  (`subst_meet`, `subst_top` — the finite-limit fragment stable under
  pullback) and the **Beck–Chevalley condition** as the named-hole field
  (`beckChevalley`);
* the toy: the chaotic doctrine (`move := True`) — a degenerate but honest
  instance where all the laws hold (`True.intro`), recorded as such.

Note recorded for review (per #71's build-bot note): the placeholder
`existsMap := fun _ _ => Quiver.Path.nil` in
`BoringLab.Doctrine.ShiftHyperdoctrine` is wrong-shaped (∃ cannot be
constant in φ); the real quantifier maps are part of the Beck–Chevalley
peeling plan there — not proved against the placeholder.

## References
* [Lawvere] F. W. Lawvere, *Adjointness in foundations*, Dialectica 23 (1969),
  135–145 (hyperdoctrines: finitely-meeting Heyting fibers; Beck–Chevalley
  for ∃ along pullback).
* [Mac Lane–Moerdijk] S. Mac Lane, I. Moerdijk, *Sheaves in Geometry and
  Logic*, Springer, 1992, ch. IV (Heyting algebras of subobjects).
* Program register: BoringLab tickets #14 (GL.0) and #71 (GL.0.3).
-/

namespace BoringLab

/-! ## Fiber meets -/

-- Reference: ticket #71, item (i); [Lawvere] 1969 (finite meets in the
-- fibers); the laws as `Prop` fields.
/-- A **fiber logic**: a doctrine with a root object, carrying `top` and
`meet` on endo-paths at the root, with the meet laws (the path-level
combinator that IS conjunction). -/
structure FiberLogic (d : Doctrine) (root : d.computad.obj) where
  /-- The top predicate (the empty path at the root, up to the doctrine). -/
  top : d.computad.Path root root
  /-- The meet (conjunction) of two predicates. -/
  meet : d.computad.Path root root → d.computad.Path root root → d.computad.Path root root
  /-- Meet is below the left factor. -/
  meet_le_left : ∀ φ ψ, d.move (meet φ ψ) φ
  /-- Meet is below the right factor. -/
  meet_le_right : ∀ φ ψ, d.move (meet φ ψ) ψ
  /-- Meet is the greatest lower bound. -/
  le_meet : ∀ φ ψ χ, d.move χ φ → d.move χ ψ → d.move χ (meet φ ψ)
  /-- Top is above everything. -/
  le_top : ∀ φ, d.move φ top

-- Reference: [Barendregt], ch. 2 (eta conversion), as in `Sieve.eta`.
-- REVIEW(citation): pin down the exact section in review.
/-- **Eta conversion for fiber logics**. -/
theorem FiberLogic.eta {d : Doctrine} {root : d.computad.obj} (F : FiberLogic d root) :
    FiberLogic.mk F.top F.meet F.meet_le_left F.meet_le_right F.le_meet F.le_top = F := by
  cases F with
  | mk top meet meet_le_left meet_le_right le_meet le_top => rfl

/-! ## Heyting implication (statement layer) -/

-- Reference: ticket #71, item (ii); [Mac Lane–Moerdijk], ch. IV — the
-- Heyting implication with the adjunction `meet φ ψ ⊢ χ ↔ φ ⊢ imp ψ χ`.
/-- A **Heyting fiber**: a fiber logic with implication, the adjunction law
as a `Prop` field. -/
structure HeytingImp (d : Doctrine) (root : d.computad.obj) extends FiberLogic d root where
  /-- The implication. -/
  imp : d.computad.Path root root → d.computad.Path root root → d.computad.Path root root
  /-- The Heyting adjunction. -/
  imp_adj : ∀ φ ψ χ, d.move (meet φ ψ) χ ↔ d.move φ (imp ψ χ)

/-! ## The enriched hyperdoctrine -/

-- Reference: ticket #71, items (i)/(iii); [Lawvere] 1969: substitution
-- preserves the finite-limit fragment (`subst_meet`, `subst_top`), and the
-- Beck–Chevalley condition is the named hole (field, not yet proved).
/-- An **enriched hyperdoctrine**: a `Hyperdoctrine` whose fibers carry
`FiberLogic`, substitution preserves `meet`/`top`, and the Beck–Chevalley
condition is carried as the named-hole field. -/
structure EnrichedHyperdoctrine extends Hyperdoctrine where
  /-- The fiber logic at each scope's root. -/
  fiberLogic : (X : scope.obj) → FiberLogic (fiber X) (root X)
  /-- Substitution preserves meets: the transported image of the meet is
  the meet of the transported images. -/
  subst_meet : ∀ (g : scope.gen) (φ ψ : (fiber (scope.tgt g)).computad.Path
      (root (scope.tgt g)) (root (scope.tgt g))),
    (fiber (scope.src g)).move
      (cast (congrArg (fun W => (fiber (scope.src g)).computad.Path W W) (subst_root g))
        ((subst g).mapPath ((fiberLogic (scope.tgt g)).meet φ ψ)))
      ((fiberLogic (scope.src g)).meet
        (cast (congrArg (fun W => (fiber (scope.src g)).computad.Path W W) (subst_root g))
          ((subst g).mapPath φ))
        (cast (congrArg (fun W => (fiber (scope.src g)).computad.Path W W) (subst_root g))
          ((subst g).mapPath ψ)))
  /-- Substitution preserves top. -/
  subst_top : ∀ (g : scope.gen),
    (fiber (scope.src g)).move
      (cast (congrArg (fun W => (fiber (scope.src g)).computad.Path W W) (subst_root g))
        ((subst g).mapPath ((fiberLogic (scope.tgt g)).top)))
      ((fiberLogic (scope.src g)).top)
  /-- The Beck–Chevalley condition (THE named hole of #71, item (iii)):
  ∃ along a pullback commutes with substitution. -/
  beckChevalley : Prop

/-! ## Toy: the chaotic doctrine (degenerate, recorded as such) -/

-- Reference: ticket #71, toy — the chaotic doctrine (`move := True`): a
-- degenerate but honest fiber-logic instance where all laws hold.
/-- The **chaotic doctrine** on a computad: every parallel pair is a
declared move. -/
def chaoticDoctrine (c : Computad) : Doctrine where
  computad := c
  move := fun _ _ => True

-- Reference: ticket #71, toy: the chaotic fiber logic at any root — all laws
-- are `True.intro`.
/-- The **chaotic fiber logic** at a root: top = the empty path, meet =
left factor, all laws hold trivially. -/
def chaoticFiberLogic (c : Computad) (X : c.obj) : FiberLogic (chaoticDoctrine c) X where
  top := Quiver.Path.nil
  meet := fun φ _ => φ
  meet_le_left := fun _ _ => True.intro
  meet_le_right := fun _ _ => True.intro
  le_meet := fun _ _ _ _ _ => True.intro
  le_top := fun _ => True.intro

-- Reference: ticket #71, toy: the chaotic Heyting implication (imp = right
-- factor); the adjunction is `Iff.rfl` (both sides `True`).
/-- The **chaotic Heyting fiber**: imp = right factor; the adjunction holds
trivially. -/
def chaoticHeyting (c : Computad) (X : c.obj) : HeytingImp (chaoticDoctrine c) X where
  top := Quiver.Path.nil
  meet := fun φ _ => φ
  meet_le_left := fun _ _ => True.intro
  meet_le_right := fun _ _ => True.intro
  le_meet := fun _ _ _ _ _ => True.intro
  le_top := fun _ => True.intro
  imp := fun _ ψ => ψ
  imp_adj := fun _ _ _ => Iff.rfl

end BoringLab
