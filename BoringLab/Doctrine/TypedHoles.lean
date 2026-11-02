/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import BoringLab.Doctrine.Computad

/-!
# Typed holes and plugging in a computad

Lab ticket (BoringLab): typed holes library, on top of `Doctrine/Computad.lean`
(A2.0 part 1). A **typed hole** at an object `Y` is a junction: a path `pre`
into `Y` and a path `post` out of `Y`. **Plugging** the hole is composition
`pre.comp post`; the hole is **well-typed** exactly when the right port word of
`pre` matches the left port word of `post` — port-word matching is the typing
discipline of plugging. This is the polygraph analogue of one-hole contexts /
the derivative of a type (the "derivative" connection is a labeled bet, see
below).

## References
* [Burroni] TCS 126 (1994) (polygraphs); [Mimram] arXiv:2312.00429, Def. 3.5
  (composition of cells); [Street] LNM (computads).
* [Abbott–Altenkirch–Ghani] "Categories of containers" / "Derivatives of
  types" (one-hole contexts) — the derivative connection is a bet, labeled.
* mathlib pin v4.35.0-rc3: `Quiver.Path.comp`.
-/

namespace BoringLab

universe u

variable {c : Computad.{u}}

-- Reference: [Mimram] Def. 3.5 (a cell boundary: source path and target
-- path); [Burroni] (polygraph cells have source/target paths).
/-- A **typed hole** at object `Y` of a computad: a path `pre` into `Y` and a
path `post` out of `Y` (the two sides of the hole). -/
structure TypedHole (c : Computad.{u}) (Y : c.obj) where
  /-- The source object of the hole. -/
  X : c.obj
  /-- The target object of the hole. -/
  Z : c.obj
  /-- The path into the hole. -/
  pre : Quiver.Path X Y
  /-- The path out of the hole. -/
  post : Quiver.Path Y Z

-- Reference: [Barendregt] ch. 2 (eta).
/-- Eta conversion for typed holes. -/
theorem TypedHole.eta {c : Computad.{u}} {Y : c.obj} (h : TypedHole c Y) :
    TypedHole.mk h.X h.Z h.pre h.post = h := by
  cases h with
  | mk X Z pre post => rfl

-- Reference: [Mimram] Def. 3.5 (plugging = composition of the two sides).
/-- **Plugging** a typed hole: the composite path `pre.comp post`. -/
def TypedHole.plug {c : Computad.{u}} {Y : c.obj} (h : TypedHole c Y) :
    Quiver.Path h.X h.Z :=
  h.pre.comp h.post

-- Reference: [Burroni]/[Mimram] (typing of a composite); Computad's
-- `pathLeftWord_comp` / `pathRightWord_comp`.
/-- The left port word of a plug is the product of the two sides' left port
words (proved). -/
theorem TypedHole.pathLeftWord_plug {c : Computad.{u}} {Y : c.obj} (h : TypedHole c Y) :
    c.pathLeftWord h.plug = c.portMul (c.pathLeftWord h.pre) (c.pathLeftWord h.post) :=
  c.pathLeftWord_comp h.pre h.post

-- Reference: as above, right side.
/-- The right port word of a plug is the product of the two sides' right port
words (proved). -/
theorem TypedHole.pathRightWord_plug {c : Computad.{u}} {Y : c.obj} (h : TypedHole c Y) :
    c.pathRightWord h.plug = c.portMul (c.pathRightWord h.pre) (c.pathRightWord h.post) :=
  c.pathRightWord_comp h.pre h.post

-- Reference: [Burroni] (the junction typing of a plugged cell is the matching
-- of the boundary port words).
/-- A typed hole is **well-typed** when the right port word of `pre` matches
the left port word of `post` — i.e. the ports line up at the junction. -/
def TypedHole.wellTyped {c : Computad.{u}} {Y : c.obj} (h : TypedHole c Y) : Prop :=
  c.pathRightWord h.pre = c.pathLeftWord h.post

-- Reference: [Abbott–Altenkirch–Ghani] (derivatives of types = one-hole
-- contexts). BET (labeled, not a theorem): for the underlying quiver of a
-- computad, the one-hole contexts at `Y` are `Σ X, Path X Y`, and plugging is
-- the derivative's action.
/-- The **one-hole contexts** at `Y`: paths into `Y` (the derivative-shaped
object; connection to derivatives of types is a labeled bet, see module doc). -/
def Computad.oneHoleContexts (c : Computad.{u}) (Y : c.obj) : Type u :=
  Σ X : c.obj, Quiver.Path X Y

end BoringLab
