/-
Copyright (c) 2026 Enid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Enid
-/
import Mathlib.Combinatorics.Quiver.Basic
import Mathlib.Combinatorics.Quiver.Path

/-!
# Computads: port-typed generators (LAB A2.0, part 1)

This module implements part 1 of the scope contract of
`EnidAnderson/BoringLab#3`: a `Computad` structure — a type of objects and a
type of generators, each generator carrying an explicit source and target
object together with a *port typing*: a list of left ports and a list of
right ports over a fixed port universe, the port monoid being carried as
explicit structure data. Composition typing is additive: the ports of a
composite path are the concatenation of the ports of its factors
(`Computad.pathLeftPorts_comp`, `Computad.pathRightPorts_comp`,
`Computad.portWord_append`) — the PROP-shaped discipline.

The quiver/path substrate is mathlib's own (`Quiver`, `Quiver.Path`), used at
the pin `v4.35.0-rc3`; every declaration in this module is computable.

## References
* [Burroni] A. Burroni, *Higher-dimensional word problems with applications to
  equational logic*, Theoret. Comput. Sci. 126 (1994), 257–291 — polygraphs
  (computads) in rewriting theory.
* [Mimram] S. Mimram, *Polygraphs: from rewriting to higher categories*,
  arXiv:2312.00429, Logical Methods in Computer Science 21(3) (2025),
  7:1–7:47 — Definitions 3.1 (1-polygraph) and 3.5 (2-polygraph).
* [Street] R. Street, *The algebra of oriented simplexes*, J. Pure Appl.
  Algebra 49 (1987), no. 3, 283–335 — computads and free higher categories.
* [Mac Lane] S. Mac Lane, *Categories for the Working Mathematician*, 2nd ed.,
  Springer, 1998.
-/

universe u

namespace BoringLab

-- Reference: [Burroni], the definition of an n-polygraph;
-- [Mimram], LMCS 21(3) (2025), Definition 3.1 (an ars / 1-polygraph);
-- [Street], §1 (computads).
-- REVIEW(citation): pin the exact sections of [Burroni] and [Street] in review.
/-- A **computad** (polygraph) of depth 1 with port typing: a type `obj` of
objects and a type `gen` of generators; each generator `g` has an explicit
source `src g` and target `tgt g` in `obj` and carries a list of left ports
`leftPorts g` and a list of right ports `rightPorts g` over the port universe
`port`. The port monoid is carried as *explicit structure data* (`portMul`,
`portOne` and the three monoid laws) rather than as a typeclass instance, per
the computability checklist (STYLE §2.3): data parameters are taken explicitly,
never instance-chosen. -/
structure Computad where
  /-- The port universe. -/
  port : Type u
  /-- The monoid product on ports. -/
  portMul : port → port → port
  /-- The unit port. -/
  portOne : port
  /-- Associativity of the port product. -/
  portMul_assoc : ∀ (a b c : port), portMul a (portMul b c) = portMul (portMul a b) c
  /-- Left unit law of the port monoid. -/
  portMul_left_one : ∀ (a : port), portMul portOne a = a
  /-- Right unit law of the port monoid. -/
  portMul_right_one : ∀ (a : port), portMul a portOne = a
  /-- The type of objects (0-cells). -/
  obj : Type u
  /-- The type of generators (1-cells). -/
  gen : Type u
  /-- The source object of a generator. -/
  src : gen → obj
  /-- The target object of a generator. -/
  tgt : gen → obj
  /-- The left ports of a generator, as a list over the port universe. -/
  leftPorts : gen → List port
  /-- The right ports of a generator, as a list over the port universe. -/
  rightPorts : gen → List port

-- Reference: [Barendregt], Chapter 2 (eta conversion).
-- REVIEW(citation): pin down the exact section in review.
/-- **Eta conversion for computads**: every computad is equal to the computad
assembled from its components. -/
theorem Computad.eta (c : Computad) :
    Computad.mk c.port c.portMul c.portOne c.portMul_assoc c.portMul_left_one
      c.portMul_right_one c.obj c.gen c.src c.tgt c.leftPorts c.rightPorts = c := by
  cases c with
  | mk port portMul portOne portMul_assoc portMul_left_one portMul_right_one
      obj gen src tgt leftPorts rightPorts => rfl

-- Reference: [Mimram], LMCS 21(3) (2025), Definition 3.1 (the underlying graph
-- of a 1-polygraph). REVIEW(citation): pin the exact definition number.
/-- The hom-type of the quiver underlying a computad: an edge from `X` to `Y`
is a generator with source `X` and target `Y`. -/
def Computad.Hom (c : Computad) (X Y : c.obj) : Type u :=
  {g : c.gen // c.src g = X ∧ c.tgt g = Y}

-- Reference: [Mimram], LMCS 21(3) (2025), Definition 3.1 (the underlying graph
-- of a 1-polygraph). REVIEW(citation): pin the exact definition number.
/-- The quiver underlying a computad. -/
instance Computad.instQuiver (c : Computad.{u}) : Quiver.{u, u} c.obj where
  Hom X Y := c.Hom X Y

-- Reference: [Street], §1 (an arrow of the underlying graph as a path of
-- length one). REVIEW(citation): pin the exact section in review.
/-- A generator edge viewed as a path of length one. -/
def Computad.toPath (c : Computad) {X Y : c.obj} (g : c.Hom X Y) : Quiver.Path X Y :=
  Quiver.Hom.toPath g

-- Reference: [Street], §1 (paths in the underlying graph).
-- REVIEW(citation): pin the exact section in review.
/-- A path in the underlying quiver of a computad, pinned at the computad's own
universe. -/
def Computad.Path (c : Computad.{u}) (X Y : c.obj) : Type u := Quiver.Path X Y

-- Reference: [Mac Lane], Chapter VII, §1 (monoids; the word/product of a list
-- in a monoid). REVIEW(citation): pin the exact section in review.
/-- The **port word** of a list of ports: the product of the list in the port
monoid, taken as explicit data. -/
def Computad.portWord (c : Computad) : List c.port → c.port
  | [] => c.portOne
  | a :: l => c.portMul a (c.portWord l)

-- Reference: [Mac Lane], Chapter VII, §1 (associativity and unit laws of a
-- monoid make the word product additive over concatenation).
-- REVIEW(citation): pin the exact statement in review.
/-- **Additivity of the port word**: the port word of a concatenation is the
product of the port words. -/
theorem Computad.portWord_append (c : Computad) (ps qs : List c.port) :
    c.portWord (ps ++ qs) = c.portMul (c.portWord ps) (c.portWord qs) := by
  induction ps with
  | nil => exact (c.portMul_left_one (c.portWord qs)).symm
  | cons a ps ih =>
      change c.portMul a (c.portWord (ps ++ qs)) =
        c.portMul (c.portMul a (c.portWord ps)) (c.portWord qs)
      rw [ih]
      exact c.portMul_assoc a (c.portWord ps) (c.portWord qs)

-- Reference: [Mimram], LMCS 21(3) (2025), Definition 3.5 (source of a
-- composite cell is the composite of the sources).
-- REVIEW(citation): pin the exact definition number.
/-- The left ports of a path: the concatenation of the left ports of its
edges, from source to target. -/
def Computad.pathLeftPorts (c : Computad) {X Y : c.obj} (p : Quiver.Path X Y) :
    List c.port :=
  match p with
  | .nil => []
  | .cons q e => c.pathLeftPorts q ++ c.leftPorts e.1

-- Reference: [Mimram], LMCS 21(3) (2025), Definition 3.5.
-- REVIEW(citation): pin the exact definition number.
/-- The left ports of the empty path are empty (definitional unfolding). -/
theorem Computad.pathLeftPorts_nil (c : Computad) {X : c.obj} :
    c.pathLeftPorts (Quiver.Path.nil : Quiver.Path X X) = [] := rfl

-- Reference: [Mimram], LMCS 21(3) (2025), Definition 3.5.
-- REVIEW(citation): pin the exact definition number.
/-- The left ports of a one-edge extension are appended at the end
(definitional unfolding). -/
theorem Computad.pathLeftPorts_cons (c : Computad) {X Y Z : c.obj}
    (p : Quiver.Path X Y) (e : Y ⟶ Z) :
    c.pathLeftPorts (p.cons e) = c.pathLeftPorts p ++ c.leftPorts e.1 := rfl

-- Reference: [Mimram], LMCS 21(3) (2025), Definition 3.5 (composition of
-- cells in a polygraph); [Burroni], the additive source/target typing of
-- composites. REVIEW(citation): pin the exact statements in review.
/-- **Additivity of path typing**: the left ports of a composite path are the
concatenation of the left ports of its factors. -/
theorem Computad.pathLeftPorts_comp (c : Computad) {X Y Z : c.obj}
    (p : Quiver.Path X Y) (q : Quiver.Path Y Z) :
    c.pathLeftPorts (p.comp q) = c.pathLeftPorts p ++ c.pathLeftPorts q := by
  induction q with
  | nil => rw [Quiver.Path.comp_nil, Computad.pathLeftPorts_nil, List.append_nil]
  | cons q e ih =>
      rw [Quiver.Path.comp_cons, Computad.pathLeftPorts_cons,
        Computad.pathLeftPorts_cons, ih, List.append_assoc]

-- Reference: [Mac Lane], Chapter VII, §1 (the word in a monoid attached to a
-- list of ports). REVIEW(citation): pin the exact statement in review.
/-- The left port word of a path: the port word of its list of left ports. -/
def Computad.pathLeftWord (c : Computad) {X Y : c.obj} (p : Quiver.Path X Y) : c.port :=
  c.portWord (c.pathLeftPorts p)

-- Reference: [Burroni], additive typing of composites; [Mac Lane], Chapter
-- VII, §1 (additivity of the word product).
-- REVIEW(citation): pin the exact statements in review.
/-- The left port word of a composite path is the product of the left port
words of its factors. -/
theorem Computad.pathLeftWord_comp (c : Computad) {X Y Z : c.obj}
    (p : Quiver.Path X Y) (q : Quiver.Path Y Z) :
    c.pathLeftWord (p.comp q) = c.portMul (c.pathLeftWord p) (c.pathLeftWord q) := by
  change c.portWord (c.pathLeftPorts (p.comp q)) =
    c.portMul (c.portWord (c.pathLeftPorts p)) (c.portWord (c.pathLeftPorts q))
  rw [Computad.pathLeftPorts_comp, Computad.portWord_append]

-- Reference: [Mimram], LMCS 21(3) (2025), Definition 3.5 (target side).
-- REVIEW(citation): pin the exact definition number.
/-- The right ports of a path: the concatenation of the right ports of its
edges, from source to target. -/
def Computad.pathRightPorts (c : Computad) {X Y : c.obj} (p : Quiver.Path X Y) :
    List c.port :=
  match p with
  | .nil => []
  | .cons q e => c.pathRightPorts q ++ c.rightPorts e.1

-- Reference: [Mimram], LMCS 21(3) (2025), Definition 3.5.
-- REVIEW(citation): pin the exact definition number.
/-- The right ports of the empty path are empty (definitional unfolding). -/
theorem Computad.pathRightPorts_nil (c : Computad) {X : c.obj} :
    c.pathRightPorts (Quiver.Path.nil : Quiver.Path X X) = [] := rfl

-- Reference: [Mimram], LMCS 21(3) (2025), Definition 3.5.
-- REVIEW(citation): pin the exact definition number.
/-- The right ports of a one-edge extension are appended at the end
(definitional unfolding). -/
theorem Computad.pathRightPorts_cons (c : Computad) {X Y Z : c.obj}
    (p : Quiver.Path X Y) (e : Y ⟶ Z) :
    c.pathRightPorts (p.cons e) = c.pathRightPorts p ++ c.rightPorts e.1 := rfl

-- Reference: [Mimram], LMCS 21(3) (2025), Definition 3.5 (composition of
-- cells in a polygraph); [Burroni], the additive source/target typing of
-- composites. REVIEW(citation): pin the exact statements in review.
/-- **Additivity of path typing, right side**: the right ports of a composite
path are the concatenation of the right ports of its factors. -/
theorem Computad.pathRightPorts_comp (c : Computad) {X Y Z : c.obj}
    (p : Quiver.Path X Y) (q : Quiver.Path Y Z) :
    c.pathRightPorts (p.comp q) = c.pathRightPorts p ++ c.pathRightPorts q := by
  induction q with
  | nil => rw [Quiver.Path.comp_nil, Computad.pathRightPorts_nil, List.append_nil]
  | cons q e ih =>
      rw [Quiver.Path.comp_cons, Computad.pathRightPorts_cons,
        Computad.pathRightPorts_cons, ih, List.append_assoc]

-- Reference: [Mac Lane], Chapter VII, §1 (the word in a monoid attached to a
-- list of ports). REVIEW(citation): pin the exact statement in review.
/-- The right port word of a path: the port word of its list of right ports. -/
def Computad.pathRightWord (c : Computad) {X Y : c.obj} (p : Quiver.Path X Y) : c.port :=
  c.portWord (c.pathRightPorts p)

-- Reference: [Burroni], additive typing of composites; [Mac Lane], Chapter
-- VII, §1 (additivity of the word product).
-- REVIEW(citation): pin the exact statements in review.
/-- The right port word of a composite path is the product of the right port
words of its factors. -/
theorem Computad.pathRightWord_comp (c : Computad) {X Y Z : c.obj}
    (p : Quiver.Path X Y) (q : Quiver.Path Y Z) :
    c.pathRightWord (p.comp q) = c.portMul (c.pathRightWord p) (c.pathRightWord q) := by
  change c.portWord (c.pathRightPorts (p.comp q)) =
    c.portMul (c.portWord (c.pathRightPorts p)) (c.portWord (c.pathRightPorts q))
  rw [Computad.pathRightPorts_comp, Computad.portWord_append]

end BoringLab
