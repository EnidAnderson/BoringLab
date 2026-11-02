/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import BoringLab.Doctrine.Computad

/-!
# Morphisms of computads (polygraph morphisms)

The morphism level of the polygraph substrate, built for the GL line
(`EnidAnderson/BoringLab#14`, LAB TREE GL.0): a morphism of computads maps
ports by a monoid homomorphism, objects to objects, and generators to
hom-edges — source/target preservation is carried by the hom-type itself —
with the port-word preservation laws as explicit `Prop` fields (STYLE §2.3:
explicit data, never instance-chosen). A morphism transports paths
(`Computad.Morph.mapPath`) compatibly with composition
(`Computad.Morph.mapPath_comp`) and with port words
(`Computad.Morph.mapPath_leftWord`), and morphisms compose
(`Computad.Morph.comp`) with identity (`Computad.Morph.id`) — the functorial
shadow of substitution along scope generators in the hyperdoctrine reading.

Every declaration in this module is computable.

## References
* [Mimram] S. Mimram, *Polygraphs: from rewriting to higher categories*,
  arXiv:2312.00429, Logical Methods in Computer Science 21(3) (2025),
  7:1–7:47 — §3 (morphisms of polygraphs: object and generator maps
  preserving sources/targets).
* [Burroni] A. Burroni, *Higher-dimensional word problems with applications to
  equational logic*, Theoret. Comput. Sci. 126 (1994), 257–291.
* [Street] R. Street, *The algebra of oriented simplexes*, J. Pure Appl.
  Algebra 49 (1987), no. 3, 283–335 — §1 (computads; morphisms of computads).
* [Mac Lane] S. Mac Lane, *Categories for the Working Mathematician*, 2nd ed.,
  Springer, 1998, ch. VII, §1 (monoid homomorphisms; word products).
-/

universe u

namespace BoringLab

-- Reference: [Mimram], LMCS 21(3) (2025), §3 (a morphism of 1-polygraphs);
-- [Street], §1 (morphisms of computads); [Burroni].
-- REVIEW(citation): pin the exact definition numbers in review.
/-- A **morphism of computads** (polygraph morphism) `c → d`: a port map that
is a monoid homomorphism (two `Prop` fields), an object map, and a generator
map valued in hom-types — the source/target preservation is carried by the
hom-type `d.Hom (objMap X) (objMap Y)` itself — plus the left/right
port-word preservation laws as `Prop` fields. All data is explicit
(STYLE §2.3). -/
structure Computad.Morph (c d : Computad.{u}) where
  /-- The port map. -/
  portMap : c.port → d.port
  /-- The port map preserves the monoid product. -/
  portMap_mul : ∀ (a b : c.port), portMap (c.portMul a b) = d.portMul (portMap a) (portMap b)
  /-- The port map preserves the unit. -/
  portMap_one : portMap c.portOne = d.portOne
  /-- The object map (0-cells). -/
  objMap : c.obj → d.obj
  /-- The generator map (1-cells), valued in hom-types. -/
  genMap : ∀ {X Y : c.obj}, c.Hom X Y → d.Hom (objMap X) (objMap Y)
  /-- Left port words of generators are preserved. -/
  leftWord_map : ∀ {X Y : c.obj} (e : c.Hom X Y),
    d.pathLeftWord (d.toPath (genMap e)) = portMap (c.pathLeftWord (c.toPath e))
  /-- Right port words of generators are preserved. -/
  rightWord_map : ∀ {X Y : c.obj} (e : c.Hom X Y),
    d.pathRightWord (d.toPath (genMap e)) = portMap (c.pathRightWord (c.toPath e))

-- Reference: [Barendregt], ch. 2 (eta conversion), as in `Computad.eta`.
-- REVIEW(citation): pin down the exact section in review.
/-- **Eta conversion for computad morphisms**: a morphism equals the morphism
assembled from its components. -/
theorem Computad.Morph.eta {c d : Computad.{u}} (F : Computad.Morph c d) :
    Computad.Morph.mk F.portMap F.portMap_mul F.portMap_one F.objMap F.genMap
      F.leftWord_map F.rightWord_map = F := by
  cases F with
  | mk portMap portMap_mul portMap_one objMap genMap leftWord_map rightWord_map => rfl

-- Reference: [Mimram], LMCS 21(3) (2025), §3 (a morphism extends to paths);
-- [Street], §1 (the induced map on free categories/paths).
-- REVIEW(citation): pin the exact statements in review.
/-- The **path transport** of a computad morphism: generators map via
`genMap`, paths by recursion. -/
def Computad.Morph.mapPath {c d : Computad.{u}} (F : Computad.Morph c d)
    {X Y : c.obj} (p : c.Path X Y) : d.Path (F.objMap X) (F.objMap Y) :=
  match p with
  | .nil => .nil
  | .cons q e => (F.mapPath q).cons (F.genMap e)

-- Reference: computation step of `mapPath`; `rfl` only in this primitive
-- definitional lemma.
/-- Path transport of the empty path is the empty path. -/
theorem Computad.Morph.mapPath_nil {c d : Computad.{u}} (F : Computad.Morph c d)
    {X : c.obj} : F.mapPath (Quiver.Path.nil : c.Path X X) = Quiver.Path.nil := rfl

-- Reference: computation step of `mapPath`; `rfl` only in this primitive
-- definitional lemma.
/-- Path transport of a one-edge extension. -/
theorem Computad.Morph.mapPath_cons {c d : Computad.{u}} (F : Computad.Morph c d)
    {X Y Z : c.obj} (p : c.Path X Y) (e : c.Hom Y Z) :
    F.mapPath (p.cons e) = (F.mapPath p).cons (F.genMap e) := rfl

-- Reference: [Mimram], LMCS 21(3) (2025), §3 (functoriality on paths);
-- [Street], §1; proof by induction on the second path, using that
-- `Quiver.Path.comp_cons` and `comp_nil` are definitional (`rfl`).
-- REVIEW(citation): pin the exact statements in review.
/-- **Path transport is compatible with composition**: `mapPath` is a map of
path structures. -/
theorem Computad.Morph.mapPath_comp {c d : Computad.{u}} (F : Computad.Morph c d)
    {X Y Z : c.obj} (p : c.Path X Y) (q : c.Path Y Z) :
    F.mapPath (p.comp q) = (F.mapPath p).comp (F.mapPath q) := by
  induction q with
  | nil => rfl
  | cons q e ih => exact congrArg (fun r => Quiver.Path.cons r (F.genMap e)) ih

-- Reference: [Mac Lane], ch. VII, §1 (monoid homomorphisms preserve word
-- products); [Burroni] (additive typing preserved by morphisms); induction
-- on the path via `portWord_append` and the `portMap` laws.
-- REVIEW(citation): pin the exact statements in review.
/-- **Port words are preserved by path transport**: the left port word of the
transported path is the port image of the original left port word. -/
theorem Computad.Morph.mapPath_leftWord {c d : Computad.{u}} (F : Computad.Morph c d)
    {X Y : c.obj} (p : c.Path X Y) :
    d.pathLeftWord (F.mapPath p) = F.portMap (c.pathLeftWord p) := by
  induction p with
  | nil => exact F.portMap_one.symm
  | cons q e ih =>
      have h1 : d.pathLeftWord ((F.mapPath q).cons (F.genMap e)) =
          d.portMul (d.pathLeftWord (F.mapPath q))
            (d.pathLeftWord (d.toPath (F.genMap e))) :=
        d.portWord_append (d.pathLeftPorts (F.mapPath q)) (d.leftPorts (F.genMap e).1)
      have h2 : F.portMap (c.pathLeftWord (q.cons e)) =
          d.portMul (F.portMap (c.pathLeftWord q))
            (F.portMap (c.pathLeftWord (c.toPath e))) :=
        (congrArg F.portMap (c.portWord_append (c.pathLeftPorts q) (c.leftPorts e.1))).trans
          (F.portMap_mul (c.pathLeftWord q) (c.pathLeftWord (c.toPath e)))
      exact h1.trans
        ((congrArg (fun x => d.portMul x (d.pathLeftWord (d.toPath (F.genMap e)))) ih).trans
          ((congrArg (fun y => d.portMul (F.portMap (c.pathLeftWord q)) y)
            (F.leftWord_map e)).trans h2.symm))

-- Reference: [Mac Lane], ch. VII, §1; as `mapPath_leftWord` on the right
-- side.
-- REVIEW(citation): as on `mapPath_leftWord`.
/-- **Right port words are preserved by path transport**. -/
theorem Computad.Morph.mapPath_rightWord {c d : Computad.{u}} (F : Computad.Morph c d)
    {X Y : c.obj} (p : c.Path X Y) :
    d.pathRightWord (F.mapPath p) = F.portMap (c.pathRightWord p) := by
  induction p with
  | nil => exact F.portMap_one.symm
  | cons q e ih =>
      have h1 : d.pathRightWord ((F.mapPath q).cons (F.genMap e)) =
          d.portMul (d.pathRightWord (F.mapPath q))
            (d.pathRightWord (d.toPath (F.genMap e))) :=
        d.portWord_append (d.pathRightPorts (F.mapPath q)) (d.rightPorts (F.genMap e).1)
      have h2 : F.portMap (c.pathRightWord (q.cons e)) =
          d.portMul (F.portMap (c.pathRightWord q))
            (F.portMap (c.pathRightWord (c.toPath e))) :=
        (congrArg F.portMap (c.portWord_append (c.pathRightPorts q) (c.rightPorts e.1))).trans
          (F.portMap_mul (c.pathRightWord q) (c.pathRightWord (c.toPath e)))
      exact h1.trans
        ((congrArg (fun x => d.portMul x (d.pathRightWord (d.toPath (F.genMap e)))) ih).trans
          ((congrArg (fun y => d.portMul (F.portMap (c.pathRightWord q)) y)
            (F.rightWord_map e)).trans h2.symm))

-- Reference: [Mimram], LMCS 21(3) (2025), §3 (the identity morphism);
-- [Street], §1.
-- REVIEW(citation): pin the exact statements in review.
/-- The **identity morphism** of a computad. -/
def Computad.Morph.id (c : Computad.{u}) : Computad.Morph c c where
  portMap := fun a => a
  portMap_mul := fun _ _ => rfl
  portMap_one := rfl
  objMap := fun X => X
  genMap := fun e => e
  leftWord_map := fun _ => rfl
  rightWord_map := fun _ => rfl

-- Reference: [Mimram], LMCS 21(3) (2025), §3 (composition of polygraph
-- morphisms); [Street], §1.
-- REVIEW(citation): pin the exact statements in review.
/-- **Composition of computad morphisms**. -/
def Computad.Morph.comp {c d e : Computad.{u}} (F : Computad.Morph c d)
    (G : Computad.Morph d e) : Computad.Morph c e where
  portMap := fun a => G.portMap (F.portMap a)
  portMap_mul := fun a b =>
    (congrArg G.portMap (F.portMap_mul a b)).trans (G.portMap_mul (F.portMap a) (F.portMap b))
  portMap_one := (congrArg G.portMap F.portMap_one).trans G.portMap_one
  objMap := fun X => G.objMap (F.objMap X)
  genMap := fun h => G.genMap (F.genMap h)
  leftWord_map := fun h =>
    (G.leftWord_map (F.genMap h)).trans (congrArg G.portMap (F.leftWord_map h))
  rightWord_map := fun h =>
    (G.rightWord_map (F.genMap h)).trans (congrArg G.portMap (F.rightWord_map h))

-- Reference: [Mimram], LMCS 21(3) (2025), §3 (the identity is neutral);
-- induction on the path.
-- REVIEW(citation): pin the exact statement in review.
/-- Path transport along the identity morphism is the identity. -/
theorem Computad.Morph.mapPath_id {c : Computad.{u}} {X Y : c.obj} (p : c.Path X Y) :
    (Computad.Morph.id c).mapPath p = p := by
  induction p with
  | nil => rfl
  | cons q e ih => exact congrArg (fun r => Quiver.Path.cons r e) ih

-- Reference: [Mimram], LMCS 21(3) (2025), §3 (composition commutes with path
-- transport); induction on the path.
-- REVIEW(citation): pin the exact statement in review.
/-- Path transport along a composite morphism is the composite of the path
transports. -/
theorem Computad.Morph.mapPath_comp_morph {c d e : Computad.{u}}
    (F : Computad.Morph c d) (G : Computad.Morph d e) {X Y : c.obj} (p : c.Path X Y) :
    (F.comp G).mapPath p = G.mapPath (F.mapPath p) := by
  induction p with
  | nil => rfl
  | cons q e ih =>
      exact congrArg (fun r => Quiver.Path.cons r (G.genMap (F.genMap e))) ih

end BoringLab
