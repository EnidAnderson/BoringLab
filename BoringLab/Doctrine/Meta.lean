/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import BoringLab.Doctrine.Geometric
import BoringLab.Doctrine.Morph
import BoringLab.Doctrine.Semicat

/-!
# LAB META.0: the doctrine of doctrines (the reprogrammable Lisp), 1-skeleton

Ticket #72 (LAB META.0, PREP-first — the reading and the 1-skeleton land
here; the full 2-layer is the goal-carrier). The reading, made precise
against what is landed: a doctrine already supplies a Lisp — computad
generators = special forms, declared moves = the macro table (the LISP.0
framing of #68), doctrine-localization = the quotient semantics
(`misereSequent_inverted` inverts exactly what the macro table declares).
The REPROGRAMMABLE Lisp is the 2-layer: a syntax for defining doctrines is
a doctrine OF doctrines:

* objects: doctrines (`Doctrine`);
* 1-cells: `DoctrineMorph` — a polygraph morphism of the underlying
  computads (`Computad.Morph`, landed) preserving declared moves
  (`preservesMoves` — the `subst_move` pattern of the hyperdoctrine);
* 2-cells: `PresentationRewrite` — a rewrite of a presentation: a lax
  naturality condition between two doctrine morphisms over the declared
  moves (the named hole for the full 2-cell structure);
* the connection, proved: the scope hyperdoctrine's `subst` IS a doctrine
  morphism between fibers (`Hyperdoctrine.substMorph`).

Hygiene = freshness of scope-generator substitution (variable capture =
an owned-vs-unowned hole violation): the game-side instance is GAL.0 #16
(the deck semantics), the syntactic instance is `BoringLab.Lisp.Hygiene`.
Same structure as cdh/Nisnevich descent (#69).

## References
* [Mimram] S. Mimram, arXiv:2312.00429, LMCS 21(3) (2025) — polygraphs and
  their morphisms; higher-dimensional rewriting.
* [Burroni] A. Burroni, Theoret. Comput. Sci. 126 (1994), 257–291.
* [Gabriel–Zisman] P. Gabriel, M. Zisman, LNM 1, Springer, 1967, Chapter I.
* Program register: BoringLab ticket #72 (LAB META.0), user steering
  2026-11-02; depends on #3 (A2.0), #14 (GL.0), #68 (LISP.0), #16 (GAL.0).
-/

universe u

namespace BoringLab

/-! ## 1-cells: doctrine morphisms -/

-- Reference: ticket #72 — a 1-cell of the doctrine-of-doctrines: a
-- polygraph morphism preserving declared moves (the `subst_move` shape).
/-- A **morphism of doctrines**: a computad morphism whose path transport
preserves declared moves. -/
structure DoctrineMorph (d d' : Doctrine.{u}) where
  /-- The underlying polygraph morphism. -/
  morph : Computad.Morph d.computad d'.computad
  /-- Path transport preserves declared moves. -/
  preservesMoves : ∀ {X Y : d.computad.obj} (p q : d.computad.Path X Y),
    d.move p q → d'.move (morph.mapPath p) (morph.mapPath q)

-- Reference: ticket #72 (identity 1-cell); preservation via
-- `Computad.Morph.mapPath_id` transports.
/-- The **identity doctrine morphism**. -/
def DoctrineMorph.id (d : Doctrine.{u}) : DoctrineMorph d d where
  morph := Computad.Morph.id d.computad
  preservesMoves := fun {_X _Y} p q h =>
    Eq.subst (motive := fun r => d.move r (Computad.Morph.mapPath (Computad.Morph.id d.computad) q))
      (Computad.Morph.mapPath_id p).symm
      (Eq.subst (motive := fun s => d.move p s) (Computad.Morph.mapPath_id q).symm h)

-- Reference: ticket #72 (composition of 1-cells): the polygraph morphisms
-- compose (`Computad.Morph.comp`), preservation chains.
/-- **Composition of doctrine morphisms**. -/
def DoctrineMorph.comp {d d' d'' : Doctrine.{u}} (f : DoctrineMorph d d')
    (g : DoctrineMorph d' d'') : DoctrineMorph d d'' where
  morph := f.morph.comp g.morph
  preservesMoves := fun {_X _Y} p q h =>
    Eq.subst (motive := fun r => d''.move r ((f.morph.comp g.morph).mapPath q))
      (Computad.Morph.mapPath_comp_morph f.morph g.morph p).symm
      (Eq.subst (motive := fun s => d''.move (g.morph.mapPath (f.morph.mapPath p)) s)
        (Computad.Morph.mapPath_comp_morph f.morph g.morph q).symm
        (g.preservesMoves (f.morph.mapPath p) (f.morph.mapPath q) (f.preservesMoves p q h)))

-- Reference: proof irrelevance on the `preservesMoves` field;
-- `cases` + `Eq.subst` along the morph equality.
/-- **Extensionality for doctrine morphisms**: equal underlying computad
morphisms give equal doctrine morphisms (the preservation field is a
proof). -/
theorem DoctrineMorph.ext {d d' : Doctrine.{u}} {f g : DoctrineMorph d d'}
    (h : f.morph = g.morph) : f = g := by
  cases f with | mk m1 p1 =>
  cases g with | mk m2 p2 =>
  subst h
  exact rfl

-- Reference: ticket #72 — associativity of 1-cell composition:
-- `Computad.Morph.comp_assoc` on the underlying polygraph morphisms +
-- `DoctrineMorph.ext` (the preservation fields are proofs).
/-- Associativity of doctrine-morphism composition. -/
theorem DoctrineMorph.comp_assoc {d d' d'' d''' : Doctrine.{u}}
    (f : DoctrineMorph d d') (g : DoctrineMorph d' d'')
    (h : DoctrineMorph d'' d''') :
    DoctrineMorph.comp (DoctrineMorph.comp f g) h =
      DoctrineMorph.comp f (DoctrineMorph.comp g h) :=
  DoctrineMorph.ext (Computad.Morph.comp_assoc f.morph g.morph h.morph)

/-! ## 2-cells: presentation rewrites -/

-- Reference: ticket #72 — a 2-cell is a rewrite of a presentation: a lax
-- naturality between two doctrine morphisms over the declared moves (the
-- macro-expansion at the meta level).
/-- A **presentation rewrite** between doctrine morphisms `f, g : d → d'`:
every declared move of `d`, transported by `f`, is declared-moved to its
`g`-image in `d'`. -/
structure PresentationRewrite {d d' : Doctrine.{u}} (f g : DoctrineMorph d d') where
  /-- The two morphisms agree on objects (so the transported paths are
  parallel). -/
  sameObj : f.morph.objMap = g.morph.objMap
  /-- The lax naturality over declared moves. -/
  laxNat : ∀ {X Y : d.computad.obj} (p q : d.computad.Path X Y),
    d.move p q → d'.move (f.morph.mapPath p)
      (cast (congrArg (fun W => d'.computad.Path (f.morph.objMap X) W) (congrFun sameObj Y).symm)
        (cast (congrArg (fun W => d'.computad.Path W (g.morph.objMap Y)) (congrFun sameObj X).symm)
          (g.morph.mapPath q)))

/-! ## The connection: the hyperdoctrine's substitution is a doctrine morphism -/

-- Reference: ticket #72 — the scope hyperdoctrine's `subst` rewrites whole
-- fibers along generators: it IS a doctrine morphism between fibers.
/-- The substitution along a scope generator, as a doctrine morphism
`fiber (tgt g) → fiber (src g)`. -/
def Hyperdoctrine.substMorph {H : Hyperdoctrine.{u}} (g : H.scope.gen) :
    DoctrineMorph (H.fiber (H.scope.tgt g)) (H.fiber (H.scope.src g)) where
  morph := H.subst g
  preservesMoves := H.subst_move g

end BoringLab
