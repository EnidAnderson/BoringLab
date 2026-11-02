/-
Copyright (c) 2026 Enid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Enid
-/
import BoringLab.Doctrine.Computad
import BoringLab.Games.Basic
import Mathlib.CategoryTheory.Localization.Predicate

/-!
# Doctrines: computads with declared reversible moves, localized (LAB A2.0, part 2)

This module implements part 2 of the scope contract of
`EnidAnderson/BoringLab#3`: a `Doctrine` is a computad together with a
declared set of reversible moves — a relation `move` on parallel paths of the
underlying path category, the 1-categorical shadow of the sub-2-groupoid of
certified reversible moves. The localized category `C[W⁻¹]` is built with
mathlib's in-tree localization machinery at the pin `v4.35.0-rc3`
(`MorphismProperty.Localization`, `MorphismProperty.Q`,
`CategoryTheory.Localization.Construction.wIso` — all names GOLD-verified
against the pin by probe files). The first theorems are
`Doctrine.localization_exists` (the localization exists) and
`Doctrine.declared_move_inversion` (the inversion of a declared move is
explicit data — the isomorphism `wIso` — not a global axiom).

The falsifiable shadow of the issue is stated, not proved: the
Plambeck–Siegel misère quotient is statable as a doctrine
(`misereQuotient`), and its generator paths are inverted in the localization
(`misereQuotient_generator_inverted`).

Scope honesty: at the pin there are no (∞,1)-categories in mathlib, so the
free (∞,1)-category on a computad is out of scope (recorded gap); the
1-categorical shadow developed here is the honest scope.

## References
* [Gabriel–Zisman] P. Gabriel, M. Zisman, *Calculus of Fractions and Homotopy
  Theory*, Lecture Notes in Mathematics 1, Springer-Verlag, 1967, Chapter I
  (the localization `C[W⁻¹]` of a category at a class of morphisms `W`).
* [Plambeck–Siegel] T. E. Plambeck, A. N. Siegel, *Misère quotients for
  impartial games*, arXiv:math/0609825 (2006); supplementary material
  arXiv:0705.2404.
* [Burroni] A. Burroni, *Higher-dimensional word problems with applications to
  equational logic*, Theoret. Comput. Sci. 126 (1994), 257–291.
* [Mimram] S. Mimram, *Polygraphs: from rewriting to higher categories*,
  arXiv:2312.00429, Logical Methods in Computer Science 21(3) (2025),
  7:1–7:47 — Definition 3.5 (2-polygraph: generators plus relations).
-/

universe u

namespace BoringLab

open CategoryTheory

-- Reference: [Mimram], LMCS 21(3) (2025), Definition 3.5 (a 2-polygraph is a
-- 1-polygraph plus a set of relations between parallel paths);
-- [Burroni], rewriting systems as polygraphs.
-- REVIEW(citation): pin the exact definition number in review.
/-- A **doctrine**: a computad together with a declared set of reversible moves,
encoded as a relation `move` on parallel paths of the underlying path
category — the 1-categorical shadow of the sub-2-groupoid of certified
reversible moves. `move p q` says that the parallel paths `p` and `q` are
connected by a declared reversible move. -/
structure Doctrine where
  /-- The underlying computad. -/
  computad : Computad.{u}
  /-- The declared reversible moves, as a relation on parallel paths. -/
  move : ∀ {X Y : computad.obj}, Computad.Path computad X Y → Computad.Path computad X Y → Prop

-- Reference: [Barendregt], Chapter 2 (eta conversion).
-- REVIEW(citation): pin down the exact section in review.
/-- **Eta conversion for doctrines**: every doctrine is equal to the doctrine
assembled from its components. -/
theorem Doctrine.eta (d : Doctrine) :
    Doctrine.mk d.computad d.move = d := by
  cases d with
  | mk computad move => rfl

-- Reference: [Gabriel–Zisman], Chapter I (the class `W` of morphisms to be
-- inverted). REVIEW(citation): pin the exact section in review.
/-- The class of morphisms inverted by the doctrine-localization: the sides of
the declared moves. A morphism `f` of the path category lies in `moveClass d`
iff it is one of the two sides of a declared move of `d`. -/
def Doctrine.moveClass (d : Doctrine) : MorphismProperty (Paths d.computad.obj) :=
  fun {X Y} (f : X ⟶ Y) => ∃ p q, d.move p q ∧ (f = p ∨ f = q)

-- Reference: [Gabriel–Zisman], Chapter I (a morphism in `W` is inverted by
-- the localization). REVIEW(citation): pin the exact section in review.
/-- The left side of a declared move lies in the move class (definitional
expansion). -/
theorem Doctrine.moveClass_left (d : Doctrine) {X Y : d.computad.obj}
    (p q : d.computad.Path X Y) (h : d.move p q) : d.moveClass p :=
  ⟨p, q, h, Or.inl rfl⟩

-- Reference: [Gabriel–Zisman], Chapter I. REVIEW(citation): pin the exact
-- section in review.
/-- The right side of a declared move lies in the move class (definitional
expansion). -/
theorem Doctrine.moveClass_right (d : Doctrine) {X Y : d.computad.obj}
    (p q : d.computad.Path X Y) (h : d.move p q) : d.moveClass q :=
  ⟨p, q, h, Or.inr rfl⟩

-- Reference: [Gabriel–Zisman], Chapter I, §1 (the localized category
-- `C[W⁻¹]` exists); mathlib at pin v4.35.0-rc3:
-- `CategoryTheory.MorphismProperty.Localization`,
-- `CategoryTheory.MorphismProperty.Q`, and the instance
-- `CategoryTheory.Functor.q_isLocalization`.
-- REVIEW(citation): pin the exact section of [Gabriel–Zisman] in review.
/-- **The doctrine-localization exists**: the localization of the path category
of the underlying computad at the declared-move class is a localization of
that category at `moveClass d`. -/
theorem Doctrine.localization_exists (d : Doctrine.{u}) :
    d.moveClass.Q.IsLocalization d.moveClass :=
  inferInstance

-- Reference: [Gabriel–Zisman], Chapter I; mathlib at pin v4.35.0-rc3:
-- `CategoryTheory.MorphismProperty.Q_inverts`.
-- REVIEW(citation): pin the exact section of [Gabriel–Zisman] in review.
/-- The localization functor `Q` inverts the declared-move class. -/
theorem Doctrine.moveClass_Q_inverts (d : Doctrine.{u}) :
    d.moveClass.IsInvertedBy d.moveClass.Q :=
  MorphismProperty.Q_inverts d.moveClass

-- Reference: [Gabriel–Zisman], Chapter I (every `w ∈ W` becomes an
-- isomorphism in `C[W⁻¹]`). REVIEW(citation): pin the exact section.
/-- **Declared-move inversion**: both sides of a declared move become
isomorphisms in the doctrine-localization. -/
theorem Doctrine.declared_move_inverted (d : Doctrine.{u}) {X Y : d.computad.obj}
    (p q : d.computad.Path X Y) (h : d.move p q) :
    IsIso (d.moveClass.Q.map p) ∧ IsIso (d.moveClass.Q.map q) :=
  ⟨MorphismProperty.Q_inverts d.moveClass p (d.moveClass_left p q h),
   MorphismProperty.Q_inverts d.moveClass q (d.moveClass_right p q h)⟩

-- Reference: [Gabriel–Zisman], Chapter I (the inverse of `Q(w)` in `C[W⁻¹]`
-- is constructed explicitly); mathlib at pin v4.35.0-rc3:
-- `CategoryTheory.Localization.Construction.wIso` and `...wInv`.
-- REVIEW(citation): pin the exact section of [Gabriel–Zisman] in review.
/-- **Declared-move inversion is data, not a global axiom**: for a declared
move `p ⇄ q`, the inverse of `Q.map p` in the localization is the explicit
morphism `wInv`, with the two inverse laws as data. -/
theorem Doctrine.declared_move_inversion (d : Doctrine.{u}) {X Y : d.computad.obj}
    (p q : d.computad.Path X Y) (h : d.move p q) :
    ∃ inv : d.moveClass.Q.obj Y ⟶ d.moveClass.Q.obj X,
      d.moveClass.Q.map p ≫ inv = 𝟙 _ ∧ inv ≫ d.moveClass.Q.map p = 𝟙 _ := by
  have hw : d.moveClass p := d.moveClass_left p q h
  exact ⟨Localization.Construction.wInv (W := d.moveClass) p hw,
    (Localization.Construction.wIso (W := d.moveClass) p hw).hom_inv_id,
    (Localization.Construction.wIso (W := d.moveClass) p hw).inv_hom_id⟩

-- Reference: [Plambeck–Siegel], arXiv:math/0609825, §2 (a misère quotient is
-- given by a set of identifications between impartial games).
-- REVIEW(citation): pin the exact section in review.
/-- The computad underlying the Plambeck–Siegel misère-quotient instance:
games are the objects, `r`-related pairs of games are the generators, and the
port universe is trivial (no ports). The relation `r` is the misère
equivalence, taken as an explicit binder. -/
def misereQuotientComputad (r : Game.{u} → Game.{u} → Prop) : Computad.{u+1} where
  port := PUnit
  portMul := fun _ _ => PUnit.unit
  portOne := PUnit.unit
  portMul_assoc := fun _ _ _ => rfl
  portMul_left_one := fun _ => rfl
  portMul_right_one := fun _ => rfl
  obj := Game.{u}
  gen := {p : Game.{u} × Game.{u} // r p.1 p.2}
  src := fun p => p.1.1
  tgt := fun p => p.1.2
  leftPorts := fun _ => []
  rightPorts := fun _ => []

-- Reference: [Plambeck–Siegel], arXiv:math/0609825, §2.
-- REVIEW(citation): pin the exact section in review.
/-- **Falsifiable shadow — the Plambeck–Siegel misère quotient as a doctrine**
(stated, not proved): given the misère-equivalence relation `r` on partizan
games, the associated doctrine has games as objects, the `r`-related pairs as
generators, and declares as reversible moves the pairs of parallel
single-generator paths; its localization inverts exactly the generator paths
arising from `r`-related pairs, i.e. it identifies `r`-related games up to
isomorphism — the 1-categorical shadow of the misère quotient. -/
def misereQuotient (r : Game.{u} → Game.{u} → Prop) : Doctrine.{u+1} where
  computad := misereQuotientComputad r
  move := fun {X Y} p q =>
    (∃ g : (misereQuotientComputad r).Hom X Y, p = (misereQuotientComputad r).toPath g) ∧
    (∃ h : (misereQuotientComputad r).Hom X Y, q = (misereQuotientComputad r).toPath h)

-- Reference: [Plambeck–Siegel], arXiv:math/0609825, §2.
-- REVIEW(citation): pin the exact section in review.
/-- A single-generator path of the misère computad is related to itself by a
declared move. -/
theorem misereQuotient_move_self (r : Game.{u} → Game.{u} → Prop) {X Y : Game.{u}}
    (g : (misereQuotientComputad r).Hom X Y) :
    (misereQuotient r).move ((misereQuotientComputad r).toPath g)
      ((misereQuotientComputad r).toPath g) :=
  ⟨⟨g, rfl⟩, ⟨g, rfl⟩⟩

-- Reference: [Plambeck–Siegel], arXiv:math/0609825, §2; [Gabriel–Zisman],
-- Chapter I (inversion in the localization).
-- REVIEW(citation): pin the exact sections in review.
/-- In the misère-quotient doctrine-localization, every generator path arising
from an `r`-related pair of games is inverted. -/
theorem misereQuotient_generator_inverted (r : Game.{u} → Game.{u} → Prop) {X Y : Game.{u}}
    (g : (misereQuotientComputad r).Hom X Y) :
    IsIso ((misereQuotient r).moveClass.Q.map ((misereQuotientComputad r).toPath g)) :=
  MorphismProperty.Q_inverts (misereQuotient r).moveClass _
    (Doctrine.moveClass_left (misereQuotient r) _ _ (misereQuotient_move_self r g))

-- Reference: [Gabriel–Zisman], Chapter I, §1; mathlib at pin v4.35.0-rc3:
-- `CategoryTheory.Functor.q_isLocalization`.
-- REVIEW(citation): pin the exact section of [Gabriel–Zisman] in review.
/-- The localization of the misère-quotient doctrine exists. -/
theorem misereQuotient_localization_exists (r : Game.{u} → Game.{u} → Prop) :
    (misereQuotient r).moveClass.Q.IsLocalization (misereQuotient r).moveClass :=
  inferInstance

end BoringLab
