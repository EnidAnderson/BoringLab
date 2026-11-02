/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import BoringLab.Doctrine.Doctrine
import BoringMath.AlgebraicGeometry.AlgebraicCycle.Pushforward

/-!
# Gysin moves are the rewriting moves

The computad depends on the local doctrine: the **background-independent
identification** we are after is between computad theory (paths + declared
moves, [Mimram] Definitions 3.1/3.5) and **Gysin morphisms** in the category
of (effective) motives. This module anchors the cycle-level half of that
identification:

* the **scheme computad** `SchemeComputad`: objects are schemes (wrapped in
  the structure `SchemeObj` so that the computad's own quiver is the only
  `Quiver` instance on its objects), generators are morphisms, so a
  **path is a composite of morphisms** (`pathMorphism` reads it back);
  ports are trivial;
* a **Gysin move** between parallel paths `p q : X ⟶ Y` is the agreement of
  the Gysin pushforwards on every cycle
  (`gysinMove p q := ∀ D, p_* D = q_* D`), where `p_*` is
  `AlgebraicCycle.pushforward (pathMorphism p)` (Fulton, ch. 1);
* the **composition law** `gysinMove_comp`: Gysin moves respect composition
  of paths, because the pushforward is functorial
  (`AlgebraicCycle.pushforward_comp`, Fulton ch. 1) — this is exactly the
  rewriting axiom "moves compose along paths" ([Mimram], Definition 3.5).

So the Gysin pushforward along a path *is* the rewriting step between the
path and any path with the same pushforward. At the correspondence level the
same composition law is `graphCorrespondence_comp` (the composite of graph
correspondences — computed by Suslin–Voevodsky composition, i.e. by
pushforward, [MVW] Appendix 1A — is the graph of the composite).

The descent half of the master identification — descent through different
computadic contexts is cdh/Nisnevich descent — lives in
`BoringMath.AlgebraicGeometry.Sites` (see the peeling plans there).

## References
* [Fulton] W. Fulton, *Intersection Theory*, 2nd ed., Springer, 1998,
  ch. 1 (pushforward of cycles; functoriality `(f ∘ g)_* = f_* ∘ g_*`).
* [MVW] V. Voevodsky, D. Cisinski, F. Déglise, *Triangulated Categories of
  Mixed Motives*, Springer, 2007, Appendix 1A (composition of finite
  correspondences via pushforward — the Gysin map at cycle level).
* [Mimram] S. Mimram, *Polygraphs: from rewriting to higher categories*,
  arXiv:2312.00429, LMCS 21(3) (2025), Definitions 3.1 and 3.5.
-/

universe u

namespace BoringLab

open CategoryTheory
open AlgebraicGeometry

/-! ## The scheme computad -/

-- Reference: the objects are schemes wrapped in a structure so that the
-- computad's own quiver (`Computad.instQuiver`) is the only `Quiver`
-- instance on `SchemeObj` (the category of schemes has its own).
/-- The **object type of the scheme computad**: a scheme, wrapped. -/
structure SchemeObj where
  /-- The underlying scheme. -/
  scheme : Scheme.{u}

-- Reference: `congrArg` on the wrapper projection; the `eqToHom` lives in the
-- category of schemes.
/-- Transport of morphisms along an equality of wrapped schemes. -/
def SchemeObj.eqToHom {X Y : SchemeObj.{u}} (h : X = Y) :
    X.scheme ⟶ Y.scheme :=
  CategoryTheory.eqToHom (congrArg SchemeObj.scheme h)

-- Reference: [Mimram], Definition 3.1 (a 1-polygraph: objects and
-- generators with source/target); [Street], §1. Ports are trivial (`PUnit`).
/-- The **scheme computad**: objects are schemes, generators are morphisms
(`Σ X Y, X ⟶ Y`), so a path is exactly a composite of morphisms. -/
def SchemeComputad : Computad.{u + 1} where
  port := PUnit
  portMul := fun _ _ => PUnit.unit
  portOne := PUnit.unit
  portMul_assoc := fun _ _ _ => rfl
  portMul_left_one := fun _ => rfl
  portMul_right_one := fun _ => rfl
  obj := SchemeObj.{u}
  gen := Σ (X Y : SchemeObj.{u}), (X.scheme ⟶ Y.scheme)
  src := fun f => f.1
  tgt := fun f => f.2.1
  leftPorts := fun _ => []
  rightPorts := fun _ => []

-- Reference: the only `Quiver` instance on `SchemeObj`, so that
-- `Quiver.Path X Y` and `Y ⟶ Z` for `X Y Z : SchemeObj` mean the computad's
-- own graph.
/-- The quiver of wrapped schemes is the scheme computad's graph. -/
instance : Quiver SchemeObj.{u} := Computad.instQuiver SchemeComputad.{u}

-- Reference: [Street], §1 (paths in the underlying graph); computation steps
-- of `pathMorphism`. The `SchemeObj.eqToHom`s transport along the
-- generator's source/target equalities (`g.2.1`, `g.2.2`).
/-- The **morphism of a path** in the scheme computad: the composite of the
generators along the path, as a morphism of schemes. -/
def pathMorphism {X Y : SchemeObj.{u}} :
    Quiver.Path X Y → (X.scheme ⟶ Y.scheme)
  | .nil => 𝟙 X.scheme
  | .cons p g =>
      pathMorphism p ≫ SchemeObj.eqToHom g.2.1.symm ≫ g.1.2.2 ≫ SchemeObj.eqToHom g.2.2

-- Reference: computation step of `pathMorphism`.
/-- The morphism of the empty path is the identity. -/
theorem pathMorphism_nil {X : SchemeObj.{u}} :
    pathMorphism (.nil : Quiver.Path X X) = 𝟙 X.scheme :=
  pathMorphism.eq_1

-- Reference: computation step of `pathMorphism`.
/-- The morphism of a cons path composes the morphisms. -/
theorem pathMorphism_cons {X Y Z : SchemeObj.{u}}
    (p : Quiver.Path X Y) (g : Y ⟶ Z) :
    pathMorphism (p.cons g) =
      pathMorphism p ≫ SchemeObj.eqToHom g.2.1.symm ≫ g.1.2.2 ≫
        SchemeObj.eqToHom g.2.2 := pathMorphism.eq_2 _ p g

-- Reference: [Mac Lane], Chapter I (composition is associative); core
-- `Quiver.Path.comp_nil`, `Quiver.Path.comp_cons`; induction on the second
-- path.
/-- The morphism of a composite path is the composite of the morphisms. -/
theorem pathMorphism_comp {X Y Z : SchemeObj.{u}}
    (p : Quiver.Path X Y) (q : Quiver.Path Y Z) :
    pathMorphism (p.comp q) = pathMorphism p ≫ pathMorphism q := by
  induction q with
  | nil =>
      exact (congrArg pathMorphism (Quiver.Path.comp_nil p)).trans
        (((congrArg (fun f => pathMorphism p ≫ f) pathMorphism_nil).trans
          (Category.comp_id (pathMorphism p))).symm)
  | cons q e ih =>
      exact (congrArg pathMorphism (Quiver.Path.comp_cons p q e)).trans
        ((pathMorphism_cons (p.comp q) e).trans
          ((congrArg (fun f => f ≫ (SchemeObj.eqToHom e.2.1.symm ≫ e.1.2.2 ≫
              SchemeObj.eqToHom e.2.2)) ih).trans
            (Category.assoc (pathMorphism p) (pathMorphism q)
              (SchemeObj.eqToHom e.2.1.symm ≫ e.1.2.2 ≫ SchemeObj.eqToHom e.2.2))))

/-! ## Gysin moves: equal pushforward on every cycle -/

-- Reference: [Fulton], ch. 1 (the Gysin pushforward `g_*` on cycles along a
-- quasicompact morphism `g`); [Mimram], Definition 3.5 (a move is a relation
-- between parallel paths). QuasiCompactness is carried as an explicit
-- hypothesis (STYLE §2.3: no instance-chosen data in definitions).
/-- A **Gysin move** between parallel paths `p q : X ⟶ Y` in the scheme
computad: the Gysin pushforwards along `p` and along `q` agree on every
cycle. -/
def gysinMove {X Y : SchemeObj.{u}}
    (p q : Computad.Path SchemeComputad.{u} X Y) : Prop :=
  ∀ (hp : QuasiCompact (pathMorphism p)) (hq : QuasiCompact (pathMorphism q))
    (D : AlgebraicCycle X.scheme ℤ),
    @AlgebraicCycle.pushforward _ _ (pathMorphism p) hp D =
      @AlgebraicCycle.pushforward _ _ (pathMorphism q) hq D

-- Reference: [Mimram], Definition 3.5; the move field of `gysinDoctrine` is
-- `gysinMove`.
/-- The **Gysin doctrine**: the scheme computad with Gysin moves as the
declared moves between parallel paths. -/
def gysinDoctrine : Doctrine.{u + 1} where
  computad := SchemeComputad.{u}
  move := fun p q => gysinMove p q

-- Reference: immediate from the definition (reflexivity of equality).
/-- Every path is Gysin-related to itself. -/
theorem gysinMove_refl {X Y : SchemeObj.{u}}
    (p : Computad.Path SchemeComputad.{u} X Y) : gysinMove p p :=
  fun _ _ _ => rfl

-- Reference: symmetry of equality.
/-- Gysin moves are symmetric. -/
theorem gysinMove_symm {X Y : SchemeObj.{u}}
    {p q : Computad.Path SchemeComputad.{u} X Y} :
    gysinMove p q → gysinMove q p :=
  fun h a b D => (h b a D).symm

-- Reference: transitivity of equality.
/-- Gysin moves are transitive. -/
theorem gysinMove_trans {X Y : SchemeObj.{u}}
    {p q r : Computad.Path SchemeComputad.{u} X Y}
    (hq : QuasiCompact (pathMorphism q)) :
    gysinMove p q → gysinMove q r → gysinMove p r :=
  fun h h' hp hr D => (h hp hq D).trans (h' hq hr D)

-- Reference: [Fulton], ch. 1 (functoriality of the pushforward:
-- `AlgebraicCycle.pushforward_comp` applied twice, plus congruence).
/-- **Pushforward composition law at the level of morphisms**: equal
pushforwards compose — `(f ≫ g)_* = g_* ∘ f_*` and congruence. -/
theorem gysin_pushforward_comp {X Y Z : Scheme.{u}} {f f' : X ⟶ Y} {g g' : Y ⟶ Z}
    [QuasiCompact f] [QuasiCompact f'] [QuasiCompact g] [QuasiCompact g']
    (h : ∀ D : AlgebraicCycle X ℤ, AlgebraicCycle.pushforward f D =
      AlgebraicCycle.pushforward f' D)
    (h' : ∀ D : AlgebraicCycle Y ℤ, AlgebraicCycle.pushforward g D =
      AlgebraicCycle.pushforward g' D)
    (D : AlgebraicCycle X ℤ) :
    AlgebraicCycle.pushforward (f ≫ g) D = AlgebraicCycle.pushforward (f' ≫ g') D :=
  (AlgebraicCycle.pushforward_comp f g D).trans
    ((congrArg (AlgebraicCycle.pushforward g) (h D)).trans
      ((h' (AlgebraicCycle.pushforward f' D)).trans
        (AlgebraicCycle.pushforward_comp f' g' D).symm))

-- Reference: [Fulton], ch. 1 (functoriality of the pushforward); [Mimram],
-- Definition 3.5 (moves compose along paths). This is THE rewriting law:
-- **Gysin moves are the rewriting moves** — the pushforward along a
-- composite path is the composite of the pushforwards, so a move before a
-- path composes with a move after it.
/-- **The composition law for Gysin moves**: if `p ~ p'` and `q ~ q'` (as
Gysin moves) then `p ≫ q ~ p' ≫ q'`. -/
theorem gysinMove_comp {X Y Z : SchemeObj.{u}}
    {p p' : Computad.Path SchemeComputad.{u} X Y}
    {q q' : Computad.Path SchemeComputad.{u} Y Z}
    (hp : QuasiCompact (pathMorphism p)) (hp' : QuasiCompact (pathMorphism p'))
    (hq : QuasiCompact (pathMorphism q)) (hq' : QuasiCompact (pathMorphism q'))
    (h : gysinMove p p') (h' : gysinMove q q') :
    gysinMove (p.comp q) (p'.comp q') := by
  intro hc hc' D
  exact Eq.subst (motive := fun f => ∀ (i : QuasiCompact f)
        (j : QuasiCompact (pathMorphism (p'.comp q')))
        (D : AlgebraicCycle X.scheme ℤ),
      @AlgebraicCycle.pushforward _ _ f i D =
        @AlgebraicCycle.pushforward _ _ (pathMorphism (p'.comp q')) j D)
      (pathMorphism_comp p q).symm
    (fun i j D => Eq.subst (motive := fun f => ∀ (k : QuasiCompact f),
        @AlgebraicCycle.pushforward _ _ (pathMorphism p ≫ pathMorphism q) i D =
          @AlgebraicCycle.pushforward _ _ f k D)
        (pathMorphism_comp p' q').symm
      (fun k => @gysin_pushforward_comp X.scheme Y.scheme Z.scheme
        (pathMorphism p) (pathMorphism p') (pathMorphism q) (pathMorphism q')
        hp hp' hq hq'
        (fun E => h hp hp' E) (fun E => h' hq hq' E) D)
      j)
    hc hc' D

end BoringLab
