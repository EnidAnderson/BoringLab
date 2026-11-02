/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import BoringLab.Doctrine.Morph

/-!
# LAB HOC.1: the semicategory-to-computad upgrade

Ticket #112 (child of HOC.0 #110): a **semicategory** (objects +
morphisms, associative composition, NO identities) IS a 1-computad —
paths are the composition. The composition-level theorems hold at the
computad level without any identity data:

* `Semicat` — the semicategory = computad alias;
* `Computad.Morph.ext` — extensionality for polygraph morphisms (funext on
  the maps; the four law fields are `Prop`, closed by proof irrelevance);
* `Computad.Morph.comp_assoc` — **proved**: morphisms of semicategories
  compose associatively, with no identities anywhere;
* `CatData` — the degenerate case: a category is a computad with chosen
  identity generators plus the unit laws; the identity laws then give the
  neutral-element results (`Computad.Morph.mapPath_id`, landed) as the
  degenerate case.

Row register (which results upgrade, which genuinely need identities):
all composition/functoriality-level results upgrade to semicategories
(computads); results using units (identity naturality, unit laws) are the
degenerate category case.

## References
* [Mac Lane] S. Mac Lane, *Categories for the Working Mathematician*, 2nd
  ed., Springer, 1998, ch. I, §1 (semicategories: associativity without
  identities; categories add identity arrows).
* [Street] R. Street, *The algebra of oriented simplexes*, JPAA 49 (1987),
  283–335 (computads = free semicategories).
* [Mimram] S. Mimram, arXiv:2312.00429, LMCS 21(3) (2025), §3.
* Program register: BoringLab tickets #110 (HOC.0), #112 (HOC.1).
-/

namespace BoringLab

/-! ## Semicategory = computad -/

-- Reference: [Mac Lane], ch. I, §1 (a semicategory: objects + morphisms +
-- associative composition, no identities); [Street] (a computad is the
-- free semicategory: paths are the composites).
/-- A **semicategory**, in pure-composition form: a 1-computad. Paths are
the composites; no identity data is needed. -/
abbrev Semicat := Computad

/-! ## Extensionality and associativity of morphisms (no identities used) -/

-- Reference: ticket #112 — named extensionality lemma (the `ext` tactic is
-- not used): the maps agree by `funext`, the generator maps pointwise, and
-- the four law fields are `Prop` (proof irrelevance).
-- Reference: ticket #112 — named extensionality lemma (the `ext` tactic is
-- not used): the maps agree by `funext`, the generator maps pointwise, and
-- the four law fields are `Prop` (proof irrelevance).
/-- **Extensionality for computad morphisms**. -/
theorem Computad.Morph.ext {c d : Computad} {F G : Computad.Morph c d}
    (hp : F.portMap = G.portMap) (ho : F.objMap = G.objMap)
    (hg : ∀ {X Y : c.obj} (e : c.Hom X Y), HEq (F.genMap e) (G.genMap e)) :
    F = G := by
  cases F with
  | mk Fp Fpm Fpo Fo Fg Fl Fr =>
  cases G with
  | mk Gp Gpm Gpo Go Gg Gl Gr =>
  cases hp
  cases ho
  have hg' : ∀ (X Y : c.obj) (e : c.Hom X Y),
      Fg (X := X) (Y := Y) e = Gg (X := X) (Y := Y) e :=
    fun X Y e => eq_of_heq (hg (X := X) (Y := Y) e)
  have e3 : (fun (X Y : c.obj) (e : c.Hom X Y) => Fg (X := X) (Y := Y) e) =
      (fun (X Y : c.obj) (e : c.Hom X Y) => Gg (X := X) (Y := Y) e) :=
    funext fun X => funext fun Y => funext fun e => hg' X Y e
  refine Eq.subst (motive := fun q : PSigma (fun (ψ : ∀ (X Y : c.obj) (e : c.Hom X Y),
      d.Hom (Fo X) (Fo Y)) =>
      ((∀ {X Y : c.obj} (e : c.Hom X Y), d.pathLeftWord (d.toPath (ψ X Y e)) =
        Fp (c.pathLeftWord (c.toPath e))) ∧
      (∀ {X Y : c.obj} (e : c.Hom X Y), d.pathRightWord (d.toPath (ψ X Y e)) =
        Fp (c.pathRightWord (c.toPath e))))) =>
      Computad.Morph.mk Fp Fpm Fpo Fo (fun {X Y : c.obj} (e : c.Hom X Y) => q.1 X Y e) q.2.1 q.2.2 =
        Computad.Morph.mk Fp Gpm Gpo Fo Gg Gl Gr)
    (PSigma.ext e3.symm (proof_irrel_heq _ _) :
      (⟨(fun (X Y : c.obj) (e : c.Hom X Y) => Gg (X := X) (Y := Y) e), Gl, Gr⟩ :
        PSigma (fun (ψ : ∀ (X Y : c.obj) (e : c.Hom X Y), d.Hom (Fo X) (Fo Y)) =>
          ((∀ {X Y : c.obj} (e : c.Hom X Y), d.pathLeftWord (d.toPath (ψ X Y e)) =
            Fp (c.pathLeftWord (c.toPath e))) ∧
          (∀ {X Y : c.obj} (e : c.Hom X Y), d.pathRightWord (d.toPath (ψ X Y e)) =
            Fp (c.pathRightWord (c.toPath e)))))) =
      ⟨(fun (X Y : c.obj) (e : c.Hom X Y) => Fg (X := X) (Y := Y) e), Fl, Fr⟩) rfl

-- Reference: ticket #112, item (ii) — **associativity of morphism
-- the maps agree pointwise (definitional after `funext`), the laws by
-- proof irrelevance.
/-- Morphisms of semicategories (computads) compose associatively. -/
theorem Computad.Morph.comp_assoc {c d e f : Computad} (F : Computad.Morph c d)
    (G : Computad.Morph d e) (H : Computad.Morph e f) :
    (F.comp G).comp H = F.comp (G.comp H) := by
  refine Computad.Morph.ext ?_ ?_ ?_
  · exact funext fun a => rfl
  · exact funext fun X => rfl
  · intro X Y g
    exact HEq.rfl
-- Reference: ticket #112, item (iii); [Mac Lane], ch. I, §1 (a category is a
-- semicategory with identity arrows and the unit laws).
/-- **Category data on a computad** (the degenerate case): a chosen identity
generator at each object, with the two unit laws as `Prop` fields. -/
structure CatData (c : Computad) where
  /-- The identity generator at each object. -/
  idGen : ∀ X : c.obj, c.Hom X X
  /-- Left unit law: `id_X` composed on the left is the identity. -/
  left_id : ∀ {X Y : c.obj} (p : c.Path X Y),
    (c.toPath (idGen X)).comp p = p
  /-- Right unit law. -/
  right_id : ∀ {X Y : c.obj} (p : c.Path X Y),
    p.comp (c.toPath (idGen Y)) = p

-- Reference: ticket #112 — the degenerate-case row: with `CatData`, the
-- identity morphism is neutral on paths (`Computad.Morph.mapPath_id`,
-- landed in `BoringLab.Doctrine.Morph`) — the category-level unit results
-- are exactly this degenerate case, while all comp-level results (above)
-- hold for plain semicategories.
/-- Categories as the degenerate case: the row statement, recorded. -/
theorem catData_degenerate_row (c : Computad) (_h : CatData c) :
    ∀ {X Y : c.obj} (p : c.Path X Y),
      (Computad.Morph.id c).mapPath p = p := fun p => Computad.Morph.mapPath_id p

end BoringLab
