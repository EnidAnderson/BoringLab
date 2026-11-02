/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import BoringLab.Doctrine.Doctrine
import Mathlib.CategoryTheory.Localization.Predicate

/-!
# Doctrine-localization: existence, universal property, inversion as data

This module continues part 2 of the scope contract of
`EnidAnderson/BoringLab#3`. Building on `BoringLab.Doctrine.Doctrine` (the
`Doctrine` structure and the declared-move class `Doctrine.moveClass`), it
states and proves the first theorems of the doctrine-localization
`C[W⁻¹]`, all via mathlib's in-tree localization machinery at the pin
`v4.35.0-rc3` (`Mathlib/CategoryTheory/Localization/`), every consumed name
GOLD-verified by probe files run with `lake env lean` against the pin:

* `Doctrine.declared_move_wIso` — a declared move `p ⇄ q` yields the explicit
  isomorphism `Localization.Construction.wIso p` between the localized
  objects: the inversion of a declared move is *data* (an `Iso`, whose fields
  are the inverse and the two inverse laws), not a global axiom.
* `Doctrine.lift_exists` / `Doctrine.lift_unique` — the universal property of
  the localization: any functor out of the path category that inverts the
  declared-move class factors through `Q`, and the factorization is unique
  (`Localization.Construction.lift` / `fac` / `uniq`).
* `misereQuotient_related_iso` — the falsifiable shadow of the issue, derived:
  in the Plambeck–Siegel misère-quotient localization, `r`-related games
  become isomorphic.

All statements are `Prop`-valued: the consumed localization construction is
choice-tainted at the pin (a `noncomputable section`), so it is used only
inside theorem statements, never in a `def` — every declaration of this
module is computable or a proof.

## References
* [Gabriel–Zisman] P. Gabriel, M. Zisman, *Calculus of Fractions and Homotopy
  Theory*, Lecture Notes in Mathematics 1, Springer-Verlag, 1967, Chapter I
  (the localization `C[W⁻¹]`, its universal property, and the inversion of
  the morphisms of `W` as explicit isomorphism data).
* [Plambeck–Siegel] T. E. Plambeck, A. N. Siegel, *Misère quotients for
  impartial games*, arXiv:math/0609825 (2006), §2.
* [Mimram] S. Mimram, *Polygraphs: from rewriting to higher categories*,
  arXiv:2312.00429, Logical Methods in Computer Science 21(3) (2025),
  7:1–7:47 — Definition 3.5 (2-polygraph: generators plus relations).
-/

universe u

namespace BoringLab

open CategoryTheory

-- Reference: [Gabriel–Zisman], Chapter I, §1 (a morphism `w ∈ W` becomes an
-- isomorphism in `C[W⁻¹]`, with an explicit inverse); mathlib at pin
-- v4.35.0-rc3: `CategoryTheory.Localization.Construction.wIso`
-- (Mathlib/CategoryTheory/Localization/Construction.lean, GOLD-verified).
-- REVIEW(citation): pin the exact section of [Gabriel–Zisman] in review.
/-- **Declared-move inversion is explicit isomorphism data**: a declared move
`p ⇄ q` of parallel paths yields an isomorphism between the localized
objects — witnessed by the explicit `wIso p`, whose fields are the inverse
and the two inverse laws, not a global axiom. (Stated as `Nonempty (Iso …)`
because the consumed `wIso` is choice-tainted at the pin and may only appear
inside a `Prop`.) -/
theorem Doctrine.declared_move_wIso (d : Doctrine.{u}) {X Y : d.computad.obj}
    (p q : d.computad.Path X Y) (h : d.move p q) :
    Nonempty (Iso (d.moveClass.Q.obj X) (d.moveClass.Q.obj Y)) :=
  ⟨Localization.Construction.wIso (W := d.moveClass) p (d.moveClass_left p q h)⟩

-- Reference: [Gabriel–Zisman], Chapter I, §1 (the universal property of
-- `C[W⁻¹]`); mathlib at pin v4.35.0-rc3:
-- `CategoryTheory.Localization.Construction.lift` and `...fac`
-- (Mathlib/CategoryTheory/Localization/Construction.lean, GOLD-verified).
-- REVIEW(citation): pin the exact section of [Gabriel–Zisman] in review.
/-- **Existence part of the universal property of the doctrine-localization**:
every functor out of the path category that inverts the declared-move class
factors through `Q`; the lifted functor is the explicit
`Localization.Construction.lift`. -/
theorem Doctrine.lift_exists (d : Doctrine.{u}) {E : Type u} [Category.{u} E]
    (F : Paths d.computad.obj ⥤ E) (hF : d.moveClass.IsInvertedBy F) :
    ∃ L : d.moveClass.Localization ⥤ E, d.moveClass.Q ⋙ L = F :=
  ⟨Localization.Construction.lift F hF, Localization.Construction.fac F hF⟩

-- Reference: [Gabriel–Zisman], Chapter I, §1 (uniqueness of the factorization
-- through `C[W⁻¹]`); mathlib at pin v4.35.0-rc3:
-- `CategoryTheory.Localization.Construction.uniq`
-- (Mathlib/CategoryTheory/Localization/Construction.lean, GOLD-verified).
-- REVIEW(citation): pin the exact section of [Gabriel–Zisman] in review.
/-- **Uniqueness part of the universal property of the doctrine-localization**:
two factorizations of the same functor through `Q` are equal. -/
theorem Doctrine.lift_unique (d : Doctrine.{u}) {E : Type u} [Category.{u} E]
    (F : Paths d.computad.obj ⥤ E) (L₁ L₂ : d.moveClass.Localization ⥤ E)
    (h₁ : d.moveClass.Q ⋙ L₁ = F) (h₂ : d.moveClass.Q ⋙ L₂ = F) :
    L₁ = L₂ :=
  Localization.Construction.uniq L₁ L₂ (h₁.trans h₂.symm)

-- Reference: [Plambeck–Siegel], arXiv:math/0609825, §2 (`r`-related games are
-- identified in the misère quotient); [Gabriel–Zisman], Chapter I (inversion
-- in the localization); mathlib at pin v4.35.0-rc3:
-- `CategoryTheory.Localization.Construction.wIso` (GOLD-verified).
-- REVIEW(citation): pin the exact section of [Plambeck–Siegel] in review.
/-- **Falsifiable shadow, derived**: in the misère-quotient doctrine-
localization, `r`-related games become isomorphic — the generator path of an
`r`-related pair is a declared move, hence inverted, giving an isomorphism
between the localized games (witnessed by the explicit `wIso`; stated as
`Nonempty (Iso …)` because `wIso` is choice-tainted at the pin). -/
theorem misereQuotient_related_iso (r : Game.{u} → Game.{u} → Prop) {X Y : Game.{u}}
    (h : r X Y) :
    Nonempty (Iso ((misereQuotient r).moveClass.Q.obj X)
      ((misereQuotient r).moveClass.Q.obj Y)) :=
  ⟨Localization.Construction.wIso (W := (misereQuotient r).moveClass)
    ((misereQuotientComputad r).toPath ⟨⟨(X, Y), h⟩, rfl, rfl⟩)
    (Doctrine.moveClass_left (misereQuotient r) _ _
      (misereQuotient_move_self r ⟨⟨(X, Y), h⟩, rfl, rfl⟩))⟩

end BoringLab
