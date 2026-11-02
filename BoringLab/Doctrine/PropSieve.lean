/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import BoringLab.Doctrine.Coverage
import BoringLab.Epistemology.Truncation

/-!
# GL.0.1: the sieve truncation ledger — decidable fragment, Prop upgrade path

Ticket #69's sibling rung `EnidAnderson/BoringLab#70` (GL.0.1): the landed
`Sieve` (`BoringLab.Doctrine.Geometric`) has `Bool`-membership — the
deliberate STYLE.C decidable choice — while the cited definition
([Mac Lane–Moerdijk] ch. III §2) is `Prop`-valued, as is BoringMath's own
cd-structure layer (`Sieve.ofTwoArrows`). Under the lab's truncation
principle, a truncation without a tracked remainder violates the central
law — so this module records the ledger:

* `PropSieve` — the `Prop`-valued sieve (the refinement target, the pinned
  definition), with closure and pullback (`PropSieve.pullback`, by
  `Quiver.Path.comp_assoc`);
* `Sieve.toProp` — the upgrade map: every decidable sieve refines to a
  `Prop`-valued sieve (THE theorem shape of the ticket);
* `Sieve.toProp_pullback` — the upgrade commutes with pullback (as an
  `Iff` on arrows, avoiding `propext`);
* `sieveDecidableTrunc` — the truncation ledger of the sieve layer: the
  decidable fragment as data, the remainder = the non-surjectivity of the
  upgrade (what decidability excludes: non-decidable sieves — NOT `True`,
  D.1 non-degenerate);
* `exists_nonDecidable_sieve` — the first-class witness that the upgrade is
  not surjective — a named hole with a diagonal peeling plan.

## References
* [Mac Lane–Moerdijk] S. Mac Lane, I. Moerdijk, *Sheaves in Geometry and
  Logic*, Springer, 1992, ch. III, §2 (sieves: `Prop`-valued membership,
  closure under precomposition; pullback).
* Program register: BoringLab tickets #14 (GL.0) and #70 (GL.0.1); the
  truncation-ledger reading is #41 (EPI.8.1, landed).
-/

namespace BoringLab

/-! ## The Prop-valued sieve -/

-- Reference: [Mac Lane–Moerdijk], ch. III, §2 (the pinned definition:
-- `Prop`-valued membership, closed under precomposition).
/-- A **`Prop`-valued sieve** on `X`: a predicate on paths into `X`, closed
under precomposition. -/
structure PropSieve (c : Computad) (X : c.obj) where
  /-- Membership in the sieve. -/
  arrows : Sigma (fun Y => c.Path Y X) → Prop
  /-- Closure under precomposition. -/
  closed : ∀ (a : Sigma fun Y => c.Path Y X), arrows a →
    ∀ (Z : c.obj) (q : c.Path Z a.1), arrows ⟨Z, q.comp a.2⟩

-- Reference: [Barendregt], ch. 2 (eta conversion), as in `Sieve.eta`.
-- REVIEW(citation): pin down the exact section in review.
/-- **Eta conversion for Prop-sieves**. -/
theorem PropSieve.eta {c : Computad} {X : c.obj} (s : PropSieve c X) :
    PropSieve.mk s.arrows s.closed = s := by
  cases s with
  | mk arrows closed => rfl

-- Reference: [Mac Lane–Moerdijk], ch. III, §2 (pullback of a sieve);
-- closure by `Quiver.Path.comp_assoc` (as `Sieve.pullback`).
/-- The **pullback of a Prop-sieve** along `g : Y ⟶ X`. -/
def PropSieve.pullback {c : Computad} {X Y : c.obj} (s : PropSieve c X) (g : c.Path Y X) :
    PropSieve c Y where
  arrows := fun h => s.arrows ⟨h.1, h.2.comp g⟩
  closed := by
    intro h hh Z q
    exact Eq.subst (motive := fun p => s.arrows ⟨Z, p⟩)
      (Quiver.Path.comp_assoc q h.2 g).symm (s.closed ⟨h.1, h.2.comp g⟩ hh Z q)

/-! ## The upgrade map -/

-- Reference: ticket #70, item (ii) — THE theorem shape: every decidable
-- sieve refines to a Prop-valued sieve; `arrows a := (s.arrows a = true)`.
/-- The **upgrade map**: the decidable sieve `s` as a `Prop`-valued sieve. -/
def Sieve.toProp {c : Computad} {X : c.obj} (s : Sieve c X) : PropSieve c X where
  arrows := fun a => s.arrows a = true
  closed := fun a ha Z q => s.closed a ha Z q

-- Reference: ticket #70 — the upgrade commutes with pullback (as an `Iff`
-- on arrows; both sides unfold to `s.arrows ⟨a.1, a.2.comp g⟩ = true`).
/-- The upgrade map commutes with pullback. -/
theorem Sieve.toProp_pullback {c : Computad} {X Y : c.obj} (s : Sieve c X) (g : c.Path Y X)
    (a : Sigma fun W => c.Path W Y) :
    (s.pullback g).toProp.arrows a ↔ ((s.toProp).pullback g).arrows a :=
  Iff.rfl

/-! ## The truncation ledger of the sieve layer -/

-- Reference: ticket #70, item (i); the `Truncation` structure of #41
-- (EPI.8.1): level, data, REMAINDER. The remainder here is the
-- non-surjectivity of the upgrade — what decidability excludes
-- (non-decidable sieves) — NOT `True` (D.1 non-degenerate).
/-- The **truncation ledger of the sieve layer**: the decidable sieves as
the displayed data (level 0, empty list), the remainder = the existence of
a non-decidable (Prop-valued, not-upgradeable) sieve. -/
def sieveDecidableTrunc (c : Computad) (X : c.obj) : Truncation (Sieve c X) where
  level := 0
  data := []
  remainderCarrier := Prop
  remainder := ∃ s : PropSieve c X, ∀ d : Sieve c X, Sieve.toProp d ≠ s
  refine := fun t =>
    Trunc.mk (t.level + 1) t.data t.remainderCarrier t.remainder

-- Reference: ticket #70, item (ii): the upgrade map's failure to be
-- surjective IS the content — a non-decidable-sieve witness is a
-- first-class finding.
-- TEMPORARY SORRY: the honest witness has not been constructed yet.
-- PEELING PLAN: classical diagonal — take `s.arrows a := ¬ ∃ d : Sieve c X,
-- d.arrows a = true ∧ …` (the sieve of arrows no decidable sieve contains
-- all of), or the direct diagonal `s.arrows a := ¬ (Classical.choose …)`;
-- needs `Nonempty (Sigma fun Y => c.Path Y X)` to diagonalize against;
-- flag any `noncomputable` inline (the nonconstructivity IS the content).
/-- A **non-decidable sieve exists**: the upgrade map `Sieve.toProp` is not
surjective. -/
theorem exists_nonDecidable_sieve (c : Computad) (X : c.obj)
    (hne : Nonempty (Sigma fun Y => c.Path Y X)) :
    ∃ s : PropSieve c X, ∀ d : Sieve c X, Sieve.toProp d ≠ s := by
  sorry

end BoringLab
