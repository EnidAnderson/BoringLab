/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import BoringLab.Doctrine.Nim

/-!
# Sieve laws and a coverage instance on the Nim computad

Continuing the GL line (`EnidAnderson/BoringLab#14`): the sieve/coverage
layer of `BoringLab.Doctrine.Geometric` gets its first laws and its first
instance.

* `Sieve.ext` — extensionality for sieves (arrows decide; the closure field
  is a `Prop`, proof-irrelevant);
* `Sieve.maximal` — the maximal sieve (all paths into `X`), with closure by
  `rfl`;
* `Sieve.pullback_comp` — **pullback along a composite is the composite of
  pullbacks** (the coverage functoriality law, via
  `Quiver.Path.comp_assoc`);
* `Sieve.pullback_maximal` — pullback of the maximal sieve is maximal;
* `nimCoverage` — a coverage on the Nim computad as data (each object's
  covering sieve is the maximal one — the GL.0 reading: the play
  CONVENTION is a coverage on the terminal stratum; recorded at comment
  level for Nim, whose positions have no terminal object).

## References
* [Mac Lane–Moerdijk] S. Mac Lane, I. Moerdijk, *Sheaves in Geometry and
  Logic*, Springer, 1992, ch. III, §2 (sieves; pullback `g*` of sieves;
  coverages).
* [Mimram] S. Mimram, arXiv:2312.00429, LMCS 21(3) (2025) (paths and their
  composition).
* Program register: ticket #14 (LAB TREE GL.0), items (i)/(iv).
-/

namespace BoringLab

/-! ## Sieve extensionality and the maximal sieve -/

-- Reference: extensionality for sieves — the membership predicate decides;
-- the closure field is a `Prop` (proof-irrelevant), so `subst` + `rfl`
-- closes after the arrows agree. Named extensionality lemma (STYLE §2:
-- `ext` is not used).
/-- **Extensionality for sieves**: two sieves with the same membership
predicate are equal. -/
theorem Sieve.ext {c : Computad} {X : c.obj} {s t : Sieve c X} (h : s.arrows = t.arrows) :
    s = t := by
  cases s
  cases t
  subst h
  rfl

-- Reference: [Mac Lane–Moerdijk], ch. III, §2 (the maximal sieve `y(X)`:
-- all arrows into `X`); closure is definitional.
/-- The **maximal sieve** on `X`: every path into `X` is in it. -/
def Sieve.maximal (c : Computad) (X : c.obj) : Sieve c X where
  arrows := fun _ => true
  closed := fun _ _ _ _ => rfl

-- Reference: computation step of `Sieve.maximal`.
/-- The maximal sieve contains every arrow. -/
theorem Sieve.maximal_arrows (c : Computad) (X : c.obj) (a : Sigma fun Y => c.Path Y X) :
    (Sieve.maximal c X).arrows a = true := rfl

/-! ## Pullback laws -/

-- Reference: [Mac Lane–Moerdijk], ch. III, §2 (pullback of sieves is
-- functorial: `h*(g*(S)) = (g∘h)*(S)`); via `Quiver.Path.comp_assoc`.
/-- **Pullback along a composite is the composite of pullbacks**. -/
theorem Sieve.pullback_comp {c : Computad} {X Y Z : c.obj} (s : Sieve c X)
    (g : c.Path Y X) (h : c.Path Z Y) :
    (s.pullback g).pullback h = s.pullback (h.comp g) := by
  apply Sieve.ext
  funext a
  exact congrArg s.arrows (congrArg (Sigma.mk a.1) (Quiver.Path.comp_assoc a.2 h g))

-- Reference: [Mac Lane–Moerdijk], ch. III, §2 (the maximal sieve pulls back
-- to the maximal sieve).
/-- Pullback of the maximal sieve is the maximal sieve. -/
theorem Sieve.pullback_maximal {c : Computad} {X Y : c.obj} (g : c.Path Y X) :
    (Sieve.maximal c X).pullback g = Sieve.maximal c Y := by
  apply Sieve.ext
  funext a
  exact Sieve.maximal_arrows c X ⟨a.1, a.2.comp g⟩

/-! ## A coverage instance on the Nim computad -/

-- Reference: ticket #14, item (iv) (`Coverage` as declared data, the PHYS.0
-- precedent); the GL.0 reading: a play CONVENTION is a coverage on the
-- terminal stratum — Nim's positions have no terminal object, so the
-- instance records the maximal coverage at every object (normal-play
-- convention: every legal move is a covering simplification — the honest
-- data-level shadow).
/-- The **Nim coverage**: at every pile size, the covering sieve is the
maximal one. -/
def nimCoverage : Coverage nimComputad := fun X => [Sieve.maximal nimComputad X]

-- Reference: computation step of `nimCoverage`.
/-- The Nim coverage at `X` is the singleton list of the maximal sieve. -/
theorem nimCoverage_eq (X : ℕ) :
    nimCoverage X = [Sieve.maximal nimComputad X] := rfl

end BoringLab
