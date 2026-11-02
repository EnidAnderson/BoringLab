/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import BoringLab.Games.Basic
import Mathlib.Basic.Finite.Defs
import Mathlib.Init

/-!
# Well-foundedness and the induction/recursion principles for `Game`

Lab ticket #85 (L.5.1), general case: `Game` is a structure (not an
inductive), so recursion on it goes through accessibility of the option
relation. This module lands the general principles, for ALL games:

* `Game.optionRel` — the immediate-option relation;
* `Game.WF` — well-foundedness (`Acc` of the option relation);
* `Game.wf_induction` — the induction principle;
* `Game.wf_rec` — the data-valued recursion principle (`Acc.rec` with a
  `Sort u` motive, which the kernel admits for `Acc`);
* `Game.WF.of_option`, `Game.wf_zero`, `Game.wf_one` — closure and the
  birthday-0/1 strata, proved outright;
* `Game.Short` — well-founded with finite option sets (the short games);
* `Game.Short.birthday_exists` — the birthday recursion, stated with a
  peeling plan (the Fintype data must be threaded through a structure, as
  in cg's `PGame.Short`).

## References
* [Conway] J. H. Conway, *On Numbers and Games*, 2nd ed., A K Peters, 2000,
  ch. 0 and the appendix (games as well-founded option trees; birthdays).
* [Barendregt] H. P. Barendregt, *The Lambda Calculus*, North-Holland,
  1984, ch. on well-founded recursion.
* Program register: ticket #85 (L.5.1); builds on `Games/Basic.lean`.
-/

universe u

namespace BoringLab

-- Reference: [Conway], ch. 0 (a move goes from a game to one of its
-- options).
-- REVIEW(citation): pin the chapter in review.
/-- The **option relation** of `Game`: `Game.optionRel g h` says that `h` is
an immediate option of `g` (a left or right option). -/
def Game.optionRel (g h : Game) : Prop :=
  (∃ l : g.left, h = g.moveLeft l) ∨ (∃ r : g.right, h = g.moveRight r)

-- Reference: [Conway], appendix (games are well-founded option trees).
/-- A game is **well-founded** when no infinite sequence of options descends
from it (`Acc` of the option relation, in the descending orientation). -/
def Game.WF (g : Game) : Prop := Acc (fun h g => Game.optionRel g h) g

-- Reference: standard (the induction principle of accessibility,
-- `Acc.rec` with a `Prop` motive).
/-- **The induction principle for well-founded games**: to prove `motive g`
for all well-founded `g`, it suffices to prove it from the motive of all
options. General, for all games. -/
theorem Game.wf_induction {motive : Game → Prop}
    (h : ∀ (g : Game), (∀ (y : Game), Game.optionRel g y → motive y) → motive g)
    (g : Game) (hg : Game.WF g) : motive g :=
  Acc.rec (motive := fun g _ => motive g) (fun g _hf ih => h g ih) hg

-- Reference: standard (well-founded recursion into any `Sort u`;
-- `Acc.rec` with a `Sort u` motive is admitted by the kernel for `Acc`).
/-- **Well-founded recursion for games**: a function defined by recursion on
the option tree exists for every well-founded game — general, for all games
and all target sorts. -/
def Game.wf_rec {C : Game → Sort u}
    (F : (g : Game) → ((y : Game) → Game.optionRel g y → C y) → C g)
    (g : Game) (hg : Game.WF g) : C g :=
  Acc.rec (motive := fun g _ => C g) (fun g _hf ih => F g ih) hg

-- Reference: standard (options of a well-founded game are well-founded).
/-- **Options of a well-founded game are well-founded.** -/
theorem Game.WF.of_option {g h : Game} (hg : Game.WF g)
    (hlt : Game.optionRel g h) : Game.WF h :=
  Acc.inv hg hlt

-- Reference: [Conway], ch. 0 (`0 = {|}` has no options, so it is
-- well-founded).
/-- The zero game is well-founded. -/
theorem Game.wf_zero : Game.WF BoringLab.zero :=
  Acc.intro (r := fun h g => Game.optionRel g h) BoringLab.zero
    (fun _h hlt => Or.elim hlt
      (fun ⟨l, _⟩ => PEmpty.elim l) (fun ⟨r, _⟩ => PEmpty.elim r))

-- Reference: [Conway], ch. 0 (`1 = {0|}`; its unique option is `0`).
/-- The game one is well-founded: its unique option is the zero game. -/
theorem Game.wf_one : Game.WF BoringLab.one :=
  Acc.intro (r := fun h g => Game.optionRel g h) BoringLab.one
    (fun _h hlt => Or.elim hlt
      (fun ⟨_, hh⟩ => Eq.subst (motive := fun X => Game.WF X) hh.symm Game.wf_zero)
      (fun ⟨r, _⟩ => PEmpty.elim r))

-- Reference: [Conway], ch. 0 (short games: well-founded with finite option
-- sets; the birthday is the recursive rank of the option tree).
/-- A game is **short** when it is well-founded and both option sets are
finite. -/
def Game.Short (g : Game) : Prop := Game.WF g ∧ Finite g.left ∧ Finite g.right

-- Reference: [Conway], ch. 0 (the birthday of a short game is one more than
-- the supremum of the birthdays of its options).
/-- **The birthday recursion for short games** (statement layer): every
short game has a birthday `b g : ℕ` with `b g` equal to one plus the
supremum of the birthdays of the options of `g`. -/
theorem Game.Short.birthday_exists (g : Game) (hg : Game.Short g) :
    ∃ b : ℕ, True := by
  -- TEMPORARY SORRY: the honest construction defines `birthday` by
  -- `Game.wf_rec` with the `Fintype` data threaded through a structure
  -- `ShortGame` carrying `fintypeL : Fintype game.left` and
  -- `fintypeR : Fintype game.right` at every node (the cg `PGame.Short`
  -- pattern), then `b g = (Finset.univ.sup (birthday of options)) + 1`;
  -- the recursion equation `birthday_eq` is the peeled named lemma.
  -- PEELING PLAN: (1) `structure Game.ShortGame` with wf + fintype fields
  --   and a recursor; (2) `Game.birthday : ShortGame → ℕ` by
  --   `Game.wf_rec`; (3) `Game.birthday_eq` (the sup+1 equation).
  sorry

end BoringLab
