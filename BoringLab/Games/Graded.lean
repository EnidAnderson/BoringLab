/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import BoringLab.Doctrine.Computad
import BoringLab.Games.Normal
import Mathlib.Init

/-!
# Games as graded computads: the outcome recursion at the computad level

Lab ticket #100 (L.15.1) made real at the base, applying the COMPUTAD-FIRST
discipline: the normal-play recursion is stated and proved for the WHOLE
CLASS of graded game computads (`GradedGameComputad`), not just for `TGame` —
theorems are upgraded to whatever class of computad they apply to.

* `GradedGameComputad` — a `Computad` (A2.0 #3) with a depth grading on
  objects that strictly decreases along generators;
* `winAux` / `Win` — the mover-win predicate by recursion on the depth bound
  (the `WinLoseTree.valueAux` pattern of #10, Prop-valued so NO finiteness or
  decidability is needed — the theorem holds for every graded computad);
* `winAux_of_le` (stabilization) and **`win_equation`** — the recursion
  equation `Win x ↔ ∃ move out of x to ¬Win`, for every object of every
  graded game computad.

## References
* [Burroni] 1994; [Mimram] arXiv:2312.00429 Def. 3.1; [Street] 1987 —
  computads/polygraphs (the ambient formalism of this module, per A2.0 #3).
* [Conway] ONAG ch. 0 (the normal-play recursion).
* Program register: tickets #100 (L.15.1), #3 (A2.0), #10 (TR.0), #14
  (GL.0), #82 (L.5.2).
-/

universe u

namespace BoringLab

-- Reference: [Burroni]/[Mimram] Def. 3.1 (a polygraph) + [Conway] ch. 0 (the
-- depth/birthday grading of a game: every move decreases the depth).
-- REVIEW(citation): pin the Mimram definition number in review.
/-- A **graded game computad**: a computad whose objects carry a depth
grading that strictly decreases along every generator. This is the class of
computads to which the normal-play recursion applies. -/
structure GradedGameComputad where
  /-- The underlying computad (objects = positions, generators = moves). -/
  comp : Computad.{u}
  /-- The depth grading on positions. -/
  depth : comp.obj → ℕ
  /-- Every move strictly decreases the depth. -/
  depth_tgt : ∀ g : comp.gen, depth (comp.tgt g) < depth (comp.src g)

-- Reference: the `WinLoseTree.valueAux` pattern of #10 (Games/Trace.lean),
-- Prop-valued: no finiteness or decidability is assumed, so the recursion is
-- stated for the whole class of graded game computads.
/-- The mover-win predicate at depth bound `d`: `winAux (d+1) x` iff some
generator out of `x` has target of depth `< d+1` and is a loss at bound `d`. -/
def GradedGameComputad.winAux (gc : GradedGameComputad) : ℕ → gc.comp.obj → Prop
  | 0, _ => False
  | d + 1, x =>
    ∃ g : gc.comp.gen, gc.comp.src g = x ∧ gc.depth (gc.comp.tgt g) < d + 1 ∧
      ¬ gc.winAux d (gc.comp.tgt g)

-- Reference: computation steps of `winAux`; `rfl` only in these primitive
-- definitional lemmas.
/-- Primitive definitional lemma: `winAux 0 x = False`. -/
theorem GradedGameComputad.winAux_zero (gc : GradedGameComputad) (x : gc.comp.obj) :
    gc.winAux 0 x = False := rfl

-- Reference: as above.
/-- Primitive definitional lemma: the successor equation of `winAux`. -/
theorem GradedGameComputad.winAux_succ (gc : GradedGameComputad) (d : ℕ)
    (x : gc.comp.obj) :
    gc.winAux (d + 1) x =
      ∃ g : gc.comp.gen, gc.comp.src g = x ∧ gc.depth (gc.comp.tgt g) < d + 1 ∧
        ¬ gc.winAux d (gc.comp.tgt g) := rfl

-- Reference: the `WinLoseTree.valueAux_of_le` pattern of #10 (Games/Trace.lean),
-- by strong recursion on the bound `d`; Prop-valued (iff), so it holds for
-- EVERY graded game computad (no finiteness/decidability assumed).
/-- **Stabilization**: above the depth of `x`, `winAux` no longer changes. -/
theorem GradedGameComputad.winAux_of_le (gc : GradedGameComputad) : ∀ d x,
    gc.depth x ≤ d → (gc.winAux d x ↔ gc.winAux (gc.depth x) x) := by
  intro d
  exact Nat.strongRecOn d
    (motive := fun d => ∀ x, gc.depth x ≤ d →
      (gc.winAux d x ↔ gc.winAux (gc.depth x) x))
    (fun d ih x h => by
      rcases Nat.eq_zero_or_pos d with rfl | hpos
      · have h0 : gc.depth x = 0 := Nat.eq_zero_of_le_zero h
        exact Eq.subst (motive := fun n => (gc.winAux 0 x ↔ gc.winAux n x)) h0.symm
          Iff.rfl
      · obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hpos)
        rcases Nat.eq_zero_or_pos (gc.depth x) with hx0 | hxpos
        · have hx : gc.depth x = 0 := hx0
          exact ⟨fun hw => by
            have hwE : ∃ g : gc.comp.gen, gc.comp.src g = x ∧
                gc.depth (gc.comp.tgt g) < k + 1 ∧ ¬ gc.winAux k (gc.comp.tgt g) :=
              Eq.subst (motive := fun P => P) (gc.winAux_succ k x) hw
            obtain ⟨g, hs, _, _⟩ := hwE
            have hlt : gc.depth (gc.comp.tgt g) < gc.depth x :=
              Eq.subst (motive := fun y => gc.depth (gc.comp.tgt g) < gc.depth y) hs
                (gc.depth_tgt g)
            exact absurd (Eq.subst (motive := fun n => gc.depth (gc.comp.tgt g) < n) hx hlt)
              (Nat.not_lt_zero _),
            fun hw => (Eq.subst (motive := fun _ => False) (gc.winAux_zero x)
              (Eq.subst (motive := fun n => gc.winAux n x) hx hw)).elim⟩
        · obtain ⟨e, he⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hxpos)
          have heqd : e ≤ k := Nat.succ_le_succ_iff.mp
            (Eq.subst (motive := fun n => n ≤ k + 1) he h)
          have hchild : ∀ g : gc.comp.gen, gc.comp.src g = x →
              gc.depth (gc.comp.tgt g) ≤ e ∧ gc.depth (gc.comp.tgt g) ≤ k := by
            intro g hs
            have hlt : gc.depth (gc.comp.tgt g) < e + 1 :=
              Eq.subst (motive := fun n => gc.depth (gc.comp.tgt g) < n) he
                (Eq.subst (motive := fun y => gc.depth (gc.comp.tgt g) < gc.depth y) hs
                  (gc.depth_tgt g))
            exact ⟨Nat.le_of_lt_succ hlt, Nat.le_trans (Nat.le_of_lt_succ hlt) heqd⟩
          have ihk : ∀ g : gc.comp.gen, gc.comp.src g = x →
              (gc.winAux k (gc.comp.tgt g) ↔
                gc.winAux (gc.depth (gc.comp.tgt g)) (gc.comp.tgt g)) :=
            fun g hs => ih k (Nat.lt_succ_self k) (gc.comp.tgt g) (hchild g hs).2
          have ihe : ∀ g : gc.comp.gen, gc.comp.src g = x →
              (gc.winAux e (gc.comp.tgt g) ↔
                gc.winAux (gc.depth (gc.comp.tgt g)) (gc.comp.tgt g)) :=
            fun g hs => ih e (Nat.lt_of_le_of_lt heqd (Nat.lt_succ_self k))
              (gc.comp.tgt g) (hchild g hs).1
          have hopt : ∀ g : gc.comp.gen, gc.comp.src g = x →
              ((gc.depth (gc.comp.tgt g) < k + 1 ∧ ¬ gc.winAux k (gc.comp.tgt g)) ↔
               (gc.depth (gc.comp.tgt g) < e + 1 ∧ ¬ gc.winAux e (gc.comp.tgt g))) := by
            intro g hs
            have hlt : gc.depth (gc.comp.tgt g) < e + 1 :=
              Eq.subst (motive := fun n => gc.depth (gc.comp.tgt g) < n) he
                (Eq.subst (motive := fun y => gc.depth (gc.comp.tgt g) < gc.depth y) hs
                  (gc.depth_tgt g))
            have h1 : gc.depth (gc.comp.tgt g) < k + 1 :=
              Nat.lt_of_lt_of_le hlt (Nat.succ_le_succ heqd)
            have h2 : (¬ gc.winAux k (gc.comp.tgt g)) ↔ ¬ gc.winAux e (gc.comp.tgt g) :=
              (ihk g hs).not.trans (ihe g hs).symm.not
            exact ⟨fun ⟨_, hn⟩ => ⟨hlt, h2.mp hn⟩,
              fun ⟨_, hn⟩ => ⟨h1, h2.mpr hn⟩⟩
          have hEx : (∃ g : gc.comp.gen, gc.comp.src g = x ∧
              gc.depth (gc.comp.tgt g) < k + 1 ∧ ¬ gc.winAux k (gc.comp.tgt g)) ↔
            (∃ g : gc.comp.gen, gc.comp.src g = x ∧
              gc.depth (gc.comp.tgt g) < e + 1 ∧ ¬ gc.winAux e (gc.comp.tgt g)) :=
            ⟨fun ⟨g, hs, h1, h2⟩ => ⟨g, hs, (hopt g hs).mp ⟨h1, h2⟩⟩,
              fun ⟨g, hs, h1, h2⟩ => ⟨g, hs, (hopt g hs).mpr ⟨h1, h2⟩⟩⟩
          have e1 : gc.winAux (k + 1) x ↔
              (∃ g : gc.comp.gen, gc.comp.src g = x ∧
                gc.depth (gc.comp.tgt g) < k + 1 ∧ ¬ gc.winAux k (gc.comp.tgt g)) :=
            Eq.subst (motive := fun P => (gc.winAux (k + 1) x ↔ P)) (gc.winAux_succ k x)
              Iff.rfl
          have e2 : gc.winAux (gc.depth x) x ↔
              (∃ g : gc.comp.gen, gc.comp.src g = x ∧
                gc.depth (gc.comp.tgt g) < e + 1 ∧ ¬ gc.winAux e (gc.comp.tgt g)) :=
            Eq.subst (motive := fun n => (gc.winAux n x ↔
              (∃ g : gc.comp.gen, gc.comp.src g = x ∧
                gc.depth (gc.comp.tgt g) < e + 1 ∧ ¬ gc.winAux e (gc.comp.tgt g))))
              he.symm
              (Eq.subst (motive := fun P => (gc.winAux (e + 1) x ↔ P))
                (gc.winAux_succ e x) Iff.rfl)
          exact e1.trans (hEx.trans e2.symm))

-- Reference: the `WinLoseTree.value` pattern of #10: the win predicate is
-- `winAux` at one plus the depth.
/-- The **mover-win predicate** of a graded game computad at `x`. -/
def GradedGameComputad.Win (gc : GradedGameComputad) (x : gc.comp.obj) : Prop :=
  gc.winAux (gc.depth x + 1) x

-- Reference: computation step of `Win`; `rfl` only in this primitive
-- definitional lemma.
/-- Primitive definitional lemma: `Win x = winAux (depth x + 1) x`. -/
theorem GradedGameComputad.win_def (gc : GradedGameComputad) (x : gc.comp.obj) :
    gc.Win x = gc.winAux (gc.depth x + 1) x := rfl

-- Reference: [Conway], ch. 0 (the normal-play recursion), UPGRADED to the
-- whole class of graded game computads: `Win x` iff some generator out of
-- `x` leads to a loss. Proved from `winAux_of_le` + `winAux_succ`; no
-- finiteness or decidability is assumed.
/-- **The recursion equation at the computad level**: for every object `x`
of every graded game computad, the mover wins at `x` iff some move out of
`x` leads to a position where the mover loses. -/
theorem GradedGameComputad.win_equation (gc : GradedGameComputad) (x : gc.comp.obj) :
    gc.Win x ↔ ∃ g : gc.comp.gen, gc.comp.src g = x ∧ ¬ gc.Win (gc.comp.tgt g) := by
  have h1 : gc.winAux (gc.depth x + 1) x =
      ∃ g : gc.comp.gen, gc.comp.src g = x ∧ gc.depth (gc.comp.tgt g) < gc.depth x + 1 ∧
        ¬ gc.winAux (gc.depth x) (gc.comp.tgt g) := gc.winAux_succ (gc.depth x) x
  have hdrop : (∃ g : gc.comp.gen, gc.comp.src g = x ∧
      gc.depth (gc.comp.tgt g) < gc.depth x + 1 ∧ ¬ gc.winAux (gc.depth x) (gc.comp.tgt g)) ↔
      (∃ g : gc.comp.gen, gc.comp.src g = x ∧ ¬ gc.winAux (gc.depth x) (gc.comp.tgt g)) :=
    ⟨fun ⟨g, hs, _, h⟩ => ⟨g, hs, h⟩,
      fun ⟨g, hs, h⟩ => ⟨g, hs,
        Nat.lt_succ_of_le (Nat.le_of_lt (Eq.subst
          (motive := fun y => gc.depth (gc.comp.tgt g) < gc.depth y) hs (gc.depth_tgt g))),
        h⟩⟩
  have hwin : ∀ g : gc.comp.gen, gc.comp.src g = x →
      ((¬ gc.winAux (gc.depth x) (gc.comp.tgt g)) ↔ ¬ gc.Win (gc.comp.tgt g)) :=
    fun g hs => by
      have hle : gc.depth (gc.comp.tgt g) ≤ gc.depth x := Nat.le_of_lt (Eq.subst
        (motive := fun y => gc.depth (gc.comp.tgt g) < gc.depth y) hs (gc.depth_tgt g))
      have h2 : gc.winAux (gc.depth x) (gc.comp.tgt g) ↔
          gc.winAux (gc.depth (gc.comp.tgt g)) (gc.comp.tgt g) :=
        gc.winAux_of_le (gc.depth x) (gc.comp.tgt g) hle
      have h3 : gc.Win (gc.comp.tgt g) ↔
          gc.winAux (gc.depth (gc.comp.tgt g)) (gc.comp.tgt g) :=
        ((gc.winAux_of_le (gc.depth (gc.comp.tgt g) + 1) (gc.comp.tgt g)
          (Nat.le_add_right _ 1)).symm.trans (Eq.subst
            (motive := fun P => (gc.Win (gc.comp.tgt g) ↔ P)) (gc.win_def (gc.comp.tgt g))
            Iff.rfl).symm).symm
      exact h2.not.trans h3.symm.not
  have hEx : (∃ g : gc.comp.gen, gc.comp.src g = x ∧
      ¬ gc.winAux (gc.depth x) (gc.comp.tgt g)) ↔
      (∃ g : gc.comp.gen, gc.comp.src g = x ∧ ¬ gc.Win (gc.comp.tgt g)) :=
    ⟨fun ⟨g, hs, h⟩ => ⟨g, hs, (hwin g hs).mp h⟩,
      fun ⟨g, hs, h⟩ => ⟨g, hs, (hwin g hs).mpr h⟩⟩
  exact (Eq.subst (motive := fun P => (gc.Win x ↔ P)) (gc.win_def x) Iff.rfl).trans
    ((Eq.subst (motive := fun P => (gc.winAux (gc.depth x + 1) x ↔ P)) h1 Iff.rfl).trans
      (hdrop.trans hEx))

end BoringLab
