/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import BoringLab.Lisp.Expand
import BoringLab.Games.Trace
import BoringLab.Doctrine.Computad

/-!
# The universal anchor: Lisp syntax, computad semantics, game protocols

This module connects the three layers of the lab around the **computad**
(1-polygraph) as the universal anchor:

* **Syntax (Lisp layer)**: `lispComputad arityOf` has a single object (the
  sort `expr`) and one generator per symbol; `lispPath` reads every
  s-expression as a path. Macro calls are rewrite moves between parallel
  paths (`callDoctrine`); one-step expansion `macroexpand1` is a declared
  move (proved below: `macroexpand1_is_declared_move`).
* **Semantics (computad layer)**: a `Computad` is a port-typed graph; its
  paths are the composites (Mimram, Definition 3.1; Street §1). A `Doctrine`
  declares moves between parallel paths (Mimram, Definition 3.5 — the
  sequent/rewrite reading).
* **Runtime (games layer)**: a two-player protocol is a `WinLoseTree`; its
  **protocol computad** `WinLoseTree.toComputad` has positions as objects
  and legal moves as generators, so a **play is exactly a path from the
  root** (proved below: `playFrom_iff_path`).

The universal reading: every protocol's runtime is a path in its protocol
computad, and every Lisp specification denotes rewrite moves in the Lisp
computad — one anchor type (`Computad`/`Doctrine`) on both sides.

NOTE (pin `v4.35.0-rc3`): the consecutive-chain predicate is
`List.IsChain` (the old name `List.Chain'` no longer exists), while
`List.Pairwise` is the all-pairs relation at this pin — so
`WinLoseTree.IsPlayPrefix` (Pairwise) is strictly stronger than
`IsPlayFrom` (IsChain), and only the implication
`isPlayPrefix_isPlayFrom` holds in general.

## References
* [Mimram] S. Mimram, *Polygraphs: from rewriting to higher categories*,
  arXiv:2312.00429, LMCS 21(3) (2025), Definitions 3.1 and 3.5.
* [Street] R. Street, *The algebra of oriented simplexes*, J. Pure Appl.
  Algebra 49 (1987), §1 (computads; paths in the underlying graph).
* [Shafer–Vovk] G. Shafer and V. Vovk, *Game-Theoretic Foundations for
  Probability and Finance*, Wiley, 2019 (DOI 10.1002/9781118548035),
  Chapter 1 (a protocol is a tree of positions; a play is a path from the
  root).
* [Conway] J. H. Conway, *On Numbers and Games*, 2nd ed., A K Peters, 2000,
  Chapter 0 (games as trees of options).
* [Graham] P. Graham, *On Lisp*, Prentice Hall, 1993, ch. 7 (macros as
  syntactic rewrites).
-/

universe u

namespace BoringLab

open CategoryTheory

/-! ## The protocol computad of a win/lose tree -/

-- Reference: [Shafer–Vovk], Chapter 1 (a protocol is a tree of positions,
-- moves are the edges); [Mimram], Definition 3.1 (the underlying graph of a
-- 1-polygraph); [Street], §1. Ports are trivial (`PUnit`) — a move carries no
-- port word.
/-- The **protocol computad** of a win/lose tree: objects are the positions,
generators are the legal moves (a generator is a pair `(p, q)` with
`q ∈ moves p`, source `p`, target `q`). -/
def WinLoseTree.toComputad (t : WinLoseTree.{u}) : Computad.{u} where
  port := PUnit
  portMul := fun _ _ => PUnit.unit
  portOne := PUnit.unit
  portMul_assoc := fun _ _ _ => rfl
  portMul_left_one := fun _ => rfl
  portMul_right_one := fun _ => rfl
  obj := t.pos
  gen := {e : t.pos × t.pos // e.2 ∈ t.moves e.1}
  src := fun e => e.1.1
  tgt := fun e => e.1.2
  leftPorts := fun _ => []
  rightPorts := fun _ => []

-- Reference: [Conway], Chapter 0; core `List.IsChain` (consecutive relation)
-- at pin `v4.35.0-rc3`, as the play reading of `WinLoseTree.IsPlayPrefix` but
-- from an arbitrary start position.
/-- A **play from `x`**: a nonempty list of positions starting at `x` whose
consecutive positions are moves. -/
def WinLoseTree.IsPlayFrom (t : WinLoseTree.{u}) (x : t.pos) (l : List t.pos) :
    Prop :=
  l.head? = some x ∧ List.IsChain (fun a b => b ∈ t.moves a) l

-- Reference: `WinLoseTree.IsPlayPrefix` unfolded together with core
-- `List.Pairwise.isChain` (at this pin `List.Pairwise` is the all-pairs
-- relation, which implies the consecutive `List.IsChain`; the converse
-- would need transitivity of `moves` and is false in general).
/-- A play prefix is a play from the root (one direction only: `Pairwise`
is stronger than `IsChain` at this pin). -/
theorem WinLoseTree.isPlayPrefix_isPlayFrom (t : WinLoseTree.{u})
    (l : List t.pos) :
    t.IsPlayPrefix l → t.IsPlayFrom t.root l :=
  fun h => ⟨h.1, List.Pairwise.isChain h.2⟩

-- Reference: [Street], §1 (paths in the underlying graph of a computad).
/-- The **object list** of a path in a computad: the start object, then the
target of each edge. -/
def Computad.pathObjList {c : Computad.{u}} {X Y : c.obj} :
    Quiver.Path X Y → List c.obj
  | .nil => [X]
  | .cons p g => pathObjList p ++ [c.tgt g.1]

-- Reference: computation step of `pathObjList`.
/-- The object list of the empty path is the singleton start. -/
theorem Computad.pathObjList_nil {c : Computad.{u}} {X : c.obj} :
    pathObjList (.nil : Quiver.Path X X) = [X] := rfl

-- Reference: computation step of `pathObjList`.
/-- The object list of a cons path appends the edge target. -/
theorem Computad.pathObjList_cons {c : Computad.{u}} {X Y Z : c.obj}
    (p : Quiver.Path X Y) (g : Y ⟶ Z) :
    pathObjList (p.cons g) = pathObjList p ++ [c.tgt g.1] := rfl

-- Reference: `pathObjList_nil`/`pathObjList_cons`; induction on the path.
/-- The object list of a path is nonempty (it starts at the source). -/
theorem Computad.pathObjList_ne_nil {c : Computad.{u}} {X Y : c.obj}
    (p : Quiver.Path X Y) : pathObjList p ≠ [] := by
  induction p with
  | nil => exact List.cons_ne_nil X []
  | cons p g ih =>
      exact fun h => ih (List.append_eq_nil_iff.mp h).1


-- Reference: `pathObjList_cons`, core `List.getLast?_append`,
-- `List.getLast?_singleton`, `Option.some_or`; induction on the path.
/-- The last object of the object list of a path is the path's target. -/
theorem Computad.pathObjList_getLast? {c : Computad.{u}} {X Y : c.obj}
    (p : Quiver.Path X Y) : (pathObjList p).getLast? = some Y := by
  induction p with
  | nil => exact List.getLast?_singleton
  | cons p g ih =>
      exact (congrArg List.getLast? (pathObjList_cons p g)).trans
        (List.getLast?_append.trans
          ((congrArg (fun o => o.or (pathObjList p).getLast?)
              (List.getLast?_singleton (a := c.tgt g.1))).trans
            (Option.some_or.trans (congrArg some g.2.2))))

-- Reference: core `List.drop` computation; case split on the list (the
-- statement is false for `l = []`).
/-- Dropping one element of `l ++ [x]` (with `l` nonempty) drops one element
of `l` and keeps the appended singleton. -/
theorem dropOne_append_singleton {α : Type u} (l : List α) (x : α) (hne : l ≠ []) :
    (l ++ [x]).drop 1 = l.drop 1 ++ [x] := by
  cases l with
  | nil => exact absurd rfl hne
  | cons a as => rfl

-- Reference: `Quiver.Hom.toPath` is `Path.cons Path.nil` ([Street], §1);
-- computation steps `pathObjList_cons`/`pathObjList_nil`.
/-- The object list of a one-edge path is the two endpoints. -/
theorem Computad.pathObjList_toPath {c : Computad.{u}} {X Y : c.obj} (g : X ⟶ Y) :
    pathObjList (Quiver.Hom.toPath g) = [X, Y] := by
  change pathObjList (Quiver.Path.cons Quiver.Path.nil g) = [X, Y]
  exact (pathObjList_cons (Quiver.Path.nil : Quiver.Path X X) g).trans
    ((congrArg (fun l => l ++ [c.tgt g.1]) pathObjList_nil).trans
      (congrArg (fun z => [X] ++ [z]) (show c.tgt g.1 = Y from g.2.2)))

-- Reference: [Mac Lane], Chapter I (composition of paths); core
-- `Quiver.Path.comp_nil`, `Quiver.Path.comp_cons`, `List.append_assoc`,
-- `dropOne_append_singleton`; induction on the second path.
/-- The object list of a composite path: the first path's objects, then the
second path's objects without its (duplicate) first. -/
theorem Computad.pathObjList_comp {c : Computad.{u}} {X Y Z : c.obj}
    (p : Quiver.Path X Y) (q : Quiver.Path Y Z) :
    pathObjList (p.comp q) = pathObjList p ++ (pathObjList q).drop 1 := by
  induction q with
  | nil =>
      have h1 : pathObjList (p.comp Quiver.Path.nil) = pathObjList p :=
        congrArg pathObjList (Quiver.Path.comp_nil p)
      have h2 : (pathObjList (Quiver.Path.nil : Quiver.Path Y Y)).drop 1 = [] := rfl
      exact h1.trans
        (((congrArg (List.append (pathObjList p)) h2).trans (List.append_nil _)).symm)
  | cons q e ih =>
      have e1 : pathObjList (p.comp (q.cons e)) =
          (pathObjList p ++ (pathObjList q).drop 1) ++ [c.tgt e.1] :=
        (congrArg pathObjList (Quiver.Path.comp_cons p q e)).trans
          ((pathObjList_cons (p.comp q) e).trans
            (congrArg (fun l => l ++ [c.tgt e.1]) ih))
      have e2 : (pathObjList p ++ (pathObjList q).drop 1) ++ [c.tgt e.1] =
          pathObjList p ++ ((pathObjList q).drop 1 ++ [c.tgt e.1]) :=
        List.append_assoc _ _ _
      have e3 : (pathObjList q).drop 1 ++ [c.tgt e.1] =
          (pathObjList q ++ [c.tgt e.1]).drop 1 :=
        (dropOne_append_singleton (pathObjList q) (c.tgt e.1)
          (pathObjList_ne_nil q)).symm
      have e4 : pathObjList p ++ (pathObjList q ++ [c.tgt e.1]).drop 1 =
          pathObjList p ++ (pathObjList (q.cons e)).drop 1 :=
        congrArg (fun l => pathObjList p ++ l.drop 1) (pathObjList_cons q e)
      exact e1.trans (e2.trans ((congrArg (List.append (pathObjList p)) e3).trans e4))

-- Reference: core `List.head?_append`, `List.IsChain.append`,
-- `Computad.pathObjList_getLast?`; induction on the path. For a protocol
-- computad an edge `p ⟶ q` is a legal move (`q ∈ moves p`) by the
-- generator's defining subtype. NOTE: objects are stated as
-- `(t.toComputad).obj` (defeq to `t.pos`) so that the `Quiver` instance of
-- the protocol computad is found by unification.
/-- The object list of a path in a tree's protocol computad is a play from the
path's source (consecutive positions are moves). -/
theorem WinLoseTree.pathObjList_isPlayFrom (t : WinLoseTree.{u})
    {X Y : (t.toComputad).obj} (p : Quiver.Path X Y) :
    t.IsPlayFrom X (Computad.pathObjList (c := t.toComputad) p) := by
  induction p with
  | nil => exact ⟨List.head?_singleton, List.IsChain.singleton X⟩
  | cons p g ih =>
      have he : Computad.pathObjList (c := t.toComputad) (p.cons g) =
          Computad.pathObjList p ++ [t.toComputad.tgt g.1] :=
        Computad.pathObjList_cons p g
      have hh : (Computad.pathObjList (c := t.toComputad) (p.cons g)).head? = some X :=
        (congrArg List.head? he).trans
          (List.head?_append.trans
            ((congrArg (fun o => o.or [t.toComputad.tgt g.1].head?) ih.1).trans
              (Option.some_or)))
      have hmem : t.toComputad.tgt g.1 ∈ t.moves (t.toComputad.src g.1) := g.1.2
      have hc : List.IsChain (fun a b => b ∈ t.moves a)
          (Computad.pathObjList (c := t.toComputad) (p.cons g)) :=
        Eq.subst (motive := fun l => List.IsChain (fun a b => b ∈ t.moves a) l) he.symm
          (List.IsChain.append ih.2 (List.IsChain.singleton (t.toComputad.tgt g.1))
            (fun x hx y hy => by
              have hx' : x = t.toComputad.src g.1 :=
                ((Option.mem_some_iff).mp
                  (Eq.subst (motive := fun o => x ∈ o)
                    (Computad.pathObjList_getLast? p) hx)).symm
                  |>.trans g.2.1.symm
              have hy' : y = t.toComputad.tgt g.1 :=
                ((Option.mem_some_iff).mp
                  (Eq.subst (motive := fun o => y ∈ o)
                    (List.head?_singleton (a := t.toComputad.tgt g.1)) hy)).symm
              exact Eq.subst (motive := fun w => y ∈ t.moves w) hx'.symm
                (Eq.subst (motive := fun z => z ∈ t.moves (t.toComputad.src g.1)) hy'.symm
                  hmem)))
      exact ⟨hh, hc⟩

-- Reference: `IsPlayFrom` unfolded; `List.head?_cons`, `List.isChain_cons`;
-- induction on the play list (generalizing the start position), prepending
-- the edge with `Quiver.Hom.toPath` and `Quiver.Path.comp`, and
-- `Computad.pathObjList_comp`/`Computad.pathObjList_toPath` for the object
-- list of the composite.
/-- Auxiliary induction for `pathOfPlayFrom`: the statement with the start
position quantified inside the induction on the list. -/
theorem WinLoseTree.pathOfPlayFrom_aux (t : WinLoseTree.{u}) :
    ∀ (l : List (t.toComputad).obj) (x : (t.toComputad).obj), t.IsPlayFrom x l →
      ∃ (Y : (t.toComputad).obj) (p : Quiver.Path x Y),
        Computad.pathObjList (c := t.toComputad) p = l := by
  intro l
  induction l with
  | nil =>
      intro x h
      exact absurd
        (Eq.subst (motive := fun o => o = some x) List.head?_nil h.1)
        (Option.some_ne_none x).symm
  | cons a l ih =>
      intro x h
      cases l with
      | nil =>
          have ha : a = x := Option.some.inj (List.head?_cons.symm.trans h.1)
          exact ⟨x, Quiver.Path.nil,
            Computad.pathObjList_nil.trans (congrArg List.singleton ha.symm)⟩
      | cons b rest =>
          have ha : a = x := Option.some.inj (List.head?_cons.symm.trans h.1)
          have hch := List.isChain_cons.mp h.2
          have hmem : b ∈ (b :: rest).head? :=
            Eq.subst (motive := fun o => b ∈ o) (List.head?_cons (a := b) (l := rest))
              (Option.mem_some_iff.mpr rfl)
          have hR : b ∈ t.moves a := hch.1 b hmem
          have hplay : t.IsPlayFrom b (b :: rest) := ⟨List.head?_cons, hch.2⟩
          obtain ⟨Y, q, hq⟩ := ih b hplay
          have g' : (t.toComputad).Hom x b :=
            ⟨⟨(x, b), Eq.subst (motive := fun z => b ∈ t.moves z) ha hR⟩, rfl, rfl⟩
          exact ⟨Y, (Quiver.Hom.toPath g').comp q,
            (Computad.pathObjList_comp (Quiver.Hom.toPath g') q).trans
              ((congrArg (fun l => l ++ (Computad.pathObjList (c := t.toComputad) q).drop 1)
                  (Computad.pathObjList_toPath g')).trans
                ((congrArg (List.append [x, b])
                    ((congrArg (fun l => l.drop 1) hq).trans
                      (List.drop_one.trans List.tail_cons))).trans
                  (congrArg (fun z => z :: b :: rest) ha).symm))⟩

-- Reference: `pathOfPlayFrom_aux` applied pointwise.
/-- Every play from `x` is a path in the protocol computad whose object list
is the play. -/
theorem WinLoseTree.pathOfPlayFrom (t : WinLoseTree.{u}) {x : (t.toComputad).obj}
    (l : List (t.toComputad).obj) (h : t.IsPlayFrom x l) :
    ∃ (Y : (t.toComputad).obj) (p : Quiver.Path x Y),
      Computad.pathObjList (c := t.toComputad) p = l :=
  pathOfPlayFrom_aux t l x h

-- Reference: `pathObjList_isPlayFrom` + `pathOfPlayFrom`.
/-- **Plays are paths**: a list of positions is a play from `x` in the tree
iff it is the object list of a path from `x` in the protocol computad. -/
theorem WinLoseTree.playFrom_iff_path (t : WinLoseTree.{u}) (x : (t.toComputad).obj)
    (l : List (t.toComputad).obj) :
    t.IsPlayFrom x l ↔
      ∃ (Y : (t.toComputad).obj) (p : Quiver.Path x Y),
        Computad.pathObjList (c := t.toComputad) p = l :=
  ⟨fun h => pathOfPlayFrom t l h,
   fun h => by
    obtain ⟨Y, p, hp⟩ := h
    exact Eq.subst (motive := fun l' => t.IsPlayFrom x l') hp
      (pathObjList_isPlayFrom t p)⟩

/-! ## Lisp as protocol specification: expansion steps are declared moves -/

-- Reference: computation step of `macroexpand1` on a macro-cons list and an
-- atom-headed call (the inner `match` on the name comparison is exposed;
-- [ANSI CL] §3.1.2.1.1).
/-- The one-step expansion of an atom-headed call against a cons macro list
exposes the name-comparison match. -/
theorem macroexpand1_cons_atom (m : MacroDef) (rest : List MacroDef)
    (name : String) (tl : List Sexpr) :
    macroexpand1 (m :: rest) (.list (.atom name :: tl)) =
      match m.name == name with
      | true => m.expansion
      | false => macroexpand1 rest (.list (.atom name :: tl)) := rfl

-- Reference: `macroexpand1`'s definition (a call headed by a declared macro
-- name expands in one step); induction on the macro list, cases on the form;
-- `macroexpand1_none`, `macroexpand1_cons_atom`, `macroexpand1_macro`,
-- `callRule_is_move`, `beq_iff_eq`; [ANSI CL] §3.1.2.1.1; [Mimram],
-- Definition 3.5.
/-- Auxiliary induction for `macroexpand1_is_declared_move`: the statement
with the form quantified inside the induction on the macro list (in the
non-matching branch the move of the tail doctrine is transported to the
cons doctrine by `List.mem_cons_of_mem`). -/
theorem macroexpand1_ne_is_move_aux (arityOf : String → ℕ) :
    ∀ (macros : List MacroDef) (s : Sexpr), macroexpand1 macros s ≠ s →
      (callDoctrine arityOf macros).move (lispPath arityOf s)
        (lispPath arityOf (macroexpand1 macros s)) := by
  intro macros
  induction macros with
  | nil =>
      intro s h
      exact absurd (macroexpand1_none s) h
  | cons m rest ih =>
      intro s h
      cases s with
      | atom a => exact absurd rfl h
      | list l =>
          cases l with
          | nil => exact absurd rfl h
          | cons hd tl =>
              cases hd with
              | atom name =>
                  have he := macroexpand1_cons_atom m rest name tl
                  cases hb : m.name == name with
                  | true =>
                      have hred : (match m.name == name with
                          | true => m.expansion
                          | false => macroexpand1 rest (.list (.atom name :: tl))) =
                          m.expansion :=
                        Eq.subst (motive := fun b =>
                            (match b with
                            | true => m.expansion
                            | false => macroexpand1 rest (.list (.atom name :: tl))) =
                            m.expansion) hb.symm rfl
                      have hexp : macroexpand1 (m :: rest) (.list (.atom name :: tl)) =
                          m.expansion := he.trans hred
                      have hnm : m.name = name := beq_iff_eq.mp hb
                      exact Eq.subst
                        (motive := fun e => (callDoctrine arityOf (m :: rest)).move
                          (lispPath arityOf (.list (.atom name :: tl)))
                          (lispPath arityOf e))
                        hexp.symm
                        (Eq.subst
                          (motive := fun n => (callDoctrine arityOf (m :: rest)).move
                            (lispPath arityOf (.list (.atom n :: tl)))
                            (lispPath arityOf m.expansion))
                          hnm
                          (callRule_is_move arityOf (m :: rest) m List.mem_cons_self tl))
                  | false =>
                      have hred : (match m.name == name with
                          | true => m.expansion
                          | false => macroexpand1 rest (.list (.atom name :: tl))) =
                          macroexpand1 rest (.list (.atom name :: tl)) :=
                        Eq.subst (motive := fun b =>
                            (match b with
                            | true => m.expansion
                            | false => macroexpand1 rest (.list (.atom name :: tl))) =
                            macroexpand1 rest (.list (.atom name :: tl))) hb.symm rfl
                      have hexp : macroexpand1 (m :: rest) (.list (.atom name :: tl)) =
                          macroexpand1 rest (.list (.atom name :: tl)) := he.trans hred
                      have h' : macroexpand1 rest (.list (.atom name :: tl)) ≠
                          .list (.atom name :: tl) :=
                        Eq.subst (motive := fun e => e ≠ .list (.atom name :: tl)) hexp h
                      obtain ⟨m', hm', args', hp, hq⟩ := ih _ h'
                      exact Eq.subst
                        (motive := fun e => (callDoctrine arityOf (m :: rest)).move
                          (lispPath arityOf (.list (.atom name :: tl)))
                          (lispPath arityOf e))
                        hexp.symm ⟨m', List.mem_cons_of_mem m hm', args', hp, hq⟩
              | list _ => exact absurd rfl h

-- Reference: `macroexpand1_ne_is_move_aux` applied pointwise; [ANSI CL]
-- §3.1.2.1.1; [Mimram], Definition 3.5.
/-- **One expansion step is a declared move**: if `macroexpand1` changes the
form, the change is a declared move of the call-level expansion doctrine. -/
theorem macroexpand1_is_declared_move (arityOf : String → ℕ) (macros : List MacroDef)
    (s : Sexpr) (h : macroexpand1 macros s ≠ s) :
    (callDoctrine arityOf macros).move (lispPath arityOf s)
      (lispPath arityOf (macroexpand1 macros s)) :=
  macroexpand1_ne_is_move_aux arityOf macros s h

-- Reference: [Shafer–Vovk], Chapter 1 (a protocol specification: a signature,
-- rewrite rules, and a start position); [Graham], ch. 7.
/-- A **protocol specification in Lisp**: a symbol arity signature, the macro
rules (rewrites), and the start expression. -/
structure ProtocolSpec where
  /-- The arity of each symbol (the port word of its generator). -/
  arity : String → ℕ
  /-- The macro rules (rewrite moves of the Lisp computad). -/
  macros : List MacroDef
  /-- The start expression. -/
  start : Sexpr

-- Reference: iteration of `macroexpand1`.
/-- The **expansion trace** of a protocol spec: the iterated one-step
expansion of the start expression. -/
def ProtocolSpec.expand (ps : ProtocolSpec) : ℕ → Sexpr
  | 0 => ps.start
  | n + 1 => macroexpand1 ps.macros (ps.expand n)

-- Reference: computation step of `ProtocolSpec.expand`.
/-- The trace step equation. -/
theorem ProtocolSpec.expand_succ (ps : ProtocolSpec) (n : ℕ) :
    ps.expand (n + 1) = macroexpand1 ps.macros (ps.expand n) := rfl

-- Reference: `macroexpand1_is_declared_move` + `ProtocolSpec.expand_succ`;
-- [Mimram], Definition 3.5 (each rewrite step is a declared move, so the
-- trace is a path in the expansion doctrine).
/-- **Each trace step is a declared move**: the expansion trace of a protocol
spec is a path through the call-level expansion doctrine. -/
theorem ProtocolSpec.expand_step_move (ps : ProtocolSpec) (n : ℕ)
    (h : ps.expand (n + 1) ≠ ps.expand n) :
    (callDoctrine ps.arity ps.macros).move (lispPath ps.arity (ps.expand n))
      (lispPath ps.arity (ps.expand (n + 1))) := by
  have h' : macroexpand1 ps.macros (ps.expand n) ≠ ps.expand n := h
  exact Eq.subst
    (motive := fun e => (callDoctrine ps.arity ps.macros).move
      (lispPath ps.arity (ps.expand n)) (lispPath ps.arity e))
    (ProtocolSpec.expand_succ ps n).symm
    (macroexpand1_is_declared_move ps.arity ps.macros (ps.expand n) h')

end BoringLab
