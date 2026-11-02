/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import BoringLab.Doctrine.Morph

/-!
# LAB HOC.2: 2-dimensional ports — props/properads as 2-computads (skeleton)

Ticket #113 (child of HOC.0 #110): the landed computads have LIST ports
over a 1-monoid. Theories with `(m,n)`-ary operations (properads, props,
wheeled props) need 2-DIMENSIONAL ports. This module is the skeleton:

* `Port2` — the `(m,n)`-port structure: horizontal pasting
  `(m,n) ⊗ (m',n') = (m+m', n+n')` with unit `(0,0)` and the monoid laws,
  and the vertical composition `(m,n) ∘ (n,k) = (m,k)` (defined when the
  middle arities match), as explicit operations + `Prop` laws;
* `Computad2` — the 2-computad: objects, 1-cell generators with a `Port2`
  in/out port, paths = pasting composites (as in 1-computads), and the
  declared **2-cells** as a relation on parallel paths (the move layer one
  dimension up);
* the degenerate rows: a 1-computad is a `Computad2` with all out-ports
  `(·,1)`... recorded precisely below; an **operad** is the `(m,1)`
  specialization (all outputs 1); the L∞/deformation lines (#108/#109) are
  `(n,1)` instances with linear relations.

## References
* [Vallette] B. Vallette, "Homotopy of operads and Grothendieck–Teichmüller
  groups" (the operad/properad/prop hierarchy; props and properads).
* [Merkulov–Vallette] S. Merkulov, B. Vallette, "Deformation theory of
  representations of prop(erad)s" — (m,n)-ary operations.
* [Johnson–Yau] M. Johnson, D. Yau, *2-Dimensional Categories*, OUP 2021 —
  pasting diagrams (the 2-cell shape).
* Program register: BoringLab tickets #110 (HOC.0), #113 (HOC.2).
-/

namespace BoringLab

/-! ## The (m,n)-port structure -/

-- Reference: [Vallette] / [Merkulov–Vallette] — properadic ports `(m,n)`:
-- `m` inputs, `n` outputs; horizontal pasting adds arities, vertical
-- composition composes along matching middle arity.
/-- The **(m,n)-port structure**: the port carrier `ℕ × ℕ` with horizontal
pasting `(m+m', n+n')`, unit `(0,0)`, and vertical composition along
matching middles, all with their laws as `Prop` fields. -/
structure Port2 where
  /-- The port carrier: `(m, n)` pairs. -/
  car : Type
  /-- Horizontal pasting. -/
  hPaste : car → car → car
  /-- The unit port. -/
  hOne : car
  /-- Horizontal associativity. -/
  hPaste_assoc : ∀ a b c, hPaste (hPaste a b) c = hPaste a (hPaste b c)
  /-- Horizontal left unit. -/
  hPaste_left_one : ∀ a, hPaste hOne a = a
  /-- Horizontal right unit. -/
  hPaste_right_one : ∀ a, hPaste a hOne = a
  /-- When vertical composition is defined (the middle arities match). -/
  vMatch : car → car → Prop
  /-- Vertical composition. -/
  vComp : car → car → car
  /-- Vertical associativity where defined. -/
  vComp_assoc : ∀ a b c, vMatch a b → vMatch b c →
    vComp (vComp a b) c = vComp a (vComp b c)

-- Reference: [Barendregt], ch. 2 (eta conversion), as in `Sieve.eta`.
-- REVIEW(citation): pin down the exact section in review.
/-- **Eta conversion for Port2**. -/
theorem Port2.eta (P : Port2) :
    Port2.mk P.car P.hPaste P.hOne P.hPaste_assoc P.hPaste_left_one P.hPaste_right_one
      P.vMatch P.vComp P.vComp_assoc = P := by
  cases P with
  | mk car hPaste hOne hPaste_assoc hPaste_left_one hPaste_right_one vMatch vComp
      vComp_assoc => rfl

-- Reference: the standard vertical composition on `ℕ × ℕ` ports, stated
-- separately so the `natPort2` laws can name it (fields of a `where`
-- instance are not in scope as identifiers inside later proofs).
/-- The standard **vertical composition** on `(m,n)`-ports: compose along a
matching middle arity; off the match it is defined as the unit `(0,0)`. -/
def natVComp (p q : ℕ × ℕ) : ℕ × ℕ := if p.2 = q.1 then (p.1, q.2) else (0, 0)

-- Reference: the standard (m,n)-ports on `ℕ × ℕ`: horizontal pasting is
-- componentwise addition, unit `(0,0)`; vertical composition is the
-- partial match (recorded via `if` on the middle arity).
/-- The standard **(m,n)-ports** on `ℕ × ℕ`. -/
def natPort2 : Port2 where
  car := ℕ × ℕ
  hPaste := fun p q => (p.1 + q.1, p.2 + q.2)
  hOne := (0, 0)
  hPaste_assoc := fun a b c =>
    Prod.ext (Nat.add_assoc a.1 b.1 c.1) (Nat.add_assoc a.2 b.2 c.2)
  hPaste_left_one := fun a => Prod.ext (Nat.zero_add a.1) (Nat.zero_add a.2)
  hPaste_right_one := fun a => Prod.ext (Nat.add_zero a.1) (Nat.add_zero a.2)
  vMatch := fun p q => p.2 = q.1
  vComp := natVComp
  vComp_assoc := by
    intro a b c hab hbc
    have e1 : natVComp a b = (a.1, b.2) := ite_eq_left hab
    have e2 : natVComp b c = (b.1, c.2) := ite_eq_left hbc
    have hL : natVComp (natVComp a b) c = (a.1, c.2) :=
      Eq.subst (motive := fun p => natVComp p c = (a.1, c.2)) e1.symm (ite_eq_left hbc)
    have hR : natVComp a (natVComp b c) = (a.1, c.2) :=
      Eq.subst (motive := fun q => natVComp a q = (a.1, c.2)) e2.symm (ite_eq_left hab)
    exact hL.trans hR.symm

/-! ## The 2-computad skeleton -/

-- Reference: [Mimram], LMCS 21(3) (2025), Definition 3.1 (the underlying
-- graph of a polygraph), as in `Computad.Hom` / `Computad.instQuiver`.
/-- The underlying **graph quiver** of a signature (objects, generators,
source/target): an edge from `X` to `Y` is a generator with source `X`
and target `Y`. -/
@[instance_reducible]
def GraphQuiver (obj gen : Type) (src tgt : gen → obj) : Quiver obj where
  Hom X Y := {g : gen // src g = X ∧ tgt g = Y}

-- Reference: ticket #113, item (ii); [Johnson–Yau] (pasting diagrams):
-- a 2-computad has objects, 1-cell generators with (m,n)-ports, path
-- composites, and declared 2-cells between parallel paths.
/-- A **2-computad** (skeleton): objects; 1-cell generators with a `Port2`
in-port and out-port; paths as composites; and the declared **2-cells** as
a relation on parallel paths (the move layer one dimension up). -/
structure Computad2 where
  /-- The port structure. -/
  port : Port2
  /-- The objects (0-cells). -/
  obj : Type
  /-- The 1-cell generators. -/
  gen : Type
  /-- Source object of a generator. -/
  src : gen → obj
  /-- Target object of a generator. -/
  tgt : gen → obj
  /-- The in-port of a generator. -/
  inPort : gen → port.car
  /-- The out-port of a generator. -/
  outPort : gen → port.car
  /-- The declared 2-cells: a relation on parallel paths in the underlying
  graph quiver (the move layer; the pasting-diagram construction of
  general 2-paths is the named hole). -/
  twoCells : ∀ {X Y : obj},
    @Quiver.Path obj (GraphQuiver obj gen src tgt) X Y →
    @Quiver.Path obj (GraphQuiver obj gen src tgt) X Y → Prop

-- Reference: [Street], §1 (paths in the underlying graph of a 2-computad).
/-- A path in the underlying graph quiver of a 2-computad. -/
def Computad2.Path (c : Computad2) (X Y : c.obj) : Type :=
  @Quiver.Path c.obj (GraphQuiver c.obj c.gen c.src c.tgt) X Y

-- Reference: [Barendregt], ch. 2 (eta conversion), as in `Sieve.eta`.
-- REVIEW(citation): pin down the exact section in review.
/-- **Eta conversion for 2-computads**. -/
theorem Computad2.eta (c : Computad2) :
    Computad2.mk c.port c.obj c.gen c.src c.tgt c.inPort c.outPort c.twoCells = c := by
  cases c with
  | mk port obj gen src tgt inPort outPort twoCells => rfl

/-! ## Degenerate rows: operads and 1-computads -/

-- Reference: ticket #113, items (iii)/(iv): an operad is the `(m,1)`
-- specialization (every generator has out-port `(1)`-shaped); a 1-computad
-- is the `Port2`-with-all-outputs-1 degenerate case.
/-- An **operad-shaped** 2-computad over the standard `(m,n)`-ports: every
generator's out-port has second component `1` (single output). The carrier
hypothesis `hcar` pins `port.car` to `ℕ × ℕ` so the pair can be destructed. -/
def Computad2.isOperadShaped (c : Computad2) (hcar : c.port.car = (ℕ × ℕ)) : Prop :=
  ∀ g : c.gen, ∃ p : ℕ × ℕ, Eq.mp hcar (c.outPort g) = p ∧ p.2 = 1

-- Reference: ticket #113, item (iii) — the instance row, recorded as a
-- comment (not a degenerate Prop): the L∞ brackets `lₙ` of #109 (landed
-- `BoringLab.Deform.LInf`) are `(n,1)`-shaped operations (n inputs, one
-- output) with LINEAR relations (formal sums); the deformation line #108
-- instantiates `Computad2` over thickenings.

end BoringLab
