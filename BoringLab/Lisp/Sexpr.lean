/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import Mathlib.Init
import Mathlib.Data.Nat.Notation

/-!
# S-expressions as data

The syntactic substrate for the LAB LISP line (the On Lisp connection: the
macro/function distinction of Common Lisp read as computadic rewriting —
functions are 1-cells of a computad, macros are declared moves between
parallel paths; see `BoringLab.Lisp.Macro`). An S-expression here is an atom
(a symbol, carried as a `String`) or a list of S-expressions — the original
form of McCarthy.

## References
* [McCarthy] J. McCarthy, "Recursive Functions of Symbolic Expressions and
  Their Computation by Machine, Part I", *CACM* 3(4):184–195, 1960 —
  S-expressions (the `atom`/`list` dichotomy).
* [Graham] P. Graham, *On Lisp: Advanced Techniques for Common Lisp*,
  Prentice Hall, 1993, ISBN 0130305529, ch. 1–2 (Lisp data: atoms and lists;
  code as data).
* [ANSI CL] American National Standards Institute, *ANSI INCITS 226-1994
  (R1999) Common Lisp*, §3.1 (S-expressions; §3.1.2.1 `macroexpand`).
-/

namespace BoringLab

-- Reference: [McCarthy], 1960 (S-expressions: atoms and lists);
-- [Graham], ch. 1 (Lisp data).
-- REVIEW(citation): pin the exact section of [Graham] in review.
/-- An **S-expression**, as data: an atom (a symbol, carried as a `String`)
or a list of S-expressions. -/
inductive Sexpr where
  /-- A symbol atom. -/
  | atom : String → Sexpr
  /-- A parenthesized list of S-expressions. -/
  | list : List Sexpr → Sexpr
deriving Repr

-- Reference: computation step of `Sexpr.isAtom`; `rfl` only in this
-- primitive definitional lemma.
/-- The atom test, as decidable data. -/
def Sexpr.isAtom : Sexpr → Bool
  | .atom _ => true
  | .list _ => false

-- Reference: computation step of `Sexpr.isAtom`.
/-- An atom is an atom; a list is not. -/
theorem Sexpr.isAtom_atom (a : String) : Sexpr.isAtom (.atom a) = true := rfl

theorem Sexpr.isAtom_list (l : List Sexpr) : Sexpr.isAtom (.list l) = false := rfl

-- Reference: [McCarthy], 1960 (the recursive size of an S-expression).
/-- The **size** of an S-expression: atoms have size `1`, lists the sum of
their elements' sizes plus one. -/
def Sexpr.size : Sexpr → ℕ
  | .atom _ => 1
  | .list l => 1 + (l.map Sexpr.size).sum

-- Reference: computation steps of `Sexpr.size`.
/-- The size of an atom is one. -/
theorem Sexpr.size_atom (a : String) : Sexpr.size (.atom a) = 1 := Sexpr.size.eq_1 a

-- Reference: computation step of `Sexpr.size`.
/-- The size of a list. -/
theorem Sexpr.size_list (l : List Sexpr) :
    Sexpr.size (.list l) = 1 + (l.map Sexpr.size).sum := Sexpr.size.eq_2 l

/-! ## Toy: the `when` macro of [Graham], ch. 7 -/

-- Reference: [Graham], ch. 7 "Macros" (the running `when` example:
-- `(when c b)` expands to `(if c (progn b))`); ANSI CL §3.1.2.1.
-- REVIEW(citation): pin the exact figure/section of [Graham] ch. 7 in
-- review.
/-- The pattern of the toy `when` macro: `(when cond body)`. -/
def whenPattern : Sexpr :=
  .list [.atom "when", .atom "cond", .atom "body"]

-- Reference: [Graham], ch. 7 (`when` expands to `if` + `progn`).
-- REVIEW(citation): as on `whenPattern`.
/-- The expansion of the toy `when` macro: `(if cond (progn body))`. -/
def whenExpansion : Sexpr :=
  .list [.atom "if", .atom "cond", .list [.atom "progn", .atom "body"]]

-- Reference: program's own toy (the #eval witness of the line).
#eval (whenPattern, whenPattern.isAtom, whenPattern.size, whenExpansion.size)

end BoringLab
