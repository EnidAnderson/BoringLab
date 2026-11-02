/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import BoringLab.Lisp.Sexpr
import BoringLab.Doctrine.Doctrine

/-!
# Macros as computadic rewriting: the Common Lisp function/macro distinction

The LAB LISP line, making the hint literal: the rules of Common Lisp and its
distinction between **functions** and **macros** mirror computadic
rewriting. Read at the polygraph level (per the human's direction — a refined,
well-typed explanation of the Lisp macro system):

* **functions** are the 1-cells (generators) of a computad
  `lispComputad arityOf`: one object (the single sort `expr`), one generator
  per function name, port typing = arity (the port monoid is `ℕ` with `+`);
* **macros** are generators *together with a declared rewrite move*: a
  `MacroDef` (pattern, expansion — [Graham] ch. 7) declares the move
  `call-path ⇄ expansion-path` in `macroDoctrine`, i.e. macro expansion is a
  2-cell / declared move between parallel paths — exactly the
  `Doctrine`/`GeometricSequent` shape of the GL line
  (`BoringLab.Doctrine.Geometric`);
* the falsifiable shadow: a declared macro move is inverted in the
  doctrine-localization (`macroCall_inverted`) — expansion is an isomorphism
  in the localized (quotient) theory, mirroring `macroexpand` being a
  semantics-preserving transformation (ANSI CL §3.1.2.1: `macroexpand`
  returns an equivalent form).

Scope honesty: this is the *typed, data-level* shadow of the macro system —
pattern matching, backquote, and hygiene (variable capture, [Graham]
ch. 9) are declared out of scope here, recorded in the module docstring of
each declaration that omits them.

## References
* [Graham] P. Graham, *On Lisp: Advanced Techniques for Common Lisp*,
  Prentice Hall, 1993, ISBN 0130305529 — ch. 7 "Macros" (a macro is a
  function that returns an expression; expansion as program
  transformation), §7.4 (`macroexpand`/`macroexpand-1` for testing
  expansions), ch. 9 (variable capture, the declared-out-of-scope part).
* [ANSI CL] American National Standards Institute, *ANSI INCITS 226-1994
  (R1999) Common Lisp*, §3.1.2.1 (`macroexpand`: expansion returns a form
  equivalent under evaluation).
* [Mimram] S. Mimram, *Polygraphs: from rewriting to higher categories*,
  arXiv:2312.00429, LMCS 21(3) (2025), Definition 3.5 (2-polygraph: generators
  plus relations between parallel paths — macros as declared relations).
* [Burroni] A. Burroni, Theoret. Comput. Sci. 126 (1994), 257–291.
-/

universe u

namespace BoringLab

open CategoryTheory

/-! ## The computad of a Lisp signature: functions as 1-cells -/

-- Reference: [Graham], ch. 2 (functions are defined by `defun` with a
-- parameter list — the arity); the port-typing discipline of
-- `BoringLab.Doctrine.Computad` (LAB A2.0).
-- REVIEW(citation): pin the exact chapter/section of [Graham] in review.
/-- The **computad of a Lisp signature**: one object (the sort `expr`,
carried by `PUnit`), one generator per function name (`String`), and port
typing = arity — the port monoid is `ℕ` with `+`, a generator of arity `n`
consumes the port word `[n]` and produces `[1]` (one expression). The arity
function is explicit data (STYLE §2.3), never instance-chosen. -/
def lispComputad (arityOf : String → ℕ) : Computad where
  port := ℕ
  portMul := fun a b => a + b
  portOne := 0
  portMul_assoc := fun a b c => (Nat.add_assoc a b c).symm
  portMul_left_one := fun a => Nat.zero_add a
  portMul_right_one := fun a => Nat.add_zero a
  obj := PUnit
  gen := String
  src := fun _ => PUnit.unit
  tgt := fun _ => PUnit.unit
  leftPorts := fun g => [arityOf g]
  rightPorts := fun _ => [1]

-- Reference: [Graham], ch. 7 (a macro call is a list whose head is the
-- macro name); [McCarthy] (S-expressions).
-- REVIEW(citation): pin the exact section of [Graham] ch. 7 in review.
/-- The **path of an S-expression** in the Lisp computad: an atom is the
one-generator path of its symbol; a list is the composite of its elements'
paths (all objects are the single sort `expr`). -/
def lispPath (arityOf : String → ℕ) :
    Sexpr → (lispComputad arityOf).Path PUnit.unit PUnit.unit
  | .atom a => (lispComputad arityOf).toPath ⟨a, rfl, rfl⟩
  | .list [] => Quiver.Path.nil
  | .list (x :: xs) => (lispPath arityOf x).comp (lispPath arityOf (.list xs))

-- Reference: computation steps of `lispPath` (the named equation lemmas
-- `lispPath.eq_1`/`eq_2`/`eq_3`; the equation compiler compiles `lispPath`
-- by well-founded recursion, so the steps are these lemmas, not `rfl`).
/-- The path of an atom is its one-generator path. -/
theorem lispPath_atom (arityOf : String → ℕ) (a : String) :
    lispPath arityOf (.atom a) = (lispComputad arityOf).toPath ⟨a, rfl, rfl⟩ :=
  lispPath.eq_1 arityOf a

-- Reference: computation step of `lispPath` (`lispPath.eq_2`).
/-- The path of the empty list is the empty path. -/
theorem lispPath_list_nil (arityOf : String → ℕ) :
    lispPath arityOf (.list []) = Quiver.Path.nil := lispPath.eq_2 arityOf

-- Reference: computation step of `lispPath` (`lispPath.eq_3`).
/-- The path of a nonempty list is the composite head-then-rest. -/
theorem lispPath_list_cons (arityOf : String → ℕ) (x : Sexpr) (xs : List Sexpr) :
    lispPath arityOf (.list (x :: xs)) =
      (lispPath arityOf x).comp (lispPath arityOf (.list xs)) := lispPath.eq_3 arityOf x xs

/-! ## Macros: declared moves between parallel paths -/

-- Reference: [Graham], ch. 7 "Macros" (a `defmacro` binds a name to a
-- pattern and an expansion — `macroexpand` computes the expansion); ANSI CL
-- §3.1.2.1.
-- REVIEW(citation): pin the exact section of [Graham] ch. 7 in review.
/-- A **macro definition**, as data: a name, a call pattern, and its expansion
(both S-expressions). Pattern matching, backquote, and hygiene are out of
scope (declared; [Graham] ch. 9 treats capture). -/
structure MacroDef where
  /-- The macro name (head of the call). -/
  name : String
  /-- The call pattern, e.g. `(when cond body)`. -/
  pattern : Sexpr
  /-- The expansion, e.g. `(if cond (progn body))`. -/
  expansion : Sexpr

-- Reference: [Mimram], Definition 3.5 (a 2-polygraph adds relations between
-- parallel paths); [Graham], ch. 7 (expansion as a rewrite of the call); the
-- GL.0 reading of `EnidAnderson/BoringLab#14` (rules as geometric sequents).
-- REVIEW(citation): as on `MacroDef`.
/-- The **macro doctrine**: the Lisp computad together with the declared
rewrite moves — for each macro `m`, the call path `toPath ⟨m.name, …⟩` is
moved to the expansion path `lispPath m.expansion`. (The `match` on the
`PUnit` endpoints reduces every path to the single sort `expr`.) -/
def macroDoctrine (arityOf : String → ℕ) (macros : List MacroDef) : Doctrine where
  computad := lispComputad arityOf
  move := fun {X Y} p q =>
    match X, Y, p, q with
    | PUnit.unit, PUnit.unit, p', q' =>
        ∃ (m : MacroDef) (_hm : m ∈ macros),
          p' = (lispComputad arityOf).toPath ⟨m.name, rfl, rfl⟩ ∧
          q' = lispPath arityOf m.expansion

-- Reference: [Graham], ch. 7; as the `misereQuotient_move_self` pattern of
-- LAB A2.0 (a declared move is witnessed by membership).
/-- A macro rule is a declared move of the macro doctrine: the call path
moves to the expansion path. -/
theorem macroRule_is_move (arityOf : String → ℕ) (macros : List MacroDef)
    (m : MacroDef) (hm : m ∈ macros) :
    (macroDoctrine arityOf macros).move
      ((lispComputad arityOf).toPath ⟨m.name, rfl, rfl⟩) (lispPath arityOf m.expansion) :=
  ⟨m, hm, rfl, rfl⟩

-- Reference: [Gabriel–Zisman], Chapter I (inversion in the localization), via
-- `Doctrine.declared_move_inverted` (LAB A2.0); the `macroexpand`-as-
-- semantics-preserving reading (ANSI CL §3.1.2.1).
-- REVIEW(citation): as on `macroRule_is_move`.
/-- **Falsifiable shadow**: the call path of every declared macro is
inverted in the doctrine-localization — expansion is an isomorphism in the
localized theory. -/
theorem macroCall_inverted (arityOf : String → ℕ) (macros : List MacroDef)
    (m : MacroDef) (hm : m ∈ macros) :
    IsIso ((macroDoctrine arityOf macros).moveClass.Q.map
      ((lispComputad arityOf).toPath ⟨m.name, rfl, rfl⟩)) ∧
    IsIso ((macroDoctrine arityOf macros).moveClass.Q.map (lispPath arityOf m.expansion)) :=
  Doctrine.declared_move_inverted (macroDoctrine arityOf macros) _ _
    (macroRule_is_move arityOf macros m hm)

-- Reference: [Graham], ch. 7 vs ch. 2 (macros are not functions: they
-- receive unevaluated arguments and return code); the data-level shadow:
-- the `isMacro` tag on a name.
/-- The **macro/function distinction as data**: `isMacro macros g` is true
exactly when `g` is the name of a declared macro (functions are the
generators without a declared move). -/
def isMacro (macros : List MacroDef) (g : String) : Bool :=
  (macros.map MacroDef.name).any fun n => n == g

-- Reference: core `List.any_eq_true` + `List.mem_map`; [Graham], ch. 7.
/-- A declared macro's name carries the macro tag. -/
theorem isMacro_of_mem (macros : List MacroDef) (m : MacroDef) (hm : m ∈ macros) :
    isMacro macros m.name = true :=
  List.any_eq_true.mpr ⟨m.name, List.mem_map.mpr ⟨m, hm, rfl⟩, beq_self_eq_true m.name⟩

/-! ## Toy: the `when` macro of [Graham], ch. 7 -/

-- Reference: [Graham], ch. 7 (the `when` macro: `(when c b)` ≡
-- `(if c (progn b))`); REVIEW(citation): as on `whenPattern`.
/-- The toy macro definition: `when`. -/
def whenMacro : MacroDef := ⟨"when", whenPattern, whenExpansion⟩

-- Reference: as on `whenMacro`.
/-- The toy macro list. -/
def toyMacros : List MacroDef := [whenMacro]

-- Reference: [Graham], ch. 7, §7.4 (`macroexpand` prints the expansion);
-- the path lengths are the computable shadow of the expansion's shape.
#eval (isMacro toyMacros "when", isMacro toyMacros "if",
  (lispPath (fun _ => 2) whenMacro.pattern).length,
  (lispPath (fun _ => 2) whenMacro.expansion).length)

end BoringLab
