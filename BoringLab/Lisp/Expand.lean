/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import BoringLab.Lisp.Macro

/-!
# macroexpand-1 as path rewriting: the one-step expansion of a macro call

The named next hole of ticket #68 (LAB LISP.0), built on
`BoringLab.Lisp.Macro`: the one-step macro expansion (`macroexpand-1`,
ANSI CL §3.1.2.1; [Graham] ch. 7, §7.4) as a declared move between paths.

* `macroexpand1` — the one-step expansion of an S-expression: if the head
  atom names a declared macro, the call is replaced by the macro's
  expansion. **Declared out of scope**: argument substitution (backquote)
  and hygiene — the expansion is returned as written, pattern variables
  unsubstituted; recorded honestly, [Graham] ch. 9 treats capture;
* `callDoctrine` — the doctrine whose declared moves are the CALL-level
  expansions: `lispPath (m.name args…) ⇄ lispPath m.expansion` (the bare
  macro move of `macroDoctrine` transported to call paths);
* the falsifiable shadow: `macroexpand1_move` (the expansion of a macro
  call IS a declared move) and `callCall_inverted` (it is inverted in the
  localization).

## References
* [ANSI CL] ANSI INCITS 226-1994 (R1999) *Common Lisp*, §3.1.2.1.1
  (`macroexpand-1`: one step of macro expansion; the form is returned
  unchanged if its head is not a macro name).
* [Graham] P. Graham, *On Lisp*, Prentice Hall, 1993, ISBN 0130305529,
  ch. 7, §7.4 (testing macroexpansion with `macroexpand`/`macroexpand-1`),
  ch. 9 (variable capture — declared out of scope here).
* [Mimram] S. Mimram, arXiv:2312.00429, LMCS 21(3) (2025), Definition 3.5
  (relations between parallel paths).
-/

namespace BoringLab

open CategoryTheory

/-! ## One-step expansion -/

-- Reference: [ANSI CL], §3.1.2.1.1 (`macroexpand-1`); [Graham], ch. 7
-- §7.4. NOTE (declared out of scope): no argument substitution — the
-- expansion is returned as written (backquote/hygiene are the ch. 9 hole).
/-- **One-step macro expansion** (`macroexpand-1` shadow): a call whose head
atom names the head of the macro list expands to that macro's expansion;
otherwise the form is unchanged. -/
def macroexpand1 : List MacroDef → Sexpr → Sexpr
  | [], s => s
  | m :: rest, .list (.atom name :: args) =>
      match m.name == name with
      | true => m.expansion
      | false => macroexpand1 rest (.list (.atom name :: args))
  | _ :: _, s => s

-- Reference: core `beq_self_eq_true` + `cases` on the Bool; [ANSI CL],
-- §3.1.2.1.1 (the head matches the macro name).
/-- A call headed by a declared macro expands to its expansion (one step). -/
theorem macroexpand1_macro (m : MacroDef) (rest : List MacroDef) (args : List Sexpr) :
    macroexpand1 (m :: rest) (.list (.atom m.name :: args)) = m.expansion := by
  change (match m.name == m.name with
    | true => m.expansion
    | false => macroexpand1 rest (.list (.atom m.name :: args))) = m.expansion
  cases h : m.name == m.name with
  | true => rfl
  | false => exact absurd (h.symm.trans (beq_self_eq_true m.name)) Bool.false_ne_true

-- Reference: [ANSI CL], §3.1.2.1.1 (a non-call or non-macro-headed form is
-- unchanged).
/-- A non-macro call is unchanged by one-step expansion (empty macro list). -/
theorem macroexpand1_none (s : Sexpr) : macroexpand1 [] s = s := rfl

/-! ## The call-level expansion doctrine -/

-- Reference: [Mimram], Definition 3.5; ticket #68 (macroexpand-1 as a
-- path-rewriting lemma): the declared moves are the CALL-level expansions.
/-- The **call-level expansion doctrine**: the Lisp computad with declared
moves `lispPath (m.name args…) ⇄ lispPath m.expansion` for each declared
macro `m`. -/
def callDoctrine (arityOf : String → ℕ) (macros : List MacroDef) : Doctrine where
  computad := lispComputad arityOf
  move := fun {X Y} p q =>
    match X, Y, p, q with
    | PUnit.unit, PUnit.unit, p', q' =>
        ∃ (m : MacroDef) (_hm : m ∈ macros) (args : List Sexpr),
          p' = lispPath arityOf (.list (.atom m.name :: args)) ∧
          q' = lispPath arityOf m.expansion

-- Reference: as `macroRule_is_move` (witness by membership); [ANSI CL],
-- §3.1.2.1.1.
/-- The call-level expansion of a declared macro is a declared move. -/
theorem callRule_is_move (arityOf : String → ℕ) (macros : List MacroDef)
    (m : MacroDef) (hm : m ∈ macros) (args : List Sexpr) :
    (callDoctrine arityOf macros).move
      (lispPath arityOf (.list (.atom m.name :: args)))
      (lispPath arityOf m.expansion) :=
  ⟨m, hm, args, rfl, rfl⟩

-- Reference: ticket #68 (macroexpand-1 IS a declared move): from
-- `macroexpand1_macro` + `callRule_is_move`.
/-- **macroexpand-1 is a declared move**: one-step expansion of a macro call
is a declared move of the call doctrine. -/
theorem macroexpand1_move (arityOf : String → ℕ)
    (m : MacroDef) (rest : List MacroDef) (hm : m ∈ m :: rest) (args : List Sexpr) :
    (callDoctrine arityOf (m :: rest)).move
      (lispPath arityOf (.list (.atom m.name :: args)))
      (lispPath arityOf (macroexpand1 (m :: rest) (.list (.atom m.name :: args)))) :=
  Eq.subst (motive := fun e => (callDoctrine arityOf (m :: rest)).move
      (lispPath arityOf (.list (.atom m.name :: args))) (lispPath arityOf e))
    (macroexpand1_macro m rest args).symm
    (callRule_is_move arityOf (m :: rest) m hm args)

-- Reference: [Gabriel–Zisman], Chapter I, via
-- `Doctrine.declared_move_inverted`; ANSI CL §3.1.2.1 (expansion preserves
-- semantics — the localization shadow).
/-- **Falsifiable shadow**: the expanded call path is inverted in the
call-doctrine localization. -/
theorem callCall_inverted (arityOf : String → ℕ) (macros : List MacroDef)
    (m : MacroDef) (hm : m ∈ macros) (args : List Sexpr) :
    IsIso ((callDoctrine arityOf macros).moveClass.Q.map
      (lispPath arityOf (.list (.atom m.name :: args)))) ∧
    IsIso ((callDoctrine arityOf macros).moveClass.Q.map
      (lispPath arityOf m.expansion)) :=
  Doctrine.declared_move_inverted (callDoctrine arityOf macros) _ _
    (callRule_is_move arityOf macros m hm args)

/-! ## Toy: expanding `(when cond body)` -/

-- Reference: [Graham], ch. 7 (the `when` toy); ticket #68.
/-- One-step expansion of the toy `when` call is the `if`/`progn` expansion
(closed computation after `macroexpand1_macro`). -/
theorem macroexpand1_when :
    macroexpand1 toyMacros whenPattern = whenExpansion :=
  macroexpand1_macro whenMacro [] [Sexpr.atom "cond", Sexpr.atom "body"]

-- Reference: ticket #68, acceptance: `#eval` prints the one-step expansion
-- of the toy call and its path length (the computable shadow).
#eval (macroexpand1 toyMacros whenPattern,
  (lispPath (fun _ => 2) (macroexpand1 toyMacros whenPattern)).length)

end BoringLab
