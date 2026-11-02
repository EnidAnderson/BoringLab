/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import BoringLab.Lisp.Expand

/-!
# Hygiene: variable capture as data (the ch. 9 hole of the LISP line)

The declared out-of-scope item of ticket #68, now landed at data level:
[Graham] ch. 9's variable capture, as a decidable check on `Sexpr`s.

* `sexprAtoms` — the atoms (symbols) occurring in an S-expression;
* `introduced` — the atoms of the expansion that are NOT pattern atoms
  (the macro-introduced symbols — in real Common Lisp these are
  package-qualified/fresh, ANSI CL §3.1.2.1.1; here they are checked
  directly);
* `hygienicCall` — the hygiene condition: no macro-introduced symbol
  occurs in the call (capture-freedom of the one-step expansion);
* the toy: `when` is hygienic on its own pattern call (`hygienic_when`),
  printed by `#eval`.

Scope honesty: this is the syntactic shadow of capture — argument
substitution (backquote) remains the declared hole (see
`BoringLab.Lisp.Expand`).

## References
* [Graham] P. Graham, *On Lisp*, Prentice Hall, 1993, ISBN 0130305529,
  ch. 9 "Variable Capture" (the problem and the gensym cure).
* [ANSI CL] ANSI INCITS 226-1994 (R1999) *Common Lisp*, §3.1.2.1.1
  (macro expansion; symbol capture rules).
* Program register: ticket #68 (LAB LISP.0).
-/

namespace BoringLab

/-! ## Atoms of an S-expression -/

-- Reference: [McCarthy] 1960 (the atoms of an S-expression); recursion on
-- the `Sexpr`, concatenating with `foldl (· ++ ·)` (computable; `List.flatMap`
-- is noncomputable at the pin — see #41's `concatMap` note).
/-- The **atoms** (symbols) occurring in an S-expression, as a list. -/
def sexprAtoms : Sexpr → List String
  | .atom a => [a]
  | .list l => (l.map sexprAtoms).foldl (fun acc x => acc ++ x) []

-- Reference: computation steps of `sexprAtoms` (the named equation lemmas
-- `sexprAtoms.eq_1`/`eq_2`; the equation compiler compiles `sexprAtoms` by
-- well-founded recursion through `List.map`, so the steps are these lemmas,
-- not `rfl`).
/-- The atoms of an atom. -/
theorem sexprAtoms_atom (a : String) : sexprAtoms (.atom a) = [a] := sexprAtoms.eq_1 a

-- Reference: computation step of `sexprAtoms` (`sexprAtoms.eq_2`).
/-- The atoms of a list. -/
theorem sexprAtoms_list (l : List Sexpr) :
    sexprAtoms (.list l) = (l.map sexprAtoms).foldl (fun acc x => acc ++ x) [] :=
  sexprAtoms.eq_2 l

/-! ## Hygiene as a decidable check -/

-- Reference: core `List.filter`/`List.all`/`List.any` with `beq` on
-- `String`.
/-- The **introduced symbols** of a macro: expansion atoms that are not
pattern atoms. -/
def introduced (m : MacroDef) : List String :=
  (sexprAtoms m.expansion).filter fun a =>
    if (sexprAtoms m.pattern).any fun p => a == p then false else true

-- Reference: [Graham], ch. 9; ANSI CL §3.1.2.1.1 — capture-freedom: no
-- introduced symbol occurs in the call.
/-- The **hygiene check**: macro `m` is capture-free on `call` iff no
introduced symbol of `m` occurs among the call's atoms. -/
def hygienicCall (m : MacroDef) (call : Sexpr) : Bool :=
  (introduced m).all fun a =>
    (sexprAtoms call).all fun c => !(a == c)

-- Reference: computation step: a macro whose expansion uses only pattern
-- atoms introduces nothing.
/-- If the expansion's atoms are all pattern atoms, nothing is introduced. -/
theorem introduced_eq_nil_of_subset (m : MacroDef)
    (h : ∀ a ∈ sexprAtoms m.expansion, a ∈ sexprAtoms m.pattern) :
    introduced m = [] := by
  unfold introduced
  exact List.filter_eq_nil_iff.mpr fun a ha => by
    have ha' : a ∈ sexprAtoms m.pattern := h a ha
    have hany : (sexprAtoms m.pattern).any (fun p => a == p) = true :=
      List.any_eq_true.mpr ⟨a, ha', beq_self_eq_true a⟩
    have hpa : (if (sexprAtoms m.pattern).any (fun p => a == p) then false else true) = false :=
      Eq.subst (motive := fun b => (if b then false else true) = false) hany.symm rfl
    intro htrue
    exact Bool.false_ne_true (hpa.symm.trans htrue)

-- Reference: from `introduced_eq_nil_of_subset`: a nothing-introduced macro
-- is hygienic on every call (core `List.all_nil`).
/-- A macro that introduces no symbols is hygienic on every call. -/
theorem hygienicCall_of_subset (m : MacroDef)
    (h : ∀ a ∈ sexprAtoms m.expansion, a ∈ sexprAtoms m.pattern) (call : Sexpr) :
    hygienicCall m call = true :=
  Eq.subst (motive := fun l => l.all (fun a => (sexprAtoms call).all fun c => !(a == c)) = true)
    (introduced_eq_nil_of_subset m h).symm rfl

/-! ## Toy: `when` is hygienic on its own pattern call -/

-- Reference: [Graham], ch. 7 (the `when` toy); its expansion introduces
-- `if` and `progn`, which do not occur in the pattern call `(when cond
-- body)` — printed by `#eval` below; the general check is `hygienicCall`.
-- TEMPORARY SORRY: the closed `String` `beq` computations are not
-- kernel-`rfl`-reliable at the pin.
-- PEELING PLAN: switch the toy's atoms from `String` to an inductive
-- `Sym` (clean decidable equality), then `hygienic_when` closes by
-- `rfl`-peeling of `introduced`/`hygienicCall` on the closed lists.
-- Next named lemma: `Sym` + `sexprAtomsSym`.
/-- The toy `when` macro is hygienic on its pattern call. -/
theorem hygienic_when : hygienicCall whenMacro whenPattern = true := by
  sorry

-- Reference: ticket #68, acceptance: `#eval` prints the introduced symbols
-- of `when` and the hygiene check on the pattern call.
#eval (introduced whenMacro, hygienicCall whenMacro whenPattern,
  sexprAtoms (macroexpand1 toyMacros whenPattern))

end BoringLab
