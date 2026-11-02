/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import BoringLab.Lisp.Hygiene

/-!
# The `when` hygiene check, proved

Ticket #68's named hole `hygienic_when` — now PROVED in `BoringLab.Lisp.Hygiene`;
# the introduced symbols of `when` are `["if", "progn"]` (neither occurs in the pattern
`(when cond body)`), so `hygienicCall whenMacro whenPattern = true`.
Peeling: `sexprAtoms` compiles well-founded (through `List.map`), so its
closed values are computed by the equation lemmas `sexprAtoms.eq_2`/`eq_1`
transported by `Eq.subst`; once the atom lists are concrete, the `filter`/
`any`/`all` steps and the `String`-literal `beq`s reduce by `rfl`.

## References
* [Graham] P. Graham, *On Lisp*, Prentice Hall, 1993, ISBN 0130305529,
  ch. 7 (the `when` toy), ch. 9 (variable capture).
* Program register: BoringLab ticket #68 (LAB LISP.0).
-/

namespace BoringLab

/-! ## Closed atom computations -/

-- Reference: computation of `sexprAtoms whenPattern`: `sexprAtoms.eq_2`
-- unfolds the `.list`, `sexprAtoms.eq_1` the atoms; the `List.map`/`foldl`/
-- `append` steps on the closed lists are `rfl`.
/-- The atoms of the `when` pattern call: `["when", "cond", "body"]`. -/
theorem whenPattern_atoms : sexprAtoms whenPattern = ["when", "cond", "body"] := by
  have h2 := sexprAtoms.eq_2 [.atom "when", .atom "cond", .atom "body"]
  exact h2.trans
    (Eq.subst
      (motive := fun A =>
        (A ++ sexprAtoms (.atom "cond")) ++ sexprAtoms (.atom "body")
          = ["when", "cond", "body"])
      (sexprAtoms.eq_1 "when").symm
      (Eq.subst
        (motive := fun B =>
          (["when"] ++ B) ++ sexprAtoms (.atom "body") = ["when", "cond", "body"])
        (sexprAtoms.eq_1 "cond").symm
        (Eq.subst
          (motive := fun C => (["when"] ++ ["cond"]) ++ C = ["when", "cond", "body"])
          (sexprAtoms.eq_1 "body").symm rfl)))

-- Reference: computation of `sexprAtoms whenExpansion`, as for the pattern
-- (the nested `.list [.atom "progn", .atom "body"]` is peeled first).
/-- The atoms of the `when` expansion: `["if", "cond", "progn", "body"]`. -/
theorem whenExpansion_atoms : sexprAtoms whenExpansion = ["if", "cond", "progn", "body"] := by
  have hIn : sexprAtoms (.list [.atom "progn", .atom "body"]) = ["progn", "body"] := by
    have h2 := sexprAtoms.eq_2 [.atom "progn", .atom "body"]
    exact h2.trans
      (Eq.subst
        (motive := fun A => A ++ sexprAtoms (.atom "body") = ["progn", "body"])
        (sexprAtoms.eq_1 "progn").symm
        (Eq.subst
          (motive := fun B => ["progn"] ++ B = ["progn", "body"])
          (sexprAtoms.eq_1 "body").symm rfl))
  have h2 := sexprAtoms.eq_2 [.atom "if", .atom "cond", .list [.atom "progn", .atom "body"]]
  exact h2.trans
    (Eq.subst
      (motive := fun A =>
        (A ++ sexprAtoms (.atom "cond"))
            ++ sexprAtoms (.list [.atom "progn", .atom "body"])
          = ["if", "cond", "progn", "body"])
      (sexprAtoms.eq_1 "if").symm
      (Eq.subst
        (motive := fun B =>
          (["if"] ++ B) ++ sexprAtoms (.list [.atom "progn", .atom "body"])
            = ["if", "cond", "progn", "body"])
        (sexprAtoms.eq_1 "cond").symm
        (Eq.subst
          (motive := fun C =>
            (["if"] ++ ["cond"]) ++ C = ["if", "cond", "progn", "body"])
          hIn.symm rfl)))

/-! ## The peeled hole -/

-- Reference: ticket #68 — the hygiene check on the pattern call, proved:
-- `introduced_whenMacro` and `hygienic_when` now live (proved) in
-- `BoringLab.Lisp.Hygiene`; this file keeps the standalone alias below,
-- transporting `introduced_whenMacro` and `whenPattern_atoms`.
/-- The `when` macro is hygienic on its own pattern call (proved). -/
theorem hygienic_when_full : hygienicCall whenMacro whenPattern = true := by
  exact Eq.subst
    (motive := fun I =>
      I.all (fun a => (sexprAtoms whenPattern).all (fun c => !(a == c))) = true)
    introduced_whenMacro.symm
    (Eq.subst
      (motive := fun P =>
        ["if", "progn"].all (fun a => P.all (fun c => !(a == c))) = true)
      whenPattern_atoms.symm rfl)

end BoringLab
