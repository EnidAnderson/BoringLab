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
-- kernel-`rfl`-reliable at the pin (verified: `rfl` fails on
-- `hygienicCall whenMacro whenPattern = true`).
-- PEELING PLAN (concrete named lemmas, all provable at the pin):
--   (1) `sexprAtoms_atoms (l : List String) : sexprAtoms (.list (l.map .atom)) = l`
--       — induction on `l` with `sexprAtoms_list`, `List.map_cons`,
--       `List.foldl_cons`/`List.foldl_nil`, `sexprAtoms_atom`;
--   (2) `string_beq_false_of_ne : s ≠ t → (s == t) = false`
--       (`beq_iff_eq` + `Bool.eq_false_iff`), with `s ≠ t` for closed strings
--       from `congrArg String.length` + `Nat.ne_of_lt` on the lengths;
--   (3) `introduced_whenMacro : introduced whenMacro = ["if", "progn"]` —
--       `List.mem_filter` + (1) + `List.any_eq_true` + the six
--       `(a == p) = false` facts of (2);
--   (4) close `hygienic_when` by `List.all_eq_true` + (3) + (1) + (2):
--       each `!(a == c)` with `a ∈ {"if","progn"}`, `c ∈ {"when","cond","body"}`
--       is `!(false) = true`.
--   Longer-term alternative (as before): switch the toy's atoms from `String`
--   to an inductive `Sym` (clean decidable equality).
 /-! ## Peeled computation lemmas for the `when` toy (ticket #68) -/

-- Reference: induction on the symbol list (`List.map_cons`, `List.map_nil`,
-- `sexprAtoms_atom`).
/-- Mapping `sexprAtoms` over a list of atoms gives the singleton lists. -/
theorem map_sexprAtoms_atom (l : List String) :
    List.map sexprAtoms (l.map Sexpr.atom) = l.map (fun a => [a]) := by
  induction l with
  | nil =>
      exact (congrArg (List.map sexprAtoms) (List.map_nil (f := Sexpr.atom))).trans
        ((List.map_nil (f := sexprAtoms)).trans (List.map_nil).symm)
  | cons a t ih =>
      exact (congrArg (List.map sexprAtoms) (List.map_cons (f := Sexpr.atom))).trans
        ((List.map_cons (f := sexprAtoms).trans
          ((congrArg (fun x => sexprAtoms (Sexpr.atom a) :: x) ih).trans
            ((congrArg (fun s => s :: t.map (fun a => [a])) (sexprAtoms_atom a)).trans
              (List.map_cons (f := fun a => [a])).symm))))

-- Reference: induction on the list, generalizing the accumulator
-- (`List.foldl_cons`, `List.foldl_nil`, `List.append_assoc`, `List.append_nil`,
-- `List.flatten_cons`, `List.flatten_nil`).
/-- Folding append over a list of lists is the accumulator plus the flattening. -/
theorem foldl_append_flatten (l : List (List String)) :
    ∀ acc, l.foldl (fun a b => a ++ b) acc = acc ++ l.flatten := by
  induction l with
  | nil =>
      intro acc
      exact (List.foldl_nil).trans (List.append_nil acc).symm
  | cons a t ih =>
      intro acc
      exact (List.foldl_cons).trans
        ((ih (acc ++ a)).trans
          ((List.append_assoc acc a t.flatten).trans
            (congrArg (fun x => acc ++ x) List.flatten_cons)))

-- Reference: induction on the symbol list (`List.map_cons`, `List.map_nil`,
-- `List.flatten_cons`, `List.cons_append`, `List.nil_append`).
/-- Flattening a list of singletons is the original list. -/
theorem flatten_map_singleton (l : List String) :
    (l.map (fun a => [a])).flatten = l := by
  induction l with
  | nil => exact (congrArg List.flatten (List.map_nil (f := fun a => [a]))).trans rfl
  | cons a t ih =>
      exact (congrArg List.flatten (List.map_cons (f := fun a => [a]))).trans
        ((List.flatten_cons).trans
          (((List.cons_append).trans
            (congrArg (fun y => a :: y) (List.nil_append _))).trans
            (congrArg (fun x => a :: x) ih)))

-- Reference: `sexprAtoms_list`, `map_sexprAtoms_atom`, `foldl_append_flatten`,
-- `flatten_map_singleton`.
/-- The atoms of a list of atoms are the atoms themselves. -/
theorem sexprAtoms_atoms (l : List String) :
    sexprAtoms (.list (l.map Sexpr.atom)) = l :=
  (sexprAtoms_list (l.map Sexpr.atom)).trans
    ((congrArg (fun m => m.foldl (fun acc x => acc ++ x) [])
        (map_sexprAtoms_atom l)).trans
      ((foldl_append_flatten (l.map (fun a => [a])) []).trans
        ((List.nil_append _).trans (flatten_map_singleton l))))

-- Reference: `String.length` congruence; `Nat.ne_of_lt` on the lengths.
/-- Closed strings of different lengths are distinct. -/
theorem string_ne_of_length_ne {s t : String} (h : s.length ≠ t.length) : s ≠ t :=
  fun he => h (congrArg String.length he)

-- Reference: `beq_iff_eq` (LawfulBEq String) + `Bool.eq_false_iff`.
/-- Distinct strings have `beq` false. -/
theorem string_beq_false_of_ne {s t : String} (h : s ≠ t) : (s == t) = false :=
  Bool.eq_false_iff.mpr (fun hb => h (beq_iff_eq.mp hb))

-- Reference: `sexprAtoms_atoms` on the concrete pattern list (definitional
-- `List.map` on the literal).
/-- The atoms of the `when` pattern are `when`, `cond`, `body`. -/
theorem sexprAtoms_whenPattern : sexprAtoms whenPattern = ["when", "cond", "body"] :=
  Eq.subst (motive := fun s => sexprAtoms s = ["when", "cond", "body"]) rfl
    (sexprAtoms_atoms ["when", "cond", "body"])

-- Reference: `sexprAtoms_list`, then the concrete `List.map` (definitional)
-- rewritten pointwise by `sexprAtoms_atom` and `sexprAtoms_atoms`, and
-- `foldl_append_flatten` + concrete `List.flatten` (definitional).
/-- The atoms of the `when` expansion are `if`, `cond`, `progn`, `body`. -/
theorem sexprAtoms_whenExpansion :
    sexprAtoms whenExpansion = ["if", "cond", "progn", "body"] := by
  have h0 : List.map sexprAtoms
      [Sexpr.atom "if", Sexpr.atom "cond", .list [Sexpr.atom "progn", Sexpr.atom "body"]]
      = [sexprAtoms (Sexpr.atom "if"), sexprAtoms (Sexpr.atom "cond"),
          sexprAtoms (.list [Sexpr.atom "progn", Sexpr.atom "body"])] := rfl
  have h1 : sexprAtoms (Sexpr.atom "if") = ["if"] := sexprAtoms_atom "if"
  have h2 : sexprAtoms (Sexpr.atom "cond") = ["cond"] := sexprAtoms_atom "cond"
  have h3 : sexprAtoms (.list [Sexpr.atom "progn", Sexpr.atom "body"]) = ["progn", "body"] :=
    Eq.subst (motive := fun s => sexprAtoms s = ["progn", "body"]) rfl
      (sexprAtoms_atoms ["progn", "body"])
  have emap : List.map sexprAtoms
      [Sexpr.atom "if", Sexpr.atom "cond", .list [Sexpr.atom "progn", Sexpr.atom "body"]]
      = [["if"], ["cond"], ["progn", "body"]] :=
    h0.trans ((congrArg (fun a => [a, sexprAtoms (Sexpr.atom "cond"),
        sexprAtoms (.list _)] ) h1).trans
      ((congrArg (fun b => [["if"], b, sexprAtoms (.list _)] ) h2).trans
        (congrArg (fun c => [["if"], ["cond"], c]) h3)))
  exact (sexprAtoms_list _).trans
    ((congrArg (fun m => m.foldl (fun acc x => acc ++ x) []) emap).trans
      ((foldl_append_flatten _ []).trans ((List.nil_append _).trans rfl)))

-- Reference: `congrArg String.length` + `Nat.succ_inj` peeling (`String.length`
-- of a literal computes by `rfl`).
/-- `"if" ≠ "when"` (lengths 2 and 4). -/
theorem string_if_ne_when : ("if" : String) ≠ "when" :=
  fun h => Nat.ne_of_lt (Nat.lt_add_of_pos_right (n := 2) (k := 2) (Nat.succ_pos 1))
    (congrArg String.length h)

-- Reference: as `string_if_ne_when`.
/-- `"if" ≠ "cond"`. -/
theorem string_if_ne_cond : ("if" : String) ≠ "cond" := by
  intro h
  exact (Nat.ne_of_lt (Nat.lt_add_of_pos_right (n := 2) (k := 2) (Nat.succ_pos 1)))
    (congrArg String.length h)

-- Reference: as `string_if_ne_when`.
/-- `"if" ≠ "body"`. -/
theorem string_if_ne_body : ("if" : String) ≠ "body" := by
  intro h
  exact (Nat.ne_of_lt (Nat.lt_add_of_pos_right (n := 2) (k := 2) (Nat.succ_pos 1)))
    (congrArg String.length h)

-- Reference: as `string_if_ne_when` (lengths 5 and 4; four `Nat.succ_inj`
-- steps reach `1 = 0`).
/-- `"progn" ≠ "when"`. -/
theorem string_progn_ne_when : ("progn" : String) ≠ "when" :=
  fun h => Nat.ne_of_lt (Nat.lt_add_of_pos_right (n := 4) (k := 1) (Nat.succ_pos 0))
    (congrArg String.length h).symm

-- Reference: as `string_progn_ne_when`.
/-- `"progn" ≠ "cond"`. -/
theorem string_progn_ne_cond : ("progn" : String) ≠ "cond" := by
  intro h
  exact (Nat.ne_of_lt (Nat.lt_add_of_pos_right (n := 4) (k := 1) (Nat.succ_pos 0)))
    (congrArg String.length h).symm

-- Reference: as `string_progn_ne_when`.
/-- `"progn" ≠ "body"`. -/
theorem string_progn_ne_body : ("progn" : String) ≠ "body" := by
  intro h
  exact (Nat.ne_of_lt (Nat.lt_add_of_pos_right (n := 4) (k := 1) (Nat.succ_pos 0)))
    (congrArg String.length h).symm

-- Reference: `string_beq_false_of_ne`.
/-- `("if" == "when") = false`. -/
theorem beq_if_when : (("if" : String) == "when") = false :=
  string_beq_false_of_ne string_if_ne_when

-- Reference: as `beq_if_when`.
/-- `("if" == "cond") = false`. -/
theorem beq_if_cond : (("if" : String) == "cond") = false :=
  string_beq_false_of_ne string_if_ne_cond

-- Reference: as `beq_if_when`.
/-- `("if" == "body") = false`. -/
theorem beq_if_body : (("if" : String) == "body") = false :=
  string_beq_false_of_ne string_if_ne_body

-- Reference: as `beq_if_when`.
/-- `("progn" == "when") = false`. -/
theorem beq_progn_when : (("progn" : String) == "when") = false :=
  string_beq_false_of_ne string_progn_ne_when

-- Reference: as `beq_if_when`.
/-- `("progn" == "cond") = false`. -/
theorem beq_progn_cond : (("progn" : String) == "cond") = false :=
  string_beq_false_of_ne string_progn_ne_cond

-- Reference: as `beq_if_when`.
/-- `("progn" == "body") = false`. -/
theorem beq_progn_body : (("progn" : String) == "body") = false :=
  string_beq_false_of_ne string_progn_ne_body

-- Reference: `List.any_eq_false`; membership by `List.mem_cons`; the
-- `beq_*` facts.
/-- A symbol matching no element of the list has `any` false. -/
theorem any_eq_false_of_forall_ne {a : String} {l : List String}
    (h : ∀ p ∈ l, (a == p) = false) :
    l.any (fun p => a == p) = false :=
  (List.any_eq_false).mpr fun p hp ht => Bool.false_ne_true ((h p hp).symm.trans ht)

-- Reference: `any_eq_false_of_forall_ne` + the `beq_if_*` facts.
/-- `"if"` occurs in no pattern atom. -/
theorem any_if_pattern : (["when", "cond", "body"] : List String).any (fun p => ("if" == p))
    = false :=
  any_eq_false_of_forall_ne fun p hp => by
    rcases List.mem_cons.mp hp with rfl | hp'
    · exact beq_if_when
    · rcases List.mem_cons.mp hp' with rfl | hp''
      · exact beq_if_cond
      · rcases List.mem_cons.mp hp'' with rfl | hp'''
        · exact beq_if_body
        · exact absurd hp''' List.not_mem_nil

-- Reference: `any_eq_false_of_forall_ne` + the `beq_progn_*` facts.
/-- `"progn"` occurs in no pattern atom. -/
theorem any_progn_pattern : (["when", "cond", "body"] : List String).any
    (fun p => ("progn" == p)) = false :=
  any_eq_false_of_forall_ne fun p hp => by
    rcases List.mem_cons.mp hp with rfl | hp'
    · exact beq_progn_when
    · rcases List.mem_cons.mp hp' with rfl | hp''
      · exact beq_progn_cond
      · rcases List.mem_cons.mp hp'' with rfl | hp'''
        · exact beq_progn_body
        · exact absurd hp''' List.not_mem_nil

-- Reference: `List.any_eq_true` + `List.mem_cons_of_mem` + `List.mem_cons_self` +
-- `beq_self_eq_true`.
/-- `"cond"` occurs in the pattern atoms. -/
theorem any_cond_pattern : (["when", "cond", "body"] : List String).any (fun p => ("cond" == p))
    = true :=
  (List.any_eq_true).mpr
    ⟨"cond", List.mem_cons_of_mem "when" List.mem_cons_self, beq_self_eq_true "cond"⟩

-- Reference: as `any_cond_pattern`.
/-- `"body"` occurs in the pattern atoms. -/
theorem any_body_pattern : (["when", "cond", "body"] : List String).any (fun p => ("body" == p))
    = true :=
  (List.any_eq_true).mpr
    ⟨"body", List.mem_cons_of_mem "when" (List.mem_cons_of_mem "cond" List.mem_cons_self),
      beq_self_eq_true "body"⟩
/-- The `when` macro introduces exactly `if` and `progn`. -/
theorem introduced_whenMacro : introduced whenMacro = ["if", "progn"] := by
  show (sexprAtoms whenExpansion).filter
      (fun a => if (sexprAtoms whenPattern).any (fun p => a == p) then false else true)
      = ["if", "progn"]
  -- rewrite the two atom lists
  have eE : sexprAtoms whenExpansion = ["if", "cond", "progn", "body"] := sexprAtoms_whenExpansion
  have eP : sexprAtoms whenPattern = ["when", "cond", "body"] := sexprAtoms_whenPattern
  refine Eq.subst (motive := fun l => l.filter
      (fun a => if (sexprAtoms whenPattern).any (fun p => a == p) then false else true)
      = ["if", "progn"]) eE.symm (Eq.subst
    (motive := fun l => (["if", "cond", "progn", "body"] : List String).filter
      (fun a => if l.any (fun p => a == p) then false else true) = ["if", "progn"]) eP.symm ?_)
  -- now compute the filter on the concrete lists: the predicate at `a` is
  -- `if (pattern-any (a == ·)) then false else true`
  have pif : (if ((["when", "cond", "body"] : List String).any (fun p => ("if" == p)))
      then false else true) = true :=
    Eq.subst (motive := fun b => (if b then false else true) = true) any_if_pattern
      rfl
  have pcond : (if ((["when", "cond", "body"] : List String).any (fun p => ("cond" == p)))
      then false else true) = false :=
    Eq.subst (motive := fun b => (if b then false else true) = false) any_cond_pattern
      rfl
  have pprogn : (if ((["when", "cond", "body"] : List String).any (fun p => ("progn" == p)))
      then false else true) = true :=
    Eq.subst (motive := fun b => (if b then false else true) = true) any_progn_pattern
      rfl
  have pbody : (if ((["when", "cond", "body"] : List String).any (fun p => ("body" == p)))
      then false else true) = false :=
    Eq.subst (motive := fun b => (if b then false else true) = false) any_body_pattern
      rfl
  exact (List.filter_cons).trans
    ((ite_eq_left pif).trans (congrArg (fun t => "if" :: t)
      ((List.filter_cons).trans
        ((ite_eq_right (fun h => Bool.false_ne_true (pcond.symm.trans h))).trans
          ((List.filter_cons).trans
            ((ite_eq_left pprogn).trans (congrArg (fun t => "progn" :: t)
              ((List.filter_cons).trans
                ((ite_eq_right (fun h => Bool.false_ne_true (pbody.symm.trans h))).trans List.filter_nil)))))))))

-- Reference: `List.all_cons`/`List.all_nil` + `beq_if_*` + `Bool.not_false`;
-- stepwise computation of the `all` over the pattern atoms (bottom-up).
/-- The `all`-check of `"if"` against the pattern atoms is `true`. -/
theorem all_pattern_not_beq_if : (["when", "cond", "body"] : List String).all
    (fun c => !(("if" : String) == c)) = true := by
  have g1 : !((("if" : String) == "when")) = true :=
    (congrArg Bool.not beq_if_when).trans Bool.not_false
  have g2 : !(("if" == "cond")) = true :=
    (congrArg Bool.not beq_if_cond).trans Bool.not_false
  have g3 : !(("if" == "body")) = true :=
    (congrArg Bool.not beq_if_body).trans Bool.not_false
  have s3 : (["body"] : List String).all (fun c => !(("if" : String) == c)) = true :=
    (List.all_cons).trans ((congrArg (fun b => b && ([] : List String).all
        (fun c => !(("if" : String) == c))) g3).trans
      ((Bool.true_and _).trans List.all_nil))
  have s2 : (["cond", "body"] : List String).all (fun c => !(("if" : String) == c))
      = true :=
    (List.all_cons).trans ((congrArg (fun b => b && (["body"] : List String).all
        (fun c => !(("if" : String) == c))) g2).trans
      ((Bool.true_and _).trans s3))
  exact (List.all_cons).trans ((congrArg (fun b => b && (["cond", "body"] : List String).all
      (fun c => !(("if" : String) == c))) g1).trans
    ((Bool.true_and _).trans s2))

-- Reference: as `all_pattern_not_beq_if`, with the `beq_progn_*` facts.
/-- The `all`-check of `"progn"` against the pattern atoms is `true`. -/
theorem all_pattern_not_beq_progn : (["when", "cond", "body"] : List String).all
    (fun c => !(("progn" : String) == c)) = true := by
  have g1 : !(("progn" == "when")) = true :=
    (congrArg Bool.not beq_progn_when).trans Bool.not_false
  have g2 : !(("progn" == "cond")) = true :=
    (congrArg Bool.not beq_progn_cond).trans Bool.not_false
  have g3 : !(("progn" == "body")) = true :=
    (congrArg Bool.not beq_progn_body).trans Bool.not_false
  have s3 : (["body"] : List String).all (fun c => !(("progn" : String) == c)) = true :=
    (List.all_cons).trans ((congrArg (fun b => b && ([] : List String).all
        (fun c => !(("progn" : String) == c))) g3).trans
      ((Bool.true_and _).trans List.all_nil))
  have s2 : (["cond", "body"] : List String).all (fun c => !(("progn" : String) == c))
      = true :=
    (List.all_cons).trans ((congrArg (fun b => b && (["body"] : List String).all
        (fun c => !(("progn" : String) == c))) g2).trans
      ((Bool.true_and _).trans s3))
  exact (List.all_cons).trans ((congrArg (fun b => b && (["cond", "body"] : List String).all
      (fun c => !(("progn" : String) == c))) g1).trans
    ((Bool.true_and _).trans s2))

-- Reference: `introduced_whenMacro`, `sexprAtoms_whenPattern`,
-- `all_pattern_not_beq_if`, `all_pattern_not_beq_progn`, `List.all_cons`,
-- `List.all_nil`, `Bool.true_and`; [Graham], ch. 9 (capture-freedom).
/-- The toy `when` macro is hygienic on its pattern call: the introduced
symbols `if`/`progn` do not occur in the call. -/
theorem hygienic_when : hygienicCall whenMacro whenPattern = true := by
  change (introduced whenMacro).all
    (fun a => (sexprAtoms whenPattern).all fun c => !(a == c)) = true
  have h0 : ([] : List String).all
      (fun a => (["when", "cond", "body"] : List String).all fun c => !(a == c)) = true :=
    List.all_nil
  have h1 : (["progn"] : List String).all
      (fun a => (["when", "cond", "body"] : List String).all fun c => !(a == c)) = true :=
    (List.all_cons).trans ((congrArg (fun b => b && ([] : List String).all
        (fun a => (["when", "cond", "body"] : List String).all fun c => !(a == c)))
      all_pattern_not_beq_progn).trans ((Bool.true_and _).trans h0))
  have h2 : (["if", "progn"] : List String).all
      (fun a => (["when", "cond", "body"] : List String).all fun c => !(a == c)) = true :=
    (List.all_cons).trans ((congrArg (fun b => b && (["progn"] : List String).all
        (fun a => (["when", "cond", "body"] : List String).all fun c => !(a == c)))
      all_pattern_not_beq_if).trans ((Bool.true_and _).trans h1))
  exact Eq.subst (motive := fun l => l.all
      (fun a => (sexprAtoms whenPattern).all fun c => !(a == c)) = true)
    introduced_whenMacro.symm
    (Eq.subst (motive := fun l => (["if", "progn"] : List String).all
        (fun a => l.all fun c => !(a == c)) = true)
      sexprAtoms_whenPattern.symm h2)
#eval (introduced whenMacro, hygienicCall whenMacro whenPattern,
  sexprAtoms (macroexpand1 toyMacros whenPattern))

end BoringLab
