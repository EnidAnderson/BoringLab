/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import BoringLab.Deform.LInf

/-!
# LAB LINF.0 (Jacobi): the unshuffle construction for the generalized Jacobi sums

Ticket #109's named hole `shuffleSum`: the generalized Jacobi identity for
`lₙ` is a sum over the (k, n−k+1)-UNSHUFFLES of the inputs, with Koszul
signs. This module lands the combinatorial core — `unshuffles`, the
order-preserving interleavings of two lists — with the computation lemmas,
and the tree skeleton `jacobiTrees n`; the bracket application + Koszul
sign assembly (`jacobiSum` as a `FormalSum` in the sense of `LInfAxioms`)
is the remaining named hole.

## References
* [Lada–Stasheff] M. Lada, J. Stasheff, JPAA 48 (1987) — the generalized
  Jacobi identity as a sum over unshuffles with Koszul signs.
* [Getzler] E. Getzler, Annals 170 (2009) — the sign conventions.
* Program register: BoringLab ticket #109 (LAB LINF.0).
-/

namespace BoringLab

/-! ## Unshuffles -/

-- Reference: ticket #109 — an unshuffle interleaves two lists preserving
-- each list's internal order; recursion on both lists.
/-- The **unshuffles** of two lists: all interleavings preserving each
list's internal order (as `α ⊕ β` sums). -/
def unshuffles {α β : Type} : List α → List β → List (List (α ⊕ β))
  | [], ys => [ys.map Sum.inr]
  | xs, [] => [xs.map Sum.inl]
  | x :: xs, y :: ys =>
      (unshuffles xs (y :: ys)).map (fun l => Sum.inl x :: l) ++
        (unshuffles (x :: xs) ys).map (fun l => Sum.inr y :: l)

-- Reference: computation steps of `unshuffles`, via its equation lemmas
-- (the double recursion compiles well-founded, so these are `eq_1`/`eq_2`/
-- `eq_3` transports, with `rfl` only at the primitive `List.map`/`List.append`
-- steps on constructors).
/-- Unshuffles with an empty left list. -/
theorem unshuffles_nil_left {α β : Type} (ys : List β) :
    unshuffles ([] : List α) ys = [ys.map Sum.inr] := unshuffles.eq_1 ys

-- Reference: computation step of `unshuffles` (`eq_1` on the nil case,
-- `eq_2` with the `cons_ne_nil` side condition on the cons case).
/-- Unshuffles with an empty right list. -/
theorem unshuffles_nil_right {α β : Type} (xs : List α) :
    unshuffles xs ([] : List β) = [xs.map Sum.inl] := by
  cases xs with
  | nil => exact (unshuffles.eq_1 ([] : List β)).trans rfl
  | cons x xs => exact unshuffles.eq_2 (x :: xs) (fun h => List.cons_ne_nil x xs h)

-- Reference: computation step of `unshuffles` (`eq_3`).
/-- Unshuffles of two conses split on which side the head comes from. -/
theorem unshuffles_cons_cons {α β : Type} (x : α) (xs : List α) (y : β) (ys : List β) :
    unshuffles (x :: xs) (y :: ys) =
      (unshuffles xs (y :: ys)).map (fun l => Sum.inl x :: l) ++
        (unshuffles (x :: xs) ys).map (fun l => Sum.inr y :: l) :=
  unshuffles.eq_3 x xs y ys

-- Reference: core `List.length_map`, `List.length_append`; the count of
-- unshuffles is the binomial (statement; the binomial law is the named
-- `unshuffles_length` hole — needs `Nat.choose`). Here: `eq_3` plus the
-- `eq_1`/`eq_2` base steps, transported by `congrArg`.
/-- The unshuffles of `[x]` and `[y]`: exactly the two interleavings. -/
theorem unshuffles_singleton_singleton {α β : Type} (x : α) (y : β) :
    unshuffles [x] [y] =
      [[Sum.inl x, Sum.inr y], [Sum.inr y, Sum.inl x]] := by
  have h1 : unshuffles ([] : List α) [y] = [[Sum.inr y]] :=
    (unshuffles.eq_1 [y]).trans rfl
  have h2 : unshuffles [x] ([] : List β) = [[Sum.inl x]] :=
    (unshuffles.eq_2 [x] (fun h => List.cons_ne_nil x [] h)).trans rfl
  have h3 := unshuffles.eq_3 x [] y []
  have e1 : (unshuffles ([] : List α) [y]).map (fun l => Sum.inl x :: l) =
      [[Sum.inl x, Sum.inr y]] :=
    (congrArg (fun L => L.map (fun l => Sum.inl x :: l)) h1).trans rfl
  have e2 : (unshuffles [x] ([] : List β)).map (fun l => Sum.inr y :: l) =
      [[Sum.inr y, Sum.inl x]] :=
    (congrArg (fun L => L.map (fun l => Sum.inr y :: l)) h2).trans rfl
  exact h3.trans
    ((congrArg
      (fun L => L ++ (unshuffles [x] ([] : List β)).map (fun l => Sum.inr y :: l)) e1).trans
      ((congrArg (fun L => [[Sum.inl x, Sum.inr y]] ++ L) e2).trans rfl))

/-! ## The Jacobi tree skeleton -/

-- Reference: ticket #109 — the Jacobi sum for `lₙ` runs over the
-- (k, n−k+1)-unshuffles: `jacobiTrees n k` is the list of input
-- interleavings for the outer bracket of arity `k`. The bracket
-- application and Koszul signs (assembling the `FormalSum` of
-- `LInfAxioms.jacobiSum`) are the remaining named hole.
/-- The **Jacobi trees** for `lₙ` with outer arity `k`: the unshuffles of
the `k−1` outer inputs with the `n−k+1` inner block (as `ℕ ⊕ ℕ`
markers). -/
def jacobiTrees (n k : ℕ) : List (List (ℕ ⊕ ℕ)) :=
  unshuffles (List.range (k - 1)) (List.range (n - k + 1))

end BoringLab
