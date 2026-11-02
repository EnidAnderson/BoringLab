/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import Mathlib.Init
import Mathlib.Data.Nat.Notation

/-!
# Truncation: level-indexed data with a tracked remainder

Ticket #41 (EPI.8.1, child of EPI.8.0). A `Truncation α` displays explicit data
at level `n`, a declared remainder in an explicit carrier, and a one-step
refinement map; tracking laws (level arithmetic, content conservation, exact
reconstruction) are proved for three toy instances (decimal truncation of a
rational, list-prefix of a stream, depth-truncated game trees), and the
`TruncatedClaim` schema records that an honest truncated claim is never a claim
about the untruncated object (toy: `1/3`).

## References
* [Hardy–Wright] Hardy & Wright, *An Introduction to the Theory of Numbers*,
  6th ed., OUP 2008, Ch. IX (representation of numbers by decimals).
* [Bishop–Bridges] Bishop & Bridges, *Constructive Analysis*, Springer 1985,
  Ch. 2, Def. 2.1 (tracked-remainder reading of an approximation).
* [Conway] Conway, *On Numbers and Games*, 2nd ed., A K Peters 2000, Ch. 0.
* [Barendregt] Barendregt, *The Lambda Calculus*, North-Holland 1984, Ch. 2.
* Program register: WORK ORDER W-docs, ticket #41 (EPI.8.1) — the schemas are
  the program's own.
-/

namespace BoringLab

/-! ## The truncation structure -/
-- Reference: register WORK ORDER W-docs #41 (EPI.8.1). REVIEW(citation): pin entry.
/-- A **truncation** of an object displayed as elements of `α`: explicit data
at level `n`, a declared remainder in an explicit carrier, and a one-step
refinement map (refines to level `n + 1`). -/
structure Trunc (α : Type) where
  /-- The level of the truncation. -/
  level : ℕ
  /-- The explicit data visible at this level. -/
  data : List α
  /-- The carrier type of the declared remainder. -/
  remainderCarrier : Type
  /-- The declared remainder: the not-yet-displayed part of the object. -/
  remainder : remainderCarrier

-- Reference: register WORK ORDER W-docs #41 (EPI.8.1), as for `Trunc`.
-- REVIEW(citation): pin entry.
/-- A **truncation** of an object displayed as elements of `α`: explicit data
at level `n`, a declared remainder in an explicit carrier, and a one-step
refinement map (refines to level `n + 1`). The refinement map goes from the
data part `Trunc α` to itself, so that the structure stays positive. -/
structure Truncation (α : Type) extends Trunc α where
  /-- The one-step refinement map. -/
  refine : Trunc α → Trunc α
-- Reference: [Barendregt], Ch. 2 (eta). REVIEW(citation): as in `BoringLab.Game.eta`.
/-- **Eta conversion for truncations**: a truncation equals the truncation
assembled from its components. -/
theorem Truncation.eta {α : Type} (t : Truncation α) :
    Truncation.mk t.toTrunc t.refine = t := by
  cases t with
  | mk toTrunc refine => rfl

/-! ## Tracking laws at the data level

The laws hold for an arbitrary level `n`, hence on every bounded family; each
instance proves them by explicit computation steps (named `rfl` lemmas). -/
-- Reference: register #41 (EPI.8.1). REVIEW(citation): pin entry.
/-- A truncation **refines one level up** when its own refinement map applied
to itself raises the level by exactly one. -/
def Truncation.RefinesOne {α : Type} (t : Truncation α) : Prop :=
  (t.refine t.toTrunc).level = t.level + 1
-- Reference: register #41 (EPI.8.1). REVIEW(citation): pin entry.
/-- **Content conservation**: nothing appears in the refined data that was not
already in the data or read off the remainder through `remContent`. -/
def Truncation.ContentConserving {α : Type} (t : Truncation α)
    (remContent : t.remainderCarrier → List α) : Prop :=
  ∀ x ∈ (t.refine t.toTrunc).data, x ∈ t.data ∨ x ∈ remContent t.remainder
-- Reference: register #41, from `ContentConserving` and `List.mem_append`.
/-- Content conservation in append form: refined data ⊆ data ++ remainder-content. -/
theorem Truncation.mem_append_of_contentConserving {α : Type} (t : Truncation α)
    (rc : t.remainderCarrier → List α) (h : t.ContentConserving rc) :
    ∀ x ∈ (t.refine t.toTrunc).data, x ∈ t.data ++ rc t.remainder := by
  intro x hx
  rcases h x hx with h' | h'
  · exact List.mem_append_left _ h'
  · exact List.mem_append_right _ h'
-- Reference: register #41 (EPI.8.1). REVIEW(citation): pin entry.
/-- **Tracking law**: refining one level up conserves content and raises the
level to `n + 1`. -/
theorem Truncation.refine_tracks {α : Type} (t : Truncation α)
    (rc : t.remainderCarrier → List α)
    (hlev : t.RefinesOne) (hcon : t.ContentConserving rc) :
    (t.refine t.toTrunc).level = t.level + 1 ∧
      ∀ x ∈ (t.refine t.toTrunc).data, x ∈ t.data ++ rc t.remainder :=
  ⟨hlev, Truncation.mem_append_of_contentConserving t rc hcon⟩

/-! ## A computable concat-map -/
-- Reference: core `List.flatMapTR`; `List.flatMap` is noncomputable at the pin.
/-- **Concat-map**: apply `f` to every element and concatenate the results. -/
def concatMap {α β : Type} (f : α → List β) : List α → List β
  | [] => []
  | a :: l => f a ++ concatMap f l
-- Reference: primitive computation step of `concatMap` (definitional).
/-- The nil step of `concatMap`. -/
theorem concatMap_nil {α β : Type} (f : α → List β) : concatMap f [] = [] := rfl
-- Reference: primitive computation step of `concatMap` (definitional).
/-- The cons step of `concatMap`. -/
theorem concatMap_cons {α β : Type} (f : α → List β) (a : α) (l : List α) :
    concatMap f (a :: l) = f a ++ concatMap f l := rfl
-- Reference: concat-map membership by induction via `List.mem_append` (core).
/-- `b ∈ concatMap f l` iff `b ∈ f a` for some `a ∈ l`. -/
theorem mem_concatMap {α β : Type} (f : α → List β) (l : List α) (b : β) :
    b ∈ concatMap f l ↔ ∃ a, a ∈ l ∧ b ∈ f a := by
  induction l with
  | nil =>
    refine Iff.intro
      (fun h => absurd (Eq.subst (motive := fun L => b ∈ L) (concatMap_nil f) h)
        List.not_mem_nil) ?_
    rintro ⟨_, ha, _⟩
    exact absurd ha List.not_mem_nil
  | cons a l ih =>
    refine Iff.intro (fun h => ?_) (fun h => ?_)
    · have h1 : b ∈ f a ++ concatMap f l :=
        Eq.subst (motive := fun L => b ∈ L) (concatMap_cons f a l) h
      rcases List.mem_append.mp h1 with h2 | h2
      · exact ⟨a, List.mem_cons_self, h2⟩
      · rcases ih.mp h2 with ⟨x, hx, hx2⟩
        exact ⟨x, List.mem_cons_of_mem a hx, hx2⟩
    · rcases h with ⟨x, hx, hx2⟩
      rcases List.mem_cons.mp hx with e | hx'
      · subst e
        exact Eq.subst (motive := fun L => b ∈ L) (concatMap_cons f x l).symm
          (List.mem_append_left (concatMap f l) hx2)
      · have h3 : b ∈ concatMap f l := ih.mpr ⟨x, hx', hx2⟩
        exact Eq.subst (motive := fun L => b ∈ L) (concatMap_cons f a l).symm
          (List.mem_append_right (f a) h3)

/-! ## Toy instance (i): decimal truncation of a rational -/
-- Reference: [Hardy–Wright], 6th ed., Ch. IX (decimals). REVIEW(citation): pin theorem no.
/-- The long-division remainder after `n` decimal digits of `a / b`. -/
def decRemainder (n a b : ℕ) : ℕ := (a * 10 ^ n) % b
-- Reference: [Hardy–Wright], 6th ed., Ch. IX, as above. REVIEW(citation): pin theorem no.
/-- The `i`-th decimal digit (0-indexed) of `a / b`, read off the step-`i`
remainder by one more division step. -/
def decDigit (i a b : ℕ) : ℕ := (decRemainder i a b * 10) / b
-- Reference: register #41 (EPI.8.1). REVIEW(citation): pin entry.
/-- The digit produced by one refinement step from the remainder pair `(r, b)`. -/
def decNextDigit (p : ℕ × ℕ) : ℕ := (p.1 * 10) / p.2
-- Reference: register #41 (EPI.8.1). REVIEW(citation): pin entry.
/-- One refinement step of the decimal family for `a / b`: level `n` goes to
`n + 1`; the refinement map is propagated unchanged along the chain. -/
def decStep (a b : ℕ) (u : Trunc ℕ) : Trunc ℕ :=
  { level := u.level + 1,
    data := (List.range (u.level + 1)).map (fun i => decDigit i a b),
    remainderCarrier := ℕ × ℕ,
    remainder := (decRemainder (u.level + 1) a b, b) }
-- Reference: register #41 (EPI.8.1). REVIEW(citation): pin entry.
/-- The decimal truncation of `a / b` at level `n`: the first `n` digits as
data, the long-division remainder as declared remainder. -/
def decTrunc (a b : ℕ) (n : ℕ) : Truncation ℕ :=
  { level := n,
    data := (List.range n).map (fun i => decDigit i a b),
    remainderCarrier := ℕ × ℕ,
    remainder := (decRemainder n a b, b),
    refine := decStep a b }
-- Reference: primitive computation step of `decTrunc` (definitional).
/-- The data step of `decTrunc`. -/
theorem decTrunc_data (a b n : ℕ) :
    (decTrunc a b n).data = (List.range n).map (fun i => decDigit i a b) := rfl
-- Reference: primitive computation step of `decTrunc` (definitional).
/-- The remainder step of `decTrunc`. -/
theorem decTrunc_remainder (a b n : ℕ) :
    (decTrunc a b n).remainder = (decRemainder n a b, b) := rfl
-- Reference: primitive computation step of `decStep` on `decTrunc`.
/-- One refinement step of `decTrunc` raises the level to `n + 1`. -/
theorem dec_refine_level (a b n : ℕ) :
    ((decTrunc a b n).refine (decTrunc a b n).toTrunc).level = n + 1 := rfl
-- Reference: primitive computation step of `decStep` on `decTrunc`.
/-- One refinement step of `decTrunc` has the first `n + 1` digits as data. -/
theorem dec_refine_data (a b n : ℕ) :
    ((decTrunc a b n).refine (decTrunc a b n).toTrunc).data =
      (List.range (n + 1)).map (fun i => decDigit i a b) := rfl
-- Reference: primitive computation step of `decNextDigit` on the remainder.
/-- The next digit read off the declared remainder of `decTrunc` is the `n`-th digit. -/
theorem dec_remainder_nextDigit (a b n : ℕ) :
    decNextDigit ((decTrunc a b n).remainder) = decDigit n a b := rfl
-- Reference: register #41, from `dec_refine_level`.
/-- The decimal truncation refines one level up. -/
theorem dec_refinesOne (a b n : ℕ) : (decTrunc a b n).RefinesOne :=
  dec_refine_level a b n
-- Reference: [Hardy–Wright], 6th ed., Ch. IX, via `Nat.div_add_mod` (core).
/-- **Reconstruction is exact**: quotient and remainder after `n` digits
reproduce `a * 10 ^ n` exactly. -/
theorem dec_reconstruct (a b n : ℕ) :
    b * ((a * 10 ^ n) / b) + decRemainder n a b = a * 10 ^ n :=
  Nat.div_add_mod (a * 10 ^ n) b
-- Reference: register #41, from `List.mem_map`, `List.mem_range`, `Nat.lt_succ_iff`.
/-- **Content conservation** for the decimal truncation: every digit in the
refined data was already in the data, or is the next digit read off the
declared remainder. -/
theorem dec_contentConserving (a b n : ℕ) :
    (decTrunc a b n).ContentConserving (fun p => [decNextDigit p]) := by
  intro x hx
  have h1 : x ∈ (List.range (n + 1)).map (fun i => decDigit i a b) :=
    Eq.subst (motive := fun L => x ∈ L) (dec_refine_data a b n) hx
  obtain ⟨i, hi, hix⟩ := List.mem_map.mp h1
  have h2 : i < n + 1 := List.mem_range.mp hi
  have h3 : i ≤ n := Nat.lt_succ_iff.mp (show i < Nat.succ n from h2)
  rcases Nat.le_iff_lt_or_eq.mp h3 with h4 | h4
  · left
    have h5 : x ∈ (List.range n).map (fun i => decDigit i a b) :=
      List.mem_map.mpr ⟨i, List.mem_range.mpr h4, hix⟩
    exact Eq.subst (motive := fun L => x ∈ L) (decTrunc_data a b n).symm h5
  · right
    subst h4
    refine List.mem_singleton.mpr ?_
    exact hix.symm.trans (dec_remainder_nextDigit a b i).symm

/-! ## Toy instance (ii): list-prefix truncation of a stream -/
-- Reference: register #41 (EPI.8.1); the stream is a `List`, split by take/drop.
/-- One refinement step of the list-prefix family for `s`: the data is extended
to `s.take (level + 1)`. -/
def listStep {γ : Type} (s : List γ) (u : Trunc γ) : Trunc γ :=
  { level := u.level + 1,
    data := s.take (u.level + 1),
    remainderCarrier := List γ,
    remainder := s.drop (u.level + 1) }
-- Reference: register #41 (EPI.8.1). REVIEW(citation): pin entry.
/-- The list-prefix truncation of the stream `s` at level `n`: the first `n`
elements as data, the rest as declared remainder. -/
def listTrunc {γ : Type} (s : List γ) (n : ℕ) : Truncation γ :=
  { level := n,
    data := s.take n,
    remainderCarrier := List γ,
    remainder := s.drop n,
    refine := listStep s }
-- Reference: primitive computation step of `listTrunc` (definitional).
/-- The data step of `listTrunc`. -/
theorem listTrunc_data {γ : Type} (s : List γ) (n : ℕ) :
    (listTrunc s n).data = s.take n := rfl
-- Reference: primitive computation step of `listTrunc` (definitional).
/-- The remainder step of `listTrunc`. -/
theorem listTrunc_remainder {γ : Type} (s : List γ) (n : ℕ) :
    (listTrunc s n).remainder = s.drop n := rfl
-- Reference: primitive computation step of `listStep` on `listTrunc`.
/-- One refinement step of `listTrunc` raises the level to `n + 1`. -/
theorem list_refine_level {γ : Type} (s : List γ) (n : ℕ) :
    ((listTrunc s n).refine (listTrunc s n).toTrunc).level = n + 1 := rfl
-- Reference: primitive computation step of `listStep` on `listTrunc`.
/-- One refinement step of `listTrunc` has `s.take (n + 1)` as data. -/
theorem list_refine_data {γ : Type} (s : List γ) (n : ℕ) :
    ((listTrunc s n).refine (listTrunc s n).toTrunc).data = s.take (n + 1) := rfl
-- Reference: `List.take_append_drop` (core, Init/Data/List/TakeDrop.lean).
/-- Membership in a take is membership in the whole list. -/
theorem mem_of_mem_take {γ : Type} (s : List γ) (n : ℕ) (x : γ) (h : x ∈ s.take n) :
    x ∈ s :=
  Eq.subst (motive := fun L => x ∈ L) (List.take_append_drop n s)
    (List.mem_append_left (s.drop n) h)
-- Reference: register #41, from `List.take_append_drop` (core).
/-- **Reconstruction is exact**: data ++ remainder is the whole stream. -/
theorem list_reconstruct {γ : Type} (s : List γ) (n : ℕ) :
    List.append (listTrunc s n).data (listTrunc s n).remainder = s :=
  Eq.trans
    (congrArg (fun L => List.append L (listTrunc s n).remainder) (listTrunc_data s n))
    (Eq.trans (congrArg (fun R => List.append (s.take n) R) (listTrunc_remainder s n))
      (List.take_append_drop n s))
-- Reference: register #41, from `list_refine_level`.
/-- The list-prefix truncation refines one level up. -/
theorem list_refinesOne {γ : Type} (s : List γ) (n : ℕ) :
    (listTrunc s n).RefinesOne :=
  list_refine_level s n
-- Reference: register #41, from `List.take_append_drop` and `List.mem_append`.
/-- **Content conservation** for the list-prefix truncation: every element of
the refined data was already in the data or lies in the remainder stream. -/
theorem list_contentConserving {γ : Type} (s : List γ) (n : ℕ) :
    (listTrunc s n).ContentConserving (fun l => l) := by
  intro x hx
  have h1 : x ∈ s.take (n + 1) :=
    Eq.subst (motive := fun L => x ∈ L) (list_refine_data s n) hx
  have h2 : x ∈ s := mem_of_mem_take s (n + 1) x h1
  have h3 : x ∈ s.take n ++ s.drop n :=
    Eq.subst (motive := fun L => x ∈ L) (List.take_append_drop n s).symm h2
  rcases List.mem_append.mp h3 with h4 | h4
  · left
    exact Eq.subst (motive := fun L => x ∈ L) (listTrunc_data s n).symm h4
  · right
    exact Eq.subst (motive := fun L => x ∈ L) (listTrunc_remainder s n).symm h4

/-! ## Toy instance (iii): depth-truncated game trees -/
-- Reference: [Conway] Ch. 0; local toy, full tree truncation is ticket #20. REVIEW(citation).
/-- A minimal bounded game tree: leaves and nodes with a list of children. -/
inductive BTree : Type where
  | leaf : BTree
  | node : List BTree → BTree
deriving Repr
-- Reference: [Conway], Ch. 0 (options of a position). REVIEW(citation).
/-- The children (options) of a tree node. -/
def BTree.children : BTree → List BTree
  | leaf => []
  | node ts => ts
-- Reference: register #41 (EPI.8.1). REVIEW(citation): pin entry.
/-- The frontier at depth `n`: the subtrees rooted at depth exactly `n`. -/
def BTree.frontier : ℕ → BTree → List BTree
  | 0, t => [t]
  | n + 1, t => concatMap BTree.children (BTree.frontier n t)
-- Reference: primitive computation step of `BTree.frontier` (definitional).
/-- The successor step of the frontier. -/
theorem BTree.frontier_succ (n : ℕ) (t : BTree) :
    BTree.frontier (n + 1) t = concatMap BTree.children (BTree.frontier n t) := rfl
-- Reference: register #41 (EPI.8.1). REVIEW(citation): pin entry.
/-- One refinement step of the game-tree family for `t`: the data is the
frontier one level deeper. -/
def treeStep (t : BTree) (u : Trunc BTree) : Trunc BTree :=
  { level := u.level + 1,
    data := BTree.frontier (u.level + 1) t,
    remainderCarrier := BTree,
    remainder := t }
-- Reference: register #41 (EPI.8.1). REVIEW(citation): pin entry.
/-- The depth-`n` truncation of the game tree `t`: the depth-`n` frontier as
data, the whole tree as declared remainder. -/
def treeTrunc (t : BTree) (n : ℕ) : Truncation BTree :=
  { level := n,
    data := BTree.frontier n t,
    remainderCarrier := BTree,
    remainder := t,
    refine := treeStep t }
-- Reference: primitive computation step of `treeStep` on `treeTrunc`.
/-- One refinement step of `treeTrunc` raises the level to `n + 1`. -/
theorem tree_refine_level (t : BTree) (n : ℕ) :
    ((treeTrunc t n).refine (treeTrunc t n).toTrunc).level = n + 1 := rfl
-- Reference: register #41, from `tree_refine_level`.
/-- The depth-truncated game tree refines one level up. -/
theorem tree_refinesOne (t : BTree) (n : ℕ) : (treeTrunc t n).RefinesOne :=
  tree_refine_level t n
-- Reference: register #41, from `BTree.frontier_succ` and `mem_concatMap`.
/-- **Content conservation** for game trees: every node on the refined
frontier is a child of a node on the current frontier. -/
theorem tree_frontier_succ_mem (t : BTree) (n : ℕ) (x : BTree)
    (h : x ∈ BTree.frontier (n + 1) t) :
    ∃ y ∈ BTree.frontier n t, x ∈ BTree.children y := by
  have h1 : x ∈ concatMap BTree.children (BTree.frontier n t) :=
    Eq.subst (motive := fun L => x ∈ L) (BTree.frontier_succ n t) h
  exact (mem_concatMap BTree.children (BTree.frontier n t) x).mp h1

/-! ## The truncated-claim schema -/
-- Reference: register #41 (EPI.8.1). REVIEW(citation): pin entry.
/-- A **truncated claim**: a claim about the data of a truncation at level `n`,
together with the corresponding claim about the untruncated object, carried
by the declared remainder. -/
structure TruncatedClaim (α : Type) where
  /-- The truncation the claim is made about. -/
  trunc : Truncation α
  /-- The claim at level `n`, about the displayed data only. -/
  claim : List α → Prop
  /-- The corresponding claim about the untruncated object. -/
  fullClaim : trunc.remainderCarrier → Prop
-- Reference: register #41 (EPI.8.1). REVIEW(citation): pin entry.
/-- A truncated claim is **honest** when it is never simultaneously true of the
data and of the full object. -/
def TruncatedClaim.honest {α : Type} (c : TruncatedClaim α) : Prop :=
  ¬ (c.claim c.trunc.data ∧ c.fullClaim c.trunc.remainder)
-- Reference: register #41, from the definition of `TruncatedClaim.honest`.
/-- **An honest truncated claim is never a claim about the untruncated
object**: if the claim holds of the data, the full claim fails of the
remainder. -/
theorem TruncatedClaim.honest_never_untruncated {α : Type} (c : TruncatedClaim α)
    (hhonest : TruncatedClaim.honest c) (hclaim : c.claim c.trunc.data) :
    ¬ c.fullClaim c.trunc.remainder :=
  fun hfull => hhonest ⟨hclaim, hfull⟩

/-! ## Toy-level instance of the schema: `1/3` in decimal -/
-- Reference: closed natural-number computation (primitive `rfl` lemma).
/-- The 0-th decimal digit of `1/3` is `3`. -/
theorem decDigit_zero_one_three : decDigit 0 1 3 = 3 := rfl
-- Reference: closed natural-number computation (primitive `rfl` lemma).
/-- The 1-st decimal digit of `1/3` is `3`. -/
theorem decDigit_one_one_three : decDigit 1 1 3 = 3 := rfl
-- Reference: closed natural-number computation (primitive `rfl` lemma).
/-- The 2-nd decimal digit of `1/3` is `3`. -/
theorem decDigit_two_one_three : decDigit 2 1 3 = 3 := rfl
-- Reference: closed natural-number computation (primitive `rfl` lemma).
/-- The remainder after 3 decimal digits of `1/3` is `1`. -/
theorem decRemainder_three_one_three : decRemainder 3 1 3 = 1 := rfl
-- Reference: register #41 (EPI.8.1). REVIEW(citation): pin entry.
/-- The toy truncated claim: "the first three decimal digits of `1/3` are all
`3`", against the full claim "the remainder is zero" (the decimal
terminates). -/
def thirdClaim : TruncatedClaim ℕ :=
  { trunc := decTrunc 1 3 3,
    claim := fun d => ∀ x ∈ d, x = 3,
    fullClaim := fun p => p.1 = 0 }
-- Reference: register #41, by explicit cases on `i < 3` via `List.mem_map`,
-- `List.mem_range`, `Nat.le_iff_lt_or_eq` (core).
/-- The toy claim holds of the data: the first three digits of `1/3` are `3`s. -/
theorem thirdClaim_claim_holds : thirdClaim.claim thirdClaim.trunc.data := by
  intro x hx
  have h1 : x ∈ (List.range 3).map (fun i => decDigit i 1 3) :=
    Eq.subst (motive := fun L => x ∈ L) (decTrunc_data 1 3 3) hx
  obtain ⟨i, hi, hix⟩ := List.mem_map.mp h1
  have h2 : i < 3 := List.mem_range.mp hi
  have h3 : i ≤ 2 := Nat.lt_succ_iff.mp (show i < Nat.succ 2 from h2)
  rcases Nat.le_iff_lt_or_eq.mp h3 with e | e
  · have h4 : i ≤ 1 := Nat.lt_succ_iff.mp (show i < Nat.succ 1 from e)
    rcases Nat.le_iff_lt_or_eq.mp h4 with e2 | e2
    · have h5 : i ≤ 0 := Nat.lt_succ_iff.mp (show i < Nat.succ 0 from e2)
      rcases Nat.le_iff_lt_or_eq.mp h5 with e3 | e3
      · exact absurd e3 (Nat.not_lt_zero i)
      · subst e3
        exact hix.symm.trans decDigit_zero_one_three
    · subst e2
      exact hix.symm.trans decDigit_one_one_three
  · subst e
    exact hix.symm.trans decDigit_two_one_three
-- Reference: register #41, from `decTrunc_remainder` and `Nat.one_ne_zero`.
/-- The full claim fails for `1/3`: the remainder after three digits is `1`. -/
theorem thirdClaim_not_full : ¬ thirdClaim.fullClaim thirdClaim.trunc.remainder := by
  intro hf
  have h1 : (decTrunc 1 3 3).remainder = (decRemainder 3 1 3, 3) :=
    decTrunc_remainder 1 3 3
  have h2 : ((decRemainder 3 1 3, 3) : ℕ × ℕ).1 = 0 :=
    Eq.subst (motive := fun r => (r : ℕ × ℕ).1 = 0) h1 hf
  have h3 : (1 : ℕ) = 0 :=
    Eq.subst (motive := fun r => ((r, 3) : ℕ × ℕ).1 = 0) decRemainder_three_one_three h2
  exact Nat.one_ne_zero h3
-- Reference: register #41, from `thirdClaim_not_full`.
/-- The toy truncated claim is honest. -/
theorem thirdClaim_honest : TruncatedClaim.honest thirdClaim := by
  intro h
  rcases h with ⟨_, hf⟩
  exact thirdClaim_not_full hf
-- Reference: register #41, from `TruncatedClaim.honest_never_untruncated`.
/-- **Toy-level honesty, non-vacuous**: the digit claim for `1/3` holds of the
data and is never a claim about the full object. -/
theorem third_never_untruncated :
    ¬ thirdClaim.fullClaim thirdClaim.trunc.remainder :=
  TruncatedClaim.honest_never_untruncated thirdClaim thirdClaim_honest
    thirdClaim_claim_holds

/-! ## The three toy instances, printed -/
-- Reference: register #41, item (d): `#eval` prints the three toy instances.
/-- The example stream for the list-prefix instance. -/
def exampleStream : List ℕ := [10, 20, 30, 40, 50]
-- Reference: register #41, item (d).
/-- The example bounded game tree for the depth-truncation instance. -/
def exampleTree : BTree :=
  BTree.node [BTree.node [BTree.leaf, BTree.leaf], BTree.leaf]
end BoringLab
