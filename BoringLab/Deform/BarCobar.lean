/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import BoringLab.Deform.Deform
import BoringLab.Deform.LInf

/-!
# LAB DEFORM.0 (bar–cobar): the bar construction as path composition

Ticket #108, item (iv): Koszul duality in pure-composition form — the bar
construction `B(A)` is the tensor coalgebra on `A`, and its differential
is built from the algebra structure by PATH COMPOSITION of tensor words.
At the computad level: the word computad has one object and generators =
tensor words (lists of elements); paths are concatenations (pasting of
words); the bar differential is a declared LINEAR relation on paths
(formal sums, as in LINF.0 #109). Dually the cobar construction `Ω(C)`.

Skeleton landed here; the differential construction (the shuffle/insertion
sum defining `d_B`) is the named hole `barDifferential`.

## References
* [Getzler] E. Getzler, *Annals of Mathematics* 170 (2009), 271–310 —
  bar/cobar and Koszul duality for dg-Lie algebras (the MC/Deligne
  principle).
* [Lurie] DAG — Koszul duality for formal moduli problems.
* [Lefèvre-Hasegawa] T. Lefèvre-Hasegawa, "Sur les A∞-catégories",
  thesis, 2003 — the bar construction as path composition on words.
* Program register: BoringLab ticket #108 (LAB DEFORM.0).
-/

namespace BoringLab

/-! ## The word computad -/

-- Reference: ticket #108 — the tensor-word computad: one object, a
-- generator per tensor word (list of elements); paths are concatenations
-- (pasting of words); ports trivial.
/-- The **word computad** of an element carrier: one object, generators =
tensor words (`List elem`), trivial ports. -/
def wordComputad (elem : Type) : Computad where
  port := PUnit
  portMul := fun _ _ => PUnit.unit
  portOne := PUnit.unit
  portMul_assoc := fun _ _ _ => rfl
  portMul_left_one := fun _ => rfl
  portMul_right_one := fun _ => rfl
  obj := PUnit
  gen := List elem
  src := fun _ => PUnit.unit
  tgt := fun _ => PUnit.unit
  leftPorts := fun _ => []
  rightPorts := fun _ => []

-- Reference: ticket #108 — concatenation of words IS path composition:
-- the path of the concatenation is the composite of the paths.
/-- The path of a word is the composite of its letters (each letter a
one-generator path). -/
def wordPath {elem : Type} (w : List elem) :
    (wordComputad elem).Path PUnit.unit PUnit.unit :=
  match w with
  | [] => Quiver.Path.nil
  | x :: xs => ((wordComputad elem).toPath ⟨[x], rfl, rfl⟩).comp (wordPath xs)

-- Reference: computation steps of `wordPath`; `rfl` only in these
-- primitive definitional lemmas.
/-- The path of the empty word is the empty path. -/
theorem wordPath_nil {elem : Type} : wordPath ([] : List elem) = Quiver.Path.nil := rfl

-- Reference: computation step of `wordPath`.
/-- The path of a cons word. -/
theorem wordPath_cons {elem : Type} (x : elem) (xs : List elem) :
    wordPath (x :: xs) =
      ((wordComputad elem).toPath ⟨[x], rfl, rfl⟩).comp (wordPath xs) := rfl

-- Reference: ticket #108 — concatenation of words is path composition
-- (definitional via `wordPath_cons` + `Quiver.Path.comp_assoc`-style
-- associativity, which is definitional at the pin).
/-- Word concatenation is path composition. -/
theorem wordPath_append {elem : Type} (w v : List elem) :
    wordPath (w ++ v) = (wordPath w).comp (wordPath v) := by
  induction w with
  | nil =>
    have h1 : wordPath ([] ++ v) = wordPath v := congrArg wordPath (List.nil_append v)
    have h2 : (wordPath ([] : List elem)).comp (wordPath v) = wordPath v :=
      Eq.subst (motive := fun p => p.comp (wordPath v) = wordPath v) wordPath_nil.symm
        (Quiver.Path.nil_comp (wordPath v))
    exact h1.trans h2.symm
  | cons x xs ih =>
    have hstep : wordPath (x :: xs ++ v) =
        ((wordComputad elem).toPath ⟨[x], rfl, rfl⟩).comp (wordPath (xs ++ v)) :=
      wordPath_cons x (xs ++ v)
    have hca : ((wordComputad elem).toPath ⟨[x], rfl, rfl⟩).comp (wordPath (xs ++ v)) =
        ((wordComputad elem).toPath ⟨[x], rfl, rfl⟩).comp ((wordPath xs).comp (wordPath v)) :=
      congrArg (fun p => ((wordComputad elem).toPath ⟨[x], rfl, rfl⟩).comp p) ih
    have hassoc :
        ((wordComputad elem).toPath ⟨[x], rfl, rfl⟩).comp ((wordPath xs).comp (wordPath v)) =
        (((wordComputad elem).toPath ⟨[x], rfl, rfl⟩).comp (wordPath xs)).comp (wordPath v) :=
      (Quiver.Path.comp_assoc _ _ _).symm
    have hrhs : wordPath (x :: xs) =
        ((wordComputad elem).toPath ⟨[x], rfl, rfl⟩).comp (wordPath xs) := wordPath_cons x xs
    exact hstep.trans (hca.trans (hassoc.trans (congrArg (fun p => p.comp (wordPath v)) hrhs).symm))

/-! ## The bar/cobar presentation skeleton -/

-- Reference: ticket #108 — a bar/cobar presentation: the word computad of
-- the element carrier, with the bar differential as declared linear
-- relations on paths (formal sums = 0). The differential construction is
-- the named `barDifferential` hole.
/-- A **bar/cobar presentation**: the word computad of an element carrier,
with declared linear relations (the bar/cobar differential). -/
structure BarPres where
  /-- The element carrier. -/
  elem : Type
  /-- The word computad. -/
  words : Computad := wordComputad elem
  /-- The declared relations (formal sums of paths, each = 0) — the bar
  differential. The endpoints are typed at `(wordComputad elem).obj` (which
  is definitionally `PUnit`), since `words.obj` is a stuck projection inside
  the structure. -/
  relations : List (FormalSum (wordComputad elem) PUnit.unit PUnit.unit)

-- Reference: [Barendregt], ch. 2 (eta conversion), as in `Sieve.eta`.
-- REVIEW(citation): pin down the exact section in review.
/-- **Eta conversion for bar/cobar presentations**. -/
theorem BarPres.eta (B : BarPres) :
    BarPres.mk B.elem B.words B.relations = B := by
  cases B with
  | mk elem words relations => rfl

end BoringLab
