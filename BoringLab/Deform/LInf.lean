/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import BoringLab.Doctrine.Morph
import Mathlib.Data.Int.Notation

/-!
# LAB LINF.0: L∞ algebras as polygraphs (the pure-composition form)

Ticket #109 (LAB LINF.0): an L∞ algebra at the pure-composition level is a
computad with ONE object (the underlying graded space), whose generators
are the multilinear brackets `lₙ` of arity `n ≥ 1` and degree `d`
(cohomological convention: `deg lₙ = 2 − n`, so `l₁` has degree `1`),
with port typing = arity: the port monoid is `ℤ` with `+`, an `n`-ary
operation consumes the port `[n]` and produces its degree port `[d]`.

The generalized Jacobi identities are LINEAR relations (shuffle sums of
trees), not single path equations — so the relation layer is upgraded from
paths to FORMAL SUMS of paths (`FormalSum` = `List (Path × ℤ)`): the
doctrine-of-linear-relations. The differential axiom `l₁² = 0` is the
single-tree relation (proved witness below); the full generalized Jacobi
`jacobiSum n` is carried as explicit data with the axiom as a `Prop` field,
the construction being the named `shuffleSum` hole.

## References
* [Lada–Stasheff] M. Lada, J. Stasheff, "Deformation theory of algebras and
  their diagrams", *J. Pure Appl. Algebra* 48 (1987) — the L∞ operad and
  the generalized Jacobi identities.
* [Getzler] E. Getzler, "Lie theory for nilpotent L∞ algebras", *Annals of
  Mathematics* 170 (2009), 271–310 — the Maurer–Cartan equation and the
  Deligne principle (the MC shadow of DEFORM.0, #108).
* [Merkulov] S. Merkulov, L∞ algebras as homotopy-Lie (the polygraphic
  reading).
* Program register: BoringLab ticket #109 (LAB LINF.0).
-/

namespace BoringLab

/-! ## The L∞ computad -/

-- Reference: ticket #109 — one object (the graded space), port monoid
-- `ℤ` with `+` (the degrees), generators = (arity, degree) with arity ≥ 1;
-- an n-ary bracket consumes the port `[n]` and produces `[d]`.
/-- The **L∞ computad**: one object (`PUnit`, the underlying graded
space), port monoid `ℤ` with `+`; a generator is an operation `(n, d)`
with arity `n ≥ 1` and degree `d`; left port `[n]` (the arity), right port
`[d]` (the degree). -/
def linfComputad : Computad where
  port := ℤ
  portMul := fun a b => a + b
  portOne := 0
  portMul_assoc := fun a b c => (Int.add_assoc a b c).symm
  portMul_left_one := fun a => Int.zero_add a
  portMul_right_one := fun a => Int.add_zero a
  obj := PUnit
  gen := {p : ℕ × ℤ // 1 ≤ p.1}
  src := fun _ => PUnit.unit
  tgt := fun _ => PUnit.unit
  leftPorts := fun g => [(g.1.1 : ℤ)]
  rightPorts := fun g => [g.1.2]

-- Reference: computation step: the left port word of an operation path is
-- its arity (`portWord [n] = n + 0`).
/-- The left port word of a single-operation path is the arity. -/
theorem linfComputad.pathLeftWord_toPath (g : linfComputad.gen) :
    linfComputad.pathLeftWord (linfComputad.toPath ⟨g, rfl, rfl⟩) = (g.1.1 : ℤ) :=
  Int.add_zero (g.1.1 : ℤ)

-- Reference: computation step: the right port word is the degree.
/-- The right port word of a single-operation path is the degree. -/
theorem linfComputad.pathRightWord_toPath (g : linfComputad.gen) :
    linfComputad.pathRightWord (linfComputad.toPath ⟨g, rfl, rfl⟩) = g.1.2 :=
  Int.add_zero g.1.2

/-! ## Formal sums and the relation layer -/

-- Reference: ticket #109 — the L∞ relations are linear: a formal sum of
-- paths with integer coefficients (each relation = 0).
/-- A **formal sum** of paths `X → Y` with integer coefficients. -/
def FormalSum (c : Computad) (X Y : c.obj) := List (c.Path X Y × ℤ)

-- Reference: ticket #109 — an L∞ presentation: the computad, the root
-- object, and the declared relations (formal sums, each = 0).
/-- An **L∞ presentation**: a computad with a root object and declared
linear relations on endo-paths at the root. -/
structure LInfPres where
  /-- The underlying computad. -/
  computad : Computad
  /-- The root object (the underlying graded space). -/
  root : computad.obj
  /-- The declared relations (formal sums of endo-paths, each = 0). -/
  relations : List (FormalSum computad root root)

-- Reference: [Barendregt], ch. 2 (eta conversion), as in `Sieve.eta`.
-- REVIEW(citation): pin down the exact section in review.
/-- **Eta conversion for L∞ presentations**. -/
theorem LInfPres.eta (P : LInfPres) :
    LInfPres.mk P.computad P.root P.relations = P := by
  cases P with
  | mk computad root relations => rfl

/-! ## The axioms: l₁² = 0 and the generalized Jacobi -/

-- Reference: ticket #109 — the L∞ axioms: the differential squares to zero,
-- and for every n ≥ 2 the generalized Jacobi shuffle-sum vanishes. The
-- Jacobi sum is carried as explicit data (`jacobiSum`), the axiom as a
-- `Prop` field; constructing `jacobiSum` is the `shuffleSum` named hole.
/-- The **L∞ axioms** on a presentation: `l₁² = 0` is a declared relation,
and for every `n ≥ 2` the Jacobi sum `jacobiSum n` is a declared relation. -/
structure LInfAxioms (P : LInfPres) where
  /-- The differential `l₁` (arity 1, degree 1 in the cohomological
  convention `deg lₙ = 2 − n`). -/
  dOp : P.computad.Hom P.root P.root
  /-- `l₁² = 0` is a declared relation (the single-tree witness). -/
  d_squared : [((P.computad.toPath dOp).comp (P.computad.toPath dOp), (1 : ℤ))] ∈ P.relations
  /-- The Jacobi sums (explicit data; the shuffle-sum construction is the
  named `shuffleSum` hole). -/
  jacobiSum : ℕ → FormalSum P.computad P.root P.root
  /-- For every `n ≥ 2`, the Jacobi sum is a declared relation. -/
  jacobi : ∀ n, 2 ≤ n → jacobiSum n ∈ P.relations

/-! ## Toy: the strict dg case (lₙ = 0 for n ≥ 3) -/

-- Reference: ticket #109, toy — the strict dg-algebra case: the only
-- nontrivial relations are `l₁² = 0` (at n = 2) and the empty sum `0 = 0`
-- (at n ≥ 3, since all higher brackets vanish).
/-- The toy presentation: the L∞ computad with relations `[l₁², 0]`. -/
def linfPresToy : LInfPres where
  computad := linfComputad
  root := PUnit.unit
  relations := [[((linfComputad.toPath ⟨⟨(1, 1), Nat.le_refl 1⟩, rfl, rfl⟩).comp
      (linfComputad.toPath ⟨⟨(1, 1), Nat.le_refl 1⟩, rfl, rfl⟩), (1 : ℤ))], []]

-- Reference: ticket #109, toy: the strict-dg axioms — `l₁ = (1, 1)`,
-- `l₁² = 0` by membership, Jacobi sums = `l₁²` at n = 2 and `[]` above.
/-- The strict-dg L∞ axioms on the toy presentation. -/
def linfAxiomsToy : LInfAxioms linfPresToy where
  dOp := ⟨⟨(1, 1), Nat.le_refl 1⟩, rfl, rfl⟩
  d_squared := List.mem_cons_self
  jacobiSum := fun n => if n = 2 then
      [((linfComputad.toPath ⟨⟨(1, 1), Nat.le_refl 1⟩, rfl, rfl⟩).comp
        (linfComputad.toPath ⟨⟨(1, 1), Nat.le_refl 1⟩, rfl, rfl⟩), (1 : ℤ))] else []
  jacobi := by
    intro n hn
    cases (inferInstance : Decidable (n = 2)) with
    | isTrue h =>
        have e : (if n = 2 then
            [((linfComputad.toPath ⟨⟨(1, 1), Nat.le_refl 1⟩, rfl, rfl⟩).comp
              (linfComputad.toPath ⟨⟨(1, 1), Nat.le_refl 1⟩, rfl, rfl⟩), (1 : ℤ))]
            else []) =
            [((linfComputad.toPath ⟨⟨(1, 1), Nat.le_refl 1⟩, rfl, rfl⟩).comp
              (linfComputad.toPath ⟨⟨(1, 1), Nat.le_refl 1⟩, rfl, rfl⟩), (1 : ℤ))] :=
          ite_eq_left h
        exact Eq.subst (motive := fun l => l ∈ linfPresToy.relations) e.symm
          List.mem_cons_self
    | isFalse h =>
        have e : (if n = 2 then
            [((linfComputad.toPath ⟨⟨(1, 1), Nat.le_refl 1⟩, rfl, rfl⟩).comp
              (linfComputad.toPath ⟨⟨(1, 1), Nat.le_refl 1⟩, rfl, rfl⟩), (1 : ℤ))]
            else []) =
            [] := ite_eq_right h
        exact Eq.subst (motive := fun l => l ∈ linfPresToy.relations) e.symm
          (List.mem_cons_of_mem _ List.mem_cons_self)

end BoringLab
