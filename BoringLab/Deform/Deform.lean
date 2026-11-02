/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import BoringLab.Deform.LInf
import BoringLab.Doctrine.Geometric

/-!
# LAB DEFORM.0: deformation theory at the computad level (statement layer)

Ticket #108 (LAB DEFORM.0). Lurie-style deformation theory in the
pure-composition form: a formal moduli problem is a functor on artinian
thickenings; here the thickenings are DATA (a ring as explicit operations
`RingData`, a square-zero ideal `Thickening`), and a deformation problem is
a DOCTRINE over thickenings — objects = thickenings of a fixed base,
generators = square-zero extensions, declared moves = the obstruction
classes (formal sums). The Maurer–Cartan locus of an L∞ algebra
(LINF.0, #109) is the deformation functor's value — Deligne's principle —
recorded as the MC shadow row (named hole: element substitution into the
brackets).

## References
* [Lurie] J. Lurie, *Derived Algebraic Geometry* (2004 thesis) and
  "Formal Moduli Problems" (DAG X) — formal moduli problems as functors on
  artinian algebras.
* [Kontsevich] M. Kontsevich, "Deformation quantization of Poisson
  manifolds", q-alg/9709040 — formal Poisson structures = L∞ on
  multivectors (the motivating instance of LINF.0/DEFORM.0).
* [Deligne] P. Deligne, letters to D. Morgan (1970s) — the Maurer–Cartan
  equation and the Deligne principle.
* [Getzler] E. Getzler, *Annals of Mathematics* 170 (2009), 271–310.
* Program register: BoringLab ticket #108 (LAB DEFORM.0); the L∞ side is
  #109 (landed, `BoringLab.Deform.LInf`).
-/

namespace BoringLab

/-! ## Rings as explicit data -/

-- Reference: [Mac Lane], ch. VIII (rings); STYLE §2.3 — the ring as
-- explicit operations + laws, never instance-chosen.
/-- A **ring as data**: a carrier with explicit addition, multiplication,
zero, one, and the ring laws as `Prop` fields. -/
structure RingData where
  /-- The carrier. -/
  car : Type
  /-- Addition. -/
  add : car → car → car
  /-- Multiplication. -/
  mul : car → car → car
  /-- Zero. -/
  zero : car
  /-- One. -/
  one : car
  /-- Addition is associative. -/
  add_assoc : ∀ a b c, add (add a b) c = add a (add b c)
  /-- Addition is commutative. -/
  add_comm : ∀ a b, add a b = add b a
  /-- Zero is the additive unit. -/
  add_zero : ∀ a, add zero a = a
  /-- Multiplication is associative. -/
  mul_assoc : ∀ a b c, mul (mul a b) c = mul a (mul b c)
  /-- One is the multiplicative unit. -/
  mul_one : ∀ a, mul one a = a
  /-- Left distributivity. -/
  mul_add : ∀ a b c, mul a (add b c) = add (mul a b) (mul a c)

-- Reference: [Barendregt], ch. 2 (eta conversion), as in `Sieve.eta`.
-- REVIEW(citation): pin down the exact section in review.
/-- **Eta conversion for ring data**. -/
theorem RingData.eta (R : RingData) :
    RingData.mk R.car R.add R.mul R.zero R.one R.add_assoc R.add_comm R.add_zero
      R.mul_assoc R.mul_one R.mul_add = R := by
  cases R with
  | mk car add mul zero one add_assoc add_comm add_zero mul_assoc mul_one mul_add => rfl

/-! ## Artinian thickenings -/

-- Reference: ticket #108 — a (square-zero) thickening of a ring: an ideal
-- predicate closed under addition, with `I · I = 0` (the square-zero
-- condition — the level-1 nilpotence; the higher nilpotence levels are the
-- EPI.8 truncation regimes).
/-- A **square-zero thickening** of a ring: an ideal predicate, closed
under addition, with `I · I = 0`. -/
structure Thickening (R : RingData) where
  /-- The ideal, as a predicate. -/
  ideal : R.car → Prop
  /-- The ideal is closed under addition. -/
  ideal_add : ∀ a b, ideal a → ideal b → ideal (R.add a b)
  /-- Square-zero: the product of two ideal elements is NOT in the ideal
  (i.e. `I · I = 0` in the quotient). -/
  sqZero : ∀ a b, ideal a → ideal b → ¬ ideal (R.mul a b)

-- Reference: [Barendregt], ch. 2 (eta conversion).
-- REVIEW(citation): pin down the exact section in review.
/-- **Eta conversion for thickenings**. -/
theorem Thickening.eta {R : RingData} (T : Thickening R) :
    Thickening.mk T.ideal T.ideal_add T.sqZero = T := by
  cases T with
  | mk ideal ideal_add sqZero => rfl

/-! ## The deformation doctrine -/

-- Reference: ticket #108 — a deformation problem as a doctrine:
-- objects = thickenings of a fixed base ring, generators = square-zero
-- extensions, declared moves = the obstruction classes (formal sums of
-- paths). The MC locus of an L∞ algebra (LINF.0) is the value of the
-- deformation functor (Deligne's principle) — the named-hole row.
/-- A **deformation problem** (pure-composition form): a base ring, a
computad of thickenings, and the declared obstruction relations. -/
structure DeformationProblem where
  /-- The base ring. -/
  base : RingData
  /-- The computad of thickenings: objects = thickenings of `base`,
  generators = square-zero extensions. -/
  thickeningComputad : Computad
  /-- The declared obstruction classes (formal sums of paths). -/
  obstructions : (X Y : thickeningComputad.obj) → List (FormalSum thickeningComputad X Y)

-- Reference: ticket #108 — the MC shadow row: the Maurer–Cartan locus of
-- an L∞ presentation is the deformation functor's value (Deligne's
-- principle). Elements of the graded space are not cells of the
-- one-object computad, so the bracket substitution is carried as data.
/-- The **Maurer–Cartan data** of an L∞ presentation: an element carrier
with degrees, the MC equation `Σₙ lₙ(e,…,e)` as a formal sum per element
(the bracket substitution is the named `elemSubst` hole), declared as a
relation on degree-1 elements. -/
structure MCData (P : LInfPres) where
  /-- The element carrier (the underlying graded space's elements). -/
  elemCar : Type
  /-- The degree of an element. -/
  degree : elemCar → ℤ
  /-- The MC equation of an element: the formal sum `Σₙ lₙ(e,…,e)`. -/
  mcEquation : elemCar → FormalSum P.computad P.root P.root
  /-- Every degree-1 element's MC equation is a declared relation. -/
  mc : ∀ e, degree e = 1 → mcEquation e ∈ P.relations

end BoringLab
