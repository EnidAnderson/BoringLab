/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import BoringLab.Deform.LInf
import BoringLab.Doctrine.TypedHoles

/-!
# The derivative of a linear homotopy type, literally: `l₁` in the L∞ computad

Lab ticket (BoringLab #112). In the L∞ computad (`Deform/LInf.lean`), the port
monoid is `ℤ` with `+` — the **cohomological degree**. The generator of arity 1
and degree 1 is the bracket `l₁`: this *is* the derivative of the presented
linear homotopy type. This module makes that literal and proves the degree
bookkeeping: the derivative raises the right port word (the degree) by exactly
`1`, and `l₁² = 0` is the declared relation (the toy witness).

The typed-hole picture (`Doctrine/TypedHoles.lean`): at the one-object computad,
the one-hole contexts at the root are the endo-paths, plugging is composition,
and a hole is well-typed exactly when the degrees (port words) match — so
"derivative = type of holes" and "plugging a hole = applying l₁" line up with
the port typing.

Motivic connections (explicit pointers; identifications are plan items, see
tickets #113–#116): cohomological degree = the `ℤ` port monoid; the Tate twist
`𝟙(1)` is the degree-1 port (the degree of `l₁`); the A¹-interval is the
thickening data of `Deform/Deform.lean`; Nisnevich/cdh descent
(`BoringMath .../Sites/Nisnevich.lean`, `.../Sites/CdStructure.lean`) is the
local-to-global principle for these degree shifts.

## References
* [Lada–Stasheff] J. Pure Appl. Algebra 48 (1987) (deg lₙ = 2 − n, so deg l₁ = 1).
* [Lurie] DAG X (formal moduli; the cotangent complex is the linear
  derivative) — connection labeled as plan.
* [Abbott–Altenkirch–Ghani] (derivatives of types = one-hole contexts).
* Program register: BoringLab #108 (DEFORM.0), #109 (LINF.0), #112+.
-/

namespace BoringLab

/-- The **differential** `l₁`: the generator of arity `1` and degree `1`
(cohomological convention `deg lₙ = 2 − n`). -/
-- Reference: [Lada–Stasheff] (deg lₙ = 2 − n, so deg l₁ = 1); `LInf.lean` toy generator.
def linfDifferential : linfComputad.gen := ⟨(1, 1), Nat.le_refl 1⟩

-- Reference: computation step; `linfComputad.pathRightWord_toPath` gives the
-- degree `g.1.2`, and `linfDifferential.1.2 = 1` definitionally.
/-- **The differential has degree `1`** (proved): its right port word is `1`. -/
theorem linfDifferential_degree :
    linfComputad.pathRightWord (linfComputad.toPath ⟨linfDifferential, rfl, rfl⟩) = (1 : ℤ) :=
  (linfComputad.pathRightWord_toPath _).trans rfl

/-- The **derivative of the root type** as an endomap of endo-paths at the
root: precompose with `l₁` (plug the universal hole with the differential). -/
def linfDerivative (p : linfComputad.Path PUnit.unit PUnit.unit) :
    linfComputad.Path PUnit.unit PUnit.unit :=
  (linfComputad.toPath ⟨linfDifferential, rfl, rfl⟩).comp p

-- Reference: [Lada–Stasheff] (deg l₁ = 1) + Computad's `pathRightWord_comp`;
-- the port product is `Int.add`.
/-- **The derivative raises cohomological degree by exactly `1`** (proved):
`deg (l₁ ∘ p) = 1 + deg p`. -/
theorem linfDerivative_degree (p : linfComputad.Path PUnit.unit PUnit.unit) :
    linfComputad.pathRightWord (linfDerivative p) =
      linfComputad.portMul (1 : ℤ) (linfComputad.pathRightWord p) :=
  (linfComputad.pathRightWord_comp _ _).trans
    (congrArg (fun w => linfComputad.portMul w (linfComputad.pathRightWord p))
      linfDifferential_degree)

-- Reference: toy witness in `LInf.lean` (`linfAxiomsToy.d_squared`); [Lada–Stasheff]
-- (the differential squares to zero).
theorem linfDifferential_sq_zero_toy :
    [((linfComputad.toPath ⟨linfDifferential, rfl, rfl⟩).comp
        (linfComputad.toPath ⟨linfDifferential, rfl, rfl⟩), (1 : ℤ))] ∈
      linfPresToy.relations :=
  linfAxiomsToy.d_squared

-- Reference: [Abbott–Altenkirch–Ghani] (derivative = one-hole contexts);
-- TypedHoles' `oneHoleContexts`. Since the L∞ computad has one object, the
-- one-hole contexts at the root are the endo-paths.
/-- The **derivative type** of the root: endo-paths at the root object (the
one-hole contexts, since `obj = PUnit` is a singleton). -/
def linfDerivativeType : Type := linfComputad.Path PUnit.unit PUnit.unit

-- Reference: as above — `oneHoleContexts` at a subsingleton object is the
-- endo-path type (the `Σ` collapses to the endo-paths, up to equivalence).
/-- The one-hole contexts at the root are equivalent to the endo-paths
(proved: the `Σ` over the singleton object collapses). -/
def oneHoleContextsEquiv :
    linfComputad.oneHoleContexts PUnit.unit ≃ linfDerivativeType where
  toFun p := cast
    (congrArg (fun Z : linfComputad.obj => Quiver.Path Z PUnit.unit)
      (@Subsingleton.elim _ (inferInstanceAs (Subsingleton PUnit)) p.1 PUnit.unit))
    p.2
  invFun p := ⟨PUnit.unit, p⟩
  left_inv p := by
    have h : p.1 = PUnit.unit :=
      @Subsingleton.elim _ (inferInstanceAs (Subsingleton PUnit)) p.1 PUnit.unit
    exact Sigma.ext h
      (cast_heq (congrArg (fun Z : linfComputad.obj => Quiver.Path Z PUnit.unit) h) p.2)
  right_inv _ := rfl
-- Reference: [Abbott–Altenkirch–Ghani] (derivative = one-hole contexts);
-- TypedHoles' `oneHoleContexts` (the `Σ` over the singleton object collapses).
theorem oneHoleContexts_linf_root :
    Nonempty (linfComputad.oneHoleContexts PUnit.unit ≃ linfDerivativeType) :=
  ⟨oneHoleContextsEquiv⟩
end BoringLab
