/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import BoringLab.Deform.LInf
import Mathlib.Algebra.Module.LinearMap.Basic

/-!
# Lie algebras as presented computads, and their representations (computadic way)

Lab ticket (BoringLab #128, REP.LIE.1). The **computadic presentation** of a
Lie algebra: a one-object computad (`Subsingleton c.obj`) whose generators are
the brackets, with the Jacobi identities as linear relations (`FormalSum`
from `Deform/LInf.lean`). A **representation** on a module `V` is an
evaluation of every generator to a linear endomorphism of `V` that annihilates
the relations — an algebra over the presented operad evaluated at `V`.

The higher (Lurie-style) picture, as the plan in tickets #129–#132:
`Rep(𝔤)` is a symmetric monoidal abelian category with a fiber functor, hence
Tannakian, with Tannakian group the algebraic group `G` with `Lie G = 𝔤`
(`Rep(𝔤) ≃ Rep(G)`). That is exactly why representations of semisimple Lie
algebras are "like motives but less general": `Rep(𝔤)` is Tannakian with
group `G`, while motives are Tannakian with the much larger motivic Galois
group; simple objects of `Rep(𝔤)` ↔ irreducible representations of `G` —
the same socle mechanism as #262.

## References
* [Burroni] TCS 126 (1994); [Mimram] arXiv:2312.00429 (polygraphs present
  algebras over operads).
* [Lada–Stasheff] (strict L∞ = Lie).
* [Deligne–Milne] Tannakian categories (Rep(𝔤) ≃ Rep(G)).
* Program register: BoringLab #109 (LINF.0), #128–#132.
-/

namespace BoringLab

universe u v

variable {c : Computad.{u}} {R : Type v} [Ring R] {V : Type v} [AddCommGroup V] [Module R V]

-- Reference: [Mimram] (semantics of a path = composite of edge semantics).
-- One-object computads (`Subsingleton c.obj`) are the Lie case: every edge is
-- an endo at the root.
/-- Evaluating an endo-path at the root `r` as the composite of the generator
maps (computadic semantics of a word in the brackets). -/
def evalEndo [Subsingleton c.obj] (r : c.obj) (ev : c.gen → (V →ₗ[R] V))
    {X Y : c.obj} (p : Quiver.Path X Y) (hX : X = r) (hY : Y = r) : (V →ₗ[R] V) := by
  revert hX hY
  induction p with
  | nil => intro _ _; exact LinearMap.id
  | cons q e ih =>
      intro hX hY
      exact (ev e.1).comp (ih hX (Subsingleton.elim _ _))
-- Reference: definitional (nil case).
/-- Evaluating the empty endo-path is the identity (proved). -/
theorem evalEndo_nil [Subsingleton c.obj] (r : c.obj) (ev : c.gen → (V →ₗ[R] V)) :
    evalEndo r ev (Quiver.Path.nil : Quiver.Path r r) rfl rfl = LinearMap.id := rfl

-- Reference: [Burroni]/[Mimram] (linear relations evaluate by summing with
-- integer coefficients).
/-- Evaluating a formal sum of endo-paths with integer coefficients as a
linear map. -/
def evalFormalSum [Subsingleton c.obj] (r : c.obj) (ev : c.gen → (V →ₗ[R] V))
    (s : FormalSum c r r) : (V →ₗ[R] V) :=
  s.foldr (fun pq acc => pq.2 • evalEndo r ev pq.1 rfl rfl + acc) 0

-- Reference: [Burroni]/[Mimram] (a presentation = computad at a root +
-- declared linear relations).
/-- A **presented Lie algebra**: a computad with a root object and declared
linear relations on endo-paths (the Jacobi identities live here). -/
structure LiePres where
  /-- The underlying computad (one-object in the Lie case). -/
  computad : Computad
  /-- The root object (the underlying vector space of the Lie algebra). -/
  root : computad.obj
  /-- Declared linear relations on endo-paths at the root (each evaluates to 0). -/
  relations : List (FormalSum computad root root)

-- Reference: [Barendregt] ch. 2 (eta).
/-- Eta conversion for Lie presentations. -/
theorem LiePres.eta (P : LiePres) :
    LiePres.mk P.computad P.root P.relations = P := by
  cases P with
  | mk computad root relations => rfl

-- Reference: [Mimram] (a representation = an algebra over the presented
-- operad, evaluated at `V`).
/-- A **representation** of a presented Lie algebra on `V`: an assignment of a
linear endomorphism of `V` to each generator, annihilating every declared
relation. -/
structure LieRep (P : LiePres) (R : Type v) [Ring R] (V : Type v) [AddCommGroup V]
    [Module R V] [Subsingleton P.computad.obj] where
  /-- The generator assignment. -/
  ev : P.computad.gen → (V →ₗ[R] V)
  /-- Every declared relation evaluates to zero. -/
  resp : ∀ r ∈ P.relations, evalFormalSum P.root ev r = 0

end BoringLab
