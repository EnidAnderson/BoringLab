/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import BoringLab.Doctrine.Nim

/-!
# The first hyperdoctrine instance: the Nim presentation over its scope

The GL-line payoff (`EnidAnderson/BoringLab#14`): a fully proved
`Hyperdoctrine` instance (`nimHyperdoctrine`) built on the Nim presentation
(`BoringLab.Doctrine.Nim`). The base is the one-scope computad `nimScope`
(one object, one generator — the identity scope); every fiber is the Nim
doctrine; substitution is the identity polygraph morphism, so the quantifier
adjunction fields `exists_adj` / `forall_adj` hold by `Computad.Morph.mapPath_id`
— the toy instance where pullback is trivial and `∃ = ∀ = identity` on
endo-paths at the root. The transport of the commutation sequent along
substitution is derived (`nimHyperdoctrine_commute_transport`).

Scope honesty: this is the degenerate (single-scope, identity-substitution)
instance — the honest first rung; nontrivial scopes (e.g. the inclusion of a
sub-position) are the named next step, with the adjunction fields then
requiring real proofs (peeling plan in `docs/geometric-logic.md`).

## References
* [Lawvere] F. W. Lawvere, *Adjointness in foundations*, Dialectica 23 (1969),
  135–145 (hyperdoctrines; `∃ ⊣ f* ⊣ ∀`).
* [Mimram] S. Mimram, *Polygraphs: from rewriting to higher categories*,
  arXiv:2312.00429, LMCS 21(3) (2025), §3 (polygraph morphisms).
* Program register: ticket #14 (LAB TREE GL.0); the Nim instance of ticket
  #14 item (iii).
-/

namespace BoringLab

/-! ## The one-scope base -/

-- Reference: ticket #14 (base = scopes); the one-object/one-generator
-- computad as explicit data (as `misereQuotientComputad`'s trivial ports).
/-- The **one-scope computad**: a single object and a single generator (the
identity scope), ports trivial. -/
def nimScope : Computad where
  port := PUnit
  portMul := fun _ _ => PUnit.unit
  portOne := PUnit.unit
  portMul_assoc := fun _ _ _ => rfl
  portMul_left_one := fun _ => rfl
  portMul_right_one := fun _ => rfl
  obj := PUnit
  gen := PUnit
  src := fun _ => PUnit.unit
  tgt := fun _ => PUnit.unit
  leftPorts := fun _ => []
  rightPorts := fun _ => []

/-! ## The instance -/

-- Reference: [Lawvere], *Adjointness in foundations* (1969); ticket #14:
-- fiber = the Nim doctrine at every scope; substitution = identity morphism;
-- quantifiers = identity on endo-paths at the root `0`; adjunctions by
-- `Computad.Morph.mapPath_id`.
-- REVIEW(citation): pin the exact page of [Lawvere] in review.
/-- The **Nim hyperdoctrine**: the degenerate first instance of
`Hyperdoctrine` — one scope, fiber = `nimDoctrine`, root `0`, substitution
the identity polygraph morphism, `∃`/`∀` the identity on root endo-paths.
All adjunction fields are proved (by `mapPath_id`), no sorries. -/
def nimHyperdoctrine : Hyperdoctrine where
  scope := nimScope
  fiber := fun _ => nimDoctrine
  root := fun _ => (0 : ℕ)
  subst := fun _ => Computad.Morph.id nimComputad
  subst_root := fun _ => rfl
  subst_move := fun _g _X _Y p q h =>
    Eq.subst
      (motive := fun r =>
        nimDoctrine.move r (Computad.Morph.mapPath (Computad.Morph.id nimComputad) q))
      (Computad.Morph.mapPath_id p).symm
      (Eq.subst (motive := fun s => nimDoctrine.move p s)
        (Computad.Morph.mapPath_id q).symm h)
  existsMap := fun _g φ => φ
  forallMap := fun _g φ => φ
  exists_adj := fun _g φ ψ =>
    Iff.intro
      (fun h => Eq.subst (motive := fun r => nimDoctrine.move φ r)
        (Computad.Morph.mapPath_id ψ) h)
      (fun h => Eq.subst (motive := fun r => nimDoctrine.move φ r)
        (Computad.Morph.mapPath_id ψ).symm h)
  forall_adj := fun _g φ ψ =>
    Iff.intro
      (fun h => Eq.subst (motive := fun r => nimDoctrine.move r φ)
        (Computad.Morph.mapPath_id ψ) h)
      (fun h => Eq.subst (motive := fun r => nimDoctrine.move r φ)
        (Computad.Morph.mapPath_id ψ).symm h)

-- Reference: ticket #14, item (ii)–(iii): substitution transports the
-- declared commutation sequent — from `nimHyperdoctrine.subst_move` and
-- `nimCommuteSequent_move`.
/-- **Substitution transports the Nim commutation sequent**: the identity
substitution of the hyperdoctrine preserves the declared move (via
`subst_move` and `mapPath_id`). -/
theorem nimHyperdoctrine_commute_transport :
    nimDoctrine.move
      ((Computad.Morph.id nimComputad).mapPath nimCommuteSequent.antecedent)
      ((Computad.Morph.id nimComputad).mapPath nimCommuteSequent.succedent) :=
  nimHyperdoctrine.subst_move PUnit.unit nimCommuteSequent.antecedent
    nimCommuteSequent.succedent nimCommuteSequent_move

end BoringLab
