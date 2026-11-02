/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import BoringLab.Doctrine.NimHyperdoctrine

/-!
# A nontrivial-scope hyperdoctrine: the +1 shift on the Nim presentation

The GL named next step (see `docs/geometric-logic.md`): a `Hyperdoctrine`
instance over a TWO-object scope, with a non-identity substitution — the
`+1` shift polygraph morphism on the Nim computad (`shiftMorph`), transport
of declared moves along it PROVED (`nim_move_map_shift`), and the quantifier
adjunction fields as named holes (Beck–Chevalley on the nontrivial scope —
the honest content of GL.0 item (ii) at instance level).

* `shiftMorph` — the morphism `n ↦ n+1`, generators `(n, m, k) ↦ (n+1, m+1,
  k)` (legality by `Nat.succ_add`); ports trivial;
* `nim_move_map_shift` — the Nim commutation sequent transports along the
  shift (proved by re-witnessing with shifted numbers and
  `mapPath_toPath`/`mapPath_comp`);
* `twoScope` — the two-object scope computad (`Bool`, one generator
  `false → true`);
* `shiftHyperdoctrine` — the instance: fiber = the Nim doctrine at each
  scope, root `true ↦ 0`, `false ↦ 1` (so the shift preserves roots),
  substitution = `shiftMorph`; `exists_adj`/`forall_adj` are declared holes
  with peeling plans.

## References
* [Lawvere] F. W. Lawvere, *Adjointness in foundations*, Dialectica 23 (1969),
  135–145 (hyperdoctrines; Beck–Chevalley for the quantifier adjoints).
* [Mimram] S. Mimram, arXiv:2312.00429, LMCS 21(3) (2025), §3 (polygraph
  morphisms).
* Program register: ticket #14 (LAB TREE GL.0), items (ii)–(iii); the Nim
  instance of the same.
-/

namespace BoringLab

/-! ## The +1 shift morphism on the Nim computad -/

-- Reference: [Mimram], §3 (polygraph morphism); the shift `n ↦ n+1` on
-- positions, generators shifted by `Nat.succ_add`; ports trivial (`PUnit`),
-- so the port-word laws are `rfl`.
/-- The **+1 shift morphism** of the Nim computad: objects `n ↦ n+1`,
generators `(n, m, k) ↦ (n+1, m+1, k)` (legality: `(m+1)+k = n+1` from
`m+k = n` by `Nat.succ_add`). -/
def shiftMorph : Computad.Morph nimComputad nimComputad where
  portMap := fun _ => PUnit.unit
  portMap_mul := fun _ _ => rfl
  portMap_one := rfl
  objMap := fun (n : ℕ) => n + 1
  genMap := fun {X Y : ℕ} e =>
    ⟨⟨⟨X + 1, Y + 1, e.1.1.2.2⟩,
        (Nat.succ_add Y e.1.1.2.2).trans
          (congrArg Nat.succ
            ((congrArg (fun z => z + e.1.1.2.2) e.2.2.symm).trans (e.1.2.1.trans e.2.1))),
        e.1.2.2⟩, rfl, rfl⟩
  leftWord_map := fun _ => rfl
  rightWord_map := fun _ => rfl

-- Reference: computation step of `shiftMorph.genMap` (the shifted
-- generator); `rfl` only in this primitive definitional lemma.
/-- The generator part of the shift: the shifted triple. -/
theorem shiftMorph_genMap {X Y : ℕ} (e : nimComputad.Hom X Y) :
    (shiftMorph.genMap e).1 =
      ⟨⟨X + 1, Y + 1, e.1.1.2.2⟩,
        (Nat.succ_add Y e.1.1.2.2).trans
          (congrArg Nat.succ
            ((congrArg (fun z => z + e.1.1.2.2) e.2.2.symm).trans (e.1.2.1.trans e.2.1))),
        e.1.2.2⟩ := rfl

-- Reference: computation step of `mapPath` on a one-generator path;
-- `rfl` only in this primitive definitional lemma.
/-- Path transport of a one-generator path is the one-generator path of the
transported generator. -/
theorem shiftMorph_mapPath_toPath {X Y : ℕ} (e : nimComputad.Hom X Y) :
    shiftMorph.mapPath (nimComputad.toPath e) = nimComputad.toPath (shiftMorph.genMap e) := rfl

-- Reference: ticket #14, item (iii); the commutation sequent transports
-- along the shift: re-witness with all numbers `+1` (legality by
-- `Nat.succ_add`), paths by `mapPath_comp`/`mapPath_toPath`.
/-- **Nim moves transport along the +1 shift**: if `p ⇄ q` is a declared
move, so is the shifted pair. -/
theorem nim_move_map_shift {X Y : ℕ} (p q : nimComputad.Path X Y)
    (h : nimDoctrine.move p q) :
    nimDoctrine.move (shiftMorph.mapPath p) (shiftMorph.mapPath q) := by
  obtain ⟨M, M', k, j, hk, hj, h1, h2, h3, h4, hp, hq⟩ := h
  have h1' : (M + 1) + k = X + 1 := (Nat.succ_add M k).trans (congrArg Nat.succ h1)
  have h2' : (Y + 1) + j = M + 1 := (Nat.succ_add Y j).trans (congrArg Nat.succ h2)
  have h3' : (M' + 1) + j = X + 1 := (Nat.succ_add M' j).trans (congrArg Nat.succ h3)
  have h4' : (Y + 1) + k = M' + 1 := (Nat.succ_add Y k).trans (congrArg Nat.succ h4)
  have hp' : shiftMorph.mapPath p =
      (nimComputad.toPath ⟨⟨⟨X + 1, M + 1, k⟩, h1', hk⟩, rfl, rfl⟩).comp
        (nimComputad.toPath ⟨⟨⟨M + 1, Y + 1, j⟩, h2', hj⟩, rfl, rfl⟩) := by
    have e1 : shiftMorph.mapPath
        (nimComputad.toPath ⟨⟨⟨X, M, k⟩, h1, hk⟩, rfl, rfl⟩) =
        nimComputad.toPath ⟨⟨⟨X + 1, M + 1, k⟩, h1', hk⟩, rfl, rfl⟩ :=
      shiftMorph_mapPath_toPath _
    have e2 : shiftMorph.mapPath
        (nimComputad.toPath ⟨⟨⟨M, Y, j⟩, h2, hj⟩, rfl, rfl⟩) =
        nimComputad.toPath ⟨⟨⟨M + 1, Y + 1, j⟩, h2', hj⟩, rfl, rfl⟩ :=
      shiftMorph_mapPath_toPath _
    exact Eq.subst (motive := fun r => shiftMorph.mapPath r =
        (nimComputad.toPath ⟨⟨⟨X + 1, M + 1, k⟩, h1', hk⟩, rfl, rfl⟩).comp
          (nimComputad.toPath ⟨⟨⟨M + 1, Y + 1, j⟩, h2', hj⟩, rfl, rfl⟩)) hp.symm
      ((Computad.Morph.mapPath_comp shiftMorph _ _).trans (congrArg₂ Quiver.Path.comp e1 e2))
  have hq' : shiftMorph.mapPath q =
      (nimComputad.toPath ⟨⟨⟨X + 1, M' + 1, j⟩, h3', hj⟩, rfl, rfl⟩).comp
        (nimComputad.toPath ⟨⟨⟨M' + 1, Y + 1, k⟩, h4', hk⟩, rfl, rfl⟩) := by
    have e1 : shiftMorph.mapPath
        (nimComputad.toPath ⟨⟨⟨X, M', j⟩, h3, hj⟩, rfl, rfl⟩) =
        nimComputad.toPath ⟨⟨⟨X + 1, M' + 1, j⟩, h3', hj⟩, rfl, rfl⟩ :=
      shiftMorph_mapPath_toPath _
    have e2 : shiftMorph.mapPath
        (nimComputad.toPath ⟨⟨⟨M', Y, k⟩, h4, hk⟩, rfl, rfl⟩) =
        nimComputad.toPath ⟨⟨⟨M' + 1, Y + 1, k⟩, h4', hk⟩, rfl, rfl⟩ :=
      shiftMorph_mapPath_toPath _
    exact Eq.subst (motive := fun r => shiftMorph.mapPath r =
        (nimComputad.toPath ⟨⟨⟨X + 1, M' + 1, j⟩, h3', hj⟩, rfl, rfl⟩).comp
          (nimComputad.toPath ⟨⟨⟨M' + 1, Y + 1, k⟩, h4', hk⟩, rfl, rfl⟩)) hq.symm
      ((Computad.Morph.mapPath_comp shiftMorph _ _).trans (congrArg₂ Quiver.Path.comp e1 e2))
  exact ⟨M + 1, M' + 1, k, j, hk, hj, h1', h2', h3', h4', hp', hq'⟩

/-! ## The two-object scope and the instance -/

-- Reference: ticket #14 (base = scopes); two scopes `false`/`true` with one
-- generator `false → true` (explicit data, trivial ports).
/-- The **two-object scope computad**: objects `Bool`, one generator from
`false` to `true`, trivial ports. -/
def twoScope : Computad where
  port := PUnit
  portMul := fun _ _ => PUnit.unit
  portOne := PUnit.unit
  portMul_assoc := fun _ _ _ => rfl
  portMul_left_one := fun _ => rfl
  portMul_right_one := fun _ => rfl
  obj := Bool
  gen := PUnit
  src := fun _ => false
  tgt := fun _ => true
  leftPorts := fun _ => []
  rightPorts := fun _ => []

-- Reference: [Lawvere], *Adjointness in foundations* (1969); ticket #14,
-- items (ii)–(iii): the two-scope instance — fiber = the Nim doctrine
-- everywhere, root `true ↦ 0` / `false ↦ 1` (so the shift preserves roots),
-- substitution = `shiftMorph` with move transport PROVED
-- (`nim_move_map_shift`).
/-- The **shift hyperdoctrine**: the Nim presentation over the two-object
scope, with the +1 shift as substitution. The quantifier adjunction fields
are named holes (Beck–Chevalley on the nontrivial scope). -/
def shiftHyperdoctrine : Hyperdoctrine where
  scope := twoScope
  fiber := fun _ => nimDoctrine
  root := fun (b : Bool) => if b then (0 : ℕ) else (1 : ℕ)
  subst := fun _ => shiftMorph
  subst_root := fun _ => rfl
  subst_move := fun _ _ _ p q h => nim_move_map_shift p q h
  existsMap := fun _ _ => Quiver.Path.nil
  forallMap := fun _ _ => Quiver.Path.nil
  exists_adj := by
    -- TEMPORARY SORRY: the ∃⊣f* adjunction on the two-scope instance
    -- (Beck–Chevalley content, ticket #14 item (ii)).
    -- PEELING PLAN: with root true ↦ 0 / false ↦ 1, a quantifier map
    -- Path 1 1 → Path 0 0 is needed (not the identity); construct it from
    -- the shift's inverse direction on the toy fibers (the witness moves
    -- live at shifted levels), then check the iff by `nim_move_map_shift`
    -- and `mapPath_id`-style transports. Next named lemmas:
    -- `shift_existsMap`, `exists_adj_shift`.
    sorry
  forall_adj := by
    -- TEMPORARY SORRY: the f*⊣∀ adjunction on the two-scope instance —
    -- same peeling plan as `exists_adj` (named lemma `forall_adj_shift`).
    sorry

end BoringLab
