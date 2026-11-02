/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import BoringLab.Doctrine.Geometric

/-!
# Normal-play Nim as a geometric theory: rules of play as sequents

The checkable GL instance (`EnidAnderson/BoringLab#14`, item (iii)): the
rules of normal-play Nim presented as a computad + doctrine, at the
polygraph level:

* positions are natural numbers (one pile), and a **legal move** is a
  generator — a triple `(n, m, k)` with `m + k = n` and `0 < k`, read
  "from `n`, remove `k`, leaving `m`" (addition-only encoding: no subtraction
  in the typing, so every legality proof is `rfl`-closed arithmetic);
* the **rules of play as geometric sequents** are the declared moves of
  `nimDoctrine`: two removals commute — from `n`, remove `k` then `j`
  equals remove `j` then `k` (the exchange/join shape of the geometric
  fragment), declared as a move between parallel paths
  (`nim_commute_witness` instantiates it at `n = 5, k = 2, j = 1`);
* the falsifiable shadow: the commutation sequent is inverted in the
  doctrine-localization (`nim_commute_inverted`), via the A2.0 inversion
  machinery.

## References
* [Conway] J. H. Conway, *On Numbers and Games*, 2nd ed., A K Peters, 2000 —
  impartial games; Nim (the subtraction-game form).
* [Berlekamp–Conway–Guy] *Winning Ways for Your Mathematical Plays*,
  vol. 1, Academic Press, 1982 — ch. on Nim (the rules: remove any positive
  number of counters from one pile; normal play: last move wins).
* [Mimram] S. Mimram, *Polygraphs: from rewriting to higher categories*,
  arXiv:2312.00429, LMCS 21(3) (2025), Definition 3.5 (relations between
  parallel paths = sequents).
* Program register: ticket #14 (LAB TREE GL.0), item (iii) — the
  falsifiable-presentation statement instantiated at Nim.
-/

namespace BoringLab

open CategoryTheory

/-! ## The Nim computad: positions and legal moves -/

-- Reference: [Berlekamp–Conway–Guy], vol. 1 (Nim: a move removes a positive
-- number of counters from one pile); the addition-only triple encoding is
-- the program's own (legality = `m + k = n ∧ 0 < k`).
-- REVIEW(citation): pin the Nim chapter of [Berlekamp–Conway–Guy] in
-- review.
/-- The **Nim computad**: objects are pile sizes (`ℕ`); a generator is a
legal removal — a triple `(n, m, k)` with `m + k = n` and `0 < k` — from
`n` to `m`. Ports are trivial (`PUnit`). -/
def nimComputad : Computad where
  port := PUnit
  portMul := fun _ _ => PUnit.unit
  portOne := PUnit.unit
  portMul_assoc := fun _ _ _ => rfl
  portMul_left_one := fun _ => rfl
  portMul_right_one := fun _ => rfl
  obj := ℕ
  gen := {t : ℕ × ℕ × ℕ // t.2.1 + t.2.2 = t.1 ∧ 0 < t.2.2}
  src := fun g => g.1.1
  tgt := fun g => g.1.2.1
  leftPorts := fun _ => []
  rightPorts := fun _ => []

-- Reference: [Berlekamp–Conway–Guy], vol. 1 (normal-play convention: the
-- rules themselves are the generators; the convention is the terminal
-- stratum — see the GL.0 reading, ticket #14).
/-- The **Nim doctrine**: the Nim computad with the declared moves being the
commutations of two removals — from `X`, remove `k` then `j` (via middle
pile `M`) equals remove `j` then `k` (via middle pile `M'`), both ending at
`Y`. The exchange/join sequent of the geometric fragment. -/
def nimDoctrine : Doctrine where
  computad := nimComputad
  move := fun {X Y : ℕ} p q =>
    ∃ (M M' k j : ℕ) (hk : 0 < k) (hj : 0 < j)
      (h1 : M + k = X) (h2 : Y + j = M) (h3 : M' + j = X) (h4 : Y + k = M'),
      p = (nimComputad.toPath ⟨⟨⟨X, M, k⟩, h1, hk⟩, rfl, rfl⟩).comp
            (nimComputad.toPath ⟨⟨⟨M, Y, j⟩, h2, hj⟩, rfl, rfl⟩) ∧
      q = (nimComputad.toPath ⟨⟨⟨X, M', j⟩, h3, hj⟩, rfl, rfl⟩).comp
            (nimComputad.toPath ⟨⟨⟨M', Y, k⟩, h4, hk⟩, rfl, rfl⟩)

/-! ## The commutation sequent: witness and inversion -/

-- Reference: ticket #14, item (iii); [Mimram], Definition 3.5. The witness:
-- from `5` remove `2` (leaving `3`) then `1` (leaving `2`), versus remove
-- `1` (leaving `4`) then `2` (leaving `2`) — all legality equations are
-- closed `ℕ` arithmetic (`rfl`); `0 < 2` is `Nat.succ_pos 1`, `0 < 1` is
-- `Nat.succ_pos 0`.
/-- **The commutation sequent holds at `5, k = 2, j = 1`**: the two removal
orders are a declared move. -/
theorem nim_commute_witness :
    nimDoctrine.move
      ((nimComputad.toPath ⟨⟨⟨5, 3, 2⟩, rfl, Nat.succ_pos 1⟩, rfl, rfl⟩).comp
        (nimComputad.toPath ⟨⟨⟨3, 2, 1⟩, rfl, Nat.succ_pos 0⟩, rfl, rfl⟩))
      ((nimComputad.toPath ⟨⟨⟨5, 4, 1⟩, rfl, Nat.succ_pos 0⟩, rfl, rfl⟩).comp
        (nimComputad.toPath ⟨⟨⟨4, 2, 2⟩, rfl, Nat.succ_pos 1⟩, rfl, rfl⟩)) :=
  ⟨3, 4, 2, 1, Nat.succ_pos 1, Nat.succ_pos 0, rfl, rfl, rfl, rfl, rfl, rfl⟩

-- Reference: ticket #14, item (iii) (the falsifiable shadow, binding);
-- [Gabriel–Zisman], Chapter I, via `Doctrine.declared_move_inverted`
-- (LAB A2.0): both sides of the commutation sequent are inverted in the
-- doctrine-localization.
-- REVIEW(citation): as on `nim_commute_witness`.
/-- **The commutation sequent is inverted in the localization**: both removal
orders become isomorphisms — order-independence of independent moves, as
localized data. -/
theorem nim_commute_inverted :
    IsIso (nimDoctrine.moveClass.Q.map
      ((nimComputad.toPath ⟨⟨⟨5, 3, 2⟩, rfl, Nat.succ_pos 1⟩, rfl, rfl⟩).comp
        (nimComputad.toPath ⟨⟨⟨3, 2, 1⟩, rfl, Nat.succ_pos 0⟩, rfl, rfl⟩))) ∧
    IsIso (nimDoctrine.moveClass.Q.map
      ((nimComputad.toPath ⟨⟨⟨5, 4, 1⟩, rfl, Nat.succ_pos 0⟩, rfl, rfl⟩).comp
        (nimComputad.toPath ⟨⟨⟨4, 2, 2⟩, rfl, Nat.succ_pos 1⟩, rfl, rfl⟩))) :=
  Doctrine.declared_move_inverted nimDoctrine _ _ nim_commute_witness

-- Reference: ticket #14, item (i) — the sequent form of the witness via
-- `Doctrine.toSequent` / `GeometricSequent` (BoringLab.Doctrine.Geometric).
/-- The commutation witness as a **geometric sequent** of the Nim computad. -/
def nimCommuteSequent : GeometricSequent nimComputad :=
  Doctrine.toSequent nimDoctrine
    ((nimComputad.toPath ⟨⟨⟨5, 3, 2⟩, rfl, Nat.succ_pos 1⟩, rfl, rfl⟩).comp
      (nimComputad.toPath ⟨⟨⟨3, 2, 1⟩, rfl, Nat.succ_pos 0⟩, rfl, rfl⟩))
    ((nimComputad.toPath ⟨⟨⟨5, 4, 1⟩, rfl, Nat.succ_pos 0⟩, rfl, rfl⟩).comp
      (nimComputad.toPath ⟨⟨⟨4, 2, 2⟩, rfl, Nat.succ_pos 1⟩, rfl, rfl⟩))

-- Reference: `Doctrine.toSequent_move`.
/-- The sequent's declaration certificate. -/
theorem nimCommuteSequent_move :
    nimDoctrine.move nimCommuteSequent.antecedent nimCommuteSequent.succedent :=
  Doctrine.toSequent_move nimDoctrine _ _ nim_commute_witness

end BoringLab
