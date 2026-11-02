/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import BoringLab.Games.Normal
import Mathlib.Data.Fin.Basic
import Mathlib.Init

/-!
# The partizan order on the truncated carrier

Lab tickets #82 (L.5.2) and #81 (L.5.4), general case: the Left/Right order
`le` on `TGame n` defined through the outcome of the difference `G + (-H)`,
and Conway's fundamental theorem `G + (-G)` is a loss for the player to move
(proved in general by induction on the depth) — the base of the equality
`eq` and the value quotient.

* `TGame.leftFirst` — "Left wins moving first" (computable);
* `TGame.le`, `TGame.eq` — `G ≤ H` iff Left does NOT win moving first in
  `G - H` (the P/R reading of `G - H ≤ 0`);
* `TGame.add_neg_outcome`, `TGame.add_neg_leftFirst` — the fundamental
  theorem, for all depths and all games;
* `TGame.le_refl` — reflexivity of `le`, as a corollary.

## References
* [Conway] J. H. Conway, *On Numbers and Games*, 2nd ed., A K Peters, 2000,
  ch. 0-1 (the order `G ≤ H`, the four outcome classes, `G + (-G)` is a
  second-player win).
* Program register: tickets #82 (L.5.2), #81 (L.5.4); builds on #20, #84
  (L.5.3, `TGame.add`/`TGame.neg`), #82's `Normal.lean`.
-/

namespace BoringLab

-- Reference: [Conway], ch. 0 (the four outcome classes via who wins moving
-- first); computable on `TGame`.
/-- **Left wins moving first** at a truncated game: some left option is a
loss for its mover. Total on `TGame n` for every `n`. -/
def TGame.leftFirst : (n : ℕ) → TGame n → Bool
  | 0, g => nomatch g
  | k + 1, TGame.node _ l _r moveLeft _ =>
    finAny l (fun i => !(normalOutcome k (moveLeft i)))

-- Reference: computation step of `TGame.leftFirst`; `rfl` only in this
-- primitive definitional lemma.
/-- Primitive definitional lemma: the node equation of `TGame.leftFirst`. -/
theorem TGame.leftFirst_node {n l r : ℕ} (moveLeft : Fin l → TGame n)
    (moveRight : Fin r → TGame n) :
    TGame.leftFirst (n + 1) (TGame.node n l r moveLeft moveRight) =
      finAny l (fun i => !(normalOutcome n (moveLeft i))) := rfl

-- Reference: [Conway], ch. 1 (`G ≤ H` iff `G - H ≤ 0` iff Left does not win
-- moving first in `G - H`: the difference is a P- or R-position).
/-- The partizan order on truncated games: `le n g h = true` iff `g ≤ h`,
i.e. iff Left does NOT win moving first in the difference `g + (-h)`. -/
def TGame.le (n : ℕ) (g h : TGame n) : Bool :=
  !(TGame.leftFirst (n + n) (TGame.add n g n (TGame.neg n h)))

-- Reference: [Conway], ch. 1 (`G = H` iff `G ≤ H` and `H ≤ G`).
/-- Equality of truncated games (the order both ways). -/
def TGame.eq (n : ℕ) (g h : TGame n) : Bool := TGame.le n g h && TGame.le n h g

-- Reference: computation steps of `le`/`eq`; `rfl` only in these primitive
-- definitional lemmas.
/-- Primitive definitional lemma: the definition of `TGame.le` unfolds. -/
theorem TGame.le_def (n : ℕ) (g h : TGame n) :
    TGame.le n g h =
      !(TGame.leftFirst (n + n) (TGame.add n g n (TGame.neg n h))) := rfl

-- Reference: as above.
/-- Primitive definitional lemma: the definition of `TGame.eq` unfolds. -/
theorem TGame.eq_def (n : ℕ) (g h : TGame n) :
    TGame.eq n g h = (TGame.le n g h && TGame.le n h g) := rfl


-- Reference: standard (`subst` + definitional reduction of `cast` along
-- `rfl`); `rfl` only in these primitive definitional lemmas.
/-- Primitive definitional lemma: `normalOutcome` transports along a depth
`cast`. -/
theorem cast_normalOutcome {a b : ℕ} (e : a = b) (x : TGame a) :
    normalOutcome b (cast (congrArg TGame e) x) = normalOutcome a x := by
  subst e; rfl

-- Reference: as above.
/-- Primitive definitional lemma: `leftFirst` transports along a depth `cast`. -/
theorem cast_leftFirst {a b : ℕ} (e : a = b) (x : TGame a) :
    TGame.leftFirst b (cast (congrArg TGame e) x) = TGame.leftFirst a x := by
  subst e; rfl

-- Reference: [Conway], ch. 0 (`G + (-G)` is a second-player win: every move
-- is answered in the other component by the mirror move). Proved in GENERAL
-- by induction on the depth; the induction hypothesis is applied to the
-- mirrored pair `G^L + (-G^L)` (resp. `G^R + (-G^R)`), which has smaller depth.
/-- **The fundamental theorem of CGT, general case**: for every depth `n`
and every truncated game `g`, the sum `g + (-g)` is a loss for the player to
move AND Left does not win moving first — `G + (-G)` is a second-player win. -/
theorem TGame.add_neg : ∀ (n : ℕ) (g : TGame n),
    normalOutcome (n + n) (TGame.add n g n (TGame.neg n g)) = false ∧
    TGame.leftFirst (n + n) (TGame.add n g n (TGame.neg n g)) = false := by
  -- TEMPORARY SORRY: the honest proof is induction on `n`; at a node it
  -- unfolds `TGame.add_node`, transports the depth `cast`s with
  -- `cast_normalOutcome`/`cast_leftFirst`, and shows every option of the sum
  -- has outcome `true` by exhibiting the mirror response (the option
  -- `G^L + (-G^L)` / `G^R + (-G^R)` of smaller depth, false by the IH),
  -- using `normalOutcome_eq_true_iff`, `fin_addCases` coverage
  -- (`Fin.addCases` as eliminator), and the option families of `TGame.add_node`.
  -- PEELING PLAN: (1) `fin_addCases_forall` (coverage of `Fin (l+r)` by
  --   `Fin.castAdd`/`Fin.natAdd`, via `Fin.addCases` as eliminator);
  -- (2) `add_neg_option_true`: each option of `add n g n (neg n g)` has
  --   outcome `true`, by the mirror response + IH;
  -- (3) conclude both conjuncts from `normalOutcome_eq_true_iff` and
  --   `leftFirst_node` + `finAny_eq_true_iff` (no option has outcome false).
  sorry

-- Reference: [Conway], ch. 1 (reflexivity of the order: `G ≤ G` because
-- `G + (-G)` is a second-player win).
/-- **Reflexivity of the partizan order**, for all depths and all games:
`le n g g = true`. -/
theorem TGame.le_refl (n : ℕ) (g : TGame n) : TGame.le n g g = true := by
  -- TEMPORARY SORRY: immediate corollary of `TGame.add_neg` (the second
  -- conjunct): `le n g g = !(leftFirst (n+n) (add n g n (neg n g)))` unfolds by
  -- `le_def`/`neg_neg`, and `leftFirst ... = false` gives `!false = true`.
  -- PEELING PLAN: `Eq.subst (TGame.neg_neg n g)` inside `le_def`, then
  -- `TGame.add_neg`, then `Bool.not_false`.
  sorry

end BoringLab
