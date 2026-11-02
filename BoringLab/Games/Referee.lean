/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import BoringLab.Games.Basic
import BoringLab.Games.Misere
import Mathlib.Data.Fin.Basic
import Mathlib.Init

/-!
# The referee interleave: an S₃ action on truncated games and outcome invariance

Lab ticket #21 (L.1.2), building on `Games/Basic.lean` and `Games/Misere.lean`
(ticket #20). (a) The symmetric group S₃ as explicit computable data — a local
table of the six permutations of `Fin 3` — and its action on `TGame n` by
reindexing the left/right option functions. (b) The equivariance shadow: the
misère outcome is invariant under the action, proved by named `rfl`-primitive
lemmas and explicit enumeration on the worked-example family of
`Games/Misere.lean` and on one local 3×3 node. (c) The lab finding, stated as a
data-backed claim below. (d) The identity action (D.5).

## Lab finding (D.4, data-backed)

The `#eval` lines at the end print the S₃ action table (each permutation as
its three images on `0, 1, 2`) and, for every member `g` of the worked-example
family of `Games/Misere.lean` (`leaf1`, `leftMove`, `rightMove`, `bothMoves`,
`leftToLoss`, `chain 0..3`) and every `σ` in `s3Table`, the outcome pair
`[misereOutcome n (act σ g), misereOutcome n g]`; every pair is diagonal. On
the family the action is the identity — the option counts are `0` or `1`,
never `3`, so `reindexSide` returns the option families unchanged
(`act_fixed_*`) — hence the family invariance lemmas `misereOutcome_act_*` are
fixed-point trivialities. The depth-3 node `mixed3` (three left and three right
options) exercises the genuine permutation branch; the six lemmas
`misereOutcome_act_mixed3_*` verify invariance there by explicit computation,
using that all six options are misère losses for their mover.

What the enumeration does NOT show: invariance of `misereOutcome` under the
action for arbitrary truncated games or arbitrary option families (that would
need a permutation-invariance lemma for `finAny`, not proved here), the group
laws of `act`, and faithfulness of the action. None of these is claimed.

## References
* [Conway] J. H. Conway, *On Numbers and Games*, 2nd ed., A K Peters, 2001.
* [BCG] E. R. Berlekamp, J. H. Conway, R. K. Guy, *Winning Ways for Your
  Mathematical Plays*, 2nd ed., vol. 1, A K Peters, 2001.
* [Dummit–Foote] D. S. Dummit, R. M. Foote, *Abstract Algebra*, 3rd ed., Wiley,
  2004.
-/

namespace BoringLab

-- Reference: [Dummit–Foote], Ch. 1, §1.3 (symmetric groups; S₃ has six elements).
-- REVIEW(citation): the exact page of the six-element table is not pinned.
/-- A permutation of `Fin 3` given by its three images: `0 ↦ a`, `1 ↦ b`,
`2 ↦ c`, assembled by `Fin.cases`. -/
def permOfImages (a b c : Fin 3) : Fin 3 → Fin 3 :=
  Fin.cases (n := 2) (motive := fun _ => Fin 3) a
    (Fin.cases (n := 1) (motive := fun _ => Fin 3) b
      (Fin.cases (n := 0) (motive := fun _ => Fin 3) c Fin.elim0))

-- Reference: [Dummit–Foote], Ch. 1, §1.3 (the identity element of S₃).
/-- The identity permutation of `Fin 3`. -/
def permId : Fin 3 → Fin 3 := fun i => i

-- Reference: [Dummit–Foote], Ch. 1, §1.3 (the transposition `(0 1)` in S₃).
/-- The transposition of `Fin 3` swapping `0` and `1`. -/
def permSwap01 : Fin 3 → Fin 3 := permOfImages 1 0 2

-- Reference: [Dummit–Foote], Ch. 1, §1.3 (the transposition `(1 2)` in S₃).
/-- The transposition of `Fin 3` swapping `1` and `2`. -/
def permSwap12 : Fin 3 → Fin 3 := permOfImages 0 2 1

-- Reference: [Dummit–Foote], Ch. 1, §1.3 (the transposition `(0 2)` in S₃).
/-- The transposition of `Fin 3` swapping `0` and `2`. -/
def permSwap02 : Fin 3 → Fin 3 := permOfImages 2 1 0

-- Reference: [Dummit–Foote], Ch. 1, §1.3 (the 3-cycle `(0 1 2)` in S₃).
/-- The 3-cycle `0 ↦ 1 ↦ 2 ↦ 0` of `Fin 3`. -/
def permCycle012 : Fin 3 → Fin 3 := permOfImages 1 2 0

-- Reference: [Dummit–Foote], Ch. 1, §1.3 (the 3-cycle `(0 2 1)` in S₃).
/-- The 3-cycle `0 ↦ 2 ↦ 1 ↦ 0` of `Fin 3`. -/
def permCycle021 : Fin 3 → Fin 3 := permOfImages 2 0 1

-- Reference: [Dummit–Foote], Ch. 1, §1.3 (S₃ consists of exactly six
-- permutations). A grep of `BoringMath` at the pin shows no merged S₃ table
-- (BoringMath #159 pending), so per the ticket the table is local explicit data.
/-- The S₃ table: the six permutations of `Fin 3` as an explicit list. -/
def s3Table : List (Fin 3 → Fin 3) :=
  [permId, permSwap01, permSwap12, permSwap02, permCycle012, permCycle021]

-- Reference: [Conway], 2nd ed. 2001, Chapter 0 (`G = {G^L | G^R}`: an option
-- family is indexed by a finite set; a permutation of the index set reindexes
-- the family).
-- REVIEW(citation): same citation state as Games/Misere.lean.
/-- Reindex an option family by a permutation `σ` of `Fin 3`: a family with
exactly `3` options is precomposed with `σ`; any other family is unchanged. -/
def reindexSide (σ : Fin 3 → Fin 3) (n l : ℕ) (m : Fin l → TGame n) :
    Fin l → TGame n :=
  match l, m with
  | 3, m => fun i => m (σ i)
  | _, m => m

-- Reference: standard (unfolding `reindexSide` at `l = 3`).
/-- Primitive definitional lemma: at three options, `reindexSide` precomposes
the family with `σ`. -/
theorem reindexSide_three (σ : Fin 3 → Fin 3) (n : ℕ) (m : Fin 3 → TGame n) :
    reindexSide σ n 3 m = fun i => m (σ i) := rfl

-- Reference: standard (unfolding `reindexSide` at `l = 0`).
/-- Primitive definitional lemma: the empty option family is unchanged. -/
theorem reindexSide_zero (σ : Fin 3 → Fin 3) (n : ℕ) (m : Fin 0 → TGame n) :
    reindexSide σ n 0 m = m := rfl

-- Reference: standard (unfolding `reindexSide` at `l = 1`).
/-- Primitive definitional lemma: a one-option family is unchanged. -/
theorem reindexSide_one (σ : Fin 3 → Fin 3) (n : ℕ) (m : Fin 1 → TGame n) :
    reindexSide σ n 1 m = m := rfl

-- Reference: [Conway], 2nd ed. 2001, Chapter 0; [Dummit–Foote], Ch. 1, §1.3
-- (the action of a permutation on an indexed family of options).
-- REVIEW(citation): same citation state as Games/Misere.lean.
/-- The S₃ action on depth-truncated games, as computable data: `σ` acts on a
node by reindexing its left and right option families (`reindexSide`); the
subgames themselves are not touched. -/
def TGame.act (σ : Fin 3 → Fin 3) : (n : ℕ) → TGame n → TGame n
  | _, TGame.node m l r mL mR =>
      TGame.node m l r (reindexSide σ m l mL) (reindexSide σ m r mR)

-- Reference: standard (depth-0 case of `TGame.act`, cf. `misereOutcome_zero`).
/-- Primitive definitional lemma: `TGame 0` has no constructors. -/
theorem TGame.act_zero (σ : Fin 3 → Fin 3) (g : TGame 0) : TGame.act σ 0 g = g :=
  nomatch g

-- Reference: standard (unfolding `TGame.act` at a node, cf. `misereOutcome_node`).
/-- Primitive definitional lemma (node case): the action reindexes both option
families of a node. -/
theorem TGame.act_node (σ : Fin 3 → Fin 3) {n l r : ℕ} (mL : Fin l → TGame n)
    (mR : Fin r → TGame n) :
    TGame.act σ (n + 1) (TGame.node n l r mL mR) =
      TGame.node n l r (reindexSide σ n l mL) (reindexSide σ n r mR) := rfl

-- Reference: [Conway], 2nd ed. 2001, Chapter 0 (worked example `leaf1` of
-- Games/Misere.lean has option counts `0`, so `reindexSide` fixes it).
-- REVIEW(citation): same citation state as Games/Misere.lean.
/-- The S₃ action fixes `leaf1`: its option counts are `0`, never `3`. -/
theorem act_fixed_leaf1 (σ : Fin 3 → Fin 3) : TGame.act σ 1 leaf1 = leaf1 := rfl

-- Reference: [Conway], 2nd ed. 2001, Chapter 0 (`leftMove` has option counts
-- `1, 0`, so `reindexSide` fixes it).
-- REVIEW(citation): same citation state as Games/Misere.lean.
/-- The S₃ action fixes `leftMove`: its option counts are `1` and `0`. -/
theorem act_fixed_leftMove (σ : Fin 3 → Fin 3) : TGame.act σ 2 leftMove = leftMove :=
  rfl

-- Reference: [Conway], 2nd ed. 2001, Chapter 0 (`rightMove` has option counts
-- `0, 1`, so `reindexSide` fixes it).
-- REVIEW(citation): same citation state as Games/Misere.lean.
/-- The S₃ action fixes `rightMove`: its option counts are `0` and `1`. -/
theorem act_fixed_rightMove (σ : Fin 3 → Fin 3) : TGame.act σ 2 rightMove = rightMove :=
  rfl

-- Reference: [Conway], 2nd ed. 2001, Chapter 0 (`bothMoves` has option counts
-- `1, 1`, so `reindexSide` fixes it).
-- REVIEW(citation): same citation state as Games/Misere.lean.
/-- The S₃ action fixes `bothMoves`: its option counts are `1` and `1`. -/
theorem act_fixed_bothMoves (σ : Fin 3 → Fin 3) : TGame.act σ 2 bothMoves = bothMoves :=
  rfl

-- Reference: [Conway], 2nd ed. 2001, Chapter 0 (`leftToLoss` has option counts
-- `1, 0`, so `reindexSide` fixes it).
-- REVIEW(citation): same citation state as Games/Misere.lean.
/-- The S₃ action fixes `leftToLoss`: its option counts are `1` and `0`. -/
theorem act_fixed_leftToLoss (σ : Fin 3 → Fin 3) :
    TGame.act σ 3 leftToLoss = leftToLoss := rfl

-- Reference: [Conway], 2nd ed. 2001, Chapter 0 (`chain 0` has option counts
-- `0, 0`, so `reindexSide` fixes it).
-- REVIEW(citation): same citation state as Games/Misere.lean.
/-- The S₃ action fixes `chain 0`: its option counts are `0` and `0`. -/
theorem act_fixed_chain_zero (σ : Fin 3 → Fin 3) : TGame.act σ 1 (chain 0) = chain 0 :=
  rfl

-- Reference: [Conway], 2nd ed. 2001, Chapter 0 (`chain 1` has option counts
-- `1, 0`, so `reindexSide` fixes it).
-- REVIEW(citation): same citation state as Games/Misere.lean.
/-- The S₃ action fixes `chain 1`: its option counts are `1` and `0`. -/
theorem act_fixed_chain_one (σ : Fin 3 → Fin 3) : TGame.act σ 2 (chain 1) = chain 1 :=
  rfl

-- Reference: [Conway], 2nd ed. 2001, Chapter 0 (`chain 2` has option counts
-- `1, 0`, so `reindexSide` fixes it).
-- REVIEW(citation): same citation state as Games/Misere.lean.
/-- The S₃ action fixes `chain 2`: its option counts are `1` and `0`. -/
theorem act_fixed_chain_two (σ : Fin 3 → Fin 3) : TGame.act σ 3 (chain 2) = chain 2 :=
  rfl

-- Reference: [Conway], 2nd ed. 2001, Chapter 0 (`chain 3` has option counts
-- `1, 0`, so `reindexSide` fixes it).
-- REVIEW(citation): same citation state as Games/Misere.lean.
/-- The S₃ action fixes `chain 3`: its option counts are `1` and `0`. -/
theorem act_fixed_chain_three (σ : Fin 3 → Fin 3) : TGame.act σ 4 (chain 3) = chain 3 :=
  rfl

-- Reference: [Conway], 2nd ed. 2001 / [BCG], vol. 1, ch. 13, misère play;
-- outcome lemma `leaf1_outcome` of Games/Misere.lean.
-- REVIEW(citation): same citation state as Games/Misere.lean.
/-- Equivariance shadow (enumerated): the misère outcome of `leaf1` is invariant
under the S₃ action — `leaf1` is a fixed point (`act_fixed_leaf1`). -/
theorem misereOutcome_act_leaf1 (σ : Fin 3 → Fin 3) :
    misereOutcome 1 (TGame.act σ 1 leaf1) = misereOutcome 1 leaf1 :=
  congrArg (misereOutcome 1) (act_fixed_leaf1 σ)

-- Reference: [Conway], 2nd ed. 2001 / [BCG], vol. 1, ch. 13, misère play;
-- `leftMove_outcome` of Games/Misere.lean.
-- REVIEW(citation): same citation state as Games/Misere.lean.
/-- Equivariance shadow (enumerated): outcome invariance of `leftMove` under the
S₃ action, via the fixed point `act_fixed_leftMove`. -/
theorem misereOutcome_act_leftMove (σ : Fin 3 → Fin 3) :
    misereOutcome 2 (TGame.act σ 2 leftMove) = misereOutcome 2 leftMove :=
  congrArg (misereOutcome 2) (act_fixed_leftMove σ)

-- Reference: [Conway], 2nd ed. 2001 / [BCG], vol. 1, ch. 13, misère play;
-- `rightMove_outcome` of Games/Misere.lean.
-- REVIEW(citation): same citation state as Games/Misere.lean.
/-- Equivariance shadow (enumerated): outcome invariance of `rightMove` under
the S₃ action, via the fixed point `act_fixed_rightMove`. -/
theorem misereOutcome_act_rightMove (σ : Fin 3 → Fin 3) :
    misereOutcome 2 (TGame.act σ 2 rightMove) = misereOutcome 2 rightMove :=
  congrArg (misereOutcome 2) (act_fixed_rightMove σ)

-- Reference: [Conway], 2nd ed. 2001 / [BCG], vol. 1, ch. 13, misère play;
-- `bothMoves_outcome` of Games/Misere.lean.
-- REVIEW(citation): same citation state as Games/Misere.lean.
/-- Equivariance shadow (enumerated): outcome invariance of `bothMoves` under
the S₃ action, via the fixed point `act_fixed_bothMoves`. -/
theorem misereOutcome_act_bothMoves (σ : Fin 3 → Fin 3) :
    misereOutcome 2 (TGame.act σ 2 bothMoves) = misereOutcome 2 bothMoves :=
  congrArg (misereOutcome 2) (act_fixed_bothMoves σ)

-- Reference: [Conway], 2nd ed. 2001 / [BCG], vol. 1, ch. 13, misère play;
-- `leftToLoss_outcome` of Games/Misere.lean.
-- REVIEW(citation): same citation state as Games/Misere.lean.
/-- Equivariance shadow (enumerated): outcome invariance of `leftToLoss` under
the S₃ action, via the fixed point `act_fixed_leftToLoss`. -/
theorem misereOutcome_act_leftToLoss (σ : Fin 3 → Fin 3) :
    misereOutcome 3 (TGame.act σ 3 leftToLoss) = misereOutcome 3 leftToLoss :=
  congrArg (misereOutcome 3) (act_fixed_leftToLoss σ)

-- Reference: [Conway], 2nd ed. 2001 / [BCG], vol. 1, ch. 13, misère play;
-- `chain_outcome_zero` of Games/Misere.lean.
-- REVIEW(citation): same citation state as Games/Misere.lean.
/-- Equivariance shadow (enumerated): outcome invariance of `chain 0` under the
S₃ action, via the fixed point `act_fixed_chain_zero`. -/
theorem misereOutcome_act_chain_zero (σ : Fin 3 → Fin 3) :
    misereOutcome 1 (TGame.act σ 1 (chain 0)) = misereOutcome 1 (chain 0) :=
  congrArg (misereOutcome 1) (act_fixed_chain_zero σ)

-- Reference: [Conway], 2nd ed. 2001 / [BCG], vol. 1, ch. 13, misère play;
-- `chain_outcome_one` of Games/Misere.lean.
-- REVIEW(citation): same citation state as Games/Misere.lean.
/-- Equivariance shadow (enumerated): outcome invariance of `chain 1` under the
S₃ action, via the fixed point `act_fixed_chain_one`. -/
theorem misereOutcome_act_chain_one (σ : Fin 3 → Fin 3) :
    misereOutcome 2 (TGame.act σ 2 (chain 1)) = misereOutcome 2 (chain 1) :=
  congrArg (misereOutcome 2) (act_fixed_chain_one σ)

-- Reference: [Conway], 2nd ed. 2001 / [BCG], vol. 1, ch. 13, misère play;
-- `chain_outcome_two` of Games/Misere.lean.
-- REVIEW(citation): same citation state as Games/Misere.lean.
/-- Equivariance shadow (enumerated): outcome invariance of `chain 2` under the
S₃ action, via the fixed point `act_fixed_chain_two`. -/
theorem misereOutcome_act_chain_two (σ : Fin 3 → Fin 3) :
    misereOutcome 3 (TGame.act σ 3 (chain 2)) = misereOutcome 3 (chain 2) :=
  congrArg (misereOutcome 3) (act_fixed_chain_two σ)

-- Reference: [Conway], 2nd ed. 2001 / [BCG], vol. 1, ch. 13, misère play;
-- `chain_outcome_three` of Games/Misere.lean.
-- REVIEW(citation): same citation state as Games/Misere.lean.
/-- Equivariance shadow (enumerated): outcome invariance of `chain 3` under the
S₃ action, via the fixed point `act_fixed_chain_three`. -/
theorem misereOutcome_act_chain_three (σ : Fin 3 → Fin 3) :
    misereOutcome 4 (TGame.act σ 4 (chain 3)) = misereOutcome 4 (chain 3) :=
  congrArg (misereOutcome 4) (act_fixed_chain_three σ)

-- Reference: standard (the `Fin.cases` pattern of `permOfImages`, at values).
/-- A three-element family `Fin 3 → α` from its three values `a, b, c`. -/
def familyOfThree {α : Type} (a b c : α) : Fin 3 → α :=
  Fin.cases (n := 2) (motive := fun _ => α) a
    (Fin.cases (n := 1) (motive := fun _ => α) b
      (Fin.cases (n := 0) (motive := fun _ => α) c Fin.elim0))

-- Reference: [Conway], 2nd ed. 2001, Chapter 0 (a node with three left
-- options, here the depth-2 worked examples of Games/Misere.lean).
-- REVIEW(citation): same citation state as Games/Misere.lean.
/-- The left option family of the referee's 3×3 node: `0 ↦ leftMove`,
`1 ↦ rightMove`, `2 ↦ bothMoves`. -/
def mixedLeft : Fin 3 → TGame 2 := familyOfThree leftMove rightMove bothMoves

-- Reference: as `mixedLeft` (three right options).
/-- The right option family of the referee's 3×3 node: `0 ↦ bothMoves`,
`1 ↦ leftMove`, `2 ↦ rightMove`. -/
def mixedRight : Fin 3 → TGame 2 := familyOfThree bothMoves leftMove rightMove

-- Reference: [Conway], 2nd ed. 2001, Chapter 0 (three left and three right
-- options).
-- REVIEW(citation): same citation state as Games/Misere.lean.
/-- The referee's worked 3×3 node: a depth-3 game whose three left and three
right options are depth-2 worked examples of Games/Misere.lean. -/
def mixed3 : TGame 3 := TGame.node 2 3 3 mixedLeft mixedRight

-- Reference: [Conway], 2nd ed. 2001 / [BCG], vol. 1, ch. 13, misère play;
-- `leftMove_outcome`, `rightMove_outcome`, `bothMoves_outcome` of Misere.lean.
-- REVIEW(citation): same citation state as Games/Misere.lean.
/-- The 3×3 node wins for the player to move: all six options are misère losses
for their mover, so some option loses for the next player. -/
theorem mixed3_outcome : misereOutcome 3 mixed3 = true := rfl

-- Reference: standard (unfolding `TGame.act` and `reindexSide_three` at
-- `mixed3`).
/-- Primitive definitional lemma: the action on `mixed3` permutes both option
families by `σ`. -/
theorem act_mixed3 (σ : Fin 3 → Fin 3) :
    TGame.act σ 3 mixed3 =
      TGame.node 2 3 3 (fun i => mixedLeft (σ i)) (fun j => mixedRight (σ j)) :=
  rfl

-- Reference: [Conway], 2nd ed. 2001 / [BCG], vol. 1, ch. 13, misère play.
-- Enumerated equivariance case `σ = permId` on `mixed3`.
-- REVIEW(citation): same citation state as Games/Misere.lean.
/-- Equivariance shadow (enumerated, `σ = permId`): outcome invariance of
`mixed3` by computation — every permuted option is still a misère loss. -/
theorem misereOutcome_act_mixed3_permId :
    misereOutcome 3 (TGame.act permId 3 mixed3) = misereOutcome 3 mixed3 := rfl

-- Reference: [Conway], 2nd ed. 2001 / [BCG], vol. 1, ch. 13, misère play.
-- Enumerated equivariance case `σ = permSwap01` on `mixed3`.
-- REVIEW(citation): same citation state as Games/Misere.lean.
/-- Equivariance shadow (enumerated, `σ = permSwap01`): outcome invariance of
`mixed3` by computation — every permuted option is still a misère loss. -/
theorem misereOutcome_act_mixed3_permSwap01 :
    misereOutcome 3 (TGame.act permSwap01 3 mixed3) = misereOutcome 3 mixed3 := rfl

-- Reference: [Conway], 2nd ed. 2001 / [BCG], vol. 1, ch. 13, misère play.
-- Enumerated equivariance case `σ = permSwap12` on `mixed3`.
-- REVIEW(citation): same citation state as Games/Misere.lean.
/-- Equivariance shadow (enumerated, `σ = permSwap12`): outcome invariance of
`mixed3` by computation — every permuted option is still a misère loss. -/
theorem misereOutcome_act_mixed3_permSwap12 :
    misereOutcome 3 (TGame.act permSwap12 3 mixed3) = misereOutcome 3 mixed3 := rfl

-- Reference: [Conway], 2nd ed. 2001 / [BCG], vol. 1, ch. 13, misère play.
-- Enumerated equivariance case `σ = permSwap02` on `mixed3`.
-- REVIEW(citation): same citation state as Games/Misere.lean.
/-- Equivariance shadow (enumerated, `σ = permSwap02`): outcome invariance of
`mixed3` by computation — every permuted option is still a misère loss. -/
theorem misereOutcome_act_mixed3_permSwap02 :
    misereOutcome 3 (TGame.act permSwap02 3 mixed3) = misereOutcome 3 mixed3 := rfl

-- Reference: [Conway], 2nd ed. 2001 / [BCG], vol. 1, ch. 13, misère play.
-- Enumerated equivariance case `σ = permCycle012` on `mixed3`.
-- REVIEW(citation): same citation state as Games/Misere.lean.
/-- Equivariance shadow (enumerated, `σ = permCycle012`): outcome invariance of
`mixed3` by computation — every permuted option is still a misère loss. -/
theorem misereOutcome_act_mixed3_permCycle012 :
    misereOutcome 3 (TGame.act permCycle012 3 mixed3) = misereOutcome 3 mixed3 := rfl

-- Reference: [Conway], 2nd ed. 2001 / [BCG], vol. 1, ch. 13, misère play.
-- Enumerated equivariance case `σ = permCycle021` on `mixed3`.
-- REVIEW(citation): same citation state as Games/Misere.lean.
/-- Equivariance shadow (enumerated, `σ = permCycle021`): outcome invariance of
`mixed3` by computation — every permuted option is still a misère loss. -/
theorem misereOutcome_act_mixed3_permCycle021 :
    misereOutcome 3 (TGame.act permCycle021 3 mixed3) = misereOutcome 3 mixed3 := rfl

-- Reference: [Dummit–Foote], Ch. 1, §1.3 (the identity element acts as the
-- identity); primitive eta/definitional computation.
/-- D.5, identity action on the 3×3 node: `permId` fixes `mixed3`. -/
theorem act_identity_mixed3 : TGame.act permId 3 mixed3 = mixed3 := rfl

-- Reference: [Dummit–Foote], Ch. 1, §1.3; fixed point `act_fixed_leaf1`.
/-- D.5, identity action on the family: `permId` fixes `leaf1`. -/
theorem act_identity_leaf1 : TGame.act permId 1 leaf1 = leaf1 :=
  act_fixed_leaf1 permId

-- Reference: standard (Boolean outcome pairing over the S₃ table).
/-- The outcome-comparison table for `g` at depth `n`: for each `σ` in `s3Table`,
the pair `[misereOutcome n (act σ g), misereOutcome n g]`. -/
def outcomePairs (n : ℕ) (g : TGame n) : List (List Bool) :=
  s3Table.map (fun σ => [misereOutcome n (TGame.act σ n g), misereOutcome n g])

#eval s3Table.map (fun σ => [σ 0, σ 1, σ 2].map (fun i => i.val))
#eval outcomePairs 1 leaf1
#eval outcomePairs 2 leftMove
#eval outcomePairs 2 rightMove
#eval outcomePairs 2 bothMoves
#eval outcomePairs 3 leftToLoss
#eval outcomePairs 1 (chain 0)
#eval outcomePairs 2 (chain 1)
#eval outcomePairs 3 (chain 2)
#eval outcomePairs 4 (chain 3)
#eval outcomePairs 3 mixed3
#eval s3Table.map (fun σ => misereOutcome 3 (TGame.act σ 3 mixed3))
#eval misereOutcome 3 mixed3

end BoringLab
