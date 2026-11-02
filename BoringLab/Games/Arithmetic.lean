/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import BoringLab.Games.Misere
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Init

/-!
# Game arithmetic on the truncated carrier: negation and disjunctive sum

Lab ticket #84 (L.5.3), general case: the definitions are total on `TGame n`
for EVERY `n`, and the laws are proved for all games by induction on the
depth — not enumerated on toy families.

* `TGame.neg` — negation (swap the option families), with the involution law
  `TGame.neg_neg` proved for all `n` and `g`;
* `TGame.add` — the disjunctive sum at depth `n + m`, with its node equation
  `TGame.add_node`;
* `TGame.lift` — reading a depth-`n` game at a larger depth (for the unit law);
* `TGame.zero`, `TGame.one` — the truncated zero and one;
* the sum laws (`TGame.add_comm`, `TGame.add_assoc`, `TGame.zero_add`) stated
  at full generality; the reindexing-heavy proofs carry peeling plans.

## References
* [Conway] J. H. Conway, *On Numbers and Games*, 2nd ed., A K Peters, 2000,
  ch. 0 (negation `-G`; the disjunctive sum `G + H`).
* [BCG] E. R. Berlekamp, J. H. Conway, R. K. Guy, *Winning Ways for Your
  Mathematical Plays*, vol. 1, 2nd ed., A K Peters, 2001, ch. 1.
* Program register: ticket #84 (L.5.3); builds on #20 (L.1.1, `TGame`).
-/

namespace BoringLab

-- Reference: [Conway], ch. 0 (negation `-G` swaps the two option families).
-- REVIEW(citation): pin the chapter in review.
/-- Negation of a depth-truncated game: swap the left and right option
families at every node, recursively. Total on `TGame n` for every `n`. -/
def TGame.neg : (n : ℕ) → TGame n → TGame n
  | 0, g => nomatch g
  | k + 1, TGame.node _ l r moveLeft moveRight =>
    TGame.node k r l (fun j => TGame.neg k (moveRight j))
      (fun i => TGame.neg k (moveLeft i))

-- Reference: computation step of `TGame.neg` on a node; `rfl` only in this
-- primitive definitional lemma.
/-- Primitive definitional lemma: the node equation of `TGame.neg`. -/
theorem TGame.neg_node {n l r : ℕ} (moveLeft : Fin l → TGame n)
    (moveRight : Fin r → TGame n) :
    TGame.neg (n + 1) (TGame.node n l r moveLeft moveRight) =
      TGame.node n r l (fun j => TGame.neg n (moveRight j))
        (fun i => TGame.neg n (moveLeft i)) := rfl

-- Reference: [Conway], ch. 0 (`-(-G) = G`); proved for ALL depths by
-- induction on `n`, with `funext` on the option families (the
-- `RegimeMap.ext` pattern of #64).
/-- **The involution law**: `neg (neg g) = g`, for every depth `n` and every
truncated game `g` (general, proved by induction on the depth). -/
theorem TGame.neg_neg : ∀ (n : ℕ) (g : TGame n), TGame.neg n (TGame.neg n g) = g := by
  intro n
  induction n with
  | zero => intro g; nomatch g
  | succ k ih =>
    intro g
    cases g with
    | node _ l r f g' =>
      change TGame.node k l r (fun i => TGame.neg k (TGame.neg k (f i)))
            (fun j => TGame.neg k (TGame.neg k (g' j))) = TGame.node k l r f g'
      have h1 : (fun i => TGame.neg k (TGame.neg k (f i))) = f :=
        funext fun i => ih (f i)
      have h2 : (fun j => TGame.neg k (TGame.neg k (g' j))) = g' :=
        funext fun j => ih (g' j)
      exact Eq.trans
        (congrArg (fun F : Fin l → TGame k =>
          TGame.node k l r F (fun j => TGame.neg k (TGame.neg k (g' j)))) h1)
        (congrArg (fun G : Fin r → TGame k => TGame.node k l r f G) h2)

-- Reference: [Conway], ch. 0 (`0 = {|}`).
-- REVIEW(citation): pin the chapter in review.
/-- The truncated zero game: the depth-1 leaf. -/
def TGame.zero : TGame 1 := TGame.node 0 0 0 Fin.elim0 Fin.elim0

-- Reference: [Conway], ch. 0 (`1 = {0|}`).
-- REVIEW(citation): pin the chapter in review.
/-- The truncated one game: the unique left option is the zero game. -/
def TGame.one : TGame 2 := TGame.node 1 1 0 (fun _ => TGame.zero) Fin.elim0

-- Reference: [Conway], ch. 0 / [BCG] vol. 1 ch. 1 (the disjunctive sum: a move
-- in `G + H` is a move in exactly one component). The `cast`s transport along
-- the `Nat` depth arithmetic (`Nat.succ_add`), since `Nat.add` recurses on its
-- second argument and `(k+1) + l` is not DEFEQ to `k + l + 1`.
-- REVIEW(citation): pin the sum chapter in review.
/-- The disjunctive sum of truncated games: `add n g m h : TGame (n + m)`; at
a pair of nodes the left options are `G^L + H` and `G + H^L`, indexed by
`Fin (a + c)` via `Fin.addCases`. Well-founded recursion on `n + m`. -/
def TGame.add : (n : ℕ) → TGame n → (m : ℕ) → TGame m → TGame (n + m)
  | 0, g, _, _ => nomatch g
  | _k + 1, TGame.node _ _ _ _ _, 0, h => nomatch h
  | k + 1, TGame.node _ a b f g', l + 1, TGame.node _ c d f' g'' =>
    cast (congrArg TGame (Nat.succ_add k (l + 1))).symm
      (TGame.node (k + l + 1) (a + c) (b + d)
        (Fin.addCases (motive := fun _ => TGame (k + l + 1))
          (fun i => TGame.add k (f i) (l + 1) (TGame.node l c d f' g''))
          (fun j => cast (congrArg TGame (Nat.succ_add k l))
            (TGame.add (k + 1) (TGame.node k a b f g') l (f' j))))
        (Fin.addCases (motive := fun _ => TGame (k + l + 1))
          (fun i => TGame.add k (g' i) (l + 1) (TGame.node l c d f' g''))
          (fun j => cast (congrArg TGame (Nat.succ_add k l))
            (TGame.add (k + 1) (TGame.node k a b f g') l (g'' j)))))
termination_by n _ m _ => n + m

-- Reference: computation step of `TGame.add` on a pair of nodes, via the
-- generated equation lemma of the well-founded recursion.
/-- Primitive definitional lemma: the node equation of `TGame.add`. -/
theorem TGame.add_node {k l a b c d : ℕ} (f : Fin a → TGame k) (g : Fin b → TGame k)
    (f' : Fin c → TGame l) (g' : Fin d → TGame l) :
    TGame.add (k + 1) (TGame.node k a b f g) (l + 1) (TGame.node l c d f' g') =
      cast (congrArg TGame (Nat.succ_add k (l + 1))).symm
        (TGame.node (k + l + 1) (a + c) (b + d)
          (Fin.addCases (motive := fun _ => TGame (k + l + 1))
            (fun i => TGame.add k (f i) (l + 1) (TGame.node l c d f' g'))
            (fun j => cast (congrArg TGame (Nat.succ_add k l))
              (TGame.add (k + 1) (TGame.node k a b f g) l (f' j))))
          (Fin.addCases (motive := fun _ => TGame (k + l + 1))
            (fun i => TGame.add k (g i) (l + 1) (TGame.node l c d f' g'))
            (fun j => cast (congrArg TGame (Nat.succ_add k l))
              (TGame.add (k + 1) (TGame.node k a b f g) l (g' j))))) :=
  TGame.add.eq_def _ _ _ _

-- Reference: [Conway], ch. 0 (a game of depth `n` read at depth `m ≥ n` is the
-- same game; the truncation carriers are nested).
/-- Lifting a truncated game to a larger depth: the options are lifted
recursively. Structural recursion on the target depth `m`. -/
def TGame.lift : (n m : ℕ) → TGame n → n ≤ m → TGame m
  | 0, _, g, _ => nomatch g
  | k + 1, 0, _, h => (Nat.not_succ_le_zero k h).elim
  | k + 1, l + 1, TGame.node _ a b f g', h =>
    TGame.node l a b
      (fun i => TGame.lift k l (f i) (Nat.le_of_succ_le_succ h))
      (fun j => TGame.lift k l (g' j) (Nat.le_of_succ_le_succ h))

-- Reference: computation step of `TGame.lift` on a node; `rfl` only in this
-- primitive definitional lemma.
/-- Primitive definitional lemma: the node equation of `TGame.lift`. -/
theorem TGame.lift_node {k l a b : ℕ} (f : Fin a → TGame k) (g : Fin b → TGame k)
    (h : k + 1 ≤ l + 1) :
    TGame.lift (k + 1) (l + 1) (TGame.node k a b f g) h =
      TGame.node l a b (fun i => TGame.lift k l (f i) (Nat.le_of_succ_le_succ h))
        (fun j => TGame.lift k l (g j) (Nat.le_of_succ_le_succ h)) := rfl

-- Reference: [Conway], ch. 0 (the sum is commutative: `G + H = H + G`); the
-- `cast` transports along `Nat.add_comm` since the sum's depth is `n + m`.
-- REVIEW(citation): pin the chapter in review.
/-- **Commutativity of the disjunctive sum**, for all depths and all games. -/
theorem TGame.add_comm (n m : ℕ) (g : TGame n) (h : TGame m) :
    TGame.add n g m h =
      cast (congrArg TGame (Nat.add_comm n m)).symm (TGame.add m h n g) := by
  -- TEMPORARY SORRY: the honest proof is well-founded induction on `n + m`
  -- reducing via `TGame.add_node` to a node equality whose option families
  -- agree after the `finSumFinEquiv` reindexing `Fin (a + c) ≃ Fin (c + a)`
  -- and the induction hypothesis; node equality closes by `funext` +
  -- `Eq.trans` as in `TGame.neg_neg`.
  -- PEELING PLAN: (1) `fin_addCases_comm`: the reindexed `Fin.addCases`
  --   equals the swapped one (via `finSumFinEquiv` of Mathlib.Logic.Equiv.Fin);
  -- (2) the WF induction on `n + m` consuming `TGame.add_node`.
  sorry

-- Reference: [Conway], ch. 0 (the sum is associative); the `cast` transports
-- along `Nat.add_assoc`.
-- REVIEW(citation): pin the chapter in review.
/-- **Associativity of the disjunctive sum**, for all depths and all games. -/
theorem TGame.add_assoc (n m p : ℕ) (g : TGame n) (h : TGame m) (q : TGame p) :
    TGame.add (n + m) (TGame.add n g m h) p q =
      cast (congrArg TGame (Nat.add_assoc n m p)).symm
        (TGame.add n g (m + p) (TGame.add m h p q)) := by
  -- TEMPORARY SORRY: WF induction on `n + m + p` via `TGame.add_node`, then
  -- reassociation of the `Fin ((a + c) + e)` indexing and `Nat.add_assoc`.
  -- PEELING PLAN: (1) `fin_addCases_assoc` (the `finSumFinEquiv`
  --   associativity reindexing); (2) the depth bookkeeping via `Eq.subst`;
  -- (3) the WF induction consuming `TGame.add_node`.
  sorry

-- Reference: [Conway], ch. 0 (`0 + G = G`).
-- REVIEW(citation): pin the chapter in review.
/-- **The unit law**: `zero + g` is `g` read at depth `1 + n`. -/
theorem TGame.zero_add (n : ℕ) (g : TGame n) :
    TGame.add 1 TGame.zero n g = TGame.lift n (1 + n) g (Nat.le_add_left n 1) := by
  -- TEMPORARY SORRY: induction on `n` via `TGame.add_node` (the `zero` side
  -- has `a = b = 0`, so the sum's option families are exactly `g`'s options,
  -- lifted); the depth equality `1 + n = n + 1` rides `Nat.add_comm`.
  -- PEELING PLAN: (1) `TGame.lift` computation lemmas; (2) the node equation
  -- on both sides and `funext` on the families.
  sorry


-- Reference: standard (coverage of `Fin (l + r)` by `Fin.castAdd`/`Fin.natAdd`,
-- via `Fin.addCases` as eliminator — peeling step for `TGame.add_comm` and
-- `TGame.add_neg`).
/-- **`Fin.addCases` is a coverage**: to prove `P i` for all `i : Fin (l + r)`,
it suffices to prove it on the `Fin.castAdd r` and `Fin.natAdd l` parts. -/
theorem fin_addCases_forall {l r : ℕ} {P : Fin (l + r) → Prop}
    (hL : ∀ i : Fin l, P (Fin.castAdd r i)) (hR : ∀ j : Fin r, P (Fin.natAdd l j)) :
    ∀ i : Fin (l + r), P i :=
  fun i => Fin.addCases hL hR i

end BoringLab
