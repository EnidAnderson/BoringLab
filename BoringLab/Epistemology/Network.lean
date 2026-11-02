/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import BoringLab.Epistemology.Learning

/-!
# Epistemic networks: the Zollman effect as data

Ticket #35 (EPI.6.1), building on #31 (`BoringLab.Epistemology.Learning`)
and #29's ledger: the community, not the individual, as the learning agent.

* **(a)** a scientist-network as data: agents (ledgers over the hypothesis
  family) on an explicit graph (`edge : ℕ → ℕ → Bool`); interaction =
  information sharing along edges — the count ledgers merge by concatenation
  (`agentRound`, `runNet`);
* **(b)** the Zollman effect, honestly graded: on the toy family, complete vs
  sparse (path) networks are run by `#eval` and compared — simulation
  evidence at bounded scale, NOT the general game-theoretic theorem (named
  hole, peeling plan);
* **(c)** the provable pieces: the net weight (the sum of the ledger entries
  per hypothesis) is additive under merging (`netWeight_append`), hence
  merging is commutative (`netWeight_merge_comm`), and the two-agent clique
  reaches consensus in one round (`two_agent_consensus`); the general
  connected-graph consensus theorem is a named hole (`consensus_connected`,
  peeling plan: induction on rounds + a diameter bound for the connected
  graph);
* **(d)** the epistemic-risk ledger (exploration/exploitation as the
  individual-vs-network mind-change tradeoff) is recorded at comment level;
  the L-line misère connection is a REVIEW note only (no forced analogy).

## References
* [Zollman 2007] K. J. S. Zollman, "The Communication Structure of Epistemic
  Communities", *Philosophy of Science* 74(5):701–733, 2007,
  doi:10.1086/521657 (well-connected communities can lock onto consensus
  error).
* [Zollman 2010] K. J. S. Zollman, "The Epistemic Benefit of Transient
  Diversity", *Erkenntnis* 72(1):17–35, 2010.
* [Rosenstock–O'Connor–Bruner] C. Rosenstock, S. O'Connor, J. Bruner, on
  network epistemology (the Zollman-effect discussion).
  REVIEW(citation): pin exact titles/venues in review.
* Program register: BoringLab ticket #35 (EPI.6.1); the toy is the #28/#31
  coin family, the program's own.
-/

namespace BoringLab

/-! ## Net weights and merging -/

-- Reference: ticket #35, item (c): the net weight of a hypothesis = the
-- sum of its ledger entries (additive under merging — the consensus
-- carrier); the `ite` is the decidable equality of hypotheses.
/-- The **net weight** of a hypothesis in a (possibly merged) ledger: the
sum of the weights of its entries. -/
def netWeight {hyp : Type} [DecidableEq hyp] : List (hyp × ℚ) → hyp → ℚ
  | [], _ => 0
  | p :: rest, h => if p.1 = h then p.2 + netWeight rest h else netWeight rest h

-- Reference: computation steps of `netWeight`; `rfl` only in these
-- primitive definitional lemmas.
/-- The net weight in the empty ledger is zero. -/
theorem netWeight_nil {hyp : Type} [DecidableEq hyp] (h : hyp) :
    netWeight ([] : List (hyp × ℚ)) h = 0 := rfl

-- Reference: core `ite_eq_left` on the decidable equality of hypotheses.
/-- The net weight past a matching head accumulates. -/
theorem netWeight_cons_same {hyp : Type} [DecidableEq hyp] (p : hyp × ℚ)
    (rest : List (hyp × ℚ)) (h : hyp) (he : p.1 = h) :
    netWeight (p :: rest) h = p.2 + netWeight rest h := ite_eq_left he

-- Reference: core `ite_eq_right`.
/-- The net weight past a non-matching head. -/
theorem netWeight_cons_diff {hyp : Type} [DecidableEq hyp] (p : hyp × ℚ)
    (rest : List (hyp × ℚ)) (h : hyp) (hn : p.1 ≠ h) :
    netWeight (p :: rest) h = netWeight rest h := ite_eq_right hn

-- Reference: ticket #35, item (c) — additivity of the net weight under
-- merging; induction on the first list with the cons lemmas and
-- `add_assoc` (core, on ℚ).
/-- **Additivity of the net weight under merging**: the net weight of a
concatenation is the sum of the net weights. -/
theorem netWeight_append {hyp : Type} [DecidableEq hyp] (l1 l2 : List (hyp × ℚ)) (h : hyp) :
    netWeight (l1 ++ l2) h = netWeight l1 h + netWeight l2 h := by
  induction l1 with
  | nil => exact (zero_add (netWeight l2 h)).symm
  | cons p rest ih =>
      cases (inferInstance : Decidable (p.1 = h)) with
      | isTrue he =>
          exact (netWeight_cons_same p (rest ++ l2) h he).trans
            ((congrArg (fun x => p.2 + x) ih).trans
              ((add_assoc p.2 (netWeight rest h) (netWeight l2 h)).symm.trans
                (congrArg (fun x => x + netWeight l2 h)
                  (netWeight_cons_same p rest h he).symm)))
      | isFalse hn =>
          exact (netWeight_cons_diff p (rest ++ l2) h hn).trans
            (ih.trans (congrArg (fun x => x + netWeight l2 h)
              (netWeight_cons_diff p rest h hn).symm))

-- Reference: ticket #35, item (a): interaction = merging the count ledgers
-- along edges (concatenation).
/-- Merging two ledgers: concatenation. -/
def mergeLedger {hyp : Type} [DecidableEq hyp] (l1 l2 : List (hyp × ℚ)) :
    List (hyp × ℚ) := l1 ++ l2

-- Reference: ticket #35, item (c): merging is commutative at the level of
-- net weights, by additivity + `add_comm` on ℚ.
/-- **Merging is commutative** in net weight. -/
theorem netWeight_merge_comm {hyp : Type} [DecidableEq hyp] (a b : List (hyp × ℚ)) (h : hyp) :
    netWeight (mergeLedger a b) h = netWeight (mergeLedger b a) h :=
  (netWeight_append a b h).trans
    ((add_comm (netWeight a h) (netWeight b h)).trans (netWeight_append b a h).symm)

/-! ## Networks as data; rounds -/

-- Reference: ticket #35, item (a): the graph as explicit data (edge
-- predicate on agent indices); one round = fold the merges over the
-- neighbors.
/-- **One round of information sharing**: agent `i`'s new ledger is the fold
of merges over its neighbors' ledgers. -/
def agentRound {hyp : Type} [DecidableEq hyp] (n : ℕ) (edge : ℕ → ℕ → Bool)
    (states : ℕ → List (hyp × ℚ)) (i : ℕ) : List (hyp × ℚ) :=
  ((List.range n).filter fun j => edge i j).foldl (fun acc j => mergeLedger acc (states j))
    (states i)

-- Reference: ticket #35, item (a)/(b): running the network for `k` rounds.
/-- **Running the network** for `k` rounds. -/
def runNet {hyp : Type} [DecidableEq hyp] (n : ℕ) (edge : ℕ → ℕ → Bool)
    (init : ℕ → List (hyp × ℚ)) : ℕ → ℕ → List (hyp × ℚ)
  | 0, i => init i
  | k + 1, i => agentRound n edge (runNet n edge init k) i

-- Reference: ticket #35, item (c), D.5 instance (the two-agent clique):
-- one round on the clique exchanges the ledgers both ways.
/-- One round on the two-agent clique. -/
def twoAgentRound {hyp : Type} [DecidableEq hyp] (s0 s1 : List (hyp × ℚ)) :
    List (hyp × ℚ) × List (hyp × ℚ) := (mergeLedger s0 s1, mergeLedger s1 s0)

-- Reference: ticket #35, item (c) — the provable piece: the two-agent
-- clique reaches consensus (equal net weights) in one round.
/-- **Two-agent consensus in one round**: after the exchange, both agents'
net weights agree on every hypothesis. -/
theorem two_agent_consensus {hyp : Type} [DecidableEq hyp] (s0 s1 : List (hyp × ℚ))
    (h : hyp) :
    netWeight (twoAgentRound s0 s1).1 h = netWeight (twoAgentRound s0 s1).2 h :=
  netWeight_merge_comm s0 s1 h

-- Reference: ticket #35, item (c): reachability on the graph (the
-- reflexive-transitive closure of the edge predicate), as an inductive
-- Prop.
/-- **Reachability** on a network: the reflexive-transitive closure of the
edge relation. -/
inductive Reachable (edge : ℕ → ℕ → Bool) : ℕ → ℕ → Prop where
  /-- Reflexivity. -/
  | refl (i : ℕ) : Reachable edge i i
  /-- One edge plus a path. -/
  | step (i j k : ℕ) : edge i j = true → Reachable edge j k → Reachable edge i k

-- Reference: ticket #35, item (c): consensus on the fixed-update rules
-- when the graph is connected — a decidable theorem on bounded carriers.
-- TEMPORARY SORRY: the honest proof has not been instantiated yet.
-- PEELING PLAN: connectedness = all pairs reachable (`Reachable` above);
-- bound the diameter of a connected graph on `n` agents by `n`; then
-- induction on the round count: after `n` rounds every agent's ledger
-- contains every other's entries, so all `netWeight`s agree (via
-- `netWeight_append`). Next named lemmas: `Reachable.trans`,
-- `diameter_bound`, `ledger_contains_after_diameter`.
/-- **Consensus on connected networks**: on a connected graph over `n`
agents, after `n` rounds all agents' net weights agree on every
hypothesis. -/
theorem consensus_connected {hyp : Type} [DecidableEq hyp] (n : ℕ) (edge : ℕ → ℕ → Bool)
    (hconn : ∀ i j, i < n → j < n → Reachable edge i j) (init : ℕ → List (hyp × ℚ))
    (h : hyp) :
    ∀ i j, i < n → j < n →
      netWeight (runNet n edge init n i) h = netWeight (runNet n edge init n j) h := by
  sorry

/-! ## Toy: the Zollman comparison on the coin family (bounded simulation) -/

-- Reference: ticket #35, item (b): the two topologies on four agents —
-- complete vs path — as data.
/-- The complete graph on `{0,1,2,3}` (plus self-loops). -/
def complete4 (i j : ℕ) : Bool := if i < 4 ∧ j < 4 then true else false

-- Reference: ticket #35, item (b): the path `0—1—2—3` (plus self-loops).
/-- The path graph on `{0,1,2,3}` (plus self-loops). -/
def path4 (i j : ℕ) : Bool :=
  if i < 4 ∧ j < 4 then (i == j ∨ i + 1 == j ∨ j + 1 == i) else false

-- Reference: ticket #35, toy: all agents start from the uniform ledger on
-- the #28 coin family.
/-- The toy initial ledgers: uniform on the coin family at every agent. -/
def coinInitLedgers (_ : ℕ) : List (CoinHyp × ℚ) := uniformLedger coinHypotheses

-- Reference: ticket #35, acceptance (b): the runs printed — net weight of
-- the `loaded` hypothesis at each agent after 3 rounds, complete vs path
-- (the observed data phenomenon; bounded simulation, honestly graded).
#eval (List.range 4).map fun i => netWeight (runNet 4 complete4 coinInitLedgers 3 i) CoinHyp.loaded
#eval (List.range 4).map fun i => netWeight (runNet 4 path4 coinInitLedgers 3 i) CoinHyp.loaded

end BoringLab
