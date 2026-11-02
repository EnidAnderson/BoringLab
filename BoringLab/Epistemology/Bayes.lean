/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import BoringLab.Epistemology.SampleComplexity

/-!
# The Bayesian mass process: conservation of total weight (martingale identity)

Ticket #167 (EPI.3.3 BAYESVALUE.0, EPI half), building on #29's count-table
update (`bayesUpdate`, `BoringLab.Epistemology.Process`) and #28's
`weightsSum`/`isDistribution`/`tableMass` (`BoringLab.Epistemology.FairExperiment`).

* `ledgerSum` — the total weight of a ledger (sum of second components);
* `ledgerSum_bayesUpdate` — PROVED one-step formula: the updated total is the
  sum of `weight × prediction mass` over the cells;
* `sum_tableMass_eq_weightsSum_of_nodup` — PROVED: over a nodup outcome list,
  the sum of `tableMass` equals the table's total weight (cells in the list);
* `bayesUpdate_conservation` — PROVED (the martingale/conservation identity,
  Doob shape): if every hypothesis's table is a distribution over a nodup
  outcome list covering all cells, then the expected updated total equals the
  current total;
* `ConservedMassProcess` — the shared abstraction (value/next/law) that the
  game value process of TR.0 (#10) is to instantiate — the parallels-register
  row; the games-side instance is a named hole (Trace.lean is unverified at
  this session — do-not-import note in workspace-notes);
* toy: `coinBayes` — the coin ledger's conservation, PROVED via the general
  theorem, with `#eval` printing both sides (= 3).

## References
* [Kolmogorov] ch. I, §1 (distributions; conditional mass) — via #28.
* Doob, *Stochastic Processes* (1953), ch. I (martingale expectation
  conservation) — REVIEW(citation): pin the martingale definition page at
  review.
* [Gold] E. M. Gold 1967 (the reliability ledger of #31); program register:
  BoringLab tickets #167 (EPI.3.3), #28, #29, #31, #10.
-/

namespace BoringLab

/-! ## Ledger totals -/

-- Reference: #28's `weightsSum` (map `Prod.fst` on tables); the ledger cells
-- are `(hyp × ℚ)`, so the total weight maps `Prod.snd`.
/-- The **total weight** of a ledger: the sum of the second components. -/
def ledgerSum {hyp : Type} (l : List (hyp × ℚ)) : ℚ := (l.map Prod.snd).sum

-- Reference: computation step of `ledgerSum`; core `List.map_cons`,
-- `List.sum_cons` (`rfl` only in this primitive definitional lemma).
/-- The total weight of a cons cell adds the cell's weight. -/
theorem ledgerSum_cons {hyp : Type} (p : hyp × ℚ) (l : List (hyp × ℚ)) :
    ledgerSum (p :: l) = p.2 + ledgerSum l := by
  unfold ledgerSum
  exact Eq.subst (motive := fun (m : List ℚ) => m.sum = p.2 + (l.map Prod.snd).sum)
    (List.map_cons (f := Prod.snd) (a := p) (l := l)).symm
    (List.sum_cons (a := Prod.snd p) (l := l.map Prod.snd))

-- Reference: computation step; core `List.map_nil`, `List.sum_nil`.
/-- The empty ledger has total weight `0`. -/
theorem ledgerSum_nil {hyp : Type} : ledgerSum ([] : List (hyp × ℚ)) = 0 :=
  (congrArg List.sum (List.map_nil (f := Prod.snd))).trans List.sum_nil

-- Reference: as `ledgerSum_cons`, with `Prod.fst` on tables (#28's
-- `weightsSum`).
/-- The total weight of a table's cons cell adds the cell's weight. -/
theorem weightsSum_cons {outcome : Type} (p : ℚ × outcome) (t : List (ℚ × outcome)) :
    weightsSum (p :: t) = p.1 + weightsSum t := by
  unfold weightsSum
  exact Eq.subst (motive := fun (m : List ℚ) => m.sum = p.1 + (t.map Prod.fst).sum)
    (List.map_cons (f := Prod.fst) (a := p) (l := t)).symm
    (List.sum_cons (a := Prod.fst p) (l := t.map Prod.fst))

/-! ## The one-step update formula -/

-- Reference: ticket #167 — PROVED by induction on the ledger, with
-- `bayesUpdate_cons` (#29), `ledgerSum_cons`, `List.map_cons`,
-- `List.sum_cons`.
/-- **One-step update formula**: the updated total weight is the sum of
`weight × prediction mass of o` over the cells. -/
theorem ledgerSum_bayesUpdate {hyp outcome : Type} [DecidableEq outcome]
    (predict : hyp → List (ℚ × outcome)) (o : outcome) (l : List (hyp × ℚ)) :
    ledgerSum (bayesUpdate predict o l)
      = (l.map fun p => p.2 * tableMass (predict p.1) o).sum := by
  induction l with
  | nil => exact rfl
  | cons p rest ih =>
      have h1 := bayesUpdate_cons predict o p rest
      have e1 : ledgerSum (bayesUpdate predict o (p :: rest))
          = p.2 * tableMass (predict p.1) o + ledgerSum (bayesUpdate predict o rest) :=
        Eq.subst (motive := fun l => ledgerSum l
            = p.2 * tableMass (predict p.1) o + ledgerSum (bayesUpdate predict o rest))
          h1 (ledgerSum_cons (p.1, p.2 * tableMass (predict p.1) o) (bayesUpdate predict o rest))
      have e2 : ((p :: rest).map fun q => q.2 * tableMass (predict q.1) o).sum
          = p.2 * tableMass (predict p.1) o
            + (rest.map fun q => q.2 * tableMass (predict q.1) o).sum :=
        Eq.subst (motive := fun (m : List ℚ) => m.sum = p.2 * tableMass (predict p.1) o
            + (rest.map fun q => q.2 * tableMass (predict q.1) o).sum)
          (List.map_cons (f := fun q => q.2 * tableMass (predict q.1) o) (a := p) (l := rest)).symm
          (List.sum_cons (a := (p.2 * tableMass (predict p.1) o))
            (l := rest.map fun q => q.2 * tableMass (predict q.1) o))
      exact e1.trans ((congrArg (fun t => p.2 * tableMass (predict p.1) o + t) ih).trans e2.symm)

/-! ## List-sum helpers -/

-- Reference: core induction with `List.map_cons`, `List.sum_cons`, `zero_add`.
/-- A sum of zeros is zero. -/
theorem sum_map_zero {α : Type} (os : List α) : (os.map fun _ => (0:ℚ)).sum = 0 := by
  induction os with
  | nil => exact List.sum_nil
  | cons o os ih =>
      exact Eq.subst (motive := fun (m : List ℚ) => m.sum = 0)
        (List.map_cons (f := fun _ => (0:ℚ)) (a := o) (l := os))
        ((List.sum_cons (a := (0:ℚ)) (l := os.map fun _ => (0:ℚ))).trans
          ((zero_add (os.map fun _ => (0:ℚ)).sum).trans ih))

-- Reference: core induction with `List.map_cons`, `List.sum_cons`, `mul_add`.
/-- Pulling a constant multiplier out of a list sum. -/
theorem sum_map_mul_left {α : Type} (c : ℚ) (l : List α) (f : α → ℚ) :
    (l.map fun a => c * f a).sum = c * (l.map f).sum := by
  induction l with
  | nil =>
      exact (congrArg List.sum (List.map_nil (f := fun a => c * f a))).trans
        (List.sum_nil.trans (mul_zero c).symm)
  | cons a l ih =>
      calc ((a :: l).map fun x => c * f x).sum
          = (c * f a) + (l.map fun x => c * f x).sum :=
             Eq.subst (motive := fun (m : List ℚ) => m.sum = c * f a
                + (l.map fun x => c * f x).sum)
              (List.map_cons (f := fun x => c * f x) (a := a) (l := l))
              (List.sum_cons (a := c * f a) (l := l.map fun x => c * f x))
        _ = c * f a + c * (l.map f).sum := congrArg (fun t => c * f a + t) ih
        _ = c * (f a + (l.map f).sum) := (mul_add c (f a) ((l.map f).sum)).symm

-- Reference: core induction on `os` with `List.map_cons`, `List.sum_cons`,
-- `List.sum_map_add`, `add_comm`.
/-- Swapping a double list sum. -/
theorem sum_sum_swap {α β : Type} (l : List α) (os : List β) (f : α → β → ℚ) :
    (os.map fun o => (l.map fun p => f p o).sum).sum
      = (l.map fun p => (os.map fun o => f p o).sum).sum := by
  induction os with
  | nil =>
      exact (congrArg List.sum (List.map_nil (f := fun o => (l.map fun p => f p o).sum))).trans
        (List.sum_nil.trans (sum_map_zero l).symm)
  | cons o os ih =>
      calc ((o :: os).map fun o' => (l.map fun p => f p o').sum).sum
          = (l.map fun p => f p o).sum + (os.map fun o' => (l.map fun p => f p o').sum).sum :=
            Eq.subst (motive := fun (m : List ℚ) => m.sum = (l.map fun p => f p o).sum
                + (os.map fun o' => (l.map fun p => f p o').sum).sum)
              (List.map_cons (f := fun o' => (l.map fun p => f p o').sum) (a := o) (l := os))
              (List.sum_cons (a := (l.map fun p => f p o).sum)
                (l := os.map fun o' => (l.map fun p => f p o').sum))
        _ = (l.map fun p => f p o).sum + (l.map fun p => (os.map fun o' => f p o').sum).sum :=
            congrArg (fun t => (l.map fun p => f p o).sum + t) ih
        _ = (l.map fun p => (f p o + (os.map fun o' => f p o').sum)).sum :=
            (List.sum_map_add (l := l) (f := fun p => f p o)
            (g := fun p => (os.map fun o' => f p o').sum)).symm
        _ = (l.map fun p => ((o :: os).map fun o' => f p o').sum).sum :=
            congrArg List.sum (List.map_congr_left (fun p _ =>
              Eq.subst (motive := fun (m : List ℚ) => m.sum = f p o
                + (os.map fun o' => f p o').sum)
                (List.map_cons (f := fun o' => f p o') (a := o) (l := os))
                (List.sum_cons (a := f p o) (l := os.map fun o' => f p o'))))

/-! ## The sum of table masses over a nodup outcome list -/

-- Reference: #28's `tableMass_cons_same`/`tableMass_cons_diff` + `add_comm`/
-- `add_zero` + `ite_eq_left`/`ite_eq_right`: pointwise decomposition.
/-- Pointwise: adding a cell adds its weight at its own outcome only. -/
theorem tableMass_cons_eq_add {outcome : Type} [DecidableEq outcome]
    (p : ℚ × outcome) (rest : List (ℚ × outcome)) (o : outcome) :
    tableMass (p :: rest) o = tableMass rest o + (if p.2 = o then p.1 else 0) := by
  have hd : Decidable (p.2 = o) := inferInstance
  cases hd with
  | isTrue h =>
      exact (tableMass_cons_same p rest o h).trans
        ((add_comm (p.1) (tableMass rest o)).trans
          (congrArg (fun x => tableMass rest o + x) (ite_eq_left h)).symm)
  | isFalse h =>
      exact (tableMass_cons_diff p rest o h).trans
        ((add_zero (tableMass rest o)).symm.trans
          (congrArg (fun x => tableMass rest o + x) (ite_eq_right h)).symm)

-- Reference: core induction on `os` with `List.map_cons`, `List.sum_cons`,
-- `List.mem_cons`, `List.nodup_cons`, `add_zero`, `ite_eq_left`/`ite_eq_right`.
/-- Over a nodup list, the sum of `if c = o then a else 0` is `a` iff `c` is
in the list, else `0`. -/
theorem sum_map_ite_mem_of_nodup {α : Type} [DecidableEq α] (os : List α)
    (hnodup : os.Nodup) (c : α) (a : ℚ) :
    (os.map fun o => if c = o then a else 0).sum = if c ∈ os then a else 0 := by
  induction os with
  | nil =>
      exact (congrArg List.sum (List.map_nil (f := fun o => if c = o then a else 0))).trans
        (List.sum_nil.trans (ite_eq_right List.not_mem_nil).symm)
  | cons o os ih =>
      rcases List.nodup_cons.mp hnodup with ⟨ho, hos⟩
      have ih' := ih hos
      have hd : Decidable (c = o) := inferInstance
      cases hd with
      | isTrue h =>
          have hno : ¬ (c ∈ os) := fun hm => ho (Eq.subst (motive := fun x => x ∈ os) h hm)
          calc ((o :: os).map fun o' => if c = o' then a else 0).sum
              = (if c = o then a else 0) + (os.map fun o' => if c = o' then a else 0).sum :=
                Eq.subst (motive := fun (m : List ℚ) => m.sum = (if c = o then a else 0)
                    + (os.map fun o' => if c = o' then a else 0).sum)
                  (List.map_cons (f := fun o' => if c = o' then a else 0) (a := o) (l := os))
                  (List.sum_cons (a := if c = o then a else 0)
                    (l := os.map fun o' => if c = o' then a else 0))
            _ = a + 0 := by
                exact (congrArg (fun t => t + (os.map fun o' => if c = o' then a else 0).sum)
                  (ite_eq_left h)).trans (congrArg (fun t => a + t) (ih'.trans (ite_eq_right hno)))
            _ = a := add_zero a
            _ = if c ∈ o :: os then a else 0 :=
                (ite_eq_left (List.mem_cons.mpr (Or.inl h))).symm
      | isFalse h =>
          have hmem_iff : (c ∈ o :: os) ↔ c ∈ os := by
            refine Iff.intro (fun hm => ?_) (fun hm => List.mem_cons.mpr (Or.inr hm))
            rcases List.mem_cons.mp hm with he | hm'
            · exact absurd he h
            · exact hm'
          have hdit : Decidable (c ∈ os) := inferInstance
          cases hdit with
          | isTrue hm =>
              calc ((o :: os).map fun o' => if c = o' then a else 0).sum
                  = (if c = o then a else 0) + (os.map fun o' => if c = o' then a else 0).sum :=
                    Eq.subst (motive := fun (m : List ℚ) => m.sum = (if c = o then a else 0)
                        + (os.map fun o' => if c = o' then a else 0).sum)
                      (List.map_cons (f := fun o' => if c = o' then a else 0) (a := o) (l := os))
                      (List.sum_cons (a := if c = o then a else 0)
                        (l := os.map fun o' => if c = o' then a else 0))
                _ = 0 + a := by
                    exact (congrArg (fun t => t + (os.map fun o' => if c = o' then a else 0).sum)
                      (ite_eq_right h)).trans (congrArg (fun t => (0:ℚ) + t)
                        (ih'.trans (ite_eq_left hm)))
                _ = a := zero_add a
                _ = if c ∈ o :: os then a else 0 :=
                    (ite_eq_left (hmem_iff.mpr hm)).symm
          | isFalse hm =>
              calc ((o :: os).map fun o' => if c = o' then a else 0).sum
                  = (if c = o then a else 0) + (os.map fun o' => if c = o' then a else 0).sum :=
                    Eq.subst (motive := fun (m : List ℚ) => m.sum = (if c = o then a else 0)
                        + (os.map fun o' => if c = o' then a else 0).sum)
                      (List.map_cons (f := fun o' => if c = o' then a else 0) (a := o) (l := os))
                      (List.sum_cons (a := if c = o then a else 0)
                        (l := os.map fun o' => if c = o' then a else 0))
                _ = 0 + 0 := by
                    exact (congrArg (fun t => t + (os.map fun o' => if c = o' then a else 0).sum)
                      (ite_eq_right h)).trans (congrArg (fun t => (0:ℚ) + t)
                        (ih'.trans (ite_eq_right hm)))
                _ = 0 := zero_add 0
                _ = if c ∈ o :: os then a else 0 :=
                    (ite_eq_right (fun h' => hm (hmem_iff.mp h'))).symm

-- Reference: `tableMass_cons_eq_add` (pointwise) + `List.sum_map_add` +
-- `sum_map_ite_mem_of_nodup`.
/-- Adding a cell to the table adds its weight exactly once over a nodup
outcome list. -/
theorem sum_map_tableMass_cons {outcome : Type} [DecidableEq outcome]
    (os : List outcome) (hnodup : os.Nodup) (p : ℚ × outcome)
    (rest : List (ℚ × outcome)) :
    (os.map (tableMass (p :: rest))).sum
      = (os.map (tableMass rest)).sum + (if p.2 ∈ os then p.1 else 0) := by
  have hpoint : (os.map (tableMass (p :: rest)))
      = (os.map fun o => tableMass rest o + (if p.2 = o then p.1 else 0)) :=
    List.map_congr_left (fun o _ => tableMass_cons_eq_add p rest o)
  exact (congrArg List.sum hpoint).trans
    ((List.sum_map_add (l := os) (f := tableMass rest)
        (g := fun o => if p.2 = o then p.1 else 0)).trans
      (congrArg (fun x => (os.map (tableMass rest)).sum + x)
        (sum_map_ite_mem_of_nodup os hnodup p.2 p.1)))

-- Reference: induction on the table `t` with `sum_map_tableMass_cons`,
-- `sum_map_zero`, `weightsSum_cons`, `add_comm`.
/-- Over a nodup outcome list covering all cells, the sum of the table's
masses is its total weight. -/
theorem sum_tableMass_eq_weightsSum_of_nodup {outcome : Type} [DecidableEq outcome]
    (t : List (ℚ × outcome)) (os : List outcome) (hnodup : os.Nodup)
    (hcells : ∀ p ∈ t, p.2 ∈ os) :
    (os.map (tableMass t)).sum = weightsSum t := by
  induction t with
  | nil =>
      have e : (os.map (tableMass ([] : List (ℚ × outcome)))).sum
          = (os.map fun _ => (0:ℚ)).sum :=
        congrArg List.sum (List.map_congr_left (fun o _ => tableMass_nil o))
      have e2 : weightsSum ([] : List (ℚ × outcome)) = 0 :=
        (congrArg List.sum (List.map_nil (f := Prod.fst))).trans List.sum_nil
      exact e.trans ((sum_map_zero os).trans e2.symm)
  | cons p rest ih =>
      have h1 := sum_map_tableMass_cons os hnodup p rest
      have hc : (if p.2 ∈ os then p.1 else 0) = p.1 := ite_eq_left (hcells p List.mem_cons_self)
      have hrest : ∀ q ∈ rest, q.2 ∈ os := fun q hq => hcells q (List.mem_cons_of_mem _ hq)
      have hw : weightsSum (p :: rest) = p.1 + weightsSum rest := weightsSum_cons p rest
      exact h1.trans ((congrArg (fun x => (os.map (tableMass rest)).sum + x) hc).trans
        ((add_comm ((os.map (tableMass rest)).sum) p.1).trans
          ((congrArg (fun x => p.1 + x) (ih hrest)).trans hw.symm)))

/-! ## The conservation law (martingale identity) -/

-- Reference: ticket #167 — PROVED: `ledgerSum_bayesUpdate` + `sum_sum_swap`
-- + `sum_map_mul_left` + `sum_tableMass_eq_weightsSum_of_nodup` +
-- `isDistribution_eq_true` + `mul_one`. [Doob] 1953 ch. I: expectation
-- conservation for martingales.
/-- **Conservation of total weight under the Bayesian update** (martingale
identity, Doob shape): if every hypothesis's prediction table is a
distribution over a nodup outcome list covering all its cells, then the
outcome-expected updated total weight equals the current total weight. -/
theorem bayesUpdate_conservation {hyp outcome : Type} [DecidableEq outcome]
    (predict : hyp → List (ℚ × outcome)) (os : List outcome) (l : List (hyp × ℚ))
    (hnodup : os.Nodup)
    (hcells : ∀ p ∈ l, ∀ q ∈ predict p.1, q.2 ∈ os)
    (hdist : ∀ p ∈ l, isDistribution (predict p.1) = true) :
    (os.map fun o => ledgerSum (bayesUpdate predict o l)).sum = ledgerSum l := by
  have step1 : (os.map fun o => ledgerSum (bayesUpdate predict o l))
      = (os.map fun o => (l.map fun p => p.2 * tableMass (predict p.1) o).sum) :=
    List.map_congr_left (fun o _ => ledgerSum_bayesUpdate predict o l)
  have step2 : (os.map fun o => (l.map fun p => p.2 * tableMass (predict p.1) o).sum).sum
      = (l.map fun p => (os.map fun o => p.2 * tableMass (predict p.1) o).sum).sum :=
    sum_sum_swap l os (fun p o => p.2 * tableMass (predict p.1) o)
  have step3 : ∀ p ∈ l, (os.map fun o => p.2 * tableMass (predict p.1) o).sum
      = p.2 * weightsSum (predict p.1) := by
    intro p hp
    exact (sum_map_mul_left p.2 os (tableMass (predict p.1))).trans
      (congrArg (fun x => p.2 * x)
        (sum_tableMass_eq_weightsSum_of_nodup (predict p.1) os hnodup
          (fun q hq => hcells p hp q hq)))
  have step4 : ∀ p ∈ l, p.2 * weightsSum (predict p.1) = p.2 := by
    intro p hp
    exact (congrArg (fun x => p.2 * x)
      ((isDistribution_eq_true (predict p.1)).mp (hdist p hp))).trans (mul_one _)
  exact (congrArg List.sum step1).trans (step2.trans
    ((congrArg List.sum (List.map_congr_left step3)).trans
      ((congrArg List.sum (List.map_congr_left step4)).trans
        (congrArg List.sum (List.map_congr_left (fun p _ => (rfl : p.2 = Prod.snd p)))))))

/-! ## The shared abstraction: a conserved mass process -/

-- Reference: ticket #167 — the shared shape of the Bayesian ledger (below)
-- and the game value process (TR.0 #10, `Games/Trace.lean`). STYLE §2.3: all
-- data explicit; the law is a `Prop` field, never a global axiom.
/-- A **conserved mass process**: a ℚ-valued process over stages with a
successor list per stage, whose one-step successor sum is conserved. -/
structure ConservedMassProcess (ι : Type) where
  value : ι → ℚ
  next : ι → List ι
  law : ∀ i : ι, ((next i).map value).sum = value i

-- Reference: ticket #167 — the Bayesian instance carrier: the hypotheses
-- (nodup outcomes, cells covered, distributions) are unconditional in `h`,
-- so the law holds at EVERY stage (ledger), not just the initial one.
/-- The **Bayesian mass process** over a distribution-valued prediction
family on a nodup outcome list: stages are ledgers, value is `ledgerSum`,
successors are the one-observation updates. -/
structure BayesMassProcess {hyp outcome : Type} [DecidableEq outcome]
    (predict : hyp → List (ℚ × outcome)) (os : List outcome) where
  nodup : os.Nodup
  cells : ∀ h : hyp, ∀ q ∈ predict h, q.2 ∈ os
  dist : ∀ h : hyp, isDistribution (predict h) = true
  process : ConservedMassProcess (List (hyp × ℚ))
  value_eq : process.value = ledgerSum
  next_eq : process.next = fun l => os.map (fun o => bayesUpdate predict o l)

-- Reference: ticket #167 — the instance: the law is
-- `bayesUpdate_conservation` composed with `List.map_map`.
/-- Construct the Bayesian mass process from its hypotheses. -/
def bayesMassProcess {hyp outcome : Type} [DecidableEq outcome]
    (predict : hyp → List (ℚ × outcome)) (os : List outcome)
    (hnodup : os.Nodup) (hcells : ∀ h : hyp, ∀ q ∈ predict h, q.2 ∈ os)
    (hdist : ∀ h : hyp, isDistribution (predict h) = true) :
    BayesMassProcess predict os where
  nodup := hnodup
  cells := hcells
  dist := hdist
  process :=
    { value := ledgerSum
      next := fun l => os.map (fun o => bayesUpdate predict o l)
      law := fun l => by
        have h := bayesUpdate_conservation predict os l hnodup
          (fun p _ q hq => hcells p.1 q hq) (fun p _ => hdist p.1)
        exact (congrArg List.sum (List.map_map (g := ledgerSum)
          (f := fun o => bayesUpdate predict o l) (l := os))).trans h }
  value_eq := rfl
  next_eq := rfl

/-! ## Toy: the coin ledger's conservation -/

-- Reference: ticket #167 toy — `List.nodup_cons`, `List.not_mem_nil`,
-- `Coin.noConfusion`.
/-- The coin outcome list is nodup. -/
theorem coinOutcomes_nodup : ([Coin.heads, Coin.tails] : List Coin).Nodup :=
  List.nodup_cons.mpr ⟨fun h => (List.mem_cons.mp h).elim (fun he => Coin.noConfusion he)
    (fun hn => absurd hn List.not_mem_nil),
    List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩⟩

-- Reference: ticket #167 toy — every cell of every coin table is a coin
-- outcome (`List.mem_cons`).
/-- All cells of all coin prediction tables are coin outcomes. -/
theorem coinPredict_cells (h : CoinHyp) (q : ℚ × Coin) (hq : q ∈ coinPredict h) :
    q.2 ∈ ([Coin.heads, Coin.tails] : List Coin) := by
  cases h with
  | fair | biased | loaded =>
      rcases List.mem_cons.mp hq with he | he'
      · subst he
        exact List.mem_cons_self
      · rcases List.mem_cons.mp he' with he | hn
        · subst he
          exact List.mem_cons_of_mem Coin.heads List.mem_cons_self
        · exact absurd hn List.not_mem_nil

-- Reference: ticket #167 toy — `weightsSum_cons`, `isDistribution_eq_true`,
-- `two_mul`/`mul_div_cancel₀` for `1/2 + 1/2 = 1`, `div_eq_mul_inv`/`add_mul`/
-- `mul_inv_cancel₀` for `2/3 + 1/3 = 1`, `add_zero` for `1 + 0 = 1`.
-- Reference: `weightsSum_cons` twice + `List.map_nil`/`List.sum_nil`.
/-- The total weight of a two-cell table is `a + (b + 0)`. -/
theorem weightsSum_two {outcome : Type} (a b : ℚ) (o1 o2 : outcome) :
    weightsSum [(a, o1), (b, o2)] = a + (b + 0) :=
  (weightsSum_cons (a, o1) [(b, o2)]).trans
    (congrArg (fun x => (a, o1).1 + x)
      ((weightsSum_cons (b, o2) []).trans
        (congrArg (fun x => b + x)
          ((congrArg List.sum (List.map_nil (f := Prod.fst))).trans List.sum_nil))))

-- Reference: ticket #167 toy — `weightsSum_two`, `isDistribution_eq_true`,
-- `two_mul`/`mul_div_cancel₀` for `1/2 + 1/2 = 1`, `div_eq_mul_inv`/`add_mul`/
-- `mul_inv_cancel₀` for `2/3 + 1/3 = 1`, `add_zero`/`zero_add` for `1 + 0 = 1`.
/-- Every coin prediction table is a distribution. -/
theorem coinPredict_dist (h : CoinHyp) : isDistribution (coinPredict h) = true := by
  have h3 : (3:ℚ) ≠ 0 := (Nat.cast_ne_zero (R := ℚ)).mpr (Nat.succ_ne_zero 2)
  have hhalf : (1/2 : ℚ) + 1/2 = 1 :=
    (two_mul (1/2)).symm.trans (mul_div_cancel₀ 1 two_ne_zero_rat)
  have hthird : (2/3 : ℚ) + 1/3 = 1 := by
    have e1 : (2/3 : ℚ) + 1/3 = 2 * (3:ℚ)⁻¹ + 1 * (3:ℚ)⁻¹ :=
      congrArg₂ (· + ·) (div_eq_mul_inv 2 3) (div_eq_mul_inv 1 3)
    have e2 : 2 * (3:ℚ)⁻¹ + 1 * (3:ℚ)⁻¹ = (2 + 1) * (3:ℚ)⁻¹ := (add_mul 2 1 _).symm
    have e3 : (2 + 1) * (3:ℚ)⁻¹ = 3 * (3:ℚ)⁻¹ :=
      congrArg (· * (3:ℚ)⁻¹) (Nat.cast_add_one (R := ℚ) 2).symm
    exact e1.trans (e2.trans (e3.trans (mul_inv_cancel₀ h3)))
  cases h with
  | fair =>
      exact (isDistribution_eq_true _).mpr
        ((weightsSum_two (1/2) (1/2) Coin.heads Coin.tails).trans
          ((congrArg (fun x => (1/2:ℚ) + x) (add_zero (1/2))).trans hhalf))
  | biased =>
      exact (isDistribution_eq_true _).mpr
        ((weightsSum_two (2/3) (1/3) Coin.heads Coin.tails).trans
          ((congrArg (fun x => (2/3:ℚ) + x) (add_zero (1/3))).trans hthird))
  | loaded =>
      exact (isDistribution_eq_true _).mpr
        ((weightsSum_two 1 0 Coin.heads Coin.tails).trans
          ((congrArg (fun x => (1:ℚ) + x) (zero_add 0)).trans (add_zero (1:ℚ))))

-- Reference: ticket #167 toy — the coin conservation
-- theorem applied to the uniform coin ledger (`coinLedger`, #29).
/-- **The coin ledger's total weight is conserved in expectation** under one
Bayesian update: both sides are `3`. -/
theorem coin_bayes_conservation :
    (coinOutcomes.map fun o => ledgerSum (bayesUpdate coinPredict o coinLedger)).sum
      = ledgerSum coinLedger :=
  bayesUpdate_conservation coinPredict coinOutcomes coinLedger coinOutcomes_nodup
    (fun p _ q hq => coinPredict_cells p.1 q hq) (fun p _ => coinPredict_dist p.1)

-- Reference: ticket #167, acceptance — `#eval` prints both sides of the coin
-- conservation (3 = 3) and the per-outcome updated totals.
#eval (coinOutcomes.map fun o => ledgerSum (bayesUpdate coinPredict o coinLedger)).sum
#eval ledgerSum coinLedger
#eval coinOutcomes.map fun o => ledgerSum (bayesUpdate coinPredict o coinLedger)

end BoringLab
