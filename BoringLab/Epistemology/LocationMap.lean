/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import BoringLab.Epistemology.TruncatedTheory
import BoringLab.Epistemology.FairExperiment
import BoringLab.Epistemology.Learning

/-!
# The location map: theory-elements located in fibers of observables

Tickets #36 (EPI.7.0, roadmap/statement layer) and #37 (EPI.7.1, observables
as periods: the prediction map on fiber data), building on the truncated
theory-elements of #42 and the theory-element category of #62:

* `LocationMap` — each truncated theory-element is located in a fiber of
  observables, with the **prediction map** on fiber data
  (`predict : t → carrier → fiber t → ℚ`, the periods-as-observables
  shadow) and the **world-connection confined to ONE hypothesis-carrier
  field** (`worldConnection`: every level-truncated intended application has
  a live observable — a `Prop` field, never a global axiom, per STYLE.D and
  MI.0.1's rule);
* the toy: the coin hypothesis theory-element located in the coin fiber,
  with the world-connection PROVED at level 1 (the `loaded` application has
  the live observable `heads`, mass `1`).

## References
* [Sneed] J. D. Sneed, *The Logical Structure of Mathematical Physics*,
  Synthese Library vol. 114, 1979, ch. 2 (theory-elements; intended
  applications).
* Program register: BoringLab tickets #36/#37 (EPI.7.0/#7.1, statement
  layer), #42, #62, #67 (MI.0.1's single-world-connection rule); the toy is
  the #28 coin family, the program's own.
-/

universe u

namespace BoringLab

/-! ## The location map -/

-- Reference: tickets #36/#37: the location map — a fiber of observables per
-- (truncated) theory-element, the prediction map on fiber data, and the
-- world-connection as ONE hypothesis-carrier field (STYLE.D; MI.0.1 #67).
/-- A **location map**: each truncated theory-element `t` is located in a
fiber `fiber t` of observables; `predict t i o` is the prediction mass of
the observable `o` under application `i`; the world-connection says every
level-truncated intended application has a live (nonzero-mass) observable. -/
structure LocationMap (carrier : Type u) where
  /-- The fiber of observables of each truncated theory-element. -/
  fiber : TruncatedTheory carrier → Type
  /-- The prediction map on fiber data. -/
  predict : (t : TruncatedTheory carrier) → carrier → fiber t → ℚ
  /-- The world-connection (the single hypothesis-carrier field): every
  level-truncated intended application has a live observable. -/
  worldConnection : ∀ (t : TruncatedTheory carrier),
    ∀ i ∈ t.te.applications.take t.level, ∃ o : fiber t, predict t i o ≠ 0

-- Reference: [Barendregt], ch. 2 (eta conversion), as in
-- `TruncatedTheory.eta`.
-- REVIEW(citation): pin down the exact section in review.
/-- **Eta conversion for location maps**. -/
theorem LocationMap.eta {carrier : Type u} (L : LocationMap carrier) :
    LocationMap.mk L.fiber L.predict L.worldConnection = L := by
  cases L with
  | mk fiber predict worldConnection => rfl

/-! ## Toy: the coin hypothesis theory-element located in the coin fiber -/

-- Reference: program's own toy: a theory-element over the #28 hypothesis
-- family as carrier (the loaded coin as the single intended application).
/-- The coin-hypothesis theory-element: models = the coin family, everything
actual, one intended application (the loaded coin). -/
def coinHypTheory : TheoryElement CoinHyp where
  models := coinHypotheses
  isActual := fun _ => true
  isPartial := fun _ => true
  applications := [CoinHyp.loaded]
  links := []
  empiricalClaim := fun _ _ => rfl

-- Reference: ticket #42 toy.
/-- The coin-hypothesis theory-element truncated at level 1. -/
def coinHypTrunc : TruncatedTheory CoinHyp where
  te := coinHypTheory
  level := 1
  claim := fun _ _ => rfl

-- Reference: #28's `tableMass_cons_same`/`_diff`/`tableMass_nil` +
-- `add_zero` (the peeled mass pattern of #28/#32).
/-- The `heads` cell of the loaded coin has mass `1`. -/
theorem coinPredict_loaded_heads_mass :
    tableMass (coinPredict CoinHyp.loaded) Coin.heads = 1 :=
  (tableMass_cons_same (1, Coin.heads) [(0, Coin.tails)] Coin.heads rfl).trans
    ((congrArg (fun x => (1, Coin.heads).1 + x)
        (tableMass_cons_diff (0, Coin.tails) [] Coin.heads (fun h => Coin.noConfusion h))).trans
      ((congrArg (fun x => (1, Coin.heads).1 + x) (tableMass_nil Coin.heads)).trans
        (add_zero (1 : ℚ))))

-- Reference: tickets #36/#37 — every hypothesis of the #28 coin family has a
-- live (nonzero-mass) cell: fair `1/2` on heads, biased `2/3` on heads,
-- loaded `1` on heads (the mass lemmas of #28 + `coinPredict_loaded_heads_mass`
-- + `div_ne_zero`/`one_ne_zero`).
/-- Every coin hypothesis has a live observable cell. -/
theorem coin_live (h : CoinHyp) : ∃ o : Coin, tableMassOf coinPredict h o ≠ 0 := by
  cases h with
  | fair =>
      exact ⟨Coin.heads, fun h0 =>
        div_ne_zero one_ne_zero (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero 1))
          (coinPredict_fair_heads_mass.symm.trans h0)⟩
  | biased =>
      exact ⟨Coin.heads, fun h0 =>
        div_ne_zero (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero 1))
          (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero 2))
          (coinPredict_biased_heads_mass.symm.trans h0)⟩
  | loaded =>
      exact ⟨Coin.heads, fun h0 =>
        one_ne_zero (coinPredict_loaded_heads_mass.symm.trans h0)⟩

-- Reference: tickets #36/#37, toy: the coin location map — fiber = the coin
-- outcome space, prediction = the #28 table mass; the world-connection holds
-- for every truncated theory because every coin hypothesis has a live cell
-- (`coin_live`).
/-- The **coin location map**: every truncated coin-hypothesis theory is
located in the coin outcome fiber, with the #28 prediction table as the
prediction map. -/
def coinLocation : LocationMap CoinHyp where
  fiber := fun _ => Coin
  predict := fun _ h o => tableMassOf coinPredict h o
  worldConnection := fun _t i _ => coin_live i

end BoringLab
