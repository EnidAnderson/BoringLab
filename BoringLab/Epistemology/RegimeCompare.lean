/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import BoringLab.Epistemology.Regime

/-!
# Truncation comparison: two regimes on one carrier, refinement data

Ticket #54 (EPI.8.4), building on the regime category of #64
(`BoringLab.Epistemology.Regime`):

* a **comparison** between two regimes on the same carrier is the
  refinement data in either direction (`RegimeComparison`: optional
  forward/backward `RegimeMap`s, with the refinement/comparability flags as
  decidable data) — the refinement/incomparability statements as data;
* a PROVED refinement morphism instance: the **level shift** `listShift` on
  the list-prefix regime — level `n ↦ n + k`, identity data map, remainder
  map `r ↦ r.drop k`, zero transfer term — with the content-transport law
  proved from #41's `List.take_append_drop` / `mem_of_mem_take` /
  `List.drop_drop`;
* the EPI.8.5 comparison instance (divergent-asymptotic vs
  convergent-exact shadow: the decimal regime vs the digit-list regime) as
  an object pair, with the incomparability claim as a named hole (the
  checkable falsifier: a violated cocycle on the family is recorded, never
  assumed).

## References
* [Bishop–Bridges] E. Bishop, D. Bridges, *Constructive Analysis*, Springer
  1985, ch. 2 (tracked remainders; comparison of approximation regimes).
* Program register: BoringLab tickets #54 (EPI.8.4), #58 (EPI.8.5), #64
  (EPI.8.6); the instances are #41's.
-/

namespace BoringLab

/-! ## Comparison data -/

-- Reference: ticket #54 (EPI.8.4): two regimes on the same theory-carrier,
-- and the refinement/incomparability statements as data — optional morphisms
-- either way, with decidable flags.
/-- A **comparison** between regimes `R` and `S` on the same carrier `α`
over the additive carrier `M`: optional refinement morphisms either way. -/
structure RegimeComparison (α : Type) (M : AddCarrier) (R S : Regime α) where
  /-- The refinement `R → S`, if declared. -/
  forward : Option (RegimeMap α M R S)
  /-- The refinement `S → R`, if declared. -/
  backward : Option (RegimeMap α M S R)

-- Reference: ticket #54 (EPI.8.4): the refinement flag, as decidable data.
/-- The refinement flag of a comparison: a forward morphism is declared. -/
def RegimeComparison.refines {α : Type} {M : AddCarrier} {R S : Regime α}
    (c : RegimeComparison α M R S) : Bool := c.forward.isSome

-- Reference: ticket #54 (EPI.8.4): the comparability flag, as decidable data.
/-- The comparability flag of a comparison: a morphism is declared either
way. -/
def RegimeComparison.comparable {α : Type} {M : AddCarrier} {R S : Regime α}
    (c : RegimeComparison α M R S) : Bool := c.forward.isSome || c.backward.isSome

-- Reference: computation step (projection of the flag def); `rfl` only in
-- this primitive definitional lemma.
/-- The refinement flag of a comparison is the forward option's `isSome`. -/
theorem RegimeComparison.refines_eq {α : Type} {M : AddCarrier} {R S : Regime α}
    (c : RegimeComparison α M R S) : c.refines = c.forward.isSome := rfl

/-! ## A proved refinement morphism: the level shift on the list regime -/

-- Reference: ticket #54/#64: the level-shift refinement `listRegime s →
-- listRegime s`, level `n ↦ n + k`: identity on displayed data, remainder
-- shifted by `r ↦ r.drop k`, zero transfer term (the unit of the cocycle).
-- The content-transport law is proved from #41's list lemmas.
/-- The **level-shift refinement** on the list-prefix regime of `s` by `k`
levels, over the rational transfer carrier. -/
def listShift {γ : Type} (s : List γ) (k : ℕ) :
    RegimeMap γ ratCarrier (listRegime s) (listRegime s) where
  levelMap := fun n => n + k
  dataMap := fun _ l => l
  remainderMap := fun _ r => r.drop k
  transferTerm := fun _ => (0 : ℚ)
  law := by
    intro n x h
    rcases h with hx | hx
    · have h1 : x ∈ s := mem_of_mem_take s n x hx
      have h2 : x ∈ s.take (n + k) ++ s.drop (n + k) :=
        Eq.subst (motive := fun L => x ∈ L) (List.take_append_drop (n + k) s).symm h1
      rcases List.mem_append.mp h2 with h3 | h3
      · exact Or.inl h3
      · exact Or.inr (Eq.subst (motive := fun L => x ∈ L)
          (List.drop_drop (i := k) (j := n) (l := s)).symm h3)
    · have h1 : x ∈ s := List.mem_of_mem_drop hx
      have h2 : x ∈ s.take (n + k) ++ s.drop (n + k) :=
        Eq.subst (motive := fun L => x ∈ L) (List.take_append_drop (n + k) s).symm h1
      rcases List.mem_append.mp h2 with h3 | h3
      · exact Or.inl h3
      · exact Or.inr (Eq.subst (motive := fun L => x ∈ L)
          (List.drop_drop (i := k) (j := n) (l := s)).symm h3)

-- Reference: ticket #54: the level shift refines; the transfer term is the
-- zero transfer (cocycle unit) — computation steps.
/-- The level shift's transfer term is zero at every level. -/
theorem listShift_transferTerm {γ : Type} (s : List γ) (k n : ℕ) :
    (listShift s k).transferTerm n = (0 : ℚ) := rfl

/-! ## The EPI.8.5 comparison instance -/

-- Reference: ticket #58 (EPI.8.5): the comparison instance — the decimal
-- regime of `1/3` (divergent-asymptotic shadow) vs the digit-list regime
-- (convergent-exact shadow) — as an object pair on `ℕ`.
/-- The comparison pair: decimal regime of `1/3` vs the regime of its digit
list `[3,3,3,3,3]`. -/
def emApPair : Regime ℕ × Regime ℕ := (decRegime 1 3, listRegime [3, 3, 3, 3, 3])

-- Reference: ticket #54/#58: the incomparability claim on the pair — a
-- checkable falsifier, never blanket-assumed.
-- TEMPORARY SORRY: the honest proof has not been instantiated yet.
-- PEELING PLAN: a `RegimeMap` out of the pair is determined on the level
-- maps and transfer terms; show no level map makes the content-transport
-- law hold for both the decimal and the list regime — reduce to the
-- transfer-cocycle check on the merged remainder ledger (the dec remainder
-- is a pair `(ℕ × ℕ)` read by `decNextDigit`, the list remainder is the
-- list itself — the carriers differ, so no remainder map exists).
-- Next named lemmas: `remainderCarrier_distinct`, `no_remainderMap_emAp`.
/-- The EPI.8.5 witness: the two regimes of `emApPair` are incomparable (no
refinement either way). -/
theorem emAp_incomparable : RegimeIncomparable ℕ ratCarrier emApPair.1 emApPair.2 := by
  sorry

-- Reference: ticket #54/#58, acceptance: the comparison flags printed.
#eval ((RegimeComparison.mk (M := ratCarrier) (R := listRegime [3, 3, 3, 3, 3])
    (S := listRegime [3, 3, 3, 3, 3])
    (forward := some (listShift [3, 3, 3, 3, 3] 1)) (backward := none)).refines,
  (RegimeComparison.mk (M := ratCarrier) (R := emApPair.1) (S := emApPair.2)
    (forward := none) (backward := none)).comparable)

end BoringLab
