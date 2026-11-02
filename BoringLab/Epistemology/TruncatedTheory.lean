/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import BoringLab.Epistemology.Truncation
import BoringLab.Epistemology.TheoryElement

/-!
# Truncated theory-elements: level-indexed requirement satisfaction

Ticket #42 (EPI.8.2), building on the truncation structure of #41
(`BoringLab.Epistemology.Truncation`) and the theory-elements of #30:
a theory-element whose empirical claim is tracked only up to a level — the
level-indexed requirement satisfaction for the physics audits (statement
layer for the PHYS rows of #44).

* `takeClaim` — the empirical claim restricted to the first `n` intended
  applications;
* `takeClaim_down` — **proved**: the claim at level `m` implies the claim at
  every lower level `n ≤ m` (prefix monotonicity of `List.take`);
* `TruncatedTheory` — a theory-element with a level and the partial claim
  as a `Prop` field (hypothesis-carrier, STYLE.D);
* the toy: the #30 coin theory-element truncated at level 1.

## References
* [Sneed] J. D. Sneed, *The Logical Structure of Mathematical Physics*,
  Synthese Library vol. 114, 1979, ch. 2 (theory-elements; the empirical
  claim `I ⊆ M`).
* [Bishop–Bridges] E. Bishop, D. Bridges, *Constructive Analysis*, Springer
  1985, ch. 2 (tracked approximations; the truncation reading of #41).
* Program register: BoringLab tickets #41 (EPI.8.1, landed) and #42
  (EPI.8.2); the toy is the #30 coin theory-element.
-/

universe u

namespace BoringLab

/-! ## The level-indexed empirical claim -/

-- Reference: ticket #42; [Sneed], ch. 2 (the empirical claim), truncated to
-- the first `n` intended applications (the level-indexed requirement
-- satisfaction).
/-- The **partial empirical claim** of a theory-element at level `n`: every
intended application among the first `n` is an actual model. -/
def takeClaim {carrier : Type u} (te : TheoryElement carrier) (n : ℕ) : Prop :=
  ∀ i ∈ te.applications.take n, te.isActual i = true

-- Reference: ticket #42 — prefix monotonicity of the claim: `n ≤ m` gives
-- `take n ⊆ take m` (via `List.take_take` and `Nat.min_eq_right`), then
-- #41's `mem_of_mem_take`.
/-- **The partial claim is downward closed in the level**: the claim at
level `m` implies the claim at every `n ≤ m`. -/
theorem takeClaim_down {carrier : Type u} (te : TheoryElement carrier) {n m : ℕ} (h : n ≤ m)
    (hc : takeClaim te m) : takeClaim te n := by
  intro i hi
  apply hc
  have htake : te.applications.take n = (te.applications.take m).take n :=
    ((List.take_take (i := n) (j := m) (l := te.applications)).trans
      (congrArg (fun k => te.applications.take k) (Nat.min_eq_left h))).symm
  exact List.mem_of_mem_take (l := te.applications.take m) (i := n)
    (Eq.subst (motive := fun L => i ∈ L) htake hi)

/-! ## Truncated theory-elements -/

-- Reference: ticket #42 (EPI.8.2): a truncated theory-element — the
-- theory-element data with a level and the partial empirical claim as a
-- `Prop` field (hypothesis-carrier, STYLE.D; never a global axiom).
/-- A **truncated theory-element**: a theory-element, a level, and the
partial empirical claim at that level. -/
structure TruncatedTheory (carrier : Type u) where
  /-- The underlying theory-element. -/
  te : TheoryElement carrier
  /-- The truncation level. -/
  level : ℕ
  /-- The partial empirical claim at the level. -/
  claim : takeClaim te level

-- Reference: [Barendregt], ch. 2 (eta conversion), as in
-- `Truncation.eta`.
-- REVIEW(citation): pin down the exact section in review.
/-- **Eta conversion for truncated theory-elements**. -/
theorem TruncatedTheory.eta {carrier : Type u} (t : TruncatedTheory carrier) :
    TruncatedTheory.mk t.te t.level t.claim = t := by
  cases t with
  | mk te level claim => rfl

-- Reference: ticket #42 — a truncated theory-element at level `m`
-- restricts to level `n ≤ m` (by `takeClaim_down`).
/-- **Restriction of a truncated theory-element** to a lower level. -/
def TruncatedTheory.restrict {carrier : Type u} (t : TruncatedTheory carrier) {n : ℕ}
    (h : n ≤ t.level) : TruncatedTheory carrier :=
  { te := t.te
    level := n
    claim := takeClaim_down t.te h t.claim }

/-! ## Toy: the coin theory-element of #30, truncated at level 1 -/

-- Reference: program's own toy (#30's `coinTheory`); the singleton
-- application list, so the level-1 claim is exactly `coinTheory_empirical`
-- (`List.take` of a singleton at 1 is the singleton, definitionally).
/-- The coin theory-element truncated at level `1`. -/
def coinTrunc : TruncatedTheory CoinData where
  te := coinTheory
  level := 1
  claim := fun i hi => coinTheory_empirical i hi

-- Reference: ticket #42, toy: the restriction to level `0` — the empty
-- claim (vacuous, `List.take 0 = []`).
/-- The level-0 restriction of the coin truncated theory. -/
def coinTrunc0 : TruncatedTheory CoinData := coinTrunc.restrict (Nat.zero_le 1)

-- Reference: ticket #42, toy: printed levels.
#eval (coinTrunc.level, coinTrunc0.level)

end BoringLab
