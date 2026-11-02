/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import BoringLab.Epistemology.RegimeCompare
import BoringLab.Epistemology.Process

/-!
# The regime–experiment row: measurement levels ARE experiment rounds

The reflexive-closure row (a) of ticket #65 (MI.0.3), made a proved
satisfaction statement about data (never a world-claim): the truncation
regime's level-`n` data has length `n` (the measurement level counts the
rounds), and the process machine's log after running a schedule `os` has
length `s.log.length + os.length` — the two level ledgers count the same
rounds. Landed pieces: `listTrunc_data` (#41), `List.length_take`,
`SciState.round_log` (#29).

## References
* [Bishop–Bridges] E. Bishop, D. Bridges, *Constructive Analysis*, Springer
  1985, ch. 2 (tracked approximations; the levels).
* Program register: BoringLab tickets #28 (EPI.1.1), #29 (EPI.1.2), #64
  (EPI.8.6), #65 (MI.0.3, row (a)).
-/

namespace BoringLab

/-! ## The level-counts-rounds law -/

-- Reference: ticket #65, row (a): a regime **tracks levels** up to `N`:
-- the level-`n` data has length `n`.
/-- A regime tracks levels up to `N`: for every `n ≤ N`, the level-`n` data
has length `n`. -/
def RegimeTracksLevels {γ : Type} (R : Regime γ) (N : ℕ) : Prop :=
  ∀ n, n ≤ N → ((R.trunc n).data).length = n

-- Reference: #41's `listTrunc_data` + `List.length_take` +
-- `Nat.min_eq_left`.
/-- The list-prefix regime tracks levels up to the stream's length
(proved). -/
theorem listRegime_tracks {γ : Type} (s : List γ) :
    RegimeTracksLevels (listRegime s) s.length := by
  intro n hn
  exact Eq.subst (motive := fun L => L.length = n)
    (listTrunc_data s n) ((List.length_take (i := n) (l := s)).trans (Nat.min_eq_left hn))

-- Reference: #29's `SciState.round_log` + induction on the schedule;
-- `add_assoc`/`Nat.add_comm` for the length arithmetic. The process
-- machine's log counts the rounds run (proved).
/-- The process machine's log length counts the rounds run (proved). -/
theorem runOn_log_length {hyp outcome : Type} [DecidableEq outcome]
    (predict : hyp → List (ℚ × outcome)) (s : SciState hyp outcome) :
    ∀ os : List outcome, (runOn predict s os).log.length = s.log.length + os.length
  | [] => (add_zero s.log.length).symm
  | o :: rest =>
      Eq.subst (motive := fun st => st.log.length = s.log.length + (o :: rest).length)
        (rfl : runOn predict s (o :: rest) = runOn predict (s.round predict o) rest)
        ((runOn_log_length predict (s.round predict o) rest).trans
          ((congrArg (fun l => l.length + rest.length) (SciState.round_log predict s o)).trans
            ((add_assoc s.log.length 1 rest.length).trans
              (congrArg (fun x => s.log.length + x) (Nat.add_comm 1 rest.length)))))

end BoringLab
