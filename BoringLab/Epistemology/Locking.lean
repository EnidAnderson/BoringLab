/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import BoringLab.Epistemology.TruncatedLearning

/-!
# Locking prefixes: the mind-change ledger stabilizes at a locking level

Ticket #163 (EPI.8.4), building on #43's level ledger
(`BoringLab.Epistemology.TruncatedLearning`: `mindChangesAtLevel`,
`changePredAt`, `mindChangesAtLevel_mono`) and on the elimination bound of
`BoringLab.Epistemology.OckhamBound` (`elimLearner_mindChanges_le`).

* `IsLockingPrefix` — from level `n` on, the learner's output on the
  prefixes of a schedule `s` never changes (Kelly's locking, on the finite
  carrier);
* `lockingPrefix_self` — PROVED: the full schedule locks at its own length;
* `mindChangesAtLevel_stable` — PROVED: past the schedule length the level
  ledger is constant (`List.take_of_length_le`, `List.take_length`);
* `changePredAt_take_of_lt` / `changePredAt_take_self` — PROVED computation
  steps: the change predicate of the truncated schedule agrees with the one
  of `s` below the level, and is `false` at the level itself;
* `changePredAt_eq_false_of_locking` — PROVED: a locked level contributes no
  change above it;
* `filter_range_changePredAt_take` / `filter_range_eq_of_false_above` —
  PROVED helpers: the level-`m` change filter collapses to the full-schedule
  one on `range m`, and a false band `[n, m)` removes nothing;
* `mindChangesAtLevel_locked_const` — PROVED: a locking level `n` freezes the
  level ledger at every `m ≥ n`;
* `mindChangesAtLevel_le_card_elim` — PROVED: the elimination learner makes
  at most `|hs|` mind changes at ANY level (level-`n` form of the Gold bound);
* `identification_locks` — PROVED: identification past a bound is locking
  onto the true hypothesis among compatible prefixes;
* `elimLearner_locks_eventually` — PROVED: the elimination learner locks at
  some level `≤ s.length`;
* `not_locking_le_card_coin_witness` — PROVED NEGATIVE RESULT (recorded
  correction): the locking level is NOT bounded by `|hs|` in general — the
  `|hs|` bound (`elimLearner_mindChanges_le`) is on the COUNT of mind changes,
  not on the locking level; a concrete coin witness below;
* toy: the coin elimination learner locks at level 0 — PROVED
  (`elimLearner_coin_fair`), cross-checked against #43's `coinLevelLedger`
  (all zeros), printed by `#eval`.

## References
* [Kelly] K. T. Kelly, *The Logic of Reliable Inquiry*, OUP, 1996 (locking
  sequences; mind changes).
* [Gold] E. M. Gold, "Language identification in the limit", *Information and
  Control* 10(5):447–474, 1967.
* Program register: BoringLab tickets #163 (EPI.8.4), #31 (EPI.3.1), #43
  (EPI.8.3). REVIEW(citation): pin Kelly's locking-lemma page/section at
  review.
-/

namespace BoringLab

open scoped List

/-! ## Locking prefixes -/

-- Reference: [Kelly] 1996 (a locking sequence: past it the learner never
-- changes its mind); ticket #163 item (a) — on the finite-prefix carrier of
-- #31, "prefix of the schedule" is `s.take i`.
/-- A level `n` **locks** the learner `M` on the schedule `s` when the output
on every prefix of length between `n` and `s.length` agrees. -/
def IsLockingPrefix {hyp datum : Type} (M : List datum → hyp) (s : List datum)
    (n : ℕ) : Prop :=
  ∀ i j : ℕ, n ≤ i → i ≤ j → j ≤ s.length → M (s.take i) = M (s.take j)

-- Reference: ticket #163 item (a) — the full schedule always locks at its own
-- length (the only prefix lengths in range coincide); core `Nat.le_antisymm`.
/-- **The full schedule locks at its own length** (trivial finite locking). -/
theorem lockingPrefix_self {hyp datum : Type} (M : List datum → hyp)
    (s : List datum) : IsLockingPrefix M s s.length := by
  intro i j hi hij hj
  have hi' : i = s.length := Nat.le_antisymm (Nat.le_trans hij hj) hi
  have hj' : j = s.length := Nat.le_antisymm hj (Nat.le_trans hi hij)
  subst hi'
  subst hj'
  exact rfl

-- Reference: ticket #163 item (a) — stabilization past the schedule length:
-- `s.take n = s` (`List.take_of_length_le`) and `s.take s.length = s`
-- (`List.take_length`), so both level ledgers are `mindChangesOn M s`.
/-- **The level ledger is stable past the schedule length**: for
`s.length ≤ n`, the ledger at level `n` equals the one at the full length. -/
theorem mindChangesAtLevel_stable {hyp datum : Type} [DecidableEq hyp]
    (M : List datum → hyp) (s : List datum) {n : ℕ} (h : s.length ≤ n) :
    mindChangesAtLevel M s n = mindChangesAtLevel M s s.length := by
  have e1 : s.take n = s := List.take_of_length_le h
  have e2 : s.take s.length = s := List.take_length
  exact (congrArg (mindChangesOn M) e1).trans (congrArg (mindChangesOn M) e2).symm

/-! ## The change predicate of a truncated schedule -/

-- Reference: ticket #163 — computation step: below the level the truncated
-- takes agree with the full ones (`List.take_take`, `Nat.min_eq_left`), so
-- the two `ite`s decide the same proposition; `ite_eq_left`/`ite_eq_right`
-- close each case.
/-- **Below the level, the truncated change predicate agrees with the full
one**: for `i < m`, the change predicate at `i` on `s.take m` equals the one
on `s`. -/
theorem changePredAt_take_of_lt {hyp datum : Type} [DecidableEq hyp]
    (M : List datum → hyp) (s : List datum) {m i : ℕ} (hi : i < m) :
    changePredAt M (s.take m) i = changePredAt M s i := by
  unfold changePredAt
  have e1 : (s.take m).take i = s.take i :=
    (List.take_take (i := i) (j := m) (l := s)).trans
      (congrArg (s.take) (Nat.min_eq_left (Nat.le_of_lt hi)))
  have e2 : (s.take m).take (i + 1) = s.take (i + 1) :=
    (List.take_take (i := i + 1) (j := m) (l := s)).trans
      (congrArg (s.take) (Nat.min_eq_left (Nat.succ_le_of_lt hi)))
  have hM1 : M ((s.take m).take i) = M (s.take i) := congrArg M e1
  have hM2 : M ((s.take m).take (i + 1)) = M (s.take (i + 1)) := congrArg M e2
  have hiff : (M ((s.take m).take i) = M ((s.take m).take (i + 1))) ↔
      (M (s.take i) = M (s.take (i + 1))) :=
    Iff.intro (fun hc => (hM1.symm.trans hc).trans hM2)
      (fun hc => (hM1.trans hc).trans hM2.symm)
  have hd : Decidable (M ((s.take m).take i) = M ((s.take m).take (i + 1))) :=
    inferInstance
  cases hd with
  | isTrue hc => exact (ite_eq_left hc).trans (ite_eq_left (hiff.mp hc)).symm
  | isFalse hc =>
      exact (ite_eq_right hc).trans (ite_eq_right (fun h' => hc (hiff.mpr h'))).symm

-- Reference: ticket #163 — computation step: at the level itself both
-- truncated takes are `s.take m` (`List.take_take`, `Nat.min_eq_left`,
-- `Nat.min_eq_right`), so the change predicate is `false` (`ite_eq_left`).
/-- **At the level itself the truncated change predicate is `false`**: the
two takes at index `m` coincide. -/
theorem changePredAt_take_self {hyp datum : Type} [DecidableEq hyp]
    (M : List datum → hyp) (s : List datum) (m : ℕ) :
    changePredAt M (s.take m) m = false := by
  unfold changePredAt
  have e1 : (s.take m).take m = s.take m :=
    (List.take_take (i := m) (j := m) (l := s)).trans
      (congrArg (s.take) (Nat.min_eq_left (Nat.le_refl m)))
  have e2 : (s.take m).take (m + 1) = s.take m :=
    (List.take_take (i := m + 1) (j := m) (l := s)).trans
      (congrArg (s.take) (Nat.min_eq_right (Nat.le_succ m)))
  have hc : M ((s.take m).take m) = M ((s.take m).take (m + 1)) :=
    (congrArg M e1).trans (congrArg M e2).symm
  exact ite_eq_left hc

-- Reference: ticket #163 — a locked level contributes no change above it:
-- `IsLockingPrefix` gives `M (s.take i) = M (s.take (i+1))` for
-- `n ≤ i < s.length`; at `i = s.length` both takes are `s`
-- (`List.take_of_length_le`, `List.take_length`); `ite_eq_left` closes.
/-- **Above a locking level the change predicate is `false`**. -/
theorem changePredAt_eq_false_of_locking {hyp datum : Type} [DecidableEq hyp]
    (M : List datum → hyp) (s : List datum) {n i : ℕ}
    (hlock : IsLockingPrefix M s n) (hni : n ≤ i) (his : i ≤ s.length) :
    changePredAt M s i = false := by
  unfold changePredAt
  rcases Nat.lt_or_ge i s.length with hlt | hge
  · have hc : M (s.take i) = M (s.take (i + 1)) :=
      hlock i (i + 1) hni (Nat.le_succ i) (Nat.succ_le_of_lt hlt)
    exact ite_eq_left hc
  · have hi : i = s.length := Nat.le_antisymm his hge
    subst hi
    have e : s.take (s.length + 1) = s.take s.length :=
      (List.take_of_length_le (Nat.le_succ s.length)).trans List.take_length.symm
    have hc : M (s.take s.length) = M (s.take (s.length + 1)) := (congrArg M e).symm
    exact ite_eq_left hc

/-! ## Filter collapse helpers -/

-- Reference: ticket #163 — the level-`m` filtered range collapses to the
-- full-schedule predicate on `range m`: `List.range_succ` +
-- `List.filter_append` + `List.filter_congr` (`changePredAt_take_of_lt`) +
-- `List.filter_cons` (`changePredAt_take_self`) + `List.append_nil`.
/-- **The level-`m` change filter is the full-schedule one on `range m`**:
index `m` itself never contributes, and below `m` the truncated predicate
agrees with the full one. -/
theorem filter_range_changePredAt_take {hyp datum : Type} [DecidableEq hyp]
    (M : List datum → hyp) (s : List datum) (m : ℕ) :
    ((List.range (m + 1)).filter (changePredAt M (s.take m)))
      = ((List.range m).filter (changePredAt M s)) := by
  have e : List.range (m + 1) = List.range m ++ [m] := List.range_succ
  have hf : ((List.range m ++ [m]).filter (changePredAt M (s.take m)))
      = ((List.range m).filter (changePredAt M (s.take m)))
        ++ ([m].filter (changePredAt M (s.take m))) :=
    List.filter_append _ _
  have hsing : [m].filter (changePredAt M (s.take m)) = [] := by
    cases hb : changePredAt M (s.take m) m with
    | true =>
        exact (Bool.false_ne_true
          ((hb.symm.trans (changePredAt_take_self M s m)).symm)).elim
    | false =>
        exact (List.filter_cons (p := changePredAt M (s.take m)) (x := m) (xs := [])).trans
          (Eq.subst (motive := fun b =>
            (if b then m :: ([] : List ℕ).filter (changePredAt M (s.take m))
              else ([] : List ℕ).filter (changePredAt M (s.take m))) = []) hb.symm rfl)
  have hcongr : ((List.range m).filter (changePredAt M (s.take m)))
      = ((List.range m).filter (changePredAt M s)) :=
    List.filter_congr (fun i hi => changePredAt_take_of_lt M s (List.mem_range.mp hi))
  exact (congrArg (List.filter (changePredAt M (s.take m))) e).trans
    (hf.trans ((congrArg (fun l => l ++ ([m].filter (changePredAt M (s.take m)))) hcongr).trans
      ((congrArg (fun l => ((List.range m).filter (changePredAt M s)) ++ l) hsing).trans
        (List.append_nil _))))

-- Reference: ticket #163 — helper: filtering `range m` at a predicate that is
-- `false` on the band `[n, m)` equals filtering `range n`; induction on `m`
-- with `List.range_succ`, `List.filter_append`, `List.append_nil` (the
-- `n = m+1` case is `rfl`).
/-- **Filtering `range m` above a false band `[n, m)` changes nothing**. -/
theorem filter_range_eq_of_false_above {P : ℕ → Bool} (n m : ℕ) (hnm : n ≤ m)
    (hf : ∀ i : ℕ, n ≤ i → i < m → P i = false) :
    ((List.range m).filter P) = ((List.range n).filter P) := by
  induction m generalizing n with
  | zero =>
      have hn : n = 0 := Nat.le_antisymm hnm (Nat.zero_le n)
      subst hn
      exact rfl
  | succ m ih =>
      rcases Nat.lt_or_ge n (m + 1) with hlt | hge
      · have hnm' : n ≤ m := Nat.le_of_lt_succ hlt
        have e : List.range (m + 1) = List.range m ++ [m] := List.range_succ
        have hf' : ((List.range m ++ [m]).filter P)
            = ((List.range m).filter P) ++ ([m].filter P) :=
          List.filter_append _ _
        have hsing : [m].filter P = [] := by
          cases hb : P m with
          | true =>
              exact (Bool.false_ne_true
                ((hb.symm.trans (hf m hnm' (Nat.lt_succ_self m))).symm)).elim
          | false =>
              exact (List.filter_cons (p := P) (x := m) (xs := [])).trans
                (Eq.subst (motive := fun b =>
                  (if b then m :: ([] : List ℕ).filter P else ([] : List ℕ).filter P) = [])
                  hb.symm rfl)
        have ih' : ((List.range m).filter P) = ((List.range n).filter P) :=
          ih n hnm' (fun i hi hi' => hf i hi (Nat.lt_of_lt_of_le hi' (Nat.le_succ m)))
        exact (congrArg (List.filter P) e).trans
          (hf'.trans ((congrArg (fun l => l ++ ([m].filter P)) ih').trans
            ((congrArg (fun l => ((List.range n).filter P) ++ l) hsing).trans
              (List.append_nil _))))
      · have hn : n = m + 1 := Nat.le_antisymm hnm hge
        subst hn
        exact rfl

/-! ## The main stabilization theorem -/

-- Reference: ticket #163 item (b) — the level-`m` ledger collapses to the
-- full-schedule filter on `range m` (`filter_range_changePredAt_take`), the
-- false band above the locking level removes the indices `[n, m)`
-- (`changePredAt_eq_false_of_locking` + `filter_range_eq_of_false_above`),
-- and `List.length_take` + `Nat.min_eq_left` align the ranges with the levels
-- (the `Eq.subst` ending pattern is #43's `mindChangesAtLevel_mono`).
/-- **A locking level freezes the level ledger**: if level `n` locks `M` on
`s`, then for every `n ≤ m ≤ s.length` the ledger at level `m` equals the one
at level `n`. -/
theorem mindChangesAtLevel_locked_const {hyp datum : Type} [DecidableEq hyp]
    (M : List datum → hyp) (s : List datum) {n m : ℕ}
    (hlock : IsLockingPrefix M s n) (hnm : n ≤ m) (hms : m ≤ s.length) :
    mindChangesAtLevel M s m = mindChangesAtLevel M s n := by
  have hns : n ≤ s.length := Nat.le_trans hnm hms
  have hlen_m : (s.take m).length = m :=
    (List.length_take (i := m) (l := s)).trans (Nat.min_eq_left hms)
  have hlen_n : (s.take n).length = n :=
    (List.length_take (i := n) (l := s)).trans (Nat.min_eq_left hns)
  have hcoll_m : ((List.range (m + 1)).filter (changePredAt M (s.take m)))
      = ((List.range m).filter (changePredAt M s)) :=
    filter_range_changePredAt_take M s m
  have hcoll_n : ((List.range (n + 1)).filter (changePredAt M (s.take n)))
      = ((List.range n).filter (changePredAt M s)) :=
    filter_range_changePredAt_take M s n
  have hband : ((List.range m).filter (changePredAt M s))
      = ((List.range n).filter (changePredAt M s)) :=
    filter_range_eq_of_false_above n m hnm
      (fun i hni him =>
        changePredAt_eq_false_of_locking M s hlock hni (Nat.le_trans (Nat.le_of_lt him) hms))
  have hlists : ((List.range (m + 1)).filter (changePredAt M (s.take m)))
      = ((List.range (n + 1)).filter (changePredAt M (s.take n))) :=
    hcoll_m.trans (hband.trans hcoll_n.symm)
  have hlen_eq := congrArg List.length hlists
  change ((List.range ((s.take m).length + 1)).filter (changePredAt M (s.take m))).length =
    ((List.range ((s.take n).length + 1)).filter (changePredAt M (s.take n))).length
  exact Eq.subst (motive := fun k =>
      ((List.range (k + 1)).filter (changePredAt M (s.take m))).length =
      ((List.range ((s.take n).length + 1)).filter (changePredAt M (s.take n))).length)
    hlen_m.symm
    (Eq.subst (motive := fun k =>
      ((List.range (m + 1)).filter (changePredAt M (s.take m))).length =
      ((List.range (k + 1)).filter (changePredAt M (s.take n))).length)
      hlen_n.symm hlen_eq)

/-! ## The level-n Gold bound and identification-as-locking -/

-- Reference: ticket #163 item (c) — the level-`n` form of the Gold bound:
-- `mindChangesAtLevel M s n` is definitionally `mindChangesOn M (s.take n)`,
-- and `elimLearner_mindChanges_le` (OckhamBound, [Gold] 1967) bounds that by
-- `|hs|`.
/-- **The elimination learner makes at most `|hs|` mind changes at ANY
level**: the level-`n` ledger of the elimination learner on `s` is bounded by
the family size. -/
theorem mindChangesAtLevel_le_card_elim {hyp datum : Type} [DecidableEq hyp]
    (hs : List hyp) (mass : hyp → datum → ℚ) (default : hyp) (s : List datum)
    (n : ℕ) :
    mindChangesAtLevel (elimLearner hs mass default) s n ≤ hs.length :=
  elimLearner_mindChanges_le hs mass default (s.take n)

-- Reference: [Gold] 1967 + ticket #163 item (d) — identification past a bound
-- IS locking onto the true hypothesis: both `p` and `q` output `h`.
/-- **Identification past a bound locks the learner onto `h` among compatible
prefixes**: any two compatible prefixes past `N` get the same output. -/
theorem identification_locks {hyp datum : Type} (M : List datum → hyp)
    (mass : hyp → datum → ℚ) (h : hyp) (N : ℕ)
    (hid : ∀ p : List datum, Compatible mass h p → N ≤ p.length → M p = h)
    (p q : List datum) (hpc : Compatible mass h p) (hqc : Compatible mass h q)
    (hpN : N ≤ p.length) (hqN : N ≤ q.length) : M p = M q :=
  (hid p hpc hpN).trans (hid q hqc hqN).symm

-- Reference: ticket #163 item (d) — locking exists at level `≤ s.length`:
-- the full schedule locks (`lockingPrefix_self`).
/-- **The elimination learner locks at some level `≤ s.length`** on any
finite schedule. -/
theorem elimLearner_locks_eventually {hyp datum : Type}
    (hs : List hyp) (mass : hyp → datum → ℚ) (default : hyp) (s : List datum) :
    ∃ n : ℕ, n ≤ s.length ∧ IsLockingPrefix (elimLearner hs mass default) s n :=
  ⟨s.length, Nat.le_refl _, lockingPrefix_self _ _⟩

/-! ## Recorded correction: the locking level is not bounded by `|hs|` -/

-- Reference: ticket #163 item (d) — the loaded coin's heads cell has mass `1`
-- (same `tableMass_cons_same`/`tableMass_cons_diff`/`tableMass_nil`/`add_zero`
-- chain as #28's `coinPredict_loaded_tails_mass`).
/-- The loaded coin's heads cell has mass `1`. -/
theorem coinMass_loaded_heads : coinMass CoinHyp.loaded Coin.heads = 1 :=
  (tableMass_cons_same (1, Coin.heads) [(0, Coin.tails)] Coin.heads rfl).trans
    ((congrArg (fun x => (1, Coin.heads).1 + x)
        (tableMass_cons_diff (0, Coin.tails) [] Coin.heads (fun h => Coin.noConfusion h))).trans
      ((congrArg (fun x => (1, Coin.heads).1 + x) (tableMass_nil Coin.heads)).trans
        (add_zero (1 : ℚ))))

-- Reference: ticket #163 toy — `massAllows_eq_true` + `coinMass_loaded_heads`
-- + `one_ne_zero`.
/-- The loaded coin allows heads (Bool shadow). -/
theorem massAllows_coin_loaded_heads : massAllows coinMass CoinHyp.loaded Coin.heads = true :=
  (massAllows_eq_true coinMass CoinHyp.loaded Coin.heads).mpr
    (Eq.subst (motive := fun x => x ≠ 0) coinMass_loaded_heads.symm one_ne_zero)

-- Reference: ticket #163 toy — `massAllows` unfolds to `ite` on the mass;
-- `coinPredict_loaded_tails_mass` (#28) gives the tails cell mass `0`, so the
-- flag is `false` (`ite_eq_left`).
/-- The loaded coin does NOT allow tails (Bool shadow). -/
theorem massAllows_coin_loaded_tails : massAllows coinMass CoinHyp.loaded Coin.tails = false := by
  unfold massAllows
  exact ite_eq_left coinPredict_loaded_tails_mass

-- Reference: ticket #163 toy — `List.all_eq_true` + the two flags above +
-- `List.mem_cons`.
/-- The loaded coin is compatible with `[heads, heads]` but not with
`[heads, heads, tails]` (Bool shadow). -/
theorem compatibleBool_coin_loaded_hh :
    compatibleBool coinMass CoinHyp.loaded [Coin.heads, Coin.heads] = true :=
  List.all_eq_true.mpr (fun d hd => by
    rcases List.mem_cons.mp hd with he | hd'
    · subst he; exact massAllows_coin_loaded_heads
    · rcases List.mem_cons.mp hd' with he | hn
      · subst he; exact massAllows_coin_loaded_heads
      · exact absurd hn List.not_mem_nil)

-- Reference: ticket #163 toy — as above; tails ∈ [heads, heads, tails] forces
-- the flag `false`.
/-- The loaded coin is incompatible with `[heads, heads, tails]`. -/
theorem compatibleBool_coin_loaded_hht :
    compatibleBool coinMass CoinHyp.loaded [Coin.heads, Coin.heads, Coin.tails] = false := by
  cases hb : compatibleBool coinMass CoinHyp.loaded [Coin.heads, Coin.heads, Coin.tails] with
  | true =>
      have hmem : Coin.tails ∈ [Coin.heads, Coin.heads, Coin.tails] :=
        List.mem_cons_of_mem Coin.heads (List.mem_cons_of_mem Coin.heads List.mem_cons_self)
      have hb' := (List.all_eq_true.mp hb) Coin.tails hmem
      exact (Bool.false_ne_true
        (Eq.subst (motive := fun b => b = true) massAllows_coin_loaded_tails hb')).elim
  | false => rfl

-- Reference: core `Nat.cast_ne_zero` (CharZero) + `Nat.succ_ne_zero` gives
-- `(2:ℚ) ≠ 0`, avoiding the `NeZero` instance route.
/-- Two is nonzero in the rationals. -/
theorem two_ne_zero_rat : (2:ℚ) ≠ 0 :=
  (Nat.cast_ne_zero (R := ℚ)).mpr (Nat.succ_ne_zero 1)

/-! ## Toy: the coin elimination learner locks at level 0 -/

-- Reference: ticket #163 item (e), toy — the fair coin has mass `1/2` on both
-- outcomes (`coinPredict_fair_heads_mass`/`coinPredict_fair_tails_mass` from
-- #28) and `div_ne_zero one_ne_zero two_ne_zero_rat` gives `(1/2 : ℚ) ≠ 0`.
/-- The fair coin's mass is nonzero on both outcomes. -/
theorem coinMass_fair_ne_zero (c : Coin) : coinMass CoinHyp.fair c ≠ 0 := by
  cases c with
  | heads =>
      exact Eq.subst (motive := fun x => x ≠ 0) coinPredict_fair_heads_mass.symm
        (div_ne_zero one_ne_zero two_ne_zero_rat)
  | tails =>
      exact Eq.subst (motive := fun x => x ≠ 0) coinPredict_fair_tails_mass.symm
        (div_ne_zero one_ne_zero two_ne_zero_rat)

-- Reference: ticket #163 toy — `massAllows_eq_true` ties the Bool shadow to
-- the Prop (`Allowed`).
/-- The fair coin allows every coin outcome (Bool shadow). -/
theorem massAllows_coin_fair (c : Coin) : massAllows coinMass CoinHyp.fair c = true :=
  (massAllows_eq_true coinMass CoinHyp.fair c).mpr (coinMass_fair_ne_zero c)

-- Reference: ticket #163 toy — `compatibleBool` is `List.all` of
-- `massAllows` (core `List.all_eq_true`).
/-- The fair coin is compatible with every coin prefix (Bool shadow). -/
theorem compatibleBool_coin_fair (p : List Coin) :
    compatibleBool coinMass CoinHyp.fair p = true :=
  List.all_eq_true.mpr (fun d _ => massAllows_coin_fair d)

-- Reference: ticket #163 toy — `elimLearner_cons_true` (OckhamBound): the
-- fair coin heads `coinHypotheses` and is always compatible, so the
-- elimination learner always outputs it.
/-- **The coin elimination learner always outputs the fair coin**. -/
theorem elimLearner_coin_fair (p : List Coin) :
    elimLearner coinHypotheses coinMass CoinHyp.fair p = CoinHyp.fair :=
  elimLearner_cons_true coinMass CoinHyp.fair p CoinHyp.fair
    [CoinHyp.biased, CoinHyp.loaded] (compatibleBool_coin_fair p)

-- Reference: ticket #163 toy — the lock at level 0: every prefix output is
-- the fair coin (`elimLearner_coin_fair`), so all outputs agree.
/-- **The coin elimination learner locks at level 0** on the coin schedule:
its output on every prefix is the fair coin. -/
theorem coin_elim_locks_zero :
    IsLockingPrefix (elimLearner coinHypotheses coinMass CoinHyp.fair) coinStream 0 := by
  intro i j _ _ _
  exact (elimLearner_coin_fair (coinStream.take i)).trans
    (elimLearner_coin_fair (coinStream.take j)).symm

-- Reference: ticket #163 item (d), CORRECTION (recorded finding): the claim
-- "locks at some level `n ≤ |hs|`" is FALSE in general — the `|hs|` bound
-- (`elimLearner_mindChanges_le`) counts mind CHANGES, not the locking level.
-- Toy witness: hs = [loaded, fair] on s = [heads, heads, tails] has one mind
-- change at index 2 (loaded eliminated by tails), so every locking level is
-- 3 > 2 = |hs|. Computation steps: `elimLearner_cons_true`/`elimLearner_cons_false`
-- + the flags above; `CoinHyp.noConfusion` separates the outputs.
/-- **NEGATIVE RESULT**: on the coin toy `[loaded, fair]` on
`[heads, heads, tails]`, no level `n ≤ 2 = |hs|` locks the elimination
learner (its only mind change is at index 2, so the locking level is 3). -/
theorem not_locking_le_card_coin_witness :
    ¬ ∃ n : ℕ, n ≤ 2 ∧
      IsLockingPrefix (elimLearner [CoinHyp.loaded, CoinHyp.fair] coinMass CoinHyp.fair)
        [Coin.heads, Coin.heads, Coin.tails] n := by
  intro hw
  obtain ⟨n, hn, hlock⟩ := hw
  have h23 : (2:ℕ) ≤ 3 := Nat.le_succ 2
  have h33 : (3:ℕ) ≤ ([Coin.heads, Coin.heads, Coin.tails] : List Coin).length := Nat.le_refl 3
  have hch := hlock 2 3 hn h23 h33
  have e2 : elimLearner [CoinHyp.loaded, CoinHyp.fair] coinMass CoinHyp.fair
      ([Coin.heads, Coin.heads, Coin.tails].take 2) = CoinHyp.loaded :=
    elimLearner_cons_true coinMass CoinHyp.fair _ CoinHyp.loaded [CoinHyp.fair]
      compatibleBool_coin_loaded_hh
  have e3 : elimLearner [CoinHyp.loaded, CoinHyp.fair] coinMass CoinHyp.fair
      ([Coin.heads, Coin.heads, Coin.tails].take 3) = CoinHyp.fair :=
    (elimLearner_cons_false coinMass CoinHyp.fair _ CoinHyp.loaded [CoinHyp.fair]
        compatibleBool_coin_loaded_hht).trans
      (elimLearner_cons_true coinMass CoinHyp.fair _ CoinHyp.fair [] (compatibleBool_coin_fair _))
  exact CoinHyp.noConfusion (e2.symm.trans (hch.trans e3))

-- Reference: ticket #163, acceptance — `#eval` prints the locking witness:
-- the outputs on all prefixes and the level ledger (cf. #43's
-- `coinLevelLedger`, all zeros).
#eval (List.range 3).map fun j =>
  (j, elimLearner coinHypotheses coinMass CoinHyp.fair (coinStream.take j))
#eval (List.range 4).map fun n =>
  (n, mindChangesAtLevel (elimLearner coinHypotheses coinMass CoinHyp.fair) coinStream n)

end BoringLab
