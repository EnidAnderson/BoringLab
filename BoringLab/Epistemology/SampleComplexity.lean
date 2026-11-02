/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import BoringLab.Epistemology.Locking
import BoringLab.Epistemology.Ockham

/-!
# Sample complexity of truncated identification at level n

Ticket #164 (EPI.8.5), building on #43 (`TruncatedIdentification`,
`truncatedIdentification_down`) and #163 (`elimLearner_coin_fair`).

* `WitnessesAtLevel` — a bound `N` witnesses truncated identification of `h`
  at level `n` (the unpacked clause of #43's `TruncatedIdentification`);
* `witness_down` — PROVED: a witness at level `m` is a witness at every
  `n ≤ m` (`Nat.le_trans`; cf. #43's `truncatedIdentification_down`);
* `witness_vacuous_above_level` — PROVED (recorded quirk): for `n < N` every
  learner "witnesses" vacuously, since no prefix has `N ≤ length ≤ n`;
* `IsLeastSampleComplexity` — the least witness as a `Prop` (no decidability
  baked in, STYLE §2.3);
* `exists_least_sampleComplexity` — named hole (least-number principle; on a
  `Fintype` carrier the explicit enumeration route is the peeling plan);
* toy, PROVED: the coin elimination learner witnesses the fair coin at every
  level with bound `0` (`coin_witness_zero`, `coin_least_sc_zero`);
* toy, NEGATIVE RESULT (first-class per the lab epistemics): no bound
  `N ≤ n` ever witnesses the loaded coin (`elimLearner_not_witness_loaded` —
  the all-heads prefix is compatible with it but the learner outputs fair);
* the Ockham trade-off on the coin family — PROVED (`ockham_sc_le_elim_coin`:
  the Ockham learner's least sample complexity for the fair coin is `0` at
  every level, same as the elimination learner's); `#eval` prints the coin
  family's zero-cell counts (#32's `zeroCellCount`).

## References
* [Gold] E. M. Gold, "Language identification in the limit", *Information
  and Control* 10(5):447–474, 1967.
* [Kelly] K. T. Kelly, *The Logic of Reliable Inquiry*, OUP, 1996 (mind
  changes; sample complexity).
* [Popper] K. R. Popper, *The Logic of Scientific Discovery*, 1959, ch. IV
  (content as refuted cells — #32's `zeroCellCount`).
* Program register: BoringLab tickets #164 (EPI.8.5), #31, #32, #43, #163.
  REVIEW(citation): pin the standard sample-complexity reference (PAC
  learning, Kearns–Vazirani ch. 3) at review.
-/

namespace BoringLab

open scoped List

/-! ## Witnesses of truncated identification -/

-- Reference: ticket #164 item (a) — the unpacked clause of #43's
-- `TruncatedIdentification` at the hypothesis `h`.
/-- A bound `N` **witnesses** truncated identification of `h` at level `n`:
the learner outputs `h` on every compatible prefix of length `≤ n` past
`N`. -/
def WitnessesAtLevel {hyp datum : Type} (M : List datum → hyp)
    (mass : hyp → datum → ℚ) (n : ℕ) (h : hyp) (N : ℕ) : Prop :=
  ∀ p : List datum, Compatible mass h p → p.length ≤ n → N ≤ p.length → M p = h

-- Reference: ticket #164 item (b) — proved: `p.length ≤ n ≤ m` gives
-- `p.length ≤ m` (`Nat.le_trans`), so the same `N` witnesses at level `n`
-- (cf. #43's `truncatedIdentification_down`).
/-- **Witnesses go down in level**: a witness at level `m` witnesses every
level `n ≤ m`. -/
theorem witness_down {hyp datum : Type} (M : List datum → hyp)
    (mass : hyp → datum → ℚ) (h : hyp) {n m N : ℕ} (hnm : n ≤ m)
    (hw : WitnessesAtLevel M mass m h N) : WitnessesAtLevel M mass n h N :=
  fun p hpc hlen hN => hw p hpc (Nat.le_trans hlen hnm) hN

-- Reference: ticket #164 item (b) — recorded quirk, proved: for `n < N` the
-- constraints `N ≤ p.length` and `p.length ≤ n` are contradictory
-- (`Nat.le_trans` + `Nat.lt_of_le_of_lt` + `Nat.lt_irrefl`), so ANY learner
-- witnesses vacuously — the least witness is always `≤ n + 1`.
/-- **Witnesses above the level are vacuous**: for `n < N`, every learner
witnesses at level `n` with bound `N`. -/
theorem witness_vacuous_above_level {hyp datum : Type} (M : List datum → hyp)
    (mass : hyp → datum → ℚ) (n N : ℕ) (h : hyp) (hnN : n < N) :
    WitnessesAtLevel M mass n h N := by
  intro p _ hlen hN
  exact (Nat.lt_irrefl N (Nat.lt_of_le_of_lt (Nat.le_trans hN hlen) hnN)).elim

-- Reference: ticket #164 item (c) — the least witness as a Prop (no
-- decidability baked in, STYLE §2.3).
/-- `N` is the **least sample complexity** of `h` at level `n`: it witnesses,
and every smaller bound fails on some compatible prefix. -/
def IsLeastSampleComplexity {hyp datum : Type} (M : List datum → hyp)
    (mass : hyp → datum → ℚ) (n : ℕ) (h : hyp) (N : ℕ) : Prop :=
  WitnessesAtLevel M mass n h N ∧
    ∀ N' : ℕ, N' < N → ∃ p : List datum, Compatible mass h p ∧ p.length ≤ n ∧
      N' ≤ p.length ∧ M p ≠ h

-- Reference: ticket #164 item (c) — existence of a least witness.
-- TEMPORARY SORRY: needs a least-number principle for the (undecidable in
-- general) witness predicate.
-- PEELING PLAN: classically this is the least-number principle (kept as a
-- hypothesis-carrier, never a global axiom). Constructively, on a
-- `[Fintype datum]` carrier the prefixes of length `≤ n` form an explicit
-- finite list (hand-built enumeration — NOT `Fintype.decidablePiFintype`,
-- which is Classical.choice-tainted at the pin; house no-Choice rule); the
-- predicate becomes decidable over that list and `Nat.find` applies. Next
-- named lemmas: `prefixesUpTo_explicit`, `witnessesAtLevel_decidable_of_fintype`,
-- `least_witness_of_fintype`.
/-- **A least witness exists** when the identification holds (named hole). -/
theorem exists_least_sampleComplexity {hyp datum : Type} (M : List datum → hyp)
    (mass : hyp → datum → ℚ) (n : ℕ) (h : hyp) (hs : List hyp) (hh : h ∈ hs)
    (hid : TruncatedIdentification M mass hs n) :
    ∃ N : ℕ, IsLeastSampleComplexity M mass n h N := by
  sorry

/-! ## Toy: the coin family -/

-- Reference: ticket #164 toy — `elimLearner_coin_fair` (#163): the
-- elimination learner outputs the fair coin on EVERY coin prefix, so bound
-- `0` witnesses at every level (every prefix is compatible with the fair
-- coin, `coinMass_fair_ne_zero`).
/-- **Bound `0` witnesses the fair coin at every level** for the coin
elimination learner. -/
theorem coin_witness_zero (n : ℕ) :
    WitnessesAtLevel (elimLearner coinHypotheses coinMass CoinHyp.fair) coinMass n
      CoinHyp.fair 0 :=
  fun p _ _ _ => elimLearner_coin_fair p

-- Reference: ticket #164 toy — `Nat.not_lt_zero`: no `N' < 0` exists, so `0`
-- is least.
/-- **The least sample complexity of the fair coin is `0` at every level**. -/
theorem coin_least_sc_zero (n : ℕ) :
    IsLeastSampleComplexity (elimLearner coinHypotheses coinMass CoinHyp.fair)
      coinMass n CoinHyp.fair 0 :=
  ⟨coin_witness_zero n, fun N' hN' => absurd hN' (Nat.not_lt_zero N')⟩

-- Reference: ticket #164 toy — the all-heads prefix of length `N` is
-- compatible with the loaded coin (`List.mem_replicate`).
/-- The all-heads prefix of length `N` is compatible with the loaded coin. -/
theorem compatible_loaded_replicate_heads (N : ℕ) :
    Compatible coinMass CoinHyp.loaded (List.replicate N Coin.heads) := by
  intro d hd
  rcases (List.mem_replicate.mp hd) with ⟨_, hd'⟩
  subst hd'
  exact Eq.subst (motive := fun x => x ≠ 0) coinMass_loaded_heads.symm one_ne_zero

-- Reference: ticket #164 toy, NEGATIVE RESULT (first-class per the lab
-- epistemics): `replicate N heads` (length `N ≤ n`) is compatible with the
-- loaded coin, yet the elimination learner outputs the fair coin there
-- (`elimLearner_coin_fair`); `CoinHyp.noConfusion` separates fair from loaded.
/-- **NEGATIVE RESULT**: for `N ≤ n`, no bound `N` witnesses the loaded coin
at level `n` for the coin elimination learner. -/
theorem elimLearner_not_witness_loaded (n N : ℕ) (hNn : N ≤ n) :
    ¬ WitnessesAtLevel (elimLearner coinHypotheses coinMass CoinHyp.fair) coinMass n
      CoinHyp.loaded N := by
  intro hw
  have hlen : (List.replicate N Coin.heads).length ≤ n :=
    Eq.subst (motive := fun k => k ≤ n)
      (List.length_replicate (n := N) (a := Coin.heads)).symm hNn
  have hlenN : N ≤ (List.replicate N Coin.heads).length :=
    Eq.subst (motive := fun k => N ≤ k) (List.length_replicate (n := N) (a := Coin.heads)).symm
      (Nat.le_refl N)
  have h := hw (List.replicate N Coin.heads) (compatible_loaded_replicate_heads N) hlen hlenN
  exact CoinHyp.noConfusion ((elimLearner_coin_fair (List.replicate N Coin.heads)).symm.trans h)

-- Reference: ticket #164 item (d), toy — the fair coin's zero-cell count is
-- `0`: both cells have mass `1/2 ≠ 0` (`coinPredict_fair_heads_mass`/
-- `coinPredict_fair_tails_mass`, `div_ne_zero one_ne_zero two_ne_zero_rat`),
-- `isZeroQ` is `false` on both (`ite_eq_right`), so the filter is empty
-- (`List.filter_cons` ×2 + `List.filter_nil`).
/-- The fair coin's zero-cell count (Popper content, #32) is `0`. -/
theorem zeroCellCount_coin_fair : zeroCellCount coinPredict coinOutcomes CoinHyp.fair = 0 := by
  unfold zeroCellCount coinOutcomes
  have h1 : isZeroQ (tableMass (coinPredict CoinHyp.fair) Coin.heads) = false :=
    Eq.subst (motive := fun q => isZeroQ q = false) coinPredict_fair_heads_mass.symm
      (by
        unfold isZeroQ
        exact ite_eq_right (div_ne_zero one_ne_zero two_ne_zero_rat))
  have h2 : isZeroQ (tableMass (coinPredict CoinHyp.fair) Coin.tails) = false :=
    Eq.subst (motive := fun q => isZeroQ q = false) coinPredict_fair_tails_mass.symm
      (by
        unfold isZeroQ
        exact ite_eq_right (div_ne_zero one_ne_zero two_ne_zero_rat))
  have hf1 : (([Coin.heads, Coin.tails] : List Coin).filter
      fun o => isZeroQ (tableMass (coinPredict CoinHyp.fair) o))
      = ([Coin.tails] : List Coin).filter
        fun o => isZeroQ (tableMass (coinPredict CoinHyp.fair) o) :=
    (List.filter_cons (p := fun o => isZeroQ (tableMass (coinPredict CoinHyp.fair) o))
        (x := Coin.heads) (xs := [Coin.tails])).trans
      (Eq.subst (motive := fun b => (if b then Coin.heads :: ([Coin.tails] : List Coin).filter
            (fun o => isZeroQ (tableMass (coinPredict CoinHyp.fair) o))
          else ([Coin.tails] : List Coin).filter
            (fun o => isZeroQ (tableMass (coinPredict CoinHyp.fair) o)))
          = ([Coin.tails] : List Coin).filter
            (fun o => isZeroQ (tableMass (coinPredict CoinHyp.fair) o)))
        h1.symm rfl)
  have hf2 : (([Coin.tails] : List Coin).filter
      fun o => isZeroQ (tableMass (coinPredict CoinHyp.fair) o))
      = ([] : List Coin).filter
        fun o => isZeroQ (tableMass (coinPredict CoinHyp.fair) o) :=
    (List.filter_cons (p := fun o => isZeroQ (tableMass (coinPredict CoinHyp.fair) o))
        (x := Coin.tails) (xs := [])).trans
      (Eq.subst (motive := fun b => (if b then Coin.tails :: ([] : List Coin).filter
            (fun o => isZeroQ (tableMass (coinPredict CoinHyp.fair) o))
          else ([] : List Coin).filter
            (fun o => isZeroQ (tableMass (coinPredict CoinHyp.fair) o)))
          = ([] : List Coin).filter
            (fun o => isZeroQ (tableMass (coinPredict CoinHyp.fair) o)))
        h2.symm rfl)
  have hf : (([Coin.heads, Coin.tails] : List Coin).filter
      fun o => isZeroQ (tableMass (coinPredict CoinHyp.fair) o)) = [] :=
    hf1.trans (hf2.trans (List.filter_nil
      (p := fun o => isZeroQ (tableMass (coinPredict CoinHyp.fair) o))))
  exact (congrArg List.length hf).trans rfl

-- Reference: ticket #164 item (d), toy — PROVED: the Ockham learner always
-- outputs the fair coin: fair heads the candidate list (`List.filter_cons` +
-- `compatibleBool_coin_fair`), has complexity `0` = the min
-- (`minComplexity_le_of_mem` + `Nat.zero_le` + `Nat.le_antisymm`), so the
-- min-filter heads with fair (`filter_head_of_head_min`, OckhamBound) and
-- `ockhamLearner_cons` closes.
/-- **The coin Ockham learner (zero-cell-count complexity) always outputs the
fair coin**. -/
theorem ockhamLearner_coin_fair (p : List Coin) :
    ockhamLearner coinHypotheses coinMass
        (fun h => zeroCellCount coinPredict coinOutcomes h) CoinHyp.fair p = CoinHyp.fair := by
  have hcands : (coinHypotheses.filter fun h => compatibleBool coinMass h p)
      = CoinHyp.fair :: ([CoinHyp.biased, CoinHyp.loaded].filter
          fun h => compatibleBool coinMass h p) :=
    (List.filter_cons (p := fun h => compatibleBool coinMass h p) (x := CoinHyp.fair)
        (xs := [CoinHyp.biased, CoinHyp.loaded])).trans
      (Eq.subst
        (motive := fun b => (if b
            then CoinHyp.fair :: ([CoinHyp.biased, CoinHyp.loaded].filter
                fun h => compatibleBool coinMass h p)
            else ([CoinHyp.biased, CoinHyp.loaded].filter
                fun h => compatibleBool coinMass h p))
          = CoinHyp.fair :: ([CoinHyp.biased, CoinHyp.loaded].filter
              fun h => compatibleBool coinMass h p))
        (compatibleBool_coin_fair p).symm rfl)
  have hmem : CoinHyp.fair ∈ coinHypotheses.filter (fun h => compatibleBool coinMass h p) :=
    Eq.subst (motive := fun l => CoinHyp.fair ∈ l) hcands.symm (List.mem_cons_self)
  have hle0 : minComplexity (fun h => zeroCellCount coinPredict coinOutcomes h)
      (coinHypotheses.filter fun h => compatibleBool coinMass h p) ≤ 0 :=
    Eq.subst (motive := fun k => minComplexity (fun h => zeroCellCount coinPredict coinOutcomes h)
        (coinHypotheses.filter fun h => compatibleBool coinMass h p) ≤ k)
      zeroCellCount_coin_fair
      (minComplexity_le_of_mem (fun h => zeroCellCount coinPredict coinOutcomes h) hmem)
  have hm0 : minComplexity (fun h => zeroCellCount coinPredict coinOutcomes h)
      (coinHypotheses.filter fun h => compatibleBool coinMass h p) = 0 :=
    Nat.le_antisymm hle0 (Nat.zero_le _)
  have hfilt : ((coinHypotheses.filter fun h => compatibleBool coinMass h p).filter
      fun h => if zeroCellCount coinPredict coinOutcomes h
          = minComplexity (fun h => zeroCellCount coinPredict coinOutcomes h)
            (coinHypotheses.filter fun h => compatibleBool coinMass h p)
        then true else false)
      = CoinHyp.fair :: ([CoinHyp.biased, CoinHyp.loaded].filter
          fun h => compatibleBool coinMass h p).filter
        (fun h => if zeroCellCount coinPredict coinOutcomes h
            = minComplexity (fun h => zeroCellCount coinPredict coinOutcomes h)
              (coinHypotheses.filter fun h => compatibleBool coinMass h p)
          then true else false) :=
    filter_head_of_head_min (fun h => zeroCellCount coinPredict coinOutcomes h) CoinHyp.fair _
      hcands (zeroCellCount_coin_fair.trans hm0.symm)
  exact ockhamLearner_cons coinHypotheses coinMass
    (fun h => zeroCellCount coinPredict coinOutcomes h) CoinHyp.fair p CoinHyp.fair _ hfilt

-- Reference: ticket #164 item (d), toy — PROVED: the Ockham learner's least
-- sample complexity for the fair coin at level `n` is `0`, same as the
-- elimination learner's (`ockhamLearner_coin_fair` + `Nat.not_lt_zero`).
/-- **Ockham trade-off on the coin family** (proved): the Ockham learner's
least sample complexity for the fair coin at level `n` is `0`. -/
theorem ockham_sc_le_elim_coin (n : ℕ) :
    IsLeastSampleComplexity (ockhamLearner coinHypotheses coinMass
        (fun h => zeroCellCount coinPredict coinOutcomes h) CoinHyp.fair) coinMass n
      CoinHyp.fair 0 :=
  ⟨fun p _ _ _ => ockhamLearner_coin_fair p, fun N' hN' => absurd hN' (Nat.not_lt_zero N')⟩

-- Reference: ticket #164, acceptance — `#eval` prints the zero-cell counts
-- (the #32 complexity measure) on the coin family: fair 0, biased 0,
-- loaded 1.
#eval coinHypotheses.map fun h => (h, zeroCellCount coinPredict coinOutcomes h)

end BoringLab
