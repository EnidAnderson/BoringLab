/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import BoringLab.Epistemology.MotivicInformation

/-!
# MI.0.3 row (c): the vanishing statements ARE the falsifiability predicate

The reflexive-closure row (c) of ticket #65, as a proved
satisfaction statement about data (never a world-claim): on the coin
family, `coinMI.vanishing h` (the tails cell vanishes — MI.0.1's empirical
claim class, ticket #67) coincides with #28's Popper predicate
`Experiment.falsifiableHyp coinExperiment h` — proved by cases on `h`
with the landed mass lemmas (`coinPredict_*_mass`, `fair_not_falsifiable`,
`loaded_falsifiable`, `coinPredict_loaded_heads_mass`).

## References
* [Popper] K. R. Popper, *The Logic of Scientific Discovery*, 1959, ch. IV
  (falsifiability).
* Program register: BoringLab tickets #28 (EPI.1.1), #65 (MI.0.3, row (c)),
  #67 (MI.0.1).
-/

namespace BoringLab

-- Reference: ticket #65, row (c) — proved by cases on `h`; the mass lemmas
-- of #28 + `coinPredict_loaded_heads_mass` (#36) + `div_ne_zero`/
-- `one_ne_zero` for the nonzero cells.
/-- On the coin family, the vanishing statement (zero tails mass) coincides
with Popper falsifiability (proved). -/
theorem coinMI_vanishing_iff_falsifiable (h : CoinHyp) :
    coinMI.vanishing h ↔ Experiment.falsifiableHyp coinExperiment h = true := by
  cases h with
  | fair =>
      have hne : (1/2 : ℚ) ≠ 0 :=
        div_ne_zero one_ne_zero (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero 1))
      refine Iff.intro ?_ ?_
      · intro hv
        exact (hne (coinPredict_fair_tails_mass.symm.trans hv)).elim
      · intro hf
        exact (Bool.false_ne_true (fair_not_falsifiable.symm.trans hf)).elim
  | biased =>
      have hne : (1/3 : ℚ) ≠ 0 :=
        div_ne_zero one_ne_zero (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero 2))
      refine Iff.intro ?_ ?_
      · intro hv
        exact (hne (coinPredict_biased_tails_mass.symm.trans hv)).elim
      · intro hf
        exact (Bool.false_ne_true (biased_not_falsifiable.symm.trans hf)).elim
  | loaded =>
      refine Iff.intro ?_ ?_
      · intro hv
        exact (Experiment.falsifiableHyp_eq_true coinExperiment CoinHyp.loaded).mpr
          ⟨Coin.tails, List.mem_cons_of_mem Coin.heads List.mem_cons_self, hv⟩
      · intro hf
        obtain ⟨o, ho, hm⟩ := (Experiment.falsifiableHyp_eq_true coinExperiment
          CoinHyp.loaded).mp hf
        rcases List.mem_cons.mp ho with hok | hot
        · have h1 : tableMass (coinPredict CoinHyp.loaded) o = 1 :=
            Eq.subst (motive := fun x => tableMass (coinPredict CoinHyp.loaded) x = 1)
              hok.symm coinPredict_loaded_heads_mass
          exact (one_ne_zero (h1.symm.trans hm)).elim
        · rcases List.mem_cons.mp hot with hot' | hn
          · exact Eq.subst (motive := fun x => tableMass (coinPredict CoinHyp.loaded) x = 0)
              hot' hm
          · exact absurd hn List.not_mem_nil

end BoringLab
