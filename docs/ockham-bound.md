# Ockham mind-change bounds — ticket #285 (repair of #32 item (c), EPI.3.2)

Module: `BoringLab/Epistemology/OckhamBound.lean` (imports
`BoringLab.Epistemology.Ockham`).

## Finding 1: `ockham_min_changes_toy` is false as stated

The sorry'd statement in `Ockham.lean` claims the Ockham learner's mind-change
count on each declared schedule is `≤` that of **every** learner. Proved
counterexample in `OckhamBound.lean` (`ockham_pointwise_minimality_fails`): on
`[heads, tails]` the Ockham learner makes 1 mind change (`ockham_two_mind_changes`,
proved in Ockham.lean) while the constant learner `fun _ => .alwaysTails` makes 0
(`mindChangesOn_const`). **Repair (#285)**: Kelly's theorem bounds mind changes
among *identifying* learners (or in the limit along compatible streams), not
pointwise over all learners. The sorry in `Ockham.lean` stays untouched; the
human reviewer should restate it with the qualifier (statement change, flagged).

## Finding 2: the true unconditional bound, proved

`elimLearner_mindChanges_le`: `mindChangesOn (elimLearner hs mass default) s ≤
hs.length` for every finite schedule `s`. Proof: compatibility is
prefix-monotone (`compatibleBool_prefix`), so a mind change at prefix length `n`
permanently eliminates the current output (`elimLearner_change_elim`); hence the
outputs at distinct mind-change indices are distinct members of `hs`
(`elimLearner_mem_of_change`, `elimLearner_compatible_of_change`), and the count
follows by `mindChangesOn_le_of_forall` (nodup map into `hs.toFinset`).
`ockhamLearner_mindChanges_le` (same bound for the Ockham learner) is a
TEMPORARY SORRY with a peeling plan: mirror the stability argument with the
min-complexity filter (`natMin_le_left/right` proved as the min-scan monotonicity
base).

## References

* [Gold] E. M. Gold, *Information and Control* 10(5):447–474, 1967.
* [Kelly] K. T. Kelly, *The Logic of Reliable Inquiry*, OUP, 1996; K. T. Kelly,
  *Theoretical Computer Science* 383:270–289, 2007.
* Program register: tickets #31 (EPI.3.1), #32 (EPI.3.2), #285 (this repair).
