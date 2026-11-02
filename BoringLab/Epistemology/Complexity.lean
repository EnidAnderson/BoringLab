/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import BoringLab.Epistemology.SampleComplexity
import BoringLab.Lisp.Sexpr

/-!
# Description-length complexity in the lab's own Lisp

Ticket #168 (EPI.3.4 COMPLEXITYLISP.0), building on #32's Ockham learner
(`ockhamLearner`, `minComplexity`, `BoringLab.Epistemology.OckhamBound`) and
the Lisp lane's S-expression carrier (`Sexpr`, `Sexpr.size`,
`BoringLab.Lisp.Sexpr`).

* hypotheses are S-expressions; the simplicity measure is `Sexpr.size`
  (description length in THIS S-expression formalism — model-relative in
  the Kolmogorov/Solomonoff sense; the relativization is recorded here per
  the anti-crank battery, not hidden);
* toy: two descriptions of the fair coin, `fairDesc` (size 2) and
  `bigFairDesc` (size 3), with identical masses — PROVED that the
  size-Ockham learner picks the smaller description even when it is listed
  second (`ockham_size_picks_smaller`: the min-scan, not the list order,
  decides);
* `ockham_min_changes_size` — named hole: the general mind-change bound for
  the size-Ockham learner (peeling plan below);
* parallels-register row 17 (S-expression size ↔ Popper zero-cell count as
  simplicity measures — both explicit `ℕ`-measures with the min-scan Ockham
  learner).

## References
* [Kolmogorov] A. N. Kolmogorov, "Three approaches to the quantitative
  definition of information", 1965 — REVIEW(citation): pin at review.
* Li–Vitányi, *An Introduction to Kolmogorov Complexity and Its
  Applications*, ch. 2 (description length; relativization to the
  description language) — REVIEW(citation): pin at review.
* [Graham] P. Graham, *ANSI Common Lisp*, ch. 7 (macros; S-expressions) —
  via the Lisp lane. Program register: BoringLab tickets #168 (EPI.3.4),
  #32, #43; Lisp lane (META.0 #68).
-/

namespace BoringLab

/-! ## Hypotheses as S-expressions -/

-- Reference: ticket #168 — program's own toy: two S-expression descriptions
-- of the fair coin, of sizes 2 and 3 (`Sexpr.size`).
/-- The small fair-coin description: `(fair)`, size 2. -/
def fairDesc : Sexpr := .list [.atom "fair"]

-- Reference: ticket #168 — program's own toy.
/-- The big fair-coin description: `(fair fair)`, size 3. -/
def bigFairDesc : Sexpr := .list [.atom "fair", .atom "fair"]

-- Reference: ticket #168 — the mass function reading the description: both
-- descriptions denote the fair coin; anything else has mass `0` (match on
-- the list shape — no `DecidableEq Sexpr` needed).
/-- The **description mass**: both fair-coin descriptions carry the fair
coin's mass; all other S-expressions carry `0`. -/
def descMass : Sexpr → Coin → ℚ
  | .list [.atom "fair"], c => coinMass CoinHyp.fair c
  | .list [.atom "fair", .atom "fair"], c => coinMass CoinHyp.fair c
  | _, c => 0

-- Reference: ticket #168 — computation steps: `Sexpr.size_list`,
-- `List.map_cons`/`List.map_nil`, `Sexpr.size_atom`, `List.sum_cons`/
-- `List.sum_nil`, `add_zero` (`List.sum` is tail-recursive, so it does not
-- reduce definitionally — the equation lemmas are used).
/-- A one-atom list has size `2`. -/
theorem size_list_singleton (a : String) : Sexpr.size (.list [.atom a]) = 2 := by
  have h := Sexpr.size_list [.atom a]
  have e1 : List.map Sexpr.size [.atom a] = [1] :=
    (List.map_cons (f := Sexpr.size) (a := .atom a) (l := [])).trans
      ((congrArg (fun x => x :: List.map Sexpr.size []) (Sexpr.size_atom a)).trans
        (congrArg (fun m => 1 :: m) (List.map_nil (f := Sexpr.size))))
  have e2 : ([1] : List ℕ).sum = 1 :=
    (List.sum_cons (a := 1) (l := [])).trans
      ((congrArg (fun x => 1 + x) List.sum_nil).trans (add_zero 1))
  exact h.trans ((congrArg (fun m => 1 + m.sum) e1).trans
    ((congrArg (fun s => 1 + s) e2).trans rfl))

-- Reference: ticket #168 — as `size_list_singleton`, two atoms.
/-- A two-atom list has size `3`. -/
theorem size_list_pair (a b : String) : Sexpr.size (.list [.atom a, .atom b]) = 3 := by
  have h := Sexpr.size_list [.atom a, .atom b]
  have e1 : List.map Sexpr.size [.atom a, .atom b] = [1, 1] :=
    (List.map_cons (f := Sexpr.size) (a := .atom a) (l := [.atom b])).trans
      ((congrArg (fun x => x :: List.map Sexpr.size [.atom b]) (Sexpr.size_atom a)).trans
        (congrArg (fun m => 1 :: m)
          ((List.map_cons (f := Sexpr.size) (a := .atom b) (l := [])).trans
            ((congrArg (fun x => x :: List.map Sexpr.size []) (Sexpr.size_atom b)).trans
              (congrArg (fun m => 1 :: m) (List.map_nil (f := Sexpr.size)))))))
  have e2 : ([1, 1] : List ℕ).sum = 2 :=
    (List.sum_cons (a := 1) (l := [1])).trans
      ((congrArg (fun x => 1 + x)
        ((List.sum_cons (a := 1) (l := [])).trans
          ((congrArg (fun x => 1 + x) List.sum_nil).trans (add_zero 1)))).trans rfl)
  exact h.trans ((congrArg (fun m => 1 + m.sum) e1).trans
    ((congrArg (fun s => 1 + s) e2).trans rfl))

-- Reference: ticket #168 — `size_list_singleton`.
/-- The small description has size `2`. -/
theorem size_fairDesc : fairDesc.size = 2 := size_list_singleton "fair"

-- Reference: ticket #168 — `size_list_pair`.
/-- The big description has size `3`. -/
theorem size_bigFairDesc : bigFairDesc.size = 3 := size_list_pair "fair" "fair"

-- Reference: ticket #168 — `descMass fairDesc c` reduces to
-- `coinMass CoinHyp.fair c` (match iota), so #163's `massAllows_coin_fair`
-- applies by definitional equality.
/-- Both descriptions allow every coin outcome (Bool shadow). -/
theorem massAllows_desc_fair (c : Coin) : massAllows descMass fairDesc c = true :=
  massAllows_coin_fair c

-- Reference: ticket #168 — as `massAllows_desc_fair`.
/-- The big description also allows every coin outcome. -/
theorem massAllows_desc_bigFair (c : Coin) : massAllows descMass bigFairDesc c = true :=
  massAllows_coin_fair c

-- Reference: ticket #168 — `List.all_eq_true` + the two flags above.
/-- Both descriptions are compatible with every coin prefix. -/
theorem compatibleBool_desc_fair (p : List Coin) :
    compatibleBool descMass fairDesc p = true :=
  List.all_eq_true.mpr (fun d _ => massAllows_desc_fair d)

-- Reference: ticket #168 — as `compatibleBool_desc_fair`.
/-- The big description is compatible with every coin prefix. -/
theorem compatibleBool_desc_bigFair (p : List Coin) :
    compatibleBool descMass bigFairDesc p = true :=
  List.all_eq_true.mpr (fun d _ => massAllows_desc_bigFair d)

/-! ## Toy: the size-Ockham learner picks the smaller description -/

-- Reference: ticket #168 toy — PROVED: with `bigFairDesc` listed FIRST, the
-- size-Ockham learner still outputs `fairDesc` — the min-scan decides, not
-- the list order. Steps: both descriptions always compatible
-- (`compatibleBool_desc_bigFair`/`_fair`), so cands = the full list
-- (`List.filter_cons` ×2); min = natMin 3 2 = 2 (`minComplexity_cons_cons`,
-- `minComplexity_singleton`, `size_*`, `Nat.not_le_of_gt`); the head does
-- not attain the min (`filter_tail_of_head_not_min`), the tail's min-filter
-- heads with `fairDesc` (`List.filter_cons` + `ite_eq_left`); `ockhamLearner_cons`.
/-- **The size-Ockham learner picks the smaller description** even when the
bigger one is listed first. -/
theorem ockham_size_picks_smaller (p : List Coin) :
    ockhamLearner [bigFairDesc, fairDesc] descMass Sexpr.size fairDesc p = fairDesc := by
  have hcands : ([bigFairDesc, fairDesc] : List Sexpr).filter
      (fun h => compatibleBool descMass h p) = [bigFairDesc, fairDesc] :=
    List.filter_eq_self.mpr (fun h hm => by
      rcases List.mem_cons.mp hm with he | he'
      · subst he; exact compatibleBool_desc_bigFair p
      · rcases List.mem_cons.mp he' with he | hn
        · subst he; exact compatibleBool_desc_fair p
        · exact absurd hn List.not_mem_nil)
  have hmin : minComplexity Sexpr.size ([bigFairDesc, fairDesc] : List Sexpr) = 2 :=
    (minComplexity_cons_cons Sexpr.size bigFairDesc fairDesc []).trans
      ((congrArg (fun x => natMin x (minComplexity Sexpr.size [fairDesc]))
          size_bigFairDesc).trans
        ((congrArg (natMin 3) (minComplexity_singleton Sexpr.size fairDesc)).trans
          ((congrArg (natMin 3) size_fairDesc).trans
            (by
              unfold natMin
              exact ite_eq_right (Nat.not_le_of_gt (Nat.lt_succ_self 2))))))
  have hnotmin : Sexpr.size bigFairDesc ≠ minComplexity Sexpr.size [bigFairDesc, fairDesc] :=
    fun h => Nat.succ_ne_self 2 (size_bigFairDesc.symm.trans (h.trans hmin))
  have hmin' : minComplexity Sexpr.size [bigFairDesc, fairDesc]
      = minComplexity Sexpr.size [fairDesc] :=
    hmin.trans ((minComplexity_singleton Sexpr.size fairDesc).trans size_fairDesc).symm
  have hfilt : (([bigFairDesc, fairDesc] : List Sexpr).filter
      (fun h => compatibleBool descMass h p)).filter
      (fun h => if Sexpr.size h = minComplexity Sexpr.size
          (([bigFairDesc, fairDesc] : List Sexpr).filter (fun h => compatibleBool descMass h p))
        then true else false)
      = ([fairDesc] : List Sexpr).filter
        (fun h => if Sexpr.size h = minComplexity Sexpr.size [fairDesc]
          then true else false) :=
    filter_tail_of_head_not_min Sexpr.size bigFairDesc [fairDesc] hcands
      (Eq.subst (motive := fun l => Sexpr.size bigFairDesc ≠ minComplexity Sexpr.size l)
        hcands.symm hnotmin)
      (Eq.subst (motive := fun l => minComplexity Sexpr.size l
          = minComplexity Sexpr.size [fairDesc]) hcands.symm hmin')
  have hcond : (if Sexpr.size fairDesc = minComplexity Sexpr.size [fairDesc]
      then true else false) = true :=
    ite_eq_left (minComplexity_singleton Sexpr.size fairDesc).symm
  have hfilt2 : (([bigFairDesc, fairDesc] : List Sexpr).filter
      (fun h => compatibleBool descMass h p)).filter
      (fun h => if Sexpr.size h = minComplexity Sexpr.size
          (([bigFairDesc, fairDesc] : List Sexpr).filter (fun h => compatibleBool descMass h p))
        then true else false)
      = fairDesc :: [] := by
    have htail : ([fairDesc] : List Sexpr).filter
        (fun h => if Sexpr.size h = minComplexity Sexpr.size [fairDesc]
          then true else false) = [fairDesc] :=
      List.filter_eq_self.mpr (fun h hm => by
        rcases List.mem_cons.mp hm with he | hn
        · subst he; exact hcond
        · exact absurd hn List.not_mem_nil)
    exact hfilt.trans htail
  exact ockhamLearner_cons [bigFairDesc, fairDesc] descMass Sexpr.size fairDesc p fairDesc []
    hfilt2


/-! ## The general mind-change bound (named hole) -/

-- Reference: ticket #168 — the general bound.
-- TEMPORARY SORRY: the honest proof has not been instantiated yet.
-- PEELING PLAN: the size-Ockham learner changes its mind only when the
-- current min-size compatible hypothesis is eliminated
-- (`elimLearner_change_elim`-shape for `ockhamLearner`: `ockhamLearner_change_elim`,
-- OckhamBound); each change strictly decreases the min complexity over the
-- surviving candidates (`minComplexity_le_of_sublist`), a `ℕ`-valued
-- quantity — so the number of mind changes is bounded by the initial min
-- complexity. Next named lemmas: `ockham_minComplexity_decreases`,
-- `ockham_min_changes_le_minComplexity`.
/-- **The size-Ockham learner's mind changes are bounded by the initial min
complexity** (named hole). -/
theorem ockham_min_changes_size {datum : Type} [DecidableEq Sexpr]
    (hs : List Sexpr) (mass : Sexpr → datum → ℚ) (default : Sexpr) (s : List datum) :
    mindChangesOn (ockhamLearner hs mass Sexpr.size default) s
      ≤ minComplexity Sexpr.size hs := by
  sorry

-- Reference: ticket #168, acceptance — `#eval` prints the description sizes
-- and the size-Ockham learner's outputs on the coin schedule prefixes.
#eval [bigFairDesc, fairDesc].map Sexpr.size
#eval (List.range 3).map fun n =>
  (n, ockhamLearner [bigFairDesc, fairDesc] descMass Sexpr.size fairDesc (coinStream.take n))

end BoringLab
