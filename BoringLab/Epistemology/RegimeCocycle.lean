/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import BoringLab.Epistemology.Regime

/-!
# The full regime-map cocycle: associativity of composition, proved

Ticket #64 (EPI.8.6), completing the named hole `RegimeMap.comp_law_assoc`
in `BoringLab.Epistemology.Regime` (kept there as the declared hole; the
proof lands here as `RegimeMap.comp_law_assoc_full`):

* the peeled computation lemmas for the composite's data and remainder maps
  (`RegimeMap.comp_dataMap_rfl`, `RegimeMap.comp_remainderMap_rfl`);
* `RegimeMap.ext'` — structure extensionality for regime maps (level maps
  equal as functions; data/transfer pointwise; remainder up to the
  level-map transport; the `law` field is a `Prop`, closed by proof
  irrelevance);
* `RegimeMap.comp_law_assoc_full` — **the full cocycle law proved**: the two
  triple compositions of regime maps agree, the data fields by the peeled
  computation lemmas and the transfer terms by the additive cocycle
  (`RegimeMap.comp_assoc_transferTerm`).

## References
* [Mac Lane] S. Mac Lane, *Categories for the Working Mathematician*, 2nd
  ed., Springer, 1998, ch. I, §4 (associativity of composition; funext).
* Program register: BoringLab ticket #64 (EPI.8.6).
-/

namespace BoringLab

-- Reference: computation steps of `RegimeMap.comp`; `rfl` only in these
-- primitive definitional lemmas.
/-- The composite's data map is the composed data map. -/
theorem RegimeMap.comp_dataMap_rfl {α : Type} (M : AddCarrier) {R S T : Regime α}
    (f : RegimeMap α M R S) (g : RegimeMap α M S T) (n : ℕ) (l : List α) :
    (f.comp M g).dataMap n l = g.dataMap (f.levelMap n) (f.dataMap n l) := rfl

-- Reference: computation step of `RegimeMap.comp` (remainder part).
/-- The composite's remainder map is the composed remainder map. -/
theorem RegimeMap.comp_remainderMap_rfl {α : Type} (M : AddCarrier) {R S T : Regime α}
    (f : RegimeMap α M R S) (g : RegimeMap α M S T) (n : ℕ)
    (r : (R.trunc n).remainderCarrier) :
    (f.comp M g).remainderMap n r =
      g.remainderMap (f.levelMap n) (f.remainderMap n r) := rfl

-- Reference: structure extensionality for `RegimeMap` (named extensionality
-- lemma; `ext` is not used): the `law` field is a `Prop`, so proof
-- irrelevance closes the final step.
/-- Two regime maps whose level maps agree as functions, whose data and
transfer maps agree pointwise, and whose remainder maps agree after the
level-map transport, are equal. -/
theorem RegimeMap.ext' {α : Type} {M : AddCarrier} {R S : Regime α}
    {f g : RegimeMap α M R S}
    (hl : f.levelMap = g.levelMap)
    (hd : ∀ n l, f.dataMap n l = g.dataMap n l)
    (hr : ∀ n (r : (R.trunc n).remainderCarrier),
      cast (congrArg (fun m => (S.trunc m).remainderCarrier) (congrFun hl n))
        (f.remainderMap n r) = g.remainderMap n r)
    (ht : ∀ n, f.transferTerm n = g.transferTerm n) : f = g := by
  revert hl hd hr ht
  cases f with
  | mk fl fd fr ft fLaw =>
  cases g with
  | mk gl gd gr gt gLaw =>
  intro hl hd hr ht
  have e1 : fl = gl := hl
  subst e1
  have e2 : fd = gd := funext fun n => funext (hd n)
  subst e2
  have e3 : fr = gr := funext fun n => funext fun r => hr n r
  subst e3
  have e4 : ft = gt := funext ht
  subst e4
  rfl

-- Reference: ticket #64 — the full cocycle law, PROVED here: the two triple
-- compositions agree (data fields by the peeled computation lemmas, the
-- transfer terms by the additive cocycle `comp_assoc_transferTerm`).
/-- **The full cocycle law**: regime-map composition is associative. -/
theorem RegimeMap.comp_law_assoc_full {α : Type} (M : AddCarrier)
    {R S T U : Regime α} (f : RegimeMap α M R S) (g : RegimeMap α M S T)
    (h : RegimeMap α M T U) :
    (f.comp M g).comp M h = f.comp M (g.comp M h) := by
  refine RegimeMap.ext' ?hl ?hd ?hr ?ht
  · exact funext fun n => RegimeMap.comp_levelMap M (f.comp M g) h n
  · intro n l
    exact RegimeMap.comp_dataMap_rfl M (f.comp M g) h n l
  · intro n r
    exact RegimeMap.comp_remainderMap_rfl M (f.comp M g) h n r
  · intro n
    exact RegimeMap.comp_assoc_transferTerm M f g h n

end BoringLab
