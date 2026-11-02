/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import BoringLab.QGRequirements.LQG
import BoringLab.QGRequirements.StringTheory
import BoringLab.Doctrine.Gysin
import BoringMath.AlgebraicGeometry.AlgebraicCycle.Trace
import BoringMath.Physics.LQG.PunctureCycle
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Nat.Prime.Defs

/-!
# MI.0.2: the motivic bridge, row by row — physics ledgers ↔ the Gysin doctrine (#66)

The Gysin lane (`BoringLab/Doctrine/Gysin.lean`, commit 4ebb51a) landed the
cycle-level anchor of the computad↔motives identification: on the scheme
computad, a **declared move** between parallel paths is agreement of the Gysin
pushforwards on every cycle, and moves compose (`gysinMove_comp`, riding
`AlgebraicCycle.pushforward_comp`, Fulton ch. 1). This module is the bridge
from the physics ledgers (LQG.1.1 #27, STR.1.1 #26) to that lane:

* `gysinMove_info_invariant` — **the hook theorem**: any information measure
  that factors through algebraic cycles is invariant under Gysin moves;
* bridge demands (QG.0.1 shape) pairing each physics invariance law with its
  cycle-level counterpart — relabeling (LQG diffeomorphism invariance, string
  background independence) as move composition, the holographic equation as
  info-invariance along the hologram — graded in a ledger.

## References
* Program register: BoringLab ticket #66 (MI.0.2, the conditional bridge row
  by row); Gysin lane 4ebb51a; QG.0.1 #23; ledgers #26/#27.
* [Fulton] ch. 1 (pushforward functoriality); [MVW] Appendix 1A;
  [Mimram] Definitions 3.1/3.5.
-/

namespace BoringLab

open BoringMath
open AlgebraicGeometry
open CategoryTheory

-- Reference: [Fulton] ch. 1 + [Mimram] Def. 3.5 — THE HOOK: an information
-- measure factoring through cycles is constant on Gysin-move classes.
/-- **Info through cycles is Gysin-invariant**: if `p ~ q` is a Gysin move,
any `F` on cycles satisfies `F (p_* D) = F (q_* D)`. -/
theorem gysinMove_info_invariant {X Y : SchemeObj.{0}}
    {p q : Computad.Path SchemeComputad.{0} X Y} (h : gysinMove p q)
    (hp : QuasiCompact (pathMorphism p)) (hq : QuasiCompact (pathMorphism q))
    (F : AlgebraicCycle Y.scheme ℤ → ℕ) (D : AlgebraicCycle X.scheme ℤ) :
    F (@AlgebraicCycle.pushforward _ _ (pathMorphism p) hp D) =
      F (@AlgebraicCycle.pushforward _ _ (pathMorphism q) hq D) :=
  congrArg F (h hp hq D)

-- Reference: [Fulton] ch. 1 §1.4 — the trace formula `degree_pushforward`
-- (BoringMath `AlgebraicCycle/Trace.lean`): the degree of a pushforward is
-- the degree along the composite. Combined with the move equality
-- `p_* D = q_* D`, this gives: **Gysin moves preserve the degree along any
-- outgoing morphism**.
/-- **Gysin moves preserve the degree (trace)**: if `p ~ q` is a Gysin move,
the degrees of `D` along `p ≫ r` and along `q ≫ r` agree. -/
theorem gysinMove_degree_trace {X Y : SchemeObj.{0}}
    {p q : Computad.Path SchemeComputad.{0} X Y} (h : gysinMove p q)
    (hp : QuasiCompact (pathMorphism p)) (hq : QuasiCompact (pathMorphism q))
    {Z : Scheme.{0}} (r : Y.scheme ⟶ Z) (D : AlgebraicCycle X.scheme ℤ)
    (s : Finset X.scheme) (t : Finset Y.scheme) (hs : D.support ⊆ ↑s)
    (htp : (pathMorphism p).base '' D.support ⊆ ↑t)
    (htq : (pathMorphism q).base '' D.support ⊆ ↑t) :
    AlgebraicCycle.degree (pathMorphism p ≫ r) D s hs
      = AlgebraicCycle.degree (pathMorphism q ≫ r) D s hs := by
  have hPQ : @AlgebraicCycle.pushforward _ _ (pathMorphism p) hp D
      = @AlgebraicCycle.pushforward _ _ (pathMorphism q) hq D := h hp hq D
  have e1 := AlgebraicCycle.degree_pushforward (pathMorphism p) r D s t hs htp
  have e2 := AlgebraicCycle.degree_pushforward (pathMorphism q) r D s t hs htq
  have mid : AlgebraicCycle.degree r (@AlgebraicCycle.pushforward _ _ (pathMorphism p) hp D)
        t (Set.Subset.trans
          (AlgebraicCycle.support_pushforward_subset_image (pathMorphism p) D) htp)
      = AlgebraicCycle.degree r (@AlgebraicCycle.pushforward _ _ (pathMorphism q) hq D)
        t (Set.Subset.trans
          (AlgebraicCycle.support_pushforward_subset_image (pathMorphism q) D) htq) :=
    (Eq.subst (motive := fun c => ∀ w : c.support ⊆ ↑t,
        AlgebraicCycle.degree r (@AlgebraicCycle.pushforward _ _ (pathMorphism p) hp D) t
            (Set.Subset.trans
              (AlgebraicCycle.support_pushforward_subset_image (pathMorphism p) D) htp)
          = AlgebraicCycle.degree r c t w)
      hPQ (fun _ => rfl))
      (Set.Subset.trans
        (AlgebraicCycle.support_pushforward_subset_image (pathMorphism q) D) htq)
  exact Eq.trans e1.symm (Eq.trans mid e2)

-- Reference: #66 — bridge row 1: Gysin-move info-invariance (the hook).
/-- **Bridge statement (hook)**: cycle-factoring info is Gysin-invariant. -/
def bridgeGysinInfoStatement : Prop :=
  ∀ {X Y : SchemeObj.{0}} {p q : Computad.Path SchemeComputad.{0} X Y},
    gysinMove p q →
    ∀ (hp : QuasiCompact (pathMorphism p)) (hq : QuasiCompact (pathMorphism q))
      (F : AlgebraicCycle Y.scheme ℤ → ℕ) (D : AlgebraicCycle X.scheme ℤ),
      F (@AlgebraicCycle.pushforward _ _ (pathMorphism p) hp D) =
        F (@AlgebraicCycle.pushforward _ _ (pathMorphism q) hq D)

-- Reference: #66 — the demand as a typed carrier.
/-- The **Gysin info-invariance bridge demand**. -/
def bridgeGysinInfoDemand : Demand QGFramework where
  statement := bridgeGysinInfoStatement
  witness := PLift bridgeGysinInfoStatement

-- Reference: 4ebb51a — certified by `gysinMove_info_invariant`.
/-- The Gysin info-invariance row is **satisfied**. -/
theorem bridgeGysinInfoDemand_satisfied : Satisfied bridgeGysinInfoDemand :=
  ⟨PLift.up (fun h hp hq F D => gysinMove_info_invariant h hp hq F D)⟩

-- Reference: #66 — bridge row 2: moves compose on the scheme computad
-- (the rewriting axiom) AND on the LQG graph side (relabeling transitivity).
/-- **Bridge statement (moves compose)**: Gysin moves compose along paths. -/
def bridgeMovesComposeStatement : Prop :=
  ∀ {X Y Z : SchemeObj.{0}} {p p' : Computad.Path SchemeComputad.{0} X Y}
    {q q' : Computad.Path SchemeComputad.{0} Y Z}
    (_hp : QuasiCompact (pathMorphism p)) (_hp' : QuasiCompact (pathMorphism p'))
    (_hq : QuasiCompact (pathMorphism q)) (_hq' : QuasiCompact (pathMorphism q')),
    gysinMove p p' → gysinMove q q' → gysinMove (p.comp q) (p'.comp q')

-- Reference: #66 — the demand as a typed carrier.
/-- The **moves-compose bridge demand** (scheme side). -/
def bridgeMovesComposeDemand : Demand QGFramework where
  statement := bridgeMovesComposeStatement
  witness := PLift bridgeMovesComposeStatement

-- Reference: 4ebb51a — certified by `gysinMove_comp`.
/-- The moves-compose row (scheme side) is **satisfied**. -/
theorem bridgeMovesComposeDemand_satisfied : Satisfied bridgeMovesComposeDemand :=
  ⟨PLift.up (fun _hp _hp' _hq _hq' h h' => gysinMove_comp _hp _hp' _hq _hq' h h')⟩

-- Reference: #66 — bridge row 3: LQG relabeling transitivity is the
-- move-composition law on the graph side (diffeomorphism invariance).
/-- **Bridge statement (LQG moves compose)**: relabelings compose. -/
def bridgeLQGRelabelStatement : Prop :=
  ∀ {ιv ιe ιw : Type} [DecidableEq ιv] [DecidableEq ιe]
    {g g' g'' : ColoredGraph ιv ιe ιw},
    ColoredGraph.Relabeling g g' → ColoredGraph.Relabeling g' g'' →
      ColoredGraph.Relabeling g g''

-- Reference: #66 — the demand as a typed carrier.
/-- The **LQG relabeling bridge demand** (move composition, graph side). -/
def bridgeLQGRelabelDemand : Demand QGFramework where
  statement := bridgeLQGRelabelStatement
  witness := PLift bridgeLQGRelabelStatement

-- Reference: #352 items 3–6 — certified by `ColoredGraph.relabeling_trans`.
/-- The LQG relabeling row is **satisfied**. -/
theorem bridgeLQGRelabelDemand_satisfied : Satisfied bridgeLQGRelabelDemand :=
  ⟨PLift.up (fun h h' => ColoredGraph.relabeling_trans h h')⟩

-- Reference: #66 — bridge row 4: string background independence is the
-- move-composition/invariance law on the worldsheet lattice side.
/-- **Bridge statement (STR background independence)**: the lattice Polyakov
action is relabeling-invariant. -/
def bridgeSTRBackgroundStatement : Prop :=
  ∀ (T : ℝ) {ιv : Type} [DecidableEq ιv] (ws : LatticeWorldsheet ιv)
    (e : ιv ≃ ιv) (X : ιv → ℝ),
    polyakovAction T (ws.relabel e) (fun v => X (e.symm v)) = polyakovAction T ws X

-- Reference: #66 — the demand as a typed carrier.
/-- The **string background-independence bridge demand**. -/
def bridgeSTRBackgroundDemand : Demand QGFramework where
  statement := bridgeSTRBackgroundStatement
  witness := PLift bridgeSTRBackgroundStatement

-- Reference: #366 item 3 — certified by `polyakovAction_relabel`.
/-- The string background-independence row is **satisfied**. -/
theorem bridgeSTRBackgroundDemand_satisfied : Satisfied bridgeSTRBackgroundDemand :=
  ⟨PLift.up (fun T {ιv} [DecidableEq ιv] ws e X => polyakovAction_relabel T ws e X)⟩

-- Reference: #66 — bridge row 5: the holographic equation is info-invariance
-- along the hologram (the MHI shadow of move-invariance of info).
/-- **Bridge statement (holographic equation)**: on the holographic toy, the
boundary records exactly the bulk's information. -/
def bridgeHolographicEqStatement : Prop :=
  ∀ (B ι : Type) (k : ℕ) (enc : B → (ι → Fin k)) (x : Discrete B),
    (Discrete.functor (fun b => Discrete.mk (enc b))).obj x =
      Discrete.mk (enc x.as)

-- Reference: #66 — the demand as a typed carrier.
/-- The **holographic-equation bridge demand**. -/
def bridgeHolographicEqDemand : Demand QGFramework where
  statement := bridgeHolographicEqStatement
  witness := PLift bridgeHolographicEqStatement

-- Reference: #356/#366 — certified by `rfl` (the MHI law field of the toy).
/-- The holographic-equation row is **satisfied**. -/
theorem bridgeHolographicEqDemand_satisfied : Satisfied bridgeHolographicEqDemand :=
  ⟨PLift.up (fun _ _ _ _ _ => rfl)⟩
-- Reference: #66 — bridge row 6 (SATISFIED): Gysin moves preserve the degree
-- (trace) of zero-cycles along any outgoing morphism — proved via the trace
-- formula `degree_pushforward` (BoringMath `AlgebraicCycle/Trace.lean`,
-- [Fulton] ch. 1 §1.4) plus the move equality `p_* D = q_* D`.
/-- **Bridge statement (degree is move-invariant)**: Gysin moves preserve the
degree of `D` along any outgoing morphism. -/
def bridgeDegreeTraceStatement : Prop :=
  ∀ {X Y : SchemeObj.{0}} {p q : Computad.Path SchemeComputad.{0} X Y},
    gysinMove p q →
    ∀ (_hp : QuasiCompact (pathMorphism p)) (_hq : QuasiCompact (pathMorphism q))
      {Z : Scheme.{0}} (r : Y.scheme ⟶ Z) (D : AlgebraicCycle X.scheme ℤ)
      (s : Finset X.scheme) (t : Finset Y.scheme) (hs : D.support ⊆ ↑s)
      (_htp : (pathMorphism p).base '' D.support ⊆ ↑t)
      (_htq : (pathMorphism q).base '' D.support ⊆ ↑t),
      AlgebraicCycle.degree (pathMorphism p ≫ r) D s hs
        = AlgebraicCycle.degree (pathMorphism q ≫ r) D s hs

-- Reference: #66 — the demand as a typed carrier.
/-- The **degree-trace bridge demand**. -/
def bridgeDegreeTraceDemand : Demand QGFramework where
  statement := bridgeDegreeTraceStatement
  witness := PLift bridgeDegreeTraceStatement

-- Reference: Trace lane (`degree_pushforward`) + Gysin lane — certified.
/-- The degree-trace row is **satisfied** (witness: `gysinMove_degree_trace`). -/
theorem bridgeDegreeTraceDemand_satisfied : Satisfied bridgeDegreeTraceDemand :=
  ⟨PLift.up (fun h _hp _hq _ r D s t hs _htp _htq =>
    gysinMove_degree_trace h _hp _hq r D s t hs _htp _htq)⟩

-- Reference: #66 — bridge row 7 (OPEN, ticketed): the LQG area spectrum as a
-- cycle-level statement: every spin network with spin has a cycle model of
-- NONZERO degree (the puncture cycles at the vertices, whose degrees are the
-- area eigenvalues via `degree_single` = r × residueDegree).
/-- **Bridge statement (puncture-degree model, OPEN)**: there is a scheme and
a cycle assignment from spin networks such that every network with positive
total spin has a cycle of nonzero degree. -/
def bridgePunctureDegreeStatement : Prop :=
  ∃ (S : SchemeObj.{0})
    (Φ : ∀ (ι : Type) [DecidableEq ι], SpinNetwork ι → AlgebraicCycle S.scheme ℤ),
    ∀ (ι : Type) [DecidableEq ι] (sn : SpinNetwork ι), 0 < sn.info →
      ∃ (s : Finset S.scheme) (hs : (Φ ι sn).support ⊆ ↑s),
        AlgebraicCycle.degree (𝟙 S.scheme) (Φ ι sn) s hs ≠ 0

-- Reference: #66 — the demand as a typed carrier.
/-- The **puncture-degree bridge demand** (open). -/
def bridgePunctureDegreeDemand : Demand QGFramework where
  statement := bridgePunctureDegreeStatement
  witness := PLift bridgePunctureDegreeStatement

-- FILLED (#369): the puncture-degree model lives in BoringMath
-- `Physics/LQG/PunctureCycle.lean` — over `Spec k` the spin network is one
-- puncture point-cycle carrying the total spin, and `degree_single` +
-- `residueDegree_id` give degree = info. The finer per-edge model (degrees =
-- area eigenvalues) is the named extension.
/-- The puncture-degree row is **satisfied** (witness: `spinNetworkCycle_degree_ne_zero`). -/
theorem bridgePunctureDegreeDemand_satisfied : Satisfied bridgePunctureDegreeDemand := by
  refine ⟨PLift.up ⟨⟨punctureScheme (ZMod 2)⟩,
    fun ι _ sn => spinNetworkCycle (ZMod 2) sn, fun ι _ sn h => ?_⟩⟩
  exact spinNetworkCycle_degree_ne_zero (ZMod 2) sn h

-- Reference: QG.0.1 #23 — the MI.0.2 bridge ledger: seven rows with grades.
/-- The **MI.0.2 bridge demand list** (six satisfied, one pending). -/
def bridgeDemands : List (Demand QGFramework) :=
  [bridgeGysinInfoDemand, bridgeMovesComposeDemand, bridgeLQGRelabelDemand,
    bridgeSTRBackgroundDemand, bridgeHolographicEqDemand, bridgeDegreeTraceDemand,
    bridgePunctureDegreeDemand]

-- Reference: #66 — the bridge ledger grading each row (last is pending #369).
/-- The **MI.0.2 bridge requirements file** over the MHI framework. -/
def bridgeRequirements : Requirements QGFramework where
  demands := bridgeDemands
  ledger := fun d hd => by
    rcases List.mem_cons.mp hd with h | h
    · exact Eq.subst (motive := fun d => DemandStatus.{1} d) h.symm DemandStatus.satisfied
    · rcases List.mem_cons.mp h with h | h
      · exact Eq.subst (motive := fun d => DemandStatus.{1} d) h.symm DemandStatus.satisfied
      · rcases List.mem_cons.mp h with h | h
        · exact Eq.subst (motive := fun d => DemandStatus.{1} d) h.symm DemandStatus.satisfied
        · rcases List.mem_cons.mp h with h | h
          · exact Eq.subst (motive := fun d => DemandStatus.{1} d) h.symm DemandStatus.satisfied
          · rcases List.mem_cons.mp h with h | h
            · exact Eq.subst (motive := fun d => DemandStatus.{1} d) h.symm DemandStatus.satisfied
            · rcases List.mem_cons.mp h with h | h
              · exact Eq.subst (motive := fun d => DemandStatus.{1} d) h.symm DemandStatus.satisfied
              · exact Eq.subst (motive := fun d => DemandStatus.{1} d)
                  (List.mem_singleton.mp h).symm DemandStatus.satisfied

end BoringLab
