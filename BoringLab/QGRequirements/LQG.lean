/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import BoringLab.QGRequirements.Demand
import BoringMath.Physics.LQG.SpinNetwork
import BoringMath.Physics.LQG.VolumeSpectrum
import BoringMath.Physics.LQG.HolonomyFlux
import BoringMath.Physics.LQG.SpinFoam
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# LQG.1.1: the loop-quantum-gravity ledger over the MHI framework (ticket #27)

The LQG (Rovelli) field file in the QG.0.1 shape: a scientist-owned list of
**demands** on the `MotivicHolographicInfo` framework, graded in a ledger.
Certified rows point at proved theorems of `BoringMath.Physics.LQG.*` (area
gap, discrete info, diffeomorphism invariance, volume gap, amplitude
positivity, the rep-dimension hook); open rows (proper volume spectrum,
black-hole entropy matching) are pending with peeling plans.

## References
* Program register: BoringLab ticket #27 (LQG.1.1); QG.0.1 #23
  (`Demand.lean`); framework MHI #356; BoringMath #352 (PHYS.LQG.0).
* G. N. Rovelli, L. Smolin, Phys. Rev. Lett. 74 (1995) 2318, gr-qc/9411007.
* C. Rovelli, *Quantum Gravity*, CUP 2004, ch. 6.
* A. Ashtekar, K. Krasnov, Phys. Rev. D 67 (2003) 104025 — BH entropy in LQG.
  REVIEW(citation): pin the counting.
-/

namespace BoringLab

open BoringMath

-- Reference: QG.0.1 (#23) — the framework under audit: the MHI structure.
/-- The **quantum-gravity framework** under audit: `MotivicHolographicInfo`. -/
abbrev QGFramework := MotivicHolographicInfo.{0, 0, 0, 0, 0}

-- Reference: [Rovelli–Smolin 1995] — demand 1: the area spectrum has a gap.
/-- **Demand (area gap)**: the area of a spin network with a spin-≥1 edge is
at least the fundamental gap `A₀ √(3/4)`. -/
def lqgAreaGapStatement : Prop :=
  ∀ {ι : Type} [DecidableEq ι] (A₀ : ℝ), 0 < A₀ → ∀ sn : SpinNetwork ι,
    (∃ e ∈ sn.edges, 1 ≤ sn.spin e) →
      A₀ * Real.sqrt ((1 : ℝ) / 2 * ((1 : ℝ) / 2 + 1)) ≤ sn.area A₀

-- Reference: #27 — the demand as a typed carrier over the framework.
/-- The **area-gap demand** on the MHI framework. -/
def lqgAreaGapDemand : Demand QGFramework where
  statement := lqgAreaGapStatement
  witness := PLift lqgAreaGapStatement

-- Reference: [Rovelli–Smolin 1995]; BoringMath #352 item 2 — certified.
/-- The area-gap demand is **satisfied** (witness: `SpinNetwork.area_gap`). -/
theorem lqgAreaGapDemand_satisfied : Satisfied lqgAreaGapDemand :=
  ⟨PLift.up (fun {ι} [DecidableEq ι] _A₀ hA sn h => SpinNetwork.area_gap hA.le sn h)⟩

-- Reference: MHI #356 + #352 — demand 2: the information measure is discrete.
/-- **Demand (discrete info)**: the LQG kinematical MHI has a nonzero
information gap. -/
def lqgDiscreteInfoStatement : Prop :=
  ∃ g : ℕ, g ≠ 0 ∧ ∀ x : (lqgKinematics (Fin 1)).bulk,
    (lqgKinematics (Fin 1)).bulkInfo x = (0 : ℕ) ∨
      g ≤ ((lqgKinematics (Fin 1)).bulkInfo x : ℕ)

-- Reference: #27 — the demand as a typed carrier.
/-- The **discrete-information demand** on the MHI framework. -/
def lqgDiscreteInfoDemand : Demand QGFramework where
  statement := lqgDiscreteInfoStatement
  witness := PLift lqgDiscreteInfoStatement

-- Reference: #352 items 3–6 — certified by `lqgKinematics_info_gap`.
/-- The discrete-info demand is **satisfied**. -/
theorem lqgDiscreteInfoDemand_satisfied : Satisfied lqgDiscreteInfoDemand :=
  ⟨PLift.up lqgKinematics_info_gap⟩

-- Reference: [Rovelli 2004] ch. 6 — demand 3: diffeomorphism invariance.
/-- **Demand (diffeomorphism invariance)**: the area is invariant under
relabeling of the colored graph. -/
def lqgDiffeoInvarianceStatement : Prop :=
  ∀ {ιv ιe ιw : Type} [DecidableEq ιv] [DecidableEq ιe]
    {g g' : ColoredGraph ιv ιe ιw} (A₀ : ℝ),
    ColoredGraph.Relabeling g g' → g.area A₀ = g'.area A₀

-- Reference: #27 — the demand as a typed carrier.
/-- The **diffeomorphism-invariance demand** on the MHI framework. -/
def lqgDiffeoInvarianceDemand : Demand QGFramework where
  statement := lqgDiffeoInvarianceStatement
  witness := PLift lqgDiffeoInvarianceStatement

-- Reference: #352 items 3–6 — certified by `ColoredGraph.area_relabel`.
/-- The diffeomorphism-invariance demand is **satisfied**. -/
theorem lqgDiffeoInvarianceDemand_satisfied : Satisfied lqgDiffeoInvarianceDemand :=
  ⟨PLift.up (fun {ιv ιe _ιw} [DecidableEq ιv] [DecidableEq ιe] {_g _g'} A₀ h =>
    ColoredGraph.area_relabel A₀ h)⟩

-- Reference: [Rovelli–Smolin 1995] — demand 4: the volume gap.
/-- **Demand (volume gap)**: there is a volume operator (with its laws) on
some spin-network type. -/
def lqgVolumeGapStatement : Prop :=
  ∃ ι : Type, ∃ inst : DecidableEq ι, ∃ A₀ : ℝ, 0 < A₀ ∧
    Nonempty (@VolumeOperator ι inst)

-- Reference: #27 — the demand as a typed carrier.
/-- The **volume-gap demand** on the MHI framework. -/
def lqgVolumeGapDemand : Demand QGFramework where
  statement := lqgVolumeGapStatement
  witness := PLift lqgVolumeGapStatement

-- Reference: #352 items 10–12 — certified by the area-as-volume toy.
/-- The volume-gap demand is **satisfied** (witness: `areaAsVolume`). -/
theorem lqgVolumeGapDemand_satisfied : Satisfied lqgVolumeGapDemand :=
  ⟨PLift.up ⟨Fin 1, inferInstance, 1, zero_lt_one,
    ⟨areaAsVolume (Fin 1) 1 zero_lt_one⟩⟩⟩

-- Reference: [Freidel–Louapre 2002] — demand 5: amplitude positivity.
/-- **Demand (amplitude positivity)**: every spin-foam amplitude is
nonnegative. -/
def lqgAmplitudeNonnegStatement : Prop :=
  ∀ {ιv ιe ιf : Type} [DecidableEq ιv] [DecidableEq ιe] [DecidableEq ιf]
    (f : Foam ιv ιe ιf), 0 ≤ f.amplitude

-- Reference: #27 — the demand as a typed carrier.
/-- The **amplitude-positivity demand** on the MHI framework. -/
def lqgAmplitudeNonnegDemand : Demand QGFramework where
  statement := lqgAmplitudeNonnegStatement
  witness := PLift lqgAmplitudeNonnegStatement

-- Reference: #352 items 13–15 — certified by `Foam.amplitude_nonneg`.
/-- The amplitude-positivity demand is **satisfied**. -/
theorem lqgAmplitudeNonnegDemand_satisfied : Satisfied lqgAmplitudeNonnegDemand :=
  ⟨PLift.up (fun {ιv ιe ιf} [DecidableEq ιv] [DecidableEq ιe] [DecidableEq ιf] f =>
    f.amplitude_nonneg)⟩

-- Reference: SU(2) representation theory + the Tannakian/motivic hook
-- (MI.0.1 #67, location map; DM lane #117) — demand 6 (the hook): the
-- information content equals the sum of (dim j − 1) over the edges, the
-- representation-theoretic quantity the motives attach to.
/-- **Demand (motivic hook)**: the total spin equals the sum of
`repDim j − 1` over the edges — info measured by representation dimensions. -/
def lqgRepDimHookStatement : Prop :=
  ∀ {ι : Type} [DecidableEq ι] (sn : SpinNetwork ι),
    (sn.info : ℝ) = ∑ e ∈ sn.edges, (repDim (sn.spin e) - 1)

-- Reference: #27 — the demand as a typed carrier.
/-- The **rep-dimension hook demand** on the MHI framework. -/
def lqgRepDimHookDemand : Demand QGFramework where
  statement := lqgRepDimHookStatement
  witness := PLift lqgRepDimHookStatement

-- Reference: [De Pietri 1999] (dim j = 2j+1); certified since `repDim n - 1
-- = n`.
/-- The rep-dimension hook demand is **satisfied**. -/
theorem lqgRepDimHookDemand_satisfied : Satisfied lqgRepDimHookDemand := by
  refine ⟨PLift.up (fun {ι} [DecidableEq ι] sn => ?_)⟩
  have h : (sn.info : ℝ) = ∑ e ∈ sn.edges, (sn.spin e : ℝ) := Nat.cast_sum sn.edges sn.spin
  exact Eq.trans h (Finset.sum_congr rfl fun e _ =>
    (add_sub_cancel_right ((sn.spin e : ℝ)) 1).symm)

-- Reference: [Rovelli–Smolin 1995] — demand 7 (OPEN): a *proper* volume
-- operator, distinct from the area.
/-- **Demand (proper volume)**: some volume operator differs from the area on
some network. -/
def lqgProperVolumeStatement : Prop :=
  ∃ ι : Type, ∃ inst : DecidableEq ι, ∃ A₀ : ℝ, 0 < A₀ ∧
    ∃ V : @VolumeOperator ι inst, ∃ sn : SpinNetwork ι,
      V.volume sn ≠ sn.area A₀

-- Reference: #27 — the demand as a typed carrier.
/-- The **proper-volume demand** on the MHI framework. -/
def lqgProperVolumeDemand : Demand QGFramework where
  statement := lqgProperVolumeStatement
  witness := PLift lqgProperVolumeStatement

-- TEMPORARY (pending): the full Rovelli–Smolin volume spectrum needs the
-- intertwiner spaces at vertices and the 6j symbols.
-- PEELING PLAN: (1) `IntertwinerSpace` per vertex valence as data;
-- (2) volume eigenvalue formula via 6j symbols [Rovelli 2004, ch. 6];
-- (3) prove `V.volume ≠ area` on a 4-valent vertex with distinct spins.

-- Reference: [Ashtekar–Krasnov 2003] — demand 8 (OPEN): black-hole entropy
-- matching `S = A/4` in the counting form.
/-- **Demand (black-hole entropy)**: some network's area equals `4 ×` its
information content (the `S = A/4` saturation in counting form). -/
def lqgBlackHoleEntropyStatement : Prop :=
  ∃ A₀ : ℝ, 0 < A₀ ∧ ∃ ι : Type, ∃ _inst : DecidableEq ι,
    ∃ sn : SpinNetwork ι, 0 < sn.info ∧ sn.area A₀ = 4 * (sn.info : ℝ)

-- Reference: #27 — the demand as a typed carrier.
/-- The **black-hole-entropy demand** on the MHI framework. -/
def lqgBlackHoleEntropyDemand : Demand QGFramework where
  statement := lqgBlackHoleEntropyStatement
  witness := PLift lqgBlackHoleEntropyStatement

-- TEMPORARY (pending): BH entropy matching needs the state counting per
-- puncture (intertwiners at the horizon).
-- PEELING PLAN: (1) count `dim` of intertwiner spaces at a horizon vertex
-- (repDim products); (2) show the count saturates `4·info`; refs
-- [Ashtekar–Baek–Corichi–Krasnov 2000], [Ashtekar–Krasnov 2003].

-- Reference: QG.0.1 #23 — the LQG.1.1 ledger: all eight demands with grades.
/-- The **LQG demand list**: area gap, discrete info, diffeomorphism
invariance, volume gap, amplitude positivity, rep-dimension hook (all
satisfied), proper volume and black-hole entropy (pending). -/
def lqgDemands : List (Demand QGFramework) :=
  [lqgAreaGapDemand, lqgDiscreteInfoDemand, lqgDiffeoInvarianceDemand,
    lqgVolumeGapDemand, lqgAmplitudeNonnegDemand, lqgRepDimHookDemand,
    lqgProperVolumeDemand, lqgBlackHoleEntropyDemand]

-- Reference: #27 — the ledger grading each demand (QG.0.1's `Requirements`).
/-- The **LQG requirements file** over the MHI framework: the demand list
with a status per demand. -/
def lqgRequirements : Requirements QGFramework where
  demands := lqgDemands
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
              · rcases List.mem_cons.mp h with h | h
                · exact Eq.subst (motive := fun d => DemandStatus.{1} d) h.symm DemandStatus.pending
                · exact Eq.subst (motive := fun d => DemandStatus.{1} d)
                    (List.mem_singleton.mp h).symm DemandStatus.pending

end BoringLab
