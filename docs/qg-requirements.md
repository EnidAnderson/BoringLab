# QG requirements ledgers — STR.1.1 (#26), LQG.1.1 (#27), QG.0.1 (#23)

`BoringLab/QGRequirements/` holds the quantum-gravity field files in the
QG.0.1 shape (`Demand.lean`, ticket #23): a field of science enters as a
scientist-owned list of **demands** on the framework
(`BoringMath.MotivicHolographicInfo`, #356), each demand a falsifiable
`Prop` statement plus a certificate type, graded `satisfied` / `partially`
/ `pending` in a ledger.

- `LQG.lean` (LQG.1.1 #27, the Rovelli lane): 8 demands. Satisfied with
  proved witnesses from `BoringMath.Physics.LQG.*`: area gap, discrete info
  (`lqgKinematics_info_gap`), diffeomorphism invariance (`area_relabel`),
  volume gap (`areaAsVolume`), amplitude positivity, and the motivic hook
  `info = Σ (repDim j − 1)`. Pending with peeling plans: proper volume
  spectrum (intertwiners/6j), black-hole entropy `S = A/4` in counting form.
- `StringTheory.lean` (STR.1.1 #26, the Susskind lane): 8 demands. Satisfied:
  holographic counting bound `#B ≤ k^#ι`, its saturation (Bekenstein in
  bits), worldsheet translation symmetry, lattice background independence
  (`polyakovAction_relabel`), AdS/CFT reconstruction adjunction
  (`adscftToy_reconstruction`), info = boundary cells. Pending with named
  holes: continuum limit of the lattice action, perturbation convergence.

The motivic-information hooks (MI.0.1 #67, #373): the info measures of the
MHI instances are where the DM-motive/period layer attaches — on the LQG side
the total spin expressed via representation dimensions `repDim j = 2j+1`;
on the string side the boundary cell count bounding the bulk states.

## MI.0.2 bridge (#66)

`QGRequirements/MotivicBridge.lean` bridges the two ledgers to the Gysin lane
(`BoringLab/Doctrine/Gysin.lean`, 4ebb51a): seven bridge demands, all
satisfied — the hook theorem `gysinMove_info_invariant` (cycle-factoring info
is invariant under Gysin moves), moves-compose on the scheme computad
(`gysinMove_comp`), LQG relabeling transitivity and string background
independence as the graph/lattice move laws, the hologram action of the
holographic toy, the degree-trace row `gysinMove_degree_trace` (via
`degree_pushforward`, Trace lane), and the puncture-degree row #369 (filled
by BoringMath `Physics/LQG/PunctureCycle.lean`).

### Gap tickets (filed, then to be filled — never simplified away)

- **#367** (LQG rows, lab LQG.1.1 #27): black-hole entropy `S = A/4` in
  counting form is FILLED at the single-puncture level
  (`lqgBlackHoleEntropyDemand_satisfied`: one spin-1 edge with
  A₀ = 4/√(j(j+1)) has area = 4·info); the full intertwiner state counting
  per puncture stays open with its peeling plan. Proper volume is FILLED at
  the toy level (`lqgProperVolumeDemand_satisfied`: `areaPlusInfoVolume`,
  area + total spin, all laws proved, differs from area); the full
  intertwiner/6j spectrum stays open with its peeling plan. All 8 LQG rows
  satisfied.
- **#368** (STR rows, lab STR.1.1 #26): continuum-limit row FILLED —
  `continuumActionLimit` is a real liminf definition and its nonnegativity is
  proved (`strContinuumLimitDemand_satisfied`) under an explicit
  bounded-above hypothesis (honest: in ℝ an unbounded sequence has junk
  liminf). STILL OPEN: identifying the limit with the continuum Polyakov
  integral (mesh→0), and perturbation convergence (`stringAmplitude`, the
  one remaining named-hole sorry, with peeling plan).
- **#369** (MI.0.2 bridge, lab #66): FILLED — puncture-degree model in
  BoringMath `Physics/LQG/PunctureCycle.lean`; row satisfied in
  `MotivicBridge.lean` (`bridgePunctureDegreeDemand_satisfied`). Open
  extension: per-edge puncture cycles with degrees = area eigenvalues.
- The discrete-info demand is stated at full generality (existence of an MHI
  instance with discrete info measure, zero element as explicit data):
  `DiscreteInfo` + `mhi_exists_discreteInfo` in BoringMath
  `Physics/LQG/SpinNetwork.lean`.
