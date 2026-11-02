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
(`BoringLab/Doctrine/Gysin.lean`, 4ebb51a): six bridge demands, all satisfied —
the hook theorem `gysinMove_info_invariant` (cycle-factoring info is invariant
under Gysin moves), moves-compose on the scheme computad (`gysinMove_comp`),
LQG relabeling transitivity and string background independence as the
graph/lattice move laws, the hologram action of the holographic toy, and the
area-as-pushforward-degree row (equality form; the degree reading is the open
part, peeling plan via the 9c88c74 residue-degree lane).
